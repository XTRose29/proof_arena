import Submission.OddOrder.BG.Section16.SummaryABC
import Submission.OddOrder.BG.Section16.TypeSpecInfrastructure

/-!
# Bender--Glauberman Section 16: the outer support sets

This module identifies the enlarged support with the ordinary support for
type-one maximal subgroups and with the mixed part of the type-P direct
product in the remaining case.
-/

namespace Submission.OddOrder.BG.Section16

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open TypeSpecInternal
open scoped Pointwise

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-- `BGsection16.v: FTsupp0_type1`. -/
theorem FTsupp0_type1 (M : Subgroup G) (htype : FTtype M = 1) :
    FTsupport0 M = FTsupport M := by
  apply Set.Subset.antisymm
  · intro x hx
    rcases hx with hxSupport | ⟨hxM, hxNotSupported, _⟩
    · exact hxSupport
    · exfalso
      apply hxNotSupported
      simpa [FTder, ftDerived, htype] using
        (show IsPiNumber (primeSupport (Nat.card M)) (orderOf x) from by
          intro p hp hpx
          exact ⟨hp, hpx.trans (by
            simpa using orderOf_dvd_natCard (⟨x, hxM⟩ : M))⟩)
  · exact Set.subset_union_left

/-- `BGsection16.v: FTsupp0_typeP`. -/
theorem FTsupp0_typeP
    (M U W₁ W₂ W : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hTypeP : of_typeP M U W W₁ W₂ defW) :
    FTsupport0 M \ FTsupport M =
      classSupportWithin M
        ((W : Set G) \ ((W₁ : Set G) ∪ (W₂ : Set G))) := by
  classical
  have hFacts := typePFacts16 hM hTypeP
  obtain ⟨V, hComplement⟩ :=
    ex_kappa_compl hM hTypeP.1.2.1.1 hFacts.W₁_hall_kappa
  have hOuter :=
    (BGsummaryC hM hComplement hTypeP.1.2.2.1).outer_support_eq_classSupport
  have hPartner : pTypePartner M W₁ = W₂ := hFacts.partner_eq
  have hJoin : pTypeJoin M W₁ = W := by
    rw [pTypeJoin, hPartner]
    calc
      W₁ ⊔ W₂ =
          ((W₁.subgroupOf W) ⊔ (W₂.subgroupOf W)).map W.subtype := by
        rw [Subgroup.map_sup,
          Subgroup.map_subgroupOf_eq_of_le defW.left_le,
          Subgroup.map_subgroupOf_eq_of_le defW.right_le]
      _ = (⊤ : Subgroup W).map W.subtype := by
        rw [defW.complement.sup_eq_top]
      _ = W := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  simpa [pTypeTISet, hPartner, hJoin] using hOuter

end

end Submission.OddOrder.BG.Section16
