import Submission.OddOrder.BG.Section08.NonPCoreFittingMaxNorm
import Submission.OddOrder.BG.Section08.NonPCoreFittingMaximalOvergroup

/-!
# Bender--Glauberman Theorem 8.1(a)

This composes the singleton maximal-normalized-family result with the
maximal-overgroup comparison to obtain the non-`p`-core Fitting uniqueness
theorem.
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07

universe u

/-- Bender--Glauberman Theorem 8.1(a): when the Fitting subgroup of a
maximal subgroup is not a `p`-group, the centralizer in that Fitting subgroup
of a maximal elementary-abelian `p`-subgroup of rank at least three has a
unique maximal overgroup. -/
theorem non_pcore_Fitting_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime] (M A₀ : Subgroup G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hFp : ¬ IsPGroup p (fittingWithin M))
    (hA₀ : IsPMaxElem p (fittingWithin M) A₀)
    (hRank3 : ∃ E : Subgroup G,
      E ≤ A₀ ∧ IsElementaryAbelianOfRank p 3 E) :
    centralizerWithin (fittingWithin M) A₀ ∈
      minSimple_uniq_max_groups (G := G) := by
  let A : Subgroup G := centralizerWithin (fittingWithin M) A₀
  have hAM : A ≤ M :=
    (centralizerWithin_le_left (fittingWithin M) A₀).trans
      (fittingWithin_le M)
  apply (uniq_mmax_subset1 hM hAM).mpr
  intro H hH
  rw [Set.mem_singleton_iff]
  exact non_pcore_fitting_maximal_overgroup p M A₀ H hM hFp hA₀
    hRank3
    (fun q hq ↦
      non_pcore_fitting_max_normed_eq_bot p M A₀ hM hFp hA₀
        hRank3 q hq)
    hH.1 hH.2

end Submission.OddOrder.BG.Section08
