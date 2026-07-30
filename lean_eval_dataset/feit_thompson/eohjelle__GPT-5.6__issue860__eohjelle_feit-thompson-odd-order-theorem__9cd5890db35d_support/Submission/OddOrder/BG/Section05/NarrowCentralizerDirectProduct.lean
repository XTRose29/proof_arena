import Submission.OddOrder.BG.Section04.ExponentOmegaOneRankTwo
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.BG.Section05.NarrowPrimeCentralizerDecomposition

/-!
Bender--Glauberman Theorem 5.3(d).
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection5.v:narrow_cent_dprod` (Bender--Glauberman Theorem 5.3(d)).

MathComp's final equation `S \x 'C_T(S) = 'C_G(S)` packages three
facts: trivial intersection, elementwise commutation, and equality of the
generated subgroup with the ambient centralizer.  They are stated separately
here using mathlib's subgroup lattice.  The numerical hypothesis
`'r_p('C_G(S)) ≤ 2` is represented by the equivalent absence of an
elementary-abelian rank-three subgroup of `C_G(S)`. -/
theorem narrow_cent_dprod
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hRank3 : ∃ A : Subgroup G, IsElementaryAbelianOfRank p 3 A)
    (hNarrow : IsNarrow p (⊤ : Subgroup G))
    {S : Subgroup G} (hScard : Nat.card S = p)
    (hCentRank : ¬ ∃ F : Subgroup G,
      F ≤ centralizerWithin (⊤ : Subgroup G) S ∧
        IsElementaryAbelianOfRank p 3 F) :
    let T := omegaUpperCentralTwoCentralizer p G
    let C := centralizerWithin T S
    IsCyclic C ∧
      Disjoint S (commutator G) ∧
      Disjoint S T ∧
      Disjoint S C ∧
      (∀ s ∈ S, ∀ c ∈ C, Commute s c) ∧
      S ⊔ C = centralizerWithin (⊤ : Subgroup G) S := by
  let T : Subgroup G := omegaUpperCentralTwoCentralizer p G
  let C : Subgroup G := centralizerWithin T S
  obtain ⟨hSDerDis, hSTdis, hSCdis, hSCcomm, hSupCent⟩ :=
    narrow_prime_centralizer_decomposition
      hG hodd hRank3 hNarrow hScard hCentRank
  have hCcyclic : IsCyclic C := by
    have hCp : IsPGroup p C := hG.to_subgroup C
    have hCodd : Odd (Nat.card C) := odd_natCard_subgroup C hodd
    apply
      (Submission.OddOrder.BG.Section04.odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        hCp hCodd).mpr
    rintro ⟨E, hE⟩
    let F : Subgroup G := E.map C.subtype
    have hF : IsElementaryAbelianOfRank p 2 F := by
      dsimp [F]
      exact
        Submission.OddOrder.BG.Section04.isElementaryAbelianOfRank_map_of_injective
          hE C.subtype C.subtype_injective
    have hFC : F ≤ C := by
      dsimp [F]
      exact Subgroup.map_subtype_le E
    have hFT : F ≤ T :=
      hFC.trans (centralizerWithin_le_left T S)
    have hSFdis : Disjoint S F := hSTdis.mono_right hFT
    have hSFcomm : ∀ s ∈ S, ∀ f ∈ F, Commute s f := by
      intro s hs f hf
      exact hSCcomm s hs f (hFC hf)
    have hS : IsElementaryAbelianOfRank p 1 S :=
      isElementaryAbelianOfRank_one_of_card_eq_prime hScard
    have hSF : IsElementaryAbelianOfRank p 3 (S ⊔ F) := by
      simpa using
        (isElementaryAbelianOfRank_sup_of_disjoint_of_commute
          hG hS hF hSFdis hSFcomm)
    apply hCentRank
    refine ⟨S ⊔ F, ?_, hSF⟩
    rw [← hSupCent]
    exact sup_le le_sup_left (hFC.trans le_sup_right)
  exact
    ⟨hCcyclic, hSDerDis, hSTdis, hSCdis, hSCcomm, hSupCent⟩

end Submission.OddOrder.BG.Section05
