import Submission.OddOrder.BG.AppendixAB.LocalConjugationRepresentation
import Submission.OddOrder.BG.AppendixAB.PairGeneratedCommutative
import Submission.OddOrder.MathlibSupport.PairGeneratedSubtype

/-!
The commuting-image branch of the odd p-stability representation argument.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

theorem local_commutator_isPGroup_of_commuting_representation
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hcomm : Commute
      (centralizerQuotientConjugationRepresentation E p
        (QuotientGroup.mk' (normalizerCentralizer E) ⟨x, hxN⟩))
      (centralizerQuotientConjugationRepresentation E p
        (QuotientGroup.mk' (normalizerCentralizer E) ⟨y, hyN⟩))) :
    let q := QuotientGroup.mk' (normalizerCentralizer E)
    let Q := pairGenerated (q ⟨x, hxN⟩) (q ⟨y, hyN⟩)
    IsPGroup p (_root_.commutator Q) := by
  dsimp only
  let q := QuotientGroup.mk' (normalizerCentralizer E)
  let xq := q ⟨x, hxN⟩
  let yq := q ⟨y, hyN⟩
  let Q := pairGenerated xq yq
  let xQ : Q := ⟨xq, mem_pairGenerated_left xq yq⟩
  let yQ : Q := ⟨yq, mem_pairGenerated_right xq yq⟩
  have hgen : pairGenerated xQ yQ = ⊤ := by
    rw [pairGenerated_subtype]
    change Q.comap Q.subtype = ⊤
    ext z
    simp
  have hxy : Commute xQ yQ := by
    rw [commute_iff_eq] at hcomm ⊢
    apply localSubgroupConjugationRepresentation_injective E p Q
    change centralizerQuotientConjugationRepresentation E p (xq * yq) =
      centralizerQuotientConjugationRepresentation E p (yq * xq)
    rw [map_mul, map_mul]
    exact hcomm
  letI : IsMulCommutative Q :=
    isMulCommutative_of_pairGenerated_eq_top hgen hxy
  have hder : _root_.commutator Q = ⊥ := _root_.commutator_eq_bot Q
  rw [hder]
  exact IsPGroup.of_bot

end Submission.OddOrder.BG.AppendixAB
