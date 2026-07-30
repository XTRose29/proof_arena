import Submission.OddOrder.BG.AppendixAB.LocalSchurNoncommutingBranch
import Submission.OddOrder.MathlibSupport.PairGeneratedSubtype

/-!
The canonical map from an ambient two-generator subgroup to its image in the
normalizer-centralizer quotient.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- Map the pair-generated subgroup, viewed inside `N_G(E)`, onto the local
pair generated in `N_G(E) / C_G(E)`. -/
def pairGeneratedToLocalQuotient (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    (pairGenerated x y).subgroupOf
        (Subgroup.normalizer (E : Set G)) →*
      localQuotientPair E hxN hyN :=
  let N := Subgroup.normalizer (E : Set G)
  let H := pairGenerated x y
  let q := QuotientGroup.mk' (normalizerCentralizer E)
  (q.comp (H.subgroupOf N).subtype).codRestrict
    (localQuotientPair E hxN hyN) fun z ↦ by
      change q (z : N) ∈
        pairGenerated (q ⟨x, hxN⟩) (q ⟨y, hyN⟩)
      rw [← pairGenerated_map_hom q ⟨x, hxN⟩ ⟨y, hyN⟩]
      refine ⟨z, ?_, rfl⟩
      rw [pairGenerated_subtype]
      exact z.property

@[simp]
theorem pairGeneratedToLocalQuotient_apply (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (z : (pairGenerated x y).subgroupOf
      (Subgroup.normalizer (E : Set G))) :
    ((pairGeneratedToLocalQuotient E hxN hyN z :
        localQuotientPair E hxN hyN) :
      (Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E) =
      QuotientGroup.mk' (normalizerCentralizer E)
        (z : Subgroup.normalizer (E : Set G)) :=
  rfl

theorem pairGeneratedToLocalQuotient_surjective (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    Function.Surjective (pairGeneratedToLocalQuotient E hxN hyN) := by
  rw [← MonoidHom.range_eq_top]
  apply top_unique
  rw [← pairGenerated_localQuotientPair_eq_top E hxN hyN]
  apply pairGenerated_le_iff.mpr
  constructor
  · refine ⟨⟨⟨x, hxN⟩, mem_pairGenerated_left x y⟩, ?_⟩
    apply Subtype.ext
    rfl
  · refine ⟨⟨⟨y, hyN⟩, mem_pairGenerated_right x y⟩, ?_⟩
    apply Subtype.ext
    rfl

/-- Pulling the local quotient action back along the canonical pair map gives
the restricted normalizer conjugation action. -/
theorem localQuotientPairRepresentation_comp_pairGeneratedToLocalQuotient
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    (localQuotientPairRepresentation E p hxN hyN).comp
        (pairGeneratedToLocalQuotient E hxN hyN) =
      (normalizerConjugationRepresentation E p).comp
        ((pairGenerated x y).subgroupOf
          (Subgroup.normalizer (E : Set G))).subtype := by
  apply MonoidHom.ext
  intro z
  apply LinearMap.ext
  intro v
  exact centralizerQuotientConjugationRepresentation_mk_apply
    E p (z : Subgroup.normalizer (E : Set G)) v

end Submission.OddOrder.BG.AppendixAB
