import Submission.OddOrder.BG.AppendixAB.LocalQuotientPairHom

/-!
The local quotient-pair action map with common domain `pairGenerated x y`.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01

variable {G : Type*} [Group G]

/-- The pair-generated subgroup maps onto its local image in
`N_G(E) / C_G(E)`. -/
def pairGeneratedLocalQuotientHom (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    pairGenerated x y →* localQuotientPair E hxN hyN :=
  (pairGeneratedToLocalQuotient E hxN hyN).comp
    (Subgroup.subgroupOfEquivOfLe
      (pairGenerated_le_normalizer hxN hyN)).symm.toMonoidHom

@[simp]
theorem pairGeneratedLocalQuotientHom_apply
    (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (z : pairGenerated x y) :
    ((pairGeneratedLocalQuotientHom E hxN hyN z :
        localQuotientPair E hxN hyN) :
      (Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E) =
      QuotientGroup.mk' (normalizerCentralizer E)
        ⟨(z : G), pairGenerated_le_normalizer hxN hyN z.property⟩ :=
  rfl

theorem pairGeneratedLocalQuotientHom_surjective
    (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    Function.Surjective (pairGeneratedLocalQuotientHom E hxN hyN) :=
  (pairGeneratedToLocalQuotient_surjective E hxN hyN).comp
    (Subgroup.subgroupOfEquivOfLe
      (pairGenerated_le_normalizer hxN hyN)).symm.surjective

theorem mem_ker_pairGeneratedLocalQuotientHom_iff
    (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (z : pairGenerated x y) :
    z ∈ (pairGeneratedLocalQuotientHom E hxN hyN).ker ↔
      (z : G) ∈ Subgroup.centralizer (E : Set G) := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro hz
    have hq := congrArg Subtype.val hz
    change QuotientGroup.mk' (normalizerCentralizer E)
      ⟨(z : G), pairGenerated_le_normalizer hxN hyN z.property⟩ = 1 at hq
    exact (QuotientGroup.eq_one_iff
      (N := normalizerCentralizer E)
      (⟨(z : G), pairGenerated_le_normalizer hxN hyN z.property⟩ :
        Subgroup.normalizer (E : Set G))).mp hq
  · intro hz
    apply Subtype.ext
    change QuotientGroup.mk' (normalizerCentralizer E)
      ⟨(z : G), pairGenerated_le_normalizer hxN hyN z.property⟩ = 1
    exact (QuotientGroup.eq_one_iff
      (N := normalizerCentralizer E)
      (⟨(z : G), pairGenerated_le_normalizer hxN hyN z.property⟩ :
        Subgroup.normalizer (E : Set G))).mpr hz

/-- Restricting the acted-on subgroup enlarges the kernel of the local pair
action. -/
theorem pairGeneratedLocalQuotientHom_ker_mono
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G)) :
    (pairGeneratedLocalQuotientHom E hxNE hyNE).ker ≤
      (pairGeneratedLocalQuotientHom M hxNM hyNM).ker := by
  intro z hz
  rw [mem_ker_pairGeneratedLocalQuotientHom_iff] at hz ⊢
  exact Subgroup.centralizer_le (SetLike.coe_mono hME) hz

end Submission.OddOrder.BG.AppendixAB
