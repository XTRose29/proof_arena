import Mathlib.GroupTheory.Complement

/-!
Complementary normal factors after quotienting by a subgroup of the normal
factor.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]
variable {K R N : Subgroup G}

namespace Subgroup.IsComplement'

/-- A quotient by a subgroup of the left complement factor is injective on
the right factor. -/
theorem quotientMap_injective_on_right
    (h : K.IsComplement' R) [N.Normal] (hNK : N ≤ K) :
    Function.Injective
      (fun r : R ↦ QuotientGroup.mk' N (r : G)) := by
  intro r s hrs
  have hn : (r : G)⁻¹ * (s : G) ∈ N :=
    QuotientGroup.eq.mp hrs
  have hk : (r : G)⁻¹ * (s : G) ∈ K := hNK hn
  have hr : (r : G)⁻¹ * (s : G) ∈ R :=
    R.mul_mem (R.inv_mem r.property) s.property
  have hKR : K ⊓ R = ⊥ := disjoint_iff.mp h.disjoint
  have hone : (r : G)⁻¹ * (s : G) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hKR]
    exact ⟨hk, hr⟩
  apply Subtype.ext
  exact inv_mul_eq_one.mp hone

/-- The quotient map restricted to the right factor is injective as a
subgroup homomorphism. -/
theorem quotientRight_subgroupMap_injective
    (h : K.IsComplement' R) [N.Normal] (hNK : N ≤ K) :
    Function.Injective
      ((QuotientGroup.mk' N).subgroupMap R) := by
  intro r s hrs
  apply quotientMap_injective_on_right h hNK
  exact congrArg Subtype.val hrs

/-- A nontrivial right complement factor remains nontrivial after quotienting
by a subgroup of the left factor. -/
theorem quotient_right_ne_bot
    (h : K.IsComplement' R) [N.Normal] (hNK : N ≤ K) (hR : R ≠ ⊥) :
    R.map (QuotientGroup.mk' N) ≠ ⊥ := by
  intro hbot
  apply hR
  apply le_bot_iff.mp
  intro r hr
  have hqr : QuotientGroup.mk' N r ∈
      R.map (QuotientGroup.mk' N) := ⟨r, hr, rfl⟩
  rw [hbot] at hqr
  have hqOne : QuotientGroup.mk' N r = 1 := Subgroup.mem_bot.mp hqr
  have hrOne : (⟨r, hr⟩ : R) = 1 :=
    quotientMap_injective_on_right h hNK (by simpa using hqOne)
  exact Subgroup.mem_bot.mpr (congrArg Subtype.val hrOne)

/-- Complementary factors remain complementary after quotienting by a normal
subgroup of the normal left factor. -/
theorem quotient_isComplement
    (h : K.IsComplement' R) [K.Normal] [N.Normal] (hNK : N ≤ K) :
    (K.map (QuotientGroup.mk' N)).IsComplement'
      (R.map (QuotientGroup.mk' N)) := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  let Kq : Subgroup (G ⧸ N) := K.map q
  let Rq : Subgroup (G ⧸ N) := R.map q
  letI : Kq.Normal :=
    Subgroup.Normal.map (inferInstance : K.Normal) q
      (QuotientGroup.mk'_surjective N)
  have hsup : Kq ⊔ Rq = ⊤ := by
    dsimp [Kq, Rq]
    rw [← Subgroup.map_sup, h.sup_eq_top,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective N)]
  have hdis : Disjoint Kq Rq := by
    rw [disjoint_iff_inf_le]
    intro z hz
    rcases hz.1 with ⟨k, hk, hkz⟩
    rcases hz.2 with ⟨r, hr, hrz⟩
    have hkr : q k = q r := hkz.trans hrz.symm
    have hn : k⁻¹ * r ∈ N := QuotientGroup.eq.mp hkr
    have hkinK : k⁻¹ * r ∈ K := hNK hn
    have hrK : r ∈ K := by
      have hrEq : r = k * (k⁻¹ * r) := by
        simp [← mul_assoc]
      rw [hrEq]
      exact K.mul_mem hk hkinK
    have hKR : K ⊓ R = ⊥ := disjoint_iff.mp h.disjoint
    have hrOne : r = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hKR]
      exact ⟨hrK, hr⟩
    apply Subgroup.mem_bot.mpr
    rw [← hrz, hrOne, map_one]
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  rw [← Subgroup.normal_mul Kq Rq, hsup]
  rfl

end Subgroup.IsComplement'

end Submission.OddOrder.MathlibSupport
