import Submission.OddOrder.MathlibSupport.PMaxElem
import Mathlib.GroupTheory.OrderOfElement

/-!
Coprime actions on abelian `p`-groups detected on their `p`-torsion.

This is the abelian action input in `BGsection1.coprime_odd_faithful_Ohm1`
and ports the substance of `coprime_abelian_faithful_Ohm1` in the form used
by the later maximal-elementary-abelian argument.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

/-- An automorphism of finite order coprime to `p` that fixes the
`p`-torsion of an abelian group pointwise fixes every element whose order
divides a power of `p`. -/
theorem mulAut_eq_one_of_coprime_of_fixed_pTorsion
    {H : Type*} [Group H] [IsMulCommutative H]
    {p m e : ℕ} (f : MulAut H)
    (hfm : f ^ m = 1) (hcop : p.Coprime m)
    (hfix : ∀ x : H, x ^ p = 1 → f x = x)
    (hexp : ∀ x : H, x ^ (p ^ e) = 1) :
    f = 1 := by
  have aux : ∀ d : ℕ, ∀ x : H, x ^ (p ^ d) = 1 → f x = x := by
    intro d
    induction d with
    | zero =>
        intro x hx
        have hx1 : x = 1 := by simpa using hx
        simp [hx1]
    | succ d ih =>
        intro x hx
        have hxpow : (x ^ p) ^ (p ^ d) = 1 := by
          rw [← pow_mul, Nat.mul_comm, ← pow_succ]
          exact hx
        have hfxpow : f (x ^ p) = x ^ p := ih (x ^ p) hxpow
        let y : H := f x * x⁻¹
        have hyp : y ^ p = 1 := by
          have hcomm : Commute (f x) x⁻¹ := mul_comm _ _
          dsimp [y]
          rw [hcomm.mul_pow, ← map_pow, inv_pow, hfxpow, mul_inv_cancel]
        have hfy : f y = y := hfix y hyp
        have hfx : f x = y * x := by
          simp [y, mul_assoc]
        have hiter : ∀ k : ℕ, (f ^ k) x = y ^ k * x := by
          intro k
          induction k with
          | zero => simp
          | succ k ihk =>
              rw [pow_succ']
              change f ((f ^ k) x) = y ^ (k + 1) * x
              rw [ihk, map_mul, map_pow, hfy, hfx]
              simp [pow_succ, mul_assoc, mul_comm]
        have hmfix : (f ^ m) x = x := by
          have := congrArg (fun g : MulAut H ↦ g x) hfm
          simpa using this
        rw [hiter m] at hmfix
        have hym : y ^ m = 1 := by
          apply mul_right_cancel (b := x)
          simpa using hmfix
        have hy : y = 1 :=
          (pow_eq_one_iff_of_coprime hcop).mp ⟨hyp, hym⟩
        simpa [hy] using hfx
  apply MulEquiv.ext
  intro x
  simpa using aux e x (hexp x)

/-- A coprime actor on an abelian `p`-subgroup is trivial once it centralizes
all elements of that subgroup whose `p`th power is one. -/
theorem abelian_pGroup_centralized_of_pTorsion_centralized
    [Finite G] {p : ℕ} [Fact p.Prime] {A H : Subgroup G}
    (hHp : IsPGroup p H) (hHcomm : IsMulCommutative H)
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hcop : p.Coprime (Nat.card A))
    (hcent : A ≤ Subgroup.centralizer
      ({x : G | x ∈ H ∧ x ^ p = 1} : Set G)) :
    A ≤ Subgroup.centralizer (H : Set G) := by
  classical
  letI : IsMulCommutative H := hHcomm
  obtain ⟨e, hcard⟩ := hHp.exists_card_eq
  have hexp : ∀ x : H, x ^ (p ^ e) = 1 := by
    intro x
    rw [← hcard]
    exact pow_card_eq_one'
  intro a ha
  let an : Subgroup.normalizer (H : Set G) := ⟨a, hAH ha⟩
  let f : MulAut H := H.normalizerMonoidHom an
  have haPow : a ^ Nat.card A = 1 := by
    have := pow_card_eq_one' (x := (⟨a, ha⟩ : A))
    exact congrArg Subtype.val this
  have hanPow : an ^ Nat.card A = 1 := by
    apply Subtype.ext
    exact haPow
  have hfPow : f ^ Nat.card A = 1 := by
    dsimp [f]
    rw [← map_pow, hanPow, map_one]
  have hfix : ∀ x : H, x ^ p = 1 → f x = x := by
    intro x hx
    apply Subtype.ext
    have hxPow : (x : G) ^ p = 1 := congrArg Subtype.val hx
    have hxa : (x : G) * a = a * (x : G) :=
      Subgroup.mem_centralizer_iff.mp (hcent ha) (x : G)
        ⟨x.property, hxPow⟩
    change a * (x : G) * a⁻¹ = (x : G)
    rw [← hxa]
    simp
  have hf : f = 1 :=
    mulAut_eq_one_of_coprime_of_fixed_pTorsion f hfPow hcop hfix hexp
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have happ := congrArg (fun g : MulAut H ↦ g (⟨x, hx⟩ : H)) hf
  have hconj : a * x * a⁻¹ = x := by
    simpa [f, an, Subgroup.normalizerMonoidHom, HSMul.hSMul] using
      congrArg Subtype.val happ
  calc
    x * a = (a * x * a⁻¹) * a := by rw [hconj]
    _ = a * x := by group

/-- Cardinal-coprime form, matching the hypothesis of
`BGsection1.coprime_abelian_faithful_Ohm1`. -/
theorem coprime_abelian_pGroup_centralized_of_pTorsion_centralized
    [Finite G] {p : ℕ} [Fact p.Prime] {A H : Subgroup G}
    (hHp : IsPGroup p H) (hHcomm : IsMulCommutative H)
    (hAH : A ≤ Subgroup.normalizer (H : Set G))
    (hcop : (Nat.card H).Coprime (Nat.card A))
    (hcent : A ≤ Subgroup.centralizer
      ({x : G | x ∈ H ∧ x ^ p = 1} : Set G)) :
    A ≤ Subgroup.centralizer (H : Set G) := by
  by_cases hH : H = ⊥
  · subst H
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx1 : x = 1 := Subgroup.mem_bot.mp hx
    subst x
    simp
  · obtain ⟨e, he⟩ := hHp.exists_card_eq
    have he0 : e ≠ 0 := by
      intro hez
      apply hH
      apply Subgroup.card_eq_one.mp
      rw [he, hez, pow_zero]
    have hpCard : p ∣ Nat.card H := by
      rw [he]
      exact dvd_pow_self p he0
    exact abelian_pGroup_centralized_of_pTorsion_centralized
      hHp hHcomm hAH (hcop.coprime_dvd_left hpCard) hcent

end Submission.OddOrder.MathlibSupport
