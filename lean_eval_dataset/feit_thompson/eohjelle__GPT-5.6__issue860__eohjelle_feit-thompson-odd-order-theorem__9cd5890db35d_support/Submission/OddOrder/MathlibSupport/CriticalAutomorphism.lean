import Submission.OddOrder.MathlibSupport.CharacteristicMulAutRestriction
import Submission.OddOrder.MathlibSupport.Critical
import Submission.OddOrder.MathlibSupport.PGroupPrimeOrderCriterion

/-!
Prime-power control of the pointwise automorphism fixer of a critical subgroup.

This is the automorphism-group form of MathComp's `critical_p_stab_Aut`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]

/-- MathComp's `critical_p_stab_Aut`: the automorphisms of a finite
`p`-group fixing a critical subgroup pointwise form a `p`-group. -/
theorem critical_fixingSubgroup_isPGroup
    {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (hG : IsPGroup p G) (hH : IsCritical H) :
    IsPGroup p (fixingSubgroup (MulAut G) (H : Set G)) := by
  classical
  letI : H.Characteristic := hH.characteristic
  apply isPGroup_of_prime_order_elements
  intro q hq hqp a haOrder
  apply Subtype.ext
  change (a : MulAut G) = 1
  apply MulEquiv.ext
  intro x
  let f : MulAut G := a
  let y : G := x⁻¹ * f x
  have hfix : ∀ h : G, h ∈ H → f h = h := by
    intro h hh
    have ha := a.property
    rw [mem_fixingSubgroup_iff] at ha
    simpa [f] using ha h hh
  have hyCentral : y ∈ Subgroup.centralizer (H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hxconj : x * h * x⁻¹ ∈ H :=
      (inferInstance : H.Normal).conj_mem h hh x
    have hconj : f x * h * (f x)⁻¹ = x * h * x⁻¹ := by
      have := hfix (x * h * x⁻¹) hxconj
      simpa only [map_mul, map_inv, hfix h hh] using this
    dsimp [y]
    calc
      h * (x⁻¹ * f x) = x⁻¹ * (x * h * x⁻¹) * f x := by group
      _ = x⁻¹ * (f x * h * (f x)⁻¹) * f x := by rw [← hconj]
      _ = (x⁻¹ * f x) * h := by group
  have hyH : y ∈ H := by
    have hyCenter : y ∈ centerWithin H := by
      rw [← hH.centralizer_eq_center]
      exact hyCentral
    exact centralizerWithin_le_left H H hyCenter
  have hfy : f y = y := hfix y hyH
  have hfx : f x = x * y := by
    dsimp [y]
    group
  have hiter : ∀ n : ℕ, (f ^ n) x = x * y ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
        calc
          (f ^ (n + 1)) x = f ((f ^ n) x) := by
            rw [pow_succ']
            rfl
          _ = f (x * y ^ n) := by rw [ih]
          _ = f x * (f y) ^ n := by rw [map_mul, map_pow]
          _ = (x * y) * y ^ n := by rw [hfx, hfy]
          _ = x * y ^ (n + 1) := by rw [pow_succ']; group
  have haPow : a ^ q = 1 := by
    rw [← haOrder]
    exact pow_orderOf_eq_one a
  have hfPow : f ^ q = 1 := by
    simpa [f] using congrArg Subtype.val haPow
  have hyPow : y ^ q = 1 := by
    have hi : x = x * y ^ q := by
      simpa [hfPow] using hiter q
    apply mul_left_cancel (a := x)
    simpa using hi
  have hpq : p.Coprime q :=
    (Nat.coprime_primes (Fact.out : p.Prime) hq).mpr (Ne.symm hqp)
  have hyOne : y = 1 := by
    apply (hG.powEquiv hpq).injective
    change y ^ q = 1 ^ q
    simpa using hyPow
  change f x = x
  rw [hfx, hyOne, mul_one]

end Submission.OddOrder.MathlibSupport
