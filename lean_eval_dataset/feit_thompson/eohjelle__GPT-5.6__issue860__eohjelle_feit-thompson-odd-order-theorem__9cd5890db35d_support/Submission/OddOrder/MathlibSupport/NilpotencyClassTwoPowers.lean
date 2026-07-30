import Mathlib.Data.Nat.Choose.Dvd
import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.Tactic.Group
import Submission.OddOrder.MathlibSupport.CentralCommutatorPowers

/-!
Power collection in groups whose commutator subgroup is central.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

theorem mul_eq_commutatorElement_mul_swap (a b : G) :
    a * b = ⁅a, b⁆ * b * a := by
  simp [commutatorElement_def, mul_assoc]

/-- The class-two Hall-Petresco formula. The commutator orientation agrees
with MathComp's formula `(x*y)^n = x^n*y^n*[y,x]^(n choose 2)`. -/
theorem mul_pow_of_commutator_le_center
    (hcentral : _root_.commutator G ≤ Subgroup.center G) (x y : G) :
    ∀ n : ℕ, (x * y) ^ n =
      x ^ n * y ^ n * ⁅y, x⁆ ^ (n.choose 2)
  | 0 => by simp
  | n + 1 => by
      let r := ⁅y, x⁆
      have hrcenter : r ∈ Subgroup.center G :=
        commutatorElement_mem_center_of_commutator_le hcentral y x
      have hrpowCenter (m : ℕ) : r ^ m ∈ Subgroup.center G :=
        (Subgroup.center G).pow_mem hrcenter m
      have hryx : y ^ n * x = r ^ n * x * y ^ n := by
        calc
          y ^ n * x = ⁅y ^ n, x⁆ * x * y ^ n :=
            mul_eq_commutatorElement_mul_swap (y ^ n) x
          _ = r ^ n * x * y ^ n := by
            rw [commutatorElement_pow_left_of_commutator_le hcentral]
      rw [pow_succ, mul_pow_of_commutator_le_center hcentral x y n]
      change (x ^ n * y ^ n * r ^ (n.choose 2)) * (x * y) = _
      calc
        (x ^ n * y ^ n * r ^ (n.choose 2)) * (x * y) =
            (x ^ n * y ^ n * (x * y)) * r ^ (n.choose 2) := by
          rw [mul_assoc (x ^ n * y ^ n),
            (Subgroup.mem_center_iff.mp
              (hrpowCenter (n.choose 2)) (x * y)).symm]
          group
        _ = (x ^ n * (y ^ n * x) * y) * r ^ (n.choose 2) := by
          group
        _ = (x ^ n * (r ^ n * x * y ^ n) * y) *
            r ^ (n.choose 2) := by rw [hryx]
        _ = x ^ (n + 1) * y ^ (n + 1) *
            (r ^ n * r ^ (n.choose 2)) := by
          have hrnCommTail : Commute (r ^ n) (x * y ^ n * y) :=
            (Subgroup.mem_center_iff.mp
              (hrpowCenter n) (x * y ^ n * y)).symm
          calc
            (x ^ n * (r ^ n * x * y ^ n) * y) * r ^ (n.choose 2) =
                x ^ n * (r ^ n * (x * y ^ n * y)) *
                  r ^ (n.choose 2) := by group
            _ = x ^ n * ((x * y ^ n * y) * r ^ n) *
                  r ^ (n.choose 2) := by rw [hrnCommTail.eq]
            _ = x ^ (n + 1) * y ^ (n + 1) *
                  (r ^ n * r ^ (n.choose 2)) := by
              rw [pow_succ, pow_succ]
              group
        _ = x ^ (n + 1) * y ^ (n + 1) *
            r ^ ((n + 1).choose 2) := by
          rw [← pow_add, Nat.choose_succ_succ]
          simp

theorem prime_dvd_choose_two (p : ℕ) (hp : p.Prime) (hpodd : Odd p) :
    p ∣ p.choose 2 := by
  apply hp.dvd_choose_self
  · norm_num
  · have hp2 : p ≠ 2 := by
      intro hpEq
      subst p
      exact (Nat.not_even_iff_odd.mpr hpodd) (by norm_num)
    have hpge : 2 ≤ p := hp.two_le
    omega

/-- In an odd prime exponent class-two group, taking `p`th powers is a
homomorphism. -/
noncomputable def primePowerMonoidHomOfCommutatorLeCenter
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hcentral : _root_.commutator G ≤ Subgroup.center G)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1) : G →* G where
  toFun x := x ^ p
  map_one' := one_pow p
  map_mul' x y := by
    rw [mul_pow_of_commutator_le_center hcentral]
    have hr : ⁅y, x⁆ ∈ _root_.commutator G :=
      Subgroup.commutator_mem_commutator trivial trivial
    obtain ⟨m, hm⟩ := prime_dvd_choose_two p hp hpodd
    rw [hm, pow_mul, hcommPow _ hr, one_pow, mul_one]

@[simp]
theorem primePowerMonoidHomOfCommutatorLeCenter_apply
    (p : ℕ) (hp : p.Prime) (hpodd : Odd p)
    (hcentral : _root_.commutator G ≤ Subgroup.center G)
    (hcommPow : ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1)
    (x : G) :
    primePowerMonoidHomOfCommutatorLeCenter p hp hpodd hcentral hcommPow x =
      x ^ p :=
  rfl

end Submission.OddOrder.MathlibSupport
