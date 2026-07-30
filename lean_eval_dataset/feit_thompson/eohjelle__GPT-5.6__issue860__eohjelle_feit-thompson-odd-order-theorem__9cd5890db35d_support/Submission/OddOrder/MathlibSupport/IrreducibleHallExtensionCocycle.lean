import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Group.Units.Equiv
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Int.GCD
import Mathlib.Tactic.Group

/-!
# Coprime trivialization of scalar factor sets

The character-extension argument used in Peterfalvi 1.7(c) passes through a
projective representation of the Hall quotient.  Its scalar factor set has
two independent annihilators: the representation degree (by taking
determinants) and the order of the quotient (by the finite-product transfer
calculation below).  This file packages the purely group-cohomological part
of that argument without introducing a projective-representation API.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v

variable {Q : Type u} {A : Type v}

/-- The multiplicative two-cocycle identity for a scalar factor set. -/
def IsScalarFactorSet [Group Q] [CommGroup A] (alpha : Q → Q → A) : Prop :=
  ∀ a b c, alpha a b * alpha (a * b) c =
    alpha b c * alpha a (b * c)

/-- A scalar factor set is a coboundary when it comes from rescaling a
choice of projective lifts. -/
def IsScalarCoboundary [Group Q] [CommGroup A] (alpha : Q → Q → A) : Prop :=
  ∃ beta : Q → A, ∀ a b,
    alpha a b = beta a * beta b * (beta (a * b))⁻¹

/-- The standard finite-product calculation: every scalar factor set on a
finite group has its `|Q|`-th power equal to a coboundary. -/
theorem scalarFactorSet_pow_card_isCoboundary
    [Group Q] [Fintype Q] [CommGroup A]
    (alpha : Q → Q → A) (halpha : IsScalarFactorSet alpha) :
    ∃ beta : Q → A, ∀ a b,
      alpha a b ^ Fintype.card Q =
        beta a * beta b * (beta (a * b))⁻¹ := by
  let beta : Q → A := fun a ↦ ∏ x : Q, alpha a x
  refine ⟨beta, fun a b ↦ ?_⟩
  have hprod :
      (∏ x : Q, alpha a b * alpha (a * b) x) =
        ∏ x : Q, alpha b x * alpha a (b * x) := by
    apply Finset.prod_congr rfl
    intro x _
    exact halpha a b x
  have hperm : (∏ x : Q, alpha a (b * x)) = ∏ x : Q, alpha a x := by
    exact Fintype.prod_bijective (b * ·) (Group.mulLeft_bijective b)
      (fun x ↦ alpha a (b * x)) (fun x ↦ alpha a x) (fun _ ↦ rfl)
  simp only [Finset.prod_mul_distrib, Finset.prod_const] at hprod
  rw [hperm] at hprod
  dsimp only [beta]
  apply mul_right_cancel (b := ∏ x : Q, alpha (a * b) x)
  calc
    alpha a b ^ Fintype.card Q *
        (∏ x : Q, alpha (a * b) x) =
      (∏ x : Q, alpha b x) * (∏ x : Q, alpha a x) := hprod
    _ = (∏ x : Q, alpha a x) * (∏ x : Q, alpha b x) := by
      rw [mul_comm]
    _ = ((∏ x : Q, alpha a x) * (∏ x : Q, alpha b x) *
          (∏ x : Q, alpha (a * b) x)⁻¹) *
        (∏ x : Q, alpha (a * b) x) := by
      group

/-- If a scalar factor set has an `n`-th power coboundary and `n` is
coprime to the order of the finite indexing group, then the factor set
itself is a coboundary. -/
theorem scalarFactorSet_isCoboundary_of_pow_of_coprime
    [Group Q] [Fintype Q] [CommGroup A]
    (alpha : Q → Q → A) (halpha : IsScalarFactorSet alpha)
    (n : ℕ) (hcop : Nat.Coprime n (Fintype.card Q))
    (delta : Q → A)
    (hdelta : ∀ a b, alpha a b ^ n =
      delta a * delta b * (delta (a * b))⁻¹) :
    IsScalarCoboundary alpha := by
  obtain ⟨gamma, hgamma⟩ :=
    scalarFactorSet_pow_card_isCoboundary alpha halpha
  let r : ℤ := Nat.gcdA n (Fintype.card Q)
  let s : ℤ := Nat.gcdB n (Fintype.card Q)
  let beta : Q → A := fun a ↦ delta a ^ r * gamma a ^ s
  refine ⟨beta, fun a b ↦ ?_⟩
  have hbezout : (n : ℤ) * r + (Fintype.card Q : ℤ) * s = 1 := by
    have hgcd := Nat.gcd_eq_gcd_ab n (Fintype.card Q)
    rw [hcop] at hgcd
    simpa [r, s] using hgcd.symm
  calc
    alpha a b = alpha a b ^ (1 : ℤ) := by simp
    _ = alpha a b ^ ((n : ℤ) * r + (Fintype.card Q : ℤ) * s) := by
      rw [hbezout]
    _ = (alpha a b ^ n) ^ r *
        (alpha a b ^ Fintype.card Q) ^ s := by
      rw [zpow_add, zpow_mul, zpow_mul, zpow_natCast, zpow_natCast]
    _ = (delta a * delta b * (delta (a * b))⁻¹) ^ r *
        (gamma a * gamma b * (gamma (a * b))⁻¹) ^ s := by
      rw [hdelta, hgamma]
    _ = beta a * beta b * (beta (a * b))⁻¹ := by
      dsimp only [beta]
      simp only [mul_zpow, inv_zpow, mul_inv_rev]
      ac_rfl

end Submission.OddOrder.MathlibSupport
