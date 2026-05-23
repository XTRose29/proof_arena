import Mathlib
import Submission.BurnsideCore

namespace Submission.Helpers

open Fintype

/-
A group of prime-power order is solvable (p-group → nilpotent → solvable).
-/
theorem isSolvable_of_card_eq_prime_pow {G : Type*} [Group G] [Fintype G]
    {p a : ℕ} (hp : Nat.Prime p) (hcard : Fintype.card G = p ^ a) :
    IsSolvable G := by
  -- If $G$ is a $p$-group, then it is nilpotent.
  have h_nilpotent : Group.IsNilpotent G := by
    have h_pgroup : IsPGroup p G := by
      -- By definition of IsPGroup, we need to show that every element of G has order a power of p.
      apply IsPGroup.of_card;
      convert hcard;
      convert Nat.card_eq_fintype_card;
    haveI := Fact.mk hp; exact h_pgroup.isNilpotent;
  infer_instance

/-
The order of a subgroup of a group of order p^a * q^b has the form p^a' * q^b'.
-/
theorem card_subgroup_eq_prime_pow_mul_prime_pow {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (_hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) (N : Subgroup G) [Fintype N] :
    ∃ a' b', a' ≤ a ∧ b' ≤ b ∧ Fintype.card N = p ^ a' * q ^ b' := by
  have := Subgroup.card_subgroup_dvd_card N; simp_all +decide ; (
  rw [ Nat.dvd_mul ] at this; simp_all +decide [ Nat.dvd_prime_pow ] ;
  grind)

/-
The order of a quotient of a group of order p^a * q^b has the form p^a' * q^b'.
-/
theorem card_quotient_eq_prime_pow_mul_prime_pow {G : Type*} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (_hpq : p ≠ q)
    (hcard : Fintype.card G = p ^ a * q ^ b) (N : Subgroup G) [N.Normal]
    [Fintype (G ⧸ N)] :
    ∃ a' b', a' ≤ a ∧ b' ≤ b ∧ Fintype.card (G ⧸ N) = p ^ a' * q ^ b' := by
  -- By definition of quotient group, we know that its order is equal to the order of G divided by the order of N.
  have h_card_quotient : (Fintype.card (G ⧸ N)) ∣ (Fintype.card G) := by
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup N; aesop;
  simp_all +decide;
  rw [ Nat.dvd_mul ] at h_card_quotient;
  rcases h_card_quotient with ⟨ k₁, k₂, hk₁, hk₂, hk ⟩ ; rw [ Nat.dvd_prime_pow hp, Nat.dvd_prime_pow hq ] at *; aesop;

/-- A group of order p^a * q^b with a, b ≥ 1 is not simple. -/
theorem not_isSimpleGroup_of_card_eq_prime_pow_mul_prime_pow {G : Type} [Group G] [Fintype G]
    {p q a b : ℕ} (hp : Nat.Prime p) (hq : Nat.Prime q) (hpq : p ≠ q)
    (ha : 0 < a) (hb : 0 < b)
    (hcard : Fintype.card G = p ^ a * q ^ b) :
    ¬ IsSimpleGroup G :=
  Submission.BurnsideCore.not_isSimpleGroup_of_card hp hq hpq ha hb hcard

end Submission.Helpers
