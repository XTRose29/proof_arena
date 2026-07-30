import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Submission.OddOrder.MathlibSupport.Solvability

/-!
Sylow arithmetic for finite groups whose order is a product of two distinct
primes.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p q : ℕ}

/-- A Sylow subgroup for the left prime in a `p * q` group has order `p`. -/
theorem sylow_card_eq_left_prime_of_natCard_eq_mul
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcard : Nat.card G = p * q) (P : Sylow p G) :
    Nat.card P = p := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [P.card_eq_multiplicity, hcard, Nat.factorization_mul hp.ne_zero hq.ne_zero,
    Finsupp.add_apply, hp.factorization_self, hq.factorization]
  simp [hpq]

/-- A Sylow subgroup for the left prime in a `p * q` group has index `q`. -/
theorem sylow_index_eq_right_prime_of_natCard_eq_mul
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcard : Nat.card G = p * q) (P : Sylow p G) :
    (P : Subgroup G).index = q := by
  have hmul := (P : Subgroup G).card_mul_index
  rw [sylow_card_eq_left_prime_of_natCard_eq_mul hp hq hpq hcard P,
    hcard] at hmul
  exact Nat.eq_of_mul_eq_mul_left hp.pos hmul

/-- In a group of order `p * q` with `p < q`, every Sylow `q`-subgroup is
normal. -/
theorem sylow_right_normal_of_lt_of_natCard_eq_mul
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card G = p * q) (Q : Sylow q G) :
    (Q : Subgroup G).Normal := by
  letI : Fact q.Prime := ⟨hq⟩
  have hcard' : Nat.card G = q * p := hcard.trans (Nat.mul_comm p q)
  have hindex : (Q : Subgroup G).index = p :=
    sylow_index_eq_right_prime_of_natCard_eq_mul hq hp hpq.ne' hcard' Q
  have hdiv : Nat.card (Sylow q G) ∣ p := by
    rw [← hindex]
    exact Q.card_dvd_index
  have hlt : Nat.card (Sylow q G) < q :=
    lt_of_le_of_lt (Nat.le_of_dvd hp.pos hdiv) hpq
  have hone : Nat.card (Sylow q G) = 1 :=
    (card_sylow_modEq_one q G).eq_of_lt_of_lt hlt hq.one_lt
  letI : Subsingleton (Sylow q G) := (Nat.card_eq_one_iff_unique.mp hone).1
  exact Sylow.normal_of_subsingleton Q

/-- Sylow subgroups for the two factors of a squarefree prime-product order
are complementary. -/
theorem sylow_isComplement_of_natCard_eq_mul
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcard : Nat.card G = p * q) (P : Sylow p G) (Q : Sylow q G) :
    (P : Subgroup G).IsComplement' (Q : Subgroup G) := by
  apply Subgroup.isComplement'_of_coprime
  · rw [sylow_card_eq_left_prime_of_natCard_eq_mul hp hq hpq hcard P]
    have hqcard : Nat.card Q = q :=
      sylow_card_eq_left_prime_of_natCard_eq_mul hq hp hpq.symm
        (hcard.trans (Nat.mul_comm p q)) Q
    rw [hqcard, hcard]
  · rw [sylow_card_eq_left_prime_of_natCard_eq_mul hp hq hpq hcard P]
    rw [sylow_card_eq_left_prime_of_natCard_eq_mul hq hp hpq.symm
      (hcard.trans (Nat.mul_comm p q)) Q]
    exact (Nat.coprime_primes hp hq).mpr hpq

/-- A finite group of order `p * q`, with `p < q` prime, is solvable. -/
theorem isSolvable_of_natCard_eq_mul_primes_of_lt
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card G = p * q) :
    IsSolvable G := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  let P : Sylow p G := default
  let Q : Sylow q G := default
  letI : (Q : Subgroup G).Normal :=
    sylow_right_normal_of_lt_of_natCard_eq_mul hp hq hpq hcard Q
  have hcomp := sylow_isComplement_of_natCard_eq_mul hp hq hpq.ne hcard P Q
  letI : IsCyclic P := isCyclic_of_prime_card
    (sylow_card_eq_left_prime_of_natCard_eq_mul hp hq hpq.ne hcard P)
  letI : IsCyclic Q := isCyclic_of_prime_card
    (sylow_card_eq_left_prime_of_natCard_eq_mul hq hp hpq.ne'
      (hcard.trans (Nat.mul_comm p q)) Q)
  letI : IsSolvable P := isSolvable_of_comm fun a b ↦ mul_comm a b
  letI : IsSolvable Q := isSolvable_of_comm fun a b ↦ mul_comm a b
  let e := hcomp.QuotientMulEquiv
  letI : IsSolvable (G ⧸ (Q : Subgroup G)) :=
    isSolvable_of_injective e.toMonoidHom e.injective
  exact isSolvable_of_normal_subgroup_and_quotient (Q : Subgroup G)

/-- Every finite group of order `p * q` for distinct primes is solvable. -/
theorem isSolvable_of_natCard_eq_mul_primes
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcard : Nat.card G = p * q) :
    IsSolvable G := by
  rcases lt_or_gt_of_ne hpq with hp_lt_q | hq_lt_p
  · exact isSolvable_of_natCard_eq_mul_primes_of_lt hp hq hp_lt_q hcard
  · have hcard' : Nat.card G = q * p := hcard.trans (Nat.mul_comm p q)
    exact isSolvable_of_natCard_eq_mul_primes_of_lt hq hp hq_lt_p hcard'

end Submission.OddOrder.MathlibSupport
