import Mathlib.GroupTheory.PGroup
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
Elementary abelian groups and the cardinal-rank form used by the local
analysis port.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G]

/-- A finite-group-theory elementary abelian `p`-group, stated without
installing its commutative and `ZMod p` structures globally. -/
structure IsElementaryAbelianGroup (p : ℕ) (G : Type u) [Group G] : Prop where
  isPGroup : IsPGroup p G
  commutative : IsMulCommutative G
  pow_eq_one : ∀ x : G, x ^ p = 1

/-- An elementary abelian subgroup of cardinal rank `n`. -/
structure IsElementaryAbelianOfRank (p n : ℕ) (E : Subgroup G) : Prop
    extends IsElementaryAbelianGroup p E where
  card_eq : Nat.card E = p ^ n

namespace IsElementaryAbelianOfRank

variable {p n : ℕ} {E : Subgroup G}

theorem one_lt_card [Fact p.Prime] (hE : IsElementaryAbelianOfRank p (n + 1) E) :
    1 < Nat.card E := by
  rw [hE.card_eq]
  exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (Nat.succ_ne_zero n)

theorem ne_bot [Fact p.Prime] [Finite G]
    (hE : IsElementaryAbelianOfRank p (n + 1) E) :
    E ≠ ⊥ :=
  E.one_lt_card_iff_ne_bot.mp hE.one_lt_card

end IsElementaryAbelianOfRank

/-- A group of cardinality `p²` and exponent dividing `p` is not cyclic. -/
theorem not_isCyclic_of_card_prime_sq_of_pow_eq_one
    [Finite G] {p : ℕ} (hp : p.Prime)
    (hcard : Nat.card G = p ^ 2) (hpow : ∀ x : G, x ^ p = 1) :
    ¬ IsCyclic G := by
  intro hcyclic
  letI : IsCyclic G := hcyclic
  letI := Fintype.ofFinite G
  classical
  have hle : Nat.card G ≤ p := by
    rw [Nat.card_eq_fintype_card]
    simpa only [hpow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := G) hp.pos)
  rw [hcard] at hle
  have hlt : p < p ^ 2 := by
    rw [pow_two]
    exact lt_mul_of_one_lt_right hp.pos hp.one_lt
  exact (not_lt_of_ge hle) hlt

theorem IsElementaryAbelianOfRank.not_isCyclic
    [Finite G] {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 2 E) : ¬ IsCyclic E :=
  not_isCyclic_of_card_prime_sq_of_pow_eq_one hp hE.card_eq hE.pow_eq_one

end Submission.OddOrder.MathlibSupport
