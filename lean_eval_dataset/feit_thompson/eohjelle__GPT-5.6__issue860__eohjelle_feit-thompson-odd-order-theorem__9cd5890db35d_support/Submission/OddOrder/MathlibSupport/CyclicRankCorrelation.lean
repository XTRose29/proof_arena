import Mathlib.Data.Nat.Dist
import Mathlib.Tactic
import Submission.OddOrder.MathlibSupport.QuasiHomocyclicRanks

/-!
Correlation and squared-distance energy for finite cyclic rank profiles.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A]

/-- Cyclic autocorrelation of a natural-valued profile at a shift. -/
def cyclicRankCorrelation (rank : A -> Nat) (a : A) : Nat :=
  ∑ x : A, rank x * rank (x + a)

/-- Squared-distance energy of a natural-valued profile at a shift. -/
def cyclicRankEnergy (rank : A -> Nat) (a : A) : Nat :=
  ∑ x : A, Nat.dist (rank x) (rank (x + a)) ^ 2

/-- The pointwise polarization identity for natural-number distance. -/
theorem two_mul_add_dist_sq (m n : Nat) :
    2 * (m * n) + Nat.dist m n ^ 2 = m ^ 2 + n ^ 2 := by
  rcases le_total m n with hmn | hnm
  · rw [Nat.dist_eq_sub_of_le hmn]
    have hsub := Nat.sub_add_cancel hmn
    nlinarith
  · rw [Nat.dist_eq_sub_of_le_right hnm]
    have hsub := Nat.sub_add_cancel hnm
    nlinarith

/-- Zero-shift correlation exceeds shifted correlation by half the
squared-distance energy. -/
theorem two_mul_cyclicRankCorrelation_zero
    (rank : A -> Nat) (a : A) :
    2 * cyclicRankCorrelation rank 0 =
      2 * cyclicRankCorrelation rank a + cyclicRankEnergy rank a := by
  have hsum :
      ∑ x : A,
          (2 * (rank x * rank (x + a)) +
            Nat.dist (rank x) (rank (x + a)) ^ 2) =
        ∑ x : A, (rank x ^ 2 + rank (x + a) ^ 2) := by
    apply Finset.sum_congr rfl
    intro x _
    exact two_mul_add_dist_sq (rank x) (rank (x + a))
  rw [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_add_distrib] at hsum
  have hshift :
      ∑ x : A, rank (x + a) ^ 2 = ∑ x : A, rank x ^ 2 :=
    Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)
  rw [hshift] at hsum
  simpa [cyclicRankCorrelation, cyclicRankEnergy, pow_two,
    two_mul, add_assoc, add_comm, add_left_comm] using hsum.symm

/-- A one-dimensional drop in cyclic correlation is equivalent to
squared-distance energy two in the direction needed here. -/
theorem cyclicRankEnergy_eq_two_of_correlation_eq_succ
    (rank : A -> Nat) (a : A)
    (hdrop : cyclicRankCorrelation rank 0 =
      cyclicRankCorrelation rank a + 1) :
    cyclicRankEnergy rank a = 2 := by
  have hpolarization := two_mul_cyclicRankCorrelation_zero rank a
  nlinarith

/-- Correlation drops by one at every nonzero shift force the
quasi-homocyclic rank profile. -/
theorem quasiHomocyclic_rank_profile_of_correlation
    [DecidableEq A]
    (rank : A -> Nat) (hrank_zero : rank 0 = 0)
    (htotal : 1 < ∑ x : A, rank x)
    (hdrop : ∀ a : A, a ≠ 0 ->
      cyclicRankCorrelation rank 0 = cyclicRankCorrelation rank a + 1) :
    Fintype.card A = (∑ x : A, rank x) + 1 ∧
      ∀ a : A, a ≠ 0 -> rank a = 1 := by
  apply quasiHomocyclic_rank_profile rank hrank_zero htotal
  intro a ha
  exact cyclicRankEnergy_eq_two_of_correlation_eq_succ rank a (hdrop a ha)

end Submission.OddOrder.MathlibSupport
