import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic
import Submission.OddOrder.MathlibSupport.CyclicRankCorrelation

/-!
The general numerical quasi-homocyclic rank-profile theorem.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]

omit [AddCommGroup A] in
/-- If all but one value of a finite profile equal `n`, its total differs
from `card A * n` by the same amount as the exceptional value. -/
theorem dist_sum_eq_card_mul_of_eq_except
    (rank : A -> Nat) (n : Nat) (i : A)
    (hi : Nat.dist (rank i) n = 1)
    (hothers : ∀ j : A, j ≠ i -> rank j = n) :
    Nat.dist (∑ j : A, rank j) (Fintype.card A * n) = 1 := by
  have hrest :
      ∑ j ∈ (Finset.univ.erase i), rank j =
        (Finset.univ.erase i).card * n := by
    calc
      ∑ j ∈ (Finset.univ.erase i), rank j =
          ∑ _j ∈ (Finset.univ.erase i), n := by
        apply Finset.sum_congr rfl
        intro j hj
        exact hothers j (Finset.ne_of_mem_erase hj)
      _ = (Finset.univ.erase i).card * n := by simp
  have hsum :
      ∑ j : A, rank j = rank i + (Fintype.card A - 1) * n := by
    calc
      ∑ j : A, rank j =
          ∑ j ∈ (Finset.univ.erase i), rank j + rank i :=
        (Finset.sum_erase_add Finset.univ rank
          (Finset.mem_univ i)).symm
      _ = rank i + (Fintype.card A - 1) * n := by
        rw [hrest]
        simp [add_comm]
  have hcard : 1 ≤ Fintype.card A :=
    Fintype.card_pos_iff.mpr ⟨i⟩
  have hbase :
      Fintype.card A * n = n + (Fintype.card A - 1) * n := by
    calc
      Fintype.card A * n = ((Fintype.card A - 1) + 1) * n := by
        rw [Nat.sub_add_cancel hcard]
      _ = n + (Fintype.card A - 1) * n := by
        rw [add_mul, one_mul, add_comm]
  rw [hsum, hbase, Nat.dist_add_add_right, hi]

/-- If every nonzero cyclic shift has squared-distance energy two, the
profile is constant except at one index, where it differs by one. -/
theorem general_quasiHomocyclic_rank_profile_of_energy
    (rank : A -> Nat) (hcard : 1 < Fintype.card A)
    (henergy : ∀ a : A, a ≠ 0 -> cyclicRankEnergy rank a = 2) :
    ∃ n : Nat, ∃ i : A,
      Nat.dist (∑ j : A, rank j) (Fintype.card A * n) = 1 ∧
      Nat.dist (rank i) n = 1 ∧
      ∀ j : A, j ≠ i -> rank j = n := by
  obtain ⟨x0, -, hx0⟩ :=
    Finset.exists_min_image Finset.univ rank Finset.univ_nonempty
  let r : A -> Nat := fun a => rank (x0 + a)
  let n : Nat := rank x0
  have hn_le (a : A) : n ≤ r a :=
    hx0 (x0 + a) (Finset.mem_univ _)
  have henergy_r (a : A) (ha : a ≠ 0) :
      cyclicRankEnergy r a = 2 := by
    rw [show cyclicRankEnergy r a = cyclicRankEnergy rank a by
      unfold cyclicRankEnergy
      exact Fintype.sum_equiv (Equiv.addLeft x0) _ _
        (fun x => by simp [r, add_assoc])]
    exact henergy a ha
  have hrange (a : A) : r a = n ∨ r a = n + 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · left
      simp [r, n]
    · have hterm :
          Nat.dist (r 0) (r (0 + a)) ^ 2 ≤
            cyclicRankEnergy r a := by
        exact Finset.single_le_sum
          (s := Finset.univ)
          (f := fun x : A => Nat.dist (r x) (r (x + a)) ^ 2)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (0 : A))
      rw [henergy_r a ha] at hterm
      have hr0 : r 0 = n := by simp [r, n]
      simp only [zero_add, hr0] at hterm
      rw [Nat.dist_eq_sub_of_le (hn_le a)] at hterm
      have hsub := Nat.sub_add_cancel (hn_le a)
      have hdiff : r a - n ≤ 1 := by nlinarith
      omega
  let b : A -> Nat := fun a => r a - n
  have hb_cases (a : A) : b a = 0 ∨ b a = 1 := by
    rcases hrange a with ha | ha <;> simp [b, ha]
  have hr_eq (a : A) : r a = n + b a := by
    rcases hrange a with ha | ha <;> simp [b, ha]
  have hb0 : b 0 = 0 := by
    simp [b, r, n]
  have henergy_b (a : A) (ha : a ≠ 0) :
      cyclicRankEnergy b a = 2 := by
    rw [show cyclicRankEnergy b a = cyclicRankEnergy r a by
      unfold cyclicRankEnergy
      apply Finset.sum_congr rfl
      intro x _
      rw [hr_eq x, hr_eq (x + a), Nat.dist_add_add_left]]
    exact henergy_r a ha
  have hsum_pos : 0 < ∑ a : A, b a := by
    have hsum_ne : (∑ a : A, b a) ≠ 0 := by
      intro hsum
      have hbzero (a : A) : b a = 0 := by
        have hle : b a ≤ ∑ x : A, b x :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (Finset.mem_univ a)
        omega
      obtain ⟨a, ha⟩ := Fintype.exists_ne_of_one_lt_card hcard 0
      have := henergy_b a ha
      simp [cyclicRankEnergy, hbzero] at this
    exact Nat.pos_of_ne_zero hsum_ne
  have hprofile :
      ∃ n' : Nat, ∃ i : A,
        Nat.dist (rank i) n' = 1 ∧
        ∀ j : A, j ≠ i -> rank j = n' := by
    by_cases hlarge : 1 < ∑ a : A, b a
    · obtain ⟨_, hb_nonzero⟩ :=
        quasiHomocyclic_rank_profile b hb0 hlarge henergy_b
      refine ⟨n + 1, x0, ?_, ?_⟩
      · simp [n, Nat.dist]
      · intro j hj
        have hshift : j - x0 ≠ 0 := sub_ne_zero.mpr hj
        have hb1 := hb_nonzero (j - x0) hshift
        have hrj := hr_eq (j - x0)
        simpa [r, hb1, add_comm] using hrj
    · have hsum_one : ∑ a : A, b a = 1 := by omega
      have hsum_ne : (∑ a : A, b a) ≠ 0 := by omega
      obtain ⟨i, -, hbi_ne⟩ :=
        Finset.exists_ne_zero_of_sum_ne_zero hsum_ne
      have hbi : b i = 1 := by
        rcases hb_cases i with hi | hi
        · exact (hbi_ne hi).elim
        · exact hi
      have hrest : ∑ a ∈ (Finset.univ.erase i), b a = 0 := by
        have hsplit := Finset.sum_erase_add Finset.univ b
          (Finset.mem_univ i)
        omega
      have hb_other (a : A) (ha : a ≠ i) : b a = 0 := by
        have hle : b a ≤ ∑ x ∈ (Finset.univ.erase i), b x :=
          Finset.single_le_sum (fun _ _ => Nat.zero_le _)
            (by simp [ha])
        omega
      refine ⟨n, x0 + i, ?_, ?_⟩
      · have hri := hr_eq i
        simp [r, hbi] at hri
        rw [hri]
        simp [Nat.dist]
      · intro j hj
        have hji : j - x0 ≠ i := by
          intro h
          apply hj
          calc
            j = x0 + (j - x0) := by abel
            _ = x0 + i := by rw [h]
        have hbj := hb_other (j - x0) hji
        have hrj := hr_eq (j - x0)
        simpa [r, hbj, add_comm] using hrj
  obtain ⟨n', i, hi, hothers⟩ := hprofile
  exact ⟨n', i,
    dist_sum_eq_card_mul_of_eq_except rank n' i hi hothers,
    hi, hothers⟩

/-- Correlation-drop form of the general quasi-homocyclic rank-profile
theorem. -/
theorem general_quasiHomocyclic_rank_profile_of_correlation
    (rank : A -> Nat) (hcard : 1 < Fintype.card A)
    (hdrop : ∀ a : A, a ≠ 0 ->
      cyclicRankCorrelation rank 0 = cyclicRankCorrelation rank a + 1) :
    ∃ n : Nat, ∃ i : A,
      Nat.dist (∑ j : A, rank j) (Fintype.card A * n) = 1 ∧
      Nat.dist (rank i) n = 1 ∧
      ∀ j : A, j ≠ i -> rank j = n := by
  apply general_quasiHomocyclic_rank_profile_of_energy rank hcard
  intro a ha
  exact cyclicRankEnergy_eq_two_of_correlation_eq_succ
    rank a (hdrop a ha)

end Submission.OddOrder.MathlibSupport
