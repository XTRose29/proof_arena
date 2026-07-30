import Mathlib

namespace Submission.Helpers

open Finset

def windowSum (a : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ∑ j ∈ range n, a (k + j)

def HasPositiveWindow (a : ℕ → ℝ) (N k : ℕ) : Prop :=
  ∃ n, 0 < n ∧ n ≤ N ∧ 0 < windowSum a k n

lemma windowSum_zero (a : ℕ → ℝ) (k : ℕ) :
    windowSum a k 0 = 0 := by
  simp [windowSum]

lemma windowSum_add (a : ℕ → ℝ) (k m n : ℕ) :
    windowSum a k (m + n) =
      windowSum a k m + windowSum a (k + m) n := by
  simp only [windowSum, sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  simp [Nat.add_assoc]

lemma windowSum_shift (a : ℕ → ℝ) (q k n : ℕ) :
    windowSum (fun j => a (q + j)) k n = windowSum a (q + k) n := by
  unfold windowSum
  apply Finset.sum_congr rfl
  intro j hj
  simp [Nat.add_assoc]

lemma hasPositiveWindow_shift (a : ℕ → ℝ) (N q k : ℕ) :
    HasPositiveWindow (fun j => a (q + j)) N k ↔
      HasPositiveWindow a N (q + k) := by
  simp only [HasPositiveWindow, windowSum_shift]

noncomputable def firstPositiveWindow
    (a : ℕ → ℝ) (N k : ℕ) (h : HasPositiveWindow a N k) : ℕ :=
  Nat.find h

lemma firstPositiveWindow_pos
    (a : ℕ → ℝ) (N k : ℕ) (h : HasPositiveWindow a N k) :
    0 < firstPositiveWindow a N k h := by
  exact (Nat.find_spec h).1

lemma firstPositiveWindow_le
    (a : ℕ → ℝ) (N k : ℕ) (h : HasPositiveWindow a N k) :
    firstPositiveWindow a N k h ≤ N := by
  exact (Nat.find_spec h).2.1

lemma firstPositiveWindow_sum_pos
    (a : ℕ → ℝ) (N k : ℕ) (h : HasPositiveWindow a N k) :
    0 < windowSum a k (firstPositiveWindow a N k h) := by
  exact (Nat.find_spec h).2.2

lemma windowSum_le_zero_of_lt_firstPositiveWindow
    (a : ℕ → ℝ) (N k : ℕ) (h : HasPositiveWindow a N k)
    {j : ℕ} (hj : j < firstPositiveWindow a N k h) :
    windowSum a k j ≤ 0 := by
  by_cases hjzero : j = 0
  · simp [hjzero, windowSum_zero]
  · by_contra hsum
    have hsum_pos : 0 < windowSum a k j := lt_of_not_ge hsum
    have hjpos : 0 < j := Nat.pos_of_ne_zero hjzero
    have hjN : j ≤ N :=
      hj.le.trans (firstPositiveWindow_le a N k h)
    exact (not_lt_of_ge (Nat.find_min' h ⟨hjpos, hjN, hsum_pos⟩)) hj

lemma hasPositiveWindow_add_of_lt_firstPositiveWindow
    (a : ℕ → ℝ) (N k : ℕ) (h : HasPositiveWindow a N k)
    {j : ℕ} (hj : j < firstPositiveWindow a N k h) :
    HasPositiveWindow a N (k + j) := by
  let n := firstPositiveWindow a N k h
  have hjn : j ≤ n := hj.le
  have htail_pos : 0 < windowSum a (k + j) (n - j) := by
    have hadd := windowSum_add a k j (n - j)
    rw [Nat.add_sub_of_le hjn] at hadd
    have htotal : 0 < windowSum a k n := by
      exact firstPositiveWindow_sum_pos a N k h
    rw [hadd] at htotal
    linarith [windowSum_le_zero_of_lt_firstPositiveWindow a N k h hj]
  refine ⟨n - j, Nat.sub_pos_of_lt hj, ?_, htail_pos⟩
  exact (Nat.sub_le n j).trans (firstPositiveWindow_le a N k h)

noncomputable def selectedWindowSum (a : ℕ → ℝ) (N m : ℕ) : ℝ := by
  classical
  exact ∑ k ∈ range m, if HasPositiveWindow a N k then a k else 0

lemma selectedWindowSum_add (a : ℕ → ℝ) (N m n : ℕ) :
    selectedWindowSum a N (m + n) =
      selectedWindowSum a N m +
        selectedWindowSum (fun j => a (m + j)) N n := by
  classical
  simp [selectedWindowSum, sum_range_add, hasPositiveWindow_shift]

lemma selectedWindowSum_eq_windowSum_of_all
    (a : ℕ → ℝ) (N m : ℕ)
    (h : ∀ k < m, HasPositiveWindow a N k) :
    selectedWindowSum a N m = windowSum a 0 m := by
  classical
  unfold selectedWindowSum windowSum
  apply Finset.sum_congr rfl
  intro k hk
  rw [if_pos (h k (Finset.mem_range.mp hk))]
  simp

lemma neg_mul_le_windowSum
    (a : ℕ → ℝ) {B : ℝ}
    (ha : ∀ k, -B ≤ a k) (k m : ℕ) :
    -(m : ℝ) * B ≤ windowSum a k m := by
  calc
    -(m : ℝ) * B = ∑ _j ∈ range m, -B := by simp
    _ ≤ ∑ j ∈ range m, a (k + j) := by
      apply Finset.sum_le_sum
      intro j hj
      exact ha (k + j)
    _ = windowSum a k m := by rfl

theorem neg_mul_le_selectedWindowSum_of_lowerBound
    (a : ℕ → ℝ) (N m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ k, -B ≤ a k) :
    -(N : ℝ) * B ≤ selectedWindowSum a N m := by
  classical
  induction m using Nat.strong_induction_on generalizing a with
  | h m ih =>
      by_cases hzero : m = 0
      · subst m
        simp only [selectedWindowSum, range_zero, sum_empty]
        nlinarith [mul_nonneg (Nat.cast_nonneg N) hB]
      by_cases hpos : HasPositiveWindow a N 0
      · let l := firstPositiveWindow a N 0 hpos
        have hlpos : 0 < l := firstPositiveWindow_pos a N 0 hpos
        have hlN : l ≤ N := firstPositiveWindow_le a N 0 hpos
        by_cases hlm : l ≤ m
        · have hmlt : m - l < m := Nat.sub_lt (Nat.pos_of_ne_zero hzero) hlpos
          have hfirst_all : ∀ k < l, HasPositiveWindow a N k := by
            intro k hk
            simpa using hasPositiveWindow_add_of_lt_firstPositiveWindow
              a N 0 hpos hk
          have hfirst_pos : 0 < selectedWindowSum a N l := by
            rw [selectedWindowSum_eq_windowSum_of_all a N l hfirst_all]
            simpa [l] using firstPositiveWindow_sum_pos a N 0 hpos
          have htail := ih (m - l) hmlt (fun j => a (l + j))
            (fun k => by simpa using ha (l + k))
          have hsplit := selectedWindowSum_add a N l (m - l)
          rw [Nat.add_sub_of_le hlm] at hsplit
          rw [hsplit]
          linarith
        · have hml : m < l := Nat.lt_of_not_ge hlm
          have hmN : m ≤ N := hml.le.trans hlN
          have hall : ∀ k < m, HasPositiveWindow a N k := by
            intro k hk
            simpa using hasPositiveWindow_add_of_lt_firstPositiveWindow
              a N 0 hpos (hk.trans hml)
          rw [selectedWindowSum_eq_windowSum_of_all a N m hall]
          have hbound := neg_mul_le_windowSum a ha 0 m
          have hcast : (m : ℝ) ≤ N := by exact_mod_cast hmN
          nlinarith
      · have hmpos : 0 < m := Nat.pos_of_ne_zero hzero
        have hpred : m - 1 < m := Nat.sub_lt hmpos zero_lt_one
        have htail := ih (m - 1) hpred (fun j => a (1 + j))
          (fun k => by simpa using ha (1 + k))
        have hsplit := selectedWindowSum_add a N 1 (m - 1)
        rw [Nat.add_sub_of_le hmpos] at hsplit
        have hfirst : selectedWindowSum a N 1 = 0 := by
          simp [selectedWindowSum, hpos]
        rw [hsplit, hfirst, zero_add]
        exact htail

theorem neg_mul_le_selectedWindowSum
    (a : ℕ → ℝ) (N m : ℕ) {B : ℝ} (hB : 0 ≤ B)
    (ha : ∀ k, |a k| ≤ B) :
    -(N : ℝ) * B ≤ selectedWindowSum a N m :=
  neg_mul_le_selectedWindowSum_of_lowerBound a N m hB
    (fun k => neg_le_of_abs_le (ha k))

end Submission.Helpers
