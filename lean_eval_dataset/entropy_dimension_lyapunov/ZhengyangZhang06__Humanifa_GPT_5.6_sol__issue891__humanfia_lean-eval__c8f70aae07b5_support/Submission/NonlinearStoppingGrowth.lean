import Submission.NonlinearBlockGrowth

namespace Submission.Helpers

open Filter MeasureTheory

noncomputable def badCount (cheap : ℕ → Prop) (k m : ℕ) : ℝ := by
  classical
  exact ∑ j ∈ Finset.range m, if cheap (k + j) then 0 else 1

lemma badCount_nonneg (cheap : ℕ → Prop) (k m : ℕ) :
    0 ≤ badCount cheap k m := by
  classical
  apply Finset.sum_nonneg
  intro j hj
  split <;> norm_num

lemma badCount_add (cheap : ℕ → Prop) (k m n : ℕ) :
    badCount cheap k (m + n) =
      badCount cheap k m + badCount cheap (k + m) n := by
  classical
  simp only [badCount, Finset.sum_range_add]
  congr 1
  apply Finset.sum_congr rfl
  intro j hj
  rw [Nat.add_assoc]

lemma badCount_tail_le (cheap : ℕ → Prop) (k : ℕ)
    {m n : ℕ} (hnm : n ≤ m) :
    badCount cheap (k + n) (m - n) ≤ badCount cheap k m := by
  have hadd := badCount_add cheap k n (m - n)
  rw [Nat.add_sub_of_le hnm] at hadd
  rw [hadd]
  exact le_add_of_nonneg_left (badCount_nonneg cheap k n)

lemma badCount_succ_of_not (cheap : ℕ → Prop) (k m : ℕ)
    (hk : ¬cheap k) :
    badCount cheap k (m + 1) =
      1 + badCount cheap (k + 1) m := by
  classical
  rw [show m + 1 = 1 + m by omega, badCount_add]
  simp [badCount, hk]

lemma nonlinear_stopping_bound
    (d : ℕ → ℝ) (cheap : ℕ → Prop)
    {a eta B delta : ℝ} {N : ℕ}
    (hd : ∀ i, 0 ≤ d i) (hB : 0 ≤ B)
    (hN : 0 < N)
    (hcheap : ∀ k, d k ≤ delta → cheap k →
      ∃ n ∈ Finset.Icc 1 N,
        d (k + n) ≤ Real.exp ((a + eta) * n) * d k)
    (hshort : ∀ k n, 0 < n → n ≤ N → d k ≤ delta →
      d (k + n) ≤ Real.exp ((B + eta) * n) * d k) :
    ∀ k m : ℕ,
      (∀ j, j ≤ m → d k * Real.exp
        ((a + eta) * j + (B + |a|) * N +
          (B + |a|) * badCount cheap k j) ≤ delta) →
      d (k + m) ≤ Real.exp
          ((a + eta) * m + (B + |a|) * N +
            (B + |a|) * badCount cheap k m) * d k := by
  classical
  let C := B + |a|
  have hC : 0 ≤ C := add_nonneg hB (abs_nonneg a)
  change ∀ k m : ℕ,
    (∀ j, j ≤ m → d k * Real.exp
      ((a + eta) * j + C * N + C * badCount cheap k j) ≤ delta) →
      d (k + m) ≤ Real.exp
        ((a + eta) * m + C * N + C * badCount cheap k m) * d k
  intro k m hsmall
  induction m using Nat.strong_induction_on generalizing k with
  | h m ih =>
      have hCN_exp : 1 ≤ Real.exp (C * N) := by
        rw [← Real.exp_zero]
        apply Real.exp_le_exp.mpr
        exact mul_nonneg hC (Nat.cast_nonneg N)
      have hdk : d k ≤ delta := by
        have hzero := hsmall 0 (Nat.zero_le m)
        simp only [Nat.cast_zero, mul_zero, zero_add, badCount,
          Finset.range_zero, Finset.sum_empty, mul_zero, add_zero] at hzero
        exact (le_mul_of_one_le_right (hd k) hCN_exp).trans hzero
      by_cases hkcheap : cheap k
      · obtain ⟨n, hnIcc, hnstep⟩ := hcheap k hdk hkcheap
        have hn_pos : 0 < n := (Finset.mem_Icc.mp hnIcc).1
        have hnN : n ≤ N := (Finset.mem_Icc.mp hnIcc).2
        by_cases hnm : n ≤ m
        · have hm_pos : 0 < m := hn_pos.trans_le hnm
          have htail_lt : m - n < m := Nat.sub_lt hm_pos hn_pos
          have hsmall_tail : ∀ r, r ≤ m - n →
              d (k + n) * Real.exp
                ((a + eta) * r + C * N +
                  C * badCount cheap (k + n) r) ≤ delta := by
            intro r hr
            have hnr : n + r ≤ m := by omega
            have hbad_tail : badCount cheap (k + n) r ≤
                badCount cheap k (n + r) := by
              simpa using badCount_tail_le cheap k (m := n + r) (n := n)
                (Nat.le_add_right n r)
            have hexponent :
                (a + eta) * n +
                    ((a + eta) * r + C * N +
                      C * badCount cheap (k + n) r) ≤
                  (a + eta) * (n + r) + C * N +
                    C * badCount cheap k (n + r) := by
              nlinarith [mul_le_mul_of_nonneg_left hbad_tail hC]
            calc
              d (k + n) * Real.exp
                  ((a + eta) * r + C * N +
                    C * badCount cheap (k + n) r) ≤
                  (Real.exp ((a + eta) * n) * d k) *
                    Real.exp ((a + eta) * r + C * N +
                      C * badCount cheap (k + n) r) := by
                gcongr
              _ = d k * (Real.exp ((a + eta) * n) *
                    Real.exp ((a + eta) * r + C * N +
                      C * badCount cheap (k + n) r)) := by ring_nf
              _ = d k * Real.exp
                  ((a + eta) * n +
                    ((a + eta) * r + C * N +
                      C * badCount cheap (k + n) r)) := by
                exact congrArg (fun t : ℝ => d k * t)
                  (Real.exp_add ((a + eta) * n)
                    ((a + eta) * r + C * N +
                      C * badCount cheap (k + n) r)).symm
              _ ≤ d k * Real.exp
                  ((a + eta) * (n + r) + C * N +
                    C * badCount cheap k (n + r)) := by
                exact mul_le_mul_of_nonneg_left
                  (Real.exp_le_exp.mpr hexponent) (hd k)
              _ ≤ delta := by
                simpa only [Nat.cast_add] using hsmall (n + r) hnr
          have htail := ih (m - n) htail_lt (k + n) hsmall_tail
          have hbad_tail := badCount_tail_le cheap k hnm
          have hexponent :
              (a + eta) * ((m - n : ℕ) : ℝ) + C * N +
                  C * badCount cheap (k + n) (m - n) +
                    (a + eta) * n ≤
                (a + eta) * m + C * N + C * badCount cheap k m := by
            rw [Nat.cast_sub hnm]
            nlinarith [mul_le_mul_of_nonneg_left hbad_tail hC]
          calc
            d (k + m) = d ((k + n) + (m - n)) := by
              congr 1
              omega
            _ ≤ Real.exp
                  ((a + eta) * ((m - n : ℕ) : ℝ) + C * N +
                    C * badCount cheap (k + n) (m - n)) * d (k + n) := htail
            _ ≤ Real.exp
                  ((a + eta) * ((m - n : ℕ) : ℝ) + C * N +
                    C * badCount cheap (k + n) (m - n)) *
                  (Real.exp ((a + eta) * n) * d k) := by
              gcongr
            _ = Real.exp
                  ((a + eta) * ((m - n : ℕ) : ℝ) + C * N +
                    C * badCount cheap (k + n) (m - n) +
                      (a + eta) * n) * d k := by
              let X := (a + eta) * ((m - n : ℕ) : ℝ) + C * N +
                C * badCount cheap (k + n) (m - n)
              let Y := (a + eta) * n
              have hmul : Real.exp X * Real.exp Y = Real.exp (X + Y) :=
                (Real.exp_add X Y).symm
              have hsum : X + Y =
                  (a + eta) * ((m - n : ℕ) : ℝ) + C * N +
                    C * badCount cheap (k + n) (m - n) +
                      (a + eta) * n := by rfl
              change Real.exp X * (Real.exp Y * d k) = _
              rw [show Real.exp X * (Real.exp Y * d k) =
                (Real.exp X * Real.exp Y) * d k by ring_nf, hmul, hsum]
            _ ≤ Real.exp
                  ((a + eta) * m + C * N + C * badCount cheap k m) * d k := by
              exact mul_le_mul_of_nonneg_right
                (Real.exp_le_exp.mpr hexponent) (hd k)
        · have hm_lt_n : m < n := lt_of_not_ge hnm
          cases m with
          | zero =>
              have hCN : 1 ≤ Real.exp (C * N) := by
                rw [← Real.exp_zero]
                exact Real.exp_le_exp.mpr
                  (mul_nonneg hC (Nat.cast_nonneg N))
              simpa [badCount] using
                (mul_le_mul_of_nonneg_right hCN (hd k))
          | succ p =>
              have hm_pos : 0 < p + 1 := Nat.succ_pos p
              have hmN : p + 1 ≤ N := hm_lt_n.le.trans hnN
              have hstep := hshort k (p + 1) hm_pos hmN hdk
              have hcoef : B - a ≤ C := by
                dsimp [C]
                linarith [neg_abs_le a]
              have hbudget : (B - a) * ((p + 1 : ℕ) : ℝ) ≤ C * N := by
                exact mul_le_mul hcoef (by exact_mod_cast hmN)
                  (by positivity) hC
              have hexponent : (B + eta) * ((p + 1 : ℕ) : ℝ) ≤
                  (a + eta) * ((p + 1 : ℕ) : ℝ) + C * N +
                    C * badCount cheap k (p + 1) := by
                calc
                  (B + eta) * ((p + 1 : ℕ) : ℝ) =
                      (a + eta) * ((p + 1 : ℕ) : ℝ) +
                        (B - a) * ((p + 1 : ℕ) : ℝ) := by ring_nf
                  _ ≤ (a + eta) * ((p + 1 : ℕ) : ℝ) + C * N :=
                    by simpa [add_comm] using
                      add_le_add_left hbudget
                        ((a + eta) * ((p + 1 : ℕ) : ℝ))
                  _ ≤ (a + eta) * ((p + 1 : ℕ) : ℝ) + C * N +
                      C * badCount cheap k (p + 1) :=
                    le_add_of_nonneg_right
                      (mul_nonneg hC (badCount_nonneg cheap k (p + 1)))
              calc
                d (k + (p + 1)) ≤
                    Real.exp ((B + eta) * ((p + 1 : ℕ) : ℝ)) * d k := by
                  simpa [Nat.cast_add, Nat.cast_one] using hstep
                _ ≤ Real.exp
                    ((a + eta) * ((p + 1 : ℕ) : ℝ) + C * N +
                      C * badCount cheap k (p + 1)) * d k := by
                  exact mul_le_mul_of_nonneg_right
                    (Real.exp_le_exp.mpr hexponent) (hd k)
      · cases m with
        | zero =>
            have hCN : 1 ≤ Real.exp (C * N) := by
              rw [← Real.exp_zero]
              exact Real.exp_le_exp.mpr
                (mul_nonneg hC (Nat.cast_nonneg N))
            simpa [badCount] using
              (mul_le_mul_of_nonneg_right hCN (hd k))
        | succ p =>
            have honeN : 1 ≤ N := hN
            have hstep := hshort k 1 (by omega) honeN hdk
            have hB_le : B ≤ a + C := by
              dsimp [C]
              linarith [neg_abs_le a]
            have hstep_coarse : d (k + 1) ≤
                Real.exp (a + C + eta) * d k := by
              calc
                d (k + 1) ≤ Real.exp ((B + eta) * 1) * d k := by
                  simpa using hstep
                _ ≤ Real.exp (a + C + eta) * d k := by
                  exact mul_le_mul_of_nonneg_right
                    (Real.exp_le_exp.mpr (by linarith)) (hd k)
            have hsmall_tail : ∀ r, r ≤ p →
                d (k + 1) * Real.exp
                  ((a + eta) * r + C * N +
                    C * badCount cheap (k + 1) r) ≤ delta := by
              intro r hr
              have hr_succ : r + 1 ≤ p + 1 := by omega
              have hbad : badCount cheap k (r + 1) =
                  1 + badCount cheap (k + 1) r :=
                badCount_succ_of_not cheap k r hkcheap
              calc
                d (k + 1) * Real.exp
                    ((a + eta) * r + C * N +
                      C * badCount cheap (k + 1) r) ≤
                    (Real.exp (a + C + eta) * d k) *
                      Real.exp ((a + eta) * r + C * N +
                        C * badCount cheap (k + 1) r) := by
                  gcongr
                _ = d k * (Real.exp (a + C + eta) *
                      Real.exp ((a + eta) * r + C * N +
                        C * badCount cheap (k + 1) r)) := by ring_nf
                _ = d k * Real.exp
                    ((a + eta) * (r + 1) + C * N +
                      C * badCount cheap k (r + 1)) := by
                  rw [hbad]
                  rw [← Real.exp_add]
                  congr 1
                  norm_num [Nat.cast_add]
                  ring_nf
                _ ≤ delta := by
                  simpa only [Nat.cast_add, Nat.cast_one] using
                    hsmall (r + 1) hr_succ
            have htail := ih p (Nat.lt_succ_self p) (k + 1) hsmall_tail
            rw [badCount_succ_of_not cheap k p hkcheap]
            calc
              d (k + (p + 1)) = d ((k + 1) + p) := by
                congr 1
                omega
              _ ≤ Real.exp
                    ((a + eta) * p + C * N +
                      C * badCount cheap (k + 1) p) * d (k + 1) := htail
              _ ≤ Real.exp
                    ((a + eta) * p + C * N +
                      C * badCount cheap (k + 1) p) *
                    (Real.exp (a + C + eta) * d k) := by
                gcongr
              _ = (Real.exp
                    ((a + eta) * p + C * N +
                      C * badCount cheap (k + 1) p) *
                    Real.exp (a + C + eta)) * d k := by ring_nf
              _ = Real.exp
                    ((a + eta) * ((p + 1 : ℕ) : ℝ) + C * N +
                      C * (1 + badCount cheap (k + 1) p)) * d k := by
                let X := (a + eta) * p + C * N +
                  C * badCount cheap (k + 1) p
                let Y := a + C + eta
                have hmul : Real.exp X * Real.exp Y = Real.exp (X + Y) :=
                  (Real.exp_add X Y).symm
                have hsum : X + Y =
                    (a + eta) * ((p + 1 : ℕ) : ℝ) + C * N +
                      C * (1 + badCount cheap (k + 1) p) := by
                  dsimp [X, Y]
                  simp only [Nat.cast_add, Nat.cast_one]
                  ring_nf
                change (Real.exp X * Real.exp Y) * d k = _
                rw [hmul, hsum]

end Submission.Helpers
