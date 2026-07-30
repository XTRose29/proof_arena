import Submission.Frostman

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open scoped ENNReal

lemma le_dimMeasure_of_geometric_closedBall_le
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    {carrier s : Set EucPlane}
    (hs_measurable : MeasurableSet s) (hmu_s : mu s ≠ 0)
    (hs_carrier : s ⊆ carrier) (hcarrier_dim : dimH carrier = dimMeasure mu)
    (d : NNReal) (hd : 0 < d)
    {A rho : ℝ} (hA : 0 < A) (hrho_pos : 0 < rho) (hrho_lt_one : rho < 1)
    (N : ℕ) (hzero : ∀ x ∈ s, mu {x} = 0)
    (hscale : ∀ x ∈ s, ∀ n, N ≤ n →
      mu (Metric.closedBall x (A * rho ^ n)) ≤
        ENNReal.ofReal (A * rho ^ (n + 1)) ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimMeasure mu := by
  have hbase_pos : 0 < A * rho ^ N := mul_pos hA (pow_pos hrho_pos N)
  apply le_dimMeasure_of_positive_subset_closedBall_le mu hs_measurable hmu_s
    hs_carrier hcarrier_dim d (ENNReal.ofReal_pos.mpr hbase_pos)
  intro x hx r hr
  have hr_top : r ≠ ∞ := by
    exact ne_top_of_le_ne_top ENNReal.ofReal_ne_top hr
  by_cases hr_zero : r = 0
  · subst r
    rw [Metric.closedEBall_zero, hzero x hx]
    exact bot_le
  have hr_real_pos : 0 < r.toReal := ENNReal.toReal_pos hr_zero hr_top
  have hr_real_le : r.toReal ≤ A * rho ^ N := by
    have hle := (ENNReal.toReal_le_toReal hr_top ENNReal.ofReal_ne_top).2 hr
    simpa [ENNReal.toReal_ofReal hbase_pos.le] using hle
  let z := r.toReal / (A * rho ^ N)
  have hz_pos : 0 < z := div_pos hr_real_pos hbase_pos
  have hz_le_one : z ≤ 1 := (div_le_one hbase_pos).2 hr_real_le
  obtain ⟨k, hk_lower, hk_upper⟩ :=
    exists_nat_pow_near_of_lt_one hz_pos hz_le_one hrho_pos hrho_lt_one
  have hnext : A * rho ^ (N + k + 1) < r.toReal := by
    have hmul : rho ^ (k + 1) * (A * rho ^ N) < r.toReal :=
      (lt_div_iff₀ hbase_pos).mp hk_lower
    calc
      A * rho ^ (N + k + 1) = rho ^ (k + 1) * (A * rho ^ N) := by
        rw [show N + k + 1 = N + (k + 1) by omega, pow_add]
        ring
      _ < r.toReal := hmul
  have hcurrent : r.toReal ≤ A * rho ^ (N + k) := by
    have hmul : r.toReal ≤ rho ^ k * (A * rho ^ N) :=
      (div_le_iff₀ hbase_pos).mp hk_upper
    calc
      r.toReal ≤ rho ^ k * (A * rho ^ N) := hmul
      _ = A * rho ^ (N + k) := by
        rw [pow_add]
        ring
  rw [← ENNReal.ofReal_toReal hr_top,
    Metric.closedEBall_ofReal ENNReal.toReal_nonneg]
  calc
    mu (Metric.closedBall x r.toReal) ≤
        mu (Metric.closedBall x (A * rho ^ (N + k))) := by
      apply measure_mono
      intro y hy
      rw [Metric.mem_closedBall] at hy ⊢
      exact hy.trans hcurrent
    _ ≤ ENNReal.ofReal (A * rho ^ (N + k + 1)) ^ (d : ℝ) :=
      hscale x hx (N + k) (Nat.le_add_right N k)
    _ ≤ ENNReal.ofReal r.toReal ^ (d : ℝ) := by
      exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal hnext.le)
        (by exact_mod_cast hd.le)

lemma le_dimMeasure_of_exponential_closedBall_le
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    {carrier s : Set EucPlane}
    (hs_measurable : MeasurableSet s) (hmu_s : mu s ≠ 0)
    (hs_carrier : s ⊆ carrier) (hcarrier_dim : dimH carrier = dimMeasure mu)
    (d : NNReal) (hd : 0 < d)
    {R h : ℝ} (hR : 0 < R) (N : ℕ)
    (hbudget : ∀ n, N ≤ n → R * (d : ℝ) * (n + 1 : ℕ) ≤ h * n)
    (hzero : ∀ x ∈ s, mu {x} = 0)
    (hball : ∀ x ∈ s, ∀ n, N ≤ n →
      mu (Metric.closedBall x (Real.exp (-R * n))) ≤
        ENNReal.ofReal (Real.exp (-h * n))) :
    (d : ℝ≥0∞) ≤ dimMeasure mu := by
  let rho := Real.exp (-R)
  have hrho_pos : 0 < rho := Real.exp_pos _
  have hrho_lt_one : rho < 1 := by
    rw [show (1 : ℝ) = Real.exp 0 by simp, Real.exp_lt_exp]
    linarith
  apply le_dimMeasure_of_geometric_closedBall_le
    (A := 1) (rho := rho) mu hs_measurable hmu_s
      hs_carrier hcarrier_dim d hd (by positivity) hrho_pos hrho_lt_one N hzero
  intro x hx n hn
  have hradius : rho ^ n = Real.exp (-R * n) := by
    rw [← Real.exp_nat_mul]
    congr 1
    ring
  rw [one_mul, hradius]
  calc
    mu (Metric.closedBall x (Real.exp (-R * n))) ≤
        ENNReal.ofReal (Real.exp (-h * n)) := hball x hx n hn
    _ ≤ ENNReal.ofReal (rho ^ (n + 1)) ^ (d : ℝ) := by
      rw [ENNReal.ofReal_rpow_of_pos (pow_pos hrho_pos (n + 1))]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_def_of_pos (pow_pos hrho_pos (n + 1))]
      rw [Real.log_pow, show Real.log rho = -R by simp [rho]]
      rw [Real.exp_le_exp]
      have := hbudget n hn
      norm_num [Nat.cast_add, Nat.cast_one] at this ⊢
      linarith
    _ = ENNReal.ofReal (1 * rho ^ (n + 1)) ^ (d : ℝ) := by rw [one_mul]

lemma exists_nat_exponential_budget
    (d : NNReal) (hd : 0 < d) {R h : ℝ} (hR : 0 < R)
    (hrate : R * (d : ℝ) < h) :
    ∃ N, ∀ n, N ≤ n →
      R * (d : ℝ) * (n + 1 : ℕ) ≤ h * n := by
  let a := R * (d : ℝ)
  let gap := h - a
  have ha_pos : 0 < a := mul_pos hR (by exact_mod_cast hd)
  have hgap_pos : 0 < gap := sub_pos.mpr hrate
  obtain ⟨N, hN⟩ := exists_nat_ge (a / gap)
  refine ⟨N, fun n hn => ?_⟩
  have ha_le_N : a ≤ gap * (N : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hgap_pos).mp hN
  have hN_le_n : gap * (N : ℝ) ≤ gap * (n : ℝ) := by
    exact mul_le_mul_of_nonneg_left (by exact_mod_cast hn) hgap_pos.le
  have ha_le_n : a ≤ gap * (n : ℝ) := ha_le_N.trans hN_le_n
  dsimp [a, gap] at ha_pos hgap_pos hrate ⊢
  norm_num [Nat.cast_add, Nat.cast_one] at ha_le_n ⊢
  linarith

end Submission.Helpers
