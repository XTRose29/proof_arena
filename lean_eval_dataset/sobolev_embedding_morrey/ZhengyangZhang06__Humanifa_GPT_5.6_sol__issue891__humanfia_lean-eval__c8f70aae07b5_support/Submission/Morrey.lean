import ChallengeDeps

namespace Submission.Morrey

open LeanEval.Analysis.SobolevMorreyProblem
open MeasureTheory Filter
open scoped ENNReal NNReal Topology

noncomputable def scale (j : ℕ) : ℝ :=
  (1 / 2 : ℝ) ^ j

theorem scale_pos (j : ℕ) : 0 < scale j := by
  exact pow_pos (by norm_num) _

theorem tendsto_scale : Tendsto scale atTop (𝓝 0) := by
  exact tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num) (by norm_num)

noncomputable def conjugateExponent (p : ℝ) : ℝ :=
  p / (p - 1)

noncomputable def morreyExponent (n : ℕ) (p : ℝ) : ℝ :=
  1 - n / p

theorem holderConjugate_conjugateExponent {p : ℝ} (hp : 1 < p) :
    p.HolderConjugate (conjugateExponent p) := by
  exact Real.HolderConjugate.conjExponent hp

theorem morreyExponent_pos {n : ℕ} {p : ℝ} (_hn : 0 < n) (hp : (n : ℝ) < p) :
    0 < morreyExponent n p := by
  have hp0 : 0 < p := (Nat.cast_nonneg n).trans_lt hp
  rw [morreyExponent, sub_pos, div_lt_one hp0]
  exact hp

theorem integral_norm_ball_le {n : ℕ} {p q : ℝ} (hpq : p.HolderConjugate q)
    {g : E n → ℝ} (hg : MemLp g (ENNReal.ofReal p) volume) (x : E n) (t : ℝ) :
    ∫ y in Metric.ball x t, ‖g y‖ ≤
      volume.real (Metric.ball x t) ^ (1 / q) *
        (∫ y, ‖g y‖ ^ p) ^ (1 / p) := by
  let χ : E n → ℝ := (Metric.ball x t).indicator fun _ ↦ 1
  have hχ : MemLp χ (ENNReal.ofReal q) volume := by
    apply memLp_indicator_const
    · exact measurableSet_ball
    · exact Or.inr measure_ball_lt_top.ne
  have h := integral_mul_norm_le_Lp_mul_Lq hpq hg hχ
  have hleft :
      ∫ y in Metric.ball x t, ‖g y‖ =
        ∫ y, ‖g y‖ * ‖χ y‖ := by
    rw [← integral_indicator measurableSet_ball]
    apply integral_congr_ae
    filter_upwards [] with y
    by_cases hy : y ∈ Metric.ball x t <;> simp [χ, hy]
  have hχpow (y : E n) :
      ‖χ y‖ ^ q = (Metric.ball x t).indicator (fun _ ↦ (1 : ℝ)) y := by
    by_cases hy : y ∈ Metric.ball x t
    · simp [χ, hy]
    · simp [χ, hy, Real.zero_rpow hpq.symm.pos.ne']
  have hright :
      ∫ y, ‖χ y‖ ^ q = volume.real (Metric.ball x t) := by
    calc
      ∫ y, ‖χ y‖ ^ q =
          ∫ y, (Metric.ball x t).indicator (fun _ ↦ (1 : ℝ)) y := by
            exact integral_congr_ae (Eventually.of_forall hχpow)
      _ = volume.real (Metric.ball x t) :=
        integral_indicator_one measurableSet_ball
  calc
    ∫ y in Metric.ball x t, ‖g y‖ =
        ∫ y, ‖g y‖ * ‖χ y‖ := hleft
    _ ≤ (∫ y, ‖g y‖ ^ p) ^ (1 / p) *
        (∫ y, ‖χ y‖ ^ q) ^ (1 / q) := h
    _ = volume.real (Metric.ball x t) ^ (1 / q) *
        (∫ y, ‖g y‖ ^ p) ^ (1 / p) := by
          rw [hright]
          ring

end Submission.Morrey
