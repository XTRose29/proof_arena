import ChallengeDeps

open LeanEval.Analysis.ODE
open Real MeasureTheory ProbabilityTheory Filter Set
open scoped NNReal

namespace Submission.Helpers

noncomputable def heatVariance (t : ℝ) : ℝ≥0 :=
  Real.toNNReal (2 * t)

lemma heatVariance_coe {t : ℝ} (ht : 0 < t) : (heatVariance t : ℝ) = 2 * t := by
  rw [heatVariance, Real.coe_toNNReal]
  positivity

lemma heatVariance_ne_zero {t : ℝ} (ht : 0 < t) : heatVariance t ≠ 0 := by
  intro h
  have hc := congrArg (fun v : ℝ≥0 ↦ (v : ℝ)) h
  rw [heatVariance_coe ht, NNReal.coe_zero] at hc
  linarith

noncomputable def heatCoefficient (t : ℝ) : ℝ :=
  (4 * Real.pi * t)⁻¹ ^ ((1 : ℝ) / 2)

noncomputable def heatKernel (t x y : ℝ) : ℝ :=
  heatCoefficient t *
    Real.exp (-((x - y) ^ 2) / (4 * t))

lemma heatKernel_eq_gaussianPDFReal {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    heatKernel t x y = gaussianPDFReal x (heatVariance t) y := by
  rw [heatKernel, heatCoefficient, gaussianPDFReal, heatVariance_coe ht]
  have hbase : 0 ≤ 4 * Real.pi * t := by positivity
  rw [Real.inv_rpow hbase, ← Real.sqrt_eq_rpow]
  rw [show 2 * Real.pi * (2 * t) = 4 * Real.pi * t by ring]
  rw [show 2 * (2 * t) = 4 * t by ring]
  congr 2
  ring

noncomputable def heatKernelX (t x y : ℝ) : ℝ :=
  (-(x - y) / (2 * t)) * heatKernel t x y

noncomputable def heatKernelXX (t x y : ℝ) : ℝ :=
  ((x - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)) * heatKernel t x y

lemma hasDerivAt_heatKernel_space {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun z ↦ heatKernel t z y) (heatKernelX t x y) x := by
  have hq : HasDerivAt (fun z : ℝ ↦ -((z - y) ^ 2) / (4 * t))
      (-(x - y) / (2 * t)) x := by
    convert ((((hasDerivAt_id x).sub_const y).pow 2).neg.div_const (4 * t)) using 1
    all_goals try funext z
    all_goals try simp only [id]
    all_goals try field_simp [ht.ne']
    all_goals first | rfl | ring
  simp only [heatKernelX, heatKernel]
  convert hq.exp.const_mul (heatCoefficient t) using 1
  all_goals first | rfl | ring

lemma hasDerivAt_heatKernelX_space {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun z ↦ heatKernelX t z y) (heatKernelXX t x y) x := by
  have hlin : HasDerivAt (fun z : ℝ ↦ -(z - y) / (2 * t)) (-1 / (2 * t)) x := by
    convert ((hasDerivAt_id x).sub_const y).neg.div_const (2 * t) using 1
    all_goals try funext z
    all_goals try simp only [id]
    all_goals try field_simp [ht.ne']
    all_goals rfl
  simp only [heatKernelX, heatKernelXX]
  convert hlin.mul (hasDerivAt_heatKernel_space ht x y) using 1
  all_goals try funext z
  all_goals try simp only [heatKernelX, Pi.mul_apply]
  all_goals try field_simp [ht.ne']
  all_goals first | rfl | ring

lemma heatCoefficient_eq_rpow_neg (t : ℝ) :
    heatCoefficient t = (4 * Real.pi * t) ^ (-((1 : ℝ) / 2)) := by
  exact (Real.rpow_neg_eq_inv_rpow (4 * Real.pi * t) ((1 : ℝ) / 2)).symm

lemma hasDerivAt_heatCoefficient {t : ℝ} (ht : 0 < t) :
    HasDerivAt heatCoefficient (-heatCoefficient t / (2 * t)) t := by
  have hbase : HasDerivAt (fun s : ℝ ↦ 4 * Real.pi * s) (4 * Real.pi) t := by
    simpa using (hasDerivAt_id t).const_mul (4 * Real.pi)
  have hpos : 0 < 4 * Real.pi * t := by positivity
  rw [show heatCoefficient = fun s : ℝ ↦ (4 * Real.pi * s) ^ (-((1 : ℝ) / 2)) by
    funext s
    exact heatCoefficient_eq_rpow_neg s]
  convert hbase.rpow_const (Or.inl hpos.ne') using 1
  rw [show -((1 : ℝ) / 2) - 1 = -((1 : ℝ) / 2) + (-1) by ring,
    Real.rpow_add hpos, Real.rpow_neg_one]
  dsimp only
  field_simp [ht.ne', Real.pi_ne_zero]

lemma hasDerivAt_heatKernel_time {t : ℝ} (ht : 0 < t) (x y : ℝ) :
    HasDerivAt (fun s ↦ heatKernel s x y) (heatKernelXX t x y) t := by
  have hden : HasDerivAt (fun s : ℝ ↦ 4 * s) 4 t := by
    simpa using (hasDerivAt_id t).const_mul 4
  have hq : HasDerivAt (fun s : ℝ ↦ -((x - y) ^ 2) / (4 * s))
      ((x - y) ^ 2 / (4 * t ^ 2)) t := by
    have hraw := (hasDerivAt_const t (-((x - y) ^ 2))).div hden (by positivity)
    convert hraw using 1
    all_goals first | rfl | ring
  simp only [heatKernelXX, heatKernel]
  convert (hasDerivAt_heatCoefficient ht).mul hq.exp using 1
  all_goals first | rfl | ring

lemma heatCoefficient_pos {t : ℝ} (ht : 0 < t) : 0 < heatCoefficient t := by
  rw [heatCoefficient_eq_rpow_neg]
  exact Real.rpow_pos_of_pos (by positivity) _

lemma heatKernel_nonneg {t : ℝ} (ht : 0 < t) (x y : ℝ) : 0 ≤ heatKernel t x y := by
  rw [heatKernel]
  exact mul_nonneg (heatCoefficient_pos ht).le (Real.exp_pos _).le

lemma abs_le_one_add_sq (x : ℝ) : |x| ≤ 1 + x ^ 2 := by
  have hsq : |x| ^ 2 = x ^ 2 := sq_abs x
  nlinarith [sq_nonneg (|x| - (1 / 2 : ℝ))]

lemma abs_le_of_mem_ball (x z : ℝ) (hz : z ∈ Metric.ball x 1) : |z| ≤ |x| + 1 := by
  rw [Metric.mem_ball, Real.dist_eq] at hz
  calc
    |z| = |(z - x) + x| := by
      congr 1
      ring
    _ ≤ |z - x| + |x| := by
      simpa only [Real.norm_eq_abs] using norm_add_le (z - x) x
    _ ≤ |x| + 1 := by linarith

lemma heatKernel_exp_le {t x z y : ℝ} (ht : 0 < t)
    (hz : z ∈ Metric.ball x 1) :
    Real.exp (-((z - y) ^ 2) / (4 * t)) ≤
      Real.exp ((|x| + 1) ^ 2 / (4 * t)) *
        Real.exp (-(1 / (8 * t)) * y ^ 2) := by
  let B : ℝ := |x| + 1
  have hB : 0 ≤ B := add_nonneg (abs_nonneg x) zero_le_one
  have hzabs : |z| ≤ B := by simpa [B] using abs_le_of_mem_ball x z hz
  have hzsq : z ^ 2 ≤ B ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hB] using hzabs
  have hd : y ^ 2 / 2 - B ^ 2 ≤ (z - y) ^ 2 := by
    nlinarith [sq_nonneg (y - 2 * z)]
  have ht8 : 0 < 8 * t := by positivity
  have harg : -((z - y) ^ 2) / (4 * t) ≤
      B ^ 2 / (4 * t) + -(1 / (8 * t)) * y ^ 2 := by
    calc
      -((z - y) ^ 2) / (4 * t) = (-2 * (z - y) ^ 2) / (8 * t) := by
        field_simp [ht.ne']
        ring
      _ ≤ (2 * B ^ 2 - y ^ 2) / (8 * t) := by
        exact (div_le_div_iff_of_pos_right ht8).2 (by nlinarith)
      _ = B ^ 2 / (4 * t) + -(1 / (8 * t)) * y ^ 2 := by
        field_simp [ht.ne']
        ring
  calc
    Real.exp (-((z - y) ^ 2) / (4 * t)) ≤
        Real.exp (B ^ 2 / (4 * t) + -(1 / (8 * t)) * y ^ 2) :=
      Real.exp_le_exp.mpr harg
    _ = Real.exp (B ^ 2 / (4 * t)) * Real.exp (-(1 / (8 * t)) * y ^ 2) := by
      rw [Real.exp_add]
    _ = _ := by rfl

lemma integrable_one_add_sq_mul_exp_neg (b : ℝ) (hb : 0 < b) :
    Integrable (fun y : ℝ ↦ (1 + y ^ 2) * Real.exp (-b * y ^ 2)) := by
  have h0 : Integrable (fun y : ℝ ↦ Real.exp (-b * y ^ 2)) :=
    integrable_exp_neg_mul_sq hb
  have h2 : Integrable (fun y : ℝ ↦ y ^ 2 * Real.exp (-b * y ^ 2)) := by
    simpa only [Real.rpow_two] using
      (integrable_rpow_mul_exp_neg_mul_sq hb (show (-1 : ℝ) < 2 by norm_num))
  rw [show (fun y : ℝ ↦ (1 + y ^ 2) * Real.exp (-b * y ^ 2)) =
      (fun y : ℝ ↦ Real.exp (-b * y ^ 2)) +
        (fun y : ℝ ↦ y ^ 2 * Real.exp (-b * y ^ 2)) by
    funext y
    simp only [Pi.add_apply]
    ring]
  exact h0.add h2

lemma integrable_gaussianQuadraticBound (b C : ℝ) (hb : 0 < b) :
    Integrable (fun y : ℝ ↦ C * (1 + y ^ 2) * Real.exp (-b * y ^ 2)) := by
  convert (integrable_one_add_sq_mul_exp_neg b hb).const_mul C using 1
  funext y
  ring

lemma bound_nonneg {f : ℝ → ℝ} {M : ℝ} (hM : ∀ y, |f y| ≤ M) : 0 ≤ M := by
  exact (abs_nonneg (f 0)).trans (hM 0)

lemma heatSolution_eq_integral_heatKernel (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ∫ y, heatKernel t x y * f y := by
  rw [heatSolution, if_pos ht, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  simp only [heatKernel, heatCoefficient]
  ring

lemma integrable_heatKernel_mul (f : ℝ → ℝ) (hf_cont : Continuous f)
    {M t x : ℝ} (hM : ∀ y, |f y| ≤ M) (ht : 0 < t) :
    Integrable (fun y ↦ heatKernel t x y * f y) := by
  have hM0 : 0 ≤ M := bound_nonneg hM
  refine Integrable.mono'
    ((integrable_gaussianPDFReal x (heatVariance t)).const_mul M) ?_ ?_
  · apply Continuous.aestronglyMeasurable
    simp only [heatKernel, heatCoefficient]
    fun_prop
  filter_upwards with y
  rw [heatKernel_eq_gaussianPDFReal ht]
  simp only [Real.norm_eq_abs, abs_mul,
    abs_of_nonneg (gaussianPDFReal_nonneg x (heatVariance t) y)]
  simpa [mul_comm] using
    mul_le_mul_of_nonneg_left (hM y) (gaussianPDFReal_nonneg x (heatVariance t) y)

lemma exists_heatKernelX_bound (f : ℝ → ℝ) {M t x : ℝ}
    (hM : ∀ y, |f y| ≤ M) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball x 1, ∀ y : ℝ,
      ‖heatKernelX t z y * f y‖ ≤
        C * (1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2) := by
  let B : ℝ := |x| + 1
  let C : ℝ := M * ((B + 1) / (2 * t)) * heatCoefficient t *
    Real.exp (B ^ 2 / (4 * t))
  have hM0 : 0 ≤ M := bound_nonneg hM
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    have hfrac : 0 ≤ (B + 1) / (2 * t) := by positivity
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hM0 hfrac) (heatCoefficient_pos ht).le)
      (Real.exp_pos _).le
  refine ⟨C, hC, ?_⟩
  intro z hz y
  have hzabs : |z| ≤ B := by simpa [B] using abs_le_of_mem_ball x z hz
  have hdist : |z - y| ≤ B + |y| := by
    calc
      |z - y| ≤ |z| + |y| := abs_sub z y
      _ ≤ B + |y| := by gcongr
  have hpoly : |z - y| ≤ (B + 1) * (1 + y ^ 2) := by
    calc
      |z - y| ≤ B + |y| := hdist
      _ ≤ B + (1 + y ^ 2) := by
        gcongr
        exact abs_le_one_add_sq y
      _ ≤ (B + 1) * (1 + y ^ 2) := by
        nlinarith [sq_nonneg y]
  have hk0 : 0 ≤ heatKernel t z y := heatKernel_nonneg ht z y
  have hc0 : 0 ≤ heatCoefficient t := (heatCoefficient_pos ht).le
  have hexp := heatKernel_exp_le ht hz (y := y)
  calc
    ‖heatKernelX t z y * f y‖ =
        (|z - y| / (2 * t)) * heatKernel t z y * |f y| := by
      simp only [Real.norm_eq_abs, heatKernelX, abs_mul, abs_neg, abs_div,
        abs_of_nonneg (show 0 ≤ 2 * t by positivity), abs_of_nonneg hk0]
    _ ≤ (((B + 1) * (1 + y ^ 2)) / (2 * t)) *
        (heatCoefficient t *
          (Real.exp (B ^ 2 / (4 * t)) *
            Real.exp (-(1 / (8 * t)) * y ^ 2))) * M := by
      rw [heatKernel]
      gcongr
      exact hM y
    _ = C * (1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2) := by
      dsimp only [C]
      ring

lemma exists_heatKernelXX_bound (f : ℝ → ℝ) {M t x : ℝ}
    (hM : ∀ y, |f y| ≤ M) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z ∈ Metric.ball x 1, ∀ y : ℝ,
      ‖heatKernelXX t z y * f y‖ ≤
        C * (1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2) := by
  let B : ℝ := |x| + 1
  let A : ℝ := 2 * (B ^ 2 + 1) / (4 * t ^ 2) + 1 / (2 * t)
  let C : ℝ := M * A * heatCoefficient t * Real.exp (B ^ 2 / (4 * t))
  have hM0 : 0 ≤ M := bound_nonneg hM
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hM0 hA) (heatCoefficient_pos ht).le)
      (Real.exp_pos _).le
  refine ⟨C, hC, ?_⟩
  intro z hz y
  have hzabs : |z| ≤ B := by simpa [B] using abs_le_of_mem_ball x z hz
  have hzsq : z ^ 2 ≤ B ^ 2 := by
    rw [sq_le_sq]
    simpa [abs_of_nonneg hB] using hzabs
  have hdsq : (z - y) ^ 2 ≤ 2 * (B ^ 2 + 1) * (1 + y ^ 2) := by
    have hfirst : (z - y) ^ 2 ≤ 2 * (z ^ 2 + y ^ 2) := by
      nlinarith [sq_nonneg (z + y)]
    calc
      (z - y) ^ 2 ≤ 2 * (z ^ 2 + y ^ 2) := hfirst
      _ ≤ 2 * (B ^ 2 + y ^ 2) := by nlinarith
      _ ≤ 2 * (B ^ 2 + 1) * (1 + y ^ 2) := by
        nlinarith [sq_nonneg B, sq_nonneg y, mul_nonneg (sq_nonneg B) (sq_nonneg y)]
  have hterm0 : 0 ≤ (z - y) ^ 2 / (4 * t ^ 2) := by positivity
  have hconst0 : 0 ≤ 1 / (2 * t) := by positivity
  have hdiv : (z - y) ^ 2 / (4 * t ^ 2) ≤
      (2 * (B ^ 2 + 1) / (4 * t ^ 2)) * (1 + y ^ 2) := by
    calc
      (z - y) ^ 2 / (4 * t ^ 2) ≤
          (2 * (B ^ 2 + 1) * (1 + y ^ 2)) / (4 * t ^ 2) := by
        exact (div_le_div_iff_of_pos_right (by positivity)).2 hdsq
      _ = (2 * (B ^ 2 + 1) / (4 * t ^ 2)) * (1 + y ^ 2) := by ring
  have hfac : |(z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
      A * (1 + y ^ 2) := by
    calc
      |(z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| ≤
          |(z - y) ^ 2 / (4 * t ^ 2)| + |1 / (2 * t)| := abs_sub _ _
      _ = (z - y) ^ 2 / (4 * t ^ 2) + 1 / (2 * t) := by
        rw [abs_of_nonneg hterm0, abs_of_nonneg hconst0]
      _ ≤ (2 * (B ^ 2 + 1) / (4 * t ^ 2)) * (1 + y ^ 2) +
          (1 / (2 * t)) * (1 + y ^ 2) := by
        exact add_le_add hdiv (by
          nlinarith [sq_nonneg y, hconst0])
      _ = A * (1 + y ^ 2) := by
        dsimp only [A]
        ring
  have hk0 : 0 ≤ heatKernel t z y := heatKernel_nonneg ht z y
  have hP : 0 ≤ A * (1 + y ^ 2) := mul_nonneg hA (by positivity)
  have hQ : 0 ≤ heatCoefficient t *
      (Real.exp (B ^ 2 / (4 * t)) * Real.exp (-(1 / (8 * t)) * y ^ 2)) := by
    exact mul_nonneg (heatCoefficient_pos ht).le
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hexp := heatKernel_exp_le ht hz (y := y)
  have hk_le : heatKernel t z y ≤ heatCoefficient t *
      (Real.exp (B ^ 2 / (4 * t)) * Real.exp (-(1 / (8 * t)) * y ^ 2)) := by
    rw [heatKernel]
    exact mul_le_mul_of_nonneg_left hexp (heatCoefficient_pos ht).le
  have hmul :
      |(z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| * heatKernel t z y ≤
        (A * (1 + y ^ 2)) *
          (heatCoefficient t *
            (Real.exp (B ^ 2 / (4 * t)) *
              Real.exp (-(1 / (8 * t)) * y ^ 2))) :=
    mul_le_mul hfac hk_le hk0 hP
  calc
    ‖heatKernelXX t z y * f y‖ =
        |(z - y) ^ 2 / (4 * t ^ 2) - 1 / (2 * t)| *
          heatKernel t z y * |f y| := by
      simp only [Real.norm_eq_abs, heatKernelXX, abs_mul, abs_of_nonneg hk0]
    _ ≤ (A * (1 + y ^ 2)) *
        (heatCoefficient t *
          (Real.exp (B ^ 2 / (4 * t)) *
            Real.exp (-(1 / (8 * t)) * y ^ 2))) * M := by
      exact mul_le_mul hmul (hM y) (abs_nonneg _) (mul_nonneg hP hQ)
    _ = C * (1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2) := by
      dsimp only [C]
      ring

lemma integral_heatKernel_space_deriv (f : ℝ → ℝ) (hf_cont : Continuous f)
    {M t x : ℝ} (hM : ∀ y, |f y| ≤ M) (ht : 0 < t) :
    Integrable (fun y ↦ heatKernelX t x y * f y) ∧
      HasDerivAt (fun z ↦ ∫ y, heatKernel t z y * f y)
        (∫ y, heatKernelX t x y * f y) x := by
  obtain ⟨C, _, hbound⟩ := exists_heatKernelX_bound f hM ht (x := x)
  have hb : 0 < 1 / (8 * t) := by positivity
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y ↦ heatKernel t z y * f y)
    (F' := fun z y ↦ heatKernelX t z y * f y)
    (bound := fun y ↦ C * (1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2))
    (s := Metric.ball x 1) (Metric.ball_mem_nhds x zero_lt_one)
    (Eventually.of_forall fun _ ↦ by
      apply Continuous.aestronglyMeasurable
      simp only [heatKernel, heatCoefficient]
      fun_prop)
    (integrable_heatKernel_mul f hf_cont hM ht)
    (by
      apply Continuous.aestronglyMeasurable
      simp only [heatKernelX, heatKernel, heatCoefficient]
      fun_prop)
    (ae_of_all _ fun y z hz ↦ hbound z hz y)
    (integrable_gaussianQuadraticBound (1 / (8 * t)) C hb)
    (ae_of_all _ fun y z _ ↦ (hasDerivAt_heatKernel_space ht z y).mul_const (f y))

lemma hasDerivAt_heatSolution_space (f : ℝ → ℝ) (hf_cont : Continuous f)
    {M t x : ℝ} (hM : ∀ y, |f y| ≤ M) (ht : 0 < t) :
    HasDerivAt (fun z ↦ heatSolution f t z)
      (∫ y, heatKernelX t x y * f y) x := by
  rw [show (fun z ↦ heatSolution f t z) =
      (fun z ↦ ∫ y, heatKernel t z y * f y) by
    funext z
    exact heatSolution_eq_integral_heatKernel f ht z]
  exact (integral_heatKernel_space_deriv f hf_cont hM ht).2

lemma integral_heatKernelX_space_deriv (f : ℝ → ℝ) (hf_cont : Continuous f)
    {M t x : ℝ} (hM : ∀ y, |f y| ≤ M) (ht : 0 < t) :
    Integrable (fun y ↦ heatKernelXX t x y * f y) ∧
      HasDerivAt (fun z ↦ ∫ y, heatKernelX t z y * f y)
        (∫ y, heatKernelXX t x y * f y) x := by
  obtain ⟨C, _, hbound⟩ := exists_heatKernelXX_bound f hM ht (x := x)
  have hb : 0 < 1 / (8 * t) := by positivity
  exact hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z y ↦ heatKernelX t z y * f y)
    (F' := fun z y ↦ heatKernelXX t z y * f y)
    (bound := fun y ↦ C * (1 + y ^ 2) * Real.exp (-(1 / (8 * t)) * y ^ 2))
    (s := Metric.ball x 1) (Metric.ball_mem_nhds x zero_lt_one)
    (Eventually.of_forall fun _ ↦ by
      apply Continuous.aestronglyMeasurable
      simp only [heatKernelX, heatKernel, heatCoefficient]
      fun_prop)
    (integral_heatKernel_space_deriv f hf_cont hM ht).1
    (by
      apply Continuous.aestronglyMeasurable
      simp only [heatKernelXX, heatKernel, heatCoefficient]
      fun_prop)
    (ae_of_all _ fun y z hz ↦ hbound z hz y)
    (integrable_gaussianQuadraticBound (1 / (8 * t)) C hb)
    (ae_of_all _ fun y z _ ↦ (hasDerivAt_heatKernelX_space ht z y).mul_const (f y))

lemma exists_heatKernelXX_time_bound (f : ℝ → ℝ) {M t x : ℝ}
    (hM : ∀ y, |f y| ≤ M) (ht : 0 < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s ∈ Metric.ball t (t / 2), ∀ y : ℝ,
      ‖heatKernelXX s x y * f y‖ ≤
        C * (1 + y ^ 2) * Real.exp (-(1 / (12 * t)) * y ^ 2) := by
  let B : ℝ := |x| + 1
  let A : ℝ := 2 * (x ^ 2 + 1) / t ^ 2 + 1 / t
  let C : ℝ := M * A * heatCoefficient (t / 2) * Real.exp (B ^ 2 / (2 * t))
  have hM0 : 0 ≤ M := bound_nonneg hM
  have hA : 0 ≤ A := by
    dsimp only [A]
    positivity
  have hC : 0 ≤ C := by
    dsimp only [C]
    exact mul_nonneg
      (mul_nonneg (mul_nonneg hM0 hA) (heatCoefficient_pos (half_pos ht)).le)
      (Real.exp_pos _).le
  refine ⟨C, hC, ?_⟩
  intro s hs y
  rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
  have hlow : t / 2 ≤ s := by linarith
  have hupp : s ≤ 3 * t / 2 := by linarith
  have hspos : 0 < s := (half_pos ht).trans_le hlow
  have hcoef : heatCoefficient s ≤ heatCoefficient (t / 2) := by
    rw [heatCoefficient_eq_rpow_neg s, heatCoefficient_eq_rpow_neg (t / 2)]
    apply Real.rpow_le_rpow_of_nonpos (by positivity) (by gcongr) (by norm_num)
  have harg1 : B ^ 2 / (4 * s) ≤ B ^ 2 / (2 * t) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left (by linarith) (sq_nonneg B)
  have hinv : 1 / (12 * t) ≤ 1 / (8 * s) := by
    simpa only [one_div] using
      (inv_le_inv₀ (show 0 < 12 * t by positivity) (show 0 < 8 * s by positivity)).2
        (by linarith)
  have harg2 : -(1 / (8 * s)) * y ^ 2 ≤ -(1 / (12 * t)) * y ^ 2 := by
    simpa only [neg_mul] using
      neg_le_neg (mul_le_mul_of_nonneg_right hinv (sq_nonneg y))
  have hexp : Real.exp (-((x - y) ^ 2) / (4 * s)) ≤
      Real.exp (B ^ 2 / (2 * t)) * Real.exp (-(1 / (12 * t)) * y ^ 2) := by
    calc
      Real.exp (-((x - y) ^ 2) / (4 * s)) ≤
          Real.exp (B ^ 2 / (4 * s)) * Real.exp (-(1 / (8 * s)) * y ^ 2) := by
        simpa only [B] using
          (heatKernel_exp_le hspos (Metric.mem_ball_self zero_lt_one) (x := x)
            (z := x) (y := y))
      _ ≤ Real.exp (B ^ 2 / (2 * t)) * Real.exp (-(1 / (12 * t)) * y ^ 2) :=
        mul_le_mul (Real.exp_le_exp.mpr harg1) (Real.exp_le_exp.mpr harg2)
          (Real.exp_pos _).le (Real.exp_pos _).le
  have hk0 : 0 ≤ heatKernel s x y := heatKernel_nonneg hspos x y
  have hk_le : heatKernel s x y ≤ heatCoefficient (t / 2) *
      (Real.exp (B ^ 2 / (2 * t)) * Real.exp (-(1 / (12 * t)) * y ^ 2)) := by
    rw [heatKernel]
    exact mul_le_mul hcoef hexp (Real.exp_pos _).le
      (heatCoefficient_pos (half_pos ht)).le
  have hdsq : (x - y) ^ 2 ≤ 2 * (x ^ 2 + 1) * (1 + y ^ 2) := by
    have hfirst : (x - y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := by
      nlinarith [sq_nonneg (x + y)]
    calc
      (x - y) ^ 2 ≤ 2 * (x ^ 2 + y ^ 2) := hfirst
      _ ≤ 2 * (x ^ 2 + 1) * (1 + y ^ 2) := by
        nlinarith [sq_nonneg x, sq_nonneg y, mul_nonneg (sq_nonneg x) (sq_nonneg y)]
  have hsquare : t ^ 2 ≤ 4 * s ^ 2 := by
    have hminus : 0 ≤ 2 * s - t := by linarith
    have hplus : 0 ≤ 2 * s + t := by positivity
    nlinarith [mul_nonneg hminus hplus]
  have hden : (x - y) ^ 2 / (4 * s ^ 2) ≤ (x - y) ^ 2 / t ^ 2 := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    exact mul_le_mul_of_nonneg_left hsquare (sq_nonneg (x - y))
  have hdiv : (x - y) ^ 2 / (4 * s ^ 2) ≤
      (2 * (x ^ 2 + 1) / t ^ 2) * (1 + y ^ 2) := by
    calc
      (x - y) ^ 2 / (4 * s ^ 2) ≤ (x - y) ^ 2 / t ^ 2 := hden
      _ ≤ (2 * (x ^ 2 + 1) * (1 + y ^ 2)) / t ^ 2 := by
        exact (div_le_div_iff_of_pos_right (by positivity)).2 hdsq
      _ = (2 * (x ^ 2 + 1) / t ^ 2) * (1 + y ^ 2) := by ring
  have hconst : 1 / (2 * s) ≤ 1 / t := by
    rw [div_le_div_iff₀ (by positivity) ht]
    linarith
  have hterm0 : 0 ≤ (x - y) ^ 2 / (4 * s ^ 2) := by positivity
  have hconst0 : 0 ≤ 1 / (2 * s) := by positivity
  have hfac : |(x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| ≤
      A * (1 + y ^ 2) := by
    calc
      |(x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| ≤
          |(x - y) ^ 2 / (4 * s ^ 2)| + |1 / (2 * s)| := abs_sub _ _
      _ = (x - y) ^ 2 / (4 * s ^ 2) + 1 / (2 * s) := by
        rw [abs_of_nonneg hterm0, abs_of_nonneg hconst0]
      _ ≤ (2 * (x ^ 2 + 1) / t ^ 2) * (1 + y ^ 2) +
          (1 / t) * (1 + y ^ 2) := by
        exact add_le_add hdiv (hconst.trans (by
          nlinarith [sq_nonneg y, (show 0 ≤ 1 / t by positivity)]))
      _ = A * (1 + y ^ 2) := by
        dsimp only [A]
        ring
  have hP : 0 ≤ A * (1 + y ^ 2) := mul_nonneg hA (by positivity)
  have hQ : 0 ≤ heatCoefficient (t / 2) *
      (Real.exp (B ^ 2 / (2 * t)) * Real.exp (-(1 / (12 * t)) * y ^ 2)) :=
    mul_nonneg (heatCoefficient_pos (half_pos ht)).le
      (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)
  have hmul :
      |(x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| * heatKernel s x y ≤
        (A * (1 + y ^ 2)) *
          (heatCoefficient (t / 2) *
            (Real.exp (B ^ 2 / (2 * t)) *
              Real.exp (-(1 / (12 * t)) * y ^ 2))) :=
    mul_le_mul hfac hk_le hk0 hP
  calc
    ‖heatKernelXX s x y * f y‖ =
        |(x - y) ^ 2 / (4 * s ^ 2) - 1 / (2 * s)| *
          heatKernel s x y * |f y| := by
      simp only [Real.norm_eq_abs, heatKernelXX, abs_mul, abs_of_nonneg hk0]
    _ ≤ (A * (1 + y ^ 2)) *
        (heatCoefficient (t / 2) *
          (Real.exp (B ^ 2 / (2 * t)) *
            Real.exp (-(1 / (12 * t)) * y ^ 2))) * M := by
      exact mul_le_mul hmul (hM y) (abs_nonneg _) (mul_nonneg hP hQ)
    _ = C * (1 + y ^ 2) * Real.exp (-(1 / (12 * t)) * y ^ 2) := by
      dsimp only [C]
      ring

lemma hasDerivAt_heatSolution_time (f : ℝ → ℝ) (hf_cont : Continuous f)
    {M t x : ℝ} (hM : ∀ y, |f y| ≤ M) (ht : 0 < t) :
    HasDerivAt (fun s ↦ heatSolution f s x)
      (∫ y, heatKernelXX t x y * f y) t := by
  obtain ⟨C, _, hbound⟩ := exists_heatKernelXX_time_bound f hM ht (x := x)
  have hb : 0 < 1 / (12 * t) := by positivity
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun s y ↦ heatKernel s x y * f y)
    (F' := fun s y ↦ heatKernelXX s x y * f y)
    (bound := fun y ↦ C * (1 + y ^ 2) * Real.exp (-(1 / (12 * t)) * y ^ 2))
    (s := Metric.ball t (t / 2)) (Metric.ball_mem_nhds t (half_pos ht))
    (Eventually.of_forall fun _ ↦ by
      apply Continuous.aestronglyMeasurable
      simp only [heatKernel, heatCoefficient]
      fun_prop)
    (integrable_heatKernel_mul f hf_cont hM ht)
    (by
      apply Continuous.aestronglyMeasurable
      simp only [heatKernelXX, heatKernel, heatCoefficient]
      fun_prop)
    (ae_of_all _ fun y s hs ↦ hbound s hs y)
    (integrable_gaussianQuadraticBound (1 / (12 * t)) C hb)
    (ae_of_all _ fun y s hs ↦ by
      rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
      have hspos : 0 < s := by linarith
      exact (hasDerivAt_heatKernel_time hspos x y).mul_const (f y))
  apply hmain.2.congr_of_eventuallyEq
  filter_upwards [isOpen_Ioi.mem_nhds ht] with s hs
  exact heatSolution_eq_integral_heatKernel f hs x

lemma heatSolution_eq_gaussianIntegral (f : ℝ → ℝ) {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x = ∫ y, f y ∂gaussianReal x (heatVariance t) := by
  rw [heatSolution, if_pos ht,
    integral_gaussianReal_eq_integral_smul (heatVariance_ne_zero ht)]
  rw [← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with y
  rw [← heatKernel_eq_gaussianPDFReal ht]
  simp only [heatKernel, heatCoefficient, smul_eq_mul]
  ring

lemma gaussianReal_map_heat (t x : ℝ) (ht : 0 < t) :
    (gaussianReal 0 1).map (fun z ↦ x + Real.sqrt (2 * t) * z) =
      gaussianReal x (heatVariance t) := by
  calc
    (gaussianReal 0 1).map (fun z ↦ x + Real.sqrt (2 * t) * z) =
        ((gaussianReal 0 1).map (fun z ↦ Real.sqrt (2 * t) * z)).map (fun z ↦ x + z) := by
          rw [Measure.map_map (by fun_prop) (by fun_prop)]
          congr 1
    _ = (gaussianReal 0
          (.mk ((Real.sqrt (2 * t)) ^ 2) (sq_nonneg _) * 1)).map (fun z ↦ x + z) := by
          rw [gaussianReal_map_const_mul]
          simp only [mul_zero]
    _ = gaussianReal (0 + x)
          (.mk ((Real.sqrt (2 * t)) ^ 2) (sq_nonneg _) * 1) := by
          rw [gaussianReal_map_const_add]
    _ = gaussianReal x (heatVariance t) := by
          rw [zero_add]
          congr 1
          apply Subtype.ext
          change (Real.sqrt (2 * t)) ^ 2 * 1 = (heatVariance t : ℝ)
          rw [mul_one, heatVariance_coe ht, Real.sq_sqrt (by positivity)]

lemma heatSolution_eq_standardGaussianIntegral (f : ℝ → ℝ) (hf : Continuous f)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    heatSolution f t x =
      ∫ z, f (x + Real.sqrt (2 * t) * z) ∂gaussianReal 0 1 := by
  rw [heatSolution_eq_gaussianIntegral f ht x, ← gaussianReal_map_heat t x ht]
  exact integral_map_of_stronglyMeasurable (by fun_prop) hf.stronglyMeasurable

lemma tendsto_heatSolution_zero (f : ℝ → ℝ) (hf_cont : Continuous f)
    (hf_bdd : ∃ M : ℝ, ∀ x, |f x| ≤ M) (x : ℝ) :
    Tendsto (fun t : ℝ ↦ heatSolution f t x)
      (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (f x)) := by
  obtain ⟨M, hM⟩ := hf_bdd
  let μ : Measure ℝ := gaussianReal 0 1
  have h_integral :
      Tendsto (fun t : ℝ ↦ ∫ z, f (x + Real.sqrt (2 * t) * z) ∂μ)
        (nhdsWithin (0 : ℝ) (Ioi 0)) (nhds (f x)) := by
    have h := tendsto_integral_filter_of_dominated_convergence
      (l := nhdsWithin (0 : ℝ) (Ioi 0)) (μ := μ)
      (F := fun t z ↦ f (x + Real.sqrt (2 * t) * z))
      (f := fun _ ↦ f x) (fun _ ↦ M)
      (Eventually.of_forall fun _ ↦ by fun_prop)
      (Eventually.of_forall fun t ↦ ae_of_all _ fun z ↦ by
        simpa [Real.norm_eq_abs] using hM (x + Real.sqrt (2 * t) * z))
      (integrable_const M)
      (ae_of_all _ fun z ↦ by
        have hc : ContinuousAt (fun t : ℝ ↦ f (x + Real.sqrt (2 * t) * z)) 0 := by
          fun_prop
        have hz := hc.tendsto.mono_left
          (show nhdsWithin (0 : ℝ) (Ioi 0) ≤ nhds 0 from inf_le_left)
        simpa using hz)
    simpa [μ] using h
  apply h_integral.congr'
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact (heatSolution_eq_standardGaussianIntegral f hf_cont ht x).symm

end Submission.Helpers
