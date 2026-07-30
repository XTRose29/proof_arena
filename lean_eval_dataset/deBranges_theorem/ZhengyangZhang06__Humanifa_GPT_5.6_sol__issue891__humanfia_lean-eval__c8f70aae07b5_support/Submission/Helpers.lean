import Mathlib

open Metric
open Filter

namespace Submission

noncomputable def taylorCoeff (f : ℂ → ℂ) (n : ℕ) : ℂ :=
  iteratedDeriv n f 0 / n.factorial

lemma hasSum_taylorCoeff_mul_pow {f : ℂ → ℂ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    HasSum (fun n : ℕ ↦ taylorCoeff f n * z ^ n) (f z) := by
  simpa only [taylorCoeff, smul_eq_mul, sub_zero, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using Complex.hasSum_taylorSeries_on_ball diff hz

lemma tsum_taylorCoeff_mul_pow {f : ℂ → ℂ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) {z : ℂ} (hz : z ∈ ball 0 1) :
    ∑' n : ℕ, taylorCoeff f n * z ^ n = f z :=
  (hasSum_taylorCoeff_mul_pow diff hz).tsum_eq

@[simp]
lemma taylorCoeff_zero {f : ℂ → ℂ} (h0 : f 0 = 0) : taylorCoeff f 0 = 0 := by
  simp [taylorCoeff, h0]

@[simp]
lemma taylorCoeff_one {f : ℂ → ℂ} (h1 : deriv f 0 = 1) : taylorCoeff f 1 = 1 := by
  simp [taylorCoeff, h1]

lemma deBranges_iff_taylorCoeff_norm_le (f : ℂ → ℂ) (n : ℕ) :
    ‖iteratedDeriv n f 0 / n.factorial‖ ≤ n ↔ ‖taylorCoeff f n‖ ≤ n := by
  rfl

noncomputable def dilate (f : ℂ → ℂ) (c z : ℂ) : ℂ :=
  f (c * z) / c

lemma mapsTo_mul_unitBall {c : ℂ} (hc : ‖c‖ ≤ 1) :
    Set.MapsTo (fun z : ℂ => c * z) (ball 0 1) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_mul]
  calc
    ‖c‖ * ‖z‖ ≤ 1 * ‖z‖ := mul_le_mul_of_nonneg_right hc (norm_nonneg z)
    _ < 1 := by simpa using hz

lemma iteratedDeriv_comp_mul_zero {f : ℂ → ℂ} {c : ℂ} {n : ℕ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) (hc : ‖c‖ ≤ 1) :
    iteratedDeriv n (fun z : ℂ => f (c * z)) 0 =
      c ^ n * iteratedDeriv n f 0 := by
  have hzero : (0 : ℂ) ∈ ball 0 1 := by simp
  have hu : UniqueDiffOn ℂ (ball (0 : ℂ) 1) := isOpen_ball.uniqueDiffOn
  have hmap := mapsTo_mul_unitBall hc
  have hfOn : ContDiffOn ℂ n f (ball 0 1) := diff.contDiffOn isOpen_ball
  have hlin : ContDiffOn ℂ n (fun z : ℂ => c * z) (ball 0 1) := by
    fun_prop
  have hcompOn : ContDiffOn ℂ n (fun z : ℂ => f (c * z)) (ball 0 1) := by
    simpa only [Function.comp_def] using hfOn.comp hlin hmap
  have hfAt : ContDiffAt ℂ n f 0 :=
    hfOn.contDiffAt (isOpen_ball.mem_nhds hzero)
  have hcompAt : ContDiffAt ℂ n (fun z : ℂ => f (c * z)) 0 :=
    hcompOn.contDiffAt (isOpen_ball.mem_nhds hzero)
  have hw := iteratedDerivWithin_comp_const_smul
    (x := (0 : ℂ)) hzero hu hfOn c hmap
  rw [iteratedDerivWithin_eq_iteratedDeriv hu hcompAt hzero] at hw
  simp only [mul_zero] at hw
  rw [iteratedDerivWithin_eq_iteratedDeriv hu hfAt hzero] at hw
  simpa only [smul_eq_mul] using hw

lemma differentiableOn_dilate {f : ℂ → ℂ} {c : ℂ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) (hc : ‖c‖ ≤ 1) :
    DifferentiableOn ℂ (dilate f c) (ball 0 1) := by
  intro z hz
  have hcz : c * z ∈ ball (0 : ℂ) 1 := mapsTo_mul_unitBall hc hz
  change DifferentiableWithinAt ℂ (fun z : ℂ => f (c * z) / c) (ball 0 1) z
  exact (((diff.differentiableAt (isOpen_ball.mem_nhds hcz)).comp z (by fun_prop)).div_const c).differentiableWithinAt

lemma injOn_dilate {f : ℂ → ℂ} {c : ℂ}
    (inj : (ball (0 : ℂ) 1).InjOn f) (hc : ‖c‖ ≤ 1) (hc0 : c ≠ 0) :
    (ball (0 : ℂ) 1).InjOn (dilate f c) := by
  intro x hx y hy hxy
  apply mul_left_cancel₀ hc0
  apply inj (mapsTo_mul_unitBall hc hx) (mapsTo_mul_unitBall hc hy)
  exact (div_left_inj' hc0).mp hxy

lemma taylorCoeff_dilate {f : ℂ → ℂ} {c : ℂ} {n : ℕ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) (hc : ‖c‖ ≤ 1) (hc0 : c ≠ 0) :
    taylorCoeff (dilate f c) n = (c ^ n / c) * taylorCoeff f n := by
  rw [taylorCoeff, taylorCoeff]
  change iteratedDeriv n (fun z : ℂ => f (c * z) / c) 0 / n.factorial = _
  rw [iteratedDeriv_div_const, iteratedDeriv_comp_mul_zero diff hc]
  field_simp [hc0]

lemma taylorCoeff_norm_le_of_dilate {f : ℂ → ℂ} {n : ℕ}
    (diff : DifferentiableOn ℂ f (ball 0 1))
    (bound : ∀ r : ℝ, 0 < r → r < 1 → ‖taylorCoeff (dilate f (r : ℂ)) n‖ ≤ n) :
    ‖taylorCoeff f n‖ ≤ n := by
  let r : ℕ → ℝ := fun k => 1 - 1 / (((k + 1 : ℕ) : ℝ) + 1)
  have hr_pos (k : ℕ) : 0 < r k := by
    have hd : (1 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by
      norm_num
      positivity
    have hd0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by linarith
    have hfrac : 1 / (((k + 1 : ℕ) : ℝ) + 1) < 1 :=
      (div_lt_one hd0).2 hd
    dsimp [r]
    linarith
  have hr_lt (k : ℕ) : r k < 1 := by
    have hd0 : (0 : ℝ) < ((k + 1 : ℕ) : ℝ) + 1 := by positivity
    have hfrac : 0 < 1 / (((k + 1 : ℕ) : ℝ) + 1) := one_div_pos.mpr hd0
    dsimp [r]
    linarith
  have hrecip :
      Tendsto (fun k : ℕ => 1 / (((k + 1 : ℕ) : ℝ) + 1)) atTop (nhds 0) :=
    (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp
      (Filter.tendsto_add_atTop_nat 1)
  have hr_tendsto : Tendsto r atTop (nhds 1) := by
    simpa [r] using tendsto_const_nhds.sub hrecip
  have hrc_tendsto :
      Tendsto (fun k => ((r k : ℝ) : ℂ)) atTop (nhds (1 : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 1).comp hr_tendsto
  have hcoef_tendsto :
      Tendsto (fun k => ((((r k : ℝ) : ℂ) ^ n / (r k : ℝ)) * taylorCoeff f n))
        atTop (nhds (taylorCoeff f n)) := by
    simpa using
      ((hrc_tendsto.pow n).div hrc_tendsto (by norm_num : (1 : ℂ) ≠ 0)).mul
        tendsto_const_nhds
  apply le_of_tendsto hcoef_tendsto.norm
  apply Filter.Eventually.of_forall
  intro k
  have hc : ‖((r k : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt (hr_pos k))]
    exact le_of_lt (hr_lt k)
  have hc0 : ((r k : ℝ) : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (hr_pos k))
  calc
    ‖((((r k : ℝ) : ℂ) ^ n / (r k : ℝ)) * taylorCoeff f n)‖ =
        ‖taylorCoeff (dilate f (r k : ℂ)) n‖ := by
      rw [taylorCoeff_dilate diff hc hc0]
    _ ≤ n := bound (r k) (hr_pos k) (hr_lt k)

lemma mapsTo_real_mul_largeBall {r : ℝ} (hr : 0 < r) :
    Set.MapsTo (fun z : ℂ => (r : ℂ) * z) (ball 0 (1 / r)) (ball 0 1) := by
  intro z hz
  rw [mem_ball_zero_iff] at hz ⊢
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
  calc
    r * ‖z‖ < r * (1 / r) := mul_lt_mul_of_pos_left hz hr
    _ = 1 := by field_simp [ne_of_gt hr]

lemma differentiableOn_dilate_largeBall {f : ℂ → ℂ} {r : ℝ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) (hr : 0 < r) :
    DifferentiableOn ℂ (dilate f (r : ℂ)) (ball 0 (1 / r)) := by
  intro z hz
  have hrz : (r : ℂ) * z ∈ ball (0 : ℂ) 1 := mapsTo_real_mul_largeBall hr hz
  change DifferentiableWithinAt ℂ (fun z : ℂ => f ((r : ℂ) * z) / r)
    (ball 0 (1 / r)) z
  exact (((diff.differentiableAt (isOpen_ball.mem_nhds hrz)).comp z (by fun_prop)).div_const
    (r : ℂ)).differentiableWithinAt

lemma injOn_dilate_largeBall {f : ℂ → ℂ} {r : ℝ}
    (inj : (ball (0 : ℂ) 1).InjOn f) (hr : 0 < r) :
    (ball (0 : ℂ) (1 / r)).InjOn (dilate f (r : ℂ)) := by
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  intro x hx y hy hxy
  apply mul_left_cancel₀ hr0
  apply inj (mapsTo_real_mul_largeBall hr hx) (mapsTo_real_mul_largeBall hr hy)
  exact (div_left_inj' hr0).mp hxy

lemma hasSum_taylorCoeff_dilate_largeBall {f : ℂ → ℂ} {r : ℝ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) (hr : 0 < r)
    {z : ℂ} (hz : z ∈ ball 0 (1 / r)) :
    HasSum (fun n : ℕ => taylorCoeff (dilate f (r : ℂ)) n * z ^ n)
      (dilate f (r : ℂ) z) := by
  simpa only [taylorCoeff, smul_eq_mul, sub_zero, div_eq_mul_inv, mul_comm, mul_left_comm,
    mul_assoc] using
    Complex.hasSum_taylorSeries_on_ball (differentiableOn_dilate_largeBall diff hr) hz

@[simp]
lemma dilate_zero {f : ℂ → ℂ} {c : ℂ} (h0 : f 0 = 0) : dilate f c 0 = 0 := by
  simp [dilate, h0]

@[simp]
lemma deriv_dilate_zero {f : ℂ → ℂ} {c : ℂ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) (hc : ‖c‖ ≤ 1) (hc0 : c ≠ 0)
    (h1 : deriv f 0 = 1) : deriv (dilate f c) 0 = 1 := by
  have h := taylorCoeff_dilate (n := 1) diff hc hc0
  rw [taylorCoeff_one h1] at h
  simpa [taylorCoeff, hc0] using h

def NormalizedUnivalentOn (f : ℂ → ℂ) (R : ℝ) : Prop :=
  DifferentiableOn ℂ f (ball 0 R) ∧
    (ball (0 : ℂ) R).InjOn f ∧ f 0 = 0 ∧ deriv f 0 = 1

lemma normalizedUnivalentOn_dilate_largeBall {f : ℂ → ℂ} {r : ℝ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) (inj : (ball (0 : ℂ) 1).InjOn f)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (hr : 0 < r) (hr1 : r < 1) :
    NormalizedUnivalentOn (dilate f (r : ℂ)) (1 / r) := by
  have hc : ‖(r : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (le_of_lt hr)]
    exact le_of_lt hr1
  have hr0 : (r : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hr
  exact ⟨differentiableOn_dilate_largeBall diff hr, injOn_dilate_largeBall inj hr,
    dilate_zero h0, deriv_dilate_zero diff hc hr0 h1⟩

lemma taylorCoeff_norm_le_of_extendedDisk {f : ℂ → ℂ} {n : ℕ}
    (diff : DifferentiableOn ℂ f (ball 0 1)) (inj : (ball (0 : ℂ) 1).InjOn f)
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1)
    (bound : ∀ (g : ℂ → ℂ) (R : ℝ), 1 < R → NormalizedUnivalentOn g R →
      ‖taylorCoeff g n‖ ≤ n) :
    ‖taylorCoeff f n‖ ≤ n := by
  apply taylorCoeff_norm_le_of_dilate diff
  intro r hr hr1
  exact bound (dilate f (r : ℂ)) (1 / r) (one_lt_one_div hr hr1)
    (normalizedUnivalentOn_dilate_largeBall diff inj h0 h1 hr hr1)

end Submission
