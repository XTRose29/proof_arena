import Submission.SignChange
import Mathlib.Analysis.Fourier.RiemannLebesgueLemma

open Complex Filter MeasureTheory Real Set Topology

namespace Submission.FejerLaplace

attribute [local instance 2000] NormedAddCommGroup.toAddCommGroup NormedSpace.toModule

noncomputable def triangleWeight (H t : ℝ) : ℝ :=
  1 - |t| / H

lemma triangleWeight_nonneg {H t : ℝ} (hH : 0 < H) (ht : t ∈ Icc (-H) H) :
    0 ≤ triangleWeight H t := by
  unfold triangleWeight
  rw [sub_nonneg, div_le_one hH]
  exact abs_le.mpr ht

lemma triangleWeight_neg (H t : ℝ) :
    triangleWeight H (-t) = triangleWeight H t := by
  simp [triangleWeight]

lemma continuous_triangleWeight (H : ℝ) : Continuous (triangleWeight H) := by
  unfold triangleWeight
  fun_prop

private noncomputable def triangleCosPrimitive (H x t : ℝ) : ℝ :=
  (1 - t / H) * Real.sin (t * x) / x - Real.cos (t * x) / (H * x ^ 2)

private lemma hasDerivAt_triangleCosPrimitive {H x : ℝ}
    (hH : H ≠ 0) (hx : x ≠ 0) (t : ℝ) :
    HasDerivAt (triangleCosPrimitive H x)
      ((1 - t / H) * Real.cos (t * x)) t := by
  have hA : HasDerivAt (fun y : ℝ => 1 - y / H) (-1 / H) t := by
    simpa [div_eq_mul_inv] using
      ((hasDerivAt_id t).div_const H).const_sub 1
  have hsin : HasDerivAt (fun y : ℝ => Real.sin (y * x))
      (Real.cos (t * x) * x) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul x).sin
  have hcos : HasDerivAt (fun y : ℝ => Real.cos (y * x))
      (-Real.sin (t * x) * x) t := by
    simpa [mul_comm] using ((hasDerivAt_id t).const_mul x).cos
  have h : HasDerivAt
      (fun y : ℝ => (1 - y / H) * Real.sin (y * x) / x -
        Real.cos (y * x) / (H * x ^ 2))
      ((-1 / H * Real.sin (t * x) +
          (1 - t / H) * (Real.cos (t * x) * x)) / x -
        (-Real.sin (t * x) * x) / (H * x ^ 2)) t := by
    apply (((hA.mul hsin).div_const x).sub
      (hcos.div_const (H * x ^ 2))).congr_of_eventuallyEq
    exact Filter.Eventually.of_forall fun _ => rfl
  have heq :
      ((-1 / H * Real.sin (t * x) +
          (1 - t / H) * (Real.cos (t * x) * x)) / x -
        (-Real.sin (t * x) * x) / (H * x ^ 2)) =
        (1 - t / H) * Real.cos (t * x) := by
    field_simp [hH, hx]
    ring
  unfold triangleCosPrimitive
  exact h.congr_deriv heq

lemma integral_triangle_cos_Icc {H x : ℝ} (hH : 0 < H) (hx : x ≠ 0) :
    ∫ t in (0 : ℝ)..H, (1 - t / H) * Real.cos (t * x) =
      (1 - Real.cos (H * x)) / (H * x ^ 2) := by
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ht => hasDerivAt_triangleCosPrimitive hH.ne' hx t)
    ((by fun_prop : Continuous fun t : ℝ => (1 - t / H) * Real.cos (t * x))
      |>.intervalIntegrable 0 H)]
  unfold triangleCosPrimitive
  simp only [zero_div, sub_zero, zero_mul, Real.sin_zero, Real.cos_zero]
  field_simp [hH.ne', hx]
  ring

lemma integral_triangle_cos_nonneg {H x : ℝ} (hH : 0 < H) :
    0 ≤ ∫ t in (-H)..H, triangleWeight H t * Real.cos (t * x) := by
  let f : ℝ → ℝ := fun t => triangleWeight H t * Real.cos (t * x)
  have hfcont : Continuous f := (continuous_triangleWeight H).mul (by fun_prop)
  have hadd :
      (∫ t in (-H)..(0 : ℝ), f t) + ∫ t in (0 : ℝ)..H, f t =
        ∫ t in (-H)..H, f t :=
    intervalIntegral.integral_add_adjacent_intervals
      (hfcont.intervalIntegrable (-H) 0) (hfcont.intervalIntegrable 0 H)
  change 0 ≤ ∫ t in (-H)..H, f t
  rw [← hadd]
  have hneg :
      ∫ t in (-H)..(0 : ℝ), f t = ∫ t in (0 : ℝ)..H, f t := by
    calc
      ∫ t in (-H)..(0 : ℝ), triangleWeight H t * Real.cos (t * x) =
          ∫ t in (0 : ℝ)..H, triangleWeight H (-t) * Real.cos ((-t) * x) := by
        change (∫ t in (-H)..(0 : ℝ), f t) = ∫ t in (0 : ℝ)..H, f (-t)
        simpa only [neg_zero] using
          (intervalIntegral.integral_comp_neg (f := f) (a := 0) (b := H)).symm
      _ = ∫ t in (0 : ℝ)..H, triangleWeight H t * Real.cos (t * x) := by
        apply intervalIntegral.integral_congr
        intro t _ht
        change triangleWeight H (-t) * Real.cos ((-t) * x) =
          triangleWeight H t * Real.cos (t * x)
        rw [triangleWeight_neg]
        congr 1
        rw [show (-t) * x = -(t * x) by ring, Real.cos_neg]
  rw [hneg, ← two_mul]
  apply mul_nonneg (by norm_num)
  by_cases hx : x = 0
  · subst x
    have hnonneg : 0 ≤ ∫ t in (0 : ℝ)..H, triangleWeight H t :=
      intervalIntegral.integral_nonneg (by linarith) fun t ht =>
        triangleWeight_nonneg hH ⟨by linarith [ht.1], ht.2⟩
    simpa only [f, mul_zero, Real.cos_zero, mul_one] using hnonneg
  · rw [show (∫ t in (0 : ℝ)..H,
        triangleWeight H t * Real.cos (t * x)) =
        ∫ t in (0 : ℝ)..H, (1 - t / H) * Real.cos (t * x) by
        apply intervalIntegral.integral_congr
        intro t ht
        have ht' : t ∈ Icc (0 : ℝ) H := by
          simpa only [uIcc_of_le hH.le] using ht
        change (1 - |t| / H) * Real.cos (t * x) =
          (1 - t / H) * Real.cos (t * x)
        rw [abs_of_nonneg ht'.1]]
    rw [integral_triangle_cos_Icc hH hx]
    exact div_nonneg (sub_nonneg.mpr (Real.cos_le_one _)) (by positivity)

lemma integral_triangle_cexp_re_nonneg {H x : ℝ} (hH : 0 < H) :
    0 ≤ (∫ t in (-H)..H,
      (triangleWeight H t : ℂ) * Complex.exp ((t * x : ℝ) * Complex.I)).re := by
  have hint : IntervalIntegrable
      (fun t : ℝ => (triangleWeight H t : ℂ) *
        Complex.exp ((t * x : ℝ) * Complex.I)) volume (-H) H :=
    ((Complex.continuous_ofReal.comp (continuous_triangleWeight H)).mul (by fun_prop))
      |>.intervalIntegrable _ _
  change 0 ≤ RCLike.re (∫ t in (-H)..H,
    (triangleWeight H t : ℂ) * Complex.exp ((t * x : ℝ) * Complex.I))
  rw [← intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hint]
  convert integral_triangle_cos_nonneg (H := H) (x := x) hH using 1
  apply intervalIntegral.integral_congr
  intro t _ht
  change ((triangleWeight H t : ℂ) *
    Complex.exp ((t * x : ℝ) * Complex.I)).re =
      triangleWeight H t * Real.cos (t * x)
  calc
    _ = triangleWeight H t *
        (Complex.exp ((t * x : ℝ) * Complex.I)).re := by
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        zero_mul, sub_zero]
    _ = triangleWeight H t * Real.cos (t * x) := by
      rw [Complex.exp_ofReal_mul_I_re]

end Submission.FejerLaplace
