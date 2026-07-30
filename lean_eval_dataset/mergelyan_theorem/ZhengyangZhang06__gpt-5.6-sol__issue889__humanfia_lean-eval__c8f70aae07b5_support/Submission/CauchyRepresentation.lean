import Submission.CauchyFormula

open Function Set
open scoped ContDiff Interval Topology

noncomputable section

namespace Submission.Helpers

/-- Whole-plane Cauchy--Pompeiu representation for a smooth compactly supported function. -/
theorem cauchyPompeiu_compactSupport (g : ℂ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (z : ℂ) :
    (2 * Real.pi * Complex.I) * g z =
      -(∫ w : ℂ, (w - z)⁻¹ * crDefect g w) := by
  let F : ℂ → ℂ := fun w ↦ (w - z)⁻¹ * g w
  let H : ℂ → ℂ := fun w ↦ (w - z)⁻¹ * crDefect g w
  have hH : MeasureTheory.Integrable H := by
    simpa only [H] using integrable_cauchyKernel_mul_crDefect g hg hgc z
  obtain ⟨R, hR, hgR⟩ := hgc.isBounded.subset_ball_lt 1 z
  have hR0 : 0 < R := by linarith
  have houterBoundary :
      rectBoundaryIntegral F
          ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ = 0 := by
    simpa only [F] using
      rectBoundaryIntegral_cauchyKernel_mul_eq_zero_of_tsupport_subset_ball
        g z R hR0 hgR
  have hhorizontal (c : ℝ) (hc : c ≠ z.im) :
      IntervalIntegrable
        (fun x : ℝ ↦
          ((((x : ℂ) + c * Complex.I) - z)⁻¹ *
            g ((x : ℂ) + c * Complex.I)))
        MeasureTheory.volume (z.re - R) (z.re + R) := by
    have hne : ∀ x : ℝ, ((x : ℂ) + c * Complex.I) - z ≠ 0 := by
      intro x hx
      have him := congrArg Complex.im hx
      have : c = z.im := sub_eq_zero.mp (by simpa using him)
      exact hc this
    exact
      ((((Complex.continuous_ofReal.add
          (continuous_const.mul continuous_const)).sub continuous_const).inv₀ hne).mul
        (hg.continuous.comp
          (Complex.continuous_ofReal.add
            (continuous_const.mul continuous_const)))).intervalIntegrable _ _
  have hvertical (c : ℝ) (hc : c ≠ z.re) :
      IntervalIntegrable
        (fun y : ℝ ↦
          (((((c : ℂ) + y * Complex.I) - z)⁻¹ *
            g ((c : ℂ) + y * Complex.I))))
        MeasureTheory.volume (z.im - R) (z.im + R) := by
    have hne : ∀ y : ℝ, ((c : ℂ) + y * Complex.I) - z ≠ 0 := by
      intro y hy
      have hre := congrArg Complex.re hy
      have : c = z.re := sub_eq_zero.mp (by simpa using hre)
      exact hc this
    exact
      ((((continuous_const.add
          (Complex.continuous_ofReal.mul continuous_const)).sub continuous_const).inv₀ hne).mul
        (hg.continuous.comp
          (continuous_const.add
            (Complex.continuous_ofReal.mul continuous_const)))).intervalIntegrable _ _
  have hannulus (n : ℕ) :
      -(rectBoundaryIntegral F
          ⟨z.re - 1 / ((n : ℝ) + 1), z.im - 1 / ((n : ℝ) + 1)⟩
          ⟨z.re + 1 / ((n : ℝ) + 1), z.im + 1 / ((n : ℝ) + 1)⟩) =
        rectIntegral H
            ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ -
          rectIntegral H
            ⟨z.re - 1 / ((n : ℝ) + 1), z.im - 1 / ((n : ℝ) + 1)⟩
            ⟨z.re + 1 / ((n : ℝ) + 1), z.im + 1 / ((n : ℝ) + 1)⟩ := by
    let r : ℝ := 1 / ((n : ℝ) + 1)
    have hr : 0 < r := by
      dsimp [r]
      positivity
    have hr1 : r ≤ 1 := by
      dsimp [r]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) + 1)]
      norm_num
    have hrR : r ≤ R := hr1.trans hR.le
    have hbottom :
        rectBoundaryIntegral F
            ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im - r⟩ =
          rectIntegral H
            ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im - r⟩ := by
      simpa only [F, H] using
        rectBoundaryIntegral_cauchyKernel_mul g hg hgc z
          ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im - r⟩ (by
            intro hzmem
            have hy := hzmem.2
            change z.im ∈ [[z.im - R, z.im - r]] at hy
            rw [uIcc_of_le (by linarith), mem_Icc] at hy
            linarith)
    have htop :
        rectBoundaryIntegral F
            ⟨z.re - R, z.im + r⟩ ⟨z.re + R, z.im + R⟩ =
          rectIntegral H
            ⟨z.re - R, z.im + r⟩ ⟨z.re + R, z.im + R⟩ := by
      simpa only [F, H] using
        rectBoundaryIntegral_cauchyKernel_mul g hg hgc z
          ⟨z.re - R, z.im + r⟩ ⟨z.re + R, z.im + R⟩ (by
            intro hzmem
            have hy := hzmem.2
            change z.im ∈ [[z.im + r, z.im + R]] at hy
            rw [uIcc_of_le (by linarith), mem_Icc] at hy
            linarith)
    have hleft :
        rectBoundaryIntegral F
            ⟨z.re - R, z.im - r⟩ ⟨z.re - r, z.im + r⟩ =
          rectIntegral H
            ⟨z.re - R, z.im - r⟩ ⟨z.re - r, z.im + r⟩ := by
      simpa only [F, H] using
        rectBoundaryIntegral_cauchyKernel_mul g hg hgc z
          ⟨z.re - R, z.im - r⟩ ⟨z.re - r, z.im + r⟩ (by
            intro hzmem
            have hx := hzmem.1
            change z.re ∈ [[z.re - R, z.re - r]] at hx
            rw [uIcc_of_le (by linarith), mem_Icc] at hx
            linarith)
    have hright :
        rectBoundaryIntegral F
            ⟨z.re + r, z.im - r⟩ ⟨z.re + R, z.im + r⟩ =
          rectIntegral H
            ⟨z.re + r, z.im - r⟩ ⟨z.re + R, z.im + r⟩ := by
      simpa only [F, H] using
        rectBoundaryIntegral_cauchyKernel_mul g hg hgc z
          ⟨z.re + r, z.im - r⟩ ⟨z.re + R, z.im + r⟩ (by
            intro hzmem
            have hx := hzmem.1
            change z.re ∈ [[z.re + r, z.re + R]] at hx
            rw [uIcc_of_le (by linarith), mem_Icc] at hx
            linarith)
    have hbannulus :=
      rectBoundaryIntegral_annulus F
        (x₀ := z.re - R) (x₁ := z.re - r)
        (x₂ := z.re + r) (x₃ := z.re + R)
        (y₀ := z.im - R) (y₁ := z.im - r)
        (y₂ := z.im + r) (y₃ := z.im + R)
        (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith)
        (hhorizontal (z.im - r) (by linarith))
        (hhorizontal (z.im + r) (by linarith))
        (hvertical (z.re - R) (by linarith))
        (hvertical (z.re + R) (by linarith))
    have hiannulus :=
      rectIntegral_annulus H
        (x₀ := z.re - R) (x₁ := z.re - r)
        (x₂ := z.re + r) (x₃ := z.re + R)
        (y₀ := z.im - R) (y₁ := z.im - r)
        (y₂ := z.im + r) (y₃ := z.im + R)
        (by linarith) (by linarith) (by linarith)
        (by linarith) (by linarith) (by linarith) hH
    change
      -(rectBoundaryIntegral F
          ⟨z.re - r, z.im - r⟩ ⟨z.re + r, z.im + r⟩) =
        rectIntegral H
            ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ -
          rectIntegral H
            ⟨z.re - r, z.im - r⟩ ⟨z.re + r, z.im + r⟩
    calc
      _ = rectBoundaryIntegral F
              ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ -
            rectBoundaryIntegral F
              ⟨z.re - r, z.im - r⟩ ⟨z.re + r, z.im + r⟩ := by
            rw [houterBoundary]
            simp
      _ = rectBoundaryIntegral F
              ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im - r⟩ +
            rectBoundaryIntegral F
              ⟨z.re - R, z.im + r⟩ ⟨z.re + R, z.im + R⟩ +
            rectBoundaryIntegral F
              ⟨z.re - R, z.im - r⟩ ⟨z.re - r, z.im + r⟩ +
            rectBoundaryIntegral F
              ⟨z.re + r, z.im - r⟩ ⟨z.re + R, z.im + r⟩ :=
          hbannulus.symm
      _ = rectIntegral H
              ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im - r⟩ +
            rectIntegral H
              ⟨z.re - R, z.im + r⟩ ⟨z.re + R, z.im + R⟩ +
            rectIntegral H
              ⟨z.re - R, z.im - r⟩ ⟨z.re - r, z.im + r⟩ +
            rectIntegral H
              ⟨z.re + r, z.im - r⟩ ⟨z.re + R, z.im + r⟩ := by
          rw [hbottom, htop, hleft, hright]
      _ = _ := hiannulus
  have hinner :
      Filter.Tendsto
        (fun n : ℕ ↦
          rectIntegral H
            ⟨z.re - 1 / ((n : ℝ) + 1), z.im - 1 / ((n : ℝ) + 1)⟩
            ⟨z.re + 1 / ((n : ℝ) + 1), z.im + 1 / ((n : ℝ) + 1)⟩)
        Filter.atTop (𝓝 0) := by
    have h :=
      tendsto_setIntegral_shrinkingSquare_zero H hH z
    apply Filter.Tendsto.congr' ?_ h
    filter_upwards with n
    have hrn : 0 < (1 / ((n : ℝ) + 1) : ℝ) := by positivity
    rw [rectIntegral_eq_setIntegral H (by linarith) (by linarith) hH.integrableOn]
    rfl
  have hboundary :
      Filter.Tendsto
        (fun n : ℕ ↦
          rectBoundaryIntegral F
            ⟨z.re - 1 / ((n : ℝ) + 1), z.im - 1 / ((n : ℝ) + 1)⟩
            ⟨z.re + 1 / ((n : ℝ) + 1), z.im + 1 / ((n : ℝ) + 1)⟩)
        Filter.atTop (𝓝 ((2 * Real.pi * Complex.I) * g z)) := by
    simpa only [F] using
      tendsto_rectBoundaryIntegral_cauchyKernel_mul_shrinkingSquare
        g hg.continuous z
  have hlimit :
      -((2 * Real.pi * Complex.I) * g z) =
        rectIntegral H
          ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ := by
    have hleft := hboundary.neg
    have hright :=
      (tendsto_const_nhds.sub hinner :
        Filter.Tendsto
          (fun n : ℕ ↦
            rectIntegral H
                ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ -
              rectIntegral H
                ⟨z.re - 1 / ((n : ℝ) + 1), z.im - 1 / ((n : ℝ) + 1)⟩
                ⟨z.re + 1 / ((n : ℝ) + 1), z.im + 1 / ((n : ℝ) + 1)⟩)
          Filter.atTop
          (𝓝 (rectIntegral H
            ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ - 0)))
    simp only [sub_zero] at hright
    apply tendsto_nhds_unique hleft
    apply hright.congr'
    filter_upwards with n
    exact (hannulus n).symm
  have houter :
      rectIntegral H
          ⟨z.re - R, z.im - R⟩ ⟨z.re + R, z.im + R⟩ =
        ∫ w : ℂ, H w := by
    rw [rectIntegral_eq_setIntegral H (by linarith) (by linarith) hH.integrableOn]
    let Q : Set ℂ :=
      Set.Ioc (z.re - R) (z.re + R) ×ℂ
        Set.Ioc (z.im - R) (z.im + R)
    have hQ : MeasurableSet Q :=
      measurableSet_reProdIm measurableSet_Ioc measurableSet_Ioc
    change (∫ w : ℂ in Q, H w) = ∫ w : ℂ, H w
    rw [← MeasureTheory.integral_indicator hQ]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    by_cases hwQ : w ∈ Q
    · simp [hwQ]
    · have hwH : H w = 0 := by
        by_contra hw
        have hwD : crDefect g w ≠ 0 := by
          intro hwD
          exact hw (by simp [H, hwD])
        have hwt : w ∈ tsupport g :=
          tsupport_crDefect_subset g (subset_tsupport _ hwD)
        have hwb := hgR hwt
        rw [Metric.mem_ball, dist_eq_norm] at hwb
        have hre :
            |w.re - z.re| < R := by
          exact lt_of_le_of_lt
            (by simpa using Complex.abs_re_le_norm (w - z)) hwb
        have him :
            |w.im - z.im| < R := by
          exact lt_of_le_of_lt
            (by simpa using Complex.abs_im_le_norm (w - z)) hwb
        rw [abs_lt] at hre him
        apply hwQ
        exact
          ⟨⟨by linarith, by linarith⟩,
            ⟨by linarith, by linarith⟩⟩
      simp [hwQ, hwH]
  rw [houter] at hlimit
  change (2 * Real.pi * Complex.I) * g z = -(∫ w : ℂ, H w)
  linear_combination -hlimit

end Submission.Helpers
