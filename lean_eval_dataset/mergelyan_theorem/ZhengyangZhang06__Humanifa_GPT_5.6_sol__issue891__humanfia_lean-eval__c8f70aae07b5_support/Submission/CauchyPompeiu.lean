import Mathlib
import Submission.Smoothing

open Function Set
open scoped ContDiff Interval Topology

noncomputable section

namespace Submission.Helpers

/-- The planar Cauchy kernel is locally integrable.  Lean defines `0⁻¹ = 0`,
so the pointwise estimate by `‖z‖⁻¹` also covers the origin. -/
theorem locallyIntegrable_inv :
    MeasureTheory.LocallyIntegrable (fun z : ℂ ↦ z⁻¹) := by
  apply MeasureTheory.locallyIntegrable_of_norm_le_rpow
      (μ := MeasureTheory.volume) (C := 1) (α := 1)
  · norm_num
  · filter_upwards with z
    simp only [norm_inv, one_mul, Real.rpow_neg_one]
    exact le_rfl
  · exact measurable_inv.aestronglyMeasurable
  · norm_num

/-- Translation invariance of planar volume gives local integrability of a
Cauchy kernel with an arbitrary pole. -/
theorem locallyIntegrable_cauchyKernel (a : ℂ) :
    MeasureTheory.LocallyIntegrable (fun z : ℂ ↦ (z - a)⁻¹) := by
  rw [MeasureTheory.locallyIntegrable_iff]
  intro k hk
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.addRight (-a)
  have hki : IsCompact (e '' k) :=
    hk.image (Homeomorph.addRight (-a)).continuous
  have hi :
      MeasureTheory.IntegrableOn (fun z : ℂ ↦ z⁻¹) (e '' k) :=
    locallyIntegrable_inv.integrableOn_isCompact hki
  have ht :=
    (MeasureTheory.measurePreserving_add_right MeasureTheory.volume (-a)).integrableOn_comp_preimage
      e.measurableEmbedding (f := fun z : ℂ ↦ z⁻¹) (s := e '' k)
  have hpre := ht.mpr hi
  change
    MeasureTheory.IntegrableOn (fun z : ℂ ↦ (z + -a)⁻¹)
      ((fun z : ℂ ↦ z + -a) ⁻¹' (fun z : ℂ ↦ z + -a) '' k) at hpre
  rw [preimage_image_eq k (add_left_injective (-a))] at hpre
  simpa only [sub_eq_add_neg] using hpre

/-- Multiplying the Cauchy kernel by the compactly supported
Cauchy--Riemann defect of a smooth function gives a globally integrable
function. -/
theorem integrable_cauchyKernel_mul_crDefect (g : ℂ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (a : ℂ) :
    MeasureTheory.Integrable (fun z : ℂ ↦ (z - a)⁻¹ * crDefect g z) := by
  simpa only [smul_eq_mul] using
    (locallyIntegrable_cauchyKernel a).integrable_smul_right_of_hasCompactSupport
      (continuous_crDefect g hg) (crDefect_hasCompactSupport g hgc)

/-- The Cauchy--Riemann defect satisfies the Leibniz rule for real-differentiable
complex-valued functions. -/
theorem crDefect_mul {u v : ℂ → ℂ} {z : ℂ}
    (hu : DifferentiableAt ℝ u z) (hv : DifferentiableAt ℝ v z) :
    crDefect (fun w ↦ u w * v w) z =
      u z * crDefect v z + v z * crDefect u z := by
  rw [crDefect, fderiv_fun_mul hu hv, crDefect, crDefect]
  simp only [add_apply, smul_apply, smul_eq_mul]
  ring

/-- Away from its base point, the divided slope has the same
Cauchy--Riemann defect as the original function, multiplied by the Cauchy
kernel. -/
theorem crDefect_dslope_of_ne {g : ℂ → ℂ} {z w : ℂ}
    (hg : DifferentiableAt ℝ g w) (hw : w ≠ z) :
    crDefect (dslope g z) w = (w - z)⁻¹ * crDefect g w := by
  have hk : DifferentiableAt ℂ (fun x : ℂ ↦ (x - z)⁻¹) w :=
    (differentiableAt_id.sub_const z).inv (sub_ne_zero.mpr hw)
  have hsub : DifferentiableAt ℝ (fun x : ℂ ↦ g x - g z) w :=
    hg.sub_const (g z)
  have hmul :=
    crDefect_mul (z := w) (hk.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ)) hsub
  have hkzero :
      crDefect (fun x : ℂ ↦ (x - z)⁻¹) w = 0 :=
    crDefect_eq_zero_of_differentiableAt hk
  rw [hkzero, mul_zero, add_zero] at hmul
  simp only [crDefect, fderiv_sub_const] at hmul
  have hlocal :
      dslope g z =ᶠ[nhds w]
        fun x ↦ (x - z)⁻¹ * (g x - g z) := by
    filter_upwards [dslope_eventuallyEq_slope_of_ne g hw] with x hx
    rw [hx, slope_def_module, smul_eq_mul]
  rw [crDefect, hlocal.fderiv_eq (𝕜 := ℝ)]
  exact hmul

/-- The two horizontal sides of the normalized square contribute the
same even real kernel after their orientations are combined. -/
theorem cauchyKernel_horizontal_pair (x : ℝ) :
    ((x : ℂ) - Complex.I)⁻¹ - ((x : ℂ) + Complex.I)⁻¹ =
      (2 * Complex.I) * ((1 + x ^ 2)⁻¹ : ℝ) := by
  have hm : Complex.normSq ((x : ℂ) - Complex.I) = 1 + x ^ 2 := by
    rw [Complex.normSq_apply]
    norm_num
    ring
  have hp : Complex.normSq ((x : ℂ) + Complex.I) = 1 + x ^ 2 := by
    rw [Complex.normSq_apply]
    norm_num
    ring
  rw [Complex.inv_def, Complex.inv_def, hm, hp]
  simp only [map_sub, map_add, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The two vertical sides of the normalized square give the same
kernel as the horizontal pair. -/
theorem cauchyKernel_vertical_pair (x : ℝ) :
    Complex.I * ((1 : ℂ) + x * Complex.I)⁻¹ -
        Complex.I * ((-1 : ℂ) + x * Complex.I)⁻¹ =
      (2 * Complex.I) * ((1 + x ^ 2)⁻¹ : ℝ) := by
  have hr : Complex.normSq ((1 : ℂ) + x * Complex.I) = 1 + x ^ 2 := by
    rw [Complex.normSq_apply]
    norm_num
    ring
  have hl : Complex.normSq ((-1 : ℂ) + x * Complex.I) = 1 + x ^ 2 := by
    rw [Complex.normSq_apply]
    norm_num
    ring
  rw [Complex.inv_def, Complex.inv_def, hr, hl]
  simp only [map_add, map_mul, map_neg, map_one, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The positively oriented boundary integral of the Cauchy kernel around
the normalized square is `2πi`.  This is the normalization needed when the
rectangle form of Cauchy--Green is applied to a divided slope. -/
theorem integral_cauchyKernel_boundary_unitSquare :
    (∫ x : ℝ in (-1)..1, ((x : ℂ) - Complex.I)⁻¹) -
        (∫ x : ℝ in (-1)..1, ((x : ℂ) + Complex.I)⁻¹) +
      Complex.I * (∫ y : ℝ in (-1)..1, ((1 : ℂ) + y * Complex.I)⁻¹) -
      Complex.I * (∫ y : ℝ in (-1)..1, ((-1 : ℂ) + y * Complex.I)⁻¹) =
        2 * Real.pi * Complex.I := by
  have hm_ne : ∀ x : ℝ, (x : ℂ) - Complex.I ≠ 0 := by
    intro x hx
    have him := congrArg Complex.im hx
    norm_num at him
  have hp_ne : ∀ x : ℝ, (x : ℂ) + Complex.I ≠ 0 := by
    intro x hx
    have him := congrArg Complex.im hx
    norm_num at him
  have hr_ne : ∀ x : ℝ, (1 : ℂ) + x * Complex.I ≠ 0 := by
    intro x hx
    have hre := congrArg Complex.re hx
    norm_num at hre
  have hl_ne : ∀ x : ℝ, (-1 : ℂ) + x * Complex.I ≠ 0 := by
    intro x hx
    have hre := congrArg Complex.re hx
    norm_num at hre
  have hm :
      IntervalIntegrable (fun x : ℝ ↦ ((x : ℂ) - Complex.I)⁻¹)
        MeasureTheory.volume (-1) 1 :=
    ((Complex.continuous_ofReal.sub continuous_const).inv₀ hm_ne).intervalIntegrable _ _
  have hp :
      IntervalIntegrable (fun x : ℝ ↦ ((x : ℂ) + Complex.I)⁻¹)
        MeasureTheory.volume (-1) 1 :=
    ((Complex.continuous_ofReal.add continuous_const).inv₀ hp_ne).intervalIntegrable _ _
  have hr :
      IntervalIntegrable (fun x : ℝ ↦ ((1 : ℂ) + x * Complex.I)⁻¹)
        MeasureTheory.volume (-1) 1 :=
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
      hr_ne).intervalIntegrable _ _
  have hl :
      IntervalIntegrable (fun x : ℝ ↦ ((-1 : ℂ) + x * Complex.I)⁻¹)
        MeasureTheory.volume (-1) 1 :=
    ((continuous_const.add (Complex.continuous_ofReal.mul continuous_const)).inv₀
      hl_ne).intervalIntegrable _ _
  have hhorizontal :
      (∫ x : ℝ in (-1)..1, ((x : ℂ) - Complex.I)⁻¹) -
          (∫ x : ℝ in (-1)..1, ((x : ℂ) + Complex.I)⁻¹) =
        ∫ x : ℝ in (-1)..1, (2 * Complex.I) * ((1 + x ^ 2)⁻¹ : ℝ) := by
    rw [← intervalIntegral.integral_sub hm hp]
    exact intervalIntegral.integral_congr fun x _ ↦ cauchyKernel_horizontal_pair x
  have hvertical :
      Complex.I * (∫ x : ℝ in (-1)..1, ((1 : ℂ) + x * Complex.I)⁻¹) -
          Complex.I * (∫ x : ℝ in (-1)..1, ((-1 : ℂ) + x * Complex.I)⁻¹) =
        ∫ x : ℝ in (-1)..1, (2 * Complex.I) * ((1 + x ^ 2)⁻¹ : ℝ) := by
    calc
      _ = (∫ x : ℝ in (-1)..1, Complex.I * ((1 : ℂ) + x * Complex.I)⁻¹) -
          (∫ x : ℝ in (-1)..1, Complex.I * ((-1 : ℂ) + x * Complex.I)⁻¹) := by
            rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
      _ = ∫ x : ℝ in (-1)..1,
          Complex.I * ((1 : ℂ) + x * Complex.I)⁻¹ -
            Complex.I * ((-1 : ℂ) + x * Complex.I)⁻¹ :=
        (intervalIntegral.integral_sub (hr.const_mul Complex.I) (hl.const_mul Complex.I)).symm
      _ = _ := intervalIntegral.integral_congr fun x _ ↦ cauchyKernel_vertical_pair x
  have heval :
      (∫ x : ℝ in (-1)..1, (2 * Complex.I) * ((1 + x ^ 2)⁻¹ : ℝ)) =
        Real.pi * Complex.I := by
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_ofReal,
      integral_inv_one_add_sq]
    simp only [Real.arctan_neg, Real.arctan_one]
    push_cast
    ring
  calc
    _ = ((∫ x : ℝ in (-1)..1, ((x : ℂ) - Complex.I)⁻¹) -
          (∫ x : ℝ in (-1)..1, ((x : ℂ) + Complex.I)⁻¹)) +
        (Complex.I * (∫ y : ℝ in (-1)..1, ((1 : ℂ) + y * Complex.I)⁻¹) -
          Complex.I * (∫ y : ℝ in (-1)..1, ((-1 : ℂ) + y * Complex.I)⁻¹)) := by
            ring
    _ = _ := by rw [hhorizontal, hvertical, heval]; ring

theorem ofReal_mul_scaled_inv (r : ℝ) (hr : r ≠ 0) (u : ℂ) :
    (r : ℂ) * ((r : ℂ) * u)⁻¹ = u⁻¹ := by
  have hr' : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  rw [mul_inv_rev]
  calc
    (r : ℂ) * (u⁻¹ * (r : ℂ)⁻¹) =
        ((r : ℂ) * (r : ℂ)⁻¹) * u⁻¹ := by ring
    _ = u⁻¹ := by rw [mul_inv_cancel₀ hr', one_mul]

/-- Rescaling and translating a horizontal side leaves its Cauchy-kernel
integral in normalized coordinates. -/
theorem integral_cauchyKernel_horizontal_scaled (z : ℂ) (r : ℝ) (hr : r ≠ 0)
    (y : ℝ) :
    (∫ x : ℝ in z.re - r..z.re + r,
        (((x : ℂ) + (z.im + r * y) * Complex.I) - z)⁻¹) =
      ∫ t : ℝ in (-1)..1, ((t : ℂ) + y * Complex.I)⁻¹ := by
  rw [show z.re - r = r * (-1) + z.re by ring,
    show z.re + r = r * 1 + z.re by ring,
    ← intervalIntegral.smul_integral_comp_mul_add]
  simp only [Complex.real_smul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have harg :
      (((r * t + z.re : ℝ) : ℂ) +
          (z.im + r * y) * Complex.I) - z =
        (r : ℂ) * ((t : ℂ) + y * Complex.I) := by
    apply Complex.ext <;> simp
  push_cast at harg ⊢
  rw [harg, ofReal_mul_scaled_inv r hr]

/-- Rescaling and translating a vertical side leaves its Cauchy-kernel
integral in normalized coordinates. -/
theorem integral_cauchyKernel_vertical_scaled (z : ℂ) (r : ℝ) (hr : r ≠ 0)
    (x : ℝ) :
    (∫ y : ℝ in z.im - r..z.im + r,
        ((((z.re + r * x : ℝ) : ℂ) + y * Complex.I) - z)⁻¹) =
      ∫ t : ℝ in (-1)..1, ((x : ℂ) + t * Complex.I)⁻¹ := by
  rw [show z.im - r = r * (-1) + z.im by ring,
    show z.im + r = r * 1 + z.im by ring,
    ← intervalIntegral.smul_integral_comp_mul_add]
  simp only [Complex.real_smul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  have harg :
      (((z.re + r * x : ℝ) : ℂ) +
          (r * t + z.im) * Complex.I) - z =
        (r : ℂ) * ((x : ℂ) + t * Complex.I) := by
    apply Complex.ext <;> simp
  push_cast at harg ⊢
  rw [harg, ofReal_mul_scaled_inv r hr]

theorem integral_cauchyKernel_mul_horizontal_scaled (G : ℂ → ℂ)
    (z : ℂ) (r : ℝ) (hr : r ≠ 0) (y : ℝ) :
    (∫ x : ℝ in z.re - r..z.re + r,
        ((((x : ℂ) + (z.im + r * y) * Complex.I) - z)⁻¹ *
          G ((x : ℂ) + (z.im + r * y) * Complex.I))) =
      ∫ t : ℝ in (-1)..1,
        ((t : ℂ) + y * Complex.I)⁻¹ *
          G (z + (r : ℂ) * ((t : ℂ) + y * Complex.I)) := by
  rw [show z.re - r = r * (-1) + z.re by ring,
    show z.re + r = r * 1 + z.re by ring,
    ← intervalIntegral.smul_integral_comp_mul_add]
  simp only [Complex.real_smul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  let u : ℂ := (t : ℂ) + y * Complex.I
  let w : ℂ := ((r * t + z.re : ℝ) : ℂ) +
    (z.im + r * y) * Complex.I
  have hwsub : w - z = (r : ℂ) * u := by
    dsimp [w, u]
    apply Complex.ext <;> simp
  have hw : w = z + (r : ℂ) * u := by
    calc
      w = z + (w - z) := by ring
      _ = z + (r : ℂ) * u := by rw [hwsub]
  dsimp only [w, u] at hwsub hw ⊢
  push_cast at hwsub hw ⊢
  rw [← mul_assoc, hwsub, ofReal_mul_scaled_inv r hr, hw]

theorem integral_cauchyKernel_mul_vertical_scaled (G : ℂ → ℂ)
    (z : ℂ) (r : ℝ) (hr : r ≠ 0) (x : ℝ) :
    (∫ y : ℝ in z.im - r..z.im + r,
        (((((z.re + r * x : ℝ) : ℂ) + y * Complex.I) - z)⁻¹ *
          G (((z.re + r * x : ℝ) : ℂ) + y * Complex.I))) =
      ∫ t : ℝ in (-1)..1,
        ((x : ℂ) + t * Complex.I)⁻¹ *
          G (z + (r : ℂ) * ((x : ℂ) + t * Complex.I)) := by
  rw [show z.im - r = r * (-1) + z.im by ring,
    show z.im + r = r * 1 + z.im by ring,
    ← intervalIntegral.smul_integral_comp_mul_add]
  simp only [Complex.real_smul, ← intervalIntegral.integral_const_mul]
  apply intervalIntegral.integral_congr
  intro t _
  let u : ℂ := (x : ℂ) + t * Complex.I
  let w : ℂ := ((z.re + r * x : ℝ) : ℂ) +
    (r * t + z.im) * Complex.I
  have hwsub : w - z = (r : ℂ) * u := by
    dsimp [w, u]
    apply Complex.ext <;> simp
  have hw : w = z + (r : ℂ) * u := by
    calc
      w = z + (w - z) := by ring
      _ = z + (r : ℂ) * u := by rw [hwsub]
  dsimp only [w, u] at hwsub hw ⊢
  push_cast at hwsub hw ⊢
  rw [← mul_assoc, hwsub, ofReal_mul_scaled_inv r hr, hw]

/-- The Cauchy-kernel boundary integral on a square, expressed on four fixed
copies of `[-1,1]`.  This normalization makes the limit as the square shrinks
an ordinary parametric-integral continuity statement. -/
def normalizedSquareBoundary (G : ℂ → ℂ) (z : ℂ) (r : ℝ) : ℂ :=
  (∫ t : ℝ in (-1)..1, ((t : ℂ) - Complex.I)⁻¹ *
      G (z + (r : ℂ) * ((t : ℂ) - Complex.I))) -
    (∫ t : ℝ in (-1)..1, ((t : ℂ) + Complex.I)⁻¹ *
      G (z + (r : ℂ) * ((t : ℂ) + Complex.I))) +
    Complex.I * (∫ t : ℝ in (-1)..1,
      ((1 : ℂ) + t * Complex.I)⁻¹ *
        G (z + (r : ℂ) * ((1 : ℂ) + t * Complex.I))) -
    Complex.I * (∫ t : ℝ in (-1)..1,
      ((-1 : ℂ) + t * Complex.I)⁻¹ *
        G (z + (r : ℂ) * ((-1 : ℂ) + t * Complex.I)))

/-- The positively oriented integral of a function around the boundary of the
rectangle with opposite corners `a` and `b`. -/
def rectBoundaryIntegral (F : ℂ → ℂ) (a b : ℂ) : ℂ :=
  (∫ x : ℝ in a.re..b.re, F (x + a.im * Complex.I)) -
      (∫ x : ℝ in a.re..b.re, F (x + b.im * Complex.I)) +
    Complex.I * (∫ y : ℝ in a.im..b.im, F (b.re + y * Complex.I)) -
    Complex.I * (∫ y : ℝ in a.im..b.im, F (a.re + y * Complex.I))

/-- The iterated integral of a function over the rectangle with opposite
corners `a` and `b`. -/
def rectIntegral (F : ℂ → ℂ) (a b : ℂ) : ℂ :=
  ∫ x : ℝ in a.re..b.re, ∫ y : ℝ in a.im..b.im,
    F (x + y * Complex.I)

/-- For ordered corners, the iterated rectangle integral agrees with the
planar set integral. -/
theorem rectIntegral_eq_setIntegral (F : ℂ → ℂ)
    {x₀ x₁ y₀ y₁ : ℝ} (hx : x₀ ≤ x₁) (hy : y₀ ≤ y₁)
    (hF : MeasureTheory.IntegrableOn F
      (Ioc x₀ x₁ ×ℂ Ioc y₀ y₁)) :
    rectIntegral F ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ =
      ∫ w : ℂ in Ioc x₀ x₁ ×ℂ Ioc y₀ y₁, F w := by
  let e : ℝ × ℝ ≃ᵐ ℂ := Complex.measurableEquivRealProd.symm
  have hpre :
      e ⁻¹' (Ioc x₀ x₁ ×ℂ Ioc y₀ y₁) =
        Ioc x₀ x₁ ×ˢ Ioc y₀ y₁ :=
    rfl
  have hcomp :
      MeasureTheory.IntegrableOn (F ∘ e)
        (Ioc x₀ x₁ ×ˢ Ioc y₀ y₁) := by
    rw [← hpre]
    exact
      ((Complex.volume_preserving_equiv_real_prod.symm _).integrableOn_comp_preimage
        e.measurableEmbedding).mpr hF
  have he :
      (F ∘ e) =
        fun p : ℝ × ℝ ↦ F ((p.1 : ℂ) + p.2 * Complex.I) := by
    funext p
    apply congrArg F
    apply Complex.ext <;> simp [e]
  rw [he] at hcomp
  rw [rectIntegral, intervalIntegral.integral_of_le hx]
  simp_rw [intervalIntegral.integral_of_le hy]
  calc
    _ = ∫ p : ℝ × ℝ in Ioc x₀ x₁ ×ˢ Ioc y₀ y₁,
          F ((p.1 : ℂ) + p.2 * Complex.I) :=
      (MeasureTheory.setIntegral_prod
        (fun p : ℝ × ℝ ↦ F ((p.1 : ℂ) + p.2 * Complex.I)) hcomp).symm
    _ = ∫ p : ℝ × ℝ in Ioc x₀ x₁ ×ˢ Ioc y₀ y₁, F (e p) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with p
      have hep : e p = (p.1 : ℂ) + p.2 * Complex.I := by
        apply Complex.ext <;> simp [e]
      rw [hep]
    _ = _ := by
      rw [← hpre]
      exact
        (Complex.volume_preserving_equiv_real_prod.symm _).setIntegral_preimage_emb
          e.measurableEmbedding F (Ioc x₀ x₁ ×ℂ Ioc y₀ y₁)

/-- Boundary integrals cancel on the four rectangles forming a rectangular
annulus. -/
theorem rectBoundaryIntegral_annulus (F : ℂ → ℂ)
    {x₀ x₁ x₂ x₃ y₀ y₁ y₂ y₃ : ℝ}
    (hx₀₁ : x₀ ≤ x₁) (hx₁₂ : x₁ ≤ x₂) (hx₂₃ : x₂ ≤ x₃)
    (hy₀₁ : y₀ ≤ y₁) (hy₁₂ : y₁ ≤ y₂) (hy₂₃ : y₂ ≤ y₃)
    (hHy₁ : IntervalIntegrable (fun x : ℝ ↦ F (x + y₁ * Complex.I))
      MeasureTheory.volume x₀ x₃)
    (hHy₂ : IntervalIntegrable (fun x : ℝ ↦ F (x + y₂ * Complex.I))
      MeasureTheory.volume x₀ x₃)
    (hVx₀ : IntervalIntegrable (fun y : ℝ ↦ F (x₀ + y * Complex.I))
      MeasureTheory.volume y₀ y₃)
    (hVx₃ : IntervalIntegrable (fun y : ℝ ↦ F (x₃ + y * Complex.I))
      MeasureTheory.volume y₀ y₃) :
    rectBoundaryIntegral F ⟨x₀, y₀⟩ ⟨x₃, y₁⟩ +
        rectBoundaryIntegral F ⟨x₀, y₂⟩ ⟨x₃, y₃⟩ +
        rectBoundaryIntegral F ⟨x₀, y₁⟩ ⟨x₁, y₂⟩ +
        rectBoundaryIntegral F ⟨x₂, y₁⟩ ⟨x₃, y₂⟩ =
      rectBoundaryIntegral F ⟨x₀, y₀⟩ ⟨x₃, y₃⟩ -
        rectBoundaryIntegral F ⟨x₁, y₁⟩ ⟨x₂, y₂⟩ := by
  have hHy₁01 : IntervalIntegrable (fun x : ℝ ↦ F (x + y₁ * Complex.I))
      MeasureTheory.volume x₀ x₁ := hHy₁.mono_set (by grind [uIcc])
  have hHy₁12 : IntervalIntegrable (fun x : ℝ ↦ F (x + y₁ * Complex.I))
      MeasureTheory.volume x₁ x₂ := hHy₁.mono_set (by grind [uIcc])
  have hHy₁23 : IntervalIntegrable (fun x : ℝ ↦ F (x + y₁ * Complex.I))
      MeasureTheory.volume x₂ x₃ := hHy₁.mono_set (by grind [uIcc])
  have hHy₂01 : IntervalIntegrable (fun x : ℝ ↦ F (x + y₂ * Complex.I))
      MeasureTheory.volume x₀ x₁ := hHy₂.mono_set (by grind [uIcc])
  have hHy₂12 : IntervalIntegrable (fun x : ℝ ↦ F (x + y₂ * Complex.I))
      MeasureTheory.volume x₁ x₂ := hHy₂.mono_set (by grind [uIcc])
  have hHy₂23 : IntervalIntegrable (fun x : ℝ ↦ F (x + y₂ * Complex.I))
      MeasureTheory.volume x₂ x₃ := hHy₂.mono_set (by grind [uIcc])
  have hVx₀01 : IntervalIntegrable (fun y : ℝ ↦ F (x₀ + y * Complex.I))
      MeasureTheory.volume y₀ y₁ := hVx₀.mono_set (by grind [uIcc])
  have hVx₀12 : IntervalIntegrable (fun y : ℝ ↦ F (x₀ + y * Complex.I))
      MeasureTheory.volume y₁ y₂ := hVx₀.mono_set (by grind [uIcc])
  have hVx₀23 : IntervalIntegrable (fun y : ℝ ↦ F (x₀ + y * Complex.I))
      MeasureTheory.volume y₂ y₃ := hVx₀.mono_set (by grind [uIcc])
  have hVx₃01 : IntervalIntegrable (fun y : ℝ ↦ F (x₃ + y * Complex.I))
      MeasureTheory.volume y₀ y₁ := hVx₃.mono_set (by grind [uIcc])
  have hVx₃12 : IntervalIntegrable (fun y : ℝ ↦ F (x₃ + y * Complex.I))
      MeasureTheory.volume y₁ y₂ := hVx₃.mono_set (by grind [uIcc])
  have hVx₃23 : IntervalIntegrable (fun y : ℝ ↦ F (x₃ + y * Complex.I))
      MeasureTheory.volume y₂ y₃ := hVx₃.mono_set (by grind [uIcc])
  have hHy₁split :
      ((∫ x : ℝ in x₀..x₁, F (x + y₁ * Complex.I)) +
          ∫ x : ℝ in x₁..x₂, F (x + y₁ * Complex.I)) +
        (∫ x : ℝ in x₂..x₃, F (x + y₁ * Complex.I)) =
      ∫ x : ℝ in x₀..x₃, F (x + y₁ * Complex.I) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hHy₁01 hHy₁12,
      intervalIntegral.integral_add_adjacent_intervals
        (hHy₁01.trans hHy₁12) hHy₁23]
  have hHy₂split :
      ((∫ x : ℝ in x₀..x₁, F (x + y₂ * Complex.I)) +
          ∫ x : ℝ in x₁..x₂, F (x + y₂ * Complex.I)) +
        (∫ x : ℝ in x₂..x₃, F (x + y₂ * Complex.I)) =
      ∫ x : ℝ in x₀..x₃, F (x + y₂ * Complex.I) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hHy₂01 hHy₂12,
      intervalIntegral.integral_add_adjacent_intervals
        (hHy₂01.trans hHy₂12) hHy₂23]
  have hVx₀split :
      ((∫ y : ℝ in y₀..y₁, F (x₀ + y * Complex.I)) +
          ∫ y : ℝ in y₁..y₂, F (x₀ + y * Complex.I)) +
        (∫ y : ℝ in y₂..y₃, F (x₀ + y * Complex.I)) =
      ∫ y : ℝ in y₀..y₃, F (x₀ + y * Complex.I) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hVx₀01 hVx₀12,
      intervalIntegral.integral_add_adjacent_intervals
        (hVx₀01.trans hVx₀12) hVx₀23]
  have hVx₃split :
      ((∫ y : ℝ in y₀..y₁, F (x₃ + y * Complex.I)) +
          ∫ y : ℝ in y₁..y₂, F (x₃ + y * Complex.I)) +
        (∫ y : ℝ in y₂..y₃, F (x₃ + y * Complex.I)) =
      ∫ y : ℝ in y₀..y₃, F (x₃ + y * Complex.I) := by
    rw [intervalIntegral.integral_add_adjacent_intervals hVx₃01 hVx₃12,
      intervalIntegral.integral_add_adjacent_intervals
        (hVx₃01.trans hVx₃12) hVx₃23]
  simp only [rectBoundaryIntegral]
  rw [← hHy₁split, ← hHy₂split, ← hVx₀split, ← hVx₃split]
  ring

/-- The Cauchy-kernel boundary integral is invariant under translations and
nonzero real rescalings of the normalized square. -/
theorem rectBoundaryIntegral_cauchyKernel_square (z : ℂ) (r : ℝ) (hr : r ≠ 0) :
    rectBoundaryIntegral (fun w ↦ (w - z)⁻¹)
        ⟨z.re - r, z.im - r⟩ ⟨z.re + r, z.im + r⟩ =
      2 * Real.pi * Complex.I := by
  simp only [rectBoundaryIntegral]
  have hbottom :
      (∫ x : ℝ in z.re - r..z.re + r,
          (((x : ℂ) + (z.im - r) * Complex.I) - z)⁻¹) =
        ∫ t : ℝ in (-1)..1, ((t : ℂ) - Complex.I)⁻¹ := by
    simpa only [sub_eq_add_neg, mul_neg, mul_one, Complex.ofReal_neg,
      Complex.ofReal_one, neg_mul, one_mul] using
      integral_cauchyKernel_horizontal_scaled z r hr (-1)
  have htop :
      (∫ x : ℝ in z.re - r..z.re + r,
          (((x : ℂ) + (z.im + r) * Complex.I) - z)⁻¹) =
        ∫ t : ℝ in (-1)..1, ((t : ℂ) + Complex.I)⁻¹ := by
    simpa only [mul_one, Complex.ofReal_one, one_mul] using
      integral_cauchyKernel_horizontal_scaled z r hr 1
  have hright :
      (∫ y : ℝ in z.im - r..z.im + r,
          ((((z.re + r : ℝ) : ℂ) + y * Complex.I) - z)⁻¹) =
        ∫ t : ℝ in (-1)..1, ((1 : ℂ) + t * Complex.I)⁻¹ := by
    simpa only [mul_one, Complex.ofReal_one, one_mul] using
      integral_cauchyKernel_vertical_scaled z r hr 1
  have hleft :
      (∫ y : ℝ in z.im - r..z.im + r,
          ((((z.re - r : ℝ) : ℂ) + y * Complex.I) - z)⁻¹) =
        ∫ t : ℝ in (-1)..1, ((-1 : ℂ) + t * Complex.I)⁻¹ := by
    simpa only [sub_eq_add_neg, mul_neg, mul_one, Complex.ofReal_neg,
      Complex.ofReal_one, neg_mul, one_mul] using
      integral_cauchyKernel_vertical_scaled z r hr (-1)
  push_cast at hbottom htop hright hleft ⊢
  rw [hbottom, htop, hright, hleft]
  simpa only [Complex.ofReal_neg, Complex.ofReal_one, neg_mul, one_mul,
    sub_eq_add_neg] using
    integral_cauchyKernel_boundary_unitSquare

theorem rectBoundaryIntegral_cauchyKernel_mul_square (G : ℂ → ℂ)
    (z : ℂ) (r : ℝ) (hr : r ≠ 0) :
    rectBoundaryIntegral (fun w ↦ (w - z)⁻¹ * G w)
        ⟨z.re - r, z.im - r⟩ ⟨z.re + r, z.im + r⟩ =
      normalizedSquareBoundary G z r := by
  simp only [rectBoundaryIntegral]
  have hbottom :
      (∫ x : ℝ in z.re - r..z.re + r,
          ((((x : ℂ) + (z.im - r) * Complex.I) - z)⁻¹ *
            G ((x : ℂ) + (z.im - r) * Complex.I))) =
        ∫ t : ℝ in (-1)..1, ((t : ℂ) - Complex.I)⁻¹ *
          G (z + (r : ℂ) * ((t : ℂ) - Complex.I)) := by
    simpa only [sub_eq_add_neg, mul_neg, mul_one, Complex.ofReal_neg,
      Complex.ofReal_one, neg_mul, one_mul] using
      integral_cauchyKernel_mul_horizontal_scaled G z r hr (-1)
  have htop :
      (∫ x : ℝ in z.re - r..z.re + r,
          ((((x : ℂ) + (z.im + r) * Complex.I) - z)⁻¹ *
            G ((x : ℂ) + (z.im + r) * Complex.I))) =
        ∫ t : ℝ in (-1)..1, ((t : ℂ) + Complex.I)⁻¹ *
          G (z + (r : ℂ) * ((t : ℂ) + Complex.I)) := by
    simpa only [mul_one, Complex.ofReal_one, one_mul] using
      integral_cauchyKernel_mul_horizontal_scaled G z r hr 1
  have hright :
      (∫ y : ℝ in z.im - r..z.im + r,
          (((((z.re + r : ℝ) : ℂ) + y * Complex.I) - z)⁻¹ *
            G (((z.re + r : ℝ) : ℂ) + y * Complex.I))) =
        ∫ t : ℝ in (-1)..1, ((1 : ℂ) + t * Complex.I)⁻¹ *
          G (z + (r : ℂ) * ((1 : ℂ) + t * Complex.I)) := by
    simpa only [mul_one, Complex.ofReal_one, one_mul] using
      integral_cauchyKernel_mul_vertical_scaled G z r hr 1
  have hleft :
      (∫ y : ℝ in z.im - r..z.im + r,
          (((((z.re - r : ℝ) : ℂ) + y * Complex.I) - z)⁻¹ *
            G (((z.re - r : ℝ) : ℂ) + y * Complex.I))) =
        ∫ t : ℝ in (-1)..1, ((-1 : ℂ) + t * Complex.I)⁻¹ *
          G (z + (r : ℂ) * ((-1 : ℂ) + t * Complex.I)) := by
    simpa only [sub_eq_add_neg, mul_neg, mul_one, Complex.ofReal_neg,
      Complex.ofReal_one, neg_mul, one_mul] using
      integral_cauchyKernel_mul_vertical_scaled G z r hr (-1)
  push_cast at hbottom htop hright hleft ⊢
  rw [hbottom, htop, hright, hleft]
  simp only [normalizedSquareBoundary, sub_eq_add_neg]

theorem normalizedSquareBoundary_zero (G : ℂ → ℂ) (z : ℂ) :
    normalizedSquareBoundary G z 0 =
      (2 * Real.pi * Complex.I) * G z := by
  simp only [normalizedSquareBoundary, Complex.ofReal_zero, zero_mul, add_zero,
    intervalIntegral.integral_mul_const]
  calc
    _ = ((∫ t : ℝ in (-1)..1, ((t : ℂ) - Complex.I)⁻¹) -
          (∫ t : ℝ in (-1)..1, ((t : ℂ) + Complex.I)⁻¹) +
          Complex.I * (∫ t : ℝ in (-1)..1,
            ((1 : ℂ) + t * Complex.I)⁻¹) -
          Complex.I * (∫ t : ℝ in (-1)..1,
            ((-1 : ℂ) + t * Complex.I)⁻¹)) * G z := by
            ring
    _ = _ := by rw [integral_cauchyKernel_boundary_unitSquare]

theorem continuous_normalizedSquareBoundary (G : ℂ → ℂ) (hG : Continuous G)
    (z : ℂ) :
    Continuous (normalizedSquareBoundary G z) := by
  have hm_ne : ∀ t : ℝ, (t : ℂ) - Complex.I ≠ 0 := by
    intro t ht
    have him := congrArg Complex.im ht
    norm_num at him
  have hp_ne : ∀ t : ℝ, (t : ℂ) + Complex.I ≠ 0 := by
    intro t ht
    have him := congrArg Complex.im ht
    norm_num at him
  have hr_ne : ∀ t : ℝ, (1 : ℂ) + t * Complex.I ≠ 0 := by
    intro t ht
    have hre := congrArg Complex.re ht
    norm_num at hre
  have hl_ne : ∀ t : ℝ, (-1 : ℂ) + t * Complex.I ≠ 0 := by
    intro t ht
    have hre := congrArg Complex.re ht
    norm_num at hre
  have hkm : Continuous fun t : ℝ ↦ ((t : ℂ) - Complex.I)⁻¹ :=
    (Complex.continuous_ofReal.sub continuous_const).inv₀ hm_ne
  have hkp : Continuous fun t : ℝ ↦ ((t : ℂ) + Complex.I)⁻¹ :=
    (Complex.continuous_ofReal.add continuous_const).inv₀ hp_ne
  have hkr : Continuous fun t : ℝ ↦ ((1 : ℂ) + t * Complex.I)⁻¹ :=
    (continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).inv₀ hr_ne
  have hkl : Continuous fun t : ℝ ↦ ((-1 : ℂ) + t * Complex.I)⁻¹ :=
    (continuous_const.add
      (Complex.continuous_ofReal.mul continuous_const)).inv₀ hl_ne
  have hm : Continuous fun r : ℝ ↦
      ∫ t : ℝ in (-1)..1, ((t : ℂ) - Complex.I)⁻¹ *
        G (z + (r : ℂ) * ((t : ℂ) - Complex.I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous fun p : ℝ × ℝ ↦
      ((p.2 : ℂ) - Complex.I)⁻¹ *
        G (z + (p.1 : ℂ) * ((p.2 : ℂ) - Complex.I))
    exact (hkm.comp continuous_snd).mul (hG.comp (by fun_prop))
  have hp : Continuous fun r : ℝ ↦
      ∫ t : ℝ in (-1)..1, ((t : ℂ) + Complex.I)⁻¹ *
        G (z + (r : ℂ) * ((t : ℂ) + Complex.I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous fun p : ℝ × ℝ ↦
      ((p.2 : ℂ) + Complex.I)⁻¹ *
        G (z + (p.1 : ℂ) * ((p.2 : ℂ) + Complex.I))
    exact (hkp.comp continuous_snd).mul (hG.comp (by fun_prop))
  have hr : Continuous fun r : ℝ ↦
      ∫ t : ℝ in (-1)..1, ((1 : ℂ) + t * Complex.I)⁻¹ *
        G (z + (r : ℂ) * ((1 : ℂ) + t * Complex.I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous fun p : ℝ × ℝ ↦
      ((1 : ℂ) + p.2 * Complex.I)⁻¹ *
        G (z + (p.1 : ℂ) * ((1 : ℂ) + p.2 * Complex.I))
    exact (hkr.comp continuous_snd).mul (hG.comp (by fun_prop))
  have hl : Continuous fun r : ℝ ↦
      ∫ t : ℝ in (-1)..1, ((-1 : ℂ) + t * Complex.I)⁻¹ *
        G (z + (r : ℂ) * ((-1 : ℂ) + t * Complex.I)) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
    change Continuous fun p : ℝ × ℝ ↦
      ((-1 : ℂ) + p.2 * Complex.I)⁻¹ *
        G (z + (p.1 : ℂ) * ((-1 : ℂ) + p.2 * Complex.I))
    exact (hkl.comp continuous_snd).mul (hG.comp (by fun_prop))
  exact ((hm.sub hp).add (continuous_const.mul hr)).sub
    (continuous_const.mul hl)

theorem tendsto_rectBoundaryIntegral_cauchyKernel_mul_square (G : ℂ → ℂ)
    (hG : Continuous G) (z : ℂ) :
    Filter.Tendsto
      (fun r : ℝ ↦
        rectBoundaryIntegral (fun w ↦ (w - z)⁻¹ * G w)
          ⟨z.re - r, z.im - r⟩ ⟨z.re + r, z.im + r⟩)
      (𝓝[≠] 0) (𝓝 ((2 * Real.pi * Complex.I) * G z)) := by
  have hlim :
      Filter.Tendsto (normalizedSquareBoundary G z) (𝓝[≠] 0)
        (𝓝 ((2 * Real.pi * Complex.I) * G z)) := by
    have h :=
      (continuous_normalizedSquareBoundary G hG z).tendsto 0
    rw [normalizedSquareBoundary_zero] at h
    exact h.mono_left inf_le_left
  apply Filter.Tendsto.congr' ?_ hlim
  filter_upwards [self_mem_nhdsWithin] with r hr
  exact (rectBoundaryIntegral_cauchyKernel_mul_square G z r (by simpa using hr)).symm

/-- Cauchy--Green on a rectangle, specialized to the real differential's
Cauchy--Riemann defect. -/
theorem rectBoundaryIntegral_eq_rectIntegral_crDefect (F : ℂ → ℂ) (a b : ℂ)
    (hF : DifferentiableOn ℝ F
      ([[a.re, b.re]] ×ℂ [[a.im, b.im]]))
    (hFi : MeasureTheory.IntegrableOn (crDefect F)
      ([[a.re, b.re]] ×ℂ [[a.im, b.im]])) :
    rectBoundaryIntegral F a b = rectIntegral (crDefect F) a b := by
  simpa only [rectBoundaryIntegral, rectIntegral, crDefect, smul_eq_mul] using
    Complex.integral_boundary_rect_of_differentiableOn_real F a b hF hFi

/-- If the pole is outside a rectangle, Cauchy--Green applied to the Cauchy
kernel times a smooth compactly supported function has the expected
kernel-times-defect integrand. -/
theorem rectBoundaryIntegral_cauchyKernel_mul (g : ℂ → ℂ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g) (z a b : ℂ)
    (hz : z ∉ ([[a.re, b.re]] ×ℂ [[a.im, b.im]])) :
    rectBoundaryIntegral (fun w ↦ (w - z)⁻¹ * g w) a b =
      rectIntegral (fun w ↦ (w - z)⁻¹ * crDefect g w) a b := by
  let R : Set ℂ := [[a.re, b.re]] ×ℂ [[a.im, b.im]]
  have hzne : ∀ w ∈ R, w ≠ z := by
    intro w hw hwz
    apply hz
    simpa only [hwz] using hw
  have hk : DifferentiableOn ℝ (fun w : ℂ ↦ (w - z)⁻¹) R := by
    intro w hw
    exact
      (((differentiableAt_id.sub_const z).inv
        (sub_ne_zero.mpr (hzne w hw))).restrictScalars
        (𝕜 := ℝ) (𝕜' := ℂ)).differentiableWithinAt
  have hprod :
      DifferentiableOn ℝ (fun w ↦ (w - z)⁻¹ * g w) R :=
    hk.mul (hg.differentiable (by simp)).differentiableOn
  have hRmeas : MeasurableSet R := by
    apply IsClosed.measurableSet
    apply IsClosed.reProdIm <;> rw [uIcc] <;> exact isClosed_Icc
  have hi :
      MeasureTheory.IntegrableOn
        (crDefect fun w ↦ (w - z)⁻¹ * g w) R := by
    have hpoint : ∀ w ∈ R,
        crDefect (fun u ↦ (u - z)⁻¹ * g u) w =
          (w - z)⁻¹ * crDefect g w := by
      intro w hw
      have hkw : DifferentiableAt ℂ (fun u : ℂ ↦ (u - z)⁻¹) w :=
        (differentiableAt_id.sub_const z).inv
          (sub_ne_zero.mpr (hzne w hw))
      simpa only [crDefect_eq_zero_of_differentiableAt hkw, mul_zero, add_zero] using
        crDefect_mul
          (hkw.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ))
          ((hg.differentiable (by simp)).differentiableAt)
    refine
      (integrable_cauchyKernel_mul_crDefect g hg hgc z).integrableOn.congr_fun
        ?_ hRmeas
    intro w hw
    exact (hpoint w hw).symm
  rw [rectBoundaryIntegral_eq_rectIntegral_crDefect _ _ _ hprod hi]
  apply intervalIntegral.integral_congr
  intro x hx
  apply intervalIntegral.integral_congr
  intro y hy
  have hw : x + y * Complex.I ∈ R := by
    constructor
    · simpa using hx
    · simpa using hy
  have hkw : DifferentiableAt ℂ (fun u : ℂ ↦ (u - z)⁻¹)
      (x + y * Complex.I) :=
    (differentiableAt_id.sub_const z).inv
      (sub_ne_zero.mpr (hzne _ hw))
  simpa only [crDefect_eq_zero_of_differentiableAt hkw, mul_zero, add_zero] using
    crDefect_mul
      (hkw.restrictScalars (𝕜 := ℝ) (𝕜' := ℂ))
      ((hg.differentiable (by simp)).differentiableAt)

end Submission.Helpers
