import Submission.BoundaryLocalization

open Function Set
open scoped Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- Every positive power of a resolvent with pole off `K` belongs to the
closed polynomial algebra on `K`. -/
theorem exists_resolventPow_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {a : ℂ} (ha : a ∉ K) (n : ℕ) :
    ∃ g : (polynomialFunctions K).topologicalClosure,
      ∀ z : K, (g : C(K, ℂ)) z = (a - (z : ℂ))⁻¹ ^ n := by
  obtain ⟨r, hr⟩ := exists_resolvent_mem_polynomialClosure hKc ha
  refine ⟨r ^ n, fun z ↦ ?_⟩
  simp [hr]

/-- A finite sum of higher-order resolvents, all of whose poles miss `K`,
belongs to the closed polynomial algebra on `K`. -/
theorem exists_resolventPowSum_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι] (a c : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a i ∉ K) :
    ∃ g : (polynomialFunctions K).topologicalClosure,
      ∀ z : K,
        (g : C(K, ℂ)) z = ∑ i, c i * (a i - (z : ℂ))⁻¹ ^ n i := by
  classical
  choose r hr using fun i ↦
    exists_resolventPow_mem_polynomialClosure hKc (ha i) (n i)
  refine ⟨∑ i, c i • r i, fun z ↦ ?_⟩
  simp [hr]

/-- The rational expression formed from the zeroth and first moments of
finitely many localized densities belongs to the polynomial closure. -/
theorem exists_firstMomentRational_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι] (a m₀ m₁ : ι → ℂ)
    (ha : ∀ i, a i ∉ K) :
    ∃ g : (polynomialFunctions K).topologicalClosure,
      ∀ z : K,
        (g : C(K, ℂ)) z =
          ∑ i, ((a i - (z : ℂ))⁻¹ * m₀ i -
            (a i - (z : ℂ))⁻¹ ^ 2 * m₁ i) := by
  classical
  choose r₁ hr₁ using fun i ↦
    exists_resolventPow_mem_polynomialClosure hKc (ha i) 1
  choose r₂ hr₂ using fun i ↦
    exists_resolventPow_mem_polynomialClosure hKc (ha i) 2
  refine ⟨∑ i, (m₀ i • r₁ i - m₁ i • r₂ i), fun z ↦ ?_⟩
  simp [hr₁, hr₂, mul_comm]

/-- The second-order Laurent expansion of the Cauchy kernel around `a`.
The displayed final term is the exact remainder. -/
theorem cauchyKernel_secondOrder_expansion
    {w a z : ℂ} (haz : a ≠ z) (hwz : w ≠ z) :
    (w - z)⁻¹ =
      (a - z)⁻¹ - (w - a) * (a - z)⁻¹ ^ 2 +
        (w - a) ^ 2 * ((a - z)⁻¹ ^ 2 * (w - z)⁻¹) := by
  field_simp [sub_ne_zero.mpr haz, sub_ne_zero.mpr hwz]
  ring

/-- Norm of the exact second-order Cauchy-kernel remainder. -/
theorem norm_cauchyKernel_secondOrder_remainder
    (w a z : ℂ) :
    ‖(w - a) ^ 2 * ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)‖ =
      ‖w - a‖ ^ 2 * (‖a - z‖⁻¹ ^ 2 * ‖w - z‖⁻¹) := by
  simp only [norm_mul, norm_pow, norm_inv]

/-- A convenient upper bound for the exact second-order remainder. -/
theorem norm_cauchyKernel_secondOrder_remainder_le
    {w a z  : ℂ} {ρ d : ℝ}
    (hwa : ‖w - a‖ ≤ ρ) (haz : d ≤ ‖a - z‖)
    (hwz : d ≤ ‖w - z‖) (hd : 0 < d) :
    ‖(w - a) ^ 2 * ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)‖ ≤
      ρ ^ 2 * d⁻¹ ^ 3 := by
  rw [norm_cauchyKernel_secondOrder_remainder]
  have hρ : 0 ≤ ρ := (norm_nonneg _).trans hwa
  have haz' : ‖a - z‖⁻¹ ≤ d⁻¹ :=
    (inv_le_inv₀ (lt_of_lt_of_le hd haz) hd).2 haz
  have hwz' : ‖w - z‖⁻¹ ≤ d⁻¹ :=
    (inv_le_inv₀ (lt_of_lt_of_le hd hwz) hd).2 hwz
  calc
    ‖w - a‖ ^ 2 * (‖a - z‖⁻¹ ^ 2 * ‖w - z‖⁻¹)
        ≤ ρ ^ 2 * (d⁻¹ ^ 2 * d⁻¹) := by
          gcongr
    _ = ρ ^ 2 * d⁻¹ ^ 3 := by ring

/-- The pointwise second-order estimate integrates to a bound by the
`L¹`-mass of the localized density.  This is the form used when summing the
localized frontier pieces. -/
theorem norm_setIntegral_cauchyKernel_secondOrder_remainder_le
    (E : Set ℂ) (hE : MeasurableSet E) (q : ℂ → ℂ)
    {a z : ℂ} {ρ d : ℝ}
    (hrem :
      MeasureTheory.IntegrableOn
        (fun w ↦
          ((w - a) ^ 2 *
            ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w) E)
    (hqnorm :
      MeasureTheory.IntegrableOn (fun w ↦ ‖q w‖) E)
    (hwa : ∀ w ∈ E, ‖w - a‖ ≤ ρ)
    (haz : d ≤ ‖a - z‖)
    (hwz : ∀ w ∈ E, d ≤ ‖w - z‖)
    (hd : 0 < d) :
    ‖∫ w : ℂ in E,
        ((w - a) ^ 2 *
          ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w‖ ≤
      (ρ ^ 2 * d⁻¹ ^ 3) * ∫ w : ℂ in E, ‖q w‖ := by
  calc
    ‖∫ w : ℂ in E,
        ((w - a) ^ 2 *
          ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w‖
        ≤ ∫ w : ℂ in E,
            ‖((w - a) ^ 2 *
              ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w‖ :=
      MeasureTheory.norm_integral_le_integral_norm _
    _ ≤ ∫ w : ℂ in E, (ρ ^ 2 * d⁻¹ ^ 3) * ‖q w‖ := by
      apply MeasureTheory.setIntegral_mono_on
        hrem.norm (hqnorm.const_mul _) hE
      intro w hw
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_cauchyKernel_secondOrder_remainder_le
          (hwa w hw) haz (hwz w hw) hd)
        (norm_nonneg _)
    _ = (ρ ^ 2 * d⁻¹ ^ 3) * ∫ w : ℂ in E, ‖q w‖ := by
      rw [MeasureTheory.integral_const_mul]

/-- Integrating the exact kernel expansion expresses a localized Cauchy
transform through its first two moments and an exact second-order remainder. -/
theorem setIntegral_cauchyKernel_eq_moments_add_remainder
    (E : Set ℂ) (q : ℂ → ℂ) {a z : ℂ} (haz : a ≠ z)
    (hq : MeasureTheory.IntegrableOn q E)
    (hq₁ :
      MeasureTheory.IntegrableOn (fun w ↦ (w - a) * q w) E)
    (hrem :
      MeasureTheory.IntegrableOn
        (fun w ↦
          ((w - a) ^ 2 *
            ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w) E) :
    (∫ w : ℂ in E, (w - z)⁻¹ * q w) =
      (a - z)⁻¹ * (∫ w : ℂ in E, q w) -
        (a - z)⁻¹ ^ 2 *
          (∫ w : ℂ in E, (w - a) * q w) +
        ∫ w : ℂ in E,
          ((w - a) ^ 2 *
            ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w := by
  let A₀ : ℂ → ℂ := fun w ↦ (a - z)⁻¹ * q w
  let A₁ : ℂ → ℂ :=
    fun w ↦ (a - z)⁻¹ ^ 2 * ((w - a) * q w)
  let R : ℂ → ℂ :=
    fun w ↦
      ((w - a) ^ 2 *
        ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w
  have hA₀ : MeasureTheory.IntegrableOn A₀ E :=
    hq.const_mul _
  have hA₁ : MeasureTheory.IntegrableOn A₁ E :=
    hq₁.const_mul _
  change MeasureTheory.IntegrableOn R E at hrem
  have hne :
      ∀ᵐ w : ℂ ∂MeasureTheory.volume.restrict E, w ≠ z :=
    MeasureTheory.ae_mono MeasureTheory.Measure.restrict_le_self
      (MeasureTheory.volume.ae_ne z)
  change
    (∫ w : ℂ in E, (w - z)⁻¹ * q w) =
      (a - z)⁻¹ * (∫ w : ℂ in E, q w) -
        (a - z)⁻¹ ^ 2 *
          (∫ w : ℂ in E, (w - a) * q w) +
        ∫ w : ℂ in E, R w
  calc
    (∫ w : ℂ in E, (w - z)⁻¹ * q w) =
        ∫ w : ℂ in E, A₀ w - A₁ w + R w := by
          apply MeasureTheory.integral_congr_ae
          filter_upwards [hne] with w hwz
          rw [cauchyKernel_secondOrder_expansion haz hwz]
          simp only [A₀, A₁, R]
          ring
    _ = (∫ w : ℂ in E, A₀ w) -
          (∫ w : ℂ in E, A₁ w) +
          ∫ w : ℂ in E, R w := by
        have hadd :
            (∫ w : ℂ in E, (A₀ w - A₁ w) + R w) =
              (∫ w : ℂ in E, A₀ w - A₁ w) +
                ∫ w : ℂ in E, R w :=
          MeasureTheory.integral_add (hA₀.sub hA₁) hrem
        have hsub :
            (∫ w : ℂ in E, A₀ w - A₁ w) =
              (∫ w : ℂ in E, A₀ w) -
                ∫ w : ℂ in E, A₁ w :=
          MeasureTheory.integral_sub hA₀ hA₁
        rw [hadd, hsub]
    _ = _ := by
      simp only [A₀, A₁, MeasureTheory.integral_const_mul]

/-- The zeroth/first-moment rational expression approximates a localized
Cauchy transform, with the exact `L¹` remainder bound needed for the finite
frontier sum. -/
theorem norm_setIntegral_cauchyKernel_sub_moments_le
    (E : Set ℂ) (hE : MeasurableSet E) (q : ℂ → ℂ)
    {a z : ℂ} {ρ d : ℝ} (hazne : a ≠ z)
    (hq : MeasureTheory.IntegrableOn q E)
    (hq₁ :
      MeasureTheory.IntegrableOn (fun w ↦ (w - a) * q w) E)
    (hrem :
      MeasureTheory.IntegrableOn
        (fun w ↦
          ((w - a) ^ 2 *
            ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w) E)
    (hqnorm :
      MeasureTheory.IntegrableOn (fun w ↦ ‖q w‖) E)
    (hwa : ∀ w ∈ E, ‖w - a‖ ≤ ρ)
    (haz : d ≤ ‖a - z‖)
    (hwz : ∀ w ∈ E, d ≤ ‖w - z‖)
    (hd : 0 < d) :
    ‖(∫ w : ℂ in E, (w - z)⁻¹ * q w) -
        ((a - z)⁻¹ * (∫ w : ℂ in E, q w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ in E, (w - a) * q w))‖ ≤
      (ρ ^ 2 * d⁻¹ ^ 3) * ∫ w : ℂ in E, ‖q w‖ := by
  rw [setIntegral_cauchyKernel_eq_moments_add_remainder
    E q hazne hq hq₁ hrem]
  have hcancel :
      ((a - z)⁻¹ * (∫ w : ℂ in E, q w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ in E, (w - a) * q w) +
          ∫ w : ℂ in E,
            ((w - a) ^ 2 *
              ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w) -
        ((a - z)⁻¹ * (∫ w : ℂ in E, q w) -
          (a - z)⁻¹ ^ 2 *
            (∫ w : ℂ in E, (w - a) * q w)) =
        ∫ w : ℂ in E,
          ((w - a) ^ 2 *
            ((a - z)⁻¹ ^ 2 * (w - z)⁻¹)) * q w := by
    ring
  rw [hcancel]
  exact norm_setIntegral_cauchyKernel_secondOrder_remainder_le
    E hE q hrem hqnorm hwa haz hwz hd

end Submission.Helpers
