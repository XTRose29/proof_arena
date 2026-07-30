import Submission.RuelleGridEntropy
import Submission.PlaneSingularConvergence
import Submission.JacobianCocycle

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open scoped Real

noncomputable def derivativeExpansion
    (S S_inv : EucPlane → EucPlane) (x : EucPlane) : ℝ :=
  Real.posLog ‖fderiv ℝ S x‖ +
    Real.posLog (1 / ‖fderiv ℝ S_inv (S x)‖)

lemma fderiv_isInvertible
    (S S_inv : EucPlane → EucPlane)
    (hS_smooth : ContDiff ℝ 2 S)
    (hS_inv_smooth : ContDiff ℝ 2 S_inv)
    (hS_left : Function.LeftInverse S_inv S)
    (hS_right : Function.RightInverse S_inv S)
    (x : EucPlane) :
    (fderiv ℝ S x).IsInvertible := by
  have hright :
      fderiv ℝ S x ∘L (fderiv ℝ S x).inverse =
        ContinuousLinearMap.id ℝ EucPlane := by
    simpa [Function.iterate_one] using
      (fderiv_iterate_comp_inverse S S_inv hS_smooth hS_inv_smooth
        hS_left hS_right 1 x)
  have hleft :
      (fderiv ℝ S x).inverse ∘L fderiv ℝ S x =
        ContinuousLinearMap.id ℝ EucPlane := by
    simpa [Function.iterate_one] using
      (fderiv_iterate_inverse_comp S S_inv hS_smooth hS_inv_smooth
        hS_left hS_right 1 x)
  exact ContinuousLinearMap.IsInvertible.of_inverse hright hleft

lemma singularImageSize_zero_eq_norm
    (A : EucPlane →L[ℝ] EucPlane) :
    singularImageSize A 0 = ‖A‖ := by
  apply sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)|>.mp
  exact (norm_apply_planeSingularBasis_sq A 0).trans
    (planeSingularValueSq_zero_eq_norm_sq A)

lemma singularImageSize_one_fderiv_eq
    (S S_inv : EucPlane → EucPlane)
    (hS_smooth : ContDiff ℝ 2 S)
    (hS_inv_smooth : ContDiff ℝ 2 S_inv)
    (hS_left : Function.LeftInverse S_inv S)
    (hS_right : Function.RightInverse S_inv S)
    (x : EucPlane) :
    singularImageSize (fderiv ℝ S x) 1 =
      1 / ‖fderiv ℝ S_inv (S x)‖ := by
  have hdet :
      (fderiv ℝ S x).toLinearMap.det ≠ 0 := by
    simpa [Function.iterate_one] using
      det_fderiv_iterate_ne_zero S S_inv hS_smooth hS_inv_smooth
        hS_left hS_right 1 x
  have hleft :
      fderiv ℝ S_inv (S x) ∘L fderiv ℝ S x =
        ContinuousLinearMap.id ℝ EucPlane := by
    have h :=
      fderiv_iterate_inverse_comp S S_inv hS_smooth hS_inv_smooth
        hS_left hS_right 1 x
    rw [fderiv_iterate_inverse S S_inv hS_smooth hS_inv_smooth
      hS_left hS_right] at h
    simpa [Function.iterate_one] using h
  exact norm_minSingular_eq_one_div_norm_inverse
    (fderiv ℝ S x) (fderiv ℝ S_inv (S x)) hdet hleft

lemma log_gridTransitionCardBound_le_derivativeExpansion
    (S S_inv : EucPlane → EucPlane)
    (hS_smooth : ContDiff ℝ 2 S)
    (hS_inv_smooth : ContDiff ℝ 2 S_inv)
    (hS_left : Function.LeftInverse S_inv S)
    (hS_right : Function.RightInverse S_inv S)
    (K : Set EucPlane) (r : ℝ) (box : Finset (ℤ × ℤ))
    (y : Option ↥box) :
    Real.log (gridTransitionCardBound S K r box y) ≤
      Real.log 3969 +
        derivativeExpansion S S_inv
          (gridCellRepresentative K (squareGridObservation r box) y) := by
  classical
  let Y := squareGridObservation r box
  by_cases hy : ∃ x, x ∈ K ∧ Y x = y
  · let x := gridCellRepresentative K Y y
    have hlog := log_singularTargetCardBound_le
      (S x) (fderiv ℝ S x) r
    rw [singularImageSize_zero_eq_norm,
      singularImageSize_one_fderiv_eq S S_inv hS_smooth hS_inv_smooth
        hS_left hS_right] at hlog
    simpa [gridTransitionCardBound, derivativeExpansion, Y, x, hy, add_assoc]
      using hlog
  · simp only [gridTransitionCardBound, derivativeExpansion, Y, dif_neg hy,
      Nat.cast_one, Real.log_one]
    exact add_nonneg (Real.log_nonneg (by norm_num))
      (add_nonneg Real.posLog_nonneg Real.posLog_nonneg)

lemma continuous_derivativeExpansion
    (S S_inv : EucPlane → EucPlane)
    (hS_smooth : ContDiff ℝ 2 S)
    (hS_inv_smooth : ContDiff ℝ 2 S_inv)
    (hS_left : Function.LeftInverse S_inv S)
    (hS_right : Function.RightInverse S_inv S) :
    Continuous (derivativeExpansion S S_inv) := by
  have hA : Continuous fun x => ‖fderiv ℝ S x‖ :=
    (hS_smooth.continuous_fderiv (by norm_num)).norm
  have hD : Continuous fun x => ‖fderiv ℝ S_inv (S x)‖ :=
    ((hS_inv_smooth.continuous_fderiv (by norm_num)).comp
      hS_smooth.continuous).norm
  have hDne : ∀ x, ‖fderiv ℝ S_inv (S x)‖ ≠ 0 := by
    intro x hzero
    have hdet :=
      det_fderiv_iterate_ne_zero S_inv S hS_inv_smooth hS_smooth
        hS_right hS_left 1 (S x)
    have hmap : fderiv ℝ S_inv (S x) = 0 := norm_eq_zero.mp hzero
    simp [hmap] at hdet
  have hDinv : Continuous fun x => 1 / ‖fderiv ℝ S_inv (S x)‖ := by
    simpa only [one_div] using hD.inv₀ hDne
  exact (Real.continuous_posLog.comp hA).add
    (Real.continuous_posLog.comp hDinv)

lemma integrable_derivativeExpansion_of_compact_support
    (S S_inv : EucPlane → EucPlane)
    (hS_smooth : ContDiff ℝ 2 S)
    (hS_inv_smooth : ContDiff ℝ 2 S_inv)
    (hS_left : Function.LeftInverse S_inv S)
    (hS_right : Function.RightInverse S_inv S)
    (K : Set EucPlane) (hK_compact : IsCompact K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmuK : mu Kᶜ = 0) :
    Integrable (derivativeExpansion S S_inv) mu := by
  let F := derivativeExpansion S S_inv
  have hOn : IntegrableOn F K mu :=
    (continuous_derivativeExpansion S S_inv hS_smooth hS_inv_smooth
      hS_left hS_right).continuousOn.integrableOn_compact hK_compact
  have hIndicator : Integrable (K.indicator F) mu :=
    hOn.integrable_indicator hK_compact.isClosed.measurableSet
  apply hIndicator.congr
  filter_upwards [mem_ae_iff.mpr hmuK] with x hx
  rw [Set.indicator_of_mem hx]

lemma weighted_gridCellRepresentative_le_integral_add
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (K : Set EucPlane) (hmuK : mu Kᶜ = 0)
    {J : Type*} [Fintype J] [MeasurableSpace J]
    [MeasurableSingletonClass J]
    (Y : EucPlane → J) (hY : Measurable Y)
    (F : EucPlane → ℝ) (hF : Integrable F mu)
    {epsilon : ℝ}
    (hosc : ∀ x ∈ K, ∀ z ∈ K, Y x = Y z →
      F x ≤ F z + epsilon) :
    (∑ y : J, mu.real (Y ⁻¹' {y}) *
      F (gridCellRepresentative K Y y)) ≤
        (∫ z, F z ∂mu) + epsilon := by
  classical
  let G : EucPlane → ℝ :=
    fun z => F (gridCellRepresentative K Y (Y z))
  have hGsum :
      G = fun z => ∑ y : J,
        (Y ⁻¹' {y}).indicator
          (fun _ => F (gridCellRepresentative K Y y)) z := by
    funext z
    rw [Finset.sum_eq_single (Y z)]
    · rw [Set.indicator_of_mem]
      exact Set.mem_preimage.mpr rfl
    · intro y _hy hyz
      rw [Set.indicator_of_notMem]
      simpa only [Set.mem_preimage, Set.mem_singleton_iff] using Ne.symm hyz
    · simp
  have hG : Integrable G mu := by
    rw [hGsum]
    apply integrable_finsetSum
    intro y _hy
    exact (integrable_const _).indicator (hY (measurableSet_singleton y))
  have hweighted :
      (∑ y : J, mu.real (Y ⁻¹' {y}) *
        F (gridCellRepresentative K Y y)) = ∫ z, G z ∂mu := by
    rw [hGsum, integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro y _hy
      rw [integral_indicator_const _
        (hY (measurableSet_singleton y)), smul_eq_mul]
    · intro y _hy
      exact (integrable_const _).indicator (hY (measurableSet_singleton y))
  rw [hweighted]
  calc
    (∫ z, G z ∂mu) ≤ ∫ z, F z + epsilon ∂mu := by
      apply integral_mono_ae hG (hF.add (integrable_const epsilon))
      filter_upwards [mem_ae_iff.mpr hmuK] with z hzK
      have hy : ∃ x, x ∈ K ∧ Y x = Y z := ⟨z, hzK, rfl⟩
      exact hosc (gridCellRepresentative K Y (Y z))
        (gridCellRepresentative_mem K Y (Y z) hy) z hzK
        (gridCellRepresentative_observation K Y (Y z) hy)
    _ = (∫ z, F z ∂mu) + epsilon := by
      rw [integral_add hF (integrable_const epsilon), integral_const]
      simp

lemma conditionalObservationEntropy_squareGrid_le_integral_expansion
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (S S_inv : EucPlane → EucPlane)
    (hS_smooth : ContDiff ℝ 2 S)
    (hS_inv_smooth : ContDiff ℝ 2 S_inv)
    (hS_left : Function.LeftInverse S_inv S)
    (hS_right : Function.RightInverse S_inv S)
    (K : Set EucPlane) (hK_compact : IsCompact K)
    (hmuK : mu Kᶜ = 0) (hSK : S '' K = K)
    (C : Set EucPlane) (hC_convex : Convex ℝ C) (hKC : K ⊆ C)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ z ∈ C, ∀ w ∈ C,
      ‖fderiv ℝ S z - fderiv ℝ S w‖ ≤ B * dist z w)
    {r : ℝ} (hr : 0 < r) (hsmall : 4 * B * r ≤ 1)
    (box : Finset (ℤ × ℤ))
    (hKbox : ∀ x ∈ K, squareGridIndex r x ∈ box)
    {epsilon : ℝ}
    (hosc : ∀ x ∈ K, ∀ z ∈ K,
      squareGridObservation r box x = squareGridObservation r box z →
      derivativeExpansion S S_inv x ≤
        derivativeExpansion S S_inv z + epsilon) :
    conditionalObservationEntropy mu
        (fun x => squareGridObservation r box (S x))
        (squareGridObservation r box) ≤
      Real.log 3969 +
        (∫ x, derivativeExpansion S S_inv x ∂mu) + epsilon := by
  let Y := squareGridObservation r box
  let F := derivativeExpansion S S_inv
  have hweightedLog :=
    conditionalObservationEntropy_squareGrid_le_weighted_log
      mu S hS_smooth.continuous.measurable hS_smooth K hmuK hSK C hC_convex hKC
        hB_nonneg hB hr hsmall box hKbox
        (fderiv_isInvertible S S_inv hS_smooth hS_inv_smooth
          hS_left hS_right)
  have hrow :
      ∑ y : Option ↥box, mu.real (Y ⁻¹' {y}) = 1 := by
    simpa [Y] using sum_measureReal_inter_fibers mu Y
      (measurable_squareGridObservation r box) MeasurableSet.univ Set.univ
  have hlogs :
      (∑ y : Option ↥box, mu.real (Y ⁻¹' {y}) *
        Real.log (gridTransitionCardBound S K r box y)) ≤
      ∑ y : Option ↥box, mu.real (Y ⁻¹' {y}) *
        (Real.log 3969 + F (gridCellRepresentative K Y y)) := by
    apply Finset.sum_le_sum
    intro y _hy
    exact mul_le_mul_of_nonneg_left
      (log_gridTransitionCardBound_le_derivativeExpansion
        S S_inv hS_smooth hS_inv_smooth hS_left hS_right K r box y)
      measureReal_nonneg
  have hrep :=
    weighted_gridCellRepresentative_le_integral_add
      mu K hmuK Y (measurable_squareGridObservation r box) F
      (integrable_derivativeExpansion_of_compact_support
        S S_inv hS_smooth hS_inv_smooth hS_left hS_right
          K hK_compact mu hmuK) hosc
  calc
    conditionalObservationEntropy mu
        (fun x => squareGridObservation r box (S x))
        (squareGridObservation r box) ≤
        ∑ y : Option ↥box, mu.real (Y ⁻¹' {y}) *
          Real.log (gridTransitionCardBound S K r box y) := hweightedLog
    _ ≤ ∑ y : Option ↥box, mu.real (Y ⁻¹' {y}) *
        (Real.log 3969 + F (gridCellRepresentative K Y y)) := hlogs
    _ = Real.log 3969 +
        ∑ y : Option ↥box, mu.real (Y ⁻¹' {y}) *
          F (gridCellRepresentative K Y y) := by
      simp_rw [mul_add]
      rw [Finset.sum_add_distrib, ← Finset.sum_mul, hrow, one_mul]
    _ ≤ Real.log 3969 + ((∫ x, F x ∂mu) + epsilon) := by
      gcongr
    _ = Real.log 3969 + (∫ x, derivativeExpansion S S_inv x ∂mu) +
        epsilon := by
      simp [F]
      ring

end Submission.Helpers
