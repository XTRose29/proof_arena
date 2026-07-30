import ChallengeDeps
import Submission.BoundarySlice
import Submission.SharpSobolev

open LeanEval.Geometry
open MeasureTheory ENNReal Metric Set Function Filter
open scoped Convolution RealInnerProductSpace Topology

namespace Submission.MollifiedBoundary

noncomputable section

/-- The real-valued indicator used as the nonsmooth factor in the convolution. -/
def indicatorOne {n : ℕ} (A : Set (E n)) : E n → ℝ :=
  A.indicator fun _ ↦ 1

/-- Mollification of a bounded set by the normalized radial kernel. -/
def mollification {n : ℕ} (A : Set (E n)) (a b : ℝ) : E n → ℝ :=
  indicatorOne A ⋆ RadialMollifier.kernel a b

private theorem integrable_indicatorOne {n : ℕ} {A : Set (E n)}
    (hA : MeasurableSet A) (hAbdd : Bornology.IsBounded A) :
    Integrable (indicatorOne A) := by
  rw [indicatorOne, integrable_indicator_iff hA]
  exact integrableOn_const hAbdd.measure_lt_top.ne

private theorem hasCompactSupport_indicatorOne {n : ℕ} {A : Set (E n)}
    (hAbdd : Bornology.IsBounded A) : HasCompactSupport (indicatorOne A) := by
  apply HasCompactSupport.intro hAbdd.isCompact_closure
  intro x hx
  apply indicator_of_notMem
  exact fun hxA ↦ hx (subset_closure hxA)

theorem contDiff_mollification {n : ℕ} {A : Set (E n)}
    (hA : MeasurableSet A) (hAbdd : Bornology.IsBounded A)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    ContDiff ℝ 1 (mollification A a b) := by
  exact (RadialMollifier.hasCompactSupport_kernel ha hab).contDiff_convolution_right
    (ContinuousLinearMap.lsmul ℝ ℝ) (integrable_indicatorOne hA hAbdd).locallyIntegrable
    (RadialMollifier.contDiff_kernel ha hab)

theorem hasCompactSupport_mollification {n : ℕ} {A : Set (E n)}
    (hAbdd : Bornology.IsBounded A) {a b : ℝ} (ha : 0 < a) (hab : a < b) :
    HasCompactSupport (mollification A a b) := by
  exact (hasCompactSupport_indicatorOne hAbdd).convolution
    (ContinuousLinearMap.lsmul ℝ ℝ)
    (RadialMollifier.hasCompactSupport_kernel ha hab)

theorem mollification_eq_one_of_thickening_subset {n : ℕ} {A K : Set (E n)}
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hKA : thickening b K ⊆ A) {x : E n} (hx : x ∈ K) :
    mollification A a b x = 1 := by
  rw [mollification, convolution_lsmul_swap]
  convert RadialMollifier.integral_kernel (n := n) ha hab using 1
  apply integral_congr_ae
  filter_upwards with y
  by_cases hy : y ∈ ball (0 : E n) b
  · have hxy : x - y ∈ A := by
      apply hKA
      apply mem_thickening_iff.mpr
      refine ⟨x, hx, ?_⟩
      simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_sub_cancel_left,
        norm_neg, sub_zero] using hy
    simp [indicatorOne, indicator_of_mem hxy]
  · rw [RadialMollifier.kernel_zero_of_mem_compl_ball ha hab hy]
    simp

private theorem integrable_fderiv_kernel {n : ℕ} {a b : ℝ}
    (ha : 0 < a) (hab : a < b) :
    Integrable (fderiv ℝ (RadialMollifier.kernel (n := n) a b)) := by
  exact (RadialMollifier.contDiff_kernel ha hab).continuous_fderiv one_ne_zero
    |>.integrable_of_hasCompactSupport
      ((RadialMollifier.hasCompactSupport_kernel ha hab).fderiv ℝ)

private theorem integrable_derivative_integrand {n : ℕ} {A : Set (E n)}
    (hA : MeasurableSet A) {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : E n) :
    Integrable (fun y ↦ indicatorOne A (x - y) •
      fderiv ℝ (RadialMollifier.kernel a b) y) := by
  have hmeas : AEStronglyMeasurable (fun y ↦ indicatorOne A (x - y)) :=
    ((Measurable.indicator measurable_const hA).comp (by fun_prop)).aestronglyMeasurable
  have hbound : ∀ᵐ y, ‖indicatorOne A (x - y)‖ ≤ (1 : ℝ) := by
    filter_upwards with y
    by_cases hy : x - y ∈ A <;>
      simp [indicatorOne, indicator_of_mem, indicator_of_notMem, hy]
  exact (integrable_fderiv_kernel ha hab).bdd_smul 1 hmeas hbound

theorem fderiv_mollification_apply {n : ℕ} {A : Set (E n)}
    (hA : MeasurableSet A) (hAbdd : Bornology.IsBounded A)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x u : E n) :
    fderiv ℝ (mollification A a b) x u =
      ∫ y, indicatorOne A (x - y) *
        fderiv ℝ (RadialMollifier.kernel a b) y u := by
  have hd : HasFDerivAt (mollification A a b)
      ((indicatorOne A ⋆[
        (ContinuousLinearMap.lsmul ℝ ℝ).precompR (E n)]
          fderiv ℝ (RadialMollifier.kernel a b)) x) x := by
    exact (RadialMollifier.hasCompactSupport_kernel ha hab).hasFDerivAt_convolution_right
      (ContinuousLinearMap.lsmul ℝ ℝ)
      (integrable_indicatorOne hA hAbdd).locallyIntegrable
      (RadialMollifier.contDiff_kernel ha hab) x
  have hint : Integrable (fun y ↦
      ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (E n))
        (indicatorOne A (x - y))
        (fderiv ℝ (RadialMollifier.kernel a b) y)) := by
    change Integrable (fun y ↦ indicatorOne A (x - y) •
      fderiv ℝ (RadialMollifier.kernel a b) y)
    exact integrable_derivative_integrand hA ha hab x
  calc
    fderiv ℝ (mollification A a b) x u =
        ((indicatorOne A ⋆[
          (ContinuousLinearMap.lsmul ℝ ℝ).precompR (E n)]
            fderiv ℝ (RadialMollifier.kernel a b)) x) u := by rw [hd.fderiv]
    _ = (∫ y, ((ContinuousLinearMap.lsmul ℝ ℝ).precompR (E n))
        (indicatorOne A (x - y))
        (fderiv ℝ (RadialMollifier.kernel a b) y)) u := by
      rw [convolution_eq_swap]
    _ = ∫ y, (((ContinuousLinearMap.lsmul ℝ ℝ).precompR (E n))
        (indicatorOne A (x - y))
        (fderiv ℝ (RadialMollifier.kernel a b) y)) u :=
      ContinuousLinearMap.integral_apply hint u
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with y
      rfl

private theorem fderiv_kernel_apply_eq_line_deriv {n : ℕ} (hn : 1 ≤ n)
    {u : E n} (hu : ‖u‖ = 1) {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (z : E (n - 1)) (t : ℝ) :
    fderiv ℝ (RadialMollifier.kernel a b)
        (Hyperplane.parametrization hn u hu (z, t)) u =
      deriv (fun s : ℝ ↦ RadialMollifier.kernel a b
        (Hyperplane.parametrization hn u hu (z, s))) t := by
  simp_rw [Hyperplane.parametrization_apply]
  have hparam := (hasDerivAt_const (x := t)
    ((Hyperplane.perpBasis hn u hu).repr.symm z : E n)).add
      ((hasDerivAt_id t).smul_const u)
  have hcomp := ((RadialMollifier.contDiff_kernel ha hab).differentiable one_ne_zero _)
    |>.hasFDerivAt.comp_hasDerivAt t hparam
  have hfun :
      RadialMollifier.kernel a b ∘
          ((fun _ : ℝ ↦ ((Hyperplane.perpBasis hn u hu).repr.symm z : E n)) +
            fun s : ℝ ↦ s • u) =
        fun s : ℝ ↦ RadialMollifier.kernel a b
          (((Hyperplane.perpBasis hn u hu).repr.symm z : E n) + s • u) := by
    funext s
    rfl
  have hbase :
      fderiv ℝ (RadialMollifier.kernel a b)
          (((Hyperplane.perpBasis hn u hu).repr.symm z : E n) + t • u) u =
        deriv (RadialMollifier.kernel a b ∘
          ((fun _ : ℝ ↦ ((Hyperplane.perpBasis hn u hu).repr.symm z : E n)) +
            fun s : ℝ ↦ s • u)) t := by
    simpa only [Pi.add_apply, id_eq, zero_add, one_smul] using hcomp.deriv.symm
  exact hbase.trans (congrArg (fun f : ℝ → ℝ ↦ deriv f t) hfun)

theorem fderiv_mollification_apply_eq_integral_slices {n : ℕ} (hn : 2 ≤ n)
    {A : Set (E n)} (hA : IsOpen A) (hAbdd : Bornology.IsBounded A)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : E n)
    {u : E n} (hu : ‖u‖ = 1) :
    fderiv ℝ (mollification A a b) x u =
      ∫ z : E (n - 1), ∫ t in BoundarySlice.slice (by omega) u hu A x z,
        deriv (fun s : ℝ ↦ RadialMollifier.kernel a b
          (Hyperplane.parametrization (by omega) u hu (z, s))) t := by
  let g : E n → ℝ := fun y ↦ indicatorOne A (x - y) *
    fderiv ℝ (RadialMollifier.kernel a b) y u
  have hg : Integrable g := by
    have hi := (integrable_derivative_integrand hA.measurableSet ha hab x)
      |>.apply_continuousLinearMap u
    simpa only [g, smul_apply, smul_eq_mul] using hi
  have hgprod : Integrable (g ∘ Hyperplane.parametrization (by omega) u hu) :=
    (Hyperplane.measurePreserving_parametrization (by omega) u hu)
      |>.integrable_comp_of_integrable hg
  calc
    fderiv ℝ (mollification A a b) x u = ∫ y, g y := by
      exact fderiv_mollification_apply hA.measurableSet hAbdd ha hab x u
    _ = ∫ q : E (n - 1) × ℝ,
        g (Hyperplane.parametrization (by omega) u hu q) :=
      ((Hyperplane.measurePreserving_parametrization (by omega) u hu)
        |>.integral_comp' g).symm
    _ = ∫ z : E (n - 1), ∫ t : ℝ,
        g (Hyperplane.parametrization (by omega) u hu (z, t)) := by
      rw [Measure.volume_eq_prod]
      simpa only [Function.comp_apply] using integral_prod _ hgprod
    _ = _ := by
      apply integral_congr_ae
      filter_upwards with z
      have hslice : MeasurableSet (BoundarySlice.slice (by omega) u hu A x z) := by
        apply hA.measurableSet.preimage
        simp_rw [Hyperplane.parametrization_apply]
        fun_prop
      rw [← integral_indicator hslice]
      apply integral_congr_ae
      filter_upwards with t
      by_cases ht : t ∈ BoundarySlice.slice (by omega) u hu A x z
      · have hAt : x - Hyperplane.parametrization (by omega) u hu (z, t) ∈ A := ht
        rw [indicator_of_mem ht]
        dsimp only [g, indicatorOne]
        rw [indicator_of_mem hAt, one_mul,
          fderiv_kernel_apply_eq_line_deriv (by omega) hu ha hab]
      · have hAt : x - Hyperplane.parametrization (by omega) u hu (z, t) ∉ A := ht
        rw [indicator_of_notMem ht]
        dsimp only [g, indicatorOne]
        rw [indicator_of_notMem hAt, zero_mul]

theorem enorm_fderiv_mollification_apply_le {n : ℕ} (hn : 2 ≤ n)
    {A : Set (E n)} (hA : IsOpen A) (hAbdd : Bornology.IsBounded A)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : E n)
    {u : E n} (hu : ‖u‖ = 1) :
    ‖fderiv ℝ (mollification A a b) x u‖ₑ ≤
      ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹ *
        μHE[n - 1] (BoundarySlice.localBoundary A x b) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹
  calc
    ‖fderiv ℝ (mollification A a b) x u‖ₑ =
        ‖∫ z : E (n - 1), ∫ t in BoundarySlice.slice (by omega) u hu A x z,
          deriv (fun s : ℝ ↦ RadialMollifier.kernel a b
            (Hyperplane.parametrization (by omega) u hu (z, s))) t‖ₑ :=
      congrArg (fun r : ℝ ↦ ‖r‖ₑ)
        (fderiv_mollification_apply_eq_integral_slices hn hA hAbdd ha hab x hu)
    _ ≤ ∫⁻ z : E (n - 1),
        ‖∫ t in BoundarySlice.slice (by omega) u hu A x z,
          deriv (fun s : ℝ ↦ RadialMollifier.kernel a b
            (Hyperplane.parametrization (by omega) u hu (z, s))) t‖ₑ :=
      enorm_integral_le_lintegral_enorm _
    _ ≤ ∫⁻ z : E (n - 1), C *
        μH[0] (BoundarySlice.localBoundary A x b ∩
          Hyperplane.projection (by omega) u hu ⁻¹' {z}) := by
      apply lintegral_mono
      intro z
      exact BoundarySlice.enorm_integral_slice_deriv_le hn hu ha hab hA x z
    _ = C * ∫⁻ z : E (n - 1),
        μH[0] (BoundarySlice.localBoundary A x b ∩
          Hyperplane.projection (by omega) u hu ⁻¹' {z}) := by
      rw [lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
    _ ≤ C * μHE[n - 1] (BoundarySlice.localBoundary A x b) := by
      gcongr
      exact Eilenberg.lintegral_hausdorffMeasure_zero_fiber_le (by omega)
        (BoundarySlice.localBoundary A x b)
        (Hyperplane.projection (by omega) u hu)
        (Hyperplane.projection_lipschitzWith (by omega) u hu)

private theorem exists_unit_enorm_apply_eq_enorm {n : ℕ}
    (l : E n →L[ℝ] ℝ) (hl : l ≠ 0) :
    ∃ u : E n, ‖u‖ = 1 ∧ ‖l u‖ₑ = ‖l‖ₑ := by
  let v : E n := (InnerProductSpace.toDual ℝ (E n)).symm l
  have hv : v ≠ 0 := by
    intro hv
    apply hl
    apply (InnerProductSpace.toDual ℝ (E n)).symm.injective
    simpa only [map_zero, v] using hv
  have hvnorm : ‖v‖ = ‖l‖ :=
    (InnerProductSpace.toDual ℝ (E n)).symm.norm_map l
  let u : E n := ‖v‖⁻¹ • v
  have hu : ‖u‖ = 1 := by
    simp only [u, norm_smul, Real.norm_eq_abs, abs_inv,
      abs_of_pos (norm_pos_iff.mpr hv), inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]
  refine ⟨u, hu, ?_⟩
  have hlnorm : ‖l‖ ≠ 0 := by
    rw [← hvnorm]
    exact norm_ne_zero_iff.mpr hv
  have hlu : l u = ‖l‖ := by
    rw [← InnerProductSpace.toDual_symm_apply]
    change inner ℝ v u = ‖l‖
    dsimp only [u]
    rw [real_inner_smul_right, real_inner_self_eq_norm_sq, hvnorm]
    field_simp [hlnorm]
  rw [hlu, ← ofReal_norm, ← ofReal_norm]
  simp

theorem enorm_fderiv_mollification_le {n : ℕ} (hn : 2 ≤ n)
    {A : Set (E n)} (hA : IsOpen A) (hAbdd : Bornology.IsBounded A)
    {a b : ℝ} (ha : 0 < a) (hab : a < b) (x : E n) :
    ‖fderiv ℝ (mollification A a b) x‖ₑ ≤
      ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹ *
        μHE[n - 1] (BoundarySlice.localBoundary A x b) := by
  by_cases hd : fderiv ℝ (mollification A a b) x = 0
  · rw [hd]
    calc
      ‖(0 : E n →L[ℝ] ℝ)‖ₑ = 0 := by
        rw [← ofReal_norm, norm_zero, ENNReal.ofReal_zero]
      _ ≤ _ := zero_le
  · rcases exists_unit_enorm_apply_eq_enorm
      (fderiv ℝ (mollification A a b) x) hd with ⟨u, hu, hueq⟩
    rw [← hueq]
    exact enorm_fderiv_mollification_apply_le hn hA hAbdd ha hab x hu

private theorem isometry_const_sub {n : ℕ} (x : E n) :
    Isometry (fun y : E n ↦ x - y) := by
  apply Isometry.of_dist_eq
  intro y z
  simp only [dist_eq_norm]
  rw [show (x - y) - (x - z) = -(y - z) by abel, norm_neg]

private theorem image_frontier_inter_ball_const_sub {n : ℕ}
    (A : Set (E n)) (x : E n) (b : ℝ) :
    (fun y : E n ↦ x - y) '' (frontier A ∩ ball x b) =
      BoundarySlice.localBoundary A x b := by
  ext y
  constructor
  · rintro ⟨z, ⟨hzfrontier, hzball⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · simpa only [mem_ball, dist_zero_right, dist_eq_norm,
        sub_zero, norm_sub_rev] using hzball
    · simpa only [show x - (x - z) = z by abel] using hzfrontier
  · rintro ⟨hyball, hyfrontier⟩
    refine ⟨x - y, ⟨?_, ?_⟩, by abel_nf⟩
    · simpa only [show x - (x - y) = y by abel] using hyfrontier
    · simpa only [mem_ball, dist_zero_right, dist_eq_norm, sub_zero,
        show (x - y) - x = -y by abel, norm_neg] using hyball

theorem euclideanHausdorffMeasure_localBoundary {n d : ℕ}
    (A : Set (E n)) (x : E n) (b : ℝ) :
    μHE[d] (BoundarySlice.localBoundary A x b) =
      μHE[d] (frontier A ∩ ball x b) := by
  calc
    μHE[d] (BoundarySlice.localBoundary A x b) =
        μHE[d] ((fun y : E n ↦ x - y) '' (frontier A ∩ ball x b)) := by
      rw [image_frontier_inter_ball_const_sub]
    _ = μHE[d] (frontier A ∩ ball x b) :=
      (isometry_const_sub x).euclideanHausdorffMeasure_image _

theorem lintegral_euclideanHausdorffMeasure_localBoundary {n d : ℕ}
    (A : Set (E n)) {b : ℝ} (_hb : 0 < b)
    (hfrontier : μHE[d] (frontier A) ≠ ⊤) :
    ∫⁻ x : E n, μHE[d] (BoundarySlice.localBoundary A x b) =
      volume (ball (0 : E n) b) * μHE[d] (frontier A) := by
  let ν : Measure (E n) := (μHE[d]).restrict (frontier A)
  have hνtop : ν univ ≠ ⊤ := by simpa only [ν, Measure.restrict_apply_univ] using hfrontier
  letI : IsFiniteMeasure ν := ⟨lt_top_iff_ne_top.mpr hνtop⟩
  let S : Set (E n × E n) := {q | dist q.2 q.1 < b}
  let g : E n × E n → ℝ≥0∞ := S.indicator fun _ ↦ 1
  have hS : MeasurableSet S := by
    exact measurableSet_lt (by fun_prop) (by fun_prop)
  have hg : Measurable g := Measurable.indicator measurable_const hS
  have hg_left (x : E n) : (fun z ↦ g (x, z)) =
      (ball x b).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext z
    dsimp only [g]
    by_cases hz : (x, z) ∈ S
    · have hzball : z ∈ ball x b := by exact hz
      rw [indicator_of_mem hz, indicator_of_mem hzball]
    · have hzball : z ∉ ball x b := by exact hz
      rw [indicator_of_notMem hz, indicator_of_notMem hzball]
  have hg_right (z : E n) : (fun x ↦ g (x, z)) =
      (ball z b).indicator (fun _ ↦ (1 : ℝ≥0∞)) := by
    funext x
    dsimp only [g]
    by_cases hx : (x, z) ∈ S
    · have hxball : x ∈ ball z b := by
        change dist x z < b
        simpa only [S, mem_setOf_eq, dist_comm] using hx
      rw [indicator_of_mem hx, indicator_of_mem hxball]
    · have hxball : x ∉ ball z b := by
        intro hxball
        apply hx
        change dist z x < b
        simpa only [mem_ball, dist_comm] using hxball
      rw [indicator_of_notMem hx, indicator_of_notMem hxball]
  have hgprod : AEMeasurable (uncurry (fun x z ↦ g (x, z))) (volume.prod ν) := by
    change AEMeasurable g (volume.prod ν)
    exact hg.aemeasurable
  calc
    ∫⁻ x : E n, μHE[d] (BoundarySlice.localBoundary A x b) =
        ∫⁻ x : E n, μHE[d] (frontier A ∩ ball x b) := by
      apply lintegral_congr
      intro x
      exact euclideanHausdorffMeasure_localBoundary A x b
    _ = ∫⁻ x : E n, ν (ball x b) := by
      apply lintegral_congr
      intro x
      rw [Measure.restrict_apply measurableSet_ball]
      rw [inter_comm]
    _ = ∫⁻ x : E n, ∫⁻ z : E n, g (x, z) ∂ν := by
      apply lintegral_congr
      intro x
      rw [hg_left, lintegral_indicator measurableSet_ball]
      simp
    _ = ∫⁻ z : E n, (∫⁻ x : E n, g (x, z)) ∂ν :=
      lintegral_lintegral_swap hgprod
    _ = ∫⁻ z : E n, volume (ball z b) ∂ν := by
      apply lintegral_congr
      intro z
      rw [hg_right, lintegral_indicator measurableSet_ball]
      simp
    _ = ∫⁻ _z : E n, volume (ball (0 : E n) b) ∂ν := by
      apply lintegral_congr
      intro z
      exact Measure.addHaar_ball_center volume z b
    _ = volume (ball (0 : E n) b) * μHE[d] (frontier A) := by
      simp [ν]

theorem lintegral_enorm_fderiv_mollification_le {n : ℕ} (hn : 2 ≤ n)
    {A : Set (E n)} (hA : IsOpen A) (hAbdd : Bornology.IsBounded A)
    {a b : ℝ} (ha : 0 < a) (hab : a < b)
    (hfrontier : μHE[n - 1] (frontier A) ≠ ⊤) :
    ∫⁻ x : E n, ‖fderiv ℝ (mollification A a b) x‖ₑ ≤
      ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹ *
        volume (ball (0 : E n) b) * μHE[n - 1] (frontier A) := by
  let C : ℝ≥0∞ := ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹
  calc
    ∫⁻ x : E n, ‖fderiv ℝ (mollification A a b) x‖ₑ ≤
        ∫⁻ x : E n, C * μHE[n - 1] (BoundarySlice.localBoundary A x b) := by
      apply lintegral_mono
      intro x
      exact enorm_fderiv_mollification_le hn hA hAbdd ha hab x
    _ = C * ∫⁻ x : E n, μHE[n - 1] (BoundarySlice.localBoundary A x b) := by
      rw [lintegral_const_mul' C _ ENNReal.ofReal_ne_top]
    _ = C * (volume (ball (0 : E n) b) * μHE[n - 1] (frontier A)) := by
      rw [lintegral_euclideanHausdorffMeasure_localBoundary A (ha.trans hab) hfrontier]
    _ = C * volume (ball (0 : E n) b) * μHE[n - 1] (frontier A) := by
      rw [← mul_assoc]

private theorem compact_surface_bound_with_radii {n : ℕ} (hn : 2 ≤ n)
    {A K : Set (E n)} (hA : IsOpen A) (hAbdd : Bornology.IsBounded A)
    {b : ℝ}
    (hKA : thickening b K ⊆ A)
    (hfrontier : μHE[n - 1] (frontier A) ≠ ⊤)
    {a : ℝ} (ha : 0 < a) (hab : a < b) :
    (n : ℝ≥0∞) * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume K ^ (((n : ℝ) - 1) / n) ≤
      (volume (closedBall (0 : E n) a))⁻¹ *
        volume (ball (0 : E n) b) * μHE[n - 1] (frontier A) := by
  have hsobolev := SharpSobolev.sharp_sobolev_of_plateau hn
    (contDiff_mollification hA.measurableSet hAbdd ha hab)
    (hasCompactSupport_mollification hAbdd ha hab)
    (fun x hx ↦ mollification_eq_one_of_thickening_subset ha hab hKA hx)
  have hgradient := lintegral_enorm_fderiv_mollification_le
    hn hA hAbdd ha hab hfrontier
  have hballtop : volume (closedBall (0 : E n) a) ≠ ⊤ := measure_closedBall_lt_top.ne
  have hmass : volume (closedBall (0 : E n) a) ≤
      ENNReal.ofReal (RadialMollifier.mass n a b) := by
    rw [← ENNReal.ofReal_toReal hballtop]
    exact ENNReal.ofReal_le_ofReal (RadialMollifier.measure_closedBall_le_mass ha hab)
  have hpeak : ENNReal.ofReal (RadialMollifier.mass n a b)⁻¹ ≤
      (volume (closedBall (0 : E n) a))⁻¹ := by
    rw [ENNReal.ofReal_inv_of_pos (RadialMollifier.mass_pos ha hab)]
    exact ENNReal.inv_le_inv.mpr hmass
  exact hsobolev.trans <| hgradient.trans <| by gcongr

theorem compact_surface_bound {n : ℕ} (hn : 2 ≤ n)
    {A K : Set (E n)} (hA : IsOpen A) (hAbdd : Bornology.IsBounded A)
    (hK : IsCompact K) (hKA : K ⊆ A)
    (hfrontier : μHE[n - 1] (frontier A) ≠ ⊤) :
    (n : ℝ≥0∞) * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume K ^ (((n : ℝ) - 1) / n) ≤ μHE[n - 1] (frontier A) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  rcases hK.exists_thickening_subset_open hA hKA with ⟨b, hb, hthick⟩
  let c : ℕ → ℝ := fun k ↦ ((k + 1 : ℕ) : ℝ) / (k + 2 : ℕ)
  let a : ℕ → ℝ := fun k ↦ b * c k
  have hcpos (k : ℕ) : 0 < c k := by
    dsimp only [c]
    positivity
  have hclt (k : ℕ) : c k < 1 := by
    dsimp only [c]
    rw [div_lt_one (by positivity : (0 : ℝ) < (k + 2 : ℕ))]
    norm_num
  have hapos (k : ℕ) : 0 < a k := mul_pos hb (hcpos k)
  have halt (k : ℕ) : a k < b := by
    dsimp only [a]
    exact (mul_lt_iff_lt_one_right hb).mpr (hclt k)
  let L : ℝ≥0∞ := (n : ℝ≥0∞) *
    volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
      volume K ^ (((n : ℝ) - 1) / n)
  let s : ℝ≥0∞ := μHE[n - 1] (frontier A)
  have hradius (k : ℕ) : L ≤
      (volume (closedBall (0 : E n) (a k)))⁻¹ *
        volume (ball (0 : E n) b) * s := by
    exact compact_surface_bound_with_radii hn hA hAbdd hthick hfrontier
      (hapos k) (halt k)
  have hscaled (k : ℕ) : volume (closedBall (0 : E n) (a k)) * L ≤
      volume (ball (0 : E n) b) * s := by
    have hball0 : volume (closedBall (0 : E n) (a k)) ≠ 0 := by
      rw [Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : E n) (a k)]
      exact (measure_ball_pos volume (0 : E n) (hapos k)).ne'
    have hballtop : volume (closedBall (0 : E n) (a k)) ≠ ⊤ :=
      measure_closedBall_lt_top.ne
    calc
      volume (closedBall (0 : E n) (a k)) * L ≤
          volume (closedBall (0 : E n) (a k)) *
            ((volume (closedBall (0 : E n) (a k)))⁻¹ *
              volume (ball (0 : E n) b) * s) :=
        mul_le_mul_right (hradius k) _
      _ = (volume (closedBall (0 : E n) (a k)) *
            (volume (closedBall (0 : E n) (a k)))⁻¹) *
              volume (ball (0 : E n) b) * s := by ac_rfl
      _ = volume (ball (0 : E n) b) * s := by
        rw [ENNReal.mul_inv_cancel hball0 hballtop, one_mul]
  have hctend : Tendsto c atTop (𝓝 1) := by
    have h := (tendsto_natCast_div_add_atTop (1 : ℝ)).comp (tendsto_add_atTop_nat 1)
    convert h using 1
    funext k
    simp only [c, Function.comp_apply, Nat.cast_add, Nat.cast_one]
    ring
  have hatend : Tendsto a atTop (𝓝 b) := by
    simpa only [a, mul_one] using tendsto_const_nhds.mul hctend
  have hvaltend : Tendsto (fun k ↦ volume (closedBall (0 : E n) (a k))) atTop
      (𝓝 (volume (ball (0 : E n) b))) := by
    have heq : (fun k ↦ volume (closedBall (0 : E n) (a k))) =
        fun k ↦ ENNReal.ofReal ((a k) ^ n) * volume (ball (0 : E n) 1) := by
      funext k
      simpa only [finrank_euclideanSpace, Fintype.card_fin] using
        Measure.addHaar_closedBall volume (0 : E n) (hapos k).le
    rw [heq, ← Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : E n) b,
      Measure.addHaar_closedBall volume (0 : E n) hb.le]
    simpa only [finrank_euclideanSpace, Fintype.card_fin] using
      ENNReal.Tendsto.mul_const (ENNReal.tendsto_ofReal (hatend.pow n))
        (Or.inr (by finiteness : volume (ball (0 : E n) 1) ≠ ⊤))
  have hball0 : volume (ball (0 : E n) b) ≠ 0 :=
    (measure_ball_pos volume (0 : E n) hb).ne'
  have hballtop : volume (ball (0 : E n) b) ≠ ⊤ := measure_ball_lt_top.ne
  have hlim : Tendsto
      (fun k ↦ volume (closedBall (0 : E n) (a k)) * L) atTop
      (𝓝 (volume (ball (0 : E n) b) * L)) :=
    ENNReal.Tendsto.mul_const hvaltend (Or.inl hball0)
  have hmul : volume (ball (0 : E n) b) * L ≤
      volume (ball (0 : E n) b) * s :=
    le_of_tendsto hlim (Eventually.of_forall hscaled)
  have hright : L * volume (ball (0 : E n) b) ≤
      s * volume (ball (0 : E n) b) := by
    simpa only [mul_comm] using hmul
  have hLS : L ≤ s :=
    (ENNReal.mul_le_mul_iff_left hball0 hballtop).mp hright
  simpa only [L, s] using hLS

theorem surface_bound_open {n : ℕ} (hn : 2 ≤ n)
    {A : Set (E n)} (hA : IsOpen A) (hAbdd : Bornology.IsBounded A)
    (hfrontier : μHE[n - 1] (frontier A) ≠ ⊤) :
    (n : ℝ≥0∞) * volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ *
        volume A ^ (((n : ℝ) - 1) / n) ≤ μHE[n - 1] (frontier A) := by
  letI : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
  let C : ℝ≥0∞ := (n : ℝ≥0∞) *
    volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹
  let α : ℝ := ((n : ℝ) - 1) / n
  let s : ℝ≥0∞ := μHE[n - 1] (frontier A)
  have hnR : (1 : ℝ) < n := by
    exact_mod_cast (show 1 < n by omega)
  have hα : 0 < α := by
    dsimp only [α]
    exact div_pos (sub_pos.mpr hnR) (lt_trans zero_lt_one hnR)
  have hn0 : (n : ℝ≥0∞) ≠ 0 := by
    exact_mod_cast (show n ≠ 0 by omega)
  have hnTop : (n : ℝ≥0∞) ≠ ⊤ := ENNReal.natCast_ne_top n
  have hunitPos : 0 < volume (closedBall (0 : E n) 1) := by
    rw [Measure.addHaar_closedBall_eq_addHaar_ball volume (0 : E n) 1]
    exact measure_ball_pos volume (0 : E n) zero_lt_one
  have hunit0 : volume (closedBall (0 : E n) 1) ≠ 0 := hunitPos.ne'
  have hunitTop : volume (closedBall (0 : E n) 1) ≠ ⊤ :=
    measure_closedBall_lt_top.ne
  have hpow0 : volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ ≠ 0 :=
    (ENNReal.rpow_pos hunitPos hunitTop).ne'
  have hpowTop : volume (closedBall (0 : E n) 1) ^ (n : ℝ)⁻¹ ≠ ⊤ :=
    ENNReal.rpow_ne_top_of_ne_zero hunit0 hunitTop
  have hC0 : C ≠ 0 := by
    dsimp only [C]
    exact mul_ne_zero hn0 hpow0
  have hCtop : C ≠ ⊤ := by
    dsimp only [C]
    exact ENNReal.mul_ne_top hnTop hpowTop
  have hcancel : C * (C⁻¹ * s) = s := by
    rw [← mul_assoc, ENNReal.mul_inv_cancel hC0 hCtop, one_mul]
  let q : ℝ≥0∞ := (C⁻¹ * s) ^ α⁻¹
  have hcompactVolume (K : Set (E n)) (hKA : K ⊆ A) (hK : IsCompact K) :
      volume K ≤ q := by
    have hk := compact_surface_bound hn hA hAbdd hK hKA hfrontier
    have hk' : C * volume K ^ α ≤ s := by
      simpa only [C, α, s, mul_assoc] using hk
    have hp : volume K ^ α ≤ C⁻¹ * s := by
      apply (ENNReal.mul_le_mul_iff_left hC0 hCtop).mp
      calc
        volume K ^ α * C = C * volume K ^ α := mul_comm _ _
        _ ≤ s := hk'
        _ = (C⁻¹ * s) * C := by simpa only [mul_comm] using hcancel.symm
    have hp' : (volume K ^ α) ^ α⁻¹ ≤ (C⁻¹ * s) ^ α⁻¹ := by
      gcongr
    rw [← ENNReal.rpow_mul, mul_inv_cancel₀ hα.ne', ENNReal.rpow_one] at hp'
    exact hp'
  have hvolume : volume A ≤ q := by
    rw [hA.measure_eq_iSup_isCompact volume]
    exact iSup_le fun K ↦ iSup_le fun hKA ↦ iSup_le fun hK ↦
      hcompactVolume K hKA hK
  have hqpow : q ^ α = C⁻¹ * s := by
    dsimp only [q]
    rw [← ENNReal.rpow_mul, inv_mul_cancel₀ hα.ne', ENNReal.rpow_one]
  change C * volume A ^ α ≤ s
  calc
    C * volume A ^ α ≤ C * q ^ α := by gcongr
    _ = C * (C⁻¹ * s) := by rw [hqpow]
    _ = s := hcancel

end

end Submission.MollifiedBoundary
