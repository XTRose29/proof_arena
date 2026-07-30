import ChallengeDeps

namespace Submission.ProductKernel

open LeanEval.Analysis.SobolevMorreyProblem
open MeasureTheory
open ContinuousLinearMap Filter
open scoped Convolution ENNReal NNReal Topology

attribute [local instance 10000] NormedField.toNormedSpace

/-- A nonnegative smooth one-dimensional density supported in `[0, 1]`.
It is chosen as a derivative so that differences of its dilates have an
explicit compactly supported primitive. -/
noncomputable def density (x : ℝ) : ℝ :=
  deriv Real.smoothTransition x

@[fun_prop]
theorem density_contDiff : ContDiff ℝ (⊤ : ℕ∞) density := by
  change @ContDiff ℝ _ ℝ NonUnitalNormedRing.toNormedAddCommGroup
    NormedField.toNormedSpace ℝ Real.normedAddCommGroup
    NormedField.toNormedSpace (⊤ : ℕ∞) density
  unfold density
  exact Real.smoothTransition.contDiff.deriv' (n := (⊤ : ℕ∞))

theorem density_nonneg (x : ℝ) : 0 ≤ density x :=
  Real.smoothTransition.monotone.deriv_nonneg

theorem density_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : density x = 0 := by
  rw [density]
  apply deriv_zero_of_frequently_const (c := 0)
  rw [frequently_nhdsWithin_iff]
  exact (frequently_lt_nhds x).mono fun y hy ↦
    ⟨Real.smoothTransition.zero_of_nonpos (hy.le.trans hx), ne_of_lt hy⟩

theorem density_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : density x = 0 := by
  rw [density]
  apply deriv_zero_of_frequently_const (c := 1)
  rw [frequently_nhdsWithin_iff]
  exact (frequently_gt_nhds x).mono fun y hy ↦
    ⟨Real.smoothTransition.one_of_one_le (hx.trans hy.le), ne_of_gt hy⟩

theorem density_support_subset : Function.support density ⊆ Set.Ioc 0 1 := by
  intro x hx
  refine ⟨lt_of_not_ge fun h ↦ hx (density_eq_zero_of_nonpos h), ?_⟩
  exact le_of_not_gt fun h ↦ hx (density_eq_zero_of_one_le h.le)

theorem density_hasCompactSupport : HasCompactSupport density :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (density_support_subset.trans Set.Ioc_subset_Icc_self)

theorem density_integral : ∫ x : ℝ, density x = 1 := by
  have hdiff : Differentiable ℝ Real.smoothTransition :=
    (@Real.smoothTransition.contDiff (1 : ℕ∞)).differentiable (by norm_num)
  rw [← intervalIntegral.integral_eq_integral_of_support_subset density_support_subset]
  simpa only [density, Real.smoothTransition.one, Real.smoothTransition.zero, sub_zero] using
    intervalIntegral.integral_deriv_eq_sub
      (f := Real.smoothTransition) (a := (0 : ℝ)) (b := 1)
      (fun x _ ↦ hdiff x)
      (density_contDiff.continuous.intervalIntegrable 0 1)

noncomputable def baseKernel (n : ℕ) (x : E n) : ℝ :=
  ∏ i, density (x i)

theorem baseKernel_nonneg (n : ℕ) (x : E n) : 0 ≤ baseKernel n x := by
  exact Finset.prod_nonneg fun i _ ↦ density_nonneg (x i)

theorem baseKernel_contDiff (n : ℕ) : ContDiff ℝ (⊤ : ℕ∞) (baseKernel n) := by
  unfold baseKernel
  fun_prop

theorem baseKernel_integral (n : ℕ) : ∫ x : E n, baseKernel n x = 1 := by
  let e : E n ≃ᵐ (Fin n → ℝ) := (MeasurableEquiv.toLp 2 (Fin n → ℝ)).symm
  calc
    ∫ x : E n, baseKernel n x =
        ∫ x : E n, (fun y : Fin n → ℝ ↦ ∏ i, density (y i)) (e x) := by
          rfl
    _ = ∫ y : Fin n → ℝ, ∏ i, density (y i) :=
      (EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (Fin n)).integral_comp'
        (fun y : Fin n → ℝ ↦ ∏ i, density (y i))
    _ = ∏ _i : Fin n, ∫ x : ℝ, density x :=
      integral_fintype_prod_volume_eq_prod (fun _i : Fin n ↦ density)
    _ = 1 := by simp only [density_integral, Finset.prod_const_one]

theorem baseKernel_support_subset_ball (n : ℕ) :
    Function.support (baseKernel n) ⊆ Metric.ball 0 ((n : ℝ) + 1) := by
  intro x hx
  have hcoord (i : Fin n) : x i ∈ Set.Ioc (0 : ℝ) 1 := by
    apply density_support_subset
    exact (Finset.prod_ne_zero_iff.mp hx) i (Finset.mem_univ i)
  have hsum : ∑ i : Fin n, (x i) ^ 2 ≤ (n : ℝ) := by
    calc
      ∑ i : Fin n, (x i) ^ 2 ≤ ∑ _i : Fin n, (1 : ℝ) := by
        gcongr with i
        have hi := hcoord i
        exact (sq_le_one_iff₀ hi.1.le).2 hi.2
      _ = (n : ℝ) := by simp
  rw [Metric.mem_ball, dist_zero_right]
  have hnorm := EuclideanSpace.real_norm_sq_eq x
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnorm0 : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

theorem baseKernel_hasCompactSupport (n : ℕ) : HasCompactSupport (baseKernel n) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : E n) ((n : ℝ) + 1))
    ((baseKernel_support_subset_ball n).trans Metric.ball_subset_closedBall)

theorem exists_density_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ x : ℝ, |density x| ≤ C := by
  obtain ⟨C, hC⟩ :=
    density_contDiff.continuous.bounded_above_of_compact_support density_hasCompactSupport
  refine ⟨max 1 C, lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun x ↦ ?_⟩
  exact (hC x).trans (le_max_right _ _)

theorem exists_baseKernel_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : E n, |baseKernel n x| ≤ C := by
  obtain ⟨C, hC, hbound⟩ := exists_density_bound
  refine ⟨C ^ n, pow_pos hC n, fun x ↦ ?_⟩
  rw [← Real.norm_eq_abs, baseKernel, norm_prod]
  simp only [Real.norm_eq_abs]
  calc
    ∏ i : Fin n, |density (x i)| ≤ ∏ _i : Fin n, C := by
      exact Finset.prod_le_prod (fun _ _ ↦ abs_nonneg _) fun i _ ↦ hbound (x i)
    _ = C ^ n := by simp

noncomputable def scaledDensity (t x : ℝ) : ℝ :=
  t⁻¹ * density (t⁻¹ * x)

noncomputable def kernel (n : ℕ) (t : ℝ) (x : E n) : ℝ :=
  (t ^ n)⁻¹ * baseKernel n (t⁻¹ • x)

theorem kernel_eq_prod_scaledDensity (n : ℕ) {t : ℝ} (_ht : t ≠ 0) (x : E n) :
    kernel n t x = ∏ i, scaledDensity t (x i) := by
  simp only [kernel, baseKernel, scaledDensity, PiLp.smul_apply,
    Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin, inv_pow]
  ring_nf

theorem kernel_nonneg (n : ℕ) {t : ℝ} (ht : 0 ≤ t) (x : E n) :
    0 ≤ kernel n t x :=
  mul_nonneg (inv_nonneg.mpr (pow_nonneg ht n)) (baseKernel_nonneg n _)

theorem kernel_integral (n : ℕ) {t : ℝ} (ht : 0 < t) :
    ∫ x : E n, kernel n t x = 1 := by
  simp_rw [kernel, ← smul_eq_mul, integral_smul]
  rw [Measure.integral_comp_inv_smul_of_nonneg volume (baseKernel n) ht.le]
  simp only [finrank_euclideanSpace, Fintype.card_fin, baseKernel_integral, smul_eq_mul, mul_one]
  field_simp

theorem kernel_contDiff (n : ℕ) {t : ℝ} (_ht : t ≠ 0) :
    ContDiff ℝ (⊤ : ℕ∞) (kernel n t) := by
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun x : E n ↦ t⁻¹ • x) := by
    fun_prop
  exact contDiff_const.mul ((baseKernel_contDiff n).comp hscale)

theorem kernel_hasCompactSupport (n : ℕ) {t : ℝ} (ht : t ≠ 0) :
    HasCompactSupport (kernel n t) := by
  change HasCompactSupport
    ((fun _ : E n ↦ (t ^ n)⁻¹) * fun x ↦ baseKernel n (t⁻¹ • x))
  exact ((baseKernel_hasCompactSupport n).comp_smul (inv_ne_zero ht)).mul_left

theorem kernel_support_subset_ball (n : ℕ) {t : ℝ} (ht : 0 < t) :
    Function.support (kernel n t) ⊆
      Metric.ball 0 (((n : ℝ) + 1) * t) := by
  intro x hx
  have hbase : t⁻¹ • x ∈ Function.support (baseKernel n) := by
    intro hzero
    exact hx (by simp only [kernel, hzero, mul_zero])
  have hball := baseKernel_support_subset_ball n hbase
  rw [Metric.mem_ball, dist_zero_right] at hball ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht] at hball
  calc
    ‖x‖ = t * (t⁻¹ * ‖x‖) := by field_simp
    _ < t * ((n : ℝ) + 1) := mul_lt_mul_of_pos_left hball ht
    _ = ((n : ℝ) + 1) * t := by ring

theorem abs_kernel_le (n : ℕ) {t C : ℝ} (ht : 0 < t)
    (hC : ∀ x : E n, |baseKernel n x| ≤ C) (x : E n) :
    |kernel n t x| ≤ (t ^ n)⁻¹ * C := by
  rw [kernel, abs_mul, abs_inv, abs_pow, abs_of_pos ht]
  exact mul_le_mul_of_nonneg_left (hC _) (inv_nonneg.mpr (pow_nonneg ht.le _))

noncomputable def regularize (n : ℕ) (t : ℝ) (f : E n → ℝ) : E n → ℝ :=
  kernel n t ⋆[lsmul ℝ ℝ, volume] f

theorem regularize_apply (n : ℕ) (t : ℝ) (f : E n → ℝ) (x : E n) :
    regularize n t f x = ∫ y, kernel n t (x - y) * f y := by
  rw [regularize, convolution_eq_swap]
  simp only [lsmul_apply, smul_eq_mul]

theorem regularize_contDiff (n : ℕ) {t : ℝ} (ht : t ≠ 0) {f : E n → ℝ}
    (hf : LocallyIntegrable f volume) :
    ContDiff ℝ (⊤ : ℕ∞) (regularize n t f) :=
  (kernel_hasCompactSupport n ht).contDiff_convolution_left
    (lsmul ℝ ℝ) (kernel_contDiff n ht) hf

theorem reflectedKernel_contDiff (n : ℕ) {t : ℝ} (ht : t ≠ 0) (x : E n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ kernel n t (x - y)) := by
  exact (kernel_contDiff n ht).comp (contDiff_const.sub contDiff_id)

theorem reflectedKernel_hasCompactSupport (n : ℕ) {t : ℝ} (ht : t ≠ 0) (x : E n) :
    HasCompactSupport (fun y ↦ kernel n t (x - y)) := by
  change HasCompactSupport ((kernel n t) ∘ Homeomorph.subLeft x)
  exact (kernel_hasCompactSupport n ht).comp_homeomorph (Homeomorph.subLeft x)

theorem partialDeriv_reflectedKernel (n : ℕ) {t : ℝ} (ht : t ≠ 0)
    (i : Fin n) (x y : E n) :
    partialDeriv i (fun z ↦ kernel n t (x - z)) y =
      -partialDeriv i (kernel n t) (x - y) := by
  unfold partialDeriv
  rw [show (fun z ↦ kernel n t (x - z)) =
      (kernel n t) ∘ (fun z ↦ x - z) by rfl]
  rw [fderiv_comp y
    ((kernel_contDiff n ht).differentiable (by norm_num) _)
    (by fun_prop)]
  have hinner :
      (fderiv ℝ (fun z : E n ↦ x - z) y)
          (EuclideanSpace.single i (1 : ℝ)) =
        -EuclideanSpace.single i (1 : ℝ) := by
    rw [fderiv_const_sub]
    simp
  rw [ContinuousLinearMap.comp_apply, hinner, map_neg]

noncomputable def primitive (x : ℝ) : ℝ :=
  Real.smoothTransition (2 * x) - Real.smoothTransition x

@[fun_prop]
theorem primitive_contDiff : ContDiff ℝ (⊤ : ℕ∞) primitive := by
  exact (Real.smoothTransition.contDiff.comp (contDiff_const.mul contDiff_id)).sub
    Real.smoothTransition.contDiff

theorem primitive_eq_zero_of_nonpos {x : ℝ} (hx : x ≤ 0) : primitive x = 0 := by
  have h2x : 2 * x ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by norm_num) hx
  rw [primitive, Real.smoothTransition.zero_of_nonpos h2x,
    Real.smoothTransition.zero_of_nonpos hx, sub_self]

theorem primitive_eq_zero_of_one_le {x : ℝ} (hx : 1 ≤ x) : primitive x = 0 := by
  have h2x : 1 ≤ 2 * x := by linarith
  rw [primitive, Real.smoothTransition.one_of_one_le h2x,
    Real.smoothTransition.one_of_one_le hx, sub_self]

theorem primitive_support_subset : Function.support primitive ⊆ Set.Ioc 0 1 := by
  intro x hx
  refine ⟨lt_of_not_ge fun h ↦ hx (primitive_eq_zero_of_nonpos h), ?_⟩
  exact le_of_not_gt fun h ↦ hx (primitive_eq_zero_of_one_le h.le)

theorem primitive_hasCompactSupport : HasCompactSupport primitive :=
  HasCompactSupport.of_support_subset_isCompact isCompact_Icc
    (primitive_support_subset.trans Set.Ioc_subset_Icc_self)

theorem deriv_primitive (x : ℝ) :
    deriv primitive x = scaledDensity (1 / 2) x - scaledDensity 1 x := by
  rw [show primitive = (fun x ↦ Real.smoothTransition (2 * x)) -
      Real.smoothTransition by rfl,
    deriv_sub]
  · rw [deriv_comp_mul_left]
    norm_num [scaledDensity, density]
  · fun_prop
  · exact (@Real.smoothTransition.contDiff (1 : ℕ∞)).differentiable
      (by norm_num) _

noncomputable def baseBridge (n : ℕ) (i : Fin n) (x : E n) : ℝ :=
  primitive (x i) *
    (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i),
      scaledDensity (1 / 2) (x j)) *
    (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ i < j),
      scaledDensity 1 (x j))

@[fun_prop]
theorem baseBridge_contDiff (n : ℕ) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (baseBridge n i) := by
  unfold baseBridge scaledDensity
  fun_prop

theorem baseBridge_support_subset_ball (n : ℕ) (i : Fin n) :
    Function.support (baseBridge n i) ⊆ Metric.ball 0 ((n : ℝ) + 1) := by
  intro x hx
  have hprimitive : primitive (x i) ≠ 0 := by
    intro hzero
    exact hx (by simp only [baseBridge, hzero, zero_mul])
  have hlower :
      (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i),
        scaledDensity (1 / 2) (x j)) ≠ 0 := by
    intro hzero
    exact hx (by simp only [baseBridge, hzero, mul_zero, zero_mul])
  have hupper :
      (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ i < j),
        scaledDensity 1 (x j)) ≠ 0 := by
    intro hzero
    exact hx (by simp only [baseBridge, hzero, mul_zero])
  have hcoord (j : Fin n) : |x j| ≤ 1 := by
    rcases lt_trichotomy j i with hji | rfl | hij
    · have hjmem : j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i) := by simp [hji]
      have hjne := (Finset.prod_ne_zero_iff.mp hlower) j hjmem
      have hdne : density (2 * x j) ≠ 0 := by
        norm_num [scaledDensity] at hjne
        exact hjne
      have hj := density_support_subset hdne
      rw [abs_of_pos (by linarith [hj.1])]
      linarith [hj.2]
    · have hj := primitive_support_subset hprimitive
      rw [abs_of_pos hj.1]
      exact hj.2
    · have hjmem : j ∈ Finset.univ.filter (fun j : Fin n ↦ i < j) := by simp [hij]
      have hjne := (Finset.prod_ne_zero_iff.mp hupper) j hjmem
      have hdne : density (x j) ≠ 0 := by
        simpa only [scaledDensity, inv_one, one_mul] using hjne
      have hj := density_support_subset hdne
      rw [abs_of_pos hj.1]
      exact hj.2
  have hsum : ∑ j : Fin n, (x j) ^ 2 ≤ (n : ℝ) := by
    calc
      ∑ j : Fin n, (x j) ^ 2 ≤ ∑ _j : Fin n, (1 : ℝ) := by
        gcongr with j
        nlinarith [abs_nonneg (x j), sq_abs (x j), hcoord j]
      _ = (n : ℝ) := by simp
  rw [Metric.mem_ball, dist_zero_right]
  have hnorm := EuclideanSpace.real_norm_sq_eq x
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hnorm0 : 0 ≤ ‖x‖ := norm_nonneg x
  nlinarith

theorem baseBridge_hasCompactSupport (n : ℕ) (i : Fin n) :
    HasCompactSupport (baseBridge n i) :=
  HasCompactSupport.of_support_subset_isCompact
    (isCompact_closedBall (0 : E n) ((n : ℝ) + 1))
    ((baseBridge_support_subset_ball n i).trans Metric.ball_subset_closedBall)

theorem exists_baseBridge_bound (n : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ i : Fin n, ∀ x : E n, |baseBridge n i x| ≤ C := by
  by_cases hn : n = 0
  · subst n
    exact ⟨1, zero_lt_one, fun i ↦ Fin.elim0 i⟩
  · letI : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero hn)
    let C₀ : Fin n → ℝ := fun i ↦ Classical.choose
      ((baseBridge_contDiff n i).continuous.bounded_above_of_compact_support
        (baseBridge_hasCompactSupport n i))
    have hC₀ (i : Fin n) (x : E n) : |baseBridge n i x| ≤ C₀ i := by
      simpa only [Real.norm_eq_abs, C₀] using
        (Classical.choose_spec
          ((baseBridge_contDiff n i).continuous.bounded_above_of_compact_support
            (baseBridge_hasCompactSupport n i))) x
    refine ⟨max 1 (Finset.univ.sup' (Finset.univ_nonempty) C₀),
      lt_of_lt_of_le zero_lt_one (le_max_left _ _), fun i x ↦ ?_⟩
    exact (hC₀ i x).trans <|
      (Finset.le_sup' C₀ (Finset.mem_univ i)).trans (le_max_right _ _)

noncomputable def bridge (n : ℕ) (t : ℝ) (i : Fin n) (x : E n) : ℝ :=
  t ^ (1 - n : ℤ) * baseBridge n i (t⁻¹ • x)

theorem bridge_contDiff (n : ℕ) {t : ℝ} (_ht : t ≠ 0) (i : Fin n) :
    ContDiff ℝ (⊤ : ℕ∞) (bridge n t i) := by
  have hscale : ContDiff ℝ (⊤ : ℕ∞) (fun x : E n ↦ t⁻¹ • x) := by
    fun_prop
  exact contDiff_const.mul ((baseBridge_contDiff n i).comp hscale)

theorem bridge_hasCompactSupport (n : ℕ) {t : ℝ} (ht : t ≠ 0) (i : Fin n) :
    HasCompactSupport (bridge n t i) := by
  change HasCompactSupport
    ((fun _ : E n ↦ t ^ (1 - n : ℤ)) * fun x ↦ baseBridge n i (t⁻¹ • x))
  exact ((baseBridge_hasCompactSupport n i).comp_smul (inv_ne_zero ht)).mul_left

theorem bridge_support_subset_ball (n : ℕ) {t : ℝ} (ht : 0 < t) (i : Fin n) :
    Function.support (bridge n t i) ⊆
      Metric.ball 0 (((n : ℝ) + 1) * t) := by
  intro x hx
  have hbase : t⁻¹ • x ∈ Function.support (baseBridge n i) := by
    intro hzero
    exact hx (by simp only [bridge, hzero, mul_zero])
  have hball := baseBridge_support_subset_ball n i hbase
  rw [Metric.mem_ball, dist_zero_right] at hball ⊢
  rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos ht] at hball
  calc
    ‖x‖ = t * (t⁻¹ * ‖x‖) := by field_simp
    _ < t * ((n : ℝ) + 1) := mul_lt_mul_of_pos_left hball ht
    _ = ((n : ℝ) + 1) * t := by ring

theorem abs_bridge_le (n : ℕ) {t C : ℝ} (ht : 0 < t)
    (hC : ∀ i : Fin n, ∀ x : E n, |baseBridge n i x| ≤ C)
    (i : Fin n) (x : E n) :
    |bridge n t i x| ≤ t ^ (1 - n : ℤ) * C := by
  rw [bridge, abs_mul, abs_zpow, abs_of_pos ht]
  exact mul_le_mul_of_nonneg_left (hC i _) (zpow_nonneg ht.le _)

theorem partialDeriv_baseBridge (n : ℕ) (i : Fin n) (x : E n) :
    partialDeriv i (baseBridge n i) x =
      (scaledDensity (1 / 2) (x i) - scaledDensity 1 (x i)) *
        (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i),
          scaledDensity (1 / 2) (x j)) *
        (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ i < j),
          scaledDensity 1 (x j)) := by
  have hd : DifferentiableAt ℝ (baseBridge n i) x :=
    (baseBridge_contDiff n i).differentiable (by norm_num) x
  unfold partialDeriv
  rw [← hd.lineDeriv_eq_fderiv]
  unfold lineDeriv
  have hline :
      (fun s : ℝ ↦
        baseBridge n i (x + s • EuclideanSpace.single i (1 : ℝ))) =
      (fun s : ℝ ↦
        primitive (x i + s) *
          (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i),
            scaledDensity (1 / 2) (x j)) *
          (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ i < j),
            scaledDensity 1 (x j))) := by
    funext s
    have hlower :
        (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i),
          scaledDensity (1 / 2)
            ((x + s • EuclideanSpace.single i (1 : ℝ)) j)) =
        ∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ j < i),
          scaledDensity (1 / 2) (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hji : j < i := (Finset.mem_filter.mp hj).2
      rw [show (x + s • EuclideanSpace.single i (1 : ℝ)) j = x j by
        simp [ne_of_lt hji]]
    have hupper :
        (∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ i < j),
          scaledDensity 1
            ((x + s • EuclideanSpace.single i (1 : ℝ)) j)) =
        ∏ j ∈ Finset.univ.filter (fun j : Fin n ↦ i < j),
          scaledDensity 1 (x j) := by
      apply Finset.prod_congr rfl
      intro j hj
      have hij : i < j := (Finset.mem_filter.mp hj).2
      rw [show (x + s • EuclideanSpace.single i (1 : ℝ)) j = x j by
        simp [ne_of_gt hij]]
    rw [baseBridge, hlower, hupper]
    simp
  rw [hline, deriv_mul_const_field, deriv_mul_const_field,
    deriv_comp_const_add]
  simp only [add_zero, deriv_primitive]

theorem sum_partialDeriv_baseBridge (n : ℕ) (x : E n) :
    ∑ i : Fin n, partialDeriv i (baseBridge n i) x =
      kernel n (1 / 2) x - kernel n 1 x := by
  rw [kernel_eq_prod_scaledDensity n (by norm_num : (1 / 2 : ℝ) ≠ 0),
    kernel_eq_prod_scaledDensity n one_ne_zero]
  simp_rw [partialDeriv_baseBridge]
  have h := Finset.prod_add_ordered (Finset.univ : Finset (Fin n))
    (fun i ↦ scaledDensity 1 (x i))
    (fun i ↦ scaledDensity (1 / 2) (x i) - scaledDensity 1 (x i))
  have hadd (i : Fin n) :
      scaledDensity 1 (x i) +
          (scaledDensity (1 / 2) (x i) - scaledDensity 1 (x i)) =
        scaledDensity (1 / 2) (x i) := by ring
  simp_rw [hadd] at h
  rw [eq_sub_iff_add_eq]
  linarith

theorem partialDeriv_bridge (n : ℕ) {t : ℝ} (ht : t ≠ 0)
    (i : Fin n) (x : E n) :
    partialDeriv i (bridge n t i) x =
      t ^ (-n : ℤ) * partialDeriv i (baseBridge n i) (t⁻¹ • x) := by
  unfold partialDeriv bridge
  have hd :
      DifferentiableAt ℝ (fun z : E n ↦ baseBridge n i (t⁻¹ • z)) x := by
    exact ((baseBridge_contDiff n i).differentiable (by norm_num) _).comp x
      (by fun_prop)
  rw [fderiv_const_mul hd, fderiv_comp_smul]
  simp only [smul_apply, smul_eq_mul]
  have hcoeff :
      t ^ (1 - (n : ℤ)) * t⁻¹ = t ^ (-(n : ℤ)) := by
    rw [← zpow_neg_one, ← zpow_add₀ ht]
    congr 1
    omega
  rw [← mul_assoc, hcoeff]

theorem sum_partialDeriv_bridge (n : ℕ) {t : ℝ} (ht : 0 < t) (x : E n) :
    ∑ i : Fin n, partialDeriv i (bridge n t i) x =
      kernel n (t / 2) x - kernel n t x := by
  simp_rw [partialDeriv_bridge n ht.ne']
  rw [← Finset.mul_sum, sum_partialDeriv_baseBridge]
  simp only [kernel]
  have ht0 : t ≠ 0 := ht.ne'
  have htwo : (2 : ℝ) ≠ 0 := by norm_num
  simp only [zpow_neg, zpow_natCast]
  field_simp
  have harg :
      (2 : ℝ) • (t⁻¹ • x) = (2 / t) • x := by
    rw [smul_smul]
    congr 1
  have hpow : (t / 2) ^ n = (2 ^ n)⁻¹ * t ^ n := by
    rw [div_pow, div_eq_mul_inv]
    ring
  simp only [one_div, one_pow, one_smul, inv_pow]
  rw [harg, hpow]
  ring

theorem reflectedBridge_contDiff (n : ℕ) {t : ℝ} (ht : t ≠ 0)
    (i : Fin n) (x : E n) :
    ContDiff ℝ (⊤ : ℕ∞) (fun y ↦ bridge n t i (x - y)) := by
  exact (bridge_contDiff n ht i).comp (contDiff_const.sub contDiff_id)

theorem reflectedBridge_hasCompactSupport (n : ℕ) {t : ℝ} (ht : t ≠ 0)
    (i : Fin n) (x : E n) :
    HasCompactSupport (fun y ↦ bridge n t i (x - y)) := by
  change HasCompactSupport ((bridge n t i) ∘ Homeomorph.subLeft x)
  exact (bridge_hasCompactSupport n ht i).comp_homeomorph (Homeomorph.subLeft x)

theorem partialDeriv_reflectedBridge (n : ℕ) {t : ℝ} (ht : t ≠ 0)
    (i : Fin n) (x y : E n) :
    partialDeriv i (fun z ↦ bridge n t i (x - z)) y =
      -partialDeriv i (bridge n t i) (x - y) := by
  unfold partialDeriv
  rw [show (fun z ↦ bridge n t i (x - z)) =
      (bridge n t i) ∘ (fun z ↦ x - z) by rfl]
  rw [fderiv_comp y
    ((bridge_contDiff n ht i).differentiable (by norm_num) _)
    (by fun_prop)]
  have hinner :
      (fderiv ℝ (fun z : E n ↦ x - z) y)
          (EuclideanSpace.single i (1 : ℝ)) =
        -EuclideanSpace.single i (1 : ℝ) := by
    rw [fderiv_const_sub]
    simp
  rw [ContinuousLinearMap.comp_apply, hinner, map_neg]

end Submission.ProductKernel
