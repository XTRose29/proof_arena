import Submission.CauchyRepresentation

open Function Set
open scoped ContDiff Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- A Cauchy kernel with a continuous density, bundled as a continuous
function on `K`.  The density support is disjoint from `K`, so every apparent
singularity has zero density on a neighborhood. -/
def cauchyDensityMap (K : Set ℂ) (q : ℂ → ℂ)
    (hdisj : Disjoint (tsupport q) K) (w : ℂ) : C(K, ℂ) where
  toFun z := (w - (z : ℂ))⁻¹ * q w
  continuous_toFun := by
    by_cases hq : q w = 0
    · simpa only [hq, mul_zero] using
        (continuous_const : Continuous fun _ : K ↦ (0 : ℂ))
    · have hwq : w ∈ tsupport q := subset_tsupport _ hq
      have hwK : w ∉ K := fun hw ↦
        Set.disjoint_left.mp hdisj hwq hw
      have hne : ∀ z : K, w - (z : ℂ) ≠ 0 := fun z ↦
        sub_ne_zero.mpr fun hwz ↦ hwK (hwz ▸ z.property)
      exact ((continuous_const.sub continuous_subtype_val).inv₀ hne).mul
        continuous_const

@[simp]
theorem cauchyDensityMap_apply (K : Set ℂ) (q : ℂ → ℂ)
    (hdisj : Disjoint (tsupport q) K) (w : ℂ) (z : K) :
    cauchyDensityMap K q hdisj w z = (w - (z : ℂ))⁻¹ * q w :=
  rfl

/-- A continuous compactly supported density with support disjoint from `K`
defines an integrable `C(K, ℂ)`-valued Cauchy kernel. -/
theorem integrable_cauchyDensityMap
    {K : Set ℂ} [CompactSpace K] (q : ℂ → ℂ)
    (hq : Continuous q) (hqc : HasCompactSupport q)
    (hdisj : Disjoint (tsupport q) K) :
    MeasureTheory.Integrable (cauchyDensityMap K q hdisj) := by
  let Φ : ℂ → C(K, ℂ) := cauchyDensityMap K q hdisj
  have huncurry :
      Continuous fun p : ℂ × K ↦
        (p.1 - (p.2 : ℂ))⁻¹ * q p.1 := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p.1 = (p.2 : ℂ)
    · have hpK : p.1 ∈ K := hp ▸ p.2.property
      have hpq : p.1 ∉ tsupport q := fun hpS ↦
        Set.disjoint_left.mp hdisj hpS hpK
      rw [notMem_tsupport_iff_eventuallyEq] at hpq
      apply ContinuousAt.congr_of_eventuallyEq
        (continuousAt_const :
          ContinuousAt (fun _ : ℂ × K ↦ (0 : ℂ)) p)
      filter_upwards [continuousAt_fst.eventually hpq] with r hr
      simp only [hr, Pi.zero_apply, mul_zero]
    · exact
        ((continuousAt_fst.sub
          (continuousAt_subtype_val.comp continuousAt_snd)).inv₀
            (sub_ne_zero.mpr hp)).mul
          (hq.continuousAt.comp continuousAt_fst)
  have hΦcontinuous : Continuous Φ := by
    refine ContinuousMap.continuous_of_continuous_uncurry Φ ?_
    change Continuous fun p : ℂ × K ↦
      (p.1 - (p.2 : ℂ))⁻¹ * q p.1
    exact huncurry
  have hΦcompact : HasCompactSupport Φ := by
    apply hqc.mono'
    intro w hw
    by_contra hwq
    have hzero : q w = 0 := by
      by_contra hne
      exact hwq (subset_tsupport _ hne)
    apply hw
    ext z
    simp [Φ, cauchyDensityMap, hzero]
  exact hΦcontinuous.integrable_of_hasCompactSupport hΦcompact

/-- The Cauchy transform of a continuous compactly supported density whose
topological support misses `K` belongs to the closed polynomial algebra on
`K`. -/
theorem cauchyDensityIntegral_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    (q : ℂ → ℂ) (hq : Continuous q) (hqc : HasCompactSupport q)
    (hdisj : Disjoint (tsupport q) K) :
    (∫ w : ℂ, cauchyDensityMap K q hdisj w) ∈
      (polynomialFunctions K).topologicalClosure := by
  let A : Subalgebra ℂ C(K, ℂ) :=
    (polynomialFunctions K).topologicalClosure
  let M : Submodule ℂ C(K, ℂ) := A.toSubmodule
  let Φ : ℂ → C(K, ℂ) := cauchyDensityMap K q hdisj
  have huncurry :
      Continuous fun p : ℂ × K ↦
        (p.1 - (p.2 : ℂ))⁻¹ * q p.1 := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p.1 = (p.2 : ℂ)
    · have hpK : p.1 ∈ K := hp ▸ p.2.property
      have hpq : p.1 ∉ tsupport q := fun hpS ↦
        Set.disjoint_left.mp hdisj hpS hpK
      rw [notMem_tsupport_iff_eventuallyEq] at hpq
      apply ContinuousAt.congr_of_eventuallyEq
        (continuousAt_const :
          ContinuousAt (fun _ : ℂ × K ↦ (0 : ℂ)) p)
      filter_upwards [continuousAt_fst.eventually hpq] with r hr
      simp only [hr, Pi.zero_apply, mul_zero]
    · exact
        ((continuousAt_fst.sub
          (continuousAt_subtype_val.comp continuousAt_snd)).inv₀
            (sub_ne_zero.mpr hp)).mul
          (hq.continuousAt.comp continuousAt_fst)
  have hΦcontinuous : Continuous Φ := by
    refine ContinuousMap.continuous_of_continuous_uncurry Φ ?_
    change Continuous fun p : ℂ × K ↦
      (p.1 - (p.2 : ℂ))⁻¹ * q p.1
    exact huncurry
  have hΦcompact : HasCompactSupport Φ := by
    apply hqc.mono'
    intro w hw
    by_contra hwq
    have hzero : q w = 0 := by
      by_contra hne
      exact hwq (subset_tsupport _ hne)
    apply hw
    ext z
    simp [Φ, cauchyDensityMap, hzero]
  have hΦintegrable : MeasureTheory.Integrable Φ :=
    hΦcontinuous.integrable_of_hasCompactSupport hΦcompact
  have hΦmem (w : ℂ) : Φ w ∈ A := by
    by_cases hqw : q w = 0
    · have hzero : Φ w = 0 := by
        ext z
        simp [Φ, cauchyDensityMap, hqw]
      rw [hzero]
      exact A.zero_mem
    · have hwq : w ∈ tsupport q := subset_tsupport _ hqw
      have hwK : w ∉ K := fun hw ↦
        Set.disjoint_left.mp hdisj hwq hw
      obtain ⟨r, hr⟩ :=
        exists_resolvent_mem_polynomialClosure hKc hwK
      have heq : Φ w = q w • (r : C(K, ℂ)) := by
        ext z
        change
          (w - (z : ℂ))⁻¹ * q w =
            q w * (r : C(K, ℂ)) z
        rw [hr z]
        ring
      rw [heq]
      exact A.smul_mem r.property _
  have hMclosed : IsClosed (M : Set C(K, ℂ)) := by
    change IsClosed (A : Set C(K, ℂ))
    exact Subalgebra.isClosed_topologicalClosure _
  letI : IsClosed (M : Set C(K, ℂ)) := hMclosed
  letI : CompleteSpace (C(K, ℂ) ⧸ M) := inferInstance
  have hquotient :
      M.mkQL (∫ w : ℂ, Φ w) = 0 := by
    rw [← ContinuousLinearMap.integral_comp_comm M.mkQL hΦintegrable]
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards with w
    exact (Submodule.Quotient.mk_eq_zero M).mpr (hΦmem w)
  change (∫ w : ℂ, Φ w) ∈ M
  rw [← Submodule.Quotient.mk_eq_zero]
  exact hquotient

/-- The Cauchy--Pompeiu integrand, bundled as a continuous function on `K`.
At a source point in `K` the defect is required to vanish, so the apparent
singularity is the zero function. -/
def cauchyDefectMap (K : Set ℂ) (g : ℂ → ℂ)
    (hdisj : Disjoint (tsupport (crDefect g)) K) (w : ℂ) : C(K, ℂ) where
  toFun z :=
    -((2 * Real.pi * Complex.I)⁻¹) *
      ((w - (z : ℂ))⁻¹ * crDefect g w)
  continuous_toFun := by
    by_cases hD : crDefect g w = 0
    · simpa only [hD, mul_zero, neg_mul, zero_mul] using
        (continuous_const : Continuous fun _ : K ↦ (0 : ℂ))
    · have hwD : w ∈ tsupport (crDefect g) :=
        subset_tsupport _ hD
      have hwK : w ∉ K := fun hw ↦
        Set.disjoint_left.mp hdisj hwD hw
      have hne : ∀ z : K, w - (z : ℂ) ≠ 0 := fun z ↦
        sub_ne_zero.mpr fun hwz ↦ hwK (hwz ▸ z.property)
      exact continuous_const.mul
        (((continuous_const.sub continuous_subtype_val).inv₀ hne).mul
          continuous_const)

@[simp]
theorem cauchyDefectMap_apply (K : Set ℂ) (g : ℂ → ℂ)
    (hdisj : Disjoint (tsupport (crDefect g)) K) (w : ℂ) (z : K) :
    cauchyDefectMap K g hdisj w z =
      -((2 * Real.pi * Complex.I)⁻¹) *
        ((w - (z : ℂ))⁻¹ * crDefect g w) :=
  rfl

/-- If the Cauchy--Riemann defect of a smooth compactly supported function is
supported away from `K`, then its restriction lies in the closed polynomial
algebra on `K`. -/
theorem mem_polynomialClosure_of_crDefect_tsupport_disjoint
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hdisj : Disjoint (tsupport (crDefect g)) K) :
    restrictTo g hg.continuous.continuousOn ∈
      (polynomialFunctions K).topologicalClosure := by
  let A : Subalgebra ℂ C(K, ℂ) :=
    (polynomialFunctions K).topologicalClosure
  let M : Submodule ℂ C(K, ℂ) := A.toSubmodule
  let Φ : ℂ → C(K, ℂ) := cauchyDefectMap K g hdisj
  have hDcontinuous : Continuous (crDefect g) :=
    continuous_crDefect g hg
  have huncurry :
      Continuous fun p : ℂ × K ↦
        -((2 * Real.pi * Complex.I)⁻¹) *
          ((p.1 - (p.2 : ℂ))⁻¹ * crDefect g p.1) := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p.1 = (p.2 : ℂ)
    · have hpK : p.1 ∈ K := hp ▸ p.2.property
      have hpD : p.1 ∉ tsupport (crDefect g) := fun hpS ↦
        Set.disjoint_left.mp hdisj hpS hpK
      rw [notMem_tsupport_iff_eventuallyEq] at hpD
      apply ContinuousAt.congr_of_eventuallyEq
        (continuousAt_const :
          ContinuousAt (fun _ : ℂ × K ↦ (0 : ℂ)) p)
      filter_upwards [continuousAt_fst.eventually hpD] with q hq
      simp only [hq, Pi.zero_apply, mul_zero]
    · exact continuousAt_const.mul
        (((continuousAt_fst.sub
          (continuousAt_subtype_val.comp continuousAt_snd)).inv₀
            (sub_ne_zero.mpr hp)).mul
          (hDcontinuous.continuousAt.comp continuousAt_fst))
  have hΦcontinuous : Continuous Φ := by
    refine ContinuousMap.continuous_of_continuous_uncurry Φ ?_
    change Continuous fun p : ℂ × K ↦
      -((2 * Real.pi * Complex.I)⁻¹) *
        ((p.1 - (p.2 : ℂ))⁻¹ * crDefect g p.1)
    exact huncurry
  have hΦcompact : HasCompactSupport Φ := by
    apply (crDefect_hasCompactSupport g hgc).mono'
    intro w hw
    by_contra hDw
    have hzero : crDefect g w = 0 := by
      by_contra hne
      exact hDw (subset_tsupport _ hne)
    apply hw
    ext z
    simp [Φ, cauchyDefectMap, hzero]
  have hΦintegrable : MeasureTheory.Integrable Φ :=
    hΦcontinuous.integrable_of_hasCompactSupport hΦcompact
  have hΦmem (w : ℂ) : Φ w ∈ A := by
    by_cases hDw : crDefect g w = 0
    · have hzero : Φ w = 0 := by
        ext z
        simp [Φ, cauchyDefectMap, hDw]
      rw [hzero]
      exact A.zero_mem
    · have hwD : w ∈ tsupport (crDefect g) :=
        subset_tsupport _ hDw
      have hwK : w ∉ K := fun hw ↦
        Set.disjoint_left.mp hdisj hwD hw
      obtain ⟨r, hr⟩ :=
        exists_resolvent_mem_polynomialClosure hKc hwK
      have heq :
          Φ w =
            (-((2 * Real.pi * Complex.I)⁻¹) * crDefect g w) •
              (r : C(K, ℂ)) := by
        ext z
        change
          -((2 * Real.pi * Complex.I)⁻¹) *
              ((w - (z : ℂ))⁻¹ * crDefect g w) =
            (-((2 * Real.pi * Complex.I)⁻¹) * crDefect g w) *
              (r : C(K, ℂ)) z
        rw [hr z]
        ring
      rw [heq]
      exact A.smul_mem r.property _
  have hMclosed : IsClosed (M : Set C(K, ℂ)) := by
    change IsClosed (A : Set C(K, ℂ))
    exact Subalgebra.isClosed_topologicalClosure _
  letI : IsClosed (M : Set C(K, ℂ)) := hMclosed
  letI : CompleteSpace (C(K, ℂ) ⧸ M) := inferInstance
  have hquotient :
      M.mkQL (∫ w : ℂ, Φ w) = 0 := by
    rw [← ContinuousLinearMap.integral_comp_comm M.mkQL hΦintegrable]
    apply MeasureTheory.integral_eq_zero_of_ae
    filter_upwards with w
    exact (Submodule.Quotient.mk_eq_zero M).mpr (hΦmem w)
  have hintegral :
      (∫ w : ℂ, Φ w) ∈ M := by
    rw [← Submodule.Quotient.mk_eq_zero]
    exact hquotient
  have htwoPiI : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero, Complex.I_ne_zero]
  have hintegral_apply (z : K) :
      (∫ w : ℂ, Φ w) z = g z := by
    rw [ContinuousMap.integral_apply hΦintegrable]
    have hformula := cauchyPompeiu_compactSupport g hg hgc (z : ℂ)
    change
      (∫ w : ℂ,
        -((2 * Real.pi * Complex.I)⁻¹) *
          ((w - (z : ℂ))⁻¹ * crDefect g w)) = g z
    calc
      (∫ w : ℂ,
          -((2 * Real.pi * Complex.I)⁻¹) *
            ((w - (z : ℂ))⁻¹ * crDefect g w)) =
          -((2 * Real.pi * Complex.I)⁻¹) *
            (∫ w : ℂ, (w - (z : ℂ))⁻¹ * crDefect g w) := by
              rw [MeasureTheory.integral_const_mul]
      _ = (2 * Real.pi * Complex.I)⁻¹ *
          (- (∫ w : ℂ, (w - (z : ℂ))⁻¹ * crDefect g w)) := by
            ring
      _ = (2 * Real.pi * Complex.I)⁻¹ *
          ((2 * Real.pi * Complex.I) * g z) := by
            rw [hformula]
      _ = g z := by
            rw [← mul_assoc, inv_mul_cancel₀ htwoPiI, one_mul]
  have heq :
      restrictTo g hg.continuous.continuousOn =
        ∫ w : ℂ, Φ w := by
    ext z
    exact (hintegral_apply z).symm
  rw [heq]
  exact hintegral

/-- A smooth compactly supported function holomorphic on a neighborhood of `K`
belongs to the closed polynomial algebra on `K`. -/
theorem mem_polynomialClosure_of_differentiableOn_nhd
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    (hgU : DifferentiableOn ℂ g U) :
    restrictTo g hg.continuous.continuousOn ∈
      (polynomialFunctions K).topologicalClosure := by
  apply mem_polynomialClosure_of_crDefect_tsupport_disjoint
    hKc g hg hgc
  rw [Set.disjoint_left]
  intro z hzD hzK
  apply ((notMem_tsupport_iff_eventuallyEq).2 ?_) hzD
  filter_upwards [hU.mem_nhds (hKU hzK)] with w hw
  simpa only [Pi.zero_apply] using
    crDefect_eq_zero_of_differentiableAt
      (hgU.differentiableAt (hU.mem_nhds hw))

/-- Runge's polynomial-approximation conclusion for a smooth compactly
supported function holomorphic on a neighborhood of `K`. -/
theorem exists_polynomial_approx_of_differentiableOn_nhd
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    {U : Set ℂ} (hU : IsOpen U) (hKU : K ⊆ U)
    (hgU : DifferentiableOn ℂ g U) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  exact
    (mem_polynomialFunctions_topologicalClosure_iff
      g hg.continuous.continuousOn).mp
      (mem_polynomialClosure_of_differentiableOn_nhd
        hKc g hg hgc hU hKU hgU) ε hε

end Submission.Helpers
