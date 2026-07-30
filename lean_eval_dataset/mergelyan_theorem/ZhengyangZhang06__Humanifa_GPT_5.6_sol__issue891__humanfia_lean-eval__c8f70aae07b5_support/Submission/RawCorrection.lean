import Submission.CenteredAggregate

open Function Set
open scoped ContDiff Manifold Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- The part of a localized integration-by-parts correction containing
only the derivative of the partition member. -/
def rawPartitionCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ) (i : ι) (z : ℂ) : ℂ :=
  -((g z - b i) *
    (ψ z * crDefect (complexPartitionCutoff χ i) z))

/-- The complementary part of a localized correction, containing the
derivative of the common frontier cutoff. -/
def cutoffDerivativeCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ) (i : ι) (z : ℂ) : ℂ :=
  -((g z - b i) *
    (complexPartitionCutoff χ i z * crDefect ψ z))

/-- Leibniz' rule splits the full correction into the partition-derivative
part and the common-cutoff-derivative part. -/
theorem frontierCorrectionDensity_eq_raw_add_cutoffDerivative
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (i : ι) (z : ℂ) :
    frontierCorrectionDensity χ ψ g b i z =
      rawPartitionCorrectionDensity χ ψ g b i z +
        cutoffDerivativeCorrectionDensity χ ψ g b i z := by
  unfold frontierCorrectionDensity rawPartitionCorrectionDensity
    cutoffDerivativeCorrectionDensity partitionedCutoff
  rw [
    crDefect_mul
      ((contDiff_complexPartitionCutoff χ i).differentiable
        (by simp)).differentiableAt
      (hψ.differentiable (by simp)).differentiableAt]
  ring

/-- A raw partition correction is continuous. -/
theorem continuous_rawPartitionCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (i : ι) :
    Continuous (rawPartitionCorrectionDensity χ ψ g b i) := by
  exact
    ((hg.continuous.sub continuous_const).mul
      (hψ.continuous.mul
        (continuous_crDefect _
          (contDiff_complexPartitionCutoff χ i)))).neg

/-- A raw partition correction stays compactly supported in the support of
the corresponding partition member. -/
theorem hasCompactSupport_rawPartitionCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    HasCompactSupport
      (rawPartitionCorrectionDensity χ ψ g b i) := by
  have hχc :
      HasCompactSupport (complexPartitionCutoff χ i) :=
    hasCompactSupport_complexPartitionCutoff_of_subordinate_variable_ball
      χ c r hχ i
  have hDχc :
      HasCompactSupport
        (crDefect (complexPartitionCutoff χ i)) :=
    crDefect_hasCompactSupport _ hχc
  exact ((hDχc.mul_left).mul_left).comp_left neg_zero

/-- A common-cutoff derivative correction is continuous. -/
theorem continuous_cutoffDerivativeCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (i : ι) :
    Continuous (cutoffDerivativeCorrectionDensity χ ψ g b i) := by
  exact
    ((hg.continuous.sub continuous_const).mul
      ((contDiff_complexPartitionCutoff χ i).continuous.mul
        (continuous_crDefect ψ hψ))).neg

/-- A common-cutoff derivative correction is compactly supported by its
partition member. -/
theorem hasCompactSupport_cutoffDerivativeCorrectionDensity
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) :
    HasCompactSupport
      (cutoffDerivativeCorrectionDensity χ ψ g b i) := by
  have hχc :
      HasCompactSupport (complexPartitionCutoff χ i) :=
    hasCompactSupport_complexPartitionCutoff_of_subordinate_variable_ball
      χ c r hχ i
  exact ((hχc.mul_right).mul_left).comp_left neg_zero

/-- The full correction transform is the sum of the two correction
transforms supplied by the Leibniz split. -/
theorem integral_frontierCorrectionDensity_eq_raw_add_cutoffDerivative
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (i : ι) (z : ℂ) :
    (∫ w : ℂ,
        (w - z)⁻¹ *
          frontierCorrectionDensity χ ψ g b i w) =
      (∫ w : ℂ,
        (w - z)⁻¹ *
          rawPartitionCorrectionDensity χ ψ g b i w) +
      ∫ w : ℂ,
        (w - z)⁻¹ *
          cutoffDerivativeCorrectionDensity χ ψ g b i w := by
  have hraw :
      MeasureTheory.Integrable
        (fun w : ℂ ↦
          (w - z)⁻¹ *
            rawPartitionCorrectionDensity χ ψ g b i w) :=
    integrable_cauchyKernel_mul_continuous_compact _
      (continuous_rawPartitionCorrectionDensity
        χ ψ g b hψ hg i)
      (hasCompactSupport_rawPartitionCorrectionDensity
        χ ψ g c b r hχ i) z
  have hcutoff :
      MeasureTheory.Integrable
        (fun w : ℂ ↦
          (w - z)⁻¹ *
            cutoffDerivativeCorrectionDensity χ ψ g b i w) :=
    integrable_cauchyKernel_mul_continuous_compact _
      (continuous_cutoffDerivativeCorrectionDensity
        χ ψ g b hψ hg i)
      (hasCompactSupport_cutoffDerivativeCorrectionDensity
        χ ψ g c b r hχ i) z
  calc
    (∫ w : ℂ,
        (w - z)⁻¹ *
          frontierCorrectionDensity χ ψ g b i w) =
      ∫ w : ℂ,
        ((w - z)⁻¹ *
            rawPartitionCorrectionDensity χ ψ g b i w) +
          ((w - z)⁻¹ *
            cutoffDerivativeCorrectionDensity χ ψ g b i w) := by
      apply MeasureTheory.integral_congr_ae
      filter_upwards with w
      rw [frontierCorrectionDensity_eq_raw_add_cutoffDerivative
        χ ψ g b hψ i w]
      ring
    _ = _ := MeasureTheory.integral_add hraw hcutoff

/-- The finite aggregate of common-cutoff derivative corrections. -/
def cutoffDerivativeCorrectionDensitySum
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ) (z : ℂ) : ℂ :=
  ∑ i, cutoffDerivativeCorrectionDensity χ ψ g b i z

/-- The cutoff-derivative aggregate is continuous. -/
theorem continuous_cutoffDerivativeCorrectionDensitySum
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g) :
    Continuous (cutoffDerivativeCorrectionDensitySum χ ψ g b) := by
  classical
  exact continuous_finsetSum _ fun i _ ↦
    continuous_cutoffDerivativeCorrectionDensity
      χ ψ g b hψ hg i

/-- The cutoff-derivative aggregate has compact support. -/
theorem hasCompactSupport_cutoffDerivativeCorrectionDensitySum
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i))) :
    HasCompactSupport
      (cutoffDerivativeCorrectionDensitySum χ ψ g b) := by
  classical
  have heq :
      cutoffDerivativeCorrectionDensitySum χ ψ g b =
        ∑ i, cutoffDerivativeCorrectionDensity χ ψ g b i := by
    funext z
    simp only [cutoffDerivativeCorrectionDensitySum,
      Finset.sum_apply]
  rw [heq]
  exact HasCompactSupport.finset_sum fun i _ ↦
    hasCompactSupport_cutoffDerivativeCorrectionDensity
      χ ψ g c b r hχ i

/-- The aggregate common-cutoff correction is supported where the
Cauchy--Riemann defect of the common cutoff is supported. -/
theorem tsupport_cutoffDerivativeCorrectionDensitySum_subset
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (b : ι → ℂ) :
    tsupport (cutoffDerivativeCorrectionDensitySum χ ψ g b) ⊆
      tsupport (crDefect ψ) := by
  classical
  rw [tsupport, tsupport]
  apply closure_mono
  intro z hz
  contrapose! hz
  have hzero : crDefect ψ z = 0 :=
    Function.notMem_support.mp hz
  simp [cutoffDerivativeCorrectionDensitySum,
    cutoffDerivativeCorrectionDensity, hzero]

/-- If the common cutoff is locally constant near `K`, its derivative
correction contributes an exact element of the closed polynomial algebra. -/
theorem cutoffDerivativeCorrectionMap_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hDψ :
      Disjoint (tsupport (crDefect ψ)) K) :
    (∫ w : ℂ,
      cauchyDensityMap K
        (cutoffDerivativeCorrectionDensitySum χ ψ g b)
        (hDψ.mono_left
          (tsupport_cutoffDerivativeCorrectionDensitySum_subset
            χ ψ g b)) w) ∈
      (polynomialFunctions K).topologicalClosure := by
  apply cauchyDensityIntegral_mem_polynomialClosure hKc
  · exact continuous_cutoffDerivativeCorrectionDensitySum
      χ ψ g b hψ hg
  · exact hasCompactSupport_cutoffDerivativeCorrectionDensitySum
      χ ψ g c b r hχ

/-- Endpoint for the raw/cutoff split.  The aggregate cutoff-derivative
transform is already in the closed polynomial algebra.  Thus it suffices
to approximate the sum of raw correction transforms by any finite family
of closed-algebra elements; in particular, those elements may be the
near/far regularized moment models. -/
theorem exists_polynomial_approx_of_rawCorrectionAggregate
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (hDψ : Disjoint (tsupport (crDefect ψ)) K)
    (u : ι →
      (polynomialFunctions K).topologicalClosure)
    (e₀ e₁ : ℝ) (he₁ : 0 ≤ e₁)
    (hres :
      ‖frontierLocalizationResidualMap (K := K)
          χ ψ g b hψ hg‖ ≤ e₀)
    (hraw :
      ∀ z : K,
        ‖∑ i,
            ((∫ w : ℂ,
                (w - (z : ℂ))⁻¹ *
                  rawPartitionCorrectionDensity χ ψ g b i w) -
              (u i : C(K, ℂ)) z)‖ ≤ e₁)
    (ε : ℝ) (hε : 0 < ε)
    (herror :
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * e₀ + e₁ <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  let qcut : ℂ → ℂ :=
    cutoffDerivativeCorrectionDensitySum χ ψ g b
  have hqcutContinuous : Continuous qcut :=
    continuous_cutoffDerivativeCorrectionDensitySum
      χ ψ g b hψ hg
  have hqcutCompact : HasCompactSupport qcut :=
    hasCompactSupport_cutoffDerivativeCorrectionDensitySum
      χ ψ g c b (fun _ ↦ r) hχ
  have hqcutSupport :
      tsupport qcut ⊆ tsupport (crDefect ψ) :=
    tsupport_cutoffDerivativeCorrectionDensitySum_subset
      χ ψ g b
  have hqcutDisj : Disjoint (tsupport qcut) K :=
    hDψ.mono_left hqcutSupport
  let Tcut : C(K, ℂ) :=
    ∫ w : ℂ, cauchyDensityMap K qcut hqcutDisj w
  have hTcutMem :
      Tcut ∈ (polynomialFunctions K).topologicalClosure := by
    dsimp only [Tcut]
    exact cauchyDensityIntegral_mem_polynomialClosure
      hKc qcut hqcutContinuous hqcutCompact hqcutDisj
  let v :
      (polynomialFunctions K).topologicalClosure :=
    ⟨Tcut, hTcutMem⟩
  have hcutIntegrable (i : ι) (z : K) :
      MeasureTheory.Integrable
        (fun w : ℂ ↦
          (w - (z : ℂ))⁻¹ *
            cutoffDerivativeCorrectionDensity χ ψ g b i w) :=
    integrable_cauchyKernel_mul_continuous_compact _
      (continuous_cutoffDerivativeCorrectionDensity
        χ ψ g b hψ hg i)
      (hasCompactSupport_cutoffDerivativeCorrectionDensity
        χ ψ g c b (fun _ ↦ r) hχ i) z
  have hTcutApply (z : K) :
      (v : C(K, ℂ)) z =
        ∑ i, ∫ w : ℂ,
          (w - (z : ℂ))⁻¹ *
            cutoffDerivativeCorrectionDensity χ ψ g b i w := by
    change
      (∫ w : ℂ, cauchyDensityMap K qcut hqcutDisj w) z = _
    rw [ContinuousMap.integral_apply
      (integrable_cauchyDensityMap
        qcut hqcutContinuous hqcutCompact hqcutDisj)]
    simp only [cauchyDensityMap_apply]
    calc
      (∫ w : ℂ, (w - (z : ℂ))⁻¹ * qcut w) =
          ∫ w : ℂ, ∑ i,
            (w - (z : ℂ))⁻¹ *
              cutoffDerivativeCorrectionDensity χ ψ g b i w := by
        apply MeasureTheory.integral_congr_ae
        filter_upwards with w
        change
          (w - (z : ℂ))⁻¹ *
              cutoffDerivativeCorrectionDensitySum χ ψ g b w =
            ∑ i,
              (w - (z : ℂ))⁻¹ *
                cutoffDerivativeCorrectionDensity χ ψ g b i w
        rw [cutoffDerivativeCorrectionDensitySum,
          Finset.mul_sum]
      _ = _ := by
        simpa only using
          MeasureTheory.integral_finsetSum Finset.univ
            (fun i _hi ↦ hcutIntegrable i z)
  let U :
      (polynomialFunctions K).topologicalClosure :=
    v + ∑ i, u i
  have hcorrection (z : K) :
      frontierCorrectionMap χ ψ g b hψ hg hdisj z =
        (v : C(K, ℂ)) z +
          ∑ i, ∫ w : ℂ,
            (w - (z : ℂ))⁻¹ *
              rawPartitionCorrectionDensity χ ψ g b i w := by
    rw [frontierCorrectionMap_eq_integral_sum
      χ ψ g c b r hψ hψc hg hgc hχ hnearS hdisj z]
    calc
      (∑ i, ∫ w : ℂ,
          (w - (z : ℂ))⁻¹ *
            frontierCorrectionDensity χ ψ g b i w) =
          ∑ i,
            ((∫ w : ℂ,
                (w - (z : ℂ))⁻¹ *
                  rawPartitionCorrectionDensity χ ψ g b i w) +
              ∫ w : ℂ,
                (w - (z : ℂ))⁻¹ *
                  cutoffDerivativeCorrectionDensity χ ψ g b i w) := by
        apply Finset.sum_congr rfl
        intro i _hi
        exact
          integral_frontierCorrectionDensity_eq_raw_add_cutoffDerivative
            χ ψ g c b (fun _ ↦ r) hψ hg hχ i (z : ℂ)
      _ = (∑ i, ∫ w : ℂ,
              (w - (z : ℂ))⁻¹ *
                rawPartitionCorrectionDensity χ ψ g b i w) +
            ∑ i, ∫ w : ℂ,
              (w - (z : ℂ))⁻¹ *
                cutoffDerivativeCorrectionDensity χ ψ g b i w := by
        rw [Finset.sum_add_distrib]
      _ = _ := by
        rw [← hTcutApply z]
        ring
  have hcorrectionU :
      ‖frontierCorrectionMap χ ψ g b hψ hg hdisj -
          (U : C(K, ℂ))‖ ≤ e₁ := by
    rw [(frontierCorrectionMap χ ψ g b hψ hg hdisj -
      (U : C(K, ℂ))).norm_le he₁]
    intro z
    change
      ‖frontierCorrectionMap χ ψ g b hψ hg hdisj z -
          (U : C(K, ℂ)) z‖ ≤ e₁
    rw [hcorrection z]
    change
      ‖(v : C(K, ℂ)) z +
          (∑ i, ∫ w : ℂ,
            (w - (z : ℂ))⁻¹ *
              rawPartitionCorrectionDensity χ ψ g b i w) -
        ((v : C(K, ℂ)) z +
          ((polynomialFunctions K).topologicalClosure.val
            (∑ i, u i)) z)‖ ≤ e₁
    rw [map_sum, ContinuousMap.sum_apply]
    calc
      ‖(v : C(K, ℂ)) z +
          (∑ i, ∫ w : ℂ,
            (w - (z : ℂ))⁻¹ *
              rawPartitionCorrectionDensity χ ψ g b i w) -
        ((v : C(K, ℂ)) z +
          ∑ i,
            ((polynomialFunctions K).topologicalClosure.val
              (u i)) z)‖ =
          ‖(∑ i, ∫ w : ℂ,
              (w - (z : ℂ))⁻¹ *
                rawPartitionCorrectionDensity χ ψ g b i w) -
            ∑ i,
              ((polynomialFunctions K).topologicalClosure.val
                (u i)) z‖ := by
        congr 1
        ring
      _ = ‖∑ i,
          ((∫ w : ℂ,
              (w - (z : ℂ))⁻¹ *
                rawPartitionCorrectionDensity χ ψ g b i w) -
            (u i : C(K, ℂ)) z)‖ := by
        rw [← Finset.sum_sub_distrib]
        rfl
      _ ≤ e₁ :=
        hraw z
  apply exists_polynomial_approx_of_frontierDefectMap_approx
    hKc g ψ hg hgc hψ hdisj ε hε U
  calc
    ‖frontierDefectMap g ψ hg hdisj - (U : C(K, ℂ))‖ =
        ‖(frontierDefectMap g ψ hg hdisj -
            frontierCorrectionMap χ ψ g b hψ hg hdisj) +
          (frontierCorrectionMap χ ψ g b hψ hg hdisj -
            (U : C(K, ℂ)))‖ := by
      congr 1
      ring
    _ ≤
        ‖frontierDefectMap g ψ hg hdisj -
            frontierCorrectionMap χ ψ g b hψ hg hdisj‖ +
          ‖frontierCorrectionMap χ ψ g b hψ hg hdisj -
            (U : C(K, ℂ))‖ :=
      norm_add_le _ _
    _ ≤ ‖(2 * Real.pi * Complex.I : ℂ)‖ * e₀ + e₁ := by
      exact add_le_add
        (norm_frontierDefectMap_sub_frontierCorrectionMap_le
          χ ψ g b hψ hg hdisj e₀ hres)
        hcorrectionU
    _ < ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2) :=
      herror

end Submission.Helpers
