import Submission.CenteredMoment
import Submission.VariablePartition

open Function Set
open scoped ContDiff Manifold Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- Integration by parts transfers a centered-moment error from the
partitioned original defect to the signed correction density.  The only
remaining term is the explicit pointwise localization residual. -/
theorem partitionedCrDefect_sub_centeredMoment_eq_correction
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hg : ContDiff ℝ ∞ g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R) (i : ι) (a z : ℂ) :
    (∫ w : ℂ,
        (w - z)⁻¹ *
          (partitionedCutoff χ ψ i w * crDefect g w)) -
        centeredMomentModel a (c i)
          (∫ w : ℂ,
            partitionedCutoff χ ψ i w * crDefect g w)
          (∫ w : ℂ,
            (w - a) *
              (partitionedCutoff χ ψ i w * crDefect g w))
          z =
      ((∫ w : ℂ,
          (w - z)⁻¹ *
            frontierCorrectionDensity χ ψ g b i w) -
        centeredMomentModel a (c i)
          (∫ w : ℂ,
            frontierCorrectionDensity χ ψ g b i w)
          (∫ w : ℂ,
            (w - a) *
              frontierCorrectionDensity χ ψ g b i w)
          z) -
        (2 * Real.pi * Complex.I : ℂ) *
          (partitionedCutoff χ ψ i z * (g z - b i)) := by
  rw [
    integral_cauchyKernel_mul_frontierCorrectionDensity_eq_localized_variable
      χ ψ g c b r R hψ hg hχ hrR i z,
    integral_frontierCorrectionDensity_eq_localized_crDefect_variable
      χ ψ g c b r R hψ hg hχ hrR i,
    integral_sub_mul_frontierCorrectionDensity_eq_localized_crDefect_variable
      χ ψ g c b r R hψ hg hχ hrR i a]
  ring

/-- Centered-moment endpoint for a variable-radius frontier partition.
The sole quantitative hypothesis compares each localized Cauchy transform
with a cubic-corrected moment model which vanishes at its geometric center.
All model terms already lie in the closed polynomial algebra. -/
theorem exists_polynomial_approx_of_partitionedCrDefectCenteredAggregate_variable
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (ψ g : ℂ → ℂ) (c b a : ι → ℂ) (r : ι → ℝ) (R : ℝ)
    (hψ : ContDiff ℝ ∞ ψ) (hψc : HasCompactSupport ψ)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) (r i)))
    (hrR : ∀ i, r i ≤ R)
    (hnearS :
      tsupport (fun w ↦ ψ w * crDefect g w) ⊆ S)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (ha : ∀ i, a i ∉ K)
    (ε : ℝ) (hε : 0 < ε)
    (haggregate :
      ∀ z : K,
        ‖∑ i,
            ((∫ w : ℂ,
                (w - (z : ℂ))⁻¹ *
                  (partitionedCutoff χ ψ i w *
                    crDefect g w)) -
              centeredMomentModel
                (a i) (c i)
                (∫ w : ℂ,
                  partitionedCutoff χ ψ i w *
                    crDefect g w)
                (∫ w : ℂ,
                  (w - a i) *
                    (partitionedCutoff χ ψ i w *
                      crDefect g w))
                (z : ℂ))‖ <
          ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  let q : ι → ℂ → ℂ :=
    fun i w ↦ partitionedCutoff χ ψ i w * crDefect g w
  let m₀ : ι → ℂ := fun i ↦ ∫ w : ℂ, q i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ, (w - a i) * q i w
  obtain ⟨u, hu⟩ :=
    exists_centeredMomentModelSum_mem_polynomialClosure
      hKc a c m₀ m₁ ha
  apply exists_polynomial_approx_of_frontierDefectMap_approx
    hKc g ψ hg hgc hψ hdisj ε hε u
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [(frontierDefectMap g ψ hg hdisj -
      (u : C(K, ℂ))).norm_lt_iff
    (mul_pos (norm_pos_iff.mpr hc) (half_pos hε))]
  intro z
  change
    ‖frontierDefectMap g ψ hg hdisj z -
        (u : C(K, ℂ)) z‖ <
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)
  rw [
    frontierDefectMap_eq_partitioned_crDefect_integral_sum_variable
      χ ψ g c b r R hψ hψc hg hgc hχ hrR hnearS hdisj z,
    hu z]
  dsimp only [m₀, m₁, q]
  rw [← Finset.sum_sub_distrib]
  exact haggregate z

end Submission.Helpers
