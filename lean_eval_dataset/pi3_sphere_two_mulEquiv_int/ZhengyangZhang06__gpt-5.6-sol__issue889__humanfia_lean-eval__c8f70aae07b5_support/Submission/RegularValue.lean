import Mathlib

open MeasureTheory Metric Set

noncomputable section

namespace Submission.RegularValue

variable {E : Type*}
variable [NormedAddCommGroup E] [InnerProductSpace ℝ E]
variable [FiniteDimensional ℝ E]

/-- A `C¹` self-map of a finite-dimensional real inner-product space has
regular values arbitrarily close to the origin. -/
theorem exists_regular_value_in_ball
    (f : E → E) (hf : ContDiff ℝ 1 f) {r : ℝ} (hr : 0 < r) :
    ∃ y ∈ ball (0 : E) r,
      ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0 := by
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  let critical : Set E := {x | (fderiv ℝ f x).det = 0}
  let μ : Measure E := Measure.addHaar
  have hcritical : μ (f '' critical) = 0 := by
    apply addHaar_image_eq_zero_of_det_fderivWithin_eq_zero μ
      (f' := fun x => fderiv ℝ f x)
    · intro x _
      exact (hf.differentiable (by norm_num) x).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hx
  have hnotSubset : ¬ball (0 : E) r ⊆ f '' critical := by
    intro hsubset
    have hle : μ (ball (0 : E) r) ≤ μ (f '' critical) :=
      measure_mono hsubset
    rw [hcritical] at hle
    exact (not_le_of_gt (measure_ball_pos μ 0 hr)) hle
  obtain ⟨y, hy, hycritical⟩ := not_subset.mp hnotSubset
  refine ⟨y, hy, fun x hxy hdet => hycritical ?_⟩
  exact ⟨x, hdet, hxy⟩

/-- A compact set contains only finitely many points of a regular fiber of a
`C¹` self-map. -/
theorem finite_regular_fiber_inter
    (f : E → E) (hf : ContDiff ℝ 1 f) (y : E)
    (hy : ∀ x, f x = y → (fderiv ℝ f x).det ≠ 0)
    (K : Set E) (hK : IsCompact K) :
    (K ∩ f ⁻¹' {y}).Finite := by
  have hcompact : IsCompact (K ∩ f ⁻¹' {y}) :=
    hK.inter_right (isClosed_singleton.preimage hf.continuous)
  apply hcompact.finite
  apply IsDiscrete.of_openPartialHomeomorph f inter_subset_right
  intro x hx
  have hxy : f x = y := hx.2
  let f' : E ≃L[ℝ] E :=
    (fderiv ℝ f x).toContinuousLinearEquivOfDetNeZero (hy x hxy)
  have hderiv : HasFDerivAt f (f' : E →L[ℝ] E) x := by
    simpa [f'] using (hf.differentiable (by norm_num) x).hasFDerivAt
  let e :=
    hf.contDiffAt.toOpenPartialHomeomorph f hderiv (by norm_num)
  refine ⟨e, ?_, ?_⟩
  · exact hf.contDiffAt.mem_toOpenPartialHomeomorph_source hderiv (by norm_num)
  · exact hf.contDiffAt.toOpenPartialHomeomorph_coe hderiv (by norm_num)

end Submission.RegularValue
