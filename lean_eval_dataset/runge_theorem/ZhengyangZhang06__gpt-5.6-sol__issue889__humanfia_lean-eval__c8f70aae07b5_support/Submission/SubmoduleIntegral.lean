import Submission.RationalMaps

open Set MeasureTheory

noncomputable section

namespace Submission.Helpers

lemma integral_mem_submodule_closure
    {α E : Type*} {mα : MeasurableSpace α} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedSpace ℂ E] [CompleteSpace E]
    (S : Submodule ℂ E) {F : α → E} {μ : Measure α}
    (hF : Integrable F μ) (hmem : ∀ x, F x ∈ S.closure) :
    (∫ x, F x ∂μ) ∈ S.closure := by
  let T : Submodule ℝ E := S.closure.toSubmodule.restrictScalars ℝ
  letI : IsClosed (T : Set E) := S.closure.isClosed'
  let L : E →L[ℝ] E ⧸ T := T.mkQL
  change (∫ x, F x ∂μ) ∈ T
  rw [← Submodule.Quotient.mk_eq_zero T]
  change L (∫ x, F x ∂μ) = 0
  rw [← L.integral_comp_comm hF]
  have hz : (fun x => L (F x)) = 0 := by
    funext x
    exact (Submodule.Quotient.mk_eq_zero T).2 (hmem x)
  rw [hz]
  simp

end Submission.Helpers
