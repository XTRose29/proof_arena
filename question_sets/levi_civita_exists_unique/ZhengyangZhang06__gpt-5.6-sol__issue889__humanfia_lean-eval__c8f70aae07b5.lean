import ChallengeDeps
import Submission.Regularity

open LeanEval.Geometry.LeviCivita
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

namespace Submission

theorem levi_civita_exists_unique {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] :
    ∃ cov : CovariantDerivative I E (TangentSpace I (M := M)),
      (ContMDiffCovariantDerivative cov ∞ ∧
        cov.torsion = 0 ∧ IsMetricCompatible cov) ∧
      ∀ cov' : CovariantDerivative I E (TangentSpace I (M := M)),
        (ContMDiffCovariantDerivative cov' ∞ ∧
          cov'.torsion = 0 ∧ IsMetricCompatible cov') →
        SameOnSmooth cov cov' := by
  refine ⟨Helpers.koszulCovariantDerivative, ?_, ?_⟩
  · exact ⟨Helpers.koszulCovariantDerivative_contMDiff,
      Helpers.koszulCovariantDerivative_torsion,
      Helpers.koszulCovariantDerivative_metricCompatible⟩
  · intro cov' hcov'
    exact Helpers.koszulCovariantDerivative_unique cov' hcov'.2.1 hcov'.2.2

end Submission
