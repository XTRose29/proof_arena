import ChallengeDeps
import Submission.Helpers

open LeanEval.Geometry.KoszulFormula
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem koszul_formula {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
      [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
      [IsManifold I ∞ M]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    [ContMDiffCovariantDerivative cov ∞]
    (_htor : cov.torsion = 0) (_hmet : IsMetricCompatible cov)
    (X Y Z : Π x : M, TangentSpace I x)
    (_hX : CMDiff ∞ (T% X)) (_hY : CMDiff ∞ (T% Y)) (_hZ : CMDiff ∞ (T% Z))
    (x : M) :
    2 * inner ℝ (cov Y x (X x)) (Z x) =
      mvfderiv I (fun y : M => inner ℝ (Y y) (Z y)) x (X x)
      + mvfderiv I (fun y : M => inner ℝ (X y) (Z y)) x (Y x)
      - mvfderiv I (fun y : M => inner ℝ (X y) (Y y)) x (Z x)
      - inner ℝ (X x) (mlieBracket I Y Z x)
      - inner ℝ (Y x) (mlieBracket I X Z x)
      + inner ℝ (Z x) (mlieBracket I X Y x) := by
  -- metric compatibility in the three cyclic positions
  have hm1 := _hmet Y Z _hY _hZ x (X x)
  have hm2 := _hmet X Z _hX _hZ x (Y x)
  have hm3 := _hmet X Y _hX _hY x (Z x)
  -- differentiability of our smooth fields, for using the torsion formula
  have hXd : MDiffAt (T% X) x :=
    (_hX.contMDiffAt).mdifferentiableAt (by simp)
  have hYd : MDiffAt (T% Y) x :=
    (_hY.contMDiffAt).mdifferentiableAt (by simp)
  have hZd : MDiffAt (T% Z) x :=
    (_hZ.contMDiffAt).mdifferentiableAt (by simp)
  have htXY : cov Y x (X x) - cov X x (Y x) = mlieBracket I X Y x :=
    (CovariantDerivative.torsion_eq_zero_iff cov).mp _htor hXd hYd
  have htXZ : cov Z x (X x) - cov X x (Z x) = mlieBracket I X Z x :=
    (CovariantDerivative.torsion_eq_zero_iff cov).mp _htor hXd hZd
  have htYZ : cov Z x (Y x) - cov Y x (Z x) = mlieBracket I Y Z x :=
    (CovariantDerivative.torsion_eq_zero_iff cov).mp _htor hYd hZd
  -- insert the three metric identities and the torsion identities; the rest is
  -- bilinearity and symmetry of the metric.
  rw [hm1, hm2, hm3]
  rw [← htYZ, ← htXZ, ← htXY]
  -- expand inner products against differences
  simp only [inner_sub_right]
  -- the metric is symmetric and the remaining claim is an identity in `ℝ`
  -- after identifying the symmetric pairs.
  simp only [real_inner_comm]
  ring


end Submission
