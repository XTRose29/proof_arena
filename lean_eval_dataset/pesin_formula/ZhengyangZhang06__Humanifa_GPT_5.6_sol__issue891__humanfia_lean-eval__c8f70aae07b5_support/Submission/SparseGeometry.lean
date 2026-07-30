import Submission.SparseAsymptotics
import Submission.GlobalOrbitGeometry
import Submission.DerivativeDistortion

namespace Submission.Helpers

open LeanEval.Dynamics

/-- Package the three compact-set bounds used by sparse shadowing into one
constant. -/
lemma exists_sparseGeometry
    (T : EucPlane → EucPlane) (hT_smooth : ContDiff ℝ 2 T)
    (K : Set EucPlane) (hK_compact : IsCompact K) :
    ∃ S : Set EucPlane, ∃ M : ℝ,
      K ⊆ S ∧ Convex ℝ S ∧ 1 ≤ M ∧
      (∀ x ∈ K, ∀ y ∈ K,
        dist (T x) (T y) ≤ M * dist x y) ∧
      (∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ M) ∧
      ∀ x ∈ S, ∀ y ∈ S,
        ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ M * dist x y := by
  obtain ⟨radius, hKball⟩ :=
    hK_compact.isBounded.subset_closedBall (0 : EucPlane)
  let S := Metric.closedBall (0 : EucPlane) radius
  obtain ⟨L, hL, hLip⟩ :=
    exists_lipschitz_constant_on_compact T hT_smooth hK_compact
  obtain ⟨D, hD, hDeriv⟩ :=
    compact_fderiv_bound T hT_smooth hK_compact
  obtain ⟨B, hB, hDerivLip⟩ :=
    exists_fderiv_lipschitz_constant_on_compact_convex
      T hT_smooth (isCompact_closedBall (0 : EucPlane) radius)
        (convex_closedBall (0 : EucPlane) radius)
  let M := L + D + B
  have hLM : L ≤ M := by
    dsimp [M]
    linarith
  have hDM : D ≤ M := by
    dsimp [M]
    linarith
  have hBM : B ≤ M := by
    dsimp [M]
    linarith
  refine ⟨S, M, hKball, convex_closedBall _ _, ?_, ?_, ?_, ?_⟩
  · exact hL.trans hLM
  · intro x hx y hy
    exact (hLip x hx y hy).trans
      (mul_le_mul_of_nonneg_right hLM dist_nonneg)
  · intro x hx
    exact (hDeriv x hx).trans hDM
  · intro x hx y hy
    exact (hDerivLip x hx y hy).trans
      (mul_le_mul_of_nonneg_right hBM dist_nonneg)

end Submission.Helpers
