import Mathlib.Analysis.Calculus.BumpFunction.Basic
import Submission.FrontierPartition

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- The standard bump centered at `c`, equal to one on the radius-`3r/2`
closed ball and supported in the radius-`2r` open ball.  The small gap is
chosen so that support intersections of bumps whose radius-`r` closed balls
are disjoint reduce to the library's unit-separated packing estimate. -/
def uniformContDiffBump
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ContDiffBump c where
  rIn := 3 * r / 2
  rOut := 2 * r
  rIn_pos := by positivity
  rIn_lt_rOut := by linarith

/-- A finite cover by radius-`3r/2` balls, realized by the explicit
uniform smooth bumps above. -/
def uniformBumpCovering
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2)) :
    BumpCovering ι ℂ S where
  toFun i :=
    ⟨uniformContDiffBump (c i) r hr,
      (uniformContDiffBump (c i) r hr).continuous⟩
  locallyFinite' :=
    locallyFinite_of_finite
      (fun i ↦ support (uniformContDiffBump (c i) r hr))
  nonneg' i z :=
    (uniformContDiffBump (c i) r hr).nonneg
  le_one' i z :=
    (uniformContDiffBump (c i) r hr).le_one
  eventuallyEq_one' z hz := by
    obtain ⟨i, hzi⟩ :=
      mem_iUnion.mp (hcover hz)
    refine ⟨i, ?_⟩
    change
      (uniformContDiffBump (c i) r hr : ℂ → ℝ) =ᶠ[𝓝 z]
        (1 : ℂ → ℝ)
    exact
      (uniformContDiffBump (c i) r hr).eventuallyEq_one_of_mem_ball hzi

/-- The smooth partition obtained by applying Mathlib's sequential
partition construction to the uniform bump covering. -/
def uniformSmoothPartition
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2)) :
    SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S :=
  (uniformBumpCovering S c r hr hcover).toSmoothPartitionOfUnity fun i ↦
    by
      change
        ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
          (uniformContDiffBump (c i) r hr)
      exact
        ((uniformContDiffBump (c i) r hr).contDiff :
          ContDiff ℝ ∞ (uniformContDiffBump (c i) r hr)).contMDiff

/-- The explicit partition is subordinate to the radius-`3r` balls.  Its
raw bumps have closed support of radius `2r`, and the sequential
partition construction only shrinks supports. -/
theorem uniformSmoothPartition_isSubordinate
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2)) :
    (uniformSmoothPartition S c r hr hcover).IsSubordinate
      (fun i ↦ Metric.ball (c i) (3 * r)) := by
  have hsub :
      (uniformBumpCovering S c r hr hcover).IsSubordinate
        (fun i ↦ Metric.ball (c i) (3 * r)) := by
    intro i
    change
      tsupport (uniformContDiffBump (c i) r hr) ⊆
        Metric.ball (c i) (3 * r)
    rw [ContDiffBump.tsupport_eq]
    change
      Metric.closedBall (c i) (2 * r) ⊆
        Metric.ball (c i) (3 * r)
    exact Metric.closedBall_subset_ball (by linarith)
  simpa only [uniformSmoothPartition] using
    hsub.toSmoothPartitionOfUnity
      (fun i ↦ by
        change
          ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℝ) ∞
            (uniformContDiffBump (c i) r hr)
        exact
          ((uniformContDiffBump (c i) r hr).contDiff :
            ContDiff ℝ ∞
              (uniformContDiffBump (c i) r hr)).contMDiff)

end Submission.Helpers
