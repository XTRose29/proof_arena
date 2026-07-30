import Submission.FrontierReduction

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- Complexification of one real-valued member of a smooth partition of
unity. -/
def complexPartitionCutoff
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (i : ι) : ℂ → ℂ :=
  fun z ↦ (χ i z : ℂ)

/-- A complexified smooth partition cutoff is smoothly differentiable. -/
theorem contDiff_complexPartitionCutoff
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (i : ι) :
    ContDiff ℝ ∞ (complexPartitionCutoff χ i) := by
  change ContDiff ℝ ∞
    (Complex.ofRealCLM ∘ fun z : ℂ ↦ χ i z)
  exact Complex.ofRealCLM.contDiff.comp (χ i).contMDiff.contDiff

/-- Complexification cannot enlarge the topological support of a real
partition cutoff. -/
theorem tsupport_complexPartitionCutoff_subset
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (i : ι) :
    tsupport (complexPartitionCutoff χ i) ⊆
      tsupport (fun z : ℂ ↦ χ i z) := by
  change
    tsupport (Complex.ofReal ∘ fun z : ℂ ↦ χ i z) ⊆
      tsupport (fun z : ℂ ↦ χ i z)
  exact
    tsupport_comp_subset Complex.ofReal_zero
      (fun z : ℂ ↦ χ i z)

/-- Subordination to a ball gives compact support after complexification. -/
theorem hasCompactSupport_complexPartitionCutoff_of_subordinate_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (c : ι → ℂ) (r : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (i : ι) :
    HasCompactSupport (complexPartitionCutoff χ i) := by
  have hreal :
      HasCompactSupport (fun z : ℂ ↦ χ i z) := by
    rw [HasCompactSupport]
    exact
      (isCompact_closedBall (c i) r).of_isClosed_subset
        (isClosed_tsupport _)
        ((hχ i).trans Metric.ball_subset_closedBall)
  exact hreal.comp_left Complex.ofReal_zero

/-- The complexified cutoff remains subordinate to the same ball. -/
theorem tsupport_complexPartitionCutoff_subset_ball
    {ι : Type*} {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    (c : ι → ℂ) (r : ℝ)
    (hχ : χ.IsSubordinate (fun i ↦ Metric.ball (c i) r))
    (i : ι) :
    tsupport (complexPartitionCutoff χ i) ⊆
      Metric.ball (c i) r :=
  (tsupport_complexPartitionCutoff_subset χ i).trans (hχ i)

/-- A finite open-ball cover of a compact set admits a smooth subordinate
partition of unity.  The two displayed finite-sum identities avoid carrying
`finsum` through the later Cauchy-integral algebra. -/
theorem exists_smoothPartitionOfUnity_subordinate_balls
    (S : Set ℂ) (hS : IsCompact S)
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (r : ℝ)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) r) :
    ∃ χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S,
      χ.IsSubordinate (fun i ↦ Metric.ball (c i) r) ∧
      (∀ z ∈ S, ∑ i, χ i z = 1) ∧
      (∀ z, ∑ i, χ i z ≤ 1) := by
  obtain ⟨χ, hχ⟩ :=
    SmoothPartitionOfUnity.exists_isSubordinate
      𝓘(ℝ, ℂ) hS.isClosed (fun i ↦ Metric.ball (c i) r)
      (fun _ ↦ Metric.isOpen_ball) hcover
  refine ⟨χ, hχ, ?_, ?_⟩
  · intro z hz
    simpa only [finsum_eq_sum_of_fintype] using
      χ.sum_eq_one hz
  · intro z
    simpa only [finsum_eq_sum_of_fintype] using
      χ.sum_le_one z

/-- On the compact set covered by a finite smooth partition, the
complexified cutoffs also sum to one. -/
theorem sum_complexPartitionCutoff_eq_one
    {ι : Type*} [Fintype ι] {S : Set ℂ}
    (χ : SmoothPartitionOfUnity ι 𝓘(ℝ, ℂ) ℂ S)
    {z : ℂ} (hz : z ∈ S) :
    ∑ i, complexPartitionCutoff χ i z = 1 := by
  have hχ := χ.sum_eq_one hz
  rw [finsum_eq_sum_of_fintype] at hχ
  change ∑ i, (χ i z : ℂ) = 1
  exact_mod_cast hχ

end Submission.Helpers
