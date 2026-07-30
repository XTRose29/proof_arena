import Mathlib
import Submission.Integration

open Set
open scoped Polynomial Topology

namespace Submission

theorem runge (K : Set ℂ) (hK : IsCompact K) (U : Set ℂ) (hU : IsOpen U)
    (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ p q : ℂ[X], (∀ z ∈ K, q.eval z ≠ 0) ∧
      (∀ z ∈ K, ‖f z - p.eval z / q.eval z‖ < ε) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let F : C(K, ℂ) :=
    ⟨fun z => f z, hf.continuousOn.comp_continuous continuous_subtype_val
      (fun z => hKU z.property)⟩
  have hF : F ∈ (Helpers.rationalMaps K).closure :=
    Helpers.analytic_restriction_mem_rationalMaps_closure K U hK hU hKU f hf
  change F ∈ closure (Helpers.rationalMaps K : Set C(K, ℂ)) at hF
  obtain ⟨r, hr, hdist⟩ := (Metric.mem_closure_iff.mp hF) ε hε
  obtain ⟨p, q, hq, hrational⟩ := hr
  refine ⟨p, q, fun z hz => hq ⟨z, hz⟩, ?_⟩
  intro z hz
  have hpoint :
      ‖F ⟨z, hz⟩ - r ⟨z, hz⟩‖ ≤ ‖F - r‖ :=
    ContinuousMap.norm_coe_le_norm (F - r) ⟨z, hz⟩
  have hpoint' : ‖F ⟨z, hz⟩ - r ⟨z, hz⟩‖ < ε :=
    hpoint.trans_lt (by simpa only [dist_eq_norm] using hdist)
  simpa only [F, ContinuousMap.coe_mk, hrational ⟨z, hz⟩] using hpoint'

end Submission
