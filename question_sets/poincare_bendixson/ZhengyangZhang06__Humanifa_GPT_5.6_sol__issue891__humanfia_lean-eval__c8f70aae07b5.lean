import ChallengeDeps
import Submission.Helpers
import Submission.OmegaSectionUnique
import Submission.PeriodicBranch
import Submission.PlanarReduction

open LeanEval.Dynamics
open Filter Metric Topology Set
open scoped NNReal

namespace Submission

theorem poincare_bendixson (F : Plane → Plane) (hF : ContDiff ℝ 1 F)
    (γ : ℝ → Plane)
    (hγ : IsIntegralCurveOn γ (fun _ x => F x) (Set.Ici 0)) :
    ¬ Bornology.IsBounded (γ '' Set.Ici 0)
    ∨ (∃ x₀, F x₀ = 0 ∧ x₀ ∈ ⋂ s : ℝ, closure (γ '' Set.Ici s))
    ∨ (∃ T : ℝ, 0 < T ∧ ∃ β : ℝ → Plane,
        IsIntegralCurve β (fun _ x => F x) ∧
        (∀ t, β (t + T) = β t) ∧
        F (β 0) ≠ 0 ∧
        (⋂ s : ℝ, closure (γ '' Set.Ici s)) = Set.range β) := by
  by_cases hbounded : Bornology.IsBounded (γ '' Ici (0 : ℝ))
  · right
    by_cases hγinj : InjOn γ (Ici (0 : ℝ))
    · obtain ⟨G, K, hGcompact, hGdiff, hG, hEq⟩ :=
        Helpers.exists_compactlySupported_lipschitz_extension
          F hF hbounded
      obtain ⟨Φ, hΦ0, hΦ⟩ :=
        GlobalFlow.exists_globalFlow G hGcompact hGdiff
      let A : Set Plane := Helpers.omegaSet γ
      have hAcompact : IsCompact A :=
        Helpers.isCompact_omegaSet γ hbounded
      have hAne : A.Nonempty :=
        Helpers.omegaSet_nonempty γ hbounded
      have hApre : IsPreconnected A :=
        Helpers.isPreconnected_omegaSet γ hγ.continuousOn hbounded
      have hAinv : ∀ x ∈ A, ∀ t : ℝ, Φ x t ∈ A := by
        intro x hx t
        exact
          OmegaInvariant.mem_omegaSet hG γ (Φ x)
            hγ hEq (hΦ x) (hΦ0 x) hx t
      have hGF : EqOn G F A := by
        intro x hx
        exact
          (hEq.closure hGdiff.continuous hF.continuous)
            (Helpers.omegaSet_subset_closure_image_Ici γ 0 hx)
      by_cases hzero : ∃ x ∈ A, F x = 0
      · obtain ⟨x, hxA, hx0⟩ := hzero
        exact Or.inl ⟨x, hx0, hxA⟩
      · have hregular : ∀ x ∈ A, G x ≠ 0 := by
          intro x hxA hGx
          apply hzero
          refine ⟨x, hxA, ?_⟩
          rw [← hGF hxA]
          exact hGx
        have hsection :
            ∀ q ∈ A, ∃ R : ℝ, 0 < R ∧
              ∀ z ∈ A, z ∈ ball q R →
                Transversal.transverseValue (G q) q z = 0 →
                  z = q := by
          intro q hqA
          exact
            OmegaSectionUnique.exists_radius_unique
              hGcompact hGdiff.continuous hG γ hγ hEq hγinj
                hΦ0 hΦ hqA (hregular q hqA)
        obtain ⟨T, hT, p, hpA, hperiodic, hArange⟩ :=
          PlanarReduction.exists_periodic_range_eq
            hGcompact hGdiff.continuous hG hΦ0 hΦ
              hAcompact hAne hApre hAinv hregular hsection
        let β : ℝ → Plane := Φ p
        have hβF :
            IsIntegralCurve β (fun _ x ↦ F x) := by
          intro t
          have hβA : β t ∈ A := hAinv p hpA t
          simpa only [β, hGF hβA] using hΦ p t
        have hβregular : F (β 0) ≠ 0 := by
          change F (Φ p 0) ≠ 0
          rw [hΦ0]
          rw [← hGF hpA]
          exact hregular p hpA
        exact
          Or.inr
            ⟨T, hT, β, hβF, hperiodic, hβregular,
              by
                simpa only [A, Helpers.omegaSet] using hArange⟩
    · rcases
        PeriodicBranch.equilibrium_or_periodic_of_not_injOn
          F hF γ hγ hbounded hγinj with heq | hper
      · exact Or.inl (by simpa only [Helpers.omegaSet] using heq)
      · exact Or.inr
          (by
            simpa only [Helpers.omegaSet, Function.Periodic] using hper)
  · exact Or.inl hbounded

end Submission
