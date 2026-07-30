import Submission.Smoothing

open Set
open scoped ContDiff Topology

noncomputable section

namespace Submission.Helpers

/-- A fixed smooth Lipschitz reference can be chosen before the depth of the
analytic core.  At every subsequently chosen core depth, a second smooth
approximant agrees with the original analytic function on that core and stays
uniformly close to the fixed reference.

This ordering is useful in the frontier localization argument: after the
Lipschitz constant is known, the core depth can be made small enough to control
oscillation without making the smoothing derivative part of the estimate. -/
theorem exists_lipschitz_reference_and_smooth_core
    (K : Set ℂ) (hK : IsCompact K)
    (f : ℂ → ℂ) (hfc : ContinuousOn f K)
    (hfh : AnalyticOnNhd ℂ f (interior K))
    (η : ℝ) (hη : 0 < η) :
    ∃ (H : ℂ → ℂ) (C : NNReal),
      ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ LipschitzWith C H ∧
        ∀ δ : ℝ, 0 < δ →
          ∃ g : ℂ → ℂ,
            ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
              (∀ z ∈ K, ‖f z - g z‖ < η) ∧
              EqOn g f (interiorCore K δ) ∧
              ∀ z w : ℂ,
                dist (g z) (g w) <
                  (C : ℝ) * dist z w + 4 * η := by
  obtain ⟨F, hFcontinuous, _hFuniform, hFcompact, hFK⟩ :=
    exists_compactSupport_uniformContinuous_extension K hK f hfc
  obtain ⟨H, hHsmooth, hHcompact, hFH, _hHempty⟩ :=
    exists_smooth_compactSupport_approx_eqOn_of_extension
      K ∅ isClosed_empty (empty_subset (interior K))
      f F hfh hFcontinuous hFcompact hFK η hη
  obtain ⟨C, hHC⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport
      hHcompact hHsmooth (by simp)
  refine ⟨H, C, hHsmooth, hHcompact, hHC, ?_⟩
  intro δ hδ
  obtain ⟨g, hgsmooth, hgcompact, hFg, hgf⟩ :=
    exists_smooth_compactSupport_approx_eqOn_of_extension
      K (interiorCore K δ)
      (isClosed_interiorCore hK.isClosed δ)
      (interiorCore_subset_interior K hδ)
      f F hfh hFcontinuous hFcompact hFK η hη
  refine ⟨g, hgsmooth, hgcompact, ?_, hgf, ?_⟩
  · intro z hz
    rw [← hFK hz]
    exact hFg z
  · have hgH : ∀ z : ℂ, dist (g z) (H z) < 2 * η := by
      intro z
      calc
        dist (g z) (H z) ≤ dist (g z) (F z) + dist (F z) (H z) :=
          dist_triangle _ _ _
        _ < η + η := by
          apply add_lt_add
          · simpa only [dist_eq_norm, norm_sub_rev] using hFg z
          · simpa only [dist_eq_norm] using hFH z
        _ = 2 * η := by ring
    intro z w
    have htri₁ :
        dist (g z) (g w) ≤
          dist (g z) (H z) + dist (H z) (g w) :=
      dist_triangle _ _ _
    have htri₂ :
        dist (H z) (g w) ≤
          dist (H z) (H w) + dist (H w) (g w) :=
      dist_triangle _ _ _
    have hHL :
        dist (H z) (H w) ≤ (C : ℝ) * dist z w :=
      hHC.dist_le_mul z w
    have hwg : dist (H w) (g w) < 2 * η := by
      simpa only [dist_comm] using hgH w
    linarith [hgH z]

/-- A strengthened two-stage smoothing statement in which the final
approximation tolerance is independent of the tolerance used to choose the
Lipschitz reference.

The second smoothing is applied to the small correction `F - H`.  On the
analytic core this correction is already real-smooth, so it can be preserved
there.  Consequently the final function can be made arbitrarily close to the
original extension while its oscillation is bounded by the Lipschitz
oscillation of `H` plus the uniformly small correction. -/
theorem exists_lipschitz_reference_and_arbitrarily_close_smooth_core
    (K : Set ℂ) (hK : IsCompact K)
    (f : ℂ → ℂ) (hfc : ContinuousOn f K)
    (hfh : AnalyticOnNhd ℂ f (interior K))
    (η : ℝ) (hη : 0 < η) :
    ∃ (H : ℂ → ℂ) (C : NNReal),
      ContDiff ℝ ∞ H ∧ HasCompactSupport H ∧ LipschitzWith C H ∧
        ∀ δ : ℝ, 0 < δ →
          ∀ σ : ℝ, 0 < σ →
            ∃ g : ℂ → ℂ,
              ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
                (∀ z ∈ K, ‖f z - g z‖ < σ) ∧
                EqOn g f (interiorCore K δ) ∧
                ∀ z w : ℂ,
                  dist (g z) (g w) <
                    (C : ℝ) * dist z w + 2 * η + 2 * σ := by
  obtain ⟨F, hFcontinuous, _hFuniform, hFcompact, hFK⟩ :=
    exists_compactSupport_uniformContinuous_extension K hK f hfc
  obtain ⟨H, hHsmooth, hHcompact, hFH, _hHempty⟩ :=
    exists_smooth_compactSupport_approx_eqOn_of_extension
      K ∅ isClosed_empty (empty_subset (interior K))
      f F hfh hFcontinuous hFcompact hFK η hη
  obtain ⟨C, hHC⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport
      hHcompact hHsmooth (by simp)
  refine ⟨H, C, hHsmooth, hHcompact, hHC, ?_⟩
  intro δ hδ σ hσ
  let E : ℂ → ℂ := F - H
  have hEcontinuous : Continuous E :=
    hFcontinuous.sub hHsmooth.continuous
  have hEcompact : HasCompactSupport E := by
    change HasCompactSupport (F - H)
    exact hFcompact.sub hHcompact
  have hfreal : ContDiffOn ℝ ∞ f (interior K) :=
    (hfh.restrictScalars (𝕜 := ℝ)).contDiffOn_of_completeSpace
  have hFreal : ContDiffOn ℝ ∞ F (interior K) :=
    hfreal.congr fun z hz ↦ hFK (interior_subset hz)
  have hEreal : ContDiffOn ℝ ∞ E (interior K) := by
    change ContDiffOn ℝ ∞ (fun z ↦ F z - H z) (interior K)
    exact hFreal.sub hHsmooth.contDiffOn
  obtain ⟨e, hesmooth, heclose, heE, hesupport⟩ :=
    hEcontinuous.exists_contDiff_approx_and_eqOn ⊤
      (continuous_const : Continuous fun _ : ℂ ↦ σ)
      (fun _ ↦ hσ)
      (isClosed_interiorCore hK.isClosed δ)
      (isOpen_interior.mem_nhdsSet.mpr
        (interiorCore_subset_interior K hδ))
      hEreal
  have hecompact : HasCompactSupport e :=
    hEcompact.mono' (hesupport.trans (subset_tsupport E))
  let g : ℂ → ℂ := H + e
  have hgsmooth : ContDiff ℝ ∞ g :=
    hHsmooth.add hesmooth
  have hgcompact : HasCompactSupport g := by
    change HasCompactSupport (H + e)
    exact hHcompact.add hecompact
  have hEsmall (z : ℂ) : ‖E z‖ < η := by
    change ‖F z - H z‖ < η
    exact hFH z
  have hesmall (z : ℂ) : ‖e z‖ < η + σ := by
    calc
      ‖e z‖ ≤ ‖e z - E z‖ + ‖E z‖ := by
        simpa only [sub_add_cancel] using
          norm_add_le (e z - E z) (E z)
      _ < σ + η := by
        apply add_lt_add
        · simpa only [dist_eq_norm] using heclose z
        · exact hEsmall z
      _ = η + σ := add_comm _ _
  refine ⟨g, hgsmooth, hgcompact, ?_, ?_, ?_⟩
  · intro z hz
    rw [← hFK hz]
    change ‖F z - (H z + e z)‖ < σ
    calc
      ‖F z - (H z + e z)‖ = ‖e z - (F z - H z)‖ := by
        rw [show F z - (H z + e z) =
            -(e z - (F z - H z)) by ring,
          norm_neg]
      _ < σ := by
        simpa [E, dist_eq_norm] using heclose z
  · intro z hz
    change H z + e z = f z
    rw [heE hz]
    change H z + (F z - H z) = f z
    rw [hFK (interior_subset
      (interiorCore_subset_interior K hδ hz))]
    ring
  · intro z w
    have hHL :
        ‖H z - H w‖ ≤ (C : ℝ) * dist z w := by
      simpa only [dist_eq_norm] using hHC.dist_le_mul z w
    rw [dist_eq_norm]
    change ‖(H z + e z) - (H w + e w)‖ < _
    calc
      ‖(H z + e z) - (H w + e w)‖ =
          ‖(H z - H w) + (e z - e w)‖ := by
        congr 1
        ring
      _ ≤ ‖H z - H w‖ + ‖e z - e w‖ :=
        norm_add_le _ _
      _ ≤ (C : ℝ) * dist z w + (‖e z‖ + ‖e w‖) :=
        add_le_add hHL (norm_sub_le _ _)
      _ < (C : ℝ) * dist z w +
          ((η + σ) + (η + σ)) := by
        linarith [hesmall z, hesmall w]
      _ = (C : ℝ) * dist z w + 2 * η + 2 * σ := by
        ring

end Submission.Helpers
