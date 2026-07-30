import Mathlib
import Submission.Helpers

open Set Function
open scoped ContDiff Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- The part of `K` which stays at least a prescribed positive distance from its frontier. -/
def interiorCore (K : Set ℂ) (δ : ℝ) : Set ℂ :=
  K \ Metric.thickening δ (frontier K)

theorem isClosed_interiorCore {K : Set ℂ} (hK : IsClosed K) (δ : ℝ) :
    IsClosed (interiorCore K δ) :=
  hK.sdiff Metric.isOpen_thickening

theorem isCompact_interiorCore {K : Set ℂ} (hK : IsCompact K) (δ : ℝ) :
    IsCompact (interiorCore K δ) :=
  hK.of_isClosed_subset (isClosed_interiorCore hK.isClosed δ) sdiff_subset

theorem interiorCore_subset_interior (K : Set ℂ) {δ : ℝ} (hδ : 0 < δ) :
    interiorCore K δ ⊆ interior K := by
  intro z hz
  rw [mem_interior_iff_notMem_frontier hz.1]
  intro hfrontier
  exact hz.2 (Metric.self_subset_thickening hδ (frontier K) hfrontier)

/-- The real differential's Cauchy--Riemann defect. -/
def crDefect (g : ℂ → ℂ) (z : ℂ) : ℂ :=
  Complex.I * fderiv ℝ g z 1 - fderiv ℝ g z Complex.I

theorem crDefect_eq_zero_of_differentiableAt {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) :
    crDefect g z = 0 := by
  rw [crDefect, hg.fderiv_restrictScalars ℝ]
  simp

theorem continuous_crDefect (g : ℂ → ℂ) (hg : ContDiff ℝ ∞ g) :
    Continuous (crDefect g) := by
  have hD : Continuous (fderiv ℝ g) := hg.continuous_fderiv (by simp)
  exact (continuous_const.mul (hD.clm_apply continuous_const)).sub
    (hD.clm_apply continuous_const)

theorem crDefect_hasCompactSupport (g : ℂ → ℂ) (hg : HasCompactSupport g) :
    HasCompactSupport (crDefect g) := by
  apply hg.mono'
  intro z hz
  by_contra hzt
  have hD : fderiv ℝ g z = 0 := fderiv_of_notMem_tsupport ℝ hzt
  exact hz (by simp [crDefect, hD])

theorem differentiableAt_of_eqOn_interiorCore (K : Set ℂ) {δ : ℝ} (hδ : 0 < δ)
    {f g : ℂ → ℂ} (hfh : AnalyticOnNhd ℂ f (interior K))
    (hgf : EqOn g f (interiorCore K δ)) {z : ℂ}
    (hz : z ∈ interior (interiorCore K δ)) :
    DifferentiableAt ℂ g z := by
  have hzK : z ∈ interior K :=
    interiorCore_subset_interior K hδ (interior_subset hz)
  have heq : g =ᶠ[𝓝 z] f := by
    filter_upwards [isOpen_interior.mem_nhds hz] with w hw
    exact hgf (interior_subset hw)
  exact heq.differentiableAt_iff.mpr (hfh z hzK).differentiableAt

theorem crDefect_eq_zero_on_interiorCore (K : Set ℂ) {δ : ℝ} (hδ : 0 < δ)
    {f g : ℂ → ℂ} (hfh : AnalyticOnNhd ℂ f (interior K))
    (hgf : EqOn g f (interiorCore K δ)) :
    ∀ z ∈ interior (interiorCore K δ), crDefect g z = 0 := by
  intro z hz
  exact crDefect_eq_zero_of_differentiableAt
    (differentiableAt_of_eqOn_interiorCore K hδ hfh hgf hz)

/-- A smooth cutoff taking values in `[0,1]` and equal to one on a fixed
neighborhood of a compact set. -/
theorem exists_smooth_cutoff_bounded
    (K U : Set ℂ) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ χ : ℂ → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ z, 0 ≤ χ z ∧ χ z ≤ 1) ∧
      (∀ z ∈ Metric.cthickening (δ / 3) K, χ z = 1) ∧
      tsupport χ ⊆ U := by
  obtain ⟨δ, hδ, hδU⟩ := hK.exists_cthickening_subset_open hU hKU
  let inner := Metric.cthickening (δ / 3) K
  let outer := Metric.thickening (2 * δ / 3) K
  have hinner : IsClosed inner := Metric.isClosed_cthickening
  have houter : IsOpen outer := Metric.isOpen_thickening
  have hinner_outer : inner ⊆ outer := by
    dsimp [inner, outer]
    exact Metric.cthickening_subset_thickening' (by positivity) (by linarith) K
  obtain ⟨χ, hχsmooth, hχrange, hχsupport, hχone⟩ :=
    exists_contMDiff_support_eq_eq_one_iff 𝓘(ℝ, ℂ) houter hinner hinner_outer
  have houter_closure :
      closure outer ⊆ Metric.cthickening δ K := by
    refine (Metric.closure_thickening_subset_cthickening (2 * δ / 3) K).trans ?_
    exact Metric.cthickening_mono (by linarith) K
  have hχtsupport : tsupport χ ⊆ U := by
    rw [tsupport, hχsupport]
    exact houter_closure.trans hδU
  have hχcompact : HasCompactSupport χ := by
    rw [HasCompactSupport]
    exact hK.cthickening.of_isClosed_subset isClosed_closure
      (by simpa only [tsupport, hχsupport] using houter_closure)
  refine ⟨δ, hδ, χ, hχsmooth.contDiff, hχcompact, ?_, ?_, hχtsupport⟩
  · intro z
    exact hχrange (mem_range_self z)
  · intro z hz
    exact (hχone z).1 hz

/-- A smooth cutoff which is one on a fixed neighborhood of a compact set. -/
theorem exists_smooth_cutoff (K U : Set ℂ) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ χ : ℂ → ℝ,
      ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      (∀ z ∈ Metric.cthickening (δ / 3) K, χ z = 1) ∧
      tsupport χ ⊆ U := by
  obtain ⟨δ, hδ, χ, hχsmooth, hχcompact, _hχbounds,
      hχone, hχsupport⟩ :=
    exists_smooth_cutoff_bounded K U hK hU hKU
  exact
    ⟨δ, hδ, χ, hχsmooth, hχcompact, hχone, hχsupport⟩

/-- A continuous function on a compact planar set has a continuous compactly supported extension. -/
theorem exists_compactSupport_continuous_extension (K : Set ℂ) (hK : IsCompact K)
    (f : ℂ → ℂ) (hfc : ContinuousOn f K) :
    ∃ F : ℂ → ℂ, Continuous F ∧ HasCompactSupport F ∧ EqOn F f K := by
  let fK : C(K, ℂ) := restrictTo f hfc
  obtain ⟨F, hF⟩ := fK.exists_restrict_eq hK.isClosed
  obtain ⟨δ, _hδ, χ, hχsmooth, hχcompact, hχone, _hχsupport⟩ :=
    exists_smooth_cutoff K univ hK isOpen_univ (subset_univ K)
  let G : ℂ → ℂ := fun z ↦ (χ z : ℂ) * F z
  have hχcomplex : ContDiff ℝ ∞ (fun z ↦ (χ z : ℂ)) := by
    change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ χ)
    exact Complex.ofRealCLM.contDiff.comp hχsmooth
  have hGcontinuous : Continuous G :=
    hχcomplex.continuous.mul F.continuous
  have hGcompact : HasCompactSupport G := by
    have hχcomplex_compact : HasCompactSupport fun z ↦ (χ z : ℂ) :=
      hχcompact.comp_left Complex.ofReal_zero
    exact hχcomplex_compact.mul_right
  refine ⟨G, hGcontinuous, hGcompact, fun z hz ↦ ?_⟩
  have hFz : F z = f z := by
    have hz' := DFunLike.congr_fun hF ⟨z, hz⟩
    simpa [fK, restrictTo] using hz'
  simp [G, hχone z (Metric.self_subset_cthickening K hz), hFz]

/-- The compactly supported extension may be retained together with its
global uniform continuity. -/
theorem exists_compactSupport_uniformContinuous_extension
    (K : Set ℂ) (hK : IsCompact K)
    (f : ℂ → ℂ) (hfc : ContinuousOn f K) :
    ∃ F : ℂ → ℂ,
      Continuous F ∧ UniformContinuous F ∧
        HasCompactSupport F ∧ EqOn F f K := by
  obtain ⟨F, hF, hFc, hFK⟩ :=
    exists_compactSupport_continuous_extension K hK f hfc
  exact
    ⟨F, hF, hFc.uniformContinuous_of_continuous hF, hFc, hFK⟩

/-- Globally smooth a specified compactly supported extension while
preserving the analytic data on a closed subset of the interior.  Keeping
the extension explicit permits geometric localization to be chosen before
the final smoothing tolerance. -/
theorem exists_smooth_compactSupport_approx_eqOn_of_extension
    (K S : Set ℂ) (hS : IsClosed S) (hSint : S ⊆ interior K)
    (f F : ℂ → ℂ) (hfh : AnalyticOnNhd ℂ f (interior K))
    (hFcontinuous : Continuous F) (hFcompact : HasCompactSupport F)
    (hFK : EqOn F f K) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ z, ‖F z - g z‖ < ε) ∧ EqOn g f S := by
  have hfreal : ContDiffOn ℝ ∞ f (interior K) :=
    (hfh.restrictScalars (𝕜 := ℝ)).contDiffOn_of_completeSpace
  have hFreal : ContDiffOn ℝ ∞ F (interior K) :=
    hfreal.congr fun z hz ↦ hFK (interior_subset hz)
  obtain ⟨g, hg, hgclose, hgF, hgsupport⟩ :=
    hFcontinuous.exists_contDiff_approx_and_eqOn ⊤
      (continuous_const : Continuous fun _ : ℂ ↦ ε)
      (fun _ ↦ hε) hS (isOpen_interior.mem_nhdsSet.mpr hSint) hFreal
  have hgcompact : HasCompactSupport g :=
    hFcompact.mono' (hgsupport.trans (subset_tsupport F))
  refine ⟨g, hg, hgcompact, ?_, ?_⟩
  · intro z
    simpa only [dist_eq_norm, norm_sub_rev] using hgclose z
  · intro z hz
    exact (hgF hz).trans (hFK (interior_subset (hSint hz)))

/-- Smooth relative approximation of a continuous-on function, preserving it on a closed
interior core and retaining compact support. -/
theorem exists_smooth_compactSupport_approx_eqOn (K S : Set ℂ)
    (hK : IsCompact K) (hS : IsClosed S) (hSint : S ⊆ interior K)
    (f : ℂ → ℂ) (hfc : ContinuousOn f K)
    (hfh : AnalyticOnNhd ℂ f (interior K)) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ z ∈ K, ‖f z - g z‖ < ε) ∧ EqOn g f S := by
  obtain ⟨F, hFcontinuous, hFcompact, hFK⟩ :=
    exists_compactSupport_continuous_extension K hK f hfc
  have hfreal : ContDiffOn ℝ ∞ f (interior K) :=
    (hfh.restrictScalars (𝕜 := ℝ)).contDiffOn_of_completeSpace
  have hFreal : ContDiffOn ℝ ∞ F (interior K) :=
    hfreal.congr fun z hz ↦ hFK (interior_subset hz)
  obtain ⟨g, hg, hgclose, hgF, hgsupport⟩ :=
    hFcontinuous.exists_contDiff_approx_and_eqOn ⊤
      (continuous_const : Continuous fun _ : ℂ ↦ ε)
      (fun _ ↦ hε) hS (isOpen_interior.mem_nhdsSet.mpr hSint) hFreal
  have hgcompact : HasCompactSupport g :=
    hFcompact.mono' (hgsupport.trans (subset_tsupport F))
  refine ⟨g, hg, hgcompact, ?_, ?_⟩
  · intro z hz
    have hclose := hgclose z
    rw [hFK hz] at hclose
    simpa only [dist_eq_norm, norm_sub_rev] using hclose
  · intro z hz
    exact (hgF hz).trans (hFK (interior_subset (hSint hz)))

/-- A smooth compactly supported approximation which agrees with the original function on a
prescribed deep-interior core. -/
theorem exists_smooth_compactSupport_approx_eqOn_interiorCore (K : Set ℂ)
    (hK : IsCompact K) (f : ℂ → ℂ) (hfc : ContinuousOn f K)
    (hfh : AnalyticOnNhd ℂ f (interior K)) (δ ε : ℝ) (hδ : 0 < δ) (hε : 0 < ε) :
    ∃ g : ℂ → ℂ, ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ z ∈ K, ‖f z - g z‖ < ε) ∧ EqOn g f (interiorCore K δ) :=
  exists_smooth_compactSupport_approx_eqOn K (interiorCore K δ) hK
    (isClosed_interiorCore hK.isClosed δ) (interiorCore_subset_interior K hδ)
    f hfc hfh ε hε

end Submission.Helpers
