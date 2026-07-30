import Submission.SmoothCutoff

open Set Function Filter
open scoped ContDiff Topology Manifold

noncomputable section

namespace Submission.Helpers

lemma exists_smooth_extension (K U : Set ℂ) (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    ∃ δ : ℝ, 0 < δ ∧ ∃ g : ℂ → ℂ,
      ContDiff ℝ ∞ g ∧ HasCompactSupport g ∧
      (∀ z ∈ Metric.cthickening (δ / 3) K, g z = f z) ∧
      (∀ z ∈ Metric.thickening (δ / 3) K,
        Complex.I * fderiv ℝ g z 1 - fderiv ℝ g z Complex.I = 0) := by
  obtain ⟨δ, hδ, χ, hχsmooth, hχcompact, hχone, hχsupport⟩ :=
    exists_smooth_cutoff K U hK hU hKU
  let g : ℂ → ℂ := fun z => (χ z : ℂ) * f z
  have hχcomplex : ContDiff ℝ ∞ (fun z => (χ z : ℂ)) := by
    change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ χ)
    exact Complex.ofRealCLM.contDiff.comp hχsmooth
  have hfreal : ContDiffOn ℝ ∞ f U :=
    (hf.restrictScalars (𝕜 := ℝ)).contDiffOn_of_completeSpace
  have hgU : ContDiffOn ℝ ∞ g U := by
    exact hχcomplex.contDiffOn.mul hfreal
  have hgzero : ∀ z ∈ (tsupport χ)ᶜ, g z = 0 := by
    intro z hz
    have hz0 : χ z = 0 := by
      rw [← notMem_support]
      exact fun hzs => hz (subset_tsupport χ hzs)
    simp [g, hz0]
  have hgcompl : ContDiffOn ℝ ∞ g (tsupport χ)ᶜ := by
    exact (contDiffOn_const : ContDiffOn ℝ ∞ (fun _ : ℂ => (0 : ℂ)) (tsupport χ)ᶜ).congr
      hgzero
  have hcover : U ∪ (tsupport χ)ᶜ = univ := by
    apply eq_univ_of_forall
    intro z
    by_cases hz : z ∈ U
    · exact Or.inl hz
    · exact Or.inr (fun hzs => hz (hχsupport hzs))
  have hgsmooth : ContDiff ℝ ∞ g :=
    contDiff_of_contDiffOn_union_of_isOpen hgU hgcompl hcover hU isClosed_closure.isOpen_compl
  have hgcompact : HasCompactSupport g := by
    have hχcomplex_compact : HasCompactSupport fun z => (χ z : ℂ) :=
      hχcompact.comp_left Complex.ofReal_zero
    exact hχcomplex_compact.mul_right
  refine ⟨δ, hδ, g, hgsmooth, hgcompact, ?_, ?_⟩
  · intro z hz
    simp [g, hχone z hz]
  · intro z hz
    have hz_inner : z ∈ interior (Metric.cthickening (δ / 3) K) :=
      Metric.thickening_subset_interior_cthickening _ _ hz
    have hgf : g =ᶠ[𝓝 z] f := by
      filter_upwards [isOpen_interior.mem_nhds hz_inner] with w hw
      simp [g, hχone w (interior_subset hw)]
    rw [hgf.fderiv_eq]
    have hzU : z ∈ U := by
      apply hχsupport
      apply subset_tsupport χ
      rw [Function.mem_support]
      simp [hχone z (interior_subset hz_inner)]
    have hfdiff : DifferentiableAt ℂ f z := (hf z hzU).differentiableAt
    rw [hfdiff.fderiv_restrictScalars ℝ]
    simp

end Submission.Helpers
