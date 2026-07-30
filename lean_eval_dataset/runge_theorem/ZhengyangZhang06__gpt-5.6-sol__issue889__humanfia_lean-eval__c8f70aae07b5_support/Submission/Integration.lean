import Submission.Cauchy

open Set MeasureTheory Function Filter
open scoped Real Topology ContDiff

noncomputable section

namespace Submission.Helpers

lemma integral_complex_eq_iterated (F : ℂ → ℂ) (hF : Integrable F) :
    (∫ z : ℂ, F z) =
      ∫ x : ℝ, ∫ y : ℝ, F (x + y * Complex.I) := by
  have hprod : Integrable (F ∘ Complex.measurableEquivRealProd.symm) :=
    ((Complex.volume_preserving_equiv_real_prod.symm).integrable_comp_emb
      Complex.measurableEquivRealProd.symm.measurableEmbedding).2 hF
  have hprod' :
      Integrable (F ∘ Complex.measurableEquivRealProd.symm)
        (volume.prod volume) := by
    rw [← Measure.volume_eq_prod]
    exact hprod
  calc
    (∫ z : ℂ, F z) =
        ∫ p : ℝ × ℝ, F (Complex.measurableEquivRealProd.symm p) := by
      symm
      exact (Complex.volume_preserving_equiv_real_prod.symm).integral_comp
        Complex.measurableEquivRealProd.symm.measurableEmbedding F
    _ = ∫ p : ℝ × ℝ, F (Complex.measurableEquivRealProd.symm p)
          ∂(volume.prod volume) := by
      rw [← Measure.volume_eq_prod]
    _ = ∫ x : ℝ, ∫ y : ℝ,
          F (Complex.measurableEquivRealProd.symm (x, y)) :=
      integral_prod _ hprod'
    _ = ∫ x : ℝ, ∫ y : ℝ, F (x + y * Complex.I) := by
      simp only [Complex.measurableEquivRealProd_symm_apply, Complex.mk_eq_add_mul_I]

lemma smooth_holomorphic_restriction_mem_rationalMaps_closure
    (K N : Set ℂ) (g : ℂ → ℂ)
    (hK : IsCompact K) (hN : IsOpen N) (hKN : K ⊆ N)
    (hg : ContDiff ℝ ∞ g) (hgc : HasCompactSupport g)
    (hhol : ∀ z ∈ K, DifferentiableAt ℂ g z)
    (hzero : ∀ w ∈ N, crDefect g w = 0) :
    (⟨fun z : K => g z, hg.continuous.comp continuous_subtype_val⟩ : C(K, ℂ)) ∈
      (rationalMaps K).closure := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp hK
  let hK0 : ∀ w ∈ K, crDefect g w = 0 := fun w hw => hzero w (hKN hw)
  let C : ℂ → C(K, ℂ) := cauchyIntegrand K (crDefect g) hK0
  have hCcont : Continuous C :=
    continuous_cauchyIntegrand K N (crDefect g) hK hN hKN
      (continuous_crDefect g hg) hzero
  have hCsupp : HasCompactSupport C :=
    cauchyIntegrand_hasCompactSupport K (crDefect g) hK0
      (crDefect_hasCompactSupport g hgc)
  have hCint : Integrable C := hCcont.integrable_of_hasCompactSupport hCsupp
  have hJmem : (∫ w : ℂ, C w) ∈ (rationalMaps K).closure := by
    apply integral_mem_submodule_closure (rationalMaps K) hCint
    intro w
    exact subset_closure (cauchyIntegrand_mem_rationalMaps K (crDefect g) hK0 w)
  have hscaled :
      (-(2 * Real.pi * Complex.I : ℂ)⁻¹) • (∫ w : ℂ, C w) ∈
        (rationalMaps K).closure :=
    (rationalMaps K).closure.smul_mem _ hJmem
  have heq :
      (⟨fun z : K => g z, hg.continuous.comp continuous_subtype_val⟩ : C(K, ℂ)) =
        (-(2 * Real.pi * Complex.I : ℂ)⁻¹) • (∫ w : ℂ, C w) := by
    ext z
    rw [ContinuousMap.smul_apply, ContinuousMap.integral_apply hCint z]
    have hscalarCont : Continuous fun w : ℂ => C w z :=
      (ContinuousMap.evalCLM ℝ z).continuous.comp hCcont
    have hscalarSupp : HasCompactSupport fun w : ℂ => C w z :=
      hCsupp.mono fun w hw hCw => hw (by
        change C w z = 0
        rw [hCw]
        rfl)
    have hscalarInt : Integrable fun w : ℂ => C w z :=
      hscalarCont.integrable_of_hasCompactSupport hscalarSupp
    rw [integral_complex_eq_iterated _ hscalarInt]
    dsimp only [C, cauchyIntegrand]
    simpa only [ContinuousMap.coe_mk, smul_eq_mul, mul_comm] using
      cauchyPompeiu_centered K N g hK hN hKN hg hgc hhol hzero z z.property
  rw [heq]
  exact hscaled

lemma analytic_restriction_mem_rationalMaps_closure
    (K U : Set ℂ) (hK : IsCompact K) (hU : IsOpen U) (hKU : K ⊆ U)
    (f : ℂ → ℂ) (hf : AnalyticOnNhd ℂ f U) :
    (⟨fun z : K => f z, hf.continuousOn.comp_continuous continuous_subtype_val
      (fun z => hKU z.property)⟩ : C(K, ℂ)) ∈ (rationalMaps K).closure := by
  obtain ⟨δ, hδ, g, hg, hgc, hgf, hzero⟩ :=
    exists_smooth_extension K U hK hU hKU f hf
  let N := Metric.thickening (δ / 3) K
  have hN : IsOpen N := Metric.isOpen_thickening
  have hKN : K ⊆ N := Metric.self_subset_thickening (by positivity) K
  have hhol : ∀ z ∈ K, DifferentiableAt ℂ g z := by
    intro z hz
    have hz_inner : z ∈ interior (Metric.cthickening (δ / 3) K) :=
      Metric.thickening_subset_interior_cthickening _ _
        (Metric.self_subset_thickening (by positivity) K hz)
    have heq : g =ᶠ[𝓝 z] f := by
      filter_upwards [isOpen_interior.mem_nhds hz_inner] with w hw
      exact hgf w (interior_subset hw)
    exact heq.differentiableAt_iff.mpr (hf z (hKU hz)).differentiableAt
  have hmem :=
    smooth_holomorphic_restriction_mem_rationalMaps_closure
      K N g hK hN hKN hg hgc hhol hzero
  convert hmem using 1
  ext z
  exact (hgf z (Metric.self_subset_cthickening K z.property)).symm

end Submission.Helpers
