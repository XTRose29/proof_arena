import Submission.CauchyIntegrandDef

open Set Function Filter
open scoped Topology

noncomputable section

namespace Submission.Helpers

lemma continuous_cauchyIntegrand (K N : Set ℂ) (h : ℂ → ℂ)
    (_hK : IsCompact K) (hN : IsOpen N) (hKN : K ⊆ N) (hh : Continuous h)
    (hzero : ∀ w ∈ N, h w = 0) :
    Continuous (cauchyIntegrand K h (fun z hz => hzero z (hKN hz))) := by
  letI : CompactSpace K := isCompact_iff_compactSpace.mp _hK
  have hscalar : Continuous fun p : ℂ × K => h p.1 * (p.1 - p.2.1)⁻¹ := by
    rw [continuous_iff_continuousAt]
    intro p
    by_cases hp : p.1 = p.2.1
    · have hpN : p.1 ∈ N := hp ▸ hKN p.2.property
      have heq : h =ᶠ[𝓝 p.1] 0 := by
        filter_upwards [hN.mem_nhds hpN] with w hw
        exact hzero w hw
      apply (continuousAt_const : ContinuousAt (fun _ : ℂ × K => (0 : ℂ)) p).congr_of_eventuallyEq
      filter_upwards [heq.comp_tendsto continuousAt_fst] with q hq
      rw [show h q.1 = 0 by
        simpa only [Function.comp_apply, Pi.zero_apply] using hq, zero_mul]
    · exact (hh.continuousAt.comp continuousAt_fst).mul <|
        (continuousAt_fst.sub
          (continuous_subtype_val.continuousAt.comp continuousAt_snd)).inv₀
            (sub_ne_zero.mpr hp)
  apply ContinuousMap.continuous_of_continuous_uncurry
  change Continuous (fun p : ℂ × K => h p.1 * (p.1 - (p.2 : ℂ))⁻¹)
  exact hscalar

end Submission.Helpers
