import Mathlib

open MeasureTheory

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace Submission

theorem bauer_unique [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (hK_cpt : IsCompact K) (hK_cvx : Convex ℝ K)
    {x : X} (hx : x ∈ K.extremePoints ℝ)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : μ Kᶜ = 0) (hbar : x = ∫ y, y ∂μ) :
    μ = Measure.dirac x := by
  have hμK : ∀ᵐ y ∂μ, y ∈ K := mem_ae_iff.mpr hμ
  have hfi : Integrable (fun y : X => y) μ := by
    have hfiK : IntegrableOn (fun y : X => y) K μ :=
      continuous_id.continuousOn.integrableOn_compact hK_cpt
    simpa only [IntegrableOn, Measure.restrict_eq_self_of_ae_mem hμK] using hfiK
  have hconst : (fun y : X => y) =ᵐ[μ] Function.const X x := by
    rcases ae_eq_const_or_exists_average_ne_compl hfi with h | ⟨t, ht, ht0, htc0, hne⟩
    · simpa only [average_eq_integral, ← hbar] using h
    · have htK : (⨍ y in t, y ∂μ) ∈ K :=
        hK_cvx.set_average_mem hK_cpt.isClosed ht0 (by finiteness)
          (ae_restrict_of_ae hμK) hfi.integrableOn
      have htcK : (⨍ y in tᶜ, y ∂μ) ∈ K :=
        hK_cvx.set_average_mem hK_cpt.isClosed htc0 (by finiteness)
          (ae_restrict_of_ae hμK) hfi.integrableOn
      have hseg : x ∈ openSegment ℝ (⨍ y in t, y ∂μ) (⨍ y in tᶜ, y ∂μ) := by
        simpa only [average_eq_integral, ← hbar] using
          average_mem_openSegment_compl_self ht.nullMeasurableSet ht0 htc0 hfi
      have havg := (mem_extremePoints.mp hx).2 _ htK _ htcK hseg
      exact (hne (havg.1.trans havg.2.symm)).elim
  calc
    μ = Measure.map (fun y : X => y) μ := Measure.map_id'.symm
    _ = Measure.map (Function.const X x) μ := Measure.map_congr hconst
    _ = Measure.dirac x := by
      change μ.map (fun _ : X => x) = Measure.dirac x
      simp only [Measure.map_const, measure_univ, one_smul]

end Submission
