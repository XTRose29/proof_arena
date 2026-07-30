import Mathlib
import Submission.Helpers

open MeasureTheory

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem bauer_unique [MeasurableSpace X] [BorelSpace X]
    (K : Set X) (hK_cpt : IsCompact K) (hK_cvx : Convex ℝ K)
    {x : X} (hx : x ∈ K.extremePoints ℝ)
    (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : μ Kᶜ = 0) (hbar : x = ∫ y, y ∂μ) :
    μ = Measure.dirac x := by
  classical
  -- Almost all the points lie in `K`.
  have hKae : ∀ᵐ y ∂μ, y ∈ K := by
    exact (mem_ae_iff.2 hμ)
  -- The identity function is integrable; the separable-valued point is useful if
  -- the ambient Banach space itself is not separable.
  have hsm : AEStronglyMeasurable (fun y : X => y) μ := by
    refine (aestronglyMeasurable_iff_aemeasurable_separable).2 ?_
    refine ⟨Measurable.aemeasurable measurable_id, K, hK_cpt.isSeparable, ?_⟩
    exact hKae
  obtain ⟨C, hC⟩ := (isBounded_iff_forall_norm_le.1 hK_cpt.isBounded)
  have hfi : Integrable (fun y : X => y) μ := by
    refine Integrable.of_bound hsm C ?_
    filter_upwards [hKae] with y hy
    exact hC y hy
  have hclosed : IsClosed K := hK_cpt.isClosed

  -- Every slice of nonzero measure, as well as its complement, has its
  -- normalized barycenter in `K`. The average of their two barycenters lies
  -- in the open segment between them.
  have havg_eq (s : Set X) (hs : MeasurableSet s)
      (hs0 : μ s ≠ 0) (hsc0 : μ sᶜ ≠ 0) :
      (⨍ y in s, y ∂μ) = x := by
    have havs : (⨍ y in s, (fun z : X => z) y ∂μ) ∈ K :=
      hK_cvx.set_average_mem hclosed hs0 (measure_ne_top _ _)
        (ae_restrict_of_ae hKae) hfi.integrableOn
    have havc : (⨍ y in sᶜ, (fun z : X => z) y ∂μ) ∈ K :=
      hK_cvx.set_average_mem hclosed hsc0 (measure_ne_top _ _)
        (ae_restrict_of_ae hKae) hfi.integrableOn
    have hseg := average_mem_openSegment_compl_self
      (μ := μ) (f := (fun z : X => z)) hs.nullMeasurableSet hs0 hsc0 hfi
    have hseg' : x ∈ openSegment ℝ
        (⨍ y in s, (fun z : X => z) y ∂μ)
        (⨍ y in sᶜ, (fun z : X => z) y ∂μ) := by
      rw [average_eq_integral (μ:=μ) (fun z : X => z)] at hseg
      rw [← hbar] at hseg
      exact hseg
    exact ((mem_extremePoints.1 hx).2 _ havs _ havc hseg').1

  -- Equality of all set integrals with the constant function `x`.
  have hint : ∀ s : Set X, MeasurableSet s → μ s < ⊤ →
      (∫ y in s, (fun z : X => z) y ∂μ) = (∫ _y in s, x ∂μ) := by
    intro s hs hlt
    by_cases hs0 : μ s = 0
    · rw [setIntegral_measure_zero _ hs0, setIntegral_measure_zero _ hs0]
    by_cases hsc0 : μ sᶜ = 0
    · have hae_s : ∀ᵐ y ∂μ, y ∈ s := (mem_ae_iff.2 hsc0)
      have hr : μ.restrict s = μ := Measure.restrict_eq_self_of_ae_mem hae_s
      change (∫ y, (fun z : X => z) y ∂(μ.restrict s)) =
        (∫ _y, x ∂(μ.restrict s))
      rw [hr]
      calc
        (∫ y : X, (fun z : X => z) y ∂μ) = x := hbar.symm
        _ = ∫ _y : X, x ∂μ := by simp
    · have hav := havg_eq s hs hs0 hsc0
      calc
        (∫ y in s, (fun z : X => z) y ∂μ) =
            ∫ _y in s, ⨍ a in s, (fun z : X => z) a ∂μ ∂μ :=
              (setIntegral_setAverage μ (fun z : X => z) s).symm
        _ = ∫ _y in s, x ∂μ := by rw [hav]

  have heq : (fun y : X => y) =ᵐ[μ] (fun _y : X => x) :=
    Integrable.ae_eq_of_forall_setIntegral_eq
      (fun y : X => y) (fun _y : X => x) hfi (integrable_const _) hint
  have hone : ∀ᵐ y ∂μ, y ∈ ({x} : Set X) := by
    filter_upwards [heq] with y hy
    simpa using hy
  have hone' : ∀ᵐ y ∂μ, y ∈ ({x} : Finset X) := by
    filter_upwards [hone] with y hy
    simpa using hy
  have hmass : μ ({x} : Set X) = 1 :=
    (prob_compl_eq_zero_iff (MeasurableSet.singleton x)).1 (mem_ae_iff.1 hone)
  have H := (Measure.ae_mem_finset_iff (μ := μ) (s := ({x} : Finset X))).1 hone'
  simpa [hmass] using H


end Submission
