import Submission.TwoSidedGenerator
import Submission.ConditionalInformation

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma exists_code_preimage_ae_eq_of_full_measurableEmbedding
    {M B : Type*} [MeasurableSpace M] [MeasurableSpace B]
    (mu : Measure M) (code : M → B)
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => code x.1))
    {A : Set M} (hA : MeasurableSet A) :
    ∃ C : Set B, MeasurableSet C ∧ A =ᵐ[mu] code ⁻¹' C := by
  let A' : Set s := Subtype.val ⁻¹' A
  let restrictedCode : s → B := fun x => code x.1
  let C : Set B := restrictedCode '' A'
  have hA' : MeasurableSet A' := hA.preimage measurable_subtype_coe
  refine ⟨C, hemb.measurableSet_image' hA', ?_⟩
  have hs : ∀ᵐ x ∂mu, x ∈ s := mem_ae_iff.mpr hfull
  filter_upwards [hs] with x hx
  apply propext
  constructor
  · intro hxA
    exact ⟨⟨x, hx⟩, hxA, rfl⟩
  · rintro ⟨y, hyA, hycode⟩
    have hyx : y = ⟨x, hx⟩ := hemb.injective hycode
    change y.1 ∈ A at hyA
    rw [hyx] at hyA
    exact hyA

lemma aestronglyMeasurable_indicator_comap_of_full_measurableEmbedding
    {M B : Type*} [MeasurableSpace M] [MeasurableSpace B]
    (mu : Measure M) (code : M → B)
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => code x.1))
    {A : Set M} (hA : MeasurableSet A) :
    AEStronglyMeasurable[MeasurableSpace.comap code inferInstance]
      (A.indicator (fun _ => (1 : ℝ))) mu := by
  obtain ⟨C, hC, hAC⟩ :=
    exists_code_preimage_ae_eq_of_full_measurableEmbedding
      mu code hfull hemb hA
  have hpreimage : MeasurableSet[MeasurableSpace.comap code inferInstance]
      (code ⁻¹' C) :=
    MeasurableSpace.measurableSet_comap.mpr ⟨C, hC, rfl⟩
  have hmeas : StronglyMeasurable[MeasurableSpace.comap code inferInstance]
      ((code ⁻¹' C).indicator (fun _ => (1 : ℝ))) :=
    (measurable_const.indicator hpreimage).stronglyMeasurable
  exact hmeas.aestronglyMeasurable.congr
    (indicator_ae_eq_of_ae_eq_set hAC).symm

lemma condExp_indicator_comap_ae_eq_of_full_measurableEmbedding
    {M B : Type*} [mM : MeasurableSpace M] [MeasurableSpace B]
    (mu : Measure M) [IsFiniteMeasure mu]
    (code : M → B) (hcode : Measurable code)
    {s : Set M} (hfull : mu sᶜ = 0)
    (hemb : MeasurableEmbedding (fun x : s => code x.1))
    {A : Set M} (hA : MeasurableSet A) :
    mu[A.indicator (fun _ => (1 : ℝ)) |
        MeasurableSpace.comap code inferInstance] =ᵐ[mu]
      A.indicator (fun _ => (1 : ℝ)) := by
  apply condExp_of_aestronglyMeasurable' hcode.comap_le
  · exact aestronglyMeasurable_indicator_comap_of_full_measurableEmbedding
      mu code hfull hemb hA
  · exact (integrable_const _).indicator hA

lemma ae_tendsto_condExp_twoSidedCode_indicator_of_shrinking
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    (P : Finset (Set EucPlane)) (hP : ∀ A ∈ P, MeasurableSet A)
    {s : Set EucPlane} (hs : MeasurableSet s) (hfull : mu sᶜ = 0)
    {lam1 lam2 R : ℝ} (hR : 0 < R)
    (good : ℕ → Set EucPlane)
    (hs_good : ∀ x ∈ s, ∀ᶠ L : ℕ in atTop, x ∈ good L)
    (hs_atom : ∀ x ∈ s, ∀ L,
      ∃ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L), x ∈ A)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L))
    {A : Set EucPlane} (hA : MeasurableSet A) :
    ∀ᵐ x ∂mu, Tendsto
      (fun n => (mu[A.indicator (fun _ => (1 : ℝ)) |
        twoSidedCodeFiltration T T_inv hT hT_inv P hP n]) x)
      atTop (nhds (A.indicator (fun _ => (1 : ℝ)) x)) := by
  have hlevy := tendsto_ae_condExp
    (μ := mu) (ℱ := twoSidedCodeFiltration T T_inv hT hT_inv P hP)
    (A.indicator (fun _ => (1 : ℝ)))
  rw [iSup_twoSidedCodeFiltration_eq_comap T T_inv hT hT_inv P hP] at hlevy
  have hcond := condExp_indicator_comap_ae_eq_of_full_measurableEmbedding
    mu (natTwoSidedPartitionCode T T_inv P)
      (measurable_natTwoSidedPartitionCode T T_inv hT hT_inv P hP)
      hfull
      (measurableEmbedding_natTwoSidedPartitionCode_restrict_of_shrinking
        T T_inv hT_right hT hT_inv P hP hs hR good hs_good hs_atom hpair)
      hA
  filter_upwards [hlevy, hcond] with x hx hcx
  simpa [hcx] using hx

end Submission.Helpers
