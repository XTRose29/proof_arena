import Submission.Conull

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology

namespace Submission.Model

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

theorem exists_isWeaklyMixing (m : Measure X)
    [IsProbabilityMeasure m] [NoAtoms m] :
    ∃ T : Automorphism m, IsWeaklyMixing m T := by
  let R₀ := Helpers.commonUniformRange m Bernoulli.probability
  have hR₀ : MeasurableSet R₀ :=
    Helpers.measurableSet_commonUniformRange m Bernoulli.probability
  have hR₀full : volume R₀ᶜ = 0 :=
    Helpers.volume_commonUniformRange_compl m Bernoulli.probability
  let D₀ := Helpers.uniformSource Bernoulli.probability R₀
  have hD₀ : MeasurableSet D₀ :=
    Helpers.measurableSet_uniformSource Bernoulli.probability hR₀
  have hD₀full : Bernoulli.probability D₀ᶜ = 0 :=
    Helpers.measure_uniformSource_compl Bernoulli.probability hR₀ hR₀full
  let C := Transport.invariantCore Bernoulli.shiftEquiv D₀
  have hC : MeasurableSet C :=
    Transport.measurableSet_invariantCore Bernoulli.shiftEquiv hD₀
  have hCfull : Bernoulli.probability Cᶜ = 0 :=
    Transport.measure_invariantCore_compl Bernoulli.probability
      Bernoulli.shiftEquiv Bernoulli.shift.measurePreserving hD₀ hD₀full
  have hCgood : C ⊆ Helpers.uniformGood Bernoulli.probability := by
    intro y hy
    have hyD := Transport.invariantCore_subset Bernoulli.shiftEquiv D₀ hy
    exact hyD.1
  let R := Helpers.uniformCoordinate Bernoulli.probability '' C
  have hR : MeasurableSet R :=
    hC.image_of_measurable_injOn
      (Helpers.measurable_uniformCoordinate Bernoulli.probability)
      ((Helpers.injOn_uniformCoordinate_uniformGood Bernoulli.probability).mono hCgood)
  have hmeasureC : Bernoulli.probability C = 1 := by
    rw [measure_of_measure_compl_eq_zero hCfull, measure_univ]
  have hmeasureR : volume R = 1 := by
    calc
      volume R = Bernoulli.probability C :=
        Helpers.measure_image_uniformCoordinate Bernoulli.probability hC hCgood
      _ = 1 := hmeasureC
  have hRfull : volume Rᶜ = 0 := by
    rw [measure_compl hR (measure_ne_top volume R), hmeasureR,
      measure_univ, tsub_self]
  have hRn : R ⊆ Helpers.uniformRange Bernoulli.probability := by
    exact Set.image_mono hCgood
  have hRm : R ⊆ Helpers.uniformRange m := by
    rintro r ⟨y, hyC, rfl⟩
    have hyD := Transport.invariantCore_subset Bernoulli.shiftEquiv D₀ hyC
    change y ∈ Helpers.uniformGood Bernoulli.probability ∧
      Helpers.uniformCoordinate Bernoulli.probability y ∈ R₀ at hyD
    exact hyD.2.1
  let DX := Helpers.uniformSource m R
  let DY := Helpers.uniformSource Bernoulli.probability R
  have hDX : MeasurableSet DX := Helpers.measurableSet_uniformSource m hR
  have hDY : MeasurableSet DY :=
    Helpers.measurableSet_uniformSource Bernoulli.probability hR
  have hDXfull : m DXᶜ = 0 :=
    Helpers.measure_uniformSource_compl m hR hRfull
  have hDYC : DY = C := by
    ext y
    constructor
    · rintro ⟨hygood, z, hzC, hzy⟩
      have hzgood := hCgood hzC
      have : z = y :=
        Helpers.injOn_uniformCoordinate_uniformGood Bernoulli.probability
          hzgood hygood hzy
      rwa [← this]
    · intro hyC
      exact ⟨hCgood hyC, y, hyC, rfl⟩
  letI : StandardBorelSpace DX := hDX.standardBorel
  letI : StandardBorelSpace DY := hDY.standardBorel
  letI : StandardBorelSpace C := hC.standardBorel
  let e₀ : DX ≃ᵐ DY :=
    Helpers.uniformBridge m Bernoulli.probability R hR hRm hRn
  have he₀ : MeasurePreserving e₀
      (Conull.subtypeMeasure m DX)
      (Conull.subtypeMeasure Bernoulli.probability DY) :=
    Helpers.measurePreserving_uniformBridge m Bernoulli.probability R hR hRm hRn
  let c : DY ≃ᵐ C :=
    { toEquiv := Equiv.setCongr hDYC
      measurable_toFun := measurable_subtype_coe.subtype_mk
      measurable_invFun := measurable_subtype_coe.subtype_mk }
  have hc : MeasurePreserving c
      (Conull.subtypeMeasure Bernoulli.probability DY)
      (Transport.invariantMeasure Bernoulli.probability Bernoulli.shiftEquiv D₀) := by
    refine ⟨c.measurable, ?_⟩
    ext A hA
    unfold Conull.subtypeMeasure Transport.invariantMeasure
    rw [Measure.map_apply c.measurable hA,
      comap_subtype_coe_apply hDY Bernoulli.probability,
      comap_subtype_coe_apply hC Bernoulli.probability]
    congr 1
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨c z, hz, rfl⟩
    · rintro ⟨z, hz, hzy⟩
      refine ⟨c.symm z, ?_, ?_⟩
      · simpa using hz
      · change (z : Bernoulli.Space) = y
        exact hzy
  let e : DX ≃ᵐ C := e₀.trans c
  have he : MeasurePreserving e
      (Conull.subtypeMeasure m DX)
      (Transport.invariantMeasure Bernoulli.probability Bernoulli.shiftEquiv D₀) :=
    hc.comp he₀
  let TC := Transport.coreAutomorphism Bernoulli.probability Bernoulli.shiftEquiv
    Bernoulli.shift.measurePreserving D₀ hD₀
  have hTC : IsWeaklyMixing
      (Transport.invariantMeasure Bernoulli.probability Bernoulli.shiftEquiv D₀) TC :=
    Transport.isWeaklyMixing_core Bernoulli.shift Bernoulli.shift_isWeaklyMixing hD₀
  let U := Transport.pullbackAutomorphism e he TC
  have hU : IsWeaklyMixing (Conull.subtypeMeasure m DX) U :=
    Transport.isWeaklyMixing_pullback e he TC hTC
  exact ⟨Conull.extendAutomorphism m DX hDX hDXfull U,
    Conull.isWeaklyMixing_extend m DX hDX hDXfull U hU⟩

end Submission.Model
