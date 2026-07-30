import Submission.Conull
import Submission.ConullEquiv

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory

namespace Submission.ConullPullback

noncomputable section

set_option linter.unusedSectionVars false

variable {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
  [StandardBorelSpace X] [StandardBorelSpace Y]

def targetCore {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) : Set d.target :=
  ((↑) : d.target → Y) ⁻¹' Transport.invariantCore T.toEquiv d.target

def sourceCore {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) : Set d.source :=
  d.equiv ⁻¹' targetCore d T

theorem measurableSet_targetCore {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    MeasurableSet (targetCore d T) :=
  (Transport.measurableSet_invariantCore T.toEquiv d.measurableTarget).preimage
    measurable_subtype_coe

theorem measurableSet_sourceCore {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    MeasurableSet (sourceCore d T) :=
  (measurableSet_targetCore d T).preimage d.equiv.measurable

def restrictedEquiv {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    sourceCore d T ≃ᵐ targetCore d T where
  toEquiv :=
    { toFun := fun (x : sourceCore d T) ↦
        ⟨d.equiv x.1, show d.equiv x.1 ∈ targetCore d T from x.2⟩
      invFun := fun (y : targetCore d T) ↦ ⟨d.equiv.symm y.1, by
        change d.equiv (d.equiv.symm y.1) ∈ targetCore d T
        simpa only [d.equiv.apply_symm_apply] using y.2⟩
      left_inv := fun (x : sourceCore d T) ↦
        Subtype.ext (d.equiv.symm_apply_apply x.1)
      right_inv := fun (y : targetCore d T) ↦
        Subtype.ext (d.equiv.apply_symm_apply y.1) }
  measurable_toFun := by
    exact (d.equiv.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := by
    exact (d.equiv.symm.measurable.comp measurable_subtype_coe).subtype_mk

def targetCoreEquiv {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    targetCore d T ≃ᵐ Transport.invariantCore T.toEquiv d.target where
  toEquiv :=
    { toFun := fun y ↦ ⟨(y.1 : Y), y.property⟩
      invFun := fun y ↦
        ⟨⟨y, Transport.invariantCore_subset T.toEquiv d.target y.property⟩,
          y.property⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  measurable_toFun := (measurable_subtype_coe.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (measurable_subtype_coe.subtype_mk).subtype_mk

def coreEquiv {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    sourceCore d T ≃ᵐ Transport.invariantCore T.toEquiv d.target :=
  (restrictedEquiv d T).trans (targetCoreEquiv d T)

theorem measurePreserving_restrictedEquiv {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    MeasurePreserving (restrictedEquiv d T)
      (Conull.subtypeMeasure (Conull.subtypeMeasure m d.source) (sourceCore d T))
      (Conull.subtypeMeasure (Conull.subtypeMeasure n d.target) (targetCore d T)) := by
  let P := sourceCore d T
  let C := targetCore d T
  have hP : MeasurableSet P := measurableSet_sourceCore d T
  have hC : MeasurableSet C := measurableSet_targetCore d T
  refine ⟨(restrictedEquiv d T).measurable, ?_⟩
  ext A hA
  unfold Conull.subtypeMeasure
  rw [Measure.map_apply (restrictedEquiv d T).measurable hA,
    comap_subtype_coe_apply hP
      (Measure.comap ((↑) : d.source → X) m),
    comap_subtype_coe_apply hC
      (Measure.comap ((↑) : d.target → Y) n)]
  have hImage : MeasurableSet (((↑) : C → d.target) '' A) :=
    hC.subtype_image hA
  have hset : ((↑) : P → d.source) '' ((restrictedEquiv d T) ⁻¹' A) =
      d.equiv ⁻¹' (((↑) : C → d.target) '' A) := by
    ext x
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨restrictedEquiv d T z, hz, rfl⟩
    · rintro ⟨z, hz, hzx⟩
      let q : P := ⟨x, by
        change d.equiv x ∈ C
        simpa [hzx] using z.property⟩
      refine ⟨q, ?_, rfl⟩
      have hqz : restrictedEquiv d T q = z := by
        apply Subtype.ext
        exact hzx.symm
      simpa [hqz] using hz
  rw [hset, d.measurePreserving.measure_preimage hImage.nullMeasurableSet]

theorem measurePreserving_targetCoreEquiv {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    MeasurePreserving (targetCoreEquiv d T)
      (Conull.subtypeMeasure (Conull.subtypeMeasure n d.target) (targetCore d T))
      (Transport.invariantMeasure n T.toEquiv d.target) := by
  let C := targetCore d T
  let K := Transport.invariantCore T.toEquiv d.target
  have hC : MeasurableSet C := measurableSet_targetCore d T
  have hK : MeasurableSet K :=
    Transport.measurableSet_invariantCore T.toEquiv d.measurableTarget
  refine ⟨(targetCoreEquiv d T).measurable, ?_⟩
  ext A hA
  unfold Conull.subtypeMeasure Transport.invariantMeasure
  rw [Measure.map_apply (targetCoreEquiv d T).measurable hA,
    comap_subtype_coe_apply hC
      (Measure.comap ((↑) : d.target → Y) n),
    comap_subtype_coe_apply hK n]
  rw [comap_subtype_coe_apply d.measurableTarget n]
  congr 1
  ext y
  simp only [targetCoreEquiv, Set.mem_image, Set.mem_preimage]
  have hsubset : K ⊆ d.target :=
    Transport.invariantCore_subset T.toEquiv d.target
  aesop

theorem measurePreserving_coreEquiv {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    MeasurePreserving (coreEquiv d T)
      (Conull.subtypeMeasure (Conull.subtypeMeasure m d.source) (sourceCore d T))
      (Transport.invariantMeasure n T.toEquiv d.target) :=
  (measurePreserving_targetCoreEquiv d T).comp
    (measurePreserving_restrictedEquiv d T)

theorem targetCoreFull {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    Conull.subtypeMeasure n d.target (targetCore d T)ᶜ = 0 := by
  let C := targetCore d T
  let K := Transport.invariantCore T.toEquiv d.target
  have hK : MeasurableSet K :=
    Transport.measurableSet_invariantCore T.toEquiv d.measurableTarget
  have hKfull : n Kᶜ = 0 :=
    Transport.measure_invariantCore_compl n T.toEquiv T.measurePreserving
      d.measurableTarget d.targetFull
  unfold Conull.subtypeMeasure
  rw [comap_subtype_coe_apply d.measurableTarget n]
  apply measure_mono_null _ hKfull
  rintro _ ⟨z, hz, rfl⟩ hKz
  exact hz hKz

theorem sourceCoreFull {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    Conull.subtypeMeasure m d.source (sourceCore d T)ᶜ = 0 := by
  have hC : MeasurableSet (targetCore d T) := measurableSet_targetCore d T
  have hpre : (sourceCore d T)ᶜ = d.equiv ⁻¹' (targetCore d T)ᶜ := by
    ext x
    simp [sourceCore]
  unfold Conull.subtypeMeasure
  rw [hpre, d.measurePreserving.measure_preimage hC.compl.nullMeasurableSet]
  exact targetCoreFull d T

def sourceAutomorphism {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) :
    Automorphism (Conull.subtypeMeasure m d.source) := by
  letI : StandardBorelSpace d.source := d.measurableSource.standardBorel
  let P := sourceCore d T
  have hP : MeasurableSet P := measurableSet_sourceCore d T
  letI : StandardBorelSpace P := hP.standardBorel
  let R := Transport.coreAutomorphism n T.toEquiv T.measurePreserving
    d.target d.measurableTarget
  let e := coreEquiv d T
  have he : MeasurePreserving e
      (Conull.subtypeMeasure (Conull.subtypeMeasure m d.source) P)
      (Transport.invariantMeasure n T.toEquiv d.target) :=
    measurePreserving_coreEquiv d T
  let U := Transport.pullbackAutomorphism e he R
  exact Conull.extendAutomorphism (Conull.subtypeMeasure m d.source) P hP
    (sourceCoreFull d T) U

def automorphism {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n) : Automorphism m :=
  Conull.extendAutomorphism m d.source d.measurableSource d.sourceFull
    (sourceAutomorphism d T)

theorem sourceAutomorphism_apply_of_mem {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n)
    (x : d.source) (hx : x ∈ sourceCore d T) :
    (sourceAutomorphism d T).toEquiv x =
      ((coreEquiv d T).symm
        ((Transport.coreAutomorphism n T.toEquiv T.measurePreserving
          d.target d.measurableTarget).toEquiv (coreEquiv d T ⟨x, hx⟩)) :
        sourceCore d T) := by
  simp only [sourceAutomorphism, Conull.extendAutomorphism]
  rw [Conull.extendEquiv_apply_of_mem]
  rfl

@[simp]
theorem coe_coreEquiv {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n)
    (x : sourceCore d T) :
    ((coreEquiv d T x : Transport.invariantCore T.toEquiv d.target) : Y) =
      d.equiv x.1 := rfl

theorem equiv_coreEquiv_symm {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n)
    (y : Transport.invariantCore T.toEquiv d.target) :
    ((d.equiv ((coreEquiv d T).symm y).1 : d.target) : Y) = y := by
  have h := congrArg Subtype.val ((coreEquiv d T).apply_symm_apply y)
  change ((d.equiv ((coreEquiv d T).symm y).1 : d.target) : Y) = (y : Y) at h
  exact h

theorem equiv_sourceAutomorphism_apply_of_mem
    {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n)
    (x : d.source) (hx : x ∈ sourceCore d T) :
    ((d.equiv ((sourceAutomorphism d T).toEquiv x) : d.target) : Y) =
      T.toEquiv (d.equiv x) := by
  rw [sourceAutomorphism_apply_of_mem d T x hx]
  let z := (Transport.coreAutomorphism n T.toEquiv T.measurePreserving
    d.target d.measurableTarget).toEquiv (coreEquiv d T ⟨x, hx⟩)
  change ((d.equiv ((coreEquiv d T).symm z).1 : d.target) : Y) =
    T.toEquiv (d.equiv x)
  rw [equiv_coreEquiv_symm]
  dsimp [z]
  change T.toEquiv
    ((coreEquiv d T ⟨x, hx⟩ :
      Transport.invariantCore T.toEquiv d.target) : Y) =
    T.toEquiv (d.equiv x)
  exact congrArg T.toEquiv (coe_coreEquiv d T ⟨x, hx⟩)

theorem automorphism_apply_of_mem {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n)
    {x : X} (hx : x ∈ d.source) :
    (automorphism d T).toEquiv x =
      (sourceAutomorphism d T).toEquiv ⟨x, hx⟩ := by
  exact Conull.extendEquiv_apply_of_mem d.source d.measurableSource
    (sourceAutomorphism d T).toEquiv hx

theorem isWeaklyMixing_sourceAutomorphism {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n)
    (hT : IsWeaklyMixing n T) :
    IsWeaklyMixing (Conull.subtypeMeasure m d.source) (sourceAutomorphism d T) := by
  letI : StandardBorelSpace d.source := d.measurableSource.standardBorel
  let P := sourceCore d T
  have hP : MeasurableSet P := measurableSet_sourceCore d T
  letI : StandardBorelSpace P := hP.standardBorel
  have hK : MeasurableSet (Transport.invariantCore T.toEquiv d.target) :=
    Transport.measurableSet_invariantCore T.toEquiv d.measurableTarget
  letI : StandardBorelSpace (Transport.invariantCore T.toEquiv d.target) :=
    hK.standardBorel
  let R := Transport.coreAutomorphism n T.toEquiv T.measurePreserving
    d.target d.measurableTarget
  have hR : IsWeaklyMixing (Transport.invariantMeasure n T.toEquiv d.target) R :=
    Transport.isWeaklyMixing_core T hT d.measurableTarget
  let e := coreEquiv d T
  have he : MeasurePreserving e
      (Conull.subtypeMeasure (Conull.subtypeMeasure m d.source) P)
      (Transport.invariantMeasure n T.toEquiv d.target) :=
    measurePreserving_coreEquiv d T
  let U := Transport.pullbackAutomorphism e he R
  have hU : IsWeaklyMixing
      (Conull.subtypeMeasure (Conull.subtypeMeasure m d.source) P) U :=
    Transport.isWeaklyMixing_pullback e he R hR
  exact Conull.isWeaklyMixing_extend (Conull.subtypeMeasure m d.source) P hP
    (sourceCoreFull d T) U hU

theorem isWeaklyMixing_automorphism {m : Measure X} {n : Measure Y}
    (d : ConullEquiv.Data m n) (T : Automorphism n)
    (hT : IsWeaklyMixing n T) : IsWeaklyMixing m (automorphism d T) :=
  Conull.isWeaklyMixing_extend m d.source d.measurableSource d.sourceFull
    (sourceAutomorphism d T) (isWeaklyMixing_sourceAutomorphism d T hT)

end

end Submission.ConullPullback
