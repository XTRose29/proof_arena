import Submission.Helpers
import Submission.Bernoulli

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology

namespace Submission.Transport

variable {Y : Type*} [MeasurableSpace Y]

def invariantCore (S : Y ≃ᵐ Y) (D : Set Y) : Set Y :=
  (⋂ n : ℕ, (S : Y → Y)^[n] ⁻¹' D) ∩
    ⋂ n : ℕ, (S.symm : Y → Y)^[n] ⁻¹' D

theorem mem_invariantCore {S : Y ≃ᵐ Y} {D : Set Y} {y : Y} :
    y ∈ invariantCore S D ↔
      (∀ n : ℕ, (S : Y → Y)^[n] y ∈ D) ∧
      ∀ n : ℕ, (S.symm : Y → Y)^[n] y ∈ D := by
  simp [invariantCore]

theorem measurableSet_invariantCore (S : Y ≃ᵐ Y) {D : Set Y}
    (hD : MeasurableSet D) : MeasurableSet (invariantCore S D) := by
  apply MeasurableSet.inter
  · exact MeasurableSet.iInter fun n ↦ hD.preimage (S.measurable.iterate n)
  · exact MeasurableSet.iInter fun n ↦ hD.preimage (S.symm.measurable.iterate n)

theorem measure_invariantCore_compl (μ : Measure Y) (S : Y ≃ᵐ Y)
    (hS : MeasurePreserving S μ μ) {D : Set Y}
    (hD : MeasurableSet D) (hDfull : μ Dᶜ = 0) :
    μ (invariantCore S D)ᶜ = 0 := by
  have hforward : μ (⋂ n : ℕ, (S : Y → Y)^[n] ⁻¹' D)ᶜ = 0 := by
    rw [Set.compl_iInter, measure_iUnion_null_iff]
    intro n
    rw [← Set.preimage_compl]
    rw [(hS.iterate n).measure_preimage hD.compl.nullMeasurableSet]
    exact hDfull
  have hbackward : μ (⋂ n : ℕ, (S.symm : Y → Y)^[n] ⁻¹' D)ᶜ = 0 := by
    rw [Set.compl_iInter, measure_iUnion_null_iff]
    intro n
    rw [← Set.preimage_compl]
    rw [((hS.symm S).iterate n).measure_preimage hD.compl.nullMeasurableSet]
    exact hDfull
  have hcompl : (invariantCore S D)ᶜ =
      (⋂ n : ℕ, (S : Y → Y)^[n] ⁻¹' D)ᶜ ∪
        (⋂ n : ℕ, (S.symm : Y → Y)^[n] ⁻¹' D)ᶜ := by
    simp only [invariantCore, Set.compl_inter]
  rw [hcompl, measure_union_null_iff]
  exact ⟨hforward, hbackward⟩

theorem invariantCore_subset (S : Y ≃ᵐ Y) (D : Set Y) :
    invariantCore S D ⊆ D := by
  intro y hy
  exact (mem_invariantCore.mp hy).1 0

theorem invariantCore_map_mem (S : Y ≃ᵐ Y) {D : Set Y} {y : Y}
    (hy : y ∈ invariantCore S D) : S y ∈ invariantCore S D := by
  rw [mem_invariantCore] at hy ⊢
  constructor
  · intro n
    simpa [Function.iterate_succ_apply] using hy.1 (n + 1)
  · intro n
    cases n with
    | zero => simpa using hy.1 1
    | succ n => simpa [Function.iterate_succ_apply] using hy.2 n

theorem invariantCore_symm_mem (S : Y ≃ᵐ Y) {D : Set Y} {y : Y}
    (hy : y ∈ invariantCore S D) : S.symm y ∈ invariantCore S D := by
  rw [mem_invariantCore] at hy ⊢
  constructor
  · intro n
    cases n with
    | zero => simpa using hy.2 1
    | succ n => simpa [Function.iterate_succ_apply] using hy.1 n
  · intro n
    simpa [Function.iterate_succ_apply] using hy.2 (n + 1)

noncomputable def invariantEquiv (S : Y ≃ᵐ Y) (D : Set Y) :
    invariantCore S D ≃ᵐ invariantCore S D where
  toEquiv :=
    { toFun := fun y ↦ ⟨S y, invariantCore_map_mem S y.property⟩
      invFun := fun y ↦ ⟨S.symm y, invariantCore_symm_mem S y.property⟩
      left_inv := fun y ↦ Subtype.ext (S.symm_apply_apply y)
      right_inv := fun y ↦ Subtype.ext (S.apply_symm_apply y) }
  measurable_toFun := (S.measurable.comp measurable_subtype_coe).subtype_mk
  measurable_invFun := (S.symm.measurable.comp measurable_subtype_coe).subtype_mk

@[simp]
theorem coe_invariantEquiv (S : Y ≃ᵐ Y) (D : Set Y)
    (y : invariantCore S D) : (invariantEquiv S D y : Y) = S y := rfl

noncomputable def invariantMeasure (μ : Measure Y) (S : Y ≃ᵐ Y)
    (D : Set Y) : Measure (invariantCore S D) :=
  Measure.comap ((↑) : invariantCore S D → Y) μ

theorem measurePreserving_invariantEquiv (μ : Measure Y) (S : Y ≃ᵐ Y)
    [StandardBorelSpace Y] (hS : MeasurePreserving S μ μ)
    {D : Set Y} (hD : MeasurableSet D) :
    MeasurePreserving (invariantEquiv S D)
      (invariantMeasure μ S D) (invariantMeasure μ S D) := by
  have hC : MeasurableSet (invariantCore S D) :=
    measurableSet_invariantCore S hD
  letI : StandardBorelSpace (invariantCore S D) := hC.standardBorel
  refine ⟨(invariantEquiv S D).measurable, ?_⟩
  ext t ht
  unfold invariantMeasure
  rw [Measure.map_apply (invariantEquiv S D).measurable ht,
    comap_subtype_coe_apply hC μ,
    comap_subtype_coe_apply hC μ]
  have htimage : MeasurableSet
      (((↑) : invariantCore S D → Y) '' t) :=
    ht.image_of_measurable_injOn measurable_subtype_coe
      (fun _ _ _ _ h ↦ Subtype.ext h)
  have hset :
      ((↑) : invariantCore S D → Y) '' ((invariantEquiv S D) ⁻¹' t) =
        S ⁻¹' (((↑) : invariantCore S D → Y) '' t) := by
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨invariantEquiv S D z, hz, rfl⟩
    · rintro ⟨z, hz, hSz⟩
      have hyC : y ∈ invariantCore S D := by
        have := invariantCore_symm_mem S z.property
        simpa [hSz] using this
      let w : invariantCore S D := ⟨y, hyC⟩
      refine ⟨w, ?_, rfl⟩
      change invariantEquiv S D w ∈ t
      have hwz : invariantEquiv S D w = z := by
        apply Subtype.ext
        exact hSz.symm
      simpa [hwz] using hz
  rw [hset, hS.measure_preimage htimage.nullMeasurableSet]

noncomputable def coreAutomorphism (μ : Measure Y) (S : Y ≃ᵐ Y)
    [StandardBorelSpace Y] (hS : MeasurePreserving S μ μ)
    (D : Set Y) (hD : MeasurableSet D) :
    Automorphism (invariantMeasure μ S D) where
  toEquiv := invariantEquiv S D
  measurePreserving := measurePreserving_invariantEquiv μ S hS hD

@[simp]
theorem coreAutomorphism_iterate_apply (μ : Measure Y) (S : Y ≃ᵐ Y)
    [StandardBorelSpace Y] (hS : MeasurePreserving S μ μ)
    (D : Set Y) (hD : MeasurableSet D)
    (k : ℕ) (y : invariantCore S D) :
    ((((coreAutomorphism μ S hS D hD).toEquiv :
      invariantCore S D → invariantCore S D)^[k]) y : Y) =
      ((S : Y → Y)^[k]) y := by
  induction k generalizing y with
  | zero => rfl
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
      rfl

theorem isWeaklyMixing_core [StandardBorelSpace Y]
    {μ : Measure Y} (T : Automorphism μ)
    (hT : IsWeaklyMixing μ T) {D : Set Y} (hD : MeasurableSet D) :
    IsWeaklyMixing (invariantMeasure μ T.toEquiv D)
      (coreAutomorphism μ T.toEquiv T.measurePreserving D hD) := by
  intro A B hA hB
  have hC : MeasurableSet (invariantCore T.toEquiv D) :=
    measurableSet_invariantCore T.toEquiv hD
  letI : StandardBorelSpace (invariantCore T.toEquiv D) := hC.standardBorel
  let A' : Set Y := ((↑) : invariantCore T.toEquiv D → Y) '' A
  let B' : Set Y := ((↑) : invariantCore T.toEquiv D → Y) '' B
  have hA' : MeasurableSet A' :=
    hA.image_of_measurable_injOn measurable_subtype_coe
      (fun _ _ _ _ h ↦ Subtype.ext h)
  have hB' : MeasurableSet B' :=
    hB.image_of_measurable_injOn measurable_subtype_coe
      (fun _ _ _ _ h ↦ Subtype.ext h)
  have hlim := hT A' B' hA' hB'
  have hmeasureA : invariantMeasure μ T.toEquiv D A = μ A' := by
    exact comap_subtype_coe_apply hC μ A
  have hmeasureB : invariantMeasure μ T.toEquiv D B = μ B' := by
    exact comap_subtype_coe_apply hC μ B
  have hmeasureInter (k : ℕ) :
      invariantMeasure μ T.toEquiv D
          (((((coreAutomorphism μ T.toEquiv T.measurePreserving D hD).toEquiv :
            invariantCore T.toEquiv D → invariantCore T.toEquiv D)^[k]) ⁻¹' A) ∩ B) =
        μ (((T.toEquiv : Y → Y)^[k] ⁻¹' A') ∩ B') := by
    unfold invariantMeasure
    rw [comap_subtype_coe_apply hC μ]
    congr 1
    ext y
    constructor
    · rintro ⟨z, ⟨hzk, hzB⟩, rfl⟩
      constructor
      · refine ⟨((coreAutomorphism μ T.toEquiv T.measurePreserving D hD).toEquiv :
          invariantCore T.toEquiv D → invariantCore T.toEquiv D)^[k] z, hzk, ?_⟩
        exact coreAutomorphism_iterate_apply μ T.toEquiv T.measurePreserving D hD k z
      · exact ⟨z, hzB, rfl⟩
    · rintro ⟨hzpre, hwpre⟩
      rcases hzpre with ⟨z, hzA, hzy⟩
      rcases hwpre with ⟨w, hwB, hwy⟩
      have hyC : y ∈ invariantCore T.toEquiv D := by
        exact hwy ▸ w.property
      let q : invariantCore T.toEquiv D := ⟨y, hyC⟩
      refine ⟨q, ⟨?_, ?_⟩, rfl⟩
      · have hiter :
            ((((coreAutomorphism μ T.toEquiv T.measurePreserving D hD).toEquiv :
              invariantCore T.toEquiv D → invariantCore T.toEquiv D)^[k]) q : Y) = z := by
          calc
            _ = ((T.toEquiv : Y → Y)^[k]) y :=
              coreAutomorphism_iterate_apply μ T.toEquiv T.measurePreserving D hD k q
            _ = z := hzy.symm
        have hsub :
            (((coreAutomorphism μ T.toEquiv T.measurePreserving D hD).toEquiv :
              invariantCore T.toEquiv D → invariantCore T.toEquiv D)^[k]) q = z :=
          Subtype.ext hiter
        simpa [hsub] using hzA
      · have hqw : q = w := Subtype.ext hwy.symm
        simpa [hqw] using hwB
  simpa only [hmeasureA, hmeasureB, hmeasureInter] using hlim

section Pullback

variable {X : Type*} [MeasurableSpace X]

noncomputable def pullbackAutomorphism {m : Measure X} {μ : Measure Y}
    (e : X ≃ᵐ Y) (he : MeasurePreserving e m μ)
    (T : Automorphism μ) : Automorphism m where
  toEquiv := e.trans (T.toEquiv.trans e.symm)
  measurePreserving :=
    (he.symm e).comp (T.measurePreserving.comp he)

@[simp]
theorem pullbackAutomorphism_apply {m : Measure X} {μ : Measure Y}
    (e : X ≃ᵐ Y) (he : MeasurePreserving e m μ)
    (T : Automorphism μ) (x : X) :
    (pullbackAutomorphism e he T).toEquiv x =
      e.symm (T.toEquiv (e x)) := rfl

theorem measure_image_equiv {m : Measure X} {μ : Measure Y}
    (e : X ≃ᵐ Y) (he : MeasurePreserving e m μ) (A : Set X) :
    μ (e '' A) = m A := by
  change μ (e.toEquiv '' A) = m A
  rw [Equiv.image_eq_preimage_symm]
  exact (he.symm e).measure_preimage_equiv A

theorem isWeaklyMixing_pullback [StandardBorelSpace X] [StandardBorelSpace Y]
    {m : Measure X} {μ : Measure Y} (e : X ≃ᵐ Y)
    (he : MeasurePreserving e m μ) (T : Automorphism μ)
    (hT : IsWeaklyMixing μ T) :
    IsWeaklyMixing m (pullbackAutomorphism e he T) := by
  intro A B hA hB
  let S := pullbackAutomorphism e he T
  let s : X → X := S.toEquiv
  let t : Y → Y := T.toEquiv
  let q : X → Y := e
  let A' : Set Y := e '' A
  let B' : Set Y := e '' B
  have hA' : MeasurableSet A' := e.measurableSet_image.mpr hA
  have hB' : MeasurableSet B' := e.measurableSet_image.mpr hB
  have hsem : Function.Semiconj q s t := by
    intro x
    change e (e.symm (T.toEquiv (e x))) = T.toEquiv (e x)
    exact e.apply_symm_apply _
  have hset (k : ℕ) :
      e '' (s^[k] ⁻¹' A ∩ B) = t^[k] ⁻¹' A' ∩ B' := by
    ext y
    constructor
    · rintro ⟨x, ⟨hxA, hxB⟩, rfl⟩
      constructor
      · refine ⟨s^[k] x, hxA, ?_⟩
        exact hsem.iterate_right k x
      · exact ⟨x, hxB, rfl⟩
    · rintro ⟨⟨z, hzA, hzy⟩, w, hwB, hwy⟩
      let x := e.symm y
      refine ⟨x, ⟨?_, ?_⟩, by simp [x]⟩
      · change s^[k] x ∈ A
        have heq : e (s^[k] x) = e z := by
          calc
            e (s^[k] x) = t^[k] (e x) := hsem.iterate_right k x
            _ = t^[k] y := by simp [x]
            _ = e z := hzy.symm
        have : s^[k] x = z := e.injective heq
        rw [this]
        exact hzA
      · have heq : e x = e w := by
          calc
            e x = y := by simp [x]
            _ = e w := hwy.symm
        have : x = w := e.injective heq
        rw [this]
        exact hwB
  have hmeasure (k : ℕ) :
      m (s^[k] ⁻¹' A ∩ B) = μ (t^[k] ⁻¹' A' ∩ B') := by
    rw [← hset]
    exact (measure_image_equiv e he _).symm
  have hmeasureA : μ A' = m A := measure_image_equiv e he A
  have hmeasureB : μ B' = m B := measure_image_equiv e he B
  have hlim := hT A' B' hA' hB'
  simpa only [hmeasure, hmeasureA, hmeasureB, s, t, S] using hlim

end Pullback

end Submission.Transport
