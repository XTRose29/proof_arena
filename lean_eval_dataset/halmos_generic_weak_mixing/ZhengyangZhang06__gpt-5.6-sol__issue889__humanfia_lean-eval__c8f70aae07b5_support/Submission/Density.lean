import Submission.ConullPullback
import Submission.MarkerMeasure
import Submission.WeakTopology

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology
open scoped symmDiff

namespace Submission.Density

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

abbrev LabelSpace (F : Finset (Set X)) := {A // A ∈ F} → Bool

noncomputable def label (F : Finset (Set X)) (x : X) : LabelSpace F := by
  classical
  exact fun A => if x ∈ (A : Set X) then true else false

@[simp]
theorem label_apply_true_iff (F : Finset (Set X)) (x : X)
    (A : {A // A ∈ F}) :
    label F x A = true ↔ x ∈ (A : Set X) := by
  simp [label]

theorem measurable_label (F : Finset (Set X))
    (hF : ∀ A ∈ F, MeasurableSet A) : Measurable (label F) := by
  classical
  refine measurable_pi_lambda _ fun A => ?_
  simpa only [label] using
    Measurable.ite (p := fun x : X => x ∈ (A : Set X))
      (hF A A.property)
      (measurable_const : Measurable fun _ : X => true)
      (measurable_const : Measurable fun _ : X => false)

def trackedSets {m : Measure X} (S : Automorphism m)
    (F : Finset (Set X)) : Finset (Set X) :=
  F ∪ F.image fun A => S.toEquiv '' A

theorem mem_trackedSets_self {m : Measure X} (S : Automorphism m)
    {F : Finset (Set X)} {A : Set X} (hA : A ∈ F) :
    A ∈ trackedSets S F := by
  exact Finset.mem_union_left _ hA

theorem mem_trackedSets_image {m : Measure X} (S : Automorphism m)
    {F : Finset (Set X)} {A : Set X} (hA : A ∈ F) :
    S.toEquiv '' A ∈ trackedSets S F := by
  apply Finset.mem_union_right
  exact Finset.mem_image.mpr ⟨A, hA, rfl⟩

theorem measurableSet_equiv_image {m : Measure X} (S : Automorphism m)
    {A : Set X} (hA : MeasurableSet A) :
    MeasurableSet (S.toEquiv '' A) := by
  have hpre := hA.preimage S.toEquiv.symm.measurable
  have himage : S.toEquiv '' A = S.toEquiv.symm ⁻¹' A := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨S.toEquiv.symm x, hx, S.toEquiv.apply_symm_apply x⟩
  rw [himage]
  exact hpre

theorem measurable_trackedSets {m : Measure X} (S : Automorphism m)
    (F : Finset (Set X)) (hF : ∀ A ∈ F, MeasurableSet A) :
    ∀ A ∈ trackedSets S F, MeasurableSet A := by
  intro A hA
  rcases Finset.mem_union.mp hA with hA | hA
  · exact hF A hA
  · obtain ⟨B, hBF, rfl⟩ := Finset.mem_image.mp hA
    exact measurableSet_equiv_image S (hF B hBF)

theorem exists_weaklyMixing_finset_close (m : Measure X)
    [IsProbabilityMeasure m] [NoAtoms m] (S : Automorphism m)
    (F : Finset (Set X)) (hF : ∀ A ∈ F, MeasurableSet A)
    (p : MarkerCode.Parameter) (hp : 0 < (p : ℝ)) :
    ∃ T : Automorphism m, IsWeaklyMixing m T ∧
      ∀ A ∈ F,
        m.real ((T.toEquiv '' A) ∆ (S.toEquiv '' A)) ≤ (p : ℝ) := by
  classical
  let H := trackedSets S F
  let f : X → LabelSpace H := label H
  let mu := MarkerCode.probability p m
  let R : Automorphism mu := MarkerCode.shift p m
  let g : MarkerCode.Space X → LabelSpace H :=
    f ∘ MarkerCode.code S
  have hH : ∀ A ∈ H, MeasurableSet A := by
    exact measurable_trackedSets S F hF
  have hf : Measurable f := measurable_label H hH
  have hg : Measurable g := hf.comp (MarkerCode.measurable_code S)
  have hcode : MeasurePreserving (MarkerCode.code S) mu m := by
    exact MarkerCode.measurePreserving_code p m hp S
  have hLaw : ∀ z, m (FiniteFactor.fiber f z) =
      mu (FiniteFactor.fiber g z) := by
    intro z
    have hz : MeasurableSet (FiniteFactor.fiber f z) :=
      FiniteFactor.measurableSet_fiber hf z
    calc
      m (FiniteFactor.fiber f z) =
          mu (MarkerCode.code S ⁻¹' FiniteFactor.fiber f z) :=
        (hcode.measure_preimage hz.nullMeasurableSet).symm
      _ = mu (FiniteFactor.fiber g z) := by
        congr 1
  let d : ConullEquiv.Data m mu :=
    FiniteFactor.conullEquivData m mu f g hf hg hLaw
  let T : Automorphism m := ConullPullback.automorphism d R
  have hR : IsWeaklyMixing mu R := by
    exact GeneralBernoulli.shift_isWeaklyMixing (MarkerCode.baseMeasure p m)
  have hT : IsWeaklyMixing m T :=
    ConullPullback.isWeaklyMixing_automorphism d R hR
  refine ⟨T, hT, ?_⟩
  intro A hAF
  let SA : Set X := S.toEquiv '' A
  have hA : MeasurableSet A := hF A hAF
  have hSA : MeasurableSet SA := measurableSet_equiv_image S hA
  let a : {B // B ∈ H} := ⟨A, mem_trackedSets_self S hAF⟩
  let sa : {B // B ∈ H} := ⟨SA, mem_trackedSets_image S hAF⟩
  have hdlabel (x : d.source) : g (d.equiv x) = f x := by
    change g (((FiniteFactor.rangeEquiv m mu f g hf hg hLaw) x :
      Set.range (FiniteFactor.targetEmbedding m mu f g hf hg hLaw)) :
        MarkerCode.Space X) = f (x : X)
    exact FiniteFactor.rangeEquiv_label m mu f g hf hg hLaw x
  have hpoint (x : d.source) (hxcore : x ∈ ConullPullback.sourceCore d R)
      (hhas : MarkerCode.hasMarker ((d.equiv x : d.target) : MarkerCode.Space X))
      (hnext : ¬ MarkerCode.nextMarker
        ((d.equiv x : d.target) : MarkerCode.Space X)) :
      T.toEquiv (x : X) ∈ SA ↔ (x : X) ∈ A := by
    let x' : d.source := (ConullPullback.sourceAutomorphism d R).toEquiv x
    have hshift : ((d.equiv x' : d.target) : MarkerCode.Space X) =
        R.toEquiv ((d.equiv x : d.target) : MarkerCode.Space X) := by
      exact ConullPullback.equiv_sourceAutomorphism_apply_of_mem d R x hxcore
    have hxlabel := congrFun (hdlabel x) a
    have hx'label := congrFun (hdlabel x') sa
    dsimp [g, f, Function.comp_def] at hxlabel hx'label
    rw [hshift, MarkerCode.code_shift p S hhas hnext] at hx'label
    have hcodeA : MarkerCode.code S
        ((d.equiv x : d.target) : MarkerCode.Space X) ∈ A ↔
        (x : X) ∈ A := by
      have ha : MarkerCode.code S
          ((d.equiv x : d.target) : MarkerCode.Space X) ∈ (a : Set X) ↔
          (x : X) ∈ (a : Set X) := by
        rw [← label_apply_true_iff H _ a,
          ← label_apply_true_iff H _ a, hxlabel]
      simpa [a] using ha
    have hcodeSA : S.toEquiv (MarkerCode.code S
        ((d.equiv x : d.target) : MarkerCode.Space X)) ∈ SA ↔
        (x' : X) ∈ SA := by
      have hsa : S.toEquiv (MarkerCode.code S
          ((d.equiv x : d.target) : MarkerCode.Space X)) ∈ (sa : Set X) ↔
          (x' : X) ∈ (sa : Set X) := by
        rw [← label_apply_true_iff H _ sa,
          ← label_apply_true_iff H _ sa, hx'label]
      simpa [sa] using hsa
    have hx'SA : (x' : X) ∈ SA ↔ (x : X) ∈ A := by
      calc
        (x' : X) ∈ SA ↔
            S.toEquiv (MarkerCode.code S
              ((d.equiv x : d.target) : MarkerCode.Space X)) ∈ SA :=
          hcodeSA.symm
        _ ↔ MarkerCode.code S
              ((d.equiv x : d.target) : MarkerCode.Space X) ∈ A := by
          simp [SA]
        _ ↔ (x : X) ∈ A := hcodeA
    have happly : T.toEquiv (x : X) = (x' : X) := by
      exact ConullPullback.automorphism_apply_of_mem d R x.property
    rw [happly]
    exact hx'SA
  let E : Set X :=
    (T.toEquiv ⁻¹' SA) ∆ (S.toEquiv ⁻¹' SA)
  have hE : MeasurableSet E :=
    (hSA.preimage T.toEquiv.measurable).symmDiff
      (hSA.preimage S.toEquiv.measurable)
  let N : Set (MarkerCode.Space X) :=
    {w | ¬ MarkerCode.hasMarker w}
  let Q : Set (MarkerCode.Space X) :=
    {w | MarkerCode.nextMarker w}
  let ND : Set d.source :=
    d.equiv ⁻¹' (((↑) : d.target → MarkerCode.Space X) ⁻¹' N)
  let QD : Set d.source :=
    d.equiv ⁻¹' (((↑) : d.target → MarkerCode.Space X) ⁻¹' Q)
  have hsubset : ((↑) : d.source → X) ⁻¹' E ⊆
      ((ConullPullback.sourceCore d R)ᶜ ∪ ND) ∪ QD := by
    intro x hx
    by_cases hxcore : x ∈ ConullPullback.sourceCore d R
    · by_cases hhas : MarkerCode.hasMarker
          ((d.equiv x : d.target) : MarkerCode.Space X)
      · by_cases hnext : MarkerCode.nextMarker
            ((d.equiv x : d.target) : MarkerCode.Space X)
        · exact Or.inr hnext
        · have hTmem := hpoint x hxcore hhas hnext
          have hSmem : S.toEquiv (x : X) ∈ SA ↔ (x : X) ∈ A := by
            simp [SA]
          have : T.toEquiv (x : X) ∈ SA ↔ S.toEquiv (x : X) ∈ SA :=
            hTmem.trans hSmem.symm
          rw [Set.mem_preimage, Set.mem_symmDiff] at hx
          rcases hx with ⟨hxT, hxS⟩ | ⟨hxS, hxT⟩
          · exact (hxS (this.mp hxT)).elim
          · exact (hxT (this.mpr hxS)).elim
      · exact Or.inl (Or.inr hhas)
    · exact Or.inl (Or.inl hxcore)
  have hN : MeasurableSet N := MarkerCode.measurableSet_hasMarker.compl
  have hQ : MeasurableSet Q := MarkerCode.measurableSet_nextMarker
  have hND : Conull.subtypeMeasure m d.source ND = 0 := by
    dsimp [ND]
    calc
      Conull.subtypeMeasure m d.source
          (d.equiv ⁻¹' (((↑) : d.target → MarkerCode.Space X) ⁻¹' N)) =
          Conull.subtypeMeasure mu d.target
            (((↑) : d.target → MarkerCode.Space X) ⁻¹' N) :=
        d.measurePreserving.measure_preimage
          (hN.preimage measurable_subtype_coe).nullMeasurableSet
      _ = mu N := Conull.subtypeMeasure_preimage mu d.target
        d.measurableTarget d.targetFull hN
      _ = 0 := by
        simpa [mu, N] using MarkerCode.noMarker_null p m hp
  have hQD : Conull.subtypeMeasure m d.source QD = mu Q := by
    dsimp [QD]
    calc
      Conull.subtypeMeasure m d.source
          (d.equiv ⁻¹' (((↑) : d.target → MarkerCode.Space X) ⁻¹' Q)) =
          Conull.subtypeMeasure mu d.target
            (((↑) : d.target → MarkerCode.Space X) ⁻¹' Q) :=
        d.measurePreserving.measure_preimage
          (hQ.preimage measurable_subtype_coe).nullMeasurableSet
      _ = mu Q := Conull.subtypeMeasure_preimage mu d.target
        d.measurableTarget d.targetFull hQ
  have hcore : Conull.subtypeMeasure m d.source
      (ConullPullback.sourceCore d R)ᶜ = 0 :=
    ConullPullback.sourceCoreFull d R
  have hmeasure : m E ≤ mu Q := by
    rw [← Conull.subtypeMeasure_preimage m d.source d.measurableSource
      d.sourceFull hE]
    calc
      Conull.subtypeMeasure m d.source (((↑) : d.source → X) ⁻¹' E) ≤
          Conull.subtypeMeasure m d.source
            (((ConullPullback.sourceCore d R)ᶜ ∪ ND) ∪ QD) :=
        measure_mono hsubset
      _ ≤ Conull.subtypeMeasure m d.source
            ((ConullPullback.sourceCore d R)ᶜ ∪ ND) +
          Conull.subtypeMeasure m d.source QD := measure_union_le _ _
      _ ≤ (Conull.subtypeMeasure m d.source
            (ConullPullback.sourceCore d R)ᶜ +
          Conull.subtypeMeasure m d.source ND) +
          Conull.subtypeMeasure m d.source QD := by
        gcongr
        exact measure_union_le _ _
      _ = mu Q := by rw [hcore, hND, hQD, zero_add, zero_add]
  have hreal : m.real E ≤ mu.real Q :=
    ENNReal.toReal_mono (measure_ne_top mu Q) hmeasure
  have himage : m.real E =
      m.real ((T.toEquiv '' A) ∆ (S.toEquiv '' A)) := by
    simpa [E, SA] using
      WeakTopology.measureReal_inverse_preimage_symmDiff m S T SA
  rw [← himage]
  simpa [mu, Q] using hreal.trans_eq (MarkerCode.measureReal_nextMarker p m)

end

end Submission.Density
