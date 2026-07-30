import Submission.Density
import Submission.GDelta

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology
open scoped symmDiff

namespace Submission.Generic

noncomputable section

variable {X : Type*} [MeasurableSpace X] [StandardBorelSpace X]

structure WeakBallData (m : Measure X) where
  center : Automorphism m
  event : Set X
  radius : ℝ
  measurable_event : MeasurableSet event
  radius_pos : 0 < radius

def WeakBallData.carrier {m : Measure X} (d : WeakBallData m) :
    Set (Automorphism m) :=
  WeakTopology.weakBall m d.center d.event d.radius

omit [StandardBorelSpace X] in
theorem topology_eq_generateFrom_weakBallData (m : Measure X) :
    (inferInstance : TopologicalSpace (Automorphism m)) =
      TopologicalSpace.generateFrom
        (Set.range (WeakBallData.carrier (m := m))) := by
  change TopologicalSpace.generateFrom _ = TopologicalSpace.generateFrom _
  congr 1
  ext U
  constructor
  · rintro ⟨T, A, ε, hA, hε, rfl⟩
    exact ⟨⟨T, A, ε, hA, hε⟩, rfl⟩
  · rintro ⟨d, rfl⟩
    exact ⟨d.center, d.event, d.radius, d.measurable_event,
      d.radius_pos, rfl⟩

set_option maxHeartbeats 800000 in
theorem dense_isWeaklyMixing (m : Measure X)
    [IsProbabilityMeasure m] [NoAtoms m] :
    Dense {T : Automorphism m | IsWeaklyMixing m T} := by
  classical
  let 𝒮 : Set (Set (Automorphism m)) :=
    Set.range (WeakBallData.carrier (m := m))
  let 𝓑 : Set (Set (Automorphism m)) :=
    (fun f : Set (Set (Automorphism m)) ↦ ⋂₀ f) ''
      {f | f.Finite ∧ f ⊆ 𝒮}
  have h𝓑 : TopologicalSpace.IsTopologicalBasis 𝓑 :=
    TopologicalSpace.isTopologicalBasis_of_subbasis
      (topology_eq_generateFrom_weakBallData m)
  rw [h𝓑.dense_iff]
  intro O hO hOne
  rcases hO with ⟨f, ⟨hf, hf𝒮⟩, rfl⟩
  obtain ⟨S, hSf⟩ := hOne
  let d : f → WeakBallData m := fun U ↦ Classical.choose (hf𝒮 U.property)
  have hd (U : f) : (d U).carrier = U :=
    Classical.choose_spec (hf𝒮 U.property)
  letI : Fintype f := hf.fintype
  have hSball (i : f) :
      m.real ((S.toEquiv '' (d i).event) ∆
        ((d i).center.toEquiv '' (d i).event)) < (d i).radius := by
    apply WeakTopology.measureReal_lt_of_mem_weakBall m (d i).center S
      (d i).event
    have hi : S ∈ (i : Set (Automorphism m)) :=
      Set.mem_sInter.mp hSf i i.property
    have : S ∈ (d i).carrier := by simpa only [hd i] using hi
    simpa only [WeakBallData.carrier] using this
  let q : f → ℝ := fun i ↦
    min ((d i).radius -
      m.real ((S.toEquiv '' (d i).event) ∆
        ((d i).center.toEquiv '' (d i).event))) 1
  have hq_pos (i : f) : 0 < q i := by
    dsimp [q]
    exact lt_min (sub_pos.mpr (hSball i)) zero_lt_one
  have hq_one (i : f) : q i ≤ 1 := by
    dsimp [q]
    exact min_le_right _ _
  have hq_margin (i : f) :
      q i ≤ (d i).radius -
        m.real ((S.toEquiv '' (d i).event) ∆
          ((d i).center.toEquiv '' (d i).event)) := by
    dsimp [q]
    exact min_le_left _ _
  have hprod_pos : 0 < ∏ i : f, q i :=
    Finset.prod_pos fun i _ ↦ hq_pos i
  have hprod_one : (∏ i : f, q i) ≤ 1 :=
    Finset.prod_le_one (fun i _ ↦ (hq_pos i).le) fun i _ ↦ hq_one i
  let pReal : ℝ := (∏ i : f, q i) / 2
  have hpReal_pos : 0 < pReal := by
    dsimp [pReal]
    positivity
  have hpReal_one : pReal ≤ 1 := by
    dsimp [pReal]
    linarith
  let p : MarkerCode.Parameter := ⟨pReal, hpReal_pos.le, hpReal_one⟩
  let F : Finset (Set X) :=
    Finset.univ.image fun i : f ↦ (d i).event
  have hF : ∀ A ∈ F, MeasurableSet A := by
    intro A hAF
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hAF
    exact (d i).measurable_event
  obtain ⟨T, hT, hclose⟩ :=
    Density.exists_weaklyMixing_finset_close m S F hF p (by
      simpa only [p, Subtype.coe_mk] using hpReal_pos)
  refine ⟨T, ?_, hT⟩
  rw [Set.mem_sInter]
  intro U hUf
  let i : f := ⟨U, hUf⟩
  have hAi : (d i).event ∈ F := by
    apply Finset.mem_image.mpr
    exact ⟨i, Finset.mem_univ i, rfl⟩
  have hprod_le_q : (∏ j : f, q j) ≤ q i := by
    have h := Finset.prod_le_prod_of_subset_of_le_one
      (f := q) (s := {i}) (t := Finset.univ)
      (Finset.singleton_subset_iff.mpr (Finset.mem_univ i))
      (fun j _ ↦ (hq_pos j).le)
      (fun j _ _ ↦ hq_one j)
    simpa using h
  have hp_margin : (p : ℝ) < (d i).radius -
      m.real ((S.toEquiv '' (d i).event) ∆
        ((d i).center.toEquiv '' (d i).event)) := by
    have hp_prod : pReal < ∏ j : f, q j := by
      dsimp [pReal]
      linarith
    change pReal < _
    exact hp_prod.trans_le (hprod_le_q.trans (hq_margin i))
  have htriangle :
      m.real ((T.toEquiv '' (d i).event) ∆
        ((d i).center.toEquiv '' (d i).event)) ≤
      m.real ((T.toEquiv '' (d i).event) ∆
        (S.toEquiv '' (d i).event)) +
      m.real ((S.toEquiv '' (d i).event) ∆
        ((d i).center.toEquiv '' (d i).event)) :=
    measureReal_symmDiff_le (μ := m)
      (s := T.toEquiv '' (d i).event)
      (t := S.toEquiv '' (d i).event)
      ((d i).center.toEquiv '' (d i).event)
      (measure_ne_top m _) (measure_ne_top m _)
  have hreal :
      m.real ((T.toEquiv '' (d i).event) ∆
        ((d i).center.toEquiv '' (d i).event)) < (d i).radius := by
    have hc := hclose (d i).event hAi
    linarith
  have hmem : T ∈ (d i).carrier := by
    apply (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top m _)).mpr
    exact hreal
  have hi : T ∈ (i : Set (Automorphism m)) := by
    rw [← hd i]
    exact hmem
  simpa only [i] using hi

theorem exists_generic_isWeaklyMixing (m : Measure X)
    [IsProbabilityMeasure m] [NoAtoms m] :
    ∃ G : Set (Automorphism m), IsGδ G ∧ Dense G ∧
      ∀ T ∈ G, IsWeaklyMixing m T := by
  obtain ⟨C, hCcount, hCdense⟩ := exists_countable_measureDense m
  let G := GDelta.genericCriterion m C
  refine ⟨G, GDelta.isGδ_genericCriterion m hCcount hCdense.measurable,
    ?_, ?_⟩
  · exact (dense_isWeaklyMixing m).mono fun T hT ↦
      GDelta.isWeaklyMixing_mem_genericCriterion m T hCdense.measurable hT
  · intro T hTG
    exact GDelta.isWeaklyMixing_of_mem_genericCriterion m T hCdense hTG

end

end Submission.Generic
