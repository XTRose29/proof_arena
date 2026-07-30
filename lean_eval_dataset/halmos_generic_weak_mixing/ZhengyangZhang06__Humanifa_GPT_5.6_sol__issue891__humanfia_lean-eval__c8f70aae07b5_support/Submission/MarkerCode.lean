import Submission.FactorConull
import Submission.GeneralBernoulli

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory ProbabilityTheory

namespace Submission.MarkerCode

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X]

abbrev Parameter := Set.Icc (0 : ℝ) 1

noncomputable def markerMeasure (p : Parameter) : Measure Bool :=
  bernoulliMeasure true false p

instance markerMeasure_isProbability (p : Parameter) :
    IsProbabilityMeasure (markerMeasure p) := by
  unfold markerMeasure
  infer_instance

noncomputable def baseMeasure (p : Parameter) (m : Measure X) :
    Measure (Bool × X) :=
  (markerMeasure p).prod m

instance baseMeasure_isProbability (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] : IsProbabilityMeasure (baseMeasure p m) := by
  unfold baseMeasure
  infer_instance

instance baseMeasure_noAtoms (p : Parameter) (m : Measure X) [NoAtoms m] :
    NoAtoms (baseMeasure p m) := by
  unfold baseMeasure
  infer_instance

abbrev Space (X : Type*) := GeneralBernoulli.Space (Bool × X)

noncomputable def probability (p : Parameter) (m : Measure X) :
    Measure (Space X) :=
  GeneralBernoulli.probability (baseMeasure p m)

instance probability_isProbability (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] : IsProbabilityMeasure (probability p m) := by
  unfold probability
  infer_instance

instance probability_noAtoms (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] [NoAtoms m] :
    NoAtoms (probability p m) := by
  refine ⟨fun w ↦ ?_⟩
  have hsub : ({w} : Set (Space X)) ⊆
      (fun v : Space X ↦ v 0) ⁻¹' {w 0} := by
    intro v hv
    simpa only [Set.mem_singleton_iff, Set.mem_preimage] using congrFun hv 0
  apply measure_mono_null hsub
  letI : ∀ _ : ℤ, IsProbabilityMeasure (baseMeasure p m) :=
    fun _ ↦ baseMeasure_isProbability p m
  have hmp : MeasurePreserving (fun v : Space X ↦ v 0)
      (probability p m) (baseMeasure p m) :=
    measurePreserving_eval_infinitePi (fun _ : ℤ ↦ baseMeasure p m) 0
  rw [hmp.measure_preimage (NullMeasurableSet.of_null (measure_singleton _))]
  exact measure_singleton _

noncomputable def shift (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] : Automorphism (probability p m) :=
  GeneralBernoulli.shift (baseMeasure p m)

def markerAt (n : ℕ) (w : Space X) : Prop :=
  (w (-(n : ℤ))).1 = true

def nextMarker (w : Space X) : Prop :=
  (w 1).1 = true

def hasMarker (w : Space X) : Prop :=
  ∃ n : ℕ, markerAt n w

def searchPred (n : ℕ) (w : Space X) : Prop :=
  markerAt n w ∨ (n = 0 ∧ ¬ hasMarker w)

theorem exists_searchPred (w : Space X) : ∃ n, searchPred n w := by
  classical
  by_cases h : hasMarker w
  · obtain ⟨n, hn⟩ := h
    exact ⟨n, Or.inl hn⟩
  · exact ⟨0, Or.inr ⟨rfl, h⟩⟩

noncomputable def distance (w : Space X) : ℕ :=
  by
    classical
    exact Nat.find (exists_searchPred w)

theorem distance_spec (w : Space X) : searchPred (distance w) w :=
  by
    classical
    unfold distance
    exact Nat.find_spec (exists_searchPred w)

theorem distance_min (w : Space X) {k : ℕ} (hk : k < distance w) :
    ¬ searchPred k w := by
  classical
  unfold distance at hk
  exact Nat.find_min (exists_searchPred w) hk

theorem searchPred_iff_of_hasMarker {n : ℕ} {w : Space X}
    (h : hasMarker w) : searchPred n w ↔ markerAt n w := by
  simp [searchPred, h]

theorem measurableSet_markerAt (n : ℕ) :
    MeasurableSet {w : Space X | markerAt n w} := by
  exact (MeasurableSet.singleton true).preimage
    (measurable_fst.comp (measurable_pi_apply (-(n : ℤ))))

theorem measurableSet_hasMarker :
    MeasurableSet {w : Space X | hasMarker w} := by
  rw [show {w : Space X | hasMarker w} =
      ⋃ n : ℕ, {w : Space X | markerAt n w} by ext; simp [hasMarker]]
  exact MeasurableSet.iUnion measurableSet_markerAt

theorem measurableSet_searchPred (n : ℕ) :
    MeasurableSet {w : Space X | searchPred n w} := by
  by_cases hn : n = 0
  · subst n
    rw [show {w : Space X | searchPred 0 w} =
        {w | markerAt 0 w} ∪ {w | hasMarker w}ᶜ by
      ext w
      simp [searchPred]]
    exact (measurableSet_markerAt (X := X) 0).union measurableSet_hasMarker.compl
  · rw [show {w : Space X | searchPred n w} = {w | markerAt n w} by
      ext w
      simp [searchPred, hn]]
    exact measurableSet_markerAt n

theorem measurable_distance : Measurable (distance : Space X → ℕ) := by
  classical
  unfold distance
  exact measurable_find exists_searchPred measurableSet_searchPred

def stateAt {m : Measure X} (S : Automorphism m)
    (n : ℕ) (w : Space X) : X :=
  ((S.toEquiv : X → X)^[n]) (w (-(n : ℤ))).2

theorem measurable_stateAt {m : Measure X} (S : Automorphism m) (n : ℕ) :
    Measurable (stateAt S n : Space X → X) := by
  exact (S.measurePreserving.iterate n).measurable.comp
    (measurable_snd.comp (measurable_pi_apply (-(n : ℤ))))

noncomputable def code {m : Measure X} (S : Automorphism m) (w : Space X) : X :=
  stateAt S (distance w) w

theorem measurable_code {m : Measure X} (S : Automorphism m) :
    Measurable (code S : Space X → X) := by
  classical
  change Measurable (fun w ↦ stateAt S (Nat.find (exists_searchPred w)) w)
  exact Measurable.find (measurable_stateAt S) measurableSet_searchPred exists_searchPred

def firstEvent (n : ℕ) : Set (Space X) :=
  {w | markerAt n w ∧ ∀ k < n, ¬ markerAt k w}

def previousFalse (n : ℕ) : Set (Space X) :=
  {w | ∀ k < n, ¬ markerAt k w}

def previousTimes (n : ℕ) : Finset ℤ :=
  (Finset.range n).image fun k : ℕ ↦ -(k : ℤ)

theorem current_not_mem_previousTimes (n : ℕ) :
    -(n : ℤ) ∉ previousTimes n := by
  intro h
  rw [previousTimes, Finset.mem_image] at h
  obtain ⟨k, hk, hkn⟩ := h
  have hklt : k < n := Finset.mem_range.mp hk
  have : k = n := by exact_mod_cast neg_inj.mp hkn
  omega

theorem measurableSet_previousFalse (n : ℕ) :
    MeasurableSet (previousFalse (X := X) n) := by
  rw [show previousFalse (X := X) n =
      ⋂ k : Fin n, {w : Space X | ¬ markerAt (k : ℕ) w} by
    ext w
    rw [Set.mem_iInter]
    constructor
    · exact fun h k ↦ h k k.isLt
    · exact fun h k hk ↦ h ⟨k, hk⟩]
  exact MeasurableSet.iInter fun k ↦ (measurableSet_markerAt k).compl

theorem measure_previousFalse_inter_coordinate
    (p : Parameter) (m : Measure X) [IsProbabilityMeasure m]
    (n : ℕ) {B : Set (Bool × X)} (hB : MeasurableSet B) :
    probability p m
        (previousFalse n ∩ (fun w : Space X ↦ w (-(n : ℤ))) ⁻¹' B) =
      probability p m (previousFalse n) * baseMeasure p m B := by
  classical
  let I := previousTimes n
  let j : ℤ := -(n : ℤ)
  have hj : j ∉ I := current_not_mem_previousTimes n
  have hdis : Disjoint I {j} := Finset.disjoint_singleton_right.mpr hj
  let F : Space X → ((i : I) → Bool × X) := fun w i ↦ w i
  let G : Space X → ((i : ({j} : Finset ℤ)) → Bool × X) := fun w i ↦ w i
  have hind :=
    (GeneralBernoulli.independent_coordinates (baseMeasure p m)).indepFun_finset
      I {j} hdis (by fun_prop)
  have hind' : IndepFun F (fun w : Space X ↦ w j) (probability p m) := by
    let take : ((i : ({j} : Finset ℤ)) → Bool × X) → Bool × X :=
      fun a ↦ a ⟨j, Finset.mem_singleton_self j⟩
    have htake : Measurable take := measurable_pi_apply _
    refine (hind.comp measurable_id htake).congr ?_ ?_
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
    · exact Filter.Eventually.of_forall fun _ ↦ rfl
  have hmem (k : Fin n) : -(k : ℤ) ∈ I := by
    unfold I previousTimes
    apply Finset.mem_image.mpr
    exact ⟨k, Finset.mem_range.mpr k.isLt, rfl⟩
  let A : Set ((i : I) → Bool × X) :=
    {a | ∀ k : Fin n, (a ⟨-(k : ℤ), hmem k⟩).1 = false}
  have hA : MeasurableSet A := by
    rw [show A = ⋂ k : Fin n,
        {a | (a ⟨-(k : ℤ), hmem k⟩).1 = false} by
      ext a
      rw [Set.mem_iInter]
      rfl]
    apply MeasurableSet.iInter
    intro k
    exact (MeasurableSet.singleton false).preimage
      (measurable_fst.comp (measurable_pi_apply
        (⟨-(k : ℤ), hmem k⟩ : I)))
  have hFA : F ⁻¹' A = previousFalse n := by
    ext w
    change (∀ k : Fin n, (w (-(k : ℤ))).1 = false) ↔
      ∀ k : ℕ, k < n → ¬ (w (-(k : ℤ))).1 = true
    constructor
    · intro hw k hk
      have hfalse := hw ⟨k, hk⟩
      intro htrue
      exact Bool.false_ne_true (hfalse.symm.trans htrue)
    · intro hw k
      have hnot := hw k k.isLt
      exact Bool.eq_false_of_not_eq_true hnot
  have heq := hind'.measure_inter_preimage_eq_mul A B hA hB
  rw [hFA] at heq
  have hcoord :=
    (measurePreserving_eval_infinitePi
      (fun _ : ℤ ↦ baseMeasure p m) j).measure_preimage hB.nullMeasurableSet
  change probability p m ((fun w : Space X ↦ w j) ⁻¹' B) =
    baseMeasure p m B at hcoord
  rw [hcoord] at heq
  exact heq

theorem measure_code_inter_firstEvent
    (p : Parameter) (m : Measure X) [IsProbabilityMeasure m]
    (S : Automorphism m) (n : ℕ) {A : Set X} (hA : MeasurableSet A) :
    probability p m ((code S ⁻¹' A) ∩ firstEvent n) =
      probability p m (firstEvent n) * m A := by
  classical
  have hd_of {w : Space X} (hw : w ∈ firstEvent n) : distance w = n := by
    have hhas : hasMarker w := ⟨n, hw.1⟩
    apply Nat.le_antisymm
    · exact Nat.find_min' (exists_searchPred w)
        ((searchPred_iff_of_hasMarker hhas).2 hw.1)
    · apply Nat.le_of_not_gt
      intro hlt
      have hmark : markerAt (distance w) w :=
        (searchPred_iff_of_hasMarker hhas).1 (distance_spec w)
      exact hw.2 (distance w) hlt hmark
  let A' : Set X := ((S.toEquiv : X → X)^[n]) ⁻¹' A
  have hA' : MeasurableSet A' :=
    hA.preimage (S.measurePreserving.iterate n).measurable
  let B : Set (Bool × X) := {true} ×ˢ A'
  let B₀ : Set (Bool × X) := {true} ×ˢ Set.univ
  have hB : MeasurableSet B := (MeasurableSet.singleton true).prod hA'
  have hB₀ : MeasurableSet B₀ :=
    (MeasurableSet.singleton true).prod MeasurableSet.univ
  have hset : (code S ⁻¹' A) ∩ firstEvent n =
      previousFalse n ∩ (fun w : Space X ↦ w (-(n : ℤ))) ⁻¹' B := by
    ext w
    constructor
    · rintro ⟨hwA, hwfirst⟩
      refine ⟨hwfirst.2, ?_⟩
      change (w (-(n : ℤ))).1 = true ∧
        ((S.toEquiv : X → X)^[n]) (w (-(n : ℤ))).2 ∈ A
      refine ⟨hwfirst.1, ?_⟩
      have hd := hd_of hwfirst
      change ((S.toEquiv : X → X)^[distance w])
        (w (-(distance w : ℤ))).2 ∈ A at hwA
      rw [hd] at hwA
      exact hwA
    · rintro ⟨hwprev, hwB⟩
      change (w (-(n : ℤ))).1 = true ∧
        ((S.toEquiv : X → X)^[n]) (w (-(n : ℤ))).2 ∈ A at hwB
      have hwfirst : w ∈ firstEvent n := ⟨hwB.1, hwprev⟩
      refine ⟨?_, hwfirst⟩
      have hd := hd_of hwfirst
      change ((S.toEquiv : X → X)^[distance w])
        (w (-(distance w : ℤ))).2 ∈ A
      rw [hd]
      exact hwB.2
  have hfirst : firstEvent (X := X) n =
      previousFalse n ∩ (fun w : Space X ↦ w (-(n : ℤ))) ⁻¹' B₀ := by
    ext w
    constructor
    · intro hw
      exact ⟨hw.2, ⟨hw.1, Set.mem_univ _⟩⟩
    · rintro ⟨hwprev, hwmark, _⟩
      exact ⟨hwmark, hwprev⟩
  rw [hset, hfirst,
    measure_previousFalse_inter_coordinate p m n hB,
    measure_previousFalse_inter_coordinate p m n hB₀]
  unfold B B₀ baseMeasure
  rw [Measure.prod_prod, Measure.prod_prod,
    (S.measurePreserving.iterate n).measure_preimage hA.nullMeasurableSet,
    measure_univ, mul_one]
  ring

theorem measurableSet_firstEvent (n : ℕ) : MeasurableSet (firstEvent (X := X) n) := by
  rw [show firstEvent (X := X) n =
      {w : Space X | markerAt n w} ∩
        ⋂ k : Fin n, {w | ¬ markerAt (k : ℕ) w} by
    ext w
    rw [Set.mem_inter_iff, Set.mem_setOf_eq, Set.mem_iInter]
    constructor
    · rintro ⟨hn, hprev⟩
      exact ⟨hn, fun k ↦ hprev k k.isLt⟩
    · rintro ⟨hn, hprev⟩
      exact ⟨hn, fun k hk ↦ hprev ⟨k, hk⟩⟩]
  exact (measurableSet_markerAt n).inter
    (MeasurableSet.iInter fun k ↦ (measurableSet_markerAt k).compl)

theorem distance_eq_of_mem_firstEvent {n : ℕ} {w : Space X}
    (hw : w ∈ firstEvent n) : distance w = n := by
  classical
  have hhas : hasMarker w := ⟨n, hw.1⟩
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_searchPred w)
      ((searchPred_iff_of_hasMarker hhas).2 hw.1)
  · apply Nat.le_of_not_gt
    intro hlt
    have hmark : markerAt (distance w) w :=
      (searchPred_iff_of_hasMarker hhas).1 (distance_spec w)
    exact hw.2 (distance w) hlt hmark

theorem mem_firstEvent_distance {w : Space X} (h : hasMarker w) :
    w ∈ firstEvent (distance w) := by
  classical
  refine ⟨(searchPred_iff_of_hasMarker h).1 (distance_spec w), ?_⟩
  intro k hk
  exact fun hmark ↦ distance_min w hk
    ((searchPred_iff_of_hasMarker h).2 hmark)

@[simp]
theorem markerAt_shift_succ {m : Measure X} [IsProbabilityMeasure m]
    (p : Parameter) (n : ℕ) (w : Space X) :
    markerAt (n + 1) ((shift p m).toEquiv w) ↔ markerAt n w := by
  change ((GeneralBernoulli.shiftEquiv w (-((n + 1 : ℕ) : ℤ))).1 = true) ↔
    (w (-(n : ℤ))).1 = true
  rw [GeneralBernoulli.shiftEquiv_apply]
  have hidx : -((n + 1 : ℕ) : ℤ) + 1 = -(n : ℤ) := by omega
  rw [hidx]

@[simp]
theorem markerAt_shift_zero {m : Measure X} [IsProbabilityMeasure m]
    (p : Parameter) (w : Space X) :
    markerAt 0 ((shift p m).toEquiv w) ↔ nextMarker w := by
  change ((GeneralBernoulli.shiftEquiv w 0).1 = true) ↔ (w 1).1 = true
  rw [GeneralBernoulli.shiftEquiv_apply]
  simp

theorem distance_shift {m : Measure X} [IsProbabilityMeasure m]
    (p : Parameter) {w : Space X} (hhas : hasMarker w)
    (hnext : ¬ nextMarker w) :
    distance ((shift p m).toEquiv w) = distance w + 1 := by
  classical
  let d := distance w
  have hdmark : markerAt d w :=
    (searchPred_iff_of_hasMarker hhas).1 (distance_spec w)
  have hshiftMark : markerAt (d + 1) ((shift p m).toEquiv w) :=
    (markerAt_shift_succ (m := m) p d w).2 hdmark
  have hshiftHas : hasMarker ((shift p m).toEquiv w) := ⟨d + 1, hshiftMark⟩
  apply Nat.le_antisymm
  · exact Nat.find_min' (exists_searchPred ((shift p m).toEquiv w))
      ((searchPred_iff_of_hasMarker hshiftHas).2 hshiftMark)
  · apply Nat.le_of_not_gt
    intro hlt
    generalize hq : distance ((shift p m).toEquiv w) = q at hlt
    have hqmark : markerAt q ((shift p m).toEquiv w) := by
      rw [← hq]
      exact
      (searchPred_iff_of_hasMarker hshiftHas).1
        (distance_spec ((shift p m).toEquiv w))
    cases q with
    | zero => exact hnext ((markerAt_shift_zero (m := m) p w).1 hqmark)
    | succ k =>
        have hk : k < d := by omega
        have hkmark : markerAt k w := by
          apply (markerAt_shift_succ (m := m) p k w).1
          simpa only [Nat.succ_eq_add_one] using hqmark
        exact distance_min w hk ((searchPred_iff_of_hasMarker hhas).2 hkmark)

theorem code_shift {m : Measure X} [IsProbabilityMeasure m]
    (p : Parameter) (S : Automorphism m) {w : Space X}
    (hhas : hasMarker w) (hnext : ¬ nextMarker w) :
    code S ((shift p m).toEquiv w) = S.toEquiv (code S w) := by
  classical
  change stateAt S (distance ((shift p m).toEquiv w)) ((shift p m).toEquiv w) =
    S.toEquiv (stateAt S (distance w) w)
  rw [distance_shift p hhas hnext]
  unfold stateAt
  rw [Function.iterate_succ_apply']
  apply congrArg S.toEquiv
  apply congrArg ((S.toEquiv : X → X)^[distance w])
  change (GeneralBernoulli.shiftEquiv w
    (-((distance w + 1 : ℕ) : ℤ))).2 = (w (-(distance w : ℤ))).2
  rw [GeneralBernoulli.shiftEquiv_apply]
  have hidx : -((distance w + 1 : ℕ) : ℤ) + 1 =
      -(distance w : ℤ) := by omega
  rw [hidx]

end

end Submission.MarkerCode
