import Submission.MarkerCode

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory ProbabilityTheory Filter Topology

namespace Submission.MarkerCode

noncomputable section

set_option linter.unusedSectionVars false

variable {X : Type*} [MeasurableSpace X]

theorem measurableSet_nextMarker :
    MeasurableSet {w : Space X | nextMarker w} :=
  (MeasurableSet.singleton true).preimage
    (measurable_fst.comp (measurable_pi_apply 1))

theorem measureReal_nextMarker (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] :
    (probability p m).real {w : Space X | nextMarker w} = p := by
  have hmp : MeasurePreserving (fun w : Space X ↦ (w 1).1)
      (probability p m) (markerMeasure p) := by
    exact measurePreserving_fst.comp
      (measurePreserving_eval_infinitePi (fun _ : ℤ ↦ baseMeasure p m) 1)
  have hmeasure := hmp.measure_preimage
    (MeasurableSet.singleton true).nullMeasurableSet
  calc
    (probability p m).real {w : Space X | nextMarker w} =
        (markerMeasure p).real {true} := congrArg ENNReal.toReal hmeasure
    _ = p := by
      unfold markerMeasure
      exact bernoulliMeasure_real_apply_of_mem_of_notMem p
        (MeasurableSet.singleton true) (Set.mem_singleton true)
        (by simp)

theorem baseMeasure_false (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] :
    baseMeasure p m ({false} ×ˢ Set.univ) =
      ENNReal.ofReal (1 - (p : ℝ)) := by
  unfold baseMeasure markerMeasure
  rw [Measure.prod_prod, measure_univ, mul_one,
    bernoulliMeasure_apply_of_notMem_of_mem p
      (MeasurableSet.singleton false) (by simp) (Set.mem_singleton false)]
  rw [← unitInterval.coe_symm_eq p]
  simpa using ENNReal.coe_nnreal_eq (unitInterval.toNNReal (unitInterval.symm p))

theorem measure_previousFalse (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] (n : ℕ) :
    probability p m (previousFalse n) =
      (ENNReal.ofReal (1 - (p : ℝ))) ^ n := by
  induction n with
  | zero => simp [previousFalse]
  | succ n ih =>
      let B : Set (Bool × X) := {false} ×ˢ Set.univ
      have hB : MeasurableSet B :=
        (MeasurableSet.singleton false).prod MeasurableSet.univ
      have hset : previousFalse (X := X) (n + 1) =
          previousFalse n ∩
            (fun w : Space X ↦ w (-(n : ℤ))) ⁻¹' B := by
        ext w
        constructor
        · intro hw
          refine ⟨fun k hk ↦ hw k (by omega), ?_⟩
          have hnfalse : (w (-(n : ℤ))).1 = false :=
            Bool.eq_false_of_not_eq_true (hw n (by omega))
          simpa [B] using hnfalse
        · rintro ⟨hw, hn⟩ k hk
          have hnfalse : (w (-(n : ℤ))).1 = false := by
            simpa [B] using hn
          by_cases hkn : k < n
          · exact hw k hkn
          · have hkeq : k = n := by omega
            subst k
            exact fun htrue ↦ Bool.false_ne_true (hnfalse.symm.trans htrue)
      rw [hset, measure_previousFalse_inter_coordinate p m n hB,
        ih, baseMeasure_false]
      exact (pow_succ _ n).symm

theorem antitone_previousFalse :
    Antitone (previousFalse (X := X)) := by
  intro a b hab w hw k hk
  exact hw k (lt_of_lt_of_le hk hab)

theorem noMarker_null (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] (hp : 0 < (p : ℝ)) :
    probability p m {w : Space X | ¬ hasMarker w} = 0 := by
  have hset : {w : Space X | ¬ hasMarker w} =
      ⋂ n : ℕ, previousFalse n := by
    ext w
    simp only [Set.mem_setOf_eq, Set.mem_iInter, hasMarker, previousFalse]
    change (¬ ∃ k : ℕ, markerAt k w) ↔
      ∀ n k : ℕ, k < n → ¬ markerAt k w
    constructor
    · exact fun h _ k _ hk ↦ h ⟨k, hk⟩
    · rintro h ⟨k, hk⟩
      exact h (k + 1) k (by omega) hk
  have hlimMeasure : Tendsto
      (fun n ↦ probability p m (previousFalse n)) atTop
      (𝓝 (probability p m (⋂ n : ℕ, previousFalse n))) :=
    tendsto_measure_iInter_atTop
      (fun n ↦ (measurableSet_previousFalse n).nullMeasurableSet)
      antitone_previousFalse ⟨0, measure_ne_top _ _⟩
  have hq : ENNReal.ofReal (1 - (p : ℝ)) < 1 := by
    rw [ENNReal.ofReal_lt_one]
    linarith
  have hlimZero : Tendsto
      (fun n ↦ probability p m (previousFalse n)) atTop (𝓝 0) := by
    simpa only [measure_previousFalse p m] using
      ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hq
  rw [hset]
  exact tendsto_nhds_unique hlimMeasure hlimZero

theorem hasMarker_ae (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] (hp : 0 < (p : ℝ)) :
    ∀ᵐ w ∂probability p m, hasMarker w := by
  rw [ae_iff]
  simpa only [Set.mem_setOf_eq] using noMarker_null p m hp

theorem pairwise_disjoint_firstEvent :
    Pairwise (fun i j : ℕ ↦
      Disjoint (firstEvent (X := X) i) (firstEvent (X := X) j)) := by
  intro i j hij
  rw [Set.disjoint_left]
  intro w hi hj
  rcases lt_or_gt_of_ne hij with hijlt | hjilt
  · exact hj.2 i hijlt hi.1
  · exact hi.2 j hjilt hj.1

theorem iUnion_firstEvent :
    ⋃ n : ℕ, firstEvent (X := X) n = {w | hasMarker w} := by
  ext w
  constructor
  · intro hw
    obtain ⟨n, hn⟩ := Set.mem_iUnion.mp hw
    exact ⟨n, hn.1⟩
  · intro hw
    exact Set.mem_iUnion.2 ⟨distance w, mem_firstEvent_distance hw⟩

theorem measurePreserving_code (p : Parameter) (m : Measure X)
    [IsProbabilityMeasure m] (hp : 0 < (p : ℝ))
    (S : Automorphism m) :
    MeasurePreserving (code S) (probability p m) m := by
  let mu := probability p m
  have hHas : mu {w : Space X | hasMarker w} = 1 := by
    rw [measure_of_measure_compl_eq_zero, measure_univ]
    change probability p m {w : Space X | ¬ hasMarker w} = 0
    exact noMarker_null p m hp
  refine ⟨measurable_code S, ?_⟩
  ext A hA
  rw [Measure.map_apply (measurable_code S) hA]
  let E : Set (Space X) := code S ⁻¹' A
  have hE : MeasurableSet E := hA.preimage (measurable_code S)
  have hpiecesDisjoint : Pairwise
      (fun i j : ℕ ↦ Disjoint (E ∩ firstEvent i) (E ∩ firstEvent j)) := by
    intro i j hij
    rw [Set.disjoint_left]
    intro w hi hj
    exact (Set.disjoint_left.mp (pairwise_disjoint_firstEvent hij)) hi.2 hj.2
  have hpiecesMeasurable (n : ℕ) :
      MeasurableSet (E ∩ firstEvent n) :=
    hE.inter (measurableSet_firstEvent n)
  have hpiecesUnion : ⋃ n : ℕ, E ∩ firstEvent n =
      E ∩ {w : Space X | hasMarker w} := by
    rw [← Set.inter_iUnion, iUnion_firstEvent]
  calc
    mu E = mu ({w : Space X | hasMarker w} ∩ E) := by
      apply measure_congr
      filter_upwards [hasMarker_ae p m hp] with w hw
      apply propext
      constructor
      · exact fun hwE => ⟨hw, hwE⟩
      · exact fun hwE => hwE.2
    _ = mu (E ∩ {w : Space X | hasMarker w}) := by rw [Set.inter_comm]
    _ = mu (⋃ n : ℕ, E ∩ firstEvent n) := congrArg mu hpiecesUnion.symm
    _ = ∑' n : ℕ, mu (E ∩ firstEvent n) :=
      measure_iUnion hpiecesDisjoint hpiecesMeasurable
    _ = ∑' n : ℕ, mu (firstEvent n) * m A := by
      apply tsum_congr
      intro n
      exact measure_code_inter_firstEvent p m S n hA
    _ = (∑' n : ℕ, mu (firstEvent n)) * m A :=
      ENNReal.tsum_mul_right
    _ = mu (⋃ n : ℕ, firstEvent n) * m A := by
      rw [measure_iUnion pairwise_disjoint_firstEvent measurableSet_firstEvent]
    _ = m A := by rw [iUnion_firstEvent, hHas, one_mul]

end

end Submission.MarkerCode
