import Submission.MeanCorrelation
import Mathlib.MeasureTheory.Measure.SeparableMeasure
import Mathlib.Topology.GDelta.Basic

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology Finset Function
open scoped symmDiff

namespace Submission.GDelta

noncomputable section

variable {X : Type*} [MeasurableSpace X]

theorem measureReal_inter_symmDiff_le (m : Measure X) [IsFiniteMeasure m]
    (A B C D : Set X) :
    m.real ((A ∩ B) ∆ (C ∩ D)) ≤
      m.real (A ∆ C) + m.real (B ∆ D) := by
  calc
    m.real ((A ∩ B) ∆ (C ∩ D)) ≤
        m.real ((A ∆ C) ∪ (B ∆ D)) :=
      measureReal_mono (by grind)
    _ ≤ m.real (A ∆ C) + m.real (B ∆ D) :=
      measureReal_union_le _ _

theorem abs_mul_sub_mul_le {a b c d : ℝ}
    (hb0 : 0 ≤ b) (hb1 : b ≤ 1) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    |a * b - c * d| ≤ |a - c| + |b - d| := by
  calc
    |a * b - c * d| = |(a - c) * b + c * (b - d)| := by ring_nf
    _ ≤ |(a - c) * b| + |c * (b - d)| := abs_add_le _ _
    _ = |a - c| * b + c * |b - d| := by
      rw [abs_mul, abs_mul, abs_of_nonneg hb0, abs_of_nonneg hc0]
    _ ≤ |a - c| + |b - d| := by
      nlinarith [abs_nonneg (a - c), abs_nonneg (b - d)]

theorem product_perturbation (m : Measure X) [IsProbabilityMeasure m]
    (A B C D : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    |m.real A * m.real B - m.real C * m.real D| ≤
      m.real (A ∆ C) + m.real (B ∆ D) := by
  refine (abs_mul_sub_mul_le measureReal_nonneg measureReal_le_one
    measureReal_nonneg measureReal_le_one).trans ?_
  exact add_le_add
    (abs_measureReal_sub_le_measureReal_symmDiff
      hA.nullMeasurableSet hC.nullMeasurableSet)
    (abs_measureReal_sub_le_measureReal_symmDiff
      hB.nullMeasurableSet hD.nullMeasurableSet)

theorem intersection_perturbation (m : Measure X) [IsProbabilityMeasure m]
    (T : Automorphism m) (k : ℕ) (A B C D : Set X)
    (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    |m.real (WeakTopology.iteratePreimage T k A ∩ B) -
        m.real (WeakTopology.iteratePreimage T k C ∩ D)| ≤
      m.real (A ∆ C) + m.real (B ∆ D) := by
  have hpre : WeakTopology.iteratePreimage T k A ∆
      WeakTopology.iteratePreimage T k C =
      WeakTopology.iteratePreimage T k (A ∆ C) := by
    ext x
    simp [WeakTopology.iteratePreimage]
  calc
    |m.real (WeakTopology.iteratePreimage T k A ∩ B) -
        m.real (WeakTopology.iteratePreimage T k C ∩ D)| ≤
        m.real ((WeakTopology.iteratePreimage T k A ∩ B) ∆
          (WeakTopology.iteratePreimage T k C ∩ D)) :=
      abs_measureReal_sub_le_measureReal_symmDiff
        ((WeakTopology.measurableSet_iteratePreimage T k hA).inter hB).nullMeasurableSet
        ((WeakTopology.measurableSet_iteratePreimage T k hC).inter hD).nullMeasurableSet
    _ ≤ m.real (WeakTopology.iteratePreimage T k A ∆
          WeakTopology.iteratePreimage T k C) + m.real (B ∆ D) :=
      measureReal_inter_symmDiff_le m _ _ _ _
    _ = m.real (A ∆ C) + m.real (B ∆ D) := by
      rw [hpre]
      exact congrArg (fun z : ℝ ↦ z + m.real (B ∆ D))
        (congrArg ENNReal.toReal
          ((T.measurePreserving.iterate k).measure_preimage
            (hA.symmDiff hC).nullMeasurableSet))

theorem correlationTerm_perturbation (m : Measure X)
    [IsProbabilityMeasure m] (T : Automorphism m) (k : ℕ)
    (A B C D : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    |Criterion.correlationTerm m T A B k -
        Criterion.correlationTerm m T C D k| ≤
      2 * (m.real (A ∆ C) + m.real (B ∆ D)) := by
  let a := m.real (WeakTopology.iteratePreimage T k A ∩ B)
  let b := m.real (WeakTopology.iteratePreimage T k C ∩ D)
  let p := m.real A * m.real B
  let q := m.real C * m.real D
  have hab : |a - b| ≤ m.real (A ∆ C) + m.real (B ∆ D) :=
    intersection_perturbation m T k A B C D hA hB hC hD
  have hpq : |p - q| ≤ m.real (A ∆ C) + m.real (B ∆ D) :=
    product_perturbation m A B C D hA hB hC hD
  change abs (abs (a - p) - abs (b - q)) ≤ _
  calc
    abs (abs (a - p) - abs (b - q)) ≤ |(a - p) - (b - q)| :=
      abs_abs_sub_abs_le_abs_sub _ _
    _ ≤ |a - b| + |p - q| := by
      calc
        |(a - p) - (b - q)| = |(a - b) - (p - q)| := by ring_nf
        _ ≤ |a - b| + |p - q| := abs_sub _ _
    _ ≤ 2 * (m.real (A ∆ C) + m.real (B ∆ D)) := by linarith

theorem correlationAverage_le_perturbation (m : Measure X)
    [IsProbabilityMeasure m] (T : Automorphism m) {n : ℕ} (hn : 0 < n)
    (A B C D : Set X) (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hC : MeasurableSet C) (hD : MeasurableSet D) :
    Criterion.correlationAverage m T A B n ≤
      Criterion.correlationAverage m T C D n +
        2 * (m.real (A ∆ C) + m.real (B ∆ D)) := by
  let e := 2 * (m.real (A ∆ C) + m.real (B ∆ D))
  have hterm (k : ℕ) : Criterion.correlationTerm m T A B k ≤
      Criterion.correlationTerm m T C D k + e := by
    have h := correlationTerm_perturbation m T k A B C D hA hB hC hD
    change |Criterion.correlationTerm m T A B k -
      Criterion.correlationTerm m T C D k| ≤ e at h
    linarith [le_abs_self (Criterion.correlationTerm m T A B k -
      Criterion.correlationTerm m T C D k)]
  have hsum : (∑ k ∈ range n, Criterion.correlationTerm m T A B k) ≤
      ∑ k ∈ range n, (Criterion.correlationTerm m T C D k + e) :=
    sum_le_sum fun k _ ↦ hterm k
  rw [sum_add_distrib, sum_const, card_range] at hsum
  simp only [nsmul_eq_mul] at hsum
  unfold Criterion.correlationAverage
  calc
    (∑ k ∈ range n, Criterion.correlationTerm m T A B k) / (n : ℝ) ≤
        ((∑ k ∈ range n, Criterion.correlationTerm m T C D k) +
          (n : ℝ) * e) / (n : ℝ) :=
      div_le_div_of_nonneg_right hsum (Nat.cast_nonneg n)
    _ = (∑ k ∈ range n, Criterion.correlationTerm m T C D k) /
        (n : ℝ) + e := by
      field_simp [Nat.ne_of_gt hn]

def lateSmallSet (m : Measure X) (A B : Set X) (j N : ℕ) :
    Set (Automorphism m) :=
  ⋃ n ∈ Set.Ici N,
    {T | MeanCorrelation.squareCorrelationAverage m T A B n <
      1 / (j + 1 : ℝ)}

def genericCriterion (m : Measure X) (C : Set (Set X)) :
    Set (Automorphism m) :=
  ⋂ A ∈ C, ⋂ B ∈ C, ⋂ j : ℕ, ⋂ N : ℕ,
    lateSmallSet m A B j N

theorem isOpen_lateSmallSet (m : Measure X) [IsFiniteMeasure m]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (j N : ℕ) : IsOpen (lateSmallSet m A B j N) := by
  apply isOpen_biUnion
  intro n hn
  exact MeanCorrelation.isOpen_squareCorrelationAverage_lt m hA hB n _

theorem isGδ_genericCriterion (m : Measure X) [IsFiniteMeasure m]
    {C : Set (Set X)} (hC : C.Countable)
    (hCmeas : ∀ A ∈ C, MeasurableSet A) :
    IsGδ (genericCriterion m C) := by
  unfold genericCriterion
  apply IsGδ.biInter hC
  intro A hAC
  apply IsGδ.biInter hC
  intro B hBC
  apply IsGδ.iInter
  intro j
  apply IsGδ.iInter
  intro N
  exact (isOpen_lateSmallSet m (hCmeas A hAC) (hCmeas B hBC) j N).isGδ

theorem mem_genericCriterion_iff (m : Measure X) (T : Automorphism m)
    (C : Set (Set X)) :
    T ∈ genericCriterion m C ↔
      ∀ A ∈ C, ∀ B ∈ C, ∀ j N : ℕ, ∃ n ≥ N,
        MeanCorrelation.squareCorrelationAverage m T A B n <
          1 / (j + 1 : ℝ) := by
  simp only [genericCriterion, lateSmallSet, Set.mem_iInter,
    Set.mem_iUnion, Set.mem_Ici, Set.mem_setOf_eq]
  aesop

theorem isWeaklyMixing_of_mem_genericCriterion (m : Measure X)
    [IsProbabilityMeasure m] (T : Automorphism m) {C : Set (Set X)}
    (hDense : m.MeasureDense C) (hT : T ∈ genericCriterion m C) :
    IsWeaklyMixing m T := by
  rw [Criterion.isWeaklyMixing_iff]
  intro A B hA hB
  apply tendsto_order.mpr
  constructor
  · intro a ha
    filter_upwards [] with n
    have hnonneg : 0 ≤ Criterion.correlationAverage m T A B n := by
      unfold Criterion.correlationAverage
      exact div_nonneg (sum_nonneg fun _ _ ↦ abs_nonneg _)
        (Nat.cast_nonneg n)
    exact lt_of_lt_of_le ha hnonneg
  · intro ε hε
    let δ := ε / 16
    have hδ : 0 < δ := by positivity
    obtain ⟨C₀, hC₀C, hAC₀⟩ := hDense.approx A hA (measure_ne_top m A) δ hδ
    obtain ⟨D₀, hD₀C, hBD₀⟩ := hDense.approx B hB (measure_ne_top m B) δ hδ
    have hC₀ := hDense.measurable C₀ hC₀C
    have hD₀ := hDense.measurable D₀ hD₀C
    have hdA : m.real (A ∆ C₀) < δ :=
      (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top m _)).mp hAC₀
    have hdB : m.real (B ∆ D₀) < δ :=
      (ENNReal.lt_ofReal_iff_toReal_lt (measure_ne_top m _)).mp hBD₀
    have hlate := (mem_genericCriterion_iff m T C).mp hT C₀ hC₀C D₀ hD₀C
    have hsquare : Tendsto
        (MeanCorrelation.squareCorrelationAverage m T C₀ D₀)
        atTop (nhds 0) :=
      MeanCorrelation.tendsto_square_of_arbitrarily_late_small m T hC₀ hD₀
        (fun r hr N ↦ by
          obtain ⟨j, hj⟩ := exists_nat_one_div_lt hr
          obtain ⟨n, hnN, hn⟩ := hlate j N
          exact ⟨n, hnN, hn.trans hj⟩)
    have hCD : Tendsto (Criterion.correlationAverage m T C₀ D₀)
        atTop (nhds 0) :=
      (MeanCorrelation.tendsto_correlationAverage_iff_square
        m T C₀ D₀).mpr hsquare
    have hev := (tendsto_order.mp hCD).2 (ε / 2) (by linarith)
    filter_upwards [hev, eventually_gt_atTop 0] with n hnCD hnpos
    have hpert := correlationAverage_le_perturbation m T hnpos
      A B C₀ D₀ hA hB hC₀ hD₀
    dsimp [δ] at hdA hdB
    linarith

theorem isWeaklyMixing_mem_genericCriterion (m : Measure X)
    [IsProbabilityMeasure m] (T : Automorphism m) {C : Set (Set X)}
    (hCmeas : ∀ A ∈ C, MeasurableSet A) (hT : IsWeaklyMixing m T) :
    T ∈ genericCriterion m C := by
  rw [mem_genericCriterion_iff]
  intro A hAC B hBC j N
  have habslim := hT A B (hCmeas A hAC) (hCmeas B hBC)
  have hsqlim := (MeanCorrelation.tendsto_correlationAverage_iff_square
    m T A B).mp habslim
  have hpos : 0 < 1 / (j + 1 : ℝ) := by positivity
  have hev := (tendsto_order.mp hsqlim).2 _ hpos
  obtain ⟨M, hM⟩ := eventually_atTop.mp hev
  exact ⟨max N M, le_max_left _ _, hM _ (le_max_right _ _)⟩

end

end Submission.GDelta
