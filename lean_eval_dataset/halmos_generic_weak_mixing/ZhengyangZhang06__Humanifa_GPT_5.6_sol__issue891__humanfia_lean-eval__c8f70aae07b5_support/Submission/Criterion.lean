import Submission.WeakTopology

open LeanEval.Dynamics.HalmosGenericWeakMixingProblem
open MeasureTheory Filter Topology
open scoped symmDiff

namespace Submission.Criterion

variable {X : Type*} [MeasurableSpace X]

def correlationTerm (m : Measure X) (T : Automorphism m)
    (A B : Set X) (k : ℕ) : ℝ :=
  |m.real (WeakTopology.iteratePreimage T k A ∩ B) -
    m.real A * m.real B|

noncomputable def correlationAverage (m : Measure X) (T : Automorphism m)
    (A B : Set X) (n : ℕ) : ℝ :=
  (∑ k ∈ Finset.range n, correlationTerm m T A B k) / (n : ℝ)

theorem isWeaklyMixing_iff (m : Measure X) (T : Automorphism m) :
    IsWeaklyMixing m T ↔
      ∀ A B : Set X, MeasurableSet A → MeasurableSet B →
        Tendsto (correlationAverage m T A B) atTop (𝓝 0) := by
  rfl

theorem abs_correlationTerm_sub_le (m : Measure X) [IsFiniteMeasure m]
    (S T : Automorphism m) {A B : Set X}
    (hA : MeasurableSet A) (hB : MeasurableSet B) (k : ℕ) :
    |correlationTerm m T A B k - correlationTerm m S A B k| ≤
      m.real (WeakTopology.iteratePreimage T k A ∆
        WeakTopology.iteratePreimage S k A) := by
  let AT := WeakTopology.iteratePreimage T k A
  let AS := WeakTopology.iteratePreimage S k A
  have hAT : MeasurableSet AT :=
    WeakTopology.measurableSet_iteratePreimage T k hA
  have hAS : MeasurableSet AS :=
    WeakTopology.measurableSet_iteratePreimage S k hA
  have hmeasure :
      |m.real (AT ∩ B) - m.real (AS ∩ B)| ≤ m.real (AT ∆ AS) := by
    calc
      |m.real (AT ∩ B) - m.real (AS ∩ B)| ≤
          m.real ((AT ∩ B) ∆ (AS ∩ B)) :=
        abs_measureReal_sub_le_measureReal_symmDiff
          (hAT.inter hB).nullMeasurableSet (hAS.inter hB).nullMeasurableSet
      _ = m.real ((AT ∆ AS) ∩ B) := by
        rw [Set.inter_symmDiff_distrib_right]
      _ ≤ m.real (AT ∆ AS) := measureReal_mono Set.inter_subset_left
  calc
    |correlationTerm m T A B k - correlationTerm m S A B k| ≤
        |(m.real (AT ∩ B) - m.real A * m.real B) -
          (m.real (AS ∩ B) - m.real A * m.real B)| := by
      exact abs_abs_sub_abs_le_abs_sub _ _
    _ = |m.real (AT ∩ B) - m.real (AS ∩ B)| := by
      congr 1
      ring
    _ ≤ m.real (AT ∆ AS) := hmeasure

theorem continuous_correlationTerm (m : Measure X) [IsFiniteMeasure m]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (k : ℕ) :
    Continuous (fun T : Automorphism m ↦ correlationTerm m T A B k) := by
  rw [continuous_iff_continuousAt]
  intro S
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  obtain ⟨U, hUopen, hSU, hU⟩ :=
    WeakTopology.exists_open_iteratePreimage_close m S hA k hε
  refine Filter.mem_of_superset (hUopen.mem_nhds hSU) ?_
  intro T hTU
  change dist (correlationTerm m T A B k) (correlationTerm m S A B k) < ε
  rw [Real.dist_eq]
  exact (abs_correlationTerm_sub_le m S T hA hB k).trans_lt (hU T hTU)

theorem continuous_correlationAverage (m : Measure X) [IsFiniteMeasure m]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B) (n : ℕ) :
    Continuous (fun T : Automorphism m ↦ correlationAverage m T A B n) := by
  unfold correlationAverage
  exact (continuous_finsetSum (Finset.range n)
    (fun k _ ↦ continuous_correlationTerm m hA hB k)).div_const n

theorem isOpen_correlationAverage_lt (m : Measure X) [IsFiniteMeasure m]
    {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (n : ℕ) (r : ℝ) :
    IsOpen {T : Automorphism m | correlationAverage m T A B n < r} :=
  isOpen_lt (continuous_correlationAverage m hA hB n) continuous_const

end Submission.Criterion
