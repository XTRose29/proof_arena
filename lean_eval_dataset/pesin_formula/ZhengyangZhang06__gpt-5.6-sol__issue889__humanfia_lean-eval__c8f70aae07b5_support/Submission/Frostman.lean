import Submission.CenteredCarrierAtoms

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open scoped ENNReal

lemma le_dimH_of_full_measure_closedBall_le
    (mu : Measure EucPlane) [IsFiniteMeasure mu] (hmu_ne_zero : mu ≠ 0)
    {s : Set EucPlane} (hmu_s : mu sᶜ = 0)
    (d : NNReal) {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon)
    (hball : ∀ x ∈ s, ∀ r ≤ epsilon,
      mu (Metric.closedEBall x r) ≤ r ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimH s := by
  have hle : mu ≤ Measure.hausdorffMeasure (d : ℝ) := by
    apply Measure.le_hausdorffMeasure (d : ℝ) mu epsilon hepsilon
    intro t ht
    by_cases hmu_t : mu t = 0
    · simp [hmu_t]
    · have hts : (t ∩ s).Nonempty := by
        by_contra hts
        rw [Set.not_nonempty_iff_eq_empty] at hts
        apply hmu_t
        apply measure_mono_null (t := sᶜ) _ hmu_s
        intro x hx
        show x ∉ s
        intro hxs
        have hxinter : x ∈ t ∩ s := ⟨hx, hxs⟩
        rw [hts] at hxinter
        simp at hxinter
      obtain ⟨x, hxt, hxs⟩ := Set.inter_nonempty_iff_exists_left.mp hts
      calc
        mu t ≤ mu (Metric.closedEBall x (Metric.ediam t)) := by
          apply measure_mono
          intro y hyt
          exact Metric.mem_closedEBall.mpr
            (Metric.edist_le_ediam_of_mem hyt hxt)
        _ ≤ Metric.ediam t ^ (d : ℝ) := hball x hxs _ ht
  have hhausdorff : Measure.hausdorffMeasure (d : ℝ) s ≠ 0 := by
    intro hzero
    have hmu_s_zero : mu s = 0 := by
      apply nonpos_iff_eq_zero.mp
      exact (hle s).trans_eq hzero
    apply hmu_ne_zero
    apply Measure.measure_univ_eq_zero.mp
    exact (measure_of_measure_compl_eq_zero hmu_s).symm.trans hmu_s_zero
  exact le_dimH_of_hausdorffMeasure_ne_zero hhausdorff

lemma le_dimMeasure_of_full_measure_closedBall_le
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    {s : Set EucPlane} (hmu_s : mu sᶜ = 0)
    (d : NNReal) {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon)
    (hball : ∀ x ∈ s, ∀ r ≤ epsilon,
      mu (Metric.closedEBall x r) ≤ r ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimMeasure mu := by
  unfold dimMeasure
  apply le_sInf
  intro q hq
  obtain ⟨t, _ht_measurable, hmu_t, rfl⟩ := hq
  have hmu_inter : mu (s ∩ t)ᶜ = 0 := by
    rw [Set.compl_inter]
    exact measure_union_null hmu_s hmu_t
  calc
    (d : ℝ≥0∞) ≤ dimH (s ∩ t) :=
      le_dimH_of_full_measure_closedBall_le mu
        (Measure.measure_univ_ne_zero.mp (by simp)) hmu_inter d hepsilon
        (fun x hx r hr => hball x hx.1 r hr)
    _ ≤ dimH t := dimH_mono Set.inter_subset_right

lemma le_dimH_of_positive_measure_closedBall_le
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    {s : Set EucPlane} (hs_measurable : MeasurableSet s) (hmu_s : mu s ≠ 0)
    (d : NNReal) {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon)
    (hball : ∀ x ∈ s, ∀ r ≤ epsilon,
      mu (Metric.closedEBall x r) ≤ r ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimH s := by
  let nu := mu.restrict s
  have hnu_ne_zero : nu ≠ 0 := by
    intro hzero
    apply hmu_s
    have huniv := congrArg (fun m : Measure EucPlane => m Set.univ) hzero
    simpa [nu] using huniv
  have hnu_full : nu sᶜ = 0 := by
    change (mu.restrict s) sᶜ = 0
    rw [Measure.restrict_apply hs_measurable.compl]
    simp
  apply le_dimH_of_full_measure_closedBall_le nu hnu_ne_zero hnu_full d hepsilon
  intro x hxs r hr
  exact (Measure.restrict_le_self (μ := mu) (s := s)
    (Metric.closedEBall x r)).trans (hball x hxs r hr)

lemma le_dimMeasure_of_positive_subset_closedBall_le
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    {carrier s : Set EucPlane}
    (hs_measurable : MeasurableSet s) (hmu_s : mu s ≠ 0)
    (hs_carrier : s ⊆ carrier) (hcarrier_dim : dimH carrier = dimMeasure mu)
    (d : NNReal) {epsilon : ℝ≥0∞} (hepsilon : 0 < epsilon)
    (hball : ∀ x ∈ s, ∀ r ≤ epsilon,
      mu (Metric.closedEBall x r) ≤ r ^ (d : ℝ)) :
    (d : ℝ≥0∞) ≤ dimMeasure mu := by
  calc
    (d : ℝ≥0∞) ≤ dimH s :=
      le_dimH_of_positive_measure_closedBall_le mu hs_measurable hmu_s
        d hepsilon hball
    _ ≤ dimH carrier := dimH_mono hs_carrier
    _ = dimMeasure mu := hcarrier_dim

end Submission.Helpers
