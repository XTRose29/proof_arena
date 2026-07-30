import Submission.Helpers

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open scoped ENNReal

def orbitSaturation
    (T T_inv : EucPlane → EucPlane) (s : Set EucPlane) : Set EucPlane :=
  (⋃ n : ℕ, T^[n] '' s) ∪ ⋃ n : ℕ, T_inv^[n] '' s

lemma subset_orbitSaturation
    (T T_inv : EucPlane → EucPlane) (s : Set EucPlane) :
    s ⊆ orbitSaturation T T_inv s := by
  intro x hx
  apply Or.inl
  exact Set.mem_iUnion_of_mem 0 (by simpa using hx)

lemma measurableSet_orbitSaturation
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {s : Set EucPlane} (hs : MeasurableSet s) :
    MeasurableSet (orbitSaturation T T_inv s) := by
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro n
    simpa [measurableEquivOfContDiffInverse] using
      (measurableEquivOfContDiffInverse (T^[n]) (T_inv^[n])
        (contDiff_iterate T hT_smooth n) (contDiff_iterate T_inv hT_inv_smooth n)
        (hT_left.iterate n) (hT_right.iterate n)).measurableSet_image.mpr hs
  · apply MeasurableSet.iUnion
    intro n
    simpa [measurableEquivOfContDiffInverse] using
      (measurableEquivOfContDiffInverse (T_inv^[n]) (T^[n])
        (contDiff_iterate T_inv hT_inv_smooth n) (contDiff_iterate T hT_smooth n)
        (hT_right.iterate n) (hT_left.iterate n)).measurableSet_image.mpr hs

lemma dimH_orbitSaturation
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (s : Set EucPlane) :
    dimH (orbitSaturation T T_inv s) = dimH s := by
  rw [orbitSaturation, dimH_union, dimH_iUnion, dimH_iUnion]
  simp_rw [dimH_image_iterate_eq_of_contDiff_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left]
  simp_rw [dimH_image_iterate_eq_of_contDiff_inverse T_inv T hT_inv_smooth hT_smooth
    hT_right]
  simp

lemma orbitSaturation_compl_measure_zero
    (T T_inv : EucPlane → EucPlane)
    (μ : Measure EucPlane) {s : Set EucPlane}
    (hμs : μ sᶜ = 0) :
    μ (orbitSaturation T T_inv s)ᶜ = 0 := by
  exact measure_mono_null
    (Set.compl_subset_compl.mpr (subset_orbitSaturation T T_inv s)) hμs

lemma image_orbitSaturation
    (T T_inv : EucPlane → EucPlane)
    (hT_right : Function.RightInverse T_inv T)
    (s : Set EucPlane) :
    T '' orbitSaturation T T_inv s = orbitSaturation T T_inv s := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    rcases hy with hy | hy
    · obtain ⟨n, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      apply Or.inl
      apply Set.mem_iUnion_of_mem (n + 1)
      exact ⟨z, hz, Function.iterate_succ_apply' T n z⟩
    · obtain ⟨n, z, hz, rfl⟩ := Set.mem_iUnion.mp hy
      cases n with
      | zero =>
          apply Or.inl
          apply Set.mem_iUnion_of_mem 1
          exact ⟨z, hz, rfl⟩
      | succ n =>
          apply Or.inr
          apply Set.mem_iUnion_of_mem n
          refine ⟨z, hz, ?_⟩
          rw [Function.iterate_succ_apply', hT_right]
  · intro hx
    rcases hx with hx | hx
    · obtain ⟨n, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
      cases n with
      | zero =>
          refine ⟨T_inv z, ?_, hT_right z⟩
          apply Or.inr
          apply Set.mem_iUnion_of_mem 1
          exact ⟨z, hz, rfl⟩
      | succ n =>
          refine ⟨T^[n] z, ?_, (Function.iterate_succ_apply' T n z).symm⟩
          apply Or.inl
          exact Set.mem_iUnion_of_mem n ⟨z, hz, rfl⟩
    · obtain ⟨n, z, hz, rfl⟩ := Set.mem_iUnion.mp hx
      refine ⟨T_inv^[n + 1] z, ?_, ?_⟩
      · apply Or.inr
        exact Set.mem_iUnion_of_mem (n + 1) ⟨z, hz, rfl⟩
      · rw [Function.iterate_succ_apply', hT_right]

lemma orbitSaturation_compl_measure_zero_of_measure_ne_zero
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_erg : Ergodic T mu)
    {s : Set EucPlane} (hs_measurable : MeasurableSet s) (hmu_s : mu s ≠ 0) :
    mu (orbitSaturation T T_inv s)ᶜ = 0 := by
  let S := orbitSaturation T T_inv s
  have hS_measurable : MeasurableSet S :=
    measurableSet_orbitSaturation T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hs_measurable
  have hS_image : T '' S = S := image_orbitSaturation T T_inv hT_right s
  have hS_preimage : T ⁻¹' S = S := by
    ext x
    constructor
    · intro hx
      have hx_image : T x ∈ T '' S := by
        rw [hS_image]
        exact hx
      obtain ⟨y, hy, hyx⟩ := hx_image
      have : y = x := hT_left.injective hyx
      simpa [this] using hy
    · intro hx
      change T x ∈ S
      rw [← hS_image]
      exact ⟨x, hx, rfl⟩
  have hmu_S : mu S ≠ 0 := by
    intro hzero
    apply hmu_s
    exact measure_mono_null (subset_orbitSaturation T T_inv s) hzero
  have hmu_S_one : mu S = 1 :=
    (hmu_erg.prob_eq_zero_or_one hS_measurable hS_preimage).resolve_left hmu_S
  rw [measure_compl hS_measurable (by finiteness), measure_univ, hmu_S_one]
  simp

lemma dimMeasure_le_dimH_of_measure_ne_zero_ergodic
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_erg : Ergodic T mu)
    {s : Set EucPlane} (hs_measurable : MeasurableSet s) (hmu_s : mu s ≠ 0) :
    dimMeasure mu ≤ dimH s := by
  calc
    dimMeasure mu ≤ dimH (orbitSaturation T T_inv s) :=
      dimMeasure_le_dimH_of_full_measure mu
        (measurableSet_orbitSaturation T T_inv hT_smooth hT_inv_smooth
          hT_left hT_right hs_measurable)
        (orbitSaturation_compl_measure_zero_of_measure_ne_zero T T_inv
          hT_smooth hT_inv_smooth hT_left hT_right mu hmu_erg hs_measurable hmu_s)
    _ = dimH s :=
      dimH_orbitSaturation T T_inv hT_smooth hT_inv_smooth hT_left hT_right s

lemma orbitSaturation_subset_of_invariant
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    {K s : Set EucPlane} (hK_inv : T '' K = K) (hsK : s ⊆ K) :
    orbitSaturation T T_inv s ⊆ K := by
  intro x hx
  rcases hx with hx | hx
  · obtain ⟨n, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    rw [← image_iterate_eq_of_image_eq T hK_inv n]
    exact ⟨y, hsK hy, rfl⟩
  · obtain ⟨n, y, hy, rfl⟩ := Set.mem_iUnion.mp hx
    rw [← image_iterate_eq_of_image_eq T_inv
      (inverse_image_eq_of_image_eq hT_left hK_inv) n]
    exact ⟨y, hsK hy, rfl⟩

lemma dimMeasure_eq_sInf_invariant
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (μ : Measure EucPlane) :
    dimMeasure μ =
      sInf {d : ℝ≥0∞ |
        ∃ s : Set EucPlane, MeasurableSet s ∧ μ sᶜ = 0 ∧
          T '' s = s ∧ dimH s = d} := by
  unfold dimMeasure
  congr 1
  ext d
  constructor
  · rintro ⟨s, hs, hμs, rfl⟩
    refine ⟨orbitSaturation T T_inv s,
      measurableSet_orbitSaturation T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right hs,
      orbitSaturation_compl_measure_zero T T_inv μ hμs,
      image_orbitSaturation T T_inv hT_right s,
      dimH_orbitSaturation T T_inv hT_smooth hT_inv_smooth hT_left hT_right s⟩
  · rintro ⟨s, hs, hμs, _hinv, hdim⟩
    exact ⟨s, hs, hμs, hdim⟩

lemma exists_invariant_full_measure_dimMeasure
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K)
    (mu : Measure EucPlane) (hmu_supp : mu Kᶜ = 0) :
    ∃ s : Set EucPlane, MeasurableSet s ∧ mu sᶜ = 0 ∧
      T '' s = s ∧ dimH s = dimMeasure mu := by
  let D : Set ℝ≥0∞ := {d | ∃ s : Set EucPlane,
    MeasurableSet s ∧ mu sᶜ = 0 ∧ dimH s = d}
  have hD : D.Nonempty := by
    refine ⟨dimH K, K, hK_compact.isClosed.measurableSet, hmu_supp, rfl⟩
  obtain ⟨d, _hd_antitone, hd_tendsto, hd_mem⟩ :=
    exists_seq_tendsto_sInf hD (by bddDefault)
  have hd_mem' : ∀ n, ∃ s : Set EucPlane,
      MeasurableSet s ∧ mu sᶜ = 0 ∧ dimH s = d n := by
    simpa [D] using hd_mem
  choose s hs_measurable hs_full hs_dim using hd_mem'
  let I : Set EucPlane := ⋂ n, s n
  have hI_measurable : MeasurableSet I := by
    apply MeasurableSet.iInter
    exact hs_measurable
  have hI_full : mu Iᶜ = 0 := by
    change mu (⋂ n, s n)ᶜ = 0
    rw [Set.compl_iInter]
    exact measure_iUnion_null hs_full
  have hd_tendsto' : Filter.Tendsto d Filter.atTop (nhds (dimMeasure mu)) := by
    simpa [dimMeasure, D] using hd_tendsto
  have hI_dim_le_each (n : ℕ) : dimH I ≤ d n := by
    calc
      dimH I ≤ dimH (s n) := dimH_mono (by
        change (⋂ i, s i) ⊆ s n
        exact Set.iInter_subset s n)
      _ = d n := hs_dim n
  have hI_dim_le : dimH I ≤ dimMeasure mu :=
    ge_of_tendsto' hd_tendsto' hI_dim_le_each
  have hI_dim : dimH I = dimMeasure mu :=
    le_antisymm hI_dim_le
      (dimMeasure_le_dimH_of_full_measure mu hI_measurable hI_full)
  refine ⟨orbitSaturation T T_inv I,
    measurableSet_orbitSaturation T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hI_measurable,
    orbitSaturation_compl_measure_zero T T_inv mu hI_full,
    image_orbitSaturation T T_inv hT_right I, ?_⟩
  exact (dimH_orbitSaturation T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right I).trans hI_dim

lemma exists_invariant_full_measure_dimMeasure_subset
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (mu : Measure EucPlane) (hmu_supp : mu Kᶜ = 0) :
    ∃ s : Set EucPlane, MeasurableSet s ∧ mu sᶜ = 0 ∧
      T '' s = s ∧ s ⊆ K ∧ dimH s = dimMeasure mu := by
  obtain ⟨s, hs_measurable, hs_full, _hs_invariant, hs_dim⟩ :=
    exists_invariant_full_measure_dimMeasure T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right K hK_compact mu hmu_supp
  have hsK_measurable : MeasurableSet (s ∩ K) :=
    hs_measurable.inter hK_compact.isClosed.measurableSet
  have hsK_full : mu (s ∩ K)ᶜ = 0 := by
    rw [Set.compl_inter]
    exact measure_union_null hs_full hmu_supp
  have hsK_dim : dimH (s ∩ K) = dimMeasure mu := by
    apply le_antisymm
    · exact (dimH_mono Set.inter_subset_left).trans_eq hs_dim
    · exact dimMeasure_le_dimH_of_full_measure mu hsK_measurable hsK_full
  refine ⟨orbitSaturation T T_inv (s ∩ K),
    measurableSet_orbitSaturation T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right hsK_measurable,
    orbitSaturation_compl_measure_zero T T_inv mu hsK_full,
    image_orbitSaturation T T_inv hT_right (s ∩ K),
    orbitSaturation_subset_of_invariant T T_inv hT_left hK_inv Set.inter_subset_right, ?_⟩
  exact (dimH_orbitSaturation T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right (s ∩ K)).trans hsK_dim

end Submission.Helpers
