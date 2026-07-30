import Submission.HausdorffCovers

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open scoped ENNReal

lemma exists_small_measurable_partition
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    {K s : Set EucPlane} (hK_compact : IsCompact K)
    (hs_measurable : MeasurableSet s) (hmu_s : mu sᶜ = 0) (hsK : s ⊆ K)
    {e : ℝ} (he : 0 < e) :
    ∃ P : Finset (Set EucPlane), IsMeasurablePartition mu P ∧
      (∀ A ∈ P, A ⊆ s) ∧
      ∀ A ∈ P, Metric.ediam A ≤ 2 * ENNReal.ofReal e := by
  classical
  obtain ⟨t, _htK, ht_finite, hKt⟩ := finite_cover_balls_of_compact hK_compact he
  let F : Finset EucPlane := ht_finite.toFinset
  let equivFin := Fintype.equivFin ↥F
  let B : Fin (Fintype.card ↥F) → Set EucPlane := fun i =>
    Metric.ball (equivFin.symm i).1 e ∩ s
  let D : Fin (Fintype.card ↥F) → Set EucPlane := disjointed B
  let P : Finset (Set EucPlane) := Finset.univ.image D
  have hB_measurable : ∀ i, MeasurableSet (B i) := fun i =>
    measurableSet_ball.inter hs_measurable
  have hD_measurable : ∀ i, MeasurableSet (D i) := by
    intro i
    change MeasurableSet (disjointed B i)
    rw [disjointed_apply, Finset.sup_set_eq_biUnion]
    exact (hB_measurable i).diff
      (Finset.measurableSet_biUnion (Finset.Iio i) fun j _hj => hB_measurable j)
  have hB_union : (⋃ i, B i) = s := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact hxi.2
    · intro hxs
      have hxK : x ∈ K := hsK hxs
      obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hKt hxK)
      obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.mp hy
      have hyF : y ∈ F := by simpa [F] using hyt
      let j : ↥F := ⟨y, hyF⟩
      let i : Fin (Fintype.card ↥F) := equivFin j
      apply Set.mem_iUnion_of_mem i
      change x ∈ Metric.ball (equivFin.symm i).1 e ∩ s
      have hcenter : (equivFin.symm i).1 = y := by simp [i, j]
      exact ⟨by simpa [hcenter] using hxy, hxs⟩
  have hD_union : (⋃ i, D i) = s := by
    change (⋃ i, disjointed B i) = s
    rw [iUnion_disjointed, hB_union]
  have hP_union : (⋃ A ∈ P, A) = s := by
    calc
      (⋃ A ∈ P, A) = ⋃ i, D i := by
        ext x
        simp [P]
      _ = s := hD_union
  have hP_measurable : ∀ A ∈ P, MeasurableSet A := by
    intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    exact hD_measurable i
  have hP_disjoint : ∀ A ∈ P, ∀ C ∈ P, A ≠ C → mu (A ∩ C) = 0 := by
    intro A hA C hC hAC
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hC
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hAC rfl
    exact (disjoint_disjointed B hij).aedisjoint.eq
  refine ⟨P, ⟨hP_measurable, ?_, hP_disjoint⟩, ?_, ?_⟩
  · rw [hP_union]
    exact hmu_s
  · intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    exact (disjointed_subset B i).trans Set.inter_subset_right
  · intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    calc
      Metric.ediam (D i) ≤ Metric.ediam (B i) :=
        Metric.ediam_mono (disjointed_subset B i)
      _ ≤ Metric.ediam (Metric.ball (equivFin.symm i).1 e) :=
        Metric.ediam_mono Set.inter_subset_left
      _ ≤ 2 * ENNReal.ofReal e := by
        rw [← Metric.eball_ofReal]
        exact Metric.ediam_eball_le

lemma exists_small_partition_on_dimMeasure_carrier
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    {e : ℝ} (he : 0 < e) :
    ∃ s : Set EucPlane, ∃ P : Finset (Set EucPlane),
      MeasurableSet s ∧ mu sᶜ = 0 ∧ T '' s = s ∧ s ⊆ K ∧
      dimH s = dimMeasure mu ∧ IsMeasurablePartition mu P ∧
      (∀ A ∈ P, A ⊆ s) ∧
      ∀ A ∈ P, Metric.ediam A ≤ 2 * ENNReal.ofReal e := by
  obtain ⟨s, hs_measurable, hs_full, hs_invariant, hsK, hs_dim⟩ :=
    exists_invariant_full_measure_dimMeasure_subset T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right K hK_compact hK_inv mu hmu_supp
  obtain ⟨P, hP, hP_subset, hP_diam⟩ :=
    exists_small_measurable_partition mu hK_compact hs_measurable hs_full hsK he
  exact ⟨s, P, hs_measurable, hs_full, hs_invariant, hsK, hs_dim,
    hP, hP_subset, hP_diam⟩

lemma edist_iterate_le_of_mem_iteratedJoin_atom
    (T : EucPlane → EucPlane) (P : Finset (Set EucPlane))
    {r : ℝ≥0∞} (hP_diam : ∀ A ∈ P, Metric.ediam A ≤ r)
    {n : ℕ} {A : Set EucPlane} (hA : A ∈ iteratedJoin T P n)
    {x y : EucPlane} (hx : x ∈ A) (hy : y ∈ A)
    (k : Fin n) :
    edist (T^[k.val] x) (T^[k.val] y) ≤ r := by
  rw [iteratedJoin] at hA
  obtain ⟨f, hf, rfl⟩ := Finset.mem_image.mp hA
  have hfk : f k ∈ P := Fintype.mem_piFinset.mp hf k
  have hxk := Set.mem_iInter.mp hx k
  have hyk := Set.mem_iInter.mp hy k
  change T^[k.val] x ∈ f k at hxk
  change T^[k.val] y ∈ f k at hyk
  exact (Metric.edist_le_ediam_of_mem hxk hyk).trans (hP_diam (f k) hfk)

end Submission.Helpers
