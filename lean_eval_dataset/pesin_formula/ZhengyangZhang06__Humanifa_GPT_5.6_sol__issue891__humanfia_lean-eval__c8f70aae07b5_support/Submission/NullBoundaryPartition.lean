import Submission.BallMass

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open scoped ENNReal

lemma exists_radius_sphere_measure_zero
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [OpensMeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] (x : M)
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Set.Ioo a b, mu (Metric.sphere x r) = 0 := by
  let bad : Set ℝ :=
    {r | mu {y | r ≤ dist y x} ≠ mu {y | r < dist y x}}
  have hbad : bad.Countable := by
    exact countable_meas_le_ne_meas_lt mu fun y => dist y x
  let f : ℝ → ℝ := fun z =>
    a + (b - a) * (Real.tanh z + 1) / 2
  have hf_injective : Function.Injective f := by
    intro z w hzw
    apply Real.tanh_injective
    have hba : b - a ≠ 0 := sub_ne_zero.mpr hab.ne'
    dsimp [f] at hzw
    apply (mul_left_cancel₀ hba)
    linarith
  have hpre_countable : (f ⁻¹' bad).Countable :=
    hbad.preimage hf_injective
  have hpre_ne_univ : f ⁻¹' bad ≠ Set.univ := by
    intro hpre
    apply Set.not_countable_univ (α := ℝ)
    rw [← hpre]
    exact hpre_countable
  have hz_exists : ∃ z, z ∉ f ⁻¹' bad := by
    by_contra hnone
    push Not at hnone
    exact hpre_ne_univ (Set.eq_univ_of_forall hnone)
  obtain ⟨z, hz⟩ := hz_exists
  let r := f z
  have hra : a < r := by
    have htanh := Real.neg_one_lt_tanh z
    have hba : 0 < b - a := sub_pos.mpr hab
    dsimp [r, f]
    nlinarith
  have hrb : r < b := by
    have htanh := Real.tanh_lt_one z
    have hba : 0 < b - a := sub_pos.mpr hab
    dsimp [r, f]
    nlinarith
  have hgood :
      mu {y | r ≤ dist y x} = mu {y | r < dist y x} := by
    simpa [bad, r] using hz
  have hclosed_ball : mu (Metric.closedBall x r) = mu (Metric.ball x r) := by
    have hclosed_compl :
        (Metric.closedBall x r)ᶜ = {y | r < dist y x} := by
      ext y
      simp [Metric.mem_closedBall, dist_comm]
    have hball_compl :
        (Metric.ball x r)ᶜ = {y | r ≤ dist y x} := by
      ext y
      simp [Metric.mem_ball, dist_comm]
    have hcompl :
        mu (Metric.ball x r)ᶜ = mu (Metric.closedBall x r)ᶜ := by
      simpa [hclosed_compl, hball_compl] using hgood
    have hball_measurable : MeasurableSet (Metric.ball x r) := measurableSet_ball
    have hclosed_measurable : MeasurableSet (Metric.closedBall x r) :=
      measurableSet_closedBall
    have hcompl_real :
        mu.real (Metric.ball x r)ᶜ = mu.real (Metric.closedBall x r)ᶜ := by
      simpa [measureReal_def] using congrArg ENNReal.toReal hcompl
    rw [measureReal_compl hball_measurable,
      measureReal_compl hclosed_measurable] at hcompl_real
    rw [← ofReal_measureReal, ← ofReal_measureReal]
    exact congrArg ENNReal.ofReal (sub_right_inj.mp hcompl_real).symm
  refine ⟨r, ⟨hra, hrb⟩, ?_⟩
  rw [← Metric.closedBall_sdiff_ball]
  rw [measure_sdiff Metric.ball_subset_closedBall
    measurableSet_ball.nullMeasurableSet (measure_ne_top mu _)]
  simp [hclosed_ball]

lemma exists_radius_ball_frontier_measure_zero
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [OpensMeasurableSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] (x : M)
    {a b : ℝ} (hab : a < b) :
    ∃ r ∈ Set.Ioo a b, mu (frontier (Metric.ball x r)) = 0 := by
  obtain ⟨r, hr, hsphere⟩ := exists_radius_sphere_measure_zero mu x hab
  exact ⟨r, hr,
    measure_mono_null Metric.frontier_ball_subset_sphere hsphere⟩

lemma exists_small_null_boundary_ball_partition
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    {K s : Set EucPlane} (hK_compact : IsCompact K)
    (hs_measurable : MeasurableSet s) (hmu_s : mu sᶜ = 0) (hsK : s ⊆ K)
    {e : ℝ} (he : 0 < e) :
    ∃ n : ℕ, ∃ center : Fin n → EucPlane, ∃ radius : Fin n → ℝ,
      ∃ P : Finset (Set EucPlane),
        (∀ i, e < radius i ∧ radius i < 2 * e ∧
          mu (frontier (Metric.ball (center i) (radius i))) = 0) ∧
        s ⊆ ⋃ i, Metric.ball (center i) (radius i) ∧
        IsMeasurablePartition mu P ∧
        (∀ A ∈ P, A ⊆ s) ∧
        (∀ A ∈ P, Metric.ediam A ≤ 2 * ENNReal.ofReal (2 * e)) ∧
        ∀ {x y}, x ∈ s → y ∈ s →
          (∀ i, x ∈ Metric.ball (center i) (radius i) ↔
            y ∈ Metric.ball (center i) (radius i)) →
          ∀ A ∈ P, x ∈ A ↔ y ∈ A := by
  classical
  obtain ⟨t, _htK, ht_finite, hKt⟩ := finite_cover_balls_of_compact hK_compact he
  let F : Finset EucPlane := ht_finite.toFinset
  let equivFin := Fintype.equivFin ↥F
  let n := Fintype.card ↥F
  let center : Fin n → EucPlane := fun i => (equivFin.symm i).1
  have hradius_exists (i : Fin n) :
      ∃ r ∈ Set.Ioo e (2 * e),
        mu (frontier (Metric.ball (center i) r)) = 0 :=
    exists_radius_ball_frontier_measure_zero mu (center i) (by linarith)
  let radius : Fin n → ℝ := fun i => (hradius_exists i).choose
  have hradius (i : Fin n) :
      e < radius i ∧ radius i < 2 * e ∧
        mu (frontier (Metric.ball (center i) (radius i))) = 0 := by
    exact ⟨(hradius_exists i).choose_spec.1.1,
      (hradius_exists i).choose_spec.1.2,
      (hradius_exists i).choose_spec.2⟩
  let C : Fin n → Set EucPlane := fun i => Metric.ball (center i) (radius i)
  let B : Fin n → Set EucPlane := fun i => C i ∩ s
  let D : Fin n → Set EucPlane := disjointed B
  let P : Finset (Set EucPlane) := Finset.univ.image D
  have hB_measurable : ∀ i, MeasurableSet (B i) := fun i =>
    measurableSet_ball.inter hs_measurable
  have hD_measurable : ∀ i, MeasurableSet (D i) := by
    intro i
    change MeasurableSet (disjointed B i)
    rw [disjointed_apply, Finset.sup_set_eq_biUnion]
    exact (hB_measurable i).diff
      (Finset.measurableSet_biUnion (Finset.Iio i) fun j _hj => hB_measurable j)
  have hsC : s ⊆ ⋃ i, C i := by
    intro x hxs
    have hxK : x ∈ K := hsK hxs
    obtain ⟨y, hy⟩ := Set.mem_iUnion.mp (hKt hxK)
    obtain ⟨hyt, hxy⟩ := Set.mem_iUnion.mp hy
    have hyF : y ∈ F := by simpa [F] using hyt
    let j : ↥F := ⟨y, hyF⟩
    let i : Fin n := equivFin j
    apply Set.mem_iUnion_of_mem i
    change x ∈ Metric.ball (center i) (radius i)
    have hcenter : center i = y := by simp [center, i, j]
    rw [Metric.mem_ball, hcenter]
    exact hxy.trans (hradius i).1
  have hB_union : (⋃ i, B i) = s := by
    ext x
    constructor
    · rintro hx
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
      exact hxi.2
    · intro hxs
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp (hsC hxs)
      exact Set.mem_iUnion_of_mem i ⟨hxi, hxs⟩
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
  have hP_disjoint : ∀ A ∈ P, ∀ Q ∈ P, A ≠ Q → mu (A ∩ Q) = 0 := by
    intro A hA Q hQ hAQ
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    obtain ⟨j, _hj, rfl⟩ := Finset.mem_image.mp hQ
    have hij : i ≠ j := by
      intro hij
      subst j
      exact hAQ rfl
    exact (disjoint_disjointed B hij).aedisjoint.eq
  have hP : IsMeasurablePartition mu P := ⟨hP_measurable, by
    rw [hP_union]
    exact hmu_s, hP_disjoint⟩
  have hP_subset : ∀ A ∈ P, A ⊆ s := by
    intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    exact (disjointed_subset B i).trans Set.inter_subset_right
  have hP_diam : ∀ A ∈ P,
      Metric.ediam A ≤ 2 * ENNReal.ofReal (2 * e) := by
    intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    calc
      Metric.ediam (D i) ≤ Metric.ediam (B i) :=
        Metric.ediam_mono (disjointed_subset B i)
      _ ≤ Metric.ediam (Metric.ball (center i) (2 * e)) := by
        apply Metric.ediam_mono
        exact Set.inter_subset_left.trans
          (Metric.ball_subset_ball (hradius i).2.1.le)
      _ ≤ 2 * ENNReal.ofReal (2 * e) := by
        rw [← Metric.eball_ofReal]
        exact Metric.ediam_eball_le
  have hstable {x y : EucPlane} (hxs : x ∈ s) (hys : y ∈ s)
      (hcode : ∀ i, x ∈ C i ↔ y ∈ C i) :
      ∀ A ∈ P, x ∈ A ↔ y ∈ A := by
    have hBcode : ∀ i, x ∈ B i ↔ y ∈ B i := by
      intro i
      simp only [B, Set.mem_inter_iff, hxs, hys, and_true]
      exact hcode i
    intro A hA
    obtain ⟨i, _hi, rfl⟩ := Finset.mem_image.mp hA
    change x ∈ disjointed B i ↔ y ∈ disjointed B i
    simp only [disjointed_apply, Finset.sup_set_eq_biUnion, Set.mem_sdiff,
      Set.mem_iUnion, not_exists]
    constructor
    · rintro ⟨hxi, hxearlier⟩
      refine ⟨(hBcode i).mp hxi, ?_⟩
      intro j hj hyj
      exact hxearlier j hj ((hBcode j).mpr hyj)
    · rintro ⟨hyi, hyearlier⟩
      refine ⟨(hBcode i).mpr hyi, ?_⟩
      intro j hj hxj
      exact hyearlier j hj ((hBcode j).mp hxj)
  refine ⟨n, center, radius, P, hradius, hsC, hP, hP_subset, hP_diam, ?_⟩
  intro x y hxs hys hcode A hA
  exact hstable hxs hys hcode A hA

end Submission.Helpers
