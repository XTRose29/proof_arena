import Submission.AnnulusAverage

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory
open scoped ENNReal

lemma exists_small_weighted_boundary_ball_partition
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    {K s : Set EucPlane} (hK_compact : IsCompact K)
    (hs_measurable : MeasurableSet s) (hmu_s : mu sᶜ = 0) (hsK : s ⊆ K)
    {e : ℝ} (he : 0 < e)
    (weight : ℕ → ℝ≥0∞) (delta : ℕ → ℝ)
    (hdelta : ∀ L, 0 ≤ delta L)
    (hsum :
      (∑' L, weight L * ENNReal.ofReal (2 * delta L) * mu Set.univ) ≠ ⊤) :
    ∃ n : ℕ, ∃ center : Fin n → EucPlane, ∃ radius : Fin n → ℝ,
      ∃ P : Finset (Set EucPlane),
        (∀ i, e < radius i ∧ radius i < 2 * e ∧
          (∑' L, weight L *
            mu {x | |dist x (center i) - radius i| ≤ delta L}) ≠ ⊤) ∧
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
        (∑' L, weight L *
          mu {x | |dist x (center i) - r| ≤ delta L}) ≠ ⊤ :=
    exists_radius_weighted_boundaryStrip_tsum_ne_top
      mu (center i) (by linarith) weight delta hdelta hsum
  let radius : Fin n → ℝ := fun i => (hradius_exists i).choose
  have hradius (i : Fin n) :
      e < radius i ∧ radius i < 2 * e ∧
        (∑' L, weight L *
          mu {x | |dist x (center i) - radius i| ≤ delta L}) ≠ ⊤ := by
    exact ⟨(hradius_exists i).choose_spec.1.1,
      (hradius_exists i).choose_spec.1.2,
      (hradius_exists i).choose_spec.2⟩
  let C : Fin n → Set EucPlane := fun i => Metric.ball (center i) (radius i)
  let B : Fin n → Set EucPlane := fun i => C i ∩ s
  let D : Fin n → Set EucPlane := fun i => disjointed B i
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
