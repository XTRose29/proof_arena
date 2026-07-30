import Submission.Helpers

open LeanEval.Dynamics.LaxApproximation
open MeasureTheory Set Function
open scoped ENNReal BigOperators

namespace Submission.Helpers

private noncomputable def zeroGridIndex (n : ℕ) (hn : 0 < n) (d : ℕ) : Fin d → Fin n :=
  fun _ => ⟨0, hn⟩

lemma measure_biUnion_cube (n : ℕ) (hn : 0 < n) {d : ℕ}
    (A : Finset (Fin d → Fin n)) :
    volume (⋃ k ∈ A, cube n k) =
      (A.card : ℝ≥0∞) * volume (cube n (zeroGridIndex n hn d)) := by
  rw [measure_biUnion_finset]
  · simp_rw [measure_cube_eq n _ (zeroGridIndex n hn d)]
    simp
  · intro k hk l hl hkl
    exact pairwise_disjoint_cube n hn hkl
  · intro k _hk
    exact measurableSet_cube n hn k

lemma measure_cube_ne_zero (n : ℕ) (hn : 0 < n) {d : ℕ} :
    volume (cube n (zeroGridIndex n hn d)) ≠ 0 := by
  intro hzero
  have hpartition := measure_iUnion (μ := (volume : Measure (Torus d)))
    (pairwise_disjoint_cube n hn) (measurableSet_cube n hn)
  rw [iUnion_cube n hn] at hpartition
  have hsumzero : ∑' k : Fin d → Fin n, volume (cube n k) = 0 := by
    simp_rw [measure_cube_eq n _ (zeroGridIndex n hn d), hzero]
    simp
  have hunivzero : volume (Set.univ : Set (Torus d)) = 0 := hpartition.trans hsumzero
  have hunivone : volume (Set.univ : Set (Torus d)) = 1 := by
    rw [volume_pi, Measure.pi_univ]
    simp [AddCircle.measure_univ]
  rw [hunivone] at hunivzero
  exact one_ne_zero hunivzero

/-- Hall's matching permutation for the grid: every matched target cube meets the image of its
source cube. -/
lemma exists_grid_matching (n : ℕ) (hn : 0 < n) {d : ℕ} (T : ToralDynamicalSystem d) :
    ∃ σ : Equiv.Perm (Fin d → Fin n), ∀ k,
      (T.toHomeomorph '' cube n k ∩ cube n (σ k)).Nonempty := by
  classical
  let R : (Fin d → Fin n) → (Fin d → Fin n) → Prop := fun k l =>
    (T.toHomeomorph '' cube n k ∩ cube n l).Nonempty
  have hHall : ∀ A : Finset (Fin d → Fin n),
      A.card ≤ (Finset.univ.filter fun l => ∃ k ∈ A, R k l).card := by
    intro A
    let B := Finset.univ.filter fun l => ∃ k ∈ A, R k l
    let UA : Set (Torus d) := ⋃ k ∈ A, cube n k
    let UB : Set (Torus d) := ⋃ l ∈ B, cube n l
    have hsubset : T.toHomeomorph '' UA ⊆ UB := by
      rintro y ⟨x, hx, rfl⟩
      rw [show T.toHomeomorph x ∈ UB ↔ _ by rfl]
      simp only [UB, mem_iUnion]
      let l := gridIndex n hn (T.toHomeomorph x)
      refine ⟨l, ?_⟩
      refine ⟨?_, mem_cube_gridIndex n hn (T.toHomeomorph x)⟩
      simp only [B, Finset.mem_filter, Finset.mem_univ, true_and]
      rw [show x ∈ UA ↔ _ by rfl] at hx
      simp only [UA, mem_iUnion] at hx
      obtain ⟨k, hkA, hxk⟩ := hx
      exact ⟨k, hkA, ⟨T.toHomeomorph x, ⟨⟨x, hxk, rfl⟩,
        mem_cube_gridIndex n hn (T.toHomeomorph x)⟩⟩⟩
    have hmeasureImage : volume (T.toHomeomorph '' UA) = volume UA := by
      let e : Torus d ≃ᵐ Torus d := T.toHomeomorph.toMeasurableEquiv
      have he : MeasurePreserving e (volume : Measure (Torus d)) volume :=
        T.measurePreserving
      have hsymm : MeasurePreserving e.symm (volume : Measure (Torus d)) volume :=
        MeasurePreserving.symm e he
      change volume (e '' UA) = volume UA
      rw [show e '' UA = e.symm ⁻¹' UA by
        ext y
        constructor
        · rintro ⟨x, hx, rfl⟩
          simpa using hx
        · intro hy
          exact ⟨e.symm y, hy, e.apply_symm_apply y⟩]
      exact hsymm.measure_preimage_equiv UA
    have hmeasure :
        (A.card : ℝ≥0∞) * volume (cube n (zeroGridIndex n hn d)) ≤
          (B.card : ℝ≥0∞) * volume (cube n (zeroGridIndex n hn d)) := by
      rw [← measure_biUnion_cube n hn A, ← measure_biUnion_cube n hn B]
      change volume UA ≤ volume UB
      rw [← hmeasureImage]
      exact measure_mono hsubset
    change A.card ≤ B.card
    by_contra hcard
    have hcard' : B.card < A.card := Nat.lt_of_not_ge hcard
    have hc0 := measure_cube_ne_zero (d := d) n hn
    have hcTop : volume (cube n (zeroGridIndex n hn d)) ≠ ∞ := measure_ne_top _ _
    have hstrict :
        (B.card : ℝ≥0∞) * volume (cube n (zeroGridIndex n hn d)) <
          (A.card : ℝ≥0∞) * volume (cube n (zeroGridIndex n hn d)) := by
      simpa [mul_comm] using ENNReal.mul_lt_mul_right hc0 hcTop (by exact_mod_cast hcard')
    exact (not_lt_of_ge hmeasure) hstrict
  have hselector :=
    (Fintype.all_card_le_filter_rel_iff_exists_injective R).1 hHall
  obtain ⟨f, hf, hRf⟩ := hselector
  have hbij : Bijective f := ⟨hf, Finite.injective_iff_surjective.mp hf⟩
  let σ : Equiv.Perm (Fin d → Fin n) := Equiv.ofBijective f hbij
  refine ⟨σ, ?_⟩
  intro k
  exact hRf k

end Submission.Helpers
