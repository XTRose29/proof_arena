import Submission.RuelleCardinality
import Submission.RuelleEntropyRate

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

noncomputable def gridCellRepresentative
    (K : Set EucPlane) {J : Type*} (Y : EucPlane → J) (y : J) :
    EucPlane := by
  classical
  exact if h : ∃ x, x ∈ K ∧ Y x = y then Classical.choose h else 0

lemma gridCellRepresentative_mem
    (K : Set EucPlane) {J : Type*} (Y : EucPlane → J) (y : J)
    (h : ∃ x, x ∈ K ∧ Y x = y) :
    gridCellRepresentative K Y y ∈ K := by
  rw [gridCellRepresentative, dif_pos h]
  exact (Classical.choose_spec h).1

lemma gridCellRepresentative_observation
    (K : Set EucPlane) {J : Type*} (Y : EucPlane → J) (y : J)
    (h : ∃ x, x ∈ K ∧ Y x = y) :
    Y (gridCellRepresentative K Y y) = y := by
  rw [gridCellRepresentative, dif_pos h]
  exact (Classical.choose_spec h).2

noncomputable def gridTransitionCardBound
    (S : EucPlane → EucPlane) (K : Set EucPlane)
    (r : ℝ) (box : Finset (ℤ × ℤ)) (y : Option ↥box) : ℕ := by
  classical
  let Y := squareGridObservation r box
  exact if h : ∃ x, x ∈ K ∧ Y x = y then
    singularTargetCardBound
      (S (gridCellRepresentative K Y y))
      (fderiv ℝ S (gridCellRepresentative K Y y)) r
  else 1

lemma gridTransitionCardBound_pos
    (S : EucPlane → EucPlane) (K : Set EucPlane)
    (r : ℝ) (box : Finset (ℤ × ℤ)) (y : Option ↥box) :
    0 < gridTransitionCardBound S K r box y := by
  classical
  let Y := squareGridObservation r box
  by_cases h : ∃ x, x ∈ K ∧ Y x = y
  · simp only [gridTransitionCardBound, Y, dif_pos h]
    exact singularTargetCardBound_pos _ _ _
  · simp [gridTransitionCardBound, Y, h]

lemma exists_mem_inter_full_of_measureReal_ne_zero
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    {K A : Set EucPlane} (hmuK : mu Kᶜ = 0)
    (hA : mu.real A ≠ 0) :
    ∃ x, x ∈ A ∧ x ∈ K := by
  by_contra h
  have hsub : A ⊆ Kᶜ := by
    intro x hxA hxK
    exact h ⟨x, hxA, hxK⟩
  have hzero : mu A = 0 := measure_mono_null hsub hmuK
  exact hA ((measureReal_eq_zero_iff).2 hzero)

lemma conditionalSupport_squareGrid_card_le
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (S : EucPlane → EucPlane) (_hS_meas : Measurable S)
    (hS_smooth : ContDiff ℝ 2 S)
    (K : Set EucPlane) (hmuK : mu Kᶜ = 0)
    (hSK : S '' K = K)
    (C : Set EucPlane) (hC_convex : Convex ℝ C) (hKC : K ⊆ C)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ z ∈ C, ∀ w ∈ C,
      ‖fderiv ℝ S z - fderiv ℝ S w‖ ≤ B * dist z w)
    {r : ℝ} (hr : 0 < r) (hsmall : 4 * B * r ≤ 1)
    (box : Finset (ℤ × ℤ))
    (hKbox : ∀ x ∈ K, squareGridIndex r x ∈ box)
    (hderiv : ∀ x, (fderiv ℝ S x).IsInvertible)
    (y : Option ↥box) :
    (conditionalSupport mu
      (fun x => squareGridObservation r box (S x))
      (squareGridObservation r box) y).card ≤
        gridTransitionCardBound S K r box y := by
  classical
  let Y := squareGridObservation r box
  let X : EucPlane → Option ↥box := fun x => Y (S x)
  by_cases hy : ∃ x, x ∈ K ∧ Y x = y
  · let x := gridCellRepresentative K Y y
    have hxK : x ∈ K := gridCellRepresentative_mem K Y y hy
    have hxY : Y x = y := gridCellRepresentative_observation K Y y hy
    let decode : Option ↥box → ℤ × ℤ
      | none => (0, 0)
      | some q => q.1
    have hsupport_point (i : Option ↥box)
        (hi : i ∈ conditionalSupport mu X Y y) :
        ∃ z, z ∈ K ∧ Y z = y ∧ X z = i := by
      have hreal :
          mu.real (Y ⁻¹' {y} ∩ X ⁻¹' {i}) ≠ 0 := by
        simpa [conditionalSupport] using (Finset.mem_filter.mp hi).2
      obtain ⟨z, hzset, hzK⟩ :=
        exists_mem_inter_full_of_measureReal_ne_zero mu hmuK hreal
      exact ⟨z, hzK, hzset.1, hzset.2⟩
    have hsupport_some (i : Option ↥box)
        (hi : i ∈ conditionalSupport mu X Y y) :
        ∃ q : ↥box, i = some q := by
      obtain ⟨z, hzK, _hzY, hzX⟩ := hsupport_point i hi
      have hzSK : S z ∈ K := by
        rw [← hSK]
        exact ⟨z, hzK, rfl⟩
      let q : ↥box := ⟨squareGridIndex r (S z), hKbox (S z) hzSK⟩
      have hobs : Y (S z) = some q :=
        (squareGridObservation_eq_some_iff r box (S z) q).2 rfl
      exact ⟨q, hzX.symm.trans hobs⟩
    have hmaps : Set.MapsTo decode
        (conditionalSupport mu X Y y : Set (Option ↥box))
        (singularTargetIndexCover (S x) (fderiv ℝ S x) r :
          Set (ℤ × ℤ)) := by
      intro i hi
      obtain ⟨z, hzK, hzY, hzX⟩ := hsupport_point i hi
      have hzSK : S z ∈ K := by
        rw [← hSK]
        exact ⟨z, hzK, rfl⟩
      let qx : ↥box := ⟨squareGridIndex r x, hKbox x hxK⟩
      have hxobs : Y x = some qx :=
        (squareGridObservation_eq_some_iff r box x qx).2 rfl
      have hzobs : Y z = some qx := hzY.trans (hxY.symm.trans hxobs)
      have hcell : squareGridIndex r x = squareGridIndex r z := by
        exact (squareGridObservation_eq_some_iff r box z qx).1 hzobs |>.symm
      let qi : ↥box :=
        ⟨squareGridIndex r (S z), hKbox (S z) hzSK⟩
      have hSi : Y (S z) = some qi :=
        (squareGridObservation_eq_some_iff r box (S z) qi).2 rfl
      have hiSome : i = some qi := hzX.symm.trans hSi
      change decode i ∈ singularTargetIndexCover (S x) (fderiv ℝ S x) r
      rw [hiSome]
      exact squareGridIndex_image_mem_singularTargetIndexCover
        S hS_smooth hC_convex hB_nonneg hB hr hsmall
          (hKC hxK) (hKC hzK) hcell (hderiv x)
    have hinj : (conditionalSupport mu X Y y : Set (Option ↥box)).InjOn
        decode := by
      intro i hi j hj hij
      obtain ⟨qi, rfl⟩ := hsupport_some i hi
      obtain ⟨qj, rfl⟩ := hsupport_some j hj
      simp only [decode] at hij
      congr 1
      exact Subtype.ext hij
    have hcard :
        (conditionalSupport mu X Y y).card ≤
          (singularTargetIndexCover (S x) (fderiv ℝ S x) r).card :=
      Finset.card_le_card_of_injOn decode hmaps hinj
    calc
      (conditionalSupport mu
          (fun z => squareGridObservation r box (S z))
          (squareGridObservation r box) y).card =
          (conditionalSupport mu X Y y).card := rfl
      _ ≤ (singularTargetIndexCover (S x) (fderiv ℝ S x) r).card :=
        hcard
      _ ≤ singularTargetCardBound (S x) (fderiv ℝ S x) r :=
        card_singularTargetIndexCover_le_bound _ _ _
      _ = gridTransitionCardBound S K r box y := by
        simp only [gridTransitionCardBound, Y, dif_pos hy, x]
  · have hempty :
        conditionalSupport mu X Y y = ∅ := by
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro i hi
      obtain ⟨z, hzset, hzK⟩ :=
        exists_mem_inter_full_of_measureReal_ne_zero mu hmuK
          (by simpa [conditionalSupport] using (Finset.mem_filter.mp hi).2)
      exact hy ⟨z, hzK, hzset.1⟩
    calc
      (conditionalSupport mu
          (fun z => squareGridObservation r box (S z))
          (squareGridObservation r box) y).card =
          (conditionalSupport mu X Y y).card := rfl
      _ = 0 := by rw [hempty]; simp
      _ ≤ gridTransitionCardBound S K r box y := Nat.zero_le _

lemma conditionalObservationEntropy_squareGrid_le_weighted_log
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (S : EucPlane → EucPlane) (hS_meas : Measurable S)
    (hS_smooth : ContDiff ℝ 2 S)
    (K : Set EucPlane) (hmuK : mu Kᶜ = 0)
    (hSK : S '' K = K)
    (C : Set EucPlane) (hC_convex : Convex ℝ C) (hKC : K ⊆ C)
    {B : ℝ} (hB_nonneg : 0 ≤ B)
    (hB : ∀ z ∈ C, ∀ w ∈ C,
      ‖fderiv ℝ S z - fderiv ℝ S w‖ ≤ B * dist z w)
    {r : ℝ} (hr : 0 < r) (hsmall : 4 * B * r ≤ 1)
    (box : Finset (ℤ × ℤ))
    (hKbox : ∀ x ∈ K, squareGridIndex r x ∈ box)
    (hderiv : ∀ x, (fderiv ℝ S x).IsInvertible) :
    conditionalObservationEntropy mu
        (fun x => squareGridObservation r box (S x))
        (squareGridObservation r box) ≤
      ∑ y : Option ↥box,
        mu.real (squareGridObservation r box ⁻¹' {y}) *
          Real.log (gridTransitionCardBound S K r box y) := by
  let Y := squareGridObservation r box
  have hY : Measurable Y := measurable_squareGridObservation r box
  exact conditionalObservationEntropy_le_weighted_log_card
    mu (fun x => Y (S x)) (hY.comp hS_meas) Y hY
      (gridTransitionCardBound S K r box)
      (gridTransitionCardBound_pos S K r box)
      (conditionalSupport_squareGrid_card_le
        mu S hS_meas hS_smooth K hmuK hSK C hC_convex hKC
          hB_nonneg hB hr hsmall box hKbox hderiv)

end Submission.Helpers
