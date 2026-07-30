import Submission.SphereFiniteCut

open scoped unitInterval

noncomputable section

namespace Submission.SphereFiniteRestrict

open Set
open Submission.SphereRegularApprox
open Submission.SphereFiniteCut

variable {m : ℕ}

theorem leftCube_injective (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) :
    Function.Injective (SphereSplit.leftCube i c hc0 hc1) := by
  intro s t hst
  funext j
  by_cases hji : j = i
  · subst j
    have hi := congrFun hst i
    have hireal := congrArg Subtype.val hi
    simp only [SphereSplit.leftCube, Function.update_self,
      SphereSplit.leftCoordinate] at hireal
    apply Subtype.ext
    exact mul_left_cancel₀ hc0.ne' hireal
  · have hj := congrFun hst j
    simpa only [SphereSplit.leftCube,
      Function.update_of_ne hji] using hj

theorem rightCube_injective (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) :
    Function.Injective (SphereSplit.rightCube i c hc0 hc1) := by
  intro s t hst
  funext j
  by_cases hji : j = i
  · subst j
    have hi := congrFun hst i
    have hireal := congrArg Subtype.val hi
    simp only [SphereSplit.rightCube, Function.update_self,
      SphereSplit.rightCoordinate] at hireal
    have hmul :
        (1 - c) * (s i : ℝ) = (1 - c) * (t i : ℝ) := by
      linarith
    apply Subtype.ext
    exact mul_left_cancel₀ (sub_ne_zero.mpr (ne_of_gt hc1)) hmul
  · have hj := congrFun hst j
    simpa only [SphereSplit.rightCube,
      Function.update_of_ne hji] using hj

theorem leftCube_coordinate_le (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (t : Cube m) :
    ((SphereSplit.leftCube i c hc0 hc1 t) i : ℝ) ≤ c := by
  simp only [SphereSplit.leftCube, Function.update_self,
    SphereSplit.leftCoordinate]
  exact mul_le_of_le_one_right hc0.le (t i).property.2

theorem rightCube_coordinate_ge (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1) (t : Cube m) :
    c ≤ ((SphereSplit.rightCube i c hc0 hc1 t) i : ℝ) := by
  simp only [SphereSplit.rightCube, Function.update_self,
    SphereSplit.rightCoordinate]
  exact le_add_of_nonneg_right <|
    mul_nonneg (sub_nonneg.mpr hc1.le) (t i).property.1

/-- Carry out one well-founded step of finite-fiber decomposition.  The
plateau deformation makes the cut legal, and the two affine restrictions
have antipode fibers of cardinality strictly below the original one. -/
theorem exists_restrictions_with_smaller_fibers
    (q : GenLoop (Fin (m + 1)) (SphereRegularApprox.UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (F : Finset (Cube m))
    (hfiber : ∀ t, t ∈ F ↔
      q t = -(SphereGenerator.canonicalBasepoint m))
    (hcard : 2 ≤ F.card) :
    ∃ pLeft pRight :
        GenLoop (Fin (m + 1)) (SphereRegularApprox.UnitSphere m)
          (SphereGenerator.canonicalBasepoint m),
      GenLoop.Homotopic q
        (GenLoop.transAt (Classical.arbitrary (Fin (m + 1)))
          pLeft pRight) ∧
      (∃ hLeft :
          {t | pLeft t =
            -(SphereGenerator.canonicalBasepoint m)}.Finite,
        hLeft.toFinset.card < F.card) ∧
      (∃ hRight :
          {t | pRight t =
            -(SphereGenerator.canonicalBasepoint m)}.Finite,
        hRight.toFinset.card < F.card) := by
  classical
  obtain ⟨i, c, hc0, hc1, d, hdq, hcut, hpreserve,
    hleftCard, hrightCard, _⟩ :=
    exists_separating_plateau q F hfiber hcard
  let q' := SpherePlateau.genLoop d q
  let pLeft :=
    SphereSplit.leftGenLoop q' i c hc0 hc1 hcut
  let pRight :=
    SphereSplit.rightGenLoop q' i c hc0 hc1 hcut
  have hsplit :
      GenLoop.Homotopic q'
        (GenLoop.transAt i pLeft pRight) :=
    SphereSplit.homotopic_transAt_restrictions
      q' i c hc0 hc1 hcut
  have hleftSet :
      {t | pLeft t =
          -(SphereGenerator.canonicalBasepoint m)} =
        SphereSplit.leftCube i c hc0 hc1 ⁻¹'
          (↑F : Set (Cube m)) := by
    ext t
    change
      q' (SphereSplit.leftCube i c hc0 hc1 t) =
          -(SphereGenerator.canonicalBasepoint m) ↔
        SphereSplit.leftCube i c hc0 hc1 t ∈ F
    exact (hpreserve _).trans (hfiber _).symm
  have hrightSet :
      {t | pRight t =
          -(SphereGenerator.canonicalBasepoint m)} =
        SphereSplit.rightCube i c hc0 hc1 ⁻¹'
          (↑F : Set (Cube m)) := by
    ext t
    change
      q' (SphereSplit.rightCube i c hc0 hc1 t) =
          -(SphereGenerator.canonicalBasepoint m) ↔
        SphereSplit.rightCube i c hc0 hc1 t ∈ F
    exact (hpreserve _).trans (hfiber _).symm
  have hLeft :
      {t | pLeft t =
        -(SphereGenerator.canonicalBasepoint m)}.Finite := by
    rw [hleftSet]
    exact F.finite_toSet.preimage
      (leftCube_injective i c hc0 hc1).injOn
  have hRight :
      {t | pRight t =
        -(SphereGenerator.canonicalBasepoint m)}.Finite := by
    rw [hrightSet]
    exact F.finite_toSet.preimage
      (rightCube_injective i c hc0 hc1).injOn
  have hLeftLe :
      hLeft.toFinset.card ≤
        (F.filter fun t => (t i : ℝ) < c).card := by
    apply Finset.card_le_card_of_injOn
      (SphereSplit.leftCube i c hc0 hc1)
    · intro t ht
      have htroot :
          pLeft t =
            -(SphereGenerator.canonicalBasepoint m) := by
        simpa using ht
      have hq'root :
          q' (SphereSplit.leftCube i c hc0 hc1 t) =
            -(SphereGenerator.canonicalBasepoint m) :=
        htroot
      have hqroot :=
        (hpreserve
          (SphereSplit.leftCube i c hc0 hc1 t)).mp hq'root
      have hmem :
          SphereSplit.leftCube i c hc0 hc1 t ∈ F :=
        (hfiber _).mpr hqroot
      apply Finset.mem_filter.mpr
      refine ⟨hmem, lt_of_le_of_ne
        (leftCube_coordinate_le i c hc0 hc1 t) ?_⟩
      intro heq
      have hsouth := hcut
        (SphereSplit.leftCube i c hc0 hc1 t) heq
      exact SphereRegularApprox.canonicalBasepoint_ne_neg m
        (hsouth.symm.trans hq'root)
    · exact (leftCube_injective i c hc0 hc1).injOn
  have hRightLe :
      hRight.toFinset.card ≤
        (F.filter fun t => c < (t i : ℝ)).card := by
    apply Finset.card_le_card_of_injOn
      (SphereSplit.rightCube i c hc0 hc1)
    · intro t ht
      have htroot :
          pRight t =
            -(SphereGenerator.canonicalBasepoint m) := by
        simpa using ht
      have hq'root :
          q' (SphereSplit.rightCube i c hc0 hc1 t) =
            -(SphereGenerator.canonicalBasepoint m) :=
        htroot
      have hqroot :=
        (hpreserve
          (SphereSplit.rightCube i c hc0 hc1 t)).mp hq'root
      have hmem :
          SphereSplit.rightCube i c hc0 hc1 t ∈ F :=
        (hfiber _).mpr hqroot
      apply Finset.mem_filter.mpr
      refine ⟨hmem, lt_of_le_of_ne
        (rightCube_coordinate_ge i c hc0 hc1 t) ?_⟩
      intro heq
      have hsouth := hcut
        (SphereSplit.rightCube i c hc0 hc1 t) heq.symm
      exact SphereRegularApprox.canonicalBasepoint_ne_neg m
        (hsouth.symm.trans hq'root)
    · exact (rightCube_injective i c hc0 hc1).injOn
  have hclass :
      GenLoop.Homotopic q
        (GenLoop.transAt
          (Classical.arbitrary (Fin (m + 1))) pLeft pRight) := by
    exact hdq.trans <|
      hsplit.trans <|
        Quotient.exact
          (HomotopyGroup.transAt_indep
            (Classical.arbitrary (Fin (m + 1))) pLeft pRight)
  exact ⟨pLeft, pRight, hclass,
    ⟨hLeft, hLeftLe.trans_lt hleftCard⟩,
    ⟨hRight, hRightLe.trans_lt hrightCard⟩⟩

end Submission.SphereFiniteRestrict
