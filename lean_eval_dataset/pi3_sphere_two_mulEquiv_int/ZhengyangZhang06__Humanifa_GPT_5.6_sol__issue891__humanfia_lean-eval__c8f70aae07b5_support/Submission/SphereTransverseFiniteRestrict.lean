import Submission.SphereFiniteRestrict
import Submission.SphereTransverse

open scoped unitInterval

noncomputable section

namespace Submission.SphereTransverseFiniteRestrict

open Set
open Submission.SphereRegularApprox
open Submission.SphereFiniteCut

variable {m : ℕ}

/-- One separating cut of a transverse finite-fiber loop produces two
transverse loops with strictly smaller antipode fibers. -/
theorem exists_restrictions_with_smaller_fibers
    (q : GenLoop (Fin (m + 1)) (SphereRegularApprox.UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (hq : SphereTransverse.Transverse q)
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
      SphereTransverse.Transverse pLeft ∧
      SphereTransverse.Transverse pRight ∧
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
  have hq' : SphereTransverse.Transverse q' :=
    SphereTransverse.transverse_plateau q d hq
  have hpLeft : SphereTransverse.Transverse pLeft :=
    SphereTransverse.transverse_leftGenLoop
      q' hq' i c hc0 hc1 hcut
  have hpRight : SphereTransverse.Transverse pRight :=
    SphereTransverse.transverse_rightGenLoop
      q' hq' i c hc0 hc1 hcut
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
      (SphereFiniteRestrict.leftCube_injective i c hc0 hc1).injOn
  have hRight :
      {t | pRight t =
        -(SphereGenerator.canonicalBasepoint m)}.Finite := by
    rw [hrightSet]
    exact F.finite_toSet.preimage
      (SphereFiniteRestrict.rightCube_injective i c hc0 hc1).injOn
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
        (SphereFiniteRestrict.leftCube_coordinate_le
          i c hc0 hc1 t) ?_⟩
      intro heq
      have hsouth := hcut
        (SphereSplit.leftCube i c hc0 hc1 t) heq
      exact canonicalBasepoint_ne_neg m
        (hsouth.symm.trans hq'root)
    · exact
        (SphereFiniteRestrict.leftCube_injective
          i c hc0 hc1).injOn
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
        (SphereFiniteRestrict.rightCube_coordinate_ge
          i c hc0 hc1 t) ?_⟩
      intro heq
      have hsouth := hcut
        (SphereSplit.rightCube i c hc0 hc1 t) heq.symm
      exact canonicalBasepoint_ne_neg m
        (hsouth.symm.trans hq'root)
    · exact
        (SphereFiniteRestrict.rightCube_injective
          i c hc0 hc1).injOn
  have hclass :
      GenLoop.Homotopic q
        (GenLoop.transAt
          (Classical.arbitrary (Fin (m + 1))) pLeft pRight) := by
    exact hdq.trans <|
      hsplit.trans <|
        Quotient.exact
          (HomotopyGroup.transAt_indep
            (Classical.arbitrary (Fin (m + 1))) pLeft pRight)
  exact ⟨pLeft, pRight, hclass, hpLeft, hpRight,
    ⟨hLeft, hLeftLe.trans_lt hleftCard⟩,
    ⟨hRight, hRightLe.trans_lt hrightCard⟩⟩

end Submission.SphereTransverseFiniteRestrict
