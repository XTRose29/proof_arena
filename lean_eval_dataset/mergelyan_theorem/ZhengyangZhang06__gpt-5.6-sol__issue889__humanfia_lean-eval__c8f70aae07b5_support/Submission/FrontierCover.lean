import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Submission.FrontierBounds

open Function Set
open scoped Topology

noncomputable section

namespace Submission.Helpers

/-- The finite Besicovitch selection with the ambient satellite bound
supplied explicitly.  This form allows the multiplicity constant to be
chosen before any analytic approximation tolerance. -/
theorem exists_finite_besicovitch_ball_cover_of_no_satelliteConfig
    (S : Set ℂ) (hS : IsCompact S)
    (r : S → ℝ) (R : ℝ)
    (hr : ∀ z, 0 < r z) (hrR : ∀ z, r z ≤ R)
    (N : ℕ) (τ : ℝ) (hτ : 1 < τ)
    (hN : IsEmpty (Besicovitch.SatelliteConfig ℂ N τ)) :
    ∃ (A : Fin N → Set S)
        (t : Finset (Σ k : Fin N, {z : S // z ∈ A k})),
      (∀ k,
        (A k).PairwiseDisjoint
          (fun z ↦ Metric.closedBall (z : ℂ) (r z))) ∧
      S ⊆ ⋃ u ∈ t,
        Metric.ball (u.2.1 : ℂ) (r u.2.1) := by
  let q : Besicovitch.BallPackage S ℂ :=
    { c := fun z ↦ (z : ℂ)
      r := r
      rpos := hr
      r_bound := R
      r_le := hrR }
  obtain ⟨A, hAdisjoint, hAcover⟩ :=
    Besicovitch.exist_disjoint_covering_families hτ hN q
  let U : (Σ k : Fin N, {z : S // z ∈ A k}) → Set ℂ :=
    fun u ↦ Metric.ball (u.2.1 : ℂ) (r u.2.1)
  have hcover : S ⊆ ⋃ u, U u := by
    intro z hz
    have hzrange : z ∈ range q.c := by
      exact ⟨⟨z, hz⟩, rfl⟩
    have hzballs := hAcover hzrange
    rcases mem_iUnion.mp hzballs with ⟨k, hk⟩
    rcases mem_iUnion.mp hk with ⟨j, hj⟩
    rcases mem_iUnion.mp hj with ⟨hjA, hjball⟩
    apply mem_iUnion.mpr
    refine ⟨⟨k, ⟨j, hjA⟩⟩, ?_⟩
    simpa only [U, q] using hjball
  obtain ⟨t, ht⟩ :=
    hS.elim_finite_subcover U
      (fun _ ↦ Metric.isOpen_ball) hcover
  refine ⟨A, t, ?_, ?_⟩
  · simpa only [q] using hAdisjoint
  · simpa only [U] using ht

/-- A compact planar set covered by balls with pointwise positive bounded
radii has a finite subcover selected from finitely many families of pairwise
disjoint closed balls.  The finite number of families depends only on the
ambient plane, not on the chosen radii or on the size of the finite
subcover. -/
theorem exists_finite_besicovitch_ball_cover
    (S : Set ℂ) (hS : IsCompact S)
    (r : S → ℝ) (R : ℝ)
    (hr : ∀ z, 0 < r z) (hrR : ∀ z, r z ≤ R) :
    ∃ (N : ℕ) (A : Fin N → Set S)
        (t : Finset (Σ k : Fin N, {z : S // z ∈ A k})),
      (∀ k,
        (A k).PairwiseDisjoint
          (fun z ↦ Metric.closedBall (z : ℂ) (r z))) ∧
      S ⊆ ⋃ u ∈ t,
        Metric.ball (u.2.1 : ℂ) (r u.2.1) := by
  obtain ⟨N, τ, hτ, hN⟩ :
      ∃ (N : ℕ) (τ : ℝ), 1 < τ ∧
        IsEmpty (Besicovitch.SatelliteConfig ℂ N τ) :=
    HasBesicovitchCovering.no_satelliteConfig
  obtain ⟨A, t, hAdisjoint, hcover⟩ :=
    exists_finite_besicovitch_ball_cover_of_no_satelliteConfig
      S hS r R hr hrR N τ hτ hN
  exact ⟨N, A, t, hAdisjoint, hcover⟩

/-- Choose pointwise positive radii, bounded by a prescribed positive
number, on which a continuous function has a prescribed pointwise
oscillation. -/
theorem exists_positive_bounded_oscillation_radii
    (S : Set ℂ) (F : ℂ → ℂ) (hF : Continuous F)
    (e : S → ℝ) (he : ∀ z, 0 < e z)
    (R : ℝ) (hR : 0 < R) :
    ∃ r : S → ℝ,
      (∀ z, 0 < r z) ∧
      (∀ z, r z ≤ R) ∧
      ∀ (z : S) (w : ℂ), dist w (z : ℂ) < 2 * r z →
        ‖F w - F z‖ < e z := by
  choose δ hδ hFδ using fun z : S ↦
    (Metric.continuousAt_iff.mp hF.continuousAt) (e z) (he z)
  let r : S → ℝ :=
    fun z ↦ min (δ z / 3) (R / 2)
  have hr : ∀ z, 0 < r z := by
    intro z
    exact lt_min (div_pos (hδ z) (by norm_num)) (half_pos hR)
  have hrR : ∀ z, r z ≤ R := by
    intro z
    calc
      r z ≤ R / 2 := min_le_right _ _
      _ ≤ R := by linarith
  refine ⟨r, hr, hrR, ?_⟩
  intro z w hw
  have hrδ : r z ≤ δ z / 3 :=
    min_le_left _ _
  have hwd : dist w (z : ℂ) < δ z := by
    nlinarith [hδ z]
  simpa only [dist_eq_norm] using hFδ z hwd

/-- Combine pointwise oscillation radii with the finite Besicovitch
selection.  This is the cover form needed for summing local frontier
corrections: its overlap complexity is independent of the final finite
subcover's cardinality. -/
theorem exists_finite_besicovitch_oscillation_cover
    (S : Set ℂ) (hS : IsCompact S)
    (F : ℂ → ℂ) (hF : Continuous F)
    (e : S → ℝ) (he : ∀ z, 0 < e z)
    (R : ℝ) (hR : 0 < R) :
    ∃ (r : S → ℝ) (N : ℕ) (A : Fin N → Set S)
        (t : Finset (Σ k : Fin N, {z : S // z ∈ A k})),
      (∀ z, 0 < r z) ∧
      (∀ z, r z ≤ R) ∧
      (∀ (z : S) (w : ℂ), dist w (z : ℂ) < 2 * r z →
        ‖F w - F z‖ < e z) ∧
      (∀ k,
        (A k).PairwiseDisjoint
          (fun z ↦ Metric.closedBall (z : ℂ) (r z))) ∧
      S ⊆ ⋃ u ∈ t,
        Metric.ball (u.2.1 : ℂ) (r u.2.1) := by
  obtain ⟨r, hr, hrR, hosc⟩ :=
    exists_positive_bounded_oscillation_radii
      S F hF e he R hR
  obtain ⟨N, A, t, hAdisjoint, hcover⟩ :=
    exists_finite_besicovitch_ball_cover S hS r R hr hrR
  exact ⟨r, N, A, t, hr, hrR, hosc, hAdisjoint, hcover⟩

end Submission.Helpers
