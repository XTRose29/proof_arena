import Submission.CenteredLightFrostman
import Submission.GeometricBoundaryScale

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory
open scoped ENNReal

lemma ae_eventually_centeredJoin_exponential_ball_subset_of_orbit_control
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    {carrier : Set EucPlane}
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_invariant : T '' carrier = carrier)
    {p : ℕ} (center : Fin p → EucPlane) (radius : Fin p → ℝ)
    (P : Finset (Set EucPlane))
    (hstable : ∀ {u v}, u ∈ carrier → v ∈ carrier →
      (∀ i, u ∈ Metric.ball (center i) (radius i) ↔
        v ∈ Metric.ball (center i) (radius i)) →
      ∀ A ∈ P, u ∈ A ↔ v ∈ A)
    (q : NNReal)
    (m n : ℕ → ℕ) (hsplit : ∀ L, m L + n L = L)
    (hsum : ∀ i,
      (∑' L : ℕ, (L + 1 : ℝ≥0∞) *
        mu {x | |dist x (center i) - radius i| ≤
          geometricBoundaryScale q L}) ≠ ⊤)
    {R : ℝ}
    (horbit : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ y ∈ carrier, dist x y ≤ Real.exp (-R * L) →
        (∀ j : Fin (n L),
          dist (T^[j.val] x) (T^[j.val] y) < geometricBoundaryScale q L) ∧
        ∀ k, 0 < k → k ≤ m L →
          dist (T_inv^[k] x) (T_inv^[k] y) < geometricBoundaryScale q L) :
    ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ A ∈ centeredJoin T T_inv P (m L) (n L), x ∈ A →
        Metric.closedBall x (Real.exp (-R * L)) ∩ carrier ⊆ A := by
  have havoid := ae_eventually_avoids_geometric_centeredBoundaries
    mu T T_inv hT hT_inv center radius q m n hsplit hsum
  filter_upwards [mem_ae_iff.mpr hcarrier_full, horbit, havoid]
    with x hxcarrier hxorbit hxavoid
  filter_upwards [hxorbit, hxavoid] with L hLorbit hLavoid
  intro A hA hxA y hy
  have hxy : dist x y ≤ Real.exp (-R * L) := by
    rw [dist_comm]
    exact Metric.mem_closedBall.mp hy.1
  obtain ⟨hforward, hbackward⟩ := hLorbit y hy.2 hxy
  exact mem_centeredJoin_atom_of_orbit_close_avoiding_boundariesReal
    T T_inv hT_left hT_right hcarrier_invariant center radius P hstable
      hA hxA hxcarrier hy.2 hLavoid hforward hbackward

lemma entropyW_sub_le_dimMeasure_mul_rate_of_balanced_orbit_control
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu) (hErg_inv : Ergodic T_inv mu)
    {carrier : Set EucPlane}
    (hcarrier_measurable : MeasurableSet carrier)
    (hcarrier_full : mu carrierᶜ = 0)
    (hcarrier_invariant : T '' carrier = carrier)
    (hcarrier_dim : dimH carrier = dimMeasure mu)
    (hdim_top : dimMeasure mu ≠ ⊤)
    {p : ℕ} (center : Fin p → EucPlane) (radius : Fin p → ℝ)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    (hstable : ∀ {u v}, u ∈ carrier → v ∈ carrier →
      (∀ i, u ∈ Metric.ball (center i) (radius i) ↔
        v ∈ Metric.ball (center i) (radius i)) →
      ∀ A ∈ P, u ∈ A ↔ v ∈ A)
    (q : NNReal)
    (hsum : ∀ i,
      (∑' L : ℕ, (L + 1 : ℝ≥0∞) *
        mu {x | |dist x (center i) - radius i| ≤
          geometricBoundaryScale q L}) ≠ ⊤)
    {lam1 lam2 epsilon R : ℝ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0) (hepsilon : 0 < epsilon)
    (hR : 0 < R) [NoAtoms mu]
    (horbit : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ y ∈ carrier, dist x y ≤ Real.exp (-R * L) →
        (∀ j : Fin (balancedForward lam1 lam2 L),
          dist (T^[j.val] x) (T^[j.val] y) < geometricBoundaryScale q L) ∧
        ∀ k, 0 < k → k ≤ balancedBackward lam1 lam2 L →
          dist (T_inv^[k] x) (T_inv^[k] y) < geometricBoundaryScale q L) :
    entropyW mu T P - epsilon ≤ (dimMeasure mu).toReal * R := by
  have hjoinSubset :=
    ae_eventually_centeredJoin_exponential_ball_subset_of_orbit_control
      mu T T_inv hT_left hT_right hT hT_inv hcarrier_full hcarrier_invariant
      center radius P hstable q
      (balancedBackward lam1 lam2) (balancedForward lam1 lam2)
      (balancedBackward_add_balancedForward hlam1 hlam2) hsum horbit
  have hlightSubset : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ A ∈ lightAtoms mu
          (centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L))
          ((entropyW mu T P - epsilon) * L),
        x ∈ A → Metric.closedBall x (Real.exp (-R * L)) ∩ carrier ⊆ A := by
    filter_upwards [hjoinSubset] with x hx
    filter_upwards [hx] with L hL
    intro A hAlight
    exact hL A (Finset.mem_filter.mp hAlight).1
  exact entropyW_sub_le_dimMeasure_mul_rate_of_balanced_ball_subset
    mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv P hP
      hcarrier_measurable hcarrier_full hcarrier_dim hdim_top
      hlam1 hlam2 hepsilon hR hlightSubset

end Submission.Helpers
