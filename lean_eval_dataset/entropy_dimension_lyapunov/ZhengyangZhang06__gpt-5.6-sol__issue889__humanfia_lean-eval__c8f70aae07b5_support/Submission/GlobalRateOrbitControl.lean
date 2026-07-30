import Submission.CenteredOrbitBridge
import Submission.GlobalOrbitGeometry

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma ae_eventually_balanced_orbit_control_of_global_lipschitz
    (mu : Measure EucPlane) [IsFiniteMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    {K carrier : Set EucPlane}
    (hcarrier_full : mu carrierᶜ = 0) (hcarrierK : carrier ⊆ K)
    (hK_inv : T '' K = K)
    {C D : ℝ} (hC : 1 ≤ C) (hD : 1 ≤ D)
    (hforward_lipschitz :
      ∀ x ∈ K, ∀ y ∈ K, dist (T x) (T y) ≤ C * dist x y)
    (hbackward_lipschitz :
      ∀ x ∈ K, ∀ y ∈ K, dist (T_inv x) (T_inv y) ≤ D * dist x y)
    {lam1 lam2 R : ℝ}
    (q : NNReal)
    (hrate : ∀ᶠ L : ℕ in atTop,
      max (C ^ balancedForward lam1 lam2 L)
          (D ^ balancedBackward lam1 lam2 L) * Real.exp (-R * L) <
        geometricBoundaryScale q L) :
    ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ y ∈ carrier, dist x y ≤ Real.exp (-R * L) →
        (∀ j : Fin (balancedForward lam1 lam2 L),
          dist (T^[j.val] x) (T^[j.val] y) < geometricBoundaryScale q L) ∧
        ∀ k, 0 < k → k ≤ balancedBackward lam1 lam2 L →
          dist (T_inv^[k] x) (T_inv^[k] y) < geometricBoundaryScale q L := by
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hforward := dist_iterate_le_pow_of_lipschitz_on_invariant
    T hK_inv (zero_le_one.trans hC) hforward_lipschitz
  have hbackward := dist_iterate_le_pow_of_lipschitz_on_invariant
    T_inv hK_inv_inv (zero_le_one.trans hD) hbackward_lipschitz
  filter_upwards [mem_ae_iff.mpr hcarrier_full] with x hxcarrier
  filter_upwards [hrate] with L hLrate
  intro y hycarrier hxy
  constructor
  · intro j
    calc
      dist (T^[j.val] x) (T^[j.val] y) ≤ C ^ j.val * dist x y :=
        hforward j.val x (hcarrierK hxcarrier) y (hcarrierK hycarrier)
      _ ≤ C ^ j.val * Real.exp (-R * L) :=
        mul_le_mul_of_nonneg_left hxy (pow_nonneg (zero_le_one.trans hC) _)
      _ ≤ max (C ^ balancedForward lam1 lam2 L)
            (D ^ balancedBackward lam1 lam2 L) * Real.exp (-R * L) := by
        gcongr
        exact (pow_le_pow_right₀ hC (Nat.le_of_lt j.isLt)).trans
          (le_max_left _ _)
      _ < geometricBoundaryScale q L := hLrate
  · intro k hk_pos hk_le
    calc
      dist (T_inv^[k] x) (T_inv^[k] y) ≤ D ^ k * dist x y :=
        hbackward k x (hcarrierK hxcarrier) y (hcarrierK hycarrier)
      _ ≤ D ^ k * Real.exp (-R * L) :=
        mul_le_mul_of_nonneg_left hxy (pow_nonneg (zero_le_one.trans hD) _)
      _ ≤ max (C ^ balancedForward lam1 lam2 L)
            (D ^ balancedBackward lam1 lam2 L) * Real.exp (-R * L) := by
        gcongr
        exact (pow_le_pow_right₀ hD hk_le).trans (le_max_right _ _)
      _ < geometricBoundaryScale q L := hLrate

end Submission.Helpers
