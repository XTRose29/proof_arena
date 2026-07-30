import Submission.SpatialOrbitUpper
import Submission.BalancedNonlinearOrbit
import Submission.DimensionOrbit

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

theorem kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_hyperbolicRate_add
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 epsilon : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (hepsilon : 0 < epsilon) :
    kolmogorovSinaiEntropy mu T - epsilon ≤
      (dimMeasure mu).toReal *
        (hyperbolicRate lam1 lam2 + epsilon) := by
  let eta := epsilon / 2
  have heta : 0 < eta := div_pos hepsilon (by norm_num)
  have hT_inv := measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hT
  have hErg_inv := ergodic_inverse T T_inv hT_smooth hT_inv_smooth
    hT_left hT_right mu hErg
  obtain ⟨carrier, hcarrier_measurable, hcarrier_full,
      hcarrier_invariant, hcarrierK, hcarrier_dim⟩ :=
    exists_invariant_full_measure_dimMeasure_subset
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp
  obtain ⟨q, hq_pos, hq_lt, horbitK⟩ :=
    exists_ae_eventually_balanced_nonlinear_orbit_control
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
  have horbit : ∀ᵐ x ∂mu, ∀ᶠ L : ℕ in atTop,
      ∀ y ∈ carrier,
        dist x y ≤ Real.exp
            (-(hyperbolicRate lam1 lam2 + eta) * L) →
          (∀ j : Fin (balancedForward lam1 lam2 L),
            dist (T^[j.val] x) (T^[j.val] y) <
              geometricBoundaryScale q L) ∧
          ∀ k, 0 < k → k ≤ balancedBackward lam1 lam2 L →
            dist (T_inv^[k] x) (T_inv^[k] y) <
              geometricBoundaryScale q L := by
    filter_upwards [horbitK] with x hx
    filter_upwards [hx] with L hL
    intro y hy
    exact hL y (hcarrierK hy)
  have hbound :=
    kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_rate_of_orbit_control
      mu T T_inv hT_left hT_right hT hT_inv hErg hErg_inv
        hK_compact hcarrier_measurable hcarrier_full hcarrier_invariant
        hcarrierK hcarrier_dim
        (dimMeasure_ne_top_of_compact_full_measure mu hK_compact hmu_supp)
        q hq_pos hq_lt hlam1_pos hlam2_neg heta
        (add_pos (hyperbolicRate_pos hlam1_pos hlam2_neg) heta) horbit
  have hdim_nonneg : 0 ≤ (dimMeasure mu).toReal := ENNReal.toReal_nonneg
  dsimp [eta] at hbound ⊢
  nlinarith

end Submission.Helpers
