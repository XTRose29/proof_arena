import ChallengeDeps
import Submission.Helpers
import Submission.DimensionOrbit
import Submission.EntropyInverse
import Submission.Orbit
import Submission.PartitionSupport
import Submission.GlobalLightBall
import Submission.HyperbolicConclusion
import Submission.GlobalRateOrbitControl
import Submission.MainReduction
import Submission.HyperbolicLower

open LeanEval.Dynamics
open scoped ENNReal
open MeasureTheory Filter Topology Real
open Submission.Helpers

namespace Submission

theorem entropy_dimension_lyapunov (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane)
    (hK_compact : IsCompact K)
    (hK_inv : T '' K = K)
    (μ : Measure EucPlane) [IsProbabilityMeasure μ]
    (hμ_supp : μ Kᶜ = 0)
    (hμ_pres : MeasurePreserving T μ μ)
    (hμ_erg : Ergodic T μ) :
    kolmogorovSinaiEntropy μ T =
      (dimMeasure μ).toReal *
        harmonicMeanLyapunov
          (∫ x, lyapunovUpperAt T x ∂μ)
          (∫ x, lyapunovLowerAt T x ∂μ) / 2 := by
  classical
  by_cases hatom : ∃ x : EucPlane, μ {x} ≠ 0
  · obtain ⟨x, hx⟩ := hatom
    exact entropy_dimension_lyapunov_of_atom_of_ergodic
      T hT_left.injective μ hμ_pres hμ_erg hx
  · have hall : ∀ x : EucPlane, μ {x} = 0 := by
      push Not at hatom
      exact hatom
    letI : NoAtoms μ := ⟨hall⟩
    let lam1 := ∫ x, lyapunovUpperAt T x ∂μ
    let lam2 := ∫ x, lyapunovLowerAt T x ∂μ
    have hlam1 :
        lam1 = ∫ x, lyapunovUpperAt T x ∂μ := rfl
    have hlam2 :
        lam2 = ∫ x, lyapunovLowerAt T x ∂μ := rfl
    by_cases hlam1_neg : lam1 < 0
    · exact entropy_dimension_lyapunov_of_integral_upper_neg
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          K hK_compact hK_inv μ hμ_supp hμ_pres hμ_erg
          hlam1 hlam1_neg
    have hlam1_nonneg : 0 ≤ lam1 := le_of_not_gt hlam1_neg
    by_cases hlam2_pos : 0 < lam2
    · exact entropy_dimension_lyapunov_of_integral_lower_pos
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          K hK_compact hK_inv μ hμ_supp hμ_pres hμ_erg
          hlam2 hlam2_pos
    have hlam2_nonpos : lam2 ≤ 0 := le_of_not_gt hlam2_pos
    by_cases hzero : lam1 = 0 ∨ lam2 = 0
    · simpa [lam1, lam2] using
        (entropy_dimension_lyapunov_of_zero_exponent
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            K hK_compact hK_inv μ hμ_supp hμ_pres hμ_erg
            hlam1 hlam2 hlam1_nonneg hlam2_nonpos hzero)
    have hlam1_pos : 0 < lam1 :=
      lt_of_le_of_ne hlam1_nonneg (fun h => hzero (Or.inl h.symm))
    have hlam2_neg : lam2 < 0 :=
      lt_of_le_of_ne hlam2_nonpos (fun h => hzero (Or.inr h))
    simpa [lam1, lam2] using
      (young_identity_of_approx_hyperbolic_bounds
        (entropy := kolmogorovSinaiEntropy μ T)
        (dim := (dimMeasure μ).toReal)
        (lam1 := lam1) (lam2 := lam2)
        ENNReal.toReal_nonneg
        (fun epsilon hepsilon =>
          kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_hyperbolicRate_add
            T T_inv hT_smooth hT_inv_smooth hT_left hT_right
              K hK_compact hK_inv μ hμ_supp hμ_pres hμ_erg
              hlam1 hlam2 hlam1_pos hlam2_neg hepsilon)
        (fun epsilon hepsilon =>
          dimMeasure_mul_hyperbolicRate_sub_le_kolmogorovSinaiEntropy
            T T_inv hT_smooth hT_inv_smooth hT_left hT_right
              K hK_compact hK_inv μ hμ_supp hμ_pres hμ_erg
              hlam1 hlam2 hlam1_pos hlam2_neg hepsilon))

end Submission
