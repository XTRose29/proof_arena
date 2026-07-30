import Submission.DegenerateEntropy
import Submission.NegativeExponentAtomic
import Submission.HyperbolicConclusion

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory

theorem entropy_dimension_lyapunov_of_integral_upper_neg
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 : ℝ} (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam1_neg : lam1 < 0) :
    kolmogorovSinaiEntropy mu T =
      (dimMeasure mu).toReal *
        harmonicMeanLyapunov
          (∫ x, lyapunovUpperAt T x ∂mu)
          (∫ x, lyapunovLowerAt T x ∂mu) / 2 := by
  obtain ⟨x, hx⟩ := exists_atom_of_integral_lyapunovUpperAt_neg
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam1_neg
  exact entropy_dimension_lyapunov_of_atom_of_ergodic
    T hT_left.injective mu hT hErg hx

theorem entropy_dimension_lyapunov_of_integral_lower_pos
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam2 : ℝ} (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam2_pos : 0 < lam2) :
    kolmogorovSinaiEntropy mu T =
      (dimMeasure mu).toReal *
        harmonicMeanLyapunov
          (∫ x, lyapunovUpperAt T x ∂mu)
          (∫ x, lyapunovLowerAt T x ∂mu) / 2 := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hlam_inv : -lam2 = ∫ x, lyapunovUpperAt T_inv x ∂mu := by
    calc
      -lam2 = -∫ x, lyapunovLowerAt T x ∂mu := congrArg Neg.neg hlam2
      _ = ∫ x, lyapunovUpperAt T_inv x ∂mu :=
        (integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            K hK_compact hK_inv mu hmu_supp hT hErg).symm
  obtain ⟨x, hx⟩ := exists_atom_of_integral_lyapunovUpperAt_neg
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
      hlam_inv (neg_neg_of_pos hlam2_pos)
  exact entropy_dimension_lyapunov_of_atom_of_ergodic
    T hT_left.injective mu hT hErg hx

theorem entropy_dimension_lyapunov_of_zero_exponent
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu] [NoAtoms mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_nonneg : 0 ≤ lam1) (hlam2_nonpos : lam2 ≤ 0)
    (hzero : lam1 = 0 ∨ lam2 = 0) :
    kolmogorovSinaiEntropy mu T =
      (dimMeasure mu).toReal * harmonicMeanLyapunov lam1 lam2 / 2 := by
  have hentropy := kolmogorovSinaiEntropy_eq_zero_of_zero_lyapunov
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_nonneg hlam2_nonpos hzero
  rcases hzero with rfl | rfl
  · simp [hentropy, harmonicMeanLyapunov]
  · simp [hentropy, harmonicMeanLyapunov]

end Submission.Helpers
