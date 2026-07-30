import Submission.MainReduction
import Submission.HyperbolicLowerReduction

open LeanEval.Dynamics
open scoped ENNReal
open MeasureTheory Filter Topology Real

namespace Submission.Helpers

/-- Reduction of the symplectic-surface Pesin formula to its genuinely
hyperbolic case. Atomic measures and the zero-exponent case are discharged
without any extra assumption. -/
theorem pesin_formula_of_hyperbolic_case
    (T T_inv : EucPlane → EucPlane)
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
    (hμ_erg : Ergodic T μ)
    (hμ_dim : dimMeasure μ = 2)
    (hlam_sym : ∫ x, lyapunovUpperAt T x ∂μ
        = -∫ x, lyapunovLowerAt T x ∂μ)
    (hhyper :
      0 < (∫ x, lyapunovUpperAt T x ∂μ) →
      (∫ x, lyapunovLowerAt T x ∂μ) < 0 →
      kolmogorovSinaiEntropy μ T =
        (dimMeasure μ).toReal *
          harmonicMeanLyapunov
            (∫ x, lyapunovUpperAt T x ∂μ)
            (∫ x, lyapunovLowerAt T x ∂μ) / 2) :
    kolmogorovSinaiEntropy μ T =
      ∫ x, lyapunovUpperAt T x ∂μ := by
  let lam1 : ℝ := ∫ x, lyapunovUpperAt T x ∂μ
  let lam2 : ℝ := ∫ x, lyapunovLowerAt T x ∂μ
  have horder : lam2 ≤ lam1 := by
    simpa [lam1, lam2] using
      integral_lyapunovLowerAt_le_integral_lyapunovUpperAt
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          K hK_compact hK_inv μ hμ_supp
  have hsym : lam1 = -lam2 := by
    simpa [lam1, lam2] using hlam_sym
  have hlam1_nonneg : 0 ≤ lam1 := by
    linarith
  have hlam2_nonpos : lam2 ≤ 0 := by
    linarith
  have finish
      (hyoung :
        kolmogorovSinaiEntropy μ T =
          (dimMeasure μ).toReal * harmonicMeanLyapunov lam1 lam2 / 2) :
      kolmogorovSinaiEntropy μ T = lam1 :=
    pesin_of_entropy_dimension_lyapunov hyoung hμ_dim hsym
  by_cases hatom : ∃ x : EucPlane, μ {x} ≠ 0
  · obtain ⟨x, hx⟩ := hatom
    apply finish
    exact entropy_dimension_lyapunov_of_atom_of_ergodic
      T hT_left.injective μ hμ_pres hμ_erg hx
  · have hsingletons : ∀ x : EucPlane, μ {x} = 0 := by
      intro x
      by_contra hx
      exact hatom ⟨x, hx⟩
    letI : NoAtoms μ := ⟨hsingletons⟩
    by_cases hzero : lam1 = 0
    · apply finish
      exact entropy_dimension_lyapunov_of_zero_exponent
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
          K hK_compact hK_inv μ hμ_supp hμ_pres hμ_erg
          (lam1 := lam1) (lam2 := lam2) rfl rfl
          hlam1_nonneg hlam2_nonpos (Or.inl hzero)
    · have hlam1_pos : 0 < lam1 :=
        lt_of_le_of_ne hlam1_nonneg (Ne.symm hzero)
      have hlam2_neg : lam2 < 0 := by
        linarith
      apply finish
      simpa [lam1, lam2] using hhyper
        (by simpa [lam1] using hlam1_pos)
        (by simpa [lam2] using hlam2_neg)

end Submission.Helpers
