import Submission.HyperbolicUpper
import Submission.HyperbolicConclusion
import Submission.UniformCenteredDiameterBridge
import Submission.MaximalBadPrefixBlock

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

/-- The analytic Young identity follows once centered partition atoms admit
high-measure exponentially contracting cores. This isolates the remaining
Pesin-shadowing input from the entropy and Hausdorff-dimension argument. -/
theorem hyperbolic_young_identity_of_centered_shadowing
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
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (hshadow : ∀ epsilon gamma : ℝ, 0 < epsilon →
      epsilon < hyperbolicRate lam1 lam2 → 0 < gamma →
      ∃ P : Finset (Set EucPlane), ∃ good : ℕ → Set EucPlane,
        IsMeasurablePartition mu P ∧
        (∀ L, MeasurableSet (good L)) ∧
        (∀ L, mu.real (good L)ᶜ ≤ gamma) ∧
        (∀ L, ∀ A ∈ centeredJoin T T_inv P
            (balancedBackward lam1 lam2 L)
            (balancedForward lam1 lam2 L),
          ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
            dist x y ≤ Real.exp
              (-(hyperbolicRate lam1 lam2 - epsilon) * L)) ∧
        entropyW mu T P ≤ kolmogorovSinaiEntropy mu T) :
    kolmogorovSinaiEntropy mu T =
      (dimMeasure mu).toReal *
        harmonicMeanLyapunov lam1 lam2 / 2 := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hdim_top : dimMeasure mu ≠ ⊤ :=
    dimMeasure_ne_top_of_compact_full_measure mu hK_compact hmu_supp
  have hdim_nonneg : 0 ≤ (dimMeasure mu).toReal :=
    ENNReal.toReal_nonneg
  apply young_identity_of_approx_hyperbolic_bounds hdim_nonneg
  · intro epsilon hepsilon
    exact kolmogorovSinaiEntropy_sub_le_dimMeasure_mul_hyperbolicRate_add
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg hepsilon
  · intro epsilon hepsilon
    by_cases hepsilon_rate :
        epsilon < hyperbolicRate lam1 lam2
    · apply
        dimMeasure_mul_rate_le_kolmogorovSinaiEntropy_of_uniform_centered_pairwise_close
          T T_inv hT_smooth hT_inv_smooth hT_left hT_right
            mu hT hT_inv hErg hdim_top hlam1_pos hlam2_neg
            (sub_pos.mpr hepsilon_rate)
      intro gamma hgamma
      exact hshadow epsilon gamma hepsilon hepsilon_rate hgamma
    · have hrate_epsilon :
          hyperbolicRate lam1 lam2 - epsilon ≤ 0 := by
        linarith
      exact (mul_nonpos_of_nonneg_of_nonpos
        hdim_nonneg hrate_epsilon).trans
          (kolmogorovSinaiEntropy_nonneg mu T)

end Submission.Helpers
