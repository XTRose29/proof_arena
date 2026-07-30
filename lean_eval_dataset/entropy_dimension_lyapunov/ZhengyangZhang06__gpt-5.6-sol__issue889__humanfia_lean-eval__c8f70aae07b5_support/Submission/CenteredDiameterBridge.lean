import Submission.CenteredGoodSetHausdorff

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma ediam_inter_le_of_pairwise_dist_le
    {M : Type*} [PseudoMetricSpace M]
    {A good : Set M} {r : ℝ}
    (hpair : ∀ x ∈ A ∩ good, ∀ y ∈ A ∩ good, dist x y ≤ r) :
    Metric.ediam (A ∩ good) ≤ ENNReal.ofReal r := by
  apply Metric.ediam_le
  intro x hx y hy
  rw [edist_dist]
  exact ENNReal.ofReal_le_ofReal (hpair x hx y hy)

lemma dimMeasure_mul_rate_le_entropyW_of_balanced_centered_pairwise_close
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (hErg : Ergodic T mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    (hdim_top : dimMeasure mu ≠ ⊤)
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (good : ℕ → Set EucPlane) (hgood_measurable : ∀ L, MeasurableSet (good L))
    (hgood_full : mu (liminf good atTop)ᶜ = 0)
    {R : ℝ} (hR : 0 < R)
    (hpair : ∀ L, ∀ A ∈ centeredJoin T T_inv P
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L),
      ∀ x ∈ A ∩ good L, ∀ y ∈ A ∩ good L,
        dist x y ≤ Real.exp (-R * L)) :
    (dimMeasure mu).toReal * R ≤ entropyW mu T P := by
  apply dimMeasure_mul_rate_le_entropyW_of_balanced_centered_good_diameter
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right mu hT hT_inv hErg
      P hP hdim_top hlam1 hlam2 good hgood_measurable hgood_full hR
  intro L A hA
  exact ediam_inter_le_of_pairwise_dist_le (hpair L A hA)

end Submission.Helpers
