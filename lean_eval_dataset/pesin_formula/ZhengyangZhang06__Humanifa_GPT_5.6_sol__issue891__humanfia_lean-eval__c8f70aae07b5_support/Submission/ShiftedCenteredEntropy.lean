import Submission.SparseParameters

namespace Submission.Helpers

open LeanEval.Dynamics
open Filter MeasureTheory

lemma tendsto_const_mul_nat_add_div
    (kappa : ℝ) (N₀ : ℕ) :
    Tendsto (fun L : ℕ => kappa * (L + N₀) / L)
      atTop (nhds kappa) := by
  have hinv :
      Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfactorBase :
      Tendsto (fun L : ℕ => 1 + (N₀ : ℝ) * (L : ℝ)⁻¹)
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hfactor :
      Tendsto
        (fun L : ℕ => ((L + N₀ : ℕ) : ℝ) / (L : ℝ))
        atTop (nhds 1) := by
    apply hfactorBase.congr'
    filter_upwards [eventually_gt_atTop 0] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp [hL0]
  have hprod :=
    (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => kappa) atTop (nhds kappa)).mul hfactor
  convert hprod using 1
  · funext L
    push_cast
    ring
  · simp

/-- Centered joins at the shifted length `L + N₀` still have entropy rate
`entropyW` when normalized by `L`. -/
lemma tendsto_shifted_centeredJoin_entropy_div
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (P : Finset (Set EucPlane)) (hP : IsMeasurablePartition mu P)
    {lam1 lam2 : ℝ} (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (N₀ : ℕ) :
    Tendsto
      (fun L : ℕ =>
        partitionEntropy mu
          (centeredJoin T T_inv P
            (balancedBackward lam1 lam2 (L + N₀))
            (balancedForward lam1 lam2 (L + N₀))) / L)
      atTop (nhds (entropyW mu T P)) := by
  let u : ℕ → ℝ := fun N =>
    partitionEntropy mu (iteratedJoin T P N)
  have hu :
      Tendsto (fun N : ℕ => u N / N)
        atTop (nhds (entropyW mu T P)) := by
    simpa [u] using
      tendsto_partitionEntropy_iteratedJoin_div_entropyW
        mu T T_inv hT_right hT P hP
  have hshift :
      Tendsto (fun L : ℕ => u (L + N₀) / (L + N₀))
        atTop (nhds (entropyW mu T P)) := by
    simpa [Function.comp_def, Nat.cast_add] using
      hu.comp (tendsto_add_atTop_nat N₀)
  have hinv :
      Tendsto (fun L : ℕ => ((L : ℝ))⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hfactorBase :
      Tendsto (fun L : ℕ => 1 + (N₀ : ℝ) * (L : ℝ)⁻¹)
        atTop (nhds 1) := by
    simpa using tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  have hfactor :
      Tendsto
        (fun L : ℕ => ((L + N₀ : ℕ) : ℝ) / (L : ℝ))
        atTop (nhds 1) := by
    apply hfactorBase.congr'
    filter_upwards [eventually_gt_atTop 0] with L hL
    have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
    push_cast
    field_simp [hL0]
  have hprod := hshift.mul hfactor
  have hshiftDiv :
      Tendsto (fun L : ℕ => u (L + N₀) / L)
        atTop (nhds (entropyW mu T P)) := by
    have hprod' :
        Tendsto (fun L : ℕ => u (L + N₀) / L)
          atTop (nhds (entropyW mu T P * 1)) := by
      apply hprod.congr'
      filter_upwards [eventually_gt_atTop 0] with L hL
      have hL0 : (L : ℝ) ≠ 0 := by exact_mod_cast hL.ne'
      have hLN0 : ((L + N₀ : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp [hL0, hLN0]
      push_cast
      rfl
    simpa using hprod'
  apply hshiftDiv.congr'
  filter_upwards [] with L
  rw [partitionEntropy_centeredJoin
    mu T T_inv hT_left hT hT_inv P hP]
  rw [balancedBackward_add_balancedForward hlam1 hlam2]

end Submission.Helpers
