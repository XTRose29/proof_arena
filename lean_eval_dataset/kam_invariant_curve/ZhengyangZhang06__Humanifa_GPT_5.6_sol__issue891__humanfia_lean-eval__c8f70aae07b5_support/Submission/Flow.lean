import Submission.Iteration

open LeanEval.Dynamics
open scoped ContDiff

namespace Submission.Majorant

noncomputable section

def inverseLiftRadius (s : ℕ) (W R : ℝ) : ℝ :=
  4 * max 1 (stepLiftAmplitude s W) * stepLiftRadius s R

def reducedStepAmplitude (α : ℝ) (hα : IsDiophantine α)
    (s : ℕ) (W E R : ℝ) : ℝ :=
  4 * stepAmplitude α hα s W E R

def reducedStepRadius (s : ℕ) (W R : ℝ) : ℝ :=
  4 * max (stepRadius s W R) (inverseLiftRadius s W R)

/-- A bound for the reduced unknown, recovered from the already estimated
Newton step by division by the positive lift derivative. -/
theorem reducedUnknown_majorized {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} (hf : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hus : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1)
    (hgood : Newton.GoodLift u) {s : ℕ} {W E R : ℝ}
    (hu : DerivativeMajorized s W R u)
    (hres : Majorized s E R (Newton.residual α c f u))
    (hW : 0 ≤ W) (hE : 0 ≤ E) (hR : 0 ≤ R) :
    Majorized (s + 2) (reducedStepAmplitude α hα s W E R)
      (reducedStepRadius s W R) (Newton.reducedUnknown α c f u) := by
  let L := stepLiftAmplitude s W
  let T := stepLiftRadius s R
  let A := stepAmplitude α hα s W E R
  let S := stepRadius s W R
  let I := inverseLiftRadius s W R
  have hsolve : 0 ≤ solveConstant α hα := (solveConstant_pos α hα).le
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hL : 0 ≤ L := by unfold L stepLiftAmplitude; positivity
  have hT : 0 ≤ T := by unfold T stepLiftRadius; positivity
  have hA : 0 ≤ A := by
    unfold A stepAmplitude reducedAmplitude secondRhsAmplitude
      firstSolutionAmplitude firstRhsAmplitude stepLiftAmplitude
    positivity
  have hS : 0 ≤ S := by
    unfold S stepRadius reducedRadius secondRhsRadius secondBaseRadius
      firstSolutionRadius inverseTwistRadius firstRhsRadius stepLiftRadius
      stepLiftAmplitude
    positivity
  have hI : 0 ≤ I := by unfold I inverseLiftRadius; positivity
  have hl : Majorized s L T (Newton.liftDeriv u) := by
    simpa only [L, T, stepLiftAmplitude, stepLiftRadius] using
      liftDeriv_majorized_of_derivativeMajorized hu hW hR hgood
  have hlSmooth := Newton.liftDeriv_contDiff hus
  have hlPos (t : ℝ) : (1 : ℝ) / 4 ≤ Newton.liftDeriv u t := by
    linarith [(hgood t).1]
  have hlinv : Majorized (s + 2) 4 I
      (fun t => (Newton.liftDeriv u t)⁻¹) := by
    simpa only [I, L, T, inverseLiftRadius] using
      hl.inv_of_ge_quarter hlSmooth hT hlPos
  have hlinvSmooth : ContDiff ℝ ∞ (fun t => (Newton.liftDeriv u t)⁻¹) :=
    hlSmooth.inv fun t => ne_of_gt
      (lt_of_lt_of_le (show (0 : ℝ) < 1 / 2 by norm_num) (hgood t).1)
  have hstep : Majorized (s + 2) A S (Newton.step α c f u) := by
    simpa only [A, S] using
      step_majorized hα c hf hfper hfmean hus huper hgood hu hres hW hE hR
  have hstepSmooth := Newton.step_contDiff hα c hf hfper hus huper hgood
  have hprod := hstep.mul hlinv hstepSmooth hlinvSmooth hA (by norm_num) hS hI
  change Majorized (s + 2) (4 * A) (4 * max S I)
    (Newton.reducedUnknown α c f u)
  rw [show Newton.reducedUnknown α c f u = fun t =>
      Newton.step α c f u t * (Newton.liftDeriv u t)⁻¹ by
    funext t
    simp only [Newton.step]
    field_simp [ne_of_gt
      (lt_of_lt_of_le (show (0 : ℝ) < 1 / 2 by norm_num) (hgood t).1)]]
  simpa only [max_self, mul_comm] using hprod

def defectAmplitude (α : ℝ) (hα : IsDiophantine α)
    (s : ℕ) (W E R : ℝ) : ℝ :=
  (E * R * 2 ^ s) * reducedStepAmplitude α hα s W E R

def defectRadius (s : ℕ) (W R : ℝ) : ℝ :=
  4 * max (2 ^ (2 * s) * R) (reducedStepRadius s W R)

def nextExponent (sf s : ℕ) : ℕ :=
  max (s + 2) (taylorRemainderExponent sf s (s + 2))

def nextAmplitude (α : ℝ) (hα : IsDiophantine α)
    (c : ℝ) (sf s : ℕ) (F RF W E R : ℝ) : ℝ :=
  defectAmplitude α hα s W E R +
    |c| * taylorRemainderAmplitude sf F RF
      (stepAmplitude α hα s W E R)

def nextRadius (α : ℝ) (hα : IsDiophantine α)
    (sf s : ℕ) (RF W E R : ℝ) : ℝ :=
  max (defectRadius s W R)
    (taylorRemainderRadius sf RF (1 + W)
      (stepAmplitude α hα s W E R) (max 1 R)
      (stepRadius s W R))

/-- Quantitative one-step Newton estimate.  Both terms in the new residual
are quadratic in the old residual amplitude (the Taylor term also carries
the external coupling `|c|`). -/
theorem residual_next_majorized {α : ℝ} (hα : IsDiophantine α)
    (c : ℝ) {f u : ℝ → ℝ} {sf s : ℕ} {F RF W E R : ℝ}
    (hf : Majorized sf F RF f) (hfs : ContDiff ℝ ∞ f)
    (hfper : Function.Periodic f 1)
    (hfmean : ∫ t in (0 : ℝ)..1, f t = 0)
    (hus : ContDiff ℝ ∞ u) (huper : Function.Periodic u 1)
    (hgood : Newton.GoodLift u)
    (hu : DerivativeMajorized s W R u)
    (hres : Majorized s E R (Newton.residual α c f u))
    (hF : 0 ≤ F) (hRF : 0 ≤ RF) (hW : 0 ≤ W)
    (hE : 0 ≤ E) (hR : 0 ≤ R) :
    Majorized (nextExponent sf s)
      (nextAmplitude α hα c sf s F RF W E R)
      (nextRadius α hα sf s RF W E R)
      (Newton.residual α c f (fun t => u t + Newton.step α c f u t)) := by
  let A := stepAmplitude α hα s W E R
  let S := stepRadius s W R
  let U := reducedStepAmplitude α hα s W E R
  let T := reducedStepRadius s W R
  let D := defectAmplitude α hα s W E R
  let Q := defectRadius s W R
  let P := taylorRemainderExponent sf s (s + 2)
  let V := taylorRemainderAmplitude sf F RF A
  let Z := taylorRemainderRadius sf RF (1 + W) A (max 1 R) S
  have hsolve : 0 ≤ solveConstant α hα := (solveConstant_pos α hα).le
  have hpi : 0 ≤ Real.pi := Real.pi_pos.le
  have hA : 0 ≤ A := by
    unfold A stepAmplitude reducedAmplitude secondRhsAmplitude
      firstSolutionAmplitude firstRhsAmplitude stepLiftAmplitude
    positivity
  have hS : 0 ≤ S := by
    unfold S stepRadius reducedRadius secondRhsRadius secondBaseRadius
      firstSolutionRadius inverseTwistRadius firstRhsRadius stepLiftRadius
      stepLiftAmplitude
    positivity
  have hU : 0 ≤ U := by unfold U reducedStepAmplitude; positivity
  have hT : 0 ≤ T := by unfold T reducedStepRadius; positivity
  have hD : 0 ≤ D := by unfold D defectAmplitude; positivity
  have hQ : 0 ≤ Q := by unfold Q defectRadius; positivity
  have hV : 0 ≤ V := by
    unfold V taylorRemainderAmplitude secondDerivativeAmplitude
    positivity
  have hZ : 0 ≤ Z := by unfold Z taylorRemainderRadius; positivity
  have hresSmooth := Newton.residual_contDiff α c hfs hus
  have hred := reducedUnknown_majorized hα c hfs hfper hfmean hus huper
    hgood hu hres hW hE hR
  have hredSmooth := Newton.reducedUnknown_contDiff
    hα c hfs hfper hus huper hgood
  have hdef : Majorized (s + 2) D Q (fun t =>
      deriv (Newton.residual α c f u) t *
        Newton.reducedUnknown α c f u t) := by
    have hd := hres.deriv
    have hp := hd.mul hred (contDiff_infty_iff_deriv.mp hresSmooth).2
      hredSmooth (by positivity) hU (by positivity) hT
    simpa only [D, Q, defectAmplitude, defectRadius, max_self] using
      hp.exponent_mono (by omega) (by positivity) (by positivity)
  have hx := hu.positive_id_add hus hW hR
  have hstep : Majorized (s + 2) A S (Newton.step α c f u) := by
    simpa only [A, S] using
      step_majorized hα c hfs hfper hfmean hus huper hgood hu hres hW hE hR
  have hstepSmooth := Newton.step_contDiff hα c hfs hfper hus huper hgood
  have hrem : Majorized P V Z
      (taylorRemainder f (fun t => t + u t) (Newton.step α c f u)) := by
    simpa only [P, V, Z] using
      taylorRemainder_majorized hf hx hstep hfs (contDiff_id.add hus)
        hstepSmooth hF hRF (by positivity) hA (by positivity) hS
  have hremSmooth : ContDiff ℝ ∞
      (taylorRemainder f (fun t => t + u t) (Newton.step α c f u)) := by
    unfold taylorRemainder
    simpa only [pow_two] using (hstepSmooth.mul hstepSmooth).mul
      (taylorIntegral_contDiff hf hx hstep hfs (contDiff_id.add hus)
        hstepSmooth hF hRF (by positivity) hA (by positivity) hS)
  have hscaled : Majorized P (|c| * V) Z (fun t =>
      c * taylorRemainder f (fun t => t + u t)
        (Newton.step α c f u) t) := by
    simpa only [abs_mul] using hrem.const_mul hremSmooth (c := c)
  have hdef' : Majorized (nextExponent sf s) D
      (nextRadius α hα sf s RF W E R) (fun t =>
        deriv (Newton.residual α c f u) t *
          Newton.reducedUnknown α c f u t) :=
    (hdef.exponent_mono (le_max_left _ _) hD hQ).radius_mono
      hD hQ (le_max_left _ _)
  have hscaled' : Majorized (nextExponent sf s) (|c| * V)
      (nextRadius α hα sf s RF W E R) (fun t =>
        c * taylorRemainder f (fun t => t + u t)
          (Newton.step α c f u) t) :=
    (hscaled.exponent_mono (le_max_right _ _)
      (mul_nonneg (abs_nonneg c) hV) hZ).radius_mono
        (mul_nonneg (abs_nonneg c) hV) hZ (le_max_right _ _)
  rw [show Newton.residual α c f (fun t => u t + Newton.step α c f u t) =
      fun t => deriv (Newton.residual α c f u) t *
        Newton.reducedUnknown α c f u t -
          c * taylorRemainder f (fun t => t + u t)
            (Newton.step α c f u) t by
    funext t
    rw [Newton.residual_add_step hα c hfs hfper hfmean hus huper hgood t,
      taylorRemainder_eq hfs t]]
  simpa only [nextAmplitude, D, V] using
    hdef'.sub hscaled'
      ((contDiff_infty_iff_deriv.mp hresSmooth).2.mul hredSmooth)
      (contDiff_const.mul hremSmooth)

end

end Submission.Majorant
