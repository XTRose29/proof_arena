import Submission.DerivativeDistortion
import Mathlib.Analysis.InnerProductSpace.LinearMap

namespace Submission.Helpers

open LeanEval.Dynamics
open InnerProductSpace

noncomputable def secantCorrection (v r : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  if v = 0 then 0
  else rankOne Real r ((norm v ^ 2)⁻¹ • v)

lemma secantCorrection_apply_self (v r : EucPlane)
    (hzero : v = 0 → r = 0) :
    secantCorrection v r v = r := by
  by_cases hv : v = 0
  · subst v
    simp [secantCorrection, hzero rfl]
  · have hvnorm : norm v ≠ 0 := norm_ne_zero_iff.mpr hv
    simp [secantCorrection, hv, rankOne_apply, hvnorm]

lemma norm_secantCorrection_le (v r : EucPlane) {B : Real}
    (hrem : norm r <= B * norm v ^ 2) :
    norm (secantCorrection v r) <= B * norm v := by
  by_cases hv : v = 0
  · subst v
    simp [secantCorrection]
  · have hvnorm : 0 < norm v := norm_pos_iff.mpr hv
    rw [secantCorrection, if_neg hv, norm_rankOne, norm_smul]
    simp only [Real.norm_eq_abs, abs_inv, abs_pow, abs_norm]
    have hscale : norm r * (norm v ^ 2)⁻¹ * norm v <= B * norm v := by
      calc
        norm r * (norm v ^ 2)⁻¹ * norm v <=
            (B * norm v ^ 2) * (norm v ^ 2)⁻¹ * norm v := by
          gcongr
        _ = B * norm v := by
          field_simp [hvnorm.ne']
    simpa [mul_assoc] using hscale

noncomputable def secantLinearMap
    (F : EucPlane → EucPlane) (x y : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  let v := y - x
  let D := fderiv Real F x
  let r := F y - F x - D v
  D + secantCorrection v r

lemma secantLinearMap_apply_sub
    (F : EucPlane → EucPlane) (x y : EucPlane) :
    secantLinearMap F x y (y - x) = F y - F x := by
  rw [secantLinearMap]
  simp only [add_apply]
  rw [secantCorrection_apply_self]
  · abel
  · intro hzero
    have hxy : y = x := sub_eq_zero.mp hzero
    subst y
    simp

lemma norm_secantLinearMap_sub_fderiv_le
    (F : EucPlane → EucPlane) (x y : EucPlane) {B : ℝ}
    (hrem : norm (F y - F x - fderiv Real F x (y - x)) <=
      B * norm (y - x) ^ 2) :
    norm (secantLinearMap F x y - fderiv Real F x) <=
      B * norm (y - x) := by
  rw [secantLinearMap]
  simp only [add_sub_cancel_left]
  exact norm_secantCorrection_le (y - x)
    (F y - F x - fderiv Real F x (y - x)) hrem

noncomputable def clmPrefixProduct
    (A : ℕ → EucPlane →L[ℝ] EucPlane) :
    ℕ → EucPlane →L[ℝ] EucPlane
  | 0 => ContinuousLinearMap.id ℝ EucPlane
  | n + 1 => A n ∘L clmPrefixProduct A n

@[simp]
lemma clmPrefixProduct_zero (A : ℕ → EucPlane →L[ℝ] EucPlane) :
    clmPrefixProduct A 0 = ContinuousLinearMap.id ℝ EucPlane := rfl

lemma clmPrefixProduct_succ
    (A : ℕ → EucPlane →L[ℝ] EucPlane) (n : ℕ) :
    clmPrefixProduct A (n + 1) = A n ∘L clmPrefixProduct A n := rfl

noncomputable def orbitSecantStep
    (F : EucPlane → EucPlane) (x y : EucPlane) (k : ℕ) :
    EucPlane →L[ℝ] EucPlane :=
  secantLinearMap F (F^[k] x) (F^[k] y)

lemma clmPrefixProduct_orbitSecantStep_apply
    (F : EucPlane → EucPlane) (x y : EucPlane) (n : ℕ) :
    clmPrefixProduct (orbitSecantStep F x y) n (y - x) =
      F^[n] y - F^[n] x := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [clmPrefixProduct_succ, ContinuousLinearMap.comp_apply, ih]
      simpa [orbitSecantStep, Function.iterate_succ_apply'] using
        secantLinearMap_apply_sub F (F^[n] x) (F^[n] y)

end Submission.Helpers
