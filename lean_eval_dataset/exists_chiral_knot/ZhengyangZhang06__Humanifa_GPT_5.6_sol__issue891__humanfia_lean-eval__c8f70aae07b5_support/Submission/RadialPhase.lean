import Submission.FiberLift
import Submission.CompactifiedSymmetry

open Complex

namespace Submission.RadialPhase

noncomputable section

abbrev Complement := CompactifiedSymmetry.Complement

theorem polynomial_zero_iff (q : Milnor.CSphere) :
    RadialMilnor.polynomial q = 0 ↔ Milnor.polynomial q = 0 := by
  rw [RadialMilnor.polynomial_zero_iff_range, Milnor.polynomial_zero_iff_range]

def phase (q : Complement) : Circle :=
  ⟨RadialMilnor.polynomial q.1 / ‖RadialMilnor.polynomial q.1‖, by
    have hne : RadialMilnor.polynomial q.1 ≠ 0 := by
      intro hzero
      exact q.2 ((polynomial_zero_iff q.1).mp hzero)
    simp [Submonoid.unitSphere, norm_ne_zero_iff.mpr hne]⟩

@[simp] theorem phase_coe (q : Complement) :
    (phase q : ℂ) = RadialMilnor.polynomial q.1 /
      ‖RadialMilnor.polynomial q.1‖ :=
  rfl

theorem phase_continuous : Continuous phase := by
  apply Continuous.subtype_mk
  have hpoly : Continuous (fun q : Complement => RadialMilnor.polynomial q.1) :=
    RadialMilnor.polynomial_continuous.comp continuous_subtype_val
  exact hpoly.div (Complex.continuous_ofReal.comp hpoly.norm) (fun q => by
    exact_mod_cast norm_ne_zero_iff.mpr (by
      intro hzero
      exact q.2 ((polynomial_zero_iff q.1).mp hzero)))

def rotateComplement (s : ℝ) : Complement ≃ Complement where
  toFun q := ⟨Milnor.weightedRotate s q.1, by
    intro hzero
    apply q.2
    apply (polynomial_zero_iff q.1).mp
    have hradial : RadialMilnor.polynomial
        (Milnor.weightedRotate s q.1) = 0 :=
      (polynomial_zero_iff _).mpr hzero
    rw [RadialMilnor.polynomial_weightedRotate] at hradial
    exact (mul_eq_zero.mp hradial).resolve_left (Complex.exp_ne_zero _)⟩
  invFun q := ⟨(Milnor.weightedRotate s).symm q.1, by
    intro hzero
    apply q.2
    have h := Milnor.polynomial_weightedRotate s
      ((Milnor.weightedRotate s).symm q.1)
    rw [Equiv.apply_symm_apply, hzero, mul_zero] at h
    exact h⟩
  left_inv q := by
    apply Subtype.ext
    exact (Milnor.weightedRotate s).symm_apply_apply q.1
  right_inv q := by
    apply Subtype.ext
    exact Equiv.apply_symm_apply (Milnor.weightedRotate s) q.1

def rotateComplementHomeomorph (s : ℝ) : Complement ≃ₜ Complement where
  toEquiv := rotateComplement s
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (Milnor.weightedRotateHomeomorph s).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact (Milnor.weightedRotateHomeomorph s).symm.continuous.comp continuous_subtype_val

theorem rotateComplement_continuous :
    Continuous (fun x : ℝ × Complement => rotateComplement x.1 x.2) := by
  apply Continuous.subtype_mk
  exact Milnor.weightedRotate_continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

theorem rotateComplement_add (s t : ℝ) (q : Complement) :
    rotateComplement s (rotateComplement t q) = rotateComplement (s + t) q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;>
    simp [rotateComplement, Milnor.weightedRotate, Milnor.rotate_add]

@[simp] theorem rotateComplement_zero (q : Complement) : rotateComplement 0 q = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;>
    simp [rotateComplement, Milnor.weightedRotate, Milnor.rotate_zero]

theorem phase_rotate (s : ℝ) (q : Complement) :
    phase (rotateComplement s q) = Circle.exp (6 * s) * phase q := by
  apply Subtype.ext
  change RadialMilnor.polynomial (Milnor.weightedRotate s q.1) /
      ‖RadialMilnor.polynomial (Milnor.weightedRotate s q.1)‖ =
    Complex.exp ((((6 * s : ℝ) : ℂ) * Complex.I)) *
      (RadialMilnor.polynomial q.1 / ‖RadialMilnor.polynomial q.1‖)
  rw [RadialMilnor.polynomial_weightedRotate, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  ring

def fiberComplement (q : RadialMilnor.Fiber) : Complement :=
  ⟨q.1, by
    intro hzero
    have hradial := (polynomial_zero_iff q.1).mpr hzero
    have hpos := q.2.1
    rw [hradial] at hpos
    norm_num at hpos⟩

theorem fiberComplement_continuous : Continuous fiberComplement := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem phase_fiber (q : RadialMilnor.Fiber) : phase (fiberComplement q) = 1 := by
  apply Subtype.ext
  change RadialMilnor.polynomial q.1 / ‖RadialMilnor.polynomial q.1‖ = (1 : ℂ)
  have hreal : RadialMilnor.polynomial q.1 = (RadialMilnor.polynomial q.1).re := by
    apply Complex.ext
    · simp
    · simpa using q.2.2
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos q.2.1]
  exact div_self (by exact_mod_cast ne_of_gt q.2.1)

theorem fiberComplement_monodromy (q : RadialMilnor.Fiber) :
    fiberComplement (RadialMilnor.fiberMonodromy q) =
      rotateComplement (Real.pi / 3) (fiberComplement q) :=
  rfl

end

end Submission.RadialPhase
