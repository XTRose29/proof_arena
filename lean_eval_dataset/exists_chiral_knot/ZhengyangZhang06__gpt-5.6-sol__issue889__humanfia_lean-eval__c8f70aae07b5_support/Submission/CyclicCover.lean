import Submission.CompactifiedSymmetry
import Mathlib.Analysis.SpecialFunctions.Complex.Circle

open Complex

namespace Submission.CyclicCover

noncomputable section

abbrev Complement := CompactifiedSymmetry.Complement

def phase (q : Complement) : Circle :=
  ⟨Milnor.polynomial q.1 / ‖Milnor.polynomial q.1‖, by
    simp [Submonoid.unitSphere, norm_ne_zero_iff.mpr q.2]⟩

@[simp] theorem phase_coe (q : Complement) :
    (phase q : ℂ) = Milnor.polynomial q.1 / ‖Milnor.polynomial q.1‖ :=
  rfl

def rotateComplement (s : ℝ) : Complement ≃ Complement where
  toFun q := ⟨Milnor.weightedRotate s q.1, by
    rw [Milnor.polynomial_weightedRotate]
    exact mul_ne_zero (Complex.exp_ne_zero _) q.2⟩
  invFun q := ⟨(Milnor.weightedRotate s).symm q.1, by
    intro hzero
    apply q.2
    have h := Milnor.polynomial_weightedRotate s ((Milnor.weightedRotate s).symm q.1)
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
    change Continuous (fun q : Complement => Milnor.weightedRotate s q.1)
    exact (Milnor.weightedRotateHomeomorph s).continuous.comp continuous_subtype_val
  continuous_invFun := by
    apply Continuous.subtype_mk
    change Continuous (fun q : Complement => (Milnor.weightedRotate s).symm q.1)
    exact (Milnor.weightedRotateHomeomorph s).symm.continuous.comp continuous_subtype_val

theorem rotateComplement_continuous :
    Continuous (fun x : ℝ × Complement => rotateComplement x.1 x.2) := by
  apply Continuous.subtype_mk
  exact Milnor.weightedRotate_continuous.comp
    (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

@[simp] theorem rotateComplement_coe (s : ℝ) (q : Complement) :
    (rotateComplement s q).1 = Milnor.weightedRotate s q.1 :=
  rfl

theorem rotateComplement_add (s t : ℝ) (q : Complement) :
    rotateComplement s (rotateComplement t q) = rotateComplement (s + t) q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;> simp [rotateComplement, Milnor.weightedRotate, Milnor.rotate_add]

@[simp] theorem rotateComplement_zero (q : Complement) : rotateComplement 0 q = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext <;> simp [rotateComplement, Milnor.weightedRotate, Milnor.rotate_zero]

theorem phase_rotate (s : ℝ) (q : Complement) :
    phase (rotateComplement s q) = Circle.exp (6 * s) * phase q := by
  apply Subtype.ext
  change Milnor.polynomial (Milnor.weightedRotate s q.1) /
      ‖Milnor.polynomial (Milnor.weightedRotate s q.1)‖ =
    Complex.exp ((((6 * s : ℝ) : ℂ) * I)) *
      (Milnor.polynomial q.1 / ‖Milnor.polynomial q.1‖)
  rw [Milnor.polynomial_weightedRotate, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]
  ring

def fiberComplement (q : Milnor.Fiber) : Complement :=
  ⟨q.1, by
    intro hzero
    have := q.2.1
    rw [hzero] at this
    norm_num at this⟩

theorem fiberComplement_continuous : Continuous fiberComplement := by
  apply Continuous.subtype_mk
  exact continuous_subtype_val

theorem phase_fiber (q : Milnor.Fiber) : phase (fiberComplement q) = 1 := by
  apply Subtype.ext
  change Milnor.polynomial q.1 / ‖Milnor.polynomial q.1‖ = (1 : ℂ)
  have hreal : Milnor.polynomial q.1 = (Milnor.polynomial q.1).re := by
    apply Complex.ext
    · simp
    · simpa using q.2.2
  rw [hreal, Complex.norm_real, Real.norm_eq_abs, abs_of_pos q.2.1]
  exact div_self (by exact_mod_cast ne_of_gt q.2.1)

abbrev Cover := {x : Complement × ℝ // phase x.1 = Circle.exp x.2}

def fromFiber (x : Milnor.Fiber × ℝ) : Cover :=
  ⟨(rotateComplement (x.2 / 6) (fiberComplement x.1), x.2), by
    rw [phase_rotate, phase_fiber, mul_one]
    congr 1
    ring⟩

theorem polynomial_rotate_back (x : Cover) :
    Milnor.polynomial (rotateComplement (-x.1.2 / 6) x.1.1).1 =
      (‖Milnor.polynomial x.1.1.1‖ : ℂ) := by
  have hphase := congrArg Subtype.val x.2
  change Milnor.polynomial x.1.1.1 / ‖Milnor.polynomial x.1.1.1‖ =
      Complex.exp (((x.1.2 : ℂ) * I)) at hphase
  have hnorm_ne : (‖Milnor.polynomial x.1.1.1‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr x.1.1.2
  have hpoly : Milnor.polynomial x.1.1.1 =
      (‖Milnor.polynomial x.1.1.1‖ : ℂ) * Complex.exp (((x.1.2 : ℂ) * I)) := by
    calc
      Milnor.polynomial x.1.1.1 =
          (Milnor.polynomial x.1.1.1 / ‖Milnor.polynomial x.1.1.1‖) *
            (‖Milnor.polynomial x.1.1.1‖ : ℂ) :=
        (div_mul_cancel₀ _ hnorm_ne).symm
      _ = Complex.exp (((x.1.2 : ℂ) * I)) *
          (‖Milnor.polynomial x.1.1.1‖ : ℂ) := by rw [hphase]
      _ = (‖Milnor.polynomial x.1.1.1‖ : ℂ) *
          Complex.exp (((x.1.2 : ℂ) * I)) := mul_comm _ _
  change Milnor.polynomial (Milnor.weightedRotate (-x.1.2 / 6) x.1.1.1) = _
  rw [Milnor.polynomial_weightedRotate]
  conv_lhs => rw [hpoly]
  have harg : (((6 : ℝ) * (-x.1.2 / 6) : ℝ) : ℂ) * I =
      -(x.1.2 : ℂ) * I := by
    push_cast
    ring
  rw [harg]
  calc
    Complex.exp (-(x.1.2 : ℂ) * I) *
        ((‖Milnor.polynomial x.1.1.1‖ : ℂ) *
          Complex.exp (((x.1.2 : ℂ) * I))) =
      (‖Milnor.polynomial x.1.1.1‖ : ℂ) *
        Complex.exp (-(x.1.2 : ℂ) * I + (x.1.2 : ℂ) * I) := by
          rw [Complex.exp_add]
          ring
    _ = (‖Milnor.polynomial x.1.1.1‖ : ℂ) := by simp

def toFiber (x : Cover) : Milnor.Fiber × ℝ :=
  (⟨(rotateComplement (-x.1.2 / 6) x.1.1).1, by
      rw [polynomial_rotate_back]
      constructor
      · simpa using norm_pos_iff.mpr x.1.1.2
      · simp⟩,
    x.1.2)

theorem toFiber_fromFiber (x : Milnor.Fiber × ℝ) : toFiber (fromFiber x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    change (rotateComplement (-x.2 / 6) (rotateComplement (x.2 / 6)
      (fiberComplement x.1))).1 = x.1.1
    rw [rotateComplement_add]
    have hsum : -x.2 / 6 + x.2 / 6 = 0 := by ring
    rw [hsum, rotateComplement_zero]
    rfl
  · rfl

theorem fromFiber_toFiber (x : Cover) : fromFiber (toFiber x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · change rotateComplement (x.1.2 / 6)
      (rotateComplement (-x.1.2 / 6) x.1.1) = x.1.1
    rw [rotateComplement_add]
    have hsum : x.1.2 / 6 + -x.1.2 / 6 = 0 := by ring
    rw [hsum, rotateComplement_zero]
  · rfl

def fiberCoverEquiv : Milnor.Fiber × ℝ ≃ Cover where
  toFun := fromFiber
  invFun := toFiber
  left_inv := toFiber_fromFiber
  right_inv := fromFiber_toFiber

theorem fromFiber_continuous : Continuous fromFiber := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact rotateComplement_continuous.comp
      ((continuous_snd.div_const 6).prodMk
        (fiberComplement_continuous.comp continuous_fst))
  · exact continuous_snd

theorem toFiber_continuous : Continuous toFiber := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.comp (rotateComplement_continuous.comp
      (((continuous_snd.comp continuous_subtype_val).neg.div_const 6).prodMk
        (continuous_fst.comp continuous_subtype_val)))
  · exact continuous_snd.comp continuous_subtype_val

def fiberCoverHomeomorph : Milnor.Fiber × ℝ ≃ₜ Cover where
  toEquiv := fiberCoverEquiv
  continuous_toFun := fromFiber_continuous
  continuous_invFun := toFiber_continuous

def deck : Cover ≃ Cover where
  toFun x := ⟨(x.1.1, x.1.2 + 2 * Real.pi), by
    rw [Circle.exp_add]
    simpa using x.2⟩
  invFun x := ⟨(x.1.1, x.1.2 - 2 * Real.pi), by
    rw [Circle.exp_sub]
    simpa using x.2⟩
  left_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> simp
  right_inv x := by
    apply Subtype.ext
    apply Prod.ext <;> simp

theorem toFiber_deck (x : Cover) :
    toFiber (deck x) = (Milnor.fiberMonodromy.symm (toFiber x).1, (toFiber x).2 + 2 * Real.pi) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;>
      simp [toFiber, deck, rotateComplement, Milnor.fiberMonodromy, Milnor.monodromy,
        Milnor.weightedRotate, Milnor.rotate_add] <;>
      congr 2 <;> ring
  · rfl

theorem toFiber_deck_symm (x : Cover) :
    toFiber (deck.symm x) =
      (Milnor.fiberMonodromy (toFiber x).1, (toFiber x).2 - 2 * Real.pi) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;>
      simp [toFiber, deck, rotateComplement, Milnor.fiberMonodromy, Milnor.monodromy,
        Milnor.weightedRotate, Milnor.rotate_add] <;>
      congr 2 <;> ring
  · rfl

end

end Submission.CyclicCover
