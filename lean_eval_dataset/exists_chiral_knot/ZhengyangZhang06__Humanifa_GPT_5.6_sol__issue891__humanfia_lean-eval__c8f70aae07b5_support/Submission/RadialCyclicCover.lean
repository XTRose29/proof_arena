import Submission.CoreCohomology

open Complex

namespace Submission.RadialCyclicCover

noncomputable section

abbrev Complement := RadialPhase.Complement

abbrev Cover := {x : Complement × ℝ // RadialPhase.phase x.1 = Circle.exp x.2}

def fromFiber (x : RadialMilnor.Fiber × ℝ) : Cover :=
  ⟨(RadialPhase.rotateComplement (x.2 / 6) (RadialPhase.fiberComplement x.1), x.2), by
    rw [RadialPhase.phase_rotate, RadialPhase.phase_fiber, mul_one]
    congr 1
    ring⟩

theorem polynomial_rotate_back (x : Cover) :
    RadialMilnor.polynomial
        (RadialPhase.rotateComplement (-x.1.2 / 6) x.1.1).1 =
      (‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) := by
  have hphase := congrArg Subtype.val x.2
  change RadialMilnor.polynomial x.1.1.1 /
      ‖RadialMilnor.polynomial x.1.1.1‖ =
    Complex.exp (((x.1.2 : ℂ) * I)) at hphase
  have hradial_ne : RadialMilnor.polynomial x.1.1.1 ≠ 0 := by
    intro hzero
    exact x.1.1.2 ((RadialPhase.polynomial_zero_iff x.1.1.1).mp hzero)
  have hnorm_ne : (‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) ≠ 0 := by
    exact_mod_cast norm_ne_zero_iff.mpr hradial_ne
  have hpoly : RadialMilnor.polynomial x.1.1.1 =
      (‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) *
        Complex.exp (((x.1.2 : ℂ) * I)) := by
    calc
      RadialMilnor.polynomial x.1.1.1 =
          (RadialMilnor.polynomial x.1.1.1 /
              ‖RadialMilnor.polynomial x.1.1.1‖) *
            (‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) :=
        (div_mul_cancel₀ _ hnorm_ne).symm
      _ = Complex.exp (((x.1.2 : ℂ) * I)) *
          (‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) := by rw [hphase]
      _ = (‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) *
          Complex.exp (((x.1.2 : ℂ) * I)) := mul_comm _ _
  change RadialMilnor.polynomial
      (Milnor.weightedRotate (-x.1.2 / 6) x.1.1.1) = _
  rw [RadialMilnor.polynomial_weightedRotate]
  conv_lhs => rw [hpoly]
  have harg : (((6 : ℝ) * (-x.1.2 / 6) : ℝ) : ℂ) * I =
      -(x.1.2 : ℂ) * I := by
    push_cast
    ring
  rw [harg]
  calc
    Complex.exp (-(x.1.2 : ℂ) * I) *
        ((‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) *
          Complex.exp (((x.1.2 : ℂ) * I))) =
      (‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) *
        Complex.exp (-(x.1.2 : ℂ) * I + (x.1.2 : ℂ) * I) := by
          rw [Complex.exp_add]
          ring
    _ = (‖RadialMilnor.polynomial x.1.1.1‖ : ℂ) := by simp

def toFiber (x : Cover) : RadialMilnor.Fiber × ℝ :=
  (⟨(RadialPhase.rotateComplement (-x.1.2 / 6) x.1.1).1, by
      rw [polynomial_rotate_back]
      constructor
      · simpa using norm_pos_iff.mpr (by
          intro hzero
          exact x.1.1.2 ((RadialPhase.polynomial_zero_iff x.1.1.1).mp hzero))
      · simp⟩,
    x.1.2)

theorem toFiber_fromFiber (x : RadialMilnor.Fiber × ℝ) :
    toFiber (fromFiber x) = x := by
  apply Prod.ext
  · apply Subtype.ext
    change (RadialPhase.rotateComplement (-x.2 / 6)
      (RadialPhase.rotateComplement (x.2 / 6)
        (RadialPhase.fiberComplement x.1))).1 = x.1.1
    rw [RadialPhase.rotateComplement_add]
    have hsum : -x.2 / 6 + x.2 / 6 = 0 := by ring
    rw [hsum, RadialPhase.rotateComplement_zero]
    rfl
  · rfl

theorem fromFiber_toFiber (x : Cover) : fromFiber (toFiber x) = x := by
  apply Subtype.ext
  apply Prod.ext
  · change RadialPhase.rotateComplement (x.1.2 / 6)
      (RadialPhase.rotateComplement (-x.1.2 / 6) x.1.1) = x.1.1
    rw [RadialPhase.rotateComplement_add]
    have hsum : x.1.2 / 6 + -x.1.2 / 6 = 0 := by ring
    rw [hsum, RadialPhase.rotateComplement_zero]
  · rfl

def fiberCoverEquiv : RadialMilnor.Fiber × ℝ ≃ Cover where
  toFun := fromFiber
  invFun := toFiber
  left_inv := toFiber_fromFiber
  right_inv := fromFiber_toFiber

theorem fromFiber_continuous : Continuous fromFiber := by
  apply Continuous.subtype_mk
  apply Continuous.prodMk
  · exact RadialPhase.rotateComplement_continuous.comp
      ((continuous_snd.div_const 6).prodMk
        (RadialPhase.fiberComplement_continuous.comp continuous_fst))
  · exact continuous_snd

theorem toFiber_continuous : Continuous toFiber := by
  apply Continuous.prodMk
  · apply Continuous.subtype_mk
    exact continuous_subtype_val.comp
      (RadialPhase.rotateComplement_continuous.comp
        (((continuous_snd.comp continuous_subtype_val).neg.div_const 6).prodMk
          (continuous_fst.comp continuous_subtype_val)))
  · exact continuous_snd.comp continuous_subtype_val

def fiberCoverHomeomorph : RadialMilnor.Fiber × ℝ ≃ₜ Cover where
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
    toFiber (deck x) =
      (RadialMilnor.fiberMonodromy.symm (toFiber x).1,
        (toFiber x).2 + 2 * Real.pi) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;>
      simp [toFiber, deck, RadialPhase.rotateComplement,
        RadialMilnor.fiberMonodromy, RadialMilnor.monodromy,
        Milnor.weightedRotate, Milnor.rotate_add] <;>
      congr 2 <;> ring
  · rfl

theorem toFiber_deck_symm (x : Cover) :
    toFiber (deck.symm x) =
      (RadialMilnor.fiberMonodromy (toFiber x).1,
        (toFiber x).2 - 2 * Real.pi) := by
  apply Prod.ext
  · apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext <;>
      simp [toFiber, deck, RadialPhase.rotateComplement,
        RadialMilnor.fiberMonodromy, RadialMilnor.monodromy,
        Milnor.weightedRotate, Milnor.rotate_add] <;>
      congr 2 <;> ring
  · rfl

end

end Submission.RadialCyclicCover
