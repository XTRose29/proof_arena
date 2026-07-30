import Submission.DeckDegree

namespace Submission.PhaseDegree

noncomputable section

def phaseMap : C(RadialPhase.Complement, Circle) :=
  ⟨RadialPhase.phase, RadialPhase.phase_continuous⟩

theorem productMap_phase (x : RadialMilnor.Fiber × ℝ) :
    ComplementLift.productMap phaseMap x = Circle.exp x.2 := by
  change RadialPhase.phase (RadialPhase.rotateComplement (x.2 / 6)
      (RadialPhase.fiberComplement x.1)) = Circle.exp x.2
  rw [RadialPhase.phase_rotate, RadialPhase.phase_fiber, mul_one]
  congr 1
  ring

def phaseOffset : ℝ :=
  ComplementLift.productLift phaseMap DeckDegree.basePoint

def linearLift : C(RadialMilnor.Fiber × ℝ, ℝ) :=
  ⟨fun x => x.2 + phaseOffset,
    continuous_snd.add continuous_const⟩

theorem exp_phaseOffset : Circle.exp phaseOffset = 1 := by
  rw [phaseOffset, ComplementLift.exp_productLift, productMap_phase]
  simp [DeckDegree.basePoint]

theorem exp_linearLift (x : RadialMilnor.Fiber × ℝ) :
    Circle.exp (linearLift x) =
      Circle.exp (ComplementLift.productLift phaseMap x) := by
  change Circle.exp (x.2 + phaseOffset) =
    Circle.exp (ComplementLift.productLift phaseMap x)
  rw [Circle.exp_add, exp_phaseOffset, mul_one,
    ComplementLift.exp_productLift, productMap_phase]

theorem productLift_phase_eq_linearLift :
    ComplementLift.productLift phaseMap = linearLift := by
  have hfun :
      (ComplementLift.productLift phaseMap : RadialMilnor.Fiber × ℝ → ℝ) =
        (linearLift : RadialMilnor.Fiber × ℝ → ℝ) :=
    Circle.isCoveringMap_exp.eq_of_comp_eq
      (ComplementLift.productLift phaseMap).continuous linearLift.continuous
      (by
        funext x
        exact (exp_linearLift x).symm)
      DeckDegree.basePoint (by
        change ComplementLift.productLift phaseMap DeckDegree.basePoint =
          DeckDegree.basePoint.2 + phaseOffset
        simp [DeckDegree.basePoint, phaseOffset])
  ext x
  exact congrFun hfun x

theorem degree_phase : DeckDegree.degree phaseMap = 1 := by
  have hdeck := DeckDegree.productLift_deckProduct phaseMap DeckDegree.basePoint
  rw [productLift_phase_eq_linearLift] at hdeck
  change (DeckDegree.deckProduct DeckDegree.basePoint).2 + phaseOffset =
    DeckDegree.basePoint.2 + phaseOffset +
      DeckDegree.degree phaseMap * (2 * Real.pi) at hdeck
  simp [DeckDegree.deckProduct, DeckDegree.basePoint] at hdeck
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : (DeckDegree.degree phaseMap : ℝ) = 1 := by
    apply mul_right_cancel₀ htwoPi
    linarith
  exact_mod_cast hcast

end

end Submission.PhaseDegree
