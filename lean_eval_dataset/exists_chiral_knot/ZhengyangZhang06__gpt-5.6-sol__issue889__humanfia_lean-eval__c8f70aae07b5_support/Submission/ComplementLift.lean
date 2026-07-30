import Submission.RadialCyclicCover

open scoped unitInterval

namespace Submission.ComplementLift

noncomputable section

abbrev Complement := RadialPhase.Complement

def productMap (u : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, Circle) :=
  ⟨fun x => u (RadialPhase.rotateComplement (x.2 / 6)
      (RadialPhase.fiberComplement x.1)),
    u.continuous.comp (RadialPhase.rotateComplement_continuous.comp
      ((continuous_snd.div_const 6).prodMk
        (RadialPhase.fiberComplement_continuous.comp continuous_fst)))⟩

def fiberLift (u : C(Complement, Circle)) : C(RadialMilnor.Fiber, ℝ) :=
  Classical.choose (CoreCohomology.fiberRestriction_lifts u)

theorem exp_fiberLift (u : C(Complement, Circle)) (q : RadialMilnor.Fiber) :
    Circle.exp (fiberLift u q) = u (RadialPhase.fiberComplement q) :=
  (Classical.choose_spec (CoreCohomology.fiberRestriction_lifts u)) q

def productStartLift (u : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, ℝ) :=
  (fiberLift u).comp ⟨Prod.fst, continuous_fst⟩

def productHomotopy (u : C(Complement, Circle)) :
    C(unitInterval × (RadialMilnor.Fiber × ℝ), Circle) :=
  ⟨fun x => u (RadialPhase.rotateComplement
      (((x.1 : ℝ) * x.2.2) / 6) (RadialPhase.fiberComplement x.2.1)), by
    have hparameter : Continuous
        (fun x : unitInterval × (RadialMilnor.Fiber × ℝ) =>
          (((x.1 : ℝ) * x.2.2) / 6)) := by
      fun_prop
    have hfiber : Continuous
        (fun x : unitInterval × (RadialMilnor.Fiber × ℝ) =>
          RadialPhase.fiberComplement x.2.1) :=
      RadialPhase.fiberComplement_continuous.comp
        (continuous_fst.comp continuous_snd)
    exact u.continuous.comp
      (RadialPhase.rotateComplement_continuous.comp
        (hparameter.prodMk hfiber))⟩

theorem productHomotopy_zero (u : C(Complement, Circle))
    (x : RadialMilnor.Fiber × ℝ) :
    productHomotopy u (0, x) = Circle.exp (productStartLift u x) := by
  change u (RadialPhase.rotateComplement (((0 : ℝ) * x.2) / 6)
      (RadialPhase.fiberComplement x.1)) = Circle.exp (fiberLift u x.1)
  rw [zero_mul, zero_div, RadialPhase.rotateComplement_zero,
    exp_fiberLift]

def productLift (u : C(Complement, Circle)) :
    C(RadialMilnor.Fiber × ℝ, ℝ) :=
  FiberLift.liftEndpoint (productHomotopy u) (productStartLift u)
    (productHomotopy_zero u)

theorem exp_productLift (u : C(Complement, Circle))
    (x : RadialMilnor.Fiber × ℝ) :
    Circle.exp (productLift u x) = productMap u x := by
  rw [productLift, FiberLift.exp_liftEndpoint]
  change u (RadialPhase.rotateComplement (((1 : ℝ) * x.2) / 6)
      (RadialPhase.fiberComplement x.1)) =
    u (RadialPhase.rotateComplement (x.2 / 6)
      (RadialPhase.fiberComplement x.1))
  rw [one_mul]

def coverLift (u : C(Complement, Circle)) : C(RadialCyclicCover.Cover, ℝ) :=
  (productLift u).comp
    ⟨RadialCyclicCover.toFiber, RadialCyclicCover.toFiber_continuous⟩

theorem exp_coverLift (u : C(Complement, Circle))
    (x : RadialCyclicCover.Cover) :
    Circle.exp (coverLift u x) = u x.1.1 := by
  rw [coverLift, ContinuousMap.comp_apply, exp_productLift]
  change u (RadialPhase.rotateComplement
      ((RadialCyclicCover.toFiber x).2 / 6)
      (RadialPhase.fiberComplement (RadialCyclicCover.toFiber x).1)) = u x.1.1
  congr 1
  have h := congrArg (fun y : RadialCyclicCover.Cover => y.1.1)
    (RadialCyclicCover.fromFiber_toFiber x)
  exact h

end

end Submission.ComplementLift
