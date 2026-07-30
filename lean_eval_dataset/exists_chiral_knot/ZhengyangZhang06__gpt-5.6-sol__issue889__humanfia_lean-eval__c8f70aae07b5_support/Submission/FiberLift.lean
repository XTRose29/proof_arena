import Submission.CoreDeformation

open scoped unitInterval

namespace Submission.FiberLift

noncomputable section

def liftEndpoint {A : Type*} [TopologicalSpace A]
    (H : C(unitInterval × A, Circle)) (f : C(A, ℝ))
    (hzero : ∀ a, H (0, a) = Circle.exp (f a)) : C(A, ℝ) :=
  ⟨fun a => Circle.isCoveringMap_exp.liftHomotopy H f hzero (1, a),
    (Circle.isCoveringMap_exp.liftHomotopy H f hzero).continuous.comp
      (continuous_const.prodMk continuous_id)⟩

theorem exp_liftEndpoint {A : Type*} [TopologicalSpace A]
    (H : C(unitInterval × A, Circle)) (f : C(A, ℝ))
    (hzero : ∀ a, H (0, a) = Circle.exp (f a)) (a : A) :
    Circle.exp (liftEndpoint H f hzero a) = H (1, a) := by
  have hlifts := Circle.isCoveringMap_exp.liftHomotopy_lifts H f hzero
  exact congrFun hlifts (1, a)

def coreToFiber : C(RadialCore.Core, RadialMilnor.Fiber) :=
  RadialSpine.spineInclusion.comp CoreDeformation.coreInclusion

def coreRestriction (g : C(RadialMilnor.Fiber, Circle)) :
    C(RadialCore.Core, Circle) :=
  g.comp coreToFiber

def spineRestriction (g : C(RadialMilnor.Fiber, Circle)) :
    C(RadialSpine.Spine, Circle) :=
  g.comp RadialSpine.spineInclusion

def coreLift (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0) :
    C(RadialCore.Core, ℝ) :=
  CoreLift.coreLift (coreRestriction g) hfirst hsecond

def spineStartLift (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0) :
    C(RadialSpine.Spine, ℝ) :=
  (coreLift g hfirst hsecond).comp CoreDeformation.coreRetraction

def spineReverseHomotopy (g : C(RadialMilnor.Fiber, Circle)) :
    C(unitInterval × RadialSpine.Spine, Circle) :=
  ⟨fun x => g (RadialSpine.spineInclusion
      (CoreDeformation.pruneSpine (unitInterval.symm x.1) x.2)), by
    have htime : Continuous (fun x : unitInterval × RadialSpine.Spine =>
        unitInterval.symm x.1) :=
      unitInterval.continuous_symm.comp continuous_fst
    have hpair : Continuous (fun x : unitInterval × RadialSpine.Spine =>
        (unitInterval.symm x.1, x.2)) := htime.prodMk continuous_snd
    have hprune := CoreDeformation.pruneSpine_continuous.comp hpair
    have hinclusion := RadialSpine.spineInclusion.continuous.comp hprune
    have hresult := g.continuous.comp hinclusion
    simpa only [Function.comp_def] using hresult⟩

theorem spineReverseHomotopy_zero (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0)
    (q : RadialSpine.Spine) :
    spineReverseHomotopy g (0, q) =
      Circle.exp (spineStartLift g hfirst hsecond q) := by
  simp only [spineReverseHomotopy, spineStartLift, ContinuousMap.comp_apply]
  change g (RadialSpine.spineInclusion
      (CoreDeformation.pruneSpine (unitInterval.symm 0) q)) =
    Circle.exp (coreLift g hfirst hsecond (CoreDeformation.coreRetraction q))
  rw [unitInterval.symm_zero]
  simp only [coreLift]
  rw [CoreLift.exp_coreLift]
  rfl

def spineLift (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0) :
    C(RadialSpine.Spine, ℝ) :=
  liftEndpoint (spineReverseHomotopy g) (spineStartLift g hfirst hsecond)
    (spineReverseHomotopy_zero g hfirst hsecond)

theorem exp_spineLift (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0)
    (q : RadialSpine.Spine) :
    Circle.exp (spineLift g hfirst hsecond q) = spineRestriction g q := by
  rw [spineLift, exp_liftEndpoint]
  change g (RadialSpine.spineInclusion
    (CoreDeformation.pruneSpine (unitInterval.symm 1) q)) = _
  rw [unitInterval.symm_one, CoreDeformation.pruneSpine_zero_time]
  rfl

def fiberStartLift (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0) :
    C(RadialMilnor.Fiber, ℝ) :=
  (spineLift g hfirst hsecond).comp RadialSpine.spineRetraction

def fiberReverseHomotopy (g : C(RadialMilnor.Fiber, Circle)) :
    C(unitInterval × RadialMilnor.Fiber, Circle) :=
  ⟨fun x => g (RadialSpine.flattenFiber (unitInterval.symm x.1 : ℝ) x.2), by
    have htime : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
        unitInterval.symm x.1) :=
      unitInterval.continuous_symm.comp continuous_fst
    have hpair : Continuous (fun x : unitInterval × RadialMilnor.Fiber =>
        (unitInterval.symm x.1, x.2)) := htime.prodMk continuous_snd
    have hflatten := RadialSpine.flattenFiber_continuous.comp hpair
    have hresult := g.continuous.comp hflatten
    simpa only [Function.comp_def] using hresult⟩

theorem fiberReverseHomotopy_zero (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0)
    (q : RadialMilnor.Fiber) :
    fiberReverseHomotopy g (0, q) =
      Circle.exp (fiberStartLift g hfirst hsecond q) := by
  simp only [fiberReverseHomotopy, fiberStartLift, ContinuousMap.comp_apply]
  change g (RadialSpine.flattenFiber (unitInterval.symm 0 : ℝ) q) =
    Circle.exp (spineLift g hfirst hsecond (RadialSpine.spineRetraction q))
  rw [unitInterval.symm_zero]
  rw [exp_spineLift]
  rfl

def fiberLift (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0) :
    C(RadialMilnor.Fiber, ℝ) :=
  liftEndpoint (fiberReverseHomotopy g) (fiberStartLift g hfirst hsecond)
    (fiberReverseHomotopy_zero g hfirst hsecond)

theorem exp_fiberLift (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0)
    (q : RadialMilnor.Fiber) :
    Circle.exp (fiberLift g hfirst hsecond q) = g q := by
  rw [fiberLift, exp_liftEndpoint]
  change g (RadialSpine.flattenFiber (unitInterval.symm 1 : ℝ) q) = g q
  rw [unitInterval.symm_one]
  change g (RadialSpine.flattenFiber 0 q) = g q
  rw [RadialSpine.flattenFiber_zero_time]

theorem exists_continuous_lift (g : C(RadialMilnor.Fiber, Circle))
    (hfirst : CircleWinding.windingReal
      (CoreCycles.firstCycle.map (coreRestriction g).continuous) = 0)
    (hsecond : CircleWinding.windingReal
      (CoreCycles.secondCycle.map (coreRestriction g).continuous) = 0) :
    ∃ G : C(RadialMilnor.Fiber, ℝ), ∀ q, Circle.exp (G q) = g q :=
  ⟨fiberLift g hfirst hsecond, exp_fiberLift g hfirst hsecond⟩

end

end Submission.FiberLift
