import Submission.CoreAction

namespace Submission.FiberAction

noncomputable section

def coreToFiber : C(RadialCore.Core, RadialMilnor.Fiber) :=
  FiberLift.coreToFiber

def fiberToCore : C(RadialMilnor.Fiber, RadialCore.Core) :=
  CoreDeformation.coreRetraction.comp RadialSpine.spineRetraction

@[simp] theorem fiberToCore_coreToFiber (q : RadialCore.Core) :
    fiberToCore (coreToFiber q) = q := by
  simp [fiberToCore, coreToFiber, FiberLift.coreToFiber]

def fiberCoreHomotopy :
    (ContinuousMap.id RadialMilnor.Fiber).Homotopy
      (coreToFiber.comp fiberToCore) := by
  let Hprune :
      (RadialSpine.spineInclusion.comp RadialSpine.spineRetraction).Homotopy
        (coreToFiber.comp fiberToCore) := by
    let H :=
      ((ContinuousMap.Homotopy.refl RadialSpine.spineInclusion).comp
        CoreDeformation.pruneHomotopy).compContinuousMap
          RadialSpine.spineRetraction
    exact H.cast (by rfl) (by rfl)
  exact RadialSpine.flattenHomotopy.trans Hprune

def inducedCore (f : C(RadialMilnor.Fiber, RadialMilnor.Fiber)) :
    C(RadialCore.Core, RadialCore.Core) :=
  fiberToCore.comp (f.comp coreToFiber)

def action (f : C(RadialMilnor.Fiber, RadialMilnor.Fiber)) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  CoreAction.action (inducedCore f)

def inducedCore_homotopy
    {f g : C(RadialMilnor.Fiber, RadialMilnor.Fiber)} (H : f.Homotopy g) :
    (inducedCore f).Homotopy (inducedCore g) := by
  exact ((ContinuousMap.Homotopy.refl fiberToCore).comp
    (H.compContinuousMap coreToFiber)).cast (by rfl) (by rfl)

theorem action_homotopy_invariant
    {f g : C(RadialMilnor.Fiber, RadialMilnor.Fiber)} (H : f.Homotopy g) :
    action f = action g :=
  CoreAction.action_homotopy_invariant (inducedCore_homotopy H)

def inducedCore_comp_homotopy
    (f g : C(RadialMilnor.Fiber, RadialMilnor.Fiber)) :
    ((inducedCore g).comp (inducedCore f)).Homotopy
      (inducedCore (g.comp f)) := by
  let Hmiddle :
      ((coreToFiber.comp fiberToCore).comp (f.comp coreToFiber)).Homotopy
        (f.comp coreToFiber) :=
    fiberCoreHomotopy.symm.compContinuousMap (f.comp coreToFiber)
  let H := (ContinuousMap.Homotopy.refl (fiberToCore.comp g)).comp Hmiddle
  exact H.cast (by rfl) (by rfl)

theorem action_comp (f g : C(RadialMilnor.Fiber, RadialMilnor.Fiber)) :
    action (g.comp f) = action g * action f := by
  rw [action, action, action]
  rw [← CoreAction.action_comp]
  exact (CoreAction.action_homotopy_invariant
    (inducedCore_comp_homotopy f g)).symm

@[simp] theorem action_id :
    action (ContinuousMap.id RadialMilnor.Fiber) = 1 := by
  have hinduced :
      inducedCore (ContinuousMap.id RadialMilnor.Fiber) =
        ContinuousMap.id RadialCore.Core := by
    ext q
    exact fiberToCore_coreToFiber q
  rw [action, hinduced, CoreAction.action_id]

def monodromyMap : C(RadialMilnor.Fiber, RadialMilnor.Fiber) :=
  RadialMilnor.fiberMonodromyHomeomorph

def monodromyInvMap : C(RadialMilnor.Fiber, RadialMilnor.Fiber) :=
  RadialMilnor.fiberMonodromyHomeomorph.symm

theorem monodromy_coreToFiber (q : RadialCore.Core) :
    monodromyMap (coreToFiber q) =
      coreToFiber (CoreMonodromy.coreMonodromy q) := by
  rfl

theorem inducedCore_monodromy :
    inducedCore monodromyMap = CoreAction.monodromyMap := by
  ext q
  rw [inducedCore, ContinuousMap.comp_apply, ContinuousMap.comp_apply,
    monodromy_coreToFiber]
  exact fiberToCore_coreToFiber (CoreMonodromy.coreMonodromy q)

@[simp] theorem action_monodromy :
    action monodromyMap = Monodromy.trefoilInv := by
  rw [action, inducedCore_monodromy, CoreAction.action_monodromy]

theorem monodromy_comp_inv :
    monodromyMap.comp monodromyInvMap =
      ContinuousMap.id RadialMilnor.Fiber := by
  ext q
  exact RadialMilnor.fiberMonodromyHomeomorph.apply_symm_apply q

@[simp] theorem action_monodromy_inv :
    action monodromyInvMap = Monodromy.trefoil := by
  have haction := action_comp monodromyInvMap monodromyMap
  rw [monodromy_comp_inv, action_id, action_monodromy] at haction
  calc
    action monodromyInvMap = 1 * action monodromyInvMap := by rw [one_mul]
    _ = (Monodromy.trefoil * Monodromy.trefoilInv) *
        action monodromyInvMap := by rw [Monodromy.trefoil_mul_trefoilInv]
    _ = Monodromy.trefoil *
        (Monodromy.trefoilInv * action monodromyInvMap) := by
      rw [mul_assoc]
    _ = Monodromy.trefoil * 1 := by rw [haction]
    _ = Monodromy.trefoil := by rw [mul_one]

end

end Submission.FiberAction
