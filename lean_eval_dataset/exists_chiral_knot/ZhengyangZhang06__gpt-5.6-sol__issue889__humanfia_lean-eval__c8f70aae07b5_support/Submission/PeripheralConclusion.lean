import Submission.PeripheralBoundary

open scoped Topology unitInterval
open LeanEval.KnotTheory

namespace Submission.PeripheralConclusion

noncomputable section

set_option maxHeartbeats 2000000

abbrev NegativeSymmetry := Symmetry.NegativeSymmetry AlgebraicTrefoil.knot
abbrev Fiber := RadialMilnor.Fiber
abbrev Core := RadialCore.Core

def localTorusOfFiber (q : Fiber)
    (hlocal : q.1 ∈ PeripheralCollar.LocalTubeSphere) :
    PeripheralTube.TorusRegion :=
  PeripheralBoundary.torusRegionOfLocalSphere q.1 hlocal

def collarParameterOfLocalFiber (q : Fiber)
    (hlocal : q.1 ∈ PeripheralCollar.LocalTubeSphere) :
    PeripheralCollar.CollarParameter :=
  PeripheralCollar.collarParameterOfFiber q (localTorusOfFiber q hlocal) rfl
    (PeripheralBoundary.torusRegionOfLocalSphere_mem q.1 hlocal).2.2

theorem collarFiber_collarParameterOfLocalFiber (q : Fiber)
    (hlocal : q.1 ∈ PeripheralCollar.LocalTubeSphere) :
    PeripheralCollar.collarFiber (collarParameterOfLocalFiber q hlocal) = q := by
  exact PeripheralCollar.collarFiber_collarParameterOfFiber q
    (localTorusOfFiber q hlocal) rfl
    (PeripheralBoundary.torusRegionOfLocalSphere_mem q.1 hlocal).2.2
    (PeripheralBoundary.torusRegionOfLocalSphere_mem q.1 hlocal).2.1

theorem collarParameterOfLocalFiber_continuous
    {Y : Type*} [TopologicalSpace Y] (f : Y → Fiber) (hf : Continuous f)
    (hlocal : ∀ y, (f y).1 ∈ PeripheralCollar.LocalTubeSphere) :
    Continuous (fun y => collarParameterOfLocalFiber (f y) (hlocal y)) := by
  apply Continuous.subtype_mk
  have hvalue : Continuous (fun y => RadialMilnor.polynomial (f y).1) :=
    RadialMilnor.polynomial_continuous.comp
      (continuous_subtype_val.comp hf)
  have htorus : Continuous (fun y => localTorusOfFiber (f y) (hlocal y)) :=
    PeripheralBoundary.torusRegionOfLocalSphere_continuous
      (fun y => (f y).1) (continuous_subtype_val.comp hf) hlocal
  exact (Complex.continuous_re.comp hvalue).prodMk
    (PeripheralBoundary.longitude_continuous.comp htorus)

def collarPathOfLocalFiber {q : Fiber} (gamma : Path q q)
    (hlocal : ∀ t : unitInterval,
      (gamma t).1 ∈ PeripheralCollar.LocalTubeSphere) :
    Path (collarParameterOfLocalFiber (gamma 0) (hlocal 0))
      (collarParameterOfLocalFiber (gamma 0) (hlocal 0)) where
  toFun t := collarParameterOfLocalFiber (gamma t) (hlocal t)
  continuous_toFun :=
    collarParameterOfLocalFiber_continuous gamma gamma.continuous hlocal
  source' := rfl
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · change (RadialMilnor.polynomial (gamma 1).1).re =
        (RadialMilnor.polynomial (gamma 0).1).re
      rw [gamma.target, gamma.source]
    · apply congrArg PeripheralTube.longitude
      apply Subtype.ext
      change (gamma 1).1 = (gamma 0).1
      rw [gamma.target, gamma.source]

@[simp] theorem collarPathOfLocalFiber_apply {q : Fiber} (gamma : Path q q)
    (hlocal : ∀ t : unitInterval,
      (gamma t).1 ∈ PeripheralCollar.LocalTubeSphere) (t : unitInterval) :
    collarPathOfLocalFiber gamma hlocal t =
      collarParameterOfLocalFiber (gamma t) (hlocal t) :=
  rfl

theorem collarCorePath_eq {q : Fiber} (gamma : Path q q)
    (hlocal : ∀ t : unitInterval,
      (gamma t).1 ∈ PeripheralCollar.LocalTubeSphere) :
    (((collarPathOfLocalFiber gamma hlocal).map
        PeripheralBoundary.collarCoreMap.continuous) :
      C(unitInterval, Core)) =
      (gamma.map FiberAction.fiberToCore.continuous : C(unitInterval, Core)) := by
  ext t
  exact congrArg FiberAction.fiberToCore
    (collarFiber_collarParameterOfLocalFiber (gamma t) (hlocal t))

def fiberSpherePath {q : Fiber} (gamma : Path q q) : Path q.1 q.1 :=
  gamma.map continuous_subtype_val

def localLongitudePathOfFiber {q : Fiber} (gamma : Path q q)
    (hlocal : ∀ t : unitInterval,
      (gamma t).1 ∈ PeripheralCollar.LocalTubeSphere) :
    Path
      (PeripheralTube.longitude (localTorusOfFiber (gamma 0) (hlocal 0)))
      (PeripheralTube.longitude (localTorusOfFiber (gamma 0) (hlocal 0))) :=
  PeripheralBoundary.localLongitudePath (fiberSpherePath gamma) hlocal

theorem windingReal_localLongitudePath_eq_of_pointwise
    {q r : Milnor.CSphere} (gamma : Path q q) (delta : Path r r)
    (hgamma : ∀ t : unitInterval,
      gamma t ∈ PeripheralCollar.LocalTubeSphere)
    (hdelta : ∀ t : unitInterval,
      delta t ∈ PeripheralCollar.LocalTubeSphere)
    (heq : ∀ t : unitInterval, gamma t = delta t) :
    CircleWinding.windingReal
        (PeripheralBoundary.localLongitudePath gamma hgamma) =
      CircleWinding.windingReal
        (PeripheralBoundary.localLongitudePath delta hdelta) := by
  have htorusZero :
      PeripheralBoundary.torusRegionOfLocalSphere (gamma 0) (hgamma 0) =
        PeripheralBoundary.torusRegionOfLocalSphere (delta 0) (hdelta 0) := by
    apply Subtype.ext
    exact heq 0
  have hbase := congrArg PeripheralTube.longitude htorusZero
  have hpath : PeripheralBoundary.localLongitudePath gamma hgamma =
      (PeripheralBoundary.localLongitudePath delta hdelta).cast hbase hbase := by
    apply Path.ext
    funext t
    apply congrArg PeripheralTube.longitude
    apply Subtype.ext
    exact heq t
  calc
    CircleWinding.windingReal
        (PeripheralBoundary.localLongitudePath gamma hgamma) =
        CircleWinding.windingReal
          ((PeripheralBoundary.localLongitudePath delta hdelta).cast
            hbase hbase) :=
      congrArg CircleWinding.windingReal hpath
    _ = CircleWinding.windingReal
        (PeripheralBoundary.localLongitudePath delta hdelta) :=
      CircleMapAlgebra.windingReal_cast _ _

theorem collarLongitudePath_eq_localLongitudePathOfFiber {q : Fiber}
    (gamma : Path q q)
    (hlocal : ∀ t : unitInterval,
      (gamma t).1 ∈ PeripheralCollar.LocalTubeSphere) :
    (collarPathOfLocalFiber gamma hlocal).map
        PeripheralBoundary.collarLongitudeMap.continuous =
      localLongitudePathOfFiber gamma hlocal := by
  apply Path.ext
  rfl

def imageFiberMap (S : NegativeSymmetry) : C(Fiber, Fiber) :=
  RadialPageObstruction.fiberMapAt
    (PeripheralBridge.complementHomeomorph S) 0

def imageFiberPath (S : NegativeSymmetry) (s : PeripheralBoundary.PositiveLevel) :
    Path (imageFiberMap S (PeripheralBoundary.boundaryFiberBase s))
      (imageFiberMap S (PeripheralBoundary.boundaryFiberBase s)) :=
  (PeripheralBoundary.boundaryFiberPath s).map (imageFiberMap S).continuous

def imageHeight (S : NegativeSymmetry) (q : Fiber) : ℝ :=
  (RadialPageObstruction.onProductMap
    (PeripheralBridge.complementHomeomorph S) (q, 0)).2

def imageRotation (S : NegativeSymmetry) (q : Fiber) : ℝ :=
  -imageHeight S q / 6

theorem imageRotation_continuous (S : NegativeSymmetry) :
    Continuous (imageRotation S) := by
  unfold imageRotation imageHeight
  have hpair : Continuous (fun q : Fiber => (q, (0 : ℝ))) :=
    continuous_id.prodMk continuous_const
  have honProduct : Continuous (fun q : Fiber =>
      RadialPageObstruction.onProductMap
        (PeripheralBridge.complementHomeomorph S) (q, 0)) :=
    (RadialPageObstruction.onProductMap
      (PeripheralBridge.complementHomeomorph S)).continuous.comp hpair
  exact (continuous_snd.comp honProduct).neg.div_const 6

theorem imageFiberMap_val (S : NegativeSymmetry) (q : Fiber) :
    (imageFiberMap S q).1 =
      Milnor.weightedRotate (imageRotation S q)
        (CompactifiedSymmetry.sphereHomeomorph S q.1) := by
  apply Subtype.ext
  apply Prod.ext <;>
    simp [imageFiberMap, imageRotation, imageHeight,
      RadialPageObstruction.fiberMapAt,
      RadialPageObstruction.onProductMap,
      RadialCyclicCover.toFiber, RadialCyclicCover.fromFiber,
      HomeomorphismDegree.coverAction,
      PeripheralBridge.complementHomeomorph,
      RadialPhase.rotateComplement, Milnor.weightedRotate,
      Milnor.rotate_zero] <;> rfl

theorem sourceFiberPath_local (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ t : unitInterval,
      PeripheralBoundary.boundarySpherePath s.1 t ∈
        PeripheralCollar.LocalTubeSphere) (t : unitInterval) :
    ((PeripheralBoundary.boundaryFiberPath s) t).1 ∈
      PeripheralCollar.LocalTubeSphere :=
  hsource t

theorem imageFiberPath_local (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (himage : ∀ t : unitInterval,
      CompactifiedSymmetry.sphereHomeomorph S
          (PeripheralBoundary.boundarySpherePath s.1 t) ∈
        PeripheralCollar.LocalTubeSphere) (t : unitInterval) :
    (imageFiberPath S s t).1 ∈ PeripheralCollar.LocalTubeSphere := by
  let q := PeripheralBoundary.boundaryFiberPoint s t
  let rawTorus := PeripheralBoundary.torusRegionOfLocalSphere
    (CompactifiedSymmetry.sphereHomeomorph S q.1) (himage t)
  refine ⟨PeripheralBoundary.weightedRotateTorus (imageRotation S q) rawTorus,
    PeripheralBoundary.weightedRotateTorus_mem_localTubeSet
      (imageRotation S q)
      (PeripheralBoundary.torusRegionOfLocalSphere_mem
        (CompactifiedSymmetry.sphereHomeomorph S q.1) (himage t)), ?_⟩
  change
    (PeripheralBoundary.weightedRotateTorus (imageRotation S q) rawTorus).1 =
      (imageFiberMap S q).1
  rw [PeripheralBoundary.weightedRotateTorus_val, imageFiberMap_val]
  exact congrArg (Milnor.weightedRotate (imageRotation S q))
    (PeripheralBoundary.torusRegionOfLocalSphere_val
      (CompactifiedSymmetry.sphereHomeomorph S q.1) (himage t))

def sourceLocalLongitudePath (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ t : unitInterval,
      PeripheralBoundary.boundarySpherePath s.1 t ∈
        PeripheralCollar.LocalTubeSphere) :=
  localLongitudePathOfFiber (PeripheralBoundary.boundaryFiberPath s)
    (sourceFiberPath_local s hsource)

def rawImageSpherePath (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel) :
    Path
      (CompactifiedSymmetry.sphereHomeomorph S
        (PeripheralBoundary.boundaryFiberBase s).1)
      (CompactifiedSymmetry.sphereHomeomorph S
        (PeripheralBoundary.boundaryFiberBase s).1) :=
  (fiberSpherePath (PeripheralBoundary.boundaryFiberPath s)).map
    (CompactifiedSymmetry.sphereHomeomorph S).continuous

def rawImageLocalLongitudePath (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (himage : ∀ t : unitInterval,
      CompactifiedSymmetry.sphereHomeomorph S
          (PeripheralBoundary.boundarySpherePath s.1 t) ∈
        PeripheralCollar.LocalTubeSphere) :=
  PeripheralBoundary.localLongitudePath (rawImageSpherePath S s) himage

def imageLocalLongitudePath (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (himage : ∀ t : unitInterval,
      CompactifiedSymmetry.sphereHomeomorph S
          (PeripheralBoundary.boundarySpherePath s.1 t) ∈
        PeripheralCollar.LocalTubeSphere) :=
  localLongitudePathOfFiber (imageFiberPath S s)
    (imageFiberPath_local S s himage)

def imageRotationCircleMap (S : NegativeSymmetry) : C(Fiber, Circle) :=
  ⟨fun q => Circle.exp (imageRotation S q),
    Circle.exp.continuous.comp (imageRotation_continuous S)⟩

def imageRotationCirclePath (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel) :
    Path
      (imageRotationCircleMap S (PeripheralBoundary.boundaryFiberBase s))
      (imageRotationCircleMap S (PeripheralBoundary.boundaryFiberBase s)) :=
  (PeripheralBoundary.boundaryFiberPath s).map
    (imageRotationCircleMap S).continuous

theorem imageRotationCirclePath_winding_zero (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel) :
    CircleWinding.windingReal (imageRotationCirclePath S s) = 0 := by
  exact CoreMapAlgebra.windingReal_eq_zero_of_lift
    (imageRotationCircleMap S)
    ⟨imageRotation S, imageRotation_continuous S⟩ (fun _ => rfl)
    (PeripheralBoundary.boundaryFiberPath s)

theorem imageLongitude_point (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (himage : ∀ t : unitInterval,
      CompactifiedSymmetry.sphereHomeomorph S
          (PeripheralBoundary.boundarySpherePath s.1 t) ∈
        PeripheralCollar.LocalTubeSphere) (t : unitInterval) :
    imageLocalLongitudePath S s himage t =
      imageRotationCirclePath S s t *
        rawImageLocalLongitudePath S s himage t := by
  let q := PeripheralBoundary.boundaryFiberPoint s t
  let rawTorus := PeripheralBoundary.torusRegionOfLocalSphere
    (CompactifiedSymmetry.sphereHomeomorph S q.1) (himage t)
  have htorus : localTorusOfFiber (imageFiberMap S q)
      (imageFiberPath_local S s himage t) =
        PeripheralBoundary.weightedRotateTorus (imageRotation S q) rawTorus := by
    apply Subtype.ext
    change (imageFiberMap S q).1 =
      (PeripheralBoundary.weightedRotateTorus (imageRotation S q) rawTorus).1
    rw [imageFiberMap_val, PeripheralBoundary.weightedRotateTorus_val]
    exact congrArg (Milnor.weightedRotate (imageRotation S q))
      (PeripheralBoundary.torusRegionOfLocalSphere_val
        (CompactifiedSymmetry.sphereHomeomorph S q.1) (himage t)).symm
  change PeripheralTube.longitude
      (localTorusOfFiber (imageFiberMap S q)
        (imageFiberPath_local S s himage t)) =
    Circle.exp (imageRotation S q) * PeripheralTube.longitude rawTorus
  rw [htorus, PeripheralBoundary.longitude_weightedRotateTorus]

theorem imageLocalLongitudePath_winding (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (himage : ∀ t : unitInterval,
      CompactifiedSymmetry.sphereHomeomorph S
          (PeripheralBoundary.boundarySpherePath s.1 t) ∈
        PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal (imageLocalLongitudePath S s himage) =
      CircleWinding.windingReal (rawImageLocalLongitudePath S s himage) := by
  have hbase := imageLongitude_point S s himage 0
  have hpath : imageLocalLongitudePath S s himage =
      (CircleMapAlgebra.loopMul (imageRotationCirclePath S s)
        (rawImageLocalLongitudePath S s himage)).cast hbase hbase := by
    apply Path.ext
    funext t
    exact imageLongitude_point S s himage t
  calc
    CircleWinding.windingReal (imageLocalLongitudePath S s himage) =
        CircleWinding.windingReal
          ((CircleMapAlgebra.loopMul (imageRotationCirclePath S s)
            (rawImageLocalLongitudePath S s himage)).cast hbase hbase) :=
      congrArg CircleWinding.windingReal hpath
    _ = CircleWinding.windingReal
        (CircleMapAlgebra.loopMul (imageRotationCirclePath S s)
          (rawImageLocalLongitudePath S s himage)) :=
      CircleMapAlgebra.windingReal_cast _ _
    _ = CircleWinding.windingReal (imageRotationCirclePath S s) +
        CircleWinding.windingReal (rawImageLocalLongitudePath S s himage) :=
      CircleMapAlgebra.windingReal_loopMul _ _
    _ = CircleWinding.windingReal
        (rawImageLocalLongitudePath S s himage) := by
      rw [imageRotationCirclePath_winding_zero, zero_add]

theorem ambientLocalLongitude_winding_eq (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal
        (sourceLocalLongitudePath s (hsource s.1 le_rfl)) =
      CircleWinding.windingReal
        (rawImageLocalLongitudePath S s (himage s.1 le_rfl)) := by
  let sourceFamilyPath := PeripheralBoundary.sphereFamilyPath
    (PeripheralBoundary.sourceBoundaryFamily s)
    (PeripheralBoundary.sourceBoundaryFamily_continuous s)
    (PeripheralBoundary.sourceBoundaryFamily_loop s) 1
  let imageFamilyPath := PeripheralBoundary.sphereFamilyPath
    (PeripheralBoundary.imageBoundaryFamily S s)
    (PeripheralBoundary.imageBoundaryFamily_continuous S s)
    (PeripheralBoundary.imageBoundaryFamily_loop S s) 1
  let sourceFamilyLocal : ∀ t : unitInterval,
      sourceFamilyPath t ∈ PeripheralCollar.LocalTubeSphere :=
    fun t => hsource (PeripheralBoundary.lowerLevel s 1)
      (PeripheralBoundary.lowerLevel_le s 1) t
  let imageFamilyLocal : ∀ t : unitInterval,
      imageFamilyPath t ∈ PeripheralCollar.LocalTubeSphere :=
    fun t => himage (PeripheralBoundary.lowerLevel s 1)
      (PeripheralBoundary.lowerLevel_le s 1) t
  let sourceDirectPath := fiberSpherePath
    (PeripheralBoundary.boundaryFiberPath s)
  let imageDirectPath := rawImageSpherePath S s
  have hsourcePoint : ∀ t : unitInterval,
      sourceFamilyPath t = sourceDirectPath t := by
    intro t
    change PeripheralBoundary.boundarySpherePath
        (PeripheralBoundary.lowerLevel s 1) t =
      PeripheralBoundary.boundarySpherePath s.1 t
    rw [PeripheralBoundary.lowerLevel_one]
  have himagePoint : ∀ t : unitInterval,
      imageFamilyPath t = imageDirectPath t := by
    intro t
    change CompactifiedSymmetry.sphereHomeomorph S
        (PeripheralBoundary.boundarySpherePath
          (PeripheralBoundary.lowerLevel s 1) t) =
      CompactifiedSymmetry.sphereHomeomorph S
        (PeripheralBoundary.boundarySpherePath s.1 t)
    rw [PeripheralBoundary.lowerLevel_one]
  have hsourceWind := windingReal_localLongitudePath_eq_of_pointwise
    sourceFamilyPath sourceDirectPath sourceFamilyLocal
    (sourceFiberPath_local s (hsource s.1 le_rfl)) hsourcePoint
  have himageWind := windingReal_localLongitudePath_eq_of_pointwise
    imageFamilyPath imageDirectPath imageFamilyLocal
    (himage s.1 le_rfl) himagePoint
  have hambient := PeripheralBoundary.ambientLongitude_winding_eq
    S s hsource himage
  change CircleWinding.windingReal
      (PeripheralBoundary.localLongitudePath sourceDirectPath
        (sourceFiberPath_local s (hsource s.1 le_rfl))) =
    CircleWinding.windingReal
      (PeripheralBoundary.localLongitudePath imageDirectPath
        (himage s.1 le_rfl))
  calc
    _ = CircleWinding.windingReal
        (PeripheralBoundary.localLongitudePath sourceFamilyPath
          sourceFamilyLocal) := hsourceWind.symm
    _ = CircleWinding.windingReal
        (PeripheralBoundary.localLongitudePath imageFamilyPath
          imageFamilyLocal) := hambient
    _ = _ := himageWind

def sourceCollarPath (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ t : unitInterval,
      PeripheralBoundary.boundarySpherePath s.1 t ∈
        PeripheralCollar.LocalTubeSphere) :=
  collarPathOfLocalFiber (PeripheralBoundary.boundaryFiberPath s)
    (sourceFiberPath_local s hsource)

def imageCollarPath (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (himage : ∀ t : unitInterval,
      CompactifiedSymmetry.sphereHomeomorph S
          (PeripheralBoundary.boundarySpherePath s.1 t) ∈
        PeripheralCollar.LocalTubeSphere) :=
  collarPathOfLocalFiber (imageFiberPath S s)
    (imageFiberPath_local S s himage)

theorem collarLongitude_winding_eq (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    CircleWinding.windingReal
        ((sourceCollarPath s (hsource s.1 le_rfl)).map
          PeripheralBoundary.collarLongitudeMap.continuous) =
      CircleWinding.windingReal
        ((imageCollarPath S s (himage s.1 le_rfl)).map
          PeripheralBoundary.collarLongitudeMap.continuous) := by
  calc
    CircleWinding.windingReal
        ((sourceCollarPath s (hsource s.1 le_rfl)).map
          PeripheralBoundary.collarLongitudeMap.continuous) =
        CircleWinding.windingReal
          (sourceLocalLongitudePath s (hsource s.1 le_rfl)) := by
      apply congrArg CircleWinding.windingReal
      apply Path.ext
      rfl
    _ =
        CircleWinding.windingReal
          (rawImageLocalLongitudePath S s (himage s.1 le_rfl)) :=
      ambientLocalLongitude_winding_eq S s hsource himage
    _ = CircleWinding.windingReal
        (imageLocalLongitudePath S s (himage s.1 le_rfl)) :=
      (imageLocalLongitudePath_winding S s (himage s.1 le_rfl)).symm
    _ = CircleWinding.windingReal
        ((imageCollarPath S s (himage s.1 le_rfl)).map
          PeripheralBoundary.collarLongitudeMap.continuous) := by
      apply congrArg CircleWinding.windingReal
      apply Path.ext
      rfl

theorem homotopy_trans_loop
    {Y : Type*} [TopologicalSpace Y]
    {f g h : C(unitInterval, Y)} (F : f.Homotopy g) (G : g.Homotopy h)
    (hF : ∀ a : unitInterval, F (a, 1) = F (a, 0))
    (hG : ∀ a : unitInterval, G (a, 1) = G (a, 0))
    (a : unitInterval) :
    F.trans G (a, 1) = F.trans G (a, 0) := by
  rw [ContinuousMap.Homotopy.trans_apply,
    ContinuousMap.Homotopy.trans_apply]
  split_ifs <;> first | exact hF _ | exact hG _

theorem homotopy_symm_loop
    {Y : Type*} [TopologicalSpace Y]
    {f g : C(unitInterval, Y)} (F : f.Homotopy g)
    (hF : ∀ a : unitInterval, F (a, 1) = F (a, 0))
    (a : unitInterval) :
    F.symm (a, 1) = F.symm (a, 0) := by
  exact hF (unitInterval.symm a)

def collarBoundaryCoreHomotopy (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    ((PeripheralBoundary.boundaryFiberPath s).map
        FiberAction.fiberToCore.continuous : C(unitInterval, Core)).Homotopy
      ((imageFiberPath S s).map
        FiberAction.fiberToCore.continuous) := by
  let sourcePath := sourceCollarPath s (hsource s.1 le_rfl)
  let targetPath := imageCollarPath S s (himage s.1 le_rfl)
  let H := PeripheralBoundary.collarCoreLoopHomotopy sourcePath targetPath
  refine H.cast ?_ ?_
  · ext t
    exact congrArg FiberAction.fiberToCore
      (collarFiber_collarParameterOfLocalFiber
        ((PeripheralBoundary.boundaryFiberPath s) t)
        (sourceFiberPath_local s (hsource s.1 le_rfl) t))
  · ext t
    exact congrArg FiberAction.fiberToCore
      (collarFiber_collarParameterOfLocalFiber
        (imageFiberPath S s t)
        (imageFiberPath_local S s (himage s.1 le_rfl) t))

theorem collarBoundaryCoreHomotopy_loop (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere)
    (a : unitInterval) :
    collarBoundaryCoreHomotopy S s hsource himage (a, 1) =
      collarBoundaryCoreHomotopy S s hsource himage (a, 0) := by
  exact PeripheralBoundary.collarCoreLoopHomotopy_loop
    (sourceCollarPath s (hsource s.1 le_rfl))
    (imageCollarPath S s (himage s.1 le_rfl))
    (collarLongitude_winding_eq S s hsource himage) a

theorem evenPath_one_val (k : Fin 6) (t : unitInterval) :
    (PeripheralBridge.evenPath k 1 t).1 =
      PeripheralBoundary.evenSpherePath k 1 t := by
  change PeripheralBridge.evenSphere k (PeripheralBridge.positiveLevel 1) t =
    PeripheralBridge.evenSphere k 1 t
  rw [PeripheralBridge.positiveLevel_one]

theorem oddPath_one_val (k : Fin 6) (t : unitInterval) :
    (PeripheralBridge.oddPath k 1 t).1 =
      PeripheralBoundary.oddSpherePath k 1 t := by
  change PeripheralBridge.oddSphere k (PeripheralBridge.positiveLevel 1) t =
    PeripheralBridge.oddSphere k 1 t
  rw [PeripheralBridge.positiveLevel_one]

theorem pairPath_one_val (k : Fin 6) (t : unitInterval) :
    (PeripheralBridge.pairPath k 1 t).1 =
      PeripheralBoundary.pairSpherePath k 1 t := by
  simp only [PeripheralBridge.pairPath, PeripheralBoundary.pairSpherePath,
    Path.trans_apply]
  split_ifs
  · exact evenPath_one_val k _
  · exact oddPath_one_val k _

theorem boundaryPath_one_val (t : unitInterval) :
    (PeripheralBridge.boundaryPath 1 t).1 =
      PeripheralBoundary.boundarySpherePath 1 t := by
  simp only [PeripheralBridge.boundaryPath,
    PeripheralBoundary.boundarySpherePath, Path.trans_apply]
  split_ifs <;> first
  | exact pairPath_one_val 0 _
  | exact pairPath_one_val 1 _
  | exact pairPath_one_val 2 _
  | exact pairPath_one_val 3 _
  | exact pairPath_one_val 4 _
  | exact pairPath_one_val 5 _

def boundaryCoreOneBridgeHomotopy :
    (((PeripheralBoundary.boundaryFiberPath
        PeripheralBoundary.onePositiveLevel).map
          FiberAction.fiberToCore.continuous) : C(unitInterval, Core)).Homotopy
      PeripheralBridge.coreBoundaryWord := by
  refine PeripheralBridge.fiberToCoreBoundaryPathOneHomotopy.toHomotopy.cast ?_ rfl
  ext t
  apply congrArg FiberAction.fiberToCore
  apply Subtype.ext
  exact boundaryPath_one_val t

theorem boundaryCoreOneBridgeHomotopy_loop (a : unitInterval) :
    boundaryCoreOneBridgeHomotopy (a, 1) =
      boundaryCoreOneBridgeHomotopy (a, 0) := by
  change PeripheralBridge.fiberToCoreBoundaryPathOneHomotopy (a, 1) =
    PeripheralBridge.fiberToCoreBoundaryPathOneHomotopy (a, 0)
  exact
    (PeripheralBridge.fiberToCoreBoundaryPathOneHomotopy.target a).trans
      (PeripheralBridge.fiberToCoreBoundaryPathOneHomotopy.source a).symm

noncomputable def coreBoundaryWordStandardPathHomotopy :
    PeripheralBridge.coreBoundaryWord.Homotopy
      PeripheralBridge.standardCoreBoundary :=
  PeripheralBridge.coreBoundaryWord_homotopic_standard.some

noncomputable def coreBoundaryWordStandardHomotopy :
    (PeripheralBridge.coreBoundaryWord : C(unitInterval, Core)).Homotopy
      PeripheralBridge.standardCoreBoundary :=
  coreBoundaryWordStandardPathHomotopy.toHomotopy

theorem coreBoundaryWordStandardHomotopy_loop (a : unitInterval) :
    coreBoundaryWordStandardHomotopy (a, 1) =
      coreBoundaryWordStandardHomotopy (a, 0) := by
  exact (coreBoundaryWordStandardPathHomotopy.target a).trans
    (coreBoundaryWordStandardPathHomotopy.source a).symm

def sourceStandardHomotopy (s : PeripheralBoundary.PositiveLevel) :
    (((PeripheralBoundary.boundaryFiberPath s).map
        FiberAction.fiberToCore.continuous) : C(unitInterval, Core)).Homotopy
      PeripheralBridge.standardCoreBoundary :=
  (PeripheralBoundary.boundaryCoreLevelHomotopy s).trans
    (boundaryCoreOneBridgeHomotopy.trans coreBoundaryWordStandardHomotopy)

theorem sourceStandardHomotopy_loop
    (s : PeripheralBoundary.PositiveLevel) (a : unitInterval) :
    sourceStandardHomotopy s (a, 1) =
      sourceStandardHomotopy s (a, 0) := by
  apply homotopy_trans_loop
  · exact PeripheralBoundary.boundaryCoreLevelHomotopy_loop s
  · exact fun b => homotopy_trans_loop boundaryCoreOneBridgeHomotopy
      coreBoundaryWordStandardHomotopy boundaryCoreOneBridgeHomotopy_loop
      coreBoundaryWordStandardHomotopy_loop b

def sourceCoreLoop (s : PeripheralBoundary.PositiveLevel) : C(unitInterval, Core) :=
  (PeripheralBoundary.boundaryFiberPath s).map
    FiberAction.fiberToCore.continuous

def imageCoreLoop (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel) : C(unitInterval, Core) :=
  (imageFiberPath S s).map FiberAction.fiberToCore.continuous

def standardBoundaryLoop : C(unitInterval, Core) :=
  PeripheralBridge.standardCoreBoundary

def inducedCoreMap (S : NegativeSymmetry) : C(Core, Core) :=
  PeripheralBridge.inducedCoreMap S

def mappedSourceStandardHomotopy (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel) :
    ((inducedCoreMap S).comp standardBoundaryLoop).Homotopy
      ((inducedCoreMap S).comp (sourceCoreLoop s)) :=
  ((ContinuousMap.Homotopy.refl (inducedCoreMap S)).comp
    (sourceStandardHomotopy s)).symm

theorem mappedSourceStandardHomotopy_loop (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel) (a : unitInterval) :
    mappedSourceStandardHomotopy S s (a, 1) =
      mappedSourceStandardHomotopy S s (a, 0) := by
  exact congrArg (inducedCoreMap S)
    (homotopy_symm_loop (sourceStandardHomotopy s)
      (sourceStandardHomotopy_loop s) a)

def deformationCoreHomotopy (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel) :
    ((inducedCoreMap S).comp (sourceCoreLoop s)).Homotopy
      (imageCoreLoop S s) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × unitInterval =>
        FiberAction.fiberToCore
          (imageFiberMap S
            (FiberAction.fiberCoreHomotopy.symm
              (p.1, PeripheralBoundary.boundaryFiberPath s p.2))), by
      have hinput : Continuous (fun p : unitInterval × unitInterval =>
          (p.1, PeripheralBoundary.boundaryFiberPath s p.2)) :=
        continuous_fst.prodMk
          ((PeripheralBoundary.boundaryFiberPath s).continuous.comp continuous_snd)
      exact FiberAction.fiberToCore.continuous.comp
        ((imageFiberMap S).continuous.comp
          (FiberAction.fiberCoreHomotopy.symm.continuous.comp hinput))⟩
    (by
      intro t
      change FiberAction.fiberToCore
          (imageFiberMap S
            (FiberAction.fiberCoreHomotopy.symm
              (0, PeripheralBoundary.boundaryFiberPath s t))) =
        inducedCoreMap S
          (FiberAction.fiberToCore
            (PeripheralBoundary.boundaryFiberPath s t))
      have hzero := (FiberAction.fiberCoreHomotopy.symm).map_zero_left
        (PeripheralBoundary.boundaryFiberPath s t)
      calc
        FiberAction.fiberToCore
            (imageFiberMap S
              (FiberAction.fiberCoreHomotopy.symm
                (0, PeripheralBoundary.boundaryFiberPath s t))) =
            FiberAction.fiberToCore
              (imageFiberMap S
                (FiberAction.coreToFiber
                  (FiberAction.fiberToCore
                    (PeripheralBoundary.boundaryFiberPath s t)))) :=
          congrArg (fun q => FiberAction.fiberToCore (imageFiberMap S q)) hzero
        _ = inducedCoreMap S
            (FiberAction.fiberToCore
              (PeripheralBoundary.boundaryFiberPath s t)) := rfl)
    (by
      intro t
      change FiberAction.fiberToCore
          (imageFiberMap S
            (FiberAction.fiberCoreHomotopy.symm
              (1, PeripheralBoundary.boundaryFiberPath s t))) =
        FiberAction.fiberToCore (imageFiberPath S s t)
      have hone := (FiberAction.fiberCoreHomotopy.symm).map_one_left
        (PeripheralBoundary.boundaryFiberPath s t)
      calc
        FiberAction.fiberToCore
            (imageFiberMap S
              (FiberAction.fiberCoreHomotopy.symm
                (1, PeripheralBoundary.boundaryFiberPath s t))) =
            FiberAction.fiberToCore
              (imageFiberMap S (PeripheralBoundary.boundaryFiberPath s t)) :=
          congrArg (fun q => FiberAction.fiberToCore (imageFiberMap S q)) hone
        _ = FiberAction.fiberToCore (imageFiberPath S s t) := rfl)

theorem deformationCoreHomotopy_loop (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel) (a : unitInterval) :
    deformationCoreHomotopy S s (a, 1) =
      deformationCoreHomotopy S s (a, 0) := by
  have hendpoint : PeripheralBoundary.boundaryFiberPath s 1 =
      PeripheralBoundary.boundaryFiberPath s 0 :=
    (PeripheralBoundary.boundaryFiberPath s).target.trans
      (PeripheralBoundary.boundaryFiberPath s).source.symm
  exact congrArg (fun q => FiberAction.fiberToCore
    (imageFiberMap S (FiberAction.fiberCoreHomotopy.symm (a, q)))) hendpoint

def standardBoundaryPreservationHomotopy (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    ((inducedCoreMap S).comp standardBoundaryLoop).Homotopy
      standardBoundaryLoop :=
  (mappedSourceStandardHomotopy S s).trans
    ((deformationCoreHomotopy S s).trans
      ((collarBoundaryCoreHomotopy S s hsource himage).symm.trans
        (sourceStandardHomotopy s)))

theorem standardBoundaryPreservationHomotopy_loop (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere)
    (a : unitInterval) :
    standardBoundaryPreservationHomotopy S s hsource himage (a, 1) =
      standardBoundaryPreservationHomotopy S s hsource himage (a, 0) := by
  apply homotopy_trans_loop
  · exact mappedSourceStandardHomotopy_loop S s
  · exact fun b => homotopy_trans_loop (deformationCoreHomotopy S s)
      ((collarBoundaryCoreHomotopy S s hsource himage).symm.trans
        (sourceStandardHomotopy s))
      (deformationCoreHomotopy_loop S s)
      (fun c => homotopy_trans_loop
        (collarBoundaryCoreHomotopy S s hsource himage).symm
        (sourceStandardHomotopy s)
        (fun d => homotopy_symm_loop
          (collarBoundaryCoreHomotopy S s hsource himage)
          (collarBoundaryCoreHomotopy_loop S s hsource himage) d)
        (sourceStandardHomotopy_loop s) c) b

def mappedBoundaryCommutator (S : NegativeSymmetry) :
    Path ((inducedCoreMap S) (CoreCycles.aVertex 0))
      ((inducedCoreMap S) (CoreCycles.aVertex 0)) :=
  CoreBoundary.commutator
    (CoreBoundary.mappedFirstCycle (inducedCoreMap S))
    (CoreBoundary.mappedSecondCycle (inducedCoreMap S)).symm

def standardBoundaryCommutator :
    Path (CoreCycles.aVertex 0) (CoreCycles.aVertex 0) :=
  CoreBoundary.commutator CoreCycles.firstCycle CoreCycles.secondCycle.symm

theorem mappedStandardBoundary_eq_commutator (S : NegativeSymmetry) :
    (inducedCoreMap S).comp standardBoundaryLoop =
      (mappedBoundaryCommutator S : C(unitInterval, Core)) := by
  ext t
  simp [inducedCoreMap, standardBoundaryLoop, mappedBoundaryCommutator,
    PeripheralBridge.standardCoreBoundary,
    CoreBoundary.mappedFirstCycle, CoreBoundary.mappedSecondCycle,
    CoreBoundary.commutator, Path.trans_apply]
  split_ifs <;> rfl

theorem standardBoundary_eq_commutator :
    standardBoundaryLoop =
      (standardBoundaryCommutator : C(unitInterval, Core)) := by
  ext t
  rfl

def commutatorPreservationHomotopy (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    (mappedBoundaryCommutator S : C(unitInterval, Core)).Homotopy
      standardBoundaryCommutator :=
  (standardBoundaryPreservationHomotopy S s hsource himage).cast
    (mappedStandardBoundary_eq_commutator S)
    standardBoundary_eq_commutator

theorem commutatorPreservationHomotopy_loop (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere)
    (a : unitInterval) :
    commutatorPreservationHomotopy S s hsource himage (a, 1) =
      commutatorPreservationHomotopy S s hsource himage (a, 0) :=
  standardBoundaryPreservationHomotopy_loop S s hsource himage a

theorem firstIndex_symm {q : Core} (gamma : Path q q) :
    CoreBoundary.firstIndex gamma.symm = -CoreBoundary.firstIndex gamma := by
  apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
  have hpath : CoreBoundary.firstCoordinateLoop gamma.symm =
      (CoreBoundary.firstCoordinateLoop gamma).symm := by
    apply Path.ext
    rfl
  rw [hpath, CircleWinding.windingReal_symm,
    CoreBoundary.firstIndex_spec]
  push_cast
  ring

theorem secondIndex_symm {q : Core} (gamma : Path q q) :
    CoreBoundary.secondIndex gamma.symm = -CoreBoundary.secondIndex gamma := by
  apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
  have hpath : CoreBoundary.secondCoordinateLoop gamma.symm =
      (CoreBoundary.secondCoordinateLoop gamma).symm := by
    apply Path.ext
    rfl
  rw [hpath, CircleWinding.windingReal_symm,
    CoreBoundary.secondIndex_spec]
  push_cast
  ring

theorem commutatorIndex_symm_right {q : Core}
    (alpha beta : Path q q) :
    CoreBoundary.commutatorIndex alpha beta.symm =
      -CoreBoundary.commutatorIndex alpha beta := by
  rw [CoreBoundary.commutatorIndex_formula,
    CoreBoundary.commutatorIndex_formula,
    firstIndex_symm, secondIndex_symm]
  push_cast
  ring

theorem preservesBoundary (S : NegativeSymmetry)
    (s : PeripheralBoundary.PositiveLevel)
    (hsource : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        PeripheralBoundary.boundarySpherePath a t ∈
          PeripheralCollar.LocalTubeSphere)
    (himage : ∀ a : unitInterval, (a : ℝ) ≤ (s.1 : ℝ) →
      ∀ t : unitInterval,
        CompactifiedSymmetry.sphereHomeomorph S
            (PeripheralBoundary.boundarySpherePath a t) ∈
          PeripheralCollar.LocalTubeSphere) :
    CoreBoundary.PreservesBoundary (inducedCoreMap S) := by
  have hnegative :
      CoreBoundary.commutatorIndex
          (CoreBoundary.mappedFirstCycle (inducedCoreMap S))
          (CoreBoundary.mappedSecondCycle (inducedCoreMap S)).symm =
        CoreBoundary.commutatorIndex CoreCycles.firstCycle
          CoreCycles.secondCycle.symm :=
    CoreBoundary.commutatorIndex_eq_of_commutator_freeHomotopy
      (commutatorPreservationHomotopy S s hsource himage)
      (commutatorPreservationHomotopy_loop S s hsource himage)
  rw [commutatorIndex_symm_right, commutatorIndex_symm_right] at hnegative
  unfold CoreBoundary.PreservesBoundary
  linarith

theorem false_of_negativeSymmetry (S : NegativeSymmetry) : False := by
  obtain ⟨s, hsource, himage⟩ :=
    PeripheralBoundary.exists_smallBoundaryLevel S
  apply PeripheralBridge.false_of_preservesBoundary S
  exact preservesBoundary S s hsource himage

theorem no_negativeSymmetry : ¬Nonempty NegativeSymmetry := by
  rintro ⟨S⟩
  exact false_of_negativeSymmetry S

end

end Submission.PeripheralConclusion
