import Submission.RadialPhase

open scoped unitInterval

namespace Submission.CoreCohomology

noncomputable section

def coreMonodromyMap : C(RadialCore.Core, RadialCore.Core) :=
  ⟨CoreMonodromy.coreMonodromy, CoreMonodromy.coreMonodromy_continuous⟩

def coreComplement : C(RadialCore.Core, RadialPhase.Complement) :=
  ⟨fun q => RadialPhase.fiberComplement (FiberLift.coreToFiber q),
    RadialPhase.fiberComplement_continuous.comp FiberLift.coreToFiber.continuous⟩

def coreMap (u : C(RadialPhase.Complement, Circle)) :
    C(RadialCore.Core, Circle) :=
  u.comp coreComplement

@[simp] theorem coreMonodromy_aVertex (i : Fin 2) :
    coreMonodromyMap (CoreCycles.aVertex i) =
      CoreCycles.aVertex (CoreMonodromy.flip i) := by
  unfold coreMonodromyMap CoreCycles.aVertex
  change CoreMonodromy.coreMonodromy (CoreEdges.edge i 0 0) =
    CoreEdges.edge (CoreMonodromy.flip i) 0 0
  rw [CoreMonodromy.coreMonodromy_edge, CoreCycles.edge_zero,
    CoreCycles.edge_zero]

@[simp] theorem coreMonodromy_bVertex (j : Fin 3) :
    coreMonodromyMap (CoreCycles.bVertex j) =
      CoreCycles.bVertex (CoreMonodromy.next j) := by
  unfold coreMonodromyMap CoreCycles.bVertex
  change CoreMonodromy.coreMonodromy (CoreEdges.edge 0 j 1) =
    CoreEdges.edge 0 (CoreMonodromy.next j) 1
  rw [CoreMonodromy.coreMonodromy_edge, CoreCycles.edge_one,
    CoreCycles.edge_one]

theorem edgePath_monodromy (i : Fin 2) (j : Fin 3) :
    (CoreCycles.edgePath i j).map coreMonodromyMap.continuous =
      (CoreCycles.edgePath (CoreMonodromy.flip i) (CoreMonodromy.next j)).cast
        (coreMonodromy_aVertex i) (coreMonodromy_bVertex j) := by
  apply Path.ext
  funext t
  exact CoreCycles.coreMonodromy_edgePath_apply i j t

theorem edgePath_symm_monodromy (i : Fin 2) (j : Fin 3) :
    (CoreCycles.edgePath i j).symm.map coreMonodromyMap.continuous =
      (CoreCycles.edgePath (CoreMonodromy.flip i) (CoreMonodromy.next j)).symm.cast
        (coreMonodromy_bVertex j) (coreMonodromy_aVertex i) := by
  rw [← Path.map_symm, edgePath_monodromy]
  apply Path.ext
  funext t
  rfl

def firstImageRaw : Path (CoreCycles.aVertex 1) (CoreCycles.aVertex 1) :=
  (CoreCycles.edgePath 1 1).trans
    ((CoreCycles.edgePath 0 1).symm.trans
      ((CoreCycles.edgePath 0 2).trans (CoreCycles.edgePath 1 2).symm))

def secondImageRaw : Path (CoreCycles.aVertex 1) (CoreCycles.aVertex 1) :=
  (CoreCycles.edgePath 1 1).trans
    ((CoreCycles.edgePath 0 1).symm.trans
      ((CoreCycles.edgePath 0 0).trans (CoreCycles.edgePath 1 0).symm))

def firstImage : Path (coreMonodromyMap (CoreCycles.aVertex 0))
    (coreMonodromyMap (CoreCycles.aVertex 0)) :=
  firstImageRaw.cast
    (by simp [CoreMonodromy.flip])
    (by simp [CoreMonodromy.flip])

def secondImage : Path (coreMonodromyMap (CoreCycles.aVertex 0))
    (coreMonodromyMap (CoreCycles.aVertex 0)) :=
  secondImageRaw.cast
    (by simp [CoreMonodromy.flip])
    (by simp [CoreMonodromy.flip])

theorem firstCycle_monodromy :
    CoreCycles.firstCycle.map coreMonodromyMap.continuous = firstImage := by
  apply Path.ext
  funext t
  simp only [CoreCycles.firstCycle, firstImage, firstImageRaw, Path.cast_coe,
    Path.map_coe, Function.comp_apply, Path.trans_apply]
  split_ifs <;> simp only [coreMonodromyMap, ContinuousMap.coe_mk] <;>
    exact CoreCycles.coreMonodromy_edgePath_apply _ _ _

theorem secondCycle_monodromy :
    CoreCycles.secondCycle.map coreMonodromyMap.continuous = secondImage := by
  apply Path.ext
  funext t
  simp only [CoreCycles.secondCycle, secondImage, secondImageRaw, Path.cast_coe,
    Path.map_coe, Function.comp_apply, Path.trans_apply]
  split_ifs <;> simp only [coreMonodromyMap, ContinuousMap.coe_mk] <;>
    exact CoreCycles.coreMonodromy_edgePath_apply _ _ _

theorem rotate_coreComplement (q : RadialCore.Core) :
    RadialPhase.rotateComplement (Real.pi / 3) (coreComplement q) =
      coreComplement (coreMonodromyMap q) :=
  rfl

def rotationHomotopy (u : C(RadialPhase.Complement, Circle))
    {q : RadialCore.Core} (gamma : Path q q) :
    (gamma.map (coreMap u).continuous : C(unitInterval, Circle)).Homotopy
      ((gamma.map coreMonodromyMap.continuous).map (coreMap u).continuous) :=
  ContinuousMap.Homotopy.mk
    ⟨fun p : unitInterval × unitInterval =>
        u (RadialPhase.rotateComplement
          ((p.1 : ℝ) * (Real.pi / 3)) (coreComplement (gamma p.2))), by
      have hparameter : Continuous (fun p : unitInterval × unitInterval =>
          (p.1 : ℝ) * (Real.pi / 3)) := by fun_prop
      have hcore : Continuous (fun p : unitInterval × unitInterval =>
          coreComplement (gamma p.2)) :=
        coreComplement.continuous.comp (gamma.continuous.comp continuous_snd)
      have hrotate := RadialPhase.rotateComplement_continuous.comp
        (hparameter.prodMk hcore)
      exact u.continuous.comp hrotate⟩
    (by
      intro t
      change u (RadialPhase.rotateComplement (0 * (Real.pi / 3))
        (coreComplement (gamma t))) = coreMap u (gamma t)
      rw [zero_mul, RadialPhase.rotateComplement_zero]
      rfl)
    (by
      intro t
      change u (RadialPhase.rotateComplement (1 * (Real.pi / 3))
        (coreComplement (gamma t))) =
        coreMap u (coreMonodromyMap (gamma t))
      rw [one_mul, rotate_coreComplement]
      rfl)

theorem winding_monodromy (u : C(RadialPhase.Complement, Circle))
    {q : RadialCore.Core} (gamma : Path q q) :
    CircleWinding.windingReal (gamma.map (coreMap u).continuous) =
      CircleWinding.windingReal
        ((gamma.map coreMonodromyMap.continuous).map (coreMap u).continuous) := by
  apply CircleWinding.windingReal_eq_of_freeHomotopy (rotationHomotopy u gamma)
  intro s
  change u (RadialPhase.rotateComplement ((s : ℝ) * (Real.pi / 3))
      (coreComplement (gamma 1))) =
    u (RadialPhase.rotateComplement ((s : ℝ) * (Real.pi / 3))
      (coreComplement (gamma 0)))
  rw [gamma.target, gamma.source]

theorem pathIncrement_edge_symm (g : C(RadialCore.Core, Circle))
    (i : Fin 2) (j : Fin 3) :
    CircleWinding.pathIncrement
      ((CoreCycles.edgePath i j).symm.map g.continuous) =
      -CoreLift.edgeIncrement g i j := by
  rw [← Path.map_symm, CircleWinding.pathIncrement_symm]
  rfl

theorem pathIncrement_edge (g : C(RadialCore.Core, Circle))
    (i : Fin 2) (j : Fin 3) :
    CircleWinding.pathIncrement
      ((CoreCycles.edgePath i j).map g.continuous) =
      CoreLift.edgeIncrement g i j :=
  rfl

theorem winding_firstCycle (g : C(RadialCore.Core, Circle)) :
    CircleWinding.windingReal (CoreCycles.firstCycle.map g.continuous) =
      CoreLift.edgeIncrement g 0 0 - CoreLift.edgeIncrement g 1 0 +
        CoreLift.edgeIncrement g 1 1 - CoreLift.edgeIncrement g 0 1 := by
  rw [← CircleWinding.pathIncrement_loop]
  simp only [CoreCycles.firstCycle, Path.map_trans,
    CircleWinding.pathIncrement_trans]
  rw [pathIncrement_edge, pathIncrement_edge_symm,
    pathIncrement_edge, pathIncrement_edge_symm]
  ring

theorem winding_secondCycle (g : C(RadialCore.Core, Circle)) :
    CircleWinding.windingReal (CoreCycles.secondCycle.map g.continuous) =
      CoreLift.edgeIncrement g 0 0 - CoreLift.edgeIncrement g 1 0 +
        CoreLift.edgeIncrement g 1 2 - CoreLift.edgeIncrement g 0 2 := by
  rw [← CircleWinding.pathIncrement_loop]
  simp only [CoreCycles.secondCycle, Path.map_trans,
    CircleWinding.pathIncrement_trans]
  rw [pathIncrement_edge, pathIncrement_edge_symm,
    pathIncrement_edge, pathIncrement_edge_symm]
  ring

theorem winding_firstImage (g : C(RadialCore.Core, Circle)) :
    CircleWinding.windingReal (firstImage.map g.continuous) =
      CoreLift.edgeIncrement g 1 1 - CoreLift.edgeIncrement g 0 1 +
        CoreLift.edgeIncrement g 0 2 - CoreLift.edgeIncrement g 1 2 := by
  rw [← CircleWinding.pathIncrement_loop]
  rw [firstImage, CircleWinding.pathIncrement_map_cast]
  simp only [firstImageRaw, Path.map_trans, CircleWinding.pathIncrement_trans]
  rw [pathIncrement_edge, pathIncrement_edge_symm,
    pathIncrement_edge, pathIncrement_edge_symm]
  ring

theorem winding_secondImage (g : C(RadialCore.Core, Circle)) :
    CircleWinding.windingReal (secondImage.map g.continuous) =
      CoreLift.edgeIncrement g 1 1 - CoreLift.edgeIncrement g 0 1 +
        CoreLift.edgeIncrement g 0 0 - CoreLift.edgeIncrement g 1 0 := by
  rw [← CircleWinding.pathIncrement_loop]
  rw [secondImage, CircleWinding.pathIncrement_map_cast]
  simp only [secondImageRaw, Path.map_trans, CircleWinding.pathIncrement_trans]
  rw [pathIncrement_edge, pathIncrement_edge_symm,
    pathIncrement_edge, pathIncrement_edge_symm]
  ring

theorem cycle_windings_zero (u : C(RadialPhase.Complement, Circle)) :
    CircleWinding.windingReal
        (CoreCycles.firstCycle.map (coreMap u).continuous) = 0 ∧
      CircleWinding.windingReal
        (CoreCycles.secondCycle.map (coreMap u).continuous) = 0 := by
  let g := coreMap u
  have hfirstInv := winding_monodromy u CoreCycles.firstCycle
  have hsecondInv := winding_monodromy u CoreCycles.secondCycle
  rw [firstCycle_monodromy] at hfirstInv
  rw [secondCycle_monodromy] at hsecondInv
  have hfirst := winding_firstCycle g
  have hsecond := winding_secondCycle g
  have hfirstImage := winding_firstImage g
  have hsecondImage := winding_secondImage g
  change CircleWinding.windingReal (CoreCycles.firstCycle.map g.continuous) =
      CircleWinding.windingReal (firstImage.map g.continuous) at hfirstInv
  change CircleWinding.windingReal (CoreCycles.secondCycle.map g.continuous) =
      CircleWinding.windingReal (secondImage.map g.continuous) at hsecondInv
  constructor <;> linarith

theorem fiberRestriction_lifts (u : C(RadialPhase.Complement, Circle)) :
    ∃ G : C(RadialMilnor.Fiber, ℝ), ∀ q,
      Circle.exp (G q) = u (RadialPhase.fiberComplement q) := by
  have hcycles := cycle_windings_zero u
  let g : C(RadialMilnor.Fiber, Circle) :=
    ⟨fun q => u (RadialPhase.fiberComplement q),
      u.continuous.comp RadialPhase.fiberComplement_continuous⟩
  have hmap : FiberLift.coreRestriction g = coreMap u := by
    ext q
    rfl
  apply FiberLift.exists_continuous_lift g
  · rw [hmap]
    exact hcycles.1
  · rw [hmap]
    exact hcycles.2

end

end Submission.CoreCohomology
