import Submission.CoreMapAlgebra
import Submission.Monodromy

open scoped unitInterval

namespace Submission.CoreAction

noncomputable section

def coordinate (i : Fin 2) : C(RadialCore.Core, Circle) :=
  ![CoreCoordinates.firstCoordinate, CoreCoordinates.secondCoordinate] i

def cycle (j : Fin 2) :
    Path (CoreCycles.aVertex 0) (CoreCycles.aVertex 0) :=
  ![CoreCycles.firstCycle, CoreCycles.secondCycle] j

def action (f : C(RadialCore.Core, RadialCore.Core)) :
    Matrix (Fin 2) (Fin 2) ℤ :=
  fun i j => CoreMapAlgebra.windingInt
    ((cycle j).map ((coordinate i).comp f).continuous)

theorem windingReal_action (f : C(RadialCore.Core, RadialCore.Core))
    (i j : Fin 2) :
    CircleWinding.windingReal
        ((cycle j).map ((coordinate i).comp f).continuous) =
      action f i j * (2 * Real.pi) :=
  CoreMapAlgebra.windingReal_eq_windingInt_mul_two_pi _

theorem action_apply_first (f : C(RadialCore.Core, RadialCore.Core))
    (i : Fin 2) :
    action f i 0 = CoreMapAlgebra.firstClass ((coordinate i).comp f) :=
  rfl

theorem action_apply_second (f : C(RadialCore.Core, RadialCore.Core))
    (i : Fin 2) :
    action f i 1 = CoreMapAlgebra.secondClass ((coordinate i).comp f) :=
  rfl

theorem action_comp (f g : C(RadialCore.Core, RadialCore.Core)) :
    action (g.comp f) = action g * action f := by
  ext i j
  have hclass := CoreMapAlgebra.windingReal_eq_classes
    ((coordinate i).comp g) ((cycle j).map f.continuous)
  have hleft :
      CircleWinding.windingReal
          ((cycle j).map ((coordinate i).comp (g.comp f)).continuous) =
      CircleWinding.windingReal
          (((cycle j).map f.continuous).map
            ((coordinate i).comp g).continuous) := by
    rfl
  rw [← hleft] at hclass
  rw [windingReal_action] at hclass
  have hfirst :
      CircleWinding.windingReal
          (((cycle j).map f.continuous).map
            CoreCoordinates.firstCoordinate.continuous) =
        action f 0 j * (2 * Real.pi) := by
    have hpath :
        ((cycle j).map f.continuous).map
            CoreCoordinates.firstCoordinate.continuous =
          (cycle j).map
            ((CoreCoordinates.firstCoordinate).comp f).continuous := by
      apply Path.ext
      rfl
    rw [hpath]
    exact windingReal_action f 0 j
  have hsecond :
      CircleWinding.windingReal
          (((cycle j).map f.continuous).map
            CoreCoordinates.secondCoordinate.continuous) =
        action f 1 j * (2 * Real.pi) := by
    have hpath :
        ((cycle j).map f.continuous).map
            CoreCoordinates.secondCoordinate.continuous =
          (cycle j).map
            ((CoreCoordinates.secondCoordinate).comp f).continuous := by
      apply Path.ext
      rfl
    rw [hpath]
    exact windingReal_action f 1 j
  rw [hfirst, hsecond] at hclass
  have hfirstClass : CoreMapAlgebra.firstClass ((coordinate i).comp g) =
      action g i 0 := by rfl
  have hsecondClass : CoreMapAlgebra.secondClass ((coordinate i).comp g) =
      action g i 1 := by rfl
  rw [hfirstClass, hsecondClass] at hclass
  have htwoPi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  have hcast : (action (g.comp f) i j : ℝ) =
      (action g i 0 * action f 0 j + action g i 1 * action f 1 j : ℤ) := by
    apply mul_right_cancel₀ htwoPi
    push_cast
    linarith
  rw [Matrix.mul_apply, Fin.sum_univ_two]
  exact_mod_cast hcast

theorem action_homotopy_invariant
    {f g : C(RadialCore.Core, RadialCore.Core)} (H : f.Homotopy g) :
    action f = action g := by
  ext i j
  let Hcoordinate : ((coordinate i).comp f).Homotopy
      ((coordinate i).comp g) :=
    (ContinuousMap.Homotopy.refl (coordinate i)).comp H
  let Hcycle :
      (((coordinate i).comp f).comp (cycle j).toContinuousMap).Homotopy
        (((coordinate i).comp g).comp (cycle j).toContinuousMap) :=
    Hcoordinate.compContinuousMap (cycle j).toContinuousMap
  have hwind :
      CircleWinding.windingReal
          ((cycle j).map ((coordinate i).comp f).continuous) =
        CircleWinding.windingReal
          ((cycle j).map ((coordinate i).comp g).continuous) := by
    apply CircleWinding.windingReal_eq_of_freeHomotopy Hcycle
    intro s
    change coordinate i (H (s, cycle j 1)) =
      coordinate i (H (s, cycle j 0))
    rw [(cycle j).target, (cycle j).source]
  apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
  rw [hwind, windingReal_action]

@[simp] theorem action_id :
    action (ContinuousMap.id RadialCore.Core) = 1 := by
  ext i j
  fin_cases i <;> fin_cases j
  · apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simp [coordinate, cycle]
  · apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simp [coordinate, cycle]
  · apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simp [coordinate, cycle]
  · apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simp [coordinate, cycle]

def monodromyMap : C(RadialCore.Core, RadialCore.Core) :=
  CoreCohomology.coreMonodromyMap

theorem windingReal_coordinate_firstImage (i : Fin 2) :
    CircleWinding.windingReal
        (CoreCohomology.firstImage.map (coordinate i).continuous) =
      ![(2 * Real.pi : ℝ), -(2 * Real.pi)] i := by
  fin_cases i
  · rw [CoreCohomology.winding_firstImage]
    simp [coordinate, CoreCoordinates.firstCoordinate,
      CoreCoordinates.edgeIncrement_coordinate]
  · rw [CoreCohomology.winding_firstImage]
    simp [coordinate, CoreCoordinates.secondCoordinate,
      CoreCoordinates.edgeIncrement_coordinate]

theorem windingReal_coordinate_secondImage (i : Fin 2) :
    CircleWinding.windingReal
        (CoreCohomology.secondImage.map (coordinate i).continuous) =
      ![(2 * Real.pi : ℝ), 0] i := by
  fin_cases i
  · rw [CoreCohomology.winding_secondImage]
    simp [coordinate, CoreCoordinates.firstCoordinate,
      CoreCoordinates.edgeIncrement_coordinate]
  · rw [CoreCohomology.winding_secondImage]
    simp [coordinate, CoreCoordinates.secondCoordinate,
      CoreCoordinates.edgeIncrement_coordinate]

theorem windingReal_coordinate_firstCycle_monodromy (i : Fin 2) :
    CircleWinding.windingReal
        (CoreCycles.firstCycle.map
          ((coordinate i).comp monodromyMap).continuous) =
      ![(2 * Real.pi : ℝ), -(2 * Real.pi)] i := by
  have hpath :
      CoreCycles.firstCycle.map ((coordinate i).comp monodromyMap).continuous =
        (CoreCycles.firstCycle.map monodromyMap.continuous).map
          (coordinate i).continuous := by
    apply Path.ext
    rfl
  have hmono := congrArg
    (fun p => p.map (coordinate i).continuous)
    CoreCohomology.firstCycle_monodromy
  calc
    CircleWinding.windingReal
        (CoreCycles.firstCycle.map
          ((coordinate i).comp monodromyMap).continuous) =
      CircleWinding.windingReal
        ((CoreCycles.firstCycle.map monodromyMap.continuous).map
          (coordinate i).continuous) :=
      congrArg CircleWinding.windingReal hpath
    _ = CircleWinding.windingReal
        (CoreCohomology.firstImage.map (coordinate i).continuous) :=
      congrArg CircleWinding.windingReal hmono
    _ = _ := windingReal_coordinate_firstImage i

theorem windingReal_coordinate_secondCycle_monodromy (i : Fin 2) :
    CircleWinding.windingReal
        (CoreCycles.secondCycle.map
          ((coordinate i).comp monodromyMap).continuous) =
      ![(2 * Real.pi : ℝ), 0] i := by
  have hpath :
      CoreCycles.secondCycle.map ((coordinate i).comp monodromyMap).continuous =
        (CoreCycles.secondCycle.map monodromyMap.continuous).map
          (coordinate i).continuous := by
    apply Path.ext
    rfl
  have hmono := congrArg
    (fun p => p.map (coordinate i).continuous)
    CoreCohomology.secondCycle_monodromy
  calc
    CircleWinding.windingReal
        (CoreCycles.secondCycle.map
          ((coordinate i).comp monodromyMap).continuous) =
      CircleWinding.windingReal
        ((CoreCycles.secondCycle.map monodromyMap.continuous).map
          (coordinate i).continuous) :=
      congrArg CircleWinding.windingReal hpath
    _ = CircleWinding.windingReal
        (CoreCohomology.secondImage.map (coordinate i).continuous) :=
      congrArg CircleWinding.windingReal hmono
    _ = _ := windingReal_coordinate_secondImage i

@[simp] theorem action_monodromy : action monodromyMap = Monodromy.trefoilInv := by
  ext i j
  fin_cases i <;> fin_cases j
  · change CoreMapAlgebra.windingInt
      (CoreCycles.firstCycle.map
        (CoreCoordinates.firstCoordinate.comp monodromyMap).continuous) = 1
    apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simpa [coordinate] using windingReal_coordinate_firstCycle_monodromy 0
  · change CoreMapAlgebra.windingInt
      (CoreCycles.secondCycle.map
        (CoreCoordinates.firstCoordinate.comp monodromyMap).continuous) = 1
    apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simpa [coordinate] using windingReal_coordinate_secondCycle_monodromy 0
  · change CoreMapAlgebra.windingInt
      (CoreCycles.firstCycle.map
        (CoreCoordinates.secondCoordinate.comp monodromyMap).continuous) = -1
    apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simpa [coordinate] using windingReal_coordinate_firstCycle_monodromy 1
  · change CoreMapAlgebra.windingInt
      (CoreCycles.secondCycle.map
        (CoreCoordinates.secondCoordinate.comp monodromyMap).continuous) = 0
    apply CoreMapAlgebra.windingInt_eq_of_windingReal_eq
    simpa [coordinate] using windingReal_coordinate_secondCycle_monodromy 1

end

end Submission.CoreAction
