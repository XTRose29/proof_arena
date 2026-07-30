import Submission.CoreCohomology
import Submission.LocalWinding

open scoped unitInterval

namespace Submission.CoreCoordinates

noncomputable section

def edgeCoordinateValue (k : Fin 3) (x : CoreLift.EdgeDomain) : Circle :=
  if x.1.1 = 1 ∧ x.1.2 = k then LocalWinding.standardLoopPos x.2 else 1

theorem edgeCoordinateValue_continuous (k : Fin 3) :
    Continuous (edgeCoordinateValue k) := by
  rw [continuous_prod_of_discrete_left]
  intro ij
  by_cases h : ij.1 = 1 ∧ ij.2 = k
  · simpa [edgeCoordinateValue, h] using LocalWinding.standardLoopPos.continuous
  · simpa [edgeCoordinateValue, h] using
      (continuous_const : Continuous (fun _ : unitInterval => (1 : Circle)))

def edgeCoordinateMap (k : Fin 3) : C(CoreLift.EdgeDomain, Circle) :=
  ⟨edgeCoordinateValue k, edgeCoordinateValue_continuous k⟩

theorem edgeCoordinateMap_factors (k : Fin 3) :
    Function.FactorsThrough (edgeCoordinateMap k) CoreLift.edgeParam := by
  rintro ⟨⟨i, j⟩, u⟩ ⟨⟨i', j'⟩, u'⟩ h
  have hu : u = u' := CoreLift.edge_parameter_eq h
  subst u'
  by_cases hu0 : u = 0
  · subst u
    simp [edgeCoordinateMap, edgeCoordinateValue, LocalWinding.standardLoopPos]
  by_cases hu1 : u = 1
  · subst u
    simp [edgeCoordinateMap, edgeCoordinateValue, LocalWinding.standardLoopPos]
  · have huVal0 : (u : ℝ) ≠ 0 := fun hval => hu0 (Subtype.ext hval)
    have huVal1 : (u : ℝ) ≠ 1 := fun hval => hu1 (Subtype.ext hval)
    have huPos : 0 < (u : ℝ) := lt_of_le_of_ne u.2.1 (Ne.symm huVal0)
    have huLt : (u : ℝ) < 1 := lt_of_le_of_ne u.2.2 huVal1
    have hi : i = i' := CoreLift.edge_z_index_eq huLt h
    have hj : j = j' := CoreLift.edge_w_index_eq huPos h
    subst i'
    subst j'
    rfl

def coordinate (k : Fin 3) : C(RadialCore.Core, Circle) :=
  CoreLift.edgeParam_isQuotientMap.lift (edgeCoordinateMap k)
    (edgeCoordinateMap_factors k)

theorem coordinate_edge (k : Fin 3) (i : Fin 2) (j : Fin 3)
    (u : unitInterval) :
    coordinate k (CoreEdges.edge i j u) =
      if i = 1 ∧ j = k then LocalWinding.standardLoopPos u else 1 := by
  have hcomp := CoreLift.edgeParam_isQuotientMap.lift_comp
    (edgeCoordinateMap k) (edgeCoordinateMap_factors k)
  exact DFunLike.congr_fun hcomp (((i, j), u) : CoreLift.EdgeDomain)

@[simp] theorem coordinate_aVertex (k : Fin 3) (i : Fin 2) :
    coordinate k (CoreCycles.aVertex i) = 1 := by
  change coordinate k (CoreEdges.edge i 0 0) = 1
  rw [coordinate_edge]
  simp [LocalWinding.standardLoopPos]

@[simp] theorem coordinate_bVertex (k : Fin 3) (j : Fin 3) :
    coordinate k (CoreCycles.bVertex j) = 1 := by
  change coordinate k (CoreEdges.edge 0 j 1) = 1
  rw [coordinate_edge]
  simp

theorem mappedEdge_coordinate_selected (k : Fin 3) :
    CoreLift.mappedEdge (coordinate k) 1 k =
      LocalWinding.standardLoopPos.cast
        (coordinate_aVertex k 1) (coordinate_bVertex k k) := by
  apply Path.ext
  funext u
  change coordinate k (CoreEdges.edge 1 k u) = LocalWinding.standardLoopPos u
  rw [coordinate_edge]
  simp

theorem mappedEdge_coordinate_unselected (k : Fin 3) (i : Fin 2) (j : Fin 3)
    (h : ¬(i = 1 ∧ j = k)) :
    CoreLift.mappedEdge (coordinate k) i j =
      (Path.refl 1).cast (coordinate_aVertex k i) (coordinate_bVertex k j) := by
  apply Path.ext
  funext u
  change coordinate k (CoreEdges.edge i j u) = (1 : Circle)
  rw [coordinate_edge]
  simp [h]

theorem edgeIncrement_coordinate (k : Fin 3) (i : Fin 2) (j : Fin 3) :
    CoreLift.edgeIncrement (coordinate k) i j =
      if i = 1 ∧ j = k then 2 * Real.pi else 0 := by
  by_cases h : i = 1 ∧ j = k
  · rcases h with ⟨rfl, rfl⟩
    simp [CoreLift.edgeIncrement, mappedEdge_coordinate_selected,
      CircleWinding.pathIncrement_loop,
      LocalWinding.windingReal_standardLoop_pos]
  · rw [CoreLift.edgeIncrement, mappedEdge_coordinate_unselected k i j h]
    simp [h]

def firstCoordinate : C(RadialCore.Core, Circle) := coordinate 1

def secondCoordinate : C(RadialCore.Core, Circle) := coordinate 2

@[simp] theorem firstCoordinate_firstCycle :
    CircleWinding.windingReal
      (CoreCycles.firstCycle.map firstCoordinate.continuous) = 2 * Real.pi := by
  rw [CoreCohomology.winding_firstCycle]
  simp [firstCoordinate, edgeIncrement_coordinate]

@[simp] theorem firstCoordinate_secondCycle :
    CircleWinding.windingReal
      (CoreCycles.secondCycle.map firstCoordinate.continuous) = 0 := by
  rw [CoreCohomology.winding_secondCycle]
  simp [firstCoordinate, edgeIncrement_coordinate]

@[simp] theorem secondCoordinate_firstCycle :
    CircleWinding.windingReal
      (CoreCycles.firstCycle.map secondCoordinate.continuous) = 0 := by
  rw [CoreCohomology.winding_firstCycle]
  simp [secondCoordinate, edgeIncrement_coordinate]

@[simp] theorem secondCoordinate_secondCycle :
    CircleWinding.windingReal
      (CoreCycles.secondCycle.map secondCoordinate.continuous) = 2 * Real.pi := by
  rw [CoreCohomology.winding_secondCycle]
  simp [secondCoordinate, edgeIncrement_coordinate]

end

end Submission.CoreCoordinates
