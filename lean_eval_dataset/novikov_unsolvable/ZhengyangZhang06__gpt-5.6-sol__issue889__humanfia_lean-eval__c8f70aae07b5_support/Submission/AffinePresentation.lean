import Submission.AffinePermutations
import Submission.SubgroupReduction
import Mathlib.GroupTheory.Subgroup.Centralizer

namespace Submission.AffinePresentation

open Submission.AffineGraph
open Submission.AffinePermutations
open Submission.Helpers
open Submission.SubgroupReduction

noncomputable section

abbrev LayerControl := Bool × Control

inductive ActionGenerator
  | global (location : LayerControl) (axis : Fin 4)
  | chart (edge : Edge) (side : Bool) (axis : Fin 2)
  | move (move : Move)
  deriving DecidableEq, Fintype

inductive Generator
  | lamp (location : LayerControl)
  | action (generator : ActionGenerator)
  deriving DecidableEq, Fintype

abbrev GeneratorCount := Fintype.card Generator

def generatorEquiv : Generator ≃ Fin GeneratorCount :=
  Fintype.equivFin Generator

def generatorIndex (generator : Generator) : Fin GeneratorCount :=
  generatorEquiv generator

def freeGenerator (generator : Generator) :
    FreeGroup (Fin GeneratorCount) :=
  FreeGroup.of (generatorIndex generator)

def coordinateBasis (axis : Fin 4) : Coord :=
  Pi.single axis 1

def globalFree (location : LayerControl) (coordinate : Coord) :
    FreeGroup (Fin GeneratorCount) :=
  freeGenerator (.action (.global location 0)) ^ coordinate 0 *
    freeGenerator (.action (.global location 1)) ^ coordinate 1 *
      freeGenerator (.action (.global location 2)) ^ coordinate 2 *
        freeGenerator (.action (.global location 3)) ^ coordinate 3

def lampFree (vertex : LayeredVertex) :
    FreeGroup (Fin GeneratorCount) :=
  let translation := globalFree (vertex.1, vertex.2.1) vertex.2.2
  translation * freeGenerator (.lamp (vertex.1, vertex.2.1)) *
    translation⁻¹

def chartFree (edge : Edge) (side : Bool) (axis : Fin 2) :
    FreeGroup (Fin GeneratorCount) :=
  freeGenerator (.action (.chart edge side axis))

def moveFree (move : Move) : FreeGroup (Fin GeneratorCount) :=
  freeGenerator (.action (.move move))

def conjugate {G : Type*} [Group G] (actor value : G) : G :=
  actor * value * actor⁻¹

def equationRelator
    (left right : FreeGroup (Fin GeneratorCount)) :
    FreeGroup (Fin GeneratorCount) :=
  left * right⁻¹

def commuteRelator
    (left right : FreeGroup (Fin GeneratorCount)) :
    FreeGroup (Fin GeneratorCount) :=
  equationRelator (left * right) (right * left)

inductive RelationTag
  | globalCommute
      (leftLocation rightLocation : LayerControl)
      (leftAxis rightAxis : Fin 4)
  | chartCommute (edge : Edge) (side : Bool)
      (leftAxis rightAxis : Fin 2)
  | chartGlobalCommute (edge : Edge) (side : Bool)
      (chartAxis directionAxis : Fin 2)
  | chartLamp (edge : Edge) (side : Bool) (axis : Fin 2)
  | flipLamp (control : Control)
  | flipGlobal (control : Control) (axis : Fin 4)
  | edgeLamp (edge : Edge)
  | edgeShift (edge : Edge) (axis : Fin 2)
  deriving DecidableEq, Fintype

def endpointBase (edge : Edge) (side : Bool) : LayeredVertex :=
  endpointEmbedding edge side 0

def endpointGlobalFree (edge : Edge) (side : Bool) (axis : Fin 2) :
    FreeGroup (Fin GeneratorCount) :=
  globalFree (side, endpointControl edge side)
    (endpointDirection edge side axis)

def relationElement : RelationTag → FreeGroup (Fin GeneratorCount)
  | .globalCommute leftLocation rightLocation leftAxis rightAxis =>
      commuteRelator
        (freeGenerator (.action (.global leftLocation leftAxis)))
        (freeGenerator (.action (.global rightLocation rightAxis)))
  | .chartCommute edge side leftAxis rightAxis =>
      commuteRelator
        (chartFree edge side leftAxis)
        (chartFree edge side rightAxis)
  | .chartGlobalCommute edge side chartAxis directionAxis =>
      commuteRelator
        (chartFree edge side chartAxis)
        (endpointGlobalFree edge side directionAxis)
  | .chartLamp edge side axis =>
      equationRelator
        (conjugate (chartFree edge side axis)
          (lampFree (endpointBase edge side)))
        (conjugate (endpointGlobalFree edge side axis)
          (lampFree (endpointBase edge side)))
  | .flipLamp control =>
      equationRelator
        (conjugate (moveFree .flip)
          (lampFree (false, control, 0)))
        (lampFree (true, control, 0))
  | .flipGlobal control axis =>
      equationRelator
        (conjugate (moveFree .flip)
          (freeGenerator (.action (.global (false, control) axis))))
        (freeGenerator (.action (.global (true, control) axis)))
  | .edgeLamp edge =>
      equationRelator
        (conjugate (moveFree (.edge edge))
          (lampFree (endpointBase edge false)))
        (lampFree (endpointBase edge true))
  | .edgeShift edge axis =>
      equationRelator
        (moveFree (.edge edge) * chartFree edge false axis)
        (chartFree edge true axis * moveFree (.edge edge))

def relators : Set (FreeGroup (Fin GeneratorCount)) :=
  Set.range relationElement

theorem relators_finite : relators.Finite :=
  Set.finite_range relationElement

private abbrev Presented :=
  PresentedGroup relators

def interpret (word : FreeGroup (Fin GeneratorCount)) : Presented :=
  PresentedGroup.mk relators word

def presentedGenerator (generator : Generator) : Presented :=
  PresentedGroup.of (generatorIndex generator)

private theorem interpret_equation_of_tag
    (tag : RelationTag)
    {left right : FreeGroup (Fin GeneratorCount)}
    (tagEqual : relationElement tag = equationRelator left right) :
    interpret left = interpret right := by
  apply PresentedGroup.mk_eq_mk_of_mul_inv_mem
  change equationRelator left right ∈ relators
  rw [← tagEqual]
  exact ⟨tag, rfl⟩

theorem global_generators_commute
    (leftLocation rightLocation : LayerControl)
    (leftAxis rightAxis : Fin 4) :
    Commute
      (presentedGenerator (.action (.global leftLocation leftAxis)))
      (presentedGenerator (.action (.global rightLocation rightAxis))) := by
  change
    interpret
        (freeGenerator (.action (.global leftLocation leftAxis)) *
          freeGenerator (.action (.global rightLocation rightAxis))) =
      interpret
        (freeGenerator (.action (.global rightLocation rightAxis)) *
          freeGenerator (.action (.global leftLocation leftAxis)))
  apply interpret_equation_of_tag
    (.globalCommute leftLocation rightLocation leftAxis rightAxis)
  rfl

theorem chart_generators_commute
    (edge : Edge) (side : Bool) (leftAxis rightAxis : Fin 2) :
    Commute
      (presentedGenerator (.action (.chart edge side leftAxis)))
      (presentedGenerator (.action (.chart edge side rightAxis))) := by
  change
    interpret (chartFree edge side leftAxis * chartFree edge side rightAxis) =
      interpret (chartFree edge side rightAxis * chartFree edge side leftAxis)
  apply interpret_equation_of_tag
    (.chartCommute edge side leftAxis rightAxis)
  rfl

theorem chart_global_generators_commute
    (edge : Edge) (side : Bool) (chartAxis directionAxis : Fin 2) :
    Commute
      (presentedGenerator (.action (.chart edge side chartAxis)))
      (interpret (endpointGlobalFree edge side directionAxis)) := by
  change
    interpret
        (chartFree edge side chartAxis *
          endpointGlobalFree edge side directionAxis) =
      interpret
        (endpointGlobalFree edge side directionAxis *
          chartFree edge side chartAxis)
  apply interpret_equation_of_tag
    (.chartGlobalCommute edge side chartAxis directionAxis)
  rfl

theorem chart_generator_lamp
    (edge : Edge) (side : Bool) (axis : Fin 2) :
    conjugate
        (presentedGenerator (.action (.chart edge side axis)))
        (interpret (lampFree (endpointBase edge side))) =
      conjugate
        (interpret (endpointGlobalFree edge side axis))
        (interpret (lampFree (endpointBase edge side))) := by
  change
    interpret
        (conjugate (chartFree edge side axis)
          (lampFree (endpointBase edge side))) =
      interpret
        (conjugate (endpointGlobalFree edge side axis)
          (lampFree (endpointBase edge side)))
  apply interpret_equation_of_tag (.chartLamp edge side axis)
  rfl

theorem flip_generator_lamp (control : Control) :
    conjugate
        (presentedGenerator (.action (.move .flip)))
        (interpret (lampFree (false, control, 0))) =
      interpret (lampFree (true, control, 0)) := by
  change
    interpret
        (conjugate (moveFree .flip)
          (lampFree (false, control, 0))) =
      interpret (lampFree (true, control, 0))
  apply interpret_equation_of_tag (.flipLamp control)
  rfl

theorem flip_generator_global (control : Control) (axis : Fin 4) :
    conjugate
        (presentedGenerator (.action (.move .flip)))
        (presentedGenerator (.action (.global (false, control) axis))) =
      presentedGenerator (.action (.global (true, control) axis)) := by
  change
    interpret
        (conjugate (moveFree .flip)
          (freeGenerator (.action (.global (false, control) axis)))) =
      interpret (freeGenerator (.action (.global (true, control) axis)))
  apply interpret_equation_of_tag (.flipGlobal control axis)
  rfl

theorem edge_generator_lamp (edge : Edge) :
    conjugate
        (presentedGenerator (.action (.move (.edge edge))))
        (interpret (lampFree (endpointBase edge false))) =
      interpret (lampFree (endpointBase edge true)) := by
  change
    interpret
        (conjugate (moveFree (.edge edge))
          (lampFree (endpointBase edge false))) =
      interpret (lampFree (endpointBase edge true))
  apply interpret_equation_of_tag (.edgeLamp edge)
  rfl

theorem edge_generator_shift (edge : Edge) (axis : Fin 2) :
    presentedGenerator (.action (.move (.edge edge))) *
        presentedGenerator (.action (.chart edge false axis)) =
      presentedGenerator (.action (.chart edge true axis)) *
        presentedGenerator (.action (.move (.edge edge))) := by
  change
    interpret (moveFree (.edge edge) * chartFree edge false axis) =
      interpret (chartFree edge true axis * moveFree (.edge edge))
  apply interpret_equation_of_tag (.edgeShift edge axis)
  rfl

def globalElement (location : LayerControl) (coordinate : Coord) : Presented :=
  interpret (globalFree location coordinate)

def globalComponent (location : LayerControl) (axis : Fin 4) : Presented :=
  presentedGenerator (.action (.global location axis))

private theorem globalElement_expand
    (location : LayerControl) (coordinate : Coord) :
    globalElement location coordinate =
      globalComponent location 0 ^ coordinate 0 *
        globalComponent location 1 ^ coordinate 1 *
          globalComponent location 2 ^ coordinate 2 *
            globalComponent location 3 ^ coordinate 3 := by
  rfl

theorem globalComponent_commutes_globalElement
    (leftLocation rightLocation : LayerControl)
    (axis : Fin 4) (coordinate : Coord) :
    Commute (globalComponent leftLocation axis)
      (globalElement rightLocation coordinate) := by
  rw [globalElement_expand]
  simpa [globalComponent, mul_assoc] using
    (((global_generators_commute leftLocation rightLocation axis 0).zpow_right _).mul_right
      ((global_generators_commute leftLocation rightLocation axis 1).zpow_right _)).mul_right
        (((global_generators_commute leftLocation rightLocation axis 2).zpow_right _).mul_right
          ((global_generators_commute leftLocation rightLocation axis 3).zpow_right _))

theorem globalElements_commute
    (leftLocation rightLocation : LayerControl)
    (leftCoordinate rightCoordinate : Coord) :
    Commute
      (globalElement leftLocation leftCoordinate)
      (globalElement rightLocation rightCoordinate) := by
  rw [globalElement_expand]
  simpa [globalComponent, mul_assoc] using
    (((globalComponent_commutes_globalElement leftLocation rightLocation 0
      rightCoordinate).zpow_left _).mul_left
        ((globalComponent_commutes_globalElement leftLocation rightLocation 1
          rightCoordinate).zpow_left _)).mul_left
      (((globalComponent_commutes_globalElement leftLocation rightLocation 2
        rightCoordinate).zpow_left _).mul_left
        ((globalComponent_commutes_globalElement leftLocation rightLocation 3
          rightCoordinate).zpow_left _))

def chartElement (edge : Edge) (side : Bool) (axis : Fin 2) : Presented :=
  presentedGenerator (.action (.chart edge side axis))

def directionElement (edge : Edge) (side : Bool) (axis : Fin 2) : Presented :=
  globalElement (side, endpointControl edge side)
    (endpointDirection edge side axis)

def endpointLamp (edge : Edge) (side : Bool) : Presented :=
  interpret (lampFree (endpointBase edge side))

theorem chartElements_commute
    (edge : Edge) (side : Bool) (leftAxis rightAxis : Fin 2) :
    Commute (chartElement edge side leftAxis)
      (chartElement edge side rightAxis) :=
  chart_generators_commute edge side leftAxis rightAxis

theorem directionElements_commute
    (edge : Edge) (side : Bool) (leftAxis rightAxis : Fin 2) :
    Commute (directionElement edge side leftAxis)
      (directionElement edge side rightAxis) :=
  globalElements_commute _ _ _ _

theorem chartElement_commutes_directionElement
    (edge : Edge) (side : Bool) (chartAxis directionAxis : Fin 2) :
    Commute (chartElement edge side chartAxis)
      (directionElement edge side directionAxis) :=
  chart_global_generators_commute edge side chartAxis directionAxis

private theorem quotient_commutes_of_conjugates
    {G : Type*} [Group G] {left right value : G}
    (equal : conjugate left value = conjugate right value) :
    Commute (right⁻¹ * left) value := by
  have equal' :
      left * value * left⁻¹ = right * value * right⁻¹ := by
    simpa [conjugate] using equal
  change (right⁻¹ * left) * value = value * (right⁻¹ * left)
  calc
    (right⁻¹ * left) * value =
        ((right⁻¹ * left) * value * (right⁻¹ * left)⁻¹) *
          (right⁻¹ * left) := by group
    _ = (right⁻¹ * (left * value * left⁻¹) * right) *
          (right⁻¹ * left) := by group
    _ = (right⁻¹ * (right * value * right⁻¹) * right) *
          (right⁻¹ * left) := by rw [equal']
    _ = value * (right⁻¹ * left) := by group

theorem chartQuotient_commutes_lamp
    (edge : Edge) (side : Bool) (axis : Fin 2) :
    Commute
      ((directionElement edge side axis)⁻¹ *
        chartElement edge side axis)
      (endpointLamp edge side) :=
  quotient_commutes_of_conjugates
    (chart_generator_lamp edge side axis)

def chartParameterElement
    (edge : Edge) (side : Bool) (parameter : Param) : Presented :=
  chartElement edge side 0 ^ parameter.1 *
    chartElement edge side 1 ^ parameter.2

def directionParameterElement
    (edge : Edge) (side : Bool) (parameter : Param) : Presented :=
  directionElement edge side 0 ^ parameter.1 *
    directionElement edge side 1 ^ parameter.2

def quotientParameterElement
    (edge : Edge) (side : Bool) (parameter : Param) : Presented :=
  ((directionElement edge side 0)⁻¹ *
      chartElement edge side 0) ^ parameter.1 *
    ((directionElement edge side 1)⁻¹ *
      chartElement edge side 1) ^ parameter.2

theorem quotientParameter_commutes_lamp
    (edge : Edge) (side : Bool) (parameter : Param) :
    Commute (quotientParameterElement edge side parameter)
      (endpointLamp edge side) :=
  ((chartQuotient_commutes_lamp edge side 0).zpow_left _).mul_left
    ((chartQuotient_commutes_lamp edge side 1).zpow_left _)

private theorem conjugate_mul_of_commute
    {G : Type*} [Group G] {left right value : G}
    (commutes : Commute right value) :
    conjugate (left * right) value = conjugate left value := by
  simp only [conjugate, mul_inv_rev]
  calc
    (left * right) * value * (right⁻¹ * left⁻¹) =
        left * (right * value * right⁻¹) * left⁻¹ := by group
    _ = left * value * left⁻¹ := by rw [commutes.mul_inv_cancel]

private theorem direction_commutes_quotient
    (edge : Edge) (side : Bool) (axis : Fin 2) :
    Commute
      (directionElement edge side axis)
      ((directionElement edge side axis)⁻¹ *
        chartElement edge side axis) :=
  ((Commute.refl (directionElement edge side axis)).inv_right).mul_right
    (chartElement_commutes_directionElement edge side axis axis).symm

private theorem regroup_of_commute
    {G : Type*} [Group G] {first second third fourth : G}
    (commutes : Commute second third) :
    (first * second) * (third * fourth) =
      (first * third) * (second * fourth) := by
  calc
    (first * second) * (third * fourth) =
        first * (second * third) * fourth := by group
    _ = first * (third * second) * fourth := by rw [commutes.eq]
    _ = (first * third) * (second * fourth) := by group

theorem chartParameter_factor
    (edge : Edge) (side : Bool) (parameter : Param) :
    chartParameterElement edge side parameter =
      directionParameterElement edge side parameter *
        quotientParameterElement edge side parameter := by
  have factor (axis : Fin 2) (power : ℤ) :
      chartElement edge side axis ^ power =
        directionElement edge side axis ^ power *
          ((directionElement edge side axis)⁻¹ *
            chartElement edge side axis) ^ power := by
    rw [← (direction_commutes_quotient edge side axis).mul_zpow]
    congr 1
    group
  rw [chartParameterElement, directionParameterElement,
    quotientParameterElement, factor, factor]
  have cross :
      Commute
        (((directionElement edge side 0)⁻¹ *
          chartElement edge side 0) ^ parameter.1)
        (directionElement edge side 1 ^ parameter.2) := by
    apply Commute.zpow_zpow
    exact
      ((directionElements_commute edge side 0 1).inv_left).mul_left
        (chartElement_commutes_directionElement edge side 0 1)
  exact regroup_of_commute cross

theorem chartParameter_lamp
    (edge : Edge) (side : Bool) (parameter : Param) :
    conjugate (chartParameterElement edge side parameter)
        (endpointLamp edge side) =
      conjugate (directionParameterElement edge side parameter)
        (endpointLamp edge side) := by
  rw [chartParameter_factor]
  exact conjugate_mul_of_commute
    (quotientParameter_commutes_lamp edge side parameter)

def globalGeneratorSet : Set Presented :=
  Set.range fun generator : LayerControl × Fin 4 =>
    globalComponent generator.1 generator.2

def globalSubgroup : Subgroup Presented :=
  Subgroup.closure globalGeneratorSet

private theorem globalGeneratorSet_commutes :
    ∀ left ∈ globalGeneratorSet, ∀ right ∈ globalGeneratorSet,
      left * right = right * left := by
  rintro left ⟨⟨leftLocation, leftAxis⟩, rfl⟩
    right ⟨⟨rightLocation, rightAxis⟩, rfl⟩
  exact (global_generators_commute
    leftLocation rightLocation leftAxis rightAxis).eq

noncomputable local instance globalSubgroup_isMulCommutative :
    IsMulCommutative globalSubgroup :=
  Subgroup.isMulCommutative_closure globalGeneratorSet_commutes

def globalComponentSubgroup
    (location : LayerControl) (axis : Fin 4) : globalSubgroup :=
  ⟨globalComponent location axis,
    Subgroup.subset_closure ⟨(location, axis), rfl⟩⟩

def globalElementSubgroup
    (location : LayerControl) (coordinate : Coord) : globalSubgroup :=
  globalComponentSubgroup location 0 ^ coordinate 0 *
    globalComponentSubgroup location 1 ^ coordinate 1 *
      globalComponentSubgroup location 2 ^ coordinate 2 *
        globalComponentSubgroup location 3 ^ coordinate 3

@[simp]
theorem globalElementSubgroup_value
    (location : LayerControl) (coordinate : Coord) :
    (globalElementSubgroup location coordinate : Presented) =
      globalElement location coordinate := rfl

open scoped IsMulCommutative in
def globalElementHom (location : LayerControl) :
    Multiplicative Coord →* globalSubgroup where
  toFun coordinate := globalElementSubgroup location coordinate.toAdd
  map_one' := by
    change globalElementSubgroup location 0 = 1
    simp [globalElementSubgroup]
  map_mul' left right := by
    change
      globalElementSubgroup location (left.toAdd + right.toAdd) =
        globalElementSubgroup location left.toAdd *
          globalElementSubgroup location right.toAdd
    simp only [globalElementSubgroup, Pi.add_apply, zpow_add]
    ac_rfl

theorem globalElement_add
    (location : LayerControl) (left right : Coord) :
    globalElement location (left + right) =
      globalElement location left * globalElement location right := by
  have mapped :=
    (globalElementHom location).map_mul
      (Multiplicative.ofAdd left) (Multiplicative.ofAdd right)
  exact congrArg Subtype.val mapped

theorem globalElement_zsmul
    (location : LayerControl) (coordinate : Coord) (power : ℤ) :
    globalElement location (power • coordinate) =
      globalElement location coordinate ^ power := by
  have mapped :=
    (globalElementHom location).map_zpow
      (Multiplicative.ofAdd coordinate) power
  exact congrArg Subtype.val mapped

def lampElement (vertex : LayeredVertex) : Presented :=
  interpret (lampFree vertex)

def originLamp (location : LayerControl) : Presented :=
  presentedGenerator (.lamp location)

theorem lampElement_expand (vertex : LayeredVertex) :
    lampElement vertex =
      conjugate
        (globalElement (vertex.1, vertex.2.1) vertex.2.2)
        (originLamp (vertex.1, vertex.2.1)) := by
  rfl

private theorem lampElement_zero (location : LayerControl) :
    lampElement (location.1, location.2, 0) = originLamp location := by
  have mapped := (globalElementHom location).map_one
  have globalZero : globalElement location 0 = 1 :=
    congrArg Subtype.val mapped
  rw [lampElement_expand, globalZero]
  simp [conjugate]

def endpointDisplacement
    (edge : Edge) (side : Bool) (parameter : Param) : Coord :=
  parameter.1 • endpointDirection edge side 0 +
    parameter.2 • endpointDirection edge side 1

theorem endpointCoordinate_eq_base_add_displacement
    (edge : Edge) (side : Bool) (parameter : Param) :
    endpointCoordinate edge side parameter =
      endpointCoordinate edge side 0 +
        endpointDisplacement edge side parameter := by
  have affine :=
    endpointCoordinate_affine edge side
      (parameter.1 • parameterBasis 0)
      (parameter.2 • parameterBasis 1)
  have parameterDecomposition :
      parameter =
        parameter.1 • parameterBasis 0 +
          parameter.2 • parameterBasis 1 := by
    ext <;> simp [parameterBasis]
  rw [← parameterDecomposition] at affine
  rw [affine, endpointDisplacement]
  simp only [endpointDirection]
  let linear : Param →+ Coord :=
    { toFun := fun current =>
        endpointCoordinate edge side current -
          endpointCoordinate edge side 0
      map_zero' := sub_self _
      map_add' := by
        intro left right
        rw [endpointCoordinate_affine]
        abel }
  -- The displacement from the affine base point is linear.
  have scale (axis : Fin 2) (power : ℤ) :
      endpointCoordinate edge side (power • parameterBasis axis) =
        endpointCoordinate edge side 0 +
          power • endpointDirection edge side axis := by
    have mapped := linear.map_zsmul power (parameterBasis axis)
    change
      endpointCoordinate edge side (power • parameterBasis axis) -
          endpointCoordinate edge side 0 =
        power •
          (endpointCoordinate edge side (parameterBasis axis) -
            endpointCoordinate edge side 0) at mapped
    rw [endpointDirection]
    calc
      endpointCoordinate edge side (power • parameterBasis axis) =
          (endpointCoordinate edge side (power • parameterBasis axis) -
              endpointCoordinate edge side 0) +
            endpointCoordinate edge side 0 := by abel
      _ = power •
            (endpointCoordinate edge side (parameterBasis axis) -
              endpointCoordinate edge side 0) +
            endpointCoordinate edge side 0 := by rw [mapped]
      _ = endpointCoordinate edge side 0 +
            power •
              (endpointCoordinate edge side (parameterBasis axis) -
                endpointCoordinate edge side 0) := by abel
  rw [scale, scale]
  abel

theorem directionParameter_eq_globalDisplacement
    (edge : Edge) (side : Bool) (parameter : Param) :
    directionParameterElement edge side parameter =
      globalElement (side, endpointControl edge side)
        (endpointDisplacement edge side parameter) := by
  rw [directionParameterElement, endpointDisplacement,
    globalElement_add, globalElement_zsmul, globalElement_zsmul]
  rfl

theorem directionParameter_lamp_base
    (edge : Edge) (side : Bool) (parameter : Param) :
    conjugate (directionParameterElement edge side parameter)
        (endpointLamp edge side) =
      lampElement (endpointEmbedding edge side parameter) := by
  rw [directionParameter_eq_globalDisplacement]
  rw [endpointLamp, endpointBase, ← lampElement]
  rw [lampElement_expand, lampElement_expand]
  simp only [endpointEmbedding_apply]
  rw [endpointCoordinate_eq_base_add_displacement edge side parameter]
  simp only [conjugate]
  rw [globalElement_add]
  have commute :=
    globalElements_commute
      (side, endpointControl edge side)
      (side, endpointControl edge side)
      (endpointDisplacement edge side parameter)
      (endpointCoordinate edge side 0)
  rw [← commute.eq]
  group

theorem chartParameter_lamp_at
    (edge : Edge) (side : Bool) (parameter : Param) :
    conjugate (chartParameterElement edge side parameter)
        (endpointLamp edge side) =
      lampElement (endpointEmbedding edge side parameter) :=
  (chartParameter_lamp edge side parameter).trans
    (directionParameter_lamp_base edge side parameter)

def semanticAction : ActionGenerator → Equiv.Perm SemanticPoint
  | .global location axis =>
      liftPerm (globalShift location.1 location.2 (coordinateBasis axis))
  | .chart edge side axis =>
      liftPerm (chartShift edge side (parameterBasis axis))
  | .move move =>
      liftPerm (movePerm move)

def semanticGenerator : Generator → Equiv.Perm SemanticPoint
  | .lamp location => lamp (location.1, location.2, 0)
  | .action generator => semanticAction generator

def freeToSemantic :
    FreeGroup (Fin GeneratorCount) →* Equiv.Perm SemanticPoint :=
  FreeGroup.lift (semanticGenerator ∘ generatorEquiv.symm)

@[simp]
theorem freeToSemantic_generator (generator : Generator) :
    freeToSemantic (freeGenerator generator) = semanticGenerator generator := by
  simp [freeToSemantic, freeGenerator, generatorIndex, Function.comp_def]

private theorem coordinate_decomposition (coordinate : Coord) :
    coordinate =
      coordinate 0 • coordinateBasis 0 +
        coordinate 1 • coordinateBasis 1 +
          coordinate 2 • coordinateBasis 2 +
            coordinate 3 • coordinateBasis 3 := by
  funext i
  fin_cases i <;> simp [coordinateBasis]

def globalActionHom (location : LayerControl) :
    Multiplicative Coord →* Equiv.Perm SemanticPoint :=
  liftPermHom.comp (rangeShiftHom (fiber location.1 location.2))

theorem freeToSemantic_globalFree
    (location : LayerControl) (coordinate : Coord) :
    freeToSemantic (globalFree location coordinate) =
      liftPerm (globalShift location.1 location.2 coordinate) := by
  have decomposition :
      Multiplicative.ofAdd coordinate =
        (Multiplicative.ofAdd (coordinateBasis 0)) ^ coordinate 0 *
          (Multiplicative.ofAdd (coordinateBasis 1)) ^ coordinate 1 *
            (Multiplicative.ofAdd (coordinateBasis 2)) ^ coordinate 2 *
              (Multiplicative.ofAdd (coordinateBasis 3)) ^ coordinate 3 := by
    apply Multiplicative.toAdd.injective
    exact coordinate_decomposition coordinate
  simp only [globalFree, map_mul, map_zpow, freeToSemantic_generator,
    semanticGenerator, semanticAction]
  change
    (globalActionHom location
        (Multiplicative.ofAdd (coordinateBasis 0))) ^ coordinate 0 *
      (globalActionHom location
          (Multiplicative.ofAdd (coordinateBasis 1))) ^ coordinate 1 *
        (globalActionHom location
            (Multiplicative.ofAdd (coordinateBasis 2))) ^ coordinate 2 *
          (globalActionHom location
            (Multiplicative.ofAdd (coordinateBasis 3))) ^ coordinate 3 =
      globalActionHom location (Multiplicative.ofAdd coordinate)
  rw [decomposition, map_mul, map_mul, map_mul, map_zpow, map_zpow,
    map_zpow, map_zpow]

theorem freeToSemantic_lampFree (vertex : LayeredVertex) :
    freeToSemantic (lampFree vertex) = lamp vertex := by
  rw [lampFree, map_mul, map_mul, map_inv, freeToSemantic_globalFree,
    freeToSemantic_generator]
  change
    liftPerm
        (globalShift vertex.1 vertex.2.1 vertex.2.2) *
      lamp (vertex.1, vertex.2.1, 0) *
        (liftPerm
          (globalShift vertex.1 vertex.2.1 vertex.2.2))⁻¹ =
      lamp vertex
  rw [liftPerm_mul_lamp]
  simp

@[simp]
theorem freeToSemantic_chartFree
    (edge : Edge) (side : Bool) (axis : Fin 2) :
    freeToSemantic (chartFree edge side axis) =
      liftPerm (chartShift edge side (parameterBasis axis)) :=
  freeToSemantic_generator _

@[simp]
theorem freeToSemantic_moveFree (move : Move) :
    freeToSemantic (moveFree move) = liftPerm (movePerm move) :=
  freeToSemantic_generator _

theorem freeToSemantic_endpointGlobalFree
    (edge : Edge) (side : Bool) (axis : Fin 2) :
    freeToSemantic (endpointGlobalFree edge side axis) =
      liftPerm
        (globalShift side (endpointControl edge side)
          (endpointDirection edge side axis)) :=
  freeToSemantic_globalFree _ _

private theorem map_equationRelator_eq_one
    {left right : FreeGroup (Fin GeneratorCount)}
    (equal : freeToSemantic left = freeToSemantic right) :
    freeToSemantic (equationRelator left right) = 1 := by
  simp [equationRelator, equal]

private theorem liftPerm_mul_equal
    {leftFirst leftSecond rightFirst rightSecond :
      Equiv.Perm LayeredVertex}
    (equal :
      leftFirst * leftSecond = rightFirst * rightSecond) :
    liftPerm leftFirst * liftPerm leftSecond =
      liftPerm rightFirst * liftPerm rightSecond := by
  calc
    liftPerm leftFirst * liftPerm leftSecond =
        liftPerm (leftFirst * leftSecond) :=
      (liftPermHom.map_mul _ _).symm
    _ = liftPerm (rightFirst * rightSecond) :=
      congrArg liftPerm equal
    _ = liftPerm rightFirst * liftPerm rightSecond :=
      liftPermHom.map_mul _ _

theorem relation_semantic_one (tag : RelationTag) :
    freeToSemantic (relationElement tag) = 1 := by
  cases tag with
  | globalCommute leftLocation rightLocation leftAxis rightAxis =>
      apply map_equationRelator_eq_one
      simp only [map_mul, freeToSemantic_generator]
      exact liftPerm_mul_equal <|
        (globalShift_commute leftLocation.1 rightLocation.1
          leftLocation.2 rightLocation.2
          (coordinateBasis leftAxis) (coordinateBasis rightAxis)).eq
  | chartCommute edge side leftAxis rightAxis =>
      apply map_equationRelator_eq_one
      simp only [map_mul, freeToSemantic_chartFree]
      exact liftPerm_mul_equal <|
        (chartShift_commute edge side
          (parameterBasis leftAxis) (parameterBasis rightAxis)).eq
  | chartGlobalCommute edge side chartAxis directionAxis =>
      apply map_equationRelator_eq_one
      simp only [map_mul, freeToSemantic_chartFree,
        freeToSemantic_endpointGlobalFree]
      exact liftPerm_mul_equal <|
        (chartShift_commute_global edge side
          (parameterBasis chartAxis) directionAxis).eq
  | chartLamp edge side axis =>
      apply map_equationRelator_eq_one
      simp only [conjugate, map_mul, map_inv,
        freeToSemantic_chartFree, freeToSemantic_endpointGlobalFree,
        freeToSemantic_lampFree]
      rw [liftPerm_mul_lamp, liftPerm_mul_lamp]
      simp only [mul_inv_cancel_right]
      congr 1
      rw [endpointBase, chartShift_apply, globalShift_endpoint]
  | flipLamp control =>
      apply map_equationRelator_eq_one
      simp only [conjugate, map_mul, map_inv,
        freeToSemantic_moveFree, movePerm, freeToSemantic_lampFree]
      rw [liftPerm_mul_lamp]
      simp
  | flipGlobal control axis =>
      apply map_equationRelator_eq_one
      simp only [conjugate, map_mul, map_inv, freeToSemantic_moveFree, movePerm,
        freeToSemantic_generator, semanticGenerator, semanticAction]
      have semanticRelation :=
        liftPerm_mul_equal
          (layerFlip_mul_globalShift control (coordinateBasis axis))
      rw [semanticRelation]
      group
  | edgeLamp edge =>
      apply map_equationRelator_eq_one
      simp only [conjugate, map_mul, map_inv,
        freeToSemantic_moveFree, movePerm, freeToSemantic_lampFree]
      rw [liftPerm_mul_lamp]
      simp only [mul_inv_cancel_right]
      congr 1
      exact edgeSwap_source edge 0
  | edgeShift edge axis =>
      apply map_equationRelator_eq_one
      simp only [map_mul,
        freeToSemantic_moveFree, movePerm, freeToSemantic_chartFree]
      exact liftPerm_mul_equal <|
        edgeSwap_mul_chartShift edge (parameterBasis axis)

theorem relations_hold
    (relator : FreeGroup (Fin GeneratorCount))
    (member : relator ∈ relators) :
    freeToSemantic relator = 1 := by
  obtain ⟨tag, rfl⟩ := member
  exact relation_semantic_one tag

def presentedToSemantic : Presented →* Equiv.Perm SemanticPoint :=
  PresentedGroup.toGroup relations_hold

theorem presentedToSemantic_mk
    (word : FreeGroup (Fin GeneratorCount)) :
    presentedToSemantic (PresentedGroup.mk relators word) =
      freeToSemantic word := rfl

/-! ## Semantic soundness of the move-and-marker subgroup -/

def acceptOrbit : Set LayeredVertex :=
  { vertex | AffinePermutations.Connected
      AffinePermutations.acceptedVertex vertex }

def protectedPoints : Set SemanticPoint :=
  {none} ∪ Option.some '' acceptOrbit

def preservesProtected : Subgroup (Equiv.Perm SemanticPoint) where
  carrier :=
    { permutation |
      ∀ point, point ∈ protectedPoints ↔
        permutation point ∈ protectedPoints }
  one_mem' := by simp
  mul_mem' := by
    intro left right leftPreserves rightPreserves point
    change point ∈ protectedPoints ↔ left (right point) ∈ protectedPoints
    exact (rightPreserves point).trans (leftPreserves (right point))
  inv_mem' := by
    intro permutation preserves point
    have atInverse := preserves (permutation⁻¹ point)
    simpa using atInverse.symm

private theorem move_connected_iff (move : Move) (vertex : LayeredVertex) :
    AffinePermutations.Connected
        AffinePermutations.acceptedVertex vertex ↔
      AffinePermutations.Connected
        AffinePermutations.acceptedVertex (movePerm move vertex) := by
  constructor
  · intro connected
    exact connected.tail ⟨move, rfl⟩
  · intro connected
    exact connected.tail
      ⟨move, movePerm_involutive move vertex⟩

theorem move_preservesProtected (move : Move) :
    liftPerm (movePerm move) ∈ preservesProtected := by
  intro point
  cases point with
  | none => simp [protectedPoints]
  | some vertex =>
      simp only [protectedPoints, Set.mem_union, Set.mem_singleton_iff,
        Option.some.injEq, Option.some_ne_none, false_or,
        Set.mem_image, acceptOrbit, liftPerm_some]
      constructor
      · rintro ⟨source, connected, rfl⟩
        exact
          ⟨movePerm move source,
            (move_connected_iff move source).mp connected, rfl⟩
      · rintro ⟨target, connected, targetEqual⟩
        refine ⟨movePerm move target, ?_, ?_⟩
        · exact (move_connected_iff move target).mp connected
        · have targetVertex :
              target = movePerm move vertex :=
            targetEqual
          subst target
          rw [movePerm_involutive move]

theorem acceptedLamp_preservesProtected :
    lamp AffinePermutations.acceptedVertex ∈ preservesProtected := by
  have selfConnected :
      AffinePermutations.Connected
        AffinePermutations.acceptedVertex
        AffinePermutations.acceptedVertex :=
    Relation.ReflTransGen.refl
  intro point
  cases point with
  | none =>
      simp [protectedPoints, acceptOrbit, selfConnected]
  | some vertex =>
      by_cases equal : vertex = AffinePermutations.acceptedVertex
      · subst vertex
        simp [protectedPoints, acceptOrbit, selfConnected]
      · have someUnequal :
          (some vertex : SemanticPoint) ≠
            some AffinePermutations.acceptedVertex := by
          simpa using equal
        rw [show lamp AffinePermutations.acceptedVertex (some vertex) =
          some vertex by
            exact Equiv.swap_apply_of_ne_of_ne
              (Option.some_ne_none _) someUnequal]

def semanticSubgroup : Subgroup (Equiv.Perm SemanticPoint) :=
  Subgroup.closure
    (Set.range (fun move : Move => liftPerm (movePerm move)) ∪
      {lamp AffinePermutations.acceptedVertex})

theorem semanticSubgroup_le_preserves :
    semanticSubgroup ≤ preservesProtected := by
  rw [semanticSubgroup, Subgroup.closure_le]
  rintro permutation (moveMember | lampMember)
  · obtain ⟨move, rfl⟩ := moveMember
    exact move_preservesProtected move
  · rw [Set.mem_singleton_iff] at lampMember
    subst permutation
    exact acceptedLamp_preservesProtected

theorem connected_of_lamp_mem_semanticSubgroup
    {vertex : LayeredVertex}
    (member : lamp vertex ∈ semanticSubgroup) :
    AffinePermutations.Connected vertex
      AffinePermutations.acceptedVertex := by
  have preserves :
      lamp vertex ∈ preservesProtected :=
    semanticSubgroup_le_preserves member
  have noneProtected : (none : SemanticPoint) ∈ protectedPoints := by
    simp [protectedPoints]
  have someProtected :
      (some vertex : SemanticPoint) ∈ protectedPoints := by
    exact (preserves none).mp noneProtected
  obtain ⟨source, connected, sourceEqual⟩ : ∃ source,
      source ∈ acceptOrbit ∧ some source = some vertex := by
    simpa [protectedPoints] using someProtected
  have sourceVertex : source = vertex := Option.some.inj sourceEqual
  subst source
  exact connected_symm connected

/-! ## Exact subgroup membership -/

def moveElement (move : Move) : Presented :=
  presentedGenerator (.action (.move move))

private theorem conjugate_eq_of_semiconj
    {G : Type*} [Group G] {actor left right : G}
    (semiconj : SemiconjBy actor left right) :
    conjugate actor left = right := by
  change actor * left = right * actor at semiconj
  apply mul_right_cancel (b := actor)
  simpa [conjugate, mul_assoc] using semiconj

private theorem semiconj_of_conjugate_eq
    {G : Type*} [Group G] {actor left right : G}
    (equal : conjugate actor left = right) :
    SemiconjBy actor left right := by
  have equal' : actor * left * actor⁻¹ = right := by
    simpa [conjugate] using equal
  change actor * left = right * actor
  calc
    actor * left = (actor * left * actor⁻¹) * actor := by group
    _ = right * actor := by rw [equal']

private theorem conjugate_inv_of_conjugate_eq
    {G : Type*} [Group G] {actor left right : G}
    (equal : conjugate actor left = right) :
    conjugate actor⁻¹ right = left := by
  rw [← equal]
  simp [conjugate]
  group

theorem edge_semiconj_chartParameter
    (edge : Edge) (parameter : Param) :
    SemiconjBy (moveElement (.edge edge))
      (chartParameterElement edge false parameter)
      (chartParameterElement edge true parameter) := by
  have first :
      SemiconjBy (moveElement (.edge edge))
        (chartElement edge false 0) (chartElement edge true 0) :=
    edge_generator_shift edge 0
  have second :
      SemiconjBy (moveElement (.edge edge))
        (chartElement edge false 1) (chartElement edge true 1) :=
    edge_generator_shift edge 1
  simpa [chartParameterElement] using
    (first.zpow_right parameter.1).mul_right
      (second.zpow_right parameter.2)

theorem edge_conjugates_source_lamp
    (edge : Edge) (parameter : Param) :
    conjugate (moveElement (.edge edge))
        (lampElement (endpointEmbedding edge false parameter)) =
      lampElement (endpointEmbedding edge true parameter) := by
  have chartSemiconj := edge_semiconj_chartParameter edge parameter
  have lampSemiconj :
      SemiconjBy (moveElement (.edge edge))
        (endpointLamp edge false) (endpointLamp edge true) := by
    exact semiconj_of_conjugate_eq (edge_generator_lamp edge)
  have transported :=
    (chartSemiconj.mul_right lampSemiconj).mul_right
      chartSemiconj.inv_right
  have conjugated := conjugate_eq_of_semiconj transported
  change
    conjugate (moveElement (.edge edge))
        (conjugate (chartParameterElement edge false parameter)
          (endpointLamp edge false)) =
      conjugate (chartParameterElement edge true parameter)
        (endpointLamp edge true) at conjugated
  rw [chartParameter_lamp_at, chartParameter_lamp_at] at conjugated
  exact conjugated

theorem flip_semiconj_globalElement
    (control : Control) (coordinate : Coord) :
    SemiconjBy (moveElement .flip)
      (globalElement (false, control) coordinate)
      (globalElement (true, control) coordinate) := by
  have component (axis : Fin 4) :
      SemiconjBy (moveElement .flip)
        (globalComponent (false, control) axis)
        (globalComponent (true, control) axis) := by
    exact semiconj_of_conjugate_eq
      (flip_generator_global control axis)
  simpa [globalElement_expand, mul_assoc] using
    (((component 0).zpow_right (coordinate 0)).mul_right
      ((component 1).zpow_right (coordinate 1))).mul_right <|
        ((component 2).zpow_right (coordinate 2)).mul_right
          ((component 3).zpow_right (coordinate 3))

theorem flip_conjugates_false_lamp
    (control : Control) (coordinate : Coord) :
    conjugate (moveElement .flip)
        (lampElement (false, control, coordinate)) =
      lampElement (true, control, coordinate) := by
  have globalSemiconj := flip_semiconj_globalElement control coordinate
  have lampSemiconj :
      SemiconjBy (moveElement .flip)
        (originLamp (false, control)) (originLamp (true, control)) := by
    apply semiconj_of_conjugate_eq
    rw [← lampElement_zero (false, control),
      ← lampElement_zero (true, control)]
    exact flip_generator_lamp control
  have transported :=
    (globalSemiconj.mul_right lampSemiconj).mul_right
      globalSemiconj.inv_right
  have conjugated := conjugate_eq_of_semiconj transported
  change
    conjugate (moveElement .flip)
        (conjugate (globalElement (false, control) coordinate)
          (originLamp (false, control))) =
      conjugate (globalElement (true, control) coordinate)
        (originLamp (true, control)) at conjugated
  rw [lampElement_expand, lampElement_expand]
  exact conjugated

def membershipGeneratorSet : Set Presented :=
  Set.range moveElement ∪ {lampElement AffinePermutations.acceptedVertex}

def membershipSubgroup : Subgroup Presented :=
  Subgroup.closure membershipGeneratorSet

private theorem moveElement_mem (move : Move) :
    moveElement move ∈ membershipSubgroup :=
  Subgroup.subset_closure (Or.inl ⟨move, rfl⟩)

private theorem adjacent_lamp_transport
    {left right : LayeredVertex}
    (adjacent : AffinePermutations.Adjacent left right) :
    ∃ actor ∈ membershipSubgroup,
      conjugate actor (lampElement left) = lampElement right := by
  obtain ⟨move, equal⟩ := adjacent
  cases move with
  | flip =>
      rcases left with ⟨layer, control, coordinate⟩
      cases layer with
      | false =>
          simp [movePerm] at equal
          subst right
          exact
            ⟨moveElement .flip, moveElement_mem .flip,
              flip_conjugates_false_lamp control coordinate⟩
      | true =>
          simp [movePerm] at equal
          subst right
          exact
            ⟨(moveElement .flip)⁻¹,
              membershipSubgroup.inv_mem (moveElement_mem .flip),
              conjugate_inv_of_conjugate_eq
                (flip_conjugates_false_lamp control coordinate)⟩
  | edge edge =>
      by_cases sourceMember :
          left ∈ Set.range (layeredSource edge)
      · obtain ⟨parameter, rfl⟩ := sourceMember
        rw [movePerm, layeredSource_apply, edgeSwap_source] at equal
        subst right
        exact
          ⟨moveElement (.edge edge), moveElement_mem (.edge edge),
            edge_conjugates_source_lamp edge parameter⟩
      · by_cases targetMember :
          left ∈ Set.range (layeredTarget edge)
        · obtain ⟨parameter, rfl⟩ := targetMember
          rw [movePerm, layeredTarget_apply, edgeSwap_target] at equal
          subst right
          exact
            ⟨(moveElement (.edge edge))⁻¹,
              membershipSubgroup.inv_mem (moveElement_mem (.edge edge)),
              conjugate_inv_of_conjugate_eq
                (edge_conjugates_source_lamp edge parameter)⟩
        · have fixed : edgeSwap edge left = left :=
            rangeSwap_of_not_mem _ _ _ sourceMember targetMember
          change edgeSwap edge left = right at equal
          rw [fixed] at equal
          subst right
          exact ⟨1, membershipSubgroup.one_mem, by simp [conjugate]⟩

private theorem lamp_mem_of_connected_from_accepted
    {vertex : LayeredVertex}
    (connected :
      AffinePermutations.Connected
        AffinePermutations.acceptedVertex vertex) :
    lampElement vertex ∈ membershipSubgroup := by
  induction connected with
  | refl =>
      exact Subgroup.subset_closure (Or.inr rfl)
  | tail _ adjacent ih =>
      obtain ⟨actor, actorMember, conjugates⟩ :=
        adjacent_lamp_transport adjacent
      rw [← conjugates]
      exact membershipSubgroup.mul_mem
        (membershipSubgroup.mul_mem actorMember ih)
        (membershipSubgroup.inv_mem actorMember)

theorem lamp_mem_of_connected
    {vertex : LayeredVertex}
    (connected :
    AffinePermutations.Connected vertex
        AffinePermutations.acceptedVertex) :
    lampElement vertex ∈ membershipSubgroup := by
  exact lamp_mem_of_connected_from_accepted (connected_symm connected)

@[simp]
theorem presentedToSemantic_moveElement (move : Move) :
    presentedToSemantic (moveElement move) =
      liftPerm (movePerm move) := by
  change freeToSemantic (moveFree move) = _
  exact freeToSemantic_moveFree move

@[simp]
theorem presentedToSemantic_lampElement (vertex : LayeredVertex) :
    presentedToSemantic (lampElement vertex) = lamp vertex := by
  change freeToSemantic (lampFree vertex) = _
  exact freeToSemantic_lampFree vertex

private theorem membershipSubgroup_maps_to_semantic
    {element : Presented} (member : element ∈ membershipSubgroup) :
    presentedToSemantic element ∈ semanticSubgroup := by
  induction member using Subgroup.closure_induction with
  | mem element member =>
      rcases member with moveMember | lampMember
      · obtain ⟨move, rfl⟩ := moveMember
        rw [presentedToSemantic_moveElement]
        exact Subgroup.subset_closure (Or.inl ⟨move, rfl⟩)
      · simp only [Set.mem_singleton_iff] at lampMember
        subst element
        rw [presentedToSemantic_lampElement]
        exact Subgroup.subset_closure (Or.inr rfl)
  | one => exact semanticSubgroup.one_mem
  | mul left right _ _ leftMember rightMember =>
      simpa only [map_mul] using
        semanticSubgroup.mul_mem leftMember rightMember
  | inv element _ elementMember =>
      simpa only [map_inv] using semanticSubgroup.inv_mem elementMember

theorem connected_of_lamp_mem
    {vertex : LayeredVertex}
    (member : lampElement vertex ∈ membershipSubgroup) :
    AffinePermutations.Connected vertex
      AffinePermutations.acceptedVertex := by
  apply connected_of_lamp_mem_semanticSubgroup
  simpa using membershipSubgroup_maps_to_semantic member

theorem lamp_mem_iff_connected (vertex : LayeredVertex) :
    lampElement vertex ∈ membershipSubgroup ↔
      AffinePermutations.Connected vertex
        AffinePermutations.acceptedVertex :=
  ⟨connected_of_lamp_mem, lamp_mem_of_connected⟩

end

end Submission.AffinePresentation
