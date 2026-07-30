import Submission.AffineGraph

namespace Submission.AffinePermutations

open Submission.AffineGraph

noncomputable section

local instance (proposition : Prop) : Decidable proposition :=
  Classical.propDecidable proposition

section PartialPermutations

variable {α β : Type*}

private def rangeShiftFun [AddGroup β]
    (embedding : β ↪ α) (shift : β) (value : α) : α :=
  if member : value ∈ Set.range embedding then
    embedding (Classical.choose member + shift)
  else
    value

private theorem rangeShiftFun_apply [AddGroup β]
    (embedding : β ↪ α) (shift parameter : β) :
    rangeShiftFun embedding shift (embedding parameter) =
      embedding (parameter + shift) := by
  rw [rangeShiftFun]
  split
  next member =>
    have chosenEqual :
        Classical.choose member = parameter :=
      embedding.injective (Classical.choose_spec member)
    rw [chosenEqual]
  next notMember =>
    exact (notMember ⟨parameter, rfl⟩).elim

private theorem rangeShiftFun_apply_of_not_mem [AddGroup β]
    (embedding : β ↪ α) (shift : β) {value : α}
    (notMember : value ∉ Set.range embedding) :
    rangeShiftFun embedding shift value = value := by
  simp [rangeShiftFun, notMember]

/-- Translate the parameter of every point in an embedded copy of an
additive group and fix the complement. -/
def rangeShift [AddGroup β]
    (embedding : β ↪ α) (shift : β) : Equiv.Perm α where
  toFun := rangeShiftFun embedding shift
  invFun := rangeShiftFun embedding (-shift)
  left_inv value := by
    by_cases member : value ∈ Set.range embedding
    · obtain ⟨parameter, rfl⟩ := member
      rw [rangeShiftFun_apply, rangeShiftFun_apply]
      simp
    · rw [rangeShiftFun_apply_of_not_mem embedding shift member,
        rangeShiftFun_apply_of_not_mem embedding (-shift) member]
  right_inv value := by
    by_cases member : value ∈ Set.range embedding
    · obtain ⟨parameter, rfl⟩ := member
      rw [rangeShiftFun_apply, rangeShiftFun_apply]
      simp
    · rw [rangeShiftFun_apply_of_not_mem embedding (-shift) member,
        rangeShiftFun_apply_of_not_mem embedding shift member]

@[simp]
theorem rangeShift_apply [AddGroup β]
    (embedding : β ↪ α) (shift parameter : β) :
    rangeShift embedding shift (embedding parameter) =
      embedding (parameter + shift) :=
  rangeShiftFun_apply embedding shift parameter

theorem rangeShift_apply_of_not_mem [AddGroup β]
    (embedding : β ↪ α) (shift : β) {value : α}
    (notMember : value ∉ Set.range embedding) :
    rangeShift embedding shift value = value :=
  rangeShiftFun_apply_of_not_mem embedding shift notMember

theorem rangeShift_commute [AddCommGroup β]
    (embedding : β ↪ α) (left right : β) :
    Commute (rangeShift embedding left) (rangeShift embedding right) := by
  apply Equiv.ext
  intro value
  change
    rangeShift embedding left (rangeShift embedding right value) =
      rangeShift embedding right (rangeShift embedding left value)
  by_cases member : value ∈ Set.range embedding
  · obtain ⟨parameter, rfl⟩ := member
    simp only [rangeShift_apply]
    congr 1
    abel
  · simp only [rangeShift_apply_of_not_mem embedding right member,
      rangeShift_apply_of_not_mem embedding left member]

@[simp]
theorem rangeShift_zero [AddGroup β] (embedding : β ↪ α) :
    rangeShift embedding 0 = 1 := by
  apply Equiv.ext
  intro value
  by_cases member : value ∈ Set.range embedding
  · obtain ⟨parameter, rfl⟩ := member
    simp
  · rw [rangeShift_apply_of_not_mem embedding 0 member]
    rfl

theorem rangeShift_add [AddCommGroup β]
    (embedding : β ↪ α) (left right : β) :
    rangeShift embedding (left + right) =
      rangeShift embedding left * rangeShift embedding right := by
  apply Equiv.ext
  intro value
  by_cases member : value ∈ Set.range embedding
  · obtain ⟨parameter, rfl⟩ := member
    simp only [rangeShift_apply, Equiv.Perm.mul_apply]
    congr 1
    abel
  · simp only [Equiv.Perm.mul_apply,
      rangeShift_apply_of_not_mem embedding (left + right) member,
      rangeShift_apply_of_not_mem embedding right member,
      rangeShift_apply_of_not_mem embedding left member]

/-- Parameter translations form a homomorphism from the additive parameter
group, written multiplicatively, into the permutation group. -/
def rangeShiftHom [AddCommGroup β] (embedding : β ↪ α) :
    Multiplicative β →* Equiv.Perm α where
  toFun shift := rangeShift embedding shift.toAdd
  map_one' := rangeShift_zero embedding
  map_mul' left right := rangeShift_add embedding left.toAdd right.toAdd

theorem rangeShift_commute_of_disjoint [AddGroup β]
    (left right : β ↪ α)
    (disjoint : Disjoint (Set.range left) (Set.range right))
    (leftShift rightShift : β) :
    Commute (rangeShift left leftShift) (rangeShift right rightShift) := by
  apply Equiv.ext
  intro value
  change
    rangeShift left leftShift (rangeShift right rightShift value) =
      rangeShift right rightShift (rangeShift left leftShift value)
  by_cases leftMember : value ∈ Set.range left
  · obtain ⟨parameter, rfl⟩ := leftMember
    have notRight : left parameter ∉ Set.range right := by
      intro member
      exact Set.disjoint_left.1 disjoint ⟨parameter, rfl⟩ member
    have shiftedNotRight :
        left (parameter + leftShift) ∉ Set.range right := by
      intro member
      exact Set.disjoint_left.1 disjoint
        ⟨parameter + leftShift, rfl⟩ member
    simp only [rangeShift_apply_of_not_mem right rightShift notRight,
      rangeShift_apply, rangeShift_apply,
      rangeShift_apply_of_not_mem right rightShift shiftedNotRight]
  · by_cases rightMember : value ∈ Set.range right
    · obtain ⟨parameter, rfl⟩ := rightMember
      have notLeft : right parameter ∉ Set.range left := by
        intro member
        exact Set.disjoint_left.1 disjoint member ⟨parameter, rfl⟩
      have shiftedNotLeft :
          right (parameter + rightShift) ∉ Set.range left := by
        intro member
        exact Set.disjoint_left.1 disjoint member
          ⟨parameter + rightShift, rfl⟩
      simp only [rangeShift_apply, rangeShift_apply_of_not_mem left leftShift
          shiftedNotLeft,
        rangeShift_apply_of_not_mem left leftShift notLeft,
        rangeShift_apply]
    · simp only [rangeShift_apply_of_not_mem right rightShift rightMember,
        rangeShift_apply_of_not_mem left leftShift leftMember]

private def rangeSwapFun
    (left right : β ↪ α) (value : α) : α :=
  if leftMember : value ∈ Set.range left then
    right (Classical.choose leftMember)
  else if rightMember : value ∈ Set.range right then
    left (Classical.choose rightMember)
  else
    value

private theorem rangeSwapFun_left
    (left right : β ↪ α) (_disjoint : Disjoint (Set.range left) (Set.range right))
    (parameter : β) :
    rangeSwapFun left right (left parameter) = right parameter := by
  rw [rangeSwapFun]
  split
  next member =>
    have chosenEqual :
        Classical.choose member = parameter :=
      left.injective (Classical.choose_spec member)
    rw [chosenEqual]
  next notMember =>
    exact (notMember ⟨parameter, rfl⟩).elim

private theorem rangeSwapFun_right
    (left right : β ↪ α) (disjoint : Disjoint (Set.range left) (Set.range right))
    (parameter : β) :
    rangeSwapFun left right (right parameter) = left parameter := by
  rw [rangeSwapFun]
  have notLeft : right parameter ∉ Set.range left := by
    intro member
    exact Set.disjoint_left.1 disjoint member ⟨parameter, rfl⟩
  simp only [notLeft, ↓reduceDIte]
  split
  next member =>
    have chosenEqual :
        Classical.choose member = parameter :=
      right.injective (Classical.choose_spec member)
    rw [chosenEqual]
  next notMember =>
    exact (notMember ⟨parameter, rfl⟩).elim

private theorem rangeSwapFun_of_not_mem
    (left right : β ↪ α) {value : α}
    (notLeft : value ∉ Set.range left)
    (notRight : value ∉ Set.range right) :
    rangeSwapFun left right value = value := by
  simp [rangeSwapFun, notLeft, notRight]

/-- Swap two disjoint embedded copies pointwise and fix their complement. -/
def rangeSwap
    (left right : β ↪ α)
    (disjoint : Disjoint (Set.range left) (Set.range right)) :
    Equiv.Perm α :=
  Function.Involutive.toPerm (rangeSwapFun left right) <| by
    intro value
    by_cases leftMember : value ∈ Set.range left
    · obtain ⟨parameter, rfl⟩ := leftMember
      rw [rangeSwapFun_left left right disjoint,
        rangeSwapFun_right left right disjoint]
    · by_cases rightMember : value ∈ Set.range right
      · obtain ⟨parameter, rfl⟩ := rightMember
        rw [rangeSwapFun_right left right disjoint,
          rangeSwapFun_left left right disjoint]
      · rw [rangeSwapFun_of_not_mem left right leftMember rightMember,
          rangeSwapFun_of_not_mem left right leftMember rightMember]

@[simp]
theorem rangeSwap_left
    (left right : β ↪ α)
    (disjoint : Disjoint (Set.range left) (Set.range right))
    (parameter : β) :
    rangeSwap left right disjoint (left parameter) = right parameter :=
  rangeSwapFun_left left right disjoint parameter

@[simp]
theorem rangeSwap_right
    (left right : β ↪ α)
    (disjoint : Disjoint (Set.range left) (Set.range right))
    (parameter : β) :
    rangeSwap left right disjoint (right parameter) = left parameter :=
  rangeSwapFun_right left right disjoint parameter

theorem rangeSwap_of_not_mem
    (left right : β ↪ α)
    (disjoint : Disjoint (Set.range left) (Set.range right))
    {value : α}
    (notLeft : value ∉ Set.range left)
    (notRight : value ∉ Set.range right) :
    rangeSwap left right disjoint value = value :=
  rangeSwapFun_of_not_mem left right notLeft notRight

/-- Pointwise swapping intertwines the translations on the two embedded
copies. -/
theorem rangeSwap_mul_rangeShift
    [AddGroup β]
    (left right : β ↪ α)
    (disjoint : Disjoint (Set.range left) (Set.range right))
    (shift : β) :
    rangeSwap left right disjoint * rangeShift left shift =
      rangeShift right shift * rangeSwap left right disjoint := by
  apply Equiv.ext
  intro value
  change
    rangeSwap left right disjoint (rangeShift left shift value) =
      rangeShift right shift (rangeSwap left right disjoint value)
  by_cases leftMember : value ∈ Set.range left
  · obtain ⟨parameter, rfl⟩ := leftMember
    rw [rangeShift_apply, rangeSwap_left, rangeSwap_left, rangeShift_apply]
  · by_cases rightMember : value ∈ Set.range right
    · obtain ⟨parameter, rfl⟩ := rightMember
      have notLeft : right parameter ∉ Set.range left := by
        intro member
        exact Set.disjoint_left.1 disjoint member ⟨parameter, rfl⟩
      have notRight : left parameter ∉ Set.range right := by
        intro member
        exact Set.disjoint_left.1 disjoint ⟨parameter, rfl⟩ member
      simp only [rangeShift_apply_of_not_mem left shift notLeft,
        rangeSwap_right, rangeSwap_right,
        rangeShift_apply_of_not_mem right shift notRight]
    · simp only [rangeShift_apply_of_not_mem left shift leftMember,
        rangeSwap_of_not_mem left right disjoint leftMember rightMember,
        rangeShift_apply_of_not_mem right shift rightMember]

end PartialPermutations

/-! ## Layered affine graph -/

/-- A second layer makes the two endpoint ranges of every chart disjoint. -/
abbrev LayeredVertex := Bool × Vertex

def layeredSource (edge : Edge) : Param ↪ LayeredVertex where
  toFun parameter := (false, source edge parameter)
  inj' := by
    intro left right equal
    exact source_injective edge (congrArg Prod.snd equal)

def layeredTarget (edge : Edge) : Param ↪ LayeredVertex where
  toFun parameter := (true, target edge parameter)
  inj' := by
    intro left right equal
    exact target_injective edge (congrArg Prod.snd equal)

@[simp]
theorem layeredSource_apply (edge : Edge) (parameter : Param) :
    layeredSource edge parameter = (false, source edge parameter) :=
  rfl

@[simp]
theorem layeredTarget_apply (edge : Edge) (parameter : Param) :
    layeredTarget edge parameter = (true, target edge parameter) :=
  rfl

private theorem layered_ranges_disjoint (edge : Edge) :
    Disjoint (Set.range (layeredSource edge))
      (Set.range (layeredTarget edge)) := by
  rw [Set.disjoint_left]
  intro value sourceMember targetMember
  obtain ⟨sourceParameter, rfl⟩ := sourceMember
  obtain ⟨targetParameter, equal⟩ := targetMember
  simp [layeredSource, layeredTarget] at equal

/-- The involution which swaps all corresponding endpoints of one affine
chart simultaneously. -/
def edgeSwap (edge : Edge) : Equiv.Perm LayeredVertex :=
  rangeSwap (layeredSource edge) (layeredTarget edge)
    (layered_ranges_disjoint edge)

@[simp]
theorem edgeSwap_source (edge : Edge) (parameter : Param) :
    edgeSwap edge (false, source edge parameter) =
      (true, target edge parameter) :=
  rangeSwap_left _ _ _ parameter

@[simp]
theorem edgeSwap_target (edge : Edge) (parameter : Param) :
    edgeSwap edge (true, target edge parameter) =
      (false, source edge parameter) :=
  rangeSwap_right _ _ _ parameter

/-- Select the source (`false`) or target (`true`) endpoint embedding. -/
def endpointEmbedding (edge : Edge) (side : Bool) : Param ↪ LayeredVertex :=
  if side then layeredTarget edge else layeredSource edge

@[simp]
theorem endpointEmbedding_false (edge : Edge) :
    endpointEmbedding edge false = layeredSource edge := rfl

@[simp]
theorem endpointEmbedding_true (edge : Edge) :
    endpointEmbedding edge true = layeredTarget edge := rfl

/-- Translation along the parameter plane of one chart endpoint. -/
def chartShift (edge : Edge) (side : Bool) (shift : Param) :
    Equiv.Perm LayeredVertex :=
  rangeShift (endpointEmbedding edge side) shift

@[simp]
theorem chartShift_apply
    (edge : Edge) (side : Bool) (shift parameter : Param) :
    chartShift edge side shift (endpointEmbedding edge side parameter) =
      endpointEmbedding edge side (parameter + shift) :=
  rangeShift_apply _ _ _

theorem chartShift_commute
    (edge : Edge) (side : Bool) (left right : Param) :
    Commute (chartShift edge side left) (chartShift edge side right) :=
  rangeShift_commute _ _ _

theorem edgeSwap_mul_chartShift
    (edge : Edge) (shift : Param) :
    edgeSwap edge * chartShift edge false shift =
      chartShift edge true shift * edgeSwap edge :=
  rangeSwap_mul_rangeShift _ _ _ shift

/-- The full coordinate fiber at one layer and one control. -/
def fiber (layer : Bool) (control : Control) : Coord ↪ LayeredVertex where
  toFun coordinate := (layer, control, coordinate)
  inj' := by
    intro left right equal
    exact congrArg (Prod.snd ∘ Prod.snd) equal

/-- Translate a complete layer/control coordinate fiber. -/
def globalShift (layer : Bool) (control : Control) (shift : Coord) :
    Equiv.Perm LayeredVertex :=
  rangeShift (fiber layer control) shift

@[simp]
theorem globalShift_apply
    (layer : Bool) (control : Control) (shift coordinate : Coord) :
    globalShift layer control shift (layer, control, coordinate) =
      (layer, control, coordinate + shift) :=
  rangeShift_apply _ _ _

theorem globalShift_commute
    (leftLayer rightLayer : Bool)
    (leftControl rightControl : Control)
    (leftShift rightShift : Coord) :
    Commute
      (globalShift leftLayer leftControl leftShift)
      (globalShift rightLayer rightControl rightShift) := by
  by_cases layerEqual : leftLayer = rightLayer
  · subst rightLayer
    by_cases controlEqual : leftControl = rightControl
    · subst rightControl
      exact rangeShift_commute _ _ _
    · apply rangeShift_commute_of_disjoint
      rw [Set.disjoint_left]
      intro value leftMember rightMember
      obtain ⟨leftCoordinate, rfl⟩ := leftMember
      obtain ⟨rightCoordinate, equal⟩ := rightMember
      exact controlEqual
        (congrArg (fun point : LayeredVertex => point.2.1) equal).symm
  · apply rangeShift_commute_of_disjoint
    rw [Set.disjoint_left]
    intro value leftMember rightMember
    obtain ⟨leftCoordinate, rfl⟩ := leftMember
    obtain ⟨rightCoordinate, equal⟩ := rightMember
    exact layerEqual (congrArg Prod.fst equal).symm

def parameterBasis : Fin 2 → Param
  | 0 => (1, 0)
  | 1 => (0, 1)

@[simp]
theorem parameter_add_basis_zero (parameter : Param) :
    parameter + parameterBasis 0 = (parameter.1 + 1, parameter.2) := by
  ext <;> simp [parameterBasis]

@[simp]
theorem parameter_add_basis_one (parameter : Param) :
    parameter + parameterBasis 1 = (parameter.1, parameter.2 + 1) := by
  ext <;> simp [parameterBasis]

/-- The affine law needed to compare chart-parameter shifts with global
coordinate translations. -/
def IsAffine (embedding : Param ↪ Coord) : Prop :=
  ∀ left right,
    embedding (left + right) =
      embedding left + embedding right - embedding 0

private theorem full_affine : IsAffine full := by
  intro left right
  funext i
  fin_cases i <;> simp [full, coord]

private theorem leftCons_affine (digit : ℤ) :
    IsAffine (leftCons digit) := by
  intro left right
  funext i
  fin_cases i <;> simp [leftCons, coord]
  ring

private theorem movedLeft_affine (digit : ℤ) :
    IsAffine (movedLeft digit) := by
  intro left right
  funext i
  fin_cases i <;> simp [movedLeft, coord]
  ring

private theorem leftEmpty_affine : IsAffine leftEmpty := by
  intro left right
  funext i
  fin_cases i <;> simp [leftEmpty, coord]

private theorem movedLeftEmpty_affine (digit : ℤ) :
    IsAffine (movedLeftEmpty digit) := by
  intro left right
  funext i
  fin_cases i <;> simp [movedLeftEmpty, coord]
  ring

private theorem rightEmpty_affine : IsAffine rightEmpty := by
  intro left right
  funext i
  fin_cases i <;> simp [rightEmpty, coord]

private theorem movedRightEmpty_affine (digit : ℤ) :
    IsAffine (movedRightEmpty digit) := by
  intro left right
  funext i
  fin_cases i <;> simp [movedRightEmpty, coord]
  ring

private theorem rightCons_affine (digit : ℤ) :
    IsAffine (rightCons digit) :=
  movedLeft_affine digit

private theorem movedRight_affine (digit : ℤ) :
    IsAffine (movedRight digit) :=
  leftCons_affine digit

private theorem physicalZero_affine : IsAffine physicalZero := by
  intro left right
  funext i
  fin_cases i <;> simp [physicalZero, coord]

private theorem idleSpec_affine :
    IsAffine idleSpec.sourceCoord ∧ IsAffine idleSpec.targetCoord :=
  ⟨full_affine, full_affine⟩

private theorem runSpec_affine
    (state : Q) (head : AffineGraph.Symbol) (kind : RunKind) :
    IsAffine (runSpec state head kind).sourceCoord ∧
      IsAffine (runSpec state head kind).targetCoord := by
  cases transition : UniversalMachine.universalTM0 state head with
  | none =>
      cases kind <;>
        simpa only [runSpec, transition, idleSpec] using
          And.intro full_affine full_affine
  | some result =>
      rcases result with ⟨nextState, statement⟩
      cases statement with
      | write written =>
          cases kind <;>
            simpa only [runSpec, transition, idleSpec] using
              And.intro full_affine full_affine
      | move direction =>
          cases direction with
          | left =>
              cases kind with
              | halt => simpa [runSpec, transition] using idleSpec_affine
              | write => simpa [runSpec, transition] using idleSpec_affine
              | leftEmpty =>
                  simpa [runSpec, transition] using
                    And.intro leftEmpty_affine (movedLeftEmpty_affine _)
              | leftCons neighbor =>
                  simpa [runSpec, transition] using
                    And.intro (leftCons_affine _) (movedLeft_affine _)
              | rightEmpty =>
                  simpa [runSpec, transition] using idleSpec_affine
              | rightCons neighbor =>
                  simpa [runSpec, transition] using idleSpec_affine
          | right =>
              cases kind with
              | halt => simpa [runSpec, transition] using idleSpec_affine
              | write => simpa [runSpec, transition] using idleSpec_affine
              | leftEmpty =>
                  simpa [runSpec, transition] using idleSpec_affine
              | leftCons neighbor =>
                  simpa [runSpec, transition] using idleSpec_affine
              | rightEmpty =>
                  simpa [runSpec, transition] using
                    And.intro rightEmpty_affine (movedRightEmpty_affine _)
              | rightCons neighbor =>
                  simpa [runSpec, transition] using
                    And.intro (rightCons_affine _) (movedRight_affine _)

theorem spec_affine (edge : Edge) :
    IsAffine (spec edge).sourceCoord ∧
      IsAffine (spec edge).targetCoord := by
  cases edge with
  | run state head kind => exact runSpec_affine state head kind
  | cleanLeftEmpty =>
      exact ⟨leftEmpty_affine, leftEmpty_affine⟩
  | cleanLeftCons symbol =>
      exact ⟨leftCons_affine _, full_affine⟩
  | cleanRightEmpty =>
      exact ⟨physicalZero_affine, physicalZero_affine⟩
  | cleanRightCons symbol =>
      exact ⟨movedLeftEmpty_affine _, leftEmpty_affine⟩

def endpointControl (edge : Edge) (side : Bool) : Control :=
  if side then (spec edge).targetControl else (spec edge).sourceControl

def endpointCoordinate (edge : Edge) (side : Bool) (parameter : Param) :
    Coord :=
  if side then (spec edge).targetCoord parameter
  else (spec edge).sourceCoord parameter

@[simp]
theorem endpointEmbedding_apply
    (edge : Edge) (side : Bool) (parameter : Param) :
    endpointEmbedding edge side parameter =
      (side, endpointControl edge side, endpointCoordinate edge side parameter) := by
  cases side <;>
    simp [endpointEmbedding, layeredSource, layeredTarget, endpointControl,
      endpointCoordinate, source, target]

theorem endpointCoordinate_affine (edge : Edge) (side : Bool) :
    ∀ left right,
      endpointCoordinate edge side (left + right) =
        endpointCoordinate edge side left +
          endpointCoordinate edge side right -
            endpointCoordinate edge side 0 := by
  cases side
  · exact (spec_affine edge).1
  · exact (spec_affine edge).2

def endpointDirection (edge : Edge) (side : Bool) (axis : Fin 2) : Coord :=
  endpointCoordinate edge side (parameterBasis axis) -
    endpointCoordinate edge side 0

theorem endpointCoordinate_add_basis
    (edge : Edge) (side : Bool) (parameter : Param) (axis : Fin 2) :
    endpointCoordinate edge side (parameter + parameterBasis axis) =
      endpointCoordinate edge side parameter +
        endpointDirection edge side axis := by
  rw [endpointCoordinate_affine]
  simp only [endpointDirection]
  abel

theorem globalShift_endpoint
    (edge : Edge) (side : Bool) (parameter : Param) (axis : Fin 2) :
    globalShift side (endpointControl edge side)
        (endpointDirection edge side axis)
        (endpointEmbedding edge side parameter) =
      endpointEmbedding edge side (parameter + parameterBasis axis) := by
  rw [endpointEmbedding_apply, globalShift_apply,
    endpointEmbedding_apply, endpointCoordinate_add_basis]

theorem endpointCoordinate_sub_basis
    (edge : Edge) (side : Bool) (parameter : Param) (axis : Fin 2) :
    endpointCoordinate edge side (parameter - parameterBasis axis) =
      endpointCoordinate edge side parameter -
        endpointDirection edge side axis := by
  have affine :=
    endpointCoordinate_affine edge side parameter (-parameterBasis axis)
  rw [show parameter + -parameterBasis axis =
    parameter - parameterBasis axis by abel] at affine
  rw [affine]
  simp only [endpointDirection]
  have affineZero :=
    endpointCoordinate_affine edge side
      (parameterBasis axis) (-parameterBasis axis)
  simp only [add_neg_cancel] at affineZero
  have negative :
      endpointCoordinate edge side (-parameterBasis axis) =
        endpointCoordinate edge side 0 +
          endpointCoordinate edge side 0 -
            endpointCoordinate edge side (parameterBasis axis) := by
    calc
      endpointCoordinate edge side (-parameterBasis axis) =
          (endpointCoordinate edge side (parameterBasis axis) +
              endpointCoordinate edge side (-parameterBasis axis) -
                endpointCoordinate edge side 0) +
            endpointCoordinate edge side 0 -
              endpointCoordinate edge side (parameterBasis axis) := by
        abel
      _ = endpointCoordinate edge side 0 +
            endpointCoordinate edge side 0 -
              endpointCoordinate edge side (parameterBasis axis) := by
        rw [← affineZero]
  rw [negative]
  abel

private theorem globalShift_endpoint_neg
    (edge : Edge) (side : Bool) (parameter : Param) (axis : Fin 2) :
    globalShift side (endpointControl edge side)
        (-endpointDirection edge side axis)
        (endpointEmbedding edge side parameter) =
      endpointEmbedding edge side (parameter - parameterBasis axis) := by
  rw [endpointEmbedding_apply, globalShift_apply,
    endpointEmbedding_apply, endpointCoordinate_sub_basis]
  simp [sub_eq_add_neg]

private theorem globalShift_preserves_endpoint_complement
    (edge : Edge) (side : Bool) (axis : Fin 2) {value : LayeredVertex}
    (notMember :
      value ∉ Set.range (endpointEmbedding edge side)) :
    globalShift side (endpointControl edge side)
        (endpointDirection edge side axis) value ∉
      Set.range (endpointEmbedding edge side) := by
  intro shiftedMember
  obtain ⟨parameter, shiftedEqual⟩ := shiftedMember
  apply notMember
  refine ⟨parameter - parameterBasis axis, ?_⟩
  have inverseEqual :=
    congrArg
      (globalShift side (endpointControl edge side)
        (-endpointDirection edge side axis)) shiftedEqual
  rw [globalShift_endpoint_neg] at inverseEqual
  have cancel :
      globalShift side (endpointControl edge side)
          (-endpointDirection edge side axis)
          (globalShift side (endpointControl edge side)
            (endpointDirection edge side axis) value) =
        value := by
    change
      rangeShift (fiber side (endpointControl edge side))
          (-endpointDirection edge side axis)
          (rangeShift (fiber side (endpointControl edge side))
            (endpointDirection edge side axis) value) = value
    exact (rangeShift
      (fiber side (endpointControl edge side))
      (endpointDirection edge side axis)).left_inv value
  exact inverseEqual.trans cancel

/-- A chart-parameter shift commutes with the matching global coordinate
translation along either affine direction. -/
theorem chartShift_commute_global
    (edge : Edge) (side : Bool) (parameterShift : Param) (axis : Fin 2) :
    Commute
      (chartShift edge side parameterShift)
      (globalShift side (endpointControl edge side)
        (endpointDirection edge side axis)) := by
  apply Equiv.ext
  intro value
  change
    chartShift edge side parameterShift
        (globalShift side (endpointControl edge side)
          (endpointDirection edge side axis) value) =
      globalShift side (endpointControl edge side)
        (endpointDirection edge side axis)
        (chartShift edge side parameterShift value)
  by_cases member : value ∈ Set.range (endpointEmbedding edge side)
  · obtain ⟨parameter, rfl⟩ := member
    simp only [globalShift_endpoint, chartShift_apply]
    apply congrArg (endpointEmbedding edge side)
    abel
  · have shiftedNotMember :=
      globalShift_preserves_endpoint_complement edge side axis member
    simp only [chartShift,
      rangeShift_apply_of_not_mem
        (endpointEmbedding edge side) parameterShift member,
      rangeShift_apply_of_not_mem
        (endpointEmbedding edge side) parameterShift shiftedNotMember]

/-- Toggle the duplicate layer without changing an affine vertex. -/
def layerFlip : Equiv.Perm LayeredVertex where
  toFun value := (!value.1, value.2)
  invFun value := (!value.1, value.2)
  left_inv value := by cases value.1 <;> simp
  right_inv value := by cases value.1 <;> simp

@[simp]
theorem layerFlip_apply (layer : Bool) (vertex : Vertex) :
    layerFlip (layer, vertex) = (!layer, vertex) := rfl

theorem layerFlip_mul_globalShift
    (control : Control) (shift : Coord) :
    layerFlip * globalShift false control shift =
      globalShift true control shift * layerFlip := by
  apply Equiv.ext
  rintro ⟨layer, currentControl, coordinate⟩
  cases layer with
  | false =>
      by_cases controlEqual : currentControl = control
      · subst currentControl
        change
          layerFlip
              (globalShift false control shift
                (false, control, coordinate)) =
            globalShift true control shift
              (layerFlip (false, control, coordinate))
        simp
      · have notFalse :
          (false, currentControl, coordinate) ∉
            Set.range (fiber false control) := by
          rintro ⟨other, equal⟩
          exact controlEqual
            (congrArg (fun point : LayeredVertex => point.2.1) equal).symm
        have notTrue :
          (true, currentControl, coordinate) ∉
            Set.range (fiber true control) := by
          rintro ⟨other, equal⟩
          exact controlEqual
            (congrArg (fun point : LayeredVertex => point.2.1) equal).symm
        change
          layerFlip
              (rangeShift (fiber false control) shift
                (false, currentControl, coordinate)) =
            rangeShift (fiber true control) shift
              (true, currentControl, coordinate)
        rw [rangeShift_apply_of_not_mem _ _ notFalse,
          rangeShift_apply_of_not_mem _ _ notTrue]
        rfl
  | true =>
      have notFalse :
          (true, currentControl, coordinate) ∉
            Set.range (fiber false control) := by
        rintro ⟨other, equal⟩
        simp [fiber] at equal
      have notTrue :
          (false, currentControl, coordinate) ∉
            Set.range (fiber true control) := by
        rintro ⟨other, equal⟩
        simp [fiber] at equal
      change
        layerFlip
            (rangeShift (fiber false control) shift
              (true, currentControl, coordinate)) =
          rangeShift (fiber true control) shift
            (false, currentControl, coordinate)
      rw [rangeShift_apply_of_not_mem _ _ notFalse,
        rangeShift_apply_of_not_mem _ _ notTrue]
      rfl

/-- The finite permutation alphabet generating the layered affine graph. -/
inductive Move
  | flip
  | edge (chart : Edge)
  deriving DecidableEq, Fintype

def movePerm : Move → Equiv.Perm LayeredVertex
  | .flip => layerFlip
  | .edge chart => edgeSwap chart

theorem movePerm_involutive (move : Move) :
    Function.Involutive (movePerm move) := by
  intro vertex
  cases move with
  | flip =>
      rcases vertex with ⟨layer, vertex⟩
      cases layer <;> rfl
  | edge chart =>
      change edgeSwap chart (edgeSwap chart vertex) = vertex
      by_cases sourceMember :
          vertex ∈ Set.range (layeredSource chart)
      · obtain ⟨parameter, rfl⟩ := sourceMember
        rw [layeredSource_apply, edgeSwap_source, edgeSwap_target]
      · by_cases targetMember :
          vertex ∈ Set.range (layeredTarget chart)
        · obtain ⟨parameter, rfl⟩ := targetMember
          rw [layeredTarget_apply, edgeSwap_target, edgeSwap_source]
        · have fixed : edgeSwap chart vertex = vertex :=
            rangeSwap_of_not_mem _ _ _ sourceMember targetMember
          exact (congrArg (edgeSwap chart) fixed).trans fixed

def Adjacent (left right : LayeredVertex) : Prop :=
  ∃ move, movePerm move left = right

def Connected (left right : LayeredVertex) : Prop :=
  Relation.ReflTransGen Adjacent left right

theorem adjacent_symm {left right : LayeredVertex} :
    Adjacent left right → Adjacent right left := by
  rintro ⟨move, equal⟩
  refine ⟨move, ?_⟩
  rw [← equal]
  exact movePerm_involutive move left

theorem connected_symm {left right : LayeredVertex} :
    Connected left right → Connected right left := by
  intro connected
  induction connected with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ adjacent ih =>
      exact Relation.ReflTransGen.head (adjacent_symm adjacent) ih

private theorem connected_of_affineAdjacent
    {left right : Vertex} (adjacent : AffineGraph.Adjacent left right) :
    Connected (false, left) (false, right) := by
  obtain ⟨edge, parameter, forward | backward⟩ := adjacent
  · obtain ⟨sourceEqual, targetEqual⟩ := forward
    subst left
    subst right
    exact
      (Relation.ReflTransGen.single
        ⟨.edge edge, edgeSwap_source edge parameter⟩).tail
          ⟨.flip, rfl⟩
  · obtain ⟨sourceEqual, targetEqual⟩ := backward
    subst left
    subst right
    exact
      (Relation.ReflTransGen.single
        ⟨.flip, rfl⟩).tail
          ⟨.edge edge, edgeSwap_target edge parameter⟩

theorem connected_of_affineConnected
    {left right : Vertex}
    (connected : AffineGraph.Connected left right) :
    Connected (false, left) (false, right) := by
  induction connected with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ adjacent ih =>
      exact ih.trans (connected_of_affineAdjacent adjacent)

private theorem edgeSwap_projection (edge : Edge) (value : LayeredVertex) :
    (edgeSwap edge value).2 = value.2 ∨
      AffineGraph.Adjacent value.2 (edgeSwap edge value).2 := by
  by_cases sourceMember : value ∈ Set.range (layeredSource edge)
  · obtain ⟨parameter, rfl⟩ := sourceMember
    rw [layeredSource_apply, edgeSwap_source]
    exact Or.inr
      ⟨edge, parameter, Or.inl ⟨rfl, rfl⟩⟩
  · by_cases targetMember : value ∈ Set.range (layeredTarget edge)
    · obtain ⟨parameter, rfl⟩ := targetMember
      rw [layeredTarget_apply, edgeSwap_target]
      exact Or.inr
        ⟨edge, parameter, Or.inr ⟨rfl, rfl⟩⟩
    · have fixed : edgeSwap edge value = value :=
        rangeSwap_of_not_mem _ _ _ sourceMember targetMember
      rw [fixed]
      exact Or.inl rfl

private theorem move_projection
    {left right : LayeredVertex} (adjacent : Adjacent left right) :
    right.2 = left.2 ∨ AffineGraph.Adjacent left.2 right.2 := by
  obtain ⟨move, rfl⟩ := adjacent
  cases move with
  | flip => exact Or.inl rfl
  | edge chart => exact edgeSwap_projection chart left

theorem affineConnected_of_connected
    {left right : LayeredVertex} (connected : Connected left right) :
    AffineGraph.Connected left.2 right.2 := by
  induction connected with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ adjacent ih =>
      obtain unchanged | affineAdjacent := move_projection adjacent
      · simpa [unchanged] using ih
      · exact ih.tail affineAdjacent

def initialVertex (code : Nat.Partrec.Code) : LayeredVertex :=
  (false, encodeState (initialState code))

def acceptedVertex : LayeredVertex :=
  (false, AffineGraph.acceptedVertex)

theorem halting_iff_connected (code : Nat.Partrec.Code) :
    (Nat.Partrec.Code.eval code 0).Dom ↔
      Connected (initialVertex code) acceptedVertex := by
  constructor
  · intro halts
    exact connected_of_affineConnected <|
      (AffineGraph.halting_iff_connected code).mp halts
  · intro connected
    exact (AffineGraph.halting_iff_connected code).mpr <|
      affineConnected_of_connected connected

/-! ## A permutation model with one movable marker -/

abbrev SemanticPoint := Option LayeredVertex

/-- Lift a vertex permutation while fixing a distinguished marker. -/
def liftPerm (permutation : Equiv.Perm LayeredVertex) :
    Equiv.Perm SemanticPoint :=
  Equiv.optionCongr permutation

def liftPermHom :
    Equiv.Perm LayeredVertex →* Equiv.Perm SemanticPoint where
  toFun := liftPerm
  map_one' := by
    ext point
    cases point <;> rfl
  map_mul' left right := by
    ext point
    cases point <;> rfl

@[simp]
theorem liftPerm_none (permutation : Equiv.Perm LayeredVertex) :
    liftPerm permutation none = none := rfl

@[simp]
theorem liftPerm_some
    (permutation : Equiv.Perm LayeredVertex) (vertex : LayeredVertex) :
    liftPerm permutation (some vertex) = some (permutation vertex) := rfl

/-- The lamp at a vertex is the transposition of that vertex with the
distinguished marker. -/
def lamp (vertex : LayeredVertex) : Equiv.Perm SemanticPoint :=
  Equiv.swap none (some vertex)

@[simp]
theorem lamp_none (vertex : LayeredVertex) :
    lamp vertex none = some vertex :=
  Equiv.swap_apply_left _ _

@[simp]
theorem lamp_self (vertex : LayeredVertex) :
    lamp vertex (some vertex) = none :=
  Equiv.swap_apply_right _ _

theorem liftPerm_mul_lamp
    (permutation : Equiv.Perm LayeredVertex) (vertex : LayeredVertex) :
    liftPerm permutation * lamp vertex =
      lamp (permutation vertex) * liftPerm permutation := by
  apply Equiv.ext
  intro point
  change
    liftPerm permutation (lamp vertex point) =
      lamp (permutation vertex) (liftPerm permutation point)
  cases point with
  | none => simp
  | some value =>
      by_cases equal : value = vertex
      · subst value
        simp
      · have mappedUnequal :
          permutation value ≠ permutation vertex :=
        permutation.injective.ne equal
        simp [lamp, Equiv.swap_apply_of_ne_of_ne, equal, mappedUnequal]

end

end Submission.AffinePermutations
