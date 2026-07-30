import Submission.AffineMachine
import Submission.UniversalMachine

open Turing

namespace Submission.AffineGraph

open Submission.AffineMachine
open Submission.MachineRules
open Submission.UniversalMachine

noncomputable section

private local instance universalStateInhabited :
    Inhabited Turing.PartrecToTM2.Λ' :=
  ⟨Turing.PartrecToTM2.trNormal universalProgram
    Turing.PartrecToTM2.Cont'.halt⟩

private abbrev MachineState :=
  Turing.TM1to0.Λ' universalTM1

private local instance : DecidableEq MachineState :=
  Classical.decEq _

abbrev Symbol :=
  Turing.TM2to1.Γ' Turing.PartrecToTM2.K'
    (fun _ => Turing.PartrecToTM2.Γ')

private local instance : Fintype Turing.PartrecToTM2.K' where
  elems :=
    { Turing.PartrecToTM2.K'.main, Turing.PartrecToTM2.K'.rev,
      Turing.PartrecToTM2.K'.aux, Turing.PartrecToTM2.K'.stack }
  complete value := by
    cases value <;> simp

private local instance : DecidableEq Symbol :=
  Classical.decEq _

private abbrev Support :=
  universalTM0Support

/-- The finite state alphabet of the supported universal machine. -/
abbrev Q := SupportedState Support

/-- Finite controls used by the run and cleanup phases. -/
inductive Control
  | run (state : Q) (head : Symbol)
  | cleanLeft
  | cleanRight
  | accepted
  deriving DecidableEq, Fintype

/-- Candidate local cases for a universal-machine transition.  Exactly the
case selected by the fixed transition function is operational; all other
cases are interpreted as harmless self-edges at `accepted`. -/
inductive RunKind
  | halt
  | write
  | leftEmpty
  | leftCons (neighbor : Symbol)
  | rightEmpty
  | rightCons (neighbor : Symbol)
  deriving DecidableEq, Fintype

/-- The finite list of affine edge charts. -/
inductive Edge
  | run (state : Q) (head : Symbol) (kind : RunKind)
  | cleanLeftEmpty
  | cleanLeftCons (symbol : Symbol)
  | cleanRightEmpty
  | cleanRightCons (symbol : Symbol)
  deriving DecidableEq, Fintype

/-- A canonical numbering of the finite compiled tape alphabet. -/
def symbolEquiv : Symbol ≃ Fin (Fintype.card Symbol) :=
  Fintype.equivFin _

/-- The base used to encode finite stacks; every symbol receives a nonzero
digit strictly below this radix. -/
def radixInt : ℤ :=
  Fintype.card Symbol + 1

theorem radixInt_pos : 0 < radixInt := by
  simp [radixInt]

def digitInt (symbol : Symbol) : ℤ :=
  (symbolEquiv symbol).val + 1

private theorem digitInt_pos (symbol : Symbol) : 0 < digitInt symbol := by
  simp [digitInt]

private theorem digitInt_lt_radix (symbol : Symbol) :
    digitInt symbol < radixInt := by
  simp [digitInt, radixInt, (symbolEquiv symbol).isLt]

private theorem digitInt_emod (symbol : Symbol) :
    digitInt symbol % radixInt = digitInt symbol :=
  Int.emod_eq_of_lt (le_of_lt (digitInt_pos symbol))
    (digitInt_lt_radix symbol)

private theorem digitInt_injective : Function.Injective digitInt := by
  intro left right equal
  apply symbolEquiv.injective
  apply Fin.ext
  simp [digitInt] at equal
  omega

/-- Base-`radixInt` coding of a finite tape half. -/
def stackCode : List Symbol → ℤ
  | [] => 0
  | symbol :: rest => digitInt symbol + radixInt * stackCode rest

@[simp]
theorem stackCode_nil : stackCode [] = 0 := rfl

@[simp]
theorem stackCode_cons (symbol : Symbol) (rest : List Symbol) :
    stackCode (symbol :: rest) =
      digitInt symbol + radixInt * stackCode rest := rfl

/-- An integer which has a valid leading digit has a unique decoded first
symbol and tail whenever it is itself a stack code. -/
private theorem stackCode_eq_digit_add
    {stack : List Symbol} {symbol : Symbol} {tailCode : ℤ}
    (equal :
      stackCode stack = digitInt symbol + radixInt * tailCode) :
    ∃ rest,
      stack = symbol :: rest ∧ stackCode rest = tailCode := by
  cases stack with
  | nil =>
      have modEqual := congrArg (fun value : ℤ => value % radixInt) equal
      rw [stackCode_nil, Int.zero_emod,
        Int.add_mul_emod_self_left, digitInt_emod] at modEqual
      exact (ne_of_gt (digitInt_pos symbol) modEqual.symm).elim
  | cons other rest =>
      have modEqual := congrArg (fun value : ℤ => value % radixInt) equal
      rw [stackCode_cons, Int.add_mul_emod_self_left, digitInt_emod,
        Int.add_mul_emod_self_left, digitInt_emod] at modEqual
      have symbolEqual : other = symbol :=
        digitInt_injective modEqual
      subst other
      refine ⟨rest, rfl, ?_⟩
      simp only [stackCode_cons] at equal
      have productEqual :
          radixInt * stackCode rest = radixInt * tailCode :=
        add_left_cancel equal
      exact mul_left_cancel₀ (ne_of_gt radixInt_pos) productEqual

theorem stackCode_injective : Function.Injective stackCode := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons symbol rest =>
          obtain ⟨tail, impossible, _⟩ :=
            stackCode_eq_digit_add
              (stack := [])
              (symbol := symbol)
              (tailCode := stackCode rest) equal
          simp at impossible
  | cons symbol rest ih =>
      intro right equal
      obtain ⟨tail, rightEqual, tailEqual⟩ :=
        stackCode_eq_digit_add
          (stack := right)
          (symbol := symbol)
          (tailCode := stackCode rest) equal.symm
      subst right
      rw [ih tailEqual.symm]

/-- Two integer parameters enumerate every local transition chart. -/
abbrev Param := ℤ × ℤ

/-- Physical left/right stack coordinates followed by two harmless ghost
coordinates used to keep the empty-stack charts rank two. -/
abbrev Coord := Fin 4 → ℤ

/-- Write a four-dimensional coordinate explicitly. -/
def coord (left right ghost₁ ghost₂ : ℤ) : Coord :=
  ![left, right, ghost₁, ghost₂]

@[simp]
theorem coord_zero : coord 0 0 0 0 = 0 := by
  funext i
  fin_cases i <;> rfl

/-- A full physical coordinate plane. -/
def full : Param ↪ Coord where
  toFun parameter := coord parameter.1 parameter.2 0 0
  inj' := by
    intro left right equal
    apply Prod.ext
    · simpa [coord] using congrFun equal (0 : Fin 4)
    · simpa [coord] using congrFun equal (1 : Fin 4)

/-- A left stack whose first base-three digit is fixed. -/
def leftCons (digit : ℤ) : Param ↪ Coord where
  toFun parameter :=
    coord (digit + radixInt * parameter.1) parameter.2 0 0
  inj' := by
    intro left right equal
    apply Prod.ext
    · have component := congrFun equal (0 : Fin 4)
      simp [coord] at component
      rcases component with component | radixZero
      · exact component
      · exact (ne_of_gt radixInt_pos radixZero).elim
    · simpa [coord] using congrFun equal (1 : Fin 4)

/-- The target chart after moving left: the old head is pushed onto the
right stack. -/
def movedLeft (digit : ℤ) : Param ↪ Coord where
  toFun parameter :=
    coord parameter.1 (digit + radixInt * parameter.2) 0 0
  inj' := by
    intro left right equal
    apply Prod.ext
    · simpa [coord] using congrFun equal (0 : Fin 4)
    · have component := congrFun equal (1 : Fin 4)
      simp [coord] at component
      rcases component with component | radixZero
      · exact component
      · exact (ne_of_gt radixInt_pos radixZero).elim

/-- An empty left stack, with the second chart parameter stored in a ghost
coordinate. -/
def leftEmpty : Param ↪ Coord where
  toFun parameter := coord 0 parameter.1 parameter.2 0
  inj' := by
    intro left right equal
    apply Prod.ext
    · simpa [coord] using congrFun equal (1 : Fin 4)
    · simpa [coord] using congrFun equal (2 : Fin 4)

/-- The target of a move from an empty left stack. -/
def movedLeftEmpty (digit : ℤ) : Param ↪ Coord where
  toFun parameter :=
    coord 0 (digit + radixInt * parameter.1) parameter.2 0
  inj' := by
    intro left right equal
    apply Prod.ext
    · have component := congrFun equal (1 : Fin 4)
      simp [coord] at component
      rcases component with component | radixZero
      · exact component
      · exact (ne_of_gt radixInt_pos radixZero).elim
    · simpa [coord] using congrFun equal (2 : Fin 4)

/-- An empty right stack, with the second chart parameter stored in a ghost
coordinate. -/
def rightEmpty : Param ↪ Coord where
  toFun parameter := coord parameter.1 0 parameter.2 0
  inj' := by
    intro left right equal
    apply Prod.ext
    · simpa [coord] using congrFun equal (0 : Fin 4)
    · simpa [coord] using congrFun equal (2 : Fin 4)

/-- The target of a move from an empty right stack. -/
def movedRightEmpty (digit : ℤ) : Param ↪ Coord where
  toFun parameter :=
    coord (digit + radixInt * parameter.1) 0 parameter.2 0
  inj' := by
    intro left right equal
    apply Prod.ext
    · have component := congrFun equal (0 : Fin 4)
      simp [coord] at component
      rcases component with component | radixZero
      · exact component
      · exact (ne_of_gt radixInt_pos radixZero).elim
    · simpa [coord] using congrFun equal (2 : Fin 4)

/-- A right stack whose first base-three digit is fixed. -/
def rightCons (digit : ℤ) : Param ↪ Coord where
  toFun parameter :=
    coord parameter.1 (digit + radixInt * parameter.2) 0 0
  inj' := movedLeft digit |>.injective

/-- The target chart after moving right. -/
def movedRight (digit : ℤ) : Param ↪ Coord where
  toFun parameter :=
    coord (digit + radixInt * parameter.1) parameter.2 0 0
  inj' := leftCons digit |>.injective

/-- A zero physical coordinate with a rank-two ghost chart. -/
def physicalZero : Param ↪ Coord where
  toFun parameter := coord 0 0 parameter.1 parameter.2
  inj' := by
    intro left right equal
    apply Prod.ext
    · simpa [coord] using congrFun equal (2 : Fin 4)
    · simpa [coord] using congrFun equal (3 : Fin 4)

private theorem full_eq_stackCoord
    {parameter : Param} {left right : List Symbol}
    (equal :
      full parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    parameter = (stackCode left, stackCode right) := by
  apply Prod.ext
  · simpa [full, coord] using congrFun equal (0 : Fin 4)
  · simpa [full, coord] using congrFun equal (1 : Fin 4)

private theorem leftEmpty_eq_stackCoord
    {parameter : Param} {left right : List Symbol}
    (equal :
      leftEmpty parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    left = [] ∧ parameter = (stackCode right, 0) := by
  have leftCode :
      stackCode left = stackCode ([] : List Symbol) := by
    simpa [leftEmpty, coord] using
      (congrFun equal (0 : Fin 4)).symm
  have parameterLeft :
      parameter.1 = stackCode right := by
    simpa [leftEmpty, coord] using congrFun equal (1 : Fin 4)
  have parameterRight : parameter.2 = 0 := by
    simpa [leftEmpty, coord] using congrFun equal (2 : Fin 4)
  exact
    ⟨stackCode_injective leftCode,
      Prod.ext parameterLeft parameterRight⟩

private theorem leftCons_eq_stackCoord
    {parameter : Param} {symbol : Symbol} {left right : List Symbol}
    (equal :
      leftCons (digitInt symbol) parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    ∃ rest,
      left = symbol :: rest ∧
        parameter = (stackCode rest, stackCode right) := by
  have leftCode :
      stackCode left =
        digitInt symbol + radixInt * parameter.1 := by
    simpa [leftCons, coord] using
      (congrFun equal (0 : Fin 4)).symm
  obtain ⟨rest, leftEqual, restCode⟩ :=
    stackCode_eq_digit_add leftCode
  refine ⟨rest, leftEqual, ?_⟩
  apply Prod.ext
  · exact restCode.symm
  · simpa [leftCons, coord] using congrFun equal (1 : Fin 4)

private theorem movedLeft_eq_stackCoord
    {parameter : Param} {symbol : Symbol} {left right : List Symbol}
    (equal :
      movedLeft (digitInt symbol) parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    ∃ rest,
      right = symbol :: rest ∧
        parameter = (stackCode left, stackCode rest) := by
  have rightCode :
      stackCode right =
        digitInt symbol + radixInt * parameter.2 := by
    simpa [movedLeft, coord] using
      (congrFun equal (1 : Fin 4)).symm
  obtain ⟨rest, rightEqual, restCode⟩ :=
    stackCode_eq_digit_add rightCode
  refine ⟨rest, rightEqual, ?_⟩
  apply Prod.ext
  · simpa [movedLeft, coord] using congrFun equal (0 : Fin 4)
  · exact restCode.symm

private theorem movedLeftEmpty_eq_stackCoord
    {parameter : Param} {symbol : Symbol} {left right : List Symbol}
    (equal :
      movedLeftEmpty (digitInt symbol) parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    ∃ rest,
      left = [] ∧ right = symbol :: rest ∧
        parameter = (stackCode rest, 0) := by
  have leftCode :
      stackCode left = stackCode ([] : List Symbol) := by
    simpa [movedLeftEmpty, coord] using
      (congrFun equal (0 : Fin 4)).symm
  have rightCode :
      stackCode right =
        digitInt symbol + radixInt * parameter.1 := by
    simpa [movedLeftEmpty, coord] using
      (congrFun equal (1 : Fin 4)).symm
  obtain ⟨rest, rightEqual, restCode⟩ :=
    stackCode_eq_digit_add rightCode
  have parameterRight : parameter.2 = 0 := by
    simpa [movedLeftEmpty, coord] using congrFun equal (2 : Fin 4)
  exact
    ⟨rest, stackCode_injective leftCode, rightEqual,
      Prod.ext restCode.symm parameterRight⟩

private theorem rightEmpty_eq_stackCoord
    {parameter : Param} {left right : List Symbol}
    (equal :
      rightEmpty parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    right = [] ∧ parameter = (stackCode left, 0) := by
  have rightCode :
      stackCode right = stackCode ([] : List Symbol) := by
    simpa [rightEmpty, coord] using
      (congrFun equal (1 : Fin 4)).symm
  have parameterLeft :
      parameter.1 = stackCode left := by
    simpa [rightEmpty, coord] using congrFun equal (0 : Fin 4)
  have parameterRight : parameter.2 = 0 := by
    simpa [rightEmpty, coord] using congrFun equal (2 : Fin 4)
  exact
    ⟨stackCode_injective rightCode,
      Prod.ext parameterLeft parameterRight⟩

private theorem movedRightEmpty_eq_stackCoord
    {parameter : Param} {symbol : Symbol} {left right : List Symbol}
    (equal :
      movedRightEmpty (digitInt symbol) parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    ∃ rest,
      left = symbol :: rest ∧ right = [] ∧
        parameter = (stackCode rest, 0) := by
  have leftCode :
      stackCode left =
        digitInt symbol + radixInt * parameter.1 := by
    simpa [movedRightEmpty, coord] using
      (congrFun equal (0 : Fin 4)).symm
  obtain ⟨rest, leftEqual, restCode⟩ :=
    stackCode_eq_digit_add leftCode
  have rightCode :
      stackCode right = stackCode ([] : List Symbol) := by
    simpa [movedRightEmpty, coord] using
      (congrFun equal (1 : Fin 4)).symm
  have parameterRight : parameter.2 = 0 := by
    simpa [movedRightEmpty, coord] using congrFun equal (2 : Fin 4)
  exact
    ⟨rest, leftEqual, stackCode_injective rightCode,
      Prod.ext restCode.symm parameterRight⟩

private theorem rightCons_eq_stackCoord
    {parameter : Param} {symbol : Symbol} {left right : List Symbol}
    (equal :
      rightCons (digitInt symbol) parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    ∃ rest,
      right = symbol :: rest ∧
        parameter = (stackCode left, stackCode rest) :=
  movedLeft_eq_stackCoord equal

private theorem movedRight_eq_stackCoord
    {parameter : Param} {symbol : Symbol} {left right : List Symbol}
    (equal :
      movedRight (digitInt symbol) parameter =
        coord (stackCode left) (stackCode right) 0 0) :
    ∃ rest,
      left = symbol :: rest ∧
        parameter = (stackCode rest, stackCode right) :=
  leftCons_eq_stackCoord equal

/-- One affine chart between two control-coordinate planes. -/
structure EdgeSpec where
  sourceControl : Control
  sourceCoord : Param ↪ Coord
  targetControl : Control
  targetCoord : Param ↪ Coord

/-- A harmless chart used for candidate cases not selected by the fixed
machine transition. -/
def idleSpec : EdgeSpec where
  sourceControl := .accepted
  sourceCoord := full
  targetControl := .accepted
  targetCoord := full

/-- The affine chart for a candidate run edge. -/
def runSpec (state : Q) (head : Symbol) (kind : RunKind) : EdgeSpec :=
  match universalTM0 state head with
  | none =>
      match kind with
      | .halt =>
          { sourceControl := .run state head
            sourceCoord := full
            targetControl := .cleanLeft
            targetCoord := full }
      | _ => idleSpec
  | some (nextState, statement) =>
      let nextSupported :=
        supportedTarget universalTM0 Support universalTM0_supports
          state head nextState
      match statement, kind with
      | .write written, .write =>
          { sourceControl := .run state head
            sourceCoord := full
            targetControl := .run nextSupported written
            targetCoord := full }
      | .move .left, .leftEmpty =>
          { sourceControl := .run state head
            sourceCoord := leftEmpty
            targetControl := .run nextSupported default
            targetCoord := movedLeftEmpty (digitInt head) }
      | .move .left, .leftCons neighbor =>
          { sourceControl := .run state head
            sourceCoord := leftCons (digitInt neighbor)
            targetControl := .run nextSupported neighbor
            targetCoord := movedLeft (digitInt head) }
      | .move .right, .rightEmpty =>
          { sourceControl := .run state head
            sourceCoord := rightEmpty
            targetControl := .run nextSupported default
            targetCoord := movedRightEmpty (digitInt head) }
      | .move .right, .rightCons neighbor =>
          { sourceControl := .run state head
            sourceCoord := rightCons (digitInt neighbor)
            targetControl := .run nextSupported neighbor
            targetCoord := movedRight (digitInt head) }
      | _, _ => idleSpec

/-- All fixed-machine and cleanup charts. -/
def spec : Edge → EdgeSpec
  | .run state head kind => runSpec state head kind
  | .cleanLeftEmpty =>
      { sourceControl := .cleanLeft
        sourceCoord := leftEmpty
        targetControl := .cleanRight
        targetCoord := leftEmpty }
  | .cleanLeftCons symbol =>
      { sourceControl := .cleanLeft
        sourceCoord := leftCons (digitInt symbol)
        targetControl := .cleanLeft
        targetCoord := full }
  | .cleanRightEmpty =>
      { sourceControl := .cleanRight
        sourceCoord := physicalZero
        targetControl := .accepted
        targetCoord := physicalZero }
  | .cleanRightCons symbol =>
      { sourceControl := .cleanRight
        sourceCoord := movedLeftEmpty (digitInt symbol)
        targetControl := .cleanRight
        targetCoord := leftEmpty }

/-- Vertices of the affine transition graph. -/
abbrev Vertex := Control × Coord

/-- Source vertex of one edge chart. -/
def source (edge : Edge) (parameter : Param) : Vertex :=
  ((spec edge).sourceControl, (spec edge).sourceCoord parameter)

/-- Target vertex of one edge chart. -/
def target (edge : Edge) (parameter : Param) : Vertex :=
  ((spec edge).targetControl, (spec edge).targetCoord parameter)

theorem source_injective (edge : Edge) :
    Function.Injective (source edge) := by
  intro left right equal
  exact (spec edge).sourceCoord.injective
    (congrArg Prod.snd equal)

theorem target_injective (edge : Edge) :
    Function.Injective (target edge) := by
  intro left right equal
  exact (spec edge).targetCoord.injective
    (congrArg Prod.snd equal)

/-- Encode a genuine cleanup-machine state as an affine vertex. -/
def encodeState : AffineMachine.State Symbol Support → Vertex
  | .run configuration =>
      (.run configuration.state configuration.head,
        coord (stackCode configuration.left) (stackCode configuration.right) 0 0)
  | .cleanLeft left right =>
      (.cleanLeft, coord (stackCode left) (stackCode right) 0 0)
  | .cleanRight right =>
      (.cleanRight, coord 0 (stackCode right) 0 0)
  | .accepted =>
      (.accepted, coord 0 0 0 0)

private theorem idle_target_eq_source
    {edge : Edge} {parameter : Param}
    (idle : spec edge = idleSpec) :
    target edge parameter = source edge parameter := by
  simp [source, target, idle, idleSpec]

private theorem halt_target_of_source
    (state : Q) (head : Symbol) (parameter : Param)
    {before : AffineMachine.State Symbol Support}
    (transition : universalTM0 state head = none)
    (sourceEqual :
      source (.run state head .halt) parameter = encodeState before) :
    ∃ after,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      target (.run state head .halt) parameter = encodeState after := by
  cases before with
  | run configuration =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      subst state
      subst head
      have parameterEqual :
          parameter =
            (stackCode configuration.left, stackCode configuration.right) :=
        full_eq_stackCoord <| by
          simpa [source, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd sourceEqual
      refine
        ⟨.cleanLeft configuration.left configuration.right, ?_, ?_⟩
      · simp [AffineMachine.step, configurationStep, transition]
      · subst parameter
        simp [target, spec, runSpec, transition, encodeState, full]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual

private theorem write_target_of_source
    (state : Q) (head written : Symbol) (nextState : MachineState)
    (parameter : Param)
    {before : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.write written))
    (sourceEqual :
      source (.run state head .write) parameter = encodeState before) :
    ∃ after,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      target (.run state head .write) parameter = encodeState after := by
  cases before with
  | run configuration =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      subst state
      subst head
      have parameterEqual :
          parameter =
            (stackCode configuration.left, stackCode configuration.right) :=
        full_eq_stackCoord <| by
          simpa [source, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd sourceEqual
      let nextSupported :=
        supportedTarget universalTM0 Support universalTM0_supports
          configuration.state configuration.head nextState
      let after : AffineMachine.State Symbol Support :=
        .run { configuration with
          state := nextSupported
          head := written }
      refine ⟨after, ?_, ?_⟩
      · simp [after, AffineMachine.step, configurationStep, transition,
          nextSupported]
      · subst parameter
        simp [after, target, spec, runSpec, transition, encodeState, full,
          nextSupported]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual

private theorem leftEmpty_target_of_source
    (state : Q) (head : Symbol) (nextState : MachineState)
    (parameter : Param)
    {before : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.move .left))
    (sourceEqual :
      source (.run state head .leftEmpty) parameter = encodeState before) :
    ∃ after,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      target (.run state head .leftEmpty) parameter = encodeState after := by
  cases before with
  | run configuration =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      subst state
      subst head
      obtain ⟨leftEqual, parameterEqual⟩ :=
        leftEmpty_eq_stackCoord <| by
          simpa [source, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd sourceEqual
      let nextSupported :=
        supportedTarget universalTM0 Support universalTM0_supports
          configuration.state configuration.head nextState
      let after : AffineMachine.State Symbol Support :=
        .run {
          state := nextSupported
          left := []
          head := default
          right := configuration.head :: configuration.right }
      refine ⟨after, ?_, ?_⟩
      · simp [after, AffineMachine.step, configurationStep, transition,
          leftEqual, nextSupported]
      · subst parameter
        simp [after, target, spec, runSpec, transition, encodeState,
          movedLeftEmpty, nextSupported]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual

private theorem leftCons_target_of_source
    (state : Q) (head neighbor : Symbol) (nextState : MachineState)
    (parameter : Param)
    {before : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.move .left))
    (sourceEqual :
      source (.run state head (.leftCons neighbor)) parameter =
        encodeState before) :
    ∃ after,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      target (.run state head (.leftCons neighbor)) parameter =
        encodeState after := by
  cases before with
  | run configuration =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      subst state
      subst head
      obtain ⟨remaining, leftEqual, parameterEqual⟩ :=
        leftCons_eq_stackCoord <| by
          simpa [source, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd sourceEqual
      let nextSupported :=
        supportedTarget universalTM0 Support universalTM0_supports
          configuration.state configuration.head nextState
      let after : AffineMachine.State Symbol Support :=
        .run {
          state := nextSupported
          left := remaining
          head := neighbor
          right := configuration.head :: configuration.right }
      refine ⟨after, ?_, ?_⟩
      · simp [after, AffineMachine.step, configurationStep, transition,
          leftEqual, nextSupported]
      · subst parameter
        simp [after, target, spec, runSpec, transition, encodeState,
          movedLeft, nextSupported]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual

private theorem rightEmpty_target_of_source
    (state : Q) (head : Symbol) (nextState : MachineState)
    (parameter : Param)
    {before : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.move .right))
    (sourceEqual :
      source (.run state head .rightEmpty) parameter = encodeState before) :
    ∃ after,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      target (.run state head .rightEmpty) parameter = encodeState after := by
  cases before with
  | run configuration =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      subst state
      subst head
      obtain ⟨rightEqual, parameterEqual⟩ :=
        rightEmpty_eq_stackCoord <| by
          simpa [source, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd sourceEqual
      let nextSupported :=
        supportedTarget universalTM0 Support universalTM0_supports
          configuration.state configuration.head nextState
      let after : AffineMachine.State Symbol Support :=
        .run {
          state := nextSupported
          left := configuration.head :: configuration.left
          head := default
          right := [] }
      refine ⟨after, ?_, ?_⟩
      · simp [after, AffineMachine.step, configurationStep, transition,
          rightEqual, nextSupported]
      · subst parameter
        simp [after, target, spec, runSpec, transition, encodeState,
          movedRightEmpty, nextSupported]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual

private theorem rightCons_target_of_source
    (state : Q) (head neighbor : Symbol) (nextState : MachineState)
    (parameter : Param)
    {before : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.move .right))
    (sourceEqual :
      source (.run state head (.rightCons neighbor)) parameter =
        encodeState before) :
    ∃ after,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      target (.run state head (.rightCons neighbor)) parameter =
        encodeState after := by
  cases before with
  | run configuration =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      subst state
      subst head
      obtain ⟨remaining, rightEqual, parameterEqual⟩ :=
        rightCons_eq_stackCoord <| by
          simpa [source, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd sourceEqual
      let nextSupported :=
        supportedTarget universalTM0 Support universalTM0_supports
          configuration.state configuration.head nextState
      let after : AffineMachine.State Symbol Support :=
        .run {
          state := nextSupported
          left := configuration.head :: configuration.left
          head := neighbor
          right := remaining }
      refine ⟨after, ?_, ?_⟩
      · simp [after, AffineMachine.step, configurationStep, transition,
          rightEqual, nextSupported]
      · subst parameter
        simp [after, target, spec, runSpec, transition, encodeState,
          movedRight, nextSupported]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst sourceEqual
      simp [source, spec, runSpec, transition, encodeState] at controlEqual

private theorem cleanup_target_of_source
    (edge : Edge) (parameter : Param)
    {before : AffineMachine.State Symbol Support}
    (notRun : ∀ state head kind, edge ≠ .run state head kind)
    (sourceEqual : source edge parameter = encodeState before) :
    ∃ after,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      target edge parameter = encodeState after := by
  cases edge with
  | run state head kind => exact (notRun state head kind rfl).elim
  | cleanLeftEmpty =>
      cases before with
      | run configuration =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
      | cleanLeft left right =>
          obtain ⟨leftEqual, parameterEqual⟩ :=
            leftEmpty_eq_stackCoord <| by
              simpa [source, spec, encodeState] using
                congrArg Prod.snd sourceEqual
          refine ⟨.cleanRight right, ?_, ?_⟩
          · simp [AffineMachine.step, leftEqual]
          · subst parameter
            simp [target, spec, encodeState, leftEmpty]
      | cleanRight right =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
      | accepted =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
  | cleanLeftCons symbol =>
      cases before with
      | run configuration =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
      | cleanLeft left right =>
          obtain ⟨remaining, leftEqual, parameterEqual⟩ :=
            leftCons_eq_stackCoord <| by
              simpa [source, spec, encodeState] using
                congrArg Prod.snd sourceEqual
          refine ⟨.cleanLeft remaining right, ?_, ?_⟩
          · simp [AffineMachine.step, leftEqual]
          · subst parameter
            simp [target, spec, encodeState, full]
      | cleanRight right =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
      | accepted =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
  | cleanRightEmpty =>
      cases before with
      | run configuration =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
      | cleanLeft left right =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
      | cleanRight right =>
          have rightCode :
              stackCode right = stackCode ([] : List Symbol) := by
            simpa [source, spec, encodeState, physicalZero, coord] using
              (congrFun (congrArg Prod.snd sourceEqual) (1 : Fin 4)).symm
          have parameterLeft : parameter.1 = 0 := by
            simpa [source, spec, encodeState, physicalZero, coord] using
              congrFun (congrArg Prod.snd sourceEqual) (2 : Fin 4)
          have parameterRight : parameter.2 = 0 := by
            simpa [source, spec, encodeState, physicalZero, coord] using
              congrFun (congrArg Prod.snd sourceEqual) (3 : Fin 4)
          have rightEqual := stackCode_injective rightCode
          have parameterEqual :
              parameter = (0, 0) :=
            Prod.ext parameterLeft parameterRight
          refine ⟨.accepted, ?_, ?_⟩
          · simp [AffineMachine.step, rightEqual]
          · subst parameter
            simp [target, spec, encodeState, physicalZero]
      | accepted =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
  | cleanRightCons symbol =>
      cases before with
      | run configuration =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
      | cleanLeft left right =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual
      | cleanRight right =>
          obtain ⟨remaining, _, rightEqual, parameterEqual⟩ :=
            movedLeftEmpty_eq_stackCoord
              (left := [])
              (right := right) <| by
                simpa [source, spec, encodeState] using
                  congrArg Prod.snd sourceEqual
          refine ⟨.cleanRight remaining, ?_, ?_⟩
          · simp [AffineMachine.step, rightEqual]
          · subst parameter
            simp [target, spec, encodeState, leftEmpty]
      | accepted =>
          have controlEqual := congrArg Prod.fst sourceEqual
          simp [source, spec, encodeState] at controlEqual

private theorem halt_source_of_target
    (state : Q) (head : Symbol) (parameter : Param)
    {after : AffineMachine.State Symbol Support}
    (transition : universalTM0 state head = none)
    (targetEqual :
      target (.run state head .halt) parameter = encodeState after) :
    ∃ before,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      source (.run state head .halt) parameter = encodeState before := by
  cases after with
  | run configuration =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | cleanLeft left right =>
      have parameterEqual :
          parameter = (stackCode left, stackCode right) :=
        full_eq_stackCoord <| by
          simpa [target, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd targetEqual
      let before : AffineMachine.State Symbol Support :=
        .run {
          state := state
          left := left
          head := head
          right := right }
      refine ⟨before, ?_, ?_⟩
      · simp [before, AffineMachine.step, configurationStep, transition]
      · subst parameter
        simp [before, source, spec, runSpec, transition, encodeState, full]
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual

private theorem write_source_of_target
    (state : Q) (head written : Symbol) (nextState : MachineState)
    (parameter : Param)
    {after : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.write written))
    (targetEqual :
      target (.run state head .write) parameter = encodeState after) :
    ∃ before,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      source (.run state head .write) parameter = encodeState before := by
  cases after with
  | run configuration =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      have parameterEqual :
          parameter =
            (stackCode configuration.left, stackCode configuration.right) :=
        full_eq_stackCoord <| by
          simpa [target, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd targetEqual
      let before : AffineMachine.State Symbol Support :=
        .run {
          state := state
          left := configuration.left
          head := head
          right := configuration.right }
      refine ⟨before, ?_, ?_⟩
      · simp [before, AffineMachine.step, configurationStep, transition]
        cases configuration
        simp_all
      · subst parameter
        simp [before, source, spec, runSpec, transition, encodeState, full]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual

private theorem leftEmpty_source_of_target
    (state : Q) (head : Symbol) (nextState : MachineState)
    (parameter : Param)
    {after : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.move .left))
    (targetEqual :
      target (.run state head .leftEmpty) parameter = encodeState after) :
    ∃ before,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      source (.run state head .leftEmpty) parameter = encodeState before := by
  cases after with
  | run configuration =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      obtain ⟨remaining, leftEqual, rightEqual, parameterEqual⟩ :=
        movedLeftEmpty_eq_stackCoord <| by
          simpa [target, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd targetEqual
      let before : AffineMachine.State Symbol Support :=
        .run {
          state := state
          left := []
          head := head
          right := remaining }
      refine ⟨before, ?_, ?_⟩
      · simp [before, AffineMachine.step, configurationStep, transition]
        cases configuration
        simp_all
      · subst parameter
        simp [before, source, spec, runSpec, transition, encodeState,
          leftEmpty]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual

private theorem leftCons_source_of_target
    (state : Q) (head neighbor : Symbol) (nextState : MachineState)
    (parameter : Param)
    {after : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.move .left))
    (targetEqual :
      target (.run state head (.leftCons neighbor)) parameter =
        encodeState after) :
    ∃ before,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      source (.run state head (.leftCons neighbor)) parameter =
        encodeState before := by
  cases after with
  | run configuration =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      obtain ⟨remaining, rightEqual, parameterEqual⟩ :=
        movedLeft_eq_stackCoord <| by
          simpa [target, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd targetEqual
      let before : AffineMachine.State Symbol Support :=
        .run {
          state := state
          left := neighbor :: configuration.left
          head := head
          right := remaining }
      refine ⟨before, ?_, ?_⟩
      · simp [before, AffineMachine.step, configurationStep, transition]
        cases configuration
        simp_all
      · subst parameter
        simp [before, source, spec, runSpec, transition, encodeState,
          leftCons]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual

private theorem rightEmpty_source_of_target
    (state : Q) (head : Symbol) (nextState : MachineState)
    (parameter : Param)
    {after : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.move .right))
    (targetEqual :
      target (.run state head .rightEmpty) parameter = encodeState after) :
    ∃ before,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      source (.run state head .rightEmpty) parameter = encodeState before := by
  cases after with
  | run configuration =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      obtain ⟨remaining, leftEqual, rightEqual, parameterEqual⟩ :=
        movedRightEmpty_eq_stackCoord <| by
          simpa [target, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd targetEqual
      let before : AffineMachine.State Symbol Support :=
        .run {
          state := state
          left := remaining
          head := head
          right := [] }
      refine ⟨before, ?_, ?_⟩
      · simp [before, AffineMachine.step, configurationStep, transition]
        cases configuration
        simp_all
      · subst parameter
        simp [before, source, spec, runSpec, transition, encodeState,
          rightEmpty]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual

private theorem rightCons_source_of_target
    (state : Q) (head neighbor : Symbol) (nextState : MachineState)
    (parameter : Param)
    {after : AffineMachine.State Symbol Support}
    (transition :
      universalTM0 state head =
        some (nextState, TM0.Stmt.move .right))
    (targetEqual :
      target (.run state head (.rightCons neighbor)) parameter =
        encodeState after) :
    ∃ before,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      source (.run state head (.rightCons neighbor)) parameter =
        encodeState before := by
  cases after with
  | run configuration =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
      obtain ⟨stateEqual, headEqual⟩ := controlEqual
      obtain ⟨remaining, leftEqual, parameterEqual⟩ :=
        movedRight_eq_stackCoord <| by
          simpa [target, spec, runSpec, transition, encodeState] using
            congrArg Prod.snd targetEqual
      let before : AffineMachine.State Symbol Support :=
        .run {
          state := state
          left := remaining
          head := head
          right := neighbor :: configuration.right }
      refine ⟨before, ?_, ?_⟩
      · simp [before, AffineMachine.step, configurationStep, transition]
        cases configuration
        simp_all
      · subst parameter
        simp [before, source, spec, runSpec, transition, encodeState,
          rightCons]
  | cleanLeft left right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | cleanRight right =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual
  | accepted =>
      have controlEqual := congrArg Prod.fst targetEqual
      simp [target, spec, runSpec, transition, encodeState] at controlEqual

private theorem cleanup_source_of_target
    (edge : Edge) (parameter : Param)
    {after : AffineMachine.State Symbol Support}
    (notRun : ∀ state head kind, edge ≠ .run state head kind)
    (targetEqual : target edge parameter = encodeState after) :
    ∃ before,
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after ∧
      source edge parameter = encodeState before := by
  cases edge with
  | run state head kind => exact (notRun state head kind rfl).elim
  | cleanLeftEmpty =>
      cases after with
      | run configuration =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | cleanLeft left right =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | cleanRight right =>
          obtain ⟨_, parameterEqual⟩ :=
            leftEmpty_eq_stackCoord
              (left := [])
              (right := right) <| by
                simpa [target, spec, encodeState] using
                  congrArg Prod.snd targetEqual
          refine ⟨.cleanLeft [] right, ?_, ?_⟩
          · simp [AffineMachine.step]
          · subst parameter
            simp [source, spec, encodeState, leftEmpty]
      | accepted =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
  | cleanLeftCons symbol =>
      cases after with
      | run configuration =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | cleanLeft left right =>
          have parameterEqual :
              parameter = (stackCode left, stackCode right) :=
            full_eq_stackCoord <| by
              simpa [target, spec, encodeState] using
                congrArg Prod.snd targetEqual
          refine ⟨.cleanLeft (symbol :: left) right, ?_, ?_⟩
          · simp [AffineMachine.step]
          · subst parameter
            simp [source, spec, encodeState, leftCons]
      | cleanRight right =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | accepted =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
  | cleanRightEmpty =>
      cases after with
      | run configuration =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | cleanLeft left right =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | cleanRight right =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | accepted =>
          have parameterLeft : parameter.1 = 0 := by
            simpa [target, spec, encodeState, physicalZero, coord] using
              congrFun (congrArg Prod.snd targetEqual) (2 : Fin 4)
          have parameterRight : parameter.2 = 0 := by
            simpa [target, spec, encodeState, physicalZero, coord] using
              congrFun (congrArg Prod.snd targetEqual) (3 : Fin 4)
          have parameterEqual :
              parameter = (0, 0) :=
            Prod.ext parameterLeft parameterRight
          refine ⟨.cleanRight [], ?_, ?_⟩
          · simp [AffineMachine.step]
          · subst parameter
            simp [source, spec, encodeState, physicalZero]
  | cleanRightCons symbol =>
      cases after with
      | run configuration =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | cleanLeft left right =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual
      | cleanRight right =>
          obtain ⟨_, parameterEqual⟩ :=
            leftEmpty_eq_stackCoord
              (left := [])
              (right := right) <| by
                simpa [target, spec, encodeState] using
                  congrArg Prod.snd targetEqual
          refine ⟨.cleanRight (symbol :: right), ?_, ?_⟩
          · simp [AffineMachine.step]
          · subst parameter
            simp [source, spec, encodeState, movedLeftEmpty]
      | accepted =>
          have controlEqual := congrArg Prod.fst targetEqual
          simp [target, spec, encodeState] at controlEqual

/-- Every operational transition of the cleanup-extended universal machine is
one of the finite affine charts. -/
theorem step_has_chart
    {before after : AffineMachine.State Symbol Support}
    (takesStep :
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after) :
    ∃ edge parameter,
      source edge parameter = encodeState before ∧
        target edge parameter = encodeState after := by
  cases before with
  | run configuration =>
      cases transition :
          universalTM0 configuration.state configuration.head with
      | none =>
          simp [AffineMachine.step, configurationStep, transition] at takesStep
          subst after
          refine ⟨.run configuration.state configuration.head .halt,
            (stackCode configuration.left, stackCode configuration.right), ?_, ?_⟩
          · simp [source, spec, runSpec, transition, encodeState, full]
          · simp [target, spec, runSpec, transition, encodeState, full]
      | some result =>
          rcases result with ⟨nextState, statement⟩
          cases statement with
          | write written =>
              simp [AffineMachine.step, configurationStep, transition] at takesStep
              subst after
              refine ⟨.run configuration.state configuration.head .write,
                (stackCode configuration.left, stackCode configuration.right),
                ?_, ?_⟩
              · simp [source, spec, runSpec, transition, encodeState, full]
              · simp [target, spec, runSpec, transition, encodeState, full]
          | move direction =>
              cases direction with
              | left =>
                  cases leftEq : configuration.left with
                  | nil =>
                      simp [AffineMachine.step, configurationStep, transition,
                        leftEq] at takesStep
                      subst after
                      refine
                        ⟨.run configuration.state configuration.head .leftEmpty,
                          (stackCode configuration.right, 0), ?_, ?_⟩
                      · simp [source, spec, runSpec, transition, encodeState,
                          leftEmpty, leftEq]
                      · simp [target, spec, runSpec, transition, encodeState,
                          movedLeftEmpty, stackCode]
                  | cons previous remaining =>
                      simp [AffineMachine.step, configurationStep, transition,
                        leftEq] at takesStep
                      subst after
                      refine
                        ⟨.run configuration.state configuration.head
                            (.leftCons previous),
                          (stackCode remaining, stackCode configuration.right),
                          ?_, ?_⟩
                      · simp [source, spec, runSpec, transition, encodeState,
                          leftCons, leftEq, digitInt]
                      · simp [target, spec, runSpec, transition, encodeState,
                          movedLeft, stackCode]
              | right =>
                  cases rightEq : configuration.right with
                  | nil =>
                      simp [AffineMachine.step, configurationStep, transition,
                        rightEq] at takesStep
                      subst after
                      refine
                        ⟨.run configuration.state configuration.head .rightEmpty,
                          (stackCode configuration.left, 0), ?_, ?_⟩
                      · simp [source, spec, runSpec, transition, encodeState,
                          rightEmpty, rightEq]
                      · simp [target, spec, runSpec, transition, encodeState,
                          movedRightEmpty, stackCode]
                  | cons following remaining =>
                      simp [AffineMachine.step, configurationStep, transition,
                        rightEq] at takesStep
                      subst after
                      refine
                        ⟨.run configuration.state configuration.head
                            (.rightCons following),
                          (stackCode configuration.left, stackCode remaining),
                          ?_, ?_⟩
                      · simp [source, spec, runSpec, transition, encodeState,
                          rightCons, rightEq, digitInt]
                      · simp [target, spec, runSpec, transition, encodeState,
                          movedRight, stackCode]
  | cleanLeft left right =>
      cases left with
      | nil =>
          simp [AffineMachine.step] at takesStep
          subst after
          refine ⟨.cleanLeftEmpty, (stackCode right, 0), ?_, ?_⟩
          · simp [source, spec, encodeState, leftEmpty]
          · simp [target, spec, encodeState, leftEmpty]
      | cons symbol remaining =>
          simp [AffineMachine.step] at takesStep
          subst after
          refine
            ⟨.cleanLeftCons symbol, (stackCode remaining, stackCode right),
              ?_, ?_⟩
          · simp [source, spec, encodeState, leftCons, digitInt, stackCode,
              radixInt]
          · simp [target, spec, encodeState, full]
  | cleanRight right =>
      cases right with
      | nil =>
          simp [AffineMachine.step] at takesStep
          subst after
          refine ⟨.cleanRightEmpty, (0, 0), ?_, ?_⟩
          · simp [source, spec, encodeState, physicalZero]
          · simp [target, spec, encodeState, physicalZero]
      | cons symbol remaining =>
          simp [AffineMachine.step] at takesStep
          subst after
          refine ⟨.cleanRightCons symbol, (stackCode remaining, 0), ?_, ?_⟩
          · simp [source, spec, encodeState, movedLeftEmpty, digitInt,
              stackCode, radixInt]
          · simp [target, spec, encodeState, leftEmpty]
  | accepted =>
      simp [AffineMachine.step] at takesStep

/-- An affine chart leaving an encoded state is either an idle self-edge or
the unique genuine cleanup-machine step. -/
theorem target_encoded_of_source_encoded
    {edge : Edge} {parameter : Param}
    {before : AffineMachine.State Symbol Support}
    (sourceEqual : source edge parameter = encodeState before) :
    target edge parameter = encodeState before ∨
      ∃ after,
        AffineMachine.step universalTM0 Support universalTM0_supports before =
          some after ∧
        target edge parameter = encodeState after := by
  cases edge with
  | run state head kind =>
      cases transition : universalTM0 state head with
      | none =>
          cases kind with
          | halt =>
              exact Or.inr <|
                halt_target_of_source state head parameter transition sourceEqual
          | write =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).trans sourceEqual
          | leftEmpty =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).trans sourceEqual
          | leftCons neighbor =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).trans sourceEqual
          | rightEmpty =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).trans sourceEqual
          | rightCons neighbor =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).trans sourceEqual
      | some result =>
          rcases result with ⟨nextState, statement⟩
          cases statement with
          | write written =>
              cases kind with
              | write =>
                  exact Or.inr <|
                    write_target_of_source state head written nextState
                      parameter transition sourceEqual
              | halt =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).trans sourceEqual
              | leftEmpty =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).trans sourceEqual
              | leftCons neighbor =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).trans sourceEqual
              | rightEmpty =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).trans sourceEqual
              | rightCons neighbor =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).trans sourceEqual
          | move direction =>
              cases direction with
              | left =>
                  cases kind with
                  | leftEmpty =>
                      exact Or.inr <|
                        leftEmpty_target_of_source state head nextState
                          parameter transition sourceEqual
                  | leftCons neighbor =>
                      exact Or.inr <|
                        leftCons_target_of_source state head neighbor nextState
                          parameter transition sourceEqual
                  | halt =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).trans sourceEqual
                  | write =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).trans sourceEqual
                  | rightEmpty =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).trans sourceEqual
                  | rightCons neighbor =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).trans sourceEqual
              | right =>
                  cases kind with
                  | rightEmpty =>
                      exact Or.inr <|
                        rightEmpty_target_of_source state head nextState
                          parameter transition sourceEqual
                  | rightCons neighbor =>
                      exact Or.inr <|
                        rightCons_target_of_source state head neighbor nextState
                          parameter transition sourceEqual
                  | halt =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).trans sourceEqual
                  | write =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).trans sourceEqual
                  | leftEmpty =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).trans sourceEqual
                  | leftCons neighbor =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).trans sourceEqual
  | cleanLeftEmpty =>
      exact Or.inr <|
        cleanup_target_of_source .cleanLeftEmpty parameter
          (by intro state head kind; simp) sourceEqual
  | cleanLeftCons symbol =>
      exact Or.inr <|
        cleanup_target_of_source (.cleanLeftCons symbol) parameter
          (by intro state head kind; simp) sourceEqual
  | cleanRightEmpty =>
      exact Or.inr <|
        cleanup_target_of_source .cleanRightEmpty parameter
          (by intro state head kind; simp) sourceEqual
  | cleanRightCons symbol =>
      exact Or.inr <|
        cleanup_target_of_source (.cleanRightCons symbol) parameter
          (by intro state head kind; simp) sourceEqual

/-- An affine chart entering an encoded state is either an idle self-edge or
the reverse of a genuine cleanup-machine step. -/
theorem source_encoded_of_target_encoded
    {edge : Edge} {parameter : Param}
    {after : AffineMachine.State Symbol Support}
    (targetEqual : target edge parameter = encodeState after) :
    source edge parameter = encodeState after ∨
      ∃ before,
        AffineMachine.step universalTM0 Support universalTM0_supports before =
          some after ∧
        source edge parameter = encodeState before := by
  cases edge with
  | run state head kind =>
      cases transition : universalTM0 state head with
      | none =>
          cases kind with
          | halt =>
              exact Or.inr <|
                halt_source_of_target state head parameter transition targetEqual
          | write =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).symm.trans targetEqual
          | leftEmpty =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).symm.trans targetEqual
          | leftCons neighbor =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).symm.trans targetEqual
          | rightEmpty =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).symm.trans targetEqual
          | rightCons neighbor =>
              exact Or.inl <|
                (idle_target_eq_source <| by
                  simp [spec, runSpec, transition]).symm.trans targetEqual
      | some result =>
          rcases result with ⟨nextState, statement⟩
          cases statement with
          | write written =>
              cases kind with
              | write =>
                  exact Or.inr <|
                    write_source_of_target state head written nextState
                      parameter transition targetEqual
              | halt =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).symm.trans targetEqual
              | leftEmpty =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).symm.trans targetEqual
              | leftCons neighbor =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).symm.trans targetEqual
              | rightEmpty =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).symm.trans targetEqual
              | rightCons neighbor =>
                  exact Or.inl <|
                    (idle_target_eq_source <| by
                      simp [spec, runSpec, transition]).symm.trans targetEqual
          | move direction =>
              cases direction with
              | left =>
                  cases kind with
                  | leftEmpty =>
                      exact Or.inr <|
                        leftEmpty_source_of_target state head nextState
                          parameter transition targetEqual
                  | leftCons neighbor =>
                      exact Or.inr <|
                        leftCons_source_of_target state head neighbor nextState
                          parameter transition targetEqual
                  | halt =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).symm.trans targetEqual
                  | write =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).symm.trans targetEqual
                  | rightEmpty =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).symm.trans targetEqual
                  | rightCons neighbor =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).symm.trans targetEqual
              | right =>
                  cases kind with
                  | rightEmpty =>
                      exact Or.inr <|
                        rightEmpty_source_of_target state head nextState
                          parameter transition targetEqual
                  | rightCons neighbor =>
                      exact Or.inr <|
                        rightCons_source_of_target state head neighbor nextState
                          parameter transition targetEqual
                  | halt =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).symm.trans targetEqual
                  | write =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).symm.trans targetEqual
                  | leftEmpty =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).symm.trans targetEqual
                  | leftCons neighbor =>
                      exact Or.inl <|
                        (idle_target_eq_source <| by
                          simp [spec, runSpec, transition]).symm.trans targetEqual
  | cleanLeftEmpty =>
      exact Or.inr <|
        cleanup_source_of_target .cleanLeftEmpty parameter
          (by intro state head kind; simp) targetEqual
  | cleanLeftCons symbol =>
      exact Or.inr <|
        cleanup_source_of_target (.cleanLeftCons symbol) parameter
          (by intro state head kind; simp) targetEqual
  | cleanRightEmpty =>
      exact Or.inr <|
        cleanup_source_of_target .cleanRightEmpty parameter
          (by intro state head kind; simp) targetEqual
  | cleanRightCons symbol =>
      exact Or.inr <|
        cleanup_source_of_target (.cleanRightCons symbol) parameter
          (by intro state head kind; simp) targetEqual

/-- Undirected adjacency generated by the finite family of affine charts. -/
def Adjacent (left right : Vertex) : Prop :=
  ∃ edge parameter,
    (source edge parameter = left ∧ target edge parameter = right) ∨
      (source edge parameter = right ∧ target edge parameter = left)

/-- Connectedness in the finite affine-chart graph. -/
def Connected (left right : Vertex) : Prop :=
  Relation.ReflTransGen Adjacent left right

/-- Every chart edge incident to a genuine encoding stays among genuine
encodings and is either a machine edge or an idle loop. -/
theorem adjacent_encoded
    {state : AffineMachine.State Symbol Support} {vertex : Vertex}
    (adjacent : Adjacent (encodeState state) vertex) :
    vertex = encodeState state ∨
      ∃ next,
        AffineMachine.Adjacent
          (AffineMachine.step universalTM0 Support universalTM0_supports)
          state next ∧
        vertex = encodeState next := by
  obtain ⟨edge, parameter, forward | backward⟩ := adjacent
  · obtain ⟨sourceEqual, targetEqual⟩ := forward
    obtain idle | step :=
      target_encoded_of_source_encoded sourceEqual
    · exact Or.inl (targetEqual.symm.trans idle)
    · obtain ⟨next, takesStep, targetEncoded⟩ := step
      exact Or.inr
        ⟨next, Or.inl takesStep, targetEqual.symm.trans targetEncoded⟩
  · obtain ⟨sourceEqual, targetEqual⟩ := backward
    obtain idle | step :=
      source_encoded_of_target_encoded targetEqual
    · exact Or.inl (sourceEqual.symm.trans idle)
    · obtain ⟨previous, takesStep, sourceEncoded⟩ := step
      exact Or.inr
        ⟨previous, Or.inr takesStep,
          sourceEqual.symm.trans sourceEncoded⟩

/-- A chart path beginning at a genuine encoding stays in the encoded
cleanup-machine component. -/
theorem connected_encoded
    {start : AffineMachine.State Symbol Support} {vertex : Vertex}
    (connected : Connected (encodeState start) vertex) :
    ∃ state,
      vertex = encodeState state ∧
        AffineMachine.Connected
          (AffineMachine.step universalTM0 Support universalTM0_supports)
          start state := by
  induction connected with
  | refl =>
      exact ⟨start, rfl, Relation.ReflTransGen.refl⟩
  | @tail middle final connectedMiddle adjacentMiddle ih =>
      obtain ⟨state, middleEqual, machineConnected⟩ := ih
      have adjacentEncoded :
          Adjacent (encodeState state) final := by
        rw [← middleEqual]
        exact adjacentMiddle
      obtain idle | step := adjacent_encoded adjacentEncoded
      · exact ⟨state, idle, machineConnected⟩
      · obtain ⟨next, machineAdjacent, finalEqual⟩ := step
        exact
          ⟨next, finalEqual,
            machineConnected.tail machineAdjacent⟩

/-- A forward cleanup-machine step is an affine-chart edge. -/
theorem adjacent_of_step
    {before after : AffineMachine.State Symbol Support}
    (takesStep :
      AffineMachine.step universalTM0 Support universalTM0_supports before =
        some after) :
    Adjacent (encodeState before) (encodeState after) := by
  obtain ⟨edge, parameter, sourceEqual, targetEqual⟩ :=
    step_has_chart takesStep
  exact ⟨edge, parameter, Or.inl ⟨sourceEqual, targetEqual⟩⟩

/-- Undirected cleanup-machine adjacency maps into affine-chart adjacency. -/
theorem adjacent_of_machineAdjacent
    {left right : AffineMachine.State Symbol Support}
    (adjacent :
      AffineMachine.Adjacent
        (AffineMachine.step universalTM0 Support universalTM0_supports)
        left right) :
    Adjacent (encodeState left) (encodeState right) := by
  rcases adjacent with forward | backward
  · exact adjacent_of_step forward
  · obtain ⟨edge, parameter, sourceEqual, targetEqual⟩ :=
      step_has_chart backward
    exact ⟨edge, parameter, Or.inr ⟨sourceEqual, targetEqual⟩⟩

/-- Cleanup-machine connectedness maps into affine-chart connectedness. -/
theorem connected_of_machineConnected
    {left right : AffineMachine.State Symbol Support}
    (connected :
      AffineMachine.Connected
        (AffineMachine.step universalTM0 Support universalTM0_supports)
        left right) :
    Connected (encodeState left) (encodeState right) :=
  Relation.ReflTransGen.lift encodeState
    (fun _ _ adjacent => adjacent_of_machineAdjacent adjacent) connected

/-- The finite-list initial state of the fixed universal machine. -/
def initialState (code : Nat.Partrec.Code) :
    AffineMachine.State Symbol Support :=
  .run <|
    FiniteConfiguration.initial universalTM0 Support universalTM0_supports
      (universalTM0Input code)

/-- The canonical accepted vertex. -/
def acceptedVertex : Vertex :=
  encodeState (.accepted : AffineMachine.State Symbol Support)

private theorem accepted_unique_terminal
    (state : AffineMachine.State Symbol Support)
    (terminal :
      AffineMachine.step universalTM0 Support universalTM0_supports state =
        none) :
    state = .accepted := by
  cases state with
  | run configuration =>
      cases transition :
          configurationStep universalTM0 Support universalTM0_supports
            configuration <;>
        simp [AffineMachine.step, transition] at terminal
  | cleanLeft left right =>
      cases left <;> simp [AffineMachine.step] at terminal
  | cleanRight right =>
      cases right <;> simp [AffineMachine.step] at terminal
  | accepted => rfl

/-- The extended finite-list machine has the original universal halting
domain. -/
theorem extended_dom_iff (code : Nat.Partrec.Code) :
    (StateTransition.eval
      (AffineMachine.step universalTM0 Support universalTM0_supports)
      (initialState code)).Dom ↔
        (Nat.Partrec.Code.eval code 0).Dom := by
  exact
    (AffineMachine.eval_dom_iff universalTM0 Support universalTM0_supports
      (FiniteConfiguration.initial universalTM0 Support universalTM0_supports
        (universalTM0Input code))).trans <|
      (FiniteConfiguration.eval_dom_iff universalTM0 Support
        universalTM0_supports (universalTM0Input code)).trans <|
          universalTM0_dom_iff code

/-- Halting supplies a path from the encoded input to the canonical affine
accept vertex. -/
theorem connected_of_halting (code : Nat.Partrec.Code)
    (halts : (Nat.Partrec.Code.eval code 0).Dom) :
    Connected (encodeState (initialState code)) acceptedVertex := by
  have machineConnected :
      AffineMachine.Connected
        (AffineMachine.step universalTM0 Support universalTM0_supports)
        (initialState code) .accepted :=
    (AffineMachine.connected_terminal_iff_dom
      (by simp [AffineMachine.step])
      accepted_unique_terminal).mpr
        ((extended_dom_iff code).mpr halts)
  exact connected_of_machineConnected machineConnected

/-- Conversely, affine connectedness to the canonical accept vertex forces
termination of the original universal computation. -/
theorem halting_of_connected (code : Nat.Partrec.Code)
    (connected :
      Connected (encodeState (initialState code)) acceptedVertex) :
    (Nat.Partrec.Code.eval code 0).Dom := by
  obtain ⟨state, acceptedEqual, machineConnected⟩ :=
    connected_encoded connected
  have stateEqual :
      state = (.accepted : AffineMachine.State Symbol Support) := by
    cases state with
    | run configuration =>
        have controlEqual := congrArg Prod.fst acceptedEqual
        simp [acceptedVertex, encodeState] at controlEqual
    | cleanLeft left right =>
        have controlEqual := congrArg Prod.fst acceptedEqual
        simp [acceptedVertex, encodeState] at controlEqual
    | cleanRight right =>
        have controlEqual := congrArg Prod.fst acceptedEqual
        simp [acceptedVertex, encodeState] at controlEqual
    | accepted => rfl
  subst state
  have extendedDom :
      (StateTransition.eval
        (AffineMachine.step universalTM0 Support universalTM0_supports)
        (initialState code)).Dom :=
    (AffineMachine.connected_terminal_iff_dom
      (by simp [AffineMachine.step])
      accepted_unique_terminal).mp machineConnected
  exact (extended_dom_iff code).mp extendedDom

theorem halting_iff_connected (code : Nat.Partrec.Code) :
    (Nat.Partrec.Code.eval code 0).Dom ↔
      Connected (encodeState (initialState code)) acceptedVertex :=
  ⟨connected_of_halting code, halting_of_connected code⟩

end

end Submission.AffineGraph
