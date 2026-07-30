import Submission.Helpers
import Mathlib.Computability.TuringMachine.PostTuringMachine

open Turing

namespace Submission.MachineRules

/-- The finite alphabet used to write a Turing-machine configuration as a
word. A configuration has exactly one state letter, or one cleanup letter
after the machine has terminated. -/
inductive MachineLetter (Γ Q : Type*)
  | leftBoundary
  | tape (symbol : Γ)
  | state (label : Q)
  | cleanup
  | rightBoundary
  deriving DecidableEq, Fintype

/-- Machine states restricted to a finite support. -/
abbrev SupportedState {Λ : Type*} (support : Finset Λ) := {q // q ∈ support}

section

variable {Γ Λ : Type*}
variable [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable [Inhabited Λ] [DecidableEq Λ]
variable (machine : TM0.Machine Γ Λ) (support : Finset Λ)
variable (supports : TM0.Supports machine (support : Set Λ))

private abbrev Q (support : Finset Λ) := SupportedState support
private abbrev Letter (Γ : Type*) (support : Finset Λ) :=
  MachineLetter Γ (Q support)
private abbrev GeneratorCount (Γ : Type*) [Fintype Γ] (support : Finset Λ) :=
  Fintype.card (Letter Γ support)
private abbrev MachineWord (Γ : Type*) [Fintype Γ] (support : Finset Λ) :=
  Helpers.Word (GeneratorCount Γ support)
private abbrev MachineRule (Γ : Type*) [Fintype Γ] (support : Finset Λ) :=
  Helpers.WordRule (GeneratorCount Γ support)

/-- A canonical numbering of the finite machine alphabet. -/
noncomputable def letterEquiv :
    Letter Γ support ≃ Fin (GeneratorCount Γ support) :=
  Fintype.equivFin _

/-- A positive group letter corresponding to a machine symbol. -/
noncomputable def atom (letter : Letter Γ support) :
    Fin (GeneratorCount Γ support) × Bool :=
  (letterEquiv support letter, true)

/-- Encode a list of tape symbols as positive group letters. -/
noncomputable def tapeWord (symbols : List Γ) : MachineWord Γ support :=
  symbols.map fun symbol => atom support (.tape symbol)

/-- The finite-list presentation of a supported TM0 configuration. The
left list is stored nearest-cell first, as in `Turing.Tape.left`. -/
structure Configuration (Γ : Type*) (support : Finset Λ) where
  state : Q support
  left : List Γ
  head : Γ
  right : List Γ

/-- Interpret a finite-list configuration as Mathlib's quotient-based tape
configuration. -/
def Configuration.toTM0 (configuration : Configuration Γ support) : TM0.Cfg Γ Λ :=
  ⟨configuration.state,
    Tape.mk' (ListBlank.mk configuration.left)
      (ListBlank.mk (configuration.head :: configuration.right))⟩

/-- Retain the support proof on a transition target without making the
definition of a machine step depend on the equation produced by its match. -/
noncomputable def supportedTarget (state : Q support) (symbol : Γ) (nextState : Λ) :
    Q support := by
  classical
  exact if transition :
      ∃ statement, (nextState, statement) ∈ machine state symbol then
    ⟨nextState, supports.2 transition.choose_spec state.2⟩
  else
    state

/-- One step of the finitely supported machine, retaining the support proof
on the target state. -/
noncomputable def configurationStep (configuration : Configuration Γ support) :
    Option (Configuration Γ support) :=
  match machine configuration.state configuration.head with
  | none => none
  | some (nextState, statement) =>
      let nextSupported :=
        supportedTarget machine support supports configuration.state
          configuration.head nextState
      match statement with
      | .write symbol =>
          some { configuration with state := nextSupported, head := symbol }
      | .move .left =>
          match configuration.left with
          | [] =>
              some {
                state := nextSupported
                left := []
                head := default
                right := configuration.head :: configuration.right }
          | symbol :: remaining =>
              some {
                state := nextSupported
                left := remaining
                head := symbol
                right := configuration.head :: configuration.right }
      | .move .right =>
          match configuration.right with
          | [] =>
              some {
                state := nextSupported
                left := configuration.head :: configuration.left
                head := default
                right := [] }
          | symbol :: remaining =>
              some {
                state := nextSupported
                left := configuration.head :: configuration.left
                head := symbol
                right := remaining }

/-- The portion of a configuration word strictly to the left of its state
letter. -/
noncomputable def leftContext (configuration : Configuration Γ support) :
    MachineWord Γ support :=
  [atom support .leftBoundary] ++ tapeWord support configuration.left.reverse

/-- The portion of a configuration word strictly to the right of the symbol
under the tape head. -/
noncomputable def rightContext (configuration : Configuration Γ support) :
    MachineWord Γ support :=
  tapeWord support configuration.right ++ [atom support .rightBoundary]

/-- Encode a supported finite-list configuration as a group word. -/
noncomputable def encodeConfiguration (configuration : Configuration Γ support) :
    MachineWord Γ support :=
  leftContext support configuration ++
    [atom support (.state configuration.state), atom support (.tape configuration.head)] ++
      rightContext support configuration

/-- Encode a local string equation as a word rule. -/
noncomputable def makeRule (source target : List (Letter Γ support)) :
    MachineRule Γ support :=
  (source.map (atom support), target.map (atom support))

/-- The finitely many local rules for one supported state and one scanned
symbol. -/
noncomputable def localRules (state : Q support) (symbol : Γ) :
    Finset (MachineRule Γ support) :=
  match machine state symbol with
  | none =>
      {makeRule support [.state state, .tape symbol] [.cleanup, .tape symbol]}
  | some (nextState, statement) =>
      let nextSupported :=
        supportedTarget machine support supports state symbol nextState
      match statement with
      | .write written =>
          {makeRule support
            [.state state, .tape symbol]
            [.state nextSupported, .tape written]}
      | .move .left =>
          (Finset.univ.image fun previous : Γ =>
            makeRule support
              [.tape previous, .state state, .tape symbol]
              [.state nextSupported, .tape previous, .tape symbol]) ∪
            {makeRule support
              [.leftBoundary, .state state, .tape symbol]
              [.leftBoundary, .state nextSupported, .tape default, .tape symbol]}
      | .move .right =>
          (Finset.univ.image fun following : Γ =>
            makeRule support
              [.state state, .tape symbol, .tape following]
              [.tape symbol, .state nextSupported, .tape following]) ∪
            {makeRule support
              [.state state, .tape symbol, .rightBoundary]
              [.tape symbol, .state nextSupported, .tape default, .rightBoundary]}

/-- All transition and halt-entry rules for the supported machine. -/
noncomputable def transitionRules : Finset (MachineRule Γ support) :=
  Finset.univ.biUnion fun state : Q support =>
    Finset.univ.biUnion fun symbol : Γ => localRules machine support supports state symbol

/-- Cleanup rules erase the finite tape after a genuine machine halt. -/
noncomputable def cleanupRules : Finset (MachineRule Γ support) :=
  (Finset.univ.image fun symbol : Γ =>
    makeRule support [.tape symbol, .cleanup] [.cleanup]) ∪
  (Finset.univ.image fun symbol : Γ =>
    makeRule support [.cleanup, .tape symbol] [.cleanup])

/-- The complete finite contextual rule set compiled from the supported
machine. -/
noncomputable def rules : Set (MachineRule Γ support) :=
  ↑(transitionRules machine support supports ∪ cleanupRules support)

omit [DecidableEq Γ] [DecidableEq Λ] in
/-- The compiled machine rule set is finite. -/
theorem rules_finite : (rules machine support supports).Finite :=
  (transitionRules machine support supports ∪ cleanupRules support).finite_toSet

/-- The single normal form reached by every cleanup phase. -/
noncomputable def haltWord : MachineWord Γ support :=
  [atom support .leftBoundary, atom support .cleanup, atom support .rightBoundary]

omit [DecidableEq Γ] [DecidableEq Λ] in
private theorem localRule_mem_rules {state : Q support} {symbol : Γ}
    {rule : MachineRule Γ support}
    (rule_mem : rule ∈ localRules machine support supports state symbol) :
    rule ∈ rules machine support supports := by
  change rule ∈ transitionRules machine support supports ∪ cleanupRules support
  apply Finset.mem_union_left
  rw [transitionRules, Finset.mem_biUnion]
  exact ⟨state, Finset.mem_univ _, Finset.mem_biUnion.mpr
    ⟨symbol, Finset.mem_univ _, rule_mem⟩⟩

omit [DecidableEq Γ] [DecidableEq Λ] in
private theorem cleanupLeftRule_mem_rules (symbol : Γ) :
    makeRule support [.tape symbol, .cleanup] [.cleanup] ∈
      rules machine support supports := by
  change makeRule support [.tape symbol, .cleanup] [.cleanup] ∈
    transitionRules machine support supports ∪ cleanupRules support
  apply Finset.mem_union_right
  rw [cleanupRules, Finset.mem_union]
  exact Or.inl (Finset.mem_image.mpr ⟨symbol, Finset.mem_univ _, rfl⟩)

omit [DecidableEq Γ] [DecidableEq Λ] in
private theorem cleanupRightRule_mem_rules (symbol : Γ) :
    makeRule support [.cleanup, .tape symbol] [.cleanup] ∈
      rules machine support supports := by
  change makeRule support [.cleanup, .tape symbol] [.cleanup] ∈
    transitionRules machine support supports ∪ cleanupRules support
  apply Finset.mem_union_right
  rw [cleanupRules, Finset.mem_union]
  exact Or.inr (Finset.mem_image.mpr ⟨symbol, Finset.mem_univ _, rfl⟩)

omit [DecidableEq Γ] [DecidableEq Λ] in
/-- Every concrete machine step is one contextual application of a compiled
word rule. -/
theorem step_ruleStep {source target : Configuration Γ support}
    (step : target ∈ configurationStep machine support supports source) :
    Submission.Helpers.RuleStep (rules machine support supports)
      (encodeConfiguration support source) (encodeConfiguration support target) := by
  classical
  cases transition : machine source.state source.head with
  | none =>
      simp [configurationStep, transition] at step
  | some result =>
      rcases result with ⟨nextState, statement⟩
      let nextSupported : Q support :=
        supportedTarget machine support supports source.state source.head nextState
      cases statement with
      | write written =>
          have target_eq :
              target = { source with state := nextSupported, head := written } := by
            simpa [configurationStep, transition, nextSupported] using step.symm
          subst target
          refine ⟨leftContext support source, rightContext support source,
            (makeRule support
              [.state source.state, .tape source.head]
              [.state nextSupported, .tape written]).1,
            (makeRule support
              [.state source.state, .tape source.head]
              [.state nextSupported, .tape written]).2,
            localRule_mem_rules machine support supports
              (state := source.state) (symbol := source.head) ?_, ?_, ?_⟩
          · simp [localRules, transition, nextSupported]
          · simp [makeRule, encodeConfiguration]
          · simp [makeRule, encodeConfiguration, leftContext, rightContext]
      | move direction =>
          cases direction with
          | left =>
              cases left_eq : source.left with
              | nil =>
                  have target_eq :
                      target = {
                        state := nextSupported
                        left := []
                        head := default
                        right := source.head :: source.right } := by
                    simpa [configurationStep, transition, left_eq, nextSupported] using step.symm
                  subst target
                  refine ⟨[], rightContext support source,
                    (makeRule support
                      [.leftBoundary, .state source.state, .tape source.head]
                      [.leftBoundary, .state nextSupported, .tape default,
                        .tape source.head]).1,
                    (makeRule support
                      [.leftBoundary, .state source.state, .tape source.head]
                      [.leftBoundary, .state nextSupported, .tape default,
                        .tape source.head]).2,
                    localRule_mem_rules machine support supports
                      (state := source.state) (symbol := source.head) ?_, ?_, ?_⟩
                  · simp [localRules, transition, nextSupported]
                  · simp [makeRule, encodeConfiguration, leftContext, left_eq, tapeWord]
                  · simp [makeRule, encodeConfiguration, leftContext, rightContext, tapeWord]
              | cons previous remaining =>
                  have target_eq :
                      target = {
                        state := nextSupported
                        left := remaining
                        head := previous
                        right := source.head :: source.right } := by
                    simpa [configurationStep, transition, left_eq, nextSupported] using step.symm
                  subst target
                  let pre : MachineWord Γ support :=
                    [atom support .leftBoundary] ++ tapeWord support remaining.reverse
                  refine ⟨pre, rightContext support source,
                    (makeRule support
                      [.tape previous, .state source.state, .tape source.head]
                      [.state nextSupported, .tape previous, .tape source.head]).1,
                    (makeRule support
                      [.tape previous, .state source.state, .tape source.head]
                      [.state nextSupported, .tape previous, .tape source.head]).2,
                    localRule_mem_rules machine support supports
                      (state := source.state) (symbol := source.head) ?_, ?_, ?_⟩
                  · simp [localRules, transition, nextSupported]
                  · simp [pre, makeRule, encodeConfiguration, leftContext, left_eq,
                      tapeWord, List.map_append, List.append_assoc]
                  · simp [pre, makeRule, encodeConfiguration, leftContext, rightContext,
                      tapeWord, List.append_assoc]
          | right =>
              cases right_eq : source.right with
              | nil =>
                  have target_eq :
                      target = {
                        state := nextSupported
                        left := source.head :: source.left
                        head := default
                        right := [] } := by
                    simpa [configurationStep, transition, right_eq, nextSupported] using step.symm
                  subst target
                  refine ⟨leftContext support source, [],
                    (makeRule support
                      [.state source.state, .tape source.head, .rightBoundary]
                      [.tape source.head, .state nextSupported, .tape default,
                        .rightBoundary]).1,
                    (makeRule support
                      [.state source.state, .tape source.head, .rightBoundary]
                      [.tape source.head, .state nextSupported, .tape default,
                        .rightBoundary]).2,
                    localRule_mem_rules machine support supports
                      (state := source.state) (symbol := source.head) ?_, ?_, ?_⟩
                  · simp [localRules, transition, nextSupported]
                  · simp [makeRule, encodeConfiguration, rightContext, right_eq, tapeWord]
                  · simp [makeRule, encodeConfiguration, leftContext, rightContext,
                      tapeWord, List.map_append, List.append_assoc]
              | cons following remaining =>
                  have target_eq :
                      target = {
                        state := nextSupported
                        left := source.head :: source.left
                        head := following
                        right := remaining } := by
                    simpa [configurationStep, transition, right_eq, nextSupported] using step.symm
                  subst target
                  let post : MachineWord Γ support :=
                    tapeWord support remaining ++ [atom support .rightBoundary]
                  refine ⟨leftContext support source, post,
                    (makeRule support
                      [.state source.state, .tape source.head, .tape following]
                      [.tape source.head, .state nextSupported, .tape following]).1,
                    (makeRule support
                      [.state source.state, .tape source.head, .tape following]
                      [.tape source.head, .state nextSupported, .tape following]).2,
                    localRule_mem_rules machine support supports
                      (state := source.state) (symbol := source.head) ?_, ?_, ?_⟩
                  · simp [localRules, transition, nextSupported]
                  · simp [post, makeRule, encodeConfiguration, rightContext, right_eq, tapeWord]
                  · simp [post, makeRule, encodeConfiguration, leftContext, rightContext,
                      tapeWord, List.append_assoc]

/-- The word used during cleanup. `left` remains nearest-cell first, while
`cells` starts with the current head symbol. -/
noncomputable def cleanupWord (left cells : List Γ) : MachineWord Γ support :=
  [atom support .leftBoundary] ++ tapeWord support left.reverse ++
    [atom support .cleanup] ++ tapeWord support cells ++
      [atom support .rightBoundary]

omit [DecidableEq Γ] [DecidableEq Λ] in
private theorem haltEntry_ruleStep (configuration : Configuration Γ support)
    (terminal : machine configuration.state configuration.head = none) :
    Submission.Helpers.RuleStep (rules machine support supports)
      (encodeConfiguration support configuration)
      (cleanupWord support configuration.left
        (configuration.head :: configuration.right)) := by
  refine ⟨leftContext support configuration, rightContext support configuration,
    (makeRule support
      [.state configuration.state, .tape configuration.head]
      [.cleanup, .tape configuration.head]).1,
    (makeRule support
      [.state configuration.state, .tape configuration.head]
      [.cleanup, .tape configuration.head]).2,
    localRule_mem_rules machine support supports
      (state := configuration.state) (symbol := configuration.head) ?_, ?_, ?_⟩
  · simp [localRules, terminal]
  · simp [makeRule, encodeConfiguration]
  · simp [makeRule, cleanupWord, leftContext, rightContext, tapeWord, List.append_assoc]

omit [DecidableEq Γ] [DecidableEq Λ] in
private theorem cleanupRight_reaches (left cells : List Γ) :
    Submission.Helpers.RuleReaches (rules machine support supports)
      (cleanupWord support left cells) (cleanupWord support left []) := by
  induction cells with
  | nil => exact Relation.ReflTransGen.refl
  | cons symbol remaining ih =>
      apply Relation.ReflTransGen.head
      · show Submission.Helpers.RuleStep (rules machine support supports)
          (cleanupWord support left (symbol :: remaining))
          (cleanupWord support left remaining)
        refine ⟨[atom support .leftBoundary] ++ tapeWord support left.reverse,
          tapeWord support remaining ++ [atom support .rightBoundary],
          [atom support .cleanup, atom support (.tape symbol)],
          [atom support .cleanup], ?_, ?_, ?_⟩
        · simpa [makeRule] using
            cleanupRightRule_mem_rules machine support supports symbol
        · simp [cleanupWord, tapeWord, List.append_assoc]
        · simp [cleanupWord, tapeWord, List.append_assoc]
      · exact ih

omit [DecidableEq Γ] [DecidableEq Λ] in
private theorem cleanupLeft_reaches (left : List Γ) :
    Submission.Helpers.RuleReaches (rules machine support supports)
      (cleanupWord support left []) (haltWord support) := by
  induction left with
  | nil =>
      change Relation.ReflTransGen (Submission.Helpers.RuleStep
        (rules machine support supports)) (haltWord support) (haltWord support)
      exact Relation.ReflTransGen.refl
  | cons symbol remaining ih =>
      apply Relation.ReflTransGen.head
      · show Submission.Helpers.RuleStep (rules machine support supports)
          (cleanupWord support (symbol :: remaining) [])
          (cleanupWord support remaining [])
        refine ⟨[atom support .leftBoundary] ++ tapeWord support remaining.reverse,
          [atom support .rightBoundary],
          [atom support (.tape symbol), atom support .cleanup],
          [atom support .cleanup], ?_, ?_, ?_⟩
        · simpa [makeRule] using
            cleanupLeftRule_mem_rules machine support supports symbol
        · simp [cleanupWord, tapeWord, List.append_assoc]
        · simp [cleanupWord, tapeWord, List.append_assoc]
      · exact ih

omit [DecidableEq Γ] [DecidableEq Λ] in
/-- Every terminal machine configuration rewrites to the single cleanup
normal form. -/
theorem terminal_reaches_halt (configuration : Configuration Γ support)
    (terminal : machine configuration.state configuration.head = none) :
    Submission.Helpers.RuleReaches (rules machine support supports)
      (encodeConfiguration support configuration) (haltWord support) :=
  Relation.ReflTransGen.head
    (haltEntry_ruleStep machine support supports configuration terminal)
    ((cleanupRight_reaches machine support supports configuration.left
      (configuration.head :: configuration.right)).trans
      (cleanupLeft_reaches machine support supports configuration.left))

omit [DecidableEq Γ] [DecidableEq Λ] in
/-- A finite sequence of concrete machine steps compiles to a finite
sequence of contextual word-rule steps. -/
theorem reaches_ruleReaches {source target : Configuration Γ support}
    (reaches : StateTransition.Reaches
      (configurationStep machine support supports) source target) :
    Submission.Helpers.RuleReaches (rules machine support supports)
      (encodeConfiguration support source) (encodeConfiguration support target) := by
  induction reaches with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ step ih =>
      exact ih.tail (step_ruleStep machine support supports step)

omit [DecidableEq Γ] [DecidableEq Λ] in
/-- Membership in the evaluator gives a complete rewrite derivation from
the starting configuration to the fixed halt word. -/
theorem eval_mem_ruleReaches {source terminal : Configuration Γ support}
    (evaluation : terminal ∈
      StateTransition.eval (configurationStep machine support supports) source) :
    Submission.Helpers.RuleReaches (rules machine support supports)
      (encodeConfiguration support source) (haltWord support) := by
  obtain ⟨reaches, terminal_step⟩ := StateTransition.mem_eval.mp evaluation
  have terminal_halts :
      machine terminal.state terminal.head = none := by
    cases transition : machine terminal.state terminal.head with
    | none => rfl
    | some result =>
        rcases result with ⟨nextState, statement⟩
        cases statement with
        | write written =>
            simp [configurationStep, transition] at terminal_step
        | move direction =>
            cases direction with
            | left =>
                cases left_eq : terminal.left <;>
                  simp [configurationStep, transition, left_eq] at terminal_step
            | right =>
                cases right_eq : terminal.right <;>
                  simp [configurationStep, transition, right_eq] at terminal_step
  exact (reaches_ruleReaches machine support supports reaches).trans
    (terminal_reaches_halt machine support supports terminal terminal_halts)

end

end Submission.MachineRules
