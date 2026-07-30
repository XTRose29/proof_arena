import Submission.FiniteConfiguration

open Turing

namespace Submission.AffineMachine

open Submission.MachineRules

/-!
# A canonical accepting extension of a supported machine

The group construction uses base-three coordinates for the two finite tape
halves.  This file first isolates the purely operational part: after the
machine stops, a deterministic cleanup phase removes both finite lists and
reaches one canonical accepting state.
-/

/-- Nonzero base-three digits for Boolean tape symbols. -/
def bitDigit : Bool → ℕ
  | false => 1
  | true => 2

theorem bitDigit_injective : Function.Injective bitDigit := by
  intro left right equal
  cases left <;> cases right <;> simp [bitDigit] at equal ⊢

/-- A prefix code for a finite Boolean stack.  Zero represents the empty
stack; nonempty stacks have last base-three digit one or two. -/
def stackCode : List Bool → ℕ
  | [] => 0
  | symbol :: rest => bitDigit symbol + 3 * stackCode rest

@[simp]
theorem stackCode_nil : stackCode [] = 0 := rfl

@[simp]
theorem stackCode_cons (symbol : Bool) (rest : List Bool) :
    stackCode (symbol :: rest) = bitDigit symbol + 3 * stackCode rest := rfl

theorem stackCode_cons_ne_zero (symbol : Bool) (rest : List Bool) :
    stackCode (symbol :: rest) ≠ 0 := by
  cases symbol <;> simp [stackCode, bitDigit]

theorem stackCode_injective : Function.Injective stackCode := by
  intro left
  induction left with
  | nil =>
      intro right equal
      cases right with
      | nil => rfl
      | cons symbol rest =>
          exact (stackCode_cons_ne_zero symbol rest equal.symm).elim
  | cons symbol rest ih =>
      intro right equal
      cases right with
      | nil =>
          exact (stackCode_cons_ne_zero symbol rest equal).elim
      | cons other remaining =>
          have symbolEq : symbol = other := by
            have modEq := congrArg (fun value : ℕ => value % 3) equal
            cases symbol <;> cases other <;>
              simp [stackCode, Nat.add_mod, bitDigit] at modEq ⊢
          subst other
          have restEq : stackCode rest = stackCode remaining := by
            cases symbol <;>
              simp only [stackCode, bitDigit] at equal <;> omega
          rw [ih restEq]

section

variable {Γ Λ : Type*}
variable [Inhabited Γ]
variable [Inhabited Λ] [DecidableEq Λ]
variable (machine : TM0.Machine Γ Λ) (support : Finset Λ)
variable (supports : TM0.Supports machine (support : Set Λ))

private abbrev Config (Γ : Type*) (support : Finset Λ) :=
  Configuration Γ support

/-- Machine configurations followed by two erasing phases and one canonical
accepting state. -/
inductive State (Γ : Type*) (support : Finset Λ)
  | run (configuration : Config Γ support)
  | cleanLeft (left right : List Γ)
  | cleanRight (right : List Γ)
  | accepted

/-- Extend the supported machine by deterministic cleanup. -/
noncomputable def step : State Γ support → Option (State Γ support)
  | .run configuration =>
      match configurationStep machine support supports configuration with
      | some next => some (.run next)
      | none => some (.cleanLeft configuration.left configuration.right)
  | .cleanLeft [] right => some (.cleanRight right)
  | .cleanLeft (_ :: remaining) right =>
      some (.cleanLeft remaining right)
  | .cleanRight [] => some .accepted
  | .cleanRight (_ :: remaining) => some (.cleanRight remaining)
  | .accepted => none

omit [DecidableEq Λ] in
/-- Every left-cleanup state reaches the corresponding right-cleanup state. -/
theorem cleanLeft_reaches (left right : List Γ) :
    StateTransition.Reaches (step machine support supports)
      (.cleanLeft left right) (.cleanRight right) := by
  induction left with
  | nil =>
      exact Relation.ReflTransGen.single (by simp [step])
  | cons symbol remaining ih =>
      exact Relation.ReflTransGen.head (by simp [step]) ih

omit [DecidableEq Λ] in
/-- Every right-cleanup state reaches the canonical accepting state. -/
theorem cleanRight_reaches (right : List Γ) :
    StateTransition.Reaches (step machine support supports)
      (.cleanRight right) .accepted := by
  induction right with
  | nil =>
      exact Relation.ReflTransGen.single (by simp [step])
  | cons symbol remaining ih =>
      exact Relation.ReflTransGen.head (by simp [step]) ih

omit [DecidableEq Λ] in
/-- One supported-machine reachability proof lifts to the run phase. -/
theorem run_reaches {source target : Config Γ support}
    (reaches :
      StateTransition.Reaches
        (configurationStep machine support supports) source target) :
    StateTransition.Reaches (step machine support supports)
      (.run source) (.run target) := by
  induction reaches with
  | refl => exact Relation.ReflTransGen.refl
  | @tail before after _ takesStep ih =>
      have takesStep' :
          configurationStep machine support supports before = some after :=
        takesStep
      exact ih.tail (by simp [step, takesStep'])

omit [DecidableEq Λ] in
/-- If the supported machine reaches a terminal configuration, the extended
machine reaches the canonical accepting state. -/
theorem reaches_accepted_of_terminal {source terminal : Config Γ support}
    (reaches :
      StateTransition.Reaches
        (configurationStep machine support supports) source terminal)
    (terminalStep :
      configurationStep machine support supports terminal = none) :
    StateTransition.Reaches (step machine support supports)
      (.run source) .accepted := by
  exact ((run_reaches machine support supports reaches).tail
    (by simp [step, terminalStep])).trans <|
      (cleanLeft_reaches machine support supports terminal.left terminal.right).trans
        (cleanRight_reaches machine support supports terminal.right)

/-- Semantic information retained by every extended state reachable from a
run configuration. -/
def ReachInvariant (source : Config Γ support) : State Γ support → Prop
  | .run current =>
      StateTransition.Reaches
        (configurationStep machine support supports) source current
  | .cleanLeft _ _ =>
      ∃ terminal,
        StateTransition.Reaches
          (configurationStep machine support supports) source terminal ∧
        configurationStep machine support supports terminal = none
  | .cleanRight _ =>
      ∃ terminal,
        StateTransition.Reaches
          (configurationStep machine support supports) source terminal ∧
        configurationStep machine support supports terminal = none
  | .accepted =>
      ∃ terminal,
        StateTransition.Reaches
          (configurationStep machine support supports) source terminal ∧
        configurationStep machine support supports terminal = none

omit [DecidableEq Λ] in
private theorem invariant_step (source : Config Γ support)
    {before after : State Γ support}
    (invariant : ReachInvariant machine support supports source before)
    (takesStep : after ∈ step machine support supports before) :
    ReachInvariant machine support supports source after := by
  cases before with
  | run current =>
      cases transition :
          configurationStep machine support supports current with
      | none =>
          simp [step, transition] at takesStep
          subst after
          exact ⟨current, invariant, transition⟩
      | some next =>
          simp [step, transition] at takesStep
          subst after
          exact invariant.tail transition
  | cleanLeft left right =>
      obtain ⟨terminal, reaches, terminalStep⟩ := invariant
      cases left with
      | nil =>
          simp [step] at takesStep
          subst after
          exact ⟨terminal, reaches, terminalStep⟩
      | cons symbol remaining =>
          simp [step] at takesStep
          subst after
          exact ⟨terminal, reaches, terminalStep⟩
  | cleanRight right =>
      obtain ⟨terminal, reaches, terminalStep⟩ := invariant
      cases right with
      | nil =>
          simp [step] at takesStep
          subst after
          exact ⟨terminal, reaches, terminalStep⟩
      | cons symbol remaining =>
          simp [step] at takesStep
          subst after
          exact ⟨terminal, reaches, terminalStep⟩
  | accepted =>
      simp [step] at takesStep

omit [DecidableEq Λ] in
theorem invariant_of_reaches (source : Config Γ support)
    {state : State Γ support}
    (reaches :
      StateTransition.Reaches (step machine support supports)
        (.run source) state) :
    ReachInvariant machine support supports source state := by
  induction reaches with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ takesStep ih =>
      exact invariant_step machine support supports source ih takesStep

omit [DecidableEq Λ] in
/-- The cleanup extension terminates exactly when the supported source
machine terminates. -/
theorem eval_dom_iff (source : Config Γ support) :
    (StateTransition.eval (step machine support supports) (.run source)).Dom ↔
      (StateTransition.eval
        (configurationStep machine support supports) source).Dom := by
  constructor
  · intro terminates
    obtain ⟨terminalState, terminalMem⟩ := Part.dom_iff_mem.mp terminates
    obtain ⟨reaches, terminalStep⟩ :=
      StateTransition.mem_eval.mp terminalMem
    have invariant :=
      invariant_of_reaches machine support supports source reaches
    cases terminalState with
    | run current =>
        cases transition :
            configurationStep machine support supports current <;>
          simp [step, transition] at terminalStep
    | cleanLeft left right =>
        cases left <;> simp [step] at terminalStep
    | cleanRight right =>
        cases right <;> simp [step] at terminalStep
    | accepted =>
        obtain ⟨terminal, sourceReaches, terminalStep⟩ := invariant
        exact Part.dom_iff_mem.mpr
          ⟨terminal, StateTransition.mem_eval.mpr
            ⟨sourceReaches, terminalStep⟩⟩
  · intro terminates
    obtain ⟨terminal, terminalMem⟩ := Part.dom_iff_mem.mp terminates
    obtain ⟨reaches, terminalStep⟩ :=
      StateTransition.mem_eval.mp terminalMem
    exact Part.dom_iff_mem.mpr
      ⟨.accepted, StateTransition.mem_eval.mpr
        ⟨reaches_accepted_of_terminal machine support supports reaches terminalStep,
          by simp [step]⟩⟩

/-- Undirected adjacency in a deterministic transition graph. -/
def Adjacent {σ : Type*} (transition : σ → Option σ) (left right : σ) : Prop :=
  right ∈ transition left ∨ left ∈ transition right

/-- Connectedness in the undirected transition graph. -/
def Connected {σ : Type*} (transition : σ → Option σ) (left right : σ) : Prop :=
  Relation.ReflTransGen (Adjacent transition) left right

private theorem eval_eq_of_adjacent {σ : Type*} {transition : σ → Option σ}
    {left right : σ} (adjacent : Adjacent transition left right) :
    StateTransition.eval transition left =
      StateTransition.eval transition right := by
  rcases adjacent with forward | backward
  · exact StateTransition.reaches_eval
      (Relation.ReflTransGen.single forward)
  · exact (StateTransition.reaches_eval
      (Relation.ReflTransGen.single backward)).symm

theorem eval_eq_of_connected {σ : Type*} {transition : σ → Option σ}
    {left right : σ} (connected : Connected transition left right) :
    StateTransition.eval transition left =
      StateTransition.eval transition right := by
  induction connected with
  | refl => rfl
  | tail _ adjacent ih =>
      exact ih.trans (eval_eq_of_adjacent adjacent)

/-- A state is connected to a terminal state exactly when its deterministic
transition terminates. -/
theorem connected_terminal_iff_dom {σ : Type*} {transition : σ → Option σ}
    {source terminal : σ} (terminalStep : transition terminal = none)
    (terminal_unique : ∀ state, transition state = none → state = terminal) :
    Connected transition source terminal ↔
      (StateTransition.eval transition source).Dom := by
  constructor
  · intro connected
    rw [eval_eq_of_connected connected]
    exact Part.dom_iff_mem.mpr
      ⟨terminal, StateTransition.mem_eval.mpr
        ⟨Relation.ReflTransGen.refl, terminalStep⟩⟩
  · intro terminates
    obtain ⟨result, resultMem⟩ := Part.dom_iff_mem.mp terminates
    obtain ⟨sourceReaches, resultStep⟩ :=
      StateTransition.mem_eval.mp resultMem
    rw [terminal_unique result resultStep] at sourceReaches
    exact sourceReaches.mono fun _ _ takesStep => Or.inl takesStep

end

end Submission.AffineMachine
