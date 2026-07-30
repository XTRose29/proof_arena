import Submission.MachineRules

open Turing

namespace Submission.FiniteConfiguration

open Submission.MachineRules

section

variable {Γ Λ : Type*}
variable [Inhabited Γ] [Fintype Γ] [DecidableEq Γ]
variable [Inhabited Λ] [DecidableEq Λ]
variable (machine : TM0.Machine Γ Λ) (support : Finset Λ)
variable (supports : TM0.Supports machine (support : Set Λ))

private abbrev Q (support : Finset Λ) := SupportedState support
private abbrev Config (Γ : Type*) (support : Finset Λ) :=
  Configuration Γ support

/-- The finite-list configuration corresponding to a standard TM0 input. -/
noncomputable def initial (input : List Γ) : Config Γ support where
  state := ⟨default, supports.1⟩
  left := []
  head := input.headI
  right := input.tail

omit [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] in
private theorem mk_default_eq_empty :
    ListBlank.mk [default] = ListBlank.mk ([] : List Γ) :=
  Quotient.sound' (Or.inr ⟨1, by simp⟩)

omit [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] in
theorem initial_toTM0 (input : List Γ) :
    (initial machine support supports input).toTM0 =
      (TM0.init input : TM0.Cfg Γ Λ) := by
  cases input <;>
    simp [initial, Configuration.toTM0, TM0.init, Tape.mk₁, Tape.mk₂, Tape.mk',
      mk_default_eq_empty]

omit [Inhabited Γ] [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] in
private theorem supportedTarget_value
    (state : Q support) (symbol : Γ) (nextState : Λ) (statement : TM0.Stmt Γ)
    (transition : machine state symbol = some (nextState, statement)) :
    (supportedTarget machine support supports state symbol nextState : Λ) =
      nextState := by
  rw [supportedTarget]
  simp [transition]

omit [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] in
/-- The finite-list transition realizes exactly one transition of the
quotient-based TM0 semantics. -/
theorem toTM0_step {source target : Config Γ support}
    (takesStep :
      configurationStep machine support supports source = some target) :
    TM0.step machine source.toTM0 = some target.toTM0 := by
  cases transition : machine source.state source.head with
  | none =>
      simp [configurationStep, transition] at takesStep
  | some result =>
      rcases result with ⟨nextState, statement⟩
      let nextSupported : Q support :=
        supportedTarget machine support supports source.state source.head nextState
      have nextSupportedValue :
          nextState = (nextSupported : Λ) :=
        (supportedTarget_value machine support supports source.state source.head
          nextState statement transition).symm
      cases statement with
      | write written =>
          simp [configurationStep, transition] at takesStep
          subst target
          simp [TM0.step, Configuration.toTM0, transition, Tape.write_mk']
          exact nextSupportedValue
      | move direction =>
          cases direction with
          | left =>
              cases leftEq : source.left with
              | nil =>
                  simp [configurationStep, transition, leftEq] at takesStep
                  subst target
                  simp [TM0.step, Configuration.toTM0, transition,
                    Tape.move_left_mk', leftEq]
                  exact nextSupportedValue
              | cons previous remaining =>
                  simp [configurationStep, transition, leftEq] at takesStep
                  subst target
                  simp [TM0.step, Configuration.toTM0, transition,
                    Tape.move_left_mk', leftEq]
                  exact nextSupportedValue
          | right =>
              cases rightEq : source.right with
              | nil =>
                  simp [configurationStep, transition, rightEq] at takesStep
                  subst target
                  simp [TM0.step, Configuration.toTM0, transition,
                    Tape.move_right_mk', rightEq, mk_default_eq_empty]
                  exact nextSupportedValue
              | cons following remaining =>
                  simp [configurationStep, transition, rightEq] at takesStep
                  subst target
                  simp [TM0.step, Configuration.toTM0, transition,
                    Tape.move_right_mk', rightEq]
                  exact nextSupportedValue

omit [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] in
/-- The finite-list configuration semantics refines Mathlib's TM0
configuration semantics. -/
theorem respects :
    StateTransition.Respects
      (configurationStep machine support supports)
      (TM0.step machine)
      (fun finiteConfig tmConfig => finiteConfig.toTM0 = tmConfig) := by
  intro source tmSource sourceEq
  subst tmSource
  cases transition :
      configurationStep machine support supports source with
  | none =>
      have machineTerminal :
          machine source.state source.head = none := by
        cases machineStep : machine source.state source.head with
        | none => rfl
        | some result =>
            rcases result with ⟨nextState, statement⟩
            cases statement with
            | write written =>
                simp [configurationStep, machineStep] at transition
            | move direction =>
                cases direction with
                | left =>
                    cases leftEq : source.left <;>
                      simp [configurationStep, machineStep, leftEq] at transition
                | right =>
                    cases rightEq : source.right <;>
                      simp [configurationStep, machineStep, rightEq] at transition
      simp [TM0.step, Configuration.toTM0, machineTerminal]
  | some target =>
      exact ⟨target.toTM0, rfl,
        Relation.TransGen.single (toTM0_step machine support supports transition)⟩

omit [Fintype Γ] [DecidableEq Γ] [DecidableEq Λ] in
/-- The standard TM0 evaluator and the finite-list configuration evaluator
have the same termination domain on a finite input. -/
theorem eval_dom_iff (input : List Γ) :
    (StateTransition.eval
        (configurationStep machine support supports)
        (initial machine support supports input)).Dom ↔
      (StateTransition.eval (TM0.step machine) (TM0.init input)).Dom := by
  rw [← initial_toTM0 machine support supports input]
  exact (StateTransition.tr_eval_dom
    (respects machine support supports) rfl).symm

end

end Submission.FiniteConfiguration
