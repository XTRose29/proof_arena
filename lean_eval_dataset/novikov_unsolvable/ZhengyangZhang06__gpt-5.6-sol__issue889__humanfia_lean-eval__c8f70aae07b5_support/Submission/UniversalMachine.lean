import Mathlib.Computability.TuringMachine.ToPartrec

open Encodable Denumerable
open List (Vector)

namespace Submission.UniversalMachine

/-- The unary partial function which interprets its input as a code and
runs that code on input zero. -/
def universalEval (v : List.Vector ℕ 1) : Part ℕ :=
  Nat.Partrec.Code.eval (ofNat Nat.Partrec.Code v.head) 0

/-- The universal evaluator is partial recursive in its encoded program
input. -/
theorem universalEval_partrec : Nat.Partrec' universalEval :=
  Nat.Partrec'.of_part <|
    Nat.Partrec.Code.eval_part.comp
      ((Computable.ofNat Nat.Partrec.Code).comp Computable.vector_head)
      (Computable.const 0)

/-- A fixed program in Mathlib's list-based partial-recursive language
which implements `universalEval`. -/
noncomputable def universalProgram : Turing.ToPartrec.Code :=
  Classical.choose (Turing.ToPartrec.Code.exists_code universalEval_partrec)

/-- Correctness of the selected fixed universal program. -/
theorem universalProgram_eval (v : List.Vector ℕ 1) :
    universalProgram.eval v.1 = pure <$> universalEval v :=
  Classical.choose_spec (Turing.ToPartrec.Code.exists_code universalEval_partrec) v

/-- The one-element input vector carrying a `Nat.Partrec.Code`. -/
def codeInput (c : Nat.Partrec.Code) : List.Vector ℕ 1 :=
  ⟨[encode c], rfl⟩

/-- On encoded programs, the fixed program has exactly the semantics of
the original universal evaluator. -/
theorem universalProgram_eval_code (c : Nat.Partrec.Code) :
    universalProgram.eval (codeInput c).1 = pure <$> Nat.Partrec.Code.eval c 0 := by
  rw [universalProgram_eval]
  simp only [universalEval]
  rw [show (codeInput c).head = encode c from rfl, ofNat_encode]

/-- In particular, the fixed program terminates exactly on the original
halting instances. -/
theorem universalProgram_dom_iff (c : Nat.Partrec.Code) :
    (universalProgram.eval (codeInput c).1).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  rw [universalProgram_eval_code]
  simp

/-- Run Mathlib's compiled list-machine from the configuration carrying
the encoded source program. -/
noncomputable def universalMachineEval (c : Nat.Partrec.Code) :=
  StateTransition.eval (Turing.TM2.step Turing.PartrecToTM2.tr)
    (Turing.PartrecToTM2.init universalProgram (codeInput c).1)

/-- Correctness of the compiled fixed machine. -/
theorem universalMachine_eval (c : Nat.Partrec.Code) :
    universalMachineEval c =
      Turing.PartrecToTM2.halt <$> universalProgram.eval (codeInput c).1 :=
  Turing.PartrecToTM2.tr_eval universalProgram (codeInput c).1

/-- The single compiled machine halts exactly when the encoded source
program halts on input zero. -/
theorem universalMachine_dom_iff (c : Nat.Partrec.Code) :
    (universalMachineEval c).Dom ↔ (Nat.Partrec.Code.eval c 0).Dom := by
  rw [universalMachine_eval]
  simpa using universalProgram_dom_iff c

/-- The finite set of instruction labels reachable by the selected
universal program. -/
noncomputable def universalSupport : Finset Turing.PartrecToTM2.Λ' :=
  Turing.PartrecToTM2.codeSupp universalProgram Turing.PartrecToTM2.Cont'.halt

/-- Mathlib's support theorem proves that the selected universal program
really uses only `universalSupport`. -/
theorem universalProgram_supports :
    @Turing.TM2.Supports _ _ _ _
      ⟨Turing.PartrecToTM2.trNormal universalProgram Turing.PartrecToTM2.Cont'.halt⟩
      Turing.PartrecToTM2.tr universalSupport :=
  Turing.PartrecToTM2.tr_supports universalProgram Turing.PartrecToTM2.Cont'.halt

/-!
## Compilation to one supported TM0 machine

The universal program is a fixed TM2 program. Mathlib supplies verified
TM2-to-TM1 and TM1-to-TM0 translations; the declarations below compose those
translations while choosing the universal program's entry label as the
initial state.
-/

noncomputable local instance universalStateInhabited :
    Inhabited Turing.PartrecToTM2.Λ' :=
  ⟨Turing.PartrecToTM2.trNormal universalProgram Turing.PartrecToTM2.Cont'.halt⟩

/-- The fixed TM1 machine obtained from the universal stack machine. -/
noncomputable def universalTM1 :=
  Turing.TM2to1.tr Turing.PartrecToTM2.tr

/-- The fixed TM0 machine obtained from the universal TM1 machine. -/
noncomputable def universalTM0 :=
  Turing.TM1to0.tr universalTM1

/-- The concrete Boolean-vector tape input for the compiled TM0 machine. -/
def universalTM0Input (c : Nat.Partrec.Code) :=
  Turing.TM2to1.trInit
    (Γ := fun _ : Turing.PartrecToTM2.K' => Turing.PartrecToTM2.Γ')
    Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList (codeInput c).1)

/-- With the universal entry label as default, Mathlib's standard TM2
initializer is the specialized partial-recursive-machine initializer. -/
theorem universalTM2_init (c : Nat.Partrec.Code) :
    (Turing.TM2.init Turing.PartrecToTM2.K'.main
      (Turing.PartrecToTM2.trList (codeInput c).1) :
        Turing.PartrecToTM2.Cfg') =
      Turing.PartrecToTM2.init universalProgram (codeInput c).1 := by
  rw [Turing.TM2.init, Turing.PartrecToTM2.init]
  congr
  funext stackIndex
  cases stackIndex <;> rfl

/-- The support theorem with the universal entry label chosen as the
machine's default initial state. -/
theorem universalProgram_supports_from_start :
    Turing.TM2.Supports Turing.PartrecToTM2.tr universalSupport := by
  constructor
  · change Turing.PartrecToTM2.trNormal universalProgram
      Turing.PartrecToTM2.Cont'.halt ∈
        Turing.PartrecToTM2.codeSupp universalProgram
          Turing.PartrecToTM2.Cont'.halt
    exact Turing.PartrecToTM2.codeSupp_self _ _
      (Turing.PartrecToTM2.trStmts₁_self _)
  · exact universalProgram_supports.2

/-- The finite state support of the compiled TM1 machine. -/
noncomputable def universalTM1Support :=
  Turing.TM2to1.trSupp Turing.PartrecToTM2.tr universalSupport

/-- The compiled TM1 machine stays in `universalTM1Support`. -/
theorem universalTM1_supports :
    Turing.TM1.Supports universalTM1 universalTM1Support :=
  Turing.TM2to1.tr_supports Turing.PartrecToTM2.tr
    universalProgram_supports_from_start

/-- The finite state support of the compiled TM0 machine. -/
noncomputable def universalTM0Support :=
  Turing.TM1to0.trStmts universalTM1 universalTM1Support

/-- The compiled TM0 machine stays in `universalTM0Support`. -/
theorem universalTM0_supports :
    Turing.TM0.Supports universalTM0 (universalTM0Support : Set _) :=
  Turing.TM1to0.tr_supports universalTM1 universalTM1_supports

/-- The standard TM2 evaluator for the fixed program has the original
universal halting domain. -/
theorem universalTM2_dom_iff (c : Nat.Partrec.Code) :
    (Turing.TM2.eval Turing.PartrecToTM2.tr Turing.PartrecToTM2.K'.main
      (Turing.PartrecToTM2.trList (codeInput c).1)).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  simpa [Turing.TM2.eval, universalMachineEval, universalTM2_init] using
    universalMachine_dom_iff c

/-- The TM2-to-TM1 compiler preserves the universal halting domain. -/
theorem universalTM1_dom_iff (c : Nat.Partrec.Code) :
    (Turing.TM1.eval universalTM1 (universalTM0Input c)).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom :=
  (Turing.TM2to1.tr_eval_dom Turing.PartrecToTM2.tr
    Turing.PartrecToTM2.K'.main
    (Turing.PartrecToTM2.trList (codeInput c).1)).trans
      (universalTM2_dom_iff c)

/-- The final fixed TM0 machine halts exactly on the original universal
halting instances. -/
theorem universalTM0_dom_iff (c : Nat.Partrec.Code) :
    (Turing.TM0.eval universalTM0 (universalTM0Input c)).Dom ↔
      (Nat.Partrec.Code.eval c 0).Dom := by
  change
    (Turing.TM0.eval (Turing.TM1to0.tr universalTM1)
      (universalTM0Input c)).Dom ↔
        (Nat.Partrec.Code.eval c 0).Dom
  rw [Turing.TM1to0.tr_eval]
  exact universalTM1_dom_iff c

end Submission.UniversalMachine
