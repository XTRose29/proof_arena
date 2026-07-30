import Mathlib

open Computability Turing

namespace Submission.Helpers.Forward

noncomputable section

open Turing.PartrecToTM2 Turing.ToPartrec

private abbrev RawΓ := Turing.PartrecToTM2.Γ'
private abbrev RawK := Turing.PartrecToTM2.K'
private abbrev RawΛ := Turing.PartrecToTM2.Λ'
private abbrev RawState := Option RawΓ
private abbrev RawStmt := TM2.Stmt (fun _ : RawK => RawΓ) RawΛ RawState
private abbrev RawCfg := TM2.Cfg (fun _ : RawK => RawΓ) RawΛ RawState

private instance : Fintype RawK where
  elems := {.main, .rev, .aux, .stack}
  complete k := by cases k <;> simp

private abbrev Support (c : Code) :=
  ↥(codeSupp c Cont'.halt)

private theorem main_mem (c : Code) :
    trNormal c Cont'.halt ∈ codeSupp c Cont'.halt :=
  codeSupp_self c Cont'.halt (trStmts₁_self _)

private def restrictStmt (c : Code) :
    (q : RawStmt) →
      TM2.SupportsStmt (codeSupp c Cont'.halt) q →
        TM2.Stmt (fun _ : RawK => RawΓ) (Support c) RawState
  | .push k f q, h => .push k f (restrictStmt c q h)
  | .peek k f q, h => .peek k f (restrictStmt c q h)
  | .pop k f q, h => .pop k f (restrictStmt c q h)
  | .load f q, h => .load f (restrictStmt c q h)
  | .branch p q₁ q₂, h =>
      .branch p (restrictStmt c q₁ h.1) (restrictStmt c q₂ h.2)
  | .goto f, h => .goto fun v => ⟨f v, h v⟩
  | .halt, _ => .halt

private def evalProgram (c : Code) (q : Support c) :
    TM2.Stmt (fun _ : RawK => RawΓ) (Support c) RawState :=
  restrictStmt c (tr q.1) ((tr_supports c Cont'.halt).2 q.1 q.2)

private def evalStep (c : Code) :
    TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState →
      Option (TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState) :=
  TM2.step (evalProgram c)

private def liftEvalCfg {c : Code}
    (p : TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState) : RawCfg where
  l := p.l.map Subtype.val
  var := p.var
  stk := p.stk

private theorem lift_restrictStmt (c : Code) (q : RawStmt)
    (hq : TM2.SupportsStmt (codeSupp c Cont'.halt) q)
    (v : RawState) (s : ∀ _ : RawK, List RawΓ) :
    liftEvalCfg (TM2.stepAux (restrictStmt c q hq) v s) =
      TM2.stepAux q v s := by
  induction q generalizing v s with
  | push k f q ih =>
      simp only [restrictStmt, TM2.stepAux]
      exact ih hq _ _
  | peek k f q ih =>
      simp only [restrictStmt, TM2.stepAux]
      exact ih hq _ _
  | pop k f q ih =>
      simp only [restrictStmt, TM2.stepAux]
      exact ih hq _ _
  | load f q ih =>
      simp only [restrictStmt, TM2.stepAux]
      exact ih hq _ _
  | branch p q₁ q₂ ih₁ ih₂ =>
      rcases hq with ⟨hq₁, hq₂⟩
      cases hp : p v <;>
        simp [restrictStmt, TM2.stepAux, hp, ih₁ hq₁, ih₂ hq₂]
  | goto f => rfl
  | halt => rfl

private theorem lift_evalStep (c : Code)
    (p : TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState) :
    Option.map liftEvalCfg (evalStep c p) =
      TM2.step tr (liftEvalCfg p) := by
  rcases p with ⟨l, v, s⟩
  rcases l with - | q
  · rfl
  · simp only [evalStep, TM2.step, Option.map_some]
    exact congr_arg some (lift_restrictStmt c (tr q.1)
      ((tr_supports c Cont'.halt).2 q.1 q.2) v s)

private theorem eval_respects (c : Code) :
    StateTransition.Respects (evalStep c) (TM2.step tr)
      (fun a b => liftEvalCfg a = b) := by
  rw [StateTransition.fun_respects]
  intro p
  cases h : evalStep c p with
  | none =>
      have hm := lift_evalStep c p
      simpa [h, StateTransition.FRespects] using hm.symm
  | some p' =>
      have hm := lift_evalStep c p
      exact Relation.TransGen.single (by simpa [h] using hm.symm)

private def evalInit (c : Code) (v : List ℕ) :
    TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState where
  l := some ⟨trNormal c Cont'.halt, main_mem c⟩
  var := none
  stk := K'.elim (trList v) [] [] []

private def evalHalt (c : Code) (v : List ℕ) :
    TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState where
  l := none
  var := none
  stk := K'.elim (trList v) [] [] []

private theorem lift_evalInit (c : Code) (v : List ℕ) :
    liftEvalCfg (evalInit c v) = PartrecToTM2.init c v :=
  rfl

private theorem lift_evalHalt (c : Code) (v : List ℕ) :
    liftEvalCfg (evalHalt c v) = PartrecToTM2.halt v :=
  rfl

private theorem optionMap_injective {α β : Type*} {f : α → β}
    (hf : Function.Injective f) : Function.Injective (Option.map f) := by
  intro x y h
  cases x with
  | none => cases y <;> simp_all
  | some x =>
      cases y with
      | none => simp_all
      | some y =>
          simp only [Option.map_some, Option.some.injEq] at h
          exact congr_arg some (hf h)

private theorem liftEvalCfg_injective (c : Code) :
    Function.Injective (@liftEvalCfg c) := by
  intro a b h
  rcases a with ⟨la, va, sa⟩
  rcases b with ⟨lb, vb, sb⟩
  have hl : Option.map Subtype.val la = Option.map Subtype.val lb :=
    congr_arg TM2.Cfg.l h
  have hv : va = vb := congr_arg TM2.Cfg.var h
  have hs : sa = sb := congr_arg TM2.Cfg.stk h
  cases optionMap_injective Subtype.val_injective hl
  cases hv
  cases hs
  rfl

private theorem evalHalt_mem (c : Code) (v out : List ℕ)
    (hc : c.eval v = Part.some out) :
    evalHalt c out ∈ StateTransition.eval (evalStep c) (evalInit c v) := by
  have hraw : PartrecToTM2.halt out ∈
      StateTransition.eval (TM2.step tr) (PartrecToTM2.init c v) := by
    rw [PartrecToTM2.tr_eval, hc]
    exact (Part.mem_map_iff _).2 ⟨out, Part.mem_some_iff.2 rfl, rfl⟩
  have hmap :
      PartrecToTM2.halt out ∈
        liftEvalCfg <$> StateTransition.eval (evalStep c) (evalInit c v) := by
    rw [← StateTransition.tr_eval' (evalStep c) (TM2.step tr) liftEvalCfg
      (eval_respects c), lift_evalInit]
    exact hraw
  rcases (Part.mem_map_iff (@liftEvalCfg c)).1 hmap with ⟨p, hp, hpLift⟩
  have : p = evalHalt c out := by
    apply liftEvalCfg_injective c
    rw [hpLift, lift_evalHalt]
  simpa [this] using hp

private theorem nonemptyEvalsToOfReaches {α : Type*} {step : α → Option α} {a b : α} :
    StateTransition.Reaches step a b →
      Nonempty (StateTransition.EvalsTo step a (some b))
  | .refl => ⟨StateTransition.EvalsTo.refl step a⟩
  | .tail h e => by
      rcases nonemptyEvalsToOfReaches h with ⟨ih⟩
      exact ⟨StateTransition.EvalsTo.trans step a _ (some b)
        ih ⟨1, by
          change step _ = some b
          exact e⟩⟩

private noncomputable def evalsToOfReaches {α : Type*} {step : α → Option α} {a b : α}
    (h : StateTransition.Reaches step a b) :
    StateTransition.EvalsTo step a (some b) :=
  Classical.choice (nonemptyEvalsToOfReaches h)

private inductive Tape
  | io
  | work (k : RawK)
  deriving DecidableEq, Fintype

private abbrev Alphabet (k : Tape) : Type :=
  match k with
  | .io => Bool
  | .work _ => RawΓ

private inductive Label (c : Code)
  | inputScan
  | inputRestore
  | eval (q : Support c)
  | outputScan
  | outputRestore
  deriving Fintype

private def wrapStmt (c : Code) :
    (q : RawStmt) →
      TM2.SupportsStmt (codeSupp c Cont'.halt) q →
        TM2.Stmt Alphabet (Label c) RawState
  | .push k f q, h => .push (.work k) f (wrapStmt c q h)
  | .peek k f q, h => .peek (.work k) f (wrapStmt c q h)
  | .pop k f q, h => .pop (.work k) f (wrapStmt c q h)
  | .load f q, h => .load f (wrapStmt c q h)
  | .branch p q₁ q₂, h =>
      .branch p (wrapStmt c q₁ h.1) (wrapStmt c q₂ h.2)
  | .goto f, h => .goto fun v => .eval ⟨f v, h v⟩
  | .halt, _ => .goto fun _ => .outputScan

private def toRawBit : Bool → RawΓ
  | false => .bit0
  | true => .bit1

private def isRawBit : RawState → Bool
  | some .bit0 => true
  | some .bit1 => true
  | _ => false

private def toBool : RawState → Bool
  | some .bit1 => true
  | _ => false

private def wrapperProgram (c : Code) : Label c → TM2.Stmt Alphabet (Label c) RawState
  | .inputScan =>
      .pop .io (fun _ b => b.map toRawBit) <|
        .branch Option.isSome
          (.push (.work K'.rev) (fun s => s.getD default) <|
            .goto fun _ => .inputScan)
          (.push (.work K'.main) (fun _ => .cons) <|
            .goto fun _ => .inputRestore)
  | .inputRestore =>
      .pop (.work K'.rev) (fun _ x => x) <|
        .branch Option.isSome
          (.push (.work K'.main) (fun s => s.getD default) <|
            .goto fun _ => .inputRestore)
          (.goto fun _ => .eval ⟨trNormal c Cont'.halt, main_mem c⟩)
  | .eval q =>
      wrapStmt c (tr q.1) ((tr_supports c Cont'.halt).2 q.1 q.2)
  | .outputScan =>
      .pop (.work K'.main) (fun _ x => x) <|
        .branch isRawBit
          (.push (.work K'.rev) (fun s => s.getD default) <|
            .goto fun _ => .outputScan)
          (.goto fun _ => .outputRestore)
  | .outputRestore =>
      .pop (.work K'.rev) (fun _ x => x) <|
        .branch Option.isSome
          (.push .io toBool <| .goto fun _ => .outputRestore)
          .halt

private abbrev wrapperMachine (c : Code) : FinTM2 where
  K := Tape
  k₀ := .io
  k₁ := .io
  Γ := Alphabet
  Λ := Label c
  main := .inputScan
  σ := RawState
  initialState := none
  m := wrapperProgram c

private def wrapStacks (s : ∀ _ : RawK, List RawΓ) :
    ∀ k : Tape, List (Alphabet k)
  | .io => []
  | .work k => s k

private theorem update_wrapStacks (s : ∀ _ : RawK, List RawΓ)
    (k : RawK) (l : List RawΓ) :
    Function.update (wrapStacks s) (.work k) l =
      wrapStacks (Function.update s k l) := by
  funext t
  cases t with
  | io => simp [wrapStacks]
  | work j =>
      by_cases hjk : j = k
      · subst j
        simp [wrapStacks]
      · have hwork : Tape.work j ≠ Tape.work k := by
          intro h
          injection h with h'
          exact hjk h'
        simp [wrapStacks, hjk, hwork]

private def wrapEvalCfg {c : Code}
    (p : TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState) :
    (wrapperMachine c).Cfg where
  l := p.l.elim (.some .outputScan) (fun q => .some (.eval q))
  var := p.var
  stk := wrapStacks p.stk

private theorem wrap_restrictStmt (c : Code) (q : RawStmt)
    (hq : TM2.SupportsStmt (codeSupp c Cont'.halt) q)
    (v : RawState) (s : ∀ _ : RawK, List RawΓ) :
    TM2.stepAux (wrapStmt c q hq) v (wrapStacks s) =
      wrapEvalCfg (TM2.stepAux (restrictStmt c q hq) v s) := by
  induction q generalizing v s with
  | push k f q ih =>
      simp only [wrapStmt, restrictStmt, TM2.stepAux]
      rw [update_wrapStacks]
      rw [ih]
      rfl
  | peek k f q ih =>
      simp only [wrapStmt, restrictStmt, TM2.stepAux, wrapStacks]
      exact ih hq _ _
  | pop k f q ih =>
      simp only [wrapStmt, restrictStmt, TM2.stepAux, wrapStacks]
      rw [update_wrapStacks]
      rw [ih]
  | load f q ih =>
      simp only [wrapStmt, restrictStmt, TM2.stepAux]
      exact ih hq _ _
  | branch p q₁ q₂ ih₁ ih₂ =>
      rcases hq with ⟨hq₁, hq₂⟩
      cases hp : p v <;>
        simp [wrapStmt, restrictStmt, TM2.stepAux, hp, ih₁ hq₁, ih₂ hq₂]
  | goto f => rfl
  | halt => rfl

private theorem wrapper_step_eval (c : Code)
    (p p' : TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState)
    (h : evalStep c p = some p') :
    (wrapperMachine c).step (wrapEvalCfg p) = some (wrapEvalCfg p') := by
  rcases p with ⟨l, v, s⟩
  rcases l with - | q
  · simp [evalStep, TM2.step] at h
  · simp only [evalStep, TM2.step, Option.some.injEq] at h
    subst p'
    simp only [wrapEvalCfg, FinTM2.step, TM2.step, wrapperMachine, wrapperProgram]
    exact congr_arg some (wrap_restrictStmt c (tr q.1)
      ((tr_supports c Cont'.halt).2 q.1 q.2) v s)

private theorem wrap_reaches (c : Code)
    {p p' : TM2.Cfg (fun _ : RawK => RawΓ) (Support c) RawState}
    (h : StateTransition.Reaches (evalStep c) p p') :
    StateTransition.Reaches (wrapperMachine c).step (wrapEvalCfg p) (wrapEvalCfg p') := by
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h e ih =>
      exact Relation.ReflTransGen.tail ih (wrapper_step_eval c _ _ e)

private theorem wrapper_eval_reaches (c : Code) (v out : List ℕ)
    (hc : c.eval v = Part.some out) :
    StateTransition.Reaches (wrapperMachine c).step
      (wrapEvalCfg (evalInit c v)) (wrapEvalCfg (evalHalt c out)) :=
  wrap_reaches c (StateTransition.mem_eval.1 (evalHalt_mem c v out hc)).1

private def tapeContents (io : List Bool) (main rev aux stackData : List RawΓ) :
    ∀ k : Tape, List (Alphabet k)
  | .io => io
  | .work K'.main => main
  | .work K'.rev => rev
  | .work K'.aux => aux
  | .work K'.stack => stackData

private theorem wrapStacks_elim (main rev aux stackData : List RawΓ) :
    wrapStacks (K'.elim main rev aux stackData) =
      tapeContents [] main rev aux stackData := by
  funext k
  cases k with
  | io => rfl
  | work k => cases k <;> rfl

@[simp]
private theorem update_stacks_io (io io' : List Bool)
    (main rev aux stackData : List RawΓ) :
    Function.update (tapeContents io main rev aux stackData) Tape.io io' =
      tapeContents io' main rev aux stackData := by
  funext k
  cases k with
  | io => simp [tapeContents]
  | work k =>
      cases k <;> simp [tapeContents]

@[simp]
private theorem update_stacks_main (io : List Bool)
    (main main' rev aux stackData : List RawΓ) :
    Function.update (tapeContents io main rev aux stackData) (.work K'.main) main' =
      tapeContents io main' rev aux stackData := by
  funext k
  cases k with
  | io => simp [tapeContents]
  | work k =>
      cases k <;> simp [tapeContents]

@[simp]
private theorem update_stacks_rev (io : List Bool)
    (main rev rev' aux stackData : List RawΓ) :
    Function.update (tapeContents io main rev aux stackData) (.work K'.rev) rev' =
      tapeContents io main rev' aux stackData := by
  funext k
  cases k with
  | io => simp [tapeContents]
  | work k =>
      cases k <;> simp [tapeContents]

private def cfg (c : Code) (l : Option (Label c)) (v : RawState)
    (io : List Bool) (main rev aux stackData : List RawΓ) :
    (wrapperMachine c).Cfg where
  l := l
  var := v
  stk := tapeContents io main rev aux stackData

private theorem cfg_ext {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {a b : TM2.Cfg Γ Λ σ} (hl : a.l = b.l) (hv : a.var = b.var)
    (hs : a.stk = b.stk) : a = b := by
  rcases a with ⟨la, va, sa⟩
  rcases b with ⟨lb, vb, sb⟩
  simp_all

private theorem initList_wrapperMachine (c : Code) (l : List Bool) :
    initList (wrapperMachine c) l =
      cfg c (some .inputScan) none l [] [] [] [] := by
  apply cfg_ext (a := initList (wrapperMachine c) l)
    (b := cfg c (some .inputScan) none l [] [] [] []) rfl rfl
  funext k
  cases k with
  | io => simp [initList, wrapperMachine, cfg, tapeContents]
  | work k =>
      cases k <;> simp [initList, wrapperMachine, cfg, tapeContents]

private theorem haltList_wrapperMachine (c : Code) (l : List Bool) :
    haltList (wrapperMachine c) l =
      cfg c none none l [] [] [] [] := by
  apply cfg_ext (a := haltList (wrapperMachine c) l)
    (b := cfg c none none l [] [] [] []) rfl rfl
  funext k
  cases k with
  | io => simp [haltList, wrapperMachine, cfg, tapeContents]
  | work k =>
      cases k <;> simp [haltList, wrapperMachine, cfg, tapeContents]

private theorem scan_reaches (c : Code) (l : List Bool) (rev : List RawΓ)
    (v : RawState) :
    StateTransition.Reaches (wrapperMachine c).step
      (cfg c (some .inputScan) v l [] rev [] [])
      (cfg c (some .inputRestore) none [] [.cons]
        (l.reverse.map toRawBit ++ rev) [] []) := by
  change Relation.ReflTransGen
    (fun a b => b ∈ (wrapperMachine c).step a) _ _
  induction l generalizing rev v with
  | nil =>
      exact Relation.ReflTransGen.single (by
        simp [FinTM2.step, wrapperMachine, wrapperProgram, cfg, tapeContents, TM2.step,
          TM2.stepAux]
        rfl)
  | cons b l ih =>
      refine Relation.ReflTransGen.head (b :=
        cfg c (some .inputScan) (some (toRawBit b)) l []
          (toRawBit b :: rev) [] []) ?_ ?_
      · cases b <;>
          simp [FinTM2.step, wrapperMachine, wrapperProgram, cfg, tapeContents, TM2.step,
            TM2.stepAux, toRawBit] <;> rfl
      · simpa [List.reverse_cons, List.map_append, List.append_assoc] using
          ih (toRawBit b :: rev) (some (toRawBit b))

private theorem restore_reaches (c : Code) (l main : List RawΓ) (v : RawState) :
    StateTransition.Reaches (wrapperMachine c).step
      (cfg c (some .inputRestore) v [] main l [] [])
      (cfg c (some (.eval ⟨trNormal c Cont'.halt, main_mem c⟩)) none []
        (l.reverse ++ main) [] [] []) := by
  change Relation.ReflTransGen
    (fun a b => b ∈ (wrapperMachine c).step a) _ _
  induction l generalizing main v with
  | nil =>
      exact Relation.ReflTransGen.single (by
        simp [FinTM2.step, wrapperMachine, wrapperProgram, cfg, tapeContents, TM2.step,
          TM2.stepAux]
        rfl)
  | cons x l ih =>
      refine Relation.ReflTransGen.head (b :=
        cfg c (some .inputRestore) (some x) [] (x :: main) l [] []) ?_ ?_
      · simp [FinTM2.step, wrapperMachine, wrapperProgram, cfg, tapeContents, TM2.step,
          TM2.stepAux]
        rfl
      · simpa [List.reverse_cons, List.append_assoc] using
          ih (x :: main) (some x)

private theorem map_encodePosNum (n : PosNum) :
    (encodePosNum n).map toRawBit = PartrecToTM2.trPosNum n := by
  induction n with
  | one => rfl
  | bit0 n ih => simpa [encodePosNum, PartrecToTM2.trPosNum, toRawBit] using ih
  | bit1 n ih => simpa [encodePosNum, PartrecToTM2.trPosNum, toRawBit] using ih

private theorem map_encodeNum (n : Num) :
    (encodeNum n).map toRawBit = PartrecToTM2.trNum n := by
  cases n with
  | zero => rfl
  | pos p => exact map_encodePosNum p

private theorem map_encodeNat (n : ℕ) :
    (encodeNat n).map toRawBit = PartrecToTM2.trNat n := by
  exact map_encodeNum (n : Num)

private theorem init_reaches (c : Code) (n : ℕ) :
    StateTransition.Reaches (wrapperMachine c).step
      (initList (wrapperMachine c) (encodeNat n))
      (wrapEvalCfg (evalInit c [n])) := by
  rw [initList_wrapperMachine]
  change Relation.ReflTransGen
    (fun a b => b ∈ (wrapperMachine c).step a) _ _
  have hscan := scan_reaches c (encodeNat n) [] none
  have hrestore := restore_reaches c
    ((encodeNat n).reverse.map toRawBit) [.cons] none
  change Relation.ReflTransGen
    (fun a b => b ∈ (wrapperMachine c).step a) _ _ at hscan hrestore
  have h := hscan.trans (by simpa only [List.append_nil] using hrestore)
  simpa [cfg, wrapperMachine, tapeContents, wrapEvalCfg, evalInit, wrapStacks,
    wrapStacks_elim, List.map_reverse, List.reverse_reverse, map_encodeNat,
    PartrecToTM2.trList] using h

private theorem outputScan_reaches (c : Code) (l : List Bool) (rev : List RawΓ)
    (v : RawState) :
    StateTransition.Reaches (wrapperMachine c).step
      (cfg c (some .outputScan) v [] (l.map toRawBit ++ [.cons]) rev [] [])
      (cfg c (some .outputRestore) (some .cons) [] []
        ((l.map toRawBit).reverse ++ rev) [] []) := by
  change Relation.ReflTransGen
    (fun a b => b ∈ (wrapperMachine c).step a) _ _
  induction l generalizing rev v with
  | nil =>
      exact Relation.ReflTransGen.single (by
        simp [FinTM2.step, wrapperMachine, wrapperProgram, cfg, tapeContents, TM2.step,
          TM2.stepAux, isRawBit]
        rfl)
  | cons b l ih =>
      refine Relation.ReflTransGen.head (b :=
        cfg c (some .outputScan) (some (toRawBit b)) []
          (l.map toRawBit ++ [.cons]) (toRawBit b :: rev) [] []) ?_ ?_
      · cases b <;>
          simp [FinTM2.step, wrapperMachine, wrapperProgram, cfg, tapeContents, TM2.step,
            TM2.stepAux, isRawBit, toRawBit] <;> rfl
      · simpa [List.map, List.reverse_cons, List.append_assoc] using
          ih (toRawBit b :: rev) (some (toRawBit b))

private theorem outputRestore_reaches (c : Code) (l acc : List Bool) (v : RawState) :
    StateTransition.Reaches (wrapperMachine c).step
      (cfg c (some .outputRestore) v acc [] (l.map toRawBit) [] [])
      (cfg c none none (l.reverse ++ acc) [] [] [] []) := by
  change Relation.ReflTransGen
    (fun a b => b ∈ (wrapperMachine c).step a) _ _
  induction l generalizing acc v with
  | nil =>
      exact Relation.ReflTransGen.single (by
        simp [FinTM2.step, wrapperMachine, wrapperProgram, cfg, tapeContents, TM2.step,
          TM2.stepAux]
        rfl)
  | cons b l ih =>
      refine Relation.ReflTransGen.head (b :=
        cfg c (some .outputRestore) (some (toRawBit b)) (b :: acc) []
          (l.map toRawBit) [] []) ?_ ?_
      · cases b <;>
          simp [FinTM2.step, wrapperMachine, wrapperProgram, cfg, tapeContents, TM2.step,
            TM2.stepAux, toRawBit, toBool] <;> rfl
      · simpa [List.reverse_cons, List.append_assoc] using
          ih (b :: acc) (some (toRawBit b))

private theorem output_reaches (c : Code) (n : ℕ) :
    StateTransition.Reaches (wrapperMachine c).step
      (wrapEvalCfg (evalHalt c [n]))
      (haltList (wrapperMachine c) (encodeNat n)) := by
  rw [haltList_wrapperMachine]
  change Relation.ReflTransGen
    (fun a b => b ∈ (wrapperMachine c).step a) _ _
  have hscan := outputScan_reaches c (encodeNat n) [] none
  have hrestore := outputRestore_reaches c (encodeNat n).reverse [] (some .cons)
  change Relation.ReflTransGen
    (fun a b => b ∈ (wrapperMachine c).step a) _ _ at hscan hrestore
  have h := hscan.trans (by
    simpa only [List.append_nil, List.map_reverse] using hrestore)
  simpa [cfg, wrapperMachine, tapeContents, wrapEvalCfg, evalHalt, wrapStacks,
    wrapStacks_elim, List.map_reverse, List.reverse_reverse, map_encodeNat,
    PartrecToTM2.trList] using h

private theorem total_reaches (c : Code) (n m : ℕ)
    (hc : c.eval [n] = Part.some [m]) :
    StateTransition.Reaches (wrapperMachine c).step
      (initList (wrapperMachine c) (encodeNat n))
      (haltList (wrapperMachine c) (encodeNat m)) :=
  (init_reaches c n).trans <|
    (wrapper_eval_reaches c [n] [m] hc).trans (output_reaches c m)

theorem tm2_of_computable {f : ℕ → ℕ} (hf : Computable f) :
    Nonempty (TM2Computable encodeNat encodeNat f) := by
  have hfPart : Partrec (f : ℕ →. ℕ) := hf
  have hfVec : @Nat.Partrec' 1 (fun v => (f v.head : Part ℕ)) :=
    Nat.Partrec'.part_iff₁.2 hfPart
  obtain ⟨c, hc⟩ := ToPartrec.Code.exists_code hfVec
  refine ⟨{
    tm := wrapperMachine c
    inputAlphabet := Equiv.refl Bool
    outputAlphabet := Equiv.refl Bool
    outputsFun := fun n => ?_
  }⟩
  have hc' : c.eval [n] = Part.some [f n] := by
    simpa [List.Vector.cons_val, List.Vector.nil] using hc (n ::ᵥ List.Vector.nil)
  simpa [TM2Outputs] using
    evalsToOfReaches (total_reaches c n (f n) hc')

end

end Submission.Helpers.Forward
