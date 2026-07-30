import Mathlib

open Computability Turing

namespace Submission.Helpers

noncomputable section

/-- Every explicitly enumerated finite type can be given a primitive-recursive coding. -/
@[implicit_reducible]
private noncomputable def finitePrimcodable (α : Type*) [Fintype α] : Primcodable α :=
  Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)

local instance (priority := 5) finitePrimcodableInstance (α : Type*) [Fintype α] :
    Primcodable α :=
  finitePrimcodable α

namespace Machine

variable (M : TM2ComputableAux Bool Bool)

local instance fintypeK : Fintype M.tm.K := M.tm.kFin
local instance fintypeΛ : Fintype M.tm.Λ := M.tm.ΛFin
local instance fintypeσ : Fintype M.tm.σ := M.tm.σFin
local instance fintypeInput : Fintype (M.tm.Γ M.tm.k₀) := M.tm.Γk₀Fin
local instance inhabitedΛ : Inhabited M.tm.Λ := ⟨M.tm.main⟩
local instance decidableEqStmt : DecidableEq M.tm.Stmt := Classical.decEq _

private abbrev StmtCode :=
  ↥(TM2.stmts M.tm.m (Finset.univ : Finset M.tm.Λ))

/--
A finite code for every stack symbol that can arise during a run.  The left
summand codes input symbols.  The right summand records the program statement
and finite control state responsible for a `push`.
-/
private abbrev Symbol :=
  Bool ⊕ (StmtCode M × M.tm.σ)

private def symbolValue : Symbol M → Sigma M.tm.Γ
  | .inl b => ⟨M.tm.k₀, M.inputAlphabet.invFun b⟩
  | .inr (q, v) =>
      match q.1 with
      | some (.push k f _) => ⟨k, f v⟩
      | _ => ⟨M.tm.k₀, M.inputAlphabet.invFun false⟩

private def symbolStack (s : Symbol M) : M.tm.K :=
  (symbolValue M s).1

private def decodeSymbol (k : M.tm.K) (s : Symbol M) : Option (M.tm.Γ k) :=
  if h : symbolStack M s = k then some (h ▸ (symbolValue M s).2) else none

private def decodeStack (k : M.tm.K) : List (Symbol M) → List (M.tm.Γ k)
  | [] => []
  | x :: xs =>
      match decodeSymbol M k x with
      | none => decodeStack k xs
      | some a => a :: decodeStack k xs

private def sameStack (k : M.tm.K) (s : Symbol M) : Bool :=
  decide (symbolStack M s = k)

private def topCode (k : M.tm.K) : List (Symbol M) → Option (Symbol M)
  | [] => none
  | s :: ss => if sameStack M k s then some s else topCode k ss

private def popCode (k : M.tm.K) : List (Symbol M) → List (Symbol M)
  | [] => []
  | s :: ss => if sameStack M k s then ss else s :: popCode k ss

private theorem topCode_primrec (k : M.tm.K) : Primrec (topCode M k) := by
  let p : Symbol M → Bool := sameStack M k
  have hp : Primrec p := Primrec.dom_finite p
  let step : Symbol M × List (Symbol M) × Option (Symbol M) → Option (Symbol M) :=
    fun x => cond (p x.1) (some x.1) x.2.2
  have hstep : Primrec step :=
    Primrec.cond (hp.comp Primrec.fst) (Primrec.option_some.comp Primrec.fst)
      (Primrec.snd.comp Primrec.snd)
  refine
    (Primrec.list_rec Primrec.id (Primrec.const none)
      ((hstep.comp Primrec.snd).to₂)).of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons s ss ih =>
      simp only [id_eq] at ih ⊢
      rw [ih]
      simp [step, p, topCode]

private theorem popCode_primrec (k : M.tm.K) : Primrec (popCode M k) := by
  let p : Symbol M → Bool := sameStack M k
  have hp : Primrec p := Primrec.dom_finite p
  let step : Symbol M × List (Symbol M) × List (Symbol M) → List (Symbol M) :=
    fun x => cond (p x.1) x.2.1 (x.1 :: x.2.2)
  have hstep : Primrec step :=
    Primrec.cond (hp.comp Primrec.fst) (Primrec.fst.comp Primrec.snd)
      (Primrec.list_cons.comp Primrec.fst (Primrec.snd.comp Primrec.snd))
  refine
    (Primrec.list_rec Primrec.id (Primrec.const [])
      ((hstep.comp Primrec.snd).to₂)).of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons s ss ih =>
      simp only [id_eq] at ih ⊢
      rw [ih]
      simp [step, p, popCode]

private abbrev Work :=
  M.tm.σ × List (Symbol M)

private abbrev PackedCfg :=
  Option M.tm.Λ × Work M

private theorem root_mem (l : M.tm.Λ) :
    some (M.tm.m l) ∈ TM2.stmts M.tm.m (Finset.univ : Finset M.tm.Λ) := by
  simp only [TM2.stmts, Finset.mem_insertNone, Finset.mem_biUnion, Option.mem_def,
    Option.some.injEq]
  intro q hq
  subst q
  exact ⟨l, Finset.mem_univ l, TM2.stmts₁_self⟩

private theorem child_mem {q q' : M.tm.Stmt}
    (hqq' : q' ∈ TM2.stmts₁ q)
    (hq : some q ∈ TM2.stmts M.tm.m (Finset.univ : Finset M.tm.Λ)) :
    some q' ∈ TM2.stmts M.tm.m (Finset.univ : Finset M.tm.Λ) :=
  TM2.stmts_trans hqq' hq

private def runStmt :
    (q : M.tm.Stmt) →
      some q ∈ TM2.stmts M.tm.m (Finset.univ : Finset M.tm.Λ) →
        Work M → PackedCfg M
  | .push k f q, hq, (v, s) =>
      runStmt q (child_mem M (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq)
        (v, .inr (⟨some (.push k f q), hq⟩, v) :: s)
  | .peek k f q, hq, (v, s) =>
      runStmt q (child_mem M (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq)
        (f v ((topCode M k s).bind (decodeSymbol M k)), s)
  | .pop k f q, hq, (v, s) =>
      runStmt q (child_mem M (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq)
        (f v ((topCode M k s).bind (decodeSymbol M k)), popCode M k s)
  | .load f q, hq, (v, s) =>
      runStmt q (child_mem M (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq) (f v, s)
  | .branch p q₁ q₂, hq, w =>
      cond (p w.1)
        (runStmt q₁ (child_mem M (by
          rw [TM2.stmts₁]
          exact Finset.mem_insert_of_mem
            (Finset.mem_union_left _ TM2.stmts₁_self)) hq) w)
        (runStmt q₂ (child_mem M (by
          rw [TM2.stmts₁]
          exact Finset.mem_insert_of_mem
            (Finset.mem_union_right _ TM2.stmts₁_self)) hq) w)
  | .goto f, _, (v, s) => (some (f v), v, s)
  | .halt, _, (v, s) => (none, v, s)

private def finiteSelect {α β γ : Type*} [DecidableEq α] [Inhabited α]
    (f : α → β → γ) : List α → α → β → γ
  | [], _, b => f default b
  | a :: as, a', b =>
      cond (decide (a' = a)) (f a b) (finiteSelect f as a' b)

private theorem primrec₂_finite_left {α β γ : Type*} [Fintype α] [Inhabited α]
    [Primcodable α] [Primcodable β] [Primcodable γ] (f : α → β → γ)
    (hf : ∀ a, Primrec (f a)) : Primrec₂ f := by
  classical
  have hselect : ∀ l, Primrec₂ (finiteSelect f l) := by
    intro l
    induction l with
    | nil =>
        exact hf default |>.comp Primrec.snd
    | cons a as ih =>
        exact Primrec.cond
          (Primrec.eq.decide.comp Primrec.fst (Primrec.const a))
          (hf a |>.comp Primrec.snd) ih
  have select_eq :
      ∀ (l : List α) (a : α), a ∈ l → ∀ b, finiteSelect f l a b = f a b := by
    intro l a ha
    induction l with
    | nil => cases ha
    | cons x xs ih =>
        rcases List.mem_cons.mp ha with rfl | ha
        · simp [finiteSelect]
        · by_cases hax : a = x
          · subst a
            simp [finiteSelect]
          · simpa [finiteSelect, hax] using ih ha
  let l := (Finset.univ : Finset α).toList
  refine (hselect l).of_eq fun a b => ?_
  exact select_eq l a (by simp [l]) b

private theorem runStmt_primrec (q : M.tm.Stmt)
    (hq : some q ∈ TM2.stmts M.tm.m (Finset.univ : Finset M.tm.Λ)) :
    Primrec (runStmt M q hq) := by
  induction q with
  | push k f q ih =>
      let hq' := child_mem M (q := .push k f q) (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
      let mk : M.tm.σ → Symbol M :=
        fun v => .inr (⟨some (.push k f q), hq⟩, v)
      have hmk : Primrec mk := Primrec.dom_finite mk
      have hprep : Primrec (fun w : Work M => (w.1, mk w.1 :: w.2)) :=
        Primrec.pair Primrec.fst
          (Primrec.list_cons.comp (hmk.comp Primrec.fst) Primrec.snd)
      exact (ih hq').comp hprep
  | peek k f q ih =>
      let hq' := child_mem M (q := .peek k f q) (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
      let read : M.tm.σ × Option (Symbol M) → M.tm.σ :=
        fun x => f x.1 (x.2.bind (decodeSymbol M k))
      have hread : Primrec read := Primrec.dom_finite read
      have htop : Primrec (fun w : Work M => topCode M k w.2) :=
        (topCode_primrec M k).comp Primrec.snd
      have hvar : Primrec (fun w : Work M => read (w.1, topCode M k w.2)) :=
        hread.comp (Primrec.pair Primrec.fst htop)
      exact (ih hq').comp (Primrec.pair hvar Primrec.snd)
  | pop k f q ih =>
      let hq' := child_mem M (q := .pop k f q) (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
      let read : M.tm.σ × Option (Symbol M) → M.tm.σ :=
        fun x => f x.1 (x.2.bind (decodeSymbol M k))
      have hread : Primrec read := Primrec.dom_finite read
      have htop : Primrec (fun w : Work M => topCode M k w.2) :=
        (topCode_primrec M k).comp Primrec.snd
      have hvar : Primrec (fun w : Work M => read (w.1, topCode M k w.2)) :=
        hread.comp (Primrec.pair Primrec.fst htop)
      have hpop : Primrec (fun w : Work M => popCode M k w.2) :=
        (popCode_primrec M k).comp Primrec.snd
      exact (ih hq').comp (Primrec.pair hvar hpop)
  | load f q ih =>
      let hq' := child_mem M (q := .load f q) (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem TM2.stmts₁_self) hq
      have hf : Primrec f := Primrec.dom_finite f
      exact (ih hq').comp (Primrec.pair (hf.comp Primrec.fst) Primrec.snd)
  | branch p q₁ q₂ ih₁ ih₂ =>
      let hq₁ := child_mem M (q := .branch p q₁ q₂) (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_left _ TM2.stmts₁_self)) hq
      let hq₂ := child_mem M (q := .branch p q₁ q₂) (by
        rw [TM2.stmts₁]
        exact Finset.mem_insert_of_mem
          (Finset.mem_union_right _ TM2.stmts₁_self)) hq
      have hp : Primrec p := Primrec.dom_finite p
      exact Primrec.cond (hp.comp Primrec.fst) (ih₁ hq₁) (ih₂ hq₂)
  | goto f =>
      have hf : Primrec f := Primrec.dom_finite f
      exact Primrec.pair
        (Primrec.option_some.comp (hf.comp Primrec.fst)) Primrec.id
  | halt =>
      exact Primrec.pair (Primrec.const none) Primrec.id

private def runLabel (l : M.tm.Λ) : Work M → PackedCfg M :=
  runStmt M (M.tm.m l) (root_mem M l)

private theorem runLabel_primrec₂ : Primrec₂ (runLabel M) :=
  primrec₂_finite_left (runLabel M) fun l =>
    runStmt_primrec M (M.tm.m l) (root_mem M l)

private def packedStep : PackedCfg M → Option (PackedCfg M)
  | (none, _) => none
  | (some l, w) => some (runLabel M l w)

private theorem packedStep_primrec : Primrec (packedStep M) := by
  let next : PackedCfg M → M.tm.Λ → Option (PackedCfg M) :=
    fun p l => some (runLabel M l p.2)
  have hnext : Primrec₂ next :=
    Primrec.option_some.comp₂
      ((runLabel_primrec₂ M).comp₂ Primrec₂.right (Primrec.snd.comp₂ Primrec₂.left))
  exact
    (Primrec.option_casesOn Primrec.fst (Primrec.const none) hnext).of_eq
      fun p => by
        rcases p with ⟨l, w⟩
        cases l <;> rfl

private def unpack (p : PackedCfg M) : M.tm.Cfg where
  l := p.1
  var := p.2.1
  stk k := decodeStack M k p.2.2

private theorem cfg_ext {K : Type*} {Γ : K → Type*} {Λ σ : Type*}
    {a b : TM2.Cfg Γ Λ σ} (hl : a.l = b.l) (hv : a.var = b.var)
    (hs : a.stk = b.stk) : a = b := by
  rcases a with ⟨la, va, sa⟩
  rcases b with ⟨lb, vb, sb⟩
  simp_all

private theorem topCode_decode (k : M.tm.K) (s : List (Symbol M)) :
    (topCode M k s).bind (decodeSymbol M k) = (decodeStack M k s).head? := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : (symbolValue M x).1 = k
      · simp [topCode, sameStack, symbolStack, decodeStack, decodeSymbol, hx]
      · have ht : topCode M k (x :: xs) = topCode M k xs := by
          simp [topCode, sameStack, symbolStack, hx]
        have hd : decodeStack M k (x :: xs) = decodeStack M k xs := by
          simp [decodeStack, decodeSymbol, symbolStack, hx]
        rw [ht, hd]
        exact ih

private theorem decodeStack_pop_same (k : M.tm.K) (s : List (Symbol M)) :
    decodeStack M k (popCode M k s) = (decodeStack M k s).tail := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : (symbolValue M x).1 = k
      · simp [popCode, sameStack, symbolStack, decodeStack, decodeSymbol, hx]
      · simp [popCode, sameStack, symbolStack, decodeStack, decodeSymbol, hx, ih]

private theorem decodeStack_pop_other {j k : M.tm.K} (hjk : j ≠ k)
    (s : List (Symbol M)) :
    decodeStack M j (popCode M k s) = decodeStack M j s := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : (symbolValue M x).1 = k
      · simp [popCode, sameStack, symbolStack, hx, decodeStack, decodeSymbol,
          Ne.symm hjk]
      · simp [popCode, sameStack, symbolStack, hx, decodeStack, decodeSymbol, ih]

private theorem decodeStack_pop (k : M.tm.K) (s : List (Symbol M)) :
    (fun j => decodeStack M j (popCode M k s)) =
      Function.update (fun j => decodeStack M j s) k (decodeStack M k s).tail := by
  funext j
  by_cases hjk : j = k
  · subst j
    simp [decodeStack_pop_same]
  · rw [Function.update_of_ne hjk]
    exact decodeStack_pop_other M hjk s

private theorem decodeStack_push (k : M.tm.K) (f : M.tm.σ → M.tm.Γ k)
    (q : M.tm.Stmt)
    (hq : some (.push k f q) ∈
      TM2.stmts M.tm.m (Finset.univ : Finset M.tm.Λ))
    (v : M.tm.σ) (s : List (Symbol M)) :
    (fun j => decodeStack M j (.inr (⟨some (.push k f q), hq⟩, v) :: s)) =
      Function.update (fun j => decodeStack M j s) k
        (f v :: decodeStack M k s) := by
  funext j
  by_cases hjk : j = k
  · subst j
    simp [decodeStack, decodeSymbol, symbolValue, symbolStack]
  · rw [Function.update_of_ne hjk]
    simp [decodeStack, decodeSymbol, symbolValue, symbolStack, Ne.symm hjk]

private theorem unpack_runStmt (q : M.tm.Stmt)
    (hq : some q ∈ TM2.stmts M.tm.m (Finset.univ : Finset M.tm.Λ))
    (v : M.tm.σ) (s : List (Symbol M)) :
    unpack M (runStmt M q hq (v, s)) =
      TM2.stepAux q v (fun k => decodeStack M k s) := by
  induction q generalizing v s with
  | push k f q ih =>
      rw [runStmt, ih]
      simp only [TM2.stepAux]
      congr
      exact decodeStack_push M k f q hq v s
  | peek k f q ih =>
      rw [runStmt, ih, topCode_decode]
      rfl
  | pop k f q ih =>
      rw [runStmt, ih, topCode_decode]
      simp only [TM2.stepAux]
      congr
      exact decodeStack_pop M k s
  | load f q ih =>
      rw [runStmt, ih]
      rfl
  | branch p q₁ q₂ ih₁ ih₂ =>
      cases hp : p v <;> simp [runStmt, TM2.stepAux, hp, ih₁, ih₂]
  | goto f => rfl
  | halt => rfl

private theorem unpack_step (p : PackedCfg M) :
    Option.map (unpack M) (packedStep M p) = M.tm.step (unpack M p) := by
  rcases p with ⟨l, v, s⟩
  rcases l with - | l
  · rfl
  · simp only [packedStep, Option.map_some, FinTM2.step, TM2.step]
    exact congr_arg some (unpack_runStmt M (M.tm.m l) (root_mem M l) v s)

private def packedNext (p : PackedCfg M) : PackedCfg M ⊕ PackedCfg M :=
  (packedStep M p).elim (Sum.inl p) Sum.inr

private theorem packedNext_primrec : Primrec (packedNext M) := by
  exact
    (Primrec.option_casesOn (packedStep_primrec M)
      (Primrec.sumInl.comp Primrec.id)
      ((Primrec.sumInr.comp Primrec.snd).to₂)).of_eq
        fun p => by
          rcases p with ⟨l, w⟩
          rcases l with - | l <;> rfl

private theorem packedEval_partrec :
    Partrec (StateTransition.eval (packedStep M)) := by
  unfold StateTransition.eval
  apply Partrec.fix
  refine ((packedNext_primrec M).to_comp.partrec).of_eq fun p => ?_
  change Part.some (packedNext M p) =
    Part.some ((packedStep M p).elim (Sum.inl p) Sum.inr)
  rfl

private def packInput (l : List Bool) : List (Symbol M) :=
  l.map Sum.inl

private def packedInit (l : List Bool) : PackedCfg M :=
  (some M.tm.main, M.tm.initialState, packInput M l)

private theorem decodeStack_packInput_same (l : List Bool) :
    decodeStack M M.tm.k₀ (packInput M l) =
      l.map M.inputAlphabet.invFun := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      change decodeStack M M.tm.k₀ (Sum.inl b :: packInput M l) =
        M.inputAlphabet.invFun b :: l.map M.inputAlphabet.invFun
      simp [decodeStack, decodeSymbol, symbolValue, symbolStack, ih]

private theorem decodeStack_packInput_other {k : M.tm.K} (hk : k ≠ M.tm.k₀)
    (l : List Bool) :
    decodeStack M k (packInput M l) = [] := by
  induction l with
  | nil => rfl
  | cons b l ih =>
      change decodeStack M k (Sum.inl b :: packInput M l) = []
      simp [decodeStack, decodeSymbol, symbolValue, symbolStack, Ne.symm hk, ih]

private theorem unpack_packedInit (l : List Bool) :
    unpack M (packedInit M l) =
      initList M.tm (l.map M.inputAlphabet.invFun) := by
  apply cfg_ext (a := unpack M (packedInit M l))
    (b := initList M.tm (l.map M.inputAlphabet.invFun)) rfl rfl
  funext k
  by_cases hk : k = M.tm.k₀
  · subst k
    simpa [unpack, packedInit, initList] using decodeStack_packInput_same M l
  · simpa [unpack, packedInit, initList, hk] using
      decodeStack_packInput_other M hk l

private def outputSymbol (s : Symbol M) : Option Bool :=
  if h : (symbolValue M s).1 = M.tm.k₁ then
    some (M.outputAlphabet (h ▸ (symbolValue M s).2))
  else
    none

private def outputBits : List (Symbol M) → List Bool
  | [] => []
  | x :: xs =>
      match outputSymbol M x with
      | none => outputBits xs
      | some b => b :: outputBits xs

private theorem outputBits_primrec : Primrec (outputBits M) := by
  have hs : Primrec (outputSymbol M) := Primrec.dom_finite (outputSymbol M)
  refine (Primrec.listFilterMap Primrec.id ((hs.comp Primrec.snd).to₂)).of_eq ?_
  intro s
  induction s with
  | nil => rfl
  | cons x xs ih =>
      simp only [id_eq] at ih ⊢
      cases hx : outputSymbol M x <;> simp [outputBits, hx, ih]

private theorem outputBits_eq (s : List (Symbol M)) :
    outputBits M s =
      (decodeStack M M.tm.k₁ s).map M.outputAlphabet := by
  induction s with
  | nil => rfl
  | cons x xs ih =>
      by_cases hx : (symbolValue M x).1 = M.tm.k₁
      · simp [outputBits, outputSymbol, decodeStack, decodeSymbol, symbolStack, hx, ih]
      · simp [outputBits, outputSymbol, decodeStack, decodeSymbol, symbolStack, hx, ih]

private def incBits : List Bool → List Bool
  | [] => [true]
  | false :: l => true :: l
  | true :: l => false :: incBits l

private theorem incBits_primrec : Primrec incBits := by
  let step : Bool × List Bool × List Bool → List Bool
    | (false, l, _) => true :: l
    | (true, _, ih) => false :: ih
  have hstep : Primrec step := by
    refine (Primrec.cond Primrec.fst
      (Primrec.list_cons.comp (Primrec.const false) (Primrec.snd.comp Primrec.snd))
      (Primrec.list_cons.comp (Primrec.const true) (Primrec.fst.comp Primrec.snd))).of_eq ?_
    rintro ⟨b, l, ih⟩
    cases b <;> rfl
  refine
    (Primrec.list_rec Primrec.id (Primrec.const [true])
      ((hstep.comp Primrec.snd).to₂)).of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [id_eq] at ih ⊢
      rw [ih]
      cases b <;> rfl

private theorem incBits_encodePosNum (n : PosNum) :
    incBits (encodePosNum n) = encodePosNum n.succ := by
  induction n with
  | one => rfl
  | bit0 n ih => rfl
  | bit1 n ih => simpa [incBits, encodePosNum, PosNum.succ] using congr_arg (false :: ·) ih

private theorem incBits_encodeNum (n : Num) :
    incBits (encodeNum n) = encodeNum n.succ := by
  cases n with
  | zero => rfl
  | pos n =>
      simpa [encodeNum, Num.succ, Num.succ'] using incBits_encodePosNum n

private theorem incBits_encodeNat (n : ℕ) :
    incBits (encodeNat n) = encodeNat (n + 1) := by
  simpa [encodeNat, Nat.cast_succ, Num.add_one] using incBits_encodeNum (n : Num)

private theorem encodeNat_primrec : Primrec encodeNat := by
  let encode' : ℕ → List Bool :=
    fun n => Nat.rec [] (fun _ ih => incBits ih) n
  have hencode' : Primrec encode' :=
    Primrec.nat_rec₁ [] ((incBits_primrec.comp Primrec.snd).to₂)
  refine hencode'.of_eq fun n => ?_
  induction n with
  | zero => rfl
  | succ n ih =>
      change incBits (encode' n) = encodeNat (n + 1)
      rw [ih, incBits_encodeNat]

private def bitsValue : List Bool → ℕ
  | [] => 0
  | false :: l => 2 * bitsValue l
  | true :: l => 2 * bitsValue l + 1

private theorem bitsValue_primrec : Primrec bitsValue := by
  let step : Bool × List Bool × ℕ → ℕ
    | (false, _, ih) => 2 * ih
    | (true, _, ih) => 2 * ih + 1
  have hstep : Primrec step := by
    have hdouble : Primrec (fun x : Bool × List Bool × ℕ => 2 * x.2.2) :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp Primrec.snd)
    refine (Primrec.cond Primrec.fst
      (Primrec.nat_add.comp hdouble (Primrec.const 1)) hdouble).of_eq ?_
    rintro ⟨b, l, ih⟩
    cases b <;> rfl
  refine
    (Primrec.list_rec Primrec.id (Primrec.const 0)
      ((hstep.comp Primrec.snd).to₂)).of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons b l ih =>
      simp only [id_eq] at ih ⊢
      rw [ih]
      cases b <;> rfl

private theorem bitsValue_encodePosNum (n : PosNum) :
    bitsValue (encodePosNum n) = n := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      simp [encodePosNum, bitsValue, ih, PosNum.cast_bit0]
      omega
  | bit1 n ih =>
      simp [encodePosNum, bitsValue, ih, PosNum.cast_bit1]
      omega

private theorem bitsValue_encodeNum (n : Num) :
    bitsValue (encodeNum n) = (n : ℕ) := by
  cases n with
  | zero => rfl
  | pos p => exact bitsValue_encodePosNum p

private theorem bitsValue_encodeNat (n : ℕ) :
    bitsValue (encodeNat n) = n := by
  change bitsValue (encodeNum (n : Num)) = n
  exact (bitsValue_encodeNum (n : Num)).trans (Num.to_of_nat n)

private def packedOutput (p : PackedCfg M) : ℕ :=
  bitsValue (outputBits M p.2.2)

private theorem packedOutput_primrec : Primrec (packedOutput M) :=
  bitsValue_primrec.comp ((outputBits_primrec M).comp (Primrec.snd.comp Primrec.snd))

private theorem semiconj_unpack :
    Function.Semiconj (Option.map (unpack M))
      (flip bind (packedStep M)) (flip bind M.tm.step) := by
  intro p
  rcases p with - | p
  · rfl
  · change Option.map (unpack M) (packedStep M p) = M.tm.step (unpack M p)
    exact unpack_step M p

private noncomputable def lift_evalsTo {p : PackedCfg M} {c : M.tm.Cfg}
    (h : StateTransition.EvalsTo M.tm.step (unpack M p) (some c)) :
    Σ p', StateTransition.EvalsTo (packedStep M) p (some p') ×
      PLift (unpack M p' = c) := by
  have hi := (semiconj_unpack M).iterate_right h.steps (some p)
  simp only [Option.map_some] at hi
  rw [h.evals_in_steps] at hi
  generalize he :
      (flip bind (packedStep M))^[h.steps] (some p) = r at hi
  rcases r with - | p'
  · cases hi
  · simp only [Option.map_some, Option.some.injEq] at hi
    refine ⟨p', ⟨h.steps, ?_⟩, ⟨hi⟩⟩
    simpa using he

private theorem iterate_none {α : Type*} (step : α → Option α) :
    ∀ n, (flip Option.bind step)^[n] none = none
  | 0 => rfl
  | n + 1 => by
      rw [Function.iterate_succ_apply]
      exact iterate_none step n

private theorem reaches_of_iterate {α : Type*} {step : α → Option α} {a b : α} :
    ∀ n, (flip Option.bind step)^[n] (some a) = some b →
      StateTransition.Reaches step a b
  | 0, h => by
      simp only [Function.iterate_zero, id_eq, Option.some.injEq] at h
      subst b
      exact Relation.ReflTransGen.refl
  | n + 1, h => by
      rw [Function.iterate_succ_apply] at h
      change (flip Option.bind step)^[n] (step a) = some b at h
      cases hs : step a with
      | none =>
          rw [hs] at h
          rw [iterate_none] at h
          cases h
      | some a' =>
          rw [hs] at h
          exact Relation.ReflTransGen.head hs (reaches_of_iterate n h)

private theorem reaches_of_evalsTo {α : Type*} {step : α → Option α} {a b : α}
    (h : StateTransition.EvalsTo step a (some b)) :
    StateTransition.Reaches step a b :=
  reaches_of_iterate h.steps (by simpa using h.evals_in_steps)

private theorem packedInit_primrec :
    Primrec (fun n : ℕ => packedInit M (encodeNat n)) := by
  have hpack : Primrec (fun l : List Bool => packInput M l) := by
    have hin : Primrec (Sum.inl : Bool → Symbol M) := Primrec.dom_finite _
    exact Primrec.list_map Primrec.id ((hin.comp Primrec.snd).to₂)
  exact Primrec.pair (Primrec.const (some M.tm.main))
    (Primrec.pair (Primrec.const M.tm.initialState)
      (hpack.comp encodeNat_primrec))

private def partialOutput (n : ℕ) : Part ℕ :=
  (StateTransition.eval (packedStep M) (packedInit M (encodeNat n))).map
    (packedOutput M)

private theorem partialOutput_partrec : Partrec (partialOutput M) := by
  exact
    ((packedEval_partrec M).comp (packedInit_primrec M).to_comp).map
      (((packedOutput_primrec M).to_comp.comp Primrec.snd.to_comp).to₂)

theorem computable_of_tm2 {f : ℕ → ℕ}
    (h : TM2Computable encodeNat encodeNat f) : Computable f := by
  let M := h.toTM2ComputableAux
  have hp : Partrec (partialOutput M) := partialOutput_partrec M
  refine hp.of_eq_tot fun n => ?_
  have hout := h.outputsFun n
  change StateTransition.EvalsTo M.tm.step
    (initList M.tm ((encodeNat n).map M.inputAlphabet.invFun))
    (some (haltList M.tm ((encodeNat (f n)).map M.outputAlphabet.invFun))) at hout
  rw [← unpack_packedInit M (encodeNat n)] at hout
  obtain ⟨p, hpEval, hpUnpackLift⟩ := lift_evalsTo M hout
  have hpUnpack := hpUnpackLift.down
  have hpTerm : packedStep M p = none := by
    rcases p with ⟨l, v, s⟩
    have hl : l = none := congr_arg TM2.Cfg.l hpUnpack
    subst l
    rfl
  have hpMem : p ∈ StateTransition.eval (packedStep M)
      (packedInit M (encodeNat n)) :=
    StateTransition.mem_eval.2 ⟨reaches_of_evalsTo hpEval, hpTerm⟩
  apply (Part.mem_map_iff (packedOutput M)).2
  refine ⟨p, hpMem, ?_⟩
  have hs := congr_arg (fun c => c.stk M.tm.k₁) hpUnpack
  have hs' : decodeStack M M.tm.k₁ p.2.2 =
      (encodeNat (f n)).map M.outputAlphabet.invFun := by
    simpa [unpack, haltList] using hs
  rw [packedOutput, outputBits_eq, hs']
  simpa [List.map_map] using bitsValue_encodeNat (f n)

end Machine

end

end Submission.Helpers
