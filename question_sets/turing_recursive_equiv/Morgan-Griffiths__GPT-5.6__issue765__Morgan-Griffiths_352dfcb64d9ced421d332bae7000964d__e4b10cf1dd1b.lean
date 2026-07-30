import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Bits.lean
section
open Computability Turing
namespace TuringRecSupport
/-- Numeric value of a little-endian bit string; unlike `decodeNat` this treats malformed
strings cheaply. On the image of `encodeNat` they agree. -/
def bitval : List Bool → ℕ
 | [] => 0
 | false::t => 2 * bitval t
 | true::t => 1 + 2 * bitval t

 theorem prim_bitval : Primrec bitval := by
  let step : List Bool → Bool × List Bool × ℕ → ℕ := fun _ p =>
    if p.1 then 1 + 2 * p.2.2 else 2 * p.2.2
  have ps : Primrec₂ step := by
    -- arithmetic / boolean branching
    have twice : Primrec (fun p : (Bool × List Bool × ℕ) => 2 * p.2.2) :=
      Primrec.nat_mul.comp (Primrec.const 2) (Primrec.snd.comp (Primrec.snd))
    have succ : Primrec (fun p : (Bool × List Bool × ℕ) => 1 + 2 * p.2.2) :=
      Primrec.nat_add.comp (Primrec.const 1) twice
    exact (Primrec.cond (Primrec.fst.comp Primrec.snd) (succ.comp Primrec.snd)
      (twice.comp Primrec.snd)).to₂.of_eq (fun x p => by rcases p with ⟨b,l,k⟩; cases b <;> rfl)
  exact (Primrec.list_rec (f:= fun x : List Bool => x) (g:= fun _ : List Bool => (0:ℕ))
    Primrec.id (Primrec.const 0) ps).of_eq (fun l => by
      induction l with
      | nil => rfl
      | cons b l ih => cases b <;> simp [step, bitval, ih])

 theorem bitval_encodePos (n : PosNum) : bitval (encodePosNum n) = (n : ℕ) := by
  induction n with
  | one => rfl
  | bit0 n ih =>
      simp [encodePosNum, bitval, ih]
      omega
  | bit1 n ih =>
      -- PosNum.cast equations simp handles
      simp [encodePosNum, bitval, ih]
      omega

 theorem bitval_encode (n : ℕ) : bitval (encodeNat n) = n := by
  have main : ∀ q : Num, bitval (encodeNum q) = (q : ℕ) := by
    intro q
    cases q with
    | zero => rfl
    | pos p => exact bitval_encodePos p
  simpa [encodeNat, Num.to_of_nat] using (main (n : Num))
end TuringRecSupport
namespace TuringRecSupport
 def binc : List Bool → List Bool
 | [] => [true]
 | false :: l => true :: l
 | true :: l => false :: binc l
 theorem prim_binc : Primrec binc := by
  -- structural recursion, the tail is available together with its recursive image
  let st : List Bool → Bool × List Bool × List Bool → List Bool := fun _ p =>
    if p.1 then false :: p.2.2 else true :: p.2.1
  have ps : Primrec₂ st := by
    have a : Primrec (fun p : Bool × List Bool × List Bool => false :: p.2.2) :=
      Primrec.list_cons.comp (Primrec.const false) (Primrec.snd.comp Primrec.snd)
    have b : Primrec (fun p : Bool × List Bool × List Bool => true :: p.2.1) :=
      Primrec.list_cons.comp (Primrec.const true) (Primrec.fst.comp Primrec.snd)
    exact (Primrec.cond (Primrec.fst.comp Primrec.snd) (a.comp Primrec.snd)
      (b.comp Primrec.snd)).to₂.of_eq (fun x p => by rcases p with ⟨b,l,r⟩; cases b <;> rfl)
  exact (Primrec.list_rec (f:= fun x : List Bool => x)
    (g:=fun _ : List Bool => [true]) Primrec.id (Primrec.const [true]) ps).of_eq (by
      intro l; induction l with
      | nil => rfl
      | cons x l ih => cases x <;> simp [st, binc, ih])

 theorem enc_succ_pos (p : PosNum) : encodePosNum p.succ = binc (encodePosNum p) := by
  induction p with
  | one => rfl
  | bit0 p ih => rfl
  | bit1 p ih =>
      simp [PosNum.succ, encodePosNum, binc]
      exact ih

 theorem enc_succ_num (q : Num) : encodeNum q.succ = binc (encodeNum q) := by
  cases q with
  | zero => rfl
  | pos p =>
    -- use positive successor
    exact enc_succ_pos p

 def genbits (n : ℕ) : List Bool := n.rec [] (fun _ l => binc l)
 theorem prim_genbits : Primrec genbits := by
  unfold genbits
  have base : Primrec (fun _ : Unit => ([] : List Bool)) := Primrec.const []
  have step : Primrec₂ (fun _ : Unit => fun p : ℕ × List Bool => binc p.2) :=
    (prim_binc.comp (Primrec.snd.comp Primrec.snd)).to₂
  have h := Primrec.nat_rec base step
  exact h.comp (Primrec.const ()) Primrec.id
 theorem genbits_eq (n : ℕ) : genbits n = encodeNat n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change binc (genbits n) = encodeNat (n+1)
    rw [ih]
    unfold encodeNat
    change binc (encodeNum (Num.ofNat' n)) = encodeNum (Num.ofNat' (n+1))
    rw [Num.ofNat'_succ, Num.add_one]
    exact (enc_succ_num (n : Num)).symm

 theorem prim_encodeNat : Primrec encodeNat :=
   prim_genbits.of_eq genbits_eq
end TuringRecSupport

end
-- END INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Bits.lean

-- BEGIN INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Forward.lean
section
open Turing
open StateTransition Function
namespace TuringRecForward
open Turing.PartrecToTM2
open Turing.ToPartrec

noncomputable instance kfin : Fintype K' where
  elems := {K'.main, K'.rev, K'.aux, K'.stack}
  complete x := by cases x <;> simp

abbrev WK := Bool ⊕ K'
noncomputable instance : DecidableEq WK := Classical.decEq _

def WG : WK → Type
 | Sum.inl _ => Bool
 | Sum.inr _ => Γ'

noncomputable instance WGfin0 : Fintype (WG (Sum.inl false)) := inferInstanceAs (Fintype Bool)

-- wrapper labels: 0 preloop, 1 reverse, 2 postloop, 3 done, core labels
abbrev Sub (c : Code) := {q : Λ' // q ∈ codeSupp c Cont'.halt}
abbrev Lab (c : Code) := Fin 4 ⊕ Sub c

noncomputable instance (c : Code) : Fintype (Lab c) := inferInstance

abbrev S (c : Code) := codeSupp c Cont'.halt

theorem q0mem (c : Code) : trNormal c Cont'.halt ∈ S c :=
  codeSupp_self _ _ (trStmts₁_self _)

def q0 (c : Code) : Sub c := ⟨trNormal c Cont'.halt, q0mem c⟩

-- lift a core statement, replacing halt by post (2); all labels known in S
noncomputable def liftQ {c : Code} :
  (q : TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ')) →
  TM2.SupportsStmt (S c) q → TM2.Stmt WG (Lab c) (Option Γ')
 | .push k f t, h => .push (Sum.inr k) f (liftQ t h)
 | .peek k f t, h => .peek (Sum.inr k) f (liftQ t h)
 | .pop k f t, h => .pop (Sum.inr k) f (liftQ t h)
 | .load f t, h => .load f (liftQ t h)
 | .branch f a b, h => .branch f (liftQ a h.1) (liftQ b h.2)
 | .goto g, h => .goto (fun v => Sum.inr ⟨g v, h v⟩)
 | .halt, h => .goto (fun _ => Sum.inl (2 : Fin 4))

-- wrapper commands
open TM2.Stmt

def bitcell : Bool → Γ' := fun b => if b then Γ'.bit1 else Γ'.bit0

noncomputable def wm (c : Code) : Lab c → TM2.Stmt WG (Lab c) (Option Γ')
 | Sum.inl i =>
   -- pre loop consumes input to rev
   if i = (0 : Fin 4) then
     .pop (Sum.inl false)
       (fun _ z => z.map bitcell)
       (.branch Option.isSome
         (.push (Sum.inr K'.rev) (fun s => s.getD default)
           (.goto (fun _ => Sum.inl (0 : Fin 4))))
         -- end input: put cons first
         (.push (Sum.inr K'.main) (fun _ => Γ'.cons)
           (.goto (fun _ => Sum.inl (1 : Fin 4)))))
   else if i = (1 : Fin 4) then
     .pop (Sum.inr K'.rev) (fun _ z => z)
       (.branch Option.isSome
         (.push (Sum.inr K'.main) (fun s => s.getD default)
           (.goto (fun _ => Sum.inl (1 : Fin 4))))
         (.goto (fun _ => Sum.inr (q0 c))))
   else if i = (2 : Fin 4) then
     -- output: pop main; ignore delimiter(s), output bits reversing twice? main result bits in order,
     -- push to rev then final transfer to out using state 3
     .pop (Sum.inr K'.main) (fun _ z => z)
       (.branch (fun s => s = some Γ'.bit0 ∨ s = some Γ'.bit1)
         (.push (Sum.inr K'.rev) (fun s => s.getD default)
           (.goto (fun _ => Sum.inl (2 : Fin 4))))
         (.goto (fun _ => Sum.inl (3 : Fin 4))))
   else
     .pop (Sum.inr K'.rev) (fun _ z => z)
       (.branch Option.isSome
         (.push (Sum.inl true) (fun s => decide (s = some Γ'.bit1))
           (.goto (fun _ => Sum.inl (3 : Fin 4))))
         .halt)
 | Sum.inr q => liftQ (tr q.1)
    ((tr_supports c Cont'.halt).2 q.1 q.2)

noncomputable def machine (c : Code) : FinTM2 where
 K := WK
 k₀ := Sum.inl false
 k₁ := Sum.inl true
 Γ := WG
 Λ := Lab c
 main := Sum.inl (0 : Fin 4)
 ΛFin := inferInstance
 σ := Option Γ'
 initialState := none
 σFin := inferInstance
 Γk₀Fin := inferInstance
 m := wm c


-- a stack embedding
noncomputable def ws (xi xo : List Bool) (A : K' → List Γ') : ∀ k, List (WG k)
 | Sum.inl false => xi
 | Sum.inl true => xo
 | Sum.inr k => A k

@[simp] theorem ws_l0 (a b A) : ws a b A (Sum.inl false) = a := rfl
@[simp] theorem ws_l1 (a b A) : ws a b A (Sum.inl true) = b := rfl
@[simp] theorem ws_r (a b A k) : ws a b A (Sum.inr k) = A k := rfl

@[simp] theorem up_r (a b A k x) :
 Function.update (ws a b A) (Sum.inr k) x = ws a b (Function.update A k x) := by
  classical
  funext j
  rcases j with j|j
  · cases j <;> simp [Function.update_of_ne]
  · by_cases e : j = k
    · subst j; simp
    · simp [Function.update_of_ne, e]

@[simp] theorem up_l0 (a b A x) :
 Function.update (ws a b A) (Sum.inl false) x = ws x b A := by
  classical
  funext j; rcases j with j|j
  · cases j <;> simp [Function.update, Sum.inl.injEq]
  · simp [Function.update, Sum.inl.injEq]

@[simp] theorem up_l1 (a b A x) :
 Function.update (ws a b A) (Sum.inl true) x = ws a x A := by
  classical
  funext j; rcases j with j|j
  · cases j <;> simp [Function.update, Sum.inl.injEq]
  · simp [Function.update, Sum.inl.injEq]

-- labels and config conversion
noncomputable def labOf {c} (l : Option Λ') (hl : l ∈ Finset.insertNone (S c)) : Option (Lab c) :=
 match l with
 | none => some (Sum.inl (2 : Fin 4))
 | some q => some (Sum.inr ⟨q, (by simpa using hl)⟩)

noncomputable def emb {c : Code} (d : TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ'))
    (hl : d.l ∈ Finset.insertNone (S c)) : (machine c).Cfg :=
 ⟨labOf d.l hl, d.var, ws [] [] d.stk⟩

-- computational form of `stepAux`: translation changes only terminal label.
theorem lift_aux {c : Code} (q : TM2.Stmt (fun _ : K' => Γ') Λ' (Option Γ'))
 (h : TM2.SupportsStmt (S c) q) (v : Option Γ') (A : K' → List Γ') :
 let d := TM2.stepAux q v A
 ∀ hd : d.l ∈ Finset.insertNone (S c),
   TM2.stepAux (liftQ q h) v (ws [] [] A) =
     ⟨labOf d.l hd, d.var, ws [] [] d.stk⟩ := by
  induction q generalizing v A with
  | push k f t ih =>
      dsimp
      intro hd
      convert (ih h v (Function.update A k (f v :: A k)) hd) using 1 <;> simp only [liftQ, List.head?, List.tail, Option.isSome, Option.map, Option.getD, TM2.stepAux, up_r, ws_r] <;> try {rfl}
  | peek k f t ih =>
      dsimp; intro hd
      convert (ih h (f v (A k).head?) A hd) using 1 <;> simp only [liftQ, List.head?, List.tail, Option.isSome, Option.map, Option.getD, TM2.stepAux, ws_r] <;> try {rfl}
  | pop k f t ih =>
      dsimp; intro hd
      convert (ih h (f v (A k).head?) (Function.update A k (A k).tail) hd) using 1 <;> simp only [liftQ, List.head?, List.tail, Option.isSome, Option.map, Option.getD, TM2.stepAux, up_r, ws_r] <;> try {rfl}
  | load f t ih =>
      dsimp; intro hd
      simpa only [liftQ, List.head?, List.tail, Option.isSome, Option.map, Option.getD, TM2.stepAux] using (ih h (f v) A hd)
  | branch f t u it iu =>
      cases e : f v
      · dsimp
        intro hd
        simpa only [liftQ, List.head?, List.tail, Option.isSome, Option.map, Option.getD, TM2.stepAux, e, cond_false] using (iu h.2 v A (by simpa only [List.head?, List.tail, Option.isSome, Option.map, Option.getD, TM2.stepAux, e, cond_false] using hd))
      · dsimp
        intro hd
        simpa only [liftQ, List.head?, List.tail, Option.isSome, Option.map, Option.getD, TM2.stepAux, e, cond_true] using (it h.1 v A (by simpa only [List.head?, List.tail, Option.isSome, Option.map, Option.getD, TM2.stepAux, e, cond_true] using hd))
  | goto g =>
      dsimp
      intro hd
      change (⟨some (Sum.inr ⟨g v, h v⟩), v, ws [] [] A⟩ : TM2.Cfg WG (Lab c) _) = _
      rfl
  | halt =>
      dsimp
      intro hd
      rfl

theorem coreclosed {c : Code} {d d' : TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ')}
 (hl : d.l ∈ Finset.insertNone (S c)) (st : d' ∈ TM2.step tr d) :
 d'.l ∈ Finset.insertNone (S c) := by
 letI : Inhabited Λ' := ⟨trNormal c Cont'.halt⟩
 exact TM2.step_supports tr (tr_supports c Cont'.halt) st hl

theorem corestep {c : Code} {d d' : TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ')}
 (hl : d.l ∈ Finset.insertNone (S c)) (st : d' ∈ TM2.step tr d) :
 (machine c).step (emb d hl) = some (emb d' (coreclosed hl st)) := by
  classical
  rcases d with ⟨l,v,A⟩
  cases l with
  | none => simp [TM2.step] at st
  | some q =>
   have qmem : q ∈ S c := by simpa using hl
   change some (TM2.stepAux (liftQ (tr q) _) v (ws [] [] A)) = _
   have ed : d' = TM2.stepAux (tr q) v A := by simpa [TM2.step] using st.symm
   subst d'
   have au := lift_aux (c:=c) (tr q) ((tr_supports c Cont'.halt).2 q qmem)
       v A (coreclosed hl st)
   congr 1

def WR {c : Code} := StateTransition.Reaches (machine c).step

theorem corerun {c : Code} {a b : TM2.Cfg (fun _ : K' => Γ') Λ' (Option Γ')}
 (r : StateTransition.Reaches (TM2.step tr) a b) :
 ∀ ha : a.l ∈ Finset.insertNone (S c),
 ∃ hb : b.l ∈ Finset.insertNone (S c), WR (c:=c) (emb a ha) (emb b hb) := by
 induction r with
 | refl => intro ha; exact ⟨ha, Relation.ReflTransGen.refl⟩
 | @tail b d r st ih =>
   intro ha
   obtain ⟨hb, rr⟩ := ih ha
   have hh := coreclosed hb st
   exact ⟨hh, Relation.ReflTransGen.tail rr (corestep hb st)⟩

noncomputable def wcfg {c : Code} (i : Lab c) (v : Option Γ')
 (xi xo : List Bool) (A : K' → List Γ') : (machine c).Cfg :=
 ⟨some i, v, ws xi xo A⟩

def kk (a b d e : List Γ') := K'.elim a b d e

-- convenient one step reach
 theorem wr_one {c : Code} {a b : (machine c).Cfg} (h : (machine c).step a = some b) : WR a b :=
 Relation.ReflTransGen.single h
 theorem wr_trans {c : Code} {a b d : (machine c).Cfg} : WR a b → WR b d → WR a d :=
 Relation.ReflTransGen.trans


end TuringRecForward

end
-- END INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Forward.lean

-- BEGIN INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Loop.lean
section
open Computability
open StateTransition
namespace TuringRecSupport

/-- Running a computable deterministic step function to its final state is partial recursive. -/
theorem eval_partrec {α : Type*} [Primcodable α]
    (step : α → Option α) (h : Computable step) :
    Partrec (StateTransition.eval step) := by
  -- the body defining `eval` is partial-recursive, and `Partrec.fix` performs
  -- the unbounded loop.  It is useful not to choose a time bound.
  let go : α → α ⊕ α := fun a => (step a).elim (Sum.inl a) (fun b => Sum.inr b)
  have hg : Computable go := by
    -- case analysis on the result of a computable option
    
    have hh := Computable.option_casesOn h (Computable.sumInl) (Computable.sumInr.comp Computable.snd).to₂
    exact hh.of_eq (fun a => by unfold go; cases step a <;> rfl)
  have hp0 : Partrec (go : α →. (α ⊕ α)) := hg.partrec
  have hp : Partrec (fun a => Part.some (go a)) :=
    hp0.of_eq (fun a => by rfl)
  simpa [StateTransition.eval, go] using (Partrec.fix hp)

end TuringRecSupport
namespace TuringRecSupport
/-- A convenient total form of `eval_partrec`: once a total input initializer and an
output reader have been supplied, the values certified to be produced by `eval` are
computable.  The hypothesis is only membership, so it also applies when it was
proved by `eval`/reachability lemmas. -/
theorem computable_of_eval {ι α β : Type*}
    [Primcodable ι] [Primcodable α] [Primcodable β]
    (step : α → Option α) (hs : Computable step)
    (init : ι → α) (hi : Computable init)
    (out : α → β) (ho : Computable out)
    (F : ι → β)
    (hF : ∀ i, F i ∈ Part.map out (StateTransition.eval step (init i))) :
    Computable F := by
  have he : Partrec (StateTransition.eval step) := eval_partrec step hs
  have he' : Partrec (fun i => StateTransition.eval step (init i)) := he.comp hi
  have hm : Partrec (fun i => Part.map out (StateTransition.eval step (init i))) :=
    he'.map (ho.comp Computable.snd).to₂
  exact hm.of_eq_tot hF
end TuringRecSupport

end
-- END INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Loop.lean

-- BEGIN INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Forward2.lean
section
open Turing StateTransition Function
open Turing.PartrecToTM2 Turing.ToPartrec
namespace TuringRecForward

 theorem step0_cons {c : Code} (v : Option Γ') (b : Bool) (xs xo : List Bool)
    (M R U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (0:Fin 4)) v (b::xs) xo (kk M R U T)) =
    some (wcfg (Sum.inl (0:Fin 4)) (some (bitcell b)) xs xo
      (kk M (bitcell b :: R) U T)) := by
  classical
  cases b <;>
    simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail, Option.isSome, Option.map, Option.getD, ws, kk, bitcell]
  all_goals congr 1
  all_goals congr 1
  all_goals funext k
  all_goals rcases k with x|x
  all_goals cases x <;> simp [Function.update, ws]
  all_goals rfl

 theorem step0_nil {c : Code} (v : Option Γ') (xo : List Bool)
    (M R U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (0:Fin 4)) v [] xo (kk M R U T)) =
    some (wcfg (Sum.inl (1:Fin 4)) none [] xo
      (kk (Γ'.cons :: M) R U T)) := by
  classical
  simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail, Option.isSome, Option.map, Option.getD, ws, kk]
  congr 1
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem step1_cons {c : Code} (v : Option Γ') (d : Γ') (ys : List Γ')
    (xi xo : List Bool) (M U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (1:Fin 4)) v xi xo (kk M (d::ys) U T)) =
    some (wcfg (Sum.inl (1:Fin 4)) (some d) xi xo (kk (d::M) ys U T)) := by
  classical
  simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail,
    Option.isSome, Option.map, Option.getD, ws, kk]
  congr 1
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem step1_nil {c : Code} (v : Option Γ') (xi xo : List Bool)
    (M U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (1:Fin 4)) v xi xo (kk M [] U T)) =
    some (wcfg (Sum.inr (q0 c)) none xi xo (kk M [] U T)) := by
  classical
  simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail,
    Option.isSome, Option.map, Option.getD, ws, kk]
  congr 1
  -- label proof maybe
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem run0 {c : Code} (v : Option Γ') (xs : List Bool) (xo : List Bool)
    (M R U T : List Γ') :
   WR (c:=c) (wcfg (Sum.inl (0:Fin 4)) v xs xo (kk M R U T))
     (wcfg (Sum.inl (1:Fin 4)) none [] xo
       (kk (Γ'.cons :: M) ((xs.map bitcell).reverse ++ R) U T)) := by
  induction xs generalizing v R with
  | nil =>
    simpa using (wr_one (step0_nil (c:=c) v xo M R U T))
  | cons b xs ih =>
    refine wr_trans (wr_one (step0_cons (c:=c) v b xs xo M R U T)) ?_
    simpa [List.map, List.reverse_cons, List.append_assoc] using
      (ih (v:= some (bitcell b)) (R := bitcell b :: R))

 theorem run1 {c : Code} (v : Option Γ') (ys : List Γ') (xi xo : List Bool)
    (M U T : List Γ') :
   WR (c:=c) (wcfg (Sum.inl (1:Fin 4)) v xi xo (kk M ys U T))
     (wcfg (Sum.inr (q0 c)) none xi xo (kk (ys.reverse ++ M) [] U T)) := by
  induction ys generalizing v M with
  | nil =>
    simpa using (step1_nil (c:=c) v xi xo M U T |> wr_one)
  | cons d ys ih =>
    refine wr_trans (wr_one (step1_cons (c:=c) v d ys xi xo M U T)) ?_
    simpa [List.reverse_cons, List.append_assoc] using
      (ih (v:= some d) (M:= d :: M))

 theorem bitcell_encode (n : ℕ) : (Computability.encodeNat n).map bitcell = trNat n := by
  have pos : ∀ p : PosNum, (Computability.encodePosNum p).map bitcell = trPosNum p := by
    intro p; induction p with
    | one => rfl
    | bit0 p ih => simpa [Computability.encodePosNum, trPosNum, bitcell] using congrArg (fun l => Γ'.bit0 :: l) ih
    | bit1 p ih => simpa [Computability.encodePosNum, trPosNum, bitcell] using congrArg (fun l => Γ'.bit1 :: l) ih
  unfold Computability.encodeNat trNat
  -- transport through Num
  generalize (n : Num) = z
  cases z with
  | zero => rfl
  | pos p => simpa [Computability.encodeNum, trNum] using pos p

 theorem initList_eq {c : Code} (xs : List Bool) :
   Turing.initList (machine c) xs =
    wcfg (Sum.inl (0:Fin 4)) none xs [] (kk [] [] [] []) := by
  classical
  unfold Turing.initList
  -- reduce record equality to stacks
  change ({ l := _, var := _, stk := _ } : (machine c).Cfg) = _
  -- expose
  simp [wcfg, machine]
  congr 1
  funext k
  rcases k with b|k
  · cases b <;> simp [ws, kk] <;> rfl
  · cases k <;> simp [ws, kk] <;> rfl

 theorem emb_init (c : Code) (n : ℕ) :
   emb (c:=c) (PartrecToTM2.init c [n]) (by simpa [PartrecToTM2.init] using q0mem c) =
    wcfg (Sum.inr (q0 c)) none [] [] (kk (trList [n]) [] [] []) := by
  classical
  -- records; label subtype proof irrelevant
  simp [emb, PartrecToTM2.init, wcfg, labOf, kk, q0]
  congr 4

 theorem prerun (c : Code) (n : ℕ) :
   WR (c:=c) (Turing.initList (machine c) (Computability.encodeNat n))
     (emb (c:=c) (PartrecToTM2.init c [n])
       (by simpa [PartrecToTM2.init] using q0mem c)) := by
  rw [initList_eq, emb_init]
  refine wr_trans (run0 (c:=c) none (Computability.encodeNat n) [] [] [] [] []) ?_
  simpa [bitcell_encode, trList, List.append_assoc] using
    (run1 (c:=c) none ((Computability.encodeNat n).map bitcell |>.reverse)
      [] [] [Γ'.cons] [] [])

 theorem step2_b0 {c : Code} (v : Option Γ') (xi xo : List Bool)
    (M R U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (2:Fin 4)) v xi xo (kk (Γ'.bit0 :: M) R U T)) =
    some (wcfg (Sum.inl (2:Fin 4)) (some Γ'.bit0) xi xo
      (kk M (Γ'.bit0 :: R) U T)) := by
  classical
  simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail,
    Option.isSome, Option.map, Option.getD, ws, kk]
  dsimp [WG]
  simp [show (some Γ'.bit0 : Option Γ') = some Γ'.bit0 from rfl,
    show (some Γ'.bit0 : Option Γ') ≠ some Γ'.bit1 by decide]
  congr 1
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem step2_b1 {c : Code} (v : Option Γ') (xi xo : List Bool)
    (M R U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (2:Fin 4)) v xi xo (kk (Γ'.bit1 :: M) R U T)) =
    some (wcfg (Sum.inl (2:Fin 4)) (some Γ'.bit1) xi xo
      (kk M (Γ'.bit1 :: R) U T)) := by
  classical
  simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail,
    Option.isSome, Option.map, Option.getD, ws, kk]
  dsimp [WG]
  simp [show (some Γ'.bit1 : Option Γ') ≠ some Γ'.bit0 by decide,
    show (some Γ'.bit1 : Option Γ') = some Γ'.bit1 from rfl]
  congr 1
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem step2_end {c : Code} (v : Option Γ') (xi xo : List Bool)
    (M R U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (2:Fin 4)) v xi xo (kk (Γ'.cons :: M) R U T)) =
    some (wcfg (Sum.inl (3:Fin 4)) (some Γ'.cons) xi xo (kk M R U T)) := by
  classical
  simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail,
    Option.isSome, Option.map, Option.getD, ws, kk]
  dsimp [WG]
  simp [show (some Γ'.cons : Option Γ') ≠ some Γ'.bit0 by decide,
    show (some Γ'.cons : Option Γ') ≠ some Γ'.bit1 by decide]
  congr 1
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem run2 {c : Code} (v : Option Γ') (bs : List Bool) (xi xo : List Bool)
    (M R U T : List Γ') :
   WR (c:=c) (wcfg (Sum.inl (2:Fin 4)) v xi xo
       (kk (bs.map bitcell ++ Γ'.cons :: M) R U T))
     (wcfg (Sum.inl (3:Fin 4)) (some Γ'.cons) xi xo
       (kk M ((bs.map bitcell).reverse ++ R) U T)) := by
  induction bs generalizing v R with
  | nil => simpa using (wr_one (step2_end (c:=c) v xi xo M R U T))
  | cons b bs ih =>
    cases b with
    | false =>
      refine wr_trans (wr_one (step2_b0 (c:=c) v xi xo
        (bs.map bitcell ++ Γ'.cons :: M) R U T)) ?_
      simpa [bitcell, List.reverse_cons, List.append_assoc] using
        (ih (v:=some Γ'.bit0) (R:= Γ'.bit0 :: R))
    | true =>
      refine wr_trans (wr_one (step2_b1 (c:=c) v xi xo
        (bs.map bitcell ++ Γ'.cons :: M) R U T)) ?_
      simpa [bitcell, List.reverse_cons, List.append_assoc] using
        (ih (v:=some Γ'.bit1) (R:= Γ'.bit1 :: R))

 noncomputable def wend {c : Code} (xi xo : List Bool) (M U T : List Γ') : (machine c).Cfg :=
  ⟨none, none, ws xi xo (kk M [] U T)⟩

 theorem step3_b0 {c : Code} (v : Option Γ') (xi xo : List Bool)
    (M R U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (3:Fin 4)) v xi xo (kk M (Γ'.bit0 :: R) U T)) =
    some (wcfg (Sum.inl (3:Fin 4)) (some Γ'.bit0) xi (false :: xo)
      (kk M R U T)) := by
  classical
  simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail,
    Option.isSome, Option.map, Option.getD, ws, kk]
  dsimp [WG]
  simp [show (some Γ'.bit0 : Option Γ') ≠ some Γ'.bit1 by decide]
  congr 1
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem step3_b1 {c : Code} (v : Option Γ') (xi xo : List Bool)
    (M R U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (3:Fin 4)) v xi xo (kk M (Γ'.bit1 :: R) U T)) =
    some (wcfg (Sum.inl (3:Fin 4)) (some Γ'.bit1) xi (true :: xo)
      (kk M R U T)) := by
  classical
  simp [FinTM2.step, wcfg, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail,
    Option.isSome, Option.map, Option.getD, ws, kk]
  dsimp [WG]
  simp [show (some Γ'.bit1 : Option Γ') = some Γ'.bit1 from rfl]
  congr 1
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem step3_nil {c : Code} (v : Option Γ') (xi xo : List Bool)
    (M U T : List Γ') :
   (machine c).step (wcfg (Sum.inl (3:Fin 4)) v xi xo (kk M [] U T)) =
    some (wend (c:=c) xi xo M U T) := by
  classical
  simp [FinTM2.step, wcfg, wend, machine, wm, TM2.step, TM2.stepAux, List.head?, List.tail,
    Option.isSome, Option.map, Option.getD, ws, kk]
  congr 1
  congr 1
  funext k
  rcases k with x|x
  · cases x <;> simp [Function.update, ws] <;> rfl
  · cases x <;> simp [Function.update, ws] <;> rfl

 theorem run3 {c : Code} (v : Option Γ') (ls : List Bool) (xi xo : List Bool)
    (M U T : List Γ') :
   WR (c:=c) (wcfg (Sum.inl (3:Fin 4)) v xi xo
       (kk M (ls.map bitcell) U T))
     (wend (c:=c) xi (ls.reverse ++ xo) M U T) := by
  induction ls generalizing v xo with
  | nil => simpa using (wr_one (step3_nil (c:=c) v xi xo M U T))
  | cons b ls ih =>
    cases b with
    | false =>
      refine wr_trans (wr_one (step3_b0 (c:=c) v xi xo M (ls.map bitcell) U T)) ?_
      simpa [bitcell, List.reverse_cons, List.append_assoc] using
        (ih (v:=some Γ'.bit0) (xo := false :: xo))
    | true =>
      refine wr_trans (wr_one (step3_b1 (c:=c) v xi xo M (ls.map bitcell) U T)) ?_
      simpa [bitcell, List.reverse_cons, List.append_assoc] using
        (ih (v:=some Γ'.bit1) (xo := true :: xo))

 theorem emb_halt (c : Code) (n : ℕ) (h :
    (PartrecToTM2.halt [n]).l ∈ Finset.insertNone (S c)) :
   emb (c:=c) (PartrecToTM2.halt [n]) h =
    wcfg (Sum.inl (2:Fin 4)) none [] [] (kk (trList [n]) [] [] []) := by
  classical
  simp [emb, PartrecToTM2.halt, wcfg, labOf, kk]
  congr 4

 theorem haltList_eq {c : Code} (bs : List Bool) :
   Turing.haltList (machine c) bs = wend (c:=c) [] bs [] [] [] := by
  classical
  unfold Turing.haltList
  change ({ l := _, var := _, stk := _ } : (machine c).Cfg) = _
  simp [wend, machine]
  congr 1
  funext k
  rcases k with b|k
  · cases b <;> simp [ws, kk] <;> rfl
  · cases k <;> simp [ws, kk] <;> rfl

 theorem postrun (c : Code) (n : ℕ)
   (h : (PartrecToTM2.halt [n]).l ∈ Finset.insertNone (S c)) :
   WR (c:=c) (emb (c:=c) (PartrecToTM2.halt [n]) h)
     (Turing.haltList (machine c) (Computability.encodeNat n)) := by
  rw [emb_halt, haltList_eq]
  refine @wr_trans c _ (wcfg (Sum.inl (3:Fin 4)) (some Γ'.cons) [] []
        (kk [] ((Computability.encodeNat n).map bitcell |>.reverse) [] [])) _ ?_ ?_
  · simpa [bitcell_encode, trList] using
      (run2 (c:=c) none (Computability.encodeNat n) [] [] [] [] [] [])
  · -- reverse bits sit on rev
    simpa [List.map_reverse, List.append_assoc] using
      (run3 (c:=c) (some Γ'.cons) (Computability.encodeNat n).reverse [] [] [] [] [])

 theorem coderun {c : Code} {n m : ℕ} (hv : [m] ∈ c.eval [n]) :
   ∃ hb : (PartrecToTM2.halt [m]).l ∈ Finset.insertNone (S c),
    WR (c:=c)
      (emb (c:=c) (PartrecToTM2.init c [n])
        (by simpa [PartrecToTM2.init] using q0mem c))
      (emb (c:=c) (PartrecToTM2.halt [m]) hb) := by
  have mem : PartrecToTM2.halt [m] ∈
      StateTransition.eval (TM2.step PartrecToTM2.tr)
        (PartrecToTM2.init c [n]) := by
    rw [PartrecToTM2.tr_eval]
    exact (Part.mem_map_iff _).2 ⟨[m], hv, rfl⟩
  have rr : StateTransition.Reaches (TM2.step PartrecToTM2.tr)
       (PartrecToTM2.init c [n]) (PartrecToTM2.halt [m]) :=
    (StateTransition.mem_eval.1 mem).1
  exact corerun rr (by simpa [PartrecToTM2.init] using q0mem c)

 theorem reachall {c : Code} {n m : ℕ} (hv : [m] ∈ c.eval [n]) :
   WR (c:=c) (Turing.initList (machine c) (Computability.encodeNat n))
     (Turing.haltList (machine c) (Computability.encodeNat m)) := by
  obtain ⟨hb, rr⟩ := coderun (c:=c) hv
  exact wr_trans (prerun c n) (wr_trans rr (postrun c m hb))

 noncomputable def reaches_evals {α : Type*} {g : α → Option α} {a b : α}
   (r : StateTransition.Reaches g a b) :
   StateTransition.EvalsTo g a (some b) := by
  classical
  have ex : ∃ k : ℕ, ((flip bind g)^[k]) a = some b := by
    induction r with
    | refl => exact ⟨0, rfl⟩
    | @tail b d r h ih =>
      obtain ⟨k, hk⟩ := ih
      refine ⟨k+1, ?_⟩
      rw [Function.iterate_succ_apply', hk]
      change g b = some d
      exact h
  exact ⟨Classical.choose ex, Classical.choose_spec ex⟩

end TuringRecForward

end
-- END INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Forward2.lean

-- BEGIN INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Uniform.lean
section
open Computability Turing
open Function
namespace TuringRecSupport
/- A flat representation of a fixed finite collection of (uniform) stacks.  Keeping a
single tagged list is convenient for recursion theory: all the datatypes which occur
in it are `Primcodable`.  The order between distinct colours is immaterial. -/
section
variable {K Γ : Type*} [DecidableEq K]

def uget (k : K) (L : List (K × Γ)) : List Γ :=
  (L.filter (fun z => decide (z.1 = k))).map Prod.snd

def uerase (k : K) (L : List (K × Γ)) : List (K × Γ) :=
  L.filter (fun z => decide (z.1 ≠ k))

def uput (k : K) (xs : List Γ) (L : List (K × Γ)) : List (K × Γ) :=
  xs.map (fun x => (k,x)) ++ uerase k L

@[simp] theorem uget_put_eq (k : K) (xs : List Γ) (L : List (K × Γ)) :
    uget k (uput k xs L) = xs := by
  have A : List.map Prod.snd
      (List.filter (fun z : K × Γ => decide (z.1 = k))
        (List.map (fun x : Γ => (k,x)) xs)) = xs := by
    induction xs with
    | nil => rfl
    | cons a t ih => simp [ih]
  -- every `k` was removed from the old part
  have B : List.filter (fun z : K × Γ => decide (z.1 = k))
      (List.filter (fun z : K × Γ => decide (z.1 ≠ k)) L) = [] := by
    induction L with
    | nil => rfl
    | cons z t ih =>
      rcases z with ⟨j,a⟩
      by_cases e : j = k <;> simp [e, ih]
  simp [uget, uput, uerase, List.filter_append, A, B]

@[simp] theorem uget_put_ne {j k : K} (h : j ≠ k) (xs : List Γ) (L : List (K × Γ)) :
    uget j (uput k xs L) = uget j L := by
  have A : List.filter (fun z : K × Γ => decide (z.1 = j))
        (List.map (fun x : Γ => (k,x)) xs) = [] := by
    induction xs with
    | nil => rfl
    | cons a t ih =>
      have kh : k ≠ j := Ne.symm h
      simpa [kh] using ih
  have B : List.filter (fun z : K × Γ => decide (z.1 = j))
      (List.filter (fun z : K × Γ => decide (z.1 ≠ k)) L) =
      List.filter (fun z : K × Γ => decide (z.1 = j)) L := by
    induction L with
    | nil => rfl
    | cons z t ih =>
      rcases z with ⟨i,a⟩
      simp only [List.filter_filter, decide_not] at ih
      by_cases e : i = k
      · subst i
        have kj : k ≠ j := Ne.symm h
        simp [kj, ih]
      · by_cases e' : i = j
        · subst i
          simp [h, ih]
        · simp [e, e', ih]
  simp only [uget, uput, uerase, List.filter_append, List.map_append]
  rw [A, B]
  simp

end
section
variable {K Γ : Type*} [DecidableEq K]
variable [Primcodable K] [Primcodable Γ]

/-- Reading a fixed colour from the tagged list is primitive recursive. -/
theorem prim_uget (k : K) : Primrec (uget (Γ:=Γ) k) := by
  have p : PrimrecPred (fun z : K × Γ => z.1 = k) :=
    Primrec.eq.comp Primrec.fst (Primrec.const k)
  have filt : Primrec (fun L : List (K × Γ) => L.filter (fun z => decide (z.1 = k))) :=
    Primrec.listFilter p
  exact Primrec.list_map filt (Primrec.snd.comp Primrec.snd).to₂ -- adjust

/-- Dropping a colour is primitive recursive. -/
theorem prim_uerase (k : K) : Primrec (uerase (Γ:=Γ) k) := by
  have p : PrimrecPred (fun z : K × Γ => ¬ z.1 = k) :=
    (Primrec.eq.comp Primrec.fst (Primrec.const k)).not
  exact Primrec.listFilter p

theorem prim_uput (k : K) :
    Primrec₂ (uput (Γ:=Γ) k) := by
  -- map the fresh stack to tagged letters
  have tag : Primrec (fun x : Γ => (k,x)) :=
    (Primrec.const k).pair Primrec.id
  have tags : Primrec (fun xs : List Γ => xs.map (fun x => (k,x))) :=
    Primrec.list_map Primrec.id (tag.comp Primrec.snd).to₂
  exact (Primrec.list_append.comp (tags.comp Primrec.fst) ((prim_uerase (Γ:=Γ) k).comp Primrec.snd)).to₂
    |>.of_eq (fun _ _ => rfl)
end
end TuringRecSupport

namespace TuringRecSupport
open Turing.TM2
section uniform
variable {K Γ S Lb : Type*} [DecidableEq K]

abbrev UState (K Γ S : Type*) := S × List (K × Γ)
abbrev UCfg (K Γ S Lb : Type*) := (Option Lb × S) × List (K × Γ)

def uaux : TM2.Stmt (fun _ : K => Γ) Lb S → UState K Γ S → UCfg K Γ S Lb
 | .push k f q, z => uaux q (z.1, uput k (f z.1 :: uget k z.2) z.2)
 | .peek k f q, z => uaux q (f z.1 (uget k z.2).head?, z.2)
 | .pop k f q, z =>
      uaux q (f z.1 (uget k z.2).head?, uput k (uget k z.2).tail z.2)
 | .load f q, z => uaux q (f z.1, z.2)
 | .branch f q₁ q₂, z => cond (f z.1) (uaux q₁ z) (uaux q₂ z)
 | .goto f, z => ((some (f z.1), z.1), z.2)
 | .halt, z => ((none, z.1), z.2)

variable [Primcodable K] [Primcodable Γ] [Primcodable S] [Primcodable Lb]
variable [Finite S] [Finite Γ]

private theorem __Uniform_prim_head (k : K) :
    Primrec (fun z : UState K Γ S => (uget k z.2).head?) :=
  Primrec.list_head?.comp ((prim_uget (Γ:=Γ) k).comp Primrec.snd)
private theorem __Uniform_prim_tail (k : K) :
    Primrec (fun z : UState K Γ S => (uget k z.2).tail) :=
  Primrec.list_tail.comp ((prim_uget (Γ:=Γ) k).comp Primrec.snd)

/-- The (bounded, single-statement) evaluator of a uniform finite alphabet stack program
is primitive recursive on the flat stack representation. Notice that we only need
`Finite S`, not an enumeration of the transition tables: every table in a statement
has finite domain. -/
theorem prim_uaux (q : TM2.Stmt (fun _ : K => Γ) Lb S) :
    Primrec (uaux q) := by
  induction q with
  | @push k f q ih =>
    have pf : Primrec f := Primrec.dom_finite f
    have xs : Primrec (fun z : UState K Γ S => f z.1 :: uget k z.2) :=
      Primrec.list_cons.comp (pf.comp Primrec.fst) ((prim_uget (Γ:=Γ) k).comp Primrec.snd)
    have st : Primrec (fun z : UState K Γ S =>
          (z.1, uput k (f z.1 :: uget k z.2) z.2)) :=
      Primrec.fst.pair ((prim_uput (Γ:=Γ) k).comp xs Primrec.snd)
    exact (ih.comp st).of_eq (fun z => rfl)
  | peek k f q ih =>
    have pf : Primrec₂ f :=
      (Primrec.dom_finite (fun z : S × (Option Γ) => f z.1 z.2)).to₂
    have nv : Primrec (fun z : UState K Γ S => f z.1 (uget k z.2).head?) :=
      pf.comp Primrec.fst (__Uniform_prim_head k)
    exact (ih.comp (nv.pair Primrec.snd)).of_eq (fun z => rfl)
  | pop k f q ih =>
    have pf : Primrec₂ f :=
      (Primrec.dom_finite (fun z : S × (Option Γ) => f z.1 z.2)).to₂
    have nv : Primrec (fun z : UState K Γ S => f z.1 (uget k z.2).head?) :=
      pf.comp Primrec.fst (__Uniform_prim_head k)
    have st : Primrec (fun z : UState K Γ S =>
        (f z.1 (uget k z.2).head?, uput k (uget k z.2).tail z.2)) :=
      nv.pair ((prim_uput (Γ:=Γ) k).comp (__Uniform_prim_tail k) Primrec.snd)
    exact (ih.comp st).of_eq (fun z => rfl)
  | load f q ih =>
    exact (ih.comp ((Primrec.dom_finite f |>.comp Primrec.fst).pair Primrec.snd)).of_eq
      (fun z => rfl)
  | branch f q₁ q₂ ih₁ ih₂ =>
    exact (Primrec.cond ((Primrec.dom_finite f).comp Primrec.fst) ih₁ ih₂).of_eq
      (fun z => by cases h : f z.1 <;> simp [uaux, h])
  | goto f =>
    exact (((Primrec.option_some.comp ((Primrec.dom_finite f).comp Primrec.fst)).pair
      Primrec.fst).pair Primrec.snd)
  | halt =>
    exact (((Primrec.const (none : Option Lb)).pair Primrec.fst).pair Primrec.snd)
end uniform
end TuringRecSupport
namespace TuringRecSupport
open Computability
/-- A useful way to compile a finite jump table. The entries need not be given in any
particular order. -/
theorem prim_finite_dispatch {ι α β : Type*}
    [Primcodable ι] [Primcodable α] [Primcodable β]
    [Finite ι] [Inhabited β]
    (g : ι → α → β) (hg : ∀ i, Primrec (g i)) :
    Primrec (fun z : ι × α => g z.1 z.2) := by
  classical
  obtain ⟨l, _, hl⟩ := Finite.exists_univ_list ι
  have aux : ∀ l : List ι,
      Primrec (fun z : ι × α => if z.1 ∈ l then g z.1 z.2 else default) := by
    intro l; induction l with
    | nil => simpa using (Primrec.const (α:=ι×α) (default : β))
    | cons i t ih =>
      have eqi : PrimrecPred (fun z : ι × α => z.1 = i) :=
        Primrec.eq.comp Primrec.fst (Primrec.const i)
      have branch : Primrec (fun z : ι × α => if z.1 = i then g i z.2
            else if z.1 ∈ t then g z.1 z.2 else default) :=
        Primrec.ite eqi ((hg i).comp Primrec.snd) ih
      exact branch.of_eq (fun z => by by_cases e : z.1 = i <;> simp [e])
  exact (aux l).of_eq (fun z => by simp [hl z.1])

open Turing.TM2
section
variable {K Γ S Lb : Type*} [DecidableEq K]
variable [Primcodable K] [Primcodable Γ] [Primcodable S] [Primcodable Lb]
variable [Inhabited S] [Finite S] [Finite Γ] [Finite Lb]

/-- The outer (one-label) step on flat uniform configurations. -/
def ustep (m : Lb → TM2.Stmt (fun _ : K => Γ) Lb S) :
    UCfg K Γ S Lb → Option (UCfg K Γ S Lb)
  | ((none, _), _) => none
  | ((some l, v), T) => some (uaux (m l) (v,T))

theorem prim_ustep (m : Lb → TM2.Stmt (fun _ : K => Γ) Lb S) :
    Primrec (ustep m) := by
  let body : Lb → UState K Γ S → UCfg K Γ S Lb := fun l => uaux (m l)
  have btab : Primrec (fun z : Lb × UState K Γ S => body z.1 z.2) :=
    prim_finite_dispatch body (fun i => prim_uaux (m i))
  have getl : Primrec (fun z : UCfg K Γ S Lb => z.1.1) := Primrec.fst.comp Primrec.fst
  have vv : Primrec (fun z : UCfg K Γ S Lb => (z.1.2,z.2)) :=
    (Primrec.snd.comp Primrec.fst).pair Primrec.snd
  have somecase : Primrec₂ (fun z : UCfg K Γ S Lb => fun l =>
      some (body l (z.1.2,z.2))) :=
    (Primrec.option_some.comp
      (btab.comp (Primrec.snd.pair (vv.comp Primrec.fst)))).to₂.of_eq (fun _ _ => rfl)
  exact (Primrec.option_casesOn getl (Primrec.const none) somecase).of_eq
    (fun z => by rcases z with ⟨⟨l,v⟩,T⟩; cases l <;> rfl)
end
end TuringRecSupport

end
-- END INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Uniform.lean

-- BEGIN INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Bridge.lean
section
open Computability Turing
open StateTransition Function
namespace TuringRecSupport
open Turing.TM2
section Hom
variable {K Γ V Lb : Type*} [DecidableEq K]

/-- agreement between a native homogeneous TM2 stack family and the flat tagged list -/
def RelStk (A : K → List Γ) (T : List (K × Γ)) : Prop :=
  ∀ k, A k = uget k T

def RelCfg (c : TM2.Cfg (fun _ : K => Γ) Lb V) (d : UCfg K Γ V Lb) : Prop :=
  c.l = d.1.1 ∧ c.var = d.1.2 ∧ RelStk c.stk d.2

theorem rel_update (A : K → List Γ) (T : List (K × Γ)) (k : K) (xs : List Γ)
    (h : RelStk A T) :
    RelStk (Function.update A k xs) (uput k xs T) := by
  intro j
  classical
  by_cases e : j = k
  · subst j; simp [Function.update_self, uget_put_eq]
  · rw [Function.update_of_ne e]
    simpa [uget_put_ne e] using h j

theorem aux_rel (q : TM2.Stmt (fun _ : K => Γ) Lb V) (v : V)
    (A : K → List Γ) (T : List (K × Γ)) (h : RelStk A T) :
    RelCfg (TM2.stepAux q v A) (uaux q (v,T)) := by
  induction q generalizing v A T with
  | push k f q ih =>
      simpa [TM2.stepAux, uaux, h k] using (ih v (Function.update A k (f v :: A k)) (uput k (f v :: A k) T) (rel_update A T k (f v :: A k) h))
  | peek k f q ih =>
      simpa [TM2.stepAux, uaux, h k] using (ih (f v (A k).head?) A T h)
  | pop k f q ih =>
      simpa [TM2.stepAux, uaux, h k] using (ih (f v (A k).head?) (Function.update A k (A k).tail) (uput k (A k).tail T) (rel_update A T k (A k).tail h))
  | load f q ih => exact ih _ _ _ h
  | branch f q₁ q₂ ih₁ ih₂ =>
      cases hf : f v <;> simp [TM2.stepAux, uaux, hf]
      · exact ih₂ _ _ _ h
      · exact ih₁ _ _ _ h
  | goto f => exact ⟨rfl, rfl, h⟩
  | halt => exact ⟨rfl, rfl, h⟩

-- above peek/pop auxiliary need rewriting heads from h; test

theorem step_rel {m : Lb → TM2.Stmt (fun _ : K => Γ) Lb V}
    {c : TM2.Cfg (fun _ : K => Γ) Lb V} {d : UCfg K Γ V Lb}
    (h : RelCfg c d) :
    match TM2.step m c with
    | none => ustep m d = none
    | some c' => ∃ d', ustep m d = some d' ∧ RelCfg c' d' := by
  rcases c with ⟨l,v,A⟩
  rcases d with ⟨⟨l',v'⟩,T⟩
  rcases h with ⟨hl,hv,hT⟩
  dsimp at hl hv hT
  subst l'; subst v'
  cases l with
  | none => simp [TM2.step, ustep]
  | some a =>
      change ∃ d', ustep m ((some a, v), T) = some d' ∧
        RelCfg (TM2.stepAux (m a) v A) d'
      exact ⟨uaux (m a) (v,T), rfl, aux_rel _ _ _ _ hT⟩

/-- Transport a finite native trace to a flat trace, preserving its final relation. -/
theorem iter_rel {m : Lb → TM2.Stmt (fun _ : K => Γ) Lb V}
    {c : TM2.Cfg (fun _ : K => Γ) Lb V} {d : UCfg K Γ V Lb}
    (h : RelCfg c d) : ∀ n c', (flip Option.bind (TM2.step m))^[n] c = some c' →
      ∃ d', (flip Option.bind (ustep m))^[n] d = some d' ∧ RelCfg c' d'
  := by
  intro n
  induction n generalizing c d with
  | zero =>
      intro c' hc
      simp at hc
      subst c'
      exact ⟨d, rfl, h⟩
  | succ n ih =>
      intro c' hc
      -- perform one step first or last? iterate_succ_apply gives iterations after n order
      rw [Function.iterate_succ_apply] at hc ⊢
      -- currently (bind^[n]) (bind c?) ; unfold flip at head?
      -- simp may isolate step c
      cases e : TM2.step m c with
      | none =>
          have zn : ∀ k : ℕ, (flip Option.bind (TM2.step m))^[k] (none : Option (TM2.Cfg (fun _ : K => Γ) Lb V)) = none := by
            intro k; induction k with
            | zero => rfl
            | succ k ik => simp [Function.iterate_succ_apply, flip, ik]
          change (flip Option.bind (TM2.step m))^[n] (TM2.step m c) = some c' at hc
          rw [e, zn n] at hc
          cases hc
      | some c1 =>
          have rr := step_rel (m:=m) h
          rw [e] at rr
          obtain ⟨d1, ed, hd1⟩ := rr
          simp [flip, e] at hc
          -- hc : iterate n c1 = some c'
          obtain ⟨d', hn, hr⟩ := ih hd1 _ hc
          refine ⟨d', ?_, hr⟩
          -- same simplification after one step on flat
          simpa [flip, ed] using hn

theorem reaches_of_iter {α : Type*} (g : α → Option α) :
    ∀ n (a b : α), (flip Option.bind g)^[n] a = some b → StateTransition.Reaches g a b := by
  intro n
  induction n with
  | zero =>
      intro a b h
      have e : a = b := by simpa using h
      subst b
      exact Relation.ReflTransGen.refl
  | succ n ih =>
      intro a b h
      rw [Function.iterate_succ_apply] at h
      change (flip Option.bind g)^[n] (g a) = some b at h
      cases e : g a with
      | none =>
          have zn : ∀ k : ℕ, (flip Option.bind g)^[k] (none : Option α) = none := by
            intro k; induction k with
            | zero => rfl
            | succ k ik => simp [Function.iterate_succ_apply, flip, ik]
          rw [e, zn n] at h
          cases h
      | some a' =>
          have hab : StateTransition.Reaches g a a' :=
            Relation.ReflTransGen.single e
          have h' : (flip Option.bind g)^[n] a' = some b := by simpa [e] using h
          exact hab.trans (ih _ _ h')

/-- Membership in the flat evaluator supplied by a native terminating finite execution. -/
theorem mem_flat_eval {m : Lb → TM2.Stmt (fun _ : K => Γ) Lb V}
    {c : TM2.Cfg (fun _ : K => Γ) Lb V} {d : UCfg K Γ V Lb}
    (rel : RelCfg c d)
    {c' : TM2.Cfg (fun _ : K => Γ) Lb V}
    (run : StateTransition.EvalsTo (TM2.step m) c (some c'))
    (halt : c'.l = none) :
    ∃ d', RelCfg c' d' ∧ d' ∈ StateTransition.eval (ustep m) d := by
  obtain ⟨n, hn⟩ := run
  obtain ⟨d', hd, rd⟩ := iter_rel (m:=m) rel n c' hn
  refine ⟨d', rd, StateTransition.mem_eval.2 ⟨?_, ?_⟩⟩
  · exact reaches_of_iter (ustep m) n d d' hd
  · -- no next step from corresponding halted label
    rcases c' with ⟨l,v,A⟩
    rcases d' with ⟨⟨l',v'⟩,T⟩
    dsimp at halt rd
    obtain ⟨rr,_,_⟩ := rd
    simp [halt] at rr
    subst l'
    rfl

end Hom
end TuringRecSupport

namespace TuringRecSupport
open Turing.TM2
open Computability
open Function
section HomComp
variable {K Γ V Lb ι : Type*} [DecidableEq K]
variable [Primcodable K] [Primcodable Γ] [Primcodable V] [Primcodable Lb]
variable [Finite V] [Finite Γ] [Finite Lb] [Inhabited V]
variable [Primcodable ι]

theorem rel_input (start : Lb) (v0 : V) (k : K) (xs : List Γ) :
    RelCfg (⟨some start, v0, Function.update (fun _ : K => ([] : List Γ)) k xs⟩ :
      TM2.Cfg (fun _ : K => Γ) Lb V)
      (((some start, v0), uput k xs []) : UCfg K Γ V Lb) := by
  refine ⟨rfl, rfl, rel_update (fun _ : K => ([] : List Γ)) ([] : List (K×Γ)) k xs ?_⟩
  intro j
  simp [uget]

theorem computable_homogeneous
    (kin kout : K) (start : Lb) (v0 : V)
    (m : Lb → TM2.Stmt (fun _ : K => Γ) Lb V)
    (inp : ι → List Γ) (hi : Computable inp)
    (F : ι → List Γ)
    (fin : ι → TM2.Cfg (fun _ : K => Γ) Lb V)
    (hrun : ∀ i, StateTransition.EvalsTo (TM2.step m)
          (⟨some start, v0, Function.update (fun _ : K => ([] : List Γ)) kin (inp i)⟩)
          (some (fin i)))
    (hhalt : ∀ i, (fin i).l = none)
    (hval : ∀ i, (fin i).stk kout = F i) :
    Computable F := by
  let ini : ι → UCfg K Γ V Lb := fun i =>
    ((some start, v0), uput kin (inp i) [])
  have pini : Computable ini := by
    dsimp [ini]
    exact ((Computable.const (some start)).pair (Computable.const v0)).pair
      ((prim_uput (Γ:=Γ) kin).to_comp.comp hi (Computable.const []))
  let out : UCfg K Γ V Lb → List Γ := fun d => uget kout d.2
  have pout : Computable out :=
    ((prim_uget (Γ:=Γ) kout).comp Primrec.snd).to_comp
  refine computable_of_eval (ustep m) (prim_ustep m).to_comp ini pini out pout F ?_
  intro i
  obtain ⟨d', rd, hd⟩ := mem_flat_eval (m:=m)
    (rel_input start v0 kin (inp i)) (hrun i) (hhalt i)
  have eqout : out d' = F i := by
    dsimp [out]
    have rs := rd.2.2 kout
    rw [← rs]
    exact hval i
  exact (Part.mem_map_iff out).2 ⟨d', hd, eqout⟩

end HomComp
end TuringRecSupport

end
-- END INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Bridge.lean

-- BEGIN INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/HomNat.lean
section
open Computability Turing Function
open Turing.TM2
namespace TuringRecSupport
section
variable {K V Lb : Type*} [DecidableEq K]
variable [Primcodable K] [Primcodable V] [Primcodable Lb]
variable [Finite V] [Finite Lb] [Inhabited V]
/-- Converse for a homogeneous binary-alphabet finite stack program. Notice the hypothesis
is the `EvalsTo` certificate used by `TM2Outputs`, not a time bound. -/
theorem computable_nat_hom
    (kin kout : K) (start : Lb) (v0 : V)
    (m : Lb → TM2.Stmt (fun _ : K => Bool) Lb V)
    (f : ℕ → ℕ)
    (fin : ℕ → TM2.Cfg (fun _ : K => Bool) Lb V)
    (hrun : ∀ i, StateTransition.EvalsTo (TM2.step m)
       (⟨some start, v0,
         Function.update (fun _ : K => ([] : List Bool)) kin (encodeNat i)⟩)
       (some (fin i)))
    (hhalt : ∀ i, (fin i).l = none)
    (hout : ∀ i, (fin i).stk kout = encodeNat (f i)) :
    Computable f := by
  have lists : Computable (fun i => encodeNat (f i)) :=
    computable_homogeneous kin kout start v0 m encodeNat
      prim_encodeNat.to_comp (fun i => encodeNat (f i)) fin hrun hhalt hout
  exact (prim_bitval.to_comp.comp lists).of_eq (fun n => bitval_encode (f n))
end
end TuringRecSupport

end
-- END INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/HomNat.lean

-- BEGIN INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Hetero.lean
section
open Computability Turing Function
open Turing.TM2
open StateTransition
namespace TuringRecSupport
noncomputable section

/- Finite symbolic alphabet for a heterogeneous stack program.
   A cell is either one of the original input letters, or a reference to a
   syntactic push in the program together with the state in which it was run. -/
section compile
variable {K : Type*} (Γ : K → Type*)

/-- A source of a letter.  There is one such source for each `push` occurrence. -/
abbrev HOcc (σ : Type*) := Σ k, σ → Γ k

variable {Γ}
-- collect occurrences in a statement

def hcollect {Λ σ : Type*} : TM2.Stmt Γ Λ σ → List (HOcc Γ σ)
  | .push k f q => ⟨k,f⟩ :: hcollect q
  | .peek _ _ q => hcollect q
  | .pop _ _ q => hcollect q
  | .load _ q => hcollect q
  | .branch _ q r => hcollect q ++ hcollect r
  | .goto _ => []
  | .halt => []

variable {Λ σ : Type*} [Fintype Λ]
/-- list of all push sites in a finite program -/
def hall (m : Λ → TM2.Stmt Γ Λ σ) : List (HOcc Γ σ) :=
  (Finset.univ : Finset Λ).toList.flatMap (fun l => hcollect (Γ:=Γ) (m l))

lemma hmem_all (m : Λ → TM2.Stmt Γ Λ σ) {l : Λ} {o : HOcc Γ σ}
    (h : o ∈ hcollect (Γ:=Γ) (m l)) : o ∈ hall (Γ:=Γ) m := by
  classical
  unfold hall
  exact (List.mem_flatMap).2 ⟨l, (Finset.mem_toList).2 (Finset.mem_univ _), h⟩

/-- select an index of a given member of a list, without requiring equality on the elements -/
def hidx {α : Type*} (L : List α) (x : α) (h : x ∈ L) : Fin L.length :=
  ⟨Classical.choose ((List.mem_iff_getElem).1 h),
   Classical.choose_spec ((List.mem_iff_getElem).1 h) |>.1⟩

lemma hget_idx {α : Type*} (L : List α) (x : α) (h : x ∈ L) :
    L.get (hidx L x h) = x := by
  classical
  -- both forms of list indexing coincide
  simpa [hidx, List.get_eq_getElem] using
    (Classical.choose_spec (Classical.choose_spec ((List.mem_iff_getElem).1 h))).symm.symm
    -- awkward; revisit
 

section
variable {K Λ σ : Type*} (Γ : K → Type*) [DecidableEq K] [Fintype Λ]
variable (k₀ : K) (m : Λ → TM2.Stmt Γ Λ σ)

/-- the uniform finite alphabet used in the compiled program -/
def HU := (Γ k₀) ⊕ (Fin (hall (Γ:=Γ) m).length × σ)

/-- interpretation of a symbolic letter on a given stack. Ill-coloured letters decode to
`none`; compiled stacks never contain them. -/
def hdec (k : K) : HU Γ k₀ m → Option (Γ k)
  | .inl a => if e : k = k₀ then some (e.symm ▸ a) else none
  | .inr z =>
      let o : HOcc Γ σ := (hall (Γ:=Γ) m).get z.1
      match o with
      | ⟨j,f⟩ => if e : j = k then some (e ▸ f z.2) else none

@[simp] lemma hdec_inl (a : Γ k₀) : hdec Γ k₀ m k₀ (.inl a) = some a := by
  simp [hdec]

/-- symbolic letter emitted by a particular push site -/
def htok {k : K} {f : σ → Γ k}
    (hf : (⟨k,f⟩ : HOcc Γ σ) ∈ hall (Γ:=Γ) m) (v : σ) : HU Γ k₀ m :=
  Sum.inr (hidx _ (⟨k,f⟩ : HOcc Γ σ) hf, v)

@[simp] lemma hdec_tok {k : K} {f : σ → Γ k}
    (hf : (⟨k,f⟩ : HOcc Γ σ) ∈ hall (Γ:=Γ) m) (v : σ) :
    hdec Γ k₀ m k (htok Γ k₀ m hf v) = some (f v) := by
  classical
  have hx : (hall (Γ:=Γ) m).get (hidx _ (⟨k,f⟩ : HOcc Γ σ) hf) = (⟨k,f⟩ : HOcc Γ σ) := hget_idx _ _ hf
  change (match (hall (Γ:=Γ) m).get (hidx _ (⟨k,f⟩ : HOcc Γ σ) hf) with
      | ⟨j,g⟩ => dite (j = k) (fun e => some (e ▸ g v)) (fun _ => none)) = some (f v)
  rw [hx]
  simp

end

/-- a commonplace primitive coding of a finite type; it is deliberately local, so no
canonical encoding of the machine's finite sets is asserted -/
noncomputable def fintPrim (α : Type*) [Fintype α] : Primcodable α :=
  Primcodable.ofEquiv (Fin (Fintype.card α)) (Fintype.equivFin α)

section
variable {K Λ σ : Type*} (Γ : K → Type*) [DecidableEq K]
variable [Fintype Λ] (k₀ : K) (m : Λ → TM2.Stmt Γ Λ σ)

-- Relation between stacks of the original program and stacks of symbolic letters.
def HStacks (A : ∀ k, List (Γ k))
    (B : K → List (HU Γ k₀ m)) : Prop :=
  ∀ k, (B k).map (hdec Γ k₀ m k) = (A k).map some

-- This orientation of the head equation is the one needed by peek and pop.
lemma hhead {A : ∀ k, List (Γ k)} {B : K → List (HU Γ k₀ m)}
    (h : HStacks Γ k₀ m A B) (k : K) :
    (B k).head?.bind (hdec Γ k₀ m k) = (A k).head? := by
  have hh := congrArg (@List.head? (Option (Γ k))) (h k)
  -- first cancel the extra option introduced by the total list map
  have hh' := congrArg (@Option.join (Γ k)) hh
  rw [List.head?_map, List.head?_map] at hh
  calc
    (B k).head?.bind (hdec Γ k₀ m k) = (Option.map (hdec Γ k₀ m k) (B k).head?).join := by cases (B k).head? <;> rfl
    _ = (Option.map some (A k).head?).join := by rw [hh]
    _ = (A k).head? := by cases (A k).head? <;> rfl

lemma htail {A : ∀ k, List (Γ k)} {B : K → List (HU Γ k₀ m)}
    (h : HStacks Γ k₀ m A B) (k : K) :
    ((B k).tail).map (hdec Γ k₀ m k) = ((A k).tail).map some := by
  simpa [List.map_tail] using congrArg (@List.tail (Option (Γ k))) (h k)

lemma hupdate {A : ∀ k, List (Γ k)} {B : K → List (HU Γ k₀ m)}
    (h : HStacks Γ k₀ m A B) (k : K) (xs : List (Γ k)) (ys : List (HU Γ k₀ m))
    (p : ys.map (hdec Γ k₀ m k) = xs.map some) :
    HStacks Γ k₀ m (Function.update A k xs) (Function.update B k ys) := by
  intro j
  classical
  by_cases e : j = k
  · subst j
    simpa [] using p
  · simp [Function.update_of_ne e, e, h j]

end

section
variable {K Λ σ : Type*} (Γ : K → Type*) [DecidableEq K] [Fintype Λ]
variable (k₀ : K) (m : Λ → TM2.Stmt Γ Λ σ)

/-- compilation of statements; the proof records which entry of the finite source list
is meant by each push -/
noncomputable def hcomp : (q : TM2.Stmt Γ Λ σ) →
    (∀ {o : HOcc Γ σ}, o ∈ hcollect (Γ:=Γ) q → o ∈ hall (Γ:=Γ) m) →
      TM2.Stmt (fun _ : K => HU Γ k₀ m) Λ σ
  | .push k f q, h =>
      .push k (fun v => htok Γ k₀ m (k:=k) (f:=f) (h (o:=⟨k,f⟩) (by simp [hcollect])) v)
        (hcomp q (fun {_} a => h (by simp [hcollect, a])))
  | .peek k f q, h =>
      .peek k (fun v x => f v (x.bind (hdec Γ k₀ m k)))
        (hcomp q (fun {_} a => h (by simpa [hcollect] using a)))
  | .pop k f q, h =>
      .pop k (fun v x => f v (x.bind (hdec Γ k₀ m k)))
        (hcomp q (fun {_} a => h (by simpa [hcollect] using a)))
  | .load f q, h =>
      .load f (hcomp q (fun {_} a => h (by simpa [hcollect] using a)))
  | .branch f q r, h =>
      .branch f
        (hcomp q (fun {_} a => h (by simp [hcollect, a])))
        (hcomp r (fun {_} a => h (by simp [hcollect, a])))
  | .goto f, _ => .goto f
  | .halt, _ => .halt

noncomputable def hprog : Λ → TM2.Stmt (fun _ : K => HU Γ k₀ m) Λ σ :=
  fun l => hcomp Γ k₀ m (m l) (fun {_} a => hmem_all (Γ:=Γ) m a)

def HCfg (c : TM2.Cfg Γ Λ σ)
    (d : TM2.Cfg (fun _ : K => HU Γ k₀ m) Λ σ) : Prop :=
  c.l = d.l ∧ c.var = d.var ∧ HStacks Γ k₀ m c.stk d.stk

lemma haux (q : TM2.Stmt Γ Λ σ)
    (hq : ∀ {o : HOcc Γ σ}, o ∈ hcollect (Γ:=Γ) q → o ∈ hall (Γ:=Γ) m)
    (v : σ) (A : ∀ k, List (Γ k)) (B : K → List (HU Γ k₀ m))
    (h : HStacks Γ k₀ m A B) :
    HCfg Γ k₀ m (TM2.stepAux q v A)
      (TM2.stepAux (hcomp Γ k₀ m q hq) v B) := by
  induction q generalizing v A B with
  | @push k f q ih =>
      dsimp [hcomp]
      apply ih (fun {_} a => hq (by simp [hcollect, a])) _ _ _
      -- updated stacks are still related
      apply hupdate Γ k₀ m h k
      simp [hdec_tok (Γ:=Γ) (k₀:=k₀) (m:=m), h k]
  | peek k f q ih =>
      dsimp [hcomp]
      have hd := hhead Γ k₀ m h k
      -- after the change of state only the relation on the unchanged stacks is used
      simpa [hd] using (ih (fun {_} a => hq (by simpa [hcollect] using a))
        (f v (A k).head?) A B h)
  | pop k f q ih =>
      dsimp [hcomp]
      have hd := hhead Γ k₀ m h k
      have ht := htail Γ k₀ m h k
      -- both stacks lose their fronts
      simpa [hd] using (ih (fun {_} a => hq (by simpa [hcollect] using a))
        (f v (A k).head?) (Function.update A k (A k).tail)
          (Function.update B k (B k).tail) (hupdate Γ k₀ m h k _ _ ht))
  | load f q ih =>
      dsimp [hcomp]
      exact ih (fun {_} a => hq (by simpa [hcollect] using a)) _ _ _ h
  | branch f q r ih₁ ih₂ =>
      dsimp [hcomp]
      cases e : f v <;> simp [e, TM2.stepAux]
      · exact ih₂ (fun {_} a => hq (by simp [hcollect, a])) _ _ _ h
      · exact ih₁ (fun {_} a => hq (by simp [hcollect, a])) _ _ _ h
  | goto f =>
      dsimp [hcomp, TM2.stepAux, HCfg]
      exact ⟨rfl, rfl, h⟩
  | halt =>
      dsimp [hcomp, TM2.stepAux, HCfg]
      exact ⟨rfl, rfl, h⟩

end

section
variable {K Λ σ : Type*} (Γ : K → Type*) [DecidableEq K] [Fintype Λ]
variable (k₀ : K) (m : Λ → TM2.Stmt Γ Λ σ)

lemma hstep {c : TM2.Cfg Γ Λ σ}
    {d : TM2.Cfg (fun _ : K => HU Γ k₀ m) Λ σ}
    (h : HCfg Γ k₀ m c d) :
    match TM2.step m c with
    | none => TM2.step (hprog Γ k₀ m) d = none
    | some c' => ∃ d', TM2.step (hprog Γ k₀ m) d = some d' ∧
          HCfg Γ k₀ m c' d' := by
  rcases c with ⟨l,v,A⟩
  rcases d with ⟨l',v',B⟩
  rcases h with ⟨hl,hv,hs⟩
  dsimp at hl hv hs
  subst l'; subst v'
  cases l with
  | none => simp [TM2.step]
  | some l =>
     change ∃ d', TM2.step (hprog Γ k₀ m) { l := some l, var := v, stk := B } = some d' ∧
        HCfg Γ k₀ m (TM2.stepAux (m l) v A) d'
     refine ⟨TM2.stepAux (hprog Γ k₀ m l) v B, rfl, ?_⟩
     unfold hprog
     apply haux Γ k₀ m (m l) _ v A B hs

lemma hiter {c : TM2.Cfg Γ Λ σ}
    {d : TM2.Cfg (fun _ : K => HU Γ k₀ m) Λ σ}
    (h : HCfg Γ k₀ m c d) : ∀ n c',
       (flip Option.bind (TM2.step m))^[n] c = some c' →
       ∃ d', (flip Option.bind (TM2.step (hprog Γ k₀ m)))^[n] d = some d' ∧
          HCfg Γ k₀ m c' d' := by
  intro n
  induction n generalizing c d with
  | zero =>
      intro c' hc
      simp at hc
      subst c'
      exact ⟨d, rfl, h⟩
  | succ n ih =>
      intro c' hc
      rw [Function.iterate_succ_apply] at hc ⊢
      cases e : TM2.step m c with
      | none =>
        have zn : ∀ t : ℕ, (flip Option.bind (TM2.step m))^[t]
             (none : Option (TM2.Cfg Γ Λ σ)) = none := by
          intro t; induction t with
          | zero => rfl
          | succ t it => simp [Function.iterate_succ_apply, flip, it]
        change (flip Option.bind (TM2.step m))^[n] (TM2.step m c) = some c' at hc
        rw [e, zn n] at hc
        cases hc
      | some c1 =>
        have hs := hstep Γ k₀ m h
        rw [e] at hs
        obtain ⟨d1, ed, rel⟩ := hs
        have hc' : (flip Option.bind (TM2.step m))^[n] c1 = some c' := by
          simpa [flip, e] using hc
        obtain ⟨d', hn, hr⟩ := ih rel _ hc'
        refine ⟨d', ?_, hr⟩
        simpa [flip, ed] using hn

end

section
variable {K Λ σ : Type*} (Γ : K → Type*) [DecidableEq K] [Fintype Λ]
variable (k₀ : K) (m : Λ → TM2.Stmt Γ Λ σ)

lemma hinit (start : Λ) (v0 : σ) (xs : List (Γ k₀)) :
   HCfg Γ k₀ m
     ({l := some start, var := v0,
       stk := (fun k => @dite (List (Γ k)) (k = k₀) (inferInstance)
               (fun h => by rw [h]; exact xs) (fun _ => []))} : TM2.Cfg Γ Λ σ)
     ({l := some start, var := v0,
       stk := Function.update (fun _ : K => ([] : List (HU Γ k₀ m))) k₀
             (xs.map (fun a => (Sum.inl a : HU Γ k₀ m)))} :
       TM2.Cfg (fun _ : K => HU Γ k₀ m) Λ σ) := by
  refine ⟨rfl, rfl, ?_⟩
  intro k
  classical
  by_cases e : k = k₀
  · subst k
    simp [hdec]
  · simp [Function.update, e]

end

section
/-- The heterogeneous alphabets in `FinTM2` present no extra computing power.
Letters on scratch stacks can be represented by their finite syntactic source and state. -/
theorem computable_finTM2_nat
    (tm : Turing.FinTM2)
    (e₀ : tm.Γ tm.k₀ ≃ Bool) (e₁ : tm.Γ tm.k₁ ≃ Bool)
    (f : ℕ → ℕ)
    (runs : ∀ n, Turing.TM2Outputs tm
       ((encodeNat n).map e₀.symm)
       (some ((encodeNat (f n)).map e₁.symm))) :
    Computable f := by
  classical
  letI dK : DecidableEq tm.K := tm.kDecidableEq
  letI fk : Fintype tm.K := tm.kFin
  letI fs0 : Fintype tm.σ := tm.σFin
  letI fl0 : Fintype tm.Λ := tm.ΛFin
  letI fi0 : Fintype (tm.Γ tm.k₀) := tm.Γk₀Fin
  -- choose elementary primitive codings of the three finite sets and of the symbolic alphabet
  letI pg0 : Primcodable (tm.Γ tm.k₀) := fintPrim _
  letI pK : Primcodable tm.K := fintPrim tm.K
  letI pS : Primcodable tm.σ := fintPrim tm.σ
  letI pL : Primcodable tm.Λ := fintPrim tm.Λ
  letI ufin : Fintype (HU tm.Γ tm.k₀ tm.m) := by unfold HU; infer_instance
  letI pu : Primcodable (HU tm.Γ tm.k₀ tm.m) := fintPrim (HU tm.Γ tm.k₀ tm.m)
  -- keep typeclass search at the opaque-as-written coding rather than unfolding the sum
  letI psum : Primcodable ((tm.Γ tm.k₀) ⊕ (Fin (hall (Γ:=tm.Γ) tm.m).length × tm.σ)) := pu
  -- finite typeclasses expected by the uniform evaluator
  letI fs : Finite tm.σ := Finite.of_fintype _
  letI fl : Finite tm.Λ := Finite.of_fintype _
  letI fu : Finite (HU tm.Γ tm.k₀ tm.m) := Finite.of_fintype _

  let xi (n : ℕ) : List (tm.Γ tm.k₀) := (encodeNat n).map e₀.symm
  let yi (n : ℕ) : List (HU tm.Γ tm.k₀ tm.m) := (xi n).map (fun a => (Sum.inl a : HU tm.Γ tm.k₀ tm.m))
  let di (n : ℕ) : TM2.Cfg (fun _ : tm.K => (HU tm.Γ tm.k₀ tm.m)) tm.Λ tm.σ :=
      { l := some tm.main, var := tm.initialState,
        stk := Function.update (fun _ : tm.K => ([] : List (HU tm.Γ tm.k₀ tm.m))) tm.k₀ (yi n) }
  let cf (n : ℕ) : tm.Cfg := haltList tm ((encodeNat (f n)).map e₁.symm)

  have relin (n : ℕ) : HCfg tm.Γ tm.k₀ tm.m (initList tm (xi n)) (di n) := by
    -- the definition of `initList` is exactly this singleton update
    simpa [di, Turing.initList] using
      (hinit (Γ:=tm.Γ) (k₀:=tm.k₀) (m:=tm.m) tm.main tm.initialState (xi n))

  have lifted : ∀ n, ∃ d : TM2.Cfg (fun _ : tm.K => (HU tm.Γ tm.k₀ tm.m)) tm.Λ tm.σ,
       (∃ t : ℕ, (flip Option.bind (TM2.step (hprog tm.Γ tm.k₀ tm.m)))^[t] (di n) = some d) ∧
       HCfg tm.Γ tm.k₀ tm.m (cf n) d := by
    intro n
    have rn := runs n
    change StateTransition.EvalsTo (TM2.step tm.m)
       (initList tm (xi n)) (some (cf n)) at rn
    obtain ⟨t, ht⟩ := rn
    obtain ⟨d, hd, rd⟩ := hiter tm.Γ tm.k₀ tm.m (relin n) t (cf n) ht
    exact ⟨d, ⟨⟨t, hd⟩, rd⟩⟩

  choose dn heval hrel using lifted
  -- The symbolic input is recursive (only a finite alphabet map is involved).
  have cxi : Computable xi := by
    dsimp [xi]
    -- maps of finite alphabets are primitive recursive
    have pe : Primrec e₀.symm := Primrec.dom_finite _
    have pm : Primrec (fun l : List Bool => l.map e₀.symm) :=
      Primrec.list_map Primrec.id (pe.comp Primrec.snd).to₂
    exact pm.to_comp.comp prim_encodeNat.to_comp
  have cy : Computable yi := by
    dsimp [yi]
    have pin : Primrec (fun a : tm.Γ tm.k₀ => (Sum.inl a : (HU tm.Γ tm.k₀ tm.m))) :=
      Primrec.dom_finite _
    have pm : Primrec (fun l : List (tm.Γ tm.k₀) =>
          l.map (fun a => (Sum.inl a : (HU tm.Γ tm.k₀ tm.m)))) :=
      Primrec.list_map Primrec.id (pin.comp Primrec.snd).to₂
    exact pm.to_comp.comp cxi

  have listU : Computable (fun n => (dn n).stk tm.k₁) := by
    apply computable_homogeneous (Γ:=(HU tm.Γ tm.k₀ tm.m)) tm.k₀ tm.k₁ tm.main tm.initialState
        (hprog tm.Γ tm.k₀ tm.m) yi cy (fun n => (dn n).stk tm.k₁) dn
    · intro n
      exact ⟨Classical.choose (heval n), by
        simpa [di] using (Classical.choose_spec (heval n))⟩
    · intro n
      have r := (hrel n).1
      -- the related target is the canonical halted configuration
      exact r.symm ▸ rfl
    · intro n; rfl

  -- Read decoded booleans; ill-coloured cells are immaterial (and never occur).
  let rd : (HU tm.Γ tm.k₀ tm.m) → Bool := fun a =>
       (hdec tm.Γ tm.k₀ tm.m tm.k₁ a).elim false e₁
  have pr : Primrec rd := Primrec.dom_finite _
  have rb : Computable (fun n => ((dn n).stk tm.k₁).map rd) := by
    have pm : Primrec (fun l : List (HU tm.Γ tm.k₀ tm.m) => l.map rd) :=
      Primrec.list_map Primrec.id (pr.comp Primrec.snd).to₂
    exact pm.to_comp.comp listU
  have enc : (fun n => ((dn n).stk tm.k₁).map rd) =
        (fun n => encodeNat (f n)) := by
    funext n
    have hh := (hrel n).2.2 tm.k₁
    have hx := congrArg (List.map (fun z : Option (tm.Γ tm.k₁) => z.elim false e₁)) hh
    -- each related stack consists of valid cells; the original halted output
    -- is the claimed list in the output alphabet
    simpa [rd, cf, Turing.haltList, List.map_map, Function.comp_def] using hx
  have outbits : Computable (fun n => encodeNat (f n)) := enc ▸ rb
  exact (prim_bitval.to_comp.comp outbits).of_eq (fun n => bitval_encode (f n))

/-- direct specialization to the mathlib structure -/
theorem TM2Computable.computable_nat {f : ℕ → ℕ}
    (h : Nonempty (TM2Computable encodeNat encodeNat f)) : Computable f := by
  classical
  rcases h with ⟨h⟩
  exact computable_finTM2_nat h.tm h.inputAlphabet h.outputAlphabet f h.outputsFun
end

end compile
end
end TuringRecSupport

end
-- END INLINED FILE: Mathlib/Support/turing_recursive_equiv_70d63b4214/Hetero.lean

-- BEGIN INLINED MAIN PRELUDE

open Computability Turing
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- END INLINED MAIN PRELUDE

namespace Submission

/-ResultBegin-/

theorem turing_recursive_equiv (f : ℕ → ℕ) :
    Computable f ↔ Nonempty (TM2Computable encodeNat encodeNat f) :=
/-ResultProofBegin-/by
  constructor
  · intro hf
    -- reduce to the concrete unary List-code compiler.  The remaining bridge now has a
    -- fixed code and its literal binary input/output convention.
    have hp : Partrec (f : ℕ →. ℕ) := hf
    have hp' : @Nat.Partrec' 1 (fun v : List.Vector ℕ 1 => (f v.head : Part ℕ)) :=
      Nat.Partrec'.part_iff₁.mpr hp
    obtain ⟨c, hc⟩ := Turing.ToPartrec.Code.exists_code hp'
    -- all finiteness/statement restriction for this `c` is in `Forward`: `machine c`,
    -- `lift_aux`, `corestep`, `corerun`.
    classical
    open TuringRecForward in
      exact (by
        refine ⟨{ tm := machine c,
                  inputAlphabet := Equiv.refl _,
                  outputAlphabet := Equiv.refl _,
                  outputsFun := ?_ }⟩
        intro n
        have eqc := hc (⟨[n], by simp⟩ : List.Vector ℕ 1)
        change c.eval [n] = (pure <$> (f n : Part ℕ)) at eqc
        have hv : [f n] ∈ c.eval [n] := by
          rw [eqc]
          simp
        -- execute the wrapper and the verified code
        change StateTransition.EvalsTo (machine c).step
          (Turing.initList (machine c) ((Computability.encodeNat n).map id))
          (some (Turing.haltList (machine c)
            ((Computability.encodeNat (f n)).map id)))
        simpa using (reaches_evals (reachall (c:=c) hv))
      )
  · exact fun h => TuringRecSupport.TM2Computable.computable_nat h
/-ResultProofEnd-/
/-ResultEnd-/

end Submission
