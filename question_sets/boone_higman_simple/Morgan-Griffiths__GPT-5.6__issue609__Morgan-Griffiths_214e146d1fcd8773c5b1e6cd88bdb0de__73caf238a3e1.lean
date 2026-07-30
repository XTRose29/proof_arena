import ChallengeDeps
import Submission.Helpers

open LeanEval.GroupTheory.BooneHigmanSimpleProblem

namespace Submission

/-ResultProofDefinitionsBegin-/

-- computational lemmas for literal words in a free group
section

lemma _aux_prim_invRev {α : Type*} [Primcodable α] :
    Primrec (@FreeGroup.invRev α) := by
  -- reverse after toggling signs
  unfold FreeGroup.invRev
  exact Primrec.list_reverse.comp
    (Primrec.list_map (Primrec.id) <|
      (Primrec.pair (Primrec.fst.comp Primrec.snd)
        (Primrec.not.comp (Primrec.snd.comp Primrec.snd))).to₂)

lemma _aux_prim_reduce {α : Type*} [Primcodable α] [DecidableEq α] :
    Primrec (@FreeGroup.reduce α _) := by
  -- the reduction is a fold from the right, keeping a reduced suffix as a stack
  let step : (α × Bool) × List (α × Bool) → List (α × Bool) := fun p =>
    List.casesOn p.2 [p.1] (fun b l =>
      if p.1.1 = b.1 ∧ p.1.2 = not b.2 then l else p.1 :: b :: l)
  have hs : Primrec step := by
    dsimp [step]
    -- case split on the reduced tail, and then the test at its head
    apply Primrec.list_casesOn (f := fun p : (α × Bool) × List (α × Bool) => p.2)
      (g := fun p : (α × Bool) × List (α × Bool) => [p.1])
      (h := fun p q => if p.1.1 = q.1.1 ∧ p.1.2 = not q.1.2
             then q.2 else p.1 :: q.1 :: q.2)
    · exact Primrec.snd
    · exact Primrec.list_cons.comp Primrec.fst (Primrec.const [])
    · -- build a primitive recursive conditional
      have hc : PrimrecPred (fun z : ((α × Bool) × List (α × Bool)) × ((α × Bool) × List (α × Bool)) =>
          z.1.1.1 = z.2.1.1 ∧ z.1.1.2 = not z.2.1.2) := by
        -- equality is primitive recursive on a primcodable type
        have h1 : PrimrecPred (fun z : ((α × Bool) × List (α × Bool)) × ((α × Bool) × List (α × Bool)) =>
            z.1.1.1 = z.2.1.1) := Primrec.eq.comp
              (Primrec.fst.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.fst.comp (Primrec.fst.comp Primrec.snd))
        have h2 : PrimrecPred (fun z : ((α × Bool) × List (α × Bool)) × ((α × Bool) × List (α × Bool)) =>
            z.1.1.2 = not z.2.1.2) := Primrec.eq.comp
              (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
              (Primrec.not.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        exact h1.and h2
      -- ite at the two arguments
      exact (Primrec.ite hc (Primrec.snd.comp Primrec.snd)
        (Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
          (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd)
            (Primrec.snd.comp Primrec.snd)))).to₂
  change Primrec fun l : List (α × Bool) => FreeGroup.reduce l
  -- express reduce by the fold
  have hfold : Primrec (fun l : List (α × Bool) =>
      l.foldr (fun a s => step (a,s)) []) :=
    Primrec.list_foldr (Primrec.id) (Primrec.const [])
      (hs.comp Primrec.snd).to₂
  refine hfold.of_eq ?_
  intro l
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.foldr_cons]
    simp only [FreeGroup.reduce.cons, ih]
    cases h : FreeGroup.reduce l with
    | nil => rfl
    | cons b t =>
      change (if a.1 = b.1 ∧ a.2 = not b.2 then t else a :: b :: t) = _
      rfl

end


abbrev _AuxW (n : ℕ) := List (Fin n × Bool)
abbrev _AuxI (n : ℕ) := _AuxW n × _AuxW n × Bool

def _auxIW {n} (z : _AuxI n) : _AuxW n :=
  z.1 ++ (if z.2.2 then z.2.1 else FreeGroup.invRev z.2.1) ++ FreeGroup.invRev z.1

def _auxEval {n} (c : List (_AuxI n)) : _AuxW n := c.flatMap _auxIW

def _auxGood {n} (A : List (_AuxW n)) (c : List (_AuxI n)) : Prop :=
  ∀ z ∈ c, z.2.1 ∈ A

lemma _aux_mk_iw {n} (u r : _AuxW n) (b : Bool) :
    FreeGroup.mk (_auxIW (u,r,b)) =
      FreeGroup.mk u * (if b then FreeGroup.mk r else (FreeGroup.mk r)⁻¹) * (FreeGroup.mk u)⁻¹ := by
  cases b <;> simp [_auxIW, ← FreeGroup.mul_mk, FreeGroup.inv_mk, mul_assoc]

lemma _aux_eval_append {n} (x y : List (_AuxI n)) :
    _auxEval (x ++ y) = _auxEval x ++ _auxEval y := by
  simp [_auxEval]

lemma _aux_eval_single {n} (z : _AuxI n) : _auxEval [z] = _auxIW z := by
  simp [_auxEval]

-- flipping all the signs reverses a certificate and gives its inverse
def _auxFlip {n} (z : _AuxI n) : _AuxI n := (z.1, z.2.1, !z.2.2)
def _auxInvC {n} (c : List (_AuxI n)) : List (_AuxI n) := (c.reverse.map _auxFlip)

lemma _aux_good_append {n} {A : List (_AuxW n)} {c d : List (_AuxI n)}
    (hc : _auxGood A c) (hd : _auxGood A d) : _auxGood A (c++d) := by
  intro z hz
  rcases List.mem_append.mp hz with h|h
  · exact hc z h
  · exact hd z h

lemma _aux_good_inv {n} {A : List (_AuxW n)} {c : List (_AuxI n)}
    (hc : _auxGood A c) : _auxGood A (_auxInvC c) := by
  intro z hz
  simp only [_auxInvC, List.mem_map, List.mem_reverse] at hz
  rcases hz with ⟨y, hy, rfl⟩
  exact hc y hy

lemma _aux_mk_eval_append {n} (c d : List (_AuxI n)) :
    FreeGroup.mk (_auxEval (c++d)) =
      FreeGroup.mk (_auxEval c) * FreeGroup.mk (_auxEval d) := by
  rw [_aux_eval_append, ← FreeGroup.mul_mk]

lemma _aux_mk_iw_flip {n} (z : _AuxI n) :
    FreeGroup.mk (_auxIW (_auxFlip z)) = (FreeGroup.mk (_auxIW z))⁻¹ := by
  rcases z with ⟨u,r,b⟩
  simp only [_auxFlip]
  rw [_aux_mk_iw, _aux_mk_iw]
  cases b <;> simp [mul_inv_rev]

lemma _aux_mk_eval_inv {n} (c : List (_AuxI n)) :
    FreeGroup.mk (_auxEval (_auxInvC c)) = (FreeGroup.mk (_auxEval c))⁻¹ := by
  induction c with
  | nil => simp [_auxInvC, _auxEval]
  | cons z c ih =>
    change FreeGroup.mk (_auxEval (( (z::c).reverse).map _auxFlip)) = _
    rw [List.reverse_cons, List.map_append, _aux_mk_eval_append]
    simp only [List.map_cons, List.map_nil]
    rw [_aux_eval_single]
    rw [_aux_mk_iw_flip]
    have ee : List.map _auxFlip c.reverse = _auxInvC c := rfl
    rw [ee, ih]
    -- a certificate beginning with z is the product with its tail
    have em : FreeGroup.mk (_auxEval (z::c)) =
        FreeGroup.mk (_auxIW z) * FreeGroup.mk (_auxEval c) := by
      change FreeGroup.mk (_auxIW z ++ _auxEval c) = _
      rw [← FreeGroup.mul_mk]
    rw [em]
    simp


lemma _aux_nc_iff {n} (A : List (_AuxW n)) (t : _AuxW n) :
    FreeGroup.mk t ∈ Subgroup.normalClosure {x : FreeGroup (Fin n) | ∃ r ∈ A, FreeGroup.mk r = x} ↔
      ∃ c : List (_AuxI n), _auxGood A c ∧ FreeGroup.reduce (_auxEval c) = FreeGroup.reduce t := by
  classical
  let S : Set (FreeGroup (Fin n)) := {x | ∃ r ∈ A, FreeGroup.mk r = x}
  -- first, the easy direction: any certificate lies in the closure
  have cert_mem : ∀ c : List (_AuxI n), _auxGood A c →
      FreeGroup.mk (_auxEval c) ∈ Subgroup.normalClosure S := by
    intro c hc
    induction c with
    | nil =>
      change (1 : FreeGroup (Fin n)) ∈ Subgroup.normalClosure S
      exact (Subgroup.normalClosure S).one_mem
    | cons z c ih =>
      have hz : z.2.1 ∈ A := hc z (by simp)
      have hc' : _auxGood A c := by
        intro q hq; exact hc q (by simp [hq])
      have tail := ih hc'
      have hr : FreeGroup.mk z.2.1 ∈ Subgroup.normalClosure S :=
        Subgroup.subset_normalClosure (show ∃ r ∈ A, FreeGroup.mk r = FreeGroup.mk z.2.1 from
          ⟨z.2.1, hz, rfl⟩)
      have hr' : (if z.2.2 then FreeGroup.mk z.2.1 else (FreeGroup.mk z.2.1)⁻¹)
            ∈ Subgroup.normalClosure S := by
        cases h : z.2.2
        · simpa [h] using (Subgroup.normalClosure S).inv_mem hr
        · simpa [h] using hr
      have ha : FreeGroup.mk (_auxIW z) ∈ Subgroup.normalClosure S := by
        rw [show z = (z.1,z.2.1,z.2.2) by cases z <;> rfl, _aux_mk_iw]
        exact (Subgroup.normalClosure_normal.conj_mem _ hr' _)
      have := ((Subgroup.normalClosure S).mul_mem ha tail)
      simpa [_auxEval, ← FreeGroup.mul_mk] using this
  constructor
  · intro ht
    -- induction on the subgroup closure of conjugates
    change FreeGroup.mk t ∈ Subgroup.closure (Group.conjugatesOfSet S) at ht
    have gen : ∀ x : FreeGroup (Fin n), x ∈ Subgroup.closure (Group.conjugatesOfSet S) →
        ∃ c : List (_AuxI n), _auxGood A c ∧ FreeGroup.mk (_auxEval c) = x := by
      intro x hx
      refine Subgroup.closure_induction (p:= fun x _ =>
        ∃ c : List (_AuxI n), _auxGood A c ∧ FreeGroup.mk (_auxEval c) = x) ?base ?one ?mul ?inv hx
      case base =>
        intro x hx
        rcases (Group.mem_conjugatesOfSet_iff).1 hx with ⟨r, ⟨w, hw, rfl⟩, hcon⟩
        rcases (isConj_iff.mp hcon) with ⟨u, hu⟩
        refine ⟨[(u.toWord, w, true)], ?_, ?_⟩
        · intro q hq
          simp at hq
          rcases hq with rfl
          exact hw
        · rw [_aux_eval_single, _aux_mk_iw]
          simp [FreeGroup.mk_toWord]
          exact hu.symm.symm
      case one => exact ⟨[], by simp [_auxGood], by rfl⟩
      case mul =>
        intro x y hx hy ix iy
        rcases ix with ⟨c,hc,eqc⟩
        rcases iy with ⟨d,hd,eqd⟩
        refine ⟨c++d, _aux_good_append hc hd, ?_⟩
        rw [_aux_mk_eval_append, eqc, eqd]
      case inv =>
        intro x hx ix
        rcases ix with ⟨c,hc,eqc⟩
        refine ⟨_auxInvC c, _aux_good_inv hc, ?_⟩
        rw [_aux_mk_eval_inv, eqc]
    rcases gen (FreeGroup.mk t) ht with ⟨c,hc,he⟩
    exact ⟨c,hc, FreeGroup.reduce.sound he⟩
  · rintro ⟨c,hc,he⟩
    have hm := cert_mem c hc
    have e : FreeGroup.mk (_auxEval c) = FreeGroup.mk t := FreeGroup.reduce.exact he
    simpa [S, e] using hm


def _auxMemB {β : Type*} [DecidableEq β] (a : β) : List β → Bool
 | [] => false
 | b::l => decide (a=b) || _auxMemB a l

lemma _aux_mem_spec {β : Type*} [DecidableEq β] (a : β) (l : List β) :
    _auxMemB a l = true ↔ a ∈ l := by
  induction l with
  | nil => simp [_auxMemB]
  | cons b l ih =>
    simp [_auxMemB, ih, or_comm]

lemma _aux_prim_mem {β : Type*} [Primcodable β] [DecidableEq β] :
    Primrec₂ (@_auxMemB β _) := by
  -- fold the second argument
  change Primrec fun p : β × List β => _auxMemB p.1 p.2
  have hf : Primrec (fun p : β × List β =>
      p.2.foldr (fun b q => decide (p.1=b) || q) false) := by
    refine Primrec.list_foldr (h:= fun p (x : β × Bool) => decide (p.1 = x.1) || x.2) (Primrec.snd) (Primrec.const false) ?_
    -- arguments: p and (b,q)
    apply Primrec₂.mk
    have he : Primrec (fun z : (β × List β) × (β × Bool) => decide (z.1.1 = z.2.1)) :=
      (Primrec.eq.decide.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp Primrec.snd))
    exact Primrec.or.comp he (Primrec.snd.comp Primrec.snd)
  have aux (a : β) (l : List β) :
      l.foldr (fun b q => decide (a=b) || q) false = _auxMemB a l := by
    induction l with
    | nil => rfl
    | cons b l ih => simp [_auxMemB, ih]
  exact (hf.of_eq (fun p => aux p.1 p.2)).to₂

-- all relators mentioned by a certificate occur in the finite list
def _auxAll {n} (A : List (_AuxW n)) : List (_AuxI n) → Bool
 | [] => true
 | z::c => _auxMemB z.2.1 A && _auxAll A c

lemma _aux_all_spec {n} (A : List (_AuxW n)) (c : List (_AuxI n)) :
    _auxAll A c = true ↔ _auxGood A c := by
  induction c with
  | nil => simp [_auxAll, _auxGood]
  | cons z c ih =>
    constructor
    · intro h q hq
      have hh : _auxMemB z.2.1 A = true ∧ _auxAll A c = true :=
        (Bool.and_eq_true_iff.mp h)
      rcases List.mem_cons.mp hq with rfl|hq
      · exact (_aux_mem_spec _ _).1 hh.1
      · exact ih.mp hh.2 _ hq
    · intro h
      apply Bool.and_eq_true_iff.mpr
      refine ⟨(_aux_mem_spec _ _).2 (h z (by simp)), ih.mpr ?_⟩
      intro q hq; exact h q (by simp [hq])

lemma _aux_prim_iw {n} : Primrec (@_auxIW n) := by
  unfold _auxIW
  -- choose between r and its inverse
  have mid : Primrec (fun z : _AuxI n =>
      if z.2.2 then z.2.1 else FreeGroup.invRev z.2.1) := by
    have hc : PrimrecPred (fun z : _AuxI n => z.2.2 = true) :=
      Primrec.eq.comp (Primrec.snd.comp Primrec.snd) (Primrec.const true)
    exact (Primrec.ite hc (Primrec.fst.comp Primrec.snd)
      (_aux_prim_invRev.comp (Primrec.fst.comp Primrec.snd))).of_eq (by
        intro z; cases z.2.2 <;> rfl)
  exact Primrec.list_append.comp (Primrec.list_append.comp Primrec.fst mid)
      (_aux_prim_invRev.comp Primrec.fst)

lemma _aux_prim_eval {n} : Primrec (@_auxEval n) := by
  unfold _auxEval
  exact Primrec.list_flatten.comp
    (Primrec.list_map (Primrec.id) ((_aux_prim_iw (n:=n)).comp Primrec.snd).to₂)

lemma _aux_prim_all {n} : Primrec₂ (@_auxAll n) := by
  change Primrec fun p : List (_AuxW n) × List (_AuxI n) => _auxAll p.1 p.2
  have hfold : Primrec (fun p : List (_AuxW n) × List (_AuxI n) =>
      p.2.foldr (fun z q => _auxMemB z.2.1 p.1 && q) true) := by
    refine Primrec.list_foldr (h:= fun p (x : _AuxI n × Bool) => _auxMemB x.1.2.1 p.1 && x.2) (Primrec.snd) (Primrec.const true) ?_
    apply Primrec₂.mk
    exact Primrec.and.comp
      ((_aux_prim_mem (β:=_AuxW n)).comp (Primrec.fst.comp (Primrec.snd.comp (Primrec.fst.comp Primrec.snd)))
        (Primrec.fst.comp Primrec.fst))
      (Primrec.snd.comp Primrec.snd)
  have aux (A : List (_AuxW n)) (l : List (_AuxI n)) :
      l.foldr (fun z q => _auxMemB z.2.1 A && q) true = _auxAll A l := by
    induction l with
    | nil => rfl
    | cons z l ih => simp [_auxAll, ih]
  exact (hfold.of_eq (fun p => aux p.1 p.2)).to₂

-- the certificate test, with A, t and certificate as inputs
def _auxTest {n} (p : List (_AuxW n) × (_AuxW n × List (_AuxI n))) : Bool :=
   _auxAll p.1 p.2.2 &&
    decide (FreeGroup.reduce (_auxEval p.2.2) = FreeGroup.reduce p.2.1)

lemma _aux_test_spec {n} (A : List (_AuxW n)) (t : _AuxW n)
    (c : List (_AuxI n)) :
    _auxTest (A,t,c) = true ↔
       _auxGood A c ∧ FreeGroup.reduce (_auxEval c) = FreeGroup.reduce t := by
  simp [_auxTest, Bool.and_eq_true, _aux_all_spec, decide_eq_true_eq]

lemma _aux_prim_test {n} : Primrec (@_auxTest n) := by
  unfold _auxTest
  apply Primrec.and.comp
  · exact (_aux_prim_all (n:=n)).comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  · exact Primrec.eq.decide.comp
      ((_aux_prim_reduce (α:=Fin n)).comp (_aux_prim_eval (n:=n) |>.comp (Primrec.snd.comp Primrec.snd)))
      ((_aux_prim_reduce (α:=Fin n)).comp (Primrec.fst.comp Primrec.snd))


-- projecting an effectively checkable existential is recursively enumerable
lemma _aux_re_exists {n} (F : _AuxW n → List (_AuxW n)) (hF : Computable F) :
    REPred (fun t : _AuxW n =>
      ∃ c : List (_AuxI n), _auxTest (F t, t, c) = true) := by
  let dec : ℕ → List (_AuxI n) := fun k => (Encodable.decode (α:= List (_AuxI n)) k).getD []
  have hd : Computable dec :=
    Computable.option_getD (Computable.decode) (Computable.const [])
  have testc : Computable₂ (fun (t : _AuxW n) (k : ℕ) =>
      _auxTest (F t, t, dec k)) := by
    apply Computable₂.mk
    exact (_aux_prim_test (n:=n)).to_comp.comp
      ((hF.comp Computable.fst).pair
        (Computable.pair Computable.fst (hd.comp Computable.snd)))
  have part : Partrec (fun t : _AuxW n =>
      Nat.rfind (fun k => Part.some (_auxTest (F t, t, dec k)))) :=
    Partrec.rfind (testc.partrec.to₂)
  have rr := Partrec.dom_re part
  refine rr.of_eq ?_
  intro t
  change (Nat.rfind (fun k => Part.some (_auxTest (F t, t, dec k)))).Dom ↔ _
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨k, hk, _⟩
    refine ⟨dec k, ?_⟩
    simpa using hk
  · rintro ⟨c,hc⟩
    refine ⟨Encodable.encode c, ?_, ?_⟩
    · simpa [dec] using hc.symm
    · intro m hm
      trivial


def _auxGenTest {n} (A : List (_AuxW n))
    (p : _AuxW n × (Fin n → List (_AuxI n))) : Bool :=
  (List.ofFn (fun i : Fin n =>
      _auxTest (p.1 :: A, [(i,true)], p.2 i))).foldr (fun b q => b && q) true

lemma _aux_fold_spec (l : List Bool) :
    l.foldr (fun b q => b && q) true = true ↔ ∀ b ∈ l, b = true := by
  induction l with
  | nil => simp
  | cons a l ih => simp [ih, Bool.and_eq_true_iff]

lemma _aux_gen_spec {n} (A : List (_AuxW n)) (t : _AuxW n)
    (v : Fin n → List (_AuxI n)) :
    _auxGenTest A (t,v) = true ↔
      ∀ i : Fin n, _auxTest (t::A, [(i,true)], v i) = true := by
  unfold _auxGenTest
  rw [_aux_fold_spec]
  constructor
  · intro h i
    exact h _ ((List.mem_ofFn).2 ⟨i,rfl⟩)
  · intro h b hb
    rcases (List.mem_ofFn).1 hb with ⟨i,rfl⟩
    exact h i

lemma _aux_comp_gen {n} (A : List (_AuxW n)) : Computable (@_auxGenTest n A) := by
  unfold _auxGenTest
  -- first build the finite list of boolean tests
  have li : Computable (fun p : _AuxW n × (Fin n → List (_AuxI n)) =>
      List.ofFn (fun i : Fin n => _auxTest (p.1 :: A, [(i,true)], p.2 i))) := by
    apply Computable.list_ofFn
    intro i
    exact (_aux_prim_test (n:=n)).to_comp.comp
      ((Computable.list_cons.comp (Computable.fst) (Computable.const A)).pair
        ((Computable.const [(i,true)]).pair
          ((Computable.fin_app.comp (Computable.snd) (Computable.const i)))))
  -- fold and on that list
  have fld : Computable (fun l : List Bool => l.foldr (fun b q => b && q) true) :=
    (Primrec.list_foldr (Primrec.id) (Primrec.const true)
      ((Primrec.and.comp (Primrec.fst.comp Primrec.snd)
           (Primrec.snd.comp Primrec.snd)).to₂)).to_comp
  exact fld.comp li

lemma _aux_re_vec {n} (A : List (_AuxW n)) :
    REPred (fun t : _AuxW n => ∃ v : Fin n → List (_AuxI n), _auxGenTest A (t,v) = true) := by
  letI : Encodable (Fin n → List (_AuxI n)) := Primcodable.toEncodable
  let dec : ℕ → (Fin n → List (_AuxI n)) := fun k =>
    (Encodable.decode (α:= Fin n → List (_AuxI n)) k).getD (fun _ => [])
  have hd : Computable dec :=
    Computable.option_getD (Computable.decode) (Computable.const (fun _ => []))
  have te : Computable₂ (fun (t : _AuxW n) (k : ℕ) => _auxGenTest A (t, dec k)) := by
    apply Computable₂.mk
    exact (_aux_comp_gen (n:=n) A).comp
      (Computable.pair Computable.fst (hd.comp Computable.snd))
  have part : Partrec (fun t : _AuxW n =>
      Nat.rfind (fun k => Part.some (_auxGenTest A (t, dec k)))) :=
    Partrec.rfind (te.partrec.to₂)
  refine (Partrec.dom_re part).of_eq ?_
  intro t
  change (Nat.rfind (fun k => Part.some (_auxGenTest A (t, dec k)))).Dom ↔ _
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨k,hk,_⟩
    exact ⟨dec k, by simpa using hk⟩
  · rintro ⟨v,hv⟩
    refine ⟨Encodable.encode v, ?_, ?_⟩
    · simpa [dec] using hv.symm
    · intro m hm; trivial
/-ResultProofDefinitionsEnd-/


theorem boone_higman_simple {G : Type*} [Group G] [IsSimpleGroup G]
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (_hsurj : Function.Surjective φ)
    (_hker : (MonoidHom.ker φ).IsNormalClosureFG) :
    WordProblemSolvable φ := by
  classical
  rcases _hker with ⟨S, hfin, hS⟩
  let L : List (FreeGroup (Fin n)) := hfin.toFinset.toList
  let A : List (_AuxW n) := L.map FreeGroup.toWord
  have eS : {x : FreeGroup (Fin n) | ∃ r ∈ A, FreeGroup.mk r = x} = S := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      rcases (List.mem_map).1 hr with ⟨y,hy,rfl⟩
      rw [FreeGroup.mk_toWord]
      have hy' : y ∈ hfin.toFinset.toList := by simpa [L] using hy
      have hy'' : y ∈ hfin.toFinset := by simpa using hy'
      simpa using hy'' 
    · intro hx
      have hy : x ∈ L := by
        change x ∈ hfin.toFinset.toList
        simpa using hx
      exact ⟨x.toWord, (List.mem_map).2 ⟨x,hy,rfl⟩, FreeGroup.mk_toWord⟩
  have eqcert (t : _AuxW n) :
      φ (FreeGroup.mk t) = 1 ↔
        ∃ c : List (_AuxI n), _auxTest (A,t,c) = true := by
    rw [← MonoidHom.mem_ker, ← hS, ← eS, _aux_nc_iff]
    constructor
    · rintro ⟨c,hc,he⟩
      exact ⟨c, (_aux_test_spec A t c).2 ⟨hc,he⟩⟩
    · rintro ⟨c,hc⟩
      exact ⟨c, (_aux_test_spec A t c).1 hc |>.1, (_aux_test_spec A t c).1 hc |>.2⟩
  have reyes : REPred (fun t : _AuxW n => φ (FreeGroup.mk t) = 1) :=
    (_aux_re_exists (n:=n) (fun _ : _AuxW n => A) (Computable.const A)).of_eq
      (fun t => (eqcert t).symm)
  -- the simple-group argument: adjoining a nontrivial element kills the group
  have collapse (x : FreeGroup (Fin n)) :
      φ x ≠ 1 ↔ ∀ i : Fin n,
        FreeGroup.of i ∈ Subgroup.normalClosure (insert x S) := by
    let N : Subgroup (FreeGroup (Fin n)) := Subgroup.normalClosure (insert x S)
    have kerle : MonoidHom.ker φ ≤ N := by
      rw [← hS]
      apply Subgroup.normalClosure_le_normal
      intro y hy
      exact Subgroup.subset_normalClosure (Set.mem_insert_of_mem _ hy)
    have xim : x ∈ N := Subgroup.subset_normalClosure (Set.mem_insert _ _)
    constructor
    · intro hx i
      have mapnorm : (N.map φ).Normal := by
        rw [show N = Subgroup.normalClosure (insert x S) by rfl,
            Subgroup.map_normalClosure _ _ _hsurj]
        infer_instance
      haveI : (N.map φ).Normal := mapnorm
      have xt : φ x ∈ N.map φ := (Subgroup.mem_map).2 ⟨x, xim, rfl⟩
      have nebot : N.map φ ≠ ⊥ := by
        intro e
        have : φ x = 1 := by
          have : φ x ∈ (⊥ : Subgroup G) := by simpa [e] using xt
          simpa using this
        exact hx this
      have mtop : N.map φ = ⊤ :=
        (mapnorm.eq_bot_or_eq_top).resolve_left nebot
      have ym : φ (FreeGroup.of i) ∈ N.map φ := by simp [mtop]
      rcases (Subgroup.mem_map).1 ym with ⟨z,hz,ez⟩
      have hdiff : FreeGroup.of i * z⁻¹ ∈ MonoidHom.ker φ :=
        (MonoidHom.mem_ker).2 (by rw [map_mul, map_inv, ez]; simp)
      have hdiff' := kerle hdiff
      have muln := N.mul_mem hdiff' hz
      simpa using muln
    · intro all hx
      have ntop : N = ⊤ := by
        apply top_unique
        have ran : Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n)) ⊆ (N : Set _) := by
          rintro _ ⟨i,rfl⟩
          exact all i
        have cl : Subgroup.closure (Set.range (FreeGroup.of : Fin n → FreeGroup (Fin n))) ≤ N :=
          (Subgroup.closure_le N).2 ran
        simpa using cl
      have nle : N ≤ MonoidHom.ker φ := by
        apply Subgroup.normalClosure_le_normal
        intro y hy
        rcases hy with rfl | hy
        · exact (MonoidHom.mem_ker).2 hx
        · rw [← hS]
          exact Subgroup.subset_normalClosure hy
      have ktop : MonoidHom.ker φ = ⊤ := by
        apply top_unique
        simpa [ntop] using nle
      have allone : ∀ g : G, g = 1 := by
        intro g
        rcases _hsurj g with ⟨y,rfl⟩
        apply (MonoidHom.mem_ker).1
        simp [ktop]
      rcases exists_pair_ne G with ⟨a,b,hab⟩
      exact hab ((allone a).trans (allone b).symm)
  have aug (t : _AuxW n) :
      {x : FreeGroup (Fin n) | ∃ r ∈ (t::A), FreeGroup.mk r = x} = insert (FreeGroup.mk t) S := by
    ext x
    constructor
    · rintro ⟨r,hr,rfl⟩
      rcases (List.mem_cons).1 hr with rfl|hr
      · exact Set.mem_insert _ _
      · exact Set.mem_insert_of_mem _ (by rw [← eS]; exact ⟨r,hr,rfl⟩)
    · intro hx
      rcases hx with h|h
      · exact ⟨t, by simp, h.symm ▸ rfl⟩
      · rw [← eS] at h
        rcases h with ⟨r,hr,er⟩
        exact ⟨r, by simp [hr], er⟩
  have oi (i : Fin n) : FreeGroup.mk ([(i,true)] : _AuxW n) = FreeGroup.of i := by rfl
  have necert (t : _AuxW n) :
      φ (FreeGroup.mk t) ≠ 1 ↔
       ∃ v : Fin n → List (_AuxI n), _auxGenTest A (t,v) = true := by
    rw [collapse]
    constructor
    · intro h
      have hh (i : Fin n) :
          FreeGroup.mk ([(i,true)] : _AuxW n) ∈
            Subgroup.normalClosure {x : FreeGroup (Fin n) |
              ∃ r ∈ t::A, FreeGroup.mk r = x} := by
        rw [aug t, oi]
        exact h i
      have ex (i : Fin n) : ∃ c : List (_AuxI n),
          _auxTest (t::A, [(i,true)], c) = true := by
        rcases (_aux_nc_iff (t::A) ([(i,true)] : _AuxW n)).1 (hh i) with ⟨c,hc,he⟩
        exact ⟨c, (_aux_test_spec _ _ _).2 ⟨hc,he⟩⟩
      choose v hv using ex
      exact ⟨v, (_aux_gen_spec A t v).2 hv⟩
    · rintro ⟨v,hv⟩ i
      have hc := (_aux_gen_spec A t v).1 hv i
      have hcc := (_aux_test_spec (t::A) ([(i,true)] : _AuxW n) (v i)).1 hc
      have mem := (_aux_nc_iff (t::A) ([(i,true)] : _AuxW n)).2 ⟨v i,hcc.1,hcc.2⟩
      rw [aug t, oi] at mem
      exact mem

  have reno : REPred (fun t : _AuxW n => ¬ φ (FreeGroup.mk t) = 1) :=
    (_aux_re_vec (n:=n) A).of_eq (fun t => (necert t).symm)
  unfold WordProblemSolvable
  exact ComputablePred.computable_iff_re_compl_re'.2 ⟨reyes, reno⟩

end Submission
