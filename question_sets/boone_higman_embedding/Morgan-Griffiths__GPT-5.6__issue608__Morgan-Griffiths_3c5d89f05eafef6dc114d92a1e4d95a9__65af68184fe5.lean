import ChallengeDeps
import Submission.Helpers

open LeanEval.GroupTheory.BooneHigmanEmbedding

namespace Submission

/-ResultProofDefinitionsBegin-/


lemma repred_exists_prim {α β : Type*} [Primcodable α] [Primcodable β]
    (P : α → β → Prop) [DecidableRel P] (hP : PrimrecRel P) :
    REPred (fun a => ∃ b, P a b) := by
  let test : α → ℕ → Bool := fun a n =>
    (((@Encodable.decode β _ n)).map (fun b => decide (P a b))).getD false
  have ht : Computable₂ test := by
    have hm : Primrec₂ (fun (a : α) (n : ℕ) =>
        ((@Encodable.decode β _ n)).map (fun b => decide (P a b))) :=
      (Primrec.map_decode_iff.mpr hP.decide)
    have hg : Primrec₂ test :=
      (Primrec.option_getD.comp hm (Primrec.const false)).to₂
    exact hg.to_comp
  have hr : Partrec (fun a => Nat.rfind (fun n => Part.some (test a n))) :=
    Partrec.rfind ((ht.partrec).to₂)
  have hd : REPred (fun a => (Nat.rfind (fun n => Part.some (test a n))).Dom) :=
    Partrec.dom_re hr
  refine REPred.of_eq hd ?_
  intro a
  rw [Nat.rfind_dom]
  constructor
  · rintro ⟨k, hk, -⟩
    have htk : test a k = true := by simpa using hk
    dsimp [test] at htk
    cases e : (@Encodable.decode β _ k) with
    | none => simp [e] at htk
    | some b =>
      refine ⟨b, ?_⟩
      simp [e] at htk
      exact htk
  · rintro ⟨b, hb⟩
    refine ⟨Encodable.encode b, ?_, ?_⟩
    · have : test a (Encodable.encode b) = true := by simp [test, hb]
      simpa [this]
    · intro m hm
      trivial

abbrev BHWord (m : ℕ) := List (Fin m × Bool)
abbrev BHDel (m : ℕ) := (BHWord m × (Fin m × Bool)) × BHWord m

def bhFlip {m} (x : Fin m × Bool) : Fin m × Bool := (x.1, ! x.2)

def bhBefore {m} (d : BHDel m) : BHWord m :=
  d.1.1 ++ d.1.2 :: bhFlip d.1.2 :: d.2

def bhAfter {m} (d : BHDel m) : BHWord m := d.1.1 ++ d.2

def bhStep {m} (o : Option (BHWord m)) (d : BHDel m) : Option (BHWord m) :=
  match o with
  | none => none
  | some w => if w = bhBefore d then some (bhAfter d) else none

def bhRun {m} (w : BHWord m) (ds : List (BHDel m)) : Option (BHWord m) :=
  ds.foldl bhStep (some w)

lemma prim_bhFlip {m} : Primrec (@bhFlip m) :=
  Primrec.dom_finite _

lemma prim_bhBefore {m} : Primrec (@bhBefore m) := by
  unfold bhBefore
  -- the tail `(x,!b)::suffix` and the leading letter
  have fl : Primrec (fun d : BHDel m => bhFlip d.1.2) :=
    prim_bhFlip.comp (Primrec.snd.comp Primrec.fst)
  have tail : Primrec (fun d : BHDel m => bhFlip d.1.2 :: d.2) :=
    Primrec.list_cons.comp fl Primrec.snd
  have tail2 : Primrec (fun d : BHDel m => d.1.2 :: (bhFlip d.1.2 :: d.2)) :=
    Primrec.list_cons.comp (Primrec.snd.comp Primrec.fst) tail
  exact Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) tail2

lemma prim_bhAfter {m} : Primrec (@bhAfter m) := by
  unfold bhAfter
  exact Primrec.list_append.comp (Primrec.fst.comp Primrec.fst) Primrec.snd

lemma prim_bhStep {m} : Primrec₂ (@bhStep m) := by
  unfold bhStep
  -- use the option eliminator on the state
  have hgood : PrimrecPred
      (fun q : (Option (BHWord m) × BHDel m) × BHWord m =>
        q.2 = bhBefore q.1.2) :=
    Primrec.eq.comp Primrec.snd
      (prim_bhBefore.comp (Primrec.snd.comp Primrec.fst))
  have hcase0 : Primrec
      (fun q : (Option (BHWord m) × BHDel m) × BHWord m =>
        if q.2 = bhBefore q.1.2
        then some (bhAfter q.1.2) else (none : Option (BHWord m))) :=
    Primrec.ite hgood
      (Primrec.option_some.comp
        (prim_bhAfter.comp (Primrec.snd.comp Primrec.fst)))
      (Primrec.const none)
  have hcase : Primrec₂
      (fun p : Option (BHWord m) × BHDel m => fun w : BHWord m =>
        if w = bhBefore p.2 then some (bhAfter p.2)
        else (none : Option (BHWord m))) := hcase0
  
  refine (Primrec.option_casesOn
      (o := (fun p : Option (BHWord m) × BHDel m => p.1))
      Primrec.fst (Primrec.const none) hcase).to₂.of_eq ?_
  intro o d
  cases o <;> rfl

lemma prim_bhRun {m} : Primrec₂ (@bhRun m) := by
  unfold bhRun
  -- fold over the list of certificates, with the input word as the initial state
  -- the extra fixed argument to `list_foldl` is unused in a deletion step
  have hstep : Primrec₂
      (fun p : (BHWord m × List (BHDel m)) => fun q : Option (BHWord m) × BHDel m =>
        bhStep q.1 q.2) := by
    -- `bhStep` has no dependence on `p`
    exact prim_bhStep.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)
  exact (Primrec.list_foldl
      (f := fun p : BHWord m × List (BHDel m) => p.2)
      (g := fun p : BHWord m × List (BHDel m) => some p.1)
      (h := fun p q => bhStep q.1 q.2)
      Primrec.snd (Primrec.option_some.comp Primrec.fst) hstep).to₂





lemma bhBeforeAfter_step {m} (d : BHDel m) :
    FreeGroup.Red.Step (bhBefore d) (bhAfter d) := by
  rcases d with ⟨⟨l, ⟨x,b⟩⟩, r⟩
  -- this is exactly the deletion constructor (Bool.not is `!`)
  change FreeGroup.Red.Step (l ++ (x,b) :: (x,!b) :: r) (l ++ r)
  exact FreeGroup.Red.Step.not

@[simp] lemma bhRun_nil {m} (w : BHWord m) : bhRun w [] = some w := rfl

lemma bhFold_none {m} (ds : List (BHDel m)) :
    ds.foldl bhStep (none : Option (BHWord m)) = none := by
  induction ds with
  | nil => rfl
  | cons d t ih =>
    -- `none` is absorbing
    simpa [List.foldl, bhStep] using (ih)

lemma bhRun_cons {m} (w : BHWord m) (d : BHDel m) (ds : List (BHDel m)) :
    bhRun w (d :: ds) =
      if w = bhBefore d then bhRun (bhAfter d) ds else none := by
  unfold bhRun
  simp only [List.foldl]
  by_cases h : w = bhBefore d
  · simp [bhStep, h, bhRun]
  · simp [bhStep, h, bhFold_none]

lemma bhRun_sound {m} {w v : BHWord m} {ds : List (BHDel m)}
    (h : bhRun w ds = some v) : FreeGroup.Red w v := by
  induction ds generalizing w v with
  | nil =>
    simp [bhRun] at h
    subst v
    exact FreeGroup.Red.refl
  | cons d t ih =>
    rw [bhRun_cons] at h
    split at h
    case isTrue e =>
      have hr : FreeGroup.Red w (bhAfter d) := by
        -- a single deletion
        simpa [e] using (FreeGroup.Red.Step.to_red (bhBeforeAfter_step d))
      exact FreeGroup.Red.trans hr (ih h)
    case isFalse ne => simp at h

lemma bhRun_extend {m} {a b : BHWord m} {ds : List (BHDel m)} (h : bhRun a ds = some b)
    (d : BHDel m) (hd : b = bhBefore d) :
    bhRun a (ds ++ [d]) = some (bhAfter d) := by
  unfold bhRun at h ⊢
  rw [List.foldl_append]
  -- substitute the state computed by the first fold
  change (bhStep (ds.foldl bhStep (some a)) d) = _
  rw [h]
  simp [bhStep, hd]

lemma bhRun_complete {m} {w v : BHWord m} (h : FreeGroup.Red w v) :
    ∃ ds : List (BHDel m), bhRun w ds = some v := by
  induction h with
  | refl => exact ⟨[], rfl⟩
  | @tail b c _ hstep ih =>
    rcases ih with ⟨ds, hds⟩
    cases hstep with
    | @not l r x bit =>
      let d : BHDel m := ((l, (x, bit)), r)
      have be : (l ++ (x, bit) :: (x, !bit) :: r) = bhBefore d := rfl
      refine ⟨ds ++ [d], ?_⟩
      have hext := bhRun_extend hds d be
      -- its after-word is definitionally this `c`
      simpa [d, bhAfter] using hext


/-- The usual finite product description of a normal closure.  Keeping the
    conjugators in the list (rather than quotienting them) is useful for
    enumerating witnesses. -/
lemma mem_normalClosure_list {X : Type*} [Group X] {s : Set X} {x : X} :
    x ∈ Subgroup.normalClosure s ↔
      ∃ L : List (X × X),
        (∀ p ∈ L, p.2 ∈ s ∨ p.2⁻¹ ∈ s) ∧
        x = (L.map (fun p : X × X => p.1 * p.2 * p.1⁻¹)).prod := by
  constructor
  · intro hx
    -- closure of conjugates
    change x ∈ Subgroup.closure (Group.conjugatesOfSet s) at hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
        rcases (Group.mem_conjugatesOfSet_iff.mp hy) with ⟨a, ha, hc⟩
        obtain ⟨c, rfl⟩ := isConj_iff.mp hc
        refine ⟨[(c,a)], ?_, ?_⟩
        · intro p hp
          have pe : p = (c,a) := by simpa using hp
          subst p
          exact Or.inl ha
        · simp
    | one =>
        exact ⟨[], by simp, by simp⟩
    | mul y z hy hz iy iz =>
        rcases iy with ⟨l, hl, eql⟩
        rcases iz with ⟨r, hr, eqr⟩
        refine ⟨l ++ r, ?_, ?_⟩
        · intro p hp
          exact (List.mem_append.mp hp).elim (hl p) (hr p)
        · simp [List.map_append, List.prod_append, eql, eqr]
    | inv y hy iy =>
        rcases iy with ⟨l, hl, eqy⟩
        let invp : X × X → X × X := fun p => (p.1, p.2⁻¹)
        refine ⟨l.reverse.map invp, ?_, ?_⟩
        · intro p hp
          rcases List.mem_map.mp hp with ⟨q, hq, rfl⟩
          have hq' := hl q (List.mem_reverse.mp hq)
          rcases hq' with hq' | hq'
          · exact Or.inr (by simpa [invp] using hq')
          · exact Or.inl (by simpa [invp] using hq')
        · subst y
          have key : ∀ t : List (X × X),
              (t.map (fun p : X × X => p.1 * p.2 * p.1⁻¹)).prod⁻¹ =
                ((t.reverse.map invp).map
                  (fun p : X × X => p.1 * p.2 * p.1⁻¹)).prod := by
            intro t
            induction t with
            | nil => simp [invp]
            | cons p u iu =>
              rw [List.reverse_cons, List.map_append, List.map_append,
                List.prod_append]
              -- the final factor is the inverse conjugate
              simp [invp, iu]
              simp [mul_assoc]
          exact key l
  · rintro ⟨L, hL, rfl⟩
    -- every listed factor is a conjugate of a relator or its inverse
    have hfactor (p : X × X) (hp : p.2 ∈ s ∨ p.2⁻¹ ∈ s) :
        p.1 * p.2 * p.1⁻¹ ∈ Subgroup.normalClosure s := by
      have hb : p.2 ∈ Subgroup.normalClosure s := by
        rcases hp with hp | hp
        · exact Subgroup.subset_normalClosure hp
        · have h0 : p.2⁻¹ ∈ Subgroup.normalClosure s :=
            Subgroup.subset_normalClosure hp
          simpa using (Subgroup.inv_mem _ h0)
      -- normality supplies the conjugates
      exact (Subgroup.normalClosure_normal.conj_mem p.2 hb p.1)
    induction L with
    | nil => simp
    | cons p t it =>
      have hp : p.2 ∈ s ∨ p.2⁻¹ ∈ s := hL p (by simp)
      have ht : ∀ q ∈ t, q.2 ∈ s ∨ q.2⁻¹ ∈ s := by
        intro q hq; exact hL _ (by simp [hq])
      have ih := it ht
      simpa using (Subgroup.mul_mem _ (hfactor p hp) ih)



def bhFactor {m} (p : BHWord m × BHWord m) : BHWord m :=
  p.1 ++ p.2 ++ FreeGroup.invRev p.1

def bhProd {m} (l : List (BHWord m × BHWord m)) : BHWord m :=
  (l.map bhFactor).flatten

lemma prim_invRev {m} : Primrec (@FreeGroup.invRev (Fin m)) := by
  unfold FreeGroup.invRev
  exact Primrec.list_reverse.comp
    (Primrec.list_map Primrec.id (prim_bhFlip.comp Primrec.snd).to₂)

lemma prim_bhFactor {m} : Primrec (@bhFactor m) := by
  unfold bhFactor
  exact Primrec.list_append.comp
    (Primrec.list_append.comp Primrec.fst Primrec.snd) -- ?
    (prim_invRev.comp Primrec.fst)

lemma prim_bhProd {m} : Primrec (@bhProd m) := by
  unfold bhProd
  exact Primrec.list_flatten.comp
    (Primrec.list_map Primrec.id (prim_bhFactor.comp Primrec.snd).to₂)

lemma mk_bhProd {m} (l : List (BHWord m × BHWord m)) :
    FreeGroup.mk (bhProd l) =
      (l.map (fun p => FreeGroup.mk p.1 * FreeGroup.mk p.2 * (FreeGroup.mk p.1)⁻¹)).prod := by
  induction l with
  | nil => rfl
  | cons p t it =>
    change FreeGroup.mk (bhFactor p ++ bhProd t) =
      (FreeGroup.mk p.1 * FreeGroup.mk p.2 * (FreeGroup.mk p.1)⁻¹) *
        (t.map (fun p => FreeGroup.mk p.1 * FreeGroup.mk p.2 * (FreeGroup.mk p.1)⁻¹)).prod
    rw [← it, FreeGroup.mul_mk, FreeGroup.inv_mk, FreeGroup.mul_mk,
        FreeGroup.mul_mk]
    simp [bhFactor]


abbrev BHCert (m : ℕ) := List (BHWord m × BHWord m) ×
  (List (BHDel m) × List (BHDel m) × BHWord m)

def bhOK {m} (a : BHWord m × List (BHWord m)) (c : BHCert m) : Prop :=
  (∀ t ∈ c.1, t.2 ∈ a.2) ∧
    bhRun a.1 c.2.1 = some c.2.2.2 ∧
    bhRun (bhProd c.1) c.2.2.1 = some c.2.2.2

instance decBhOK {m} : DecidableRel (@bhOK m) := by
  intro a c
  unfold bhOK
  infer_instance

lemma prim_bhMem {m} : PrimrecRel (fun (l : List (BHWord m)) x => x ∈ l) := by
  have h := PrimrecRel.exists_mem_list (α:= BHWord m) (β:= BHWord m)
    (Primrec.eq : PrimrecRel (@Eq (BHWord m)))
  exact h.of_eq (by intro l x; simp)

lemma prim_bhOK {m} : PrimrecRel (@bhOK m) := by
  -- form the list which pairs every used relator with the fixed allowed list
  let marked : ((BHWord m × List (BHWord m)) × BHCert m) →
      List (List (BHWord m) × BHWord m) := fun q =>
        q.2.1.map (fun t => (q.1.2, t.2))
  have hmarked : Primrec marked := by
    exact Primrec.list_map (Primrec.fst.comp Primrec.snd)
      ((Primrec.pair
        (Primrec.snd.comp (Primrec.fst.comp Primrec.fst))
        (Primrec.snd.comp Primrec.snd)).to₂)
  have hall0 : PrimrecPred (fun z : List (BHWord m) × BHWord m => z.2 ∈ z.1) := by
    exact (prim_bhMem (m:=m)).comp Primrec.fst Primrec.snd
  have hall : PrimrecPred
      (fun q : ((BHWord m × List (BHWord m)) × BHCert m) =>
        ∀ z ∈ marked q, z.2 ∈ z.1) :=
    (PrimrecPred.forall_mem_list hall0).comp hmarked
  have he1 : PrimrecPred
      (fun q : ((BHWord m × List (BHWord m)) × BHCert m) =>
        bhRun q.1.1 q.2.2.1 = some q.2.2.2.2) :=
    Primrec.eq.comp
      (prim_bhRun.comp
        (Primrec.fst.comp Primrec.fst)
        (Primrec.fst.comp (Primrec.snd.comp Primrec.snd)))
      (Primrec.option_some.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have he2 : PrimrecPred
      (fun q : ((BHWord m × List (BHWord m)) × BHCert m) =>
        bhRun (bhProd q.2.1) q.2.2.2.1 = some q.2.2.2.2) :=
    Primrec.eq.comp
      (prim_bhRun.comp
        (prim_bhProd.comp (Primrec.fst.comp Primrec.snd))
        (Primrec.fst.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
      (Primrec.option_some.comp
        (Primrec.snd.comp (Primrec.snd.comp (Primrec.snd.comp Primrec.snd))))
  have hb : PrimrecPred
      (fun q : ((BHWord m × List (BHWord m)) × BHCert m) => bhOK q.1 q.2) :=
    (hall.and (he1.and he2)).of_eq (by
      intro q
      have hm : (∀ z ∈ marked q, z.2 ∈ z.1) ↔
          ∀ t ∈ q.2.1, t.2 ∈ q.1.2 := by
        constructor
        · intro h t ht
          have hz : (q.1.2, t.2) ∈ marked q := by
            exact List.mem_map.mpr ⟨t, ht, rfl⟩
          exact h _ hz
        · intro h z hz
          rcases List.mem_map.mp hz with ⟨t, ht, rfl⟩
          exact h t ht
      exact and_congr hm (Iff.rfl))
  exact hb.primrecRel


lemma bhOK_sound {m} {a : BHWord m × List (BHWord m)} {c : BHCert m} (h : bhOK a c) :
    FreeGroup.mk a.1 ∈ Subgroup.normalClosure (FreeGroup.mk '' ( {r | r ∈ a.2} : Set (BHWord m))) := by
  rcases h with ⟨hmem, h1, h2⟩
  have red1 := bhRun_sound h1
  have red2 := bhRun_sound h2
  have eqw : FreeGroup.mk a.1 = FreeGroup.mk (bhProd c.1) :=
    FreeGroup.Red.exact.mpr ⟨c.2.2.2, red1, red2⟩
  rw [mk_bhProd] at eqw
  rw [eqw]
  -- use the explicit finite-product half of the closure description
  apply (mem_normalClosure_list).mpr
  let L : List (FreeGroup (Fin m) × FreeGroup (Fin m)) :=
    c.1.map (fun t => (FreeGroup.mk t.1, FreeGroup.mk t.2))
  refine ⟨L, ?_, ?_⟩
  · intro p hp
    rcases List.mem_map.mp hp with ⟨t, ht, rfl⟩
    exact Or.inl ⟨t.2, hmem t ht, rfl⟩
  · simp [L, Function.comp_def, FreeGroup.mul_mk, FreeGroup.inv_mk]


/- Completeness of the deletion/product certificates when the list of
   relators is closed under formal inverse.  Keeping the closure as words (and
   not as elements of the free group) lets us effectively enumerate it. -/
lemma bhOK_complete {m} {a : BHWord m × List (BHWord m)}
    (hinv : ∀ r ∈ a.2, FreeGroup.invRev r ∈ a.2)
    (h : FreeGroup.mk a.1 ∈
      Subgroup.normalClosure (FreeGroup.mk '' ({r | r ∈ a.2} : Set (BHWord m)))) :
    ∃ c : BHCert m, bhOK a c := by
  classical
  rcases (mem_normalClosure_list.mp h) with ⟨L, hL, heq⟩
  -- Replace every group element occurring in the product by a word.  If the
  -- listed middle element is the inverse of a relator, use the inverse word;
  -- `hinv` keeps it on the finite list.
  have conv : ∀ (L : List (FreeGroup (Fin m) × FreeGroup (Fin m))),
      (∀ p ∈ L, p.2 ∈
          (FreeGroup.mk '' ({r | r ∈ a.2} : Set (BHWord m))) ∨
        p.2⁻¹ ∈ (FreeGroup.mk '' ({r | r ∈ a.2} : Set (BHWord m)))) →
      ∃ T : List (BHWord m × BHWord m),
        (∀ t ∈ T, t.2 ∈ a.2) ∧
        (T.map (fun t : BHWord m × BHWord m =>
            FreeGroup.mk t.1 * FreeGroup.mk t.2 * (FreeGroup.mk t.1)⁻¹)).prod =
          (L.map (fun p : FreeGroup (Fin m) × FreeGroup (Fin m) =>
            p.1 * p.2 * p.1⁻¹)).prod := by
    intro U
    induction U with
    | nil =>
        intro _
        exact ⟨[], by simp, by simp⟩
    | cons p u ih =>
        intro hu
        have hp := hu p (by simp)
        have htail : ∀ q ∈ u,
            q.2 ∈ (FreeGroup.mk '' ({r | r ∈ a.2} : Set (BHWord m))) ∨
              q.2⁻¹ ∈ (FreeGroup.mk '' ({r | r ∈ a.2} : Set (BHWord m))) := by
          intro q hq
          exact hu q (by simp [hq])
        rcases ih htail with ⟨T, hTm, hTe⟩
        -- a representative for the conjugating element
        rcases (Quot.exists_rep p.1) with ⟨uword, huword⟩
        change FreeGroup.mk uword = p.1 at huword
        rcases hp with hp | hp
        · rcases hp with ⟨r, hr, hrmk⟩
          -- `hrmk : mk r = p.2`
          refine ⟨(uword, r) :: T, ?_, ?_⟩
          · intro t ht
            rcases (List.mem_cons.mp ht) with ht | ht
            · cases ht
              exact hr
            · exact hTm _ ht
          · simp only [List.map_cons, List.prod_cons]
            rw [hTe, huword, hrmk]
        · rcases hp with ⟨r, hr, hrmk⟩
          -- now `r` denotes the inverse of the middle element
          let r' : BHWord m := FreeGroup.invRev r
          have hr' : r' ∈ a.2 := by
            exact hinv r hr
          have hr'mk : FreeGroup.mk r' = p.2 := by
            -- formal inverse on representatives agrees with inverse in the
            -- free group
            dsimp [r']
            rw [← FreeGroup.inv_mk]
            -- invert the witnessing equality
            have hx := congrArg (fun z : FreeGroup (Fin m) => z⁻¹) hrmk
            -- `hrmk` has orientation from the image witness
            simpa using hx
          refine ⟨(uword, r') :: T, ?_, ?_⟩
          · intro t ht
            rcases (List.mem_cons.mp ht) with ht | ht
            · cases ht
              exact hr'
            · exact hTm _ ht
          · simp only [List.map_cons, List.prod_cons]
            rw [hTe, huword, hr'mk]
  rcases conv L hL with ⟨T, hTm, hTe⟩
  have eqword : FreeGroup.mk a.1 = FreeGroup.mk (bhProd T) := by
    rw [mk_bhProd]
    -- the two lists of conjugates compute the same product
    exact heq.trans hTe.symm
  rcases (FreeGroup.Red.exact.mp eqword) with ⟨v, hv1, hv2⟩
  rcases (bhRun_complete hv1) with ⟨d1, hd1⟩
  rcases (bhRun_complete hv2) with ⟨d2, hd2⟩
  refine ⟨(T, (d1, d2, v)), ?_⟩
  exact ⟨hTm, hd1, hd2⟩


lemma repred_bhok {m} {γ : Type*} [Primcodable γ]
    (A : γ → BHWord m × List (BHWord m)) (hA : Primrec A) :
    REPred (fun x => ∃ c : BHCert m, bhOK (A x) c) := by
  classical
  have hrel : PrimrecRel (fun x (c : BHCert m) => bhOK (A x) c) := by
    exact (prim_bhOK (m:=m)).comp (hA.comp Primrec.fst) Primrec.snd
  -- restore a computable decision procedure rather than the classical one
  letI dp : DecidableRel (fun x (c : BHCert m) => bhOK (A x) c) :=
    fun x c => decBhOK (A x) c
  exact repred_exists_prim _ hrel


/-- From a finite inverse-closed list of relator words, membership in its
    normal closure is r.e., uniformly in a primitive-recursive word. -/
lemma repred_normalClosure {m} (rs : List (BHWord m))
    (hinv : ∀ r ∈ rs, FreeGroup.invRev r ∈ rs)
    {γ : Type*} [Primcodable γ] (F : γ → BHWord m) (hF : Primrec F) :
    REPred (fun x => FreeGroup.mk (F x) ∈
      Subgroup.normalClosure (FreeGroup.mk '' ({r | r ∈ rs} : Set (BHWord m)))) := by
  let A : γ → BHWord m × List (BHWord m) := fun x => (F x, rs)
  have hA : Primrec A := Primrec.pair hF (Primrec.const rs)
  have hR := repred_bhok A hA
  refine REPred.of_eq hR ?_
  intro x
  constructor
  · rintro ⟨c, hc⟩
    change bhOK (F x, rs) c at hc
    exact (bhOK_sound (a := (F x, rs)) hc)
  · intro hx
    have hx' : FreeGroup.mk (F x) ∈
        Subgroup.normalClosure
          (FreeGroup.mk '' ({r | r ∈ rs} : Set (BHWord m))) := hx
    obtain ⟨c, hc⟩ := (bhOK_complete (a := (F x, rs)) hinv hx')
    refine ⟨c, ?_⟩
    change bhOK (F x, rs) c
    exact hc


/-- add formal inverse representatives; it does not change the normal
    closure. -/
def bhClosed {m} (rs : List (BHWord m)) : List (BHWord m) :=
  rs ++ rs.map FreeGroup.invRev

lemma bhClosed_inv {m} (rs : List (BHWord m)) :
    ∀ r ∈ bhClosed rs, FreeGroup.invRev r ∈ bhClosed rs := by
  intro r hr
  have hi := (List.mem_append.mp hr)
  rcases hi with hi | hi
  · -- inverses of original words are in the second half
    apply List.mem_append.mpr
    right
    exact List.mem_map.mpr ⟨r, hi, rfl⟩
  · rcases List.mem_map.mp hi with ⟨q, hq, hqr⟩
    -- the inverse of an inverse is the original word
    apply List.mem_append.mpr
    left
    subst r
    simpa using hq

lemma normalClosure_bhClosed {m} (rs : List (BHWord m)) :
    Subgroup.normalClosure
        (FreeGroup.mk '' ({r | r ∈ bhClosed rs} : Set (BHWord m))) =
      Subgroup.normalClosure
        (FreeGroup.mk '' ({r | r ∈ rs} : Set (BHWord m))) := by
  -- both inclusions follow from the universal property; all newly added
  -- relators are group inverses of old ones.
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    intro z hz
    rcases hz with ⟨r, hr, rfl⟩
    rcases (List.mem_append.mp hr) with hr | hr
    · exact Subgroup.subset_normalClosure ⟨r, hr, rfl⟩
    · rcases List.mem_map.mp hr with ⟨q, hq, rfl⟩
      have hq' : FreeGroup.mk q ∈
          Subgroup.normalClosure
            (FreeGroup.mk '' ({r | r ∈ rs} : Set (BHWord m))) :=
        Subgroup.subset_normalClosure ⟨q, hq, rfl⟩
      -- inverse in the subgroup
      simpa [FreeGroup.inv_mk] using (Subgroup.inv_mem _ hq')
  · apply Subgroup.normalClosure_mono
    intro z hz
    rcases hz with ⟨r, hr, rfl⟩
    refine ⟨r, ?_, rfl⟩
    exact List.mem_append.mpr (Or.inl hr)

/-- Turn a finite set of free-group elements normally generating a subgroup
    into a word list, with inverse closure built in. -/
lemma relators_words {m} {N : Subgroup (FreeGroup (Fin m))}
    (hN : N.IsNormalClosureFG) :
    ∃ rs : List (BHWord m),
      (∀ r ∈ rs, FreeGroup.invRev r ∈ rs) ∧
      Subgroup.normalClosure
        (FreeGroup.mk '' ({r | r ∈ rs} : Set (BHWord m))) = N := by
  classical
  rcases hN with ⟨S, hSf, hS⟩
  -- choose the quotient representative word of each member of the finite set
  let T : Finset (FreeGroup (Fin m)) := hSf.toFinset
  let chooseWord (x : FreeGroup (Fin m)) : BHWord m := Quot.out x
  have hout (x : FreeGroup (Fin m)) : FreeGroup.mk (chooseWord x) = x := by
    exact Quot.out_eq x
  let base : List (BHWord m) := T.toList.map chooseWord
  refine ⟨bhClosed base, bhClosed_inv base, ?_⟩
  rw [normalClosure_bhClosed]
  have im : (FreeGroup.mk '' ({r | r ∈ base} : Set (BHWord m))) = S := by
    ext x
    constructor
    · rintro ⟨r, hr, rfl⟩
      -- it was chosen from the finite set
      rcases List.mem_map.mp hr with ⟨y, hy, rfl⟩
      have hy' : y ∈ S := by
        have hyT : y ∈ T := Finset.mem_toList.mp hy
        exact (Set.Finite.mem_toFinset hSf).1 (by simpa [T] using hyT)
      simpa [hout y] using hy' 
    · intro hx
      have hx' : x ∈ T := (Set.Finite.mem_toFinset hSf).2 hx
      refine ⟨chooseWord x, ?_, hout x⟩
      apply List.mem_map.mpr
      refine ⟨x, ?_, rfl⟩
      exact (Finset.mem_toList.mpr hx')
  simpa [im] using hS


/-- Substitute fixed words for the generators. -/
def bhSubst {n k : ℕ} (θ : Fin n → BHWord k) (w : BHWord n) : BHWord k :=
  (w.map (fun z : Fin n × Bool => cond z.2 (θ z.1) (FreeGroup.invRev (θ z.1)))).flatten

lemma prim_bhSubst {n k : ℕ} (θ : Fin n → BHWord k) :
    Primrec (bhSubst θ) := by
  have hθ : Primrec θ := Primrec.dom_finite _
  have hp : Primrec (fun z : Fin n × Bool => z.2) := Primrec.snd
  have hz : Primrec (fun z : Fin n × Bool => θ z.1) :=
    hθ.comp Primrec.fst
  have hzi : Primrec (fun z : Fin n × Bool => FreeGroup.invRev (θ z.1)) :=
    prim_invRev.comp hz
  have hl : Primrec (fun z : Fin n × Bool =>
      cond z.2 (θ z.1) (FreeGroup.invRev (θ z.1))) :=
    Primrec.cond hp hz hzi
  unfold bhSubst
  exact Primrec.list_flatten.comp
    (Primrec.list_map Primrec.id (hl.comp Primrec.snd).to₂)

lemma mk_bhSubst {n k : ℕ} (θ : Fin n → BHWord k) (w : BHWord n) :
    FreeGroup.mk (bhSubst θ w) =
      FreeGroup.lift (fun i => FreeGroup.mk (θ i)) (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons z t ih =>
    rcases z with ⟨i,b⟩
    cases b with
    | false =>
      -- negative letter
      change FreeGroup.mk (FreeGroup.invRev (θ i) ++ bhSubst θ t) = _
      rw [← FreeGroup.mul_mk]
      rw [← FreeGroup.inv_mk]
      -- `lift_mk`/the inductive tail is multiplication of the head and tail
      change (FreeGroup.mk (θ i))⁻¹ * FreeGroup.mk (bhSubst θ t) =
        (FreeGroup.mk (θ i))⁻¹ *
          (List.map (fun x : Fin n × Bool =>
            cond x.2 (FreeGroup.mk (θ x.1)) (FreeGroup.mk (θ x.1))⁻¹) t).prod
      rw [ih]
      rfl
    | true =>
      change FreeGroup.mk (θ i ++ bhSubst θ t) = _
      rw [← FreeGroup.mul_mk]
      change FreeGroup.mk (θ i) * FreeGroup.mk (bhSubst θ t) =
        FreeGroup.mk (θ i) *
          (List.map (fun x : Fin n × Bool =>
            cond x.2 (FreeGroup.mk (θ x.1)) (FreeGroup.mk (θ x.1))⁻¹) t).prod
      rw [ih]
      rfl


lemma lift_subst {X : Type*} [Group X] {n k : ℕ}
    (ψ : FreeGroup (Fin k) →* X) (u : FreeGroup (Fin n) →* X)
    (θ : Fin n → BHWord k)
    (hθ : ∀ i, ψ (FreeGroup.mk (θ i)) = u (FreeGroup.of i))
    (w : BHWord n) :
    ψ (FreeGroup.mk (bhSubst θ w)) = u (FreeGroup.mk w) := by
  let Lh : FreeGroup (Fin n) →* FreeGroup (Fin k) :=
    FreeGroup.lift (fun i => FreeGroup.mk (θ i))
  have he : ψ.comp Lh = u := by
    apply DFunLike.ext _ _
    intro x
    calc
      (ψ.comp Lh) x =
          FreeGroup.lift (fun i => ψ (FreeGroup.mk (θ i))) x := by
            apply FreeGroup.lift_unique
            intro i
            simp [Lh]
      _ = u x := by
            symm
            apply FreeGroup.lift_unique
            exact fun i => (hθ i).symm
  rw [mk_bhSubst]
  exact DFunLike.congr_fun he (FreeGroup.mk w)

lemma word_preimage {X : Type*} [Group X] {k : ℕ}
    (ψ : FreeGroup (Fin k) →* X) (hψ : Function.Surjective ψ) (x : X) :
    ∃ w : BHWord k, ψ (FreeGroup.mk w) = x := by
  rcases hψ x with ⟨z, hz⟩
  rcases (Quot.exists_rep z) with ⟨w, hw⟩
  change FreeGroup.mk w = z at hw
  exact ⟨w, by rw [hw, hz]⟩

/- A word for a product of conjugates of a varying word `bhSubst θ w` (or
   its inverse).  `true` chooses the word, `false` its inverse. -/
def bhNormProd {n k : ℕ} (θ : Fin n → BHWord k)
    (w : BHWord n) (L : List (BHWord k × Bool)) : BHWord k :=
  (L.map (fun t => t.1 ++
      (cond t.2 (bhSubst θ w) (FreeGroup.invRev (bhSubst θ w))) ++
      FreeGroup.invRev t.1)).flatten

def bhNormEq {n k : ℕ} (θ : Fin n → BHWord k) (v : BHWord k)
    (w : BHWord n) (L : List (BHWord k × Bool)) : BHWord k :=
  FreeGroup.invRev v ++ bhNormProd θ w L

lemma prim_bhNormProd {n k : ℕ} (θ : Fin n → BHWord k) :
    Primrec₂ (bhNormProd θ) := by
  have hs : Primrec (bhSubst θ) := prim_bhSubst θ
  -- primitive recursion is a map followed by flatten; the word parameter is
  -- kept as the first component of the pair.
  have hg : Primrec₂ (fun q : BHWord n × List (BHWord k × Bool) =>
        fun t : BHWord k × Bool => t.1 ++
          (cond t.2 (bhSubst θ q.1) (FreeGroup.invRev (bhSubst θ q.1))) ++
          FreeGroup.invRev t.1) := by
    -- first form the middle word from the flag
    have hm : Primrec (fun z : (BHWord n × List (BHWord k × Bool)) ×
          (BHWord k × Bool) =>
          cond z.2.2 (bhSubst θ z.1.1)
            (FreeGroup.invRev (bhSubst θ z.1.1))) := by
      have hp : Primrec (fun z : (BHWord n × List (BHWord k × Bool)) ×
          (BHWord k × Bool) => z.2.2) := Primrec.snd.comp Primrec.snd
      have hw : Primrec (fun z : (BHWord n × List (BHWord k × Bool)) ×
          (BHWord k × Bool) => bhSubst θ z.1.1) :=
        hs.comp (Primrec.fst.comp Primrec.fst)
      exact Primrec.cond hp hw (prim_invRev.comp hw)
    have ha : Primrec (fun z : (BHWord n × List (BHWord k × Bool)) ×
          (BHWord k × Bool) => z.2.1) := Primrec.fst.comp Primrec.snd
    have hi : Primrec (fun z : (BHWord n × List (BHWord k × Bool)) ×
          (BHWord k × Bool) => FreeGroup.invRev z.2.1) :=
      prim_invRev.comp ha
    exact (Primrec.list_append.comp
        (Primrec.list_append.comp ha hm) hi).to₂
  -- map this factor over the list, then flatten
  exact (Primrec.list_flatten.comp
    (Primrec.list_map Primrec.snd hg)).to₂

lemma prim_bhNormEq {n k : ℕ} (θ : Fin n → BHWord k) (v : BHWord k) :
    Primrec₂ (bhNormEq θ v) := by
  unfold bhNormEq
  have hc : Primrec
      (fun q : BHWord n × List (BHWord k × Bool) => FreeGroup.invRev v) :=
    Primrec.const _
  exact (Primrec.list_append.comp hc
    (prim_bhNormProd θ)).to₂

lemma mk_bhNormProd {n k : ℕ} (θ : Fin n → BHWord k)
    (w : BHWord n) (L : List (BHWord k × Bool)) :
    FreeGroup.mk (bhNormProd θ w L) =
      (L.map (fun t => FreeGroup.mk t.1 *
          (cond t.2 (FreeGroup.mk (bhSubst θ w))
            ((FreeGroup.mk (bhSubst θ w))⁻¹)) *
          (FreeGroup.mk t.1)⁻¹)).prod := by
  induction L with
  | nil => rfl
  | cons t u ih =>
    rcases t with ⟨q,b⟩
    cases b with
    | false =>
      simp only [bhNormProd, List.map_cons, List.flatten_cons, List.prod_cons]
      simp only [cond_false]
      rw [← ih]
      change FreeGroup.mk (q ++ FreeGroup.invRev (bhSubst θ w) ++
        FreeGroup.invRev q ++ bhNormProd θ w u) = _
      rw [FreeGroup.inv_mk, FreeGroup.inv_mk]
      repeat' rw [FreeGroup.mul_mk]
    | true =>
      simp only [bhNormProd, List.map_cons, List.flatten_cons, List.prod_cons]
      simp only [cond_true]
      rw [← ih]
      change FreeGroup.mk (q ++ bhSubst θ w ++
        FreeGroup.invRev q ++ bhNormProd θ w u) = _
      rw [FreeGroup.inv_mk]
      repeat' rw [FreeGroup.mul_mk]

/-ResultProofDefinitionsEnd-/


theorem boone_higman_embedding {G H K : Type*} [Group G] [Group H] [Group K]
    [IsSimpleGroup H] [Group.IsFinitelyPresented K]
    (f : G →* H) (hf : Function.Injective f)
    (g : H →* K) (hg : Function.Injective g)
    {n : ℕ} (φ : FreeGroup (Fin n) →* G)
    (hsurj : Function.Surjective φ)
    (hker : (MonoidHom.ker φ).IsNormalClosureFG) :
    WordProblemSolvable φ := by
  classical
  -- finite relator lists for the two finite presentations
  obtain ⟨rG, hiG, heG⟩ := relators_words hker
  obtain ⟨k, ψ, hψ, hNK⟩ :=
    (inferInstance : Group.IsFinitelyPresented K).out
  obtain ⟨rK, hiK, heK⟩ := relators_words hNK
  let u0 : G →* K := g.comp f
  let u : FreeGroup (Fin n) →* K := u0.comp φ
  have huinj : Function.Injective u0 := hg.comp hf
  -- spell the images of the finitely many generators in the presentation of K
  have gen : ∀ i : Fin n, ∃ q : BHWord k,
      ψ (FreeGroup.mk q) = u (FreeGroup.of i) := by
    intro i
    exact word_preimage ψ hψ _
  choose θ hθ using gen
  have hsub (w : BHWord n) :
      ψ (FreeGroup.mk (bhSubst θ w)) = u (FreeGroup.mk w) :=
    lift_subst ψ u θ hθ w
  -- a fixed nonidentity member of the simple subgroup
  obtain ⟨a0, ha0⟩ := exists_ne (1 : H)
  obtain ⟨v, hv⟩ := word_preimage ψ hψ (g a0)

  -- positive instances are enumerated straight from the given presentation
  have hp0 : REPred (fun w : BHWord n => FreeGroup.mk w ∈
        Subgroup.normalClosure
          (FreeGroup.mk '' ({r | r ∈ rG} : Set (BHWord n)))) :=
    repred_normalClosure rG hiG (fun w : BHWord n => w) Primrec.id
  have hp : REPred (fun w : BHWord n => φ (FreeGroup.mk w) = 1) := by
    refine REPred.of_eq hp0 ?_
    intro w
    rw [heG]
    exact MonoidHom.mem_ker

  -- certificates for a negative instance consist of a list of conjugators
  -- and one ordinary kernel certificate in the presentation of K.
  let Q := List (BHWord k × Bool)
  have hrel : PrimrecRel (fun (w : BHWord n) (d : Q × BHCert k) =>
      bhOK (bhNormEq θ v w d.1, rK) d.2) := by
    have harg : Primrec (fun z : BHWord n × (Q × BHCert k) =>
        (bhNormEq θ v z.1 z.2.1, rK)) := by
      exact Primrec.pair
        (prim_bhNormEq θ v |>.comp Primrec.fst
          (Primrec.fst.comp Primrec.snd))
        (Primrec.const rK)
    exact (prim_bhOK (m:=k)).comp harg
      (Primrec.snd.comp Primrec.snd)
  letI drel : DecidableRel (fun (w : BHWord n) (d : Q × BHCert k) =>
      bhOK (bhNormEq θ v w d.1, rK) d.2) :=
    fun w d => decBhOK (bhNormEq θ v w d.1, rK) d.2
  have hn0 : REPred (fun w : BHWord n =>
      ∃ d : Q × BHCert k, bhOK (bhNormEq θ v w d.1, rK) d.2) :=
    repred_exists_prim _ hrel

  have hn : REPred (fun w : BHWord n => ¬ φ (FreeGroup.mk w) = 1) := by
    refine REPred.of_eq hn0 ?_
    intro w
    constructor
    · rintro ⟨⟨L,c⟩, hc⟩ href
      -- if the word were trivial every conjugate in the product is one;
      -- the kernel equation would force our fixed `g a0` to be one.
      have km := (bhOK_sound (a := (bhNormEq θ v w L, rK)) hc)
      rw [heK] at km
      have keq : ψ (FreeGroup.mk (bhNormEq θ v w L)) = 1 :=
        MonoidHom.mem_ker.mp km
      have yone : ψ (FreeGroup.mk (bhSubst θ w)) = 1 := by
        rw [hsub]
        change u0 (φ (FreeGroup.mk w)) = _
        simp [href]
      have helpOne : ∀ T : List (BHWord k × Bool),
          ψ (FreeGroup.mk (bhNormProd θ w T)) = 1 := by
        intro T
        rw [mk_bhNormProd]
        induction T with
        | nil => simp
        | cons t z iz =>
          simp only [List.map_cons, List.prod_cons, map_mul]
          rw [iz]
          rcases t with ⟨t,b⟩
          cases b <;>
            simp [← FreeGroup.inv_mk, yone]
      have pone : ψ (FreeGroup.mk (bhNormProd θ w L)) = 1 :=
        helpOne L
      have bad : g a0 = 1 := by
        -- expand the equation `v⁻¹ * product = 1`
        change ψ (FreeGroup.mk (FreeGroup.invRev v ++ bhNormProd θ w L)) = 1 at keq
        rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul,
          map_inv, hv, pone, mul_one] at keq
        -- keq : (g a0)⁻¹ = 1
        simpa using congrArg (fun z : K => z⁻¹) keq
      exact ha0 (hg (by simpa using bad))
    · intro hne
      -- Simplicity: a nontrivial element normally generates H
      let aa : H := f (φ (FreeGroup.mk w))
      have haa : aa ≠ 1 := by
        intro hh
        apply hne
        exact hf (by simpa [aa] using hh)
      have atop : Subgroup.normalClosure ({aa} : Set H) = ⊤ := by
        rcases (Subgroup.normalClosure_normal (s := ({aa} : Set H))).eq_bot_or_eq_top with hb | ht
        · have hm : aa ∈ Subgroup.normalClosure ({aa} : Set H) :=
            Subgroup.subset_normalClosure (Set.mem_singleton _)
          rw [hb] at hm
          exact (haa (Subgroup.mem_bot.mp hm)).elim
        · exact ht
      have hmem0 : a0 ∈ Subgroup.normalClosure ({aa} : Set H) := by
        rw [atop]
        trivial
      rcases (mem_normalClosure_list.mp hmem0) with ⟨LH, hLH, eLH⟩
      -- turn the finitely many conjugators from H into words of K.
      have conv : ∀ (T : List (H × H)),
          (∀ p ∈ T, p.2 ∈ ({aa} : Set H) ∨ p.2⁻¹ ∈ ({aa} : Set H)) →
          ∃ LW : Q, ψ (FreeGroup.mk (bhNormProd θ w LW)) =
              g ((T.map (fun p : H × H => p.1 * p.2 * p.1⁻¹)).prod) := by
        intro T
        induction T with
        | nil =>
            intro _
            refine ⟨[], ?_⟩
            change ψ (FreeGroup.mk []) = g 1
            change ψ 1 = g 1
            simp
        | cons p t ih =>
            intro ht
            have hpt := ht p (by simp)
            have htt : ∀ z ∈ t, z.2 ∈ ({aa} : Set H) ∨ z.2⁻¹ ∈ ({aa} : Set H) := by
              intro z hz
              exact ht z (by simp [hz])
            rcases ih htt with ⟨R, hR⟩
            obtain ⟨q, hq⟩ := word_preimage ψ hψ (g p.1)
            have hR' := hR
            rw [mk_bhNormProd] at hR'
            have yy : ψ (FreeGroup.mk (bhSubst θ w)) = g aa := by
              rw [hsub]
              rfl
            rcases hpt with hpt | hpt
            · have pe : p.2 = aa := Set.mem_singleton_iff.mp hpt
              refine ⟨(q,true) :: R, ?_⟩
              rw [mk_bhNormProd]
              simp only [List.map_cons, List.prod_cons, cond_true, map_mul, map_inv]
              rw [yy, hq]
              rw [← pe]
              rw [hR']
            · have pe0 : p.2⁻¹ = aa := Set.mem_singleton_iff.mp hpt
              have pe : p.2 = aa⁻¹ := by
                simpa using congrArg (fun z : H => z⁻¹) pe0
              refine ⟨(q,false) :: R, ?_⟩
              rw [mk_bhNormProd]
              simp only [List.map_cons, List.prod_cons, cond_false, map_mul, map_inv]
              rw [yy, hq]
              rw [pe, hR']
              simp
      rcases conv LH hLH with ⟨LW, hLW⟩
      have kval : ψ (FreeGroup.mk (bhNormEq θ v w LW)) = 1 := by
        unfold bhNormEq
        rw [← FreeGroup.mul_mk, ← FreeGroup.inv_mk, map_mul, map_inv,
          hv, hLW, ← eLH]
        simp
      have kmem : FreeGroup.mk (bhNormEq θ v w LW) ∈
          Subgroup.normalClosure
            (FreeGroup.mk '' ({r | r ∈ rK} : Set (BHWord k))) := by
        rw [heK]
        exact MonoidHom.mem_ker.mpr kval
      obtain ⟨c, hc⟩ :=
        (bhOK_complete (a := (bhNormEq θ v w LW, rK)) hiK kmem)
      exact ⟨⟨LW, c⟩, hc⟩
  unfold WordProblemSolvable
  exact (ComputablePred.computable_iff_re_compl_re').2 ⟨hp, hn⟩


end Submission
