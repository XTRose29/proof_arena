import ChallengeDeps
import Mathlib.GroupTheory.FreeGroup.Reduce

namespace Submission.Helpers

abbrev Word (n : ℕ) := List (Fin n × Bool)

abbrev Factor (n : ℕ) := Word n × Word n × Bool

def relatorSet {n : ℕ} (relations : List (Word n)) : Set (FreeGroup (Fin n)) :=
  FreeGroup.mk '' {word | word ∈ relations}

def signedWord {n : ℕ} (positive : Bool) (word : Word n) : Word n :=
  if positive then word else FreeGroup.invRev word

def factorWord {n : ℕ} (factor : Factor n) : Word n :=
  factor.1 ++ signedWord factor.2.2 factor.2.1 ++ FreeGroup.invRev factor.1

def witnessWord {n : ℕ} (witness : List (Factor n)) : Word n :=
  (witness.map factorWord).flatten

def factorValue {n : ℕ} (factor : Factor n) : FreeGroup (Fin n) :=
  FreeGroup.mk factor.1 *
    (if factor.2.2 then FreeGroup.mk factor.2.1 else (FreeGroup.mk factor.2.1)⁻¹) *
      (FreeGroup.mk factor.1)⁻¹

def witnessValue {n : ℕ} (witness : List (Factor n)) : FreeGroup (Fin n) :=
  (witness.map factorValue).prod

def invertFactor {n : ℕ} (factor : Factor n) : Factor n :=
  (factor.1, factor.2.1, !factor.2.2)

def invertWitness {n : ℕ} (witness : List (Factor n)) : List (Factor n) :=
  (witness.map invertFactor).reverse

def ValidWitness {n : ℕ} (relations : List (Word n)) (witness : List (Factor n)) : Prop :=
  ∀ factor ∈ witness, factor.2.1 ∈ relations

def NCWitness {n : ℕ} (relations : List (Word n)) (target : Word n)
    (witness : List (Factor n)) : Prop :=
  ValidWitness relations witness ∧
    FreeGroup.reduce (witnessWord witness) = FreeGroup.reduce target

@[simp]
theorem mk_signedWord {n : ℕ} (positive : Bool) (word : Word n) :
    FreeGroup.mk (signedWord positive word) =
      if positive then FreeGroup.mk word else (FreeGroup.mk word)⁻¹ := by
  cases positive <;> simp [signedWord, ← FreeGroup.inv_mk]

@[simp]
theorem mk_factorWord {n : ℕ} (factor : Factor n) :
    FreeGroup.mk (factorWord factor) = factorValue factor := by
  simp [factorWord, factorValue, ← FreeGroup.mul_mk, ← FreeGroup.inv_mk, mul_assoc]

@[simp]
theorem mk_witnessWord {n : ℕ} (witness : List (Factor n)) :
    FreeGroup.mk (witnessWord witness) = witnessValue witness := by
  induction witness with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons factor witness ih =>
      rw [show witnessWord (factor :: witness) = factorWord factor ++ witnessWord witness by
        simp [witnessWord]]
      rw [← FreeGroup.mul_mk, mk_factorWord, ih]
      rfl

@[simp]
theorem factorValue_invertFactor {n : ℕ} (factor : Factor n) :
    factorValue (invertFactor factor) = (factorValue factor)⁻¹ := by
  rcases factor with ⟨conjugator, relation, positive⟩
  cases positive <;> simp [factorValue, invertFactor]

@[simp]
theorem witnessValue_invertWitness {n : ℕ} (witness : List (Factor n)) :
    witnessValue (invertWitness witness) = (witnessValue witness)⁻¹ := by
  unfold witnessValue invertWitness
  rw [List.map_reverse, List.map_map]
  rw [show factorValue ∘ invertFactor = fun factor : Factor n => (factorValue factor)⁻¹ by
    funext factor
    exact factorValue_invertFactor factor]
  simpa only [List.map_map, Function.comp_def] using
    (List.prod_inv_reverse (witness.map factorValue)).symm

theorem validWitness_append {n : ℕ} {relations : List (Word n)}
    {left right : List (Factor n)}
    (hleft : ValidWitness relations left) (hright : ValidWitness relations right) :
    ValidWitness relations (left ++ right) := by
  intro factor hfactor
  exact (List.mem_append.mp hfactor).elim (hleft factor) (hright factor)

theorem validWitness_invertWitness {n : ℕ} {relations : List (Word n)}
    {witness : List (Factor n)} (hvalid : ValidWitness relations witness) :
    ValidWitness relations (invertWitness witness) := by
  intro factor hfactor
  simp only [invertWitness, List.mem_reverse, List.mem_map] at hfactor
  obtain ⟨original, horiginal, rfl⟩ := hfactor
  exact hvalid original horiginal

theorem exists_ncWitness_iff_mem_normalClosure {n : ℕ} (relations : List (Word n))
    (target : Word n) :
    (∃ witness, NCWitness relations target witness) ↔
      FreeGroup.mk target ∈ Subgroup.normalClosure (relatorSet relations) := by
  constructor
  · rintro ⟨witness, hvalid, heq⟩
    have hwitness : witnessValue witness ∈ Subgroup.normalClosure (relatorSet relations) := by
      clear heq target
      induction witness with
      | nil => simp [witnessValue]
      | cons factor witness ih =>
          have hrelation : FreeGroup.mk factor.2.1 ∈ relatorSet relations :=
            ⟨factor.2.1, hvalid factor (by simp), rfl⟩
          have hrelationNC :
              FreeGroup.mk factor.2.1 ∈ Subgroup.normalClosure (relatorSet relations) :=
            Subgroup.subset_normalClosure hrelation
          have hsigned :
              (if factor.2.2 then FreeGroup.mk factor.2.1 else (FreeGroup.mk factor.2.1)⁻¹) ∈
                Subgroup.normalClosure (relatorSet relations) := by
            cases factor.2.2
            · exact Subgroup.inv_mem _ hrelationNC
            · exact hrelationNC
          have hfactor : factorValue factor ∈ Subgroup.normalClosure (relatorSet relations) := by
            exact Subgroup.normalClosure_normal.conj_mem _ hsigned _
          exact Subgroup.mul_mem _ hfactor (ih fun f hf => hvalid f (by simp [hf]))
    have hmk := FreeGroup.reduce.exact heq
    rw [← hmk, mk_witnessWord]
    exact hwitness
  · intro htarget
    have hconstruct : ∀ x ∈ Subgroup.normalClosure (relatorSet relations),
        ∃ witness, ValidWitness relations witness ∧ witnessValue witness = x := by
      intro x hx
      induction hx using Subgroup.closure_induction with
      | mem x hx =>
          obtain ⟨relation, hrelation, hconj⟩ := Group.mem_conjugatesOfSet_iff.mp hx
          obtain ⟨word, hword, rfl⟩ := hrelation
          change word ∈ relations at hword
          obtain ⟨conjugator, rfl⟩ := isConj_iff.mp hconj
          refine ⟨[(conjugator.toWord, word, true)], ?_, ?_⟩
          · intro factor hfactor
            simp only [List.mem_singleton] at hfactor
            subst factor
            exact hword
          · simp [witnessValue, factorValue, FreeGroup.mk_toWord]
      | one =>
          exact ⟨[], by simp [ValidWitness], by simp [witnessValue]⟩
      | mul x y _ _ hx hy =>
          obtain ⟨left, hleft, rfl⟩ := hx
          obtain ⟨right, hright, rfl⟩ := hy
          refine ⟨left ++ right, validWitness_append hleft hright, ?_⟩
          simp [witnessValue]
      | inv x _ hx =>
          obtain ⟨witness, hvalid, rfl⟩ := hx
          exact ⟨invertWitness witness, validWitness_invertWitness hvalid,
            witnessValue_invertWitness witness⟩
    obtain ⟨witness, hvalid, hwitness⟩ := hconstruct _ htarget
    refine ⟨witness, hvalid, ?_⟩
    apply FreeGroup.reduce.sound
    rw [mk_witnessWord, hwitness]

theorem primrec_invRev {n : ℕ} : Primrec (@FreeGroup.invRev (Fin n)) := by
  have hletter : Primrec (fun letter : Fin n × Bool => (letter.1, !letter.2)) :=
    Primrec.fst.pair (Primrec.not.comp Primrec.snd)
  exact Primrec.list_reverse.comp
    (Primrec.list_map Primrec.id ((hletter.comp Primrec.snd).to₂))

theorem primrec_signedWord {n : ℕ} : Primrec₂ (@signedWord n) := by
  refine (Primrec.cond Primrec.fst Primrec.snd
    (primrec_invRev.comp Primrec.snd)).of_eq ?_
  rintro ⟨positive, word⟩
  cases positive <;> rfl

theorem primrec_factorWord {n : ℕ} : Primrec (@factorWord n) := by
  have hsigned : Primrec (fun factor : Factor n => signedWord factor.2.2 factor.2.1) :=
    primrec_signedWord.comp (Primrec.snd.comp Primrec.snd) (Primrec.fst.comp Primrec.snd)
  exact Primrec.list_append.comp
    (Primrec.list_append.comp Primrec.fst hsigned) (primrec_invRev.comp Primrec.fst)

theorem primrec_witnessWord {n : ℕ} : Primrec (@witnessWord n) := by
  exact Primrec.list_flatten.comp
    (Primrec.list_map Primrec.id ((primrec_factorWord.comp Primrec.snd).to₂))

def reduceCons {n : ℕ} (letter : Fin n × Bool) (word : Word n) : Word n :=
  match word with
  | [] => [letter]
  | head :: tail =>
      if letter.1 = head.1 ∧ letter.2 = !head.2 then tail else letter :: head :: tail

theorem primrec_reduceCons {n : ℕ} : Primrec₂ (@reduceCons n) := by
  let Letter := Fin n × Bool
  let P := Letter × Word n
  have hnil : Primrec (fun input : P => [input.1]) :=
    Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  have hpLetter : Primrec (fun input : P × (Letter × Word n) => input.1.1) :=
    Primrec.fst.comp Primrec.fst
  have hhead : Primrec (fun input : P × (Letter × Word n) => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have htail : Primrec (fun input : P × (Letter × Word n) => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have hcancel : PrimrecPred (fun input : P × (Letter × Word n) =>
      input.1.1.1 = input.2.1.1 ∧ input.1.1.2 = !input.2.1.2) :=
    (Primrec.eq.comp (Primrec.fst.comp hpLetter) (Primrec.fst.comp hhead)).and
      (Primrec.eq.comp (Primrec.snd.comp hpLetter)
        (Primrec.not.comp (Primrec.snd.comp hhead)))
  have hkeep : Primrec (fun input : P × (Letter × Word n) =>
      input.1.1 :: input.2.1 :: input.2.2) :=
    Primrec.list_cons.comp hpLetter (Primrec.list_cons.comp hhead htail)
  have hstep : Primrec₂ (fun (input : P) (headTail : Letter × Word n) =>
      if input.1.1 = headTail.1.1 ∧ input.1.2 = !headTail.1.2 then headTail.2
      else input.1 :: headTail.1 :: headTail.2) :=
    Primrec.ite hcancel htail hkeep
  exact (Primrec.list_casesOn Primrec.snd hnil hstep).of_eq fun input => by
    cases input.2 <;> rfl

theorem reduce_eq_foldr {n : ℕ} (word : Word n) :
    FreeGroup.reduce word = word.foldr reduceCons [] := by
  induction word with
  | nil => rfl
  | cons letter word ih =>
      rw [FreeGroup.reduce.cons, ih]
      simp only [List.foldr_cons]
      cases hred : word.foldr reduceCons [] with
      | nil => simp [reduceCons]
      | cons head tail => simp [reduceCons]

theorem primrec_reduce {n : ℕ} : Primrec (@FreeGroup.reduce (Fin n) inferInstance) := by
  have hstep : Primrec₂ (fun (_word : Word n) (input : (Fin n × Bool) × Word n) =>
      reduceCons input.1 input.2) :=
    (primrec_reduceCons.comp (Primrec.fst.comp Primrec.snd)
      (Primrec.snd.comp Primrec.snd)).to₂
  have hfold : Primrec (fun word : Word n => word.foldr reduceCons []) :=
    Primrec.list_foldr (f := fun word : Word n => word) (g := fun _ => [])
      (h := fun _ input => reduceCons input.1 input.2) Primrec.id (Primrec.const []) hstep
  exact hfold.of_eq fun word => (reduce_eq_foldr word).symm

theorem primrecRel_word_mem {n : ℕ} :
    PrimrecRel (fun (relations : List (Word n)) word => word ∈ relations) := by
  exact (PrimrecRel.exists_mem_list (Primrec.eq (α := Word n))).of_eq (by simp)

theorem primrecRel_validWitness {n : ℕ} : PrimrecRel (@ValidWitness n) := by
  have hfactorRelator : Primrec₂ (fun (factor : Factor n) (_relations : List (Word n)) =>
      factor.2.1) :=
    (Primrec.fst.comp Primrec.snd).comp₂ Primrec₂.left
  have hfactorMem : PrimrecRel (fun (factor : Factor n) (relations : List (Word n)) =>
      factor.2.1 ∈ relations) :=
    primrecRel_word_mem.comp₂ Primrec₂.right hfactorRelator
  exact hfactorMem.forall_mem_list.swap.of_eq fun _ _ => Iff.rfl

theorem primrecPred_ncWitness {n : ℕ} :
    PrimrecPred (fun input : List (Word n) × Word n × List (Factor n) =>
      NCWitness input.1 input.2.1 input.2.2) := by
  have hvalid : PrimrecPred (fun input : List (Word n) × Word n × List (Factor n) =>
      ValidWitness input.1 input.2.2) :=
    primrecRel_validWitness.comp Primrec.fst (Primrec.snd.comp Primrec.snd)
  have heq : PrimrecPred (fun input : List (Word n) × Word n × List (Factor n) =>
      FreeGroup.reduce (witnessWord input.2.2) = FreeGroup.reduce input.2.1) :=
    Primrec.eq.comp
      (primrec_reduce.comp (primrec_witnessWord.comp (Primrec.snd.comp Primrec.snd)))
      (primrec_reduce.comp (Primrec.fst.comp Primrec.snd))
  exact hvalid.and heq

theorem computablePred_comp {α β : Type*} [Primcodable α] [Primcodable β]
    {predicate : β → Prop} (hpredicate : ComputablePred predicate)
    {f : α → β} (hf : Computable f) : ComputablePred (fun input => predicate (f input)) := by
  obtain ⟨test, htest, hspec⟩ := ComputablePred.computable_iff.mp hpredicate
  refine ComputablePred.computable_iff.mpr ⟨test ∘ f, htest.comp hf, ?_⟩
  rw [hspec]
  rfl

theorem rePred_exists {α β : Type*} [Primcodable α] [Primcodable β]
    {predicate : α → β → Prop}
    (hpredicate : ComputablePred (fun input : α × β => predicate input.1 input.2)) :
    REPred (fun input => ∃ witness, predicate input witness) := by
  obtain ⟨test, htest, hspec⟩ := ComputablePred.computable_iff.mp hpredicate
  let searchTest : α → ℕ → Bool := fun input code =>
    ((Encodable.decode (α := β) code).map fun witness => test (input, witness)).getD false
  have htest₂ : Computable₂ (fun input witness => test (input, witness)) := htest.to₂
  have hdecoded : Computable₂ (fun input code =>
      (Encodable.decode (α := β) code).map fun witness => test (input, witness)) :=
    Computable.map_decode_iff.mpr htest₂
  have hsearchTest : Computable₂ searchTest := by
    exact Computable.option_getD hdecoded (Computable.const false)
  have hsearch : Partrec (fun input => Nat.rfind fun code => Part.some (searchTest input code)) :=
    Partrec.rfind hsearchTest.partrec₂
  refine (Partrec.dom_re hsearch).of_eq fun input => ?_
  rw [Nat.rfind_dom]
  simp only [Part.mem_some_iff, Part.some_dom]
  constructor
  · rintro ⟨code, hcode⟩
    unfold searchTest at hcode
    cases hdecode : Encodable.decode (α := β) code with
    | none => simp [hdecode] at hcode
    | some witness =>
        refine ⟨witness, ?_⟩
        have htestTrue : test (input, witness) = true := by
          simpa [hdecode] using hcode.symm
        have hiff : predicate input witness ↔ test (input, witness) = true := by
          exact Iff.of_eq (congr_fun hspec (input, witness))
        exact hiff.mpr htestTrue
  · rintro ⟨witness, hwitness⟩
    refine ⟨Encodable.encode witness, ?_⟩
    have hiff : predicate input witness ↔ test (input, witness) = true := by
      exact Iff.of_eq (congr_fun hspec (input, witness))
    simpa [searchTest] using (hiff.mp hwitness).symm

theorem normalClosure_re {α : Type*} [Primcodable α] {n : ℕ}
    (relations : α → List (Word n)) (target : α → Word n)
    (hrelations : Computable relations) (htarget : Computable target) :
    REPred (fun input =>
      FreeGroup.mk (target input) ∈ Subgroup.normalClosure (relatorSet (relations input))) := by
  let verifierInput : α × List (Factor n) → List (Word n) × Word n × List (Factor n) :=
    fun input => (relations input.1, target input.1, input.2)
  have hverifierInput : Computable verifierInput :=
    (hrelations.comp Computable.fst).pair
      ((htarget.comp Computable.fst).pair Computable.snd)
  have hverifier : ComputablePred (fun input : α × List (Factor n) =>
      NCWitness (relations input.1) (target input.1) input.2) :=
    computablePred_comp primrecPred_ncWitness.computablePred hverifierInput
  exact (rePred_exists hverifier).of_eq fun input =>
    exists_ncWitness_iff_mem_normalClosure (relations input) (target input)

def substitute {n m : ℕ} (images : Fin n → Word m) (word : Word n) : Word m :=
  (word.map fun letter => signedWord letter.2 (images letter.1)).flatten

theorem mk_substitute {n m : ℕ} (images : Fin n → Word m) (word : Word n) :
    FreeGroup.mk (substitute images word) =
      FreeGroup.lift (fun generator => FreeGroup.mk (images generator)) (FreeGroup.mk word) := by
  rw [FreeGroup.lift_mk]
  induction word with
  | nil => exact FreeGroup.one_eq_mk.symm
  | cons letter word ih =>
      rw [show substitute images (letter :: word) =
          signedWord letter.2 (images letter.1) ++ substitute images word by
        simp [substitute]]
      rw [← FreeGroup.mul_mk, mk_signedWord, ih]
      rcases letter with ⟨generator, positive⟩
      cases positive <;> simp

theorem primrec_substitute {n m : ℕ} (images : Fin n → Word m) :
    Primrec (substitute images) := by
  have himages : Primrec images :=
    Primrec.fin_app.comp (Primrec.const images) Primrec.id
  have hletter : Primrec (fun letter : Fin n × Bool =>
      signedWord letter.2 (images letter.1)) :=
    primrec_signedWord.comp Primrec.snd (himages.comp Primrec.fst)
  exact Primrec.list_flatten.comp
    (Primrec.list_map Primrec.id ((hletter.comp Primrec.snd).to₂))

@[simp]
theorem relatorSet_cons {n : ℕ} (relation : Word n) (relations : List (Word n)) :
    relatorSet (relation :: relations) =
      ({FreeGroup.mk relation} : Set (FreeGroup (Fin n))) ∪ relatorSet relations := by
  ext x
  simp [relatorSet, eq_comm]

theorem map_normalClosure_cons_of_base_eq_ker {n : ℕ} {K : Type*} [Group K]
    (presentation : FreeGroup (Fin n) →* K) (hpresentation : Function.Surjective presentation)
    (relations : List (Word n))
    (hbase : Subgroup.normalClosure (relatorSet relations) = MonoidHom.ker presentation)
    (extra : Word n) :
    (Subgroup.normalClosure (relatorSet (extra :: relations))).map presentation =
      Subgroup.normalClosure ({presentation (FreeGroup.mk extra)} : Set K) := by
  rw [Subgroup.map_normalClosure _ presentation hpresentation]
  apply le_antisymm
  · apply Subgroup.normalClosure_le_normal
    rintro image ⟨source, hsource, rfl⟩
    rw [relatorSet_cons] at hsource
    rcases hsource with hsource | hsource
    · obtain rfl := Set.mem_singleton_iff.mp hsource
      exact Subgroup.subset_normalClosure (Set.mem_singleton _)
    · have hkernel : source ∈ MonoidHom.ker presentation := by
        rw [← hbase]
        exact Subgroup.subset_normalClosure hsource
      rw [MonoidHom.mem_ker.mp hkernel]
      exact Subgroup.one_mem _
  · apply Subgroup.normalClosure_le_normal
    intro image himage
    obtain rfl := Set.mem_singleton_iff.mp himage
    exact Subgroup.subset_normalClosure
      ⟨FreeGroup.mk extra, by
        rw [relatorSet_cons]
        exact Or.inl (Set.mem_singleton _), rfl⟩

end Submission.Helpers
