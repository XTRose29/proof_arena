import ChallengeDeps

namespace Submission.Helpers

abbrev Letter (n : ℕ) := Fin n × Bool

abbrev Word (n : ℕ) := List (Letter n)

/-- A relator, a conjugating word, and a sign. -/
abbrev Step (n : ℕ) := Word n × (Word n × Bool)

abbrev Certificate (n : ℕ) := List (Step n)

def flipLetter {n : ℕ} (x : Letter n) : Letter n :=
  (x.1, !x.2)

def signedRelator {n : ℕ} (r : Word n) (positive : Bool) : Word n :=
  if positive then r else FreeGroup.invRev r

def stepWord {n : ℕ} (s : Step n) : Word n :=
  s.2.1 ++ signedRelator s.1 s.2.2 ++ FreeGroup.invRev s.2.1

def certificateWord {n : ℕ} (c : Certificate n) : Word n :=
  c.foldr (fun s w => stepWord s ++ w) []

def cancels {n : ℕ} (x y : Letter n) : Bool :=
  decide (x.1 = y.1 ∧ x.2 = !y.2)

def reduceStep {n : ℕ} (x : Letter n) : Word n → Word n
  | [] => [x]
  | y :: ys => bif cancels x y then ys else x :: y :: ys

def normalize {n : ℕ} (w : Word n) : Word n :=
  w.foldr reduceStep []

theorem normalize_eq_reduce {n : ℕ} (w : Word n) :
    normalize w = FreeGroup.reduce w := by
  induction w with
  | nil => rfl
  | cons x w ih =>
      rw [show normalize (x :: w) = reduceStep x (normalize w) from rfl,
        FreeGroup.reduce.cons, ih]
      cases FreeGroup.reduce w with
      | nil => rfl
      | cons y ys => simp only [reduceStep, cancels, Bool.cond_decide]

theorem primrec_flipLetter {n : ℕ} : Primrec (@flipLetter n) :=
  Primrec.dom_finite _

theorem primrec_invRev {n : ℕ} : Primrec (@FreeGroup.invRev (Fin n)) := by
  unfold FreeGroup.invRev
  exact Primrec.list_reverse.comp
    (Primrec.list_map Primrec.id (primrec_flipLetter.comp Primrec.snd).to₂)

theorem primrec_signedRelator {n : ℕ} : Primrec₂ (@signedRelator n) := by
  apply Primrec₂.mk
  exact (Primrec.cond Primrec.snd Primrec.fst
    (primrec_invRev.comp Primrec.fst)).of_eq fun p => by
      cases p.2 <;> rfl

theorem primrec_stepWord {n : ℕ} : Primrec (@stepWord n) := by
  let rel : Primrec fun s : Step n => s.1 := Primrec.fst
  let conjugator : Primrec fun s : Step n => s.2.1 := Primrec.fst.comp Primrec.snd
  let positive : Primrec fun s : Step n => s.2.2 := Primrec.snd.comp Primrec.snd
  exact Primrec.list_append.comp
    (Primrec.list_append.comp conjugator
      (primrec_signedRelator.comp rel positive))
    (primrec_invRev.comp conjugator)

theorem primrec_reduceStep {n : ℕ} : Primrec₂ (@reduceStep n) := by
  apply Primrec₂.mk
  let singletonHead : Primrec fun p : Letter n × Word n => [p.1] :=
    Primrec.list_cons.comp Primrec.fst (Primrec.const [])
  let cancel : Primrec fun p : (Letter n × Word n) × (Letter n × Word n) =>
      cancels p.1.1 p.2.1 :=
    (Primrec.dom_finite fun p : Letter n × Letter n => cancels p.1 p.2).comp
      (Primrec.pair (Primrec.fst.comp Primrec.fst) (Primrec.fst.comp Primrec.snd))
  let keepTail : Primrec fun p : (Letter n × Word n) × (Letter n × Word n) => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  let keepBoth : Primrec fun p : (Letter n × Word n) × (Letter n × Word n) =>
      p.1.1 :: p.2.1 :: p.2.2 :=
    Primrec.list_cons.comp (Primrec.fst.comp Primrec.fst)
      (Primrec.list_cons.comp (Primrec.fst.comp Primrec.snd) (Primrec.snd.comp Primrec.snd))
  exact (Primrec.list_casesOn Primrec.snd singletonHead
    (Primrec.cond cancel keepTail keepBoth).to₂).of_eq fun p => by
      cases p.2 <;> rfl

theorem primrec_normalize {n : ℕ} : Primrec (@normalize n) := by
  unfold normalize
  exact Primrec.list_foldr Primrec.id (Primrec.const [])
    (primrec_reduceStep.comp₂
      (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.snd.comp₂ Primrec₂.right))

theorem primrec_certificateWord {n : ℕ} : Primrec (@certificateWord n) := by
  unfold certificateWord
  exact Primrec.list_foldr Primrec.id (Primrec.const [])
    (Primrec.list_append.comp
      (primrec_stepWord.comp (Primrec.fst.comp Primrec.snd))
      (Primrec.snd.comp Primrec.snd)).to₂

def Certifies {n : ℕ} (rels : List (Word n)) (target : Word n)
    (certificate : Certificate n) : Prop :=
  (∀ s ∈ certificate, s.1 ∈ rels) ∧
    normalize (certificateWord certificate) = normalize target

abbrev CertifiesInput (n : ℕ) :=
  List (Word n) × (Word n × Certificate n)

theorem primrecPred_certifiesInput {n : ℕ} :
    PrimrecPred fun p : CertifiesInput n => Certifies p.1 p.2.1 p.2.2 := by
  have hmem : PrimrecRel fun (rels : List (Word n)) (w : Word n) => w ∈ rels :=
    (Primrec.eq.exists_mem_list).of_eq fun rels w => by simp
  have hstep : PrimrecRel fun (s : Step n) (p : CertifiesInput n) => s.1 ∈ p.1 :=
    hmem.comp₂ (Primrec.fst.comp₂ Primrec₂.right)
      (Primrec.fst.comp₂ Primrec₂.left)
  have hvalid : PrimrecPred fun p : CertifiesInput n => ∀ s ∈ p.2.2, s.1 ∈ p.1 :=
    hstep.forall_mem_list.comp (Primrec.snd.comp Primrec.snd) Primrec.id
  have heq : PrimrecPred fun p : CertifiesInput n =>
      normalize (certificateWord p.2.2) = normalize p.2.1 :=
    Primrec.eq.comp
      (primrec_normalize.comp
        (primrec_certificateWord.comp (Primrec.snd.comp Primrec.snd)))
      (primrec_normalize.comp (Primrec.fst.comp Primrec.snd))
  exact hvalid.and heq

def wordSet {n : ℕ} (rels : List (Word n)) : Set (FreeGroup (Fin n)) :=
  {x | ∃ w ∈ rels, FreeGroup.mk w = x}

theorem certificateWord_append {n : ℕ} (c d : Certificate n) :
    certificateWord (c ++ d) = certificateWord c ++ certificateWord d := by
  induction c with
  | nil => rfl
  | cons s c ih =>
      change stepWord s ++ certificateWord (c ++ d) =
        (stepWord s ++ certificateWord c) ++ certificateWord d
      rw [ih, List.append_assoc]

theorem mk_stepWord {n : ℕ} (s : Step n) :
    FreeGroup.mk (stepWord s) =
      FreeGroup.mk s.2.1 *
        (if s.2.2 then FreeGroup.mk s.1 else (FreeGroup.mk s.1)⁻¹) *
          (FreeGroup.mk s.2.1)⁻¹ := by
  rcases s with ⟨r, c, positive⟩
  cases positive <;>
    simp [stepWord, signedRelator, ← FreeGroup.mul_mk, FreeGroup.inv_mk, mul_assoc]

theorem certifies_mem_normalClosure {n : ℕ} {rels : List (Word n)}
    {target : Word n} {certificate : Certificate n}
    (h : Certifies rels target certificate) :
    FreeGroup.mk target ∈ Subgroup.normalClosure (wordSet rels) := by
  rcases h with ⟨hvalid, heq⟩
  have certificate_mem : ∀ c : Certificate n, (∀ s ∈ c, s.1 ∈ rels) →
      FreeGroup.mk (certificateWord c) ∈ Subgroup.normalClosure (wordSet rels) := by
    intro c hc
    induction c with
    | nil => exact Subgroup.one_mem _
    | cons s c ih =>
        have hsrel : s.1 ∈ rels := hc s (by simp)
        have hvalidTail : ∀ t ∈ c, t.1 ∈ rels := by
          intro t ht
          exact hc t (by simp [ht])
        have hr : FreeGroup.mk s.1 ∈ Subgroup.normalClosure (wordSet rels) :=
          Subgroup.subset_normalClosure ⟨s.1, hsrel, rfl⟩
        have hsigned :
            (if s.2.2 then FreeGroup.mk s.1 else (FreeGroup.mk s.1)⁻¹) ∈
              Subgroup.normalClosure (wordSet rels) := by
          cases hb : s.2.2 with
          | false => simpa [hb] using Subgroup.inv_mem _ hr
          | true => simpa [hb] using hr
        have hstep : FreeGroup.mk (stepWord s) ∈ Subgroup.normalClosure (wordSet rels) := by
          rw [mk_stepWord]
          exact (inferInstance : (Subgroup.normalClosure (wordSet rels)).Normal).conj_mem
            _ hsigned _
        rw [show certificateWord (s :: c) =
          stepWord s ++ certificateWord c from rfl, ← FreeGroup.mul_mk]
        exact Subgroup.mul_mem _ hstep (ih hvalidTail)
  have hcertificate := certificate_mem certificate hvalid
  have hmk : FreeGroup.mk (certificateWord certificate) = FreeGroup.mk target :=
    FreeGroup.reduce.exact (by simpa only [normalize_eq_reduce] using heq)
  rw [← hmk]
  exact hcertificate

theorem mem_normalClosure_exists_certificate {n : ℕ} {rels : List (Word n)}
    {x : FreeGroup (Fin n)} (hx : x ∈ Subgroup.normalClosure (wordSet rels)) :
    ∃ certificate : Certificate n,
      (∀ s ∈ certificate, s.1 ∈ rels) ∧ FreeGroup.mk (certificateWord certificate) = x := by
  refine Subgroup.closure_induction''
    (p := fun x _ => ∃ certificate : Certificate n,
      (∀ s ∈ certificate, s.1 ∈ rels) ∧ FreeGroup.mk (certificateWord certificate) = x)
    ?_ ?_ ?_ ?_ hx
  · intro x hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨a, ha, hax⟩
    rcases ha with ⟨r, hr, rfl⟩
    rcases isConj_iff.mp hax with ⟨c, hc⟩
    refine ⟨[(r, (FreeGroup.toWord c, true))], ?_, ?_⟩
    · simpa using hr
    · rw [show certificateWord [(r, (FreeGroup.toWord c, true))] =
        stepWord (r, (FreeGroup.toWord c, true)) by
          simp [certificateWord], mk_stepWord]
      simpa only [if_true, FreeGroup.mk_toWord] using hc
  · intro x hx
    rcases Group.mem_conjugatesOfSet_iff.mp hx with ⟨a, ha, hax⟩
    rcases ha with ⟨r, hr, rfl⟩
    rcases isConj_iff.mp hax with ⟨c, hc⟩
    refine ⟨[(r, (FreeGroup.toWord c, false))], ?_, ?_⟩
    · simpa using hr
    · have hinv := congrArg Inv.inv hc
      rw [show certificateWord [(r, (FreeGroup.toWord c, false))] =
        stepWord (r, (FreeGroup.toWord c, false)) by
          simp [certificateWord], mk_stepWord]
      simpa [FreeGroup.mk_toWord, mul_assoc] using hinv
  · exact ⟨[], by simp, rfl⟩
  · rintro x y _ _ ⟨cx, hcx, ecx⟩ ⟨cy, hcy, ecy⟩
    refine ⟨cx ++ cy, ?_, ?_⟩
    · intro s hs
      rcases List.mem_append.mp hs with hs | hs
      · exact hcx s hs
      · exact hcy s hs
    · rw [certificateWord_append, ← FreeGroup.mul_mk, ecx, ecy]

theorem mem_normalClosure_iff_exists_certificate {n : ℕ} {rels : List (Word n)}
    {target : Word n} :
    FreeGroup.mk target ∈ Subgroup.normalClosure (wordSet rels) ↔
      ∃ certificate : Certificate n, Certifies rels target certificate := by
  constructor
  · intro htarget
    obtain ⟨certificate, hvalid, heq⟩ :=
      mem_normalClosure_exists_certificate htarget
    refine ⟨certificate, hvalid, ?_⟩
    simpa only [normalize_eq_reduce] using FreeGroup.reduce.sound heq
  · rintro ⟨certificate, hcertificate⟩
    exact certifies_mem_normalClosure hcertificate

abbrev DecisionCertificate (n : ℕ) :=
  Certificate n ⊕ (Fin n → Certificate n)

def NegativeCertifies {n : ℕ} (rels : List (Word n)) (target : Word n)
    (certificates : Fin n → Certificate n) : Prop :=
  ∀ i, Certifies (rels ++ [target]) [(i, true)] (certificates i)

def DecisionCertifies {n : ℕ} (rels : List (Word n)) (target : Word n) :
    DecisionCertificate n → Prop
  | Sum.inl certificate => Certifies rels target certificate
  | Sum.inr certificates => NegativeCertifies rels target certificates

theorem primrecRel_certifies {n : ℕ} (rels : List (Word n)) :
    PrimrecRel fun target certificate => Certifies rels target certificate := by
  exact (primrecPred_certifiesInput.comp
    (Primrec.pair (Primrec.const rels) (Primrec.pair Primrec.fst Primrec.snd))).primrecRel

abbrev NegativeInput (n : ℕ) := Word n × (Fin n → Certificate n)

theorem primrecPred_negativeInput {n : ℕ} (rels : List (Word n)) :
    PrimrecPred fun p : NegativeInput n => NegativeCertifies rels p.1 p.2 := by
  let target : Primrec fun p : Fin n × NegativeInput n => p.2.1 :=
    Primrec.fst.comp Primrec.snd
  let certificates : Primrec fun p : Fin n × NegativeInput n => p.2.2 :=
    Primrec.snd.comp Primrec.snd
  let certificate : Primrec fun p : Fin n × NegativeInput n => p.2.2 p.1 :=
    Primrec.fin_app.comp certificates Primrec.fst
  let generator : Primrec fun p : Fin n × NegativeInput n => [(p.1, true)] :=
    Primrec.list_cons.comp (Primrec.pair Primrec.fst (Primrec.const true))
      (Primrec.const [])
  let extendedRelators : Primrec fun p : Fin n × NegativeInput n =>
      rels ++ [p.2.1] :=
    Primrec.list_append.comp (Primrec.const rels)
      (Primrec.list_cons.comp target (Primrec.const []))
  have hindex : PrimrecRel fun (i : Fin n) (p : NegativeInput n) =>
      Certifies (rels ++ [p.1]) [(i, true)] (p.2 i) :=
    (primrecPred_certifiesInput.comp
      (Primrec.pair extendedRelators (Primrec.pair generator certificate))).primrecRel
  have hall := hindex.forall_mem_list.comp
    (Primrec.const (Finset.univ.toList : List (Fin n))) Primrec.id
  exact hall.of_eq fun p => by simp [NegativeCertifies]

theorem primrecRel_decisionCertifies {n : ℕ} (rels : List (Word n)) :
    PrimrecRel (DecisionCertifies rels) := by
  classical
  have hpositive := primrecRel_certifies rels
  have hnegative := (primrecPred_negativeInput rels).primrecRel
  apply Primrec₂.primrecRel
  exact (Primrec.sumCasesOn Primrec.snd
    (hpositive.decide.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)
    (hnegative.decide.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).to₂.of_eq
      fun target certificate => by cases certificate <;> rfl

@[implicit_reducible]
def decisionCertificatePrimcodable (n : ℕ) : Primcodable (DecisionCertificate n) :=
  inferInstance

def decodeDecisionCertificate {n : ℕ} (code : ℕ) : Option (DecisionCertificate n) :=
  @Encodable.decode (DecisionCertificate n)
    (decisionCertificatePrimcodable n).toEncodable code

def encodeDecisionCertificate {n : ℕ} (certificate : DecisionCertificate n) : ℕ :=
  @Encodable.encode (DecisionCertificate n)
    (decisionCertificatePrimcodable n).toEncodable certificate

@[simp]
theorem decodeDecisionCertificate_encode {n : ℕ} (certificate : DecisionCertificate n) :
    decodeDecisionCertificate (encodeDecisionCertificate certificate) = some certificate :=
  @Encodable.encodek (DecisionCertificate n)
    (decisionCertificatePrimcodable n).toEncodable certificate

theorem primrec_decodeDecisionCertificate {n : ℕ} :
    Primrec (@decodeDecisionCertificate n) := by
  unfold decodeDecisionCertificate
  exact @Primrec.decode (DecisionCertificate n)
    (decisionCertificatePrimcodable n)

def EncodedDecisionCertifies {n : ℕ} (rels : List (Word n))
    (target : Word n) (code : ℕ) : Prop :=
  match decodeDecisionCertificate code with
  | none => False
  | some certificate => DecisionCertifies rels target certificate

theorem primrecRel_encodedDecisionCertifies {n : ℕ} (rels : List (Word n)) :
    PrimrecRel (EncodedDecisionCertifies rels) := by
  classical
  have hdecision := primrecRel_decisionCertifies rels
  let check (target : Word n) (code : ℕ) : Bool :=
    Option.casesOn (decodeDecisionCertificate code) false
      fun certificate => decide (DecisionCertifies rels target certificate)
  have hcheck : Primrec₂ check :=
    (Primrec.option_casesOn (primrec_decodeDecisionCertificate.comp Primrec.snd)
    (Primrec.const false)
    (hdecision.decide.comp₂ (Primrec.fst.comp₂ Primrec₂.left) Primrec₂.right)).to₂.of_eq
      fun target code => by
        simp only [check]
  have hrel : PrimrecRel fun target code => check target code = true :=
    Primrec.eq.comp₂ hcheck (Primrec₂.const true)
  exact hrel.of_eq fun target code => by
    simp only [check, EncodedDecisionCertifies]
    cases decodeDecisionCertificate code <;> simp

def codeIsPositive {n : ℕ} (code : ℕ) : Bool :=
  Option.casesOn (@decodeDecisionCertificate n code) false
    (fun certificate : DecisionCertificate n =>
      Sum.casesOn certificate (fun _ => true) (fun _ => false))

theorem primrec_codeIsPositive {n : ℕ} : Primrec (@codeIsPositive n) := by
  have hsum : Primrec fun certificate : DecisionCertificate n =>
      match certificate with
      | Sum.inl _ => true
      | Sum.inr _ => false :=
    (Primrec.sumCasesOn Primrec.id (Primrec.const true).to₂
      (Primrec.const false).to₂).of_eq fun certificate => by
        cases certificate <;> rfl
  exact (Primrec.option_casesOn primrec_decodeDecisionCertificate (Primrec.const false)
    (hsum.comp Primrec.snd).to₂).of_eq fun code => by
      cases h : @decodeDecisionCertificate n code with
      | none => simp [codeIsPositive, h]
      | some certificate =>
          cases certificate <;> simp [codeIsPositive, h]

theorem exists_negativeCertifies_iff {n : ℕ} {rels : List (Word n)}
    {target : Word n} :
    (∃ certificates, NegativeCertifies rels target certificates) ↔
      Subgroup.normalClosure (wordSet (rels ++ [target])) = ⊤ := by
  constructor
  · rintro ⟨certificates, hcertificates⟩
    apply le_antisymm le_top
    intro x _
    refine FreeGroup.induction_on x (Subgroup.one_mem _) ?_ ?_ ?_
    · intro i
      exact mem_normalClosure_iff_exists_certificate.mpr
        ⟨certificates i, hcertificates i⟩
    · intro i hi
      exact Subgroup.inv_mem _ hi
    · intro a b ha hb
      exact Subgroup.mul_mem _ ha hb
  · intro htop
    classical
    have hexists (i : Fin n) :
        ∃ certificate, Certifies (rels ++ [target]) [(i, true)] certificate :=
      mem_normalClosure_iff_exists_certificate.mp (by rw [htop]; trivial)
    exact ⟨fun i => (hexists i).choose, fun i => (hexists i).choose_spec⟩

end Submission.Helpers
