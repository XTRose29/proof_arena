import Submission.AffinePresentation

namespace Submission.AffineCertificate

open Submission.Helpers
open Submission.AffineGraph
open Submission.AffinePermutations
open Submission.AffinePresentation

noncomputable section

private local instance : Fintype Turing.PartrecToTM2.K' where
  elems :=
    { Turing.PartrecToTM2.K'.main, Turing.PartrecToTM2.K'.rev,
      Turing.PartrecToTM2.K'.aux, Turing.PartrecToTM2.K'.stack }
  complete value := by
    cases value <;> simp

def moveWord (move : Move) : Word GeneratorCount :=
  [(generatorIndex (.action (.move move)), true)]

def acceptedLampWord : Word GeneratorCount :=
  FreeGroup.toWord (lampFree AffinePermutations.acceptedVertex)

def subgroupGeneratorWords : Finset (Word GeneratorCount) :=
  insert acceptedLampWord (Finset.univ.image moveWord)

@[simp]
theorem mk_moveWord (move : Move) :
    FreeGroup.mk (moveWord move) = moveFree move := by
  rfl

@[simp]
theorem mk_acceptedLampWord :
    FreeGroup.mk acceptedLampWord =
      lampFree AffinePermutations.acceptedVertex :=
  FreeGroup.mk_toWord

theorem subgroupGenerator_image :
    PresentedGroup.mk relators ∘ FreeGroup.mk ''
        (subgroupGeneratorWords : Set (Word GeneratorCount)) =
      membershipGeneratorSet := by
  ext element
  constructor
  · rintro ⟨word, wordMember, rfl⟩
    change word ∈ subgroupGeneratorWords at wordMember
    rcases Finset.mem_insert.mp wordMember with wordEqual | moveMember
    · subst word
      exact Or.inr <| by
        simp [lampElement, interpret]
    · obtain ⟨move, _, rfl⟩ := Finset.mem_image.mp moveMember
      exact Or.inl ⟨move, rfl⟩
  · rintro (moveMember | lampMember)
    · obtain ⟨move, rfl⟩ := moveMember
      refine ⟨moveWord move, ?_, ?_⟩
      · change
          moveWord move ∈
            insert acceptedLampWord (Finset.univ.image moveWord)
        exact Finset.mem_insert_of_mem <|
          Finset.mem_image.mpr ⟨move, Finset.mem_univ _, rfl⟩
      · change
          PresentedGroup.mk relators (FreeGroup.mk (moveWord move)) =
            moveElement move
        rw [mk_moveWord]
        rfl
    · simp only [Set.mem_singleton_iff] at lampMember
      subst element
      refine ⟨acceptedLampWord, ?_, ?_⟩
      · change
          acceptedLampWord ∈
            insert acceptedLampWord (Finset.univ.image moveWord)
        exact Finset.mem_insert_self _ _
      simp [lampElement, interpret]

theorem certificateSubgroup_eq :
    Subgroup.closure
        (PresentedGroup.mk relators ∘ FreeGroup.mk ''
          (subgroupGeneratorWords : Set (Word GeneratorCount))) =
      membershipSubgroup := by
  rw [subgroupGenerator_image]
  rfl

/-! ## The effective input lamp -/

abbrev TapeSymbol := Turing.PartrecToTM2.Γ'

def compiledSymbol (symbol : TapeSymbol) : Symbol :=
  (false, Function.update (fun _ => none)
    Turing.PartrecToTM2.K'.main (some symbol))

def inputHead : Symbol :=
  (true, Function.update (fun _ => none)
    Turing.PartrecToTM2.K'.main (some Turing.PartrecToTM2.Γ'.cons))

def binaryRight (value : ℕ) : List Symbol :=
  (Turing.PartrecToTM2.trNat value).reverse.map compiledSymbol

def inputRight (code : Nat.Partrec.Code) : List Symbol :=
  binaryRight (Encodable.encode code)

theorem universalTM0Input_eq (code : Nat.Partrec.Code) :
    Submission.UniversalMachine.universalTM0Input code =
      inputHead :: inputRight code := by
  simp [Submission.UniversalMachine.universalTM0Input,
    Submission.UniversalMachine.codeInput, Turing.TM2to1.trInit,
    Turing.PartrecToTM2.trList, inputHead, inputRight, binaryRight,
    compiledSymbol, List.map_reverse]

def radixNat : ℕ :=
  Fintype.card Symbol + 1

def digitNat (symbol : Symbol) : ℕ :=
  (symbolEquiv symbol).val + 1

def stackCodeNat : List Symbol → ℕ
  | [] => 0
  | symbol :: rest =>
      digitNat symbol + radixNat * stackCodeNat rest

theorem stackCodeNat_cast (stack : List Symbol) :
    (stackCodeNat stack : ℤ) = AffineGraph.stackCode stack := by
  induction stack with
  | nil => rfl
  | cons symbol rest ih =>
      simp only [stackCodeNat, AffineGraph.stackCode, Nat.cast_add,
        Nat.cast_mul, digitNat, radixNat, digitInt, radixInt, ih,
        Nat.cast_one]

private theorem stackCodeNat_append_singleton
    (stack : List Symbol) (symbol : Symbol) :
    stackCodeNat (stack ++ [symbol]) =
      stackCodeNat stack +
        radixNat ^ stack.length * digitNat symbol := by
  induction stack with
  | nil => simp [stackCodeNat]
  | cons head tail ih =>
      simp [stackCodeNat, ih, pow_succ]
      ring

private def bitSymbol (bit : Bool) : TapeSymbol :=
  if bit then .bit1 else .bit0

private def binaryStep (value : ℕ) (prior : ℕ × ℕ) : ℕ × ℕ :=
  (prior.1 +
      prior.2 * digitNat (compiledSymbol (bitSymbol value.bodd)),
    prior.2 * radixNat)

def binaryData : ℕ → ℕ × ℕ
  | 0 => (0, 1)
  | value + 1 =>
      binaryStep (value + 1) (binaryData (value + 1).div2)
termination_by value => value
decreasing_by
  simp only [Nat.div2_val]
  omega

private theorem trNum_bit
    (bit : Bool) (value : Num)
    (nonzero : Num.bit bit value ≠ 0) :
    Turing.PartrecToTM2.trNum (Num.bit bit value) =
      bitSymbol bit :: Turing.PartrecToTM2.trNum value := by
  cases bit <;> cases value <;>
    simp [Num.bit, Num.bit0, Num.bit1,
      Turing.PartrecToTM2.trNum, Turing.PartrecToTM2.trPosNum,
      bitSymbol] at nonzero ⊢

private theorem trNat_eq_cons (value : ℕ) (nonzero : value ≠ 0) :
    Turing.PartrecToTM2.trNat value =
      bitSymbol value.bodd ::
        Turing.PartrecToTM2.trNat value.div2 := by
  unfold Turing.PartrecToTM2.trNat
  have decomposition :
      Num.ofNat' value =
        Num.bit value.bodd (Num.ofNat' value.div2) := by
    calc
      Num.ofNat' value =
          Num.ofNat' (Nat.bit value.bodd value.div2) :=
        congrArg Num.ofNat' (Nat.bit_bodd_div2 value).symm
      _ = Num.bit value.bodd (Num.ofNat' value.div2) := by
        rw [Num.ofNat'_bit]
        cases value.bodd <;> rfl
  change
    Turing.PartrecToTM2.trNum (Num.ofNat' value) =
      bitSymbol value.bodd ::
        Turing.PartrecToTM2.trNum (Num.ofNat' value.div2)
  rw [decomposition]
  apply trNum_bit
  rw [← decomposition]
  simpa using nonzero

private theorem binaryRight_eq_append
    (value : ℕ) (nonzero : value ≠ 0) :
    binaryRight value =
      binaryRight value.div2 ++
        [compiledSymbol (bitSymbol value.bodd)] := by
  simp only [binaryRight, trNat_eq_cons value nonzero,
    List.reverse_cons, List.map_append, List.map_singleton]

theorem binaryData_spec (value : ℕ) :
    binaryData value =
      (stackCodeNat (binaryRight value),
        radixNat ^ (binaryRight value).length) := by
  induction value using Nat.strong_induction_on with
  | h value ih =>
      cases value with
      | zero =>
        simp [binaryData, binaryRight, stackCodeNat]
      | succ value =>
        have smaller : (value + 1).div2 < value + 1 := by
          simp only [Nat.div2_val]
          exact Nat.div_lt_self (Nat.succ_pos _) (by decide)
        have prior := ih (value + 1).div2 smaller
        rw [binaryData,
          binaryRight_eq_append (value + 1) (Nat.succ_ne_zero _),
          stackCodeNat_append_singleton, prior]
        simp [binaryStep, pow_succ]

private theorem binaryStep_primrec :
    Primrec₂ binaryStep := by
  apply Primrec₂.mk
  have value :
      Primrec (fun input : ℕ × (ℕ × ℕ) => input.1) :=
    Primrec.fst
  have priorFirst :
      Primrec (fun input : ℕ × (ℕ × ℕ) => input.2.1) :=
    Primrec.fst.comp Primrec.snd
  have priorSecond :
      Primrec (fun input : ℕ × (ℕ × ℕ) => input.2.2) :=
    Primrec.snd.comp Primrec.snd
  have digit :
      Primrec (fun input : ℕ × (ℕ × ℕ) =>
        digitNat (compiledSymbol (bitSymbol input.1.bodd))) :=
    (Primrec.cond (Primrec.nat_bodd.comp value)
      (Primrec.const
        (digitNat (compiledSymbol (bitSymbol true))))
      (Primrec.const
        (digitNat (compiledSymbol (bitSymbol false))))).of_eq <| by
          intro input
          cases input.1.bodd <;> simp [bitSymbol]
  exact
    (Primrec.nat_add.comp priorFirst
      (Primrec.nat_mul.comp priorSecond digit)).pair
        (Primrec.nat_mul.comp priorSecond (Primrec.const radixNat))

private def binaryHistoryStep
    (_ : Unit) (history : List (ℕ × ℕ)) : Option (ℕ × ℕ) :=
  history.length.casesOn (some (0, 1)) fun previous =>
    (history[(previous + 1).div2]?).map
      (binaryStep (previous + 1))

private theorem binaryHistoryStep_primrec :
    Primrec₂ binaryHistoryStep := by
  apply Primrec₂.mk
  apply Primrec.nat_casesOn
    (Primrec.list_length.comp Primrec.snd)
    (Primrec.const (some (0, 1)))
  apply Primrec₂.mk
  have actual :
      Primrec (fun input : (Unit × List (ℕ × ℕ)) × ℕ =>
        input.2 + 1) :=
    Primrec.succ.comp Primrec.snd
  have prior :
      Primrec (fun input : (Unit × List (ℕ × ℕ)) × ℕ =>
        input.1.2[(input.2 + 1).div2]?) :=
    Primrec.list_getElem?.comp
      (Primrec.snd.comp Primrec.fst)
      (Primrec.nat_div2.comp actual)
  exact Primrec.option_map prior <|
    binaryStep_primrec.comp₂
      (actual.comp Primrec.fst).to₂ Primrec₂.right

theorem binaryData_computable : Computable binaryData := by
  have recursive :=
    Computable.nat_strong_rec
      (fun (_ : Unit) value => binaryData value)
      binaryHistoryStep_primrec.to_comp
      (fun _ value => by
        cases value with
        | zero => simp [binaryHistoryStep, binaryData]
        | succ value =>
            have indexLt : (value + 1).div2 < value + 1 := by
              simp only [Nat.div2_val]
              exact Nat.div_lt_self (Nat.succ_pos _) (by decide)
            simp only [binaryHistoryStep, List.length_map,
              List.length_range, List.getElem?_map]
            rw [List.getElem?_range indexLt]
            simp [binaryData])
  exact recursive.comp (Computable.const ()) Computable.id

theorem binaryData_inputRight (code : Nat.Partrec.Code) :
    (binaryData (Encodable.encode code)).1 =
      stackCodeNat (inputRight code) := by
  simpa [inputRight] using congrArg Prod.fst
    (binaryData_spec (Encodable.encode code))

def inputControl : Control :=
  (encodeState
    (AffineGraph.initialState Nat.Partrec.Code.zero)).1

def inputLocation : LayerControl :=
  (false, inputControl)

def inputCoordinate (code : Nat.Partrec.Code) : Coord :=
  coord 0 (binaryData (Encodable.encode code)).1 0 0

theorem initialVertex_eq (code : Nat.Partrec.Code) :
    AffinePermutations.initialVertex code =
      (false, inputControl, inputCoordinate code) := by
  have codeInput :
      Submission.UniversalMachine.universalTM0Input code =
        inputHead :: inputRight code :=
    universalTM0Input_eq code
  have zeroInput :
      Submission.UniversalMachine.universalTM0Input Nat.Partrec.Code.zero =
        inputHead :: inputRight Nat.Partrec.Code.zero :=
    universalTM0Input_eq Nat.Partrec.Code.zero
  rw [AffinePermutations.initialVertex]
  simp [AffineGraph.initialState, Submission.FiniteConfiguration.initial,
    encodeState, inputControl, codeInput, zeroInput, inputCoordinate,
    ← stackCodeNat_cast, ← binaryData_inputRight]

def translationGenerator : Fin GeneratorCount :=
  generatorIndex (.action (.global inputLocation 1))

def inputLampGenerator : Fin GeneratorCount :=
  generatorIndex (.lamp inputLocation)

def translationWord (code : Nat.Partrec.Code) : Word GeneratorCount :=
  List.replicate (binaryData (Encodable.encode code)).1
    (translationGenerator, true)

def inputLampWord (code : Nat.Partrec.Code) : Word GeneratorCount :=
  translationWord code ++ [(inputLampGenerator, true)] ++
    FreeGroup.invRev (translationWord code)

private theorem replicateLetter_primrec
    (letter : Fin GeneratorCount × Bool) :
    Primrec (fun power : ℕ => List.replicate power letter) := by
  apply (Primrec.nat_rec₁ ([] : List (Fin GeneratorCount × Bool))
    (Primrec.list_cons.comp₂
      (Primrec₂.const letter) Primrec₂.right)).of_eq
  intro power
  induction power with
  | zero => rfl
  | succ power ih =>
      simp [ih, List.replicate_succ]

theorem translationWord_computable :
    Computable translationWord := by
  have power :
      Computable (fun code : Nat.Partrec.Code =>
        (binaryData (Encodable.encode code)).1) :=
    Computable.fst.comp <|
      binaryData_computable.comp Computable.encode
  exact
    (replicateLetter_primrec (translationGenerator, true)).to_comp.comp power

theorem inputLampWord_computable :
    Computable inputLampWord := by
  exact
    Computable.list_append.comp
      (Computable.list_append.comp translationWord_computable
        (Computable.const [(inputLampGenerator, true)]))
      (Submission.SubgroupReduction.invRev_computable.comp
        translationWord_computable)

theorem mk_translationWord (code : Nat.Partrec.Code) :
    FreeGroup.mk (translationWord code) =
      freeGenerator (.action (.global inputLocation 1)) ^
        (binaryData (Encodable.encode code)).1 := by
  change
    FreeGroup.mk
        (List.replicate (binaryData (Encodable.encode code)).1
          (generatorIndex (.action (.global inputLocation 1)), true)) =
      FreeGroup.mk
          [(generatorIndex (.action (.global inputLocation 1)), true)] ^
        (binaryData (Encodable.encode code)).1
  rw [FreeGroup.pow_mk, List.flatten_replicate_singleton]

theorem mk_inputLampWord (code : Nat.Partrec.Code) :
    FreeGroup.mk (inputLampWord code) =
      lampFree (AffinePermutations.initialVertex code) := by
  rw [inputLampWord, ← FreeGroup.mul_mk, ← FreeGroup.mul_mk,
    ← FreeGroup.inv_mk, mk_translationWord, initialVertex_eq]
  simp [lampFree, globalFree, inputLampGenerator, inputLocation,
    inputCoordinate, freeGenerator, FreeGroup.of, coord, zpow_natCast]

def certificate :
    Submission.SubgroupReduction.SubgroupMembershipCertificate where
  n := GeneratorCount
  baseRels := relators
  baseRels_finite := relators_finite
  subgroupGenerators := subgroupGeneratorWords
  encode := inputLampWord
  encode_computable := inputLampWord_computable
  encode_spec code := by
    rw [mk_inputLampWord, certificateSubgroup_eq]
    change
      (Nat.Partrec.Code.eval code 0).Dom ↔
        lampElement (AffinePermutations.initialVertex code) ∈
          membershipSubgroup
    exact
      (AffinePermutations.halting_iff_connected code).trans
        (lamp_mem_iff_connected
          (AffinePermutations.initialVertex code)).symm

end

end Submission.AffineCertificate
