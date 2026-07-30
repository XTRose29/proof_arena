import Submission.FourierIdentity

namespace Submission.Helpers

open scoped BigOperators Filter Topology

noncomputable section

lemma exists_strictMono_const_subsequence
    {A : Type} [Finite A] (f : ℕ → A) :
    ∃ a : A, ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ n, f (φ n) = a := by
  classical
  obtain ⟨a, ha⟩ := Finite.exists_infinite_fiber f
  have hs' : (f ⁻¹' {a}).Infinite := Set.infinite_coe_iff.mp ha
  have heq : f ⁻¹' {a} = {n : ℕ | f n = a} := by ext; simp
  have hs : ({n : ℕ | f n = a} : Set ℕ).Infinite := by
    simpa [heq] using hs'
  refine ⟨a, Nat.nth (fun n => f n = a), Nat.nth_strictMono hs, ?_⟩
  intro n
  exact Nat.nth_mem_of_infinite hs n

def FiniteCommProbWitness.commutatorCard (W : FiniteCommProbWitness) : ℕ :=
  letI := W.group
  Nat.card (commutator W.carrier)

def FiniteCommProbWitness.commutatorFinEquiv
    (W : FiniteCommProbWitness) (d : ℕ) (hcard : W.commutatorCard = d) :
    letI := W.group
    commutator W.carrier ≃ Fin d := by
  letI := W.group
  letI := W.finite
  letI := Fintype.ofFinite (commutator W.carrier)
  apply Fintype.equivFinOfCardEq
  simpa [FiniteCommProbWitness.commutatorCard, Nat.card_eq_fintype_card] using hcard

def FiniteCommProbWitness.commutatorMulCode
    (W : FiniteCommProbWitness) (d : ℕ) (hcard : W.commutatorCard = d) :
    Fin d → Fin d → Fin d := fun a b =>
  letI := W.group
  let e := W.commutatorFinEquiv d hcard
  e (e.symm a * e.symm b)

def commutatorMulEquivOfCodeEq
    (W V : FiniteCommProbWitness) (d : ℕ)
    (hW : W.commutatorCard = d) (hV : V.commutatorCard = d)
    (hcode : W.commutatorMulCode d hW = V.commutatorMulCode d hV) :
    letI := W.group
    letI := V.group
    commutator W.carrier ≃* commutator V.carrier := by
  letI := W.group
  letI := V.group
  let eW := W.commutatorFinEquiv d hW
  let eV := V.commutatorFinEquiv d hV
  refine {
    toEquiv := eW.trans eV.symm
    map_mul' := ?_ }
  intro x y
  apply eV.injective
  have h := congrFun (congrFun hcode (eW x)) (eW y)
  simpa [FiniteCommProbWitness.commutatorMulCode, eW, eV] using h

lemma exists_fixed_commutator_model_subsequence
    (W : ℕ → FiniteCommProbWitness) (B : ℕ)
    (hbound : ∀ n, (W n).commutatorCard ≤ B) :
    ∃ d : ℕ, ∃ φ : ℕ → ℕ,
      StrictMono φ ∧
      (∀ n, (W (φ n)).commutatorCard = d) ∧
      ∀ n (hn : (W (φ n)).commutatorCard = d)
        (hzero : (W (φ 0)).commutatorCard = d),
        (W (φ n)).commutatorMulCode d hn =
          (W (φ 0)).commutatorMulCode d hzero := by
  classical
  let cardCode : ℕ → Fin (B + 1) := fun n =>
    ⟨(W n).commutatorCard, Nat.lt_succ_of_le (hbound n)⟩
  obtain ⟨a, φ₁, hφ₁, hcardCode⟩ := exists_strictMono_const_subsequence cardCode
  let W₁ : ℕ → FiniteCommProbWitness := fun n => W (φ₁ n)
  have hcard₁ : ∀ n, (W₁ n).commutatorCard = a.val := by
    intro n
    exact congrArg Fin.val (hcardCode n)
  let mulCode : ℕ → (Fin a.val → Fin a.val → Fin a.val) := fun n =>
    (W₁ n).commutatorMulCode a.val (hcard₁ n)
  obtain ⟨c, φ₂, hφ₂, hmulCode⟩ := exists_strictMono_const_subsequence mulCode
  let φ : ℕ → ℕ := fun n => φ₁ (φ₂ n)
  have hφ : StrictMono φ := hφ₁.comp hφ₂
  have hcard : ∀ n, (W (φ n)).commutatorCard = a.val := by
    intro n
    exact hcard₁ (φ₂ n)
  refine ⟨a.val, φ, hφ, hcard, ?_⟩
  intro n hn hzero
  have hn := hmulCode n
  have hzero := hmulCode 0
  simpa [mulCode, W₁, φ] using hn.trans hzero.symm

def fixedCommutatorMulEquiv
    (W : ℕ → FiniteCommProbWitness) (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ) :
    letI := (W n).group
    letI := (W 0).group
    commutator (W n).carrier ≃* commutator (W 0).carrier := by
  exact commutatorMulEquivOfCodeEq (W n) (W 0) d (hcard n) (hcard 0)
    (hcode n (hcard n) (hcard 0))

def unitCharToComplex {D : Type} [Group D] (chi : D →* ℂˣ) :
    AddChar (Additive D) ℂ :=
  AddChar.toMonoidHomEquiv.symm ((Units.coeHom ℂ).comp chi)

@[simp]
lemma unitCharToComplex_apply {D : Type} [Group D] (chi : D →* ℂˣ) (x : D) :
    unitCharToComplex chi (Additive.ofMul x) = (chi x : ℂ) := rfl

def transportedCommutatorCharacter
    (W : ℕ → FiniteCommProbWitness) (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ)
    (chi : letI := (W 0).group; commutator (W 0).carrier →* ℂˣ) :
    letI := (W n).group
    AddChar (Additive (commutator (W n).carrier)) ℂ := by
  letI := (W n).group
  letI := (W 0).group
  exact unitCharToComplex
    (chi.comp (fixedCommutatorMulEquiv W d hcard hcode n).toMonoidHom)

def classTwoCharacterIndex
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ)
    (chi : letI := (W 0).group; commutator (W 0).carrier →* ℂˣ) : ℕ :=
  letI := (W n).group
  letI := (W n).finite
  (commutatorCharMap (W n).carrier (hcentral n)
    (transportedCommutatorCharacter W d hcard hcode n chi)).ker.index

lemma eventually_eq_of_tendsto_withTop_coe
    {f : ℕ → WithTop ℕ} {a : ℕ}
    (hf : Filter.Tendsto f Filter.atTop (𝓝 (a : WithTop ℕ))) :
    ∀ᶠ n in Filter.atTop, f n = a := by
  have hopen : IsOpen (((fun n : ℕ => (n : WithTop ℕ)) '' {a}) : Set (WithTop ℕ)) :=
    WithTop.isOpenEmbedding_coe.isOpenMap _ (isOpen_discrete {a})
  have himage : (fun n : ℕ => (n : WithTop ℕ)) '' {a} =
      ({(a : WithTop ℕ)} : Set (WithTop ℕ)) := by
    ext x
    simp
  have hsingleton : ({(a : WithTop ℕ)} : Set (WithTop ℕ)) ∈
      𝓝 (a : WithTop ℕ) := by
    rw [← himage]
    exact hopen.mem_nhds ⟨a, Set.mem_singleton a, rfl⟩
  exact hf.eventually hsingleton

lemma exists_classTwoCharacterIndex_profile_subsequence
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero) :
    letI := (W 0).group
    letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
    ∃ a : (commutator (W 0).carrier →* ℂˣ) → WithTop ℕ,
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        ∀ chi, Filter.Tendsto
          (fun n => (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : WithTop ℕ))
          Filter.atTop (𝓝 (a chi)) := by
  classical
  letI := (W 0).group
  letI := (W 0).finite
  letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
  letI := Fintype.ofFinite (commutator (W 0).carrier →* ℂˣ)
  let f : ℕ → ((commutator (W 0).carrier →* ℂˣ) → WithTop ℕ) := fun n chi =>
    classTwoCharacterIndex W hcentral d hcard hcode n chi
  obtain ⟨a, _ha, φ, hφ, hfa⟩ :=
    isSeqCompact_univ (x := f) (fun _ => Set.mem_univ _)
  refine ⟨a, φ, hφ, ?_⟩
  intro chi
  exact tendsto_pi_nhds.mp hfa chi

end

end Submission.Helpers
