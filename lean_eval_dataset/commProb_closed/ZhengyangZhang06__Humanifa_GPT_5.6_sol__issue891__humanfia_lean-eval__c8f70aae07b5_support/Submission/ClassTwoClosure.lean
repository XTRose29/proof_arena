import Submission.ClassTwoProfile

namespace Submission.Helpers

open scoped BigOperators Filter Topology commutatorElement

noncomputable section

def mulAddMulEquiv (D : Type) [Group D] : D ≃* Multiplicative (Additive D) where
  toFun x := Multiplicative.ofAdd (Additive.ofMul x)
  invFun x := Additive.toMul (Multiplicative.toAdd x)
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

def complexAddCharToUnitChar {D : Type} [CommGroup D] [Finite D]
    (psi : AddChar (Additive D) ℂ) : D →* ℂˣ := by
  let psiCircle : AddChar (Additive D) Circle :=
    AddChar.circleEquivComplex.symm psi
  exact Circle.toUnits.comp
    ((AddChar.toMonoidHomEquiv psiCircle).comp (mulAddMulEquiv D).toMonoidHom)

def unitCharEquivComplexAddChar (D : Type) [CommGroup D] [Finite D] :
    (D →* ℂˣ) ≃ AddChar (Additive D) ℂ where
  toFun := unitCharToComplex
  invFun := complexAddCharToUnitChar
  left_inv chi := by
    ext x
    have h := DFunLike.congr_fun
      (AddChar.circleEquivComplex.apply_symm_apply (unitCharToComplex chi))
      (Additive.ofMul x)
    exact h
  right_inv psi := by
    ext x
    have h := DFunLike.congr_fun
      (AddChar.circleEquivComplex.apply_symm_apply psi) x
    exact h

noncomputable instance unitCharFintype (D : Type) [CommGroup D] [Finite D] :
    Fintype (D →* ℂˣ) :=
  Fintype.ofEquiv (AddChar (Additive D) ℂ)
    (unitCharEquivComplexAddChar D).symm

def transportedCommutatorCharacterEquiv
    (W : ℕ → FiniteCommProbWitness) (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (n : ℕ) :
    letI := (W 0).group
    letI := (W n).group
    letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
    letI := commutatorCommGroupOfLeCenter (W n).carrier (hcentral n)
    (commutator (W 0).carrier →* ℂˣ) ≃
      AddChar (Additive (commutator (W n).carrier)) ℂ := by
  letI := (W 0).group
  letI := (W 0).finite
  letI := (W n).group
  letI := (W n).finite
  letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
  letI := commutatorCommGroupOfLeCenter (W n).carrier (hcentral n)
  let e := fixedCommutatorMulEquiv W d hcard hcode n
  refine {
    toFun := transportedCommutatorCharacter W d hcard hcode n
    invFun := fun psi =>
      (complexAddCharToUnitChar psi).comp e.symm.toMonoidHom
    left_inv := ?_
    right_inv := ?_ }
  · intro chi
    change (complexAddCharToUnitChar
      (unitCharToComplex (chi.comp e.toMonoidHom))).comp e.symm.toMonoidHom = chi
    have hinv : complexAddCharToUnitChar
        (unitCharToComplex (chi.comp e.toMonoidHom)) = chi.comp e.toMonoidHom :=
      (unitCharEquivComplexAddChar
        (commutator (W n).carrier)).symm_apply_apply (chi.comp e.toMonoidHom)
    rw [hinv]
    ext x
    simp [e]
  · intro psi
    change unitCharToComplex
      (((complexAddCharToUnitChar psi).comp e.symm.toMonoidHom).comp e.toMonoidHom) = psi
    have hcomp :
        ((complexAddCharToUnitChar psi).comp e.symm.toMonoidHom).comp e.toMonoidHom =
          complexAddCharToUnitChar psi := by
      ext x
      simp [e]
    rw [hcomp]
    exact (unitCharEquivComplexAddChar
      (commutator (W n).carrier)).apply_symm_apply psi

lemma commProb_eq_expect_inv_classTwoCharacterIndex
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ) :
    letI := (W 0).group
    letI := (W 0).finite
    letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
    ((W n).probability : ℂ) =
      𝔼 chi : commutator (W 0).carrier →* ℂˣ,
        1 / (classTwoCharacterIndex W hcentral d hcard hcode n chi : ℂ) := by
  classical
  letI := (W 0).group
  letI := (W 0).finite
  letI := (W n).group
  letI := (W n).finite
  letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
  letI := commutatorCommGroupOfLeCenter (W n).carrier (hcentral n)
  letI := Fintype.ofFinite (commutator (W 0).carrier)
  letI := Fintype.ofFinite (commutator (W n).carrier)
  have hfourier := commProb_eq_expect_inv_commutatorCharMap_index
    (W n).carrier (hcentral n)
  calc
    ((W n).probability : ℂ) =
        𝔼 psi : AddChar (Additive (commutator (W n).carrier)) ℂ,
          1 / ((commutatorCharMap (W n).carrier (hcentral n) psi).ker.index : ℂ) := by
      simpa [FiniteCommProbWitness.probability] using hfourier
    _ = 𝔼 chi : commutator (W 0).carrier →* ℂˣ,
        1 / (classTwoCharacterIndex W hcentral d hcard hcode n chi : ℂ) := by
      symm
      apply Fintype.expect_equiv
        (transportedCommutatorCharacterEquiv W d hcard hcode hcentral n)
      intro chi
      rfl

lemma mem_CommProbRange_of_classTwoCharacterIndex_profile_finite
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (φ : ℕ → ℕ) {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W (φ n)).probability)
      Filter.atTop (𝓝 p))
    (a : letI := (W 0).group;
      letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
      (commutator (W 0).carrier →* ℂˣ) → WithTop ℕ)
    (ha : letI := (W 0).group;
      letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
      ∀ chi, Filter.Tendsto
        (fun n => (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : WithTop ℕ))
        Filter.atTop (𝓝 (a chi)))
    (hfinite : letI := (W 0).group;
      letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
      ∀ chi, a chi ≠ ⊤) :
    p ∈ CommProbRange := by
  classical
  letI := (W 0).group
  letI := (W 0).finite
  letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
  let b : (commutator (W 0).carrier →* ℂˣ) → ℕ := fun chi =>
    (a chi).untop (hfinite chi)
  have heventIndex : ∀ chi : commutator (W 0).carrier →* ℂˣ,
      ∀ᶠ n in Filter.atTop,
        classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi = b chi := by
    intro chi
    have h := ha chi
    rw [← WithTop.coe_untop (a chi) (hfinite chi)] at h
    have hevent := eventually_eq_of_tendsto_withTop_coe h
    filter_upwards [hevent] with n hn
    exact WithTop.coe_eq_coe.mp hn
  have heventAll : ∀ᶠ n in Filter.atTop, ∀ chi,
      classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi = b chi :=
    Filter.eventually_all.mpr heventIndex
  obtain ⟨N, hN⟩ := Filter.eventually_atTop.mp heventAll
  have hprobEq : ∀ n, N ≤ n →
      (W (φ n)).probability = (W (φ N)).probability := by
    intro n hn
    apply Complex.ofReal_injective
    rw [commProb_eq_expect_inv_classTwoCharacterIndex W hcentral d hcard hcode (φ n),
      commProb_eq_expect_inv_classTwoCharacterIndex W hcentral d hcard hcode (φ N)]
    apply Finset.expect_congr rfl
    intro chi _
    rw [hN n hn chi, hN N le_rfl chi]
  have heventProb : (fun n => (W (φ n)).probability) =ᶠ[Filter.atTop]
      fun _ => (W (φ N)).probability := by
    filter_upwards [Filter.eventually_ge_atTop N] with n hn
    exact hprobEq n hn
  have hprobConst : Filter.Tendsto (fun _ : ℕ => (W (φ N)).probability)
      Filter.atTop (𝓝 (W (φ N)).probability) := tendsto_const_nhds
  have hprob' : Filter.Tendsto (fun n => (W (φ n)).probability)
      Filter.atTop (𝓝 (W (φ N)).probability) :=
    hprobConst.congr' heventProb.symm
  have hp : p = (W (φ N)).probability := tendsto_nhds_unique hprob hprob'
  rw [hp]
  exact ⟨(W (φ N)).carrier, (W (φ N)).group, rfl⟩

lemma transportedCommutatorCharacter_mul
    (W : ℕ → FiniteCommProbWitness) (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ)
    (psi chi : letI := (W 0).group; commutator (W 0).carrier →* ℂˣ) :
    letI := (W n).group
    transportedCommutatorCharacter W d hcard hcode n (psi * chi) =
      transportedCommutatorCharacter W d hcard hcode n psi +
        transportedCommutatorCharacter W d hcard hcode n chi := by
  letI := (W 0).group
  letI := (W n).group
  ext x
  rfl

lemma transportedCommutatorCharacter_inv
    (W : ℕ → FiniteCommProbWitness)
    (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ)
    (chi : letI := (W 0).group; commutator (W 0).carrier →* ℂˣ) :
    letI := (W n).group
    transportedCommutatorCharacter W d hcard hcode n chi⁻¹ =
      unitCharToComplex
        ((chi.comp (fixedCommutatorMulEquiv W d hcard hcode n).toMonoidHom)⁻¹) := by
  letI := (W 0).group
  letI := (W n).group
  ext x
  rfl

lemma classTwoCharacterIndex_mul_le_mul
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ)
    (psi chi : letI := (W 0).group; commutator (W 0).carrier →* ℂˣ) :
    classTwoCharacterIndex W hcentral d hcard hcode n (psi * chi) ≤
      classTwoCharacterIndex W hcentral d hcard hcode n psi *
        classTwoCharacterIndex W hcentral d hcard hcode n chi := by
  letI := (W 0).group
  letI := (W n).group
  letI := (W n).finite
  simpa [classTwoCharacterIndex, transportedCommutatorCharacter_mul] using
    commutatorCharMap_index_add_le_mul (W n).carrier (hcentral n)
      (transportedCommutatorCharacter W d hcard hcode n psi)
      (transportedCommutatorCharacter W d hcard hcode n chi)

lemma classTwoCharacterIndex_inv
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ)
    (chi : letI := (W 0).group; commutator (W 0).carrier →* ℂˣ) :
    classTwoCharacterIndex W hcentral d hcard hcode n chi⁻¹ =
      classTwoCharacterIndex W hcentral d hcard hcode n chi := by
  letI := (W 0).group
  letI := (W n).group
  letI := (W n).finite
  change (commutatorCharMap (W n).carrier (hcentral n)
    (transportedCommutatorCharacter W d hcard hcode n chi⁻¹)).ker.index = _
  rw [transportedCommutatorCharacter_inv]
  exact commutatorCharMap_index_unitChar_inv (W n).carrier (hcentral n)
    (chi.comp (fixedCommutatorMulEquiv W d hcard hcode n).toMonoidHom)

lemma classTwoCharacterIndex_one
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ) :
    letI := (W 0).group
    classTwoCharacterIndex W hcentral d hcard hcode n 1 = 1 := by
  letI := (W 0).group
  letI := (W n).group
  letI := (W n).finite
  change (commutatorCharMap (W n).carrier (hcentral n)
    (transportedCommutatorCharacter W d hcard hcode n 1)).ker.index = 1
  have htransport : transportedCommutatorCharacter W d hcard hcode n 1 =
      unitCharToComplex (1 : commutator (W n).carrier →* ℂˣ) := by
    ext x
    rfl
  rw [htransport]
  exact commutatorCharMap_index_unitChar_one (W n).carrier (hcentral n)

def finiteClassTwoCharacterProfileSubgroup
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (φ : ℕ → ℕ)
    (a : letI := (W 0).group;
      letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
      (commutator (W 0).carrier →* ℂˣ) → WithTop ℕ)
    (ha : letI := (W 0).group;
      letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
      ∀ chi, Filter.Tendsto
        (fun n => (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : WithTop ℕ))
        Filter.atTop (𝓝 (a chi))) :
    letI := (W 0).group
    letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
    Subgroup (commutator (W 0).carrier →* ℂˣ) := by
  letI := (W 0).group
  letI := (W 0).finite
  letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
  refine {
    carrier := {chi | a chi ≠ ⊤}
    mul_mem' := ?_
    one_mem' := ?_
    inv_mem' := ?_ }
  · intro psi chi hpsi hchi
    change a psi ≠ ⊤ at hpsi
    change a chi ≠ ⊤ at hchi
    change a (psi * chi) ≠ ⊤
    let bpsi := (a psi).untop hpsi
    let bchi := (a chi).untop hchi
    have heventPsi : ∀ᶠ n in Filter.atTop,
        classTwoCharacterIndex W hcentral d hcard hcode (φ n) psi = bpsi := by
      have h := ha psi
      rw [← WithTop.coe_untop (a psi) hpsi] at h
      have hevent := eventually_eq_of_tendsto_withTop_coe h
      filter_upwards [hevent] with n hn
      exact WithTop.coe_eq_coe.mp hn
    have heventChi : ∀ᶠ n in Filter.atTop,
        classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi = bchi := by
      have h := ha chi
      rw [← WithTop.coe_untop (a chi) hchi] at h
      have hevent := eventually_eq_of_tendsto_withTop_coe h
      filter_upwards [hevent] with n hn
      exact WithTop.coe_eq_coe.mp hn
    intro htop
    have hprodTop := ha (psi * chi)
    rw [htop] at hprodTop
    have heventLarge : ∀ᶠ n in Filter.atTop,
        (bpsi * bchi : WithTop ℕ) <
          classTwoCharacterIndex W hcentral d hcard hcode (φ n) (psi * chi) :=
      (WithTop.tendsto_nhds_top_iff _).mp hprodTop (bpsi * bchi)
    obtain ⟨n, hnpsi, hnchi, hnlarge⟩ :=
      (heventPsi.and (heventChi.and heventLarge)).exists
    have hle := classTwoCharacterIndex_mul_le_mul W hcentral d hcard hcode
      (φ n) psi chi
    rw [hnpsi, hnchi] at hle
    have hle' :
        (classTwoCharacterIndex W hcentral d hcard hcode (φ n) (psi * chi) :
          WithTop ℕ) ≤ bpsi * bchi := by
      exact_mod_cast hle
    exact (not_lt_of_ge hle') hnlarge
  · change a 1 ≠ ⊤
    have honeTend : Filter.Tendsto
        (fun _ : ℕ => (1 : WithTop ℕ)) Filter.atTop (𝓝 (1 : WithTop ℕ)) :=
      tendsto_const_nhds
    have honeTend' : Filter.Tendsto
        (fun n => (classTwoCharacterIndex W hcentral d hcard hcode (φ n) 1 : WithTop ℕ))
        Filter.atTop (𝓝 (1 : WithTop ℕ)) := by
      have heq :
          (fun n => (classTwoCharacterIndex W hcentral d hcard hcode (φ n) 1 :
            WithTop ℕ)) = fun _ => (1 : WithTop ℕ) := by
        funext n
        rw [classTwoCharacterIndex_one]
        norm_num
      rw [heq]
      exact honeTend
    have hone : a 1 = (1 : WithTop ℕ) :=
      tendsto_nhds_unique (ha 1) honeTend'
    rw [hone]
    exact WithTop.coe_ne_top
  · intro chi hchi
    change a chi ≠ ⊤ at hchi
    change a chi⁻¹ ≠ ⊤
    have hinvTend : Filter.Tendsto
        (fun n => (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi⁻¹ :
          WithTop ℕ)) Filter.atTop (𝓝 (a chi)) := by
      apply (ha chi).congr
      intro n
      exact congrArg (fun k : ℕ => (k : WithTop ℕ))
        (classTwoCharacterIndex_inv W hcentral d hcard hcode (φ n) chi).symm
    have hinv : a chi⁻¹ = a chi :=
      tendsto_nhds_unique (ha chi⁻¹) hinvTend
    rw [hinv]
    exact hchi

noncomputable def subgroupPart {G : Type} [Group G] (K : Subgroup G) (x : G) : K :=
  ⟨(Quotient.out (x : G ⧸ K))⁻¹ * x, by
    rw [← QuotientGroup.eq]
    simp⟩

lemma out_mul_subgroupPart {G : Type} [Group G] (K : Subgroup G) (x : G) :
    Quotient.out (x : G ⧸ K) * subgroupPart K x = x := by
  simp [subgroupPart]

lemma subgroupPart_out_mul {G : Type} [Group G] (K : Subgroup G)
    (q : G ⧸ K) (k : K) :
    subgroupPart K (Quotient.out q * k) = k := by
  apply Subtype.ext
  simp [subgroupPart]

lemma quotient_out_mul_subgroup {G : Type} [Group G] (K : Subgroup G)
    (q : G ⧸ K) (k : K) :
    ((Quotient.out q * k : G) : G ⧸ K) = q := by
  calc
    ((Quotient.out q * k : G) : G ⧸ K) =
        Quotient.mk'' (Quotient.out q) := by simp
    _ = q := Quotient.out_eq q

abbrev QuotientCommutingLiftPairs (G : Type) [Group G] (K : Subgroup G) [K.Normal] :=
  {p : G × G // Commute ((p.1 : G) : G ⧸ K) ((p.2 : G) : G ⧸ K)}

noncomputable def quotientCommutingLiftPairsEquiv
    (G : Type) [Group G] (K : Subgroup G) [K.Normal] :
    QuotientCommutingLiftPairs G K ≃
      CommutingPairs (G ⧸ K) × (K × K) where
  toFun p :=
    let qx : G ⧸ K := p.1.1
    let qy : G ⧸ K := p.1.2
    let kx := subgroupPart K p.1.1
    let ky := subgroupPart K p.1.2
    ⟨⟨(qx, qy), p.2⟩, (kx, ky)⟩
  invFun p :=
    ⟨(Quotient.out p.1.1.1 * p.2.1, Quotient.out p.1.1.2 * p.2.2), by
      change Commute
        (((Quotient.out p.1.1.1 * p.2.1 : G) : G ⧸ K))
        (((Quotient.out p.1.1.2 * p.2.2 : G) : G ⧸ K))
      simpa [quotient_out_mul_subgroup] using p.1.2⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · exact out_mul_subgroupPart K p.1.1
    · exact out_mul_subgroupPart K p.1.2
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact quotient_out_mul_subgroup K p.1.1.1 p.2.1
      · exact quotient_out_mul_subgroup K p.1.1.2 p.2.2
    · apply Prod.ext
      · exact subgroupPart_out_mul K p.1.1.1 p.2.1
      · exact subgroupPart_out_mul K p.1.1.2 p.2.2

lemma commProb_quotient_eq_liftPairRatio
    (G : Type) [Group G] [Finite G] (K : Subgroup G) [K.Normal] :
    commProb (G ⧸ K) = Nat.card (QuotientCommutingLiftPairs G K) /
      (Nat.card G : ℚ) ^ 2 := by
  rw [commProb_def]
  rw [Nat.card_congr (quotientCommutingLiftPairsEquiv G K),
    Nat.card_prod, Nat.card_prod]
  rw [← K.card_mul_index]
  rw [K.index_eq_card]
  push_cast
  have hK : (Nat.card K : ℚ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Finite.card_pos.ne'
  field_simp

def unitCharacterAnnihilator (D : Type) [Group D]
    (X : Subgroup (D →* ℂˣ)) : Subgroup D where
  carrier := {d | ∀ chi : X, chi.1 d = 1}
  mul_mem' := by
    intro x y hx hy chi
    rw [map_mul, hx chi, hy chi, mul_one]
  one_mem' := by
    intro chi
    exact map_one chi.1
  inv_mem' := by
    intro x hx chi
    rw [map_inv, hx chi, inv_one]

def classTwoAnnihilatorInGroup
    (G : Type) [Group G]
    (_hcentral : commutator G ≤ Subgroup.center G)
    (X : Subgroup (commutator G →* ℂˣ)) : Subgroup G :=
  (unitCharacterAnnihilator (commutator G) X).map (commutator G).subtype

lemma classTwoAnnihilatorInGroup_le_center
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (X : Subgroup (commutator G →* ℂˣ)) :
    classTwoAnnihilatorInGroup G hcentral X ≤ Subgroup.center G := by
  intro x hx
  rcases hx with ⟨d, _hd, rfl⟩
  exact hcentral d.property

theorem classTwoAnnihilatorInGroupNormal
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (X : Subgroup (commutator G →* ℂˣ)) :
    (classTwoAnnihilatorInGroup G hcentral X).Normal := by
  constructor
  intro x hx g
  have hxcenter := classTwoAnnihilatorInGroup_le_center G hcentral X hx
  have hxg : x * g = g * x := (Subgroup.mem_center_iff.mp hxcenter g).symm
  have hconj : g * x * g⁻¹ = x := by
    calc
      g * x * g⁻¹ = x * g * g⁻¹ := by rw [hxg]
      _ = x := by simp
  rw [hconj]
  exact hx

lemma commutator_mem_classTwoAnnihilatorInGroup_iff
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (X : Subgroup (commutator G →* ℂˣ)) (d : commutator G) :
    (d : G) ∈ classTwoAnnihilatorInGroup G hcentral X ↔
      d ∈ unitCharacterAnnihilator (commutator G) X := by
  constructor
  · rintro ⟨e, he, hval⟩
    have hed : e = d := Subtype.ext hval
    simpa [hed] using he
  · intro hd
    exact ⟨d, hd, rfl⟩

def unitCharacterEvaluation
    (D : Type) [CommGroup D] (X : Subgroup (D →* ℂˣ)) (d : D) :
    AddChar (Additive X) ℂ :=
  unitCharToComplex {
    toFun := fun chi => chi.1 d
    map_one' := rfl
    map_mul' := fun _ _ => rfl }

noncomputable def complexPropIndicator (P : Prop) : ℂ := by
  classical
  exact if P then 1 else 0

lemma expect_unitCharacterEvaluation_eq_indicator
    (D : Type) [CommGroup D] [Finite D]
    (X : Subgroup (D →* ℂˣ)) (d : D) :
    letI := Fintype.ofFinite X
    (𝔼 chi : X, ((chi.1 d : ℂˣ) : ℂ)) =
      complexPropIndicator (d ∈ unitCharacterAnnihilator D X) := by
  classical
  letI := Fintype.ofFinite X
  let eval := unitCharacterEvaluation D X d
  have hexpect : (𝔼 chi : X, ((chi.1 d : ℂˣ) : ℂ)) =
      𝔼 chi : Additive X, eval chi := by
    apply Fintype.expect_equiv Additive.ofMul
    intro chi
    rfl
  rw [hexpect, AddChar.expect_eq_ite]
  by_cases hd : d ∈ unitCharacterAnnihilator D X
  · have heval : eval = 0 := by
      apply AddChar.ext
      intro chi
      change ((chi.toMul.1 d : ℂˣ) : ℂ) = 1
      exact congrArg (fun u : ℂˣ => (u : ℂ)) (hd chi.toMul)
    simp [hd, heval, complexPropIndicator]
  · have heval : eval ≠ 0 := by
      intro heval
      apply hd
      intro chi
      have h := congrArg (fun f : AddChar (Additive X) ℂ => f (Additive.ofMul chi)) heval
      change ((chi.1 d : ℂˣ) : ℂ) = 1 at h
      exact Units.ext h
    simp [hd, heval, complexPropIndicator]

lemma quotient_commute_iff_derivedCommutator_mem_annihilator
    (G : Type) [Group G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (X : Subgroup (commutator G →* ℂˣ)) (x y : G) :
    let K := classTwoAnnihilatorInGroup G hcentral X
    letI := classTwoAnnihilatorInGroupNormal G hcentral X
    Commute ((x : G) : G ⧸ K) ((y : G) : G ⧸ K) ↔
      derivedCommutator G x y ∈ unitCharacterAnnihilator (commutator G) X := by
  let K := classTwoAnnihilatorInGroup G hcentral X
  letI := classTwoAnnihilatorInGroupNormal G hcentral X
  change (((x : G) : G ⧸ K) * (y : G)) =
      ((y : G) : G ⧸ K) * (x : G) ↔ _
  rw [← commutatorElement_eq_one_iff_mul_comm]
  change ((⁅x, y⁆ : G) : G ⧸ K) = 1 ↔ _
  rw [QuotientGroup.eq_one_iff]
  exact commutator_mem_classTwoAnnihilatorInGroup_iff G hcentral X
    (derivedCommutator G x y)

lemma expect_quotient_commute_indicator_eq_liftPairRatio
    (G : Type) [Group G] [Finite G] (K : Subgroup G) [K.Normal] :
    letI := Fintype.ofFinite G
    (𝔼 x : G, 𝔼 y : G,
      complexPropIndicator (Commute ((x : G) : G ⧸ K) ((y : G) : G ⧸ K))) =
      (((Nat.card (QuotientCommutingLiftPairs G K) : ℚ) /
        (Nat.card G : ℚ) ^ 2 : ℚ) : ℂ) := by
  classical
  letI := Fintype.ofFinite G
  rw [← Finset.expect_product']
  simp only [Finset.univ_product_univ]
  rw [Fintype.expect_eq_sum_div_card]
  simp only [complexPropIndicator]
  rw [Finset.sum_boole]
  push_cast
  congr 2
  · rw [Nat.card_eq_fintype_card]
    exact (Fintype.subtype_card _ (by simp)).symm
  · rw [Fintype.card_prod, Nat.card_eq_fintype_card]
    simp [pow_two, Nat.cast_mul]

lemma commProb_classTwoAnnihilatorQuotient_eq_expect
    (G : Type) [Group G] [Finite G]
    (hcentral : commutator G ≤ Subgroup.center G)
    (X : Subgroup (commutator G →* ℂˣ)) :
    let K := classTwoAnnihilatorInGroup G hcentral X
    letI := classTwoAnnihilatorInGroupNormal G hcentral X
    letI := commutatorCommGroupOfLeCenter G hcentral
    letI := Fintype.ofFinite X
    ((commProb (G ⧸ K) : ℚ) : ℂ) =
      𝔼 chi : X,
        1 / ((commutatorCharMap G hcentral (unitCharToComplex chi.1)).ker.index : ℂ) := by
  classical
  let K := classTwoAnnihilatorInGroup G hcentral X
  letI := classTwoAnnihilatorInGroupNormal G hcentral X
  letI := commutatorCommGroupOfLeCenter G hcentral
  letI := Fintype.ofFinite G
  letI := Fintype.ofFinite (commutator G)
  letI := Fintype.ofFinite X
  calc
    ((commProb (G ⧸ K) : ℚ) : ℂ) =
        (((Nat.card (QuotientCommutingLiftPairs G K) : ℚ) /
          (Nat.card G : ℚ) ^ 2 : ℚ) : ℂ) := by
      exact_mod_cast commProb_quotient_eq_liftPairRatio G K
    _ = 𝔼 x : G, 𝔼 y : G,
        complexPropIndicator (Commute ((x : G) : G ⧸ K) ((y : G) : G ⧸ K)) :=
      (expect_quotient_commute_indicator_eq_liftPairRatio G K).symm
    _ = 𝔼 x : G, 𝔼 y : G, 𝔼 chi : X,
        ((chi.1 (derivedCommutator G x y) : ℂˣ) : ℂ) := by
      apply Finset.expect_congr rfl
      intro x _
      apply Finset.expect_congr rfl
      intro y _
      rw [expect_unitCharacterEvaluation_eq_indicator]
      congr 1
      exact propext
        (quotient_commute_iff_derivedCommutator_mem_annihilator G hcentral X x y)
    _ = 𝔼 chi : X, 𝔼 x : G, 𝔼 y : G,
        ((chi.1 (derivedCommutator G x y) : ℂˣ) : ℂ) :=
      @expect_rotate_three G G X _ _ _
        (fun x y chi => ((chi.1 (derivedCommutator G x y) : ℂˣ) : ℂ))
    _ = 𝔼 chi : X,
        1 / ((commutatorCharMap G hcentral (unitCharToComplex chi.1)).ker.index : ℂ) := by
      apply Finset.expect_congr rfl
      intro chi _
      exact expect_commutator_character_on_group_eq_inv_index
        G hcentral (unitCharToComplex chi.1)

def transportedUnitCharacterMulEquiv
    (W : ℕ → FiniteCommProbWitness) (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ) :
    letI := (W 0).group
    letI := (W n).group
    (commutator (W 0).carrier →* ℂˣ) ≃*
      (commutator (W n).carrier →* ℂˣ) := by
  letI := (W 0).group
  letI := (W n).group
  let e := fixedCommutatorMulEquiv W d hcard hcode n
  refine {
    toFun := fun chi => chi.comp e.toMonoidHom
    invFun := fun chi => chi.comp e.symm.toMonoidHom
    left_inv := ?_
    right_inv := ?_
    map_mul' := ?_ }
  · intro chi
    ext x
    simp [e]
  · intro chi
    ext x
    simp [e]
  · intro psi chi
    rfl

def transportedUnitCharacterHom
    (W : ℕ → FiniteCommProbWitness) (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ) :
    letI := (W 0).group
    letI := (W n).group
    (commutator (W 0).carrier →* ℂˣ) →*
      (commutator (W n).carrier →* ℂˣ) where
  toFun chi := chi.comp (fixedCommutatorMulEquiv W d hcard hcode n).toMonoidHom
  map_one' := rfl
  map_mul' _ _ := rfl

lemma transportedUnitCharacterHom_injective
    (W : ℕ → FiniteCommProbWitness) (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (n : ℕ) :
    letI := (W 0).group
    letI := (W n).group
    Function.Injective (transportedUnitCharacterHom W d hcard hcode n) := by
  letI := (W 0).group
  letI := (W n).group
  intro psi chi h
  ext x
  have hx := congrArg
    (fun f : commutator (W n).carrier →* ℂˣ =>
      f ((fixedCommutatorMulEquiv W d hcard hcode n).symm x)) h
  have hx' := congrArg (fun u : ℂˣ => (u : ℂ)) hx
  simpa [transportedUnitCharacterHom] using hx'

def transportedUnitCharacterSubgroup
    (W : ℕ → FiniteCommProbWitness) (d : ℕ)
    (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (X : letI := (W 0).group; Subgroup (commutator (W 0).carrier →* ℂˣ))
    (n : ℕ) :
    letI := (W n).group
    Subgroup (commutator (W n).carrier →* ℂˣ) :=
  X.map (transportedUnitCharacterHom W d hcard hcode n)

def classTwoProfileQuotientWitness
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (X : letI := (W 0).group; Subgroup (commutator (W 0).carrier →* ℂˣ))
    (n : ℕ) : FiniteCommProbWitness := by
  letI := (W 0).group
  letI := (W n).group
  letI := (W n).finite
  let Xn := transportedUnitCharacterSubgroup W d hcard hcode X n
  let K := classTwoAnnihilatorInGroup (W n).carrier (hcentral n) Xn
  letI := classTwoAnnihilatorInGroupNormal (W n).carrier (hcentral n) Xn
  exact ⟨(W n).carrier ⧸ K, inferInstance, inferInstance⟩

lemma classTwoProfileQuotient_probability_eq_expect
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (X : letI := (W 0).group; Subgroup (commutator (W 0).carrier →* ℂˣ))
    (n : ℕ) :
    letI := (W 0).group
    letI := (W 0).finite
    letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
    letI := Fintype.ofFinite X
    ((classTwoProfileQuotientWitness W hcentral d hcard hcode X n).probability : ℂ) =
      𝔼 chi : X,
        1 / (classTwoCharacterIndex W hcentral d hcard hcode n chi.1 : ℂ) := by
  classical
  letI := (W 0).group
  letI := (W 0).finite
  letI := (W n).group
  letI := (W n).finite
  letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
  letI := commutatorCommGroupOfLeCenter (W n).carrier (hcentral n)
  letI := Fintype.ofFinite (commutator (W 0).carrier)
  letI := Fintype.ofFinite (commutator (W n).carrier)
  letI := Fintype.ofFinite X
  let e := transportedUnitCharacterHom W d hcard hcode n
  let Xn := transportedUnitCharacterSubgroup W d hcard hcode X n
  let K := classTwoAnnihilatorInGroup (W n).carrier (hcentral n) Xn
  letI := classTwoAnnihilatorInGroupNormal (W n).carrier (hcentral n) Xn
  letI := Fintype.ofFinite Xn
  have hquot := commProb_classTwoAnnihilatorQuotient_eq_expect
    (W n).carrier (hcentral n) Xn
  calc
    ((classTwoProfileQuotientWitness W hcentral d hcard hcode X n).probability : ℂ) =
        𝔼 chi : Xn,
          1 / ((commutatorCharMap (W n).carrier (hcentral n)
            (unitCharToComplex chi.1)).ker.index : ℂ) := by
      change ((((commProb ((W n).carrier ⧸ K) : ℚ) : ℝ)) : ℂ) = _
      exact_mod_cast hquot
    _ = 𝔼 chi : X,
        1 / (classTwoCharacterIndex W hcentral d hcard hcode n chi.1 : ℂ) := by
      let eX : X ≃* Xn := by
        exact Subgroup.equivMapOfInjective X e
          (transportedUnitCharacterHom_injective W d hcard hcode n)
      let f : X → ℂ := fun chi =>
        1 / (classTwoCharacterIndex W hcentral d hcard hcode n chi.1 : ℂ)
      let g : Xn → ℂ := fun chi =>
        1 / ((commutatorCharMap (W n).carrier (hcentral n)
          (unitCharToComplex chi.1)).ker.index : ℂ)
      have hfg : ∀ chi, f chi = g (eX chi) := by
        intro chi
        change 1 / (classTwoCharacterIndex W hcentral d hcard hcode n chi.1 : ℂ) =
          1 / ((commutatorCharMap (W n).carrier (hcentral n)
            (unitCharToComplex ((eX chi).1))).ker.index : ℂ)
        rfl
      have hreindex := Fintype.expect_equiv eX.toEquiv f g hfg
      change (𝔼 chi : Xn, g chi) = 𝔼 chi : X, f chi
      exact hreindex.symm

noncomputable def subgroupComplementFinset
    (A : Type) [Group A] [Fintype A] (X : Subgroup A) : Finset A := by
  classical
  exact Finset.univ.filter fun a => a ∉ X

lemma subgroup_index_mul_expect_eq_expect_add_compl
    (A : Type) [Group A] [Fintype A]
    (X : Subgroup A) [Fintype X] (f : A → ℂ) :
    (X.index : ℂ) * (𝔼 a : A, f a) =
      (𝔼 x : X, f x.1) +
        (∑ a ∈ subgroupComplementFinset A X, f a) / (Fintype.card X : ℂ) := by
  classical
  have hsubtype :
      ∑ a ∈ Finset.univ with a ∈ X, f a = ∑ x : X, f x.1 := by
    exact Finset.sum_subtype _ (by simp) f
  have hpartition := Finset.sum_filter_add_sum_filter_not Finset.univ
    (fun a : A => a ∈ X) f
  have hcard : Fintype.card X * X.index = Fintype.card A := by
    simpa [Nat.card_eq_fintype_card] using X.card_mul_index
  have hcardC : (Fintype.card A : ℂ) =
      (Fintype.card X : ℂ) * (X.index : ℂ) := by
    exact_mod_cast hcard.symm
  rw [Finset.expect_eq_sum_div_card, Finset.expect_eq_sum_div_card]
  simp only [Finset.card_univ]
  rw [← hpartition, hsubtype, hcardC]
  change _ = _ +
    (∑ a ∈ Finset.univ with a ∉ X, f a) / (Fintype.card X : ℂ)
  have hX : (Fintype.card X : ℂ) ≠ 0 := by
    exact_mod_cast Fintype.card_ne_zero
  have hindex : (X.index : ℂ) ≠ 0 := by
    exact_mod_cast X.index_ne_zero_of_finite
  field_simp [hX, hindex]

lemma tendsto_inv_natCast_zero_of_tendsto_withTop_top
    {f : ℕ → ℕ}
    (hf : Filter.Tendsto (fun n => (f n : WithTop ℕ)) Filter.atTop (𝓝 ⊤)) :
    Filter.Tendsto (fun n => 1 / (f n : ℂ)) Filter.atTop (𝓝 0) := by
  apply (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℂ)).comp
  rw [Filter.tendsto_atTop]
  intro b
  have hlarge := (WithTop.tendsto_nhds_top_iff _).mp hf b
  filter_upwards [hlarge] with n hn
  exact (WithTop.coe_lt_coe.mp hn).le

lemma classTwoCharacterIndex_profile_dichotomy
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (d : ℕ) (hcard : ∀ n, (W n).commutatorCard = d)
    (hcode : ∀ n (hn : (W n).commutatorCard = d)
      (hzero : (W 0).commutatorCard = d),
      (W n).commutatorMulCode d hn = (W 0).commutatorMulCode d hzero)
    (φ : ℕ → ℕ) {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W (φ n)).probability)
      Filter.atTop (𝓝 p))
    (a : letI := (W 0).group;
      letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
      (commutator (W 0).carrier →* ℂˣ) → WithTop ℕ)
    (ha : letI := (W 0).group;
      letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
      ∀ chi, Filter.Tendsto
        (fun n => (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi :
          WithTop ℕ)) Filter.atTop (𝓝 (a chi))) :
    p ∈ CommProbRange ∨
      ∃ q : ℕ, 2 ≤ q ∧
        ClusterPt ((q : ℝ) * p) (Filter.principal CommProbRange) := by
  classical
  letI := (W 0).group
  letI := (W 0).finite
  letI := commutatorCommGroupOfLeCenter (W 0).carrier (hcentral 0)
  letI := Fintype.ofFinite (commutator (W 0).carrier)
  by_cases hfinite : ∀ chi, a chi ≠ ⊤
  · exact Or.inl (mem_CommProbRange_of_classTwoCharacterIndex_profile_finite
      W hcentral d hcard hcode φ hprob a ha hfinite)
  · let A := commutator (W 0).carrier →* ℂˣ
    let X := finiteClassTwoCharacterProfileSubgroup
      W hcentral d hcard hcode φ a ha
    letI := Fintype.ofFinite X
    have hX_ne_top : X ≠ ⊤ := by
      intro htop
      apply hfinite
      intro chi
      have hmem : chi ∈ X := by
        rw [htop]
        exact Subgroup.mem_top chi
      change a chi ≠ ⊤ at hmem
      exact hmem
    let q := X.index
    have hq : 2 ≤ q := by
      have := Subgroup.one_lt_index_of_ne_top hX_ne_top
      omega
    have hfull : Filter.Tendsto
        (fun n => 𝔼 chi : A,
          1 / (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : ℂ))
        Filter.atTop (𝓝 (p : ℂ)) := by
      refine hprob.ofReal.congr' (Filter.Eventually.of_forall fun n => ?_)
      exact commProb_eq_expect_inv_classTwoCharacterIndex
        W hcentral d hcard hcode (φ n)
    have hcomplTerm : ∀ chi ∈ subgroupComplementFinset A X,
        Filter.Tendsto
          (fun n => 1 /
            (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : ℂ))
          Filter.atTop (𝓝 0) := by
      intro chi hchi
      have hnot : chi ∉ X := by
        simpa [subgroupComplementFinset] using hchi
      have hatop : a chi = ⊤ := by
        by_contra hne
        apply hnot
        change a chi ≠ ⊤
        exact hne
      have hindex := ha chi
      rw [hatop] at hindex
      exact tendsto_inv_natCast_zero_of_tendsto_withTop_top hindex
    have hcomplSum : Filter.Tendsto
        (fun n => ∑ chi ∈ subgroupComplementFinset A X,
          1 / (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : ℂ))
        Filter.atTop (𝓝 0) := by
      simpa using tendsto_finsetSum (subgroupComplementFinset A X) hcomplTerm
    have hcompl : Filter.Tendsto
        (fun n => (∑ chi ∈ subgroupComplementFinset A X,
          1 / (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : ℂ)) /
            (Fintype.card X : ℂ)) Filter.atTop (𝓝 0) := by
      simpa using hcomplSum.div_const (Fintype.card X : ℂ)
    have hscaledFull : Filter.Tendsto
        (fun n => (q : ℂ) * (𝔼 chi : A,
          1 / (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : ℂ)))
        Filter.atTop (𝓝 ((q : ℂ) * (p : ℂ))) :=
      hfull.const_mul (q : ℂ)
    have hdiff : Filter.Tendsto
        (fun n => (q : ℂ) * (𝔼 chi : A,
            1 / (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : ℂ)) -
          (∑ chi ∈ subgroupComplementFinset A X,
            1 / (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : ℂ)) /
              (Fintype.card X : ℂ))
        Filter.atTop (𝓝 ((q : ℂ) * (p : ℂ))) := by
      simpa using hscaledFull.sub hcompl
    have hXexpect : Filter.Tendsto
        (fun n => 𝔼 chi : X,
          1 / (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi.1 : ℂ))
        Filter.atTop (𝓝 ((q : ℂ) * (p : ℂ))) := by
      refine hdiff.congr' (Filter.Eventually.of_forall fun n => ?_)
      have hid := subgroup_index_mul_expect_eq_expect_add_compl A X
        (fun chi =>
          1 / (classTwoCharacterIndex W hcentral d hcard hcode (φ n) chi : ℂ))
      change _ - _ = _
      exact ((eq_sub_iff_add_eq).2 hid.symm).symm
    let V : ℕ → FiniteCommProbWitness := fun n =>
      classTwoProfileQuotientWitness W hcentral d hcard hcode X (φ n)
    have hVcomplex : Filter.Tendsto (fun n => ((V n).probability : ℂ))
        Filter.atTop (𝓝 ((q : ℂ) * (p : ℂ))) := by
      refine hXexpect.congr' (Filter.Eventually.of_forall fun n => ?_)
      exact (classTwoProfileQuotient_probability_eq_expect
        W hcentral d hcard hcode X (φ n)).symm
    have hVreal : Filter.Tendsto (fun n => (V n).probability)
        Filter.atTop (𝓝 ((q : ℝ) * p)) := by
      have hre := Complex.continuous_re.continuousAt.tendsto.comp hVcomplex
      change Filter.Tendsto (fun n => Complex.re ((V n).probability : ℂ))
        Filter.atTop (𝓝 (Complex.re ((q : ℂ) * (p : ℂ)))) at hre
      simpa using hre
    have hcluster : ClusterPt ((q : ℝ) * p)
        (Filter.principal CommProbRange) := by
      rw [← mem_closure_iff_clusterPt]
      apply mem_closure_iff_seq_limit.mpr
      refine ⟨fun n => (V n).probability, ?_, hVreal⟩
      intro n
      exact ⟨(V n).carrier, (V n).group, rfl⟩
    exact Or.inr ⟨q, hq, hcluster⟩

lemma classTwo_probability_limit_dichotomy
    (W : ℕ → FiniteCommProbWitness)
    (hcentral : ∀ n,
      letI := (W n).group
      commutator (W n).carrier ≤ Subgroup.center (W n).carrier)
    (B : ℕ) (hbound : ∀ n, (W n).commutatorCard ≤ B)
    {p : ℝ}
    (hprob : Filter.Tendsto (fun n => (W n).probability)
      Filter.atTop (𝓝 p)) :
    p ∈ CommProbRange ∨
      ∃ q : ℕ, 2 ≤ q ∧
        ClusterPt ((q : ℝ) * p) (Filter.principal CommProbRange) := by
  obtain ⟨d, φ₁, hφ₁, hcard, hcode⟩ :=
    exists_fixed_commutator_model_subsequence W B hbound
  let W₁ : ℕ → FiniteCommProbWitness := fun n => W (φ₁ n)
  have hcentral₁ : ∀ n,
      letI := (W₁ n).group
      commutator (W₁ n).carrier ≤ Subgroup.center (W₁ n).carrier := by
    intro n
    exact hcentral (φ₁ n)
  have hcard₁ : ∀ n, (W₁ n).commutatorCard = d := by
    intro n
    exact hcard n
  have hcode₁ : ∀ n (hn : (W₁ n).commutatorCard = d)
      (hzero : (W₁ 0).commutatorCard = d),
      (W₁ n).commutatorMulCode d hn = (W₁ 0).commutatorMulCode d hzero := by
    intro n hn hzero
    exact hcode n hn hzero
  have hprob₁ : Filter.Tendsto (fun n => (W₁ n).probability)
      Filter.atTop (𝓝 p) := hprob.comp hφ₁.tendsto_atTop
  obtain ⟨a, φ₂, hφ₂, ha⟩ :=
    exists_classTwoCharacterIndex_profile_subsequence
      W₁ hcentral₁ d hcard₁ hcode₁
  exact classTwoCharacterIndex_profile_dichotomy
    W₁ hcentral₁ d hcard₁ hcode₁ φ₂
    (hprob₁.comp hφ₂.tendsto_atTop) a ha

end

end Submission.Helpers
