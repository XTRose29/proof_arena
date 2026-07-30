import Submission.OddOrder.PF.Section12.FTType1SequentialOrthogonality

/-!
# Peterfalvi Section 12: constituent and inverse-Dade constants

This module proves Peterfalvi (12.4)--(12.5).  Orthogonality to the
canonical type-I target families first forces a class function to be
constant on cosets of the Fitting core outside that core.  Via inverse-Dade
reciprocity, the same hypothesis then forces the inverse-Dade image to be
constant on the nonderived layer of the Fitting core.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open ClassFunction
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance : Fintype G := Fintype.ofFinite G

local instance : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Transport across the ambient top subgroup -/

private noncomputable def constituentTopTargetMap :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

private noncomputable def constituentAmbientTopMap :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

private theorem constituentTopTargetMap_ambientTopMap
    (phi : ClassFunction G ℂ) :
    constituentTopTargetMap (constituentAmbientTopMap phi) = phi := by
  ext x
  simp [constituentTopTargetMap, constituentAmbientTopMap,
    ClassFunction.comap_apply]

private theorem constituentTopTargetMap_starPairing
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    starCharacterPairing (constituentTopTargetMap phi)
        (constituentTopTargetMap psi) =
      starCharacterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold starCharacterPairing twistedCharacterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [constituentTopTargetMap, ClassFunction.comap_apply]

private theorem constituentTopTargetMap_eq_induceTop
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    constituentTopTargetMap phi =
      ClassFunction.induce (⊤ : Subgroup G) phi := by
  apply ClassFunction.ext
  intro x
  rw [ClassFunction.induce_apply_formula]
  have hvalue (y : G) :
      phi ⟨y⁻¹ * x * y, Subgroup.mem_top _⟩ =
        phi (Subgroup.topEquiv.symm x) := by
    have harg :
        (⟨y⁻¹ * x * y, Subgroup.mem_top _⟩ : (⊤ : Subgroup G)) =
          Subgroup.topEquiv.symm y⁻¹ *
            Subgroup.topEquiv.symm x *
              (Subgroup.topEquiv.symm y⁻¹)⁻¹ := by
      apply Subtype.ext
      simp
    rw [harg]
    exact ClassFunction.conj_apply phi
      (Subgroup.topEquiv.symm y⁻¹) (Subgroup.topEquiv.symm x)
  simp_rw [dif_pos (Subgroup.mem_top _), hvalue]
  simp only [constituentTopTargetMap, ClassFunction.comap_apply,
    Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card]
  have hcard : Nat.card (⊤ : Subgroup G) = Nat.card G :=
    Nat.card_congr Subgroup.topEquiv.toEquiv
  rw [hcard]
  field_simp [Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne']
  rfl

/-- A difference whose values agree at the identity is supported away from
the identity. -/
private theorem subSupportedOnNonidentityOfEqAtOne
    {Q : Type} [Group Q]
    (phi psi : ClassFunction Q ℂ) (h : phi 1 = psi 1) :
    phi - psi ∈ ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxOne : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp [h]

/-- Finite sums do not depend on whether a finite set is indexed through
its `Finset` subtype or through the subtype of its coercion to a `Set`. -/
private theorem finsetSum_eq_sumCoeSubtype
    {α M : Type*} [AddCommMonoid M]
    (s : Finset α) (f : α → M) :
    s.sum f = ∑ x : (s : Set α), f x.1 := by
  classical
  calc
    s.sum f = ∑ x : {x // x ∈ s}, f x.1 :=
      Finset.sum_subtype s (fun _ ↦ Iff.rfl) f
    _ = ∑ x : (s : Set α), f x.1 := by
      apply Fintype.sum_equiv (Equiv.refl _)
      intro x
      rfl

/-- A finite sum is independent of the chosen `Fintype` enumeration. -/
private theorem fintypeSum_eq
    {α M : Type*} [AddCommMonoid M]
    (i j : Fintype α) (f : α → M) :
    (@Finset.univ α i).sum f = (@Finset.univ α j).sum f := by
  apply Finset.sum_congr
  · ext x
    simp
  · intro x hx
    rfl

/-- Restrict a complement decomposition to an intermediate subgroup
containing the normal factor. -/
private theorem complementSubgroupOfInfRight
    {Q : Type*} [Group Q] {N C T : Subgroup Q}
    (hNC : N.IsComplement' C) (hNT : N ≤ T) :
    (N.subgroupOf T).IsComplement'
      ((C ⊓ T).subgroupOf T) := by
  change Function.Bijective
    (fun x : (N.subgroupOf T) × ((C ⊓ T).subgroupOf T) ↦
      (x.1 : T) * (x.2 : T))
  constructor
  · intro x y hxy
    let xQ : N × C :=
      (⟨((x.1 : T) : Q), x.1.property⟩,
        ⟨((x.2 : T) : Q), x.2.property.1⟩)
    let yQ : N × C :=
      (⟨((y.1 : T) : Q), y.1.property⟩,
        ⟨((y.2 : T) : Q), y.2.property.1⟩)
    have hxyQ : (xQ.1 : Q) * (xQ.2 : Q) =
        (yQ.1 : Q) * (yQ.2 : Q) :=
      congrArg Subtype.val hxy
    have hpair : xQ = yQ := hNC.1 hxyQ
    apply Prod.ext
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : N × C ↦ (z.1 : Q)) hpair
    · apply Subtype.ext
      apply Subtype.ext
      exact congrArg (fun z : N × C ↦ (z.2 : Q)) hpair
  · intro t
    obtain ⟨⟨n, c⟩, hnc⟩ := hNC.2 (t : Q)
    have hcT : (c : Q) ∈ T := by
      have hcEq : (c : Q) = (n : Q)⁻¹ * (t : Q) := by
        rw [← hnc]
        simp
      rw [hcEq]
      exact T.mul_mem (T.inv_mem (hNT n.property)) t.property
    let nT : N.subgroupOf T :=
      ⟨⟨(n : Q), hNT n.property⟩, n.property⟩
    let cT : (C ⊓ T).subgroupOf T :=
      ⟨⟨(c : Q), hcT⟩, ⟨c.property, hcT⟩⟩
    refine ⟨(nT, cT), ?_⟩
    apply Subtype.ext
    exact hnc

/-! ## Peterfalvi (12.4) -/

/-- In the normal Hall/abelian-inertia setting, every inertia constituent
restricts to the canonical extension of the original character. -/
private theorem inertiaConstituentRestrictEqCanonical
    {Q : Type} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    [IsMulCommutative
      ((ClassFunction.inertia H (theta : ClassFunction H ℂ)) ⧸
        H.subgroupOf
          (ClassFunction.inertia H (theta : ClassFunction H ℂ)))]
    (hHall : Nat.Coprime
      (Nat.card (H.subgroupOf
        (ClassFunction.inertia H (theta : ClassFunction H ℂ))))
      (H.subgroupOf
        (ClassFunction.inertia H (theta : ClassFunction H ℂ))).index)
    (psi : IrreducibleCharacter
      (ClassFunction.inertia H (theta : ClassFunction H ℂ)) ℂ)
    (hpsi : psi ∈ ClassFunction.inertiaConstituents H theta) :
    let T := ClassFunction.inertia H (theta : ClassFunction H ℂ)
    let K := H.subgroupOf T
    ClassFunction.restrict K (psi : ClassFunction T ℂ) =
      (ClassFunction.inertiaSubgroupCharacter H theta :
        ClassFunction K ℂ) := by
  let T := ClassFunction.inertia H (theta : ClassFunction H ℂ)
  let K := H.subgroupOf T
  let thetaT := ClassFunction.inertiaSubgroupCharacter H theta
  letI : Fintype K := Fintype.ofFinite _
  letI : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let V : FDRep ℂ T :=
    FDRep.induceFromSubgroup K thetaT.representation
  let F : ClassFunction T ℂ := ClassFunction.ofRepresentation V.ρ
  have hInvariant : ClassFunction.inertia K
      (thetaT : ClassFunction K ℂ) = ⊤ :=
    ClassFunction.inertia_inertiaSubgroupCharacter_eq_top H theta
  obtain ⟨psi₀, hpsi₀Restrict⟩ :=
    exists_irreducible_extension_of_normal_hall_abelian
      K thetaT hHall hInvariant
  have hF : F = ClassFunction.induce K
      (thetaT : ClassFunction K ℂ) := by
    dsimp only [F, V]
    exact
      (ClassFunction.ofRepresentation_induceFromSubgroup_general
        K thetaT.representation).trans
        (congrArg (ClassFunction.induce K)
          thetaT.ofRepresentation_representation)
  have hpsi₀Pair : characterPairing F
      (psi₀ : ClassFunction T ℂ) = 1 := by
    rw [hF, ClassFunction.frobeniusReciprocity K, hpsi₀Restrict]
    exact IrreducibleCharacter.characterPairing_self thetaT
  have hpsi₀ : psi₀ ∈ ClassFunction.inertiaConstituents H theta := by
    apply (ClassFunction.mem_constituents_iff F psi₀).2
    unfold IrreducibleCharacter.IsConstituent
    rw [hpsi₀Pair]
    exact one_ne_zero
  have hpsi₀Multiplicity : psi₀.multiplicity V = 1 := by
    apply Nat.cast_injective (R := ℂ)
    simpa using
      (psi₀.characterPairing_ofRepresentation_eq_multiplicity V).symm.trans
        hpsi₀Pair
  obtain ⟨e, _, hUniform, _, _, _⟩ :=
    ClassFunction.cfInd_central_inertia H theta
  change ∀ phi ∈ ClassFunction.inertiaConstituents H theta,
    phi.multiplicity V = e at hUniform
  have he : e = 1 :=
    (hUniform psi₀ hpsi₀).symm.trans hpsi₀Multiplicity
  have hRestrict :=
    ClassFunction.inertiaConstituent_restrict_eq_multiplicity_smul
      H theta psi hpsi
  simpa only [T, K, thetaT, V, hUniform psi hpsi, he,
    Nat.cast_one, one_smul] using hRestrict

/-- Ambient constituents lying over the same Hall-subgroup character have
equal restrictions to that subgroup. -/
private theorem inducedConstituentsRestrictEq
    {Q : Type} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    [IsMulCommutative
      ((ClassFunction.inertia H (theta : ClassFunction H ℂ)) ⧸
        H.subgroupOf
          (ClassFunction.inertia H (theta : ClassFunction H ℂ)))]
    (hHall : Nat.Coprime
      (Nat.card (H.subgroupOf
        (ClassFunction.inertia H (theta : ClassFunction H ℂ))))
      (H.subgroupOf
        (ClassFunction.inertia H (theta : ClassFunction H ℂ))).index)
    {i j : IrreducibleCharacter Q ℂ}
    (hi : i ∈ constituents
      (ClassFunction.induce H (theta : ClassFunction H ℂ)))
    (hj : j ∈ constituents
      (ClassFunction.induce H (theta : ClassFunction H ℂ))) :
    ClassFunction.restrict H (i : ClassFunction Q ℂ) =
      ClassFunction.restrict H (j : ClassFunction Q ℂ) := by
  let T := ClassFunction.inertia H (theta : ClassFunction H ℂ)
  let K := H.subgroupOf T
  have hiImage : i ∈ Finset.univ.image
      (ClassFunction.inertiaConstituentMap H theta) := by
    rw [← ClassFunction.inertiaConstituentMap_image H theta]
    exact hi
  have hjImage : j ∈ Finset.univ.image
      (ClassFunction.inertiaConstituentMap H theta) := by
    rw [← ClassFunction.inertiaConstituentMap_image H theta]
    exact hj
  obtain ⟨psi, _, hpsi⟩ := Finset.mem_image.mp hiImage
  obtain ⟨eta, _, heta⟩ := Finset.mem_image.mp hjImage
  have hpsiRestrict := inertiaConstituentRestrictEqCanonical
    H theta hHall psi.1 psi.2
  have hetaRestrict := inertiaConstituentRestrictEqCanonical
    H theta hHall eta.1 eta.2
  have hiInduced : (i : ClassFunction Q ℂ) =
      ClassFunction.induce T (psi.1 : ClassFunction T ℂ) := by
    rw [← hpsi]
    exact ClassFunction.coe_inertiaConstituentMap H theta psi
  have hjInduced : (j : ClassFunction Q ℂ) =
      ClassFunction.induce T (eta.1 : ClassFunction T ℂ) := by
    rw [← heta]
    exact ClassFunction.coe_inertiaConstituentMap H theta eta
  rw [hiInduced, hjInduced]
  ext h
  rw [ClassFunction.restrict_apply, ClassFunction.restrict_apply,
    ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula]
  congr 1
  apply Finset.sum_congr rfl
  intro x _
  have hxH : x⁻¹ * (h : Q) * x ∈ H := by
    simpa using (inferInstance : H.Normal).conj_mem
      (h : Q) h.property x⁻¹
  have hxT : x⁻¹ * (h : Q) * x ∈ T :=
    ClassFunction.le_inertia H _ hxH
  rw [dif_pos hxT, dif_pos hxT]
  dsimp only at hpsiRestrict hetaRestrict
  have hpsiValue := congrFun (congrArg Subtype.val hpsiRestrict)
    (⟨⟨x⁻¹ * (h : Q) * x, hxT⟩, hxH⟩ : K)
  have hetaValue := congrFun (congrArg Subtype.val hetaRestrict)
    (⟨⟨x⁻¹ * (h : Q) * x, hxT⟩, hxH⟩ : K)
  simpa only [ClassFunction.restrict_apply] using
    hpsiValue.trans hetaValue.symm

/-- Two constituents in the same type-I sequential block have equal
restrictions to the Fitting core. -/
private theorem constituentRestrictionsAgree
    {L : Subgroup G} (ctx : FTType1Context L)
    {chi : ClassFunction L ℂ}
    (hchi : chi ∈ FTType1SeqIndFamily L)
    {i j : IrreducibleCharacter L ℂ}
    (hi : i ∈ constituents chi) (hj : j ∈ constituents chi) :
    ClassFunction.restrict (FTType1FittingIn L)
        (i : ClassFunction L ℂ) =
      ClassFunction.restrict (FTType1FittingIn L)
        (j : ClassFunction L ℂ) := by
  let H := FTType1FittingIn L
  letI : H.Normal := Fcore_normal L
  obtain ⟨theta, hthetaNe, hchiEq⟩ :=
    (seqIndC1P (k := ℂ) H).mp hchi
  let T : Subgroup L :=
    ClassFunction.inertia H (theta : ClassFunction H ℂ)
  have hHT : H ≤ T := ClassFunction.le_inertia H _
  have hHall : Nat.Coprime
      (Nat.card (H.subgroupOf T)) (H.subgroupOf T).index := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hHT]
    change Nat.Coprime (Nat.card H) (H.relIndex T)
    exact (Fcore_Hall L).coprime_card_index.coprime_dvd_right
      (Subgroup.relIndex_dvd_index_of_le hHT)
  obtain ⟨U, hTypeI⟩ := (FTtypeP 1 L ctx.maxL).mpr ctx.type_one
  have hTypeF : of_typeF L U := hTypeI.1
  obtain ⟨U₁, hU₁⟩ := hTypeF.2.2.2.1
  have hHnormal : H.Normal := by
    simpa only [H] using hTypeF.2.2.1.2.2.1
  have hComplement : H.IsComplement' (U.subgroupOf L) := by
    simpa only [H] using hTypeF.2.2.1.2.2.2
  let eH : H ≃* Fitting_core L :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub L)
  let thetaF : IrreducibleCharacter (Fitting_core L) ℂ :=
    IrreducibleCharacter.comapMulEquiv eH.symm theta
  have hthetaFNe : thetaF ≠
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter (Fitting_core L) ℂ) := by
    intro htriv
    apply hthetaNe
    apply Subtype.ext
    ext h
    have hpoint := congrArg
      (fun eta : IrreducibleCharacter (Fitting_core L) ℂ ↦ eta (eH h))
      htriv
    simpa [thetaF, IrreducibleCharacter.comapMulEquiv_apply] using hpoint
  let thetaH : ClassFunction H ℂ :=
    ⟨fun h ↦ thetaF (eH h), by
      intro x h
      change thetaF (eH (x * h * x⁻¹)) = thetaF (eH h)
      simpa only [map_mul, map_inv] using
        ClassFunction.conj_apply
          (thetaF : ClassFunction (Fitting_core L) ℂ) (eH x) (eH h)⟩
  have hthetaH : thetaH = (theta : ClassFunction H ℂ) := by
    ext h
    simp [thetaH, thetaF, IrreducibleCharacter.comapMulEquiv_apply]
  have hComplementMap : ((U.subgroupOf L) ⊓ T).map L.subtype ≤ U₁ := by
    have hle :=
      (typeF_context L U hTypeF).inertia_le U₁ thetaF hU₁ hthetaFNe
    change ((U.subgroupOf L) ⊓
      ClassFunction.inertia H thetaH).map L.subtype ≤ U₁ at hle
    rw [hthetaH] at hle
    simpa only [T] using hle
  have hComplementCommutative :
      IsMulCommutative ((U.subgroupOf L) ⊓ T : Subgroup L) := by
    apply isMulCommutative_iff.mpr
    intro x y
    let x₁ : U₁ := ⟨((x : L) : G),
      hComplementMap (Subgroup.mem_map_of_mem L.subtype x.property)⟩
    let y₁ : U₁ := ⟨((y : L) : G),
      hComplementMap (Subgroup.mem_map_of_mem L.subtype y.property)⟩
    apply Subtype.ext
    apply Subtype.ext
    change ((x : L) : G) * ((y : L) : G) =
      ((y : L) : G) * ((x : L) : G)
    simpa [x₁, y₁] using congrArg Subtype.val
      (isMulCommutative_iff.mp hU₁.2.2.1 x₁ y₁)
  have hSemidirectT : IsInternalSemidirectProductIn H
      ((U.subgroupOf L) ⊓ T) T := by
    refine ⟨hHT, inf_le_right, ?_, ?_⟩
    · exact Subgroup.Normal.subgroupOf hHnormal T
    · exact complementSubgroupOfInfRight hComplement hHT
  letI : IsMulCommutative (T ⧸ H.subgroupOf T) :=
    FTType1InfrastructureInternal.semidirectQuotientCommutative
      hSemidirectT hComplementCommutative
  apply inducedConstituentsRestrictEq H theta hHall
  · simpa only [hchiEq] using hi
  · simpa only [hchiEq] using hj

/-- A difference inside one constituent block is confined to the part of
the full Feit--Thompson support not contained in its first layer. -/
private theorem constituentDifferenceSupported
    {L : Subgroup G} (ctx : FTType1Context L)
    {chi : ClassFunction L ℂ}
    (hchi : chi ∈ FTType1SeqIndFamily L)
    {i j : IrreducibleCharacter L ℂ}
    (hi : i ∈ constituents chi) (hj : j ∈ constituents chi) :
    (i : ClassFunction L ℂ) - (j : ClassFunction L ℂ) ∈
      ClassFunction.supportedOn
        {x : L | (x : G) ∈ FTsupport L \ FTsupport1 L} := by
  let H := FTType1FittingIn L
  have hrestrict := constituentRestrictionsAgree ctx hchi hi hj
  have hiSupport :=
    (FTtype1_seqInd_facts ctx chi hchi).constituent_supported i hi
  have hjSupport :=
    (FTtype1_seqInd_facts ctx chi hchi).constituent_supported j hj
  rw [ClassFunction.mem_supportedOn_iff]
  intro y hy
  by_cases hyH : y ∈ H
  · have hyEq := congrFun (congrArg Subtype.val hrestrict) ⟨y, hyH⟩
    simpa only [ClassFunction.restrict_apply,
      ClassFunction.sub_apply, sub_eq_zero] using hyEq
  · have hyOne : y ≠ 1 := by
      intro hyOne
      apply hyH
      simpa [hyOne, H]
    have hyNotFirst : (y : G) ∉ FTsupport1 L := by
      rw [FTsupp1_type1 L ctx.type_one]
      exact fun hyFirst ↦ hyH hyFirst.1
    have hyNotFull : (y : G) ∉ FTsupport L :=
      fun hyFull ↦ hy ⟨hyFull, hyNotFirst⟩
    have hiZero : (i : ClassFunction L ℂ) y = 0 := by
      apply ClassFunction.eq_zero_of_mem_supportedOn hiSupport
      rintro (rfl | hyFull)
      · exact hyOne rfl
      · exact hyNotFull hyFull
    have hjZero : (j : ClassFunction L ℂ) y = 0 := by
      apply ClassFunction.eq_zero_of_mem_supportedOn hjSupport
      rintro (rfl | hyFull)
      · exact hyOne rfl
      · exact hyNotFull hyFull
    simp only [ClassFunction.sub_apply, hiZero, hjZero, sub_zero]

/-- The Dade image of a difference inside one constituent block belongs to
the integral span of that block's canonical target family. -/
private theorem dadeConstituentDifferenceInTargetSpan
    {L : Subgroup G} (ctx : FTType1Context L)
    {chi : ClassFunction L ℂ}
    (hchi : chi ∈ FTType1SeqIndFamily L)
    {i j : IrreducibleCharacter L ℂ}
    (hi : i ∈ constituents chi) (hj : j ∈ constituents chi) :
    ctx.tau ((i : ClassFunction L ℂ) - (j : ClassFunction L ℂ)) ∈
      AddSubgroup.closure (ctx.R chi : Set (ClassFunction G ℂ)) := by
  have hiIndex : i ∈ FTType1IrrIndex L :=
    (FTtype1_irrP ctx i).mpr ⟨chi, hchi, hi⟩
  have hjIndex : j ∈ FTType1IrrIndex L :=
    (FTtype1_irrP ctx j).mpr ⟨chi, hchi, hj⟩
  have hiFamily : (i : ClassFunction L ℂ) ∈ FTType1IrrFamily L :=
    Finset.mem_image.mpr ⟨i, hiIndex, rfl⟩
  have hjFamily : (j : ClassFunction L ℂ) ∈ FTType1IrrFamily L :=
    Finset.mem_image.mpr ⟨j, hjIndex, rfl⟩
  obtain ⟨degree, hdegree⟩ :=
    (FTtype1_seqInd_facts ctx chi hchi).constituent_degrees_constant
  have hijDegree : (i : ClassFunction L ℂ) 1 =
      (j : ClassFunction L ℂ) 1 :=
    (hdegree i hi).trans (hdegree j hj).symm
  obtain ⟨S, hiS, hjS, hS, tauS, hcoherent⟩ :=
    pair_degree_coherence ctx.R1_subcoherent
      hiFamily hjFamily hijDegree
  obtain ⟨Ei, hEi, htauI⟩ :=
    mem_coherent_sum_subseq ctx.R1_subcoherent hS hcoherent hiS
  obtain ⟨Ej, hEj, htauJ⟩ :=
    mem_coherent_sum_subseq ctx.R1_subcoherent hS hcoherent hjS
  have hspan :
      (i : ClassFunction L ℂ) - (j : ClassFunction L ℂ) ∈
        AddSubgroup.closure S :=
    (AddSubgroup.closure S).sub_mem
      (AddSubgroup.subset_closure hiS)
      (AddSubgroup.subset_closure hjS)
  have hoff :
      (i : ClassFunction L ℂ) - (j : ClassFunction L ℂ) ∈
        ClassFunction.supportedOn (nonidentitySet L) :=
    subSupportedOnNonidentityOfEqAtOne _ _ hijDegree
  have hagree := hcoherent.agrees _ hspan hoff
  have hEiR : ∀ alpha ∈ Ei, alpha ∈ ctx.R chi := by
    intro alpha halpha
    rw [ctx.R_spec.flatten]
    exact Finset.mem_biUnion.mpr ⟨i, hi, hEi halpha⟩
  have hEjR : ∀ alpha ∈ Ej, alpha ∈ ctx.R chi := by
    intro alpha halpha
    rw [ctx.R_spec.flatten]
    exact Finset.mem_biUnion.mpr ⟨j, hj, hEj halpha⟩
  rw [← hagree, map_sub, htauI, htauJ]
  exact (AddSubgroup.closure _).sub_mem
    (by
      apply AddSubgroup.sum_mem
      intro alpha halpha
      exact AddSubgroup.subset_closure (hEiR alpha halpha))
    (by
      apply AddSubgroup.sum_mem
      intro alpha halpha
      exact AddSubgroup.subset_closure (hEjR alpha halpha))

/-- Orthogonality to the target block descends, by Dade induction and
Frobenius reciprocity, to differences of source constituents. -/
private theorem restrictedPairingConstituentDifference
    {L : Subgroup G} (ctx : FTType1Context L)
    (psi : ClassFunction G ℂ)
    (horth : FTType1OrthogonalToImages ctx psi)
    {chi : ClassFunction L ℂ}
    (hchi : chi ∈ FTType1SeqIndFamily L)
    {i j : IrreducibleCharacter L ℂ}
    (hi : i ∈ constituents chi) (hj : j ∈ constituents chi) :
    characterPairing (ClassFunction.restrict L psi)
      ((i : ClassFunction L ℂ) - (j : ClassFunction L ℂ)) = 0 := by
  let B : Set G := FTsupport L \ FTsupport1 L
  let d : ClassFunction L ℂ :=
    (i : ClassFunction L ℂ) - (j : ClassFunction L ℂ)
  have hdSupport : d ∈ ClassFunction.supportedOn
      {x : L | (x : G) ∈ B} :=
    constituentDifferenceSupported ctx hchi hi hj
  by_cases hB : B = ∅
  · have hdZero : d = 0 := by
      apply ClassFunction.ext
      intro x
      apply ClassFunction.eq_zero_of_mem_supportedOn hdSupport
      simpa [hB]
    change characterPairing (ClassFunction.restrict L psi) d = 0
    rw [hdZero]
    simp
  · obtain ⟨U, hTypeI⟩ := (FTtypeP 1 L ctx.maxL).mpr ctx.type_one
    have hdecomposition : IsInternalSemidirectProductIn
        (Fitting_core L) U L := hTypeI.1.2.2.1
    have hTI : IsNormalizedTI B (⊤ : Subgroup G) L :=
      (FTtypeI_II_facts 1 L U ctx.maxL ctx.type_one
        (by
          simpa [derivedSeriesWithin8, ← MonoidHom.range_eq_map,
            L.range_subtype] using hdecomposition)
        (by omega)).support_difference_normalizedTI hB
    have hBsub : B ⊆ FTsupport L := Set.diff_subset
    have hBnormal : L ≤ Subgroup.normalizer B :=
      fun x hx ↦ (hTI.2.1 hx).2
    have hDadeInduce : ctx.tau d = ClassFunction.induce L d := by
      calc
        ctx.tau d = constituentTopTargetMap
            (Dade (FT_Dade_hyp L ctx.maxL) d) := rfl
        _ = constituentTopTargetMap
            (restr_Dade (FT_Dade_hyp L ctx.maxL)
              hBsub hBnormal d) :=
          congrArg constituentTopTargetMap
            (restr_DadeE (FT_Dade_hyp L ctx.maxL)
              hBsub hBnormal d hdSupport).symm
        _ = constituentTopTargetMap
            (ClassFunction.induce (L.subgroupOf (⊤ : Subgroup G))
              (ClassFunction.toSubgroupOf L (⊤ : Subgroup G)
                le_top d)) := by
          apply congrArg constituentTopTargetMap
          simpa only [restr_Dade] using
            Dade_Ind
              (restr_Dade_hyp (FT_Dade_hyp L ctx.maxL)
                hBsub hBnormal)
              hTI d hdSupport
        _ = ClassFunction.induce (⊤ : Subgroup G)
            (ClassFunction.induce (L.subgroupOf (⊤ : Subgroup G))
              (ClassFunction.toSubgroupOf L (⊤ : Subgroup G)
                le_top d)) :=
          constituentTopTargetMap_eq_induceTop _
        _ = ClassFunction.induce L d :=
          ClassFunction.induce_trans L (⊤ : Subgroup G) le_top d
    have hdTarget : ctx.tau d ∈
        AddSubgroup.closure (ctx.R chi : Set (ClassFunction G ℂ)) := by
      simpa only [d] using
        dadeConstituentDifferenceInTargetSpan ctx hchi hi hj
    have hpairClosure : ∀ z ∈
        AddSubgroup.closure (ctx.R chi : Set (ClassFunction G ℂ)),
        characterPairing psi z = 0 := by
      intro z hz
      induction hz using AddSubgroup.closure_induction with
      | mem alpha halpha => exact horth chi hchi alpha halpha
      | zero => simp
      | add alpha beta _ _ hAlpha hBeta =>
          rw [characterPairing_add_right, hAlpha, hBeta, add_zero]
      | neg alpha _ hAlpha =>
          rw [← neg_one_smul ℂ alpha,
            characterPairing_smul_right, hAlpha, mul_zero]
    have hpsiDade : characterPairing psi (ctx.tau d) = 0 :=
      hpairClosure _ hdTarget
    rw [hDadeInduce, characterPairing_comm,
      ClassFunction.frobeniusReciprocity, characterPairing_comm] at hpsiDade
    exact hpsiDade

/-- The Fourier summand indexed by type-I irreducibles is supported on the
Fitting core. -/
private theorem indexedFourierPartSupported
    {L : Subgroup G} (ctx : FTType1Context L)
    (psi : ClassFunction G ℂ)
    (horth : FTType1OrthogonalToImages ctx psi) :
    (∑ i : {i : IrreducibleCharacter L ℂ //
        i ∈ FTType1IrrIndex L},
      characterPairing (i.1 : ClassFunction L ℂ)
          (ClassFunction.restrict L psi) •
        (i.1 : ClassFunction L ℂ)) ∈
      ClassFunction.supportedOn (FTType1FittingIn L : Set L) := by
  let rpsi := ClassFunction.restrict L psi
  let term : IrreducibleCharacter L ℂ → ClassFunction L ℂ :=
    fun i ↦ characterPairing (i : ClassFunction L ℂ) rpsi •
      (i : ClassFunction L ℂ)
  have hcoefficient
      {chi : ClassFunction L ℂ}
      (hchi : chi ∈ FTType1SeqIndFamily L)
      {i j : IrreducibleCharacter L ℂ}
      (hi : i ∈ constituents chi) (hj : j ∈ constituents chi) :
      characterPairing (i : ClassFunction L ℂ) rpsi =
        characterPairing (j : ClassFunction L ℂ) rpsi := by
    have hp := restrictedPairingConstituentDifference
      ctx psi horth hchi hi hj
    rw [FTType1InfrastructureInternal.pairingSubRight] at hp
    have hp' := sub_eq_zero.mp hp
    rw [characterPairing_comm i rpsi,
      characterPairing_comm j rpsi]
    exact hp'
  let s := FTType1IrrIndex L
  have hsource :
      (∑ i : {i : IrreducibleCharacter L ℂ //
          i ∈ FTType1IrrIndex L}, term i.1) =
        ∑ i : (s : Set (IrreducibleCharacter L ℂ)), term i.1 := by
    calc
      (∑ i : {i : IrreducibleCharacter L ℂ //
          i ∈ FTType1IrrIndex L}, term i.1) =
          s.sum term := by
        symm
        exact Finset.sum_subtype s (fun _ ↦ Iff.rfl) term
      _ = ∑ i : (s : Set (IrreducibleCharacter L ℂ)), term i.1 :=
        finsetSum_eq_sumCoeSubtype s term
  change
    (∑ i : {i : IrreducibleCharacter L ℂ //
        i ∈ FTType1IrrIndex L}, term i.1) ∈
      ClassFunction.supportedOn (FTType1FittingIn L : Set L)
  let rawS : Fintype (s : Set (IrreducibleCharacter L ℂ)) :=
    Subtype.fintype _
  have hraw :
      (@Finset.univ (s : Set (IrreducibleCharacter L ℂ))
          (FinsetCoe.fintype s)).sum (fun i ↦ term i.1) =
        (@Finset.univ (s : Set (IrreducibleCharacter L ℂ)) rawS).sum
          (fun i ↦ term i.1) :=
    fintypeSum_eq (FinsetCoe.fintype s) rawS _
  have hpartition := (FTtype1_irr_partition ctx).sum_subtype term
  rw [fintypeSum_eq _ rawS _] at hpartition
  have hdecomposition := hsource.trans (hraw.trans hpartition)
  rw [hdecomposition]
  apply Submodule.sum_mem
  intro A _
  obtain ⟨chi, hchi, hA⟩ := A.property
  have hAne : (A : Set (IrreducibleCharacter L ℂ)) ≠ ∅ := by
    intro hzero
    exact (FTtype1_irr_partition ctx).2.2 (hzero ▸ A.property)
  obtain ⟨j, hj⟩ := Set.nonempty_iff_ne_empty.mpr hAne
  have hjChi : j ∈ constituents chi := by
    exact Finset.mem_coe.mp (hA ▸ hj)
  have hsum : (∑ i : A, term i.1) =
      characterPairing (j : ClassFunction L ℂ) rpsi • chi := by
    calc
      (∑ i : A, term i.1) =
          ∑ i : A,
            characterPairing (j : ClassFunction L ℂ) rpsi •
              (i.1 : ClassFunction L ℂ) := by
        apply Finset.sum_congr rfl
        intro i _
        dsimp only [term]
        rw [hcoefficient hchi
          (Finset.mem_coe.mp (hA ▸ i.property)) hjChi]
      _ = characterPairing (j : ClassFunction L ℂ) rpsi •
          ∑ i : A, (i.1 : ClassFunction L ℂ) := by
        rw [Finset.smul_sum]
      _ = characterPairing (j : ClassFunction L ℂ) rpsi • chi := by
        congr 1
        calc
          (∑ i : A, (i.1 : ClassFunction L ℂ)) =
              ∑ i : (constituents chi : Set
                (IrreducibleCharacter L ℂ)),
                (i.1 : ClassFunction L ℂ) := by
            apply Fintype.sum_equiv (Equiv.setCongr hA)
            intro i
            rfl
          _ = (constituents chi).sum
              (fun i ↦ (i : ClassFunction L ℂ)) :=
            (finsetSum_eq_sumCoeSubtype (constituents chi)
              (fun i ↦ (i : ClassFunction L ℂ))).symm
          _ = chi := (FTtype1_seqInd_facts ctx chi hchi).constituent_sum.symm
  rw [hsum]
  have hchiSupport : chi ∈
      ClassFunction.supportedOn (FTType1FittingIn L : Set L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    exact seqInd_on (FTType1FittingIn L) hchi
  exact (ClassFunction.supportedOn
    (FTType1FittingIn L : Set L)).smul_mem _ hchiSupport

/-- `PFsection12.v: FTtype1_ortho_constant`, Peterfalvi (12.4). -/
theorem FTtype1_ortho_constant
    {L : Subgroup G} (ctx : FTType1Context L)
    (psi : ClassFunction G ℂ) (x : G)
    (horth : FTType1OrthogonalToImages ctx psi)
    (hxL : x ∈ L) (hxH : x ∉ Fitting_core L) :
    ∀ y : G,
      y ∈ ({x} : Set G) * (Fitting_core L : Set G) →
        psi y = psi x := by
  classical
  intro y hy
  rcases Set.mem_mul.mp hy with ⟨x', hx', h, hh, hxy⟩
  have hx'Eq : x' = x := Set.mem_singleton_iff.mp hx'
  subst x'
  subst y
  let H := FTType1FittingIn L
  let xL : L := ⟨x, hxL⟩
  let hL : L := ⟨h, Fcore_sub L hh⟩
  let yL : L := xL * hL
  let rpsi : ClassFunction L ℂ := ClassFunction.restrict L psi
  let term : IrreducibleCharacter L ℂ → ClassFunction L ℂ :=
    fun i ↦ characterPairing (i : ClassFunction L ℂ) rpsi •
      (i : ClassFunction L ℂ)
  let p : ClassFunction L ℂ :=
    (FTType1IrrIndex L).sum term
  let q : ClassFunction L ℂ :=
    ((Finset.univ : Finset (IrreducibleCharacter L ℂ)).filter
        (fun i ↦ i ∉ FTType1IrrIndex L)).sum term
  have hpEq : p =
      ∑ i : {i : IrreducibleCharacter L ℂ //
        i ∈ FTType1IrrIndex L}, term i.1 := by
    dsimp only [p]
    rw [Finset.sum_subtype (FTType1IrrIndex L) (fun _ ↦ Iff.rfl)]
  have hpSupport : p ∈ ClassFunction.supportedOn (H : Set L) := by
    rw [hpEq]
    exact indexedFourierPartSupported ctx psi horth
  have hxNotH : xL ∉ H := hxH
  have hyNotH : yL ∉ H := by
    intro hyH
    apply hxNotH
    have hhH : hL ∈ H := hh
    have hxRecover : xL = yL * hL⁻¹ := by
      dsimp only [yL]
      group
    rw [hxRecover]
    exact H.mul_mem hyH (H.inv_mem hhH)
  have hpX : p xL = 0 :=
    ClassFunction.eq_zero_of_mem_supportedOn hpSupport hxNotH
  have hpY : p yL = 0 :=
    ClassFunction.eq_zero_of_mem_supportedOn hpSupport hyNotH
  have houtside (i : IrreducibleCharacter L ℂ)
      (hi : i ∉ FTType1IrrIndex L) :
      term i yL = term i xL := by
    have hkernel : H ≤ ClassFunction.translationKernel
        (i : ClassFunction L ℂ) := by
      rw [FTType1IrrIndex, mem_Iirr_kerD] at hi
      exact Classical.byContradiction
        (fun hnot ↦ hi ⟨bot_le, hnot⟩)
    have hhKernel : hL ∈ ClassFunction.translationKernel
        (i : ClassFunction L ℂ) := hkernel hh
    have hleft : (i : ClassFunction L ℂ) (hL * xL) =
        (i : ClassFunction L ℂ) xL := hhKernel xL
    have hright : (i : ClassFunction L ℂ) yL =
        (i : ClassFunction L ℂ) (hL * xL) := by
      calc
        (i : ClassFunction L ℂ) yL =
            (i : ClassFunction L ℂ)
              (xL * (hL * xL) * xL⁻¹) := by
          congr 1
          dsimp only [yL]
          group
        _ = (i : ClassFunction L ℂ) (hL * xL) :=
          ClassFunction.conj_apply (i : ClassFunction L ℂ)
            xL (hL * xL)
    dsimp only [term]
    simp only [ClassFunction.smul_apply, smul_eq_mul]
    rw [hright, hleft]
  have hqYX : q yL = q xL := by
    dsimp only [q]
    simp only [ClassFunction.finset_sum_apply]
    apply Finset.sum_congr rfl
    intro i hi
    exact houtside i (Finset.mem_filter.mp hi).2
  have hsplit :
      (∑ i : IrreducibleCharacter L ℂ, term i) = p + q := by
    have hfilter :
        (Finset.univ : Finset (IrreducibleCharacter L ℂ)).filter
            (fun i ↦ i ∈ FTType1IrrIndex L) =
          FTType1IrrIndex L := by
      ext i
      simp
    dsimp only [p, q]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset (IrreducibleCharacter L ℂ)))
      (p := fun i ↦ i ∈ FTType1IrrIndex L)]
    rw [hfilter]
  have hexpansion : p + q = rpsi := by
    rw [← hsplit]
    exact irreducibleCharacterExpansion_eq rpsi
  calc
    psi (x * h) = rpsi yL := by rfl
    _ = (p + q) yL :=
      congrFun (congrArg Subtype.val hexpansion.symm) yL
    _ = q yL := by
      simp only [ClassFunction.add_apply, hpY, zero_add]
    _ = q xL := hqYX
    _ = (p + q) xL := by
      simp only [ClassFunction.add_apply, hpX, zero_add]
    _ = rpsi xL := congrFun (congrArg Subtype.val hexpansion) xL
    _ = psi x := by rfl

/-! ## Clifford blocks above the derived subgroup -/

/-- Restricting an irreducible character to a subgroup produces at least
one irreducible constituent. -/
private theorem existsConstituentAfterRestrict
    {Q : Type} [Group Q] [Fintype Q]
    (H : Subgroup Q) [Fintype H]
    (chi : IrreducibleCharacter Q ℂ) :
    ∃ theta : IrreducibleCharacter H ℂ,
      theta.IsConstituent
        (ClassFunction.restrict H (chi : ClassFunction Q ℂ)) := by
  let V : FDRep ℂ H :=
    FDRep.restrictToSubgroup H chi.representation
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  letI : Nontrivial V :=
    inferInstanceAs (Nontrivial chi.representation)
  obtain ⟨theta, htheta⟩ :=
    ClassFunction.exists_irreducible_constituent_of_nontrivial V
  refine ⟨theta, ?_⟩
  rw [← chi.ofRepresentation_representation,
    ← FDRep.ofRepresentation_restrictToSubgroup]
  exact htheta

/-- Induction from the commutator subgroup gives the Clifford partition of
the irreducible characters of a normal subgroup. -/
private theorem commutatorInductionConstituentPartition
    {Q : Type} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal] :
    let D := _root_.commutator H
    IsSetPartition
      {A : Set (IrreducibleCharacter H ℂ) |
        ∃ theta : IrreducibleCharacter D ℂ,
          A = (constituents
            (ClassFunction.induce D (theta : ClassFunction D ℂ)) :
              Set (IrreducibleCharacter H ℂ))}
      Set.univ := by
  let D : Subgroup H := _root_.commutator H
  let P : Set (Set (IrreducibleCharacter H ℂ)) :=
    {A | ∃ theta : IrreducibleCharacter D ℂ,
      A = (constituents
        (ClassFunction.induce D (theta : ClassFunction D ℂ)) :
          Set (IrreducibleCharacter H ℂ))}
  letI : D.Normal := inferInstance
  letI : Invertible (Nat.card D : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  refine ⟨?_, ?_, ?_⟩
  · ext chi
    simp only [Set.mem_sUnion, Set.mem_univ, iff_true]
    obtain ⟨theta, htheta⟩ := existsConstituentAfterRestrict D chi
    refine ⟨(constituents
      (ClassFunction.induce D (theta : ClassFunction D ℂ)) :
        Set (IrreducibleCharacter H ℂ)), ⟨theta, rfl⟩, ?_⟩
    change chi ∈ constituents
      (ClassFunction.induce D (theta : ClassFunction D ℂ))
    exact (ClassFunction.mem_constituents_iff _ _).mpr
      ((theta.isConstituent_restrict_iff_induce D chi).mp htheta)
  · intro A hA B hB hne
    obtain ⟨theta, rfl⟩ := hA
    obtain ⟨eta, rfl⟩ := hB
    have hblocksNe :
        (constituents
          (ClassFunction.induce D (theta : ClassFunction D ℂ)) :
            Set (IrreducibleCharacter H ℂ)) ≠
        (constituents
          (ClassFunction.induce D (eta : ClassFunction D ℂ)) :
            Set (IrreducibleCharacter H ℂ)) := hne
    rcases ClassFunction.cfclass_Ind_cases D theta eta with heq | horth
    · exact (hblocksNe
        (congrArg
          (fun s : Finset (IrreducibleCharacter H ℂ) ↦
            (s : Set (IrreducibleCharacter H ℂ)))
          (congrArg constituents heq.2))).elim
    · let V : FDRep ℂ H :=
        FDRep.induceFromSubgroup D theta.representation
      let W : FDRep ℂ H :=
        FDRep.induceFromSubgroup D eta.representation
      have hV : ClassFunction.ofRepresentation V.ρ =
          ClassFunction.induce D (theta : ClassFunction D ℂ) := by
        dsimp only [V]
        exact
          (ClassFunction.ofRepresentation_induceFromSubgroup_general
            D theta.representation).trans
          (congrArg (ClassFunction.induce D)
            theta.ofRepresentation_representation)
      have hW : ClassFunction.ofRepresentation W.ρ =
          ClassFunction.induce D (eta : ClassFunction D ℂ) := by
        dsimp only [W]
        exact
          (ClassFunction.ofRepresentation_induceFromSubgroup_general
            D eta.representation).trans
          (congrArg (ClassFunction.induce D)
            eta.ofRepresentation_representation)
      change Disjoint
        (↑(constituents
          (ClassFunction.induce D (theta : ClassFunction D ℂ))) :
            Set (IrreducibleCharacter H ℂ))
        (↑(constituents
          (ClassFunction.induce D (eta : ClassFunction D ℂ))) :
            Set (IrreducibleCharacter H ℂ))
      simpa only [hV, hW] using
        (FTType1InfrastructureInternal.constituentsDisjointOfPairingEqZero
          V W (by simpa only [hV, hW] using horth.2))
  · rintro ⟨theta, hblockEmpty⟩
    have hconstituentsEmpty :
        constituents
          (ClassFunction.induce D (theta : ClassFunction D ℂ)) = ∅ := by
      apply Finset.coe_injective
      simpa only [D, Finset.coe_empty] using hblockEmpty.symm
    have hsum := ClassFunction.sum_constituents_eq
      (ClassFunction.induce D (theta : ClassFunction D ℂ))
    rw [hconstituentsEmpty] at hsum
    simp only [Finset.sum_empty] at hsum
    have hone := congrFun (congrArg Subtype.val hsum.symm) (1 : H)
    rw [ClassFunction.induce_one] at hone
    have hindex : (D.index : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr D.index_ne_zero_of_finite
    letI : CategoryTheory.Simple theta.representation :=
      theta.representation_simple
    letI : Nontrivial theta.representation := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply CategoryTheory.id_nonzero theta.representation
      apply CategoryTheory.ConcreteCategory.hom_ext
      intro z
      exact Subsingleton.elim _ _
    have hthetaDegree : theta 1 ≠ 0 := by
      rw [IrreducibleCharacter.apply_one_eq_finrank]
      exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    exact (mul_ne_zero hindex hthetaDegree) hone

/-- Equal-degree sequential-induction pairing relations make a class
function constant outside the commutator subgroup. -/
private theorem constantOnCommutatorComplementOfSeqIndPairing
    {Q : Type} [Group Q] [Fintype Q]
    (H : Subgroup Q) [H.Normal]
    (f : ClassFunction Q ℂ)
    (hpair : ∀ xi₁ ∈ seqIndD (k := ℂ) H ⊤ ⊥,
      ∀ xi₂ ∈ seqIndD (k := ℂ) H ⊤ ⊥,
        xi₁ 1 = xi₂ 1 →
          characterPairing f (xi₁ - xi₂) = 0) :
    ∀ x : H, x ∉ _root_.commutator H →
      ∀ y : H, y ∉ _root_.commutator H →
        f (x : Q) = f (y : Q) := by
  classical
  let D : Subgroup H := _root_.commutator H
  letI : D.Normal := inferInstance
  let rH : ClassFunction H ℂ := ClassFunction.restrict H f
  let coeff : IrreducibleCharacter H ℂ → ℂ :=
    fun chi ↦ characterPairing (chi : ClassFunction H ℂ) rH
  let term : IrreducibleCharacter H ℂ → ClassFunction H ℂ :=
    fun chi ↦ coeff chi • (chi : ClassFunction H ℂ)
  let P : Set (Set (IrreducibleCharacter H ℂ)) :=
    {A | ∃ theta : IrreducibleCharacter D ℂ,
      A = (constituents
        (ClassFunction.induce D (theta : ClassFunction D ℂ)) :
          Set (IrreducibleCharacter H ℂ))}
  have hpartition : IsSetPartition P Set.univ := by
    simpa only [D, P] using
      (commutatorInductionConstituentPartition H)
  let rawUniv : Fintype
      (Set.univ : Set (IrreducibleCharacter H ℂ)) :=
    Subtype.fintype _
  let rawP : Fintype P := Subtype.fintype _
  let rawBlock : (A : P) →
      Fintype (A : Set (IrreducibleCharacter H ℂ)) :=
    fun A ↦ Subtype.fintype _
  have hfourier :
      irreducibleCharacterExpansion rH =
        (@Finset.univ P rawP).sum (fun A ↦
          (@Finset.univ (A : Set (IrreducibleCharacter H ℂ))
            (rawBlock A)).sum (fun chi ↦ term chi.1)) := by
    have huniv :
        (∑ chi : (Set.univ : Set (IrreducibleCharacter H ℂ)),
          term chi.1) =
            ∑ chi : IrreducibleCharacter H ℂ, term chi := by
      apply Fintype.sum_equiv (Equiv.Set.univ _)
      intro chi
      rfl
    have hrawUniv :
        (∑ chi : (Set.univ : Set (IrreducibleCharacter H ℂ)),
          term chi.1) =
          (@Finset.univ
            (Set.univ : Set (IrreducibleCharacter H ℂ)) rawUniv).sum
              (fun chi ↦ term chi.1) :=
      fintypeSum_eq _ rawUniv _
    have hpartitionSum := hpartition.sum_subtype term
    rw [fintypeSum_eq _ rawUniv _] at hpartitionSum
    rw [fintypeSum_eq _ rawP _] at hpartitionSum
    simp_rw [fintypeSum_eq _ (rawBlock _) _] at hpartitionSum
    calc
      irreducibleCharacterExpansion rH =
          ∑ chi : IrreducibleCharacter H ℂ, term chi := by
        rw [irreducibleCharacterExpansion]
      _ = ∑ chi : (Set.univ : Set (IrreducibleCharacter H ℂ)),
          term chi.1 := huniv.symm
      _ = (@Finset.univ
            (Set.univ : Set (IrreducibleCharacter H ℂ)) rawUniv).sum
          (fun chi ↦ term chi.1) := hrawUniv
      _ = (@Finset.univ P rawP).sum (fun A ↦
          (@Finset.univ (A : Set (IrreducibleCharacter H ℂ))
            (rawBlock A)).sum (fun chi ↦ term chi.1)) := by
        exact hpartitionSum
  intro x hx y hy
  change rH x = rH y
  rw [← irreducibleCharacterExpansion_eq rH,
    hfourier]
  simp only [ClassFunction.finset_sum_apply]
  apply Finset.sum_congr rfl
  intro A _
  obtain ⟨theta, hA⟩ := A.property
  let s : Finset (IrreducibleCharacter H ℂ) :=
    constituents
      (ClassFunction.induce D (theta : ClassFunction D ℂ))
  let Btheta : Set (IrreducibleCharacter H ℂ) :=
    {chi | chi ∈ s}
  let Atheta : P :=
    ⟨Btheta, ⟨theta, by ext chi; simp [Btheta, s]⟩⟩
  have hAA : A = Atheta := by
    apply Subtype.ext
    calc
      (A : Set (IrreducibleCharacter H ℂ)) =
          (constituents
            (ClassFunction.induce D (theta : ClassFunction D ℂ)) : Set _) :=
        hA
      _ = Btheta := by ext chi; simp [Btheta, s]
  rw [hAA]
  letI : Fintype (Atheta : Set (IrreducibleCharacter H ℂ)) :=
    rawBlock Atheta
  let T : Subgroup H :=
    ClassFunction.inertia D (theta : ClassFunction D ℂ)
  have hDT : D ≤ T := ClassFunction.le_inertia D _
  letI : IsMulCommutative (T ⧸ D.subgroupOf T) := by
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    intro z hz
    have hzMap : (z : H) ∈ (_root_.commutator T).map T.subtype :=
      Subgroup.mem_map_of_mem T.subtype hz
    have hmap : (_root_.commutator T).map T.subtype ≤ D := by
      rw [map_commutator_eq, T.range_subtype]
      exact Subgroup.commutator_mono le_top le_top
    exact hmap hzMap
  obtain ⟨e, he, _hmult, hInd, _hcard, hdegree⟩ :=
    ClassFunction.cfInd_central_inertia D theta
  change ClassFunction.induce D (theta : ClassFunction D ℂ) =
    (e : ℂ) • s.sum (fun chi ↦ (chi : ClassFunction H ℂ)) at hInd
  have hdegreeS : ∀ chi ∈ s,
      chi 1 = (T.index : ℂ) * (e : ℂ) * theta 1 := by
    intro chi hchi
    simpa only [s, T] using hdegree chi hchi
  have hIndMem :
      ClassFunction.induce D (theta : ClassFunction D ℂ) ∈
        seqInd D (Finset.univ : Finset (IrreducibleCharacter D ℂ)) :=
    seqIndP.mpr ⟨theta, Finset.mem_univ theta, rfl⟩
  have hIndSupport := seqInd_on D hIndMem
  have hIndX :
      ClassFunction.induce D (theta : ClassFunction D ℂ) x = 0 :=
    ClassFunction.eq_zero_of_mem_supportedOn hIndSupport hx
  have hIndY :
      ClassFunction.induce D (theta : ClassFunction D ℂ) y = 0 :=
    ClassFunction.eq_zero_of_mem_supportedOn hIndSupport hy
  have heCast : (e : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr he.ne'
  have hsumXDouble :
      s.sum (fun chi ↦ (chi : ClassFunction H ℂ) x) = 0 := by
    have heval := congrFun (congrArg Subtype.val hInd) x
    simp only [ClassFunction.smul_apply, ClassFunction.finset_sum_apply,
      smul_eq_mul, hIndX] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left heCast
  have hsumYDouble :
      s.sum (fun chi ↦ (chi : ClassFunction H ℂ) y) = 0 := by
    have heval := congrFun (congrArg Subtype.val hInd) y
    simp only [ClassFunction.smul_apply, ClassFunction.finset_sum_apply,
      smul_eq_mul, hIndY] at heval
    exact (mul_eq_zero.mp heval.symm).resolve_left heCast
  have hsumX :
      (∑ chi : (Atheta : Set (IrreducibleCharacter H ℂ)),
        (chi.1 : ClassFunction H ℂ) x) = 0 := by
    calc
      (∑ chi : (Atheta : Set (IrreducibleCharacter H ℂ)),
          (chi.1 : ClassFunction H ℂ) x) =
          ∑ chi : (s : Set (IrreducibleCharacter H ℂ)),
            (chi.1 : ClassFunction H ℂ) x := by
        exact fintypeSum_eq _ _ _
      _ = s.sum (fun chi ↦ (chi : ClassFunction H ℂ) x) :=
        (finsetSum_eq_sumCoeSubtype s
          (fun chi ↦ (chi : ClassFunction H ℂ) x)).symm
      _ = 0 := hsumXDouble
  have hsumY :
      (∑ chi : (Atheta : Set (IrreducibleCharacter H ℂ)),
        (chi.1 : ClassFunction H ℂ) y) = 0 := by
    calc
      (∑ chi : (Atheta : Set (IrreducibleCharacter H ℂ)),
          (chi.1 : ClassFunction H ℂ) y) =
          ∑ chi : (s : Set (IrreducibleCharacter H ℂ)),
            (chi.1 : ClassFunction H ℂ) y := by
        exact fintypeSum_eq _ _ _
      _ = s.sum (fun chi ↦ (chi : ClassFunction H ℂ) y) :=
        (finsetSum_eq_sumCoeSubtype s
          (fun chi ↦ (chi : ClassFunction H ℂ) y)).symm
      _ = 0 := hsumYDouble
  by_cases hnontrivial : ∃ chi : IrreducibleCharacter H ℂ,
      chi ∈ s ∧
        chi ≠ (IrreducibleCharacter.trivial :
          IrreducibleCharacter H ℂ)
  · obtain ⟨eta, heta, hetaNe⟩ := hnontrivial
    have hcoeff (chi : IrreducibleCharacter H ℂ)
        (hchi : chi ∈ s)
        (hchiNe : chi ≠ (IrreducibleCharacter.trivial :
          IrreducibleCharacter H ℂ)) :
        coeff chi = coeff eta := by
      let xiChi : ClassFunction Q ℂ :=
        ClassFunction.induce H (chi : ClassFunction H ℂ)
      let xiEta : ClassFunction Q ℂ :=
        ClassFunction.induce H (eta : ClassFunction H ℂ)
      have hxiChi : xiChi ∈ seqIndD (k := ℂ) H ⊤ ⊥ := by
        apply (seqIndC1P (k := ℂ) H).mpr
        exact ⟨chi, hchiNe, rfl⟩
      have hxiEta : xiEta ∈ seqIndD (k := ℂ) H ⊤ ⊥ := by
        apply (seqIndC1P (k := ℂ) H).mpr
        exact ⟨eta, hetaNe, rfl⟩
      have hdegreeEq : xiChi 1 = xiEta 1 := by
        dsimp only [xiChi, xiEta]
        rw [ClassFunction.induce_one, ClassFunction.induce_one,
          hdegreeS chi hchi, hdegreeS eta heta]
      have hp := hpair xiChi hxiChi xiEta hxiEta hdegreeEq
      rw [characterPairing_comm f (xiChi - xiEta),
        FTType1InfrastructureInternal.pairingSubLeft,
        ClassFunction.frobeniusReciprocity,
        ClassFunction.frobeniusReciprocity] at hp
      exact sub_eq_zero.mp (by simpa only [coeff, rH] using hp)
    simp only [term, ClassFunction.smul_apply, smul_eq_mul]
    rw [← sub_eq_zero, ← Finset.sum_sub_distrib]
    calc
      (∑ chi : (Atheta : Set (IrreducibleCharacter H ℂ)),
        (coeff chi.1 * (chi.1 : ClassFunction H ℂ) x -
          coeff chi.1 * (chi.1 : ClassFunction H ℂ) y)) =
          coeff eta *
            ∑ chi : (Atheta : Set (IrreducibleCharacter H ℂ)),
              ((chi.1 : ClassFunction H ℂ) x -
                (chi.1 : ClassFunction H ℂ) y) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro chi _
        by_cases hchiOne : chi.1 =
            (IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ)
        · simp [hchiOne]
        · rw [hcoeff chi.1
            (by simpa only [Atheta, Btheta, Set.mem_setOf_eq]
              using chi.property) hchiOne]
          ring
      _ = 0 := by
        rw [Finset.sum_sub_distrib, hsumX, hsumY, sub_self, mul_zero]
  · simp only [term, ClassFunction.smul_apply, smul_eq_mul]
    apply Finset.sum_congr rfl
    intro chi _
    have hchiOne : chi.1 =
        (IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) := by
      by_contra hne
      exact hnontrivial
        ⟨chi.1, by simpa only [Atheta, Btheta, Set.mem_setOf_eq]
          using chi.property, hne⟩
    simp [hchiOne]

/-! ## Peterfalvi (12.5) -/

/-- An equal-degree difference of two type-I sequential characters is
supported on the nonidentity part of the Fitting core. -/
private theorem seqIndDifferenceSupportedOnFittingCore
    {L : Subgroup G}
    {xi₁ xi₂ : ClassFunction L ℂ}
    (hxi₁ : xi₁ ∈ FTType1SeqIndFamily L)
    (hxi₂ : xi₂ ∈ FTType1SeqIndFamily L)
    (hdegree : xi₁ 1 = xi₂ 1) :
    xi₁ - xi₂ ∈ ClassFunction.supportedOn
      {x : L | (x : G) ∈ subgroupNonidentity (Fitting_core L)} := by
  let H := FTType1FittingIn L
  have hxi₁On := seqInd_on H hxi₁
  have hxi₂On := seqInd_on H hxi₂
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  by_cases hxH : x ∈ H
  · have hxOne : x = 1 := by
      by_contra hxOne
      apply hx
      exact ⟨hxH, fun hxAmbientOne ↦
        hxOne (Subtype.ext hxAmbientOne)⟩
    subst x
    simp only [ClassFunction.sub_apply, hdegree, sub_self]
  · have hxi₁Zero :=
      ClassFunction.eq_zero_of_mem_supportedOn hxi₁On hxH
    have hxi₂Zero :=
      ClassFunction.eq_zero_of_mem_supportedOn hxi₂On hxH
    simp only [ClassFunction.sub_apply, hxi₁Zero, hxi₂Zero, sub_zero]

/-- Orthogonality to the canonical target families transfers, by
inverse-Dade reciprocity, to equal-degree source differences. -/
private theorem inverseDadeSourceDifferencePairing
    {L : Subgroup G} (ctx : FTType1Context L)
    (psi : ClassFunction G ℂ)
    (horth : FTType1OrthogonalToImages ctx psi)
    {xi₁ xi₂ : ClassFunction L ℂ}
    (hxi₁ : xi₁ ∈ FTType1SeqIndFamily L)
    (hxi₂ : xi₂ ∈ FTType1SeqIndFamily L)
    (hdegree : xi₁ 1 = xi₂ 1) :
    characterPairing (ctx.rho psi) (xi₁ - xi₂) = 0 := by
  classical
  let ddF := FT_DadeF_hyp L ctx.maxL
  let rpsi : ClassFunction L ℂ := ctx.rho psi
  obtain ⟨S, hxi₁S, hxi₂S, hS, tauS, hcoherent⟩ :=
    pair_degree_coherence
      ctx.R_spec.subcoherent_family hxi₁ hxi₂ hdegree
  have hpsiTau (xi : ClassFunction L ℂ) (hxi : xi ∈ S) :
      characterPairing psi (tauS xi) = 0 := by
    obtain ⟨E, hER, htau⟩ :=
      mem_coherent_sum_subseq
        ctx.R_spec.subcoherent_family hS hcoherent hxi
    rw [htau,
      FTType1InfrastructureInternal.pairingFinsetSumRight]
    exact Finset.sum_eq_zero fun alpha halpha ↦
      horth xi (hS.1 hxi) alpha (hER halpha)
  let alpha : ClassFunction L ℂ := xi₁ - xi₂
  have halphaSpan : alpha ∈ AddSubgroup.closure S :=
    (AddSubgroup.closure S).sub_mem
      (AddSubgroup.subset_closure hxi₁S)
      (AddSubgroup.subset_closure hxi₂S)
  have halphaOff : alpha ∈
      ClassFunction.supportedOn (nonidentitySet L) :=
    subSupportedOnNonidentityOfEqAtOne xi₁ xi₂ hdegree
  have halphaF : alpha ∈ ClassFunction.supportedOn
      {x : L | (x : G) ∈ subgroupNonidentity (Fitting_core L)} :=
    seqIndDifferenceSupportedOnFittingCore hxi₁ hxi₂ hdegree
  have halphaFull : alpha ∈ ClassFunction.supportedOn
      {x : L | (x : G) ∈ FTsupport L} := by
    rw [ClassFunction.mem_supportedOn_iff] at halphaF ⊢
    intro x hx
    apply halphaF x
    intro hxF
    exact hx (Fcore_sub_FTsupp ctx.maxL hxF)
  have hagree : tauS alpha = ctx.tau alpha :=
    hcoherent.agrees alpha halphaSpan halphaOff
  have hpsiDifference : characterPairing psi (tauS alpha) = 0 := by
    dsimp only [alpha]
    rw [map_sub, FTType1InfrastructureInternal.pairingSubRight,
      hpsiTau xi₁ hxi₁S, hpsiTau xi₂ hxi₂S, sub_self]
  have htauVirtual : ClassFunction.IsVirtual (tauS alpha) :=
    hcoherent.mapsToVirtual alpha halphaSpan
  have hstarPsi : starCharacterPairing psi (tauS alpha) = 0 := by
    rw [FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
      psi htauVirtual, hpsiDifference]
  have hstarTauPsi : starCharacterPairing (tauS alpha) psi = 0 := by
    calc
      starCharacterPairing (tauS alpha) psi =
          star (starCharacterPairing psi (tauS alpha)) :=
        starCharacterPairing_conj_symm _ _
      _ = 0 := by simp [hstarPsi]
  let psiTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    constituentAmbientTopMap psi
  have hDadeEq :
      constituentTopTargetMap (Dade ddF alpha) = tauS alpha := by
    calc
      constituentTopTargetMap (Dade ddF alpha) =
          constituentTopTargetMap
            (Dade (FT_Dade0_hyp L ctx.maxL) alpha) :=
        congrArg constituentTopTargetMap
          (FT_DadeF_E L ctx.maxL alpha halphaF)
      _ = constituentTopTargetMap
          (Dade (FT_Dade_hyp L ctx.maxL) alpha) :=
        congrArg constituentTopTargetMap
          (FT_DadeE L ctx.maxL alpha halphaFull).symm
      _ = ctx.tau alpha := rfl
      _ = tauS alpha := hagree.symm
  have hstarDadeTop :
      starCharacterPairing (Dade ddF alpha) psiTop = 0 := by
    calc
      starCharacterPairing (Dade ddF alpha) psiTop =
          starCharacterPairing
            (constituentTopTargetMap (Dade ddF alpha))
            (constituentTopTargetMap psiTop) :=
        (constituentTopTargetMap_starPairing _ _).symm
      _ = starCharacterPairing (tauS alpha) psi := by
        rw [hDadeEq]
        dsimp only [psiTop]
        rw [constituentTopTargetMap_ambientTopMap]
      _ = 0 := hstarTauPsi
  have hreciprocity := invDade_reciprocity ddF psiTop alpha halphaF
  rw [hstarDadeTop] at hreciprocity
  have hrpsi : rpsi = invDade ddF psiTop := rfl
  have hstarAlphaRpsi : starCharacterPairing alpha rpsi = 0 := by
    rw [hrpsi]
    exact hreciprocity.symm
  have halphaVirtual : ClassFunction.IsVirtual alpha :=
    (ctx.R_spec.subcoherent_family.source_virtual xi₁ hxi₁).sub
      (ctx.R_spec.subcoherent_family.source_virtual xi₂ hxi₂)
  have hstarRpsiAlpha : starCharacterPairing rpsi alpha = 0 := by
    calc
      starCharacterPairing rpsi alpha =
          star (starCharacterPairing alpha rpsi) :=
        starCharacterPairing_conj_symm _ _
      _ = 0 := by simp [hstarAlphaRpsi]
  change characterPairing rpsi alpha = 0
  rw [← FTType1InfrastructureInternal.starPairingEqPairingOfRightVirtual
    rpsi halphaVirtual]
  exact hstarRpsiAlpha

/-- Membership in the Fitting-derived layer becomes nonmembership in the
commutator after changing subgroup levels. -/
private theorem fittingDerivedLayerOutsideCommutator
    {L : Subgroup G} {x : L}
    (hx : x ∈ FTType1FittingDerivedLayer L) :
    (⟨x, hx.1⟩ : FTType1FittingIn L) ∉
      _root_.commutator (FTType1FittingIn L) := by
  let H := FTType1FittingIn L
  let xH : H := ⟨x, hx.1⟩
  change xH ∉ _root_.commutator H
  intro hxD
  apply hx.2
  let eH : H ≃* Fitting_core L :=
    Subgroup.subgroupOfEquivOfLe (Fcore_sub L)
  have hxCore : eH xH ∈ _root_.commutator (Fitting_core L) := by
    have hmap : (_root_.commutator H).map eH.toMonoidHom =
        _root_.commutator (Fitting_core L) := by
      rw [map_commutator_eq,
        MonoidHom.range_eq_top.mpr eH.surjective]
      rfl
    rw [← hmap]
    exact Subgroup.mem_map_of_mem eH.toMonoidHom hxD
  change (x : G) ∈
    (_root_.commutator (Fitting_core L)).map
      (Fitting_core L).subtype
  convert Subgroup.mem_map_of_mem (Fitting_core L).subtype hxCore using 1
  rfl

/-- `PFsection12.v: FtypeI_invDade_ortho_constant`, Peterfalvi (12.5). -/
theorem FtypeI_invDade_ortho_constant
    {L : Subgroup G} (ctx : FTType1Context L)
    (psi : ClassFunction G ℂ)
    (horth : FTType1OrthogonalToImages ctx psi) :
    ∀ x ∈ FTType1FittingDerivedLayer L,
      ∀ y ∈ FTType1FittingDerivedLayer L,
        ctx.rho psi x = ctx.rho psi y := by
  classical
  let H := FTType1FittingIn L
  letI : H.Normal := Fcore_normal L
  let rpsi : ClassFunction L ℂ := ctx.rho psi
  have hpair : ∀ xi₁ ∈ FTType1SeqIndFamily L,
      ∀ xi₂ ∈ FTType1SeqIndFamily L,
        xi₁ 1 = xi₂ 1 →
          characterPairing rpsi (xi₁ - xi₂) = 0 := by
    intro xi₁ hxi₁ xi₂ hxi₂ hdegree
    exact inverseDadeSourceDifferencePairing
      ctx psi horth hxi₁ hxi₂ hdegree
  have hconstant :=
    constantOnCommutatorComplementOfSeqIndPairing
      H rpsi (by simpa only [H, FTType1SeqIndFamily] using hpair)
  intro x hx y hy
  let xH : H := ⟨x, hx.1⟩
  let yH : H := ⟨y, hy.1⟩
  have hxNotD : xH ∉ _root_.commutator H := by
    simpa only [xH, H] using fittingDerivedLayerOutsideCommutator hx
  have hyNotD : yH ∉ _root_.commutator H := by
    simpa only [yH, H] using fittingDerivedLayerOutsideCommutator hy
  exact hconstant xH hxNotD yH hyNotD

end

end Submission.OddOrder.PF
