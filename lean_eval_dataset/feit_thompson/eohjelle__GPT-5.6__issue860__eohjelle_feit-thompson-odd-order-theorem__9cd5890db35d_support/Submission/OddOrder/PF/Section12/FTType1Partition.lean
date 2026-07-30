import Submission.OddOrder.PF.Section12.FTType1Infrastructure

/-!
# Peterfalvi Section 12: the type-I constituent partition

This module proves Peterfalvi (12.2)(a).  It identifies the type-I
irreducibles with the constituents of the sequentially induced family,
packages those constituents as a partition, and applies the Dade isometry to
obtain the subcoherent family used by the later parts of Section 12.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance : Fintype G := Fintype.ofFinite G

/-! ## Two local restriction lemmas -/

private theorem subgroupOf_ne_bot
    {Q : Type u} [Group Q] {H J : Subgroup Q}
    (hHJ : H ≤ J) (hH : H ≠ ⊥) :
    H.subgroupOf J ≠ ⊥ := by
  intro hbot
  apply hH
  apply le_bot_iff.mp
  intro x hx
  let xJ : J := ⟨x, hHJ hx⟩
  have hxH : xJ ∈ H.subgroupOf J := hx
  rw [hbot] at hxH
  exact Subgroup.mem_bot.mpr
    (congrArg Subtype.val (Subgroup.mem_bot.mp hxH))

private theorem exists_constituent_restrict
    {Q : Type u} [Group Q] [Fintype Q]
    (H : Subgroup Q) [Fintype H]
    (chi : IrreducibleCharacter Q ℂ) :
    ∃ theta : IrreducibleCharacter H ℂ,
      theta.IsConstituent
        (ClassFunction.restrict H (chi : ClassFunction Q ℂ)) := by
  let V : FDRep ℂ H :=
    FDRep.of (chi.representation.ρ.comp H.subtype)
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
  have hV : ClassFunction.ofRepresentation V.ρ =
      ClassFunction.restrict H (chi : ClassFunction Q ℂ) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  rwa [hV] at htheta

private theorem complement_subgroupOf_inf_right
    {Q : Type u} [Group Q] {N C T : Subgroup Q}
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

/-! ## The constituent family -/

/-- `PFsection12.v: FTtype1_ref_irr`. -/
theorem FTtype1_ref_irr
    {L : Subgroup G} (ctx : FTType1Context L) :
    ∃ phi : ClassFunction L ℂ,
      phi ∈ FTType1SeqIndFamily L ∧
        phi 1 = ((FTType1FittingIn L).index : ℂ) := by
  let H := FTType1FittingIn L
  letI : IsSolvable L := mmax_sol ctx.maxL
  letI : IsSolvable H := by infer_instance
  have hHne : H ≠ ⊥ :=
    subgroupOf_ne_bot (Fcore_sub L) (mmax_Fcore_neq1 ctx.maxL)
  letI : Nontrivial H := H.nontrivial_iff_ne_bot.mpr hHne
  have hbot : (⊥ : Subgroup H) < ⊤ := by
    rw [bot_lt_iff_ne_bot]
    exact top_ne_bot
  simpa [H, FTType1SeqIndFamily] using
    (exists_linInd H (⊥ : Subgroup H) hbot)

/-- `PFsection12.v: FTtype1_irrP`. -/
theorem FTtype1_irrP
    {L : Subgroup G} (ctx : FTType1Context L)
    (i : IrreducibleCharacter L ℂ) :
    i ∈ FTType1IrrIndex L ↔
      ∃ chi : ClassFunction L ℂ,
        chi ∈ FTType1SeqIndFamily L ∧
          i ∈ ClassFunction.constituents chi := by
  let H := FTType1FittingIn L
  letI : H.Normal := Fcore_normal L
  rw [FTType1IrrIndex, mem_Iirr_kerD]
  constructor
  · rintro ⟨_, hiH⟩
    rw [ClassFunction.translationKernel_irreducibleCharacter] at hiH
    obtain ⟨theta, htheta⟩ := exists_constituent_restrict H i
    have hthetaNe :
        theta ≠ (IrreducibleCharacter.trivial :
          IrreducibleCharacter H ℂ) := by
      intro hthetaOne
      apply hiH
      have hker :=
        (IrreducibleCharacter.sub_ker_constituent_restrict_iff
          H H le_rfl i theta htheta).mp
      apply hker
      subst theta
      rw [← ClassFunction.translationKernel_irreducibleCharacter
        (IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ)]
      intro x hx
      rw [ClassFunction.mem_translationKernel_iff]
      intro y
      simp
    let chi : ClassFunction L ℂ :=
      ClassFunction.induce H (theta : ClassFunction H ℂ)
    refine ⟨chi, ?_, ?_⟩
    · apply (seqIndC1P (k := ℂ) H).mpr
      exact ⟨theta, hthetaNe, rfl⟩
    · rw [ClassFunction.mem_constituents_iff]
      exact (theta.isConstituent_restrict_iff_induce H i).mp htheta
  · rintro ⟨chi, hchi, hi⟩
    obtain ⟨theta, hthetaNe, hchiEq⟩ :=
      (seqIndC1P (k := ℂ) H).mp hchi
    have hiConst : i.IsConstituent
        (ClassFunction.induce H (theta : ClassFunction H ℂ)) := by
      rw [← hchiEq]
      exact (ClassFunction.mem_constituents_iff chi i).mp hi
    have hnotTop :
        ¬(⊤ : Subgroup H) ≤ theta.representation.ρ.ker := by
      have hmem := (mem_Iirr_ker1 theta).mpr hthetaNe
      rw [mem_Iirr_kerD,
        ClassFunction.translationKernel_irreducibleCharacter] at hmem
      simpa using hmem.2
    refine ⟨bot_le, ?_⟩
    rw [ClassFunction.translationKernel_irreducibleCharacter]
    intro hiKer
    apply hnotTop
    simpa using
      (IrreducibleCharacter.sub_ker_constituent_induce_iff
        H H le_rfl i theta hiConst).mpr hiKer

/-- `PFsection12.v: FTtype1_irr_partition`. -/
theorem FTtype1_irr_partition
    {L : Subgroup G} (ctx : FTType1Context L) :
    IsSetPartition (FTType1ConstituentFamily L)
      (FTType1IrrIndex L : Set (IrreducibleCharacter L ℂ)) := by
  let H := FTType1FittingIn L
  letI : H.Normal := Fcore_normal L
  refine ⟨?_, ?_, ?_⟩
  · ext i
    constructor
    · rintro ⟨A, ⟨chi, hchi, rfl⟩, hi⟩
      exact (FTtype1_irrP ctx i).mpr ⟨chi, hchi, hi⟩
    · intro hi
      obtain ⟨chi, hchi, hiChi⟩ := (FTtype1_irrP ctx i).mp hi
      exact ⟨(ClassFunction.constituents chi :
          Set (IrreducibleCharacter L ℂ)),
        ⟨chi, hchi, rfl⟩, hiChi⟩
  · intro A hA B hB hAB
    obtain ⟨chiA, hchiA, rfl⟩ := hA
    obtain ⟨chiB, hchiB, rfl⟩ := hB
    have hchiNe : chiA ≠ chiB := by
      intro h
      apply hAB
      rw [h]
    obtain ⟨V, hV⟩ := seqInd_char H hchiA
    obtain ⟨W, hW⟩ := seqInd_char H hchiB
    have hpair : characterPairing chiA chiB = 0 :=
      seqInd_ortho H hchiA hchiB hchiNe
    have hpair' : characterPairing
        (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) = 0 := by
      rw [hV, hW]
      exact hpair
    change Disjoint
      (ClassFunction.constituents chiA :
        Set (IrreducibleCharacter L ℂ))
      (ClassFunction.constituents chiB :
        Set (IrreducibleCharacter L ℂ))
    rw [← hV, ← hW]
    exact FTType1InfrastructureInternal.constituentsDisjointOfPairingEqZero
      V W hpair'
  · rintro ⟨chi, hchi, hconst⟩
    have hconstEmpty : ClassFunction.constituents chi = ∅ := by
      ext i
      constructor
      · intro hi
        have hiEmpty : i ∈
            (∅ : Set (IrreducibleCharacter L ℂ)) := by
          rw [hconst]
          exact hi
        exact hiEmpty.elim
      · simp
    have hsum := ClassFunction.sum_constituents_eq chi
    rw [hconstEmpty] at hsum
    simp only [Finset.sum_empty] at hsum
    exact (seqInd_neq0 H hchi) hsum.symm

/-! ## Peterfalvi (12.2)(a) -/

/-- `PFsection12.v: FTtype1_seqInd_facts`, Peterfalvi (12.2)(a). -/
theorem FTtype1_seqInd_facts
    {L : Subgroup G} (ctx : FTType1Context L)
    (chi : ClassFunction L ℂ)
    (hchi : chi ∈ FTType1SeqIndFamily L) :
    FTType1SeqIndFacts L chi := by
  let H := FTType1FittingIn L
  letI : H.Normal := Fcore_normal L
  obtain ⟨theta, hthetaNe, rfl⟩ :=
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
  have hthetaFNe :
      thetaF ≠ (IrreducibleCharacter.trivial :
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
  have hVmap :
      ((U.subgroupOf L) ⊓ T).map L.subtype ≤ U₁ := by
    have hle :=
      (typeF_context L U hTypeF).inertia_le U₁ thetaF hU₁ hthetaFNe
    change ((U.subgroupOf L) ⊓
      ClassFunction.inertia H thetaH).map L.subtype ≤ U₁ at hle
    rw [hthetaH] at hle
    simpa only [T] using hle
  have hVcomm : IsMulCommutative
      ((U.subgroupOf L) ⊓ T : Subgroup L) := by
    apply isMulCommutative_iff.mpr
    intro x y
    let x₁ : U₁ :=
      ⟨((x : L) : G),
        hVmap (Subgroup.mem_map_of_mem L.subtype x.property)⟩
    let y₁ : U₁ :=
      ⟨((y : L) : G),
        hVmap (Subgroup.mem_map_of_mem L.subtype y.property)⟩
    have hxy := isMulCommutative_iff.mp hU₁.2.2.1 x₁ y₁
    apply Subtype.ext
    apply Subtype.ext
    change ((x : L) : G) * ((y : L) : G) =
      ((y : L) : G) * ((x : L) : G)
    simpa [x₁, y₁] using congrArg Subtype.val hxy
  have hsdT : IsInternalSemidirectProductIn H
      ((U.subgroupOf L) ⊓ T) T := by
    refine ⟨hHT, inf_le_right, ?_, ?_⟩
    · exact Subgroup.Normal.subgroupOf hHnormal T
    · exact complement_subgroupOf_inf_right hComplement hHT
  letI : IsMulCommutative (T ⧸ H.subgroupOf T) :=
    FTType1InfrastructureInternal.semidirectQuotientCommutative hsdT hVcomm
  have hInd :=
    ClassFunction.cfInd_Hall_central_inertia H theta hHall
  refine
    ⟨hInd.1,
      ⟨(T.index : ℂ) * theta 1, hInd.2.2⟩,
      ?_⟩
  intro i hi
  have hiConst : i.IsConstituent
      (ClassFunction.induce H (theta : ClassFunction H ℂ)) :=
    (ClassFunction.mem_constituents_iff _ _).mp hi
  have hthetaNotTop :
      ¬(⊤ : Subgroup H) ≤
        ClassFunction.translationKernel (theta : ClassFunction H ℂ) := by
    have hmem := (mem_Iirr_ker1 theta).mpr hthetaNe
    rw [mem_Iirr_kerD] at hmem
    exact hmem.2
  have hiKer : ¬ H ≤
      ClassFunction.translationKernel (i : ClassFunction L ℂ) := by
    intro hker
    apply hthetaNotTop
    have hker' : H ≤ i.representation.ρ.ker := by
      simpa only [ClassFunction.translationKernel_irreducibleCharacter]
        using hker
    rw [ClassFunction.translationKernel_irreducibleCharacter]
    simpa only [Subgroup.subgroupOf_self] using
      (IrreducibleCharacter.sub_ker_constituent_induce_iff
        H H le_rfl i theta hiConst).mpr hker'
  rw [ClassFunction.mem_supportedOn_iff]
  intro y hySupport
  have hyOne : y ≠ 1 := by
    intro hy
    apply hySupport
    exact Or.inl hy
  have hyAmbientOne : (y : G) ≠ 1 := by
    intro hy
    apply hyOne
    exact Subtype.ext hy
  have hyNotFT : (y : G) ∉ FTsupport L := by
    intro hy
    apply hySupport
    exact Or.inr hy
  apply irr_reg_off_ker_0 H i hiKer y
  apply le_antisymm _ bot_le
  intro z hz
  apply Subgroup.mem_bot.mpr
  by_contra hzOne
  have hzAmbientOne : ((z : L) : G) ≠ 1 := by
    intro hz
    apply hzOne
    exact Subtype.ext hz
  have hzSupp1 : ((z : L) : G) ∈ FTsupport1 L := by
    rw [FTsupp1_type1 L ctx.type_one]
    exact ⟨hz.1, hzAmbientOne⟩
  have hyCentral : (y : G) ∈
      centralizerWithin (FTder L)
        (Subgroup.zpowers ((z : L) : G)) := by
    apply mem_centralizerWithin.mpr
    refine ⟨?_, ?_⟩
    · simpa [FTder, ftDerived, ctx.type_one] using y.property
    · intro a ha
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
      have hyz : Commute y (z : L) :=
        (mem_centralizerWithin.mp hz).2 y (Subgroup.mem_zpowers y)
      exact congrArg Subtype.val (hyz.symm.zpow_left n).eq
  apply hyNotFT
  simp only [FTsupport, ftSupport, Set.mem_iUnion]
  exact ⟨((z : L) : G), hzSupp1, ⟨hyCentral, hyAmbientOne⟩⟩

/-! ## Dade isometry and subcoherence -/

private noncomputable def type1DadeTargetMap :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

private theorem type1DadeTargetMap_pairing
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (type1DadeTargetMap phi)
        (type1DadeTargetMap psi) =
      characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [type1DadeTargetMap, ClassFunction.comap_apply]

private theorem type1DadeTargetMap_virtual
    {phi : ClassFunction (⊤ : Subgroup G) ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (type1DadeTargetMap phi) := by
  obtain ⟨z, hz⟩ := hphi
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.symm.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]
  rfl

private theorem type1DadeTargetMap_supported
    {phi : ClassFunction (⊤ : Subgroup G) ℂ}
    (hphi : phi ∈ ClassFunction.supportedOn
      (nonidentitySet (⊤ : Subgroup G))) :
    type1DadeTargetMap phi ∈
      ClassFunction.supportedOn (nonidentitySet G) := by
  rw [ClassFunction.mem_supportedOn_iff] at hphi ⊢
  intro x hx
  have hxOne : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simpa [type1DadeTargetMap, ClassFunction.comap_apply] using
    hphi (1 : (⊤ : Subgroup G)) (by simp [nonidentitySet])

/-- `PFsection12.v: FTtype1_irr_isometry`. -/
theorem FTtype1_irr_isometry
    {L : Subgroup G} (ctx : FTType1Context L) :
    FTType1IrrIsometryConclusion L ctx.tau := by
  let S : Set (ClassFunction L ℂ) := FTType1IrrFamily L
  have hGeneratorSupport {phi : ClassFunction L ℂ} (hphi : phi ∈ S) :
      phi ∈ ClassFunction.supportedOn (FTType1CharacterSupport L) := by
    rcases Finset.mem_image.mp hphi with ⟨i, hi, rfl⟩
    obtain ⟨chi, hchi, hiChi⟩ := (FTtype1_irrP ctx i).mp hi
    exact (FTtype1_seqInd_facts ctx chi hchi).constituent_supported i hiChi
  have hSpanSupport {phi : ClassFunction L ℂ}
      (hphi : phi ∈ AddSubgroup.closure S) :
      phi ∈ ClassFunction.supportedOn (FTType1CharacterSupport L) := by
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi => exact hGeneratorSupport hphi
    | zero =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (FTType1CharacterSupport L)).zero_mem
    | add phi psi hphi hpsi ihphi ihpsi =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (FTType1CharacterSupport L)).add_mem ihphi ihpsi
    | neg phi hphi ihphi =>
        exact (ClassFunction.supportedOn (R := ℂ)
          (FTType1CharacterSupport L)).neg_mem ihphi
  have hSpanVirtual {phi : ClassFunction L ℂ}
      (hphi : phi ∈ AddSubgroup.closure S) :
      ClassFunction.IsVirtual phi := by
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi =>
        rcases Finset.mem_image.mp hphi with ⟨i, hi, rfl⟩
        exact FTType1InfrastructureInternal.irreducibleIsVirtual i
    | zero => exact ClassFunction.IsVirtual.zero
    | add phi psi hphi hpsi ihphi ihpsi => exact ihphi.add ihpsi
    | neg phi hphi ihphi => exact ihphi.neg
  have hDadeSupport {phi : ClassFunction L ℂ}
      (hphi : phi ∈ AddSubgroup.closure S)
      (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet L)) :
      phi ∈ ClassFunction.supportedOn
        {x : L | (x : G) ∈ FTsupport L} := by
    have hsupp := hSpanSupport hphi
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxOne : x = 1
    · subst x
      exact ClassFunction.eq_zero_of_mem_supportedOn hoff
        (by simp [nonidentitySet])
    · apply ClassFunction.eq_zero_of_mem_supportedOn hsupp
      simpa [FTType1CharacterSupport, hxOne] using hx
  let dd := FT_Dade_hyp L ctx.maxL
  refine ⟨?_, ?_, ?_⟩
  · intro phi hphi hphiOff psi hpsi hpsiOff
    obtain ⟨z, hz⟩ := hSpanVirtual hphi
    obtain ⟨w, hw⟩ := hSpanVirtual hpsi
    have hzA : VirtualCharacter.realize z ∈
        ClassFunction.supportedOn {x : L | (x : G) ∈ FTsupport L} := by
      rw [hz]
      exact hDadeSupport hphi hphiOff
    have hwA : VirtualCharacter.realize w ∈
        ClassFunction.supportedOn {x : L | (x : G) ∈ FTsupport L} := by
      rw [hw]
      exact hDadeSupport hpsi hpsiOff
    obtain ⟨z', hz', _⟩ := (Dade_Zisometry dd).2 z hzA
    obtain ⟨w', hw', _⟩ := (Dade_Zisometry dd).2 w hwA
    have hstar₀ := (Dade_Zisometry dd).1 z w hzA hwA
    have hpair : characterPairing
        (VirtualCharacter.realize z') (VirtualCharacter.realize w') =
        characterPairing
          (VirtualCharacter.realize z) (VirtualCharacter.realize w) := by
      rw [← FTType1InfrastructureInternal.starPairingRealizeEqPairing z' w',
        ← FTType1InfrastructureInternal.starPairingRealizeEqPairing z w]
      simpa only [hz', hw'] using hstar₀
    change characterPairing
      (type1DadeTargetMap (Dade dd phi))
      (type1DadeTargetMap (Dade dd psi)) = _
    calc
      characterPairing
          (type1DadeTargetMap (Dade dd phi))
          (type1DadeTargetMap (Dade dd psi)) =
          characterPairing (Dade dd phi) (Dade dd psi) :=
        type1DadeTargetMap_pairing _ _
      _ =
          characterPairing (VirtualCharacter.realize z')
            (VirtualCharacter.realize w') := by
              rw [← hz, ← hw, hz', hw']
      _ = characterPairing (VirtualCharacter.realize z)
          (VirtualCharacter.realize w) := hpair
      _ = characterPairing phi psi := by rw [hz, hw]
  · intro phi hphi hphiOff
    obtain ⟨z, hz⟩ := hSpanVirtual hphi
    have hzA : VirtualCharacter.realize z ∈
        ClassFunction.supportedOn {x : L | (x : G) ∈ FTsupport L} := by
      rw [hz]
      exact hDadeSupport hphi hphiOff
    obtain ⟨beta, hbeta, _⟩ := (Dade_Zisometry dd).2 z hzA
    change ClassFunction.IsVirtual
      (type1DadeTargetMap (Dade dd phi))
    apply type1DadeTargetMap_virtual
    refine ⟨beta, ?_⟩
    change VirtualCharacter.realize beta = Dade dd phi
    rw [← hz]
    exact hbeta.symm
  · intro phi hphi hphiOff
    change type1DadeTargetMap (Dade dd phi) ∈
      ClassFunction.supportedOn (nonidentitySet G)
    exact type1DadeTargetMap_supported (Dade_cfun dd phi)

/-- `PFsection12.v: FTtype1_irr_subcoherent`. -/
theorem FTtype1_irr_subcoherent
    {L : Subgroup G} (ctx : FTType1Context L) :
    ∃ R1 : ClassFunction L ℂ → Finset (ClassFunction G ℂ),
      subcoherent
        (FTType1IrrFamily L : Set (ClassFunction L ℂ))
        ctx.tau R1 := by
  let S : Set (ClassFunction L ℂ) := FTType1IrrFamily L
  have hclosed : cfConjC_subset S
      (Set.range fun chi : IrreducibleCharacter L ℂ ↦
        (chi : ClassFunction L ℂ)) := by
    constructor
    · intro phi hphi
      rcases Finset.mem_image.mp hphi with ⟨i, hi, rfl⟩
      exact ⟨i, rfl⟩
    · intro phi hphi
      rcases Finset.mem_image.mp hphi with ⟨i, hi, rfl⟩
      rw [ClassFunction.inverseLinear_irreducible]
      apply Finset.mem_image.mpr
      refine ⟨IrreducibleCharacter.dual i, ?_, rfl⟩
      rw [FTType1IrrIndex, mem_Iirr_kerD] at hi ⊢
      have hker :
          ClassFunction.translationKernel
              (IrreducibleCharacter.dual i : ClassFunction L ℂ) =
            ClassFunction.translationKernel (i : ClassFunction L ℂ) := by
        rw [← ClassFunction.inverseLinear_irreducible,
          ClassFunction.translationKernel_inverseLinear]
      simpa only [hker] using hi
  have hnonreal : ∀ phi ∈ S,
      ClassFunction.inverseLinear phi ≠ phi := by
    intro phi hphi
    rcases Finset.mem_image.mp hphi with ⟨i, hi, rfl⟩
    have hiNe : i ≠
        (IrreducibleCharacter.trivial : IrreducibleCharacter L ℂ) := by
      intro hiOne
      subst i
      rw [FTType1IrrIndex, mem_Iirr_kerD] at hi
      apply hi.2
      intro x hx y
      simp
    rw [ClassFunction.inverseLinear_irreducible]
    intro hreal
    have hdual : IrreducibleCharacter.dual i = i := by
      apply Subtype.ext
      exact hreal
    exact hiNe ((odd_eq_conj_irr1 (mFT_odd L) i).mp hdual)
  have hiso := FTtype1_irr_isometry ctx
  exact irr_subcoherent S ctx.tau hclosed hnonreal
    hiso.isometry hiso.mapsToVirtual hiso.supported

end

end Submission.OddOrder.PF
