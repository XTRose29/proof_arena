import Submission.OddOrder.PF.Section12.FTType1Subcoherence

/-!
# Peterfalvi Section 12: orthogonality of type-I sequential images

This module proves Peterfalvi (12.3).  The canonical families supplied by
type-I subcoherence for two nonconjugate maximal subgroups are mutually
orthogonal.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance : Fintype G := Fintype.ofFinite G

local instance : Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Orthogonality interfaces -/

/-- A class function is orthogonal to every canonical target family attached
to the type-I sequential family. -/
def FTType1OrthogonalToImages
    {L : Subgroup G} (ctx : FTType1Context L)
    (psi : ClassFunction G ℂ) : Prop :=
  ∀ chi ∈ FTType1SeqIndFamily L,
    ∀ mu ∈ ctx.R chi, characterPairing psi mu = 0

/-- The canonical target families attached to two type-I maximal subgroups
are mutually orthogonal. -/
def FTType1ImageFamiliesOrthogonal
    {L1 L2 : Subgroup G}
    (ctx1 : FTType1Context L1) (ctx2 : FTType1Context L2) : Prop :=
  ∀ chi1 ∈ FTType1SeqIndFamily L1,
    ∀ chi2 ∈ FTType1SeqIndFamily L2,
      ∀ mu ∈ ctx1.R chi1, ∀ nu ∈ ctx2.R chi2,
        characterPairing mu nu = 0

/-! ## Transport from the ambient top subgroup -/

/-- Pull a class function on the top subgroup back to the ambient group. -/
private noncomputable def topTargetMap :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

private theorem topTargetMap_pairing
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (topTargetMap phi) (topTargetMap psi) =
      characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [topTargetMap, ClassFunction.comap_apply]

private theorem topTargetMap_irreducible
    (chi : IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
    topTargetMap (chi : ClassFunction (⊤ : Subgroup G) ℂ) =
      (IrreducibleCharacter.comapMulEquiv
        Subgroup.topEquiv.symm chi : ClassFunction G ℂ) := by
  ext x
  simp [topTargetMap, ClassFunction.comap_apply]

private theorem comapTop_dual
    (chi : IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
    IrreducibleCharacter.comapMulEquiv Subgroup.topEquiv.symm
        (IrreducibleCharacter.dual chi) =
      IrreducibleCharacter.dual
        (IrreducibleCharacter.comapMulEquiv
          Subgroup.topEquiv.symm chi) := by
  ext x
  simp [IrreducibleCharacter.dual_apply]

private theorem topTargetMap_conjC
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    topTargetMap (cfConjC phi) = cfConjC (topTargetMap phi) := by
  ext x
  simp [topTargetMap, ClassFunction.comap_apply]

/-- The global Dade support is inverse-stable when the underlying Dade set is
the nonidentity part of a subgroup. -/
private theorem dadeSupportSubgroupNonidentityInvStable
    {L H : Subgroup G}
    (ddA : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity H)) :
    IsInvStable (Dade_support ddA) := by
  have hinv : ∀ x : G,
      x ∈ Dade_support ddA → x⁻¹ ∈ Dade_support ddA := by
    intro x
    rintro ⟨a, haA, z, hz, g, hgTop, hzx⟩
    have haH : a ∈ H := haA.1
    have haOne : a ≠ 1 := haA.2
    rcases Set.mem_mul.mp hz with ⟨s, hs, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst b
    have hsa : Commute s a :=
      (Subgroup.mem_centralizer_iff.mp
        (Dade_signalizer_cent ddA a hs) a
          (Subgroup.mem_zpowers a)).symm
    have haInv : a⁻¹ ∈ subgroupNonidentity H :=
      ⟨H.inv_mem haH, inv_ne_one.mpr haOne⟩
    have hsignalizerInv :
        DadeSignalizer ddA a⁻¹ = DadeSignalizer ddA a := by
      simp [DadeSignalizer, Subgroup.zpowers_inv]
    refine ⟨a⁻¹, haInv, s⁻¹ * a⁻¹, ?_, g, hgTop, ?_⟩
    · apply Set.mem_mul.mpr
      exact ⟨s⁻¹, by simpa [hsignalizerInv] using
          (DadeSignalizer ddA a).inv_mem hs,
        a⁻¹, Set.mem_singleton a⁻¹, rfl⟩
    · have hsaInv : s⁻¹ * a⁻¹ = a⁻¹ * s⁻¹ := by
        simpa only [mul_inv_rev] using congrArg Inv.inv hsa.symm
      rw [← hzx, mul_inv_rev, hsaInv]
      group
  intro x
  constructor
  · intro hx
    simpa only [inv_inv] using hinv x⁻¹ hx
  · exact hinv x

/-- Dade images with disjoint global supports are orthogonal when the first
underlying Dade set is a subgroup's nonidentity set. -/
private theorem disjointDadeOrthoFirst
    {L₁ L₂ H : Subgroup G} {A₂ : Set G}
    (ddA₁ : DadeHypothesis (⊤ : Subgroup G) L₁
      (subgroupNonidentity H))
    (ddA₂ : DadeHypothesis (⊤ : Subgroup G) L₂ A₂)
    (hdis : Disjoint (Dade_support ddA₁) (Dade_support ddA₂))
    (phi : ClassFunction L₁ ℂ) (psi : ClassFunction L₂ ℂ) :
    characterPairing (Dade ddA₁ phi) (Dade ddA₂ psi) = 0 := by
  have hsubdis : Disjoint
      {x : (⊤ : Subgroup G) | (x : G) ∈ Dade_support ddA₁}
      {x : (⊤ : Subgroup G) | (x : G) ∈ Dade_support ddA₂} := by
    rw [Set.disjoint_left]
    intro x hx₁ hx₂
    exact Set.disjoint_left.mp hdis hx₁ hx₂
  apply characterPairing_eq_zero_of_disjoint_of_invStable_left hsubdis
  · intro x
    change (x : G)⁻¹ ∈ Dade_support ddA₁ ↔
      (x : G) ∈ Dade_support ddA₁
    exact dadeSupportSubgroupNonidentityInvStable ddA₁ (x : G)
  · exact Dade_cfunS ddA₁ phi
  · exact Dade_cfunS ddA₂ psi

private theorem tau_conjC
    {L : Subgroup G} (ctx : FTType1Context L)
    (phi : ClassFunction L ℂ) :
    cfConjC (ctx.tau phi) = ctx.tau (cfConjC phi) := by
  change cfConjC (topTargetMap (Dade (FT_Dade_hyp L ctx.maxL) phi)) =
    topTargetMap (Dade (FT_Dade_hyp L ctx.maxL) (cfConjC phi))
  rw [← topTargetMap_conjC]
  exact congrArg topTargetMap
    (Dade_conjC (FT_Dade_hyp L ctx.maxL) phi).symm

/-! ## Differences belonging to one target family -/

/-- A member of a canonical irreducible target pair realizes the complete
anti-dual difference of that pair. -/
private theorem targetMemberDifference
    {L : Subgroup G} (ctx : FTType1Context L)
    {i : IrreducibleCharacter L ℂ}
    (hi : i ∈ FTType1IrrIndex L)
    {alpha : ClassFunction G ℂ}
    (halpha : alpha ∈ ctx.R1 (i : ClassFunction L ℂ)) :
    ctx.tau
        ((i : ClassFunction L ℂ) -
          ClassFunction.inverseLinear (i : ClassFunction L ℂ)) =
      alpha - ClassFunction.inverseLinear alpha := by
  let E := ctx.R1 (i : ClassFunction L ℂ)
  have hiFamily : (i : ClassFunction L ℂ) ∈ FTType1IrrFamily L :=
    Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hpairFacts := ctx.R_spec.irreducible_pairs i hi
  have halphaVirtual : ClassFunction.IsVirtual alpha :=
    ctx.R1_subcoherent.image_virtual _ hiFamily alpha halpha
  have halphaNorm : characterPairing alpha alpha = 1 := by
    simpa using hpairFacts.orthonormal alpha halpha alpha halpha
  obtain ⟨eta, epsilon, hepsilon, halphaEq⟩ :=
    FTType1InfrastructureInternal.existsSignedIrreducibleOfVirtualNormOne
      halphaVirtual halphaNorm
  obtain ⟨chi, hchi, hiChi⟩ := (FTtype1_irrP ctx i).mp hi
  have hiSupport :=
    (FTtype1_seqInd_facts ctx chi hchi).constituent_supported i hiChi
  have hiSupport' : (i : ClassFunction L ℂ) ∈
      ClassFunction.supportedOn
        ({1} ∪ {x : L | (x : G) ∈ FTsupport L}) := by
    simpa [FTType1CharacterSupport, Set.mem_union] using hiSupport
  obtain ⟨theta, htheta⟩ :=
    Dade_irr_sub_conjC (FT_Dade_hyp L ctx.maxL) i hiSupport'
  let thetaG : IrreducibleCharacter G ℂ :=
    IrreducibleCharacter.comapMulEquiv Subgroup.topEquiv.symm theta
  have hthetaTop :
      Dade (FT_Dade_hyp L ctx.maxL)
          ((i : ClassFunction L ℂ) -
            ClassFunction.inverseLinear (i : ClassFunction L ℂ)) =
        (theta : ClassFunction (⊤ : Subgroup G) ℂ) -
          (IrreducibleCharacter.dual theta :
            ClassFunction (⊤ : Subgroup G) ℂ) := by
    simpa only [cfConjC_irreducible,
      FTType1InfrastructureInternal.conjugateIrreducibleEqDual,
      ClassFunction.inverseLinear_irreducible] using htheta
  have htheta' :
      ctx.tau
          ((i : ClassFunction L ℂ) -
            ClassFunction.inverseLinear (i : ClassFunction L ℂ)) =
        (thetaG : ClassFunction G ℂ) -
          (IrreducibleCharacter.dual thetaG : ClassFunction G ℂ) := by
    calc
      ctx.tau
          ((i : ClassFunction L ℂ) -
            ClassFunction.inverseLinear (i : ClassFunction L ℂ)) =
          topTargetMap
            (Dade (FT_Dade_hyp L ctx.maxL)
              ((i : ClassFunction L ℂ) -
                ClassFunction.inverseLinear (i : ClassFunction L ℂ))) := rfl
      _ = topTargetMap
          ((theta : ClassFunction (⊤ : Subgroup G) ℂ) -
            (IrreducibleCharacter.dual theta :
              ClassFunction (⊤ : Subgroup G) ℂ)) := by rw [hthetaTop]
      _ = (thetaG : ClassFunction G ℂ) -
          (IrreducibleCharacter.dual thetaG : ClassFunction G ℂ) := by
        rw [map_sub, topTargetMap_irreducible,
          topTargetMap_irreducible, comapTop_dual]
  have halphaPair :
      characterPairing alpha
        (ctx.tau
          ((i : ClassFunction L ℂ) -
            ClassFunction.inverseLinear (i : ClassFunction L ℂ))) = 1 := by
    rw [hpairFacts.dade_difference]
    calc
      characterPairing alpha (∑ beta ∈ E, beta) =
          ∑ beta ∈ E, characterPairing alpha beta :=
        FTType1InfrastructureInternal.pairingFinsetSumRight alpha E id
      _ = 1 := by
        rw [Finset.sum_eq_single alpha]
        · exact halphaNorm
        · intro beta hbeta hbetaNe
          have hne : alpha ≠ beta := Ne.symm hbetaNe
          simpa [hne] using
            hpairFacts.orthonormal alpha halpha beta hbeta
        · exact fun hnot ↦ (hnot halpha).elim
  have hcoefficient :
      (epsilon : ℂ) * (if eta = thetaG then 1 else 0) -
        (epsilon : ℂ) *
          (if eta = IrreducibleCharacter.dual thetaG then 1 else 0) = 1 := by
    rw [halphaEq, htheta', characterPairing_smul_left,
      FTType1InfrastructureInternal.pairingSubRight,
      IrreducibleCharacter.characterPairing_eq_ite,
      IrreducibleCharacter.characterPairing_eq_ite] at halphaPair
    simpa [mul_sub] using halphaPair
  rcases hepsilon with rfl | rfl
  · have heta : eta = thetaG := by
      by_contra heta
      by_cases hdual : eta = IrreducibleCharacter.dual thetaG
      · have hdualNe : IrreducibleCharacter.dual thetaG ≠ thetaG := by
          intro h
          exact heta (hdual.trans h)
        simp [heta, hdual, hdualNe] at hcoefficient
        norm_num at hcoefficient
      · simp [heta, hdual] at hcoefficient
    subst eta
    simpa only [Int.cast_one, one_smul, halphaEq,
      ClassFunction.inverseLinear_irreducible] using htheta'
  · have heta : eta = IrreducibleCharacter.dual thetaG := by
      by_contra hdual
      by_cases heta : eta = thetaG
      · have hthetaNe : thetaG ≠ IrreducibleCharacter.dual thetaG := by
          intro h
          exact hdual (heta.trans h)
        simp [heta, hdual, hthetaNe] at hcoefficient
        norm_num at hcoefficient
      · simp [heta, hdual] at hcoefficient
    subst eta
    have hinvDual :
        ClassFunction.inverseLinear
            ((-1 : ℂ) •
              (IrreducibleCharacter.dual thetaG : ClassFunction G ℂ)) =
          (-1 : ℂ) • (thetaG : ClassFunction G ℂ) := by
      rw [map_smul, ClassFunction.inverseLinear_irreducible]
      simp
    rw [Int.cast_neg, Int.cast_one] at halphaEq
    rw [halphaEq, hinvDual, htheta']
    module

/-- For a type-I sequential character, its anti-dual difference is supported
on the first Feit--Thompson support. -/
private theorem seqIndInverseSubSupportedFirst
    {L : Subgroup G} (ctx : FTType1Context L)
    {chi : ClassFunction L ℂ}
    (hchi : chi ∈ FTType1SeqIndFamily L) :
    chi - ClassFunction.inverseLinear chi ∈
      ClassFunction.supportedOn
        {x : L | (x : G) ∈ FTsupport1 L} := by
  let H := FTType1FittingIn L
  letI : H.Normal := Fcore_normal L
  have hchiVirtual : ClassFunction.IsVirtual chi :=
    ctx.R_spec.subcoherent_family.source_virtual chi hchi
  have hconj :
      ClassFunction.mapRingHom complexConjugation.toRingHom chi =
        ClassFunction.inverseLinear chi := by
    exact
      (FTType1InfrastructureInternal.inverseEqConjOfVirtual hchiVirtual).symm
  obtain ⟨z, hz, hzSupport⟩ :=
    seqInd_sub_aut_zchar complexConjugation H ⊤ ⊥ hchi
  rw [hconj] at hz
  rw [hz] at hzSupport
  rw [ClassFunction.mem_supportedOn_iff] at hzSupport ⊢
  intro x hx
  apply hzSupport
  intro hxH
  apply hx
  rw [FTsupp1_type1 L ctx.type_one]
  refine ⟨hxH.1, ?_⟩
  intro hxOne
  apply hxH.2
  apply Subtype.ext
  exact hxOne

/-- The Dade image of an anti-dual difference is itself anti-invariant under
inversion. -/
private theorem inverseDadeInverseSub
    {L : Subgroup G} (ctx : FTType1Context L)
    {phi : ClassFunction L ℂ}
    (hphiVirtual : ClassFunction.IsVirtual phi)
    (himageVirtual : ClassFunction.IsVirtual
      (ctx.tau (phi - ClassFunction.inverseLinear phi))) :
    ClassFunction.inverseLinear
        (ctx.tau (phi - ClassFunction.inverseLinear phi)) =
      -ctx.tau (phi - ClassFunction.inverseLinear phi) := by
  let d := phi - ClassFunction.inverseLinear phi
  have hconjPhi : cfConjC phi = ClassFunction.inverseLinear phi :=
    (FTType1InfrastructureInternal.inverseEqConjOfVirtual hphiVirtual).symm
  have hconjD : cfConjC d = -d := by
    dsimp only [d]
    rw [map_sub, hconjPhi, ← hconjPhi, cfConjC_involutive]
    module
  rw [FTType1InfrastructureInternal.inverseEqConjOfVirtual himageVirtual]
  rw [tau_conjC, hconjD, map_neg]

/-! ## Peterfalvi (12.3) -/

/-- Oriented form of Peterfalvi (12.3): the first Dade support of `Lfirst`
is disjoint from the full Dade support of `Lfull`. -/
private theorem seqIndOrthogonalOriented
    {Lfull Lfirst : Subgroup G}
    (ctxFull : FTType1Context Lfull)
    (ctxFirst : FTType1Context Lfirst)
    (hdis : Disjoint (FT_Dade1_support Lfirst)
      (FT_Dade_full_support Lfull))
    {chiFull : ClassFunction Lfull ℂ}
    (hchiFull : chiFull ∈ FTType1SeqIndFamily Lfull)
    {chiFirst : ClassFunction Lfirst ℂ}
    (hchiFirst : chiFirst ∈ FTType1SeqIndFamily Lfirst)
    {alpha beta : ClassFunction G ℂ}
    (halpha : alpha ∈ ctxFull.R chiFull)
    (hbeta : beta ∈ ctxFirst.R chiFirst) :
    characterPairing alpha beta = 0 := by
  rw [ctxFull.R_spec.flatten] at halpha
  rcases Finset.mem_biUnion.mp halpha with ⟨i, hi, halphaI⟩
  have hiIndex : i ∈ FTType1IrrIndex Lfull :=
    (FTtype1_irrP ctxFull i).mpr ⟨chiFull, hchiFull, hi⟩
  have halphaDiff := targetMemberDifference ctxFull hiIndex halphaI
  let dFull : ClassFunction Lfull ℂ :=
    (i : ClassFunction Lfull ℂ) -
      ClassFunction.inverseLinear (i : ClassFunction Lfull ℂ)
  let dFirst : ClassFunction Lfirst ℂ :=
    chiFirst - ClassFunction.inverseLinear chiFirst
  let psiFirst : ClassFunction G ℂ := ctxFirst.tau dFirst
  have hdFirstSupport :=
    seqIndInverseSubSupportedFirst ctxFirst hchiFirst
  have hdFirstSupportFull : dFirst ∈
      ClassFunction.supportedOn
        {x : Lfirst | (x : G) ∈ FTsupport Lfirst} := by
    rw [ClassFunction.mem_supportedOn_iff] at hdFirstSupport ⊢
    intro x hxFull
    apply hdFirstSupport
    intro hxFirst
    exact hxFull (FTsupp1_sub ctxFirst.maxL hxFirst)
  have hpsiFirstDade1 :
      psiFirst = topTargetMap
        (Dade (FT_Dade1_hyp Lfirst ctxFirst.maxL) dFirst) := by
    calc
      psiFirst = topTargetMap
          (Dade (FT_Dade_hyp Lfirst ctxFirst.maxL) dFirst) := rfl
      _ = topTargetMap
          (Dade (FT_Dade0_hyp Lfirst ctxFirst.maxL) dFirst) := by
        rw [FT_DadeE Lfirst ctxFirst.maxL dFirst hdFirstSupportFull]
      _ = topTargetMap
          (Dade (FT_Dade1_hyp Lfirst ctxFirst.maxL) dFirst) := by
        rw [(FT_Dade1E Lfirst ctxFirst.maxL dFirst hdFirstSupport).symm]
  have hDadeDisjoint :
      Disjoint
        (Dade_support (FT_Dade_hyp Lfull ctxFull.maxL))
        (Dade_support (FT_Dade1_hyp Lfirst ctxFirst.maxL)) := by
    rw [FT_Dade_supportE Lfull ctxFull.maxL,
      FT_Dade1_supportE Lfirst ctxFirst.maxL]
    exact hdis.symm
  have hrawDadePair : characterPairing
      (Dade (FT_Dade_hyp Lfull ctxFull.maxL) dFull)
      (Dade (FT_Dade1_hyp Lfirst ctxFirst.maxL) dFirst) = 0 := by
    rw [characterPairing_comm]
    exact disjointDadeOrthoFirst
      (H := FTcore Lfirst)
      (FT_Dade1_hyp Lfirst ctxFirst.maxL)
      (FT_Dade_hyp Lfull ctxFull.maxL)
      hDadeDisjoint.symm dFirst dFull
  have hdiffPair : characterPairing
      (alpha - ClassFunction.inverseLinear alpha) psiFirst = 0 := by
    calc
      characterPairing
          (alpha - ClassFunction.inverseLinear alpha) psiFirst =
          characterPairing (ctxFull.tau dFull) psiFirst := by
        rw [halphaDiff]
      _ = characterPairing
          (topTargetMap
            (Dade (FT_Dade_hyp Lfull ctxFull.maxL) dFull))
          (topTargetMap
            (Dade (FT_Dade1_hyp Lfirst ctxFirst.maxL) dFirst)) := by
        rw [hpsiFirstDade1]
        rfl
      _ = characterPairing
          (Dade (FT_Dade_hyp Lfull ctxFull.maxL) dFull)
          (Dade (FT_Dade1_hyp Lfirst ctxFirst.maxL) dFirst) :=
        topTargetMap_pairing _ _
      _ = 0 := hrawDadePair
  have hchiFirstVirtual : ClassFunction.IsVirtual chiFirst :=
    ctxFirst.R_spec.subcoherent_family.source_virtual chiFirst hchiFirst
  have hdFirstSpan : dFirst ∈ AddSubgroup.closure
      (FTType1SeqIndFamily Lfirst : Set (ClassFunction Lfirst ℂ)) :=
    (AddSubgroup.closure _).sub_mem
      (AddSubgroup.subset_closure hchiFirst)
      (AddSubgroup.subset_closure
        (ctxFirst.R_spec.subcoherent_family.inverse_mem _ hchiFirst))
  have hpsiFirstVirtual : ClassFunction.IsVirtual psiFirst :=
    ctxFirst.R_spec.subcoherent_family.tau_virtual dFirst
      hdFirstSpan
      (FTType1InfrastructureInternal.inverseSubSupported chiFirst)
  have hpsiFirstInverse :
      ClassFunction.inverseLinear psiFirst = -psiFirst :=
    inverseDadeInverseSub ctxFirst hchiFirstVirtual hpsiFirstVirtual
  have halphaPsi : characterPairing alpha psiFirst = 0 := by
    have heq : characterPairing alpha psiFirst =
        characterPairing (ClassFunction.inverseLinear alpha) psiFirst := by
      rw [FTType1InfrastructureInternal.pairingSubLeft] at hdiffPair
      exact sub_eq_zero.mp hdiffPair
    have hneg :
        characterPairing (ClassFunction.inverseLinear alpha) psiFirst =
          -characterPairing alpha psiFirst := by
      calc
        characterPairing (ClassFunction.inverseLinear alpha) psiFirst =
            characterPairing alpha
              (ClassFunction.inverseLinear psiFirst) :=
          FTType1InfrastructureInternal.pairingInverseLeft alpha psiFirst
        _ = characterPairing alpha (-psiFirst) := by rw [hpsiFirstInverse]
        _ = -characterPairing alpha psiFirst := by
          rw [← neg_one_smul ℂ psiFirst, characterPairing_smul_right]
          ring
    have hanti : characterPairing alpha psiFirst =
        -characterPairing alpha psiFirst := heq.trans hneg
    have hsum : characterPairing alpha psiFirst +
        characterPairing alpha psiFirst = 0 := by
      calc
        characterPairing alpha psiFirst + characterPairing alpha psiFirst =
            -characterPairing alpha psiFirst +
              characterPairing alpha psiFirst :=
          congrArg (fun z ↦ z + characterPairing alpha psiFirst) hanti
        _ = 0 := neg_add_cancel _
    have htwice : (2 : ℂ) * characterPairing alpha psiFirst = 0 := by
      simpa [two_mul] using hsum
    exact (mul_eq_zero.mp htwice).resolve_left (by norm_num)
  have hsubFirst := ctxFirst.R_spec.subcoherent_family
  have halphaMem : alpha ∈ ctxFull.R chiFull := by
    rw [ctxFull.R_spec.flatten]
    exact Finset.mem_biUnion.mpr ⟨i, hi, halphaI⟩
  have halphaVirtual : ClassFunction.IsVirtual alpha :=
    ctxFull.R_spec.subcoherent_family.image_virtual
      chiFull hchiFull alpha halphaMem
  have halphaNorm : characterPairing alpha alpha = 1 := by
    simpa using ctxFull.R_spec.subcoherent_family.image_orthonormal
      chiFull hchiFull alpha halphaMem alpha halphaMem
  have hbetaVirtual : ClassFunction.IsVirtual beta :=
    hsubFirst.image_virtual chiFirst hchiFirst beta hbeta
  have hbetaNorm : characterPairing beta beta = 1 := by
    simpa using hsubFirst.image_orthonormal chiFirst hchiFirst
      beta hbeta beta hbeta
  by_contra hab
  obtain ⟨c, hc, hac⟩ :=
    FTType1InfrastructureInternal.virtualNormOneCollinear
      halphaVirtual halphaNorm hbetaVirtual hbetaNorm hab
  have hbetaSum : characterPairing beta
      (∑ nu ∈ ctxFirst.R chiFirst, nu) = 1 := by
    calc
      characterPairing beta (∑ nu ∈ ctxFirst.R chiFirst, nu) =
          ∑ nu ∈ ctxFirst.R chiFirst, characterPairing beta nu :=
        FTType1InfrastructureInternal.pairingFinsetSumRight
          beta (ctxFirst.R chiFirst) id
      _ = 1 := by
        rw [Finset.sum_eq_single beta]
        · exact hbetaNorm
        · intro nu hnu hne
          have hne' : beta ≠ nu := Ne.symm hne
          simpa [hne'] using hsubFirst.image_orthonormal
            chiFirst hchiFirst beta hbeta nu hnu
        · exact fun hnot ↦ (hnot hbeta).elim
  have hpsiFirstSum :
      psiFirst = ∑ nu ∈ ctxFirst.R chiFirst, nu :=
    hsubFirst.tau_inverse_sub chiFirst hchiFirst
  apply hc
  calc
    c = c * 1 := by rw [mul_one]
    _ = characterPairing alpha
        (∑ nu ∈ ctxFirst.R chiFirst, nu) := by
      rw [hac, characterPairing_smul_left, hbetaSum]
    _ = characterPairing alpha psiFirst := by rw [hpsiFirstSum]
    _ = 0 := halphaPsi

/-- `PFsection12.v: FTtype1_seqInd_ortho`, Peterfalvi (12.3). -/
theorem FTtype1_seqInd_ortho
    {L1 L2 : Subgroup G}
    (ctx1 : FTType1Context L1) (ctx2 : FTType1Context L2)
    (hnot : ¬ FTAmbientConjugate L1 L2) :
    FTType1ImageFamiliesOrthogonal ctx1 ctx2 := by
  intro chi1 hchi1 chi2 hchi2 alpha halpha beta hbeta
  rcases (FT_Dade_support_disjoint
      ctx1.maxL ctx2.maxL hnot).2.2 with h12 | h21
  · rw [characterPairing_comm]
    exact seqIndOrthogonalOriented ctx2 ctx1 h12
      hchi2 hchi1 hbeta halpha
  · exact seqIndOrthogonalOriented ctx1 ctx2 h21
      hchi1 hchi2 halpha hbeta

end

end Submission.OddOrder.PF
