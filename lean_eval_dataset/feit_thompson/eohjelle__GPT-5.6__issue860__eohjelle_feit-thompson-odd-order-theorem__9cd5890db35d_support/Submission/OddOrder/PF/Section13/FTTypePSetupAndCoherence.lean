import Submission.OddOrder.PF.Section11.FTType34Structure
import Submission.OddOrder.PF.Section12.FTType1Exclusion

/-!
# Peterfalvi Section 13: type-P setup and reduced-column coherence

This file develops the canonical Section 13 context from a maximal type-P
subgroup and proves the setup, no-induced alternative, and coherence theorem.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.BG.AppendixC
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise IsMulCommutative
  commutatorElement

open PTypeGaloisSubgroupAdaptersInternal

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance (priority := 10) ftTypePSetupFintypeOfFinite
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-! ## Canonical families and context -/

def ftTypePFittingFamily (S : Subgroup G) :
    Finset (ClassFunction S ℂ) :=
  seqIndT ((fittingWithin S).subgroupOf S)

/-- `PFsection13.v: irr_Ind_Fitting`. -/
def irr_Ind_Fitting (S : Subgroup G) : Set (ClassFunction S ℂ) :=
  {chi | IsIrreducibleCharacter S ℂ chi ∧ chi ∈ ftTypePFittingFamily S}

def ftTypePCoreFamily (S : Subgroup G) :
    Finset (ClassFunction S ℂ) :=
  seqIndD (k := ℂ) (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥

def ftTypePSupport0InS (S : Subgroup G) : Set S :=
  {x | (x : G) ∈ FTsupport0 S}

structure FTTypePSetupContext
    (S U W W₁ W₂ : Subgroup G)
    (defW : IsInternalDirectProductIn W₁ W₂ W) where
  maxS : S ∈ minSimple_max_groups (G := G)
  StypeP : of_typeP S U W W₁ W₂ defW

namespace FTTypePSetupContext

variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

abbrev notType5 (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    FTtype S ≠ 5 :=
  FTtype5_exclusion S ctx.maxS

abbrev ptypeCtx (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    PTypeFCoreContext S U W W₁ W₂ :=
  Ptype_Fcore_context ctx.maxS defW ctx.StypeP ctx.notType5

noncomputable abbrev factorFacts
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    PTypeFCoreFactorFacts ctx.ptypeCtx :=
  Ptype_Fcore_factor_facts ctx.ptypeCtx

noncomputable abbrev D
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    PTypeFactorActionData (ptypeFCoreFactor ctx.ptypeCtx) U W₁ :=
  Ptype_factor_action ctx.ptypeCtx ctx.factorFacts

abbrev actionHypotheses
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    PTypeFactorActionHypotheses ctx.D :=
  Ptype_factor_action_hypotheses ctx.ptypeCtx ctx.factorFacts

abbrev primeTI (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    PrimeTIHypothesis S (derivedWithin S) W W₁ W₂ defW :=
  FT_primeTI_hyp defW ctx.StypeP

noncomputable abbrev isoS
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    CyclicTIIsometryData (k := ℂ) ctx.primeTI.prime_cycTIhyp :=
  ctx.primeTI.prime_cycTIhyp.cyclicTIIsometryData

noncomputable abbrev primeDade
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    PrimeDadeHypothesis (⊤ : Subgroup G) S (derivedWithin S)
      (FTcore S) (FTsupport S) (FTsupport0 S) W W₁ W₂ defW :=
  FT_prDade_hyp defW ctx.maxS ctx.StypeP

noncomputable abbrev primeDadeF
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    PrimeDadeHypothesis (⊤ : Subgroup G) S (derivedWithin S)
      (Fitting_core S) (FTsupport S) (FTsupport0 S) W W₁ W₂ defW :=
  FT_prDade_hypF defW ctx.maxS ctx.StypeP

noncomputable abbrev isoG
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    CyclicTIIsometryData (k := ℂ) ctx.primeDade.prDade_cycTI :=
  ctx.primeDade.prDade_cycTI.cyclicTIIsometryData

noncomputable abbrev targetMap
    (_ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

noncomputable abbrev tau
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ctx.targetMap.comp (Dade (FT_Dade0_hyp S ctx.maxS))

noncomputable abbrev mu
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction S ℂ :=
  ctx.primeTI.primeTIRed ctx.isoS j

noncomputable abbrev delta
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ℤ :=
  ctx.primeTI.primeTISign ctx.isoS j

noncomputable abbrev eta
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction G ℂ :=
  ctx.targetMap (ctx.isoG.cyclicTIImage (i, j))

abbrev galoisAlternative
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : Prop :=
  typeP_Galois ctx.D

abbrev P (_ctx : FTTypePSetupContext S U W W₁ W₂ defW) : Subgroup G :=
  Fitting_core S

abbrev PU (_ctx : FTTypePSetupContext S U W W₁ W₂ defW) : Subgroup G :=
  derivedWithin S

abbrev H (_ctx : FTTypePSetupContext S U W W₁ W₂ defW) : Subgroup G :=
  fittingWithin S

abbrev H0 (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : Subgroup G :=
  Ptype_Fcore_kernel ctx.ptypeCtx

abbrev C (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : Subgroup G :=
  centralizerWithin U ctx.P

abbrev CInU (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : Subgroup U :=
  ctx.C.subgroupOf U

abbrev p (_ctx : FTTypePSetupContext S U W W₁ W₂ defW) : ℕ :=
  Nat.card W₂

abbrev q (_ctx : FTTypePSetupContext S U W W₁ W₂ defW) : ℕ :=
  Nat.card W₁

abbrev u (ctx : FTTypePSetupContext S U W W₁ W₂ defW) : ℕ :=
  ctx.CInU.index

private def asType34Base
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hnot2 : FTtype S ≠ 2) : FTType34Base S U W W₁ W₂ defW :=
  { MtypeP := ctx.StypeP
    notMtype2 := hnot2
    ptypeCtx := ctx.ptypeCtx }

end FTTypePSetupContext

/-! ## Transport across the top-subgroup equivalence -/

private noncomputable def ftTypePSourceMap :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

@[simp] private theorem ftTypePSourceMap_targetMap
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    ftTypePSourceMap (ctx.targetMap phi) = phi := by
  ext x
  simpa [ftTypePSourceMap, ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.symm_apply_apply x)

@[simp] private theorem ftTypePTargetMap_sourceMap
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction G ℂ) :
    ctx.targetMap (ftTypePSourceMap phi) = phi := by
  ext x
  simpa [ftTypePSourceMap, ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.apply_symm_apply x)

private theorem ftTypePTargetMap_pairing
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (ctx.targetMap phi) (ctx.targetMap psi) =
      characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [ClassFunction.comap_apply]

private theorem ftTypePSourceMap_pairing
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction G ℂ) :
    characterPairing (ftTypePSourceMap phi) (ftTypePSourceMap psi) =
      characterPairing phi psi := by
  rw [← ftTypePTargetMap_pairing ctx
    (ftTypePSourceMap phi) (ftTypePSourceMap psi)]
  simp

private theorem ftTypePTargetMap_virtual
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {phi : ClassFunction (⊤ : Subgroup G) ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (ctx.targetMap phi) := by
  rcases hphi with ⟨z, hz⟩
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.symm.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]

private theorem ftTypePSourceMap_virtual
    {phi : ClassFunction G ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (ftTypePSourceMap phi) := by
  rcases hphi with ⟨z, hz⟩
  refine ⟨VirtualCharacter.comap Subgroup.topEquiv.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]
  rfl

private theorem ftTypePCoherent_targetMap
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {calS : Set (ClassFunction S ℂ)} {A : Set S}
    {sigma : ClassFunction S ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ}
    (hcoh : coherent calS A sigma) :
    coherent calS A (ctx.targetMap.comp sigma) := by
  rcases hcoh with ⟨nu, hnu⟩
  refine ⟨ctx.targetMap.comp nu, ?_⟩
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro phi hphi psi hpsi
    simpa [LinearMap.comp_apply] using
      (ftTypePTargetMap_pairing ctx (nu phi) (nu psi)).trans
        (hnu.isometry phi hphi psi hpsi)
  · intro phi hphi
    exact ftTypePTargetMap_virtual ctx (hnu.mapsToVirtual phi hphi)
  · intro phi hphi hsupp
    simpa [LinearMap.comp_apply, hnu.agrees phi hphi hsupp]

private theorem ftTypePCoherentWith_targetMap
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {calS : Set (ClassFunction S ℂ)} {A : Set S}
    {sigma nu : ClassFunction S ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ}
    (hcoh : coherent_with calS A sigma nu) :
    coherent_with calS A (ctx.targetMap.comp sigma)
      (ctx.targetMap.comp nu) := by
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro phi hphi psi hpsi
    simpa [LinearMap.comp_apply] using
      (ftTypePTargetMap_pairing ctx (nu phi) (nu psi)).trans
        (hcoh.isometry phi hphi psi hpsi)
  · intro phi hphi
    exact ftTypePTargetMap_virtual ctx (hcoh.mapsToVirtual phi hphi)
  · intro phi hphi hsupp
    simpa [LinearMap.comp_apply, hcoh.agrees phi hphi hsupp]

private theorem ftTypePCoherentWith_sourceMap
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {calS : Set (ClassFunction S ℂ)} {A : Set S}
    {sigma nu : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hcoh : coherent_with calS A sigma nu) :
    coherent_with calS A (ftTypePSourceMap.comp sigma)
      (ftTypePSourceMap.comp nu) := by
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro phi hphi psi hpsi
    simpa [LinearMap.comp_apply] using
      (ftTypePSourceMap_pairing ctx (nu phi) (nu psi)).trans
        (hcoh.isometry phi hphi psi hpsi)
  · intro phi hphi
    exact ftTypePSourceMap_virtual (hcoh.mapsToVirtual phi hphi)
  · intro phi hphi hsupp
    simpa [LinearMap.comp_apply, hcoh.agrees phi hphi hsupp]

/-! ## Factor and kernel calculations -/

private theorem ptypeFCore_kernel_eq_bot_of_factor_card_pf13
    {S U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext S U W W₁ W₂)
    (hcard : Nat.card (ptypeFCoreFactor ctx) = Nat.card (Fitting_core S)) :
    Ptype_Fcore_kernel ctx = ⊥ := by
  let K := (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core S)
  have hmul :
      Nat.card (Fitting_core S) =
        Nat.card (ptypeFCoreFactor ctx) * Nat.card K :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup K
  have hK : Nat.card K = 1 := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.card_pos (α := ptypeFCoreFactor ctx))
    calc
      Nat.card (ptypeFCoreFactor ctx) * Nat.card K =
          Nat.card (Fitting_core S) := hmul.symm
      _ = Nat.card (ptypeFCoreFactor ctx) := hcard.symm
      _ = Nat.card (ptypeFCoreFactor ctx) * 1 := (Nat.mul_one _).symm
  apply Subgroup.eq_bot_of_card_eq
  rw [← MathlibSupport.natCard_subgroupOf_eq
    (Ptype_Fcore_kernel_lt ctx).le]
  exact hK

private theorem mem_ptypeFCoreAction_ker_iff_pf13
    {S U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext S U W W₁ W₂) (u : U) :
    u ∈ (ptypeFCoreAction ctx).ker ↔
      ∀ h : G, h ∈ Fitting_core S →
        ⁅(u : G), h⁆ ∈ Ptype_Fcore_kernel ctx := by
  unfold ptypeFCoreAction
  exact mem_ker_subgroupConjugationFactorHom_iff _ _ _ _ _ u

private theorem ptypeFcompl_kernel_eq_centralizer_of_kernel_eq_bot_pf13
    {S U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext S U W W₁ W₂)
    (hK : Ptype_Fcore_kernel ctx = ⊥) :
    Ptype_Fcompl_kernel ctx = centralizerWithin U (Fitting_core S) := by
  rw [Ptype_Fcompl_kernel]
  ext x
  constructor
  · rintro ⟨u, hu, rfl⟩
    refine mem_centralizerWithin.mpr ⟨u.property, ?_⟩
    intro h hh
    have hcomm := (mem_ptypeFCoreAction_ker_iff_pf13 ctx u).mp hu h hh
    rw [hK] at hcomm
    exact (commutatorElement_eq_one_iff_mul_comm.mp
      (Subgroup.mem_bot.mp hcomm)).symm
  · intro hx
    rcases mem_centralizerWithin.mp hx with ⟨hxU, hxcent⟩
    let u : U := ⟨x, hxU⟩
    refine ⟨u, (mem_ptypeFCoreAction_ker_iff_pf13 ctx u).mpr ?_, rfl⟩
    intro h hh
    rw [hK]
    exact Subgroup.mem_bot.mpr
      (commutatorElement_eq_one_iff_mul_comm.mpr (hxcent h hh).symm)

/-! ## Peterfalvi (13.2) and the structural part of (13.3) -/

/-- `PFsection13.v: Ptype_factor_prime`. -/
theorem Ptype_factor_prime
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ptypeFactorPrime ctx.ptypeCtx = ctx.p :=
  def_Ptype_factor_prime ctx.ptypeCtx
    (FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP).2

@[simp] private theorem ftTypeP_factorAction_p_pf13
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.p = ctx.p := by
  rw [Ptype_factor_action_p, Ptype_factor_prime ctx]

@[simp] private theorem ftTypeP_factorAction_q_pf13
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.q = ctx.q :=
  rfl

/-- `PFsection13.v: Ptype_Fcore_kernel_trivial`. -/
theorem Ptype_Fcore_kernel_trivial
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.H0 = ⊥ := by
  by_cases htype2 : FTtype S = 2
  · have hfactor : Nat.card (ptypeFCoreFactor ctx.ptypeCtx) =
        ctx.p ^ ctx.q := by
      rw [ctx.factorFacts.factor_card, Ptype_factor_prime ctx]
    have hcore := typeII_IV_core ctx.ptypeCtx
    rw [TypeIIIVCoreConclusion, if_pos htype2] at hcore
    exact ptypeFCore_kernel_eq_bot_of_factor_card_pf13 ctx.ptypeCtx
      (hfactor.trans hcore.2.symm)
  · exact (FTtype34_Fcore_kernel_trivial
      (ctx.asType34Base htype2)).H0_eq_bot

private theorem Ptype_Fcompl_kernel_cent_pf13
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Ptype_Fcompl_kernel ctx.ptypeCtx = ctx.C := by
  by_cases htype2 : FTtype S = 2
  · exact ptypeFcompl_kernel_eq_centralizer_of_kernel_eq_bot_pf13
      ctx.ptypeCtx (Ptype_Fcore_kernel_trivial ctx)
  · exact Ptype_Fcompl_kernel_cent (ctx.asType34Base htype2)

private theorem ftTypeP_actionKernel_map_eq_C_pf13
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.C.map U.subtype = ctx.C := by
  change (ptypeFCoreAction ctx.ptypeCtx).ker.map U.subtype = ctx.C
  exact Ptype_Fcompl_kernel_cent_pf13 ctx

private theorem ftTypeP_actionKernel_eq_CInU_pf13
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.C = ctx.CInU := by
  apply Subgroup.map_injective U.subtype_injective
  rw [ftTypeP_actionKernel_map_eq_C_pf13 ctx]
  exact (Subgroup.map_subgroupOf_eq_of_le
    (centralizerWithin_le_left U ctx.P)).symm

private theorem ftTypeP_actionFactorCard_eq_u_pf13
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    pTypeActionFactorCard ctx.D = ctx.u := by
  unfold pTypeActionFactorCard
  letI : ctx.D.C.Normal := ctx.D.C_normal
  change Nat.card (U ⧸ ctx.D.C) = ctx.CInU.index
  rw [← ctx.D.C.index_eq_card, ftTypeP_actionKernel_eq_CInU_pf13 ctx]

private theorem ftTypeP_type_and_complement_facts
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    (FTtype S = 2 ∨ FTtype S = 3) ∧
      (ctx.q < ctx.p → FTtype S = 2) ∧
      PTypeFrobeniusProduct U W₁ ∧
      IsMulCommutative U := by
  by_cases htype2 : FTtype S = 2
  · refine ⟨Or.inl htype2, fun _ ↦ htype2,
      Ptype_compl_Frobenius ctx.ptypeCtx, ?_⟩
    exact (compl_of_typeII S U W W₁ W₂ defW
      ctx.maxS ctx.StypeP htype2).2.1
  · have h34 := FTtype34_structure (ctx.asType34Base htype2)
    have hpq : ctx.p < ctx.q := h34.2.1
    refine ⟨Or.inr h34.2.2.1, ?_,
      Ptype_compl_Frobenius ctx.ptypeCtx, ?_⟩
    · intro hqp
      omega
    · exact (compl_of_typeIII S U W W₁ W₂ defW
        ctx.maxS ctx.StypeP h34.2.2.1).2.1

private theorem ftTypeP_fcore_prime_facts
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IsElementaryAbelianGroup ctx.p ctx.P ∧
      Nat.card ctx.P = ctx.p ^ ctx.q := by
  by_cases htype2 : FTtype S = 2
  · have hII := FTtypeII_prime_facts S U W W₁ W₂ defW
      ctx.maxS ctx.StypeP htype2
    exact ⟨hII.1, hII.2.1⟩
  · have h34 := FTtype34_Fcore_kernel_trivial
      (ctx.asType34Base htype2)
    exact ⟨h34.H_elementaryAbelian, h34.card_H_eq⟩

private theorem ftTypeP_pow_pred_le_nU {p q : ℕ} (hq : 0 < q) :
    p ^ (q - 1) ≤ nU p q := by
  rw [nU]
  apply Finset.single_le_sum (fun i _ ↦ Nat.zero_le (p ^ i))
  simp only [Finset.mem_range]
  omega

private theorem ftTypeP_complement_index_bound
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.u ≤ (ctx.p ^ ctx.q - 1) / (ctx.p - 1) := by
  let D := ctx.D
  have hu : ctx.u = pTypeActionFactorCard D :=
    (ftTypeP_actionFactorCard_eq_u_pf13 ctx).symm
  by_cases hGalois : typeP_Galois D
  · let data := typeP_Galois_P ctx.actionHypotheses hGalois
    letI : D.C.Normal := D.C_normal
    have hnUpos : 0 < nU D.p D.q :=
      lt_of_lt_of_le (pow_pos D.p_prime.pos (D.q - 1))
        (ftTypeP_pow_pred_le_nU D.q_prime.pos)
    have hdiv : Nat.card (U ⧸ D.C) ∣ nU D.p D.q := by
      rw [nU_eq_div_of_prime D.p_prime]
      exact data.complement_factor_dvd
    calc
      ctx.u = Nat.card (U ⧸ D.C) := hu.trans rfl
      _ ≤ nU D.p D.q := Nat.le_of_dvd hnUpos hdiv
      _ = (D.p ^ D.q - 1) / (D.p - 1) :=
        nU_eq_div_of_prime D.p_prime
      _ = (ctx.p ^ ctx.q - 1) / (ctx.p - 1) := by
        dsimp only [D]
        rw [ftTypeP_factorAction_p_pf13 ctx,
          ftTypeP_factorAction_q_pf13 ctx]
  · let data := typeP_Galois_Pn ctx.actionHypotheses hGalois
    let a := (pointwiseActionKernel D.U_action data.H₁).index
    have ha0 : a ≠ 0 := by
      dsimp only [a]
      exact Subgroup.index_ne_zero_of_finite
    letI : NeZero a := ⟨ha0⟩
    letI : D.C.Normal := D.C_normal
    obtain ⟨iota, hiota⟩ := data.complement_factor_vector
    have hquotient : Nat.card (U ⧸ D.C) ≤ a ^ (D.q - 1) := by
      calc
        Nat.card (U ⧸ D.C) ≤
            Nat.card (Multiplicative (Fin (D.q - 1) → ZMod a)) :=
          Nat.card_le_card_of_injective iota hiota
        _ = a ^ (D.q - 1) := by
          rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
            Nat.card_fin, Nat.card_zmod]
    have ha : a ≤ D.p - 1 :=
      Nat.le_of_dvd (Nat.sub_pos_of_lt D.p_prime.one_lt)
        data.index_dvd_prime_pred
    have hpred : (D.p - 1) ^ (D.q - 1) ≤ nU D.p D.q :=
      (Nat.pow_le_pow_left (Nat.sub_le D.p 1) (D.q - 1)).trans
        (ftTypeP_pow_pred_le_nU D.q_prime.pos)
    calc
      ctx.u = Nat.card (U ⧸ D.C) := hu.trans rfl
      _ ≤ a ^ (D.q - 1) := hquotient
      _ ≤ (D.p - 1) ^ (D.q - 1) :=
        Nat.pow_le_pow_left ha (D.q - 1)
      _ ≤ nU D.p D.q := hpred
      _ = (D.p ^ D.q - 1) / (D.p - 1) :=
        nU_eq_div_of_prime D.p_prime
      _ = (ctx.p ^ ctx.q - 1) / (ctx.p - 1) := by
        dsimp only [D]
        rw [ftTypeP_factorAction_p_pf13 ctx,
          ftTypeP_factorAction_q_pf13 ctx]

private theorem ftTypeP_coreKernelDerivedComplement_eq_bot
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    pTypeCoreKernelDerivedComplement ctx.ptypeCtx = ⊥ := by
  letI : IsMulCommutative U :=
    (ftTypeP_type_and_complement_facts ctx).2.2.2
  let D := ctx.D
  have hcomm : _root_.commutator D.C = ⊥ :=
    _root_.commutator_eq_bot (G := D.C)
  have hH0 :
      pTypeH0InDerived S (derivedWithin S)
          (Ptype_Fcore_kernel ctx.ptypeCtx) = ⊥ := by
    ext x
    simp [pTypeH0InDerived, Ptype_Fcore_kernel_trivial ctx]
  have hderived :
      pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype) = ⊥ := by
    simp [pTypeDerivedComplementInMaximal, hcomm]
  have hnested :
      ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf S).subgroupOf
            (pTypeHUInMaximal S (derivedWithin S)) = ⊥ := by
    ext x
    simp [hderived]
  change
    pTypeH0InDerived S (derivedWithin S)
          (Ptype_Fcore_kernel ctx.ptypeCtx) ⊔
        ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf S).subgroupOf
            (pTypeHUInMaximal S (derivedWithin S)) = ⊥
  rw [hH0, hnested]
  simp

private theorem ftTypeP_core_coherence
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    coherent
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau := by
  have hcoh :
      coherent
        (↑(pTypeCoreFamilyOfContext ctx.ptypeCtx) :
          Set (ClassFunction S ℂ))
        (nonidentitySet S)
        (Dade (FT_Dade0_hyp S ctx.maxS)) := by
    simpa only using
      Ptype_core_coherence ctx.maxS defW ctx.StypeP ctx.notType5
  unfold pTypeCoreFamilyOfContext at hcoh
  rw [ftTypeP_coreKernelDerivedComplement_eq_bot ctx] at hcoh
  apply ftTypePCoherent_targetMap ctx
  simpa only [ftTypePCoreFamily, pTypeCoreDerived,
    pTypeCoreFitting] using hcoh

private theorem mem_elementCentralizer_of_commute13
    {Q : Type} [Group Q] {x y : Q} (hxy : Commute x y) :
    x ∈ Subgroup.centralizer (Subgroup.zpowers y : Set Q) := by
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, rfl⟩
  exact (hxy.zpow_right n).symm

private theorem centralizer_frobeniusKernel_le13
    {Q : Type} [Group Q] [Finite Q]
    {K R : Subgroup Q}
    (hFrob : IsFrobeniusDecomposition K R)
    {z : Q} (hzK : z ∈ K) (hzOne : z ≠ 1) :
    Subgroup.centralizer (Subgroup.zpowers z : Set Q) ≤ K := by
  intro x hx
  by_contra hxK
  obtain ⟨k, r, hrR, hrx⟩ :=
    hFrob.exists_kernel_conjugate_complement_of_not_mem hxK
  have hrx' : (k : Q) * r * (k : Q)⁻¹ = x := by
    simpa [MulAut.conj_apply] using hrx
  let rR : R := ⟨r, hrR⟩
  have hrOne : rR ≠ 1 := by
    intro hr
    apply hxK
    have hrQ : r = 1 := congrArg Subtype.val hr
    have hxOne : x = 1 := by
      rw [← hrx', hrQ]
      simp
    simpa [hxOne]
  have hzConj : (k : Q)⁻¹ * z * (k : Q) ∈ K := by
    simpa using hFrob.kernel_normal.conj_mem z hzK (k : Q)⁻¹
  let zK : K := ⟨(k : Q)⁻¹ * z * (k : Q), hzConj⟩
  have hzKOne : zK ≠ 1 := by
    intro hz
    apply hzOne
    have hzQ := congrArg Subtype.val hz
    dsimp only [zK] at hzQ
    calc
      z = (k : Q) * ((k : Q)⁻¹ * z * (k : Q)) * (k : Q)⁻¹ := by
        group
      _ = 1 := by rw [hzQ]; simp
  have hxcomm : Commute x z :=
    (Subgroup.mem_centralizer_iff.mp hx z
      (Subgroup.mem_zpowers z)).symm
  have hxfix : x * z * x⁻¹ = z := by
    rw [hxcomm.eq]
    simp
  have hrfix : (rR : Q) * (zK : Q) * (rR : Q)⁻¹ = (zK : Q) := by
    change r * ((k : Q)⁻¹ * z * (k : Q)) * r⁻¹ =
      (k : Q)⁻¹ * z * (k : Q)
    calc
      r * ((k : Q)⁻¹ * z * (k : Q)) * r⁻¹ =
          (k : Q)⁻¹ * (((k : Q) * r * (k : Q)⁻¹) * z *
            ((k : Q) * r * (k : Q)⁻¹)⁻¹) * (k : Q) := by
        group
      _ = (k : Q)⁻¹ * (x * z * x⁻¹) * (k : Q) := by rw [hrx']
      _ = (k : Q)⁻¹ * z * (k : Q) := by rw [hxfix]
  exact hzKOne (hFrob.fixedPointFree rR hrOne zK hrfix)

private theorem summaryFrobeniusData_isFrobeniusIn13
    {L : Subgroup G} (data : BGSummaryIIFrobeniusData L) :
    IsFrobeniusIn (Fitting_core L) data.complement L := by
  have hcore : Fitting_core L ≤ L := Fcore_sub L
  have hsup : Fitting_core L ⊔ data.complement = L := by
    apply le_antisymm (sup_le hcore data.complement_le)
    intro x hx
    let xL : L := ⟨x, hx⟩
    have htop : xL ∈ (⊤ : Subgroup L) := Subgroup.mem_top xL
    rw [← data.frobenius.isComplement.sup_eq_top,
      ← Subgroup.subgroupOf_sup hcore data.complement_le] at htop
    exact htop
  have hsd : IsInternalSemidirectProductIn
      (Fitting_core L) data.complement L :=
    ⟨hcore, data.complement_le, data.frobenius.kernel_normal,
      data.frobenius.isComplement⟩
  refine ⟨hsup, ?_⟩
  rw [hsup]
  exact ⟨hsd, data.frobenius⟩

private theorem ftTypeP_support0_normalizedTI
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IsNormalizedTI (FTsupport0 S) (⊤ : Subgroup G) S := by
  apply isNormalizedTI_iff_mem_conj.mpr
  refine ⟨Set.nonempty_iff_ne_empty.mpr (FTsupp0_neq0 ctx.maxS), le_top, ?_⟩
  intro x hx z _hz
  constructor
  · intro hxz
    have hxz0 : conjugateElement16 x z⁻¹ ∈ FTsupport0 S := by
      simpa [conjugateElement16, MulAut.conj_apply, mul_assoc] using hxz
    let facts := FTsupport_facts S ctx.maxS
    obtain ⟨y, hyS, hfusion⟩ := facts.fusion_control x hx z⁻¹ hxz0
    have hcentral : centralizerOfElement8 x ≤ S := by
      by_contra hnot
      let data := facts.element_data x ⟨hx, hnot⟩
      let N : Subgroup G := elementNormalizer15 x
      have hNmax : N ∈ minSimple_max_groups (G := G) :=
        (mem_uniq_mmax data.unique_maximal_centralizer).1
      rcases data.type_one_or_two with htype1 | htype2
      · have hxA1 := data.support_not_support1.1
        change x ∈ ⋃ y ∈ FTsupport1 N,
          subgroupNonidentity
            (elementCentralizerWithin (FTder N) y) at hxA1
        obtain ⟨y, hxA1⟩ := Set.mem_iUnion.mp hxA1
        obtain ⟨hyA1, hxy⟩ := Set.mem_iUnion.mp hxA1
        have hyCore : y ∈ subgroupNonidentity (Fitting_core N) := by
          rwa [FTsupp1_type1 N htype1] at hyA1
        have hxN : x ∈ N := by
          simpa [FTder, ftDerived, N, htype1] using hxy.1.1
        have hcomm : Commute x y :=
          (Subgroup.mem_centralizer_iff.mp hxy.1.2 y
            (Subgroup.mem_zpowers y)).symm
        obtain ⟨E, hFrob⟩ := FTtype1_Frobenius N hNmax htype1
        let J : Subgroup G := Fitting_core N ⊔ E
        have hxJ : x ∈ J := by
          change x ∈ Fitting_core N ⊔ E
          rw [hFrob.1]
          exact hxN
        let xJ : J := ⟨x, hxJ⟩
        let yJ : J := ⟨y, by
          change y ∈ Fitting_core N ⊔ E
          exact (show Fitting_core N ≤ Fitting_core N ⊔ E from
            le_sup_left) hyCore.1⟩
        have hyKernel : yJ ∈ (Fitting_core N).subgroupOf J := hyCore.1
        have hyOne : yJ ≠ 1 := by
          intro hy
          exact hyCore.2 (congrArg (fun t : J ↦ (t : G)) hy)
        have hxCent : xJ ∈ Subgroup.centralizer
            (Subgroup.zpowers yJ : Set J) := by
          rw [Subgroup.mem_centralizer_iff]
          intro t ht
          rcases Subgroup.mem_zpowers_iff.mp ht with ⟨n, rfl⟩
          apply Subtype.ext
          exact (hcomm.zpow_right n).symm.eq
        have hxKernel : xJ ∈ (Fitting_core N).subgroupOf J :=
          centralizer_frobeniusKernel_le13 hFrob.2.2
            hyKernel hyOne hxCent
        apply data.support_not_support1.2
        rw [FTsupp1_type1 N htype1]
        exact ⟨hxKernel, hxy.2⟩
      · let fdata := data.typeTwo_frobenius htype2
        have hfrob := summaryFrobeniusData_isFrobeniusIn13 fdata
        exact (typePF_exclusion S U W W₁ W₂ fdata.complement
          defW ctx.StypeP)
          (Frobenius_of_typeF S fdata.complement hfrob)
    have hfusion' : z⁻¹ * x * z = y * x * y⁻¹ := by
      simpa [conjugateElement16, MulAut.conj_apply] using hfusion
    have hcomm : Commute (y⁻¹ * z⁻¹) x := by
      show (y⁻¹ * z⁻¹) * x = x * (y⁻¹ * z⁻¹)
      calc
        (y⁻¹ * z⁻¹) * x = y⁻¹ * (z⁻¹ * x * z) * z⁻¹ := by
          group
        _ = y⁻¹ * (y * x * y⁻¹) * z⁻¹ := by rw [hfusion']
        _ = x * (y⁻¹ * z⁻¹) := by group
    have hyzS : y⁻¹ * z⁻¹ ∈ S :=
      hcentral (mem_elementCentralizer_of_commute13 hcomm)
    rw [show z = (y⁻¹ * z⁻¹)⁻¹ * y⁻¹ by group]
    exact S.mul_mem (S.inv_mem hyzS) (S.inv_mem hyS)
  · intro hzS
    have hnorm : z ∈ Subgroup.normalizer (FTsupport0 S) :=
      (FTsupp0_norm S) hzS
    exact ((Subgroup.mem_set_normalizer_iff''.mp hnorm) x).1 hx

private theorem ftTypeP_targetMap_eq_induce_top
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    ctx.targetMap phi = ClassFunction.induce (⊤ : Subgroup G) phi := by
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
  simp only [ClassFunction.comap_apply, Finset.sum_const,
    nsmul_eq_mul, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card,
    Nat.card_congr Subgroup.topEquiv.toEquiv]
  have hne : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hne]
  rfl

private theorem ftTypeP_tau_eq_induce
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hTI : IsNormalizedTI (FTsupport0 S) (⊤ : Subgroup G) S)
    (phi : ClassFunction S ℂ)
    (hphi : phi ∈ ClassFunction.supportedOn (ftTypePSupport0InS S)) :
    ctx.tau phi = ClassFunction.induce S phi := by
  have hDade := Dade_Ind (FT_Dade0_hyp S ctx.maxS) hTI phi
    (by simpa only [ftTypePSupport0InS] using hphi)
  calc
    ctx.tau phi =
        ctx.targetMap (Dade (FT_Dade0_hyp S ctx.maxS) phi) := rfl
    _ = ctx.targetMap
        (ClassFunction.induce (S.subgroupOf (⊤ : Subgroup G))
          (ClassFunction.toSubgroupOf S (⊤ : Subgroup G) le_top phi)) :=
      congrArg ctx.targetMap hDade
    _ = ClassFunction.induce (⊤ : Subgroup G)
        (ClassFunction.induce (S.subgroupOf (⊤ : Subgroup G))
          (ClassFunction.toSubgroupOf S (⊤ : Subgroup G) le_top phi)) :=
      ftTypeP_targetMap_eq_induce_top ctx _
    _ = ClassFunction.induce S phi :=
      ClassFunction.induce_trans S (⊤ : Subgroup G) le_top phi

/-- `PFsection13.v: FTtypeP_facts`, as its direct source conjunction. -/
theorem FTtypeP_facts
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    (FTtype S = 2 ∨ FTtype S = 3) ∧
      (ctx.q < ctx.p → FTtype S = 2) ∧
      PTypeFrobeniusProduct U W₁ ∧
      IsMulCommutative U ∧
      IsElementaryAbelianGroup ctx.p ctx.P ∧
      Nat.card ctx.P = ctx.p ^ ctx.q ∧
      ctx.u ≤ (ctx.p ^ ctx.q - 1) / (ctx.p - 1) ∧
      coherent
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
        (nonidentitySet S) ctx.tau ∧
      IsNormalizedTI (FTsupport0 S) (⊤ : Subgroup G) S ∧
      ∀ phi : ClassFunction S ℂ,
        phi ∈ ClassFunction.supportedOn (ftTypePSupport0InS S) →
          ctx.tau phi = ClassFunction.induce S phi := by
  have hstruct := ftTypeP_type_and_complement_facts ctx
  have hcore := ftTypeP_fcore_prime_facts ctx
  have hTI := ftTypeP_support0_normalizedTI ctx
  refine ⟨hstruct.1, hstruct.2.1, hstruct.2.2.1, hstruct.2.2.2,
    hcore.1, hcore.2, ftTypeP_complement_index_bound ctx,
    ftTypeP_core_coherence ctx, hTI, ?_⟩
  intro phi hphi
  exact ftTypeP_tau_eq_induce ctx hTI phi hphi

/-- `PFsection13.v: FTseqInd_TIred`. -/
theorem FTseqInd_TIred
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ctx.mu j ∈ ftTypePCoreFamily S := by
  change ctx.mu j ∈
    seqIndD (k := ℂ) (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥
  change ctx.primeTI.primeTIRed ctx.isoS j ∈
    seqIndD (k := ℂ) (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥
  rw [← ctx.primeTI.cfInd_prTIres ctx.isoS j]
  apply seqIndP.mpr
  refine ⟨ctx.primeTI.primeTI_Ires ctx.isoS j, ?_, rfl⟩
  rw [mem_Iirr_kerD]
  exact ⟨bot_le, ctx.primeDadeF.cfker_prTIres ctx.isoS j hj⟩

/-! ## The Fitting subgroup and induced degrees -/

private theorem ftTypeP_directProductCard
    {A B K : Subgroup G} (h : IsInternalDirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.left_le,
    MathlibSupport.natCard_subgroupOf_eq h.right_le] using
      h.complement.card_mul

private theorem ftTypeP_semidirectProductCard
    {A B K : Subgroup G} (h : IsInternalSemidirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.1,
    MathlibSupport.natCard_subgroupOf_eq h.2.1] using
      h.2.2.2.card_mul

private theorem ftTypeP_directProductSup
    {A B K : Subgroup G} (h : IsInternalDirectProductIn A B K) :
    A ⊔ B = K := by
  apply le_antisymm (sup_le h.left_le h.right_le)
  intro x hx
  obtain ⟨⟨a, b⟩, hab⟩ := h.complement.2 ⟨x, hx⟩
  have habG : (a : G) * (b : G) = x := congrArg Subtype.val hab
  rw [← habG]
  exact Subgroup.mul_mem_sup a.property b.property

private theorem ftTypeP_subgroupOf_isMulCommutative
    {Q : Type} [Group Q] {H L : Subgroup Q}
    (hHL : H ≤ L) (hH : IsMulCommutative H) :
    IsMulCommutative (H.subgroupOf L) := by
  let e : H.subgroupOf L ≃* H := Subgroup.subgroupOfEquivOfLe hHL
  apply isMulCommutative_iff.mpr
  intro x y
  exact e.injective (isMulCommutative_iff.mp hH (e x) (e y))

private theorem ftTypeP_irreducible_degree_one
    {Q : Type} [Group Q] [Fintype Q] [IsMulCommutative Q]
    (chi : IrreducibleCharacter Q ℂ) :
    chi 1 = 1 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    MathlibSupport.representation_isIrreducible_of_simple_fdRep
      chi.representation
  rw [IrreducibleCharacter.apply_one_eq_finrank,
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      chi.representation.ρ]
  norm_num

/-- `PFsection13.v: FTtypeP_Fitting_abelian`. -/
theorem FTtypeP_Fitting_abelian
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IsMulCommutative ctx.H := by
  obtain ⟨_, _, _, hUcomm, hPelem, _, _, _, _, _⟩ :=
    FTtypeP_facts ctx
  letI : IsMulCommutative ctx.P := hPelem.commutative
  letI : IsMulCommutative U := hUcomm
  have hCU : ctx.C ≤ U := centralizerWithin_le_left U ctx.P
  letI : IsMulCommutative (ctx.C.subgroupOf U) := inferInstance
  letI : IsMulCommutative ctx.C :=
    FTContextInternal.isMulCommutative_of_mulEquiv8
      (K := ctx.C.subgroupOf U) (L := ctx.C) inferInstance
      (Subgroup.subgroupOfEquivOfLe hCU)
  letI : IsMulCommutative (ctx.P × ctx.C) := inferInstance
  exact FTContextInternal.isMulCommutative_of_mulEquiv8
    (K := ctx.P × ctx.C) (L := ctx.H) inferInstance
    (typeP_context S U W W₁ W₂ defW
      ctx.StypeP).fitting_decomposition.mulEquiv

private theorem ftTypeP_fitting_index_eq_uq
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    (ctx.H.subgroupOf S).index = ctx.u * ctx.q := by
  have hfit :=
    (typeP_context S U W W₁ W₂ defW ctx.StypeP).fitting_decomposition
  have hinner : IsInternalSemidirectProductIn ctx.P U ctx.PU :=
    ctx.StypeP.2.1.2.2.2
  have houter : IsInternalSemidirectProductIn ctx.PU W₁ S :=
    ctx.StypeP.1.2.2.2
  have hH : Nat.card ctx.P * Nat.card ctx.C = Nat.card ctx.H :=
    ftTypeP_directProductCard hfit
  have hPU : Nat.card ctx.P * Nat.card U = Nat.card ctx.PU :=
    ftTypeP_semidirectProductCard hinner
  have hS : Nat.card ctx.PU * Nat.card W₁ = Nat.card S :=
    ftTypeP_semidirectProductCard houter
  have hC : Nat.card ctx.CInU = Nat.card ctx.C :=
    MathlibSupport.natCard_subgroupOf_eq
      (centralizerWithin_le_left U ctx.P)
  have hu : ctx.u * Nat.card ctx.C = Nat.card U := by
    change ctx.CInU.index * Nat.card ctx.C = Nat.card U
    simpa only [hC] using ctx.CInU.index_mul_card
  apply Nat.mul_right_cancel (Nat.card_pos (α := ctx.H))
  calc
    (ctx.H.subgroupOf S).index * Nat.card ctx.H =
        (ctx.H.subgroupOf S).index * Nat.card (ctx.H.subgroupOf S) := by
      rw [MathlibSupport.natCard_subgroupOf_eq (fittingWithin_le S)]
    _ = Nat.card S := (ctx.H.subgroupOf S).index_mul_card
    _ = Nat.card ctx.PU * Nat.card W₁ := hS.symm
    _ = (Nat.card ctx.P * Nat.card U) * ctx.q := by rw [hPU]
    _ = (Nat.card ctx.P * (ctx.u * Nat.card ctx.C)) * ctx.q := by rw [hu]
    _ = (ctx.u * ctx.q) * (Nat.card ctx.P * Nat.card ctx.C) := by ac_rfl
    _ = (ctx.u * ctx.q) * Nat.card ctx.H := by rw [hH]

/-- `PFsection13.v: FTtypeP_Ind_Fitting_1`. -/
theorem FTtypeP_Ind_Fitting_1
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (hlambda : lambda ∈ ftTypePFittingFamily S) :
    lambda 1 = ((ctx.u * ctx.q : ℕ) : ℂ) := by
  obtain ⟨theta, _, rfl⟩ := seqIndP.mp hlambda
  letI : IsMulCommutative ctx.H := FTtypeP_Fitting_abelian ctx
  letI : IsMulCommutative (ctx.H.subgroupOf S) :=
    ftTypeP_subgroupOf_isMulCommutative
      (fittingWithin_le S) (FTtypeP_Fitting_abelian ctx)
  rw [ClassFunction.induce_one, ftTypeP_irreducible_degree_one theta,
    ftTypeP_fitting_index_eq_uq ctx, mul_one]

private theorem ftTypeP_HCInMaximal_eq_fitting
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    pTypeHCInMaximal S ctx.P U W₁ ctx.D = ctx.H.subgroupOf S := by
  have hinner : IsInternalSemidirectProductIn ctx.P U ctx.PU :=
    ctx.StypeP.2.1.2.2.2
  have houter : IsInternalSemidirectProductIn ctx.PU W₁ S :=
    ctx.StypeP.1.2.2.2
  have hUS : U ≤ S := hinner.2.1.trans houter.1
  have hCS : ctx.C ≤ S :=
    (centralizerWithin_le_left U ctx.P).trans hUS
  have hsup : ctx.P ⊔ ctx.C = ctx.H :=
    ftTypeP_directProductSup
      (typeP_context S U W W₁ W₂ defW
        ctx.StypeP).fitting_decomposition
  rw [pTypeHCInMaximal, ftTypeP_actionKernel_map_eq_C_pf13 ctx,
    ← Subgroup.subgroupOf_sup (Fcore_sub S) hCS, hsup]

/-- `PFsection13.v: FTprTIred_Ind_Fitting`. -/
theorem FTprTIred_Ind_Fitting
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ctx.mu j ∈ ftTypePFittingFamily S := by
  have hdata := typeP_reducible_core_Ind S U W W₁ W₂ defW
    ctx.maxS ctx.StypeP ctx.notType5
  dsimp only at hdata
  have hred :
      ctx.mu j ∈
        pTypeReducibleLayer
          (pTypeHUInMaximal S (derivedWithin S))
          (pTypeHInDerived S (derivedWithin S) ctx.P)
          (pTypeH0InDerived S (derivedWithin S) ctx.H0) := by
    rw [pTypeReducibleLayer, Finset.mem_filter]
    refine ⟨?_, ctx.primeTI.prTIred_not_irr ctx.isoS j⟩
    simpa [ftTypePCoreFamily, pTypeH0InDerived,
      Ptype_Fcore_kernel_trivial ctx] using FTseqInd_TIred ctx j hj
  have hinduced := hdata.2.2.2 (ctx.mu j) hred
  rw [ftTypeP_HCInMaximal_eq_fitting ctx] at hinduced
  rcases hinduced.2.2 with ⟨xi, _, hmu⟩
  rw [hmu]
  exact mem_seqIndT (ctx.H.subgroupOf S) xi

/-- `PFsection13.v: FTprTIred1`. -/
theorem FTprTIred1
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ctx.mu j 1 = ((ctx.u * ctx.q : ℕ) : ℂ) :=
  FTtypeP_Ind_Fitting_1 ctx (ctx.mu j)
    (FTprTIred_Ind_Fitting ctx j hj)

/-! ## The quotient action and the prime-TI sign -/

private noncomputable def ftTypeP_quotientMulAut
    {E : Type} [Group E] (N : Subgroup E) [N.Normal]
    (e : MulAut E) (hN : N.map e.toMonoidHom = N) :
    MulAut (E ⧸ N) := by
  have he : N ≤ N.comap e.toMonoidHom := by
    intro x hx
    change e x ∈ N
    have : e x ∈ N.map e.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hN] at this
  have heinv : N ≤ N.comap e.symm.toMonoidHom := by
    intro x hx
    change e.symm x ∈ N
    have hxmap : x ∈ N.map e.toMonoidHom := by
      rw [hN]
      exact hx
    rcases hxmap with ⟨y, hy, rfl⟩
    simpa using hy
  let q := QuotientGroup.map N N e.toMonoidHom he
  let qinv := QuotientGroup.map N N e.symm.toMonoidHom heinv
  exact MonoidHom.toMulEquiv q qinv
    (by
      apply MonoidHom.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
      simp [q, qinv])
    (by
      apply MonoidHom.ext
      intro z
      obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
      simp [q, qinv])

@[simp] private theorem ftTypeP_quotientMulAut_apply_mk
    {E : Type} [Group E] (N : Subgroup E) [N.Normal]
    (e : MulAut E) (hN : N.map e.toMonoidHom = N) (x : E) :
    ftTypeP_quotientMulAut N e hN (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N (e x) :=
  rfl

private noncomputable def ftTypeP_quotientMulAutHom
    {A E : Type} [Group A] [Group E]
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E)
    (hN : ∀ a, N.map (f a).toMonoidHom = N) :
    A →* MulAut (E ⧸ N) where
  toFun a := ftTypeP_quotientMulAut N (f a) (hN a)
  map_one' := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [ftTypeP_quotientMulAut_apply_mk, map_one,
      MulAut.one_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [ftTypeP_quotientMulAut_apply_mk, map_mul,
      MulAut.mul_apply]

@[simp] private theorem ftTypeP_quotientMulAutHom_apply_mk
    {A E : Type} [Group A] [Group E]
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E)
    (hN : ∀ a, N.map (f a).toMonoidHom = N)
    (a : A) (x : E) :
    ftTypeP_quotientMulAutHom N f hN a (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N (f a x) :=
  ftTypeP_quotientMulAut_apply_mk N (f a) (hN a) x

private theorem ftTypeP_actionFactor_pred_dvd_q
    {Hbar U W₁ : Type}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁)
    (hD : PTypeFactorActionHypotheses D) :
    D.q ∣ pTypeActionFactorCard D - 1 := by
  letI : D.C.Normal := D.C_normal
  let Q := U ⧸ D.C
  let alphaQ : W₁ →* MulAut Q :=
    ftTypeP_quotientMulAutHom D.C D.W₁_action_U D.C_invariant
  letI : MulAction W₁ Q := MulAction.compHom Q alphaQ
  have hone : ∀ w : W₁, w • (1 : Q) = 1 := by
    intro w
    change alphaQ w 1 = 1
    exact map_one (alphaQ w)
  have hfixed : ∀ w : W₁, w ≠ 1 →
      ∀ x : Q, w • x = x → x = 1 := by
    intro w hw x hx
    obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective D.C x
    have hsmul :
        w • (QuotientGroup.mk' D.C u : Q) =
          QuotientGroup.mk' D.C (D.W₁_action_U w u) := by
      change alphaQ w (QuotientGroup.mk' D.C u) = _
      exact ftTypeP_quotientMulAutHom_apply_mk
        D.C D.W₁_action_U D.C_invariant w u
    have hx' : QuotientGroup.mk' D.C (D.W₁_action_U w u) =
        QuotientGroup.mk' D.C u := by
      rw [← hsmul]
      exact hx
    have hdelta : D.W₁_action_U w u * u⁻¹ ∈ D.C := by
      simpa only [div_eq_mul_inv] using
        (QuotientGroup.eq_iff_div_mem.mp hx')
    exact (QuotientGroup.eq_one_iff (N := D.C) u).mpr
      (hD.fixed_coset_trivial w hw u hdelta)
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := W₁) (X := Q))
  have hcardQ : Nat.card Q = 1 + t * Nat.card W₁ := by
    simpa [t] using natCard_eq_one_add_fixedOneOrbits_mul_natCard
      (G := W₁) (X := Q) hone hfixed
  have hcard : pTypeActionFactorCard D = 1 + t * D.q := by
    calc
      pTypeActionFactorCard D = Nat.card Q := rfl
      _ = 1 + t * Nat.card W₁ := hcardQ
      _ = 1 + t * D.q := by rw [D.card_W₁]
  refine ⟨t, ?_⟩
  calc
    pTypeActionFactorCard D - 1 = t * D.q := by rw [hcard]; omega
    _ = D.q * t := Nat.mul_comm _ _

private theorem ftTypeP_q_dvd_u_pred
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.q ∣ ctx.u - 1 := by
  simpa only [ftTypeP_factorAction_q_pf13,
    ftTypeP_actionFactorCard_eq_u_pf13] using
    ftTypeP_actionFactor_pred_dvd_q ctx.D ctx.actionHypotheses

private theorem ftTypeP_sign_eq_one_of_integralModEq
    (q : ℕ) (hq : 2 < q) (delta : ℤ)
    (hdelta : IsSign delta)
    (hmod : IsIntegralModEq (q : ℂ) (delta : ℂ) 1) :
    delta = 1 := by
  rcases hdelta with hplus | hminus
  · exact hplus
  · exfalso
    have hq0 : q ≠ 0 := by omega
    have hqC : (q : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hq0
    have hnotDvd : ¬ q ∣ 2 := by
      intro hdiv
      exact (Nat.not_le_of_gt hq)
        (Nat.le_of_dvd (by omega : 0 < 2) hdiv)
    obtain ⟨z, hz, heq⟩ := hmod
    rw [hminus] at heq
    have heq' : -(((2 : ℕ) : ℂ)) = (q : ℂ) * z := by
      norm_num at heq ⊢
      exact heq
    have hdiv : ((2 : ℕ) : ℂ) / (q : ℂ) = -z := by
      apply (div_eq_iff hqC).2
      linear_combination -heq'
    have hint : IsIntegral ℤ (((2 : ℕ) : ℂ) / (q : ℂ)) := by
      rw [hdiv]
      exact hz.neg
    exact hnotDvd (nat_dvd_of_cast_div_isIntegral 2 q hq0 hint)

/-- `PFsection13.v: FTprTIsign`. -/
theorem FTprTIsign
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    ctx.delta j = 1 := by
  by_cases hj : j = IrreducibleCharacter.trivial
  · subst j
    exact ctx.primeTI.prTIsign0 ctx.isoS
  · have hqC : (ctx.q : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hdegree :
        ctx.primeTI.primeTICharacter ctx.isoS
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
            j 1 = (ctx.u : ℂ) := by
      apply mul_left_cancel₀ hqC
      calc
        (ctx.q : ℂ) *
            ctx.primeTI.primeTICharacter ctx.isoS
              (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
              j 1 = ctx.mu j 1 :=
          (ctx.primeTI.prTIred_1 ctx.isoS j).symm
        _ = ((ctx.u * ctx.q : ℕ) : ℂ) := FTprTIred1 ctx j hj
        _ = (ctx.q : ℂ) * (ctx.u : ℂ) := by push_cast; ring
    have hcharMod :=
      ctx.primeTI.primeTICharacter_one_mod_card_left ctx.isoS
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j
    rw [hdegree] at hcharMod
    have huOne : IsIntegralModEq (ctx.q : ℂ) (ctx.u : ℂ) 1 := by
      obtain ⟨n, hn⟩ := ftTypeP_q_dvd_u_pred ctx
      refine ⟨(n : ℂ), isIntegral_natCast n, ?_⟩
      have huPos : 0 < ctx.u :=
        Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
      calc
        (ctx.u : ℂ) - 1 = ((ctx.u - 1 : ℕ) : ℂ) := by
          rw [Nat.cast_sub huPos]
          norm_num
        _ = ((ctx.q * n : ℕ) : ℂ) := by rw [hn]
        _ = (ctx.q : ℂ) * (n : ℂ) := by push_cast; rfl
    exact ftTypeP_sign_eq_one_of_integralModEq ctx.q
      ctx.primeTI.prime_cycTIhyp.two_lt_card_left (ctx.delta j)
      (ctx.primeTI.primeTISign_isSign ctx.isoS j)
      (hcharMod.symm.trans huOne)

/-! ## The no-induced alternative -/

private theorem ftTypeP_coreInduced_to_ambient
    {M : Type} [Group M] [Fintype M]
    (HU HC : Subgroup M) (hHC : HC ≤ HU) (actionCard : ℕ)
    (s : IrreducibleCharacter HU ℂ)
    (hs : PTypeCoreInduced (HC.subgroupOf HU) actionCard s) :
    ∃ xi : IrreducibleCharacter HC ℂ,
      pTypeIsLinearCharacter xi ∧
        ClassFunction.induce HU (s : ClassFunction HU ℂ) =
          ClassFunction.induce HC (xi : ClassFunction HC ℂ) := by
  rcases hs with ⟨_, theta, htheta, hs⟩
  let e : HC.subgroupOf HU ≃* HC :=
    Subgroup.subgroupOfEquivOfLe hHC
  let xi : IrreducibleCharacter HC ℂ :=
    internal.pTypeGaloisComapMulEquiv e.symm theta
  have hxi : pTypeIsLinearCharacter xi :=
    internal.pTypeIsLinearCharacter_comapMulEquiv e.symm theta htheta
  have htransport :
      ClassFunction.toSubgroupOf HC HU hHC (xi : ClassFunction HC ℂ) =
        (theta : ClassFunction (HC.subgroupOf HU) ℂ) := by
    ext x
    simp [ClassFunction.toSubgroupOf_apply, xi, e,
      internal.pTypeGaloisComapMulEquiv_apply]
  refine ⟨xi, hxi, ?_⟩
  calc
    ClassFunction.induce HU (s : ClassFunction HU ℂ) =
        ClassFunction.induce HU
          (ClassFunction.induce (HC.subgroupOf HU)
            (theta : ClassFunction (HC.subgroupOf HU) ℂ)) := by
      rw [hs]
    _ = ClassFunction.induce HU
        (ClassFunction.induce (HC.subgroupOf HU)
          (ClassFunction.toSubgroupOf HC HU hHC
            (xi : ClassFunction HC ℂ))) := by rw [htransport]
    _ = ClassFunction.induce HC (xi : ClassFunction HC ℂ) :=
      ClassFunction.induce_trans HC HU hHC _

/-- `PFsection13.v: FTtypeP_no_Ind_Fitting_facts`. -/
theorem FTtypeP_no_Ind_Fitting_facts
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hno : ¬ ∃ lambda ∈ ftTypePCoreFamily S,
      lambda ∈ irr_Ind_Fitting S) :
    ctx.galoisAlternative ∧ ctx.C = ⊥ ∧
      ctx.u = (ctx.p ^ ctx.q - 1) / (ctx.p - 1) := by
  obtain ⟨_, _, _, hUcomm, _, _, _, _, _, _⟩ := FTtypeP_facts ctx
  letI : IsMulCommutative U := hUcomm
  let HU := pTypeHUInMaximal S (derivedWithin S)
  let HF := pTypeHInDerived S (derivedWithin S) ctx.P
  let H₀ := pTypeH0InDerived S (derivedWithin S) ctx.H0
  let H₀CPrime := pTypeH0CPrimeInDerived S (derivedWithin S)
    ctx.H0 U W₁ ctx.D
  let HC := pTypeHCInDerived S (derivedWithin S) ctx.P U W₁ ctx.D
  let UHU := pTypeUInDerived S (derivedWithin S) U
  have hH₀CPrime : H₀CPrime = ⊥ := by
    simpa only [H₀CPrime, pTypeCoreKernelDerivedComplement] using
      ftTypeP_coreKernelDerivedComplement_eq_bot ctx
  have hHCInS :
      pTypeHCInMaximal S ctx.P U W₁ ctx.D = ctx.H.subgroupOf S :=
    ftTypeP_HCInMaximal_eq_fitting ctx
  have hcases := typeP_reducible_core_cases S U W W₁ W₂ defW
    ctx.maxS ctx.StypeP ctx.notType5
  dsimp only at hcases
  rw [hHCInS] at hcases
  have hGalois : typeP_Galois ctx.D := by
    rcases hcases with hinduced | hfull
    · rcases hinduced with
        ⟨chi, hchiCore, _, xi, _, hchiInduced⟩
      change (chi : ClassFunction S ℂ) ∈
        seqIndD (k := ℂ) HU HF H₀CPrime at hchiCore
      rw [hH₀CPrime] at hchiCore
      have hchiCal :
          (chi : ClassFunction S ℂ) ∈ ftTypePCoreFamily S := by
        simpa only [ftTypePCoreFamily, HU, HF, pTypeCoreDerived,
          pTypeCoreFitting] using hchiCore
      change (chi : ClassFunction S ℂ) =
        ClassFunction.induce (ctx.H.subgroupOf S)
          (xi : ClassFunction (ctx.H.subgroupOf S) ℂ) at hchiInduced
      have hchiFit :
          (chi : ClassFunction S ℂ) ∈ ftTypePFittingFamily S := by
        rw [hchiInduced]
        exact mem_seqIndT (ctx.H.subgroupOf S) xi
      exact (hno ⟨(chi : ClassFunction S ℂ), hchiCal,
        ⟨chi.2, hchiFit⟩⟩).elim
    · exact hfull.1
  have hGchars := typeP_Galois_characters S U W W₁ W₂ defW
    ctx.maxS ctx.StypeP ctx.notType5 hGalois
  dsimp only at hGchars
  have hAllReducible :
      ∀ zeta ∈ seqIndD (k := ℂ) HU HF H₀CPrime,
        ¬ IsIrreducibleCharacter S ℂ zeta := by
    intro zeta hzeta hirr
    obtain ⟨s, hs, hzetaEq⟩ := seqIndP.mp hzeta
    have hsCore : PTypeCoreInduced HC
        (pTypeActionFactorCard ctx.D) s := hGchars.1.2 s hs
    have hHCle : ctx.H.subgroupOf S ≤ HU := by
      rw [← hHCInS]
      exact pTypeHCInMaximal_le_HU ctx.ptypeCtx ctx.D
    have hHCeq : HC = (ctx.H.subgroupOf S).subgroupOf HU := by
      calc
        HC =
            (pTypeHCInMaximal S ctx.P U W₁ ctx.D).subgroupOf HU := by
          simpa only [HC, HU] using
            pTypeHCInDerived_eq_subgroupOf ctx.ptypeCtx ctx.D
        _ = (ctx.H.subgroupOf S).subgroupOf HU := by rw [hHCInS]
    have hsNested : PTypeCoreInduced
        ((ctx.H.subgroupOf S).subgroupOf HU)
          (pTypeActionFactorCard ctx.D) s := by
      rw [← hHCeq]
      exact hsCore
    obtain ⟨xi, _, hsAmbient⟩ :=
      ftTypeP_coreInduced_to_ambient HU (ctx.H.subgroupOf S) hHCle
        (pTypeActionFactorCard ctx.D) s hsNested
    have hzetaAmbient : zeta =
        ClassFunction.induce (ctx.H.subgroupOf S)
          (xi : ClassFunction (ctx.H.subgroupOf S) ℂ) :=
      hzetaEq.trans hsAmbient
    have hzetaFit : zeta ∈ ftTypePFittingFamily S := by
      rw [hzetaAmbient]
      exact mem_seqIndT (ctx.H.subgroupOf S) xi
    have hzetaCal : zeta ∈ ftTypePCoreFamily S := by
      rw [hH₀CPrime] at hzeta
      simpa only [ftTypePCoreFamily, HU, HF, pTypeCoreDerived,
        pTypeCoreFitting] using hzeta
    exact hno ⟨zeta, hzetaCal, ⟨hirr, hzetaFit⟩⟩
  have hfull := hGchars.2.2 hAllReducible
  have hDC : ctx.D.C = ⊥ :=
    (pTypeCInDerived_eq_bot_iff ctx.ptypeCtx ctx.D).mp hfull.1
  have hC : ctx.C = ⊥ := by
    calc
      ctx.C = ctx.D.C.map U.subtype :=
        (ftTypeP_actionKernel_map_eq_C_pf13 ctx).symm
      _ = ⊥ := by rw [hDC, Subgroup.map_bot]
  have hu := hfull.2.1
  rw [ftTypeP_actionFactorCard_eq_u_pf13 ctx,
    ftTypeP_factorAction_p_pf13 ctx,
    ftTypeP_factorAction_q_pf13 ctx] at hu
  exact ⟨hGalois, hC, hu⟩
def ftTypePSignIndex
    {W₂ : Subgroup G} (b : Bool)
    (j : IrreducibleCharacter W₂ ℂ) : IrreducibleCharacter W₂ ℂ :=
  if b then IrreducibleCharacter.dual j else j

def ftTypePBooleanSign (b : Bool) : ℂ :=
  if b then -1 else 1

/-- `PFsection13.v: typeP_TIred_coherent`. -/
def typeP_TIred_coherent
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau₁ : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ) : Prop :=
  ∃ b : Bool,
    (b = true → ctx.p = 3) ∧
      ∀ j : IrreducibleCharacter W₂ ℂ,
        j ≠ IrreducibleCharacter.trivial →
          tau₁ (ctx.mu j) =
            ftTypePBooleanSign b •
              ∑ i : IrreducibleCharacter W₁ ℂ,
                ctx.eta i (ftTypePSignIndex b j)

private def ftTypePTopRows
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tauTop : ClassFunction S ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ) : Prop :=
  ∃ b : Bool,
    (b = true → ctx.p = 3) ∧
      ∀ j : IrreducibleCharacter W₂ ℂ,
        j ≠ IrreducibleCharacter.trivial →
          tauTop (ctx.mu j) =
            ftTypePBooleanSign b •
              ∑ i : IrreducibleCharacter W₁ ℂ,
                ctx.isoG.cyclicTIImage
                  (i, ftTypePSignIndex b j)

private theorem ftTypePCyclicRow_virtual
    {Q W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {h : CyclicTIHypothesis Q W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := ℂ) h)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (iso.cyclicTIImage (i, j)) := by
  let chi : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW i j
  let z : VirtualCharacter W ℂ := Finsupp.single chi 1
  refine ⟨iso.virtualMap z, ?_⟩
  calc
    VirtualCharacter.realize (iso.virtualMap z) =
        iso.linearMap (VirtualCharacter.realize z) :=
      iso.realize_virtualMap z
    _ = iso.cyclicTIImage (i, j) := by
      simp [z, chi, CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible]

private theorem ftTypePSumRow_virtual
    {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ)
    (hf : ∀ i, ClassFunction.IsVirtual (f i)) :
    ClassFunction.IsVirtual (∑ i, f i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simpa using ClassFunction.IsVirtual.zero (H := Q)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i).add ih

private theorem ftTypePUniformTop
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (hj₀ : j₀ ≠ IrreducibleCharacter.trivial) :
    let T := ctx.primeTI.uniform_prTIred_seq ctx.isoS j₀
    ∃ tauTop : ClassFunction S ℂ →ₗ[ℂ]
        ClassFunction (⊤ : Subgroup G) ℂ,
      coherent_with T (nonidentitySet S)
          (Dade ctx.primeDadeF.prDade_hyp) tauTop ∧
        ∀ j, tauTop (ctx.mu j) =
          (ctx.delta j₀ : ℂ) •
            ∑ i : IrreducibleCharacter W₁ ℂ,
              ctx.isoG.cyclicTIImage (i, j) := by
  classical
  let T := ctx.primeTI.uniform_prTIred_seq ctx.isoS j₀
  obtain ⟨_, tauTop, hrow, hisometry, hagrees⟩ :=
    ctx.primeDadeF.uniform_prTIred_coherent
      ctx.isoS ctx.isoG j₀ hj₀
  have hgenerators : ∀ phi ∈ T,
      ClassFunction.IsVirtual (tauTop phi) := by
    rintro phi ⟨j, _hj, rfl⟩
    rw [hrow]
    have hsum := (ftTypePSumRow_virtual
      (fun i : IrreducibleCharacter W₁ ℂ ↦
        ctx.isoG.cyclicTIImage (i, j))
      (fun i ↦ ftTypePCyclicRow_virtual ctx.isoG i j)).zsmul
        (ctx.delta j₀)
    exact (Int.cast_smul_eq_zsmul ℂ (ctx.delta j₀)
      (∑ i : IrreducibleCharacter W₁ ℂ,
        ctx.isoG.cyclicTIImage (i, j))).symm ▸ hsum
  have hvirtual : ∀ phi ∈ AddSubgroup.closure T,
      ClassFunction.IsVirtual (tauTop phi) := by
    intro phi hphi
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi => exact hgenerators phi hphi
    | zero => simpa using ClassFunction.IsVirtual.zero
    | add phi psi _ _ hphi hpsi =>
        simpa only [map_add] using hphi.add hpsi
    | neg phi _ hphi => simpa only [map_neg] using hphi.neg
  refine ⟨tauTop, ?_, ?_⟩
  · exact
      { isometry := hisometry
        mapsToVirtual := hvirtual
        agrees := hagrees }
  · simpa only [FTTypePSetupContext.mu,
      FTTypePSetupContext.delta] using hrow

private theorem ftTypePCoreFamily_in_kernel
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    cfConjC_subset
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (FTtypePKernelLayer ctx.primeDadeF) := by
  refine ⟨?_, ?_⟩
  · intro phi hphi
    simpa only [ftTypePCoreFamily, pTypeCoreDerived,
      pTypeCoreFitting, FTtypePKernelLayer,
      PrimeDadeHypothesis.signalizerInKernel] using hphi
  · intro phi hphi
    exact seqInd_inverse_mem (k := ℂ)
      (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥ hphi

private theorem ftTypePH0InDerived_bot
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hH₀ : ctx.H0 = ⊥) :
    pTypeH0InDerived S (derivedWithin S) ctx.H0 = ⊥ := by
  ext x
  simp [pTypeH0InDerived, hH₀]

private theorem ftTypePCoreFamily_in_uniform
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hH₀ : ctx.H0 = ⊥)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (hj₀ : j₀ ≠ IrreducibleCharacter.trivial)
    (hreducible : ∀ phi ∈ ftTypePCoreFamily S,
      ¬ IsIrreducibleCharacter S ℂ phi)
    (hdegree : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        ctx.mu j 1 = ((ctx.u * ctx.q : ℕ) : ℂ)) :
    (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) ⊆
      ctx.primeTI.uniform_prTIred_seq ctx.isoS j₀ := by
  intro phi hphi
  change phi ∈ ftTypePCoreFamily S at hphi
  have hdecomposition := typeP_reducible_core_Ind
    S U W W₁ W₂ defW ctx.maxS ctx.StypeP ctx.notType5
  have hphiLayer : phi ∈ pTypeReducibleLayer
      (pTypeHUInMaximal S (derivedWithin S))
      (pTypeHInDerived S (derivedWithin S) (Fitting_core S))
      (pTypeH0InDerived S (derivedWithin S) ctx.H0) := by
    rw [pTypeReducibleLayer, Finset.mem_filter]
    exact ⟨by
      rw [ftTypePH0InDerived_bot ctx hH₀]
      simpa only [ftTypePCoreFamily, pTypeCoreDerived,
        pTypeCoreFitting, pTypeHUInMaximal,
        pTypeHInDerived] using hphi,
      hreducible phi hphi⟩
  have hcovered := hdecomposition.2.2.1 hphiLayer
  obtain ⟨j, hjErase, hjphi⟩ := Finset.mem_image.mp hcovered
  have hj : j ≠
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter W₂ ℂ) :=
    (Finset.mem_erase.mp hjErase).1
  refine ⟨j, ⟨hj, ?_⟩, ?_⟩
  · exact (hdegree j hj).trans (hdegree j₀ hj₀).symm
  · simpa only [FTTypePSetupContext.mu,
      FTTypePSetupContext.primeTI,
      FTTypePSetupContext.isoS] using hjphi

private theorem ftTypePTransportTopRows
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {tauTop : ClassFunction S ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ}
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) (Dade ctx.primeDadeF.prDade_hyp) tauTop)
    (hrows : ftTypePTopRows ctx tauTop) :
    ∃ tau₁ : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ,
      coherent_with
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
        (nonidentitySet S) ctx.tau tau₁ ∧
      typeP_TIred_coherent ctx tau₁ := by
  let tau₁ : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    ctx.targetMap.comp tauTop
  have hcoh₁ : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau₁ := by
    simpa only [tau₁, FTTypePSetupContext.tau] using
      ftTypePCoherentWith_targetMap ctx hcoh
  obtain ⟨b, hb, hrow⟩ := hrows
  refine ⟨tau₁, hcoh₁, b, hb, ?_⟩
  intro j hj
  change ctx.targetMap (tauTop (ctx.mu j)) = _
  rw [hrow j hj, map_smul, map_sum]

private theorem ftTypePTopCoherenceWitness
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hcore : coherent
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau) :
    ∃ tauTop : ClassFunction S ℂ →ₗ[ℂ]
        ClassFunction (⊤ : Subgroup G) ℂ,
      coherent_with
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
        (nonidentitySet S) (Dade ctx.primeDadeF.prDade_hyp)
        tauTop := by
  obtain ⟨tau₁, hcoh₁⟩ := hcore
  let tauTop : ClassFunction S ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    ftTypePSourceMap.comp tau₁
  have hsource := ftTypePCoherentWith_sourceMap ctx hcoh₁
  refine ⟨tauTop, ?_⟩
  exact
    { isometry := hsource.isometry
      mapsToVirtual := hsource.mapsToVirtual
      agrees := by
        intro phi hphi hsupp
        have hagree := hsource.agrees phi hphi hsupp
        simpa only [tauTop, FTTypePSetupContext.tau,
          LinearMap.comp_apply, ftTypePSourceMap_targetMap] using
          hagree }

private theorem ftTypePPairing_neg_left
    {Q : Type} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (-phi) psi = -characterPairing phi psi := by
  rw [← neg_one_smul ℂ phi, characterPairing_smul_left]
  simp

private theorem ftTypePIrreducibleTopRows
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hcore : coherent
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau)
    (hmu : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        ctx.mu j ∈ ftTypePCoreFamily S)
    (hdegree : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        ctx.mu j 1 = ((ctx.u * ctx.q : ℕ) : ℂ))
    (hsign : ∀ j : IrreducibleCharacter W₂ ℂ,
      ctx.delta j = 1)
    (zeta₀ : ClassFunction S ℂ)
    (hzeta₀ : zeta₀ ∈ ftTypePCoreFamily S)
    (hzetaIrr : IsIrreducibleCharacter S ℂ zeta₀) :
    ∃ tauTop : ClassFunction S ℂ →ₗ[ℂ]
        ClassFunction (⊤ : Subgroup G) ℂ,
      coherent_with
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
        (nonidentitySet S) (Dade ctx.primeDadeF.prDade_hyp)
        tauTop ∧
      ftTypePTopRows ctx tauTop := by
  classical
  letI : IsCyclic W₂ := ctx.primeTI.fixed_cyclic
  obtain ⟨tauTop, hcohTop⟩ := ftTypePTopCoherenceWitness ctx hcore
  let zeta : IrreducibleCharacter S ℂ := ⟨zeta₀, hzetaIrr⟩
  have hzeta :
      (zeta : ClassFunction S ℂ) ∈ ftTypePCoreFamily S := by
    simpa only [zeta] using hzeta₀
  by_cases hordinary :
      ∀ j : IrreducibleCharacter W₂ ℂ,
        j ≠ IrreducibleCharacter.trivial →
          tauTop (ctx.mu j) =
            ∑ i : IrreducibleCharacter W₁ ℂ,
              ctx.isoG.cyclicTIImage (i, j)
  · refine ⟨tauTop, hcohTop, false, by simp, ?_⟩
    intro j hj
    simpa [ftTypePBooleanSign, ftTypePSignIndex] using
      hordinary j hj
  · push_neg at hordinary
    obtain ⟨j, hj, hjNotOrdinary⟩ := hordinary
    have hjCases := FTtypeP_coherent_TIred
      ctx.primeDadeF ctx.isoS ctx.isoG (mFT_odd S)
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      tauTop zeta j (ftTypePCoreFamily_in_kernel ctx)
      hcohTop hzeta (hmu j hj)
    have hjExceptional :
        tauTop (ctx.mu j) =
            (-(ctx.delta j : ℂ)) •
              ∑ i : IrreducibleCharacter W₁ ℂ,
                ctx.isoG.cyclicTIImage
                  (i, IrreducibleCharacter.dual j) ∧
          ∀ ell : IrreducibleCharacter W₂ ℂ,
            ctx.mu ell ∈
                (↑(ftTypePCoreFamily S) :
                  Set (ClassFunction S ℂ)) →
            ctx.mu ell 1 = ctx.mu j 1 →
            ell = j ∨ ell = IrreducibleCharacter.dual j := by
      rcases hjCases with hjOrdinary | hjExceptional
      · exfalso
        apply hjNotOrdinary
        simpa only [hsign j, Int.cast_one, one_smul] using
          hjOrdinary
      · exact hjExceptional
    let k : IrreducibleCharacter W₂ ℂ :=
      IrreducibleCharacter.dual j
    have hrowJ :
        tauTop (ctx.mu j) =
          (-1 : ℂ) •
            ∑ i : IrreducibleCharacter W₁ ℂ,
              ctx.isoG.cyclicTIImage (i, k) := by
      simpa only [k, hsign j, Int.cast_one] using
        hjExceptional.1
    have hk : k ≠
        (IrreducibleCharacter.trivial :
          IrreducibleCharacter W₂ ℂ) := by
      intro hk0
      apply hj
      calc
        j = IrreducibleCharacter.dual
              (IrreducibleCharacter.dual j) :=
          (IrreducibleCharacter.dual_dual j).symm
        _ = IrreducibleCharacter.dual
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ) :=
          congrArg IrreducibleCharacter.dual hk0
        _ = IrreducibleCharacter.trivial :=
          IrreducibleCharacter.dual_trivial
    have hkj : k ≠ j := by
      intro hself
      apply hj
      exact (odd_eq_conj_irr1 (mFT_odd W₂) j).mp
        (show IrreducibleCharacter.dual j = j from hself)
    have hclassify :
        ∀ ell : IrreducibleCharacter W₂ ℂ,
          ell ≠ IrreducibleCharacter.trivial →
            ell = j ∨ ell = k := by
      intro ell hell
      simpa only [k] using hjExceptional.2 ell (hmu ell hell)
        ((hdegree ell hell).trans (hdegree j hj).symm)
    have huniv :
        (Finset.univ :
          Finset (IrreducibleCharacter W₂ ℂ)) =
          {IrreducibleCharacter.trivial, j, k} := by
      ext ell
      simp only [Finset.mem_univ, true_iff, Finset.mem_insert,
        Finset.mem_singleton]
      by_cases hell :
          ell = (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ ℂ)
      · exact Or.inl hell
      · exact Or.inr (hclassify ell hell)
    have hpThree : ctx.p = 3 := by
      calc
        ctx.p = Nat.card W₂ := rfl
        _ = Fintype.card (IrreducibleCharacter W₂ ℂ) :=
          (IrreducibleCharacter.card_eq_natCard_of_isCyclic
            (C := W₂) (k := ℂ)).symm
        _ = 3 := by
          rw [← Finset.card_univ, huniv]
          have htriv :
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ) ∉ ({j, k} :
                  Finset (IrreducibleCharacter W₂ ℂ)) := by
            simp [Ne.symm hj, Ne.symm hk]
          have hjk : j ∉ ({k} :
              Finset (IrreducibleCharacter W₂ ℂ)) := by
            simpa using Ne.symm hkj
          rw [Finset.card_insert_of_notMem htriv,
            Finset.card_insert_of_notMem hjk]
          simp
    have hkCases := FTtypeP_coherent_TIred
      ctx.primeDadeF ctx.isoS ctx.isoG (mFT_odd S)
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      tauTop zeta k (ftTypePCoreFamily_in_kernel ctx)
      hcohTop hzeta (hmu k hk)
    have hrowK :
        tauTop (ctx.mu k) =
          (-1 : ℂ) •
            ∑ i : IrreducibleCharacter W₁ ℂ,
              ctx.isoG.cyclicTIImage
                (i, IrreducibleCharacter.dual k) := by
      rcases hkCases with hkOrdinary | hkExceptional
      · have hkOrdinary' :
            tauTop (ctx.mu k) =
              (1 : ℂ) •
                ∑ i : IrreducibleCharacter W₁ ℂ,
                  ctx.isoG.cyclicTIImage (i, k) := by
          simpa only [hsign k, Int.cast_one] using hkOrdinary
        have hneg : tauTop (ctx.mu k) = -tauTop (ctx.mu j) := by
          let row := ∑ i : IrreducibleCharacter W₁ ℂ,
            ctx.isoG.cyclicTIImage (i, k)
          calc
            tauTop (ctx.mu k) = (1 : ℂ) • row := hkOrdinary'
            _ = row := one_smul ℂ row
            _ = -((-1 : ℂ) • row) := by
              have hminus : (-1 : ℂ) • row = -row := by
                ext x
                simp
              rw [hminus, neg_neg]
            _ = -tauTop (ctx.mu j) := by rw [hrowJ]
        have hjClosure : ctx.mu j ∈ AddSubgroup.closure
            (↑(ftTypePCoreFamily S) :
              Set (ClassFunction S ℂ)) :=
          AddSubgroup.subset_closure (hmu j hj)
        have hkClosure : ctx.mu k ∈ AddSubgroup.closure
            (↑(ftTypePCoreFamily S) :
              Set (ClassFunction S ℂ)) :=
          AddSubgroup.subset_closure (hmu k hk)
        have hpairJJ := hcohTop.isometry
          (ctx.mu j) hjClosure (ctx.mu j) hjClosure
        have hpairKJ := hcohTop.isometry
          (ctx.mu k) hkClosure (ctx.mu j) hjClosure
        have hnormJ :
            characterPairing (ctx.mu j) (ctx.mu j) =
              (Nat.card W₁ : ℂ) := by
          simpa only [FTTypePSetupContext.mu] using
            ctx.primeTI.cfnorm_prTIred ctx.isoS j
        have horthKJ :
            characterPairing (ctx.mu k) (ctx.mu j) = 0 := by
          simpa only [FTTypePSetupContext.mu, if_neg hkj] using
            ctx.primeTI.cfdot_prTIred ctx.isoS k j
        have hzero : -(Nat.card W₁ : ℂ) = 0 := by
          calc
            -(Nat.card W₁ : ℂ) =
                -characterPairing (ctx.mu j) (ctx.mu j) := by
              rw [hnormJ]
            _ = -characterPairing
                  (tauTop (ctx.mu j)) (tauTop (ctx.mu j)) := by
              rw [hpairJJ]
            _ = characterPairing
                  (-tauTop (ctx.mu j)) (tauTop (ctx.mu j)) :=
              (ftTypePPairing_neg_left
                (tauTop (ctx.mu j)) (tauTop (ctx.mu j))).symm
            _ = characterPairing
                  (tauTop (ctx.mu k)) (tauTop (ctx.mu j)) := by
              rw [hneg]
            _ = characterPairing (ctx.mu k) (ctx.mu j) := hpairKJ
            _ = 0 := horthKJ
        exact ((Nat.cast_ne_zero.mpr Nat.card_pos.ne' :
          (Nat.card W₁ : ℂ) ≠ 0) (neg_eq_zero.mp hzero)).elim
      · simpa only [hsign k, Int.cast_one] using
          hkExceptional.1
    refine ⟨tauTop, hcohTop, true, ?_, ?_⟩
    · intro _
      exact hpThree
    · intro ell hell
      rcases hclassify ell hell with rfl | rfl
      · simpa [ftTypePBooleanSign, ftTypePSignIndex, k] using
          hrowJ
      · simpa [ftTypePBooleanSign, ftTypePSignIndex] using
          hrowK

/-- `PFsection13.v: FTtypeP_coherence`, Peterfalvi (13.3)(c). -/
theorem FTtypeP_coherence
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ∃ tau₁ : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ,
      coherent_with
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
        (nonidentitySet S) ctx.tau tau₁ ∧
      typeP_TIred_coherent ctx tau₁ := by
  classical
  obtain ⟨_, _, _, _, _, _, _, hcore, _, _⟩ :=
    FTtypeP_facts ctx
  have hH₀ : ctx.H0 = ⊥ := Ptype_Fcore_kernel_trivial ctx
  have hmu : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        ctx.mu j ∈ ftTypePCoreFamily S :=
    FTseqInd_TIred ctx
  have hdegree : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        ctx.mu j 1 = ((ctx.u * ctx.q : ℕ) : ℂ) :=
    FTprTIred1 ctx
  have hsign : ∀ j : IrreducibleCharacter W₂ ℂ,
      ctx.delta j = 1 :=
    FTprTIsign ctx
  by_cases hreducible : ∀ phi ∈ ftTypePCoreFamily S,
      ¬ IsIrreducibleCharacter S ℂ phi
  · letI : IsCyclic W₂ := ctx.primeTI.fixed_cyclic
    obtain ⟨j₀, hj₀⟩ :=
      IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
        (k := ℂ) ctx.primeTI.prime_cycTIhyp.one_lt_card_right
    obtain ⟨tauTop, hcohUniform, hrowUniform⟩ :=
      ftTypePUniformTop ctx j₀ hj₀
    have hsubset := ftTypePCoreFamily_in_uniform
      ctx hH₀ j₀ hj₀ hreducible hdegree
    have hcohTop : coherent_with
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
        (nonidentitySet S) (Dade ctx.primeDadeF.prDade_hyp)
        tauTop :=
      subset_coherent_with hsubset hcohUniform
    have hrows : ftTypePTopRows ctx tauTop := by
      refine ⟨false, by simp, ?_⟩
      intro j hj
      simpa only [ftTypePBooleanSign, ftTypePSignIndex,
        Bool.false_eq_true, if_false, hsign j₀, Int.cast_one,
        one_smul] using hrowUniform j
    exact ftTypePTransportTopRows ctx hcohTop hrows
  · push_neg at hreducible
    obtain ⟨zeta, hzeta, hzetaIrr⟩ := hreducible
    obtain ⟨tauTop, hcohTop, hrows⟩ :=
      ftTypePIrreducibleTopRows
        ctx hcore hmu hdegree hsign zeta hzeta hzetaIrr
    exact ftTypePTransportTopRows ctx hcohTop hrows

end

end Submission.OddOrder.PF
