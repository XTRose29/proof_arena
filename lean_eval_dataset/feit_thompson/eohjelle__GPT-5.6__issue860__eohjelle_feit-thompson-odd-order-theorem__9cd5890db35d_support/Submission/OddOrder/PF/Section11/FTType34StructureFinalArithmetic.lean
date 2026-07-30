import Submission.OddOrder.PF.Section11.FTType34StructureProjection

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open PTypeCoreActionKernelInternal
open PTypeCoreBoundsInternal
open PTypeCoreContextInternal
open scoped BigOperators Classical Pointwise IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {M U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftType34FinalArithmeticFintypeOfFinite
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace FTType34StructureInternal

private theorem factorActionHypotheses34
    (base : FTType34Base M U W W₁ W₂ defW) :
    PTypeFactorActionHypotheses (factorAction34 base) :=
  Ptype_factor_action_hypotheses base.ptypeCtx (factorFacts34 base)

/-!
# Peterfalvi (11.9)(b,c): final arithmetic

This phase uses internal declarations exported by the preceding modules,
including

* `FTtype34_zeroRowProjection34` and
  `zeroColumn_fullSupport_projection34` from the projection block; and
* the `ftType34S1_*34`, `ftType34S2_*34`, action-kernel, and reducible-column
  adapters from the infrastructure block.

The endpoint theorem is a direct conjunction; none of the supporting
declarations below is part of its public interface.
-/

private theorem pairing_sub_left_final34
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingRight c (a - b) = _
  exact map_sub (characterPairingRight c) a b

private theorem pairing_sub_right_final34
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingLeft a (b - c) = _
  exact map_sub (characterPairingLeft a) b c

/-! ## The Section-10 reference belongs to the Section-11 family -/

private theorem ftType34_HCInHU_eq_commutator34
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.HCInHU = _root_.commutator base.HUInM := by
  rw [← ftType34_secondDerived_subgroup_eq_HCInHU11 base]
  rw [secondDerivedInM_eq_commutator_map11 M]
  exact Subgroup.comap_map_eq_self_of_injective
    base.HUInM.subtype_injective (_root_.commutator base.HUInM)

private theorem ftType34_reference_mem_S1_34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta) :
    zeta ∈ ftType34S1 base := by
  have hzetaFamily := hzeta.mem_calS
  change zeta ∈ seqIndD (k := ℂ) base.HUInM
    (⊤ : Subgroup base.HUInM) ⊥ at hzetaFamily
  obtain ⟨theta, htheta, hzetaInd⟩ := seqIndP.mp hzetaFamily
  have hthetaOne : theta 1 = 1 := by
    have hindexNe : (base.HUInM.index : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr base.HUInM.index_ne_zero_of_finite
    apply mul_left_cancel₀ hindexNe
    calc
      (base.HUInM.index : ℂ) * theta 1 =
          ClassFunction.induce base.HUInM
            (theta : ClassFunction base.HUInM ℂ) 1 := by
        rw [ClassFunction.induce_one]
      _ = zeta 1 := congrArg (fun f : ClassFunction M ℂ => f 1)
        hzetaInd.symm
      _ = (base.q : ℂ) := hzeta.degree
      _ = (base.HUInM.index : ℂ) := by
        rw [ftType34_HUInM_index_eq_q11 base]
      _ = (base.HUInM.index : ℂ) * 1 := by ring
  have hlinear : pTypeIsLinearCharacter theta := by
    change Module.finrank ℂ theta.representation = 1
    apply Nat.cast_injective (R := ℂ)
    simpa only [Nat.cast_one,
      IrreducibleCharacter.apply_one_eq_finrank] using hthetaOne
  have hHCkernel : base.HCInHU ≤
      ClassFunction.translationKernel
        (theta : ClassFunction base.HUInM ℂ) := by
    rw [ftType34_HCInHU_eq_commutator34 base]
    exact
      PTypeGaloisCharacterArithmeticInternal.commutator_le_translationKernel_of_isLinear
        theta hlinear
  change zeta ∈ seqIndD (k := ℂ) base.HUInM
    (⊤ : Subgroup base.HUInM) base.HCInHU
  apply seqIndP.mpr
  refine ⟨theta, (mem_Iirr_kerD.mpr ⟨hHCkernel, ?_⟩), hzetaInd⟩
  exact (mem_Iirr_kerD.mp htheta).2

/-! ## The strict inequality `p < q` -/

private theorem ftType34_p_ne_q_final34
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.p ≠ base.q := by
  intro hpq
  have hcop := base.primeTI.factor_card_coprime
  have hqOne : base.q = 1 := by
    change Nat.Coprime base.q base.p at hcop
    rw [hpq] at hcop
    exact (Nat.coprime_self base.q).mp hcop
  exact base.q_prime.ne_one hqOne

private theorem ftType34_p_lt_q_final34
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.p < base.q := by
  classical
  obtain ⟨zeta, hzeta⟩ := FTtypeP_ref_irr base.maxM base.MtypeP
  have hzetaS1 : zeta ∈ ftType34S1 base :=
    ftType34_reference_mem_S1_34 base zeta hzeta
  by_contra hpq
  have hqp : base.q < base.p := by
    have hpne := ftType34_p_ne_q_final34 base
    omega
  obtain ⟨chi, hbridge, _hchiVirtual, _hchiNorm, hchiEta⟩ :=
    FTtype345_Dade_bridge0 base.maxM base.MtypeP base.notMtype2
      zeta hzeta hqp
  have hbridgeRaw :
      Dade (FT_Dade0_hyp M base.maxM) (muZero34 base - zeta) =
        (∑ i : IrreducibleCharacter W₁ ℂ,
          base.isoG.cyclicTIImage
            (i, (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ))) - chi := by
    exact hbridge
  have hbridgeTarget :
      dadeBridgeZero34 base zeta =
        etaColumn34 base
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ) -
          base.targetMap chi := by
    have hmap := congrArg base.targetMap hbridgeRaw
    simpa only [dadeBridgeZero34, muZero34, etaColumn34, eta34,
      LinearMap.comp_apply, map_sub, map_sum] using hmap
  apply FTtype34_not_ortho_cycTIiso base zeta hzetaS1
  apply (eqProjection34_iff base
    (dadeBridgeZero34 base zeta)
    (etaColumn34 base
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter W₂ ℂ))).2
  intro i j
  have hchiTarget : characterPairing (base.targetMap chi)
      (eta34 base i j) = 0 := by
    rw [eta34, base.targetMap_pairing]
    exact hchiEta i j
  rw [hbridgeTarget, pairing_sub_left_final34,
    hchiTarget, sub_zero]

/-! ## Common normally-induced and Dade adapters -/

private theorem ftType34_seqIndD_mem_seqIndT_final34
    (base : FTType34Base M U W W₁ W₂ defW)
    (K N : Subgroup base.HUInM)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ seqIndD (k := ℂ) base.HUInM K N) :
    phi ∈ seqIndT (k := ℂ) base.HUInM := by
  have htop : phi ∈ seqIndD (k := ℂ) base.HUInM
      (⊤ : Subgroup base.HUInM) ⊥ :=
    seqInd_sub (k := ℂ) base.HUInM K N hphi
  rw [seqIndC1_filter (k := ℂ) base.HUInM] at htop
  exact (Finset.mem_filter.mp htop).1

private theorem ftType34_mu_mem_seqIndT_final34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    mu34 base j ∈ seqIndT (k := ℂ) base.HUInM := by
  change base.primeTI.primeTIRed base.isoM j ∈
    seqIndT (k := ℂ) base.HUInM
  rw [← base.primeTI.cfInd_prTIres base.isoM j]
  exact mem_seqIndT base.HUInM
    (base.primeTI.primeTI_Ires base.isoM j)

private theorem ftType34S2_subset_kernelLayer_final34
    (base : FTType34Base M U W W₁ W₂ defW) :
    cfConjC_subset
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer base.primeDade) := by
  have h := ftType34S2_cfConjC_subset34 base
  refine ⟨?_, h.2⟩
  intro phi hphi
  have hbottom := h.1 hphi
  simpa [FTtypePKernelLayer,
    PrimeDadeHypothesis.signalizerInKernel, ftType34Layer,
    base.FTcore_eq_HU] using hbottom

private theorem ftType34_lowerKernel_eq_CInHU_final34
    (base : FTType34Base M U W W₁ W₂ defW) :
    pTypeH0DerivedComplementInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel base.ptypeCtx) U = base.CInHU := by
  rw [PTypeNonGaloisHCProjectionInternal.pTypeH0DerivedComplementInDerived_eq_subgroupOf
    base.ptypeCtx]
  change base.subgroupInHU (base.H0 ⊔ base.U') = base.CInHU
  rw [(FTtype34_Fcore_kernel_trivial base).H0_eq_bot, bot_sup_eq,
    ← (FTtype34_facts base).C_eq_derived_U]

private theorem ftType34_dade_virtual_final34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction M ℂ}
    (hphiVirtual : ClassFunction.IsVirtual phi)
    (hphiSupport : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M}) :
    ClassFunction.IsVirtual
      (Dade (FT_Dade0_hyp M base.maxM) phi) := by
  obtain ⟨z, hz⟩ := hphiVirtual
  obtain ⟨w, hw, _⟩ := (Dade_Zisometry
    (FT_Dade0_hyp M base.maxM)).2 z (by
      simpa [hz] using hphiSupport)
  exact ⟨w, by simpa [hz] using hw.symm⟩

private theorem ftType34_dade_pairing_final34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi psi : ClassFunction M ℂ}
    (hphiVirtual : ClassFunction.IsVirtual phi)
    (hpsiVirtual : ClassFunction.IsVirtual psi)
    (hphiSupport : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M})
    (hpsiSupport : psi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M}) :
    characterPairing
        (Dade (FT_Dade0_hyp M base.maxM) phi)
        (Dade (FT_Dade0_hyp M base.maxM) psi) =
      characterPairing phi psi := by
  have hDphiVirtual := ftType34_dade_virtual_final34
    base hphiVirtual hphiSupport
  have hDpsiVirtual := ftType34_dade_virtual_final34
    base hpsiVirtual hpsiSupport
  calc
    characterPairing
        (Dade (FT_Dade0_hyp M base.maxM) phi)
        (Dade (FT_Dade0_hyp M base.maxM) psi) =
        starCharacterPairing
          (Dade (FT_Dade0_hyp M base.maxM) phi)
          (Dade (FT_Dade0_hyp M base.maxM) psi) :=
      (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hDphiVirtual hDpsiVirtual).symm
    _ = starCharacterPairing phi psi :=
      Dade_isometry (FT_Dade0_hyp M base.maxM)
        phi psi hphiSupport hpsiSupport
    _ = characterPairing phi psi :=
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hphiVirtual hpsiVirtual

private theorem ftType34_pair_bridge_etaColumn_final34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ) (hzeta : zeta ∈ ftType34S1 base)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing
        (Dade (FT_Dade0_hyp M base.maxM) (muZero34 base - zeta))
        (∑ i : IrreducibleCharacter W₁ ℂ,
          base.isoG.cyclicTIImage (i, j)) = 1 := by
  classical
  rw [← base.targetMap_pairing, map_sum]
  change characterPairing (dadeBridgeZero34 base zeta)
    (etaColumn34 base j) = 1
  have hproj := (eqProjection34_iff base
    (dadeBridgeZero34 base zeta) (etaZeroRow34 base)).mp
      (FTtype34_zeroRowProjection34 base zeta hzeta)
  rw [etaColumn34]
  change characterPairingLeft (dadeBridgeZero34 base zeta)
    (∑ i, eta34 base i j) = 1
  rw [map_sum]
  calc
    (∑ i : IrreducibleCharacter W₁ ℂ,
        characterPairing (dadeBridgeZero34 base zeta)
          (eta34 base i j)) =
        ∑ i : IrreducibleCharacter W₁ ℂ,
          characterPairing (etaZeroRow34 base) (eta34 base i j) := by
      apply Finset.sum_congr rfl
      intro i _
      exact hproj i j
    _ = 1 := by
      rw [Finset.sum_eq_single
        (IrreducibleCharacter.trivial :
          IrreducibleCharacter W₁ ℂ)]
      · rw [characterPairing_etaZeroRow34, if_pos rfl]
      · intro i _ hi
        rw [characterPairing_etaZeroRow34, if_neg hi]
      · simp

/-! ## The fixed-point-free quotient orbit count -/

private noncomputable def pTypeQuotientMulAut_final34
    {E : Type*} [Group E] (N : Subgroup E) [N.Normal]
    (e : MulAut E) (hN : N.map e.toMonoidHom = N) :
    MulAut (E ⧸ N) := by
  have he : N ≤ N.comap e.toMonoidHom := by
    intro x hx
    change e x ∈ N
    have hx' : e x ∈ N.map e.toMonoidHom := ⟨x, hx, rfl⟩
    rwa [hN] at hx'
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

@[simp] private theorem pTypeQuotientMulAut_final34_apply_mk
    {E : Type*} [Group E] (N : Subgroup E) [N.Normal]
    (e : MulAut E) (hN : N.map e.toMonoidHom = N) (x : E) :
    pTypeQuotientMulAut_final34 N e hN (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N (e x) := by
  rfl

private noncomputable def pTypeQuotientMulAutHom_final34
    {A E : Type*} [Group A] [Group E]
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E)
    (hN : ∀ a, N.map (f a).toMonoidHom = N) :
    A →* MulAut (E ⧸ N) where
  toFun a := pTypeQuotientMulAut_final34 N (f a) (hN a)
  map_one' := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [pTypeQuotientMulAut_final34_apply_mk,
      map_one, MulAut.one_apply]
  map_mul' a b := by
    apply MulEquiv.ext
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N z
    simp only [pTypeQuotientMulAut_final34_apply_mk,
      map_mul, MulAut.mul_apply]

@[simp] private theorem pTypeQuotientMulAutHom_final34_apply_mk
    {A E : Type*} [Group A] [Group E]
    (N : Subgroup E) [N.Normal]
    (f : A →* MulAut E)
    (hN : ∀ a, N.map (f a).toMonoidHom = N)
    (a : A) (x : E) :
    pTypeQuotientMulAutHom_final34 N f hN a
        (QuotientGroup.mk' N x) =
      QuotientGroup.mk' N (f a x) := by
  exact pTypeQuotientMulAut_final34_apply_mk N (f a) (hN a) x

private theorem ftType34_q_le_u_of_one_lt_final34
    (base : FTType34Base M U W W₁ W₂ defW)
    (hu : 1 < base.u) : base.q ≤ base.u := by
  classical
  let D := factorAction34 base
  let hD := factorActionHypotheses34 base
  letI : D.C.Normal := D.C_normal
  let Q := U ⧸ D.C
  let alphaQ : W₁ →* MulAut Q :=
    pTypeQuotientMulAutHom_final34 D.C D.W₁_action_U D.C_invariant
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
      exact pTypeQuotientMulAutHom_final34_apply_mk
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
  have hcardU : base.u = 1 + t * base.q := by
    calc
      base.u = pTypeActionFactorCard D :=
        (ftType34_actionFactorCard_eq_u11 base).symm
      _ = Nat.card Q := rfl
      _ = 1 + t * Nat.card W₁ := hcardQ
      _ = 1 + t * base.q := rfl
  have ht : 0 < t := by
    by_contra ht
    have ht0 : t = 0 := Nat.eq_zero_of_not_pos ht
    rw [hcardU, ht0, zero_mul, add_zero] at hu
    omega
  calc
    base.q ≤ t * base.q := Nat.le_mul_of_pos_left base.q ht
    _ ≤ 1 + t * base.q := Nat.le_add_left _ _
    _ = base.u := hcardU.symm

/-! ## The non-Galois arithmetic contradiction -/

set_option maxHeartbeats 2500000 in
private theorem ftType34_typeP_Galois_final34
    (base : FTType34Base M U W W₁ W₂ defW) :
    typeP_Galois (factorAction34 base) := by
  classical
  let D := factorAction34 base
  let hD := factorActionHypotheses34 base
  by_contra hnot
  let a := pTypeNonGaloisIndex hD hnot
  let scale := base.u / a
  have haOne : 1 < a := one_lt_pTypeNonGaloisIndex hD hnot
  have haPos : 0 < a := Nat.zero_lt_of_lt haOne
  have haDvdU : a ∣ base.u := by
    change pTypeNonGaloisIndex hD hnot ∣ base.u
    rw [← ftType34_actionFactorCard_eq_u11 base]
    exact pTypeCore_nonGalois_index_dvd_factorCard
      base.ptypeCtx (factorFacts34 base) hnot

  let X := pTypeCoreLowerSlice
    base.ptypeCtx (factorFacts34 base) hnot
  let lower := ((D.p - 1) * (_root_.commutator U).index) / a ^ 2
  have hdenDvd : a ^ 2 ∣
      (D.p - 1) * (_root_.commutator U).index := by
    simpa only [D, hD, a] using
      pTypeCore_indexSquare_dvd_primePred_mul_derivedIndex
        base.ptypeCtx (factorFacts34 base) hnot
  have hlowerPos : 0 < lower := by
    have hpPredPos : 0 < D.p - 1 :=
      Nat.sub_pos_of_lt D.p_prime.one_lt
    have hvPos : 0 < (_root_.commutator U).index :=
      Nat.pos_of_ne_zero
        (_root_.commutator U).index_ne_zero_of_finite
    have hnumerPos : 0 <
        (D.p - 1) * (_root_.commutator U).index :=
      Nat.mul_pos hpPredPos hvPos
    have hcancel : lower * a ^ 2 =
        (D.p - 1) * (_root_.commutator U).index := by
      simpa only [lower] using Nat.div_mul_cancel hdenDvd
    by_contra hzero
    have hlowerZero : lower = 0 := Nat.eq_zero_of_not_pos hzero
    rw [hlowerZero, zero_mul] at hcancel
    omega
  have hcardLower : lower ≤ X.card := by
    simpa only [lower, X, D, hD, a] using
      pTypeCoreLowerSlice_card_lower_bound
        base.ptypeCtx (factorFacts34 base) hnot
  obtain ⟨lambda, hlambdaX⟩ :=
    Finset.card_pos.mp (hlowerPos.trans_le hcardLower)
  have hlambdaSlice :=
    pTypeCoreLowerSlice_subset_degreeSlice
      base.ptypeCtx (factorFacts34 base) hnot hlambdaX
  have hlambdaDegree : lambda 1 = ((D.q * a : ℕ) : ℂ) :=
    (Finset.mem_filter.mp hlambdaSlice).2
  have hlambdaIrr : IsIrreducibleCharacter M ℂ lambda :=
    pTypeCoreLowerSlice_irreducible hlambdaX
  let lambdaIrr : IrreducibleCharacter M ℂ := ⟨lambda, hlambdaIrr⟩
  have hlambdaS2 : lambda ∈ ftType34S2 base := by
    have hraw := (Finset.mem_filter.mp hlambdaX).1
    rw [ftType34_lowerKernel_eq_CInHU_final34 base] at hraw
    rw [ftType34S2_eq_H_C11 base]
    exact hraw

  letI : IsCyclic W₂ := base.primeTI.fixed_cyclic
  obtain ⟨j, hj⟩ :=
    IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) base.primeTI.prime_cycTIhyp.one_lt_card_right
  have hmuData := ftType34_mu_mem_S2_reducible11 base j hj
  have hmuS2 : mu34 base j ∈ ftType34S2 base := hmuData.1
  have hmuRed : ¬ IsIrreducibleCharacter M ℂ (mu34 base j) := hmuData.2
  have hmuDegree : mu34 base j 1 = ((base.q * base.u : ℕ) : ℂ) :=
    ftType34_mu_degree11 base j hj
  let psi : ClassFunction M ℂ :=
    mu34 base j - (scale : ℂ) • lambda
  have hscaleMul : scale * a = base.u := Nat.div_mul_cancel haDvdU
  have hpsiOne : psi 1 = 0 := by
    change mu34 base j 1 - (scale : ℂ) * lambda 1 = 0
    rw [hmuDegree, hlambdaDegree]
    have hDq : D.q = base.q := by
      simp only [D, factorAction34, Ptype_factor_action_q]
    apply sub_eq_zero.mpr
    have hnat : base.q * base.u = scale * (D.q * a) := by
      rw [hDq, ← hscaleMul]
      ring
    exact_mod_cast hnat
  have hlambdaVirtual : ClassFunction.IsVirtual lambda :=
    ⟨Finsupp.single lambdaIrr 1, by simp [lambdaIrr]⟩
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    exact (base.primeTI.prTIred_char base.isoM j).isVirtual.sub
      (hlambdaVirtual.natCast_smul scale)
  have hpsiClosure : psi ∈ AddSubgroup.closure
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ)) := by
    apply (AddSubgroup.closure
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))).sub_mem
    · exact AddSubgroup.subset_closure hmuS2
    · simpa only [Nat.cast_smul_eq_nsmul] using
        (AddSubgroup.closure
          (↑(ftType34S2 base) : Set (ClassFunction M ℂ))).nsmul_mem
            (AddSubgroup.subset_closure hlambdaS2) scale
  have hpsiOff : psi ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxOne : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    exact hpsiOne
  have hmuT : mu34 base j ∈ seqIndT (k := ℂ) base.HUInM :=
    ftType34_mu_mem_seqIndT_final34 base j
  have hlambdaT : lambda ∈ seqIndT (k := ℂ) base.HUInM := by
    rw [ftType34S2_eq_H_C11 base] at hlambdaS2
    exact ftType34_seqIndD_mem_seqIndT_final34
      base base.HInHU base.CInHU hlambdaS2
  have hpsiHU : psi ∈
      ClassFunction.supportedOn (base.HUInM : Set M) := by
    apply Submodule.sub_mem
    · exact seqInd_on base.HUInM hmuT
    · exact Submodule.smul_mem _ _ (seqInd_on base.HUInM hlambdaT)
  have hpsiFull : psi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxHU : x ∈ base.HUInM
    · have hxOne : x = 1 := by
        by_contra hxNe
        apply hx
        rw [FTsupp_eq1 base.maxM base.type_gt_two,
          FTsupp1_type_gt2 M base.type_gt_two]
        exact ⟨hxHU, fun hval => hxNe (Subtype.ext hval)⟩
      subst x
      exact ClassFunction.eq_zero_of_mem_supportedOn hpsiOff (by simp)
    · exact ClassFunction.eq_zero_of_mem_supportedOn hpsiHU hxHU
  have hpsiSupport : psi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
    rw [ClassFunction.mem_supportedOn_iff] at hpsiFull ⊢
    intro x hx
    apply hpsiFull x
    intro hxFull
    exact hx (FTsupp_sub0 M hxFull)

  obtain ⟨zeta, hzetaRef⟩ := FTtypeP_ref_irr base.maxM base.MtypeP
  have hzetaS1 : zeta ∈ ftType34S1 base :=
    ftType34_reference_mem_S1_34 base zeta hzetaRef
  let phi : ClassFunction M ℂ := muZero34 base - zeta
  let phiD : ClassFunction (⊤ : Subgroup G) ℂ :=
    Dade (FT_Dade0_hyp M base.maxM) phi
  have hphiVirtual : ClassFunction.IsVirtual phi := by
    simpa only [phi, ftType34Bridge0] using
      ftType34_bridgeZero_virtual34 base zeta hzetaS1
  have hphiFull : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
    simpa only [phi] using
      zeroColumn_fullSupport_projection34 base zeta hzetaRef
  have hphiSupport : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
    rw [ClassFunction.mem_supportedOn_iff] at hphiFull ⊢
    intro x hx
    apply hphiFull x
    intro hxFull
    exact hx (FTsupp_sub0 M hxFull)
  have hphiDVirtual : ClassFunction.IsVirtual phiD := by
    exact ftType34_dade_virtual_final34 base hphiVirtual hphiSupport

  have hzetaT : zeta ∈ seqIndT (k := ℂ) base.HUInM := by
    exact ftType34_seqIndD_mem_seqIndT_final34 base
      (⊤ : Subgroup base.HUInM) base.HCInHU hzetaS1
  have hmuZeroT : muZero34 base ∈
      seqIndT (k := ℂ) base.HUInM :=
    ftType34_mu_mem_seqIndT_final34 base
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  have hmuZeroMu : muZero34 base ≠ mu34 base j := by
    intro heq
    have hindex :
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) = j :=
      base.primeTI.prTIred_inj base.isoM heq
    exact hj hindex.symm
  have hzetaMu : zeta ≠ mu34 base j := by
    intro heq
    exact hmuRed (heq ▸ hzetaRef.irreducible)
  have hmuZeroLambda : muZero34 base ≠ lambda := by
    intro heq
    have hirrZero : IsIrreducibleCharacter M ℂ (muZero34 base) :=
      heq.symm ▸ hlambdaIrr
    change IsIrreducibleCharacter M ℂ
      (base.primeTI.primeTIRed base.isoM
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) at hirrZero
    exact (base.primeTI.prTIred_not_irr base.isoM
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) hirrZero
  have hzetaLambda : zeta ≠ lambda := by
    intro heq
    have hdegree := congrArg (fun f : ClassFunction M ℂ => f 1) heq
    rw [hzetaRef.degree, hlambdaDegree] at hdegree
    have hDq : D.q = base.q := by
      simp only [D, factorAction34, Ptype_factor_action_q]
    rw [hDq] at hdegree
    have hnat : base.q = base.q * a := by exact_mod_cast hdegree
    have hmul : base.q * 1 = base.q * a := by simpa using hnat
    have hOneA : 1 = a :=
      Nat.eq_of_mul_eq_mul_left base.q_prime.pos hmul
    exact haOne.ne hOneA
  have hmuZeroMuPair : characterPairing (muZero34 base)
      (mu34 base j) = 0 :=
    seqInd_ortho base.HUInM hmuZeroT hmuT hmuZeroMu
  have hmuZeroLambdaPair : characterPairing (muZero34 base)
      lambda = 0 :=
    seqInd_ortho base.HUInM hmuZeroT hlambdaT hmuZeroLambda
  have hzetaMuPair : characterPairing zeta (mu34 base j) = 0 :=
    seqInd_ortho base.HUInM hzetaT hmuT hzetaMu
  have hzetaLambdaPair : characterPairing zeta lambda = 0 :=
    seqInd_ortho base.HUInM hzetaT hlambdaT hzetaLambda
  have hsourcePair : characterPairing phi psi = 0 := by
    rw [show phi = muZero34 base - zeta from rfl,
      show psi = mu34 base j - (scale : ℂ) • lambda from rfl,
      pairing_sub_left_final34, pairing_sub_right_final34,
      pairing_sub_right_final34, characterPairing_smul_right,
      characterPairing_smul_right,
      hmuZeroMuPair, hmuZeroLambdaPair, hzetaMuPair,
      hzetaLambdaPair]
    simp

  have hcore := Ptype_core_coherence
    base.maxM defW base.MtypeP base.notMtype5
  dsimp only at hcore
  have hctx :
      Ptype_Fcore_context base.maxM defW base.MtypeP base.notMtype5 =
        base.ptypeCtx := Subsingleton.elim _ _
  rw [hctx] at hcore
  have hS2Dade := subset_coherent
    (ftType34S2_subset_core11 base) hcore
  obtain ⟨tau2, hcoh2⟩ := hS2Dade
  have hagreePsi : tau2 psi =
      Dade (FT_Dade0_hyp M base.maxM) psi :=
    hcoh2.agrees psi hpsiClosure hpsiOff
  have hpairPsi : characterPairing phiD (tau2 psi) = 0 := by
    rw [hagreePsi]
    exact (ftType34_dade_pairing_final34 base
      hphiVirtual hpsiVirtual hphiSupport hpsiSupport).trans hsourcePair

  have hcases := FTtypeP_coherent_TIred
    base.primeDade base.isoM base.isoG (mFT_odd M)
    (↑(ftType34S2 base) : Set (ClassFunction M ℂ)) tau2
    lambdaIrr j (ftType34S2_subset_kernelLayer_final34 base)
    hcoh2 hlambdaS2 hmuS2
  have hpairMu : ∃ epsilon : ℤ, IsSign epsilon ∧
      characterPairing phiD (tau2 (mu34 base j)) = (epsilon : ℂ) := by
    rcases hcases with hfirst | hsecond
    · refine ⟨base.primeTI.primeTISign base.isoM j,
        base.primeTI.primeTISign_isSign base.isoM j, ?_⟩
      rw [hfirst, characterPairing_smul_right]
      rw [ftType34_pair_bridge_etaColumn_final34 base zeta hzetaS1 j]
      simp
    · rcases hsecond with ⟨hdual, _⟩
      refine ⟨-base.primeTI.primeTISign base.isoM j, ?_, ?_⟩
      · rcases base.primeTI.primeTISign_isSign base.isoM j with
          hsign | hsign <;> rw [hsign] <;> simp [IsSign]
      · rw [hdual, characterPairing_smul_right]
        rw [ftType34_pair_bridge_etaColumn_final34 base zeta hzetaS1
          (IrreducibleCharacter.dual j)]
        simp
  obtain ⟨epsilon, hepsilon, hpairMu⟩ := hpairMu
  have htauPsi : tau2 psi = tau2 (mu34 base j) -
      (scale : ℂ) • tau2 lambda := by
    simp only [psi, map_sub, map_smul]
  have hscalePair : (scale : ℂ) *
      characterPairing phiD (tau2 lambda) = (epsilon : ℂ) := by
    rw [htauPsi, pairing_sub_right_final34,
      characterPairing_smul_right, hpairMu] at hpairPsi
    simpa using (sub_eq_zero.mp hpairPsi).symm
  have htauLambdaVirtual : ClassFunction.IsVirtual (tau2 lambda) :=
    hcoh2.mapsToVirtual lambda
      (AddSubgroup.subset_closure hlambdaS2)
  obtain ⟨n, hn⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt
      hphiDVirtual htauLambdaVirtual
  rw [hn] at hscalePair
  have hint : (scale : ℤ) * n = epsilon := by
    exact_mod_cast hscalePair
  have hscale : scale = 1 := by
    rcases hepsilon with rfl | rfl
    · rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp hint with h | h
      · exact_mod_cast h.1
      · have hsNonneg : (0 : ℤ) ≤ scale := Int.natCast_nonneg scale
        omega
    · rcases Int.mul_eq_neg_one_iff_eq_one_or_neg_one.mp hint with h | h
      · exact_mod_cast h.1
      · have hsNonneg : (0 : ℤ) ≤ scale := Int.natCast_nonneg scale
        omega
  have huEq : base.u = a := by
    calc
      base.u = scale * a := (Nat.div_mul_cancel haDvdU).symm
      _ = 1 * a := by rw [hscale]
      _ = a := one_mul a
  have hqLeU : base.q ≤ base.u :=
    ftType34_q_le_u_of_one_lt_final34 base (huEq.symm ▸ haOne)
  have haDvdPred : a ∣ D.p - 1 :=
    pTypeNonGaloisIndex_dvd_prime_pred hD hnot
  have haLePred : a ≤ D.p - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt D.p_prime.one_lt) haDvdPred
  have hDp : D.p = base.p := by
    simp only [D, factorAction34,
      Ptype_factor_action_p,
      typeIII_IV_core_prime base.ptypeCtx base.notMtype2]
  have hpLtq := ftType34_p_lt_q_final34 base
  rw [huEq] at hqLeU
  rw [hDp] at haLePred
  omega

/-! ## A finite nilpotent group with cyclic abelianization is cyclic -/

private theorem commutator_le_frattini_of_nilpotent_final34
    {A : Type} [Group A] [Finite A] [Group.IsNilpotent A] :
    _root_.commutator A ≤ frattini A := by
  rw [frattini, Order.radical]
  apply le_iInf
  intro H
  apply le_iInf
  intro hH
  change IsCoatom H at hH
  letI : H.Normal :=
    ((Group.isNilpotent_of_finite_tfae (G := A)).out 0 2 rfl rfl).mp
      (inferInstance : Group.IsNilpotent A) H hH
  by_contra hnot
  have hsupNe : H ⊔ _root_.commutator A ≠ H := by
    intro heq
    exact hnot (sup_eq_left.mp heq)
  have hlt : H < H ⊔ _root_.commutator A :=
    lt_of_le_of_ne le_sup_left hsupNe.symm
  have hsup : H ⊔ _root_.commutator A = ⊤ := hH.lt_iff.mp hlt
  let Q := A ⧸ H
  letI : Nontrivial Q := QuotientGroup.nontrivial_iff.mpr hH.1
  letI : Group.IsNilpotent Q := by infer_instance
  have hcommTop : _root_.commutator Q = ⊤ := by
    have hsur : Function.Surjective (QuotientGroup.mk' H) :=
      QuotientGroup.mk'_surjective H
    have hmapComm :
        (_root_.commutator A).map (QuotientGroup.mk' H) =
          _root_.commutator Q := by
      rw [map_commutator_eq,
        MonoidHom.range_eq_top.mpr hsur]
      rfl
    have hmapTop :
        (⊤ : Subgroup A).map (QuotientGroup.mk' H) =
          (⊤ : Subgroup Q) :=
      Subgroup.map_top_of_surjective (QuotientGroup.mk' H) hsur
    have hmap := congrArg
      (fun K : Subgroup A => K.map (QuotientGroup.mk' H)) hsup
    simpa only [Subgroup.map_sup, QuotientGroup.map_mk'_self,
      hmapComm, hmapTop, bot_sup_eq] using hmap
  exact (IsSolvable.commutator_lt_top_of_nontrivial Q).ne hcommTop

private theorem isCyclic_of_nilpotent_cyclic_abelianization_final34
    {A : Type} [Group A] [Finite A] [Group.IsNilpotent A]
    [IsCyclic (A ⧸ _root_.commutator A)] :
    IsCyclic A := by
  let D : Subgroup A := _root_.commutator A
  obtain ⟨x, hx⟩ := isCyclic_iff_exists_zpowers_eq_top.mp
    (inferInstance : IsCyclic (A ⧸ D))
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective D x
  have hmap : (Subgroup.zpowers g).map (QuotientGroup.mk' D) = ⊤ := by
    rw [MonoidHom.map_zpowers, hx]
  have hsupD : Subgroup.zpowers g ⊔ D = ⊤ := by
    calc
      Subgroup.zpowers g ⊔ D =
          ((Subgroup.zpowers g).map (QuotientGroup.mk' D)).comap
            (QuotientGroup.mk' D) := by
        rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
      _ = ⊤ := by rw [hmap, Subgroup.comap_top]
  have hDfrattini : D ≤ frattini A :=
    commutator_le_frattini_of_nilpotent_final34
  have hsupFrattini : Subgroup.zpowers g ⊔ frattini A = ⊤ := by
    apply top_unique
    rw [← hsupD]
    exact sup_le_sup le_rfl hDfrattini
  exact isCyclic_iff_exists_zpowers_eq_top.mpr
    ⟨g, frattini_nongenerating hsupFrattini⟩

private theorem ftType34_CInU_eq_commutator_final34
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.CInU = _root_.commutator U := by
  apply Subgroup.map_injective U.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le base.C_le_U]
  simpa only [FTType34Base.U', derivedWithin] using
    (FTtype34_facts base).C_eq_derived_U

private theorem ftType34_type_eq_three_final34
    (base : FTType34Base M U W W₁ W₂ defW)
    (hGalois : typeP_Galois (factorAction34 base)) :
    FTtype M = 3 := by
  let D := factorAction34 base
  letI : D.C.Normal := D.C_normal
  have hcyclicFactor : IsCyclic (U ⧸ D.C) :=
    (typeP_Galois_P (factorActionHypotheses34 base)
      hGalois).complement_factor_cyclic
  have hDC : D.C = base.CInU := by
    simpa only [D, factorAction34, factorFacts34] using
        ftType34_actionKernel_eq_CInU11 base
  have hCcomm : base.CInU = _root_.commutator U :=
    ftType34_CInU_eq_commutator_final34 base
  have hDCcomm : D.C = _root_.commutator U := hDC.trans hCcomm
  have hcyclicAb : IsCyclic (U ⧸ _root_.commutator U) := by
    exact (QuotientGroup.quotientMulEquivOfEq hDCcomm).isCyclic.mp
      hcyclicFactor
  letI : Group.IsNilpotent U := base.MtypeP.2.1.1
  letI : IsCyclic (U ⧸ _root_.commutator U) := hcyclicAb
  letI : IsCyclic U :=
    isCyclic_of_nilpotent_cyclic_abelianization_final34
  have hUcomm : IsMulCommutative U := IsCyclic.isMulCommutative
  rcases base.type_eq_three_or_four with hthree | hfour
  · exact hthree
  · exact ((compl_of_typeIV M U W W₁ W₂ defW
      base.maxM base.MtypeP hfour).2.1 hUcomm).elim


end FTType34StructureInternal

/-- Peterfalvi (11.9). -/
theorem FTtype34_structure
    (base : FTType34Base M U W W₁ W₂ defW) :
    (∀ zeta ∈ ftType34S1 base,
      let eta := fun (i : IrreducibleCharacter W₁ ℂ)
          (j : IrreducibleCharacter W₂ ℂ) ↦
        base.targetMap (base.isoG.cyclicTIImage (i, j))
      let muZero :=
        base.primeTI.primeTIRed base.isoM
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
      let etaZeroRow :=
        ∑ j : IrreducibleCharacter W₂ ℂ,
          eta
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₁ ℂ) j
      ∀ i j, characterPairing
        (base.tau (muZero - zeta) - etaZeroRow) (eta i j) = 0) ∧
      base.p < base.q ∧
      FTtype M = 3 ∧
      typeP_Galois
        (Ptype_factor_action base.ptypeCtx
          (Ptype_Fcore_factor_facts base.ptypeCtx)) := by
  have hprojection :=
    FTType34StructureInternal.FTtype34_zeroRowProjection34 base
  have hpq :=
    FTType34StructureInternal.ftType34_p_lt_q_final34 base
  have hGalois :=
    FTType34StructureInternal.ftType34_typeP_Galois_final34 base
  have htype :=
    FTType34StructureInternal.ftType34_type_eq_three_final34 base hGalois
  refine ⟨?_, hpq, htype, ?_⟩
  · intro zeta hzeta
    change FTType34StructureInternal.eqProjection34 base
      (FTType34StructureInternal.dadeBridgeZero34 base zeta)
      (FTType34StructureInternal.etaZeroRow34 base)
    exact hprojection zeta hzeta
  · simpa only [FTType34StructureInternal.factorAction34,
      FTType34StructureInternal.factorFacts34] using hGalois

end

end Submission.OddOrder.PF
