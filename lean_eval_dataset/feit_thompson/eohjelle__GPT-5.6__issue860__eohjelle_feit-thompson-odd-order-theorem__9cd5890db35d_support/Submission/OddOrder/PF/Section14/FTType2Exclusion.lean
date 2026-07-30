import Mathlib.Analysis.Complex.ExponentialBounds
import Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism
import Submission.OddOrder.PF.Section14.FullGaloisExclusion

/-!
# Peterfalvi Section 14: exclusion of type II

This file proves the type-II maximal and minimal assertions and the final
contradiction from `PFsection14.v`, lines 478--1209.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.AppendixC
open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]

local instance (priority := 10) ftt2Fintype
    (X : Type*) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-! The type-I comparison lemmas are stated over the ambient top subgroup,
whereas the source-facing hypotheses below use class functions on `G`.
These mutually inverse transports keep that distinction local. -/

private noncomputable def ftt2SourceMap :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

private noncomputable def ftt2TargetMap :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

@[simp] private theorem ftt2_source_target
    (f : ClassFunction (⊤ : Subgroup G) ℂ) :
    ftt2SourceMap (ftt2TargetMap f) = f := by
  ext x
  simpa [ftt2SourceMap, ftt2TargetMap, ClassFunction.comap_apply] using
    congrArg f (Subgroup.topEquiv.symm_apply_apply x)

@[simp] private theorem ftt2_target_source
    (f : ClassFunction G ℂ) :
    ftt2TargetMap (ftt2SourceMap f) = f := by
  ext x
  simpa [ftt2SourceMap, ftt2TargetMap, ClassFunction.comap_apply] using
    congrArg f (Subgroup.topEquiv.apply_symm_apply x)

private theorem ftt2_target_pairing
    (f g : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (ftt2TargetMap f) (ftt2TargetMap g) =
      characterPairing f g := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [ftt2TargetMap, ClassFunction.comap_apply]

private theorem ftt2_source_pairing
    (f g : ClassFunction G ℂ) :
    characterPairing (ftt2SourceMap f) (ftt2SourceMap g) =
      characterPairing f g := by
  rw [← ftt2_target_pairing (ftt2SourceMap f) (ftt2SourceMap g)]
  simp

private theorem ftt2_target_starPairing
    (f g : ClassFunction (⊤ : Subgroup G) ℂ) :
    starCharacterPairing (ftt2TargetMap f) (ftt2TargetMap g) =
      starCharacterPairing f g := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold starCharacterPairing twistedCharacterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [ftt2TargetMap, ClassFunction.comap_apply]

private theorem ftt2_source_starPairing
    (f g : ClassFunction G ℂ) :
    starCharacterPairing (ftt2SourceMap f) (ftt2SourceMap g) =
      starCharacterPairing f g := by
  rw [← ftt2_target_starPairing (ftt2SourceMap f) (ftt2SourceMap g)]
  simp

private theorem ftt2_target_normSq
    (f : ClassFunction (⊤ : Subgroup G) ℂ) :
    classFunctionNormSq (ftt2TargetMap f) = classFunctionNormSq f := by
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    ftt2_target_starPairing,
    ← classFunctionNormSq_eq_re_starCharacterPairing]

private theorem ftt2_source_normSq (f : ClassFunction G ℂ) :
    classFunctionNormSq (ftt2SourceMap f) = classFunctionNormSq f := by
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    ftt2_source_starPairing,
    ← classFunctionNormSq_eq_re_starCharacterPairing]

private theorem ftt2_target_virtual
    {f : ClassFunction (⊤ : Subgroup G) ℂ}
    (hf : ClassFunction.IsVirtual f) :
    ClassFunction.IsVirtual (ftt2TargetMap f) := by
  obtain ⟨z, rfl⟩ := hf
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.symm.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap]
  rfl

private theorem ftt2_source_virtual
    {f : ClassFunction G ℂ} (hf : ClassFunction.IsVirtual f) :
    ClassFunction.IsVirtual (ftt2SourceMap f) := by
  obtain ⟨z, rfl⟩ := hf
  refine ⟨VirtualCharacter.comap Subgroup.topEquiv.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap]
  rfl

private theorem ftt2CoherentWith_sourceMap
    {Q : Type} [Group Q] [Fintype Q]
    {calS : Set (ClassFunction Q ℂ)} {A : Set Q}
    {sigma nu : ClassFunction Q ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hcoh : coherent_with calS A sigma nu) :
    coherent_with calS A (ftt2SourceMap.comp sigma)
      (ftt2SourceMap.comp nu) := by
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro phi hphi psi hpsi
    simpa [LinearMap.comp_apply] using
      (ftt2_source_pairing (nu phi) (nu psi)).trans
        (hcoh.isometry phi hphi psi hpsi)
  · intro phi hphi
    exact ftt2_source_virtual (hcoh.mapsToVirtual phi hphi)
  · intro phi hphi hsupp
    exact congrArg ftt2SourceMap (hcoh.agrees phi hphi hsupp)

@[simp] private theorem ftt2_source_ftType1Dade
    {L : Subgroup G}
    (maxL : L ∈ minSimple_max_groups (G := G))
    (phi : ClassFunction L ℂ) :
    ftt2SourceMap (FTtype1Dade L maxL phi) =
      Dade (FT_DadeF_hyp L maxL) phi := by
  change ftt2SourceMap
    (ftt2TargetMap (Dade (FT_DadeF_hyp L maxL) phi)) = _
  exact ftt2_source_target _

@[simp] private theorem ftt2_source_comp_ftType1Dade
    {L : Subgroup G}
    (maxL : L ∈ minSimple_max_groups (G := G)) :
    ftt2SourceMap.comp (FTtype1Dade L maxL) =
      Dade (FT_DadeF_hyp L maxL) := by
  apply LinearMap.ext
  intro phi
  exact ftt2_source_ftType1Dade maxL phi

private theorem ftt2Type1Coherence_top
    {L : Subgroup G}
    {maxL : L ∈ minSimple_max_groups (G := G)}
    {tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁) :
    coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade (FT_DadeF_hyp L maxL))
      (ftt2SourceMap.comp tau₁) := by
  simpa only [ftt2_source_comp_ftType1Dade] using
    ftt2CoherentWith_sourceMap cohL

@[simp] private theorem ftt2_fittingIn_map_subtype
    (L : Subgroup G) :
    (FTType1FittingIn L).map L.subtype = Fitting_core L := by
  simpa only [FTType1FittingIn] using
    Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)

private noncomputable def ftt2Type1DadeHypothesis
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G)) :
    DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity ((FTType1FittingIn L).map L.subtype)) := by
  simpa only [ftt2_fittingIn_map_subtype] using
    FT_DadeF_hyp L maxL

private theorem ftt2_Dade_support_eq_of_set_eq
    {Γ : Type*} [Group Γ]
    {K L : Subgroup Γ} {A B : Set Γ}
    (hAB : A = B) (ddA : DadeHypothesis K L A)
    (ddB : DadeHypothesis K L B) :
    Dade_support ddA = Dade_support ddB := by
  subst B
  congr

private theorem ftt2_target_dadeInd1Beta
    {L : Subgroup G}
    (maxL : L ∈ minSimple_max_groups (G := G))
    (dd : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity
        ((FTType1FittingIn L).map L.subtype)))
    (phi : ClassFunction L ℂ) :
    ftt2TargetMap
        (dadeInd1Beta (FTType1FittingIn L) dd phi) =
      FTtype1Dade L maxL (FTtype1Bridge L phi) := by
  simpa only [dadeInd1Beta, dadeInducedTrivial, FTtype1Dade,
    FTtype1Bridge, ftt2TargetMap, LinearMap.comp_apply,
    FTType1FittingIn,
    Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)]

private theorem ftt2_actionKernel_eq_bot
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.D.C = ⊥ := by
  apply (Subgroup.map_eq_bot_iff_of_injective
    ctx.D.C U.subtype_injective).mp
  change (ptypeFCoreAction ctx.ptypeCtx).ker.map U.subtype = ⊥
  simpa only [Ptype_Fcompl_kernel] using
    Ptype_Fcompl_kernel_trivial ctx

private theorem ftt2_u_eq_card
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.u = Nat.card U := by
  change (ctx.C.subgroupOf U).index = Nat.card U
  rw [FTtypeP_reg_Fcore ctx, Subgroup.bot_subgroupOf,
    Subgroup.index_bot]

private theorem ftt2_galois_card_of_swapped_lt
    {T V W W₂ W₁ : Subgroup G}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (hlt : ctxT.p < ctxT.q) :
    ctxT.galoisAlternative ∧
      Nat.card V = nU ctxT.p ctxT.q := by
  have hprimes : ctxT.q.Prime ∧ ctxT.p.Prime :=
    FTtypeP_primes T V W W₂ W₁ xdefW ctxT.maxS ctxT.StypeP
  have hthree : 3 ≤ ctxT.p := by
    apply hprimes.2.odd_iff.mp
    change Odd (Nat.card W₁)
    exact mFT_odd W₁
  have hGalT : ctxT.galoisAlternative := by
    by_contra hnot
    have hq : ctxT.q = 3 := (FTtypeP_nonGalois_facts ctxT hnot).1
    omega
  have hnotMod : ¬ Nat.ModEq ctxT.q ctxT.p 1 := by
    intro hmod
    have hpOne : ctxT.p = 1 :=
      hmod.eq_of_lt_of_lt hlt hprimes.1.one_lt
    exact hprimes.2.ne_one hpOne
  refine ⟨hGalT, ?_⟩
  calc
    Nat.card V = ctxT.ustar := by
      simpa only [if_neg hnotMod] using
        card_FTtypeP_Galois_compl ctxT hGalT
    _ = nU ctxT.p ctxT.q := by
      simpa only [FTTypePSetupContext.ustar] using
        (nU_eq_div_of_prime hprimes.2).symm

private theorem ftt2_frobeniusIn_decomposition
    {H E L : Subgroup G} (h : IsFrobeniusIn H E L) :
    IsFrobeniusDecomposition (H.subgroupOf L) (E.subgroupOf L) := by
  let J := H ⊔ E
  let e : J ≃* L := MulEquiv.subgroupCongr h.1
  have hfrob := FTContextInternal.frobenius_map_mulEquiv8 h.2.2 e
  have hHmap :
      (H.subgroupOf J).map e.toMonoidHom = H.subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  have hEmap :
      (E.subgroupOf J).map e.toMonoidHom = E.subgroupOf L := by
    ext x
    rw [Subgroup.mem_map_equiv]
    rfl
  rw [hHmap, hEmap] at hfrob
  exact hfrob

private theorem ftt2_mem_kernel_of_commute
    {Q : Type*} [Group Q] [Finite Q]
    {K R : Subgroup Q}
    (hFrob : IsFrobeniusDecomposition K R)
    {g : Q} {k : K} (hk : k ≠ 1)
    (hcomm : Commute g (k : Q)) :
    g ∈ K := by
  by_contra hg
  obtain ⟨x, hx⟩ :=
    hFrob.exists_kernel_conjugate_complement_of_not_mem hg
  rcases hx with ⟨r, hr, hrg⟩
  have hrg' : (x : Q) * r * (x : Q)⁻¹ = g := by
    simpa [MulAut.conj_apply] using hrg
  let rR : R := ⟨r, hr⟩
  have hrNe : rR ≠ 1 := by
    intro hrOne
    apply hg
    have hrOneQ : r = 1 := congrArg Subtype.val hrOne
    rw [← hrg', hrOneQ]
    simpa using x.property
  let kx : K :=
    ⟨(x : Q)⁻¹ * (k : Q) * (x : Q),
      by
        simpa using hFrob.kernel_normal.conj_mem
          (k : Q) k.property (x : Q)⁻¹⟩
  have hkxNe : kx ≠ 1 := by
    intro hkxOne
    apply hk
    apply Subtype.ext
    have hkxValue : (kx : Q) = 1 := congrArg Subtype.val hkxOne
    change (x : Q)⁻¹ * (k : Q) * (x : Q) = 1 at hkxValue
    calc
      (k : Q) =
          (x : Q) * ((x : Q)⁻¹ * (k : Q) * (x : Q)) *
            (x : Q)⁻¹ := by group
      _ = 1 := by rw [hkxValue]; simp
  have hfixed :
      (rR : Q) * (kx : Q) * (rR : Q)⁻¹ = (kx : Q) := by
    change r * ((x : Q)⁻¹ * (k : Q) * (x : Q)) * r⁻¹ =
      (x : Q)⁻¹ * (k : Q) * (x : Q)
    calc
      r * ((x : Q)⁻¹ * (k : Q) * (x : Q)) * r⁻¹ =
          (x : Q)⁻¹ *
            (((x : Q) * r * (x : Q)⁻¹) * (k : Q) *
              ((x : Q) * r * (x : Q)⁻¹)⁻¹) * (x : Q) := by
        group
      _ = (x : Q)⁻¹ * (g * (k : Q) * g⁻¹) * (x : Q) := by
        rw [hrg']
      _ = (x : Q)⁻¹ * ((k : Q) * g * g⁻¹) * (x : Q) := by
        rw [hcomm.eq]
      _ = (x : Q)⁻¹ * (k : Q) * (x : Q) := by simp
  exact hkxNe (hFrob.fixedPointFree rR hrNe kx hfixed)

private theorem ftt2_semiregular_of_semidirect_complement
    {K E R A L : Subgroup G}
    (hFrob : IsFrobeniusIn K E L)
    (hsd : IsInternalSemidirectProductIn K R L)
    (hAR : A ≤ R) :
    IsSemiregularConjugation K A := by
  let KL : Subgroup L := K.subgroupOf L
  let RL : Subgroup L := R.subgroupOf L
  have hExisting :
      IsFrobeniusDecomposition KL (E.subgroupOf L) := by
    simpa only [KL] using ftt2_frobeniusIn_decomposition hFrob
  intro a ha k hfix
  by_contra hk
  have hAL : A ≤ L := hAR.trans hsd.2.1
  let aL : L := ⟨(a : G), hAL a.property⟩
  let kL : KL :=
    ⟨⟨(k : G), hsd.1 k.property⟩, k.property⟩
  have hkL : kL ≠ 1 := by
    intro hkOne
    apply hk
    apply Subtype.ext
    exact congrArg (fun z : KL ↦ (((z : L) : G))) hkOne
  have hcomm : Commute aL (kL : L) := by
    rw [commute_iff_eq]
    apply Subtype.ext
    exact mul_inv_eq_iff_eq_mul.mp hfix
  have haK : aL ∈ KL :=
    ftt2_mem_kernel_of_commute hExisting hkL hcomm
  have haR : aL ∈ RL := hAR a.property
  have hInfBot : KL ⊓ RL = ⊥ :=
    disjoint_iff.mp hsd.2.2.2.disjoint
  have haBot : aL ∈ (⊥ : Subgroup L) := by
    rw [← hInfBot]
    exact ⟨haK, haR⟩
  have haLOne : aL = 1 := Subgroup.mem_bot.mp haBot
  apply ha
  apply Subtype.ext
  exact congrArg (fun z : L ↦ (z : G)) haLOne

private theorem ftt2_semiregular_card_dvd_sub_one
    {Q : Type*} [Group Q] [Finite Q]
    {A R : Subgroup Q}
    (hreg : IsSemiregularConjugation A R)
    (hnorm : R ≤ Subgroup.normalizer (A : Set Q)) :
    Nat.card R ∣ Nat.card A - 1 := by
  letI := subgroupConjugationAction A R hnorm
  have hfixed : ∀ r : R, r ≠ 1 → ∀ a : A,
      r • a = a → a = 1 := by
    intro r hr a ha
    apply hreg r hr a
    simpa only [coe_subgroupConjugationAction_smul A R hnorm] using
      congrArg Subtype.val ha
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := A))
  have hcard : Nat.card A = 1 + t * Nat.card R := by
    simpa [t] using natCard_eq_one_add_fixedOneOrbits_mul_natCard
      (G := R) (X := A) (fun r ↦ smul_one r) hfixed
  refine ⟨t, ?_⟩
  rw [hcard]
  simp [Nat.mul_comm]

private theorem ftt2_frobenius_index_dvd_kernel_sub_one
    {H E L : Subgroup G} (hFrob : IsFrobeniusIn H E L) :
    (H.subgroupOf L).index ∣ Nat.card H - 1 := by
  let HL : Subgroup L := H.subgroupOf L
  let EL : Subgroup L := E.subgroupOf L
  have hHL : H ≤ L := by
    rw [← hFrob.1]
    exact le_sup_left
  have hHcard : Nat.card HL = Nat.card H :=
    MathlibSupport.natCard_subgroupOf_eq hHL
  have hdecomp : IsFrobeniusDecomposition HL EL := by
    simpa only [HL, EL] using ftt2_frobeniusIn_decomposition hFrob
  have hdiv : Nat.card EL ∣ Nat.card HL - 1 := by
    letI : MulDistribMulAction EL HL := hdecomp.conjugationAction
    let t := Nat.card
      (nonidentityFixedOneOrbitQuotient (G := EL) (X := HL))
    have hcard : Nat.card HL = 1 + t * Nat.card EL := by
      simpa [t] using hdecomp.kernel_card_eq_one_add_orbits_mul_card
    refine ⟨t, ?_⟩
    rw [hcard]
    simp [Nat.mul_comm]
  change HL.index ∣ Nat.card H - 1
  rw [hdecomp.isComplement.symm.index_eq_card, ← hHcard]
  exact hdiv

private theorem ftt2_frobenius_pred_dvd
    {Q : Type*} [Group Q] [Finite Q]
    {K R : Subgroup Q} (h : IsFrobeniusDecomposition K R) :
    Nat.card R ∣ Nat.card K - 1 := by
  letI : MulDistribMulAction R K := h.conjugationAction
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := K))
  have hcard : Nat.card K = 1 + t * Nat.card R := by
    simpa only [t] using h.kernel_card_eq_one_add_orbits_mul_card
  refine ⟨t, ?_⟩
  rw [hcard]
  simp [Nat.mul_comm]

private theorem ftt2_nU_modEq_one
    {p q : ℕ} (hq : 0 < q) :
    Nat.ModEq p (nU p q) 1 := by
  obtain ⟨r, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq.ne'
  change Nat.ModEq p (∑ i ∈ Finset.range (r + 1), p ^ i) 1
  rw [geom_sum_succ]
  exact Nat.modulus_mul_add_modEq_iff.mpr Nat.ModEq.rfl

private theorem ftt2_pairing_sub_left
    {Q : Type*} [Group Q] [Fintype Q]
    (f g z : ClassFunction Q ℂ) :
    characterPairing (f - g) z =
      characterPairing f z - characterPairing g z := by
  change characterPairingRight z (f - g) = _
  exact map_sub (characterPairingRight z) f g

private theorem ftt2_pairing_sub_right
    {Q : Type*} [Group Q] [Fintype Q]
    (f g z : ClassFunction Q ℂ) :
    characterPairing f (g - z) =
      characterPairing f g - characterPairing f z := by
  rw [characterPairing_comm, ftt2_pairing_sub_left,
    characterPairing_comm g, characterPairing_comm z]

private theorem ftt2_pairing_fintype_sum_left
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ) (g : ClassFunction Q ℂ) :
    characterPairing (∑ i, f i) g =
      ∑ i, characterPairing (f i) g := by
  change characterPairingRight g (∑ i, f i) = _
  exact map_sum (characterPairingRight g) f Finset.univ

private theorem ftt2_eta_mem_cyclicImageFamily
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ctx.eta i j ∈ FTtypePCyclicImageFamily ctx := by
  rw [FTtypePCyclicImageFamily, Finset.mem_image]
  refine ⟨(IrreducibleCharacter.cyclicTICharacter defW i j :
      ClassFunction W ℂ), ?_, rfl⟩
  change
    (IrreducibleCharacter.cyclicTICharacter defW i j :
      ClassFunction W ℂ) ∈
      Finset.univ.image
        (fun chi : IrreducibleCharacter W ℂ ↦
          (chi : ClassFunction W ℂ))
  rw [Finset.mem_image]
  exact ⟨IrreducibleCharacter.cyclicTICharacter defW i j,
    Finset.mem_univ _, rfl⟩

private theorem ftt2_subgroup_characteristic_of_isCyclic
    {C : Type*} [Group C] [IsCyclic C] (K : Subgroup C) :
    K.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  obtain ⟨m, hm⟩ := e.toMonoidHom.map_cyclic
  rintro _ ⟨x, hx, rfl⟩
  rw [hm]
  exact K.zpow_mem hx m

private theorem ftt2_exceptional_prime_cards
    {p q v : ℕ}
    (hpPrime : p.Prime) (hqPrime : q.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hqp : q < p)
    (hv : v = nU q p)
    (hPowSwap : p ^ (q + 1) < q ^ (p + 1))
    (hcore :
      ((((v - 1 : ℕ) : ℝ)) / (((p * q : ℕ) : ℝ))) ≤
        (((p * q : ℕ) : ℝ)) - 1) :
    q = 3 ∧ p = 5 := by
  have hpThree : 3 ≤ p := hpPrime.odd_iff.mp hpOdd
  have hqThree : 3 ≤ q := hqPrime.odd_iff.mp hqOdd
  have hvPos : 0 < v := by
    rw [hv, ← Nat.succ_pred_eq_of_pos hpPrime.pos, nU_succ]
    exact Nat.add_pos_right _ (pow_pos hqPrime.pos _)
  have hvOne : 1 ≤ v := hvPos
  have hpqPos : 0 < p * q := Nat.mul_pos hpPrime.pos hqPrime.pos
  have hpqOne : 1 ≤ p * q := hpqPos
  have hpqPosR : (0 : ℝ) < (((p * q : ℕ) : ℝ)) := by
    exact_mod_cast hpqPos
  have hpqOneR : (1 : ℝ) ≤ (p : ℝ) * (q : ℝ) := by
    exact_mod_cast hpqOne
  have hmul := (div_le_iff₀ hpqPosR).mp hcore
  have hvSquareR :
      (v : ℝ) ≤ ((((p * q) ^ 2 : ℕ) : ℝ)) := by
    norm_num only [Nat.cast_sub hvOne, Nat.cast_one, Nat.cast_mul,
      Nat.cast_pow] at hmul ⊢
    nlinarith [hpqOneR]
  have hvSquare : v ≤ (p * q) ^ 2 := by
    exact_mod_cast hvSquareR
  have hgeom : v * (q - 1) = q ^ p - 1 := by
    rw [hv]
    exact nU_mul_sub_one q p hqPrime.one_le
  have hpowEq : q ^ p = v * (q - 1) + 1 := by
    calc
      q ^ p = (q ^ p - 1) + 1 :=
        (Nat.sub_add_cancel (one_le_pow₀ hqPrime.one_le)).symm
      _ = v * (q - 1) + 1 := by rw [hgeom]
  have hpqSqOne : 1 < (p * q) ^ 2 := by
    have hpqOne : 1 < p * q :=
      hpPrime.one_lt.trans_le (Nat.le_mul_of_pos_right p hqPrime.pos)
    exact one_lt_pow₀ hpqOne (by norm_num)
  have hpowLt : q ^ p < p ^ 2 * q ^ 3 := by
    calc
      q ^ p = v * (q - 1) + 1 := hpowEq
      _ ≤ (p * q) ^ 2 * (q - 1) + 1 :=
        Nat.add_le_add_right
          (Nat.mul_le_mul_right (q - 1) hvSquare) 1
      _ < (p * q) ^ 2 * (q - 1) + (p * q) ^ 2 :=
        Nat.add_lt_add_left hpqSqOne _
      _ = (p * q) ^ 2 * q := by
        calc
          (p * q) ^ 2 * (q - 1) + (p * q) ^ 2 =
              (p * q) ^ 2 * ((q - 1) + 1) := by
            rw [Nat.mul_add, Nat.mul_one]
          _ = (p * q) ^ 2 * q := by
            rw [Nat.sub_add_cancel hqPrime.one_le]
      _ = p ^ 2 * q ^ 3 := by ring
  have hpowSplit : q ^ p = q ^ (p - 3) * q ^ 3 := by
    rw [← pow_add]
    congr 1
    omega
  have hsmall : q ^ (p - 3) < p ^ 2 := by
    have hmulSmall : q ^ (p - 3) * q ^ 3 < p ^ 2 * q ^ 3 := by
      rw [← hpowSplit]
      exact hpowLt
    exact (Nat.mul_lt_mul_right (pow_pos hqPrime.pos 3)).mp hmulSmall
  have hqLtFive : q < 5 := by
    by_contra hnot
    have hqFive : 5 ≤ q := Nat.le_of_not_gt hnot
    have hpSixLe : p ^ 6 ≤ p ^ (q + 1) :=
      Nat.pow_le_pow_right hpPrime.pos (by omega)
    have hqFourLt : q ^ 4 < p ^ 4 :=
      pow_lt_pow_left₀ hqp (Nat.zero_le q) (by norm_num)
    have hqUpper : q ^ (p + 1) < p ^ 6 := by
      calc
        q ^ (p + 1) = q ^ (p - 3) * q ^ 4 := by
          rw [show p + 1 = (p - 3) + 4 by omega, pow_add]
        _ < p ^ 2 * q ^ 4 :=
          Nat.mul_lt_mul_of_pos_right hsmall (pow_pos hqPrime.pos 4)
        _ < p ^ 2 * p ^ 4 :=
          Nat.mul_lt_mul_of_pos_left hqFourLt (pow_pos hpPrime.pos 2)
        _ = p ^ 6 := by ring
    exact (not_lt_of_ge hpSixLe) (hPowSwap.trans hqUpper)
  have hqEq : q = 3 := by
    obtain ⟨k, hk⟩ := hqOdd
    omega
  have hthreeLower : ∀ n : ℕ, 7 ≤ n → n ^ 2 ≤ 3 ^ (n - 3) := by
    intro n hn
    induction n, hn using Nat.le_induction with
    | base => norm_num
    | succ n hn ih =>
        calc
          (n + 1) ^ 2 ≤ 3 * n ^ 2 := by nlinarith
          _ ≤ 3 * 3 ^ (n - 3) := Nat.mul_le_mul_left 3 ih
          _ = 3 ^ ((n + 1) - 3) := by
            rw [show (n + 1) - 3 = (n - 3) + 1 by omega, pow_succ]
            ring
  have hpLtSeven : p < 7 := by
    by_contra hnot
    have hpSeven : 7 ≤ p := Nat.le_of_not_gt hnot
    have hlower := hthreeLower p hpSeven
    rw [hqEq] at hsmall
    exact (not_lt_of_ge hlower) hsmall
  have hpEq : p = 5 := by
    obtain ⟨k, hk⟩ := hpOdd
    omega
  exact ⟨hqEq, hpEq⟩

private theorem ftt2_induce_mem_ambientClassSupport
    {K : Subgroup G} {A : Set G}
    (alpha : ClassFunction K ℂ)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : K | (x : G) ∈ A}) :
    ClassFunction.induce K alpha ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G) A) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  rw [ClassFunction.induce_apply_formula]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hy
  · apply ClassFunction.eq_zero_of_mem_supportedOn halpha
    intro ha
    apply hx
    exact ⟨y⁻¹ * x * y, ha, y⁻¹,
      Subgroup.mem_top _, by group⟩
  · rfl

private theorem ftt2_dade1_support_eq_of_within_top
    {M L : Subgroup G}
    (hML : AreConjugateSubgroupsWithin (⊤ : Subgroup G) M L) :
    FT_Dade1_support M = FT_Dade1_support L := by
  induction hML with
  | rel M L h =>
      rcases h with ⟨x, _, rfl⟩
      exact (FT_Dade1_supportJ M x).symm
  | refl M => rfl
  | symm M L _ ih => exact ih.symm
  | trans M L H _ _ hML hLH => exact hML.trans hLH

private theorem ftt2_dade1_support_mem_family
    {M : Subgroup G}
    (maxM : M ∈ minSimple_max_groups (G := G)) :
    FT_Dade1_support M ∈ ftFirstDadeSupportFamily (G := G) := by
  obtain ⟨R, hR, hMR⟩ :=
    (mmax_transversalP (G := G)).representative maxM
  change FT_Dade1_support M ∈
    FT_Dade1_support '' mmax_transversal (⊤ : Subgroup G)
  refine ⟨R, hR, ?_⟩
  exact (ftt2_dade1_support_eq_of_within_top hMR).symm

private theorem ftt2_typeP_exceptional_disjoint_dade1
    {S T W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pairST : typeP_pair S T W W₁ W₂ defW) :
    Disjoint (ftCyclicExceptionalSupport W W₁ W₂)
      (FT_Dade1_support T) := by
  rcases FT_Dade_support_partition (G := G) with
    ⟨_, _, _, _, _, hpairPartition⟩
  have hpack := hpairPartition S T W W₁ W₂ defW pairST
  have hTmem : FT_Dade1_support T ∈
      ftFirstDadeSupportFamily (G := G) :=
    ftt2_dade1_support_mem_family pairST.T_maximal
  apply hpack.1.2.1 (Or.inl rfl) (Or.inr hTmem)
  intro heq
  apply hpack.2
  rw [heq]
  exact hTmem

private theorem ftt2_classSupport_subset_Dade
    (M : Subgroup G) (A : Set G) :
    classSupportWithin (⊤ : Subgroup G) A ⊆
      FT_Dade_support M A := by
  rintro x ⟨a, ha, z, hz, hzx⟩
  refine ⟨a, ha, a, ?_, z, hz, hzx⟩
  exact ⟨1, (FTsignalizer M a).one_mem,
    a, Set.mem_singleton a, by simp⟩

private theorem ftt2_classSupport_nonidentity_invStable
    (H : Subgroup G) :
    IsInvStable
      (classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity H)) := by
  have hinv : ∀ x : G,
      x ∈ classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity H) →
        x⁻¹ ∈ classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity H) := by
    rintro x ⟨a, ⟨haH, haOne⟩, g, hg, rfl⟩
    refine ⟨a⁻¹, ⟨H.inv_mem haH, inv_ne_one.mpr haOne⟩,
      g, hg, ?_⟩
    group
  intro x
  constructor
  · intro hx
    simpa only [inv_inv] using hinv x⁻¹ hx
  · exact hinv x

private theorem ftt2_supportedOn_mono
    {Q : Type*} [Group Q] [Fintype Q]
    {A B : Set Q} {f : ClassFunction Q ℂ}
    (hAB : A ⊆ B)
    (hf : f ∈ ClassFunction.supportedOn A) :
    f ∈ ClassFunction.supportedOn B := by
  rw [ClassFunction.mem_supportedOn_iff] at hf ⊢
  intro x hxB
  exact hf x (fun hxA ↦ hxB (hAB hxA))

private theorem ftt2_no_direct_L
    {S U W W₁ W₂ L : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (hlt : Nat.card W₁ < Nat.card W₂)
    (Stype2 : FTtype S = 2)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (sNUL : Subgroup.normalizer (U : Set G) ≤ L)
    (sUH : U ≤ Fitting_core L)
    (Ltype1 : FTtype L = 1)
    (tau₁L : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (phi : ClassFunction L ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁L)
    (Lphi : phi ∈ FTType1SeqIndFamily L)
    (phi1 : phi 1 = (FTtype1CoreIndex L : ℂ))
    (hsdL : IsInternalSemidirectProductIn
      (Fitting_core L) W₁ L) :
    False := by
  have factsI :=
    FTtypeI_bridge_facts ctxS L maxL Ltype1 tau₁L phi cohL Lphi phi1
  have factsP := FTtypeP_bridge_facts ctxS
  have hindex : FTtype1CoreIndex L = Nat.card W₁ := by
    change ((Fitting_core L).subgroupOf L).index = Nat.card W₁
    exact hsdL.2.2.2.symm.index_eq_card.trans
      (MathlibSupport.natCard_subgroupOf_eq hsdL.2.1)
  rcases factsI.2.2.2 with hratio | hlarge
  · have hdiv : Nat.card W₁ ∣ Nat.card U - 1 :=
      factsP.2.2.2.2
    have hratio' := hratio.2
    rw [hindex, Nat.cast_div_charZero hdiv] at hratio'
    have hqpos : (0 : ℝ) < Nat.card W₁ := by
      exact_mod_cast (Nat.card_pos : 0 < Nat.card W₁)
    have hpredReal :
        (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ)) ≤
          (((Nat.card U - 1 : ℕ) : ℝ)) :=
      (div_le_div_iff_of_pos_right hqpos).mp hratio'
    have hpred : Nat.card (Fitting_core L) - 1 ≤
        Nat.card U - 1 := by
      exact_mod_cast hpredReal
    have hcard : Nat.card (Fitting_core L) ≤ Nat.card U := by
      have hFpos : 0 < Nat.card (Fitting_core L) := Nat.card_pos
      have hUpos : 0 < Nat.card U := Nat.card_pos
      omega
    have hUF : U = Fitting_core L :=
      Subgroup.eq_of_le_of_card_ge sUH hcard
    have hLS : L ≤ S := by
      rw [← FTContextInternal.semidirect_sup_eq8 hsdL, ← hUF]
      exact sup_le
        (ctxS.StypeP.2.1.2.1.trans ctxS.StypeP.1.2.2.2.1)
        ctxS.StypeP.1.2.1.1
    exact (compl_of_typeII S U W W₁ W₂ defW
      ctxS.maxS ctxS.StypeP Stype2).2.2.1 (sNUL.trans hLS)
  · rw [hindex] at hlarge
    omega

private theorem ftt2_forced_join_L
    {S T U W W₁ W₂ L : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (hlt : Nat.card W₁ < Nat.card W₂)
    (Stype2 : FTtype S = 2)
    (maxNU_L : L ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (U : Set G) : Set G))
    (maxL : L ∈ minSimple_max_groups (G := G))
    (sNUL : Subgroup.normalizer (U : Set G) ≤ L)
    (sUH : U ≤ Fitting_core L)
    (Ltype1 : FTtype L = 1)
    (tau₁L : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (phi : ClassFunction L ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁L)
    (Lphi : phi ∈ FTType1SeqIndFamily L)
    (phi1 : phi 1 = (FTtype1CoreIndex L : ℂ)) :
    ∃ y : G, y ∈ Fitting_core T ∧
      IsInternalSemidirectProductIn (Fitting_core L)
        (W₁ ⊔ conjugateSubgroup8 W₂ y) L := by
  obtain ⟨_frobL, _sUH, hcases⟩ :=
    FTtypeII_support_facts ctxS T L Stype2 pairST maxNU_L
  rcases hcases with hsdL | hjoin
  · exact False.elim (ftt2_no_direct_L ctxS hlt Stype2
      maxL sNUL sUH Ltype1 tau₁L phi cohL Lphi phi1 hsdL)
  · exact hjoin

private theorem ftt2_index_of_join_L
    {S T U V W W₁ W₂ L : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (pairST : typeP_pair S T W W₁ W₂ defW)
    {y : G} (hyQ : y ∈ Fitting_core T)
    (defLy : IsInternalSemidirectProductIn (Fitting_core L)
      (W₁ ⊔ conjugateSubgroup8 W₂ y) L) :
    FTtype1CoreIndex L = Nat.card W₂ * Nat.card W₁ := by
  obtain ⟨hq, hp⟩ :=
    FTtypeP_pair_primes S T W W₁ W₂ defW pairST
  have hqp : Nat.card W₁ ≠ Nat.card W₂ :=
    pairST.cyclic_ti.factor_card_ne
  let Q : Subgroup G := Fitting_core T
  let W₂y : Subgroup G := conjugateSubgroup8 W₂ y
  letI : IsMulCommutative Q :=
    (FTtypeP_facts ctxT).2.2.2.2.1.commutative
  have hW₁Q : W₁ ≤ Q := ctxT.StypeP.2.2.2.1.2.2.1
  have hcardW₂y : Nat.card W₂y = Nat.card W₂ := by
    dsimp only [W₂y, conjugateSubgroup8]
    rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
  have hW₁cent : W₁ ≤ Subgroup.centralizer (W₂y : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rcases hz with ⟨z₀, hz₀, rfl⟩
    have hyw : Commute y w := by
      exact congrArg Subtype.val
        (mul_comm' (⟨y, by simpa only [Q] using hyQ⟩ : Q)
          (⟨w, hW₁Q hw⟩ : Q))
    have hwz : Commute w z₀ :=
      defW.commute ⟨w, hw⟩ ⟨z₀, hz₀⟩
    have hwConj : Commute w (y * z₀ * y⁻¹) :=
      (hyw.symm.mul_right hwz).mul_right hyw.symm.inv_right
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      hwConj.symm.eq
  have hW₁norm : W₁ ≤ Subgroup.normalizer (W₂y : Set G) :=
    hW₁cent.trans (Subgroup.centralizer_le_normalizer (W₂y : Set G))
  have hcop : Nat.Coprime (Nat.card W₁) (Nat.card W₂y) := by
    rw [hcardW₂y]
    exact (Nat.coprime_primes hq hp).mpr hqp
  have hdis : Disjoint W₁ W₂y :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hjoin : Nat.card (W₁ ⊔ W₂y : Subgroup G) =
      Nat.card W₁ * Nat.card W₂ := by
    rw [natCard_sup_eq_mul_of_disjoint_of_le_normalizer hdis hW₁norm,
      hcardW₂y]
  have hindexJoin : FTtype1CoreIndex L =
      Nat.card (W₁ ⊔ W₂y : Subgroup G) := by
    change ((Fitting_core L).subgroupOf L).index =
      Nat.card (W₁ ⊔ W₂y : Subgroup G)
    exact defLy.2.2.2.symm.index_eq_card.trans
      (MathlibSupport.natCard_subgroupOf_eq defLy.2.1)
  rw [hindexJoin, hjoin, Nat.mul_comm]

private theorem ftt2_ambientConjugate_symm
    {M L : Subgroup G} :
    FTAmbientConjugate M L → FTAmbientConjugate L M := by
  rintro ⟨x, rfl⟩
  refine ⟨x⁻¹, ?_⟩
  rw [Subgroup.map_map]
  ext y
  simp [MulAut.conj_apply, mul_assoc]

/-! The arithmetic comparison used by the minimum-type argument. -/

private theorem ftt2_one_add_two_div_pow_lt_sq
    {q n : ℕ} (hqPrime : q.Prime) (hqOdd : Odd q)
    (hqn : q ≤ n) :
    (1 + (2 : ℝ) / n) ^ (q + 1) < (q : ℝ) ^ 2 := by
  have hqThree : 3 ≤ q := hqPrime.odd_iff.mp hqOdd
  have hqPosR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
  have hnPos : 0 < n := by omega
  have hnPosR : (0 : ℝ) < n := by exact_mod_cast hnPos
  by_cases hqEq : q = 3
  · subst q
    have hnThree : 3 ≤ n := by omega
    have hnThreeR : (3 : ℝ) ≤ n := by exact_mod_cast hnThree
    have hfrac : (2 : ℝ) / n ≤ 2 / 3 := by
      apply (div_le_iff₀ hnPosR).2
      nlinarith
    have hbase : (1 : ℝ) + 2 / n ≤ 5 / 3 := by
      norm_num
      linarith
    calc
      (1 + (2 : ℝ) / n) ^ (3 + 1) ≤ (5 / 3 : ℝ) ^ 4 :=
        pow_le_pow_left₀ (by positivity) hbase 4
      _ < (3 : ℝ) ^ 2 := by norm_num
  · have hqFive : 5 ≤ q := by
      rcases hqOdd with ⟨k, hk⟩
      omega
    have hqFiveR : (5 : ℝ) ≤ q := by exact_mod_cast hqFive
    have hqLeN : q ≤ n := by omega
    have hqLeNR : (q : ℝ) ≤ n := by exact_mod_cast hqLeN
    have hinvNQ : (n : ℝ)⁻¹ ≤ (q : ℝ)⁻¹ :=
      (inv_le_inv₀ hnPosR hqPosR).2 hqLeNR
    have hfracNQ : (2 : ℝ) / n ≤ 2 / q := by
      simpa only [div_eq_mul_inv] using
        mul_le_mul_of_nonneg_left hinvNQ (by norm_num : (0 : ℝ) ≤ 2)
    let a : ℝ := 1 + (q : ℝ)⁻¹
    have haNonneg : 0 ≤ a := by positivity
    have hbaseSq : (1 : ℝ) + 2 / q ≤ a * a := by
      dsimp only [a]
      rw [div_eq_mul_inv]
      nlinarith [sq_nonneg ((q : ℝ)⁻¹)]
    have haPow : a ^ q ≤ Real.exp 1 := by
      simpa only [a] using (Real.one_add_inv_pow_le_exp (n := q))
    have hinvQFive : (q : ℝ)⁻¹ ≤ (5 : ℝ)⁻¹ :=
      (inv_le_inv₀ hqPosR (by norm_num : (0 : ℝ) < 5)).2 hqFiveR
    have haSixFifths : a ≤ (6 : ℝ) / 5 := by
      dsimp only [a]
      norm_num at hinvQFive ⊢
      linarith
    have haSucc : a ^ (q + 1) ≤ Real.exp 1 * ((6 : ℝ) / 5) := by
      rw [pow_succ]
      calc
        a ^ q * a ≤ Real.exp 1 * a :=
          mul_le_mul_of_nonneg_right haPow haNonneg
        _ ≤ Real.exp 1 * ((6 : ℝ) / 5) :=
          mul_le_mul_of_nonneg_left haSixFifths (Real.exp_pos 1).le
    have hExpBound :
        Real.exp 1 * ((6 : ℝ) / 5) < (18 : ℝ) / 5 := by
      calc
        _ < 3 * ((6 : ℝ) / 5) :=
          mul_lt_mul_of_pos_right Real.exp_one_lt_three (by norm_num)
        _ = _ := by norm_num
    have hmainQ :
        ((1 : ℝ) + 2 / q) ^ (q + 1) < (q : ℝ) ^ 2 := by
      calc
        ((1 : ℝ) + 2 / q) ^ (q + 1) ≤ (a * a) ^ (q + 1) :=
          pow_le_pow_left₀ (by positivity) hbaseSq (q + 1)
        _ = (a ^ (q + 1)) ^ 2 := by rw [mul_pow, pow_two]
        _ ≤ (Real.exp 1 * ((6 : ℝ) / 5)) ^ 2 :=
          pow_le_pow_left₀ (by positivity) haSucc 2
        _ < (((18 : ℝ) / 5)) ^ 2 := by
          exact pow_lt_pow_left₀ hExpBound (by positivity) two_ne_zero
        _ < (q : ℝ) ^ 2 := by
          apply pow_lt_pow_left₀ _ (by positivity) two_ne_zero
          nlinarith
    have hbaseNQ : (1 : ℝ) + 2 / n ≤ 1 + 2 / q := by
      linarith
    exact lt_of_le_of_lt
      (pow_le_pow_left₀ (by positivity) hbaseNQ (q + 1)) hmainQ

private theorem ftt2_swapped_prime_power_lt
    {p q : ℕ} (hpPrime : p.Prime) (hqPrime : q.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hqp : q < p) :
    p ^ (q + 1) < q ^ (p + 1) := by
  have hqThree : 3 ≤ q := hqPrime.odd_iff.mp hqOdd
  have hpForm : ∃ k : ℕ, p = q + 2 + 2 * k := by
    rcases hpOdd with ⟨a, ha⟩
    rcases hqOdd with ⟨b, hb⟩
    refine ⟨a - b - 1, ?_⟩
    omega
  obtain ⟨k, hpEq⟩ := hpForm
  have hfamily : ∀ k : ℕ,
      (q + 2 + 2 * k) ^ (q + 1) <
        q ^ ((q + 2 + 2 * k) + 1) := by
    intro k
    induction k with
    | zero =>
        have hbaseReal := ftt2_one_add_two_div_pow_lt_sq
          hqPrime hqOdd (n := q) (by omega)
        have hqPosR : (0 : ℝ) < q := by exact_mod_cast hqPrime.pos
        have hfactor : (q : ℝ) + 2 =
            (q : ℝ) * (1 + (2 : ℝ) / q) := by
          field_simp [hqPosR.ne']
        have hbaseNat :
            (q + 2) ^ (q + 1) < q ^ 2 * q ^ (q + 1) := by
          have hreal :
              ((((q + 2) ^ (q + 1) : ℕ) : ℝ)) <
                (((q ^ 2 * q ^ (q + 1) : ℕ) : ℝ)) := by
            norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
              Nat.cast_ofNat]
            rw [hfactor, mul_pow]
            simpa only [mul_comm] using
              mul_lt_mul_of_pos_left hbaseReal (pow_pos hqPosR (q + 1))
          exact_mod_cast hreal
        simpa only [Nat.mul_zero, Nat.add_zero] using
          (calc
            (q + 2) ^ (q + 1) < q ^ 2 * q ^ (q + 1) := hbaseNat
            _ = q ^ ((q + 2) + 1) := by
              rw [← pow_add]
              congr 1
              omega)
    | succ k ih =>
        let n : ℕ := q + 2 + 2 * k
        have hqn : q + 2 ≤ n := by dsimp only [n]; omega
        have hratioReal := ftt2_one_add_two_div_pow_lt_sq
          hqPrime hqOdd (n := n) (by omega)
        have hnPos : 0 < n := by omega
        have hnPosR : (0 : ℝ) < n := by exact_mod_cast hnPos
        have hfactor : (n : ℝ) + 2 =
            (n : ℝ) * (1 + (2 : ℝ) / n) := by
          field_simp [hnPosR.ne']
        have hstep :
            (n + 2) ^ (q + 1) < q ^ 2 * n ^ (q + 1) := by
          have hreal :
              ((((n + 2) ^ (q + 1) : ℕ) : ℝ)) <
                (((q ^ 2 * n ^ (q + 1) : ℕ) : ℝ)) := by
            norm_num only [Nat.cast_pow, Nat.cast_add, Nat.cast_mul,
              Nat.cast_ofNat]
            rw [hfactor, mul_pow]
            simpa only [mul_comm] using
              mul_lt_mul_of_pos_left hratioReal (pow_pos hnPosR (q + 1))
          exact_mod_cast hreal
        have ih' : n ^ (q + 1) < q ^ (n + 1) := by
          simpa only [n] using ih
        have hscaled : q ^ 2 * n ^ (q + 1) <
            q ^ 2 * q ^ (n + 1) :=
          (Nat.mul_lt_mul_left (pow_pos hqPrime.pos 2)).2 ih'
        have hnext :
            (n + 2) ^ (q + 1) < q ^ ((n + 2) + 1) := by
          calc
            (n + 2) ^ (q + 1) < q ^ 2 * n ^ (q + 1) := hstep
            _ < q ^ 2 * q ^ (n + 1) := hscaled
            _ = q ^ ((n + 2) + 1) := by
              rw [← pow_add]
              congr 1
              omega
        have hnnext : q + 2 + 2 * (k + 1) = n + 2 := by
          dsimp only [n]
          omega
        simpa only [hnnext] using hnext
  simpa only [hpEq] using hfamily k

private theorem ftt2_geometric_pred_cross_lt
    {p q : ℕ} (hpPrime : p.Prime) (hqPrime : q.Prime)
    (hpOdd : Odd p) (hqOdd : Odd q) (hqp : q < p) :
    (nU p q - 1) * p < (nU q p - 1) * q := by
  have hpow : p ^ (q + 1) < q ^ (p + 1) :=
    ftt2_swapped_prime_power_lt hpPrime hqPrime hpOdd hqOdd hqp
  have hnUPPos : 0 < nU p q := by
    rw [← Nat.succ_pred_eq_of_pos hqPrime.pos, nU_succ]
    exact Nat.add_pos_right _ (pow_pos hpPrime.pos _)
  have hnUQPos : 0 < nU q p := by
    rw [← Nat.succ_pred_eq_of_pos hpPrime.pos, nU_succ]
    exact Nat.add_pos_right _ (pow_pos hqPrime.pos _)
  have hnUPOne : 1 ≤ nU p q := hnUPPos
  have hnUQOne : 1 ≤ nU q p := hnUQPos
  have hgeomPNat := nU_mul_sub_one p q hpPrime.one_le
  have hgeomQNat := nU_mul_sub_one q p hqPrime.one_le
  have hgeomP :
      (nU p q : ℝ) * ((p : ℝ) - 1) = (p : ℝ) ^ q - 1 := by
    have hcast := congrArg (fun z : ℕ ↦ (z : ℝ)) hgeomPNat
    norm_num only [Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub hpPrime.one_le,
      Nat.cast_sub (one_le_pow₀ hpPrime.one_le), Nat.cast_one] at hcast
    exact hcast
  have hgeomQ :
      (nU q p : ℝ) * ((q : ℝ) - 1) = (q : ℝ) ^ p - 1 := by
    have hcast := congrArg (fun z : ℕ ↦ (z : ℝ)) hgeomQNat
    norm_num only [Nat.cast_mul, Nat.cast_pow,
      Nat.cast_sub hqPrime.one_le,
      Nat.cast_sub (one_le_pow₀ hqPrime.one_le), Nat.cast_one] at hcast
    exact hcast
  have hleftIdentity :
      ((nU p q : ℝ) - 1) * (p : ℝ) * ((p : ℝ) - 1) =
        (p : ℝ) ^ (q + 1) - (p : ℝ) ^ 2 := by
    calc
      ((nU p q : ℝ) - 1) * p * (p - 1) =
          p * ((nU p q : ℝ) * (p - 1) - (p - 1)) := by ring
      _ = p * (((p : ℝ) ^ q - 1) - (p - 1)) := by rw [hgeomP]
      _ = (p : ℝ) ^ (q + 1) - p ^ 2 := by rw [pow_succ]; ring
  have hrightIdentity :
      ((nU q p : ℝ) - 1) * (q : ℝ) * ((q : ℝ) - 1) =
        (q : ℝ) ^ (p + 1) - (q : ℝ) ^ 2 := by
    calc
      ((nU q p : ℝ) - 1) * q * (q - 1) =
          q * ((nU q p : ℝ) * (q - 1) - (q - 1)) := by ring
      _ = q * (((q : ℝ) ^ p - 1) - (q - 1)) := by rw [hgeomQ]
      _ = (q : ℝ) ^ (p + 1) - q ^ 2 := by rw [pow_succ]; ring
  have hpowR : (p : ℝ) ^ (q + 1) < (q : ℝ) ^ (p + 1) := by
    exact_mod_cast hpow
  have hpqR : (q : ℝ) < p := by exact_mod_cast hqp
  have hsqR : (q : ℝ) ^ 2 < (p : ℝ) ^ 2 :=
    pow_lt_pow_left₀ hpqR (by positivity) two_ne_zero
  have hdiff :
      (p : ℝ) ^ (q + 1) - p ^ 2 <
        (q : ℝ) ^ (p + 1) - q ^ 2 := by
    linarith
  let XP : ℝ := ((nU p q : ℝ) - 1) * p
  let XQ : ℝ := ((nU q p : ℝ) - 1) * q
  have hpredLe : (q : ℝ) - 1 ≤ (p : ℝ) - 1 := by linarith
  have hXPNonneg : 0 ≤ XP := by
    dsimp only [XP]
    have hnUPOneR : (1 : ℝ) ≤ nU p q := by exact_mod_cast hnUPOne
    exact mul_nonneg (sub_nonneg.mpr hnUPOneR) (Nat.cast_nonneg p)
  have hqPredPos : (0 : ℝ) < (q : ℝ) - 1 := by
    have hqOneR : (1 : ℝ) < q := by exact_mod_cast hqPrime.one_lt
    linarith
  have hmul : XP * ((q : ℝ) - 1) < XQ * ((q : ℝ) - 1) := by
    calc
      XP * ((q : ℝ) - 1) ≤ XP * ((p : ℝ) - 1) :=
        mul_le_mul_of_nonneg_left hpredLe hXPNonneg
      _ = (p : ℝ) ^ (q + 1) - p ^ 2 := hleftIdentity
      _ < (q : ℝ) ^ (p + 1) - q ^ 2 := hdiff
      _ = XQ * ((q : ℝ) - 1) := hrightIdentity.symm
  have hcrossR : XP < XQ :=
    lt_of_mul_lt_mul_right hmul hqPredPos.le
  have hcastP :
      ((((nU p q - 1) * p : ℕ) : ℝ)) = XP := by
    dsimp only [XP]
    rw [Nat.cast_mul, Nat.cast_sub hnUPOne]
    norm_num
  have hcastQ :
      ((((nU q p - 1) * q : ℕ) : ℝ)) = XQ := by
    dsimp only [XQ]
    rw [Nat.cast_mul, Nat.cast_sub hnUQOne]
    norm_num
  exact_mod_cast (show
    ((((nU p q - 1) * p : ℕ) : ℝ)) <
      (((nU q p - 1) * q : ℕ) : ℝ) by
        simpa only [hcastP, hcastQ] using hcrossR)

private theorem ftt2_forward_gap
    {S T U V W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (hlt : Nat.card W₁ < Nat.card W₂) :
    (Nat.card U - 1) / Nat.card W₁ <
      (Nat.card V - 1) / Nat.card W₂ := by
  let p : ℕ := Nat.card W₂
  let q : ℕ := Nat.card W₁
  have hqp : q < p := by simpa only [p, q] using hlt
  obtain ⟨hqPrime, hpPrime⟩ :=
    FTtypeP_primes S U W W₁ W₂ defW ctxS.maxS ctxS.StypeP
  have hqOdd : Odd q := by simpa only [q] using mFT_odd W₁
  have hpOdd : Odd p := by simpa only [p] using mFT_odd W₂
  obtain ⟨_, _, _, _, _, _, hIndexBoundS, _, _, _⟩ :=
    FTtypeP_facts ctxS
  have hUle : Nat.card U ≤ nU p q := by
    calc
      Nat.card U = ctxS.u := (ftt2_u_eq_card ctxS).symm
      _ ≤ (ctxS.p ^ ctxS.q - 1) / (ctxS.p - 1) := hIndexBoundS
      _ = nU p q := by
        change (p ^ q - 1) / (p - 1) = nU p q
        exact (nU_eq_div_of_prime hpPrime).symm
  have hGalT : ctxT.galoisAlternative := by
    by_contra hnotGalT
    obtain ⟨hRankThreeT, _⟩ := FTtypeP_nonGalois_facts ctxT hnotGalT
    have hpThree : p = 3 := by simpa only [p] using hRankThreeT
    have hqThree : 3 ≤ q := hqPrime.odd_iff.mp hqOdd
    omega
  have hNotMod : ¬ Nat.ModEq p q 1 := by
    intro hmod
    have hpDvdQPred : p ∣ q - 1 :=
      (Nat.modEq_iff_dvd' hqPrime.one_le).mp hmod.symm
    have hqPredPos : 0 < q - 1 := Nat.sub_pos_of_lt hqPrime.one_lt
    have hpLeQPred : p ≤ q - 1 := Nat.le_of_dvd hqPredPos hpDvdQPred
    omega
  have hNotModT : ¬ Nat.ModEq ctxT.q ctxT.p 1 := by
    simpa only [p, q] using hNotMod
  have hVFormula := card_FTtypeP_Galois_compl ctxT hGalT
  rw [if_neg hNotModT] at hVFormula
  have hVcard : Nat.card V = nU q p := by
    calc
      Nat.card V = ctxT.ustar := hVFormula
      _ = (q ^ p - 1) / (q - 1) := rfl
      _ = nU q p := (nU_eq_div_of_prime hqPrime).symm
  obtain ⟨_, _, _, _, hBridgeDvdT⟩ := FTtypeP_bridge_facts ctxT
  have hpDvdVPred : p ∣ Nat.card V - 1 := by
    simpa only [p] using hBridgeDvdT
  have hpDvdGeomPred : p ∣ nU q p - 1 := by
    simpa only [hVcard] using hpDvdVPred
  have hcross : (nU p q - 1) * p < (nU q p - 1) * q :=
    ftt2_geometric_pred_cross_lt hpPrime hqPrime hpOdd hqOdd hqp
  have hnum : nU p q - 1 < ((nU q p - 1) / p) * q := by
    apply Nat.lt_of_mul_lt_mul_right (a := p)
    calc
      (nU p q - 1) * p < (nU q p - 1) * q := hcross
      _ = (((nU q p - 1) / p) * q) * p := by
        calc
          (nU q p - 1) * q =
              ((nU q p - 1) / p * p) * q := by
            rw [Nat.div_mul_cancel hpDvdGeomPred]
          _ = (((nU q p - 1) / p) * q) * p := by ac_rfl
  have hGeomRatio :
      (nU p q - 1) / q < (nU q p - 1) / p :=
    (Nat.div_lt_iff_lt_mul hqPrime.pos).2 hnum
  have hUSub : Nat.card U - 1 ≤ nU p q - 1 :=
    Nat.sub_le_sub_right hUle 1
  calc
    (Nat.card U - 1) / Nat.card W₁ = (Nat.card U - 1) / q := by rfl
    _ ≤ (nU p q - 1) / q := Nat.div_le_div_right hUSub
    _ < (nU q p - 1) / p := hGeomRatio
    _ = (Nat.card V - 1) / Nat.card W₂ := by rw [hVcard]

private theorem ftt2_support_of_core_ne
    {S T U V W W₁ W₂ M : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (hlt : Nat.card W₁ < Nat.card W₂)
    (Ttype2 : FTtype T = 2)
    (hUV : (Nat.card U - 1) / Nat.card W₁ <
      (Nat.card V - 1) / Nat.card W₂)
    (maxNV_M : M ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (V : Set G) : Set G))
    (maxM : M ∈ minSimple_max_groups (G := G))
    (sNVM : Subgroup.normalizer (V : Set G) ≤ M)
    (frobM : FTFrobeniusWithFittingKernel M)
    (tau₁M : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (psi : ClassFunction M ℂ)
    (cohM : coherent_with
      (↑(FTType1SeqIndFamily M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (FTtype1Dade M maxM) tau₁M)
    (Mpsi : psi ∈ FTType1SeqIndFamily M)
    (psi1 : psi 1 = (FTtype1CoreIndex M : ℂ))
    (hCoreNe : Fitting_core M ≠ V) :
    2 * Nat.card W₂ * Nat.card V < Nat.card (Fitting_core M) ∧
      FTtype1CoreIndex M = Nat.card W₁ * Nat.card W₂ ∧
      ∃ eps : IrreducibleCharacter W₂ ℂ →
          IrreducibleCharacter W₁ ℂ → Bool,
        ∃ chi : ClassFunction G ℂ,
          (chi = tau₁M psi ∨
            chi = -tau₁M (ClassFunction.inverseLinear psi)) ∧
          FTtype1Dade M maxM (FTtype1Bridge M psi) =
            (∑ i, ∑ j,
              if eps i j then -(ctxT.eta i j) else ctxT.eta i j) - chi := by
  classical
  let pairTS : typeP_pair T S W W₂ W₁ xdefW :=
    typeP_pair_sym S T W W₁ W₂ defW xdefW pairST
  obtain ⟨_frobSupportM, hVcore, hCompM⟩ :=
    FTtypeII_support_facts ctxT S M Ttype2 pairTS maxNV_M
  obtain ⟨E, hFrobME⟩ := frobM
  have hVltCore : V < Fitting_core M :=
    lt_of_le_of_ne hVcore hCoreNe.symm
  have hVcardLt : Nat.card V < Nat.card (Fitting_core M) :=
    natCard_subgroup_lt_of_lt hVltCore
  have hIndexLe :
      FTtype1CoreIndex M ≤ Nat.card W₁ * Nat.card W₂ := by
    rcases hCompM with hsd | ⟨y, hyS, hsd⟩
    · have he : FTtype1CoreIndex M = Nat.card W₂ := by
        change ((Fitting_core M).subgroupOf M).index = Nat.card W₂
        exact hsd.2.2.2.symm.index_eq_card.trans
          (MathlibSupport.natCard_subgroupOf_eq hsd.2.1)
      rw [he]
      exact Nat.le_mul_of_pos_left (Nat.card W₂)
        (Nat.card_pos ( α := W₁))
    · exact (ftt2_index_of_join_L ctxT ctxS pairTS hyS hsd).le
  have hIndexLe' :
      FTtype1CoreIndex M ≤ Nat.card W₂ * Nat.card W₁ := by
    simpa only [Nat.mul_comm] using hIndexLe
  have hIndexDvdCorePred :
      FTtype1CoreIndex M ∣ Nat.card (Fitting_core M) - 1 := by
    simpa only [FTtype1CoreIndex, FTType1FittingIn] using
      ftt2_frobenius_index_dvd_kernel_sub_one hFrobME
  have hCoreW₂regular :
      IsSemiregularConjugation (Fitting_core M) W₂ := by
    rcases hCompM with hsd | ⟨y, hyS, hsd⟩
    · exact ftt2_semiregular_of_semidirect_complement
        hFrobME hsd le_rfl
    · exact ftt2_semiregular_of_semidirect_complement
        hFrobME hsd le_sup_left
  have hW₂M : W₂ ≤ M :=
    ctxT.StypeP.2.1.2.2.1.trans sNVM
  have hW₂normCore :
      W₂ ≤ Subgroup.normalizer (Fitting_core M : Set G) :=
    hW₂M.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  have hW₂DvdCorePred :
      Nat.card W₂ ∣ Nat.card (Fitting_core M) - 1 :=
    ftt2_semiregular_card_dvd_sub_one
      hCoreW₂regular hW₂normCore
  obtain ⟨_, _, _, _, hW₂DvdVPred⟩ :=
    FTtypeP_bridge_facts ctxT
  obtain ⟨x, hCoreCard⟩ :
      ∃ x, Nat.card (Fitting_core M) = Nat.card V * x :=
    Subgroup.card_dvd_of_le hVcore
  have hxOne : 1 < x := by
    have hmul : Nat.card V * 1 < Nat.card V * x := by
      calc
        Nat.card V * 1 = Nat.card V := Nat.mul_one _
        _ < Nat.card (Fitting_core M) := hVcardLt
        _ = Nat.card V * x := hCoreCard
    exact lt_of_mul_lt_mul_left hmul (Nat.zero_le (Nat.card V))
  have hxPos : 0 < x := hxOne.trans' Nat.zero_lt_one
  have hVmod : Nat.ModEq (Nat.card W₂) 1 (Nat.card V) :=
    (Nat.modEq_iff_dvd'
      (Nat.card_pos (α := V))).mpr hW₂DvdVPred
  have hCoreMod : Nat.ModEq (Nat.card W₂) 1
      (Nat.card (Fitting_core M)) :=
    (Nat.modEq_iff_dvd'
      (Nat.card_pos (α := Fitting_core M))).mpr
        hW₂DvdCorePred
  have hxCoreMod : Nat.ModEq (Nat.card W₂) x
      (Nat.card (Fitting_core M)) := by
    simpa only [one_mul, hCoreCard] using hVmod.mul_right x
  have hxMod : Nat.ModEq (Nat.card W₂) 1 x :=
    hCoreMod.trans hxCoreMod.symm
  have hW₂DvdXPred : Nat.card W₂ ∣ x - 1 :=
    (Nat.modEq_iff_dvd' hxPos).mp hxMod
  have hxOdd : Odd x := by
    have hoddMul : Odd (Nat.card V * x) := by
      rw [← hCoreCard]
      exact mFT_odd (Fitting_core M)
    exact (Nat.odd_mul.mp hoddMul).2
  have hTwoDvdXPred : 2 ∣ x - 1 :=
    even_iff_two_dvd.mp (Nat.Odd.sub_odd hxOdd odd_one)
  have hTwoW₂DvdXPred : 2 * Nat.card W₂ ∣ x - 1 :=
    (Nat.coprime_two_left.mpr (mFT_odd W₂)).mul_dvd_of_dvd_of_dvd
      hTwoDvdXPred hW₂DvdXPred
  have hTwoW₂LeXPred : 2 * Nat.card W₂ ≤ x - 1 :=
    Nat.le_of_dvd (Nat.sub_pos_of_lt hxOne) hTwoW₂DvdXPred
  have hTwoW₂LtX : 2 * Nat.card W₂ < x := by omega
  have hCoreLower :
      2 * Nat.card W₂ * Nat.card V <
        Nat.card (Fitting_core M) := by
    calc
      2 * Nat.card W₂ * Nat.card V < x * Nat.card V :=
        (Nat.mul_lt_mul_right (Nat.card_pos ( α := V))).2 hTwoW₂LtX
      _ = Nat.card V * x := Nat.mul_comm _ _
      _ = Nat.card (Fitting_core M) := hCoreCard.symm
  have hRatioPred :
      (Nat.card V - 1) * Nat.card W₁ <
        Nat.card (Fitting_core M) - 1 := by
    have hVPredLt : Nat.card V - 1 < Nat.card V :=
      Nat.sub_lt (Nat.card_pos (α := V)) zero_lt_one
    have hW₁LtTwoW₂ : Nat.card W₁ < 2 * Nat.card W₂ := by
      omega
    have hsmall :
        (Nat.card V - 1) * Nat.card W₁ <
          2 * Nat.card W₂ * Nat.card V := by
      calc
        (Nat.card V - 1) * Nat.card W₁ <
            Nat.card V * Nat.card W₁ :=
          (Nat.mul_lt_mul_right (Nat.card_pos ( α := W₁))).2 hVPredLt
        _ < Nat.card V * (2 * Nat.card W₂) :=
          (Nat.mul_lt_mul_left (Nat.card_pos ( α := V))).2
            hW₁LtTwoW₂
        _ = 2 * Nat.card W₂ * Nat.card V := by ac_rfl
    have hLowerPred :
        2 * Nat.card W₂ * Nat.card V ≤
          Nat.card (Fitting_core M) - 1 := by
      omega
    exact hsmall.trans_le hLowerPred
  have hVGap :
      (Nat.card V - 1) / Nat.card W₂ <
        (Nat.card (Fitting_core M) - 1) / FTtype1CoreIndex M := by
    by_contra hnot
    have hquotLe :
        (Nat.card (Fitting_core M) - 1) / FTtype1CoreIndex M ≤
          (Nat.card V - 1) / Nat.card W₂ :=
      Nat.le_of_not_gt hnot
    have hbad :
        Nat.card (Fitting_core M) - 1 ≤
          (Nat.card V - 1) * Nat.card W₁ := by
      calc
        Nat.card (Fitting_core M) - 1 =
            ((Nat.card (Fitting_core M) - 1) /
              FTtype1CoreIndex M) * FTtype1CoreIndex M :=
          (Nat.div_mul_cancel hIndexDvdCorePred).symm
        _ ≤ ((Nat.card V - 1) / Nat.card W₂) *
              FTtype1CoreIndex M :=
          Nat.mul_le_mul_right (FTtype1CoreIndex M) hquotLe
        _ ≤ ((Nat.card V - 1) / Nat.card W₂) *
              (Nat.card W₂ * Nat.card W₁) :=
          Nat.mul_le_mul_left
            ((Nat.card V - 1) / Nat.card W₂) hIndexLe'
        _ = (((Nat.card V - 1) / Nat.card W₂) * Nat.card W₂) *
              Nat.card W₁ := by ac_rfl
        _ = (Nat.card V - 1) * Nat.card W₁ := by
          rw [Nat.div_mul_cancel hW₂DvdVPred]
    exact (not_le_of_gt hRatioPred) hbad
  have hUGap :
      (Nat.card U - 1) / Nat.card W₁ <
        (Nat.card (Fitting_core M) - 1) / FTtype1CoreIndex M :=
    hUV.trans hVGap
  exact ⟨hCoreLower, FTtype2_support_coherence ctxT ctxS pairTS Ttype2
    maxNV_M tau₁M psi cohM Mpsi psi1 hVGap hUGap⟩

private theorem ftt2_card_U_eq_nU_of_LM
    {S U W W₁ W₂ L : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (hGalS : ctxS.galoisAlternative)
    (hlt : Nat.card W₁ < Nat.card W₂)
    (sUH : U ≤ Fitting_core L)
    (frobL : FTFrobeniusWithFittingKernel L)
    {y : G}
    (defLy : IsInternalSemidirectProductIn (Fitting_core L)
      (W₁ ⊔ conjugateSubgroup8 W₂ y) L)
    (hLM :
      (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
          ((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ) ≤
        ((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ) - 1) ∨
      (Nat.card W₁ = 3 ∧ Nat.card W₂ = 5)) :
    Nat.card U = nU (Nat.card W₂) (Nat.card W₁) := by
  let p : ℕ := Nat.card W₂
  let q : ℕ := Nat.card W₁
  let u : ℕ := Nat.card U
  let H : Subgroup G := Fitting_core L
  let h : ℕ := Nat.card H
  obtain ⟨hqPrime0, hpPrime0⟩ :=
    FTtypeP_primes S U W W₁ W₂ defW ctxS.maxS ctxS.StypeP
  have hpPrime : p.Prime := by simpa only [p] using hpPrime0
  have hqPrime : q.Prime := by simpa only [q] using hqPrime0
  have hpOdd : Odd p := by simpa only [p] using mFT_odd W₂
  have hqOdd : Odd q := by simpa only [q] using mFT_odd W₁
  have hqp : q < p := by simpa only [p, q] using hlt
  have hqThree : 3 ≤ q := hqPrime.odd_iff.mp hqOdd
  have hUstar : ctxS.ustar = nU p q := by
    change (p ^ q - 1) / (p - 1) = nU p q
    exact (nU_eq_div_of_prime hpPrime).symm
  have hGaloisFormula := card_FTtypeP_Galois_compl ctxS hGalS
  by_cases hmodS : Nat.ModEq ctxS.q ctxS.p 1
  · have hmod : Nat.ModEq q p 1 := by
      simpa only [p, q] using hmodS
    rw [if_pos hmodS] at hGaloisFormula
    obtain ⟨_, hModDvd, _⟩ := FTtypeP_primes_mod_cases ctxS
    have hqDvdNU : q ∣ nU p q := by
      have hqDvdUstar := hModDvd hmodS
      simpa only [q, hUstar] using hqDvdUstar
    have hUFormula : u = nU p q / q := by
      calc
        u = ctxS.ustar / q := by
          simpa only [u, q] using hGaloisFormula
        _ = nU p q / q := by rw [hUstar]
    have hqMulU : q * u = nU p q := by
      rw [hUFormula]
      exact Nat.mul_div_cancel' hqDvdNU
    have hFrobUW₁ : PTypeFrobeniusProduct U W₁ :=
      (FTtypeP_facts ctxS).2.2.1
    let J : Subgroup G := U ⊔ W₁
    have hFrobJ : IsFrobeniusDecomposition
        (U.subgroupOf J) (W₁.subgroupOf J) := by
      simpa only [PTypeFrobeniusProduct, J] using hFrobUW₁
    have hqDvdUPred : q ∣ u - 1 := by
      have hd := ftt2_frobenius_pred_dvd hFrobJ
      simpa only [J, p, q, u,
        MathlibSupport.natCard_subgroupOf_eq le_sup_left,
        MathlibSupport.natCard_subgroupOf_eq le_sup_right] using hd
    have huOne : 1 ≤ u := by
      dsimp only [u]
      exact Nat.card_pos
    have hUmodQ : Nat.ModEq q 1 u :=
      (Nat.modEq_iff_dvd' huOne).2 hqDvdUPred
    obtain ⟨x, hCoreCard⟩ : ∃ x, h = u * x := by
      have hd : Nat.card U ∣ Nat.card (Fitting_core L) :=
        Subgroup.card_dvd_of_le sUH
      rcases hd with ⟨x, hx⟩
      exact ⟨x, by simpa only [h, H, u] using hx⟩
    have hhOne : 1 ≤ h := by
      dsimp only [h, H]
      exact Nat.card_pos
    obtain ⟨E, hFrobLE⟩ := frobL
    have hIndexDvdCorePred :
        (H.subgroupOf L).index ∣ h - 1 := by
      simpa only [H, h] using
        ftt2_frobenius_index_dvd_kernel_sub_one hFrobLE
    let W₂y : Subgroup G := conjugateSubgroup8 W₂ y
    have hcardW₂y : Nat.card W₂y = Nat.card W₂ := by
      dsimp only [W₂y, conjugateSubgroup8]
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    have hIndexEq :
        (H.subgroupOf L).index = Nat.card (W₁ ⊔ W₂y : Subgroup G) := by
      exact defLy.2.2.2.symm.index_eq_card.trans
        (MathlibSupport.natCard_subgroupOf_eq defLy.2.1)
    have hpDvdIndex : p ∣ (H.subgroupOf L).index := by
      rw [hIndexEq]
      change Nat.card W₂ ∣ Nat.card (W₁ ⊔ W₂y : Subgroup G)
      rw [← hcardW₂y]
      exact Subgroup.card_dvd_of_le le_sup_right
    have hqDvdIndex : q ∣ (H.subgroupOf L).index := by
      rw [hIndexEq]
      change Nat.card W₁ ∣ Nat.card (W₁ ⊔ W₂y : Subgroup G)
      exact Subgroup.card_dvd_of_le le_sup_left
    have hpDvdCorePred : p ∣ h - 1 :=
      hpDvdIndex.trans hIndexDvdCorePred
    have hqDvdCorePred : q ∣ h - 1 :=
      hqDvdIndex.trans hIndexDvdCorePred
    have hCoreModP : Nat.ModEq p 1 h :=
      (Nat.modEq_iff_dvd' hhOne).2 hpDvdCorePred
    have hCoreModQ : Nat.ModEq q 1 h :=
      (Nat.modEq_iff_dvd' hhOne).2 hqDvdCorePred
    have hCoreCardS : Nat.card ctxS.P = p ^ q := by
      simpa only [p, q] using (FTtypeP_facts ctxS).2.2.2.2.2.1
    have hpDvdCoreS : p ∣ Nat.card ctxS.P := by
      rw [hCoreCardS]
      exact dvd_pow_self p hqPrime.ne_zero
    have huDvdJoin : u ∣ Nat.card (U ⊔ W₁ : Subgroup G) := by
      change Nat.card U ∣ Nat.card (U ⊔ W₁ : Subgroup G)
      exact Subgroup.card_dvd_of_le le_sup_left
    have hpuCoprime : Nat.Coprime p u :=
      ((Ptype_Fcore_coprime ctxS.ptypeCtx).coprime_dvd_left
        hpDvdCoreS).coprime_dvd_right huDvdJoin
    have hnUmodP : Nat.ModEq p (nU p q) 1 :=
      ftt2_nU_modEq_one hqPrime.pos
    have hqxMul : Nat.ModEq p (q * u) (x * u) := by
      calc
        q * u = nU p q := hqMulU
        _ ≡ 1 [MOD p] := hnUmodP
        _ ≡ h [MOD p] := hCoreModP
        _ = u * x := hCoreCard
        _ = x * u := Nat.mul_comm _ _
    have hqx : Nat.ModEq p q x :=
      Nat.ModEq.cancel_right_of_coprime hpuCoprime.gcd_eq_one hqxMul
    have hxRemP : x % p = q :=
      Nat.mod_eq_of_modEq hqx.symm hqp
    obtain ⟨n, hxEq⟩ : ∃ n, x = q + n * p := by
      refine ⟨x / p, ?_⟩
      calc
        x = x % p + p * (x / p) := (Nat.mod_add_div x p).symm
        _ = q + (x / p) * p := by rw [hxRemP, Nat.mul_comm]
    have hxToCore : Nat.ModEq q x h := by
      calc
        x = 1 * x := (Nat.one_mul x).symm
        _ ≡ u * x [MOD q] := hUmodQ.mul_right x
        _ = h := hCoreCard.symm
    have hxModQ : Nat.ModEq q 1 x :=
      hCoreModQ.trans hxToCore.symm
    have hqZero : Nat.ModEq q q 0 := Nat.modulus_modEq_zero
    have hxn : Nat.ModEq q x n := by
      rw [hxEq]
      simpa only [zero_add, Nat.mul_one] using
        hqZero.add (hmod.mul_left n)
    have hnModQ : Nat.ModEq q 1 n := hxModQ.trans hxn
    have hnPos : 0 < n := by
      by_contra hn
      have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      have hqDvdOne : q ∣ 1 := Nat.modEq_zero_iff_dvd.mp hnModQ
      have hqLeOne : q ≤ 1 := Nat.le_of_dvd Nat.zero_lt_one hqDvdOne
      omega
    have hqDvdNPred : q ∣ n - 1 :=
      (Nat.modEq_iff_dvd' hnPos).mp hnModQ
    have hCoreOdd : Odd h := by
      simpa only [h, H] using mFT_odd (Fitting_core L)
    have hMulOdd : Odd (u * x) := by
      simpa only [hCoreCard] using hCoreOdd
    have hxOdd : Odd x := (Nat.odd_mul.mp hMulOdd).2
    have hnNeOne : n ≠ 1 := by
      intro hnOne
      subst n
      have hxEven : Even x := by
        rw [hxEq, one_mul]
        exact hqOdd.add_odd hpOdd
      exact (Nat.not_even_iff_odd.mpr hxOdd) hxEven
    have hnPredPos : 0 < n - 1 := by omega
    have hqLeNPred : q ≤ n - 1 :=
      Nat.le_of_dvd hnPredPos hqDvdNPred
    have hnLower : q + 1 ≤ n := by omega
    have hxLower : q + (q + 1) * p ≤ x := by
      rw [hxEq]
      exact Nat.add_le_add_left (Nat.mul_le_mul_right p hnLower) q
    have hqPredPos : 0 < q - 1 := by omega
    have hnUPrevPos : 0 < nU p (q - 1) := by
      rw [← Nat.succ_pred_eq_of_pos hqPredPos, nU_succ]
      exact Nat.add_pos_right _ (pow_pos hpPrime.pos _)
    have hnUSplit :
        nU p q = nU p (q - 1) + p ^ (q - 1) := by
      calc
        nU p q = nU p ((q - 1) + 1) := by
          rw [Nat.sub_add_cancel hqPrime.one_le]
        _ = nU p (q - 1) + p ^ (q - 1) := nU_succ p (q - 1)
    have hpPowSplit : p ^ q = p * p ^ (q - 1) := by
      calc
        p ^ q = p ^ ((q - 1) + 1) := by
          rw [Nat.sub_add_cancel hqPrime.one_le]
        _ = p * p ^ (q - 1) := by rw [pow_succ']
    have hpPowLtPNu : p ^ q < p * nU p q := by
      rw [hnUSplit, Nat.mul_add, hpPowSplit]
      have hpos : 0 < p * nU p (q - 1) :=
        Nat.mul_pos hpPrime.pos hnUPrevPos
      omega
    have hpqLeX : p * q ≤ x := by
      calc
        p * q ≤ p * q + (q + p) := Nat.le_add_right _ _
        _ = q + (q + 1) * p := by ring
        _ ≤ x := hxLower
    have hpNuLeCore : p * nU p q ≤ h := by
      calc
        p * nU p q = p * (q * u) := by rw [hqMulU]
        _ = u * (p * q) := by ac_rfl
        _ ≤ u * x := Nat.mul_le_mul_left u hpqLeX
        _ = h := hCoreCard.symm
    have hCoreLower : p ^ q < h := hpPowLtPNu.trans_le hpNuLeCore
    have hLMCases :
        (((h - 1 : ℕ) : ℝ) / ((p * q : ℕ) : ℝ) ≤
          ((p * q : ℕ) : ℝ) - 1) ∨ (q = 3 ∧ p = 5) := by
      simpa only [h, H, p, q] using hLM
    have hCoreUpper : h ≤ p ^ 2 * q ^ 2 := by
      rcases hLMCases with hratio | ⟨hq3, hp5⟩
      · have hpqPos : 0 < p * q := Nat.mul_pos hpPrime.pos hqPrime.pos
        have hpqPosR : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by
          exact_mod_cast hpqPos
        have hpqOne : 1 ≤ p * q := hpqPos
        have hpqOneR : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by
          exact_mod_cast hpqOne
        have hmul := (div_le_iff₀ hpqPosR).mp hratio
        rw [Nat.cast_sub hhOne] at hmul
        have hreal :
            (h : ℝ) ≤ ((p ^ 2 * q ^ 2 : ℕ) : ℝ) := by
          calc
            (h : ℝ) = ((h : ℝ) - 1) + 1 := by ring
            _ ≤ ((((p * q : ℕ) : ℝ) - 1) *
                  ((p * q : ℕ) : ℝ)) + 1 :=
              by
                simpa only [Nat.cast_one, add_comm] using
                  add_le_add_right hmul 1
            _ ≤ ((((p * q : ℕ) : ℝ) - 1) *
                  ((p * q : ℕ) : ℝ)) + ((p * q : ℕ) : ℝ) :=
              by
                simpa only [add_comm] using
                  add_le_add_left hpqOneR
                    ((((p * q : ℕ) : ℝ) - 1) *
                      ((p * q : ℕ) : ℝ))
            _ = ((p ^ 2 * q ^ 2 : ℕ) : ℝ) := by
              norm_num only [Nat.cast_mul, Nat.cast_pow]
              ring
        exact_mod_cast hreal
      · have hbad : Nat.ModEq 3 5 1 := by
          simpa only [hq3, hp5] using hmod
        have hthreeDvdFour : 3 ∣ 4 :=
          (Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 5)).mp hbad.symm
        norm_num at hthreeDvdFour
    have hpFactor : p ^ q = p ^ (q - 2) * p ^ 2 := by
      rw [← pow_add, Nat.sub_add_cancel hqPrime.two_le]
    have hSmallMul : p ^ (q - 2) * p ^ 2 < q ^ 2 * p ^ 2 := by
      calc
        p ^ (q - 2) * p ^ 2 = p ^ q := hpFactor.symm
        _ < h := hCoreLower
        _ ≤ p ^ 2 * q ^ 2 := hCoreUpper
        _ = q ^ 2 * p ^ 2 := by ac_rfl
    have hSmall : p ^ (q - 2) < q ^ 2 :=
      (Nat.mul_lt_mul_right (pow_pos hpPrime.pos 2)).mp hSmallMul
    have hqEq : q = 3 := by
      by_contra hqNe
      have hqFive : 5 ≤ q := by
        rcases hqOdd with ⟨a, ha⟩
        omega
      have hreverse : q ^ 2 < p ^ (q - 2) := by
        calc
          q ^ 2 < q ^ 3 := Nat.pow_lt_pow_right hqPrime.one_lt (by omega)
          _ < p ^ 3 := Nat.pow_lt_pow_left hqp (by norm_num)
          _ ≤ p ^ (q - 2) := Nat.pow_le_pow_right hpPrime.pos (by omega)
      exact (lt_asymm hSmall hreverse).elim
    have hpNine : p < 9 := by
      simpa [hqEq] using hSmall
    have hpModThree : p % 3 = 1 := by
      simpa [Nat.ModEq, hqEq] using hmod
    have hpEq : p = 7 := by
      rcases hpOdd with ⟨a, ha⟩
      omega
    have huEq : u = 19 := by
      have hqMulU' := hqMulU
      rw [hqEq, hpEq] at hqMulU'
      norm_num [nU] at hqMulU'
      omega
    have hxLower' := hxLower
    have hCoreUpper' := hCoreUpper
    have hCoreCard' := hCoreCard
    rw [hqEq, hpEq] at hxLower' hCoreUpper'
    rw [huEq] at hCoreCard'
    norm_num at hxLower' hCoreUpper' hCoreCard'
    omega
  · calc
      Nat.card U = ctxS.ustar := by
        simpa only [if_neg hmodS] using hGaloisFormula
      _ = nU p q := hUstar
      _ = nU (Nat.card W₂) (Nat.card W₁) := rfl

private theorem ftt2_subgroupNonidentity_ncard (H : Subgroup G) :
    (subgroupNonidentity H).ncard = Nat.card H - 1 := by
  have hone : (1 : G) ∈ (H : Set G) := H.one_mem
  rw [show subgroupNonidentity H = (H : Set G) \ {1} by
    ext x
    simp [subgroupNonidentity, nonidentitySet]]
  rw [Set.ncard_sdiff_singleton_of_mem hone, ← Nat.card_coe_set_eq,
    SetLike.coe_sort_coe]

private theorem ftt2_ncard_preimage_top (A : Set G) :
    ({x : (⊤ : Subgroup G) | (x : G) ∈ A} : Set (⊤ : Subgroup G)).ncard =
      A.ncard := by
  calc
    _ = (A ∩ ((⊤ : Subgroup G) : Set G)).ncard := Set.ncard_subtype _ _
    _ = A.ncard := by
      rw [Set.inter_eq_left.mpr (fun _ _ => Subgroup.mem_top _)]

private theorem ftt2_ncard_classSupport_normalizedTI
    {S : Set G} {N : Subgroup G}
    (hTI : IsNormalizedTI S (⊤ : Subgroup G) N) :
    (classSupportWithin (⊤ : Subgroup G) S).ncard =
      S.ncard * N.index := by
  let action := subgroupConjugationActionOnAmbient (⊤ : Subgroup G)
  letI : SMul (⊤ : Subgroup G) G := action.toSMul
  letI : MulAction (⊤ : Subgroup G) G := action.toMulAction
  letI : MulAction (⊤ : Subgroup G) (Set G) := Set.mulActionSet
  have hpart := normalizedTI_classSupport_partition hTI
  change IsSetPartition (MulAction.orbit (⊤ : Subgroup G) S)
      (classSupportWithin (⊤ : Subgroup G) S) ∧
    (MulAction.orbit (⊤ : Subgroup G) S).ncard =
      N.relIndex (⊤ : Subgroup G) at hpart
  have horbitFinite :
      (MulAction.orbit (⊤ : Subgroup G) S).Finite := Set.toFinite _
  have hblock : ∀ B ∈ MulAction.orbit (⊤ : Subgroup G) S,
      B.ncard = S.ncard := by
    intro B hB
    rcases hB with ⟨g, rfl⟩
    exact Set.ncard_smul_set g S
  rw [← hpart.1.1]
  have hsUnion : ⋃₀ (MulAction.orbit (⊤ : Subgroup G) S) =
      ⋃ B ∈ MulAction.orbit (⊤ : Subgroup G) S, B := by
    ext x
    simp
  rw [hsUnion]
  calc
    (⋃ B ∈ MulAction.orbit (⊤ : Subgroup G) S, B).ncard =
        ∑ᶠ B ∈ MulAction.orbit (⊤ : Subgroup G) S, B.ncard :=
      horbitFinite.ncard_biUnion
        (fun B _ => Set.toFinite B) hpart.1.2.1
    _ = ∑ᶠ _B ∈ MulAction.orbit (⊤ : Subgroup G) S, S.ncard :=
      finsum_mem_congr rfl hblock
    _ = (∑ᶠ _B ∈ MulAction.orbit (⊤ : Subgroup G) S, (1 : Nat)) *
          S.ncard := by
      rw [finsum_mem_mul' (fun _B : Set G => 1) S.ncard horbitFinite]
      simp
    _ = (MulAction.orbit (⊤ : Subgroup G) S).ncard * S.ncard := by
      rw [finsum_one]
    _ = N.relIndex (⊤ : Subgroup G) * S.ncard := by rw [hpart.2]
    _ = S.ncard * N.index := by
      rw [N.relIndex_top_right, Nat.mul_comm]

private theorem ftt2_classSupport_ratio_eq
    {S : Set G} {N : Subgroup G}
    (hTI : IsNormalizedTI S (⊤ : Subgroup G) N) :
    (classSupportWithin (⊤ : Subgroup G) S).ncard /
        (Nat.card G : Real) =
      S.ncard / (Nat.card N : Real) := by
  have hcard := ftt2_ncard_classSupport_normalizedTI hTI
  have hindex : N.index * Nat.card N = Nat.card G := by
    simpa only [Subgroup.card_top] using N.index_mul_card
  rw [hcard]
  norm_num only [Nat.cast_mul]
  rw [← hindex]
  norm_num only [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne',
    Nat.cast_ne_zero.mpr N.index_ne_zero_of_finite]

private theorem ftt2_oneCover_upper_bound
    {Q : Type} [Fintype Q]
    (chi : Q → Complex) (C C0 C1 : Set Q)
    (hpartition : C = C0 ∪ C1)
    (hdisjoint : Disjoint C0 C1)
    (hlarge : ∀ x ∈ C0, 1 ≤ Complex.normSq (chi x))
    (rho base : Real)
    (hSuzuki :
      (Nat.card Q : Real)⁻¹ *
          ((∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0) -
            C.ncard) + rho - base ≤ 0) :
    rho ≤ base + C1.ncard / (Nat.card Q : Real) := by
  classical
  have hcard0 :
      (Finset.univ.filter (fun x : Q => x ∈ C0)).card = C0.ncard := by
    calc
      _ = ((Finset.univ.filter (fun x : Q => x ∈ C0) : Set Q)).ncard :=
        (Set.ncard_coe_finset _).symm
      _ = C0.ncard := by
        congr 1
        ext x
        simp
  have hmass : (C0.ncard : Real) ≤
      ∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0 := by
    calc
      (C0.ncard : Real) =
          ∑ x : Q, if x ∈ C0 then (1 : Real) else 0 := by
        rw [← Finset.sum_filter]
        simp only [Finset.sum_const, nsmul_eq_mul, mul_one]
        exact_mod_cast hcard0.symm
      _ ≤ ∑ x : Q,
          if x ∈ C then Complex.normSq (chi x) else 0 := by
        apply Finset.sum_le_sum
        intro x _
        by_cases hx0 : x ∈ C0
        · have hxC : x ∈ C := by
            rw [hpartition]
            exact Or.inl hx0
          simp only [hx0, hxC, if_true]
          exact hlarge x hx0
        · by_cases hxC : x ∈ C
          · simp only [hx0, hxC, if_false, if_true]
            exact Complex.normSq_nonneg _
          · simp [hx0, hxC]
  have hcardC : C.ncard = C0.ncard + C1.ncard := by
    rw [hpartition, Set.ncard_union_eq hdisjoint]
  have hinvnonneg : (0 : Real) ≤ (Nat.card Q : Real)⁻¹ :=
    inv_nonneg.mpr (Nat.cast_nonneg _)
  have hterm :
      -(C1.ncard / (Nat.card Q : Real)) ≤
        (Nat.card Q : Real)⁻¹ *
          ((∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0) -
            C.ncard) := by
    rw [hcardC]
    norm_num only [Nat.cast_add]
    have h := mul_le_mul_of_nonneg_left
      (show -(C1.ncard : Real) ≤
          (∑ x : Q, if x ∈ C then Complex.normSq (chi x) else 0) -
            ((C0.ncard : Real) + C1.ncard) by linarith)
      hinvnonneg
    simpa [div_eq_inv_mul, mul_comm, mul_left_comm] using h
  linarith

private theorem ftt2_normSq_smul
    {Q : Type} [Group Q] [Fintype Q]
    (a : Complex) (f : ClassFunction Q Complex) :
    classFunctionNormSq (a • f) =
      Complex.normSq a * classFunctionNormSq f := by
  unfold classFunctionNormSq
  simp only [ClassFunction.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]
  ring_nf

private theorem ftt2_one_lt_nU_of_primes {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime) : 1 < nU p q := by
  have hpTwo : 2 ≤ p := hp.two_le
  have hqTwo : 2 ≤ q := hq.two_le
  have hmono : nU p 2 ≤ nU p q := by
    unfold nU
    apply Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono hqTwo)
    intro i _ _
    exact Nat.zero_le _
  have hsmall : 1 < nU p 2 := by
    simp only [nU, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, pow_one]
    omega
  exact hsmall.trans_le hmono

/-! ## The signed eta rectangle at a coprime-order element -/

private theorem ftt2_targetMap_inverse_eta
    {S U W W1 W2 : Subgroup G}
    {defW : IsInternalDirectProductIn W1 W2 W}
    (ctx : FTTypePSetupContext S U W W1 W2 defW)
    (phi : ClassFunction (⊤ : Subgroup G) Complex) :
    ClassFunction.inverseLinear (ctx.targetMap phi) =
      ctx.targetMap (ClassFunction.inverseLinear phi) := by
  ext x
  simp [ClassFunction.inverseLinear_apply, ClassFunction.comap_apply]

private theorem ftt2_cyclicSource_inverse_eta
    {W W1 W2 : Subgroup G}
    {defW : IsInternalDirectProductIn W1 W2 W}
    (i : IrreducibleCharacter W1 Complex)
    (j : IrreducibleCharacter W2 Complex) :
    ClassFunction.inverseLinear
        (CyclicTIIsometryData.cyclicTISourceIrreducible
          (defW := defW) (i, j)) =
      CyclicTIIsometryData.cyclicTISourceIrreducible
        (defW := defW)
        (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j) := by
  ext w
  simp [CyclicTIIsometryData.cyclicTISourceIrreducible,
    IrreducibleCharacter.cyclicTICharacter_apply]

private theorem ftt2_eta_inverse
    {S U W W1 W2 : Subgroup G}
    {defW : IsInternalDirectProductIn W1 W2 W}
    (ctx : FTTypePSetupContext S U W W1 W2 defW)
    (i : IrreducibleCharacter W1 Complex)
    (j : IrreducibleCharacter W2 Complex) :
    ClassFunction.inverseLinear (ctx.eta i j) =
      ctx.eta (IrreducibleCharacter.dual i)
        (IrreducibleCharacter.dual j) := by
  rw [ftt2_targetMap_inverse_eta]
  change ctx.targetMap
      (ClassFunction.inverseLinear
        (ctx.isoG.linearMap
          (CyclicTIIsometryData.cyclicTISourceIrreducible
            (defW := defW) (i, j)))) = _
  rw [ctx.isoG.inverse_cyclicTIIsometry,
    ftt2_cyclicSource_inverse_eta]
  rfl

private theorem ftt2_eta_virtual
    {S U W W1 W2 : Subgroup G}
    {defW : IsInternalDirectProductIn W1 W2 W}
    (ctx : FTTypePSetupContext S U W W1 W2 defW)
    (i : IrreducibleCharacter W1 Complex)
    (j : IrreducibleCharacter W2 Complex) :
    ClassFunction.IsVirtual (ctx.eta i j) := by
  obtain ⟨theta, e, _he, himage⟩ :=
    ctx.isoG.cyclicTIImage_eq_signed_irreducible (i, j)
  have htop : ClassFunction.IsVirtual
      (ctx.isoG.cyclicTIImage (i, j)) := by
    refine ⟨Finsupp.single theta e, ?_⟩
    rw [VirtualCharacter.realize_single]
    exact himage.symm
  simpa only [FTTypePSetupContext.eta, FTTypePSetupContext.targetMap,
    ftt2TargetMap] using ftt2_target_virtual htop

private theorem ftt2_int_sum_ne_zero_of_unique_fixed_involution
    {I : Type} [Fintype I] [DecidableEq I]
    (sigma : Equiv.Perm I) (i0 : I)
    (hinvol : ∀ i, sigma (sigma i) = i)
    (hsigma : ∀ i, sigma i = i ↔ i = i0)
    (d : I → Int)
    (hpair : ∀ i,
      (d i : ZMod 2) + (d (sigma i) : ZMod 2) = 0)
    (hd0 : (d i0 : ZMod 2) = 1) :
    ∑ i, d i ≠ 0 := by
  let moved : Finset I := Finset.univ.filter fun i => sigma i ≠ i
  have hsigmaMoved : ∀ i, i ∈ moved → sigma i ∈ moved := by
    intro i hi
    simp only [moved, Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    intro hfix
    apply hi
    exact sigma.injective hfix
  have hsigmaMovedNe : ∀ i, i ∈ moved → sigma i ≠ i := by
    intro i hi
    exact (Finset.mem_filter.mp hi).2
  have hmoved : ∑ i ∈ moved, (d i : ZMod 2) = 0 := by
    apply Finset.sum_involution
        (s := moved) (f := fun i => (d i : ZMod 2))
        (fun i _ => sigma i)
    · intro i _
      exact hpair i
    · intro i hi _
      exact hsigmaMovedNe i hi
    · exact hsigmaMoved
    · intro i _
      exact hinvol i
  have hfixed : Finset.univ.filter (fun i => sigma i = i) = {i0} := by
    ext i
    simp [hsigma i]
  have hcast : ((∑ i, d i : Int) : ZMod 2) = 1 := by
    simp only [Int.cast_sum]
    rw [← Finset.sum_filter_add_sum_filter_not
      (s := (Finset.univ : Finset I)) (p := fun i => sigma i = i)]
    rw [hfixed, Finset.sum_singleton, hd0]
    have hmoved' :
        Finset.univ.filter (fun i => sigma i ≠ i) = moved := by
      ext i
      simp [moved]
    rw [hmoved', hmoved, add_zero]
  intro hzero
  rw [hzero, Int.cast_zero] at hcast
  exact zero_ne_one hcast

private theorem ftt2_not_mem_cyclic_product_support
    {S T U V W W1 W2 : Subgroup G}
    {defW : IsInternalDirectProductIn W1 W2 W}
    {xdefW : IsInternalDirectProductIn W2 W1 W}
    (ctxS : FTTypePSetupContext S U W W1 W2 defW)
    (ctxT : FTTypePSetupContext T V W W2 W1 xdefW)
    (g : G)
    (hSW : g ∉ classSupportWithin (⊤ : Subgroup G)
      (cyclicTISet W W1 W2))
    (hSP : g ∉ classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity (Fitting_core S)))
    (hSQ : g ∉ classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity (Fitting_core T))) :
    g ∉ classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity W) := by
  rintro ⟨x, hx, y, hy, hxy⟩
  by_cases hxW1 : x ∈ W1
  · apply hSQ
    exact ⟨x, ⟨ctxT.StypeP.2.2.2.1.2.2.1 hxW1, hx.2⟩, y, hy, hxy⟩
  by_cases hxW2 : x ∈ W2
  · apply hSP
    exact ⟨x, ⟨ctxS.StypeP.2.2.2.1.2.2.1 hxW2, hx.2⟩, y, hy, hxy⟩
  apply hSW
  exact ⟨x, (mem_cyclicTISet.mpr ⟨hx.1, hxW1, hxW2⟩), y, hy, hxy⟩

private theorem ftt2_cyclicTI_coprime_value_isInt_complex
    {Gamma : Type} [Group Gamma] [Fintype Gamma]
    {H W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (h : CyclicTIHypothesis H W W₁ W₂ defW)
    (iso : CyclicTIIsometryData (k := ℂ) h)
    (w : IrreducibleCharacter W ℂ) (x : H)
    (hx : (orderOf x).Coprime (Fintype.card W)) :
    ∃ z : ℤ,
      iso.linearMap (w : ClassFunction W ℂ) x = (z : ℂ) := by
  let phi : ClassFunction H ℂ :=
    iso.linearMap (w : ClassFunction W ℂ)
  have hphiIntegral : IsIntegral ℤ (phi x) := by
    obtain ⟨psi, epsilon, _hepsilon, hphi⟩ :=
      iso.exists_signed_irreducible_image w
    have hpsi : IsIntegral ℤ (psi x) := by
      rw [← psi.representation_character]
      exact representation_character_isIntegral psi.representation.ρ x
    have hepsilonIntegral : IsIntegral ℤ (epsilon : ℂ) :=
      isIntegral_intCast epsilon
    have hvalue : phi x = (epsilon : ℂ) * psi x :=
      congrArg (fun f : ClassFunction H ℂ => f x) hphi
    rw [hvalue]
    exact hepsilonIntegral.mul hpsi
  let a := Fintype.card W
  have haPos : 0 < a := Fintype.card_pos
  letI : NeZero a := ⟨Nat.ne_of_gt haPos⟩
  obtain ⟨omegaValue, homegaValue⟩ :=
    HasEnoughRootsOfUnity.exists_primitiveRoot ℂ a
  let omega : ℂˣ := Units.mk0 omegaValue
    (homegaValue.ne_zero (NeZero.ne a))
  have homega : IsPrimitiveRoot omega a := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa only [omega, Units.val_mk0] using homegaValue
  have hphiFixedComplex :
      ∀ sigma : ℂ ≃ₐ[ℚ] ℂ, sigma (phi x) = phi x := by
    intro sigma
    have hsigmaPrimitive :
        IsPrimitiveRoot (sigma omegaValue) a :=
      homegaValue.map_of_injective sigma.injective
    obtain ⟨k, _hklt, hkcop, hkpow⟩ :=
      (homegaValue.isPrimitiveRoot_iff).mp hsigmaPrimitive
    have hsigmaOmega :
        sigma (omega : ℂ) = (omega : ℂ) ^ k := by
      simpa only [omega, Units.val_mk0] using hkpow.symm
    obtain ⟨nu, hnuPower, hnuFixed⟩ :=
      make_pi_cfAut_complex H a k hkcop
    have hsource :
        ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
            (w : ClassFunction W ℂ) =
          ClassFunction.mapRingHom sigma.toRingEquiv.toRingHom
            (w : ClassFunction W ℂ) := by
      ext y
      change nu (w y) = sigma (w y)
      have hnuY := hnuPower
        (Finsupp.single w 1 : VirtualCharacter W ℂ) y
        orderOf_dvd_card
      have hsigmaY := algEquiv_virtualCharacter_apply_eq_pow
        homega sigma k hsigmaOmega
        (Finsupp.single w 1 : VirtualCharacter W ℂ) y
        orderOf_dvd_card
      simpa only [VirtualCharacter.realize_single,
        ClassFunction.smul_apply, Int.cast_one, one_smul] using
        hnuY.trans hsigmaY.symm
    let z : VirtualCharacter H ℂ :=
      iso.virtualMap (Finsupp.single w 1)
    have hz : VirtualCharacter.realize z = phi := by
      rw [iso.realize_virtualMap]
      simp only [VirtualCharacter.realize_single, Int.cast_one, one_smul,
        phi]
    calc
      sigma (phi x) =
          iso.linearMap
            (ClassFunction.mapRingHom sigma.toRingEquiv.toRingHom
              (w : ClassFunction W ℂ)) x := by
        exact congrArg (fun f : ClassFunction H ℂ => f x)
          (iso.mapRingEquiv_cyclicTIIsometry sigma.toRingEquiv
            (w : ClassFunction W ℂ))
      _ = iso.linearMap
            (ClassFunction.mapRingHom nu.toRingEquiv.toRingHom
              (w : ClassFunction W ℂ)) x := by
        rw [hsource]
      _ = nu (phi x) := by
        exact congrArg (fun f : ClassFunction H ℂ => f x)
          (iso.mapRingEquiv_cyclicTIIsometry nu.toRingEquiv
            (w : ClassFunction W ℂ)).symm
      _ = phi x := by
        simpa only [hz] using hnuFixed z x hx
  have hphiIntegralQ : IsIntegral ℚ (phi x) :=
    IsIntegral.tower_top hphiIntegral
  let A := algebraicClosure ℚ ℂ
  letI : Module.IsTorsionFree ℚ A :=
    Module.isTorsionFree_iff_algebraMap_injective.mpr
      (algebraMap ℚ A).injective
  letI : IsAlgClosure ℚ A := by
    dsimp only [A]
    exact algebraicClosure.isAlgClosure ℚ ℂ
  let phiA : A :=
    ⟨phi x, mem_algebraicClosure_iff'.2 hphiIntegralQ⟩
  have hphiFixedA : ∀ sigma : A ≃ₐ[ℚ] A, sigma phiA = phiA := by
    intro sigma
    obtain ⟨sigmaC, hsigmaC⟩ :=
      exists_complex_algEquiv_extending_algebraicClosure sigma
    apply Subtype.ext
    exact (hsigmaC phiA).symm.trans (hphiFixedComplex sigmaC)
  have hphiRat : ∃ q : ℚ, phi x = (q : ℂ) := by
    have hmem : phiA ∈ Set.range (algebraMap ℚ A) :=
      (InfiniteGalois.mem_range_algebraMap_iff_fixed phiA).2 hphiFixedA
    obtain ⟨q, hq⟩ := hmem
    refine ⟨q, ?_⟩
    exact (congrArg Subtype.val hq).symm.trans rfl
  obtain ⟨z, hz⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hphiIntegral).mp hphiRat
  exact ⟨z, by simpa only [phi] using hz⟩

private theorem ftt2_signed_eta_rectangle_lower
    {S T U V W W1 W2 : Subgroup G}
    {defW : IsInternalDirectProductIn W1 W2 W}
    {xdefW : IsInternalDirectProductIn W2 W1 W}
    (ctxS : FTTypePSetupContext S U W W1 W2 defW)
    (ctxT : FTTypePSetupContext T V W W2 W1 xdefW)
    (hGalS : ctxS.galoisAlternative)
    (hGalT : ctxT.galoisAlternative)
    (eps : IrreducibleCharacter W2 Complex →
      IrreducibleCharacter W1 Complex → Bool)
    (g : G)
    (hSW : g ∉ classSupportWithin (⊤ : Subgroup G)
      (cyclicTISet W W1 W2))
    (hSP : g ∉ classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity (Fitting_core S)))
    (hSQ : g ∉ classSupportWithin (⊤ : Subgroup G)
      (subgroupNonidentity (Fitting_core T))) :
    1 ≤ Complex.normSq
      ((∑ i, ∑ j,
        if eps i j then -(ctxT.eta i j) else ctxT.eta i j) g) := by
  classical
  have hW := ftt2_not_mem_cyclic_product_support ctxS ctxT g hSW hSP hSQ
  have hcopP : Nat.Coprime (orderOf g) (Nat.card W2) :=
    coprime_typeP_Galois_core ctxS g hGalS hW hSP
  have hcopQ : Nat.Coprime (orderOf g) (Nat.card W1) :=
    coprime_typeP_Galois_core ctxT g hGalT hW hSQ
  have hcopW : Nat.Coprime (orderOf g) (Fintype.card W) := by
    rw [Fintype.card_eq_nat_card, defW.card_eq_mul_card]
    exact Nat.Coprime.mul_right hcopQ hcopP
  have hetaInt (i : IrreducibleCharacter W2 Complex)
      (j : IrreducibleCharacter W1 Complex) :
      ∃ z : Int, ctxT.eta i j g = (z : Complex) := by
    have hcopTop : Nat.Coprime
        (orderOf (Subgroup.topEquiv.symm g)) (Fintype.card W) := by
      have horderTop : orderOf (Subgroup.topEquiv.symm g) = orderOf g := by
        rw [← Subgroup.orderOf_coe (Subgroup.topEquiv.symm g)]
        exact congrArg orderOf (Subgroup.topEquiv.apply_symm_apply g)
      rw [horderTop]
      exact hcopW
    have htopEval :
        Subgroup.topEquiv.symm.toMonoidHom g =
          Subgroup.topEquiv.symm g := by
      apply Subtype.ext
      rfl
    simpa only [FTTypePSetupContext.eta,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible,
      CyclicTIHypothesis.cyclicTIIsometry,
      FTTypePSetupContext.targetMap, ClassFunction.comap_apply,
      htopEval] using
      ftt2_cyclicTI_coprime_value_isInt_complex
        ctxT.primeDade.prDade_cycTI ctxT.isoG
        (IrreducibleCharacter.cyclicTICharacter xdefW i j)
        (Subgroup.topEquiv.symm g) hcopTop
  let c : IrreducibleCharacter W2 Complex →
      IrreducibleCharacter W1 Complex → Int :=
    fun i j => Classical.choose (hetaInt i j)
  have hcValue (i : IrreducibleCharacter W2 Complex)
      (j : IrreducibleCharacter W1 Complex) :
      ctxT.eta i j g = (c i j : Complex) :=
    Classical.choose_spec (hetaInt i j)
  have hetaDual (i : IrreducibleCharacter W2 Complex)
      (j : IrreducibleCharacter W1 Complex) :
      ctxT.eta (IrreducibleCharacter.dual i)
          (IrreducibleCharacter.dual j) g = ctxT.eta i j g := by
    have hconj := FTType1InfrastructureInternal.inverseEqConjOfVirtual
      (ftt2_eta_virtual ctxT i j)
    have h := congrArg (fun f : ClassFunction G Complex => f g)
      ((ftt2_eta_inverse ctxT i j).symm.trans hconj)
    simpa [cfConjC_apply, hcValue] using h
  have hcDual (i : IrreducibleCharacter W2 Complex)
      (j : IrreducibleCharacter W1 Complex) :
      c (IrreducibleCharacter.dual i)
          (IrreducibleCharacter.dual j) = c i j := by
    apply Int.cast_injective (α := Complex)
    rw [← hcValue, ← hcValue]
    exact hetaDual i j
  have heta00 : ctxT.eta
      (IrreducibleCharacter.trivial : IrreducibleCharacter W2 Complex)
      (IrreducibleCharacter.trivial : IrreducibleCharacter W1 Complex) g = 1 := by
    have hetaOne : ctxT.eta
        (IrreducibleCharacter.trivial : IrreducibleCharacter W2 Complex)
        (IrreducibleCharacter.trivial : IrreducibleCharacter W1 Complex) =
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G Complex) :
          ClassFunction G Complex) := by
      change ctxT.targetMap
        (ctxT.isoG.linearMap
          (CyclicTIIsometryData.cyclicTISourceIrreducible
            (defW := xdefW)
            (IrreducibleCharacter.trivial,
              IrreducibleCharacter.trivial))) = _
      rw [show CyclicTIIsometryData.cyclicTISourceIrreducible
          (defW := xdefW)
          (IrreducibleCharacter.trivial,
            IrreducibleCharacter.trivial) =
          ((IrreducibleCharacter.trivial : IrreducibleCharacter W Complex) :
            ClassFunction W Complex) by
        exact congrArg
          (fun z : IrreducibleCharacter W Complex =>
            (z : ClassFunction W Complex))
          (IrreducibleCharacter.cyclicTICharacter_trivial xdefW)]
      rw [ctxT.isoG.map_trivial]
      ext x
      simp [ClassFunction.comap_apply]
    have hvalue := congrArg (fun f : ClassFunction G Complex => f g) hetaOne
    simpa only [IrreducibleCharacter.trivial_apply] using hvalue
  have hc00 : c
      (IrreducibleCharacter.trivial : IrreducibleCharacter W2 Complex)
      (IrreducibleCharacter.trivial : IrreducibleCharacter W1 Complex) = 1 := by
    apply Int.cast_injective (α := Complex)
    rw [← hcValue, heta00, Int.cast_one]
  let I := IrreducibleCharacter W2 Complex ×
    IrreducibleCharacter W1 Complex
  let sigma : Equiv.Perm I := Equiv.prodCongr
    IrreducibleCharacter.dualEquiv IrreducibleCharacter.dualEquiv
  let i0 : I :=
    ((IrreducibleCharacter.trivial : IrreducibleCharacter W2 Complex),
      (IrreducibleCharacter.trivial : IrreducibleCharacter W1 Complex))
  let d : I → Int := fun ij =>
    if eps ij.1 ij.2 then -c ij.1 ij.2 else c ij.1 ij.2
  have hsigmaApply (i : IrreducibleCharacter W2 Complex)
      (j : IrreducibleCharacter W1 Complex) :
      sigma (i, j) =
        (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j) := rfl
  have hinvol : ∀ ij, sigma (sigma ij) = ij := by
    rintro ⟨i, j⟩
    calc
      sigma (sigma (i, j)) =
          sigma (IrreducibleCharacter.dual i,
            IrreducibleCharacter.dual j) :=
        congrArg sigma (hsigmaApply i j)
      _ = (IrreducibleCharacter.dual (IrreducibleCharacter.dual i),
          IrreducibleCharacter.dual (IrreducibleCharacter.dual j)) :=
        hsigmaApply (IrreducibleCharacter.dual i)
          (IrreducibleCharacter.dual j)
      _ = (i, j) := by
        rw [IrreducibleCharacter.dual_dual,
          IrreducibleCharacter.dual_dual]
  have hfixed : ∀ ij, sigma ij = ij ↔ ij = i0 := by
    rintro ⟨i, j⟩
    rw [hsigmaApply i j]
    constructor
    · intro h
      have hi : IrreducibleCharacter.dual i = i :=
        congrArg Prod.fst h
      have hj : IrreducibleCharacter.dual j = j :=
        congrArg Prod.snd h
      change (i, j) =
        ((IrreducibleCharacter.trivial :
            IrreducibleCharacter W2 Complex),
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W1 Complex))
      exact Prod.ext
        ((odd_eq_conj_irr1 (mFT_odd W2) i).mp hi)
        ((odd_eq_conj_irr1 (mFT_odd W1) j).mp hj)
    · intro h
      have hi : i =
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W2 Complex) := by
        simpa only [i0] using congrArg Prod.fst h
      have hj : j =
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W1 Complex) := by
        simpa only [i0] using congrArg Prod.snd h
      exact Prod.ext
        ((odd_eq_conj_irr1 (mFT_odd W2) i).mpr hi)
        ((odd_eq_conj_irr1 (mFT_odd W1) j).mpr hj)
  have hnegZModTwo (z : ZMod 2) : -z = z := by
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    calc
      -z = z - (2 : ZMod 2) * z := by ring
      _ = z := by rw [htwo, zero_mul, sub_zero]
  have hdmod (ij : I) :
      (d ij : ZMod 2) = (c ij.1 ij.2 : ZMod 2) := by
    rcases ij with ⟨i, j⟩
    by_cases h : eps i j
    · simpa only [d, h, if_true, Int.cast_neg] using
        hnegZModTwo (c i j : ZMod 2)
    · simp only [d, h, Bool.false_eq_true, if_false]
  have hpair : ∀ ij,
      (d ij : ZMod 2) + (d (sigma ij) : ZMod 2) = 0 := by
    intro ij
    rw [hdmod ij, hdmod (sigma ij)]
    rcases ij with ⟨i, j⟩
    rw [hsigmaApply i j, hcDual i j]
    have htwo : (2 : ZMod 2) = 0 := ZMod.natCast_self 2
    calc
      (c i j : ZMod 2) + (c i j : ZMod 2) =
          (2 : ZMod 2) * (c i j : ZMod 2) := by ring
      _ = 0 := by rw [htwo, zero_mul]
  have hd0 : (d i0 : ZMod 2) = 1 := by
    calc
      (d i0 : ZMod 2) = (c i0.1 i0.2 : ZMod 2) := hdmod i0
      _ = 1 := by simp only [i0, hc00, Int.cast_one]
  have hsumNe : ∑ ij : I, d ij ≠ 0 :=
    ftt2_int_sum_ne_zero_of_unique_fixed_involution
      sigma i0 hinvol hfixed d hpair hd0
  have hsumCast :
      (∑ i, ∑ j,
          if eps i j then -(ctxT.eta i j) else ctxT.eta i j) g =
        ((∑ ij : I, d ij : Int) : Complex) := by
    simp only [ClassFunction.finset_sum_apply, Int.cast_sum]
    rw [Fintype.sum_prod_type]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    by_cases he : eps i j
    · simp [d, he, hcValue]
    · simp [d, he, hcValue]
  rw [hsumCast, Complex.normSq_intCast]
  exact_mod_cast Int.add_one_le_iff.mpr (mul_self_pos.mpr hsumNe)

private theorem ftt2_omegaOneCenterAmbient_ne_bot
    {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {P : Subgroup K}
    (hPp : IsPGroup p P) (hPne : P ≠ ⊥) :
    omegaOneCenterAmbient p P ≠ ⊥ := by
  letI : Nontrivial P := P.nontrivial_iff_ne_bot.mpr hPne
  let Z : Subgroup P := Subgroup.center P
  have hZne : Z ≠ ⊥ := by
    letI : Group.IsNilpotent P := hPp.isNilpotent
    exact Group.IsNilpotent.center_ne_bot P
  have hZp : IsPGroup p Z := hPp.to_subgroup Z
  have hZcard : Nat.card Z ≠ 1 :=
    (Z.one_lt_card_iff_ne_bot.mpr hZne).ne'
  have hOmegaNe : omegaOne p Z ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup hZp hZcard
  have hCenterOmegaNe :
      Submission.OddOrder.BG.Section05.omegaOneCenter p P ≠ ⊥ := by
    dsimp [Submission.OddOrder.BG.Section05.omegaOneCenter, Z]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (omegaOne p (Subgroup.center P))
      (Subgroup.center P).subtype_injective)).mpr hOmegaNe
  dsimp [omegaOneCenterAmbient]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
    (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
    P.subtype_injective)).mpr hCenterOmegaNe

private theorem ftt2_omegaOneCenterAmbient_map_conj_eq
    (p : ℕ) (P : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (P : Set G)) :
    (omegaOneCenterAmbient p P).map (MulAut.conj g).toMonoidHom =
      omegaOneCenterAmbient p P := by
  let Z : Subgroup G := omegaOneCenterAmbient p P
  have hgZ : g ∈ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      exact characteristic_map_subtype_invariant_under_normalizer
        P (Subgroup.normalizer (P : Set G))
        (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
        le_rfl g hg z hz
    · intro hz
      have hginv : g⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
        (Subgroup.normalizer (P : Set G)).inv_mem hg
      have hback := characteristic_map_subtype_invariant_under_normalizer
        P (Subgroup.normalizer (P : Set G))
        (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
        le_rfl g⁻¹ hginv (g * z * g⁻¹) hz
      have hcancel : g⁻¹ * (g * z * g⁻¹) * (g⁻¹)⁻¹ = z := by group
      simpa only [Z, omegaOneCenterAmbient, hcancel] using hback
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp hgZ

private theorem ftt2_starPairing_sub_left
    {Q : Type*} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    starCharacterPairing (f - g) h =
      starCharacterPairing f h - starCharacterPairing g h := by
  simp [sub_eq_add_neg, starCharacterPairing, twistedCharacterPairing,
    add_mul, Finset.sum_add_distrib]
  ring

private theorem ftt2_starPairing_finset_sum_left
    {Q I : Type*} [Group Q] [Fintype Q]
    (s : Finset I) (f : I → ClassFunction Q ℂ)
    (g : ClassFunction Q ℂ) :
    starCharacterPairing (∑ i ∈ s, f i) g =
      ∑ i ∈ s, starCharacterPairing (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_left, ih,
        Finset.sum_insert hi]

private theorem ftt2_starPairing_fintype_sum_left
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ) (g : ClassFunction Q ℂ) :
    starCharacterPairing (∑ i, f i) g =
      ∑ i, starCharacterPairing (f i) g := by
  simpa only [Finset.sum_filter, implies_true] using
    ftt2_starPairing_finset_sum_left Finset.univ f g

/-! ## Source (14.11.3)--(14.11.4), exact paste-site interface -/

/-- Hypothesis (14.3): the larger cyclic factor forces type II. -/
theorem FTtypeP_max_typeII
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (hlt : Nat.card W₁ < Nat.card W₂) :
    FTtype S = 2 :=
  (FTtypeP_facts ctxS).2.1 hlt

/-- Hypothesis (14.9): the smaller cyclic factor also forces type II. -/
theorem FTtypeP_min_typeII
    {S T U V W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (hlt : Nat.card W₁ < Nat.card W₂) :
    FTtype T = 2 := by
  classical
  letI : Invertible (Nat.card T : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := T)).ne')
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne')
  have hforward := ftt2_forward_gap ctxS ctxT hlt
  by_contra hnot2

  let baseT : FTType34Base T V W W₂ W₁ xdefW :=
    { MtypeP := ctxT.StypeP
      notMtype2 := hnot2
      ptypeCtx := ctxT.ptypeCtx }
  letI : baseT.HUInM.Normal := by
    exact TypeSpecInternal.derivedWithin_normal16 T
  have h34 := FTtype34_structure baseT
  have hTtype3 : FTtype T = 3 := h34.2.2.1
  let pairST : typeP_pair S T W W₁ W₂ defW :=
    of_typeP_pair defW ctxS.maxS ctxS.StypeP
      xdefW ctxT.maxS ctxT.StypeP

  let calT : Finset (ClassFunction T ℂ) := ftType34S1 baseT
  let RTop := FTtypeP_coh_base baseT.primeDade baseT.isoM
    baseT.isoG (mFT_odd T)
  have hS₁Kernel : cfConjC_subset
      (↑calT : Set (ClassFunction T ℂ))
      (FTtypePKernelLayer baseT.primeDade) := by
    refine ⟨?_, ?_⟩
    · intro zeta hzeta
      exact FTType34StructureInternal.ftType34S1_subset_kernelLayer34
        baseT (by simpa only [calT] using hzeta)
    · intro zeta hzeta
      exact (FTType34StructureInternal.ftType34S1_cfConjC_subset34
        baseT).2 zeta (by simpa only [calT] using hzeta)
  have hsubTop : subcoherent
      (↑calT : Set (ClassFunction T ℂ))
      (Dade baseT.primeDade.prDade_hyp) RTop := by
    exact subset_subcoherent
      (FTtypeP_subcoherent baseT.primeDade baseT.isoM baseT.isoG
        (mFT_odd T)) hS₁Kernel
  have hcoherentTop : coherent
      (↑calT : Set (ClassFunction T ℂ))
      (nonidentitySet T) (Dade baseT.primeDade.prDade_hyp) := by
    apply uniform_degree_coherence hsubTop
    intro chi hchi psi hpsi
    exact
      (FTType34StructureInternal.ftType34S1_degree34 baseT chi
        (by simpa only [calT, Finset.mem_coe] using hchi)).trans
      (FTType34StructureInternal.ftType34S1_degree34 baseT psi
        (by simpa only [calT, Finset.mem_coe] using hpsi)).symm
  obtain ⟨tauTop, hcohTop⟩ := hcoherentTop
  let tau₁T : ClassFunction T ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    baseT.targetMap.comp tauTop
  have hcohT : coherent_with
      (↑calT : Set (ClassFunction T ℂ))
      (nonidentitySet T) baseT.tau tau₁T := by
    refine
      { isometry := ?_
        mapsToVirtual := ?_
        agrees := ?_ }
    · intro phi hphi psi hpsi
      change characterPairing (baseT.targetMap (tauTop phi))
          (baseT.targetMap (tauTop psi)) = characterPairing phi psi
      exact (baseT.targetMap_pairing (tauTop phi) (tauTop psi)).trans
        (hcohTop.isometry phi hphi psi hpsi)
    · intro phi hphi
      change ClassFunction.IsVirtual (baseT.targetMap (tauTop phi))
      exact baseT.targetMap_virtual (hcohTop.mapsToVirtual phi hphi)
    · intro phi hphi hsupp
      change baseT.targetMap (tauTop phi) =
        baseT.targetMap (Dade baseT.primeDade.prDade_hyp phi)
      exact congrArg baseT.targetMap (hcohTop.agrees phi hphi hsupp)

  have hetaSwap (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      ctxS.eta i j = ctxT.eta j i := by
    have hswap := CyclicTIHypothesis.cycTIisoC defW xdefW
      ctxS.primeDade.prDade_cycTI
      ctxT.primeDade.prDade_cycTI i j
    have hmapped := congrArg ctxS.targetMap hswap
    simpa only [FTTypePSetupContext.eta,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible,
      CyclicTIHypothesis.cyclicTIIsometry] using hmapped

  have hTauEtaT (zeta : ClassFunction T ℂ) (hzeta : zeta ∈ calT)
      (i : IrreducibleCharacter W₂ ℂ)
      (j : IrreducibleCharacter W₁ ℂ) :
      characterPairing (tau₁T zeta) (ctxT.eta i j) = 0 := by
    have htop := coherent_ortho_cycTIiso
      baseT.primeDade baseT.isoM baseT.isoG (mFT_odd T)
      hS₁Kernel hcohTop
      (by simpa only [calT, Finset.mem_coe] using hzeta)
      (FTType34StructureInternal.ftType34S1_irreducible34 baseT zeta
        (by simpa only [calT] using hzeta))
      (IrreducibleCharacter.cyclicTICharacter xdefW i j)
    change characterPairing (baseT.targetMap (tauTop zeta))
      (baseT.targetMap (baseT.isoG.cyclicTIImage (i, j))) = 0
    rw [baseT.targetMap_pairing]
    simpa only [CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using htop
  have hTauEtaS (zeta : ClassFunction T ℂ) (hzeta : zeta ∈ calT)
      (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      characterPairing (tau₁T zeta) (ctxS.eta i j) = 0 := by
    rw [hetaSwap i j]
    exact hTauEtaT zeta hzeta j i

  have hsourcePair (psi : ClassFunction T ℂ) (hpsi : psi ∈ calT)
      (xi : ClassFunction T ℂ) (hxi : xi ∈ calT) :
      characterPairing psi xi = if psi = xi then 1 else 0 := by
    by_cases hEq : psi = xi
    · subst xi
      rw [if_pos rfl]
      let psiIrr : IrreducibleCharacter T ℂ :=
        ⟨psi, FTType34StructureInternal.ftType34S1_irreducible34
          baseT psi (by simpa only [calT] using hpsi)⟩
      simpa only [psiIrr] using psiIrr.characterPairing_self
    · rw [if_neg hEq]
      exact seqInd_ortho baseT.HUInM
        (by simpa only [calT, ftType34S1, ftType34Layer, seqIndD] using hpsi)
        (by simpa only [calT, ftType34S1, ftType34Layer, seqIndD] using hxi)
        hEq
  have htauInj : Set.InjOn tau₁T
      (↑calT : Set (ClassFunction T ℂ)) := by
    intro psi hpsi xi hxi heq
    by_contra hne
    have hcross := hcohT.isometry psi
      (AddSubgroup.subset_closure hpsi) xi
      (AddSubgroup.subset_closure hxi)
    have hself := hcohT.isometry xi
      (AddSubgroup.subset_closure hxi) xi
      (AddSubgroup.subset_closure hxi)
    rw [heq, hsourcePair psi hpsi xi hxi, if_neg hne] at hcross
    rw [hself, hsourcePair xi hxi xi hxi, if_pos rfl] at hcross
    exact one_ne_zero hcross
  have hfamilyVirtual : ∀ alpha ∈ calT.image tau₁T,
      ClassFunction.IsVirtual alpha := by
    intro alpha halpha
    rcases Finset.mem_image.mp halpha with ⟨psi, hpsi, rfl⟩
    exact hcohT.mapsToVirtual psi (AddSubgroup.subset_closure hpsi)
  have hfamilyOrthonormal : ∀ alpha ∈ calT.image tau₁T,
      ∀ gamma ∈ calT.image tau₁T,
        characterPairing alpha gamma =
          if alpha = gamma then 1 else 0 := by
    intro alpha halpha gamma hgamma
    rcases Finset.mem_image.mp halpha with ⟨psi, hpsi, rfl⟩
    rcases Finset.mem_image.mp hgamma with ⟨xi, hxi, rfl⟩
    rw [hcohT.isometry psi (AddSubgroup.subset_closure hpsi)
      xi (AddSubgroup.subset_closure hxi),
      hsourcePair psi hpsi xi hxi]
    by_cases hEq : psi = xi
    · rw [if_pos hEq, if_pos (congrArg tau₁T hEq)]
    · rw [if_neg hEq,
        if_neg (fun h ↦ hEq (htauInj hpsi hxi h))]

  obtain ⟨⟨hbridgeA, hbridgeCore⟩, _hbridgeNorm,
      ⟨hgap, hGammaOne, hGammaReal⟩,
      hGammaBound, hdivS⟩ := FTtypeP_bridge_facts ctxS
  let Gamma : ClassFunction G ℂ := FTtypeP_bridge_gap ctxS
  letI : IsCyclic W₂ := ctxS.primeTI.fixed_cyclic
  obtain ⟨j₀, hj₀⟩ :=
    IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctxS.primeTI.prime_cycTIhyp.one_lt_card_right
  let oneG : ClassFunction G ℂ :=
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)
  have hgapG (j : IrreducibleCharacter W₂ ℂ)
      (hj : j ≠ IrreducibleCharacter.trivial) :
      ctxS.tau (FTtypeP_bridge ctxS j) - oneG +
          ctxS.eta IrreducibleCharacter.trivial j = Gamma := by
    apply ClassFunction.ext
    intro x
    have hx := congrArg (fun f : ClassFunction G ℂ => f x) (hgap j hj)
    simpa [Gamma, oneG] using hx
  have hGammaOneG : characterPairing Gamma oneG = 0 := by
    simpa [Gamma, oneG, characterPairing] using hGammaOne

  have hirrVirtual {Q : Type} [Group Q] [Fintype Q]
      (chi : IrreducibleCharacter Q ℂ) :
      ClassFunction.IsVirtual (chi : ClassFunction Q ℂ) := by
    refine ⟨Finsupp.single chi 1, ?_⟩
    simp
  have honeVirtual : ClassFunction.IsVirtual oneG := by
    dsimp only [oneG]
    exact hirrVirtual
      (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ)
  have hetaVirtual (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      ClassFunction.IsVirtual (ctxS.eta i j) := by
    obtain ⟨chiTop, epsilon, _hepsilon, himage⟩ :=
      ctxS.isoG.cyclicTIImage_eq_signed_irreducible (i, j)
    have htop : ClassFunction.IsVirtual
        (ctxS.isoG.cyclicTIImage (i, j)) := by
      refine ⟨Finsupp.single chiTop epsilon, ?_⟩
      rw [VirtualCharacter.realize_single]
      exact himage.symm
    simpa only [FTTypePSetupContext.eta] using
      baseT.targetMap_virtual htop
  have hinduceTrivialVirtual (H : Subgroup S) :
      ClassFunction.IsVirtual
        (ClassFunction.induce H
          ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
            ClassFunction H ℂ)) := by
    let z : VirtualCharacter H ℂ :=
      Finsupp.single
        (IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) 1
    refine ⟨VirtualCharacter.induce H z, ?_⟩
    simpa only [z, VirtualCharacter.realize_induce,
      VirtualCharacter.realize_single, Int.cast_one, one_smul]
  have hbridgeVirtual :
      ClassFunction.IsVirtual (FTtypeP_bridge ctxS j₀) := by
    rw [FTtypeP_bridge]
    apply ClassFunction.IsVirtual.sub
    · exact hinduceTrivialVirtual _
    · simpa only [PrimeTIHypothesis.primeTICharacter] using
        hirrVirtual (ctxS.primeTI.primeTIIndex ctxS.isoS
          (IrreducibleCharacter.trivial, j₀))
  have htauBridgeVirtual : ClassFunction.IsVirtual
      (ctxS.tau (FTtypeP_bridge ctxS j₀)) := by
    obtain ⟨z, hz⟩ := hbridgeVirtual
    have hsourceSupport : VirtualCharacter.realize z ∈
        ClassFunction.supportedOn
          {x : S | (x : G) ∈ FTsupport0 S} := by
      rw [hz]
      change FTtypeP_bridge ctxS j₀ ∈
        ClassFunction.supportedOn
          {x : S | (x : G) ∈ FTsupport0 S}
      exact hbridgeA j₀ hj₀
    have hdade := Dade_vchar (FT_Dade0_hyp S ctxS.maxS)
      z hsourceSupport
    have hdadeVirtual : ClassFunction.IsVirtual
        (Dade (FT_Dade0_hyp S ctxS.maxS)
          (FTtypeP_bridge ctxS j₀)) := by
      refine ⟨Dade_virtualCharacter (FT_Dade0_hyp S ctxS.maxS) z, ?_⟩
      calc
        VirtualCharacter.realize
            (Dade_virtualCharacter (FT_Dade0_hyp S ctxS.maxS) z) =
            Dade (FT_Dade0_hyp S ctxS.maxS)
              (VirtualCharacter.realize z) := hdade.symm
        _ = Dade (FT_Dade0_hyp S ctxS.maxS)
              (FTtypeP_bridge ctxS j₀) := congrArg _ hz
    simpa only [FTTypePSetupContext.tau, LinearMap.comp_apply] using
      baseT.targetMap_virtual hdadeVirtual
  have hGammaVirtual : ClassFunction.IsVirtual Gamma := by
    rw [← hgapG j₀ hj₀]
    exact (htauBridgeVirtual.sub honeVirtual).add
      (hetaVirtual IrreducibleCharacter.trivial j₀)

  /- The following is the literal parity subargument of Coq (14.9).
  Everything except the one cross-support pairing is expressible through
  current public endpoints; keeping it local makes the remaining API gap
  explicit. -/
  have hGammaCoefficient : ∀ zeta ∈ calT,
      characterPairing Gamma (tau₁T zeta) ≠ 0 := by
    intro zeta hzeta
    let etaT (i : IrreducibleCharacter W₂ ℂ)
        (j : IrreducibleCharacter W₁ ℂ) : ClassFunction G ℂ :=
      baseT.targetMap (baseT.isoG.cyclicTIImage (i, j))
    let muZeroT : ClassFunction T ℂ :=
      baseT.primeTI.primeTIRed baseT.isoM
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
    let betaT : ClassFunction T ℂ := muZeroT - zeta
    let etaZeroRowT : ClassFunction G ℂ :=
      ∑ j : IrreducibleCharacter W₁ ℂ,
        etaT (IrreducibleCharacter.trivial :
          IrreducibleCharacter W₂ ℂ) j
    have hzetaS1 : zeta ∈ ftType34S1 baseT := by
      simpa only [calT] using hzeta
    have hzetaSet : zeta ∈
        (↑calT : Set (ClassFunction T ℂ)) := by
      simpa only [Finset.mem_coe] using hzeta
    have hprojection (i : IrreducibleCharacter W₂ ℂ)
        (j : IrreducibleCharacter W₁ ℂ) :
        characterPairing (baseT.tau betaT - etaZeroRowT)
          (etaT i j) = 0 := by
      simpa only [betaT, muZeroT, etaZeroRowT, etaT] using
        h34.1 zeta hzetaS1 i j
    have hetaPair (i k : IrreducibleCharacter W₂ ℂ)
        (j ell : IrreducibleCharacter W₁ ℂ) :
        characterPairing (etaT i j) (etaT k ell) =
          if (i, j) = (k, ell) then 1 else 0 := by
      calc
        characterPairing (etaT i j) (etaT k ell) =
            characterPairing
              (baseT.isoG.cyclicTIImage (i, j))
              (baseT.isoG.cyclicTIImage (k, ell)) := by
          dsimp only [etaT]
          exact baseT.targetMap_pairing _ _
        _ = if (i, j) = (k, ell) then 1 else 0 :=
          baseT.isoG.characterPairing_cyclicTIImage (i, j) (k, ell)
    have hrowPair (i : IrreducibleCharacter W₂ ℂ)
        (j : IrreducibleCharacter W₁ ℂ) :
        characterPairing etaZeroRowT (etaT i j) =
          if i = IrreducibleCharacter.trivial then 1 else 0 := by
      dsimp only [etaZeroRowT]
      change characterPairingRight (etaT i j)
          (∑ k : IrreducibleCharacter W₁ ℂ,
            etaT IrreducibleCharacter.trivial k) = _
      rw [map_sum]
      by_cases hi : i = IrreducibleCharacter.trivial
      · subst i
        rw [if_pos rfl, Finset.sum_eq_single j]
        · change characterPairing
            (etaT IrreducibleCharacter.trivial j)
            (etaT IrreducibleCharacter.trivial j) = 1
          rw [hetaPair, if_pos rfl]
        · intro k _ hkj
          change characterPairing
            (etaT IrreducibleCharacter.trivial k)
            (etaT IrreducibleCharacter.trivial j) = 0
          rw [hetaPair, if_neg]
          exact fun h ↦ hkj (congrArg Prod.snd h)
        · simp
      · rw [if_neg hi]
        apply Finset.sum_eq_zero
        intro k _
        change characterPairing
          (etaT IrreducibleCharacter.trivial k) (etaT i j) = 0
        rw [hetaPair, if_neg]
        exact fun h ↦ hi (congrArg Prod.fst h).symm
    have htauBetaEta (i : IrreducibleCharacter W₂ ℂ)
        (j : IrreducibleCharacter W₁ ℂ) :
        characterPairing (baseT.tau betaT) (etaT i j) =
          if i = IrreducibleCharacter.trivial then 1 else 0 := by
      have hp := hprojection i j
      change characterPairingRight (etaT i j)
        (baseT.tau betaT - etaZeroRowT) = 0 at hp
      rw [map_sub] at hp
      change characterPairing (baseT.tau betaT) (etaT i j) -
        characterPairing etaZeroRowT (etaT i j) = 0 at hp
      rw [hrowPair i j] at hp
      exact sub_eq_zero.mp hp

    let K : Subgroup T :=
      FTType345ConstantsInternal.ftType345DerivedInM T
    letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 T
    have hzetaLayer : zeta ∈ seqIndD (k := ℂ) baseT.HUInM
        (⊤ : Subgroup baseT.HUInM) baseT.HCInHU := by
      simpa only [ftType34S1, ftType34Layer] using hzetaS1
    have hderived : baseT.HU = derivedWithin T := by
      calc
        baseT.HU = FTcore T := baseT.FTcore_eq_HU.symm
        _ = derivedWithin T :=
          FTcore_type_gt2 T baseT.type_gt_two
    have hKbase : baseT.HUInM =
        FTType345ConstantsInternal.ftType345DerivedInM T := by
      simp only [FTType34Base.HUInM,
        FTType345ConstantsInternal.ftType345DerivedInM, hderived]
    have hzetaRefMem : zeta ∈
        FTType345ConstantsInternal.ftType345InducedFamily10 T := by
      rw [FTType345ConstantsInternal.ftType345InducedFamily10, ← hKbase]
      exact seqIndS baseT.HUInM
        (Iirr_kerDS (k := ℂ)
          (bot_le : (⊥ : Subgroup baseT.HUInM) ≤ baseT.HCInHU)
          (le_rfl : (⊤ : Subgroup baseT.HUInM) ≤ ⊤)) hzetaLayer
    let hzetaRef : FTType345ReferenceChoice T W₂ zeta :=
      { irreducible :=
          FTType34StructureInternal.ftType34S1_irreducible34
            baseT zeta hzetaS1
        mem_calS := hzetaRefMem
        degree :=
          FTType34StructureInternal.ftType34S1_degree34
            baseT zeta hzetaS1 }
    have hKindex : K.index = Nat.card W₂ := by
      have houter : IsInternalSemidirectProductIn
          (derivedWithin T) W₂ T := baseT.MtypeP.1.2.2.2
      calc
        K.index = Nat.card (W₂.subgroupOf T) :=
          houter.2.2.2.symm.index_eq_card
        _ = Nat.card W₂ :=
          MathlibSupport.natCard_subgroupOf_eq houter.2.1
    have hbetaTDerived : betaT ∈ ClassFunction.supportedOn
        (subgroupNonidentity K) := by
      have hsmall := cfInd1_sub_lin_on (k := ℂ) K
        hzetaRef.mem_calS (by rw [hzetaRef.degree, hKindex])
      rw [← baseT.primeTI.prTIred0 baseT.isoM] at hsmall
      simpa only [betaT, muZeroT] using hsmall
    have hbetaTSupport : betaT ∈ ClassFunction.supportedOn
        {x : T | (x : G) ∈ FTsupport0 T} := by
      rw [ClassFunction.mem_supportedOn_iff] at hbetaTDerived ⊢
      intro x hx
      apply hbetaTDerived x
      intro hxK
      apply hx
      apply FTsupp1_sub0 baseT.maxM
      rw [FTsupp1_type_gt2 T baseT.type_gt_two]
      exact ⟨hxK.1, fun hxOne ↦ hxK.2 (Subtype.ext hxOne)⟩
    have hbetaTVirtual : ClassFunction.IsVirtual betaT := by
      have hmuZeroVirtual : ClassFunction.IsVirtual muZeroT := by
        dsimp only [muZeroT]
        exact (baseT.primeTI.prTIred_char baseT.isoM
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₁ ℂ)).isVirtual
      have hzetaVirtual : ClassFunction.IsVirtual zeta := by
        refine ⟨Finsupp.single
          (⟨zeta, hzetaRef.irreducible⟩ :
            IrreducibleCharacter T ℂ) 1, ?_⟩
        simp
      exact hmuZeroVirtual.sub hzetaVirtual
    have hDadeBetaVirtual : ClassFunction.IsVirtual
        (Dade baseT.primeDade.prDade_hyp betaT) := by
      obtain ⟨z, hz⟩ := hbetaTVirtual
      obtain ⟨beta, hbeta, _⟩ :=
        (Dade_Zisometry baseT.primeDade.prDade_hyp).2 z
          (by simpa only [hz] using hbetaTSupport)
      exact ⟨beta, by simpa only [hz] using hbeta.symm⟩

    let oneTop : ClassFunction (⊤ : Subgroup G) ℂ :=
      ((IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
          ClassFunction (⊤ : Subgroup G) ℂ)
    let deltaTop : ClassFunction (⊤ : Subgroup G) ℂ :=
      Dade baseT.primeDade.prDade_hyp betaT - oneTop + tauTop zeta
    let Delta : ClassFunction G ℂ := baseT.targetMap deltaTop
    have honeTopVirtual : ClassFunction.IsVirtual oneTop :=
      hirrVirtual (IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ)
    have htauZetaVirtual : ClassFunction.IsVirtual (tauTop zeta) :=
      hcohTop.mapsToVirtual zeta
        (AddSubgroup.subset_closure hzetaSet)
    have hdeltaTopVirtual : ClassFunction.IsVirtual deltaTop := by
      dsimp only [deltaTop]
      exact (hDadeBetaVirtual.sub honeTopVirtual).add htauZetaVirtual
    have hDeltaVirtual : ClassFunction.IsVirtual Delta :=
      baseT.targetMap_virtual hdeltaTopVirtual

    let zetaIrr : IrreducibleCharacter T ℂ :=
      ⟨zeta, FTType34StructureInternal.ftType34S1_irreducible34
        baseT zeta hzetaS1⟩
    let zetaC : IrreducibleCharacter T ℂ :=
      IrreducibleCharacter.mapRingEquiv complexConjugation zetaIrr
    have hzetaCeq : zetaC = IrreducibleCharacter.dual zetaIrr :=
      FTType1InfrastructureInternal.conjugateIrreducibleEqDual zetaIrr
    have hzetaCmem : (zetaC : ClassFunction T ℂ) ∈ calT := by
      rw [hzetaCeq, ← ClassFunction.inverseLinear_irreducible]
      simpa only [Finset.mem_coe] using hS₁Kernel.2 zeta hzetaSet
    have hdiffSpan : zeta - (zetaC : ClassFunction T ℂ) ∈
        AddSubgroup.closure
          (↑calT : Set (ClassFunction T ℂ)) :=
      (AddSubgroup.closure _).sub_mem
        (AddSubgroup.subset_closure hzetaSet)
        (AddSubgroup.subset_closure
          (by simpa only [Finset.mem_coe] using hzetaCmem))
    have hdiffOn : zeta - (zetaC : ClassFunction T ℂ) ∈
        ClassFunction.supportedOn (nonidentitySet T) := by
      rw [hzetaCeq, ← ClassFunction.inverseLinear_irreducible]
      exact FTType1InfrastructureInternal.inverseSubSupported zeta
    have hagree : tauTop (zeta - (zetaC : ClassFunction T ℂ)) =
        Dade baseT.primeDade.prDade_hyp
          (zeta - (zetaC : ClassFunction T ℂ)) :=
      hcohTop.agrees _ hdiffSpan hdiffOn
    have hconjTau : cfConjC (tauTop zeta) = tauTop zetaC := by
      simpa only [zetaIrr] using
        cfConjC_Dade_coherent baseT.primeDade.prDade_hyp
          baseT.HUInM ⊤ baseT.HCInHU hcohTop
          (mFT_odd (⊤ : Subgroup G)) zetaIrr
          hzetaLayer
    have hzetaConj : cfConjC zeta = (zetaC : ClassFunction T ℂ) := by
      change cfConjC (zetaIrr : ClassFunction T ℂ) =
        (zetaC : ClassFunction T ℂ)
      rw [cfConjC_irreducible]
    have hmuConj : cfConjC muZeroT = muZeroT := by
      have hmuVirtual :=
        (baseT.primeTI.prTIred_char baseT.isoM
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₁ ℂ)).isVirtual
      dsimp only [muZeroT]
      rw [← FTType1InfrastructureInternal.inverseEqConjOfVirtual
        hmuVirtual]
      simpa only [IrreducibleCharacter.dual_trivial] using
        baseT.primeTI.prTIred_aut baseT.isoM
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₁ ℂ)
    have hconjDadeBeta :
        cfConjC (Dade baseT.primeDade.prDade_hyp betaT) =
          Dade baseT.primeDade.prDade_hyp
            (muZeroT - (zetaC : ClassFunction T ℂ)) := by
      calc
        cfConjC (Dade baseT.primeDade.prDade_hyp betaT) =
            Dade baseT.primeDade.prDade_hyp (cfConjC betaT) :=
          (Dade_conjC baseT.primeDade.prDade_hyp betaT).symm
        _ = Dade baseT.primeDade.prDade_hyp
              (muZeroT - (zetaC : ClassFunction T ℂ)) := by
          congr 1
          dsimp only [betaT]
          rw [map_sub, hmuConj, hzetaConj]
    have honeTopConj : cfConjC oneTop = oneTop := by
      apply ClassFunction.ext
      intro x
      simp [oneTop, cfConjC_apply,
        IrreducibleCharacter.trivial_apply]
    have hconjDeltaTop : cfConjC deltaTop = deltaTop := by
      change cfConjC
          (Dade baseT.primeDade.prDade_hyp betaT - oneTop + tauTop zeta) =
        Dade baseT.primeDade.prDade_hyp betaT - oneTop + tauTop zeta
      rw [map_add, map_sub, hconjDadeBeta, honeTopConj, hconjTau]
      have hsource :
          muZeroT - (zetaC : ClassFunction T ℂ) =
            betaT + (zeta - (zetaC : ClassFunction T ℂ)) := by
        dsimp only [betaT]
        abel
      calc
        Dade baseT.primeDade.prDade_hyp
                (muZeroT - (zetaC : ClassFunction T ℂ)) - oneTop +
              tauTop zetaC =
            (Dade baseT.primeDade.prDade_hyp betaT +
                Dade baseT.primeDade.prDade_hyp
                  (zeta - (zetaC : ClassFunction T ℂ))) - oneTop +
              tauTop zetaC := by rw [← map_add, ← hsource]
        _ = (Dade baseT.primeDade.prDade_hyp betaT +
                tauTop (zeta - (zetaC : ClassFunction T ℂ))) - oneTop +
              tauTop zetaC := by rw [hagree]
        _ = Dade baseT.primeDade.prDade_hyp betaT - oneTop +
              tauTop zeta := by
          have htauSub :
              tauTop (zeta - (zetaC : ClassFunction T ℂ)) =
                tauTop zeta - tauTop (zetaC : ClassFunction T ℂ) :=
            map_sub tauTop zeta (zetaC : ClassFunction T ℂ)
          rw [htauSub]
          abel
    have hdeltaTopReal : cfReal deltaTop := by
      rw [cfReal,
        FTType1InfrastructureInternal.inverseEqConjOfVirtual
          hdeltaTopVirtual,
        hconjDeltaTop]
    have htargetInverse (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
        ClassFunction.inverseLinear (baseT.targetMap phi) =
          baseT.targetMap (ClassFunction.inverseLinear phi) := by
      ext x
      simp [ClassFunction.inverseLinear_apply,
        ClassFunction.comap_apply]
    have hDeltaReal : cfReal Delta := by
      rw [cfReal, htargetInverse, hdeltaTopReal]

    have heta00 : ctxS.eta IrreducibleCharacter.trivial
        IrreducibleCharacter.trivial = oneG := by
      change ctxS.targetMap
          (ctxS.isoG.linearMap
            (CyclicTIIsometryData.cyclicTISourceIrreducible
              (defW := defW)
              (IrreducibleCharacter.trivial,
                IrreducibleCharacter.trivial))) = _
      rw [show CyclicTIIsometryData.cyclicTISourceIrreducible
          (defW := defW)
          (IrreducibleCharacter.trivial,
            IrreducibleCharacter.trivial) =
          ((IrreducibleCharacter.trivial :
            IrreducibleCharacter W ℂ) : ClassFunction W ℂ) by
        exact congrArg
          (fun chi : IrreducibleCharacter W ℂ ↦
            (chi : ClassFunction W ℂ))
          (IrreducibleCharacter.cyclicTICharacter_trivial defW)]
      rw [ctxS.isoG.map_trivial]
      ext x
      simp [oneG, ClassFunction.comap_apply,
        IrreducibleCharacter.trivial_apply]
    have honePair : characterPairing oneG oneG = 1 := by
      simpa only [oneG] using
        IrreducibleCharacter.characterPairing_self
          (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ)
    have heta₀One : characterPairing
        (ctxS.eta IrreducibleCharacter.trivial j₀) oneG = 0 := by
      rw [← heta00,
        FTTypePCyclicRectangleInternal.characterPairing_eta, if_neg]
      intro h
      exact hj₀ (congrArg Prod.snd h)
    have hTauZetaOne : characterPairing (tau₁T zeta) oneG = 0 := by
      rw [← heta00]
      exact hTauEtaS zeta hzeta
        IrreducibleCharacter.trivial IrreducibleCharacter.trivial
    have hGammaEq : Gamma =
        ctxS.tau (FTtypeP_bridge ctxS j₀) - oneG +
          ctxS.eta IrreducibleCharacter.trivial j₀ :=
      (hgapG j₀ hj₀).symm
    have hbetaSOne : characterPairing
        (ctxS.tau (FTtypeP_bridge ctxS j₀)) oneG = 1 := by
      have h := hGammaOneG
      rw [hGammaEq] at h
      change characterPairingRight oneG
        (ctxS.tau (FTtypeP_bridge ctxS j₀) - oneG +
          ctxS.eta IrreducibleCharacter.trivial j₀) = 0 at h
      rw [map_add, map_sub] at h
      change
        characterPairing (ctxS.tau (FTtypeP_bridge ctxS j₀)) oneG -
            characterPairing oneG oneG +
          characterPairing
            (ctxS.eta IrreducibleCharacter.trivial j₀) oneG = 0 at h
      rw [honePair, heta₀One, add_zero] at h
      exact sub_eq_zero.mp h
    have htauBetaOne : characterPairing (baseT.tau betaT) oneG = 1 := by
      rw [← heta00, hetaSwap]
      simpa only [etaT, baseT, FTTypePSetupContext.eta, if_pos] using
        htauBetaEta
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
    have heta₀TauBeta : characterPairing
        (ctxS.eta IrreducibleCharacter.trivial j₀)
        (baseT.tau betaT) = 0 := by
      rw [characterPairing_comm, hetaSwap]
      simpa only [etaT, baseT, FTTypePSetupContext.eta,
        if_neg hj₀] using
        htauBetaEta j₀
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
    have heta₀TauZeta : characterPairing
        (ctxS.eta IrreducibleCharacter.trivial j₀)
        (tau₁T zeta) = 0 := by
      rw [characterPairing_comm]
      exact hTauEtaS zeta hzeta IrreducibleCharacter.trivial j₀

    have honeTarget : baseT.targetMap oneTop = oneG := by
      ext x
      simp [oneTop, oneG, ClassFunction.comap_apply,
        IrreducibleCharacter.trivial_apply]
    have hDeltaEq : Delta =
        baseT.tau betaT - oneG + tau₁T zeta := by
      dsimp only [Delta, deltaTop, tau₁T]
      rw [map_add, map_sub, honeTarget]
      simpa only [FTType34Base.tau, LinearMap.comp_apply]

    have hpairSubLeft (a b c : ClassFunction G ℂ) :
        characterPairing (a - b) c =
          characterPairing a c - characterPairing b c := by
      change characterPairingRight c (a - b) = _
      exact map_sub (characterPairingRight c) a b
    have hpairSubRight (a b c : ClassFunction G ℂ) :
        characterPairing a (b - c) =
          characterPairing a b - characterPairing a c := by
      change characterPairingLeft a (b - c) = _
      exact map_sub (characterPairingLeft a) b c

    have hcross : characterPairing
        (ctxS.tau (FTtypeP_bridge ctxS j₀))
        (baseT.tau betaT) = 0 := by
      /- Induction carries a source support to its ambient conjugacy
      saturation.  This is the local, public-API spelling of the private
      Section 13 adapter used by the analogous type-I argument. -/
      have hinduceSupport
          {L : Subgroup G} {A : Set G}
          (alpha : ClassFunction L ℂ)
          (halpha : alpha ∈
            ClassFunction.supportedOn {x : L | (x : G) ∈ A}) :
          ClassFunction.induce L alpha ∈
            ClassFunction.supportedOn
              (classSupportWithin (⊤ : Subgroup G) A) := by
        rw [ClassFunction.mem_supportedOn_iff]
        intro x hx
        rw [ClassFunction.induce_apply_formula]
        apply mul_eq_zero_of_right
        apply Finset.sum_eq_zero
        intro y _
        split_ifs with hy
        · apply ClassFunction.eq_zero_of_mem_supportedOn halpha
          intro ha
          apply hx
          exact ⟨(y⁻¹ * x * y : G), ha, y⁻¹,
            Subgroup.mem_top _, by group⟩
        · rfl

      have hbridgeA₀ : FTtypeP_bridge ctxS j₀ ∈
          ClassFunction.supportedOn (ftTypePSupport0InS S) := by
        change FTtypeP_bridge ctxS j₀ ∈
          ClassFunction.supportedOn
            {x : S | (x : G) ∈ FTsupport0 S}
        exact hbridgeA j₀ hj₀
      have htauSInduce :
          ctxS.tau (FTtypeP_bridge ctxS j₀) =
            ClassFunction.induce S (FTtypeP_bridge ctxS j₀) :=
        (FTtypeP_facts ctxS).2.2.2.2.2.2.2.2.2
          (FTtypeP_bridge ctxS j₀) hbridgeA₀
      have hbridgeCoreAmbient : FTtypeP_bridge ctxS j₀ ∈
          ClassFunction.supportedOn
            {x : S | (x : G) ∈
              subgroupNonidentity (Fitting_core S) ∪
                classSupportWithin S (cyclicTISet W W₁ W₂)} := by
        change FTtypeP_bridge ctxS j₀ ∈
          ClassFunction.supportedOn
            {x : S | (x : G) ∈
              subgroupNonidentity (Fitting_core S) ∪
                classSupportWithin S (cyclicTISet W W₁ W₂)}
        exact hbridgeCore j₀ hj₀
      have htauSSupport : ctxS.tau (FTtypeP_bridge ctxS j₀) ∈
          ClassFunction.supportedOn
            (classSupportWithin (⊤ : Subgroup G)
              (subgroupNonidentity (Fitting_core S) ∪
                classSupportWithin S (cyclicTISet W W₁ W₂))) := by
        rw [htauSInduce]
        exact hinduceSupport _ hbridgeCoreAmbient

      have hbetaA₀ : betaT ∈
          ClassFunction.supportedOn (ftTypePSupport0InS T) := by
        change betaT ∈ ClassFunction.supportedOn
          {x : T | (x : G) ∈ FTsupport0 T}
        exact hbetaTSupport
      have htauTInduce : baseT.tau betaT =
          ClassFunction.induce T betaT := by
        change ctxT.tau betaT = ClassFunction.induce T betaT
        exact (FTtypeP_facts ctxT).2.2.2.2.2.2.2.2.2
          betaT hbetaA₀
      have hbetaDerivedAmbient : betaT ∈
          ClassFunction.supportedOn
            {x : T | (x : G) ∈
              subgroupNonidentity (derivedWithin T)} := by
        rw [ClassFunction.mem_supportedOn_iff] at hbetaTDerived ⊢
        intro x hx
        apply hbetaTDerived x
        intro hxK
        apply hx
        exact ⟨hxK.1, fun hxOne ↦ hxK.2 (Subtype.ext hxOne)⟩
      have htauTSupport : baseT.tau betaT ∈
          ClassFunction.supportedOn
            (classSupportWithin (⊤ : Subgroup G)
              (subgroupNonidentity (derivedWithin T))) := by
        rw [htauTInduce]
        exact hinduceSupport _ hbetaDerivedAmbient

      /- The two saturated source supports sit in blocks of the public
      Peterfalvi 8.17 partition.  The Fitting part of the bridge sits in
      the first Dade block of S, and its cyclic part is the exceptional
      block. -/
      have hbridgeSaturation :
          classSupportWithin (⊤ : Subgroup G)
              (subgroupNonidentity (Fitting_core S) ∪
                classSupportWithin S (cyclicTISet W W₁ W₂)) ⊆
            FT_Dade1_support S ∪
              ftCyclicExceptionalSupport W W₁ W₂ := by
        rintro x ⟨a, ha, g, hg, rfl⟩
        rcases ha with haF | haW
        · apply Or.inl
          refine ⟨a, Fcore_sub_FTsupp1 ctxS.maxS haF,
            a, ?_, g, hg, rfl⟩
          exact ⟨1, (FTsignalizer S a).one_mem,
            a, Set.mem_singleton a, one_mul a⟩
        · apply Or.inr
          rcases haW with ⟨w, hw, s, hs, rfl⟩
          exact ⟨w, hw, s * g, Subgroup.mem_top _, by group⟩
      have hderivedSaturation :
          classSupportWithin (⊤ : Subgroup G)
              (subgroupNonidentity (derivedWithin T)) ⊆
            FT_Dade1_support T := by
        rintro x ⟨a, ha, g, hg, rfl⟩
        have haSupport : a ∈ FTsupport1 T := by
          rw [FTsupp1_type_gt2 T baseT.type_gt_two]
          exact ha
        refine ⟨a, haSupport, a, ?_, g, hg, rfl⟩
        exact ⟨1, (FTsignalizer T a).one_mem,
          a, Set.mem_singleton a, one_mul a⟩

      have hStype2 : FTtype S = 2 :=
        (FTtypeP_facts ctxS).2.1 hlt
      have hnotST : ¬ FTAmbientConjugate S T := by
        rintro ⟨g, hT⟩
        have htype : FTtype T = FTtype S := by
          rw [hT]
          exact FTtypeJ S g
        omega
      have hdisST : Disjoint (FT_Dade1_support S)
          (FT_Dade1_support T) :=
        FT_Dade1_support_disjoint ctxS.maxS ctxT.maxS hnotST

      /- Put T's first Dade support into the canonical transversal family;
      invariance is proved directly along the public EqvGen witness. -/
      obtain ⟨R, hRrep, hTR⟩ :=
        (mmax_transversalP (G := G)).representative ctxT.maxS
      have hsupportTR : FT_Dade1_support T = FT_Dade1_support R :=
        ftt2_dade1_support_eq_of_within_top hTR
      have hTblock : FT_Dade1_support T ∈
          ftFirstDadeSupportFamily (G := G) := by
        change FT_Dade1_support T ∈
          FT_Dade1_support '' mmax_transversal (⊤ : Subgroup G)
        exact ⟨R, hRrep, hsupportTR.symm⟩
      obtain ⟨_, _, _, _, _, hPairPartition⟩ :=
        FT_Dade_support_partition (G := G)
      have hpairPartition :=
        hPairPartition S T W W₁ W₂ defW pairST
      have hExceptionalNe :
          ftCyclicExceptionalSupport W W₁ W₂ ≠
            FT_Dade1_support T := by
        intro heq
        apply hpairPartition.2
        rw [heq]
        exact hTblock
      have hdisExceptionalT :
          Disjoint (ftCyclicExceptionalSupport W W₁ W₂)
            (FT_Dade1_support T) := by
        exact hpairPartition.1.2.1
          (Or.inl rfl) (Or.inr hTblock) hExceptionalNe
      have hdisBlocks :
          Disjoint
            (FT_Dade1_support S ∪
              ftCyclicExceptionalSupport W W₁ W₂)
            (FT_Dade1_support T) :=
        hdisST.union_left hdisExceptionalT
      have hdisSupports :
          Disjoint
            (classSupportWithin (⊤ : Subgroup G)
              (subgroupNonidentity (Fitting_core S) ∪
                classSupportWithin S (cyclicTISet W W₁ W₂)))
            (classSupportWithin (⊤ : Subgroup G)
              (subgroupNonidentity (derivedWithin T))) :=
        hdisBlocks.mono hbridgeSaturation hderivedSaturation

      have hderivedInv : IsInvStable
          (classSupportWithin (⊤ : Subgroup G)
            (subgroupNonidentity (derivedWithin T))) := by
        have hinv : ∀ x : G,
            x ∈ classSupportWithin (⊤ : Subgroup G)
                (subgroupNonidentity (derivedWithin T)) →
              x⁻¹ ∈ classSupportWithin (⊤ : Subgroup G)
                (subgroupNonidentity (derivedWithin T)) := by
          rintro x ⟨a, ha, g, hg, rfl⟩
          refine ⟨a⁻¹,
            ⟨(derivedWithin T).inv_mem ha.1, inv_ne_one.mpr ha.2⟩,
            g, hg, ?_⟩
          group
        intro x
        constructor
        · intro hx
          simpa only [inv_inv] using hinv x⁻¹ hx
        · exact hinv x
      exact characterPairing_eq_zero_of_disjoint_of_invStable_right
        hdisSupports hderivedInv htauSSupport htauTSupport
    have hparityRelation :
        characterPairing Gamma Delta =
          characterPairing Gamma (tau₁T zeta) - 1 := by
      rw [hGammaEq, hDeltaEq]
      simp only [characterPairing_add_left, characterPairing_add_right,
        hpairSubLeft, hpairSubRight]
      rw [hcross, hbetaSOne,
        characterPairing_comm oneG (baseT.tau betaT), htauBetaOne,
        honePair, characterPairing_comm oneG (tau₁T zeta),
        hTauZetaOne, heta₀TauBeta, heta₀One, heta₀TauZeta]
      ring
    have hEven : evenCharacterPairing Gamma Delta := by
      apply (cfdot_real_vchar_even (Q := G)
        (IsMinSimpleOddGroup.odd_card (G := G)) Gamma Delta
        ⟨hGammaVirtual, by simpa only [Gamma] using hGammaReal⟩
        ⟨hDeltaVirtual, hDeltaReal⟩).2
      left
      refine ⟨0, ?_⟩
      simpa only [Int.mul_zero, Int.cast_zero] using hGammaOneG
    obtain ⟨n, hn⟩ := hEven
    rw [hparityRelation] at hn
    have hodd : characterPairing Gamma (tau₁T zeta) =
        (((2 * n + 1 : ℤ) : ℂ)) := by
      calc
        characterPairing Gamma (tau₁T zeta) =
            (characterPairing Gamma (tau₁T zeta) - 1) + 1 := by ring
        _ = (((2 * n : ℤ) : ℂ)) + 1 := by rw [hn]
        _ = (((2 * n + 1 : ℤ) : ℂ)) := by push_cast; ring
    rw [hodd]
    exact Int.cast_ne_zero.mpr (by omega)

  obtain ⟨X, Y, hXspan, hXvirtual, hYvirtual,
      hGammaSplit, hYorth, hXY⟩ :=
    orthogonal_split_virtual (calT.image tau₁T)
      hfamilyVirtual hfamilyOrthonormal hGammaVirtual
  have hYXstar : starCharacterPairing Y X = 0 := by
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hYvirtual hXvirtual, characterPairing_comm, hXY]
  have hXcyclic : ∀ Z ∈
      (↑(FTtypePCyclicImageFamily ctxS) : Set (ClassFunction G ℂ)),
      starCharacterPairing X Z = 0 := by
    intro Z hZ
    have hZFin : Z ∈ FTtypePCyclicImageFamily ctxS := by
      simpa only [Finset.mem_coe] using hZ
    rw [FTtypePCyclicImageFamily] at hZFin
    rcases Finset.mem_image.mp hZFin with ⟨chiCF, hchiCF, rfl⟩
    rcases Finset.mem_image.mp hchiCF with ⟨chi, _hchi, rfl⟩
    obtain ⟨i, j, rfl⟩ :=
      IrreducibleCharacter.exists_cyclicTICharacter defW chi
    have hZVirtual : ClassFunction.IsVirtual (ctxS.eta i j) :=
      hetaVirtual i j
    have hclosure : ∀ {A : ClassFunction G ℂ},
        A ∈ AddSubgroup.closure
          (↑(calT.image tau₁T) : Set (ClassFunction G ℂ)) →
        starCharacterPairing A (ctxS.eta i j) = 0 := by
      intro A hA
      induction hA using AddSubgroup.closure_induction with
      | mem alpha halpha =>
          have halphaFin : alpha ∈ calT.image tau₁T := by
            simpa only [Finset.mem_coe] using halpha
          rcases Finset.mem_image.mp halphaFin with ⟨zeta, hzeta, rfl⟩
          rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
            (hcohT.mapsToVirtual zeta
              (AddSubgroup.subset_closure hzeta)) hZVirtual]
          exact hTauEtaS zeta hzeta i j
      | zero => simp
      | add a b ha hb iha ihb =>
          rw [starCharacterPairing_add_left, iha, ihb, add_zero]
      | neg a ha iha =>
          rw [← neg_one_smul ℂ, starCharacterPairing_smul_left,
            iha, mul_zero]
    exact hclosure hXspan
  have hXupper : classFunctionNormSq X ≤
      ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ)) := by
    apply hGammaBound Y X
    · simpa only [Gamma, add_comm] using hGammaSplit
    · exact hYXstar
    · exact hXcyclic
  have hXPair : ∀ alpha ∈ calT.image tau₁T,
      characterPairing X alpha ≠ 0 := by
    intro alpha halpha
    rcases Finset.mem_image.mp halpha with ⟨zeta, hzeta, rfl⟩
    have hYzero := hYorth (tau₁T zeta)
      (Finset.mem_image.mpr ⟨zeta, hzeta, rfl⟩)
    have hnonzero := hGammaCoefficient zeta hzeta
    rw [hGammaSplit, characterPairing_add_left, hYzero, add_zero] at hnonzero
    exact hnonzero
  have hfamilyLower : ((calT.image tau₁T).card : ℝ) ≤
      (characterPairing X X).re :=
    PTypeCorePairingInternal.pTypeCore_orthonormal_card_le_norm
      (calT.image tau₁T) hfamilyVirtual hfamilyOrthonormal
      hXvirtual hXPair
  have hXnorm : (characterPairing X X).re = classFunctionNormSq X := by
    calc
      (characterPairing X X).re =
          (starCharacterPairing X X).re :=
        congrArg Complex.re
          (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
            hXvirtual hXvirtual).symm
      _ = classFunctionNormSq X :=
        (classFunctionNormSq_eq_re_starCharacterPairing X).symm

  have hdivT : Nat.card W₂ ∣ Nat.card V - 1 :=
    (FTtypeP_bridge_facts ctxT).2.2.2.2
  have huT : baseT.u = Nat.card V := by
    change (baseT.C.subgroupOf V).index = Nat.card V
    rw [show baseT.C = ⊥ by
      simpa only [baseT] using FTtypeP_reg_Fcore ctxT,
      Subgroup.bot_subgroupOf, Subgroup.index_bot]
  have hconstants := FTType34StructureInternal.ftType34_constants34 baseT
  have hratio := hconstants.2.2
  rw [FTtype345_ratio, hconstants.1, hconstants.2.1, huT] at hratio
  have hcalCard : calT.card =
      (Nat.card V - 1) / Nat.card W₂ := by
    have hcast :
        ((((Nat.card V - 1) / Nat.card W₂ : ℕ) : ℂ)) =
          ((calT.card : ℕ) : ℂ) := by
      rw [Nat.cast_div_charZero hdivT,
        Nat.cast_sub (Nat.card_pos : 0 < Nat.card V)]
      simpa only [calT, Nat.cast_one, Int.cast_one] using hratio
    exact_mod_cast hcast.symm
  have hImageCard : (calT.image tau₁T).card = calT.card :=
    Finset.card_image_iff.mpr htauInj
  have hreverse :
      (Nat.card V - 1) / Nat.card W₂ ≤
        (Nat.card U - 1) / Nat.card W₁ := by
    have hreal :
        ((((Nat.card V - 1) / Nat.card W₂ : ℕ) : ℝ)) ≤
          ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ)) := by
      rw [← hcalCard, ← hImageCard]
      exact hfamilyLower.trans (hXnorm.le.trans hXupper)
    exact_mod_cast hreal
  omega


set_option maxHeartbeats 2000000 in
/-- Peterfalvi (14.15): the type-II exceptional configuration is impossible. -/
theorem FTtype2_exclusion
    {S T U V W W₁ W₂ L M : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (hlt : Nat.card W₁ < Nat.card W₂)
    (maxNU_L : L ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (U : Set G) : Set G))
    (maxL : L ∈ minSimple_max_groups (G := G))
    (sNUL : Subgroup.normalizer (U : Set G) ≤ L)
    (sUH : U ≤ Fitting_core L)
    (frobL : FTFrobeniusWithFittingKernel L)
    (Ltype1 : FTtype L = 1)
    (tau₁L : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (phi : ClassFunction L ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁L)
    (Lphi : phi ∈ FTType1SeqIndFamily L)
    (phi1 : phi 1 = (FTtype1CoreIndex L : ℂ))
    (maxNV_M : M ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (V : Set G) : Set G))
    (maxM : M ∈ minSimple_max_groups (G := G))
    (sNVM : Subgroup.normalizer (V : Set G) ≤ M)
    (frobM : FTFrobeniusWithFittingKernel M)
    (Mtype1 : FTtype M = 1)
    (tau₁M : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (psi : ClassFunction M ℂ)
    (cohM : coherent_with
      (↑(FTType1SeqIndFamily M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (FTtype1Dade M maxM) tau₁M)
    (Mpsi : psi ∈ FTType1SeqIndFamily M)
    (psi1 : psi 1 = (FTtype1CoreIndex M : ℂ)) :
    False := by
  classical
  letI : Invertible (Nat.card M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let pairTS : typeP_pair T S W W₂ W₁ xdefW :=
    typeP_pair_sym S T W W₁ W₂ defW xdefW pairST
  have Stype2 : FTtype S = 2 :=
    FTtypeP_max_typeII ctxS hlt
  have Ttype2 : FTtype T = 2 :=
    FTtypeP_min_typeII ctxS ctxT hlt
  have hFactsS := FTtypeP_facts ctxS
  have hFactsT := FTtypeP_facts ctxT
  have hPrimeS : ctxS.q.Prime ∧ ctxS.p.Prime :=
    FTtypeP_primes S U W W₁ W₂ defW ctxS.maxS ctxS.StypeP
  have hPrimeCasesS := FTtypeP_primes_mod_cases ctxS
  have hFcoreKernelS : ctxS.H0 = ⊥ :=
    Ptype_Fcore_kernel_trivial ctxS
  have hFcomplKernelS : Ptype_Fcompl_kernel ctxS.ptypeCtx = ⊥ :=
    Ptype_Fcompl_kernel_trivial ctxS
  have hActionKernelS : ctxS.D.C = ⊥ := by
    apply (Subgroup.map_eq_bot_iff_of_injective
      ctxS.D.C U.subtype_injective).mp
    change (ptypeFCoreAction ctxS.ptypeCtx).ker.map U.subtype = ⊥
    simpa only [Ptype_Fcompl_kernel] using hFcomplKernelS
  have hSdprodS := Ptype_Fcore_sdprod ctxS.ptypeCtx
  have hCoprimeS := Ptype_Fcore_coprime ctxS.ptypeCtx
  have hCentCoreS : centralizerWithin (Fitting_core S) W₁ = W₂ :=
    typeP_cent_core_compl S U W W₁ W₂ defW ctxS.StypeP
  have hFactorPrimeS : ptypeFactorPrime ctxS.ptypeCtx = ctxS.p :=
    Ptype_factor_prime ctxS
  have hNonGaloisFactsS :
      ¬ ctxS.galoisAlternative →
        ctxS.q = 3 ∧ Nat.card U = ((ctxS.p - 1) / 2) ^ 2 :=
    FTtypeP_nonGalois_facts ctxS
  have hGaloisCardS := card_FTtypeP_Galois_compl ctxS
  have nonGaloisSData :
      ∀ hnot : ¬ ctxS.galoisAlternative,
        TypePGaloisNonConclusion ctxS.D :=
    fun hnot ↦ typeP_Galois_Pn ctxS.actionHypotheses hnot
  have galoisSData :
      ∀ hgal : ctxS.galoisAlternative,
        TypePGaloisConclusion ctxS.D :=
    fun hgal ↦ typeP_Galois_P ctxS.actionHypotheses hgal

  obtain ⟨hGalT, hCardVnUSwapped⟩ :=
    ftt2_galois_card_of_swapped_lt ctxT (by simpa only using hlt)
  have hUV :
      (Nat.card U - 1) / Nat.card W₁ <
        (Nat.card V - 1) / Nat.card W₂ :=
    ftt2_forward_gap ctxS ctxT hlt
  obtain ⟨y, hyQ, defLy⟩ :=
    ftt2_forced_join_L ctxS pairST hlt Stype2 maxNU_L maxL
      sNUL sUH Ltype1 tau₁L phi cohL Lphi phi1
  have indexLH : FTtype1CoreIndex L =
      Nat.card W₂ * Nat.card W₁ :=
    ftt2_index_of_join_L ctxS ctxT pairST hyQ defLy

  have hGalS : ctxS.galoisAlternative := by
    by_contra hnot
    obtain ⟨hq3, hUcard⟩ := hNonGaloisFactsS hnot
    have hDq : ctxS.D.q = 3 :=
      ctxS.D.card_W₁.symm.trans
        (by simpa only [FTTypePSetupContext.q] using hq3)
    have hDqPred : ctxS.D.q - 1 = 2 := by omega
    let data : TypePGaloisNonConclusion ctxS.D := nonGaloisSData hnot
    let a : ℕ :=
      (pointwiseActionKernel ctxS.D.U_action data.H₁).index
    let b : ℕ := (ctxS.p - 1) / 2
    have hpOdd : Odd ctxS.p := by
      change Odd (Nat.card W₂)
      exact mFT_odd W₂
    have hpThree : 3 ≤ ctxS.p := hPrimeS.2.odd_iff.mp hpOdd
    have haOne : 1 < a := by
      simpa only [a] using data.index_gt_one
    letI : NeZero a := ⟨by omega⟩
    let K := pointwiseActionKernel ctxS.D.U_action data.H₁
    have haOdd : Odd a := by
      have hKodd : Odd K.index :=
        (mFT_odd U).of_dvd_nat K.index_dvd_card
      simpa only [a, K] using hKodd
    have hDp : ctxS.D.p = ctxS.p :=
      (Ptype_factor_action_p ctxS.ptypeCtx ctxS.factorFacts).trans
        hFactorPrimeS
    have haPred : a ∣ ctxS.p - 1 := by
      simpa only [a, hDp] using data.index_dvd_prime_pred
    obtain ⟨k, hk⟩ := haPred
    have hpPredEven : Even (ctxS.p - 1) :=
      Nat.Odd.sub_odd hpOdd odd_one
    have hkEven : 2 ∣ k := by
      have htwo : 2 ∣ a * k := by
        rw [← hk]
        exact even_iff_two_dvd.mp hpPredEven
      exact haOdd.coprime_two_right.symm.dvd_of_dvd_mul_left htwo
    obtain ⟨j, hj⟩ := hkEven
    have htwoDvd : 2 ∣ ctxS.p - 1 := even_iff_two_dvd.mp hpPredEven
    have haHalf : a ∣ b := by
      refine ⟨j, ?_⟩
      apply Nat.eq_of_mul_eq_mul_left (by decide : 0 < 2)
      calc
        2 * b = ctxS.p - 1 := by
          dsimp only [b]
          exact Nat.mul_div_cancel' htwoDvd
        _ = a * k := hk
        _ = 2 * (a * j) := by rw [hj]; ring
    have hbPos : 0 < b := by dsimp only [b]; omega
    have habLe : a ≤ b := Nat.le_of_dvd hbPos haHalf

    letI : ctxS.D.C.Normal := ctxS.D.C_normal
    obtain ⟨iota, hiota⟩ := data.complement_factor_vector
    let qC : U →* U ⧸ ctxS.D.C := QuotientGroup.mk' ctxS.D.C
    have hqCinj : Function.Injective qC := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hActionKernelS
    let eC : U ≃* U ⧸ ctxS.D.C :=
      MulEquiv.ofBijective qC
        ⟨hqCinj, QuotientGroup.mk'_surjective ctxS.D.C⟩
    let f : U →* Multiplicative
        (Fin (ctxS.D.q - 1) → ZMod a) :=
      iota.comp eC.toMonoidHom
    have hfinj : Function.Injective f := hiota.comp eC.injective
    have htargetCard : Nat.card (Multiplicative
        (Fin (ctxS.D.q - 1) → ZMod a)) = a ^ 2 := by
      rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
        Nat.card_fin, Nat.card_zmod]
      exact congrArg (fun n : ℕ ↦ a ^ n) hDqPred
    have hsquareLe : b ^ 2 ≤ a ^ 2 := by
      rw [← hUcard, ← htargetCard]
      exact Nat.card_le_card_of_injective f hfinj
    have hbaLe : b ≤ a := by nlinarith
    have hab : a = b := Nat.le_antisymm habLe hbaLe
    have hcardEq : Nat.card U = Nat.card (Multiplicative
        (Fin (ctxS.D.q - 1) → ZMod a)) := by
      rw [hUcard, htargetCard, hab]
    have hfbij : Function.Bijective f :=
      (Nat.bijective_iff_injective_and_card f).2 ⟨hfinj, hcardEq⟩
    let eU : U ≃* Multiplicative
        (Fin (ctxS.D.q - 1) → ZMod a) :=
      MulEquiv.ofBijective f hfbij
    let e₂ : Multiplicative (Fin 2 → ZMod a) ≃*
        Multiplicative (ZMod a) × Multiplicative (ZMod a) :=
      (AddEquiv.toMultiplicative
        (RingEquiv.piFinTwo (fun _ : Fin 2 ↦ ZMod a)).toAddEquiv).trans
          (MulEquiv.prodMultiplicative (ZMod a) (ZMod a))
    have hUmeta : IsMetacyclic U := by
      have hprod : IsMetacyclic
          (Multiplicative (ZMod a) × Multiplicative (ZMod a)) :=
        isMetacyclic_prod_of_isCyclic (by infer_instance) (by infer_instance)
      have hvec2 : IsMetacyclic (Multiplicative (Fin 2 → ZMod a)) :=
        isMetacyclic_of_mulEquiv _ e₂ hprod
      have htarget : IsMetacyclic (Multiplicative
          (Fin (ctxS.D.q - 1) → ZMod a)) := by
        rw [hDqPred]
        exact hvec2
      exact isMetacyclic_of_mulEquiv U eU htarget
    have hUncyc : ¬ IsCyclic U := by
      intro hUcyc
      have htargetCyc : IsCyclic (Multiplicative
          (Fin (ctxS.D.q - 1) → ZMod a)) := eU.isCyclic.mp hUcyc
      have hvec2Cyc : IsCyclic (Multiplicative (Fin 2 → ZMod a)) := by
        rw [← hDqPred]
        exact htargetCyc
      have hprodCyc : IsCyclic
          (Multiplicative (ZMod a) × Multiplicative (ZMod a)) :=
        e₂.isCyclic.mp hvec2Cyc
      letI : IsCyclic
          (Multiplicative (ZMod a) × Multiplicative (ZMod a)) := hprodCyc
      letI : Finite (Multiplicative (ZMod a)) :=
        Finite.of_equiv (ZMod a) Multiplicative.ofAdd
      have hcop := coprime_card_of_isCyclic_prod
        (Multiplicative (ZMod a)) (Multiplicative (ZMod a))
      have haa : Nat.Coprime a a := by
        simpa only [Nat.card_congr Multiplicative.toAdd,
          Nat.card_zmod] using hcop
      exact haOne.ne' ((Nat.coprime_self a).mp haa)

    obtain ⟨r, hr, R₀, hR₀ncyc⟩ :
        ∃ r : ℕ, r.Prime ∧ ∃ R₀ : Sylow r U, ¬ IsCyclic R₀ := by
      by_contra hall
      push_neg at hall
      letI : IsZGroup U := ⟨fun r hr R ↦ hall r hr R⟩
      letI : Group.IsNilpotent U := ctxS.StypeP.2.1.1
      exact hUncyc (by infer_instance)
    letI : Fact r.Prime := ⟨hr⟩
    have hR₀ne : (R₀ : Subgroup U) ≠ ⊥ := by
      intro hbot
      apply hR₀ncyc
      rw [show (R₀ : Subgroup U) = ⊥ from hbot]
      infer_instance
    have hrR₀ : r ∣ Nat.card R₀ :=
      R₀.isPGroup'.card_eq_or_dvd.resolve_left
        ((R₀ : Subgroup U).one_lt_card_iff_ne_bot.mpr hR₀ne).ne'
    have hrU : r ∣ Nat.card U :=
      hrR₀.trans (R₀ : Subgroup U).card_subgroup_dvd_card
    have hrB : r ∣ b := by
      apply hr.dvd_of_dvd_pow
      simpa only [hUcard] using hrU
    have hrLeB : r ≤ b := Nat.le_of_dvd hbPos hrB
    have hrLtP : r < ctxS.p := by omega
    have hrOdd : Odd r := (mFT_odd U).of_dvd_nat hrU
    have hR₀meta : IsMetacyclic R₀ :=
      isMetacyclic_subgroup hUmeta (R₀ : Subgroup U)

    obtain ⟨_, _, hFrobUW₁, hUcomm, _, _, _, _, hTIS, _⟩ := hFactsS
    letI : IsMulCommutative U := hUcomm
    have hUS : U ≤ S := le_sup_left.trans hSdprodS.2.1
    let J : Subgroup G := U ⊔ W₁
    have hUJ : U ≤ J := le_sup_left
    have hJS : J ≤ S := hSdprodS.2.1
    have hUHallS : IsHall (primeSupport (Nat.card U))
        (U.subgroupOf S) := by
      have hUHallJ : IsHall (primeSupport (Nat.card U))
          (U.subgroupOf J) := by
        have hcop : (Nat.card (U.subgroupOf J)).Coprime
            (U.subgroupOf J).index := by
          rw [hFrobUW₁.isComplement.symm.index_eq_card]
          exact IsFrobeniusDecomposition.natCard_coprime hFrobUW₁
        simpa only [MathlibSupport.natCard_subgroupOf_eq hUJ] using
          isHall_primeSupport (U.subgroupOf J) hcop
      have hJHallS : IsHall (primeSupport (Nat.card J))
          (J.subgroupOf S) := by
        have hcop : (Nat.card (J.subgroupOf S)).Coprime
            (J.subgroupOf S).index := by
          rw [MathlibSupport.natCard_subgroupOf_eq hJS,
            hSdprodS.2.2.2.index_eq_card,
            MathlibSupport.natCard_subgroupOf_eq (Fcore_sub S)]
          exact hCoprimeS.symm
        simpa only [MathlibSupport.natCard_subgroupOf_eq hJS] using
          isHall_primeSupport (J.subgroupOf S) hcop
      exact TypeSpecInternal.hall_of_le_hall_of_hall16
        hUJ hJS hUHallJ hJHallS (by
          intro t ht
          exact ⟨ht.1, ht.2.trans (Subgroup.card_dvd_of_le hUJ)⟩)
    let US : Subgroup S := U.subgroupOf S
    let eUS : U ≃* US := (Subgroup.subgroupOfEquivOfLe hUS).symm
    let R₀US : Sylow r US :=
      R₀.mapSurjective (f := eUS.toMonoidHom) eUS.surjective
    obtain ⟨Rₛ, hRₛ⟩ :=
      FTContextInternal.exists_sylow_eq_map_of_sylow_hall8
        hr hUHallS ⟨hr, hrU⟩ R₀US
    let A : Subgroup G := (R₀ : Subgroup U).map U.subtype
    let eA : R₀ ≃* A :=
      (R₀ : Subgroup U).equivMapOfInjective U.subtype U.subtype_injective
    have hAcomm : IsMulCommutative A := by
      rw [isMulCommutative_iff]
      intro x y
      obtain ⟨x₀, rfl⟩ := eA.surjective x
      obtain ⟨y₀, rfl⟩ := eA.surjective y
      simpa only [map_mul] using congrArg eA (mul_comm' x₀ y₀)
    have hAncyc : ¬ IsCyclic A := by
      intro hAcyc
      exact hR₀ncyc (eA.isCyclic.mpr hAcyc)
    have hAmeta : IsMetacyclic A :=
      isMetacyclic_of_mulEquiv A eA.symm hR₀meta
    have hAU : A ≤ U := Subgroup.map_subtype_le _
    have hAnormP : A ≤ Subgroup.normalizer (Fitting_core S : Set G) :=
      (hAU.trans (le_sup_left.trans hSdprodS.2.1)).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer hSdprodS.1).mp
          hSdprodS.2.2.1)
    have hcopPA : (Nat.card (Fitting_core S)).Coprime (Nat.card A) :=
      hCoprimeS.coprime_dvd_right
        (Subgroup.card_dvd_of_le (hAU.trans le_sup_left))
    have hPsol : IsSolvable (Fitting_core S) := by
      letI : Group.IsNilpotent (Fitting_core S) := Fcore_nil S
      infer_instance
    have hPne : Fitting_core S ≠ ⊥ := by
      intro hbot
      apply ctxS.StypeP.2.2.1.1
      rw [hbot]
      infer_instance
    obtain ⟨x, hxA, hxOne, hcentNe⟩ :
        ∃ x : G, x ∈ A ∧ x ≠ 1 ∧
          centralizerWithin (Fitting_core S) (Subgroup.zpowers x) ≠ ⊥ := by
      by_contra hall
      push_neg at hall
      have hPbot : Fitting_core S ≤ (⊥ : Subgroup G) :=
        le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
          hAcomm hAncyc hAnormP hcopPA hPsol
          (fun a ha haOne => (hall a ha haOne).le)
      exact hPne (le_bot_iff.mp hPbot)
    obtain ⟨zC, hzCOne⟩ :=
      Subgroup.ne_bot_iff_exists_ne_one.mp hcentNe
    let z : G := zC
    have hzCent : z ∈
        centralizerWithin (Fitting_core S) (Subgroup.zpowers x) :=
      zC.property
    have hzOne : z ≠ 1 := by
      intro hz
      apply hzCOne
      apply Subtype.ext
      exact hz
    have hzP : z ∈ Fitting_core S :=
      (mem_centralizerWithin.mp hzCent).1
    have hxU : x ∈ U := hAU hxA
    have hcomm : Commute z x := by
      rw [Commute]
      exact ((mem_centralizerWithin.mp hzCent).2 x
        (Subgroup.mem_zpowers x)).symm
    have hxSupport : x ∈ FTsupport S := by
      simp only [FTsupport, ftSupport, Set.mem_iUnion]
      refine ⟨z, ⟨Fcore_sub_FTcore ctxS.maxS hzP, hzOne⟩, ?_⟩
      refine ⟨⟨?_, ?_⟩, hxOne⟩
      · simpa [FTder, ftDerived, Stype2] using
          ctxS.StypeP.2.1.2.1 hxU
      · intro w hw
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (hcomm.zpow_left n).eq
    have hxSupport0 : x ∈ FTsupport0 S := FTsupp_sub0 S hxSupport

    let H : Subgroup G := Fitting_core L
    let R₀H : Subgroup H :=
      (R₀ : Subgroup U).map (Subgroup.inclusion sUH)
    have hR₀Hp : IsPGroup r R₀H :=
      R₀.isPGroup'.map (Subgroup.inclusion sUH)
    let RH : Subgroup H := pCore r H
    have hR₀HRH : R₀H ≤ RH := by
      dsimp only [RH]
      exact hR₀Hp.le_pCore_of_isNilpotent
    let R : Subgroup G := RH.map H.subtype
    have hR₀Hmap : R₀H.map H.subtype = A := by
      dsimp only [R₀H, A]
      rw [Subgroup.map_map]
      apply congrArg (fun f : U →* G ↦ (R₀ : Subgroup U).map f)
      ext u
      rfl
    have hAR : A ≤ R := by
      rw [← hR₀Hmap]
      exact Subgroup.map_mono hR₀HRH
    have hRp : IsPGroup r R := by
      dsimp only [R, RH]
      exact pCore_isPGroup.map H.subtype
    have hAne : A ≠ ⊥ := by
      intro hbot
      apply hAncyc
      rw [hbot]
      infer_instance
    have hRne : R ≠ ⊥ := by
      intro hbot
      exact hAne (le_bot_iff.mp (hAR.trans (le_of_eq hbot)))
    let Z : Subgroup G := omegaOneCenterAmbient r R
    have hZcenter : Z ≤ centerWithin R := by
      simpa only [Z] using omegaOneCenterAmbient_le_centerWithin r R
    have hZR : Z ≤ R :=
      hZcenter.trans (centralizerWithin_le_left R R)
    have hRₛA : (Rₛ : Subgroup S).map S.subtype = A := by
      rw [hRₛ]
      simp only [R₀US, Sylow.coe_mapSurjective]
      rw [Subgroup.map_map, Subgroup.map_map]
      apply congrArg (fun f : U →* G ↦ (R₀ : Subgroup U).map f)
      ext u
      rfl
    let I : Subgroup S := (R ⊓ S : Subgroup G).subgroupOf S
    have hIp : IsPGroup r I := by
      have hInfp : IsPGroup r (R ⊓ S : Subgroup G) :=
        hRp.to_inf_left
      exact hInfp.of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hRₛI : (Rₛ : Subgroup S) ≤ I := by
      intro s hs
      have hsA : (s : G) ∈ A := by
        rw [← hRₛA]
        exact ⟨s, hs, rfl⟩
      exact ⟨hAR hsA, s.property⟩
    have hIeq : I = (Rₛ : Subgroup S) :=
      Rₛ.is_maximal' hIp hRₛI
    have hZA : Z ≤ A := by
      intro t htZ
      have htR : t ∈ R := hZR htZ
      have hxR : x ∈ R := hAR hxA
      have hxt : Commute x t := by
        rw [Commute]
        exact (mem_centralizerWithin.mp (hZcenter htZ)).2 x hxR
      have htS : t ∈ S := by
        apply hTIS.centralizerWithin_zpowers_le hxSupport0
        refine mem_centralizerWithin.mpr ⟨Subgroup.mem_top t, ?_⟩
        intro w hw
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
        exact (hxt.zpow_left n).eq
      have htI : (⟨t, htS⟩ : S) ∈ I := ⟨htR, htS⟩
      have htRₛ : (⟨t, htS⟩ : S) ∈ (Rₛ : Subgroup S) := by
        rw [← hIeq]
        exact htI
      have htMap : t ∈ (Rₛ : Subgroup S).map S.subtype :=
        ⟨⟨t, htS⟩, htRₛ, rfl⟩
      rwa [hRₛA] at htMap

    have hZmeta : IsMetacyclic Z := by
      have hsub : IsMetacyclic (Z.subgroupOf A) :=
        isMetacyclic_subgroup hAmeta (Z.subgroupOf A)
      exact isMetacyclic_of_mulEquiv Z
        (Subgroup.subgroupOfEquivOfLe hZA).symm hsub
    have hZrank : Group.rank Z ≤ 2 :=
      rank_le_two_of_isMetacyclic hZmeta
    have hZne : Z ≠ ⊥ := by
      simpa only [Z] using ftt2_omegaOneCenterAmbient_ne_bot hRp hRne
    have hZp : IsPGroup r Z := hRp.to_le hZR
    have hZexp : ∀ z : Z, z ^ r = 1 := by
      intro z
      apply Subtype.ext
      change (z : G) ^ r = 1
      rcases z.property with ⟨zR, hzR, hzEq⟩
      have hzpow :=
        Submission.OddOrder.BG.Section05.omegaOneCenter_pow_eq_one
          (G := R) r ⟨zR, hzR⟩
      have hzpowG : (zR : G) ^ r = 1 :=
        congrArg Subtype.val (congrArg Subtype.val hzpow)
      rw [← hzEq]
      exact hzpowG
    have hZcardDvd : Nat.card Z ∣ r ^ Group.rank Z := by
      letI : CommGroup Z :=
        { (inferInstance : Group Z) with
          mul_comm := fun z w ↦ by
            apply Subtype.ext
            exact ((mem_centralizerWithin.mp
              (hZcenter z.property)).2 (w : G)
                (hZR w.property)).symm }
      exact card_dvd_exponent_pow_rank' Z hZexp
    have hZcardLe : Nat.card Z ≤ r ^ 2 :=
      (Nat.le_of_dvd (pow_pos hr.pos _) hZcardDvd).trans
        (Nat.pow_le_pow_right hr.pos hZrank)
    obtain ⟨m, hm⟩ := hZp.exists_card_eq
    have hmPos : 0 < m := by
      by_contra hm0
      have hm0' : m = 0 := Nat.eq_zero_of_not_pos hm0
      have hcardOne : Nat.card Z = 1 := by simpa [hm0'] using hm
      exact hZne (Subgroup.card_eq_one.mp hcardOne)
    have hmLe : m ≤ 2 := by
      apply (Nat.pow_le_pow_iff_right hr.one_lt).mp
      rw [← hm]
      exact hZcardLe
    have hmCases : m = 1 ∨ m = 2 := by omega

    let W₂y : Subgroup G := conjugateSubgroup8 W₂ y
    have hW₂yL : W₂y ≤ L := le_sup_right.trans defLy.2.1
    have hW₂yNormH : W₂y ≤ Subgroup.normalizer (H : Set G) :=
      hW₂yL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Fcore_sub L)).mp (Fcore_normal L))
    have hW₂yNormR : W₂y ≤ Subgroup.normalizer (R : Set G) := by
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        simpa only [R] using
          characteristic_map_subtype_invariant_under_normalizer
            H W₂y RH hW₂yNormH g hg t ht
      · intro ht
        have hginv : g⁻¹ ∈ W₂y := W₂y.inv_mem hg
        have hback := characteristic_map_subtype_invariant_under_normalizer
          H W₂y RH hW₂yNormH g⁻¹ hginv (g * t * g⁻¹) ht
        have hcancel : g⁻¹ * (g * t * g⁻¹) * (g⁻¹)⁻¹ = t := by group
        simpa only [R, hcancel] using hback
    have hW₂yNormZ : W₂y ≤ Subgroup.normalizer (Z : Set G) := by
      intro g hg
      apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      simpa only [Z, MulEquiv.toMonoidHom_eq_coe] using
        ftt2_omegaOneCenterAmbient_map_conj_eq r R (hW₂yNormR hg)
    obtain ⟨E, hFrobLE⟩ := frobL
    have hHreg : IsSemiregularConjugation H W₂y :=
      ftt2_semiregular_of_semidirect_complement hFrobLE defLy le_sup_right
    have hZH : Z ≤ H :=
      hZR.trans (by
        dsimp only [R]
        exact Subgroup.map_subtype_le RH)
    have hZreg : IsSemiregularConjugation Z W₂y := by
      intro w hw t hfix
      apply Subtype.ext
      exact congrArg (fun z : H => (z : G))
        (hHreg w hw ⟨(t : G), hZH t.property⟩ hfix)
    have hW₂yCard : Nat.card W₂y = ctxS.p := by
      dsimp only [W₂y, conjugateSubgroup8, FTTypePSetupContext.p]
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    have hpDvdZPred : ctxS.p ∣ Nat.card Z - 1 := by
      rw [← hW₂yCard]
      exact ftt2_semiregular_card_dvd_sub_one hZreg hW₂yNormZ
    have hpDvdPow : ctxS.p ∣ r ^ m - 1 := by
      simpa only [hm] using hpDvdZPred
    rcases hmCases with rfl | rfl
    · have hpDvdRPred : ctxS.p ∣ r - 1 := by
        simpa only [pow_one] using hpDvdPow
      have hpLe : ctxS.p ≤ r - 1 :=
        Nat.le_of_dvd (Nat.sub_pos_of_lt hr.one_lt) hpDvdRPred
      omega
    · have hpNeR : ctxS.p ≠ r := ne_of_gt hrLtP
      have hpLtR :=
        (prime_lt_and_dvd_half_factor_of_dvd_sq_sub_one
          hr hrOdd hPrimeS.2 hpNeR (by simpa using hpDvdPow)).1
      omega

  let W₂y : Subgroup G := conjugateSubgroup8 W₂ y
  have hW₂yL : W₂y ≤ L := le_sup_right.trans defLy.2.1
  have hW₂yNormH : W₂y ≤ Subgroup.normalizer (Fitting_core L : Set G) :=
    hW₂yL.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
      (Fcore_sub L)).mp (Fcore_normal L))
  obtain ⟨E, hFrobLE⟩ := frobL

  have hU_not_characteristic :
      ¬ (U.subgroupOf (Fitting_core L)).Characteristic := by
    intro hchar
    letI : (U.subgroupOf (Fitting_core L)).Characteristic := hchar
    have hW₂yNormU : W₂y ≤ Subgroup.normalizer (U : Set G) := by
      rw [← Subgroup.map_subgroupOf_eq_of_le sUH]
      intro g hg
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · exact characteristic_map_subtype_invariant_under_normalizer
          (Fitting_core L) W₂y (U.subgroupOf (Fitting_core L))
          hW₂yNormH g hg u
      · intro hu
        have hginv : g⁻¹ ∈ W₂y := W₂y.inv_mem hg
        have hback := characteristic_map_subtype_invariant_under_normalizer
          (Fitting_core L) W₂y (U.subgroupOf (Fitting_core L))
          hW₂yNormH g⁻¹ hginv (g * u * g⁻¹) hu
        have hcancel : g⁻¹ * (g * u * g⁻¹) * (g⁻¹)⁻¹ = u := by group
        simpa only [hcancel] using hback

    have hHreg : IsSemiregularConjugation (Fitting_core L) W₂y :=
      ftt2_semiregular_of_semidirect_complement hFrobLE defLy le_sup_right
    have hUreg : IsSemiregularConjugation U W₂y := by
      intro w hw u hfix
      apply Subtype.ext
      exact congrArg (fun z : Fitting_core L => (z : G))
        (hHreg w hw ⟨(u : G), sUH u.property⟩ hfix)
    have hW₂yCard : Nat.card W₂y = ctxS.p := by
      dsimp only [W₂y, conjugateSubgroup8, FTTypePSetupContext.p]
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective]
    have hpDvdUPred : ctxS.p ∣ Nat.card U - 1 := by
      rw [← hW₂yCard]
      exact ftt2_semiregular_card_dvd_sub_one hUreg hW₂yNormU
    have hUmodP : Nat.ModEq ctxS.p (Nat.card U) 1 :=
      ((Nat.modEq_iff_dvd' (Nat.card_pos (α := U))).2 hpDvdUPred).symm

    have hUstar : ctxS.ustar = nU ctxS.p ctxS.q := by
      simpa only [FTTypePSetupContext.ustar] using
        (nU_eq_div_of_prime hPrimeS.2).symm
    have hnotModS : ¬ Nat.ModEq ctxS.q ctxS.p 1 := by
      intro hmod
      have hqDvdUstar : ctxS.q ∣ ctxS.ustar := hPrimeCasesS.2.1 hmod
      have hcardDiv : Nat.card U = ctxS.ustar / ctxS.q := by
        simpa only [if_pos hmod] using hGaloisCardS hGalS
      have hqMulU : ctxS.q * Nat.card U = nU ctxS.p ctxS.q := by
        rw [hcardDiv, ← hUstar]
        exact Nat.mul_div_cancel' hqDvdUstar
      have hnUmodP : Nat.ModEq ctxS.p (nU ctxS.p ctxS.q) 1 :=
        ftt2_nU_modEq_one hPrimeS.1.pos
      have hmulMod : Nat.ModEq ctxS.p
          (ctxS.q * Nat.card U) ctxS.q := by
        simpa only [Nat.mul_one] using hUmodP.mul_left ctxS.q
      have hqModP : Nat.ModEq ctxS.p ctxS.q 1 :=
        hmulMod.symm.trans (by simpa only [hqMulU] using hnUmodP)
      have hqOne : ctxS.q = 1 :=
        hqModP.eq_of_lt_of_lt hlt hPrimeS.2.one_lt
      exact hPrimeS.1.ne_one hqOne
    have hUcardNU : Nat.card U = nU ctxS.p ctxS.q := by
      calc
        Nat.card U = ctxS.ustar := by
          simpa only [if_neg hnotModS] using hGaloisCardS hGalS
        _ = nU ctxS.p ctxS.q := hUstar
    have hNUcop : (nU ctxS.p ctxS.q).Coprime (ctxS.p - 1) := by
      simpa only [hUstar] using (hPrimeCasesS.2.2 hnotModS).1

    let data : TypePGaloisConclusion ctxS.D := galoisSData hGalS
    let P : Subgroup G := Fitting_core S
    let N : Subgroup P := ctxS.H0.subgroupOf P
    let qP : P →* ptypeFCoreFactor ctxS.ptypeCtx := QuotientGroup.mk' N
    have hNbot : N = ⊥ := by
      dsimp only [N]
      rw [hFcoreKernelS, Subgroup.bot_subgroupOf]
    have hqPinj : Function.Injective qP := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk']
      exact hNbot
    have hqPbij : Function.Bijective qP :=
      ⟨hqPinj, QuotientGroup.mk'_surjective N⟩
    let eP := MulEquiv.ofBijective qP hqPbij
    let sigma : Additive P ≃+ data.F :=
      (MulEquiv.toAdditive eP).trans data.phi
    have hpsiInj : Function.Injective data.psi :=
      data.psi.ker_eq_bot_iff.mp (data.psi_kernel.trans hActionKernelS)
    have hUcomm : IsMulCommutative U := hFactsS.2.2.2.1
    have hinvMul (u v : U) :
        (u * v)⁻¹ = u⁻¹ * v⁻¹ :=
      (mul_inv_rev u v).trans
        (hUcomm.is_comm.comm (v⁻¹) (u⁻¹))
    have hinvOne : (1 : U)⁻¹ = 1 := by
      apply Subtype.ext
      exact inv_one
    let invU : U →* U :=
      { toFun := fun u : U ↦ u⁻¹
        map_one' := hinvOne
        map_mul' := hinvMul }
    let psiInv : U →* data.Fˣ := data.psi.comp invU
    have hpsiInvInj : Function.Injective psiInv := by
      intro u v huv
      apply inv_injective
      apply hpsiInj
      exact huv
    have hprimeLine :
        (primeAdditiveLine data.F).comap sigma.toAddMonoidHom =
          (W₂.subgroupOf P).toAddSubgroup := by
      ext x
      change Additive.ofMul (eP x.toMul) ∈
          (primeAdditiveLine data.F).comap data.phi.toAddMonoidHom ↔
        (x.toMul : G) ∈ W₂
      rw [data.primeLine_comap]
      change eP x.toMul ∈ ctxS.D.W₂bar ↔ (x.toMul : G) ∈ W₂
      rw [ctxS.D.W₂bar_fixed]
      constructor
      · intro hfix
        have hxCent : (x.toMul : G) ∈ centralizerWithin P W₁ := by
          refine mem_centralizerWithin.mpr ⟨x.toMul.property, ?_⟩
          intro w hw
          let w₁ : W₁ := ⟨w, hw⟩
          have hwfix := hfix w₁
          change ptypeW₁FactorAction ctxS.ptypeCtx w₁ (qP x.toMul) =
            qP x.toMul at hwfix
          rw [ptypeW₁FactorAction,
            subgroupConjugationFactorHom_apply_mk] at hwfix
          have hconj := hqPinj hwfix
          exact mul_inv_eq_iff_eq_mul.mp (congrArg Subtype.val hconj)
        rw [hCentCoreS] at hxCent
        exact hxCent
      · intro hxW₂ w
        have hxCent : (x.toMul : G) ∈ centralizerWithin P W₁ := by
          rw [hCentCoreS]
          exact hxW₂
        change ptypeW₁FactorAction ctxS.ptypeCtx w (qP x.toMul) =
          qP x.toMul
        rw [ptypeW₁FactorAction,
          subgroupConjugationFactorHom_apply_mk]
        apply congrArg qP
        apply Subtype.ext
        have hcomm := (mem_centralizerWithin.mp hxCent).2 (w : G) w.property
        calc
          (w : G) * (x.toMul : G) * (w : G)⁻¹ =
              (x.toMul : G) * (w : G) * (w : G)⁻¹ := by rw [hcomm]
          _ = (x.toMul : G) := by simp
    let fieldModel : FiniteFieldImage P W₂ U :=
      { F := data.F
        sigma := sigma
        p0_le := ctxS.StypeP.2.2.2.1.2.2.1
        primeLine_comap := hprimeLine
        psi := psiInv
        psi_injective := hpsiInvInj
        conjugation_compatibility := by
          intro hUP x u
          change data.phi
              (Additive.ofMul (eP (rightConjugate P U hUP x u))) =
            data.phi (Additive.ofMul (eP x)) *
              (data.psi u⁻¹ : data.F)
          have haction :
              eP (rightConjugate P U hUP x u) =
                ctxS.D.U_action u⁻¹ (eP x) := by
            change qP (rightConjugate P U hUP x u) =
              ptypeFCoreAction ctxS.ptypeCtx u⁻¹ (qP x)
            rw [ptypeFCoreAction, subgroupConjugationFactorHom_apply_mk]
            apply congrArg qP
            apply Subtype.ext
            rw [coe_rightConjugate]
            simp
          rw [haction]
          exact data.phi_U_compatible (eP x) u⁻¹ }
    have hPcard : Nat.card P = ctxS.p ^ ctxS.q := by
      simpa only [P] using
        (FTtypeP_facts ctxS).2.2.2.2.2.1
    have hQelem : IsElementaryAbelianGroup ctxS.q (Fitting_core T) := by
      simpa only [FTTypePSetupContext.q] using
        (FTtypeP_facts ctxT).2.2.2.2.1
    have hW₂T : W₂ ≤ T := ctxT.StypeP.1.2.1.1
    have hW₂NormQ : W₂ ≤ Subgroup.normalizer (Fitting_core T : Set G) :=
      hW₂T.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Fcore_sub T)).mp (Fcore_normal T))
    apply no_full_FT_Galois_structure defW ctxS.maxS ctxS.StypeP hlt
    refine ⟨⟨fieldModel, ?_, ?_, ?_⟩, hQelem, hW₂NormQ, ?_⟩
    · simpa only [P, FTTypePSetupContext.p, FTTypePSetupContext.q] using hPcard
    · simpa only [FTTypePSetupContext.p, FTTypePSetupContext.q] using hUcardNU
    · simpa only [FTTypePSetupContext.p, FTTypePSetupContext.q] using hNUcop
    · refine ⟨y⁻¹, (Fitting_core T).inv_mem hyQ, ?_⟩
      simpa only [W₂y, appendixCP1, inv_inv, conjugateSubgroup8]
        using hW₂yNormU

  have defK : Fitting_core M = V := by
    by_contra hCoreNe
    obtain ⟨hCoreLower, hIndex, eps, chi, hchi, hdecomp⟩ :=
      ftt2_support_of_core_ne ctxS ctxT pairST hlt Ttype2 hUV
        maxNV_M maxM sNVM frobM tau₁M psi cohM Mpsi psi1 hCoreNe
    let H : Subgroup M := FTType1FittingIn M
    letI : H.Normal := by
      simpa only [H, FTType1FittingIn] using Fcore_normal M
    let dd : DadeHypothesis (⊤ : Subgroup G) M
        (subgroupNonidentity (H.map M.subtype)) :=
      ftt2Type1DadeHypothesis M maxM
    let tauTop : ClassFunction M Complex →ₗ[ℂ]
        ClassFunction (⊤ : Subgroup G) Complex := ftt2SourceMap.comp tau₁M
    let chiTop : ClassFunction (⊤ : Subgroup G) Complex := ftt2SourceMap chi
    let rho : ClassFunction M Complex := invDade dd chiTop

    have hcohTop : coherent_with
        ((FTType1SeqIndFamily M : Finset (ClassFunction M Complex)) :
          Set (ClassFunction M Complex))
        (nonidentitySet M) (Dade dd) tauTop := by
      simpa only [dd, tauTop, H, FTType1FittingIn,
        Subgroup.map_subgroupOf_eq_of_le (Fcore_sub M)] using
        ftt2Type1Coherence_top cohM
    have hpsiSeq : psi ∈ seqIndD (k := Complex) H
        (⊤ : Subgroup H) ⊥ := by
      simpa only [H, FTType1SeqIndFamily] using Mpsi

    have htauNorm (theta : ClassFunction M Complex)
        (htheta : theta ∈ FTType1SeqIndFamily M) :
        classFunctionNormSq (tau₁M theta) = 1 := by
      have hvirtual := cohM.mapsToVirtual theta
        (AddSubgroup.subset_closure htheta)
      let thetaIrr : IrreducibleCharacter M Complex :=
        ⟨theta, FTtype1_Ind_irr M maxM Mtype1 theta htheta⟩
      have hself : characterPairing theta theta = 1 := by
        simpa only [thetaIrr] using thetaIrr.characterPairing_self
      rw [classFunctionNormSq_eq_re_starCharacterPairing,
        PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hvirtual hvirtual,
        cohM.isometry theta (AddSubgroup.subset_closure htheta)
          theta (AddSubgroup.subset_closure htheta), hself]
      norm_num

    let invPsi : ClassFunction M Complex := ClassFunction.inverseLinear psi
    have hInvPsi : invPsi ∈ FTType1SeqIndFamily M := by
      simpa only [invPsi, H, FTType1SeqIndFamily] using
        seqInd_inverse_mem (k := Complex) H (⊤ : Subgroup H) ⊥ hpsiSeq
    have hchiNorm : classFunctionNormSq chi = 1 := by
      rcases hchi with hchi | hchi
      · rw [hchi]
        exact htauNorm psi Mpsi
      · rw [hchi, ← neg_one_smul ℂ (tau₁M invPsi),
          ftt2_normSq_smul, htauNorm invPsi hInvPsi]
        norm_num
    have hchiTopNorm : classFunctionNormSq chiTop = 1 := by
      simpa only [chiTop, ftt2_source_normSq] using hchiNorm

    let beta : ClassFunction G Complex :=
      FTtype1Dade M maxM (FTtype1Bridge M psi)
    have hbetaTop : ftt2TargetMap (dadeInd1Beta H dd psi) = beta := by
      simpa only [H, beta] using ftt2_target_dadeInd1Beta maxM dd psi

    let C : Set (⊤ : Subgroup G) :=
      {g | (g : G) ∉ Dade_support dd}
    let SW : Set (⊤ : Subgroup G) :=
      {g | (g : G) ∈ classSupportWithin (⊤ : Subgroup G)
        (cyclicTISet W W₁ W₂)}
    let SP : Set (⊤ : Subgroup G) :=
      {g | (g : G) ∈ classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity (Fitting_core S))}
    let SQ : Set (⊤ : Subgroup G) :=
      {g | (g : G) ∈ classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity (Fitting_core T))}
    let C0 : Set (⊤ : Subgroup G) := C \ (SW ∪ SP ∪ SQ)
    let C1 : Set (⊤ : Subgroup G) := C \ C0

    /- Source (14.11.3). -/
    have hlarge : ∀ g ∈ C0, 1 ≤ Complex.normSq (chiTop g) := by
      intro g hg
      have hSW : (g : G) ∉ classSupportWithin (⊤ : Subgroup G)
          (cyclicTISet W W₁ W₂) := by
        intro h
        exact hg.2 (Or.inl (Or.inl h))
      have hSP : (g : G) ∉ classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (Fitting_core S)) := by
        intro h
        exact hg.2 (Or.inl (Or.inr h))
      have hSQ : (g : G) ∉ classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (Fitting_core T)) := by
        intro h
        exact hg.2 (Or.inr h)
      have hgOutside : (g : G) ∉ Dade_support dd := by
        have hgC : g ∈ C := hg.1
        change (g : G) ∉ Dade_support dd at hgC
        exact hgC
      have hbetaZero : dadeInd1Beta H dd psi g = 0 := by
        apply ClassFunction.eq_zero_of_mem_supportedOn
          (Dade_cfunS dd (dadeInducedTrivial H - psi))
        simpa only [Set.mem_setOf_eq] using hgOutside
      have hbetaZeroG : beta (g : G) = 0 := by
        have hgTop :
            Subgroup.topEquiv.symm.toMonoidHom (g : G) = g := by
          apply Subtype.ext
          rfl
        have h := congrArg
          (fun f : ClassFunction G ℂ => f (g : G)) hbetaTop
        simp only [ftt2TargetMap, ClassFunction.comap_apply] at h
        rw [hgTop, hbetaZero] at h
        exact h.symm
      have hchiValue : chi (g : G) =
          (∑ i, ∑ j,
            if eps i j then -(ctxT.eta i j) else ctxT.eta i j) (g : G) := by
        have h := congrArg (fun f : ClassFunction G Complex => f (g : G)) hdecomp
        change beta (g : G) =
          (∑ i, ∑ j,
            if eps i j then -(ctxT.eta i j) else ctxT.eta i j) (g : G) -
              chi (g : G) at h
        rw [hbetaZeroG] at h
        exact (sub_eq_zero.mp h.symm).symm
      change 1 ≤ Complex.normSq (chi (g : G))
      rw [hchiValue]
      exact ftt2_signed_eta_rectangle_lower ctxS ctxT hGalS hGalT
        eps (g : G) hSW hSP hSQ

    have hpartition : C = C0 ∪ C1 := by
      ext g
      simp [C0, C1]
    have hdisjoint : Disjoint C0 C1 := by
      rw [Set.disjoint_left]
      intro g hg0 hg1
      exact hg1.2 hg0

    have hSuzuki := Dade_cover_inequality
      (I := Fin 1) (fun _ => dd)
      (fun i j hij => (hij (Subsingleton.elim i j)).elim)
      chiTop hchiTopNorm
    have hCover : DadeCoverComplement (fun _ : Fin 1 => dd) =
        {g : G | g ∉ Dade_support dd} := by
      ext g
      simp [DadeCoverComplement]
    have hCcard : C.ncard =
        ({g : G | g ∉ Dade_support dd} : Set G).ncard := by
      change
        ({g : (⊤ : Subgroup G) | (g : G) ∈
            ({x : G | x ∉ Dade_support dd} : Set G)} :
          Set (⊤ : Subgroup G)).ncard =
          ({x : G | x ∉ Dade_support dd} : Set G).ncard
      exact ftt2_ncard_preimage_top _
    have hSuzuki' :
        (Nat.card (⊤ : Subgroup G) : Real)⁻¹ *
            ((∑ g : (⊤ : Subgroup G),
              if g ∈ C then Complex.normSq (chiTop g) else 0) - C.ncard) +
          classFunctionNormSq rho -
            (subgroupNonidentity (H.map M.subtype)).ncard /
              (Nat.card M : Real) ≤ 0 := by
      simpa only [Fin.sum_univ_one, hCover, hCcard, rho, C,
        Set.mem_setOf_eq, sub_eq_add_neg, add_assoc] using hSuzuki
    have hUpper0 : classFunctionNormSq rho ≤
        (subgroupNonidentity (H.map M.subtype)).ncard /
            (Nat.card M : Real) +
          C1.ncard / (Nat.card G : Real) := by
      have hUpperTop : classFunctionNormSq rho ≤
          (subgroupNonidentity (H.map M.subtype)).ncard /
              (Nat.card M : Real) +
            C1.ncard / (Nat.card (⊤ : Subgroup G) : Real) := by
        exact ftt2_oneCover_upper_bound
          (Q := (⊤ : Subgroup G))
          (chi := fun g => chiTop g)
          (C := C) (C0 := C0) (C1 := C1)
          (hpartition := hpartition) (hdisjoint := hdisjoint)
          (hlarge := hlarge)
          (rho := classFunctionNormSq rho)
          (base := (subgroupNonidentity (H.map M.subtype)).ncard /
            (Nat.card M : Real))
          (hSuzuki := by
            have hsum :
                (∑ g : (⊤ : Subgroup G),
                  @ite Real (g ∈ C) (Classical.propDecidable _)
                    (Complex.normSq (chiTop g)) 0) =
                  ∑ g : (⊤ : Subgroup G),
                    if g ∈ C then Complex.normSq (chiTop g) else 0 := by
              apply Finset.sum_congr rfl
              intro g _
              by_cases hg : g ∈ C <;> simp only [hg, if_pos, if_neg]
            rw [hsum]
            exact hSuzuki')
      simpa only [Subgroup.card_top] using hUpperTop

    /- The linear-subtraction lower estimate, used for `psi` or for `psi*`
    according to the branch defining `chi`. -/
    have hfamilyCard : 1 <
        (seqIndD (k := Complex) H (⊤ : Subgroup H) ⊥).card := by
      have htwo : 2 ≤
          (seqIndD (k := Complex) H (⊤ : Subgroup H) ⊥).card :=
        seqInd_nontrivial (k := Complex) H (mFT_odd M)
          (⊤ : Subgroup H) ⊥ hpsiSeq
      exact lt_of_lt_of_le
        (Nat.succ_lt_succ (Nat.zero_lt_succ 0)) htwo
    have hindexHalf : (H.index : Real) ≤
        ((Nat.card H : Real) - 1) / 2 := by
      obtain ⟨E, hME⟩ := frobM
      have hFrob : IsFrobeniusDecomposition H (E.subgroupOf M) := by
        simpa only [H] using ftt2_frobeniusIn_decomposition hME
      exact odd_Frobenius_index_ler H (E.subgroupOf M) (mFT_odd M) hFrob
    have hDadeLower (theta : ClassFunction M Complex)
        (htheta : theta ∈ FTType1SeqIndFamily M)
        (htheta1 : theta 1 = (H.index : Complex)) :
        1 - (H.index : Real) / Nat.card H ≤
          classFunctionNormSq (invDade dd (tauTop theta)) := by
      have hthetaSeq : theta ∈ seqIndD (k := Complex) H
          (⊤ : Subgroup H) ⊥ := by
        simpa only [H, FTType1SeqIndFamily] using htheta
      let thetaIrr : IrreducibleCharacter M Complex :=
        ⟨theta, FTtype1_Ind_irr M maxM Mtype1 theta htheta⟩
      exact ((Dade_Ind1_sub_lin H dd tauTop thetaIrr hcohTop
        hfamilyCard hthetaSeq
          (by simpa only [thetaIrr] using htheta1)).norm_bounds hindexHalf).1
    have hLower :
        1 - ((Nat.card W₂ * Nat.card W₁ : Nat) : Real) /
            Nat.card (Fitting_core M) ≤ classFunctionNormSq rho := by
      have hHindex : H.index = Nat.card W₂ * Nat.card W₁ := by
        simpa only [H, FTtype1CoreIndex, Nat.mul_comm] using hIndex
      have hHcard : Nat.card H = Nat.card (Fitting_core M) := by
        simpa only [H, FTType1FittingIn] using
          MathlibSupport.natCard_subgroupOf_eq (Fcore_sub M)
      rcases hchi with hchi | hchi
      · have h := hDadeLower psi Mpsi
          (by simpa only [H, FTtype1CoreIndex] using psi1)
        simpa only [rho, chiTop, tauTop, hchi, LinearMap.comp_apply,
          hHindex, hHcard] using h
      · have hInv1 : invPsi 1 = (H.index : Complex) := by
          simpa only [invPsi, H, FTtype1CoreIndex,
            ClassFunction.inverseLinear_apply, inv_one] using psi1
        have h := hDadeLower invPsi hInvPsi hInv1
        have hrho : rho = -invDade dd (tauTop invPsi) := by
          simp only [rho, chiTop, hchi, tauTop, invPsi,
            map_neg, LinearMap.comp_apply]
        rw [hrho,
          ← neg_one_smul ℂ (invDade dd (tauTop invPsi)),
          ftt2_normSq_smul]
        norm_num only [Complex.normSq_neg, Complex.normSq_one, one_mul]
        simpa only [hHindex, hHcard] using h

    /- Count the residual part of the cover by the cyclic support and the
    two type-II cores.  These are exactly the three source summands. -/
    have hC1sub : C1 ⊆ SW ∪ SP ∪ SQ := by
      intro g hg
      by_contra hout
      exact hg.2 ⟨hg.1, hout⟩
    have hC1ratio : C1.ncard / (Nat.card G : Real) ≤
        SW.ncard / (Nat.card G : Real) +
          SP.ncard / (Nat.card G : Real) +
          SQ.ncard / (Nat.card G : Real) := by
      have hn := (Set.ncard_mono hC1sub).trans
        ((Set.ncard_union_le (SW ∪ SP) SQ).trans
          (Nat.add_le_add_right (Set.ncard_union_le SW SP) SQ.ncard))
      have hGpos : (0 : Real) < Nat.card G := Nat.cast_pos.mpr Nat.card_pos
      calc
        (C1.ncard : Real) / Nat.card G ≤
            ((SW.ncard + SP.ncard) + SQ.ncard : Nat) / Nat.card G := by
          exact div_le_div_of_nonneg_right (by exact_mod_cast hn) hGpos.le
        _ = _ := by
          norm_num only [Nat.cast_add]
          ring
    have hSWcard : SW.ncard =
        (classSupportWithin (⊤ : Subgroup G)
          (cyclicTISet W W₁ W₂)).ncard := by
      change
        ({g : (⊤ : Subgroup G) | (g : G) ∈
            classSupportWithin (⊤ : Subgroup G) (cyclicTISet W W₁ W₂)} :
          Set (⊤ : Subgroup G)).ncard =
          (classSupportWithin (⊤ : Subgroup G)
            (cyclicTISet W W₁ W₂)).ncard
      exact ftt2_ncard_preimage_top _
    have hSPcard : SP.ncard =
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (Fitting_core S))).ncard := by
      change
        ({g : (⊤ : Subgroup G) | (g : G) ∈
            classSupportWithin (⊤ : Subgroup G)
              (subgroupNonidentity (Fitting_core S))} :
          Set (⊤ : Subgroup G)).ncard =
          (classSupportWithin (⊤ : Subgroup G)
            (subgroupNonidentity (Fitting_core S))).ncard
      exact ftt2_ncard_preimage_top _
    have hSQcard : SQ.ncard =
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (Fitting_core T))).ncard := by
      change
        ({g : (⊤ : Subgroup G) | (g : G) ∈
            classSupportWithin (⊤ : Subgroup G)
              (subgroupNonidentity (Fitting_core T))} :
          Set (⊤ : Subgroup G)).ncard =
          (classSupportWithin (⊤ : Subgroup G)
            (subgroupNonidentity (Fitting_core T))).ncard
      exact ftt2_ncard_preimage_top _
    have hSWratio : SW.ncard / (Nat.card G : Real) =
        1 - (Nat.card W₁ : Real)⁻¹ - (Nat.card W₂ : Real)⁻¹ +
          ((Nat.card W₂ * Nat.card W₁ : Nat) : Real)⁻¹ := by
      rw [hSWcard,
        ftt2_classSupport_ratio_eq
          ctxS.primeDade.prDade_cycTI.normedTI,
        defW.ncard_cyclicTISet, defW.card_eq_mul_card]
      have hq : (0 : Real) < Nat.card W₁ := Nat.cast_pos.mpr Nat.card_pos
      have hp : (0 : Real) < Nat.card W₂ := Nat.cast_pos.mpr Nat.card_pos
      norm_num only [Nat.cast_mul,
        Nat.cast_sub (Nat.card_pos (α := W₁)),
        Nat.cast_sub (Nat.card_pos (α := W₂)),
        Nat.cast_one]
      field_simp [hq.ne', hp.ne']
      ring
    have hSPratio : SP.ncard / (Nat.card G : Real) ≤
        ((Nat.card U * Nat.card W₁ : Nat) : Real)⁻¹ := by
      rw [hSPcard, div_eq_mul_inv, mul_comm]
      exact FTtype2_cc_core_ler defW ctxS.maxS ctxS.StypeP Stype2
    have hSQratio : SQ.ncard / (Nat.card G : Real) ≤
        ((Nat.card V * Nat.card W₂ : Nat) : Real)⁻¹ := by
      rw [hSQcard, div_eq_mul_inv, mul_comm]
      exact FTtype2_cc_core_ler xdefW ctxT.maxS ctxT.StypeP Ttype2
    have hresidual : C1.ncard / (Nat.card G : Real) ≤
        1 - (Nat.card W₁ : Real)⁻¹ - (Nat.card W₂ : Real)⁻¹ +
          ((Nat.card W₂ * Nat.card W₁ : Nat) : Real)⁻¹ +
          ((Nat.card U * Nat.card W₁ : Nat) : Real)⁻¹ +
          ((Nat.card V * Nat.card W₂ : Nat) : Real)⁻¹ := by
      calc
        _ ≤ SW.ncard / (Nat.card G : Real) +
            SP.ncard / (Nat.card G : Real) +
            SQ.ncard / (Nat.card G : Real) := hC1ratio
        _ ≤ _ := by rw [hSWratio]; linarith

    have hHmap : H.map M.subtype = Fitting_core M := by
      simpa only [H, FTType1FittingIn] using
        Subgroup.map_subgroupOf_eq_of_le (Fcore_sub M)
    have hMcard : Nat.card M =
        Nat.card (Fitting_core M) * (Nat.card W₂ * Nat.card W₁) := by
      have hHcard : Nat.card H = Nat.card (Fitting_core M) := by
        simpa only [H, FTType1FittingIn] using
          MathlibSupport.natCard_subgroupOf_eq (Fcore_sub M)
      have hHindex : H.index = Nat.card W₁ * Nat.card W₂ := by
        simpa only [H, FTtype1CoreIndex] using hIndex
      calc
        Nat.card M = H.index * Nat.card H := H.index_mul_card.symm
        _ = (Nat.card W₁ * Nat.card W₂) *
            Nat.card (Fitting_core M) := by rw [hHindex, hHcard]
        _ = Nat.card (Fitting_core M) *
            (Nat.card W₂ * Nat.card W₁) := by ac_rfl
    have hbase :
        (subgroupNonidentity (H.map M.subtype)).ncard /
            (Nat.card M : Real) =
          ((Nat.card (Fitting_core M) - 1 : Nat) : Real) /
            ((Nat.card (Fitting_core M) *
              (Nat.card W₂ * Nat.card W₁) : Nat) : Real) := by
      rw [hHmap, ftt2_subgroupNonidentity_ncard, hMcard]
    have hbaseLt :
        (subgroupNonidentity (H.map M.subtype)).ncard /
            (Nat.card M : Real) <
          ((Nat.card W₂ * Nat.card W₁ : Nat) : Real)⁻¹ := by
      rw [hbase]
      have hk : (0 : Real) < Nat.card (Fitting_core M) :=
        Nat.cast_pos.mpr Nat.card_pos
      have hp : (0 : Real) < Nat.card W₂ := Nat.cast_pos.mpr Nat.card_pos
      have hq : (0 : Real) < Nat.card W₁ := Nat.cast_pos.mpr Nat.card_pos
      norm_num only [Nat.cast_mul,
        Nat.cast_sub (Nat.card_pos (α := Fitting_core M)),
        Nat.cast_one]
      field_simp [hk.ne', hp.ne', hq.ne']
      linarith

    have hUpper : classFunctionNormSq rho <
        1 - (Nat.card W₁ : Real)⁻¹ - (Nat.card W₂ : Real)⁻¹ +
          2 * ((Nat.card W₂ * Nat.card W₁ : Nat) : Real)⁻¹ +
          ((Nat.card U * Nat.card W₁ : Nat) : Real)⁻¹ +
          ((Nat.card V * Nat.card W₂ : Nat) : Real)⁻¹ := by
      calc
        _ ≤ (subgroupNonidentity (H.map M.subtype)).ncard /
            (Nat.card M : Real) + C1.ncard / (Nat.card G : Real) := hUpper0
        _ < _ := by linarith [hbaseLt, hresidual]

    have hReverse :
        (Nat.card W₂ : Real)⁻¹ + (Nat.card W₁ : Real)⁻¹ ≤
          ((Nat.card W₂ * Nat.card W₁ : Nat) : Real) /
              Nat.card (Fitting_core M) +
            2 * ((Nat.card W₂ * Nat.card W₁ : Nat) : Real)⁻¹ +
            ((Nat.card U * Nat.card W₁ : Nat) : Real)⁻¹ +
            ((Nat.card V * Nat.card W₂ : Nat) : Real)⁻¹ := by
      linarith [hLower, hUpper]

    /- Source (14.11.4): `p*q | v-1`, the core bound, and the two
    complement estimates make the right side strictly smaller. -/
    obtain ⟨hqPrime, hpPrime⟩ :=
      FTtypeP_primes S U W W₁ W₂ defW ctxS.maxS ctxS.StypeP
    have hpDvd : Nat.card W₂ ∣ Nat.card V - 1 :=
      (FTtypeP_bridge_facts ctxT).2.2.2.2
    have hgeomMod : ∀ n,
        Nat.ModEq (Nat.card W₁) 1 (nU (Nat.card W₁) (n + 1)) := by
      intro n
      induction n with
      | zero =>
          simpa only [Nat.zero_add, nU_succ, nU_zero, pow_zero, zero_add]
            using (Nat.ModEq.refl 1 :
              Nat.ModEq (Nat.card W₁) 1 1)
      | succ n ih =>
          rw [nU_succ]
          exact ih.add
            ((dvd_pow_self (Nat.card W₁) (Nat.succ_ne_zero n)).zero_modEq_nat)
    have hqDvd : Nat.card W₁ ∣ Nat.card V - 1 := by
      have hpPos := hpPrime.pos
      have hmod := hgeomMod (Nat.card W₂ - 1)
      rw [Nat.sub_add_cancel hpPrime.one_le] at hmod
      rw [hCardVnUSwapped]
      exact (Nat.modEq_iff_dvd'
        (by have := Nat.card_pos (α := V); omega)).mp hmod
    have hpqCoprime : Nat.Coprime (Nat.card W₂) (Nat.card W₁) :=
      (Nat.coprime_primes hpPrime hqPrime).mpr (Nat.ne_of_gt hlt)
    have hpqDvd : Nat.card W₂ * Nat.card W₁ ∣ Nat.card V - 1 :=
      hpqCoprime.mul_dvd_of_dvd_of_dvd hpDvd hqDvd
    have hpqLtV : Nat.card W₂ * Nat.card W₁ < Nat.card V := by
      have hpredPos : 0 < Nat.card V - 1 := by
        rw [hCardVnUSwapped]
        exact Nat.sub_pos_of_lt (ftt2_one_lt_nU_of_primes hqPrime hpPrime)
      have hle := Nat.le_of_dvd hpredPos hpqDvd
      omega

    have hcoreTerm :
        ((Nat.card W₂ * Nat.card W₁ : Nat) : Real) /
            Nat.card (Fitting_core M) <
          (2 * Nat.card W₂ : Real)⁻¹ := by
      have hsmall :
          2 * Nat.card W₂ * (Nat.card W₂ * Nat.card W₁) <
            Nat.card (Fitting_core M) := by
        calc
          _ < 2 * Nat.card W₂ * Nat.card V :=
            (Nat.mul_lt_mul_left
              (Nat.mul_pos (by norm_num : 0 < 2) hpPrime.pos)).2 hpqLtV
          _ < _ := hCoreLower
      have hk : (0 : Real) < Nat.card (Fitting_core M) :=
        Nat.cast_pos.mpr Nat.card_pos
      have hp : (0 : Real) < Nat.card W₂ := Nat.cast_pos.mpr hpPrime.pos
      have hq : (0 : Real) < Nat.card W₁ := Nat.cast_pos.mpr hqPrime.pos
      have hsmallR :
          (2 : Real) * Nat.card W₂ * (Nat.card W₂ * Nat.card W₁) <
            Nat.card (Fitting_core M) := by exact_mod_cast hsmall
      simp only [Nat.cast_mul]
      field_simp [hk.ne', hp.ne', hq.ne']
      nlinarith only [hsmallR]
    have hcomplU :
        ((Nat.card U * Nat.card W₁ : Nat) : Real)⁻¹ <
          ((2 * Nat.card W₁ ^ 2 : Nat) : Real)⁻¹ :=
      FTtypeP_complV_ltr defW ctxS.maxS ctxS.StypeP
        (Wn := W₁) le_rfl
    have hcomplV :
        ((Nat.card V * Nat.card W₂ : Nat) : Real)⁻¹ <
          ((2 * Nat.card W₁ ^ 2 : Nat) : Real)⁻¹ :=
      FTtypeP_complV_ltr xdefW ctxT.maxS ctxT.StypeP
        (Wn := W₁) (Nat.le_of_lt hlt)
    have hqThree : 3 ≤ Nat.card W₁ :=
      hqPrime.odd_iff.mp (mFT_odd W₁)
    have hpPosR : (0 : Real) < Nat.card W₂ := Nat.cast_pos.mpr hpPrime.pos
    have hqPosR : (0 : Real) < Nat.card W₁ := Nat.cast_pos.mpr hqPrime.pos
    have hpure :
        (2 * Nat.card W₂ : Real)⁻¹ +
            2 * ((Nat.card W₂ * Nat.card W₁ : Nat) : Real)⁻¹ +
            ((Nat.card W₁ : Real)⁻¹) ^ 2 <
          (Nat.card W₂ : Real)⁻¹ + (Nat.card W₁ : Real)⁻¹ := by
      have hqThreeR : (3 : Real) ≤ Nat.card W₁ := by
        exact_mod_cast hqThree
      have hpTwoR : (2 : Real) ≤ Nat.card W₂ := by
        exact_mod_cast hpPrime.two_le
      have hqFactor :
          0 < ((Nat.card W₁ : Real) - 2) *
              ((Nat.card W₁ : Real) + 2) := by
        apply mul_pos <;> linarith
      have hpqFactor :
          0 ≤ ((Nat.card W₂ : Real) - 2) *
              ((Nat.card W₁ : Real) - 1) := by
        apply mul_nonneg <;> linarith
      have hpoly :
          0 < (Nat.card W₁ : Real) ^ 2 +
              2 * (Nat.card W₂ : Real) * Nat.card W₁ -
              4 * Nat.card W₁ - 2 * Nat.card W₂ := by
        nlinarith only [hqFactor, hpqFactor]
      simp only [Nat.cast_mul]
      field_simp [hpPosR.ne', hqPosR.ne']
      nlinarith only [hpoly]
    have hStrict :
        ((Nat.card W₂ * Nat.card W₁ : Nat) : Real) /
              Nat.card (Fitting_core M) +
            2 * ((Nat.card W₂ * Nat.card W₁ : Nat) : Real)⁻¹ +
            ((Nat.card U * Nat.card W₁ : Nat) : Real)⁻¹ +
            ((Nat.card V * Nat.card W₂ : Nat) : Real)⁻¹ <
          (Nat.card W₂ : Real)⁻¹ + (Nat.card W₁ : Real)⁻¹ := by
      have hcompl :
          ((Nat.card U * Nat.card W₁ : Nat) : Real)⁻¹ +
              ((Nat.card V * Nat.card W₂ : Nat) : Real)⁻¹ <
            ((Nat.card W₁ : Real)⁻¹) ^ 2 := by
        have htwo :
            2 * ((2 * Nat.card W₁ ^ 2 : Nat) : Real)⁻¹ =
              ((Nat.card W₁ : Real)⁻¹) ^ 2 := by
          field_simp [hqPosR.ne']
          norm_num only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
        rw [← htwo]
        linarith
      linarith [hcoreTerm, hcompl, hpure]
    exact (not_lt_of_ge hReverse) hStrict


  have indexMK : FTtype1CoreIndex M =
      Nat.card W₁ * Nat.card W₂ := by
    obtain ⟨_hFrobM, _hVcore, hCompM⟩ :=
      FTtypeII_support_facts ctxT S M Ttype2 pairTS maxNV_M
    rcases hCompM with hsd | ⟨yM, hyS, hsd⟩
    · have hMT : M ≤ T := by
        rw [← FTContextInternal.semidirect_sup_eq8 hsd, defK]
        exact sup_le
          (ctxT.StypeP.2.1.2.1.trans ctxT.StypeP.1.2.2.2.1)
          ctxT.StypeP.1.2.1.1
      have hEq : M = T := eq_mmax maxM ctxT.maxS hMT
      exfalso
      have htype : FTtype M = FTtype T := congrArg FTtype hEq
      omega
    · exact ftt2_index_of_join_L ctxT ctxS pairTS hyS hsd

  /- (14.12)--(14.13): Galois cyclicity rules out conjugacy of M and L. -/
  have hcyclicV : IsCyclic V :=
    PTypeGaloisSubgroupAdaptersInternal.pTypeGalois_complement_cyclic_of_C_eq_bot
      ctxT.actionHypotheses hGalT (ftt2_actionKernel_eq_bot ctxT)
  have not_MG_L : ¬ FTAmbientConjugate M L := by
    rintro ⟨g, hLg⟩
    let e : G ≃* G := MulAut.conj g
    have hcyclicK : IsCyclic (Fitting_core M) := by
      rw [defK]
      exact hcyclicV
    have hcoreMap :
        Fitting_core L = (Fitting_core M).map e.toMonoidHom := by
      rw [hLg]
      exact Fitting_core_map_mulEquiv M e
    have hcyclicL : IsCyclic (Fitting_core L) := by
      rw [hcoreMap]
      exact (e.subgroupMap (Fitting_core M)).isCyclic.mp hcyclicK
    letI : IsCyclic (Fitting_core L) := hcyclicL
    exact hU_not_characteristic
      (ftt2_subgroup_characteristic_of_isCyclic
        (U.subgroupOf (Fitting_core L)))
  have not_LG_M : ¬ FTAmbientConjugate L M :=
    fun hLM => not_MG_L (ftt2_ambientConjugate_symm hLM)

  have LM_cases :
      (starCharacterPairing
          (FTtype1Dade M maxM (FTtype1Bridge M psi)) (tau₁L phi) ≠ 0 ∧
        ((((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ)) /
          (((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ))) ≤
          (((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ)) - 1) ∨
      (starCharacterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi)) (tau₁M psi) ≠ 0 ∧
        Nat.card W₁ = 3 ∧ Nat.card W₂ = 5) := by
    /- Put both canonical type-I coherences over the ambient top subgroup. -/
    let HM : Subgroup M := FTType1FittingIn M
    let HL : Subgroup L := FTType1FittingIn L
    letI : HM.Normal := by
      simpa only [HM, FTType1FittingIn] using Fcore_normal M
    letI : HL.Normal := by
      simpa only [HL, FTType1FittingIn] using Fcore_normal L
    let ddM : DadeHypothesis (⊤ : Subgroup G) M
        (subgroupNonidentity (HM.map M.subtype)) := by
      simpa only [HM] using ftt2Type1DadeHypothesis M maxM
    let ddL : DadeHypothesis (⊤ : Subgroup G) L
        (subgroupNonidentity (HL.map L.subtype)) := by
      simpa only [HL] using ftt2Type1DadeHypothesis L maxL
    let nuM := ftt2SourceMap.comp tau₁M
    let nuL := ftt2SourceMap.comp tau₁L
    have cohTopM : coherent_with
        (↑(seqIndD (k := ℂ) HM (⊤ : Subgroup HM) ⊥) :
          Set (ClassFunction M ℂ))
        (nonidentitySet M) (Dade ddM) nuM := by
      simpa only [HM, ddM, nuM, FTType1SeqIndFamily,
        ftt2Type1DadeHypothesis, ftt2_fittingIn_map_subtype] using
          ftt2Type1Coherence_top cohM
    have cohTopL : coherent_with
        (↑(seqIndD (k := ℂ) HL (⊤ : Subgroup HL) ⊥) :
          Set (ClassFunction L ℂ))
        (nonidentitySet L) (Dade ddL) nuL := by
      simpa only [HL, ddL, nuL, FTType1SeqIndFamily,
        ftt2Type1DadeHypothesis, ftt2_fittingIn_map_subtype] using
          ftt2Type1Coherence_top cohL
    let psiIrr : IrreducibleCharacter M ℂ :=
      ⟨psi, FTtype1_Ind_irr M maxM Mtype1 psi Mpsi⟩
    let phiIrr : IrreducibleCharacter L ℂ :=
      ⟨phi, FTtype1_Ind_irr L maxL Ltype1 phi Lphi⟩
    have hpsiMem :
        (psiIrr : ClassFunction M ℂ) ∈
          seqIndD (k := ℂ) HM (⊤ : Subgroup HM) ⊥ := by
      simpa only [psiIrr, HM, FTType1SeqIndFamily] using Mpsi
    have hphiMem :
        (phiIrr : ClassFunction L ℂ) ∈
          seqIndD (k := ℂ) HL (⊤ : Subgroup HL) ⊥ := by
      simpa only [phiIrr, HL, FTType1SeqIndFamily] using Lphi
    have hpsiOne : psiIrr 1 = (HM.index : ℂ) := by
      simpa only [psiIrr, HM, FTtype1CoreIndex] using psi1
    have hphiOne : phiIrr 1 = (HL.index : ℂ) := by
      simpa only [phiIrr, HL, FTtype1CoreIndex] using phi1
    have hHMmap : HM.map M.subtype = Fitting_core M := by
      simpa only [HM] using ftt2_fittingIn_map_subtype M
    have hHLmap : HL.map L.subtype = Fitting_core L := by
      simpa only [HL] using ftt2_fittingIn_map_subtype L
    have hsupportM : Dade_support ddM =
        Dade_support (FT_DadeF_hyp M maxM) :=
      ftt2_Dade_support_eq_of_set_eq
        (congrArg subgroupNonidentity hHMmap) ddM
        (FT_DadeF_hyp M maxM)
    have hsupportL : Dade_support ddL =
        Dade_support (FT_DadeF_hyp L maxL) :=
      ftt2_Dade_support_eq_of_set_eq
        (congrArg subgroupNonidentity hHLmap) ddL
        (FT_DadeF_hyp L maxL)
    have hdis : Disjoint (Dade_support ddM) (Dade_support ddL) := by
      rw [hsupportM, hsupportL]
      exact disjoint_Dade_FTtype1 maxM maxL Mtype1 Ltype1 not_MG_L

    have hcross := Dade_sub_lin_nonorthogonal
      (H₁ := HM) (H₂ := HL) (ddA₁ := ddM) (ddA₂ := ddL)
      (disjointA := hdis) (mFT_odd (⊤ : Subgroup G))
      nuM nuL cohTopM cohTopL psiIrr phiIrr
      hpsiMem hphiMem hpsiOne hphiOne

    rcases hcross with hbetaM | hbetaL
    · /- betaM is nonorthogonal to tau1L: this gives the first LM case. -/
      have hbetaMTop : starCharacterPairing
          (Dade (FT_DadeF_hyp M maxM)
            (dadeInducedTrivial (FTType1FittingIn M) - psi))
          (nuL phi) ≠ 0 := by
        simpa only [dadeInd1Beta, HM, ddM,
          ftt2Type1DadeHypothesis, ftt2_fittingIn_map_subtype,
          psiIrr, phiIrr] using hbetaM
      have hbetaMG : starCharacterPairing
          (FTtype1Dade M maxM (FTtype1Bridge M psi))
          (tau₁L phi) ≠ 0 := by
        have ht : starCharacterPairing
            (ftt2TargetMap (dadeInd1Beta HM ddM psi))
            (ftt2TargetMap (nuL phi)) ≠ 0 := by
          rw [ftt2_target_starPairing]
          simpa only [psiIrr, phiIrr] using hbetaM
        have hbetaTarget :
            ftt2TargetMap (dadeInd1Beta HM ddM psi) =
              FTtype1Dade M maxM (FTtype1Bridge M psi) := by
          simpa only [HM] using
            ftt2_target_dadeInd1Beta maxM ddM psi
        have hnuTarget : ftt2TargetMap (nuL phi) = tau₁L phi := by
          simp only [nuL, LinearMap.comp_apply, ftt2_target_source]
        simpa only [hbetaTarget, hnuTarget] using ht
      have hcoreL := coherent_FTtype1_core_ltr
        maxL maxM Ltype1 Mtype1 nuL nuM
        (ftt2Type1Coherence_top cohL) (ftt2Type1Coherence_top cohM)
        phi psi Lphi Mpsi
        (by simpa only [FTtype1CoreIndex] using phi1)
        (by simpa only [FTtype1CoreIndex] using psi1)
        not_LG_M hbetaMTop
      change
        ((((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ)) /
            (FTtype1CoreIndex L : ℝ)) ≤
          (FTtype1CoreIndex M : ℝ) - 1 at hcoreL
      have hboundL :
          ((((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ)) /
            (((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ))) ≤
          (((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ)) - 1 := by
        simpa only [indexLH, indexMK, Nat.cast_mul, mul_comm] using hcoreL
      exact Or.inl ⟨hbetaMG, hboundL⟩

    · /- betaL is nonorthogonal to tau1M: the core bound is exceptional. -/
      have hbetaLTop : starCharacterPairing
          (Dade (FT_DadeF_hyp L maxL)
            (dadeInducedTrivial (FTType1FittingIn L) - phi))
          (nuM psi) ≠ 0 := by
        simpa only [dadeInd1Beta, HL, ddL,
          ftt2Type1DadeHypothesis, ftt2_fittingIn_map_subtype,
          psiIrr, phiIrr] using hbetaL
      have hbetaLG : starCharacterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (tau₁M psi) ≠ 0 := by
        have ht : starCharacterPairing
            (ftt2TargetMap (dadeInd1Beta HL ddL phi))
            (ftt2TargetMap (nuM psi)) ≠ 0 := by
          rw [ftt2_target_starPairing]
          simpa only [psiIrr, phiIrr] using hbetaL
        have hbetaTarget :
            ftt2TargetMap (dadeInd1Beta HL ddL phi) =
              FTtype1Dade L maxL (FTtype1Bridge L phi) := by
          simpa only [HL] using
            ftt2_target_dadeInd1Beta maxL ddL phi
        have hnuTarget : ftt2TargetMap (nuM psi) = tau₁M psi := by
          simp only [nuM, LinearMap.comp_apply, ftt2_target_source]
        simpa only [hbetaTarget, hnuTarget] using ht
      have hcoreM := coherent_FTtype1_core_ltr
        maxM maxL Mtype1 Ltype1 nuM nuL
        (ftt2Type1Coherence_top cohM) (ftt2Type1Coherence_top cohL)
        psi phi Mpsi Lphi
        (by simpa only [FTtype1CoreIndex] using psi1)
        (by simpa only [FTtype1CoreIndex] using phi1)
        not_MG_L hbetaLTop
      change
        ((((Nat.card (Fitting_core M) - 1 : ℕ) : ℝ)) /
            (FTtype1CoreIndex M : ℝ)) ≤
          (FTtype1CoreIndex L : ℝ) - 1 at hcoreM
      have hcoreV :
          ((((Nat.card V - 1 : ℕ) : ℝ)) /
            (((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ))) ≤
          (((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ)) - 1 := by
        simpa only [defK, indexLH, indexMK, Nat.cast_mul, mul_comm]
          using hcoreM
      obtain ⟨hqPrime, hpPrime⟩ :=
        FTtypeP_primes S U W W₁ W₂ defW ctxS.maxS ctxS.StypeP
      have hqOdd : Odd (Nat.card W₁) := mFT_odd W₁
      have hpOdd : Odd (Nat.card W₂) := mFT_odd W₂
      have hPowSwap :
          (Nat.card W₂) ^ (Nat.card W₁ + 1) <
            (Nat.card W₁) ^ (Nat.card W₂ + 1) :=
        ftt2_swapped_prime_power_lt hpPrime hqPrime hpOdd hqOdd hlt
      have hexception := ftt2_exceptional_prime_cards
        hpPrime hqPrime hpOdd hqOdd hlt hCardVnUSwapped hPowSwap hcoreV
      exact Or.inr ⟨hbetaLG, hexception.1, hexception.2⟩


  have hLMArith :
      (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
          ((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ) ≤
        ((Nat.card W₂ * Nat.card W₁ : ℕ) : ℝ) - 1) ∨
      (Nat.card W₁ = 3 ∧ Nat.card W₂ = 5) := by
    rcases LM_cases with hfirst | hsecond
    · exact Or.inl hfirst.2
    · exact Or.inr ⟨hsecond.2.1, hsecond.2.2⟩
  have hCardUnU :
      Nat.card U = nU (Nat.card W₂) (Nat.card W₁) :=
    ftt2_card_U_eq_nU_of_LM ctxS hGalS hlt sUH
      (⟨E, hFrobLE⟩ : FTFrobeniusWithFittingKernel L) defLy hLMArith

  let p : ℕ := Nat.card W₂
  let q : ℕ := Nat.card W₁
  have indexLH' : FTtype1CoreIndex L = p * q := by
    simpa only [p, q] using indexLH
  have indexMK' : FTtype1CoreIndex M = q * p := by
    simpa only [p, q] using indexMK
  have hCardVnUSwapped' : Nat.card V = nU q p := by
    simpa only [p, q] using hCardVnUSwapped
  have hCardUnU' : Nat.card U = nU p q := by
    simpa only [p, q] using hCardUnU
  have hUV' : (Nat.card U - 1) / q < (Nat.card V - 1) / p := by
    simpa only [p, q] using hUV
  obtain ⟨hqPrime0, hpPrime0⟩ :=
    FTtypeP_pair_primes S T W W₁ W₂ defW pairST
  have hpPrime : p.Prime := by simpa only [p] using hpPrime0
  have hqPrime : q.Prime := by simpa only [q] using hqPrime0
  have hpqNe : p ≠ q := by
    simpa only [p, q] using pairST.cyclic_ti.factor_card_ne.symm
  have hpqCoprime : Nat.Coprime p q :=
    (Nat.coprime_primes hpPrime hqPrime).mpr hpqNe

  have hCoreL : Fitting_core L = U := by
    by_contra hCoreNe
    let x : ℕ := (U.subgroupOf (Fitting_core L)).index
    have hxgt : 1 < x := by
      dsimp only [x]
      apply Subgroup.one_lt_index_of_ne_top
      intro htop
      apply hCoreNe
      exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) sUH
    have hCoreCard :
        Nat.card (Fitting_core L) = Nat.card U * x := by
      dsimp only [x]
      simpa only [MathlibSupport.natCard_subgroupOf_eq sUH] using
        (U.subgroupOf (Fitting_core L)).card_mul_index.symm

    have hFrobDecL := ftt2_frobeniusIn_decomposition hFrobLE
    have hCoreDvd : p * q ∣ Nat.card (Fitting_core L) - 1 := by
      have hraw := ftt2_frobenius_pred_dvd hFrobDecL
      have hcompCard :
          Nat.card (E.subgroupOf L) = FTtype1CoreIndex L := by
        change Nat.card (E.subgroupOf L) =
          ((Fitting_core L).subgroupOf L).index
        exact hFrobDecL.isComplement.symm.index_eq_card.symm
      simpa only [MathlibSupport.natCard_subgroupOf_eq (Fcore_sub L),
        hcompCard, indexLH'] using hraw
    have hCoreMod :
        Nat.ModEq (p * q) (Nat.card (Fitting_core L)) 1 := by
      exact ((Nat.modEq_iff_dvd'
        (Nat.card_pos : 1 ≤ Nat.card (Fitting_core L))).2 hCoreDvd).symm

    have hqDvdU : q ∣ Nat.card U - 1 := by
      simpa only [q] using (FTtypeP_bridge_facts ctxS).2.2.2.2
    have hUmodQ : Nat.ModEq q (Nat.card U) 1 := by
      exact ((Nat.modEq_iff_dvd'
        (Nat.card_pos : 1 ≤ Nat.card U)).2 hqDvdU).symm
    have hUmodP : Nat.ModEq p (Nat.card U) 1 := by
      rw [hCardUnU']
      exact ftt2_nU_modEq_one hqPrime.pos
    have hUmodPQ : Nat.ModEq (p * q) (Nat.card U) 1 :=
      (Nat.modEq_and_modEq_iff_modEq_mul hpqCoprime).mp
        ⟨hUmodP, hUmodQ⟩
    have hxmod : Nat.ModEq (p * q) x 1 := by
      have hCoreMod' := hCoreMod
      rw [hCoreCard] at hCoreMod'
      simpa using (hUmodPQ.mul_right x).symm.trans hCoreMod'
    have hmx : p * q < x := by
      have := hxmod.symm.add_le_of_lt hxgt
      omega

    have hFrobUW₁ : PTypeFrobeniusProduct U W₁ :=
      (FTtypeP_facts ctxS).2.2.1
    have hUgt : 1 < Nat.card U := by
      have hker : 1 < Nat.card (U.subgroupOf (U ⊔ W₁)) :=
        (U.subgroupOf (U ⊔ W₁)).one_lt_card_iff_ne_bot.mpr
          hFrobUW₁.kernel_ne_bot
      simpa only [MathlibSupport.natCard_subgroupOf_eq le_sup_left] using hker
    have hmU : p * q < Nat.card U := by
      have := hUmodPQ.symm.add_le_of_lt hUgt
      omega

    rcases LM_cases with ⟨_haML, hUpper⟩ |
        ⟨haLM, hqThree0, hpFive0⟩
    · have hUpper' :
          (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
              ((p * q : ℕ) : ℝ) ≤
            ((p * q : ℕ) : ℝ) - 1) := by
        simpa only [indexLH', indexMK', Nat.mul_comm] using hUpper
      have hmPos : 0 < p * q := Nat.mul_pos hpPrime.pos hqPrime.pos
      have hmPosR : (0 : ℝ) < ((p * q : ℕ) : ℝ) := by
        exact_mod_cast hmPos
      have hmOneR : (1 : ℝ) ≤ ((p * q : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ p * q from hmPos)
      have hUpperMul :
          (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) ≤
            ((p * q : ℕ) : ℝ) *
              (((p * q : ℕ) : ℝ) - 1)) := by
        simpa only [mul_comm] using (div_le_iff₀ hmPosR).mp hUpper'
      rw [Nat.cast_sub
          (Nat.card_pos : 1 ≤ Nat.card (Fitting_core L)),
        hCoreCard, Nat.cast_mul] at hUpperMul
      norm_num at hUpperMul
      have hmUReal :
          ((p * q : ℕ) : ℝ) < (Nat.card U : ℝ) := by
        exact_mod_cast hmU
      have hmXReal : ((p * q : ℕ) : ℝ) < (x : ℝ) := by
        exact_mod_cast hmx
      have hUPosR : (0 : ℝ) < (Nat.card U : ℝ) := by positivity
      have hmulLower :
          ((p * q : ℕ) : ℝ) * ((p * q : ℕ) : ℝ) <
            (Nat.card U : ℝ) * (x : ℝ) := by
        calc
          ((p * q : ℕ) : ℝ) * ((p * q : ℕ) : ℝ) <
              (Nat.card U : ℝ) * ((p * q : ℕ) : ℝ) :=
            mul_lt_mul_of_pos_right hmUReal hmPosR
          _ < (Nat.card U : ℝ) * (x : ℝ) :=
            mul_lt_mul_of_pos_left hmXReal hUPosR
      norm_num [Nat.cast_mul] at hmOneR hmulLower
      nlinarith
    · have hqThree : q = 3 := by
        simpa only [q] using hqThree0
      have hpFive : p = 5 := by
        simpa only [p] using hpFive0
      have hvb : (Nat.card V - 1) / p <
          (Nat.card (Fitting_core L) - 1) / FTtype1CoreIndex L := by
        rw [hCardVnUSwapped', hCoreCard, hCardUnU', indexLH',
          hqThree, hpFive]
        norm_num [nU, hpFive, hqThree] at hmx ⊢
        omega
      have hub : (Nat.card U - 1) / q <
          (Nat.card (Fitting_core L) - 1) / FTtype1CoreIndex L :=
        hUV'.trans hvb
      have cohL' : coherent_with
          (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
          (nonidentitySet L) (FTtype1Dade L maxNU_L.1) tau₁L := by
        simpa only using cohL
      obtain ⟨_hindex, eps, chi, hchi, hshape0⟩ :=
        FTtype2_support_coherence ctxS ctxT pairST Stype2 maxNU_L
          tau₁L phi cohL' Lphi phi1
          (by simpa only [q] using hub)
          (by simpa only [p] using hvb)
      have hshape :
          FTtype1Dade L maxL (FTtype1Bridge L phi) =
            (∑ i, ∑ j,
              if eps i j then -(ctxS.eta i j) else ctxS.eta i j) - chi := by
        simpa only using hshape0

      have bridgeSM :=
        FTtypeI_bridge_facts ctxS M maxM Mtype1 tau₁M psi
          cohM Mpsi psi1
      have hTauMVirtual : ClassFunction.IsVirtual (tau₁M psi) :=
        cohM.mapsToVirtual psi (AddSubgroup.subset_closure Mpsi)
      have hEtaPairing (i : IrreducibleCharacter W₁ ℂ)
          (j : IrreducibleCharacter W₂ ℂ) :
          characterPairing (ctxS.eta i j) (tau₁M psi) = 0 := by
        rw [characterPairing_comm]
        exact bridgeSM.2.1 _ ⟨psi, Mpsi, rfl⟩ _
          (ftt2_eta_mem_cyclicImageFamily ctxS i j)
      have hEtaOrtho (i : IrreducibleCharacter W₁ ℂ)
          (j : IrreducibleCharacter W₂ ℂ) :
          starCharacterPairing (ctxS.eta i j) (tau₁M psi) = 0 := by
        rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          (ftt2_eta_virtual ctxS i j) hTauMVirtual,
          hEtaPairing]
      have hSignedSumZero :
          starCharacterPairing
            (∑ i, ∑ j,
              if eps i j then -(ctxS.eta i j) else ctxS.eta i j)
            (tau₁M psi) = 0 := by
        rw [ftt2_starPairing_fintype_sum_left]
        apply Finset.sum_eq_zero
        intro i _hi
        rw [ftt2_starPairing_fintype_sum_left]
        apply Finset.sum_eq_zero
        intro j _hj
        by_cases hij : eps i j
        · rw [if_pos hij, ← neg_one_smul ℂ (ctxS.eta i j),
            starCharacterPairing_smul_left, hEtaOrtho]
          simp
        · rw [if_neg hij, hEtaOrtho]

      let tauLTop := ftt2SourceMap.comp tau₁L
      let tauMTop := ftt2SourceMap.comp tau₁M
      have cohLTop := ftt2Type1Coherence_top cohL
      have cohMTop := ftt2Type1Coherence_top cohM
      have hOrthoTop := coherent_FTtype1_ortho
        maxM maxL Mtype1 Ltype1 tauMTop tauLTop
        (by simpa only [tauMTop] using cohMTop)
        (by simpa only [tauLTop] using cohLTop) not_MG_L
      have hOrthoG (xi : ClassFunction M ℂ)
          (hxi : xi ∈ FTType1SeqIndFamily M)
          (eta : ClassFunction L ℂ)
          (heta : eta ∈ FTType1SeqIndFamily L) :
          characterPairing (tau₁M xi) (tau₁L eta) = 0 := by
        have htop := hOrthoTop xi hxi eta heta
        change characterPairing
          (ftt2SourceMap (tau₁M xi))
          (ftt2SourceMap (tau₁L eta)) = 0 at htop
        calc
          characterPairing (tau₁M xi) (tau₁L eta) =
              characterPairing
                (ftt2SourceMap (tau₁M xi))
                (ftt2SourceMap (tau₁L eta)) :=
            (ftt2_source_pairing _ _).symm
          _ = 0 := htop
      have hInvL : ClassFunction.inverseLinear phi ∈
          FTType1SeqIndFamily L := by
        simpa only [FTType1SeqIndFamily] using
          seqInd_inverse_mem (k := ℂ) (FTType1FittingIn L)
            (⊤ : Subgroup (FTType1FittingIn L)) ⊥ Lphi
      have hPhiVirtual : ClassFunction.IsVirtual (tau₁L phi) :=
        cohL.mapsToVirtual phi (AddSubgroup.subset_closure Lphi)
      have hInvVirtual :
          ClassFunction.IsVirtual
            (tau₁L (ClassFunction.inverseLinear phi)) :=
        cohL.mapsToVirtual _ (AddSubgroup.subset_closure hInvL)
      have hChiZero : starCharacterPairing chi (tau₁M psi) = 0 := by
        rcases hchi with hchi | hchi
        · rw [hchi,
            PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
              hPhiVirtual hTauMVirtual,
            characterPairing_comm]
          exact hOrthoG psi Mpsi phi Lphi
        · rw [hchi, ← neg_one_smul ℂ,
            starCharacterPairing_smul_left,
            PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
              hInvVirtual hTauMVirtual,
            characterPairing_comm,
            hOrthoG psi Mpsi _ hInvL]
          simp
      apply haLM
      rw [hshape, ftt2_starPairing_sub_left,
        hSignedSumZero, hChiZero, sub_zero]

  exact hU_not_characteristic (by
    rw [hCoreL, Subgroup.subgroupOf_self]
    exact Subgroup.topCharacteristic)



end

end Submission.OddOrder.PF
