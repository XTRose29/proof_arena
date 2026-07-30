import Submission.OddOrder.PF.Section11.FTType34StructureNonorthogonalityCore

/-!
# Peterfalvi (11.8): nonorthogonality

This module normalizes the two coherence branches and derives the final
nonorthogonality contradiction.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTType345ConstantsInternal
open PTypeCoreContextInternal
open scoped BigOperators Classical Pointwise IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {M U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftType34NonorthTauFintypeOfFinite
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

local instance ftType34NonorthTauInvertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace FTType34StructureInternal

/-! The first phase works directly with the raw top-valued Dade map. -/

private theorem ftType34_HUInM_normal34
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.HUInM.Normal := by
  have hHU : base.HU = derivedWithin M := by
    calc
      base.HU = FTcore M := base.FTcore_eq_HU.symm
      _ = derivedWithin M := FTcore_type_gt2 M base.type_gt_two
  rw [FTType34Base.HUInM, hHU]
  exact TypeSpecInternal.derivedWithin_normal16 M

/-! ## Pairing algebra shared by the remaining nonorthogonality phases -/

private theorem ftType34_pairing_sub_left34
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingRight c (a - b) = _
  exact map_sub (characterPairingRight c) a b

private theorem ftType34_pairing_sub_right34
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingLeft a (b - c) = _
  exact map_sub (characterPairingLeft a) b c

private theorem ftType34_pairing_neg_left34
    {Q : Type} [Group Q] [Fintype Q]
    (a b : ClassFunction Q ℂ) :
    characterPairing (-a) b = -characterPairing a b := by
  change characterPairingRight b (-a) = _
  exact map_neg (characterPairingRight b) a

private theorem ftType34_pairing_neg_right34
    {Q : Type} [Group Q] [Fintype Q]
    (a b : ClassFunction Q ℂ) :
    characterPairing a (-b) = -characterPairing a b := by
  change characterPairingLeft a (-b) = _
  exact map_neg (characterPairingLeft a) b

/-! ## Source support for the distinguished bridge and the `S₁` lattice -/

private theorem ftType34S1_mem_referenceFamily34
    (base : FTType34Base M U W W₁ W₂ defW)
    {zeta : ClassFunction M ℂ}
    (hzeta : zeta ∈ ftType34S1 base) :
    zeta ∈ FTType345ConstantsInternal.ftType345InducedFamily10 M := by
  have hHU : base.HU = derivedWithin M := by
    calc
      base.HU = FTcore M := base.FTcore_eq_HU.symm
      _ = derivedWithin M := FTcore_type_gt2 M base.type_gt_two
  have hK : base.HUInM =
      FTType345ConstantsInternal.ftType345DerivedInM M := by
    simp only [FTType34Base.HUInM,
      FTType345ConstantsInternal.ftType345DerivedInM, hHU]
  rw [ftType34S1, ftType34Layer] at hzeta
  rw [FTType345ConstantsInternal.ftType345InducedFamily10, ← hK]
  exact seqIndS base.HUInM
    (Iirr_kerDS (k := ℂ)
      (bot_le : (⊥ : Subgroup base.HUInM) ≤ base.HCInHU)
      (le_rfl : (⊤ : Subgroup base.HUInM) ≤ ⊤)) hzeta

private def ftType34S1_referenceChoice34
    (base : FTType34Base M U W W₁ W₂ defW)
    {zeta : ClassFunction M ℂ}
    (hzeta : zeta ∈ ftType34S1 base) :
    FTType345ReferenceChoice M W₁ zeta where
  irreducible := ftType34S1_irreducible34 base zeta hzeta
  mem_calS := ftType34S1_mem_referenceFamily34 base hzeta
  degree := ftType34S1_degree34 base zeta hzeta

private theorem ftType34_mu_ortho_S1_34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base) :
    characterPairing (mu34 base j) zeta = 0 := by
  classical
  let hzetaRef : FTType345ReferenceChoice M W₁ zeta :=
    ftType34S1_referenceChoice34 base hzeta
  rw [mu34, base.primeTI.primeTIRed_eq_sum]
  change characterPairingRight zeta
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.primeTI.primeTICharacter base.isoM i j) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
    base.MtypeP zeta hzetaRef i j

private theorem ftType34_muZero_ortho_S1_34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base) :
    characterPairing (muZero34 base) zeta = 0 := by
  simpa only [muZero34] using
    ftType34_mu_ortho_S1_34 base
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
      zeta hzeta

private theorem ftType34_bridgeZero_supportedOn_FTsupport0_34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base) :
    muZero34 base - zeta ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
  let K : Subgroup M :=
    FTType345ConstantsInternal.ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  let hzetaRef := ftType34S1_referenceChoice34 base hzeta
  have hindex : K.index = Nat.card W₁ := by
    have houter : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := base.MtypeP.1.2.2.2
    calc
      K.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq houter.2.1
  have hsmall := cfInd1_sub_lin_on (k := ℂ) K hzetaRef.mem_calS (by
    rw [hzetaRef.degree, hindex])
  rw [← base.primeTI.prTIred0 base.isoM] at hsmall
  rw [ClassFunction.mem_supportedOn_iff] at hsmall ⊢
  intro x hx
  apply hsmall x
  intro hxK
  apply hx
  apply FTsupp1_sub0 base.maxM
  rw [FTsupp1_type_gt2 M base.type_gt_two]
  exact ⟨hxK.1, fun hxOne ↦ hxK.2 (Subtype.ext hxOne)⟩

private theorem ftType34_HUsharp_supportedOn_FTsupport0_34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ ClassFunction.supportedOn
      (subgroupNonidentity base.HUInM)) :
    phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
  have hHU : base.HU = derivedWithin M := by
    calc
      base.HU = FTcore M := base.FTcore_eq_HU.symm
      _ = derivedWithin M := FTcore_type_gt2 M base.type_gt_two
  rw [ClassFunction.mem_supportedOn_iff] at hphi ⊢
  intro x hx
  apply hphi x
  intro hxHU
  apply hx
  apply FTsupp1_sub0 base.maxM
  rw [FTsupp1_type_gt2 M base.type_gt_two]
  refine ⟨?_, ?_⟩
  · have hxmem : (x : G) ∈ base.HU := hxHU.1
    rwa [hHU] at hxmem
  · intro hxOne
    exact hxHU.2 (Subtype.ext hxOne)

private theorem ftType34S1_sub_supportedOn_FTsupport0_34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi psi : ClassFunction M ℂ}
    (hphi : phi ∈ ftType34S1 base)
    (hpsi : psi ∈ ftType34S1 base) :
    phi - psi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
  letI : base.HUInM.Normal := ftType34_HUInM_normal34 base
  have hweighted := sub_seqInd_on base.HUInM
    (show phi ∈ seqInd (k := ℂ) base.HUInM
        (Iirr_kerD (k := ℂ) ⊤ base.HCInHU) by
      simpa only [ftType34S1, ftType34Layer, seqIndD] using hphi)
    (show psi ∈ seqInd (k := ℂ) base.HUInM
        (Iirr_kerD (k := ℂ) ⊤ base.HCInHU) by
      simpa only [ftType34S1, ftType34Layer, seqIndD] using hpsi)
  have hqne : (base.q : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr base.q_prime.ne_zero
  rw [ftType34S1_degree34 base phi hphi,
    ftType34S1_degree34 base psi hpsi] at hweighted
  have hfactor : (base.q : ℂ) • (phi - psi) =
      (base.q : ℂ) • phi - (base.q : ℂ) • psi :=
    smul_sub _ _ _
  rw [← hfactor, ClassFunction.mem_supportedOn_iff] at hweighted
  have hraw : phi - psi ∈ ClassFunction.supportedOn
      (subgroupNonidentity base.HUInM) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxValue := hweighted x hx
    simp only [ClassFunction.smul_apply, smul_eq_mul] at hxValue
    exact (mul_eq_zero.mp hxValue).resolve_left hqne
  exact ftType34_HUsharp_supportedOn_FTsupport0_34 base hraw

/-! ## Integral Dade and cyclic-column adapters -/

private theorem ftType34_fintype_sum_virtual34
    {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ)
    (hf : ∀ i, ClassFunction.IsVirtual (f i)) :
    ClassFunction.IsVirtual (∑ i, f i) := by
  classical
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty =>
      simpa using ClassFunction.IsVirtual.zero (H := Q)
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i).add ih

private theorem ftType34_cyclicTIImageTop_virtual34
    (base : FTType34Base M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (base.isoG.cyclicTIImage (i, j)) := by
  let chi : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW i j
  let z : VirtualCharacter W ℂ := Finsupp.single chi 1
  refine ⟨base.isoG.virtualMap z, ?_⟩
  calc
    VirtualCharacter.realize (base.isoG.virtualMap z) =
        base.isoG.linearMap (VirtualCharacter.realize z) :=
      base.isoG.realize_virtualMap z
    _ = base.isoG.cyclicTIImage (i, j) := by
      simp [z, chi, CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible]

private theorem ftType34_cyclicColumnTop_virtual34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage (i, j)) := by
  exact ftType34_fintype_sum_virtual34 _
    (fun i ↦ ftType34_cyclicTIImageTop_virtual34 base i j)

private theorem ftType34_dade_virtual34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction M ℂ}
    (hphiVirtual : ClassFunction.IsVirtual phi)
    (hphiSupport : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M}) :
    ClassFunction.IsVirtual (ftType345Tau base.maxM phi) := by
  obtain ⟨z, hz⟩ := hphiVirtual
  have hzSupport : VirtualCharacter.realize z ∈
      ClassFunction.supportedOn {x : M | (x : G) ∈ FTsupport0 M} := by
    simpa only [hz] using hphiSupport
  obtain ⟨beta, hbeta, _⟩ :=
    (Dade_Zisometry (FT_Dade0_hyp M base.maxM)).2 z hzSupport
  exact ⟨beta, by simpa only [hz] using hbeta.symm⟩

private theorem ftType34_dade_pairing34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi psi : ClassFunction M ℂ}
    (hphiVirtual : ClassFunction.IsVirtual phi)
    (hpsiVirtual : ClassFunction.IsVirtual psi)
    (hphiSupport : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M})
    (hpsiSupport : psi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M}) :
    characterPairing (ftType345Tau base.maxM phi)
        (ftType345Tau base.maxM psi) =
      characterPairing phi psi := by
  have hDphiVirtual : ClassFunction.IsVirtual
      (ftType345Tau base.maxM phi) :=
    ftType34_dade_virtual34 base hphiVirtual hphiSupport
  have hDpsiVirtual : ClassFunction.IsVirtual
      (ftType345Tau base.maxM psi) :=
    ftType34_dade_virtual34 base hpsiVirtual hpsiSupport
  calc
    characterPairing (ftType345Tau base.maxM phi)
        (ftType345Tau base.maxM psi) =
        starCharacterPairing (ftType345Tau base.maxM phi)
          (ftType345Tau base.maxM psi) :=
      (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hDphiVirtual hDpsiVirtual).symm
    _ = starCharacterPairing phi psi :=
      Dade_isometry (FT_Dade0_hyp M base.maxM)
        phi psi hphiSupport hpsiSupport
    _ = characterPairing phi psi :=
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hphiVirtual hpsiVirtual

private theorem ftType34_cyclicColumnTop_entry34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing
        (∑ k : IrreducibleCharacter W₁ ℂ,
          base.isoG.cyclicTIImage (k, j₀))
        (base.isoG.cyclicTIImage (i, j)) =
      if j = j₀ then 1 else 0 := by
  classical
  change characterPairingRight (base.isoG.cyclicTIImage (i, j))
      (∑ k : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage (k, j₀)) = _
  rw [map_sum]
  by_cases hj : j = j₀
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · change characterPairing
          (base.isoG.cyclicTIImage (i, j₀))
          (base.isoG.cyclicTIImage (i, j₀)) = 1
      rw [base.isoG.characterPairing_cyclicTIImage, if_pos rfl]
    · intro k _ hki
      change characterPairing
          (base.isoG.cyclicTIImage (k, j₀))
          (base.isoG.cyclicTIImage (i, j₀)) = 0
      rw [base.isoG.characterPairing_cyclicTIImage, if_neg]
      exact fun h ↦ hki (congrArg Prod.fst h)
    · simp
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k _
    change characterPairing
        (base.isoG.cyclicTIImage (k, j₀))
        (base.isoG.cyclicTIImage (i, j)) = 0
    rw [base.isoG.characterPairing_cyclicTIImage, if_neg]
    intro h
    exact hj (congrArg Prod.snd h).symm

private theorem ftType34_cyclicColumnTop_self34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing
        (∑ i : IrreducibleCharacter W₁ ℂ,
          base.isoG.cyclicTIImage (i, j))
        (∑ i : IrreducibleCharacter W₁ ℂ,
          base.isoG.cyclicTIImage (i, j)) =
      (base.q : ℂ) := by
  classical
  letI : IsCyclic W₁ := base.primeTI.complement_cyclic
  have hcard : Fintype.card (IrreducibleCharacter W₁ ℂ) = base.q := by
    simpa only [FTType34Base.q] using
      (IrreducibleCharacter.card_eq_natCard_of_isCyclic
        (C := W₁) (k := ℂ))
  have heach (i : IrreducibleCharacter W₁ ℂ) :
      characterPairingLeft
          (∑ k : IrreducibleCharacter W₁ ℂ,
            base.isoG.cyclicTIImage (k, j))
          (base.isoG.cyclicTIImage (i, j)) = 1 := by
    change characterPairing
        (∑ k : IrreducibleCharacter W₁ ℂ,
          base.isoG.cyclicTIImage (k, j))
        (base.isoG.cyclicTIImage (i, j)) = 1
    simpa only [if_pos] using
      ftType34_cyclicColumnTop_entry34 base j i j
  change characterPairingLeft
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage (i, j))
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage (i, j)) = _
  rw [map_sum]
  simp only [heach,
    Finset.sum_const, Finset.card_univ, hcard, nsmul_eq_mul, mul_one]

private theorem ftType34_coherent_ortho_etaTop34
    (base : FTType34Base M U W W₁ W₂ defW)
    {S : Set (ClassFunction M ℂ)}
    {nu : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ}
    (hS : cfConjC_subset S (FTtypePKernelLayer base.primeDade))
    (hnu : coherent_with S (nonidentitySet M)
      (ftType345Tau base.maxM) nu)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ S)
    (hirr : IsIrreducibleCharacter M ℂ phi)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (nu phi) (base.isoG.cyclicTIImage (i, j)) = 0 := by
  have hraw := coherent_ortho_cycTIiso
    base.primeDade base.isoM base.isoG (mFT_odd M)
    hS hnu hphi hirr (IrreducibleCharacter.cyclicTICharacter defW i j)
  simpa only [CyclicTIIsometryData.cyclicTIImage,
    CyclicTIIsometryData.cyclicTISourceIrreducible] using hraw

/-! ## Unit-norm virtual characters -/

private theorem ftType34_exists_signed_irreducible34
    {Q : Type} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hnorm : characterPairing phi phi = 1) :
    ∃ (chi : IrreducibleCharacter Q ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        phi = (epsilon : ℂ) • (chi : ClassFunction Q ℂ) := by
  obtain ⟨z, hz⟩ := hphi
  have hnormZ : normSq z = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self, hz, hnorm]
    norm_num
  obtain ⟨chi, epsilon, hepsilon, hsingle⟩ :=
    eq_signed_single_of_normSq_eq_one z hnormZ
  refine ⟨chi, epsilon, hepsilon, ?_⟩
  rw [← hz, hsingle, VirtualCharacter.realize_single]

private theorem ftType34_signed_irreducible_pivot34
    {Q : Type} [Group Q] [Fintype Q]
    {f g h : ClassFunction Q ℂ}
    {chi psi theta : IrreducibleCharacter Q ℂ}
    {epsilon delta kappa : ℤ}
    (hepsilon : IsSign epsilon)
    (hdelta : IsSign delta)
    (hkappa : IsSign kappa)
    (hf : f = (epsilon : ℂ) • (chi : ClassFunction Q ℂ))
    (hg : g = (delta : ℂ) • (psi : ClassFunction Q ℂ))
    (hh : h = (kappa : ℂ) • (theta : ClassFunction Q ℂ))
    (hgh : characterPairing g h = 0)
    (hdiff : characterPairing f h - characterPairing f g = -1) :
    f = g ∨ f = -h := by
  subst f
  subst g
  subst h
  by_cases hchiPsi : chi = psi
  · subst psi
    have hchiTheta : chi ≠ theta := by
      intro h
      subst theta
      have hself : characterPairing
          (chi : ClassFunction Q ℂ) (chi : ClassFunction Q ℂ) = 1 := by
        rw [IrreducibleCharacter.characterPairing_eq_ite, if_pos rfl]
      have hzero : (kappa : ℂ) * (delta : ℂ) = 0 := by
        simpa only [characterPairing_smul_left,
          characterPairing_smul_right,
          hself, mul_one] using hgh
      exact (mul_ne_zero
        (Int.cast_ne_zero.mpr (isSign_ne_zero hkappa))
        (Int.cast_ne_zero.mpr (isSign_ne_zero hdelta))) hzero
    have hchiThetaPair : characterPairing
        (chi : ClassFunction Q ℂ) (theta : ClassFunction Q ℂ) = 0 := by
      rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg hchiTheta]
    have hself : characterPairing
        (chi : ClassFunction Q ℂ) (chi : ClassFunction Q ℂ) = 1 := by
      rw [IrreducibleCharacter.characterPairing_eq_ite, if_pos rfl]
    have hrel : (delta : ℂ) * (epsilon : ℂ) = 1 := by
      have hrel' : -((delta : ℂ) * (epsilon : ℂ)) = -1 := by
        simpa only [characterPairing_smul_left,
          characterPairing_smul_right,
          hchiThetaPair, hself, mul_zero, mul_one, zero_sub] using hdiff
      exact neg_inj.mp hrel'
    have hdeltaSq : (delta : ℂ) * (delta : ℂ) = 1 := by
      rcases hdelta with rfl | rfl <;> norm_num
    have hscalar : (epsilon : ℂ) = (delta : ℂ) := by
      calc
        (epsilon : ℂ) = 1 * (epsilon : ℂ) := (one_mul _).symm
        _ = ((delta : ℂ) * (delta : ℂ)) * (epsilon : ℂ) := by
          rw [hdeltaSq]
        _ = (delta : ℂ) * ((delta : ℂ) * (epsilon : ℂ)) := by
          ring
        _ = (delta : ℂ) * 1 := by rw [hrel]
        _ = (delta : ℂ) := mul_one _
    exact Or.inl (by rw [hscalar])
  · have hchiTheta : chi = theta := by
      by_contra hne
      have hchiThetaPair : characterPairing
          (chi : ClassFunction Q ℂ) (theta : ClassFunction Q ℂ) = 0 := by
        rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg hne]
      have hchiPsiPair : characterPairing
          (chi : ClassFunction Q ℂ) (psi : ClassFunction Q ℂ) = 0 := by
        rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg hchiPsi]
      have hbad : (0 : ℂ) = -1 := by
        simpa only [characterPairing_smul_left,
          characterPairing_smul_right,
          hchiThetaPair, hchiPsiPair, mul_zero, sub_self] using hdiff
      norm_num at hbad
    subst theta
    have hself : characterPairing
        (chi : ClassFunction Q ℂ) (chi : ClassFunction Q ℂ) = 1 := by
      rw [IrreducibleCharacter.characterPairing_eq_ite, if_pos rfl]
    have hchiPsiPair : characterPairing
        (chi : ClassFunction Q ℂ) (psi : ClassFunction Q ℂ) = 0 := by
      rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg hchiPsi]
    have hrel : (kappa : ℂ) * (epsilon : ℂ) = -1 := by
      simpa only [characterPairing_smul_left,
        characterPairing_smul_right,
        hself, hchiPsiPair, mul_one, mul_zero, sub_zero] using hdiff
    have hkappaSq : (kappa : ℂ) * (kappa : ℂ) = 1 := by
      rcases hkappa with rfl | rfl <;> norm_num
    have hscalar : (epsilon : ℂ) = -(kappa : ℂ) := by
      calc
        (epsilon : ℂ) = 1 * (epsilon : ℂ) := (one_mul _).symm
        _ = ((kappa : ℂ) * (kappa : ℂ)) * (epsilon : ℂ) := by
          rw [hkappaSq]
        _ = (kappa : ℂ) * ((kappa : ℂ) * (epsilon : ℂ)) := by
          ring
        _ = (kappa : ℂ) * (-1 : ℂ) := by rw [hrel]
        _ = -(kappa : ℂ) := by ring
    exact Or.inr (by rw [hscalar]; module)

/-! ## Direct normalization of the top-valued `S₁` coherence -/

set_option maxHeartbeats 800000 in
private theorem ftType34_choose_tau1_aligned_top34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base)
    (hprojection : eqProjection34 base (dadeBridgeZero34 base zeta)
      (etaColumn34 base
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))) :
    ∃ tau1Top : ClassFunction M ℂ →ₗ[ℂ]
        ClassFunction (⊤ : Subgroup G) ℂ,
      coherent_with
          (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
          (nonidentitySet M) (ftType345Tau base.maxM) tau1Top ∧
        ftType345Tau base.maxM
            (base.primeTI.primeTIRed base.isoM
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ) - zeta) =
          (∑ i : IrreducibleCharacter W₁ ℂ,
              base.isoG.cyclicTIImage
                (i, (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ))) -
            tau1Top zeta := by
  classical
  let j₀ : IrreducibleCharacter W₂ ℂ :=
    IrreducibleCharacter.trivial
  let bridge : ClassFunction M ℂ := muZero34 base - zeta
  let psi : ClassFunction (⊤ : Subgroup G) ℂ :=
    ftType345Tau base.maxM bridge
  let col : ClassFunction (⊤ : Subgroup G) ℂ :=
    ∑ i : IrreducibleCharacter W₁ ℂ,
      base.isoG.cyclicTIImage (i, j₀)
  let chi : ClassFunction (⊤ : Subgroup G) ℂ := col - psi

  have hzetaIrr : IsIrreducibleCharacter M ℂ zeta :=
    ftType34S1_irreducible34 base zeta hzeta
  have hzetaVirtual : ClassFunction.IsVirtual zeta :=
    (ftType34S1_subcoherent34 base).source_virtual zeta hzeta
  have hbridgeVirtual : ClassFunction.IsVirtual bridge := by
    simpa only [bridge, ftType34Bridge0] using
      ftType34_bridgeZero_virtual34 base zeta hzeta
  have hbridgeSupport : bridge ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
    simpa only [bridge] using
      ftType34_bridgeZero_supportedOn_FTsupport0_34 base zeta hzeta
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    exact ftType34_dade_virtual34 base hbridgeVirtual hbridgeSupport
  have hcolVirtual : ClassFunction.IsVirtual col := by
    simpa only [col] using ftType34_cyclicColumnTop_virtual34 base j₀
  have hchiVirtual : ClassFunction.IsVirtual chi := by
    exact hcolVirtual.sub hpsiVirtual

  have hmuNorm : characterPairing (muZero34 base) (muZero34 base) =
      (base.q : ℂ) := by
    simpa only [muZero34, mu34, j₀, FTType34Base.q] using
      base.primeTI.cfnorm_prTIred base.isoM j₀
  have hmuZeta : characterPairing (muZero34 base) zeta = 0 :=
    ftType34_muZero_ortho_S1_34 base zeta hzeta
  have hzetaMu : characterPairing zeta (muZero34 base) = 0 := by
    rw [characterPairing_comm, hmuZeta]
  have hzetaNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self ⟨zeta, hzetaIrr⟩
  have hbridgeNorm : characterPairing bridge bridge =
      (base.q + 1 : ℂ) := by
    simp only [bridge, ftType34_pairing_sub_left34,
      ftType34_pairing_sub_right34]
    rw [hmuNorm, hmuZeta, hzetaMu, hzetaNorm]
    push_cast
    ring
  have hpsiNorm : characterPairing psi psi = (base.q + 1 : ℂ) := by
    exact (ftType34_dade_pairing34 base
      hbridgeVirtual hbridgeVirtual hbridgeSupport hbridgeSupport).trans
      hbridgeNorm

  have hprojection' :=
    (eqProjection34_iff base (dadeBridgeZero34 base zeta)
      (etaColumn34 base j₀)).mp hprojection
  have hpsiEta (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing psi (base.isoG.cyclicTIImage (i, j₀)) = 1 := by
    have hi := hprojection' i j₀
    rw [characterPairing_etaColumn34, if_pos rfl] at hi
    have hiRaw :
        characterPairing
          (ftType345Tau base.maxM (muZero34 base - zeta))
          (base.isoG.cyclicTIImage (i, j₀)) = 1 := by
      change characterPairing
          (base.targetMap
            (ftType345Tau base.maxM (muZero34 base - zeta)))
          (base.targetMap (base.isoG.cyclicTIImage (i, j₀))) = 1 at hi
      rw [base.targetMap_pairing] at hi
      exact hi
    simpa only [psi, bridge] using hiRaw
  letI : IsCyclic W₁ := base.primeTI.complement_cyclic
  have hcardW₁ : Fintype.card (IrreducibleCharacter W₁ ℂ) = base.q := by
    simpa only [FTType34Base.q] using
      (IrreducibleCharacter.card_eq_natCard_of_isCyclic
        (C := W₁) (k := ℂ))
  have hcolPsi : characterPairing col psi = (base.q : ℂ) := by
    change characterPairingRight psi
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage (i, j₀)) = _
    rw [map_sum]
    have heach : ∀ i : IrreducibleCharacter W₁ ℂ,
        characterPairingRight psi
          (base.isoG.cyclicTIImage (i, j₀)) = 1 := by
      intro i
      change characterPairing
          (base.isoG.cyclicTIImage (i, j₀)) psi = 1
      rw [characterPairing_comm, hpsiEta i]
    simp only [heach, Finset.sum_const, Finset.card_univ,
      hcardW₁, nsmul_eq_mul, mul_one]
  have hpsiCol : characterPairing psi col = (base.q : ℂ) := by
    rw [characterPairing_comm, hcolPsi]
  have hcolNorm : characterPairing col col = (base.q : ℂ) := by
    simpa only [col] using ftType34_cyclicColumnTop_self34 base j₀
  have hchiNorm : characterPairing chi chi = 1 := by
    simp only [chi, ftType34_pairing_sub_left34,
      ftType34_pairing_sub_right34]
    rw [hcolNorm, hcolPsi, hpsiCol, hpsiNorm]
    ring
  obtain ⟨chiIrr, epsilon, hepsilon, hchiSigned⟩ :=
    ftType34_exists_signed_irreducible34 hchiVirtual hchiNorm

  have hS₁Kernel : cfConjC_subset
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer base.primeDade) :=
    ⟨ftType34S1_subset_kernelLayer34 base,
      (ftType34S1_cfConjC_subset34 base).2⟩
  have hsubTop : subcoherent
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (ftType345Tau base.maxM)
      (FTtypeP_coh_base base.primeDade base.isoM base.isoG (mFT_odd M)) :=
    subset_subcoherent
      (FTtypeP_subcoherent base.primeDade base.isoM base.isoG (mFT_odd M))
      hS₁Kernel
  have hcoherentTop : coherent
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau base.maxM) :=
    (base.coherent_targetMap_iff
      (S := (↑(ftType34S1 base) : Set (ClassFunction M ℂ)))
      (A := nonidentitySet M)
      (sigma := ftType345Tau base.maxM)).mp
      (ftType34S1_coherent34 base)
  obtain ⟨tau1, hcoh1⟩ := hcoherentTop

  have htauSigned : ∀ xi ∈ ftType34S1 base,
      ∃ (rho : IrreducibleCharacter (⊤ : Subgroup G) ℂ) (delta : ℤ),
        IsSign delta ∧
          tau1 xi = (delta : ℂ) •
            (rho : ClassFunction (⊤ : Subgroup G) ℂ) := by
    intro xi hxi
    have hxiIrr := ftType34S1_irreducible34 base xi hxi
    have hxiSpan : xi ∈ AddSubgroup.closure
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) :=
      AddSubgroup.subset_closure hxi
    have htauVirtual := hcoh1.mapsToVirtual xi hxiSpan
    have hsourceNorm : characterPairing xi xi = 1 :=
      IrreducibleCharacter.characterPairing_self ⟨xi, hxiIrr⟩
    have htauNorm : characterPairing (tau1 xi) (tau1 xi) = 1 :=
      (hcoh1.isometry xi hxiSpan xi hxiSpan).trans hsourceNorm
    exact ftType34_exists_signed_irreducible34 htauVirtual htauNorm
  have hcolTau : ∀ xi ∈ ftType34S1 base,
      characterPairing col (tau1 xi) = 0 := by
    intro xi hxi
    change characterPairingRight (tau1 xi)
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage (i, j₀)) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change characterPairing
        (base.isoG.cyclicTIImage (i, j₀)) (tau1 xi) = 0
    rw [characterPairing_comm]
    exact ftType34_coherent_ortho_etaTop34 base hS₁Kernel hcoh1
      hxi (ftType34S1_irreducible34 base xi hxi) i j₀
  have htauCol : ∀ xi ∈ ftType34S1 base,
      characterPairing (tau1 xi) col = 0 := by
    intro xi hxi
    rw [characterPairing_comm, hcolTau xi hxi]

  by_cases haligned : chi = tau1 zeta
  · refine ⟨tau1, hcoh1, ?_⟩
    dsimp only [psi, col, chi, bridge, j₀] at haligned ⊢
    rw [← haligned]
    module
  · have hnegative : ∀ xi ∈ ftType34S1 base, xi ≠ zeta →
        chi = -tau1 xi := by
      intro xi hxi hxiNe
      have hxiIrr := ftType34S1_irreducible34 base xi hxi
      have hdiffSpan : zeta - xi ∈ AddSubgroup.closure
          (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) :=
        (AddSubgroup.closure _).sub_mem
          (AddSubgroup.subset_closure hzeta)
          (AddSubgroup.subset_closure hxi)
      have hdiffOff : zeta - xi ∈
          ClassFunction.supportedOn (nonidentitySet M) := by
        rw [ClassFunction.mem_supportedOn_iff]
        intro x hx
        have hxOne : x = 1 := by
          simpa [nonidentitySet] using not_not.mp hx
        subst x
        simp only [ClassFunction.sub_apply,
          ftType34S1_degree34 base zeta hzeta,
          ftType34S1_degree34 base xi hxi, sub_self]
      have hdiffSupport : zeta - xi ∈ ClassFunction.supportedOn
          {x : M | (x : G) ∈ FTsupport0 M} :=
        ftType34S1_sub_supportedOn_FTsupport0_34 base hzeta hxi
      have hxiVirtual : ClassFunction.IsVirtual xi :=
        hsubTop.source_virtual xi hxi
      have hdiffVirtual : ClassFunction.IsVirtual (zeta - xi) :=
        hzetaVirtual.sub hxiVirtual
      have hmuXi : characterPairing (muZero34 base) xi = 0 :=
        ftType34_muZero_ortho_S1_34 base xi hxi
      have hzetaXi : characterPairing zeta xi = 0 := by
        let zetaI : IrreducibleCharacter M ℂ := ⟨zeta, hzetaIrr⟩
        let xiI : IrreducibleCharacter M ℂ := ⟨xi, hxiIrr⟩
        have hneI : zetaI ≠ xiI := by
          intro h
          exact hxiNe (congrArg Subtype.val h).symm
        exact IrreducibleCharacter.characterPairing_eq_zero hneI
      have hsourcePair : characterPairing bridge (zeta - xi) = -1 := by
        simp only [bridge, ftType34_pairing_sub_left34,
          ftType34_pairing_sub_right34]
        rw [hmuZeta, hmuXi, hzetaNorm, hzetaXi]
        ring
      have hagree := hcoh1.agrees (zeta - xi) hdiffSpan hdiffOff
      have htargetPair :
          characterPairing psi (tau1 zeta - tau1 xi) = -1 := by
        calc
          characterPairing psi (tau1 zeta - tau1 xi) =
              characterPairing psi (tau1 (zeta - xi)) := by rw [map_sub]
          _ = characterPairing psi
              (ftType345Tau base.maxM (zeta - xi)) := by rw [hagree]
          _ = characterPairing bridge (zeta - xi) := by
            exact ftType34_dade_pairing34 base
              hbridgeVirtual hdiffVirtual hbridgeSupport hdiffSupport
          _ = -1 := hsourcePair
      have htargetPair' :
          characterPairing psi (tau1 zeta) -
              characterPairing psi (tau1 xi) = -1 := by
        simpa only [ftType34_pairing_sub_right34] using htargetPair
      have hpivotPair :
          characterPairing chi (tau1 xi) -
              characterPairing chi (tau1 zeta) = -1 := by
        calc
          characterPairing chi (tau1 xi) -
              characterPairing chi (tau1 zeta) =
              characterPairing psi (tau1 zeta) -
                characterPairing psi (tau1 xi) := by
            simp only [chi, ftType34_pairing_sub_left34,
              hcolTau zeta hzeta, hcolTau xi hxi, zero_sub]
            ring
          _ = -1 := htargetPair'
      have hzetaXiTarget : characterPairing (tau1 zeta) (tau1 xi) = 0 :=
        (hcoh1.isometry zeta (AddSubgroup.subset_closure hzeta)
          xi (AddSubgroup.subset_closure hxi)).trans hzetaXi
      obtain ⟨zetaImage, delta, hdelta, hzetaImage⟩ :=
        htauSigned zeta hzeta
      obtain ⟨xiImage, kappa, hkappa, hxiImage⟩ :=
        htauSigned xi hxi
      exact (ftType34_signed_irreducible_pivot34
        hepsilon hdelta hkappa hchiSigned hzetaImage hxiImage
        hzetaXiTarget hpivotPair).resolve_left haligned

    let zetaInv : ClassFunction M ℂ :=
      ClassFunction.inverseLinear (G := M) (k := ℂ) zeta
    have hzetaInvMem : zetaInv ∈ ftType34S1 base :=
      (ftType34S1_cfConjC_subset34 base).2 zeta hzeta
    have hzetaInvNe : zetaInv ≠ zeta :=
      hsubTop.inverse_ne zeta hzeta
    have hnegativeInv : chi = -tau1 zetaInv :=
      hnegative zetaInv hzetaInvMem hzetaInvNe
    have hmemberEq : ∀ xi ∈ ftType34S1 base,
        xi = zeta ∨ xi = zetaInv := by
      intro xi hxi
      by_cases hxiZeta : xi = zeta
      · exact Or.inl hxiZeta
      · right
        have hnegativeXi := hnegative xi hxi hxiZeta
        have himageXi : tau1 xi = -chi := by
          rw [hnegativeXi]
          module
        have himageInv : tau1 zetaInv = -chi := by
          rw [hnegativeInv]
          module
        have hxiIrr := ftType34S1_irreducible34 base xi hxi
        have hinvIrr :=
          ftType34S1_irreducible34 base zetaInv hzetaInvMem
        have hsourcePair : characterPairing xi zetaInv = 1 := by
          calc
            characterPairing xi zetaInv =
                characterPairing (tau1 xi) (tau1 zetaInv) :=
              (hcoh1.isometry xi (AddSubgroup.subset_closure hxi)
                zetaInv (AddSubgroup.subset_closure hzetaInvMem)).symm
            _ = characterPairing (-chi) (-chi) := by
              rw [himageXi, himageInv]
            _ = 1 := by
              rw [ftType34_pairing_neg_left34,
                ftType34_pairing_neg_right34, neg_neg, hchiNorm]
        let xiI : IrreducibleCharacter M ℂ := ⟨xi, hxiIrr⟩
        let invI : IrreducibleCharacter M ℂ := ⟨zetaInv, hinvIrr⟩
        have hIrrEq : xiI = invI := by
          by_contra hne
          have hzero := IrreducibleCharacter.characterPairing_eq_zero hne
          exact zero_ne_one (hzero.symm.trans hsourcePair)
        exact congrArg Subtype.val hIrrEq
    have hfinSubset : ftType34S1 base ⊆
        ({zeta, zetaInv} : Finset (ClassFunction M ℂ)) := by
      intro xi hxi
      rcases hmemberEq xi hxi with rfl | rfl <;> simp
    have hcardFin : (ftType34S1 base).card ≤ 2 := by
      calc
        (ftType34S1 base).card ≤
            ({zeta, zetaInv} : Finset (ClassFunction M ℂ)).card :=
          Finset.card_le_card hfinSubset
        _ ≤ 2 := Finset.card_le_two
    have hcardSet :
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ)).ncard ≤ 2 := by
      simpa using hcardFin
    have hdual := dual_coherence hsubTop hcoh1 hcardSet
    have hdualZeta : dual_iso tau1 zeta = chi := by
      rw [dual_iso_apply]
      exact hnegativeInv.symm
    refine ⟨dual_iso tau1, hdual, ?_⟩
    dsimp only [psi, col, chi, bridge, j₀] at hdualZeta ⊢
    rw [hdualZeta]
    module

/-! ## The two kernel layers over `C` -/

private theorem ftType34SecondDerivedInMNormalFresh34
    (M : Subgroup G) :
    ((secondDerivedWithin M).subgroupOf M).Normal := by
  let K : Subgroup M := (derivedWithin M).subgroupOf M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  rw [secondDerivedInM_eq_commutator_map11 M]
  infer_instance

private theorem ftType34S2DisjointS1Fresh34
    (base : FTType34Base M U W W₁ W₂ defW) :
    (↑(ftType34S2 base) : Set (ClassFunction M ℂ)) ⊆
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))ᶜ := by
  letI : base.HUInM.Normal := ftType34_HUInM_normal34 base
  letI :
      ((base.HCInHU.map base.HUInM.subtype : Subgroup M)).Normal := by
    rw [Subgroup.map_subgroupOf_eq_of_le
      (Subgroup.subgroupOf_mono M base.HC_le_HU)]
    rw [← FTtype34_der2 base]
    exact ftType34SecondDerivedInMNormalFresh34 M
  letI :
      (((⊤ : Subgroup base.HUInM).map
        base.HUInM.subtype : Subgroup M)).Normal := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact TypeSpecInternal.derivedWithin_normal16 M
  intro phi hphi2 hphi1
  change phi ∈ seqIndD (k := ℂ) base.HUInM
      base.HCInHU base.CInHU at hphi2
  change phi ∈ seqIndD (k := ℂ) base.HUInM
      (⊤ : Subgroup base.HUInM) base.HCInHU at hphi1
  obtain ⟨theta, htheta2, rfl⟩ := seqIndP.mp hphi2
  have htheta1 :=
    (mem_seqInd base.HUInM (⊤ : Subgroup base.HUInM)
      base.HCInHU theta).mp hphi1
  have htheta2Data := (mem_Iirr_kerD (k := ℂ)).mp htheta2
  have htheta1Data := (mem_Iirr_kerD (k := ℂ)).mp htheta1
  exact htheta2Data.2 htheta1Data.1

private theorem ftType34S1UnionS2EqCLayerFresh34
    (base : FTType34Base M U W W₁ W₂ defW) :
    (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) ∪
        (↑(ftType34S2 base) : Set (ClassFunction M ℂ)) =
      (↑(ftType34Layer base base.CInHU) :
        Set (ClassFunction M ℂ)) := by
  classical
  have hC_le_HC : base.CInHU ≤ base.HCInHU :=
    Subgroup.subgroupOf_mono base.HUInM
      (Subgroup.subgroupOf_mono M
        (show base.C ≤ base.HC from le_sup_right))
  ext phi
  constructor
  · rintro (hphi1 | hphi2)
    · change phi ∈ seqIndD (k := ℂ) base.HUInM
          (⊤ : Subgroup base.HUInM) base.HCInHU at hphi1
      obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hphi1
      apply seqIndP.mpr
      refine ⟨theta, ?_, rfl⟩
      have hthetaData := (mem_Iirr_kerD (k := ℂ)).mp htheta
      exact (mem_Iirr_kerD (k := ℂ)).mpr
        ⟨hC_le_HC.trans hthetaData.1, hthetaData.2⟩
    · change phi ∈ seqIndD (k := ℂ) base.HUInM
          base.HCInHU base.CInHU at hphi2
      obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hphi2
      apply seqIndP.mpr
      refine ⟨theta, ?_, rfl⟩
      have hthetaData := (mem_Iirr_kerD (k := ℂ)).mp htheta
      apply (mem_Iirr_kerD (k := ℂ)).mpr
      refine ⟨hthetaData.1, ?_⟩
      intro htop
      exact hthetaData.2
        ((show base.HCInHU ≤ (⊤ : Subgroup base.HUInM) from le_top).trans
          htop)
  · intro hphi
    change phi ∈ seqIndD (k := ℂ) base.HUInM
        (⊤ : Subgroup base.HUInM) base.CInHU at hphi
    obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hphi
    have hthetaData := (mem_Iirr_kerD (k := ℂ)).mp htheta
    by_cases hHC : base.HCInHU ≤
        ClassFunction.translationKernel
          (theta : ClassFunction base.HUInM ℂ)
    · left
      apply seqIndP.mpr
      exact ⟨theta,
        (mem_Iirr_kerD (k := ℂ)).mpr ⟨hHC, hthetaData.2⟩, rfl⟩
    · right
      apply seqIndP.mpr
      exact ⟨theta,
        (mem_Iirr_kerD (k := ℂ)).mpr ⟨hthetaData.1, hHC⟩, rfl⟩

/-! ## Uniform reducible columns -/

private theorem ftType34UniformPrimeTIRedCoherentFresh34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j0 : IrreducibleCharacter W₂ ℂ)
    (hj0 : j0 ≠ IrreducibleCharacter.trivial) :
    let T := base.primeTI.uniform_prTIred_seq base.isoM j0
    ∃ tauTop : ClassFunction M ℂ →ₗ[ℂ]
        ClassFunction (⊤ : Subgroup G) ℂ,
      coherent_with T (nonidentitySet M)
          (Dade base.primeDade.prDade_hyp) tauTop ∧
        ∀ j, tauTop (mu34 base j) =
          (base.primeTI.primeTISign base.isoM j0 : ℂ) •
            ∑ i : IrreducibleCharacter W₁ ℂ,
              base.isoG.cyclicTIImage (i, j) := by
  classical
  let T := base.primeTI.uniform_prTIred_seq base.isoM j0
  obtain ⟨_, tauTop, htauTop, hisometry, hagrees⟩ :=
    base.primeDade.uniform_prTIred_coherent
      base.isoM base.isoG j0 hj0
  have hgeneratorVirtual : ∀ phi ∈ T,
      ClassFunction.IsVirtual (tauTop phi) := by
    rintro phi ⟨j, _hj, rfl⟩
    rw [htauTop]
    have hsumVirtual : ClassFunction.IsVirtual
        (∑ i : IrreducibleCharacter W₁ ℂ,
          base.isoG.cyclicTIImage (i, j)) :=
      ftType34_cyclicColumnTop_virtual34 base j
    have hzsmul := hsumVirtual.zsmul
      (base.primeTI.primeTISign base.isoM j0)
    exact (Int.cast_smul_eq_zsmul ℂ
      (base.primeTI.primeTISign base.isoM j0)
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage (i, j))).symm ▸ hzsmul
  have hmapsToVirtual : ∀ phi ∈ AddSubgroup.closure T,
      ClassFunction.IsVirtual (tauTop phi) := by
    intro phi hphi
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi => exact hgeneratorVirtual phi hphi
    | zero =>
        rw [map_zero]
        exact ClassFunction.IsVirtual.zero
    | add phi psi _ _ hphi hpsi =>
        rw [map_add]
        exact hphi.add hpsi
    | neg phi _ hphi =>
        rw [map_neg]
        exact hphi.neg
  refine ⟨tauTop, ?_, ?_⟩
  · exact
      { isometry := hisometry
        mapsToVirtual := hmapsToVirtual
        agrees := hagrees }
  · simpa only [mu34] using htauTop

private theorem ftType34S2SubsetUniformOfReducibleFresh34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j0 : IrreducibleCharacter W₂ ℂ)
    (hj0 : j0 ≠ IrreducibleCharacter.trivial)
    (hreducible : ∀ phi ∈ ftType34S2 base,
      ¬ IsIrreducibleCharacter M ℂ phi) :
    (↑(ftType34S2 base) : Set (ClassFunction M ℂ)) ⊆
      base.primeTI.uniform_prTIred_seq base.isoM j0 := by
  intro phi hphi
  have hphiSaved := hphi
  change phi ∈ seqIndD (k := ℂ) base.HUInM
      base.HCInHU base.CInHU at hphi
  obtain ⟨theta, htheta, rfl⟩ := seqIndP.mp hphi
  rcases base.primeTI.prTIres_irr_cases base.isoM theta with
      ⟨j, hj⟩ | ⟨hirr, _⟩
  · have hjNe : j ≠ IrreducibleCharacter.trivial := by
      intro hjTrivial
      subst j
      apply ((mem_Iirr_kerD (k := ℂ)).mp htheta).2
      rw [hj, base.primeTI.prTIres0 base.isoM]
      intro x _hx
      rw [ClassFunction.mem_translationKernel_iff]
      intro y
      simp
    refine ⟨j, ⟨hjNe, ?_⟩, ?_⟩
    · exact (ftType34_mu_degree11 base j hjNe).trans
        (ftType34_mu_degree11 base j0 hj0).symm
    · change mu34 base j = ClassFunction.induce base.HUInM
          (theta : ClassFunction base.HUInM ℂ)
      rw [hj, base.primeTI.cfInd_prTIres base.isoM]
  · exact (hreducible _ hphiSaved hirr).elim

private theorem ftType34ChooseTau2UniformFresh34
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hreducible : ∀ phi ∈ ftType34S2 base,
      ¬ IsIrreducibleCharacter M ℂ phi) :
    ∃ tau2 : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ,
      coherent_with
          (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
          (nonidentitySet M) base.tau tau2 ∧
        tau2 (mu34 base j) = etaColumn34 base j := by
  classical
  obtain ⟨tauTop, hcohTop, htauTop⟩ :=
    ftType34UniformPrimeTIRedCoherentFresh34 base j hj
  have hsubset :=
    ftType34S2SubsetUniformOfReducibleFresh34 base j hj hreducible
  have hcohS2Top := subset_coherent_with hsubset hcohTop
  let tau2 : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    base.targetMap.comp tauTop
  have hcohS2 : coherent_with
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) base.tau tau2 :=
    { isometry := by
        intro phi hphi psi hpsi
        change characterPairing
            (base.targetMap (tauTop phi))
            (base.targetMap (tauTop psi)) = characterPairing phi psi
        exact (base.targetMap_pairing (tauTop phi) (tauTop psi)).trans
          (hcohS2Top.isometry phi hphi psi hpsi)
      mapsToVirtual := by
        intro phi hphi
        change ClassFunction.IsVirtual (base.targetMap (tauTop phi))
        exact base.targetMap_virtual
          (hcohS2Top.mapsToVirtual phi hphi)
      agrees := by
        intro phi hphi hsupp
        change base.targetMap (tauTop phi) =
          base.targetMap (Dade base.primeDade.prDade_hyp phi)
        exact congrArg base.targetMap
          (hcohS2Top.agrees phi hphi hsupp) }
  have hsign : base.primeTI.primeTISign base.isoM j = 1 := by
    calc
      base.primeTI.primeTISign base.isoM j =
          FTtype345_TIsign base.MtypeP :=
        (FTtype345_constants base.maxM base.MtypeP base.notMtype2).sign_constant
          j hj
      _ = 1 := (ftType34_constants34 base).2.1
  refine ⟨tau2, hcohS2, ?_⟩
  change base.targetMap (tauTop (mu34 base j)) = etaColumn34 base j
  rw [htauTop j, hsign, Int.cast_one, one_smul, etaColumn34, map_sum]

/-! ## Support and transport for the irreducible `S₂` branch -/

private theorem ftType34_tau_pairing34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi psi : ClassFunction M ℂ}
    (hphiVirt : ClassFunction.IsVirtual phi)
    (hpsiVirt : ClassFunction.IsVirtual psi)
    (hphiSupp : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M})
    (hpsiSupp : psi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M}) :
    characterPairing (base.tau phi) (base.tau psi) =
      characterPairing phi psi := by
  change characterPairing
      (base.targetMap (ftType345Tau base.maxM phi))
      (base.targetMap (ftType345Tau base.maxM psi)) = _
  rw [base.targetMap_pairing]
  exact ftType34_dade_pairing34 base
    hphiVirt hpsiVirt hphiSupp hpsiSupp

private theorem ftType34_virtual_of_closure34
    {Q : Type} [Group Q] [Fintype Q]
    {S : Set (ClassFunction Q ℂ)}
    (hS : ∀ phi ∈ S, ClassFunction.IsVirtual phi)
    {phi : ClassFunction Q ℂ}
    (hphi : phi ∈ AddSubgroup.closure S) :
    ClassFunction.IsVirtual phi := by
  induction hphi using AddSubgroup.closure_induction with
  | mem phi hphi => exact hS phi hphi
  | zero => exact ClassFunction.IsVirtual.zero
  | add phi psi _ _ hphi hpsi => exact hphi.add hpsi
  | neg phi _ hphi => exact hphi.neg

private theorem ftType34_HUsharp_supportedOn_nonidentity34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ ClassFunction.supportedOn
      (subgroupNonidentity base.HUInM)) :
    phi ∈ ClassFunction.supportedOn (nonidentitySet M) := by
  rw [ClassFunction.mem_supportedOn_iff] at hphi ⊢
  intro x hx
  apply hphi x
  intro hxHU
  exact hx hxHU.2

private theorem ftType34_theta_supportedOn_FTsupport0_34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    mu34 base j - (base.u : ℂ) • zeta ∈
      ClassFunction.supportedOn {x : M | (x : G) ∈ FTsupport0 M} := by
  letI : base.HUInM.Normal := ftType34_HUInM_normal34 base
  have hzetaSeq : zeta ∈ seqIndT (k := ℂ) base.HUInM := by
    apply seqInd_subT base.HUInM
      (Iirr_kerD (k := ℂ) ⊤ base.HCInHU)
    simpa only [ftType34S1, ftType34Layer, seqIndD] using hzeta
  have hmuS2 : mu34 base j ∈ ftType34S2 base :=
    (ftType34_mu_mem_S2_reducible11 base j hj).1
  have hmuSeq : mu34 base j ∈ seqIndT (k := ℂ) base.HUInM := by
    apply seqInd_subT base.HUInM
      (Iirr_kerD (k := ℂ) base.HCInHU base.CInHU)
    simpa only [ftType34S2, seqIndD] using hmuS2
  have hzetaOne : zeta 1 = (base.HUInM.index : ℂ) := by
    rw [ftType34S1_degree34 base zeta hzeta,
      ftType34_HUInM_index_eq_q11 base]
  have hbalanced := seqInd_sub_lin_on base.HUInM
    hzetaSeq hzetaOne hmuSeq
  have hcoefficient :
      mu34 base j 1 / (base.HUInM.index : ℂ) = (base.u : ℂ) := by
    rw [ftType34_mu_degree11 base j hj,
      ftType34_HUInM_index_eq_q11 base, Nat.cast_mul]
    exact mul_div_cancel_left₀ _
      (Nat.cast_ne_zero.mpr base.q_prime.ne_zero)
  rw [hcoefficient] at hbalanced
  exact ftType34_HUsharp_supportedOn_FTsupport0_34 base hbalanced

private theorem ftType34_sourceMap_coherentWith34
    (base : FTType34Base M U W W₁ W₂ defW)
    {S : Set (ClassFunction M ℂ)}
    {nu : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hnu : coherent_with S (nonidentitySet M) base.tau nu) :
    coherent_with S (nonidentitySet M)
      (ftType345Tau base.maxM) (base.sourceMap.comp nu) := by
  exact
    { isometry := by
        intro phi hphi psi hpsi
        simpa only [LinearMap.comp_apply] using
          (base.sourceMap_pairing (nu phi) (nu psi)).trans
            (hnu.isometry phi hphi psi hpsi)
      mapsToVirtual := by
        intro phi hphi
        exact base.sourceMap_virtual (hnu.mapsToVirtual phi hphi)
      agrees := by
        intro phi hphi hsupp
        have hagree := hnu.agrees phi hphi hsupp
        simpa only [LinearMap.comp_apply, hagree, FTType34Base.tau,
          base.sourceMap_targetMap] }

private theorem ftType34_coherent_ortho_eta34
    (base : FTType34Base M U W W₁ W₂ defW)
    {S : Set (ClassFunction M ℂ)}
    {nu : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hS : cfConjC_subset S (FTtypePKernelLayer base.primeDade))
    (hnu : coherent_with S (nonidentitySet M) base.tau nu)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ S)
    (hirr : IsIrreducibleCharacter M ℂ phi)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (nu phi) (eta34 base i j) = 0 := by
  have htop := ftType34_coherent_ortho_etaTop34 base hS
    (ftType34_sourceMap_coherentWith34 base hnu) hphi hirr i j
  have hsource := base.sourceMap_pairing (nu phi) (eta34 base i j)
  rw [show base.sourceMap (eta34 base i j) =
      base.isoG.cyclicTIImage (i, j) by
        exact base.sourceMap_targetMap _] at hsource
  exact hsource.symm.trans htop

private theorem ftType34S2_subset_kernelLayer34
    (base : FTType34Base M U W W₁ W₂ defW) :
    cfConjC_subset
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer base.primeDade) := by
  have hS2 := ftType34S2_cfConjC_subset34 base
  refine ⟨?_, hS2.2⟩
  intro phi hphi
  have hbottom := hS2.1 hphi
  simpa [FTtypePKernelLayer,
    PrimeDadeHypothesis.signalizerInKernel, ftType34Layer,
    base.FTcore_eq_HU] using hbottom

private theorem ftType34S1DisjointS2Fresh34
    (base : FTType34Base M U W W₁ W₂ defW) :
    (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) ⊆
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))ᶜ := by
  intro phi hphi1 hphi2
  exact ftType34S2DisjointS1Fresh34 base hphi2 hphi1

private theorem ftType34_etaColumns_ortho34
    (base : FTType34Base M U W W₁ W₂ defW)
    {j ell : IrreducibleCharacter W₂ ℂ}
    (h : ell ≠ j) :
    characterPairing (etaColumn34 base j) (etaColumn34 base ell) = 0 := by
  classical
  rw [etaColumn34]
  change characterPairingRight (etaColumn34 base ell)
      (∑ i : IrreducibleCharacter W₁ ℂ, eta34 base i j) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  change characterPairing (eta34 base i j) (etaColumn34 base ell) = 0
  rw [characterPairing_comm, characterPairing_etaColumn34, if_neg h.symm]

private theorem ftType34_choose_tau2_irreducibleFresh34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base)
    (tau1 : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh1 : coherent_with
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) base.tau tau1)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (htheta :
      base.tau (mu34 base j - (base.u : ℂ) • zeta) =
        etaColumn34 base j - (base.u : ℂ) • tau1 zeta)
    (hexists : ∃ xi ∈ ftType34S2 base,
      IsIrreducibleCharacter M ℂ xi) :
    ∃ tau2 : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ,
      coherent_with
          (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
          (nonidentitySet M) base.tau tau2 ∧
        tau2 (mu34 base j) = etaColumn34 base j := by
  classical
  obtain ⟨xi, hxiS2, hxiIrr⟩ := hexists
  obtain ⟨tau2, hcoh2⟩ := ftType34S2_coherent34 base
  have hmuData := ftType34_mu_mem_S2_reducible11 base j hj
  have hmuS2 : mu34 base j ∈ ftType34S2 base := hmuData.1
  have hmuReducible :
      ¬ IsIrreducibleCharacter M ℂ (mu34 base j) := hmuData.2

  let calX : Finset (IrreducibleCharacter base.HUInM ℂ) :=
    Iirr_kerD (k := ℂ) base.HCInHU base.CInHU
  have hxiSeq : xi ∈ seqInd base.HUInM calX := by
    simpa only [calX, ftType34S2, seqIndD] using hxiS2
  have hmuSeq : mu34 base j ∈ seqInd base.HUInM calX := by
    simpa only [calX, ftType34S2, seqIndD] using hmuS2
  obtain ⟨m, hmuOne⟩ := Cnat_seqInd1 base.HUInM hmuSeq
  obtain ⟨n, hxiOne⟩ := Cnat_seqInd1 base.HUInM hxiSeq

  let gamma : ClassFunction M ℂ :=
    (xi 1) • mu34 base j - (mu34 base j 1) • xi
  let theta : ClassFunction M ℂ :=
    mu34 base j - (base.u : ℂ) • zeta

  have hgammaSpan : gamma ∈ AddSubgroup.closure
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ)) := by
    have hnMu := (AddSubgroup.closure
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))).nsmul_mem
        (AddSubgroup.subset_closure hmuS2) n
    have hmXi := (AddSubgroup.closure
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))).nsmul_mem
        (AddSubgroup.subset_closure hxiS2) m
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n (mu34 base j)] at hnMu
    rw [← Nat.cast_smul_eq_nsmul (R := ℂ) m xi] at hmXi
    simpa only [gamma, hxiOne, hmuOne] using
      (AddSubgroup.closure
        (↑(ftType34S2 base) : Set (ClassFunction M ℂ))).sub_mem
          hnMu hmXi

  letI : base.HUInM.Normal := ftType34_HUInM_normal34 base
  have hgammaHU : gamma ∈ ClassFunction.supportedOn
      (subgroupNonidentity base.HUInM) := by
    simpa only [gamma] using
      sub_seqInd_on base.HUInM hmuSeq hxiSeq
  have hgammaOff : gamma ∈
      ClassFunction.supportedOn (nonidentitySet M) :=
    ftType34_HUsharp_supportedOn_nonidentity34 base hgammaHU
  have hgammaSupp : gamma ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} :=
    ftType34_HUsharp_supportedOn_FTsupport0_34 base hgammaHU
  have hthetaSupp : theta ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
    simpa only [theta] using
      ftType34_theta_supportedOn_FTsupport0_34 base zeta hzeta j hj

  have hgammaVirt : ClassFunction.IsVirtual gamma := by
    apply ftType34_virtual_of_closure34
      (S := (↑(ftType34S2 base) : Set (ClassFunction M ℂ)))
    · intro phi hphi
      exact (ftType34_bottom_subcoherent34 base).source_virtual phi
        ((ftType34S2_cfConjC_subset34 base).1 hphi)
    · exact hgammaSpan
  have hzetaVirt : ClassFunction.IsVirtual zeta :=
    (ftType34_bottom_subcoherent34 base).source_virtual zeta
      ((ftType34S1_cfConjC_subset34 base).1 hzeta)
  have hscaledZetaVirt :
      ClassFunction.IsVirtual ((base.u : ℂ) • zeta) := by
    simpa only [Nat.cast_smul_eq_nsmul] using hzetaVirt.nsmul base.u
  have hthetaVirt : ClassFunction.IsVirtual theta := by
    have hmuVirt := (base.primeTI.prTIred_char base.isoM j).isVirtual
    simpa only [theta] using hmuVirt.sub hscaledZetaVirt

  have hcross := coherent_ortho
    (ftType34_bottom_subcoherent34 base)
    (ftType34S2_cfConjC_subset34 base) hcoh2
    (ftType34S1_cfConjC_subset34 base) hcoh1
    (ftType34S1DisjointS2Fresh34 base)
  have hmuTauZeta :
      characterPairing (tau2 (mu34 base j)) (tau1 zeta) = 0 :=
    hcross (tau2 (mu34 base j))
      ⟨mu34 base j, AddSubgroup.subset_closure hmuS2, rfl⟩
      (tau1 zeta)
      ⟨zeta, AddSubgroup.subset_closure hzeta, rfl⟩
  have hxiTauZeta : characterPairing (tau2 xi) (tau1 zeta) = 0 :=
    hcross (tau2 xi)
      ⟨xi, AddSubgroup.subset_closure hxiS2, rfl⟩
      (tau1 zeta)
      ⟨zeta, AddSubgroup.subset_closure hzeta, rfl⟩
  have hxiEta :
      characterPairing (tau2 xi) (etaColumn34 base j) = 0 := by
    rw [characterPairing_comm, etaColumn34]
    change characterPairingRight (tau2 xi)
        (∑ i : IrreducibleCharacter W₁ ℂ, eta34 base i j) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _
    change characterPairing (eta34 base i j) (tau2 xi) = 0
    rw [characterPairing_comm]
    exact ftType34_coherent_ortho_eta34 base
      (ftType34S2_subset_kernelLayer34 base) hcoh2
      hxiS2 hxiIrr i j

  have hmuXi : characterPairing (mu34 base j) xi = 0 := by
    apply (ftType34_bottom_subcoherent34 base).pairwise_orthogonal
      ((ftType34S2_cfConjC_subset34 base).1 hmuS2)
      ((ftType34S2_cfConjC_subset34 base).1 hxiS2)
    intro hEq
    apply hmuReducible
    simpa only [hEq] using hxiIrr
  have hxiMu : characterPairing xi (mu34 base j) = 0 := by
    rw [characterPairing_comm, hmuXi]
  have hmuZeta : characterPairing (mu34 base j) zeta = 0 := by
    apply (ftType34_bottom_subcoherent34 base).pairwise_orthogonal
      ((ftType34S2_cfConjC_subset34 base).1 hmuS2)
      ((ftType34S1_cfConjC_subset34 base).1 hzeta)
    intro hEq
    exact ftType34S2DisjointS1Fresh34 base hmuS2
      (hEq.symm ▸ hzeta)
  have hxiZeta : characterPairing xi zeta = 0 := by
    apply (ftType34_bottom_subcoherent34 base).pairwise_orthogonal
      ((ftType34S2_cfConjC_subset34 base).1 hxiS2)
      ((ftType34S1_cfConjC_subset34 base).1 hzeta)
    intro hEq
    exact ftType34S2DisjointS1Fresh34 base hxiS2
      (hEq.symm ▸ hzeta)
  have hmuNorm : characterPairing (mu34 base j) (mu34 base j) =
      (base.q : ℂ) := by
    simpa only [mu34] using
      base.primeTI.cfnorm_prTIred base.isoM j

  have hsourcePair : characterPairing gamma theta =
      xi 1 * (base.q : ℂ) := by
    simp only [gamma, theta, ftType34_pairing_sub_left34,
      ftType34_pairing_sub_right34, characterPairing_smul_left,
      characterPairing_smul_right]
    rw [hmuNorm, hmuZeta, hxiMu, hxiZeta]
    simp [hxiOne, hmuOne]
  have hsourcePairNe : characterPairing gamma theta ≠ 0 := by
    rw [hsourcePair]
    exact mul_ne_zero
      ((ftType34_bottom_subcoherent34 base).degree_ne_zero xi
        ((ftType34S2_cfConjC_subset34 base).1 hxiS2))
      (Nat.cast_ne_zero.mpr base.q_prime.ne_zero)

  have hpairingNonzero :
      characterPairing (tau2 (mu34 base j))
        (etaColumn34 base j) ≠ 0 := by
    intro hzero
    have htargetZero : characterPairing (tau2 gamma)
        (etaColumn34 base j - (base.u : ℂ) • tau1 zeta) = 0 := by
      simp only [gamma, map_sub, map_smul,
        ftType34_pairing_sub_left34, ftType34_pairing_sub_right34,
        characterPairing_smul_left, characterPairing_smul_right]
      rw [hzero, hmuTauZeta, hxiEta, hxiTauZeta]
      simp [hxiOne, hmuOne]
    have htargetPair : characterPairing (tau2 gamma)
        (etaColumn34 base j - (base.u : ℂ) • tau1 zeta) =
          characterPairing gamma theta := by
      calc
        characterPairing (tau2 gamma)
            (etaColumn34 base j - (base.u : ℂ) • tau1 zeta) =
            characterPairing (base.tau gamma) (base.tau theta) := by
          rw [hcoh2.agrees gamma hgammaSpan hgammaOff, htheta]
        _ = characterPairing gamma theta :=
          ftType34_tau_pairing34 base hgammaVirt hthetaVirt
            hgammaSupp hthetaSupp
    exact hsourcePairNe (htargetPair.symm.trans htargetZero)

  let tau2Top : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ := base.sourceMap.comp tau2
  have hcoh2Top : coherent_with
      (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau base.maxM) tau2Top := by
    simpa only [tau2Top] using
      ftType34_sourceMap_coherentWith34 base hcoh2
  let xiI : IrreducibleCharacter M ℂ := ⟨xi, hxiIrr⟩
  have hcases := FTtypeP_coherent_TIred
    base.primeDade base.isoM base.isoG (mFT_odd M)
    (↑(ftType34S2 base) : Set (ClassFunction M ℂ)) tau2Top
    xiI j (ftType34S2_subset_kernelLayer34 base)
    hcoh2Top hxiS2 hmuS2
  have hsign : base.primeTI.primeTISign base.isoM j = 1 := by
    calc
      base.primeTI.primeTISign base.isoM j =
          FTtype345_TIsign base.MtypeP :=
        (FTtype345_constants base.maxM base.MtypeP base.notMtype2).sign_constant
          j hj
      _ = 1 := (ftType34_constants34 base).2.1

  rcases hcases with hfirst | hsecond
  · refine ⟨tau2, hcoh2, ?_⟩
    have hfirstG := congrArg base.targetMap hfirst
    simpa only [tau2Top, LinearMap.comp_apply,
      base.targetMap_sourceMap, hsign, Int.cast_one, one_smul,
      etaColumn34, eta34, map_sum, map_smul] using hfirstG
  · rcases hsecond with ⟨hdualTop, _⟩
    have hdualG := congrArg base.targetMap hdualTop
    have hdualEqSmul : tau2 (mu34 base j) =
        (-1 : ℂ) •
          etaColumn34 base (IrreducibleCharacter.dual j) := by
      simpa only [tau2Top, LinearMap.comp_apply,
        base.targetMap_sourceMap, hsign, Int.cast_one,
        etaColumn34, eta34, map_sum, map_smul] using hdualG
    have hdualEq : tau2 (mu34 base j) =
        -etaColumn34 base (IrreducibleCharacter.dual j) :=
      hdualEqSmul.trans
        (neg_one_smul ℂ
          (etaColumn34 base (IrreducibleCharacter.dual j)))
    exfalso
    apply hpairingNonzero
    rw [hdualEq, ftType34_pairing_neg_left34,
      ftType34_etaColumns_ortho34 base
        (dual_ne_self_of_odd_of_ne_trivial (mFT_odd W₂) hj).symm,
      neg_zero]

/-! ## Final assembly -/

private theorem ftType34_targetMap_coherentWith34
    (base : FTType34Base M U W W₁ W₂ defW)
    {S : Set (ClassFunction M ℂ)}
    {nu : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ}
    (hnu : coherent_with S (nonidentitySet M)
      (ftType345Tau base.maxM) nu) :
    coherent_with S (nonidentitySet M)
      base.tau (base.targetMap.comp nu) := by
  exact
    { isometry := by
        intro phi hphi psi hpsi
        simpa only [LinearMap.comp_apply] using
          (base.targetMap_pairing (nu phi) (nu psi)).trans
            (hnu.isometry phi hphi psi hpsi)
      mapsToVirtual := by
        intro phi hphi
        exact base.targetMap_virtual (hnu.mapsToVirtual phi hphi)
      agrees := by
        intro phi hphi hsupp
        change base.targetMap (nu phi) =
          base.targetMap (ftType345Tau base.maxM phi)
        exact congrArg base.targetMap
          (hnu.agrees phi hphi hsupp) }

private theorem ftType34_not_ortho_final34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base) :
    ¬ eqProjection34 base (dadeBridgeZero34 base zeta)
      (etaColumn34 base
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) := by
  classical
  intro hprojection

  obtain ⟨tau1Top, hcoh1Top, hzeroTop⟩ :=
    ftType34_choose_tau1_aligned_top34 base zeta hzeta hprojection

  let j : IrreducibleCharacter W₂ ℂ := FTtype345_jOne base.MtypeP
  have hj : j ≠ IrreducibleCharacter.trivial := by
    simpa only [j] using FTtype345_jOne_ne_trivial base.MtypeP
  have hthetaTop :=
    ftType34TauThetaFromNormalizedMiddle base zeta hzeta
      tau1Top hcoh1Top hzeroTop j hj

  let tau1 : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ :=
    base.targetMap.comp tau1Top
  have hcoh1 : coherent_with
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) base.tau tau1 := by
    simpa only [tau1] using
      ftType34_targetMap_coherentWith34 base hcoh1Top
  have hthetaMap := congrArg base.targetMap hthetaTop
  have htheta :
      base.tau (mu34 base j - (base.u : ℂ) • zeta) =
        etaColumn34 base j - (base.u : ℂ) • tau1 zeta := by
    simpa only [mu34, etaColumn34, eta34, tau1,
      FTType34Base.tau, LinearMap.comp_apply, map_sub, map_smul,
      map_sum] using hthetaMap

  obtain ⟨tau2, hcoh2, hmuAligned⟩ :
      ∃ tau2 : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ,
        coherent_with
            (↑(ftType34S2 base) : Set (ClassFunction M ℂ))
            (nonidentitySet M) base.tau tau2 ∧
          tau2 (mu34 base j) = etaColumn34 base j := by
    by_cases hexists : ∃ xi ∈ ftType34S2 base,
        IsIrreducibleCharacter M ℂ xi
    · exact ftType34_choose_tau2_irreducibleFresh34 base zeta hzeta
        tau1 hcoh1 j hj htheta hexists
    · apply ftType34ChooseTau2UniformFresh34 base j hj
      intro phi hphi hphiIrr
      exact hexists ⟨phi, hphi, hphiIrr⟩

  have hmuS2 : mu34 base j ∈ ftType34S2 base :=
    (ftType34_mu_mem_S2_reducible11 base j hj).1
  have hscaledZetaSpan : (base.u : ℂ) • zeta ∈
      AddSubgroup.closure
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      (AddSubgroup.closure
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ))).nsmul_mem
          (AddSubgroup.subset_closure hzeta) base.u
  have hthetaOff : mu34 base j - (base.u : ℂ) • zeta ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxOne : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
      smul_eq_mul, ftType34_mu_degree11 base j hj,
      ftType34S1_degree34 base zeta hzeta, Nat.cast_mul]
    ring
  have hbridge : base.tau
      (mu34 base j - (base.u : ℂ) • zeta) =
        tau2 (mu34 base j) - tau1 ((base.u : ℂ) • zeta) := by
    rw [htheta, hmuAligned, map_smul]

  have hcohUnion : coherent
      ((↑(ftType34S2 base) : Set (ClassFunction M ℂ)) ∪
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ)))
      (nonidentitySet M) base.tau := by
    exact bridge_coherent
      (ftType34_bottom_subcoherent34 base)
      (ftType34S2_cfConjC_subset34 base) hcoh2
      (ftType34S1_cfConjC_subset34 base) hcoh1
      (ftType34S1DisjointS2Fresh34 base)
      hmuS2 hscaledZetaSpan hthetaOff hbridge
  have hcover :
      ((↑(ftType34S2 base) : Set (ClassFunction M ℂ)) ∪
        (↑(ftType34S1 base) : Set (ClassFunction M ℂ))) =
      (↑(ftType34Layer base base.CInHU) :
        Set (ClassFunction M ℂ)) := by
    rw [Set.union_comm]
    exact ftType34S1UnionS2EqCLayerFresh34 base
  have hcohC : ftType34Coherent base base.CInHU := by
    simpa only [ftType34Coherent, hcover] using hcohUnion

  have hH0C : base.H0CInHU = base.CInHU := by
    change base.subgroupInHU (base.H0 ⊔ base.C) =
      base.subgroupInHU base.C
    rw [(FTtype34_Fcore_kernel_trivial base).H0_eq_bot, bot_sup_eq]
  apply FTtype34_noncoherence base
  rw [hH0C]
  exact hcohC

end FTType34StructureInternal

/-- `PFsection11.v: FTtype34_not_ortho_cycTIiso`, Peterfalvi (11.8). -/
theorem FTtype34_not_ortho_cycTIiso
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base) :
    let eta := fun i j ↦ base.targetMap (base.isoG.cyclicTIImage (i, j))
    let muZero := base.primeTI.primeTIRed base.isoM
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
    let etaColumnZero := ∑ i, eta i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
    ¬ ∀ i j,
      characterPairing (base.tau (muZero - zeta) - etaColumnZero)
        (eta i j) = 0 := by
  dsimp only
  change ¬ FTType34StructureInternal.eqProjection34 base
    (FTType34StructureInternal.dadeBridgeZero34 base zeta)
    (FTType34StructureInternal.etaColumn34 base
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
  exact FTType34StructureInternal.ftType34_not_ortho_final34
    base zeta hzeta

end

end Submission.OddOrder.PF
