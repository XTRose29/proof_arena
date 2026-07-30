import Submission.OddOrder.PF.Section10.FTType345TauAlpha

/-!
# The reduced-column identities in Peterfalvi (10.6)

This phase contains the two reduced-column identities consumed by the final
coherence calculation.  The proof uses the supported difference
`mu_j - d * zeta`; this is slightly shorter than the source's use of the dual
reference character and consumes the fixed SupportNorm orthogonality API
directly.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise IsMulCommutative
open FTType345ConstantsInternal

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
variable [IsMinSimpleOddGroup Gamma]
variable {M U W W₁ W₂ : Subgroup Gamma}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance tauReducedInvertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace FTType345CoherenceInternal

private theorem tauReduced_pairing_sub_left
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingLeft (a - b) c = _
  exact map_sub (characterPairingRight c) a b

private theorem tauReduced_pairing_sub_right
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingRight (b - c) a = _
  exact map_sub (characterPairingLeft a) b c

private theorem tauReduced_pairing_fintype_sum_right
    {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (a : ClassFunction Q ℂ) (f : I → ClassFunction Q ℂ) :
    characterPairing a (∑ i, f i) =
      ∑ i, characterPairing a (f i) := by
  change characterPairingLeft a (∑ i, f i) = _
  exact map_sum (characterPairingLeft a) f Finset.univ

private theorem tauReduced_fullDerived_sub_kernelLayer
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2) :
    (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) ⊆
      FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP) := by
  have hnot1 : FTtype M ≠ 1 :=
    FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
  have hgt : 2 < FTtype M := by
    have hrange := FTtype_range M
    omega
  have hcore : FTcore M = derivedWithin M :=
    FTcore_type_gt2 M hgt
  intro phi hphi
  simpa [ftType345InducedFamily10, FTtypePKernelLayer,
    PrimeDadeHypothesis.signalizerInKernel, hcore] using hphi

private theorem tauReduced_fullDerived_cfConjC_subset
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2) :
    cfConjC_subset
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP)) := by
  refine ⟨tauReduced_fullDerived_sub_kernelLayer
    hmaxM MtypeP notMtype2, ?_⟩
  intro phi hphi
  exact seqInd_inverse_mem (k := ℂ) (ftType345DerivedInM M)
    (⊤ : Subgroup (ftType345DerivedInM M)) ⊥ hphi

private theorem tauReduced_reducedColumn_mem
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP) j ∈
      ftType345InducedFamily10 M := by
  let K : Subgroup M := ftType345DerivedInM M
  apply (seqIndC1P (k := ℂ) K).mpr
  refine ⟨(ftType345PrimeTI MtypeP).primeTI_Ires
      (ftType345IsoM MtypeP) j, ?_, ?_⟩
  · intro htriv
    apply hj
    apply (ftType345PrimeTI MtypeP).prTIres_inj
      (ftType345IsoM MtypeP)
    exact htriv.trans
      ((ftType345PrimeTI MtypeP).prTIres0
        (ftType345IsoM MtypeP)).symm
  · exact ((ftType345PrimeTI MtypeP).cfInd_prTIres
      (ftType345IsoM MtypeP) j).symm

private theorem tauReduced_reference_difference_mem_closure
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j -
        (FTtype345_TIirr_degree MtypeP : ℂ) • zeta ∈
      AddSubgroup.closure
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
  let C := AddSubgroup.closure
    (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
  apply C.sub_mem
  · exact AddSubgroup.subset_closure
      (tauReduced_reducedColumn_mem MtypeP j hj)
  · simpa only [Nat.cast_smul_eq_nsmul] using
      C.nsmul_mem (AddSubgroup.subset_closure hzeta.mem_calS)
        (FTtype345_TIirr_degree MtypeP)

private theorem tauReduced_reference_difference_supportedOn_nonidentity
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j -
        (FTtype345_TIirr_degree MtypeP : ℂ) • zeta ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxOne : x = 1 := by simpa [nonidentitySet] using hx
  subst x
  have hdegree := (ftType345PrimeTI MtypeP).prTIred_1
    (ftType345IsoM MtypeP) j
  have hconstant :=
    (FTtype345_constants hmaxM MtypeP notMtype2).degree_constant
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
      j hj
  simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, smul_eq_mul]
  rw [hdegree, hconstant, hzeta.degree]
  ring

private theorem tauReduced_reference_difference_supportedOn_FTsupport0
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j -
        (FTtype345_TIirr_degree MtypeP : ℂ) • zeta ∈
      ClassFunction.supportedOn
        {x : M | (x : Gamma) ∈ FTsupport0 M} := by
  let K : Subgroup M := ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  have hindex : K.index = Nat.card W₁ := by
    have houter : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := MtypeP.1.2.2.2
    calc
      K.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq houter.2.1
  have hzetaSeq : zeta ∈
      seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥ := by
    simpa only [K, ftType345InducedFamily10] using hzeta.mem_calS
  have hmuSeq :
      (ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j ∈
        seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥ := by
    simpa only [K, ftType345InducedFamily10] using
      tauReduced_reducedColumn_mem MtypeP j hj
  have hzetaOne : zeta 1 = (K.index : ℂ) := by
    rw [hzeta.degree, hindex]
  have hmuOne :
      (ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j 1 =
        (Nat.card W₁ : ℂ) *
          (FTtype345_TIirr_degree MtypeP : ℂ) := by
    rw [(ftType345PrimeTI MtypeP).prTIred_1
      (ftType345IsoM MtypeP) j,
      (FTtype345_constants hmaxM MtypeP notMtype2).degree_constant
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
        j hj]
  have hcoefficient :
      (ftType345PrimeTI MtypeP).primeTIRed
            (ftType345IsoM MtypeP) j 1 / (K.index : ℂ) =
        (FTtype345_TIirr_degree MtypeP : ℂ) := by
    rw [hmuOne, hindex]
    field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne']
  have hsmall := seqInd_sub_lin_on (k := ℂ) K
    (calX := Iirr_kerD (k := ℂ) (⊤ : Subgroup K) ⊥)
    hzetaSeq hzetaOne hmuSeq
  rw [hcoefficient] at hsmall
  rw [ClassFunction.mem_supportedOn_iff] at hsmall ⊢
  intro x hx
  apply hsmall
  intro hxDerived
  apply hx
  apply FTsupp1_sub0 hmaxM
  have hnot1 : FTtype M ≠ 1 :=
    FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
  have hgt : 2 < FTtype M := by
    have hrange := FTtype_range M
    omega
  rw [FTsupp1_type_gt2 M hgt]
  change (x : Gamma) ∈ derivedWithin M ∧ (x : Gamma) ≠ 1
  refine ⟨hxDerived.1, ?_⟩
  intro hxOne
  exact hxDerived.2 (Subtype.ext hxOne)

private theorem tauReduced_source_pairing_isometry
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hcoh : coherent_with
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau hmaxM) tau₁)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    characterPairing
      (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j))
      (tau₁ ((ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j -
        (FTtype345_TIirr_degree MtypeP : ℂ) • zeta)) =
      characterPairing
        (FTtype345_bridge MtypeP zeta i j)
        ((ftType345PrimeTI MtypeP).primeTIRed
            (ftType345IsoM MtypeP) j -
          (FTtype345_TIirr_degree MtypeP : ℂ) • zeta) := by
  let psi := (ftType345PrimeTI MtypeP).primeTIRed
      (ftType345IsoM MtypeP) j -
    (FTtype345_TIirr_degree MtypeP : ℂ) • zeta
  have hpsiClosure := tauReduced_reference_difference_mem_closure
    MtypeP zeta hzeta j hj
  have hpsiNonidentity :=
    tauReduced_reference_difference_supportedOn_nonidentity
      hmaxM MtypeP notMtype2 zeta hzeta j hj
  have hpsiAgree : tau₁ psi = ftType345Tau hmaxM psi :=
    hcoh.agrees psi hpsiClosure hpsiNonidentity
  have hzetaVirtual : ClassFunction.IsVirtual zeta := by
    refine ⟨Finsupp.single ⟨zeta, hzeta.irreducible⟩ 1, ?_⟩
    simp
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    exact ((ftType345PrimeTI MtypeP).prTIred_char
      (ftType345IsoM MtypeP) j).isVirtual.sub
        (hzetaVirtual.natCast_smul (FTtype345_TIirr_degree MtypeP))
  have hDadePsiVirtual :
      ClassFunction.IsVirtual (ftType345Tau hmaxM psi) := by
    rw [← hpsiAgree]
    exact hcoh.mapsToVirtual psi hpsiClosure
  have hAlphaVirtual :=
    vchar_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i j
  have hDadeAlphaVirtual :=
    vchar_Dade_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i j hj
  have hAlphaSupport :=
    supp_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i j hj
  have hpsiSupport :=
    tauReduced_reference_difference_supportedOn_FTsupport0
      hmaxM MtypeP notMtype2 zeta hzeta j hj
  rw [hpsiAgree]
  calc
    characterPairing
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j))
        (ftType345Tau hmaxM psi) =
      starCharacterPairing
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j))
        (ftType345Tau hmaxM psi) :=
      (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hDadeAlphaVirtual hDadePsiVirtual).symm
    _ = starCharacterPairing
        (FTtype345_bridge MtypeP zeta i j) psi := by
      exact Dade_isometry (FT_Dade0_hyp M hmaxM)
        (FTtype345_bridge MtypeP zeta i j) psi
        hAlphaSupport hpsiSupport
    _ = characterPairing
        (FTtype345_bridge MtypeP zeta i j) psi :=
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hAlphaVirtual hpsiVirtual

/-! Peterfalvi (10.6)(a), first identity. -/
theorem ftType345_tau1mu
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hcoh : coherent_with
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau hmaxM) tau₁)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    tau₁ ((ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP) j) =
      (FTtype345_TIsign MtypeP : ℂ) •
        ∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Eta hmaxM MtypeP i j := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let isoG := ftType345IsoG hmaxM MtypeP
  let mu : ClassFunction M ℂ := pti.primeTIRed isoM j
  let psi : ClassFunction M ℂ :=
    mu - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta
  let deltaDifference (i : IrreducibleCharacter W₁ ℂ) :
      ClassFunction (⊤ : Subgroup Gamma) ℂ :=
    (FTtype345_TIsign MtypeP : ℂ) •
      (ftType345Eta hmaxM MtypeP i j -
        ftType345Eta hmaxM MtypeP i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
  have hsub := tauReduced_fullDerived_cfConjC_subset
    hmaxM MtypeP notMtype2
  have hmuMem : mu ∈ ftType345InducedFamily10 M := by
    exact tauReduced_reducedColumn_mem MtypeP j hj
  have hpsiClosure : psi ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
    exact tauReduced_reference_difference_mem_closure
      MtypeP zeta hzeta j hj
  have hpsiSupport : psi ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
    exact tauReduced_reference_difference_supportedOn_nonidentity
      hmaxM MtypeP notMtype2 zeta hzeta j hj
  have hpsiAgree : tau₁ psi = ftType345Tau hmaxM psi :=
    hcoh.agrees psi hpsiClosure hpsiSupport
  have hmuDecomp : tau₁ mu =
      tau₁ psi +
        (FTtype345_TIirr_degree MtypeP : ℂ) • tau₁ zeta := by
    rw [show mu = psi +
        (FTtype345_TIirr_degree MtypeP : ℂ) • zeta by
      dsimp only [psi]
      module]
    rw [map_add, map_smul]
  have hEtaOrthogonal (i : IrreducibleCharacter W₁ ℂ)
      (k : IrreducibleCharacter W₂ ℂ) :
      characterPairing
        (ftType345Eta hmaxM MtypeP i k) (tau₁ zeta) = 0 := by
    rw [characterPairing_comm]
    simpa only [ftType345Eta,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using
      coherent_ortho_cycTIiso
        (ftType345PrimeDade hmaxM MtypeP) isoM isoG
        (mFT_odd M) hsub hcoh hzeta.mem_calS hzeta.irreducible
        (IrreducibleCharacter.cyclicTICharacter defW i k)
  have hDifferenceOrthogonal
      (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (deltaDifference i)
        ((FTtype345_TIirr_degree MtypeP : ℂ) • tau₁ zeta) = 0 := by
    simp only [deltaDifference, characterPairing_smul_left,
      characterPairing_smul_right, tauReduced_pairing_sub_left,
      hEtaOrthogonal]
    ring
  have hmu2jMu (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (ftType345Mu2 MtypeP i j) mu = 1 := by
    change characterPairing
      ((ftType345PrimeTI MtypeP).primeTICharacter
        (ftType345IsoM MtypeP) i j)
      ((ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP) j) = 1
    simpa using
      (ftType345PrimeTI MtypeP).cfdot_prTIirr_red
        (ftType345IsoM MtypeP) i j j
  have hmu20Mu (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing
        (ftType345Mu2 MtypeP i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
        mu = 0 := by
    simpa only [mu, pti, isoM, ftType345Mu2, if_neg hj.symm] using
      (ftType345PrimeTI MtypeP).cfdot_prTIirr_red
        (ftType345IsoM MtypeP) i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) j
  have hmu2jZeta (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (ftType345Mu2 MtypeP i j) zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i j
  have hmu20Zeta (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing
        (ftType345Mu2 MtypeP i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
        zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i IrreducibleCharacter.trivial
  have hzetaMu : characterPairing zeta mu = 0 := by
    rw [characterPairing_comm]
    change characterPairing
      ((ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP) j) zeta = 0
    rw [(ftType345PrimeTI MtypeP).primeTIRed_eq_sum]
    change characterPairingRight zeta
      (∑ i : IrreducibleCharacter W₁ ℂ,
        ftType345Mu2 MtypeP i j) = 0
    rw [map_sum]
    exact Finset.sum_eq_zero (fun i _ ↦ hmu2jZeta i)
  have hzetaNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self
      ⟨zeta, hzeta.irreducible⟩
  have hAlphaPsi (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (FTtype345_bridge MtypeP zeta i j) psi =
        1 + FTtype345_ratio MtypeP *
          (FTtype345_TIirr_degree MtypeP : ℂ) := by
    simp only [psi, FTtype345_bridge, tauReduced_pairing_sub_left,
      tauReduced_pairing_sub_right, characterPairing_smul_left,
      characterPairing_smul_right, hmu2jMu, hmu20Mu,
      hmu2jZeta, hmu20Zeta, hzetaMu, hzetaNorm]
    ring
  have hZetaPsi : characterPairing zeta psi =
      -(FTtype345_TIirr_degree MtypeP : ℂ) := by
    simp only [psi, tauReduced_pairing_sub_right,
      characterPairing_smul_right, hzetaMu, hzetaNorm]
    ring
  have hPairDade (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j))
        (tau₁ psi) =
      characterPairing (FTtype345_bridge MtypeP zeta i j) psi := by
    exact tauReduced_source_pairing_isometry
      hmaxM MtypeP notMtype2 zeta hzeta tau₁ hcoh i j hj
  have hPairCoherent : characterPairing (tau₁ zeta) (tau₁ psi) =
      characterPairing zeta psi :=
    hcoh.isometry zeta
      (AddSubgroup.subset_closure hzeta.mem_calS) psi hpsiClosure
  have hEtaMu (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (deltaDifference i) (tau₁ mu) = 1 := by
    have hAlpha := ftType345_tau_alpha
      hmaxM MtypeP notMtype2 zeta hzeta tau₁ hcoh i j hj
    have hDifferenceDecomp : deltaDifference i =
        ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) +
          FTtype345_ratio MtypeP • tau₁ zeta := by
      rw [hAlpha]
      dsimp only [deltaDifference]
      module
    rw [hmuDecomp, characterPairing_add_right,
      hDifferenceOrthogonal i, add_zero, hDifferenceDecomp,
      characterPairing_add_left, characterPairing_smul_left,
      hPairDade i, hPairCoherent, hAlphaPsi i, hZetaPsi]
    ring
  have hcases := FTtypeP_coherent_TIred
    (ftType345PrimeDade hmaxM MtypeP) isoM isoG (mFT_odd M)
    (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
    tau₁ ⟨zeta, hzeta.irreducible⟩ j hsub hcoh hzeta.mem_calS hmuMem
  rcases hcases with hfirst | hsecond
  · simpa only [mu, pti, isoM,
      (FTtype345_constants hmaxM MtypeP notMtype2).sign_constant j hj]
      using hfirst
  · rcases hsecond with ⟨hdual, _⟩
    have hdualNe : IrreducibleCharacter.dual j ≠ j :=
      dual_ne_self_of_odd_of_ne_trivial
        (ftType345PrimeTI MtypeP).prime_cycTIhyp.right_odd_card hj
    have hdualNontrivial : IrreducibleCharacter.dual j ≠
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) := by
      intro h
      apply hj
      have hd := congrArg IrreducibleCharacter.dual h
      simpa using hd
    have hzero :
        characterPairing (deltaDifference IrreducibleCharacter.trivial)
          ((-((ftType345PrimeTI MtypeP).primeTISign
              (ftType345IsoM MtypeP) j : ℂ)) •
            ∑ x : IrreducibleCharacter W₁ ℂ,
              ftType345Eta hmaxM MtypeP x
                (IrreducibleCharacter.dual j)) = 0 := by
      have hsum :
          ∑ x : IrreducibleCharacter W₁ ℂ,
            characterPairing
              (ftType345Eta hmaxM MtypeP
                  (IrreducibleCharacter.trivial :
                    IrreducibleCharacter W₁ ℂ) j -
                ftType345Eta hmaxM MtypeP
                  (IrreducibleCharacter.trivial :
                    IrreducibleCharacter W₁ ℂ)
                  (IrreducibleCharacter.trivial :
                    IrreducibleCharacter W₂ ℂ))
              (ftType345Eta hmaxM MtypeP x
                (IrreducibleCharacter.dual j)) = 0 := by
        apply Finset.sum_eq_zero
        intro x hx
        rw [tauReduced_pairing_sub_left,
          (ftType345IsoG hmaxM MtypeP).characterPairing_cyclicTIImage,
          (ftType345IsoG hmaxM MtypeP).characterPairing_cyclicTIImage]
        simp only [Prod.mk.injEq]
        rw [if_neg (by
          intro h
          exact hdualNe h.2.symm),
          if_neg (by
            intro h
            exact hdualNontrivial h.2.symm)]
        ring
      simp only [deltaDifference, characterPairing_smul_left,
        characterPairing_smul_right,
        tauReduced_pairing_fintype_sum_right, hsum]
      ring
    have hpair := hEtaMu
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
    rw [hdual, hzero] at hpair
    exact (one_ne_zero hpair.symm).elim

private theorem tauReduced_card_ratio
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    (Nat.card W₁ : ℂ) * FTtype345_ratio MtypeP =
      (FTtype345_TIirr_degree MtypeP : ℂ) -
        (FTtype345_TIsign MtypeP : ℂ) := by
  rw [FTtype345_ratio]
  field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne']

private theorem tauReduced_sum_const_smul
    {Q I : Type} [Group Q] [Fintype I]
    (a : ℂ) (f : ClassFunction Q ℂ) :
    ∑ _i : I, a • f =
      ((Fintype.card I : ℂ) * a) • f := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

/-! Peterfalvi (10.6)(a), zero-column identity. -/
theorem ftType345_tau1mu0
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hcoh : coherent_with
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau hmaxM) tau₁) :
    ftType345Tau hmaxM
        ((ftType345PrimeTI MtypeP).primeTIRed
            (ftType345IsoM MtypeP)
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
          zeta) =
      (∑ i : IrreducibleCharacter W₁ ℂ,
        ftType345Eta hmaxM MtypeP i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) -
        tau₁ zeta := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let mu := fun j : IrreducibleCharacter W₂ ℂ ↦
    pti.primeTIRed isoM j
  let eta := fun i : IrreducibleCharacter W₁ ℂ ↦
    fun j : IrreducibleCharacter W₂ ℂ ↦
      ftType345Eta hmaxM MtypeP i j
  letI : IsCyclic W₁ := (ftType345PrimeTI MtypeP).complement_cyclic
  let j : IrreducibleCharacter W₂ ℂ := FTtype345_jOne MtypeP
  have hj : j ≠ IrreducibleCharacter.trivial :=
    FTtype345_jOne_ne_trivial MtypeP
  have hcardI :
      Fintype.card (IrreducibleCharacter W₁ ℂ) = Nat.card W₁ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hratio := tauReduced_card_ratio MtypeP
  have hsumMuJ :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Mu2 MtypeP i j) = mu j := by
    exact (pti.primeTIRed_eq_sum isoM j).symm
  have hsumMu0 :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Mu2 MtypeP i
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) =
        mu IrreducibleCharacter.trivial := by
    exact (pti.primeTIRed_eq_sum isoM IrreducibleCharacter.trivial).symm
  have hsumSignedMu0 :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          (FTtype345_TIsign MtypeP : ℂ) •
            ftType345Mu2 MtypeP i
              (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) =
        (FTtype345_TIsign MtypeP : ℂ) •
          mu IrreducibleCharacter.trivial := by
    rw [← Finset.smul_sum, hsumMu0]
  have hsumRatioZeta :
      (∑ _i : IrreducibleCharacter W₁ ℂ,
          FTtype345_ratio MtypeP • zeta) =
        ((FTtype345_TIirr_degree MtypeP : ℂ) -
          (FTtype345_TIsign MtypeP : ℂ)) • zeta := by
    rw [tauReduced_sum_const_smul
      (Q := M) (I := IrreducibleCharacter W₁ ℂ), hcardI, hratio]
  have hsumAlpha :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          FTtype345_bridge MtypeP zeta i j) =
        mu j - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta -
          (FTtype345_TIsign MtypeP : ℂ) •
            (mu IrreducibleCharacter.trivial - zeta) := by
    calc
      (∑ i : IrreducibleCharacter W₁ ℂ,
          FTtype345_bridge MtypeP zeta i j) =
          (∑ i : IrreducibleCharacter W₁ ℂ,
              ftType345Mu2 MtypeP i j) -
            (∑ i : IrreducibleCharacter W₁ ℂ,
              (FTtype345_TIsign MtypeP : ℂ) •
                ftType345Mu2 MtypeP i
                  (IrreducibleCharacter.trivial :
                    IrreducibleCharacter W₂ ℂ)) -
            (∑ _i : IrreducibleCharacter W₁ ℂ,
              FTtype345_ratio MtypeP • zeta) := by
            simp_rw [FTtype345_bridge]
            rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = mu j -
          (FTtype345_TIsign MtypeP : ℂ) •
            mu IrreducibleCharacter.trivial -
          ((FTtype345_TIirr_degree MtypeP : ℂ) -
            (FTtype345_TIsign MtypeP : ℂ)) • zeta := by
            rw [hsumMuJ, hsumSignedMu0, hsumRatioZeta]
      _ = mu j - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta -
          (FTtype345_TIsign MtypeP : ℂ) •
            (mu IrreducibleCharacter.trivial - zeta) := by
            module
  have hpsiClosure := tauReduced_reference_difference_mem_closure
    MtypeP zeta hzeta j hj
  have hpsiSupport :=
    tauReduced_reference_difference_supportedOn_nonidentity
      hmaxM MtypeP notMtype2 zeta hzeta j hj
  have hAgree :
      ftType345Tau hmaxM
          (mu j - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta) =
        tau₁ (mu j -
          (FTtype345_TIirr_degree MtypeP : ℂ) • zeta) := by
    exact (hcoh.agrees
      (mu j - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta)
      hpsiClosure hpsiSupport).symm
  have hTauMu : tau₁ (mu j) =
      (FTtype345_TIsign MtypeP : ℂ) •
        ∑ i : IrreducibleCharacter W₁ ℂ, eta i j := by
    exact ftType345_tau1mu hmaxM MtypeP notMtype2
      zeta hzeta tau₁ hcoh j hj
  have hsumTauAlpha :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) =
        (FTtype345_TIsign MtypeP : ℂ) •
            ((∑ i : IrreducibleCharacter W₁ ℂ, eta i j) -
              ∑ i : IrreducibleCharacter W₁ ℂ,
                eta i IrreducibleCharacter.trivial) -
          ((FTtype345_TIirr_degree MtypeP : ℂ) -
            (FTtype345_TIsign MtypeP : ℂ)) • tau₁ zeta := by
    calc
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) =
          ∑ i : IrreducibleCharacter W₁ ℂ,
            ((FTtype345_TIsign MtypeP : ℂ) •
                (eta i j - eta i IrreducibleCharacter.trivial) -
              FTtype345_ratio MtypeP • tau₁ zeta) := by
            apply Finset.sum_congr rfl
            intro i hi
            exact ftType345_tau_alpha hmaxM MtypeP notMtype2
              zeta hzeta tau₁ hcoh i j hj
      _ = (FTtype345_TIsign MtypeP : ℂ) •
            ((∑ i : IrreducibleCharacter W₁ ℂ, eta i j) -
              ∑ i : IrreducibleCharacter W₁ ℂ,
                eta i IrreducibleCharacter.trivial) -
          (∑ _i : IrreducibleCharacter W₁ ℂ,
            FTtype345_ratio MtypeP • tau₁ zeta) := by
            rw [Finset.sum_sub_distrib, ← Finset.smul_sum,
              Finset.sum_sub_distrib]
      _ = (FTtype345_TIsign MtypeP : ℂ) •
            ((∑ i : IrreducibleCharacter W₁ ℂ, eta i j) -
              ∑ i : IrreducibleCharacter W₁ ℂ,
                eta i IrreducibleCharacter.trivial) -
          ((FTtype345_TIirr_degree MtypeP : ℂ) -
            (FTtype345_TIsign MtypeP : ℂ)) • tau₁ zeta := by
            rw [tauReduced_sum_const_smul
              (Q := (⊤ : Subgroup Gamma))
              (I := IrreducibleCharacter W₁ ℂ), hcardI, hratio]
  have hMapped :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) =
        ftType345Tau hmaxM
            (mu j - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta) -
          (FTtype345_TIsign MtypeP : ℂ) •
            ftType345Tau hmaxM
              (mu IrreducibleCharacter.trivial - zeta) := by
    calc
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) =
          ftType345Tau hmaxM
            (∑ i : IrreducibleCharacter W₁ ℂ,
              FTtype345_bridge MtypeP zeta i j) := by
            rw [map_sum]
      _ = ftType345Tau hmaxM
          (mu j - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta -
            (FTtype345_TIsign MtypeP : ℂ) •
              (mu IrreducibleCharacter.trivial - zeta)) := by
            rw [hsumAlpha]
      _ = ftType345Tau hmaxM
            (mu j - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta) -
          (FTtype345_TIsign MtypeP : ℂ) •
            ftType345Tau hmaxM
              (mu IrreducibleCharacter.trivial - zeta) := by
            rw [map_sub, map_smul]
  rw [hsumTauAlpha, hAgree, map_sub, map_smul, hTauMu] at hMapped
  rw [map_sub]
  have hsign : IsSign (FTtype345_TIsign MtypeP) :=
    (ftType345PrimeTI MtypeP).primeTISign_isSign
      (ftType345IsoM MtypeP) (FTtype345_jOne MtypeP)
  rcases hsign with hsign | hsign
  · rw [hsign] at hMapped
    norm_num at hMapped
    calc
      ftType345Tau hmaxM (mu IrreducibleCharacter.trivial) -
            ftType345Tau hmaxM zeta =
          ((∑ i : IrreducibleCharacter W₁ ℂ, eta i j) -
              (FTtype345_TIirr_degree MtypeP : ℂ) • tau₁ zeta) -
            ((∑ i : IrreducibleCharacter W₁ ℂ, eta i j) -
              (∑ i : IrreducibleCharacter W₁ ℂ,
                eta i IrreducibleCharacter.trivial) -
              ((FTtype345_TIirr_degree MtypeP : ℂ) - 1) • tau₁ zeta) := by
            rw [hMapped]
            module
      _ = (∑ i : IrreducibleCharacter W₁ ℂ,
              eta i IrreducibleCharacter.trivial) - tau₁ zeta := by
            module
  · rw [hsign] at hMapped
    norm_num at hMapped
    calc
      ftType345Tau hmaxM (mu IrreducibleCharacter.trivial) -
            ftType345Tau hmaxM zeta =
          ((-1 : ℂ) •
                ((∑ i : IrreducibleCharacter W₁ ℂ, eta i j) -
                  ∑ i : IrreducibleCharacter W₁ ℂ,
                    eta i IrreducibleCharacter.trivial) -
              ((FTtype345_TIirr_degree MtypeP : ℂ) + 1) • tau₁ zeta) -
            ((-1 : ℂ) •
                (∑ i : IrreducibleCharacter W₁ ℂ, eta i j) -
              (FTtype345_TIirr_degree MtypeP : ℂ) • tau₁ zeta) := by
            rw [hMapped]
            module
      _ = (∑ i : IrreducibleCharacter W₁ ℂ,
              eta i IrreducibleCharacter.trivial) - tau₁ zeta := by
            module

end FTType345CoherenceInternal

end

end Submission.OddOrder.PF
