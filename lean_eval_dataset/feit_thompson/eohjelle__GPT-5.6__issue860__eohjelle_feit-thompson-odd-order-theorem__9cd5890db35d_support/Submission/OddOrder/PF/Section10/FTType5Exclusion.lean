import Submission.OddOrder.BG.Section16.TypesAndSupport
import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.PF.Section06.OddFrobeniusQuotient
import Submission.OddOrder.PF.Section06.SibleyCoherence
import Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence
import Submission.OddOrder.PF.Section09.PTypeFCoreKernel
import Submission.OddOrder.PF.Section09.PTypeCoreCoherence
import Submission.OddOrder.PF.Section10.FTType345Bridge

/-!
# Peterfalvi Section 10: exclusion of type V

This module proves Peterfalvi (10.9)--(10.11): the zero-column Dade bridge,
the exclusion of type V, and the resulting prime and type-II core facts.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTType345ConstantsInternal
open scoped BigOperators Classical Pointwise IsMulCommutative commutatorElement

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
variable [IsMinSimpleOddGroup Gamma]
variable {M U W W₁ W₂ : Subgroup Gamma}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance zeroBridgeInvertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private noncomputable abbrev ftType5Tau
    (M : Subgroup Gamma)
    (hM : M ∈ minSimple_max_groups (G := Gamma)) :
    ClassFunction M ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup Gamma) ℂ :=
  Dade (FT_Dade0_hyp M hM)

private abbrev ftType5PrimeTI
    {M U W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hP : of_typeP M U W W₁ W₂ defW) :
    PrimeTIHypothesis M (derivedWithin M) W W₁ W₂ defW :=
  FT_primeTI_hyp defW hP

private noncomputable abbrev ftType5IsoM
    {M U W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hP : of_typeP M U W W₁ W₂ defW) :
    CyclicTIIsometryData (k := ℂ) (ftType5PrimeTI hP).prime_cycTIhyp :=
  (ftType5PrimeTI hP).prime_cycTIhyp.cyclicTIIsometryData

private noncomputable abbrev ftType5PrimeDade
    {M U W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hM : M ∈ minSimple_max_groups (G := Gamma))
    (hP : of_typeP M U W W₁ W₂ defW) :
    PrimeDadeHypothesis (⊤ : Subgroup Gamma) M (derivedWithin M)
      (FTcore M) (FTsupport M) (FTsupport0 M) W W₁ W₂ defW :=
  FT_prDade_hyp defW hM hP

private noncomputable abbrev ftType5IsoG
    {M U W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hM : M ∈ minSimple_max_groups (G := Gamma))
    (hP : of_typeP M U W W₁ W₂ defW) :
    CyclicTIIsometryData (k := ℂ)
      (ftType5PrimeDade hM hP).prDade_cycTI :=
  (ftType5PrimeDade hM hP).prDade_cycTI.cyclicTIIsometryData

private noncomputable abbrev ftType5Eta
    {M U W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hM : M ∈ minSimple_max_groups (G := Gamma))
    (hP : of_typeP M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction (⊤ : Subgroup Gamma) ℂ :=
  (ftType5IsoG hM hP).cyclicTIImage (i, j)

private noncomputable abbrev ftType5Mu
    {M U W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hP : of_typeP M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction M ℂ :=
  (ftType5PrimeTI hP).primeTIRed (ftType5IsoM hP) j

private theorem pairing_sub_left
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingLeft (a - b) c = _
  exact map_sub (characterPairingRight c) a b

private theorem pairing_sub_right
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingRight (b - c) a = _
  exact map_sub (characterPairingLeft a) b c

private theorem pairing_neg_left
    {Q : Type} [Group Q] [Fintype Q]
    (a b : ClassFunction Q ℂ) :
    characterPairing (-a) b = -characterPairing a b := by
  change characterPairingLeft (-a) b = _
  exact map_neg (characterPairingRight b) a

private theorem pairing_fintype_sum_left
    {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ) (b : ClassFunction Q ℂ) :
    characterPairing (∑ i, f i) b =
      ∑ i, characterPairing (f i) b := by
  exact map_sum (characterPairingRight b) f Finset.univ

private theorem pairing_fintype_sum_right
    {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (a : ClassFunction Q ℂ) (f : I → ClassFunction Q ℂ) :
    characterPairing a (∑ i, f i) =
      ∑ i, characterPairing a (f i) := by
  exact map_sum (characterPairingLeft a) f Finset.univ

private theorem cyclicTIImage_isVirtual
    {Q W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {h : CyclicTIHypothesis Q W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := ℂ) h)
    (p : IrreducibleCharacter W₁ ℂ × IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (iso.cyclicTIImage p) := by
  let chi : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW p.1 p.2
  let z : VirtualCharacter W ℂ := Finsupp.single chi 1
  exact ⟨iso.virtualMap z, by
    calc
      VirtualCharacter.realize (iso.virtualMap z) =
          iso.linearMap (VirtualCharacter.realize z) :=
        iso.realize_virtualMap z
      _ = iso.cyclicTIImage p := by
        simp [z, chi, CyclicTIIsometryData.cyclicTIImage,
          CyclicTIIsometryData.cyclicTISourceIrreducible]⟩

private theorem fintype_sum_isVirtual
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

private theorem zeroColumn_fullSupport
    {M U W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hM : M ∈ minSimple_max_groups (G := Gamma))
    (hP : of_typeP M U W W₁ W₂ defW)
    (hnot2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta) :
    ftType5Mu hP
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        zeta ∈ ClassFunction.supportedOn
          {x : M | (x : Gamma) ∈ FTsupport M} := by
  let K : Subgroup M := ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  have hindex : K.index = Nat.card W₁ := by
    have houter : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := hP.1.2.2.2
    calc
      K.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq houter.2.1
  have hbase := cfInd1_sub_lin_on (k := ℂ) K hzeta.mem_calS (by
    rw [hzeta.degree, hindex])
  rw [← (ftType5PrimeTI hP).prTIred0 (ftType5IsoM hP)] at hbase
  have hnot1 : FTtype M ≠ 1 :=
    FTtypeP_neq1 M U W W₁ W₂ defW hM hP
  have hgt : 2 < FTtype M := by
    have hrange := FTtype_range M
    omega
  rw [ClassFunction.mem_supportedOn_iff] at hbase ⊢
  intro x hx
  apply hbase x
  intro hxK
  apply hx
  have hxDerived : (x : Gamma) ∈ subgroupNonidentity (derivedWithin M) :=
    ⟨hxK.1, fun hxOne ↦ hxK.2 (Subtype.ext hxOne)⟩
  change (x : Gamma) ∈ FTsupport M
  rw [FTsupp_eq1 hM hgt, FTsupp1_type_gt2 M hgt]
  exact hxDerived

/-! ## Peterfalvi (10.9) -/

/-- Peterfalvi (10.9), the zero-column Dade bridge. -/
theorem FTtype345_Dade_bridge0
    {M U W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (hM : M ∈ minSimple_max_groups (G := Gamma))
    (hP : of_typeP M U W W₁ W₂ defW)
    (hnot2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (hw : Nat.card W₁ < Nat.card W₂) :
    ∃ chi : ClassFunction (⊤ : Subgroup Gamma) ℂ,
      ftType5Tau M hM
          (ftType5Mu hP IrreducibleCharacter.trivial - zeta) =
        (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType5Eta hM hP i IrreducibleCharacter.trivial) - chi ∧
      ClassFunction.IsVirtual chi ∧
      characterPairing chi chi = 1 ∧
      ∀ i j, characterPairing chi (ftType5Eta hM hP i j) = 0 := by
  classical
  let pti := ftType5PrimeTI hP
  let isoM := ftType5IsoM hP
  let isoG := ftType5IsoG hM hP
  let j0 : IrreducibleCharacter W₂ ℂ := IrreducibleCharacter.trivial
  let psi : ClassFunction M ℂ := pti.primeTIRed isoM j0 - zeta
  let psiG : ClassFunction (⊤ : Subgroup Gamma) ℂ := ftType5Tau M hM psi

  have hzetaVirtual : ClassFunction.IsVirtual zeta := by
    exact ⟨Finsupp.single ⟨zeta, hzeta.irreducible⟩ 1, by simp⟩
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    exact (pti.prTIred_char isoM j0).isVirtual.sub hzetaVirtual
  have hpsiFull : psi ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport M} := by
    exact zeroColumn_fullSupport hM hP hnot2 zeta hzeta
  have hpsiSupport : psi ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport0 M} := by
    rw [ClassFunction.mem_supportedOn_iff] at hpsiFull ⊢
    intro x hx
    apply hpsiFull x
    intro hxFull
    exact hx (FTsupp_sub0 M hxFull)
  obtain ⟨psiZ, hpsiZ⟩ := hpsiVirtual
  have hpsiVirtual' : ClassFunction.IsVirtual psi := ⟨psiZ, hpsiZ⟩
  obtain ⟨psiGZ, hpsiGZ, _⟩ :=
    (Dade_Zisometry (FT_Dade0_hyp M hM)).2 psiZ (by
      simpa [hpsiZ] using hpsiSupport)
  have hpsiGVirtual : ClassFunction.IsVirtual psiG := by
    exact ⟨psiGZ, by
      simpa [psiG, psi, hpsiZ, ftType5Tau] using hpsiGZ.symm⟩
  have hpsiGZRealize : VirtualCharacter.realize psiGZ = psiG := by
    simpa [psiG, psi, hpsiZ, ftType5Tau] using hpsiGZ.symm

  have hmuZ : characterPairing (pti.primeTIRed isoM j0) zeta = 0 := by
    rw [pti.primeTIRed_eq_sum]
    change characterPairingRight zeta
      (∑ i : IrreducibleCharacter W₁ ℂ,
        pti.primeTICharacter isoM i j0) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i hi
    exact FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      hP zeta hzeta i j0
  have hzMu : characterPairing zeta (pti.primeTIRed isoM j0) = 0 := by
    rw [characterPairing_comm, hmuZ]
  have hmuNorm : characterPairing (pti.primeTIRed isoM j0)
      (pti.primeTIRed isoM j0) = (Nat.card W₁ : ℂ) :=
    pti.cfnorm_prTIred isoM j0
  have hzetaNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self ⟨zeta, hzeta.irreducible⟩
  have hpsiNorm : characterPairing psi psi = (Nat.card W₁ + 1 : ℂ) := by
    simp only [psi]
    rw [pairing_sub_left, pairing_sub_right, pairing_sub_right,
      hmuNorm, hmuZ, hzMu, hzetaNorm]
    push_cast
    ring
  have hpsiGNorm : characterPairing psiG psiG =
      (Nat.card W₁ + 1 : ℂ) := by
    calc
      characterPairing psiG psiG = starCharacterPairing psiG psiG :=
        (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hpsiGVirtual hpsiGVirtual).symm
      _ = starCharacterPairing psi psi := by
        simpa [psiG, ftType5Tau] using
          Dade_isometry (FT_Dade0_hyp M hM) psi psi hpsiSupport hpsiSupport
      _ = characterPairing psi psi :=
        PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hpsiVirtual' hpsiVirtual'
      _ = (Nat.card W₁ + 1 : ℂ) := hpsiNorm

  have h00 : characterPairing psiG
      (isoG.cyclicTIImage
        (IrreducibleCharacter.trivial, IrreducibleCharacter.trivial)) = 1 := by
    let oneG : ClassFunction (⊤ : Subgroup Gamma) ℂ :=
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup Gamma) ℂ)
    let oneM : ClassFunction M ℂ :=
      (IrreducibleCharacter.trivial : IrreducibleCharacter M ℂ)
    have heta00 : isoG.cyclicTIImage
          ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ),
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) =
        oneG := by
      change isoG.linearMap
          (IrreducibleCharacter.cyclicTICharacter defW
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :
              ClassFunction W ℂ) = oneG
      rw [IrreducibleCharacter.cyclicTICharacter_trivial, isoG.map_trivial]
    have honeGVirtual : ClassFunction.IsVirtual oneG := by
      exact ⟨Finsupp.single
        (IrreducibleCharacter.trivial :
          IrreducibleCharacter (⊤ : Subgroup Gamma) ℂ) 1, by
            simp [oneG]⟩
    have honeMVirtual : ClassFunction.IsVirtual oneM := by
      exact ⟨Finsupp.single
        (IrreducibleCharacter.trivial : IrreducibleCharacter M ℂ) 1, by
            simp [oneM]⟩
    have hcomap :
        ClassFunction.comap
            (Subgroup.inclusion (FT_Dade0_hyp M hM).2.1) oneG = oneM := by
      ext x
      simp [oneG, oneM]
    have hrecip := Dade_reciprocity
      (FT_Dade0_hyp M hM) psi oneG hpsiSupport (by
        intro a ha x
        simp [oneG])
    have hstar : starCharacterPairing psiG oneG =
        starCharacterPairing psi oneM := by
      simpa [psiG, ftType5Tau, hcomap] using hrecip
    have hpair : characterPairing psiG oneG =
        characterPairing psi oneM := by
      calc
        characterPairing psiG oneG = starCharacterPairing psiG oneG :=
          (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
            hpsiGVirtual honeGVirtual).symm
        _ = starCharacterPairing psi oneM := hstar
        _ = characterPairing psi oneM :=
          PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
            hpsiVirtual' honeMVirtual
    have hmuTriv : characterPairing (pti.primeTIRed isoM j0) oneM = 1 := by
      rw [characterPairing_comm]
      have h := pti.cfdot_prTIirr_red isoM
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j0 j0
      rw [if_pos rfl] at h
      simpa [oneM, j0, PrimeTIHypothesis.primeTICharacter,
        pti.prTIirr00 isoM] using h
    have htrivZ : characterPairing oneM zeta = 0 := by
      have h :=
        FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
          hP zeta hzeta
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j0
      simpa [oneM, j0, ftType345Mu2,
        PrimeTIHypothesis.primeTICharacter, pti.prTIirr00 isoM] using h
    have hzetaTriv : characterPairing zeta oneM = 0 := by
      rw [characterPairing_comm, htrivZ]
    have hsource : characterPairing psi oneM = 1 := by
      simp only [psi]
      rw [pairing_sub_left, hmuTriv, hzetaTriv, sub_zero]
    rw [heta00]
    exact hpair.trans hsource

  have hzero : Set.EqOn
      (fun w : W ↦ psiG
        ⟨w, (ftType5PrimeDade hM hP).prDade_cycTI.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
    intro w hwCyclic
    let pd := ftType5PrimeDade hM hP
    let wM : M := ⟨w, pti.directProduct_le_group w.property⟩
    let wG : (⊤ : Subgroup Gamma) :=
      ⟨w, pd.prDade_cycTI.le_group w.property⟩
    have hwAmbient : (w : Gamma) ∈ cyclicTISet W W₁ W₂ := hwCyclic
    have hwClass : (w : Gamma) ∈
        classSupportWithin M (cyclicTISet W W₁ W₂) := by
      exact ⟨(w : Gamma), hwAmbient, 1, M.one_mem, by simp⟩
    have hwA0 : (w : Gamma) ∈ FTsupport0 M := by
      rw [FTtypeP_supp0_def defW hM hP]
      exact Or.inr hwClass
    have hwNotFull : (w : Gamma) ∉ FTsupport M := by
      have hnot1 : FTtype M ≠ 1 :=
        FTtypeP_neq1 M U W W₁ W₂ defW hM hP
      have hgt : 2 < FTtype M := by
        have hrange := FTtype_range M
        omega
      rw [FTsupp_eq1 hM hgt, FTsupp1_type_gt2 M hgt]
      intro hwFull
      exact pd.prDade_supp_disjoint hwAmbient hwFull.1
    have hDade := Dade_id (FT_Dade0_hyp M hM) psi hwA0
    change psiG wG = (0 : W → ℂ) w
    simp only [Pi.zero_apply]
    calc
      psiG wG = psi wM := by
        simpa [psiG, ftType5Tau, wG, wM] using hDade
      _ = 0 := ClassFunction.eq_zero_of_mem_supportedOn hpsiFull hwNotFull

  letI : IsCyclic W₁ := pti.complement_cyclic
  letI : IsCyclic W₂ := pti.fixed_cyclic
  have hcard₁ : Fintype.card (IrreducibleCharacter W₁ ℂ) = Nat.card W₁ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hcard₂ : Fintype.card (IrreducibleCharacter W₂ ℂ) = Nat.card W₂ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hpsiGZNorm : normSq psiGZ = (Nat.card W₁ + 1 : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self,
      hpsiGZRealize, hpsiGNorm]
    push_cast
    rfl
  have hNCle : isoG.cyclicTINC psiG ≤ Nat.card W₁ + 1 := by
    have hbound := isoG.cyclicTINC_realize_le_normSq psiGZ
    rw [hpsiGZRealize, hpsiGZNorm] at hbound
    exact_mod_cast hbound
  have hsmall : isoG.cyclicTINC psiG <
      2 * min
        (Fintype.card (IrreducibleCharacter W₁ ℂ))
        (Fintype.card (IrreducibleCharacter W₂ ℂ)) := by
    rw [hcard₁, hcard₂, Nat.min_eq_left hw.le]
    have hleft := (ftType5PrimeDade hM hP).prDade_cycTI.two_lt_card_left
    omega

  have h00Linear : characterPairing psiG
      (isoG.linearMap
        (IrreducibleCharacter.cyclicTICharacter defW
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :
            ClassFunction W ℂ)) = 1 := by
    simpa only [CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using h00

  rcases isoG.small_cyclicTINC psiG hzero
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
      hsmall (by rw [h00Linear]; exact one_ne_zero) with hrow | hcolumn
  · have hrow' : ∀ i j,
        characterPairing psiG (isoG.cyclicTIImage (i, j)) =
          if j = IrreducibleCharacter.trivial then 1 else 0 := by
      intro i j
      simpa only [CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible,
        h00Linear] using hrow i j
    let coefficient (ij : IrreducibleCharacter W₁ ℂ ×
        IrreducibleCharacter W₂ ℂ) : ℂ :=
      characterPairing psiG (isoG.cyclicTIImage ij)
    let X : ClassFunction (⊤ : Subgroup Gamma) ℂ :=
      ∑ ij : IrreducibleCharacter W₁ ℂ ×
          IrreducibleCharacter W₂ ℂ,
        coefficient ij • isoG.cyclicTIImage ij
    let residual : ClassFunction (⊤ : Subgroup Gamma) ℂ := psiG - X
    have hsplit : psiG = X + residual := by
      dsimp [residual]
      abel
    have hresOrth (i : IrreducibleCharacter W₁ ℂ)
        (j : IrreducibleCharacter W₂ ℂ) :
        characterPairing residual (isoG.cyclicTIImage (i, j)) = 0 := by
      simp only [residual]
      rw [pairing_sub_left]
      have hprojection :
          characterPairing X (isoG.cyclicTIImage (i, j)) =
            coefficient (i, j) := by
        simp only [X]
        change characterPairing
            (∑ ij : IrreducibleCharacter W₁ ℂ ×
                IrreducibleCharacter W₂ ℂ,
              coefficient ij • isoG.cyclicTIImage ij)
            (isoG.cyclicTIImage (i, j)) = coefficient (i, j)
        rw [pairing_fintype_sum_left]
        simp only [characterPairing_smul_left,
          isoG.characterPairing_cyclicTIImage]
        rw [Finset.sum_eq_single (i, j)]
        · simp
        · intro q _ hq
          simp [hq]
        · simp
      rw [hprojection]
      simp only [coefficient, sub_self]
    let rowSum : ClassFunction (⊤ : Subgroup Gamma) ℂ :=
      ∑ i : IrreducibleCharacter W₁ ℂ,
        isoG.cyclicTIImage (i, IrreducibleCharacter.trivial)
    have hXrow : X = rowSum := by
      simp only [X, rowSum]
      simp only [coefficient]
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro i _
      rw [show (∑ j : IrreducibleCharacter W₂ ℂ,
          characterPairing psiG (isoG.cyclicTIImage (i, j)) •
            isoG.cyclicTIImage (i, j)) =
          isoG.cyclicTIImage (i, IrreducibleCharacter.trivial) by
        rw [Finset.sum_eq_single IrreducibleCharacter.trivial]
        · rw [hrow' i IrreducibleCharacter.trivial,
            if_pos rfl, one_smul]
        · intro j _ hj
          rw [hrow' i j, if_neg hj, zero_smul]
        · simp]
    let chi : ClassFunction (⊤ : Subgroup Gamma) ℂ := -residual
    have hXVirtual : ClassFunction.IsVirtual X := by
      rw [hXrow]
      simp only [rowSum]
      exact fintype_sum_isVirtual
        (fun i ↦ isoG.cyclicTIImage
          (i, IrreducibleCharacter.trivial))
        (fun i ↦ cyclicTIImage_isVirtual isoG
          (i, IrreducibleCharacter.trivial))
    have hresVirtual : ClassFunction.IsVirtual residual := by
      simpa [residual] using hpsiGVirtual.sub hXVirtual
    have hchiVirtual : ClassFunction.IsVirtual chi := hresVirtual.neg
    have hXNorm : characterPairing X X = (Nat.card W₁ : ℂ) := by
      rw [hXrow]
      simp only [rowSum, pairing_fintype_sum_left,
        pairing_fintype_sum_right,
        isoG.characterPairing_cyclicTIImage]
      simp [hcard₁]
    have hresNorm : characterPairing residual residual = 1 := by
      have hresX : characterPairing residual X = 0 := by
        rw [hXrow]
        simp only [rowSum, pairing_fintype_sum_right]
        exact Finset.sum_eq_zero (fun i _ ↦
          hresOrth i IrreducibleCharacter.trivial)
      have hXres : characterPairing X residual = 0 := by
        rw [characterPairing_comm, hresX]
      have hnorm := hpsiGNorm
      rw [hsplit, characterPairing_add_left,
        characterPairing_add_right, characterPairing_add_right,
        hXNorm, hXres, hresX] at hnorm
      push_cast at hnorm
      linear_combination hnorm
    have hchiNorm : characterPairing chi chi = 1 := by
      dsimp [chi]
      rw [← neg_one_smul ℂ residual,
        characterPairing_smul_left, characterPairing_smul_right, hresNorm]
      norm_num
    exact ⟨chi, by
          change psiG = rowSum - chi
          rw [hsplit, hXrow]
          dsimp [chi]
          abel,
        hchiVirtual,
        hchiNorm,
        by
          intro i j
          dsimp [chi]
          rw [pairing_neg_left, hresOrth i j, neg_zero]⟩
  · exfalso
    have hcolumn' : ∀ i j,
        characterPairing psiG (isoG.cyclicTIImage (i, j)) =
          if i = IrreducibleCharacter.trivial then 1 else 0 := by
      intro i j
      simpa only [CyclicTIIsometryData.cyclicTIImage,
        CyclicTIIsometryData.cyclicTISourceIrreducible,
        h00Linear] using hcolumn i j
    let line : Finset
        (IrreducibleCharacter W₁ ℂ × IrreducibleCharacter W₂ ℂ) :=
      Finset.univ.image fun j ↦
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ), j)
    have hlinecard : line.card =
        Fintype.card (IrreducibleCharacter W₂ ℂ) := by
      change (Finset.univ.image
        (fun j : IrreducibleCharacter W₂ ℂ ↦
          ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ), j))).card = _
      rw [Finset.card_image_of_injective _
        (Prod.mk_right_injective IrreducibleCharacter.trivial),
        Finset.card_univ]
    have hlineSub : line ⊆ isoG.cyclicTICoefficientSupport psiG := by
      intro p hp
      obtain ⟨j, -, rfl⟩ := Finset.mem_image.mp hp
      rw [isoG.mem_cyclicTICoefficientSupport,
        hcolumn' IrreducibleCharacter.trivial j, if_pos rfl]
      exact one_ne_zero
    have hW₂le : Nat.card W₂ ≤ isoG.cyclicTINC psiG := by
      rw [← hcard₂, ← hlinecard]
      exact Finset.card_le_card hlineSub
    have hodd₁ :=
      (ftType5PrimeDade hM hP).prDade_cycTI.left_odd_card
    have hodd₂ :=
      (ftType5PrimeDade hM hP).prDade_cycTI.right_odd_card
    rcases hodd₁ with ⟨a, ha⟩
    rcases hodd₂ with ⟨b, hb⟩
    omega

/-! ## Peterfalvi (10.8) -/

/-- The exported type-III--V noncoherence statement. -/
theorem FTtype345_noncoherence
    (M : Subgroup Gamma)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma)) :
    2 < FTtype M →
      ¬ coherent
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
        (nonidentitySet M) (ftType5Tau M hmaxM) := by
  intro hgt hcoherent
  have hnot1 : FTtype M ≠ 1 := by omega
  have hnot2 : FTtype M ≠ 2 := by omega
  obtain ⟨U, W, W₁, W₂, defW, hP⟩ :=
    FTtypeP_witness M hmaxM hnot1
  obtain ⟨zeta, hzeta⟩ := FTtypeP_ref_irr hmaxM hP
  obtain ⟨tau₁, htau₁⟩ := hcoherent
  exact FTtype345_noncoherence_main
    hmaxM hP hnot2 zeta hzeta tau₁ htau₁

/-! ## Peterfalvi (10.10) -/

private theorem ftType5_typeV_cases
    (MtypeV : of_typeV M U W W₁ W₂ defW)
    (hFcoreDerived : Fitting_core M = derivedWithin M)
    {p : ℕ} (hp : p.Prime)
    (hHp : IsPGroup p (derivedWithin M))
    (hHnonabelian : ¬ IsMulCommutative (derivedWithin M))
    (hnotdvd : ¬ Nat.card W₁ ∣ p - 1) :
    IsNormalizedTI
        (subgroupNonidentity (derivedWithin M)) ⊤ M ∨
      Nat.card (pCore p (derivedWithin M)) = p ^ 3 ∧
        Nat.card W₁ ∣ p + 1 ∧
        IsCyclic (pPrimeCore p (derivedWithin M)) := by
  classical
  have hHne : derivedWithin M ≠ ⊥ := by
    intro hbot
    apply hHnonabelian
    rw [hbot]
    infer_instance
  letI : Nontrivial (derivedWithin M) :=
    (derivedWithin M).nontrivial_iff_ne_bot.mpr hHne
  letI : Fact p.Prime := ⟨hp⟩
  have hsupport : primeSupport (Nat.card (derivedWithin M)) = {p} :=
    hHp.primeSupport_natCard_eq_singleton
  have hprimeUnique : ∀ {q : ℕ},
      q ∈ primeSupport (Nat.card (derivedWithin M)) → q = p := by
    intro q hq
    rw [hsupport] at hq
    exact Set.mem_singleton_iff.mp hq
  have hcardEq : Nat.card (Fitting_core M) =
      Nat.card (derivedWithin M) :=
    Nat.card_congr (MulEquiv.subgroupCongr hFcoreDerived).toEquiv
  have hcases := MtypeV.2.2
  rcases hcases with hTI | hrest
  · exact Or.inl (by simpa only [hFcoreDerived] using hTI)
  · rcases hrest with hsecond | hthird
    · rcases hsecond with ⟨q, hq, hdiv, _hcyclic⟩
      have hq' : q ∈ primeSupport (Nat.card (derivedWithin M)) := by
        simpa only [hcardEq] using hq
      exact (hnotdvd (by simpa only [hprimeUnique hq'] using hdiv)).elim
    · rcases hthird with ⟨q, hq, hcard, hdiv, hcyclic⟩
      have hq' : q ∈ primeSupport (Nat.card (derivedWithin M)) := by
        simpa only [hcardEq] using hq
      have hqp : q = p := hprimeUnique hq'
      subst q
      let e : Fitting_core M ≃* derivedWithin M :=
        MulEquiv.subgroupCongr hFcoreDerived
      have hmapCore : (pCore p (Fitting_core M)).map e.toMonoidHom =
          pCore p (derivedWithin M) :=
        FTContextInternal.pCore_map_mulEquiv8 p e
      have hcard' : Nat.card (pCore p (derivedWithin M)) = p ^ 3 := by
        calc
          Nat.card (pCore p (derivedWithin M)) =
              Nat.card ((pCore p (Fitting_core M)).map e.toMonoidHom) := by
            rw [hmapCore]
          _ = Nat.card (pCore p (Fitting_core M)) :=
            Subgroup.card_map_of_injective e.injective
          _ = p ^ 3 := hcard
      let ep : pPrimeCore p (Fitting_core M) ≃*
          (pPrimeCore p (Fitting_core M)).map e.toMonoidHom :=
        (pPrimeCore p (Fitting_core M)).equivMapOfInjective
          e.toMonoidHom e.injective
      have hcyclicMap : IsCyclic
          ((pPrimeCore p (Fitting_core M)).map e.toMonoidHom) :=
        ep.isCyclic.mp hcyclic
      have hcyclic' : IsCyclic (pPrimeCore p (derivedWithin M)) := by
        rw [MathlibSupport.map_pPrimeCore_eq_mulEquiv e] at hcyclicMap
        exact hcyclicMap
      exact Or.inr ⟨hcard', hdiv, hcyclic'⟩

/-- The numerical core of Peterfalvi (10.10.1).  In the application,
`w₁ = |W₁|`, `w₂ = |W₂| = p`, and the index bound is converted to
`p² ≤ 4w₁² + 1` using the extraspecial third branch. -/
private theorem ftType5_step_10_10_1_nat
    {p w₁ w₂ : ℕ}
    (hp : p.Prime) (hpOdd : Odd p)
    (hw₁Odd : Odd w₁) (hw₁gt2 : 2 < w₁)
    (hdiv : w₁ ∣ p + 1)
    (hub : p ^ 2 ≤ 4 * w₁ ^ 2 + 1)
    (hw₂ : w₂ = p) :
    p = 2 * w₁ - 1 ∧ w₁ < w₂ := by
  have htwo : 2 ∣ p + 1 := even_iff_two_dvd.mp hpOdd.add_one
  have hcop : Nat.Coprime 2 w₁ :=
    Nat.coprime_two_left.mpr hw₁Odd
  have htwodiv : 2 * w₁ ∣ p + 1 :=
    hcop.mul_dvd_of_dvd_of_dvd htwo hdiv
  obtain ⟨k, hk⟩ := htwodiv
  have hkpos : 0 < k := by
    by_contra hknot
    have hkzero : k = 0 := Nat.eq_zero_of_not_pos hknot
    subst k
    simp at hk
  have hkone : k = 1 := by
    by_contra hkne
    have hktwo : 2 ≤ k := by omega
    have hlower : 4 * w₁ ≤ p + 1 := by
      calc
        4 * w₁ = (2 * w₁) * 2 := by ring
        _ ≤ (2 * w₁) * k := Nat.mul_le_mul_left _ hktwo
        _ = p + 1 := hk.symm
    have hpLower : 4 * w₁ - 1 ≤ p := by omega
    have hsquareLower : (4 * w₁ - 1) ^ 2 ≤ p ^ 2 :=
      Nat.pow_le_pow_left hpLower 2
    have hstrict : 4 * w₁ ^ 2 + 1 < (4 * w₁ - 1) ^ 2 := by
      nlinarith
    exact (Nat.not_lt_of_ge hub) (hstrict.trans_le hsquareLower)
  subst k
  constructor
  · omega
  · rw [hw₂]
    omega

/-- A prime-order subgroup of a `p`-group has order `p`. -/
private theorem ftType5_prime_subgroup_card
    {H X : Subgroup Gamma} {p : ℕ}
    (hp : p.Prime) (hHp : IsPGroup p H)
    (hXH : X ≤ H) (hXprime : (Nat.card X).Prime) :
    Nat.card X = p := by
  letI : Fact p.Prime := ⟨hp⟩
  have hXp : IsPGroup p (X.subgroupOf H) :=
    hHp.to_subgroup (X.subgroupOf H)
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hXp
  have hcardSub : Nat.card (X.subgroupOf H) = Nat.card X :=
    MathlibSupport.natCard_subgroupOf_eq hXH
  have hpowPrime : (p ^ n).Prime := by
    rw [← hn, hcardSub]
    exact hXprime
  have hnOne : n = 1 := hpowPrime.eq_one_of_pow
  calc
    Nat.card X = Nat.card (X.subgroupOf H) := hcardSub.symm
    _ = p ^ n := hn
    _ = p := by rw [hnOne, pow_one]

/-- The extraspecial/index package extracted from the third type-V branch. -/
private theorem ftType5_prime_cube_index
    {H : Type} [Group H] [Fintype H]
    {p : ℕ} (hp : p.Prime)
    (hHp : IsPGroup p H)
    (hHnonabelian : ¬ IsMulCommutative H)
    (hcoreCard : Nat.card (pCore p H) = p ^ 3) :
    Nat.card H = p ^ 3 ∧
      Nat.card (_root_.commutator H) = p ∧
      (_root_.commutator H).index = p ^ 2 := by
  letI : Fact p.Prime := ⟨hp⟩
  have hpCoreTop : pCore p H = ⊤ := pCore_eq_top_of_isPGroup hHp
  have hHcard : Nat.card H = p ^ 3 := by
    simpa only [hpCoreTop, Subgroup.card_top] using hcoreCard
  have hExtra : IsExtraspecial H :=
    isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
      hHp hHcard hHnonabelian
  have hDcard : Nat.card (_root_.commutator H) = p := by
    rw [hExtra.toIsSpecial.commutator_eq_center]
    exact hExtra.center_card_eq hHp
  have hDindex : (_root_.commutator H).index = p ^ 2 := by
    apply Nat.mul_right_cancel hp.pos
    calc
      (_root_.commutator H).index * p =
          (_root_.commutator H).index *
            Nat.card (_root_.commutator H) := by rw [hDcard]
      _ = Nat.card H := (_root_.commutator H).index_mul_card
      _ = p ^ 3 := hHcard
      _ = p ^ 2 * p := by ring
  exact ⟨hHcard, hDcard, hDindex⟩

/-- Transport a displayed Frobenius decomposition when only the quotient
denominator has been replaced by an equal normal subgroup. -/
private theorem ftType5_frobenius_quotient_congr
    {L : Type} [Group L] [Fintype L]
    (K R D E : Subgroup L) [D.Normal] [E.Normal]
    (hDE : D = E)
    (hfrob : IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk' D))
      (R.map (QuotientGroup.mk' D))) :
    ∃ S : Subgroup (L ⧸ E),
      IsFrobeniusDecomposition
        (K.map (QuotientGroup.mk' E)) S := by
  subst E
  exact ⟨R.map (QuotientGroup.mk' D), hfrob⟩

/-- In type V the prime-TI kernel is the Fitting core, hence nilpotent;
the standard type-P derived quotient supplies the Frobenius quotient in
Peterfalvi's exceptional-chief argument. -/
private theorem ftType5_odd_frobenius_bot
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hFcoreDerived : Fitting_core M = derivedWithin M) :
    odd_Frobenius_quotient (ftType345DerivedInM M)
      (⊥ : Subgroup (ftType345DerivedInM M)) := by
  classical
  let K : Subgroup M := ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  have hderM : derivedWithin M ≤ M :=
    TypeSpecInternal.derivedWithin_le16_final M
  let eK : K ≃* derivedWithin M :=
    Subgroup.subgroupOfEquivOfLe hderM
  have hderNil : Group.IsNilpotent (derivedWithin M) :=
    (Group.isNilpotent_congr
      (MulEquiv.subgroupCongr hFcoreDerived)).mp (Fcore_nil M)
  have hKNil : Group.IsNilpotent K :=
    (Group.isNilpotent_congr eK).mpr hderNil
  letI : Group.IsNilpotent K := hKNil
  have hquotNil : Group.IsNilpotent (K ⧸ (⊥ : Subgroup K)) :=
    Group.nilpotent_of_surjective
      (QuotientGroup.mk' (⊥ : Subgroup K))
      (QuotientGroup.mk'_surjective (⊥ : Subgroup K))
  have hD : (secondDerivedWithin M).subgroupOf M =
      (_root_.commutator K).map K.subtype := by
    change (derivedWithin (derivedWithin M)).subgroupOf M =
      (_root_.commutator ((derivedWithin M).subgroupOf M)).map
        ((derivedWithin M).subgroupOf M).subtype
    rw [show derivedWithin (derivedWithin M) =
        ⁅derivedWithin M, derivedWithin M⁆ by
      exact (derivedWithin M).map_subtype_commutator]
    rw [subgroupOf_commutator_eq hderM hderM]
    exact ((derivedWithin M).subgroupOf M).map_subtype_commutator.symm
  have hfrob := ftType345_derived_quotient_frobenius MtypeP
  refine ⟨mFT_odd M, hquotNil, ?_⟩
  change ∃ E : Subgroup
      (M ⧸ ((_root_.commutator K ⊔ (⊥ : Subgroup K)).map K.subtype)),
    IsFrobeniusDecomposition
      (K.map (QuotientGroup.mk'
        ((_root_.commutator K ⊔ (⊥ : Subgroup K)).map K.subtype))) E
  have hdenom : (secondDerivedWithin M).subgroupOf M =
      (_root_.commutator K ⊔ (⊥ : Subgroup K)).map K.subtype := by
    simpa only [sup_bot_eq] using hD
  exact ftType5_frobenius_quotient_congr K (W₁.subgroupOf M)
    ((secondDerivedWithin M).subgroupOf M)
    ((_root_.commutator K ⊔ (⊥ : Subgroup K)).map K.subtype)
    hdenom hfrob

private theorem ftType5_normalizedTI_coherent
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hUbot : U = ⊥)
    (htype5 : FTtype M = 5)
    (hTI : IsNormalizedTI
      (subgroupNonidentity (Fitting_core M)) ⊤ M) :
    coherent
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau hmaxM) := by
  classical
  have hgt : 2 < FTtype M := by omega
  have hFcoreDerived : Fitting_core M = derivedWithin M :=
    (TypeSpecInternal.semidirect_right_eq_bot_iff_left_eq_ambient16
      MtypeP.2.1.2.2.2).1 hUbot
  have hTIder : IsNormalizedTI
      (subgroupNonidentity (derivedWithin M)) ⊤ M := by
    simpa only [hFcoreDerived] using hTI
  have hcore : FTcore M = derivedWithin M :=
    FTcore_type_gt2 M hgt
  have hsupp : FTsupport M =
      subgroupNonidentity (derivedWithin M) :=
    (FTsupp_eq1 hmaxM hgt).trans (FTsupp1_type_gt2 M hgt)
  have hpW₂ : (Nat.card W₂).Prime :=
    FTtype345_core_prime hmaxM MtypeP (by omega)
  have hW₂comm : W₂ ≤ ambientCommutator (derivedWithin M) := by
    simpa only [ambientCommutator, secondDerivedWithin, derivedWithin] using
      MtypeP.2.2.2.1.2.2.2.1
  let pd := ftType345PrimeDade hmaxM MtypeP
  have hpd : PrimeDadeHypothesis ⊤ M (derivedWithin M)
      (derivedWithin M) (subgroupNonidentity (derivedWithin M))
      (FTsupport0 M) W W₁ W₂ defW := by
    simpa only [hcore, hsupp] using pd
  have hstruct : SibleyStructuralAlternative ⊤ M
      (derivedWithin M) W₁ := by
    exact Or.inr ⟨W₂, hpW₂, hW₂comm,
      FTsupport0 M, W, defW, hpd⟩
  obtain ⟨nu, hnu⟩ := Sibley_coherence ⊤ M (derivedWithin M) W₁
    le_top (TypeSpecInternal.derivedWithin_le16_final M)
    MtypeP.1.2.1.1 (mFT_odd M) (by
      exact (Group.isNilpotent_congr
        (MulEquiv.subgroupCongr hFcoreDerived)).mp (Fcore_nil M))
    hTIder hstruct
  refine ⟨nu, hnu.isometry, hnu.mapsToVirtual, ?_⟩
  intro phi hphi hoff
  let K : Subgroup M := (derivedWithin M).subgroupOf M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  have hclosureK : ∀ psi : ClassFunction M ℂ,
      psi ∈ AddSubgroup.closure
          (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) →
        psi ∈ ClassFunction.supportedOn (K : Set M) := by
    intro psi hpsi
    induction hpsi using AddSubgroup.closure_induction with
    | mem psi hpsi =>
        exact seqInd_on K (by
          simpa only [ftType345InducedFamily10, ftType345DerivedInM,
            seqIndD, K, Finset.mem_coe] using hpsi)
    | zero => exact Submodule.zero_mem _
    | add a b _ _ ha hb => exact Submodule.add_mem _ ha hb
    | neg a _ ha => exact Submodule.neg_mem _ ha
  have hphiK : phi ∈ ClassFunction.supportedOn (K : Set M) :=
    hclosureK phi hphi
  have hphiKne : phi ∈
      ClassFunction.supportedOn (subgroupNonidentity K) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxK : x ∈ K
    · have hxOne : x = 1 := by
        by_contra hxOne
        exact hx ⟨hxK, hxOne⟩
      subst x
      exact ClassFunction.eq_zero_of_mem_supportedOn hoff (by
        simp [nonidentitySet])
    · exact ClassFunction.eq_zero_of_mem_supportedOn hphiK hxK
  have hsupp1 : phi ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport1 M} := by
    rw [FTsupp1_type_gt2 M hgt]
    have hset : {x : M |
        (x : Gamma) ∈ subgroupNonidentity (derivedWithin M)} =
        subgroupNonidentity K := by
      ext x
      constructor
      · rintro ⟨hx, hxne⟩
        exact ⟨hx, fun h ↦ hxne (congrArg Subtype.val h)⟩
      · rintro ⟨hx, hxne⟩
        exact ⟨hx, fun h ↦ hxne (Subtype.ext h)⟩
    rw [hset]
    exact hphiKne
  calc
    nu phi = sibleyInduce ⊤ M le_top phi :=
      hnu.agrees phi hphi hoff
    _ = Dade (FT_Dade1_hyp M hmaxM) phi := by
      symm
      simpa only [sibleyInduce, LinearMap.comp_apply] using
        Dade_Ind (FT_Dade1_hyp M hmaxM) (by
          simpa only [FTsupp1_type_gt2 M hgt] using hTIder) phi hsupp1
    _ = ftType345Tau hmaxM phi :=
      FT_Dade1E M hmaxM phi hsupp1

variable {defW : IsInternalDirectProductIn W₁ W₂ W}

private theorem ftType5_primeTI_Ires_degree
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hconstants : FTType345Constants MtypeP)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    Module.finrank ℂ
        ((ftType345PrimeTI MtypeP).primeTI_Ires
          (ftType345IsoM MtypeP) j).representation =
      FTtype345_TIirr_degree MtypeP := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let theta := pti.primeTI_Ires isoM j
  apply Nat.cast_injective (R := ℂ)
  have hres := congrArg
    (fun f : ClassFunction (ftType345DerivedInM M) ℂ ↦ f 1)
    (pti.cfRes_prTIirr isoM
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j)
  calc
    (Module.finrank ℂ theta.representation : ℂ) = theta 1 := by
      rw [IrreducibleCharacter.apply_one_eq_finrank]
    _ = ftType345Mu2 MtypeP
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j 1 := by
      simpa only [theta, pti, isoM, ftType345DerivedInM,
        ClassFunction.restrict_apply, Subgroup.coe_one] using hres.symm
    _ = (FTtype345_TIirr_degree MtypeP : ℂ) :=
      hconstants.degree_constant _ _ hj

private theorem ftType5_degree_one_of_commutator_le_kernel
    {A : Type} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ)
    (hder : _root_.commutator A ≤
      ClassFunction.translationKernel (chi : ClassFunction A ℂ)) :
    Module.finrank ℂ chi.representation = 1 := by
  let rho := chi.representation.ρ
  have hder' : _root_.commutator A ≤ rho.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter chi]
    exact hder
  let Q := A ⧸ rho.ker
  let sigmaQ : Representation ℂ Q chi.representation :=
    quotientKerRepresentation rho
  let q : A →* Q := QuotientGroup.mk' rho.ker
  letI : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hder'
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible (sigmaQ.comp q) := by
    change Representation.IsIrreducible rho
    infer_instance
  letI : Representation.IsIrreducible sigmaQ :=
    representation_isIrreducible_of_comp sigmaQ q
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    sigmaQ

private theorem ftType5_degree_eq_prime
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hconstants : FTType345Constants MtypeP)
    {p : ℕ} (hp : p.Prime)
    (hHp : IsPGroup p (derivedWithin M))
    (hHnonabelian : ¬ IsMulCommutative (derivedWithin M))
    (hHcard : Nat.card (derivedWithin M) = p ^ 3)
    (hW₂card : Nat.card W₂ = p) :
    let K : Subgroup M := ftType345DerivedInM M
    let D : Subgroup K := _root_.commutator K
    let T : Finset (IrreducibleCharacter W₂ ℂ) :=
      Finset.univ.erase IrreducibleCharacter.trivial
    FTtype345_TIirr_degree MtypeP = p ∧
      Iirr_kerD (k := ℂ) (⊤ : Subgroup K) ⊥ =
        Iirr_kerD (k := ℂ) (⊤ : Subgroup K) D ∪
          T.image ((ftType345PrimeTI MtypeP).primeTI_Ires
            (ftType345IsoM MtypeP)) := by
  classical
  dsimp only
  let K : Subgroup M := ftType345DerivedInM M
  let D : Subgroup K := _root_.commutator K
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let d := FTtype345_TIirr_degree MtypeP
  let T : Finset (IrreducibleCharacter W₂ ℂ) :=
    Finset.univ.erase IrreducibleCharacter.trivial
  let A : Finset (IrreducibleCharacter K ℂ) :=
    Iirr_ker (k := ℂ) D
  let B : Finset (IrreducibleCharacter K ℂ) :=
    T.image (pti.primeTI_Ires isoM)
  let Omega : Finset (IrreducibleCharacter K ℂ) :=
    Iirr_ker (k := ℂ) ⊥
  let degreeSq : IrreducibleCharacter K ℂ → ℕ := fun theta ↦
    Module.finrank ℂ theta.representation ^ 2

  let hKM : derivedWithin M ≤ M :=
    TypeSpecInternal.derivedWithin_le16_final M
  let eK : K ≃* derivedWithin M :=
    Subgroup.subgroupOfEquivOfLe hKM
  have hKp : IsPGroup p K := hHp.of_equiv eK.symm
  have hKcard : Nat.card K = p ^ 3 := by
    exact (Nat.card_congr eK.toEquiv).trans hHcard
  have hKnonabelian : ¬ IsMulCommutative K := by
    intro hKcomm
    apply hHnonabelian
    apply isMulCommutative_iff.mpr
    intro x y
    have hxy := isMulCommutative_iff.mp hKcomm (eK.symm x) (eK.symm y)
    simpa only [map_mul, eK.apply_symm_apply] using congrArg eK hxy
  letI : Fact p.Prime := ⟨hp⟩
  have hExtra : IsExtraspecial K :=
    isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
      hKp hKcard hKnonabelian
  have hDcard : Nat.card D = p := by
    change Nat.card (_root_.commutator K) = p
    rw [hExtra.toIsSpecial.commutator_eq_center]
    exact hExtra.center_card_eq hKp
  have hDindex : D.index = p ^ 2 := by
    apply Nat.mul_right_cancel hp.pos
    calc
      D.index * p = D.index * Nat.card D := by rw [hDcard]
      _ = Nat.card K := D.index_mul_card
      _ = p ^ 3 := hKcard
      _ = p ^ 2 * p := by ring

  have hTcard : T.card = p - 1 := by
    have hcardIrr : Fintype.card (IrreducibleCharacter W₂ ℂ) =
        Nat.card W₂ := by
      letI : IsCyclic W₂ := pti.fixed_cyclic
      exact IrreducibleCharacter.card_eq_natCard_of_isCyclic
    dsimp [T]
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      hcardIrr, hW₂card]
  have hselectedDegree (j : IrreducibleCharacter W₂ ℂ) (hj : j ∈ T) :
      Module.finrank ℂ (pti.primeTI_Ires isoM j).representation = d := by
    apply ftType5_primeTI_Ires_degree MtypeP hconstants j
    exact Finset.ne_of_mem_erase hj
  have hsumB : ∑ theta ∈ B, degreeSq theta = (p - 1) * d ^ 2 := by
    rw [show B = T.image (pti.primeTI_Ires isoM) from rfl,
      Finset.sum_image
        (Set.injOn_of_injective (pti.prTIres_inj isoM))]
    calc
      ∑ j ∈ T, degreeSq (pti.primeTI_Ires isoM j) =
          ∑ _j ∈ T, d ^ 2 := by
        apply Finset.sum_congr rfl
        intro j hj
        change Module.finrank ℂ
            (pti.primeTI_Ires isoM j).representation ^ 2 = d ^ 2
        rw [hselectedDegree j hj]
      _ = T.card * d ^ 2 := by
        simp
      _ = (p - 1) * d ^ 2 := by rw [hTcard]
  have hABdisjoint : Disjoint A B := by
    rw [Finset.disjoint_left]
    intro theta hthetaA hthetaB
    obtain ⟨j, hjT, rfl⟩ := Finset.mem_image.mp hthetaB
    have hlinear := ftType5_degree_one_of_commutator_le_kernel
      (pti.primeTI_Ires isoM j) (mem_Iirr_ker.mp hthetaA)
    have hdegree := hselectedDegree j hjT
    have hdgt : 1 < d := hconstants.degree_gt_one
    exact (by
      omega)
  have hABsub : A ∪ B ⊆ Omega := by
    intro theta htheta
    rw [Finset.mem_union] at htheta
    exact mem_Iirr_ker.mpr bot_le
  have hsumA : ∑ theta ∈ A, degreeSq theta = p ^ 2 := by
    apply Nat.cast_injective (R := ℂ)
    simpa only [A, degreeSq, Nat.cast_sum, Nat.cast_pow,
      IrreducibleCharacter.apply_one_eq_finrank, Nat.cast_ofNat,
      hDindex] using (sum_Iirr_ker_square (k := ℂ) D)
  have hsumOmega : ∑ theta ∈ Omega, degreeSq theta = p ^ 3 := by
    apply Nat.cast_injective (R := ℂ)
    simpa only [Omega, degreeSq, Nat.cast_sum, Nat.cast_pow,
      IrreducibleCharacter.apply_one_eq_finrank, Subgroup.index_bot,
      hKcard] using
        (sum_Iirr_ker_square (k := ℂ) (⊥ : Subgroup K))
  have hbound : p ^ 2 + (p - 1) * d ^ 2 ≤ p ^ 3 := by
    have hle := Finset.sum_le_sum_of_subset (f := degreeSq) hABsub
    rw [Finset.sum_union hABdisjoint, hsumA, hsumB, hsumOmega] at hle
    exact hle
  have hdle : d ≤ p := by
    have hpPos : 0 < p := hp.pos
    have hpTwo : 1 < p := hp.one_lt
    have hidentity : p ^ 3 = p ^ 2 + (p - 1) * p ^ 2 := by
      calc
        p ^ 3 = p * p ^ 2 := by ring
        _ = (1 + (p - 1)) * p ^ 2 := by
          nth_rewrite 1 [show p = 1 + (p - 1) by omega]
          rfl
        _ = p ^ 2 + (p - 1) * p ^ 2 := by ring
    have hmul : (p - 1) * d ^ 2 ≤ (p - 1) * p ^ 2 := by
      rw [hidentity] at hbound
      exact Nat.le_of_add_le_add_left hbound
    have hsquare : d ^ 2 ≤ p ^ 2 :=
      Nat.le_of_mul_le_mul_left hmul (by omega)
    exact (Nat.pow_le_pow_iff_left (by omega : 2 ≠ 0)).mp hsquare
  have hdDvd : d ∣ p ^ 3 := by
    have hdegDvd :=
      (pti.primeTI_Ires isoM (FTtype345_jOne MtypeP)).finrank_representation_dvd_natCard
    rw [ftType5_primeTI_Ires_degree MtypeP hconstants
      (FTtype345_jOne MtypeP) (FTtype345_jOne_ne_trivial MtypeP), hKcard]
      at hdegDvd
    exact hdegDvd
  obtain ⟨a, _ha3, hda⟩ := (Nat.dvd_prime_pow hp).mp hdDvd
  have haPos : 0 < a := by
    by_contra ha
    have ha0 : a = 0 := Nat.eq_zero_of_not_pos ha
    rw [ha0, pow_zero] at hda
    exact (Nat.ne_of_gt hconstants.degree_gt_one) hda
  have hple : p ≤ d := by
    rw [hda]
    simpa only [pow_one] using
      Nat.pow_le_pow_right hp.pos (show 1 ≤ a by omega)
  have hdp : d = p := Nat.le_antisymm hdle hple
  have hsumUnion : ∑ theta ∈ A ∪ B, degreeSq theta = p ^ 3 := by
    have hpPos : 0 < p := hp.pos
    rw [Finset.sum_union hABdisjoint, hsumA, hsumB, hdp]
    calc
      p ^ 2 + (p - 1) * p ^ 2 = p ^ 2 * (1 + (p - 1)) := by ring
      _ = p ^ 2 * p := by rw [show 1 + (p - 1) = p by omega]
      _ = p ^ 3 := by ring
  have hAllEq : Omega = A ∪ B := by
    apply Finset.Subset.antisymm
    · intro theta hthetaOmega
      by_contra hthetaUnion
      have hthetaDiff : theta ∈ Omega \ (A ∪ B) :=
        Finset.mem_sdiff.mpr ⟨hthetaOmega, hthetaUnion⟩
      have hdegreePos : 0 < degreeSq theta := by
        have hfinrankPos : 0 < Module.finrank ℂ theta.representation :=
          Nat.pos_of_dvd_of_pos
            theta.finrank_representation_dvd_natCard Nat.card_pos
        exact pow_pos hfinrankPos _
      have htermLe : degreeSq theta ≤
          ∑ psi ∈ Omega \ (A ∪ B), degreeSq psi :=
        Finset.single_le_sum (fun _ _ ↦ Nat.zero_le _) hthetaDiff
      have hsplit := Finset.sum_sdiff hABsub (f := degreeSq)
      have hdiffZero : ∑ psi ∈ Omega \ (A ∪ B), degreeSq psi = 0 := by
        rw [hsumUnion, hsumOmega] at hsplit
        omega
      rw [hdiffZero] at htermLe
      omega
    · exact hABsub
  have hsourceEq :
      Iirr_kerD (k := ℂ) (⊤ : Subgroup K) ⊥ =
        Iirr_kerD (k := ℂ) (⊤ : Subgroup K) D ∪ B := by
    ext theta
    constructor
    · intro htheta
      have hthetaOmega : theta ∈ Omega :=
        mem_Iirr_ker.mpr (mem_Iirr_kerD.mp htheta).1
      rw [hAllEq, Finset.mem_union] at hthetaOmega
      rw [Finset.mem_union]
      rcases hthetaOmega with hthetaA | hthetaB
      · exact Or.inl (mem_Iirr_kerD.mpr ⟨mem_Iirr_ker.mp hthetaA,
          (mem_Iirr_kerD.mp htheta).2⟩)
      · exact Or.inr hthetaB
    · intro htheta
      rw [Finset.mem_union] at htheta
      rcases htheta with hthetaLinear | hthetaSelected
      · exact mem_Iirr_kerD.mpr
          ⟨bot_le, (mem_Iirr_kerD.mp hthetaLinear).2⟩
      · obtain ⟨j, hjT, rfl⟩ := Finset.mem_image.mp hthetaSelected
        refine mem_Iirr_kerD.mpr ⟨bot_le, ?_⟩
        intro htop
        have hlinear := ftType5_degree_one_of_commutator_le_kernel
          (pti.primeTI_Ires isoM j) (le_top.trans htop)
        have hdegree := hselectedDegree j hjT
        have hpgt : 1 < p := hp.one_lt
        omega
  exact ⟨hdp, hsourceEq⟩

private theorem ftType5_sign_ratio_eq
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hconstants : FTType345Constants MtypeP)
    {p : ℕ}
    (hdegree : FTtype345_TIirr_degree MtypeP = p)
    (hpW₁ : p = 2 * Nat.card W₁ - 1) :
    FTtype345_TIsign MtypeP = -1 ∧
      FTtype345_ratio MtypeP = 2 := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let d := FTtype345_TIirr_degree MtypeP
  let delta := FTtype345_TIsign MtypeP
  let w₁ := Nat.card W₁
  obtain ⟨n, hnRatio⟩ := hconstants.ratio_natural
  have hw₁gt : 2 < w₁ := pti.prime_cycTIhyp.two_lt_card_left
  have hdelta : IsSign delta := by
    simpa only [delta, FTtype345_TIsign, ftType345Sign] using
      pti.primeTISign_isSign isoM (FTtype345_jOne MtypeP)
  have hw₁C : (w₁ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (by omega)
  have hratioMul :
      (d : ℂ) - (delta : ℂ) = (w₁ : ℂ) * (n : ℂ) := by
    calc
      (d : ℂ) - (delta : ℂ) =
          (((d : ℂ) - (delta : ℂ)) / (w₁ : ℂ)) *
            (w₁ : ℂ) := (div_mul_cancel₀ _ hw₁C).symm
      _ = FTtype345_ratio MtypeP * (w₁ : ℂ) := rfl
      _ = (n : ℂ) * (w₁ : ℂ) := by rw [hnRatio]
      _ = (w₁ : ℂ) * (n : ℂ) := mul_comm _ _
  have hrelation : (d : ℤ) =
      delta + (w₁ : ℤ) * (n : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination hratioMul
  rw [show d = p by exact hdegree] at hrelation
  rcases hdelta with hdeltaPos | hdeltaNeg
  · rw [hdeltaPos] at hrelation
    have hnat : p = 1 + w₁ * n := by
      exact_mod_cast hrelation
    by_cases hn0 : n = 0
    · subst n
      simp only [mul_zero, add_zero] at hnat
      omega
    by_cases hn1 : n = 1
    · subst n
      simp only [mul_one] at hnat
      omega
    have hn2 : 2 ≤ n := by omega
    have hmul : 2 * w₁ ≤ w₁ * n := by
      simpa only [Nat.mul_comm] using Nat.mul_le_mul_left w₁ hn2
    omega
  · rw [hdeltaNeg] at hrelation
    have hnat : p + 1 = w₁ * n := by
      have hcast : ((p + 1 : ℕ) : ℤ) = ((w₁ * n : ℕ) : ℤ) := by
        push_cast
        omega
      exact Int.ofNat_inj.mp hcast
    have hpSucc : p + 1 = 2 * w₁ := by omega
    have hmul : w₁ * n = w₁ * 2 := by
      rw [← hnat, hpSucc, Nat.mul_comm]
    have hn : n = 2 :=
      Nat.eq_of_mul_eq_mul_left (by omega : 0 < w₁) hmul
    refine ⟨hdeltaNeg, ?_⟩
    rw [hnRatio, hn]
    norm_num


private theorem ftType5_reduced_mem_full
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP) j ∈
      seqIndD (k := ℂ) (ftType345DerivedInM M)
        (⊤ : Subgroup (ftType345DerivedInM M)) ⊥ := by
  let K : Subgroup M := ftType345DerivedInM M
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  apply (seqIndC1P (k := ℂ) K).mpr
  refine ⟨pti.primeTI_Ires isoM j, ?_, ?_⟩
  · intro htrivial
    apply hj
    apply pti.prTIres_inj isoM
    exact htrivial.trans (pti.prTIres0 isoM).symm
  · exact (pti.cfInd_prTIres isoM j).symm

private theorem ftType5_family_partition
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hconstants : FTType345Constants MtypeP)
    {p : ℕ} (hp : p.Prime)
    (hHp : IsPGroup p (derivedWithin M))
    (hHnonabelian : ¬ IsMulCommutative (derivedWithin M))
    (hHcard : Nat.card (derivedWithin M) = p ^ 3)
    (hW₂card : Nat.card W₂ = p)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (hj₀ : j₀ ≠ IrreducibleCharacter.trivial) :
    let K : Subgroup M := ftType345DerivedInM M
    let D : Subgroup K := _root_.commutator K
    let full : Set (ClassFunction M ℂ) :=
      ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥)
    let Sirr : Set (ClassFunction M ℂ) :=
      ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) D)
    let Sred : Set (ClassFunction M ℂ) :=
      (ftType345PrimeTI MtypeP).uniform_prTIred_seq
        (ftType345IsoM MtypeP) j₀
    cfConjC_subset Sirr full ∧
      cfConjC_subset Sred full ∧
      (∀ phi ∈ Sirr,
        IsIrreducibleCharacter M ℂ phi ∧ phi 1 = (Nat.card W₁ : ℂ)) ∧
      full = Sred ∪ Sirr ∧
      Sirr ⊆ Sredᶜ := by
  classical
  dsimp only
  let K : Subgroup M := ftType345DerivedInM M
  let D : Subgroup K := _root_.commutator K
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let full : Set (ClassFunction M ℂ) :=
    ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥)
  let Sirr : Set (ClassFunction M ℂ) :=
    ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) D)
  let Sred : Set (ClassFunction M ℂ) :=
    pti.uniform_prTIred_seq isoM j₀
  let T : Finset (IrreducibleCharacter W₂ ℂ) :=
    Finset.univ.erase IrreducibleCharacter.trivial
  obtain ⟨hdegree, hsource⟩ := ftType5_degree_eq_prime MtypeP hconstants
    hp hHp hHnonabelian hHcard hW₂card
  have hindex : K.index = Nat.card W₁ := by
    have houter : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := MtypeP.1.2.2.2
    calc
      K.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq houter.2.1
  have hreducedDegree (j : IrreducibleCharacter W₂ ℂ)
      (hj : j ≠ IrreducibleCharacter.trivial) :
      pti.primeTIRed isoM j 1 = pti.primeTIRed isoM j₀ 1 := by
    rw [pti.prTIred_1 isoM j, pti.prTIred_1 isoM j₀,
      hconstants.degree_constant
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j hj,
      hconstants.degree_constant
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j₀ hj₀]
  have hSirrSub : Sirr ⊆ full := by
    intro phi hphi
    exact seqInd_sub (k := ℂ) K (⊤ : Subgroup K) D hphi
  have hSirrClosed : cfConjC_closed Sirr := by
    intro phi hphi
    exact seqInd_inverse_mem (k := ℂ) K (⊤ : Subgroup K) D hphi
  have hSirrFamily : cfConjC_subset Sirr full :=
    ⟨hSirrSub, hSirrClosed⟩
  have hSredSub : Sred ⊆ full := by
    rintro phi ⟨j, ⟨hj, _hdegree⟩, rfl⟩
    exact ftType5_reduced_mem_full MtypeP j hj
  have hSredClosed : cfConjC_closed Sred := by
    rintro phi ⟨j, ⟨hj, hjDegree⟩, rfl⟩
    rw [pti.prTIred_aut isoM j]
    refine ⟨IrreducibleCharacter.dual j, ⟨?_, ?_⟩, rfl⟩
    · intro hdualTrivial
      apply hj
      calc
        j = IrreducibleCharacter.dual (IrreducibleCharacter.dual j) :=
          (IrreducibleCharacter.dual_dual j).symm
        _ = IrreducibleCharacter.dual
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) := by
          rw [hdualTrivial]
        _ = IrreducibleCharacter.trivial :=
          IrreducibleCharacter.dual_trivial
    · have hinverse := congrArg
          (fun f : ClassFunction M ℂ ↦ f 1) (pti.prTIred_aut isoM j)
      calc
        pti.primeTIRed isoM (IrreducibleCharacter.dual j) 1 =
            ClassFunction.inverseLinear (pti.primeTIRed isoM j) 1 :=
          hinverse.symm
        _ = pti.primeTIRed isoM j 1 := by simp
        _ = pti.primeTIRed isoM j₀ 1 := hjDegree
  have hSredFamily : cfConjC_subset Sred full :=
    ⟨hSredSub, hSredClosed⟩
  have hSirrIrrDegree (phi : ClassFunction M ℂ) (hphi : phi ∈ Sirr) :
      IsIrreducibleCharacter M ℂ phi ∧ phi 1 = (Nat.card W₁ : ℂ) := by
    obtain ⟨theta, htheta, hphiEq⟩ := seqIndP.mp hphi
    have hthetaNe : theta ≠ IrreducibleCharacter.trivial := by
      apply (mem_Iirr_ker1 theta).mp
      exact mem_Iirr_kerD.mpr ⟨bot_le, (mem_Iirr_kerD.mp htheta).2⟩
    have hthetaLinear : Module.finrank ℂ theta.representation = 1 :=
      ftType5_degree_one_of_commutator_le_kernel theta
        (mem_Iirr_kerD.mp htheta).1
    rcases pti.prTIres_irr_cases isoM theta with hselected | hinduced
    · obtain ⟨j, hj⟩ := hselected
      have hjNontrivial : j ≠ IrreducibleCharacter.trivial := by
        intro hjTrivial
        subst j
        apply hthetaNe
        rw [hj, pti.prTIres0 isoM]
      have hjDegree := ftType5_primeTI_Ires_degree MtypeP hconstants j
        hjNontrivial
      rw [hj] at hthetaLinear
      rw [hjDegree, hdegree] at hthetaLinear
      exact (hp.one_lt.ne hthetaLinear.symm).elim
    · refine ⟨hphiEq.symm ▸ hinduced.1, ?_⟩
      calc
        phi 1 = ClassFunction.induce K (theta : ClassFunction K ℂ) 1 :=
          congrArg (fun f : ClassFunction M ℂ ↦ f 1) hphiEq
        _ = (K.index : ℂ) * (theta : ClassFunction K ℂ) 1 := by
          rw [ClassFunction.induce_one]
        _ = (K.index : ℂ) := by
          rw [IrreducibleCharacter.apply_one_eq_finrank, hthetaLinear]
          norm_num
        _ = (Nat.card W₁ : ℂ) := by rw [hindex]
  have hcover : full = Sred ∪ Sirr := by
    apply Set.Subset.antisymm
    · intro phi hphi
      obtain ⟨theta, hthetaNe, hphiEq⟩ := (seqIndC1P (k := ℂ) K).mp hphi
      have hthetaSource : theta ∈ Iirr_kerD (k := ℂ) (⊤ : Subgroup K) ⊥ :=
        (mem_Iirr_ker1 theta).mpr hthetaNe
      rw [hsource, Finset.mem_union] at hthetaSource
      rcases hthetaSource with hthetaLinear | hthetaSelected
      · exact Or.inr (seqIndP.mpr ⟨theta, hthetaLinear, hphiEq⟩)
      · obtain ⟨j, hjT, hthetaEq⟩ := Finset.mem_image.mp hthetaSelected
        have hj : j ≠ IrreducibleCharacter.trivial :=
          Finset.ne_of_mem_erase hjT
        apply Or.inl
        rw [hphiEq, ← hthetaEq, pti.cfInd_prTIres isoM j]
        exact ⟨j, ⟨hj, hreducedDegree j hj⟩, rfl⟩
    · intro phi hphi
      rcases hphi with hphiRed | hphiIrr
      · exact hSredSub hphiRed
      · exact hSirrSub hphiIrr
  have hdisjoint : Sirr ⊆ Sredᶜ := by
    intro phi hphiIrr hphiRed
    obtain ⟨j, _hj, hphiEq⟩ := hphiRed
    have hirr := (hSirrIrrDegree phi hphiIrr).1
    rw [← hphiEq] at hirr
    exact pti.prTIred_not_irr isoM j hirr
  exact ⟨hSirrFamily, hSredFamily, hSirrIrrDegree,
    hcover, hdisjoint⟩

private theorem ftType5_reference_mem_Sirr
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hconstants : FTType345Constants MtypeP)
    {p : ℕ} (hp : p.Prime)
    (hHp : IsPGroup p (derivedWithin M))
    (hHnonabelian : ¬ IsMulCommutative (derivedWithin M))
    (hHcard : Nat.card (derivedWithin M) = p ^ 3)
    (hW₂card : Nat.card W₂ = p)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (hj₀ : j₀ ≠ IrreducibleCharacter.trivial)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta) :
    zeta ∈ seqIndD (k := ℂ) (ftType345DerivedInM M)
      (⊤ : Subgroup (ftType345DerivedInM M))
      (_root_.commutator (ftType345DerivedInM M)) := by
  let K : Subgroup M := ftType345DerivedInM M
  let D : Subgroup K := _root_.commutator K
  let full : Set (ClassFunction M ℂ) :=
    ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥)
  let Sirr : Set (ClassFunction M ℂ) :=
    ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) D)
  let Sred : Set (ClassFunction M ℂ) :=
    (ftType345PrimeTI MtypeP).uniform_prTIred_seq
      (ftType345IsoM MtypeP) j₀
  obtain ⟨_hSirr, _hSred, _hdegree, hcover, _hdisjoint⟩ :=
    ftType5_family_partition MtypeP hconstants hp hHp hHnonabelian
      hHcard hW₂card j₀ hj₀
  have hzetaUnion : zeta ∈
      (ftType345PrimeTI MtypeP).uniform_prTIred_seq
          (ftType345IsoM MtypeP) j₀ ∪
        (↑(seqIndD (k := ℂ) (ftType345DerivedInM M)
          (⊤ : Subgroup (ftType345DerivedInM M))
          (_root_.commutator (ftType345DerivedInM M))) :
            Set (ClassFunction M ℂ)) := by
    rw [← hcover]
    exact hzeta.mem_calS
  rcases hzetaUnion with hzetaRed | hzetaIrr
  · obtain ⟨j, _hj, hjEq⟩ := hzetaRed
    have hzetaIrr : IsIrreducibleCharacter M ℂ
        ((ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j) := by
      rw [hjEq]
      exact hzeta.irreducible
    exact ((ftType345PrimeTI MtypeP).prTIred_not_irr
      (ftType345IsoM MtypeP) j hzetaIrr).elim
  · exact hzetaIrr

private theorem ftType5_Sirr_card
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hconstants : FTType345Constants MtypeP)
    {p : ℕ} (hp : p.Prime)
    (hHp : IsPGroup p (derivedWithin M))
    (hHnonabelian : ¬ IsMulCommutative (derivedWithin M))
    (hHcard : Nat.card (derivedWithin M) = p ^ 3)
    (hW₂card : Nat.card W₂ = p)
    (hpW₁ : p = 2 * Nat.card W₁ - 1) :
    (seqIndD (k := ℂ) (ftType345DerivedInM M)
      (⊤ : Subgroup (ftType345DerivedInM M))
      (_root_.commutator (ftType345DerivedInM M))).card =
        4 * (Nat.card W₁ - 1) := by
  classical
  let K : Subgroup M := ftType345DerivedInM M
  let D : Subgroup K := _root_.commutator K
  let SirrFin : Finset (ClassFunction M ℂ) :=
    seqIndD (k := ℂ) K (⊤ : Subgroup K) D
  let Sirr : Set (ClassFunction M ℂ) := ↑SirrFin
  let j₀ : IrreducibleCharacter W₂ ℂ := FTtype345_jOne MtypeP
  have hj₀ : j₀ ≠ IrreducibleCharacter.trivial :=
    FTtype345_jOne_ne_trivial MtypeP
  obtain ⟨_hSirr, _hSred, hSirrData, _hcover, _hdisjoint⟩ :=
    ftType5_family_partition MtypeP hconstants hp hHp hHnonabelian
      hHcard hW₂card j₀ hj₀
  have hindex : K.index = Nat.card W₁ := by
    have houter : IsInternalSemidirectProductIn
        (derivedWithin M) W₁ M := MtypeP.1.2.2.2
    calc
      K.index = Nat.card (W₁.subgroupOf M) :=
        houter.2.2.2.symm.index_eq_card
      _ = Nat.card W₁ :=
        MathlibSupport.natCard_subgroupOf_eq houter.2.1
  let hKM : derivedWithin M ≤ M :=
    TypeSpecInternal.derivedWithin_le16_final M
  let eK : K ≃* derivedWithin M :=
    Subgroup.subgroupOfEquivOfLe hKM
  have hKp : IsPGroup p K := hHp.of_equiv eK.symm
  have hKcard : Nat.card K = p ^ 3 :=
    (Nat.card_congr eK.toEquiv).trans hHcard
  have hKnonabelian : ¬ IsMulCommutative K := by
    intro hKcomm
    apply hHnonabelian
    apply isMulCommutative_iff.mpr
    intro x y
    have hxy := isMulCommutative_iff.mp hKcomm (eK.symm x) (eK.symm y)
    simpa only [map_mul, eK.apply_symm_apply] using congrArg eK hxy
  letI : Fact p.Prime := ⟨hp⟩
  have hExtra : IsExtraspecial K :=
    isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
      hKp hKcard hKnonabelian
  have hDcard : Nat.card D = p := by
    change Nat.card (_root_.commutator K) = p
    rw [hExtra.toIsSpecial.commutator_eq_center]
    exact hExtra.center_card_eq hKp
  have hDindex : D.index = p ^ 2 := by
    apply Nat.mul_right_cancel hp.pos
    calc
      D.index * p = D.index * Nat.card D := by rw [hDcard]
      _ = Nat.card K := D.index_mul_card
      _ = p ^ 3 := hKcard
      _ = p ^ 2 * p := by ring
  letI : Invertible (Nat.card M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hsumLeft :
      (∑ phi ∈ SirrFin,
          phi 1 ^ 2 / characterPairing phi phi) =
        (SirrFin.card : ℂ) * (Nat.card W₁ : ℂ) ^ 2 := by
    calc
      (∑ phi ∈ SirrFin,
          phi 1 ^ 2 / characterPairing phi phi) =
          ∑ _phi ∈ SirrFin, (Nat.card W₁ : ℂ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro phi hphi
        have hdata := hSirrData phi hphi
        have hpair : characterPairing phi phi = 1 :=
          IrreducibleCharacter.characterPairing_self ⟨phi, hdata.1⟩
        rw [hdata.2, hpair]
        simp
      _ = (SirrFin.card : ℂ) * (Nat.card W₁ : ℂ) ^ 2 := by
        simp
  have hsum := sum_seqIndD_square (k := ℂ) K
    (⊤ : Subgroup K) D le_top
  have hcomplex :
      (SirrFin.card : ℂ) * (Nat.card W₁ : ℂ) ^ 2 =
        (Nat.card W₁ : ℂ) * ((p : ℂ) ^ 2 - 1) := by
    calc
      (SirrFin.card : ℂ) * (Nat.card W₁ : ℂ) ^ 2 =
          ∑ phi ∈ SirrFin,
            phi 1 ^ 2 / characterPairing phi phi := hsumLeft.symm
      _ = (K.index : ℂ) *
          (((⊤ : Subgroup K).index : ℂ) *
            (((D.relIndex (⊤ : Subgroup K) : ℕ) : ℂ) - 1)) := hsum
      _ = (Nat.card W₁ : ℂ) * ((p : ℂ) ^ 2 - 1) := by
        rw [hindex, Subgroup.index_top, D.relIndex_top_right, hDindex]
        norm_num
  have hpSq : 1 ≤ p ^ 2 := by
    nlinarith [hp.one_lt]
  have hnatProduct :
      SirrFin.card * (Nat.card W₁) ^ 2 =
        Nat.card W₁ * (p ^ 2 - 1) := by
    apply Nat.cast_injective (R := ℂ)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul,
      Nat.cast_sub hpSq, Nat.cast_pow, Nat.cast_one]
    exact hcomplex
  have hw₁Pos : 0 < Nat.card W₁ := Nat.card_pos
  have hcancel : SirrFin.card * Nat.card W₁ = p ^ 2 - 1 := by
    apply Nat.eq_of_mul_eq_mul_left hw₁Pos
    calc
      Nat.card W₁ * (SirrFin.card * Nat.card W₁) =
          SirrFin.card * (Nat.card W₁) ^ 2 := by ring
      _ = Nat.card W₁ * (p ^ 2 - 1) := hnatProduct
  have hw₁gt : 2 < Nat.card W₁ :=
    (ftType345PrimeTI MtypeP).prime_cycTIhyp.two_lt_card_left
  have htargetProduct :
      SirrFin.card * Nat.card W₁ =
        (4 * (Nat.card W₁ - 1)) * Nat.card W₁ := by
    rw [hcancel, hpW₁]
    let a := Nat.card W₁ - 1
    change (2 * Nat.card W₁ - 1) ^ 2 - 1 =
      (4 * a) * Nat.card W₁
    have hw₁Eq : Nat.card W₁ = a + 1 := by
      dsimp only [a]
      omega
    have hbase : 2 * Nat.card W₁ - 1 =
        2 * a + 1 := by omega
    rw [hbase]
    have hsqPos : 1 ≤ (2 * a + 1) ^ 2 := by
      exact one_le_pow₀ (by omega : 1 ≤ 2 * a + 1)
    apply (Nat.sub_eq_iff_eq_add hsqPos).2
    rw [hw₁Eq]
    ring
  exact Nat.eq_of_mul_eq_mul_right hw₁Pos htargetProduct


private theorem type5BridgeGlue_cyclicTIImage_isVirtual
    {G W W₁ W₂ : Subgroup Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    {h : CyclicTIHypothesis G W W₁ W₂ defW}
    (iso : CyclicTIIsometryData (k := ℂ) h)
    (p : IrreducibleCharacter W₁ ℂ × IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (iso.cyclicTIImage p) := by
  let chi : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW p.1 p.2
  let z : VirtualCharacter W ℂ := Finsupp.single chi 1
  exact ⟨iso.virtualMap z, by
    calc
      VirtualCharacter.realize (iso.virtualMap z) =
          iso.linearMap (VirtualCharacter.realize z) :=
        iso.realize_virtualMap z
      _ = iso.cyclicTIImage p := by
        simp [z, chi, CyclicTIIsometryData.cyclicTIImage,
          CyclicTIIsometryData.cyclicTISourceIrreducible]⟩

private theorem type5BridgeGlue_fintype_sum_isVirtual
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

/-- Package Peterfalvi (4.9)'s explicit uniform-column map as the
`coherent_with` witness needed by the Section 5 bridge lemma. -/
private theorem type5BridgeGlue_uniform_prTIred_coherentWith
    {G L K H W W₁ W₂ : Subgroup Gamma}
    {A A₀ : Set Gamma}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (pd : PrimeDadeHypothesis G L K H A A₀ W W₁ W₂ defW)
    (isoL : CyclicTIIsometryData (k := ℂ)
      pd.prDade_prTI.prime_cycTIhyp)
    (isoG : CyclicTIIsometryData (k := ℂ) pd.prDade_cycTI)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (hj₀ : j₀ ≠ IrreducibleCharacter.trivial) :
    let T := pd.prDade_prTI.uniform_prTIred_seq isoL j₀
    ∃ tau₂ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ,
      coherent_with T (nonidentitySet L) (Dade pd.prDade_hyp) tau₂ ∧
      ∀ j, tau₂ (pd.prDade_prTI.primeTIRed isoL j) =
        (pd.prDade_prTI.primeTISign isoL j₀ : ℂ) •
          ∑ i : IrreducibleCharacter W₁ ℂ, isoG.cyclicTIImage (i, j) := by
  classical
  let T := pd.prDade_prTI.uniform_prTIred_seq isoL j₀
  obtain ⟨_, tau₂, htau₂, hisometry, hagrees⟩ :=
    pd.uniform_prTIred_coherent isoL isoG j₀ hj₀
  have hgeneratorVirtual : ∀ phi ∈ T,
      ClassFunction.IsVirtual (tau₂ phi) := by
    rintro phi ⟨j, _hj, rfl⟩
    rw [htau₂]
    have hsum := (type5BridgeGlue_fintype_sum_isVirtual
      (fun i : IrreducibleCharacter W₁ ℂ ↦ isoG.cyclicTIImage (i, j))
      (fun i ↦ type5BridgeGlue_cyclicTIImage_isVirtual isoG (i, j))).zsmul
        (pd.prDade_prTI.primeTISign isoL j₀)
    exact (Int.cast_smul_eq_zsmul ℂ
      (pd.prDade_prTI.primeTISign isoL j₀)
      (∑ i : IrreducibleCharacter W₁ ℂ,
        isoG.cyclicTIImage (i, j))).symm ▸ hsum
  have hmapsToVirtual : ∀ phi ∈ AddSubgroup.closure T,
      ClassFunction.IsVirtual (tau₂ phi) := by
    intro phi hphi
    induction hphi using AddSubgroup.closure_induction with
    | mem phi hphi => exact hgeneratorVirtual phi hphi
    | zero => simpa using ClassFunction.IsVirtual.zero (H := G)
    | add phi psi _ _ hphi hpsi =>
        simpa only [map_add] using hphi.add hpsi
    | neg phi _ hphi =>
        simpa only [map_neg] using hphi.neg
  refine ⟨tau₂, ?_, htau₂⟩
  exact
    { isometry := hisometry
      mapsToVirtual := hmapsToVirtual
      agrees := hagrees }

private theorem type5BridgeGlue_sum_const_smul
    {Q I : Type} [Group Q] [Fintype I]
    (a : ℂ) (f : ClassFunction Q ℂ) :
    ∑ _i : I, a • f =
      ((Fintype.card I : ℂ) * a) • f := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

/-- Sum the type-III--V bridge formulas and eliminate the zero column.  This
is the algebraic core of the last display in Peterfalvi (10.10). -/
private theorem type5BridgeGlue_pairing_sub_left
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingLeft (a - b) c = _
  exact map_sub (characterPairingRight c) a b

private theorem type5BridgeGlue_pairing_sub_right
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingRight (b - c) a = _
  exact map_sub (characterPairingLeft a) b c

private theorem type5BridgeGlue_pairing_sum_right
    {Q I : Type} [Group Q] [Fintype Q] [Fintype I]
    (a : ClassFunction Q ℂ) (f : I → ClassFunction Q ℂ) :
    characterPairing a (∑ i, f i) =
      ∑ i, characterPairing a (f i) := by
  exact map_sum (characterPairingLeft a) f Finset.univ

private theorem type5BridgeGlue_exists_signed_irreducible
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

private theorem type5BridgeGlue_signedIrreducible_eq_of_pairing_one
    {Q : Type} [Group Q] [Fintype Q]
    {f g : ClassFunction Q ℂ}
    {chi psi : IrreducibleCharacter Q ℂ} {epsilon delta : ℤ}
    (hepsilon : IsSign epsilon) (hdelta : IsSign delta)
    (hf : f = (epsilon : ℂ) • (chi : ClassFunction Q ℂ))
    (hg : g = (delta : ℂ) • (psi : ClassFunction Q ℂ))
    (hpair : characterPairing f g = 1) :
    f = g := by
  subst f
  subst g
  rcases hepsilon with rfl | rfl <;>
    rcases hdelta with rfl | rfl <;>
    by_cases hchi : chi = psi <;>
    simp [characterPairing_smul_left, characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_eq_ite, hchi] at hpair ⊢ <;>
    norm_num at hpair


private theorem type5BridgeGlue_balancingIdentity
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (tau₁ : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hDalpha : ∀ i : IrreducibleCharacter W₁ ℂ,
      ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) =
        (FTtype345_TIsign MtypeP : ℂ) •
            (ftType345Eta hmaxM MtypeP i j -
              ftType345Eta hmaxM MtypeP i
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ)) -
          FTtype345_ratio MtypeP • tau₁ zeta)
    (hzero : ftType345Tau hmaxM
        ((ftType345PrimeTI MtypeP).primeTIRed
            (ftType345IsoM MtypeP)
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ) - zeta) =
      (∑ i : IrreducibleCharacter W₁ ℂ,
        ftType345Eta hmaxM MtypeP i
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ ℂ)) - tau₁ zeta) :
    ftType345Tau hmaxM
        ((ftType345PrimeTI MtypeP).primeTIRed
            (ftType345IsoM MtypeP) j -
          (FTtype345_TIirr_degree MtypeP : ℂ) • zeta) =
      (FTtype345_TIsign MtypeP : ℂ) •
          ∑ i : IrreducibleCharacter W₁ ℂ,
            ftType345Eta hmaxM MtypeP i j -
        tau₁ ((FTtype345_TIirr_degree MtypeP : ℂ) • zeta) := by
  classical
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let mu := fun k : IrreducibleCharacter W₂ ℂ ↦
    pti.primeTIRed isoM k
  let eta := fun i : IrreducibleCharacter W₁ ℂ ↦
    fun k : IrreducibleCharacter W₂ ℂ ↦
      ftType345Eta hmaxM MtypeP i k
  letI : IsCyclic W₁ := pti.complement_cyclic
  have hcardI :
      Fintype.card (IrreducibleCharacter W₁ ℂ) = Nat.card W₁ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hratio :
      (Nat.card W₁ : ℂ) * FTtype345_ratio MtypeP =
        (FTtype345_TIirr_degree MtypeP : ℂ) -
          (FTtype345_TIsign MtypeP : ℂ) := by
    rw [FTtype345_ratio]
    field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne']
  have hsumMuJ :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Mu2 MtypeP i j) = mu j :=
    (pti.primeTIRed_eq_sum isoM j).symm
  have hsumMu0 :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Mu2 MtypeP i
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ)) =
        mu IrreducibleCharacter.trivial :=
    (pti.primeTIRed_eq_sum isoM IrreducibleCharacter.trivial).symm
  have hsumSignedMu0 :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          (FTtype345_TIsign MtypeP : ℂ) •
            ftType345Mu2 MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) =
        (FTtype345_TIsign MtypeP : ℂ) •
          mu IrreducibleCharacter.trivial := by
    rw [← Finset.smul_sum, hsumMu0]
  have hsumRatioZeta :
      (∑ _i : IrreducibleCharacter W₁ ℂ,
          FTtype345_ratio MtypeP • zeta) =
        ((FTtype345_TIirr_degree MtypeP : ℂ) -
          (FTtype345_TIsign MtypeP : ℂ)) • zeta := by
    rw [type5BridgeGlue_sum_const_smul
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
            intro i _hi
            exact hDalpha i
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
            rw [type5BridgeGlue_sum_const_smul
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
  rw [hsumTauAlpha, hzero] at hMapped
  have hSolve :
      ftType345Tau hmaxM
          (mu j - (FTtype345_TIirr_degree MtypeP : ℂ) • zeta) =
        ((FTtype345_TIsign MtypeP : ℂ) •
              ((∑ i : IrreducibleCharacter W₁ ℂ, eta i j) -
                ∑ i : IrreducibleCharacter W₁ ℂ,
                  eta i IrreducibleCharacter.trivial) -
            ((FTtype345_TIirr_degree MtypeP : ℂ) -
              (FTtype345_TIsign MtypeP : ℂ)) • tau₁ zeta) +
          (FTtype345_TIsign MtypeP : ℂ) •
            ((∑ i : IrreducibleCharacter W₁ ℂ,
              eta i IrreducibleCharacter.trivial) - tau₁ zeta) :=
    sub_eq_iff_eq_add.mp hMapped.symm
  rw [map_smul]
  rw [hSolve]
  module

/-- Identify the norm-one residual in the zero-column bridge with the image
of the reference character under the induced-family coherence map.  The
arguments `hDalpha` and `hzeroBridge` are exactly the outputs of the two
preceding phases of (10.10.3) and (10.9), respectively. -/
private theorem type5BridgeGlue_identify_zeroResidual
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (Sirr : Set (ClassFunction M ℂ))
    (tauIrr : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hSirrKernel : cfConjC_subset Sirr
      (FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP)))
    (hcohIrr : coherent_with Sirr (nonidentitySet M)
      (ftType345Tau hmaxM) tauIrr)
    (hzetaSirr : zeta ∈ Sirr)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hDalpha : ftType345Tau hmaxM
        (FTtype345_bridge MtypeP zeta
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₁ ℂ) j) =
      (FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₁ ℂ) j -
            ftType345Eta hmaxM MtypeP
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₁ ℂ)
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) -
        FTtype345_ratio MtypeP • tauIrr zeta)
    (hpsiSupport :
      (ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP)
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ ℂ) - zeta ∈
        ClassFunction.supportedOn
          {x : M | (x : Gamma) ∈ FTsupport0 M})
    (chi : ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hzeroBridge : ftType345Tau hmaxM
        ((ftType345PrimeTI MtypeP).primeTIRed
            (ftType345IsoM MtypeP)
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ) - zeta) =
      (∑ i : IrreducibleCharacter W₁ ℂ,
        ftType345Eta hmaxM MtypeP i
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ ℂ)) - chi)
    (hchiVirtual : ClassFunction.IsVirtual chi)
    (hchiNorm : characterPairing chi chi = 1)
    (hchiEta : ∀ i j,
      characterPairing chi (ftType345Eta hmaxM MtypeP i j) = 0)
    (hratioTwo : FTtype345_ratio MtypeP = 2) :
    ftType345Tau hmaxM
        ((ftType345PrimeTI MtypeP).primeTIRed
            (ftType345IsoM MtypeP)
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ) - zeta) =
      (∑ i : IrreducibleCharacter W₁ ℂ,
        ftType345Eta hmaxM MtypeP i
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ ℂ)) - tauIrr zeta := by
  classical
  let pd := ftType345PrimeDade hmaxM MtypeP
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let isoG := ftType345IsoG hmaxM MtypeP
  let i₀ : IrreducibleCharacter W₁ ℂ :=
    IrreducibleCharacter.trivial
  let j₀ : IrreducibleCharacter W₂ ℂ :=
    IrreducibleCharacter.trivial
  let alpha : ClassFunction M ℂ :=
    FTtype345_bridge MtypeP zeta i₀ j
  let psi : ClassFunction M ℂ := pti.primeTIRed isoM j₀ - zeta
  let eta := fun i : IrreducibleCharacter W₁ ℂ ↦
    fun k : IrreducibleCharacter W₂ ℂ ↦
      ftType345Eta hmaxM MtypeP i k

  have hzetaSpan : zeta ∈ AddSubgroup.closure Sirr :=
    AddSubgroup.subset_closure hzetaSirr
  have hzetaNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self
      ⟨zeta, hzeta.irreducible⟩
  have htauZetaVirtual : ClassFunction.IsVirtual (tauIrr zeta) :=
    hcohIrr.mapsToVirtual zeta hzetaSpan
  have htauZetaNorm :
      characterPairing (tauIrr zeta) (tauIrr zeta) = 1 := by
    rw [hcohIrr.isometry zeta hzetaSpan zeta hzetaSpan, hzetaNorm]

  have htauZetaEta (i : IrreducibleCharacter W₁ ℂ)
      (k : IrreducibleCharacter W₂ ℂ) :
      characterPairing (tauIrr zeta) (eta i k) = 0 := by
    have h := coherent_ortho_cycTIiso pd isoM isoG (mFT_odd M)
      hSirrKernel hcohIrr hzetaSirr hzeta.irreducible
      (IrreducibleCharacter.cyclicTICharacter defW i k)
    simpa only [eta, ftType345Eta,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using h

  have hAlphaVirtual : ClassFunction.IsVirtual alpha :=
    vchar_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i₀ j
  have hTauAlphaVirtual :
      ClassFunction.IsVirtual (ftType345Tau hmaxM alpha) :=
    vchar_Dade_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i₀ j hj
  have hzetaVirtual : ClassFunction.IsVirtual zeta :=
    ⟨Finsupp.single ⟨zeta, hzeta.irreducible⟩ 1, by simp⟩
  have hPsiVirtual : ClassFunction.IsVirtual psi :=
    (pti.prTIred_char isoM j₀).isVirtual.sub hzetaVirtual
  have hEtaSumVirtual : ClassFunction.IsVirtual
      (∑ i : IrreducibleCharacter W₁ ℂ, eta i j₀) :=
    type5BridgeGlue_fintype_sum_isVirtual _
      (fun i ↦ type5BridgeGlue_cyclicTIImage_isVirtual isoG (i, j₀))
  have hTauPsiVirtual :
      ClassFunction.IsVirtual (ftType345Tau hmaxM psi) := by
    rw [show ftType345Tau hmaxM psi =
        (∑ i : IrreducibleCharacter W₁ ℂ, eta i j₀) - chi by
      simpa only [psi, eta, pti, isoM, j₀] using hzeroBridge]
    exact hEtaSumVirtual.sub hchiVirtual

  have hAlphaSupport : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport0 M} := by
    simpa only [alpha, ftType345Support0InM] using
      supp_FTtype345_bridge hmaxM MtypeP notMtype2
        zeta hzeta i₀ j hj
  have hPsiSupport : psi ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport0 M} := by
    simpa only [psi, pti, isoM, j₀] using hpsiSupport
  have hPairDade :
      characterPairing (ftType345Tau hmaxM alpha)
          (ftType345Tau hmaxM psi) =
        characterPairing alpha psi := by
    calc
      characterPairing (ftType345Tau hmaxM alpha)
          (ftType345Tau hmaxM psi) =
          starCharacterPairing (ftType345Tau hmaxM alpha)
            (ftType345Tau hmaxM psi) :=
        (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hTauAlphaVirtual hTauPsiVirtual).symm
      _ = starCharacterPairing alpha psi := by
        exact Dade_isometry (FT_Dade0_hyp M hmaxM)
          alpha psi hAlphaSupport hPsiSupport
      _ = characterPairing alpha psi :=
        PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hAlphaVirtual hPsiVirtual

  have hmuJMu0 : characterPairing
      (ftType345Mu2 MtypeP i₀ j) (pti.primeTIRed isoM j₀) = 0 := by
    rw [pti.cfdot_prTIirr_red isoM, if_neg]
    exact hj
  have hmu0Mu0 : characterPairing
      (ftType345Mu2 MtypeP i₀ j₀) (pti.primeTIRed isoM j₀) = 1 := by
    rw [pti.cfdot_prTIirr_red isoM, if_pos rfl]
  have hmuJZeta : characterPairing
      (ftType345Mu2 MtypeP i₀ j) zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i₀ j
  have hmu0Zeta : characterPairing
      (ftType345Mu2 MtypeP i₀ j₀) zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i₀ j₀
  have hzetaMu0 : characterPairing zeta (pti.primeTIRed isoM j₀) = 0 := by
    rw [characterPairing_comm, pti.primeTIRed_eq_sum]
    change characterPairingRight zeta
      (∑ i : IrreducibleCharacter W₁ ℂ,
        ftType345Mu2 MtypeP i j₀) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro i _hi
    exact FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i j₀
  have hPairSource : characterPairing alpha psi =
      -(FTtype345_TIsign MtypeP : ℂ) + FTtype345_ratio MtypeP := by
    simp only [alpha, psi, i₀, j₀, pti, isoM, FTtype345_bridge,
      type5BridgeGlue_pairing_sub_left,
      type5BridgeGlue_pairing_sub_right,
      characterPairing_smul_left, hmuJMu0, hmu0Mu0,
      hmuJZeta, hmu0Zeta, hzetaMu0, hzetaNorm]
    ring

  have hetaJsum : characterPairing (eta i₀ j)
      (∑ i : IrreducibleCharacter W₁ ℂ, eta i j₀) = 0 := by
    rw [type5BridgeGlue_pairing_sum_right]
    apply Finset.sum_eq_zero
    intro i _hi
    rw [isoG.characterPairing_cyclicTIImage]
    rw [if_neg]
    intro hpair
    have hright : j = j₀ := congrArg Prod.snd hpair
    exact hj (by simpa only [j₀] using hright)
  have heta0sum : characterPairing (eta i₀ j₀)
      (∑ i : IrreducibleCharacter W₁ ℂ, eta i j₀) = 1 := by
    rw [type5BridgeGlue_pairing_sum_right]
    classical
    rw [Finset.sum_eq_single i₀]
    · rw [isoG.characterPairing_cyclicTIImage, if_pos rfl]
    · intro i _hi hine
      rw [isoG.characterPairing_cyclicTIImage, if_neg]
      intro hpair
      exact hine (congrArg Prod.fst hpair).symm
    · simp
  have htauZetaSum : characterPairing (tauIrr zeta)
      (∑ i : IrreducibleCharacter W₁ ℂ, eta i j₀) = 0 := by
    rw [type5BridgeGlue_pairing_sum_right]
    exact Finset.sum_eq_zero (fun i _ ↦ htauZetaEta i j₀)
  have hetaJChi : characterPairing (eta i₀ j) chi = 0 := by
    rw [characterPairing_comm]
    exact hchiEta i₀ j
  have heta0Chi : characterPairing (eta i₀ j₀) chi = 0 := by
    rw [characterPairing_comm]
    exact hchiEta i₀ j₀
  have hPairTarget :
      characterPairing (ftType345Tau hmaxM alpha)
          (ftType345Tau hmaxM psi) =
        -(FTtype345_TIsign MtypeP : ℂ) +
          FTtype345_ratio MtypeP * characterPairing (tauIrr zeta) chi := by
    rw [show ftType345Tau hmaxM alpha =
        (FTtype345_TIsign MtypeP : ℂ) •
            (eta i₀ j - eta i₀ j₀) -
          FTtype345_ratio MtypeP • tauIrr zeta by
      simpa only [alpha, eta, i₀, j₀] using hDalpha]
    rw [show ftType345Tau hmaxM psi =
        (∑ i : IrreducibleCharacter W₁ ℂ, eta i j₀) - chi by
      simpa only [psi, eta, pti, isoM, j₀] using hzeroBridge]
    simp only [type5BridgeGlue_pairing_sub_left,
      type5BridgeGlue_pairing_sub_right, characterPairing_smul_left,
      hetaJsum, heta0sum, htauZetaSum, hetaJChi, heta0Chi]
    ring

  rw [hPairTarget, hPairSource] at hPairDade
  rw [hratioTwo] at hPairDade
  have htauZetaChi : characterPairing (tauIrr zeta) chi = 1 := by
    linear_combination hPairDade / 2
  obtain ⟨tauChi, tauSign, htauSign, htauSigned⟩ :=
    type5BridgeGlue_exists_signed_irreducible
      htauZetaVirtual htauZetaNorm
  obtain ⟨resChi, resSign, hresSign, hresSigned⟩ :=
    type5BridgeGlue_exists_signed_irreducible hchiVirtual hchiNorm
  have htauEqChi : tauIrr zeta = chi :=
    type5BridgeGlue_signedIrreducible_eq_of_pairing_one
      htauSign hresSign htauSigned hresSigned htauZetaChi
  simpa only [htauEqChi] using hzeroBridge

/- The coefficient-counting half of (10.10.3).  The preceding Dade
pairing calculation supplies `hpairShift`: every non-reference coefficient
is the reference coefficient plus the ratio, here `2`.  Bessel's bound and
the eight-element lower bound force the shifted coefficient to vanish. -/
private theorem type5BridgeGlue_alphaFormula_of_pairingShift
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (Sirr : Finset (ClassFunction M ℂ))
    (tauIrr : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hSirrKernel : cfConjC_subset
      (↑Sirr : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP)))
    (hcohIrr : coherent_with
      (↑Sirr : Set (ClassFunction M ℂ)) (nonidentitySet M)
      (ftType345Tau hmaxM) tauIrr)
    (hirr : ∀ phi ∈ Sirr, IsIrreducibleCharacter M ℂ phi)
    (hzetaSirr : zeta ∈ Sirr)
    (hcard : 8 ≤ Sirr.card)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hratioTwo : FTtype345_ratio MtypeP = 2)
    (hpairShift : ∀ lam ∈ Sirr, lam ≠ zeta →
      characterPairing
          (ftType345Tau hmaxM
            (FTtype345_bridge MtypeP zeta i j)) (tauIrr lam) =
        characterPairing
            (ftType345Tau hmaxM
              (FTtype345_bridge MtypeP zeta i j)) (tauIrr zeta) + 2) :
    ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) =
      (FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP i j -
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) -
        FTtype345_ratio MtypeP • tauIrr zeta := by
  classical
  let beta : ClassFunction (⊤ : Subgroup Gamma) ℂ :=
    ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)
  let T : Finset (ClassFunction (⊤ : Subgroup Gamma) ℂ) :=
    Sirr.image tauIrr
  have hspan (phi : ClassFunction M ℂ) (hphi : phi ∈ Sirr) :
      phi ∈ AddSubgroup.closure
        (↑Sirr : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hphi
  have hsourceNorm (phi : ClassFunction M ℂ) (hphi : phi ∈ Sirr) :
      characterPairing phi phi = 1 :=
    IrreducibleCharacter.characterPairing_self ⟨phi, hirr phi hphi⟩
  have htauNorm (phi : ClassFunction M ℂ) (hphi : phi ∈ Sirr) :
      characterPairing (tauIrr phi) (tauIrr phi) = 1 := by
    rw [hcohIrr.isometry phi (hspan phi hphi) phi (hspan phi hphi),
      hsourceNorm phi hphi]
  have htauVirtual (phi : ClassFunction M ℂ) (hphi : phi ∈ Sirr) :
      ClassFunction.IsVirtual (tauIrr phi) :=
    hcohIrr.mapsToVirtual phi (hspan phi hphi)
  have htauInj : Set.InjOn tauIrr (↑Sirr : Set (ClassFunction M ℂ)) := by
    intro phi hphi psi hpsi heq
    by_contra hne
    let chi : IrreducibleCharacter M ℂ := ⟨phi, hirr phi hphi⟩
    let eta : IrreducibleCharacter M ℂ := ⟨psi, hirr psi hpsi⟩
    have hchiEta : chi ≠ eta := by
      intro h
      exact hne (congrArg Subtype.val h)
    have hsourceZero : characterPairing phi psi = 0 := by
      simpa only [chi, eta] using
        IrreducibleCharacter.characterPairing_eq_zero hchiEta
    have hisom := hcohIrr.isometry phi (hspan phi hphi)
      psi (hspan psi hpsi)
    rw [heq, htauNorm psi hpsi, hsourceZero] at hisom
    exact one_ne_zero hisom
  have hTcard : T.card = Sirr.card := by
    exact Finset.card_image_iff.mpr htauInj
  have htauZetaT : tauIrr zeta ∈ T := by
    exact Finset.mem_image.mpr ⟨zeta, hzetaSirr, rfl⟩
  have hTvirtual : ∀ alpha ∈ T, ClassFunction.IsVirtual alpha := by
    intro alpha halpha
    obtain ⟨phi, hphi, rfl⟩ := Finset.mem_image.mp halpha
    exact htauVirtual phi hphi
  have hTorthonormal : ∀ alpha ∈ T, ∀ gamma ∈ T,
      characterPairing alpha gamma = if alpha = gamma then 1 else 0 := by
    intro alpha halpha gamma hgamma
    obtain ⟨phi, hphi, rfl⟩ := Finset.mem_image.mp halpha
    obtain ⟨psi, hpsi, rfl⟩ := Finset.mem_image.mp hgamma
    rw [hcohIrr.isometry phi (hspan phi hphi) psi (hspan psi hpsi)]
    by_cases heq : tauIrr phi = tauIrr psi
    · rw [if_pos heq]
      have hphiPsi : phi = psi := htauInj hphi hpsi heq
      subst psi
      exact hsourceNorm phi hphi
    · rw [if_neg heq]
      have hphiPsi : phi ≠ psi := fun h ↦ heq (congrArg tauIrr h)
      let chi : IrreducibleCharacter M ℂ := ⟨phi, hirr phi hphi⟩
      let eta : IrreducibleCharacter M ℂ := ⟨psi, hirr psi hpsi⟩
      have hchiEta : chi ≠ eta := by
        intro h
        exact hphiPsi (congrArg Subtype.val h)
      simpa only [chi, eta] using
        IrreducibleCharacter.characterPairing_eq_zero hchiEta
  have hbetaVirtual : ClassFunction.IsVirtual beta := by
    simpa only [beta] using
      vchar_Dade_FTtype345_bridge hmaxM MtypeP notMtype2
        zeta hzeta i j hj
  have hbetaNorm : characterPairing beta beta = 6 := by
    have hnorm := norm_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i j hj
    change characterPairing
      (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j))
      (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) = 6
    calc
      _ = 2 + FTtype345_ratio MtypeP ^ 2 := hnorm
      _ = 6 := by rw [hratioTwo]; norm_num
  obtain ⟨b, hb⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt hbetaVirtual
      (htauVirtual zeta hzetaSirr)
  let a : ℤ := b + 2
  have haCast : (a : ℂ) = (b : ℂ) + 2 := by
    simp only [a, Int.cast_add, Int.cast_ofNat]
  have haZero : a = 0 := by
    by_contra haNe
    by_cases hbNe : b ≠ 0
    · have hnonzero : ∀ alpha ∈ T,
          characterPairing beta alpha ≠ 0 := by
        intro alpha halpha
        obtain ⟨phi, hphi, rfl⟩ := Finset.mem_image.mp halpha
        by_cases hphiZeta : phi = zeta
        · subst phi
          rw [hb]
          exact Int.cast_ne_zero.mpr hbNe
        · rw [show characterPairing beta (tauIrr phi) =
              characterPairing beta (tauIrr zeta) + 2 by
            simpa only [beta] using hpairShift phi hphi hphiZeta]
          rw [hb, ← haCast]
          exact Int.cast_ne_zero.mpr haNe
      have hbound :=
        PTypeCorePairingInternal.pTypeCore_orthonormal_card_le_norm
        T hTvirtual hTorthonormal hbetaVirtual hnonzero
      rw [hbetaNorm] at hbound
      norm_num at hbound
      have hle : T.card ≤ 6 := hbound
      omega
    · have hbZero : b = 0 := not_ne_iff.mp hbNe
      have haTwo : a = 2 := by simp only [a, hbZero, zero_add]
      have hnonzero : ∀ alpha ∈ T.erase (tauIrr zeta),
          characterPairing beta alpha ≠ 0 := by
        intro alpha halpha
        have halphaT := (Finset.mem_erase.mp halpha).2
        have halphaNe := (Finset.mem_erase.mp halpha).1
        obtain ⟨phi, hphi, hphiImage⟩ := Finset.mem_image.mp halphaT
        subst alpha
        have hphiZeta : phi ≠ zeta := by
          intro h
          subst phi
          exact halphaNe rfl
        rw [show characterPairing beta (tauIrr phi) =
              characterPairing beta (tauIrr zeta) + 2 by
            simpa only [beta] using hpairShift phi hphi hphiZeta]
        rw [hb, ← haCast]
        exact Int.cast_ne_zero.mpr haNe
      have hbound :=
        PTypeCorePairingInternal.pTypeCore_orthonormal_card_le_norm
        (T.erase (tauIrr zeta))
        (fun alpha halpha ↦ hTvirtual alpha (Finset.mem_of_mem_erase halpha))
        (fun alpha halpha gamma hgamma ↦
          hTorthonormal alpha (Finset.mem_of_mem_erase halpha)
            gamma (Finset.mem_of_mem_erase hgamma))
        hbetaVirtual hnonzero
      rw [hbetaNorm] at hbound
      norm_num at hbound
      have hle : (T.erase (tauIrr zeta)).card ≤ 6 := hbound
      rw [Finset.card_erase_of_mem htauZetaT, hTcard] at hle
      omega
  have hbNegTwo : b = -2 := by
    dsimp only [a] at haZero
    omega
  have hbetaZeta : characterPairing beta (tauIrr zeta) = (-2 : ℂ) := by
    rw [hb, hbNegTwo]
    norm_num
  let Y : ClassFunction (⊤ : Subgroup Gamma) ℂ :=
    (-2 : ℤ) • tauIrr zeta
  let X : ClassFunction (⊤ : Subgroup Gamma) ℂ := beta - Y
  have hdecomp : beta = X + Y := by
    dsimp only [X]
    abel
  have hYspan : Y ∈ AddSubgroup.closure
      (tauIrr '' (↑Sirr : Set (ClassFunction M ℂ))) := by
    have hmem : tauIrr zeta ∈
        tauIrr '' (↑Sirr : Set (ClassFunction M ℂ)) :=
      ⟨zeta, hzetaSirr, rfl⟩
    have hzsmul := (AddSubgroup.closure
      (tauIrr '' (↑Sirr : Set (ClassFunction M ℂ)))).zsmul_mem
        (AddSubgroup.subset_closure hmem) (-2 : ℤ)
    simpa only [Y] using hzsmul
  have hYX : characterPairing Y X = 0 := by
    have hZetaBeta : characterPairing (tauIrr zeta) beta = (-2 : ℂ) := by
      rw [characterPairing_comm, hbetaZeta]
    simp only [Y, X, ← Int.cast_smul_eq_zsmul ℂ,
      type5BridgeGlue_pairing_sub_right,
      characterPairing_smul_left, characterPairing_smul_right,
      hZetaBeta, htauNorm zeta hzetaSirr]
    norm_num
  have hYnorm : characterPairing Y Y = FTtype345_ratio MtypeP ^ 2 := by
    simp only [Y, ← Int.cast_smul_eq_zsmul ℂ,
      characterPairing_smul_left,
      characterPairing_smul_right, htauNorm zeta hzetaSirr, hratioTwo]
    norm_num
  have hbridge := FTtype345_bridge_coherence hmaxM MtypeP notMtype2
    zeta hzeta (↑Sirr : Set (ClassFunction M ℂ)) tauIrr i j X Y
      hcohIrr (by simpa only [beta] using hdecomp) hSirrKernel hirr hj
      hYspan hYX hYnorm
  calc
    ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) =
        X + Y := by simpa only [beta] using hdecomp
    _ = (FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP i j -
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) + Y := by rw [hbridge]
    _ = (FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP i j -
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) -
        FTtype345_ratio MtypeP • tauIrr zeta := by
      dsimp only [Y]
      rw [← Int.cast_smul_eq_zsmul ℂ, hratioTwo]
      module


private theorem type5BridgeGlue_alphaFormula
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (Sirr : Finset (ClassFunction M ℂ))
    (tauIrr : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hSirrKernel : cfConjC_subset
      (↑Sirr : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP)))
    (hcohIrr : coherent_with
      (↑Sirr : Set (ClassFunction M ℂ)) (nonidentitySet M)
      (ftType345Tau hmaxM) tauIrr)
    (hirr : ∀ phi ∈ Sirr, IsIrreducibleCharacter M ℂ phi)
    (hdegree : ∀ phi ∈ Sirr, ∀ psi ∈ Sirr, phi 1 = psi 1)
    (hzetaSirr : zeta ∈ Sirr)
    (hcard : 8 ≤ Sirr.card)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hratioTwo : FTtype345_ratio MtypeP = 2) :
    ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) =
      (FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP i j -
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) -
        FTtype345_ratio MtypeP • tauIrr zeta := by
  classical
  have hnot1 : FTtype M ≠ 1 :=
    FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
  have htypeGt : 2 < FTtype M := by
    have hrange := FTtype_range M
    omega
  have hcore : FTcore M = derivedWithin M :=
    FTcore_type_gt2 M htypeGt
  have hSirrFull :
      (↑Sirr : Set (ClassFunction M ℂ)) ⊆
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
    intro phi hphi
    have hphiKernel := hSirrKernel.1 hphi
    simpa [ftType345InducedFamily10, FTtypePKernelLayer,
      PrimeDadeHypothesis.signalizerInKernel, hcore] using hphiKernel

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
  have hzetaOne : zeta 1 = (K.index : ℂ) := by
    rw [hzeta.degree, hindex]

  apply type5BridgeGlue_alphaFormula_of_pairingShift
    hmaxM MtypeP notMtype2 zeta hzeta Sirr tauIrr hSirrKernel
      hcohIrr hirr hzetaSirr hcard i j hj hratioTwo
  intro lam hlam hlamNe
  let alpha : ClassFunction M ℂ :=
    FTtype345_bridge MtypeP zeta i j
  let diff : ClassFunction M ℂ := lam - zeta

  have hlamFull : lam ∈ ftType345InducedFamily10 M :=
    hSirrFull hlam
  have hlamSeq : lam ∈
      seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥ := by
    simpa only [K, ftType345InducedFamily10] using hlamFull
  have hlamReference : FTType345ReferenceChoice M W₁ lam :=
    { irreducible := hirr lam hlam
      mem_calS := hlamFull
      degree := (hdegree lam hlam zeta hzetaSirr).trans hzeta.degree }

  have hdiffSpan : diff ∈ AddSubgroup.closure
      (↑Sirr : Set (ClassFunction M ℂ)) := by
    exact (AddSubgroup.closure
      (↑Sirr : Set (ClassFunction M ℂ))).sub_mem
        (AddSubgroup.subset_closure hlam)
        (AddSubgroup.subset_closure hzetaSirr)
  have hdiffOff : diff ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxOne : x = 1 := by simpa [nonidentitySet] using hx
    subst x
    simp only [diff, ClassFunction.sub_apply]
    rw [hdegree lam hlam zeta hzetaSirr, sub_self]
  have hcoefficient : lam 1 / (K.index : ℂ) = 1 := by
    rw [hdegree lam hlam zeta hzetaSirr, hzeta.degree, hindex]
    exact div_self (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hsmall := seqInd_sub_lin_on (k := ℂ) K
    (calX := Iirr_kerD (k := ℂ) (⊤ : Subgroup K) ⊥)
    hzetaSeq hzetaOne hlamSeq
  rw [hcoefficient, one_smul] at hsmall
  have hdiffSmall : diff ∈
      ClassFunction.supportedOn (subgroupNonidentity K) := by
    simpa only [diff] using hsmall
  have hdiffSupport : diff ∈
      ClassFunction.supportedOn (ftType345Support0InM M) := by
    change diff ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport0 M}
    rw [ClassFunction.mem_supportedOn_iff] at hdiffSmall ⊢
    intro x hx
    apply hdiffSmall
    intro hxDerived
    apply hx
    apply FTsupp1_sub0 hmaxM
    rw [FTsupp1_type_gt2 M htypeGt]
    change (x : Gamma) ∈ derivedWithin M ∧ (x : Gamma) ≠ 1
    refine ⟨hxDerived.1, ?_⟩
    intro hxOne
    exact hxDerived.2 (Subtype.ext hxOne)

  have hdiffAgree : tauIrr diff = ftType345Tau hmaxM diff :=
    hcohIrr.agrees diff hdiffSpan hdiffOff
  have hlamVirtual : ClassFunction.IsVirtual lam :=
    ⟨Finsupp.single ⟨lam, hirr lam hlam⟩ 1, by simp⟩
  have hzetaVirtual : ClassFunction.IsVirtual zeta :=
    ⟨Finsupp.single ⟨zeta, hzeta.irreducible⟩ 1, by simp⟩
  have hdiffVirtual : ClassFunction.IsVirtual diff := by
    simpa only [diff] using hlamVirtual.sub hzetaVirtual
  have htauDiffVirtual : ClassFunction.IsVirtual (tauIrr diff) :=
    hcohIrr.mapsToVirtual diff hdiffSpan
  have hAlphaVirtual : ClassFunction.IsVirtual alpha := by
    simpa only [alpha] using
      vchar_FTtype345_bridge hmaxM MtypeP notMtype2
        zeta hzeta i j
  have hTauAlphaVirtual :
      ClassFunction.IsVirtual (ftType345Tau hmaxM alpha) := by
    simpa only [alpha] using
      vchar_Dade_FTtype345_bridge hmaxM MtypeP notMtype2
        zeta hzeta i j hj
  have hAlphaSupport : alpha ∈
      ClassFunction.supportedOn (ftType345Support0InM M) := by
    simpa only [alpha] using
      supp_FTtype345_bridge hmaxM MtypeP notMtype2
        zeta hzeta i j hj

  have hZetaLam : characterPairing zeta lam = 0 := by
    let chi : IrreducibleCharacter M ℂ := ⟨zeta, hzeta.irreducible⟩
    let psi : IrreducibleCharacter M ℂ := ⟨lam, hirr lam hlam⟩
    have hchiPsi : chi ≠ psi := by
      intro h
      exact hlamNe (congrArg Subtype.val h).symm
    simpa only [chi, psi] using
      IrreducibleCharacter.characterPairing_eq_zero hchiPsi
  have hZetaNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self
      ⟨zeta, hzeta.irreducible⟩
  have hMuJLam :
      characterPairing (ftType345Mu2 MtypeP i j) lam = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP lam hlamReference i j
  have hMuZeroLam : characterPairing
      (ftType345Mu2 MtypeP i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
      lam = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP lam hlamReference i IrreducibleCharacter.trivial
  have hMuJZeta :
      characterPairing (ftType345Mu2 MtypeP i j) zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i j
  have hMuZeroZeta : characterPairing
      (ftType345Mu2 MtypeP i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
      zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i IrreducibleCharacter.trivial
  have hAlphaLam : characterPairing alpha lam = 0 := by
    simp only [alpha, FTtype345_bridge,
      type5BridgeGlue_pairing_sub_left, characterPairing_smul_left,
      hMuJLam, hMuZeroLam, hZetaLam]
    ring
  have hAlphaZeta : characterPairing alpha zeta =
      -FTtype345_ratio MtypeP := by
    simp only [alpha, FTtype345_bridge,
      type5BridgeGlue_pairing_sub_left, characterPairing_smul_left,
      hMuJZeta, hMuZeroZeta, hZetaNorm]
    ring
  have hAlphaDiff : characterPairing alpha diff =
      FTtype345_ratio MtypeP := by
    simp only [diff, type5BridgeGlue_pairing_sub_right,
      hAlphaLam, hAlphaZeta]
    ring

  have hPairDade :
      characterPairing (ftType345Tau hmaxM alpha) (tauIrr diff) =
        characterPairing alpha diff := by
    calc
      characterPairing (ftType345Tau hmaxM alpha) (tauIrr diff) =
          starCharacterPairing (ftType345Tau hmaxM alpha) (tauIrr diff) :=
        (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hTauAlphaVirtual htauDiffVirtual).symm
      _ = starCharacterPairing (ftType345Tau hmaxM alpha)
          (ftType345Tau hmaxM diff) := by rw [← hdiffAgree]
      _ = starCharacterPairing alpha diff :=
        Dade_isometry (FT_Dade0_hyp M hmaxM) alpha diff
          hAlphaSupport hdiffSupport
      _ = characterPairing alpha diff :=
        PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hAlphaVirtual hdiffVirtual
  rw [show tauIrr diff = tauIrr lam - tauIrr zeta by
        simp only [diff, map_sub],
      type5BridgeGlue_pairing_sub_right, hAlphaDiff, hratioTwo] at hPairDade
  change characterPairing (ftType345Tau hmaxM alpha) (tauIrr lam) =
    characterPairing (ftType345Tau hmaxM alpha) (tauIrr zeta) + 2
  linear_combination hPairDade

/-- The final Section 10.10 gluing step, with the numerical/zero-column work
compressed into the single balancing identity `hbridge`. -/
private theorem type5BridgeGlue_final
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (Sirr Sred : Set (ClassFunction M ℂ))
    (R : ClassFunction M ℂ →
      Finset (ClassFunction (⊤ : Subgroup Gamma) ℂ))
    (hsub : subcoherent
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (ftType345Tau hmaxM) R)
    (hcover :
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) =
        Sred ∪ Sirr)
    (hSirr : cfConjC_subset Sirr
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)))
    (hdegree : ∀ chi ∈ Sirr, ∀ psi ∈ Sirr, chi 1 = psi 1)
    (hSred : cfConjC_subset Sred
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)))
    (tauRed : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup Gamma) ℂ)
    (hcohRed : coherent_with Sred (nonidentitySet M)
      (ftType345Tau hmaxM) tauRed)
    (hdisjoint : Sirr ⊆ Sredᶜ)
    (mu phi : ClassFunction M ℂ)
    (hmu : mu ∈ Sred)
    (hphi : phi ∈ AddSubgroup.closure Sirr)
    (hoff : mu - phi ∈
      ClassFunction.supportedOn (nonidentitySet M))
    (hbridge : ftType345Tau hmaxM (mu - phi) =
      tauRed mu -
        (Classical.choose
          (uniform_degree_coherence (subset_subcoherent hsub hSirr)
            hdegree)) phi) :
    coherent
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau hmaxM) := by
  let tauIrr := Classical.choose
    (uniform_degree_coherence (subset_subcoherent hsub hSirr) hdegree)
  have hcohIrr : coherent_with Sirr (nonidentitySet M)
      (ftType345Tau hmaxM) tauIrr :=
    Classical.choose_spec
      (uniform_degree_coherence (subset_subcoherent hsub hSirr) hdegree)
  rw [hcover]
  apply bridge_coherent hsub hSred hcohRed hSirr hcohIrr hdisjoint
    (chi := mu) (phi := phi) hmu hphi hoff
  simpa only [tauIrr] using hbridge

private theorem ftType5_coherent
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (hMtype5 : FTtype M = 5) :
    coherent
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType5Tau M hmaxM) := by
  classical
  have MtypeV : of_typeV M U W W₁ W₂ defW :=
    compl_of_typeV M U W W₁ W₂ defW hmaxM MtypeP hMtype5
  have hUbot : U = ⊥ := MtypeV.2.1
  have hFcoreDerived : Fitting_core M = derivedWithin M :=
    (TypeSpecInternal.semidirect_right_eq_bot_iff_left_eq_ambient16
      MtypeP.2.1.2.2.2).1 hUbot
  have htypeGt : 2 < FTtype M := by omega
  have hcore : FTcore M = derivedWithin M :=
    FTcore_type_gt2 M htypeGt

  let K : Subgroup M := ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  letI : IsSolvable M :=
    of_typeP_sol M U W W₁ W₂ defW MtypeP
  letI : IsSolvable K := inferInstance
  let pd := ftType5PrimeDade hmaxM MtypeP
  let isoM := ftType5IsoM MtypeP
  let isoG := ftType5IsoG hmaxM MtypeP
  let R := FTtypeP_coh_base pd isoM isoG (mFT_odd M)
  have hsub0 := FTtypeP_subcoherent pd isoM isoG (mFT_odd M)
  have hsub : subcoherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) :
        Set (ClassFunction M ℂ))
      (ftType5Tau M hmaxM) R := by
    simpa only [K, pd, ftType5PrimeDade, FTtypePKernelLayer,
      PrimeDadeHypothesis.signalizerInKernel, hcore,
      Subgroup.subgroupOf_self] using hsub0
  have hfq : odd_Frobenius_quotient K (⊥ : Subgroup K) := by
    simpa only [K] using
      ftType5_odd_frobenius_bot MtypeP hFcoreDerived

  rcases non_coherent_chief K (ftType5Tau M hmaxM) R hsub ⊥ hfq with
      hcoherent | hexception
  · simpa only [ftType345InducedFamily10, K] using hcoherent
  · rcases hexception with
      ⟨_hchief, hindexBound, p, hp, hKquotP,
        hKquotNoncommutative, hKindexNotDvd⟩
    letI : Fact p.Prime := ⟨hp⟩
    have hKp : IsPGroup p K :=
      hKquotP.of_equiv QuotientGroup.quotientBot
    have hKnoncommutative : ¬ IsMulCommutative K := by
      intro hKcommutative
      letI : IsMulCommutative K := hKcommutative
      apply hKquotNoncommutative
      rw [isMulCommutative_iff]
      intro x y
      apply QuotientGroup.quotientBot.injective
      simp only [map_mul]
      exact mul_comm _ _
    have hderivedLe : derivedWithin M ≤ M :=
      TypeSpecInternal.derivedWithin_le16_final M
    let eK : K ≃* derivedWithin M :=
      Subgroup.subgroupOfEquivOfLe hderivedLe
    have hHp : IsPGroup p (derivedWithin M) := hKp.of_equiv eK
    have hHnoncommutative : ¬ IsMulCommutative (derivedWithin M) := by
      intro hcommutative
      letI : IsMulCommutative (derivedWithin M) := hcommutative
      apply hKnoncommutative
      rw [isMulCommutative_iff]
      intro x y
      apply eK.injective
      simp only [map_mul]
      exact mul_comm _ _
    have hKindex : K.index = Nat.card W₁ := by
      have houter : IsInternalSemidirectProductIn
          (derivedWithin M) W₁ M := MtypeP.1.2.2.2
      calc
        K.index = Nat.card (W₁.subgroupOf M) :=
          houter.2.2.2.symm.index_eq_card
        _ = Nat.card W₁ :=
          MathlibSupport.natCard_subgroupOf_eq houter.2.1
    have hnotdvd : ¬ Nat.card W₁ ∣ p - 1 := by
      simpa only [hKindex] using hKindexNotDvd
    rcases ftType5_typeV_cases MtypeV hFcoreDerived hp hHp
        hHnoncommutative hnotdvd with hnormalized | hthird
    · apply ftType5_normalizedTI_coherent hmaxM MtypeP hUbot
        hMtype5
      simpa only [hFcoreDerived] using hnormalized
    · rcases hthird with ⟨hcoreCard, hW₁div, _hcyclic⟩
      have hmapCore : (pCore p K).map eK.toMonoidHom =
          pCore p (derivedWithin M) :=
        FTContextInternal.pCore_map_mulEquiv8 p eK
      have hcoreCardK : Nat.card (pCore p K) = p ^ 3 := by
        calc
          Nat.card (pCore p K) =
              Nat.card ((pCore p K).map eK.toMonoidHom) :=
            (Subgroup.card_map_of_injective eK.injective).symm
          _ = Nat.card (pCore p (derivedWithin M)) := by rw [hmapCore]
          _ = p ^ 3 := hcoreCard
      have hKcube := ftType5_prime_cube_index hp hKp
        hKnoncommutative hcoreCardK
      have hbound : p ^ 2 ≤ 4 * (Nat.card W₁) ^ 2 + 1 := by
        calc
          p ^ 2 = (_root_.commutator K).index := hKcube.2.2.symm
          _ ≤ 4 * K.index ^ 2 + 1 := by
            simpa only [sup_bot_eq] using hindexBound
          _ = 4 * (Nat.card W₁) ^ 2 + 1 := by rw [hKindex]
      have hW₂le : W₂ ≤ derivedWithin M := by
        rw [← hFcoreDerived]
        exact MtypeP.2.2.2.1.2.2.1
      have hW₂card : Nat.card W₂ = p :=
        ftType5_prime_subgroup_card hp hHp hW₂le
          (FTtype345_core_prime hmaxM MtypeP notMtype2)
      have hderivedNe : derivedWithin M ≠ ⊥ := by
        intro hbot
        apply hHnoncommutative
        rw [hbot]
        infer_instance
      have hpDvd : p ∣ Nat.card (derivedWithin M) :=
        hHp.card_eq_or_dvd.resolve_left
          (ne_of_gt ((derivedWithin M).one_lt_card_iff_ne_bot.mpr
            hderivedNe))
      have hpOdd : Odd p :=
        (mFT_odd (derivedWithin M)).of_dvd_nat hpDvd
      obtain ⟨hpEq, hW₁ltW₂⟩ := ftType5_step_10_10_1_nat hp hpOdd
        (mFT_odd W₁)
        (ftType5PrimeTI MtypeP).prime_cycTIhyp.two_lt_card_left
        hW₁div hbound hW₂card
      have hderivedCard : Nat.card (derivedWithin M) = p ^ 3 := by
        calc
          Nat.card (derivedWithin M) = Nat.card K :=
            (Nat.card_congr eK.toEquiv).symm
          _ = p ^ 3 := hKcube.1
      have hconstants : FTType345Constants MtypeP :=
        FTtype345_constants hmaxM MtypeP notMtype2
      have hdegreePrime : FTtype345_TIirr_degree MtypeP = p :=
        (ftType5_degree_eq_prime MtypeP hconstants hp hHp
          hHnoncommutative hderivedCard hW₂card).1
      have hratioTwo : FTtype345_ratio MtypeP = 2 :=
        (ftType5_sign_ratio_eq MtypeP hconstants hdegreePrime hpEq).2

      let D : Subgroup K := _root_.commutator K
      let SirrFin : Finset (ClassFunction M ℂ) :=
        seqIndD (k := ℂ) K (⊤ : Subgroup K) D
      let Sirr : Set (ClassFunction M ℂ) := ↑SirrFin
      let j₀ : IrreducibleCharacter W₂ ℂ := FTtype345_jOne MtypeP
      have hj₀ : j₀ ≠ IrreducibleCharacter.trivial := by
        simpa only [j₀] using FTtype345_jOne_ne_trivial MtypeP
      let Sred : Set (ClassFunction M ℂ) :=
        (ftType345PrimeTI MtypeP).uniform_prTIred_seq
          (ftType345IsoM MtypeP) j₀

      obtain ⟨hSirr₀, hSred₀, hSirrData₀, hcover₀, hdisjoint₀⟩ :=
        ftType5_family_partition MtypeP hconstants hp hHp
          hHnoncommutative hderivedCard hW₂card j₀ hj₀
      have hSirr : cfConjC_subset Sirr
          (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
        simpa only [Sirr, SirrFin, D, K, ftType345InducedFamily10] using
          hSirr₀
      have hSred : cfConjC_subset Sred
          (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
        simpa only [Sred, K, ftType345InducedFamily10] using hSred₀
      have hSirrData : ∀ phi ∈ Sirr,
          IsIrreducibleCharacter M ℂ phi ∧
            phi 1 = (Nat.card W₁ : ℂ) := by
        simpa only [Sirr, SirrFin, D, K] using hSirrData₀
      have hcover :
          (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) =
            Sred ∪ Sirr := by
        simpa only [Sred, Sirr, SirrFin, D, K,
          ftType345InducedFamily10] using hcover₀
      have hdisjoint : Sirr ⊆ Sredᶜ := by
        simpa only [Sred, Sirr, SirrFin, D, K] using hdisjoint₀
      have hdegree : ∀ chi ∈ Sirr, ∀ psi ∈ Sirr,
          chi 1 = psi 1 := by
        intro chi hchi psi hpsi
        rw [(hSirrData chi hchi).2, (hSirrData psi hpsi).2]

      have hzetaSirrFin : zeta ∈ SirrFin := by
        simpa only [SirrFin, D, K] using
          ftType5_reference_mem_Sirr MtypeP hconstants hp hHp
            hHnoncommutative hderivedCard hW₂card j₀ hj₀ zeta hzeta
      have hzetaSirr : zeta ∈ Sirr := by
        exact hzetaSirrFin
      have hSirrCard : SirrFin.card = 4 * (Nat.card W₁ - 1) := by
        simpa only [SirrFin, D, K] using
          ftType5_Sirr_card MtypeP hconstants hp hHp
            hHnoncommutative hderivedCard hW₂card hpEq
      have hcard : 8 ≤ SirrFin.card := by
        rw [hSirrCard]
        have hw₁gt :=
          (ftType345PrimeTI MtypeP).prime_cycTIhyp.two_lt_card_left
        omega

      have hfullKernel :
          (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) ⊆
            FTtypePKernelLayer
              (ftType345PrimeDade hmaxM MtypeP) := by
        intro phi hphi
        simpa [ftType345InducedFamily10, FTtypePKernelLayer,
          PrimeDadeHypothesis.signalizerInKernel, hcore] using hphi
      have hSirrKernel : cfConjC_subset Sirr
          (FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP)) :=
        ⟨fun phi hphi ↦ hfullKernel (hSirr.1 hphi), hSirr.2⟩

      let tauIrr := Classical.choose
        (uniform_degree_coherence (subset_subcoherent hsub hSirr) hdegree)
      have hcohIrr : coherent_with Sirr (nonidentitySet M)
          (ftType345Tau hmaxM) tauIrr :=
        Classical.choose_spec
          (uniform_degree_coherence (subset_subcoherent hsub hSirr) hdegree)
      have hDalpha : ∀ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j₀) =
            (FTtype345_TIsign MtypeP : ℂ) •
                (ftType345Eta hmaxM MtypeP i j₀ -
                  ftType345Eta hmaxM MtypeP i
                    (IrreducibleCharacter.trivial :
                      IrreducibleCharacter W₂ ℂ)) -
              FTtype345_ratio MtypeP • tauIrr zeta := by
        intro i
        apply type5BridgeGlue_alphaFormula hmaxM MtypeP notMtype2
          zeta hzeta SirrFin tauIrr
        · simpa only [Sirr] using hSirrKernel
        · simpa only [Sirr] using hcohIrr
        · intro phi hphi
          exact (hSirrData phi hphi).1
        · intro phi hphi psi hpsi
          exact hdegree phi hphi psi hpsi
        · exact hzetaSirrFin
        · exact hcard
        · exact hj₀
        · exact hratioTwo

      have hpsiFull :
          (ftType345PrimeTI MtypeP).primeTIRed
                (ftType345IsoM MtypeP)
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ) - zeta ∈
            ClassFunction.supportedOn
              {x : M | (x : Gamma) ∈ FTsupport M} := by
        simpa only [ftType5Mu] using
          zeroColumn_fullSupport hmaxM MtypeP notMtype2 zeta hzeta
      have hpsiSupport :
          (ftType345PrimeTI MtypeP).primeTIRed
                (ftType345IsoM MtypeP)
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ) - zeta ∈
            ClassFunction.supportedOn
              {x : M | (x : Gamma) ∈ FTsupport0 M} := by
        rw [ClassFunction.mem_supportedOn_iff] at hpsiFull ⊢
        intro x hx
        apply hpsiFull x
        intro hxFull
        exact hx (FTsupp_sub0 M hxFull)
      obtain ⟨chi, hzeroBridge₀, hchiVirtual, hchiNorm, hchiEta⟩ :=
        FTtype345_Dade_bridge0 hmaxM MtypeP notMtype2
          zeta hzeta hW₁ltW₂
      have hzeroBridge : ftType345Tau hmaxM
            ((ftType345PrimeTI MtypeP).primeTIRed
                (ftType345IsoM MtypeP)
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ) - zeta) =
          (∑ i : IrreducibleCharacter W₁ ℂ,
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) - chi := by
        simpa only [ftType5Tau, ftType5Mu, ftType5Eta] using hzeroBridge₀
      have hzero := type5BridgeGlue_identify_zeroResidual
        hmaxM MtypeP notMtype2 zeta hzeta Sirr tauIrr
        hSirrKernel hcohIrr hzetaSirr j₀ hj₀
        (hDalpha (IrreducibleCharacter.trivial :
          IrreducibleCharacter W₁ ℂ)) hpsiSupport chi hzeroBridge
        hchiVirtual hchiNorm hchiEta hratioTwo

      obtain ⟨tauRed, hcohRed₀, htauRed₀⟩ :=
        type5BridgeGlue_uniform_prTIred_coherentWith
          (ftType345PrimeDade hmaxM MtypeP)
          (ftType345IsoM MtypeP) (ftType345IsoG hmaxM MtypeP)
          j₀ hj₀
      have hcohRed : coherent_with Sred (nonidentitySet M)
          (ftType345Tau hmaxM) tauRed := by
        simpa only [Sred] using hcohRed₀
      have htauRed : tauRed
            ((ftType345PrimeTI MtypeP).primeTIRed
              (ftType345IsoM MtypeP) j₀) =
          (FTtype345_TIsign MtypeP : ℂ) •
            ∑ i : IrreducibleCharacter W₁ ℂ,
              ftType345Eta hmaxM MtypeP i j₀ := by
        simpa only [j₀, FTtype345_TIsign] using htauRed₀ j₀
      have hbalancing := type5BridgeGlue_balancingIdentity
        hmaxM MtypeP zeta tauIrr j₀ hDalpha hzero
      have hbridge : ftType345Tau hmaxM
            ((ftType345PrimeTI MtypeP).primeTIRed
                (ftType345IsoM MtypeP) j₀ -
              (FTtype345_TIirr_degree MtypeP : ℂ) • zeta) =
          tauRed ((ftType345PrimeTI MtypeP).primeTIRed
              (ftType345IsoM MtypeP) j₀) -
            tauIrr ((FTtype345_TIirr_degree MtypeP : ℂ) • zeta) := by
        rw [htauRed]
        exact hbalancing

      have hmu :
          (ftType345PrimeTI MtypeP).primeTIRed
              (ftType345IsoM MtypeP) j₀ ∈ Sred := by
        refine ⟨j₀, ⟨hj₀, rfl⟩, rfl⟩
      have hphi : (FTtype345_TIirr_degree MtypeP : ℂ) • zeta ∈
          AddSubgroup.closure Sirr := by
        simpa only [Nat.cast_smul_eq_nsmul] using
          (AddSubgroup.closure Sirr).nsmul_mem
            (AddSubgroup.subset_closure hzetaSirr)
            (FTtype345_TIirr_degree MtypeP)
      have hoff :
          (ftType345PrimeTI MtypeP).primeTIRed
                (ftType345IsoM MtypeP) j₀ -
              (FTtype345_TIirr_degree MtypeP : ℂ) • zeta ∈
            ClassFunction.supportedOn (nonidentitySet M) := by
        rw [ClassFunction.mem_supportedOn_iff]
        intro x hx
        have hxOne : x = 1 := by simpa [nonidentitySet] using hx
        subst x
        simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
          smul_eq_mul]
        rw [(ftType345PrimeTI MtypeP).prTIred_1
          (ftType345IsoM MtypeP) j₀,
          hconstants.degree_constant
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₁ ℂ) j₀ hj₀,
          hzeta.degree]
        ring
      apply type5BridgeGlue_final hmaxM Sirr Sred R hsub hcover hSirr
        hdegree hSred tauRed hcohRed hdisjoint
        ((ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j₀)
        ((FTtype345_TIirr_degree MtypeP : ℂ) • zeta)
        hmu hphi hoff
      simpa only [tauIrr] using hbridge

/-- The local form of Peterfalvi (10.10). -/
theorem FTtype5_exclusion_main
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta) :
    FTtype M ≠ 5 := by
  intro hMtype5
  obtain ⟨tau₁, htau₁⟩ :=
    ftType5_coherent hmaxM MtypeP notMtype2 zeta hzeta hMtype5
  exact FTtype345_noncoherence_main
    hmaxM MtypeP notMtype2 zeta hzeta tau₁ htau₁

/-- Peterfalvi (10.10), excluding type V. -/
theorem FTtype5_exclusion
    (M : Subgroup Gamma)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma)) :
    FTtype M ≠ 5 := by
  intro hMtype5
  obtain ⟨U, W, W₁, W₂, defW, hV⟩ :=
    (FTtypeP 5 M hmaxM).mpr hMtype5
  have hnot2 : FTtype M ≠ 2 := by omega
  obtain ⟨zeta, hzeta⟩ := FTtypeP_ref_irr hmaxM hV.1
  exact (FTtype5_exclusion_main hmaxM hV.1 hnot2 zeta hzeta)
    hMtype5

/-! ## Peterfalvi (10.11) -/

/-- The source family `seqIndD M' M M_F 1` in the type-II conclusion. -/
def ftTypeIICoreFamily (M : Subgroup Gamma) : Set (ClassFunction M ℂ) :=
  ↑(seqIndD (k := ℂ) (pTypeCoreDerived M) (pTypeCoreFitting M) ⊥)

private theorem ftType5_FcoreKernel_eq_bot_of_factor_card
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (hcard : Nat.card (ptypeFCoreFactor ctx) =
      Nat.card (Fitting_core M)) :
    Ptype_Fcore_kernel ctx = ⊥ := by
  let H₀P :=
    (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)
  have hmul :
      Nat.card (Fitting_core M) =
        Nat.card (ptypeFCoreFactor ctx) * Nat.card H₀P :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup H₀P
  have hH₀Pcard : Nat.card H₀P = 1 := by
    apply Nat.eq_of_mul_eq_mul_left
      (Nat.card_pos (α := ptypeFCoreFactor ctx))
    calc
      Nat.card (ptypeFCoreFactor ctx) * Nat.card H₀P =
          Nat.card (Fitting_core M) := hmul.symm
      _ = Nat.card (ptypeFCoreFactor ctx) := hcard.symm
      _ = Nat.card (ptypeFCoreFactor ctx) * 1 := (Nat.mul_one _).symm
  apply Subgroup.eq_bot_of_card_eq
  rw [← MathlibSupport.natCard_subgroupOf_eq
    (Ptype_Fcore_kernel_lt ctx).le]
  exact hH₀Pcard

/-- Both cyclic factors in a type-P pair have prime cardinality. -/
theorem FTtypeP_pair_primes
    (S T W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hpair : typeP_pair S T W W₁ W₂ defW) :
    (Nat.card W₁).Prime ∧ (Nat.card W₂).Prime := by
  have hSnot5 := FTtype5_exclusion S hpair.S_maximal
  have hTnot5 := FTtype5_exclusion T hpair.T_maximal
  obtain ⟨U, hSP⟩ := typeP_pairW S T W W₁ W₂ defW hpair
  let swappedDefW : IsInternalDirectProductIn W₂ W₁ W := defW.swap
  have hpair' : typeP_pair T S W W₂ W₁ swappedDefW :=
    typeP_pair_sym S T W W₁ W₂ defW swappedDefW hpair
  obtain ⟨V, hTP⟩ := typeP_pairW T S W W₂ W₁ swappedDefW hpair'
  exact
    ⟨(compl_of_typeII_IV S U W W₁ W₂ defW
        hpair.S_maximal hSP hSnot5).2.2.1,
      (compl_of_typeII_IV T V W W₂ W₁ swappedDefW
        hpair.T_maximal hTP hTnot5).2.2.1⟩

/-- Both cyclic factors in any type-P witness have prime cardinality. -/
theorem FTtypeP_primes
    (M U W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW) :
    (Nat.card W₁).Prime ∧ (Nat.card W₂).Prime := by
  obtain ⟨T, hpair, _swappedDefW, _V, _TtypeP⟩ :=
    FTtypeP_pair_witness defW hmaxM MtypeP
  exact FTtypeP_pair_primes M T W W₁ W₂ defW hpair

set_option maxHeartbeats 1000000 in
/-- The remaining type-II conclusions of Peterfalvi (10.11). -/
theorem FTtypeII_prime_facts
    (M U W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (hMtype2 : FTtype M = 2) :
    IsElementaryAbelianGroup (Nat.card W₂) (Fitting_core M) ∧
      Nat.card (Fitting_core M) =
        (Nat.card W₂) ^ (Nat.card W₁) ∧
      coherent (ftTypeIICoreFamily M) (nonidentitySet M)
        (ftType5Tau M hmaxM) := by
  classical
  have hnot5 := FTtype5_exclusion M hmaxM
  have hII := compl_of_typeII M U W W₁ W₂ defW
    hmaxM MtypeP hMtype2
  have hprimes := FTtypeP_primes M U W W₁ W₂ defW hmaxM MtypeP
  let ctx : PTypeFCoreContext M U W W₁ W₂ :=
    Ptype_Fcore_context hmaxM defW MtypeP hnot5
  have hcore := typeII_IV_core ctx
  have hcore' :
      centralizerWithin (Fitting_core M) U = ⊥ ∧
        Nat.card (Fitting_core M) =
          (Nat.card W₂) ^ (Nat.card W₁) := by
    simpa [TypeIIIVCoreConclusion, hMtype2] using hcore

  have hfacts := Ptype_Fcore_factor_facts ctx
  have hfactorPrime : ptypeFactorPrime ctx = Nat.card W₂ :=
    def_Ptype_factor_prime ctx hprimes.2
  have hfactorCard :
      Nat.card (ptypeFCoreFactor ctx) = Nat.card (Fitting_core M) := by
    calc
      Nat.card (ptypeFCoreFactor ctx) =
          ptypeFactorPrime ctx ^ Nat.card W₁ := hfacts.factor_card
      _ = (Nat.card W₂) ^ Nat.card W₁ := by rw [hfactorPrime]
      _ = Nat.card (Fitting_core M) := hcore'.2.symm
  have hkernelBot : Ptype_Fcore_kernel ctx = ⊥ :=
    ftType5_FcoreKernel_eq_bot_of_factor_card ctx hfactorCard
  have hfactorElementary :
      IsElementaryAbelianGroup (Nat.card W₂) (ptypeFCoreFactor ctx) := by
    simpa only [hfactorPrime] using ptypeFCoreFactor_elementary ctx
  have hcoreElementary :
      IsElementaryAbelianGroup (Nat.card W₂) (Fitting_core M) := by
    have hsubgroupBot :
        (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M) = ⊥ := by
      apply le_bot_iff.mp
      intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hx' : (x : Gamma) ∈ Ptype_Fcore_kernel ctx := hx
      rw [hkernelBot] at hx'
      exact Subgroup.mem_bot.mp hx'
    let e₀ : ptypeFCoreFactor ctx ≃*
        (Fitting_core M ⧸ (⊥ : Subgroup (Fitting_core M))) :=
      QuotientGroup.quotientMulEquivOfEq hsubgroupBot
    let e : ptypeFCoreFactor ctx ≃* Fitting_core M :=
      e₀.trans (QuotientGroup.quotientBot (G := Fitting_core M))
    refine
      { isPGroup := hfactorElementary.isPGroup.of_equiv e
        commutative := ?_
        pow_eq_one := ?_ }
    · apply isMulCommutative_iff.mpr
      intro x y
      apply e.symm.injective
      simpa only [map_mul] using
        (isMulCommutative_iff.mp hfactorElementary.commutative
          (e.symm x) (e.symm y))
    · intro x
      apply e.symm.injective
      simpa only [map_pow, map_one] using
        hfactorElementary.pow_eq_one (e.symm x)

  letI : IsMulCommutative U := hII.2.1
  let hfacts' := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx hfacts'
  have hcommD : _root_.commutator D.C = ⊥ := by
    exact _root_.commutator_eq_bot (G := D.C)
  have hH₀nested :
      pTypeH0InDerived M (derivedWithin M) (Ptype_Fcore_kernel ctx) =
        ⊥ := by
    ext x
    simp [pTypeH0InDerived, hkernelBot]
  have hderivedBot :
      pTypeDerivedComplementInMaximal (U.subtype.comp D.C.subtype) =
        ⊥ := by
    simp [pTypeDerivedComplementInMaximal, hcommD]
  have hderivedNested :
      ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf
            (pTypeHUInMaximal M (derivedWithin M)) = ⊥ := by
    ext x
    simp [hderivedBot]
  have hkernelDerivedBot : pTypeCoreKernelDerivedComplement ctx = ⊥ := by
    change
      pTypeH0InDerived M (derivedWithin M) (Ptype_Fcore_kernel ctx) ⊔
          ((pTypeDerivedComplementInMaximal
            (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf
              (pTypeHUInMaximal M (derivedWithin M)) = ⊥
    rw [hH₀nested, hderivedNested]
    simp
  have hcoh :
      coherent
        (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))
        (nonidentitySet M) (ftType5Tau M hmaxM) := by
    simpa only [ctx, ftType5Tau] using
      Ptype_core_coherence hmaxM defW MtypeP hnot5
  exact ⟨hcoreElementary, hcore'.2, by
    unfold ftTypeIICoreFamily
    unfold pTypeCoreFamilyOfContext at hcoh
    rw [hkernelDerivedBot] at hcoh
    convert hcoh using 1
    congr 2 <;> apply Subsingleton.elim⟩

end

end Submission.OddOrder.PF
