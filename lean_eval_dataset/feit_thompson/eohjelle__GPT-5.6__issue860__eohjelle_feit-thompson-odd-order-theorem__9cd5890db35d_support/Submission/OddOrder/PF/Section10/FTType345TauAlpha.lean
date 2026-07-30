import Submission.OddOrder.PF.Section10.FTType345BridgeCoherence

/-!
# Peterfalvi Section 10: the tau-alpha identity

This phase proves the first explicit bridge formula in Peterfalvi (10.5).  The
coherence uniqueness theorem is imported from `FTType345BridgeCoherence`; the
reference-pairing calculation and its integral arithmetic remain private to
this module.
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

local instance tauAlphaInvertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace FTType345CoherenceInternal

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

private theorem inverseLinear_involutive
    {Q : Type} [Group Q] (phi : ClassFunction Q ℂ) :
    ClassFunction.inverseLinear (ClassFunction.inverseLinear phi) = phi := by
  ext x
  simp

private theorem pairing_inverseLinear_left
    {Q : Type} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.inverseLinear phi) psi =
      characterPairing phi (ClassFunction.inverseLinear psi) := by
  unfold characterPairing
  congr 1
  refine Fintype.sum_equiv (Equiv.inv Q) _ _ fun x ↦ ?_
  simp only [Equiv.inv_apply, ClassFunction.inverseLinear_apply, inv_inv]

private theorem coeffDot_sq_le_normSq_mul_normSq
    {I : Type*} (a b : IntegralLattice I) :
    coeffDot a b ^ 2 ≤ normSq a * normSq b := by
  classical
  let s : Finset I := a.support ∪ b.support
  have hab : coeffDot a b = ∑ i ∈ s, a i * b i := by
    rw [coeffDot]
    apply Finset.sum_subset Finset.subset_union_left
    intro i hi his
    have hai : a i = 0 := Finsupp.notMem_support_iff.mp his
    simp [hai]
  have haa : normSq a = ∑ i ∈ s, a i ^ 2 := by
    rw [normSq_eq_sum]
    apply Finset.sum_subset Finset.subset_union_left
    intro i hi his
    have hai : a i = 0 := Finsupp.notMem_support_iff.mp his
    simp [hai]
  have hbb : normSq b = ∑ i ∈ s, b i ^ 2 := by
    rw [normSq_eq_sum]
    apply Finset.sum_subset Finset.subset_union_right
    intro i hi his
    have hbi : b i = 0 := Finsupp.notMem_support_iff.mp his
    simp [hbi]
  rw [hab, haa, hbb]
  exact Finset.sum_mul_sq_le_sq_mul_sq s a b

private theorem type345_coefficient_zero_of_bound
    (m d n : ℕ) (delta a : ℤ)
    (hmOdd : Odd m) (hmGtTwo : 2 < m)
    (hdOdd : Odd d) (hdGtOne : 1 < d)
    (hdelta : IsSign delta)
    (hrelation : (d : ℤ) = delta + (m : ℤ) * (n : ℤ))
    (hbound : ((d : ℤ) * a) ^ 2 ≤
      ((2 : ℤ) + (n : ℤ) ^ 2) * (m : ℤ)) :
    a = 0 := by
  by_contra ha
  have haSq : (1 : ℤ) ≤ a ^ 2 := by
    have hpos : (0 : ℤ) < a ^ 2 := sq_pos_of_ne_zero ha
    omega
  have hbase : (d : ℤ) ^ 2 ≤
      ((2 : ℤ) + (n : ℤ) ^ 2) * (m : ℤ) := by
    calc
      (d : ℤ) ^ 2 = (d : ℤ) ^ 2 * 1 := by ring
      _ ≤ (d : ℤ) ^ 2 * a ^ 2 :=
        mul_le_mul_of_nonneg_left haSq (sq_nonneg _)
      _ = ((d : ℤ) * a) ^ 2 := by ring
      _ ≤ _ := hbound
  rcases hdelta with hdelta | hdelta
  · rw [hdelta] at hrelation
    have hrelationNat : d = m * n + 1 := by
      exact_mod_cast (show (d : ℤ) =
        (m : ℤ) * (n : ℤ) + 1 by omega)
    have hprodNotOdd : ¬ Odd (m * n) := by
      apply Nat.odd_add_one.mp
      rw [← hrelationNat]
      exact hdOdd
    have hprodEven : Even (m * n) :=
      Nat.not_odd_iff_even.mp hprodNotOdd
    have hnEven : Even n := by
      rcases Nat.even_or_odd n with hn | hn
      · exact hn
      · exact False.elim
          ((Nat.not_odd_iff_even.mpr hprodEven) (hmOdd.mul hn))
    have hnPos : 0 < n := by
      by_contra hn
      have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp at hrelationNat
      omega
    have hnTwo : 2 ≤ n := by
      obtain ⟨q, hq⟩ := hnEven
      omega
    have hdiff :
        (d : ℤ) ^ 2 -
            ((2 : ℤ) + (n : ℤ) ^ 2) * (m : ℤ) =
          (m : ℤ) * ((m : ℤ) - 1) * (n : ℤ) ^ 2 +
            2 * (m : ℤ) * ((n : ℤ) - 1) + 1 := by
      rw [show (d : ℤ) = (m : ℤ) * (n : ℤ) + 1 by
        exact_mod_cast hrelationNat]
      ring
    have hmOne : (0 : ℤ) ≤ (m : ℤ) - 1 := by omega
    have hnOne : (0 : ℤ) ≤ (n : ℤ) - 1 := by omega
    have hfirst : (0 : ℤ) ≤
        (m : ℤ) * ((m : ℤ) - 1) * (n : ℤ) ^ 2 := by
      positivity
    have hsecond : (0 : ℤ) ≤
        2 * (m : ℤ) * ((n : ℤ) - 1) := by
      positivity
    nlinarith
  · rw [hdelta] at hrelation
    have hrelationNat : d + 1 = m * n := by
      exact_mod_cast (show (d : ℤ) + 1 = (m : ℤ) * (n : ℤ) by
        omega)
    have hprodEven : Even (m * n) := by
      rw [← hrelationNat]
      exact hdOdd.add_one
    have hnEven : Even n := by
      rcases Nat.even_or_odd n with hn | hn
      · exact hn
      · exact False.elim
          ((Nat.not_odd_iff_even.mpr hprodEven) (hmOdd.mul hn))
    have hnPos : 0 < n := by
      by_contra hn
      have hnZero : n = 0 := Nat.eq_zero_of_not_pos hn
      subst n
      simp at hrelationNat
    have hnTwo : 2 ≤ n := by
      obtain ⟨q, hq⟩ := hnEven
      omega
    let x : ℤ := (m : ℤ) - 3
    let y : ℤ := (n : ℤ) - 2
    have hx : 0 ≤ x := by dsimp [x]; omega
    have hy : 0 ≤ y := by dsimp [y]; omega
    have hpoly : (0 : ℤ) ≤
        x ^ 2 * y ^ 2 + 4 * x ^ 2 * y + 4 * x ^ 2 +
          5 * x * y ^ 2 + 18 * x * y + 14 * x +
          6 * y ^ 2 + 18 * y := by
      positivity
    have hdiff :
        (d : ℤ) ^ 2 -
            ((2 : ℤ) + (n : ℤ) ^ 2) * (m : ℤ) =
          x ^ 2 * y ^ 2 + 4 * x ^ 2 * y + 4 * x ^ 2 +
            5 * x * y ^ 2 + 18 * x * y + 14 * x +
            6 * y ^ 2 + 18 * y + 7 := by
      have hd : (d : ℤ) = (m : ℤ) * (n : ℤ) - 1 := by
        omega
      rw [hd]
      dsimp [x, y]
      ring
    nlinarith

private theorem fullDerivedFamily_sub_kernelLayer
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

private theorem fullDerivedClosure_supportedOn_fullSupport
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)))
    (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet M)) :
    phi ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport M} := by
  have hnot1 : FTtype M ≠ 1 :=
    FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
  have htypeMgt2 : 2 < FTtype M := by
    have hrange := FTtype_range M
    omega
  let K : Subgroup M := ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  have hphiK : phi ∈ ClassFunction.supportedOn (K : Set M) := by
    have hle : AddSubgroup.closure
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) ≤
        (ClassFunction.supportedOn (K : Set M)).toAddSubgroup := by
      refine (AddSubgroup.closure_le _).2 ?_
      intro psi hpsi
      exact seqInd_on K hpsi
    exact hle hphi
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  by_cases hxK : x ∈ K
  · by_cases hxOne : x = 1
    · exact ClassFunction.eq_zero_of_mem_supportedOn hoff (by simpa [hxOne])
    · exfalso
      apply hx
      have hxDerived : (x : Gamma) ∈
          subgroupNonidentity (derivedWithin M) :=
        ⟨hxK, fun hx ↦ hxOne (Subtype.ext hx)⟩
      change (x : Gamma) ∈ FTsupport M
      rw [FTsupp_eq1 hmaxM htypeMgt2,
        FTsupp1_type_gt2 M htypeMgt2]
      exact hxDerived
  · exact ClassFunction.eq_zero_of_mem_supportedOn hphiK hxK

private theorem reducedColumn_mem_fullDerivedFamily
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
    simpa using htriv.trans
      ((ftType345PrimeTI MtypeP).prTIres0
        (ftType345IsoM MtypeP)).symm
  · exact ((ftType345PrimeTI MtypeP).cfInd_prTIres
      (ftType345IsoM MtypeP) j).symm

private theorem inverse_reference_mem_fullDerivedFamily
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType345InducedFamily10 M) :
    ClassFunction.inverseLinear zeta ∈ ftType345InducedFamily10 M := by
  exact seqInd_inverse_mem (k := ℂ) (ftType345DerivedInM M)
    (⊤ : Subgroup (ftType345DerivedInM M)) ⊥ hzeta

private theorem inverse_irreducible
    {phi : ClassFunction M ℂ}
    (hphi : IsIrreducibleCharacter M ℂ phi) :
    IsIrreducibleCharacter M ℂ (ClassFunction.inverseLinear phi) := by
  simpa only [← ClassFunction.inverseLinear_irreducible] using
    (IrreducibleCharacter.dual
      (⟨phi, hphi⟩ : IrreducibleCharacter M ℂ)).property

private theorem irreducible_isVirtual
    {Q : Type} [Group Q] {phi : ClassFunction Q ℂ}
    (hphi : IsIrreducibleCharacter Q ℂ phi) :
    ClassFunction.IsVirtual phi := by
  exact ⟨Finsupp.single ⟨phi, hphi⟩ 1, by simp⟩

private theorem reducedColumn_isVirtual
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual
      ((ftType345PrimeTI MtypeP).primeTIRed
        (ftType345IsoM MtypeP) j) := by
  exact ⟨(ftType345PrimeTI MtypeP).primeTIRedVirtualCharacter
    (ftType345IsoM MtypeP) j, rfl⟩

private theorem sub_inverse_supportedOn_nonidentity
    (phi : ClassFunction M ℂ) :
    phi - ClassFunction.inverseLinear phi ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hxOne : x = 1 := by simpa [nonidentitySet] using hx
  subst x
  simp

private theorem fullDerived_reference_dual_orthogonal
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType345InducedFamily10 M) :
    characterPairing zeta (ClassFunction.inverseLinear zeta) = 0 := by
  letI : (ftType345DerivedInM M).Normal :=
    TypeSpecInternal.derivedWithin_normal16 M
  exact seqInd_conjC_ortho (k := ℂ) (ftType345DerivedInM M)
    (mFT_odd M) (⊤ : Subgroup (ftType345DerivedInM M)) ⊥ hzeta

private theorem fullDerived_difference_supportedOn_nonidentity
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    (ftType345PrimeTI MtypeP).primeTIRed
          (ftType345IsoM MtypeP) j -
        (FTtype345_TIirr_degree MtypeP : ℂ) •
          ClassFunction.inverseLinear zeta ∈
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
  simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
    ClassFunction.inverseLinear_apply, inv_one, smul_eq_mul]
  rw [hdegree, hconstant, hzeta.degree]
  ring

private theorem bridge_reference_pairing
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
      (tau₁ zeta) = -FTtype345_ratio MtypeP := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let alpha := FTtype345_bridge MtypeP zeta i j
  let alphaTau := ftType345Tau hmaxM alpha
  let zetaStar := ClassFunction.inverseLinear zeta
  let d := FTtype345_TIirr_degree MtypeP
  let delta := FTtype345_TIsign MtypeP

  obtain ⟨n, hn⟩ :=
    (FTtype345_constants hmaxM MtypeP notMtype2).ratio_natural

  have hzetaSpan : zeta ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hzeta.mem_calS
  have hzetaStarMem : zetaStar ∈ ftType345InducedFamily10 M := by
    exact inverse_reference_mem_fullDerivedFamily zeta hzeta.mem_calS
  have hzetaStarSpan : zetaStar ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hzetaStarMem
  have hzetaVirtual : ClassFunction.IsVirtual zeta :=
    irreducible_isVirtual hzeta.irreducible
  have hzetaStarIrr : IsIrreducibleCharacter M ℂ zetaStar := by
    exact inverse_irreducible hzeta.irreducible
  have hzetaStarVirtual : ClassFunction.IsVirtual zetaStar :=
    irreducible_isVirtual hzetaStarIrr

  have hmuZ (a : IrreducibleCharacter W₁ ℂ)
      (b : IrreducibleCharacter W₂ ℂ) :
      characterPairing (ftType345Mu2 MtypeP a b) zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta a b
  have hmuInverse (a : IrreducibleCharacter W₁ ℂ)
      (b : IrreducibleCharacter W₂ ℂ) :
      ClassFunction.inverseLinear (ftType345Mu2 MtypeP a b) =
        ftType345Mu2 MtypeP (IrreducibleCharacter.dual a)
          (IrreducibleCharacter.dual b) := by
    calc
      ClassFunction.inverseLinear (ftType345Mu2 MtypeP a b) =
          (IrreducibleCharacter.dual
            (pti.primeTIIndex isoM (a, b)) : ClassFunction M ℂ) :=
        ClassFunction.inverseLinear_irreducible
          (pti.primeTIIndex isoM (a, b))
      _ = (pti.primeTIIndex isoM
            (IrreducibleCharacter.dual a,
              IrreducibleCharacter.dual b) : ClassFunction M ℂ) := by
        rw [pti.primeTIIndex_dual isoM]
      _ = ftType345Mu2 MtypeP (IrreducibleCharacter.dual a)
          (IrreducibleCharacter.dual b) := rfl
  have hmuZstar (a : IrreducibleCharacter W₁ ℂ)
      (b : IrreducibleCharacter W₂ ℂ) :
      characterPairing (ftType345Mu2 MtypeP a b) zetaStar = 0 := by
    calc
      characterPairing (ftType345Mu2 MtypeP a b) zetaStar =
          characterPairing
            (ClassFunction.inverseLinear (ftType345Mu2 MtypeP a b))
            zeta :=
        (pairing_inverseLinear_left
          (ftType345Mu2 MtypeP a b) zeta).symm
      _ = characterPairing
          (ftType345Mu2 MtypeP (IrreducibleCharacter.dual a)
            (IrreducibleCharacter.dual b)) zeta := by rw [hmuInverse]
      _ = 0 := hmuZ _ _

  have hzetaNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self ⟨zeta, hzeta.irreducible⟩
  have hzetaDualOrth : characterPairing zeta zetaStar = 0 := by
    exact fullDerived_reference_dual_orthogonal zeta hzeta.mem_calS
  have hAlphaZ : characterPairing alpha zeta = -FTtype345_ratio MtypeP := by
    simp only [alpha, FTtype345_bridge, pairing_sub_left,
      characterPairing_smul_left, hmuZ, hzetaNorm]
    ring
  have hAlphaZstar : characterPairing alpha zetaStar = 0 := by
    simp only [alpha, FTtype345_bridge, pairing_sub_left,
      characterPairing_smul_left, hmuZstar, hzetaDualOrth]
    ring

  let zdiff : ClassFunction M ℂ := zeta - zetaStar
  have hzdiffSpan : zdiff ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
    exact (AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))).sub_mem
        hzetaSpan hzetaStarSpan
  have hzdiffOff : zdiff ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
    exact sub_inverse_supportedOn_nonidentity zeta
  have hzdiffFull : zdiff ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport M} :=
    fullDerivedClosure_supportedOn_fullSupport hmaxM MtypeP notMtype2
      hzdiffSpan hzdiffOff
  have hzdiffSupport0 : zdiff ∈
      ClassFunction.supportedOn (ftType345Support0InM M) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    apply ClassFunction.eq_zero_of_mem_supportedOn hzdiffFull
    intro hxSupport
    exact hx (FTsupp_sub0 M hxSupport)
  have hzdiffVirtual : ClassFunction.IsVirtual zdiff :=
    hzetaVirtual.sub hzetaStarVirtual
  have htauZdiffVirtual : ClassFunction.IsVirtual (tau₁ zdiff) :=
    hcoh.mapsToVirtual zdiff hzdiffSpan
  have hzdiffAgree : tau₁ zdiff = ftType345Tau hmaxM zdiff :=
    hcoh.agrees zdiff hzdiffSpan hzdiffOff
  have hAlphaSupport := supp_FTtype345_bridge hmaxM MtypeP notMtype2
    zeta hzeta i j hj
  have hAlphaVirtual := vchar_FTtype345_bridge hmaxM MtypeP notMtype2
    zeta hzeta i j
  have hAlphaTauVirtual := vchar_Dade_FTtype345_bridge
    hmaxM MtypeP notMtype2 zeta hzeta i j hj
  have hAlphaZdiff : characterPairing alpha zdiff =
      -FTtype345_ratio MtypeP := by
    simp only [zdiff]
    rw [pairing_sub_right, hAlphaZ, hAlphaZstar, sub_zero]
  have hAlphaTauZdiff : characterPairing alphaTau (tau₁ zdiff) =
      characterPairing alpha zdiff := by
    calc
      characterPairing alphaTau (tau₁ zdiff) =
          starCharacterPairing alphaTau (tau₁ zdiff) :=
        (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hAlphaTauVirtual htauZdiffVirtual).symm
      _ = starCharacterPairing alphaTau (ftType345Tau hmaxM zdiff) := by
        rw [hzdiffAgree]
      _ = starCharacterPairing alpha zdiff :=
        Dade_isometry (FT_Dade0_hyp M hmaxM) alpha zdiff
          hAlphaSupport hzdiffSupport0
      _ = characterPairing alpha zdiff :=
        PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hAlphaVirtual hzdiffVirtual

  have htauZetaVirtual : ClassFunction.IsVirtual (tau₁ zeta) :=
    hcoh.mapsToVirtual zeta hzetaSpan
  obtain ⟨c, hc⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt
      hAlphaTauVirtual htauZetaVirtual
  let a : ℤ := c + n
  have hAlphaTauZetaStar :
      characterPairing alphaTau (tau₁ zetaStar) = (a : ℂ) := by
    have h := hAlphaTauZdiff
    simp only [zdiff] at h
    rw [map_sub, pairing_sub_right, hc, hAlphaZdiff, hn] at h
    dsimp [a]
    push_cast
    linear_combination -h

  have hcardI : 2 < Fintype.card (IrreducibleCharacter W₂ ℂ) := by
    letI : IsCyclic W₂ := pti.fixed_cyclic
    rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic]
    exact pti.prime_cycTIhyp.two_lt_card_right
  let e : IrreducibleCharacter W₂ ℂ ≃
      Fin (Fintype.card (IrreducibleCharacter W₂ ℂ)) :=
    Fintype.equivFin _
  obtain ⟨kf, hkf0, hkfj⟩ := Fin.exists_ne_and_ne_of_two_lt
    (e (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
    (e j) hcardI
  let k : IrreducibleCharacter W₂ ℂ := e.symm kf
  have hk0 : k ≠
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) := by
    intro hk
    apply hkf0
    simpa [k] using congrArg e hk
  have hkj : k ≠ j := by
    intro hk
    apply hkfj
    simpa [k] using congrArg e hk

  let muK : ClassFunction M ℂ := pti.primeTIRed isoM k
  have hmuKMem : muK ∈ ftType345InducedFamily10 M := by
    exact reducedColumn_mem_fullDerivedFamily MtypeP k hk0
  have hmuKSpan : muK ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hmuKMem
  have hmuKVirtual : ClassFunction.IsVirtual muK :=
    reducedColumn_isVirtual MtypeP k
  have htauMuKVirtual : ClassFunction.IsVirtual (tau₁ muK) :=
    hcoh.mapsToVirtual muK hmuKSpan

  have hzetaMuK : characterPairing zeta muK = 0 := by
    rw [characterPairing_comm]
    change characterPairing (pti.primeTIRed isoM k) zeta = 0
    rw [pti.primeTIRed_eq_sum]
    change characterPairingRight zeta
      (∑ q : IrreducibleCharacter W₁ ℂ,
        pti.primeTICharacter isoM q k) = 0
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro q hq
    exact hmuZ q k
  have hAlphaMuK : characterPairing alpha muK = 0 := by
    have hjk : j ≠ k := Ne.symm hkj
    have h0k : (IrreducibleCharacter.trivial :
        IrreducibleCharacter W₂ ℂ) ≠ k := Ne.symm hk0
    change characterPairing
      ((pti.primeTICharacter isoM i j -
          (FTtype345_TIsign MtypeP : ℂ) •
            pti.primeTICharacter isoM i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) -
        FTtype345_ratio MtypeP • zeta)
      (pti.primeTIRed isoM k) = 0
    rw [pairing_sub_left, pairing_sub_left,
      characterPairing_smul_left,
      pti.cfdot_prTIirr_red isoM i j k,
      pti.cfdot_prTIirr_red isoM i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) k,
      if_neg hjk, if_neg h0k, characterPairing_smul_left, hzetaMuK]
    ring

  let psi : ClassFunction M ℂ := muK - (d : ℂ) • zetaStar
  have hdZetaStarSpan : (d : ℂ) • zetaStar ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
    simpa only [Nat.cast_smul_eq_nsmul] using
      (AddSubgroup.closure
        (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))).nsmul_mem
          hzetaStarSpan d
  have hpsiSpan : psi ∈ AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
    exact (AddSubgroup.closure
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ))).sub_mem
        hmuKSpan hdZetaStarSpan
  have hpsiOff : psi ∈ ClassFunction.supportedOn (nonidentitySet M) := by
    exact fullDerived_difference_supportedOn_nonidentity
      hmaxM MtypeP notMtype2 zeta hzeta k hk0
  have hpsiFull : psi ∈ ClassFunction.supportedOn
      {x : M | (x : Gamma) ∈ FTsupport M} :=
    fullDerivedClosure_supportedOn_fullSupport hmaxM MtypeP notMtype2
      hpsiSpan hpsiOff
  have hpsiSupport0 : psi ∈
      ClassFunction.supportedOn (ftType345Support0InM M) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    apply ClassFunction.eq_zero_of_mem_supportedOn hpsiFull
    intro hxSupport
    exact hx (FTsupp_sub0 M hxSupport)
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    exact hmuKVirtual.sub (hzetaStarVirtual.natCast_smul d)
  have htauPsiVirtual : ClassFunction.IsVirtual (tau₁ psi) :=
    hcoh.mapsToVirtual psi hpsiSpan
  have hpsiAgree : tau₁ psi = ftType345Tau hmaxM psi :=
    hcoh.agrees psi hpsiSpan hpsiOff
  have hAlphaPsi : characterPairing alpha psi = 0 := by
    simp only [psi]
    rw [pairing_sub_right, characterPairing_smul_right,
      hAlphaMuK, hAlphaZstar]
    ring
  have hAlphaTauPsi : characterPairing alphaTau (tau₁ psi) =
      characterPairing alpha psi := by
    calc
      characterPairing alphaTau (tau₁ psi) =
          starCharacterPairing alphaTau (tau₁ psi) :=
        (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hAlphaTauVirtual htauPsiVirtual).symm
      _ = starCharacterPairing alphaTau (ftType345Tau hmaxM psi) := by
        rw [hpsiAgree]
      _ = starCharacterPairing alpha psi :=
        Dade_isometry (FT_Dade0_hyp M hmaxM) alpha psi
          hAlphaSupport hpsiSupport0
      _ = characterPairing alpha psi :=
        PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hAlphaVirtual hpsiVirtual
  have hAlphaTauMuK : characterPairing alphaTau (tau₁ muK) =
      (((d : ℤ) * a : ℤ) : ℂ) := by
    have h := hAlphaTauPsi
    simp only [psi] at h
    rw [map_sub, map_smul, pairing_sub_right,
      characterPairing_smul_right, hAlphaTauZetaStar, hAlphaPsi] at h
    push_cast
    linear_combination h

  obtain ⟨alphaV, halphaV⟩ := hAlphaTauVirtual
  obtain ⟨muV, hmuV⟩ := htauMuKVirtual
  have hcoeffCast : ((coeffDot alphaV muV : ℤ) : ℂ) =
      (((d : ℤ) * a : ℤ) : ℂ) := by
    calc
      ((coeffDot alphaV muV : ℤ) : ℂ) =
          characterPairing (VirtualCharacter.realize alphaV)
            (VirtualCharacter.realize muV) :=
        (VirtualCharacter.characterPairing_realize alphaV muV).symm
      _ = characterPairing alphaTau (tau₁ muK) := by
        rw [halphaV, hmuV]
      _ = (((d : ℤ) * a : ℤ) : ℂ) := hAlphaTauMuK
  have hcoeff : coeffDot alphaV muV = (d : ℤ) * a :=
    Int.cast_injective hcoeffCast

  have hnormAlpha : normSq alphaV = (2 : ℤ) + (n : ℤ) ^ 2 := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self, halphaV,
      norm_FTtype345_bridge hmaxM MtypeP notMtype2 zeta hzeta i j hj, hn]
    push_cast
    ring
  have hmuKNorm : characterPairing (tau₁ muK) (tau₁ muK) =
      (Nat.card W₁ : ℂ) := by
    calc
      characterPairing (tau₁ muK) (tau₁ muK) =
          characterPairing muK muK :=
        hcoh.isometry muK hmuKSpan muK hmuKSpan
      _ = (Nat.card W₁ : ℂ) := pti.cfnorm_prTIred isoM k
  have hnormMu : normSq muV = (Nat.card W₁ : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self, hmuV, hmuKNorm]
    push_cast
    rfl
  have hbound0 := coeffDot_sq_le_normSq_mul_normSq alphaV muV
  rw [hcoeff, hnormAlpha, hnormMu] at hbound0

  have hdDvd : d ∣ Nat.card M := by
    simpa only [d, FTtype345_TIirr_degree] using
      (pti.primeTIIndex isoM
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ),
          FTtype345_jOne MtypeP)).finrank_representation_dvd_natCard
  have hdOdd : Odd d := (mFT_odd M).of_dvd_nat hdDvd
  have hdelta : IsSign delta := by
    simpa only [delta, FTtype345_TIsign, ftType345Sign] using
      pti.primeTISign_isSign isoM (FTtype345_jOne MtypeP)
  have hcardC : (Nat.card W₁ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hratioMul :
      (d : ℂ) - (delta : ℂ) = (Nat.card W₁ : ℂ) * (n : ℂ) := by
    calc
      (d : ℂ) - (delta : ℂ) =
          (((d : ℂ) - (delta : ℂ)) / (Nat.card W₁ : ℂ)) *
            (Nat.card W₁ : ℂ) :=
        (div_mul_cancel₀ _ hcardC).symm
      _ = FTtype345_ratio MtypeP * (Nat.card W₁ : ℂ) := rfl
      _ = (n : ℂ) * (Nat.card W₁ : ℂ) := by rw [hn]
      _ = (Nat.card W₁ : ℂ) * (n : ℂ) := mul_comm _ _
  have hrelation : (d : ℤ) =
      delta + (Nat.card W₁ : ℤ) * (n : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    linear_combination hratioMul
  have haZero : a = 0 :=
    type345_coefficient_zero_of_bound
      (Nat.card W₁) d n delta a
      pti.complement_odd_card pti.prime_cycTIhyp.two_lt_card_left
      hdOdd (FTtype345_constants hmaxM MtypeP notMtype2).degree_gt_one
      hdelta hrelation hbound0

  rw [hc, hn]
  have hcNeg : c = -(n : ℤ) := by
    dsimp [a] at haZero
    omega
  exact_mod_cast hcNeg

/-- The specialized bridge formula called `tau_alpha` in the source. -/
theorem ftType345_tau_alpha
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
    ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) =
      (FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP i j -
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) -
        FTtype345_ratio MtypeP • tau₁ zeta := by
  have hreference := bridge_reference_pairing hmaxM MtypeP notMtype2
    zeta hzeta tau₁ hcoh i j hj

  let Sref : Set (ClassFunction M ℂ) :=
    {zeta, ClassFunction.inverseLinear zeta}
  let correction : ClassFunction (⊤ : Subgroup Gamma) ℂ :=
    -(FTtype345_ratio MtypeP • tau₁ zeta)
  let bridgePart : ClassFunction (⊤ : Subgroup Gamma) ℂ :=
    ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) - correction

  have hSref : Sref ⊆
      (↑(ftType345InducedFamily10 M) : Set (ClassFunction M ℂ)) := by
    intro phi hphi
    simp only [Sref, Set.mem_insert_iff, Set.mem_singleton_iff] at hphi
    rcases hphi with rfl | rfl
    · exact hzeta.mem_calS
    · exact inverse_reference_mem_fullDerivedFamily zeta hzeta.mem_calS
  have hcohRef : coherent_with Sref (nonidentitySet M)
      (ftType345Tau hmaxM) tau₁ :=
    subset_coherent_with hSref hcoh
  have hSrefKernel : cfConjC_subset Sref
      (FTtypePKernelLayer (ftType345PrimeDade hmaxM MtypeP)) := by
    refine ⟨fun phi hphi ↦
      fullDerivedFamily_sub_kernelLayer hmaxM MtypeP notMtype2
        (hSref hphi), ?_⟩
    intro phi hphi
    simp only [Sref, Set.mem_insert_iff, Set.mem_singleton_iff] at hphi ⊢
    rcases hphi with rfl | rfl
    · exact Or.inr rfl
    · exact Or.inl (inverseLinear_involutive zeta)
  have hSrefIrr : ∀ phi ∈ Sref,
      IsIrreducibleCharacter M ℂ phi := by
    intro phi hphi
    simp only [Sref, Set.mem_insert_iff, Set.mem_singleton_iff] at hphi
    rcases hphi with rfl | rfl
    · exact hzeta.irreducible
    · exact inverse_irreducible hzeta.irreducible

  have hdecomp :
      ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) =
        bridgePart + correction := by
    dsimp [bridgePart]
    abel
  have hcorrectionEq : correction =
      (-FTtype345_ratio MtypeP) • tau₁ zeta := by
    dsimp [correction]
    module
  have hcorrectionSpan : correction ∈
      AddSubgroup.closure (tau₁ '' Sref) := by
    obtain ⟨n, hn⟩ :=
      (FTtype345_constants hmaxM MtypeP notMtype2).ratio_natural
    simp only [correction]
    rw [hn]
    simpa only [Nat.cast_smul_eq_nsmul, neg_smul] using
      (AddSubgroup.closure (tau₁ '' Sref)).neg_mem
        ((AddSubgroup.closure (tau₁ '' Sref)).nsmul_mem
          (AddSubgroup.subset_closure
            (show tau₁ zeta ∈ tau₁ '' Sref from
              ⟨zeta, Set.mem_insert zeta _, rfl⟩)) n)
  have hcorrectionNorm : characterPairing correction correction =
      FTtype345_ratio MtypeP ^ 2 := by
    have hzetaSpan : zeta ∈ AddSubgroup.closure Sref :=
      AddSubgroup.subset_closure (Set.mem_insert zeta _)
    have hzetaNorm : characterPairing zeta zeta = 1 :=
      IrreducibleCharacter.characterPairing_self
        ⟨zeta, hzeta.irreducible⟩
    rw [hcorrectionEq, characterPairing_smul_left,
      characterPairing_smul_right,
      hcohRef.isometry zeta hzetaSpan zeta hzetaSpan, hzetaNorm]
    ring
  have hcorrectionOrthogonal :
      characterPairing correction bridgePart = 0 := by
    have hzetaSpan : zeta ∈ AddSubgroup.closure Sref :=
      AddSubgroup.subset_closure (Set.mem_insert zeta _)
    have hreference' : characterPairing (tau₁ zeta)
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) =
        -FTtype345_ratio MtypeP := by
      rw [characterPairing_comm, hreference]
    simp only [bridgePart]
    rw [hcorrectionEq, characterPairing_smul_left,
      pairing_sub_right, hreference', characterPairing_smul_right,
      hcohRef.isometry zeta hzetaSpan zeta hzetaSpan,
      IrreducibleCharacter.characterPairing_self
        ⟨zeta, hzeta.irreducible⟩]
    ring

  have hbridge := FTtype345_bridge_coherence hmaxM MtypeP notMtype2
    zeta hzeta Sref tau₁ i j bridgePart correction hcohRef hdecomp
      hSrefKernel hSrefIrr hj hcorrectionSpan hcorrectionOrthogonal
      hcorrectionNorm
  calc
    ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) =
        bridgePart + correction := hdecomp
    _ = (FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP i j -
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) + correction := by
      rw [hbridge]
    _ = (FTtype345_TIsign MtypeP : ℂ) •
          (ftType345Eta hmaxM MtypeP i j -
            ftType345Eta hmaxM MtypeP i
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) -
        FTtype345_ratio MtypeP • tau₁ zeta := by
      dsimp [correction]
      abel

end FTType345CoherenceInternal

end

end Submission.OddOrder.PF
