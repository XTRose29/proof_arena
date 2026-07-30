import Submission.OddOrder.PF.Section10.FTType345Constants

/-!
# Peterfalvi Section 10: support and norm of the type-III--V bridge

This phase constructs the bridge character in Peterfalvi (10.5), proves its
support and virtuality, transports it through the canonical Dade map, and
computes its norm.  The reference character and the numerical constants are
provided by `FTType345Constants`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open FTType345ConstantsInternal
open scoped BigOperators Classical Pointwise IsMulCommutative

variable {Gamma : Type} [Group Gamma] [Fintype Gamma]
variable [IsMinSimpleOddGroup Gamma]
variable {M U W W₁ W₂ : Subgroup Gamma}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance invertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## The bridge -/

/-- The source formula `mu2_ i j - delta *: mu2_ i 0 - n *: zeta`. -/
def FTtype345_bridge
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction M ℂ :=
  ftType345Mu2 MtypeP i j -
      (FTtype345_TIsign MtypeP : ℂ) •
        ftType345Mu2 MtypeP i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
    FTtype345_ratio MtypeP • zeta

private theorem ftType345_irreducible_isVirtual
    {Q : Type} [Group Q]
    (chi : IrreducibleCharacter Q ℂ) :
    ClassFunction.IsVirtual (chi : ClassFunction Q ℂ) := by
  exact ⟨Finsupp.single chi 1, by simp⟩

namespace FTType345SupportNormInternal

/-- A prime-TI rectangle entry is orthogonal to the chosen induced reference
character.  This is also consumed by the next Section 10 phase. -/
theorem ftType345_primeTI_ortho_reference
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (ftType345Mu2 MtypeP i j) zeta = 0 := by
  let K : Subgroup M := ftType345DerivedInM M
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  obtain ⟨theta, _htheta, hzetaInd⟩ :=
    (seqIndC1P (k := ℂ) K).mp hzeta.mem_calS
  have hthetaNe : theta ≠ pti.primeTI_Ires isoM j := by
    intro hthetaEq
    have hzetaRed : zeta = pti.primeTIRed isoM j := by
      calc
        zeta = ClassFunction.induce K
            (theta : ClassFunction K ℂ) := hzetaInd
        _ = ClassFunction.induce K
            (pti.primeTI_Ires isoM j : ClassFunction K ℂ) := by
          rw [hthetaEq]
        _ = pti.primeTIRed isoM j := pti.cfInd_prTIres isoM j
    exact (pti.prTIred_not_irr isoM j) (hzetaRed ▸ hzeta.irreducible)
  rw [hzetaInd, characterPairing_comm,
    ClassFunction.frobeniusReciprocity K,
    pti.cfRes_prTIirr isoM i j,
    IrreducibleCharacter.characterPairing_eq_ite,
    if_neg hthetaNe]

end FTType345SupportNormInternal

private theorem ftType345_bridge_vanishes_on_left
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (x : W₁) :
    FTtype345_bridge MtypeP zeta i j
      ⟨x, MtypeP.1.2.1.1 x.property⟩ = 0 := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let xM : M := ⟨x, MtypeP.1.2.1.1 x.property⟩
  by_cases hx : x = 1
  · subst x
    have hxMOne :
        (⟨(1 : W₁), MtypeP.1.2.1.1 (1 : W₁).property⟩ : M) = 1 := by
      apply Subtype.ext
      rfl
    have hdegree :=
      (FTtype345_constants hmaxM MtypeP notMtype2).degree_constant i j hj
    have hcard : (Nat.card W₁ : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    simp only [FTtype345_bridge, ClassFunction.sub_apply,
      ClassFunction.smul_apply, smul_eq_mul]
    rw [hxMOne, hdegree, pti.prTIirr0_1 isoM i, hzeta.degree]
    simp only [FTtype345_ratio]
    field_simp [hcard]
    ring
  · let xW : W := defW.leftEmbedding x
    letI : IsCyclic W₂ := pti.fixed_cyclic
    have hxW₂ : (x : Gamma) ∉ W₂ := by
      intro hxW₂
      have hxW₂' :
          (((defW.mulEquiv (x, 1) : W) : Gamma)) ∈ W₂ := by
        simpa using hxW₂
      exact hx ((defW.mulEquiv_mem_right_iff (x, 1)).mp hxW₂')
    have hxPrime : xW ∈ primeTISetInW W W₂ :=
      mem_primeTISetInW.mpr hxW₂
    have hvaluej :=
      (pti.primeTICharacterData isoM).restrict_character i j hxPrime
    have hvalue0 :=
      (pti.primeTICharacterData isoM).restrict_character i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
        hxPrime
    have hzetaZero : zeta xM = 0 := by
      let K : Subgroup M := ftType345DerivedInM M
      letI : K.Normal := pti.kernel_normal
      apply ClassFunction.eq_zero_of_mem_supportedOn
        (seqInd_on K hzeta.mem_calS)
      intro hxK
      have hxInter : xM ∈ K ⊓ W₁.subgroupOf M :=
        ⟨hxK, x.property⟩
      have hxMOne : xM = 1 := by
        apply Subgroup.mem_bot.mp
        exact pti.semidirect_complement.disjoint.le_bot hxInter
      exact hx (Subtype.ext
        (congrArg (fun z : M => (z : Gamma)) hxMOne))
    have hsignj :=
      (FTtype345_constants hmaxM MtypeP notMtype2).sign_constant j hj
    have hsignj' : (pti.primeTISign isoM j : ℂ) =
        (FTtype345_TIsign MtypeP : ℂ) := by
      exact_mod_cast hsignj
    have hsign0' :
        (pti.primeTISign isoM
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) : ℂ) =
          1 := by
      exact_mod_cast pti.prTIsign0 isoM
    simp only [FTtype345_bridge, ClassFunction.sub_apply,
      ClassFunction.smul_apply, smul_eq_mul]
    rw [show (⟨x, MtypeP.1.2.1.1 x.property⟩ : M) = xM by rfl,
      hzetaZero, mul_zero, sub_zero]
    change
      pti.primeTICharacter isoM i j xM -
          (FTtype345_TIsign MtypeP : ℂ) *
            pti.primeTICharacter isoM i
              (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
              xM = 0
    have hvaluej' : pti.primeTICharacter isoM i j xM =
        (pti.primeTISign isoM j : ℂ) *
          IrreducibleCharacter.cyclicTICharacter defW i j xW := by
      simpa [xW, xM, PrimeTIHypothesis.primeTICharacter,
        PrimeTIHypothesis.primeTIIndex,
        PrimeTIHypothesis.primeTISign] using hvaluej
    have hvalue0' : pti.primeTICharacter isoM i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) xM =
        (pti.primeTISign isoM
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) : ℂ) *
          IrreducibleCharacter.cyclicTICharacter defW i
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
            xW := by
      simpa [xW, xM, PrimeTIHypothesis.primeTICharacter,
        PrimeTIHypothesis.primeTIIndex,
        PrimeTIHypothesis.primeTISign] using hvalue0
    rw [hvaluej', hvalue0', hsignj', hsign0']
    simp only [xW, IrreducibleCharacter.cyclicTICharacter_leftEmbedding,
      IrreducibleCharacter.apply_one_eq_one_of_isCyclic, mul_one, one_mul]
    ring

private theorem ftType345_piSubgroup_le_normalHall
    {Q : Type} [Group Q] [Finite Q] {pi : Set ℕ}
    {L N : Subgroup Q}
    (hNnormal : N.Normal) (hNHall : IsHall pi N)
    (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcoprime : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hNHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let q : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hqL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have hqIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have hqOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcoprime hqL hqIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp hqOne)

private theorem ftType345_outside_support_isPiComplement
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (x : M)
    (hx : (x : Gamma) ∉ FTsupport0 M) :
    IsPiNumber (primeSupport (Nat.card (derivedWithin M)))ᶜ
      (orderOf (x : Gamma)) := by
  let K : Subgroup M := ftType345DerivedInM M
  have hcardK : Nat.card K = Nat.card (derivedWithin M) :=
    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (TypeSpecInternal.derivedWithin_le16_final M)
  let pi := primeSupport (Nat.card (derivedWithin M))
  change IsPiNumber piᶜ (orderOf (x : Gamma))
  by_cases hxOne : x = 1
  · subst x
    intro p hp hpOne
    exact (hp.not_dvd_one (by simpa using hpOne)).elim
  have hnot1 : FTtype M ≠ 1 :=
    FTtypeP_neq1 M U W W₁ W₂ defW hmaxM MtypeP
  have hgt : 2 < FTtype M := by
    have hrange := FTtype_range M
    omega
  have hFTder : FTder M = derivedWithin M := by
    simp [FTder, ftDerived, hnot1]
  by_cases hxPi : IsPiNumber pi (orderOf (x : Gamma))
  · let pti := ftType345PrimeTI MtypeP
    have hKnormal : K.Normal := pti.kernel_normal
    have hKHall : IsHall pi K := by
      simpa only [pi, hcardK] using isHall_primeSupport K (by
        rw [pti.semidirect_complement.symm.index_eq_card,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          pti.complement_le_group, hcardK]
        exact pti.kernel_complement_card_coprime)
    let A : Subgroup M := Subgroup.zpowers x
    have horderX : orderOf x = orderOf (x : Gamma) :=
      (orderOf_injective M.subtype M.subtype_injective x).symm
    have hApi : IsPiNumber pi (Nat.card A) := by
      simpa only [A, Nat.card_zpowers, horderX] using hxPi
    have hAK : A ≤ K :=
      ftType345_piSubgroup_le_normalHall hKnormal hKHall hApi
    have hxK : x ∈ K := hAK (Subgroup.mem_zpowers x)
    apply False.elim
    apply hx
    exact FTsupp_sub0 M (by
      apply FTsupp1_sub hmaxM
      rw [FTsupp1_type_gt2 M hgt]
      exact ⟨hxK, fun hxAmbient ↦
        hxOne (Subtype.ext hxAmbient)⟩)
  · by_contra hxCompl
    apply hx
    unfold FTsupport0 ftSupport0
    dsimp only
    right
    refine ⟨x.property, ?_, ?_⟩
    · simpa [pi, hFTder] using hxPi
    · simpa [pi, hFTder] using hxCompl

private theorem ftType345_outside_support_conjugate_left
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (x : M)
    (hx : (x : Gamma) ∉ FTsupport0 M) :
    ∃ y : M, ∃ w : W₁,
      y⁻¹ * x * y = ⟨w, MtypeP.1.2.1.1 w.property⟩ := by
  let K : Subgroup M := ftType345DerivedInM M
  let C : Subgroup M := W₁.subgroupOf M
  let pi := primeSupport (Nat.card (derivedWithin M))
  let pti := ftType345PrimeTI MtypeP
  have hcardK : Nat.card K = Nat.card (derivedWithin M) :=
    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (TypeSpecInternal.derivedWithin_le16_final M)
  have hKdecomp : K.IsComplement' C := pti.semidirect_complement
  have hKHall : IsHall pi K := by
    simpa only [pi, hcardK] using isHall_primeSupport K (by
      rw [hKdecomp.symm.index_eq_card,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          pti.complement_le_group, hcardK]
      exact pti.kernel_complement_card_coprime)
  have hxPi :=
    ftType345_outside_support_isPiComplement
      hmaxM MtypeP notMtype2 x hx
  let A : Subgroup M := Subgroup.zpowers x
  have horderX : orderOf x = orderOf (x : Gamma) :=
    (orderOf_injective M.subtype M.subtype_injective x).symm
  have hApi : IsPiNumber piᶜ (Nat.card A) := by
    simpa only [A, Nat.card_zpowers, pi, horderX] using hxPi
  letI : IsSolvable M := of_typeP_sol M U W W₁ W₂ defW MtypeP
  obtain ⟨C', hC'decomp, hAC'⟩ :=
    exists_right_complement_ge_of_coprime
      (N := K) (A := A) hKHall.coprime_card_index
        (hKHall.isPiNumber_card.coprime_compl hApi)
  obtain ⟨y, hy⟩ :=
    Subgroup.solvable_complement_conjugacy
      hKHall.coprime_card_index hKdecomp hC'decomp
  have hxC' : x ∈ C' := hAC' (Subgroup.mem_zpowers x)
  rw [hy] at hxC'
  rcases hxC' with ⟨v, hvC, hvx⟩
  let w : W₁ := ⟨(v : M), hvC⟩
  refine ⟨(y : M), w, ?_⟩
  calc
    (y : M)⁻¹ * x * (y : M) = v := by
      rw [← hvx]
      change (y : M)⁻¹ * ((y : M) * v * (y : M)⁻¹) * (y : M) = v
      group
    _ = ⟨w, MtypeP.1.2.1.1 w.property⟩ := by
      apply Subtype.ext
      rfl

/-! ## Support and virtuality -/

/-- `PFsection10.v: supp_FTtype345_bridge`, the first part of (10.5). -/
theorem supp_FTtype345_bridge
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    FTtype345_bridge MtypeP zeta i j ∈
      ClassFunction.supportedOn (ftType345Support0InM M) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  obtain ⟨y, w, hxy⟩ :=
    ftType345_outside_support_conjugate_left
      hmaxM MtypeP notMtype2 x hx
  rw [← ClassFunction.conj_apply
      (FTtype345_bridge MtypeP zeta i j) y⁻¹ x]
  simpa [hxy] using
    ftType345_bridge_vanishes_on_left hmaxM MtypeP notMtype2
      zeta hzeta i j hj w

/-- `PFsection10.v: vchar_FTtype345_bridge`. -/
theorem vchar_FTtype345_bridge
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (FTtype345_bridge MtypeP zeta i j) := by
  obtain ⟨n, hn⟩ :=
    (FTtype345_constants hmaxM MtypeP notMtype2).ratio_natural
  have hmu : ClassFunction.IsVirtual (ftType345Mu2 MtypeP i j) :=
    ftType345_irreducible_isVirtual
      ((ftType345PrimeTI MtypeP).primeTIIndex
        (ftType345IsoM MtypeP) (i, j))
  have hmu0 : ClassFunction.IsVirtual
      (ftType345Mu2 MtypeP i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) :=
    ftType345_irreducible_isVirtual
      ((ftType345PrimeTI MtypeP).primeTIIndex
        (ftType345IsoM MtypeP)
        (i, IrreducibleCharacter.trivial))
  have hz : ClassFunction.IsVirtual zeta :=
    ftType345_irreducible_isVirtual ⟨zeta, hzeta.irreducible⟩
  have hsigned : ClassFunction.IsVirtual
      ((FTtype345_TIsign MtypeP : ℂ) •
        ftType345Mu2 MtypeP i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) := by
    rcases (ftType345PrimeTI MtypeP).primeTISign_isSign
      (ftType345IsoM MtypeP) (FTtype345_jOne MtypeP) with hs | hs
    · simpa [FTtype345_TIsign, ftType345Sign, hs] using hmu0
    · have hneg :
          (FTtype345_TIsign MtypeP : ℂ) •
              ftType345Mu2 MtypeP i
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ) =
            -ftType345Mu2 MtypeP i
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ) := by
        ext x
        simp [FTtype345_TIsign, ftType345Sign, hs,
          ClassFunction.smul_apply]
      rw [hneg]
      exact hmu0.neg
  rw [FTtype345_bridge, hn]
  exact (hmu.sub hsigned).sub (hz.natCast_smul n)

/-- `PFsection10.v: vchar_Dade_FTtype345_bridge`. -/
theorem vchar_Dade_FTtype345_bridge
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ClassFunction.IsVirtual
      (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) := by
  obtain ⟨alpha, halpha⟩ :=
    vchar_FTtype345_bridge hmaxM MtypeP notMtype2 zeta hzeta i j
  obtain ⟨beta, hbeta, _⟩ :=
    (Dade_Zisometry (FT_Dade0_hyp M hmaxM)).2 alpha
      (by
        rw [halpha]
        exact supp_FTtype345_bridge hmaxM MtypeP notMtype2
          zeta hzeta i j hj)
  exact ⟨beta, by
    simpa [halpha, ftType345Tau] using hbeta.symm⟩

private theorem ftType345_pairing_sub_left
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingLeft (a - b) c = _
  exact map_sub (characterPairingRight c) a b

private theorem ftType345_pairing_sub_right
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingRight (b - c) a = _
  exact map_sub (characterPairingLeft a) b c

private theorem ftType345_bridge_norm_source
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    characterPairing (FTtype345_bridge MtypeP zeta i j)
        (FTtype345_bridge MtypeP zeta i j) =
      2 + FTtype345_ratio MtypeP ^ 2 := by
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  have hmu : characterPairing
      (ftType345Mu2 MtypeP i j) (ftType345Mu2 MtypeP i j) = 1 :=
    IrreducibleCharacter.characterPairing_self
      (pti.primeTIIndex isoM (i, j))
  have hmu0 : characterPairing
      (ftType345Mu2 MtypeP i IrreducibleCharacter.trivial)
      (ftType345Mu2 MtypeP i IrreducibleCharacter.trivial) = 1 :=
    IrreducibleCharacter.characterPairing_self
      (pti.primeTIIndex isoM (i, IrreducibleCharacter.trivial))
  have hmuMu0 : characterPairing
      (ftType345Mu2 MtypeP i j)
      (ftType345Mu2 MtypeP i IrreducibleCharacter.trivial) = 0 := by
    change characterPairing
      (pti.primeTIIndex isoM (i, j) : ClassFunction M ℂ)
      (pti.primeTIIndex isoM (i, IrreducibleCharacter.trivial) :
        ClassFunction M ℂ) = 0
    rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg]
    intro heq
    exact hj (congrArg Prod.snd ((pti.primeTIirr_spec isoM).1 heq))
  have hmu0Mu : characterPairing
      (ftType345Mu2 MtypeP i IrreducibleCharacter.trivial)
      (ftType345Mu2 MtypeP i j) = 0 := by
    rw [characterPairing_comm, hmuMu0]
  have hmuZ : characterPairing (ftType345Mu2 MtypeP i j) zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i j
  have hmu0Z : characterPairing
      (ftType345Mu2 MtypeP i IrreducibleCharacter.trivial) zeta = 0 :=
    FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      MtypeP zeta hzeta i IrreducibleCharacter.trivial
  have hzMu : characterPairing zeta (ftType345Mu2 MtypeP i j) = 0 := by
    rw [characterPairing_comm, hmuZ]
  have hzMu0 : characterPairing zeta
      (ftType345Mu2 MtypeP i IrreducibleCharacter.trivial) = 0 := by
    rw [characterPairing_comm, hmu0Z]
  have hzNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self ⟨zeta, hzeta.irreducible⟩
  have hsignSq : ((FTtype345_TIsign MtypeP : ℂ) ^ 2) = 1 := by
    rcases pti.primeTISign_isSign isoM (FTtype345_jOne MtypeP) with hs | hs
    · have hs' : FTtype345_TIsign MtypeP = 1 := by
        simpa [FTtype345_TIsign, ftType345Sign] using hs
      rw [hs']
      norm_num
    · have hs' : FTtype345_TIsign MtypeP = -1 := by
        simpa [FTtype345_TIsign, ftType345Sign] using hs
      rw [hs']
      norm_num
  simp only [FTtype345_bridge, ftType345_pairing_sub_left,
    ftType345_pairing_sub_right, characterPairing_smul_left,
    characterPairing_smul_right, hmu, hmu0, hmuMu0, hmu0Mu,
    hmuZ, hmu0Z, hzMu, hzMu0, hzNorm]
  linear_combination hsignSq

/-- `PFsection10.v: norm_FTtype345_bridge`. -/
theorem norm_FTtype345_bridge
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    characterPairing
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j))
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) =
      2 + FTtype345_ratio MtypeP ^ 2 := by
  have hsourceVirtual :=
    vchar_FTtype345_bridge hmaxM MtypeP notMtype2 zeta hzeta i j
  have htargetVirtual :=
    vchar_Dade_FTtype345_bridge hmaxM MtypeP notMtype2
      zeta hzeta i j hj
  have hsupp := supp_FTtype345_bridge hmaxM MtypeP notMtype2
    zeta hzeta i j hj
  calc
    characterPairing
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j))
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) =
      starCharacterPairing
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j))
        (ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j)) :=
      (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        htargetVirtual htargetVirtual).symm
    _ = starCharacterPairing (FTtype345_bridge MtypeP zeta i j)
        (FTtype345_bridge MtypeP zeta i j) :=
      Dade_isometry (FT_Dade0_hyp M hmaxM)
        (FTtype345_bridge MtypeP zeta i j)
        (FTtype345_bridge MtypeP zeta i j) hsupp hsupp
    _ = characterPairing (FTtype345_bridge MtypeP zeta i j)
        (FTtype345_bridge MtypeP zeta i j) :=
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hsourceVirtual hsourceVirtual
    _ = 2 + FTtype345_ratio MtypeP ^ 2 :=
      ftType345_bridge_norm_source hmaxM MtypeP notMtype2
        zeta hzeta i j hj

namespace FTType345SupportNormInternal

/-- On the cyclic-TI set, the Dade image of the bridge is the signed
difference of the corresponding ambient cyclic-TI characters. -/
theorem ftType345_Dade_bridge_value_on_cyclicTI
    (hmaxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype2 : FTtype M ≠ 2)
    (zeta : ClassFunction M ℂ)
    (hzeta : FTType345ReferenceChoice M W₁ zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (w : W) (hw : w ∈ cyclicTISetInW W W₁ W₂) :
    Dade (FT_Dade0_hyp M hmaxM)
        (FTtype345_bridge MtypeP zeta i j)
        ⟨w, (FT_prDade_hyp defW hmaxM MtypeP).prDade_cycTI.le_group
          w.property⟩ =
      ((FTtype345_TIsign MtypeP : ℂ) •
        (((FT_prDade_hyp defW hmaxM MtypeP).prDade_cycTI.cyclicTIIsometryData).cyclicTIImage
            (i, j) -
          ((FT_prDade_hyp defW hmaxM MtypeP).prDade_cycTI.cyclicTIIsometryData).cyclicTIImage
              (i, IrreducibleCharacter.trivial)))
        ⟨w, (FT_prDade_hyp defW hmaxM MtypeP).prDade_cycTI.le_group
          w.property⟩ := by
  let pd := ftType345PrimeDade hmaxM MtypeP
  let pti := ftType345PrimeTI MtypeP
  let isoM := ftType345IsoM MtypeP
  let isoG := ftType345IsoG hmaxM MtypeP
  let wM : M := ⟨w, pti.directProduct_le_group w.property⟩
  let wG : (⊤ : Subgroup Gamma) :=
    ⟨w, pd.prDade_cycTI.le_group w.property⟩
  have hwAmbient : (w : Gamma) ∈ cyclicTISet W W₁ W₂ := hw
  have hwClass : (w : Gamma) ∈
      classSupportWithin M (cyclicTISet W W₁ W₂) := by
    exact ⟨(w : Gamma), hwAmbient, 1, M.one_mem, by simp⟩
  have hwA₀ : (w : Gamma) ∈ FTsupport0 M := by
    rw [FTtypeP_supp0_def defW hmaxM MtypeP]
    exact Or.inr hwClass
  have hDade := Dade_id (FT_Dade0_hyp M hmaxM)
    (FTtype345_bridge MtypeP zeta i j) hwA₀
  have hwPrime : w ∈ primeTISetInW W W₂ :=
    pti.cyclicTISetInW_subset_primeTISetInW hw
  have hmuj :=
    (pti.primeTICharacterData isoM).restrict_character i j hwPrime
  have hmu0 :=
    (pti.primeTICharacterData isoM).restrict_character i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
      hwPrime
  have hetaj := isoG.restrict
    (IrreducibleCharacter.cyclicTICharacter defW i j :
      ClassFunction W ℂ) hw
  have heta0 := isoG.restrict
    (IrreducibleCharacter.cyclicTICharacter defW i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :
      ClassFunction W ℂ) hw
  have hwNotK : (w : Gamma) ∉ derivedWithin M :=
    pd.prDade_supp_disjoint hw
  have hzetaZero : zeta wM = 0 := by
    let K : Subgroup M := ftType345DerivedInM M
    letI : K.Normal := pti.kernel_normal
    apply ClassFunction.eq_zero_of_mem_supportedOn
      (seqInd_on K hzeta.mem_calS)
    intro hwK
    exact hwNotK hwK
  have hsign :=
    (FTtype345_constants hmaxM MtypeP notMtype2).sign_constant j hj
  have hsign0 : ftType345Sign MtypeP
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) = 1 := by
    simpa [ftType345Sign] using pti.prTIsign0 isoM
  have hmuj' : ftType345Mu2 MtypeP i j wM =
      (ftType345Sign MtypeP j : ℂ) *
        IrreducibleCharacter.cyclicTICharacter defW i j w := by
    simpa [ftType345Mu2, ftType345Sign, wM,
      PrimeTIHypothesis.primeTICharacter,
      PrimeTIHypothesis.primeTIIndex,
      PrimeTIHypothesis.primeTISign] using hmuj
  have hmu0' : ftType345Mu2 MtypeP i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) wM =
      (ftType345Sign MtypeP
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) : ℂ) *
        IrreducibleCharacter.cyclicTICharacter defW i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) w := by
    simpa [ftType345Mu2, ftType345Sign, wM,
      PrimeTIHypothesis.primeTICharacter,
      PrimeTIHypothesis.primeTIIndex,
      PrimeTIHypothesis.primeTISign] using hmu0
  have hetaj' : ftType345Eta hmaxM MtypeP i j wG =
      IrreducibleCharacter.cyclicTICharacter defW i j w := by
    simpa [ftType345Eta, wG, CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using hetaj
  have heta0' : ftType345Eta hmaxM MtypeP i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) wG =
      IrreducibleCharacter.cyclicTICharacter defW i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) w := by
    simpa [ftType345Eta, wG, CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using heta0
  change ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) wG =
    ((FTtype345_TIsign MtypeP : ℂ) •
      (ftType345Eta hmaxM MtypeP i j -
        ftType345Eta hmaxM MtypeP i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))) wG
  rw [show ftType345Tau hmaxM (FTtype345_bridge MtypeP zeta i j) wG =
      FTtype345_bridge MtypeP zeta i j wM by
        simpa [ftType345Tau, wG, wM] using hDade]
  simp only [FTtype345_bridge, ClassFunction.sub_apply,
    ClassFunction.smul_apply, smul_eq_mul]
  rw [hmuj', hmu0', hzetaZero, mul_zero, sub_zero,
    hsign, hsign0, hetaj', heta0']
  ring

end FTType345SupportNormInternal

end


end Submission.OddOrder.PF
