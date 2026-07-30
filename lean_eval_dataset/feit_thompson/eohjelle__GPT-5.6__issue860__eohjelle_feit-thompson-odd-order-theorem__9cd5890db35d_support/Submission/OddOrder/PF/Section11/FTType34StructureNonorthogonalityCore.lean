import Submission.OddOrder.PF.Section04.PrimeTIDadeDoubleSubtraction
import Submission.OddOrder.PF.Section11.FTType34StructureInfrastructure

/-!
# Peterfalvi (11.8): coefficient core

This phase proves the S1 count and the three constants, proves the
index-independence of Peterfalvi's `beta`, isolates the integral
coefficient/norm argument, and gives the balancing identity used for
`tau_theta`.
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

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {M U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftType34NonorthogonalityCoreFintypeOfFinite
    (X : Type) [Finite X] : Fintype X :=
  Fintype.ofFinite X

local instance middleInvertibleNatCardComplex
    {Q : Type} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private noncomputable abbrev etaTopMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction (⊤ : Subgroup G) ℂ :=
  ftType345Eta base.maxM base.MtypeP i j

private noncomputable abbrev muMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction M ℂ :=
  base.primeTI.primeTIRed base.isoM j

private noncomputable abbrev alphaMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction M ℂ :=
  FTtype345_bridge base.MtypeP zeta i j

private noncomputable def etaColumnTopMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction (⊤ : Subgroup G) ℂ :=
  ∑ i : IrreducibleCharacter W₁ ℂ, etaTopMiddle base i j

private noncomputable def betaMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (tau1 : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (zeta : ClassFunction M ℂ)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction (⊤ : Subgroup G) ℂ :=
  ftType345Tau base.maxM (alphaMiddle base zeta i j) -
      (etaTopMiddle base i j - etaTopMiddle base i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) +
    FTtype345_ratio base.MtypeP • tau1 zeta

private theorem pairingSubLeftMiddle
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingLeft (a - b) c = _
  exact map_sub (characterPairingRight c) a b

private theorem pairingSubRightMiddle
    {Q : Type} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingRight (b - c) a = _
  exact map_sub (characterPairingLeft a) b c

private theorem directProductCardMiddle
    {A B K : Subgroup G} (h : IsInternalDirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.left_le,
    MathlibSupport.natCard_subgroupOf_eq h.right_le] using
      h.complement.card_mul

private theorem semidirectProductCardMiddle
    {A B K : Subgroup G} (h : IsInternalSemidirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [MathlibSupport.natCard_subgroupOf_eq h.1,
    MathlibSupport.natCard_subgroupOf_eq h.2.1] using
      h.2.2.2.card_mul

private theorem directProductSupEqMiddle
    {A B K : Subgroup G} (h : IsInternalDirectProductIn A B K) :
    A ⊔ B = K := by
  apply le_antisymm (sup_le h.left_le h.right_le)
  intro x hx
  obtain ⟨⟨a, b⟩, hab⟩ := h.complement.2 ⟨x, hx⟩
  have habG : (a : G) * (b : G) = x := congrArg Subtype.val hab
  rw [← habG]
  exact Subgroup.mul_mem_sup a.property b.property

private theorem ftType34HCDirectMiddle
    (base : FTType34Base M U W W₁ W₂ defW) :
    IsInternalDirectProductIn base.H base.C base.HC := by
  have h :=
    (typeP_context M U W W₁ W₂ defW base.MtypeP).fitting_decomposition
  simpa only [directProductSupEqMiddle h] using h

private theorem ftType34HCInHUIndexMiddle
    (base : FTType34Base M U W W₁ W₂ defW) :
    base.HCInHU.index = base.u := by
  have hHCcard := directProductCardMiddle (ftType34HCDirectMiddle base)
  have hHUcard :=
    semidirectProductCardMiddle base.fcore_complement_decomposition
  have huCard : base.u * Nat.card base.C = Nat.card U := by
    change base.CInU.index * Nat.card base.C = Nat.card U
    simpa only [MathlibSupport.natCard_subgroupOf_eq base.C_le_U] using
      base.CInU.index_mul_card
  have hrel : base.HC.relIndex base.HU = base.u := by
    apply Nat.mul_right_cancel
      (Nat.mul_pos
        (show 0 < Nat.card base.H from Nat.card_pos)
        (show 0 < Nat.card base.C from Nat.card_pos))
    calc
      base.HC.relIndex base.HU *
          (Nat.card base.H * Nat.card base.C) =
          base.HC.relIndex base.HU * Nat.card base.HC := by
            rw [hHCcard]
      _ = Nat.card base.HU := by
        change (base.HC.subgroupOf base.HU).index * Nat.card base.HC =
          Nat.card base.HU
        simpa only [MathlibSupport.natCard_subgroupOf_eq base.HC_le_HU] using
          (base.HC.subgroupOf base.HU).index_mul_card
      _ = Nat.card base.H * Nat.card U := hHUcard.symm
      _ = Nat.card base.H * (base.u * Nat.card base.C) := by
        rw [huCard]
      _ = base.u * (Nat.card base.H * Nat.card base.C) := by
        ac_rfl
  change (base.HC.subgroupOf M).relIndex base.HUInM = base.u
  rw [Subgroup.relIndex_subgroupOf base.HU_le_M, hrel]

private theorem secondDerivedInMNormalMiddle
    (M : Subgroup G) :
    ((secondDerivedWithin M).subgroupOf M).Normal := by
  let K : Subgroup M := (derivedWithin M).subgroupOf M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  have hsecond :
      (secondDerivedWithin M).subgroupOf M =
        (_root_.commutator K).map K.subtype := by
    have hderM : derivedWithin M ≤ M :=
      TypeSpecInternal.derivedWithin_le16_final M
    change (derivedWithin (derivedWithin M)).subgroupOf M =
      (_root_.commutator ((derivedWithin M).subgroupOf M)).map
        ((derivedWithin M).subgroupOf M).subtype
    rw [show derivedWithin (derivedWithin M) =
        ⁅derivedWithin M, derivedWithin M⁆ by
      exact (derivedWithin M).map_subtype_commutator]
    rw [subgroupOf_commutator_eq hderM hderM]
    exact ((derivedWithin M).subgroupOf M).map_subtype_commutator.symm
  rw [hsecond]
  infer_instance

private theorem ftType34S1CardMulQMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (hirr : ∀ zeta ∈ ftType34S1 base,
      IsIrreducibleCharacter M ℂ zeta)
    (hdegree : ∀ zeta ∈ ftType34S1 base,
      zeta 1 = (base.q : ℂ)) :
    (ftType34S1 base).card * base.q = base.u - 1 := by
  letI : base.HUInM.Normal := TypeSpecInternal.derivedWithin_normal16 M
  letI :
      ((base.HCInHU.map base.HUInM.subtype : Subgroup M)).Normal := by
    rw [Subgroup.map_subgroupOf_eq_of_le
      (Subgroup.subgroupOf_mono M base.HC_le_HU)]
    rw [← FTtype34_der2 base]
    exact secondDerivedInMNormalMiddle M
  have hsumLeft :
      (∑ phi ∈ ftType34S1 base,
          phi 1 ^ 2 / characterPairing phi phi) =
        ((ftType34S1 base).card : ℂ) * (base.q : ℂ) ^ 2 := by
    calc
      (∑ phi ∈ ftType34S1 base,
          phi 1 ^ 2 / characterPairing phi phi) =
          ∑ _phi ∈ ftType34S1 base, (base.q : ℂ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro phi hphi
        rw [hdegree phi hphi,
          IrreducibleCharacter.characterPairing_self ⟨phi, hirr phi hphi⟩]
        simp
      _ = ((ftType34S1 base).card : ℂ) * (base.q : ℂ) ^ 2 := by
        simp
  have hsum := sum_seqIndD_square (k := ℂ) base.HUInM
    (⊤ : Subgroup base.HUInM) base.HCInHU le_top
  have hcomplex :
      ((ftType34S1 base).card : ℂ) * (base.q : ℂ) ^ 2 =
        (base.q : ℂ) * ((base.u : ℂ) - 1) := by
    calc
      ((ftType34S1 base).card : ℂ) * (base.q : ℂ) ^ 2 =
          ∑ phi ∈ ftType34S1 base,
            phi 1 ^ 2 / characterPairing phi phi := hsumLeft.symm
      _ = (base.HUInM.index : ℂ) *
          (((⊤ : Subgroup base.HUInM).index : ℂ) *
            (((base.HCInHU.relIndex
              (⊤ : Subgroup base.HUInM) : ℕ) : ℂ) - 1)) := hsum
      _ = (base.q : ℂ) * ((base.u : ℂ) - 1) := by
        rw [Subgroup.index_top, Subgroup.relIndex_top_right,
          ftType34HCInHUIndexMiddle base,
          FTType34StructureInternal.ftType34_HUInM_index_eq_q11 base]
        norm_num
  have huPos : 0 < base.u :=
    Nat.pos_of_ne_zero base.CInU.index_ne_zero_of_finite
  have hnat :
      (ftType34S1 base).card * base.q ^ 2 =
        base.q * (base.u - 1) := by
    apply Nat.cast_injective (R := ℂ)
    rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_mul,
      Nat.cast_sub huPos, Nat.cast_one]
    exact hcomplex
  apply Nat.mul_right_cancel base.q_prime.pos
  calc
    (ftType34S1 base).card * base.q * base.q =
        (ftType34S1 base).card * base.q ^ 2 := by ring
    _ = base.q * (base.u - 1) := hnat
    _ = (base.u - 1) * base.q := Nat.mul_comm _ _

private theorem ftType34ConstantsMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (hS1Card : (ftType34S1 base).card * base.q = base.u - 1)
    (hmuDegree : ∀ j : IrreducibleCharacter W₂ ℂ,
      j ≠ IrreducibleCharacter.trivial →
        muMiddle base j 1 = ((base.q * base.u : ℕ) : ℂ)) :
    FTtype345_TIirr_degree base.MtypeP = base.u ∧
      FTtype345_TIsign base.MtypeP = 1 ∧
      FTtype345_ratio base.MtypeP = ((ftType34S1 base).card : ℂ) := by
  let pti := base.primeTI
  let jOne := FTtype345_jOne base.MtypeP
  have hjOne : jOne ≠
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :=
    FTtype345_jOne_ne_trivial base.MtypeP
  let constants := FTtype345_constants base.maxM base.MtypeP base.notMtype2
  have hqC : (base.q : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr base.q_prime.ne_zero
  have hd : FTtype345_TIirr_degree base.MtypeP = base.u := by
    apply Nat.cast_injective (R := ℂ)
    apply mul_left_cancel₀ hqC
    calc
      (base.q : ℂ) * (FTtype345_TIirr_degree base.MtypeP : ℂ) =
          muMiddle base jOne 1 := by
        rw [pti.prTIred_1 base.isoM jOne,
          constants.degree_constant
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
            jOne hjOne]
      _ = (base.q : ℂ) * (base.u : ℂ) := by
        simpa only [Nat.cast_mul] using hmuDegree jOne hjOne
  obtain ⟨r, hr⟩ := constants.ratio_natural
  let delta := FTtype345_TIsign base.MtypeP
  have hratioMul :
      (FTtype345_TIirr_degree base.MtypeP : ℂ) - (delta : ℂ) =
        (base.q : ℂ) * (r : ℂ) := by
    have hqCard : Nat.card W₁ = base.q := rfl
    calc
      (FTtype345_TIirr_degree base.MtypeP : ℂ) - (delta : ℂ) =
          FTtype345_ratio base.MtypeP * (Nat.card W₁ : ℂ) := by
        rw [FTtype345_ratio]
        exact (div_mul_cancel₀ _
          (Nat.cast_ne_zero.mpr Nat.card_pos.ne')).symm
      _ = (r : ℂ) * (base.q : ℂ) := by
        rw [hr, hqCard]
      _ = (base.q : ℂ) * (r : ℂ) := mul_comm _ _
  have hrelation :
      (FTtype345_TIirr_degree base.MtypeP : ℤ) =
        delta + (base.q : ℤ) * (r : ℤ) := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    simpa only [add_comm] using (sub_eq_iff_eq_add.mp hratioMul)
  have huPos : 0 < base.u :=
    Nat.pos_of_ne_zero base.CInU.index_ne_zero_of_finite
  have huEq : base.u = (ftType34S1 base).card * base.q + 1 := by
    omega
  have hsign : IsSign delta := by
    simpa only [delta, FTtype345_TIsign, ftType345Sign] using
      pti.primeTISign_isSign base.isoM jOne
  have hdelta : delta = 1 := by
    rcases hsign with hplus | hminus
    · exact hplus
    · exfalso
      have hqr : base.q * r = base.u + 1 := by
        have hz : (base.u : ℤ) = -1 + (base.q : ℤ) * (r : ℤ) := by
          rw [hd] at hrelation
          rw [hminus] at hrelation
          omega
        exact_mod_cast (show (base.q : ℤ) * (r : ℤ) =
          (base.u : ℤ) + 1 by omega)
      have hrLarge : (ftType34S1 base).card < r := by
        by_contra hnot
        have hrLe : r ≤ (ftType34S1 base).card := Nat.le_of_not_gt hnot
        have hmul := Nat.mul_le_mul_left base.q hrLe
        nlinarith
      have hstep : (ftType34S1 base).card + 1 ≤ r := by omega
      have hmul := Nat.mul_le_mul_left base.q hstep
      have hqGtTwo : 2 < base.q := by
        have hqThree : 3 ≤ base.q :=
          (Nat.Prime.odd_iff base.q_prime).mp base.q_odd
        omega
      nlinarith
  have hrCard : r = (ftType34S1 base).card := by
    have hqr : base.q * r =
        base.q * (ftType34S1 base).card := by
      have hz : (base.u : ℤ) =
          1 + (base.q : ℤ) * (r : ℤ) := by
        rw [hd] at hrelation
        rw [hdelta] at hrelation
        omega
      have huEqZ : (base.u : ℤ) =
          ((ftType34S1 base).card : ℤ) * (base.q : ℤ) + 1 := by
        exact_mod_cast huEq
      exact_mod_cast (show (base.q : ℤ) * (r : ℤ) =
        (base.q : ℤ) * ((ftType34S1 base).card : ℤ) by
          nlinarith [hz, huEqZ])
    exact Nat.eq_of_mul_eq_mul_left base.q_prime.pos hqr
  refine ⟨hd, hdelta, ?_⟩
  rw [hr, hrCard]

private theorem ftType34BetaIndexIndependentMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (tau1 : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (hdelta : FTtype345_TIsign base.MtypeP = 1)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    betaMiddle base tau1 zeta i j =
      betaMiddle base tau1 zeta
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
        (FTtype345_jOne base.MtypeP) := by
  let jOne := FTtype345_jOne base.MtypeP
  have hjOne : jOne ≠
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :=
    FTtype345_jOne_ne_trivial base.MtypeP
  let constants := FTtype345_constants base.maxM base.MtypeP base.notMtype2
  have hsign (r : IrreducibleCharacter W₂ ℂ)
      (hr : r ≠ IrreducibleCharacter.trivial) :
      base.primeTI.primeTISign base.isoM r = 1 := by
    change ftType345Sign base.MtypeP r = 1
    rw [constants.sign_constant r hr, hdelta]
  have hdegree (a : IrreducibleCharacter W₁ ℂ)
      (r s : IrreducibleCharacter W₂ ℂ)
      (hr : r ≠ IrreducibleCharacter.trivial)
      (hs : s ≠ IrreducibleCharacter.trivial) :
      ftType345Mu2 base.MtypeP a r 1 =
        ftType345Mu2 base.MtypeP a s 1 := by
    rw [constants.degree_constant a r hr,
      constants.degree_constant a s hs]
  have hTauColumn :
      ftType345Tau base.maxM (alphaMiddle base zeta i j) -
          ftType345Tau base.maxM (alphaMiddle base zeta i jOne) =
        etaTopMiddle base i j - etaTopMiddle base i jOne := by
    rw [← map_sub]
    have hAlpha :
        alphaMiddle base zeta i j - alphaMiddle base zeta i jOne =
          ftType345Mu2 base.MtypeP i j -
            ftType345Mu2 base.MtypeP i jOne := by
      simp only [alphaMiddle, FTtype345_bridge]
      module
    rw [hAlpha]
    rw [base.primeDade.prDade_sub_TIirr base.isoM base.isoG
      i j jOne hj hjOne (hdegree i j jOne hj hjOne), hsign j hj]
    simp
  have hTauColumn' :
      ftType345Tau base.maxM (alphaMiddle base zeta i j) =
        (etaTopMiddle base i j - etaTopMiddle base i jOne) +
          ftType345Tau base.maxM (alphaMiddle base zeta i jOne) :=
    sub_eq_iff_eq_add.mp hTauColumn
  have hBetaColumn :
      betaMiddle base tau1 zeta i j =
        betaMiddle base tau1 zeta i jOne := by
    dsimp only [betaMiddle]
    rw [hTauColumn']
    module
  rw [hBetaColumn]
  have hTauRow :
      ftType345Tau base.maxM (alphaMiddle base zeta i jOne) -
          ftType345Tau base.maxM
            (alphaMiddle base zeta IrreducibleCharacter.trivial jOne) =
        (etaTopMiddle base i jOne -
            etaTopMiddle base i IrreducibleCharacter.trivial) -
          (etaTopMiddle base IrreducibleCharacter.trivial jOne -
            etaTopMiddle base IrreducibleCharacter.trivial
              IrreducibleCharacter.trivial) := by
    rw [← map_sub]
    have hAlpha :
        alphaMiddle base zeta i jOne -
            alphaMiddle base zeta IrreducibleCharacter.trivial jOne =
          (base.primeTI.primeTISign base.isoM jOne : ℂ) •
              ftType345Mu2 base.MtypeP i jOne -
            (base.primeTI.primeTISign base.isoM jOne : ℂ) •
              ftType345Mu2 base.MtypeP IrreducibleCharacter.trivial jOne -
            ftType345Mu2 base.MtypeP i IrreducibleCharacter.trivial +
            ftType345Mu2 base.MtypeP IrreducibleCharacter.trivial
              IrreducibleCharacter.trivial := by
      simp only [alphaMiddle, FTtype345_bridge]
      rw [hdelta, hsign jOne hjOne]
      module
    rw [hAlpha]
    rw [base.primeDade.prDade_sub2_TIirr
      base.isoM base.isoG i jOne]
    change
      etaTopMiddle base i jOne -
          etaTopMiddle base IrreducibleCharacter.trivial jOne -
          etaTopMiddle base i IrreducibleCharacter.trivial +
          etaTopMiddle base IrreducibleCharacter.trivial
            IrreducibleCharacter.trivial =
        etaTopMiddle base i jOne -
          etaTopMiddle base i IrreducibleCharacter.trivial -
          (etaTopMiddle base IrreducibleCharacter.trivial jOne -
            etaTopMiddle base IrreducibleCharacter.trivial
              IrreducibleCharacter.trivial)
    module
  have hTauRow' :
      ftType345Tau base.maxM (alphaMiddle base zeta i jOne) =
        ((etaTopMiddle base i jOne -
            etaTopMiddle base i IrreducibleCharacter.trivial) -
          (etaTopMiddle base IrreducibleCharacter.trivial jOne -
            etaTopMiddle base IrreducibleCharacter.trivial
              IrreducibleCharacter.trivial)) +
          ftType345Tau base.maxM
            (alphaMiddle base zeta IrreducibleCharacter.trivial jOne) :=
    sub_eq_iff_eq_add.mp hTauRow
  dsimp only [betaMiddle]
  rw [hTauRow']
  module

private theorem representationCharacterInvEqStarMiddle
    {Q : Type} {V : Type*} [Group Q] [Fintype Q]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ Q V) (g : Q) :
    rho.character g⁻¹ = star (rho.character g) := by
  let n := Nat.card Q
  have hn : n ≠ 0 := Nat.card_pos.ne'
  letI : NeZero n := ⟨hn⟩
  let omega₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have homega₀ : IsPrimitiveRoot omega₀ n := by
    simpa only [omega₀] using Complex.isPrimitiveRoot_exp n hn
  let omega : ℂˣ := Units.mk0 omega₀ (homega₀.ne_zero hn)
  have homega : IsPrimitiveRoot omega n := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [omega] using homega₀
  have homegaNorm : ‖(omega : ℂ)‖ = 1 := by
    simpa [omega] using homega₀.norm'_eq_one hn
  have homegaPow : (omega : ℂ) ^ n = 1 := by
    exact congrArg (fun z : ℂˣ ↦ (z : ℂ)) homega.pow_eq_one
  have hpow : (rho g) ^ n = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hginvPow : g⁻¹ = g ^ (n - 1) := by
    exact inv_eq_of_mul_eq_one_right (by
      rw [mul_pow_sub_one hn, pow_card_eq_one'])
  have hinvPow : rho g⁻¹ = (rho g) ^ (n - 1) := by
    rw [hginvPow, map_pow]
  have hweight (i : ZMod n) :
      (primitiveRootUnitWeight homega i : ℂ) =
        (omega : ℂ) ^ i.val := by
    conv_lhs =>
      rw [← ZMod.natCast_zmod_val i,
        primitiveRootUnitWeight_natCast]
    rfl
  have hweightStar (i : ZMod n) :
      (starRingEnd ℂ) (primitiveRootUnitWeight homega i : ℂ) =
        (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) := by
    let w : ℂ := primitiveRootUnitWeight homega i
    have hwNorm : ‖w‖ = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        norm_pow, homegaNorm, one_pow]
    have hwPow : w ^ n = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        ← pow_mul, Nat.mul_comm, pow_mul, homegaPow, one_pow]
    have hwInv : w⁻¹ = w ^ (n - 1) :=
      inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, hwPow])
    change (starRingEnd ℂ) w = w ^ (n - 1)
    rw [← Complex.inv_eq_conj hwNorm, hwInv]
  have htraceOne :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho g) hpow 1
  have htracePred :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho g) hpow (n - 1)
  simp only [pow_one] at htraceOne
  calc
    rho.character g⁻¹ = LinearMap.trace ℂ V (rho g⁻¹) := rfl
    _ = LinearMap.trace ℂ V ((rho g) ^ (n - 1)) := by rw [hinvPow]
    _ = ∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho g)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) :=
      htracePred
    _ = star (∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho g)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ)) := by
      change _ = (starRingEnd ℂ) (∑ i : ZMod n,
        (Module.finrank ℂ
            (Module.End.eigenspace (rho g)
              (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
          (primitiveRootUnitWeight homega i : ℂ))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_natCast, hweightStar]
    _ = star (LinearMap.trace ℂ V (rho g)) := by rw [htraceOne]
    _ = star (rho.character g) := rfl

private theorem irreducibleCharacterApplyInvEqStarMiddle
    {Q : Type} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) (g : Q) :
    chi g⁻¹ = star (chi g) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representationCharacterInvEqStarMiddle chi.representation.ρ g

private theorem starRealizeApplyEqInverseMiddle
    {Q : Type} [Group Q] [Fintype Q]
    (z : VirtualCharacter Q ℂ) (x : Q) :
    star (VirtualCharacter.realize z x) =
      VirtualCharacter.realize z x⁻¹ := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add chi m z hchi hm ih =>
      rw [VirtualCharacter.realize_add, VirtualCharacter.realize_single]
      change (starRingEnd ℂ) ((m : ℂ) * chi.val x +
          VirtualCharacter.realize z x) =
        (m : ℂ) * chi.val x⁻¹ + VirtualCharacter.realize z x⁻¹
      have hchiStar :=
        (irreducibleCharacterApplyInvEqStarMiddle chi x).symm
      change (starRingEnd ℂ) (chi.val x) = chi.val x⁻¹ at hchiStar
      change (starRingEnd ℂ) (VirtualCharacter.realize z x) =
        VirtualCharacter.realize z x⁻¹ at ih
      rw [map_add, map_mul, map_intCast, ih, hchiStar]

private theorem inverseEqConjOfVirtualMiddle
    {Q : Type} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.inverseLinear phi = cfConjC phi := by
  obtain ⟨z, rfl⟩ := hphi
  ext x
  exact (starRealizeApplyEqInverseMiddle z x).symm

private theorem conjugateIrreducibleEqDualMiddle
    {Q : Type} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    IrreducibleCharacter.mapRingEquiv complexConjugation chi =
      IrreducibleCharacter.dual chi := by
  ext x
  rw [IrreducibleCharacter.mapRingEquiv_apply,
    IrreducibleCharacter.dual_apply]
  change star (chi x) = chi x⁻¹
  exact (irreducibleCharacterApplyInvEqStarMiddle chi x).symm

private theorem cyclicTIImageIsVirtualMiddle
    {Q W W₁ W₂ : Subgroup G}
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

private theorem cfConjCSmulNatMiddle
    {Q : Type} [Group Q]
    (n : ℕ) (phi : ClassFunction Q ℂ) :
    cfConjC ((n : ℂ) • phi) = (n : ℂ) • cfConjC phi := by
  ext x
  simp [cfConjC_apply, ClassFunction.smul_apply]

private theorem cfConjCMuMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    cfConjC (ftType345Mu2 base.MtypeP i j) =
      ftType345Mu2 base.MtypeP
        (IrreducibleCharacter.dual i) (IrreducibleCharacter.dual j) := by
  change cfConjC
      (base.primeTI.primeTIIndex base.isoM (i, j) :
        ClassFunction M ℂ) =
    (base.primeTI.primeTIIndex base.isoM
      (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j) :
        ClassFunction M ℂ)
  rw [cfConjC_irreducible, conjugateIrreducibleEqDualMiddle,
    base.primeTI.primeTIIndex_dual base.isoM]

private theorem cfConjCEtaMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    cfConjC (etaTopMiddle base i j) =
      etaTopMiddle base (IrreducibleCharacter.dual i)
        (IrreducibleCharacter.dual j) := by
  let source : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW i j
  let target : IrreducibleCharacter W ℂ :=
    IrreducibleCharacter.cyclicTICharacter defW
      (IrreducibleCharacter.dual i) (IrreducibleCharacter.dual j)
  have hsourceIrr :
      IrreducibleCharacter.mapRingEquiv complexConjugation source =
        target := by
    calc
      IrreducibleCharacter.mapRingEquiv complexConjugation source =
          IrreducibleCharacter.cyclicTICharacter defW
            (IrreducibleCharacter.mapRingEquiv complexConjugation i)
            (IrreducibleCharacter.mapRingEquiv complexConjugation j) := by
        simpa only [source] using
          (IrreducibleCharacter.cyclicTICharacter_mapRingEquiv
            defW complexConjugation i j).symm
      _ = IrreducibleCharacter.cyclicTICharacter defW
          (IrreducibleCharacter.dual i)
          (IrreducibleCharacter.dual j) := by
        rw [conjugateIrreducibleEqDualMiddle,
          conjugateIrreducibleEqDualMiddle]
      _ = target := rfl
  have hsource :
      ClassFunction.mapRingHom complexConjugation.toRingHom
          (source : ClassFunction W ℂ) =
        (target : ClassFunction W ℂ) := by
    calc
      ClassFunction.mapRingHom complexConjugation.toRingHom
          (source : ClassFunction W ℂ) =
          (IrreducibleCharacter.mapRingEquiv complexConjugation source :
            ClassFunction W ℂ) :=
        ClassFunction.mapRingHom_irreducible complexConjugation source
      _ = (target : ClassFunction W ℂ) :=
        congrArg
          (fun chi : IrreducibleCharacter W ℂ ↦
            (chi : ClassFunction W ℂ)) hsourceIrr
  change ClassFunction.mapRingHom complexConjugation.toRingHom
      (base.isoG.cyclicTIImage (i, j)) =
    base.isoG.cyclicTIImage
      (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j)
  rw [CyclicTIIsometryData.cyclicTIImage,
    CyclicTIIsometryData.cyclicTIImage,
    base.isoG.mapRingEquiv_cyclicTIIsometry]
  exact congrArg base.isoG.linearMap hsource

private theorem characterPairingEtaTopMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (i k : IrreducibleCharacter W₁ ℂ)
    (j ell : IrreducibleCharacter W₂ ℂ) :
    characterPairing (etaTopMiddle base i j) (etaTopMiddle base k ell) =
      if (i, j) = (k, ell) then 1 else 0 := by
  exact base.isoG.characterPairing_cyclicTIImage (i, j) (k, ell)

private theorem characterPairingEtaColumnTopMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (j₀ : IrreducibleCharacter W₂ ℂ)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (etaColumnTopMiddle base j₀) (etaTopMiddle base i j) =
      if j = j₀ then 1 else 0 := by
  classical
  rw [etaColumnTopMiddle]
  change characterPairingRight (etaTopMiddle base i j)
      (∑ k : IrreducibleCharacter W₁ ℂ, etaTopMiddle base k j₀) = _
  rw [map_sum]
  by_cases hj : j = j₀
  · subst j
    rw [if_pos rfl, Finset.sum_eq_single i]
    · change characterPairing (etaTopMiddle base i j₀)
          (etaTopMiddle base i j₀) = 1
      rw [characterPairingEtaTopMiddle, if_pos rfl]
    · intro k _ hki
      change characterPairing (etaTopMiddle base k j₀)
          (etaTopMiddle base i j₀) = 0
      rw [characterPairingEtaTopMiddle, if_neg]
      exact fun h ↦ hki (congrArg Prod.fst h)
    · simp
  · rw [if_neg hj]
    apply Finset.sum_eq_zero
    intro k _
    change characterPairing (etaTopMiddle base k j₀)
        (etaTopMiddle base i j) = 0
    rw [characterPairingEtaTopMiddle, if_neg]
    intro h
    exact hj (congrArg Prod.snd h).symm

private theorem fintypeSumVirtualMiddle
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

private theorem etaColumnTopVirtualMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (etaColumnTopMiddle base j) := by
  rw [etaColumnTopMiddle]
  exact fintypeSumVirtualMiddle _
    (fun i ↦ cyclicTIImageIsVirtualMiddle base.isoG (i, j))

private theorem etaZeroColumnTopRealMiddle
    (base : FTType34Base M U W W₁ W₂ defW) :
    cfReal (etaColumnTopMiddle base
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) := by
  let j₀ : IrreducibleCharacter W₂ ℂ := IrreducibleCharacter.trivial
  have hvirtual := etaColumnTopVirtualMiddle base j₀
  rw [cfReal, inverseEqConjOfVirtualMiddle hvirtual]
  rw [etaColumnTopMiddle, map_sum]
  apply Fintype.sum_equiv IrreducibleCharacter.dualEquiv
  intro i
  change cfConjC (etaTopMiddle base i j₀) =
    etaTopMiddle base (IrreducibleCharacter.dual i) j₀
  simpa only [j₀, IrreducibleCharacter.dual_trivial] using
    cfConjCEtaMiddle base i j₀

private theorem ftType34BetaRealMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base)
    (hzetaRef : FTType345ReferenceChoice M W₁ zeta)
    (tau1 : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (hcoh : coherent_with
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau base.maxM) tau1)
    (hsub : cfConjC_subset
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer base.primeDade))
    (hirr : ∀ xi ∈ ftType34S1 base,
      IsIrreducibleCharacter M ℂ xi)
    (hdelta : FTtype345_TIsign base.MtypeP = 1)
    (hratio : FTtype345_ratio base.MtypeP =
      ((ftType34S1 base).card : ℂ))
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    cfReal (betaMiddle base tau1 zeta i j) := by
  classical
  let zetaStar := ClassFunction.inverseLinear zeta
  have hzetaStar : zetaStar ∈ ftType34S1 base :=
    hsub.2 zeta hzeta
  have hzetaVirtual : ClassFunction.IsVirtual zeta :=
    ⟨Finsupp.single ⟨zeta, hirr zeta hzeta⟩ 1, by simp⟩
  have hzetaConj : cfConjC zeta = zetaStar := by
    exact (inverseEqConjOfVirtualMiddle hzetaVirtual).symm
  have hstarSpan : zetaStar ∈ AddSubgroup.closure
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hzetaStar
  have hzetaSpan : zeta ∈ AddSubgroup.closure
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hzeta
  have hTau1Conj : cfConjC (tau1 zeta) = tau1 zetaStar := by
    let chi : IrreducibleCharacter M ℂ := ⟨zeta, hirr zeta hzeta⟩
    have h := cfConjC_Dade_coherent base.primeDade.prDade_hyp
      base.HUInM (⊤ : Subgroup base.HUInM) base.HCInHU hcoh
      (mFT_odd (⊤ : Subgroup G)) chi hzeta
    have hsource :
        (IrreducibleCharacter.mapRingEquiv complexConjugation chi :
          ClassFunction M ℂ) = zetaStar := by
      calc
        (IrreducibleCharacter.mapRingEquiv complexConjugation chi :
            ClassFunction M ℂ) =
            (IrreducibleCharacter.dual chi : ClassFunction M ℂ) :=
          congrArg
            (fun psi : IrreducibleCharacter M ℂ ↦
              (psi : ClassFunction M ℂ))
            (conjugateIrreducibleEqDualMiddle chi)
        _ = ClassFunction.inverseLinear (chi : ClassFunction M ℂ) :=
          (ClassFunction.inverseLinear_irreducible chi).symm
        _ = zetaStar := rfl
    change cfConjC (tau1 (chi : ClassFunction M ℂ)) = tau1 zetaStar
    calc
      cfConjC (tau1 (chi : ClassFunction M ℂ)) =
          tau1
            (IrreducibleCharacter.mapRingEquiv complexConjugation chi :
              ClassFunction M ℂ) := h
      _ = tau1 zetaStar := congrArg (fun phi ↦ tau1 phi) hsource
  have hAlphaConj (a : IrreducibleCharacter W₁ ℂ)
      (b : IrreducibleCharacter W₂ ℂ) :
      cfConjC (alphaMiddle base zeta a b) =
        alphaMiddle base zetaStar
          (IrreducibleCharacter.dual a)
          (IrreducibleCharacter.dual b) := by
    have hsignSmul (phi : ClassFunction M ℂ) :
        ((FTtype345_TIsign base.MtypeP : ℤ) : ℂ) • phi = phi := by
      rw [hdelta, Int.cast_one]
      exact one_smul ℂ phi
    have hconjSign :
        cfConjC
            (((FTtype345_TIsign base.MtypeP : ℤ) : ℂ) •
              ftType345Mu2 base.MtypeP a
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ)) =
          ((FTtype345_TIsign base.MtypeP : ℤ) : ℂ) •
            ftType345Mu2 base.MtypeP
              (IrreducibleCharacter.dual a)
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ) := by
      calc
        cfConjC
            (((FTtype345_TIsign base.MtypeP : ℤ) : ℂ) •
              ftType345Mu2 base.MtypeP a
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ)) =
            cfConjC
              (ftType345Mu2 base.MtypeP a
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ ℂ)) :=
          congrArg
            (fun phi : ClassFunction M ℂ ↦ cfConjC phi)
            (hsignSmul _)
        _ = ftType345Mu2 base.MtypeP
            (IrreducibleCharacter.dual a)
            (IrreducibleCharacter.dual
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ)) :=
          cfConjCMuMiddle base a IrreducibleCharacter.trivial
        _ = ftType345Mu2 base.MtypeP
            (IrreducibleCharacter.dual a)
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂ ℂ) := by
          rw [IrreducibleCharacter.dual_trivial]
        _ = ((FTtype345_TIsign base.MtypeP : ℤ) : ℂ) •
            ftType345Mu2 base.MtypeP
              (IrreducibleCharacter.dual a)
              (IrreducibleCharacter.trivial :
                IrreducibleCharacter W₂ ℂ) :=
          (hsignSmul _).symm
    have hconjRatio :
        cfConjC (FTtype345_ratio base.MtypeP • zeta) =
          FTtype345_ratio base.MtypeP • zetaStar := by
      rw [hratio,
        cfConjCSmulNatMiddle (ftType34S1 base).card zeta,
        hzetaConj]
    dsimp only [alphaMiddle, FTtype345_bridge]
    rw [map_sub, map_sub, cfConjCMuMiddle base a b,
      hconjSign, hconjRatio]
  have hTauAlphaConj (a : IrreducibleCharacter W₁ ℂ)
      (b : IrreducibleCharacter W₂ ℂ) :
      cfConjC
          (ftType345Tau base.maxM (alphaMiddle base zeta a b)) =
        ftType345Tau base.maxM
          (alphaMiddle base zetaStar
            (IrreducibleCharacter.dual a)
            (IrreducibleCharacter.dual b)) := by
    calc
      cfConjC
          (ftType345Tau base.maxM (alphaMiddle base zeta a b)) =
          ftType345Tau base.maxM
            (cfConjC (alphaMiddle base zeta a b)) :=
        (Dade_conjC base.primeDade.prDade_hyp
          (alphaMiddle base zeta a b)).symm
      _ = _ := by rw [hAlphaConj]
  have hConjBeta :
      cfConjC (betaMiddle base tau1 zeta i j) =
        betaMiddle base tau1 zetaStar
          (IrreducibleCharacter.dual i)
          (IrreducibleCharacter.dual j) := by
    dsimp only [betaMiddle]
    rw [map_add, map_sub, map_sub, hTauAlphaConj,
      cfConjCEtaMiddle, cfConjCEtaMiddle,
      IrreducibleCharacter.dual_trivial, hratio,
      cfConjCSmulNatMiddle, hTau1Conj]
  have hdualJ : IrreducibleCharacter.dual j ≠
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) := by
    intro h
    apply hj
    calc
      j = IrreducibleCharacter.dual (IrreducibleCharacter.dual j) :=
        (IrreducibleCharacter.dual_dual j).symm
      _ = IrreducibleCharacter.dual
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :=
        congrArg
          (fun chi : IrreducibleCharacter W₂ ℂ ↦
            IrreducibleCharacter.dual chi) h
      _ = IrreducibleCharacter.trivial :=
        IrreducibleCharacter.dual_trivial
  have hBetaStarIndices :=
    ftType34BetaIndexIndependentMiddle base zetaStar tau1 hdelta
      (IrreducibleCharacter.dual i) (IrreducibleCharacter.dual j) hdualJ
  have hBetaIndices :=
    ftType34BetaIndexIndependentMiddle base zeta tau1 hdelta i j hj
  let zdiff : ClassFunction M ℂ := zetaStar - zeta
  have hdiffSpan : zdiff ∈ AddSubgroup.closure
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ)) :=
    (AddSubgroup.closure
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))).sub_mem
        hstarSpan hzetaSpan
  have hdiffOff : zdiff ∈
      ClassFunction.supportedOn (nonidentitySet M) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxOne : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp [zdiff, zetaStar]
  have hAgree : tau1 zdiff = ftType345Tau base.maxM zdiff :=
    hcoh.agrees zdiff hdiffSpan hdiffOff
  have hAgreeSub :
      tau1 zetaStar - tau1 zeta =
        ftType345Tau base.maxM zetaStar -
          ftType345Tau base.maxM zeta := by
    simpa only [zdiff, map_sub] using hAgree
  have hTau1Star :
      tau1 zetaStar =
        (ftType345Tau base.maxM zetaStar -
          ftType345Tau base.maxM zeta) + tau1 zeta := by
    calc
      tau1 zetaStar =
          (tau1 zetaStar - tau1 zeta) + tau1 zeta := by abel
      _ = (ftType345Tau base.maxM zetaStar -
          ftType345Tau base.maxM zeta) + tau1 zeta := by
        rw [hAgreeSub]
  have hBetaReference :
      betaMiddle base tau1 zetaStar
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          (FTtype345_jOne base.MtypeP) =
        betaMiddle base tau1 zeta
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          (FTtype345_jOne base.MtypeP) := by
    dsimp only [betaMiddle, alphaMiddle, FTtype345_bridge]
    simp only [hdelta, Int.cast_one, one_smul, hratio,
      map_sub, map_smul]
    rw [hTau1Star]
    module
  have hconj : cfConjC (betaMiddle base tau1 zeta i j) =
      betaMiddle base tau1 zeta i j := by
    calc
      cfConjC (betaMiddle base tau1 zeta i j) =
          betaMiddle base tau1 zetaStar
            (IrreducibleCharacter.dual i)
            (IrreducibleCharacter.dual j) := hConjBeta
      _ = betaMiddle base tau1 zetaStar
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          (FTtype345_jOne base.MtypeP) := hBetaStarIndices
      _ = betaMiddle base tau1 zeta
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          (FTtype345_jOne base.MtypeP) := hBetaReference
      _ = betaMiddle base tau1 zeta i j := hBetaIndices.symm
  have hTauVirtual := vchar_Dade_FTtype345_bridge base.maxM base.MtypeP
    base.notMtype2 zeta hzetaRef i j hj
  have hEtaVirtual : ClassFunction.IsVirtual
      (etaTopMiddle base i j -
        etaTopMiddle base i IrreducibleCharacter.trivial) :=
    (cyclicTIImageIsVirtualMiddle base.isoG (i, j)).sub
      (cyclicTIImageIsVirtualMiddle base.isoG
        (i, IrreducibleCharacter.trivial))
  have hTau1Virtual : ClassFunction.IsVirtual (tau1 zeta) :=
    hcoh.mapsToVirtual zeta hzetaSpan
  have hbetaVirtual : ClassFunction.IsVirtual
      (betaMiddle base tau1 zeta i j) := by
    dsimp only [betaMiddle]
    rw [hratio]
    exact (hTauVirtual.sub hEtaVirtual).add
      (hTau1Virtual.natCast_smul (ftType34S1 base).card)
  rw [cfReal, inverseEqConjOfVirtualMiddle hbetaVirtual, hconj]

private theorem middleEvenCoefficientZeroOrTwo
    (n : ℕ) (a : ℤ) (hn : 0 < n) (ha : Even a)
    (hbound : (n : ℤ) * a * (a - 2) ≤ 2) :
    a = 0 ∨ a = 2 := by
  obtain ⟨b, rfl⟩ := ha
  by_cases hb0 : b = 0
  · exact Or.inl (by simp [hb0])
  by_cases hb1 : b = 1
  · exact Or.inr (by simp [hb1])
  have hbCases : b ≤ -1 ∨ 2 ≤ b := by omega
  exfalso
  rcases hbCases with hbNeg | hbPos
  · have hquad : 2 ≤ b * (b - 1) := by nlinarith
    have hnOne : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith
  · have hquad : 2 ≤ b * (b - 1) := by nlinarith
    have hnOne : (1 : ℤ) ≤ n := by exact_mod_cast hn
    nlinarith

private theorem middleCoefficientZero
    (n : ℕ) (a : ℤ) (hn : 0 < n)
    (haEven : Even a)
    (hbound : (n : ℤ) * a * (a - 2) ≤ 2)
    (hpairA : (a : ℂ) = 0 → a = 0)
    (hcaseTwoImpossible : a = 2 → False) :
    a = 0 := by
  rcases middleEvenCoefficientZeroOrTwo n a hn haEven hbound with ha | ha
  · exact ha
  · exact False.elim (hcaseTwoImpossible ha)

private theorem pairingFinsetSumLeftMiddle
    {Q I : Type} [Group Q] [Fintype Q]
    (s : Finset I) (f : I → ClassFunction Q ℂ)
    (psi : ClassFunction Q ℂ) :
    characterPairing (∑ i ∈ s, f i) psi =
      ∑ i ∈ s, characterPairing (f i) psi := by
  exact map_sum (characterPairingRight psi) (fun i ↦ f i) s

private theorem pairingFinsetSumRightMiddle
    {Q I : Type} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) (s : Finset I)
    (f : I → ClassFunction Q ℂ) :
    characterPairing phi (∑ i ∈ s, f i) =
      ∑ i ∈ s, characterPairing phi (f i) := by
  exact map_sum (characterPairingLeft phi) (fun i ↦ f i) s

private theorem ftType34_characterPairing_eq_ite_core34
    {Q : Type} [Group Q] [Fintype Q]
    (xi psi : ClassFunction Q ℂ)
    (hxi : IsIrreducibleCharacter Q ℂ xi)
    (hpsi : IsIrreducibleCharacter Q ℂ psi) :
    characterPairing xi psi = if xi = psi then 1 else 0 := by
  classical
  by_cases hxiPsi : xi = psi
  · subst psi
    rw [if_pos rfl]
    exact IrreducibleCharacter.characterPairing_self ⟨xi, hxi⟩
  · rw [if_neg hxiPsi]
    exact IrreducibleCharacter.characterPairing_eq_zero
      (chi := ⟨xi, hxi⟩) (psi := ⟨psi, hpsi⟩) (by
        intro h
        exact hxiPsi (congrArg Subtype.val h))

/-!
This is the coefficient/norm half of the `tau_alpha` proof.  The hypotheses
`hYform`, `haEven`, and `hcol0Beta` are exactly the three local outputs of the
preceding projection, reality/parity, and zero-column calculations.  All
remaining norm arithmetic, use of the Section 10 coherence bridge, exclusion
of `a = 2`, and assembly of `tau_alpha` are performed here.
-/
private theorem ftType34TauAlphaFromCoefficientMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base)
    (hzetaRef : FTType345ReferenceChoice M W₁ zeta)
    (tau1 : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (hcoh : coherent_with
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau base.maxM) tau1)
    (hsub : cfConjC_subset
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer base.primeDade))
    (hirr : ∀ xi ∈ ftType34S1 base,
      IsIrreducibleCharacter M ℂ xi)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hd : FTtype345_TIirr_degree base.MtypeP = base.u)
    (hdelta : FTtype345_TIsign base.MtypeP = 1)
    (hratio : FTtype345_ratio base.MtypeP =
      ((ftType34S1 base).card : ℂ))
    (X Y : ClassFunction (⊤ : Subgroup G) ℂ)
    (a : ℤ)
    (hXvirtual : ClassFunction.IsVirtual X)
    (hdecomp :
      ftType345Tau base.maxM (alphaMiddle base zeta i j) = X + Y)
    (hYspan : Y ∈ AddSubgroup.closure
      (tau1 '' (↑(ftType34S1 base) : Set (ClassFunction M ℂ))))
    (hYX : characterPairing Y X = 0)
    (hYform : Y =
      (a : ℂ) •
          (∑ xi ∈ ftType34S1 base, tau1 xi) -
        ((ftType34S1 base).card : ℂ) • tau1 zeta)
    (haEven : Even a)
    (etaZero : ClassFunction (⊤ : Subgroup G) ℂ)
    (hetaZeroTau : ∀ xi ∈ ftType34S1 base,
      characterPairing etaZero (tau1 xi) = 0)
    (hcol0Beta :
      characterPairing etaZero
        (betaMiddle base tau1 zeta i j) = (a : ℂ)) :
    ftType345Tau base.maxM (alphaMiddle base zeta i j) =
      etaTopMiddle base i j -
        etaTopMiddle base i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        FTtype345_ratio base.MtypeP • tau1 zeta := by
  classical
  let S := ftType34S1 base
  let n := S.card
  let sumTau : ClassFunction (⊤ : Subgroup G) ℂ :=
    ∑ xi ∈ S, tau1 xi
  let etaDiff : ClassFunction (⊤ : Subgroup G) ℂ :=
    etaTopMiddle base i j -
      etaTopMiddle base i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  have hnPos : 0 < n := by
    exact Finset.card_pos.mpr ⟨zeta, hzeta⟩
  have hspan (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      xi ∈ AddSubgroup.closure
        (↑S : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hxi
  have hpairTau (xi : ClassFunction M ℂ) (hxi : xi ∈ S)
      (psi : ClassFunction M ℂ) (hpsi : psi ∈ S) :
      characterPairing (tau1 xi) (tau1 psi) =
        if xi = psi then 1 else 0 := by
    rw [hcoh.isometry xi (hspan xi hxi) psi (hspan psi hpsi)]
    exact ftType34_characterPairing_eq_ite_core34 xi psi
      (hirr xi hxi) (hirr psi hpsi)
  have hsumPair (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      characterPairing sumTau (tau1 xi) = 1 := by
    dsimp only [sumTau]
    rw [pairingFinsetSumLeftMiddle]
    rw [Finset.sum_eq_single xi]
    · rw [hpairTau xi hxi xi hxi, if_pos rfl]
    · intro psi hpsi hpsiXi
      rw [hpairTau psi hpsi xi hxi, if_neg hpsiXi]
    · exact fun hnot ↦ False.elim (hnot hxi)
  have hpairSum (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      characterPairing (tau1 xi) sumTau = 1 := by
    rw [characterPairing_comm, hsumPair xi hxi]
  have hsumNorm : characterPairing sumTau sumTau = (n : ℂ) := by
    dsimp only [sumTau]
    rw [pairingFinsetSumRightMiddle]
    calc
      (∑ xi ∈ S, characterPairing sumTau (tau1 xi)) =
          ∑ _xi ∈ S, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro xi hxi
        exact hsumPair xi hxi
      _ = (S.card : ℂ) := by simp
      _ = (n : ℂ) := rfl
  have hzetaNorm : characterPairing (tau1 zeta) (tau1 zeta) = 1 := by
    rw [hcoh.isometry zeta (hspan zeta hzeta) zeta (hspan zeta hzeta)]
    exact IrreducibleCharacter.characterPairing_self
      ⟨zeta, hirr zeta hzeta⟩
  have hsumZeta : characterPairing sumTau (tau1 zeta) = 1 :=
    hsumPair zeta hzeta
  have hzetaSum : characterPairing (tau1 zeta) sumTau = 1 :=
    hpairSum zeta hzeta
  have hYnorm :
      characterPairing Y Y =
        (n : ℂ) * (a : ℂ) * ((a : ℂ) - 2) + (n : ℂ) ^ 2 := by
    rw [hYform]
    change characterPairing
      ((a : ℂ) • sumTau - (n : ℂ) • tau1 zeta)
      ((a : ℂ) • sumTau - (n : ℂ) • tau1 zeta) = _
    simp only [pairingSubLeftMiddle, pairingSubRightMiddle,
      characterPairing_smul_left, characterPairing_smul_right,
      hsumNorm, hsumZeta, hzetaSum, hzetaNorm]
    ring
  have hXY : characterPairing X Y = 0 := by
    rw [characterPairing_comm, hYX]
  have hsumNormDecomp :
      characterPairing (X + Y) (X + Y) =
        characterPairing X X + characterPairing Y Y := by
    rw [characterPairing_add_left, characterPairing_add_right,
      characterPairing_add_right, hXY, hYX]
    ring
  obtain ⟨xV, hxV⟩ := hXvirtual
  have hXnormCast :
      characterPairing X X = ((normSq xV : ℤ) : ℂ) := by
    rw [← hxV]
    exact VirtualCharacter.characterPairing_realize_self xV
  have htotal := norm_FTtype345_bridge base.maxM base.MtypeP
    base.notMtype2 zeta hzetaRef i j hj
  rw [hdecomp, hsumNormDecomp, hXnormCast, hYnorm, hratio] at htotal
  have hIntEq :
      normSq xV + (n : ℤ) * a * (a - 2) = 2 := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    dsimp only [n, S] at htotal ⊢
    linear_combination htotal
  have hbound : (n : ℤ) * a * (a - 2) ≤ 2 := by
    nlinarith [normSq_nonneg xV]
  have haCases := middleEvenCoefficientZeroOrTwo n a hnPos haEven hbound
  have hXeq : X = etaDiff := by
    have hYnormRatio :
        characterPairing Y Y = FTtype345_ratio base.MtypeP ^ 2 := by
      rcases haCases with ha | ha
      · rw [hYnorm, ha, hratio]
        dsimp only [n, S]
        ring
      · rw [hYnorm, ha, hratio]
        dsimp only [n, S]
        ring
    have hbridge := FTtype345_bridge_coherence base.maxM base.MtypeP
      base.notMtype2 zeta hzetaRef
      (↑S : Set (ClassFunction M ℂ)) tau1 i j X Y hcoh hdecomp
      hsub hirr hj hYspan hYX hYnormRatio
    dsimp only [etaDiff]
    simpa only [hdelta, Int.cast_one, one_smul] using hbridge
  have hEtaSum : characterPairing etaZero sumTau = 0 := by
    dsimp only [sumTau]
    rw [pairingFinsetSumRightMiddle]
    apply Finset.sum_eq_zero
    intro xi hxi
    exact hetaZeroTau xi hxi
  have hbetaEq :
      betaMiddle base tau1 zeta i j = (a : ℂ) • sumTau := by
    dsimp only [betaMiddle]
    rw [hdecomp, hXeq, hYform, hratio]
    dsimp only [etaDiff, n, S]
    module
  have haZero : a = 0 := by
    rcases haCases with ha | ha
    · exact ha
    · have hcastZero : (a : ℂ) = 0 := by
        calc
          (a : ℂ) = characterPairing etaZero
              (betaMiddle base tau1 zeta i j) := hcol0Beta.symm
          _ = characterPairing etaZero ((a : ℂ) • sumTau) := by rw [hbetaEq]
          _ = (a : ℂ) * characterPairing etaZero sumTau :=
            characterPairing_smul_right (a : ℂ) etaZero sumTau
          _ = 0 := by rw [hEtaSum, mul_zero]
      apply Int.cast_injective (α := ℂ)
      simpa only [Int.cast_zero] using hcastZero
  calc
    ftType345Tau base.maxM (alphaMiddle base zeta i j) = X + Y := hdecomp
    _ = etaDiff +
        ((a : ℂ) • sumTau - (n : ℂ) • tau1 zeta) := by
      rw [hXeq, hYform]
    _ = etaDiff - FTtype345_ratio base.MtypeP • tau1 zeta := by
      rw [haZero, Int.cast_zero, zero_smul, zero_sub, hratio]
      dsimp only [n, S]
      rw [sub_eq_add_neg]
    _ = etaTopMiddle base i j -
          etaTopMiddle base i
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
          FTtype345_ratio base.MtypeP • tau1 zeta := rfl

private theorem ftType34S1_mem_referenceFamily_core34
    (base : FTType34Base M U W W₁ W₂ defW)
    {zeta : ClassFunction M ℂ}
    (hzeta : zeta ∈ ftType34S1 base) :
    zeta ∈ FTType345ConstantsInternal.ftType345InducedFamily10 M := by
  have hderived : base.HU = derivedWithin M := by
    calc
      base.HU = FTcore M := base.FTcore_eq_HU.symm
      _ = derivedWithin M := FTcore_type_gt2 M base.type_gt_two
  have hK : base.HUInM =
      FTType345ConstantsInternal.ftType345DerivedInM M := by
    simp only [FTType34Base.HUInM,
      FTType345ConstantsInternal.ftType345DerivedInM, hderived]
  rw [ftType34S1, ftType34Layer] at hzeta
  rw [FTType345ConstantsInternal.ftType345InducedFamily10, ← hK]
  exact seqIndS base.HUInM
    (Iirr_kerDS (k := ℂ)
      (bot_le : (⊥ : Subgroup base.HUInM) ≤ base.HCInHU)
      (le_rfl : (⊤ : Subgroup base.HUInM) ≤ ⊤)) hzeta

private def ftType34S1_referenceChoice_core34
    (base : FTType34Base M U W W₁ W₂ defW)
    {zeta : ClassFunction M ℂ}
    (hzeta : zeta ∈ ftType34S1 base) :
    FTType345ReferenceChoice M W₁ zeta where
  irreducible :=
    FTType34StructureInternal.ftType34S1_irreducible34 base zeta hzeta
  mem_calS := ftType34S1_mem_referenceFamily_core34 base hzeta
  degree := FTType34StructureInternal.ftType34S1_degree34 base zeta hzeta

private theorem ftType34_muZero_ortho_S1_core34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ) (hzeta : zeta ∈ ftType34S1 base) :
    characterPairing
      (muMiddle base
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
      zeta = 0 := by
  classical
  let hzetaRef : FTType345ReferenceChoice M W₁ zeta :=
    ftType34S1_referenceChoice_core34 base hzeta
  rw [muMiddle, base.primeTI.primeTIRed_eq_sum]
  change characterPairingRight zeta
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.primeTI.primeTICharacter base.isoM i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) = 0
  rw [map_sum]
  apply Finset.sum_eq_zero
  intro i _
  exact FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
    base.MtypeP zeta hzetaRef i IrreducibleCharacter.trivial

private theorem ftType34_bridgeZero_supportedOn_FTsupport_core34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ) (hzeta : zeta ∈ ftType34S1 base) :
    muMiddle base
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        zeta ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
  let K : Subgroup M :=
    FTType345ConstantsInternal.ftType345DerivedInM M
  letI : K.Normal := TypeSpecInternal.derivedWithin_normal16 M
  let hzetaRef := ftType34S1_referenceChoice_core34 base hzeta
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
  rw [FTsupp_eq1 base.maxM base.type_gt_two,
    FTsupp1_type_gt2 M base.type_gt_two]
  exact ⟨hxK.1, fun hxOne ↦ hxK.2 (Subtype.ext hxOne)⟩

private theorem ftType34_bridgeZero_supportedOn_FTsupport0_core34
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ) (hzeta : zeta ∈ ftType34S1 base) :
    muMiddle base
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        zeta ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
  have hfull :=
    ftType34_bridgeZero_supportedOn_FTsupport_core34 base zeta hzeta
  rw [ClassFunction.mem_supportedOn_iff] at hfull ⊢
  intro x hx
  apply hfull x
  intro hxFull
  exact hx (FTsupp_sub0 M hxFull)

private theorem ftType34_tau_pairing_core34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi psi : ClassFunction M ℂ}
    (hphiVirtual : ClassFunction.IsVirtual phi)
    (hpsiVirtual : ClassFunction.IsVirtual psi)
    (hphiSupport : phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M})
    (hpsiSupport : psi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M}) :
    characterPairing (base.tau phi) (base.tau psi) =
      characterPairing phi psi := by
  have hDphiVirtual : ClassFunction.IsVirtual
      (Dade (FT_Dade0_hyp M base.maxM) phi) := by
    obtain ⟨z, hz⟩ := hphiVirtual
    obtain ⟨beta, hbeta, _⟩ :=
      (Dade_Zisometry (FT_Dade0_hyp M base.maxM)).2 z (by
        simpa only [hz] using hphiSupport)
    exact ⟨beta, by simpa only [hz] using hbeta.symm⟩
  have hDpsiVirtual : ClassFunction.IsVirtual
      (Dade (FT_Dade0_hyp M base.maxM) psi) := by
    obtain ⟨z, hz⟩ := hpsiVirtual
    obtain ⟨beta, hbeta, _⟩ :=
      (Dade_Zisometry (FT_Dade0_hyp M base.maxM)).2 z (by
        simpa only [hz] using hpsiSupport)
    exact ⟨beta, by simpa only [hz] using hbeta.symm⟩
  change characterPairing
      (base.targetMap (Dade (FT_Dade0_hyp M base.maxM) phi))
      (base.targetMap (Dade (FT_Dade0_hyp M base.maxM) psi)) = _
  rw [base.targetMap_pairing]
  calc
    characterPairing (Dade (FT_Dade0_hyp M base.maxM) phi)
        (Dade (FT_Dade0_hyp M base.maxM) psi) =
        starCharacterPairing (Dade (FT_Dade0_hyp M base.maxM) phi)
          (Dade (FT_Dade0_hyp M base.maxM) psi) :=
      (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hDphiVirtual hDpsiVirtual).symm
    _ = starCharacterPairing phi psi :=
      Dade_isometry (FT_Dade0_hyp M base.maxM)
        phi psi hphiSupport hpsiSupport
    _ = characterPairing phi psi :=
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hphiVirtual hpsiVirtual

private theorem ftType34_HUsharp_supportedOn_FTsupport0_core34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ ClassFunction.supportedOn
      (subgroupNonidentity base.HUInM)) :
    phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
  have hderived : base.HU = derivedWithin M := by
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
  · have hxHUmem : (x : G) ∈ base.HU := hxHU.1
    rwa [hderived] at hxHUmem
  · intro hxOne
    exact hxHU.2 (Subtype.ext hxOne)

private theorem ftType34S1_closure_supportedOn_FTsupport0_core34
    (base : FTType34Base M U W W₁ W₂ defW)
    {phi : ClassFunction M ℂ}
    (hspan : phi ∈ AddSubgroup.closure
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ)))
    (hoff : phi ∈ ClassFunction.supportedOn (nonidentitySet M)) :
    phi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
  letI : base.HUInM.Normal := by
    exact TypeSpecInternal.derivedWithin_normal16 M
  let calX : Finset (IrreducibleCharacter base.HUInM ℂ) :=
    Iirr_kerD (k := ℂ) ⊤ base.HCInHU
  have hrealize : ∀ psi ∈ AddSubgroup.closure
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ)),
      ∃ z : SeqIndLattice base.HUInM calX,
        seqIndRealize base.HUInM calX z = psi := by
    intro psi hpsi
    induction hpsi using AddSubgroup.closure_induction with
    | mem psi hpsi =>
        change psi ∈ seqInd base.HUInM
          (Iirr_kerD (k := ℂ) ⊤ base.HCInHU) at hpsi
        simpa only [calX] using
          (seqInd_zcharW base.HUInM hpsi)
    | zero =>
        exact ⟨0, by simp⟩
    | add psi theta _ _ hpsi htheta =>
        obtain ⟨z, hz⟩ := hpsi
        obtain ⟨w, hw⟩ := htheta
        exact ⟨z + w, by simp only [map_add, hz, hw]⟩
    | neg psi _ hpsi =>
        obtain ⟨z, hz⟩ := hpsi
        exact ⟨-z, by simp only [map_neg, hz]⟩
  obtain ⟨z, hz⟩ := hrealize phi hspan
  have hHU : phi ∈ ClassFunction.supportedOn
      (subgroupNonidentity base.HUInM) := by
    rw [← hz]
    apply zcharD1_seqInd_on base.HUInM calX z
    rwa [hz]
  exact ftType34_HUsharp_supportedOn_FTsupport0_core34 base hHU
private theorem ftType34TauAlphaFromNormalizedMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base)
    (tau1 : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (hcoh : coherent_with
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau base.maxM) tau1)
    (hzero : ftType345Tau base.maxM
        (muMiddle base
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
          zeta) =
      etaColumnTopMiddle base
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        tau1 zeta)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ftType345Tau base.maxM (alphaMiddle base zeta i j) =
      etaTopMiddle base i j -
        etaTopMiddle base i
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        FTtype345_ratio base.MtypeP • tau1 zeta := by
  classical
  let S := ftType34S1 base
  let n := S.card
  let alpha := alphaMiddle base zeta i j
  let phi := ftType345Tau base.maxM alpha
  let sumTau : ClassFunction (⊤ : Subgroup G) ℂ :=
    ∑ xi ∈ S, tau1 xi
  let etaZero : ClassFunction (⊤ : Subgroup G) ℂ :=
    etaColumnTopMiddle base
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  let etaDiff : ClassFunction (⊤ : Subgroup G) ℂ :=
    etaTopMiddle base i j -
      etaTopMiddle base i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  let hzetaRef : FTType345ReferenceChoice M W₁ zeta :=
    ftType34S1_referenceChoice_core34 base hzeta
  have hirr :=
    FTType34StructureInternal.ftType34S1_irreducible34 base
  have hdegree :=
    FTType34StructureInternal.ftType34S1_degree34 base
  have hSCard := ftType34S1CardMulQMiddle base hirr hdegree
  obtain ⟨hd, hdelta, hratio⟩ :=
    ftType34ConstantsMiddle base hSCard
      (fun k hk ↦
        FTType34StructureInternal.ftType34_mu_degree11 base k hk)
  have hsub : cfConjC_subset
      (↑S : Set (ClassFunction M ℂ))
      (FTtypePKernelLayer base.primeDade) := by
    refine ⟨?_, ?_⟩
    · simpa only [S] using
        FTType34StructureInternal.ftType34S1_subset_kernelLayer34 base
    · simpa only [S] using
        (FTType34StructureInternal.ftType34S1_cfConjC_subset34 base).2
  have hsourceVirtual (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      ClassFunction.IsVirtual xi :=
    ⟨Finsupp.single ⟨xi, hirr xi (by simpa only [S] using hxi)⟩ 1,
      by simp⟩
  have hspan (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      xi ∈ AddSubgroup.closure
        (↑S : Set (ClassFunction M ℂ)) :=
    AddSubgroup.subset_closure hxi
  have htauVirtual (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      ClassFunction.IsVirtual (tau1 xi) :=
    hcoh.mapsToVirtual xi (hspan xi hxi)
  have htauInj : Set.InjOn tau1
      (↑S : Set (ClassFunction M ℂ)) := by
    intro xi hxi psi hpsi heq
    have hdiffSpan : xi - psi ∈ AddSubgroup.closure
        (↑S : Set (ClassFunction M ℂ)) :=
      (AddSubgroup.closure
        (↑S : Set (ClassFunction M ℂ))).sub_mem
          (hspan xi hxi) (hspan psi hpsi)
    have hmapZero : tau1 (xi - psi) = 0 := by
      rw [map_sub, heq, sub_self]
    have hnorm : characterPairing (xi - psi) (xi - psi) = 0 := by
      rw [← hcoh.isometry (xi - psi) hdiffSpan (xi - psi) hdiffSpan,
        hmapZero]
      simp
    have hdiffVirtual := (hsourceVirtual xi hxi).sub
      (hsourceVirtual psi hpsi)
    exact sub_eq_zero.mp
      (PTypeCorePairingInternal.pTypeCore_virtual_eq_zero_of_pairing_self_eq_zero
        hdiffVirtual hnorm)
  let T : Finset (ClassFunction (⊤ : Subgroup G) ℂ) :=
    S.image tau1
  have hTvirtual : ∀ gamma ∈ T, ClassFunction.IsVirtual gamma := by
    intro gamma hgamma
    obtain ⟨xi, hxi, rfl⟩ := Finset.mem_image.mp hgamma
    exact htauVirtual xi hxi
  have hTorthonormal : ∀ gamma ∈ T, ∀ theta ∈ T,
      characterPairing gamma theta =
        if gamma = theta then 1 else 0 := by
    intro gamma hgamma theta htheta
    obtain ⟨xi, hxi, rfl⟩ := Finset.mem_image.mp hgamma
    obtain ⟨psi, hpsi, rfl⟩ := Finset.mem_image.mp htheta
    rw [hcoh.isometry xi (hspan xi hxi) psi (hspan psi hpsi),
      ftType34_characterPairing_eq_ite_core34 xi psi
        (hirr xi (by simpa only [S] using hxi))
        (hirr psi (by simpa only [S] using hpsi))]
    by_cases hxiPsi : xi = psi
    · rw [if_pos hxiPsi, if_pos (congrArg tau1 hxiPsi)]
    · have htauNe : tau1 xi ≠ tau1 psi := by
        intro htau
        exact hxiPsi (htauInj hxi hpsi htau)
      rw [if_neg hxiPsi, if_neg htauNe]
  have hTauEta (xi : ClassFunction M ℂ) (hxi : xi ∈ S)
      (k : IrreducibleCharacter W₁ ℂ)
      (ell : IrreducibleCharacter W₂ ℂ) :
      characterPairing (tau1 xi) (etaTopMiddle base k ell) = 0 := by
    have hxiBase : xi ∈ ftType34S1 base := by
      simpa only [S] using hxi
    simpa only [etaTopMiddle, ftType345Eta,
      CyclicTIIsometryData.cyclicTIImage,
      CyclicTIIsometryData.cyclicTISourceIrreducible] using
      coherent_ortho_cycTIiso base.primeDade base.isoM base.isoG
        (mFT_odd M) hsub hcoh
        (by
          change xi ∈ ftType34S1 base
          exact hxiBase)
        (hirr xi hxiBase)
        (IrreducibleCharacter.cyclicTICharacter defW k ell)
  have hetaZeroTau : ∀ xi ∈ S,
      characterPairing etaZero (tau1 xi) = 0 := by
    intro xi hxi
    rw [characterPairing_comm]
    dsimp only [etaZero, etaColumnTopMiddle]
    rw [pairingFinsetSumRightMiddle]
    apply Finset.sum_eq_zero
    intro k _
    exact hTauEta xi hxi k IrreducibleCharacter.trivial

  have hAlphaVirtual : ClassFunction.IsVirtual alpha := by
    simpa only [alpha] using
      vchar_FTtype345_bridge base.maxM base.MtypeP base.notMtype2
        zeta hzetaRef i j
  have hPhiVirtual : ClassFunction.IsVirtual phi := by
    simpa only [phi, alpha] using
      vchar_Dade_FTtype345_bridge base.maxM base.MtypeP base.notMtype2
        zeta hzetaRef i j hj
  have hTauZetaVirtual : ClassFunction.IsVirtual (tau1 zeta) :=
    htauVirtual zeta (by simpa only [S] using hzeta)
  obtain ⟨c, hc⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt
      hPhiVirtual hTauZetaVirtual
  let a : ℤ := c + n
  have haCast : (a : ℂ) = (c : ℂ) + (n : ℂ) := by
    dsimp only [a]
    push_cast
    rfl
  have hmuPair (xi : ClassFunction M ℂ) (hxi : xi ∈ S)
      (r : IrreducibleCharacter W₁ ℂ)
      (s : IrreducibleCharacter W₂ ℂ) :
      characterPairing (ftType345Mu2 base.MtypeP r s) xi = 0 := by
    exact FTType345SupportNormInternal.ftType345_primeTI_ortho_reference
      base.MtypeP xi
        (ftType34S1_referenceChoice_core34 base
          (by simpa only [S] using hxi)) r s
  have hpairPhiOther (xi : ClassFunction M ℂ) (hxi : xi ∈ S)
      (hxiZeta : xi ≠ zeta) :
      characterPairing phi (tau1 xi) = (a : ℂ) := by
    let zdiff : ClassFunction M ℂ := zeta - xi
    have hdiffSpan : zdiff ∈ AddSubgroup.closure
        (↑S : Set (ClassFunction M ℂ)) :=
      (AddSubgroup.closure
        (↑S : Set (ClassFunction M ℂ))).sub_mem
          (hspan zeta (by simpa only [S] using hzeta)) (hspan xi hxi)
    have hdiffOff : zdiff ∈
        ClassFunction.supportedOn (nonidentitySet M) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      have hxOne : x = 1 := by
        simpa [nonidentitySet] using not_not.mp hx
      subst x
      simp only [zdiff, ClassFunction.sub_apply]
      rw [hdegree zeta hzeta,
        hdegree xi (by simpa only [S] using hxi), sub_self]
    have hdiffSupport :=
      ftType34S1_closure_supportedOn_FTsupport0_core34 base
        hdiffSpan hdiffOff
    have hdiffVirtual :=
      (hsourceVirtual zeta (by simpa only [S] using hzeta)).sub
        (hsourceVirtual xi hxi)
    have hAgree : tau1 zdiff = ftType345Tau base.maxM zdiff :=
      hcoh.agrees zdiff hdiffSpan hdiffOff
    have hAlphaSupport : alpha ∈ ClassFunction.supportedOn
        {x : M | (x : G) ∈ FTsupport0 M} := by
      simpa only [alpha, ftType345Support0InM] using
        supp_FTtype345_bridge base.maxM base.MtypeP base.notMtype2
          zeta hzetaRef i j hj
    have hDadePairG := ftType34_tau_pairing_core34 base
      hAlphaVirtual hdiffVirtual hAlphaSupport hdiffSupport
    have hDadePair : characterPairing phi
        (ftType345Tau base.maxM zdiff) =
          characterPairing alpha zdiff := by
      change characterPairing (base.targetMap phi)
          (base.targetMap (ftType345Tau base.maxM zdiff)) =
        characterPairing alpha zdiff at hDadePairG
      rw [base.targetMap_pairing] at hDadePairG
      exact hDadePairG
    have hzetaXi : characterPairing zeta xi = 0 := by
      let zetaI : IrreducibleCharacter M ℂ := ⟨zeta, hirr zeta hzeta⟩
      let xiI : IrreducibleCharacter M ℂ :=
        ⟨xi, hirr xi (by simpa only [S] using hxi)⟩
      have hne : zetaI ≠ xiI := by
        intro h
        exact hxiZeta (congrArg Subtype.val h).symm
      simpa only [zetaI, xiI] using
        IrreducibleCharacter.characterPairing_eq_zero hne
    have hAlphaZeta : characterPairing alpha zeta = -(n : ℂ) := by
      simp only [alpha, alphaMiddle, FTtype345_bridge, hdelta,
        Int.cast_one, one_smul, hratio, pairingSubLeftMiddle,
        characterPairing_smul_left,
        hmuPair zeta (by simpa only [S] using hzeta),
        IrreducibleCharacter.characterPairing_self
          ⟨zeta, hirr zeta hzeta⟩]
      ring
    have hAlphaXi : characterPairing alpha xi = 0 := by
      simp only [alpha, alphaMiddle, FTtype345_bridge, hdelta,
        Int.cast_one, one_smul, hratio, pairingSubLeftMiddle,
        characterPairing_smul_left, hmuPair xi hxi, hzetaXi]
      ring
    have hAlphaDiff : characterPairing alpha zdiff = -(n : ℂ) := by
      dsimp only [zdiff]
      rw [pairingSubRightMiddle, hAlphaZeta, hAlphaXi, sub_zero]
    have hshift : characterPairing phi (tau1 zeta) -
        characterPairing phi (tau1 xi) = -(n : ℂ) := by
      calc
        characterPairing phi (tau1 zeta) -
            characterPairing phi (tau1 xi) =
            characterPairing phi (tau1 zdiff) := by
              rw [map_sub, pairingSubRightMiddle]
        _ = characterPairing phi (ftType345Tau base.maxM zdiff) := by
              rw [hAgree]
        _ = characterPairing alpha zdiff := hDadePair
        _ = -(n : ℂ) := hAlphaDiff
    rw [hc] at hshift
    rw [haCast]
    linear_combination -hshift

  obtain ⟨Y, X, hYspan, hYvirtual, hXvirtual, hsplit,
      hXorth, hYX⟩ :=
    orthogonal_split_virtual T hTvirtual hTorthonormal hPhiVirtual
  have hdecomp : phi = X + Y := by
    rw [hsplit]
    exact add_comm Y X
  have hYpair (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      characterPairing Y (tau1 xi) =
        if xi = zeta then (a : ℂ) - (n : ℂ) else (a : ℂ) := by
    have htauMem : tau1 xi ∈ T :=
      Finset.mem_image.mpr ⟨xi, hxi, rfl⟩
    have hpairFromSplit : characterPairing Y (tau1 xi) =
        characterPairing phi (tau1 xi) := by
      have h := congrArg
        (fun f : ClassFunction (⊤ : Subgroup G) ℂ ↦
          characterPairing f (tau1 xi)) hdecomp
      rw [characterPairing_add_left, hXorth (tau1 xi) htauMem,
        zero_add] at h
      exact h.symm
    by_cases hxiEq : xi = zeta
    · subst xi
      rw [if_pos rfl, hpairFromSplit, hc, haCast]
      ring
    · rw [if_neg hxiEq, hpairFromSplit,
        hpairPhiOther xi hxi hxiEq]
  have hpairTau (xi : ClassFunction M ℂ) (hxi : xi ∈ S)
      (psi : ClassFunction M ℂ) (hpsi : psi ∈ S) :
      characterPairing (tau1 xi) (tau1 psi) =
        if xi = psi then 1 else 0 := by
    rw [hcoh.isometry xi (hspan xi hxi) psi (hspan psi hpsi)]
    exact ftType34_characterPairing_eq_ite_core34 xi psi
      (hirr xi (by simpa only [S] using hxi))
      (hirr psi (by simpa only [S] using hpsi))
  have hsumPair (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      characterPairing sumTau (tau1 xi) = 1 := by
    dsimp only [sumTau]
    rw [pairingFinsetSumLeftMiddle, Finset.sum_eq_single xi]
    · rw [hpairTau xi hxi xi hxi, if_pos rfl]
    · intro psi hpsi hpsiXi
      rw [hpairTau psi hpsi xi hxi, if_neg hpsiXi]
    · exact fun h ↦ False.elim (h hxi)
  let Y0 : ClassFunction (⊤ : Subgroup G) ℂ :=
    (a : ℂ) • sumTau - (n : ℂ) • tau1 zeta
  have hsumSpan : sumTau ∈ AddSubgroup.closure
      (↑T : Set (ClassFunction (⊤ : Subgroup G) ℂ)) := by
    dsimp only [sumTau]
    apply AddSubgroup.sum_mem
    intro xi hxi
    exact AddSubgroup.subset_closure
      (Finset.mem_image.mpr ⟨xi, hxi, rfl⟩)
  have hY0span : Y0 ∈ AddSubgroup.closure
      (↑T : Set (ClassFunction (⊤ : Subgroup G) ℂ)) := by
    apply (AddSubgroup.closure
      (↑T : Set (ClassFunction (⊤ : Subgroup G) ℂ))).sub_mem
    · simpa only [← Int.cast_smul_eq_zsmul ℂ] using
        (AddSubgroup.closure
          (↑T : Set (ClassFunction (⊤ : Subgroup G) ℂ))).zsmul_mem
            hsumSpan a
    · simpa only [Nat.cast_smul_eq_nsmul] using
        (AddSubgroup.closure
          (↑T : Set (ClassFunction (⊤ : Subgroup G) ℂ))).nsmul_mem
            (AddSubgroup.subset_closure
              (Finset.mem_image.mpr
                ⟨zeta, by simpa only [S] using hzeta, rfl⟩)) n
  have hY0pair (xi : ClassFunction M ℂ) (hxi : xi ∈ S) :
      characterPairing Y0 (tau1 xi) =
        if xi = zeta then (a : ℂ) - (n : ℂ) else (a : ℂ) := by
    dsimp only [Y0]
    rw [pairingSubLeftMiddle, characterPairing_smul_left,
      characterPairing_smul_left, hsumPair xi hxi,
      hpairTau zeta (by simpa only [S] using hzeta) xi hxi]
    by_cases hxiEq : xi = zeta
    · subst xi
      rw [if_pos rfl, if_pos rfl]
      ring
    · rw [if_neg hxiEq, if_neg (Ne.symm hxiEq)]
      ring
  have hYform : Y = (a : ℂ) • sumTau - (n : ℂ) • tau1 zeta := by
    change Y = Y0
    rw [PTypeCorePairingInternal.pTypeCore_eq_sum_pairing_smul_of_mem_closure
          T hTorthonormal hYspan,
      PTypeCorePairingInternal.pTypeCore_eq_sum_pairing_smul_of_mem_closure
          T hTorthonormal hY0span]
    apply Finset.sum_congr rfl
    intro gamma hgamma
    obtain ⟨xi, hxi, rfl⟩ := Finset.mem_image.mp hgamma
    rw [hYpair xi hxi, hY0pair xi hxi]

  let psi := ftType345Tau base.maxM
    (muMiddle base
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) - zeta)
  have hbridgeVirtual :=
    FTType34StructureInternal.ftType34_bridgeZero_virtual34 base zeta hzeta
  have hbridgeSupport :=
    ftType34_bridgeZero_supportedOn_FTsupport0_core34 base zeta hzeta
  have hAlphaSupport : alpha ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport0 M} := by
    simpa only [alpha, ftType345Support0InM] using
      supp_FTtype345_bridge base.maxM base.MtypeP base.notMtype2
        zeta hzetaRef i j hj
  have hPsiPhiG := ftType34_tau_pairing_core34 base hbridgeVirtual
    hAlphaVirtual hbridgeSupport hAlphaSupport
  have hPsiPhiDade : characterPairing psi phi =
      characterPairing
        (muMiddle base
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
          zeta) alpha := by
    change characterPairing (base.targetMap psi) (base.targetMap phi) = _
      at hPsiPhiG
    rw [base.targetMap_pairing] at hPsiPhiG
    exact hPsiPhiG
  have hmuZeroMuJ : characterPairing
      (muMiddle base IrreducibleCharacter.trivial)
      (ftType345Mu2 base.MtypeP i j) = 0 := by
    rw [characterPairing_comm]
    simpa only [muMiddle, if_neg hj] using
      base.primeTI.cfdot_prTIirr_red base.isoM i j
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  have hmuZeroMuZero : characterPairing
      (muMiddle base IrreducibleCharacter.trivial)
      (ftType345Mu2 base.MtypeP i IrreducibleCharacter.trivial) = 1 := by
    rw [characterPairing_comm]
    change characterPairing
      (base.primeTI.primeTICharacter base.isoM i
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ))
      (base.primeTI.primeTIRed base.isoM
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) = 1
    have h := base.primeTI.cfdot_prTIirr_red base.isoM i
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
    rw [if_pos rfl] at h
    exact h
  have hmuZeroZeta : characterPairing
      (muMiddle base IrreducibleCharacter.trivial) zeta = 0 := by
    simpa only [muMiddle] using
      ftType34_muZero_ortho_S1_core34 base zeta hzeta
  have hzetaMuJ : characterPairing zeta
      (ftType345Mu2 base.MtypeP i j) = 0 := by
    rw [characterPairing_comm]
    exact hmuPair zeta (by simpa only [S] using hzeta) i j
  have hzetaMuZero : characterPairing zeta
      (ftType345Mu2 base.MtypeP i IrreducibleCharacter.trivial) = 0 := by
    rw [characterPairing_comm]
    exact hmuPair zeta (by simpa only [S] using hzeta) i
      IrreducibleCharacter.trivial
  have hzetaNorm : characterPairing zeta zeta = 1 :=
    IrreducibleCharacter.characterPairing_self ⟨zeta, hirr zeta hzeta⟩
  have hPsiPhi : characterPairing psi phi = (n : ℂ) - 1 := by
    rw [hPsiPhiDade]
    simp only [alpha, alphaMiddle, FTtype345_bridge, hdelta,
      Int.cast_one, one_smul, hratio, pairingSubLeftMiddle,
      pairingSubRightMiddle, characterPairing_smul_right,
      hmuZeroMuJ, hmuZeroMuZero, hmuZeroZeta, hzetaMuJ,
      hzetaMuZero, hzetaNorm]
    ring
  have hetaZeroDecomp : etaZero = psi + tau1 zeta := by
    dsimp only [etaZero, psi]
    rw [hzero]
    module
  have hetaZeroEtaDiff : characterPairing etaZero etaDiff = -1 := by
    dsimp only [etaZero, etaDiff]
    rw [pairingSubRightMiddle,
      characterPairingEtaColumnTopMiddle,
      characterPairingEtaColumnTopMiddle,
      if_neg hj, if_pos rfl]
    ring
  have hetaZeroPhi : characterPairing etaZero phi =
      (n : ℂ) - 1 + (c : ℂ) := by
    rw [hetaZeroDecomp, characterPairing_add_left, hPsiPhi,
      characterPairing_comm, hc]
  have hcol0Beta : characterPairing etaZero
      (betaMiddle base tau1 zeta i j) = (a : ℂ) := by
    dsimp only [betaMiddle, phi, alpha, etaDiff]
    rw [hratio, characterPairing_add_right, pairingSubRightMiddle,
      characterPairing_smul_right, hetaZeroPhi, hetaZeroEtaDiff,
      hetaZeroTau zeta (by simpa only [S] using hzeta), haCast]
    ring

  let jOne := FTtype345_jOne base.MtypeP
  have hjOne : jOne ≠
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :=
    FTtype345_jOne_ne_trivial base.MtypeP
  have hbetaEq := ftType34BetaIndexIndependentMiddle base zeta tau1
    hdelta i j hj
  have hBetaReal := ftType34BetaRealMiddle base zeta hzeta hzetaRef
    tau1 hcoh hsub hirr hdelta hratio i j hj
  have hBetaVirtual : ClassFunction.IsVirtual
      (betaMiddle base tau1 zeta i j) := by
    dsimp only [betaMiddle]
    rw [hratio]
    exact (hPhiVirtual.sub
      ((cyclicTIImageIsVirtualMiddle base.isoG (i, j)).sub
        (cyclicTIImageIsVirtualMiddle base.isoG
          (i, IrreducibleCharacter.trivial)))).add
      (hTauZetaVirtual.natCast_smul n)
  let oneTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    (IrreducibleCharacter.trivial :
      IrreducibleCharacter (⊤ : Subgroup G) ℂ)
  let oneM : ClassFunction M ℂ :=
    (IrreducibleCharacter.trivial : IrreducibleCharacter M ℂ)
  have heta00 : etaTopMiddle base
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) =
      oneTop := by
    change base.isoG.linearMap
        (IrreducibleCharacter.cyclicTICharacter defW
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :
            ClassFunction W ℂ) = oneTop
    rw [IrreducibleCharacter.cyclicTICharacter_trivial,
      base.isoG.map_trivial]
  have honeTopVirtual : ClassFunction.IsVirtual oneTop :=
    ⟨Finsupp.single
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ) 1, by simp [oneTop]⟩
  have honeMVirtual : ClassFunction.IsVirtual oneM :=
    ⟨Finsupp.single
      (IrreducibleCharacter.trivial : IrreducibleCharacter M ℂ) 1,
      by simp [oneM]⟩
  have hTauZetaOne : characterPairing (tau1 zeta) oneTop = 0 := by
    rw [← heta00]
    exact hTauEta zeta (by simpa only [S] using hzeta)
      IrreducibleCharacter.trivial IrreducibleCharacter.trivial
  let alphaRef := alphaMiddle base zeta
    (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) jOne
  let phiRef := ftType345Tau base.maxM alphaRef
  have hAlphaRefVirtual : ClassFunction.IsVirtual alphaRef := by
    simpa only [alphaRef] using
      vchar_FTtype345_bridge base.maxM base.MtypeP base.notMtype2
        zeta hzetaRef IrreducibleCharacter.trivial jOne
  have hPhiRefVirtual : ClassFunction.IsVirtual phiRef := by
    simpa only [phiRef, alphaRef] using
      vchar_Dade_FTtype345_bridge base.maxM base.MtypeP base.notMtype2
        zeta hzetaRef IrreducibleCharacter.trivial jOne hjOne
  have hAlphaRefSupport : alphaRef ∈ ClassFunction.supportedOn
      (ftType345Support0InM M) := by
    simpa only [alphaRef] using
      supp_FTtype345_bridge base.maxM base.MtypeP base.notMtype2
        zeta hzetaRef IrreducibleCharacter.trivial jOne hjOne
  have hcomap : ClassFunction.comap
      (Subgroup.inclusion (FT_Dade0_hyp M base.maxM).2.1) oneTop = oneM := by
    ext x
    simp [oneTop, oneM]
  have hrecip := Dade_reciprocity (FT_Dade0_hyp M base.maxM)
    alphaRef oneTop hAlphaRefSupport (by
      intro x hx y
      simp [oneTop])
  have hPhiRefOne : characterPairing phiRef oneTop =
      characterPairing alphaRef oneM := by
    calc
      characterPairing phiRef oneTop =
          starCharacterPairing phiRef oneTop :=
        (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hPhiRefVirtual honeTopVirtual).symm
      _ = starCharacterPairing alphaRef oneM := by
        simpa only [phiRef, ftType345Tau, hcomap] using hrecip
      _ = characterPairing alphaRef oneM :=
        PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hAlphaRefVirtual honeMVirtual
  have hmuJOne : characterPairing
      (ftType345Mu2 base.MtypeP IrreducibleCharacter.trivial jOne) oneM = 0 := by
    change characterPairing
      (base.primeTI.primeTIIndex base.isoM
        (IrreducibleCharacter.trivial, jOne) : ClassFunction M ℂ)
      oneM = 0
    rw [show oneM =
        (base.primeTI.primeTIIndex base.isoM
          (IrreducibleCharacter.trivial,
            IrreducibleCharacter.trivial) : IrreducibleCharacter M ℂ) by
      rw [base.primeTI.prTIirr00 base.isoM]]
    apply IrreducibleCharacter.characterPairing_eq_zero
    intro h
    exact hjOne (congrArg Prod.snd
      ((base.primeTI.primeTIirr_spec base.isoM).1 h))
  have hmu00Eq :
      ftType345Mu2 base.MtypeP
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) =
        oneM := by
    change
      (base.primeTI.primeTIIndex base.isoM
          (IrreducibleCharacter.trivial,
            IrreducibleCharacter.trivial) : ClassFunction M ℂ) = oneM
    rw [base.primeTI.prTIirr00 base.isoM]
  have hmu00One : characterPairing
      (ftType345Mu2 base.MtypeP IrreducibleCharacter.trivial
        IrreducibleCharacter.trivial) oneM = 1 := by
    rw [hmu00Eq]
    simpa only [oneM] using
      IrreducibleCharacter.characterPairing_self
        (IrreducibleCharacter.trivial : IrreducibleCharacter M ℂ)
  have hzetaOne : characterPairing zeta oneM = 0 := by
    rw [characterPairing_comm]
    have h := hmuPair zeta (by simpa only [S] using hzeta)
      IrreducibleCharacter.trivial IrreducibleCharacter.trivial
    rw [hmu00Eq] at h
    exact h
  have hAlphaRefOne : characterPairing alphaRef oneM = -1 := by
    simp only [alphaRef, alphaMiddle, FTtype345_bridge, hdelta,
      Int.cast_one, one_smul, hratio, pairingSubLeftMiddle,
      characterPairing_smul_left, hmuJOne, hmu00One, hzetaOne]
    ring
  have hEtaRefDiffOne : characterPairing
      (etaTopMiddle base IrreducibleCharacter.trivial jOne -
        etaTopMiddle base IrreducibleCharacter.trivial
          IrreducibleCharacter.trivial) oneTop = -1 := by
    rw [pairingSubLeftMiddle, ← heta00,
      characterPairingEtaTopMiddle,
      characterPairingEtaTopMiddle, if_neg, if_pos rfl]
    · ring
    · intro h
      exact hjOne (congrArg Prod.snd h)
  have hBetaOne : characterPairing
      (betaMiddle base tau1 zeta i j) oneTop = 0 := by
    rw [hbetaEq]
    dsimp only [betaMiddle]
    rw [hratio, characterPairing_add_left, pairingSubLeftMiddle,
      characterPairing_smul_left, hPhiRefOne, hAlphaRefOne,
      hEtaRefDiffOne, hTauZetaOne]
    ring
  have hEtaZeroVirtual : ClassFunction.IsVirtual etaZero := by
    simpa only [etaZero] using etaColumnTopVirtualMiddle base
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  have hEtaZeroReal : cfReal etaZero := by
    simpa only [etaZero] using etaZeroColumnTopRealMiddle base
  have hEvenPair : evenCharacterPairing etaZero
      (betaMiddle base tau1 zeta i j) := by
    apply (cfdot_real_vchar_even (mFT_odd (⊤ : Subgroup G))
      etaZero (betaMiddle base tau1 zeta i j)
      ⟨hEtaZeroVirtual, hEtaZeroReal⟩
      ⟨hBetaVirtual, hBetaReal⟩).2
    right
    exact ⟨0, by rw [hBetaOne]; norm_num⟩
  have haEven : Even a := by
    obtain ⟨b, hb⟩ := hEvenPair
    have hab : a = 2 * b := by
      apply Int.cast_injective (α := ℂ)
      rw [← hcol0Beta]
      exact hb
    exact ⟨b, by omega⟩

  have hYspanImage : Y ∈ AddSubgroup.closure
      (tau1 '' (↑(ftType34S1 base) : Set (ClassFunction M ℂ))) := by
    simpa only [T, S, Finset.coe_image] using hYspan
  exact ftType34TauAlphaFromCoefficientMiddle
    (base := base)
    (zeta := zeta)
    (hzeta := hzeta)
    (hzetaRef := hzetaRef)
    (tau1 := tau1)
    (hcoh := hcoh)
    (hsub := hsub)
    (hirr := hirr)
    (i := i)
    (j := j)
    (hj := hj)
    (hd := hd)
    (hdelta := hdelta)
    (hratio := hratio)
    (X := X)
    (Y := Y)
    (a := a)
    (hXvirtual := hXvirtual)
    (hdecomp := by simpa only [phi, alpha] using hdecomp)
    (hYspan := hYspanImage)
    (hYX := hYX)
    (hYform := by simpa only [sumTau, n, S] using hYform)
    (haEven := haEven)
    (etaZero := etaZero)
    (hetaZeroTau := by
      intro xi hxi
      exact hetaZeroTau xi (by simpa only [S] using hxi))
    (hcol0Beta := hcol0Beta)

/-! ## The balancing identity (11.8.6) -/

private theorem ftType34SumConstSmulMiddle
    {Q I : Type} [Group Q] [Fintype I]
    (a : ℂ) (f : ClassFunction Q ℂ) :
    ∑ _i : I, a • f =
      ((Fintype.card I : ℂ) * a) • f := by
  rw [Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul]

private theorem ftType34BalancingIdentityTopMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (tau1 : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hTauAlpha : ∀ i : IrreducibleCharacter W₁ ℂ,
      ftType345Tau base.maxM (alphaMiddle base zeta i j) =
        etaTopMiddle base i j -
          etaTopMiddle base i
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
          FTtype345_ratio base.MtypeP • tau1 zeta)
    (hzero : ftType345Tau base.maxM
        (muMiddle base
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
          zeta) =
      etaColumnTopMiddle base
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        tau1 zeta)
    (hd : FTtype345_TIirr_degree base.MtypeP = base.u)
    (hdelta : FTtype345_TIsign base.MtypeP = 1) :
    ftType345Tau base.maxM
        (muMiddle base j -
          (FTtype345_TIirr_degree base.MtypeP : ℂ) • zeta) =
      etaColumnTopMiddle base j -
        (FTtype345_TIirr_degree base.MtypeP : ℂ) • tau1 zeta := by
  classical
  letI : IsCyclic W₁ := base.primeTI.complement_cyclic
  have hcardI :
      Fintype.card (IrreducibleCharacter W₁ ℂ) = Nat.card W₁ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hratio :
      (Nat.card W₁ : ℂ) * FTtype345_ratio base.MtypeP =
        (FTtype345_TIirr_degree base.MtypeP : ℂ) - 1 := by
    calc
      (Nat.card W₁ : ℂ) * FTtype345_ratio base.MtypeP =
          (FTtype345_TIirr_degree base.MtypeP : ℂ) -
            (FTtype345_TIsign base.MtypeP : ℂ) := by
        rw [FTtype345_ratio]
        field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne']
      _ = (FTtype345_TIirr_degree base.MtypeP : ℂ) - 1 := by
        simp only [hdelta, Int.cast_one]
  have hsumMuJ :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Mu2 base.MtypeP i j) = muMiddle base j :=
    (base.primeTI.primeTIRed_eq_sum base.isoM j).symm
  have hsumMuZero :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Mu2 base.MtypeP i
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) =
        muMiddle base
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) :=
    (base.primeTI.primeTIRed_eq_sum base.isoM
      IrreducibleCharacter.trivial).symm
  have hsumRatioZeta :
      (∑ _i : IrreducibleCharacter W₁ ℂ,
          FTtype345_ratio base.MtypeP • zeta) =
        ((FTtype345_TIirr_degree base.MtypeP : ℂ) - 1) • zeta := by
    rw [ftType34SumConstSmulMiddle
      (Q := M) (I := IrreducibleCharacter W₁ ℂ), hcardI, hratio]
  have hsumAlpha :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          alphaMiddle base zeta i j) =
        muMiddle base j -
          (FTtype345_TIirr_degree base.MtypeP : ℂ) • zeta -
          (muMiddle base IrreducibleCharacter.trivial - zeta) := by
    calc
      (∑ i : IrreducibleCharacter W₁ ℂ,
          alphaMiddle base zeta i j) =
          (∑ i : IrreducibleCharacter W₁ ℂ,
            ftType345Mu2 base.MtypeP i j) -
          (∑ i : IrreducibleCharacter W₁ ℂ,
            ftType345Mu2 base.MtypeP i IrreducibleCharacter.trivial) -
          (∑ _i : IrreducibleCharacter W₁ ℂ,
            FTtype345_ratio base.MtypeP • zeta) := by
        simp_rw [alphaMiddle, FTtype345_bridge, hdelta, Int.cast_one,
          one_smul]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = muMiddle base j -
          muMiddle base IrreducibleCharacter.trivial -
          ((FTtype345_TIirr_degree base.MtypeP : ℂ) - 1) • zeta := by
        rw [hsumMuJ, hsumMuZero, hsumRatioZeta]
      _ = muMiddle base j -
          (FTtype345_TIirr_degree base.MtypeP : ℂ) • zeta -
          (muMiddle base IrreducibleCharacter.trivial - zeta) := by
        module
  have hsumTauAlpha :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau base.maxM (alphaMiddle base zeta i j)) =
        etaColumnTopMiddle base j -
          etaColumnTopMiddle base IrreducibleCharacter.trivial -
          ((FTtype345_TIirr_degree base.MtypeP : ℂ) - 1) • tau1 zeta := by
    calc
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau base.maxM (alphaMiddle base zeta i j)) =
          ∑ i : IrreducibleCharacter W₁ ℂ,
            (etaTopMiddle base i j -
              etaTopMiddle base i IrreducibleCharacter.trivial -
              FTtype345_ratio base.MtypeP • tau1 zeta) := by
        apply Finset.sum_congr rfl
        intro i _
        exact hTauAlpha i
      _ = etaColumnTopMiddle base j -
          etaColumnTopMiddle base IrreducibleCharacter.trivial -
          (∑ _i : IrreducibleCharacter W₁ ℂ,
            FTtype345_ratio base.MtypeP • tau1 zeta) := by
        simp only [etaColumnTopMiddle]
        rw [Finset.sum_sub_distrib, Finset.sum_sub_distrib]
      _ = etaColumnTopMiddle base j -
          etaColumnTopMiddle base IrreducibleCharacter.trivial -
          ((FTtype345_TIirr_degree base.MtypeP : ℂ) - 1) • tau1 zeta := by
        rw [ftType34SumConstSmulMiddle
          (Q := (⊤ : Subgroup G))
          (I := IrreducibleCharacter W₁ ℂ), hcardI, hratio]
  have hmapped :
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau base.maxM (alphaMiddle base zeta i j)) =
        ftType345Tau base.maxM
            (muMiddle base j -
              (FTtype345_TIirr_degree base.MtypeP : ℂ) • zeta) -
          ftType345Tau base.maxM
            (muMiddle base IrreducibleCharacter.trivial - zeta) := by
    calc
      (∑ i : IrreducibleCharacter W₁ ℂ,
          ftType345Tau base.maxM (alphaMiddle base zeta i j)) =
          ftType345Tau base.maxM
            (∑ i : IrreducibleCharacter W₁ ℂ,
              alphaMiddle base zeta i j) := by rw [map_sum]
      _ = ftType345Tau base.maxM
          (muMiddle base j -
            (FTtype345_TIirr_degree base.MtypeP : ℂ) • zeta -
            (muMiddle base IrreducibleCharacter.trivial - zeta)) := by
        rw [hsumAlpha]
      _ = ftType345Tau base.maxM
            (muMiddle base j -
              (FTtype345_TIirr_degree base.MtypeP : ℂ) • zeta) -
          ftType345Tau base.maxM
            (muMiddle base IrreducibleCharacter.trivial - zeta) := by
        rw [map_sub]
  rw [hsumTauAlpha, hzero] at hmapped
  have hsolve := sub_eq_iff_eq_add.mp hmapped.symm
  rw [hsolve]
  module

/-! The sole cross-phase interface.  The outer nonorthogonality phase chooses
and normalizes `tau1`; this coefficient phase consumes that normalized witness
and returns the corresponding nontrivial theta-column identity. -/

namespace FTType34StructureInternal

theorem ftType34_constants34
    (base : FTType34Base M U W W₁ W₂ defW) :
    FTtype345_TIirr_degree base.MtypeP = base.u ∧
      FTtype345_TIsign base.MtypeP = 1 ∧
      FTtype345_ratio base.MtypeP = ((ftType34S1 base).card : ℂ) := by
  have hSCard := ftType34S1CardMulQMiddle base
    (ftType34S1_irreducible34 base) (ftType34S1_degree34 base)
  exact ftType34ConstantsMiddle base hSCard
    (fun j hj ↦ ftType34_mu_degree11 base j hj)

theorem ftType34TauThetaFromNormalizedMiddle
    (base : FTType34Base M U W W₁ W₂ defW)
    (zeta : ClassFunction M ℂ)
    (hzeta : zeta ∈ ftType34S1 base)
    (tau1 : ClassFunction M ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (hcoh : coherent_with
      (↑(ftType34S1 base) : Set (ClassFunction M ℂ))
      (nonidentitySet M) (ftType345Tau base.maxM) tau1)
    (hzero : ftType345Tau base.maxM
        (base.primeTI.primeTIRed base.isoM
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
          zeta) =
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage
          (i, (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂ ℂ))) - tau1 zeta)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ftType345Tau base.maxM
        (base.primeTI.primeTIRed base.isoM j -
          (base.u : ℂ) • zeta) =
      (∑ i : IrreducibleCharacter W₁ ℂ,
        base.isoG.cyclicTIImage (i, j)) -
          (base.u : ℂ) • tau1 zeta := by
  have hzeroMiddle : ftType345Tau base.maxM
      (muMiddle base
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
        zeta) =
    etaColumnTopMiddle base
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
      tau1 zeta := by
    simpa only [muMiddle, etaColumnTopMiddle, etaTopMiddle] using hzero
  have hirr := ftType34S1_irreducible34 base
  have hdegree := ftType34S1_degree34 base
  have hSCard := ftType34S1CardMulQMiddle base hirr hdegree
  obtain ⟨hd, hdelta, _hratio⟩ :=
    ftType34ConstantsMiddle base hSCard
      (fun k hk ↦ ftType34_mu_degree11 base k hk)
  have hTauAlpha : ∀ i : IrreducibleCharacter W₁ ℂ,
      ftType345Tau base.maxM (alphaMiddle base zeta i j) =
        etaTopMiddle base i j -
          etaTopMiddle base i
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) -
          FTtype345_ratio base.MtypeP • tau1 zeta := by
    intro i
    exact ftType34TauAlphaFromNormalizedMiddle base zeta hzeta tau1 hcoh
      hzeroMiddle i j hj
  have htheta := ftType34BalancingIdentityTopMiddle base zeta tau1 j
    hTauAlpha hzeroMiddle hd hdelta
  simpa only [muMiddle, etaColumnTopMiddle, etaTopMiddle, hd] using htheta

end FTType34StructureInternal

end

end Submission.OddOrder.PF
