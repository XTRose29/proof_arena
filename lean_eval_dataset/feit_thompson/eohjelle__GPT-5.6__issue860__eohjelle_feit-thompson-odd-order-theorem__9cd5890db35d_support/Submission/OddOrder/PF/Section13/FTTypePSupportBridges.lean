import Submission.OddOrder.PF.Section07.CoherentFrobeniusPartition
import Submission.OddOrder.PF.Section07.DadeCoverSeqInd
import Submission.OddOrder.PF.Section13.FTTypePRegularCore
import Submission.OddOrder.BG.Section03.RegularPrimeProduct

/-!
# Peterfalvi Section 13: type-P supports and cross-type bridges

This file ports `PFsection13.v`, lines 1659--2191: Peterfalvi
(13.17)--(13.19).  The bridge characters use the canonical prime-TI
rectangle and Dade maps supplied by `FTTypePSetupContext`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) ftTypePSupportBridgesFintype
    (X : Type*) [Finite X] : Fintype X :=
  Fintype.ofFinite X

local instance ftTypePSupportBridgesInvertibleCard
    {Q : Type*} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

local instance (Q : Type*) [Group Q] [Fintype Q] :
    One (ClassFunction Q ℂ) where
  one := ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
    ClassFunction Q ℂ)

@[simp]
private theorem ftTypePSupportBridgesOne_apply
    {Q : Type*} [Group Q] [Fintype Q] (x : Q) :
    (1 : ClassFunction Q ℂ) x = 1 := by
  exact IrreducibleCharacter.trivial_apply x

/-! ## Canonical type-P bridge characters -/

private def FTtypePBridgeInducingSubgroup
    (S W₁ : Subgroup G) : Subgroup S :=
  (Fitting_core S).subgroupOf S ⊔ W₁.subgroupOf S

/-- A canonical representative of the source index `#1 : Iirr W₂`. -/
private noncomputable def FTtypePBridgeIndex
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    IrreducibleCharacter W₂ ℂ := by
  letI : IsCyclic W₂ := ctx.primeTI.fixed_cyclic
  exact Classical.choose
    (IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctx.primeTI.prime_cycTIhyp.one_lt_card_right)

private theorem FTtypePBridgeIndex_ne_trivial
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    FTtypePBridgeIndex ctx ≠
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ) := by
  letI : IsCyclic W₂ := ctx.primeTI.fixed_cyclic
  exact Classical.choose_spec
    (IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctx.primeTI.prime_cycTIhyp.one_lt_card_right)

/-- `PFsection13.v: FTtypeP_bridge`. -/
def FTtypeP_bridge
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction S ℂ :=
  ClassFunction.induce (FTtypePBridgeInducingSubgroup S W₁)
      ((IrreducibleCharacter.trivial :
          IrreducibleCharacter (FTtypePBridgeInducingSubgroup S W₁) ℂ) :
        ClassFunction (FTtypePBridgeInducingSubgroup S W₁) ℂ) -
    ctx.primeTI.primeTICharacter ctx.isoS
      IrreducibleCharacter.trivial j

/-- `PFsection13.v: FTtypeP_bridge_gap`. -/
def FTtypeP_bridge_gap
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ClassFunction G ℂ :=
  ctx.tau (FTtypeP_bridge ctx (FTtypePBridgeIndex ctx)) -
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) +
    ctx.eta IrreducibleCharacter.trivial (FTtypePBridgeIndex ctx)

/-! ## Source-facing support and family adapters -/

private def subgroupPullbackSet
    (M : Subgroup G) (A : Set G) : Set M :=
  {x | (x : G) ∈ A}

/-- The source support `'A0(S)`, displayed in the subgroup type `S`. -/
def FTtypePBridgeDadeSupport (S : Subgroup G) : Set S :=
  subgroupPullbackSet S (ftSupport0 S)

/-- The source support `P^# :|: V_S` from (13.18)(a). -/
def FTtypePBridgeCoreSupport
    (S W W₁ W₂ : Subgroup G) : Set S :=
  subgroupPullbackSet S
    (subgroupNonidentity (Fitting_core S) ∪
      classSupportWithin S (cyclicTISet W W₁ W₂))

private def irreducibleClassFunctionFamily
    (Q : Type u) [Group Q] [Fintype Q] :
    Finset (ClassFunction Q ℂ) :=
  Finset.univ.image fun chi : IrreducibleCharacter Q ℂ ↦
    (chi : ClassFunction Q ℂ)

/-- The canonical source family `map sigma (irr W)`. -/
def FTtypePCyclicImageFamily
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Finset (ClassFunction G ℂ) :=
  (irreducibleClassFunctionFamily W).image
    (ctx.targetMap.comp ctx.isoG.linearMap)

/-- Congruence of an integral character pairing to one modulo two. -/
def oddCharacterPairing
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ) : Prop :=
  ∃ n : ℤ, characterPairing phi psi = (((2 * n + 1 : ℤ) : ℂ))

/-- Source `tauL = FT_DadeF maxL`, transported from the ambient top
subgroup to `G`. -/
def FTtype1Dade
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G)) :
    ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  (ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom).comp
    (Dade (FT_DadeF_hyp L maxL))

/-- Source `e = |L : H|`, where `H = L`_F`. -/
def FTtype1CoreIndex (L : Subgroup G) : ℕ :=
  (FTType1FittingIn L).index

/-- Source `betaL = Ind[L,H] 1 - phi`. -/
def FTtype1Bridge
    (L : Subgroup G) (phi : ClassFunction L ℂ) :
    ClassFunction L ℂ :=
  ClassFunction.induce (FTType1FittingIn L)
      ((IrreducibleCharacter.trivial :
          IrreducibleCharacter (FTType1FittingIn L) ℂ) :
        ClassFunction (FTType1FittingIn L) ℂ) -
    phi

private theorem semiregularConjugation_mono_right_primeOddNormal
    {G : Type u} [Group G] {H A R : Subgroup G}
    (hAR : A ≤ R) (hreg : IsSemiregularConjugation H R) :
    IsSemiregularConjugation H A := by
  intro a ha h hfix
  let aR : R := ⟨(a : G), hAR a.property⟩
  have haR : aR ≠ 1 := by
    intro haROne
    apply ha
    apply Subtype.ext
    exact congrArg (fun x : R ↦ (x : G)) haROne
  exact hreg aR haR h hfix

/-- Every subgroup of a cyclic group is characteristic. -/
private theorem subgroup_characteristic_of_isCyclic_primeOddNormal
    {C : Type*} [Group C] [IsCyclic C] (K : Subgroup C) :
    K.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  obtain ⟨m, hm⟩ := e.toMonoidHom.map_cyclic
  rintro _ ⟨x, hx, rfl⟩
  rw [hm]
  exact K.zpow_mem hx m

/-- The downstream part of Coq `prime_odd_regular_normal`.

This isolates the only unavailable input from the source proof: every
prime-power subgroup of the odd semiregular actor is cyclic.  The remainder
is the original Fitting/omega-one argument and concludes relative normality
of the given prime-order subgroup. -/
private theorem prime_odd_regular_normal_of_cyclic_pSubgroups
    {G : Type u} [Group G] [Finite G]
    (H R P : Subgroup G)
    (hPprime : (Nat.card P).Prime)
    (hRodd : Odd (Nat.card R))
    (hPR : P ≤ R)
    (hHne : H ≠ ⊥)
    (hRnormH : R ≤ Subgroup.normalizer (H : Set G))
    (hreg : IsSemiregularConjugation H R)
    (hcyc : ∀ (q : ℕ), q.Prime → ∀ Q : Subgroup R,
      IsPGroup q Q → IsCyclic Q) :
    (P.subgroupOf R).Normal := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let p := Nat.card P
  let PR : Subgroup R := P.subgroupOf R
  have hp : p.Prime := by simpa only [p] using hPprime
  letI : Fact p.Prime := ⟨hp⟩
  have hcardPR : Nat.card PR = p := by
    simpa only [PR, p] using
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hPR
  have hPRp : IsPGroup p PR := by
    apply IsPGroup.of_card (n := 1)
    simpa only [pow_one] using hcardPR

  have hRz : IsZGroup R :=
    { isZGroup := fun q hq Q ↦ hcyc q hq Q Q.isPGroup' }
  letI : IsZGroup R := hRz
  letI : IsSolvable R := by infer_instance

  obtain ⟨S, hPRS⟩ := hPRp.exists_le_sylow
  have hPRcentF :
      PR ≤ Subgroup.centralizer (fittingCore R : Set R) := by
    apply Subgroup.le_centralizer_iff.mpr
    rw [fittingCore]
    apply iSup_le
    intro q
    letI : Fact (q : ℕ).Prime := ⟨q.property⟩
    by_cases hqp : (q : ℕ) = p
    · have hcoreEq : pCore (q : ℕ) R = pCore p R := by
        exact congrArg (fun r : ℕ ↦ pCore r R) hqp
      rw [hcoreEq]
      letI : IsCyclic S := by infer_instance
      letI : IsMulCommutative S := inferInstance
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      let xS : S := ⟨x, pCore_le_sylow S hx⟩
      let yS : S := ⟨y, hPRS hy⟩
      exact congrArg Subtype.val (mul_comm' yS xS)
    · let Q : Subgroup R := pCore (q : ℕ) R
      have hQq : IsPGroup (q : ℕ) Q := by
        simpa only [Q] using
          (pCore_isPGroup (p := (q : ℕ)) (G := R))
      have hQnormal : Q.Normal := by
        dsimp only [Q]
        infer_instance
      letI : Q.Normal := hQnormal
      by_cases hQbot : Q = ⊥
      · rw [show pCore (q : ℕ) R = ⊥ by simpa only [Q] using hQbot]
        exact bot_le
      · have hQcyc : IsCyclic Q := hcyc (q : ℕ) q.property Q hQq
        letI : IsCyclic Q := hQcyc
        let Omega : Subgroup R := (omegaOne (q : ℕ) Q).map Q.subtype
        have hOmegaNormal : Omega.Normal := by
          dsimp only [Omega]
          infer_instance
        letI : Omega.Normal := hOmegaNormal
        have hOmegaq : IsPGroup (q : ℕ) Omega := by
          dsimp only [Omega]
          exact (omegaOne_isPGroup (q : ℕ) hQq).map Q.subtype
        have hQcardNe : Nat.card Q ≠ 1 :=
          (Q.one_lt_card_iff_ne_bot.mpr hQbot).ne'
        have hOmegaCard : Nat.card Omega = (q : ℕ) := by
          dsimp only [Omega]
          rw [Subgroup.card_map_of_injective Q.subtype_injective]
          exact card_omegaOne_of_isCyclic_isPGroup
            q.property hQq hQcardNe
        have hpq : p ≠ (q : ℕ) := Ne.symm hqp
        have hdis : Disjoint PR Omega :=
          IsPGroup.disjoint_of_ne p (q : ℕ) hpq PR Omega hPRp hOmegaq
        let J : Subgroup R := PR ⊔ Omega
        have hPRJ : PR ≤ J := by
          dsimp only [J]
          exact le_sup_left
        have hOmegaJ : Omega ≤ J := by
          dsimp only [J]
          exact le_sup_right
        have hcardJ : Nat.card J = p * (q : ℕ) := by
          dsimp only [J]
          rw [natCard_sup_eq_mul_of_disjoint_of_le_normalizer hdis
            Subgroup.le_normalizer_of_normal, hcardPR, hOmegaCard]
        let A : Subgroup G := J.map R.subtype
        have hAR : A ≤ R := by
          dsimp only [A]
          exact Subgroup.map_subtype_le J
        have hcardA : Nat.card A = p * (q : ℕ) := by
          dsimp only [A]
          rw [Subgroup.card_map_of_injective R.subtype_injective, hcardJ]
        have hAnormH : A ≤ Subgroup.normalizer (H : Set G) :=
          hAR.trans hRnormH
        have hregA : IsSemiregularConjugation H A :=
          semiregularConjugation_mono_right_primeOddNormal hAR hreg
        have hAcyc : IsCyclic A :=
          Submission.OddOrder.BG.Section03.regular_pq_group_cyclic
            hp q.property hpq hcardA hHne hAnormH hregA
        let eJ : J ≃* A :=
          Subgroup.equivMapOfInjective J R.subtype R.subtype_injective
        have hJcyc : IsCyclic J := eJ.isCyclic.mpr hAcyc
        letI : IsCyclic J := hJcyc
        letI : IsMulCommutative J := inferInstance
        have hPRcentOmega :
            PR ≤ Subgroup.centralizer (Omega : Set R) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          let xJ : J := ⟨x, hPRJ hx⟩
          let yJ : J := ⟨y, hOmegaJ hy⟩
          exact congrArg Subtype.val (mul_comm' yJ xJ)
        have hPRnormQ : PR ≤ Subgroup.normalizer (Q : Set R) := by
          rw [Q.normalizer_eq_top]
          exact le_top
        have hcopQPR : Nat.Coprime (Nat.card Q) (Nat.card PR) :=
          IsPGroup.coprime_card_of_ne (q : ℕ) p hqp Q PR hQq hPRp
        have hQodd : Odd (Nat.card Q) :=
          hRodd.of_dvd_nat Q.card_subgroup_dvd_card
        have hPRcentQ : PR ≤ Subgroup.centralizer (Q : Set R) :=
          coprime_odd_faithful_omegaOne_of_odd_card
            hQq hPRnormQ hcopQPR hQodd hPRcentOmega
        change Q ≤ Subgroup.centralizer (PR : Set R)
        exact Subgroup.le_centralizer_iff.mp hPRcentQ

  have hPRF : PR ≤ fittingCore R :=
    hPRcentF.trans centralizer_fittingCore_le
  let F : Subgroup R := fittingCore R
  let PF : Subgroup F := PR.subgroupOf F
  have hPFp : IsPGroup p PF :=
    hPRp.of_equiv (Subgroup.subgroupOfEquivOfLe hPRF).symm
  have hPFcore : PF ≤ pCore p F := by
    exact hPFp.le_pCore_of_isNilpotent
  have hPRcore : PR ≤ pCore p R := by
    calc
      PR = PF.map F.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hPRF).symm
      _ ≤ (pCore p F).map F.subtype := Subgroup.map_mono hPFcore
      _ = pCore p R := by
        simpa only [F] using map_pCore_fittingCore_eq_pCore R p

  have hcoreCyc : IsCyclic (pCore p R) :=
    hcyc p hp (pCore p R) pCore_isPGroup
  letI : IsCyclic (pCore p R) := hcoreCyc
  let K : Subgroup (pCore p R) := PR.subgroupOf (pCore p R)
  have hKchar : K.Characteristic :=
    subgroup_characteristic_of_isCyclic_primeOddNormal K
  letI : K.Characteristic := hKchar
  have hmapNormal : (K.map (pCore p R).subtype).Normal := by
    infer_instance
  have hPRnormal : PR.Normal := by
    simpa only [K, Subgroup.map_subgroupOf_eq_of_le hPRcore] using hmapNormal
  simpa only [PR] using hPRnormal

/-- Solvable-kernel wrapper sufficient for the PF13 application.

This has the source theorem's hypotheses plus solvability of `H`, and uses
the existing Section 12 port of `odd_regular_pgroup_cyclic` to discharge the
cyclic-prime-power-subgroup input above. -/
private theorem prime_odd_regular_normal_of_solvable_kernel
    {G : Type u} [Group G] [Finite G]
    (H R P : Subgroup G)
    (hPprime : (Nat.card P).Prime)
    (hRodd : Odd (Nat.card R))
    (hPR : P ≤ R)
    (hHsol : IsSolvable H)
    (hHne : H ≠ ⊥)
    (hRnormH : R ≤ Subgroup.normalizer (H : Set G))
    (hreg : IsSemiregularConjugation H R) :
    (P.subgroupOf R).Normal := by
  classical
  apply prime_odd_regular_normal_of_cyclic_pSubgroups
    H R P hPprime hRodd hPR hHne hRnormH hreg
  intro q hq Q hQq
  letI : Fact q.Prime := ⟨hq⟩
  let A : Subgroup G := Q.map R.subtype
  have hAR : A ≤ R := by
    dsimp only [A]
    exact Subgroup.map_subtype_le Q
  have hAq : IsPGroup q A := by
    dsimp only [A]
    exact hQq.map R.subtype
  have hAodd : Odd (Nat.card A) :=
    hRodd.of_dvd_nat (Subgroup.card_dvd_of_le hAR)
  have hAnormH : A ≤ Subgroup.normalizer (H : Set G) :=
    hAR.trans hRnormH
  have hregA : IsSemiregularConjugation H A :=
    semiregularConjugation_mono_right_primeOddNormal hAR hreg
  have hAcyc : IsCyclic A :=
    Submission.OddOrder.BG.Section12.quotient_regular_qgroup_isCyclic_12_12
      hAq hAodd hAnormH hHsol hHne hregA
  let eQ : Q ≃* A :=
    Subgroup.equivMapOfInjective Q R.subtype R.subtype_injective
  exact eQ.isCyclic.mpr hAcyc

/-- PF13-facing form with the exact integration signature.  In the minimal
odd simple ambient group, semiregularity together with the prime-order
subgroup forces `H < ⊤`: a nonidentity element of `P` would otherwise be
a nonidentity fixed point of its own conjugation action on `H = ⊤`.
Thus `mFT_sol` supplies the one additional hypothesis needed by the existing
Lean port of `odd_regular_pgroup_cyclic`. -/
private theorem supportBridges_prime_odd_regular_normal
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {H R P : Subgroup G}
    (hP : (Nat.card P).Prime)
    (hRodd : Odd (Nat.card R))
    (hPR : P ≤ R)
    (hHne : H ≠ ⊥)
    (hNorm : R ≤ Subgroup.normalizer (H : Set G))
    (hreg : IsSemiregularConjugation H R) :
    (P.subgroupOf R).Normal := by
  have hPne : P ≠ ⊥ := by
    rw [← P.one_lt_card_iff_ne_bot]
    exact hP.one_lt
  obtain ⟨x, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hPne
  let xR : R := ⟨(x : G), hPR x.property⟩
  have hxRne : xR ≠ 1 := by
    intro hxOne
    apply hxne
    apply Subtype.ext
    exact congrArg (fun z : R ↦ (z : G)) hxOne
  have hHproper : H < ⊤ := by
    apply lt_top_iff_ne_top.mpr
    intro hHtop
    let xH : H := ⟨(x : G), by rw [hHtop]; trivial⟩
    have hfix :
        (xR : G) * (xH : G) * (xR : G)⁻¹ = (xH : G) := by
      dsimp only [xR, xH]
      group
    have hxHOne : xH = 1 := hreg xR hxRne xH hfix
    apply hxne
    apply Subtype.ext
    exact congrArg (fun z : H ↦ (z : G)) hxHOne
  exact prime_odd_regular_normal_of_solvable_kernel
    H R P hP hRodd hPR (mFT_sol hHproper) hHne hNorm hreg

/-! ## Peterfalvi (13.17) -/

private theorem supportBridges_exists_mem_ne_one13
    {A : Subgroup G} (hA : A ≠ ⊥) :
    ∃ x : G, x ∈ A ∧ x ≠ 1 := by
  by_contra h
  push_neg at h
  apply hA
  ext x
  constructor
  · intro hx
    exact Subgroup.mem_bot.mpr (h x hx)
  · intro hx
    simpa [Subgroup.mem_bot.mp hx] using A.one_mem

/-! A numerical Hall transport used in the conjugate-`S` branch. -/

private theorem supportBridges_isHall_primeSupport_of_card_eq13
    {A B K L : Subgroup G}
    (hAK : A ≤ K) (hBL : B ≤ L)
    (hAB : Nat.card A = Nat.card B)
    (hKL : Nat.card K = Nat.card L)
    (hA : IsHall (primeSupport (Nat.card A)) (A.subgroupOf K)) :
    IsHall (primeSupport (Nat.card B)) (B.subgroupOf L) := by
  have hBmul : Nat.card B * (B.subgroupOf L).index = Nat.card L := by
    simpa only [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hBL]
      using (B.subgroupOf L).card_mul_index
  have hAmul : Nat.card A * (A.subgroupOf K).index = Nat.card K := by
    simpa only [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hAK]
      using (A.subgroupOf K).card_mul_index
  have hindex : (B.subgroupOf L).index = (A.subgroupOf K).index := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := A))
    calc
      Nat.card A * (B.subgroupOf L).index =
          Nat.card B * (B.subgroupOf L).index := by rw [hAB]
      _ = Nat.card L := hBmul
      _ = Nat.card K := hKL.symm
      _ = Nat.card A * (A.subgroupOf K).index := hAmul.symm
  have hcop : (Nat.card (B.subgroupOf L)).Coprime
      (B.subgroupOf L).index := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hBL,
      ← hAB, hindex]
    simpa only [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hAK]
      using hA.coprime_card_index
  simpa only [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hBL]
    using isHall_primeSupport (B.subgroupOf L) hcop

/-! A type-P maximal and a type-I maximal have coprime Fitting cores. -/

private theorem supportBridges_typeOneFitting_coprime_typeP13
    {T V A B C : Subgroup G}
    {defC : IsInternalDirectProductIn A B C}
    (ctxT : FTTypePSetupContext T V C A B defC)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1) :
    Nat.Coprime (Nat.card (Fitting_core L))
      (Nat.card (Fitting_core T)) := by
  have hnot : ¬ FTAmbientConjugate L T := by
    rintro ⟨g, hTmap⟩
    have htype : FTtype T = FTtype L := by
      rw [hTmap]
      exact FTtypeJ L g
    exact FTtypeP_neq1 T V C A B defC ctxT.maxS ctxT.StypeP
      (htype.trans Ltype1)
  have hcop :=
    (FT_Dade_support_partition (G := G)).2.1 maxL ctxT.maxS hnot
  have hcoreL : ftCore L = Fitting_core L :=
    FTcore_type1 L Ltype1
  rw [hcoreL] at hcop
  rcases (FTtypeP_facts ctxT).1 with htype2 | htype3
  · have hcoreT : ftCore T = Fitting_core T :=
      FTcore_type2 T htype2
    simpa only [hcoreT] using hcop
  · have hgt : 2 < FTtype T := by omega
    have hcoreT : ftCore T = derivedWithin T :=
      FTcore_type_gt2 T hgt
    rw [hcoreT] at hcop
    exact hcop.coprime_dvd_right
      (Subgroup.card_dvd_of_le ctxT.StypeP.2.1.2.2.2.1)

/-! Frobenius centralizer adapters. -/

private theorem supportBridges_centralizer_frobeniusKernel_le13
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
  have hrRne : rR ≠ 1 := by
    intro hrOne
    apply hxK
    have hrOneQ : r = 1 := congrArg Subtype.val hrOne
    have hxOne : x = 1 := by
      calc
        x = (k : Q) * r * (k : Q)⁻¹ := hrx'.symm
        _ = 1 := by rw [hrOneQ]; simp
    exact hxOne ▸ K.one_mem
  have hzKconj : (k : Q)⁻¹ * z * (k : Q) ∈ K := by
    simpa using hFrob.kernel_normal.conj_mem z hzK (k : Q)⁻¹
  let zK : K := ⟨(k : Q)⁻¹ * z * (k : Q), hzKconj⟩
  have hzKne : zK ≠ 1 := by
    intro hzKOne
    apply hzOne
    have hval := congrArg Subtype.val hzKOne
    dsimp only [zK] at hval
    calc
      z = (k : Q) * ((k : Q)⁻¹ * z * (k : Q)) * (k : Q)⁻¹ := by
        group
      _ = 1 := by rw [hval]; simp
  have hxcomm : Commute x z := by
    show x * z = z * x
    exact (Subgroup.mem_centralizer_iff.mp hx z
      (Subgroup.mem_zpowers z)).symm
  have hxfix : x * z * x⁻¹ = z := by
    calc
      x * z * x⁻¹ = z * x * x⁻¹ := by rw [hxcomm.eq]
      _ = z := by simp
  have hfix : (rR : Q) * (zK : Q) * (rR : Q)⁻¹ = (zK : Q) := by
    change r * ((k : Q)⁻¹ * z * (k : Q)) * r⁻¹ =
      (k : Q)⁻¹ * z * (k : Q)
    calc
      r * ((k : Q)⁻¹ * z * (k : Q)) * r⁻¹ =
          (k : Q)⁻¹ *
            (((k : Q) * r * (k : Q)⁻¹) * z *
              ((k : Q) * r * (k : Q)⁻¹)⁻¹) * (k : Q) := by
        group
      _ = (k : Q)⁻¹ * (x * z * x⁻¹) * (k : Q) := by rw [hrx']
      _ = (k : Q)⁻¹ * z * (k : Q) := by rw [hxfix]
  exact hzKne (hFrob.fixedPointFree rR hrRne zK hfix)

private theorem supportBridges_centralizer_frobeniusIn_kernel_le13
    {H E L : Subgroup G}
    (hFrob : IsFrobeniusIn H E L)
    {z x : G} (hzH : z ∈ H) (hzOne : z ≠ 1)
    (hxL : x ∈ L)
    (hxCent : x ∈ Subgroup.centralizer
      (Subgroup.zpowers z : Set G)) :
    x ∈ H := by
  let J : Subgroup G := H ⊔ E
  have hzJmem : z ∈ J := (show H ≤ J from le_sup_left) hzH
  have hxJmem : x ∈ J := by
    change x ∈ H ⊔ E
    rw [hFrob.1]
    exact hxL
  let zJ : J := ⟨z, hzJmem⟩
  let xJ : J := ⟨x, hxJmem⟩
  have hzJH : zJ ∈ H.subgroupOf J := hzH
  have hzJOne : zJ ≠ 1 := by
    intro hz
    exact hzOne (congrArg (fun y : J ↦ (y : G)) hz)
  have hxJCent : xJ ∈ Subgroup.centralizer
      (Subgroup.zpowers zJ : Set J) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : Commute z x := by
      show z * x = x * z
      exact Subgroup.mem_centralizer_iff.mp hxCent z
        (Subgroup.mem_zpowers z)
    apply Subtype.ext
    exact (hcomm.zpow_left n).eq
  exact supportBridges_centralizer_frobeniusKernel_le13
    hFrob.2.2 hzJH hzJOne hxJCent

private theorem supportBridges_frobenius_kernel_centralizer_eq_bot13
    {K R : Subgroup G}
    (hFrob : IsFrobeniusDecomposition
      (K.subgroupOf (K ⊔ R)) (R.subgroupOf (K ⊔ R))) :
    centralizerWithin K R = ⊥ := by
  let J : Subgroup G := K ⊔ R
  change IsFrobeniusDecomposition
    (K.subgroupOf J) (R.subgroupOf J) at hFrob
  have hKJ : K ≤ J := by
    dsimp only [J]
    exact le_sup_left
  have hRJ : R ≤ J := by
    dsimp only [J]
    exact le_sup_right
  rw [eq_bot_iff]
  intro x hx
  apply Subgroup.mem_bot.mpr
  have hRne : R ≠ ⊥ := by
    intro hbot
    apply hFrob.complement_ne_bot
    ext r
    simp [hbot]
  obtain ⟨r, hrR, hrOne⟩ :=
    supportBridges_exists_mem_ne_one13 hRne
  have hrJoin : r ∈ J := hRJ hrR
  have hxJoin : x ∈ J := hKJ hx.1
  let rJ : R.subgroupOf J := ⟨⟨r, hrJoin⟩, hrR⟩
  let xJ : K.subgroupOf J := ⟨⟨x, hxJoin⟩, hx.1⟩
  have hrJ : rJ ≠ 1 := by
    intro hr
    have hrAmbient : r = (1 : G) :=
      congrArg
        (fun z : R.subgroupOf J ↦ (((z : J) : G))) hr
    exact hrOne hrAmbient
  have hcomm : r * x = x * r :=
    (mem_centralizerWithin.mp hx).2 r hrR
  have hfix : (rJ : J) * (xJ : J) * (rJ : J)⁻¹ = (xJ : J) := by
    apply Subtype.ext
    simpa [rJ, xJ, mul_assoc] using
      congrArg (fun z : G ↦ z * r⁻¹) hcomm
  have hxOne : xJ = 1 := hFrob.fixedPointFree rJ hrJ xJ hfix
  have hxAmbient : x = (1 : G) :=
    congrArg
      (fun z : K.subgroupOf J ↦ (((z : J) : G))) hxOne
  exact hxAmbient

private theorem supportBridges_frobeniusDecomp_semiregular13
    {H E : Subgroup G}
    (hFrob : IsFrobeniusDecomposition
      (H.subgroupOf (H ⊔ E)) (E.subgroupOf (H ⊔ E))) :
    IsSemiregularConjugation H E := by
  let J : Subgroup G := H ⊔ E
  change IsFrobeniusDecomposition
    (H.subgroupOf J) (E.subgroupOf J) at hFrob
  have hHJ : H ≤ J := by
    dsimp only [J]
    exact le_sup_left
  have hEJ : E ≤ J := by
    dsimp only [J]
    exact le_sup_right
  intro e he h hfix
  let eJ : E.subgroupOf J :=
    ⟨⟨(e : G), hEJ e.property⟩, e.property⟩
  let hJ : H.subgroupOf J :=
    ⟨⟨(h : G), hHJ h.property⟩, h.property⟩
  have heJ : eJ ≠ 1 := by
    intro heOne
    apply he
    apply Subtype.ext
    exact congrArg
      (fun z : E.subgroupOf J ↦ (((z : J) : G))) heOne
  have hfixJ : (eJ : J) * (hJ : J) * (eJ : J)⁻¹ = (hJ : J) := by
    apply Subtype.ext
    exact hfix
  have hhOne : hJ = 1 := hFrob.fixedPointFree eJ heJ hJ hfixJ
  apply Subtype.ext
  exact congrArg
    (fun z : H.subgroupOf J ↦ (((z : J) : G))) hhOne
private theorem supportBridges_frobeniusIn_semiregular13
    {H E L : Subgroup G} (hFrob : IsFrobeniusIn H E L) :
    IsSemiregularConjugation H E :=
  supportBridges_frobeniusDecomp_semiregular13 hFrob.2.2

private theorem supportBridges_isFrobeniusIn_map13
    {H E L : Subgroup G} (h : IsFrobeniusIn H E L) (e : G ≃* G) :
    IsFrobeniusIn (H.map e.toMonoidHom) (E.map e.toMonoidHom)
      (L.map e.toMonoidHom) := by
  let J := H ⊔ E
  let J' := H.map e.toMonoidHom ⊔ E.map e.toMonoidHom
  have hJ : J.map e.toMonoidHom = J' := by
    dsimp only [J, J']
    rw [Subgroup.map_sup]
  let eJ : J ≃* J' :=
    (e.subgroupMap J).trans (MulEquiv.subgroupCongr hJ)
  have hHmap :
      (H.subgroupOf J).map eJ.toMonoidHom =
        (H.map e.toMonoidHom).subgroupOf J' := by
    ext y
    rw [Subgroup.mem_map_equiv]
    change e.symm (y : G) ∈ H ↔ (y : G) ∈ H.map e.toMonoidHom
    rw [Subgroup.mem_map_equiv]
  have hEmap :
      (E.subgroupOf J).map eJ.toMonoidHom =
        (E.map e.toMonoidHom).subgroupOf J' := by
    ext y
    rw [Subgroup.mem_map_equiv]
    change e.symm (y : G) ∈ E ↔ (y : G) ∈ E.map e.toMonoidHom
    rw [Subgroup.mem_map_equiv]
  have hsd := FTContextInternal.semidirect_map_mulEquiv8 h.2.1 e
  have hfrob := FTContextInternal.frobenius_map_mulEquiv8 h.2.2 eJ
  rw [hHmap, hEmap] at hfrob
  refine ⟨?_, ?_, ?_⟩
  · rw [← Subgroup.map_sup, h.1]
  · simpa only [Subgroup.map_sup] using hsd
  · simpa only [J'] using hfrob

/-! Hall bookkeeping used on the two Frobenius complements. -/

private theorem supportBridges_le_normalHall_of_isPiNumber13
    {pi : Set ℕ} {C K A : Subgroup G}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    (hAC : A ≤ C) (hApi : IsPiNumber pi (Nat.card A)) :
    A ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa only [KC] using hKnormal
  have hcop : (Nat.card A).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro q hq hqA hqIndex
    exact (hKHall.isPiNumber_index hq hqIndex) (hApi hq hqA)
  intro x hxA
  let xC : C := ⟨x, hAC hxA⟩
  let quotientMap : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderA : orderOf (quotientMap xC) ∣ Nat.card A :=
    (orderOf_map_dvd quotientMap xC).trans (by
      simpa [xC] using A.orderOf_dvd_natCard hxA)
  have horderIndex : orderOf (quotientMap xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (quotientMap xC)
  have horderOne : orderOf (quotientMap xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderA horderIndex
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp
      (orderOf_eq_one_iff.mp horderOne)
  exact hxKC

private theorem supportBridges_card_dvd_index_of_disjoint_normal13
    {C K A : Subgroup G}
    (hKC : K ≤ C) (hAC : A ≤ C)
    (hKnormal : (K.subgroupOf C).Normal)
    (hdis : Disjoint K A) :
    Nat.card A ∣ (K.subgroupOf C).index := by
  let KC : Subgroup C := K.subgroupOf C
  let AC : Subgroup C := A.subgroupOf C
  letI : KC.Normal := by simpa only [KC] using hKnormal
  let q : C →* C ⧸ KC := QuotientGroup.mk' KC
  let f : AC →* C ⧸ KC := q.comp AC.subtype
  have hf : Function.Injective f := by
    intro x y hxy
    have hker : q ((x : C) * (y : C)⁻¹) = 1 := by
      change f x * (f y)⁻¹ = 1
      rw [hxy]
      simp
    have hxyK : ((x : C) : G) * ((y : C) : G)⁻¹ ∈ K :=
      (QuotientGroup.eq_one_iff ((x : C) * (y : C)⁻¹)).mp hker
    have hxyA : ((x : C) : G) * ((y : C) : G)⁻¹ ∈ A :=
      A.mul_mem x.property (A.inv_mem y.property)
    have hxyOne : ((x : C) : G) * ((y : C) : G)⁻¹ = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdis]
      exact ⟨hxyK, hxyA⟩
    apply Subtype.ext
    apply Subtype.ext
    exact mul_inv_eq_one.mp hxyOne
  have hdvd : Nat.card AC ∣ Nat.card (C ⧸ KC) :=
    Subgroup.card_dvd_of_injective f hf
  simpa only [AC, KC,
    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hAC,
    KC.index_eq_card] using hdvd

private theorem supportBridges_coprime_fitting_of_disjoint13
    {L A : Subgroup G}
    (hAL : A ≤ L) (hdis : Disjoint (Fitting_core L) A) :
    Nat.Coprime (Nat.card (Fitting_core L)) (Nat.card A) := by
  have hdvd : Nat.card A ∣ ((Fitting_core L).subgroupOf L).index :=
    supportBridges_card_dvd_index_of_disjoint_normal13
      (Fcore_sub L) hAL (Fcore_normal L) hdis
  have hcop : Nat.Coprime (Nat.card (Fitting_core L))
      ((Fitting_core L).subgroupOf L).index := by
    simpa only [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (Fcore_sub L)] using (Fcore_Hall L).coprime_card_index
  exact hcop.coprime_dvd_right hdvd

private theorem supportBridges_frobenius_subgroup_centralizer_eq_bot13
    {H E L A : Subgroup G}
    (hFrob : IsFrobeniusIn H E L)
    (hAne : A ≠ ⊥) (hAL : A ≤ L) (hdis : Disjoint H A) :
    centralizerWithin H A = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  apply Subgroup.mem_bot.mpr
  by_contra hxOne
  have hALH : A ≤ H := by
    intro a ha
    have hcomm : Commute a x := by
      show a * x = x * a
      exact Subgroup.mem_centralizer_iff.mp hx.2 a ha
    have haCent : a ∈ Subgroup.centralizer
        (Subgroup.zpowers x : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (hcomm.symm.zpow_left n).eq
    exact supportBridges_centralizer_frobeniusIn_kernel_le13
      hFrob hx.1 hxOne (hAL ha) haCent
  have hAbot : A = ⊥ := by
    apply le_antisymm _ bot_le
    intro a ha
    apply Subgroup.mem_bot.mpr
    have haInf : a ∈ H ⊓ A := ⟨hALH ha, ha⟩
    have haBot : a ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hdis]
      exact haInf
    exact Subgroup.mem_bot.mp haBot
  exact hAne hAbot

private theorem supportBridges_isHall_inf_of_normal_le13
    {pi : Set ℕ} {H C M : Subgroup G}
    (hHM : H ≤ M) (hCM : C ≤ M)
    (hHnormal : (H.subgroupOf M).Normal)
    (hHHall : IsHall pi (H.subgroupOf M)) :
    IsHall pi ((H ⊓ C).subgroupOf C) := by
  constructor
  · rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      inf_le_right]
    have hHpi : IsPiNumber pi (Nat.card H) := by
      simpa only [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hHM]
        using hHHall.isPiNumber_card
    exact hHpi.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
  · change IsPiNumber piᶜ ((H ⊓ C).relIndex C)
    rw [Subgroup.inf_relIndex_right]
    let HM : Subgroup M := H.subgroupOf M
    let CM : Subgroup M := C.subgroupOf M
    letI : HM.Normal := by simpa only [HM] using hHnormal
    have hdvd : HM.relIndex CM ∣ HM.index :=
      Subgroup.relIndex_dvd_index_of_normal HM CM
    have hrel : HM.relIndex CM = H.relIndex C := by
      simpa only [HM, CM] using
        Subgroup.relIndex_subgroupOf (H := H) hCM
    rw [hrel] at hdvd
    exact hHHall.isPiNumber_index.of_dvd hdvd

private theorem supportBridges_normal_inf_subgroupOf_of_le13
    {M H C : Subgroup G}
    (hHM : H ≤ M) (hCM : C ≤ M)
    (hHnormal : (H.subgroupOf M).Normal) :
    ((H ⊓ C).subgroupOf C).Normal := by
  have hMnormH : M ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHnormal
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  intro c hc
  have hcH := Subgroup.mem_normalizer_iff.mp (hMnormH (hCM hc))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨(hcH x).mp hx.1,
      C.mul_mem (C.mul_mem hc hx.2) (C.inv_mem hc)⟩
  · intro hx
    have hxC : x ∈ C := by
      have hconj : c⁻¹ * (c * x * c⁻¹) * c ∈ C :=
        C.mul_mem (C.mul_mem (C.inv_mem hc) hx.2) hc
      have heq : c⁻¹ * (c * x * c⁻¹) * c = x := by group
      simpa only [heq] using hconj
    exact ⟨(hcH x).mpr hx.1, hxC⟩

private theorem supportBridges_elementary_subgroup13
    {q : ℕ} {Q X : Subgroup G}
    (hQ : IsElementaryAbelianGroup q Q) (hXQ : X ≤ Q) :
    IsElementaryAbelianGroup q X := by
  letI : IsMulCommutative Q := hQ.commutative
  letI : IsMulCommutative X := by
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    apply Subtype.ext
    change (x : G) * (y : G) = (y : G) * (x : G)
    exact congrArg Subtype.val
      (mul_comm' (⟨(x : G), hXQ x.property⟩ : Q)
        (⟨(y : G), hXQ y.property⟩ : Q))
  refine
    { isPGroup := hQ.isPGroup.to_le hXQ
      commutative := inferInstance
      pow_eq_one := ?_ }
  intro x
  apply Subtype.ext
  change (x : G) ^ q = 1
  have hxQ : (⟨(x : G), hXQ x.property⟩ : Q) ^ q = 1 :=
    hQ.pow_eq_one ⟨(x : G), hXQ x.property⟩
  exact congrArg Subtype.val hxQ

private theorem supportBridges_natCard_eq_prime_of_elementary_cyclic13
    {X : Type} [Group X] [Finite X] {q : ℕ}
    (hq : q.Prime) (hX : IsElementaryAbelianGroup q X)
    (hcyclic : IsCyclic X) (hcard : 1 < Nat.card X) :
    Nat.card X = q := by
  letI : Fact q.Prime := ⟨hq⟩
  letI : IsCyclic X := hcyclic
  have hcardNe : Nat.card X ≠ 1 := (ne_of_gt hcard)
  have hOmegaCard : Nat.card (omegaOne q X) = q :=
    card_omegaOne_of_isCyclic_isPGroup hq hX.isPGroup hcardNe
  have hOmegaTop : omegaOne q X = ⊤ := by
    apply top_unique
    intro x _
    exact mem_omegaOne_of_pow_eq_one q (hX.pow_eq_one x)
  rw [hOmegaTop, Subgroup.card_top] at hOmegaCard
  exact hOmegaCard

private theorem supportBridges_hall_complement13
    {K : Type} [Group K] [Finite K]
    {pi : Set ℕ} {A B : Subgroup K}
    (hA : IsHall pi A) (hAB : A.IsComplement' B) :
    IsHall piᶜ B := by
  constructor
  · rw [← hAB.symm.index_eq_card]
    exact hA.isPiNumber_index
  · rw [hAB.index_eq_card]
    simpa using hA.isPiNumber_card

private theorem supportBridges_complementaryHall_isComplement13
    {K : Type} [Group K] [Finite K]
    {pi : Set ℕ} {A B : Subgroup K}
    (hA : IsHall pi A) (hB : IsHall piᶜ B) :
    A.IsComplement' B := by
  have hcop : Nat.Coprime (Nat.card A) (Nat.card B) :=
    hA.isPiNumber_card.coprime_compl hB.isPiNumber_card
  have hdis : Disjoint A B := Subgroup.disjoint_of_coprime_natCard hcop
  apply Subgroup.isComplement'_of_card_mul_and_disjoint _ hdis
  have hBindexPi : IsPiNumber pi B.index := by
    simpa only [compl_compl] using hB.isPiNumber_index
  have hcopIndex : Nat.Coprime B.index A.index :=
    hBindexPi.coprime_compl hA.isPiNumber_index
  have hAcardDvd : Nat.card A ∣ B.index := by
    apply hcop.dvd_of_dvd_mul_left
    rw [B.card_mul_index]
    exact A.card_subgroup_dvd_card
  have hBindexDvd : B.index ∣ Nat.card A := by
    apply hcopIndex.dvd_of_dvd_mul_right
    rw [A.card_mul_index]
    exact B.index_dvd_card
  have hAcard : Nat.card A = B.index :=
    Nat.dvd_antisymm hAcardDvd hBindexDvd
  rw [hAcard, B.index_mul_card]

/-- `PFsection13.v: FTtypeII_support_facts`, Peterfalvi (13.17). -/
theorem FTtypeII_support_facts
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (T L : Subgroup G)
    (Stype2 : FTtype S = 2)
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (Lnormalizer : L ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (U : Set G) : Set G)) :
    (∃ E : Subgroup G,
      IsFrobeniusIn (Fitting_core L) E L) ∧
      U ≤ Fitting_core L ∧
      (IsInternalSemidirectProductIn (Fitting_core L) W₁ L ∨
        ∃ y : G, y ∈ Fitting_core T ∧
          IsInternalSemidirectProductIn (Fitting_core L)
            (W₁ ⊔ conjugateSubgroup8 W₂ y) L) := by
  classical
  let xdefW : IsInternalDirectProductIn W₂ W₁ W := defW.swap
  have pairTS : typeP_pair T S W W₂ W₁ xdefW :=
    typeP_pair_sym S T W W₁ W₂ defW xdefW pairST
  obtain ⟨V, TtypeP⟩ := typeP_pairW T S W W₂ W₁ xdefW pairTS
  let ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW :=
    ⟨pairST.T_maximal, TtypeP⟩

  have maxL : L ∈ minSimple_max_groups (G := G) := Lnormalizer.1
  have hNU_L : Subgroup.normalizer (U : Set G) ≤ L := Lnormalizer.2
  have hUL : U ≤ L := Subgroup.le_normalizer.trans hNU_L
  have hsdS := Ptype_Fcore_sdprod ctx.ptypeCtx
  have hUS : U ≤ S := le_sup_left.trans hsdS.2.1
  have hW₁S : W₁ ≤ S := le_sup_right.trans hsdS.2.1
  have hsdT := Ptype_Fcore_sdprod ctxT.ptypeCtx
  have hQT : Fitting_core T ≤ T := Fcore_sub T

  rcases FTtypeP_facts ctx with
    ⟨_, _, hFrobUW₁, hUcomm, _, _, _, _, _, _⟩
  rcases FTtypeP_facts ctxT with
    ⟨_, _, _, _, hQelem, hQcard, _, _, _, _⟩
  obtain ⟨hq, hp⟩ := FTtypeP_pair_primes S T W W₁ W₂ defW pairST
  letI : Fact (Nat.card W₁).Prime := ⟨hq⟩
  have hqp : Nat.card W₁ ≠ Nat.card W₂ :=
    pairST.cyclic_ti.factor_card_ne
  have hW₁ne : W₁ ≠ ⊥ :=
    W₁.one_lt_card_iff_ne_bot.mp hq.one_lt
  have hW₂ne : W₂ ≠ ⊥ :=
    W₂.one_lt_card_iff_ne_bot.mp hp.one_lt
  have hII := compl_of_typeII S U W W₁ W₂ defW
    ctx.maxS ctx.StypeP Stype2
  have hUne : U ≠ ⊥ := hII.1.2.1
  have hUnotNorm : ¬ Subgroup.normalizer (U : Set G) ≤ S := hII.2.2.1

  have hJoinNormU : U ⊔ W₁ ≤
      Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mp
      hFrobUW₁.kernel_normal
  have hW₁normU : W₁ ≤ Subgroup.normalizer (U : Set G) :=
    le_sup_right.trans hJoinNormU
  have hW₁L : W₁ ≤ L := hW₁normU.trans hNU_L

  have hUHallS :
      IsHall (primeSupport (Nat.card U)) (U.subgroupOf S) := by
    let J : Subgroup G := U ⊔ W₁
    have hUJ : U ≤ J := le_sup_left
    have hJS : J ≤ S := hsdS.2.1
    have hUHallJ :
        IsHall (primeSupport (Nat.card U)) (U.subgroupOf J) := by
      have hcop : (Nat.card (U.subgroupOf J)).Coprime
          (U.subgroupOf J).index := by
        rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUJ,
          hFrobUW₁.isComplement.symm.index_eq_card,
          Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
            (show W₁ ≤ J from le_sup_right)]
        have hregUW₁ : IsSemiregularConjugation U W₁ :=
          supportBridges_frobeniusDecomp_semiregular13 hFrobUW₁
        exact IsSemiregularConjugation.natCard_coprime
          (G := G) (H := U) (R := W₁) hregUW₁
          (le_sup_right.trans hJoinNormU)
      simpa only [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUJ]
        using isHall_primeSupport (U.subgroupOf J) hcop
    have hJHallS :
        IsHall (primeSupport (Nat.card J)) (J.subgroupOf S) := by
      have hcop : (Nat.card (J.subgroupOf S)).Coprime
          (J.subgroupOf S).index := by
        rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hJS,
          hsdS.2.2.2.index_eq_card,
          Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq (Fcore_sub S)]
        exact (Ptype_Fcore_coprime ctx.ptypeCtx).symm
      simpa only [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hJS]
        using isHall_primeSupport (J.subgroupOf S) hcop
    exact TypeSpecInternal.hall_of_le_hall_of_hall16
      hUJ hJS hUHallJ hJHallS (by
        intro r hr
        exact ⟨hr.1, hr.2.trans (Subgroup.card_dvd_of_le hUJ)⟩)

  have Ltype1 : FTtype L = 1 := by
    by_contra hLtype
    rcases pairST.controls_non_type_one L maxL hLtype with hSL | hTL
    · rcases hSL with ⟨g, hLg⟩
      let Ug : Subgroup G := conjugateSubgroup8 U g
      have hUgL : Ug ≤ L := by
        dsimp only [Ug, conjugateSubgroup8]
        rw [hLg]
        exact Subgroup.map_mono hUS
      have hcardSL : Nat.card S = Nat.card L := by
        rw [hLg, Subgroup.card_map_of_injective (MulAut.conj g).injective]
      have hcardUUg : Nat.card U = Nat.card Ug := by
        dsimp only [Ug, conjugateSubgroup8]
        rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
      have hUgHallL :
          IsHall (primeSupport (Nat.card Ug)) (Ug.subgroupOf L) :=
        supportBridges_isHall_primeSupport_of_card_eq13
          hUS hUgL hcardUUg hcardSL hUHallS
      have hUHallL :
          IsHall (primeSupport (Nat.card U)) (U.subgroupOf L) :=
        supportBridges_isHall_primeSupport_of_card_eq13
          hUS hUL rfl hcardSL hUHallS
      have hUgHallL' :
          IsHall (primeSupport (Nat.card U)) (Ug.subgroupOf L) := by
        simpa only [hcardUUg] using hUgHallL
      obtain ⟨x, hx⟩ :=
        exists_map_conj_eq_of_isHall_of_isSolvable
          (mmax_sol maxL) hUgHallL' hUHallL
      have hUgConj : conjugateSubgroup8 Ug (x : G) = U :=
        FTContextInternal.ambient_conjugate_eq_of_subgroupOf8
          hUgL hUL x hx
      let n : G := (x : G) * g
      have hnU : n ∈ Subgroup.normalizer (U : Set G) := by
        apply Subgroup.mem_normalizer_iff_map_conj_eq.mpr
        change conjugateSubgroup8 U n = U
        calc
          conjugateSubgroup8 U n =
              conjugateSubgroup8 Ug (x : G) := by
            exact (FTContextInternal.conjugateSubgroup8_mul U g (x : G)).symm
          _ = U := hUgConj
      have hSn : conjugateSubgroup8 S n = L := by
        calc
          conjugateSubgroup8 S n =
              conjugateSubgroup8 (conjugateSubgroup8 S g) (x : G) := by
            exact (FTContextInternal.conjugateSubgroup8_mul S g (x : G)).symm
          _ = conjugateSubgroup8 L (x : G) := by
            simpa only [conjugateSubgroup8] using congrArg
              (fun A : Subgroup G ↦ A.map (MulAut.conj (x : G)).toMonoidHom)
              hLg.symm
          _ = L :=
            FTContextInternal.conjugateSubgroup8_eq_self_of_mem_normalizer
              (Subgroup.le_normalizer x.property)
      have hNfix : conjugateSubgroup8
          (Subgroup.normalizer (U : Set G)) n⁻¹ =
          Subgroup.normalizer (U : Set G) :=
        FTContextInternal.conjugateSubgroup8_eq_self_of_mem_normalizer
          (Subgroup.le_normalizer
            ((Subgroup.normalizer (U : Set G)).inv_mem hnU))
      have hLback : conjugateSubgroup8 L n⁻¹ = S := by
        calc
          conjugateSubgroup8 L n⁻¹ =
              conjugateSubgroup8 (conjugateSubgroup8 S n) n⁻¹ := by
            rw [hSn]
          _ = conjugateSubgroup8 S (n⁻¹ * n) :=
            FTContextInternal.conjugateSubgroup8_mul S n n⁻¹
          _ = S := by
            rw [inv_mul_cancel]
            exact FTContextInternal.conjugateSubgroup8_eq_self_of_mem_normalizer
              (Subgroup.one_mem _)
      have hmapLe : conjugateSubgroup8
          (Subgroup.normalizer (U : Set G)) n⁻¹ ≤
          conjugateSubgroup8 L n⁻¹ :=
        Subgroup.map_mono hNU_L
      rw [hNfix, hLback] at hmapLe
      exact hUnotNorm hmapLe
    · rcases hTL with ⟨g, hLg⟩
      have hcardH : Nat.card (Fitting_core L) =
          (Nat.card W₁) ^ Nat.card W₂ := by
        rw [hLg, FcoreJ,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
        exact hQcard
      have hW₁pi : IsPiNumber
          (primeSupport (Nat.card (Fitting_core L))) (Nat.card W₁) := by
        apply IsPiNumber.primeSupport_self.of_dvd
        rw [hcardH]
        exact dvd_pow_self (Nat.card W₁) hp.ne_zero
      have hW₁H : W₁ ≤ Fitting_core L :=
        supportBridges_le_normalHall_of_isPiNumber13
          (Fcore_normal L) (Fcore_Hall L) hW₁L hW₁pi
      have hcopUW₁ : Nat.Coprime (Nat.card U) (Nat.card W₁) := by
        have hregUW₁ : IsSemiregularConjugation U W₁ :=
          supportBridges_frobeniusDecomp_semiregular13 hFrobUW₁
        exact IsSemiregularConjugation.natCard_coprime
          (G := G) (H := U) (R := W₁) hregUW₁
          (le_sup_right.trans hJoinNormU)
      have hcopUH : Nat.Coprime (Nat.card U)
          (Nat.card (Fitting_core L)) := by
        rw [hcardH]
        exact hcopUW₁.pow_right _
      have hdisUH : Disjoint U (Fitting_core L) :=
        Subgroup.disjoint_of_coprime_natCard hcopUH
      have hcentUW₁ : centralizerWithin U W₁ = ⊥ :=
        supportBridges_frobenius_kernel_centralizer_eq_bot13 hFrobUW₁
      have hUcentW₁ : U ≤ centralizerWithin U W₁ := by
        intro u hu
        refine ⟨hu, ?_⟩
        change u ∈ Subgroup.centralizer (W₁ : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        let c : G := w * u * w⁻¹ * u⁻¹
        have hcU : c ∈ U := by
          have hwu : w * u * w⁻¹ ∈ U :=
            (Subgroup.mem_normalizer_iff.mp (hW₁normU hw) u).mp hu
          exact U.mul_mem hwu (U.inv_mem hu)
        have hLnormH : L ≤ Subgroup.normalizer
            (Fitting_core L : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub L)).mp
            (Fcore_normal L)
        have hcH : c ∈ Fitting_core L := by
          have hwH : w ∈ Fitting_core L := hW₁H hw
          have hconj : u * w⁻¹ * u⁻¹ ∈ Fitting_core L :=
            (Subgroup.mem_normalizer_iff.mp (hLnormH (hUL hu)) w⁻¹).mp
              ((Fitting_core L).inv_mem hwH)
          have hproduct :
              w * (u * w⁻¹ * u⁻¹) ∈ Fitting_core L :=
            (Fitting_core L).mul_mem hwH hconj
          simpa only [c, mul_assoc] using hproduct
        have hcOne : c = 1 := by
          apply Subgroup.mem_bot.mp
          rw [← disjoint_iff.mp hdisUH]
          exact ⟨hcU, hcH⟩
        have hcomm : w * u = u * w := by
          apply eq_of_mul_inv_eq_one
          simpa only [mul_inv_rev, inv_inv, c, mul_assoc] using hcOne
        exact hcomm
      rw [hcentUW₁] at hUcentW₁
      apply hUne
      exact le_antisymm hUcentW₁ bot_le

  obtain ⟨E₀, hFrob₀⟩ := FTtype1_Frobenius L maxL Ltype1
  let H := Fitting_core L
  have hTypeF₀ : of_typeF L E₀ :=
    Frobenius_of_typeF L E₀ hFrob₀
  have hHL : H ≤ L := Fcore_sub L
  have hE₀L : E₀ ≤ L := hTypeF₀.2.2.1.2.1
  have hHne : H ≠ ⊥ := by
    simpa only [H] using hTypeF₀.1
  have hLnormH : L ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHL).mp (Fcore_normal L)
  have hcopFitting :=
    supportBridges_typeOneFitting_coprime_typeP13 ctxT L maxL Ltype1
  have hW₁dvdFittingT : Nat.card W₁ ∣ Nat.card (Fitting_core T) :=
    Subgroup.card_dvd_of_le ctxT.StypeP.2.2.2.1.2.2.1
  have hcopHW₁ : Nat.Coprime (Nat.card H) (Nat.card W₁) := by
    simpa only [H] using
      hcopFitting.coprime_dvd_right hW₁dvdFittingT
  have hdisHW₁ : Disjoint H W₁ :=
    Subgroup.disjoint_of_coprime_natCard hcopHW₁

  have hUH : U ≤ H := by
    by_contra hUH
    have hdisHU : Disjoint H U := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      apply Subgroup.mem_bot.mpr
      by_contra hxOne
      apply hUH
      intro u hu
      have hcomm : Commute u x := by
        letI : IsMulCommutative U := hUcomm
        show u * x = x * u
        exact congrArg (fun z : U ↦ (z : G))
          (mul_comm' (⟨u, hu⟩ : U) (⟨x, hx.2⟩ : U))
      have huCent : u ∈ Subgroup.centralizer
          (Subgroup.zpowers x : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (hcomm.symm.zpow_left n).eq
      exact supportBridges_centralizer_frobeniusIn_kernel_le13
        hFrob₀ hx.1 hxOne (hUL hu) huCent
    have hcopHU : Nat.Coprime (Nat.card H) (Nat.card U) :=
      supportBridges_coprime_fitting_of_disjoint13 hUL hdisHU
    let J : Subgroup G := U ⊔ W₁
    let UJ : Subgroup J := U.subgroupOf J
    let WJ : Subgroup J := W₁.subgroupOf J
    have hFrobJ : IsFrobeniusDecomposition UJ WJ := by
      simpa only [PTypeFrobeniusProduct, J, UJ, WJ] using hFrobUW₁
    have hUleJ : U ≤ J := by
      simpa only [J] using
        (show U ≤ U ⊔ W₁ from le_sup_left)
    have hWleJ : W₁ ≤ J := by
      simpa only [J] using
        (show W₁ ≤ U ⊔ W₁ from le_sup_right)
    have hUJcard : Nat.card UJ = Nat.card U := by
      simpa only [UJ] using
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUleJ
    have hWJcard : Nat.card WJ = Nat.card W₁ := by
      simpa only [WJ] using
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hWleJ
    have hcardUW₁ : Nat.card J = Nat.card U * Nat.card W₁ := by
      calc
        Nat.card J = Nat.card UJ * Nat.card WJ :=
          hFrobJ.isComplement.card_mul.symm
        _ = Nat.card U * Nat.card W₁ := by
          rw [hUJcard, hWJcard]
    have hcopHJoin : Nat.Coprime (Nat.card H) (Nat.card J) := by
      rw [hcardUW₁]
      exact hcopHU.mul_right hcopHW₁
    have hJoinL : J ≤ L := by
      simpa only [J] using (sup_le hUL hW₁L)
    have hJoinNormH : J ≤ Subgroup.normalizer (H : Set G) :=
      hJoinL.trans hLnormH
    have hcentHW₁ : centralizerWithin H W₁ = ⊥ :=
      supportBridges_frobenius_subgroup_centralizer_eq_bot13
        hFrob₀ hW₁ne hW₁L hdisHW₁
    have hHsol : IsSolvable H := by
      letI : Group.IsNilpotent H := by
        simpa only [H] using Fcore_nil L
      infer_instance
    have hUcentH : U ≤ Subgroup.centralizer (H : Set G) :=
      (Frobenius_Wielandt_fixpoint hFrobUW₁
        (by simpa only [J] using hJoinNormH)
        (by simpa only [J] using hcopHJoin) hHsol).2.1 hcentHW₁
    obtain ⟨h, hhH, hhOne⟩ := supportBridges_exists_mem_ne_one13 hHne
    have hUleH : U ≤ H := by
      intro u hu
      have huCent : u ∈ Subgroup.centralizer
          (Subgroup.zpowers h : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hcomm : Commute h u := by
          show h * u = u * h
          exact Subgroup.mem_centralizer_iff.mp (hUcentH hu) h hhH
        exact (hcomm.zpow_left n).eq
      exact supportBridges_centralizer_frobeniusIn_kernel_le13
        hFrob₀ hhH hhOne (hUL hu) huCent
    have hUbot : U = ⊥ := by
      apply le_antisymm _ bot_le
      intro u hu
      apply Subgroup.mem_bot.mp
      rw [← disjoint_iff.mp hdisHU]
      exact ⟨hUleH hu, hu⟩
    exact hUne hUbot

  let piH : Set ℕ := primeSupport (Nat.card H)
  have hHallE₀ : IsHall piHᶜ (E₀.subgroupOf L) := by
    exact supportBridges_hall_complement13
      (by simpa only [H, piH] using Fcore_Hall L)
      hTypeF₀.2.2.1.2.2.2
  have hW₁pi : IsPiNumber piHᶜ (Nat.card W₁) := by
    intro r hr hrW
    show r ∉ primeSupport (Nat.card H)
    rintro ⟨_, hrH⟩
    exact (Nat.not_coprime_of_dvd_of_dvd hr.one_lt hrH hrW) hcopHW₁
  obtain ⟨x, hW₁Ex, hExL, _, _, _, _⟩ :=
    exists_ambient_isHall_map_conj_ge_of_isSolvable
      hW₁L hE₀L (mmax_sol maxL) hW₁pi hHallE₀
  let E : Subgroup G := E₀.map (MulAut.conj (x : G)).toMonoidHom
  have hEL : E ≤ L := hExL
  have hFcoreFix : (Fitting_core L).map
      (MulAut.conj (x : G)).toMonoidHom = Fitting_core L :=
    FTContextInternal.conjugateSubgroup8_eq_self_of_mem_normalizer
      (hLnormH x.property)
  have hLfix : L.map (MulAut.conj (x : G)).toMonoidHom = L :=
    FTContextInternal.conjugateSubgroup8_eq_self_of_mem_normalizer
      (Subgroup.le_normalizer x.property)
  have hFrobE : IsFrobeniusIn H E L := by
    have hmap := supportBridges_isFrobeniusIn_map13 hFrob₀
      (MulAut.conj (x : G))
    simpa only [H, E, hFcoreFix, hLfix] using hmap
  have hregHE : IsSemiregularConjugation H E :=
    supportBridges_frobeniusIn_semiregular13 hFrobE
  have hEnormH : E ≤ Subgroup.normalizer (H : Set G) :=
    hEL.trans hLnormH
  have hW₁normalE : (W₁.subgroupOf E).Normal :=
    supportBridges_prime_odd_regular_normal hq (mFT_odd E)
      hW₁Ex hHne hEnormH hregHE

  refine ⟨⟨E, by simpa only [H] using hFrobE⟩,
    by simpa only [H] using hUH, ?_⟩

  /- The remaining source block identifies `Q ∩ E` with `W₁`, chooses the
  complementary `q'`-Hall subgroup of `E`, and conjugates it into `W₂`
  inside `N_G(W₁)`. -/
  let Q := Fitting_core T
  let N := Subgroup.normalizer (W₁ : Set G)
  have hsdN : IsInternalSemidirectProductIn Q W₂ N := by
    simpa only [Q, N] using (FTtypeP_norm_cent_compl ctxT).1
  have hQN : Q ≤ N := hsdN.1
  have hW₂N : W₂ ≤ N := hsdN.2.1
  have hEN : E ≤ N :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW₁Ex).mp hW₁normalE
  have hQnormalN : (Q.subgroupOf N).Normal := hsdN.2.2.1

  let piq : Set ℕ := {Nat.card W₁}
  have hQHallN : IsHall piq (Q.subgroupOf N) := by
    constructor
    · rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hQN]
      exact hQelem.isPGroup.isPiNumber_natCard (by simp [piq])
    · rw [hsdN.2.2.2.symm.index_eq_card,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hW₂N]
      intro r hr hrW₂
      show r ∉ piq
      intro hrpi
      have hrq : r = Nat.card W₁ := by
        simpa only [piq, Set.mem_singleton_iff] using hrpi
      subst r
      rcases (Nat.dvd_prime hp).mp hrW₂ with hqOne | hqEq
      · exact hq.ne_one hqOne
      · exact hqp hqEq
  let Q₁ : Subgroup G := Q ⊓ E
  have hQ₁HallE : IsHall piq (Q₁.subgroupOf E) := by
    simpa only [Q₁] using supportBridges_isHall_inf_of_normal_le13
      hQN hEN hQnormalN hQHallN
  have hQ₁normalE : (Q₁.subgroupOf E).Normal := by
    simpa only [Q₁] using supportBridges_normal_inf_subgroupOf_of_le13
      hQN hEN hQnormalN
  have hW₁Q : W₁ ≤ Q := ctxT.StypeP.2.2.2.1.2.2.1
  have hW₁Q₁ : W₁ ≤ Q₁ := le_inf hW₁Q hW₁Ex
  have hQ₁elem : IsElementaryAbelianGroup (Nat.card W₁) Q₁ :=
    supportBridges_elementary_subgroup13 hQelem inf_le_left
  have hQ₁p : IsPGroup (Nat.card W₁) (Q₁.subgroupOf E) :=
    hQ₁elem.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  have hqNotQ₁Index : ¬ Nat.card W₁ ∣ (Q₁.subgroupOf E).index := by
    intro hdvd
    exact hQ₁HallE.isPiNumber_index hq hdvd (by simp [piq])
  let P₁ : Sylow (Nat.card W₁) E :=
    hQ₁p.toSylow hqNotQ₁Index
  have hP₁coe : (P₁ : Subgroup E) = Q₁.subgroupOf E :=
    IsPGroup.toSylow_coe hQ₁p hqNotQ₁Index
  have hP₁map : (P₁ : Subgroup E).map E.subtype = Q₁ := by
    rw [hP₁coe, Subgroup.map_subgroupOf_eq_of_le inf_le_right]
  have hZE : IsZGroup8 E :=
    (typeF_context L E
      (Frobenius_of_typeF L E hFrobE)).frobenius_iff_zgroup.mp hFrobE
  have hP₁cyclic : IsCyclic P₁ := hZE (Nat.card W₁) P₁
  let eP₁ : P₁ ≃* Q₁ :=
    ((P₁ : Subgroup E).equivMapOfInjective E.subtype
      E.subtype_injective).trans (MulEquiv.subgroupCongr hP₁map)
  have hQ₁cyclic : IsCyclic Q₁ := eP₁.isCyclic.mp hP₁cyclic
  have hQ₁ne : Q₁ ≠ ⊥ := by
    intro hbot
    apply hW₁ne
    apply le_antisymm _ bot_le
    intro w hw
    have hwQ₁ : w ∈ Q₁ := hW₁Q₁ hw
    rw [hbot] at hwQ₁
    exact hwQ₁
  have hQ₁card : Nat.card Q₁ = Nat.card W₁ :=
    supportBridges_natCard_eq_prime_of_elementary_cyclic13
      hq hQ₁elem hQ₁cyclic (Q₁.one_lt_card_iff_ne_bot.mpr hQ₁ne)
  have hQ₁eq : Q₁ = W₁ := by
    symm
    apply Subgroup.eq_of_le_of_card_ge hW₁Q₁
    rw [hQ₁card]

  have hW₁HallE : IsHall piq (W₁.subgroupOf E) := by
    simpa only [← hQ₁eq] using hQ₁HallE
  have hW₁normalE' : (W₁.subgroupOf E).Normal := by
    simpa only [← hQ₁eq] using hQ₁normalE
  have hEsol : IsSolvable E :=
    mFT_sol (hEL.trans_lt (mmax_proper maxL))
  obtain ⟨P₂E, hP₂Hall⟩ :=
    exists_isHall_of_isSolvable hEsol piqᶜ
  let P₂ : Subgroup G := P₂E.map E.subtype
  have hP₂E : P₂ ≤ E := Subgroup.map_subtype_le P₂E
  have hP₂sub : P₂.subgroupOf E = P₂E :=
    Subgroup.comap_map_eq_self_of_injective E.subtype_injective P₂E
  have hcompW₁P₂ : (W₁.subgroupOf E).IsComplement'
      (P₂.subgroupOf E) := by
    rw [hP₂sub]
    exact supportBridges_complementaryHall_isComplement13
      hW₁HallE hP₂Hall
  have hsdE : IsInternalSemidirectProductIn W₁ P₂ E :=
    ⟨hW₁Ex, hP₂E, hW₁normalE', hcompW₁P₂⟩
  have hW₁P₂eq : W₁ ⊔ P₂ = E :=
    FTContextInternal.semidirect_sup_eq8 hsdE
  have hsdHL : IsInternalSemidirectProductIn H (W₁ ⊔ P₂) L := by
    simpa only [hW₁P₂eq] using
      (Frobenius_of_typeF L E hFrobE).2.2.1

  by_cases hP₂bot : P₂ = ⊥
  · left
    simpa only [H, hP₂bot, sup_bot_eq] using hsdHL
  · have hW₂HallN : IsHall piqᶜ (W₂.subgroupOf N) :=
      supportBridges_hall_complement13 hQHallN hsdN.2.2.2
    have hP₂pi : IsPiNumber piqᶜ (Nat.card P₂) := by
      simpa only [P₂,
        Subgroup.card_map_of_injective E.subtype_injective] using
          hP₂Hall.isPiNumber_card
    have hNleT : N ≤ T := by
      rw [← FTContextInternal.semidirect_sup_eq8 hsdN]
      exact sup_le hQT ctxT.StypeP.1.2.1.1
    have hNsol : IsSolvable N :=
      mFT_sol (hNleT.trans_lt (mmax_proper pairST.T_maximal))
    obtain ⟨a, hP₂W₂a, _, _, _, _, _⟩ :=
      exists_ambient_isHall_map_conj_ge_of_isSolvable
        (hP₂E.trans hEN) hW₂N hNsol hP₂pi hW₂HallN
    obtain ⟨⟨y, z⟩, hyz⟩ := hsdN.2.2.2.2 a
    have hyQ : (y : G) ∈ Q := y.property
    have hzW₂ : (z : G) ∈ W₂ := z.property
    have haeq : (a : G) = (y : G) * (z : G) :=
      (congrArg (fun t : N ↦ (t : G)) hyz).symm
    have hW₂a : conjugateSubgroup8 W₂ (a : G) =
        conjugateSubgroup8 W₂ (y : G) := by
      rw [haeq]
      calc
        conjugateSubgroup8 W₂ ((y : G) * (z : G)) =
            conjugateSubgroup8 (conjugateSubgroup8 W₂ (z : G))
              (y : G) :=
          (FTContextInternal.conjugateSubgroup8_mul W₂ (z : G) (y : G)).symm
        _ = conjugateSubgroup8 W₂ (y : G) := by
          rw [FTContextInternal.conjugateSubgroup8_eq_self_of_mem_normalizer
            (Subgroup.le_normalizer hzW₂)]
    have hP₂le : P₂ ≤ conjugateSubgroup8 W₂ (y : G) := by
      change P₂ ≤ conjugateSubgroup8 W₂ (a : G) at hP₂W₂a
      rw [hW₂a] at hP₂W₂a
      exact hP₂W₂a
    have hP₂eq : P₂ = conjugateSubgroup8 W₂ (y : G) := by
      let A : Subgroup G := conjugateSubgroup8 W₂ (y : G)
      have hAcard : Nat.card A = Nat.card W₂ := by
        dsimp only [A, conjugateSubgroup8]
        rw [Subgroup.card_map_of_injective (MulAut.conj (y : G)).injective]
      let PA : Subgroup A := P₂.subgroupOf A
      letI : Fact (Nat.card A).Prime := ⟨by rw [hAcard]; exact hp⟩
      rcases PA.eq_bot_or_eq_top_of_prime_card with hbot | htop
      · exfalso
        apply hP₂bot
        have hdisP₂A : Disjoint P₂ A := by
          apply Subgroup.subgroupOf_eq_bot.mp
          simpa only [PA] using hbot
        apply le_antisymm _ bot_le
        intro p hpP₂
        exact hdisP₂A.le_bot ⟨hpP₂, hP₂le hpP₂⟩
      · exact le_antisymm hP₂le (Subgroup.subgroupOf_eq_top.mp htop)
    right
    refine ⟨(y : G), by simpa only [Q] using hyQ, ?_⟩
    rw [← hP₂eq]
    simpa only [H] using hsdHL
private theorem supportBridges_pairing_sub_left
    {Q : Type} [Group Q] [Fintype Q]
    (f g z : ClassFunction Q ℂ) :
    characterPairing (f - g) z =
      characterPairing f z - characterPairing g z := by
  change characterPairingRight z (f - g) = _
  exact map_sub (characterPairingRight z) f g

private theorem supportBridges_pairing_sub_right
    {Q : Type} [Group Q] [Fintype Q]
    (z f g : ClassFunction Q ℂ) :
    characterPairing z (f - g) =
      characterPairing z f - characterPairing z g := by
  change characterPairingLeft z (f - g) = _
  exact map_sub (characterPairingLeft z) f g

private theorem supportBridges_pairing_sub_self
    {Q : Type} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing (f - g) (f - g) =
      characterPairing f f - characterPairing f g -
        characterPairing g f + characterPairing g g := by
  rw [supportBridges_pairing_sub_left,
    supportBridges_pairing_sub_right,
    supportBridges_pairing_sub_right]
  ring

/-- Pullback along a finite quotient preserves the normalized pairing. -/
private theorem supportBridges_pairing_comap_surjective
    {A Q : Type} [Group A] [Group Q] [Fintype A] [Fintype Q]
    (q : A →* Q) (hq : Function.Surjective q)
    (f g : ClassFunction Q ℂ) :
    characterPairing (ClassFunction.comap q f)
        (ClassFunction.comap q g) =
      characterPairing f g := by
  have hcard : Nat.card A = Nat.card q.ker * Nat.card Q := by
    calc
      Nat.card A = Nat.card (⊤ : Subgroup A) := by simp
      _ = Nat.card q.ker * Nat.card ((⊤ : Subgroup A).map q) :=
        ClassFunction.natCard_eq_ker_mul_map q ⊤ le_top
      _ = Nat.card q.ker * Nat.card Q := by
        rw [Subgroup.map_top_of_surjective q hq, Subgroup.card_top]
  unfold characterPairing
  simp only [ClassFunction.comap_apply, map_inv]
  rw [ClassFunction.sum_comp_surjective q hq
    (fun y : Q ↦ f y * g y⁻¹), hcard, Nat.cast_mul,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_eq_mul]
  have hker : (Nat.card q.ker : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := q.ker)).ne'
  have hQ : (Nat.card Q : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Nat.card_pos (α := Q)).ne'
  field_simp [hker, hQ]

/-! ## The universal Frobenius permutation-character calculation -/

/-- On a Frobenius complement, the character induced from the trivial
character takes the value `|K|` at one and the value one elsewhere. -/
private theorem supportBridges_frobenius_induce_trivial_apply
    {Q : Type} [Group Q] [Fintype Q]
    (K R : Subgroup Q) (hFrob : IsFrobeniusDecomposition K R)
    (r : R) :
    ClassFunction.induce R
        ((IrreducibleCharacter.trivial : IrreducibleCharacter R ℂ) :
          ClassFunction R ℂ) (r : Q) =
      if r = 1 then (Nat.card K : ℂ) else 1 := by
  classical
  by_cases hr : r = 1
  · subst r
    have hdegree :
        ClassFunction.induce R
            ((IrreducibleCharacter.trivial : IrreducibleCharacter R ℂ) :
              ClassFunction R ℂ) (1 : Q) =
          (Nat.card K : ℂ) := by
      rw [ClassFunction.induce_one R]
      simp only [IrreducibleCharacter.trivial_apply, mul_one,
        hFrob.isComplement.index_eq_card]
    simpa only [Subgroup.coe_one, if_pos] using hdegree
  · rw [if_neg hr, ClassFunction.induce_apply_formula]
    have hmem (x : Q) :
        x⁻¹ * (r : Q) * x ∈ R ↔ x ∈ R := by
      constructor
      · intro hx
        by_contra hxR
        have hrMap : (r : Q) ∈
            R.map (MulAut.conj x).toMonoidHom := by
          refine ⟨x⁻¹ * (r : Q) * x, hx, ?_⟩
          change x * (x⁻¹ * (r : Q) * x) * x⁻¹ = (r : Q)
          group
        have hrBot : (r : Q) ∈ (⊥ : Subgroup Q) := by
          rw [← disjoint_iff.mp
            (hFrob.disjoint_complement_conjugate_of_not_mem hxR)]
          exact ⟨r.property, hrMap⟩
        apply hr
        apply Subtype.ext
        exact Subgroup.mem_bot.mp hrBot
      · intro hx
        exact R.mul_mem (R.mul_mem (R.inv_mem hx) r.property) hx
    have hsum :
        (∑ x : Q,
          if hx : x⁻¹ * (r : Q) * x ∈ R then
            ((IrreducibleCharacter.trivial : IrreducibleCharacter R ℂ) :
              ClassFunction R ℂ) ⟨x⁻¹ * (r : Q) * x, hx⟩
          else 0) =
        ∑ x : Q, if x ∈ R then (1 : ℂ) else 0 := by
      apply Finset.sum_congr rfl
      intro x _
      by_cases hx : x ∈ R
      · rw [if_pos hx, dif_pos ((hmem x).2 hx)]
        simp only [IrreducibleCharacter.trivial_apply]
      · rw [if_neg hx, dif_neg ((hmem x).not.mpr hx)]
    have hcount :
        (∑ x : Q, if x ∈ R then (1 : ℂ) else 0) =
          (Nat.card R : ℂ) := by
      rw [Finset.sum_boole]
      congr 2
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_subtype (fun x : Q ↦ x ∈ R)).symm
    rw [hsum, hcount]
    have hR : (Nat.card R : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr (Nat.card_pos (α := R)).ne'
    field_simp [hR]

/-- Exact squared norm of the permutation character of a Frobenius
complement.  The result is stated with natural-number division, matching the
source theorem (13.18). -/
private theorem supportBridges_frobenius_induce_trivial_norm
    {Q : Type} [Group Q] [Fintype Q]
    (K R : Subgroup Q) (hFrob : IsFrobeniusDecomposition K R) :
    characterPairing
        (ClassFunction.induce R
          ((IrreducibleCharacter.trivial : IrreducibleCharacter R ℂ) :
            ClassFunction R ℂ))
        (ClassFunction.induce R
          ((IrreducibleCharacter.trivial : IrreducibleCharacter R ℂ) :
            ClassFunction R ℂ)) =
      ((((Nat.card K - 1) / Nat.card R + 1 : ℕ) : ℂ)) := by
  classical
  letI := hFrob.conjugationAction
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := K))
  have hcard : Nat.card K = 1 + t * Nat.card R := by
    simpa only [t] using hFrob.kernel_card_eq_one_add_orbits_mul_card
  have hkpred : Nat.card K - 1 = t * Nat.card R := by omega
  have hRpos : 0 < Nat.card R := Nat.card_pos
  have hquot : (Nat.card K - 1) / Nat.card R = t := by
    rw [hkpred]
    exact Nat.mul_div_left t hRpos
  rw [ClassFunction.frobeniusReciprocity R]
  unfold characterPairing
  simp only [IrreducibleCharacter.trivial_apply,
    ClassFunction.restrict_apply, one_mul]
  have hind (r : R) :
      ClassFunction.induce R
          ((IrreducibleCharacter.trivial : IrreducibleCharacter R ℂ) :
            ClassFunction R ℂ) ((r⁻¹ : R) : Q) =
        if r = 1 then (Nat.card K : ℂ) else 1 := by
    simpa only [inv_eq_one] using
      (supportBridges_frobenius_induce_trivial_apply K R hFrob r⁻¹)
  simp_rw [hind]
  have hsum :
      (∑ r : R, if r = 1 then (Nat.card K : ℂ) else 1) =
        (Nat.card K : ℂ) + ((Nat.card R - 1 : ℕ) : ℂ) := by
    calc
      (∑ r : R, if r = 1 then (Nat.card K : ℂ) else 1) =
          (if (1 : R) = 1 then (Nat.card K : ℂ) else 1) +
            ∑ r ∈ (Finset.univ : Finset R).erase 1,
              if r = 1 then (Nat.card K : ℂ) else 1 := by
                let f : R → ℂ := fun r ↦
                  if r = 1 then (Nat.card K : ℂ) else 1
                change (∑ r : R, f r) =
                  f 1 + ∑ r ∈ (Finset.univ : Finset R).erase 1, f r
                calc
                  (∑ r : R, f r) =
                      (∑ r ∈ (Finset.univ : Finset R).erase 1, f r) +
                        f 1 :=
                    (Finset.sum_erase_add
                      (Finset.univ : Finset R) f
                      (Finset.mem_univ (1 : R))).symm
                  _ = f 1 +
                      ∑ r ∈ (Finset.univ : Finset R).erase 1, f r :=
                    add_comm _ _
      _ = (Nat.card K : ℂ) +
          ∑ _r ∈ (Finset.univ : Finset R).erase 1, (1 : ℂ) := by
            congr 1
            · simp
            · apply Finset.sum_congr rfl
              intro r hr
              rw [if_neg (Finset.mem_erase.mp hr).1]
      _ = (Nat.card K : ℂ) +
          (((Finset.univ : Finset R).erase 1).card : ℂ) := by simp
      _ = (Nat.card K : ℂ) + ((Nat.card R - 1 : ℕ) : ℂ) := by
            rw [Finset.card_erase_of_mem (Finset.mem_univ (1 : R)),
              Finset.card_univ, Fintype.card_eq_nat_card]
  rw [hsum, hquot]
  have hR : (Nat.card R : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hRpos.ne'
  have hRone : 1 ≤ Nat.card R := hRpos
  have hnat :
      Nat.card K + (Nat.card R - 1) = Nat.card R * (t + 1) := by
    calc
      Nat.card K + (Nat.card R - 1) =
          (1 + t * Nat.card R) + (Nat.card R - 1) := by rw [hcard]
      _ = t * Nat.card R + ((Nat.card R - 1) + 1) := by ac_rfl
      _ = t * Nat.card R + Nat.card R := by
        rw [Nat.sub_add_cancel hRone]
      _ = Nat.card R * t + Nat.card R := by
        rw [Nat.mul_comm t (Nat.card R)]
      _ = Nat.card R * t + Nat.card R * 1 := by
        rw [Nat.mul_one]
      _ = Nat.card R * (t + 1) :=
        (Nat.mul_add (Nat.card R) t 1).symm
  rw [← Nat.cast_add, hnat, Nat.cast_mul]
  field_simp [hR]

private def supportBridges_typePGamma
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ClassFunction S ℂ :=
  ClassFunction.induce (FTtypePBridgeInducingSubgroup S W₁)
    ((IrreducibleCharacter.trivial :
        IrreducibleCharacter (FTtypePBridgeInducingSubgroup S W₁) ℂ) :
      ClassFunction (FTtypePBridgeInducingSubgroup S W₁) ℂ)

private def supportBridges_typePMu
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) : ClassFunction S ℂ :=
  ctx.primeTI.primeTICharacter ctx.isoS
    (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j

private theorem supportBridges_bridge_eq_gamma_sub_mu
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    FTtypeP_bridge ctx j =
      supportBridges_typePGamma ctx - supportBridges_typePMu ctx j := by
  unfold FTtypeP_bridge supportBridges_typePGamma supportBridges_typePMu
  rfl

private theorem supportBridges_typePMu_pairing_self
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (supportBridges_typePMu ctx j)
        (supportBridges_typePMu ctx j) = 1 := by
  letI : Invertible (Nat.card S : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := S)).ne')
  simpa only [supportBridges_typePMu,
    PrimeTIHypothesis.primeTICharacter] using
    (IrreducibleCharacter.characterPairing_self
      (ctx.primeTI.primeTIIndex ctx.isoS
        ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ), j)))

/-- The induced trivial character is orthogonal to every nontrivial selected
right-column prime-TI irreducible.  A nonzero pairing would make that
irreducible a constituent of the induced representation.  Normality then
forces the F-core into its kernel, and restriction to the derived subgroup
contradicts the selected prime-Dade kernel exclusion. -/
private theorem supportBridges_typePGamma_pairing_typePMu_eq_zero
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    characterPairing (supportBridges_typePGamma ctx)
        (supportBridges_typePMu ctx j) = 0 := by
  classical
  let P : Subgroup S := (Fitting_core S).subgroupOf S
  let B : Subgroup S := FTtypePBridgeInducingSubgroup S W₁
  let H : Subgroup S := (derivedWithin S).subgroupOf S
  let oneB : IrreducibleCharacter B ℂ := IrreducibleCharacter.trivial
  let V : FDRep ℂ S :=
    FDRep.induceFromSubgroup B oneB.representation
  let mu : IrreducibleCharacter S ℂ :=
    ctx.primeTI.primeTIIndex ctx.isoS
      ((IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ), j)
  let psi : IrreducibleCharacter H ℂ :=
    ctx.primeTI.primeTI_Ires ctx.isoS j
  letI : P.Normal := by
    simpa only [P] using Fcore_normal S
  letI : H.Normal := ctx.primeTI.kernel_normal
  letI : Invertible (Nat.card S : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := S)).ne')
  letI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := H)).ne')
  have hPB : P ≤ B := le_sup_left
  have hPH : P ≤ H :=
    Subgroup.subgroupOf_mono S ctx.StypeP.2.1.2.2.2.1
  have hPtrivial : P.subgroupOf B ≤ oneB.representation.ρ.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter oneB]
    intro x _hx
    rw [ClassFunction.mem_translationKernel_iff]
    intro y
    change
      (IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) (x * y) =
        (IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) y
    simp only [IrreducibleCharacter.trivial_apply]
  have hPV : P ≤ V.ρ.ker := by
    change P ≤
      (FDRep.induceFromSubgroup B oneB.representation).ρ.ker
    exact (FDRep.sub_ker_induceFromSubgroup_iff
      B P hPB oneB.representation).2 hPtrivial
  have hVcharacter :
      ClassFunction.ofRepresentation V.ρ =
        supportBridges_typePGamma ctx := by
    simpa only [V, B, oneB, supportBridges_typePGamma] using
      (ClassFunction.ofRepresentation_induceFromSubgroup_general
        B oneB.representation).trans
          (congrArg (ClassFunction.induce B)
            oneB.ofRepresentation_representation)
  by_contra hpair
  have hconstituent : mu.IsConstituent
      (ClassFunction.ofRepresentation V.ρ) := by
    unfold IrreducibleCharacter.IsConstituent
    rw [hVcharacter]
    simpa only [mu, supportBridges_typePMu,
      PrimeTIHypothesis.primeTICharacter] using hpair
  have hPmu : P ≤ mu.representation.ρ.ker :=
    hPV.trans
      (FDRep.ker_le_irreducible_ker_of_isConstituent
        V mu hconstituent)
  have hrestrict :
      ClassFunction.restrict H (mu : ClassFunction S ℂ) =
        (psi : ClassFunction H ℂ) := by
    simpa only [H, mu, psi, PrimeTIHypothesis.primeTICharacter] using
      (ctx.primeTI.cfRes_prTIirr ctx.isoS
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j)
  have hpsiConstituent : psi.IsConstituent
      (ClassFunction.restrict H (mu : ClassFunction S ℂ)) := by
    unfold IrreducibleCharacter.IsConstituent
    rw [hrestrict, IrreducibleCharacter.characterPairing_self]
    exact one_ne_zero
  have hPpsiRep : P.subgroupOf H ≤ psi.representation.ρ.ker :=
    (IrreducibleCharacter.sub_ker_constituent_restrict_iff
      H P hPH mu psi hpsiConstituent).mpr hPmu
  have hPpsi : P.subgroupOf H ≤
      ClassFunction.translationKernel (psi : ClassFunction H ℂ) := by
    rw [ClassFunction.translationKernel_irreducibleCharacter psi]
    exact hPpsiRep
  apply ctx.primeDadeF.cfker_prTIres ctx.isoS j hj
  simpa only [P, H, psi, PrimeDadeHypothesis.signalizerInKernel] using hPpsi

/-- Once the quotient-Frobenius norm and the kernel orthogonality have been
supplied, the bridge norm is exactly the source value. -/
private theorem supportBridges_bridge_norm_of_gamma_norm_orthogonal
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hgamma :
      characterPairing (supportBridges_typePGamma ctx)
          (supportBridges_typePGamma ctx) =
        ((((Nat.card U - 1) / Nat.card W₁ + 1 : ℕ) : ℂ)))
    (horth :
      characterPairing (supportBridges_typePGamma ctx)
          (supportBridges_typePMu ctx j) = 0) :
    characterPairing (FTtypeP_bridge ctx j) (FTtypeP_bridge ctx j) =
      ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ)) := by
  rw [supportBridges_bridge_eq_gamma_sub_mu,
    supportBridges_pairing_sub_self, hgamma, horth,
    characterPairing_comm (supportBridges_typePMu ctx j)
      (supportBridges_typePGamma ctx), horth,
    supportBridges_typePMu_pairing_self]
  push_cast
  ring

/-! ## The complement-to-quotient equivalence -/

private theorem supportBridges_quotientMap_surjective_on_right
    {Q : Type} [Group Q] {N B : Subgroup Q} [N.Normal]
    (h : N.IsComplement' B) :
    Function.Surjective
      ((QuotientGroup.mk' N).comp B.subtype) := by
  intro z
  obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective N z
  obtain ⟨nb, hnb, _⟩ := h.existsUnique g
  refine ⟨nb.2, ?_⟩
  change QuotientGroup.mk' N (nb.2 : Q) = QuotientGroup.mk' N g
  rw [← hnb, map_mul]
  have hn : QuotientGroup.mk' N (nb.1 : Q) = 1 :=
    QuotientGroup.eq_one_iff (nb.1 : Q) |>.mpr nb.1.property
  rw [hn, one_mul]

/-- The right factor of an internal semidirect product is canonically the
quotient by the normal left factor. -/
private noncomputable def supportBridges_rightQuotientMulEquiv
    {Q : Type} [Group Q] {N B : Subgroup Q} [N.Normal]
    (h : N.IsComplement' B) : B ≃* (Q ⧸ N) :=
  MulEquiv.ofBijective ((QuotientGroup.mk' N).comp B.subtype)
    ⟨h.quotientMap_injective_on_right le_rfl,
      supportBridges_quotientMap_surjective_on_right h⟩

@[simp]
private theorem supportBridges_rightQuotientMulEquiv_apply
    {Q : Type} [Group Q] {N B : Subgroup Q} [N.Normal]
    (h : N.IsComplement' B) (b : B) :
    supportBridges_rightQuotientMulEquiv h b =
      QuotientGroup.mk' N (b : Q) := by
  change ((QuotientGroup.mk' N).comp B.subtype) b = _
  rfl

/-! ## Type-P quotient coordinates -/

/-- The permutation character induced from
`(Fitting_core S) ⊔ W₁` has the Frobenius quotient norm. -/
private theorem supportBridges_typePGamma_norm
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    characterPairing (supportBridges_typePGamma ctx)
        (supportBridges_typePGamma ctx) =
      ((((Nat.card U - 1) / Nat.card W₁ + 1 : ℕ) : ℂ)) := by
  classical
  let P : Subgroup S := (Fitting_core S).subgroupOf S
  letI : P.Normal := by
    simpa only [P] using Fcore_normal S
  let J₀ : Subgroup G := U ⊔ W₁
  have hJ₀S : J₀ ≤ S :=
    (Ptype_Fcore_sdprod ctx.ptypeCtx).2.1
  let J : Subgroup S := J₀.subgroupOf S
  let UJ₀ : Subgroup J₀ := U.subgroupOf J₀
  let WJ₀ : Subgroup J₀ := W₁.subgroupOf J₀
  let US : Subgroup S := U.subgroupOf S
  let W₁S : Subgroup S := W₁.subgroupOf S
  let B : Subgroup S := FTtypePBridgeInducingSubgroup S W₁
  let q : S →* S ⧸ P := QuotientGroup.mk' P

  have hcomp : P.IsComplement' J := by
    simpa only [P, J, J₀] using
      (Ptype_Fcore_sdprod ctx.ptypeCtx).2.2.2
  let eJ : J ≃* J₀ := Subgroup.subgroupOfEquivOfLe hJ₀S
  let e : J₀ ≃* (S ⧸ P) :=
    eJ.symm.trans (supportBridges_rightQuotientMulEquiv hcomp)
  have he_apply (a : J₀) :
      e.toMonoidHom a =
        q ⟨(a : G), hJ₀S a.property⟩ := by
    change supportBridges_rightQuotientMulEquiv hcomp
      (eJ.symm a) = _
    rw [supportBridges_rightQuotientMulEquiv_apply]
    rfl

  have hFrob₀ : IsFrobeniusDecomposition UJ₀ WJ₀ := by
    simpa only [PTypeFrobeniusProduct, J₀, UJ₀, WJ₀] using
      (FTtypeP_facts ctx).2.2.1

  have hUmap : US.map q = UJ₀.map e.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (u : G) ∈ U at hu
      have huJ₀ : (u : G) ∈ J₀ := by
        change (u : G) ∈ U ⊔ W₁
        exact (show U ≤ U ⊔ W₁ from le_sup_left) hu
      let a : J₀ := ⟨(u : G), huJ₀⟩
      refine ⟨a, ?_, ?_⟩
      · change (a : G) ∈ U
        simpa only [a] using hu
      · calc
          e.toMonoidHom a =
              q ⟨(a : G), hJ₀S a.property⟩ := he_apply a
          _ = q u := by
            apply congrArg q
            exact Subtype.ext rfl
    · rintro ⟨a, ha, rfl⟩
      change (a : G) ∈ U at ha
      let u : S := ⟨(a : G), hJ₀S a.property⟩
      refine ⟨u, ?_, ?_⟩
      · exact ha
      · simpa only [u] using (he_apply a).symm

  have hB_eq : B = P ⊔ W₁S := by
    rfl
  have hBmapW : B.map q = W₁S.map q := by
    rw [hB_eq, Subgroup.map_sup]
    change P.map (QuotientGroup.mk' P) ⊔ W₁S.map q = W₁S.map q
    rw [QuotientGroup.map_mk'_self, bot_sup_eq]
  have hWmap : W₁S.map q = WJ₀.map e.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      change (w : G) ∈ W₁ at hw
      have hwJ₀ : (w : G) ∈ J₀ := by
        change (w : G) ∈ U ⊔ W₁
        exact (show W₁ ≤ U ⊔ W₁ from le_sup_right) hw
      let a : J₀ := ⟨(w : G), hwJ₀⟩
      refine ⟨a, ?_, ?_⟩
      · change (a : G) ∈ W₁
        simpa only [a] using hw
      · calc
          e.toMonoidHom a =
              q ⟨(a : G), hJ₀S a.property⟩ := he_apply a
          _ = q w := by
            apply congrArg q
            exact Subtype.ext rfl
    · rintro ⟨a, ha, rfl⟩
      change (a : G) ∈ W₁ at ha
      let w : S := ⟨(a : G), hJ₀S a.property⟩
      refine ⟨w, ?_, ?_⟩
      · exact ha
      · simpa only [w] using (he_apply a).symm

  let Kq : Subgroup (S ⧸ P) := US.map q
  let Rq : Subgroup (S ⧸ P) := B.map q
  have hKqmap : Kq = UJ₀.map e.toMonoidHom := by
    simpa only [Kq] using hUmap
  have hRqmap : Rq = WJ₀.map e.toMonoidHom := by
    simpa only [Rq] using hBmapW.trans hWmap
  have hFrobq : IsFrobeniusDecomposition Kq Rq := by
    have hmap := FTContextInternal.frobenius_map_mulEquiv8 hFrob₀ e
    simpa only [Kq, Rq, hUmap, hBmapW, hWmap] using hmap

  have hKqcard : Nat.card Kq = Nat.card U := by
    calc
      Nat.card Kq = Nat.card (UJ₀.map e.toMonoidHom) := by
        rw [hKqmap]
      _ = Nat.card UJ₀ :=
        Subgroup.card_map_of_injective
          (K := UJ₀) (f := e.toMonoidHom) e.injective
      _ = Nat.card U :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          (H := U) (K := J₀) (show U ≤ J₀ from le_sup_left)
  have hRqcard : Nat.card Rq = Nat.card W₁ := by
    calc
      Nat.card Rq = Nat.card (WJ₀.map e.toMonoidHom) := by
        rw [hRqmap]
      _ = Nat.card WJ₀ :=
        Subgroup.card_map_of_injective
          (K := WJ₀) (f := e.toMonoidHom) e.injective
      _ = Nat.card W₁ :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          (H := W₁) (K := J₀) (show W₁ ≤ J₀ from le_sup_right)

  let gammaq : ClassFunction (S ⧸ P) ℂ :=
    ClassFunction.induce Rq
      ((IrreducibleCharacter.trivial : IrreducibleCharacter Rq ℂ) :
        ClassFunction Rq ℂ)
  have hPB : P ≤ B := by
    rw [hB_eq]
    exact le_sup_left
  have hcomapTrivial :
      ClassFunction.comap (q.subgroupMap B)
          ((IrreducibleCharacter.trivial : IrreducibleCharacter Rq ℂ) :
            ClassFunction Rq ℂ) =
        ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
          ClassFunction B ℂ) := by
    apply ClassFunction.ext
    intro b
    simp only [ClassFunction.comap_apply,
      IrreducibleCharacter.trivial_apply]
  have hinflate : ClassFunction.inflate P gammaq =
      ClassFunction.induce B
        ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
          ClassFunction B ℂ) := by
    calc
      ClassFunction.inflate P gammaq =
          ClassFunction.induce B
            (ClassFunction.comap (q.subgroupMap B)
              ((IrreducibleCharacter.trivial : IrreducibleCharacter Rq ℂ) :
                ClassFunction Rq ℂ)) := by
                simpa only [gammaq, q, Rq] using
                  (ClassFunction.inflate_induce_quotientImage
                    (k := ℂ) P B hPB
                    ((IrreducibleCharacter.trivial :
                        IrreducibleCharacter Rq ℂ) :
                      ClassFunction Rq ℂ))
      _ = ClassFunction.induce B
          ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
            ClassFunction B ℂ) := by
            rw [hcomapTrivial]
  have hgamma : supportBridges_typePGamma ctx =
      ClassFunction.inflate P gammaq := by
    change ClassFunction.induce B
        ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
          ClassFunction B ℂ) = ClassFunction.inflate P gammaq
    exact hinflate.symm

  have hquotientNorm :
      characterPairing gammaq gammaq =
        ((((Nat.card U - 1) / Nat.card W₁ + 1 : ℕ) : ℂ)) := by
    simpa only [gammaq, hKqcard, hRqcard] using
      supportBridges_frobenius_induce_trivial_norm Kq Rq hFrobq
  calc
    characterPairing (supportBridges_typePGamma ctx)
        (supportBridges_typePGamma ctx) =
      characterPairing (ClassFunction.inflate P gammaq)
        (ClassFunction.inflate P gammaq) := by rw [hgamma]
    _ = characterPairing gammaq gammaq := by
      change characterPairing (ClassFunction.comap q gammaq)
          (ClassFunction.comap q gammaq) = _
      exact supportBridges_pairing_comap_surjective q
        (QuotientGroup.mk'_surjective P) gammaq gammaq
    _ = ((((Nat.card U - 1) / Nat.card W₁ + 1 : ℕ) : ℂ)) :=
      hquotientNorm

/-- Type-P bridge norm reduced solely to the quotient-Frobenius norm of
`supportBridges_typePGamma`; orthogonality is discharged by the kernel
exclusion above. -/
private theorem supportBridges_bridge_norm_of_gamma_norm
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hgamma :
      characterPairing (supportBridges_typePGamma ctx)
          (supportBridges_typePGamma ctx) =
        ((((Nat.card U - 1) / Nat.card W₁ + 1 : ℕ) : ℂ))) :
    characterPairing (FTtypeP_bridge ctx j) (FTtypeP_bridge ctx j) =
      ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ)) :=
  supportBridges_bridge_norm_of_gamma_norm_orthogonal ctx j hgamma
    (supportBridges_typePGamma_pairing_typePMu_eq_zero ctx j hj)

/-! The inside-derived branch of the source support calculation. -/

private theorem supportBridges_bridge_zero_of_mem_derived
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (z : S)
    (hzD : (z : G) ∈ derivedWithin S)
    (hzCore : z ∉ FTtypePBridgeCoreSupport S W W₁ W₂) :
    FTtypeP_bridge ctx j z = 0 := by
  classical
  let P : Subgroup S := (Fitting_core S).subgroupOf S
  let D : Subgroup S := (derivedWithin S).subgroupOf S
  let W₁S : Subgroup S := W₁.subgroupOf S
  let B : Subgroup S := FTtypePBridgeInducingSubgroup S W₁
  let PW : Subgroup G := ctx.P ⊔ W₁

  letI : P.Normal := by
    simpa only [P] using Fcore_normal S
  letI : D.Normal := by
    simpa only [D] using ctx.StypeP.1.2.2.2.2.2.1

  have hinner : IsInternalSemidirectProductIn ctx.P U ctx.PU :=
    ctx.StypeP.2.1.2.2.2
  have houter : IsInternalSemidirectProductIn ctx.PU W₁ S :=
    ctx.StypeP.1.2.2.2
  have hPW : IsInternalSemidirectProductIn ctx.P W₁
      (Subgroup.normalizer (W₂ : Set G)) :=
    (FTtypeP_norm_cent_compl ctx).1

  have hP_eq_H : ctx.P = ctx.H := by
    have hdecomp :=
      (typeP_context S U W W₁ W₂ defW ctx.StypeP).fitting_decomposition
    have hsup : ctx.P ⊔ ctx.C = ctx.H :=
      FTContextInternal.directProduct_sup_eq8 hdecomp
    rw [FTtypeP_reg_Fcore ctx, sup_bot_eq] at hsup
    exact hsup

  have hu : ctx.u = Nat.card U := by
    change (ctx.C.subgroupOf U).index = Nat.card U
    rw [FTtypeP_reg_Fcore ctx, Subgroup.bot_subgroupOf,
      Subgroup.index_bot]

  have semidirectCard {A H K : Subgroup G}
      (h : IsInternalSemidirectProductIn A H K) :
      Nat.card A * Nat.card H = Nat.card K := by
    simpa only [
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq h.1,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq h.2.1]
      using h.2.2.2.card_mul
  have hDcard : Nat.card ctx.P * Nat.card U = Nat.card ctx.PU :=
    semidirectCard hinner
  have hScard : Nat.card ctx.PU * Nat.card W₁ = Nat.card S :=
    semidirectCard houter
  have hPWambient :
      Nat.card ctx.P * Nat.card W₁ =
        Nat.card (Subgroup.normalizer (W₂ : Set G)) :=
    semidirectCard hPW
  have hPWeq : PW = Subgroup.normalizer (W₂ : Set G) := by
    simpa only [PW] using FTContextInternal.semidirect_sup_eq8 hPW
  have hPWsupCard :
      Nat.card PW = Nat.card (Subgroup.normalizer (W₂ : Set G)) :=
    congrArg (fun L : Subgroup G ↦ Nat.card L) hPWeq
  have hPWcard :
      Nat.card ctx.P * Nat.card W₁ = Nat.card PW :=
    hPWambient.trans hPWsupCard.symm
  have hPWleS : PW ≤ S := by
    simpa only [PW] using
      (sup_le (Fcore_sub S) ctx.primeTI.complement_le_group)
  have hB_eq : B = PW.subgroupOf S := by
    dsimp only [B, PW, FTtypePBridgeInducingSubgroup]
    exact (Subgroup.subgroupOf_sup (Fcore_sub S)
      ctx.primeTI.complement_le_group).symm
  have hBsupCard : Nat.card B = Nat.card PW := by
    calc
      Nat.card B = Nat.card (PW.subgroupOf S) :=
        congrArg (fun L : Subgroup S ↦ Nat.card L) hB_eq
      _ = Nat.card PW :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hPWleS
  have hBcard : Nat.card B = Nat.card ctx.P * Nat.card W₁ :=
    hBsupCard.trans hPWcard.symm
  have hBindex : B.index = Nat.card U := by
    apply Nat.mul_right_cancel
      (Nat.mul_pos (Nat.card_pos (α := ctx.P))
        (Nat.card_pos (α := W₁)))
    calc
      B.index * (Nat.card ctx.P * Nat.card W₁) =
          B.index * Nat.card B := by rw [hBcard]
      _ = Nat.card S := B.index_mul_card
      _ = Nat.card ctx.PU * Nat.card W₁ := hScard.symm
      _ = (Nat.card ctx.P * Nat.card U) * Nat.card W₁ := by
        rw [hDcard]
      _ = Nat.card U * (Nat.card ctx.P * Nat.card W₁) := by
        ac_rfl

  have hIndOne :
      ClassFunction.induce B
          ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
            ClassFunction B ℂ) 1 =
        (ctx.u : ℂ) := by
    rw [ClassFunction.induce_one, hBindex, ← hu]
    simp
  have hqC : (Nat.card W₁ : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hIrrOne :
      ctx.primeTI.primeTICharacter ctx.isoS
          IrreducibleCharacter.trivial j 1 =
        (ctx.u : ℂ) := by
    apply mul_left_cancel₀ hqC
    calc
      (Nat.card W₁ : ℂ) *
          ctx.primeTI.primeTICharacter ctx.isoS
            IrreducibleCharacter.trivial j 1 =
        ctx.mu j 1 :=
          (ctx.primeTI.prTIred_1 ctx.isoS j).symm
      _ = ((ctx.u * ctx.q : ℕ) : ℂ) := FTprTIred1 ctx j hj
      _ = (Nat.card W₁ : ℂ) * (ctx.u : ℂ) := by
        simp only [FTTypePSetupContext.q]
        push_cast
        ring

  by_cases hzOne : z = 1
  · subst z
    change
      ClassFunction.induce B
          ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
            ClassFunction B ℂ) 1 -
        ctx.primeTI.primeTICharacter ctx.isoS
          IrreducibleCharacter.trivial j 1 = 0
    rw [hIndOne, hIrrOne, sub_self]

  have hzOneG : (z : G) ≠ 1 := by
    intro hz
    apply hzOne
    exact Subtype.ext hz
  have hzNotP : (z : G) ∉ ctx.P := by
    intro hzP
    apply hzCore
    change (z : G) ∈
      subgroupNonidentity ctx.P ∪
        classSupportWithin S (cyclicTISet W W₁ W₂)
    exact Or.inl (mem_subgroupNonidentity.mpr ⟨hzP, hzOneG⟩)
  have hzNotH : z ∉ ctx.H.subgroupOf S := by
    intro hzH
    apply hzNotP
    rw [hP_eq_H]
    exact hzH

  have hmuSupport :
      ctx.mu j ∈
        ClassFunction.supportedOn
          ((ctx.H.subgroupOf S : Subgroup S) : Set S) := by
    exact seqInd_on (ctx.H.subgroupOf S)
      (FTprTIred_Ind_Fitting ctx j hj)
  have hmuZero : ctx.mu j z = 0 :=
    ClassFunction.eq_zero_of_mem_supportedOn hmuSupport hzNotH

  let zD : D := ⟨z, hzD⟩
  have hresIrr :
      ctx.primeTI.primeTICharacter ctx.isoS
          IrreducibleCharacter.trivial j z =
        (ctx.primeTI.primeTI_Ires ctx.isoS j :
          ClassFunction D ℂ) zD := by
    have h := congrArg (fun f : ClassFunction D ℂ ↦ f zD)
      (ctx.primeTI.cfRes_prTIirr ctx.isoS
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j)
    simpa only [ClassFunction.restrict_apply] using h
  have hresRed :
      ctx.mu j z =
        (Nat.card W₁ : ℂ) *
          (ctx.primeTI.primeTI_Ires ctx.isoS j :
            ClassFunction D ℂ) zD := by
    have h := congrArg (fun f : ClassFunction D ℂ ↦ f zD)
      (ctx.primeTI.cfRes_prTIred ctx.isoS j)
    simpa only [ClassFunction.restrict_apply, ClassFunction.smul_apply,
      smul_eq_mul] using h
  have hIrrZero :
      ctx.primeTI.primeTICharacter ctx.isoS
          IrreducibleCharacter.trivial j z = 0 := by
    apply mul_left_cancel₀ hqC
    calc
      (Nat.card W₁ : ℂ) *
          ctx.primeTI.primeTICharacter ctx.isoS
            IrreducibleCharacter.trivial j z =
        (Nat.card W₁ : ℂ) *
          (ctx.primeTI.primeTI_Ires ctx.isoS j :
            ClassFunction D ℂ) zD := by
              rw [hresIrr]
      _ = ctx.mu j z := hresRed.symm
      _ = 0 := hmuZero
      _ = (Nat.card W₁ : ℂ) * 0 := by simp

  have hzDlocal : z ∈ D := by
    exact hzD
  have hPD : P ≤ D := by
    intro p hp
    change (p : G) ∈ derivedWithin S
    exact hinner.1 hp
  have hDW : Disjoint D W₁S := by
    simpa only [D, W₁S] using houter.2.2.2.disjoint
  have hB_sup : B = P ⊔ W₁S := by
    rfl
  have hDB_le : D ⊓ B ≤ P := by
    intro y hy
    have hySup : y ∈ P ⊔ W₁S := by
      rw [← hB_sup]
      exact hy.2
    have hyProd : y ∈ (P : Set S) * (W₁S : Set S) := by
      rw [← Subgroup.normal_mul P W₁S]
      exact hySup
    rcases Set.mem_mul.mp hyProd with ⟨p, hp, w, hw, hpw⟩
    have hpD : p ∈ D := hPD hp
    have hwD : w ∈ D := by
      have hmul : p⁻¹ * y ∈ D := D.mul_mem (D.inv_mem hpD) hy.1
      have heq : p⁻¹ * y = w := by
        rw [← hpw]
        group
      rwa [heq] at hmul
    have hwBot : w ∈ (⊥ : Subgroup S) :=
      hDW.le_bot ⟨hwD, hw⟩
    have hwOne : w = 1 := Subgroup.mem_bot.mp hwBot
    have hyEq : y = p := by
      rw [← hpw, hwOne, mul_one]
    rwa [hyEq]

  have hconjNotB (x : S) : x⁻¹ * z * x ∉ B := by
    intro hxB
    have hxD : x⁻¹ * z * x ∈ D := by
      simpa using (inferInstance : D.Normal).conj_mem z hzDlocal x⁻¹
    have hxP : x⁻¹ * z * x ∈ P := hDB_le ⟨hxD, hxB⟩
    have hzP : z ∈ P := by
      have hback :=
        (inferInstance : P.Normal).conj_mem (x⁻¹ * z * x) hxP x
      have heq : x * (x⁻¹ * z * x) * x⁻¹ = z := by group
      rwa [heq] at hback
    exact hzNotP hzP

  have hIndZero :
      ClassFunction.induce B
          ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
            ClassFunction B ℂ) z = 0 := by
    rw [ClassFunction.induce_apply_formula]
    apply mul_eq_zero_of_right
    apply Finset.sum_eq_zero
    intro x _hx
    rw [dif_neg (hconjNotB x)]

  change
    ClassFunction.induce B
        ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
          ClassFunction B ℂ) z -
      ctx.primeTI.primeTICharacter ctx.isoS
        IrreducibleCharacter.trivial j z = 0
  rw [hIndZero, hIrrZero, sub_self]

private theorem supportBridges_typePGamma_apply_W₁
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (x : W₁) (hx : x ≠ 1) :
    supportBridges_typePGamma ctx
        ⟨(x : G), ctx.primeTI.complement_le_group x.property⟩ = 1 := by
  classical
  let P : Subgroup S := (Fitting_core S).subgroupOf S
  letI : P.Normal := by
    simpa only [P] using Fcore_normal S
  let J₀ : Subgroup G := U ⊔ W₁
  have hJ₀S : J₀ ≤ S :=
    (Ptype_Fcore_sdprod ctx.ptypeCtx).2.1
  let J : Subgroup S := J₀.subgroupOf S
  let UJ₀ : Subgroup J₀ := U.subgroupOf J₀
  let WJ₀ : Subgroup J₀ := W₁.subgroupOf J₀
  let US : Subgroup S := U.subgroupOf S
  let W₁S : Subgroup S := W₁.subgroupOf S
  let B : Subgroup S := FTtypePBridgeInducingSubgroup S W₁
  let q : S →* S ⧸ P := QuotientGroup.mk' P
  let xS : S :=
    ⟨(x : G), ctx.primeTI.complement_le_group x.property⟩

  have hcomp : P.IsComplement' J := by
    simpa only [P, J, J₀] using
      (Ptype_Fcore_sdprod ctx.ptypeCtx).2.2.2
  let eJ : J ≃* J₀ := Subgroup.subgroupOfEquivOfLe hJ₀S
  let e : J₀ ≃* (S ⧸ P) :=
    eJ.symm.trans (supportBridges_rightQuotientMulEquiv hcomp)
  have he_apply (a : J₀) :
      e.toMonoidHom a =
        q ⟨(a : G), hJ₀S a.property⟩ := by
    change supportBridges_rightQuotientMulEquiv hcomp
      (eJ.symm a) = _
    rw [supportBridges_rightQuotientMulEquiv_apply]
    rfl

  have hFrob₀ : IsFrobeniusDecomposition UJ₀ WJ₀ := by
    simpa only [PTypeFrobeniusProduct, J₀, UJ₀, WJ₀] using
      (FTtypeP_facts ctx).2.2.1

  have hUmap : US.map q = UJ₀.map e.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨u, hu, rfl⟩
      change (u : G) ∈ U at hu
      have huJ₀ : (u : G) ∈ J₀ := by
        change (u : G) ∈ U ⊔ W₁
        exact (show U ≤ U ⊔ W₁ from le_sup_left) hu
      let a : J₀ := ⟨(u : G), huJ₀⟩
      refine ⟨a, ?_, ?_⟩
      · change (a : G) ∈ U
        simpa only [a] using hu
      · calc
          e.toMonoidHom a =
              q ⟨(a : G), hJ₀S a.property⟩ := he_apply a
          _ = q u := by
            apply congrArg q
            exact Subtype.ext rfl
    · rintro ⟨a, ha, rfl⟩
      change (a : G) ∈ U at ha
      let u : S := ⟨(a : G), hJ₀S a.property⟩
      refine ⟨u, ?_, ?_⟩
      · exact ha
      · simpa only [u] using (he_apply a).symm

  have hB_eq : B = P ⊔ W₁S := by
    rfl
  have hBmapW : B.map q = W₁S.map q := by
    rw [hB_eq, Subgroup.map_sup]
    change P.map (QuotientGroup.mk' P) ⊔ W₁S.map q = W₁S.map q
    rw [QuotientGroup.map_mk'_self, bot_sup_eq]
  have hWmap : W₁S.map q = WJ₀.map e.toMonoidHom := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      change (w : G) ∈ W₁ at hw
      have hwJ₀ : (w : G) ∈ J₀ := by
        change (w : G) ∈ U ⊔ W₁
        exact (show W₁ ≤ U ⊔ W₁ from le_sup_right) hw
      let a : J₀ := ⟨(w : G), hwJ₀⟩
      refine ⟨a, ?_, ?_⟩
      · change (a : G) ∈ W₁
        simpa only [a] using hw
      · calc
          e.toMonoidHom a =
              q ⟨(a : G), hJ₀S a.property⟩ := he_apply a
          _ = q w := by
            apply congrArg q
            exact Subtype.ext rfl
    · rintro ⟨a, ha, rfl⟩
      change (a : G) ∈ W₁ at ha
      let w : S := ⟨(a : G), hJ₀S a.property⟩
      refine ⟨w, ?_, ?_⟩
      · exact ha
      · simpa only [w] using (he_apply a).symm

  let Kq : Subgroup (S ⧸ P) := US.map q
  let Rq : Subgroup (S ⧸ P) := B.map q
  have hKqmap : Kq = UJ₀.map e.toMonoidHom := by
    simpa only [Kq] using hUmap
  have hRqmap : Rq = WJ₀.map e.toMonoidHom := by
    simpa only [Rq] using hBmapW.trans hWmap
  have hFrobq : IsFrobeniusDecomposition Kq Rq := by
    rw [hKqmap, hRqmap]
    exact FTContextInternal.frobenius_map_mulEquiv8 hFrob₀ e

  let gammaq : ClassFunction (S ⧸ P) ℂ :=
    ClassFunction.induce Rq
      ((IrreducibleCharacter.trivial : IrreducibleCharacter Rq ℂ) :
        ClassFunction Rq ℂ)
  have hPB : P ≤ B := by
    rw [hB_eq]
    exact le_sup_left
  have hcomapTrivial :
      ClassFunction.comap (q.subgroupMap B)
          ((IrreducibleCharacter.trivial : IrreducibleCharacter Rq ℂ) :
            ClassFunction Rq ℂ) =
        ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
          ClassFunction B ℂ) := by
    apply ClassFunction.ext
    intro b
    simp only [ClassFunction.comap_apply,
      IrreducibleCharacter.trivial_apply]
  have hinflate : ClassFunction.inflate P gammaq =
      ClassFunction.induce B
        ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
          ClassFunction B ℂ) := by
    calc
      ClassFunction.inflate P gammaq =
          ClassFunction.induce B
            (ClassFunction.comap (q.subgroupMap B)
              ((IrreducibleCharacter.trivial : IrreducibleCharacter Rq ℂ) :
                ClassFunction Rq ℂ)) := by
                simpa only [gammaq, q, Rq] using
                  (ClassFunction.inflate_induce_quotientImage
                    (k := ℂ) P B hPB
                    ((IrreducibleCharacter.trivial :
                        IrreducibleCharacter Rq ℂ) :
                      ClassFunction Rq ℂ))
      _ = ClassFunction.induce B
          ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
            ClassFunction B ℂ) := by
            rw [hcomapTrivial]
  have hgamma : supportBridges_typePGamma ctx =
      ClassFunction.inflate P gammaq := by
    change ClassFunction.induce B
        ((IrreducibleCharacter.trivial : IrreducibleCharacter B ℂ) :
          ClassFunction B ℂ) = ClassFunction.inflate P gammaq
    exact hinflate.symm

  have hxRq : q xS ∈ Rq := by
    change q xS ∈ B.map q
    rw [hBmapW]
    refine ⟨xS, ?_, rfl⟩
    change (x : G) ∈ W₁
    exact x.property
  let xq : Rq := ⟨q xS, hxRq⟩
  have hxq : xq ≠ 1 := by
    intro hxqOne
    have hqxOne : q xS = 1 := congrArg Subtype.val hxqOne
    have hxP : xS ∈ P := by
      change QuotientGroup.mk' P xS = 1 at hqxOne
      exact (QuotientGroup.eq_one_iff xS).mp hqxOne
    have hxJ : xS ∈ J := by
      change (x : G) ∈ J₀
      change (x : G) ∈ U ⊔ W₁
      exact (show W₁ ≤ U ⊔ W₁ from le_sup_right) x.property
    have hxBot : xS ∈ (⊥ : Subgroup S) := by
      rw [← disjoint_iff.mp hcomp.disjoint]
      exact ⟨hxP, hxJ⟩
    have hxSOne : xS = (1 : S) := Subgroup.mem_bot.mp hxBot
    have hxGOne : (x : G) = 1 := by
      simpa only [xS, Subgroup.coe_one] using
        congrArg (fun s : S ↦ (s : G)) hxSOne
    exact hx (Subtype.ext hxGOne)
  have hgammaq : gammaq (xq : S ⧸ P) = 1 := by
    simpa only [gammaq, if_neg hxq] using
      (supportBridges_frobenius_induce_trivial_apply Kq Rq hFrobq xq)

  calc
    supportBridges_typePGamma ctx xS =
        ClassFunction.inflate P gammaq xS := by rw [hgamma]
    _ = gammaq (q xS) := rfl
    _ = gammaq (xq : S ⧸ P) := rfl
    _ = 1 := hgammaq

private theorem supportBridges_typePMu_apply_W₁
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (x : W₁) (hx : x ≠ 1) :
    supportBridges_typePMu ctx j
        ⟨(x : G), ctx.primeTI.complement_le_group x.property⟩ = 1 := by
  letI : IsCyclic W₂ := ctx.primeTI.fixed_cyclic
  let xW : W := defW.leftEmbedding x
  have hxW₂ : (x : G) ∉ W₂ := by
    intro hxMem
    have hxMem' : (((defW.mulEquiv (x, 1) : W) : G)) ∈ W₂ := by
      simpa using hxMem
    exact hx ((defW.mulEquiv_mem_right_iff (x, 1)).mp hxMem')
  have hxPrime : xW ∈ primeTISetInW W W₂ :=
    mem_primeTISetInW.mpr hxW₂
  have hvalue :=
    (ctx.primeTI.primeTICharacterData ctx.isoS).restrict_character
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j
      hxPrime
  have hvalue' :
      ctx.primeTI.primeTICharacter ctx.isoS
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j
          ⟨(x : G), ctx.primeTI.complement_le_group x.property⟩ =
        (ctx.primeTI.primeTISign ctx.isoS j : ℂ) *
          IrreducibleCharacter.cyclicTICharacter defW
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j
            xW := by
    simpa [xW, PrimeTIHypothesis.primeTICharacter,
      PrimeTIHypothesis.primeTIIndex,
      PrimeTIHypothesis.primeTISign] using hvalue
  have hsign : ctx.primeTI.primeTISign ctx.isoS j = 1 := by
    simpa only [FTTypePSetupContext.delta] using FTprTIsign ctx j
  have hsignC : (ctx.primeTI.primeTISign ctx.isoS j : ℂ) = 1 := by
    exact_mod_cast hsign
  have hcyc :
      IrreducibleCharacter.cyclicTICharacter defW
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j
          xW = 1 := by
    change
      IrreducibleCharacter.cyclicTICharacter defW
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j
          (defW.leftEmbedding x) = 1
    rw [IrreducibleCharacter.cyclicTICharacter_leftEmbedding,
      IrreducibleCharacter.trivial_apply,
      IrreducibleCharacter.apply_one_eq_one_of_isCyclic,
      one_mul]
  calc
    supportBridges_typePMu ctx j
        ⟨(x : G), ctx.primeTI.complement_le_group x.property⟩ =
      ctx.primeTI.primeTICharacter ctx.isoS
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j
        ⟨(x : G), ctx.primeTI.complement_le_group x.property⟩ := rfl
    _ = (ctx.primeTI.primeTISign ctx.isoS j : ℂ) *
          IrreducibleCharacter.cyclicTICharacter defW
            (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ) j
            xW := hvalue'
    _ = 1 := by rw [hsignC, hcyc, one_mul]

/-! ## Coset partition and exclusion of the mixed cyclic-TI case -/

private theorem supportBridges_exists_W₁_conjugate_of_not_mem_derived
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (z : S)
    (hzD : (z : G) ∉ derivedWithin S)
    (hzCore : z ∉ FTtypePBridgeCoreSupport S W W₁ W₂) :
    ∃ (y : S) (x : W₁), x ≠ 1 ∧
      (z : G) = (y : G) * (x : G) * (y : G)⁻¹ := by
  classical
  change (z : G) ∉
      subgroupNonidentity (Fitting_core S) ∪
        classSupportWithin S (cyclicTISet W W₁ W₂) at hzCore
  rcases ctx.primeTI.semidirect_complement.2 z with
    ⟨⟨dS, xS⟩, hdxS⟩
  let d : derivedWithin S :=
    ⟨((dS : S) : G), dS.property⟩
  let x : W₁ :=
    ⟨((xS : S) : G), xS.property⟩
  have hzx : (d : G) * (x : G) = (z : G) := by
    simpa [d, x] using congrArg Subtype.val hdxS
  have hx : x ≠ 1 := by
    intro hxOne
    apply hzD
    have hzEq : (d : G) = (z : G) := by
      simpa [hxOne] using hzx
    rw [← hzEq]
    exact d.property

  have hxNorm :
      (x : G) ∈ Subgroup.normalizer (derivedWithin S : Set G) :=
    ctx.primeTI.group_le_normalizer_kernel
      (ctx.primeTI.complement_le_group x.property)
  have hxCop : Nat.Coprime (Nat.card (derivedWithin S)) (orderOf (x : G)) :=
    ctx.primeTI.kernel_complement_card_coprime.coprime_dvd_right
      (W₁.orderOf_dvd_natCard x.property)
  have hpart := partition_cent_rcoset
    (derivedWithin S) (x : G) hxNorm hxCop
  let conjugationAction :=
    subgroupConjugationActionOnAmbient (derivedWithin S)
  letI : SMul (derivedWithin S) G := conjugationAction.toSMul
  letI : MulAction (derivedWithin S) G := conjugationAction.toMulAction
  letI : MulAction (derivedWithin S) (Set G) := Set.mulActionSet
  let C := centralizerWithin (derivedWithin S) (Subgroup.zpowers (x : G))
  have hC : C = W₂ := ctx.primeTI.centralizer_kernel x hx
  have hzCoset :
      (z : G) ∈
        (derivedWithin S : Set G) * ({(x : G)} : Set G) := by
    exact Set.mem_mul.mpr
      ⟨(d : G), d.property, (x : G), by simp, hzx⟩
  have hzUnion : (z : G) ∈
      ⋃₀ (MulAction.orbit (derivedWithin S)
        ((C : Set G) * ({(x : G)} : Set G))) := by
    rw [hpart.1.1]
    exact hzCoset
  rcases Set.mem_sUnion.mp hzUnion with ⟨A, hA, hzA⟩
  rcases hA with ⟨y, rfl⟩
  rcases Set.mem_smul_set.mp hzA with ⟨v, hv, hvz⟩
  rcases Set.mem_mul.mp hv with ⟨c, hc, t, ht, hct⟩
  have htEq : t = (x : G) := Set.mem_singleton_iff.mp ht
  subst t
  have hconj :
      (z : G) = (y : G) * (c * (x : G)) * (y : G)⁻¹ := by
    change (y : G) * v * (y : G)⁻¹ = (z : G) at hvz
    rw [← hvz, ← hct]
  have hcW₂ : c ∈ W₂ := by
    rw [← hC]
    exact hc
  have hcOne : c = 1 := by
    by_contra hcNe
    let c₀ : W₂ := ⟨c, hcW₂⟩
    have hc₀Ne : c₀ ≠ 1 := by
      intro hc₀One
      exact hcNe (congrArg Subtype.val hc₀One)
    have hprodV :
        (((defW.mulEquiv (x, c₀) : W) : G)) ∈
          cyclicTISet W W₁ W₂ := by
      rw [mem_cyclicTISet, defW.mulEquiv_mem_left_iff,
        defW.mulEquiv_mem_right_iff]
      exact ⟨(defW.mulEquiv (x, c₀)).property, hc₀Ne, hx⟩
    have hcxV : c * (x : G) ∈ cyclicTISet W W₁ W₂ := by
      have hprod :
          (((defW.mulEquiv (x, c₀) : W) : G)) =
            c * (x : G) := by
        exact (defW.commute x c₀).eq
      rwa [hprod] at hprodV
    have hzClass : (z : G) ∈
        classSupportWithin S (cyclicTISet W W₁ W₂) := by
      refine ⟨c * (x : G), hcxV, ?_⟩
      refine ⟨(y : G)⁻¹,
        S.inv_mem (ctx.primeTI.kernel_le_group y.property), ?_⟩
      simpa using hconj.symm
    exact hzCore (Or.inr hzClass)
  let yS : S :=
    ⟨(y : G), ctx.primeTI.kernel_le_group y.property⟩
  refine ⟨yS, x, hx, ?_⟩
  simpa [yS, hcOne] using hconj

/-! ## Requested outside-derived pointwise branch -/

private theorem supportBridges_bridge_zero_of_not_mem_derived
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (_hj : j ≠ IrreducibleCharacter.trivial)
    (z : S)
    (hzD : (z : G) ∉ derivedWithin S)
    (hzCore : z ∉ FTtypePBridgeCoreSupport S W W₁ W₂) :
    FTtypeP_bridge ctx j z = 0 := by
  obtain ⟨y, x, hx, hzx⟩ :=
    supportBridges_exists_W₁_conjugate_of_not_mem_derived
      ctx z hzD hzCore
  let xS : S :=
    ⟨(x : G), ctx.primeTI.complement_le_group x.property⟩
  have hzxS : z = y * xS * y⁻¹ := by
    apply Subtype.ext
    exact hzx
  have hgamma : supportBridges_typePGamma ctx z = 1 := by
    rw [hzxS,
      ClassFunction.conj_apply (supportBridges_typePGamma ctx) y xS]
    exact supportBridges_typePGamma_apply_W₁ ctx x hx
  have hmu : supportBridges_typePMu ctx j z = 1 := by
    rw [hzxS,
      ClassFunction.conj_apply (supportBridges_typePMu ctx j) y xS]
    exact supportBridges_typePMu_apply_W₁ ctx j x hx
  rw [supportBridges_bridge_eq_gamma_sub_mu,
    ClassFunction.sub_apply, hgamma, hmu, sub_self]

/-! ## Hermitian pairing and norm adapters -/

private theorem supportBridges_starPairing_sub_left
    {Q : Type*} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    starCharacterPairing (f - g) h =
      starCharacterPairing f h - starCharacterPairing g h := by
  simp [sub_eq_add_neg, starCharacterPairing, twistedCharacterPairing,
    add_mul, Finset.sum_add_distrib]
  ring

private theorem supportBridges_starPairing_sub_right
    {Q : Type*} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    starCharacterPairing f (g - h) =
      starCharacterPairing f g - starCharacterPairing f h := by
  simp [sub_eq_add_neg, starCharacterPairing, twistedCharacterPairing,
    mul_add, Finset.sum_add_distrib]

private theorem supportBridges_normSq_add_of_orthogonal
    {Q : Type*} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ)
    (hfg : starCharacterPairing f g = 0) :
    classFunctionNormSq (f + g) =
      classFunctionNormSq f + classFunctionNormSq g := by
  have hgf : starCharacterPairing g f = 0 := by
    rw [starCharacterPairing_conj_symm, hfg]
    simp
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    starCharacterPairing_add_left, starCharacterPairing_add_right,
    starCharacterPairing_add_right, hfg, hgf]
  simp

private theorem supportBridges_normSq_smul
    {Q : Type*} [Group Q] [Fintype Q]
    (a : ℂ) (f : ClassFunction Q ℂ) :
    classFunctionNormSq (a • f) =
      Complex.normSq a * classFunctionNormSq f := by
  unfold classFunctionNormSq
  simp only [ClassFunction.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]
  ring

private theorem supportBridges_gap_norm
    {Q : Type*} [Group Q] [Fintype Q]
    (betaImage Gamma eta oneQ : ClassFunction Q ℂ)
    (r : ℝ) (a : ℤ)
    (hbetaNorm : classFunctionNormSq betaImage = r + 2)
    (hbetaImage : betaImage = Gamma - eta + oneQ)
    (hGammaOne : starCharacterPairing Gamma oneQ = 0)
    (hetaOne : starCharacterPairing eta oneQ = 0)
    (honeNorm : classFunctionNormSq oneQ = 1)
    (hetaNorm : classFunctionNormSq eta = 1)
    (hGammaEta : starCharacterPairing Gamma eta = (a : ℂ)) :
    classFunctionNormSq Gamma = r + 2 * (a : ℝ) := by
  have hetaGamma : starCharacterPairing eta Gamma = (a : ℂ) := by
    rw [starCharacterPairing_conj_symm, hGammaEta]
    simp
  have hdiffOne : starCharacterPairing (Gamma - eta) oneQ = 0 := by
    rw [supportBridges_starPairing_sub_left, hGammaOne, hetaOne, sub_self]
  have hdiffNorm : classFunctionNormSq (Gamma - eta) =
      classFunctionNormSq Gamma + 1 - 2 * (a : ℝ) := by
    rw [classFunctionNormSq_eq_re_starCharacterPairing,
      supportBridges_starPairing_sub_left,
      supportBridges_starPairing_sub_right,
      supportBridges_starPairing_sub_right,
      starCharacterPairing_self_eq_classFunctionNormSq,
      starCharacterPairing_self_eq_classFunctionNormSq,
      hGammaEta, hetaGamma, hetaNorm]
    norm_num
    ring
  have hsumNorm : classFunctionNormSq betaImage =
      classFunctionNormSq (Gamma - eta) + classFunctionNormSq oneQ := by
    rw [hbetaImage,
      supportBridges_normSq_add_of_orthogonal _ _ hdiffOne]
  rw [hbetaNorm, hdiffNorm, honeNorm] at hsumNorm
  nlinarith

/-!
The corrected form of (13.18)(d) is a two-coordinate Bessel estimate.
The two coordinates are `eta` and its inverse.  Integrality of `a` is the
only discrete input: `2 * a * (1-a) ≤ 0` for every integer `a`.
-/
private theorem supportBridges_twoCoordinate_norm_bound
    {Q : Type*} [Group Q] [Fintype Q]
    (Gamma X Y eta etaInv : ClassFunction Q ℂ)
    (r : ℝ) (a : ℤ)
    (hGamma : Gamma = X + Y)
    (hXY : starCharacterPairing X Y = 0)
    (hetaNorm : classFunctionNormSq eta = 1)
    (hetaInvNorm : classFunctionNormSq etaInv = 1)
    (hetaInvOrth : starCharacterPairing eta etaInv = 0)
    (hXeta : starCharacterPairing X eta = (a : ℂ))
    (hXetaInv : starCharacterPairing X etaInv = (a : ℂ))
    (hGammaNorm : classFunctionNormSq Gamma = r + 2 * (a : ℝ)) :
    classFunctionNormSq Y ≤ r := by
  let X₀ : ClassFunction Q ℂ :=
    X - (a : ℂ) • eta - (a : ℂ) • etaInv
  have hetaInvEta : starCharacterPairing etaInv eta = 0 := by
    rw [starCharacterPairing_conj_symm, hetaInvOrth]
    simp
  have hX₀eta : starCharacterPairing X₀ eta = 0 := by
    dsimp only [X₀]
    rw [supportBridges_starPairing_sub_left,
      supportBridges_starPairing_sub_left,
      starCharacterPairing_smul_left,
      starCharacterPairing_smul_left,
      hXeta, hetaInvEta]
    rw [starCharacterPairing_self_eq_classFunctionNormSq, hetaNorm]
    norm_num
  have hX₀etaInv : starCharacterPairing X₀ etaInv = 0 := by
    dsimp only [X₀]
    rw [supportBridges_starPairing_sub_left,
      supportBridges_starPairing_sub_left,
      starCharacterPairing_smul_left,
      starCharacterPairing_smul_left,
      hXetaInv, hetaInvOrth]
    rw [starCharacterPairing_self_eq_classFunctionNormSq, hetaInvNorm]
    norm_num
  have hX₀projection : starCharacterPairing X₀
      ((a : ℂ) • eta + (a : ℂ) • etaInv) = 0 := by
    rw [starCharacterPairing_add_right,
      starCharacterPairing_smul_right,
      starCharacterPairing_smul_right, hX₀eta, hX₀etaInv]
    simp
  have hprojectionOrth : starCharacterPairing
      ((a : ℂ) • eta) ((a : ℂ) • etaInv) = 0 := by
    rw [starCharacterPairing_smul_left,
      starCharacterPairing_smul_right, hetaInvOrth]
    simp
  have hXdecomp :
      X = X₀ + ((a : ℂ) • eta + (a : ℂ) • etaInv) := by
    dsimp only [X₀]
    abel
  have hprojectionNorm :
      classFunctionNormSq
          ((a : ℂ) • eta + (a : ℂ) • etaInv) =
        2 * (a : ℝ) ^ 2 := by
    rw [supportBridges_normSq_add_of_orthogonal _ _ hprojectionOrth,
      supportBridges_normSq_smul,
      supportBridges_normSq_smul, hetaNorm, hetaInvNorm]
    simp only [Complex.normSq_intCast]
    ring
  have hXnorm : classFunctionNormSq X =
      classFunctionNormSq X₀ + 2 * (a : ℝ) ^ 2 := by
    rw [hXdecomp,
      supportBridges_normSq_add_of_orthogonal _ _ hX₀projection,
      hprojectionNorm]
  have hGammaDecomp : classFunctionNormSq Gamma =
      classFunctionNormSq X + classFunctionNormSq Y := by
    rw [hGamma,
      supportBridges_normSq_add_of_orthogonal _ _ hXY]
  have haDiscrete : (a : ℝ) ≤ 0 ∨ 1 ≤ (a : ℝ) := by
    have haInt : a ≤ 0 ∨ 1 ≤ a := by omega
    rcases haInt with ha | ha
    · exact Or.inl (by exact_mod_cast ha)
    · exact Or.inr (by exact_mod_cast ha)
  have haQuadratic : 2 * (a : ℝ) - 2 * (a : ℝ) ^ 2 ≤ 0 := by
    rcases haDiscrete with ha | ha <;> nlinarith
  nlinarith [classFunctionNormSq_nonneg X₀]

/-! ## Cyclic-image and virtual-character adapters -/

private theorem supportBridges_targetMap_inverse
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    ClassFunction.inverseLinear (ctx.targetMap phi) =
      ctx.targetMap (ClassFunction.inverseLinear phi) := by
  ext x
  simp [ClassFunction.inverseLinear_apply, ClassFunction.comap_apply]

private theorem supportBridges_targetMap_starPairing
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    starCharacterPairing (ctx.targetMap phi) (ctx.targetMap psi) =
      starCharacterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold starCharacterPairing twistedCharacterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [ClassFunction.comap_apply]

private theorem supportBridges_targetMap_virtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {phi : ClassFunction (⊤ : Subgroup G) ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (ctx.targetMap phi) := by
  rcases hphi with ⟨z, hz⟩
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.symm.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]

private theorem supportBridges_targetMap_cfConjC
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    cfConjC (ctx.targetMap phi) = ctx.targetMap (cfConjC phi) := by
  apply ClassFunction.ext
  intro x
  simp [cfConjC_apply, ClassFunction.comap_apply]

private theorem supportBridges_cyclicSource_inverse
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.inverseLinear
        (CyclicTIIsometryData.cyclicTISourceIrreducible
          (defW := defW) (i, j)) =
      CyclicTIIsometryData.cyclicTISourceIrreducible
        (defW := defW)
        (IrreducibleCharacter.dual i, IrreducibleCharacter.dual j) := by
  ext w
  simp [CyclicTIIsometryData.cyclicTISourceIrreducible,
    IrreducibleCharacter.cyclicTICharacter_apply]

private theorem supportBridges_eta_inverse
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.inverseLinear (ctx.eta i j) =
      ctx.eta (IrreducibleCharacter.dual i)
        (IrreducibleCharacter.dual j) := by
  rw [supportBridges_targetMap_inverse]
  change ctx.targetMap
      (ClassFunction.inverseLinear
        (ctx.isoG.linearMap
          (CyclicTIIsometryData.cyclicTISourceIrreducible
            (defW := defW) (i, j)))) = _
  rw [ctx.isoG.inverse_cyclicTIIsometry,
    supportBridges_cyclicSource_inverse]
  rfl

private theorem supportBridges_eta_eq_signed_irreducible
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ∃ (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        ctx.eta i j =
          (epsilon : ℂ) • (chi : ClassFunction G ℂ) := by
  obtain ⟨chiTop, epsilon, hepsilon, hsource⟩ :=
    ctx.isoG.cyclicTIImage_eq_signed_irreducible (i, j)
  let chi : IrreducibleCharacter G ℂ :=
    IrreducibleCharacter.comapMulEquiv Subgroup.topEquiv.symm chiTop
  refine ⟨chi, epsilon, hepsilon, ?_⟩
  apply ClassFunction.ext
  intro x
  have hsourceAt := congrArg
    (fun f : ClassFunction (⊤ : Subgroup G) ℂ ↦
      f (Subgroup.topEquiv.symm x)) hsource
  change
    ctx.isoG.cyclicTIImage (i, j) (Subgroup.topEquiv.symm x) =
      (epsilon : ℂ) * chi x
  simpa only [ClassFunction.smul_apply, smul_eq_mul, chi,
    IrreducibleCharacter.comapMulEquiv_apply] using hsourceAt

private theorem supportBridges_eta_isVirtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (ctx.eta i j) := by
  obtain ⟨chi, epsilon, _hepsilon, heta⟩ :=
    supportBridges_eta_eq_signed_irreducible ctx i j
  refine ⟨Finsupp.single chi epsilon, ?_⟩
  rw [VirtualCharacter.realize_single]
  exact heta.symm

private theorem supportBridges_irreducible_isVirtual
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    ClassFunction.IsVirtual (chi : ClassFunction Q ℂ) := by
  refine ⟨Finsupp.single chi 1, ?_⟩
  simp

private theorem supportBridges_irreducible_normSq
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    classFunctionNormSq (chi : ClassFunction Q ℂ) = 1 := by
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (supportBridges_irreducible_isVirtual chi)
      (supportBridges_irreducible_isVirtual chi),
    IrreducibleCharacter.characterPairing_self chi]
  norm_num

private theorem supportBridges_eta_normSq
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    classFunctionNormSq (ctx.eta i j) = 1 := by
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (supportBridges_eta_isVirtual ctx i j)
      (supportBridges_eta_isVirtual ctx i j),
    FTTypePCyclicRectangleInternal.characterPairing_eta, if_pos rfl]
  norm_num

private theorem supportBridges_eta_inverse_orthogonal
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    starCharacterPairing (ctx.eta i j)
        (ctx.eta (IrreducibleCharacter.dual i)
          (IrreducibleCharacter.dual j)) = 0 := by
  rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (supportBridges_eta_isVirtual ctx i j)
      (supportBridges_eta_isVirtual ctx
        (IrreducibleCharacter.dual i) (IrreducibleCharacter.dual j)),
    FTTypePCyclicRectangleInternal.characterPairing_eta, if_neg]
  intro hpairs
  have hjdual : j = IrreducibleCharacter.dual j := congrArg Prod.snd hpairs
  exact (dual_ne_self_of_odd_of_ne_trivial
    ctx.primeTI.prime_cycTIhyp.right_odd_card hj) hjdual.symm

private theorem supportBridges_eta_trivial_trivial
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ctx.eta IrreducibleCharacter.trivial
        IrreducibleCharacter.trivial = 1 := by
  change ctx.targetMap
      (ctx.isoG.linearMap
        (CyclicTIIsometryData.cyclicTISourceIrreducible
          (defW := defW)
          (IrreducibleCharacter.trivial,
            IrreducibleCharacter.trivial))) = 1
  rw [show CyclicTIIsometryData.cyclicTISourceIrreducible
      (defW := defW)
      (IrreducibleCharacter.trivial,
        IrreducibleCharacter.trivial) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter W ℂ) :
        ClassFunction W ℂ) by
    exact congrArg
      (fun chi : IrreducibleCharacter W ℂ ↦
        (chi : ClassFunction W ℂ))
      (IrreducibleCharacter.cyclicTICharacter_trivial defW)]
  rw [ctx.isoG.map_trivial]
  ext x
  simp [ClassFunction.comap_apply]

private theorem supportBridges_eta_one_orthogonal
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    starCharacterPairing (ctx.eta i j) 1 = 0 := by
  rw [← supportBridges_eta_trivial_trivial ctx,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (supportBridges_eta_isVirtual ctx i j)
      (supportBridges_eta_isVirtual ctx
        IrreducibleCharacter.trivial IrreducibleCharacter.trivial),
    FTTypePCyclicRectangleInternal.characterPairing_eta, if_neg]
  intro hpairs
  exact hj (congrArg Prod.snd hpairs)

/-! ## Virtuality and norm transport for the bridge -/

private theorem supportBridges_bridge_isVirtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.IsVirtual (FTtypeP_bridge ctx j) := by
  let H : Subgroup S := FTtypePBridgeInducingSubgroup S W₁
  let z : VirtualCharacter H ℂ :=
    Finsupp.single IrreducibleCharacter.trivial 1
  have hInd : ClassFunction.IsVirtual
      (ClassFunction.induce H
        ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
          ClassFunction H ℂ)) := by
    refine ⟨VirtualCharacter.induce H z, ?_⟩
    simpa only [z, VirtualCharacter.realize_induce,
      VirtualCharacter.realize_single, Int.cast_one, one_smul]
  have hmu : ClassFunction.IsVirtual
      (ctx.primeTI.primeTICharacter ctx.isoS
        IrreducibleCharacter.trivial j) := by
    exact supportBridges_irreducible_isVirtual
      (ctx.primeTI.primeTIIndex ctx.isoS
        (IrreducibleCharacter.trivial, j))
  simpa only [FTtypeP_bridge, H,
    PrimeTIHypothesis.primeTICharacter] using hInd.sub hmu

private theorem supportBridges_bridge_inverse
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ) :
    ClassFunction.inverseLinear (FTtypeP_bridge ctx j) =
      FTtypeP_bridge ctx (IrreducibleCharacter.dual j) := by
  let H : Subgroup S := FTtypePBridgeInducingSubgroup S W₁
  have htriv : ClassFunction.inverseLinear
      ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
        ClassFunction H ℂ) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
        ClassFunction H ℂ) := by
    apply ClassFunction.ext
    intro x
    simp [ClassFunction.inverseLinear_apply,
      IrreducibleCharacter.trivial_apply]
  have hmu : ClassFunction.inverseLinear
      (ctx.primeTI.primeTICharacter ctx.isoS
        IrreducibleCharacter.trivial j) =
      ctx.primeTI.primeTICharacter ctx.isoS
        IrreducibleCharacter.trivial
        (IrreducibleCharacter.dual j) := by
    change ClassFunction.inverseLinear
        (ctx.primeTI.primeTIIndex ctx.isoS
          (IrreducibleCharacter.trivial, j) : ClassFunction S ℂ) =
      (ctx.primeTI.primeTIIndex ctx.isoS
        (IrreducibleCharacter.trivial,
          IrreducibleCharacter.dual j) : ClassFunction S ℂ)
    rw [show ctx.primeTI.primeTIIndex ctx.isoS
        (IrreducibleCharacter.trivial,
          IrreducibleCharacter.dual j) =
        IrreducibleCharacter.dual
          (ctx.primeTI.primeTIIndex ctx.isoS
            (IrreducibleCharacter.trivial, j)) by
      simpa only [IrreducibleCharacter.dual_trivial] using
        (ctx.primeTI.primeTIIndex_dual ctx.isoS
          IrreducibleCharacter.trivial j)]
    apply ClassFunction.ext
    intro x
    simp [ClassFunction.inverseLinear_apply]
  rw [FTtypeP_bridge, map_sub,
    ClassFunction.inverseLinear_induce H, htriv, hmu]
  rfl

private theorem supportBridges_tau_bridge_isVirtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hA : FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) :
    ClassFunction.IsVirtual (ctx.tau (FTtypeP_bridge ctx j)) := by
  obtain ⟨z, hz⟩ := supportBridges_bridge_isVirtual ctx j
  have hsourceSupport : VirtualCharacter.realize z ∈
      ClassFunction.supportedOn
        {x : S | (x : G) ∈ FTsupport0 S} := by
    rw [hz]
    simpa only [FTtypePBridgeDadeSupport, subgroupPullbackSet] using hA
  have hdade := Dade_vchar (FT_Dade0_hyp S ctx.maxS) z hsourceSupport
  have hdadeVirtual : ClassFunction.IsVirtual
      (Dade (FT_Dade0_hyp S ctx.maxS) (FTtypeP_bridge ctx j)) := by
    refine ⟨Dade_virtualCharacter (FT_Dade0_hyp S ctx.maxS) z, ?_⟩
    calc
      VirtualCharacter.realize
          (Dade_virtualCharacter (FT_Dade0_hyp S ctx.maxS) z) =
          Dade (FT_Dade0_hyp S ctx.maxS)
            (VirtualCharacter.realize z) := hdade.symm
      _ = Dade (FT_Dade0_hyp S ctx.maxS)
            (FTtypeP_bridge ctx j) := congrArg _ hz
  simpa only [FTTypePSetupContext.tau, LinearMap.comp_apply] using
    supportBridges_targetMap_virtual ctx hdadeVirtual

private theorem supportBridges_tau_bridge_inverse
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hA : FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) :
    ClassFunction.inverseLinear (ctx.tau (FTtypeP_bridge ctx j)) =
      ctx.tau (FTtypeP_bridge ctx (IrreducibleCharacter.dual j)) := by
  have hbetaVirtual := supportBridges_bridge_isVirtual ctx j
  have htauVirtual := supportBridges_tau_bridge_isVirtual ctx j hA
  rw [FTType1InfrastructureInternal.inverseEqConjOfVirtual htauVirtual]
  change cfConjC
      (ctx.targetMap
        (Dade (FT_Dade0_hyp S ctx.maxS) (FTtypeP_bridge ctx j))) =
    ctx.targetMap
      (Dade (FT_Dade0_hyp S ctx.maxS)
        (FTtypeP_bridge ctx (IrreducibleCharacter.dual j)))
  rw [supportBridges_targetMap_cfConjC]
  apply congrArg ctx.targetMap
  calc
    cfConjC
          (Dade (FT_Dade0_hyp S ctx.maxS) (FTtypeP_bridge ctx j)) =
        Dade (FT_Dade0_hyp S ctx.maxS)
          (cfConjC (FTtypeP_bridge ctx j)) :=
      (Dade_conjC (FT_Dade0_hyp S ctx.maxS)
        (FTtypeP_bridge ctx j)).symm
    _ = Dade (FT_Dade0_hyp S ctx.maxS)
          (ClassFunction.inverseLinear (FTtypeP_bridge ctx j)) :=
      congrArg (Dade (FT_Dade0_hyp S ctx.maxS))
        (FTType1InfrastructureInternal.inverseEqConjOfVirtual
          hbetaVirtual).symm
    _ = Dade (FT_Dade0_hyp S ctx.maxS)
          (FTtypeP_bridge ctx (IrreducibleCharacter.dual j)) :=
      congrArg (Dade (FT_Dade0_hyp S ctx.maxS))
        (supportBridges_bridge_inverse ctx j)

private theorem supportBridges_gap_isVirtual
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hA : FTtypeP_bridge ctx (FTtypePBridgeIndex ctx) ∈
      ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) :
    ClassFunction.IsVirtual (FTtypeP_bridge_gap ctx) := by
  have htau := supportBridges_tau_bridge_isVirtual ctx
    (FTtypePBridgeIndex ctx) hA
  have hone : ClassFunction.IsVirtual
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) := by
    exact supportBridges_irreducible_isVirtual
      (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ)
  have heta := supportBridges_eta_isVirtual ctx
    IrreducibleCharacter.trivial (FTtypePBridgeIndex ctx)
  simpa only [FTtypeP_bridge_gap] using (htau.sub hone).add heta

private theorem supportBridges_tau_bridge_normSq
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hA : FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn (FTtypePBridgeDadeSupport S))
    (hnorm : characterPairing (FTtypeP_bridge ctx j)
        (FTtypeP_bridge ctx j) =
      ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ))) :
    classFunctionNormSq (ctx.tau (FTtypeP_bridge ctx j)) =
      ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ)) + 2 := by
  have hsourceSupport : FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn
        {x : S | (x : G) ∈ FTsupport0 S} := by
    simpa only [FTtypePBridgeDadeSupport, subgroupPullbackSet] using hA
  have hbetaVirtual := supportBridges_bridge_isVirtual ctx j
  have hstar : starCharacterPairing
      (ctx.tau (FTtypeP_bridge ctx j))
      (ctx.tau (FTtypeP_bridge ctx j)) =
      ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ)) := by
    change starCharacterPairing
      (ctx.targetMap
        (Dade (FT_Dade0_hyp S ctx.maxS) (FTtypeP_bridge ctx j)))
      (ctx.targetMap
        (Dade (FT_Dade0_hyp S ctx.maxS) (FTtypeP_bridge ctx j))) = _
    rw [supportBridges_targetMap_starPairing,
      Dade_isometry (FT_Dade0_hyp S ctx.maxS)
        (FTtypeP_bridge ctx j) (FTtypeP_bridge ctx j)
        hsourceSupport hsourceSupport,
      PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hbetaVirtual hbetaVirtual,
      hnorm]
  rw [classFunctionNormSq_eq_re_starCharacterPairing, hstar]
  norm_num [Nat.cast_add]

/-! ## Constancy of the gap across nontrivial right indices -/

private theorem supportBridges_gap_constant
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial) :
    ctx.tau (FTtypeP_bridge ctx j) - 1 +
        ctx.eta IrreducibleCharacter.trivial j =
      FTtypeP_bridge_gap ctx := by
  let j₀ : IrreducibleCharacter W₂ ℂ := FTtypePBridgeIndex ctx
  let oneG : ClassFunction G ℂ :=
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)
  have honeEq : (1 : ClassFunction G ℂ) = oneG := by
    rfl
  have hj₀ : j₀ ≠ IrreducibleCharacter.trivial :=
    FTtypePBridgeIndex_ne_trivial ctx
  have hdegree :
      ctx.primeTI.primeTICharacter ctx.isoS
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          j 1 =
        ctx.primeTI.primeTICharacter ctx.isoS
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₁ ℂ)
          j₀ 1 := by
    apply mul_left_cancel₀
      (Nat.cast_ne_zero.mpr
        (Nat.card_pos.ne' : Nat.card W₁ ≠ 0))
    rw [← ctx.primeTI.prTIred_1 ctx.isoS j,
      ← ctx.primeTI.prTIred_1 ctx.isoS j₀,
      FTprTIred1 ctx j hj, FTprTIred1 ctx j₀ hj₀]
  have hDadeMu := ctx.primeDade.prDade_sub_TIirr
    ctx.isoS ctx.isoG IrreducibleCharacter.trivial j j₀
      hj hj₀ hdegree
  have hDadeMu' :
      Dade (FT_Dade0_hyp S ctx.maxS)
          (ctx.primeTI.primeTICharacter ctx.isoS
              IrreducibleCharacter.trivial j -
            ctx.primeTI.primeTICharacter ctx.isoS
              IrreducibleCharacter.trivial j₀) =
        ctx.isoG.cyclicTIImage
            (IrreducibleCharacter.trivial, j) -
          ctx.isoG.cyclicTIImage
            (IrreducibleCharacter.trivial, j₀) := by
    simpa only [FTprTIsign ctx j, Int.cast_one, one_smul] using hDadeMu
  have hTauMu :
      ctx.tau
          (ctx.primeTI.primeTICharacter ctx.isoS
              IrreducibleCharacter.trivial j -
            ctx.primeTI.primeTICharacter ctx.isoS
              IrreducibleCharacter.trivial j₀) =
        ctx.eta IrreducibleCharacter.trivial j -
          ctx.eta IrreducibleCharacter.trivial j₀ := by
    change ctx.targetMap
        (Dade (FT_Dade0_hyp S ctx.maxS)
          (ctx.primeTI.primeTICharacter ctx.isoS
              IrreducibleCharacter.trivial j -
            ctx.primeTI.primeTICharacter ctx.isoS
              IrreducibleCharacter.trivial j₀)) = _
    rw [hDadeMu', map_sub]
  have hBridgeDiff :
      FTtypeP_bridge ctx j - FTtypeP_bridge ctx j₀ =
        -(ctx.primeTI.primeTICharacter ctx.isoS
              IrreducibleCharacter.trivial j -
          ctx.primeTI.primeTICharacter ctx.isoS
              IrreducibleCharacter.trivial j₀) := by
    simp only [FTtypeP_bridge]
    module
  have hTauBridgeDiff :
      ctx.tau (FTtypeP_bridge ctx j) -
          ctx.tau (FTtypeP_bridge ctx j₀) =
        -(ctx.eta IrreducibleCharacter.trivial j -
          ctx.eta IrreducibleCharacter.trivial j₀) := by
    rw [← map_sub, hBridgeDiff, map_neg, hTauMu]
  rw [honeEq]
  change
    ctx.tau (FTtypeP_bridge ctx j) - oneG +
        ctx.eta IrreducibleCharacter.trivial j =
      ctx.tau (FTtypeP_bridge ctx j₀) - oneG +
        ctx.eta IrreducibleCharacter.trivial j₀
  calc
    ctx.tau (FTtypeP_bridge ctx j) - oneG +
          ctx.eta IrreducibleCharacter.trivial j =
        (ctx.tau (FTtypeP_bridge ctx j) -
            ctx.tau (FTtypeP_bridge ctx j₀)) +
          (ctx.tau (FTtypeP_bridge ctx j₀) - oneG) +
          ctx.eta IrreducibleCharacter.trivial j := by
            abel
    _ = -(ctx.eta IrreducibleCharacter.trivial j -
            ctx.eta IrreducibleCharacter.trivial j₀) +
          (ctx.tau (FTtypeP_bridge ctx j₀) - oneG) +
          ctx.eta IrreducibleCharacter.trivial j := by
            rw [hTauBridgeDiff]
    _ = ctx.tau (FTtypeP_bridge ctx j₀) - oneG +
          ctx.eta IrreducibleCharacter.trivial j₀ := by
            abel

private theorem supportBridges_gap_real
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hA : FTtypeP_bridge ctx (FTtypePBridgeIndex ctx) ∈
      ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) :
    cfReal (FTtypeP_bridge_gap ctx) := by
  let j₀ : IrreducibleCharacter W₂ ℂ := FTtypePBridgeIndex ctx
  have hj₀ : j₀ ≠ IrreducibleCharacter.trivial :=
    FTtypePBridgeIndex_ne_trivial ctx
  have hj₀dual : IrreducibleCharacter.dual j₀ ≠
      IrreducibleCharacter.trivial := by
    intro hdual
    apply hj₀
    have := congrArg IrreducibleCharacter.dual hdual
    simpa using this
  have honeInv : ClassFunction.inverseLinear
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) := by
    apply ClassFunction.ext
    intro x
    simp [ClassFunction.inverseLinear_apply,
      IrreducibleCharacter.trivial_apply]
  have hgapDual := supportBridges_gap_constant ctx
    (IrreducibleCharacter.dual j₀) hj₀dual
  rw [cfReal]
  dsimp only [FTtypeP_bridge_gap, j₀]
  rw [map_add, map_sub,
    supportBridges_tau_bridge_inverse ctx j₀ (by
      simpa only [j₀] using hA),
    honeInv,
    supportBridges_eta_inverse,
    IrreducibleCharacter.dual_trivial]
  exact hgapDual

/-! ## Orthogonality of the gap to the trivial character -/

private theorem supportBridges_gap_one_orthogonal
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hA : FTtypeP_bridge ctx (FTtypePBridgeIndex ctx) ∈
      ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) :
    characterPairing (FTtypeP_bridge_gap ctx) 1 = 0 := by
  let j₀ : IrreducibleCharacter W₂ ℂ := FTtypePBridgeIndex ctx
  let H : Subgroup S := FTtypePBridgeInducingSubgroup S W₁
  have hj₀ : j₀ ≠ IrreducibleCharacter.trivial :=
    FTtypePBridgeIndex_ne_trivial ctx
  have hmuNe :
      ctx.primeTI.primeTIIndex ctx.isoS
          (IrreducibleCharacter.trivial, j₀) ≠
        (IrreducibleCharacter.trivial : IrreducibleCharacter S ℂ) := by
    intro hidx
    have hidx' :
        ctx.primeTI.primeTIIndex ctx.isoS
            (IrreducibleCharacter.trivial, j₀) =
          ctx.primeTI.primeTIIndex ctx.isoS
            (IrreducibleCharacter.trivial,
              IrreducibleCharacter.trivial) := by
      rw [ctx.primeTI.prTIirr00 ctx.isoS]
      exact hidx
    have hpairs := (ctx.primeTI.primeTIirr_spec ctx.isoS).1 hidx'
    exact hj₀ (congrArg Prod.snd hpairs)
  have hrestrictH :
      ClassFunction.restrict H (1 : ClassFunction S ℂ) =
        ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
          ClassFunction H ℂ) := by
    apply ClassFunction.ext
    intro x
    simp [IrreducibleCharacter.trivial_apply]
  have hIndOne : characterPairing
      (ClassFunction.induce H
        ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
          ClassFunction H ℂ))
      (1 : ClassFunction S ℂ) = 1 := by
    rw [ClassFunction.frobeniusReciprocity H, hrestrictH]
    exact IrreducibleCharacter.characterPairing_self
      (IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ)
  have hmuOne : characterPairing
      (ctx.primeTI.primeTICharacter ctx.isoS
        IrreducibleCharacter.trivial j₀)
      (1 : ClassFunction S ℂ) = 0 := by
    change characterPairing
      (ctx.primeTI.primeTIIndex ctx.isoS
          (IrreducibleCharacter.trivial, j₀) : ClassFunction S ℂ)
      ((IrreducibleCharacter.trivial : IrreducibleCharacter S ℂ) :
        ClassFunction S ℂ) = 0
    rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg hmuNe]
  have hbetaOne : characterPairing (FTtypeP_bridge ctx j₀)
      (1 : ClassFunction S ℂ) = 1 := by
    rw [FTtypeP_bridge,
      FTType1InfrastructureInternal.pairingSubLeft,
      hIndOne, hmuOne]
    norm_num
  have hA0 : FTtypeP_bridge ctx j₀ ∈
      ClassFunction.supportedOn (ftTypePSupport0InS S) := by
    simpa only [j₀, FTtypePBridgeDadeSupport,
      subgroupPullbackSet, ftTypePSupport0InS] using hA
  have htauInduce :
      ctx.tau (FTtypeP_bridge ctx j₀) =
        ClassFunction.induce S (FTtypeP_bridge ctx j₀) :=
    (FTtypeP_facts ctx).2.2.2.2.2.2.2.2.2
      (FTtypeP_bridge ctx j₀) hA0
  have hrestrictS :
      ClassFunction.restrict S (1 : ClassFunction G ℂ) =
        (1 : ClassFunction S ℂ) := by
    apply ClassFunction.ext
    intro x
    simp [IrreducibleCharacter.trivial_apply]
  have htauOne : characterPairing
      (ctx.tau (FTtypeP_bridge ctx j₀))
      (1 : ClassFunction G ℂ) = 1 := by
    rw [htauInduce, ClassFunction.frobeniusReciprocity S,
      hrestrictS, hbetaOne]
  have hetaOneStar : starCharacterPairing
      (ctx.eta IrreducibleCharacter.trivial j₀)
      (1 : ClassFunction G ℂ) = 0 :=
    supportBridges_eta_one_orthogonal ctx
      IrreducibleCharacter.trivial j₀ hj₀
  have hetaVirtual := supportBridges_eta_isVirtual ctx
    IrreducibleCharacter.trivial j₀
  have htrivialOne :
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) =
        (1 : ClassFunction G ℂ) := by
    apply ClassFunction.ext
    intro x
    rw [IrreducibleCharacter.trivial_apply,
      ftTypePSupportBridgesOne_apply]
  have honeVirtual : ClassFunction.IsVirtual (1 : ClassFunction G ℂ) := by
    rw [← htrivialOne]
    exact supportBridges_irreducible_isVirtual
      (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ)
  have hetaOne : characterPairing
      (ctx.eta IrreducibleCharacter.trivial j₀)
      (1 : ClassFunction G ℂ) = 0 := by
    rw [← PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hetaVirtual honeVirtual]
    exact hetaOneStar
  have honeOne : characterPairing
      (1 : ClassFunction G ℂ) (1 : ClassFunction G ℂ) = 1 := by
    rw [← htrivialOne]
    exact IrreducibleCharacter.characterPairing_self
      (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ)
  dsimp only [FTtypeP_bridge_gap, j₀]
  rw [htrivialOne, characterPairing_add_left,
    FTType1InfrastructureInternal.pairingSubLeft,
    htauOne, honeOne, hetaOne]
  norm_num

private theorem supportBridges_eta_mem_cyclicImageFamily
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ctx.eta i j ∈ FTtypePCyclicImageFamily ctx := by
  rw [FTtypePCyclicImageFamily, Finset.mem_image]
  refine ⟨(IrreducibleCharacter.cyclicTICharacter defW i j :
    ClassFunction W ℂ), ?_, rfl⟩
  rw [irreducibleClassFunctionFamily, Finset.mem_image]
  exact ⟨IrreducibleCharacter.cyclicTICharacter defW i j,
    Finset.mem_univ _, rfl⟩

/-!
The complete corrected norm clause, factored from the hard support/norm
prefix.  `hTauBetaNorm` is the single quantitative seam supplied by that
prefix.  The remaining hypotheses are exactly the preceding parts of
(13.18)(c) plus virtuality of the gap.
-/
private theorem supportBridges_corrected_norm_clause
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hTauBetaNorm :
      classFunctionNormSq
          (ctx.tau
            (FTtypeP_bridge ctx (FTtypePBridgeIndex ctx))) =
        ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ)) + 2)
    (hGammaOne : characterPairing (FTtypeP_bridge_gap ctx) 1 = 0)
    (hGammaReal : cfReal (FTtypeP_bridge_gap ctx))
    (hGammaVirtual :
      ClassFunction.IsVirtual (FTtypeP_bridge_gap ctx)) :
    ∀ X Y : ClassFunction G ℂ,
      FTtypeP_bridge_gap ctx = X + Y →
      starCharacterPairing X Y = 0 →
      (∀ Z ∈
          (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)),
        starCharacterPairing Y Z = 0) →
      classFunctionNormSq Y ≤
        ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ)) := by
  intro X Y hGamma hXY hYfamily
  let j₀ : IrreducibleCharacter W₂ ℂ := FTtypePBridgeIndex ctx
  let eta : ClassFunction G ℂ :=
    ctx.eta IrreducibleCharacter.trivial j₀
  let etaInv : ClassFunction G ℂ :=
    ctx.eta IrreducibleCharacter.trivial
      (IrreducibleCharacter.dual j₀)
  let Gamma : ClassFunction G ℂ := FTtypeP_bridge_gap ctx
  let oneG : ClassFunction G ℂ :=
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)
  let r : ℝ := (((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ)
  have honeEq : (1 : ClassFunction G ℂ) = oneG := by
    rfl
  have hj₀ : j₀ ≠ IrreducibleCharacter.trivial := by
    exact FTtypePBridgeIndex_ne_trivial ctx
  have hetaVirtual : ClassFunction.IsVirtual eta :=
    supportBridges_eta_isVirtual ctx IrreducibleCharacter.trivial j₀
  have hetaInvVirtual : ClassFunction.IsVirtual etaInv :=
    supportBridges_eta_isVirtual ctx IrreducibleCharacter.trivial
      (IrreducibleCharacter.dual j₀)
  have honeVirtual : ClassFunction.IsVirtual oneG := by
    dsimp only [oneG]
    simpa using supportBridges_irreducible_isVirtual
      (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ)
  have honeNorm : classFunctionNormSq oneG = 1 := by
    dsimp only [oneG]
    simpa using supportBridges_irreducible_normSq
      (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ)
  have hetaNorm : classFunctionNormSq eta = 1 :=
    supportBridges_eta_normSq ctx IrreducibleCharacter.trivial j₀
  have hetaInvNorm : classFunctionNormSq etaInv = 1 :=
    supportBridges_eta_normSq ctx IrreducibleCharacter.trivial
      (IrreducibleCharacter.dual j₀)
  have hetaInvOrth : starCharacterPairing eta etaInv = 0 := by
    simpa only [eta, etaInv,
      IrreducibleCharacter.dual_trivial] using
        supportBridges_eta_inverse_orthogonal ctx
          IrreducibleCharacter.trivial j₀ hj₀
  have hetaOne : starCharacterPairing eta oneG = 0 := by
    change starCharacterPairing
      (ctx.eta IrreducibleCharacter.trivial j₀) oneG = 0
    rw [← honeEq]
    exact supportBridges_eta_one_orthogonal ctx
      IrreducibleCharacter.trivial j₀ hj₀
  have hGammaOneStar : starCharacterPairing Gamma oneG = 0 := by
    change starCharacterPairing (FTtypeP_bridge_gap ctx) oneG = 0
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hGammaVirtual honeVirtual,
      ← honeEq]
    exact hGammaOne
  obtain ⟨a, haPair⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt
      hGammaVirtual hetaVirtual
  have haStar : starCharacterPairing Gamma eta = (a : ℂ) := by
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hGammaVirtual hetaVirtual]
    exact haPair
  have hetaInverse : ClassFunction.inverseLinear eta = etaInv := by
    simpa only [eta, etaInv,
      IrreducibleCharacter.dual_trivial] using
        supportBridges_eta_inverse ctx
          IrreducibleCharacter.trivial j₀
  have haPairInv : characterPairing Gamma etaInv = (a : ℂ) := by
    rw [← hetaInverse,
      ← FTType1InfrastructureInternal.pairingInverseLeft,
      hGammaReal]
    exact haPair
  have haStarInv : starCharacterPairing Gamma etaInv = (a : ℂ) := by
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hGammaVirtual hetaInvVirtual]
    exact haPairInv
  have hYeta : starCharacterPairing Y eta = 0 := by
    apply hYfamily eta
    change eta ∈ FTtypePCyclicImageFamily ctx
    exact supportBridges_eta_mem_cyclicImageFamily ctx
      IrreducibleCharacter.trivial j₀
  have hYetaInv : starCharacterPairing Y etaInv = 0 := by
    apply hYfamily etaInv
    change etaInv ∈ FTtypePCyclicImageFamily ctx
    exact supportBridges_eta_mem_cyclicImageFamily ctx
      IrreducibleCharacter.trivial (IrreducibleCharacter.dual j₀)
  have hXeta : starCharacterPairing X eta = (a : ℂ) := by
    calc
      starCharacterPairing X eta =
          starCharacterPairing (X + Y) eta := by
            rw [starCharacterPairing_add_left, hYeta, add_zero]
      _ = starCharacterPairing Gamma eta := by
            change starCharacterPairing (X + Y) eta =
              starCharacterPairing (FTtypeP_bridge_gap ctx) eta
            rw [hGamma]
      _ = (a : ℂ) := haStar
  have hXetaInv : starCharacterPairing X etaInv = (a : ℂ) := by
    calc
      starCharacterPairing X etaInv =
          starCharacterPairing (X + Y) etaInv := by
            rw [starCharacterPairing_add_left, hYetaInv, add_zero]
      _ = starCharacterPairing Gamma etaInv := by
            change starCharacterPairing (X + Y) etaInv =
              starCharacterPairing (FTtypeP_bridge_gap ctx) etaInv
            rw [hGamma]
      _ = (a : ℂ) := haStarInv
  have hbetaImage :
      ctx.tau (FTtypeP_bridge ctx j₀) = Gamma - eta + oneG := by
    dsimp only [Gamma, eta, oneG, j₀, FTtypeP_bridge_gap]
    abel
  have hGammaNorm : classFunctionNormSq Gamma = r + 2 * (a : ℝ) := by
    apply supportBridges_gap_norm
      (ctx.tau (FTtypeP_bridge ctx j₀)) Gamma eta oneG r a
    · simpa only [j₀, r] using hTauBetaNorm
    · exact hbetaImage
    · exact hGammaOneStar
    · exact hetaOne
    · exact honeNorm
    · exact hetaNorm
    · exact haStar
  exact supportBridges_twoCoordinate_norm_bound
    Gamma X Y eta etaInv r a
    (by
      change FTtypeP_bridge_gap ctx = X + Y
      exact hGamma)
    hXY hetaNorm hetaInvNorm hetaInvOrth hXeta hXetaInv hGammaNorm

private theorem supportBridges_q_dvd_cardU_pred
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card W₁ ∣ Nat.card U - 1 := by
  let J : Subgroup G := U ⊔ W₁
  let UJ : Subgroup J := U.subgroupOf J
  let WJ : Subgroup J := W₁.subgroupOf J
  have hfrob : IsFrobeniusDecomposition UJ WJ := by
    simpa only [PTypeFrobeniusProduct, J, UJ, WJ] using
      (FTtypeP_facts ctx).2.2.1
  letI := hfrob.conjugationAction
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := WJ) (X := UJ))
  have hUleJ : U ≤ J := by
    simpa only [J] using (show U ≤ U ⊔ W₁ from le_sup_left)
  have hWleJ : W₁ ≤ J := by
    simpa only [J] using (show W₁ ≤ U ⊔ W₁ from le_sup_right)
  have hUJcard : Nat.card UJ = Nat.card U := by
    simpa only [UJ] using
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUleJ
  have hWJcard : Nat.card WJ = Nat.card W₁ := by
    simpa only [WJ] using
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hWleJ
  have hcard : Nat.card U = 1 + t * Nat.card W₁ := by
    simpa only [t, hUJcard, hWJcard] using
      hfrob.kernel_card_eq_one_add_orbits_mul_card
  refine ⟨t, ?_⟩
  calc
    Nat.card U - 1 = (1 + t * Nat.card W₁) - 1 :=
      congrArg (fun n : ℕ ↦ n - 1) hcard
    _ = t * Nat.card W₁ :=
      Nat.add_sub_cancel_left 1 (t * Nat.card W₁)
    _ = Nat.card W₁ * t := Nat.mul_comm _ _

private theorem supportBridges_coreSupport_subset_dadeSupport
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    FTtypePBridgeCoreSupport S W W₁ W₂ ⊆
      FTtypePBridgeDadeSupport S := by
  intro z hz
  change (z : G) ∈ FTsupport0 S
  rw [FTtypeP_supp0_def defW ctx.maxS ctx.StypeP]
  change (z : G) ∈
      subgroupNonidentity (Fitting_core S) ∪
        classSupportWithin S (cyclicTISet W W₁ W₂) at hz
  rcases hz with hzF | hzV
  · exact Or.inl (Fcore_sub_FTsupp ctx.maxS hzF)
  · exact Or.inr hzV

private theorem supportBridges_bridge_dadeSupport_of_coreSupport
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hcore : FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn
        (FTtypePBridgeCoreSupport S W W₁ W₂)) :
    FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn (FTtypePBridgeDadeSupport S) := by
  rw [ClassFunction.mem_supportedOn_iff] at hcore ⊢
  intro z hzDade
  apply hcore z
  intro hzCore
  exact hzDade (supportBridges_coreSupport_subset_dadeSupport ctx hzCore)

private theorem supportBridges_bridge_coreSupport_of_zero_branches
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (j : IrreducibleCharacter W₂ ℂ)
    (hj : j ≠ IrreducibleCharacter.trivial)
    (hderived : ∀ z : S,
      (z : G) ∈ derivedWithin S →
      z ∉ FTtypePBridgeCoreSupport S W W₁ W₂ →
      FTtypeP_bridge ctx j z = 0)
    (houtside : ∀ z : S,
      (z : G) ∉ derivedWithin S →
      z ∉ FTtypePBridgeCoreSupport S W W₁ W₂ →
      FTtypeP_bridge ctx j z = 0) :
    FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn
        (FTtypePBridgeCoreSupport S W W₁ W₂) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro z hzCore
  by_cases hzD : (z : G) ∈ derivedWithin S
  · exact hderived z hzD hzCore
  · exact houtside z hzD hzCore

private theorem supportBridges_support_clauses_of_coreSupport
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hcore : ∀ j, j ≠ IrreducibleCharacter.trivial →
      FTtypeP_bridge ctx j ∈
        ClassFunction.supportedOn
          (FTtypePBridgeCoreSupport S W W₁ W₂)) :
    ((∀ j, j ≠ IrreducibleCharacter.trivial →
        FTtypeP_bridge ctx j ∈
          ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) ∧
      ∀ j, j ≠ IrreducibleCharacter.trivial →
        FTtypeP_bridge ctx j ∈
          ClassFunction.supportedOn
            (FTtypePBridgeCoreSupport S W W₁ W₂)) := by
  refine ⟨?_, hcore⟩
  intro j hj
  exact supportBridges_bridge_dadeSupport_of_coreSupport ctx j
    (hcore j hj)

private theorem supportBridges_support_clauses_of_zero_branches
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hderived : ∀ (j : IrreducibleCharacter W₂ ℂ),
      j ≠ IrreducibleCharacter.trivial → ∀ z : S,
        (z : G) ∈ derivedWithin S →
        z ∉ FTtypePBridgeCoreSupport S W W₁ W₂ →
        FTtypeP_bridge ctx j z = 0)
    (houtside : ∀ (j : IrreducibleCharacter W₂ ℂ),
      j ≠ IrreducibleCharacter.trivial → ∀ z : S,
        (z : G) ∉ derivedWithin S →
        z ∉ FTtypePBridgeCoreSupport S W W₁ W₂ →
        FTtypeP_bridge ctx j z = 0) :
    ((∀ j, j ≠ IrreducibleCharacter.trivial →
        FTtypeP_bridge ctx j ∈
          ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) ∧
      ∀ j, j ≠ IrreducibleCharacter.trivial →
        FTtypeP_bridge ctx j ∈
          ClassFunction.supportedOn
            (FTtypePBridgeCoreSupport S W W₁ W₂)) := by
  apply supportBridges_support_clauses_of_coreSupport ctx
  intro j hj
  exact supportBridges_bridge_coreSupport_of_zero_branches
    ctx j hj (hderived j hj) (houtside j hj)

private theorem supportBridges_assemble
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (hsupport :
      ((∀ j, j ≠ IrreducibleCharacter.trivial →
          FTtypeP_bridge ctx j ∈
            ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) ∧
        ∀ j, j ≠ IrreducibleCharacter.trivial →
          FTtypeP_bridge ctx j ∈
            ClassFunction.supportedOn
              (FTtypePBridgeCoreSupport S W W₁ W₂)))
    (hnorm :
      ∀ j, j ≠ IrreducibleCharacter.trivial →
        characterPairing (FTtypeP_bridge ctx j)
            (FTtypeP_bridge ctx j) =
          ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ))) :
    ((∀ j, j ≠ IrreducibleCharacter.trivial →
        FTtypeP_bridge ctx j ∈
          ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) ∧
      ∀ j, j ≠ IrreducibleCharacter.trivial →
        FTtypeP_bridge ctx j ∈
          ClassFunction.supportedOn
            (FTtypePBridgeCoreSupport S W W₁ W₂)) ∧
    (∀ j, j ≠ IrreducibleCharacter.trivial →
      characterPairing (FTtypeP_bridge ctx j)
          (FTtypeP_bridge ctx j) =
        ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ))) ∧
    ((∀ j, j ≠ IrreducibleCharacter.trivial →
        ctx.tau (FTtypeP_bridge ctx j) - 1 +
            ctx.eta IrreducibleCharacter.trivial j =
          FTtypeP_bridge_gap ctx) ∧
      characterPairing (FTtypeP_bridge_gap ctx) 1 = 0 ∧
      cfReal (FTtypeP_bridge_gap ctx)) ∧
    (∀ X Y : ClassFunction G ℂ,
      FTtypeP_bridge_gap ctx = X + Y →
      starCharacterPairing X Y = 0 →
      (∀ Z ∈
          (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)),
        starCharacterPairing Y Z = 0) →
      classFunctionNormSq Y ≤
        ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ))) ∧
    Nat.card W₁ ∣ Nat.card U - 1 := by
  have hA :
      FTtypeP_bridge ctx (FTtypePBridgeIndex ctx) ∈
        ClassFunction.supportedOn (FTtypePBridgeDadeSupport S) :=
    hsupport.1 (FTtypePBridgeIndex ctx)
      (FTtypePBridgeIndex_ne_trivial ctx)
  have hgap := supportBridges_gap_constant ctx
  have hgapOne := supportBridges_gap_one_orthogonal ctx hA
  have hgapReal := supportBridges_gap_real ctx hA
  have hgapVirtual := supportBridges_gap_isVirtual ctx hA
  have htauNorm := supportBridges_tau_bridge_normSq ctx
    (FTtypePBridgeIndex ctx) hA
    (hnorm (FTtypePBridgeIndex ctx)
      (FTtypePBridgeIndex_ne_trivial ctx))
  have hnormClause := supportBridges_corrected_norm_clause ctx
    htauNorm hgapOne hgapReal hgapVirtual
  exact ⟨hsupport, hnorm, ⟨hgap, hgapOne, hgapReal⟩,
    hnormClause, supportBridges_q_dvd_cardU_pred ctx⟩

/-! ## Peterfalvi (13.18) -/

/-- `PFsection13.v: FTtypeP_bridge_facts`, Peterfalvi (13.18). -/
theorem FTtypeP_bridge_facts
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ((∀ j, j ≠ IrreducibleCharacter.trivial →
        FTtypeP_bridge ctx j ∈
          ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) ∧
      ∀ j, j ≠ IrreducibleCharacter.trivial →
        FTtypeP_bridge ctx j ∈
          ClassFunction.supportedOn
            (FTtypePBridgeCoreSupport S W W₁ W₂)) ∧
    (∀ j, j ≠ IrreducibleCharacter.trivial →
      characterPairing (FTtypeP_bridge ctx j)
          (FTtypeP_bridge ctx j) =
        ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ))) ∧
    ((∀ j, j ≠ IrreducibleCharacter.trivial →
        ctx.tau (FTtypeP_bridge ctx j) - 1 +
            ctx.eta IrreducibleCharacter.trivial j =
          FTtypeP_bridge_gap ctx) ∧
      characterPairing (FTtypeP_bridge_gap ctx) 1 = 0 ∧
      cfReal (FTtypeP_bridge_gap ctx)) ∧
    (∀ X Y : ClassFunction G ℂ,
      FTtypeP_bridge_gap ctx = X + Y →
      starCharacterPairing X Y = 0 →
      (∀ Z ∈
          (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)),
        starCharacterPairing Y Z = 0) →
      classFunctionNormSq Y ≤
        ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ))) ∧
    Nat.card W₁ ∣ Nat.card U - 1 := by
  have hsupport := supportBridges_support_clauses_of_zero_branches ctx
    (fun j hj ↦ supportBridges_bridge_zero_of_mem_derived ctx j hj)
    (fun j hj ↦ supportBridges_bridge_zero_of_not_mem_derived ctx j hj)
  have hnorm : ∀ j, j ≠ IrreducibleCharacter.trivial →
      characterPairing (FTtypeP_bridge ctx j) (FTtypeP_bridge ctx j) =
        ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ)) := by
    intro j hj
    exact supportBridges_bridge_norm_of_gamma_norm ctx j hj
      (supportBridges_typePGamma_norm ctx)
  exact supportBridges_assemble ctx hsupport hnorm

/-! ## Type-I Frobenius coherence -/

private theorem FTtype1_coherentWith_fittingDade
    {L : Subgroup G}
    (ctx : FTFrobeniusContext L)
    {nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hcoh : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) ctx.tau nu) :
    coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L ctx.maxL) nu := by
  refine
    { isometry := hcoh.isometry
      mapsToVirtual := hcoh.mapsToVirtual
      agrees := ?_ }
  intro phi hphi hoff
  have hcoreSupport :
      phi ∈ ClassFunction.supportedOn (FTType1FittingIn L : Set L) := by
    have hclosure : ∀ {psi : ClassFunction L ℂ},
        psi ∈ AddSubgroup.closure
            (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)) →
          psi ∈ ClassFunction.supportedOn
            (FTType1FittingIn L : Set L) := by
      intro psi hpsi
      induction hpsi using AddSubgroup.closure_induction with
      | mem xi hxi => exact seqInd_on (FTType1FittingIn L) hxi
      | zero => exact Submodule.zero_mem _
      | add x y hx hy ihx ihy => exact Submodule.add_mem _ ihx ihy
      | neg x hx ihx => exact Submodule.neg_mem _ ihx
    exact hclosure hphi
  have hsharpSupport : phi ∈ ClassFunction.supportedOn
      {x : L | (x : G) ∈ subgroupNonidentity (Fitting_core L)} := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    by_cases hxF : x ∈ FTType1FittingIn L
    · apply ClassFunction.eq_zero_of_mem_supportedOn hoff
      intro hxne
      have hxneG : (x : G) ≠ 1 := by
        intro hxOne
        apply hxne
        exact Subtype.ext hxOne
      exact hx ⟨hxF, hxneG⟩
    · exact ClassFunction.eq_zero_of_mem_supportedOn hcoreSupport hxF
  have hfullSupport : phi ∈ ClassFunction.supportedOn
      {x : L | (x : G) ∈ FTsupport L} := by
    rw [ClassFunction.mem_supportedOn_iff] at hsharpSupport ⊢
    intro x hx
    apply hsharpSupport
    intro hxSharp
    exact hx (Fcore_sub_FTsupp ctx.maxL hxSharp)
  calc
    nu phi = ctx.tau phi := hcoh.agrees phi hphi hoff
    _ = FTtype1Dade L ctx.maxL phi := by
      simp only [FTFrobeniusContext.tau, FTtype1Dade,
        LinearMap.comp_apply]
      rw [FT_DadeE L ctx.maxL phi hfullSupport,
        FT_DadeF_E L ctx.maxL phi hsharpSupport]

/-- The canonical Fitting-support Dade map is coherent on the type-I
sequential-induction family. -/
theorem FTtype1_coherence
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1) :
    coherent
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) := by
  let fctx : FTFrobeniusContext L :=
    { maxL := maxL
      frobenius := FTtype1_Frobenius L maxL Ltype1 }
  obtain ⟨nu, hnu⟩ := (FT_Frobenius_coherence fctx).coherent_family
  exact ⟨nu, FTtype1_coherentWith_fittingDade fctx hnu⟩

/-- The type-I sequentially induced characters are irreducible. -/
theorem FTtype1_Ind_irr
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1) :
    ∀ phi ∈ FTType1SeqIndFamily L,
      IsIrreducibleCharacter L ℂ phi := by
  let fctx : FTFrobeniusContext L :=
    ⟨maxL, FTtype1_Frobenius L maxL Ltype1⟩
  exact (FT_Frobenius_coherence fctx).seqInd_irreducible

/-! ## Peterfalvi (13.19) -/

/-! ## Transport between the ambient group and its top subgroup -/

private noncomputable def typeIBridgeSourceMap :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

private noncomputable def typeIBridgeTargetMap :
    ClassFunction (⊤ : Subgroup G) ℂ →ₗ[ℂ] ClassFunction G ℂ :=
  ClassFunction.comap Subgroup.topEquiv.symm.toMonoidHom

@[simp] private theorem typeIBridgeSource_target
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    typeIBridgeSourceMap (typeIBridgeTargetMap phi) = phi := by
  ext x
  simpa [typeIBridgeSourceMap, typeIBridgeTargetMap,
    ClassFunction.comap_apply] using
      congrArg phi (Subgroup.topEquiv.symm_apply_apply x)

@[simp] private theorem typeIBridgeTarget_source
    (phi : ClassFunction G ℂ) :
    typeIBridgeTargetMap (typeIBridgeSourceMap phi) = phi := by
  ext x
  simpa [typeIBridgeSourceMap, typeIBridgeTargetMap,
    ClassFunction.comap_apply] using
      congrArg phi (Subgroup.topEquiv.apply_symm_apply x)

private theorem typeIBridgeTarget_pairing
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (typeIBridgeTargetMap phi)
        (typeIBridgeTargetMap psi) = characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [typeIBridgeTargetMap, ClassFunction.comap_apply]

private theorem typeIBridgeSource_pairing
    (phi psi : ClassFunction G ℂ) :
    characterPairing (typeIBridgeSourceMap phi)
        (typeIBridgeSourceMap psi) = characterPairing phi psi := by
  rw [← typeIBridgeTarget_pairing
    (typeIBridgeSourceMap phi) (typeIBridgeSourceMap psi)]
  simp

private theorem typeIBridgeTarget_virtual
    {phi : ClassFunction (⊤ : Subgroup G) ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (typeIBridgeTargetMap phi) := by
  obtain ⟨z, hz⟩ := hphi
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.symm.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]
  rfl

private theorem typeIBridgeSource_virtual
    {phi : ClassFunction G ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (typeIBridgeSourceMap phi) := by
  obtain ⟨z, hz⟩ := hphi
  refine ⟨VirtualCharacter.comap Subgroup.topEquiv.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]
  rfl

private theorem typeIBridgeCoherenceTop
    {L : Subgroup G}
    {tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {maxL : L ∈ minSimple_max_groups (G := G)}
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁) :
    coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade (FT_DadeF_hyp L maxL))
      (typeIBridgeSourceMap.comp tau₁) := by
  refine
    { isometry := ?_
      mapsToVirtual := ?_
      agrees := ?_ }
  · intro xi hxi mu hmu
    simpa [LinearMap.comp_apply] using
      (typeIBridgeSource_pairing (tau₁ xi) (tau₁ mu)).trans
        (cohL.isometry xi hxi mu hmu)
  · intro xi hxi
    exact typeIBridgeSource_virtual (cohL.mapsToVirtual xi hxi)
  · intro xi hxi hxiOn
    change typeIBridgeSourceMap (tau₁ xi) =
      Dade (FT_DadeF_hyp L maxL) xi
    rw [cohL.agrees xi hxi hxiOn]
    change typeIBridgeSourceMap
      (typeIBridgeTargetMap (Dade (FT_DadeF_hyp L maxL) xi)) = _
    exact typeIBridgeSource_target _

private theorem typeIBridgeRightFactor_mem_zpowers
    {r x : G} (hcomm : Commute r x)
    (hcop : (orderOf r).Coprime (orderOf x)) :
    x ∈ Subgroup.zpowers (r * x) := by
  let e₀ := Nat.chineseRemainder hcop 0 1
  let e : ℕ := e₀
  have her : e ≡ 0 [MOD orderOf r] := e₀.property.1
  have hex : e ≡ 1 [MOD orderOf x] := e₀.property.2
  have hrpow : r ^ e = 1 := pow_eq_one_iff_modEq.mpr her
  have hxpow : x ^ e = x := by
    simpa using (pow_eq_pow_iff_modEq.mpr hex : x ^ e = x ^ 1)
  have hpow : (r * x) ^ e = x := by
    rw [hcomm.mul_pow, hrpow, hxpow, one_mul]
  have hmem : (r * x) ^ e ∈ Subgroup.zpowers (r * x) :=
    Subgroup.npow_mem_zpowers (r * x) e
  exact Eq.mp
    (congrArg (fun y : G ↦ y ∈ Subgroup.zpowers (r * x)) hpow)
    hmem

private theorem typeIBridgeDadeSupport_invStable
    {L H : Subgroup G}
    (ddA : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity H)) :
    IsInvStable (Dade_support ddA) := by
  have hinv : ∀ x : G,
      x ∈ Dade_support ddA → x⁻¹ ∈ Dade_support ddA := by
    intro x
    rintro ⟨a, haA, z, hz, g, hgG, hzx⟩
    rcases Set.mem_mul.mp hz with ⟨s, hs, b, hb, rfl⟩
    rw [Set.mem_singleton_iff] at hb
    subst b
    have hsa : Commute s a := by
      exact (Subgroup.mem_centralizer_iff.mp
        (Dade_signalizer_cent ddA a hs) a
          (Subgroup.mem_zpowers a)).symm
    have haInvA : a⁻¹ ∈ subgroupNonidentity H :=
      ⟨H.inv_mem haA.1, inv_ne_one.mpr haA.2⟩
    have hsignalizerInv :
        DadeSignalizer ddA a⁻¹ = DadeSignalizer ddA a := by
      simp [DadeSignalizer, Subgroup.zpowers_inv]
    refine ⟨a⁻¹, haInvA, s⁻¹ * a⁻¹, ?_, g, hgG, ?_⟩
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

/-! ## Coprimality and the first conclusion of (13.19) -/

private theorem typeIBridge_typeOneFitting_coprime_typeP
    {T V A B C : Subgroup G}
    {defC : IsInternalDirectProductIn A B C}
    (ctxT : FTTypePSetupContext T V C A B defC)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1) :
    Nat.Coprime (Nat.card (Fitting_core L))
      (Nat.card (Fitting_core T)) := by
  exact supportBridges_typeOneFitting_coprime_typeP13
    ctxT L maxL Ltype1

private theorem typeIBridge_typeOneFitting_coprime_P_and_W
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1) :
    Nat.Coprime (Nat.card (Fitting_core L))
        (Nat.card (Fitting_core S)) ∧
      Nat.Coprime (Nat.card (Fitting_core L)) (Nat.card W) := by
  have hcopP := typeIBridge_typeOneFitting_coprime_typeP
    ctx L maxL Ltype1
  obtain ⟨T, pairST, xdefW, V, TtypeP⟩ :=
    FTtypeP_pair_witness defW ctx.maxS ctx.StypeP
  let ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW :=
    ⟨pairST.T_maximal, TtypeP⟩
  have hcopPT := typeIBridge_typeOneFitting_coprime_typeP
    ctxT L maxL Ltype1
  have hcopW₂ : Nat.Coprime (Nat.card (Fitting_core L))
      (Nat.card W₂) :=
    hcopP.coprime_dvd_right
      (Subgroup.card_dvd_of_le ctx.StypeP.2.2.2.1.2.2.1)
  have hcopW₁ : Nat.Coprime (Nat.card (Fitting_core L))
      (Nat.card W₁) :=
    hcopPT.coprime_dvd_right
      (Subgroup.card_dvd_of_le ctxT.StypeP.2.2.2.1.2.2.1)
  have hcardW : Nat.card W₁ * Nat.card W₂ = Nat.card W := by
    simpa only [
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq defW.left_le,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq defW.right_le]
      using defW.complement.card_mul
  refine ⟨hcopP, ?_⟩
  rw [← hcardW]
  exact hcopW₁.mul_right hcopW₂

private theorem typeIBridge_order_coprime_of_mem_classSupport
    {L K : Subgroup G} {x : G}
    (hcop : Nat.Coprime (Nat.card (Fitting_core L)) (Nat.card K))
    (hx : x ∈ classSupportWithin (⊤ : Subgroup G) (K : Set G)) :
    Nat.Coprime (Nat.card (Fitting_core L)) (orderOf x) := by
  rcases hx with ⟨y, hyK, g, _hg, rfl⟩
  have hyOrder : orderOf y ∣ Nat.card K :=
    K.orderOf_dvd_natCard hyK
  have hconjOrder : orderOf (g⁻¹ * y * g) = orderOf y := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective y
  rw [hconjOrder]
  exact hcop.coprime_dvd_right hyOrder

private theorem typeIBridgeFullSupport_disjoint
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1) :
    Disjoint (FT_Dade_full_support L)
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G)) := by
  let fctx : FTFrobeniusContext L :=
    ⟨maxL, FTtype1_Frobenius L maxL Ltype1⟩
  obtain ⟨hcopP, hcopW⟩ :=
    typeIBridge_typeOneFitting_coprime_P_and_W
      ctx L maxL Ltype1
  rw [Set.disjoint_left]
  intro x hxD hxPW
  have hcopX : Nat.Coprime (Nat.card (Fitting_core L))
      (orderOf x) := by
    rcases hxPW with hxP | hxW
    · exact typeIBridge_order_coprime_of_mem_classSupport hcopP hxP
    · exact typeIBridge_order_coprime_of_mem_classSupport hcopW hxW
  rcases hxD with ⟨a, ha, za, hza, g, _hg, hconj⟩
  rcases Set.mem_mul.mp hza with ⟨r, hr, b, hb, hrb⟩
  have hbA : b = a := Set.mem_singleton_iff.mp hb
  subst b
  subst za
  have haCore : a ∈ subgroupNonidentity (Fitting_core L) := by
    rw [← FTsupp_Frobenius fctx]
    exact ha
  have hrDade : r ∈ DadeSignalizer (FT_Dade_hyp L maxL) a := by
    rw [def_FTsignalizer L maxL ha]
    exact hr
  have hcomm : Commute r a :=
    (Dade_signalizer_cent (FT_Dade_hyp L maxL)
      a hrDade a (Subgroup.mem_zpowers a)).symm
  have haCL : a ∈
      Submission.OddOrder.BG.Section14.elementCentralizerWithin L a := by
    refine ⟨Fcore_sub L haCore.1, ?_⟩
    intro z hz
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact ((Commute.refl a).zpow_left n).eq
  have hcopSignalizer :=
    Dade_coprime (FT_Dade_hyp L maxL) ha ha
  have hcopRA : (orderOf r).Coprime (orderOf a) :=
    (hcopSignalizer.coprime_dvd_left
      ((DadeSignalizer (FT_Dade_hyp L maxL) a).orderOf_dvd_natCard
        hrDade)).coprime_dvd_right
          ((Submission.OddOrder.BG.Section14.elementCentralizerWithin L a).orderOf_dvd_natCard
            haCL)
  have haPow : a ∈ Subgroup.zpowers (r * a) :=
    typeIBridgeRightFactor_mem_zpowers hcomm hcopRA
  have haOrderProd : orderOf a ∣ orderOf (r * a) := by
    simpa only [Nat.card_zpowers] using
      (Subgroup.zpowers (r * a)).orderOf_dvd_natCard haPow
  have hconjOrder :
      orderOf (g⁻¹ * (r * a) * g) = orderOf (r * a) := by
    simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] using
      orderOf_injective (MulAut.conj g⁻¹).toMonoidHom
        (MulAut.conj g⁻¹).injective (r * a)
  have hprodOrder : orderOf (r * a) = orderOf x := by
    calc
      orderOf (r * a) = orderOf (g⁻¹ * (r * a) * g) :=
        hconjOrder.symm
      _ = orderOf x := congrArg orderOf hconj
  have haOrderX : orderOf a ∣ orderOf x := by
    rw [← hprodOrder]
    exact haOrderProd
  have haOrderCore : orderOf a ∣ Nat.card (Fitting_core L) :=
    (Fitting_core L).orderOf_dvd_natCard haCore.1
  have haOrderOne : orderOf a = 1 :=
    Nat.eq_one_of_dvd_coprimes hcopX haOrderCore haOrderX
  exact haCore.2 (orderOf_eq_one_iff.mp haOrderOne)

private theorem typeIBridge_exists_signed_irreducible
    {Q : Type} [Group Q] [Fintype Q]
    {f : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f)
    (hnorm : characterPairing f f = 1) :
    ∃ (chi : IrreducibleCharacter Q ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        f = (epsilon : ℂ) • (chi : ClassFunction Q ℂ) := by
  obtain ⟨z, hz⟩ := hf
  have hnormZ : normSq z = 1 := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self, hz, hnorm]
    norm_num
  obtain ⟨chi, epsilon, hepsilon, hsingle⟩ :=
    eq_signed_single_of_normSq_eq_one z hnormZ
  refine ⟨chi, epsilon, hepsilon, ?_⟩
  rw [← hz, hsingle, VirtualCharacter.realize_single]

private theorem typeIBridge_tau_orthogonal_cyclicCharacter
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1)
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁)
    (hdis : Disjoint (FT_Dade_full_support L)
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G)))
    (psi : ClassFunction L ℂ)
    (hpsi : psi ∈ FTType1SeqIndFamily L)
    (chi : IrreducibleCharacter W ℂ) :
    characterPairing (tau₁ psi)
      (ctx.targetMap (ctx.isoG.linearMap
        (chi : ClassFunction W ℂ))) = 0 := by
  classical
  obtain ⟨i, j, hchi⟩ :=
    IrreducibleCharacter.exists_cyclicTICharacter defW chi
  subst chi
  change characterPairing (tau₁ psi)
    (ctx.targetMap (ctx.isoG.cyclicTIImage (i, j))) = 0
  let H : Subgroup L := FTType1FittingIn L
  letI : H.Normal := by
    simpa only [H, FTType1FittingIn] using Fcore_normal L
  let dd : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity (Fitting_core L)) :=
    FT_DadeF_hyp L maxL
  let nuTop : ClassFunction L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    typeIBridgeSourceMap.comp tau₁
  have hcohTop : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade dd) nuTop := by
    simpa only [dd, nuTop] using typeIBridgeCoherenceTop cohL
  let psiIrr : IrreducibleCharacter L ℂ :=
    ⟨psi, FTtype1_Ind_irr L maxL Ltype1 psi hpsi⟩
  have hpsiInv : ClassFunction.inverseLinear psi ∈
      FTType1SeqIndFamily L := by
    simpa only [H, FTType1SeqIndFamily] using
      seqInd_inverse_mem (k := ℂ) H ⊤ ⊥ hpsi
  let d : ClassFunction L ℂ :=
    psi - ClassFunction.inverseLinear psi
  have hdSpan : d ∈ AddSubgroup.closure
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)) :=
    (AddSubgroup.closure _).sub_mem
      (AddSubgroup.subset_closure hpsi)
      (AddSubgroup.subset_closure hpsiInv)
  have hdOff : d ∈ ClassFunction.supportedOn (nonidentitySet L) :=
    FTType1InfrastructureInternal.inverseSubSupported psi
  have hagree : nuTop d = Dade dd d :=
    hcohTop.agrees d hdSpan hdOff
  let beta : ClassFunction (⊤ : Subgroup G) ℂ := Dade dd d
  let psiTop : ClassFunction (⊤ : Subgroup G) ℂ := nuTop psi
  let psiInvTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    nuTop (ClassFunction.inverseLinear psi)
  let etaTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    ctx.isoG.cyclicTIImage (i, j)
  have hsourceSelf : characterPairing psi psi = 1 := by
    simpa only [psiIrr] using psiIrr.characterPairing_self
  have hsourceCross : characterPairing psi
      (ClassFunction.inverseLinear psi) = 0 := by
    simpa only [H, FTType1SeqIndFamily] using
      seqInd_conjC_ortho (k := ℂ) H (mFT_odd L) ⊤ ⊥ hpsi
  have hsourceCross' : characterPairing
      (ClassFunction.inverseLinear psi) psi = 0 := by
    rw [FTType1InfrastructureInternal.pairingInverseLeft,
      hsourceCross]
  have hsourceInvSelf : characterPairing
      (ClassFunction.inverseLinear psi)
      (ClassFunction.inverseLinear psi) = 1 := by
    rw [FTType1InfrastructureInternal.pairingInverse, hsourceSelf]
  have hsourceNorm : characterPairing d d = (2 : ℂ) := by
    dsimp only [d]
    rw [FTType1InfrastructureInternal.pairingSubLeft,
      FTType1InfrastructureInternal.pairingSubRight,
      FTType1InfrastructureInternal.pairingSubRight,
      hsourceSelf, hsourceCross, hsourceCross', hsourceInvSelf]
    norm_num
  have hbetaVirtual : ClassFunction.IsVirtual beta := by
    rw [show beta = Dade dd d by rfl, ← hagree]
    exact hcohTop.mapsToVirtual d hdSpan
  have hbetaNorm : characterPairing beta beta = (2 : ℂ) := by
    rw [show beta = Dade dd d by rfl, ← hagree]
    exact (hcohTop.isometry d hdSpan d hdSpan).trans hsourceNorm
  obtain ⟨betaZ, hbetaZ⟩ := hbetaVirtual
  have hbetaZNorm : normSq betaZ = 2 := by
    apply Int.cast_injective (α := ℂ)
    rw [← VirtualCharacter.characterPairing_realize_self,
      hbetaZ, hbetaNorm]
    norm_num
  have hbetaZero : Set.EqOn
      (fun w : W ↦ beta
        ⟨w, ctx.primeDade.prDade_cycTI.le_group w.property⟩)
      0 (cyclicTISetInW W W₁ W₂) := by
    intro w hw
    let wTop : (⊤ : Subgroup G) :=
      ⟨w, ctx.primeDade.prDade_cycTI.le_group w.property⟩
    have hwClass : (w : G) ∈
        classSupportWithin (⊤ : Subgroup G) (W : Set G) :=
      ⟨(w : G), w.property, 1, Subgroup.mem_top 1, by simp⟩
    have hwNotFull : (w : G) ∉ FT_Dade_full_support L := by
      intro hwFull
      exact Set.disjoint_left.mp hdis hwFull (Or.inr hwClass)
    have hwNotDade : (w : G) ∉ Dade_support dd := by
      intro hwDade
      apply hwNotFull
      have hwF : (w : G) ∈ FT_Dade_support L
          (subgroupNonidentity (Fitting_core L)) := by
        simpa only [dd, FT_DadeF_supportE L maxL] using hwDade
      exact FT_Dade_supportS L (Fcore_sub_FTsupp maxL) hwF
    change beta wTop = (0 : W → ℂ) w
    simp only [Pi.zero_apply]
    exact ClassFunction.eq_zero_of_mem_supportedOn
      (Dade_cfunS dd d) hwNotDade
  have hNCle : ctx.isoG.cyclicTINC beta ≤ 2 := by
    have hle := ctx.isoG.cyclicTINC_realize_le_normSq betaZ
    rw [hbetaZ, hbetaZNorm] at hle
    exact_mod_cast hle
  letI : IsCyclic W₁ := ctx.primeTI.complement_cyclic
  letI : IsCyclic W₂ := ctx.primeTI.fixed_cyclic
  have hcard₁ : Fintype.card (IrreducibleCharacter W₁ ℂ) =
      Nat.card W₁ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hcard₂ : Fintype.card (IrreducibleCharacter W₂ ℂ) =
      Nat.card W₂ :=
    IrreducibleCharacter.card_eq_natCard_of_isCyclic
  have hminGt : 2 < min
      (Fintype.card (IrreducibleCharacter W₁ ℂ))
      (Fintype.card (IrreducibleCharacter W₂ ℂ)) := by
    rw [hcard₁, hcard₂]
    exact lt_min ctx.primeDade.prDade_cycTI.two_lt_card_left
      ctx.primeDade.prDade_cycTI.two_lt_card_right
  have hNCzero : ctx.isoG.cyclicTINC beta = 0 := by
    by_contra hne
    have hpos : 0 < ctx.isoG.cyclicTINC beta := Nat.pos_of_ne_zero hne
    have hsmall : ctx.isoG.cyclicTINC beta <
        2 * min
          (Fintype.card (IrreducibleCharacter W₁ ℂ))
          (Fintype.card (IrreducibleCharacter W₂ ℂ)) := by
      omega
    have hminLe := ctx.isoG.cyclicTINC_min_le
      beta hbetaZero hpos hsmall
    omega
  have hbetaEta : characterPairing beta etaTop = 0 := by
    by_contra hpair
    have hmem : (i, j) ∈
        ctx.isoG.cyclicTICoefficientSupport beta :=
      (ctx.isoG.mem_cyclicTICoefficientSupport beta (i, j)).2
        (by simpa only [etaTop] using hpair)
    have hpos : 0 < ctx.isoG.cyclicTINC beta :=
      Finset.card_pos.mpr ⟨(i, j), hmem⟩
    omega
  have hpsiTopVirtual : ClassFunction.IsVirtual psiTop :=
    hcohTop.mapsToVirtual psi (AddSubgroup.subset_closure hpsi)
  have hpsiInvTopVirtual : ClassFunction.IsVirtual psiInvTop :=
    hcohTop.mapsToVirtual (ClassFunction.inverseLinear psi)
      (AddSubgroup.subset_closure hpsiInv)
  have hpsiTopNorm : characterPairing psiTop psiTop = 1 := by
    exact (hcohTop.isometry psi (AddSubgroup.subset_closure hpsi)
      psi (AddSubgroup.subset_closure hpsi)).trans hsourceSelf
  obtain ⟨alpha, epsilon, hepsilon, hpsiTop⟩ :=
    typeIBridge_exists_signed_irreducible
      hpsiTopVirtual hpsiTopNorm
  obtain ⟨theta, delta, hdelta, himage⟩ :=
    ctx.isoG.cyclicTIImage_eq_signed_irreducible (i, j)
  have hetaTopSigned :
      etaTop = (delta : ℂ) •
        (theta : ClassFunction (⊤ : Subgroup G) ℂ) := by
    simpa only [etaTop] using himage
  have htargetPsi : typeIBridgeTargetMap psiTop = tau₁ psi := by
    dsimp only [psiTop, nuTop, LinearMap.comp_apply]
    exact typeIBridgeTarget_source (tau₁ psi)
  have htargetEta :
      ctx.targetMap (ctx.isoG.cyclicTIImage (i, j)) =
        typeIBridgeTargetMap etaTop := by
    rfl
  have hpairTransport :
      characterPairing (tau₁ psi)
          (ctx.targetMap (ctx.isoG.cyclicTIImage (i, j))) =
        characterPairing psiTop etaTop := by
    rw [htargetEta, ← htargetPsi]
    exact typeIBridgeTarget_pairing psiTop etaTop
  by_contra hpairAmbient
  have hpairTop : characterPairing psiTop etaTop ≠ 0 := by
    intro hzero
    exact hpairAmbient (hpairTransport.trans hzero)
  have halphaTheta : alpha = theta := by
    by_contra hne
    apply hpairTop
    rw [hpsiTop, hetaTopSigned, characterPairing_smul_left,
      characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_eq_zero hne]
    simp
  have hpsiInvTop_psiTop :
      characterPairing psiInvTop psiTop = 0 := by
    rw [hcohTop.isometry
      (ClassFunction.inverseLinear psi)
        (AddSubgroup.subset_closure hpsiInv)
      psi (AddSubgroup.subset_closure hpsi), hsourceCross']
  have hpsiInvTop_alpha :
      characterPairing psiInvTop
        (alpha : ClassFunction (⊤ : Subgroup G) ℂ) = 0 := by
    rw [hpsiTop, characterPairing_smul_right] at hpsiInvTop_psiTop
    exact (mul_eq_zero.mp hpsiInvTop_psiTop).resolve_left
      (Int.cast_ne_zero.mpr (isSign_ne_zero hepsilon))
  have hpsiInvTop_eta : characterPairing psiInvTop etaTop = 0 := by
    rw [hetaTopSigned, ← halphaTheta, characterPairing_smul_right,
      hpsiInvTop_alpha, mul_zero]
  have hbetaEq : beta = psiTop - psiInvTop := by
    rw [show beta = Dade dd d by rfl, ← hagree]
    simp only [d, psiTop, psiInvTop, nuTop, map_sub,
      LinearMap.comp_apply]
  have hbetaEtaNe : characterPairing beta etaTop ≠ 0 := by
    rw [hbetaEq, FTType1InfrastructureInternal.pairingSubLeft,
      hpsiInvTop_eta, sub_zero]
    exact hpairTop
  exact hbetaEtaNe hbetaEta
private theorem typeIBridge_orthogonalFamilies
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1)
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁)
    (hdis : Disjoint (FT_Dade_full_support L)
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G))) :
    orthogonalFamilies
      (tau₁ ''
        (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)))
      (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)) := by
  rintro _ ⟨psi, hpsi, rfl⟩ _ heta
  rw [Finset.mem_coe] at heta
  rcases Finset.mem_image.mp heta with ⟨chiCF, hchiCF, rfl⟩
  rcases Finset.mem_image.mp hchiCF with ⟨chi, _hchi, rfl⟩
  exact typeIBridge_tau_orthogonal_cyclicCharacter
    ctx L maxL Ltype1 tau₁ cohL hdis psi hpsi chi

/-! Paste-ready prefix of `FTtypeI_bridge_facts`. -/

private theorem typeIBridge_first_two_facts
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1)
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁) :
    Disjoint (FT_Dade_full_support L)
        (classSupportWithin (⊤ : Subgroup G)
            (Fitting_core S : Set G) ∪
          classSupportWithin (⊤ : Subgroup G) (W : Set G)) ∧
      orthogonalFamilies
        (tau₁ ''
          (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)))
        (↑(FTtypePCyclicImageFamily ctx) :
          Set (ClassFunction G ℂ)) := by
  have hdis := typeIBridgeFullSupport_disjoint
    ctx L maxL Ltype1
  exact ⟨hdis, typeIBridge_orthogonalFamilies
    ctx L maxL Ltype1 tau₁ cohL hdis⟩

/-! ## Corrected constant-eta chain -/

/-! Induction takes source support to its ambient conjugacy saturation. -/

private theorem typeIConstantEta_induce_mem_ambientClassSupport
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
    exact ⟨(y⁻¹ * x * y : G), ha, y⁻¹,
      Subgroup.mem_top _, by group⟩
  · rfl

/-! Saturating the bridge's source core support lands in the `P ∪ W`
ambient support used by the Type-I/Type-P disjointness clause. -/

private theorem typeIConstantEta_bridgeCore_saturates_into_PW :
    classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity (Fitting_core S) ∪
          classSupportWithin S (cyclicTISet W W₁ W₂)) ⊆
      classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G) := by
  rintro x ⟨y, hy, g, _hg, rfl⟩
  rcases hy with hyP | hyW
  · exact Or.inl ⟨y, hyP.1, g, Subgroup.mem_top _, rfl⟩
  · rcases hyW with ⟨w, hw, s, _hsS, rfl⟩
    exact Or.inr ⟨w, cyclicTISet_subset W W₁ W₂ hw,
      s * g, Subgroup.mem_top _, by group⟩

/-! The ambient `P ∪ W` support is inverse-stable.  Using stability on the
right is important: it avoids the mismatched attempt to use inverse-stability
of the smaller Fitting-Dade support as if it were the full Type-I support. -/

private theorem typeIBridge_one_eq_trivial
    {Q : Type*} [Group Q] [Fintype Q] :
    (1 : ClassFunction Q ℂ) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
        ClassFunction Q ℂ) := by
  apply ClassFunction.ext
  intro x
  rw [ftTypePSupportBridgesOne_apply,
    IrreducibleCharacter.trivial_apply]

private theorem typeIBridge_inverse_one
    {Q : Type*} [Group Q] [Fintype Q] :
    ClassFunction.inverseLinear (1 : ClassFunction Q ℂ) = 1 := by
  apply ClassFunction.ext
  intro x
  simp only [ClassFunction.inverseLinear_apply,
    ftTypePSupportBridgesOne_apply]

private theorem typeIBridgeTarget_trivial :
    typeIBridgeTargetMap
        (((IrreducibleCharacter.trivial :
            IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
          ClassFunction (⊤ : Subgroup G) ℂ)) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) := by
  apply ClassFunction.ext
  intro x
  simp only [typeIBridgeTargetMap, ClassFunction.comap_apply,
    IrreducibleCharacter.trivial_apply]

private theorem typeIConstantEta_PW_invStable :
    IsInvStable
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G)) := by
  have hinvClass : ∀ (K : Subgroup G) (x : G),
      x ∈ classSupportWithin (⊤ : Subgroup G) (K : Set G) →
        x⁻¹ ∈ classSupportWithin (⊤ : Subgroup G) (K : Set G) := by
    intro K x
    rintro ⟨a, ha, g, hg, hax⟩
    refine ⟨a⁻¹, K.inv_mem ha, g, hg, ?_⟩
    change g⁻¹ * a⁻¹ * g = x⁻¹
    calc
      g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
      _ = x⁻¹ := congrArg Inv.inv hax
  have hinv : ∀ x : G,
      x ∈
          classSupportWithin (⊤ : Subgroup G)
              (Fitting_core S : Set G) ∪
            classSupportWithin (⊤ : Subgroup G) (W : Set G) →
        x⁻¹ ∈
          classSupportWithin (⊤ : Subgroup G)
              (Fitting_core S : Set G) ∪
            classSupportWithin (⊤ : Subgroup G) (W : Set G) := by
    intro x hx
    rcases hx with hxP | hxW
    · exact Or.inl (hinvClass (Fitting_core S) x hxP)
    · exact Or.inr (hinvClass W x hxW)
  intro x
  constructor
  · intro hx
    simpa only [inv_inv] using hinv x⁻¹ hx
  · exact hinv x

/-! Coq `o_tauL_S`: a Type-I Fitting-Dade image is orthogonal to every
transported nontrivial Type-P bridge. -/

private theorem typeIConstantEta_tauL_bridge_orthogonal
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (hdis : Disjoint (FT_Dade_full_support L)
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G)))
    (zeta : ClassFunction L ℂ)
    (j : IrreducibleCharacter W₂ ℂ)
    (hA : FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn (FTtypePBridgeDadeSupport S))
    (hcore : FTtypeP_bridge ctx j ∈
      ClassFunction.supportedOn
        (FTtypePBridgeCoreSupport S W W₁ W₂)) :
    characterPairing (FTtype1Dade L maxL zeta)
        (ctx.tau (FTtypeP_bridge ctx j)) = 0 := by
  have htauEq : ctx.tau (FTtypeP_bridge ctx j) =
      ClassFunction.induce S (FTtypeP_bridge ctx j) := by
    exact (FTtypeP_facts ctx).2.2.2.2.2.2.2.2.2
      (FTtypeP_bridge ctx j)
      (by simpa only [ftTypePSupport0InS,
        FTtypePBridgeDadeSupport, subgroupPullbackSet] using hA)
  have htauSupport : ctx.tau (FTtypeP_bridge ctx j) ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity (Fitting_core S) ∪
            classSupportWithin S (cyclicTISet W W₁ W₂))) := by
    rw [htauEq]
    apply typeIConstantEta_induce_mem_ambientClassSupport
    simpa only [FTtypePBridgeCoreSupport, subgroupPullbackSet] using hcore
  have htauPW : ctx.tau (FTtypeP_bridge ctx j) ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G)
            (Fitting_core S : Set G) ∪
          classSupportWithin (⊤ : Subgroup G) (W : Set G)) := by
    rw [ClassFunction.mem_supportedOn_iff] at htauSupport ⊢
    intro x hx
    apply htauSupport
    intro hxSmall
    exact hx (typeIConstantEta_bridgeCore_saturates_into_PW hxSmall)
  have hzetaSupport : FTtype1Dade L maxL zeta ∈
      ClassFunction.supportedOn (FT_Dade_full_support L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    change Dade (FT_DadeF_hyp L maxL) zeta
      (Subgroup.topEquiv.symm x) = 0
    apply ClassFunction.eq_zero_of_mem_supportedOn
      (Dade_cfunS (FT_DadeF_hyp L maxL) zeta)
    intro hxD
    apply hx
    have hxFTop : (Subgroup.topEquiv.symm x : G) ∈
        FT_Dade_support L
          (subgroupNonidentity (Fitting_core L)) := by
      rw [← FT_DadeF_supportE L maxL]
      exact hxD
    have hxFullTop : (Subgroup.topEquiv.symm x : G) ∈
        FT_Dade_full_support L :=
      FT_Dade_supportS L (Fcore_sub_FTsupp maxL) hxFTop
    have hcoe : (Subgroup.topEquiv.symm x : G) = x :=
      Subgroup.topEquiv.apply_symm_apply x
    exact hcoe ▸ hxFullTop
  apply characterPairing_eq_zero_of_disjoint_of_invStable_right hdis
  · exact typeIConstantEta_PW_invStable
  · exact hzetaSupport
  · exact htauPW

private theorem typeIConstantEta_fragment
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (phi : ClassFunction L ℂ)
    (hdis : Disjoint (FT_Dade_full_support L)
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G)))
    (hbridgeFacts :
      ((∀ j, j ≠ IrreducibleCharacter.trivial →
          FTtypeP_bridge ctx j ∈
            ClassFunction.supportedOn (FTtypePBridgeDadeSupport S)) ∧
        ∀ j, j ≠ IrreducibleCharacter.trivial →
          FTtypeP_bridge ctx j ∈
            ClassFunction.supportedOn
              (FTtypePBridgeCoreSupport S W W₁ W₂)) ∧
      (∀ j, j ≠ IrreducibleCharacter.trivial →
        characterPairing (FTtypeP_bridge ctx j)
            (FTtypeP_bridge ctx j) =
          ((((Nat.card U - 1) / Nat.card W₁ + 2 : ℕ) : ℂ))) ∧
      ((∀ j, j ≠ IrreducibleCharacter.trivial →
          ctx.tau (FTtypeP_bridge ctx j) - 1 +
              ctx.eta IrreducibleCharacter.trivial j =
            FTtypeP_bridge_gap ctx) ∧
        characterPairing (FTtypeP_bridge_gap ctx) 1 = 0 ∧
        cfReal (FTtypeP_bridge_gap ctx)) ∧
      (∀ X Y : ClassFunction G ℂ,
        FTtypeP_bridge_gap ctx = X + Y →
        starCharacterPairing X Y = 0 →
        (∀ Z ∈
            (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)),
          starCharacterPairing Y Z = 0) →
        classFunctionNormSq Y ≤
          ((((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ))) ∧
      Nat.card W₁ ∣ Nat.card U - 1) :
    ∀ j, j ≠ IrreducibleCharacter.trivial →
      characterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial j) =
        characterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial
            (FTtypePBridgeIndex ctx)) := by
  obtain ⟨⟨hA, hcore⟩, _hnorm,
    ⟨hgap, _hgapOne, _hgapReal⟩, _hub, _hdvd⟩ := hbridgeFacts
  intro j hj
  let j₀ : IrreducibleCharacter W₂ ℂ := FTtypePBridgeIndex ctx
  have hj₀ : j₀ ≠ IrreducibleCharacter.trivial :=
    FTtypePBridgeIndex_ne_trivial ctx
  have hjEq := hgap j hj
  have hj₀Eq := hgap j₀ hj₀
  have hEq :
      ctx.tau (FTtypeP_bridge ctx j) - 1 +
          ctx.eta IrreducibleCharacter.trivial j =
        ctx.tau (FTtypeP_bridge ctx j₀) - 1 +
          ctx.eta IrreducibleCharacter.trivial j₀ :=
    hjEq.trans hj₀Eq.symm
  have hetaDiff :
      ctx.eta IrreducibleCharacter.trivial j -
          ctx.eta IrreducibleCharacter.trivial j₀ =
        -(ctx.tau (FTtypeP_bridge ctx j) -
          ctx.tau (FTtypeP_bridge ctx j₀)) := by
    calc
      ctx.eta IrreducibleCharacter.trivial j -
            ctx.eta IrreducibleCharacter.trivial j₀ =
          (ctx.tau (FTtypeP_bridge ctx j) - 1 +
              ctx.eta IrreducibleCharacter.trivial j) -
            (ctx.tau (FTtypeP_bridge ctx j) - 1) -
              ctx.eta IrreducibleCharacter.trivial j₀ := by
        module
      _ = (ctx.tau (FTtypeP_bridge ctx j₀) - 1 +
              ctx.eta IrreducibleCharacter.trivial j₀) -
            (ctx.tau (FTtypeP_bridge ctx j) - 1) -
              ctx.eta IrreducibleCharacter.trivial j₀ :=
        congrArg
          (fun z : ClassFunction G ℂ ↦
            z - (ctx.tau (FTtypeP_bridge ctx j) - 1) -
              ctx.eta IrreducibleCharacter.trivial j₀)
          hEq
      _ = -(ctx.tau (FTtypeP_bridge ctx j) -
            ctx.tau (FTtypeP_bridge ctx j₀)) := by
        module
  have horthj := typeIConstantEta_tauL_bridge_orthogonal
    ctx L maxL hdis (FTtype1Bridge L phi) j
      (hA j hj) (hcore j hj)
  have horthj₀ := typeIConstantEta_tauL_bridge_orthogonal
    ctx L maxL hdis (FTtype1Bridge L phi) j₀
      (hA j₀ hj₀) (hcore j₀ hj₀)
  apply sub_eq_zero.mp
  rw [← supportBridges_pairing_sub_right]
  rw [hetaDiff, ← neg_one_smul ℂ,
    characterPairing_smul_right,
    supportBridges_pairing_sub_right, horthj, horthj₀]
  simp

/-! ## Pairing, projection, parity, and numerical helpers -/

private theorem typeIParity_starPairing_finset_sum_left
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (g : ClassFunction Q ℂ) :
    starCharacterPairing (∑ i ∈ s, f i) g =
      ∑ i ∈ s, starCharacterPairing (f i) g := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_left, ih,
        Finset.sum_insert hi]

private theorem typeIParity_starPairing_finset_sum_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) {I : Type*}
    (s : Finset I) (g : I → ClassFunction Q ℂ) :
    starCharacterPairing f (∑ i ∈ s, g i) =
      ∑ i ∈ s, starCharacterPairing f (g i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_right, ih,
        Finset.sum_insert hi]

private theorem typeIParity_normSq_sum_orthogonal
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ClassFunction Q ℂ)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j →
      starCharacterPairing (f i) (f j) = 0) :
    classFunctionNormSq (∑ i ∈ s, f i) =
      ∑ i ∈ s, classFunctionNormSq (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [classFunctionNormSq]
  | @insert i s hi ih =>
      have his :
          starCharacterPairing (f i) (∑ j ∈ s, f j) = 0 := by
        rw [typeIParity_starPairing_finset_sum_right]
        apply Finset.sum_eq_zero
        intro j hj
        exact horth i (Finset.mem_insert_self i s) j
          (Finset.mem_insert_of_mem hj) (fun hij ↦ hi (hij ▸ hj))
      rw [Finset.sum_insert hi,
        supportBridges_normSq_add_of_orthogonal _ _ his,
        Finset.sum_insert hi]
      congr 1
      exact ih fun a ha b hb hab ↦
        horth a (Finset.mem_insert_of_mem ha)
          b (Finset.mem_insert_of_mem hb) hab

private theorem typeIParity_one_le_normSq_intCast
    (z : ℤ) (hz : z ≠ 0) :
    1 ≤ Complex.normSq (z : ℂ) := by
  rw [Complex.normSq_intCast]
  have hpos : 0 < z * z := mul_self_pos.mpr hz
  exact_mod_cast (Int.add_one_le_iff.mpr hpos)

/-!
The elementary Bessel step used twice below.  It deliberately takes the
coefficients in `ℂ`: the two applications respectively use the normalized
type-I degrees and the constant coefficient `bLeta`.
-/
private theorem typeIParity_weighted_projection_le_norm
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} [DecidableEq I]
    (s : Finset I) (f : I → ClassFunction Q ℂ)
    (c : I → ℂ) (beta : ClassFunction Q ℂ)
    (horth : ∀ i ∈ s, ∀ j ∈ s,
      starCharacterPairing (f i) (f j) = if i = j then 1 else 0)
    (hpair : ∀ i ∈ s,
      starCharacterPairing beta (f i) = c i) :
    ∑ i ∈ s, Complex.normSq (c i) ≤ classFunctionNormSq beta := by
  classical
  let X : ClassFunction Q ℂ := ∑ i ∈ s, c i • f i
  let Y : ClassFunction Q ℂ := beta - X
  have hXpair (j : I) (hj : j ∈ s) :
      starCharacterPairing X (f j) = c j := by
    dsimp only [X]
    rw [typeIParity_starPairing_finset_sum_left]
    rw [Finset.sum_eq_single j]
    · rw [starCharacterPairing_smul_left,
        horth j hj j hj, if_pos rfl, mul_one]
    · intro i hi hij
      rw [starCharacterPairing_smul_left,
        horth i hi j hj, if_neg hij]
      simp
    · exact fun h ↦ (h hj).elim
  have hYpair (j : I) (hj : j ∈ s) :
      starCharacterPairing Y (f j) = 0 := by
    dsimp only [Y]
    rw [supportBridges_starPairing_sub_left,
      hpair j hj, hXpair j hj, sub_self]
  have hYX : starCharacterPairing Y X = 0 := by
    dsimp only [X]
    rw [typeIParity_starPairing_finset_sum_right]
    apply Finset.sum_eq_zero
    intro i hi
    rw [starCharacterPairing_smul_right, hYpair i hi]
    simp
  have hXY : starCharacterPairing X Y = 0 := by
    calc
      starCharacterPairing X Y =
          star (starCharacterPairing Y X) :=
        starCharacterPairing_conj_symm X Y
      _ = 0 := by rw [hYX]; simp
  have hdecomp : beta = X + Y := by
    dsimp only [Y]
    abel
  have hnormX : classFunctionNormSq X =
      ∑ i ∈ s, Complex.normSq (c i) := by
    dsimp only [X]
    rw [typeIParity_normSq_sum_orthogonal]
    · apply Finset.sum_congr rfl
      intro i hi
      rw [supportBridges_normSq_smul,
        classFunctionNormSq_eq_re_starCharacterPairing,
        horth i hi i hi, if_pos rfl]
      norm_num
    · intro i hi j hj hij
      rw [starCharacterPairing_smul_left,
        starCharacterPairing_smul_right,
        horth i hi j hj, if_neg hij]
      simp
  rw [hdecomp,
    supportBridges_normSq_add_of_orthogonal _ _ hXY,
    hnormX]
  exact le_add_of_nonneg_right (classFunctionNormSq_nonneg Y)

private theorem typeIParity_frobeniusIn_decomposition
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

private theorem typeIParity_target_inverse
    (f : ClassFunction (⊤ : Subgroup G) ℂ) :
    ClassFunction.inverseLinear (typeIBridgeTargetMap f) =
      typeIBridgeTargetMap (ClassFunction.inverseLinear f) := by
  ext x
  simp [ClassFunction.inverseLinear_apply, typeIBridgeTargetMap,
    ClassFunction.comap_apply]

private theorem typeIParity_target_normSq
    (f : ClassFunction (⊤ : Subgroup G) ℂ) :
    classFunctionNormSq (typeIBridgeTargetMap f) =
      classFunctionNormSq f := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold classFunctionNormSq
  rw [hcard]
  congr 1
  apply Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv
  intro x
  simp [typeIBridgeTargetMap, ClassFunction.comap_apply]

private theorem typeIParity_cfConjC_dadeInducedTrivial
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {Q : Subgroup Gamma} (K : Subgroup Q) :
    cfConjC (dadeInducedTrivial K) = dadeInducedTrivial K := by
  unfold dadeInducedTrivial cfConjC
  rw [ClassFunction.mapRingHom_induce]
  congr 1
  ext x
  simp [IrreducibleCharacter.trivial_apply]

private def typeIParity_fittingDadeHyp
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G)) :
    DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity ((FTType1FittingIn L).map L.subtype)) := by
  simpa only [FTType1FittingIn,
    Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)] using
      FT_DadeF_hyp L maxL

private theorem typeIParity_delta_context_top
    {L : Subgroup G} (H : Subgroup L) [H.Normal]
    (dd : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ)
    (zeta : IrreducibleCharacter L ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade dd) nu)
    (hzeta : (zeta : ClassFunction L ℂ) ∈
      seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥)
    (_hzetaOne : zeta 1 = (H.index : ℂ))
    (data : DadeInd1SubLinConclusion H dd nu zeta) :
    let beta := dadeInd1Beta H dd (zeta : ClassFunction L ℂ)
    let delta := beta + nu zeta
    characterPairing delta
          (((IrreducibleCharacter.trivial :
              IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
            ClassFunction (⊤ : Subgroup G) ℂ)) = 1 ∧
      ClassFunction.IsVirtual delta ∧ cfReal delta := by
  let calS := seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥
  let beta := dadeInd1Beta H dd (zeta : ClassFunction L ℂ)
  let delta := beta + nu zeta
  let oneTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    ((IrreducibleCharacter.trivial :
      IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
        ClassFunction (⊤ : Subgroup G) ℂ)
  have hzetaSpan : (zeta : ClassFunction L ℂ) ∈
      AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hzeta
  have hnuVirtual : ClassFunction.IsVirtual (nu zeta) :=
    hcoh.mapsToVirtual _ hzetaSpan
  have hdeltaVirtual : ClassFunction.IsVirtual delta :=
    data.beta_virtual.add hnuVirtual
  have honeVirtual : ClassFunction.IsVirtual oneTop := by
    dsimp only [oneTop]
    exact supportBridges_irreducible_isVirtual
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ)
  have hdeltaStarOne :
      starCharacterPairing delta oneTop = 1 := by
    change starCharacterPairing (beta + nu zeta) oneTop = 1
    rw [starCharacterPairing_add_left]
    change starCharacterPairing beta
          (((IrreducibleCharacter.trivial :
              IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
            ClassFunction (⊤ : Subgroup G) ℂ)) +
        starCharacterPairing (nu zeta)
          (((IrreducibleCharacter.trivial :
              IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
            ClassFunction (⊤ : Subgroup G) ℂ)) = 1
    rw [data.beta_pairing_one,
      data.image_orthogonal_one (zeta : ClassFunction L ℂ) hzeta,
      add_zero]
  have hdeltaOne : characterPairing delta oneTop = 1 := by
    rw [← PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      hdeltaVirtual honeVirtual]
    exact hdeltaStarOne
  let zetaC : IrreducibleCharacter L ℂ :=
    IrreducibleCharacter.mapRingEquiv complexConjugation zeta
  have hzetaCeq : zetaC = IrreducibleCharacter.dual zeta :=
    FTType1InfrastructureInternal.conjugateIrreducibleEqDual zeta
  have hzetaCmem : (zetaC : ClassFunction L ℂ) ∈ calS := by
    rw [hzetaCeq, ← ClassFunction.inverseLinear_irreducible]
    exact seqInd_inverse_mem (k := ℂ) H ⊤ ⊥ hzeta
  have hzetaCSpan : (zetaC : ClassFunction L ℂ) ∈
      AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hzetaCmem
  have hdiffSpan :
      (zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ) ∈
        AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ)) :=
    (AddSubgroup.closure _).sub_mem hzetaSpan hzetaCSpan
  have hdiffOn :
      (zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ) ∈
        ClassFunction.supportedOn (nonidentitySet L) := by
    rw [hzetaCeq, ← ClassFunction.inverseLinear_irreducible]
    exact FTType1InfrastructureInternal.inverseSubSupported
      (zeta : ClassFunction L ℂ)
  have hagree :
      nu ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) =
        Dade dd
          ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) :=
    hcoh.agrees _ hdiffSpan hdiffOn
  have hconjNu : cfConjC (nu zeta) = nu zetaC :=
    cfConjC_Dade_coherent dd H ⊤ ⊥ hcoh
      (mFT_odd (⊤ : Subgroup G)) zeta hzeta
  have hconjBeta :
      cfConjC beta =
        Dade dd (dadeInducedTrivial H - (zetaC : ClassFunction L ℂ)) := by
    have htriv :
        ClassFunction.mapRingHom (starRingEnd ℂ) (dadeInducedTrivial H) =
          dadeInducedTrivial H := by
      change cfConjC (dadeInducedTrivial H) = dadeInducedTrivial H
      exact typeIParity_cfConjC_dadeInducedTrivial H
    have hzetaConj :
        ClassFunction.mapRingHom (starRingEnd ℂ)
            (zeta : ClassFunction L ℂ) =
          (zetaC : ClassFunction L ℂ) := by
      change cfConjC (zeta : ClassFunction L ℂ) =
        (zetaC : ClassFunction L ℂ)
      rw [cfConjC_irreducible]
    change ClassFunction.mapRingHom (starRingEnd ℂ)
        (Dade dd (dadeInducedTrivial H - (zeta : ClassFunction L ℂ))) = _
    rw [← Dade_conjC, map_sub, htriv, hzetaConj]
  have hconjDelta : cfConjC delta = delta := by
    change cfConjC (beta + nu zeta) = beta + nu zeta
    rw [map_add, hconjBeta, hconjNu]
    have hsource :
        dadeInducedTrivial H - (zetaC : ClassFunction L ℂ) =
          (dadeInducedTrivial H - (zeta : ClassFunction L ℂ)) +
            ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) := by
      abel
    have hnuCancel :
        nu ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) +
            nu zetaC = nu zeta := by
      have hsourceCancel :
          ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) +
              (zetaC : ClassFunction L ℂ) = zeta := by
        module
      calc
        nu ((zeta : ClassFunction L ℂ) - (zetaC : ClassFunction L ℂ)) +
              nu zetaC =
            nu (((zeta : ClassFunction L ℂ) -
              (zetaC : ClassFunction L ℂ)) + zetaC) :=
          (map_add nu _ _).symm
        _ = nu zeta := congrArg nu hsourceCancel
    calc
      Dade dd (dadeInducedTrivial H - (zetaC : ClassFunction L ℂ)) +
            nu zetaC =
          (Dade dd (dadeInducedTrivial H - (zeta : ClassFunction L ℂ)) +
              Dade dd ((zeta : ClassFunction L ℂ) -
                (zetaC : ClassFunction L ℂ))) + nu zetaC := by
            rw [← map_add, ← hsource]
      _ = (Dade dd
              (dadeInducedTrivial H - (zeta : ClassFunction L ℂ)) +
            nu ((zeta : ClassFunction L ℂ) -
              (zetaC : ClassFunction L ℂ))) + nu zetaC := by
            rw [hagree]
      _ = Dade dd
              (dadeInducedTrivial H - (zeta : ClassFunction L ℂ)) +
            nu zeta := by
            rw [add_assoc, hnuCancel]
      _ = beta + nu zeta := rfl
  have hdeltaReal : cfReal delta := by
    rw [cfReal,
      FTType1InfrastructureInternal.inverseEqConjOfVirtual hdeltaVirtual,
      hconjDelta]
  exact ⟨hdeltaOne, hdeltaVirtual, hdeltaReal⟩

private theorem typeIParity_odd_sum_cases
    {Q : Type u} [Group Q] [Fintype Q]
    {f₁ g₁ f₂ g₂ : ClassFunction Q ℂ}
    (hf₁ : ClassFunction.IsVirtual f₁)
    (hg₁ : ClassFunction.IsVirtual g₁)
    (hf₂ : ClassFunction.IsVirtual f₂)
    (hg₂ : ClassFunction.IsVirtual g₂)
    {E F : ClassFunction Q ℂ}
    (hEven : evenCharacterPairing E F)
    (hrelation : characterPairing E F =
      characterPairing f₁ g₁ + characterPairing f₂ g₂ - 1) :
    oddCharacterPairing f₁ g₁ ∨ oddCharacterPairing f₂ g₂ := by
  obtain ⟨a, ha⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt hf₁ hg₁
  obtain ⟨b, hb⟩ :=
    PTypeCorePairingInternal.pTypeCore_virtual_pairing_isInt hf₂ hg₂
  obtain ⟨k, hk⟩ := hEven
  have habCast : ((2 * k : ℤ) : ℂ) = ((a + b - 1 : ℤ) : ℂ) := by
    calc
      ((2 * k : ℤ) : ℂ) = characterPairing E F := hk.symm
      _ = characterPairing f₁ g₁ + characterPairing f₂ g₂ - 1 :=
        hrelation
      _ = ((a + b - 1 : ℤ) : ℂ) := by
        rw [ha, hb]
        push_cast
        ring
  have hab : 2 * k = a + b - 1 := Int.cast_injective habCast
  rcases Int.even_or_odd a with ⟨m, hm⟩ | ⟨m, hm⟩
  · right
    refine ⟨k - m, ?_⟩
    calc
      characterPairing f₂ g₂ = (b : ℂ) := hb
      _ = ((2 * (k - m) + 1 : ℤ) : ℂ) := by
        exact congrArg ((↑) : ℤ → ℂ) (by omega)
  · left
    refine ⟨m, ?_⟩
    calc
      characterPairing f₁ g₁ = (a : ℂ) := ha
      _ = ((2 * m + 1 : ℤ) : ℂ) := congrArg ((↑) : ℤ → ℂ) hm

private theorem typeIParity_normalized_degree_square_sum
    (L : Subgroup G)
    (H : Subgroup L) [H.Normal]
    (q : ClassFunction L ℂ → ℕ)
    (hq : ∀ psi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥,
      psi 1 / (H.index : ℂ) = (q psi : ℂ))
    (hirr : ∀ psi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥,
      IsIrreducibleCharacter L ℂ psi) :
    ∑ psi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥,
        (q psi : ℝ) ^ 2 =
      ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
  classical
  let calS := seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥
  have hself (psi : ClassFunction L ℂ) (hpsi : psi ∈ calS) :
      characterPairing psi psi = 1 := by
    let psiIrr : IrreducibleCharacter L ℂ :=
      ⟨psi, hirr psi (by simpa only [calS] using hpsi)⟩
    simpa only [psiIrr] using psiIrr.characterPairing_self
  have hindexNe : (H.index : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
  have hdegreeQ (psi : ClassFunction L ℂ) (hpsi : psi ∈ calS) :
      psi 1 = (H.index : ℂ) * (q psi : ℂ) := by
    have hdiv := hq psi (by simpa only [calS] using hpsi)
    have hmul : psi 1 = (q psi : ℂ) * (H.index : ℂ) :=
      (div_eq_iff hindexNe).mp hdiv
    simpa only [mul_comm] using hmul
  have hsum :
      (∑ psi ∈ calS,
          psi 1 ^ 2 / characterPairing psi psi) =
        (H.index : ℂ) * ((Nat.card H : ℂ) - 1) := by
    simpa only [calS] using sum_seqIndC1_square (k := ℂ) H
  have hsumQ :
      (∑ psi ∈ calS, ((q psi : ℂ) ^ 2)) =
        ((Nat.card H : ℂ) - 1) / (H.index : ℂ) := by
    calc
      (∑ psi ∈ calS, ((q psi : ℂ) ^ 2)) =
          (H.index : ℂ)⁻¹ ^ 2 *
            ∑ psi ∈ calS,
              psi 1 ^ 2 / characterPairing psi psi := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro psi hpsi
        rw [hself psi hpsi, div_one, hdegreeQ psi hpsi]
        field_simp [hindexNe]
      _ = (H.index : ℂ)⁻¹ ^ 2 *
          ((H.index : ℂ) * ((Nat.card H : ℂ) - 1)) := by
        rw [hsum]
      _ = ((Nat.card H : ℂ) - 1) / (H.index : ℂ) := by
        field_simp [hindexNe]
  have hre := congrArg Complex.re hsumQ
  rw [Complex.re_sum] at hre
  simp only [pow_two, Complex.mul_re, Complex.natCast_re,
    Complex.natCast_im, mul_zero, zero_mul, sub_zero,
    Complex.div_natCast_re, Complex.sub_re, Complex.one_re] at hre
  simpa only [calS, pow_two] using hre

private theorem typeIParity_final_disjunction
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1)
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (phi : ClassFunction L ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁)
    (Lphi : phi ∈ FTType1SeqIndFamily L)
    (phi1e : phi 1 = ((FTtype1CoreIndex L : ℕ) : ℂ))
    (hdis : Disjoint (FT_Dade_full_support L)
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G)))
    (horth : orthogonalFamilies
      (tau₁ ''
        (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)))
      (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)))
    (hc : ∀ j, j ≠ IrreducibleCharacter.trivial →
      characterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial j) =
        characterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial
            (FTtypePBridgeIndex ctx))) :
    (oddCharacterPairing
        (ctx.tau
          (FTtypeP_bridge ctx (FTtypePBridgeIndex ctx)))
        (tau₁ phi) ∧
      (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
          (FTtype1CoreIndex L : ℝ) ≤
        (((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ))) ∨
      (oddCharacterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial
            (FTtypePBridgeIndex ctx)) ∧
        Nat.card W₂ ≤ FTtype1CoreIndex L) := by
  classical
  obtain ⟨⟨hA, hcore⟩, _hnorm,
    ⟨hgap, hGammaOne, hGammaReal⟩, hGammaBound, _hdvd⟩ :=
    FTtypeP_bridge_facts ctx
  let j₀ : IrreducibleCharacter W₂ ℂ := FTtypePBridgeIndex ctx
  have hj₀ : j₀ ≠ IrreducibleCharacter.trivial :=
    FTtypePBridgeIndex_ne_trivial ctx
  let H : Subgroup L := FTType1FittingIn L
  letI : H.Normal := by
    simpa only [H, FTType1FittingIn] using Fcore_normal L
  let dd : DadeHypothesis (⊤ : Subgroup G) L
      (subgroupNonidentity (H.map L.subtype)) :=
    typeIParity_fittingDadeHyp L maxL
  let nuTop : ClassFunction L ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    typeIBridgeSourceMap.comp tau₁
  have hcohTop : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade dd) nuTop := by
    simpa only [H, dd, nuTop, FTType1SeqIndFamily,
      typeIParity_fittingDadeHyp, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)] using
        typeIBridgeCoherenceTop cohL
  have hphiMem : phi ∈
      seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥ := by
    simpa only [H, FTType1SeqIndFamily] using Lphi
  let phiIrr : IrreducibleCharacter L ℂ :=
    ⟨phi, FTtype1_Ind_irr L maxL Ltype1 phi Lphi⟩
  have hcalS : 1 <
      (seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥).card := by
    have htwo := seqInd_nontrivial (k := ℂ) H (mFT_odd L)
      (⊤ : Subgroup H) ⊥ hphiMem
    omega
  let data : DadeInd1SubLinConclusion H dd nuTop phiIrr :=
    Dade_Ind1_sub_lin H dd nuTop phiIrr hcohTop hcalS hphiMem
      (by simpa only [H, FTtype1CoreIndex, phiIrr] using phi1e)
  let betaTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    dadeInd1Beta H dd phi
  let betaL : ClassFunction G ℂ :=
    FTtype1Dade L maxL (FTtype1Bridge L phi)
  let betaS : ClassFunction G ℂ :=
    ctx.tau (FTtypeP_bridge ctx j₀)
  let eta₀ : ClassFunction G ℂ :=
    ctx.eta IrreducibleCharacter.trivial j₀
  let GammaS : ClassFunction G ℂ := FTtypeP_bridge_gap ctx
  let oneTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    ((IrreducibleCharacter.trivial :
      IrreducibleCharacter (⊤ : Subgroup G) ℂ) :
        ClassFunction (⊤ : Subgroup G) ℂ)
  let oneG : ClassFunction G ℂ :=
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)
  let deltaTop : ClassFunction (⊤ : Subgroup G) ℂ :=
    betaTop + nuTop phi
  let deltaL : ClassFunction G ℂ := betaL + tau₁ phi
  let GammaL : ClassFunction G ℂ := deltaL - oneG
  have hbetaAdapter : typeIBridgeTargetMap betaTop = betaL := by
    simpa only [betaTop, betaL, H, dd,
      typeIParity_fittingDadeHyp, dadeInd1Beta, dadeInducedTrivial,
      FTtype1Dade, FTtype1Bridge, typeIBridgeTargetMap,
      LinearMap.comp_apply, FTType1FittingIn,
      Subgroup.map_subgroupOf_eq_of_le (Fcore_sub L)]
  have hdeltaAdapter : typeIBridgeTargetMap deltaTop = deltaL := by
    dsimp only [deltaTop, deltaL]
    rw [map_add, hbetaAdapter]
    simpa only [nuTop, LinearMap.comp_apply, typeIBridgeTarget_source]
  have hdeltaTop :
      characterPairing deltaTop oneTop = 1 ∧
        ClassFunction.IsVirtual deltaTop ∧ cfReal deltaTop := by
    simpa only [deltaTop, betaTop, oneTop, phiIrr] using
      typeIParity_delta_context_top
        H dd nuTop phiIrr hcohTop hphiMem
          (by simpa only [H, FTtype1CoreIndex, phiIrr] using phi1e) data
  have htargetOne : typeIBridgeTargetMap oneTop = oneG := by
    simpa only [oneTop, oneG] using
      (typeIBridgeTarget_trivial (G := G))
  have hdeltaOne : characterPairing deltaL oneG = 1 := by
    have htransport := typeIBridgeTarget_pairing deltaTop oneTop
    rw [hdeltaAdapter, htargetOne] at htransport
    exact htransport.trans hdeltaTop.1
  have hdeltaVirtual : ClassFunction.IsVirtual deltaL := by
    rw [← hdeltaAdapter]
    exact typeIBridgeTarget_virtual hdeltaTop.2.1
  have hdeltaReal : cfReal deltaL := by
    rw [cfReal, ← hdeltaAdapter, typeIParity_target_inverse]
    exact congrArg typeIBridgeTargetMap hdeltaTop.2.2
  have honeVirtual : ClassFunction.IsVirtual oneG := by
    dsimp only [oneG]
    exact supportBridges_irreducible_isVirtual
      (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ)
  have honeReal : cfReal oneG := by
    rw [cfReal]
    apply ClassFunction.ext
    intro x
    simp only [oneG, ClassFunction.inverseLinear_apply,
      IrreducibleCharacter.trivial_apply]
  have honePair : characterPairing oneG oneG = 1 := by
    simpa only [oneG] using
      (IrreducibleCharacter.characterPairing_self
        (IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ))
  have hGammaLVirtual : ClassFunction.IsVirtual GammaL :=
    hdeltaVirtual.sub honeVirtual
  have hGammaLReal : cfReal GammaL := by
    dsimp only [GammaL]
    rw [cfReal, map_sub]
    rw [show ClassFunction.inverseLinear deltaL = deltaL from hdeltaReal,
      show ClassFunction.inverseLinear oneG = oneG from honeReal]
  have hGammaLOne : characterPairing GammaL oneG = 0 := by
    dsimp only [GammaL]
    rw [supportBridges_pairing_sub_left, hdeltaOne, honePair, sub_self]
  have hGammaSVirtual : ClassFunction.IsVirtual GammaS := by
    dsimp only [GammaS]
    exact supportBridges_gap_isVirtual ctx (hA j₀ hj₀)
  have hGammaSReal : cfReal GammaS := by
    simpa only [GammaS] using hGammaReal
  have hEvenCross : evenCharacterPairing GammaL GammaS := by
    apply (cfdot_real_vchar_even (Q := G)
      (IsMinSimpleOddGroup.odd_card (G := G)) GammaL GammaS
      ⟨hGammaLVirtual, hGammaLReal⟩
      ⟨hGammaSVirtual, hGammaSReal⟩).2
    left
    refine ⟨0, ?_⟩
    simpa only [oneG, Int.mul_zero, Int.cast_zero] using hGammaLOne
  have hbetaLVirtual : ClassFunction.IsVirtual betaL := by
    rw [← hbetaAdapter]
    apply typeIBridgeTarget_virtual
    simpa only [betaTop, phiIrr] using data.beta_virtual
  have hbetaSVirtual : ClassFunction.IsVirtual betaS := by
    dsimp only [betaS]
    exact supportBridges_tau_bridge_isVirtual ctx j₀ (hA j₀ hj₀)
  have htauPhiVirtual : ClassFunction.IsVirtual (tau₁ phi) :=
    cohL.mapsToVirtual phi (AddSubgroup.subset_closure Lphi)
  have heta₀Virtual : ClassFunction.IsVirtual eta₀ := by
    dsimp only [eta₀]
    exact supportBridges_eta_isVirtual ctx IrreducibleCharacter.trivial j₀
  have hbetaLbetaS : characterPairing betaL betaS = 0 := by
    dsimp only [betaL, betaS]
    exact typeIConstantEta_tauL_bridge_orthogonal ctx L maxL hdis
      (FTtype1Bridge L phi) j₀ (hA j₀ hj₀) (hcore j₀ hj₀)
  have htauPhiEta : characterPairing (tau₁ phi) eta₀ = 0 := by
    apply horth (tau₁ phi) ⟨phi, Lphi, rfl⟩ eta₀
    dsimp only [eta₀]
    rw [Finset.mem_coe]
    exact supportBridges_eta_mem_cyclicImageFamily ctx
      IrreducibleCharacter.trivial j₀
  have heta₀OneStar : starCharacterPairing eta₀ oneG = 0 := by
    simpa only [eta₀, oneG, typeIBridge_one_eq_trivial] using
      supportBridges_eta_one_orthogonal ctx
        IrreducibleCharacter.trivial j₀ hj₀
  have heta₀One : characterPairing eta₀ oneG = 0 := by
    rw [← PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      heta₀Virtual honeVirtual]
    exact heta₀OneStar
  have honeTopVirtual : ClassFunction.IsVirtual oneTop := by
    dsimp only [oneTop]
    exact supportBridges_irreducible_isVirtual
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter (⊤ : Subgroup G) ℂ)
  have htauPhiOne : characterPairing (tau₁ phi) oneG = 0 := by
    have htop := data.image_orthogonal_one phi hphiMem
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (hcohTop.mapsToVirtual phi (AddSubgroup.subset_closure hphiMem))
      honeTopVirtual] at htop
    have hamb := typeIBridgeTarget_pairing (nuTop phi) oneTop
    rw [htargetOne] at hamb
    simpa only [nuTop, LinearMap.comp_apply,
      typeIBridgeTarget_source] using hamb.trans htop
  have hbetaLOne : characterPairing betaL oneG = 1 := by
    have htop := data.beta_pairing_one
    rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      data.beta_virtual honeTopVirtual] at htop
    have hamb := typeIBridgeTarget_pairing betaTop oneTop
    rw [hbetaAdapter, htargetOne] at hamb
    simpa only [betaTop, phiIrr] using hamb.trans htop
  have hGammaSEq : GammaS = betaS - oneG + eta₀ := by
    simpa only [GammaS, betaS, eta₀, oneG,
      typeIBridge_one_eq_trivial] using (hgap j₀ hj₀).symm
  have hGammaSOne : characterPairing GammaS oneG = 0 := by
    simpa only [GammaS, oneG, typeIBridge_one_eq_trivial] using hGammaOne
  have hbetaSOne : characterPairing betaS oneG = 1 := by
    rw [hGammaSEq, characterPairing_add_left,
      supportBridges_pairing_sub_left, honePair, heta₀One,
      add_zero] at hGammaSOne
    exact sub_eq_zero.mp hGammaSOne
  have honeBetaS : characterPairing oneG betaS = 1 := by
    rw [characterPairing_comm, hbetaSOne]
  have honeEta₀ : characterPairing oneG eta₀ = 0 := by
    rw [characterPairing_comm, heta₀One]
  have honeTauPhi : characterPairing oneG (tau₁ phi) = 0 := by
    rw [characterPairing_comm, htauPhiOne]
  have htauPhiBetaS : characterPairing (tau₁ phi) betaS =
      characterPairing betaS (tau₁ phi) :=
    characterPairing_comm _ _
  have hGammaLEq : GammaL = betaL - oneG + tau₁ phi := by
    dsimp only [GammaL, deltaL]
    module
  have hparityRelation :
      characterPairing GammaL GammaS =
        characterPairing betaS (tau₁ phi) +
          characterPairing betaL eta₀ - 1 := by
    rw [hGammaLEq, hGammaSEq]
    simp only [characterPairing_add_left, characterPairing_add_right,
      supportBridges_pairing_sub_left, supportBridges_pairing_sub_right,
      hbetaLbetaS, hbetaLOne, honeBetaS, honePair,
      honeEta₀, htauPhiBetaS, htauPhiOne, htauPhiEta]
    ring
  have hoddCases :
      oddCharacterPairing betaS (tau₁ phi) ∨
        oddCharacterPairing betaL eta₀ :=
    typeIParity_odd_sum_cases hbetaSVirtual htauPhiVirtual
      hbetaLVirtual heta₀Virtual hEvenCross hparityRelation
  rcases hoddCases with hoddS | hoddL
  · left
    refine ⟨by simpa only [betaS, j₀] using hoddS, ?_⟩
    let calL := FTType1SeqIndFamily L
    have hfamilyVirtual : ∀ alpha ∈ calL.image tau₁,
        ClassFunction.IsVirtual alpha := by
      intro alpha halpha
      rcases Finset.mem_image.mp halpha with ⟨psi, hpsi, rfl⟩
      exact cohL.mapsToVirtual psi (AddSubgroup.subset_closure hpsi)
    have hfamilyOrthonormal : ∀ alpha ∈ calL.image tau₁,
        ∀ gamma ∈ calL.image tau₁,
          characterPairing alpha gamma = if alpha = gamma then 1 else 0 := by
      intro alpha halpha gamma hgamma
      rcases Finset.mem_image.mp halpha with ⟨psi, hpsi, rfl⟩
      rcases Finset.mem_image.mp hgamma with ⟨xi, hxi, rfl⟩
      rw [cohL.isometry psi (AddSubgroup.subset_closure hpsi)
        xi (AddSubgroup.subset_closure hxi)]
      by_cases hEq : psi = xi
      · subst xi
        rw [if_pos rfl]
        let psiIrr : IrreducibleCharacter L ℂ :=
          ⟨psi, FTtype1_Ind_irr L maxL Ltype1 psi hpsi⟩
        simpa only [psiIrr] using psiIrr.characterPairing_self
      · have himageNe : tau₁ psi ≠ tau₁ xi := by
          intro heq
          have hcross := cohL.isometry psi
            (AddSubgroup.subset_closure hpsi)
            xi (AddSubgroup.subset_closure hxi)
          have hself := cohL.isometry xi
            (AddSubgroup.subset_closure hxi)
            xi (AddSubgroup.subset_closure hxi)
          let xiIrr : IrreducibleCharacter L ℂ :=
            ⟨xi, FTtype1_Ind_irr L maxL Ltype1 xi hxi⟩
          have hxiSelf : characterPairing xi xi = 1 := by
            simpa only [xiIrr] using xiIrr.characterPairing_self
          rw [heq, seqInd_ortho H hpsi hxi hEq] at hcross
          rw [hself, hxiSelf] at hcross
          exact one_ne_zero hcross
        rw [if_neg himageNe, seqInd_ortho H hpsi hxi hEq]
    obtain ⟨X, Y, hXspan, hXvirtual, hYvirtual,
      hGammaSplit, hYorth, hXY⟩ :=
      orthogonal_split_virtual (calL.image tau₁)
        hfamilyVirtual hfamilyOrthonormal hGammaSVirtual
    have hYXstar : starCharacterPairing Y X = 0 := by
      rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hYvirtual hXvirtual, characterPairing_comm, hXY]
    have hXcyclic : ∀ Z ∈
        (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)),
        starCharacterPairing X Z = 0 := by
      intro Z hZ
      have hZVirtual : ClassFunction.IsVirtual Z := by
        have hZFin : Z ∈ FTtypePCyclicImageFamily ctx := by
          simpa only [Finset.mem_coe] using hZ
        rcases Finset.mem_image.mp hZFin with ⟨chiCF, hchiCF, rfl⟩
        rcases Finset.mem_image.mp hchiCF with ⟨chi, _hchi, rfl⟩
        obtain ⟨i, j, rfl⟩ :=
          IrreducibleCharacter.exists_cyclicTICharacter defW chi
        exact supportBridges_eta_isVirtual ctx i j
      have hclosure : ∀ {A : ClassFunction G ℂ},
          A ∈ AddSubgroup.closure
              (↑(calL.image tau₁) : Set (ClassFunction G ℂ)) →
            starCharacterPairing A Z = 0 := by
        intro A hA
        induction hA using AddSubgroup.closure_induction with
        | mem alpha halpha =>
            have halphaFin : alpha ∈ calL.image tau₁ := by
              simpa only [Finset.mem_coe] using halpha
            rcases Finset.mem_image.mp halphaFin with ⟨psi, hpsi, rfl⟩
            have hpsiFamily : psi ∈ FTType1SeqIndFamily L := by
              simpa only [calL] using hpsi
            have hpsiFamilySet : psi ∈
                (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)) := by
              simpa only [Finset.mem_coe] using hpsiFamily
            have hp := horth (tau₁ psi)
              ⟨psi, hpsiFamilySet, rfl⟩ Z hZ
            rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
              (cohL.mapsToVirtual psi
                (AddSubgroup.subset_closure hpsiFamilySet))
              hZVirtual]
            exact hp
        | zero => simp
        | add a b ha hb iha ihb =>
            rw [starCharacterPairing_add_left, iha, ihb, add_zero]
        | neg a ha iha =>
            rw [← neg_one_smul ℂ, starCharacterPairing_smul_left,
              iha, mul_zero]
      exact hclosure hXspan
    have hXupper : classFunctionNormSq X ≤
        (((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ) := by
      apply hGammaBound Y X
      · simpa only [GammaS, add_comm] using hGammaSplit
      · exact hYXstar
      · exact hXcyclic
    obtain ⟨n, hnOdd⟩ := hoddS
    let a : ℤ := 2 * n + 1
    have haOdd : characterPairing betaS (tau₁ phi) = (a : ℂ) := by
      simpa only [a] using hnOdd
    have haNe : a ≠ 0 := by
      dsimp only [a]
      omega
    have hqExists (psi : ClassFunction L ℂ) :
        ∃ n : ℕ, psi ∈ calL →
          psi 1 / (H.index : ℂ) = (n : ℂ) := by
      by_cases hpsi : psi ∈ calL
      · have hpsiSeq : psi ∈ seqInd H
            (Iirr_kerD (k := ℂ) (⊤ : Subgroup H) ⊥) := by
          simpa only [calL, H, FTType1SeqIndFamily, seqIndD] using hpsi
        obtain ⟨n, hn⟩ := dvd_index_seqInd1 H hpsiSeq
        exact ⟨n, fun _ ↦ hn⟩
      · exact ⟨0, fun hmem ↦ (hpsi hmem).elim⟩
    let q : ClassFunction L ℂ → ℕ :=
      fun psi ↦ Classical.choose (hqExists psi)
    have hq (psi : ClassFunction L ℂ) (hpsi : psi ∈ calL) :
        psi 1 / (H.index : ℂ) = (q psi : ℂ) :=
      Classical.choose_spec (hqExists psi) hpsi
    have hGammaPair (psi : ClassFunction L ℂ) (hpsi : psi ∈ calL) :
        starCharacterPairing GammaS (tau₁ psi) =
          (a : ℂ) * (q psi : ℂ) := by
      let d : ClassFunction L ℂ :=
        psi - (q psi : ℂ) • phi
      have hdClosure : d ∈ AddSubgroup.closure
          (↑calL : Set (ClassFunction L ℂ)) := by
        dsimp only [d]
        exact (AddSubgroup.closure _).sub_mem
          (AddSubgroup.subset_closure hpsi)
          (by
            have hm := (AddSubgroup.closure
              (↑calL : Set (ClassFunction L ℂ))).nsmul_mem
                (AddSubgroup.subset_closure Lphi) (q psi)
            rw [← Nat.cast_smul_eq_nsmul (R := ℂ)] at hm
            exact hm)
      have hdOn : d ∈ ClassFunction.supportedOn (nonidentitySet L) := by
        have hphiSeq : phi ∈ seqInd H
            (Iirr_kerD (k := ℂ) (⊤ : Subgroup H) ⊥) := by
          simpa only [seqIndD] using hphiMem
        have hpsiSeq : psi ∈ seqInd H
            (Iirr_kerD (k := ℂ) (⊤ : Subgroup H) ⊥) := by
          simpa only [calL, H, FTType1SeqIndFamily, seqIndD] using hpsi
        have hdSharp := seqInd_sub_lin_on H hphiSeq
          (by simpa only [H, FTtype1CoreIndex] using phi1e) hpsiSeq
        rw [hq psi hpsi] at hdSharp
        rw [ClassFunction.mem_supportedOn_iff] at hdSharp ⊢
        intro x hx
        apply hdSharp
        intro hxH
        exact hx hxH.2
      have hagree := cohL.agrees d hdClosure hdOn
      have hDadeOrth := typeIConstantEta_tauL_bridge_orthogonal
        ctx L maxL hdis d j₀ (hA j₀ hj₀) (hcore j₀ hj₀)
      have hsourcePair : characterPairing betaS (tau₁ psi) =
          (q psi : ℂ) * characterPairing betaS (tau₁ phi) := by
        have hzero : characterPairing betaS (tau₁ d) = 0 := by
          rw [characterPairing_comm, hagree]
          exact hDadeOrth
        dsimp only [d] at hzero
        rw [map_sub, map_smul, supportBridges_pairing_sub_right,
          characterPairing_smul_right] at hzero
        exact sub_eq_zero.mp hzero
      have htauPsiOne : characterPairing (tau₁ psi) oneG = 0 := by
        have hpsiTop : psi ∈ seqIndD (k := ℂ) H
            (⊤ : Subgroup H) ⊥ := by
          simpa only [calL, H, FTType1SeqIndFamily] using hpsi
        have htop := data.image_orthogonal_one psi hpsiTop
        rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          (hcohTop.mapsToVirtual psi
            (AddSubgroup.subset_closure hpsiTop))
          honeTopVirtual] at htop
        have hamb := typeIBridgeTarget_pairing (nuTop psi) oneTop
        rw [htargetOne] at hamb
        simpa only [nuTop, LinearMap.comp_apply,
          typeIBridgeTarget_source] using hamb.trans htop
      have honeTauPsi : characterPairing oneG (tau₁ psi) = 0 := by
        rw [characterPairing_comm, htauPsiOne]
      have hetaPsi : characterPairing eta₀ (tau₁ psi) = 0 := by
        rw [characterPairing_comm]
        exact horth (tau₁ psi) ⟨psi, hpsi, rfl⟩ eta₀
          (by
            rw [Finset.mem_coe]
            exact supportBridges_eta_mem_cyclicImageFamily ctx
              IrreducibleCharacter.trivial j₀)
      have hchar : characterPairing GammaS (tau₁ psi) =
          (a : ℂ) * (q psi : ℂ) := by
        rw [hGammaSEq, characterPairing_add_left,
          supportBridges_pairing_sub_left, hsourcePair,
          honeTauPsi, hetaPsi, sub_zero, add_zero, haOdd]
        ring
      rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        hGammaSVirtual
        (cohL.mapsToVirtual psi (AddSubgroup.subset_closure hpsi))]
      exact hchar
    have hXPair (psi : ClassFunction L ℂ) (hpsi : psi ∈ calL) :
        starCharacterPairing X (tau₁ psi) =
          (a : ℂ) * (q psi : ℂ) := by
      have hYzero : starCharacterPairing Y (tau₁ psi) = 0 := by
        rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hYvirtual (cohL.mapsToVirtual psi
            (AddSubgroup.subset_closure hpsi))]
        exact hYorth (tau₁ psi)
          (Finset.mem_image.mpr ⟨psi, hpsi, rfl⟩)
      have hp := hGammaPair psi hpsi
      rw [hGammaSplit, starCharacterPairing_add_left,
        hYzero, add_zero] at hp
      exact hp
    have hTauStarOrtho : ∀ psi ∈ calL, ∀ xi ∈ calL,
        starCharacterPairing (tau₁ psi) (tau₁ xi) =
          if psi = xi then 1 else 0 := by
      intro psi hpsi xi hxi
      rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        (cohL.mapsToVirtual psi (AddSubgroup.subset_closure hpsi))
        (cohL.mapsToVirtual xi (AddSubgroup.subset_closure hxi)),
        cohL.isometry psi (AddSubgroup.subset_closure hpsi)
          xi (AddSubgroup.subset_closure hxi)]
      split_ifs with heq
      · subst xi
        let psiIrr : IrreducibleCharacter L ℂ :=
          ⟨psi, FTtype1_Ind_irr L maxL Ltype1 psi hpsi⟩
        simpa only [psiIrr] using psiIrr.characterPairing_self
      · exact seqInd_ortho H hpsi hxi heq
    have hprojection := typeIParity_weighted_projection_le_norm calL
      tau₁ (fun psi ↦ (a : ℂ) * (q psi : ℂ)) X
      hTauStarOrtho hXPair
    have hqCore (psi : ClassFunction L ℂ)
        (hpsi : psi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        psi 1 / (H.index : ℂ) = (q psi : ℂ) := by
      apply hq psi
      simpa only [calL, H, FTType1SeqIndFamily] using hpsi
    have hsumQ := typeIParity_normalized_degree_square_sum L H q hqCore
      (fun psi hpsi ↦ FTtype1_Ind_irr L maxL Ltype1 psi
        (by simpa only [calL, H, FTType1SeqIndFamily] using hpsi))
    have haNorm : 1 ≤ Complex.normSq (a : ℂ) :=
      typeIParity_one_le_normSq_intCast a haNe
    have hcardH : Nat.card H = Nat.card (Fitting_core L) := by
      simpa only [H, FTType1FittingIn] using
        (Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          (G := G) (H := Fitting_core L) (K := L) (Fcore_sub L))
    have hindexH : H.index = FTtype1CoreIndex L := rfl
    have hsumQ' :
        ∑ psi ∈ calL, (q psi : ℝ) ^ 2 =
          ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
      simpa only [calL, H, FTType1SeqIndFamily] using hsumQ
    have hbaseEq :
        (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
            (FTtype1CoreIndex L : ℝ)) =
          ∑ psi ∈ calL, (q psi : ℝ) ^ 2 := by
      calc
        (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
              (FTtype1CoreIndex L : ℝ)) =
            (((Nat.card H - 1 : ℕ) : ℝ) / (H.index : ℝ)) := by
          rw [← hcardH, ← hindexH]
        _ = ((Nat.card H : ℝ) - 1) / (H.index : ℝ) := by
          rw [Nat.cast_sub (Nat.card_pos (α := H)), Nat.cast_one]
        _ = ∑ psi ∈ calL, (q psi : ℝ) ^ 2 := hsumQ'.symm
    have hbaseNonneg :
        0 ≤ (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
            (FTtype1CoreIndex L : ℝ)) := by
      rw [hbaseEq]
      positivity
    have hweighted :
        ∑ psi ∈ calL,
            Complex.normSq ((a : ℂ) * (q psi : ℂ)) =
          Complex.normSq (a : ℂ) *
            ∑ psi ∈ calL, (q psi : ℝ) ^ 2 := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro psi hpsi
      rw [Complex.normSq_mul, Complex.normSq_natCast, pow_two]
    have hlower :
        (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
            (FTtype1CoreIndex L : ℝ)) ≤
          ∑ psi ∈ calL,
            Complex.normSq ((a : ℂ) * (q psi : ℂ)) := by
      rw [hweighted, ← hbaseEq]
      exact le_mul_of_one_le_left hbaseNonneg haNorm
    exact hlower.trans (hprojection.trans hXupper)
  · right
    refine ⟨by simpa only [betaL, eta₀, j₀] using hoddL, ?_⟩
    obtain ⟨n, hnOdd⟩ := hoddL
    let b : ℤ := 2 * n + 1
    have hbOdd : characterPairing betaL eta₀ = (b : ℂ) := by
      simpa only [b] using hnOdd
    have hbNe : b ≠ 0 := by
      dsimp only [b]
      omega
    obtain ⟨E, hFrobE⟩ := FTtype1_Frobenius L maxL Ltype1
    have hFrobHE : IsFrobeniusDecomposition H (E.subgroupOf L) := by
      simpa only [H] using typeIParity_frobeniusIn_decomposition hFrobE
    have hindexBound : (H.index : ℝ) ≤
        ((Nat.card H : ℝ) - 1) / 2 :=
      odd_Frobenius_index_ler H (E.subgroupOf L) (mFT_odd L) hFrobHE
    have hgammaUpperTop : classFunctionNormSq data.gamma ≤
        (H.index : ℝ) - 1 := (data.norm_bounds hindexBound).2
    let gamma : ClassFunction G ℂ := typeIBridgeTargetMap data.gamma
    have hgammaUpper : classFunctionNormSq gamma ≤
        (FTtype1CoreIndex L : ℝ) - 1 := by
      rw [typeIParity_target_normSq]
      simpa only [H, FTtype1CoreIndex] using hgammaUpperTop
    let J : Finset (IrreducibleCharacter W₂ ℂ) :=
      Finset.univ.erase IrreducibleCharacter.trivial
    let eta : IrreducibleCharacter W₂ ℂ → ClassFunction G ℂ :=
      fun j ↦ ctx.eta IrreducibleCharacter.trivial j
    have hJ (j : IrreducibleCharacter W₂ ℂ) :
        j ∈ J ↔ j ≠ IrreducibleCharacter.trivial := by
      simp [J]
    have hetaOrtho : ∀ j ∈ J, ∀ k ∈ J,
        starCharacterPairing (eta j) (eta k) =
          if j = k then 1 else 0 := by
      intro j hj k hk
      dsimp only [eta]
      rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
        (supportBridges_eta_isVirtual ctx IrreducibleCharacter.trivial j)
        (supportBridges_eta_isVirtual ctx IrreducibleCharacter.trivial k),
        FTTypePCyclicRectangleInternal.characterPairing_eta]
      simp only [Prod.mk.injEq, true_and]
    have hgammaPair (j : IrreducibleCharacter W₂ ℂ) (hj : j ∈ J) :
        starCharacterPairing gamma (eta j) = (b : ℂ) := by
      have hj0 : j ≠ IrreducibleCharacter.trivial := (hJ j).mp hj
      have hbetaEta := hc j hj0
      have hdecompTop := data.decomposition
      have hdecompAmbient := congrArg typeIBridgeTargetMap hdecompTop
      have hsumEta : starCharacterPairing
          (typeIBridgeTargetMap (dadeInd1CoherentSum H nuTop))
          (eta j) = 0 := by
        dsimp only [dadeInd1CoherentSum]
        rw [map_sum, typeIParity_starPairing_finset_sum_left]
        apply Finset.sum_eq_zero
        intro psi hpsi
        have hpsiFamily : psi ∈ FTType1SeqIndFamily L := by
          simpa only [H, FTType1SeqIndFamily] using hpsi
        have hpsiFamilySet : psi ∈
            (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)) := by
          simpa only [Finset.mem_coe] using hpsiFamily
        have htauFamily : tau₁ psi ∈
            tau₁ ''
              (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)) :=
          ⟨psi, hpsiFamilySet, rfl⟩
        have hetaFamily : eta j ∈
            (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)) := by
          rw [Finset.mem_coe]
          exact supportBridges_eta_mem_cyclicImageFamily ctx
            IrreducibleCharacter.trivial j
        have hp : characterPairing (tau₁ psi) (eta j) = 0 :=
          horth (tau₁ psi) htauFamily (eta j) hetaFamily
        have hpStar : starCharacterPairing (tau₁ psi) (eta j) = 0 :=
          (PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
            (cohL.mapsToVirtual psi
              (AddSubgroup.subset_closure hpsiFamilySet))
            (supportBridges_eta_isVirtual ctx
              IrreducibleCharacter.trivial j)).trans hp
        rw [map_smul, starCharacterPairing_smul_left]
        simp only [nuTop, LinearMap.comp_apply,
          typeIBridgeTarget_source, hpStar, mul_zero]
      have hetaOneStar : starCharacterPairing (eta j) oneG = 0 := by
        simpa only [eta, oneG, typeIBridge_one_eq_trivial] using
          supportBridges_eta_one_orthogonal ctx
            IrreducibleCharacter.trivial j hj0
      have honeEta : starCharacterPairing oneG (eta j) = 0 := by
        calc
          starCharacterPairing oneG (eta j) =
              star (starCharacterPairing (eta j) oneG) :=
            starCharacterPairing_conj_symm oneG (eta j)
          _ = 0 := by rw [hetaOneStar]; simp
      have hnuEta : starCharacterPairing (tau₁ phi) (eta j) = 0 := by
        rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          htauPhiVirtual
          (supportBridges_eta_isVirtual ctx IrreducibleCharacter.trivial j)]
        exact horth (tau₁ phi) ⟨phi, Lphi, rfl⟩ (eta j)
          (by
            rw [Finset.mem_coe]
            exact supportBridges_eta_mem_cyclicImageFamily ctx
              IrreducibleCharacter.trivial j)
      have hbetaEtaStar : starCharacterPairing betaL (eta j) = (b : ℂ) := by
        rw [PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
          hbetaLVirtual
          (supportBridges_eta_isVirtual ctx IrreducibleCharacter.trivial j),
          hbetaEta, hbOdd]
      have hdecomp : betaL =
          oneG - tau₁ phi +
            (data.coefficient : ℂ) •
              typeIBridgeTargetMap (dadeInd1CoherentSum H nuTop) + gamma := by
        change typeIBridgeTargetMap betaTop =
          typeIBridgeTargetMap
            (oneTop - nuTop phi +
              (data.coefficient : ℂ) •
                dadeInd1CoherentSum H nuTop + data.gamma) at hdecompAmbient
        rw [hbetaAdapter, map_add, map_add, map_sub, map_smul,
          htargetOne] at hdecompAmbient
        simpa only [nuTop, LinearMap.comp_apply,
          typeIBridgeTarget_source, gamma] using hdecompAmbient
      rw [hdecomp] at hbetaEtaStar
      rw [starCharacterPairing_add_left,
        starCharacterPairing_add_left,
        supportBridges_starPairing_sub_left,
        honeEta, hnuEta, sub_self,
        starCharacterPairing_smul_left, hsumEta,
        mul_zero] at hbetaEtaStar
      simpa only [zero_add] using hbetaEtaStar
    have hprojection := typeIParity_weighted_projection_le_norm J eta
      (fun _ ↦ (b : ℂ)) gamma hetaOrtho hgammaPair
    have hbNorm : 1 ≤ Complex.normSq (b : ℂ) :=
      typeIParity_one_le_normSq_intCast b hbNe
    have hcardJ : J.card = Nat.card W₂ - 1 := by
      letI : IsCyclic W₂ := ctx.primeTI.fixed_cyclic
      dsimp only [J]
      rw [Finset.card_erase_of_mem (Finset.mem_univ _),
        Finset.card_univ,
        IrreducibleCharacter.card_eq_natCard_of_isCyclic]
    have hreal : ((Nat.card W₂ - 1 : ℕ) : ℝ) ≤
        (FTtype1CoreIndex L : ℝ) - 1 := by
      calc
        ((Nat.card W₂ - 1 : ℕ) : ℝ) = (J.card : ℝ) := by
          rw [hcardJ]
        _ ≤ ∑ j ∈ J, Complex.normSq (b : ℂ) := by
          simp only [Finset.sum_const, nsmul_eq_mul]
          exact le_mul_of_one_le_right (Nat.cast_nonneg J.card) hbNorm
        _ ≤ classFunctionNormSq gamma := hprojection
        _ ≤ (FTtype1CoreIndex L : ℝ) - 1 := hgammaUpper
    have hreal' : (Nat.card W₂ : ℝ) - 1 ≤
        (FTtype1CoreIndex L : ℝ) - 1 := by
      calc
        (Nat.card W₂ : ℝ) - 1 =
            ((Nat.card W₂ - 1 : ℕ) : ℝ) := by
          rw [Nat.cast_sub (Nat.card_pos (α := W₂)), Nat.cast_one]
        _ ≤ (FTtype1CoreIndex L : ℝ) - 1 := hreal
    have hcast : (Nat.card W₂ : ℝ) ≤
        (FTtype1CoreIndex L : ℝ) :=
      (sub_le_sub_iff_right (1 : ℝ)).mp hreal'
    exact_mod_cast hcast

private theorem typeICleanAssembly_fragment
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1)
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (phi : ClassFunction L ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁)
    (Lphi : phi ∈ FTType1SeqIndFamily L)
    (phi1e : phi 1 = ((FTtype1CoreIndex L : ℕ) : ℂ)) :
    Disjoint (FT_Dade_full_support L)
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G)) ∧
    orthogonalFamilies
      (tau₁ ''
        (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)))
      (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)) ∧
    (∀ j, j ≠ IrreducibleCharacter.trivial →
      characterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial j) =
        characterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial
            (FTtypePBridgeIndex ctx))) ∧
    ((oddCharacterPairing
        (ctx.tau
          (FTtypeP_bridge ctx (FTtypePBridgeIndex ctx)))
        (tau₁ phi) ∧
      (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
          (FTtype1CoreIndex L : ℝ) ≤
        (((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ))) ∨
      (oddCharacterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial
            (FTtypePBridgeIndex ctx)) ∧
        Nat.card W₂ ≤ FTtype1CoreIndex L)) := by
  have hab := typeIBridge_first_two_facts
    ctx L maxL Ltype1 tau₁ cohL
  have hc := typeIConstantEta_fragment
    ctx L maxL phi hab.1 (FTtypeP_bridge_facts ctx)
  have hd := typeIParity_final_disjunction
    ctx L maxL Ltype1 tau₁ phi cohL Lphi phi1e
      hab.1 hab.2 hc
  exact ⟨hab.1, hab.2, hc, hd⟩

/-- `PFsection13.v: FTtypeI_bridge_facts`, Peterfalvi (13.19). -/
theorem FTtypeI_bridge_facts
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (L : Subgroup G)
    (maxL : L ∈ minSimple_max_groups (G := G))
    (Ltype1 : FTtype L = 1)
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (phi : ClassFunction L ℂ)
    (cohL : coherent_with
      (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (FTtype1Dade L maxL) tau₁)
    (Lphi : phi ∈ FTType1SeqIndFamily L)
    (phi1e : phi 1 = ((FTtype1CoreIndex L : ℕ) : ℂ)) :
    Disjoint (FT_Dade_full_support L)
      (classSupportWithin (⊤ : Subgroup G)
          (Fitting_core S : Set G) ∪
        classSupportWithin (⊤ : Subgroup G) (W : Set G)) ∧
    orthogonalFamilies
      (tau₁ ''
        (↑(FTType1SeqIndFamily L) : Set (ClassFunction L ℂ)))
      (↑(FTtypePCyclicImageFamily ctx) : Set (ClassFunction G ℂ)) ∧
    (∀ j, j ≠ IrreducibleCharacter.trivial →
      characterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial j) =
        characterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial
            (FTtypePBridgeIndex ctx))) ∧
    ((oddCharacterPairing
        (ctx.tau
          (FTtypeP_bridge ctx (FTtypePBridgeIndex ctx)))
        (tau₁ phi) ∧
      (((Nat.card (Fitting_core L) - 1 : ℕ) : ℝ) /
          (FTtype1CoreIndex L : ℝ) ≤
        (((Nat.card U - 1) / Nat.card W₁ : ℕ) : ℝ))) ∨
      (oddCharacterPairing
          (FTtype1Dade L maxL (FTtype1Bridge L phi))
          (ctx.eta IrreducibleCharacter.trivial
            (FTtypePBridgeIndex ctx)) ∧
        Nat.card W₂ ≤ FTtype1CoreIndex L)) := by
  exact typeICleanAssembly_fragment
    ctx L maxL Ltype1 tau₁ phi cohL Lphi phi1e

end

end Submission.OddOrder.PF
