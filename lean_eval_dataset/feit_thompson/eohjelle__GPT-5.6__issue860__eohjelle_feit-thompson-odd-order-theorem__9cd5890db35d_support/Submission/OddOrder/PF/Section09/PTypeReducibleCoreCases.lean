import Submission.OddOrder.PF.Section09.PTypeGaloisConclusion
import Submission.OddOrder.PF.Section09.PTypeNonGaloisConclusion

/-!
# Peterfalvi Section 9: convergence of the reducible-core cases

This module combines the Galois and non-Galois character conclusions.  It
exports the common reducible layer used downstream and the constructive
alternative of Peterfalvi (9.10).
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical IsMulCommutative Pointwise

noncomputable section

universe u

namespace PTypeReducibleCoreCasesInternal

open PTypeGaloisCharacterArithmeticInternal
open PTypeGaloisSubgroupAdaptersInternal
open internal

private theorem isIndHC_of_smaller_kernel
    {M : Type u} [Group M] [Fintype M]
    (HU : Subgroup M) (H A B : Subgroup HU) (HC : Subgroup M)
    {q actionCard : ℕ} {zeta : ClassFunction M ℂ}
    (hBA : B ≤ A)
    (hzeta : pTypeIsIndHC HU H A HC q actionCard zeta) :
    pTypeIsIndHC HU H B HC q actionCard zeta := by
  rcases hzeta with ⟨hdegree, hmember, xi, hlinear, hinduced⟩
  refine ⟨hdegree, ?_, xi, hlinear, hinduced⟩
  exact seqIndS HU
    (Iirr_kerDS (k := ℂ) (A₁ := A) (A₂ := B)
      (B₁ := H) (B₂ := H) hBA le_rfl) hmember

private theorem coreInduced_to_ambient
    {M : Type u} [Group M] [Fintype M]
    (HU HC : Subgroup M) (hHC : HC ≤ HU) (actionCard : ℕ)
    (s : IrreducibleCharacter HU ℂ)
    (hs : PTypeCoreInduced (HC.subgroupOf HU) actionCard s) :
    ∃ xi : IrreducibleCharacter HC ℂ,
      pTypeIsLinearCharacter xi ∧
        ClassFunction.induce HU (s : ClassFunction HU ℂ) =
          ClassFunction.induce HC (xi : ClassFunction HC ℂ) := by
  rcases hs with ⟨_, theta, hthetaLinear, hsInduced⟩
  let e : HC.subgroupOf HU ≃* HC :=
    Subgroup.subgroupOfEquivOfLe hHC
  let xi : IrreducibleCharacter HC ℂ :=
    pTypeGaloisComapMulEquiv e.symm theta
  have hxiLinear : pTypeIsLinearCharacter xi :=
    pTypeIsLinearCharacter_comapMulEquiv e.symm theta hthetaLinear
  have htransport :
      ClassFunction.toSubgroupOf HC HU hHC (xi : ClassFunction HC ℂ) =
        (theta : ClassFunction (HC.subgroupOf HU) ℂ) := by
    ext x
    simp [ClassFunction.toSubgroupOf_apply, xi, e,
      pTypeGaloisComapMulEquiv_apply]
  refine ⟨xi, hxiLinear, ?_⟩
  calc
    ClassFunction.induce HU (s : ClassFunction HU ℂ) =
        ClassFunction.induce HU
          (ClassFunction.induce (HC.subgroupOf HU)
            (theta : ClassFunction (HC.subgroupOf HU) ℂ)) := by
      rw [hsInduced]
    _ = ClassFunction.induce HU
        (ClassFunction.induce (HC.subgroupOf HU)
          (ClassFunction.toSubgroupOf HC HU hHC
            (xi : ClassFunction HC ℂ))) := by
      rw [htransport]
    _ = ClassFunction.induce HC (xi : ClassFunction HC ℂ) :=
      ClassFunction.induce_trans HC HU hHC _

private theorem frobenius_map_equiv
    {A B : Type u} [Group A] [Finite A] [Group B] [Finite B]
    {K C : Subgroup A}
    (h : IsFrobeniusDecomposition K C) (e : A ≃* B) :
    IsFrobeniusDecomposition
      (K.map e.toMonoidHom) (C.map e.toMonoidHom) := by
  refine
    { isComplement := pTypeIsComplement_map_mulEquiv h.isComplement e
      kernel_normal := Subgroup.Normal.map h.kernel_normal
        e.toMonoidHom e.surjective
      kernel_ne_bot := (not_congr
        (Subgroup.map_eq_bot_iff_of_injective K e.injective)).mpr
          h.kernel_ne_bot
      complement_ne_bot := (not_congr
        (Subgroup.map_eq_bot_iff_of_injective C e.injective)).mpr
          h.complement_ne_bot
      fixedPointFree := ?_ }
  intro c hc k hfix
  let c₀ : C := (e.subgroupMap C).symm c
  let k₀ : K := (e.subgroupMap K).symm k
  have hc₀ : c₀ ≠ 1 := by
    intro hcOne
    apply hc
    simpa [c₀] using congrArg (e.subgroupMap C) hcOne
  have hfix₀ : (c₀ : A) * (k₀ : A) * (c₀ : A)⁻¹ = k₀ := by
    apply e.injective
    simpa [c₀, k₀] using hfix
  have hk₀ := h.fixedPointFree c₀ hc₀ k₀ hfix₀
  simpa [k₀] using congrArg (e.subgroupMap K) hk₀

private theorem typeII_full_frobenius
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (hGal : typeP_Galois (Ptype_factor_action ctx facts))
    (hC : (Ptype_factor_action ctx facts).C = ⊥) :
    FTtype M = 2 →
      IsFrobeniusDecomposition
        (pTypeHInDerived M (derivedWithin M) (Fitting_core M))
        (pTypeUInDerived M (derivedWithin M) U) := by
  intro htype
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  letI : IsCyclic U :=
    pTypeGalois_complement_cyclic_of_C_eq_bot hD hGal hC
  have htypeII : of_typeII M U W W₁ W₂ ctx.defW :=
    compl_of_typeII M U W W₁ W₂ ctx.defW
      ctx.maxM ctx.typeP htype
  have htypeF : of_typeF (derivedWithin M) U :=
    htypeII.2.2.2.1
  have hZ : IsZGroup8 U := by
    intro p hp P
    exact Subgroup.isCyclic_of_le le_top
  have hFrobIn :
      IsFrobeniusIn (Fitting_core (derivedWithin M)) U
        (derivedWithin M) :=
    (typeF_context (derivedWithin M) U htypeF).frobenius_iff_zgroup.mpr hZ
  have hcore : Fitting_core (derivedWithin M) = Fitting_core M :=
    htypeII.2.2.2.2
  have hFrobDerived := hFrobIn.2.2
  rw [hFrobIn.1, hcore] at hFrobDerived
  have houter : IsInternalSemidirectProductIn
      (derivedWithin M) W₁ M := ctx.typeP.1.2.2.2
  let eHU : pTypeHUInMaximal M (derivedWithin M) ≃*
      derivedWithin M :=
    Subgroup.subgroupOfEquivOfLe houter.1
  have hmapped := frobenius_map_equiv hFrobDerived eHU.symm
  have hmapH :
      ((Fitting_core M).subgroupOf (derivedWithin M)).map
          eHU.symm.toMonoidHom =
        pTypeHInDerived M (derivedWithin M) (Fitting_core M) := by
    ext x
    constructor
    · rintro ⟨h, hh, rfl⟩
      exact hh
    · intro hx
      let h : (Fitting_core M).subgroupOf (derivedWithin M) :=
        ⟨eHU x, hx⟩
      exact ⟨h, h.property, by
        apply Subtype.ext
        rfl⟩
  have hmapU :
      (U.subgroupOf (derivedWithin M)).map eHU.symm.toMonoidHom =
        pTypeUInDerived M (derivedWithin M) U := by
    ext x
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact hv
    · intro hx
      let v : U.subgroupOf (derivedWithin M) := ⟨eHU x, hx⟩
      exact ⟨v, v.property, by
        apply Subtype.ext
        rfl⟩
  simpa only [hmapH, hmapU] using hmapped

end PTypeReducibleCoreCasesInternal

open PTypeReducibleCoreCasesInternal
open PTypeGaloisSubgroupAdaptersInternal

/-- The common reducible-character conclusion of Peterfalvi (9.8)(b) and
(9.9)(b). -/
theorem typeP_reducible_core_Ind
    {Gamma : Type} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    (M U W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (maxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype5 : FTtype M ≠ 5) :
    let ctx := Ptype_Fcore_context maxM defW MtypeP notMtype5
    let facts := Ptype_Fcore_factor_facts ctx
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HCInM := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let pti := FT_primeTI_hyp defW MtypeP
    let iso := pti.prime_cycTIhyp.cyclicTIIsometryData (k := ℂ)
    let mu := pTypeReducibleLayer HU H H₀
    mu.card = D.p - 1 ∧ mu.Nonempty ∧
      mu ⊆ Finset.image (pti.primeTIRed iso)
        (Finset.univ.erase
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) ∧
      ∀ zeta ∈ mu,
        pTypeIsIndHC HU H H₀C HCInM D.q
          (pTypeActionFactorCard D) zeta := by
  classical
  let ctx := Ptype_Fcore_context maxM defW MtypeP notMtype5
  let facts := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HCInM := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let pti := FT_primeTI_hyp defW MtypeP
  let iso := pti.prime_cycTIhyp.cyclicTIIsometryData (k := ℂ)
  let mu := pTypeReducibleLayer HU H H₀
  change mu.card = D.p - 1 ∧ mu.Nonempty ∧
    mu ⊆ Finset.image (pti.primeTIRed iso)
      (Finset.univ.erase
        (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) ∧
    ∀ zeta ∈ mu,
      pTypeIsIndHC HU H H₀C HCInM D.q
        (pTypeActionFactorCard D) zeta
  have hbranch : mu.card = D.p - 1 ∧
      ∀ zeta ∈ mu,
        pTypeIsIndHC HU H H₀C HCInM D.q
          (pTypeActionFactorCard D) zeta := by
    by_cases hGal : typeP_Galois D
    · have hcount := pType_nb_redM_H0 ctx facts
      have hGalois := typeP_Galois_characters M U W W₁ W₂
        defW maxM MtypeP notMtype5 hGal
      exact ⟨hcount.1, hGalois.2.1.2⟩
    · have hNonGalois := typeP_nonGalois_characters ctx hGal
      exact ⟨hNonGalois.reducible_layer_card,
        hNonGalois.reducible_layer_induced⟩
  have hnonempty : mu.Nonempty :=
    PTypeGaloisCharacterArithmeticInternal.reducibleLayer_nonempty_of_card_eq_prime_pred
      HU H H₀ D.p_prime hbranch.1
  have hcover :
      mu ⊆ Finset.image (pti.primeTIRed iso)
        (Finset.univ.erase
          (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)) :=
    PTypeGaloisCharacterArithmeticInternal.reducibleLayer_subset_primeTIRed
      defW MtypeP H₀
  exact ⟨hbranch.1, hnonempty, hcover, hbranch.2⟩

/-- Peterfalvi (9.10), in constructive-alternative form. -/
theorem typeP_reducible_core_cases
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    (M U W W₁ W₂ : Subgroup Gamma)
    (defW : IsInternalDirectProductIn W₁ W₂ W)
    (maxM : M ∈ minSimple_max_groups (G := Gamma))
    (MtypeP : of_typeP M U W W₁ W₂ defW)
    (notMtype5 : FTtype M ≠ 5) :
    let ctx := Ptype_Fcore_context maxM defW MtypeP notMtype5
    let facts := Ptype_Fcore_factor_facts ctx
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HCInM := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let UHU := pTypeUInDerived M (derivedWithin M) U
    let actionCard := pTypeActionFactorCard D
    letI : H₀.Normal := pTypeH0InDerived_normal ctx
    (∃ chi : IrreducibleCharacter M ℂ,
      (chi : ClassFunction M ℂ) ∈
          seqIndD (k := ℂ) HU H H₀CPrime ∧
        chi 1 = ((D.q * actionCard : ℕ) : ℂ) ∧
        ∃ xi : IrreducibleCharacter HCInM ℂ,
          pTypeIsLinearCharacter xi ∧
            (chi : ClassFunction M ℂ) =
              ClassFunction.induce HCInM
                (xi : ClassFunction HCInM ℂ)) ∨
    (typeP_Galois D ∧
      IsFrobeniusDecomposition
        (ptypeQuotientImage H₀ H)
        (ptypeQuotientImage H₀ UHU) ∧
      IsCyclic U ∧ Nat.card U = (D.p ^ D.q - 1) / (D.p - 1) ∧
      (FTtype M = 2 → IsFrobeniusDecomposition H UHU)) := by
  classical
  let ctx := Ptype_Fcore_context maxM defW MtypeP notMtype5
  let facts := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  let HCInM := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let UHU := pTypeUInDerived M (derivedWithin M) U
  let actionCard := pTypeActionFactorCard D
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  change
    (∃ chi : IrreducibleCharacter M ℂ,
      (chi : ClassFunction M ℂ) ∈
          seqIndD (k := ℂ) HU H H₀CPrime ∧
        chi 1 = ((D.q * actionCard : ℕ) : ℂ) ∧
        ∃ xi : IrreducibleCharacter HCInM ℂ,
          pTypeIsLinearCharacter xi ∧
            (chi : ClassFunction M ℂ) =
              ClassFunction.induce HCInM
                (xi : ClassFunction HCInM ℂ)) ∨
    (typeP_Galois D ∧
      IsFrobeniusDecomposition
        (ptypeQuotientImage H₀ H)
        (ptypeQuotientImage H₀ UHU) ∧
      IsCyclic U ∧ Nat.card U = (D.p ^ D.q - 1) / (D.p - 1) ∧
      (FTtype M = 2 → IsFrobeniusDecomposition H UHU))
  by_cases hGal : typeP_Galois D
  · have hGalois := typeP_Galois_characters M U W W₁ W₂
      defW maxM MtypeP notMtype5 hGal
    by_cases hAllReducible :
        ∀ zeta ∈ seqIndD (k := ℂ) HU H H₀CPrime,
          ¬ IsIrreducibleCharacter M ℂ zeta
    · rcases hGalois.2.2 hAllReducible with ⟨hC, haction, hFrob⟩
      have hDC : D.C = ⊥ :=
        (pTypeCInDerived_eq_bot_iff ctx D).mp hC
      have hcyclic : IsCyclic U :=
        pTypeGalois_complement_cyclic_of_C_eq_bot hD hGal hDC
      have hcard : actionCard = Nat.card U :=
        pTypeActionFactorCard_eq_card_of_C_eq_bot D hDC
      exact Or.inr ⟨hGal, hFrob, hcyclic,
        hcard.symm.trans haction,
        typeII_full_frobenius ctx facts hGal hDC⟩
    · push Not at hAllReducible
      obtain ⟨zeta, hzeta, hzetaIrr⟩ := hAllReducible
      obtain ⟨s, hs, hzetaEq⟩ := seqIndP.mp hzeta
      have hcore : PTypeCoreInduced HC actionCard s :=
        hGalois.1.2 s hs
      have hHCle : HCInM ≤ HU := pTypeHCInMaximal_le_HU ctx D
      have hHCeq : HC = HCInM.subgroupOf HU :=
        pTypeHCInDerived_eq_subgroupOf ctx D
      have hcoreNested :
          PTypeCoreInduced (HCInM.subgroupOf HU) actionCard s := by
        rw [← hHCeq]
        exact hcore
      obtain ⟨xi, hxiLinear, hInduced⟩ :=
        coreInduced_to_ambient HU HCInM hHCle actionCard s hcoreNested
      let chi : IrreducibleCharacter M ℂ := ⟨zeta, hzetaIrr⟩
      refine Or.inl ⟨chi, hzeta, ?_, xi, hxiLinear, ?_⟩
      · change zeta 1 = ((D.q * actionCard : ℕ) : ℂ)
        calc
          zeta 1 = ClassFunction.induce HU
              (s : ClassFunction HU ℂ) 1 := by rw [hzetaEq]
          _ = (HU.index : ℂ) * s 1 :=
            ClassFunction.induce_one HU _
          _ = (D.q : ℂ) * (actionCard : ℂ) := by
            rw [pTypeHUInMaximal_index_eq_action_q ctx facts,
              hcore.1]
          _ = ((D.q * actionCard : ℕ) : ℂ) := by norm_num
      · change zeta = ClassFunction.induce HCInM
          (xi : ClassFunction HCInM ℂ)
        exact hzetaEq.trans hInduced
  · have hNonGalois := typeP_nonGalois_characters ctx hGal
    obtain ⟨chi, hchi⟩ := hNonGalois.exists_induced_irreducible
    have hkernel : H₀CPrime ≤ H₀C :=
      pTypeH0CPrimeInDerived_le_H0CInDerived
        M (derivedWithin M) (Ptype_Fcore_kernel ctx) U W₁ D
    have hchiPrime :
        pTypeIsIndHC HU H H₀CPrime HCInM D.q actionCard
          (chi : ClassFunction M ℂ) :=
      isIndHC_of_smaller_kernel HU H H₀C H₀CPrime HCInM
        hkernel hchi
    exact Or.inl ⟨chi, hchiPrime.2.1, hchiPrime.1,
      hchiPrime.2.2⟩

end

end Submission.OddOrder.PF
