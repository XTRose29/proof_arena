import Submission.OddOrder.PF.Section09.PTypeCoreGamma

/-!
# Peterfalvi Section 9: support and orthogonality in the rigid branch

This module proves the support half of Peterfalvi (9.11.4).  The selected
quotient-regular character is supported on the prime-Dade support, while the
kernel-layer characters are supplied by the Section 8 prime-Dade theorem.
It also records the orthogonality statements used by the subsequent pairing
calculation.

The narrow downstream interface is in `PTypeCoreSupportInternal`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section16
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open PTypeCoreBoundsInternal
open PTypeCoreActionKernelInternal
open PTypeCoreGammaInternal
open PTypeNonGaloisSelectedCoordinateInternal
open PTypeNonGaloisInertiaCoreInternal
open scoped BigOperators Classical

universe u

namespace PTypeCoreSupportInternal

local instance subgroupCoeTCToAmbient
    {A : Type u} [Group A] (S : Subgroup A) : CoeTC S A :=
  ⟨fun x ↦ x.1⟩

local instance subgroupOfCoeTCToAmbient
    {A : Type u} [Group A] (S T : Subgroup A) :
    CoeTC (S.subgroupOf T) A :=
  ⟨fun x ↦ x.1.1⟩

local instance invertibleNatCardComplex
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## The selected inertia subgroup lies in the Dade support -/

/-- A nonidentity derived element centralizing a nonidentity Fitting-core
element belongs to the canonical Type-P support. -/
private theorem mem_FTsupport_of_commutes_with_fitting
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (x : M) (hxDerived : (x : G) ∈ derivedWithin M) (hx : x ≠ 1)
    (h : Fitting_core M) (hh : h ≠ 1)
    (hxh : Commute (x : G) (h : G)) :
    (x : G) ∈ FTsupport M := by
  have hxG : (x : G) ≠ 1 := fun hx1 ↦ hx (Subtype.ext hx1)
  have hhG : (h : G) ≠ 1 := fun hh1 ↦ hh (Subtype.ext hh1)
  exact (FT_prDade_hypF ctx.defW ctx.maxM ctx.typeP).prDade_def
    |>.centralizerSupport_le
      ⟨hxDerived, hxG, (h : G), h.property, hhG, hxh⟩

/-- Every element of the selected inertia pullback is either the identity or
belongs to the Type-P support. -/
private theorem selectedInertia_le_primeDadeSupport
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let HU := pTypeCoreDerived M
    let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
    ∀ t : HU, t ∈ T →
      ((t : HU) : M) ∈ primeDadeSupport M (FTsupport M) := by
  classical
  dsimp only
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let UHU := (U.subgroupOf M).subgroupOf HU
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let K := pointwiseActionKernel D.U_action data.H₁
  let projection : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let V := UHU ⊓ T
  let HT := H.subgroupOf T
  let VT := V.subgroupOf T
  have hDerivedM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hHDerived : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUDerived : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUDerived.trans hDerivedM
  have hHMHU : (Fitting_core M).subgroupOf M ≤ HU := by
    intro h hh
    exact hHDerived hh
  have hUHU : U.subgroupOf M ≤ HU := by
    intro x hx
    exact hUDerived hx
  have hHUdecomp : H.IsComplement' UHU := by
    simpa only [H, UHU] using pTypeCoreH_isComplement_U ctx
  have hHT : H ≤ T := by
    intro h hh
    change projection h ∈ K
    have hhker : h ∈ (pTypeNonGaloisHUToUProjection ctx).ker := by
      rw [pTypeNonGaloisHUToUProjection_ker ctx]
      exact hh
    rw [MonoidHom.mem_ker.mp hhker]
    exact K.one_mem
  have hTdecomp : HT.IsComplement' VT := by
    simpa only [HT, VT, V] using
      pTypeCore_isComplement_subgroupOf_of_left_le hHUdecomp hHT
  letI : H.Normal :=
    Subgroup.Normal.subgroupOf (Fcore_normal M) HU
  letI : HT.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : H.Normal) T
  have hcardH : Nat.card H = Nat.card (Fitting_core M) := by
    rw [natCard_subgroupOf_eq
        hHMHU,
      natCard_subgroupOf_eq (Fcore_sub M)]
  have hcardUHU : Nat.card UHU = Nat.card U := by
    rw [natCard_subgroupOf_eq
        hUHU,
      natCard_subgroupOf_eq hUM]
  have hVcard : Nat.card V ∣ Nat.card U := by
    rw [← hcardUHU]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcoprimeHU :
      Nat.Coprime (Nat.card (Fitting_core M)) (Nat.card U) :=
    (Ptype_Fcore_coprime ctx).coprime_dvd_right
      (Subgroup.card_dvd_of_le le_sup_left)
  have hcoprimeTV : Nat.Coprime (Nat.card HT) (Nat.card VT) := by
    rw [natCard_subgroupOf_eq hHT,
      natCard_subgroupOf_eq (show V ≤ T from inf_le_right), hcardH]
    exact hcoprimeHU.coprime_dvd_right hVcard
  have hHallH : IsHall (primeSupport (Nat.card HT)) HT := by
    apply isHall_primeSupport
    rw [hTdecomp.symm.index_eq_card]
    exact hcoprimeTV
  let primeSet := primeSupport (Nat.card HT)
  have hHallV : IsHall primeSetᶜ VT := by
    constructor
    · rw [← hTdecomp.symm.index_eq_card]
      exact hHallH.isPiNumber_index
    · simpa only [compl_compl, hTdecomp.index_eq_card] using
        hHallH.isPiNumber_card
  letI : IsSolvable M := mmax_sol ctx.maxM
  letI : IsSolvable HU := isSolvable_subgroup_of_isSolvable HU
  letI : IsSolvable T := isSolvable_subgroup_of_isSolvable T
  intro t ht
  by_cases htOne : t = 1
  · left
    rw [htOne]
    rfl
  right
  let y : T := ⟨t, ht⟩
  have hyOne : y ≠ 1 := fun hy ↦ htOne (congrArg Subtype.val hy)
  let tM : M := (t : HU)
  have htMOne : tM ≠ 1 := fun htM ↦ htOne (Subtype.ext htM)
  have htDerived : (tM : G) ∈ derivedWithin M := t.property
  by_cases hyPi : IsPiNumber primeSetᶜ (orderOf y)
  · let A : Subgroup T := Subgroup.zpowers y
    have hApi : IsPiNumber primeSetᶜ (Nat.card A) := by
      simpa only [A, Nat.card_zpowers] using hyPi
    obtain ⟨C, hCdecomp, hAC⟩ :=
      exists_right_complement_ge_of_coprime
        (N := HT) (A := A) hHallH.coprime_card_index
          (hHallH.isPiNumber_card.coprime_compl hApi)
    obtain ⟨n, hn⟩ :=
      Subgroup.solvable_complement_conjugacy
        hHallH.coprime_card_index hTdecomp hCdecomp
    have hyC : y ∈ C := hAC (Subgroup.mem_zpowers y)
    rw [hn] at hyC
    rcases hyC with ⟨v, hvVT, hvy⟩
    let vT : T := n⁻¹ * y * n
    have hvEq : vT = (v : T) := by
      dsimp only [vT]
      rw [← hvy]
      change (n : T)⁻¹ * ((n : T) * v * (n : T)⁻¹) * (n : T) = v
      group
    have hvMem : vT ∈ VT := by
      rw [hvEq]
      exact hvVT
    have hvOne : vT ≠ 1 := by
      intro hv
      apply hyOne
      calc
        y = n * vT * n⁻¹ := by dsimp [vT]; group
        _ = 1 := by rw [hv]; simp
    let vHU : HU := (vT : T)
    have hvUHU : vHU ∈ UHU := hvMem.1
    let u : U := ⟨((vHU : HU) : M), hvUHU⟩
    let vUHU : UHU := ⟨vHU, hvUHU⟩
    have hprojection : projection vHU = u := by
      simpa only [projection, vUHU, u] using
        pTypeNonGaloisHUToUProjection_apply_complement ctx vUHU
    have huK : u ∈ K := by
      rw [← hprojection]
      exact vT.property
    have hH₁card : 1 < Nat.card data.H₁ := by
      rw [data.card_H₁]
      exact D.p_prime.one_lt
    letI : Nontrivial data.H₁ :=
      Finite.one_lt_card_iff_nontrivial.mp hH₁card
    obtain ⟨z : data.H₁, hzOne⟩ := exists_ne (1 : data.H₁)
    let H₀H := (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)
    let qH : Fitting_core M →* ptypeFCoreFactor ctx :=
      QuotientGroup.mk' H₀H
    obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective H₀H
      (z : ptypeFCoreFactor ctx)
    have hfixed :=
      (mem_pointwiseActionKernel_iff D.U_action data.H₁ u).mp huK
        (z : ptypeFCoreFactor ctx) z.property
    rw [← hh] at hfixed
    change ptypeFCoreAction ctx u (qH h) = qH h at hfixed
    rw [ptypeFCoreAction, subgroupConjugationFactorHom_apply_mk] at hfixed
    let HM : Subgroup M := (Fitting_core M).subgroupOf M
    let NM : Subgroup M := (Ptype_Fcore_kernel ctx).subgroupOf M
    let vM : M := (vHU : HU)
    let RM : Subgroup M := Subgroup.zpowers vM
    letI : NM.Normal := Ptype_Fcore_kernel_normal_M ctx
    let qM : M →* M ⧸ NM := QuotientGroup.mk' NM
    let hM : M := ⟨(h : G), Fcore_sub M h.property⟩
    have hNMHM : NM ≤ HM :=
      Subgroup.subgroupOf_mono M (Ptype_Fcore_kernel_lt ctx).le
    letI : IsSolvable RM :=
      _root_.isSolvable_of_comm (fun a b ↦ mul_comm' a b)
    have hRMcard : Nat.card RM ∣ Nat.card U := by
      let UM : Subgroup M := U.subgroupOf M
      have hRMUM : RM ≤ UM := by
        apply Subgroup.zpowers_le.mpr
        exact hvUHU
      have hdvd := Subgroup.card_dvd_of_le hRMUM
      simpa only [UM, natCard_subgroupOf_eq hUM] using hdvd
    have hcoprimeAmbient :
        Nat.Coprime (Nat.card (Ptype_Fcore_kernel ctx))
          (Nat.card RM) :=
      ((Ptype_Fcore_coprime ctx).coprime_dvd_left
        (Subgroup.card_dvd_of_le (Ptype_Fcore_kernel_lt ctx).le))
          |>.coprime_dvd_right
            (hRMcard.trans (Subgroup.card_dvd_of_le le_sup_left))
    have hcoprime : Nat.Coprime (Nat.card NM) (Nat.card RM) := by
      simpa only [NM,
        natCard_subgroupOf_eq (Ptype_Fcore_kernel_le_M ctx)] using
          hcoprimeAmbient
    have hconjQuotient : qM (vM * hM * vM⁻¹) = qM hM := by
      apply QuotientGroup.eq.mpr
      have hdiff := QuotientGroup.eq.mp hfixed
      change
        (((vM * hM * vM⁻¹)⁻¹ * hM : M) : G) ∈
          Ptype_Fcore_kernel ctx
      change
        ((⟨(u : G) * (h : G) * (u : G)⁻¹,
            (Fcore_normal M).conj_mem
              (⟨(h : G), Fcore_sub M h.property⟩ : M) h.property
              (⟨(u : G), hUM u.property⟩ : M)⟩ :
              Fitting_core M)⁻¹ * h : Fitting_core M) ∈ H₀H at hdiff
      change
        (((u : G) * (h : G) * (u : G)⁻¹)⁻¹ * (h : G)) ∈
          Ptype_Fcore_kernel ctx at hdiff
      change
        (((u : G) * (h : G) * (u : G)⁻¹)⁻¹ * (h : G)) ∈
          Ptype_Fcore_kernel ctx
      exact hdiff
    have hcommQuotient : Commute (qM vM) (qM hM) := by
      change qM vM * qM hM = qM hM * qM vM
      calc
        qM vM * qM hM =
            (qM vM * qM hM * (qM vM)⁻¹) * qM vM := by group
        _ = qM hM * qM vM := by
          rw [← map_inv, ← map_mul, ← map_mul, hconjQuotient]
    have hzCentralizer : qM hM ∈
        centralizerWithin (HM.map qM) (RM.map qM) := by
      refine ⟨⟨hM, h.property, rfl⟩, ?_⟩
      intro r hr
      rcases hr with ⟨rM, hrRM, rfl⟩
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hrRM
      change Commute (qM vM ^ j) (qM hM)
      exact hcommQuotient.zpow_left j
    have hmapCentralizer :=
      map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := NM) (Y := HM) (R := RM) hNMHM hcoprime
    rw [← hmapCentralizer] at hzCentralizer
    rcases hzCentralizer with ⟨cM, hcM, hqc⟩
    let c : Fitting_core M := ⟨((cM : M) : G), hcM.1⟩
    have hcOne : c ≠ 1 := by
      intro hc
      have hqC : qM cM = 1 := by
        apply QuotientGroup.eq_one_iff cM |>.mpr
        change ((cM : M) : G) ∈ Ptype_Fcore_kernel ctx
        have hcG : (c : G) = 1 := congrArg Subtype.val hc
        have : (cM : M) = 1 :=
          Subtype.ext (by simpa only [c, Subgroup.coe_one] using hcG)
        rw [this]
        exact (Ptype_Fcore_kernel ctx).one_mem
      have hqH : qM hM = 1 := hqc.symm.trans hqC
      have hhH₀ : (h : G) ∈ Ptype_Fcore_kernel ctx :=
        QuotientGroup.eq_one_iff hM |>.mp hqH
      apply hzOne
      have hqH' : qH h = 1 := by
        apply QuotientGroup.eq_one_iff h |>.mpr
        exact hhH₀
      exact Subtype.ext (hh.symm.trans hqH')
    have hvMOne : vM ≠ 1 := fun hv ↦ hvOne (Subtype.ext (Subtype.ext hv))
    have hvDerived : (vM : G) ∈ derivedWithin M := vHU.property
    have hvComm : Commute (vM : G) (c : G) := by
      have hc := hcM.2 vM (Subgroup.mem_zpowers vM)
      exact congrArg Subtype.val hc
    have hvSupport : (vM : G) ∈ FTsupport M :=
      mem_FTsupport_of_commutes_with_fitting
        ctx vM hvDerived hvMOne c hcOne hvComm
    have hnNormalizer : ((((n : T) : HU) : M) : G) ∈
        Subgroup.normalizer (FTsupport M) :=
      FTsupp_norm M (((n : T) : HU) : M).property
    apply (Subgroup.mem_set_normalizer_iff''.mp hnNormalizer (tM : G)).mpr
    simpa [vM, vHU, vT, y, tM] using hvSupport
  · rw [IsPiNumber] at hyPi
    push Not at hyPi
    obtain ⟨p, hp, hpOrder, hpSet⟩ := hyPi
    have hpPrimeSet : p ∈ primeSet := by
      simpa only [Set.mem_compl_iff, not_not] using hpSet
    letI : Fact p.Prime := ⟨hp⟩
    let A : Subgroup T := Subgroup.zpowers y
    have hpA : p ∣ Nat.card A := by
      simpa only [A, Nat.card_zpowers] using hpOrder
    obtain ⟨x, hxOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := A) p hpA
    let xT : T := (x : A)
    have hxOrderT : orderOf xT = p :=
      (Subgroup.orderOf_coe x).trans hxOrder
    have hxOne : xT ≠ 1 := by
      intro hx
      rw [hx, orderOf_one] at hxOrderT
      exact hp.ne_one hxOrderT.symm
    have hpNotIndex : ¬ p ∣ HT.index := by
      intro hpIndex
      exact (hHallH.isPiNumber_index hp hpIndex) hpPrimeSet
    have hpCoprimeIndex : p.Coprime HT.index :=
      hp.coprime_iff_not_dvd.mpr hpNotIndex
    let quotientT : T →* T ⧸ HT := QuotientGroup.mk' HT
    have horderP : orderOf (quotientT xT) ∣ p := by
      exact (orderOf_map_dvd quotientT xT).trans (by rw [hxOrderT])
    have horderIndex : orderOf (quotientT xT) ∣ HT.index := by
      simpa only [HT.index_eq_card] using
        orderOf_dvd_natCard (quotientT xT)
    have horderOne : orderOf (quotientT xT) = 1 :=
      Nat.eq_one_of_dvd_coprimes
        hpCoprimeIndex horderP horderIndex
    have hquotientOne : quotientT xT = 1 :=
      orderOf_eq_one_iff.mp horderOne
    change (xT : T ⧸ HT) = 1 at hquotientOne
    have hxHT : xT ∈ HT :=
      (QuotientGroup.eq_one_iff xT).mp hquotientOne
    let h : Fitting_core M := ⟨(((xT : T) : HU) : M), hxHT⟩
    have hhOne : h ≠ 1 := by
      intro hh
      have hhG : (h : G) = 1 := congrArg Subtype.val hh
      have hxG : ((((xT : T) : HU) : M) : G) = 1 := by
        simpa only [h] using hhG
      exact hxOne (Subtype.ext (Subtype.ext (Subtype.ext hxG)))
    obtain ⟨j, hxPow⟩ := Subgroup.mem_zpowers_iff.mp x.property
    have hcommT : Commute y xT := by
      dsimp only [xT]
      rw [← hxPow]
      exact (Commute.refl y).zpow_right j
    let inclusion : T →* G :=
      M.subtype.comp (HU.subtype.comp T.subtype)
    have hcommG : Commute (tM : G) (h : G) := by
      change Commute (inclusion y) (inclusion xT)
      exact hcommT.map inclusion
    exact mem_FTsupport_of_commutes_with_fitting
      ctx tM htDerived htMOne h hhOne hcommG

/-! ## Orthogonality -/

/-- The character affording `gamma` kills the Fitting core, so it is
orthogonal to an irreducible whose kernel does not contain that core. -/
private theorem gamma_pairing_irreducible_eq_zero
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (psi : IrreducibleCharacter M ℂ)
    (hpsi : ¬ (Fitting_core M).subgroupOf M ≤
      psi.representation.ρ.ker) :
    characterPairing (pTypeCoreGamma ctx facts not_Galois)
      (psi : ClassFunction M ℂ) = 0 := by
  classical
  let D := Ptype_factor_action ctx facts
  let data := typeP_Galois_Pn
    (Ptype_factor_action_hypotheses ctx facts) not_Galois
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let HM : Subgroup M := (Fitting_core M).subgroupOf M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  let projection : HU →* U := pTypeNonGaloisHUToUProjection ctx
  let oneT : IrreducibleCharacter T ℂ := IrreducibleCharacter.trivial
  let representationHU : FDRep ℂ HU :=
    FDRep.induceFromSubgroup T oneT.representation
  let representationM : FDRep ℂ M :=
    FDRep.induceFromSubgroup HU representationHU
  letI : H.Normal :=
    Subgroup.Normal.subgroupOf (Fcore_normal M) HU
  letI : HM.Normal := Fcore_normal M
  have hHT : H ≤ T := by
    intro h hh
    change projection h ∈ pointwiseActionKernel D.U_action data.H₁
    have hhker : h ∈ (pTypeNonGaloisHUToUProjection ctx).ker := by
      rw [pTypeNonGaloisHUToUProjection_ker ctx]
      exact hh
    rw [MonoidHom.mem_ker.mp hhker]
    exact Subgroup.one_mem _
  have htrivial : H.subgroupOf T ≤ oneT.representation.ρ.ker := by
    rw [← ClassFunction.translationKernel_irreducibleCharacter oneT]
    intro x _
    rw [ClassFunction.mem_translationKernel_iff]
    intro y
    change (IrreducibleCharacter.trivial : IrreducibleCharacter T ℂ)
        (x * y) =
      (IrreducibleCharacter.trivial : IrreducibleCharacter T ℂ) y
    simp
  have hHkerHU : H ≤ representationHU.ρ.ker := by
    change H ≤
      (FDRep.induceFromSubgroup T oneT.representation).ρ.ker
    exact (FDRep.sub_ker_induceFromSubgroup_iff
      T H hHT oneT.representation).2 htrivial
  have hHMHU : HM ≤ HU := by
    intro h hh
    exact ctx.typeP.2.1.2.2.2.1 hh
  have hHMkerM : HM ≤ representationM.ρ.ker := by
    change HM ≤
      (FDRep.induceFromSubgroup HU representationHU).ρ.ker
    apply (FDRep.sub_ker_induceFromSubgroup_iff
      HU HM hHMHU representationHU).2
    exact hHkerHU
  have hHUcharacter : ClassFunction.ofRepresentation representationHU.ρ =
      pTypeCoreSelectedInducedTrivial ctx facts not_Galois := by
    change ClassFunction.ofRepresentation representationHU.ρ =
      ClassFunction.induce T (oneT : ClassFunction T ℂ)
    exact (ClassFunction.ofRepresentation_induceFromSubgroup_general
      T oneT.representation).trans
        (congrArg (ClassFunction.induce T)
          oneT.ofRepresentation_representation)
  have hMcharacter : ClassFunction.ofRepresentation representationM.ρ =
      pTypeCoreGamma ctx facts not_Galois := by
    change ClassFunction.ofRepresentation representationM.ρ =
      ClassFunction.induce HU
        (pTypeCoreSelectedInducedTrivial ctx facts not_Galois)
    exact (ClassFunction.ofRepresentation_induceFromSubgroup_general
      HU representationHU).trans
        (congrArg (ClassFunction.induce HU) hHUcharacter)
  by_contra hpair
  have hconstituent : psi.IsConstituent
      (ClassFunction.ofRepresentation representationM.ρ) := by
    unfold IrreducibleCharacter.IsConstituent
    rw [hMcharacter]
    exact hpair
  exact hpsi (hHMkerM.trans
    (FDRep.ker_le_irreducible_ker_of_isConstituent
      representationM psi hconstituent))

private theorem pairing_finset_sum_right
    {Q : Type} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (phi : ClassFunction Q ℂ) :
    characterPairing phi (∑ i ∈ s, f i) =
      ∑ i ∈ s, characterPairing phi (f i) := by
  exact map_sum (characterPairingLeft phi) f s

/-- A class function orthogonal to every irreducible constituent of another
class function is orthogonal to that class function. -/
private theorem pairing_eq_zero_of_constituents
    {Q : Type} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ)
    (hzero : ∀ chi : IrreducibleCharacter Q ℂ,
      chi ∈ ClassFunction.constituents psi →
        characterPairing phi (chi : ClassFunction Q ℂ) = 0) :
    characterPairing phi psi = 0 := by
  rw [← ClassFunction.sum_constituents_eq psi]
  rw [pairing_finset_sum_right]
  apply Finset.sum_eq_zero
  intro chi hchi
  rw [characterPairing_smul_right, hzero chi hchi, mul_zero]

/-! The representation-theoretic argument is kept separate from the
proof-irrelevant family boundary below. -/
private theorem gamma_pairing_induce_eq_zero
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (s : IrreducibleCharacter (pTypeCoreDerived M) ℂ)
    (hs : ¬ pTypeCoreFitting M ≤
      ClassFunction.translationKernel
        (s : ClassFunction (pTypeCoreDerived M) ℂ)) :
    characterPairing (pTypeCoreGamma ctx facts not_Galois)
      (ClassFunction.induce (pTypeCoreDerived M)
        (s : ClassFunction (pTypeCoreDerived M) ℂ)) = 0 := by
  classical
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let HM : Subgroup M := (Fitting_core M).subgroupOf M
  let induced : ClassFunction M ℂ :=
    ClassFunction.induce HU (s : ClassFunction HU ℂ)
  have hHMHU : HM ≤ HU := by
    intro h hh
    exact ctx.typeP.2.1.2.2.2.1 hh
  letI : HU.Normal :=
    Submission.OddOrder.BG.Section16.TypeSpecInternal.derivedWithin_normal16 M
  have hnotKernel
      (chi : IrreducibleCharacter M ℂ)
      (hchi : chi.IsConstituent induced) :
      ¬ HM ≤ chi.representation.ρ.ker := by
    intro hHMker
    have hHker : H ≤ s.representation.ρ.ker :=
      (IrreducibleCharacter.sub_ker_constituent_induce_iff
        HU HM hHMHU chi s hchi).mpr hHMker
    apply hs
    rw [ClassFunction.translationKernel_irreducibleCharacter]
    exact hHker
  have hzero (chi : IrreducibleCharacter M ℂ)
      (hchi : chi ∈ ClassFunction.constituents induced) :
      characterPairing (pTypeCoreGamma ctx facts not_Galois)
        (chi : ClassFunction M ℂ) = 0 :=
    gamma_pairing_irreducible_eq_zero ctx facts not_Galois chi
      (hnotKernel chi
        ((ClassFunction.mem_constituents_iff induced chi).mp hchi))
  exact pairing_eq_zero_of_constituents
    (pTypeCoreGamma ctx facts not_Galois) induced hzero

/-- `gamma` is orthogonal to the full sequentially induced kernel layer. -/
theorem pTypeCoreGamma_pairing_family_eq_zero
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    {phi : ClassFunction M ℂ}
    (hphi : phi ∈ pTypeCoreFamilyOfContext ctx) :
    characterPairing (pTypeCoreGamma ctx facts not_Galois) phi = 0 := by
  classical
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  have hphiSeq : phi ∈ seqIndD (k := ℂ) HU H H₀CPrime := by
    convert hphi using 1
    unfold pTypeCoreFamilyOfContext
    congr 1
    all_goals apply Subsingleton.elim
  obtain ⟨s, hs, hphiEq⟩ := seqIndP.mp hphiSeq
  rw [hphiEq]
  exact gamma_pairing_induce_eq_zero ctx facts not_Galois s
    (mem_Iirr_kerD.mp hs).2

/-- Every character in the rigid degree slice is orthogonal to `gamma`. -/
theorem PTypeCoreRigidFacts.gamma_pairing_slice_eq_zero
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂)
    {psi : ClassFunction M ℂ} (hpsi : psi ∈ S₂) :
    characterPairing (pTypeCoreGamma ctx facts not_Galois) psi = 0 := by
  classical
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let HM : Subgroup M := (Fitting_core M).subgroupOf M
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ (Ptype_factor_action ctx facts)
  let psiIrr : IrreducibleCharacter M ℂ :=
    ⟨psi, rigid.slice_irreducible psi hpsi⟩
  have hfamily := rigid.slice_small_kernel psi hpsi
  change psi ∈ seqIndD (k := ℂ) HU H H₀C at hfamily
  obtain ⟨s, hs, hpsiInduced⟩ := seqIndP.mp hfamily
  have hHMHU : HM ≤ HU := by
    intro h hh
    exact ctx.typeP.2.1.2.2.2.1 hh
  letI : HU.Normal := by
    exact Submission.OddOrder.BG.Section16.TypeSpecInternal.derivedWithin_normal16 M
  letI : HM.Normal := Fcore_normal M
  have hpsiNot : ¬ HM ≤ psiIrr.representation.ρ.ker := by
    intro hHMker
    have hconstituent : psiIrr.IsConstituent
        (ClassFunction.induce HU (s : ClassFunction HU ℂ)) := by
      unfold IrreducibleCharacter.IsConstituent
      rw [← hpsiInduced]
      change characterPairing
          (psiIrr : ClassFunction M ℂ)
          (psiIrr : ClassFunction M ℂ) ≠ 0
      rw [IrreducibleCharacter.characterPairing_self]
      exact one_ne_zero
    have hHker : H ≤ s.representation.ρ.ker :=
      (IrreducibleCharacter.sub_ker_constituent_induce_iff
        HU HM hHMHU psiIrr s hconstituent).mpr hHMker
    apply (mem_Iirr_kerD.mp hs).2
    rw [ClassFunction.translationKernel_irreducibleCharacter]
    exact hHker
  simpa only [psiIrr] using
    gamma_pairing_irreducible_eq_zero
      ctx facts not_Galois psiIrr hpsiNot

/-! ## Support -/

/-- Induction transports the selected-inertia support calculation to
`gamma`. -/
theorem pTypeCoreGamma_supportedOn
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeCoreGamma ctx facts not_Galois ∈
      ClassFunction.supportedOn (primeDadeSupport M (FTsupport M)) := by
  classical
  let HU := pTypeCoreDerived M
  let T := pTypeNonGaloisH1InertiaInHU ctx facts not_Galois
  have hT := selectedInertia_le_primeDadeSupport ctx facts not_Galois
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  rw [pTypeCoreGamma, ClassFunction.induce_apply_formula]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro y _
  split_ifs with hy
  · let t : HU := ⟨y⁻¹ * x * y, hy⟩
    rw [pTypeCoreSelectedInducedTrivial_apply]
    by_cases ht : t ∈ T
    · exfalso
      apply hx
      rcases hT t ht with htOne | htSupport
      · left
        have hconjOne : y⁻¹ * x * y = 1 := by
          apply Subtype.ext
          exact htOne
        have hxOne : x = 1 := by
          calc
            x = y * (y⁻¹ * x * y) * y⁻¹ := by group
            _ = 1 := by rw [hconjOne]; simp
        exact congrArg Subtype.val hxOne
      · right
        have hyNormalizer : (y : G) ∈ Subgroup.normalizer (FTsupport M) :=
          FTsupp_norm M y.property
        exact (Subgroup.mem_set_normalizer_iff''.mp
          hyNormalizer (x : G)).mpr htSupport
    · rw [if_neg ht]
  · rfl

/-- Every character in the source kernel layer has prime-Dade support. -/
theorem pTypeCoreFamilyOfContext_supportedOn
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (_facts : PTypeFCoreFactorFacts ctx)
    {psi : ClassFunction M ℂ}
    (hpsi : psi ∈ pTypeCoreFamilyOfContext ctx) :
    psi ∈ ClassFunction.supportedOn
      (primeDadeSupport M (FTsupport M)) := by
  classical
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  let pd := FT_prDade_hypF ctx.defW ctx.maxM ctx.typeP
  have hsource : psi ∈ seqIndD (k := ℂ) HU H H₀CPrime := by
    convert hpsi using 1
    unfold pTypeCoreFamilyOfContext
    congr 1
    all_goals apply Subsingleton.elim
  obtain ⟨s, hs, hpsiEq⟩ := seqIndP.mp hsource
  rw [hpsiEq]
  exact pd.prDade_Ind_irr_on s (mem_Iirr_kerD.mp hs).2

/-- Equal-degree differences remove the identity from the prime-Dade
support. -/
theorem pTypeCore_family_difference_supportedOn
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    {phi psi : ClassFunction M ℂ}
    (hphi : phi ∈ pTypeCoreFamilyOfContext ctx)
    (hpsi : psi ∈ pTypeCoreFamilyOfContext ctx)
    (hdegree : phi 1 = psi 1) :
    phi - psi ∈ ClassFunction.supportedOn
      {x : M | (x : G) ∈ FTsupport M} := by
  have hsupport : phi - psi ∈ ClassFunction.supportedOn
      (primeDadeSupport M (FTsupport M)) :=
    (ClassFunction.supportedOn
      (R := ℂ) (primeDadeSupport M (FTsupport M))).sub_mem
        (pTypeCoreFamilyOfContext_supportedOn ctx facts hphi)
        (pTypeCoreFamilyOfContext_supportedOn ctx facts hpsi)
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  by_cases hxOne : x = 1
  · subst x
    change phi 1 - psi 1 = 0
    rw [hdegree, sub_self]
  · apply ClassFunction.eq_zero_of_mem_supportedOn hsupport
    rw [mem_primeDadeSupport, not_or]
    exact ⟨fun hx' ↦ hxOne (Subtype.ext hx'), hx⟩

/-- Every rigid-slice character has prime-Dade support. -/
theorem PTypeCoreRigidFacts.slice_supportedOn
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂)
    {psi : ClassFunction M ℂ} (hpsi : psi ∈ S₂) :
    psi ∈ ClassFunction.supportedOn
      (primeDadeSupport M (FTsupport M)) := by
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ (Ptype_factor_action ctx facts)
  let pd := FT_prDade_hypF ctx.defW ctx.maxM ctx.typeP
  have hfamily := rigid.slice_small_kernel psi hpsi
  change psi ∈ seqIndD (k := ℂ) HU H H₀C at hfamily
  obtain ⟨s, hs, rfl⟩ := seqIndP.mp hfamily
  exact pd.prDade_Ind_irr_on s (mem_Iirr_kerD.mp hs).2

/-- The degree-zero difference `gamma - psi` is supported on the Type-P
support itself. -/
theorem pTypeCoreAlpha_supportedOn
    {G : Type} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂)
    {psi : ClassFunction M ℂ} (hpsi : psi ∈ S₂) :
    pTypeCoreAlpha (pTypeCoreGamma ctx facts not_Galois) psi ∈
      ClassFunction.supportedOn {x : M | (x : G) ∈ FTsupport M} := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let gamma := pTypeCoreGamma ctx facts not_Galois
  have hgamma : gamma ∈ ClassFunction.supportedOn
      (primeDadeSupport M (FTsupport M)) :=
    pTypeCoreGamma_supportedOn ctx facts not_Galois
  have hpsiSupport : psi ∈ ClassFunction.supportedOn
      (primeDadeSupport M (FTsupport M)) :=
    PTypeCoreSupportInternal.PTypeCoreRigidFacts.slice_supportedOn
      rigid hpsi
  have halpha : pTypeCoreAlpha gamma psi ∈
      ClassFunction.supportedOn (primeDadeSupport M (FTsupport M)) :=
    (ClassFunction.supportedOn
      (R := ℂ) (primeDadeSupport M (FTsupport M))).sub_mem
        hgamma hpsiSupport
  have hpsiDegree : psi 1 = ((D.q * a : ℕ) : ℂ) := by
    have hslice : psi ∈
        pTypeCoreDegreeSlice (pTypeCoreFamilyOfContext ctx) (D.q * a) := by
      rw [← rigid.current_eq_slice]
      exact hpsi
    exact (Finset.mem_filter.mp hslice).2
  have hgammaDegree : gamma 1 = ((D.q * a : ℕ) : ℂ) := by
    simpa only [gamma, D, hD, a] using
      pTypeCoreGamma_one ctx facts not_Galois
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  by_cases hxOne : x = 1
  · subst x
    change gamma 1 - psi 1 = 0
    rw [hgammaDegree, hpsiDegree, sub_self]
  · apply ClassFunction.eq_zero_of_mem_supportedOn halpha
    rw [mem_primeDadeSupport, not_or]
    exact ⟨fun hx' ↦ hxOne (Subtype.ext hx'), hx⟩

end PTypeCoreSupportInternal

end

end Submission.OddOrder.PF
