import Submission.OddOrder.PF.Section09.PTypeGaloisInfrastructure
import Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore

/-!
# Peterfalvi Section 9: Galois subgroup adapters

This module packages the subgroup calculations used by the Galois-character
phases of Peterfalvi (9.9).  It relates the canonical copies of `H`, `U`, `C`,
and `HC` inside `HU`, records the relevant index and commutator bounds, and
supplies the two-sided quotient algebra needed by the local Frobenius phase.

It deliberately stops before constructing the canonical Frobenius quotient.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open scoped Classical IsMulCommutative Pointwise commutatorElement

noncomputable section

universe u

namespace PTypeGaloisSubgroupAdaptersInternal

/-! ## Normality and complement transport -/

/-- The canonical named subgroup `HC` is normal in `HU`.  The infrastructure
lemma deliberately exposes the join defining `HC`; this adapter rewrites it to
the coordinate-core name used by downstream phases. -/
theorem pTypeHCInDerived_normal
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)).Normal := by
  change (pTypeHInDerived M (derivedWithin M) (Fitting_core M) ⊔
    pTypeCInDerived M (derivedWithin M) U W₁
      (Ptype_factor_action ctx facts)).Normal
  exact internal.pTypeHCInDerived_normal ctx facts

/-! ## Canonical subgroup transports -/

/-- The source equality `[M : HU] = q`, specialized to the canonical factor
action. -/
theorem pTypeHUInMaximal_index_eq_action_q
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeHUInMaximal M (derivedWithin M)).index =
      (Ptype_factor_action ctx facts).q := by
  have houter : IsInternalSemidirectProductIn
      (derivedWithin M) W₁ M := ctx.typeP.1.2.2.2
  calc
    (pTypeHUInMaximal M (derivedWithin M)).index =
        Nat.card (W₁.subgroupOf M) :=
      houter.2.2.2.symm.index_eq_card
    _ = Nat.card W₁ :=
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq houter.2.1
    _ = (Ptype_factor_action ctx facts).q := by
      rw [Ptype_factor_action_q]

/-- The ambient presentation of `HC` is contained in `HU = M'`. -/
theorem pTypeHCInMaximal_le_HU
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    (D : PTypeFactorActionData Hbar U W₁) :
    pTypeHCInMaximal M (Fitting_core M) U W₁ D ≤
      pTypeHUInMaximal M (derivedWithin M) := by
  have hinner : IsInternalSemidirectProductIn
      (Fitting_core M) U (derivedWithin M) :=
    ctx.typeP.2.1.2.2.2
  apply sup_le
  · exact Subgroup.subgroupOf_mono M hinner.1
  · exact Subgroup.subgroupOf_mono M
      ((Subgroup.map_subtype_le D.C).trans hinner.2.1)

/-- Forming `HC` directly in `HU` agrees with restricting its ambient
presentation in `M`. -/
theorem pTypeHCInDerived_eq_subgroupOf
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    (D : PTypeFactorActionData Hbar U W₁) :
    pTypeHCInDerived M (derivedWithin M) (Fitting_core M) U W₁ D =
      (pTypeHCInMaximal M (Fitting_core M) U W₁ D).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M)) := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  have hHC := pTypeHCInMaximal_le_HU ctx D
  have hH : (Fitting_core M).subgroupOf M ≤ HU :=
    le_sup_left.trans hHC
  have hC : (D.C.map U.subtype).subgroupOf M ≤ HU :=
    le_sup_right.trans hHC
  exact (Subgroup.subgroupOf_sup hH hC).symm

/-- Triviality of the canonical copy of the complement kernel is equivalent
to triviality of the action kernel itself. -/
theorem pTypeCInDerived_eq_bot_iff
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    (D : PTypeFactorActionData Hbar U W₁) :
    pTypeCInDerived M (derivedWithin M) U W₁ D = ⊥ ↔
      D.C = ⊥ := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  have hinner : IsInternalSemidirectProductIn
      (Fitting_core M) U (derivedWithin M) :=
    ctx.typeP.2.1.2.2.2
  have houter : IsInternalSemidirectProductIn
      (derivedWithin M) W₁ M := ctx.typeP.1.2.2.2
  constructor
  · intro hC
    apply eq_bot_iff.mpr
    intro c hc
    let cM : M :=
      ⟨(c : Gamma), hinner.2.1.trans houter.1 c.property⟩
    let cHU : HU := ⟨cM, hinner.2.1 c.property⟩
    have hcHU :
        cHU ∈ pTypeCInDerived M (derivedWithin M) U W₁ D := by
      exact ⟨(c : U), hc, rfl⟩
    have hcOne : cHU = 1 := by
      have hcBot : cHU ∈ (⊥ : Subgroup HU) := by
        simpa [hC] using hcHU
      exact Subgroup.mem_bot.mp hcBot
    apply Subtype.ext
    exact congrArg (fun x : HU ↦ (((x : M) : Gamma))) hcOne
  · intro hC
    simp [pTypeCInDerived, hC]

/-- If the action kernel is trivial, the action-factor cardinal is the
cardinality of the original complement. -/
theorem pTypeActionFactorCard_eq_card_of_C_eq_bot
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁)
    (hC : D.C = ⊥) :
    pTypeActionFactorCard D = Nat.card U := by
  letI : D.C.Normal := D.C_normal
  change Nat.card (U ⧸ D.C) = Nat.card U
  calc
    Nat.card (U ⧸ D.C) = Nat.card (U ⧸ (⊥ : Subgroup U)) :=
      Nat.card_congr
        (QuotientGroup.quotientMulEquivOfEq hC).toEquiv
    _ = Nat.card U :=
      Nat.card_congr QuotientGroup.quotientBot.toEquiv

/-- In the Galois branch, a trivial action kernel makes the original
complement cyclic. -/
theorem pTypeGalois_complement_cyclic_of_C_eq_bot
    {Hbar U W₁ : Type u}
    [Group Hbar] [Finite Hbar]
    [Group U] [Finite U]
    [Group W₁] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (hGal : typeP_Galois D) (hC : D.C = ⊥) :
    IsCyclic U := by
  letI : D.C.Normal := D.C_normal
  have hcyclic := (typeP_Galois_P hD hGal).complement_factor_cyclic
  have hcyclicBot : IsCyclic (U ⧸ (⊥ : Subgroup U)) :=
    (QuotientGroup.quotientMulEquivOfEq hC).isCyclic.mp hcyclic
  exact QuotientGroup.quotientBot.isCyclic.mp hcyclicBot

/-- Complementary commuting subgroups give the canonical internal direct
product decomposition of the whole ambient group. -/
theorem pTypeInternalDirectProduct_top_of_complement_commute
    {A : Type u} [Group A] (K R : Subgroup A)
    (hcomp : K.IsComplement' R)
    (hcomm : ∀ x : K, ∀ y : R, Commute (x : A) (y : A)) :
    IsInternalDirectProductIn K R (⊤ : Subgroup A) := by
  have hcompTop :=
    internal.pTypeIsComplement_subgroupOf_of_left_le hcomp le_top
  refine
    { left_le := le_top
      right_le := le_top
      complement := ?_
      commute := hcomm }
  simpa using hcompTop

/-- The canonical copies of `H = F(M)` and `U` are complementary inside
`HU = M'`. -/
theorem pTypeHInDerived_isComplement_UInDerived
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeHInDerived M (derivedWithin M)
      (Fitting_core M)).IsComplement'
        (pTypeUInDerived M (derivedWithin M) U) := by
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  let eHU : pTypeHUInMaximal M (derivedWithin M) ≃*
      derivedWithin M :=
    Subgroup.subgroupOfEquivOfLe hDerM
  have hmapped :=
    Submission.OddOrder.PF.internal.pTypeIsComplement_map_mulEquiv
      ctx.typeP.2.1.2.2.2.2.2.2 eHU.symm
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

/-- The pieces removed in `HU / H₀C` are proper in their respective kernel
and complement factors. -/
theorem pTypeH0_C_strict_in_derived
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let UHU := pTypeUInDerived M (derivedWithin M) U
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    H₀ < H ∧ C < UHU := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let UHU := pTypeUInDerived M (derivedWithin M) U
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hH₀H : H₀ ≤ H := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Ptype_Fcore_kernel_lt ctx).le)
  have hCU : C ≤ UHU := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Subgroup.map_subtype_le D.C))
  constructor
  · refine lt_iff_le_not_ge.mpr ⟨hH₀H, ?_⟩
    intro hreverse
    apply (Ptype_Fcore_kernel_lt ctx).2
    intro x hx
    let xM : M := ⟨x, hHder.trans hDerM hx⟩
    let xHU : HU := ⟨xM, hHder hx⟩
    have hxH : xHU ∈ H := hx
    have hxH₀ : xHU ∈ H₀ := hreverse hxH
    exact hxH₀
  · refine lt_iff_le_not_ge.mpr ⟨hCU, ?_⟩
    intro hreverse
    apply D.C_ne_top
    apply top_unique
    intro x _hx
    let xM : M :=
      ⟨(x : Gamma), hUder.trans hDerM x.property⟩
    let xHU : HU := ⟨xM, hUder x.property⟩
    have hxU : xHU ∈ UHU := x.property
    have hxC : xHU ∈ C := hreverse hxU
    change (x : Gamma) ∈ D.C.map U.subtype at hxC
    obtain ⟨c, hc, hcx⟩ := hxC
    have hxc : x = c := by
      apply Subtype.ext
      exact hcx.symm
    exact hxc.symm ▸ hc

/-! ## Generic semidirect-product intersections and quotients -/

/-- In an internal semidirect product, adjoining a subgroup of the kernel to
a subgroup of the complement has the expected intersections with the two
factors. -/
theorem pTypeInf_sup_eq_of_isComplement
    {A : Type u} [Group A]
    (H U N C : Subgroup A) [N.Normal]
    (hHU : H.IsComplement' U) (hNH : N ≤ H) (hCU : C ≤ U) :
    H ⊓ (N ⊔ C) = N ∧ U ⊓ (N ⊔ C) = C := by
  constructor
  · apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, c, hc, hnc⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hx.2
      have hcH : c ∈ H := by
        have hcEq : c = n⁻¹ * x := by
          rw [← hnc]
          simp
        rw [hcEq]
        exact H.mul_mem (H.inv_mem (hNH hn)) hx.1
      have hcOne : c = 1 := by
        apply Subgroup.mem_bot.mp
        exact hHU.disjoint.le_bot ⟨hcH, hCU hc⟩
      have hxEq : x = n := by
        rw [← hnc, hcOne, mul_one]
      exact hxEq.symm ▸ hn
    · intro n hn
      exact ⟨hNH hn, (show N ≤ N ⊔ C from le_sup_left) hn⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, c, hc, hnc⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hx.2
      have hnU : n ∈ U := by
        have hnEq : n = x * c⁻¹ := by
          rw [← hnc]
          simp
        rw [hnEq]
        exact U.mul_mem hx.1 (U.inv_mem (hCU hc))
      have hnOne : n = 1 := by
        apply Subgroup.mem_bot.mp
        exact hHU.disjoint.le_bot ⟨hNH hn, hnU⟩
      have hxEq : x = c := by
        rw [← hnc, hnOne, one_mul]
      exact hxEq.symm ▸ hc
    · intro c hc
      exact ⟨hCU hc, (show C ≤ N ⊔ C from le_sup_right) hc⟩

/-! ## Canonical index calculation -/

/-- The source identity `[HU : HC] = |U / C|` for the canonical Section 9
subgroups. -/
theorem pTypeHCInDerived_index_eq_actionFactorCard
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    HC.index = pTypeActionFactorCard D := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let UHU := pTypeUInDerived M (derivedWithin M) U
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  letI : H.Normal :=
    Submission.OddOrder.PF.internal.pTypeHInDerived_normal ctx
  letI : D.C.Normal := D.C_normal
  have hcomp : H.IsComplement' UHU :=
    pTypeHInDerived_isComplement_UInDerived ctx
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  have hCU : C ≤ UHU := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M
        (Subgroup.map_subtype_le D.C))
  have hHHC : H ≤ HC := le_sup_left
  have hindexRel : HC.index = HC.relIndex UHU :=
    internal.pTypeIndex_eq_relIndex_of_isComplement_of_left_le
      hcomp hHHC
  have hinter := pTypeInf_sup_eq_of_isComplement
    H UHU H C hcomp le_rfl hCU
  have hHCcap : HC.subgroupOf UHU = C.subgroupOf UHU := by
    ext x
    change (x : HU) ∈ H ⊔ C ↔ (x : HU) ∈ C
    constructor
    · intro hx
      have hxInf : (x : HU) ∈ UHU ⊓ (H ⊔ C) :=
        ⟨x.property, hx⟩
      rw [hinter.2] at hxInf
      exact hxInf
    · exact fun hx ↦
        (show C ≤ H ⊔ C from le_sup_right) hx
  have hUHU : U.subgroupOf M ≤ HU := by
    intro x hx
    exact hUder hx
  have hcardUHU : Nat.card UHU = Nat.card U := by
    calc
      Nat.card UHU = Nat.card (U.subgroupOf M) :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUHU
      _ = Nat.card U :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUM
  have hDCder : D.C.map U.subtype ≤ derivedWithin M :=
    (Subgroup.map_subtype_le D.C).trans hUder
  have hDCM : D.C.map U.subtype ≤ M := hDCder.trans hDerM
  have hDCHU : (D.C.map U.subtype).subgroupOf M ≤ HU := by
    intro x hx
    exact hDCder hx
  have hcardC : Nat.card C = Nat.card D.C := by
    calc
      Nat.card C =
          Nat.card ((D.C.map U.subtype).subgroupOf M) :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hDCHU
      _ = Nat.card (D.C.map U.subtype) :=
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hDCM
      _ = Nat.card D.C :=
        Subgroup.card_map_of_injective U.subtype_injective
  have hcardCsub : Nat.card (C.subgroupOf UHU) = Nat.card D.C :=
    (Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hCU).trans
      hcardC
  have hleft : (C.subgroupOf UHU).index * Nat.card D.C =
      Nat.card U := by
    calc
      (C.subgroupOf UHU).index * Nat.card D.C =
          (C.subgroupOf UHU).index *
            Nat.card (C.subgroupOf UHU) := by rw [hcardCsub]
      _ = Nat.card UHU := (C.subgroupOf UHU).index_mul_card
      _ = Nat.card U := hcardUHU
  have hright : D.C.index * Nat.card D.C = Nat.card U :=
    D.C.index_mul_card
  have hindexC : (C.subgroupOf UHU).index = D.C.index :=
    Nat.eq_of_mul_eq_mul_right (Nat.card_pos (α := D.C))
      (hleft.trans hright.symm)
  calc
    HC.index = HC.relIndex UHU := hindexRel
    _ = (HC.subgroupOf UHU).index := rfl
    _ = (C.subgroupOf UHU).index := by rw [hHCcap]
    _ = D.C.index := hindexC
    _ = pTypeActionFactorCard D := rfl

/-! ## Canonical commutator bounds -/

/-- The derived-complement kernel bound `H₀C'` lies below `H₀C`. -/
theorem pTypeH0CPrimeInDerived_le_H0CInDerived
    {Gamma : Type u} [Group Gamma]
    (M K H₀ U W₁ : Subgroup Gamma)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) :
    pTypeH0CPrimeInDerived M K H₀ U W₁ D ≤
      pTypeH0CInDerived M K H₀ U W₁ D := by
  have hderived :
      pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype) ≤
        D.C.map U.subtype := by
    rintro _ ⟨c, _hc, rfl⟩
    exact ⟨(c : U), c.property, rfl⟩
  exact sup_le_sup le_rfl
    (Subgroup.subgroupOf_mono (pTypeHUInMaximal M K)
      (Subgroup.subgroupOf_mono M hderived))

/-- The canonical action kernel centralizes the Fitting core modulo the
selected F-core kernel. -/
theorem pTypeGalois_commutator_C_H_le_H0
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
    let H₀ := pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)
    let C := pTypeCInDerived M (derivedWithin M) U W₁ D
    ⁅C, H⁆ ≤ H₀ := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let H₀ := pTypeH0InDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let Hₐ := Fitting_core M
  let H₀a := Ptype_Fcore_kernel ctx
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUM : U ≤ M := hUder.trans hDerM
  have hUnormH : U ≤ Subgroup.normalizer (Hₐ : Set Gamma) :=
    hUM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (Fcore_sub M)).mp
        (Fcore_normal M))
  have hUnormH₀ : U ≤ Subgroup.normalizer (H₀a : Set Gamma) :=
    hUM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Ptype_Fcore_kernel_le_M ctx)).mp
          (Ptype_Fcore_kernel_normal_M ctx))
  apply Subgroup.commutator_le.mpr
  intro x hx y hy
  have hxC : (((x : HU) : M) : Gamma) ∈
      D.C.map U.subtype := hx
  obtain ⟨u, hu, hux⟩ := hxC
  let yH : Hₐ :=
    ⟨(((y : HU) : M) : Gamma), hy⟩
  have huKer : u ∈ (ptypeFCoreAction ctx).ker := by
    change u ∈ ((ptypeFCoreAction ctx).ker : Set U)
    simpa only [D, Ptype_factor_action_C] using hu
  have huKer' : u ∈
      (subgroupConjugationFactorHom H₀a Hₐ U
        hUnormH hUnormH₀).ker := by
    simpa only [ptypeFCoreAction] using huKer
  have hcomm : ⁅(u : Gamma), (yH : Gamma)⁆ ∈ H₀a :=
    (mem_ker_subgroupConjugationFactorHom_iff
      H₀a Hₐ U hUnormH hUnormH₀ u).mp huKer'
        (yH : Gamma) yH.property
  change ⁅(((x : HU) : M) : Gamma),
    (((y : HU) : M) : Gamma)⁆ ∈ H₀a
  rw [← hux]
  exact hcomm

/-- The derived subgroup of the canonical inducing subgroup `HC` lies in
the canonical source kernel `H₀C'`. -/
theorem pTypeGalois_commutator_HC_le_H0CPrime
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HC := pTypeHCInDerived M (derivedWithin M)
      (Fitting_core M) U W₁ D
    let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    _root_.commutator HC ≤ H₀CPrime.subgroupOf HC := by
  classical
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := pTypeHInDerived M (derivedWithin M) (Fitting_core M)
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  let H₀CPrime := pTypeH0CPrimeInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let Hₐ := Fitting_core M
  let H₀a := Ptype_Fcore_kernel ctx
  change _root_.commutator HC ≤ H₀CPrime.subgroupOf HC
  letI : (H₀a.subgroupOf Hₐ).Normal :=
    Ptype_Fcore_kernel_normal_Fcore ctx
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    (ptypeFCoreFactor_elementary ctx).commutative
  letI : H₀CPrime.Normal :=
    internal.pTypeH0CPrimeInDerived_normal ctx facts
  have hHcomm : _root_.commutator Hₐ ≤ H₀a.subgroupOf Hₐ :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      (inferInstance : IsMulCommutative (ptypeFCoreFactor ctx))
  have hHH : ⁅H, H⁆ ≤ H₀CPrime := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    let xH : Hₐ :=
      ⟨(((x : HU) : M) : Gamma), hx⟩
    let yH : Hₐ :=
      ⟨(((y : HU) : M) : Gamma), hy⟩
    have hxyComm : ⁅xH, yH⁆ ∈ _root_.commutator Hₐ := by
      change ⁅xH, yH⁆ ∈ ⁅(⊤ : Subgroup Hₐ), ⊤⁆
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top xH) (Subgroup.mem_top yH)
    have hleft :
        pTypeH0InDerived M (derivedWithin M) H₀a ≤ H₀CPrime := by
      exact le_sup_left
    apply hleft
    change ⁅(((x : HU) : M) : Gamma),
      (((y : HU) : M) : Gamma)⁆ ∈ H₀a
    have hxyH0 : ((⁅xH, yH⁆ : Hₐ) : Gamma) ∈ H₀a :=
      hHcomm hxyComm
    change ⁅(xH : Gamma), (yH : Gamma)⁆ ∈ H₀a at hxyH0
    simpa only [xH, yH] using hxyH0
  have hCH : ⁅C, H⁆ ≤ H₀CPrime := by
    exact (pTypeGalois_commutator_C_H_le_H0 ctx facts).trans le_sup_left
  have hHC : ⁅H, C⁆ ≤ H₀CPrime := by
    rw [Subgroup.commutator_comm]
    exact hCH
  have hCC : ⁅C, C⁆ ≤ H₀CPrime := by
    apply Subgroup.commutator_le.mpr
    intro x hx y hy
    have hxC : (((x : HU) : M) : Gamma) ∈
        D.C.map U.subtype := hx
    have hyC : (((y : HU) : M) : Gamma) ∈
        D.C.map U.subtype := hy
    obtain ⟨u, hu, hux⟩ := hxC
    obtain ⟨v, hv, hvy⟩ := hyC
    let uC : D.C := ⟨u, hu⟩
    let vC : D.C := ⟨v, hv⟩
    have huvComm : ⁅uC, vC⁆ ∈ _root_.commutator D.C := by
      change ⁅uC, vC⁆ ∈ ⁅(⊤ : Subgroup D.C), ⊤⁆
      exact Subgroup.commutator_mem_commutator
        (Subgroup.mem_top uC) (Subgroup.mem_top vC)
    have hright :
        ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU ≤
          H₀CPrime := by
      exact le_sup_right
    apply hright
    change ⁅(((x : HU) : M) : Gamma),
        (((y : HU) : M) : Gamma)⁆ ∈
      pTypeDerivedComplementInMaximal
        (U.subtype.comp D.C.subtype)
    refine ⟨⁅uC, vC⁆, huvComm, ?_⟩
    rw [map_commutatorElement]
    change ⁅(u : Gamma), (v : Gamma)⁆ =
      ⁅(((x : HU) : M) : Gamma), (((y : HU) : M) : Gamma)⁆
    exact congrArg₂ (fun a b : Gamma ↦ ⁅a, b⁆) hux hvy
  have hHsup : ⁅H, H ⊔ C⁆ ≤ H₀CPrime :=
    commutator_sup_le_of_normal hHH hHC
  have hCsup : ⁅C, H ⊔ C⁆ ≤ H₀CPrime :=
    commutator_sup_le_of_normal hCH hCC
  have hsupH : ⁅H ⊔ C, H⁆ ≤ H₀CPrime := by
    rw [Subgroup.commutator_comm]
    exact hHsup
  have hsupC : ⁅H ⊔ C, C⁆ ≤ H₀CPrime := by
    rw [Subgroup.commutator_comm]
    exact hCsup
  have hHCcomm : ⁅HC, HC⁆ ≤ H₀CPrime := by
    change ⁅H ⊔ C, H ⊔ C⁆ ≤ H₀CPrime
    exact commutator_sup_le_of_normal hsupH hsupC
  intro z hz
  change (z : HU) ∈ H₀CPrime
  apply hHCcomm
  rw [← HC.map_subtype_commutator]
  exact ⟨z, hz, rfl⟩

/-- Quotienting an internal semidirect product by `N ⋔ C`, where `N`
lies in its kernel and `C` lies in its complement, leaves the two quotient
images complementary. -/
theorem pTypeIsComplement_quotient_sup
    {A : Type u} [Group A]
    (H U N C : Subgroup A) [H.Normal] [N.Normal]
    [(N ⊔ C).Normal]
    (hHU : H.IsComplement' U) (hNH : N ≤ H) (hCU : C ≤ U) :
    (H.map (QuotientGroup.mk' (N ⊔ C))).IsComplement'
      (U.map (QuotientGroup.mk' (N ⊔ C))) := by
  let q : A →* A ⧸ (N ⊔ C) := QuotientGroup.mk' (N ⊔ C)
  let Hq : Subgroup (A ⧸ (N ⊔ C)) := H.map q
  let Uq : Subgroup (A ⧸ (N ⊔ C)) := U.map q
  letI : Hq.Normal :=
    Subgroup.Normal.map (inferInstance : H.Normal) q
      (QuotientGroup.mk'_surjective (N ⊔ C))
  have hsup : Hq ⊔ Uq = ⊤ := by
    dsimp [Hq, Uq]
    rw [← Subgroup.map_sup, hHU.sup_eq_top,
      Subgroup.map_top_of_surjective q
        (QuotientGroup.mk'_surjective (N ⊔ C))]
  have hdis : Disjoint Hq Uq := by
    rw [disjoint_iff_inf_le]
    intro z hz
    rcases hz.1 with ⟨h, hh, hhz⟩
    rcases hz.2 with ⟨v, hv, hvz⟩
    have hquot : q h = q v := hhz.trans hvz.symm
    have hmem : h⁻¹ * v ∈ N ⊔ C := QuotientGroup.eq.mp hquot
    obtain ⟨n, hn, c, hc, hnc⟩ :=
      Subgroup.mem_sup_of_normal_left.mp hmem
    have hfactorEq : h * n = v * c⁻¹ := by
      calc
        h * n = h * (n * c) * c⁻¹ := by group
        _ = h * (h⁻¹ * v) * c⁻¹ := by rw [hnc]
        _ = v * c⁻¹ := by group
    have hleftH : h * n ∈ H := H.mul_mem hh (hNH hn)
    have hleftU : h * n ∈ U := by
      rw [hfactorEq]
      exact U.mul_mem hv (U.inv_mem (hCU hc))
    have hleftOne : h * n = 1 := by
      apply Subgroup.mem_bot.mp
      exact hHU.disjoint.le_bot ⟨hleftH, hleftU⟩
    have hqn : q n = 1 :=
      QuotientGroup.eq_one_iff n |>.mpr
        ((show N ≤ N ⊔ C from le_sup_left) hn)
    apply Subgroup.mem_bot.mpr
    rw [← hhz]
    calc
      q h = q (h * n) := by rw [map_mul, hqn, mul_one]
      _ = 1 := by rw [hleftOne, map_one]
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
  rw [← Subgroup.normal_mul Hq Uq, hsup]
  rfl

/-- If the kernel-side and complement-side pieces removed by a two-sided
quotient are proper, both quotient images remain nontrivial. -/
theorem pTypeQuotientSup_images_ne_bot
    {A : Type u} [Group A]
    (H U N C : Subgroup A) [N.Normal] [(N ⊔ C).Normal]
    (hHU : H.IsComplement' U) (hN : N < H) (hC : C < U) :
    H.map (QuotientGroup.mk' (N ⊔ C)) ≠ ⊥ ∧
      U.map (QuotientGroup.mk' (N ⊔ C)) ≠ ⊥ := by
  have hinter := pTypeInf_sup_eq_of_isComplement
    H U N C hHU hN.le hC.le
  constructor
  · intro hmap
    have hleKer : H ≤ (QuotientGroup.mk' (N ⊔ C)).ker :=
      (Subgroup.map_eq_bot_iff H).mp hmap
    rw [QuotientGroup.ker_mk'] at hleKer
    apply hN.2
    intro x hx
    have hxInf : x ∈ H ⊓ (N ⊔ C) := ⟨hx, hleKer hx⟩
    rw [hinter.1] at hxInf
    exact hxInf
  · intro hmap
    have hleKer : U ≤ (QuotientGroup.mk' (N ⊔ C)).ker :=
      (Subgroup.map_eq_bot_iff U).mp hmap
    rw [QuotientGroup.ker_mk'] at hleKer
    apply hC.2
    intro x hx
    have hxInf : x ∈ U ⊓ (N ⊔ C) := ⟨hx, hleKer hx⟩
    rw [hinter.2] at hxInf
    exact hxInf

end PTypeGaloisSubgroupAdaptersInternal

end

end Submission.OddOrder.PF
