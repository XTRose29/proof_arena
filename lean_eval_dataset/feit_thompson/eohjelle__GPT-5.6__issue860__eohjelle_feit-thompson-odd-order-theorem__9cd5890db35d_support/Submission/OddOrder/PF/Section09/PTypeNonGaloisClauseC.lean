import Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleCharacters

/-!
# Peterfalvi Section 9: the non-Galois clause (c)

This module separates the genuinely irreducible part of the full coordinate
family from its constant-coordinate, reducible subfamily.  A character in the
complement induces irreducibly to the maximal subgroup and, by induction
transitivity, is still induced directly from a linear character of `HC`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative MonoidAlgebra

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF.internal
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open PTypeNonGaloisCoordinateCoreInternal
open PTypeNonGaloisHCProjectionInternal
open PTypeNonGaloisHUFamilyInternal
open PTypeNonGaloisReducibleCharactersInternal

universe u

namespace PTypeNonGaloisClauseCInternal

/-! ## The two subgroup indices -/

/-- Intersecting `N C` with either factor of a complement decomposition
recovers the corresponding subgroup. -/
private theorem inf_sup_eq_of_isComplement
    {A : Type u} [Group A]
    (H U N C : Subgroup A) [N.Normal]
    (hHU : H.IsComplement' U) (hNH : N ≤ H) (hCU : C ≤ U) :
    H ⊓ (N ⊔ C) = N ∧ U ⊓ (N ⊔ C) = C := by
  constructor
  · apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, c, hc, rfl⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hx.2
      have hcH : c ∈ H := by
        have : (c : A) = n⁻¹ * (n * c) := by simp
        rw [this]
        exact H.mul_mem (H.inv_mem (hNH hn)) hx.1
      have hcOne : c = 1 := by
        apply Subgroup.mem_bot.mp
        exact hHU.disjoint.le_bot ⟨hcH, hCU hc⟩
      simpa [hcOne] using hn
    · intro n hn
      exact ⟨hNH hn, (show N ≤ N ⊔ C from le_sup_left) hn⟩
  · apply le_antisymm
    · intro x hx
      obtain ⟨n, hn, c, hc, rfl⟩ :=
        Subgroup.mem_sup_of_normal_left.mp hx.2
      have hnU : n ∈ U := by
        have : (n : A) = (n * c) * c⁻¹ := by simp
        rw [this]
        exact U.mul_mem hx.1 (U.inv_mem (hCU hc))
      have hnOne : n = 1 := by
        apply Subgroup.mem_bot.mp
        exact hHU.disjoint.le_bot ⟨hNH hn, hnU⟩
      simpa [hnOne] using hc
    · intro c hc
      exact ⟨hCU hc, (show C ≤ N ⊔ C from le_sup_right) hc⟩

/-- The Fitting subgroup and the chosen complement remain complementary in
the canonical copy of the derived subgroup inside `M`. -/
private theorem fittingInHU_isComplement_complementInHU
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (((Fitting_core M).subgroupOf M).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M))).IsComplement'
      ((U.subgroupOf M).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M))) := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  let eHU : HU ≃* derivedWithin M :=
    Subgroup.subgroupOfEquivOfLe hDerM
  have hmapped := pTypeIsComplement_map_mulEquiv
    ctx.typeP.2.1.2.2.2.2.2.2 eHU.symm
  have hmapH :
      ((Fitting_core M).subgroupOf (derivedWithin M)).map
          eHU.symm.toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨eHU x, hx, eHU.symm_apply_apply x⟩
  have hmapU :
      (U.subgroupOf (derivedWithin M)).map
          eHU.symm.toMonoidHom = UHU := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨eHU x, hx, eHU.symm_apply_apply x⟩
  rw [hmapH, hmapU] at hmapped
  exact hmapped

/-- The intermediate induction index is the cardinality of the action
quotient `U / C`. -/
theorem pTypeNonGaloisHCInHU_index_eq_actionFactorCard
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    (HC.subgroupOf HU).index = pTypeActionFactorCard D := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let C : Subgroup HU :=
    ((D.C.map U.subtype).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  let HCder : Subgroup HU := H ⊔ C
  change HCN.index = pTypeActionFactorCard D
  letI : H.Normal :=
    Subgroup.Normal.subgroupOf (Fcore_normal M) HU
  letI : D.C.Normal := D.C_normal
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  have hCder : D.C.map U.subtype ≤ derivedWithin M :=
    (Subgroup.map_subtype_le D.C).trans hUder
  have hH_HU : (Fitting_core M).subgroupOf M ≤ HU := by
    intro x hx
    exact hHder hx
  have hC_HU : (D.C.map U.subtype).subgroupOf M ≤ HU := by
    intro x hx
    exact hCder hx
  have hHCN : HCN = HCder := by
    change (((Fitting_core M).subgroupOf M ⊔
          (D.C.map U.subtype).subgroupOf M).subgroupOf HU) =
      ((Fitting_core M).subgroupOf M).subgroupOf HU ⊔
        ((D.C.map U.subtype).subgroupOf M).subgroupOf HU
    exact Subgroup.subgroupOf_sup hH_HU hC_HU
  have hcomp : H.IsComplement' UHU :=
    fittingInHU_isComplement_complementInHU ctx
  have hCU : C ≤ UHU :=
    Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M (Subgroup.map_subtype_le D.C))
  have hindexRel : HCder.index = HCder.relIndex UHU :=
    pTypeIndex_eq_relIndex_of_isComplement_of_left_le hcomp le_sup_left
  have hinter := inf_sup_eq_of_isComplement
    H UHU H C hcomp le_rfl hCU
  have hHCcap : HCder.subgroupOf UHU = C.subgroupOf UHU := by
    ext x
    change (x : HU) ∈ H ⊔ C ↔ (x : HU) ∈ C
    constructor
    · intro hx
      have hxInf : (x : HU) ∈ UHU ⊓ (H ⊔ C) := ⟨x.property, hx⟩
      rw [hinter.2] at hxInf
      exact hxInf
    · exact fun hx ↦ (show C ≤ H ⊔ C from le_sup_right) hx
  have hUHU : U.subgroupOf M ≤ HU := by
    intro x hx
    exact hUder hx
  have hcardUHU : Nat.card UHU = Nat.card U := by
    calc
      Nat.card UHU = Nat.card (U.subgroupOf M) :=
        natCard_subgroupOf_eq hUHU
      _ = Nat.card U := natCard_subgroupOf_eq hUM
  have hDCM : D.C.map U.subtype ≤ M := hCder.trans hDerM
  have hDCHU : (D.C.map U.subtype).subgroupOf M ≤ HU := by
    intro x hx
    exact hCder hx
  have hcardC : Nat.card C = Nat.card D.C := by
    calc
      Nat.card C = Nat.card ((D.C.map U.subtype).subgroupOf M) :=
        natCard_subgroupOf_eq hDCHU
      _ = Nat.card (D.C.map U.subtype) :=
        natCard_subgroupOf_eq hDCM
      _ = Nat.card D.C :=
        Subgroup.card_map_of_injective U.subtype_injective
  have hcardCsub : Nat.card (C.subgroupOf UHU) = Nat.card D.C :=
    (natCard_subgroupOf_eq hCU).trans hcardC
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
  rw [hHCN]
  calc
    HCder.index = HCder.relIndex UHU := hindexRel
    _ = (HCder.subgroupOf UHU).index := rfl
    _ = (C.subgroupOf UHU).index := by rw [hHCcap]
    _ = D.C.index := hindexC
    _ = pTypeActionFactorCard D := rfl

/-- The outer induction index is the prime `q` from the factor action. -/
theorem pTypeNonGaloisHUInMaximal_index_eq_action_q
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
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
    _ = Nat.card W₁ := natCard_subgroupOf_eq houter.2.1
    _ = (Ptype_factor_action ctx facts).q := by
      rw [Ptype_factor_action_q]

/-- Hence direct induction from `HC` has degree multiplier `q |U/C|`. -/
theorem pTypeNonGaloisHCInMaximal_index
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    HC.index = D.q * pTypeActionFactorCard D := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  have hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  calc
    HC.index = HC.relIndex HU * HU.index :=
      (Subgroup.relIndex_mul_index hHC).symm
    _ = (HC.subgroupOf HU).index * HU.index := rfl
    _ = pTypeActionFactorCard D * D.q := by
      rw [pTypeNonGaloisHCInHU_index_eq_actionFactorCard,
        pTypeNonGaloisHUInMaximal_index_eq_action_q]
    _ = D.q * pTypeActionFactorCard D := Nat.mul_comm _ _

/-! ## Separating the full and constant families -/

/-- Induction from `HC` to `HU` has constant fiber size `|U/C|` on the
stable full coordinate family. -/
private theorem fullHUCoordinateFamily_card_relation
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    (D.p - 1) ^ D.q = pTypeActionFactorCard D *
      (pTypeNonGaloisFullHUCoordinateFamily
        ctx facts not_Galois).card := by
  classical
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  let X := pTypeNonGaloisFullHCCharacterInHUFamily
    ctx facts not_Galois
  let hInd := pTypeNonGaloisFullHCCharacterInHUFamily_induce_irreducible
    ctx facts not_Galois
  letI : Invertible (Nat.card HCN : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HCN)).ne')
  have hcard := ClassFunction.card_imset_Ind_irr HCN X hInd
    (pTypeNonGaloisFullHCCharacterInHUFamily_stable
      ctx facts not_Galois)
  calc
    (D.p - 1) ^ D.q = X.card :=
      (pTypeNonGaloisFullHCCharacterInHUFamily_card
        ctx facts not_Galois).symm
    _ = HCN.index *
        (pTypeNonGaloisFullHUCoordinateFamily
          ctx facts not_Galois).card := by
      simpa only [X, pTypeNonGaloisFullHUCoordinateFamily,
        HCN, HC, HU, D] using hcard
    _ = pTypeActionFactorCard D *
        (pTypeNonGaloisFullHUCoordinateFamily
          ctx facts not_Galois).card := by
      rw [pTypeNonGaloisHCInHU_index_eq_actionFactorCard ctx facts]

/-- The full HU coordinate family contains more characters than the constant
subfamily.  The parity obstruction is that `|U/C|` is odd whereas the
remaining power of `p - 1` is even. -/
private theorem fullHUCoordinateFamily_ne_constant
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeNonGaloisFullHUCoordinateFamily ctx facts not_Galois ≠
      pTypeNonGaloisConstantHUFamily ctx facts not_Galois := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : D.C.Normal := D.C_normal
  intro heq
  have hcard := fullHUCoordinateFamily_card_relation
    ctx facts not_Galois
  rw [heq, pTypeNonGaloisConstantHUFamily_card
    ctx facts not_Galois] at hcard
  have hFodd : Odd (Nat.card (Fitting_core M)) :=
    mFT_odd (Fitting_core M)
  have hFactorOdd : Odd (Nat.card (ptypeFCoreFactor ctx)) :=
    odd_natCard_quotient
      ((Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M))
      hFodd
  have hpOdd : Odd D.p := by
    have hH₁Odd : Odd (Nat.card data.H₁) :=
      odd_natCard_subgroup data.H₁ hFactorOdd
    simpa only [data.card_H₁] using hH₁Odd
  have huOdd : Odd (pTypeActionFactorCard D) := by
    change Odd (Nat.card (U ⧸ D.C))
    exact odd_natCard_quotient D.C
      (mFT_odd U)
  have hpPredEven : Even (D.p - 1) :=
    Nat.Odd.sub_odd hpOdd odd_one
  have hpPredPos : 0 < D.p - 1 :=
    Nat.sub_pos_of_lt D.p_prime.one_lt
  have hcancel : (D.p - 1) ^ (D.q - 1) =
      pTypeActionFactorCard D := by
    apply Nat.eq_of_mul_eq_mul_right hpPredPos
    calc
      (D.p - 1) ^ (D.q - 1) * (D.p - 1) =
          (D.p - 1) ^ D.q := by
        rw [← pow_succ, Nat.sub_add_cancel D.q_prime.one_le]
      _ = pTypeActionFactorCard D * (D.p - 1) := hcard
  have hqPredPos : 0 < D.q - 1 :=
    Nat.sub_pos_of_lt D.q_prime.one_lt
  obtain ⟨r, hr⟩ := Nat.exists_eq_succ_of_ne_zero hqPredPos.ne'
  obtain ⟨c, hc⟩ := hpPredEven
  have hpowEven : Even ((D.p - 1) ^ (D.q - 1)) := by
    refine ⟨c * (D.p - 1) ^ r, ?_⟩
    rw [hr, pow_succ, hc]
    ring
  have hpowOdd : Odd ((D.p - 1) ^ (D.q - 1)) := by
    rw [hcancel]
    exact huOdd
  exact (Nat.not_even_iff_odd.mpr hpowOdd) hpowEven

/-- A character in the full HU family but outside the constant subfamily. -/
theorem pTypeNonGalois_exists_nonconstant_HU_character
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    ∃ chi : IrreducibleCharacter
        (pTypeHUInMaximal M (derivedWithin M)) ℂ,
      chi ∈ pTypeNonGaloisFullHUCoordinateFamily
          ctx facts not_Galois ∧
        chi ∉ pTypeNonGaloisConstantHUFamily
          ctx facts not_Galois := by
  classical
  have hnotSubset : ¬ pTypeNonGaloisFullHUCoordinateFamily
      ctx facts not_Galois ⊆
        pTypeNonGaloisConstantHUFamily ctx facts not_Galois := by
    intro hsubset
    apply fullHUCoordinateFamily_ne_constant ctx facts not_Galois
    exact Finset.Subset.antisymm hsubset
      (pTypeNonGaloisConstantHUFamily_subset_full
        ctx facts not_Galois)
  by_contra hnone
  apply hnotSubset
  intro chi hchi
  by_contra hchiConst
  exact hnone ⟨chi, hchi, hchiConst⟩

/-! ## Ambient induction -/

/-- Outside the constant HU family, a full coordinate character induces
irreducibly to the ambient maximal subgroup. -/
theorem pTypeNonGaloisHUCoordinateCharacter_induce_irreducible_of_not_constant
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
    pTypeNonGaloisHUCoordinateCharacter
        ctx facts not_Galois lambda hlambda ∉
      pTypeNonGaloisConstantHUFamily ctx facts not_Galois →
    let HU := pTypeHUInMaximal M (derivedWithin M)
    IsIrreducibleCharacter M ℂ
      (ClassFunction.induce HU
        (pTypeNonGaloisHUCoordinateCharacter
          ctx facts not_Galois lambda hlambda : ClassFunction HU ℂ)) := by
  classical
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda hnotConstant
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ : Subgroup HU :=
    ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
  let xiHU : IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisHUCoordinateCharacter
      ctx facts not_Galois lambda hlambda
  by_contra hReducible
  have hInLayer : ClassFunction.induce HU
      (xiHU : ClassFunction HU ℂ) ∈
        pTypeReducibleLayer HU H H₀ := by
    rw [pTypeReducibleLayer, Finset.mem_filter]
    refine ⟨seqIndP.mpr ⟨xiHU, ?_, rfl⟩, hReducible⟩
    exact pTypeNonGaloisHUCoordinateCharacter_mem_Iirr_kerD
      ctx facts not_Galois lambda hlambda
  have hConstantAmbient : ClassFunction.induce HU
      (xiHU : ClassFunction HU ℂ) ∈
        pTypeNonGaloisConstantAmbientFamily ctx facts not_Galois := by
    rw [pTypeNonGaloisConstantAmbientFamily_eq_reducibleLayer
      ctx facts not_Galois]
    exact hInLayer
  rw [pTypeNonGaloisConstantAmbientFamily] at hConstantAmbient
  obtain ⟨mu, _hmuUniv, hmuImage⟩ :=
    Finset.mem_image.mp hConstantAmbient
  let hmu : (mu : MulChar data.H₁ ℂ) ≠ 1 :=
    (mem_pTypeNontrivialMulChars
      (Q := data.H₁) (mu : MulChar data.H₁ ℂ)).mp mu.property
  have hIndEq : ClassFunction.induce HU
        (xiHU : ClassFunction HU ℂ) =
      ClassFunction.induce HU
        (pTypeNonGaloisConstantHUCharacter
          ctx facts not_Galois mu hmu : ClassFunction HU ℂ) := by
    simpa [pTypeNonGaloisConstantAmbientCharacterFromIndex,
      pTypeNonGaloisConstantHUCharacterFromIndex, xiHU, hmu] using
        hmuImage.symm
  have hxiEq :=
    pTypeNonGaloisHUCoordinateCharacter_eq_constant_of_ambientInduce_eq
      ctx facts not_Galois lambda hlambda mu hmu hIndEq
  apply hnotConstant
  rw [pTypeNonGaloisConstantHUFamily]
  refine Finset.mem_image.mpr ⟨mu, Finset.mem_univ mu, ?_⟩
  simpa [pTypeNonGaloisConstantHUCharacterFromIndex, hmu] using hxiEq.symm

/-- Every reducible member of the `H₀` layer already has the direct
induced-linear description required in clause (b). -/
theorem pTypeNonGalois_reducibleLayer_induced
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    ∀ zeta ∈ pTypeReducibleLayer HU H H₀,
      pTypeIsIndHC HU H H₀C HC D.q
        (pTypeActionFactorCard D) zeta := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  intro zeta hzeta
  have hzetaFamily : zeta ∈
      pTypeNonGaloisConstantAmbientFamily ctx facts not_Galois := by
    rw [pTypeNonGaloisConstantAmbientFamily_eq_reducibleLayer
      ctx facts not_Galois]
    exact hzeta
  rw [pTypeNonGaloisConstantAmbientFamily] at hzetaFamily
  obtain ⟨lambda, _hlambdaUniv, hlambdaImage⟩ :=
    Finset.mem_image.mp hzetaFamily
  let hlambda : (lambda : MulChar data.H₁ ℂ) ≠ 1 :=
    (mem_pTypeNontrivialMulChars
      (Q := data.H₁) (lambda : MulChar data.H₁ ℂ)).mp
        lambda.property
  let xiHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois (fun _ ↦ (lambda : MulChar data.H₁ ℂ))
  have hlinear : pTypeIsLinearCharacter xiHC :=
    pTypeNonGaloisHCCoordinateCharacter_linear
      ctx facts not_Galois (fun _ ↦ (lambda : MulChar data.H₁ ℂ))
  have hdirect :
      pTypeNonGaloisConstantAmbientCharacterFromIndex
          ctx facts not_Galois lambda =
        ClassFunction.induce HC (xiHC : ClassFunction HC ℂ) := by
    simpa [pTypeNonGaloisConstantAmbientCharacterFromIndex,
      pTypeNonGaloisConstantHUCharacterFromIndex, xiHC, hlambda] using
        (pTypeNonGaloisConstantAmbientInduce_eq_direct
          ctx facts not_Galois (lambda : MulChar data.H₁ ℂ) hlambda)
  have hind : zeta = ClassFunction.induce HC
      (xiHC : ClassFunction HC ℂ) :=
    hlambdaImage.symm.trans hdirect
  have hxiOne : xiHC 1 = 1 := by
    rw [IrreducibleCharacter.apply_one_eq_finrank]
    change ((pTypeIrreducibleDegree xiHC : ℕ) : ℂ) = 1
    rw [hlinear]
    norm_num
  rw [pTypeIsIndHC]
  refine ⟨?_, (pType_nb_redM_H0 ctx facts).2 zeta hzeta, ?_⟩
  · calc
      zeta 1 = ClassFunction.induce HC
          (xiHC : ClassFunction HC ℂ) 1 := by rw [hind]
      _ = (HC.index : ℂ) * xiHC 1 :=
        ClassFunction.induce_one HC _
      _ = ((D.q * pTypeActionFactorCard D : ℕ) : ℂ) := by
        rw [pTypeNonGaloisHCInMaximal_index ctx facts,
          hxiOne, mul_one]
  · exact ⟨xiHC, hlinear, hind⟩

set_option maxHeartbeats 800000 in
/-- Induction through `HU` agrees with direct induction of the underlying
linear coordinate character from `HC`.  Keeping this transitivity step
opaque prevents the final existence proof from repeatedly unfolding the
coordinate construction. -/
private theorem huCoordinate_induce_eq_hcCoordinate
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)
    ClassFunction.induce HU
        (pTypeNonGaloisHUCoordinateCharacter
          ctx facts not_Galois lambda hlambda : ClassFunction HU ℂ) =
      ClassFunction.induce HC
        (pTypeNonGaloisHCCoordinateCharacter
          ctx facts not_Galois lambda : ClassFunction HC ℂ) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  let xiHU := pTypeNonGaloisHUCoordinateCharacter
    ctx facts not_Galois lambda hlambda
  let xiHC := pTypeNonGaloisHCCoordinateCharacter
    ctx facts not_Galois lambda
  let xiHCN := pTypeNonGaloisHCCoordinateCharacterInHU
    ctx facts not_Galois lambda
  have hNested : (xiHCN : ClassFunction HCN ℂ) =
      ClassFunction.toSubgroupOf HC HU hHC
        (xiHC : ClassFunction HC ℂ) := by
    ext x
    rw [pTypeNonGaloisHCCoordinateCharacterInHU_apply,
      ClassFunction.toSubgroupOf_apply]
  calc
    ClassFunction.induce HU (xiHU : ClassFunction HU ℂ) =
        ClassFunction.induce HU
          (ClassFunction.induce HCN
            (xiHCN : ClassFunction HCN ℂ)) := by
      rw [pTypeNonGaloisHUCoordinateCharacter_coe]
    _ = ClassFunction.induce HC (xiHC : ClassFunction HC ℂ) :=
      calc
        ClassFunction.induce HU
            (ClassFunction.induce HCN
              (xiHCN : ClassFunction HCN ℂ)) =
            ClassFunction.induce HU
              (ClassFunction.induce HCN
                (ClassFunction.toSubgroupOf HC HU hHC
                  (xiHC : ClassFunction HC ℂ))) := by
          rw [hNested]
        _ = ClassFunction.induce HC (xiHC : ClassFunction HC ℂ) :=
          pTypeNonGaloisHCCoordinateCharacter_induce_trans
            ctx facts not_Galois lambda

/-- Package any nonconstant coordinate family as the irreducible ambient
character required by clause (c). -/
private theorem exists_induced_irreducible_of_nonconstant_coordinate
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
    pTypeNonGaloisHUCoordinateCharacter
        ctx facts not_Galois lambda hlambda ∉
      pTypeNonGaloisConstantHUFamily ctx facts not_Galois →
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    ∃ chi : IrreducibleCharacter M ℂ,
      pTypeIsIndHC HU H H₀C HC D.q
        (pTypeActionFactorCard D) (chi : ClassFunction M ℂ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda hnotConstant
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀C : Subgroup HU := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let xiHU : IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisHUCoordinateCharacter
      ctx facts not_Galois lambda hlambda
  have hirr : IsIrreducibleCharacter M ℂ
      (ClassFunction.induce HU (xiHU : ClassFunction HU ℂ)) :=
    pTypeNonGaloisHUCoordinateCharacter_induce_irreducible_of_not_constant
      ctx facts not_Galois lambda hlambda hnotConstant
  let chi : IrreducibleCharacter M ℂ :=
    ⟨ClassFunction.induce HU (xiHU : ClassFunction HU ℂ), hirr⟩
  let xiHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter ctx facts not_Galois lambda
  have hlinear : pTypeIsLinearCharacter xiHC :=
    pTypeNonGaloisHCCoordinateCharacter_linear
      ctx facts not_Galois lambda
  have hdirect : ClassFunction.induce HU
        (xiHU : ClassFunction HU ℂ) =
      ClassFunction.induce HC (xiHC : ClassFunction HC ℂ) :=
    huCoordinate_induce_eq_hcCoordinate
      ctx facts not_Galois lambda hlambda
  have hxiOne : xiHC 1 = 1 := by
    rw [IrreducibleCharacter.apply_one_eq_finrank]
    change ((pTypeIrreducibleDegree xiHC : ℕ) : ℂ) = 1
    rw [hlinear]
    norm_num
  refine ⟨chi, ?_⟩
  rw [pTypeIsIndHC]
  refine ⟨?_, ?_, ?_⟩
  · change ClassFunction.induce HU
        (xiHU : ClassFunction HU ℂ) 1 =
      ((D.q * pTypeActionFactorCard D : ℕ) : ℂ)
    calc
      ClassFunction.induce HU (xiHU : ClassFunction HU ℂ) 1 =
          ClassFunction.induce HC (xiHC : ClassFunction HC ℂ) 1 := by
        rw [hdirect]
      _ = (HC.index : ℂ) * xiHC 1 :=
        ClassFunction.induce_one HC _
      _ = ((D.q * pTypeActionFactorCard D : ℕ) : ℂ) := by
        rw [pTypeNonGaloisHCInMaximal_index ctx facts,
          hxiOne, mul_one]
  · change ClassFunction.induce HU
        (xiHU : ClassFunction HU ℂ) ∈
      seqIndD (k := ℂ) HU H H₀C
    apply seqIndP.mpr
    refine ⟨xiHU, ?_, rfl⟩
    exact pTypeNonGaloisHUCoordinateCharacter_mem_Iirr_kerD_H0C
      ctx facts not_Galois lambda hlambda
  · exact ⟨xiHC, hlinear, hdirect⟩

/-- Clause (c): some ambient irreducible character is induced directly from
a linear coordinate character of `HC` and lies in the required Dade layer. -/
theorem pTypeNonGalois_exists_induced_irreducible
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    ∃ chi : IrreducibleCharacter M ℂ,
      pTypeIsIndHC HU H H₀C HC D.q
        (pTypeActionFactorCard D) (chi : ClassFunction M ℂ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀C : Subgroup HU := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let X := pTypeNonGaloisFullHCCharacterInHUFamily
    ctx facts not_Galois
  let hInd := pTypeNonGaloisFullHCCharacterInHUFamily_induce_irreducible
    ctx facts not_Galois
  obtain ⟨xiSelected, hxiFull, hxiNotConstant⟩ :=
    pTypeNonGalois_exists_nonconstant_HU_character
      ctx facts not_Galois
  rw [pTypeNonGaloisFullHUCoordinateFamily] at hxiFull
  obtain ⟨source, _hsourceUniv, hsourceImage⟩ :=
    Finset.mem_image.mp hxiFull
  have hsourceMem : source.1 ∈
      pTypeNonGaloisFullHCCharacterInHUFamily
        ctx facts not_Galois := by
    simpa only [X] using source.property
  change source.1 ∈
      (Finset.univ :
        Finset (PTypeNonGaloisCoordinateFamilyIndex data)).image
        (pTypeNonGaloisFullHCCharacterInHUFromIndex
          ctx facts not_Galois) at hsourceMem
  obtain ⟨f, _hfUniv, hfSource⟩ := Finset.mem_image.mp hsourceMem
  let lambda : W₁ → MulChar data.H₁ ℂ :=
    fun w ↦ (f w : MulChar data.H₁ ℂ)
  have hlambda : ∀ w, lambda w ≠ 1 := fun w ↦
    (mem_pTypeNontrivialMulChars
      (Q := data.H₁) (f w : MulChar data.H₁ ℂ)).mp (f w).property
  let xiHU : IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisHUCoordinateCharacter
      ctx facts not_Galois lambda hlambda
  have hxiEq : xiSelected = xiHU := by
    apply Subtype.ext
    calc
      (xiSelected : ClassFunction HU ℂ) =
          (ClassFunction.induceIrreducibleOn HCN X hInd source :
            ClassFunction HU ℂ) :=
        congrArg (fun chi : IrreducibleCharacter HU ℂ ↦
          (chi : ClassFunction HU ℂ)) hsourceImage.symm
      _ = ClassFunction.induce HCN
          (source.1 : ClassFunction HCN ℂ) := rfl
      _ = ClassFunction.induce HCN
          (pTypeNonGaloisFullHCCharacterInHUFromIndex
            ctx facts not_Galois f : ClassFunction HCN ℂ) := by
        rw [hfSource]
      _ = (xiHU : ClassFunction HU ℂ) := rfl
  have hxiNotConstant' : xiHU ∉
      pTypeNonGaloisConstantHUFamily ctx facts not_Galois := by
    intro hxi
    apply hxiNotConstant
    rw [hxiEq]
    exact hxi
  exact exists_induced_irreducible_of_nonconstant_coordinate
    ctx facts not_Galois lambda hlambda hxiNotConstant'

end PTypeNonGaloisClauseCInternal

end

end Submission.OddOrder.PF
