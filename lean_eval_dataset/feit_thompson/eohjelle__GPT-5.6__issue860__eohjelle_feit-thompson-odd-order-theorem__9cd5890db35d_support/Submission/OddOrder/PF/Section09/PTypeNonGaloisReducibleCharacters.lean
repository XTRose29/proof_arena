import Submission.OddOrder.PF.Section09.PTypeNonGaloisHUFamily
import Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer

/-!
# Peterfalvi Section 9: convergence of the non-Galois reducible family

This module identifies the ambient inductions of the nonprincipal constant
coordinate characters with the complete reducible layer attached to the
F-core kernel.  The resulting description is the bridge from the explicit
character family on `HU` to the numerical and induction statements used in
the non-Galois conclusion.
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

universe u

namespace PTypeNonGaloisReducibleCharactersInternal

/-- Induction of a constant-coordinate character through `HU` agrees with
direct induction of its linear `HC` source. -/
theorem pTypeNonGaloisConstantAmbientInduce_eq_direct
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
    ∀ (lambda : MulChar data.H₁ ℂ) (hlambda : lambda ≠ 1),
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)
    let xiHU := pTypeNonGaloisConstantHUCharacter
      ctx facts not_Galois lambda hlambda
    let xiHC := pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois (fun _ ↦ lambda)
    ClassFunction.induce HU (xiHU : ClassFunction HU ℂ) =
      ClassFunction.induce HC (xiHC : ClassFunction HC ℂ) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
    (Ptype_factor_action ctx facts)
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  let xiHC := pTypeNonGaloisHCCoordinateCharacter
    ctx facts not_Galois (fun _ ↦ lambda)
  let xiHCN := pTypeNonGaloisHCCoordinateCharacterInHU
    ctx facts not_Galois (fun _ ↦ lambda)
  change ClassFunction.induce HU
      (pTypeNonGaloisHUCoordinateCharacter
        ctx facts not_Galois (fun _ ↦ lambda) (fun _ ↦ hlambda) :
          ClassFunction HU ℂ) =
    ClassFunction.induce HC (xiHC : ClassFunction HC ℂ)
  have hNested : (xiHCN : ClassFunction HCN ℂ) =
      ClassFunction.toSubgroupOf HC HU hHC
        (xiHC : ClassFunction HC ℂ) := by
    ext x
    rw [pTypeNonGaloisHCCoordinateCharacterInHU_apply,
      ClassFunction.toSubgroupOf_apply]
  calc
    ClassFunction.induce HU
        (pTypeNonGaloisHUCoordinateCharacter
          ctx facts not_Galois (fun _ ↦ lambda) (fun _ ↦ hlambda) :
            ClassFunction HU ℂ) =
        ClassFunction.induce HU
          (ClassFunction.induce HCN
            (xiHCN : ClassFunction HCN ℂ)) := by
      rw [pTypeNonGaloisHUCoordinateCharacter_coe]
    _ = ClassFunction.induce HU
        (ClassFunction.induce HCN
          (ClassFunction.toSubgroupOf HC HU hHC
            (xiHC : ClassFunction HC ℂ))) := by
      rw [hNested]
    _ = ClassFunction.induce HC (xiHC : ClassFunction HC ℂ) :=
      pTypeNonGaloisHCCoordinateCharacter_induce_trans
        ctx facts not_Galois (fun _ ↦ lambda)

/-- The ambient induction indexed by a nonprincipal scalar character. -/
noncomputable def pTypeNonGaloisConstantAmbientCharacterFromIndex
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
    ↑(pTypeNontrivialMulChars data.H₁) → ClassFunction M ℂ := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda
  exact ClassFunction.induce
    (pTypeHUInMaximal M (derivedWithin M))
    (pTypeNonGaloisConstantHUCharacterFromIndex
      ctx facts not_Galois lambda :
        ClassFunction (pTypeHUInMaximal M (derivedWithin M)) ℂ)

/-- Distinct nonprincipal scalar coordinates remain distinct after ambient
induction. -/
theorem pTypeNonGaloisConstantAmbientCharacterFromIndex_injective
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
    Function.Injective
      (pTypeNonGaloisConstantAmbientCharacterFromIndex
        ctx facts not_Galois) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda mu hInd
  let hlambda : (lambda : MulChar data.H₁ ℂ) ≠ 1 :=
    (mem_pTypeNontrivialMulChars
      (Q := data.H₁) (lambda : MulChar data.H₁ ℂ)).mp
        lambda.property
  let hmu : (mu : MulChar data.H₁ ℂ) ≠ 1 :=
    (mem_pTypeNontrivialMulChars
      (Q := data.H₁) (mu : MulChar data.H₁ ℂ)).mp mu.property
  change ClassFunction.induce
      (pTypeHUInMaximal M (derivedWithin M))
      (pTypeNonGaloisConstantHUCharacter
        ctx facts not_Galois lambda hlambda :
          ClassFunction (pTypeHUInMaximal M (derivedWithin M)) ℂ) =
    ClassFunction.induce
      (pTypeHUInMaximal M (derivedWithin M))
      (pTypeNonGaloisConstantHUCharacter
        ctx facts not_Galois mu hmu :
          ClassFunction (pTypeHUInMaximal M (derivedWithin M)) ℂ) at hInd
  have hHU :=
    pTypeNonGaloisHUCoordinateCharacter_eq_constant_of_ambientInduce_eq
      ctx facts not_Galois (fun _ ↦ (lambda : MulChar data.H₁ ℂ))
        (fun _ ↦ hlambda) (mu : MulChar data.H₁ ℂ) hmu hInd
  change pTypeNonGaloisConstantHUCharacter
      ctx facts not_Galois lambda hlambda =
    pTypeNonGaloisConstantHUCharacter
      ctx facts not_Galois mu hmu at hHU
  apply Subtype.ext
  exact pTypeNonGaloisConstantHUCharacter_eq
    ctx facts not_Galois lambda mu hlambda hmu hHU

/-- The ambient image of the nonprincipal constant-coordinate family. -/
noncomputable def pTypeNonGaloisConstantAmbientFamily
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Finset (ClassFunction M ℂ) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  exact Finset.univ.image
    (pTypeNonGaloisConstantAmbientCharacterFromIndex
      ctx facts not_Galois)

/-- The ambient constant-coordinate image has cardinality `p - 1`. -/
theorem pTypeNonGaloisConstantAmbientFamily_card
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    (pTypeNonGaloisConstantAmbientFamily
      ctx facts not_Galois).card =
        (Ptype_factor_action ctx facts).p - 1 := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  rw [pTypeNonGaloisConstantAmbientFamily,
    Finset.card_image_of_injective _
      (pTypeNonGaloisConstantAmbientCharacterFromIndex_injective
        ctx facts not_Galois),
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    natCard_pTypeNontrivialMulChars, data.card_H₁]

/-- Every constant-coordinate ambient induction belongs to the reducible
F-core-kernel layer. -/
theorem pTypeNonGaloisConstantAmbientFamily_subset_reducibleLayer
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
    pTypeNonGaloisConstantAmbientFamily ctx facts not_Galois ⊆
      pTypeReducibleLayer HU H H₀ := by
  classical
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
  intro zeta hzeta
  change zeta ∈ (Finset.univ :
      Finset ↑(pTypeNontrivialMulChars data.H₁)).image
        (pTypeNonGaloisConstantAmbientCharacterFromIndex
          ctx facts not_Galois) at hzeta
  obtain ⟨lambda, _hlambdaUniv, rfl⟩ := Finset.mem_image.mp hzeta
  let hlambda : (lambda : MulChar data.H₁ ℂ) ≠ 1 :=
    (mem_pTypeNontrivialMulChars
      (Q := data.H₁) (lambda : MulChar data.H₁ ℂ)).mp
        lambda.property
  let xiHU : IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisConstantHUCharacter
      ctx facts not_Galois lambda hlambda
  rw [pTypeReducibleLayer, Finset.mem_filter]
  constructor
  · apply seqIndP.mpr
    refine ⟨xiHU, ?_, rfl⟩
    exact pTypeNonGaloisConstantHUCharacter_mem_Iirr_kerD
      ctx facts not_Galois lambda hlambda
  · simpa [pTypeNonGaloisConstantAmbientCharacterFromIndex,
      pTypeNonGaloisConstantHUCharacterFromIndex,
      pTypeNonGaloisConstantHUCharacter, xiHU, hlambda] using
        (pTypeNonGaloisConstantHUCoordinateCharacter_induce_reducible
          ctx facts not_Galois lambda hlambda)

/-- The explicit constant-coordinate family is the complete reducible layer. -/
theorem pTypeNonGaloisConstantAmbientFamily_eq_reducibleLayer
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
    pTypeNonGaloisConstantAmbientFamily ctx facts not_Galois =
      pTypeReducibleLayer HU H H₀ := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
  apply Finset.eq_of_subset_of_card_le
    (pTypeNonGaloisConstantAmbientFamily_subset_reducibleLayer
      ctx facts not_Galois)
  rw [(pType_nb_redM_H0 ctx facts).1,
    pTypeNonGaloisConstantAmbientFamily_card
      ctx facts not_Galois]

end PTypeNonGaloisReducibleCharactersInternal

end

end Submission.OddOrder.PF
