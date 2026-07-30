import Submission.OddOrder.PF.Section09.PTypeNonGaloisFixedDegree
import Submission.OddOrder.PF.Section09.PTypeNonGaloisClauseC
import Submission.OddOrder.PF.Section09.PTypeNonGaloisTwistInduction
import Submission.OddOrder.PF.Section09.PTypeNonGaloisTwoCoordinate

/-!
# Peterfalvi Section 9: the non-Galois character conclusion

This module packages the completed fixed-degree, reducible-layer,
induced-character, and twist-counting phases as Peterfalvi (9.8).  The
two-coordinate construction is imported alongside the four clauses so that
the completed non-Galois branch exposes the character needed later in Section
9 through the same dependency boundary.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open scoped Classical

universe u

/-! ## The four conclusions of Peterfalvi (9.8) -/

/-- Proposition-valued form of the four clauses of
`typeP_nonGalois_characters`.

`a` is the index of the centralizer in `U` of the prime-order normal factor
selected by `typeP_Galois_Pn`. -/
structure PTypeNonGaloisCharactersConclusion
    {M : Type u} [Group M] [Fintype M]
    (HU : Subgroup M) (H H₀ H₀C H₀U' : Subgroup HU)
    (HC U U' : Subgroup M) (p q u a : ℕ) : Prop where
  /-- Clause (a): the non-Galois centralizer index divides every degree in
  `X_ H0`. -/
  fixed_degree_divisibility :
    ∀ chi ∈ Iirr_kerD (k := ℂ) H H₀,
      a ∣ pTypeIrreducibleDegree chi

  /-- First half of clause (b): there are `p - 1` reducible characters in
  the layer `S_ H0`. -/
  reducible_layer_card :
    (pTypeReducibleLayer HU H H₀).card = p - 1

  /-- Second half of clause (b): every member of `mu_` is induced from a
  linear character of `HC`. -/
  reducible_layer_induced :
    ∀ zeta ∈ pTypeReducibleLayer HU H H₀,
      pTypeIsIndHC HU H H₀C HC q u zeta

  /-- Clause (c): at least one irreducible character of `M` has the same
  induced-linear description. -/
  exists_induced_irreducible :
    ∃ chi : IrreducibleCharacter M ℂ,
      pTypeIsIndHC HU H H₀C HC q u
        (chi : ClassFunction M ℂ)

  /-- Divisibility assertion in clause (d). -/
  lower_denominator_dvd :
    pTypeNonGaloisLowerDenominator a U' ∣
      pTypeNonGaloisLowerNumerator p U

  /-- Counting assertion in clause (d). -/
  lower_count_bound :
    pTypeNonGaloisLowerNumerator p U /
        pTypeNonGaloisLowerDenominator a U' ≤
      pTypeNonGaloisDegreeCount HU H H₀U' q a

set_option maxHeartbeats 800000 in
/-- Peterfalvi (9.8): all four non-Galois P-type character conclusions in
the canonical F-core factor-action model. -/
theorem typeP_nonGalois_characters
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {L U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext L U W W₁ W₂)
    (not_Galois :
      ¬ typeP_Galois
        (Ptype_factor_action ctx (Ptype_Fcore_factor_facts ctx))) :
    let facts := Ptype_Fcore_factor_facts ctx
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let hUL : U ≤ L :=
      ctx.typeP.2.1.2.1.trans ctx.typeP.1.2.2.2.1
    PTypeNonGaloisCharactersConclusion
      (pTypeHUInMaximal L (derivedWithin L))
      (pTypeHInDerived L (derivedWithin L) (Fitting_core L))
      (pTypeH0InDerived L (derivedWithin L)
        (Ptype_Fcore_kernel ctx))
      (pTypeH0CInDerived L (derivedWithin L)
        (Ptype_Fcore_kernel ctx) U W₁ D)
      (pTypeH0DerivedComplementInDerived L (derivedWithin L)
        (Ptype_Fcore_kernel ctx) U)
      (pTypeHCInMaximal L (Fitting_core L) U W₁ D)
      (U.subgroupOf L)
      (pTypeDerivedComplementInMaximal (Subgroup.inclusion hUL))
      D.p D.q (pTypeActionFactorCard D)
      (pTypeNonGaloisIndex hD not_Galois) := by
  let facts := Ptype_Fcore_factor_facts ctx
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let hUL : U ≤ L :=
    ctx.typeP.2.1.2.1.trans ctx.typeP.1.2.2.2.1
  refine
    { fixed_degree_divisibility := ?_
      reducible_layer_card := ?_
      reducible_layer_induced := ?_
      exists_induced_irreducible := ?_
      lower_denominator_dvd := ?_
      lower_count_bound := ?_ }
  · exact pTypeNonGalois_fixed_degree_divisibility
      ctx facts not_Galois
  · exact
      (pType_nb_redM_H0
        (M := L) (U := U) (W := W) (W₁ := W₁) (W₂ := W₂)
        ctx facts).1
  · exact
      PTypeNonGaloisClauseCInternal.pTypeNonGalois_reducibleLayer_induced
        ctx facts not_Galois
  · exact
      PTypeNonGaloisClauseCInternal.pTypeNonGalois_exists_induced_irreducible
        ctx facts not_Galois
  · exact pTypeNonGaloisLowerDenominator_dvd_mapped
      hUL hD not_Galois
  · exact
      PTypeNonGaloisTwistInductionInternal.pTypeNonGalois_lower_count_bound_mapped
        ctx facts not_Galois

end

end Submission.OddOrder.PF
