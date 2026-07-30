import Submission.OddOrder.PF.Section13.FTTypePBoundsFirstThree
import Submission.OddOrder.PF.Section13.FTTypePBoundsNonFitting

/-!
# Peterfalvi Section 13: the complement-kernel ratio

This module derives Peterfalvi (13.10) from the four preceding local mass
bounds.  The proof compares the two type-P members of the exceptional pair,
transports the two normalized-TI supports to the ambient group, and converts
the resulting strict mean inequality to the stated cardinal ratio.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open scoped BigOperators Classical Pointwise IsMulCommutative

universe u

variable {G : Type} [Group G] [Finite G] [IsMinSimpleOddGroup G]
variable {S U W W₁ W₂ : Subgroup G}
variable {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance (priority := 10) boundsRatioFintypeOfFinite
    (X : Type*) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-! The proof is deliberately private apart from the mapped endpoint. -/

/-! ## The paired maximal subgroup and its cardinal data -/

private theorem ftTypePPairedSetup
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    ∃ T : Subgroup G,
      typeP_pair S T W W₁ W₂ defW ∧
        ∃ xdefW : IsInternalDirectProductIn W₂ W₁ W,
          ∃ V : Subgroup G,
            FTTypePSetupContext T V W W₂ W₁ xdefW := by
  obtain ⟨T, pairST, xdefW, V, TtypeP⟩ :=
    FTtypeP_pair_witness defW ctx.maxS ctx.StypeP
  exact ⟨T, pairST, xdefW, V,
    { maxS := pairST.T_maximal
      StypeP := TtypeP }⟩

private theorem ftTypePPairedIndex
    {T V : Subgroup G}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW) :
    ftTypePRightIndex ctxT = ftTypePLeftIndex ctx := by
  unfold ftTypePRightIndex ftTypePLeftIndex
  congr

private theorem ftTypePPairedEta
    {T V : Subgroup G}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW) :
    ftTypePEta10 ctx = ftTypePEta01 ctxT := by
  have hswap :=
    CyclicTIHypothesis.cycTIisoC defW xdefW
      ctx.primeDade.prDade_cycTI ctxT.primeDade.prDade_cycTI
      (ftTypePLeftIndex ctx)
      (IrreducibleCharacter.trivial : IrreducibleCharacter W₂ ℂ)
  have hmapped := congrArg ctx.targetMap hswap
  simpa only [ftTypePEta10, ftTypePEta01, FTTypePSetupContext.eta,
    CyclicTIIsometryData.cyclicTIImage,
    CyclicTIIsometryData.cyclicTISourceIrreducible,
    CyclicTIHypothesis.cyclicTIIsometry,
    ftTypePPairedIndex ctx ctxT] using hmapped

private theorem ftTypePSemidirectCard
    {A B K : Subgroup G}
    (h : IsInternalSemidirectProductIn A B K) :
    Nat.card A * Nat.card B = Nat.card K := by
  simpa only [
    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq h.1,
    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq h.2.1] using
      h.2.2.2.card_mul

private theorem ftTypePCoreCard
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card ctx.P = ctx.p ^ ctx.q :=
  (FTtypeP_facts ctx).2.2.2.2.2.1

private theorem ftTypePDerivedCard
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card ctx.P * Nat.card U = Nat.card ctx.PU :=
  ftTypePSemidirectCard ctx.StypeP.2.1.2.2.2

private theorem ftTypePMaximalCard
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card ctx.PU * ctx.q = Nat.card S := by
  simpa only [FTTypePSetupContext.q] using
    ftTypePSemidirectCard ctx.StypeP.1.2.2.2

private theorem ftTypePComplementCard
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card U = ctx.u * Nat.card ctx.C := by
  have hsubgroup : Nat.card ctx.CInU = Nat.card ctx.C :=
    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      (centralizerWithin_le_left U ctx.P)
  calc
    Nat.card U = ctx.CInU.index * Nat.card ctx.CInU :=
      ctx.CInU.index_mul_card.symm
    _ = ctx.u * Nat.card ctx.C := by rw [hsubgroup]

private theorem ftTypePSetupCardFormula
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    Nat.card S = ctx.p ^ ctx.q * (ctx.u * Nat.card ctx.C) * ctx.q := by
  calc
    Nat.card S = Nat.card ctx.PU * ctx.q :=
      (ftTypePMaximalCard ctx).symm
    _ = (Nat.card ctx.P * Nat.card U) * ctx.q := by
      rw [ftTypePDerivedCard ctx]
    _ = ctx.p ^ ctx.q * (ctx.u * Nat.card ctx.C) * ctx.q := by
      rw [ftTypePCoreCard ctx, ftTypePComplementCard ctx]

private theorem ftTypePFittingEqCoreOfCentralizerEqBot
    {T V : Subgroup G}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (hC : ctxT.C = ⊥) :
    ctxT.H = ctxT.P := by
  simpa [hC] using
    (FTContextInternal.directProduct_sup_eq8
      (typeP_context T V W W₂ W₁ xdefW
        ctxT.StypeP).fitting_decomposition).symm

private theorem ftTypePAmbientCardOfCentralizerEqBot
    {T V : Subgroup G}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (hC : ctxT.C = ⊥) :
    Nat.card V = ctxT.u := by
  have hCInV : ctxT.CInU = ⊥ := by
    apply le_antisymm
    · intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      apply Subgroup.mem_bot.mp
      rw [← hC]
      exact hx
    · exact bot_le
  change Nat.card V = ctxT.CInU.index
  rw [hCInV, Subgroup.index_bot]

/-! ## The numerical conversion -/

private theorem ftTypePRatioArithmetic
    (p q u c v : ℕ)
    (hp : 0 < p) (hq : 1 < q) (hu : 0 < u) (hc : 0 < c)
    (hv : 0 < v)
    (hvFactor :
      (v : ℝ) * ((q - 1 : ℕ) : ℝ) = (q : ℝ) ^ p - 1)
    (hraw :
      ((q : ℝ) ^ p * (v : ℝ) - (v : ℝ) ^ 2 -
          ((q : ℝ) ^ p - 1)) /
          ((q : ℝ) ^ p * (v : ℝ) * (p : ℝ)) <
        ((u : ℝ) * (q : ℝ)) ^ 2 /
          ((p : ℝ) ^ q * ((u : ℝ) * (c : ℝ)) * (q : ℝ))) :
    let qm1 : ℝ := (q - 1 : ℕ)
    (1 - qm1⁻¹ - qm1 / (q : ℝ) ^ p +
        (qm1 * (q : ℝ) ^ p)⁻¹) *
          (p : ℝ) ^ (q - 1) / (q : ℝ) <
      (u : ℝ) / (c : ℝ) := by
  let P : ℝ := p
  let Q : ℝ := q
  let U : ℝ := u
  let C : ℝ := c
  let V : ℝ := v
  let qm1 : ℝ := (q - 1 : ℕ)
  have hP : 0 < P := by
    change (0 : ℝ) < (p : ℝ)
    exact_mod_cast hp
  have hQ : 0 < Q := by
    change (0 : ℝ) < (q : ℝ)
    exact_mod_cast Nat.zero_lt_of_lt hq
  have hU : 0 < U := by
    change (0 : ℝ) < (u : ℝ)
    exact_mod_cast hu
  have hC : 0 < C := by
    change (0 : ℝ) < (c : ℝ)
    exact_mod_cast hc
  have hV : 0 < V := by
    change (0 : ℝ) < (v : ℝ)
    exact_mod_cast hv
  have hqm1 : 0 < qm1 := by
    dsimp only [qm1]
    exact_mod_cast Nat.sub_pos_of_lt hq
  have hQpow : 0 < Q ^ p := pow_pos hQ p
  have hPpow : 0 < P ^ q := pow_pos hP q
  have hfactor : V * qm1 = Q ^ p - 1 := by
    simpa only [V, qm1, Q] using hvFactor
  let m : ℝ :=
    1 - qm1⁻¹ - qm1 / Q ^ p + (qm1 * Q ^ p)⁻¹
  have hm :
      m = (Q ^ p * V - V ^ 2 - (Q ^ p - 1)) / (Q ^ p * V) := by
    dsimp only [m]
    field_simp [hqm1.ne', hQpow.ne', hV.ne']
    nlinarith [hfactor]
  have hraw' : m / P < U * Q / (P ^ q * C) := by
    have hleft :
        (Q ^ p * V - V ^ 2 - (Q ^ p - 1)) /
            (Q ^ p * V * P) = m / P := by
      rw [hm]
      field_simp [hP.ne', hQpow.ne', hV.ne']
    have hright :
        (U * Q) ^ 2 / (P ^ q * (U * C) * Q) =
          U * Q / (P ^ q * C) := by
      field_simp [hU.ne', hQ.ne', hC.ne', hPpow.ne']
    have hrawLocal :
        (Q ^ p * V - V ^ 2 - (Q ^ p - 1)) /
            (Q ^ p * V * P) <
          (U * Q) ^ 2 / (P ^ q * (U * C) * Q) := by
      simpa only [P, Q, U, C, V] using hraw
    rw [hleft, hright] at hrawLocal
    exact hrawLocal
  have hpow : P ^ q = P ^ (q - 1) * P := by
    calc
      P ^ q = P ^ ((q - 1) + 1) := by congr 1 <;> omega
      _ = P ^ (q - 1) * P := pow_succ _ _
  have hscale : 0 < P ^ q / Q := div_pos hPpow hQ
  calc
    (1 - qm1⁻¹ - qm1 / Q ^ p + (qm1 * Q ^ p)⁻¹) *
          P ^ (q - 1) / Q =
        (m / P) * (P ^ q / Q) := by
      dsimp only [m]
      field_simp [hP.ne', hQ.ne']
      rw [hpow]
      ring
    _ < (U * Q / (P ^ q * C)) * (P ^ q / Q) :=
      mul_lt_mul_of_pos_right hraw' hscale
    _ = U / C := by
      field_simp [hQ.ne', hC.ne', hPpow.ne']

private theorem ftTypePComplKerRatioOfRawBound
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (hirr : lambda ∈ irr_Ind_Fitting S)
    {T V : Subgroup G}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (hpartner :
      ctxT.galoisAlternative ∧ ctxT.C = ⊥ ∧
        ctxT.u = (ctxT.p ^ ctxT.q - 1) / (ctxT.p - 1))
    (hraw :
      ((Nat.card ctxT.PU : ℝ) - (ctxT.u : ℝ) ^ 2 -
          ((Nat.card ctxT.P - 1 : ℕ) : ℝ)) /
          (Nat.card T : ℝ) <
        Complex.normSq (lambda 1) / (Nat.card S : ℝ)) :
    let qm1 : ℝ := (ctx.q - 1 : ℕ)
    (1 - qm1⁻¹ - qm1 / (ctx.q : ℝ) ^ ctx.p +
        (qm1 * (ctx.q : ℝ) ^ ctx.p)⁻¹) *
          (ctx.p : ℝ) ^ (ctx.q - 1) / (ctx.q : ℝ) <
      (ctx.u : ℝ) / (Nat.card ctx.C : ℝ) := by
  have hpPrime : ctx.p.Prime :=
    (FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP).2
  have hqPrime : ctx.q.Prime :=
    (FTtypeP_primes S U W W₁ W₂ defW ctx.maxS ctx.StypeP).1
  have hp : 0 < ctx.p := hpPrime.pos
  have hq : 1 < ctx.q := hqPrime.one_lt
  have hu : 0 < ctx.u :=
    Nat.pos_of_ne_zero ctx.CInU.index_ne_zero_of_finite
  have hc : 0 < Nat.card ctx.C := Nat.card_pos
  have hv : 0 < ctxT.u :=
    Nat.pos_of_ne_zero ctxT.CInU.index_ne_zero_of_finite
  have hswapP : ctxT.p = ctx.q := rfl
  have hswapQ : ctxT.q = ctx.p := rfl
  have hPcardT : Nat.card ctxT.P = ctx.q ^ ctx.p := by
    simpa only [hswapP, hswapQ] using ftTypePCoreCard ctxT
  have hVcard : Nat.card V = ctxT.u :=
    ftTypePAmbientCardOfCentralizerEqBot ctxT hpartner.2.1
  have hPUcardT : Nat.card ctxT.PU = ctx.q ^ ctx.p * ctxT.u := by
    calc
      Nat.card ctxT.PU = Nat.card ctxT.P * Nat.card V :=
        (ftTypePDerivedCard ctxT).symm
      _ = ctx.q ^ ctx.p * ctxT.u := by rw [hPcardT, hVcard]
  have hTcard : Nat.card T = (ctx.q ^ ctx.p * ctxT.u) * ctx.p := by
    calc
      Nat.card T = Nat.card ctxT.PU * ctxT.q :=
        (ftTypePMaximalCard ctxT).symm
      _ = (ctx.q ^ ctx.p * ctxT.u) * ctx.p := by
        rw [hPUcardT, hswapQ]
  have hScard :
      Nat.card S = ctx.p ^ ctx.q * (ctx.u * Nat.card ctx.C) * ctx.q :=
    ftTypePSetupCardFormula ctx
  have hlambdaOne : lambda 1 = ((ctx.u * ctx.q : ℕ) : ℂ) :=
    FTtypeP_Ind_Fitting_1 ctx lambda hirr.2
  have hquotient :
      ctxT.u = (ctx.q ^ ctx.p - 1) / (ctx.q - 1) := by
    simpa only [hswapP, hswapQ] using hpartner.2.2
  have hnU :
      ctxT.u = Submission.OddOrder.BG.AppendixC.nU ctx.q ctx.p := by
    rw [hquotient]
    exact (Submission.OddOrder.BG.AppendixC.nU_eq_div
      ctx.q ctx.p hqPrime.two_le).symm
  have hvFactorNat :
      ctxT.u * (ctx.q - 1) = ctx.q ^ ctx.p - 1 := by
    rw [hnU]
    exact Submission.OddOrder.BG.AppendixC.nU_mul_sub_one
      ctx.q ctx.p hqPrime.one_le
  have hpowSub :
      (((ctx.q ^ ctx.p - 1 : ℕ) : ℝ)) =
        (ctx.q : ℝ) ^ ctx.p - 1 := by
    rw [Nat.cast_sub (one_le_pow₀ hqPrime.one_le),
      Nat.cast_pow, Nat.cast_one]
  have hvFactor :
      (ctxT.u : ℝ) * ((ctx.q - 1 : ℕ) : ℝ) =
        (ctx.q : ℝ) ^ ctx.p - 1 := by
    calc
      (ctxT.u : ℝ) * ((ctx.q - 1 : ℕ) : ℝ) =
          ((ctxT.u * (ctx.q - 1) : ℕ) : ℝ) := by
        rw [Nat.cast_mul]
      _ = ((ctx.q ^ ctx.p - 1 : ℕ) : ℝ) :=
        congrArg (fun n : ℕ ↦ (n : ℝ)) hvFactorNat
      _ = (ctx.q : ℝ) ^ ctx.p - 1 := hpowSub
  have hraw' :
      (((ctx.q : ℝ) ^ ctx.p * (ctxT.u : ℝ) -
          (ctxT.u : ℝ) ^ 2 - ((ctx.q : ℝ) ^ ctx.p - 1)) /
          ((ctx.q : ℝ) ^ ctx.p * (ctxT.u : ℝ) * (ctx.p : ℝ))) <
        (((ctx.u : ℝ) * (ctx.q : ℝ)) ^ 2 /
          ((ctx.p : ℝ) ^ ctx.q *
            ((ctx.u : ℝ) * (Nat.card ctx.C : ℝ)) *
              (ctx.q : ℝ))) := by
    rw [hPUcardT, hTcard, hPcardT, hlambdaOne,
      Complex.normSq_natCast, hScard] at hraw
    norm_num only [Nat.cast_mul, Nat.cast_pow] at hraw
    rw [hpowSub] at hraw
    simpa only [pow_two] using hraw
  exact ftTypePRatioArithmetic ctx.p ctx.q ctx.u (Nat.card ctx.C)
    ctxT.u hp hq hu hc hv hvFactor hraw'

/-! ## Normalized-TI means and the strict raw ratio -/

namespace FTTypePBoundsRatioMeanScratch

/-! ### Finite sets and normalized-TI transport -/

private theorem finiteSet_sum_eq_subtypeSum
    {Q : Type u} [Fintype Q] (A : Set Q) (f : Q → ℝ) :
    (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet A, f x) =
      ∑ x : A, f x := by
  apply Finset.sum_subtype
  intro x
  simp [FTTypePBoundsInfrastructureInternal.finiteSet]

private theorem finiteSet_union
    {Q : Type u} [Fintype Q] (A B : Set Q) :
    FTTypePBoundsInfrastructureInternal.finiteSet (A ∪ B) =
      FTTypePBoundsInfrastructureInternal.finiteSet A ∪
        FTTypePBoundsInfrastructureInternal.finiteSet B := by
  ext x
  simp [FTTypePBoundsInfrastructureInternal.finiteSet]

private theorem finiteSet_insert
    {Q : Type u} [Fintype Q] (x : Q) (A : Set Q) :
    FTTypePBoundsInfrastructureInternal.finiteSet (insert x A) =
      insert x (FTTypePBoundsInfrastructureInternal.finiteSet A) := by
  ext y
  simp [FTTypePBoundsInfrastructureInternal.finiteSet]

private theorem sum_split_set_complement
    {Q : Type u} [Fintype Q] (A : Set Q) (f : Q → ℝ) :
    (∑ x : Q, f x) =
      (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet A, f x) +
        ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet Aᶜ, f x := by
  have h := Finset.sum_filter_add_sum_filter_not
    (s := (Finset.univ : Finset Q)) (p := fun x ↦ x ∈ A) f
  simpa [FTTypePBoundsInfrastructureInternal.finiteSet] using h.symm

private theorem sum_classSupport_normalizedTI
    {Q : Type u} [Group Q] [Fintype Q]
    {A : Set Q} {N : Subgroup Q}
    (hTI : IsNormalizedTI A (⊤ : Subgroup Q) N)
    (f : Q → ℝ)
    (hconj : ∀ g x : Q, f (g * x * g⁻¹) = f x) :
    (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
        (classSupportWithin (⊤ : Subgroup Q) A), f x) =
      (N.index : ℝ) *
        ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet A, f x := by
  let action := subgroupConjugationActionOnAmbient (⊤ : Subgroup Q)
  letI : SMul (⊤ : Subgroup Q) Q := action.toSMul
  letI : MulAction (⊤ : Subgroup Q) Q := action.toMulAction
  letI : MulAction (⊤ : Subgroup Q) (Set Q) := Set.mulActionSet
  have hpart := normalizedTI_classSupport_partition hTI
  change IsSetPartition (MulAction.orbit (⊤ : Subgroup Q) A)
      (classSupportWithin (⊤ : Subgroup Q) A) ∧
    (MulAction.orbit (⊤ : Subgroup Q) A).ncard =
      N.relIndex (⊤ : Subgroup Q) at hpart
  have hblock (B : Set Q)
      (hB : B ∈ MulAction.orbit (⊤ : Subgroup Q) A) :
      (∑ x : B, f x) = ∑ x : A, f x := by
    rcases hB with ⟨g, rfl⟩
    let e : A ≃ (g • A : Set Q) := by
      change A ≃ (MulAction.toPerm g) '' A
      exact Equiv.Set.image (MulAction.toPerm g) A
        (MulAction.toPerm g).injective
    symm
    apply Fintype.sum_equiv e
    intro x
    change f x = f ((g : Q) * (x : Q) * (g : Q)⁻¹)
    exact (hconj (g : Q) (x : Q)).symm
  have horbitCard :
      Fintype.card (MulAction.orbit (⊤ : Subgroup Q) A) = N.index := by
    rw [← Nat.card_eq_fintype_card, Nat.card_coe_set_eq, hpart.2,
      N.relIndex_top_right]
  rw [finiteSet_sum_eq_subtypeSum, finiteSet_sum_eq_subtypeSum]
  calc
    (∑ x : classSupportWithin (⊤ : Subgroup Q) A, f x) =
        ∑ B : MulAction.orbit (⊤ : Subgroup Q) A,
          ∑ x : (B : Set Q), f x := hpart.1.sum_subtype f
    _ = ∑ _B : MulAction.orbit (⊤ : Subgroup Q) A,
          ∑ x : A, f x := by
      apply Finset.sum_congr rfl
      intro B _
      exact hblock (B : Set Q) B.property
    _ = (Fintype.card (MulAction.orbit (⊤ : Subgroup Q) A) : ℝ) *
          ∑ x : A, f x := by
      rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ]
    _ = (N.index : ℝ) * ∑ x : A, f x := by rw [horbitCard]

private theorem mean_classSupport_normalizedTI
    {Q : Type u} [Group Q] [Fintype Q]
    {A : Set Q} {N : Subgroup Q}
    (hTI : IsNormalizedTI A (⊤ : Subgroup Q) N)
    (f : Q → ℝ)
    (hconj : ∀ g x : Q, f (g * x * g⁻¹) = f x) :
    (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
        (classSupportWithin (⊤ : Subgroup Q) A), f x) /
        (Nat.card Q : ℝ) =
      (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet A, f x) /
        (Nat.card N : ℝ) := by
  have hindex : N.index * Nat.card N = Nat.card Q := by
    simpa only [Subgroup.card_top] using N.index_mul_card
  rw [sum_classSupport_normalizedTI hTI f hconj, ← hindex]
  norm_num only [Nat.cast_mul]
  field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne',
    Nat.cast_ne_zero.mpr N.index_ne_zero_of_finite]

/-! ### The four regions -/

private def sharpSupport
    {Q : Type u} [Group Q] (H : Subgroup Q) : Set Q :=
  classSupportWithin (⊤ : Subgroup Q) (subgroupNonidentity H)

private def outsideSupports
    {Q : Type u} [Group Q] (H K : Subgroup Q) : Set Q :=
  (classSupportWithin (⊤ : Subgroup Q) (H : Set Q) ∪
    classSupportWithin (⊤ : Subgroup Q) (K : Set Q))ᶜ

private theorem classSupport_subgroup_eq_insert_sharp
    {Q : Type u} [Group Q] (H : Subgroup Q) :
    classSupportWithin (⊤ : Subgroup Q) (H : Set Q) =
      insert 1 (sharpSupport H) := by
  ext x
  constructor
  · rintro ⟨y, hyH, g, hg, rfl⟩
    by_cases hy : y = 1
    · subst y
      simp
    · exact Set.mem_insert_iff.mpr
        (Or.inr ⟨y, ⟨hyH, hy⟩, g, hg, rfl⟩)
  · intro hx
    rcases Set.mem_insert_iff.mp hx with rfl | ⟨y, hy, g, hg, hgy⟩
    · exact ⟨1, H.one_mem, 1, Subgroup.mem_top 1, by simp⟩
    · exact ⟨y, hy.1, g, hg, hgy⟩

private theorem one_not_mem_sharpSupport
    {Q : Type u} [Group Q] (H : Subgroup Q) :
    (1 : Q) ∉ sharpSupport H := by
  rintro ⟨y, ⟨hyH, hy⟩, g, hg, hgy⟩
  change g⁻¹ * y * g = 1 at hgy
  apply hy
  calc
    y = g * (g⁻¹ * y * g) * g⁻¹ := by group
    _ = 1 := by rw [hgy]; simp

private theorem four_region_sum
    {Q : Type u} [Group Q] [Fintype Q]
    (H K : Subgroup Q)
    (hdisjoint : Disjoint (sharpSupport H) (sharpSupport K))
    (f : Q → ℝ) :
    (∑ x : Q, f x) =
      f 1 +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (sharpSupport H), f x) +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (sharpSupport K), f x) +
        ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports H K), f x := by
  have hsupportUnion :
      classSupportWithin (⊤ : Subgroup Q) (H : Set Q) ∪
          classSupportWithin (⊤ : Subgroup Q) (K : Set Q) =
        insert 1 (sharpSupport H ∪ sharpSupport K) := by
    rw [classSupport_subgroup_eq_insert_sharp H,
      classSupport_subgroup_eq_insert_sharp K]
    ext x
    simp [or_assoc, or_left_comm, or_comm]
  have hone :
      (1 : Q) ∉ FTTypePBoundsInfrastructureInternal.finiteSet
        (sharpSupport H ∪ sharpSupport K) := by
    simp [FTTypePBoundsInfrastructureInternal.finiteSet,
      one_not_mem_sharpSupport]
  have hfinDisjoint :
      Disjoint
        (FTTypePBoundsInfrastructureInternal.finiteSet (sharpSupport H))
        (FTTypePBoundsInfrastructureInternal.finiteSet (sharpSupport K)) := by
    rw [Finset.disjoint_left]
    intro x hxH hxK
    exact Set.disjoint_left.mp hdisjoint
      (by simpa [FTTypePBoundsInfrastructureInternal.finiteSet] using hxH)
      (by simpa [FTTypePBoundsInfrastructureInternal.finiteSet] using hxK)
  have hcovered :
      (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (classSupportWithin (⊤ : Subgroup Q) (H : Set Q) ∪
            classSupportWithin (⊤ : Subgroup Q) (K : Set Q)), f x) =
        f 1 +
          ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (sharpSupport H ∪ sharpSupport K), f x := by
    rw [hsupportUnion, finiteSet_insert, Finset.sum_insert hone]
  have hsharp :
      (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (sharpSupport H ∪ sharpSupport K), f x) =
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (sharpSupport H), f x) +
          ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (sharpSupport K), f x := by
    rw [finiteSet_union, Finset.sum_union hfinDisjoint]
  calc
    (∑ x : Q, f x) =
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (classSupportWithin (⊤ : Subgroup Q) (H : Set Q) ∪
            classSupportWithin (⊤ : Subgroup Q) (K : Set Q)), f x) +
          ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (outsideSupports H K), f x :=
      sum_split_set_complement _ f
    _ = (f 1 +
          ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (sharpSupport H ∪ sharpSupport K), f x) +
          ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (outsideSupports H K), f x := by rw [hcovered]
    _ = _ := by rw [hsharp]; ring

private theorem four_region_mean_normalizedTI
    {Q : Type u} [Group Q] [Fintype Q]
    (H K NH NK : Subgroup Q)
    (hTIH : IsNormalizedTI (subgroupNonidentity H)
      (⊤ : Subgroup Q) NH)
    (hTIK : IsNormalizedTI (subgroupNonidentity K)
      (⊤ : Subgroup Q) NK)
    (hdisjoint : Disjoint (sharpSupport H) (sharpSupport K))
    (f : Q → ℝ)
    (hconj : ∀ g x : Q, f (g * x * g⁻¹) = f x) :
    (∑ x : Q, f x) / (Nat.card Q : ℝ) =
      f 1 / (Nat.card Q : ℝ) +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity H), f x) / (Nat.card NH : ℝ) +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity K), f x) / (Nat.card NK : ℝ) +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports H K), f x) / (Nat.card Q : ℝ) := by
  calc
    (∑ x : Q, f x) / (Nat.card Q : ℝ) =
        f 1 / (Nat.card Q : ℝ) +
          (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (sharpSupport H), f x) / (Nat.card Q : ℝ) +
          (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (sharpSupport K), f x) / (Nat.card Q : ℝ) +
          (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (outsideSupports H K), f x) / (Nat.card Q : ℝ) := by
      rw [four_region_sum H K hdisjoint f]
      ring
    _ = _ := by
      unfold sharpSupport
      rw [mean_classSupport_normalizedTI hTIH f hconj,
        mean_classSupport_normalizedTI hTIK f hconj]

private theorem four_region_card_mean
    {Q : Type u} [Group Q] [Fintype Q]
    (H K NH NK : Subgroup Q)
    (hTIH : IsNormalizedTI (subgroupNonidentity H)
      (⊤ : Subgroup Q) NH)
    (hTIK : IsNormalizedTI (subgroupNonidentity K)
      (⊤ : Subgroup Q) NK)
    (hdisjoint : Disjoint (sharpSupport H) (sharpSupport K)) :
    (1 : ℝ) =
      (Nat.card Q : ℝ)⁻¹ +
        ((FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity H)).card : ℝ) / (Nat.card NH : ℝ) +
        ((FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity K)).card : ℝ) / (Nat.card NK : ℝ) +
        ((FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports H K)).card : ℝ) / (Nat.card Q : ℝ) := by
  have h := four_region_mean_normalizedTI H K NH NK hTIH hTIK
    hdisjoint (fun _ : Q ↦ (1 : ℝ)) (fun _ _ ↦ rfl)
  have hQ : (Nat.card Q : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hNH : (Nat.card NH : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hNK : (Nat.card NK : ℝ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  simpa [Nat.card_eq_fintype_card, div_eq_mul_inv, hQ, hNH, hNK] using h

private theorem normSq_conj_invariant
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : ClassFunction Q ℂ) (g x : Q) :
    Complex.normSq (chi (g * x * g⁻¹)) = Complex.normSq (chi x) := by
  rw [ClassFunction.conj_apply chi g x]

private theorem normSq_four_region
    {Q : Type u} [Group Q] [Fintype Q]
    (H K NH NK : Subgroup Q)
    (hTIH : IsNormalizedTI (subgroupNonidentity H)
      (⊤ : Subgroup Q) NH)
    (hTIK : IsNormalizedTI (subgroupNonidentity K)
      (⊤ : Subgroup Q) NK)
    (hdisjoint : Disjoint (sharpSupport H) (sharpSupport K))
    (chi : ClassFunction Q ℂ) :
    classFunctionNormSq chi =
      Complex.normSq (chi 1) / (Nat.card Q : ℝ) +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity H), Complex.normSq (chi x)) /
            (Nat.card NH : ℝ) +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity K), Complex.normSq (chi x)) /
            (Nat.card NK : ℝ) +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports H K), Complex.normSq (chi x)) /
            (Nat.card Q : ℝ) := by
  calc
    classFunctionNormSq chi =
        (∑ x : Q, Complex.normSq (chi x)) / (Nat.card Q : ℝ) := by
      unfold classFunctionNormSq
      rw [div_eq_mul_inv, mul_comm]
    _ = _ := four_region_mean_normalizedTI H K NH NK hTIH hTIK
      hdisjoint (fun x ↦ Complex.normSq (chi x))
        (normSq_conj_invariant chi)

private theorem finiteSet_subgroupNonidentity_card
    {Q : Type u} [Group Q] [Fintype Q] (H : Subgroup Q) :
    (FTTypePBoundsInfrastructureInternal.finiteSet
      (subgroupNonidentity H)).card = Nat.card H - 1 := by
  have hone : (1 : Q) ∈ (H : Set Q) := H.one_mem
  have hset : subgroupNonidentity H = (H : Set Q) \ {1} := by
    ext x
    simp [subgroupNonidentity, nonidentitySet]
  have hfiniteSetCard :
      (FTTypePBoundsInfrastructureInternal.finiteSet
        (subgroupNonidentity H)).card = (subgroupNonidentity H).ncard := by
    rw [show FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity H) =
        (Set.toFinite (subgroupNonidentity H)).toFinset by
      ext x
      simp [FTTypePBoundsInfrastructureInternal.finiteSet]]
    exact (Set.ncard_eq_toFinset_card _ _).symm
  rw [hfiniteSetCard, hset, Set.ncard_sdiff_singleton_of_mem hone,
    ← Nat.card_coe_set_eq, SetLike.coe_sort_coe]

/-!
The single analytic lemma needed by the source seam.  It combines both
norm-one complement upper bounds with the non-Fitting cover, retaining the
strict identity contribution instead of routing through several intermediate
upper-bound declarations.
-/
private theorem strict_raw_ratio_of_four_bounds
    {Q : Type u} [Group Q] [Fintype Q]
    (H K NH NK : Subgroup Q)
    (hTIH : IsNormalizedTI (subgroupNonidentity H)
      (⊤ : Subgroup Q) NH)
    (hTIK : IsNormalizedTI (subgroupNonidentity K)
      (⊤ : Subgroup Q) NK)
    (hdisjoint : Disjoint (sharpSupport H) (sharpSupport K))
    (chi eta : ClassFunction Q ℂ) (degreeMass partnerMass : ℝ)
    (hchiNorm : classFunctionNormSq chi = 1)
    (hetaNorm : classFunctionNormSq eta = 1)
    (hchiOne : (Nat.card Q : ℝ)⁻¹ ≤
      Complex.normSq (chi 1) / (Nat.card Q : ℝ))
    (hetaOne : (Nat.card Q : ℝ)⁻¹ ≤
      Complex.normSq (eta 1) / (Nat.card Q : ℝ))
    (hchiH : (Nat.card NH : ℝ) - degreeMass ≤
      ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
        (subgroupNonidentity H), Complex.normSq (chi x))
    (hetaH :
      ((FTTypePBoundsInfrastructureInternal.finiteSet
        (subgroupNonidentity H)).card : ℝ) ≤
        ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity H), Complex.normSq (eta x))
    (hetaK : partnerMass ≤
      ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
        (subgroupNonidentity K), Complex.normSq (eta x))
    (hcover :
      ((FTTypePBoundsInfrastructureInternal.finiteSet
        (outsideSupports H K)).card : ℝ) ≤
        ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports H K),
          (Complex.normSq (chi x) + Complex.normSq (eta x))) :
    (partnerMass - ((Nat.card K - 1 : ℕ) : ℝ)) /
        (Nat.card NK : ℝ) <
      degreeMass / (Nat.card NH : ℝ) := by
  have hQpos : (0 : ℝ) < Nat.card Q := Nat.cast_pos.mpr Nat.card_pos
  have hNHpos : (0 : ℝ) < Nat.card NH := Nat.cast_pos.mpr Nat.card_pos
  have hNKpos : (0 : ℝ) < Nat.card NK := Nat.cast_pos.mpr Nat.card_pos
  have hinvQpos : (0 : ℝ) < (Nat.card Q : ℝ)⁻¹ := inv_pos.mpr hQpos
  have hchiDecomp := normSq_four_region H K NH NK hTIH hTIK
    hdisjoint chi
  have hetaDecomp := normSq_four_region H K NH NK hTIH hTIK
    hdisjoint eta
  have hcardDecomp := four_region_card_mean H K NH NK hTIH hTIK
    hdisjoint
  rw [hchiNorm] at hchiDecomp
  rw [hetaNorm] at hetaDecomp
  have hchiHMean :
      1 - degreeMass / (Nat.card NH : ℝ) ≤
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity H), Complex.normSq (chi x)) /
            (Nat.card NH : ℝ) := by
    calc
      1 - degreeMass / (Nat.card NH : ℝ) =
          ((Nat.card NH : ℝ) - degreeMass) /
            (Nat.card NH : ℝ) := by field_simp
      _ ≤ _ := (div_le_div_iff_of_pos_right hNHpos).2 hchiH
  have hetaHMean :
      ((FTTypePBoundsInfrastructureInternal.finiteSet
        (subgroupNonidentity H)).card : ℝ) / (Nat.card NH : ℝ) ≤
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity H), Complex.normSq (eta x)) /
            (Nat.card NH : ℝ) :=
    (div_le_div_iff_of_pos_right hNHpos).2 hetaH
  have hetaKMean : partnerMass / (Nat.card NK : ℝ) ≤
      (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
        (subgroupNonidentity K), Complex.normSq (eta x)) /
          (Nat.card NK : ℝ) :=
    (div_le_div_iff_of_pos_right hNKpos).2 hetaK
  have hchiKNonneg :
      0 ≤
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity K), Complex.normSq (chi x)) /
            (Nat.card NK : ℝ) :=
    div_nonneg
      (Finset.sum_nonneg fun x _ ↦ Complex.normSq_nonneg (chi x))
      hNKpos.le
  have hchiUpper :
      (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
        (outsideSupports H K), Complex.normSq (chi x)) /
          (Nat.card Q : ℝ) ≤
        degreeMass / (Nat.card NH : ℝ) - (Nat.card Q : ℝ)⁻¹ := by
    linarith
  have hetaUpper :
      (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
        (outsideSupports H K), Complex.normSq (eta x)) /
          (Nat.card Q : ℝ) ≤
        ((FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports H K)).card : ℝ) / (Nat.card Q : ℝ) -
          (partnerMass / (Nat.card NK : ℝ) -
            ((FTTypePBoundsInfrastructureInternal.finiteSet
              (subgroupNonidentity K)).card : ℝ) /
                (Nat.card NK : ℝ)) := by
    linarith
  have hcoverMean :
      ((FTTypePBoundsInfrastructureInternal.finiteSet
        (outsideSupports H K)).card : ℝ) / (Nat.card Q : ℝ) ≤
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports H K), Complex.normSq (chi x)) /
            (Nat.card Q : ℝ) +
        (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports H K), Complex.normSq (eta x)) /
            (Nat.card Q : ℝ) := by
    calc
      ((FTTypePBoundsInfrastructureInternal.finiteSet
        (outsideSupports H K)).card : ℝ) / (Nat.card Q : ℝ) =
          ((FTTypePBoundsInfrastructureInternal.finiteSet
            (outsideSupports H K)).card : ℝ) *
              (Nat.card Q : ℝ)⁻¹ := div_eq_mul_inv _ _
      _ ≤ (∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
            (outsideSupports H K),
            (Complex.normSq (chi x) + Complex.normSq (eta x))) *
              (Nat.card Q : ℝ)⁻¹ :=
        mul_le_mul_of_nonneg_right hcover hinvQpos.le
      _ = _ := by
        rw [Finset.sum_add_distrib]
        simp only [div_eq_mul_inv]
        ring
  have hstrict :
      partnerMass / (Nat.card NK : ℝ) -
          ((FTTypePBoundsInfrastructureInternal.finiteSet
            (subgroupNonidentity K)).card : ℝ) / (Nat.card NK : ℝ) <
        degreeMass / (Nat.card NH : ℝ) := by
    linarith
  calc
    (partnerMass - ((Nat.card K - 1 : ℕ) : ℝ)) /
        (Nat.card NK : ℝ) =
      partnerMass / (Nat.card NK : ℝ) -
        ((Nat.card K - 1 : ℕ) : ℝ) / (Nat.card NK : ℝ) := by ring
    _ < degreeMass / (Nat.card NH : ℝ) := by
      simpa only [finiteSet_subgroupNonidentity_card] using hstrict

/-! ### Signed-irreducible adapters -/

private theorem irreducible_isVirtual
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    ClassFunction.IsVirtual (chi : ClassFunction Q ℂ) := by
  refine ⟨Finsupp.single chi 1, ?_⟩
  simp

private theorem irreducible_norm_one
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    classFunctionNormSq (chi : ClassFunction Q ℂ) = 1 := by
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    PTypeCorePairingInternal.pTypeCore_starPairing_eq_pairing_of_virtual
      (irreducible_isVirtual chi) (irreducible_isVirtual chi),
    IrreducibleCharacter.characterPairing_self chi]
  norm_num

private theorem signed_irreducible_norm_one
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) (chi : IrreducibleCharacter Q ℂ)
    (epsilon : ℤ) (hepsilon : IsSign epsilon)
    (hphi : phi = (epsilon : ℂ) • (chi : ClassFunction Q ℂ)) :
    classFunctionNormSq phi = 1 := by
  have hepsilonNorm : Complex.normSq (epsilon : ℂ) = 1 := by
    rcases hepsilon with rfl | rfl <;> norm_num
  have hchi := irreducible_norm_one chi
  rw [hphi]
  unfold classFunctionNormSq at hchi ⊢
  simp only [ClassFunction.smul_apply, smul_eq_mul,
    Complex.normSq_mul, hepsilonNorm, one_mul]
  exact hchi

private theorem irreducible_degree_pos
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    0 < Module.finrank ℂ chi.representation := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  exact Module.finrank_pos

private theorem signed_irreducible_identity_mean_lower
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) (chi : IrreducibleCharacter Q ℂ)
    (epsilon : ℤ) (hepsilon : IsSign epsilon)
    (hphi : phi = (epsilon : ℂ) • (chi : ClassFunction Q ℂ)) :
    (Nat.card Q : ℝ)⁻¹ ≤
      Complex.normSq (phi 1) / (Nat.card Q : ℝ) := by
  have hepsilonNorm : Complex.normSq (epsilon : ℂ) = 1 := by
    rcases hepsilon with rfl | rfl <;> norm_num
  have hvalue := congrArg (fun psi : ClassFunction Q ℂ ↦ psi 1) hphi
  change phi 1 = (epsilon : ℂ) * chi 1 at hvalue
  have hdegree : (1 : ℝ) ≤ Module.finrank ℂ chi.representation := by
    exact_mod_cast irreducible_degree_pos chi
  have hone : (1 : ℝ) ≤ Complex.normSq (phi 1) := by
    rw [hvalue, Complex.normSq_mul, hepsilonNorm, one_mul,
      IrreducibleCharacter.apply_one_eq_finrank,
      Complex.normSq_natCast]
    nlinarith
  have hQpos : (0 : ℝ) < Nat.card Q := Nat.cast_pos.mpr Nat.card_pos
  calc
    (Nat.card Q : ℝ)⁻¹ = 1 / (Nat.card Q : ℝ) := by simp
    _ ≤ Complex.normSq (phi 1) / (Nat.card Q : ℝ) :=
      (div_le_div_iff_of_pos_right hQpos).2 hone

end FTTypePBoundsRatioMeanScratch

open FTTypePBoundsRatioMeanScratch

/-!
The exact private source-specific seam consumed by the final ratio assembly.
It depends only on the four public Section 13 bounds and the already-public
signed-irreducible witnesses from `FTTypePGeneratorBounds`.
-/
private theorem ftTypePStrictRawRatioBound13
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {T V : Subgroup G}
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (lambda : ClassFunction S ℂ)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (hirr : lambda ∈ irr_Ind_Fitting S)
    (tau₁ : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau₁)
    (hTIred : typeP_TIred_coherent ctx tau₁)
    (hdis : Disjoint
      (classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity ctx.H))
      (classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity ctxT.H)))
    (heta : ftTypePEta10 ctx = ftTypePEta01 ctxT)
    (hHT : ctxT.H = ctxT.P) :
    ((Nat.card ctxT.PU : ℝ) - (ctxT.u : ℝ) ^ 2 -
        ((Nat.card ctxT.P - 1 : ℕ) : ℝ)) /
        (Nat.card T : ℝ) <
      Complex.normSq (lambda 1) / (Nat.card S : ℝ) := by
  have hTIH : IsNormalizedTI (subgroupNonidentity ctx.H)
      (⊤ : Subgroup G) S :=
    (compl_of_typeII_IV S U W W₁ W₂ defW ctx.maxS ctx.StypeP
      ctx.notType5).2.2.2
  have hTIK : IsNormalizedTI (subgroupNonidentity ctxT.H)
      (⊤ : Subgroup G) T :=
    (compl_of_typeII_IV T V W W₂ W₁ xdefW ctxT.maxS ctxT.StypeP
      ctxT.notType5).2.2.2
  obtain ⟨chi, epsilon, hepsilon, hchi⟩ :=
    FTTypePGeneratorBoundsInternal.tau1_lambda_eq_signed_irreducible
      ctx tau₁ lambda hcoh hcalS hirr
  obtain ⟨etaIrr, etaSign, hetaSign, hetaIrr⟩ :=
    FTTypePGeneratorBoundsInternal.eta10_eq_signed_irreducible ctx
  have hchiNorm : classFunctionNormSq (tau₁ lambda) = 1 :=
    signed_irreducible_norm_one
      (tau₁ lambda) chi epsilon hepsilon hchi
  have hetaNorm : classFunctionNormSq (ftTypePEta10 ctx) = 1 :=
    signed_irreducible_norm_one
      (ftTypePEta10 ctx) etaIrr etaSign hetaSign hetaIrr
  have hchiOne : (Nat.card G : ℝ)⁻¹ ≤
      Complex.normSq (tau₁ lambda 1) / (Nat.card G : ℝ) :=
    signed_irreducible_identity_mean_lower
      (tau₁ lambda) chi epsilon hepsilon hchi
  have hetaOne : (Nat.card G : ℝ)⁻¹ ≤
      Complex.normSq (ftTypePEta10 ctx 1) / (Nat.card G : ℝ) :=
    signed_irreducible_identity_mean_lower
      (ftTypePEta10 ctx) etaIrr etaSign hetaSign hetaIrr
  have hchiH : (Nat.card S : ℝ) - Complex.normSq (lambda 1) ≤
      ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
        (subgroupNonidentity ctx.H), Complex.normSq (tau₁ lambda x) := by
    simpa only [ftTypePSumNormSq] using
      FTtypeP_sum_Ind_Fitting_lb ctx tau₁ lambda hcoh hirr hcalS
  have hetaH :
      ((FTTypePBoundsInfrastructureInternal.finiteSet
        (subgroupNonidentity ctx.H)).card : ℝ) ≤
        ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity ctx.H), Complex.normSq (ftTypePEta10 ctx x) := by
    simpa only [ftTypePSumNormSq, ftTypePSetCard] using
      FTtypeP_sum_cycTIiso10_lb ctx
  have hetaK :
      (Nat.card ctxT.PU : ℝ) - (ctxT.u : ℝ) ^ 2 ≤
        ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (subgroupNonidentity ctxT.H),
            Complex.normSq (ftTypePEta10 ctx x) := by
    have hpartner := FTtypeP_sum_cycTIiso01_lb ctxT
    rw [← heta] at hpartner
    simpa only [ftTypePSumNormSq] using hpartner
  have hcover :
      ((FTTypePBoundsInfrastructureInternal.finiteSet
        (outsideSupports ctx.H ctxT.H)).card : ℝ) ≤
        ∑ x ∈ FTTypePBoundsInfrastructureInternal.finiteSet
          (outsideSupports ctx.H ctxT.H),
          (Complex.normSq (tau₁ lambda x) +
            Complex.normSq (ftTypePEta10 ctx x)) := by
    simpa only [outsideSupports, ftTypePNonFittingSet, ftTypePSetCard] using
      FTtypeP_sum_nonFitting_lb ctx ctxT.H tau₁ lambda
        hcoh hTIred hcalS hirr
  have hraw := strict_raw_ratio_of_four_bounds
    ctx.H ctxT.H S T hTIH hTIK (by simpa only [sharpSupport] using hdis)
      (tau₁ lambda) (ftTypePEta10 ctx)
      (Complex.normSq (lambda 1))
      ((Nat.card ctxT.PU : ℝ) - (ctxT.u : ℝ) ^ 2)
      hchiNorm hetaNorm hchiOne hetaOne hchiH hetaH hetaK hcover
  simpa only [hHT] using hraw

/-! ## The obstruction supplied by the paired type-P subgroup -/

private theorem partner_pairing_sub_left
    {Q : Type*} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing (a - b) c =
      characterPairing a c - characterPairing b c := by
  change characterPairingLeft (a - b) c = _
  exact map_sub (characterPairingRight c) a b

private theorem partner_pairing_sub_right
    {Q : Type*} [Group Q] [Fintype Q]
    (a b c : ClassFunction Q ℂ) :
    characterPairing a (b - c) =
      characterPairing a b - characterPairing a c := by
  change characterPairingRight (b - c) a = _
  exact map_sub (characterPairingLeft a) b c

private theorem partner_pairing_sum_left
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (f : I → ClassFunction Q ℂ) (a : ClassFunction Q ℂ) :
    characterPairing (∑ i, f i) a =
      ∑ i, characterPairing (f i) a := by
  change characterPairingRight a (∑ i, f i) = _
  exact map_sum (characterPairingRight a) f Finset.univ

private theorem partner_pairing_sum_right
    {Q I : Type*} [Group Q] [Fintype Q] [Fintype I]
    (a : ClassFunction Q ℂ) (f : I → ClassFunction Q ℂ) :
    characterPairing a (∑ i, f i) =
      ∑ i, characterPairing a (f i) := by
  change characterPairingLeft a (∑ i, f i) = _
  exact map_sum (characterPairingLeft a) f Finset.univ

private theorem partner_sub_supported_off_one
    {Q : Type*} [Group Q]
    (phi psi : ClassFunction Q ℂ) (hone : phi 1 = psi 1) :
    phi - psi ∈ ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp [hone]

private theorem partner_dual_sub_supported_off_one
    {Q : Type*} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    (chi : ClassFunction Q ℂ) -
        (IrreducibleCharacter.dual chi : ClassFunction Q ℂ) ∈
      ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp [IrreducibleCharacter.apply_one_eq_finrank]

private theorem partner_orthonormal_pair
    {Q : Type*} [Group Q] [Fintype Q]
    (a b : VirtualCharacter Q ℂ)
    (ha : characterPairing (VirtualCharacter.realize a)
        (VirtualCharacter.realize a) = 1)
    (hb : characterPairing (VirtualCharacter.realize b)
        (VirtualCharacter.realize b) = 1)
    (hab : characterPairing (VirtualCharacter.realize a)
        (VirtualCharacter.realize b) = 0) :
    IntegralLattice.IsOrthonormalPair a b := by
  constructor
  · apply Int.cast_injective (α := ℂ)
    unfold normSq
    simpa only [VirtualCharacter.characterPairing_realize,
      Int.cast_one] using ha
  constructor
  · apply Int.cast_injective (α := ℂ)
    unfold normSq
    simpa only [VirtualCharacter.characterPairing_realize,
      Int.cast_one] using hb
  · apply Int.cast_injective (α := ℂ)
    simpa only [VirtualCharacter.characterPairing_realize,
      Int.cast_zero] using hab

private theorem partner_sharp_inv_stable (H : Subgroup G) :
    IsInvStable
      (classSupportWithin (⊤ : Subgroup G) (subgroupNonidentity H)) := by
  have hinv : ∀ x : G,
      x ∈ classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity H) →
        x⁻¹ ∈ classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity H) := by
    intro x
    rintro ⟨a, ha, g, hg, hax⟩
    change g⁻¹ * a * g = x at hax
    refine ⟨a⁻¹, ⟨H.inv_mem ha.1, inv_ne_one.mpr ha.2⟩,
      g, hg, ?_⟩
    change g⁻¹ * a⁻¹ * g = x⁻¹
    calc
      g⁻¹ * a⁻¹ * g = (g⁻¹ * a * g)⁻¹ := by group
      _ = x⁻¹ := congrArg Inv.inv hax
  intro x
  constructor
  · intro hx
    simpa only [inv_inv] using hinv x⁻¹ hx
  · exact hinv x

private theorem partner_one_not_mem_sharp (H : Subgroup G) :
    (1 : G) ∉
      classSupportWithin (⊤ : Subgroup G) (subgroupNonidentity H) := by
  rintro ⟨a, ha, g, _hg, haOne⟩
  change g⁻¹ * a * g = 1 at haOne
  apply ha.2
  calc
    a = g * (g⁻¹ * a * g) * g⁻¹ := by group
    _ = 1 := by rw [haOne]; group

private theorem partner_induce_supported_on_class_support
    {L : Subgroup G} {A : Set G}
    (alpha : ClassFunction L ℂ)
    (halpha : alpha ∈
      ClassFunction.supportedOn {x : L | (x : G) ∈ A}) :
    ClassFunction.induce L alpha ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G) A) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  rw [ClassFunction.induce_apply_formula]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro y _hy
  split_ifs with hy
  · apply ClassFunction.eq_zero_of_mem_supportedOn halpha
    intro hA
    apply hx
    refine ⟨y⁻¹ * x * y, hA, y⁻¹, Subgroup.mem_top _, ?_⟩
    group
  · rfl

private theorem partner_fitting_supports_disjoint
    {S T U V W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW) :
    Disjoint
      (classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity ctxS.H))
      (classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity ctxT.H)) := by
  rw [Set.disjoint_left]
  intro z hzS hzT
  rcases hzS with ⟨x, hx, g₁, _hg₁, hxz⟩
  rcases hzT with ⟨y, hy, g₂, _hg₂, hyz⟩
  change g₁⁻¹ * x * g₁ = z at hxz
  change g₂⁻¹ * y * g₂ = z at hyz
  let g : G := g₁ * g₂⁻¹
  have hxy : (MulAut.conj g) y = x := by
    rw [MulAut.conj_apply]
    dsimp only [g]
    calc
      (g₁ * g₂⁻¹) * y * (g₁ * g₂⁻¹)⁻¹ =
          g₁ * (g₂⁻¹ * y * g₂) * g₁⁻¹ := by group
      _ = g₁ * z * g₁⁻¹ := by rw [hyz]
      _ = x := by rw [← hxz]; group
  let Qg : Subgroup G := conjugateSubgroup8 ctxT.P g
  have hPTH : ctxT.P ≤ ctxT.H :=
    (typeP_context T V W W₂ W₁ xdefW
      ctxT.StypeP).fitting_decomposition.left_le
  letI : IsMulCommutative ctxT.H := FTtypeP_Fitting_abelian ctxT
  have hQgCentral :
      Qg ≤ centralizerWithin (⊤ : Subgroup G) (Subgroup.zpowers x) := by
    rintro q ⟨q₀, hq₀, rfl⟩
    have hcomm : Commute q₀ y :=
      congrArg Subtype.val
        (mul_comm (⟨q₀, hPTH hq₀⟩ : ctxT.H)
          (⟨y, hy.1⟩ : ctxT.H))
    have hcomm' : Commute ((MulAut.conj g) q₀) x := by
      rw [← hxy]
      exact hcomm.map (MulAut.conj g).toMonoidHom
    refine ⟨Subgroup.mem_top _, ?_⟩
    intro xn hxn
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hxn
    exact (hcomm'.symm.zpow_left n).eq
  obtain ⟨_, _, _, _, _, _, _, _, hTIS, _⟩ := FTtypeP_facts ctxS
  have hxFT : x ∈ FTsupport0 S :=
    Fitting_sub_FTsupp0 ctxS.maxS hx
  have hQgS : Qg ≤ S :=
    hQgCentral.trans (hTIS.centralizerWithin_zpowers_le hxFT)
  have hcardQgDvd : Nat.card Qg ∣ Nat.card S :=
    Subgroup.card_dvd_of_le hQgS
  have hcardQg : Nat.card Qg = Nat.card ctxT.P := by
    dsimp only [Qg, conjugateSubgroup8]
    exact Subgroup.card_map_of_injective (MulAut.conj g).injective
  obtain ⟨_, _, _, _, _, hPcardT, _, _, _, _⟩ := FTtypeP_facts ctxT
  have hPcardT' :
      Nat.card ctxT.P = (Nat.card W₁) ^ Nat.card W₂ := by
    simpa only [FTTypePSetupContext.p,
      FTTypePSetupContext.q] using hPcardT
  have hPowDvdS : (Nat.card W₁) ^ Nat.card W₂ ∣ Nat.card S := by
    rw [← hPcardT', ← hcardQg]
    exact hcardQgDvd
  have hprimes :
      (Nat.card W₁).Prime ∧ (Nat.card W₂).Prime :=
    FTtypeP_pair_primes S T W W₁ W₂ defW pairST
  have hSquareDvdS : (Nat.card W₁) ^ 2 ∣ Nat.card S :=
    (pow_dvd_pow (Nat.card W₁) hprimes.2.two_le).trans hPowDvdS
  rw [← (W₁.subgroupOf S).index_mul_card,
    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      ctxS.primeTI.complement_le_group] at hSquareDvdS
  have hMulDvd :
      Nat.card W₁ * Nat.card W₁ ∣
        Nat.card W₁ * (W₁.subgroupOf S).index := by
    simpa only [pow_two, mul_comm] using hSquareDvdS
  have hqDvdIndex : Nat.card W₁ ∣ (W₁.subgroupOf S).index :=
    (Nat.mul_dvd_mul_iff_left hprimes.1.pos).mp hMulDvd
  have hcop : Nat.Coprime (Nat.card W₁)
      (W₁.subgroupOf S).index := by
    simpa only [
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        ctxS.primeTI.complement_le_group] using
      ctxS.primeTI.complement_hall.coprime_card_index
  exact (Nat.not_coprime_of_dvd_of_dvd hprimes.1.one_lt
    (dvd_refl (Nat.card W₁)) hqDvdIndex) hcop

private theorem partner_difference_tau_supported
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction S ℂ)
    (hphi : phi ∈ ClassFunction.supportedOn
      ((ctx.H.subgroupOf S : Subgroup S) : Set S))
    (hpsi : psi ∈ ClassFunction.supportedOn
      ((ctx.H.subgroupOf S : Subgroup S) : Set S))
    (hone : phi 1 = psi 1) :
    ctx.tau (phi - psi) ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity ctx.H)) := by
  let HInS : Subgroup S := ctx.H.subgroupOf S
  have hdiffOn : phi - psi ∈
      ClassFunction.supportedOn (HInS : Set S) :=
    (ClassFunction.supportedOn (R := ℂ)
      (HInS : Set S)).sub_mem hphi hpsi
  have hdiffSharp : phi - psi ∈
      ClassFunction.supportedOn
        {x : S | (x : G) ∈ subgroupNonidentity ctx.H} := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hxSharp
    by_cases hxOne : x = 1
    · subst x
      simp [hone]
    · apply ClassFunction.eq_zero_of_mem_supportedOn hdiffOn
      intro hxH
      apply hxSharp
      refine ⟨hxH, ?_⟩
      exact fun hxAmbientOne ↦ hxOne (Subtype.ext hxAmbientOne)
  have hdiffA0 : phi - psi ∈
      ClassFunction.supportedOn (ftTypePSupport0InS S) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hxA0
    by_cases hxOne : x = 1
    · subst x
      simp [hone]
    · apply ClassFunction.eq_zero_of_mem_supportedOn hdiffOn
      intro hxH
      apply hxA0
      change (x : G) ∈ FTsupport0 S
      apply Fitting_sub_FTsupp0 ctx.maxS
      refine ⟨hxH, ?_⟩
      exact fun hxAmbientOne ↦ hxOne (Subtype.ext hxAmbientOne)
  obtain ⟨_, _, _, _, _, _, _, _, _, hInduce⟩ := FTtypeP_facts ctx
  rw [hInduce (phi - psi) hdiffA0]
  exact partner_induce_supported_on_class_support (phi - psi) hdiffSharp

private theorem partner_fitting_difference_tau_supported
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction S ℂ)
    (hphi : phi ∈ ftTypePFittingFamily S)
    (hpsi : psi ∈ ftTypePFittingFamily S)
    (hone : phi 1 = psi 1) :
    ctx.tau (phi - psi) ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity ctx.H)) := by
  exact partner_difference_tau_supported ctx phi psi
    (seqInd_on (ctx.H.subgroupOf S) hphi)
    (seqInd_on (ctx.H.subgroupOf S) hpsi) hone

private theorem partner_dual_supported_on_fitting
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (chi : IrreducibleCharacter S ℂ)
    (hchi : (chi : ClassFunction S ℂ) ∈ ftTypePFittingFamily S) :
    (IrreducibleCharacter.dual chi : ClassFunction S ℂ) ∈
      ClassFunction.supportedOn
        ((ctx.H.subgroupOf S : Subgroup S) : Set S) := by
  have hchiOn : (chi : ClassFunction S ℂ) ∈
      ClassFunction.supportedOn
        ((ctx.H.subgroupOf S : Subgroup S) : Set S) :=
    seqInd_on (ctx.H.subgroupOf S) hchi
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  rw [← ClassFunction.inverseLinear_irreducible,
    ClassFunction.inverseLinear_apply]
  apply ClassFunction.eq_zero_of_mem_supportedOn hchiOn
  intro hxInv
  change x ∉ (ctx.H.subgroupOf S : Subgroup S) at hx
  change x⁻¹ ∈ (ctx.H.subgroupOf S : Subgroup S) at hxInv
  apply hx
  rw [← inv_inv x]
  exact (ctx.H.subgroupOf S).inv_mem hxInv

private theorem partner_dual_difference_tau_supported
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (chi : IrreducibleCharacter S ℂ)
    (hchi : (chi : ClassFunction S ℂ) ∈ ftTypePFittingFamily S) :
    ctx.tau ((chi : ClassFunction S ℂ) -
        (IrreducibleCharacter.dual chi : ClassFunction S ℂ)) ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity ctx.H)) := by
  apply partner_difference_tau_supported ctx
    (chi : ClassFunction S ℂ)
    (IrreducibleCharacter.dual chi : ClassFunction S ℂ)
  · exact seqInd_on (ctx.H.subgroupOf S) hchi
  · exact partner_dual_supported_on_fitting ctx chi hchi
  · simp [IrreducibleCharacter.apply_one_eq_finrank]

private theorem partner_core_inverse_mem
    {S : Subgroup G} {phi : ClassFunction S ℂ}
    (hphi : phi ∈ ftTypePCoreFamily S) :
    ClassFunction.inverseLinear phi ∈ ftTypePCoreFamily S := by
  change phi ∈ seqIndD (k := ℂ)
    (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥ at hphi
  change ClassFunction.inverseLinear phi ∈ seqIndD (k := ℂ)
    (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥
  exact seqInd_inverse_mem (k := ℂ)
    (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥ hphi

private theorem partner_core_irreducible_dual_orthogonal
    {S : Subgroup G}
    (chi : IrreducibleCharacter S ℂ)
    (hchi : (chi : ClassFunction S ℂ) ∈ ftTypePCoreFamily S) :
    characterPairing (chi : ClassFunction S ℂ)
      (IrreducibleCharacter.dual chi : ClassFunction S ℂ) = 0 := by
  letI : (pTypeCoreDerived S).Normal := by infer_instance
  rw [← ClassFunction.inverseLinear_irreducible]
  change (chi : ClassFunction S ℂ) ∈ seqIndD (k := ℂ)
    (pTypeCoreDerived S) (pTypeCoreFitting S) ⊥ at hchi
  exact seqInd_conjC_ortho (k := ℂ)
    (pTypeCoreDerived S) (mFT_odd S)
    (pTypeCoreFitting S) ⊥ hchi

private theorem partner_disjoint_coherent_irreducibles_orthogonal
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    {T V X X₁ X₂ : Subgroup G}
    {defX : IsInternalDirectProductIn X₁ X₂ X}
    (ctxT : FTTypePSetupContext T V X X₁ X₂ defX)
    (tauS : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (tauT : ClassFunction T ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcohS : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctxS.tau tauS)
    (hcohT : coherent_with
      (↑(ftTypePCoreFamily T) : Set (ClassFunction T ℂ))
      (nonidentitySet T) ctxT.tau tauT)
    (hdis : Disjoint
      (classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity ctxS.H))
      (classSupportWithin (⊤ : Subgroup G)
        (subgroupNonidentity ctxT.H)))
    (lambda : IrreducibleCharacter S ℂ)
    (theta : IrreducibleCharacter T ℂ)
    (hlambdaCore : (lambda : ClassFunction S ℂ) ∈
      ftTypePCoreFamily S)
    (hlambdaFit : (lambda : ClassFunction S ℂ) ∈
      ftTypePFittingFamily S)
    (hthetaCore : (theta : ClassFunction T ℂ) ∈
      ftTypePCoreFamily T)
    (hthetaFit : (theta : ClassFunction T ℂ) ∈
      ftTypePFittingFamily T) :
    characterPairing
      (tauS (lambda : ClassFunction S ℂ))
      (tauT (theta : ClassFunction T ℂ)) = 0 := by
  have hlambdaDual :
      (IrreducibleCharacter.dual lambda : ClassFunction S ℂ) ∈
        ftTypePCoreFamily S := by
    rw [← ClassFunction.inverseLinear_irreducible]
    exact partner_core_inverse_mem hlambdaCore
  have hthetaDual :
      (IrreducibleCharacter.dual theta : ClassFunction T ℂ) ∈
        ftTypePCoreFamily T := by
    rw [← ClassFunction.inverseLinear_irreducible]
    exact partner_core_inverse_mem hthetaCore
  have hlambdaSpan : (lambda : ClassFunction S ℂ) ∈
      AddSubgroup.closure
        (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) :=
    AddSubgroup.subset_closure hlambdaCore
  have hlambdaDualSpan :
      (IrreducibleCharacter.dual lambda : ClassFunction S ℂ) ∈
        AddSubgroup.closure
          (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) :=
    AddSubgroup.subset_closure hlambdaDual
  have hthetaSpan : (theta : ClassFunction T ℂ) ∈
      AddSubgroup.closure
        (↑(ftTypePCoreFamily T) : Set (ClassFunction T ℂ)) :=
    AddSubgroup.subset_closure hthetaCore
  have hthetaDualSpan :
      (IrreducibleCharacter.dual theta : ClassFunction T ℂ) ∈
        AddSubgroup.closure
          (↑(ftTypePCoreFamily T) : Set (ClassFunction T ℂ)) :=
    AddSubgroup.subset_closure hthetaDual
  obtain ⟨a, ha⟩ := hcohS.mapsToVirtual _ hlambdaSpan
  obtain ⟨b, hb⟩ := hcohS.mapsToVirtual _ hlambdaDualSpan
  obtain ⟨c, hc⟩ := hcohT.mapsToVirtual _ hthetaSpan
  obtain ⟨d, hd⟩ := hcohT.mapsToVirtual _ hthetaDualSpan
  letI : Invertible (Nat.card S : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card T : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hab : IntegralLattice.IsOrthonormalPair a b := by
    apply partner_orthonormal_pair
    · rw [ha, hcohS.isometry _ hlambdaSpan _ hlambdaSpan,
        IrreducibleCharacter.characterPairing_self]
    · rw [hb, hcohS.isometry _ hlambdaDualSpan _ hlambdaDualSpan,
        IrreducibleCharacter.characterPairing_self]
    · rw [ha, hb, hcohS.isometry _ hlambdaSpan _ hlambdaDualSpan]
      exact partner_core_irreducible_dual_orthogonal
        lambda hlambdaCore
  have hcd : IntegralLattice.IsOrthonormalPair c d := by
    apply partner_orthonormal_pair
    · rw [hc, hcohT.isometry _ hthetaSpan _ hthetaSpan,
        IrreducibleCharacter.characterPairing_self]
    · rw [hd, hcohT.isometry _ hthetaDualSpan _ hthetaDualSpan,
        IrreducibleCharacter.characterPairing_self]
    · rw [hc, hd, hcohT.isometry _ hthetaSpan _ hthetaDualSpan]
      exact partner_core_irreducible_dual_orthogonal
        theta hthetaCore
  have hdiffSspan :
      (lambda : ClassFunction S ℂ) -
          (IrreducibleCharacter.dual lambda : ClassFunction S ℂ) ∈
        AddSubgroup.closure
          (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) :=
    (AddSubgroup.closure
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))).sub_mem
        hlambdaSpan hlambdaDualSpan
  have hdiffTspan :
      (theta : ClassFunction T ℂ) -
          (IrreducibleCharacter.dual theta : ClassFunction T ℂ) ∈
        AddSubgroup.closure
          (↑(ftTypePCoreFamily T) : Set (ClassFunction T ℂ)) :=
    (AddSubgroup.closure
      (↑(ftTypePCoreFamily T) : Set (ClassFunction T ℂ))).sub_mem
        hthetaSpan hthetaDualSpan
  have hagreeS := hcohS.agrees _ hdiffSspan
    (partner_dual_sub_supported_off_one lambda)
  have hagreeT := hcohT.agrees _ hdiffTspan
    (partner_dual_sub_supported_off_one theta)
  have htauSsupport :=
    partner_dual_difference_tau_supported ctxS lambda hlambdaFit
  have htauTsupport :=
    partner_dual_difference_tau_supported ctxT theta hthetaFit
  have hpairs :
      characterPairing (VirtualCharacter.realize (a - b))
        (VirtualCharacter.realize (c - d)) = 0 := by
    rw [VirtualCharacter.realize_sub, VirtualCharacter.realize_sub,
      ha, hb, hc, hd, ← map_sub, ← map_sub, hagreeS, hagreeT]
    apply characterPairing_eq_zero_of_disjoint_of_invStable_left hdis
    · exact partner_sharp_inv_stable ctxS.H
    · exact htauSsupport
    · exact htauTsupport
  have habOne : VirtualCharacter.realize (a - b) 1 = 0 := by
    rw [VirtualCharacter.realize_sub, ha, hb, ← map_sub, hagreeS]
    apply ClassFunction.eq_zero_of_mem_supportedOn htauSsupport
    exact partner_one_not_mem_sharp ctxS.H
  have hcdOne : VirtualCharacter.realize (c - d) 1 = 0 := by
    rw [VirtualCharacter.realize_sub, hc, hd, ← map_sub, hagreeT]
    apply ClassFunction.eq_zero_of_mem_supportedOn htauTsupport
    exact partner_one_not_mem_sharp ctxT.H
  have hac := orthonormal_vchar_diff_ortho a b c d hab hcd
    hpairs habOne hcdOne
  simpa only [ha, hc] using hac

private noncomputable def partner_source_map :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction (⊤ : Subgroup G) ℂ :=
  ClassFunction.comap Subgroup.topEquiv.toMonoidHom

@[simp] private theorem partner_source_map_target
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction (⊤ : Subgroup G) ℂ) :
    partner_source_map (ctx.targetMap phi) = phi := by
  ext x
  simpa [partner_source_map, ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.symm_apply_apply x)

@[simp] private theorem partner_target_map_source
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi : ClassFunction G ℂ) :
    ctx.targetMap (partner_source_map phi) = phi := by
  ext x
  simpa [partner_source_map, ClassFunction.comap_apply] using
    congrArg phi (Subgroup.topEquiv.apply_symm_apply x)

private theorem partner_target_map_pairing
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction (⊤ : Subgroup G) ℂ) :
    characterPairing (ctx.targetMap phi) (ctx.targetMap psi) =
      characterPairing phi psi := by
  have hcard : Nat.card G = Nat.card (⊤ : Subgroup G) :=
    Nat.card_congr Subgroup.topEquiv.symm.toEquiv
  unfold characterPairing
  rw [hcard]
  congr 1
  refine Fintype.sum_equiv Subgroup.topEquiv.symm.toEquiv _ _ fun x ↦ ?_
  simp [ClassFunction.comap_apply]

private theorem partner_source_map_pairing
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (phi psi : ClassFunction G ℂ) :
    characterPairing (partner_source_map phi)
        (partner_source_map psi) =
      characterPairing phi psi := by
  calc
    characterPairing (partner_source_map phi)
        (partner_source_map psi) =
        characterPairing
          (ctx.targetMap (partner_source_map phi))
          (ctx.targetMap (partner_source_map psi)) :=
      (partner_target_map_pairing ctx
        (partner_source_map phi) (partner_source_map psi)).symm
    _ = characterPairing phi psi := by
      rw [partner_target_map_source, partner_target_map_source]

private theorem partner_source_map_virtual
    {phi : ClassFunction G ℂ}
    (hphi : ClassFunction.IsVirtual phi) :
    ClassFunction.IsVirtual (partner_source_map phi) := by
  obtain ⟨z, hz⟩ := hphi
  refine ⟨VirtualCharacter.comap
    Subgroup.topEquiv.toMonoidHom z, ?_⟩
  rw [VirtualCharacter.realize_comap, hz]
  rfl

private theorem partner_coherent_source_map
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    {calS : Set (ClassFunction S ℂ)} {A : Set S}
    {sigma nu : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hcoh : coherent_with calS A sigma nu) :
    coherent_with calS A
      (partner_source_map.comp sigma)
      (partner_source_map.comp nu) := by
  exact
    { isometry := by
        intro phi hphi psi hpsi
        simpa [LinearMap.comp_apply] using
          (partner_source_map_pairing ctx (nu phi) (nu psi)).trans
            (hcoh.isometry phi hphi psi hpsi)
      mapsToVirtual := by
        intro phi hphi
        exact partner_source_map_virtual (hcoh.mapsToVirtual phi hphi)
      agrees := by
        intro phi hphi hsupp
        simpa [LinearMap.comp_apply, hcoh.agrees phi hphi hsupp] }

private theorem partner_core_family_conjugation_closed
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW) :
    cfConjC_subset
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (FTtypePKernelLayer ctx.primeDadeF) := by
  refine ⟨?_, ?_⟩
  · intro phi hphi
    simpa only [ftTypePCoreFamily, pTypeCoreDerived,
      pTypeCoreFitting, FTtypePKernelLayer,
      PrimeDadeHypothesis.signalizerInKernel] using hphi
  · intro phi hphi
    exact partner_core_inverse_mem hphi

private theorem partner_coherent_orthogonal_eta
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (tau1 : ClassFunction S ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcoh : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S) ctx.tau tau1)
    (phi : ClassFunction S ℂ)
    (hphi : phi ∈ ftTypePCoreFamily S)
    (hirr : IsIrreducibleCharacter S ℂ phi)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    characterPairing (tau1 phi) (ctx.eta i j) = 0 := by
  let tauTop : ClassFunction S ℂ →ₗ[ℂ]
      ClassFunction (⊤ : Subgroup G) ℂ :=
    partner_source_map.comp tau1
  have hsource := partner_coherent_source_map ctx hcoh
  have hcohTop : coherent_with
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))
      (nonidentitySet S)
      (Dade ctx.primeDadeF.prDade_hyp) tauTop := by
    exact
      { isometry := hsource.isometry
        mapsToVirtual := hsource.mapsToVirtual
        agrees := by
          intro alpha halpha hsupp
          have hagree := hsource.agrees alpha halpha hsupp
          simpa only [tauTop, FTTypePSetupContext.tau,
            LinearMap.comp_apply, partner_source_map_target] using hagree }
  have htop := coherent_ortho_cycTIiso
    ctx.primeDadeF ctx.isoS ctx.isoG (mFT_odd S)
    (partner_core_family_conjugation_closed ctx) hcohTop
    hphi hirr
    (IrreducibleCharacter.cyclicTICharacter defW i j)
  rw [← partner_source_map_pairing ctx (tau1 phi) (ctx.eta i j)]
  simpa only [tauTop, LinearMap.comp_apply,
    FTTypePSetupContext.eta, partner_source_map_target,
    CyclicTIIsometryData.cyclicTIImage,
    CyclicTIIsometryData.cyclicTISourceIrreducible] using htop

private theorem partner_eta_swap
    {S T U V W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW)
    (i : IrreducibleCharacter W₁ ℂ)
    (j : IrreducibleCharacter W₂ ℂ) :
    ctxS.eta i j = ctxT.eta j i := by
  have hswap := CyclicTIHypothesis.cycTIisoC defW xdefW
    ctxS.primeDade.prDade_cycTI
    ctxT.primeDade.prDade_cycTI i j
  have hmapped := congrArg ctxS.targetMap hswap
  simpa only [FTTypePSetupContext.eta,
    CyclicTIIsometryData.cyclicTIImage,
    CyclicTIIsometryData.cyclicTISourceIrreducible,
    CyclicTIHypothesis.cyclicTIIsometry] using hmapped

private theorem partner_no_induced_fitting
    {S U W W₁ W₂ : Subgroup G}
    {defW : IsInternalDirectProductIn W₁ W₂ W}
    (ctxS : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (hlambdaCore : lambda ∈ ftTypePCoreFamily S)
    (hlambdaIrrFit : lambda ∈ irr_Ind_Fitting S)
    {T V : Subgroup G}
    (pairST : typeP_pair S T W W₁ W₂ defW)
    (xdefW : IsInternalDirectProductIn W₂ W₁ W)
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW) :
    ¬ ∃ theta ∈ ftTypePCoreFamily T,
      theta ∈ irr_Ind_Fitting T := by
  rintro ⟨theta, hthetaCore, hthetaIrrFit⟩
  let lambdaIrr : IrreducibleCharacter S ℂ :=
    ⟨lambda, hlambdaIrrFit.1⟩
  let thetaIrr : IrreducibleCharacter T ℂ :=
    ⟨theta, hthetaIrrFit.1⟩
  have hdis := partner_fitting_supports_disjoint
    ctxS pairST xdefW ctxT
  obtain ⟨tauS, hcohS, hrowsS⟩ := FTtypeP_coherence ctxS
  obtain ⟨tauT, hcohT, hrowsT⟩ := FTtypeP_coherence ctxT
  have hLambdaTheta :
      characterPairing (tauS lambda) (tauT theta) = 0 := by
    simpa only [lambdaIrr, thetaIrr] using
      partner_disjoint_coherent_irreducibles_orthogonal
        ctxS ctxT tauS tauT hcohS hcohT hdis
        lambdaIrr thetaIrr hlambdaCore hlambdaIrrFit.2
        hthetaCore hthetaIrrFit.2

  letI : IsCyclic W₂ := ctxS.primeTI.fixed_cyclic
  letI : IsCyclic W₁ := ctxT.primeTI.fixed_cyclic
  obtain ⟨jS, hjS⟩ :=
    IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctxS.primeTI.prime_cycTIhyp.one_lt_card_right
  obtain ⟨jT, hjT⟩ :=
    IrreducibleCharacter.exists_ne_trivial_of_one_lt_card
      (k := ℂ) ctxT.primeTI.prime_cycTIhyp.one_lt_card_right
  have hmuSCore : ctxS.mu jS ∈ ftTypePCoreFamily S :=
    FTseqInd_TIred ctxS jS hjS
  have hmuTCore : ctxT.mu jT ∈ ftTypePCoreFamily T :=
    FTseqInd_TIred ctxT jT hjT
  have hmuSFit : ctxS.mu jS ∈ ftTypePFittingFamily S :=
    FTprTIred_Ind_Fitting ctxS jS hjS
  have hmuTFit : ctxT.mu jT ∈ ftTypePFittingFamily T :=
    FTprTIred_Ind_Fitting ctxT jT hjT
  have hdegreeS : lambda 1 = ctxS.mu jS 1 :=
    (FTtypeP_Ind_Fitting_1 ctxS lambda hlambdaIrrFit.2).trans
      (FTtypeP_Ind_Fitting_1 ctxS (ctxS.mu jS) hmuSFit).symm
  have hdegreeT : theta 1 = ctxT.mu jT 1 :=
    (FTtypeP_Ind_Fitting_1 ctxT theta hthetaIrrFit.2).trans
      (FTtypeP_Ind_Fitting_1 ctxT (ctxT.mu jT) hmuTFit).symm

  obtain ⟨bS, _hbS, hrowSRaw⟩ := hrowsS
  obtain ⟨bT, _hbT, hrowTRaw⟩ := hrowsT
  let jS' : IrreducibleCharacter W₂ ℂ := ftTypePSignIndex bS jS
  let jT' : IrreducibleCharacter W₁ ℂ := ftTypePSignIndex bT jT
  have hrowS : tauS (ctxS.mu jS) =
      ftTypePBooleanSign bS •
        ∑ i : IrreducibleCharacter W₁ ℂ, ctxS.eta i jS' := by
    simpa only [jS'] using hrowSRaw jS hjS
  have hrowT : tauT (ctxT.mu jT) =
      ftTypePBooleanSign bT •
        ∑ j : IrreducibleCharacter W₂ ℂ, ctxT.eta j jT' := by
    simpa only [jT'] using hrowTRaw jT hjT

  have hLambdaEtaS
      (i : IrreducibleCharacter W₁ ℂ)
      (j : IrreducibleCharacter W₂ ℂ) :
      characterPairing (tauS lambda) (ctxS.eta i j) = 0 :=
    partner_coherent_orthogonal_eta ctxS tauS hcohS
      lambda hlambdaCore hlambdaIrrFit.1 i j
  have hThetaEtaT
      (j : IrreducibleCharacter W₂ ℂ)
      (i : IrreducibleCharacter W₁ ℂ) :
      characterPairing (tauT theta) (ctxT.eta j i) = 0 :=
    partner_coherent_orthogonal_eta ctxT tauT hcohT
      theta hthetaCore hthetaIrrFit.1 j i
  have hLambdaRowT :
      characterPairing (tauS lambda)
        (∑ j : IrreducibleCharacter W₂ ℂ, ctxT.eta j jT') = 0 := by
    rw [partner_pairing_sum_right]
    apply Finset.sum_eq_zero
    intro j _hj
    rw [← partner_eta_swap ctxS xdefW ctxT jT' j]
    exact hLambdaEtaS jT' j
  have hRowSTheta :
      characterPairing
        (∑ i : IrreducibleCharacter W₁ ℂ, ctxS.eta i jS')
        (tauT theta) = 0 := by
    rw [partner_pairing_sum_left]
    apply Finset.sum_eq_zero
    intro i _hi
    rw [partner_eta_swap ctxS xdefW ctxT i jS',
      characterPairing_comm]
    exact hThetaEtaT jS' i
  have hLambdaMuT :
      characterPairing (tauS lambda) (tauT (ctxT.mu jT)) = 0 := by
    rw [hrowT, characterPairing_smul_right, hLambdaRowT, mul_zero]
  have hMuSTheta :
      characterPairing (tauS (ctxS.mu jS)) (tauT theta) = 0 := by
    rw [hrowS, characterPairing_smul_left, hRowSTheta, mul_zero]

  let alpha : ClassFunction S ℂ := lambda - ctxS.mu jS
  let beta : ClassFunction T ℂ := theta - ctxT.mu jT
  have hAlphaSpan : alpha ∈ AddSubgroup.closure
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ)) := by
    dsimp only [alpha]
    exact (AddSubgroup.closure
      (↑(ftTypePCoreFamily S) : Set (ClassFunction S ℂ))).sub_mem
        (AddSubgroup.subset_closure hlambdaCore)
        (AddSubgroup.subset_closure hmuSCore)
  have hBetaSpan : beta ∈ AddSubgroup.closure
      (↑(ftTypePCoreFamily T) : Set (ClassFunction T ℂ)) := by
    dsimp only [beta]
    exact (AddSubgroup.closure
      (↑(ftTypePCoreFamily T) : Set (ClassFunction T ℂ))).sub_mem
        (AddSubgroup.subset_closure hthetaCore)
        (AddSubgroup.subset_closure hmuTCore)
  have hAlphaOff : alpha ∈
      ClassFunction.supportedOn (nonidentitySet S) := by
    dsimp only [alpha]
    exact partner_sub_supported_off_one lambda (ctxS.mu jS) hdegreeS
  have hBetaOff : beta ∈
      ClassFunction.supportedOn (nonidentitySet T) := by
    dsimp only [beta]
    exact partner_sub_supported_off_one theta (ctxT.mu jT) hdegreeT
  have hAlphaSupport : ctxS.tau alpha ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity ctxS.H)) := by
    dsimp only [alpha]
    exact partner_fitting_difference_tau_supported
      ctxS lambda (ctxS.mu jS) hlambdaIrrFit.2 hmuSFit hdegreeS
  have hBetaSupport : ctxT.tau beta ∈
      ClassFunction.supportedOn
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity ctxT.H)) := by
    dsimp only [beta]
    exact partner_fitting_difference_tau_supported
      ctxT theta (ctxT.mu jT) hthetaIrrFit.2 hmuTFit hdegreeT
  have hAlphaBeta :
      characterPairing (tauS alpha) (tauT beta) = 0 := by
    rw [hcohS.agrees alpha hAlphaSpan hAlphaOff,
      hcohT.agrees beta hBetaSpan hBetaOff]
    apply characterPairing_eq_zero_of_disjoint_of_invStable_left hdis
    · exact partner_sharp_inv_stable ctxS.H
    · exact hAlphaSupport
    · exact hBetaSupport
  have hMuMuZero :
      characterPairing (tauS (ctxS.mu jS))
        (tauT (ctxT.mu jT)) = 0 := by
    have h := hAlphaBeta
    dsimp only [alpha, beta] at h
    rw [map_sub, map_sub, partner_pairing_sub_left,
      partner_pairing_sub_right, partner_pairing_sub_right,
      hLambdaTheta, hLambdaMuT, hMuSTheta] at h
    simpa using h

  have hsumPair :
      characterPairing
        (∑ i : IrreducibleCharacter W₁ ℂ, ctxS.eta i jS')
        (∑ j : IrreducibleCharacter W₂ ℂ, ctxT.eta j jT') = 1 := by
    calc
      characterPairing
          (∑ i : IrreducibleCharacter W₁ ℂ, ctxS.eta i jS')
          (∑ j : IrreducibleCharacter W₂ ℂ, ctxT.eta j jT') =
          ∑ i : IrreducibleCharacter W₁ ℂ,
            ∑ j : IrreducibleCharacter W₂ ℂ,
              characterPairing (ctxS.eta i jS')
                (ctxT.eta j jT') := by
            rw [partner_pairing_sum_left]
            apply Finset.sum_congr rfl
            intro i _hi
            rw [partner_pairing_sum_right]
      _ = ∑ i : IrreducibleCharacter W₁ ℂ,
            ∑ j : IrreducibleCharacter W₂ ℂ,
              if (i, jS') = (jT', j) then 1 else 0 := by
            apply Finset.sum_congr rfl
            intro i _hi
            apply Finset.sum_congr rfl
            intro j _hj
            rw [← partner_eta_swap ctxS xdefW ctxT jT' j]
            exact FTTypePCyclicRectangleInternal.characterPairing_eta
              ctxS i jT' jS' j
      _ = 1 := by
            rw [Finset.sum_eq_single jT']
            · simp
            · intro i _hi hne
              simp [hne]
            · simp
  have hsignS : ftTypePBooleanSign bS ≠ 0 := by
    cases bS <;> simp [ftTypePBooleanSign]
  have hsignT : ftTypePBooleanSign bT ≠ 0 := by
    cases bT <;> simp [ftTypePBooleanSign]
  rw [hrowS, hrowT, characterPairing_smul_left,
    characterPairing_smul_right, hsumPair] at hMuMuZero
  exact ((mul_ne_zero hsignS hsignT)
    (by simpa using hMuMuZero)).elim

private theorem ftTypePPartnerNoInducedAndDisjoint13
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (hirr : lambda ∈ irr_Ind_Fitting S)
    {T : Subgroup G}
    (pairST : typeP_pair S T W W₁ W₂ defW)
    {xdefW : IsInternalDirectProductIn W₂ W₁ W}
    {V : Subgroup G}
    (ctxT : FTTypePSetupContext T V W W₂ W₁ xdefW) :
    (¬ ∃ theta ∈ ftTypePCoreFamily T,
        theta ∈ irr_Ind_Fitting T) ∧
      Disjoint
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity ctx.H))
        (classSupportWithin (⊤ : Subgroup G)
          (subgroupNonidentity ctxT.H)) := by
  exact
    ⟨partner_no_induced_fitting ctx lambda hcalS hirr
        pairST xdefW ctxT,
      partner_fitting_supports_disjoint ctx pairST xdefW ctxT⟩

/-! ## Peterfalvi (13.10) -/

/-- `PFsection13.v: FTtypeP_compl_ker_ratio_lb`, Peterfalvi (13.10). -/
theorem FTtypeP_compl_ker_ratio_lb
    (ctx : FTTypePSetupContext S U W W₁ W₂ defW)
    (lambda : ClassFunction S ℂ)
    (hcalS : lambda ∈ ftTypePCoreFamily S)
    (hirr : lambda ∈ irr_Ind_Fitting S) :
    let qm1 : ℝ := (ctx.q - 1 : ℕ)
    (1 - qm1⁻¹ - qm1 / (ctx.q : ℝ) ^ ctx.p +
        (qm1 * (ctx.q : ℝ) ^ ctx.p)⁻¹) *
          (ctx.p : ℝ) ^ (ctx.q - 1) / (ctx.q : ℝ) <
      (ctx.u : ℝ) / (Nat.card ctx.C : ℝ) := by
  obtain ⟨T, pairST, xdefW, V, ctxT⟩ := ftTypePPairedSetup ctx
  have hpair :=
    ftTypePPartnerNoInducedAndDisjoint13
      ctx lambda hcalS hirr pairST ctxT
  have hpartner := FTtypeP_no_Ind_Fitting_facts ctxT hpair.1
  obtain ⟨tau₁, hcoh, hTIred⟩ := FTtypeP_coherence ctx
  have hraw :=
    ftTypePStrictRawRatioBound13 ctx ctxT lambda hcalS hirr
      tau₁ hcoh hTIred hpair.2
      (ftTypePPairedEta ctx ctxT)
      (ftTypePFittingEqCoreOfCentralizerEqBot ctxT hpartner.2.1)
  exact ftTypePComplKerRatioOfRawBound
    ctx lambda hirr ctxT hpartner hraw

end

end Submission.OddOrder.PF
