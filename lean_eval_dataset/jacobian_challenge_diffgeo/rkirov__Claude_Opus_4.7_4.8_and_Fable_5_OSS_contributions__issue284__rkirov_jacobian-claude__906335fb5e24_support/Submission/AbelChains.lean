/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-0: 1-chains and the `pathPrimValue = lineIntegral` bridge

Connects the path-integral layer (`lineIntegral`, `periodVec`, `abelJacobi`) to the
discrete-monodromy layer (`pathPrimValue`, `PrimitiveChain`):

* `hasDerivAt_comp_of_isLocalPrimitiveOn` — the pointwise FTC: along a chart-C¹ path, a local
  primitive of `η` differentiates to the `lineIntegral` integrand `η(γ t)(γ'(t))`;
* `pathPrimValue_eq_lineIntegral` — the discrete path value (the telescoping sum over any
  primitive chain) IS the line integral, for chart-C¹ paths with integrable integrand;
  specialized to `IsSmoothPath` / `IsClosedSmoothLoop` and to `periodVec`;
* `OneChain` — Forster §20.4 1-chains: finitely many continuous curves with ℤ-coefficients,
  their `boundary` divisor `∂c` and `period` (the discrete `∫_c η`);
* `exists_oneChain_of_abelJacobi_eq_zero` — the Abel hypothesis unfolded: if
  `abelJacobi (P - Q) = 0` (`P ≠ Q`), some 1-chain `c` has `∂c = P - Q` and all
  basis-form periods zero.

This is the entry plumbing for Forster's proof of Abel's theorem (20.7, sufficiency
direction): the chain produced here is the one fed to the weak-solution machinery of
§§20.1–20.5.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.4 (chains), §20.7;
plan `docs/walls_bc_plan_2026-06-10.md`, phase C-0.
-/
import Submission.Abel
import Submission.HolomorphicPrimitiveMonodromy
import Submission.Dolbeault.FormTraceSheetCovector

noncomputable section

-- The ℝ/ℂ-module diamond (`Bundle.Trivial`-fiber instances from the Dolbeault import chain
-- shadow the canonical `ContinuousSMul ℝ ℂ` path): the permissive-transparency option is the
-- standing repo discipline (`RealForms`, `DolbeaultH01`, …).
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set MeasureTheory

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The pointwise FTC

A local primitive `F` of `η` (`IsLocalPrimitiveOn`), composed with a path `γ` that is
C¹ in the chart at `γ t`, has derivative exactly the `lineIntegral` integrand
`η (γ t) (pathSpeed γ t)`. This is the chart-level chain rule plus the frame identity
`mfderiv F y 1 = (F ∘ chart⁻¹)′(chart y)` (`mfderiv_apply_symmL_eq_deriv` +
`symmL_self_one`). -/

/-- **Pointwise FTC along a path.** If `F` is a local primitive of `η` near `γ t`, and the
chart pullback of `γ` is differentiable at `t`, then `F ∘ γ` has derivative
`η (γ t) (pathSpeed γ t)` at `t`. -/
theorem hasDerivAt_comp_of_isLocalPrimitiveOn
    {η : HolomorphicOneForms X} {F : X → ℂ} {U : Set X}
    (hprim : IsLocalPrimitiveOn η F U) {γ : ℝ → X} {t : ℝ}
    (hmem : γ t ∈ U) (hcont : ContinuousAt γ t)
    (hdiff : DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) :
    HasDerivAt (F ∘ γ) ((η.toFun (γ t) (pathSpeed γ t) : ℂ)) t := by
  obtain ⟨hF, hηF⟩ := hprim (γ t) hmem
  -- the chart pullback of `F` is ℂ-differentiable at the chart point
  have hfloc_diff_C : DifferentiableAt ℂ (F ∘ (chartAt (H := ℂ) (γ t)).symm)
      ((chartAt (H := ℂ) (γ t)) (γ t)) :=
    differentiableAt_comp_chart_symm (x := γ t) (mem_chart_source ℂ (γ t)) hF
  -- ℝ-Fréchet derivative of the pullback: the explicit multiplication CLM
  -- `w ↦ (F ∘ chart⁻¹)′(z) * w` (bypassing the `restrictScalars` ℝ/ℂ-module diamond:
  -- the `IsLittleO` asymptotics of the ℂ- and ℝ-statements are literally the same)
  have hfloc_hasFD_R : HasFDerivAt (F ∘ (chartAt (H := ℂ) (γ t)).symm)
      ((ContinuousLinearMap.mul ℝ ℂ)
        (deriv (F ∘ (chartAt (H := ℂ) (γ t)).symm) ((chartAt (H := ℂ) (γ t)) (γ t))))
      ((chartAt (H := ℂ) (γ t)) (γ t)) := by
    have h := hfloc_diff_C.hasDerivAt
    rw [hasDerivAt_iff_isLittleO_nhds_zero] at h
    rw [hasFDerivAt_iff_isLittleO_nhds_zero]
    simpa only [ContinuousLinearMap.mul_apply', smul_eq_mul, mul_comm] using h
  -- chain rule for the composite through the chart
  have hcomp : HasFDerivAt ((F ∘ (chartAt (H := ℂ) (γ t)).symm) ∘
      ((chartAt (H := ℂ) (γ t)).toFun ∘ γ))
      (((ContinuousLinearMap.mul ℝ ℂ)
        (deriv (F ∘ (chartAt (H := ℂ) (γ t)).symm) ((chartAt (H := ℂ) (γ t)) (γ t)))).comp
        (fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)) t :=
    hfloc_hasFD_R.comp t hdiff.hasFDerivAt
  -- `F ∘ γ` agrees with the chart factorization near `t`
  have hev : F ∘ γ =ᶠ[𝓝 t] (F ∘ (chartAt (H := ℂ) (γ t)).symm) ∘
      ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) := by
    filter_upwards [hcont.preimage_mem_nhds
      ((chartAt (H := ℂ) (γ t)).open_source.mem_nhds (mem_chart_source ℂ (γ t)))] with s hs
    show F (γ s) = F ((chartAt (H := ℂ) (γ t)).symm ((chartAt (H := ℂ) (γ t)) (γ s)))
    rw [(chartAt (H := ℂ) (γ t)).left_inv hs]
  have hFγ : HasFDerivAt (F ∘ γ)
      (((ContinuousLinearMap.mul ℝ ℂ)
        (deriv (F ∘ (chartAt (H := ℂ) (γ t)).symm) ((chartAt (H := ℂ) (γ t)) (γ t)))).comp
        (fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)) t :=
    hcomp.congr_of_eventuallyEq hev
  -- the frame identity: `localRep η (γ t) (γ t) = (F ∘ chart⁻¹)′(chart (γ t))` —
  -- the primitive property evaluated on the unit frame vector `symmL 1`
  have hframe : Montel.localRep η (γ t) (γ t)
      = deriv (F ∘ (chartAt (H := ℂ) (γ t)).symm) ((chartAt (H := ℂ) (γ t)) (γ t)) := by
    show η.toFun (γ t)
        ((trivializationAt ℂ (TangentSpace 𝓘(ℂ, ℂ) (M := X)) (γ t)).symmL ℂ (γ t) 1) = _
    rw [hηF _]
    exact Dolbeault.mfderiv_apply_symmL_eq_deriv F (mem_chart_source ℂ (γ t)) hF
  -- the integrand value equals the Fréchet value at `1`
  have hval : (((ContinuousLinearMap.mul ℝ ℂ)
      (deriv (F ∘ (chartAt (H := ℂ) (γ t)).symm) ((chartAt (H := ℂ) (γ t)) (γ t)))).comp
        (fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)) (1 : ℝ)
      = (η.toFun (γ t) (pathSpeed γ t) : ℂ) := by
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.mul_apply']
    -- `fderiv ℝ g t 1 = pathSpeed γ t` by definition
    rw [show (fderiv ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t) (1 : ℝ) = pathSpeed γ t from rfl]
    -- the form side: ℂ-linearity on the 1-dimensional tangent space
    rw [Dolbeault.FormTraceSheet.toFun_apply_eq_mul_localRep η (γ t) (pathSpeed γ t), hframe]
    ring
  exact hval ▸ hFγ.hasDerivAt

/-! ### The FTC bridge: `pathPrimValue = lineIntegral` -/

/-- **The FTC bridge.** For a chart-C¹ path with integrable integrand, the discrete path
value (the telescoping primitive-chain sum, classically `∫_γ η`) equals the line integral.
Each chain block integrates by the pointwise FTC; the blocks sum by adjacency. -/
theorem pathPrimValue_eq_lineIntegral (η : HolomorphicOneForms X) {γ : ℝ → X}
    (hγ : ContinuousOn γ (Icc 0 1)) (hcont : Continuous γ)
    (hdiff : ∀ t ∈ Set.uIcc (0 : ℝ) 1,
      DifferentiableAt ℝ ((chartAt (H := ℂ) (γ t)).toFun ∘ γ) t)
    (hint : IntervalIntegrable (fun s => η.toFun (γ s) (pathSpeed γ s)) volume 0 1) :
    pathPrimValue η γ hγ = lineIntegral η γ := by
  obtain ⟨C⟩ := exists_primitiveChain η hγ
  rw [pathPrimValue_eq η hγ C]
  -- block intervals sit inside `[0,1]`
  have hsub : ∀ k, Set.uIcc (C.t k) (C.t (k + 1)) ⊆ Set.uIcc (0 : ℝ) 1 := by
    intro k
    rw [Set.uIcc_of_le (C.mono (Nat.le_succ k)), Set.uIcc_of_le zero_le_one]
    exact Set.Icc_subset_Icc (C.t_nonneg k) (C.t_le_one (k + 1))
  -- each block integrates to the primitive increment
  have hblock : ∀ k, k < C.n →
      ∫ s in C.t k..C.t (k + 1), η.toFun (γ s) (pathSpeed γ s)
        = C.F k (γ (C.t (k + 1))) - C.F k (γ (C.t k)) := by
    intro k hk
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt
      (f := C.F k ∘ γ) (f' := fun s => η.toFun (γ s) (pathSpeed γ s))
      (fun s hs => by
        have hs' : s ∈ Icc (C.t k) (C.t (k + 1)) := by
          rwa [Set.uIcc_of_le (C.mono (Nat.le_succ k))] at hs
        exact hasDerivAt_comp_of_isLocalPrimitiveOn (C.prim k) (C.covers k s hs')
          hcont.continuousAt (hdiff s (hsub k hs)))
      (hint.mono_set (hsub k))
    exact h
  -- sum the blocks by adjacency
  have hint_k : ∀ k < C.n, IntervalIntegrable
      (fun s => η.toFun (γ s) (pathSpeed γ s)) volume (C.t k) (C.t (k + 1)) :=
    fun k _ => hint.mono_set (hsub k)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals hint_k
  calc C.value
      = ∑ k ∈ Finset.range C.n, (C.F k (γ (C.t (k + 1))) - C.F k (γ (C.t k))) := rfl
    _ = ∑ k ∈ Finset.range C.n,
          ∫ s in C.t k..C.t (k + 1), η.toFun (γ s) (pathSpeed γ s) :=
        Finset.sum_congr rfl fun k hk => (hblock k (Finset.mem_range.mp hk)).symm
    _ = ∫ s in C.t 0..C.t C.n, η.toFun (γ s) (pathSpeed γ s) := hsum
    _ = lineIntegral η γ := by rw [C.t_zero, C.t_stab C.n le_rfl]; rfl

/-- The FTC bridge for a smooth path, any holomorphic form (the integrand is integrable
from the continuous-velocity field). -/
theorem IsSmoothPath.pathPrimValue_eq_lineIntegral {P Q : X} {γ : ℝ → X}
    (h : IsSmoothPath P Q γ) (η : HolomorphicOneForms X)
    (hγ : ContinuousOn γ (Icc 0 1)) :
    pathPrimValue η γ hγ = lineIntegral η γ :=
  Jacobians.pathPrimValue_eq_lineIntegral η hγ h.cont h.diff
    (intervalIntegrable_form_pathSpeed_of_velContinuous η γ h.velCont)

/-- The FTC bridge for a closed smooth loop, any holomorphic form. -/
theorem IsClosedSmoothLoop.pathPrimValue_eq_lineIntegral {γ : ℝ → X}
    (h : IsClosedSmoothLoop γ) (η : HolomorphicOneForms X)
    (hγ : ContinuousOn γ (Icc 0 1)) :
    pathPrimValue η γ hγ = lineIntegral η γ :=
  Jacobians.pathPrimValue_eq_lineIntegral η hγ h.cont h.diff
    (intervalIntegrable_form_pathSpeed_of_velContinuous η γ h.velCont)

/-- The discrete path value of the `i`-th basis form along a smooth path is the `i`-th
component of the period vector. -/
theorem IsSmoothPath.pathPrimValue_eq_periodVec {P Q : X} {γ : ℝ → X}
    (h : IsSmoothPath P Q γ) (i : Fin (genus X)) (hγ : ContinuousOn γ (Icc 0 1)) :
    pathPrimValue (periodBasisForm X i) γ hγ = periodVec γ i :=
  h.pathPrimValue_eq_lineIntegral (periodBasisForm X i) hγ

/-- The discrete path value of the `i`-th basis form along a closed smooth loop is the
`i`-th component of the period vector. -/
theorem IsClosedSmoothLoop.pathPrimValue_eq_periodVec {γ : ℝ → X}
    (h : IsClosedSmoothLoop γ) (i : Fin (genus X)) (hγ : ContinuousOn γ (Icc 0 1)) :
    pathPrimValue (periodBasisForm X i) γ hγ = periodVec γ i :=
  h.pathPrimValue_eq_lineIntegral (periodBasisForm X i) hγ

/-! ### 1-chains (Forster §20.4)

A 1-chain is a formal finite ℤ-linear combination of continuous curves `[0,1] → X`. Its
boundary `∂c` is the divisor `∑ n_j ((γ_j 1) − (γ_j 0))`; its period against a holomorphic
1-form is `∑ n_j ∫_{γ_j} η` with the integral in its discrete (`pathPrimValue`)
incarnation — defined for *continuous* curves, which is what the subdivision arguments of
§20.5 need. -/

/-- A **1-chain** on `X` (Forster §20.4): finitely many curves with ℤ-coefficients. Curves
are totalized to `ℝ → X`; only the restriction to `[0,1]` matters, and continuity is
required there. -/
structure OneChain (X : Type*) [TopologicalSpace X] where
  /-- number of curves -/
  m : ℕ
  /-- the ℤ-coefficients -/
  coeff : Fin m → ℤ
  /-- the curves -/
  curve : Fin m → ℝ → X
  /-- continuity of each curve on `[0,1]` -/
  cont : ∀ j, ContinuousOn (curve j) (Icc 0 1)

namespace OneChain

/-- The **boundary divisor** `∂c = ∑ n_j ((γ_j 1) − (γ_j 0))` of a 1-chain
(Forster §20.4). -/
def boundary (c : OneChain X) : Divisor X :=
  ∑ j, c.coeff j •
    (Finsupp.single (c.curve j 1) (1 : ℤ) - Finsupp.single (c.curve j 0) (1 : ℤ))

/-- The **period** `∫_c η = ∑ n_j ∫_{γ_j} η` of a 1-chain against a holomorphic 1-form,
with each curve integral in its discrete (`pathPrimValue`) incarnation. -/
def period (c : OneChain X) (η : HolomorphicOneForms X) : ℂ :=
  ∑ j, c.coeff j • pathPrimValue η (c.curve j) (c.cont j)

/-- The boundary of a 1-chain has degree zero (Forster §20.4: `deg (∂c) = 0`). -/
theorem boundary_deg (c : OneChain X) : Divisor.deg X c.boundary = 0 := by
  rw [boundary, map_sum]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [map_zsmul, map_sub, Divisor.deg_single, Divisor.deg_single, sub_self, smul_zero]

end OneChain

/-! ### Unfolding the Abel hypothesis

`abelJacobi (P − Q) = 0` says exactly that `periodVec (smoothPath P₀ P) −
periodVec (smoothPath P₀ Q)` lies in the period lattice — a finite ℤ-combination of
closed-smooth-loop periods. The chain `smoothPath P₀ P − smoothPath P₀ Q − ∑ n_k λ_k`
then has boundary `P − Q` and **all basis periods zero** (Forster 20.7, hypothesis (∗)). -/

/-- **The Abel hypothesis, unfolded** (Forster 20.7 (∗)): if the Abel–Jacobi class of the
two-point divisor `P − Q` vanishes (`P ≠ Q`), there is a 1-chain `c` with `∂c = P − Q`
whose period against every basis form is zero. -/
theorem exists_oneChain_of_abelJacobi_eq_zero {P Q : X} (hPQ : P ≠ Q)
    (h : abelJacobi ⟨twoPointDivisor X P Q, twoPointDivisor_mem_degZero X P Q⟩ = 0) :
    ∃ c : OneChain X, c.boundary = twoPointDivisor X P Q ∧
      ∀ i : Fin (genus X), c.period (periodBasisForm X i) = 0 := by
  classical
  -- the lattice membership
  have h2 := abelJacobi_twoPointDivisor P Q hPQ
  have h0 : (QuotientAddGroup.mk (periodVec (smoothPath (Classical.arbitrary X) P)) :
      (Fin (genus X) → ℂ) ⧸ (truePeriodLattice X).toAddSubgroup) -
      QuotientAddGroup.mk (periodVec (smoothPath (Classical.arbitrary X) Q)) = 0 :=
    h2.symm.trans h
  have hmem : periodVec (smoothPath (Classical.arbitrary X) P) -
      periodVec (smoothPath (Classical.arbitrary X) Q) ∈ truePeriodLattice X := by
    rw [← Submodule.mem_toAddSubgroup, ← QuotientAddGroup.eq_zero_iff]
    rw [QuotientAddGroup.mk_sub]
    exact h0
  -- span membership ⟹ finite ℤ-combination of loop periods
  rw [truePeriodLattice, Submodule.mem_span_set'] at hmem
  obtain ⟨n, f, g, hsum⟩ := hmem
  choose lam hlam hval using fun k : Fin n => (g k).2
  -- the chain: `smoothPath P₀ P − smoothPath P₀ Q − ∑ f_k λ_k`
  refine ⟨{
    m := n + 2
    coeff := Fin.cons 1 (Fin.cons (-1) fun k => -(f k))
    curve := Fin.cons (smoothPath (Classical.arbitrary X) P)
      (Fin.cons (smoothPath (Classical.arbitrary X) Q) lam)
    cont := ?_ }, ?_, ?_⟩
  · -- continuity of each curve
    intro j
    refine j.cases ?_ fun j' => ?_
    · exact (isSmoothPath_smoothPath _ _).cont.continuousOn
    · refine j'.cases ?_ fun k => ?_
      · exact (isSmoothPath_smoothPath _ _).cont.continuousOn
      · exact (hlam k).cont.continuousOn
  · -- boundary = twoPointDivisor
    show (∑ j : Fin (n + 2), _) = _
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ, smoothPath_zero, smoothPath_one]
    have hloop : ∀ k : Fin n,
        Finsupp.single (lam k 1) (1 : ℤ) - Finsupp.single (lam k 0) (1 : ℤ) = 0 := by
      intro k
      rw [(hlam k).closed, sub_self]
    have hloopsum : (∑ k : Fin n, (-(f k)) •
        (Finsupp.single (lam k 1) (1 : ℤ) - Finsupp.single (lam k 0) (1 : ℤ))) = 0 :=
      Finset.sum_eq_zero fun k _ => by rw [hloop k, smul_zero]
    rw [hloopsum, add_zero, twoPointDivisor]
    rw [one_smul, neg_one_zsmul]
    abel
  · -- all basis periods vanish
    intro i
    show (∑ j : Fin (n + 2), _) = 0
    rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    -- bridge each `pathPrimValue` to `periodVec`
    rw [(isSmoothPath_smoothPath (Classical.arbitrary X) P).pathPrimValue_eq_periodVec i _,
      (isSmoothPath_smoothPath (Classical.arbitrary X) Q).pathPrimValue_eq_periodVec i _]
    have hloops : ∀ k : Fin n, pathPrimValue (periodBasisForm X i) (lam k)
        ((hlam k).cont.continuousOn) = periodVec (lam k) i :=
      fun k => (hlam k).pathPrimValue_eq_periodVec i _
    -- the span identity at component `i`
    have hsum_i : ∑ k : Fin n, (f k : ℂ) * periodVec (lam k) i =
        periodVec (smoothPath (Classical.arbitrary X) P) i -
          periodVec (smoothPath (Classical.arbitrary X) Q) i := by
      have hc := congrFun hsum i
      simp only [hval] at hc
      simp only [Finset.sum_apply, Pi.sub_apply, zsmul_eq_mul] at hc
      exact hc
    simp only [one_smul, zsmul_eq_mul, Int.cast_neg, Int.cast_one, neg_mul, one_mul]
    simp only [hloops]
    rw [Finset.sum_neg_distrib, hsum_i]
    ring

end Jacobians
