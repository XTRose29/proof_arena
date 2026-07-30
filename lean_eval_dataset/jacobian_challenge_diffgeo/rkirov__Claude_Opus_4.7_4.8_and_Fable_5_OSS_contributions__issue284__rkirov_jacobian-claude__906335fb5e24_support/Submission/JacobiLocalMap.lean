/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Forster 21.4(a) — the local Jacobi map and its open image

The local Jacobi map at a family of base points `a : Fin g → X`:

    G(z)ᵢ := ∑ⱼ Φ̃_{a j, i}(z j),

where `Φ̃_{Q₀,i} = localLiftChart Q₀ 0 i` is the chart-coordinate primitive of the period-basis
form `ω_i` at `Q₀` (the straight-segment integral of `chartFormCoeff`).  `G` is a sum of
one-variable holomorphic functions, `G(center) = 0`, and its Fréchet derivative at the center is
the evaluation matrix `A = jacobiEvalMatrix a` (B-1).  At a base-point family with `det A ≠ 0`
(Forster 21.3, `exists_jacobiBasePoints_det_ne_zero`), the inverse function theorem
(`HasStrictFDerivAt.map_nhds_eq_of_equiv`) makes `G` open at the center:

    Filter.map G (𝓝 center) = 𝓝 0,

so every `t` near `0 ∈ ℂ^g` is `G(z)` for `z` near the center — the engine of Forster's
dissection-free discreteness argument (21.4(b), phase B-4).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), 21.4(a) (pp. 168–169).
-/
import Submission.JacobiBasePoints
import Submission.OfCurveAnalyticitySkeleton
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.FDeriv
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

open scoped Manifold ContDiff
open Jacobians.OfCurveSkeleton

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The chart primitive at the chart center: value and derivative -/

/-- `chartFormCoeff` at the chart center is the `localRep` self-evaluation (the
`jacobiEvalMatrix` entry). -/
theorem chartFormCoeff_center (Q₀ : X) (i : Fin (genus X)) :
    chartFormCoeff (X := X) Q₀ i ((chartAt (H := ℂ) Q₀) Q₀)
      = Jacobians.Montel.localRep (periodBasisForm X i) Q₀ Q₀ := by
  rw [chartFormCoeff, (chartAt (H := ℂ) Q₀).left_inv (mem_chart_source ℂ Q₀)]

/-- The chart primitive at the chart center takes its constant value (the segment degenerates). -/
theorem localLiftChart_center (Q₀ : X) (constants : Fin (genus X) → ℂ) (i : Fin (genus X)) :
    localLiftChart (X := X) Q₀ constants i ((chartAt (H := ℂ) Q₀) Q₀) = constants i := by
  rw [localLiftChart]
  simp [sub_self, mul_zero]

/-- **`HasDerivAt` of the chart primitive at the chart center**, with derivative the chart form
coefficient: rewrite `localLiftChart` on a chart ball as `constants i + g z − g z₀` for an
analytic primitive `g` of `chartFormCoeff` (the `localLiftChart_analyticAt` mechanism), and read
the derivative off `g`. -/
theorem localLiftChart_hasDerivAt_center (Q₀ : X) (constants : Fin (genus X) → ℂ)
    (i : Fin (genus X)) :
    HasDerivAt (localLiftChart (X := X) Q₀ constants i)
      (chartFormCoeff (X := X) Q₀ i ((chartAt (H := ℂ) Q₀) Q₀))
      ((chartAt (H := ℂ) Q₀) Q₀) := by
  classical
  set z₀ : ℂ := (chartAt (H := ℂ) Q₀) Q₀ with hz₀_def
  have h_open := (chartAt (H := ℂ) Q₀).open_target
  have h_mem : z₀ ∈ (chartAt (H := ℂ) Q₀).target :=
    (chartAt (H := ℂ) Q₀).map_source (mem_chart_source ℂ Q₀)
  obtain ⟨r, hr_pos, hr_subset⟩ := Metric.isOpen_iff.mp h_open _ h_mem
  have hdiff : DifferentiableOn ℂ (chartFormCoeff (X := X) Q₀ i) (Metric.ball z₀ r) :=
    (chartFormCoeff_differentiableOn Q₀ i).mono hr_subset
  obtain ⟨g, hg_deriv, _hg_ana⟩ := exists_analytic_primitive_on_ball hdiff
  have hf_cont : ContinuousOn (chartFormCoeff (X := X) Q₀ i) (Metric.ball z₀ r) :=
    hdiff.continuousOn
  -- on the ball, the chart primitive is `constants i + g z − g z₀`.
  have h_eq : Set.EqOn (localLiftChart (X := X) Q₀ constants i)
      (fun z => constants i + g z - g z₀) (Metric.ball z₀ r) := by
    intro z hz
    have hz₀_mem : z₀ ∈ Metric.ball z₀ r := Metric.mem_ball_self hr_pos
    have hseg : Set.Icc (0 : ℝ) 1 ⊆ {t | z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r} := by
      intro t ht
      show z₀ + (t : ℂ) * (z - z₀) ∈ Metric.ball z₀ r
      have h_rewrite : z₀ + (t : ℂ) * (z - z₀) = z₀ + t • (z - z₀) := by
        rw [Complex.real_smul]
      rw [h_rewrite]
      exact (convex_ball z₀ r).add_smul_sub_mem hz₀_mem hz ht
    have hFTC := segmentIntegral_eq_primitive_diff (c := z₀) (r := r) (a := z₀) (b := z)
      (f := chartFormCoeff (X := X) Q₀ i) (g := g) hz₀_mem hz hseg hf_cont hg_deriv
    simp only [localLiftChart]
    rw [hFTC]
    ring
  -- the model has the derivative at `z₀`; transfer along the local equality.
  have h_model : HasDerivAt (fun z => constants i + g z - g z₀)
      (chartFormCoeff (X := X) Q₀ i z₀) z₀ := by
    have hg₀ : HasDerivAt g (chartFormCoeff (X := X) Q₀ i z₀) z₀ :=
      hg_deriv z₀ (Metric.mem_ball_self hr_pos)
    simpa using (hg₀.const_add (constants i)).sub_const (g z₀)
  refine h_model.congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self hr_pos)] with z hz
  exact h_eq hz

/-- **Strict differentiability of the chart primitive at the chart center** (analytic ⟹ strict),
with the derivative identified by `localLiftChart_hasDerivAt_center`. -/
theorem localLiftChart_hasStrictDerivAt_center (Q₀ : X) (constants : Fin (genus X) → ℂ)
    (i : Fin (genus X)) :
    HasStrictDerivAt (localLiftChart (X := X) Q₀ constants i)
      (chartFormCoeff (X := X) Q₀ i ((chartAt (H := ℂ) Q₀) Q₀))
      ((chartAt (H := ℂ) Q₀) Q₀) := by
  have hstrict := ((localLiftChart_analyticAt Q₀ constants i).contDiffAt).hasStrictDerivAt
    (n := ω) (by simp)
  rwa [(localLiftChart_hasDerivAt_center Q₀ constants i).deriv] at hstrict

/-! ### The local Jacobi map -/

/-- **The local Jacobi map** at a base-point family `a : Fin g → X` (Forster 21.4(a)):
`G(z)ᵢ = ∑ⱼ Φ̃_{a j, i}(z j)`, the sum of the chart primitives of `ω_i` at the `a j`, each read
in its own chart coordinate `z j`. -/
noncomputable def jacobiMap (a : Fin (genus X) → X) (z : Fin (genus X) → ℂ) :
    Fin (genus X) → ℂ :=
  fun i => ∑ j, localLiftChart (X := X) (a j) 0 i (z j)

/-- The chart-coordinate center of the local Jacobi map. -/
noncomputable def jacobiCenter (a : Fin (genus X) → X) : Fin (genus X) → ℂ :=
  fun j => (chartAt (H := ℂ) (a j)) (a j)

/-- The local Jacobi map vanishes at the center (`Φ̃` is normalized by `constants = 0`). -/
theorem jacobiMap_center (a : Fin (genus X) → X) :
    jacobiMap a (jacobiCenter a) = 0 := by
  funext i
  rw [jacobiMap]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [jacobiCenter, localLiftChart_center]
  rfl

/-- The Fréchet derivative of the local Jacobi map at the center: the continuous linear map
`v ↦ A.mulVec v` with `A = jacobiEvalMatrix a` (assembled as a `Pi` of summed projections). -/
noncomputable def jacobiDeriv (a : Fin (genus X) → X) :
    (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    ∑ j, jacobiEvalMatrix a i j • ContinuousLinearMap.proj j

@[simp] theorem jacobiDeriv_apply (a : Fin (genus X) → X) (v : Fin (genus X) → ℂ)
    (i : Fin (genus X)) :
    jacobiDeriv a v i = ∑ j, jacobiEvalMatrix a i j * v j := by
  rw [jacobiDeriv, ContinuousLinearMap.pi_apply, ContinuousLinearMap.sum_apply]
  exact Finset.sum_congr rfl fun j _ => rfl

/-- **Strict differentiability of the local Jacobi map at the center**, with derivative the
evaluation matrix: assemble per-summand strict derivatives (`HasStrictDerivAt.comp` with the
coordinate projections) through `Finset.sum` and `Pi`. -/
theorem jacobiMap_hasStrictFDerivAt (a : Fin (genus X) → X) :
    HasStrictFDerivAt (jacobiMap a) (jacobiDeriv a) (jacobiCenter a) := by
  rw [show jacobiDeriv a = ContinuousLinearMap.pi fun i =>
      ∑ j, jacobiEvalMatrix a i j • ContinuousLinearMap.proj j from rfl]
  apply hasStrictFDerivAt_pi''
  intro i
  rw [ContinuousLinearMap.proj_pi]
  have hfun : (∑ j, fun z : Fin (genus X) → ℂ => localLiftChart (X := X) (a j) 0 i (z j))
      = fun z => jacobiMap a z i := by
    funext z
    rw [Finset.sum_apply]
    rfl
  rw [← hfun]
  refine HasStrictFDerivAt.sum fun j _ => ?_
  -- the `(i,j)` summand: `z ↦ Φ̃_{a j, i}(z j)`, the chart primitive after the projection.
  have houter : HasStrictDerivAt (localLiftChart (X := X) (a j) 0 i)
      (jacobiEvalMatrix a i j) (jacobiCenter a j) := by
    have h := localLiftChart_hasStrictDerivAt_center (a j) 0 i
    rwa [chartFormCoeff_center, show Jacobians.Montel.localRep (periodBasisForm X i) (a j) (a j)
      = jacobiEvalMatrix a i j from rfl] at h
  have hproj : HasStrictFDerivAt (fun z : Fin (genus X) → ℂ => z j)
      (ContinuousLinearMap.proj j) (jacobiCenter a) :=
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (genus X) => ℂ)
      j).hasStrictFDerivAt
  show HasStrictFDerivAt
    ((localLiftChart (X := X) (a j) 0 i) ∘ (fun z : Fin (genus X) → ℂ => z j))
    (jacobiEvalMatrix a i j • ContinuousLinearMap.proj j) (jacobiCenter a)
  exact houter.comp_hasStrictFDerivAt (jacobiCenter a) hproj

/-! ### The inverse function theorem at a rank-`g` base-point family -/

/-- At a base-point family with invertible evaluation matrix, `jacobiDeriv` is (the coercion of)
a continuous linear equivalence. -/
noncomputable def jacobiDerivEquiv (a : Fin (genus X) → X)
    (ha : (jacobiEvalMatrix (X := X) a).det ≠ 0) :
    (Fin (genus X) → ℂ) ≃L[ℂ] (Fin (genus X) → ℂ) :=
  ((jacobiEvalMatrix (X := X) a).toLinearEquiv'
    ((jacobiEvalMatrix (X := X) a).invertibleOfIsUnitDet
      (isUnit_iff_ne_zero.mpr ha))).toContinuousLinearEquiv

theorem coe_jacobiDerivEquiv (a : Fin (genus X) → X)
    (ha : (jacobiEvalMatrix (X := X) a).det ≠ 0) :
    (jacobiDerivEquiv a ha : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ))
      = jacobiDeriv a := by
  ext v i
  show ((jacobiEvalMatrix (X := X) a).toLinearEquiv' _) v i = jacobiDeriv a v i
  rw [jacobiDeriv_apply]
  show (jacobiEvalMatrix (X := X) a).mulVec v i = _
  rw [Matrix.mulVec, dotProduct]

/-- **Forster 21.4(a), the open-image conclusion.**  At a base-point family with `det A ≠ 0`,
the local Jacobi map sends neighbourhoods of the center to neighbourhoods of `0` (the inverse
function theorem `HasStrictFDerivAt.map_nhds_eq_of_equiv`). -/
theorem jacobiMap_map_nhds (a : Fin (genus X) → X)
    (ha : (jacobiEvalMatrix (X := X) a).det ≠ 0) :
    Filter.map (jacobiMap a) (nhds (jacobiCenter a)) = nhds 0 := by
  have hstrict : HasStrictFDerivAt (jacobiMap a)
      (jacobiDerivEquiv a ha : (Fin (genus X) → ℂ) →L[ℂ] (Fin (genus X) → ℂ))
      (jacobiCenter a) := by
    rw [coe_jacobiDerivEquiv]
    exact jacobiMap_hasStrictFDerivAt a
  have h := hstrict.map_nhds_eq_of_equiv
  rwa [jacobiMap_center a] at h

/-- **The packaged 21.4(a) statement**: a base-point family `a` (injective, rank-`g` evaluation
matrix) at which the local Jacobi map `G` has `G(center) = 0` and maps every neighbourhood of
the center onto a neighbourhood of `0 ∈ ℂ^g`. -/
theorem exists_jacobiMap_map_nhds :
    ∃ a : Fin (genus X) → X, Function.Injective a ∧
      (jacobiEvalMatrix (X := X) a).det ≠ 0 ∧
      jacobiMap a (jacobiCenter a) = 0 ∧
      ∀ V ∈ nhds (jacobiCenter a), jacobiMap a '' V ∈ nhds (0 : Fin (genus X) → ℂ) := by
  obtain ⟨a, hinj, hdet⟩ := exists_jacobiBasePoints_det_ne_zero (X := X)
  refine ⟨a, hinj, hdet, jacobiMap_center a, fun V hV => ?_⟩
  rw [← jacobiMap_map_nhds a hdet]
  exact Filter.image_mem_map hV

end Jacobians
