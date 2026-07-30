import Submission.MoserField
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.DifferentialForm.Basic

open Set Function Matrix Metric Filter Topology
open scoped ContDiff
open LeanEval.Geometry.Darboux

namespace Submission.LocalForms

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

def radialRetraction (b : ContDiffBump (0 : V)) (z : V) : V :=
  b z • z

theorem radialRetraction_contDiff (b : ContDiffBump (0 : V)) :
    ContDiff ℝ ∞ (radialRetraction b) := by
  unfold radialRetraction
  exact b.contDiff.smul contDiff_id

theorem radialRetraction_mem_closedBall (b : ContDiffBump (0 : V)) (z : V) :
    radialRetraction b z ∈ closedBall 0 b.rOut := by
  by_cases hz : z ∈ ball 0 b.rOut
  · rw [mem_closedBall, dist_zero_right, radialRetraction, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg b.nonneg]
    calc
      b z * ‖z‖ ≤ 1 * ‖z‖ := by gcongr; exact b.le_one
      _ ≤ b.rOut := by simpa [dist_zero_right] using (mem_ball.mp hz).le
  · have hb0 : b z = 0 := by
      apply b.zero_of_le_dist
      simpa [mem_ball, not_lt] using hz
    simp [radialRetraction, hb0, b.rOut_pos.le]

theorem radialRetraction_eq_self (b : ContDiffBump (0 : V))
    {z : V} (hz : z ∈ closedBall 0 b.rIn) : radialRetraction b z = z := by
  rw [radialRetraction, b.one_of_mem_closedBall hz, one_smul]

theorem radialRetraction_eventuallyEq_id (b : ContDiffBump (0 : V))
    {z : V} (hz : z ∈ ball 0 b.rIn) : radialRetraction b =ᶠ[𝓝 z] id := by
  filter_upwards [b.eventuallyEq_one_of_mem_ball hz] with y hy
  simp [radialRetraction, hy]

def extendByRetraction (form : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (b : ContDiffBump (0 : V)) (z : V) : V [⋀^Fin 2]→L[ℝ] ℝ :=
  form (radialRetraction b z)

theorem extendByRetraction_contDiff {D : Set V}
    (form : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hform : ContDiffOn ℝ ∞ form D)
    (b : ContDiffBump (0 : V)) (hrange : closedBall 0 b.rOut ⊆ D) :
    ContDiff ℝ ∞ (extendByRetraction form b) := by
  have hmaps : MapsTo (radialRetraction b) univ D := fun z _ =>
    hrange (radialRetraction_mem_closedBall b z)
  have hcompOn : ContDiffOn ℝ ∞ (form ∘ radialRetraction b) univ :=
    hform.comp (radialRetraction_contDiff b).contDiffOn hmaps
  change ContDiff ℝ ∞ (form ∘ radialRetraction b)
  exact contDiffOn_univ.mp hcompOn

theorem extendByRetraction_eventuallyEq {form : V → V [⋀^Fin 2]→L[ℝ] ℝ}
    (b : ContDiffBump (0 : V)) {z : V} (hz : z ∈ ball 0 b.rIn) :
    extendByRetraction form b =ᶠ[𝓝 z] form := by
  filter_upwards [radialRetraction_eventuallyEq_id b hz] with y hy
  simp [extendByRetraction, hy]

theorem extendByRetraction_eq {form : V → V [⋀^Fin 2]→L[ℝ] ℝ}
    (b : ContDiffBump (0 : V)) {z : V} (hz : z ∈ ball 0 b.rIn) :
    extendByRetraction form b z = form z :=
  (extendByRetraction_eventuallyEq b hz).self_of_nhds

/-- A global smooth representative of a smooth closed two-form germ at the origin. -/
theorem exists_global_smooth_germ {D : Set V} (hD : IsOpen D) (h0 : (0 : V) ∈ D)
    (form : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hform : ContDiffOn ℝ ∞ form D)
    (hclosed : ∀ z ∈ D, extDeriv form z = 0) :
    ∃ global : V → V [⋀^Fin 2]→L[ℝ] ℝ, ∃ r > (0 : ℝ),
      ContDiff ℝ ∞ global ∧ EqOn global form (ball 0 r) ∧
        (∀ z ∈ ball 0 r, extDeriv global z = 0) ∧ ball 0 r ⊆ D := by
  obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp (hD.mem_nhds h0)
  let b : ContDiffBump (0 : V) :=
    ⟨ε / 4, ε / 2, by positivity, by linarith⟩
  have hrange : closedBall (0 : V) b.rOut ⊆ D := by
    apply subset_trans (closedBall_subset_ball (by dsimp [b]; linarith)) hball
  refine ⟨extendByRetraction form b, b.rIn, b.rIn_pos, ?_, ?_, ?_, ?_⟩
  · exact extendByRetraction_contDiff form hform b hrange
  · intro z hz
    exact extendByRetraction_eq b hz
  · intro z hz
    have hzD : z ∈ D := hrange <| mem_closedBall.mpr <|
      ((mem_ball.mp hz).trans b.rIn_lt_rOut).le
    rw [(extendByRetraction_eventuallyEq b hz).extDeriv_eq]
    exact hclosed z hzD
  · intro z hz
    exact hrange <| mem_closedBall.mpr <| ((mem_ball.mp hz).trans b.rIn_lt_rOut).le

omit [FiniteDimensional ℝ V] in def affineMap (x : V) (e : V ≃L[ℝ] V) (z : V) : V :=
  x + e z

omit [FiniteDimensional ℝ V] in theorem affineMap_contDiff (x : V) (e : V ≃L[ℝ] V) :
    ContDiff ℝ ∞ (affineMap x e) := by
  unfold affineMap
  fun_prop

omit [FiniteDimensional ℝ V] in theorem fderiv_affineMap (x : V) (e : V ≃L[ℝ] V) (z : V) :
    fderiv ℝ (affineMap x e) z = e.toContinuousLinearMap := by
  exact (e.hasFDerivAt.const_add x).fderiv

omit [FiniteDimensional ℝ V] in def coordinateDomain
    (U : Set V) (x : V) (e : V ≃L[ℝ] V) : Set V :=
  affineMap x e ⁻¹' U

omit [FiniteDimensional ℝ V] in theorem isOpen_coordinateDomain
    {U : Set V} (hU : IsOpen U) (x : V) (e : V ≃L[ℝ] V) :
    IsOpen (coordinateDomain U x e) :=
  hU.preimage (affineMap_contDiff x e).continuous

omit [FiniteDimensional ℝ V] in theorem zero_mem_coordinateDomain
    {U : Set V} {x : V} (hx : x ∈ U) (e : V ≃L[ℝ] V) :
    (0 : V) ∈ coordinateDomain U x e := by
  simpa [coordinateDomain, affineMap]

omit [FiniteDimensional ℝ V] in def normalizedForm
    (form : V → V [⋀^Fin 2]→L[ℝ] ℝ) (x : V) (e : V ≃L[ℝ] V) (z : V) :
    V [⋀^Fin 2]→L[ℝ] ℝ :=
  (form (affineMap x e z)).compContinuousLinearMap e.toContinuousLinearMap

omit [FiniteDimensional ℝ V] in theorem normalizedForm_contDiffOn
    {U : Set V} (form : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hform : ContDiffOn ℝ ∞ form U) (x : V) (e : V ≃L[ℝ] V) :
    ContDiffOn ℝ ∞ (normalizedForm form x e) (coordinateDomain U x e) := by
  have hcomp : ContDiffOn ℝ ∞ (form ∘ affineMap x e) (coordinateDomain U x e) :=
    hform.comp (affineMap_contDiff x e).contDiffOn fun z hz => hz
  let L : (V [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (V [⋀^Fin 2]→L[ℝ] ℝ) :=
    ContinuousAlternatingMap.compContinuousLinearMapCLM e.toContinuousLinearMap
  change ContDiffOn ℝ ∞ (fun z => L ((form ∘ affineMap x e) z)) (coordinateDomain U x e)
  exact L.contDiff.comp_contDiffOn hcomp

omit [FiniteDimensional ℝ V] in theorem normalizedForm_closed
    {U : Set V} (hU : IsOpen U) (form : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hform : ContDiffOn ℝ ∞ form U) (hclosed : ∀ y ∈ U, extDeriv form y = 0)
    (x : V) (e : V ≃L[ℝ] V) (z : V) (hz : z ∈ coordinateDomain U x e) :
    extDeriv (normalizedForm form x e) z = 0 := by
  have hyU : affineMap x e z ∈ U := hz
  have hformAt : DifferentiableAt ℝ form (affineMap x e z) :=
    (hform.contDiffAt (hU.mem_nhds hyU)).differentiableAt (by simp)
  have heq : normalizedForm form x e = fun y =>
      (form (affineMap x e y)).compContinuousLinearMap
        (fderiv ℝ (affineMap x e) y) := by
    funext y
    rw [fderiv_affineMap]
    rfl
  have hr : minSmoothness ℝ (2 : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by
    rw [minSmoothness_of_isRCLikeNormedField]
    exact ENat.LEInfty.out
  rw [heq, extDeriv_pullback hformAt (affineMap_contDiff x e).contDiffAt hr]
  rw [hclosed _ hyU]
  ext v
  simp [ContinuousAlternatingMap.compContinuousLinearMap_apply]

omit [FiniteDimensional ℝ V] in theorem normalizedForm_zero
    (form : V → V [⋀^Fin 2]→L[ℝ] ℝ) (x : V) (e : V ≃L[ℝ] V) :
    normalizedForm form x e 0 =
      (form x).compContinuousLinearMap e.toContinuousLinearMap := by
  simp [normalizedForm, affineMap]

omit [FiniteDimensional ℝ V] in theorem normalizedForm_zero_nondegenerate
    {U : Set V} (form : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hnondeg : ∀ y ∈ U, ∀ v, v ≠ 0 → ∃ w, form y ![v, w] ≠ 0)
    {x : V} (hx : x ∈ U) (e : V ≃L[ℝ] V) :
    ∀ v, v ≠ 0 → ∃ w, normalizedForm form x e 0 ![v, w] ≠ 0 := by
  intro v hv
  have hev : e v ≠ 0 := fun h => hv (e.injective (by simpa using h))
  obtain ⟨w, hw⟩ := hnondeg x hx (e v) hev
  refine ⟨e.symm w, ?_⟩
  rw [normalizedForm_zero]
  simp only [ContinuousAlternatingMap.compContinuousLinearMap_apply]
  have hvec : e.toContinuousLinearMap ∘ ![v, e.symm w] = ![e v, w] := by
    funext i
    fin_cases i <;> simp
  rw [hvec]
  exact hw

end

end Submission.LocalForms
