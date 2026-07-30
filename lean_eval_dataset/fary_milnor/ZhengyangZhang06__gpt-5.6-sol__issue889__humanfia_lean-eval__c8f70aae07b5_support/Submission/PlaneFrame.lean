import Submission.KnotStability

open LeanEval.Geometry.FaryMilnorProblem
open Set
open scoped Real
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def coordinateAxis (i : Fin 3) : Space :=
  EuclideanSpace.single i 1

@[simp] theorem coordinateAxis_apply (i j : Fin 3) :
    coordinateAxis i j = if i = j then 1 else 0 := by
  by_cases h : i = j
  · simp [coordinateAxis, h]
  · simp [coordinateAxis, h, Ne.symm h]

@[simp] theorem inner_coordinateAxis_left (i : Fin 3) (x : Space) :
    inner ℝ (coordinateAxis i) x = x i := by
  simp [coordinateAxis, EuclideanSpace.inner_single_left]

@[simp] theorem inner_coordinateAxis_right (x : Space) (i : Fin 3) :
    inner ℝ x (coordinateAxis i) = x i := by
  rw [real_inner_comm]
  simp

@[simp] theorem inner_coordinateAxis (i j : Fin 3) :
    inner ℝ (coordinateAxis i) (coordinateAxis j) = if i = j then 1 else 0 := by
  simp

@[simp] theorem norm_coordinateAxis (i : Fin 3) : ‖coordinateAxis i‖ = 1 := by
  have hsquare : ‖coordinateAxis i‖ ^ 2 = 1 := by
    have hinner : inner ℝ (coordinateAxis i) (coordinateAxis i) = 1 := by
      rw [inner_coordinateAxis, if_pos rfl]
    rwa [real_inner_self_eq_norm_sq] at hinner
  have hfactor : (‖coordinateAxis i‖ - 1) * (‖coordinateAxis i‖ + 1) = 0 := by
    nlinarith only [hsquare]
  rcases mul_eq_zero.mp hfactor with h | h
  · linarith
  · linarith [norm_nonneg (coordinateAxis i)]

noncomputable def planeRotation (u v : Space) (θ : ℝ) (x : Space) : Space :=
  x + ((Real.cos θ - 1) * inner ℝ u x - Real.sin θ * inner ℝ v x) • u +
    (Real.sin θ * inner ℝ u x + (Real.cos θ - 1) * inner ℝ v x) • v

theorem planeRotation_apply_left {u v : Space}
    (hu : inner ℝ u u = 1) (hvu : inner ℝ v u = 0) (θ : ℝ) :
    planeRotation u v θ u = Real.cos θ • u + Real.sin θ • v := by
  rw [planeRotation]
  simp only [hu, hvu, mul_one, mul_zero, sub_zero, add_zero]
  module

theorem planeRotation_apply_right {u v : Space}
    (hv : inner ℝ v v = 1) (huv : inner ℝ u v = 0) (θ : ℝ) :
    planeRotation u v θ v = -Real.sin θ • u + Real.cos θ • v := by
  rw [planeRotation]
  simp only [hv, huv, mul_one, mul_zero]
  module

theorem inner_planeRotation_planeRotation {u v x y : Space} {θ : ℝ}
    (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 0) :
    inner ℝ (planeRotation u v θ x) (planeRotation u v θ y) = inner ℝ x y := by
  have hvu : inner ℝ v u = 0 := by rwa [real_inner_comm]
  simp only [planeRotation, inner_add_left, inner_add_right,
    real_inner_smul_left, real_inner_smul_right, hu, hv, huv, hvu]
  rw [show inner ℝ x u = inner ℝ u x by rw [real_inner_comm],
    show inner ℝ x v = inner ℝ v x by rw [real_inner_comm]]
  ring_nf
  linear_combination
    (inner ℝ u x * inner ℝ u y + inner ℝ v x * inner ℝ v y) *
      Real.sin_sq_add_cos_sq θ

theorem norm_planeRotation {u v x : Space} {θ : ℝ}
    (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 0) :
    ‖planeRotation u v θ x‖ = ‖x‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq,
    inner_planeRotation_planeRotation hu hv huv]

theorem planeRotation_ne_zero {u v x : Space} {θ : ℝ}
    (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 0) (hx : x ≠ 0) :
    planeRotation u v θ x ≠ 0 := by
  intro hzero
  have hnorm := norm_planeRotation (θ := θ) hu hv huv (x := x)
  rw [hzero, norm_zero] at hnorm
  exact hx (norm_eq_zero.mp hnorm.symm)

theorem planeRotation_injective {u v : Space} {θ : ℝ}
    (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 0) :
    Function.Injective (planeRotation u v θ) := by
  intro x y hxy
  have hsub : planeRotation u v θ (x - y) =
      planeRotation u v θ x - planeRotation u v θ y := by
    simp only [planeRotation, inner_sub_right]
    module
  have hzero : planeRotation u v θ (x - y) = 0 := by
    rw [hsub, hxy, sub_self]
  apply sub_eq_zero.mp
  by_contra hne
  exact planeRotation_ne_zero (θ := θ) hu hv huv hne hzero

theorem contDiff_planeRotation (u v : Space) :
    ContDiff ℝ ⊤ (fun p : Space × ℝ => planeRotation u v p.2 p.1) := by
  have hinnerU : ContDiff ℝ ⊤ (fun p : Space × ℝ => inner ℝ u p.1) :=
    (innerSL ℝ u).contDiff.comp contDiff_fst
  have hinnerV : ContDiff ℝ ⊤ (fun p : Space × ℝ => inner ℝ v p.1) :=
    (innerSL ℝ v).contDiff.comp contDiff_fst
  have hcos : ContDiff ℝ ⊤ (fun p : Space × ℝ => Real.cos p.2) := by fun_prop
  have hsin : ContDiff ℝ ⊤ (fun p : Space × ℝ => Real.sin p.2) := by fun_prop
  have hcoefU : ContDiff ℝ ⊤ (fun p : Space × ℝ =>
      (Real.cos p.2 - 1) * inner ℝ u p.1 - Real.sin p.2 * inner ℝ v p.1) :=
    ((hcos.sub contDiff_const).mul hinnerU).sub (hsin.mul hinnerV)
  have hcoefV : ContDiff ℝ ⊤ (fun p : Space × ℝ =>
      Real.sin p.2 * inner ℝ u p.1 + (Real.cos p.2 - 1) * inner ℝ v p.1) :=
    (hsin.mul hinnerU).add ((hcos.sub contDiff_const).mul hinnerV)
  simpa [planeRotation] using
    (contDiff_fst.add (hcoefU.smul
      (contDiff_const : ContDiff ℝ ⊤ (fun _ : Space × ℝ => u)))).add
      (hcoefV.smul
        (contDiff_const : ContDiff ℝ ⊤ (fun _ : Space × ℝ => v)))

end Submission.Helpers
