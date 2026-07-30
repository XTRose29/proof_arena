import Mathlib

namespace Submission.Helpers

open Filter
open scoped InnerProductSpace Topology

/-- The second derivative of a twice continuously differentiable real function
is nonnegative at a local minimum. -/
lemma iteratedDeriv_two_nonneg_of_isLocalMin {g : ℝ → ℝ} {x : ℝ}
    (hg : ContDiffAt ℝ 2 g x) (hmin : IsLocalMin g x) :
    0 ≤ iteratedDeriv 2 g x := by
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ, iteratedDeriv_one]
  by_contra hnonneg
  have hneg : deriv (deriv g) x < 0 := lt_of_not_ge hnonneg
  have hmax : IsLocalMax g x :=
    isLocalMax_of_deriv_deriv_neg hneg hmin.deriv_eq_zero hg.continuousAt
  have heq : g =ᶠ[𝓝 x] fun _ ↦ g x := by
    filter_upwards [hmin, hmax] with y hymin hymax
    exact le_antisymm hymax hymin
  have hderiv : deriv g =ᶠ[𝓝 x] fun _ ↦ 0 := by
    simpa using heq.deriv
  have : deriv (deriv g) x = 0 := by
    rw [hderiv.deriv_eq]
    simp
  linarith

/-- The second derivative of a function along an affine line is the
Hessian applied twice to the direction of that line. -/
lemma iteratedDeriv_comp_affineLine_two
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x v : E} (hg : ContDiffAt ℝ 2 g x) :
    iteratedDeriv 2 (g ∘ fun t : ℝ ↦ x + t • v) 0 =
      iteratedFDeriv ℝ 2 g x ![v, v] := by
  let line : ℝ → E := fun t ↦ x + t • v
  have hline : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  have hgAtLine : ContDiffAt ℝ 2 g (line 0) := by
    simpa [line] using hg
  rw [iteratedDeriv_vcomp_two hgAtLine hline]
  have hline_deriv : deriv line = fun _ ↦ v := by
    funext t
    simpa [line] using
      (((hasDerivAt_const t x).add
        ((hasDerivAt_id' t).smul_const v)).deriv)
  have hsecond : iteratedDeriv 2 line 0 = 0 := by
    rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
      iteratedDeriv_one, hline_deriv]
    simp
  rw [hline_deriv, hsecond]
  simp only [line, zero_smul, add_zero, map_zero]
  congr
  funext i
  fin_cases i <;> rfl

/-- Every diagonal entry of the Hessian is nonnegative at a local
minimum. -/
lemma iteratedFDeriv_two_apply_self_nonneg_of_isLocalMin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} {x : E} (hg : ContDiffAt ℝ 2 g x)
    (hmin : IsLocalMin g x) (v : E) :
    0 ≤ iteratedFDeriv ℝ 2 g x ![v, v] := by
  let line : ℝ → E := fun t ↦ x + t • v
  have hline : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  have hgAtLine : ContDiffAt ℝ 2 g (line 0) := by
    simpa [line] using hg
  have hgline : ContDiffAt ℝ 2 (g ∘ line) 0 := by
    exact hgAtLine.comp 0 hline
  have hminline : IsLocalMin (g ∘ line) 0 := by
    have hminAtLine : IsLocalMin g (line 0) := by
      simpa [line] using hmin
    exact hminAtLine.comp_continuous hline.continuousAt
  have hnonneg :=
    iteratedDeriv_two_nonneg_of_isLocalMin hgline hminline
  simpa [line] using
    (iteratedDeriv_comp_affineLine_two (v := v) hg ▸ hnonneg)

/-- At an interior local minimum, the Laplacian of a `C²` real-valued
function is nonnegative. -/
lemma laplacian_nonneg_of_isLocalMin
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {g : E → ℝ} {x : E}
    (hg : ContDiffAt ℝ 2 g x) (hmin : IsLocalMin g x) :
    0 ≤ Laplacian.laplacian g x := by
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis g) x]
  exact Finset.sum_nonneg fun i _ ↦
    iteratedFDeriv_two_apply_self_nonneg_of_isLocalMin hg hmin
      ((stdOrthonormalBasis ℝ E) i)

section PlaneReflection

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Reflection across the affine hyperplane
`{x | ⟪x, e⟫_ℝ = μ}` when `e` is a unit vector. -/
def planeReflect (e : E) (μ : ℝ) (x : E) : E :=
  x - (2 * (⟪x, e⟫_ℝ - μ)) • e

lemma real_inner_planeReflect (e : E) (μ : ℝ) (x : E)
    (he : ‖e‖ = 1) :
    ⟪planeReflect e μ x, e⟫_ℝ = 2 * μ - ⟪x, e⟫_ℝ := by
  rw [planeReflect, inner_sub_left, real_inner_smul_left,
    real_inner_self_eq_norm_sq, he]
  norm_num
  ring

lemma planeReflect_eq_self (e : E) (μ : ℝ) (x : E)
    (hx : ⟪x, e⟫_ℝ = μ) :
    planeReflect e μ x = x := by
  simp [planeReflect, hx]

lemma planeReflect_involutive (e : E) (μ : ℝ) (he : ‖e‖ = 1) :
    Function.Involutive (planeReflect e μ) := by
  intro x
  calc
    planeReflect e μ (planeReflect e μ x) =
        planeReflect e μ x -
          (2 * (⟪planeReflect e μ x, e⟫_ℝ - μ)) • e := rfl
    _ = planeReflect e μ x -
          (2 * ((2 * μ - ⟪x, e⟫_ℝ) - μ)) • e := by
            rw [real_inner_planeReflect e μ x he]
    _ = x := by
      rw [planeReflect]
      module

lemma norm_sq_planeReflect (e : E) (μ : ℝ) (x : E)
    (he : ‖e‖ = 1) :
    ‖planeReflect e μ x‖ ^ 2 =
      ‖x‖ ^ 2 + 4 * μ * (μ - ⟪x, e⟫_ℝ) := by
  rw [planeReflect, norm_sub_sq_real, real_inner_smul_right,
    norm_smul, he, mul_one, Real.norm_eq_abs, sq_abs]
  ring

lemma norm_planeReflect_lt (e : E) (μ : ℝ) (x : E)
    (he : ‖e‖ = 1) (hμ : 0 < μ) (hx : μ < ⟪x, e⟫_ℝ) :
    ‖planeReflect e μ x‖ < ‖x‖ := by
  have hsquare := norm_sq_planeReflect e μ x he
  nlinarith [norm_nonneg (planeReflect e μ x), norm_nonneg x]

lemma norm_planeReflect_le (e : E) (μ : ℝ) (x : E)
    (he : ‖e‖ = 1) (hμ : 0 ≤ μ) (hx : μ ≤ ⟪x, e⟫_ℝ) :
    ‖planeReflect e μ x‖ ≤ ‖x‖ := by
  have hsquare := norm_sq_planeReflect e μ x he
  nlinarith [norm_nonneg (planeReflect e μ x), norm_nonneg x]

end PlaneReflection

end Submission.Helpers
