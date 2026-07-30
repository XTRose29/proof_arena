/-
  Planar change of variables under a holomorphic map (Route-H Stage B).

  Three tools for transporting the residue-ledger integrands between charts of a Riemann
  surface (consumed by `ResidueTheoremStokes.lean`):

  * `det_fderiv_eq_normSq_deriv` — the REAL Jacobian determinant of a ℂ-differentiable map is
    the squared modulus of its complex derivative: `det(fderiv ℝ T z) = |T′(z)|²` (the ℝ-linear
    map "multiply by `T′(z)`" has matrix `[[a, −b], [b, a]]` in the basis `(1, I)`).

  * `integral_image_holomorphic` — the change-of-variables formula
    `∫_{T''U} F = ∫_U normSq(T′) • (F ∘ T)` for `T` holomorphic and injective on a measurable
    `U ⊆ ℂ` (Mathlib's `integral_image_eq_integral_abs_det_fderiv_smul` + the determinant
    identity; unconditional — no integrability hypotheses).

  * `dbar_comp_holomorphic` — the Wirtinger chain rule under a holomorphic inner map:
    `∂̄(g∘T)(z) = ∂̄g(T z) · conj T′(z)` (the `(0,1)`-form coefficient transformation rule).
    Plus `deriv_mul_deriv_inverse`, the chain-rule inversion `S′(Tz)·T′(z) = 1` for a local
    inverse `S` of `T`.

  Everything here is complete and depends on no unproved lemma.
-/
import Mathlib
import Submission.DbarDisk

-- The ℂ-as-ℝ-module diamond fix used across the Dolbeault tree.
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Complex MeasureTheory Set Filter Topology

namespace Jacobians.Dolbeault

/-! ### The determinant of multiplication by a complex number, as an ℝ-linear map -/

/-- The ℝ-linear endomorphism of `ℂ` given by multiplication by `d` (the `restrictScalars` of the
canonical `smulRight` form of the complex derivative) has determinant `normSq d = |d|²`. -/
theorem det_restrictScalars_smulRight (d : ℂ) :
    (((1 : ℂ →L[ℂ] ℂ).smulRight d).restrictScalars ℝ : ℂ →L[ℝ] ℂ).det
      = Complex.normSq d := by
  show LinearMap.det _ = _
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp only [LinearMap.toMatrix_apply, Complex.coe_basisOneI_repr, Complex.coe_basisOneI,
    ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.one_apply, smul_eq_mul,
    Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, one_mul,
    Complex.normSq_apply, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.one_re, Complex.one_im]
  ring

/-- **The real Jacobian of a holomorphic map**: at a point of ℂ-differentiability,
`det (fderiv ℝ T z) = normSq (deriv T z)`. -/
theorem det_fderiv_eq_normSq_deriv {T : ℂ → ℂ} {z : ℂ} (hT : DifferentiableAt ℂ T z) :
    (fderiv ℝ T z).det = Complex.normSq (deriv T z) := by
  have hfd : fderiv ℝ T z = ((1 : ℂ →L[ℂ] ℂ).smulRight (deriv T z)).restrictScalars ℝ :=
    ((hT.hasDerivAt.hasFDerivAt).restrictScalars ℝ).fderiv
  rw [hfd, det_restrictScalars_smulRight]

/-! ### Change of variables under a holomorphic injective map -/

/-- **Planar holomorphic change of variables** (unconditional — both sides may fail to be
integrable, in which case both are `0`):

  `∫_{T''U} F(w) dw = ∫_U normSq(T′(z)) • F(T(z)) dz`

for `T` ℂ-differentiable and injective on the measurable `U`. -/
theorem integral_image_holomorphic {U : Set ℂ} (hU : MeasurableSet U) {T : ℂ → ℂ}
    (hT : ∀ z ∈ U, DifferentiableAt ℂ T z) (hinj : Set.InjOn T U) (F : ℂ → ℂ) :
    ∫ w in T '' U, F w = ∫ z in U, Complex.normSq (deriv T z) • F (T z) := by
  have h := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (μ := volume) hU
    (f' := fun z => ((1 : ℂ →L[ℂ] ℂ).smulRight (deriv T z)).restrictScalars ℝ)
    (fun z hz => (((hT z hz).hasDerivAt.hasFDerivAt).restrictScalars ℝ).hasFDerivWithinAt)
    hinj F
  rw [h]
  refine setIntegral_congr_fun hU (fun z hz => ?_)
  rw [det_restrictScalars_smulRight, abs_of_nonneg (Complex.normSq_nonneg _)]

/-! ### The Wirtinger chain rule under a holomorphic inner map -/

/-- **The `∂̄` chain rule for `g ∘ T` with `T` holomorphic**:

  `∂̄(g∘T)(z) = ∂̄g(T z) · conj (T′ z)`.

This is the transformation rule of a `(0,1)`-form coefficient.  Pure linear algebra on the real
Fréchet derivatives: `fderiv ℝ T z` is multiplication by `c := T′(z)`, and for any ℝ-linear
`M : ℂ → ℂ`, `M(c) + i·M(i·c) = conj(c)·(M(1) + i·M(i))` (decompose `c = c.re + c.im·i`). -/
theorem dbar_comp_holomorphic {g T : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℝ g (T z)) (hT : DifferentiableAt ℂ T z) :
    DbarDisk.dbar (g ∘ T) z = DbarDisk.dbar g (T z) * (starRingEnd ℂ) (deriv T z) := by
  have hTr : DifferentiableAt ℝ T z := hT.restrictScalars ℝ
  have hcomp : fderiv ℝ (g ∘ T) z = (fderiv ℝ g (T z)).comp (fderiv ℝ T z) :=
    fderiv_comp z hg hTr
  have hfd : fderiv ℝ T z = ((1 : ℂ →L[ℂ] ℂ).smulRight (deriv T z)).restrictScalars ℝ :=
    ((hT.hasDerivAt.hasFDerivAt).restrictScalars ℝ).fderiv
  set c := deriv T z with hc
  set M := fderiv ℝ g (T z) with hM
  have hc_decomp : c = c.re • (1 : ℂ) + c.im • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    exact (Complex.re_add_im c).symm
  have hIc_decomp : Complex.I * c = (-c.im) • (1 : ℂ) + c.re • Complex.I := by
    rw [Complex.real_smul, Complex.real_smul, mul_one]
    apply Complex.ext <;> simp
  have hMc : M c = c.re • M 1 + c.im • M Complex.I := by
    conv_lhs => rw [hc_decomp]
    rw [map_add, map_smul, map_smul]
  have hMIc : M (Complex.I * c) = (-c.im) • M 1 + c.re • M Complex.I := by
    conv_lhs => rw [hIc_decomp]
    rw [map_add, map_smul, map_smul]
  have hconj : (starRingEnd ℂ) c = (c.re : ℂ) - (c.im : ℂ) * Complex.I := by
    apply Complex.ext <;> simp
  unfold DbarDisk.dbar
  rw [hcomp, hfd]
  simp only [ContinuousLinearMap.coe_comp', Function.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul, one_mul]
  rw [show Complex.I * c = (Complex.I : ℂ) * c from rfl] at hMIc
  rw [← hM, hMc, hMIc, hconj]
  simp only [Complex.real_smul]
  push_cast
  linear_combination ((c.im : ℂ) * M Complex.I / 2) * Complex.I_sq

/-- The chain-rule inversion: if `S` inverts `T` near `z` (`S ∘ T = id` as germs), then
`S′(T z) · T′(z) = 1`.  Gives the derivative cancellations of the chart-transport algebra. -/
theorem deriv_mul_deriv_inverse {T S : ℂ → ℂ} {z : ℂ}
    (hT : DifferentiableAt ℂ T z) (hS : DifferentiableAt ℂ S (T z))
    (hid : (S ∘ T) =ᶠ[𝓝 z] id) :
    deriv S (T z) * deriv T z = 1 := by
  have h := deriv_comp z hS hT
  rw [hid.deriv_eq, deriv_id] at h
  exact h.symm

/-- The combined transport factor: for `T` holomorphic at `z` with local inverse `S` at `T z`,
`S′(T z) · normSq (T′ z) = conj (T′ z)` — exactly how the `(1,0)`-coefficient derivative and the
real Jacobian combine in the ledger's change of variables. -/
theorem deriv_inverse_mul_normSq {T S : ℂ → ℂ} {z : ℂ}
    (hT : DifferentiableAt ℂ T z) (hS : DifferentiableAt ℂ S (T z))
    (hid : (S ∘ T) =ᶠ[𝓝 z] id) :
    deriv S (T z) * (Complex.normSq (deriv T z) : ℂ) = (starRingEnd ℂ) (deriv T z) := by
  have hinv := deriv_mul_deriv_inverse hT hS hid
  have hns : (Complex.normSq (deriv T z) : ℂ) = deriv T z * (starRingEnd ℂ) (deriv T z) :=
    (Complex.mul_conj (deriv T z)).symm
  rw [hns, ← mul_assoc, hinv, one_mul]

end Jacobians.Dolbeault
