/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-2 (planar layer): the Forster 20.3 integration atoms on `ℂ`

The planar heart of Forster's Lemma 20.5 identity `∫_c ω = (1/2πi)∬(df/f)∧ω`.  This file
provides the Wirtinger `∂`-calculus (`del`, conjugate partner of the repo's `DbarDisk.dbar`)
and the two integration atoms the identity rests on:

  1. `integral_logDeriv_cross_eq_zero` — `∫_ℂ (∂W/W·∂̄G − ∂̄W/W·∂G) dA = 0` for smooth
     nonvanishing `W` and `G ∈ C_c^∞(ℂ)`: this is `∬ d(G·dW/W) = 0` in Wirtinger coordinates
     (compact-support Stokes `∫∂̄φ = ∫∂φ = 0`, `PlanarCompactSupportStokes`) plus the mixed
     Wirtinger commutation `∂̄∂W = ∂∂̄W` (`dbar_del_eq_del_dbar`, symmetry of the second
     Fréchet derivative);
  2. `integral_dbar_mul_inv_sub` — `∫_ℂ ∂̄G·((z−α)⁻¹ − (z−β)⁻¹) dA = π·(G β − G α)`
     (two applications of Cauchy–Pompeiu, `DbarDisk.cauchyPompeiu_area`).

These are exactly the "planar Stokes + residue" ingredients of Forster's proof of 20.3
(p. 160): the first kills the `dW/W` part of `df/f`, the second evaluates the two poles.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.3 (p. 160);
plan `docs/walls_bc_plan_2026-06-10.md`, phase C-2 (E2).
-/
import Submission.Dolbeault.AnnulusResidueIntegral

noncomputable section

-- ℂ-as-ℝ-module diamond discipline (as in `DbarOpenDisk`/`AnnulusResidueIntegral`).
set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open Complex Metric MeasureTheory Filter Set DbarDisk
open scoped Real Topology ContDiff

namespace Jacobians.AbelPlanar

/-! ### The Wirtinger holomorphic derivative `∂`

`DbarDisk.dbar` is the repo's `∂̄ = ½(∂ₓ + i∂_y)`; here we add its conjugate partner
`del = ∂ = ½(∂ₓ − i∂_y)` and the calculus the 20.3 Stokes argument needs. -/

/-- The Wirtinger holomorphic derivative `∂f = ½(∂ₓf − i·∂_yf)`, via the real Fréchet
derivative at the basis directions `1, I` (conjugate partner of `DbarDisk.dbar`). -/
def del (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  (2 : ℂ)⁻¹ * (fderiv ℝ f z 1 - Complex.I * fderiv ℝ f z Complex.I)

/-- `∂` only depends on the germ. -/
theorem del_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : del f z = del g z := by
  unfold del
  rw [h.fderiv_eq]

/-- **`∂` of a holomorphic function is its complex derivative** (the Wirtinger split of the
Cauchy–Riemann equations; companion of `dbar_eq_zero_of_differentiableAt`). -/
theorem del_eq_deriv_of_differentiableAt {f : ℂ → ℂ} {z : ℂ}
    (hf : DifferentiableAt ℂ f z) : del f z = deriv f z := by
  have hr : fderiv ℝ f z = (deriv f z) • (1 : ℂ →L[ℝ] ℂ) :=
    hf.hasDerivAt.complexToReal_fderiv.fderiv
  rw [del, hr]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, smul_eq_mul,
    mul_one]
  have hII : Complex.I * (deriv f z * Complex.I) = - deriv f z := by
    rw [show Complex.I * (deriv f z * Complex.I) = deriv f z * (Complex.I * Complex.I) by ring,
      Complex.I_mul_I]; ring
  rw [hII]; ring

/-- **Wirtinger–Leibniz product rule for `∂`.** -/
theorem del_fun_mul {f g : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z)
    (hg : DifferentiableAt ℝ g z) :
    del (fun w => f w * g w) z = f z * del g z + g z * del f z := by
  have h : HasFDerivAt (fun w => f w * g w) (f z • fderiv ℝ g z + g z • fderiv ℝ f z) z :=
    hf.hasFDerivAt.mul hg.hasFDerivAt
  unfold del
  rw [h.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- `∂̄` of a pointwise inverse: `∂̄(f⁻¹) = −f⁻²·∂̄f` at points where `f ≠ 0`. -/
theorem dbar_fun_inv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (h0 : f z ≠ 0) :
    dbar (fun w => (f w)⁻¹) z = -((f z) ^ 2)⁻¹ * dbar f z := by
  have hinv : HasDerivAt Inv.inv (-((f z) ^ 2)⁻¹) (f z) := hasDerivAt_inv h0
  have hcomp : HasFDerivAt (fun w => (f w)⁻¹)
      (((-((f z) ^ 2)⁻¹) • (1 : ℂ →L[ℝ] ℂ)).comp (fderiv ℝ f z)) z :=
    (hinv.complexToReal_fderiv).comp z hf.hasFDerivAt
  unfold dbar
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

/-- `∂` of a pointwise inverse: `∂(f⁻¹) = −f⁻²·∂f` at points where `f ≠ 0`. -/
theorem del_fun_inv {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℝ f z) (h0 : f z ≠ 0) :
    del (fun w => (f w)⁻¹) z = -((f z) ^ 2)⁻¹ * del f z := by
  have hinv : HasDerivAt Inv.inv (-((f z) ^ 2)⁻¹) (f z) := hasDerivAt_inv h0
  have hcomp : HasFDerivAt (fun w => (f w)⁻¹)
      (((-((f z) ^ 2)⁻¹) • (1 : ℂ →L[ℝ] ℂ)).comp (fderiv ℝ f z)) z :=
    (hinv.complexToReal_fderiv).comp z hf.hasFDerivAt
  unfold del
  rw [hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

/-! ### Smoothness of the Wirtinger reads -/

/-- The directional Fréchet read `z ↦ (fderiv ℝ f z) v` of a `C^∞` function is `C^∞`. -/
theorem contDiff_fderiv_apply {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (v : ℂ) :
    ContDiff ℝ (⊤ : ℕ∞) (fun z => fderiv ℝ f z v) := by
  have h1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  exact (ContinuousLinearMap.apply ℝ ℂ v).contDiff.comp h1

/-- `∂̄f` is `C^∞` for `C^∞` `f`. -/
theorem contDiff_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (dbar f) := by
  have h1 := contDiff_fderiv_apply hf 1
  have hI := contDiff_fderiv_apply hf Complex.I
  exact contDiff_const.mul (h1.add (contDiff_const.mul hI))

/-- `∂f` is `C^∞` for `C^∞` `f`. -/
theorem contDiff_del {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) :
    ContDiff ℝ (⊤ : ℕ∞) (del f) := by
  have h1 := contDiff_fderiv_apply hf 1
  have hI := contDiff_fderiv_apply hf Complex.I
  exact contDiff_const.mul (h1.sub (contDiff_const.mul hI))

/-- `∂f` inherits compact support from `f` (companion of `hasCompactSupport_dbar`). -/
theorem hasCompactSupport_del {f : ℂ → ℂ} (hf : HasCompactSupport f) :
    HasCompactSupport (del f) := by
  apply HasCompactSupport.intro (hf.fderiv ℝ).isCompact
  intro z hz
  have : fderiv ℝ f z = 0 := image_eq_zero_of_notMem_tsupport hz
  simp [del, this]

/-! ### The mixed Wirtinger derivatives commute -/

/-- **`∂̄∂f = ∂∂̄f`** for `C^∞` `f` (symmetry of the second Fréchet derivative read in the
Wirtinger frame). -/
theorem dbar_del_eq_del_dbar {f : ℂ → ℂ} (hf : ContDiff ℝ (⊤ : ℕ∞) f) (z : ℂ) :
    dbar (del f) z = del (dbar f) z := by
  -- the second derivative and its symmetry
  have hsymm : IsSymmSndFDerivAt ℝ f z := by
    have h2 : ContDiffAt ℝ 2 f z := hf.contDiffAt.of_le (WithTop.coe_le_coe.mpr le_top)
    refine h2.isSymmSndFDerivAt ?_
    rw [minSmoothness_of_isRCLikeNormedField]
  have hf1 : ContDiff ℝ (⊤ : ℕ∞) (fderiv ℝ f) := hf.fderiv_right (by simp)
  have hD2 : HasFDerivAt (fderiv ℝ f) (fderiv ℝ (fderiv ℝ f) z) z :=
    ((hf1.differentiable (by simp)).differentiableAt).hasFDerivAt
  set D2 : ℂ →L[ℝ] ℂ →L[ℝ] ℂ := fderiv ℝ (fderiv ℝ f) z with hD2def
  -- Fréchet derivatives of the directional reads
  have hread : ∀ v : ℂ, HasFDerivAt (fun w => fderiv ℝ f w v)
      ((ContinuousLinearMap.apply ℝ ℂ v).comp D2) z :=
    fun v => (ContinuousLinearMap.apply ℝ ℂ v).hasFDerivAt.comp z hD2
  -- Fréchet derivatives of `∂f` and `∂̄f`
  have hdel : HasFDerivAt (del f)
      ((2 : ℂ)⁻¹ • (((ContinuousLinearMap.apply ℝ ℂ 1).comp D2)
        - Complex.I • ((ContinuousLinearMap.apply ℝ ℂ Complex.I).comp D2))) z := by
    have h := ((hread 1).sub ((hread Complex.I).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    simpa [smul_smul, ContinuousLinearMap.smul_comp] using h
  have hdbar : HasFDerivAt (dbar f)
      ((2 : ℂ)⁻¹ • (((ContinuousLinearMap.apply ℝ ℂ 1).comp D2)
        + Complex.I • ((ContinuousLinearMap.apply ℝ ℂ Complex.I).comp D2))) z := by
    have h := ((hread 1).add ((hread Complex.I).const_mul Complex.I)).const_mul (2 : ℂ)⁻¹
    simpa [smul_smul, ContinuousLinearMap.smul_comp] using h
  -- evaluate both sides in the `{1, I}` frame and use the symmetry `D2 u v = D2 v u`
  show (2 : ℂ)⁻¹ * (fderiv ℝ (del f) z 1 + Complex.I * fderiv ℝ (del f) z Complex.I)
      = (2 : ℂ)⁻¹ * (fderiv ℝ (dbar f) z 1 - Complex.I * fderiv ℝ (dbar f) z Complex.I)
  rw [hdel.fderiv, hdbar.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.sub_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.apply_apply, smul_eq_mul]
  have hsym1I : D2 1 Complex.I = D2 Complex.I 1 := hsymm.eq 1 Complex.I
  rw [hsym1I]
  ring

/-! ### Integration atom 1: the cross-term Stokes identity -/

/-- `∫_ℂ ∂φ = 0` for `C¹` compactly-supported `φ` (named-`del` form of
`Jacobians.Dolbeault.integral_del_eq_zero`). -/
theorem integral_del_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) : ∫ z, del φ z = 0 :=
  Jacobians.Dolbeault.integral_del_eq_zero φ hφ hsupp

/-- `∫_ℂ ∂̄φ = 0` for `C¹` compactly-supported `φ` (re-export of the
`PlanarCompactSupportStokes` atom in the `dbar` spelling). -/
theorem integral_dbar_eq_zero {φ : ℂ → ℂ} (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) : ∫ z, dbar φ z = 0 :=
  Jacobians.Dolbeault.integral_dbar_eq_zero φ hφ hsupp

/-- **The 20.3 cross-term Stokes identity**: for smooth nonvanishing `W` and `G ∈ C_c^∞(ℂ)`,

  `∫_ℂ (∂W/W·∂̄G − ∂̄W/W·∂G) dA = 0`.

This is `∬_ℂ d(G·dW/W) = 0` read in Wirtinger coordinates: expand `∫∂̄(G·∂W/W) = 0` and
`∫∂(G·∂̄W/W) = 0` (compact-support Stokes) and cancel the mixed second Wirtinger derivatives
of `W` (`dbar_del_eq_del_dbar`). -/
theorem integral_logDeriv_cross_eq_zero {W G : ℂ → ℂ}
    (hW : ContDiff ℝ (⊤ : ℕ∞) W) (hW0 : ∀ z, W z ≠ 0)
    (hG : ContDiff ℝ (⊤ : ℕ∞) G) (hGsupp : HasCompactSupport G) :
    ∫ z, (del W z / W z * dbar G z - dbar W z / W z * del G z) = 0 := by
  have hWd : Differentiable ℝ W := hW.differentiable (by simp)
  have hGd : Differentiable ℝ G := hG.differentiable (by simp)
  have hdelW : ContDiff ℝ (⊤ : ℕ∞) (del W) := contDiff_del hW
  have hdbarW : ContDiff ℝ (⊤ : ℕ∞) (dbar W) := contDiff_dbar hW
  have hinvW : ContDiff ℝ (⊤ : ℕ∞) (fun z => (W z)⁻¹) :=
    contDiff_iff_contDiffAt.mpr fun z => (contDiffAt_inv ℝ (hW0 z)).comp z hW.contDiffAt
  have hP : ContDiff ℝ (⊤ : ℕ∞) (fun z => del W z / W z) := by
    simp only [div_eq_mul_inv]
    exact hdelW.mul hinvW
  have hU : ContDiff ℝ (⊤ : ℕ∞) (fun z => dbar W z / W z) := by
    simp only [div_eq_mul_inv]
    exact hdbarW.mul hinvW
  -- the two compactly-supported products
  set A : ℂ → ℂ := fun z => G z * (del W z / W z) with hAdef
  set B : ℂ → ℂ := fun z => G z * (dbar W z / W z) with hBdef
  have hA : ContDiff ℝ (⊤ : ℕ∞) A := hG.mul hP
  have hB : ContDiff ℝ (⊤ : ℕ∞) B := hG.mul hU
  have hAsupp : HasCompactSupport A := hGsupp.mul_right
  have hBsupp : HasCompactSupport B := hGsupp.mul_right
  -- the two Stokes identities
  have h1 : ∫ z, dbar A z = 0 := integral_dbar_eq_zero (hA.of_le (by simp)) hAsupp
  have h2 : ∫ z, del B z = 0 := integral_del_eq_zero (hB.of_le (by simp)) hBsupp
  -- pointwise: `∂̄A − ∂B = ∂W/W·∂̄G − ∂̄W/W·∂G` (the `G·(∂̄(∂W/W) − ∂(∂̄W/W))` term cancels)
  have hpt : ∀ z, del W z / W z * dbar G z - dbar W z / W z * del G z
      = dbar A z - del B z := by
    intro z
    have hexpA : dbar A z = G z * dbar (fun w => del W w / W w) z
        + (del W z / W z) * dbar G z := by
      rw [hAdef]
      exact dbar_fun_mul hGd.differentiableAt (hP.differentiable (by simp)).differentiableAt
    have hexpB : del B z = G z * del (fun w => dbar W w / W w) z
        + (dbar W z / W z) * del G z := by
      rw [hBdef]
      exact del_fun_mul hGd.differentiableAt (hU.differentiable (by simp)).differentiableAt
    -- the mixed-derivative cancellation: `∂̄(∂W·W⁻¹) = ∂(∂̄W·W⁻¹)`
    have hmixed : dbar (fun w => del W w / W w) z = del (fun w => dbar W w / W w) z := by
      have hdelWd : DifferentiableAt ℝ (del W) z :=
        (hdelW.differentiable (by simp)).differentiableAt
      have hdbarWd : DifferentiableAt ℝ (dbar W) z :=
        (hdbarW.differentiable (by simp)).differentiableAt
      have hinvWd : DifferentiableAt ℝ (fun w => (W w)⁻¹) z :=
        (hinvW.differentiable (by simp)).differentiableAt
      have e1 : dbar (fun w => del W w / W w) z
          = del W z * dbar (fun w => (W w)⁻¹) z + (W z)⁻¹ * dbar (del W) z := by
        have h := dbar_fun_mul hdelWd hinvWd
        simpa only [div_eq_mul_inv] using h
      have e2 : del (fun w => dbar W w / W w) z
          = dbar W z * del (fun w => (W w)⁻¹) z + (W z)⁻¹ * del (dbar W) z := by
        have h := del_fun_mul hdbarWd hinvWd
        simpa only [div_eq_mul_inv] using h
      rw [e1, e2, dbar_fun_inv hWd.differentiableAt (hW0 z),
        del_fun_inv hWd.differentiableAt (hW0 z), dbar_del_eq_del_dbar hW z]
      ring
    rw [hexpA, hexpB, hmixed]
    ring
  -- assemble
  have hint1 : Integrable (fun z => dbar A z) volume :=
    (contDiff_dbar hA).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_dbar hAsupp)
  have hint2 : Integrable (fun z => del B z) volume :=
    (contDiff_del hB).continuous.integrable_of_hasCompactSupport
      (hasCompactSupport_del hBsupp)
  calc ∫ z, (del W z / W z * dbar G z - dbar W z / W z * del G z)
      = ∫ z, (dbar A z - del B z) := by
        exact integral_congr_ae (Eventually.of_forall hpt)
    _ = (∫ z, dbar A z) - ∫ z, del B z := integral_sub hint1 hint2
    _ = 0 := by rw [h1, h2, sub_self]

/-! ### Integration atom 2: the two-pole Cauchy–Pompeiu pairing -/

/-- The pole pairing integrand `∂̄G·(z − a)⁻¹` is integrable for `G ∈ C_c^∞` (transport of
`DbarDisk.integrable_dbar_mul_cauchyKernel`). -/
theorem integrable_dbar_mul_inv {G : ℂ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGsupp : HasCompactSupport G) (a : ℂ) :
    Integrable (fun z => dbar G z * (z - a)⁻¹) volume := by
  have h := (integrable_dbar_mul_cauchyKernel hG hGsupp a).const_mul (-(π : ℂ))
  refine h.congr (Eventually.of_forall fun z => ?_)
  show -(π : ℂ) * (dbar G z * cauchyKernel (a - z)) = dbar G z * (z - a)⁻¹
  have hker : cauchyKernel (a - z) = 1 / ((π : ℂ) * (a - z)) := rfl
  rcases eq_or_ne z a with rfl | hz
  · rw [hker, sub_self]
    simp
  · have hπ : (π : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
    have haz : a - z ≠ 0 := sub_ne_zero.mpr (fun h' => hz h'.symm)
    rw [hker]
    field_simp [sub_ne_zero.mpr hz]
    ring

/-- **The two-pole Cauchy–Pompeiu pairing** (the residue half of Forster 20.3):

  `∫_ℂ ∂̄G·((z−α)⁻¹ − (z−β)⁻¹) dA = π·(G β − G α)`   for `G ∈ C_c^∞(ℂ)`. -/
theorem integral_dbar_mul_inv_sub {G : ℂ → ℂ} (hG : ContDiff ℝ (⊤ : ℕ∞) G)
    (hGsupp : HasCompactSupport G) (α β : ℂ) :
    ∫ z, dbar G z * ((z - α)⁻¹ - (z - β)⁻¹) = (π : ℂ) * (G β - G α) := by
  have hα := integrable_dbar_mul_inv hG hGsupp α
  have hβ := integrable_dbar_mul_inv hG hGsupp β
  have hsplit : ∫ z, dbar G z * ((z - α)⁻¹ - (z - β)⁻¹)
      = (∫ z, dbar G z * (z - α)⁻¹) - ∫ z, dbar G z * (z - β)⁻¹ := by
    rw [← integral_sub hα hβ]
    exact integral_congr_ae (Eventually.of_forall fun z => by ring)
  have hpomp : ∀ w : ℂ, ∫ z, dbar G z * (z - w)⁻¹ = -π * G w := by
    intro w
    have h := cauchyPompeiu_area hG hGsupp w
    rw [← h]
    exact integral_congr_ae (Eventually.of_forall fun z =>
      (div_eq_mul_inv (dbar G z) (z - w)).symm)
  rw [hsplit, hpomp α, hpomp β]
  ring

/-! ### The planar piece solution (Forster 20.5(a))

For endpoints `α, β ∈ ball c₀ ρ`, the data of Forster's explicit per-piece weak solution
`f₀ = exp(ψ·log((z−β)/(z−α)))`, normalized through the smooth nonvanishing cofactor
`W`: the actual solution is `F = W·(z−β)/(z−α)`, with `W ≡ 1` on the inner ball (where the
curve and its endpoints live) and `W = (z−α)/(z−β)` outside `ball c₀ (5ρ)` (so `F ≡ 1`
there, ready to be glued to `1` on the surface).  Its `∂̄`-datum `U = ∂̄W/W` (which is
`∂̄F/F` away from `α, β`) is smooth, supported in the closed annulus `4ρ ≤ dist ≤ 5ρ`. -/

/-- **Planar piece-solution data** (Forster 20.5(a), normalized): a smooth nonvanishing
cofactor `W` with `W ≡ 1` inside and `W = (z−α)/(z−β)` outside; the per-piece weak solution
is `F = W·(z−β)/(z−α)` and its global `∂̄`-datum is `U = ∂̄W/W`. -/
structure PlanarPieceSolution (c₀ : ℂ) (ρ : ℝ) (α β : ℂ) where
  /-- the smooth nonvanishing cofactor -/
  W : ℂ → ℂ
  ρ_pos : 0 < ρ
  dist_alpha : dist α c₀ < ρ
  dist_beta : dist β c₀ < ρ
  smooth : ContDiff ℝ (⊤ : ℕ∞) W
  ne_zero : ∀ z, W z ≠ 0
  inner : ∀ z, dist z c₀ < 4 * ρ → W z = 1
  outer : ∀ z, 5 * ρ < dist z c₀ → W z = (z - α) / (z - β)

namespace PlanarPieceSolution

variable {c₀ α β : ℂ} {ρ : ℝ} (S : PlanarPieceSolution c₀ ρ α β)

/-- The piece solution `F = W·(z−β)/(z−α)`: simple zero at `β`, simple pole at `α`
(junk-normalized to `0` at `α`), `≡ 1` outside `ball c₀ (5ρ)`. -/
def F : ℂ → ℂ := fun z => S.W z * (z - β) / (z - α)

/-- The `∂̄`-datum `U = ∂̄W/W` of the piece solution (equal to `∂̄F/F` away from `α, β`,
smooth everywhere). -/
def U : ℂ → ℂ := fun z => dbar S.W z / S.W z

theorem U_smooth : ContDiff ℝ (⊤ : ℕ∞) S.U := by
  have hinv : ContDiff ℝ (⊤ : ℕ∞) (fun z => (S.W z)⁻¹) :=
    contDiff_iff_contDiffAt.mpr fun z =>
      (contDiffAt_inv ℝ (S.ne_zero z)).comp z S.smooth.contDiffAt
  have h : ContDiff ℝ (⊤ : ℕ∞) (fun z => dbar S.W z * (S.W z)⁻¹) :=
    (contDiff_dbar S.smooth).mul hinv
  simpa only [U, div_eq_mul_inv] using h

theorem U_continuous : Continuous S.U := S.U_smooth.continuous

/-- `U` vanishes on the inner ball (`W ≡ 1` there). -/
theorem U_eq_zero_inner {z : ℂ} (hz : dist z c₀ < 4 * ρ) : S.U z = 0 := by
  have hcongr : S.W =ᶠ[𝓝 z] fun _ => 1 := by
    filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball c₀ (4 * ρ) from hz)] with w hw
    exact S.inner w hw
  have : dbar S.W z = 0 := by
    rw [dbar_congr hcongr]
    simp
  simp [U, this]

/-- `U` vanishes outside `closedBall c₀ (5ρ)` (`W` is holomorphic there). -/
theorem U_eq_zero_outer {z : ℂ} (hz : 5 * ρ < dist z c₀) : S.U z = 0 := by
  have hzβ : z - β ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    rw [h] at hz
    linarith [S.dist_beta, S.ρ_pos]
  have hcongr : S.W =ᶠ[𝓝 z] fun w => (w - α) / (w - β) := by
    have hopen : IsOpen {w : ℂ | 5 * ρ < dist w c₀} :=
      isOpen_lt continuous_const (continuous_id.dist continuous_const)
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact S.outer w hw
  have hdiff : DifferentiableAt ℂ (fun w : ℂ => (w - α) / (w - β)) z :=
    (differentiableAt_id.sub_const α).div (differentiableAt_id.sub_const β) hzβ
  have : dbar S.W z = 0 := by
    rw [dbar_congr hcongr]
    exact dbar_eq_zero_of_differentiableAt hdiff
  simp [U, this]

/-- The support window of `U`: nonvanishing forces `4ρ ≤ dist z c₀ ≤ 5ρ`. -/
theorem dist_mem_of_U_ne_zero {z : ℂ} (hz : S.U z ≠ 0) :
    4 * ρ ≤ dist z c₀ ∧ dist z c₀ ≤ 5 * ρ := by
  constructor
  · by_contra h
    exact hz (S.U_eq_zero_inner (lt_of_not_ge h))
  · by_contra h
    exact hz (S.U_eq_zero_outer (lt_of_not_ge h))

/-- `U` has compact support (inside `closedBall c₀ (5ρ)`). -/
theorem U_hasCompactSupport : HasCompactSupport S.U := by
  refine HasCompactSupport.intro (isCompact_closedBall c₀ (5 * ρ)) fun z hz => ?_
  by_contra h
  exact hz (mem_closedBall.mpr (S.dist_mem_of_U_ne_zero h).2)

/-- Outside `ball c₀ (5ρ)` the piece solution is `≡ 1`. -/
theorem F_eq_one_outer {z : ℂ} (hz : 5 * ρ < dist z c₀) : S.F z = 1 := by
  have hzα : z - α ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    rw [h] at hz
    linarith [S.dist_alpha, S.ρ_pos]
  have hzβ : z - β ≠ 0 := by
    refine sub_ne_zero.mpr fun h => ?_
    rw [h] at hz
    linarith [S.dist_beta, S.ρ_pos]
  rw [F, S.outer z hz]
  field_simp

/-- The piece solution is nonvanishing away from the two endpoints. -/
theorem F_ne_zero {z : ℂ} (hzα : z ≠ α) (hzβ : z ≠ β) : S.F z ≠ 0 := by
  have h1 : z - β ≠ 0 := sub_ne_zero.mpr hzβ
  have h2 : z - α ≠ 0 := sub_ne_zero.mpr hzα
  exact div_ne_zero (mul_ne_zero (S.ne_zero z) h1) h2

@[simp] theorem F_alpha : S.F α = 0 := by
  rw [F, sub_self, div_zero]

@[simp] theorem F_beta : S.F β = 0 := by
  rw [F, sub_self, mul_zero, zero_div]

/-! ### The 20.5(a) identity: `∫ U·g′ = π·(g β − g α)` -/

/-- **The planar piece identity** (Forster 20.3 + 20.5(a) for holomorphic test data): if `g`
is a primitive of `h` on `ball c₀ (8ρ)`, then

  `∫_ℂ U·h dA = π·(g β − g α)`.

In Forster's notation this is `(1/2πi)∬ (df₀/f₀)∧ω = ∫_c ω` for `ω = h·dz = dg`:
`(df₀/f₀)∧(h dz) = U·h·dz̄∧dz = 2i·U·h·dA`, so `∬(df₀/f₀)∧ω = 2i·π·(g β − g α)` matches
`2πi·(g(b) − g(a))` exactly. -/
theorem integral_U_mul {g h : ℂ → ℂ}
    (hg : ∀ z ∈ ball c₀ (8 * ρ), HasDerivAt g (h z) z) :
    ∫ z, S.U z * h z = (π : ℂ) * (g β - g α) := by
  have hρ := S.ρ_pos
  have hαmem8 : α ∈ ball c₀ (8 * ρ) := mem_ball.mpr (by linarith [S.dist_alpha])
  have hβmem8 : β ∈ ball c₀ (8 * ρ) := mem_ball.mpr (by linarith [S.dist_beta])
  -- analyticity of `g` on the ball
  have hganal : AnalyticOnNhd ℂ g (ball c₀ (8 * ρ)) := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) isOpen_ball
    exact ((hg z hz).differentiableAt).differentiableWithinAt
  -- the bump truncation `G = χ·g`
  set χ : ContDiffBump c₀ := ⟨6 * ρ, 7 * ρ, by linarith, by linarith⟩ with hχdef
  set G : ℂ → ℂ := fun z => ((χ z : ℝ) : ℂ) * g z with hGdef
  have hχsmooth : ContDiff ℝ (⊤ : ℕ∞) (fun z : ℂ => ((χ z : ℝ) : ℂ)) :=
    Complex.ofRealCLM.contDiff.comp χ.contDiff
  -- `G = g` near every point of `ball c₀ (6ρ)`
  have hGg : ∀ z ∈ ball c₀ (6 * ρ), G =ᶠ[𝓝 z] g := by
    intro z hz
    filter_upwards [isOpen_ball.mem_nhds hz] with w hw
    have h1 : χ w = 1 := χ.one_of_mem_closedBall (ball_subset_closedBall hw)
    rw [hGdef]
    simp [h1]
  have hGsmooth : ContDiff ℝ (⊤ : ℕ∞) G := by
    rw [contDiff_iff_contDiffAt]
    intro z
    rcases lt_or_ge (dist z c₀) (8 * ρ) with hz | hz
    · exact hχsmooth.contDiffAt.mul
        (((hganal z (mem_ball.mpr hz)).contDiffAt).restrict_scalars ℝ)
    · have hzero : G =ᶠ[𝓝 z] fun _ => 0 := by
        have hopen : IsOpen {w : ℂ | 7 * ρ < dist w c₀} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        filter_upwards [hopen.mem_nhds (show 7 * ρ < dist z c₀ by linarith)] with w hw
        have h0 : χ w = 0 := χ.zero_of_le_dist (le_of_lt hw)
        show ((χ w : ℝ) : ℂ) * g w = 0
        rw [h0]
        simp
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  have hGsupp : HasCompactSupport G := by
    refine HasCompactSupport.intro (isCompact_closedBall c₀ (7 * ρ)) fun z hz => ?_
    have hdist : 7 * ρ < dist z c₀ := lt_of_not_ge fun h => hz (mem_closedBall.mpr h)
    have h0 : χ z = 0 := χ.zero_of_le_dist hdist.le
    show ((χ z : ℝ) : ℂ) * g z = 0
    rw [h0]
    simp
  -- `∂̄G` vanishes on `ball c₀ (6ρ)` (there `G = g`, holomorphic)
  have hdbarG_inner : ∀ z ∈ ball c₀ (6 * ρ), dbar G z = 0 := by
    intro z hz
    rw [dbar_congr (hGg z hz)]
    exact dbar_eq_zero_of_differentiableAt
      ((hg z (ball_subset_ball (by linarith) hz)).differentiableAt)
  -- STEP 1: `U·h = U·∂G` pointwise
  have hstep1 : ∀ z, S.U z * h z = S.U z * del G z := by
    intro z
    rcases eq_or_ne (S.U z) 0 with h0 | h0
    · rw [h0, zero_mul, zero_mul]
    · obtain ⟨_, h5⟩ := S.dist_mem_of_U_ne_zero h0
      have hz6 : z ∈ ball c₀ (6 * ρ) := mem_ball.mpr (by linarith)
      have hz8 : z ∈ ball c₀ (8 * ρ) := mem_ball.mpr (by linarith)
      have : del G z = h z := by
        rw [del_congr (hGg z hz6), del_eq_deriv_of_differentiableAt (hg z hz8).differentiableAt,
          (hg z hz8).deriv]
      rw [this]
  -- STEP 2: the cross-term Stokes identity transfers `∫U·∂G` to `∫(∂W/W)·∂̄G`
  have hPint : Integrable (fun z => del S.W z / S.W z * dbar G z) volume := by
    have hcont : Continuous fun z => del S.W z / S.W z * dbar G z := by
      have hP : Continuous fun z => del S.W z / S.W z := by
        have hinv : ContDiff ℝ (⊤ : ℕ∞) (fun z => (S.W z)⁻¹) :=
          contDiff_iff_contDiffAt.mpr fun z =>
            (contDiffAt_inv ℝ (S.ne_zero z)).comp z S.smooth.contDiffAt
        have h := ((contDiff_del S.smooth).mul hinv).continuous
        simpa only [div_eq_mul_inv] using h
      exact hP.mul (contDiff_dbar hGsmooth).continuous
    exact hcont.integrable_of_hasCompactSupport
      ((hasCompactSupport_dbar hGsupp).mul_left)
  have hUint : Integrable (fun z => S.U z * del G z) volume := by
    have hcont : Continuous fun z => S.U z * del G z :=
      S.U_continuous.mul (contDiff_del hGsmooth).continuous
    exact hcont.integrable_of_hasCompactSupport (S.U_hasCompactSupport.mul_right)
  have hstep2 : ∫ z, S.U z * del G z = ∫ z, del S.W z / S.W z * dbar G z := by
    have hzero := integral_logDeriv_cross_eq_zero S.smooth S.ne_zero hGsmooth hGsupp
    have hsub : (∫ z, del S.W z / S.W z * dbar G z) - ∫ z, S.U z * del G z = 0 := by
      rw [← integral_sub hPint hUint]
      exact hzero
    exact (sub_eq_zero.mp hsub).symm
  -- STEP 3: on `supp ∂̄G`, `∂W/W` is the two-pole expression
  have hstep3 : ∀ z, del S.W z / S.W z * dbar G z
      = dbar G z * ((z - α)⁻¹ - (z - β)⁻¹) := by
    intro z
    rcases eq_or_ne (dbar G z) 0 with h0 | h0
    · rw [h0, mul_zero, zero_mul]
    · -- `z` is outside `ball c₀ (6ρ)`, where `W = (z−α)/(z−β)` holomorphically
      have hz6 : 6 * ρ ≤ dist z c₀ := by
        by_contra h
        exact h0 (hdbarG_inner z (mem_ball.mpr (lt_of_not_ge h)))
      have hz5 : 5 * ρ < dist z c₀ := by linarith
      have hzα : z - α ≠ 0 := by
        refine sub_ne_zero.mpr fun h => ?_
        rw [h] at hz5
        linarith [S.dist_alpha]
      have hzβ : z - β ≠ 0 := by
        refine sub_ne_zero.mpr fun h => ?_
        rw [h] at hz5
        linarith [S.dist_beta]
      have hopen : IsOpen {w : ℂ | 5 * ρ < dist w c₀} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hcongr : S.W =ᶠ[𝓝 z] fun w => (w - α) / (w - β) := by
        filter_upwards [hopen.mem_nhds hz5] with w hw
        exact S.outer w hw
      have h1 : HasDerivAt (fun w : ℂ => w - α) 1 z := (hasDerivAt_id z).sub_const α
      have h2 : HasDerivAt (fun w : ℂ => w - β) 1 z := (hasDerivAt_id z).sub_const β
      have hr : HasDerivAt (fun w : ℂ => (w - α) / (w - β))
          ((1 * (z - β) - (z - α) * 1) / (z - β) ^ 2) z := h1.div h2 hzβ
      have hdel : del S.W z = (1 * (z - β) - (z - α) * 1) / (z - β) ^ 2 := by
        rw [del_congr hcongr, del_eq_deriv_of_differentiableAt hr.differentiableAt, hr.deriv]
      have hWz : S.W z = (z - α) / (z - β) := S.outer z hz5
      rw [hdel, hWz]
      field_simp
  -- STEP 4: the two-pole Cauchy–Pompeiu pairing
  have hstep4 : ∫ z, dbar G z * ((z - α)⁻¹ - (z - β)⁻¹) = (π : ℂ) * (G β - G α) :=
    integral_dbar_mul_inv_sub hGsmooth hGsupp α β
  -- STEP 5: the bump is `1` at the endpoints
  have hGα : G α = g α :=
    (hGg α (mem_ball.mpr (by linarith [S.dist_alpha]))).eq_of_nhds
  have hGβ : G β = g β :=
    (hGg β (mem_ball.mpr (by linarith [S.dist_beta]))).eq_of_nhds
  calc ∫ z, S.U z * h z
      = ∫ z, S.U z * del G z := integral_congr_ae (Eventually.of_forall hstep1)
    _ = ∫ z, del S.W z / S.W z * dbar G z := hstep2
    _ = ∫ z, dbar G z * ((z - α)⁻¹ - (z - β)⁻¹) :=
        integral_congr_ae (Eventually.of_forall hstep3)
    _ = (π : ℂ) * (G β - G α) := hstep4
    _ = (π : ℂ) * (g β - g α) := by rw [hGα, hGβ]

end PlanarPieceSolution

/-! ### Existence (the Forster 20.5(a) construction)

`W := exp((ψ−1)·log((z−β)/(z−α)))` with a bump `ψ` (`= 1` on `closedBall c₀ (4ρ)`,
supported in `ball c₀ (5ρ)`): inside it is `exp 0 = 1`; outside the bump it is
`exp(−log((z−β)/(z−α))) = (z−α)/(z−β)`.  The principal branch is available because
`(z−β)/(z−α) ∈ ball 1 1 ⊂ slitPlane` as soon as `dist z c₀ > 3ρ`. -/

/-- The branch quotient stays in `ball 1 1` outside `closedBall c₀ (3ρ)`. -/
private theorem quot_near_one {c₀ α β : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hα : dist α c₀ < ρ) (hβ : dist β c₀ < ρ) {z : ℂ} (hz : 3 * ρ < dist z c₀) :
    ‖(z - β) / (z - α) - 1‖ < 1 := by
  have hzα_norm : 2 * ρ < ‖z - α‖ := by
    have h1 : dist z c₀ ≤ dist z α + dist α c₀ := dist_triangle z α c₀
    have h2 : dist z α = ‖z - α‖ := by rw [dist_eq_norm]
    linarith
  have hzα : z - α ≠ 0 := by
    intro h
    rw [h, norm_zero] at hzα_norm
    linarith
  have hαβ : ‖α - β‖ < 2 * ρ := by
    have h1 : dist α β ≤ dist α c₀ + dist c₀ β := dist_triangle α c₀ β
    have h2 : dist α β = ‖α - β‖ := by rw [dist_eq_norm]
    have h3 : dist c₀ β = dist β c₀ := dist_comm c₀ β
    linarith
  have hq : (z - β) / (z - α) - 1 = (α - β) / (z - α) := by
    field_simp
    ring
  rw [hq, norm_div]
  rw [div_lt_one (by linarith)]
  linarith

/-- **Planar piece solutions exist** for any endpoints `α, β ∈ ball c₀ ρ` (Forster 20.5(a):
bump times the principal branch of `log((z−β)/(z−α))`). -/
theorem nonempty_planarPieceSolution {c₀ α β : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hα : dist α c₀ < ρ) (hβ : dist β c₀ < ρ) :
    Nonempty (PlanarPieceSolution c₀ ρ α β) := by
  -- the branch data outside `closedBall c₀ (3ρ)`
  set Lq : ℂ → ℂ := fun z => (z - β) / (z - α) with hLqdef
  have hslit : ∀ z, 3 * ρ < dist z c₀ → Lq z ∈ Complex.slitPlane := by
    intro z hz
    have hnear := quot_near_one hρ hα hβ hz
    refine Complex.mem_slitPlane_iff.mpr (Or.inl ?_)
    have h1 : |(Lq z - 1).re| ≤ ‖Lq z - 1‖ := Complex.abs_re_le_norm _
    have h2 : (Lq z).re = 1 + (Lq z - 1).re := by simp
    have := abs_le.mp h1
    rw [h2]
    linarith
  have hLq_ne : ∀ z, 3 * ρ < dist z c₀ → Lq z ≠ 0 := by
    intro z hz h0
    have hnear := quot_near_one hρ hα hβ hz
    rw [hLqdef] at h0
    simp only [h0] at hnear
    rw [show (0 : ℂ) - 1 = -1 by ring, norm_neg, norm_one] at hnear
    exact lt_irrefl 1 hnear
  have hzα_ne : ∀ z : ℂ, 3 * ρ < dist z c₀ → z - α ≠ 0 := by
    intro z hz h
    rw [sub_eq_zero.mp h] at hz
    linarith [hα]
  have hL_anal : ∀ z, 3 * ρ < dist z c₀ →
      AnalyticAt ℂ (fun w => Complex.log (Lq w)) z := by
    intro z hz
    have hq : AnalyticAt ℂ Lq z :=
      ((analyticAt_id.sub analyticAt_const).div (analyticAt_id.sub analyticAt_const)
        (hzα_ne z hz))
    exact hq.clog (hslit z hz)
  -- the bump and the glued exponent
  set ψ : ContDiffBump c₀ := ⟨4 * ρ, 5 * ρ, by linarith, by linarith⟩ with hψdef
  set V : ℂ → ℂ := fun z =>
    if dist z c₀ ≤ 7 / 2 * ρ then 0 else ((ψ z : ℝ) - 1) * Complex.log (Lq z) with hVdef
  -- `V ≡ 0` on the inner ball
  have hV0 : ∀ z, dist z c₀ < 4 * ρ → V z = 0 := by
    intro z hz
    show (if dist z c₀ ≤ 7 / 2 * ρ then 0
      else (((ψ z : ℝ) : ℂ) - 1) * Complex.log (Lq z)) = 0
    rcases le_or_gt (dist z c₀) (7 / 2 * ρ) with h | h
    · rw [if_pos h]
    · rw [if_neg (not_le.mpr h)]
      have h1 : ψ z = 1 := ψ.one_of_mem_closedBall (mem_closedBall.mpr hz.le)
      rw [h1]
      simp
  -- `V = −log Lq` outside the bump
  have hVout : ∀ z, 5 * ρ < dist z c₀ → V z = -Complex.log (Lq z) := by
    intro z hz
    show (if dist z c₀ ≤ 7 / 2 * ρ then 0
      else (((ψ z : ℝ) : ℂ) - 1) * Complex.log (Lq z)) = -Complex.log (Lq z)
    rw [if_neg (not_le.mpr (by linarith))]
    have h0 : ψ z = 0 := ψ.zero_of_le_dist hz.le
    rw [h0]
    push_cast
    ring
  -- smoothness by the two-chart gluing
  have hVsmooth : ContDiff ℝ (⊤ : ℕ∞) V := by
    rw [contDiff_iff_contDiffAt]
    intro z
    rcases lt_or_ge (dist z c₀) (4 * ρ) with hz | hz
    · have hzero : V =ᶠ[𝓝 z] fun _ => (0 : ℂ) := by
        filter_upwards [isOpen_ball.mem_nhds (show z ∈ ball c₀ (4 * ρ) from hz)] with w hw
        exact hV0 w hw
      exact contDiffAt_const.congr_of_eventuallyEq hzero
    · -- on the open region `dist > 7/2·ρ`, `V` is the smooth product
      have hz72 : 7 / 2 * ρ < dist z c₀ := by linarith
      have hopen : IsOpen {w : ℂ | 7 / 2 * ρ < dist w c₀} :=
        isOpen_lt continuous_const (continuous_id.dist continuous_const)
      have hcongr : V =ᶠ[𝓝 z]
          fun w => (((ψ w : ℝ) : ℂ) - 1) * Complex.log (Lq w) := by
        filter_upwards [hopen.mem_nhds hz72] with w hw
        show (if dist w c₀ ≤ 7 / 2 * ρ then 0
          else (((ψ w : ℝ) : ℂ) - 1) * Complex.log (Lq w))
            = (((ψ w : ℝ) : ℂ) - 1) * Complex.log (Lq w)
        rw [if_neg (not_le.mpr hw)]
      refine ContDiffAt.congr_of_eventuallyEq ?_ hcongr
      have hψC : ContDiffAt ℝ (⊤ : ℕ∞) (fun w : ℂ => (((ψ w : ℝ) : ℂ) - 1)) z :=
        ((Complex.ofRealCLM.contDiff.comp ψ.contDiff).contDiffAt).sub contDiffAt_const
      have hLC : ContDiffAt ℝ (⊤ : ℕ∞) (fun w => Complex.log (Lq w)) z :=
        ((hL_anal z (by linarith)).contDiffAt).restrict_scalars ℝ
      exact hψC.mul hLC
  -- assemble
  refine ⟨⟨fun z => Complex.exp (V z), hρ, hα, hβ, ?_, fun z => Complex.exp_ne_zero _,
    ?_, ?_⟩⟩
  · exact (Complex.contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ |>.comp hVsmooth
  · intro z hz
    show Complex.exp (V z) = 1
    rw [hV0 z hz, Complex.exp_zero]
  · intro z hz
    show Complex.exp (V z) = (z - α) / (z - β)
    rw [hVout z hz, Complex.exp_neg, Complex.exp_log (hLq_ne z (by linarith))]
    show (Lq z)⁻¹ = (z - α) / (z - β)
    rw [hLqdef]
    exact inv_div _ _

end Jacobians.AbelPlanar
