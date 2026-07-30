/-
  Planar compact-support Stokes (the Forster (10.20) engine; Route-H atom 1).

  Two layers:

  1. **Green's theorem on an axis-aligned rectangle** (`green_rectangle`): for `C¹` scalar fields
     `P, Q : ℝ × ℝ → ℝ`, the four-edge counter-clockwise boundary sum equals the iterated integral
     of the curl, `∮_{∂R}(P dx + Q dy) = ∫∫_R (∂Q/∂x − ∂P/∂y)`.  FTC slices + continuous Fubini.

     PORTED (with adaptations to this repo's Mathlib pin) from the MIT-licensed
     tangentstorm/JacobianChallenge, file `Jacobian/Blueprint/Sec03/StokesOnRSWithBoundary.lean`
     (sub-leaf #5 `stokes_local_euclidean` + helpers), Copyright (c) 2026 Michal J Wallace,
     https://github.com/tangentstorm/JacobianChallenge — inspection-verified sorry-free at port
     time.  This rectangle engine is the seed for the Forster (10.21) annulus/residue identity.

  2. **Compact-support vanishing on ℂ** (Forster (10.20) itself, `∬_X dσ = 0` in the plane):
     for `φ : ℂ → ℂ` that is `ContDiff ℝ 1` with `HasCompactSupport φ`,
       * `integral_fderiv_apply_eq_zero` — `∫_ℂ (∂_v φ) = 0` for EVERY direction `v`
         (in particular the two partials `v = 1`, `v = I`);
       * `integral_dbar_eq_zero` — `∫_ℂ ∂̄φ = 0` (`DbarDisk.dbar`, the repo's Wirtinger operator);
       * `integral_del_eq_zero` — `∫_ℂ ∂φ = 0` (Wirtinger `∂ = ½(∂ₓ − i∂_y)`, stated inline).
     Proof: Mathlib's Haar-measure integration by parts
     (`integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable`) against the constant function `1`.
     Integration conventions match the repo's `Dbar*` files: plain `volume` on `ℂ`.

  Everything here is complete and depends on no unproved lemma.
-/
import Mathlib
import Submission.DbarDisk

open MeasureTheory Complex

namespace Jacobians.Dolbeault

/-! ### Layer 1 — Green's theorem on an axis-aligned rectangle
(ported from tangentstorm/JacobianChallenge, MIT, see file header) -/

/-- **FTC slice for `P`** (the `dy`-direction): the top-minus-bottom edge difference is the
iterated `y`-integral of `∂P/∂y` over the rectangle. -/
theorem green_rectangle_slice_P (P : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (hP : ContDiff ℝ 1 P) :
    (∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))
      = ∫ x in a..b, ∫ y in c..d, fderiv ℝ P (x, y) (0, 1) := by
  have hslice : ∀ x : ℝ,
      (∫ y in c..d, fderiv ℝ P (x, y) (0, 1)) = P (x, d) - P (x, c) := by
    intro x
    have hderiv : ∀ y ∈ Set.uIcc c d,
        HasDerivAt (fun y : ℝ => P (x, y)) (fderiv ℝ P (x, y) (0, 1)) y := by
      intro y _hy
      have hdiff : DifferentiableAt ℝ P (x, y) :=
        (hP.differentiable one_ne_zero).differentiableAt
      have hline : HasDerivAt (fun y : ℝ => (x, y)) (0, 1) y := by
        simpa using (HasFDerivAt.hasDerivAt (hasFDerivAt_prodMk_right (𝕜 := ℝ) x y))
      have h := hdiff.hasFDerivAt.comp_hasDerivAt y hline
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
    have hint : IntervalIntegrable (fun y : ℝ => fderiv ℝ P (x, y) (0, 1))
        MeasureTheory.volume c d := by
      have hc : Continuous fun y : ℝ => fderiv ℝ P (x, y) (0, 1) :=
        (hP.continuous_fderiv_apply one_ne_zero).comp
          ((continuous_const.prodMk continuous_id).prodMk continuous_const)
      exact hc.intervalIntegrable _ _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_sub]
  · simp_rw [← hslice]
  · exact (hP.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _
  · exact (hP.continuous.comp (continuous_id.prodMk continuous_const)).intervalIntegrable _ _

/-- **FTC slice for `Q`** (the `dx`-direction): the right-minus-left edge difference is the
iterated `x`-integral of `∂Q/∂x` over the rectangle. -/
theorem green_rectangle_slice_Q (Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (hQ : ContDiff ℝ 1 Q) :
    (∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))
      = ∫ y in c..d, ∫ x in a..b, fderiv ℝ Q (x, y) (1, 0) := by
  have hslice : ∀ y : ℝ,
      (∫ x in a..b, fderiv ℝ Q (x, y) (1, 0)) = Q (b, y) - Q (a, y) := by
    intro y
    have hderiv : ∀ x ∈ Set.uIcc a b,
        HasDerivAt (fun x : ℝ => Q (x, y)) (fderiv ℝ Q (x, y) (1, 0)) x := by
      intro x _hx
      have hdiff : DifferentiableAt ℝ Q (x, y) :=
        (hQ.differentiable one_ne_zero).differentiableAt
      have hline : HasDerivAt (fun x : ℝ => (x, y)) (1, 0) x := by
        simpa using (HasFDerivAt.hasDerivAt (hasFDerivAt_prodMk_left (𝕜 := ℝ) x y))
      have h := hdiff.hasFDerivAt.comp_hasDerivAt x hline
      exact h.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
    have hint : IntervalIntegrable (fun x : ℝ => fderiv ℝ Q (x, y) (1, 0))
        MeasureTheory.volume a b := by
      have hc : Continuous fun x : ℝ => fderiv ℝ Q (x, y) (1, 0) :=
        (hQ.continuous_fderiv_apply one_ne_zero).comp
          ((continuous_id.prodMk continuous_const).prodMk continuous_const)
      exact hc.intervalIntegrable _ _
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [← intervalIntegral.integral_sub]
  · simp_rw [← hslice]
  · exact (hQ.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _
  · exact (hQ.continuous.comp (continuous_const.prodMk continuous_id)).intervalIntegrable _ _

/-- The iterated `x`-then-`y` interval integral of a continuous field equals the set integral over
the product rectangle. -/
theorem rectangle_iterated_eq_setIntegral (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hf : Continuous f) :
    (∫ x in a..b, ∫ y in c..d, f (x, y))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
  erw [MeasureTheory.setIntegral_prod]
  · simp +decide [hab, hcd, MeasureTheory.integral_Icc_eq_integral_Ioc,
      intervalIntegral.integral_of_le]
  · exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hf.continuousOn

/-- **Continuous Fubini for the rectangle**: the iterated integrals in either order agree (this is
the form needed after one `fderiv`, where only continuity of the derivative term survives). -/
theorem rectangle_fubini_swap_continuous (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hf : Continuous f) :
    (∫ x in a..b, ∫ y in c..d, f (x, y))
      = ∫ y in c..d, ∫ x in a..b, f (x, y) := by
  rw [rectangle_iterated_eq_setIntegral f a b c d hab hcd hf]
  erw [MeasureTheory.setIntegral_prod]
  · rw [MeasureTheory.integral_integral_swap]
    · simp +decide only [MeasureTheory.integral_Icc_eq_integral_Ioc,
        intervalIntegral.integral_of_le hab, intervalIntegral.integral_of_le hcd]
    · rw [MeasureTheory.Measure.prod_restrict]
      exact ContinuousOn.integrableOn_compact
        (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hf.continuousOn
  · exact ContinuousOn.integrableOn_compact
      (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hf.continuousOn

/-- Reverse-order companion of `rectangle_iterated_eq_setIntegral`. -/
theorem rectangle_iterated_eq_setIntegral_rev (f : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d) (hf : Continuous f) :
    (∫ y in c..d, ∫ x in a..b, f (x, y))
      = ∫ p in Set.Icc a b ×ˢ Set.Icc c d, f p := by
  rw [← rectangle_fubini_swap_continuous f a b c d hab hcd hf]
  exact rectangle_iterated_eq_setIntegral f a b c d hab hcd hf

/-- **Green's theorem on the axis-aligned rectangle `[a,b] × [c,d] ⊂ ℝ²`** (Forster (10.20)'s
local engine): for `C¹` scalar fields `P, Q : ℝ × ℝ → ℝ`,

  `∮_{∂R} (P dx + Q dy) = ∫∫_R (∂Q/∂x − ∂P/∂y)`,

the boundary integral written as the four counter-clockwise edge integrals and the partials read
off `fderiv ℝ` at the basis directions `(1,0)`, `(0,1)`. -/
theorem green_rectangle (P Q : ℝ × ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hcd : c ≤ d)
    (hP : ContDiff ℝ 1 P) (hQ : ContDiff ℝ 1 Q) :
    (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y))
        - (∫ x in a..b, P (x, d)) - (∫ y in c..d, Q (a, y))
      = ∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) := by
  set q : ℝ × ℝ → ℝ := fun p => fderiv ℝ Q p (1, 0) with hq
  set pfun : ℝ × ℝ → ℝ := fun p => fderiv ℝ P p (0, 1) with hpfun
  have hqc : Continuous q :=
    (hQ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have hpc : Continuous pfun :=
    (hP.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have hQset : (∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))
      = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, q z := by
    rw [green_rectangle_slice_Q Q a b c d hQ]
    exact rectangle_iterated_eq_setIntegral_rev q a b c d hab hcd hqc
  have hPset : (∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))
      = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, pfun z := by
    rw [green_rectangle_slice_P P a b c d hP]
    exact rectangle_iterated_eq_setIntegral pfun a b c d hab hcd hpc
  have hRset : (∫ y in c..d, ∫ x in a..b,
        (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)))
      = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, (q z - pfun z) :=
    rectangle_iterated_eq_setIntegral_rev (fun z => q z - pfun z) a b c d hab hcd
      (hqc.sub hpc)
  calc
    (∫ x in a..b, P (x, c)) + (∫ y in c..d, Q (b, y))
        - (∫ x in a..b, P (x, d)) - (∫ y in c..d, Q (a, y))
        = ((∫ y in c..d, Q (b, y)) - (∫ y in c..d, Q (a, y))) -
          ((∫ x in a..b, P (x, d)) - (∫ x in a..b, P (x, c))) := by ring
    _ = (∫ z in Set.Icc a b ×ˢ Set.Icc c d, q z) -
          (∫ z in Set.Icc a b ×ˢ Set.Icc c d, pfun z) := by rw [hQset, hPset]
    _ = ∫ z in Set.Icc a b ×ˢ Set.Icc c d, (q z - pfun z) := by
      rw [← MeasureTheory.integral_sub]
      · exact ContinuousOn.integrableOn_compact
          (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hqc.continuousOn
      · exact ContinuousOn.integrableOn_compact
          (isCompact_Icc.prod CompactIccSpace.isCompact_Icc) hpc.continuousOn
    _ = ∫ y in c..d, ∫ x in a..b,
          (fderiv ℝ Q (x, y) (1, 0) - fderiv ℝ P (x, y) (0, 1)) := by rw [hRset]

/-! ### Layer 2 — compact-support vanishing on `ℂ` (Forster (10.20)) -/

/-- The directional derivative of a `C¹` compactly-supported `φ : ℂ → ℂ` is integrable. -/
theorem integrable_fderiv_apply_of_compactSupport (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) (v : ℂ) :
    Integrable (fun z : ℂ => fderiv ℝ φ z v) volume := by
  have hcont : Continuous fun z : ℂ => fderiv ℝ φ z v :=
    (hφ.continuous_fderiv_apply one_ne_zero).comp (continuous_id.prodMk continuous_const)
  have hsupp' : HasCompactSupport fun z : ℂ => fderiv ℝ φ z v :=
    (hsupp.fderiv (𝕜 := ℝ)).comp_left (g := fun L : ℂ →L[ℝ] ℂ => L v) (by simp)
  exact hcont.integrable_of_hasCompactSupport hsupp'

/-- **Forster (10.20) on the plane, directional form**: every directional derivative of a `C¹`
compactly-supported `φ : ℂ → ℂ` has vanishing area integral, `∫_ℂ ∂_v φ = 0` (in particular the
two partials `v = 1`, `v = I`).  Mathlib Haar integration by parts against the constant `1`. -/
theorem integral_fderiv_apply_eq_zero (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) (v : ℂ) :
    ∫ z : ℂ, fderiv ℝ φ z v = 0 := by
  have h1 : Integrable (fun x : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℂ)) x v * φ x) volume := by
    have heq : (fun x : ℂ => fderiv ℝ (fun _ : ℂ => (1 : ℂ)) x v * φ x) = fun _ => 0 := by
      ext x; simp
    rw [heq]; exact integrable_zero _ _ _
  have h2 : Integrable (fun x : ℂ => (1 : ℂ) * fderiv ℝ φ x v) volume := by
    simpa using integrable_fderiv_apply_of_compactSupport φ hφ hsupp v
  have h3 : Integrable (fun x : ℂ => (1 : ℂ) * φ x) volume := by
    simpa using hφ.continuous.integrable_of_hasCompactSupport hsupp
  have key := integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable
    (f := fun _ : ℂ => (1 : ℂ)) (g := φ) (v := v) h1 h2 h3
    (fun x _ => differentiableAt_const _)
    (fun x _ => (hφ.differentiable one_ne_zero).differentiableAt)
  simpa using key

/-- **`∫_ℂ ∂̄φ = 0`** for `C¹` compactly-supported `φ` (`DbarDisk.dbar` = the repo's Wirtinger
`∂̄ = ½(∂ₓ + i∂_y)`).  The well-definedness engine for the residue functional (Forster 17.1). -/
theorem integral_dbar_eq_zero (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) :
    ∫ z : ℂ, DbarDisk.dbar φ z = 0 := by
  have h1 := integrable_fderiv_apply_of_compactSupport φ hφ hsupp 1
  have hI := integrable_fderiv_apply_of_compactSupport φ hφ hsupp Complex.I
  -- (the `e·` steps are term-mode: `rw`/`simp` trip on the `MeasurableSpace ℂ` instance forms)
  have e1 : ∫ z : ℂ, DbarDisk.dbar φ z
      = (2 : ℂ)⁻¹ * ∫ z : ℂ, (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I) :=
    MeasureTheory.integral_const_mul _ _
  have e2 : ∫ z : ℂ, (fderiv ℝ φ z 1 + Complex.I * fderiv ℝ φ z Complex.I)
      = (∫ z : ℂ, fderiv ℝ φ z 1) + ∫ z : ℂ, Complex.I * fderiv ℝ φ z Complex.I :=
    MeasureTheory.integral_add h1 (hI.const_mul Complex.I)
  have e3 : ∫ z : ℂ, Complex.I * fderiv ℝ φ z Complex.I
      = Complex.I * ∫ z : ℂ, fderiv ℝ φ z Complex.I :=
    MeasureTheory.integral_const_mul _ _
  rw [e1, e2, e3, integral_fderiv_apply_eq_zero φ hφ hsupp 1,
    integral_fderiv_apply_eq_zero φ hφ hsupp Complex.I]
  ring

/-- **`∫_ℂ ∂φ = 0`** for `C¹` compactly-supported `φ` (Wirtinger `∂ = ½(∂ₓ − i∂_y)`, stated
inline — the repo has no named `∂`). -/
theorem integral_del_eq_zero (φ : ℂ → ℂ) (hφ : ContDiff ℝ 1 φ)
    (hsupp : HasCompactSupport φ) :
    ∫ z : ℂ, (2 : ℂ)⁻¹ * (fderiv ℝ φ z 1 - Complex.I * fderiv ℝ φ z Complex.I) = 0 := by
  have h1 := integrable_fderiv_apply_of_compactSupport φ hφ hsupp 1
  have hI := integrable_fderiv_apply_of_compactSupport φ hφ hsupp Complex.I
  have e1 : ∫ z : ℂ, (2 : ℂ)⁻¹ * (fderiv ℝ φ z 1 - Complex.I * fderiv ℝ φ z Complex.I)
      = (2 : ℂ)⁻¹ * ∫ z : ℂ, (fderiv ℝ φ z 1 - Complex.I * fderiv ℝ φ z Complex.I) :=
    MeasureTheory.integral_const_mul _ _
  have e2 : ∫ z : ℂ, (fderiv ℝ φ z 1 - Complex.I * fderiv ℝ φ z Complex.I)
      = (∫ z : ℂ, fderiv ℝ φ z 1) - ∫ z : ℂ, Complex.I * fderiv ℝ φ z Complex.I :=
    MeasureTheory.integral_sub h1 (hI.const_mul Complex.I)
  have e3 : ∫ z : ℂ, Complex.I * fderiv ℝ φ z Complex.I
      = Complex.I * ∫ z : ℂ, fderiv ℝ φ z Complex.I :=
    MeasureTheory.integral_const_mul _ _
  rw [e1, e2, e3, integral_fderiv_apply_eq_zero φ hφ hsupp 1,
    integral_fderiv_apply_eq_zero φ hφ hsupp Complex.I]
  ring

end Jacobians.Dolbeault
