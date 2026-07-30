/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-3 (logDbar layer): the global `(0,1)`-datum `σ_f = d″f/f` (Forster 20.2)

For a weak solution `F` of a divisor `D`, the logarithmic `∂̄`-datum is, at each point `x`,
`(ψ_x x)⁻¹ • ∂̄ψ_x|_x` with `ψ_x = F.unit x` the centred local unit — smooth ACROSS the
divisor because locally `d″f/f = d″ψ/ψ` (the holomorphic factor `z^k` is killed by `∂̄`).

* `WeakSolution.logDbarFiber` / `WeakSolution.logDbar` — the fiber and the bundled smooth
  `(0,1)`-form (`logDbar_mem_zeroOne`);
* `logDbarFiber_eventuallyEq` — the locality: near `a` the fiber is computed from the single
  unit `ψ_a` (the soundness-critical Forster 20.2 smoothness mechanism);
* the algebra `logDbarFiber_mul` / `_one` / `_inv` / `_recast` / `_zpow` (mirroring the
  weak-solution algebra of `AbelWeakSolutions`);
* `logDbarFiber_eq_zero_of_eventually_one` — vanishing where `f ≡ 1`;
* `read01_logDbar_of_coeff_zero` — the chart read off the divisor: `∂̄(f∘chart⁻¹)/f`.

Also provides `exists_smoothCFunction_eventuallyEq`, the bump-glued global extension of a
locally-smooth function (the device that turns local units into global `SmoothCFunctions`
for the section-smoothness argument).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.1–20.2 (pp. 159–160);
plan `docs/walls_bc_plan_2026-06-10.md`, phase C-3.
-/
import Submission.AbelFormRead
import Submission.AbelWeakSolutions

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Filter Complex Jacobians.Dolbeault

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The global smooth extension of a locally-smooth function -/

/-- **Bump-glued global extension**: a function smooth on an open neighbourhood of `a`
agrees near `a` with a global `SmoothCFunctions`. (Planar bump in the chart at `a` ×
the chart read, lifted by `exists_smoothLift_of_chartFun`.) -/
theorem exists_smoothCFunction_eventuallyEq {w : X → ℂ} {V : Set X} (hV : IsOpen V)
    {a : X} (ha : a ∈ V)
    (hw : ∀ x ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) w x) :
    ∃ u : SmoothCFunctions X, ⇑u =ᶠ[𝓝 a] w := by
  classical
  set e := chartAt (H := ℂ) a with he
  -- shrink to the chart source and pass to the open chart image.
  set V' : Set X := V ∩ e.source with hV'
  have hV'open : IsOpen V' := hV.inter e.open_source
  have haV' : a ∈ V' := ⟨ha, mem_chart_source ℂ a⟩
  have himg_open : IsOpen (e '' V') := e.isOpen_image_of_subset_source hV'open inter_subset_right
  have haimg : e a ∈ e '' V' := mem_image_of_mem _ haV'
  obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp himg_open _ haimg
  -- the planar cutoff read.
  set χ : ContDiffBump (e a) := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩ with hχ
  set f : ℂ → ℂ := fun z => ((χ z : ℝ) : ℂ) * w (e.symm z) with hf
  have hf_smooth : ContDiff ℝ (⊤ : ℕ∞) f := by
    rw [contDiff_iff_contDiffAt]
    intro z
    rcases lt_or_ge (dist z (e a)) r with hz | hz
    · -- inside the ball: both factors smooth.
      have hzimg : z ∈ e '' V' := hr_sub (Metric.mem_ball.mpr hz)
      obtain ⟨x, hxV', rfl⟩ := hzimg
      have hxsrc : x ∈ e.source := hxV'.2
      have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) e.symm (e x) :=
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := a) _
          (e.map_source hxsrc)).contMDiffAt
          (e.open_target.mem_nhds (e.map_source hxsrc))
      have hwx : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) w (e.symm (e x)) := by
        rw [e.left_inv hxsrc]
        exact hw x hxV'.1
      have hcomp : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun z => w (e.symm z)) (e x) :=
        hwx.comp _ hsymm
      have hχs : ContDiffAt ℝ (⊤ : ℕ∞) (fun z : ℂ => ((χ z : ℝ) : ℂ)) (e x) :=
        (Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt
      exact hχs.mul (contMDiffAt_iff_contDiffAt.mp hcomp)
    · -- outside: `χ = 0` locally.
      have hzero : f =ᶠ[𝓝 z] fun _ => 0 := by
        have hopen : IsOpen {v : ℂ | 3 * r / 4 < dist v (e a)} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        filter_upwards [hopen.mem_nhds (show 3 * r / 4 < dist z (e a) by linarith)] with v hv
        have h0 : χ v = 0 := χ.zero_of_le_dist hv.le
        show ((χ v : ℝ) : ℂ) * w (e.symm v) = 0
        rw [h0]; simp
      exact contDiffAt_const.congr_of_eventuallyEq hzero
  -- lift to a global smooth function.
  obtain ⟨V₀, u, hV₀open, haV₀, hu⟩ := exists_smoothLift_of_chartFun f hf_smooth a
  refine ⟨u, ?_⟩
  have hpre : IsOpen (e.source ∩ e ⁻¹' Metric.ball (e a) (r / 2)) :=
    e.isOpen_inter_preimage Metric.isOpen_ball
  have hapre : a ∈ e.source ∩ e ⁻¹' Metric.ball (e a) (r / 2) :=
    ⟨mem_chart_source ℂ a, by simp [Metric.mem_ball, hr_pos]⟩
  filter_upwards [hV₀open.mem_nhds haV₀, hpre.mem_nhds hapre] with x hxV₀ hxpre
  have hue : (u x : ℂ) = f (extChartAt 𝓘(ℝ, ℂ) a x) := hu x hxV₀
  have hext : (extChartAt 𝓘(ℝ, ℂ) a) x = e x := by
    rw [Dolbeault.AbelPairing.extChartAt_real_eq_chartAt]
  rw [hue, hext]
  show ((χ (e x) : ℝ) : ℂ) * w (e.symm (e x)) = w x
  have hχ1 : χ (e x) = 1 := χ.one_of_mem_closedBall
    (Metric.ball_subset_closedBall hxpre.2)
  rw [hχ1, e.left_inv hxpre.1]
  simp

/-! ### The logarithmic `∂̄`-fiber of a weak solution -/

namespace WeakSolution

variable {D D₁ D₂ : Divisor X}

/-- **The logarithmic `∂̄`-fiber** of a weak solution at `x`: `(ψ_x x)⁻¹ • ∂̄ψ_x|_x` with
`ψ_x = F.unit x` the centred local unit (Forster 20.2: `d″f/f = d″ψ/ψ`). -/
def logDbarFiber (F : WeakSolution D) (x : X) : ℂ →L[ℝ] ℂ :=
  (F.unit x x)⁻¹ • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit x) x)

/-- **Locality of the logarithmic fiber** (the Forster 20.2 mechanism): on `nbhd a` the
fiber is computed from the single unit `ψ_a` — the holomorphic normal-form factor `z_a^k`
is killed by `∂̄`. -/
theorem logDbarFiber_eventuallyEq (F : WeakSolution D) (a : X) :
    ∀ x ∈ F.nbhd a, F.logDbarFiber x
      = (F.unit a x)⁻¹ • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit a) x) := by
  intro x hx
  rcases eq_or_ne x a with rfl | hne
  · rfl
  -- off the centre: `D x = 0` and `ψ_x ≈ ψ_a · z_a^{D a}` as germs at `x`.
  have hDx : D x = 0 := F.coeff_eq_zero_of_mem_nbhd hx hne
  have hgerm : F.unit x =ᶠ[𝓝 x]
      fun y => F.unit a y * chartCoord a y ^ (D a) := by
    have h1 : F.toFun =ᶠ[𝓝 x] F.unit x := F.toFun_eventuallyEq_unit hDx
    have h2 : F.toFun =ᶠ[𝓝 x] fun y => F.unit a y * chartCoord a y ^ (D a) := by
      filter_upwards [(F.isOpen_nbhd a).mem_nhds hx] with y hy
      exact F.normalForm a y hy
    exact h1.symm.trans h2
  have hxsrc : x ∈ (chartAt (H := ℂ) a).source := F.nbhd_subset a hx
  have hz : chartCoord a x ≠ 0 := chartCoord_ne_zero hxsrc hne
  -- the product rule at `x`.
  have hu : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit a) x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit a) x) :=
    ((F.unit_contMDiffAt a hx).mdifferentiableAt (by simp)).hasMFDerivAt
  have hzk_cm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun y => chartCoord a y ^ (D a)) x :=
    chartCoord_zpow_contMDiffAt (D a) hxsrc (Or.inl hne)
  have hzk : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y => chartCoord a y ^ (D a)) x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y => chartCoord a y ^ (D a)) x) :=
    (hzk_cm.mdifferentiableAt (by simp)).hasMFDerivAt
  have hmul := (hu.mul hzk).mfderiv
  -- assemble.
  have hux : F.unit x x = F.unit a x * chartCoord a x ^ (D a) := hgerm.eq_of_nhds
  rw [logDbarFiber, hgerm.mfderiv_eq,
    show (fun y => F.unit a y * chartCoord a y ^ (D a))
      = (F.unit a * fun y => chartCoord a y ^ (D a)) from rfl, hmul, map_add,
    proj01_smul, proj01_smul, proj01_mfderiv_chartCoord_zpow_eq_zero (D a) hxsrc (Or.inl hne),
    hux]
  have hune : F.unit a x ≠ 0 := F.unit_ne_zero a x hx
  have hcoeff : (F.unit a x * chartCoord a x ^ (D a))⁻¹ * (chartCoord a x ^ (D a))
      = (F.unit a x)⁻¹ := by
    field_simp
  calc ((F.unit a x * chartCoord a x ^ (D a))⁻¹ : ℂ) •
        (F.unit a x • (0 : ℂ →L[ℝ] ℂ) + (chartCoord a x ^ (D a)) •
          proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit a) x))
      = ((F.unit a x * chartCoord a x ^ (D a))⁻¹ * (chartCoord a x ^ (D a))) •
          proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit a) x) := by
        module
    _ = (F.unit a x)⁻¹ • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit a) x) := by rw [hcoeff]

/-- The logarithmic fiber is `(0,1)` (fixed by `proj01`). -/
theorem proj01_logDbarFiber (F : WeakSolution D) (x : X) :
    proj01 (F.logDbarFiber x) = F.logDbarFiber x := by
  rw [logDbarFiber, proj01_smul, proj01_idempotent]

/-- **Smoothness of the logarithmic fiber section**: near each `a`, replace `ψ_a` by a
bump-glued global smooth function and use the smoothness of `(u⁻¹) • ∂̄u`. -/
theorem contMDiff_logDbarFiber (F : WeakSolution D) :
    ContMDiff (𝓘(ℝ, ℂ)) (𝓘(ℝ, ℂ).prod 𝓘(ℝ, ℂ →L[ℝ] ℂ)) (⊤ : ℕ∞)
      (fun x => (⟨x, F.logDbarFiber x⟩ : Bundle.TotalSpace (ℂ →L[ℝ] ℂ)
        (fun x : X => TangentSpace (𝓘(ℝ, ℂ)) x →L[ℝ] (Bundle.Trivial X ℂ) x))) := by
  intro a
  -- the global smooth model of the unit at `a`.
  obtain ⟨u, hu⟩ := exists_smoothCFunction_eventuallyEq (F.isOpen_nbhd a) (F.mem_nbhd a)
    (fun x hx => F.unit_contMDiffAt a hx)
  have hua : (u a : ℂ) = F.unit a a := hu.eq_of_nhds
  have hu0 : (u a : ℂ) ≠ 0 := by rw [hua]; exact F.unit_ne_zero a a (F.mem_nbhd a)
  -- the smooth model section `x ↦ (u x)⁻¹ • (∂̄u) x`.
  have hinv : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun x => (u x : ℂ)⁻¹) a :=
    (WeakSolution.contMDiffAt_inv_complex hu0).comp a (u.contMDiff a)
  have hmodel := contMDiffAt_cSmul_section (X := X) (F := fun x => (u x : ℂ)⁻¹)
    (s := fun x => (dbarL u) x) hinv ((dbarL u).contMDiff_toFun a)
  refine hmodel.congr_of_eventuallyEq ?_
  -- the two sections agree near `a`.
  have hnbhd : ∀ᶠ x in 𝓝 a, x ∈ F.nbhd a := (F.isOpen_nbhd a).mem_nhds (F.mem_nbhd a)
  filter_upwards [hnbhd, hu.eventually_nhds] with x hx hux
  have hux' : (⇑u : X → ℂ) =ᶠ[𝓝 x] F.unit a := hux
  have h1 : F.logDbarFiber x
      = (F.unit a x)⁻¹ • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit a) x) :=
    F.logDbarFiber_eventuallyEq a x hx
  have h2 : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit a) x = mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x :=
    hux'.symm.mfderiv_eq
  have h3 : (dbarL u) x = proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⇑u) x) := rfl
  have hval : (fun x => (u x : ℂ)⁻¹) x • (dbarL u) x = F.logDbarFiber x := by
    show (u x : ℂ)⁻¹ • (dbarL u) x = F.logDbarFiber x
    rw [h1, h3, ← h2, hux'.eq_of_nhds]
  exact congrArg (Bundle.TotalSpace.mk x) hval.symm

/-- **The global `(0,1)`-datum `σ_f = d″f/f`** of a weak solution (Forster 20.2), as a
smooth `ℂ`-valued 1-form. -/
def logDbar (F : WeakSolution D) : SmoothCOneForms X where
  toFun := F.logDbarFiber
  contMDiff_toFun := F.contMDiff_logDbarFiber

@[simp] theorem logDbar_apply (F : WeakSolution D) (x : X) :
    F.logDbar x = F.logDbarFiber x := rfl

/-- `σ_f` is a `(0,1)`-form. -/
theorem logDbar_mem_zeroOne (F : WeakSolution D) : F.logDbar ∈ OneFormsZeroOne X := by
  refine ⟨F.logDbar, ?_⟩
  refine ContMDiffSection.ext fun x => ?_
  show proj01 (F.logDbar x) = F.logDbar x
  rw [logDbar_apply]
  exact F.proj01_logDbarFiber x

/-! ### The logDbar algebra (mirroring the weak-solution algebra) -/

/-- `σ_{f₁f₂} = σ_{f₁} + σ_{f₂}` (pointwise). -/
theorem logDbarFiber_mul (F₁ : WeakSolution D₁) (F₂ : WeakSolution D₂) (x : X) :
    (F₁.mul F₂).logDbarFiber x = F₁.logDbarFiber x + F₂.logDbarFiber x := by
  have h1 : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₁.unit x) x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₁.unit x) x) :=
    ((F₁.unit_contMDiffAt x (F₁.mem_nbhd x)).mdifferentiableAt (by simp)).hasMFDerivAt
  have h2 : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₂.unit x) x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₂.unit x) x) :=
    ((F₂.unit_contMDiffAt x (F₂.mem_nbhd x)).mdifferentiableAt (by simp)).hasMFDerivAt
  have hmul := (h1.mul h2).mfderiv
  have hunit : (F₁.mul F₂).unit x = fun y => F₁.unit x y * F₂.unit x y := rfl
  rw [logDbarFiber, hunit,
    show (fun y => F₁.unit x y * F₂.unit x y) = (F₁.unit x * F₂.unit x) from rfl,
    hmul, map_add, proj01_smul, proj01_smul]
  have hne₁ : F₁.unit x x ≠ 0 := F₁.unit_ne_zero x x (F₁.mem_nbhd x)
  have hne₂ : F₂.unit x x ≠ 0 := F₂.unit_ne_zero x x (F₂.mem_nbhd x)
  have ha : (F₁.unit x x * F₂.unit x x)⁻¹ * F₂.unit x x = (F₁.unit x x)⁻¹ := by
    field_simp
  have hb : (F₁.unit x x * F₂.unit x x)⁻¹ * F₁.unit x x = (F₂.unit x x)⁻¹ := by
    field_simp
  show ((F₁.unit x x * F₂.unit x x : ℂ))⁻¹ •
      (F₁.unit x x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₂.unit x) x)
        + F₂.unit x x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₁.unit x) x))
    = F₁.logDbarFiber x + F₂.logDbarFiber x
  simp only [logDbarFiber]
  calc ((F₁.unit x x * F₂.unit x x : ℂ))⁻¹ •
        (F₁.unit x x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₂.unit x) x)
          + F₂.unit x x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₁.unit x) x))
      = ((F₁.unit x x * F₂.unit x x)⁻¹ * F₂.unit x x) •
          proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₁.unit x) x)
        + ((F₁.unit x x * F₂.unit x x)⁻¹ * F₁.unit x x) •
          proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₂.unit x) x) := by
        module
    _ = (F₁.unit x x)⁻¹ • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₁.unit x) x)
        + (F₂.unit x x)⁻¹ • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F₂.unit x) x) := by
        rw [ha, hb]

/-- `σ_1 = 0`. -/
theorem logDbarFiber_one (x : X) : (one X).logDbarFiber x = 0 := by
  rw [logDbarFiber]
  have h : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) ((one X).unit x) x = 0 := by
    show mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun _ : X => (1 : ℂ)) x = 0
    exact mfderiv_const
  rw [h, map_zero]
  module

/-- `σ_{1/f} = −σ_f` (pointwise) — via the product rule on the germ `ψ·ψ⁻¹ = 1`. -/
theorem logDbarFiber_inv (F : WeakSolution D) (x : X) :
    F.inv.logDbarFiber x = -F.logDbarFiber x := by
  have hu : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (F.unit x) x :=
    F.unit_contMDiffAt x (F.mem_nbhd x)
  have hne : F.unit x x ≠ 0 := F.unit_ne_zero x x (F.mem_nbhd x)
  have hinv_cm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => (F.unit x y)⁻¹) x :=
    (contMDiffAt_inv_complex hne).comp x hu
  have h1 : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit x) x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit x) x) :=
    (hu.mdifferentiableAt (by simp)).hasMFDerivAt
  have h2 : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y => (F.unit x y)⁻¹) x
      (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y => (F.unit x y)⁻¹) x) :=
    (hinv_cm.mdifferentiableAt (by simp)).hasMFDerivAt
  have hmul := (h1.mul h2).mfderiv
  -- the product is the constant `1` near `x`.
  have hev : (F.unit x * fun y => (F.unit x y)⁻¹) =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
    filter_upwards [hu.continuousAt.eventually_ne hne] with y hy
    show F.unit x y * (F.unit x y)⁻¹ = 1
    exact mul_inv_cancel₀ hy
  have hzero : mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit x * fun y => (F.unit x y)⁻¹) x = 0 := by
    rw [hev.mfderiv_eq]
    exact mfderiv_const
  rw [hzero] at hmul
  -- read off: `ψ x • ∂̄(ψ⁻¹) = −(ψ x)⁻¹ • ∂̄ψ` after `proj01`.
  have hrel : F.unit x x • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y => (F.unit x y)⁻¹) x)
      + (F.unit x x)⁻¹ • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (F.unit x) x) = 0 := by
    have h := congrArg proj01 hmul.symm
    rw [map_add, proj01_smul, proj01_smul, map_zero] at h
    exact h
  have hunit : F.inv.unit x = fun y => (F.unit x y)⁻¹ := rfl
  rw [logDbarFiber, hunit]
  show ((F.unit x x)⁻¹)⁻¹ •
      proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y => (F.unit x y)⁻¹) x) = -F.logDbarFiber x
  rw [inv_inv, logDbarFiber]
  exact eq_neg_of_add_eq_zero_left hrel

/-- Recasting along a divisor equality does not change the fiber. -/
theorem logDbarFiber_recast (h : D₁ = D₂) (F : WeakSolution D₁) (x : X) :
    (F.recast h).logDbarFiber x = F.logDbarFiber x := by
  cases h; rfl

/-- `σ_{f^n} = n·σ_f` for natural powers (pointwise). -/
theorem logDbarFiber_pow (F : WeakSolution D) (n : ℕ) (x : X) :
    (F.pow n).logDbarFiber x = (n : ℤ) • F.logDbarFiber x := by
  induction n with
  | zero =>
    rw [pow, logDbarFiber_recast, logDbarFiber_one]
    simp
  | succ m ih =>
    rw [pow, logDbarFiber_recast, logDbarFiber_mul, ih]
    push_cast
    rw [add_zsmul, one_zsmul]

/-- `σ_{f^n} = n·σ_f` for integer powers (pointwise). -/
theorem logDbarFiber_zpow (F : WeakSolution D) (n : ℤ) (x : X) :
    (F.zpow n).logDbarFiber x = n • F.logDbarFiber x := by
  cases n with
  | ofNat m => exact F.logDbarFiber_pow m x
  | negSucc m =>
    rw [zpow, logDbarFiber_recast, logDbarFiber_inv, logDbarFiber_pow]
    rw [Int.negSucc_eq]
    push_cast
    rw [neg_smul]

/-! ### Vanishing and reads -/

/-- Where `f ≡ 1` locally, the logarithmic fiber vanishes. -/
theorem logDbarFiber_eq_zero_of_eventually_one (F : WeakSolution D) {x : X}
    (h : ∀ᶠ y in 𝓝 x, F.toFun y = 1) : F.logDbarFiber x = 0 := by
  have hDx : D x = 0 := by
    by_contra hD
    have h0 := F.toFun_eq_zero_of_coeff_ne_zero hD
    have h1 : F.toFun x = 1 := h.self_of_nhds
    rw [h0] at h1
    exact zero_ne_one h1
  have hgerm : F.unit x =ᶠ[𝓝 x] fun _ => (1 : ℂ) :=
    (F.toFun_eventuallyEq_unit hDx).symm.trans h
  rw [logDbarFiber, hgerm.mfderiv_eq, mfderiv_const, map_zero]
  module

/-- **The chart read of `σ_f` off the divisor**: `read01 σ_f y x = ∂̄(f∘chart_y⁻¹)/f` at
points `x ∈ source_y` with `D x = 0`. -/
theorem read01_logDbar_of_coeff_zero (F : WeakSolution D) {y x : X}
    (hx : x ∈ (chartAt (H := ℂ) y).source) (hD : D x = 0) :
    Dolbeault.AbelPairing.read01 F.logDbar y x
      = (F.toFun x)⁻¹
        * DbarDisk.dbar (F.toFun ∘ (chartAt (H := ℂ) y).symm) ((chartAt (H := ℂ) y) x) := by
  -- rewrite the fiber through `toFun` (off the divisor `ψ_x ≈ f` as germs at `x`).
  have hgerm : F.unit x =ᶠ[𝓝 x] F.toFun := (F.toFun_eventuallyEq_unit hD).symm
  have hfx : F.unit x x = F.toFun x := hgerm.eq_of_nhds
  have hsm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) F.toFun x :=
    F.contMDiffAt_toFun (le_of_eq hD.symm)
  have hfiber : F.logDbarFiber x
      = (F.toFun x)⁻¹ • proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F.toFun x) := by
    rw [logDbarFiber, hgerm.mfderiv_eq, hfx]
  show (F.logDbar x) ((Bundle.Trivialization.symmL ℝ
      (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) (1 : ℂ)) = _
  rw [logDbar_apply, hfiber, ContinuousLinearMap.smul_apply]
  show (F.toFun x)⁻¹ * (proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F.toFun x))
      ((Bundle.Trivialization.symmL ℝ
        (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) y) x) (1 : ℂ)) = _
  congr 1
  exact Dolbeault.AbelPairing.read01_proj01_mfderiv hx (hsm.mdifferentiableAt (by simp))

end WeakSolution

end Jacobians
