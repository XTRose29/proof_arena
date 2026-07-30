/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-5 (E4): the meromorphic solution `F = e⁻ᵘ·f` (Forster 20.7 (a))

The exp-correction of the chain weak solution: with `σ_G = ∂̄u` (the σ layer), the function
`F := e⁻ᵘ·G` is genuinely meromorphic with divisor `∂c`:

* locally `F = (e⁻ᵘ·ψ_a)·z_a^{D a}` and the cofactor `h_a := e⁻ᵘ·ψ_a` has
  `∂̄h_a = h_a·(σ_G − ∂̄u) = 0`, hence is **holomorphic** (planar Wirtinger:
  `differentiableAt_of_dbar_eq_zero` after a bump extension) and nonvanishing;
* so in each centred chart `F̂ = H·(w − w₀)^{D a}` with `H` analytic nonvanishing — giving
  `MeromorphicAt` everywhere and `orderAtPoint = D` (`meromorphicOrderAt_mul` +
  `meromorphicOrderAt_zpow_id_sub_const`);
* `exists_meromorphic_of_oneChain` — **the Abel engine**: a 1-chain with vanishing basis
  periods bounds a principal divisor: `∃ f, f.div = ∂c`.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), 20.7 proof part (a)
(p. 164); plan `docs/walls_bc_plan_2026-06-10.md`, phase C-5 (E4).
-/
import Submission.AbelEngineSigma

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Real
open Set Filter Complex MeasureTheory Metric
open Jacobians.Dolbeault Jacobians.Dolbeault.AbelPairing

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### Planar `∂̄`-calculus complements -/

/-- The `∂̄` chain rule for a holomorphic OUTER map: `∂̄(f∘g) = f′(g)·∂̄g`. -/
theorem dbar_holo_comp {f g : ℂ → ℂ} {w : ℂ} (hf : DifferentiableAt ℂ f (g w))
    (hg : DifferentiableAt ℝ g w) :
    DbarDisk.dbar (f ∘ g) w = deriv f (g w) * DbarDisk.dbar g w := by
  have hffd : HasFDerivAt f ((deriv f (g w)) • (1 : ℂ →L[ℝ] ℂ)) (g w) :=
    hf.hasDerivAt.complexToReal_fderiv
  have hcomp : fderiv ℝ (f ∘ g) w
      = ((deriv f (g w)) • (1 : ℂ →L[ℝ] ℂ)).comp (fderiv ℝ g w) :=
    (hffd.comp w hg.hasFDerivAt).fderiv
  unfold DbarDisk.dbar
  rw [hcomp]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.one_apply, smul_eq_mul]
  ring

/-- `∂̄(−g) = −∂̄g`. -/
theorem dbar_neg {g : ℂ → ℂ} (w : ℂ) :
    DbarDisk.dbar (fun z => -(g z)) w = -DbarDisk.dbar g w := by
  unfold DbarDisk.dbar
  rw [show (fun z => -(g z)) = -g from rfl, fderiv_neg]
  simp only [ContinuousLinearMap.neg_apply]
  ring

/-! ### The meromorphic solution -/

set_option maxHeartbeats 2000000 in
/-- **The Abel engine** (Forster 20.7, sufficiency): a 1-chain whose basis periods all
vanish bounds a principal divisor — there is a meromorphic function with `div f = ∂c`,
together with its centred local normal form `f̂ = H·(w − w₀)^{∂c(a)}` (analytic
nonvanishing `H`) at every point — the Laurent data the discreteness argument (B-4)
reads residues from. -/
theorem exists_meromorphic_of_oneChain (c : OneChain X)
    (hper : ∀ i : Fin (genus X), c.period (periodBasisForm X i) = 0) :
    ∃ f : MeromorphicFunction X, f.div = c.boundary ∧
      ∀ a : X, ∃ H : ℂ → ℂ,
        AnalyticAt ℂ H ((chartAt (H := ℂ) a) a) ∧ H ((chartAt (H := ℂ) a) a) ≠ 0 ∧
        (f.toFun ∘ (chartAt (H := ℂ) a).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) a) a)]
          fun w => H w * (w - (chartAt (H := ℂ) a) a) ^ (c.boundary a) := by
  classical
  obtain ⟨G, u, hu⟩ := exists_dbar_potential_of_oneChain c hper
  set Ffun : X → ℂ := fun x => Complex.exp (-(u x)) * G.toFun x with hFfun
  -- THE LOCAL MODEL: at every `a`, in the centred chart, `F̂ = H·(w − w₀)^{D a}` with `H`
  -- analytic and nonvanishing at `w₀ = chart a a`.
  have hloc : ∀ a : X, ∃ H : ℂ → ℂ,
      AnalyticAt ℂ H ((chartAt (H := ℂ) a) a) ∧ H ((chartAt (H := ℂ) a) a) ≠ 0 ∧
      (Ffun ∘ (chartAt (H := ℂ) a).symm) =ᶠ[𝓝 ((chartAt (H := ℂ) a) a)]
        fun w => H w * (w - (chartAt (H := ℂ) a) a) ^ (c.boundary a) := by
    intro a
    set φ : OpenPartialHomeomorph X ℂ := chartAt (H := ℂ) a with hφ
    set w₀ : ℂ := φ a with hw₀
    -- the planar reads on the chart image of the unit neighbourhood.
    set N : Set X := G.nbhd a ∩ φ.source with hN
    have hNopen : IsOpen N := (G.isOpen_nbhd a).inter φ.open_source
    have haN : a ∈ N := ⟨G.mem_nbhd a, mem_chart_source ℂ a⟩
    have hNsub : N ⊆ φ.source := fun x hx => hx.2
    set T : Set ℂ := φ '' N with hT
    have hTopen : IsOpen T := φ.isOpen_image_of_subset_source hNopen hNsub
    have hw₀T : w₀ ∈ T := mem_image_of_mem _ haN
    set hcof : X → ℂ := fun y => Complex.exp (-(u y)) * G.unit a y with hcof_def
    set Hraw : ℂ → ℂ := fun w => hcof (φ.symm w) with hHraw
    -- smoothness of the cofactor read at points of `T`.
    have hexp_cm : ContMDiff 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun z : ℂ => Complex.exp z) := by
      rw [contMDiff_iff_contDiff]
      exact (Complex.contDiff_exp (𝕜 := ℂ)).restrict_scalars ℝ
    have hcof_cm : ∀ x ∈ N, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) hcof x := by
      intro x hx
      have h1 : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => Complex.exp (-(u y))) x :=
        (hexp_cm.contMDiffAt).comp x ((u.contMDiff x).neg)
      exact h1.mul (G.unit_contMDiffAt a hx.1)
    have hHraw_cd : ∀ w ∈ T, ContDiffAt ℝ (⊤ : ℕ∞) Hraw w := by
      rintro w ⟨x, hxN, rfl⟩
      have hsymm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm (φ x) :=
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := a) _
          (φ.map_source (hNsub hxN))).contMDiffAt
          (φ.open_target.mem_nhds (φ.map_source (hNsub hxN)))
      have hx' : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) hcof (φ.symm (φ x)) := by
        rw [φ.left_inv (hNsub hxN)]
        exact hcof_cm x hxN
      exact contMDiffAt_iff_contDiffAt.mp (hx'.comp (φ x) hsymm)
    -- `∂̄Hraw = 0` on `T` (the key cancellation `σ_G = ∂̄u`).
    have hdbar0 : ∀ w ∈ T, DbarDisk.dbar Hraw w = 0 := by
      rintro w ⟨x, hxN, rfl⟩
      have hxsrc : x ∈ φ.source := hNsub hxN
      have hxz : φ.symm (φ x) = x := φ.left_inv hxsrc
      -- the two planar reads at `φ x`.
      have hu_read : DbarDisk.dbar (⇑u ∘ φ.symm) (φ x)
          = read01 (dbarL u) a x := (read01_dbarL u hxsrc).symm
      -- `read01 (logDbar) = ψ⁻¹·∂̄ψ̂` at points of the unit neighbourhood.
      have hψ_md : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (G.unit a) x :=
        (G.unit_contMDiffAt a hxN.1).mdifferentiableAt (by simp)
      have hfiber : (G.logDbar x) = (G.unit a x)⁻¹ •
          Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (G.unit a) x) := by
        rw [WeakSolution.logDbar_apply]
        exact G.logDbarFiber_eventuallyEq a x hxN.1
      have hread_log : read01 G.logDbar a x
          = (G.unit a x)⁻¹ * DbarDisk.dbar ((G.unit a) ∘ φ.symm) (φ x) := by
        show (G.logDbar x) ((Bundle.Trivialization.symmL ℝ
          (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) a) x) (1 : ℂ)) = _
        rw [hfiber, ContinuousLinearMap.smul_apply]
        show (G.unit a x)⁻¹ * (Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (G.unit a) x))
            ((Bundle.Trivialization.symmL ℝ
              (trivializationAt ℂ (TangentSpace (𝓘(ℝ, ℂ))) a) x) (1 : ℂ)) = _
        congr 1
        exact read01_proj01_mfderiv hxsrc hψ_md
      -- `∂̄u = σ_G` at the read level.
      have hreads : DbarDisk.dbar (⇑u ∘ φ.symm) (φ x)
          = (G.unit a x)⁻¹ * DbarDisk.dbar ((G.unit a) ∘ φ.symm) (φ x) := by
        rw [hu_read, hu, hread_log]
      have hψ0 : G.unit a x ≠ 0 := G.unit_ne_zero a x hxN.1
      have hψdbar : DbarDisk.dbar ((G.unit a) ∘ φ.symm) (φ x)
          = G.unit a x * DbarDisk.dbar (⇑u ∘ φ.symm) (φ x) := by
        rw [hreads, ← mul_assoc, mul_inv_cancel₀ hψ0, one_mul]
      -- expand `∂̄Hraw` by the product/chain rules.
      have hT_tgt : φ x ∈ φ.target := φ.map_source hxsrc
      have hsymm_diff : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ.symm (φ x) :=
        (contMDiffOn_chart_symm (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := a) _
          hT_tgt).contMDiffAt (φ.open_target.mem_nhds hT_tgt)
      have huread_diff : DifferentiableAt ℝ (⇑u ∘ φ.symm) (φ x) :=
        (contMDiffAt_iff_contDiffAt.mp (((u.contMDiff (φ.symm (φ x)))).comp (φ x)
          hsymm_diff)).differentiableAt (by simp)
      have hψread_diff : DifferentiableAt ℝ ((G.unit a) ∘ φ.symm) (φ x) := by
        have h := contMDiffAt_iff_contDiffAt.mp
          (((by rw [hxz]; exact G.unit_contMDiffAt a hxN.1 :
            ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (G.unit a) (φ.symm (φ x)))).comp (φ x)
            hsymm_diff)
        exact h.differentiableAt (by simp)
      have hneg_diff : DifferentiableAt ℝ (fun w => -((⇑u ∘ φ.symm) w)) (φ x) :=
        huread_diff.neg
      have hexp_diff : DifferentiableAt ℝ (fun w => Complex.exp (-((⇑u ∘ φ.symm) w)))
          (φ x) := by
        have : DifferentiableAt ℝ (Complex.exp ∘ fun w => -((⇑u ∘ φ.symm) w)) (φ x) :=
          (Complex.differentiable_exp (𝕜 := ℝ) _).comp (φ x) hneg_diff
        exact this
      have hHraw_eq : Hraw = fun w => Complex.exp (-((⇑u ∘ φ.symm) w))
          * ((G.unit a) ∘ φ.symm) w := rfl
      rw [hHraw_eq, DbarDisk.dbar_fun_mul hexp_diff hψread_diff]
      -- `∂̄(exp(−û)) = −exp(−û)·∂̄û`.
      have hdbar_exp : DbarDisk.dbar (fun w => Complex.exp (-((⇑u ∘ φ.symm) w))) (φ x)
          = -Complex.exp (-((⇑u ∘ φ.symm) (φ x))) * DbarDisk.dbar (⇑u ∘ φ.symm) (φ x) := by
        rw [show (fun w => Complex.exp (-((⇑u ∘ φ.symm) w)))
            = Complex.exp ∘ (fun w => -((⇑u ∘ φ.symm) w)) from rfl,
          dbar_holo_comp (Complex.differentiable_exp (𝕜 := ℂ) _) hneg_diff,
          Complex.deriv_exp, dbar_neg]
        ring
      rw [hdbar_exp, hψdbar,
        show ((G.unit a) ∘ φ.symm) (φ x) = G.unit a x from by
          rw [Function.comp_apply, hxz]]
      ring
    -- the bump extension and analyticity at `w₀`.
    obtain ⟨r, hr_pos, hr_sub⟩ := Metric.isOpen_iff.mp hTopen w₀ hw₀T
    set χ : ContDiffBump w₀ := ⟨r / 2, 3 * r / 4, by positivity, by linarith⟩ with hχ
    set H : ℂ → ℂ := fun w => ((χ w : ℝ) : ℂ) * Hraw w with hH
    have hH_smooth : ContDiff ℝ (⊤ : ℕ∞) H := by
      rw [contDiff_iff_contDiffAt]
      intro w
      rcases lt_or_ge (dist w w₀) r with hw | hw
      · exact ((Complex.ofRealCLM.contDiff.comp χ.contDiff).contDiffAt).mul
          (hHraw_cd w (hr_sub (mem_ball.mpr hw)))
      · refine (contDiffAt_const (c := (0 : ℂ))).congr_of_eventuallyEq ?_
        have hopen : IsOpen {v : ℂ | 3 * r / 4 < dist v w₀} :=
          isOpen_lt continuous_const (continuous_id.dist continuous_const)
        filter_upwards [hopen.mem_nhds (show 3 * r / 4 < dist w w₀ by linarith)] with v hv
        show ((χ v : ℝ) : ℂ) * Hraw v = 0
        rw [χ.zero_of_le_dist hv.le]
        simp
    have hH_eq : ∀ w ∈ ball w₀ (r / 2), H w = Hraw w := by
      intro w hw
      show ((χ w : ℝ) : ℂ) * Hraw w = Hraw w
      rw [χ.one_of_mem_closedBall (ball_subset_closedBall hw)]
      simp
    have hH_dbar0 : ∀ w ∈ ball w₀ (r / 2), DbarDisk.dbar H w = 0 := by
      intro w hw
      have hgermH : H =ᶠ[𝓝 w] Hraw := by
        filter_upwards [isOpen_ball.mem_nhds hw] with v hv
        exact hH_eq v hv
      rw [DbarDisk.dbar_congr hgermH]
      exact hdbar0 w (hr_sub (ball_subset_ball (by linarith) hw))
    have hH_anal : AnalyticAt ℂ H w₀ := by
      have hdiff : DifferentiableOn ℂ H (ball w₀ (r / 2)) := fun w hw =>
        (Dolbeault.DbarDiskCohomology.differentiableAt_of_dbar_eq_zero hH_smooth
          (hH_dbar0 w hw)).differentiableWithinAt
      exact (hdiff.analyticOnNhd isOpen_ball) w₀ (mem_ball_self (by positivity))
    have hH_ne : H w₀ ≠ 0 := by
      rw [hH_eq w₀ (mem_ball_self (by positivity))]
      show Complex.exp (-(u (φ.symm w₀))) * G.unit a (φ.symm w₀) ≠ 0
      rw [show φ.symm w₀ = a from φ.left_inv (mem_chart_source ℂ a)]
      exact mul_ne_zero (Complex.exp_ne_zero _) (G.unit_ne_zero a a (G.mem_nbhd a))
    -- the germ identity `F̂ = H·(w − w₀)^{D a}` near `w₀`.
    refine ⟨H, hH_anal, hH_ne, ?_⟩
    have hpre : ∀ᶠ w in 𝓝 w₀, w ∈ φ.target ∧ φ.symm w ∈ N ∧ w ∈ ball w₀ (r / 2) := by
      have h1 : ∀ᶠ w in 𝓝 w₀, w ∈ φ.target :=
        φ.open_target.mem_nhds (φ.map_source (mem_chart_source ℂ a))
      have h2 : ∀ᶠ w in 𝓝 w₀, φ.symm w ∈ N := by
        have hcont : ContinuousAt φ.symm w₀ :=
          φ.continuousAt_symm (φ.map_source (mem_chart_source ℂ a))
        refine hcont.preimage_mem_nhds (hNopen.mem_nhds ?_)
        rw [show φ.symm w₀ = a from φ.left_inv (mem_chart_source ℂ a)]
        exact haN
      have h3 : ∀ᶠ w in 𝓝 w₀, w ∈ ball w₀ (r / 2) :=
        isOpen_ball.mem_nhds (mem_ball_self (by positivity))
      filter_upwards [h1, h2, h3] with w hw1 hw2 hw3
      exact ⟨hw1, hw2, hw3⟩
    filter_upwards [hpre] with w hw
    obtain ⟨hw_tgt, hw_N, hw_ball⟩ := hw
    show Ffun (φ.symm w) = H w * (w - w₀) ^ (c.boundary a)
    rw [hH_eq w hw_ball]
    show Complex.exp (-(u (φ.symm w))) * G.toFun (φ.symm w)
      = (Complex.exp (-(u (φ.symm w))) * G.unit a (φ.symm w)) * (w - w₀) ^ (c.boundary a)
    rw [G.normalForm a (φ.symm w) hw_N.1]
    have hcc : chartCoord a (φ.symm w) = w - w₀ := by
      show φ (φ.symm w) - φ a = w - w₀
      rw [φ.right_inv hw_tgt, hw₀]
    rw [hcc]
    ring
  -- MEROMORPHY everywhere.
  have hmero : IsMeromorphic X Ffun := by
    intro a
    obtain ⟨H, hH, _, hgerm⟩ := hloc a
    have hM : MeromorphicAt (fun w => H w * (w - (chartAt (H := ℂ) a) a) ^ (c.boundary a))
        ((chartAt (H := ℂ) a) a) := by
      have h1 : MeromorphicAt H ((chartAt (H := ℂ) a) a) := hH.meromorphicAt
      have h2 : MeromorphicAt ((· - (chartAt (H := ℂ) a) a) ^ (c.boundary a))
          ((chartAt (H := ℂ) a) a) := by fun_prop
      exact h1.mul h2
    exact hM.congr (hgerm.filter_mono nhdsWithin_le_nhds).symm
  -- THE ORDER COMPUTATION.
  refine ⟨⟨Ffun, hmero⟩, ?_, hloc⟩
  have horder : ∀ a : X,
      (⟨Ffun, hmero⟩ : MeromorphicFunction X).orderAtPoint a = c.boundary a := by
    intro a
    obtain ⟨H, hH, hH0, hgerm⟩ := hloc a
    rw [MeromorphicFunction.orderAtPoint,
      meromorphicOrderAt_congr (hgerm.filter_mono nhdsWithin_le_nhds)]
    have hsplit : (fun w => H w * (w - (chartAt (H := ℂ) a) a) ^ (c.boundary a))
        = H * ((· - (chartAt (H := ℂ) a) a) ^ (c.boundary a)) := rfl
    rw [hsplit, meromorphicOrderAt_mul hH.meromorphicAt (by fun_prop),
      hH.meromorphicOrderAt_eq, (hH.analyticOrderAt_eq_zero).mpr hH0,
      meromorphicOrderAt_zpow_id_sub_const]
    simp
  refine Finsupp.ext fun x => ?_
  rw [show ((⟨Ffun, hmero⟩ : MeromorphicFunction X).div) x
      = (⟨Ffun, hmero⟩ : MeromorphicFunction X).orderAtPoint x from rfl]
  exact horder x

end Jacobians
