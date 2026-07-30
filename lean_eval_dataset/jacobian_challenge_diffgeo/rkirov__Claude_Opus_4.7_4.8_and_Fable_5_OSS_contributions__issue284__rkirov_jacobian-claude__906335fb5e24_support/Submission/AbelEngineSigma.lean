/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-5 (σ layer): the chain `∂̄`-datum and its `∂̄`-potential

Given a 1-chain `c` with all basis periods zero, the total weak solution `G` of `∂c`
(the `zpow`-fold of the per-curve solutions) has `∂̄`-datum `σ_G = d″G/G` pairing to zero
against every basis form — so by the kill theorem (Forster 19.10) `σ_G = ∂̄u`:

* `pairForm_congr_off_finite` — the pairing ignores finitely many fiber values;
* `proj01_logDeriv_prod` — the logarithmic-`∂̄` product rule for finite pointwise products;
* `pairForm_logDbar_piece` — **the per-piece value**: `⟨η, σ_{fₖ}⟩ = ∫ Uₖ·η̂ₖ` (the collapse
  lemma + the planar `U = ∂̄F/F` identity);
* `pairForm_logDbar_curve` — **the per-curve value** `⟨η, σ_{f_γ}⟩ = π·∫_γ η`
  (Forster 20.5's identity through the subdivision product);
* `exists_dbar_potential_of_oneChain` — the assembled `σ_G = ∂̄u`.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.5–20.7 (pp. 162–165);
plan `docs/walls_bc_plan_2026-06-10.md`, phase C-5.
-/
import Submission.AbelDbarKill
import Submission.AbelLogDbar
import Submission.AbelCurveSolution

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology Real
open Set Filter Complex MeasureTheory Metric
open Jacobians.Montel Jacobians.Dolbeault.StokesResidue Jacobians.AbelPlanar

namespace Jacobians

open Jacobians.Dolbeault Jacobians.Dolbeault.AbelPairing

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The planar `U = F⁻¹·∂̄F` identity -/

/-- Away from the two endpoints, the planar `∂̄`-datum is the logarithmic `∂̄` of the piece
solution: `U = F⁻¹·∂̄F`. -/
theorem AbelPlanar.PlanarPieceSolution.inv_mul_dbar_F {c₀ α β : ℂ} {ρ : ℝ}
    (S : PlanarPieceSolution c₀ ρ α β) {z : ℂ} (hzα : z ≠ α) (hzβ : z ≠ β) :
    (S.F z)⁻¹ * DbarDisk.dbar S.F z = S.U z := by
  set r : ℂ → ℂ := fun w => (w - β) / (w - α) with hr
  have hF : S.F = fun w => S.W w * r w := by
    funext w
    rw [PlanarPieceSolution.F, hr, mul_div_assoc]
  have hrd : DifferentiableAt ℂ r z :=
    (differentiableAt_id.sub_const β).div (differentiableAt_id.sub_const α)
      (sub_ne_zero.mpr hzα)
  have hdbar : DbarDisk.dbar S.F z = r z * DbarDisk.dbar S.W z := by
    rw [hF, DbarDisk.dbar_fun_mul ((S.smooth.differentiable (by simp)) z)
      (hrd.restrictScalars ℝ), DbarDisk.dbar_eq_zero_of_differentiableAt hrd]
    ring
  have hFz : S.F z = S.W z * r z := by rw [hF]
  have hWz : S.W z ≠ 0 := S.ne_zero z
  have hrz : r z ≠ 0 := div_ne_zero (sub_ne_zero.mpr hzβ) (sub_ne_zero.mpr hzα)
  rw [hdbar, hFz, PlanarPieceSolution.U]
  field_simp

/-! ### The coefficient-free fiber and the product rule -/

/-- Off the divisor the logarithmic fiber is `f⁻¹·∂̄f` directly. -/
theorem WeakSolution.logDbarFiber_eq_of_coeff_zero {D : Divisor X} (F : WeakSolution D)
    {x : X} (hD : D x = 0) :
    F.logDbarFiber x
      = (F.toFun x)⁻¹ • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) F.toFun x) := by
  have hgerm : F.unit x =ᶠ[𝓝 x] F.toFun := (F.toFun_eventuallyEq_unit hD).symm
  rw [WeakSolution.logDbarFiber, hgerm.mfderiv_eq, hgerm.eq_of_nhds]

/-- The two-factor logarithmic-`∂̄` product rule (function form of `logDbarFiber_mul`). -/
theorem proj01_logDeriv_mul {f g : X → ℂ} {x : X}
    (hf : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) f x)
    (hg : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) g x)
    (hf0 : f x ≠ 0) (hg0 : g x ≠ 0) :
    ((f x * g x)⁻¹ : ℂ) • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (fun y => f y * g y) x)
      = (f x)⁻¹ • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x)
        + (g x)⁻¹ • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x) := by
  have h1 : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x) :=
    (hf.mdifferentiableAt (by simp)).hasMFDerivAt
  have h2 : HasMFDerivAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x) :=
    (hg.mdifferentiableAt (by simp)).hasMFDerivAt
  have hmul := (h1.mul h2).mfderiv
  rw [show (fun y => f y * g y) = (f * g) from rfl, hmul, map_add,
    Dolbeault.proj01_smul, Dolbeault.proj01_smul]
  have ha : (f x * g x)⁻¹ * g x = (f x)⁻¹ := by field_simp
  have hb : (f x * g x)⁻¹ * f x = (g x)⁻¹ := by field_simp
  calc ((f x * g x : ℂ))⁻¹ •
        (f x • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x)
          + g x • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x))
      = ((f x * g x)⁻¹ * g x) • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) f x)
        + ((f x * g x)⁻¹ * f x) • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x) := by
        module
    _ = _ := by rw [ha, hb]

/-- The finite logarithmic-`∂̄` product rule. -/
theorem proj01_logDeriv_prod {x : X} (n : ℕ) (f : ℕ → X → ℂ)
    (hf : ∀ k < n, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (f k) x)
    (hf0 : ∀ k < n, f k x ≠ 0) :
    ((∏ k ∈ Finset.range n, f k x)⁻¹ : ℂ) •
        Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ)
          (fun y => ∏ k ∈ Finset.range n, f k y) x)
      = ∑ k ∈ Finset.range n,
          (f k x)⁻¹ • Dolbeault.proj01 (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (f k) x) := by
  induction n with
  | zero =>
    rw [show (fun y => ∏ k ∈ Finset.range 0, f k y) = fun _ => (1 : ℂ) from by
      funext y; rw [Finset.prod_range_zero], mfderiv_const, map_zero, Finset.sum_range_zero]
    rw [Finset.prod_range_zero, inv_one]
    module
  | succ m ih =>
    have hsm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
        (fun y => ∏ k ∈ Finset.range m, f k y) x := by
      clear ih
      induction m with
      | zero =>
        rw [show (fun y => ∏ k ∈ Finset.range 0, f k y) = fun _ => (1 : ℂ) from by
          funext y; rw [Finset.prod_range_zero]]
        exact contMDiffAt_const
      | succ p ihp =>
        rw [show (fun y => ∏ k ∈ Finset.range (p + 1), f k y)
            = fun y => (∏ k ∈ Finset.range p, f k y) * f p y from by
          funext y; rw [Finset.prod_range_succ]]
        exact (ihp (fun k hk => hf k (by omega)) (fun k hk => hf0 k (by omega))).mul
          (hf p (by omega))
    have hs0 : (∏ k ∈ Finset.range m, f k x) ≠ 0 :=
      Finset.prod_ne_zero_iff.mpr fun k hk => hf0 k (by
        have := Finset.mem_range.mp hk
        omega)
    rw [show (fun y => ∏ k ∈ Finset.range (m + 1), f k y)
        = fun y => (∏ k ∈ Finset.range m, f k y) * f m y from by
      funext y; rw [Finset.prod_range_succ], Finset.prod_range_succ,
      proj01_logDeriv_mul hsm (hf m (by omega)) hs0 (hf0 m (by omega)),
      ih (fun k hk => hf k (by omega)) (fun k hk => hf0 k (by omega)),
      Finset.sum_range_succ]

/-! ### The pairing ignores finitely many fibers -/

theorem Dolbeault.AbelPairing.read01_congr_of_apply_eq {g₁ g₂ : SmoothCOneForms X} {x : X}
    (h : (g₁ x) = (g₂ x)) (y : X) : read01 g₁ y x = read01 g₂ y x := by
  unfold Dolbeault.AbelPairing.read01
  rw [h]

/-- **The pairing ignores finitely many fiber values** (a finite set of chart points is
volume-null). -/
theorem Dolbeault.AbelPairing.pairForm_congr_off_finite (η : HolomorphicOneForms X)
    {g₁ g₂ : SmoothCOneForms X} {E : Set X} (hE : E.Finite)
    (h : ∀ x ∉ E, (g₁ x) = (g₂ x)) :
    pairForm η g₁ = pairForm η g₂ := by
  rw [pairForm, pairForm]
  refine Finset.sum_congr rfl fun j _ => ?_
  refine integral_congr_ae ?_
  have hEfin : (((chartAt (H := ℂ) (coverCenter j)) '' E) : Set ℂ).Finite := hE.image _
  filter_upwards [compl_mem_ae_iff.mpr (hEfin.measure_zero volume)] with z hzE
  show pairingIntegrand g₁ η (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z
    = pairingIntegrand g₂ η (coverRhoC j) (coverCenter j) (coverWindow (X := X) j) z
  rw [pairingIntegrand, pairingIntegrand]
  by_cases hz : z ∈ (chartAt (H := ℂ) (coverCenter j)) '' coverWindow (X := X) j
  · rw [if_pos hz, if_pos hz]
    obtain ⟨hz_tgt, hz_mem⟩ := StokesResidue.symm_mem_of_mem_image
      (coverWindow_subset_source j) hz
    have hxE : (chartAt (H := ℂ) (coverCenter j)).symm z ∉ E := fun hmem =>
      hzE ⟨_, hmem, (chartAt (H := ℂ) (coverCenter j)).right_inv hz_tgt⟩
    rw [read01_congr_of_apply_eq (h _ hxE)]
  · rw [if_neg hz, if_neg hz]

/-! ### The per-piece pairing value -/

set_option maxHeartbeats 1600000 in
/-- **The per-piece pairing value**: the pairing of `η` against the piece `∂̄`-datum is the
planar integral `∫ Uₖ·η̂ₖ` of Forster 20.5. -/
theorem pairForm_logDbar_piece (η : HolomorphicOneForms X) {γ : ℝ → X}
    {hγ : ContinuousOn γ (Icc 0 1)} (S : CurveWeakSolution γ hγ) (k : ℕ) :
    pairForm η (S.pieceSol k).logDbar
      = ∫ z, (S.planar k).U z
          * Jacobians.Montel.localRep η (S.center k)
            ((chartAt (H := ℂ) (S.center k)).symm z) := by
  classical
  set c := S.center k with hc
  set e : OpenPartialHomeomorph X ℂ := chartAt (H := ℂ) c with he
  set ρk := S.ρ k with hρk
  have hρpos : 0 < ρk := (S.planar k).ρ_pos
  have hsub8 : ball (e c) (8 * ρk) ⊆ e.target := S.ball_subset k
  have hsub5t : closedBall (e c) (5 * ρk) ⊆ e.target := fun w hw =>
    hsub8 (mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hw) (by linarith)))
  have hsub6t : ball (e c) (6 * ρk) ⊆ e.target := fun w hw =>
    hsub8 (mem_ball.mpr (lt_of_lt_of_le (mem_ball.mp hw) (by linarith)))
  -- the compact core and the window.
  set K : Set X := e.symm '' closedBall (e c) (5 * ρk) with hK
  set W : Set X := e.source ∩ e ⁻¹' ball (e c) (6 * ρk) with hW
  have hKcomp : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    (e.continuousOn_symm.mono hsub5t)
  have hWopen : IsOpen W := e.isOpen_inter_preimage isOpen_ball
  have hWsub : W ⊆ e.source := fun x hx => hx.1
  have hKW : K ⊆ W := by
    rintro x ⟨w, hw, rfl⟩
    refine ⟨e.map_target (hsub5t hw), ?_⟩
    show e (e.symm w) ∈ ball (e c) (6 * ρk)
    rw [e.right_inv (hsub5t hw)]
    exact mem_ball.mpr (lt_of_le_of_lt (mem_closedBall.mp hw) (by linarith))
  -- the fiber dies off the core (`f ≡ 1` there).
  have hone : ∀ x ∉ K, (S.pieceSol k).toFun x = 1 := by
    intro x hxK
    refine S.pieceSol_one k x fun hxsrc => ?_
    by_contra hdist
    exact hxK ⟨e x, mem_closedBall.mpr (le_of_not_gt hdist), e.left_inv hxsrc⟩
  have hgsupp : ∀ x, x ∉ K → ((S.pieceSol k).logDbar x) = (0 : ℂ →L[ℝ] ℂ) := by
    intro x hxK
    rw [WeakSolution.logDbar_apply]
    refine (S.pieceSol k).logDbarFiber_eq_zero_of_eventually_one ?_
    filter_upwards [hKcomp.isClosed.isOpen_compl.mem_nhds hxK] with y hy
    exact hone y hy
  -- collapse to the single chart-`c` integral.
  rw [pairForm_eq_singleChart ((S.pieceSol k).logDbar_mem_zeroOne) η hWopen hWsub hKcomp
    hKW hgsupp]
  -- the chart image of the window is the `6ρ`-ball.
  have himgW : e '' W = ball (e c) (6 * ρk) := by
    apply Set.Subset.antisymm
    · rintro _ ⟨x, hx, rfl⟩
      exact hx.2
    · intro w hw
      exact ⟨e.symm w, ⟨e.map_target (hsub6t hw), by
        show e (e.symm w) ∈ ball (e c) (6 * ρk)
        rw [e.right_inv (hsub6t hw)]
        exact hw⟩, e.right_inv (hsub6t hw)⟩
  -- a.e. identification with the planar `U·η̂` integrand.
  refine integral_congr_ae ?_
  have hfin : ({(e (γ (S.t k))), (e (γ (S.t (k + 1))))} : Set ℂ).Finite :=
    (Set.finite_singleton _).insert _
  filter_upwards [compl_mem_ae_iff.mpr (hfin.measure_zero volume)] with z hzE
  have hzα : z ≠ e (γ (S.t k)) := fun h => hzE (by rw [h]; exact Set.mem_insert _ _)
  have hzβ : z ≠ e (γ (S.t (k + 1))) := fun h => hzE (by
    rw [h]; exact Set.mem_insert_of_mem _ rfl)
  show pairingIntegrand (S.pieceSol k).logDbar η (fun _ => 1) c W z
    = (S.planar k).U z * Jacobians.Montel.localRep η c (e.symm z)
  rw [pairingIntegrand]
  by_cases hz : z ∈ e '' W
  · rw [if_pos hz]
    have hztgt : z ∈ e.target := by
      rw [himgW] at hz
      exact hsub6t hz
    set x := e.symm z with hx
    have hzball : z ∈ ball ((chartAt (H := ℂ) c) c) (6 * ρk) := by
      rw [← himgW]
      exact hz
    have hxW : x ∈ W := by
      refine ⟨e.map_target hztgt, ?_⟩
      show e (e.symm z) ∈ ball (e c) (6 * ρk)
      rw [e.right_inv hztgt]
      exact hzball
    have hxsrc : x ∈ e.source := hWsub hxW
    have hzx : e x = z := e.right_inv hztgt
    -- the endpoints are inside the chart source.
    have hγk_src : γ (S.t k) ∈ e.source :=
      (S.curve_mem k (S.t k) ⟨le_rfl, S.mono (Nat.le_succ k)⟩).1
    have hγk1_src : γ (S.t (k + 1)) ∈ e.source :=
      (S.curve_mem k (S.t (k + 1)) ⟨S.mono (Nat.le_succ k), le_rfl⟩).1
    -- `x` avoids both endpoints.
    have hxa : x ≠ γ (S.t k) := fun h => hzα (by rw [← hzx, h])
    have hxb : x ≠ γ (S.t (k + 1)) := fun h => hzβ (by rw [← hzx, h])
    -- the divisor dies at `x`.
    have hD0 : (Finsupp.single (γ (S.t (k + 1))) (1 : ℤ)
        - Finsupp.single (γ (S.t k)) 1 : Divisor X) x = 0 := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne hxb, Finsupp.single_eq_of_ne hxa]
      ring
    rw [one_mul]
    rw [(S.pieceSol k).read01_logDbar_of_coeff_zero hxsrc hD0]
    -- the chart read of the solution is the planar `F` near `z`.
    have hgerm : ((S.pieceSol k).toFun ∘ e.symm) =ᶠ[𝓝 z] (S.planar k).F := by
      have hopen : IsOpen (e.target ∩ {w : ℂ | w ≠ e (γ (S.t k))}) :=
        e.open_target.inter (isOpen_compl_singleton)
      filter_upwards [hopen.mem_nhds ⟨hztgt, hzα⟩] with w hw
      have hsymm_src : e.symm w ∈ e.source := e.map_target hw.1
      have hne : e (e.symm w) ≠ e (γ (S.t k)) := by
        rw [e.right_inv hw.1]
        exact hw.2
      show (S.pieceSol k).toFun (e.symm w) = (S.planar k).F w
      rw [S.pieceSol_read k (e.symm w) hsymm_src hne, e.right_inv hw.1]
    have hval : (S.pieceSol k).toFun x = (S.planar k).F z := by
      have h := S.pieceSol_read k x hxsrc (by rw [hzx]; exact hzα)
      rwa [hzx] at h
    rw [hzx, DbarDisk.dbar_congr hgerm, hval,
      (S.planar k).inv_mul_dbar_F hzα hzβ]
  · rw [if_neg hz]
    -- off the window the planar datum vanishes.
    have hUz : (S.planar k).U z = 0 := by
      refine (S.planar k).U_eq_zero_outer ?_
      by_contra hd
      have hd' : dist z ((chartAt (H := ℂ) c) c) ≤ 5 * ρk := le_of_not_gt hd
      refine hz ?_
      rw [himgW]
      exact mem_ball.mpr (lt_of_le_of_lt hd' (by linarith))
    rw [hUz, zero_mul]

/-! ### The per-curve pairing value (Forster 20.5) -/

set_option maxHeartbeats 1600000 in
/-- **The per-curve pairing value** (Forster 20.5): `⟨η, σ_{f_γ}⟩ = π·∫_γ η`. -/
theorem pairForm_logDbar_curve (η : HolomorphicOneForms X) {γ : ℝ → X}
    {hγ : ContinuousOn γ (Icc 0 1)} (S : CurveWeakSolution γ hγ) :
    pairForm η S.sol.logDbar = (π : ℂ) * pathPrimValue η γ hγ := by
  classical
  -- the finite exceptional set of subdivision points.
  set E : Set X := (fun j : Fin (S.n + 1) => γ (S.t j)) '' Set.univ with hE
  have hEfin : E.Finite := (Set.finite_univ).image _
  have hEmem : ∀ j : ℕ, γ (S.t j) ∈ E := by
    intro j
    rcases le_or_gt j S.n with hj | hj
    · exact ⟨⟨j, by omega⟩, Set.mem_univ _, rfl⟩
    · refine ⟨⟨S.n, by omega⟩, Set.mem_univ _, ?_⟩
      show γ (S.t S.n) = γ (S.t j)
      rw [S.t_stab S.n le_rfl, S.t_stab j (by omega)]
  have hEopen : IsOpen Eᶜ := hEfin.isClosed.isOpen_compl
  -- the section decomposition off `E`.
  have hdecomp : ∀ x ∉ E, (S.sol.logDbar x)
      = ((∑ k ∈ Finset.range S.n, (S.pieceSol k).logDbar) x) := by
    intro x hxE
    have hxne : ∀ j : ℕ, x ≠ γ (S.t j) := fun j h => hxE (h ▸ hEmem j)
    -- coefficient bookkeeping: all divisors die at `x`.
    have hγ1 : γ 1 = γ (S.t S.n) := by rw [S.t_stab S.n le_rfl]
    have hγ0 : γ 0 = γ (S.t 0) := by rw [S.t_zero]
    have hDsol : (Finsupp.single (γ 1) (1 : ℤ) - Finsupp.single (γ 0) 1 : Divisor X) x
        = 0 := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne (by rw [hγ1]; exact hxne S.n),
        Finsupp.single_eq_of_ne (by rw [hγ0]; exact hxne 0)]
      ring
    have hDk : ∀ k : ℕ, (Finsupp.single (γ (S.t (k + 1))) (1 : ℤ)
        - Finsupp.single (γ (S.t k)) 1 : Divisor X) x = 0 := by
      intro k
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne (hxne (k + 1)),
        Finsupp.single_eq_of_ne (hxne k)]
      ring
    -- the LHS fiber via the product germ.
    have hprodgerm : S.sol.toFun =ᶠ[𝓝 x]
        fun y => ∏ k ∈ Finset.range S.n, (S.pieceSol k).toFun y := by
      filter_upwards [hEopen.mem_nhds hxE] with y hy
      exact S.sol_eq_prod y fun j h => hy (h ▸ hEmem j)
    have hsolval : S.sol.toFun x = ∏ k ∈ Finset.range S.n, (S.pieceSol k).toFun x :=
      S.sol_eq_prod x hxne
    have hpiece_cm : ∀ k < S.n, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
        (S.pieceSol k).toFun x :=
      fun k _ => (S.pieceSol k).contMDiffAt_toFun (le_of_eq (hDk k).symm)
    have hpiece_ne : ∀ k < S.n, (S.pieceSol k).toFun x ≠ 0 :=
      fun k _ => (S.pieceSol k).toFun_ne_zero_of_coeff_zero (hDk k)
    rw [WeakSolution.logDbar_apply, S.sol.logDbarFiber_eq_of_coeff_zero hDsol,
      hprodgerm.mfderiv_eq, hsolval,
      proj01_logDeriv_prod S.n (fun k => (S.pieceSol k).toFun) hpiece_cm hpiece_ne]
    -- the RHS section-sum value.
    have hcoe : (⇑(∑ k ∈ Finset.range S.n, (S.pieceSol k).logDbar))
        = ∑ k ∈ Finset.range S.n, ⇑((S.pieceSol k).logDbar) :=
      map_sum (ContMDiffSection.coeAddHom _ _ _ _) _ _
    rw [show ((∑ k ∈ Finset.range S.n, (S.pieceSol k).logDbar) x)
        = (⇑(∑ k ∈ Finset.range S.n, (S.pieceSol k).logDbar)) x from rfl, hcoe,
      Finset.sum_apply]
    refine Finset.sum_congr rfl fun k hk => ?_
    rw [show (⇑((S.pieceSol k).logDbar)) x = ((S.pieceSol k).logDbar) x from rfl,
      WeakSolution.logDbar_apply,
      (S.pieceSol k).logDbarFiber_eq_of_coeff_zero (hDk k)]
  -- transfer the pairing through the decomposition and apply the per-piece values.
  rw [Dolbeault.AbelPairing.pairForm_congr_off_finite η hEfin hdecomp, pairForm_sum]
  rw [Finset.sum_congr rfl fun k _ => pairForm_logDbar_piece η S k]
  exact (S.identity η).symm

/-! ### The chain `∂̄`-potential -/

/-- The `zpow`-fold of a finite family of weak solutions, with the `logDbar` sum rule. -/
theorem exists_weakSolution_finsum {n : ℕ} (D : Fin n → Divisor X)
    (F : (m : Fin n) → WeakSolution (D m)) :
    ∃ G : WeakSolution (∑ m, D m),
      ∀ x, G.logDbarFiber x = ∑ m, (F m).logDbarFiber x := by
  induction n with
  | zero =>
    refine ⟨(WeakSolution.one X).recast (by simp), fun x => ?_⟩
    rw [WeakSolution.logDbarFiber_recast, WeakSolution.logDbarFiber_one]
    simp
  | succ m ih =>
    obtain ⟨G', hG'⟩ := ih (fun i => D i.succ) (fun i => F i.succ)
    refine ⟨((F 0).mul G').recast (Fin.sum_univ_succ D).symm, fun x => ?_⟩
    rw [WeakSolution.logDbarFiber_recast, WeakSolution.logDbarFiber_mul, hG' x,
      Fin.sum_univ_succ]

set_option maxHeartbeats 1600000 in
/-- **The chain `∂̄`-potential** (Forster 20.7 (a), the analytic heart): a 1-chain with all
basis periods zero has a weak solution `G` of its boundary whose `∂̄`-datum is exact:
`σ_G = ∂̄u`. -/
theorem exists_dbar_potential_of_oneChain (c : OneChain X)
    (hper : ∀ i : Fin (genus X), c.period (periodBasisForm X i) = 0) :
    ∃ (G : WeakSolution c.boundary) (u : SmoothCFunctions X), dbarL u = G.logDbar := by
  classical
  -- the per-curve solutions.
  have hCWS : ∀ m : Fin c.m, Nonempty (CurveWeakSolution (c.curve m) (c.cont m)) :=
    fun m => exists_curveWeakSolution (c.curve m) (c.cont m)
  set CWS : (m : Fin c.m) → CurveWeakSolution (c.curve m) (c.cont m) :=
    fun m => (hCWS m).some with hCWSdef
  -- the powered solutions and the fold.
  obtain ⟨G, hG⟩ := exists_weakSolution_finsum
    (fun m => c.coeff m • (Finsupp.single (c.curve m 1) (1 : ℤ)
      - Finsupp.single (c.curve m 0) 1))
    (fun m => (CWS m).sol.zpow (c.coeff m))
  -- the boundary is that sum.
  have hbd : c.boundary = ∑ m, c.coeff m • (Finsupp.single (c.curve m 1) (1 : ℤ)
      - Finsupp.single (c.curve m 0) 1) := rfl
  set G' : WeakSolution c.boundary := G.recast hbd.symm with hG'def
  refine ⟨G', ?_⟩
  -- the basis pairings of `σ_{G'}` vanish.
  have hσ : ∀ i : Fin (genus X), pairForm (periodBasisForm X i) G'.logDbar = 0 := by
    intro i
    -- decompose the section.
    have hsec : G'.logDbar = ∑ m, (c.coeff m) • (CWS m).sol.logDbar := by
      refine ContMDiffSection.ext fun x => ?_
      have hcoe : (⇑(∑ m, (c.coeff m) • (CWS m).sol.logDbar))
          = ∑ m, ⇑((c.coeff m) • (CWS m).sol.logDbar) :=
        map_sum (ContMDiffSection.coeAddHom _ _ _ _) _ _
      rw [show ((∑ m, (c.coeff m) • (CWS m).sol.logDbar) x)
          = (⇑(∑ m, (c.coeff m) • (CWS m).sol.logDbar)) x from rfl, hcoe, Finset.sum_apply]
      rw [WeakSolution.logDbar_apply, hG'def, WeakSolution.logDbarFiber_recast, hG x]
      refine Finset.sum_congr rfl fun m _ => ?_
      rw [WeakSolution.logDbarFiber_zpow]
      rw [show (⇑((c.coeff m) • (CWS m).sol.logDbar)) x
          = ((c.coeff m) • (CWS m).sol.logDbar) x from rfl, ContMDiffSection.coe_zsmul]
      rfl
    rw [hsec, pairForm_sum]
    rw [Finset.sum_congr rfl fun m _ => pairForm_zsmul (periodBasisForm X i) (c.coeff m)
      ((CWS m).sol.logDbar)]
    rw [Finset.sum_congr rfl fun m _ => by
      rw [pairForm_logDbar_curve (periodBasisForm X i) (CWS m)]]
    -- `∑ₘ nₘ • (π·∫_{γₘ}) = π·(chain period) = 0`.
    have hp := hper i
    rw [OneChain.period] at hp
    calc (∑ m, c.coeff m • ((π : ℂ) * pathPrimValue (periodBasisForm X i)
          (c.curve m) (c.cont m)))
        = (π : ℂ) * ∑ m, c.coeff m • pathPrimValue (periodBasisForm X i)
            (c.curve m) (c.cont m) := by
          rw [Finset.mul_sum]
          refine Finset.sum_congr rfl fun m _ => ?_
          rw [zsmul_eq_mul, zsmul_eq_mul]
          ring
      _ = 0 := by rw [hp, mul_zero]
  -- the kill theorem.
  obtain ⟨u, hu⟩ := exists_dbarL_eq_of_pairForm_eq_zero G'.logDbar_mem_zeroOne hσ
  exact ⟨u, hu⟩

end Jacobians
