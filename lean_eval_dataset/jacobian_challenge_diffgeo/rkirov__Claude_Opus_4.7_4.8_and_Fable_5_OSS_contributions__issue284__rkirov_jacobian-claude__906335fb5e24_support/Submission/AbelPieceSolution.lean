/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-2 (manifold layer): the per-piece weak solution (Forster 20.5(a))

Lifts the planar piece solution (`PlanarPieceSolution`, `AbelPlanarPiece`) to a genuine
`WeakSolution` of the two-point divisor `(γ(t_{k+1})) − (γ(t_k))` on the surface:

* `exists_chartCompare_unit` — the chart-comparison unit: for `p` in the source of the chart
  at `x₀`, the centred coordinate of the `x₀`-chart factors through the canonical centred
  coordinate `chartCoord p` by a smooth nonvanishing unit (`dslope` of the chart transition;
  nonvanishing from `deriv_chart_transition_of_isManifold_ne_zero`).  This is what lets a
  divisor-normal-form in the *piece* chart be re-read in the *canonical* chart that
  `WeakSolution` fixes.
* `exists_pieceWeakSolution` — the per-piece weak solution: glue `F = W·(z−β)/(z−α)` (read
  through the piece chart) with the constant `1` off the compact `5ρ`-ball preimage; its
  local units at the pole `Pa` / zero `Pb` are the planar cofactor times the
  chart-comparison units.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.5 proof part (a),
pp. 162–163; plan `docs/walls_bc_plan_2026-06-10.md`, phase C-2 (E2).
-/
import Submission.AbelPlanarPiece
import Submission.AbelWeakSolutions
import Submission.Discharge.Manifold.MeromorphicAt

noncomputable section

-- ℝ/ℂ-module diamond discipline (as in `AbelChains`/`AbelWeakSolutions`).
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology
open Set Metric Filter Jacobians.AbelPlanar

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The chart-comparison unit -/

/-- **The chart-comparison unit.**  For `p` in the source of the chart at `x₀`, the centred
`x₀`-chart coordinate of `p` factors as a smooth nonvanishing unit times the canonical
centred coordinate `chartCoord p`:

  `chartAt x₀ x − chartAt x₀ p = u x · chartCoord p x`   near `p`.

`u` is `dslope` of the chart transition read through the chart at `p`; its value at `p` is
the transition derivative, nonzero on a complex manifold. -/
theorem exists_chartCompare_unit {x₀ p : X} (hp : p ∈ (chartAt (H := ℂ) x₀).source) :
    ∃ (V : Set X) (u : X → ℂ), IsOpen V ∧ p ∈ V ∧
      V ⊆ (chartAt (H := ℂ) x₀).source ∩ (chartAt (H := ℂ) p).source ∧
      (∀ x ∈ V, ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) u x) ∧ (∀ x ∈ V, u x ≠ 0) ∧
      ∀ x ∈ V, (chartAt (H := ℂ) x₀) x - (chartAt (H := ℂ) x₀) p
        = u x * chartCoord p x := by
  set e : OpenPartialHomeomorph X ℂ := chartAt (H := ℂ) x₀ with he
  set ep : OpenPartialHomeomorph X ℂ := chartAt (H := ℂ) p with hep
  set w₀ : ℂ := ep p with hw₀
  set T : ℂ → ℂ := e ∘ ep.symm with hT
  -- the transition is analytic at the centre with nonzero derivative
  have hTanal : AnalyticAt ℂ T w₀ := Dolbeault.transition_analyticAt hp
  have hT'ne : deriv T w₀ ≠ 0 :=
    Jacobians.Discharge.deriv_chart_transition_of_isManifold_ne_zero
      (chart_mem_atlas ℂ p) (chart_mem_atlas ℂ x₀) (mem_chart_source ℂ p) hp
  -- `q := dslope T w₀` is analytic at `w₀` with nonzero value there
  obtain ⟨pser, hpser⟩ := hTanal
  have hq : AnalyticAt ℂ (dslope T w₀) w₀ := ⟨_, hpser.has_fpower_series_dslope_fslope⟩
  have hq0 : dslope T w₀ w₀ ≠ 0 := by
    rw [dslope_same]
    exact hT'ne
  -- an open planar neighbourhood where `q` is analytic and nonvanishing
  have hev : ∀ᶠ w in 𝓝 w₀, AnalyticAt ℂ (dslope T w₀) w ∧ dslope T w₀ w ≠ 0 :=
    hq.eventually_analyticAt.and (hq.continuousAt.eventually_ne hq0)
  obtain ⟨O, hOsub, hOopen, hw₀O⟩ := _root_.eventually_nhds_iff.mp hev
  -- the manifold neighbourhood and the unit
  refine ⟨(ep.source ∩ ep ⁻¹' O) ∩ e.source, fun x => dslope T w₀ (ep x),
    ((ep.isOpen_inter_preimage hOopen).inter e.open_source),
    ⟨⟨mem_chart_source ℂ p, hw₀O⟩, hp⟩, fun x hx => ⟨hx.2, hx.1.1⟩, ?_, ?_, ?_⟩
  · -- smoothness: `q ∘ (chart at p)` is chart-analytic at every point of the set
    rintro x ⟨⟨hxs, hxO⟩, _⟩
    refine Dolbeault.contMDiffAt_real_of_chart_analyticAt ?_
    -- read in the self chart at `x`: `q ∘ (ep ∘ (chartAt x).symm)`
    have htrans : AnalyticAt ℂ ((ep : X → ℂ) ∘ (chartAt (H := ℂ) x).symm)
        ((chartAt (H := ℂ) x) x) := Dolbeault.transition_analyticAt hxs
    have hpt : ((ep : X → ℂ) ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)
        = ep x := by
      simp only [Function.comp_apply, (chartAt (H := ℂ) x).left_inv (mem_chart_source ℂ x)]
    have hqx : AnalyticAt ℂ (dslope T w₀)
        (((ep : X → ℂ) ∘ (chartAt (H := ℂ) x).symm) ((chartAt (H := ℂ) x) x)) := by
      rw [hpt]
      exact (hOsub _ hxO).1
    exact hqx.comp htrans
  · -- nonvanishing
    rintro x ⟨⟨hxs, hxO⟩, _⟩
    exact (hOsub _ hxO).2
  · -- the factorization
    rintro x ⟨⟨hxs, _⟩, hxe⟩
    have hfact : (ep x - w₀) * dslope T w₀ (ep x) = T (ep x) - T w₀ := by
      have h := sub_smul_dslope T w₀ (ep x)
      simpa [smul_eq_mul] using h
    have hTx : T (ep x) = e x := by
      rw [hT]
      simp only [Function.comp_apply, ep.left_inv hxs]
    have hTw₀ : T w₀ = e p := by
      rw [hT, hw₀]
      simp only [Function.comp_apply, ep.left_inv (mem_chart_source ℂ p)]
    have hcc : chartCoord p x = ep x - w₀ := rfl
    rw [hcc, ← hTx, ← hTw₀, ← hfact]
    ring

/-! ### Smoothness helpers: planar functions read through a chart -/

/-- The chart map is real-smooth at every source point. -/
theorem contMDiffAt_chart_real {x₀ x : X} (hx : x ∈ (chartAt (H := ℂ) x₀).source) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (chartAt (H := ℂ) x₀ : X → ℂ) x :=
  (contMDiffOn_chart (I := 𝓘(ℝ, ℂ)) (n := (⊤ : ℕ∞)) (x := x₀)).contMDiffAt
    ((chartAt (H := ℂ) x₀).open_source.mem_nhds hx)

/-- A planar `C^∞` function read through a chart is real-smooth at every source point. -/
theorem contMDiffAt_planar_comp_chart {φ : ℂ → ℂ} (hφ : ContDiff ℝ (⊤ : ℕ∞) φ)
    {x₀ x : X} (hx : x ∈ (chartAt (H := ℂ) x₀).source) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => φ ((chartAt (H := ℂ) x₀) y)) x := by
  have hφm : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) φ ((chartAt (H := ℂ) x₀) x) :=
    contMDiffAt_iff_contDiffAt.mpr hφ.contDiffAt
  exact hφm.comp x (contMDiffAt_chart_real hx)

/-- The piece solution `F = W·(z−β)/(z−α)` read through a chart is real-smooth at every
source point whose chart image avoids the pole `α`. -/
theorem AbelPlanar.PlanarPieceSolution.contMDiffAt_F_comp_chart {c₀ α β : ℂ} {ρ : ℝ}
    (S : PlanarPieceSolution c₀ ρ α β) {x₀ x : X}
    (hx : x ∈ (chartAt (H := ℂ) x₀).source) (hne : (chartAt (H := ℂ) x₀) x ≠ α) :
    ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞)
      (fun y => S.F ((chartAt (H := ℂ) x₀) y)) x := by
  set e : OpenPartialHomeomorph X ℂ := chartAt (H := ℂ) x₀ with he
  have hW : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => S.W (e y)) x :=
    contMDiffAt_planar_comp_chart S.smooth hx
  have hsubβ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => e y - β) x :=
    (contMDiffAt_chart_real hx).sub contMDiffAt_const
  have hsubα : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => e y - α) x :=
    (contMDiffAt_chart_real hx).sub contMDiffAt_const
  have hinv : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => (e y - α)⁻¹) x :=
    (WeakSolution.contMDiffAt_inv_complex (sub_ne_zero.mpr hne)).comp x hsubα
  refine ContMDiffAt.congr_of_eventuallyEq ((hW.mul hsubβ).mul hinv) ?_
  filter_upwards with y
  show S.F (e y) = S.W (e y) * (e y - β) * (e y - α)⁻¹
  rw [AbelPlanar.PlanarPieceSolution.F, div_eq_mul_inv]

/-! ### The per-piece weak solution (Forster 20.5(a) on the surface) -/

/-- **The per-piece weak solution.**  Given a planar piece solution `S` for the chart
endpoints `α = chart Pa`, `β = chart Pb` (with trivial cofactor in the degenerate case
`Pa = Pb`), the function `S.F ∘ chart`, glued with the constant `1` off the compact
`closedBall c₀ (5ρ)`-preimage, is a weak solution of the divisor `(Pb) − (Pa)`.  It is
`≡ 1` as soon as the chart image leaves `ball c₀ (5ρ)` (or off the chart source), and it
reads as the planar `S.F` throughout the chart source away from the pole point. -/
theorem exists_pieceWeakSolution {x₀ Pa Pb : X} {ρ : ℝ}
    (hPa : Pa ∈ (chartAt (H := ℂ) x₀).source) (hPb : Pb ∈ (chartAt (H := ℂ) x₀).source)
    (hball : Metric.ball ((chartAt (H := ℂ) x₀) x₀) (8 * ρ) ⊆ (chartAt (H := ℂ) x₀).target)
    (S : PlanarPieceSolution ((chartAt (H := ℂ) x₀) x₀) ρ
      ((chartAt (H := ℂ) x₀) Pa) ((chartAt (H := ℂ) x₀) Pb))
    (hW1 : Pa = Pb → ∀ z, S.W z = 1) :
    ∃ sol : WeakSolution (Finsupp.single Pb (1 : ℤ) - Finsupp.single Pa 1),
      (∀ x, (x ∈ (chartAt (H := ℂ) x₀).source →
          5 * ρ < dist ((chartAt (H := ℂ) x₀) x) ((chartAt (H := ℂ) x₀) x₀)) →
        sol.toFun x = 1) ∧
      (∀ x, x ∈ (chartAt (H := ℂ) x₀).source →
        (chartAt (H := ℂ) x₀) x ≠ (chartAt (H := ℂ) x₀) Pa →
        sol.toFun x = S.F ((chartAt (H := ℂ) x₀) x)) := by
  classical
  rcases eq_or_ne Pa Pb with hPab | hPab
  · -- degenerate piece: the constant solution `1`
    subst hPab
    refine ⟨(WeakSolution.one X).recast (sub_self _).symm, ?_, ?_⟩
    · intro x _
      rw [WeakSolution.recast_toFun]
      rfl
    · intro x _ hne
      rw [WeakSolution.recast_toFun]
      show (1 : ℂ) = S.F ((chartAt (H := ℂ) x₀) x)
      rw [AbelPlanar.PlanarPieceSolution.F, hW1 rfl, one_mul,
        div_self (sub_ne_zero.mpr hne)]
  -- the genuine two-point piece
  have hρ := S.ρ_pos
  have hαβ : ((chartAt (H := ℂ) x₀) Pa) ≠ ((chartAt (H := ℂ) x₀) Pb) := fun h => hPab ((chartAt (H := ℂ) x₀).injOn hPa hPb h)
  -- chart-comparison units at the two endpoints
  obtain ⟨Vu, u, hVuo, hPaVu, hVusub, husm, hu0, huid⟩ := exists_chartCompare_unit hPa
  obtain ⟨Vv, v, hVvo, hPbVv, hVvsub, hvsm, hv0, hvid⟩ := exists_chartCompare_unit hPb
  -- the inner open region and the gluing compact
  set A : Set X := (chartAt (H := ℂ) x₀).source ∩ (chartAt (H := ℂ) x₀) ⁻¹' Metric.ball ((chartAt (H := ℂ) x₀) x₀) (6 * ρ) with hA
  have hAopen : IsOpen A := (chartAt (H := ℂ) x₀).isOpen_inter_preimage Metric.isOpen_ball
  have hAsub : A ⊆ (chartAt (H := ℂ) x₀).source := fun x hx => hx.1
  have hsub5t : Metric.closedBall ((chartAt (H := ℂ) x₀) x₀) (5 * ρ) ⊆ (chartAt (H := ℂ) x₀).target := fun w hw =>
    hball (Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith)))
  set K : Set X := (chartAt (H := ℂ) x₀).symm '' Metric.closedBall ((chartAt (H := ℂ) x₀) x₀) (5 * ρ) with hK
  have hKcomp : IsCompact K := (isCompact_closedBall _ _).image_of_continuousOn
    ((chartAt (H := ℂ) x₀).continuousOn_symm.mono hsub5t)
  have hKA : K ⊆ A := by
    rintro x ⟨w, hw, rfl⟩
    refine ⟨(chartAt (H := ℂ) x₀).map_target (hsub5t hw), ?_⟩
    show (chartAt (H := ℂ) x₀) ((chartAt (H := ℂ) x₀).symm w) ∈ Metric.ball ((chartAt (H := ℂ) x₀) x₀) (6 * ρ)
    rw [(chartAt (H := ℂ) x₀).right_inv (hsub5t hw)]
    exact Metric.mem_ball.mpr (lt_of_le_of_lt (Metric.mem_closedBall.mp hw) (by linarith))
  have hPaA : Pa ∈ A := ⟨hPa, Metric.mem_ball.mpr (by linarith [S.dist_alpha])⟩
  have hPbA : Pb ∈ A := ⟨hPb, Metric.mem_ball.mpr (by linarith [S.dist_beta])⟩
  -- the glued solution function
  set f : X → ℂ := fun x => if x ∈ A then S.F ((chartAt (H := ℂ) x₀) x) else 1 with hf
  have hf_A : ∀ x ∈ A, f x = S.F ((chartAt (H := ℂ) x₀) x) := fun x hx => if_pos hx
  have hf_one : ∀ x, x ∉ K → f x = 1 := by
    intro x hxK
    by_cases hxA : x ∈ A
    · have h5 : 5 * ρ < dist ((chartAt (H := ℂ) x₀) x) ((chartAt (H := ℂ) x₀) x₀) := by
        by_contra h
        exact hxK ⟨(chartAt (H := ℂ) x₀) x, Metric.mem_closedBall.mpr (le_of_not_gt h), (chartAt (H := ℂ) x₀).left_inv (hAsub hxA)⟩
      rw [hf_A x hxA, S.F_eq_one_outer h5]
    · show (if x ∈ A then S.F ((chartAt (H := ℂ) x₀) x) else 1) = 1
      rw [if_neg hxA]
  have hf_conj1 : ∀ x, (x ∈ (chartAt (H := ℂ) x₀).source → 5 * ρ < dist ((chartAt (H := ℂ) x₀) x) ((chartAt (H := ℂ) x₀) x₀)) → f x = 1 := by
    intro x hx5
    by_cases hxA : x ∈ A
    · rw [hf_A x hxA, S.F_eq_one_outer (hx5 (hAsub hxA))]
    · show (if x ∈ A then S.F ((chartAt (H := ℂ) x₀) x) else 1) = 1
      rw [if_neg hxA]
  have hf_read : ∀ x, x ∈ (chartAt (H := ℂ) x₀).source → (chartAt (H := ℂ) x₀) x ≠ ((chartAt (H := ℂ) x₀) Pa) → f x = S.F ((chartAt (H := ℂ) x₀) x) := by
    intro x hx _
    by_cases hxA : x ∈ A
    · exact hf_A x hxA
    · have h6 : 6 * ρ ≤ dist ((chartAt (H := ℂ) x₀) x) ((chartAt (H := ℂ) x₀) x₀) := by
        by_contra h
        exact hxA ⟨hx, Metric.mem_ball.mpr (lt_of_not_ge h)⟩
      have h5 : 5 * ρ < dist ((chartAt (H := ℂ) x₀) x) ((chartAt (H := ℂ) x₀) x₀) := by linarith
      rw [S.F_eq_one_outer h5]
      show (if x ∈ A then S.F ((chartAt (H := ℂ) x₀) x) else 1) = 1
      rw [if_neg hxA]
  -- divisor coefficients
  have hDPa : (Finsupp.single Pb (1 : ℤ) - Finsupp.single Pa 1 : Divisor X) Pa = -1 := by
    rw [Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne hPab]
    ring
  have hDPb : (Finsupp.single Pb (1 : ℤ) - Finsupp.single Pa 1 : Divisor X) Pb = 1 := by
    rw [Finsupp.sub_apply, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (Ne.symm hPab)]
    ring
  have hD0 : ∀ a, a ≠ Pa → a ≠ Pb →
      (Finsupp.single Pb (1 : ℤ) - Finsupp.single Pa 1 : Divisor X) a = 0 := by
    intro a h1 h2
    rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne h2, Finsupp.single_eq_of_ne h1]
    ring
  -- assemble the weak solution
  refine ⟨{
    toFun := f
    nbhd := fun a =>
      if a = Pa then (A ∩ Vu) \ {Pb}
      else if a = Pb then (A ∩ Vv) \ {Pa}
      else if a ∈ K then (A ∩ (chartAt (H := ℂ) a).source) \ {Pa, Pb}
      else Kᶜ ∩ (chartAt (H := ℂ) a).source
    unit := fun a =>
      if a = Pa then fun x => S.W ((chartAt (H := ℂ) x₀) x) * ((chartAt (H := ℂ) x₀) x - ((chartAt (H := ℂ) x₀) Pb)) * (u x)⁻¹
      else if a = Pb then fun x => S.W ((chartAt (H := ℂ) x₀) x) * v x * ((chartAt (H := ℂ) x₀) x - ((chartAt (H := ℂ) x₀) Pa))⁻¹
      else f
    isOpen_nbhd := ?_
    mem_nbhd := ?_
    nbhd_subset := ?_
    unit_contMDiffOn := ?_
    unit_ne_zero := ?_
    normalForm := ?_ }, hf_conj1, hf_read⟩
  · -- isOpen_nbhd
    intro a
    by_cases h1 : a = Pa
    · rw [if_pos h1]
      exact (hAopen.inter hVuo).sdiff isClosed_singleton
    rw [if_neg h1]
    by_cases h2 : a = Pb
    · rw [if_pos h2]
      exact (hAopen.inter hVvo).sdiff isClosed_singleton
    rw [if_neg h2]
    by_cases h3 : a ∈ K
    · rw [if_pos h3]
      exact (hAopen.inter (chartAt (H := ℂ) a).open_source).sdiff
        ((Set.finite_singleton Pb).insert Pa).isClosed
    · rw [if_neg h3]
      exact hKcomp.isClosed.isOpen_compl.inter (chartAt (H := ℂ) a).open_source
  · -- mem_nbhd
    intro a
    by_cases h1 : a = Pa
    · subst h1
      rw [if_pos rfl]
      exact ⟨⟨hPaA, hPaVu⟩, by simp [hPab]⟩
    rw [if_neg h1]
    by_cases h2 : a = Pb
    · subst h2
      rw [if_pos rfl]
      exact ⟨⟨hPbA, hPbVv⟩, by simp [Ne.symm hPab]⟩
    rw [if_neg h2]
    by_cases h3 : a ∈ K
    · rw [if_pos h3]
      exact ⟨⟨hKA h3, mem_chart_source ℂ a⟩, by simp [h1, h2]⟩
    · rw [if_neg h3]
      exact ⟨h3, mem_chart_source ℂ a⟩
  · -- nbhd_subset
    intro a
    by_cases h1 : a = Pa
    · subst h1
      rw [if_pos rfl]
      exact fun x hx => (hVusub hx.1.2).2
    rw [if_neg h1]
    by_cases h2 : a = Pb
    · subst h2
      rw [if_pos rfl]
      exact fun x hx => (hVvsub hx.1.2).2
    rw [if_neg h2]
    by_cases h3 : a ∈ K
    · rw [if_pos h3]
      exact fun x hx => hx.1.2
    · rw [if_neg h3]
      exact fun x hx => hx.2
  · -- unit_contMDiffOn
    intro a
    by_cases h1 : a = Pa
    · subst h1
      rw [if_pos rfl, if_pos rfl]
      intro x hx
      refine ContMDiffAt.contMDiffWithinAt ?_
      have hxsrc : x ∈ (chartAt (H := ℂ) x₀).source := hAsub hx.1.1
      have hW := contMDiffAt_planar_comp_chart S.smooth hxsrc
      have hsubβ : ContMDiffAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (⊤ : ℕ∞) (fun y => (chartAt (H := ℂ) x₀) y - ((chartAt (H := ℂ) x₀) Pb)) x :=
        (contMDiffAt_chart_real hxsrc).sub contMDiffAt_const
      have huinv := (WeakSolution.contMDiffAt_inv_complex (hu0 x hx.1.2)).comp x
        (husm x hx.1.2)
      exact (hW.mul hsubβ).mul huinv
    rw [if_neg h1, if_neg h1]
    by_cases h2 : a = Pb
    · subst h2
      rw [if_pos rfl, if_pos rfl]
      intro x hx
      refine ContMDiffAt.contMDiffWithinAt ?_
      have hxsrc : x ∈ (chartAt (H := ℂ) x₀).source := hAsub hx.1.1
      have hW := contMDiffAt_planar_comp_chart S.smooth hxsrc
      have hxPa : x ≠ Pa := by simpa using hx.2
      have hne : (chartAt (H := ℂ) x₀) x ≠ ((chartAt (H := ℂ) x₀) Pa) := fun h => hxPa ((chartAt (H := ℂ) x₀).injOn hxsrc hPa h)
      have hinv := (WeakSolution.contMDiffAt_inv_complex (sub_ne_zero.mpr hne)).comp x
        ((contMDiffAt_chart_real hxsrc).sub contMDiffAt_const)
      exact (hW.mul (hvsm x hx.1.2)).mul hinv
    rw [if_neg h2, if_neg h2]
    by_cases h3 : a ∈ K
    · rw [if_pos h3]
      intro x hx
      have hxA := hx.1.1
      have hxsrc : x ∈ (chartAt (H := ℂ) x₀).source := hAsub hxA
      have hxPa : x ≠ Pa := fun h => hx.2 (by simp [h])
      have hne : (chartAt (H := ℂ) x₀) x ≠ ((chartAt (H := ℂ) x₀) Pa) := fun h => hxPa ((chartAt (H := ℂ) x₀).injOn hxsrc hPa h)
      have hcongr : f =ᶠ[𝓝 x] fun y => S.F ((chartAt (H := ℂ) x₀) y) := by
        filter_upwards [hAopen.mem_nhds hxA] with y hy
        exact hf_A y hy
      exact ContMDiffAt.contMDiffWithinAt
        ((S.contMDiffAt_F_comp_chart hxsrc hne).congr_of_eventuallyEq hcongr)
    · rw [if_neg h3]
      intro x hx
      have hone : f =ᶠ[𝓝 x] fun _ => (1 : ℂ) := by
        filter_upwards [hKcomp.isClosed.isOpen_compl.mem_nhds hx.1] with y hy
        exact hf_one y hy
      exact ContMDiffAt.contMDiffWithinAt (contMDiffAt_const.congr_of_eventuallyEq hone)
  · -- unit_ne_zero
    intro a
    by_cases h1 : a = Pa
    · subst h1
      rw [if_pos rfl, if_pos rfl]
      intro x hx
      have hxsrc : x ∈ (chartAt (H := ℂ) x₀).source := hAsub hx.1.1
      have hxPb : x ≠ Pb := by simpa using hx.2
      have hneβ : (chartAt (H := ℂ) x₀) x ≠ ((chartAt (H := ℂ) x₀) Pb) := fun h => hxPb ((chartAt (H := ℂ) x₀).injOn hxsrc hPb h)
      exact mul_ne_zero (mul_ne_zero (S.ne_zero _) (sub_ne_zero.mpr hneβ))
        (inv_ne_zero (hu0 x hx.1.2))
    rw [if_neg h1, if_neg h1]
    by_cases h2 : a = Pb
    · subst h2
      rw [if_pos rfl, if_pos rfl]
      intro x hx
      have hxsrc : x ∈ (chartAt (H := ℂ) x₀).source := hAsub hx.1.1
      have hxPa : x ≠ Pa := by simpa using hx.2
      have hneα : (chartAt (H := ℂ) x₀) x ≠ ((chartAt (H := ℂ) x₀) Pa) := fun h => hxPa ((chartAt (H := ℂ) x₀).injOn hxsrc hPa h)
      exact mul_ne_zero (mul_ne_zero (S.ne_zero _) (hv0 x hx.1.2))
        (inv_ne_zero (sub_ne_zero.mpr hneα))
    rw [if_neg h2, if_neg h2]
    by_cases h3 : a ∈ K
    · rw [if_pos h3]
      intro x hx
      have hxA := hx.1.1
      have hxsrc : x ∈ (chartAt (H := ℂ) x₀).source := hAsub hxA
      have hxPa : x ≠ Pa := fun h => hx.2 (by simp [h])
      have hxPb : x ≠ Pb := fun h => hx.2 (by simp [h])
      have hneα : (chartAt (H := ℂ) x₀) x ≠ ((chartAt (H := ℂ) x₀) Pa) := fun h => hxPa ((chartAt (H := ℂ) x₀).injOn hxsrc hPa h)
      have hneβ : (chartAt (H := ℂ) x₀) x ≠ ((chartAt (H := ℂ) x₀) Pb) := fun h => hxPb ((chartAt (H := ℂ) x₀).injOn hxsrc hPb h)
      rw [hf_A x hxA]
      exact S.F_ne_zero hneα hneβ
    · rw [if_neg h3]
      intro x hx
      rw [hf_one x hx.1]
      exact one_ne_zero
  · -- normalForm
    intro a
    by_cases h1 : a = Pa
    · rw [if_pos h1, if_pos h1]
      intro x hx
      rw [h1, hDPa, zpow_neg_one, hf_A x hx.1.1]
      have hid : (chartAt (H := ℂ) x₀) x - ((chartAt (H := ℂ) x₀) Pa)
          = u x * chartCoord Pa x := huid x hx.1.2
      show S.F ((chartAt (H := ℂ) x₀) x) = S.W ((chartAt (H := ℂ) x₀) x)
        * ((chartAt (H := ℂ) x₀) x - ((chartAt (H := ℂ) x₀) Pb)) * (u x)⁻¹
        * (chartCoord Pa x)⁻¹
      rw [AbelPlanar.PlanarPieceSolution.F, div_eq_mul_inv, hid, mul_inv]
      ring
    rw [if_neg h1, if_neg h1]
    by_cases h2 : a = Pb
    · rw [if_pos h2, if_pos h2]
      intro x hx
      rw [h2, hDPb, zpow_one, hf_A x hx.1.1]
      have hid : (chartAt (H := ℂ) x₀) x - ((chartAt (H := ℂ) x₀) Pb)
          = v x * chartCoord Pb x := hvid x hx.1.2
      show S.F ((chartAt (H := ℂ) x₀) x) = S.W ((chartAt (H := ℂ) x₀) x) * v x
        * ((chartAt (H := ℂ) x₀) x - ((chartAt (H := ℂ) x₀) Pa))⁻¹ * chartCoord Pb x
      rw [AbelPlanar.PlanarPieceSolution.F, div_eq_mul_inv, hid]
      ring
    rw [if_neg h2, if_neg h2]
    by_cases h3 : a ∈ K
    · rw [if_pos h3]
      intro x _
      rw [hD0 a h1 h2, zpow_zero, mul_one]
    · rw [if_neg h3]
      intro x _
      rw [hD0 a h1 h2, zpow_zero, mul_one]

end Jacobians
