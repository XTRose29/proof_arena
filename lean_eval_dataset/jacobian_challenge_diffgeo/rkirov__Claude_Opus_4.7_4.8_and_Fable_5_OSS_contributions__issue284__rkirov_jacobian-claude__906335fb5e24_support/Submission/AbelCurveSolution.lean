/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Abel engine C-2 (curve layer): the per-curve weak solution (Forster 20.5)

The full Lemma 20.5: every continuous curve `γ : [0,1] → X` has a weak solution of its
boundary divisor `(γ 1) − (γ 0)` together with the **integral identity** tying the planar
`∂̄`-data of its pieces to the path value of every holomorphic 1-form:

  `π · ∫_γ η = ∑ₖ ∫_ℂ Uₖ·(η-coefficient in chart k) dA`     (Forster: `∫_c ω = (1/2πi)∬(df/f)∧ω`).

Contents:
* `CurveWeakSolution γ hγ` — the bundled data: a chart-ball subdivision of the curve,
  per-piece planar solutions (`PlanarPieceSolution`) and per-piece weak solutions with their
  chart reads, the product weak solution of `(γ 1) − (γ 0)`, and the identity;
* `exists_curveWeakSolution` — existence: subdivision by the monotone-cover lemma
  (`exists_monotone_Icc_subset_open_cover_Icc`, as in `exists_primitiveChain`), pieces from
  `exists_pieceWeakSolution`, the identity by evaluating `pathPrimValue` on the primitive
  chain made of the per-chart-ball primitives (`exists_primitive_of_convex`) and applying
  the planar identity `PlanarPieceSolution.integral_U_mul` piecewise.

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), §20.5 (pp. 162–163);
plan `docs/walls_bc_plan_2026-06-10.md`, phase C-2 (E2).
-/
import Submission.AbelPieceSolution
import Submission.AbelChains

noncomputable section

-- ℝ/ℂ-module diamond discipline (as in `AbelChains`/`AbelWeakSolutions`).
set_option backward.isDefEq.respectTransparency false

open scoped Manifold ContDiff Topology Real
open Set Metric Filter Jacobians.AbelPlanar

namespace Jacobians

set_option linter.unusedSectionVars false

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The trivial planar piece solution (degenerate endpoints) -/

/-- The trivial planar piece solution for equal endpoints: `W ≡ 1`. -/
def AbelPlanar.PlanarPieceSolution.trivialOfEq {c₀ α β : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hα : dist α c₀ < ρ) (hβ : dist β c₀ < ρ) (hαβ : α = β) :
    PlanarPieceSolution c₀ ρ α β where
  W := fun _ => 1
  ρ_pos := hρ
  dist_alpha := hα
  dist_beta := hβ
  smooth := contDiff_const
  ne_zero := fun _ => one_ne_zero
  inner := fun _ _ => rfl
  outer := fun z hz => by
    subst hαβ
    have hzα : z - α ≠ 0 := by
      refine sub_ne_zero.mpr fun h => ?_
      rw [h] at hz
      linarith
    rw [div_self hzα]

/-- Planar piece solutions exist with the **unital degenerate normalization**: `W ≡ 1`
whenever the endpoints coincide (needed to keep the piece chart-read uniform). -/
theorem exists_planarPieceSolution_unital {c₀ α β : ℂ} {ρ : ℝ} (hρ : 0 < ρ)
    (hα : dist α c₀ < ρ) (hβ : dist β c₀ < ρ) :
    ∃ S : PlanarPieceSolution c₀ ρ α β, α = β → ∀ z, S.W z = 1 := by
  by_cases hαβ : α = β
  · exact ⟨.trivialOfEq hρ hα hβ hαβ, fun _ _ => rfl⟩
  · obtain ⟨S⟩ := nonempty_planarPieceSolution hρ hα hβ
    exact ⟨S, fun h => absurd h hαβ⟩

/-! ### Primitives over a chart ball -/

/-- A planar primitive of the chart coefficient of `η` over a chart ball is a local
primitive of `η` on the ball preimage (extracted from `exists_isLocalPrimitiveOn`). -/
theorem isLocalPrimitiveOn_comp_chart {η : HolomorphicOneForms X} {x₀ : X} {r : ℝ}
    (hball : ball ((chartAt (H := ℂ) x₀) x₀) r ⊆ (chartAt (H := ℂ) x₀).target)
    {G : ℂ → ℂ}
    (hG : ∀ z ∈ ball ((chartAt (H := ℂ) x₀) x₀) r,
      HasDerivAt G (Montel.localRep η x₀ ((chartAt (H := ℂ) x₀).symm z)) z) :
    IsLocalPrimitiveOn η (G ∘ (chartAt (H := ℂ) x₀))
      ((chartAt (H := ℂ) x₀).source ∩
        (chartAt (H := ℂ) x₀) ⁻¹' ball ((chartAt (H := ℂ) x₀) x₀) r) := by
  rintro y ⟨hys, hyb⟩
  have hzy : (chartAt (H := ℂ) x₀) y ∈ ball ((chartAt (H := ℂ) x₀) x₀) r := hyb
  -- the chart pullback of the primitive agrees with `G` near `chart y`
  have hgerm : (G ∘ (chartAt (H := ℂ) x₀)) ∘ (chartAt (H := ℂ) x₀).symm
      =ᶠ[𝓝 ((chartAt (H := ℂ) x₀) y)] G := by
    filter_upwards [isOpen_ball.mem_nhds hzy] with z hz
    have : (chartAt (H := ℂ) x₀) ((chartAt (H := ℂ) x₀).symm z) = z :=
      (chartAt (H := ℂ) x₀).right_inv (hball hz)
    simp [Function.comp_apply, this]
  have hGdiff : DifferentiableAt ℂ G ((chartAt (H := ℂ) x₀) y) :=
    (hG _ hzy).differentiableAt
  have hpull : DifferentiableAt ℂ ((G ∘ (chartAt (H := ℂ) x₀)) ∘ (chartAt (H := ℂ) x₀).symm)
      ((chartAt (H := ℂ) x₀) y) := hGdiff.congr_of_eventuallyEq hgerm
  have hMD : MDifferentiableAt 𝓘(ℂ) 𝓘(ℂ) (G ∘ (chartAt (H := ℂ) x₀)) y := by
    have h := Dolbeault.mdifferentiableAt_of_differentiableAt_comp
      (G ∘ (chartAt (H := ℂ) x₀)) (hball hzy) hpull
    rwa [(chartAt (H := ℂ) x₀).left_inv hys] at h
  refine ⟨hMD, ?_⟩
  refine oneForm_eq_mfderiv_of_frame_eq η (G ∘ (chartAt (H := ℂ) x₀)) hys hMD ?_
  have hderiv : deriv ((G ∘ (chartAt (H := ℂ) x₀)) ∘ (chartAt (H := ℂ) x₀).symm)
      ((chartAt (H := ℂ) x₀) y) = deriv G ((chartAt (H := ℂ) x₀) y) :=
    Filter.EventuallyEq.deriv_eq hgerm
  rw [hderiv, (hG _ hzy).deriv]
  rw [(chartAt (H := ℂ) x₀).left_inv hys]

/-! ### Folding the pieces -/

/-- **The telescoping product of piece solutions**: the product of weak solutions of the
boundary divisors `(γ(t_{k+1})) − (γ(t_k))`, `k < n`, is a weak solution of
`(γ(t_n)) − (γ 0)`, and away from all subdivision points its value is the pointwise
product. -/
theorem exists_foldWeakSolution (γ : ℝ → X) (t : ℕ → ℝ) (ht0 : t 0 = 0)
    (piece : (k : ℕ) →
      WeakSolution (Finsupp.single (γ (t (k + 1))) (1 : ℤ) - Finsupp.single (γ (t k)) 1))
    (n : ℕ) :
    ∃ F : WeakSolution (Finsupp.single (γ (t n)) (1 : ℤ) - Finsupp.single (γ 0) 1),
      ∀ x, (∀ k, x ≠ γ (t k)) →
        F.toFun x = ∏ k ∈ Finset.range n, (piece k).toFun x := by
  induction n with
  | zero =>
    refine ⟨(WeakSolution.one X).recast ?_, ?_⟩
    · rw [ht0]
      exact (sub_self _).symm
    · intro x _
      rw [WeakSolution.recast_toFun, Finset.prod_range_zero]
      rfl
  | succ m ih =>
    obtain ⟨F, hF⟩ := ih
    refine ⟨(F.mul (piece m)).recast (by abel), ?_⟩
    intro x hx
    have hD1 : (Finsupp.single (γ (t m)) (1 : ℤ) - Finsupp.single (γ 0) 1 : Divisor X) x
        = 0 := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne (hx m),
        Finsupp.single_eq_of_ne (ht0 ▸ hx 0)]
      ring
    have hD2 : (Finsupp.single (γ (t (m + 1))) (1 : ℤ)
        - Finsupp.single (γ (t m)) 1 : Divisor X) x = 0 := by
      rw [Finsupp.sub_apply, Finsupp.single_eq_of_ne (hx (m + 1)),
        Finsupp.single_eq_of_ne (hx m)]
      ring
    rw [WeakSolution.recast_toFun, WeakSolution.mul_toFun_of_coeff_zero F (piece m) hD1 hD2,
      hF x hx, Finset.prod_range_succ]

/-! ### The per-curve weak solution (Forster 20.5) -/

/-- **Per-curve weak-solution data** (Forster 20.5): a chart-ball subdivision
`0 = t₀ ≤ … ≤ t_n = 1` of the curve, per-piece planar solutions and weak solutions with
their chart reads, the product weak solution of the boundary `(γ 1) − (γ 0)`, and the
**integral identity** `π·∫_γ η = ∑ₖ ∫ Uₖ·(η-coefficient)` for every holomorphic 1-form. -/
structure CurveWeakSolution (γ : ℝ → X) (hγ : ContinuousOn γ (Icc 0 1)) where
  /-- number of pieces (indices `k ≥ n` are degenerate `{1}`-blocks) -/
  n : ℕ
  /-- the subdivision (stabilized at `1` from index `n` on) -/
  t : ℕ → ℝ
  t_zero : t 0 = 0
  t_stab : ∀ k, n ≤ k → t k = 1
  mono : Monotone t
  /-- the piece chart centres -/
  center : ℕ → X
  /-- the piece radii -/
  ρ : ℕ → ℝ
  ball_subset : ∀ k, ball ((chartAt (H := ℂ) (center k)) (center k)) (8 * ρ k)
      ⊆ (chartAt (H := ℂ) (center k)).target
  curve_mem : ∀ k, ∀ s ∈ Icc (t k) (t (k + 1)),
      γ s ∈ (chartAt (H := ℂ) (center k)).source ∧
        (chartAt (H := ℂ) (center k)) (γ s) ∈
          ball ((chartAt (H := ℂ) (center k)) (center k)) (ρ k)
  /-- the planar piece solutions (for the chart endpoints of each piece) -/
  planar : (k : ℕ) → PlanarPieceSolution ((chartAt (H := ℂ) (center k)) (center k)) (ρ k)
      ((chartAt (H := ℂ) (center k)) (γ (t k)))
      ((chartAt (H := ℂ) (center k)) (γ (t (k + 1))))
  /-- the per-piece weak solutions -/
  pieceSol : (k : ℕ) →
      WeakSolution (Finsupp.single (γ (t (k + 1))) (1 : ℤ) - Finsupp.single (γ (t k)) 1)
  pieceSol_one : ∀ k x, (x ∈ (chartAt (H := ℂ) (center k)).source →
      5 * ρ k < dist ((chartAt (H := ℂ) (center k)) x)
        ((chartAt (H := ℂ) (center k)) (center k))) → (pieceSol k).toFun x = 1
  pieceSol_read : ∀ k x, x ∈ (chartAt (H := ℂ) (center k)).source →
      (chartAt (H := ℂ) (center k)) x ≠ (chartAt (H := ℂ) (center k)) (γ (t k)) →
      (pieceSol k).toFun x = (planar k).F ((chartAt (H := ℂ) (center k)) x)
  /-- the product weak solution of the curve boundary -/
  sol : WeakSolution (Finsupp.single (γ 1) (1 : ℤ) - Finsupp.single (γ 0) 1)
  sol_eq_prod : ∀ x, (∀ k, x ≠ γ (t k)) →
      sol.toFun x = ∏ k ∈ Finset.range n, (pieceSol k).toFun x
  /-- **the Forster 20.5 identity**: `π·∫_γ η = ∑ₖ ∫ Uₖ·(η-coefficient in chart k)` -/
  identity : ∀ η : HolomorphicOneForms X,
      (π : ℂ) * pathPrimValue η γ hγ
        = ∑ k ∈ Finset.range n, ∫ z, (planar k).U z
            * Montel.localRep η (center k) ((chartAt (H := ℂ) (center k)).symm z)

/-- **Per-curve weak solutions exist** for every continuous curve (Forster 20.5):
subdivision over the chart-ball cover, per-piece solutions, the telescoped product, and
the identity through a chart-ball primitive chain. -/
theorem exists_curveWeakSolution (γ : ℝ → X) (hγ : ContinuousOn γ (Icc 0 1)) :
    Nonempty (CurveWeakSolution γ hγ) := by
  classical
  -- chart-ball radii at every point
  have hdata : ∀ p : X, ∃ ρ : ℝ, 0 < ρ ∧
      ball ((chartAt (H := ℂ) p) p) (8 * ρ) ⊆ (chartAt (H := ℂ) p).target := by
    intro p
    obtain ⟨ε, hε, hsub⟩ := Metric.isOpen_iff.mp (chartAt (H := ℂ) p).open_target _
      ((chartAt (H := ℂ) p).map_source (mem_chart_source ℂ p))
    refine ⟨ε / 8, by linarith, ?_⟩
    rw [show 8 * (ε / 8) = ε by ring]
    exact hsub
  choose ρfun hρpos hρsub using hdata
  -- the open cover of `[0,1]` by piece-ball preimages
  set γ' : Icc (0 : ℝ) 1 → X := fun s => γ s with hγ'
  have hγ'c : Continuous γ' := hγ.restrict
  set Vp : X → Set X := fun p => (chartAt (H := ℂ) p).source ∩
    (chartAt (H := ℂ) p) ⁻¹' ball ((chartAt (H := ℂ) p) p) (ρfun p) with hVp
  have hVpo : ∀ p, IsOpen (Vp p) := fun p =>
    (chartAt (H := ℂ) p).isOpen_inter_preimage isOpen_ball
  have hVpm : ∀ p, p ∈ Vp p := fun p =>
    ⟨mem_chart_source ℂ p, mem_ball_self (hρpos p)⟩
  set c : Icc (0 : ℝ) 1 → Set (Icc (0 : ℝ) 1) := fun τ => γ' ⁻¹' (Vp (γ' τ)) with hc
  have hc₁ : ∀ τ, IsOpen (c τ) := fun τ => (hVpo _).preimage hγ'c
  have hc₂ : (univ : Set (Icc (0 : ℝ) 1)) ⊆ ⋃ τ, c τ := fun τ _ =>
    Set.mem_iUnion.mpr ⟨τ, hVpm _⟩
  obtain ⟨tsub, ht0, htmono, ⟨m, hm⟩, hblocks⟩ :=
    exists_monotone_Icc_subset_open_cover_Icc zero_le_one hc₁ hc₂
  choose τ hτ using hblocks
  set n : ℕ := m + 1 with hn
  set t : ℕ → ℝ := fun k => (tsub k : ℝ) with ht
  have ht_zero : t 0 = 0 := by exact_mod_cast ht0
  have ht_stab : ∀ k, n ≤ k → t k = 1 := fun k hk => by
    exact_mod_cast hm k (le_trans (Nat.le_succ m) hk)
  have ht_mono : Monotone t := fun a b hab => Subtype.coe_le_coe.mpr (htmono hab)
  set center : ℕ → X := fun k => γ' (τ k) with hcenter
  set ρ : ℕ → ℝ := fun k => ρfun (center k) with hρ
  -- block membership in the piece balls
  have hmem : ∀ k, ∀ s ∈ Icc (t k) (t (k + 1)),
      γ s ∈ (chartAt (H := ℂ) (center k)).source ∧
        (chartAt (H := ℂ) (center k)) (γ s) ∈
          ball ((chartAt (H := ℂ) (center k)) (center k)) (ρ k) := by
    intro k s hs
    have hs01 : s ∈ Icc (0 : ℝ) 1 :=
      ⟨le_trans (tsub k).2.1 hs.1, le_trans hs.2 (tsub (k + 1)).2.2⟩
    have hmem' : (⟨s, hs01⟩ : Icc (0 : ℝ) 1) ∈ Icc (tsub k) (tsub (k + 1)) := ⟨hs.1, hs.2⟩
    have h := hτ k hmem'
    rw [hc] at h
    exact h
  -- the endpoints are inside the piece balls
  have htk_mem : ∀ k : ℕ, t k ∈ Icc (t k) (t (k + 1)) :=
    fun k => ⟨le_rfl, ht_mono (Nat.le_succ k)⟩
  have htk1_mem : ∀ k : ℕ, t (k + 1) ∈ Icc (t k) (t (k + 1)) :=
    fun k => ⟨ht_mono (Nat.le_succ k), le_rfl⟩
  have hαball : ∀ k, dist ((chartAt (H := ℂ) (center k)) (γ (t k)))
      ((chartAt (H := ℂ) (center k)) (center k)) < ρ k :=
    fun k => mem_ball.mp (hmem k (t k) (htk_mem k)).2
  have hβball : ∀ k, dist ((chartAt (H := ℂ) (center k)) (γ (t (k + 1))))
      ((chartAt (H := ℂ) (center k)) (center k)) < ρ k :=
    fun k => mem_ball.mp (hmem k (t (k + 1)) (htk1_mem k)).2
  -- planar piece solutions, unital in the degenerate case
  have hplanars : ∀ k : ℕ, ∃ S : PlanarPieceSolution
      ((chartAt (H := ℂ) (center k)) (center k)) (ρ k)
      ((chartAt (H := ℂ) (center k)) (γ (t k)))
      ((chartAt (H := ℂ) (center k)) (γ (t (k + 1)))),
      (chartAt (H := ℂ) (center k)) (γ (t k)) = (chartAt (H := ℂ) (center k)) (γ (t (k + 1)))
        → ∀ z, S.W z = 1 :=
    fun k => exists_planarPieceSolution_unital (hρpos _) (hαball k) (hβball k)
  choose planars hWuni using hplanars
  -- per-piece weak solutions
  have hpieces : ∀ k : ℕ, ∃ sol : WeakSolution
      (Finsupp.single (γ (t (k + 1))) (1 : ℤ) - Finsupp.single (γ (t k)) 1),
      (∀ x, (x ∈ (chartAt (H := ℂ) (center k)).source →
          5 * ρ k < dist ((chartAt (H := ℂ) (center k)) x)
            ((chartAt (H := ℂ) (center k)) (center k))) → sol.toFun x = 1) ∧
      (∀ x, x ∈ (chartAt (H := ℂ) (center k)).source →
        (chartAt (H := ℂ) (center k)) x ≠ (chartAt (H := ℂ) (center k)) (γ (t k)) →
        sol.toFun x = (planars k).F ((chartAt (H := ℂ) (center k)) x)) := by
    intro k
    exact exists_pieceWeakSolution (hmem k (t k) (htk_mem k)).1
      (hmem k (t (k + 1)) (htk1_mem k)).1 (hρsub (center k)) (planars k)
      (fun h => hWuni k (congrArg _ h))
  choose pieceSols hpsol1 hpsol2 using hpieces
  -- the telescoped product
  obtain ⟨Fsol, hFsol⟩ := exists_foldWeakSolution γ t ht_zero pieceSols n
  have hrecast : (Finsupp.single (γ (t n)) (1 : ℤ) - Finsupp.single (γ 0) 1 : Divisor X)
      = Finsupp.single (γ 1) (1 : ℤ) - Finsupp.single (γ 0) 1 := by
    rw [ht_stab n le_rfl]
  -- assemble
  refine ⟨{
    n := n, t := t, t_zero := ht_zero, t_stab := ht_stab, mono := ht_mono
    center := center, ρ := ρ
    ball_subset := fun k => hρsub (center k)
    curve_mem := hmem
    planar := planars
    pieceSol := pieceSols
    pieceSol_one := hpsol1
    pieceSol_read := hpsol2
    sol := Fsol.recast hrecast
    sol_eq_prod := fun x hx => by
      rw [WeakSolution.recast_toFun]
      exact hFsol x hx
    identity := ?_ }⟩
  -- the Forster 20.5 identity, through a chart-ball primitive chain
  intro η
  -- per-piece primitives of the chart coefficient of `η`
  have hcoeff : ∀ k : ℕ, ∃ g : ℂ → ℂ,
      ∀ z ∈ ball ((chartAt (H := ℂ) (center k)) (center k)) (8 * ρ k),
        HasDerivAt g (Montel.localRep η (center k) ((chartAt (H := ℂ) (center k)).symm z))
          z := by
    intro k
    have hanal : DifferentiableOn ℂ
        (fun z => Montel.localRep η (center k) ((chartAt (H := ℂ) (center k)).symm z))
        (ball ((chartAt (H := ℂ) (center k)) (center k)) (8 * ρ k)) :=
      ((Montel.localRep_analyticOn_chartTarget η (center k)).mono
        (hρsub (center k))).differentiableOn
    exact exists_primitive_of_convex (convex_ball _ _) isOpen_ball hanal
  choose g hg using hcoeff
  -- the primitive chain over the subdivision
  let C : PrimitiveChain η γ := {
    n := n, t := t, t_zero := ht_zero, t_stab := ht_stab, mono := ht_mono
    U := fun i => (chartAt (H := ℂ) (center i)).source ∩
      (chartAt (H := ℂ) (center i)) ⁻¹'
        ball ((chartAt (H := ℂ) (center i)) (center i)) (8 * ρ i)
    F := fun i => g i ∘ (chartAt (H := ℂ) (center i))
    isOpen := fun i => (chartAt (H := ℂ) (center i)).isOpen_inter_preimage isOpen_ball
    prim := fun i => isLocalPrimitiveOn_comp_chart (hρsub (center i)) (hg i)
    covers := fun i s hs => ⟨(hmem i s hs).1, Set.mem_preimage.mpr
      (ball_subset_ball (by linarith [hρpos (center i)]) (hmem i s hs).2)⟩ }
  rw [pathPrimValue_eq η hγ C]
  have hval : C.value = ∑ i ∈ Finset.range C.n,
      (C.F i (γ (C.t (i + 1))) - C.F i (γ (C.t i))) := rfl
  rw [hval, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  exact ((planars k).integral_U_mul (hg k)).symm

end Jacobians
