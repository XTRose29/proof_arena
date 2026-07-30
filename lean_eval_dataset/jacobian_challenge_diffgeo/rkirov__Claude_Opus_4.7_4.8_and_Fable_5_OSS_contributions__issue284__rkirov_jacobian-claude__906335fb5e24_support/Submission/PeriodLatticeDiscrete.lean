/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Forster 21.4(b) — discreteness of the period lattice (dissection-free)

The period lattice is isolated at `0`: there is a neighbourhood `W ∈ 𝓝 0` of `ℂ^g`
meeting `truePeriodLattice X` only in `0`.

Forster's argument: `W` is the image of the local Jacobi map `G` (B-2, the IFT); a nonzero
lattice point `t = G(z) ∈ W` yields a 1-chain — chart segments `aⱼ → xⱼ` minus the loop
combination realizing `t` — with ALL basis periods zero, so the **Abel engine** (C-5)
produces a meromorphic `f` with `div f = ∑ⱼ(xⱼ − aⱼ)`: simple poles at the `aⱼ` (those with
`xⱼ ≠ aⱼ`) with nonvanishing leading Laurent coefficients.  The **residue theorem** applied
to each `f·ωᵢ` gives `A·c = 0` for the evaluation matrix `A = (ωᵢ(aⱼ))` and the residue
vector `c ≠ 0` — contradicting `det A ≠ 0` (B-1).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), 21.4(b) (p. 169);
plan `docs/walls_bc_plan_2026-06-10.md`, phase B-4.
-/
import Submission.AbelEngineMeromorphic
import Submission.AbelChains
import Submission.PeriodLatticeNondegenerate
import Submission.Dolbeault.SerreResidueRamifiedRealSlitGeometry

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Topology
open Set Filter Complex Metric
open Jacobians.OfCurveSkeleton Jacobians.Dolbeault

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The simple-pole residue read -/

/-- `Res_c (Φ·(z−c)⁻¹) = Φ(c)` for `Φ` analytic at `c` (split off the constant term via
`dslope`). -/
theorem resAt_analyticAt_mul_sub_inv {Φ : ℂ → ℂ} {c : ℂ} (hΦ : AnalyticAt ℂ Φ c) :
    Dolbeault.resAt (fun w => Φ w * (w - c)⁻¹) c = Φ c := by
  obtain ⟨pser, hpser⟩ := hΦ
  have hd : AnalyticAt ℂ (dslope Φ c) c := ⟨_, hpser.has_fpower_series_dslope_fslope⟩
  -- the split `Φ·(w−c)⁻¹ = Φ(c)·(w−c)⁻¹ + dslope Φ c` off `c`.
  have hgerm : (fun w => Φ w * (w - c)⁻¹) =ᶠ[𝓝[≠] c]
      (fun w => Φ c * (w - c)⁻¹) + dslope Φ c := by
    filter_upwards [self_mem_nhdsWithin] with w hw
    have hwc : w - c ≠ 0 := sub_ne_zero.mpr hw
    have hds : (w - c) * dslope Φ c w = Φ w - Φ c := by
      have h := sub_smul_dslope Φ c w
      simpa [smul_eq_mul] using h
    show Φ w * (w - c)⁻¹ = Φ c * (w - c)⁻¹ + dslope Φ c w
    rw [show dslope Φ c w = (Φ w - Φ c) * (w - c)⁻¹ from by
      rw [eq_mul_inv_iff_mul_eq₀ hwc, mul_comm]; exact hds]
    ring
  rw [Dolbeault.resAt_congr hgerm]
  -- additivity + the two atomic residues.
  have h1 : Dolbeault.HoloPunctured (fun w => Φ c * (w - c)⁻¹) c := by
    refine ⟨1, one_pos, fun z hz => ?_⟩
    exact (differentiableAt_const _).mul
      ((differentiableAt_id.sub_const c).inv (sub_ne_zero.mpr hz.2))
  obtain ⟨ρd, hρd, hball⟩ := Metric.isOpen_iff.mp (isOpen_analyticAt ℂ (dslope Φ c)) c
    hd.eventually_analyticAt.self_of_nhds
  have h2 : Dolbeault.HoloPunctured (dslope Φ c) c := by
    refine ⟨ρd, hρd, fun z hz => ?_⟩
    exact (hball hz.1).differentiableAt
  rw [Dolbeault.resAt_add h1 h2, Dolbeault.resAt_const_mul_sub_inv,
    Dolbeault.resAt_eq_zero_of_differentiableOn_ball hρd
      (fun z hz => (hball hz).differentiableAt), add_zero]

/-- `pathPrimValue` only depends on the curve (any continuity witness). -/
theorem pathPrimValue_congr_curve {η : HolomorphicOneForms X} {γ₁ γ₂ : ℝ → X} (h : γ₁ = γ₂)
    (h₁ : ContinuousOn γ₁ (Icc 0 1)) :
    pathPrimValue η γ₁ h₁ = pathPrimValue η γ₂ (h ▸ h₁) := by
  subst h
  rfl

/-! ### Pairwise-disjoint chart-ball data at the base points -/

/-- Pairwise-disjoint open neighbourhoods of an injective finite family (T2 separation,
intersected over the off-diagonal pairs). -/
theorem exists_pairwise_disjoint_opens {n : ℕ} {a : Fin n → X} (ha : Function.Injective a) :
    ∃ O : Fin n → Set X, (∀ j, IsOpen (O j)) ∧ (∀ j, a j ∈ O j) ∧
      ∀ j k, j ≠ k → Disjoint (O j) (O k) := by
  classical
  have hpair : ∀ j k : Fin n, j ≠ k → ∃ uv : Set X × Set X,
      IsOpen uv.1 ∧ IsOpen uv.2 ∧ a j ∈ uv.1 ∧ a k ∈ uv.2 ∧ Disjoint uv.1 uv.2 := by
    intro j k hjk
    obtain ⟨u, v, hu, hv, hau, hav, huv⟩ := t2_separation (fun h => hjk (ha h))
    exact ⟨(u, v), hu, hv, hau, hav, huv⟩
  choose! uv huv1 huv2 hauv havuv hdisj using hpair
  refine ⟨fun j => ⋂ k ∈ (Finset.univ.erase j), ((uv j k).1 ∩ (uv k j).2), ?_, ?_, ?_⟩
  · intro j
    refine isOpen_biInter_finset fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact (huv1 j k (Ne.symm hkj)).inter (huv2 k j hkj)
  · intro j
    refine Set.mem_biInter fun k hk => ?_
    have hkj : k ≠ j := (Finset.mem_erase.mp hk).1
    exact ⟨hauv j k (Ne.symm hkj), havuv k j hkj⟩
  · intro j k hjk
    have hsub1 : (⋂ l ∈ (Finset.univ.erase j), ((uv j l).1 ∩ (uv l j).2)) ⊆ (uv j k).1 := by
      intro x hx
      have := Set.mem_iInter₂.mp hx k (Finset.mem_erase.mpr ⟨Ne.symm hjk, Finset.mem_univ k⟩)
      exact this.1
    have hsub2 : (⋂ l ∈ (Finset.univ.erase k), ((uv k l).1 ∩ (uv l k).2)) ⊆ (uv j k).2 := by
      intro x hx
      have := Set.mem_iInter₂.mp hx j (Finset.mem_erase.mpr ⟨hjk, Finset.mem_univ j⟩)
      exact this.2
    exact Set.disjoint_of_subset hsub1 hsub2 (hdisj j k hjk)

set_option maxHeartbeats 2000000 in
/-- **Forster 21.4(b): the period lattice is isolated at `0`.**  There is a neighbourhood
of `0 ∈ ℂ^g` meeting the period lattice only in `0`. -/
theorem truePeriodLattice_isolated_zero :
    ∃ U ∈ 𝓝 (0 : Fin (genus X) → ℂ),
      ∀ v ∈ truePeriodLattice X, v ∈ U → v = 0 := by
  classical
  obtain ⟨a, hainj, hdet, hG0, hmap⟩ := exists_jacobiMap_map_nhds (X := X)
  -- pairwise-disjoint opens at the base points.
  obtain ⟨O, hOopen, haO, hOdisj⟩ := exists_pairwise_disjoint_opens hainj
  -- chart-ball radii whose `symm`-images stay in `O j`.
  have hrad : ∀ j, ∃ r : ℝ, 0 < r ∧
      ball ((chartAt (H := ℂ) (a j)) (a j)) r
        ⊆ (chartAt (H := ℂ) (a j)) '' (O j ∩ (chartAt (H := ℂ) (a j)).source) := by
    intro j
    have hopen : IsOpen ((chartAt (H := ℂ) (a j)) ''
        (O j ∩ (chartAt (H := ℂ) (a j)).source)) :=
      (chartAt (H := ℂ) (a j)).isOpen_image_of_subset_source
        ((hOopen j).inter (chartAt (H := ℂ) (a j)).open_source) inter_subset_right
    have hmem : (chartAt (H := ℂ) (a j)) (a j) ∈ (chartAt (H := ℂ) (a j)) ''
        (O j ∩ (chartAt (H := ℂ) (a j)).source) :=
      mem_image_of_mem _ ⟨haO j, mem_chart_source ℂ (a j)⟩
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp hopen _ hmem
    exact ⟨r, hr, hsub⟩
  choose r hrpos hrsub using hrad
  -- the polydisc window and its Jacobi image.
  set V : Set (Fin (genus X) → ℂ) :=
    Set.univ.pi (fun j => ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)) with hV
  have hVnhds : V ∈ 𝓝 (jacobiCenter a) := by
    refine set_pi_mem_nhds Set.finite_univ fun j _ => ?_
    exact isOpen_ball.mem_nhds (mem_ball_self (hrpos j))
  refine ⟨jacobiMap a '' V, hmap V hVnhds, ?_⟩
  -- the discreteness claim.
  intro t htΓ htW
  by_contra ht0
  obtain ⟨z, hzV, hzt⟩ := htW
  have hz_ball : ∀ j, z j ∈ ball ((chartAt (H := ℂ) (a j)) (a j)) (r j) :=
    fun j => hzV j (Set.mem_univ j)
  -- the ball is inside the chart target.
  have hball_tgt : ∀ j, ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)
      ⊆ (chartAt (H := ℂ) (a j)).target := by
    intro j w hw
    obtain ⟨y, hy, hyz⟩ := hrsub j hw
    rw [← hyz]
    exact (chartAt (H := ℂ) (a j)).map_source hy.2
  -- the endpoints `x j` and their geometry.
  set x : Fin (genus X) → X := fun j => (chartAt (H := ℂ) (a j)).symm (z j) with hx
  have hx_mem : ∀ j, x j ∈ O j ∩ (chartAt (H := ℂ) (a j)).source := by
    intro j
    obtain ⟨y, hy, hyz⟩ := hrsub j (hz_ball j)
    have hxy : x j = y := by
      rw [hx]
      show (chartAt (H := ℂ) (a j)).symm (z j) = y
      rw [← hyz, (chartAt (H := ℂ) (a j)).left_inv hy.2]
    rw [hxy]
    exact hy
  have hchart_x : ∀ j, (chartAt (H := ℂ) (a j)) (x j) = z j :=
    fun j => (chartAt (H := ℂ) (a j)).right_inv (hball_tgt j (hz_ball j))
  have hsymm_c : ∀ j, (chartAt (H := ℂ) (a j)).symm ((chartAt (H := ℂ) (a j)) (a j)) = a j :=
    fun j => (chartAt (H := ℂ) (a j)).left_inv (mem_chart_source ℂ (a j))
  -- nondegeneracy: some coordinate moved.
  have hzc : z ≠ jacobiCenter a := by
    intro h
    rw [h, hG0] at hzt
    exact ht0 hzt.symm
  obtain ⟨j₀, hj₀⟩ := Function.ne_iff.mp hzc
  have hxa : ∀ j, z j ≠ jacobiCenter a j → x j ≠ a j := by
    intro j hzj h
    refine hzj ?_
    rw [← hchart_x j, h]
    rfl
  have hxa_eq : ∀ j, z j = jacobiCenter a j → x j = a j := by
    intro j hzj
    rw [hx]
    show (chartAt (H := ℂ) (a j)).symm (z j) = a j
    rw [show z j = (chartAt (H := ℂ) (a j)) (a j) from hzj]
    exact hsymm_c j
  -- the chain: chart segments `a j → x j` minus the lattice combination of loops.
  set σ : Fin (genus X) → ℝ → X := fun j s =>
    (chartAt (H := ℂ) (a j)).symm
      ((chartAt (H := ℂ) (a j)) (a j) + (s : ℂ) * (z j - (chartAt (H := ℂ) (a j)) (a j)))
    with hσ
  have hseg_ball : ∀ j, ∀ s : ℝ, s ∈ Icc (0 : ℝ) 1 →
      (chartAt (H := ℂ) (a j)) (a j) + (s : ℂ) * (z j - (chartAt (H := ℂ) (a j)) (a j))
        ∈ ball ((chartAt (H := ℂ) (a j)) (a j)) (r j) := by
    intro j s hs
    have h := (convex_ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)).add_smul_sub_mem
      (mem_ball_self (hrpos j)) (hz_ball j) ⟨hs.1, hs.2⟩
    rwa [show (s : ℂ) * (z j - (chartAt (H := ℂ) (a j)) (a j))
        = s • (z j - (chartAt (H := ℂ) (a j)) (a j)) from Complex.real_smul.symm]
  have hσ_cont : ∀ j, ContinuousOn (σ j) (Icc 0 1) := by
    intro j
    refine ((chartAt (H := ℂ) (a j)).continuousOn_symm.comp ?_ ?_)
    · exact (Continuous.continuousOn (by fun_prop))
    · intro s hs
      exact hball_tgt j (hseg_ball j s hs)
  have hσ0 : ∀ j, σ j 0 = a j := by
    intro j
    show (chartAt (H := ℂ) (a j)).symm ((chartAt (H := ℂ) (a j)) (a j)
        + ((0 : ℝ) : ℂ) * (z j - (chartAt (H := ℂ) (a j)) (a j))) = a j
    rw [show (chartAt (H := ℂ) (a j)) (a j)
        + ((0 : ℝ) : ℂ) * (z j - (chartAt (H := ℂ) (a j)) (a j))
        = (chartAt (H := ℂ) (a j)) (a j) by push_cast; ring]
    exact hsymm_c j
  have hσ1 : ∀ j, σ j 1 = x j := by
    intro j
    show (chartAt (H := ℂ) (a j)).symm ((chartAt (H := ℂ) (a j)) (a j)
        + ((1 : ℝ) : ℂ) * (z j - (chartAt (H := ℂ) (a j)) (a j))) = x j
    rw [show (chartAt (H := ℂ) (a j)) (a j)
        + ((1 : ℝ) : ℂ) * (z j - (chartAt (H := ℂ) (a j)) (a j)) = z j by push_cast; ring]
  -- the lattice combination realizing `t`.
  have htmem := htΓ
  rw [truePeriodLattice, Submodule.mem_span_set'] at htmem
  obtain ⟨nl, fl, gl, hsum⟩ := htmem
  choose lam hlam hval using fun k : Fin nl => (gl k).2
  -- the chain.
  set c : OneChain X := {
    m := genus X + nl
    coeff := Fin.addCases (fun _ => 1) (fun k => -(fl k))
    curve := Fin.addCases σ lam
    cont := by
      intro j
      refine Fin.addCases ?_ ?_ j
      · intro j'
        rw [Fin.addCases_left]
        exact hσ_cont j'
      · intro k
        rw [Fin.addCases_right]
        exact (hlam k).cont.continuousOn } with hc
  -- the boundary.
  have hbd : c.boundary = ∑ j, (Finsupp.single (x j) (1 : ℤ) - Finsupp.single (a j) 1) := by
    rw [OneChain.boundary]
    show (∑ m : Fin (genus X + nl), _) = _
    rw [Fin.sum_univ_add]
    have hL : ∀ j : Fin (genus X),
        (Fin.addCases (motive := fun _ => ℤ) (fun _ => 1) (fun k => -(fl k))
            (Fin.castAdd nl j)) •
          (Finsupp.single ((Fin.addCases (motive := fun _ => ℝ → X) σ lam
              (Fin.castAdd nl j)) 1) (1 : ℤ)
            - Finsupp.single ((Fin.addCases (motive := fun _ => ℝ → X) σ lam
              (Fin.castAdd nl j)) 0) 1)
        = Finsupp.single (x j) (1 : ℤ) - Finsupp.single (a j) 1 := by
      intro j
      rw [Fin.addCases_left, Fin.addCases_left, hσ1 j, hσ0 j, one_smul]
    have hR : ∀ k : Fin nl,
        (Fin.addCases (motive := fun _ => ℤ) (fun _ => 1) (fun k => -(fl k))
            (Fin.natAdd (genus X) k)) •
          (Finsupp.single ((Fin.addCases (motive := fun _ => ℝ → X) σ lam
              (Fin.natAdd (genus X) k)) 1) (1 : ℤ)
            - Finsupp.single ((Fin.addCases (motive := fun _ => ℝ → X) σ lam
              (Fin.natAdd (genus X) k)) 0) 1)
        = 0 := by
      intro k
      rw [Fin.addCases_right, Fin.addCases_right, (hlam k).closed, sub_self, smul_zero]
    rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_congr rfl fun k _ => hR k,
      Finset.sum_const_zero, add_zero]
  -- the segment path values: `∫_{σ j} ωᵢ = Φ̃_{a j, i}(z j)` (the Jacobi-map summand).
  have hseg_val : ∀ (j : Fin (genus X)) (i : Fin (genus X)),
      pathPrimValue (periodBasisForm X i) (σ j) (hσ_cont j)
        = localLiftChart (X := X) (a j) 0 i (z j) := by
    intro j i
    -- an analytic primitive of the chart coefficient on the ball.
    have hdiff : DifferentiableOn ℂ (chartFormCoeff (X := X) (a j) i)
        (ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)) :=
      (chartFormCoeff_differentiableOn (a j) i).mono (hball_tgt j)
    obtain ⟨g, hg_deriv, _⟩ := exists_analytic_primitive_on_ball hdiff
    -- the single-block primitive chain.
    set C : PrimitiveChain (periodBasisForm X i) (σ j) := {
      n := 1
      t := fun k => if k = 0 then 0 else 1
      t_zero := rfl
      t_stab := fun k hk => by
        rw [if_neg]
        omega
      mono := by
        intro p q hpq
        show (if p = 0 then (0 : ℝ) else 1) ≤ (if q = 0 then (0 : ℝ) else 1)
        by_cases hp : p = 0
        · by_cases hq : q = 0
          · rw [hp, hq]
          · rw [hp, if_pos rfl, if_neg hq]
            norm_num
        · have hq : q ≠ 0 := by omega
          rw [if_neg hp, if_neg hq]
      U := fun _ => (chartAt (H := ℂ) (a j)).source ∩
        (chartAt (H := ℂ) (a j)) ⁻¹' ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)
      F := fun _ => g ∘ (chartAt (H := ℂ) (a j))
      isOpen := fun _ => (chartAt (H := ℂ) (a j)).isOpen_inter_preimage isOpen_ball
      prim := fun _ => isLocalPrimitiveOn_comp_chart (hball_tgt j) (fun w hw =>
        hg_deriv w hw)
      covers := by
        intro i' s hs
        have hs01 : s ∈ Icc (0 : ℝ) 1 := by
          constructor
          · refine le_trans ?_ hs.1
            by_cases h : i' = 0 <;> simp [h]
          · refine le_trans hs.2 ?_
            by_cases h : i' + 1 = 0 <;> simp [h]
        have hmem := hseg_ball j s hs01
        refine ⟨(chartAt (H := ℂ) (a j)).map_target (hball_tgt j hmem), ?_⟩
        show (chartAt (H := ℂ) (a j)) (σ j s) ∈ ball _ _
        rw [hσ]
        rw [(chartAt (H := ℂ) (a j)).right_inv (hball_tgt j hmem)]
        exact hmem }
    rw [pathPrimValue_eq (periodBasisForm X i) (hσ_cont j) C]
    -- the chain value is the primitive difference.
    have hval : C.value = g (z j) - g ((chartAt (H := ℂ) (a j)) (a j)) := by
      rw [PrimitiveChain.value]
      rw [show C.n = 1 from rfl, Finset.sum_range_one]
      have ht0 : C.t 0 = 0 := rfl
      have ht1 : C.t 1 = 1 := rfl
      rw [ht0, ht1]
      show (g ∘ (chartAt (H := ℂ) (a j))) (σ j 1) - (g ∘ (chartAt (H := ℂ) (a j))) (σ j 0)
        = _
      rw [hσ1 j, hσ0 j]
      show g ((chartAt (H := ℂ) (a j)) (x j)) - g ((chartAt (H := ℂ) (a j)) (a j)) = _
      rw [hchart_x j]
    rw [hval]
    -- ... which is the straight-segment integral `Φ̃` (the FTC on the ball).
    have hseg : Icc (0 : ℝ) 1 ⊆ {s : ℝ | (chartAt (H := ℂ) (a j)) (a j)
        + (s : ℂ) * (z j - (chartAt (H := ℂ) (a j)) (a j))
          ∈ ball ((chartAt (H := ℂ) (a j)) (a j)) (r j)} :=
      fun s hs => hseg_ball j s hs
    have hFTC := segmentIntegral_eq_primitive_diff
      (c := (chartAt (H := ℂ) (a j)) (a j)) (r := r j)
      (a := (chartAt (H := ℂ) (a j)) (a j)) (b := z j)
      (f := chartFormCoeff (X := X) (a j) i) (g := g)
      (mem_ball_self (hrpos j)) (hz_ball j) hseg hdiff.continuousOn hg_deriv
    rw [localLiftChart, hFTC]
    show g (z j) - g _ = (0 : Fin (genus X) → ℂ) i + (g (z j) - g _)
    rw [Pi.zero_apply, zero_add]
  -- the chain has vanishing basis periods.
  have hper : ∀ i : Fin (genus X), c.period (periodBasisForm X i) = 0 := by
    intro i
    rw [OneChain.period]
    show (∑ m : Fin (genus X + nl), _) = 0
    rw [Fin.sum_univ_add]
    have hL : ∀ j : Fin (genus X),
        (Fin.addCases (motive := fun _ => ℤ) (fun _ => 1) (fun k => -(fl k))
            (Fin.castAdd nl j)) •
          pathPrimValue (periodBasisForm X i)
            (Fin.addCases (motive := fun _ => ℝ → X) σ lam (Fin.castAdd nl j))
            (c.cont (Fin.castAdd nl j))
        = localLiftChart (X := X) (a j) 0 i (z j) := by
      intro j
      have hcurve : (Fin.addCases (motive := fun _ => ℝ → X) σ lam (Fin.castAdd nl j))
          = σ j := Fin.addCases_left j
      rw [Fin.addCases_left, one_smul,
        pathPrimValue_congr_curve hcurve (c.cont (Fin.castAdd nl j))]
      exact hseg_val j i
    have hR : ∀ k : Fin nl,
        (Fin.addCases (motive := fun _ => ℤ) (fun _ => 1) (fun k => -(fl k))
            (Fin.natAdd (genus X) k)) •
          pathPrimValue (periodBasisForm X i)
            (Fin.addCases (motive := fun _ => ℝ → X) σ lam (Fin.natAdd (genus X) k))
            (c.cont (Fin.natAdd (genus X) k))
        = -(fl k • periodVec (lam k) i) := by
      intro k
      have hcurve : (Fin.addCases (motive := fun _ => ℝ → X) σ lam (Fin.natAdd (genus X) k))
          = lam k := Fin.addCases_right k
      rw [Fin.addCases_right,
        pathPrimValue_congr_curve hcurve (c.cont (Fin.natAdd (genus X) k)),
        (hlam k).pathPrimValue_eq_periodVec i _, neg_smul]
    rw [Finset.sum_congr rfl fun j _ => hL j, Finset.sum_congr rfl fun k _ => hR k]
    -- `∑ⱼ Φ̃ⱼ(z j) = (jacobiMap a z) i = t i` and the loop part is `−t i`.
    have hjac : (∑ j, localLiftChart (X := X) (a j) 0 i (z j)) = t i := by
      rw [show (∑ j, localLiftChart (X := X) (a j) 0 i (z j)) = jacobiMap a z i from rfl,
        hzt]
    have hloop : (∑ k, fl k • periodVec (lam k) i) = t i := by
      have hc : (∑ k, fl k • (gl k : Fin (genus X) → ℂ)) i = t i := congrFun hsum i
      simp only [Finset.sum_apply, Pi.smul_apply] at hc
      rw [← hc]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hval k]
    rw [hjac, show (∑ k, -(fl k • periodVec (lam k) i))
        = -∑ k, fl k • periodVec (lam k) i from
      Finset.sum_neg_distrib (fun k => fl k • periodVec (lam k) i), hloop]
    ring
  -- THE ENGINE: a meromorphic `f` with `div f = ∑ⱼ(xⱼ − aⱼ)` and its local models.
  obtain ⟨f, hdiv, hmodel⟩ := exists_meromorphic_of_oneChain c hper
  rw [hbd] at hdiv
  set D : Divisor X := ∑ j, (Finsupp.single (x j) (1 : ℤ) - Finsupp.single (a j) 1)
    with hD
  -- divisor coefficient bookkeeping.
  have hD_apply : ∀ y : X, D y = ∑ j, ((if x j = y then (1 : ℤ) else 0)
      - (if a j = y then 1 else 0)) := by
    intro y
    rw [hD, Finsupp.finset_sum_apply]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finsupp.sub_apply, Finsupp.single_apply, Finsupp.single_apply]
  have hxO : ∀ j, x j ∈ O j := fun j => (hx_mem j).1
  have hxne : ∀ j k, j ≠ k → x j ≠ x k := by
    intro j k hjk h
    exact (hOdisj j k hjk).ne_of_mem (hxO j) (hxO k) h
  have hxa_ne : ∀ j k, j ≠ k → x j ≠ a k := by
    intro j k hjk h
    exact (hOdisj j k hjk).ne_of_mem (hxO j) (haO k) h
  have hane : ∀ j k, j ≠ k → a j ≠ a k := fun j k hjk h => hjk (hainj h)
  -- `D (a j) = -1` when `x j ≠ a j`, `0` otherwise; `D` vanishes off `{a, x}`.
  have hD_a : ∀ j, x j ≠ a j → D (a j) = -1 := by
    intro j hxj
    rw [hD_apply]
    rw [Finset.sum_eq_single j]
    · rw [if_neg hxj, if_pos rfl]
      norm_num
    · intro k _ hkj
      rw [if_neg (fun h => hxa_ne k j hkj h), if_neg (fun h => hane k j hkj h)]
      ring
    · intro h
      exact absurd (Finset.mem_univ j) h
  -- the residue vector.
  set cvec : Fin (genus X) → ℂ := fun j =>
    if hj : x j = a j then 0 else (hmodel (a j)).choose ((chartAt (H := ℂ) (a j)) (a j))
    with hcvec
  -- the pole set.
  set poles : Finset X := Finset.univ.image a ∪ Finset.univ.image x with hpoles
  -- analyticity off the divisor support (from the local model with exponent `≥ 0`).
  have hread_model : ∀ y : X, (f.toFun ∘ (chartAt (H := ℂ) y).symm)
      =ᶠ[𝓝 ((chartAt (H := ℂ) y) y)]
      fun w => (hmodel y).choose w * (w - (chartAt (H := ℂ) y) y) ^ (D y) := by
    intro y
    have h := (hmodel y).choose_spec.2.2
    have hDb : c.boundary y = D y := by rw [hbd]
    rw [← hDb]
    exact h
  have hgood : ∀ y : X, 0 ≤ D y →
      AnalyticAt ℂ (fun w => f.toFun ((chartAt (H := ℂ) y).symm w))
        ((chartAt (H := ℂ) y) y) := by
    intro y hDy
    have hgerm := hread_model y
    rw [analyticAt_congr (by exact hgerm)]
    have hzpow : AnalyticAt ℂ (fun w => (w - (chartAt (H := ℂ) y) y) ^ (D y))
        ((chartAt (H := ℂ) y) y) := by
      rw [show (fun w : ℂ => (w - (chartAt (H := ℂ) y) y) ^ (D y))
          = fun w => (w - (chartAt (H := ℂ) y) y) ^ (D y).toNat from by
        funext w
        rw [← zpow_natCast, Int.toNat_of_nonneg hDy]]
      exact (analyticAt_id.sub analyticAt_const).pow _
    exact ((hmodel y).choose_spec.1).mul hzpow
  -- the divisor vanishes off the poles.
  have hD_off : ∀ y : X, y ∉ poles → D y = 0 := by
    intro y hy
    rw [hD_apply]
    refine Finset.sum_eq_zero fun j _ => ?_
    have hyx : x j ≠ y := fun h => hy (by
      rw [hpoles]
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩))
    have hya : a j ≠ y := fun h => hy (by
      rw [hpoles]
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩))
    rw [if_neg hyx, if_neg hya]
    ring
  -- THE RESIDUE THEOREM on each `f·ωᵢ`.
  have hres : ∀ i : Fin (genus X),
      ∑ y ∈ poles, formFnResidue (periodBasisForm X i) f.toFun y = 0 := by
    intro i
    refine SerreResidueTheorem.residueTheorem_unconditional (periodBasisForm X i) f poles
      (fun y hy => hgood y (le_of_eq (hD_off y hy).symm))
  -- the residue at `a j` is `cvec j · A i j`; elsewhere it vanishes.
  have hres_a : ∀ (i j : Fin (genus X)),
      formFnResidue (periodBasisForm X i) f.toFun (a j)
        = cvec j * jacobiEvalMatrix (X := X) a i j := by
    intro i j
    by_cases hxj : x j = a j
    · -- no pole: `D (a j) = 0`, analytic read, residue `0`.
      have hDaj : D (a j) = 0 := by
        rw [hD_apply]
        rw [Finset.sum_eq_single j]
        · rw [if_pos hxj, if_pos rfl]
          norm_num
        · intro k _ hkj
          rw [if_neg (fun h => hxa_ne k j hkj h), if_neg (fun h => hane k j hkj h)]
          ring
        · intro h
          exact absurd (Finset.mem_univ j) h
      rw [show cvec j = 0 from by rw [hcvec]; exact dif_pos hxj, zero_mul]
      exact formFnResidue_eq_zero_of_analyticAt _ _ _
        (hgood (a j) (le_of_eq hDaj.symm))
    · -- simple pole: residue `H(w₀)·coeff(w₀)`.
      have hDaj : D (a j) = -1 := hD_a j hxj
      have hgermf := hread_model (a j)
      rw [hDaj] at hgermf
      have hH := (hmodel (a j)).choose_spec.1
      -- the integrand is `Φ·(w−w₀)⁻¹` with `Φ = coeffAt·H` analytic.
      rw [formFnResidue]
      have hint_germ : (fun w => coeffAt (periodBasisForm X i) (a j) w
            * f.toFun ((chartAt ℂ (a j)).symm w))
          =ᶠ[𝓝[≠] ((chartAt (H := ℂ) (a j)) (a j))]
          fun w => (coeffAt (periodBasisForm X i) (a j) w * (hmodel (a j)).choose w)
            * (w - (chartAt (H := ℂ) (a j)) (a j))⁻¹ := by
        filter_upwards [(hgermf.filter_mono nhdsWithin_le_nhds :)] with w hw
        rw [show f.toFun ((chartAt ℂ (a j)).symm w)
            = (f.toFun ∘ (chartAt (H := ℂ) (a j)).symm) w from rfl, hw]
        rw [zpow_neg_one]
        ring
      have hΦ : AnalyticAt ℂ (fun w => coeffAt (periodBasisForm X i) (a j) w
            * (hmodel (a j)).choose w) ((chartAt (H := ℂ) (a j)) (a j)) :=
        (coeffAt_analyticAt (periodBasisForm X i) (a j)
          ((chartAt (H := ℂ) (a j)).map_source (mem_chart_source ℂ (a j)))).mul hH
      rw [Dolbeault.resAt_congr hint_germ, resAt_analyticAt_mul_sub_inv hΦ]
      rw [coeffAt_chartCenter]
      rw [show cvec j = (hmodel (a j)).choose ((chartAt (H := ℂ) (a j)) (a j)) from by
        rw [hcvec]; exact dif_neg hxj]
      rw [jacobiEvalMatrix_apply]
      ring
  have hres_x : ∀ (i : Fin (genus X)) (y : X), y ∈ poles → y ∉ Finset.univ.image a →
      formFnResidue (periodBasisForm X i) f.toFun y = 0 := by
    intro i y hy hya
    -- `y = x j` for some `j` with `x j` distinct from all `a k`: `D y = 1 ≥ 0`.
    have hDy : 0 ≤ D y := by
      rw [hD_apply]
      refine Finset.sum_nonneg fun j _ => ?_
      have hyaj : a j ≠ y := fun h => hya (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, h⟩)
      rw [if_neg hyaj]
      by_cases h : x j = y <;> simp [h]
    exact formFnResidue_eq_zero_of_analyticAt _ _ _ (hgood y hDy)
  -- assemble: `A.mulVec cvec = 0`.
  have hmul : ∀ i : Fin (genus X),
      ∑ j, jacobiEvalMatrix (X := X) a i j * cvec j = 0 := by
    intro i
    have h := hres i
    rw [hpoles, Finset.sum_union_eq_left (fun y hy hyn => hres_x i y
      (by rw [hpoles]; exact Finset.mem_union_right _ hy) hyn)] at h
    rw [Finset.sum_image (fun j _ k _ h => hainj h)] at h
    rw [← h]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hres_a i j]
    ring
  -- contradiction with `det A ≠ 0`.
  have hcvec0 : cvec ≠ 0 := by
    intro h
    have hj : cvec j₀ = 0 := by rw [h]; rfl
    rw [hcvec] at hj
    simp only [dif_neg (hxa j₀ hj₀)] at hj
    exact (hmodel (a j₀)).choose_spec.2.1 hj
  refine hdet ?_
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨cvec, hcvec0, ?_⟩
  funext i
  rw [Matrix.mulVec, dotProduct]
  exact hmul i

end Jacobians
