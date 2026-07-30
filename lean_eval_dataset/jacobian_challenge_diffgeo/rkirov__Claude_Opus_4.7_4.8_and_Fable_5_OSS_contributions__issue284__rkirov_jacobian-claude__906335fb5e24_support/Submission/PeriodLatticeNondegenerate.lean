/-
Copyright (c) 2026 Rado Kirov. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Rado Kirov

# Forster 21.4(c) — non-degeneracy: the period lattice spans `ℂ^g` over `ℝ`

If a nonzero real-linear functional vanished on `truePeriodLattice X`, writing it as
`v ↦ Re (∑ⱼ dⱼ·vⱼ)` would give `d ∈ ℂ^g ∖ {0}` with `Re ∫_γ ∑ dⱼωⱼ = 0` for every closed smooth
loop `γ`.  Then `u(x) := Re (∑ⱼ dⱼ·periodVec (smoothPath x₀ x)ⱼ)` is well-defined up to nothing
(a definite function) and **locally the real part of an analytic function** — near `Q₀` it agrees
with `Re H_{Q₀} ∘ chart` for `H_{Q₀}(z) = ∑ⱼ dⱼ·Φ̃_{Q₀,j}(z)` (the chart primitives), because two
smooth paths with the same endpoints have lattice-equal periods
(`localLift_quotient_eq_ofCurve_eventually`).  At a maximum of `u` (compactness) the open-mapping
dichotomy forces `H` locally constant, so `{u = max}` is clopen, `u` is constant, every chart
derivative `∑ⱼ dⱼ·ω_j`-coefficient vanishes, and `∑ dⱼωⱼ = 0` — contradicting `d ≠ 0`.

No harmonic theory, no surface integration: the only analysis is Mathlib's planar open-mapping
dichotomy (`AnalyticAt.eventually_constant_or_nhds_le_map_nhds`).

Reference: Forster, *Lectures on Riemann Surfaces* (GTM 81), 21.4(c) (pp. 169–170) and 19.8.
-/
import Submission.JacobiLocalMap
import Mathlib.Analysis.Complex.OpenMapping

open scoped Manifold ContDiff Topology
open Jacobians.OfCurveSkeleton

set_option linter.unusedSectionVars false

namespace Jacobians

variable {X : Type*} [TopologicalSpace X] [T2Space X] [CompactSpace X]
    [ConnectedSpace X] [Nonempty X] [ChartedSpace ℂ X] [IsManifold 𝓘(ℂ) ω X]

/-! ### The planar maximum-principle atom -/

/-- **Local maximum of `Re` forces local constancy** (the open-mapping dichotomy): an analytic
function whose real part has a local maximum at `z₀` is locally constant at `z₀`. -/
theorem eventually_const_of_re_le {H : ℂ → ℂ} {z₀ : ℂ} (hH : AnalyticAt ℂ H z₀)
    (hmax : ∀ᶠ z in 𝓝 z₀, (H z).re ≤ (H z₀).re) :
    ∀ᶠ z in 𝓝 z₀, H z = H z₀ := by
  rcases hH.eventually_constant_or_nhds_le_map_nhds with hconst | hopen
  · exact hconst
  · exfalso
    -- the closed half-plane `{Re ≤ Re (H z₀)}` would be a neighbourhood of its boundary point.
    have hV : {w : ℂ | w.re ≤ (H z₀).re} ∈ 𝓝 (H z₀) := hopen (by
      rw [Filter.mem_map]
      exact hmax.mono fun z hz => hz)
    obtain ⟨ε, hε, hball⟩ := Metric.mem_nhds_iff.mp hV
    have hmem : H z₀ + (ε / 2 : ℝ) ∈ Metric.ball (H z₀) ε := by
      rw [Metric.mem_ball, dist_eq_norm]
      simp only [add_sub_cancel_left]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
      linarith
    have := hball hmem
    rw [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re] at this
    linarith

/-! ### The real-functional representation `λ = Re ⟨d, ·⟩` -/

/-- Every `ℝ`-linear functional on `ℂ^g` is `v ↦ Re (∑ⱼ dⱼ·vⱼ)` for some `d : ℂ^g`
(`dⱼ = λ(eⱼ) − λ(i·eⱼ)·i`). -/
theorem exists_re_dotProduct_repr {n : ℕ} (l : (Fin n → ℂ) →ₗ[ℝ] ℝ) :
    ∃ d : Fin n → ℂ, ∀ v : Fin n → ℂ, (∑ j, d j * v j).re = l v := by
  classical
  set e : Fin n → (Fin n → ℂ) := fun j => Pi.single j (1 : ℂ) with he
  set f : Fin n → (Fin n → ℂ) := fun j => Pi.single j Complex.I with hf
  refine ⟨fun j => (l (e j) : ℂ) - (l (f j) : ℂ) * Complex.I, fun v => ?_⟩
  -- decompose `v = ∑ⱼ single j (v j)` and each `single j z` over the real frame `{eⱼ, i·eⱼ}`.
  have hdecomp : ∀ (j : Fin n) (z : ℂ),
      (Pi.single j z : Fin n → ℂ) = z.re • e j + z.im • f j := by
    intro j z
    rw [he, hf]
    funext k
    rcases eq_or_ne k j with rfl | hk
    · show (Pi.single k z : Fin n → ℂ) k
        = (z.re • (Pi.single k (1 : ℂ) : Fin n → ℂ) + z.im • (Pi.single k Complex.I : Fin n → ℂ)) k
      simp only [Pi.single_eq_same, Pi.add_apply, Pi.smul_apply, Complex.real_smul, mul_one]
      exact (Complex.re_add_im z).symm
    · show (Pi.single j z : Fin n → ℂ) k
        = (z.re • (Pi.single j (1 : ℂ) : Fin n → ℂ) + z.im • (Pi.single j Complex.I : Fin n → ℂ)) k
      simp only [Pi.single_eq_of_ne hk, Pi.add_apply, Pi.smul_apply, Complex.real_smul,
        mul_zero, smul_zero, add_zero]
  have hv : v = ∑ j, (Pi.single j (v j) : Fin n → ℂ) :=
    (Finset.univ_sum_single v).symm
  calc (∑ j, ((l (e j) : ℂ) - (l (f j) : ℂ) * Complex.I) * v j).re
      = ∑ j, (((l (e j) : ℂ) - (l (f j) : ℂ) * Complex.I) * v j).re := by
        rw [Complex.re_sum]
    _ = ∑ j, ((v j).re * l (e j) + (v j).im * l (f j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.mul_im,
          Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
        ring
    _ = ∑ j, l (Pi.single j (v j)) := by
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [hdecomp j (v j), map_add, map_smul, map_smul, smul_eq_mul, smul_eq_mul]
    _ = l v := by rw [← map_sum, ← hv]

/-! ### The headline: `span ℝ (truePeriodLattice) = ⊤` -/

set_option maxHeartbeats 1000000 in
/-- **Forster 21.4(c): the period lattice is non-degenerate** — its real span is all of `ℂ^g`.
A nonzero killing functional `Re ⟨d, ·⟩` would make `u = Re ⟨d, periodVec (smoothPath x₀ ·)⟩` a
global continuous function that is locally the real part of an analytic chart primitive; the
maximum principle (open-mapping dichotomy) forces `u` constant, all chart coefficients of
`∑ dⱼωⱼ` vanish, and `d = 0` — contradiction. -/
theorem span_real_truePeriodLattice_eq_top :
    Submodule.span ℝ ((truePeriodLattice X : Set (Fin (genus X) → ℂ))) = ⊤ := by
  classical
  by_contra hne
  set p : Submodule ℝ (Fin (genus X) → ℂ) :=
    Submodule.span ℝ ((truePeriodLattice X : Set (Fin (genus X) → ℂ))) with hp
  -- a vector outside the span and a functional separating it.
  obtain ⟨x, hx⟩ : ∃ x, x ∉ p := by
    by_contra hcon
    push Not at hcon
    exact hne (Submodule.eq_top_iff'.mpr hcon)
  have hxq : p.mkQ x ≠ 0 := fun h0 => hx ((Submodule.Quotient.mk_eq_zero p).mp h0)
  obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual ℝ ((Fin (genus X) → ℂ) ⧸ p), φ (p.mkQ x) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hxq ((Module.forall_dual_apply_eq_zero_iff ℝ _).mp hcon)
  obtain ⟨d, hd⟩ := exists_re_dotProduct_repr (φ.comp p.mkQ)
  -- the concrete killing functional.
  set Λ : (Fin (genus X) → ℂ) → ℝ := fun v => (∑ j, d j * v j).re with hΛ
  have hΛx : Λ x ≠ 0 := by
    rw [hΛ]
    show (∑ j, d j * x j).re ≠ 0
    rw [hd x]
    exact hφ
  have hΛadd : ∀ a b, Λ (a + b) = Λ a + Λ b := by
    intro a b
    show (∑ j, d j * (a j + b j)).re = (∑ j, d j * a j).re + (∑ j, d j * b j).re
    rw [← Complex.add_re, ← Finset.sum_add_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => by ring
  have hΛneg : ∀ a, Λ (-a) = -Λ a := by
    intro a
    show (∑ j, d j * (-a) j).re = -(∑ j, d j * a j).re
    rw [← Complex.neg_re, ← Finset.sum_neg_distrib]
    congr 1
    exact Finset.sum_congr rfl fun j _ => mul_neg _ _
  have hkill : ∀ v ∈ (truePeriodLattice X).toAddSubgroup, Λ v = 0 := by
    intro v hv
    have hvp : v ∈ p := Submodule.subset_span hv
    show (∑ j, d j * v j).re = 0
    rw [hd v]
    show φ (p.mkQ v) = 0
    have h0 : p.mkQ v = 0 := by
      rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
      exact hvp
    rw [h0, map_zero]
  -- the global potential and its chart-local analytic models.
  obtain ⟨x₀⟩ := (inferInstance : Nonempty X)
  set u : X → ℝ := fun Q => Λ (periodVec (smoothPath x₀ Q)) with hu
  set Hf : X → ℂ → ℂ :=
    fun Q₀ z => ∑ j, d j * localLiftChart (X := X) Q₀ (periodVec (smoothPath x₀ Q₀)) j z
    with hHf
  -- the local identity `u = Re ∘ H_{Q₀} ∘ chart` near `Q₀`.
  have hloc : ∀ Q₀ : X, ∀ᶠ Q in 𝓝 Q₀,
      u Q = (Hf Q₀ ((chartAt (H := ℂ) Q₀) Q)).re := by
    intro Q₀
    filter_upwards [localLift_quotient_eq_ofCurve_eventually x₀ Q₀] with Q hQ
    have hmem := (QuotientAddGroup.eq (s := (truePeriodLattice X).toAddSubgroup)).mp hQ
    have hzero := hkill _ hmem
    rw [hΛadd, hΛneg] at hzero
    have hΛeq : Λ (periodVec (smoothPath x₀ Q))
        = Λ (localLift (X := X) Q₀ (periodVec (smoothPath x₀ Q₀)) Q) := by linarith
    show Λ (periodVec (smoothPath x₀ Q)) = _
    rw [hΛeq]
    rfl
  -- analyticity of each chart model at its center.
  have hHan : ∀ Q₀ : X, AnalyticAt ℂ (Hf Q₀) ((chartAt (H := ℂ) Q₀) Q₀) := by
    intro Q₀
    have h := Finset.analyticAt_fun_sum (𝕜 := ℂ) (Finset.univ : Finset (Fin (genus X)))
      (f := fun j (z : ℂ) =>
        d j * localLiftChart (X := X) Q₀ (periodVec (smoothPath x₀ Q₀)) j z)
      (fun j _ => analyticAt_const.mul (localLiftChart_analyticAt Q₀ _ j))
    exact h
  -- continuity of `u` (via the local models).
  have hΛcont : Continuous Λ := by
    rw [hΛ]
    exact Complex.continuous_re.comp
      (continuous_finset_sum _ fun j _ => continuous_const.mul (continuous_apply j))
  have hHcont : ∀ Q₀ : X, ContinuousAt (fun Q => (Hf Q₀ ((chartAt (H := ℂ) Q₀) Q)).re) Q₀ := by
    intro Q₀
    have h1 : ContinuousAt (chartAt (H := ℂ) Q₀) Q₀ :=
      (chartAt (H := ℂ) Q₀).continuousAt (mem_chart_source ℂ Q₀)
    exact (Complex.continuous_re.continuousAt).comp ((hHan Q₀).continuousAt.comp h1)
  have hucont : Continuous u := by
    rw [continuous_iff_continuousAt]
    intro Q₀
    have h : u =ᶠ[𝓝 Q₀] fun Q => (Hf Q₀ ((chartAt (H := ℂ) Q₀) Q)).re := hloc Q₀
    exact (hHcont Q₀).congr h.symm
  -- the maximum and the clopen level set.
  obtain ⟨y₀, -, hy₀⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hucont.continuousOn
  have hy₀max : ∀ Q : X, u Q ≤ u y₀ := fun Q => hy₀ (Set.mem_univ Q)
  -- the key step: at any point where `u` attains the maximum, the chart model is locally const.
  have hkey : ∀ Q₀ : X, u Q₀ = u y₀ →
      ∀ᶠ z in 𝓝 ((chartAt (H := ℂ) Q₀) Q₀),
        Hf Q₀ z = Hf Q₀ ((chartAt (H := ℂ) Q₀) Q₀) := by
    intro Q₀ hQ₀
    refine eventually_const_of_re_le (hHan Q₀) ?_
    -- transfer the max property through `chart.symm`.
    set e := chartAt (H := ℂ) Q₀ with he
    have hz₀tgt : e Q₀ ∈ e.target := e.map_source (mem_chart_source ℂ Q₀)
    have hsymm : Filter.Tendsto e.symm (𝓝 (e Q₀)) (𝓝 Q₀) := by
      have h : Filter.Tendsto e.symm (𝓝 (e Q₀)) (𝓝 (e.symm (e Q₀))) :=
        e.continuousAt_symm hz₀tgt
      rwa [e.left_inv (mem_chart_source ℂ Q₀)] at h
    have hself : u Q₀ = (Hf Q₀ (e Q₀)).re := by
      have h : ∀ᶠ Q in 𝓝 Q₀, u Q = (Hf Q₀ ((chartAt (H := ℂ) Q₀) Q)).re := hloc Q₀
      exact h.self_of_nhds
    filter_upwards [e.open_target.mem_nhds hz₀tgt, hsymm.eventually (hloc Q₀)] with z hztgt hzloc
    have hzz : e (e.symm z) = z := e.right_inv hztgt
    rw [hzz] at hzloc
    calc (Hf Q₀ z).re = u (e.symm z) := hzloc.symm
      _ ≤ u y₀ := hy₀max _
      _ = u Q₀ := hQ₀.symm
      _ = (Hf Q₀ (e Q₀)).re := hself
  -- the level set `{u = max}` is clopen and nonempty, hence everything.
  have hSopen : IsOpen {Q : X | u Q = u y₀} := by
    rw [isOpen_iff_mem_nhds]
    intro Q₀ hQ₀
    set e := chartAt (H := ℂ) Q₀ with he
    have hchart : Filter.Tendsto e (𝓝 Q₀) (𝓝 (e Q₀)) :=
      (e.continuousAt (mem_chart_source ℂ Q₀)).tendsto
    have hself : u Q₀ = (Hf Q₀ (e Q₀)).re := by
      have h : ∀ᶠ Q in 𝓝 Q₀, u Q = (Hf Q₀ ((chartAt (H := ℂ) Q₀) Q)).re := hloc Q₀
      exact h.self_of_nhds
    filter_upwards [hloc Q₀, hchart.eventually (hkey Q₀ hQ₀)] with Q hQloc hQconst
    show u Q = u y₀
    rw [hQloc, hQconst, ← hself, hQ₀]
  have hSuniv : {Q : X | u Q = u y₀} = Set.univ :=
    IsClopen.eq_univ ⟨isClosed_eq hucont continuous_const, hSopen⟩ ⟨y₀, rfl⟩
  -- every point is a maximum point, so every chart derivative vanishes.
  have hcoeff : ∀ Q₀ : X, ∑ j, d j * formEvalSelf Q₀ (periodBasisForm X j) = 0 := by
    intro Q₀
    have hQ₀ : Q₀ ∈ {Q : X | u Q = u y₀} := by
      rw [hSuniv]
      trivial
    have hconst := hkey Q₀ hQ₀
    have hderiv : HasDerivAt (Hf Q₀)
        (∑ j, d j * chartFormCoeff (X := X) Q₀ j ((chartAt (H := ℂ) Q₀) Q₀))
        ((chartAt (H := ℂ) Q₀) Q₀) := by
      have h := HasDerivAt.sum (u := (Finset.univ : Finset (Fin (genus X))))
        (A := fun j (z : ℂ) =>
          d j * localLiftChart (X := X) Q₀ (periodVec (smoothPath x₀ Q₀)) j z)
        (A' := fun j => d j * chartFormCoeff (X := X) Q₀ j ((chartAt (H := ℂ) Q₀) Q₀))
        (fun j _ =>
          (localLiftChart_hasDerivAt_center Q₀ (periodVec (smoothPath x₀ Q₀)) j).const_mul (d j))
      have hfun : (∑ j : Fin (genus X), fun z : ℂ =>
          d j * localLiftChart (X := X) Q₀ (periodVec (smoothPath x₀ Q₀)) j z) = Hf Q₀ := by
        funext z
        rw [Finset.sum_apply]
      rwa [hfun] at h
    have hzero : deriv (Hf Q₀) ((chartAt (H := ℂ) Q₀) Q₀) = 0 := by
      have hcongr : deriv (Hf Q₀) ((chartAt (H := ℂ) Q₀) Q₀)
          = deriv (fun _ : ℂ => Hf Q₀ ((chartAt (H := ℂ) Q₀) Q₀))
            ((chartAt (H := ℂ) Q₀) Q₀) := Filter.EventuallyEq.deriv_eq hconst
      rw [hcongr, deriv_const]
    have hsum := hderiv.deriv
    rw [hzero] at hsum
    have hconv : ∑ j, d j * formEvalSelf Q₀ (periodBasisForm X j)
        = ∑ j, d j * chartFormCoeff (X := X) Q₀ j ((chartAt (H := ℂ) Q₀) Q₀) :=
      Finset.sum_congr rfl fun j _ => by rw [chartFormCoeff_center, formEvalSelf_apply]
    rw [hconv, ← hsum]
  -- the coefficient vector is the form `∑ dⱼωⱼ`, which therefore vanishes identically.
  have hform : ∀ Q₀ : X, formEvalSelf Q₀ (ambientIso X d) = 0 := by
    intro Q₀
    have hsum : ambientIso X d = ∑ j, d j • periodBasisForm X j := by
      have hv' : (∑ i, d i • Pi.basisFun ℂ (Fin (genus X)) i) = d := by
        ext k
        simp [Pi.basisFun_apply, Pi.single_apply, Finset.sum_ite_eq]
      calc ambientIso X d = ambientIso X (∑ i, d i • Pi.basisFun ℂ (Fin (genus X)) i) := by
            rw [hv']
        _ = ∑ i, d i • periodBasisForm X i := by
            rw [map_sum]
            exact Finset.sum_congr rfl fun i _ => by rw [map_smul]; rfl
    rw [hsum, map_sum]
    rw [show (∑ j, formEvalSelf Q₀ (d j • periodBasisForm X j))
        = ∑ j, d j * formEvalSelf Q₀ (periodBasisForm X j) from
      Finset.sum_congr rfl fun j _ => by rw [map_smul, smul_eq_mul]]
    exact hcoeff Q₀
  have hα : ambientIso X d = 0 := by
    by_contra hαne
    obtain ⟨a, ha⟩ := Jacobians.Dolbeault.exists_localRep_self_ne_zero (ambientIso X d) hαne
    exact ha (hform a)
  have hd0 : d = 0 := (ambientIso X).map_eq_zero_iff.mp hα
  -- contradiction with `Λ x ≠ 0`.
  refine hΛx ?_
  rw [hΛ]
  show (∑ j, d j * x j).re = 0
  rw [hd0]
  simp

end Jacobians
