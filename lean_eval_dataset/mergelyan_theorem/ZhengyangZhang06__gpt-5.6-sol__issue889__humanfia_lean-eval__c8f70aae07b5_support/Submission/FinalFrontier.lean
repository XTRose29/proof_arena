import Submission.ScaleControlledAggregate
import Submission.FrontierCover
import Submission.SmoothCore

open Function Set
open scoped ContDiff Manifold Topology

noncomputable section

namespace Submission.Helpers

/-- Equal-radius Besicovitch selection with both the tight source cover and
the scale-independent active-bump bound exposed. -/
theorem exists_tight_uniform_besicovitch_cover_of_no_satelliteConfig
    (S : Set ℂ) (hS : IsCompact S)
    (r : ℝ) (hr : 0 < r)
    (N : ℕ) (τ : ℝ) (hτ : 1 < τ)
    (hN : IsEmpty (Besicovitch.SatelliteConfig ℂ N τ)) :
    ∃ (A : Fin N → Set S)
        (t : Finset (Σ k : Fin N, {z : S // z ∈ A k})),
      (∀ k,
        (A k).PairwiseDisjoint
          (fun z ↦ Metric.closedBall (z : ℂ) r)) ∧
      S ⊆ ⋃ i : t,
        Metric.ball (i.1.2.1 : ℂ) r ∧
      ∀ z : ℂ,
        (activeUniformBumps
          (fun i : t ↦ (i.1.2.1 : ℂ)) r hr z).card ≤
            N * 25 := by
  obtain ⟨A, t, hAdisjoint, hcover⟩ :=
    exists_finite_besicovitch_ball_cover_of_no_satelliteConfig
      S hS (fun _ ↦ r) r (fun _ ↦ hr)
        (fun _ ↦ le_rfl) N τ hτ hN
  refine ⟨A, t, hAdisjoint, ?_, ?_⟩
  · intro z hz
    rcases mem_iUnion.mp (hcover hz) with ⟨u, hu⟩
    rcases mem_iUnion.mp hu with ⟨hut, hzu⟩
    apply mem_iUnion.mpr
    exact ⟨⟨u, hut⟩, hzu⟩
  · have hindexDisjoint :
        ∀ k,
          Set.Pairwise
            {i : t | i.1.1 = k}
            (Disjoint on fun i ↦
              Metric.closedBall (i.1.2.1 : ℂ) r) := by
      intro k i hi j hj hij
      rcases i with ⟨⟨ki, xi⟩, hit⟩
      rcases j with ⟨⟨kj, xj⟩, hjt⟩
      change ki = k at hi
      change kj = k at hj
      subst ki
      subst kj
      have hxine : xi.1 ≠ xj.1 := by
        intro h
        have hx : xi = xj := Subtype.ext h
        subst xj
        exact hij rfl
      exact hAdisjoint k xi.2 xj.2 hxine
    intro z
    have hbound :=
      card_activeUniformBumps_le_of_pairwiseDisjoint
        (family := fun i : t ↦ i.1.1)
        (c := fun i : t ↦ (i.1.2.1 : ℂ))
        r hr hindexDisjoint z
    simpa [Complex.finrank_real_complex] using hbound

/-- A compactly supported smooth cutoff can be chosen identically one near
all of `K`.  Its derivative and its complementary defect density are then
supported off `K`; if `g` is analytic on a deep core, the retained defect
lies in a prescribed thin frontier strip. -/
theorem exists_frontierCutoff_locallyOne
    (K : Set ℂ) (hK : IsCompact K) (hKne : K.Nonempty)
    {η r : ℝ} (hη : 0 < η) (hr : 0 < r)
    (hηr : η < r / 2)
    {f g : ℂ → ℂ}
    (hfh : AnalyticOnNhd ℂ f (interior K))
    (hgf : EqOn g f (interiorCore K η)) :
    ∃ ψ : ℂ → ℂ,
      ContDiff ℝ ∞ ψ ∧
      HasCompactSupport ψ ∧
      (∀ z, ‖ψ z‖ ≤ 1) ∧
      tsupport (fun z ↦ ψ z * crDefect g z) ⊆
        Metric.thickening (r / 2) (frontier K) ∧
      Disjoint
        (tsupport (fun z ↦
          (1 - ψ z) * crDefect g z)) K ∧
      Disjoint (tsupport (crDefect ψ)) K := by
  let U : Set ℂ :=
    Metric.thickening (r / 4) K
  have hUopen : IsOpen U :=
    Metric.isOpen_thickening
  have hKU : K ⊆ U :=
    Metric.self_subset_thickening (by positivity) K
  obtain ⟨δ, hδ, χ, hχsmooth, hχcompact, hχbounds,
      hχone, hχsupport⟩ :=
    exists_smooth_cutoff_bounded K U hK hUopen hKU
  let ψ : ℂ → ℂ :=
    fun z ↦ (χ z : ℂ)
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ χ)
    exact Complex.ofRealCLM.contDiff.comp hχsmooth
  have hψcompact : HasCompactSupport ψ :=
    hχcompact.comp_left Complex.ofReal_zero
  have hψsupport : tsupport ψ ⊆ U :=
    (tsupport_comp_subset Complex.ofReal_zero χ).trans
      hχsupport
  have hψnorm : ∀ z, ‖ψ z‖ ≤ 1 := by
    intro z
    simp [ψ, abs_of_nonneg (hχbounds z).1,
      (hχbounds z).2]
  have hψone_inner (z : ℂ)
      (hz : z ∈ Metric.thickening (δ / 3) K) :
      ψ =ᶠ[𝓝 z] (fun _ ↦ 1) := by
    filter_upwards
      [Metric.isOpen_thickening.mem_nhds hz] with w hw
    have hwclosed :
        w ∈ Metric.cthickening (δ / 3) K :=
      Metric.thickening_subset_cthickening _ _ hw
    simp [ψ, hχone w hwclosed]
  have hψone_nhds (z : ℂ) (hz : z ∈ K) :
      ψ =ᶠ[𝓝 z] (fun _ ↦ 1) :=
    hψone_inner z
      (Metric.self_subset_thickening
        (by positivity) K hz)
  have hfarDisj :
      Disjoint
        (tsupport (fun z ↦
          (1 - ψ z) * crDefect g z)) K := by
    rw [disjoint_left]
    intro z hzfar hzK
    apply ((notMem_tsupport_iff_eventuallyEq).2 ?_) hzfar
    filter_upwards [hψone_nhds z hzK] with w hw
    rw [hw]
    simp
  have hDψDisj :
      Disjoint (tsupport (crDefect ψ)) K := by
    rw [disjoint_left]
    intro z hzD hzK
    apply ((notMem_tsupport_iff_eventuallyEq).2 ?_) hzD
    have hzinner :
        z ∈ Metric.thickening (δ / 3) K :=
      Metric.self_subset_thickening
        (by positivity) K hzK
    filter_upwards
      [Metric.isOpen_thickening.mem_nhds hzinner] with w hw
    have heq := hψone_inner w hw
    have hdiff : DifferentiableAt ℂ ψ w :=
      (heq.differentiableAt_iff).2
        (differentiableAt_const (c := (1 : ℂ)))
    simpa only [Pi.zero_apply] using
      crDefect_eq_zero_of_differentiableAt hdiff
  have hdefectK :
      tsupport (crDefect g) ∩ K ⊆
        Metric.cthickening η (frontier K) :=
    crDefect_tsupport_inter_subset_cthickening_frontier
      K hη hfh hgf
  have hnearSupport :
      tsupport (fun z ↦ ψ z * crDefect g z) ⊆
        Metric.thickening (r / 2) (frontier K) := by
    intro z hz
    have hzψ : z ∈ tsupport ψ :=
      tsupport_mul_subset_left hz
    have hzD : z ∈ tsupport (crDefect g) :=
      tsupport_mul_subset_right hz
    by_cases hzK : z ∈ K
    · exact
        Metric.cthickening_subset_thickening'
          (by positivity : 0 < r / 2) hηr (frontier K)
            (hdefectK ⟨hzD, hzK⟩)
    · have hzU : z ∈ U :=
        hψsupport hzψ
      obtain ⟨y, hyK, hzy⟩ :=
        Metric.mem_thickening_iff.mp hzU
      have hKcne : Kᶜ ≠ (Set.univ : Set ℂ) := by
        rw [ne_eq, Set.compl_univ_iff]
        exact hKne.ne_empty
      obtain ⟨w, hwfront, hwEq⟩ :=
        exists_mem_frontier_infDist_compl_eq_dist
          (s := Kᶜ) (x := z) hzK hKcne
      have hwfrontK : w ∈ frontier K := by
        simpa only [frontier_compl] using hwfront
      have hinf :
          Metric.infDist z K < r / 4 :=
        (Metric.infDist_le_dist_of_mem hyK).trans_lt hzy
      have hzw : dist z w < r / 4 := by
        have hwEq' :
            Metric.infDist z K = dist z w := by
          simpa only [compl_compl] using hwEq
        rw [← hwEq']
        exact hinf
      rw [Metric.mem_thickening_iff]
      refine ⟨w, hwfrontK, ?_⟩
      linarith
  exact ⟨ψ, hψsmooth, hψcompact, hψnorm,
    hnearSupport, hfarDisj, hDψDisj⟩

end Submission.Helpers
