import Submission.Localization

open Function Set
open scoped ContDiff Topology

noncomputable section

namespace Submission.Helpers

/-- A point in the open thickening of the frontier is within twice the
thickening radius of a point outside the set. -/
theorem exists_compl_point_near_of_mem_thickening_frontier
    {K : Set ℂ} {δ : ℝ} (hδ : 0 < δ) {z : ℂ}
    (hz : z ∈ Metric.thickening δ (frontier K)) :
    ∃ a ∈ Kᶜ, dist z a < 2 * δ := by
  obtain ⟨x, hxfrontier, hzx⟩ := Metric.mem_thickening_iff.mp hz
  have hxclosure : x ∈ closure (Kᶜ) := by
    rw [frontier_eq_closure_inter_closure] at hxfrontier
    exact hxfrontier.2
  obtain ⟨a, ha, hxa⟩ :=
    (Metric.mem_closure_iff.mp hxclosure) δ hδ
  refine ⟨a, ha, (dist_triangle z x a).trans_lt ?_⟩
  linarith

/-- The same proximity statement for the thickened closed frontier strip
used to support the near part of the defect. -/
theorem exists_compl_point_near_of_mem_thickening_cthickening_frontier
    {K : Set ℂ} {η δ : ℝ} (hη : 0 < η) (hδ : 0 < δ) {z : ℂ}
    (hz :
      z ∈ Metric.thickening δ
        (Metric.cthickening η (frontier K))) :
    ∃ a ∈ Kᶜ, dist z a < 2 * (δ + η) := by
  apply exists_compl_point_near_of_mem_thickening_frontier
    (K := K) (δ := δ + η) (by positivity)
  exact Metric.thickening_cthickening_subset δ hη.le
    (frontier K) hz

/-- A compact subset of a frontier strip has a finite cover by arbitrarily
small balls whose centers each admit a uniformly nearby pole off `K`. -/
theorem exists_finite_ball_cover_with_compl_poles
    {K S : Set ℂ} (hS : IsCompact S) {δ ρ : ℝ}
    (hδ : 0 < δ) (hρ : 0 < ρ)
    (hSfrontier : S ⊆ Metric.thickening δ (frontier K)) :
    ∃ t : Set ℂ,
      t.Finite ∧ t ⊆ S ∧
      S ⊆ ⋃ z ∈ t, Metric.ball z ρ ∧
      ∀ z ∈ t, ∃ a ∈ Kᶜ, dist z a < 2 * δ := by
  obtain ⟨t, htS, htfinite, hcover⟩ :=
    hS.finite_cover_balls hρ
  refine ⟨t, htfinite, htS, hcover, ?_⟩
  intro z hzt
  exact exists_compl_point_near_of_mem_thickening_frontier
    hδ (hSfrontier (htS hzt))

/-- If a smooth function agrees with an analytic function on a deep interior
core, then the part of its Cauchy--Riemann-defect support lying in `K` stays
inside the corresponding closed frontier strip. -/
theorem crDefect_tsupport_inter_subset_cthickening_frontier
    (K : Set ℂ) {δ : ℝ} (hδ : 0 < δ)
    {f g : ℂ → ℂ}
    (hfh : AnalyticOnNhd ℂ f (interior K))
    (hgf : EqOn g f (interiorCore K δ)) :
    tsupport (crDefect g) ∩ K ⊆
      Metric.cthickening δ (frontier K) := by
  intro z hz
  by_contra hzstrip
  have hznotfrontier : z ∉ frontier K := fun hzfrontier ↦
    hzstrip (Metric.self_subset_cthickening (frontier K) hzfrontier)
  have hzintK : z ∈ interior K := by
    rw [mem_interior_iff_notMem_frontier hz.2]
    exact hznotfrontier
  let U : Set ℂ :=
    interior K ∩ (Metric.cthickening δ (frontier K))ᶜ
  have hUopen : IsOpen U :=
    isOpen_interior.inter Metric.isClosed_cthickening.isOpen_compl
  have hzU : z ∈ U := ⟨hzintK, hzstrip⟩
  have hUcore : U ⊆ interior (interiorCore K δ) := by
    apply interior_maximal
    · intro w hw
      exact ⟨interior_subset hw.1, fun hwthick ↦
        hw.2 (Metric.thickening_subset_cthickening δ (frontier K) hwthick)⟩
    · exact hUopen
  have hzero :
      crDefect g =ᶠ[𝓝 z] (0 : ℂ → ℂ) := by
    filter_upwards [hUopen.mem_nhds hzU] with w hw
    simpa only [Pi.zero_apply] using
      crDefect_eq_zero_on_interiorCore K hδ hfh hgf w (hUcore hw)
  exact ((notMem_tsupport_iff_eventuallyEq).2 hzero) hz.1

/-- Split a density whose support meets `K` only in a compact set `S` into
a near part supported in a prescribed neighborhood of `S` and a far part
whose topological support is disjoint from `K`, retaining the unit norm bound
on the cutoff. -/
theorem exists_smooth_density_split_near_compact_bounded
    (K S U : Set ℂ) (hS : IsCompact S) (hU : IsOpen U)
    (hSU : S ⊆ U) (q : ℂ → ℂ)
    (hqK : tsupport q ∩ K ⊆ S) :
    ∃ ψ : ℂ → ℂ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ z, ‖ψ z‖ ≤ 1) ∧
      tsupport (fun z ↦ ψ z * q z) ⊆ U ∧
      Disjoint (tsupport (fun z ↦ (1 - ψ z) * q z)) K := by
  obtain ⟨ρ, hρ, χ, hχsmooth, hχcompact, hχbounds,
      hχone, hχsupport⟩ :=
    exists_smooth_cutoff_bounded S U hS hU hSU
  let ψ : ℂ → ℂ := fun z ↦ (χ z : ℂ)
  have hψsmooth : ContDiff ℝ ∞ ψ := by
    change ContDiff ℝ ∞ (Complex.ofRealCLM ∘ χ)
    exact Complex.ofRealCLM.contDiff.comp hχsmooth
  have hψcompact : HasCompactSupport ψ :=
    hχcompact.comp_left Complex.ofReal_zero
  have hψsupport : tsupport ψ ⊆ U := by
    exact (tsupport_comp_subset Complex.ofReal_zero χ).trans hχsupport
  have hψnorm : ∀ z, ‖ψ z‖ ≤ 1 := by
    intro z
    simp [ψ, abs_of_nonneg (hχbounds z).1, (hχbounds z).2]
  refine ⟨ψ, hψsmooth, hψcompact, hψnorm,
    (tsupport_mul_subset_left (f := ψ) (g := q)).trans hψsupport, ?_⟩
  rw [disjoint_left]
  intro z hzfar hzK
  apply ((notMem_tsupport_iff_eventuallyEq).2 ?_) hzfar
  by_cases hzq : z ∈ tsupport q
  · have hzS : z ∈ S := hqK ⟨hzq, hzK⟩
    have hzthick :
        z ∈ Metric.thickening (ρ / 3) S :=
      Metric.self_subset_thickening (by positivity) S hzS
    filter_upwards
      [Metric.isOpen_thickening.mem_nhds hzthick] with w hw
    have hχw : χ w = 1 :=
      hχone w (Metric.thickening_subset_cthickening (ρ / 3) S hw)
    simp [ψ, hχw]
  · have hqzero : q =ᶠ[𝓝 z] (0 : ℂ → ℂ) :=
      (notMem_tsupport_iff_eventuallyEq).1 hzq
    filter_upwards [hqzero] with w hw
    simp only [hw, mul_zero, Pi.zero_apply]

/-- The near/far density split without exposing the cutoff bound. -/
theorem exists_smooth_density_split_near_compact
    (K S U : Set ℂ) (hS : IsCompact S) (hU : IsOpen U)
    (hSU : S ⊆ U) (q : ℂ → ℂ)
    (hqK : tsupport q ∩ K ⊆ S) :
    ∃ ψ : ℂ → ℂ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport (fun z ↦ ψ z * q z) ⊆ U ∧
      Disjoint (tsupport (fun z ↦ (1 - ψ z) * q z)) K := by
  obtain ⟨ψ, hψ, hψc, _hψnorm, hψsupport, hψdisj⟩ :=
    exists_smooth_density_split_near_compact_bounded
      K S U hS hU hSU q hqK
  exact ⟨ψ, hψ, hψc, hψsupport, hψdisj⟩

/-- For the relative smooth approximant used in the Mergelyan reduction,
the Cauchy--Riemann defect admits a smooth near/far split.  The near part is
confined to an arbitrarily small neighborhood of the closed frontier strip,
while the far part has support disjoint from `K`. -/
theorem exists_crDefect_split_frontier
    (K : Set ℂ) (hK : IsCompact K) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ)
    {f g : ℂ → ℂ} (hfh : AnalyticOnNhd ℂ f (interior K))
    (hgf : EqOn g f (interiorCore K η)) :
    ∃ ψ : ℂ → ℂ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      tsupport (fun z ↦ ψ z * crDefect g z) ⊆
        Metric.thickening δ
          (Metric.cthickening η (frontier K)) ∧
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K := by
  have hfrontier : IsCompact (frontier K) :=
    hK.of_isClosed_subset isClosed_frontier hK.isClosed.frontier_subset
  have hstrip :
      IsCompact (Metric.cthickening η (frontier K)) :=
    hfrontier.cthickening
  apply exists_smooth_density_split_near_compact
    K (Metric.cthickening η (frontier K))
      (Metric.thickening δ
        (Metric.cthickening η (frontier K)))
      hstrip Metric.isOpen_thickening
      (Metric.self_subset_thickening hδ
        (Metric.cthickening η (frontier K)))
      (crDefect g)
  exact crDefect_tsupport_inter_subset_cthickening_frontier
    K hη hfh hgf

/-- Bounded version of the frontier defect split. -/
theorem exists_crDefect_split_frontier_bounded
    (K : Set ℂ) (hK : IsCompact K) {η δ : ℝ}
    (hη : 0 < η) (hδ : 0 < δ)
    {f g : ℂ → ℂ} (hfh : AnalyticOnNhd ℂ f (interior K))
    (hgf : EqOn g f (interiorCore K η)) :
    ∃ ψ : ℂ → ℂ,
      ContDiff ℝ ∞ ψ ∧ HasCompactSupport ψ ∧
      (∀ z, ‖ψ z‖ ≤ 1) ∧
      tsupport (fun z ↦ ψ z * crDefect g z) ⊆
        Metric.thickening δ
          (Metric.cthickening η (frontier K)) ∧
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K := by
  have hfrontier : IsCompact (frontier K) :=
    hK.of_isClosed_subset isClosed_frontier hK.isClosed.frontier_subset
  have hstrip :
      IsCompact (Metric.cthickening η (frontier K)) :=
    hfrontier.cthickening
  apply exists_smooth_density_split_near_compact_bounded
    K (Metric.cthickening η (frontier K))
      (Metric.thickening δ
        (Metric.cthickening η (frontier K)))
      hstrip Metric.isOpen_thickening
      (Metric.self_subset_thickening hδ
        (Metric.cthickening η (frontier K)))
      (crDefect g)
  exact crDefect_tsupport_inter_subset_cthickening_frontier
    K hη hfh hgf

/-- The far term in a defect split belongs to the closed polynomial algebra.
Thus only the frontier-supported near term remains in the Mergelyan reduction. -/
theorem cauchyFarDefectIntegral_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ ∞ ψ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K) :
    (∫ w : ℂ,
      cauchyDensityMap K
        (fun z ↦ (1 - ψ z) * crDefect g z) hdisj w) ∈
      (polynomialFunctions K).topologicalClosure := by
  apply cauchyDensityIntegral_mem_polynomialClosure hKc
  · exact (continuous_const.sub hψ.continuous).mul
      (continuous_crDefect g hg)
  · exact (crDefect_hasCompactSupport g hgc).mul_left

end Submission.Helpers
