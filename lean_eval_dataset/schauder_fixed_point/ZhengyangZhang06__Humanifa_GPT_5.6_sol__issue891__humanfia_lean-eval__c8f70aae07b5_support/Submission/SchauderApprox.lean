import Submission.FiniteBrouwer

open Filter Set
open Metric
open scoped Topology

namespace Submission

/-- A compact convex self-map has an approximate fixed point at every positive
scale.  The finite-dimensional approximation is built from a partition of
unity subordinate to a finite cover by small balls. -/
theorem exists_approximate_fixed_point {E : Type*}
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {K : Set E}
    (hK_compact : IsCompact K) (hK_convex : Convex ℝ K)
    (hK_nonempty : K.Nonempty)
    (f : E → E)
    (hf_cont : ContinuousOn f K) (hf_maps : MapsTo f K K)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ K, dist (f x) x < ε := by
  classical
  obtain ⟨S, hS_sub, hS_finite, hS_cover⟩ :=
    hK_compact.finite_cover_balls hε

  let T : K → Set E := fun x =>
    convexHull ℝ (S ∩ ball (x : E) ε)
  have hT_convex : ∀ x, Convex ℝ (T x) := fun x =>
    convex_convexHull ℝ (S ∩ ball (x : E) ε)
  have hT_local : ∀ x : K, ∃ c : E, ∀ᶠ y in 𝓝 x, c ∈ T y := by
    intro x
    have hx_cover := hS_cover x.property
    simp only [mem_iUnion] at hx_cover
    obtain ⟨s, hsS, hxs⟩ := hx_cover
    refine ⟨s, ?_⟩
    have hevent : ∀ᶠ y : K in 𝓝 x, (y : E) ∈ ball s ε :=
      continuousAt_subtype_val.preimage_mem_nhds
        (isOpen_ball.mem_nhds hxs)
    filter_upwards [hevent] with y hys
    apply subset_convexHull ℝ
    exact ⟨hsS, mem_ball_comm.2 hys⟩

  obtain ⟨p, hp⟩ :=
    exists_continuous_forall_mem_convex_of_local_const hT_convex hT_local
  have hp_hull (x : K) : p x ∈ convexHull ℝ S := by
    exact convexHull_mono inter_subset_left (hp x)
  have hp_ball (x : K) : p x ∈ ball (x : E) ε := by
    exact convexHull_min inter_subset_right (convex_ball (x : E) ε) (hp x)

  let V : Submodule ℝ E := Submodule.span ℝ S
  letI : FiniteDimensional ℝ V :=
    FiniteDimensional.span_of_finite ℝ hS_finite
  have hHull_span : convexHull ℝ S ⊆ (V : Set E) := by
    apply convexHull_min
    · exact Submodule.subset_span
    · exact V.convex
  have hHull_K : convexHull ℝ S ⊆ K :=
    convexHull_min hS_sub hK_convex

  let C : Set V := {v | (v : E) ∈ convexHull ℝ S}
  have hC_closed : IsClosed C := by
    exact (hS_finite.isClosed_convexHull ℝ).preimage continuous_subtype_val
  have hC_bounded : Bornology.IsBounded C := by
    change Bornology.IsBounded
      (((fun v : V => (v : E)) ⁻¹' convexHull ℝ S))
    exact isometry_subtype_coe.antilipschitz.isBounded_preimage
      (hS_finite.isCompact_convexHull ℝ).isBounded
  have hC_compact : IsCompact C :=
    Metric.isCompact_iff_isClosed_bounded.2 ⟨hC_closed, hC_bounded⟩
  have hS_nonempty : S.Nonempty := by
    obtain ⟨x, hxK⟩ := hK_nonempty
    have hx_cover := hS_cover hxK
    simp only [mem_iUnion] at hx_cover
    obtain ⟨s, hsS, _⟩ := hx_cover
    exact ⟨s, hsS⟩
  have hC_nonempty : C.Nonempty := by
    obtain ⟨s, hsS⟩ := hS_nonempty
    refine ⟨⟨s, Submodule.subset_span hsS⟩, ?_⟩
    exact subset_convexHull ℝ S hsS
  have hC_convex : Convex ℝ C := by
    exact (convex_convexHull ℝ S).linear_preimage V.subtype

  let x₀ : K := ⟨hK_nonempty.some, hK_nonempty.some_mem⟩
  let q : V → K := fun v =>
    if hv : v ∈ C then
      ⟨f v, hf_maps (hHull_K hv)⟩
    else
      x₀
  let g : V → V := fun v =>
    ⟨p (q v), hHull_span (hp_hull (q v))⟩

  have hg_maps : MapsTo g C C := by
    intro v hv
    exact hp_hull (q v)
  have hg_cont : ContinuousOn g C := by
    let r : C → K := fun v =>
      ⟨f v, hf_maps (hHull_K v.property)⟩
    have hinc : Continuous (fun v : C => (v : E)) := by
      fun_prop
    have hfr : Continuous (fun v : C => f (v : E)) := by
      rw [← continuousOn_univ]
      exact hf_cont.comp hinc.continuousOn
        (fun v _ => hHull_K v.property)
    have hr : Continuous r :=
      hfr.subtype_mk (fun v => hf_maps (hHull_K v.property))
    let G : C → V := fun v =>
      ⟨p (r v), hHull_span (hp_hull (r v))⟩
    have hG : Continuous G :=
      (p.continuous.comp hr).subtype_mk
        (fun v => hHull_span (hp_hull (r v)))
    rw [continuousOn_iff_continuous_restrict]
    apply hG.congr
    intro v
    simp only [g, q, G, r]
    simp [v.property]

  obtain ⟨v, hvC, hgv⟩ :=
    finiteDimensional_fixed_point hC_compact hC_convex hC_nonempty
      g hg_cont hg_maps
  refine ⟨(v : E), hHull_K hvC, ?_⟩
  have hp_eq : p ⟨f v, hf_maps (hHull_K hvC)⟩ = (v : E) := by
    have hval := congrArg (fun w : V => (w : E)) hgv
    simpa [g, q, hvC] using hval
  have hball := hp_ball ⟨f v, hf_maps (hHull_K hvC)⟩
  rw [mem_ball, hp_eq, dist_comm] at hball
  exact hball

end Submission
