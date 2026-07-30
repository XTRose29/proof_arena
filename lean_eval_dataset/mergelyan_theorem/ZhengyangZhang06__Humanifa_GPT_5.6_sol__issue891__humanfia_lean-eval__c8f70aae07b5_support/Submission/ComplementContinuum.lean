import Mathlib.Topology.Subpath
import Submission.CenteredMoment

open Set
open scoped Topology

noncomputable section

namespace Submission.Helpers

/-- At every frontier point and every positive scale, the complement
contains a compact connected set which starts within that scale and reaches
the sphere of radius three times that scale, without leaving the
corresponding closed ball. -/
theorem exists_local_complement_continuum
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    {x : ℂ} (hx : x ∈ frontier K) (r : ℝ) (hr : 0 < r) :
    ∃ E : Set ℂ,
      IsCompact E ∧ IsConnected E ∧
      E ⊆ Kᶜ ∩ Metric.closedBall x (3 * r) ∧
      ∃ u ∈ E, ∃ v ∈ E,
        dist x u < r ∧ dist x v = 3 * r := by
  have hxclosure : x ∈ closure (Kᶜ) := by
    rw [frontier_eq_closure_inter_closure] at hx
    exact hx.2
  obtain ⟨u, huKc, hxu⟩ :=
    (Metric.mem_closure_iff.mp hxclosure) r hr
  obtain ⟨a, haKc, hxa, _hax⟩ :=
    exists_compl_point_controlled_distance_of_mem_frontier
      K hK hKc hx r hr
  have hKcPath : IsPathConnected (Kᶜ) :=
    hK.isClosed.isOpen_compl.isConnected_iff_isPathConnected.mp hKc
  let hjoin : JoinedIn (Kᶜ) u a :=
    hKcPath.joinedIn u huKc a haKc
  let γ : Path u a := hjoin.somePath
  let φ : Set.Icc (0 : ℝ) 1 → ℝ :=
    fun t ↦ dist x (γ t)
  have hφ : Continuous φ :=
    continuous_const.dist γ.continuous
  have hφzero : φ 0 < 3 * r := by
    dsimp only [φ]
    rw [γ.source]
    linarith
  have hφone : 3 * r < φ 1 := by
    dsimp only [φ]
    rw [γ.target]
    exact hxa
  let T : Set (Set.Icc (0 : ℝ) 1) :=
    {t | φ t = 3 * r}
  have hTcompact : IsCompact T := by
    apply IsClosed.isCompact
    exact isClosed_singleton.preimage hφ
  have hTnonempty : T.Nonempty := by
    have hlevel : 3 * r ∈ Set.Icc (φ 0) (φ 1) :=
      ⟨hφzero.le, hφone.le⟩
    obtain ⟨t, _ht, hφt⟩ :=
      intermediate_value_Icc
        (show (0 : Set.Icc (0 : ℝ) 1) ≤ 1 by simp)
        hφ.continuousOn hlevel
    exact ⟨t, hφt⟩
  obtain ⟨t₀, ht₀⟩ :=
    hTcompact.exists_isLeast hTnonempty
  have hprefix :
      ∀ s : Set.Icc (0 : ℝ) 1, s ≤ t₀ → φ s ≤ 3 * r := by
    intro s hs
    by_contra hle
    have hgt : 3 * r < φ s := lt_of_not_ge hle
    have hlevel : 3 * r ∈ Set.Icc (φ 0) (φ s) :=
      ⟨hφzero.le, hgt.le⟩
    obtain ⟨q, hq, hφq⟩ :=
      intermediate_value_Icc (show (0 : Set.Icc (0 : ℝ) 1) ≤ s by simp)
        hφ.continuousOn hlevel
    have hqT : q ∈ T := hφq
    have hqne : q ≠ s := by
      intro hqs
      rw [hqs] at hφq
      linarith
    have hqlt : q < s :=
      lt_of_le_of_ne hq.2 hqne
    exact (not_lt_of_ge (ht₀.2 hqT)) (hqlt.trans_le hs)
  let E : Set ℂ := Set.range (γ.subpath 0 t₀)
  refine ⟨E, isCompact_range (γ.subpath 0 t₀).continuous,
    isConnected_range (γ.subpath 0 t₀).continuous, ?_, ?_⟩
  · intro z hz
    have hzimage :
        z ∈ γ '' Set.Icc (0 : Set.Icc (0 : ℝ) 1) t₀ := by
      simpa only [E, Path.range_subpath_of_le γ 0 t₀ (by simp)] using hz
    obtain ⟨s, hs, rfl⟩ := hzimage
    constructor
    · exact hjoin.somePath_mem s
    · rw [Metric.mem_closedBall, dist_comm]
      exact hprefix s hs.2
  · refine ⟨u, ?_, γ t₀, ?_, hxu, ?_⟩
    · simpa only [E, γ.source] using
        Path.source_mem_range (γ.subpath 0 t₀)
    · simpa only [E] using
        Path.target_mem_range (γ.subpath 0 t₀)
    · exact ht₀.1

end Submission.Helpers
