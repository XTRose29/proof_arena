import Mathlib.Analysis.Complex.AbsMax
import Mathlib.Analysis.Complex.SqrtDeriv
import Mathlib.Topology.UniformSpace.Path
import Submission.AnalyticCapacityGerm
import Submission.ComplementContinuum
import Submission.PlaneTopology

open Filter Function Metric Set
open scoped Pointwise Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- The branch cut associated to the ordered pair `a, b`. -/
def segmentRatio (a b z : ℂ) : ℂ :=
  (z - a) / (z - b)

/-- Off the real segment from `a` to `b`, the associated quotient lies in
the principal slit plane. -/
theorem segmentRatio_mem_slitPlane_of_notMem_segment
    {a b z : ℂ} (hz : z ∉ segment ℝ a b) :
    segmentRatio a b z ∈ Complex.slitPlane := by
  rw [Complex.mem_slitPlane_iff_not_le_zero]
  intro hratio
  have hzb : z ≠ b := by
    intro h
    subst z
    exact hz (right_mem_segment ℝ a b)
  let t : ℝ := -(segmentRatio a b z).re
  have ht : 0 ≤ t := by
    dsimp only [t]
    exact neg_nonneg.mpr hratio.1
  have hratio_eq : segmentRatio a b z = -(t : ℂ) := by
    apply Complex.ext
    · simp [t]
    · simpa [t] using hratio.2
  have hone : (1 + t : ℝ) ≠ 0 := by positivity
  refine hz ?_
  refine ⟨(1 / (1 + t) : ℝ), t / (1 + t), ?_, ?_, ?_, ?_⟩
  · positivity
  · positivity
  · field_simp
  · change
      ((1 / (1 + t) : ℝ) : ℂ) * a +
          ((t / (1 + t) : ℝ) : ℂ) * b = z
    have hden : z - b ≠ 0 := sub_ne_zero.mpr hzb
    have hcross :
        z - a = -(t : ℂ) * (z - b) := by
      apply (div_eq_iff hden).mp
      simpa only [segmentRatio] using hratio_eq
    have hsolve :
        (((1 + t : ℝ) : ℂ) * z) = a + (t : ℂ) * b := by
      push_cast
      linear_combination hcross
    have honeC : ((1 + t : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hone
    rw [Complex.ofReal_div, Complex.ofReal_div]
    norm_num only [Complex.ofReal_one, Complex.ofReal_add] at hsolve honeC ⊢
    calc
      (1 : ℂ) / (1 + (t : ℂ)) * a +
            (t : ℂ) / (1 + (t : ℂ)) * b =
          (a + (t : ℂ) * b) / (1 + (t : ℂ)) := by ring
      _ = ((1 + (t : ℂ)) * z) / (1 + (t : ℂ)) := by
        rw [hsolve]
      _ = z := by simp [honeC]

/-- The finite polygonal trace determined by consecutive vertices. -/
def polygonalTrace (p : ℕ → ℂ) (N : ℕ) : Set ℂ :=
  ⋃ k ∈ Finset.range N, segment ℝ (p k) (p (k + 1))

/-- The product of principal square roots attached to a polygonal chain. -/
def polygonalRootProduct (p : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∏ k ∈ Finset.range N,
    Complex.sqrt (segmentRatio (p k) (p (k + 1)) z)

theorem notMem_segment_of_notMem_polygonalTrace
    {p : ℕ → ℂ} {N : ℕ} {z : ℂ}
    (hz : z ∉ polygonalTrace p N) {k : ℕ}
    (hk : k ∈ Finset.range N) :
    z ∉ segment ℝ (p k) (p (k + 1)) := by
  intro hzk
  apply hz
  exact mem_iUnion₂.mpr ⟨k, hk, hzk⟩

theorem differentiableAt_polygonalRootProduct
    {p : ℕ → ℂ} {N : ℕ} {z : ℂ}
    (hz : z ∉ polygonalTrace p N) :
    DifferentiableAt ℂ (polygonalRootProduct p N) z := by
  classical
  change
    DifferentiableAt ℂ
      (fun z ↦ ∏ k ∈ Finset.range N,
        Complex.sqrt
          (segmentRatio (p k) (p (k + 1)) z)) z
  apply DifferentiableAt.fun_finsetProd
  intro k hk
  apply (Complex.differentiableAt_sqrt
    (segmentRatio_mem_slitPlane_of_notMem_segment
      (notMem_segment_of_notMem_polygonalTrace hz hk))).comp
  unfold segmentRatio
  apply DifferentiableAt.div
  · fun_prop
  · fun_prop
  · exact sub_ne_zero.mpr fun h ↦ by
      apply notMem_segment_of_notMem_polygonalTrace hz hk
      rw [h]
      exact right_mem_segment ℝ (p k) (p (k + 1))

theorem continuousAt_polygonalRootProduct
    {p : ℕ → ℂ} {N : ℕ} {z : ℂ}
    (hz : z ∉ polygonalTrace p N) :
    ContinuousAt (polygonalRootProduct p N) z :=
  (differentiableAt_polygonalRootProduct hz).continuousAt

theorem complex_sqrt_sq (z : ℂ) :
    Complex.sqrt z ^ 2 = z := by
  rw [Complex.sqrt, ← Complex.cpow_nat_mul]
  norm_num

theorem mem_polygonalTrace_vertex_of_lt
    (p : ℕ → ℂ) {N k : ℕ} (hk : k < N) :
    p k ∈ polygonalTrace p N := by
  apply mem_iUnion₂.mpr
  exact ⟨k, Finset.mem_range.mpr hk,
    left_mem_segment ℝ (p k) (p (k + 1))⟩

theorem mem_polygonalTrace_last
    (p : ℕ → ℂ) {N : ℕ} (hN : 0 < N) :
    p N ∈ polygonalTrace p N := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hN.ne'
  apply mem_iUnion₂.mpr
  exact ⟨n, Finset.mem_range.mpr (Nat.lt_succ_self n), by
    simpa only using right_mem_segment ℝ (p n) (p (n + 1))⟩

theorem ne_polygonal_vertex_of_notMem
    {p : ℕ → ℂ} {N : ℕ} (hN : 0 < N) {z : ℂ}
    (hz : z ∉ polygonalTrace p N) {k : ℕ} (hk : k ≤ N) :
    z ≠ p k := by
  intro h
  apply hz
  rw [h]
  rcases hk.eq_or_lt with rfl | hk
  · exact mem_polygonalTrace_last p hN
  · exact mem_polygonalTrace_vertex_of_lt p hk

theorem prod_segmentRatio_eq_endpoints
    (p : ℕ → ℂ) (N : ℕ) (z : ℂ)
    (hz : ∀ k ≤ N, z ≠ p k) :
    (∏ k ∈ Finset.range N,
        segmentRatio (p k) (p (k + 1)) z) =
      (z - p 0) / (z - p N) := by
  induction N with
  | zero =>
      rw [Finset.prod_range_zero, div_self
        (sub_ne_zero.mpr (hz 0 le_rfl))]
  | succ N ih =>
      have hz' : ∀ k ≤ N, z ≠ p k :=
        fun k hk ↦ hz k (hk.trans (Nat.le_succ N))
      rw [Finset.prod_range_succ, ih hz']
      unfold segmentRatio
      have hN : z - p N ≠ 0 :=
        sub_ne_zero.mpr (hz N (Nat.le_succ N))
      have hNs : z - p (N + 1) ≠ 0 :=
        sub_ne_zero.mpr (hz (N + 1) le_rfl)
      field_simp [hN, hNs]

theorem polygonalRootProduct_sq
    {p : ℕ → ℂ} {N : ℕ} (hN : 0 < N) {z : ℂ}
    (hz : z ∉ polygonalTrace p N) :
    polygonalRootProduct p N z ^ 2 =
      (z - p 0) / (z - p N) := by
  classical
  rw [polygonalRootProduct, ← Finset.prod_pow]
  simp_rw [complex_sqrt_sq]
  exact prod_segmentRatio_eq_endpoints p N z
    (fun k hk ↦ ne_polygonal_vertex_of_notMem hN hz hk)

/-- A path in an open set can be replaced by a finite polygonal chain
which stays in that open set.  If the path also lies in a convex set, the
polygonal chain retains that constraint. -/
theorem exists_polygonal_trace_of_path
    {u v : ℂ} (γ : Path u v) {O C : Set ℂ}
    (hO : IsOpen O) (hγO : range γ ⊆ O)
    (hC : Convex ℝ C) (hγC : range γ ⊆ C) :
    ∃ (N : ℕ) (p : ℕ → ℂ),
      0 < N ∧ p 0 = u ∧ p N = v ∧
      polygonalTrace p N ⊆ O ∩ C := by
  have hγcompact : IsCompact (range γ) :=
    isCompact_range γ.continuous
  obtain ⟨δ, hδ, hδO⟩ :=
    hγcompact.exists_cthickening_subset_open hO hγO
  obtain ⟨η, hη, hmod⟩ :=
    (Metric.uniformContinuous_iff.mp γ.uniformContinuous_extend) δ hδ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt hη
  let N : ℕ := n + 1
  let p : ℕ → ℂ :=
    fun k ↦ γ.extend ((k : ℝ) / (N : ℝ))
  have hN : 0 < N := by
    dsimp only [N]
    omega
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hparam_mem (k : ℕ) (hk : k ≤ N) :
      (k : ℝ) / (N : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor
    · positivity
    · exact (div_le_one hNreal).2 (by exact_mod_cast hk)
  have hp_range (k : ℕ) (hk : k ≤ N) :
      p k ∈ range γ := by
    refine ⟨⟨(k : ℝ) / (N : ℝ), hparam_mem k hk⟩, ?_⟩
    exact (Path.extend_apply γ (hparam_mem k hk)).symm
  have hpC (k : ℕ) (hk : k ≤ N) : p k ∈ C :=
    hγC (hp_range k hk)
  have hparam_dist (k : ℕ) :
      dist ((k : ℝ) / (N : ℝ))
          (((k + 1 : ℕ) : ℝ) / (N : ℝ)) =
        1 / (N : ℝ) := by
    have heq :
        (k : ℝ) / (N : ℝ) -
            (((k + 1 : ℕ) : ℝ) / (N : ℝ)) =
          -(1 / (N : ℝ)) := by
      push_cast
      field_simp [hNreal.ne']
      ring
    rw [Real.dist_eq, heq, abs_neg,
      abs_of_pos (one_div_pos.mpr hNreal)]
  have hadj (k : ℕ) (hk : k < N) :
      dist (p k) (p (k + 1)) < δ := by
    apply hmod
    rw [hparam_dist]
    simpa only [N, Nat.cast_add, Nat.cast_one] using hn
  refine ⟨N, p, hN, ?_, ?_, ?_⟩
  · simp [p]
  · simp [p, hN.ne']
  · intro z hz
    rcases mem_iUnion₂.mp hz with ⟨k, hk, hzk⟩
    have hkN : k < N := Finset.mem_range.mp hk
    have hk1N : k + 1 ≤ N := hkN
    constructor
    · apply hδO
      apply Metric.mem_cthickening_of_dist_le z (p k) δ (range γ)
      · exact hp_range k hkN.le
      · have hdist :
            dist z (p k) ≤ dist (p k) (p (k + 1)) := by
          simpa only [Metric.mem_closedBall] using
            segment_subset_closedBall_left (p k) (p (k + 1)) hzk
        exact hdist.trans (hadj k hkN).le
    · exact hC.segment_subset (hpC k hkN.le) (hpC (k + 1) hk1N) hzk

/-- Path-valued form of the local complement-continuum construction. -/
theorem exists_local_complement_path
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    {x : ℂ} (hx : x ∈ frontier K) (r : ℝ) (hr : 0 < r) :
    ∃ (u v : ℂ) (γ : Path u v),
      range γ ⊆ Kᶜ ∩ Metric.closedBall x (3 * r) ∧
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
      intermediate_value_Icc
        (show (0 : Set.Icc (0 : ℝ) 1) ≤ s by simp)
        hφ.continuousOn hlevel
    have hqT : q ∈ T := hφq
    have hqne : q ≠ s := by
      intro hqs
      rw [hqs] at hφq
      linarith
    have hqlt : q < s :=
      lt_of_le_of_ne hq.2 hqne
    exact (not_lt_of_ge (ht₀.2 hqT)) (hqlt.trans_le hs)
  let γ₀ : Path (γ 0) (γ t₀) :=
    γ.subpath 0 t₀
  refine ⟨γ 0, γ t₀, γ₀, ?_, ?_, ?_⟩
  · intro z hz
    have hzimage :
        z ∈ γ '' Set.Icc (0 : Set.Icc (0 : ℝ) 1) t₀ := by
      simpa only [γ₀, Path.range_subpath_of_le γ 0 t₀ (by simp)]
        using hz
    obtain ⟨s, hs, rfl⟩ := hzimage
    constructor
    · exact hjoin.somePath_mem s
    · rw [Metric.mem_closedBall, dist_comm]
      exact hprefix s hs.2
  · simpa only [γ.source] using hxu
  · exact ht₀.1

/-- Every frontier scale admits a finite polygonal continuum in the
complement with endpoint separation comparable to that scale. -/
theorem exists_local_complement_polygon
    (K : Set ℂ) (hK : IsCompact K) (hKc : IsConnected (Kᶜ))
    {x : ℂ} (hx : x ∈ frontier K) (r : ℝ) (hr : 0 < r) :
    ∃ (N : ℕ) (p : ℕ → ℂ),
      0 < N ∧
      polygonalTrace p N ⊆ Kᶜ ∩ Metric.closedBall x (3 * r) ∧
      dist x (p 0) < r ∧ dist x (p N) = 3 * r := by
  obtain ⟨u, v, γ, hγ, hu, hv⟩ :=
    exists_local_complement_path K hK hKc hx r hr
  obtain ⟨N, p, hN, hp0, hpN, hp⟩ :=
    exists_polygonal_trace_of_path γ
      hK.isClosed.isOpen_compl (hγ.trans inter_subset_left)
      (convex_closedBall x (3 * r)) (hγ.trans inter_subset_right)
  exact ⟨N, p, hN, hp, hp0 ▸ hu, hpN ▸ hv⟩

theorem isCompact_polygonalTrace (p : ℕ → ℂ) (N : ℕ) :
    IsCompact (polygonalTrace p N) := by
  rw [polygonalTrace]
  apply (Finset.range N).isCompact_biUnion
  intro k _hk
  rw [← convexHull_pair]
  exact
    (by simp : ({p k, p (k + 1)} : Set ℂ).Finite).isCompact_convexHull ℝ

theorem polygonalTrace_nonempty
    (p : ℕ → ℂ) {N : ℕ} (hN : 0 < N) :
    (polygonalTrace p N).Nonempty :=
  ⟨p 0, mem_polygonalTrace_vertex_of_lt p hN⟩

theorem tendsto_segmentRatio_cocompact
    (a b : ℂ) :
    Tendsto (segmentRatio a b) (cocompact ℂ) (𝓝 1) := by
  have hinv :
      Tendsto (fun z : ℂ ↦ (z - b)⁻¹) (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded.comp
      (tendsto_sub_const_cobounded b)
  have hlim :
      Tendsto
        (fun z : ℂ ↦ 1 + (b - a) * (z - b)⁻¹)
        (cocompact ℂ) (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  apply hlim.congr'
  filter_upwards [isCompact_singleton.compl_mem_cocompact] with z hz
  have hzb : z - b ≠ 0 := by
    exact sub_ne_zero.mpr (by simpa only [mem_compl_iff,
      mem_singleton_iff] using hz)
  unfold segmentRatio
  field_simp [hzb]
  ring

theorem tendsto_polygonalRootProduct_cocompact
    (p : ℕ → ℂ) (N : ℕ) :
    Tendsto (polygonalRootProduct p N) (cocompact ℂ) (𝓝 1) := by
  classical
  change
    Tendsto
      (fun z ↦ ∏ k ∈ Finset.range N,
        Complex.sqrt
          (segmentRatio (p k) (p (k + 1)) z))
      (cocompact ℂ) (𝓝 1)
  simpa only [Function.comp_apply, Complex.sqrt_one,
    Finset.prod_const_one] using
    tendsto_finsetProd (Finset.range N) fun k _hk ↦
      (Complex.continuousAt_sqrt (by left; norm_num)).tendsto.comp
        (tendsto_segmentRatio_cocompact (p k) (p (k + 1)))

/-- Cayley transform of the polygonal square-root product. -/
def polygonalFraction (p : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  (polygonalRootProduct p N z - 1) /
    (polygonalRootProduct p N z + 1)

/-- Universally normalized polygonal capacity function. -/
def polygonalCapacityFunction (p : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  polygonalFraction p N z / 25

theorem polygonalRootProduct_add_one_ne_zero
    {p : ℕ → ℂ} {N : ℕ} (hN : 0 < N)
    (hend : p 0 ≠ p N) {z : ℂ}
    (hz : z ∉ polygonalTrace p N) :
    polygonalRootProduct p N z + 1 ≠ 0 := by
  intro hadd
  have hs : polygonalRootProduct p N z = -1 := by
    linear_combination hadd
  have hquot : (z - p 0) / (z - p N) = 1 := by
    rw [← polygonalRootProduct_sq hN hz, hs]
    norm_num
  have hzN : z - p N ≠ 0 :=
    sub_ne_zero.mpr
      (ne_polygonal_vertex_of_notMem hN hz le_rfl)
  have heq : z - p 0 = z - p N :=
    (div_eq_one_iff_eq hzN).mp hquot
  apply hend
  calc
    p 0 = z - (z - p 0) := by abel
    _ = z - (z - p N) := by rw [heq]
    _ = p N := by abel

theorem differentiableAt_polygonalCapacityFunction
    {p : ℕ → ℂ} {N : ℕ} (hN : 0 < N)
    (hend : p 0 ≠ p N) {z : ℂ}
    (hz : z ∉ polygonalTrace p N) :
    DifferentiableAt ℂ (polygonalCapacityFunction p N) z := by
  unfold polygonalCapacityFunction polygonalFraction
  apply DifferentiableAt.div_const
  apply DifferentiableAt.div
  · exact (differentiableAt_polygonalRootProduct hz).sub_const 1
  · exact (differentiableAt_polygonalRootProduct hz).add_const 1
  · exact polygonalRootProduct_add_one_ne_zero hN hend hz

theorem tendsto_polygonalCapacityFunction_cocompact
    (p : ℕ → ℂ) (N : ℕ) :
    Tendsto (polygonalCapacityFunction p N)
      (cocompact ℂ) (𝓝 0) := by
  have hcont :
      ContinuousAt (fun s : ℂ ↦ (s - 1) / (s + 1) / 25) 1 := by
    fun_prop (disch := norm_num)
  change
    Tendsto
      (fun z ↦
        (polygonalRootProduct p N z - 1) /
          (polygonalRootProduct p N z + 1) / 25)
      (cocompact ℂ) (𝓝 0)
  convert
    hcont.tendsto.comp
      (tendsto_polygonalRootProduct_cocompact p N) using 1 <;>
    simp [Function.comp_def]

/-- Near the polygonal cut, endpoint separation gives a universal bound
for its Cayley transform. -/
theorem norm_polygonalFraction_le_twentyFive_of_mem_cthickening
    {p : ℕ → ℂ} {N : ℕ} (hN : 0 < N)
    {x : ℂ} {r : ℝ} (hr : 0 < r)
    (htrace :
      polygonalTrace p N ⊆ Metric.closedBall x (3 * r))
    (hu : dist x (p 0) < r)
    (hv : dist x (p N) = 3 * r)
    {z : ℂ} (hz : z ∉ polygonalTrace p N)
    (hznear :
      z ∈ Metric.cthickening r (polygonalTrace p N)) :
    ‖polygonalFraction p N z‖ ≤ 25 := by
  have hzunion :
      z ∈ ⋃ w ∈ polygonalTrace p N,
        Metric.closedBall w (2 * r) :=
    Metric.cthickening_subset_iUnion_closedBall_of_lt
      (polygonalTrace p N) (by positivity) (by linarith) hznear
  rcases mem_iUnion₂.mp hzunion with ⟨w, hwE, hzw⟩
  have hzw' : dist z w ≤ 2 * r := by
    simpa only [Metric.mem_closedBall] using hzw
  have hwx : dist w x ≤ 3 * r := by
    simpa only [Metric.mem_closedBall] using htrace hwE
  have hwv : dist w (p N) ≤ 6 * r := by
    calc
      dist w (p N) ≤ dist w x + dist x (p N) :=
        dist_triangle _ _ _
      _ ≤ 3 * r + 3 * r := by rw [hv]; gcongr
      _ = 6 * r := by ring
  have hzv : dist z (p N) ≤ 8 * r := by
    calc
      dist z (p N) ≤ dist z w + dist w (p N) :=
        dist_triangle _ _ _
      _ ≤ 2 * r + 6 * r := add_le_add hzw' hwv
      _ = 8 * r := by ring
  have huv : 2 * r < dist (p 0) (p N) := by
    have htri :
        dist x (p N) ≤ dist x (p 0) + dist (p 0) (p N) :=
      dist_triangle _ _ _
    rw [hv] at htri
    linarith
  let S : ℂ := polygonalRootProduct p N z
  let q : ℂ := (z - p 0) / (z - p N)
  have hzN : z - p N ≠ 0 :=
    sub_ne_zero.mpr
      (ne_polygonal_vertex_of_notMem hN hz le_rfl)
  have hqnorm_mul :
      ‖q - 1‖ * dist z (p N) = dist (p 0) (p N) := by
    have hqeq :
        q - 1 = (p N - p 0) / (z - p N) := by
      dsimp only [q]
      field_simp [hzN]
      ring
    rw [hqeq, norm_div, dist_eq_norm, dist_eq_norm,
      div_mul_cancel₀ _ (norm_ne_zero_iff.mpr hzN)]
    rw [norm_sub_rev (p N) (p 0)]
  have hqquarter : (1 : ℝ) / 4 < ‖q - 1‖ := by
    by_contra h
    have hle : ‖q - 1‖ ≤ (1 : ℝ) / 4 := le_of_not_gt h
    have hnonneg : 0 ≤ ‖q - 1‖ := norm_nonneg _
    nlinarith [hqnorm_mul, hzv]
  have hSq : S ^ 2 = q := by
    exact polygonalRootProduct_sq hN hz
  have hfactor :
      (S - 1) * (S + 1) = q - 1 := by
    rw [← hSq]
    ring
  let D : ℝ := ‖S + 1‖
  let A : ℝ := ‖S - 1‖
  have hprod : ‖q - 1‖ = A * D := by
    rw [← hfactor, norm_mul]
  have hA : A ≤ D + 2 := by
    dsimp only [A, D]
    calc
      ‖S - 1‖ = ‖(S + 1) - 2‖ := by
        congr 1
        ring
      _ ≤ ‖S + 1‖ + ‖(2 : ℂ)‖ := norm_sub_le _ _
      _ = ‖S + 1‖ + 2 := by norm_num
  have hD : (1 : ℝ) / 12 ≤ D := by
    by_cases hD1 : 1 ≤ D
    · linarith
    · have hDlt : D < 1 := lt_of_not_ge hD1
      have hAlt : A < 3 := hA.trans_lt (by linarith)
      have hDnonneg : 0 ≤ D := norm_nonneg _
      have hAnonneg : 0 ≤ A := norm_nonneg _
      rw [hprod] at hqquarter
      nlinarith [mul_lt_mul_of_pos_right hAlt
        (show 0 < D by
          by_contra hDz
          have : D = 0 := le_antisymm (le_of_not_gt hDz) hDnonneg
          rw [this, mul_zero] at hqquarter
          norm_num at hqquarter)]
  have hDpos : 0 < D := lt_of_lt_of_le (by norm_num) hD
  unfold polygonalFraction
  rw [norm_div]
  change A / D ≤ 25
  rw [div_le_iff₀ hDpos]
  nlinarith

theorem norm_polygonalCapacityFunction_le_one_of_fraction
    {p : ℕ → ℂ} {N : ℕ} {z : ℂ}
    (h : ‖polygonalFraction p N z‖ ≤ 25) :
    ‖polygonalCapacityFunction p N z‖ ≤ 1 := by
  rw [polygonalCapacityFunction, norm_div]
  norm_num
  calc
    ‖polygonalFraction p N z‖ / 25 ≤ 25 / 25 := by
      exact div_le_div_of_nonneg_right h (by norm_num)
    _ = 1 := by norm_num

/-- The normalized polygonal capacity function is bounded by one on the
entire complement of its branch cut. -/
theorem norm_polygonalCapacityFunction_le_one
    {p : ℕ → ℂ} {N : ℕ} (hN : 0 < N)
    {x : ℂ} {r : ℝ} (hr : 0 < r)
    (htrace :
      polygonalTrace p N ⊆ Metric.closedBall x (3 * r))
    (hu : dist x (p 0) < r)
    (hv : dist x (p N) = 3 * r)
    {z : ℂ} (hz : z ∉ polygonalTrace p N) :
    ‖polygonalCapacityFunction p N z‖ ≤ 1 := by
  let E : Set ℂ := polygonalTrace p N
  have hEcompact : IsCompact E :=
    isCompact_polygonalTrace p N
  have hEclosed : IsClosed E :=
    hEcompact.isClosed
  have hEne : E.Nonempty :=
    polygonalTrace_nonempty p hN
  have hend : p 0 ≠ p N := by
    intro heq
    rw [heq, hv] at hu
    linarith
  have hzclosure : z ∉ closure E := by
    rwa [hEclosed.closure_eq]
  obtain ⟨e, he, heE⟩ :=
    exists_real_pos_lt_infEDist_of_notMem_closure hzclosure
  let δ : ℝ := min (r / 2) (e / 2)
  have hδ : 0 < δ := by
    exact lt_min (half_pos hr) (half_pos he)
  have hδr : δ ≤ r := by
    exact (min_le_left _ _).trans (by linarith)
  have hδe : δ < e := by
    exact (min_le_right _ _).trans_lt (half_lt_self he)
  have hzδ : z ∉ Metric.cthickening δ E := by
    rw [Metric.mem_cthickening_iff]
    exact not_le.mpr
      (((ENNReal.ofReal_lt_ofReal_iff he).mpr hδe).trans heE)
  have hfarEventually :
      ∀ᶠ w : ℂ in cocompact ℂ,
        ‖polygonalCapacityFunction p N w‖ ≤ 1 := by
    have h :=
      tendsto_polygonalCapacityFunction_cocompact p N
        (Metric.closedBall_mem_nhds (0 : ℂ) zero_lt_one)
    change
      ∀ᶠ w : ℂ in cocompact ℂ,
        polygonalCapacityFunction p N w ∈
          Metric.closedBall (0 : ℂ) 1 at h
    simpa only [Metric.mem_closedBall, dist_zero_right,
      mem_setOf_eq] using h
  obtain ⟨R₀, hR₀⟩ :=
    Metric.closedBall_compl_subset_of_mem_cocompact
      hfarEventually 0
  let R : ℝ := max (R₀ + 1) (‖z‖ + 1)
  have hR₀R : R₀ < R := by
    exact (lt_add_one R₀).trans_le (le_max_left _ _)
  have hzR : ‖z‖ < R := by
    exact (lt_add_one ‖z‖).trans_le (le_max_right _ _)
  have hR : 0 < R := by
    exact (norm_nonneg z).trans_lt hzR
  let U : Set ℂ :=
    Metric.ball 0 R ∩ (Metric.cthickening δ E)ᶜ
  have hzU : z ∈ U := by
    exact ⟨by simpa only [Metric.mem_ball, dist_zero_right] using hzR,
      by simpa only [mem_compl_iff] using hzδ⟩
  have hUbounded : Bornology.IsBounded U :=
    isBounded_ball.subset inter_subset_left
  have hUthick :
      U ⊆ (Metric.thickening δ E)ᶜ := by
    intro w hw
    exact
      (compl_subset_compl.mpr
        (Metric.thickening_subset_cthickening δ E)) hw.2
  have hclosureU :
      closure U ⊆ (Metric.thickening δ E)ᶜ :=
    closure_minimal hUthick Metric.isOpen_thickening.isClosed_compl
  have hdiff :
      DifferentiableOn ℂ
        (polygonalCapacityFunction p N) (closure U) := by
    intro w hw
    apply
      (differentiableAt_polygonalCapacityFunction hN hend ?_).differentiableWithinAt
    intro hwE
    have hwthick :
        w ∈ Metric.thickening δ E :=
      Metric.self_subset_thickening hδ E hwE
    exact (hclosureU hw) hwthick
  have hDC :
      DiffContOnCl ℂ (polygonalCapacityFunction p N) U :=
    hdiff.diffContOnCl
  apply
    Complex.norm_le_of_forall_mem_frontier_norm_le
      hUbounded hDC (C := 1) ?_ (subset_closure hzU)
  intro w hw
  rcases
      frontier_inter_subset
        (Metric.ball (0 : ℂ) R)
        ((Metric.cthickening δ E)ᶜ) hw with
    hwouter | hwinner
  · have hwsphere : w ∈ Metric.sphere (0 : ℂ) R := by
      rw [← frontier_ball 0 hR.ne']
      exact hwouter.1
    have hwnorm : ‖w‖ = R := by
      simpa only [Metric.mem_sphere, dist_zero_right] using hwsphere
    apply hR₀
    simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      hwnorm, not_le]
    exact hR₀R
  · have hwfront :
        w ∈ frontier (Metric.cthickening δ E) := by
      simpa only [frontier_compl] using hwinner.2
    have hwδ : w ∈ Metric.cthickening δ E := by
      have := frontier_subset_closure hwfront
      rwa [Metric.isClosed_cthickening.closure_eq] at this
    have hwr : w ∈ Metric.cthickening r E :=
      Metric.cthickening_mono hδr E hwδ
    have hw_not_E : w ∉ E := by
      intro hwE
      have hwthick :
          w ∈ Metric.thickening δ E :=
        Metric.self_subset_thickening hδ E hwE
      exact (hclosureU (frontier_subset_closure hw)) hwthick
    apply norm_polygonalCapacityFunction_le_one_of_fraction
    exact
      norm_polygonalFraction_le_twentyFive_of_mem_cthickening
        hN hr htrace hu hv hw_not_E hwr

/-- Endpoint square-root germ expressed in the inverse coordinate based at
the terminal vertex. -/
def endpointRootGerm (u v s : ℂ) : ℂ :=
  Complex.sqrt (1 + (u - v) * s)

def endpointCapacityGerm (u v s : ℂ) : ℂ :=
  ((endpointRootGerm u v s - 1) /
      (endpointRootGerm u v s + 1)) / 25

/-- The fixed germ whose rescalings give all endpoint capacity germs. -/
def baseCapacityGerm (s : ℂ) : ℂ :=
  ((Complex.sqrt (1 + s) - 1) /
      (Complex.sqrt (1 + s) + 1)) / 25

theorem endpointCapacityGerm_eq_baseCapacityGerm
    (u v s : ℂ) :
    endpointCapacityGerm u v s =
      baseCapacityGerm ((u - v) * s) := by
  rfl

theorem baseCapacityGerm_zero :
    baseCapacityGerm 0 = 0 := by
  simp [baseCapacityGerm]

theorem analyticAt_baseCapacityGerm :
    AnalyticAt ℂ baseCapacityGerm 0 := by
  have hsqrt :
      AnalyticAt ℂ Complex.sqrt 1 :=
    Complex.differentiableOn_sqrt.analyticOnNhd
      Complex.isOpen_slitPlane 1 Complex.one_mem_slitPlane
  have hinner :
      AnalyticAt ℂ (fun s : ℂ ↦ 1 + s) 0 :=
    AnalyticAt.fun_add analyticAt_const analyticAt_id
  have hroot :
      AnalyticAt ℂ (fun s : ℂ ↦ Complex.sqrt (1 + s)) 0 := by
    change
      AnalyticAt ℂ
        (Complex.sqrt ∘ fun s : ℂ ↦ 1 + s) 0
    exact hsqrt.comp_of_eq hinner (by norm_num)
  unfold baseCapacityGerm
  exact
    ((hroot.sub analyticAt_const).div
      (hroot.add analyticAt_const) (by norm_num)).div_const

theorem deriv_baseCapacityGerm :
    deriv baseCapacityGerm 0 = 1 / 100 := by
  let root : ℂ → ℂ :=
    fun s ↦ Complex.sqrt (1 + s)
  have hinnerDiff :
      DifferentiableAt ℂ (fun s : ℂ ↦ 1 + s) 0 :=
    ((hasDerivAt_id (𝕜 := ℂ) (x := 0)).const_add 1).differentiableAt
  have hrootDiff : DifferentiableAt ℂ root 0 := by
    change
      DifferentiableAt ℂ
        (Complex.sqrt ∘ fun s : ℂ ↦ 1 + s) 0
    apply
      (Complex.differentiableAt_sqrt
        (by simp)).comp 0
    exact hinnerDiff
  have hrootDeriv : deriv root 0 = 1 / 2 := by
    change
      deriv
        (Complex.sqrt ∘ fun s : ℂ ↦ 1 + s) 0 =
          1 / 2
    rw [deriv_comp 0
      (Complex.differentiableAt_sqrt
        (by simp))
      hinnerDiff]
    rw [Complex.deriv_sqrt
      (by simp), deriv_const_add, deriv_id'']
    norm_num
  change
    deriv
      (fun s : ℂ ↦
        ((root s - 1) / (root s + 1)) / 25) 0 =
      1 / 100
  rw [deriv_div_const]
  rw [deriv_fun_div (hrootDiff.sub_const 1)
    (hrootDiff.add_const 1) (by norm_num [root])]
  rw [deriv_sub_const, deriv_add_const, hrootDeriv]
  norm_num [root]

theorem deriv_baseCapacityGerm_ne_zero :
    deriv baseCapacityGerm 0 ≠ 0 := by
  rw [deriv_baseCapacityGerm]
  norm_num

theorem tendsto_endpointRoot_cocompact
    (u v : ℂ) :
    Tendsto
      (fun z ↦ endpointRootGerm u v (v - z)⁻¹)
      (cocompact ℂ) (𝓝 1) := by
  have hinv :
      Tendsto (fun z : ℂ ↦ (v - z)⁻¹)
        (cocompact ℂ) (𝓝 0) := by
    rw [← Metric.cobounded_eq_cocompact]
    exact Filter.tendsto_inv₀_cobounded.comp
      (tendsto_const_sub_cobounded v)
  have harg :
      Tendsto
        (fun z : ℂ ↦ 1 + (u - v) * (v - z)⁻¹)
        (cocompact ℂ) (𝓝 1) := by
    simpa only [mul_zero, add_zero] using
      tendsto_const_nhds.add (tendsto_const_nhds.mul hinv)
  change
    Tendsto
      (fun z ↦ Complex.sqrt
        (1 + (u - v) * (v - z)⁻¹))
      (cocompact ℂ) (𝓝 1)
  convert
    (Complex.continuousAt_sqrt (by left; norm_num)).tendsto.comp
      harg using 1 <;>
    simp [Function.comp_def]

/-- On the controlled exterior, the polygonal root product is the
principal endpoint square-root germ.  The sign is fixed by the common
limit `1` at infinity. -/
theorem polygonalRootProduct_eq_endpointRootGerm
    {p : ℕ → ℂ} {N : ℕ} (hN : 0 < N)
    {x : ℂ} {r : ℝ} (hr : 0 < r)
    (htrace :
      polygonalTrace p N ⊆ Metric.closedBall x (3 * r))
    (hu : dist x (p 0) < r)
    (hv : dist x (p N) = 3 * r) :
    EqOn
      (polygonalRootProduct p N)
      (fun z ↦ endpointRootGerm (p 0) (p N)
        (p N - z)⁻¹)
      ((Metric.closedBall (p N) (6 * r))ᶜ) := by
  let V : Set ℂ :=
    (Metric.closedBall (p N) (6 * r))ᶜ
  let S : ℂ → ℂ := polygonalRootProduct p N
  let T : ℂ → ℂ :=
    fun z ↦ endpointRootGerm (p 0) (p N)
      (p N - z)⁻¹
  have hdistEndpoints : dist (p 0) (p N) < 4 * r := by
    calc
      dist (p 0) (p N) ≤
          dist (p 0) x + dist x (p N) :=
        dist_triangle _ _ _
      _ < r + 3 * r := by
        rw [hv]
        have hu' : dist (p 0) x < r := by
          simpa only [dist_comm] using hu
        linarith
      _ = 4 * r := by ring
  have htraceV :
      polygonalTrace p N ⊆ Metric.closedBall (p N) (6 * r) := by
    intro w hw
    have hwx : dist w x ≤ 3 * r := by
      simpa only [Metric.mem_closedBall] using htrace hw
    rw [Metric.mem_closedBall]
    calc
      dist w (p N) ≤ dist w x + dist x (p N) :=
        dist_triangle _ _ _
      _ ≤ 3 * r + 3 * r := by rw [hv]; gcongr
      _ = 6 * r := by ring
  have hV_not_trace {z : ℂ} (hz : z ∈ V) :
      z ∉ polygonalTrace p N := by
    intro hzE
    exact hz (htraceV hzE)
  have hfar {z : ℂ} (hz : z ∈ V) :
      6 * r < dist z (p N) := by
    simpa only [V, mem_compl_iff, Metric.mem_closedBall,
      not_le] using hz
  have hperturb {z : ℂ} (hz : z ∈ V) :
      ‖(p 0 - p N) * (p N - z)⁻¹‖ < 1 := by
    have hzpos : 0 < dist (p N) z :=
      (by
        rw [dist_comm]
        exact (by positivity : 0 < 6 * r).trans (hfar hz))
    rw [norm_mul, norm_inv]
    rw [show ‖p 0 - p N‖ = dist (p 0) (p N) by
      rw [dist_eq_norm],
      show ‖p N - z‖ = dist (p N) z by rw [dist_eq_norm]]
    rw [← div_eq_mul_inv]
    exact
      (div_lt_one hzpos).2
        (hdistEndpoints.trans (by
          rw [dist_comm]
          linarith [hfar hz]))
  have hScontinuous : ContinuousOn S V := by
    intro z hz
    exact
      (continuousAt_polygonalRootProduct
        (hV_not_trace hz)).continuousWithinAt
  have hTcontinuous : ContinuousOn T V := by
    intro z hz
    have hslit :
        1 + (p 0 - p N) * (p N - z)⁻¹ ∈
          Complex.slitPlane :=
      Complex.mem_slitPlane_of_norm_lt_one (hperturb hz)
    change
      ContinuousWithinAt
        (fun z ↦ Complex.sqrt
          (1 + (p 0 - p N) * (p N - z)⁻¹)) V z
    have hzne : p N - z ≠ 0 := by
      rw [sub_ne_zero]
      intro heq
      have hf := hfar hz
      rw [← heq, dist_self] at hf
      linarith
    have hinner :
        ContinuousAt
          (fun z ↦ 1 + (p 0 - p N) * (p N - z)⁻¹) z := by
      fun_prop
    have hsqrt :
        ContinuousAt Complex.sqrt
          (1 + (p 0 - p N) * (p N - z)⁻¹) :=
      Complex.continuousAt_sqrt (hslit.imp le_of_lt id)
    exact
      (ContinuousAt.comp' (f := fun z ↦
          1 + (p 0 - p N) * (p N - z)⁻¹)
        hsqrt hinner).continuousWithinAt
  have hsquares : EqOn (S ^ 2) (T ^ 2) V := by
    intro z hz
    change S z ^ 2 = T z ^ 2
    rw [show S z ^ 2 =
        (z - p 0) / (z - p N) by
      exact polygonalRootProduct_sq hN (hV_not_trace hz)]
    rw [show T z ^ 2 =
        1 + (p 0 - p N) * (p N - z)⁻¹ by
      exact complex_sqrt_sq _]
    have hzN : z - p N ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      have hf := hfar hz
      rw [h, dist_self] at hf
      linarith
    have hNz : p N - z ≠ 0 := by
      rw [sub_ne_zero]
      exact (sub_ne_zero.mp hzN).symm
    field_simp [hzN, hNz]
    ring
  have hTne :
      ∀ {z : ℂ}, z ∈ V → T z ≠ 0 := by
    intro z hz hTz
    have hargzero :
        1 + (p 0 - p N) * (p N - z)⁻¹ = 0 := by
      rw [← complex_sqrt_sq
        (1 + (p 0 - p N) * (p N - z)⁻¹)]
      change T z ^ 2 = 0
      rw [hTz, zero_pow (by norm_num : 2 ≠ 0)]
    have hnormone :
        ‖(p 0 - p N) * (p N - z)⁻¹‖ = 1 := by
      have heq :
          (p 0 - p N) * (p N - z)⁻¹ = -1 := by
        linear_combination hargzero
      rw [heq]
      norm_num
    exact (ne_of_lt (hperturb hz)) hnormone
  have hVconnected : IsPreconnected V :=
    (isConnected_compl_closedBall_complex (p N) (6 * r)).isPreconnected
  rcases
      hVconnected.eq_or_eq_neg_of_sq_eq
        hScontinuous hTcontinuous hsquares hTne with
    hEq | hNeg
  · exact hEq
  · have hSclose :
        ∀ᶠ z : ℂ in cocompact ℂ, dist (S z) 1 < 1 / 2 := by
      exact
        tendsto_polygonalRootProduct_cocompact p N
          (Metric.ball_mem_nhds 1 (by norm_num))
    have hTclose :
        ∀ᶠ z : ℂ in cocompact ℂ, dist (T z) 1 < 1 / 2 := by
      exact
        tendsto_endpointRoot_cocompact (p 0) (p N)
          (Metric.ball_mem_nhds 1 (by norm_num))
    have hVevent : ∀ᶠ z : ℂ in cocompact ℂ, z ∈ V := by
      exact
        (isCompact_closedBall (p N) (6 * r)).compl_mem_cocompact
    obtain ⟨z, hzV, hzS, hzT⟩ :=
      (hVevent.and (hSclose.and hTclose)).exists
    have hneg : S z = -T z := by
      simpa only [Pi.neg_apply] using hNeg hzV
    have htwo :
        (2 : ℂ) = (1 - S z) + (1 - T z) := by
      rw [hneg]
      ring
    have hnorm :=
      norm_add_le (1 - S z) (1 - T z)
    rw [← htwo] at hnorm
    have hSdist : ‖1 - S z‖ = dist (S z) 1 := by
      rw [dist_eq_norm, norm_sub_rev]
    have hTdist : ‖1 - T z‖ = dist (T z) 1 := by
      rw [dist_eq_norm, norm_sub_rev]
    rw [hSdist, hTdist] at hnorm
    norm_num at hnorm
    linarith

/-- The corresponding normalized capacity function has the fixed endpoint
germ on the same controlled exterior. -/
theorem polygonalCapacityFunction_eq_endpointCapacityGerm
    {p : ℕ → ℂ} {N : ℕ} (hN : 0 < N)
    {x : ℂ} {r : ℝ} (hr : 0 < r)
    (htrace :
      polygonalTrace p N ⊆ Metric.closedBall x (3 * r))
    (hu : dist x (p 0) < r)
    (hv : dist x (p N) = 3 * r) :
    EqOn
      (polygonalCapacityFunction p N)
      (fun z ↦ endpointCapacityGerm (p 0) (p N)
        (p N - z)⁻¹)
      ((Metric.closedBall (p N) (6 * r))ᶜ) := by
  intro z hz
  unfold polygonalCapacityFunction polygonalFraction
    endpointCapacityGerm
  rw [polygonalRootProduct_eq_endpointRootGerm
    hN hr htrace hu hv hz]

/-- Taylor data for the one fixed germ used in every polygonal capacity
construction. -/
theorem exists_baseCapacityGerm_cubic_data :
    ∃ (c₂ : ℂ) (B ρ : ℝ),
      0 ≤ B ∧ 0 < ρ ∧
      ∀ s : ℂ, ‖s‖ ≤ ρ →
        ‖baseCapacityGerm s -
            (s * (1 / 100) + s ^ 2 * c₂)‖ ≤
          B * ‖s‖ ^ 3 := by
  obtain ⟨c₁, c₂, B, ρ, hB, hρ, hc₁, hTaylor⟩ :=
    exists_cubic_taylor_bound_of_analyticAt
      baseCapacityGerm analyticAt_baseCapacityGerm
        baseCapacityGerm_zero
  have hc₁' : c₁ = 1 / 100 := by
    rw [← hc₁, deriv_baseCapacityGerm]
  refine ⟨c₂, B, ρ, hB, hρ, ?_⟩
  intro s hs
  simpa only [hc₁'] using hTaylor s hs

end Submission.Helpers
