import Mathlib

namespace Submission.Helpers

open Set

/-- The ambient Euclidean space has rank greater than one in the range of
dimensions relevant to separation. -/
theorem euclidean_rank_gt_one (d : ℕ) (hd : 2 ≤ d) :
    1 < Module.rank ℝ (EuclideanSpace ℝ (Fin d)) := by
  rw [← Module.finrank_eq_rank, finrank_euclideanSpace_fin]
  exact_mod_cast hd

/-- A continuous image of the relevant Euclidean unit sphere is connected. -/
theorem sphere_range_connected (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) : IsConnected (Set.range r) := by
  letI : ConnectedSpace
      (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    isConnected_iff_connectedSpace.mp
      (isConnected_sphere (euclidean_rank_gt_one d hd) 0 (by positivity))
  exact isConnected_range hcont

/-- Outside a centered closed ball is path-connected in a real normed space
of rank greater than one. -/
theorem isPathConnected_norm_gt {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (hrank : 1 < Module.rank ℝ E) (R : ℝ) (hR : 0 ≤ R) :
    IsPathConnected {x : E | R < ‖x‖} := by
  let f : E → E := fun y ↦ ((R + ‖y‖) * ‖y‖⁻¹) • y
  have hf : ContinuousOn f ({0}ᶜ : Set E) := by
    intro y hy
    change ContinuousWithinAt
      (fun z : E ↦ ((R + ‖z‖) * ‖z‖⁻¹) • z) {0}ᶜ y
    exact (((continuousAt_const.add continuousAt_id.norm).mul
      (ContinuousAt.inv₀ continuousAt_id.norm (by simpa using hy))).smul
        continuousAt_id).continuousWithinAt
  have hdomain : IsPathConnected ({0}ᶜ : Set E) :=
    isPathConnected_compl_singleton_of_one_lt_rank hrank 0
  rw [← show f '' ({0}ᶜ : Set E) = {x : E | R < ‖x‖} by
    apply Set.Subset.antisymm
    · rintro _ ⟨y, hy, rfl⟩
      have hynorm : ‖y‖ ≠ 0 := by simpa using hy
      have hcoef : 0 ≤ (R + ‖y‖) * ‖y‖⁻¹ :=
        mul_nonneg (add_nonneg hR (norm_nonneg y))
          (inv_nonneg.mpr (norm_nonneg y))
      change R < ‖((R + ‖y‖) * ‖y‖⁻¹) • y‖
      rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hcoef]
      rw [mul_assoc, inv_mul_cancel₀ hynorm, mul_one]
      exact lt_add_of_pos_right R
        (lt_of_le_of_ne (norm_nonneg y) hynorm.symm)
    · intro x hx
      have hxnorm : ‖x‖ ≠ 0 := ne_of_gt (hR.trans_lt hx)
      let a : ℝ := (‖x‖ - R) * ‖x‖⁻¹
      have hxpos : 0 < ‖x‖ := lt_of_le_of_ne (norm_nonneg x) hxnorm.symm
      have ha : 0 < a := mul_pos (sub_pos.mpr hx) (inv_pos.mpr hxpos)
      refine ⟨a • x, ?_, ?_⟩
      · have hxzero : x ≠ 0 := norm_ne_zero_iff.mp hxnorm
        simpa only [mem_compl_iff, mem_singleton_iff] using
          smul_ne_zero ha.ne' hxzero
      · simp only [f, norm_smul, Real.norm_eq_abs, abs_of_pos ha]
        have hsub : ‖x‖ - R ≠ 0 := ne_of_gt (sub_pos.mpr hx)
        rw [smul_smul]
        rw [show ((R + a * ‖x‖) * (a * ‖x‖)⁻¹) * a = 1 by
          dsimp [a]
          field_simp [hsub, hxnorm]
          ring]
        exact one_smul ℝ x]
  exact hdomain.image' hf

/-- The compact image lies inside a ball whose exterior is path-connected and
is contained in the complementary region. -/
theorem exists_pathConnected_exterior_subset_compl (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) :
    ∃ R : ℝ, 0 < R ∧
      IsPathConnected {x : EuclideanSpace ℝ (Fin d) | R < ‖x‖} ∧
      {x : EuclideanSpace ℝ (Fin d) | R < ‖x‖} ⊆ (Set.range r)ᶜ := by
  obtain ⟨R, hbound⟩ :=
    (isCompact_range hcont).isBounded.subset_ball
      (0 : EuclideanSpace ℝ (Fin d))
  have hR : 0 < R := by
    obtain ⟨x, hx⟩ := (sphere_range_connected d hd r hcont).nonempty
    have hxball := hbound hx
    rw [Metric.mem_ball, dist_zero_right] at hxball
    exact (norm_nonneg x).trans_lt hxball
  refine ⟨R, hR,
    isPathConnected_norm_gt (euclidean_rank_gt_one d hd) R hR.le, ?_⟩
  intro x hx
  rw [Set.mem_compl_iff]
  intro hxrange
  have hxball := hbound hxrange
  rw [Metric.mem_ball, dist_zero_right] at hxball
  exact (not_lt_of_ge hx.le) hxball

/-- All sufficiently far-away points belong to one connected component of the
complementary region. -/
theorem exists_exterior_component (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) :
    ∃ (R : ℝ) (p : EuclideanSpace ℝ (Fin d)),
      0 < R ∧ p ∈ (Set.range r)ᶜ ∧
      {x : EuclideanSpace ℝ (Fin d) | R < ‖x‖} ⊆
        connectedComponentIn (Set.range r)ᶜ p := by
  obtain ⟨R, hR, hpath, hsubset⟩ :=
    exists_pathConnected_exterior_subset_compl d hd r hcont
  obtain ⟨p, hp⟩ := hpath.nonempty
  exact ⟨R, p, hR, hsubset hp,
    hpath.isConnected.isPreconnected.subset_connectedComponentIn hp hsubset⟩

/-- Beyond one radius, all points determine the same complementary connected
component. -/
theorem exists_radius_connectedComponentIn_eq (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) :
    ∃ R : ℝ, 0 < R ∧ ∀ x y : EuclideanSpace ℝ (Fin d),
      R < ‖x‖ → R < ‖y‖ →
      connectedComponentIn (Set.range r)ᶜ x =
        connectedComponentIn (Set.range r)ᶜ y := by
  obtain ⟨R, hR, hpath, hsubset⟩ :=
    exists_pathConnected_exterior_subset_compl d hd r hcont
  refine ⟨R, hR, ?_⟩
  intro x y hx hy
  apply connectedComponentIn_eq
  exact hpath.isConnected.isPreconnected.subset_connectedComponentIn hx hsubset hy

/-- Thus two unbounded complementary connected components cannot be
distinct. -/
theorem connectedComponentIn_eq_of_not_isBounded (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) {x y : EuclideanSpace ℝ (Fin d)}
    (hx : ¬ Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ x))
    (hy : ¬ Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ y)) :
    connectedComponentIn (Set.range r)ᶜ x =
      connectedComponentIn (Set.range r)ᶜ y := by
  obtain ⟨R, _hR, hfar⟩ :=
    exists_radius_connectedComponentIn_eq d hd r hcont
  have hxfar : ∃ z ∈ connectedComponentIn (Set.range r)ᶜ x, R < ‖z‖ := by
    by_contra h
    push Not at h
    apply hx
    exact isBounded_iff_forall_norm_le.2
      ⟨R, fun (z : EuclideanSpace ℝ (Fin d)) hz ↦ h z hz⟩
  have hyfar : ∃ z ∈ connectedComponentIn (Set.range r)ᶜ y, R < ‖z‖ := by
    by_contra h
    push Not at h
    apply hy
    exact isBounded_iff_forall_norm_le.2
      ⟨R, fun (z : EuclideanSpace ℝ (Fin d)) hz ↦ h z hz⟩
  obtain ⟨z, hzx, hzR⟩ := hxfar
  obtain ⟨w, hwy, hwR⟩ := hyfar
  exact (connectedComponentIn_eq hzx).trans
    ((hfar z w hzR hwR).trans (connectedComponentIn_eq hwy).symm)

/-- The component containing the exterior of a sufficiently large ball is
unbounded. -/
theorem exists_unbounded_connectedComponentIn (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) :
    ∃ p ∈ (Set.range r)ᶜ,
      ¬ Bornology.IsBounded (connectedComponentIn (Set.range r)ᶜ p) := by
  obtain ⟨R, p, hR, hp, hext⟩ :=
    exists_exterior_component d hd r hcont
  refine ⟨p, hp, ?_⟩
  intro hbounded
  obtain ⟨C, hC⟩ := isBounded_iff_forall_norm_le.mp hbounded
  obtain ⟨u, hu⟩ :=
    (isConnected_sphere (euclidean_rank_gt_one d hd) 0
      (show (0 : ℝ) ≤ 1 by norm_num)).nonempty
  letI : NontrivialTopology (EuclideanSpace ℝ (Fin d)) :=
    NontrivialTopology.of_exists_norm_ne_zero ⟨u, by
      rw [mem_sphere_zero_iff_norm] at hu
      simp [hu]⟩
  have htarget : 0 ≤ max R C + 1 := by
    linarith [le_max_left R C]
  obtain ⟨z, hz⟩ :=
    exists_norm_eq (EuclideanSpace ℝ (Fin d)) htarget
  have hzR : R < ‖z‖ := by
    rw [hz]
    linarith [le_max_left R C]
  have hzC : ‖z‖ ≤ C := hC z (hext hzR)
  rw [hz] at hzC
  linarith [le_max_right R C]

/-- A type split into exactly one witness satisfying a predicate and exactly
one witness not satisfying it has cardinality two. -/
theorem natCard_eq_two_of_predicate {α : Type*} (P : α → Prop)
    (hpos : ∃ x, P x) (hneg : ∃ x, ¬ P x)
    (hpos_unique : ∀ x y, P x → P y → x = y)
    (hneg_unique : ∀ x y, ¬ P x → ¬ P y → x = y) :
    Nat.card α = 2 := by
  classical
  let classify : α → Bool := fun x ↦ decide (P x)
  have hinjective : Function.Injective classify := by
    intro x y hxy
    by_cases hx : P x <;> by_cases hy : P y
    · exact hpos_unique x y hx hy
    · simp [classify, hx, hy] at hxy
    · simp [classify, hx, hy] at hxy
    · exact hneg_unique x y hx hy
  have hsurjective : Function.Surjective classify := by
    intro b
    cases b with
    | false =>
        obtain ⟨x, hx⟩ := hneg
        exact ⟨x, by simp [classify, hx]⟩
    | true =>
        obtain ⟨x, hx⟩ := hpos
        exact ⟨x, by simp [classify, hx]⟩
  calc
    Nat.card α = Nat.card Bool :=
      Nat.card_congr (Equiv.ofBijective classify ⟨hinjective, hsurjective⟩)
    _ = 2 := by simp

/-- If the complementary components consist of one bounded component and one
unbounded component, their connected-component quotient has cardinality two. -/
theorem natCard_connectedComponents_eq_two_of_bounded_partition
    {E : Type*} [TopologicalSpace E] [Bornology E] (s : Set E)
    (hbounded : ∃ x ∈ s,
      Bornology.IsBounded (connectedComponentIn s x))
    (hunbounded : ∃ x ∈ s,
      ¬ Bornology.IsBounded (connectedComponentIn s x))
    (hbounded_unique : ∀ x ∈ s, ∀ y ∈ s,
      Bornology.IsBounded (connectedComponentIn s x) →
      Bornology.IsBounded (connectedComponentIn s y) →
      connectedComponentIn s x = connectedComponentIn s y)
    (hunbounded_unique : ∀ x ∈ s, ∀ y ∈ s,
      ¬ Bornology.IsBounded (connectedComponentIn s x) →
      ¬ Bornology.IsBounded (connectedComponentIn s y) →
      connectedComponentIn s x = connectedComponentIn s y) :
    Nat.card (ConnectedComponents (s : Set E)) = 2 := by
  classical
  have hcomponent (x y : (s : Set E)) :
      (x : ConnectedComponents (s : Set E)) = y ↔
        connectedComponentIn s x = connectedComponentIn s y := by
    rw [ConnectedComponents.coe_eq_coe,
      connectedComponentIn_eq_image x.2, connectedComponentIn_eq_image y.2]
    constructor
    · exact fun h ↦ congrArg (fun t ↦ Subtype.val '' t) h
    · intro h
      exact (Set.image_injective.mpr Subtype.val_injective) h
  let P : ConnectedComponents (s : Set E) → Prop := fun c ↦
    ∃ x : (s : Set E),
      (x : ConnectedComponents (s : Set E)) = c ∧
        Bornology.IsBounded (connectedComponentIn s x)
  apply natCard_eq_two_of_predicate P
  · obtain ⟨x, hxs, hx⟩ := hbounded
    exact ⟨(⟨x, hxs⟩ : (s : Set E)), ⟨⟨x, hxs⟩, rfl, hx⟩⟩
  · obtain ⟨x, hxs, hx⟩ := hunbounded
    refine ⟨(⟨x, hxs⟩ : (s : Set E)), ?_⟩
    rintro ⟨y, hyc, hy⟩
    apply hx
    have heq : connectedComponentIn s y = connectedComponentIn s x :=
      (hcomponent y ⟨x, hxs⟩).mp hyc
    simpa only [heq] using hy
  · intro c e hc he
    obtain ⟨x, hxc, hx⟩ := hc
    obtain ⟨y, hye, hy⟩ := he
    have hxy : (x : ConnectedComponents (s : Set E)) = y :=
      (hcomponent x y).mpr
        (hbounded_unique x x.2 y y.2 hx hy)
    exact hxc.symm.trans (hxy.trans hye)
  · intro c e hc he
    obtain ⟨x, hxc⟩ := ConnectedComponents.surjective_coe c
    obtain ⟨y, hye⟩ := ConnectedComponents.surjective_coe e
    have hx : ¬ Bornology.IsBounded (connectedComponentIn s x) :=
      fun hx ↦ hc ⟨x, hxc, hx⟩
    have hy : ¬ Bornology.IsBounded (connectedComponentIn s y) :=
      fun hy ↦ he ⟨y, hye, hy⟩
    have hxy : (x : ConnectedComponents (s : Set E)) = y :=
      (hcomponent x y).mpr
        (hunbounded_unique x x.2 y y.2 hx hy)
    exact hxc.symm.trans (hxy.trans hye)

/-- A two-piece clopen connected partition computes the number of connected
components without requiring a separately supplied finiteness instance. -/
theorem natCard_connectedComponents_eq_two_of_partition
    {α : Type*} [TopologicalSpace α] (U : Fin 2 → Set α)
    (hclopen : ∀ i, IsClopen (U i))
    (hdisjoint : Pairwise (Function.onFun Disjoint U))
    (hcover : ⋃ i, U i = Set.univ)
    (hconnected : ∀ i, IsConnected (U i)) :
    Nat.card (ConnectedComponents α) = 2 := by
  calc
    Nat.card (ConnectedComponents α) = Nat.card (Fin 2) :=
      Nat.card_congr
        (ConnectedComponents.equivOfIsClopenOfIsConnected
          hclopen hdisjoint hcover hconnected)
    _ = 2 := by simp

/-- It is enough to exhibit one clopen connected component whose complement
is connected. -/
theorem natCard_connectedComponents_eq_two_of_component
    {α : Type*} [TopologicalSpace α] (p : α)
    (hclopen : IsClopen (connectedComponent p))
    (hother : IsConnected (connectedComponent p)ᶜ) :
    Nat.card (ConnectedComponents α) = 2 := by
  let U : Fin 2 → Set α := ![connectedComponent p, (connectedComponent p)ᶜ]
  apply natCard_connectedComponents_eq_two_of_partition U
  · intro i
    fin_cases i
    · simpa [U] using hclopen
    · simpa [U] using hclopen.compl
  · intro i j hij
    fin_cases i <;> fin_cases j
    · exact (hij rfl).elim
    · change Disjoint (connectedComponent p) (connectedComponent p)ᶜ
      exact disjoint_compl_right
    · change Disjoint (connectedComponent p)ᶜ (connectedComponent p)
      exact disjoint_compl_left
    · exact (hij rfl).elim
  · ext x
    simp [U]
    exact Classical.em _
  · intro i
    fin_cases i
    · simpa [U] using (isConnected_connectedComponent (x := p))
    · simpa [U] using hother

/-- A continuous injection of the finite-dimensional unit sphere is a closed
embedding, since its domain is compact and Euclidean space is Hausdorff. -/
theorem sphere_isClosedEmbedding (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Topology.IsClosedEmbedding r :=
  hcont.isClosedEmbedding hinj

/-- The image of a continuous sphere injection is closed. -/
theorem isClosed_range_sphere_embedding (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    IsClosed (Set.range r) :=
  (sphere_isClosedEmbedding d r hcont hinj).isClosed_range

/-- Consequently, the complementary region in Jordan–Brouwer is open. -/
theorem isOpen_compl_range_sphere_embedding (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    IsOpen (Set.range r)ᶜ :=
  (isClosed_range_sphere_embedding d r hcont hinj).isOpen_compl

/-- The open complement is locally path-connected; hence its connected
components agree with its path components and are clopen. -/
theorem locPathConnectedSpace_compl_range_sphere_embedding (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    LocPathConnectedSpace
      ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))) :=
  (isOpen_compl_range_sphere_embedding d r hcont hinj).locPathConnectedSpace

end Submission.Helpers
