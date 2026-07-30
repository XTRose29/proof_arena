import Submission.Separation
import Submission.JordanHelpers

open Function Set Topology

namespace Submission.ArcSeparation

noncomputable section

/-- A bounded open planar region disjoint from a simple arc cannot have all
of its frontier contained in that arc.  The nonvanishing function `z - x`
has a logarithm along the arc; extending that logarithm contradicts the
winding obstruction for a bounded region. -/
theorem not_frontier_subset_range_simple_arc
    {a b : ℂ} (α : Path a b) (hα : Injective α)
    (U : Set ℂ) (hU : IsOpen U) (hUb : Bornology.IsBounded U)
    (hUne : U.Nonempty) (hdisj : Disjoint U (range α))
    (hfront : frontier U ⊆ range α) :
    False := by
  obtain ⟨x, hxU⟩ := hUne
  let g : C(unitInterval, ℂ) :=
    α.toContinuousMap - ContinuousMap.const unitInterval x
  have hg0 (t : unitInterval) : g t ≠ 0 := by
    intro hzero
    have hat : α t = x := sub_eq_zero.mp hzero
    exact
      Set.disjoint_left.1 hdisj hxU
        ⟨t, hat⟩
  letI : ContractibleSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).contractibleSpace
      ⟨0, by norm_num⟩
  letI : LocPathConnectedSpace unitInterval :=
    (convex_Icc (0 : ℝ) 1).locPathConnectedSpace
  obtain ⟨L, hL, _hLunique⟩ :=
    Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts g
      (a₀ := (0 : unitInterval)) (e₀ := Complex.log (g 0))
      (Complex.exp_log (hg0 0)) (fun t ↦ hg0 t)
  have hLexp (t : unitInterval) :
      Complex.exp (L t) = g t := by
    exact congrFun hL.2 t
  have hαclosed : IsClosedEmbedding α :=
    α.continuous.isClosedEmbedding hα
  obtain ⟨Q, hQ⟩ := L.exists_extension hαclosed
  let F : ℂ → ℂ := fun z ↦ Complex.exp (Q z)
  apply
    Separation.no_nonzero_extension_over_bounded_open
      U hU hUb x hxU 1 one_ne_zero F
  · exact Q.continuous.cexp.continuousOn
  · intro z _hz
    exact Complex.exp_ne_zero _
  · intro z hz
    obtain ⟨t, rfl⟩ := hfront hz
    have hQt : Q (α t) = L t :=
      DFunLike.congr_fun hQ t
    calc
      F (α t) = Complex.exp (L t) := by
        dsimp only [F]
        rw [hQt]
      _ = g t := hLexp t
      _ = (α t - x) ^ (1 : ℤ) := by
        simp [g]

/-- The frontier of a complementary component of a planar arc is contained
in the arc. -/
theorem frontier_component_subset_range
    {a b : ℂ} (α : Path a b) {x : ℂ}
    (_hx : x ∈ (range α)ᶜ) :
    frontier (connectedComponentIn (range α)ᶜ x) ⊆ range α := by
  have hopenCompl : IsOpen (range α)ᶜ :=
    (isCompact_range α.continuous).isClosed.isOpen_compl
  have hopenComponent (z : ℂ) :
      IsOpen (connectedComponentIn (range α)ᶜ z) :=
    hopenCompl.connectedComponentIn
  intro y hy
  by_contra hyr
  have hyCompl : y ∈ (range α)ᶜ := hyr
  have hyNot : y ∉ connectedComponentIn (range α)ᶜ x := by
    intro hyx
    exact hy.2
      (mem_interior_iff_mem_nhds.mpr
        (IsOpen.mem_nhds (hopenComponent x) hyx))
  have hySelf : y ∈ connectedComponentIn (range α)ᶜ y :=
    mem_connectedComponentIn hyCompl
  obtain ⟨z, hzy, hzx⟩ :=
    mem_closure_iff.mp hy.1
      (connectedComponentIn (range α)ᶜ y)
      (hopenComponent y) hySelf
  have hyz :
      connectedComponentIn (range α)ᶜ y =
        connectedComponentIn (range α)ᶜ z :=
    connectedComponentIn_eq hzy
  have hxz :
      connectedComponentIn (range α)ᶜ x =
        connectedComponentIn (range α)ᶜ z :=
    connectedComponentIn_eq hzx
  have hyx :
      connectedComponentIn (range α)ᶜ y =
        connectedComponentIn (range α)ᶜ x :=
    hyz.trans hxz.symm
  exact hyNot (hyx ▸ hySelf)

/-- Every complementary component of a simple planar arc is unbounded. -/
theorem component_not_isBounded
    {a b : ℂ} (α : Path a b) (hα : Injective α)
    {x : ℂ} (hx : x ∈ (range α)ᶜ) :
    ¬ Bornology.IsBounded
      (connectedComponentIn (range α)ᶜ x) := by
  intro hbounded
  let U : Set ℂ := connectedComponentIn (range α)ᶜ x
  have hUopen : IsOpen U :=
    (isCompact_range α.continuous).isClosed.isOpen_compl
      |>.connectedComponentIn
  have hUne : U.Nonempty :=
    ⟨x, mem_connectedComponentIn hx⟩
  have hdisj : Disjoint U (range α) := by
    exact Set.disjoint_left.2 fun _ hyU hyα ↦
      (connectedComponentIn_subset (range α)ᶜ x hyU) hyα
  exact
    not_frontier_subset_range_simple_arc
      α hα U hUopen hbounded hUne hdisj
        (frontier_component_subset_range α hx)

/-- All points outside a simple planar arc belong to the same complementary
component. -/
theorem connectedComponentIn_compl_range_eq
    {a b : ℂ} (α : Path a b) (hα : Injective α)
    {x y : ℂ} (hx : x ∈ (range α)ᶜ) (hy : y ∈ (range α)ᶜ) :
    connectedComponentIn (range α)ᶜ x =
      connectedComponentIn (range α)ᶜ y := by
  have hxUnbounded := component_not_isBounded α hα hx
  have hyUnbounded := component_not_isBounded α hα hy
  obtain ⟨R, hRsub⟩ :=
    (isCompact_range α.continuous).isBounded.subset_ball (0 : ℂ)
  have hR : 0 < R := by
    have hmem := hRsub (⟨(0 : unitInterval), rfl⟩ : α 0 ∈ range α)
    rw [Metric.mem_ball, dist_zero_right] at hmem
    exact (norm_nonneg (α 0)).trans_lt hmem
  have houtside : {z : ℂ | R < ‖z‖} ⊆ (range α)ᶜ := by
    intro z hz hzRange
    have hzBall := hRsub hzRange
    rw [Metric.mem_ball, dist_zero_right] at hzBall
    exact (not_lt_of_ge hz.le) hzBall
  have houtsideConnected : IsPathConnected {z : ℂ | R < ‖z‖} :=
    JordanHelpers.isPathConnected_norm_gt
      (E := ℂ) (by rw [Complex.rank_real_complex]; norm_num) R hR.le
  have hxFar :
      ∃ z ∈ connectedComponentIn (range α)ᶜ x, R < ‖z‖ := by
    by_contra h
    push Not at h
    apply hxUnbounded
    exact
      (isBounded_iff_forall_norm_le
        (s := connectedComponentIn (range α)ᶜ x)).2
          ⟨R, fun z hz ↦ h z hz⟩
  have hyFar :
      ∃ z ∈ connectedComponentIn (range α)ᶜ y, R < ‖z‖ := by
    by_contra h
    push Not at h
    apply hyUnbounded
    exact
      (isBounded_iff_forall_norm_le
        (s := connectedComponentIn (range α)ᶜ y)).2
          ⟨R, fun z hz ↦ h z hz⟩
  obtain ⟨z, hzx, hzR⟩ := hxFar
  obtain ⟨w, hwy, hwR⟩ := hyFar
  have hzw :
      connectedComponentIn (range α)ᶜ z =
        connectedComponentIn (range α)ᶜ w := by
    apply connectedComponentIn_eq
    exact
      houtsideConnected.isConnected.isPreconnected
        |>.subset_connectedComponentIn hzR houtside hwR
  exact
    (connectedComponentIn_eq hzx).trans
      (hzw.trans (connectedComponentIn_eq hwy).symm)

/-- The complement of a simple planar arc is preconnected. -/
theorem isPreconnected_compl_range
    {a b : ℂ} (α : Path a b) (hα : Injective α) :
    IsPreconnected (range α)ᶜ := by
  obtain ⟨R, hRsub⟩ :=
    (isCompact_range α.continuous).isBounded.subset_ball (0 : ℂ)
  have hR : 0 < R := by
    have hmem := hRsub (⟨(0 : unitInterval), rfl⟩ : α 0 ∈ range α)
    rw [Metric.mem_ball, dist_zero_right] at hmem
    exact (norm_nonneg (α 0)).trans_lt hmem
  let x : ℂ := (R + 1 : ℝ)
  have hxNorm : ‖x‖ = R + 1 := by
    change ‖((R + 1 : ℝ) : ℂ)‖ = R + 1
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : 0 < R + 1)]
  have hx : x ∈ (range α)ᶜ := by
    intro hxRange
    have hxBall := hRsub hxRange
    rw [Metric.mem_ball, dist_zero_right, hxNorm] at hxBall
    linarith
  have hcomponent :
      connectedComponentIn (range α)ᶜ x = (range α)ᶜ := by
    apply Subset.antisymm
    · exact connectedComponentIn_subset (range α)ᶜ x
    · intro y hy
      have hxy := connectedComponentIn_compl_range_eq α hα hx hy
      rw [hxy]
      exact mem_connectedComponentIn hy
  rw [← hcomponent]
  exact isPreconnected_connectedComponentIn

end

end Submission.ArcSeparation
