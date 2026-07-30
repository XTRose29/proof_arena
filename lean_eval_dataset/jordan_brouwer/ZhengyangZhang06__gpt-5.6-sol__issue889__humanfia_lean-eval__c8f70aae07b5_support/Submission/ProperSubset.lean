import Submission.DimensionAvoidance
import Submission.Components
import Submission.BoundedGauss

namespace Submission.Helpers

open Set

noncomputable section

/-- Sphere-valued data on a compact space embedded in a strict subspace
extends over that whole subspace. -/
theorem exists_sphere_extension_of_compact_embedding_submodule
    {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (d : ℕ) (P : Submodule ℝ (EuclideanSpace ℝ (Fin d))) (hP : P ≠ ⊤)
    (e : C(X, P)) (he : Function.Injective e)
    (h : C(X, Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    ∃ H : C(P, Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
      ∀ x, H (e x) = h x := by
  let E := EuclideanSpace ℝ (Fin d)
  let eE : C(X, E) :=
    { toFun := fun x ↦ (e x : E)
      continuous_toFun := continuous_subtype_val.comp e.continuous }
  have heE : Function.Injective eE := by
    intro x y hxy
    apply he
    exact Subtype.ext hxy
  have heClosed : Topology.IsClosedEmbedding eE :=
    eE.continuous.isClosedEmbedding heE
  let s : Set E := Set.range eE
  let es : X ≃ₜ s := heClosed.isEmbedding.toHomeomorph
  let hs : C(s, Metric.sphere (0 : E) 1) :=
    { toFun := fun y ↦ h (es.symm y)
      continuous_toFun := h.continuous.comp es.symm.continuous }
  have hsCompact : IsCompact s := isCompact_range eE.continuous
  have hsP : s ⊆ (P : Set E) := by
    rintro _ ⟨x, rfl⟩
    exact (e x).2
  obtain ⟨H, hH⟩ :=
    exists_sphere_extension_of_compact_subset_submodule
      d P hP s hsCompact hsP hs
  refine ⟨H, ?_⟩
  intro x
  have hx := hH (es x)
  simpa [es, hs, s, eE] using hx

/-- Sphere-valued data on a compact proper subset of the unit sphere extends
over the closed unit ball.  Stereographic projection puts the compact set in
a strict hyperplane; Tietze extension of its coordinates then transports the
lower-dimensional extension back across the ball. -/
theorem exists_closedBall_extension_of_compact_proper_sphere_subset
    (d : ℕ)
    (k : Set (Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hkCompact : IsCompact k) (hkProper : k ≠ Set.univ)
    (h : C(k, Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    ∃ H : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
        Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
      ∀ z : k, H (unitSphereClosedBallInclusion d z.1) = h z := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let S := Metric.sphere (0 : E) 1
  letI : CompactSpace k := isCompact_iff_compactSpace.mp hkCompact
  obtain ⟨v, hvk⟩ := (Set.ne_univ_iff_exists_notMem k).mp hkProper
  have hvNorm : ‖(v : E)‖ = 1 := mem_sphere_zero_iff_norm.mp v.2
  let P : Submodule ℝ E := (ℝ ∙ (v : E))ᗮ
  have hP : P ≠ ⊤ := by
    intro htop
    have hvP : (v : E) ∈ P := by
      rw [htop]
      exact Set.mem_univ _
    have hvInner : inner ℝ (v : E) (v : E) = 0 := by
      exact Submodule.mem_orthogonal_singleton_iff_inner_right.mp hvP
    rw [real_inner_self_eq_norm_sq, hvNorm] at hvInner
    norm_num at hvInner
  have hkSource : k ⊆ (stereographic hvNorm).source := by
    intro z hz
    rw [stereographic_source, Set.mem_compl_iff,
      Set.mem_singleton_iff]
    intro hzv
    have hzv' : z = v := by
      apply Subtype.ext
      exact congrArg Subtype.val hzv
    exact hvk (hzv' ▸ hz)
  let coords : C(k, P) :=
    { toFun := fun z ↦ stereographic hvNorm z.1
      continuous_toFun :=
        continuousOn_iff_continuous_restrict.mp
          ((stereographic hvNorm).continuousOn.mono hkSource) }
  have hcoords : Function.Injective coords := by
    intro x y hxy
    apply Subtype.ext
    exact (stereographic hvNorm).injOn
      (hkSource x.2) (hkSource y.2) hxy
  obtain ⟨HP, hHP⟩ :=
    exists_sphere_extension_of_compact_embedding_submodule
      d P hP coords hcoords h
  let inclusion : C(k, Metric.closedBall (0 : E) 1) :=
    { toFun := fun z ↦ unitSphereClosedBallInclusion d z.1
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact continuous_subtype_val.comp continuous_subtype_val }
  have hinclusion : Function.Injective inclusion := by
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    have hambient := congrArg Subtype.val hxy
    simpa [inclusion, unitSphereClosedBallInclusion] using hambient
  have hinclusionClosed : Topology.IsClosedEmbedding inclusion :=
    inclusion.continuous.isClosedEmbedding hinclusion
  obtain ⟨Q, hQ⟩ := coords.exists_extension hinclusionClosed
  let H := HP.comp Q
  refine ⟨H, ?_⟩
  intro z
  have hQz : Q (inclusion z) = coords z := by
    exact DFunLike.congr_fun hQ z
  change HP (Q (inclusion z)) = h z
  rw [hQz]
  exact hHP z

/-- If a compact set separates the relevant Euclidean space, one of its
complementary components is bounded. -/
theorem exists_bounded_component_of_compact_separator (d : ℕ) (hd : 2 ≤ d)
    (k : Set (EuclideanSpace ℝ (Fin d))) (hkCompact : IsCompact k)
    (hseparates : ¬ IsPreconnected kᶜ) :
    ∃ x ∈ kᶜ, Bornology.IsBounded (connectedComponentIn kᶜ x) := by
  let E := EuclideanSpace ℝ (Fin d)
  obtain ⟨R, hkBall⟩ := hkCompact.isBounded.subset_ball (0 : E)
  let R' : ℝ := max R 0 + 1
  have hR' : 0 < R' := by
    dsimp [R']
    linarith [le_max_right R 0]
  let exterior : Set E := {x | R' < ‖x‖}
  have hExteriorPath : IsPathConnected exterior :=
    isPathConnected_norm_gt (euclidean_rank_gt_one d hd) R' hR'.le
  have hExteriorCompl : exterior ⊆ kᶜ := by
    intro x hx
    rw [Set.mem_compl_iff]
    intro hxk
    have hxBall := hkBall hxk
    rw [Metric.mem_ball, dist_zero_right] at hxBall
    have hRR' : R < R' := by
      dsimp [R']
      linarith [le_max_left R 0]
    exact (not_lt_of_ge hx.le) (hxBall.trans hRR')
  obtain ⟨p, hpExterior⟩ := hExteriorPath.nonempty
  have hp : p ∈ kᶜ := hExteriorCompl hpExterior
  have hExteriorComponent : exterior ⊆ connectedComponentIn kᶜ p :=
    hExteriorPath.isConnected.isPreconnected.subset_connectedComponentIn
      hpExterior hExteriorCompl
  have hothers (x : E) (hx : x ∈ kᶜ)
      (hxne : connectedComponentIn kᶜ x ≠ connectedComponentIn kᶜ p) :
      Bornology.IsBounded (connectedComponentIn kᶜ x) := by
    by_contra hxUnbounded
    have hxfar : ∃ z ∈ connectedComponentIn kᶜ x, R' < ‖z‖ := by
      by_contra hfar
      push Not at hfar
      apply hxUnbounded
      exact isBounded_iff_forall_norm_le.2
        ⟨R', fun z hz ↦ hfar z hz⟩
    obtain ⟨z, hzx, hzExterior⟩ := hxfar
    apply hxne
    exact (connectedComponentIn_eq hzx).trans
      (connectedComponentIn_eq (hExteriorComponent hzExterior)).symm
  obtain ⟨x, hx, y, hy, hxy⟩ :=
    (exists_two_connectedComponents_iff_not_isPreconnected
      ⟨p, hp⟩).2 hseparates
  by_cases hxp : connectedComponentIn kᶜ x = connectedComponentIn kᶜ p
  · refine ⟨y, hy, hothers y hy ?_⟩
    intro hyp
    exact hxy (hxp.trans hyp.symm)
  · exact ⟨x, hx, hothers x hx hxp⟩

/-- No compact proper subset of an embedded sphere separates the ambient
Euclidean space. -/
theorem isPreconnected_compl_compact_proper_subset_sphere_range
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (k : Set (EuclideanSpace ℝ (Fin d))) (hkCompact : IsCompact k)
    (hkRange : k ⊆ Set.range r) (hkProper : k ≠ Set.range r) :
    IsPreconnected kᶜ := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let S := Metric.sphere (0 : E) 1
  by_contra hseparates
  obtain ⟨x, hx, hxBounded⟩ :=
    exists_bounded_component_of_compact_separator
      d hd k hkCompact hseparates
  let U : Set E := connectedComponentIn kᶜ x
  have hxU : x ∈ U := mem_connectedComponentIn hx
  have hUOpen : IsOpen U := hkCompact.isClosed.isOpen_compl.connectedComponentIn
  have hfrontK : frontier U ⊆ k := by
    simpa only [U, compl_compl] using
      frontier_connectedComponentIn_subset_compl
        hkCompact.isClosed.isOpen_compl x
  let ks : Set S := r ⁻¹' frontier U
  have hksClosed : IsClosed ks := isClosed_frontier.preimage hcont
  have hksCompact : IsCompact ks := hksClosed.isCompact
  have hrangeNotSubset : ¬ Set.range r ⊆ k := by
    intro hrangeK
    exact hkProper (Set.Subset.antisymm hkRange hrangeK)
  obtain ⟨_y, ⟨z, rfl⟩, hzk⟩ := Set.not_subset.mp hrangeNotSubset
  have hzks : z ∉ ks := by
    intro hzfront
    exact hzk (hfrontK hzfront)
  have hksProper : ks ≠ Set.univ :=
    (Set.ne_univ_iff_exists_notMem ks).2 ⟨z, hzks⟩
  have hvector (w : ks) : r w.1 - x ≠ 0 := by
    rw [sub_ne_zero]
    intro hwx
    exact hx (hwx ▸ hfrontK w.2)
  let boundaryDirection : C(ks, S) :=
    { toFun := fun w ↦ ⟨NormedSpace.normalize (r w.1 - x), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize (hvector w)⟩
      continuous_toFun := by
        have hval : Continuous (fun w : ks ↦ (w.1 : S)) :=
          continuous_subtype_val
        have hr : Continuous (fun w : ks ↦ r w.1) := hcont.comp hval
        have hv : Continuous (fun w : ks ↦ r w.1 - x) :=
          hr.sub continuous_const
        apply Continuous.subtype_mk
        change Continuous (fun w : ks ↦ ‖r w.1 - x‖⁻¹ • (r w.1 - x))
        exact (hv.norm.inv₀ fun w ↦
          norm_ne_zero_iff.mpr (hvector w)).smul hv }
  obtain ⟨G, hG⟩ :=
    exists_closedBall_extension_of_compact_proper_sphere_subset
      d ks hksCompact hksProper boundaryDirection
  obtain ⟨f, hf, hfle, _hflt⟩ :=
    exists_strict_unitBall_extension d hd r hcont hinj
  let fBall : C(E, Metric.closedBall (0 : E) 1) :=
    { toFun := fun y ↦ ⟨f y, by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hfle y⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact f.continuous }
  let direction : C(E, S) := G.comp fBall
  let logRadius : C(frontier U, ℝ) :=
    { toFun := fun y ↦ Real.log ‖(y : E) - x‖
      continuous_toFun := by
        apply Continuous.log
        · exact (continuous_subtype_val.sub continuous_const).norm
        · intro y
          exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun hyx ↦
            hx (hyx ▸ hfrontK y.2)) }
  obtain ⟨L, hL⟩ :=
    logRadius.exists_extension isClosed_frontier.isClosedEmbedding_subtypeVal
  let F : C(E, E) :=
    { toFun := fun y ↦ Real.exp (L y) • (direction y : E)
      continuous_toFun := (Real.continuous_exp.comp L.continuous).smul
        (continuous_subtype_val.comp direction.continuous) }
  have hF0 (y : E) : F y ≠ 0 := by
    have hdirection : (direction y : E) ≠ 0 := by
      intro hzero
      have hnorm := mem_sphere_zero_iff_norm.mp (direction y).2
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    exact smul_ne_zero (Real.exp_ne_zero (L y)) hdirection
  apply no_zeroFree_extension_over_bounded_open d U hxBounded x hxU F
    (fun y _hy ↦ hF0 y)
  intro y hy
  obtain ⟨w, hw⟩ := hkRange (hfrontK hy)
  subst y
  let wk : ks := ⟨w, hy⟩
  have hfBall : fBall (r w) = unitSphereClosedBallInclusion d w := by
    apply Subtype.ext
    exact hf w
  have hdirection : direction (r w) = boundaryDirection wk := by
    change G (fBall (r w)) = boundaryDirection wk
    rw [hfBall]
    exact hG wk
  have hLw : L (r w) = logRadius ⟨r w, hy⟩ := by
    exact DFunLike.congr_fun hL ⟨r w, hy⟩
  change Real.exp (L (r w)) • (direction (r w) : E) = r w - x
  rw [hLw, hdirection]
  change Real.exp (Real.log ‖r w - x‖) •
      NormedSpace.normalize (r w - x) = r w - x
  rw [Real.exp_log (norm_pos_iff.mpr (hvector wk))]
  exact NormedSpace.norm_smul_normalize _

/-- The frontier of every bounded complementary component of an embedded
sphere is the whole embedded sphere. -/
theorem frontier_bounded_sphere_complement_component_eq_range
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ (Set.range r)ᶜ)
    (hbounded : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ x)) :
    frontier (connectedComponentIn (Set.range r)ᶜ x) = Set.range r := by
  letI : Nonempty (Fin d) :=
    ⟨⟨0, lt_of_lt_of_le (by norm_num) hd⟩⟩
  let k := frontier (connectedComponentIn (Set.range r)ᶜ x)
  have hkCompact : IsCompact k :=
    isCompact_frontier_connectedComponentIn_of_isBounded hbounded
  have hkRange : k ⊆ Set.range r := by
    simpa only [k, compl_compl] using
      frontier_connectedComponentIn_subset_compl
        (isOpen_compl_range_sphere_embedding d r hcont hinj) x
  by_contra hkProper
  exact
    (not_isPreconnected_compl_frontier_connectedComponentIn
      (isOpen_compl_range_sphere_embedding d r hcont hinj) hx hbounded)
      (isPreconnected_compl_compact_proper_subset_sphere_range
        d hd r hcont hinj k hkCompact hkRange hkProper)

end

end Submission.Helpers
