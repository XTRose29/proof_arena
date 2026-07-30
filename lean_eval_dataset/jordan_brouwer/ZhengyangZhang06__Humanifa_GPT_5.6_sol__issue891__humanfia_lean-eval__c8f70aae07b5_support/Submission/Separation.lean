import Submission.AmbientMove
import Submission.ProperSubset
import Submission.Projection
import Submission.RegularApproximation

namespace Submission.Helpers

open Function Set

noncomputable section

/-- Normalization bundles a zero-free Euclidean-valued sphere map as a
sphere-valued map. -/
def normalizedSphereMap (d : ℕ)
    (u : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      EuclideanSpace ℝ (Fin d))) (hu : ∀ z, u z ≠ 0) :
    C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) where
  toFun z := ⟨NormedSpace.normalize (u z), by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize (hu z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous (fun z ↦ ‖u z‖⁻¹ • u z)
    exact (u.continuous.norm.inv₀ fun z ↦
      norm_ne_zero_iff.mpr (hu z)).smul u.continuous

/-- A zero-free map less than one unit from the tautological unit-sphere
inclusion normalizes to a map homotopic to the identity. -/
theorem homotopic_normalizedSphereMap_of_close (d : ℕ)
    (u : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      EuclideanSpace ℝ (Fin d))) (hu : ∀ z, u z ≠ 0)
    (hclose : ∀ z,
      ‖u z - (z : EuclideanSpace ℝ (Fin d))‖ < 1) :
    ContinuousMap.Homotopic (ContinuousMap.id _)
      (normalizedSphereMap d u hu) := by
  let v : unitInterval × Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d) := fun q ↦
    (q.2 : EuclideanSpace ℝ (Fin d)) + (q.1 : ℝ) •
      (u q.2 - (q.2 : EuclideanSpace ℝ (Fin d)))
  have hv_ne (q : unitInterval × Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1) : v q ≠ 0 := by
    intro hzero
    have heq : (q.2 : EuclideanSpace ℝ (Fin d)) =
        -(q.1 : ℝ) •
          (u q.2 - (q.2 : EuclideanSpace ℝ (Fin d))) := by
      calc
        (q.2 : EuclideanSpace ℝ (Fin d)) =
            v q - (q.1 : ℝ) •
              (u q.2 - (q.2 : EuclideanSpace ℝ (Fin d))) := by
          dsimp [v]
          abel
        _ = -(q.1 : ℝ) •
              (u q.2 - (q.2 : EuclideanSpace ℝ (Fin d))) := by
          rw [hzero, zero_sub, neg_smul]
    have ht0 : 0 ≤ (q.1 : ℝ) := q.1.2.1
    have ht1 : (q.1 : ℝ) ≤ 1 := q.1.2.2
    have hnorm : (1 : ℝ) ≤
        ‖u q.2 - (q.2 : EuclideanSpace ℝ (Fin d))‖ := by
      calc
        (1 : ℝ) = ‖(q.2 : EuclideanSpace ℝ (Fin d))‖ :=
          (mem_sphere_zero_iff_norm.mp q.2.2).symm
        _ = ‖-(q.1 : ℝ) •
            (u q.2 - (q.2 : EuclideanSpace ℝ (Fin d)))‖ :=
          congrArg norm heq
        _ = (q.1 : ℝ) *
            ‖u q.2 - (q.2 : EuclideanSpace ℝ (Fin d))‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonpos (neg_nonpos.mpr ht0), neg_neg]
        _ ≤ 1 * ‖u q.2 - (q.2 : EuclideanSpace ℝ (Fin d))‖ :=
          mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ = ‖u q.2 - (q.2 : EuclideanSpace ℝ (Fin d))‖ :=
          one_mul _
    exact (not_le_of_gt (hclose q.2)) hnorm
  have hv : Continuous v := by
    dsimp [v]
    exact (continuous_subtype_val.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        ((u.continuous.comp continuous_snd).sub
          (continuous_subtype_val.comp continuous_snd)))
  exact ⟨{
    toFun := fun q ↦ ⟨NormedSpace.normalize (v q), by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize (hv_ne q)⟩
    continuous_toFun := by
      apply Continuous.subtype_mk
      change Continuous (fun q ↦ ‖v q‖⁻¹ • v q)
      exact (hv.norm.inv₀ fun q ↦
        norm_ne_zero_iff.mpr (hv_ne q)).smul hv
    map_zero_left := by
      intro z
      apply Subtype.ext
      change NormedSpace.normalize
          ((z : EuclideanSpace ℝ (Fin d)) +
            (0 : ℝ) • (u z - (z : EuclideanSpace ℝ (Fin d)))) = z
      simp only [zero_smul, add_zero]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.mp z.2)
    map_one_left := by
      intro z
      apply Subtype.ext
      change NormedSpace.normalize
          ((z : EuclideanSpace ℝ (Fin d)) +
            (1 : ℝ) • (u z - (z : EuclideanSpace ℝ (Fin d)))) =
        NormedSpace.normalize (u z)
      congr 1
      module }⟩

/-- Every embedded sphere in the relevant dimension has a bounded
complementary component.  Otherwise its complement is one unbounded
preconnected region.  Moving all roots of a finite regular approximation
outside a ball containing the embedded sphere would make its normalized
boundary map extend over the standard closed ball, contradicting Brouwer's
no-retraction theorem. -/
theorem exists_bounded_sphere_complement_component
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    ∃ x ∈ (Set.range r)ᶜ,
      Bornology.IsBounded
        (connectedComponentIn (Set.range r)ᶜ x) := by
  classical
  let E := EuclideanSpace ℝ (Fin d)
  let S := Metric.sphere (0 : E) 1
  let K := Set.range r
  by_contra hbounded
  push Not at hbounded
  have hKCompact : IsCompact K := isCompact_range hcont
  have hUOpen : IsOpen Kᶜ := hKCompact.isClosed.isOpen_compl
  have hUPreconnected : IsPreconnected Kᶜ := by
    by_contra hseparates
    obtain ⟨x, hx, hxBounded⟩ :=
      exists_bounded_component_of_compact_separator
        d hd K hKCompact hseparates
    exact hbounded x hx hxBounded
  have hUUnbounded : ¬ Bornology.IsBounded Kᶜ := by
    obtain ⟨p, hp, hpUnbounded⟩ :=
      exists_unbounded_connectedComponentIn d hd r hcont
    intro hU
    apply hpUnbounded
    exact hU.subset (connectedComponentIn_subset Kᶜ p)
  obtain ⟨A⟩ := exists_regularApproximation d hd r hcont hinj
  let P : Set E := {x | A.g x = A.a}
  have hPFinite : P.Finite := A.roots_finite
  have hPU : P ⊆ Kᶜ := by
    intro x hx
    exact A.root_not_mem_range hx
  obtain ⟨R, hKBall⟩ := hKCompact.isBounded.subset_ball (0 : E)
  have hR : 0 < R := by
    obtain ⟨x, hx⟩ := (sphere_range_connected d hd r hcont).nonempty
    have hxBall := hKBall hx
    rw [Metric.mem_ball, dist_zero_right] at hxBall
    exact (norm_nonneg x).trans_lt hxBall
  let C : Set E := Metric.closedBall (0 : E) R
  have hKC : K ⊆ C := by
    exact hKBall.trans Metric.ball_subset_closedBall
  have hCBounded : Bornology.IsBounded C :=
    (isCompact_closedBall (0 : E) R).isBounded
  obtain ⟨e, heP, heFix⟩ :=
    exists_homeomorph_image_finite_disjoint_bounded
      (euclidean_rank_gt_one d hd) hUOpen hUPreconnected hUUnbounded
      hPFinite hPU hCBounded
  let q : C(E, E) :=
    { toFun := fun x ↦ A.g (e.symm x) - A.a
      continuous_toFun :=
        A.smooth'.continuous.comp e.symm.continuous |>.sub
          continuous_const }
  have hq0 (x : C) : q x ≠ 0 := by
    intro hxZero
    have hxRoot : e.symm (x : E) ∈ P := by
      change A.g (e.symm (x : E)) = A.a
      exact sub_eq_zero.mp hxZero
    have hxImage : (x : E) ∈ e '' P :=
      ⟨e.symm (x : E), hxRoot, e.apply_symm_apply (x : E)⟩
    exact Set.disjoint_left.mp heP hxImage x.2
  let H : C(C, S) :=
    { toFun := fun x ↦ ⟨NormedSpace.normalize (q x), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize (hq0 x)⟩
      continuous_toFun := by
        have hq : Continuous (fun x : C ↦ q x) :=
          q.continuous.comp continuous_subtype_val
        apply Continuous.subtype_mk
        change Continuous (fun x : C ↦ ‖q x‖⁻¹ • q x)
        exact (hq.norm.inv₀ fun x ↦
          norm_ne_zero_iff.mpr (hq0 x)).smul hq }
  let u : C(S, E) :=
    { toFun := fun z ↦ A.g (r z) - A.a
      continuous_toFun :=
        A.smooth'.continuous.comp hcont |>.sub continuous_const }
  have hu0 (z : S) : u z ≠ 0 := by
    intro hz
    have hclose := A.close_on_sphere z
    rw [show A.g (r z) - A.a = 0 by exact hz,
      zero_sub, norm_neg, mem_sphere_zero_iff_norm.mp z.2] at hclose
    exact (lt_irrefl 1) hclose
  let uSphere : C(S, S) := normalizedSphereMap d u hu0
  have hidu : ContinuousMap.Homotopic (ContinuousMap.id S) uSphere :=
    homotopic_normalizedSphereMap_of_close d u hu0 A.close_on_sphere
  have hHBoundary (z : S) : H ⟨r z, hKC ⟨z, rfl⟩⟩ = uSphere z := by
    apply Subtype.ext
    change NormedSpace.normalize
        (A.g (e.symm (r z)) - A.a) =
      NormedSpace.normalize (A.g (r z) - A.a)
    have heR : e (r z) = r z := by
      apply heFix
      exact fun hzCompl ↦ hzCompl ⟨z, rfl⟩
    have heSymmR : e.symm (r z) = r z := by
      calc
        e.symm (r z) = e.symm (e (r z)) := by rw [heR]
        _ = r z := e.symm_apply_apply (r z)
    rw [heSymmR]
  have hinc : Topology.IsClosedEmbedding
      (unitSphereClosedBallInclusion d) :=
    (unitSphereClosedBallInclusion d).continuous.isClosedEmbedding (by
      intro z w hzw
      apply Subtype.ext
      exact congrArg
        (fun q : Metric.closedBall (0 : E) 1 ↦ (q : E)) hzw)
  let rMap : C(S, E) := ⟨r, hcont⟩
  obtain ⟨Rext, hRext⟩ := rMap.exists_extension hinc
  have hCNonempty : C.Nonempty := by
    refine ⟨0, ?_⟩
    simp [C, hR.le]
  have hCComplete : IsComplete C := Metric.isClosed_closedBall.isComplete
  have hCConvex : Convex ℝ C := convex_closedBall (0 : E) R
  let RtoC : C(Metric.closedBall (0 : E) 1, C) :=
    { toFun := fun x ↦ ⟨metricProjection C hCNonempty hCComplete hCConvex
          (Rext x),
        metricProjection_mem C hCNonempty hCComplete hCConvex (Rext x)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (metricProjection_continuous C hCNonempty hCComplete
          hCConvex).comp Rext.continuous }
  let G : C(Metric.closedBall (0 : E) 1, S) := H.comp RtoC
  have hG (z : S) : G (unitSphereClosedBallInclusion d z) = uSphere z := by
    have hRz : Rext (unitSphereClosedBallInclusion d z) = r z :=
      DFunLike.congr_fun hRext z
    have hproject : metricProjection C hCNonempty hCComplete hCConvex
        (Rext (unitSphereClosedBallInclusion d z)) = r z := by
      rw [hRz]
      exact metricProjection_eq_self_of_mem C hCNonempty hCComplete
        hCConvex (hKC ⟨z, rfl⟩)
    change H ⟨metricProjection C hCNonempty hCComplete hCConvex
      (Rext (unitSphereClosedBallInclusion d z)), _⟩ = uSphere z
    simpa only [hproject] using hHBoundary z
  have huNull : SphereMapNullhomotopic d uSphere :=
    sphereMapNullhomotopic_of_closedBall_extension d uSphere G hG
  obtain ⟨c, huc⟩ := huNull
  have hidNull : SphereMapNullhomotopic d (ContinuousMap.id S) :=
    ⟨c, hidu.trans huc⟩
  obtain ⟨Gid, hGid⟩ :=
    exists_closedBall_extension_of_sphereMapNullhomotopic d
      (ContinuousMap.id S) hidNull
  exact noUnitSphereRetraction_all d ⟨Gid, hGid⟩

end

end Submission.Helpers
