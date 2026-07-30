import Submission.Obstruction

namespace Submission.Helpers

open Set
open Filter
open scoped Topology

/-- A nullhomotopy of a sphere map descends along radial coordinates to an
extension over the closed unit ball. -/
theorem exists_closedBall_extension_of_sphereMapNullhomotopic (d : ℕ)
    (g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1))
    (hnull : SphereMapNullhomotopic d g) :
    ∃ G : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
        Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
      ∀ z, G (unitSphereClosedBallInclusion d z) = g z := by
  obtain ⟨c, ⟨H⟩⟩ := hnull
  let radialTime : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin d)) 1 → unitInterval :=
    fun x ↦ ⟨1 - ‖(x : EuclideanSpace ℝ (Fin d))‖, by
      have hx : ‖(x : EuclideanSpace ℝ (Fin d))‖ ≤ 1 := by
        have hx' := x.2
        rw [Metric.mem_closedBall, dist_zero_right] at hx'
        exact hx'
      constructor
      · exact sub_nonneg.mpr hx
      · exact sub_le_self 1
          (norm_nonneg (x : EuclideanSpace ℝ (Fin d)))⟩
  have radialTime_continuous : Continuous radialTime := by
    apply Continuous.subtype_mk
    exact continuous_const.sub
      (continuous_norm.comp continuous_subtype_val)
  let radialDirection : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin d)) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    fun x ↦ if hx : (x : EuclideanSpace ℝ (Fin d)) = 0 then c else
      ⟨NormedSpace.normalize (x : EuclideanSpace ℝ (Fin d)), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize hx⟩
  have radialDirection_continuousAt
      (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
      (hx : (x : EuclideanSpace ℝ (Fin d)) ≠ 0) :
      ContinuousAt radialDirection x := by
    change Filter.Tendsto radialDirection (𝓝 x) (𝓝 (radialDirection x))
    rw [tendsto_subtype_rng]
    have hval : ContinuousAt
        (fun y : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
            (y : EuclideanSpace ℝ (Fin d))) x :=
      continuousAt_subtype_val
    have hnormalize : ContinuousAt
        (fun y : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
            NormedSpace.normalize
              (y : EuclideanSpace ℝ (Fin d))) x := by
      change ContinuousAt (fun y : Metric.closedBall
          (0 : EuclideanSpace ℝ (Fin d)) 1 ↦
        ‖(y : EuclideanSpace ℝ (Fin d))‖⁻¹ •
          (y : EuclideanSpace ℝ (Fin d))) x
      exact (hval.norm.inv₀ (norm_ne_zero_iff.mpr hx)).smul hval
    apply hnormalize.congr
    filter_upwards [hval.eventually_ne hx] with y hy
    dsimp [radialDirection]
    rw [dif_neg hy]
  let cone : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin d)) 1 →
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    fun x ↦ if hx : (x : EuclideanSpace ℝ (Fin d)) = 0 then c
      else H (radialTime x, radialDirection x)
  have cone_continuousAt_center
      (x : Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1)
      (hx : (x : EuclideanSpace ℝ (Fin d)) = 0) :
      ContinuousAt cone x := by
    rw [Metric.continuousAt_iff]
    intro ε hε
    have hHuniform : UniformContinuous H :=
      CompactSpace.uniformContinuous_of_continuous H.continuous
    obtain ⟨δ, hδ, hHδ⟩ :=
      (Metric.uniformContinuous_iff.mp hHuniform) ε hε
    refine ⟨δ, hδ, ?_⟩
    intro y hy
    by_cases hy0 : (y : EuclideanSpace ℝ (Fin d)) = 0
    · have hyx : y = x := by
        apply Subtype.ext
        exact hy0.trans hx.symm
      simpa [hyx]
    · have hnorm : ‖(y : EuclideanSpace ℝ (Fin d))‖ < δ := by
        simpa [Subtype.dist_eq, hx, dist_zero_right] using hy
      have hpair : dist
          (radialTime y, radialDirection y)
          ((1 : unitInterval), radialDirection y) < δ := by
        rw [dist_prod_same_right]
        change |(1 - ‖(y : EuclideanSpace ℝ (Fin d))‖) - 1| < δ
        simpa [abs_neg, abs_of_nonneg
          (norm_nonneg (y : EuclideanSpace ℝ (Fin d)))] using hnorm
      have himage := hHδ hpair
      have hconeX : cone x = c := by
        dsimp [cone]
        rw [if_pos hx]
      have hconeY : cone y = H (radialTime y, radialDirection y) := by
        dsimp [cone]
        rw [if_neg hy0]
      rw [hconeX, hconeY]
      simpa using himage
  have cone_continuous : Continuous cone := by
    rw [continuous_iff_continuousAt]
    intro x
    by_cases hx : (x : EuclideanSpace ℝ (Fin d)) = 0
    · exact cone_continuousAt_center x hx
    · have hbranch : ContinuousAt
          (fun y ↦ H (radialTime y, radialDirection y)) x :=
        H.continuous.continuousAt.comp
          (radialTime_continuous.continuousAt.prodMk
            (radialDirection_continuousAt x hx))
      apply hbranch.congr
      filter_upwards [continuousAt_subtype_val.eventually_ne hx] with y hy
      dsimp [cone]
      rw [if_neg hy]
  let G : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    ⟨cone, cone_continuous⟩
  refine ⟨G, ?_⟩
  intro z
  have hz : ((unitSphereClosedBallInclusion d z :
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :
      EuclideanSpace ℝ (Fin d)) ≠ 0 := by
    change (z : EuclideanSpace ℝ (Fin d)) ≠ 0
    intro hz0
    have hznorm := mem_sphere_zero_iff_norm.mp z.2
    rw [hz0, norm_zero] at hznorm
    norm_num at hznorm
  have htime : radialTime (unitSphereClosedBallInclusion d z) = 0 := by
    apply Subtype.ext
    simp [radialTime, unitSphereClosedBallInclusion,
      mem_sphere_zero_iff_norm.mp z.2]
  have hdirection :
      radialDirection (unitSphereClosedBallInclusion d z) = z := by
    dsimp [radialDirection]
    rw [dif_neg hz]
    apply Subtype.ext
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp z.2)
  change cone (unitSphereClosedBallInclusion d z) = g z
  dsimp [cone]
  rw [if_neg hz]
  rw [htime, hdirection]
  exact H.map_zero_left z

/-- Nullhomotopy of a sphere map is equivalent to extendability over the
closed unit ball. -/
theorem sphereMapNullhomotopic_iff_exists_closedBall_extension (d : ℕ)
    (g : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1)) :
    SphereMapNullhomotopic d g ↔
      ∃ G : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
          Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1),
        ∀ z, G (unitSphereClosedBallInclusion d z) = g z := by
  constructor
  · exact exists_closedBall_extension_of_sphereMapNullhomotopic d g
  · rintro ⟨G, hG⟩
    exact sphereMapNullhomotopic_of_closedBall_extension d g G hG

end Submission.Helpers
