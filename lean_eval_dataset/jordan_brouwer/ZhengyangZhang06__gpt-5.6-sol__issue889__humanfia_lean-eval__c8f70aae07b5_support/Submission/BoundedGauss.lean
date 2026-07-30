import Submission.Components
import Submission.Cone
import Submission.Gauss

namespace Submission.Helpers

open Set

/-- A zero-free map on the closure of a bounded open set cannot agree on
the frontier with translation away from an interior point.  Patching it to
that translation outside the set would give a retraction of a closed ball
onto its boundary. -/
theorem no_zeroFree_extension_over_bounded_open (d : ℕ)
    (U : Set (EuclideanSpace ℝ (Fin d))) (hUb : Bornology.IsBounded U)
    (x : EuclideanSpace ℝ (Fin d)) (hx : x ∈ U)
    (F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d)))
    (hF0 : ∀ z ∈ closure U, F z ≠ 0)
    (hfront : ∀ z ∈ frontier U, F z = z - x) : False := by
  classical
  let Kfun : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d) :=
    U.piecewise F (fun z ↦ z - x)
  have hKcont : Continuous Kfun := by
    exact continuous_piecewise hfront F.continuous.continuousOn
      (continuous_id.sub continuous_const).continuousOn
  let K : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d)) :=
    ⟨Kfun, hKcont⟩
  have hK0 (z : EuclideanSpace ℝ (Fin d)) : K z ≠ 0 := by
    by_cases hz : z ∈ U
    · simpa [K, Kfun, Set.piecewise, hz] using
        hF0 z (subset_closure hz)
    · change Kfun z ≠ 0
      rw [show Kfun z = z - x by simp [Kfun, hz]]
      exact sub_ne_zero.mpr fun hzx ↦ hz (hzx ▸ hx)
  obtain ⟨R, hRsub⟩ := hUb.closure.subset_ball x
  have hR : 0 < R := by
    have h := hRsub (subset_closure hx)
    simpa only [Metric.mem_ball, dist_self] using h
  let affineBall : Metric.closedBall
      (0 : EuclideanSpace ℝ (Fin d)) 1 → EuclideanSpace ℝ (Fin d) :=
    fun q ↦ x + R • (q : EuclideanSpace ℝ (Fin d))
  have haffine : Continuous affineBall := by
    exact continuous_const.add
      (continuous_const.smul (continuous_subtype_val))
  let ρ : C(Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    { toFun := fun q ↦
        ⟨NormedSpace.normalize (K (affineBall q)), by
          rw [mem_sphere_zero_iff_norm]
          exact NormedSpace.norm_normalize (hK0 (affineBall q))⟩
      continuous_toFun := by
        have hv : Continuous (fun q ↦ K (affineBall q)) :=
          K.continuous.comp haffine
        apply Continuous.subtype_mk
        change Continuous (fun q ↦
          ‖K (affineBall q)‖⁻¹ • K (affineBall q))
        exact (hv.norm.inv₀ fun q ↦
          norm_ne_zero_iff.mpr (hK0 (affineBall q))).smul hv }
  apply noUnitSphereRetraction_all d
  refine ⟨ρ, ?_⟩
  intro z
  apply Subtype.ext
  change NormedSpace.normalize
      (K (x + R • (z : EuclideanSpace ℝ (Fin d)))) = z
  have hzOutside : x + R • (z : EuclideanSpace ℝ (Fin d)) ∉ U := by
    intro hzU
    have hzBall := hRsub (subset_closure hzU)
    rw [Metric.mem_ball, dist_eq_norm] at hzBall
    have hznorm : ‖(z : EuclideanSpace ℝ (Fin d))‖ = 1 :=
      mem_sphere_zero_iff_norm.mp z.2
    have : ‖x + R • (z : EuclideanSpace ℝ (Fin d)) - x‖ = R := by
      rw [show x + R • (z : EuclideanSpace ℝ (Fin d)) - x =
          R • (z : EuclideanSpace ℝ (Fin d)) by abel,
        norm_smul, Real.norm_eq_abs, abs_of_pos hR, hznorm, mul_one]
    rw [this] at hzBall
    exact (lt_irrefl R) hzBall
  rw [show K (x + R • (z : EuclideanSpace ℝ (Fin d))) =
      R • (z : EuclideanSpace ℝ (Fin d)) by
    simp [K, Kfun, hzOutside]]
  rw [NormedSpace.normalize_smul_of_pos hR]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (mem_sphere_zero_iff_norm.mp z.2)

/-- The Gauss map based in a bounded complementary component is essential.
Together with the converse in `GaussReduction`, boundedness is therefore
exactly the obstruction detected by this Gauss map. -/
theorem gaussMap_not_nullhomotopic_of_isBounded (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r)
    (x : ((Set.range r)ᶜ : Set (EuclideanSpace ℝ (Fin d))))
    (hxb : Bornology.IsBounded
      (connectedComponentIn (Set.range r)ᶜ
        (x : EuclideanSpace ℝ (Fin d)))) :
    ¬ SphereMapNullhomotopic d (gaussMap d r hcont x) := by
  intro hnull
  obtain ⟨G, hG⟩ :=
    exists_closedBall_extension_of_sphereMapNullhomotopic d
      (gaussMap d r hcont x) hnull
  obtain ⟨f, hf, hfle, _hflt⟩ :=
    exists_strict_unitBall_extension d hd r hcont hinj
  let fBall : C(EuclideanSpace ℝ (Fin d),
      Metric.closedBall (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    { toFun := fun y ↦ ⟨f y, by
        rw [Metric.mem_closedBall, dist_zero_right]
        exact hfle y⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact f.continuous }
  let direction : C(EuclideanSpace ℝ (Fin d),
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    G.comp fBall
  let logRadius : C(Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1, ℝ) :=
    { toFun := fun z ↦
        Real.log ‖r z - (x : EuclideanSpace ℝ (Fin d))‖
      continuous_toFun := by
        apply Continuous.log
        · exact (hcont.sub continuous_const).norm
        · intro z
          exact norm_ne_zero_iff.mpr (sub_ne_zero.mpr fun h ↦
            x.2 ⟨z, h⟩) }
  obtain ⟨L, hL⟩ :=
    logRadius.exists_extension (sphere_isClosedEmbedding d r hcont hinj)
  let F : C(EuclideanSpace ℝ (Fin d), EuclideanSpace ℝ (Fin d)) :=
    { toFun := fun y ↦ Real.exp (L y) •
        (direction y : EuclideanSpace ℝ (Fin d))
      continuous_toFun := (Real.continuous_exp.comp L.continuous).smul
        (continuous_subtype_val.comp direction.continuous) }
  have hF0 : ∀ y, F y ≠ 0 := by
    intro y
    have hdirection :
        (direction y : EuclideanSpace ℝ (Fin d)) ≠ 0 := by
      intro hzero
      have hnorm := mem_sphere_zero_iff_norm.mp (direction y).2
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
    exact smul_ne_zero (Real.exp_ne_zero (L y)) hdirection
  let U := connectedComponentIn (Set.range r)ᶜ
    (x : EuclideanSpace ℝ (Fin d))
  have hfrontRange : frontier U ⊆ Set.range r := by
    simpa only [U, compl_compl] using
      frontier_connectedComponentIn_subset_compl
        (isOpen_compl_range_sphere_embedding d r hcont hinj)
        (x : EuclideanSpace ℝ (Fin d))
  apply no_zeroFree_extension_over_bounded_open d U hxb
    (x : EuclideanSpace ℝ (Fin d))
    (mem_connectedComponentIn x.2) F
    (fun y hy ↦ hF0 y)
  intro y hy
  obtain ⟨z, rfl⟩ := hfrontRange hy
  have hfBall : fBall (r z) = unitSphereClosedBallInclusion d z := by
    apply Subtype.ext
    exact hf z
  have hdirection : direction (r z) = gaussMap d r hcont x z := by
    change G (fBall (r z)) = gaussMap d r hcont x z
    rw [hfBall]
    exact hG z
  have hLz : L (r z) = logRadius z := by
    exact DFunLike.congr_fun hL z
  change Real.exp (L (r z)) •
      (direction (r z) : EuclideanSpace ℝ (Fin d)) =
    r z - (x : EuclideanSpace ℝ (Fin d))
  rw [hLz, hdirection]
  change Real.exp (Real.log ‖r z -
      (x : EuclideanSpace ℝ (Fin d))‖) •
      NormedSpace.normalize (r z -
        (x : EuclideanSpace ℝ (Fin d))) =
    r z - (x : EuclideanSpace ℝ (Fin d))
  rw [Real.exp_log (norm_pos_iff.mpr <|
    sub_ne_zero.mpr fun h ↦ x.2 ⟨z, h⟩)]
  exact NormedSpace.norm_smul_normalize _

end Submission.Helpers
