import Submission.SuspensionBridge

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Submission.Helpers

open Set

noncomputable section

private abbrev GE (d : ℕ) := EuclideanSpace ℝ (Fin d)

private def firstGaussDeformationVector (d : ℕ)
    (r : Metric.sphere (0 : GE d) 1 → GE d)
    (x : ((Set.range r)ᶜ : Set (GE d)))
    (q : unitInterval × Metric.sphere (0 : GE (d + d)) 1) : GE (d + d) :=
  joinBlocks d
    (radialEmbeddingExtension d r (firstBlock d q.2) -
      ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * ‖firstBlock d q.2‖) • (x : GE d))
    (secondBlock d q.2)

private theorem continuous_firstGaussDeformationVector (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : GE d) 1 → GE d) (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (GE d))) :
    Continuous (firstGaussDeformationVector d r x) := by
  have hu : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      firstBlock d (q.2 : GE (d + d))) :=
    (continuous_firstBlock d).comp (continuous_subtype_val.comp continuous_snd)
  have hv : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      secondBlock d (q.2 : GE (d + d))) :=
    (continuous_secondBlock d).comp (continuous_subtype_val.comp continuous_snd)
  have ht : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦ (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hcoeff : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      (1 - (q.1 : ℝ)) + (q.1 : ℝ) * ‖firstBlock d q.2‖) :=
    (continuous_const.sub ht).add (ht.mul hu.norm)
  have hfirst : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      radialEmbeddingExtension d r (firstBlock d q.2) -
        ((1 - (q.1 : ℝ)) + (q.1 : ℝ) * ‖firstBlock d q.2‖) •
          (x : GE d)) :=
    ((continuous_radialEmbeddingExtension d hd r hcont).comp hu).sub
      (hcoeff.smul continuous_const)
  unfold firstGaussDeformationVector joinBlocks
  exact (splitBlocks d).symm.continuous.comp (hfirst.prodMk hv)

private theorem firstGaussDeformationVector_ne_zero (d : ℕ)
    (r : Metric.sphere (0 : GE d) 1 → GE d)
    (x : ((Set.range r)ᶜ : Set (GE d)))
    (q : unitInterval × Metric.sphere (0 : GE (d + d)) 1) :
    firstGaussDeformationVector d r x q ≠ 0 := by
  intro hzero
  let u : GE d := firstBlock d (q.2 : GE (d + d))
  let v : GE d := secondBlock d (q.2 : GE (d + d))
  have hv0 : v = 0 := by
    have h := congrArg (secondBlock d) hzero
    simpa only [firstGaussDeformationVector, secondBlock_joinBlocks,
      secondBlock_zero, v] using h
  have hqnorm : ‖(q.2 : GE (d + d))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp q.2.2
  have hblocks := norm_sq_eq_blocks d (q.2 : GE (d + d))
  have hunorm : ‖u‖ = 1 := by
    rw [hqnorm, one_pow, show secondBlock d (q.2 : GE (d + d)) = v from rfl,
      hv0, norm_zero, zero_pow (by norm_num), add_zero] at hblocks
    nlinarith [norm_nonneg u]
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hunorm]; norm_num)
  have hfirst := congrArg (firstBlock d) hzero
  have hradial : radialEmbeddingExtension d r u = (x : GE d) := by
    simp only [firstGaussDeformationVector, firstBlock_joinBlocks,
      firstBlock_zero] at hfirst
    rw [hunorm] at hfirst
    have hcoeff : (1 - (q.1 : ℝ)) + (q.1 : ℝ) * 1 = 1 := by ring
    rw [hcoeff, one_smul] at hfirst
    exact sub_eq_zero.mp hfirst
  apply x.2
  refine ⟨normalizedSpherePoint d u hu0, ?_⟩
  rw [radialEmbeddingExtension, dif_neg hu0, hunorm, one_smul] at hradial
  exact hradial

private def middleSuspendedGaussMap (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : GE d) 1 → GE d) (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (GE d))) :
    C(Metric.sphere (0 : GE (d + d)) 1,
      Metric.sphere (0 : GE (d + d)) 1) where
  toFun q := ⟨NormedSpace.normalize
      (firstGaussDeformationVector d r x (1, q)), by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize
      (firstGaussDeformationVector_ne_zero d r x (1, q))⟩
  continuous_toFun := by
    have hvec : Continuous (fun q : Metric.sphere (0 : GE (d + d)) 1 ↦
        firstGaussDeformationVector d r x (1, q)) :=
      (continuous_firstGaussDeformationVector d hd r hcont x).comp
        (continuous_const.prodMk continuous_id)
    apply Continuous.subtype_mk
    change Continuous (fun q : Metric.sphere (0 : GE (d + d)) 1 ↦
      ‖firstGaussDeformationVector d r x (1, q)‖⁻¹ •
        firstGaussDeformationVector d r x (1, q))
    exact (hvec.norm.inv₀ fun q ↦ norm_ne_zero_iff.mpr
      (firstGaussDeformationVector_ne_zero d r x (1, q))).smul hvec

private theorem firstGaussVector_zero_eq (d : ℕ)
    (r : Metric.sphere (0 : GE d) 1 → GE d)
    (x : ((Set.range r)ᶜ : Set (GE d)))
    (q : Metric.sphere (0 : GE (d + d)) 1) :
    firstGaussDeformationVector d r x (0, q) =
      suspendedEmbedding d r q - (suspendedComplementPoint d r x : GE (d + d)) := by
  simpa [firstGaussDeformationVector, suspendedEmbedding] using joinBlocks_sub d
    (radialEmbeddingExtension d r (firstBlock d q)) (x : GE d)
    (secondBlock d q) 0

private theorem gaussMap_suspendedEmbedding_homotopic_middle (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : GE d) 1 → GE d) (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (GE d))) :
    ContinuousMap.Homotopic
      (gaussMap (d + d) (suspendedEmbedding d r)
        (continuous_suspendedEmbedding d hd r hcont)
        (suspendedComplementPoint d r x))
      (middleSuspendedGaussMap d hd r hcont x) := by
  let H : C(unitInterval × Metric.sphere (0 : GE (d + d)) 1,
      Metric.sphere (0 : GE (d + d)) 1) :=
    { toFun := fun q ↦ ⟨NormedSpace.normalize
          (firstGaussDeformationVector d r x q), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize
          (firstGaussDeformationVector_ne_zero d r x q)⟩
      continuous_toFun := by
        have hvec := continuous_firstGaussDeformationVector d hd r hcont x
        apply Continuous.subtype_mk
        change Continuous (fun q ↦
          ‖firstGaussDeformationVector d r x q‖⁻¹ •
            firstGaussDeformationVector d r x q)
        exact (hvec.norm.inv₀ fun q ↦ norm_ne_zero_iff.mpr
          (firstGaussDeformationVector_ne_zero d r x q)).smul hvec }
  refine ⟨{
    toFun := H
    continuous_toFun := H.continuous
    map_zero_left := by
      intro q
      apply Subtype.ext
      change NormedSpace.normalize (firstGaussDeformationVector d r x (0, q)) =
        NormedSpace.normalize
          (suspendedEmbedding d r q -
            (suspendedComplementPoint d r x : GE (d + d)))
      rw [firstGaussVector_zero_eq]
    map_one_left := by
      intro q
      rfl
  }⟩

private def secondGaussDeformationVector (d : ℕ)
    (r : Metric.sphere (0 : GE d) 1 → GE d) (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (GE d)))
    (q : unitInterval × Metric.sphere (0 : GE (d + d)) 1) : GE (d + d) :=
  let u := firstBlock d (q.2 : GE (d + d))
  let base := radialEmbeddingExtension d r u - ‖u‖ • (x : GE d)
  let target := radialExtension d (gaussMap d r hcont x) u
  joinBlocks d ((1 - (q.1 : ℝ)) • base + (q.1 : ℝ) • target)
    (secondBlock d q.2)

private theorem continuous_secondGaussDeformationVector (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : GE d) 1 → GE d) (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (GE d))) :
    Continuous (secondGaussDeformationVector d r hcont x) := by
  have hu : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      firstBlock d (q.2 : GE (d + d))) :=
    (continuous_firstBlock d).comp (continuous_subtype_val.comp continuous_snd)
  have hv : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      secondBlock d (q.2 : GE (d + d))) :=
    (continuous_secondBlock d).comp (continuous_subtype_val.comp continuous_snd)
  have ht : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦ (q.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hbase : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      radialEmbeddingExtension d r (firstBlock d q.2) -
        ‖firstBlock d q.2‖ • (x : GE d)) :=
    ((continuous_radialEmbeddingExtension d hd r hcont).comp hu).sub
      (hu.norm.smul continuous_const)
  have htarget : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      radialExtension d (gaussMap d r hcont x) (firstBlock d q.2)) :=
    (continuous_radialExtension d (gaussMap d r hcont x)).comp hu
  have hfirst : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : GE (d + d)) 1 ↦
      (1 - (q.1 : ℝ)) •
          (radialEmbeddingExtension d r (firstBlock d q.2) -
            ‖firstBlock d q.2‖ • (x : GE d)) +
        (q.1 : ℝ) •
          radialExtension d (gaussMap d r hcont x) (firstBlock d q.2)) :=
    ((continuous_const.sub ht).smul hbase).add (ht.smul htarget)
  unfold secondGaussDeformationVector joinBlocks
  exact (splitBlocks d).symm.continuous.comp (hfirst.prodMk hv)

private theorem secondGaussDeformationVector_ne_zero (d : ℕ)
    (r : Metric.sphere (0 : GE d) 1 → GE d) (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (GE d)))
    (q : unitInterval × Metric.sphere (0 : GE (d + d)) 1) :
    secondGaussDeformationVector d r hcont x q ≠ 0 := by
  intro hzero
  let u : GE d := firstBlock d (q.2 : GE (d + d))
  let v : GE d := secondBlock d (q.2 : GE (d + d))
  have hv0 : v = 0 := by
    have h := congrArg (secondBlock d) hzero
    simpa only [secondGaussDeformationVector, secondBlock_joinBlocks,
      secondBlock_zero, v] using h
  have hqnorm : ‖(q.2 : GE (d + d))‖ = 1 :=
    mem_sphere_zero_iff_norm.mp q.2.2
  have hblocks := norm_sq_eq_blocks d (q.2 : GE (d + d))
  have hunorm : ‖u‖ = 1 := by
    rw [hqnorm, one_pow, show secondBlock d (q.2 : GE (d + d)) = v from rfl,
      hv0, norm_zero, zero_pow (by norm_num), add_zero] at hblocks
    nlinarith [norm_nonneg u]
  have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (by rw [hunorm]; norm_num)
  let z : Metric.sphere (0 : GE d) 1 := normalizedSpherePoint d u hu0
  let b : GE d := r z - (x : GE d)
  have hb0 : b ≠ 0 := by
    intro hb
    apply x.2
    refine ⟨z, ?_⟩
    exact sub_eq_zero.mp hb
  have hbase : radialEmbeddingExtension d r u - ‖u‖ • (x : GE d) = b := by
    rw [radialEmbeddingExtension, dif_neg hu0, hunorm, one_smul]
    simp only [one_smul]
    rfl
  have htarget : radialExtension d (gaussMap d r hcont x) u =
      NormedSpace.normalize b := by
    rw [radialExtension, dif_neg hu0, hunorm, one_smul]
    rfl
  have hfirst := congrArg (firstBlock d) hzero
  simp only [secondGaussDeformationVector, firstBlock_joinBlocks,
    firstBlock_zero] at hfirst
  rw [hbase, htarget] at hfirst
  have hnormalize : NormedSpace.normalize b = ‖b‖⁻¹ • b := rfl
  rw [hnormalize, smul_smul, ← add_smul] at hfirst
  have ht0 : 0 ≤ (q.1 : ℝ) := q.1.2.1
  have ht1 : (q.1 : ℝ) ≤ 1 := q.1.2.2
  have hbnorm : 0 < ‖b‖ := norm_pos_iff.mpr hb0
  have hcoeff : 0 < (1 - (q.1 : ℝ)) + (q.1 : ℝ) * ‖b‖⁻¹ := by
    by_cases ht : (q.1 : ℝ) = 0
    · simp [ht]
    · exact add_pos_of_nonneg_of_pos (sub_nonneg.mpr ht1)
        (mul_pos (lt_of_le_of_ne ht0 (Ne.symm ht)) (inv_pos.mpr hbnorm))
  exact hb0 (smul_eq_zero.mp hfirst |>.resolve_left hcoeff.ne')

private theorem middle_homotopic_stableGaussMap (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : GE d) 1 → GE d) (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (GE d))) :
    ContinuousMap.Homotopic (middleSuspendedGaussMap d hd r hcont x)
      (stableSphereMap d (gaussMap d r hcont x)) := by
  let H : C(unitInterval × Metric.sphere (0 : GE (d + d)) 1,
      Metric.sphere (0 : GE (d + d)) 1) :=
    { toFun := fun q ↦ ⟨NormedSpace.normalize
          (secondGaussDeformationVector d r hcont x q), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize
          (secondGaussDeformationVector_ne_zero d r hcont x q)⟩
      continuous_toFun := by
        have hvec := continuous_secondGaussDeformationVector d hd r hcont x
        apply Continuous.subtype_mk
        change Continuous (fun q ↦
          ‖secondGaussDeformationVector d r hcont x q‖⁻¹ •
            secondGaussDeformationVector d r hcont x q)
        exact (hvec.norm.inv₀ fun q ↦ norm_ne_zero_iff.mpr
          (secondGaussDeformationVector_ne_zero d r hcont x q)).smul hvec }
  refine ⟨{
    toFun := H
    continuous_toFun := H.continuous
    map_zero_left := by
      intro q
      apply Subtype.ext
      change NormedSpace.normalize
          (secondGaussDeformationVector d r hcont x (0, q)) =
        NormedSpace.normalize
          (firstGaussDeformationVector d r x (1, q))
      congr 1
      simp [secondGaussDeformationVector, firstGaussDeformationVector]
    map_one_left := by
      intro q
      apply Subtype.ext
      change NormedSpace.normalize
          (secondGaussDeformationVector d r hcont x (1, q)) =
        (stableSphereMap d (gaussMap d r hcont x) q : GE (d + d))
      have hraw : secondGaussDeformationVector d r hcont x (1, q) =
          (stableSphereMap d (gaussMap d r hcont x) q : GE (d + d)) := by
        apply (splitBlocks d).injective
        apply Prod.ext <;>
          simp [secondGaussDeformationVector, stableSphereMap]
      rw [hraw]
      exact NormedSpace.normalize_eq_self_of_norm_eq_one
        (mem_sphere_zero_iff_norm.mp
          (stableSphereMap d (gaussMap d r hcont x) q).2)
  }⟩

/-- At a point in the equatorial copy of the original complement, the Gauss
map of the suspended embedding is homotopic to the stable suspension of the
original Gauss map. -/
theorem gaussMap_suspendedEmbedding_homotopic_stableSphereMap
    (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : GE d) 1 → GE d) (hcont : Continuous r)
    (x : ((Set.range r)ᶜ : Set (GE d))) :
    ContinuousMap.Homotopic
      (gaussMap (d + d) (suspendedEmbedding d r)
        (continuous_suspendedEmbedding d hd r hcont)
        (suspendedComplementPoint d r x))
      (stableSphereMap d (gaussMap d r hcont x)) :=
  (gaussMap_suspendedEmbedding_homotopic_middle d hd r hcont x).trans
    (middle_homotopic_stableGaussMap d hd r hcont x)

end

end Submission.Helpers
