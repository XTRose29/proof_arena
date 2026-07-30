import Submission.Obstruction

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

namespace Submission.Helpers

open Set

noncomputable section

private abbrev E (d : ℕ) := EuclideanSpace ℝ (Fin d)

abbrev splitBlocks (d : ℕ) :
    E (d + d) ≃L[ℝ] E d × E d :=
  EuclideanSpace.finAddEquivProd

def firstBlock (d : ℕ) (x : E (d + d)) : E d :=
  (splitBlocks d x).1

def secondBlock (d : ℕ) (x : E (d + d)) : E d :=
  (splitBlocks d x).2

def joinBlocks (d : ℕ) (x y : E d) : E (d + d) :=
  (splitBlocks d).symm (x, y)

theorem norm_sq_eq_blocks (d : ℕ) (x : E (d + d)) :
    ‖x‖ ^ 2 = ‖firstBlock d x‖ ^ 2 + ‖secondBlock d x‖ ^ 2 := by
  rw [EuclideanSpace.norm_sq_eq, EuclideanSpace.norm_sq_eq,
    EuclideanSpace.norm_sq_eq]
  simp only [firstBlock, secondBlock, splitBlocks,
    EuclideanSpace.finAddEquivProd, ContinuousLinearEquiv.trans_apply,
    LinearIsometryEquiv.coe_toContinuousLinearEquiv,
    WithLp.prodContinuousLinearEquiv_apply]
  rw [Fin.sum_univ_add]
  rfl

theorem firstBlock_joinBlocks (d : ℕ) (x y : E d) :
    firstBlock d (joinBlocks d x y) = x := by
  change ((splitBlocks d) ((splitBlocks d).symm (x, y))).1 = x
  rw [(splitBlocks d).apply_symm_apply]

theorem secondBlock_joinBlocks (d : ℕ) (x y : E d) :
    secondBlock d (joinBlocks d x y) = y := by
  change ((splitBlocks d) ((splitBlocks d).symm (x, y))).2 = y
  rw [(splitBlocks d).apply_symm_apply]

theorem joinBlocks_blocks (d : ℕ) (x : E (d + d)) :
    joinBlocks d (firstBlock d x) (secondBlock d x) = x := by
  exact (splitBlocks d).symm_apply_apply x

@[simp] theorem firstBlock_zero (d : ℕ) :
    firstBlock d (0 : E (d + d)) = 0 := by
  change ((splitBlocks d) 0).1 = 0
  rw [map_zero]
  rfl

@[simp] theorem secondBlock_zero (d : ℕ) :
    secondBlock d (0 : E (d + d)) = 0 := by
  change ((splitBlocks d) 0).2 = 0
  rw [map_zero]
  rfl

theorem joinBlocks_sub (d : ℕ) (a b c e : E d) :
    joinBlocks d (a - b) (c - e) =
      joinBlocks d a c - joinBlocks d b e := by
  change (splitBlocks d).symm (a - b, c - e) =
    (splitBlocks d).symm (a, c) - (splitBlocks d).symm (b, e)
  rw [← map_sub]
  rfl

theorem norm_sq_joinBlocks (d : ℕ) (x y : E d) :
    ‖joinBlocks d x y‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 := by
  rw [norm_sq_eq_blocks, firstBlock_joinBlocks, secondBlock_joinBlocks]

theorem continuous_firstBlock (d : ℕ) :
    Continuous (firstBlock d) :=
  continuous_fst.comp (splitBlocks d).continuous

theorem continuous_secondBlock (d : ℕ) :
    Continuous (secondBlock d) :=
  continuous_snd.comp (splitBlocks d).continuous

theorem continuous_joinBlocks (d : ℕ) :
    Continuous (Function.uncurry (joinBlocks d)) :=
  (splitBlocks d).symm.continuous.comp
    (continuous_fst.prodMk continuous_snd)

/-- The homogeneous radial extension of a sphere self-map.  It preserves
the norm and is continuous at the origin because its value has norm exactly
the radius. -/
def radialExtension (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1))
    (x : E d) : E d :=
  if hx : x = 0 then 0 else
    ‖x‖ • (f ⟨NormedSpace.normalize x, by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize hx⟩ : E d)

theorem radialExtension_zero (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    radialExtension d f 0 = 0 := by
  simp [radialExtension]

theorem norm_radialExtension (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1))
    (x : E d) : ‖radialExtension d f x‖ = ‖x‖ := by
  by_cases hx : x = 0
  · simp [hx, radialExtension]
  · rw [radialExtension, dif_neg hx, norm_smul, Real.norm_eq_abs,
      abs_norm, mem_sphere_zero_iff_norm.mp (f ⟨NormedSpace.normalize x, by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize hx⟩).2, mul_one]

private theorem continuousAt_radialExtension_zero (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    ContinuousAt (radialExtension d f) 0 := by
  rw [Metric.continuousAt_iff]
  intro ε hε
  refine ⟨ε, hε, ?_⟩
  intro y hy
  rw [radialExtension_zero, dist_zero_right, norm_radialExtension]
  simpa only [dist_zero_right] using hy

theorem continuous_radialExtension (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    Continuous (radialExtension d f) := by
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · simpa only [hx] using continuousAt_radialExtension_zero d f
  · let P : Set (E d) := ({0} : Set (E d))ᶜ
    let normalizeMap : C(P, Metric.sphere (0 : E d) 1) :=
      { toFun := fun y ↦ ⟨NormedSpace.normalize (y : E d), by
          rw [mem_sphere_zero_iff_norm]
          exact NormedSpace.norm_normalize (by
            simpa only [P, mem_compl_iff, mem_singleton_iff] using y.2)⟩
        continuous_toFun := by
          apply Continuous.subtype_mk
          change Continuous (fun y : P ↦ ‖(y : E d)‖⁻¹ • (y : E d))
          exact ((continuous_subtype_val.norm).inv₀ (fun y ↦
            norm_ne_zero_iff.mpr (by
              simpa only [P, mem_compl_iff, mem_singleton_iff] using y.2))).smul
              continuous_subtype_val }
    let radialOnP : C(P, E d) :=
      { toFun := fun y ↦ ‖(y : E d)‖ • (f (normalizeMap y) : E d)
        continuous_toFun := continuous_subtype_val.norm.smul
          (continuous_subtype_val.comp (f.continuous.comp normalizeMap.continuous)) }
    have hOn : ContinuousOn (radialExtension d f) P := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : P.restrict (radialExtension d f) = radialOnP := by
        funext y
        change radialExtension d f (y : E d) =
          ‖(y : E d)‖ • (f (normalizeMap y) : E d)
        rw [radialExtension, dif_neg (by
          simpa only [P, mem_compl_iff, mem_singleton_iff] using y.2)]
        congr 2
      rw [heq]
      exact radialOnP.continuous
    exact hOn.continuousAt
      (isOpen_compl_singleton.mem_nhds (by
        simpa only [P, mem_compl_iff, mem_singleton_iff] using hx))

theorem radialExtension_smul_nonneg (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1))
    {c : ℝ} (hc : 0 ≤ c) (x : E d) :
    radialExtension d f (c • x) = c • radialExtension d f x := by
  by_cases hc0 : c = 0
  · simp [hc0, radialExtension_zero]
  by_cases hx : x = 0
  · simp [hx, radialExtension_zero]
  have hcx : c • x ≠ 0 := smul_ne_zero hc0 hx
  let zcx : Metric.sphere (0 : E d) 1 :=
    ⟨NormedSpace.normalize (c • x), by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize hcx⟩
  let zx : Metric.sphere (0 : E d) 1 :=
    ⟨NormedSpace.normalize x, by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize hx⟩
  have hzcx : zcx = zx := by
    apply Subtype.ext
    exact NormedSpace.normalize_smul_of_pos
      (lt_of_le_of_ne hc (Ne.symm hc0)) x
  rw [radialExtension, dif_neg hcx, radialExtension, dif_neg hx]
  change ‖c • x‖ • (f zcx : E d) = c • (‖x‖ • (f zx : E d))
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg hc, hzcx]
  module

private theorem radialExtension_comp (d : ℕ)
    (f g : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1))
    (x : E d) :
    radialExtension d (f.comp g) x =
      radialExtension d f (radialExtension d g x) := by
  by_cases hx : x = 0
  · simp [hx, radialExtension_zero]
  have hnormx : 0 < ‖x‖ := norm_pos_iff.mpr hx
  let z : Metric.sphere (0 : E d) 1 :=
    ⟨NormedSpace.normalize x, by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize hx⟩
  have hgz : (g z : E d) ≠ 0 := by
    intro hzero
    have hnorm := mem_sphere_zero_iff_norm.mp (g z).2
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  have hradialg : radialExtension d g x = ‖x‖ • (g z : E d) := by
    rw [radialExtension, dif_neg hx]
  rw [hradialg, radialExtension_smul_nonneg d f hnormx.le]
  have hcomp : radialExtension d (f.comp g) x =
      ‖x‖ • (f (g z) : E d) := by
    rw [radialExtension, dif_neg hx]
    rfl
  rw [hcomp]
  congr 1
  rw [radialExtension, dif_neg hgz]
  have hnormalize : NormedSpace.normalize (g z : E d) = (g z : E d) :=
    NormedSpace.normalize_eq_self_of_norm_eq_one
      (mem_sphere_zero_iff_norm.mp (g z).2)
  have hnormalizeSubtype :
      (⟨NormedSpace.normalize (g z : E d), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize hgz⟩ : Metric.sphere (0 : E d) 1) =
      g z := Subtype.ext hnormalize
  rw [mem_sphere_zero_iff_norm.mp (g z).2, one_smul,
    hnormalizeSubtype]

/-- Suspension by a second block of the same dimension, written in the unit
sphere of the block sum. -/
def stableSphereMap (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    C(Metric.sphere (0 : E (d + d)) 1,
      Metric.sphere (0 : E (d + d)) 1) where
  toFun q := ⟨joinBlocks d
      (radialExtension d f (firstBlock d q)) (secondBlock d q), by
    rw [mem_sphere_zero_iff_norm]
    have hq := mem_sphere_zero_iff_norm.mp q.2
    apply (sq_eq_sq₀ (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)).mp
    rw [norm_sq_joinBlocks, norm_radialExtension,
      ← norm_sq_eq_blocks, hq]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hfirst : Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
        radialExtension d f (firstBlock d (q : E (d + d)))) :=
      (continuous_radialExtension d f).comp
        ((continuous_firstBlock d).comp continuous_subtype_val)
    have hsecond : Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
        secondBlock d (q : E (d + d))) :=
      (continuous_secondBlock d).comp continuous_subtype_val
    change Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
      joinBlocks d (radialExtension d f (firstBlock d q)) (secondBlock d q))
    change Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
      (splitBlocks d).symm
        (radialExtension d f (firstBlock d q), secondBlock d q))
    exact (splitBlocks d).symm.continuous.comp (hfirst.prodMk hsecond)

private def stableSphereMapSecond (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    C(Metric.sphere (0 : E (d + d)) 1,
      Metric.sphere (0 : E (d + d)) 1) where
  toFun q := ⟨joinBlocks d (firstBlock d q)
      (radialExtension d f (secondBlock d q)), by
    rw [mem_sphere_zero_iff_norm]
    have hq := mem_sphere_zero_iff_norm.mp q.2
    apply (sq_eq_sq₀ (norm_nonneg _) (show (0 : ℝ) ≤ 1 by norm_num)).mp
    rw [norm_sq_joinBlocks, norm_radialExtension,
      ← norm_sq_eq_blocks, hq]⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hfirst : Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
        firstBlock d (q : E (d + d))) :=
      (continuous_firstBlock d).comp continuous_subtype_val
    have hsecond : Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
        radialExtension d f (secondBlock d (q : E (d + d)))) :=
      (continuous_radialExtension d f).comp
        ((continuous_secondBlock d).comp continuous_subtype_val)
    change Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
      joinBlocks d (firstBlock d q) (radialExtension d f (secondBlock d q)))
    change Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
      (splitBlocks d).symm
        (firstBlock d q, radialExtension d f (secondBlock d q)))
    exact (splitBlocks d).symm.continuous.comp (hfirst.prodMk hsecond)

theorem stableSphereMap_comp (d : ℕ)
    (f g : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    stableSphereMap d (f.comp g) =
      (stableSphereMap d f).comp (stableSphereMap d g) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change joinBlocks d
      (radialExtension d (f.comp g) (firstBlock d q)) (secondBlock d q) =
    joinBlocks d
      (radialExtension d f
        (firstBlock d (joinBlocks d
          (radialExtension d g (firstBlock d q)) (secondBlock d q))))
      (secondBlock d (joinBlocks d
        (radialExtension d g (firstBlock d q)) (secondBlock d q)))
  rw [firstBlock_joinBlocks, secondBlock_joinBlocks,
    radialExtension_comp]

private theorem stableMaps_different_blocks_commute (d : ℕ)
    (f g : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    (stableSphereMapSecond d f).comp (stableSphereMap d g) =
      (stableSphereMap d g).comp (stableSphereMapSecond d f) := by
  apply ContinuousMap.ext
  intro q
  apply Subtype.ext
  change joinBlocks d
      (firstBlock d (joinBlocks d
        (radialExtension d g (firstBlock d q)) (secondBlock d q)))
      (radialExtension d f
        (secondBlock d (joinBlocks d
          (radialExtension d g (firstBlock d q)) (secondBlock d q)))) =
    joinBlocks d
      (radialExtension d g
        (firstBlock d (joinBlocks d (firstBlock d q)
          (radialExtension d f (secondBlock d q)))))
      (secondBlock d (joinBlocks d (firstBlock d q)
        (radialExtension d f (secondBlock d q))))
  rw [firstBlock_joinBlocks, secondBlock_joinBlocks,
    firstBlock_joinBlocks, secondBlock_joinBlocks]

private def blockRotation (d : ℕ) (t : ℝ) (q : E (d + d)) : E (d + d) :=
  joinBlocks d
    (Real.cos t • firstBlock d q - Real.sin t • secondBlock d q)
    (Real.sin t • firstBlock d q + Real.cos t • secondBlock d q)

private theorem norm_blockRotation (d : ℕ) (t : ℝ) (q : E (d + d)) :
    ‖blockRotation d t q‖ = ‖q‖ := by
  have hsq := norm_sq_joinBlocks d
    (Real.cos t • firstBlock d q - Real.sin t • secondBlock d q)
    (Real.sin t • firstBlock d q + Real.cos t • secondBlock d q)
  have hparallelogram :
      ‖Real.cos t • firstBlock d q - Real.sin t • secondBlock d q‖ ^ 2 +
          ‖Real.sin t • firstBlock d q + Real.cos t • secondBlock d q‖ ^ 2 =
        ‖firstBlock d q‖ ^ 2 + ‖secondBlock d q‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_add_sq_real]
    simp only [real_inner_smul_left, real_inner_smul_right,
      norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]
    nlinarith [Real.sin_sq_add_cos_sq t]
  rw [hparallelogram, ← norm_sq_eq_blocks] at hsq
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp hsq

private theorem blockRotation_add (d : ℕ) (s t : ℝ) (q : E (d + d)) :
    blockRotation d s (blockRotation d t q) = blockRotation d (s + t) q := by
  apply (splitBlocks d).injective
  apply Prod.ext
  · change firstBlock d (blockRotation d s (blockRotation d t q)) =
      firstBlock d (blockRotation d (s + t) q)
    simp only [blockRotation, firstBlock_joinBlocks, secondBlock_joinBlocks]
    rw [Real.cos_add, Real.sin_add]
    module
  · change secondBlock d (blockRotation d s (blockRotation d t q)) =
      secondBlock d (blockRotation d (s + t) q)
    simp only [blockRotation, firstBlock_joinBlocks, secondBlock_joinBlocks]
    rw [Real.cos_add, Real.sin_add]
    module

private theorem blockRotation_zero (d : ℕ) (q : E (d + d)) :
    blockRotation d 0 q = q := by
  rw [blockRotation]
  simp only [Real.cos_zero, one_smul, Real.sin_zero, zero_smul, sub_zero,
    zero_add]
  exact joinBlocks_blocks d q

private theorem blockRotation_neg_cancel (d : ℕ) (t : ℝ) (q : E (d + d)) :
    blockRotation d t (blockRotation d (-t) q) = q := by
  rw [blockRotation_add, add_neg_cancel, blockRotation_zero]

private theorem continuous_blockRotation (d : ℕ) :
    Continuous (fun q : ℝ × E (d + d) ↦ blockRotation d q.1 q.2) := by
  have hfirst : Continuous (fun q : ℝ × E (d + d) ↦
      Real.cos q.1 • firstBlock d q.2 -
        Real.sin q.1 • secondBlock d q.2) :=
    ((Real.continuous_cos.comp continuous_fst).smul
      ((continuous_firstBlock d).comp continuous_snd)).sub
        ((Real.continuous_sin.comp continuous_fst).smul
          ((continuous_secondBlock d).comp continuous_snd))
  have hsecond : Continuous (fun q : ℝ × E (d + d) ↦
      Real.sin q.1 • firstBlock d q.2 +
        Real.cos q.1 • secondBlock d q.2) :=
    ((Real.continuous_sin.comp continuous_fst).smul
      ((continuous_firstBlock d).comp continuous_snd)).add
        ((Real.continuous_cos.comp continuous_fst).smul
          ((continuous_secondBlock d).comp continuous_snd))
  change Continuous (fun q : ℝ × E (d + d) ↦
    (splitBlocks d).symm
      (Real.cos q.1 • firstBlock d q.2 - Real.sin q.1 • secondBlock d q.2,
       Real.sin q.1 • firstBlock d q.2 + Real.cos q.1 • secondBlock d q.2))
  exact (splitBlocks d).symm.continuous.comp (hfirst.prodMk hsecond)

private def blockRotationMap (d : ℕ) : C(ℝ × E (d + d), E (d + d)) :=
  ⟨fun q ↦ blockRotation d q.1 q.2, continuous_blockRotation d⟩

private def sphereRotation (d : ℕ) :
    C(ℝ × Metric.sphere (0 : E (d + d)) 1,
      Metric.sphere (0 : E (d + d)) 1) where
  toFun q := ⟨blockRotationMap d (q.1, q.2), by
    rw [mem_sphere_zero_iff_norm]
    change ‖blockRotation d q.1 (q.2 : E (d + d))‖ = 1
    rw [norm_blockRotation]
    exact mem_sphere_zero_iff_norm.mp q.2.2⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact (blockRotationMap d).continuous.comp
      (continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd))

private theorem stableSphereMap_homotopic_second (d : ℕ)
    (f : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    ContinuousMap.Homotopic (stableSphereMap d f)
      (stableSphereMapSecond d f) := by
  let angle : unitInterval → ℝ := fun t ↦ (t : ℝ) * (Real.pi / 2)
  have hangle : Continuous (fun q : unitInterval ×
      Metric.sphere (0 : E (d + d)) 1 ↦ angle q.1) :=
    (continuous_subtype_val.comp continuous_fst).mul continuous_const
  let negativeInput : C(unitInterval × Metric.sphere (0 : E (d + d)) 1,
      ℝ × Metric.sphere (0 : E (d + d)) 1) :=
    { toFun := fun q ↦ (-angle q.1, q.2)
      continuous_toFun := hangle.neg.prodMk continuous_snd }
  let rotated : C(unitInterval × Metric.sphere (0 : E (d + d)) 1,
      Metric.sphere (0 : E (d + d)) 1) :=
    (sphereRotation d).comp negativeInput
  let mapped : C(unitInterval × Metric.sphere (0 : E (d + d)) 1,
      Metric.sphere (0 : E (d + d)) 1) :=
    (stableSphereMap d f).comp rotated
  let positiveInput : C(unitInterval × Metric.sphere (0 : E (d + d)) 1,
      ℝ × Metric.sphere (0 : E (d + d)) 1) :=
    { toFun := fun q ↦ (angle q.1, mapped q)
      continuous_toFun := hangle.prodMk mapped.continuous }
  let H : C(unitInterval × Metric.sphere (0 : E (d + d)) 1,
      Metric.sphere (0 : E (d + d)) 1) :=
    (sphereRotation d).comp positiveInput
  refine ⟨{
    toFun := H
    continuous_toFun := H.continuous
    map_zero_left := by
      intro q
      dsimp [H, positiveInput, mapped, rotated, negativeInput, sphereRotation,
        blockRotationMap]
      apply Subtype.ext
      change blockRotation d (angle 0)
          ((stableSphereMap d f) ⟨blockRotation d (-angle 0) q, _⟩) =
        (stableSphereMap d f q : E (d + d))
      simp [angle, blockRotation_zero]
    map_one_left := by
      intro q
      dsimp [H, positiveInput, mapped, rotated, negativeInput, sphereRotation,
        blockRotationMap]
      apply Subtype.ext
      change blockRotation d (angle 1)
          ((stableSphereMap d f) ⟨blockRotation d (-angle 1) q, _⟩) =
        (stableSphereMapSecond d f q : E (d + d))
      have hangleOne : angle 1 = Real.pi / 2 := by simp [angle]
      rw [hangleOne]
      change blockRotation d (Real.pi / 2)
          (joinBlocks d
            (radialExtension d f
              (firstBlock d (blockRotation d (-(Real.pi / 2)) q)))
            (secondBlock d (blockRotation d (-(Real.pi / 2)) q))) =
        joinBlocks d (firstBlock d q)
          (radialExtension d f (secondBlock d q))
      apply (splitBlocks d).injective
      apply Prod.ext <;>
        simp [blockRotation, Real.cos_pi_div_two, Real.sin_pi_div_two,
          firstBlock_joinBlocks, secondBlock_joinBlocks]
  }⟩

/-- After suspending a pair of sphere self-maps by a block of the same
dimension, their two composition orders are homotopic.  The proof moves one
map to the other coordinate block by a quarter-turn; maps acting on separate
blocks commute literally. -/
theorem stableSphereMap_comp_comm (d : ℕ)
    (f g : C(Metric.sphere (0 : E d) 1, Metric.sphere (0 : E d) 1)) :
    ContinuousMap.Homotopic (stableSphereMap d (f.comp g))
      (stableSphereMap d (g.comp f)) := by
  rw [stableSphereMap_comp, stableSphereMap_comp]
  have hmiddle : ContinuousMap.Homotopic
      ((stableSphereMapSecond d f).comp (stableSphereMap d g))
      ((stableSphereMap d g).comp (stableSphereMapSecond d f)) := by
    rw [stableMaps_different_blocks_commute]
  exact (ContinuousMap.Homotopic.comp
      (stableSphereMap_homotopic_second d f)
      (ContinuousMap.Homotopic.refl (stableSphereMap d g))).trans
    (hmiddle.trans (ContinuousMap.Homotopic.comp
      (ContinuousMap.Homotopic.refl (stableSphereMap d g))
      (stableSphereMap_homotopic_second d f).symm))

/-! ### Suspending an embedded sphere -/

def normalizedSpherePoint (d : ℕ) (x : E d) (hx : x ≠ 0) :
    Metric.sphere (0 : E d) 1 :=
  ⟨NormedSpace.normalize x, by
    rw [mem_sphere_zero_iff_norm]
    exact NormedSpace.norm_normalize hx⟩

def radialEmbeddingExtension (d : ℕ)
    (r : Metric.sphere (0 : E d) 1 → E d) (x : E d) : E d :=
  if hx : x = 0 then 0 else
    ‖x‖ • r (normalizedSpherePoint d x hx)

theorem radialEmbeddingExtension_zero (d : ℕ)
    (r : Metric.sphere (0 : E d) 1 → E d) :
    radialEmbeddingExtension d r 0 = 0 := by
  simp [radialEmbeddingExtension]

theorem continuous_radialEmbeddingExtension (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : E d) 1 → E d) (hcont : Continuous r) :
    Continuous (radialEmbeddingExtension d r) := by
  obtain ⟨R, hbound⟩ :=
    (isCompact_range hcont).isBounded.subset_ball (0 : E d)
  obtain ⟨z₀, hz₀⟩ :=
    (isConnected_sphere (euclidean_rank_gt_one d hd) 0
      (show (0 : ℝ) ≤ 1 by norm_num)).nonempty
  have hR : 0 < R := by
    have hz := hbound (show r ⟨z₀, hz₀⟩ ∈ Set.range r from ⟨_, rfl⟩)
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact (norm_nonneg _).trans_lt hz
  rw [continuous_iff_continuousAt]
  intro x
  by_cases hx : x = 0
  · subst x
    rw [Metric.continuousAt_iff]
    intro ε hε
    refine ⟨ε / R, div_pos hε hR, ?_⟩
    intro y hy
    rw [radialEmbeddingExtension_zero, dist_zero_right]
    rw [dist_zero_right] at hy
    by_cases hy0 : y = 0
    · simpa [hy0, radialEmbeddingExtension_zero] using hε
    · rw [radialEmbeddingExtension, dif_neg hy0, norm_smul,
        Real.norm_eq_abs, abs_norm]
      have hrlt : ‖r (normalizedSpherePoint d y hy0)‖ < R := by
        have hrange : r (normalizedSpherePoint d y hy0) ∈ Set.range r :=
          ⟨_, rfl⟩
        have := hbound hrange
        simpa only [Metric.mem_ball, dist_zero_right] using this
      have hynonneg : 0 ≤ ‖y‖ := norm_nonneg _
      calc
        ‖y‖ * ‖r (normalizedSpherePoint d y hy0)‖ ≤ ‖y‖ * R :=
          mul_le_mul_of_nonneg_left hrlt.le hynonneg
        _ < (ε / R) * R := mul_lt_mul_of_pos_right hy hR
        _ = ε := div_mul_cancel₀ ε hR.ne'
  · let P : Set (E d) := ({0} : Set (E d))ᶜ
    let normalizeMap : C(P, Metric.sphere (0 : E d) 1) :=
      { toFun := fun y ↦ ⟨NormedSpace.normalize (y : E d), by
          rw [mem_sphere_zero_iff_norm]
          exact NormedSpace.norm_normalize (by
            simpa only [P, mem_compl_iff, mem_singleton_iff] using y.2)⟩
        continuous_toFun := by
          apply Continuous.subtype_mk
          change Continuous (fun y : P ↦ ‖(y : E d)‖⁻¹ • (y : E d))
          exact ((continuous_subtype_val.norm).inv₀ (fun y ↦
            norm_ne_zero_iff.mpr (by
              simpa only [P, mem_compl_iff, mem_singleton_iff] using y.2))).smul
              continuous_subtype_val }
    let radialOnP : C(P, E d) :=
      { toFun := fun y ↦ ‖(y : E d)‖ • r (normalizeMap y)
        continuous_toFun := continuous_subtype_val.norm.smul
          (hcont.comp normalizeMap.continuous) }
    have hOn : ContinuousOn (radialEmbeddingExtension d r) P := by
      rw [continuousOn_iff_continuous_restrict]
      have heq : P.restrict (radialEmbeddingExtension d r) = radialOnP := by
        funext y
        change radialEmbeddingExtension d r (y : E d) =
          ‖(y : E d)‖ • r (normalizeMap y)
        rw [radialEmbeddingExtension, dif_neg (by
          simpa only [P, mem_compl_iff, mem_singleton_iff] using y.2)]
        congr 2
      rw [heq]
      exact radialOnP.continuous
    exact hOn.continuousAt
      (isOpen_compl_singleton.mem_nhds (by
        simpa only [P, mem_compl_iff, mem_singleton_iff] using hx))

private theorem normalizedSpherePoint_eq_of_radialEmbeddingExtension_eq
    (d : ℕ) (r : Metric.sphere (0 : E d) 1 → E d)
    (hinj : Function.Injective r) {x y : E d} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ‖x‖ = ‖y‖)
    (heq : radialEmbeddingExtension d r x =
      radialEmbeddingExtension d r y) :
    normalizedSpherePoint d x hx = normalizedSpherePoint d y hy := by
  rw [radialEmbeddingExtension, dif_neg hx,
    radialEmbeddingExtension, dif_neg hy] at heq
  have hnorm : ‖x‖ ≠ 0 := norm_ne_zero_iff.mpr hx
  apply hinj
  apply (smul_right_injective (E d) hnorm)
  simpa only [hxy] using heq

private theorem eq_of_norm_eq_of_normalizedSpherePoint_eq
    (d : ℕ) {x y : E d} (hx : x ≠ 0) (hy : y ≠ 0)
    (hxy : ‖x‖ = ‖y‖)
    (hnormalized : normalizedSpherePoint d x hx =
      normalizedSpherePoint d y hy) : x = y := by
  have hnormalized' : NormedSpace.normalize x = NormedSpace.normalize y :=
    congrArg Subtype.val hnormalized
  calc
    x = ‖x‖ • NormedSpace.normalize x := by
      symm
      exact NormedSpace.norm_smul_normalize x
    _ = ‖y‖ • NormedSpace.normalize y := by rw [hxy, hnormalized']
    _ = y := NormedSpace.norm_smul_normalize y

private theorem radialEmbeddingExtension_eq_of_norm_eq
    (d : ℕ) (r : Metric.sphere (0 : E d) 1 → E d)
    (hinj : Function.Injective r) {x y : E d} (hxy : ‖x‖ = ‖y‖)
    (heq : radialEmbeddingExtension d r x =
      radialEmbeddingExtension d r y) : x = y := by
  by_cases hx : x = 0
  · have hy : y = 0 := norm_eq_zero.mp (hxy ▸ (hx ▸ norm_zero))
    exact hx.trans hy.symm
  have hy : y ≠ 0 := by
    intro hy
    exact hx (norm_eq_zero.mp (hxy.trans (hy ▸ norm_zero)))
  apply eq_of_norm_eq_of_normalizedSpherePoint_eq d hx hy hxy
  exact normalizedSpherePoint_eq_of_radialEmbeddingExtension_eq
    d r hinj hx hy hxy heq

/-- The `d`-fold suspension of an embedded sphere, realized directly in the
block sum of two copies of the ambient Euclidean space. -/
def suspendedEmbedding (d : ℕ)
    (r : Metric.sphere (0 : E d) 1 → E d) :
    Metric.sphere (0 : E (d + d)) 1 → E (d + d) :=
  fun q ↦ joinBlocks d
    (radialEmbeddingExtension d r (firstBlock d q)) (secondBlock d q)

theorem continuous_suspendedEmbedding (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : E d) 1 → E d) (hcont : Continuous r) :
    Continuous (suspendedEmbedding d r) := by
  have hfirst : Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
      radialEmbeddingExtension d r (firstBlock d (q : E (d + d)))) :=
    (continuous_radialEmbeddingExtension d hd r hcont).comp
      ((continuous_firstBlock d).comp continuous_subtype_val)
  have hsecond : Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
      secondBlock d (q : E (d + d))) :=
    (continuous_secondBlock d).comp continuous_subtype_val
  change Continuous (fun q : Metric.sphere (0 : E (d + d)) 1 ↦
    (splitBlocks d).symm
      (radialEmbeddingExtension d r (firstBlock d q), secondBlock d q))
  exact (splitBlocks d).symm.continuous.comp (hfirst.prodMk hsecond)

theorem injective_suspendedEmbedding (d : ℕ)
    (r : Metric.sphere (0 : E d) 1 → E d) (hinj : Function.Injective r) :
    Function.Injective (suspendedEmbedding d r) := by
  intro p q hpq
  have hfirst : radialEmbeddingExtension d r (firstBlock d p) =
      radialEmbeddingExtension d r (firstBlock d q) := by
    have := congrArg (firstBlock d) hpq
    simpa only [suspendedEmbedding, firstBlock_joinBlocks] using this
  have hsecond : secondBlock d p = secondBlock d q := by
    have := congrArg (secondBlock d) hpq
    simpa only [suspendedEmbedding, secondBlock_joinBlocks] using this
  have hpSphere := mem_sphere_zero_iff_norm.mp p.2
  have hqSphere := mem_sphere_zero_iff_norm.mp q.2
  have hpNorm := norm_sq_eq_blocks d (p : E (d + d))
  have hqNorm := norm_sq_eq_blocks d (q : E (d + d))
  rw [hpSphere, one_pow, hsecond] at hpNorm
  rw [hqSphere, one_pow] at hqNorm
  have hnorm : ‖firstBlock d p‖ = ‖firstBlock d q‖ := by
    nlinarith [norm_nonneg (firstBlock d p), norm_nonneg (firstBlock d q)]
  have hfirst' : firstBlock d p = firstBlock d q :=
    radialEmbeddingExtension_eq_of_norm_eq d r hinj hnorm hfirst
  apply Subtype.ext
  rw [← joinBlocks_blocks d (p : E (d + d)),
    ← joinBlocks_blocks d (q : E (d + d)), hfirst', hsecond]

end

end Submission.Helpers
