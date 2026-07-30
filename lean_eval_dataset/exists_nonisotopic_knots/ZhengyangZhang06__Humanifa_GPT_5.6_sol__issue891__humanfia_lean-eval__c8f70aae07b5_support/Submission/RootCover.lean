import Submission.Unknot

open CategoryTheory Complex Set
open scoped ContinuousMap FundamentalGroupoid unitInterval

namespace Submission.RootCover

noncomputable section

/-- A polynomial parametrization of the roots of
`r ^ 3 + 135 * w * r - 720 * z`. -/
def rootMap (u : ℂ × ℂ) : ℂ × ℂ :=
  ((720 : ℂ)⁻¹ * (u.2 ^ 3 + u.1 * (u.2 * 135)), u.1)

private def rootSlope (u : ℂ × ℂ) : ℂ :=
  (3 * u.2 ^ 2 + 135 * u.1) / 720

private def rootCross (u : ℂ × ℂ) : ℂ :=
  135 * u.2 / 720

private def rootDerivative (u : ℂ × ℂ) : (ℂ × ℂ) →L[ℂ] (ℂ × ℂ) :=
  (((720 : ℂ)⁻¹ • (3 * u.2 ^ 2) • ContinuousLinearMap.snd ℂ ℂ ℂ) +
      (((720 : ℂ)⁻¹ • (u.1 * 135) • ContinuousLinearMap.snd ℂ ℂ ℂ) +
        ((720 : ℂ)⁻¹ • u.2 • (135 : ℂ) • ContinuousLinearMap.fst ℂ ℂ ℂ))).prod
    (ContinuousLinearMap.fst ℂ ℂ ℂ)

private theorem rootDerivative_apply (u v : ℂ × ℂ) :
    rootDerivative u v =
      (rootCross u * v.1 + rootSlope u * v.2, v.1) := by
  apply Prod.ext
  · simp [rootDerivative, rootSlope, rootCross]
    ring
  · rfl

private def rootDerivativeEquiv (u : ℂ × ℂ) (h : rootSlope u ≠ 0) :
    (ℂ × ℂ) ≃L[ℂ] (ℂ × ℂ) where
  toFun v := rootDerivative u v
  invFun v := (v.2, (v.1 - rootCross u * v.2) / rootSlope u)
  left_inv v := by
    apply Prod.ext
    · rfl
    · change ((rootDerivative u v).1 - rootCross u * (rootDerivative u v).2) /
        rootSlope u = v.2
      rw [rootDerivative_apply]
      dsimp
      field_simp [h]
      ring
  right_inv v := by
    apply Prod.ext
    · change (rootDerivative u
        (v.2, (v.1 - rootCross u * v.2) / rootSlope u)).1 = v.1
      rw [rootDerivative_apply]
      dsimp
      field_simp [h]
      ring
    · rfl
  map_add' x y := (rootDerivative u).map_add x y
  map_smul' c x := (rootDerivative u).map_smul c x
  continuous_toFun := (rootDerivative u).continuous
  continuous_invFun := by fun_prop

private theorem rootDerivativeEquiv_toContinuousLinearMap
    (u : ℂ × ℂ) (h : rootSlope u ≠ 0) :
    (rootDerivativeEquiv u h).toContinuousLinearMap = rootDerivative u := by
  apply ContinuousLinearMap.ext
  intro v
  rfl

private theorem rootMap_hasFDerivAt (u : ℂ × ℂ) :
    HasFDerivAt rootMap (rootDerivative u) u := by
  have hw : HasFDerivAt (fun v : ℂ × ℂ => v.1)
      (ContinuousLinearMap.fst ℂ ℂ ℂ) u := hasFDerivAt_fst
  have hr : HasFDerivAt (fun v : ℂ × ℂ => v.2)
      (ContinuousLinearMap.snd ℂ ℂ ℂ) u := hasFDerivAt_snd
  have hz := ((hr.pow 3).add ((hw.const_mul 135).mul hr)).const_smul ((720 : ℂ)⁻¹)
  change HasFDerivAt
    (fun x : ℂ × ℂ => ((720 : ℂ)⁻¹ * (x.2 ^ 3 + x.1 * (x.2 * 135)), x.1))
    (rootDerivative u) u
  simpa [rootDerivative, mul_comm, mul_left_comm, mul_assoc] using hz.prodMk hw

private theorem rootMap_contDiff : ContDiff ℂ (⊤ : ℕ∞) rootMap := by
  unfold rootMap
  fun_prop

private def rootMapLocalHomeomorph (u : ℂ × ℂ) (h : rootSlope u ≠ 0) :
    OpenPartialHomeomorph (ℂ × ℂ) (ℂ × ℂ) := by
  let e := rootDerivativeEquiv u h
  have hd : HasFDerivAt rootMap e.toContinuousLinearMap u := by
    rw [rootDerivativeEquiv_toContinuousLinearMap]
    exact rootMap_hasFDerivAt u
  exact (rootMap_contDiff.contDiffAt.toOpenPartialHomeomorph rootMap hd (by simp))

private theorem rootMap_mem_localHomeomorph_source (u : ℂ × ℂ)
    (h : rootSlope u ≠ 0) : u ∈ (rootMapLocalHomeomorph u h).source := by
  unfold rootMapLocalHomeomorph
  exact ContDiffAt.mem_toOpenPartialHomeomorph_source _ _ _

def ambientPolynomial (q : ℂ × ℂ) : ℂ :=
  64 * q.1 ^ 2 + 45 * q.2 ^ 3

def trefoilBaseSet : Set (ℂ × ℂ) :=
  {q | Complex.normSq q.1 + Complex.normSq q.2 = 1 ∧ ambientPolynomial q ≠ 0}

def trefoilBaseHomeomorph :
    Compactification.SphereTrefoilComplement ≃ₜ trefoilBaseSet where
  toFun q := ⟨q.1.1, q.1.2, q.2⟩
  invFun q := ⟨⟨q.1, q.2.1⟩, q.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by fun_prop

private theorem rootMap_mem_ball {u q : ℂ × ℂ}
    (hsphere : Complex.normSq q.1 + Complex.normSq q.2 = 1)
    (hmap : rootMap u = q) : u ∈ Metric.ball 0 21 := by
  have hzle : ‖q.1‖ ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsphere
    nlinarith [norm_nonneg q.1, norm_nonneg q.2]
  have hwle : ‖q.2‖ ≤ 1 := by
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq] at hsphere
    nlinarith [norm_nonneg q.1, norm_nonneg q.2]
  have hw : u.1 = q.2 := congrArg Prod.snd hmap
  have hz : (720 : ℂ)⁻¹ * (u.2 ^ 3 + u.1 * (u.2 * 135)) = q.1 :=
    congrArg Prod.fst hmap
  have hsum : u.2 ^ 3 + u.1 * (u.2 * 135) = 720 * q.1 := by
    calc
      u.2 ^ 3 + u.1 * (u.2 * 135) =
          720 * ((720 : ℂ)⁻¹ * (u.2 ^ 3 + u.1 * (u.2 * 135))) := by
            field_simp
      _ = 720 * q.1 := by rw [hz]
  have hcubic : u.2 ^ 3 = 720 * q.1 - u.1 * (u.2 * 135) := by
    rw [← hsum]
    ring
  have hnorm : ‖u.2‖ ^ 3 ≤ 720 + 135 * ‖u.2‖ := by
    calc
      ‖u.2‖ ^ 3 = ‖u.2 ^ 3‖ := by rw [norm_pow]
      _ = ‖720 * q.1 - u.1 * (u.2 * 135)‖ := congrArg norm hcubic
      _ ≤ ‖720 * q.1‖ + ‖u.1 * (u.2 * 135)‖ := norm_sub_le _ _
      _ = 720 * ‖q.1‖ + 135 * ‖u.1‖ * ‖u.2‖ := by
        simp
        ring
      _ ≤ 720 + 135 * ‖u.2‖ := by
        rw [hw]
        apply add_le_add
        · exact mul_le_of_le_one_right (by norm_num) hzle
        · apply mul_le_mul_of_nonneg_right _ (norm_nonneg u.2)
          exact mul_le_of_le_one_right (by norm_num) hwle
  have hrlt : ‖u.2‖ < 20 := by
    by_contra h
    have hge : 20 ≤ ‖u.2‖ := le_of_not_gt h
    have hfactor : 0 ≤ (‖u.2‖ - 20) *
        (‖u.2‖ ^ 2 + 20 * ‖u.2‖ + 265) := by
      apply mul_nonneg (sub_nonneg.mpr hge)
      nlinarith [sq_nonneg ‖u.2‖]
    nlinarith
  rw [Metric.mem_ball, dist_zero_right, Prod.norm_def, max_lt_iff]
  constructor
  · rw [hw]
    linarith
  · linarith

abbrev RootDomain := Metric.closedBall (0 : ℂ × ℂ) 21

noncomputable instance : CompactSpace RootDomain :=
  isCompact_iff_compactSpace.mp (isCompact_closedBall _ _)

def rootProjection (u : RootDomain) : ℂ × ℂ := rootMap u

private theorem rootProjection_continuous : Continuous rootProjection := by
  unfold rootProjection rootMap
  fun_prop

private theorem rootSlope_ne_of_mem_base {u : ℂ × ℂ}
    (hbase : rootMap u ∈ trefoilBaseSet) : rootSlope u ≠ 0 := by
  intro hslope
  have hcritical : u.2 ^ 2 + 45 * u.1 = 0 := by
    have h := hslope
    simp [rootSlope] at h
    linear_combination h / 3
  have hz : (rootMap u).1 = u.1 * u.2 / 8 := by
    simp [rootMap]
    rw [show u.2 ^ 3 = -45 * u.1 * u.2 by
      calc
        u.2 ^ 3 = u.2 * u.2 ^ 2 := by ring
        _ = u.2 * (-45 * u.1) := by rw [show u.2 ^ 2 = -45 * u.1 by
          linear_combination hcritical]
        _ = -45 * u.1 * u.2 := by ring]
    ring
  apply hbase.2
  unfold ambientPolynomial
  rw [hz]
  change 64 * (u.1 * u.2 / 8) ^ 2 + 45 * u.1 ^ 3 = 0
  calc
    64 * (u.1 * u.2 / 8) ^ 2 + 45 * u.1 ^ 3 =
        u.1 ^ 2 * (u.2 ^ 2 + 45 * u.1) := by ring
    _ = 0 := by rw [hcritical, mul_zero]

private def rootDomainLift (x : ℂ × ℂ) : RootDomain := by
  classical
  exact if hx : x ∈ Metric.closedBall (0 : ℂ × ℂ) 21 then
    ⟨x, hx⟩ else ⟨0, by norm_num⟩

private theorem rootDomainLift_val_of_mem {x : ℂ × ℂ}
    (hx : x ∈ Metric.closedBall (0 : ℂ × ℂ) 21) :
    (rootDomainLift x).1 = x := by
  classical
  simp [rootDomainLift, hx]

private def rootDomainInterior : OpenPartialHomeomorph RootDomain (ℂ × ℂ) where
  toPartialEquiv :=
    { toFun := Subtype.val
      invFun := rootDomainLift
      source := Subtype.val ⁻¹' Metric.ball (0 : ℂ × ℂ) 21
      target := Metric.ball (0 : ℂ × ℂ) 21
      map_source' := fun _ hx => hx
      map_target' := fun x hx => by
        change (rootDomainLift x).1 ∈ Metric.ball (0 : ℂ × ℂ) 21
        rw [rootDomainLift_val_of_mem (Metric.ball_subset_closedBall hx)]
        exact hx
      left_inv' := fun x hx => by
        apply Subtype.ext
        exact rootDomainLift_val_of_mem (Metric.ball_subset_closedBall hx)
      right_inv' := fun x hx => by
        exact rootDomainLift_val_of_mem (Metric.ball_subset_closedBall hx) }
  open_source := Metric.isOpen_ball.preimage continuous_subtype_val
  open_target := Metric.isOpen_ball
  continuousOn_toFun := continuous_subtype_val.continuousOn
  continuousOn_invFun := by
    rw [continuousOn_iff_continuous_restrict]
    apply Continuous.subtype_mk
    apply Continuous.congr continuous_subtype_val
    intro x
    exact (rootDomainLift_val_of_mem (Metric.ball_subset_closedBall x.2)).symm

private theorem rootProjection_isLocalHomeomorphOn :
    IsLocalHomeomorphOn rootProjection (rootProjection ⁻¹' trefoilBaseSet) := by
  apply IsLocalHomeomorphOn.mk
  intro u hu
  have hball : u.1 ∈ Metric.ball (0 : ℂ × ℂ) 21 :=
    rootMap_mem_ball hu.1 (rfl : rootMap u.1 = rootProjection u)
  have hslope : rootSlope u.1 ≠ 0 := rootSlope_ne_of_mem_base hu
  let e := rootDomainInterior.trans (rootMapLocalHomeomorph u.1 hslope)
  refine ⟨e, ?_, ?_⟩
  · exact ⟨hball, rootMap_mem_localHomeomorph_source u.1 hslope⟩
  · intro x hx
    change rootMap x.1 = rootMap x.1
    rfl

private theorem rootProjection_isCoveringMapOn :
    IsCoveringMapOn rootProjection trefoilBaseSet := by
  apply IsCoveringMapOn.of_openPartialHomeomorph rootProjection_continuous
  intro u hu
  rcases rootProjection_isLocalHomeomorphOn u hu with ⟨e, he, hEq⟩
  exact ⟨e, he, hEq.symm⟩

abbrev RestrictedRootTotal := {u : RootDomain // rootProjection u ∈ trefoilBaseSet}

def restrictedRootProjection : RestrictedRootTotal → trefoilBaseSet :=
  trefoilBaseSet.restrictPreimage rootProjection

private theorem restrictedRootProjection_isCoveringMap :
    IsCoveringMap restrictedRootProjection :=
  rootProjection_isCoveringMapOn.isCoveringMap_restrictPreimage

private theorem restrictedRootProjection_continuous :
    Continuous restrictedRootProjection := by
  apply Continuous.subtype_mk
  exact rootProjection_continuous.comp continuous_subtype_val

abbrev RootCoverTotal :=
  {p : RootDomain × trefoilBaseSet // rootProjection p.1 = p.2}

def rootCoverProjection (p : RootCoverTotal) : trefoilBaseSet := p.1.2

private def rootCoverTotalHomeomorph : RootCoverTotal ≃ₜ RestrictedRootTotal where
  toFun p := ⟨p.1.1, by
    rw [p.2]
    exact p.1.2.2⟩
  invFun p := ⟨(p.1, restrictedRootProjection p), rfl⟩
  left_inv p := by
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · apply Subtype.ext
      exact p.2
  right_inv _ := rfl
  continuous_toFun := by fun_prop
  continuous_invFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.prodMk restrictedRootProjection_continuous

theorem rootCoverProjection_isCoveringMap : IsCoveringMap rootCoverProjection := by
  have hcov := restrictedRootProjection_isCoveringMap.comp_homeomorph
    rootCoverTotalHomeomorph
  have heq : restrictedRootProjection ∘ rootCoverTotalHomeomorph =
      rootCoverProjection := by
    funext p
    apply Subtype.ext
    exact p.2
  rw [heq] at hcov
  exact hcov

private def fullTurn (t : ℝ) : ℂ :=
  Complex.exp (((2 * Real.pi * t : ℝ) : ℂ) * Complex.I)

private def halfTurn (t : ℝ) : ℂ :=
  Complex.exp (((Real.pi * t : ℝ) : ℂ) * Complex.I)

private theorem fullTurn_normSq (t : ℝ) : Complex.normSq (fullTurn t) = 1 := by
  unfold fullTurn
  rw [Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
  norm_num

private theorem fullTurn_ne_zero (t : ℝ) : fullTurn t ≠ 0 :=
  Complex.exp_ne_zero _

@[simp] private theorem fullTurn_zero : fullTurn 0 = 1 := by
  simp [fullTurn]

@[simp] private theorem fullTurn_one : fullTurn 1 = 1 := by
  apply Complex.ext <;>
    simp [fullTurn]

@[simp] private theorem halfTurn_zero : halfTurn 0 = 1 := by
  simp [halfTurn]

@[simp] private theorem halfTurn_one : halfTurn 1 = -1 := by
  apply Complex.ext <;>
    simp [halfTurn]

private theorem halfTurn_sq (t : ℝ) : halfTurn t ^ 2 = fullTurn t := by
  unfold halfTurn fullTurn
  rw [pow_two, ← Complex.exp_add]
  congr 1
  push_cast
  ring

private def baseA : trefoilBaseSet :=
  ⟨(0, 1), by
    constructor
    · simp [Complex.normSq_apply]
    · norm_num [ambientPolynomial]⟩

private def loopA : Path baseA baseA where
  toFun t := ⟨(0, fullTurn t), by
    constructor
    · simp [fullTurn_normSq]
    · simp [ambientPolynomial, fullTurn_ne_zero]⟩
  source' := by
    apply Subtype.ext
    simp [baseA]
  target' := by
    apply Subtype.ext
    simp [baseA]
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold fullTurn
    fun_prop [fullTurn]

private def rootA : ℂ := ((3 * Real.sqrt 15 : ℝ) : ℂ) * Complex.I

private theorem rootA_sq : rootA ^ 2 = -135 := by
  have hsqrt : (Real.sqrt 15) ^ 2 = 15 := by norm_num
  have hreal : (3 * Real.sqrt 15) ^ 2 = (135 : ℝ) := by
    rw [mul_pow, hsqrt]
    norm_num
  have hcomplex : (((3 * Real.sqrt 15 : ℝ) : ℂ) ^ 2) = 135 := by
    exact_mod_cast hreal
  unfold rootA
  rw [mul_pow, hcomplex]
  norm_num

private theorem rootA_ne_zero : rootA ≠ 0 := by
  intro h
  have := rootA_sq
  rw [h] at this
  norm_num at this

private def rootCoverPoint (u : ℂ × ℂ) (q : trefoilBaseSet)
    (hmap : rootMap u = q.1) : RootCoverTotal :=
  ⟨(⟨u, Metric.ball_subset_closedBall (rootMap_mem_ball q.2.1 hmap)⟩, q), by
    change rootMap u = q.1
    exact hmap⟩

private theorem rootMap_zeroRoot (w : ℂ) :
    rootMap (w, 0) = (0, w) := by
  simp [rootMap]

private theorem rootMap_turningRoot (t : ℝ) :
    rootMap (fullTurn t, rootA * halfTurn t) = (0, fullTurn t) := by
  apply Prod.ext
  · simp [rootMap]
    have hsquare : (rootA * halfTurn t) ^ 2 = -135 * fullTurn t := by
      rw [mul_pow, rootA_sq, halfTurn_sq]
    rw [show (rootA * halfTurn t) ^ 3 =
        (rootA * halfTurn t) * (-135 * fullTurn t) by
      calc
        (rootA * halfTurn t) ^ 3 =
            (rootA * halfTurn t) * (rootA * halfTurn t) ^ 2 := by ring
        _ = (rootA * halfTurn t) * (-135 * fullTurn t) := by rw [hsquare]]
    ring
  · rfl

private theorem rootMap_negTurningRoot (t : ℝ) :
    rootMap (fullTurn t, -rootA * halfTurn t) = (0, fullTurn t) := by
  have hp := congrArg Prod.fst (rootMap_turningRoot t)
  change (720 : ℂ)⁻¹ *
      ((rootA * halfTurn t) ^ 3 + fullTurn t * (rootA * halfTurn t * 135)) = 0 at hp
  apply Prod.ext
  · change (720 : ℂ)⁻¹ *
      ((-rootA * halfTurn t) ^ 3 + fullTurn t * (-rootA * halfTurn t * 135)) = 0
    linear_combination -hp
  · rfl

private def fiberZero : rootCoverProjection ⁻¹' {baseA} :=
  ⟨rootCoverPoint (1, 0) baseA (by simp [rootMap_zeroRoot, baseA]), rfl⟩

private def fiberPlus : rootCoverProjection ⁻¹' {baseA} :=
  ⟨rootCoverPoint (1, rootA) baseA (by
      change rootMap (1, rootA) = (0, 1)
      simpa using rootMap_turningRoot 0), rfl⟩

private def fiberMinus : rootCoverProjection ⁻¹' {baseA} :=
  ⟨rootCoverPoint (1, -rootA) baseA (by
      change rootMap (1, -rootA) = (0, 1)
      simpa using rootMap_turningRoot 1), rfl⟩

private def liftAZero : Path fiberZero.1 fiberZero.1 where
  toFun t := rootCoverPoint (fullTurn t, 0) (loopA t) (by
    change rootMap (fullTurn t, 0) = (0, fullTurn t)
    exact rootMap_zeroRoot (fullTurn t))
  source' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [fiberZero]
    · apply Subtype.ext
      exact congrArg Subtype.val loopA.source
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [fiberZero]
    · apply Subtype.ext
      exact congrArg Subtype.val loopA.target
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hroot : Continuous (fun t : I =>
        (⟨(fullTurn t, 0), by
          exact Metric.ball_subset_closedBall
            (rootMap_mem_ball (loopA t).2.1 (rootMap_zeroRoot (fullTurn t)))⟩ : RootDomain)) := by
      apply Continuous.subtype_mk
      unfold fullTurn
      fun_prop
    exact hroot.prodMk loopA.continuous

private def liftAPlus : Path fiberPlus.1 fiberMinus.1 where
  toFun t := rootCoverPoint (fullTurn t, rootA * halfTurn t) (loopA t)
    (rootMap_turningRoot t)
  source' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [fiberPlus]
    · apply Subtype.ext
      exact congrArg Subtype.val loopA.source
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [fiberMinus]
    · apply Subtype.ext
      exact congrArg Subtype.val loopA.target
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hroot : Continuous (fun t : I =>
        (⟨(fullTurn t, rootA * halfTurn t), by
          exact Metric.ball_subset_closedBall
            (rootMap_mem_ball (loopA t).2.1 (rootMap_turningRoot t))⟩ : RootDomain)) := by
      apply Continuous.subtype_mk
      unfold fullTurn halfTurn
      fun_prop
    exact hroot.prodMk loopA.continuous

private def liftAMinus : Path fiberMinus.1 fiberPlus.1 where
  toFun t := rootCoverPoint (fullTurn t, -rootA * halfTurn t) (loopA t)
    (rootMap_negTurningRoot t)
  source' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [fiberMinus]
    · apply Subtype.ext
      exact congrArg Subtype.val loopA.source
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      simp [fiberPlus]
    · apply Subtype.ext
      exact congrArg Subtype.val loopA.target
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hroot : Continuous (fun t : I =>
        (⟨(fullTurn t, -rootA * halfTurn t), by
          exact Metric.ball_subset_closedBall
            (rootMap_mem_ball (loopA t).2.1 (rootMap_negTurningRoot t))⟩ : RootDomain)) := by
      apply Continuous.subtype_mk
      unfold fullTurn halfTurn
      fun_prop
    exact hroot.prodMk loopA.continuous

private theorem liftAZero_projection :
  liftAZero.map rootCoverProjection_isCoveringMap.continuous = loopA := by
  apply Path.ext
  funext t
  rfl

private theorem liftAPlus_projection :
  liftAPlus.map rootCoverProjection_isCoveringMap.continuous = loopA := by
  apply Path.ext
  funext t
  rfl

private theorem liftAMinus_projection :
  liftAMinus.map rootCoverProjection_isCoveringMap.continuous = loopA := by
  apply Path.ext
  funext t
  rfl

private theorem monodromyA_zero :
    rootCoverProjection_isCoveringMap.monodromy (.mk loopA) fiberZero = fiberZero := by
  have h := rootCoverProjection_isCoveringMap.monodromy_map
    (Path.Homotopic.Quotient.mk liftAZero)
  rw [← Path.Homotopic.Quotient.mk_map, liftAZero_projection] at h
  exact h

private theorem monodromyA_plus :
    rootCoverProjection_isCoveringMap.monodromy (.mk loopA) fiberPlus = fiberMinus := by
  have h := rootCoverProjection_isCoveringMap.monodromy_map
    (Path.Homotopic.Quotient.mk liftAPlus)
  rw [← Path.Homotopic.Quotient.mk_map, liftAPlus_projection] at h
  exact h

private theorem monodromyA_minus :
    rootCoverProjection_isCoveringMap.monodromy (.mk loopA) fiberMinus = fiberPlus := by
  have h := rootCoverProjection_isCoveringMap.monodromy_map
    (Path.Homotopic.Quotient.mk liftAMinus)
  rw [← Path.Homotopic.Quotient.mk_map, liftAMinus_projection] at h
  exact h

private theorem fiber_classification (e : rootCoverProjection ⁻¹' {baseA}) :
    e = fiberZero ∨ e = fiberPlus ∨ e = fiberMinus := by
  have hbase : e.1.1.2 = baseA := by
    change rootCoverProjection e.1 = baseA
    exact Set.mem_singleton_iff.mp e.2
  have hmap : rootMap e.1.1.1.1 = (0, 1) := by
    calc
      rootMap e.1.1.1.1 = (e.1.1.2 : ℂ × ℂ) :=
        e.1.2
      _ = (baseA : ℂ × ℂ) :=
        congrArg (fun q : trefoilBaseSet => (q : ℂ × ℂ)) hbase
      _ = (0, 1) := rfl
  have hw : e.1.1.1.1.1 = 1 := congrArg Prod.snd hmap
  have hz : (720 : ℂ)⁻¹ *
      (e.1.1.1.1.2 ^ 3 + e.1.1.1.1.1 * (e.1.1.1.1.2 * 135)) = 0 :=
    congrArg Prod.fst hmap
  have hsum : e.1.1.1.1.2 ^ 3 +
      e.1.1.1.1.1 * (e.1.1.1.1.2 * 135) = 0 :=
    (mul_eq_zero.mp hz).resolve_left (inv_ne_zero (by norm_num))
  have hfactor : e.1.1.1.1.2 * (e.1.1.1.1.2 ^ 2 + 135) = 0 := by
    rw [hw] at hsum
    linear_combination hsum
  rcases mul_eq_zero.mp hfactor with hzero | hquad
  · left
    apply Subtype.ext
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext hw hzero
    · exact hbase
  · have hsplit : (e.1.1.1.1.2 - rootA) *
        (e.1.1.1.1.2 + rootA) = 0 := by
      calc
        (e.1.1.1.1.2 - rootA) * (e.1.1.1.1.2 + rootA) =
            e.1.1.1.1.2 ^ 2 - rootA ^ 2 := by ring
        _ = e.1.1.1.1.2 ^ 2 + 135 := by rw [rootA_sq]; ring
        _ = 0 := hquad
    rcases mul_eq_zero.mp hsplit with hplus | hminus
    · right; left
      have hr : e.1.1.1.1.2 = rootA := sub_eq_zero.mp hplus
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext hw hr
      · exact hbase
    · right; right
      have hr : e.1.1.1.1.2 = -rootA := eq_neg_of_add_eq_zero_left hminus
      apply Subtype.ext
      apply Subtype.ext
      apply Prod.ext
      · apply Subtype.ext
        exact Prod.ext hw hr
      · exact hbase

private theorem fiberPlus_ne_fiberMinus : fiberPlus ≠ fiberMinus := by
  intro h
  have hr := congrArg (fun e : rootCoverProjection ⁻¹' {baseA} => e.1.1.1.1.2) h
  change rootA = -rootA at hr
  apply rootA_ne_zero
  linear_combination hr / 2

private theorem monodromyA_fixed_iff (e : rootCoverProjection ⁻¹' {baseA}) :
    rootCoverProjection_isCoveringMap.monodromy (.mk loopA) e = e ↔
      e = fiberZero := by
  constructor
  · intro h
    rcases fiber_classification e with rfl | rfl | rfl
    · rfl
    · rw [monodromyA_plus] at h
      exact (fiberPlus_ne_fiberMinus h.symm).elim
    · rw [monodromyA_minus] at h
      exact (fiberPlus_ne_fiberMinus h).elim
  · rintro rfl
    exact monodromyA_zero

private def diagonalPhase : ℂ :=
  (((Real.sqrt 2 / 2 : ℝ) : ℂ)) * (1 + Complex.I)

private theorem diagonalPhase_normSq : Complex.normSq diagonalPhase = 1 := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hcoef : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    nlinarith
  have honeI : Complex.normSq (1 + Complex.I) = 2 := by
    norm_num [Complex.normSq_apply]
  unfold diagonalPhase
  rw [Complex.normSq_mul, Complex.normSq_ofReal, honeI]
  rw [← pow_two]
  rw [hcoef]
  norm_num

private theorem diagonalPhase_sq : diagonalPhase ^ 2 = Complex.I := by
  have hsqrt : (Real.sqrt 2) ^ 2 = 2 := by norm_num
  have hcoefReal : (Real.sqrt 2 / 2) ^ 2 = (1 / 2 : ℝ) := by
    nlinarith
  have hcoef : ((((Real.sqrt 2 / 2 : ℝ) : ℂ)) ^ 2) = (1 / 2 : ℂ) := by
    have hsqrtComplex : ((((Real.sqrt 2 : ℝ) : ℂ)) ^ 2) = 2 := by
      exact_mod_cast hsqrt
    calc
      (((Real.sqrt 2 / 2 : ℝ) : ℂ)) ^ 2 =
          (((Real.sqrt 2 : ℝ) : ℂ)) ^ 2 / 4 := by
            push_cast
            ring
      _ = (1 / 2 : ℂ) := by rw [hsqrtComplex]; norm_num
  have honeI : (1 + Complex.I) ^ 2 = 2 * Complex.I := by
    apply Complex.ext <;> norm_num [pow_two]
  unfold diagonalPhase
  rw [mul_pow, hcoef, honeI]
  ring

private theorem diagonalPhase_ne_zero : diagonalPhase ≠ 0 := by
  intro h
  have := diagonalPhase_normSq
  rw [h] at this
  norm_num at this

private def baseC : trefoilBaseSet :=
  ⟨(diagonalPhase, 0), by
    constructor
    · simp [diagonalPhase_normSq]
    · simp [ambientPolynomial, diagonalPhase_ne_zero]⟩

private theorem connector_mem_base (t : I) :
    (diagonalPhase * ((t : ℝ) : ℂ),
      (Real.sqrt (1 - (t : ℝ) ^ 2) : ℂ)) ∈
      trefoilBaseSet := by
  have ht0 : 0 ≤ (t : ℝ) := t.2.1
  have htle : (t : ℝ) ≤ 1 := t.2.2
  have htsq : 0 ≤ 1 - (t : ℝ) ^ 2 := by
    nlinarith [sq_nonneg ((t : ℝ) - 1)]
  constructor
  · rw [Complex.normSq_mul, diagonalPhase_normSq, one_mul,
      Complex.normSq_ofReal, Complex.normSq_ofReal,
      Real.mul_self_sqrt htsq]
    ring
  · intro hzero
    unfold ambientPolynomial at hzero
    rw [mul_pow, diagonalPhase_sq] at hzero
    change 64 * (Complex.I * (((t : ℝ) : ℂ) ^ 2)) +
      45 * (((Real.sqrt (1 - (t : ℝ) ^ 2) : ℝ) : ℂ) ^ 3) = 0 at hzero
    have hzero' : ((((64 * (t : ℝ) ^ 2 : ℝ) : ℂ)) * Complex.I) +
        (((45 * (Real.sqrt (1 - (t : ℝ) ^ 2)) ^ 3 : ℝ) : ℂ)) = 0 := by
      calc
        ((((64 * (t : ℝ) ^ 2 : ℝ) : ℂ)) * Complex.I) +
            (((45 * (Real.sqrt (1 - (t : ℝ) ^ 2)) ^ 3 : ℝ) : ℂ)) =
          64 * (Complex.I * (((t : ℝ) : ℂ) ^ 2)) +
            45 * (((Real.sqrt (1 - (t : ℝ) ^ 2) : ℝ) : ℂ) ^ 3) := by
              push_cast
              ring
        _ = 0 := hzero
    have him := congrArg Complex.im hzero'
    norm_num [Complex.ofReal_re, Complex.ofReal_im] at him
    have htpowRe : (((((t : ℝ) : ℂ)) ^ 2).re) = (t : ℝ) ^ 2 := by
      norm_num [pow_two]
    have hsqrtpowIm :
        ((((Real.sqrt (1 - (t : ℝ) ^ 2) : ℝ) : ℂ) ^ 3).im) = 0 := by
      have hcast : (((Real.sqrt (1 - (t : ℝ) ^ 2) : ℝ) : ℂ) ^ 3) =
          (((Real.sqrt (1 - (t : ℝ) ^ 2)) ^ 3 : ℝ) : ℂ) := by
        push_cast
        rfl
      rw [hcast]
      rfl
    rw [htpowRe, hsqrtpowIm] at him
    norm_num at him
    have ht : (t : ℝ) = 0 := congrArg Subtype.val him
    have hre := congrArg Complex.re hzero
    simp [ht] at hre

private def connector : Path baseA baseC where
  toFun t := ⟨(diagonalPhase * ((t : ℝ) : ℂ),
      (Real.sqrt (1 - (t : ℝ) ^ 2) : ℂ)), connector_mem_base t⟩
  source' := by
    apply Subtype.ext
    simp [baseA]
  target' := by
    apply Subtype.ext
    simp [baseC]
  continuous_toFun := by
    apply Continuous.subtype_mk
    fun_prop

private def loopC : Path baseC baseC where
  toFun t := ⟨(diagonalPhase * fullTurn t, 0), by
    constructor
    · rw [Complex.normSq_mul, diagonalPhase_normSq, fullTurn_normSq]
      simp
    · simp [ambientPolynomial, diagonalPhase_ne_zero, fullTurn_ne_zero]⟩
  source' := by
    apply Subtype.ext
    simp [baseC]
  target' := by
    apply Subtype.ext
    simp [baseC]
  continuous_toFun := by
    apply Continuous.subtype_mk
    unfold fullTurn
    fun_prop

private def thirdTurn (t : ℝ) : ℂ :=
  Complex.exp ((((2 * Real.pi * t / 3 : ℝ) : ℂ)) * Complex.I)

private theorem thirdTurn_cube (t : ℝ) : thirdTurn t ^ 3 = fullTurn t := by
  unfold thirdTurn fullTurn
  rw [pow_succ, pow_two]
  rw [← Complex.exp_add, ← Complex.exp_add]
  congr 1
  push_cast
  ring

@[simp] private theorem thirdTurn_zero : thirdTurn 0 = 1 := by
  simp [thirdTurn]

private theorem thirdTurn_one_ne_one : thirdTurn 1 ≠ 1 := by
  intro h
  have hthird : thirdTurn 1 =
      Complex.exp ((((2 * Real.pi / 3 : ℝ) : ℂ)) * Complex.I) := by
    unfold thirdTurn
    congr 1
    norm_num
  rw [hthird] at h
  have hre := congrArg Complex.re h
  have hre' : Real.cos (2 * Real.pi / 3) = 1 := by
    simpa only [Complex.exp_ofReal_mul_I_re, one_re] using hre
  have hangle : 2 * Real.pi / 3 = 2 * (Real.pi / 3) := by ring
  rw [hangle, Real.cos_two_mul, Real.cos_pi_div_three] at hre'
  norm_num at hre'

private theorem fiberC_base_eq (e : rootCoverProjection ⁻¹' {baseC}) :
    e.1.1.2 = baseC := by
  change rootCoverProjection e.1 = baseC
  exact Set.mem_singleton_iff.mp e.2

private theorem fiberC_rootMap (e : rootCoverProjection ⁻¹' {baseC}) :
    rootMap e.1.1.1.1 = (diagonalPhase, 0) := by
  calc
    rootMap e.1.1.1.1 = (e.1.1.2 : ℂ × ℂ) := e.1.2
    _ = (baseC : ℂ × ℂ) := congrArg
      (fun q : trefoilBaseSet => (q : ℂ × ℂ)) (fiberC_base_eq e)
    _ = (diagonalPhase, 0) := rfl

private theorem fiberC_w_zero (e : rootCoverProjection ⁻¹' {baseC}) :
    e.1.1.1.1.1 = 0 := congrArg Prod.snd (fiberC_rootMap e)

private theorem fiberC_root_cube (e : rootCoverProjection ⁻¹' {baseC}) :
    e.1.1.1.1.2 ^ 3 = 720 * diagonalPhase := by
  have hz := congrArg Prod.fst (fiberC_rootMap e)
  change (720 : ℂ)⁻¹ *
      (e.1.1.1.1.2 ^ 3 + e.1.1.1.1.1 * (e.1.1.1.1.2 * 135)) =
    diagonalPhase at hz
  rw [fiberC_w_zero e] at hz
  simp only [zero_mul] at hz
  have hz' : (720 : ℂ)⁻¹ * e.1.1.1.1.2 ^ 3 = diagonalPhase := by
    simpa using hz
  calc
    e.1.1.1.1.2 ^ 3 = 720 * ((720 : ℂ)⁻¹ * e.1.1.1.1.2 ^ 3) := by
      field_simp
    _ = 720 * diagonalPhase := by rw [hz']

private theorem fiberC_root_ne_zero (e : rootCoverProjection ⁻¹' {baseC}) :
    e.1.1.1.1.2 ≠ 0 := by
  intro hzero
  have hcube := fiberC_root_cube e
  rw [hzero] at hcube
  simp only [zero_pow (by norm_num : 3 ≠ 0)] at hcube
  apply diagonalPhase_ne_zero
  exact (mul_eq_zero.mp hcube.symm).resolve_left (by norm_num)

private def normalizedFiberC (e : rootCoverProjection ⁻¹' {baseC}) :
    rootCoverProjection ⁻¹' {baseC} :=
  ⟨rootCoverPoint e.1.1.1.1 baseC (fiberC_rootMap e), rfl⟩

private theorem normalizedFiberC_eq (e : rootCoverProjection ⁻¹' {baseC}) :
    normalizedFiberC e = e := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · apply Subtype.ext
    rfl
  · exact (fiberC_base_eq e).symm

private theorem rootMap_rotatingFiber (e : rootCoverProjection ⁻¹' {baseC}) (t : ℝ) :
    rootMap (0, e.1.1.1.1.2 * thirdTurn t) =
      (diagonalPhase * fullTurn t, 0) := by
  apply Prod.ext
  · simp [rootMap]
    rw [mul_pow, fiberC_root_cube e, thirdTurn_cube]
    field_simp
  · rfl

private def rotatedFiber (e : rootCoverProjection ⁻¹' {baseC}) :
    rootCoverProjection ⁻¹' {baseC} :=
  ⟨rootCoverPoint (0, e.1.1.1.1.2 * thirdTurn 1) baseC (by
      change rootMap (0, e.1.1.1.1.2 * thirdTurn 1) = (diagonalPhase, 0)
      simpa using rootMap_rotatingFiber e 1), rfl⟩

private theorem rotatedFiber_ne (e : rootCoverProjection ⁻¹' {baseC}) :
    rotatedFiber e ≠ normalizedFiberC e := by
  intro h
  have hr := congrArg
    (fun x : rootCoverProjection ⁻¹' {baseC} => x.1.1.1.1.2) h
  change e.1.1.1.1.2 * thirdTurn 1 = e.1.1.1.1.2 at hr
  apply thirdTurn_one_ne_one
  calc
    thirdTurn 1 = (e.1.1.1.1.2)⁻¹ *
        (e.1.1.1.1.2 * thirdTurn 1) := by
          field_simp [fiberC_root_ne_zero e]
    _ = (e.1.1.1.1.2)⁻¹ * e.1.1.1.1.2 := by rw [hr]
    _ = 1 := inv_mul_cancel₀ (fiberC_root_ne_zero e)

private def liftC (e : rootCoverProjection ⁻¹' {baseC}) :
    Path (normalizedFiberC e).1 (rotatedFiber e).1 where
  toFun t := rootCoverPoint (0, e.1.1.1.1.2 * thirdTurn t) (loopC t)
    (rootMap_rotatingFiber e t)
  source' := by
    rw [normalizedFiberC_eq]
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      apply Prod.ext
      · exact (fiberC_w_zero e).symm
      · change e.1.1.1.1.2 * thirdTurn 0 = e.1.1.1.1.2
        simp
    · exact loopC.source.trans (fiberC_base_eq e).symm
  target' := by
    apply Subtype.ext
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · exact loopC.target
  continuous_toFun := by
    apply Continuous.subtype_mk
    have hroot : Continuous (fun t : I =>
        (⟨(0, e.1.1.1.1.2 * thirdTurn t), by
          exact Metric.ball_subset_closedBall
            (rootMap_mem_ball (loopC t).2.1 (rootMap_rotatingFiber e t))⟩ : RootDomain)) := by
      apply Continuous.subtype_mk
      unfold thirdTurn
      fun_prop
    exact hroot.prodMk loopC.continuous

private theorem liftC_projection (e : rootCoverProjection ⁻¹' {baseC}) :
    (liftC e).map rootCoverProjection_isCoveringMap.continuous = loopC := by
  apply Path.ext
  funext t
  rfl

private theorem monodromyC (e : rootCoverProjection ⁻¹' {baseC}) :
    rootCoverProjection_isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk loopC) (normalizedFiberC e) = rotatedFiber e := by
  have h := rootCoverProjection_isCoveringMap.monodromy_map
    (Path.Homotopic.Quotient.mk (liftC e))
  rw [← Path.Homotopic.Quotient.mk_map, liftC_projection] at h
  exact h

private theorem monodromyC_ne (e : rootCoverProjection ⁻¹' {baseC}) :
    rootCoverProjection_isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk loopC) e ≠ e := by
  intro hfix
  have hfix' : rootCoverProjection_isCoveringMap.monodromy
      (Path.Homotopic.Quotient.mk loopC) (normalizedFiberC e) =
        normalizedFiberC e := by
    simpa only [normalizedFiberC_eq e] using hfix
  rw [monodromyC] at hfix'
  exact rotatedFiber_ne e hfix'

private def loopB : Path.Homotopic.Quotient baseA baseA :=
  (Path.Homotopic.Quotient.mk connector).trans
    ((Path.Homotopic.Quotient.mk loopC).trans
      (Path.Homotopic.Quotient.mk connector.symm))

private theorem monodromy_connector_inverse
    (e : rootCoverProjection ⁻¹' {baseA}) :
    rootCoverProjection_isCoveringMap.monodromy
        (Path.Homotopic.Quotient.mk connector.symm)
        (rootCoverProjection_isCoveringMap.monodromy
          (Path.Homotopic.Quotient.mk connector) e) = e := by
  have h := rootCoverProjection_isCoveringMap.monodromy_trans_apply
    (Path.Homotopic.Quotient.mk connector)
    (Path.Homotopic.Quotient.mk connector.symm) e
  rw [Path.Homotopic.Quotient.mk_symm,
    Path.Homotopic.Quotient.trans_symm,
    rootCoverProjection_isCoveringMap.monodromy_refl] at h
  exact h.symm

private theorem monodromyB_ne (e : rootCoverProjection ⁻¹' {baseA}) :
    rootCoverProjection_isCoveringMap.monodromy loopB e ≠ e := by
  intro hfix
  let y := rootCoverProjection_isCoveringMap.monodromy
    (Path.Homotopic.Quotient.mk connector) e
  apply monodromyC_ne y
  apply (rootCoverProjection_isCoveringMap.monodromy_bijective
    (Path.Homotopic.Quotient.mk connector.symm)).1
  have hinv := monodromy_connector_inverse e
  rw [loopB, rootCoverProjection_isCoveringMap.monodromy_trans_apply,
    rootCoverProjection_isCoveringMap.monodromy_trans_apply] at hfix
  exact hfix.trans hinv.symm

/-- The two explicit loops act noncommutatively on the three-sheeted root cover. -/
theorem trefoilBaseSet_not_hasAbelianFundamentalGroups :
    ¬ Helpers.HasAbelianFundamentalGroups trefoilBaseSet := by
  intro habelian
  have hcomm := habelian baseA
    (Path.Homotopic.Quotient.mk loopA) loopB
  change loopB.trans (Path.Homotopic.Quotient.mk loopA) =
    (Path.Homotopic.Quotient.mk loopA).trans loopB at hcomm
  have haction := congrArg
    (fun gamma : Path.Homotopic.Quotient baseA baseA =>
      rootCoverProjection_isCoveringMap.monodromy gamma fiberZero) hcomm
  rw [rootCoverProjection_isCoveringMap.monodromy_trans_apply,
    rootCoverProjection_isCoveringMap.monodromy_trans_apply,
    monodromyA_zero] at haction
  exact (monodromyB_ne fiberZero)
    ((monodromyA_fixed_iff
      (rootCoverProjection_isCoveringMap.monodromy loopB fiberZero)).mp haction)

private theorem not_hasAbelianFundamentalGroups_of_homeomorph
    {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₜ Y) (hY : ¬ Helpers.HasAbelianFundamentalGroups Y) :
    ¬ Helpers.HasAbelianFundamentalGroups X := by
  intro hX
  apply hY
  intro y a b
  let g := Helpers.fundamentalGroupMulEquivOfHomeomorph e.symm y
  apply g.injective
  simpa only [map_mul] using hX (e.symm y) (g a) (g b)

/-- The compactified complement of the checked algebraic trefoil has a
nonabelian fundamental group. -/
theorem trefoilCompactComplement_not_hasAbelianFundamentalGroups :
    ¬ Helpers.HasAbelianFundamentalGroups
      (Compactification.CompactComplement AlgebraicTrefoil.knot) := by
  let e := Compactification.trefoilCompactComplementHomeomorph.trans
    trefoilBaseHomeomorph
  exact not_hasAbelianFundamentalGroups_of_homeomorph e
    trefoilBaseSet_not_hasAbelianFundamentalGroups

end

end Submission.RootCover
