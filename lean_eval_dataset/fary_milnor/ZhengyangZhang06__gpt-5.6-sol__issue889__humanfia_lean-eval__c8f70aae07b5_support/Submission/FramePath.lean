import Submission.PlaneFrame

open LeanEval.Geometry.FaryMilnorProblem
open Set
open Matrix
open scoped Real
open scoped RealInnerProductSpace
open WithLp

namespace Submission.Helpers

noncomputable def firstAxisCompanion (u : Space) : Space :=
  if u = coordinateAxis 0 then coordinateAxis 1
  else if u = -coordinateAxis 0 then coordinateAxis 1
  else normalizedDirection
    (coordinateAxis 0 - inner ℝ u (coordinateAxis 0) • u)

theorem firstAxisProjection_ne_zero {u : Space} (hu : ‖u‖ = 1)
    (hpos : u ≠ coordinateAxis 0) (hneg : u ≠ -coordinateAxis 0) :
    coordinateAxis 0 - inner ℝ u (coordinateAxis 0) • u ≠ 0 := by
  intro hzero
  have heq : coordinateAxis 0 = inner ℝ u (coordinateAxis 0) • u :=
    sub_eq_zero.mp hzero
  have hnorm := congrArg norm heq
  rw [norm_coordinateAxis, norm_smul, Real.norm_eq_abs, hu, mul_one] at hnorm
  rcases (abs_eq zero_le_one).mp hnorm.symm with hc | hc
  · apply hpos
    rw [hc] at heq
    simpa using heq.symm
  · apply hneg
    rw [hc] at heq
    have h := congrArg Neg.neg heq
    simpa using h.symm

theorem inner_firstAxisProjection {u : Space} (hu : ‖u‖ = 1) :
    inner ℝ u
      (coordinateAxis 0 - inner ℝ u (coordinateAxis 0) • u) = 0 := by
  rw [inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hu]
  ring

theorem norm_firstAxisCompanion {u : Space} (hu : ‖u‖ = 1) :
    ‖firstAxisCompanion u‖ = 1 := by
  by_cases hpos : u = coordinateAxis 0
  · subst u
    simp [firstAxisCompanion]
  · by_cases hneg : u = -coordinateAxis 0
    · subst u
      simp [firstAxisCompanion]
    · rw [firstAxisCompanion, if_neg hpos, if_neg hneg]
      exact norm_normalizedDirection (firstAxisProjection_ne_zero hu hpos hneg)

theorem inner_firstAxisCompanion {u : Space} (hu : ‖u‖ = 1) :
    inner ℝ u (firstAxisCompanion u) = 0 := by
  by_cases hpos : u = coordinateAxis 0
  · subst u
    simp [firstAxisCompanion]
  · by_cases hneg : u = -coordinateAxis 0
    · subst u
      simp [firstAxisCompanion]
    · rw [firstAxisCompanion, if_neg hpos, if_neg hneg, normalizedDirection,
        real_inner_smul_right, inner_firstAxisProjection hu, mul_zero]

noncomputable def firstAxisAngle (u : Space) : ℝ :=
  Real.arccos (inner ℝ u (coordinateAxis 0))

theorem abs_inner_firstAxis_le_one {u : Space} (hu : ‖u‖ = 1) :
    |inner ℝ u (coordinateAxis 0)| ≤ 1 := by
  simpa [hu] using abs_real_inner_le_norm u (coordinateAxis 0)

theorem firstAxisRotation_one {u : Space} (hu : ‖u‖ = 1) :
    planeRotation u (firstAxisCompanion u) (firstAxisAngle u) u =
      coordinateAxis 0 := by
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hvu : inner ℝ (firstAxisCompanion u) u = 0 := by
    rw [real_inner_comm, inner_firstAxisCompanion hu]
  rw [planeRotation_apply_left huu hvu]
  by_cases hpos : u = coordinateAxis 0
  · subst u
    simp [firstAxisAngle]
  · by_cases hneg : u = -coordinateAxis 0
    · subst u
      simp [firstAxisAngle]
    · rw [firstAxisCompanion, if_neg hpos, if_neg hneg]
      let c : ℝ := inner ℝ u (coordinateAxis 0)
      let p : Space := coordinateAxis 0 - c • u
      have hpne : p ≠ 0 := by
        exact firstAxisProjection_ne_zero hu hpos hneg
      have hcLower : -1 ≤ c := by
        have h := abs_inner_firstAxis_le_one hu
        exact (abs_le.mp h).1
      have hcUpper : c ≤ 1 := by
        have h := abs_inner_firstAxis_le_one hu
        exact (abs_le.mp h).2
      have hcos : Real.cos (firstAxisAngle u) = c := by
        exact Real.cos_arccos hcLower hcUpper
      have hsq : 1 - c ^ 2 = ‖p‖ ^ 2 := by
        rw [← real_inner_self_eq_norm_sq]
        dsimp [p, c]
        simp only [inner_sub_left, inner_sub_right, real_inner_smul_left,
          real_inner_smul_right]
        rw [huu, inner_coordinateAxis, if_pos rfl]
        rw [show inner ℝ (coordinateAxis 0) u =
            inner ℝ u (coordinateAxis 0) by rw [real_inner_comm]]
        ring
      have hsin : Real.sin (firstAxisAngle u) = ‖p‖ := by
        rw [firstAxisAngle, Real.sin_arccos, show 1 - inner ℝ u
            (coordinateAxis 0) ^ 2 = 1 - c ^ 2 by rfl, hsq,
          Real.sqrt_sq (norm_nonneg p)]
      rw [hcos, hsin]
      change c • u + ‖p‖ • normalizedDirection p = coordinateAxis 0
      rw [normalizedDirection, smul_smul]
      have hnormne : ‖p‖ ≠ 0 := norm_ne_zero_iff.mpr hpne
      rw [mul_inv_cancel₀ hnormne, one_smul]
      dsimp [p]
      module

theorem planeRotation_add (u v : Space) (theta : ℝ) (x y : Space) :
    planeRotation u v theta (x + y) =
      planeRotation u v theta x + planeRotation u v theta y := by
  simp only [planeRotation, inner_add_right]
  module

theorem planeRotation_smul (u v : Space) (theta c : ℝ) (x : Space) :
    planeRotation u v theta (c • x) = c • planeRotation u v theta x := by
  simp only [planeRotation, real_inner_smul_right]
  module

noncomputable def firstAxisRotation (u : Space) (s : ℝ) (x : Space) : Space :=
  planeRotation u (firstAxisCompanion u) (s * firstAxisAngle u) x

@[simp] theorem firstAxisRotation_zero (u x : Space) :
    firstAxisRotation u 0 x = x := by
  simp [firstAxisRotation, planeRotation]

theorem firstAxisRotation_end {u : Space} (hu : ‖u‖ = 1) :
    firstAxisRotation u 1 u = coordinateAxis 0 := by
  simpa [firstAxisRotation] using firstAxisRotation_one hu

theorem norm_firstAxisRotation {u x : Space} (hu : ‖u‖ = 1) (s : ℝ) :
    ‖firstAxisRotation u s x‖ = ‖x‖ := by
  apply norm_planeRotation
  · rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  · rw [real_inner_self_eq_norm_sq, norm_firstAxisCompanion hu]
    norm_num
  · exact inner_firstAxisCompanion hu

theorem firstAxisRotation_injective {u : Space} (hu : ‖u‖ = 1) (s : ℝ) :
    Function.Injective (firstAxisRotation u s) := by
  apply planeRotation_injective
  · rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  · rw [real_inner_self_eq_norm_sq, norm_firstAxisCompanion hu]
    norm_num
  · exact inner_firstAxisCompanion hu

theorem contDiff_firstAxisRotation (u : Space) :
    ContDiff ℝ ⊤ (fun p : Space × ℝ => firstAxisRotation u p.2 p.1) := by
  unfold firstAxisRotation
  exact (contDiff_planeRotation u (firstAxisCompanion u)).comp
    (contDiff_fst.prodMk (contDiff_snd.mul contDiff_const))

noncomputable def secondAxisVector (u d : Space) : Space :=
  firstAxisRotation u 1 d

noncomputable def secondAxisComplex (u d : Space) : ℂ :=
  ⟨secondAxisVector u d 1, secondAxisVector u d 2⟩

noncomputable def secondAxisAngle (u d : Space) : ℝ :=
  (secondAxisComplex u d).arg

theorem norm_secondAxisVector {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) : ‖secondAxisVector u d‖ = 1 := by
  rw [secondAxisVector, norm_firstAxisRotation hu, hd]

theorem secondAxisVector_coord_zero {u d : Space} (hu : ‖u‖ = 1)
    (hud : inner ℝ u d = 0) : secondAxisVector u d 0 = 0 := by
  rw [← inner_coordinateAxis_left]
  rw [← firstAxisRotation_end hu]
  unfold secondAxisVector firstAxisRotation
  exact inner_planeRotation_planeRotation
    (by rw [real_inner_self_eq_norm_sq, hu]; norm_num)
    (by rw [real_inner_self_eq_norm_sq, norm_firstAxisCompanion hu]; norm_num)
    (inner_firstAxisCompanion hu) |>.trans hud

theorem norm_secondAxisComplex {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) (hud : inner ℝ u d = 0) :
    ‖secondAxisComplex u d‖ = 1 := by
  have hvnorm := norm_secondAxisVector hu hd
  have hvzero := secondAxisVector_coord_zero hu hud
  have hsquare : ‖secondAxisComplex u d‖ ^ 2 = 1 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    have hspace : ‖secondAxisVector u d‖ ^ 2 = 1 := by rw [hvnorm]; norm_num
    rw [EuclideanSpace.real_norm_sq_eq] at hspace
    simpa [secondAxisComplex, Fin.sum_univ_succ, hvzero, pow_two] using hspace
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  simpa using hsquare

theorem secondAxisComplex_ne_zero {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) (hud : inner ℝ u d = 0) :
    secondAxisComplex u d ≠ 0 := by
  intro hzero
  have hnorm := norm_secondAxisComplex hu hd hud
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

theorem cos_secondAxisAngle {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) (hud : inner ℝ u d = 0) :
    Real.cos (secondAxisAngle u d) = secondAxisVector u d 1 := by
  rw [secondAxisAngle, Complex.cos_arg (secondAxisComplex_ne_zero hu hd hud),
    norm_secondAxisComplex hu hd hud]
  simp [secondAxisComplex]

theorem sin_secondAxisAngle {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) (hud : inner ℝ u d = 0) :
    Real.sin (secondAxisAngle u d) = secondAxisVector u d 2 := by
  rw [secondAxisAngle, Complex.sin_arg, norm_secondAxisComplex hu hd hud]
  simp [secondAxisComplex]

theorem secondAxisVector_eq {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) (hud : inner ℝ u d = 0) :
    secondAxisVector u d =
      Real.cos (secondAxisAngle u d) • coordinateAxis 1 +
        Real.sin (secondAxisAngle u d) • coordinateAxis 2 := by
  ext i
  fin_cases i
  · simp [secondAxisVector_coord_zero hu hud]
  · simp [cos_secondAxisAngle hu hd hud]
  · simp [sin_secondAxisAngle hu hd hud]

noncomputable def secondAxisRotation (u d : Space) (s : ℝ) (x : Space) : Space :=
  planeRotation (coordinateAxis 1) (coordinateAxis 2)
    (-s * secondAxisAngle u d) x

@[simp] theorem secondAxisRotation_zero (u d x : Space) :
    secondAxisRotation u d 0 x = x := by
  simp [secondAxisRotation, planeRotation]

theorem secondAxisRotation_firstAxis (u d : Space) (s : ℝ) :
    secondAxisRotation u d s (coordinateAxis 0) = coordinateAxis 0 := by
  simp [secondAxisRotation, planeRotation]

theorem secondAxisRotation_end {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) (hud : inner ℝ u d = 0) :
    secondAxisRotation u d 1 (secondAxisVector u d) = coordinateAxis 1 := by
  rw [secondAxisVector_eq hu hd hud]
  ext i
  fin_cases i <;>
    simp [secondAxisRotation, planeRotation, Real.cos_neg, Real.sin_neg]
  all_goals nlinarith [Real.sin_sq_add_cos_sq (secondAxisAngle u d)]

theorem secondAxisRotation_injective (u d : Space) (s : ℝ) :
    Function.Injective (secondAxisRotation u d s) := by
  apply planeRotation_injective <;> simp

theorem contDiff_secondAxisRotation (u d : Space) :
    ContDiff ℝ ⊤ (fun p : Space × ℝ => secondAxisRotation u d p.2 p.1) := by
  unfold secondAxisRotation
  have hangle : ContDiff ℝ ⊤ (fun p : Space × ℝ =>
      -p.2 * secondAxisAngle u d) := contDiff_snd.neg.mul contDiff_const
  have hpair : ContDiff ℝ ⊤ (fun p : Space × ℝ =>
      (p.1, -p.2 * secondAxisAngle u d)) := contDiff_fst.prodMk hangle
  exact (contDiff_planeRotation (coordinateAxis 1) (coordinateAxis 2)).comp hpair

noncomputable def frameRotation (u d : Space) (s : ℝ) (x : Space) : Space :=
  secondAxisRotation u d s (firstAxisRotation u s x)

theorem frameRotation_add (u d : Space) (s : ℝ) (x y : Space) :
    frameRotation u d s (x + y) =
      frameRotation u d s x + frameRotation u d s y := by
  simp [frameRotation, firstAxisRotation, secondAxisRotation, planeRotation_add]

theorem frameRotation_smul (u d : Space) (s c : ℝ) (x : Space) :
    frameRotation u d s (c • x) = c • frameRotation u d s x := by
  simp [frameRotation, firstAxisRotation, secondAxisRotation, planeRotation_smul]

@[simp] theorem frameRotation_zero (u d x : Space) :
    frameRotation u d 0 x = x := by
  simp [frameRotation]

theorem frameRotation_end_left {u d : Space} (hu : ‖u‖ = 1) :
    frameRotation u d 1 u = coordinateAxis 0 := by
  rw [frameRotation, firstAxisRotation_end hu,
    secondAxisRotation_firstAxis]

theorem frameRotation_end_right {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) (hud : inner ℝ u d = 0) :
    frameRotation u d 1 d = coordinateAxis 1 := by
  exact secondAxisRotation_end hu hd hud

theorem frameRotation_injective {u d : Space} (hu : ‖u‖ = 1) (s : ℝ) :
    Function.Injective (frameRotation u d s) :=
  (secondAxisRotation_injective u d s).comp (firstAxisRotation_injective hu s)

set_option maxHeartbeats 1000000 in
theorem contDiff_frameRotation (u d : Space) :
    ContDiff ℝ ⊤ (fun p : Space × ℝ => frameRotation u d p.2 p.1) := by
  have hfirst : ContDiff ℝ ⊤ (fun p : Space × ℝ =>
      firstAxisRotation u p.2 p.1) := contDiff_firstAxisRotation u
  have hpair : ContDiff ℝ ⊤ (fun p : Space × ℝ =>
      (firstAxisRotation u p.2 p.1, p.2)) := hfirst.prodMk contDiff_snd
  exact (contDiff_secondAxisRotation u d).comp hpair

noncomputable def frameNormal (u d : Space) : Space :=
  toLp 2 (crossProduct (ofLp u) (ofLp d))

theorem inner_left_frameNormal (u d : Space) :
    inner ℝ u (frameNormal u d) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  exact dot_self_cross _ _

theorem inner_right_frameNormal (u d : Space) :
    inner ℝ d (frameNormal u d) = 0 := by
  rw [EuclideanSpace.inner_eq_star_dotProduct, dotProduct_comm]
  exact dot_cross_self _ _

theorem norm_frameNormal {u d : Space} (hu : ‖u‖ = 1) (hd : ‖d‖ = 1)
    (hud : inner ℝ u d = 0) : ‖frameNormal u d‖ = 1 := by
  have huuInner : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hddInner : inner ℝ d d = 1 := by
    rw [real_inner_self_eq_norm_sq, hd]
    norm_num
  rw [EuclideanSpace.inner_eq_star_dotProduct] at huuInner hddInner hud
  have huu : ofLp u ⬝ᵥ ofLp u = 1 := by simpa using huuInner
  have hdd : ofLp d ⬝ᵥ ofLp d = 1 := by simpa using hddInner
  have hdu : ofLp d ⬝ᵥ ofLp u = 0 := by simpa using hud
  have hud' : ofLp u ⬝ᵥ ofLp d = 0 := by rw [dotProduct_comm, hdu]
  apply (sq_eq_sq₀ (norm_nonneg _) zero_le_one).mp
  rw [← real_inner_self_eq_norm_sq, EuclideanSpace.inner_eq_star_dotProduct]
  simp [frameNormal, cross_dot_cross, huu, hdd, hud', hdu]

noncomputable def frameEmbedding (u d : Space) (lambda : ℝ) (x : Space) : Space :=
  x 0 • u + (lambda * x 1) • d + x 2 • frameNormal u d

theorem frameEmbedding_injective {u d : Space} (hu : ‖u‖ = 1)
    (hd : ‖d‖ = 1) (hud : inner ℝ u d = 0) {lambda : ℝ}
    (hlambda : lambda ≠ 0) : Function.Injective (frameEmbedding u d lambda) := by
  intro x y hxy
  have huu : inner ℝ u u = 1 := by
    rw [real_inner_self_eq_norm_sq, hu]
    norm_num
  have hdd : inner ℝ d d = 1 := by
    rw [real_inner_self_eq_norm_sq, hd]
    norm_num
  have hdu : inner ℝ d u = 0 := by rwa [real_inner_comm]
  have h0 := congrArg (fun z : Space => inner ℝ u z) hxy
  have h1 := congrArg (fun z : Space => inner ℝ d z) hxy
  have h2 := congrArg (fun z : Space => inner ℝ (frameNormal u d) z) hxy
  have hn : inner ℝ (frameNormal u d) (frameNormal u d) = 1 := by
    rw [real_inner_self_eq_norm_sq, norm_frameNormal hu hd hud]
    norm_num
  have hnU : inner ℝ (frameNormal u d) u = 0 := by
    rw [real_inner_comm, inner_left_frameNormal]
  have hnD : inner ℝ (frameNormal u d) d = 0 := by
    rw [real_inner_comm, inner_right_frameNormal]
  simp only [frameEmbedding, inner_add_right, real_inner_smul_right,
    huu, hdd, hud, hdu, inner_left_frameNormal, inner_right_frameNormal,
    hn, hnU, hnD, mul_one, mul_zero, add_zero, zero_add] at h0 h1 h2
  ext i
  fin_cases i
  · exact h0
  · exact (mul_left_cancel₀ hlambda h1)
  · exact h2

noncomputable def frameEmbeddingCLM (u d : Space) (lambda : ℝ) :
    Space →L[ℝ] Space :=
  (spaceCoordinateCLM 0).smulRight u +
    (lambda • spaceCoordinateCLM 1).smulRight d +
      (spaceCoordinateCLM 2).smulRight (frameNormal u d)

@[simp] theorem frameEmbeddingCLM_apply (u d : Space) (lambda : ℝ) (x : Space) :
    frameEmbeddingCLM u d lambda x = frameEmbedding u d lambda x := by
  simp [frameEmbeddingCLM, frameEmbedding, spaceCoordinateCLM,
    ofLpContinuousLinearMap]

theorem velocity_continuousLinearMap {q : ℝ → Space} (hq : IsSmoothKnot q)
    (L : Space →L[ℝ] Space) (t : ℝ) :
    velocity (fun z => L (q z)) t = L (velocity q t) := by
  have h := L.hasFDerivAt.comp_hasDerivAt t (hasDerivAt_curve hq t)
  exact h.deriv

theorem isSmoothKnot_continuousLinearMap {q : ℝ → Space} (hq : IsSmoothKnot q)
    (L : Space →L[ℝ] Space) (hL : Function.Injective L) :
    IsSmoothKnot (fun t => L (q t)) where
  smooth := L.contDiff.comp hq.smooth
  periodic := by
    intro t
    change L (q (t + period)) = L (q t)
    rw [hq.periodic t]
  injective_on_period := by
    intro x hx y hy hxy
    exact hq.injective_on_period hx hy (hL hxy)
  regular := by
    intro t hzero
    rw [velocity_continuousLinearMap hq L t] at hzero
    apply hq.regular t
    apply hL
    simpa using hzero

theorem isSmoothKnot_frameEmbedding {q : ℝ → Space} (hq : IsSmoothKnot q)
    {u d : Space} (hu : ‖u‖ = 1) (hd : ‖d‖ = 1)
    (hud : inner ℝ u d = 0) {lambda : ℝ} (hlambda : lambda ≠ 0) :
    IsSmoothKnot (fun t => frameEmbedding u d lambda (q t)) := by
  apply isSmoothKnot_continuousLinearMap hq (frameEmbeddingCLM u d lambda)
  intro x y hxy
  apply frameEmbedding_injective hu hd hud hlambda
  simpa using hxy

noncomputable def planeRotationLM (u v : Space) (theta : ℝ) :
    Space →ₗ[ℝ] Space where
  toFun := planeRotation u v theta
  map_add' := planeRotation_add u v theta
  map_smul' := planeRotation_smul u v theta

noncomputable def planeRotationCLM (u v : Space) (theta : ℝ) :
    Space →L[ℝ] Space :=
  ⟨planeRotationLM u v theta,
    (planeRotationLM u v theta).continuous_of_finiteDimensional⟩

@[simp] theorem planeRotationCLM_apply (u v : Space) (theta : ℝ) (x : Space) :
    planeRotationCLM u v theta x = planeRotation u v theta x := rfl

theorem isSmoothKnot_planeRotation {q : ℝ → Space} (hq : IsSmoothKnot q)
    {u v : Space} (hu : inner ℝ u u = 1) (hv : inner ℝ v v = 1)
    (huv : inner ℝ u v = 0) (theta : ℝ) :
    IsSmoothKnot (fun t => planeRotation u v theta (q t)) := by
  apply isSmoothKnot_continuousLinearMap hq (planeRotationCLM u v theta)
  intro x y hxy
  apply planeRotation_injective hu hv huv
  simpa using hxy

theorem isSmoothKnot_frameRotation {q : ℝ → Space} (hq : IsSmoothKnot q)
    {u d : Space} (hu : ‖u‖ = 1) (s : ℝ) :
    IsSmoothKnot (fun t => frameRotation u d s (q t)) := by
  have hfirst : IsSmoothKnot (fun t => firstAxisRotation u s (q t)) := by
    exact isSmoothKnot_planeRotation hq
      (by rw [real_inner_self_eq_norm_sq, hu]; norm_num)
      (by rw [real_inner_self_eq_norm_sq, norm_firstAxisCompanion hu]; norm_num)
      (inner_firstAxisCompanion hu) _
  exact isSmoothKnot_planeRotation hfirst (by simp) (by simp) (by simp) _

end Submission.Helpers
