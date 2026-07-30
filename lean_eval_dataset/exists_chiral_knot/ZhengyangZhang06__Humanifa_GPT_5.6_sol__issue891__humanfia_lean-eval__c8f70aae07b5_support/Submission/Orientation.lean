import ChallengeDeps

open LeanEval.KnotTheory

namespace Submission.Orientation

noncomputable section

def spatialFDeriv (Phi : AmbientIsotopy) (t : ℝ) (x : R3) : R3 →L[ℝ] R3 :=
  fderiv ℝ (Phi.H t) x

def spatialFDerivInv (Phi : AmbientIsotopy) (t : ℝ) (x : R3) : R3 →L[ℝ] R3 :=
  fderiv ℝ (Phi.Hinv t) x

def frameMatrix (u v w : R3) : Matrix (Fin 3) (Fin 3) ℝ :=
  fun i j => (![u, v, w] j).ofLp i

def frameDet (u v w : R3) : ℝ :=
  Matrix.det (frameMatrix u v w)

theorem frameMatrix_map (L : R3 →ₗ[ℝ] R3) (u v w : R3) :
    frameMatrix (L u) (L v) (L w) =
      LinearMap.toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
        (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L * frameMatrix u v w := by
  ext i j
  fin_cases j
  · have h := congrFun (LinearMap.toMatrix_mulVec_repr
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L u) i
    simpa [frameMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      EuclideanSpace.basisFun_repr] using h.symm
  · have h := congrFun (LinearMap.toMatrix_mulVec_repr
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L v) i
    simpa [frameMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      EuclideanSpace.basisFun_repr] using h.symm
  · have h := congrFun (LinearMap.toMatrix_mulVec_repr
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis L w) i
    simpa [frameMatrix, Matrix.mul_apply, Matrix.mulVec, dotProduct,
      EuclideanSpace.basisFun_repr] using h.symm

theorem frameDet_map (L : R3 →ₗ[ℝ] R3) (u v w : R3) :
    frameDet (L u) (L v) (L w) = L.det * frameDet u v w := by
  rw [frameDet, frameMatrix_map, Matrix.det_mul, frameDet,
    ← LinearMap.det_toMatrix (EuclideanSpace.basisFun (Fin 3) ℝ).toBasis]

theorem slice_contDiff (Phi : AmbientIsotopy) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Phi.H t) := by
  exact Phi.smooth.comp (contDiff_const.prodMk contDiff_id)

theorem slice_inv_contDiff (Phi : AmbientIsotopy) (t : ℝ) :
    ContDiff ℝ (⊤ : ℕ∞) (Phi.Hinv t) := by
  exact Phi.smooth_inv.comp (contDiff_const.prodMk contDiff_id)

theorem spatialFDerivInv_comp_spatialFDeriv
    (Phi : AmbientIsotopy) (t : ℝ) (x : R3) :
    spatialFDerivInv Phi t (Phi.H t x) ∘L spatialFDeriv Phi t x =
      ContinuousLinearMap.id ℝ R3 := by
  have hH : HasFDerivAt (Phi.H t) (spatialFDeriv Phi t x) x :=
    ((slice_contDiff Phi t).differentiable (by simp) x).hasFDerivAt
  have hHinv : HasFDerivAt (Phi.Hinv t) (spatialFDerivInv Phi t (Phi.H t x))
      (Phi.H t x) :=
    ((slice_inv_contDiff Phi t).differentiable (by simp) (Phi.H t x)).hasFDerivAt
  have hcomp := hHinv.comp x hH
  have hid : HasFDerivAt (fun y : R3 => y) (ContinuousLinearMap.id ℝ R3) x :=
    hasFDerivAt_id x
  have hfun : Phi.Hinv t ∘ Phi.H t = id := by
    funext y
    exact Phi.inv_left t y
  rw [hfun] at hcomp
  exact hcomp.unique hid

theorem spatialFDeriv_injective (Phi : AmbientIsotopy) (t : ℝ) (x : R3) :
    Function.Injective (spatialFDeriv Phi t x) := by
  apply Function.LeftInverse.injective
    (g := spatialFDerivInv Phi t (Phi.H t x))
  intro v
  have h := congrArg
    (fun L : R3 →L[ℝ] R3 => L v)
    (spatialFDerivInv_comp_spatialFDeriv Phi t x)
  simpa using h

theorem spatialFDeriv_det_ne_zero (Phi : AmbientIsotopy) (t : ℝ) (x : R3) :
    (spatialFDeriv Phi t x).det ≠ 0 := by
  intro hdet
  exact (LinearMap.det_eq_zero_iff_ker_ne_bot.mp hdet)
    (LinearMap.ker_eq_bot.mpr (spatialFDeriv_injective Phi t x))

theorem spatialFDeriv_continuous (Phi : AmbientIsotopy) (x : R3) :
    Continuous (fun t => spatialFDeriv Phi t x) := by
  change Continuous (fun t => fderiv ℝ (Phi.H t) x)
  exact (Phi.smooth.fderiv
    (contDiff_const : ContDiff ℝ 0 (fun _ : ℝ => x)) (by simp)).continuous

theorem spatialFDeriv_det_continuous (Phi : AmbientIsotopy) (x : R3) :
    Continuous (fun t => (spatialFDeriv Phi t x).det) :=
  ContinuousLinearMap.continuous_det.comp (spatialFDeriv_continuous Phi x)

theorem spatialFDeriv_zero (Phi : AmbientIsotopy) (x : R3) :
    (spatialFDeriv Phi 0 x).det = 1 := by
  change (fderiv ℝ (Phi.H 0) x).det = 1
  rw [Phi.start, fderiv_id]
  change LinearMap.det (LinearMap.id : R3 →ₗ[ℝ] R3) = 1
  exact LinearMap.det_id

theorem spatialFDeriv_det_pos (Phi : AmbientIsotopy) (t : ℝ) (x : R3) :
    0 < (spatialFDeriv Phi t x).det := by
  have hne := spatialFDeriv_det_ne_zero Phi t x
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have hzero_mem : 0 ∈ Set.Icc ((spatialFDeriv Phi t x).det)
        ((spatialFDeriv Phi 0 x).det) := by
      rw [spatialFDeriv_zero]
      exact ⟨hneg.le, zero_le_one⟩
    obtain ⟨s, hs⟩ := intermediate_value_univ t 0
      (spatialFDeriv_det_continuous Phi x) hzero_mem
    exact (spatialFDeriv_det_ne_zero Phi s x hs).elim
  · exact hpos

theorem frameDet_spatialFDeriv_pos_iff
    (Phi : AmbientIsotopy) (t : ℝ) (x u v w : R3) :
    0 < frameDet (spatialFDeriv Phi t x u) (spatialFDeriv Phi t x v)
        (spatialFDeriv Phi t x w) ↔
      0 < frameDet u v w := by
  have hmap := frameDet_map (spatialFDeriv Phi t x).toLinearMap u v w
  change frameDet (spatialFDeriv Phi t x u) (spatialFDeriv Phi t x v)
      (spatialFDeriv Phi t x w) =
        (spatialFDeriv Phi t x).det * frameDet u v w at hmap
  rw [hmap]
  constructor
  · intro h
    exact pos_of_mul_pos_right h (spatialFDeriv_det_pos Phi t x).le
  · exact mul_pos (spatialFDeriv_det_pos Phi t x)

theorem circleReparam_deriv_pos (sigma : CircleReparam) (t : ℝ) :
    0 < deriv sigma.f t := by
  have hf : HasDerivAt sigma.f (deriv sigma.f t) t :=
    (sigma.smooth.differentiable (by simp) t).hasDerivAt
  have hfinv : HasDerivAt sigma.finv (deriv sigma.finv (sigma.f t)) (sigma.f t) :=
    (sigma.smooth_inv.differentiable (by simp) (sigma.f t)).hasDerivAt
  have hcomp := hfinv.comp t hf
  have hfun : sigma.finv ∘ sigma.f = id := by
    funext x
    exact sigma.left_inv x
  rw [hfun] at hcomp
  have hmul : deriv sigma.finv (sigma.f t) * deriv sigma.f t = 1 :=
    hcomp.unique (hasDerivAt_id t)
  have hne : deriv sigma.f t ≠ 0 := by
    intro hzero
    rw [hzero, mul_zero] at hmul
    norm_num at hmul
  exact lt_of_le_of_ne sigma.mono.monotone.deriv_nonneg (Ne.symm hne)

theorem endpoint_tangent
    {K1 K2 : Knot} (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hendpoint : ∀ t, Phi.H 1 (K1.curve t) = K2.curve (sigma.f t)) (t : ℝ) :
    spatialFDeriv Phi 1 (K1.curve t) (deriv K1.curve t) =
      deriv sigma.f t • deriv K2.curve (sigma.f t) := by
  have hK1 : HasDerivAt K1.curve (deriv K1.curve t) t :=
    (K1.smooth.differentiable (by simp) t).hasDerivAt
  have hPhi : HasFDerivAt (Phi.H 1) (spatialFDeriv Phi 1 (K1.curve t))
      (K1.curve t) :=
    ((slice_contDiff Phi 1).differentiable (by simp) (K1.curve t)).hasFDerivAt
  have hleft := hPhi.comp_hasDerivAt t hK1
  have hsigma : HasDerivAt sigma.f (deriv sigma.f t) t :=
    (sigma.smooth.differentiable (by simp) t).hasDerivAt
  have hK2 : HasDerivAt K2.curve (deriv K2.curve (sigma.f t)) (sigma.f t) :=
    (K2.smooth.differentiable (by simp) (sigma.f t)).hasDerivAt
  have hright := hK2.scomp t hsigma
  have hfun : Phi.H 1 ∘ K1.curve = K2.curve ∘ sigma.f := by
    funext x
    exact hendpoint x
  rw [hfun] at hleft
  exact hleft.unique hright

end

end Submission.Orientation
