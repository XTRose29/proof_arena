import Submission.AlgebraicTrefoil

open LeanEval.KnotTheory

namespace Submission.Symmetry

noncomputable section

structure NegativeSymmetry (K : Knot) where
  F : R3 → R3
  Finv : R3 → R3
  smooth : ContDiff ℝ (⊤ : ℕ∞) F
  smooth_inv : ContDiff ℝ (⊤ : ℕ∞) Finv
  inv_left : ∀ p, Finv (F p) = p
  inv_right : ∀ p, F (Finv p) = p
  det_neg : ∀ p, (fderiv ℝ F p).det < 0
  sigma : CircleReparam
  map_curve : ∀ t, F (K.curve t) = K.curve (sigma.f t)

def ofMirrorIsotopy {K : Knot} (Phi : AmbientIsotopy) (sigma : CircleReparam)
    (hendpoint : ∀ t, Phi.H 1 (K.curve t) = (Helpers.mirrorKnot K).curve (sigma.f t)) :
    NegativeSymmetry K where
  F p := reflectZ (Phi.H 1 p)
  Finv p := Phi.Hinv 1 (reflectZ p)
  smooth := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (Helpers.reflectZContinuousLinearEquiv ∘ Phi.H 1)
    exact Helpers.reflectZContinuousLinearEquiv.contDiff.comp
      (Orientation.slice_contDiff Phi 1)
  smooth_inv := by
    change ContDiff ℝ (⊤ : ℕ∞)
      (Phi.Hinv 1 ∘ Helpers.reflectZContinuousLinearEquiv)
    exact (Orientation.slice_inv_contDiff Phi 1).comp
      Helpers.reflectZContinuousLinearEquiv.contDiff
  inv_left := by
    intro p
    rw [Helpers.reflectZ_involutive, Phi.inv_left]
  inv_right := by
    intro p
    rw [Phi.inv_right, Helpers.reflectZ_involutive]
  det_neg := by
    intro p
    have hPhi : HasFDerivAt (Phi.H 1) (Orientation.spatialFDeriv Phi 1 p) p :=
      ((Orientation.slice_contDiff Phi 1).differentiable (by simp) p).hasFDerivAt
    have hcomp := Helpers.reflectZContinuousLinearEquiv.hasFDerivAt.comp p hPhi
    change (fderiv ℝ (Helpers.reflectZContinuousLinearEquiv ∘ Phi.H 1) p).det < 0
    rw [hcomp.fderiv]
    change LinearMap.det
      (Helpers.reflectZLinearEquiv.toLinearMap ∘ₗ
        (Orientation.spatialFDeriv Phi 1 p).toLinearMap) < 0
    rw [LinearMap.det_comp, Helpers.reflectZLinearEquiv_det]
    simpa using neg_lt_zero.mpr (Orientation.spatialFDeriv_det_pos Phi 1 p)
  sigma := sigma
  map_curve := by
    intro t
    rw [hendpoint]
    exact Helpers.reflectZ_involutive _

theorem exists_of_isotopic_mirror {K : Knot}
    (hiso : K.Isotopic (Helpers.mirrorKnot K)) : Nonempty (NegativeSymmetry K) := by
  rcases hiso with ⟨Phi, sigma, hendpoint⟩
  exact ⟨ofMirrorIsotopy Phi sigma hendpoint⟩

theorem chiral_of_no_negativeSymmetry (K : Knot)
    (h : ¬Nonempty (NegativeSymmetry K)) : K.Chiral := by
  rw [Helpers.chiral_iff_not_isotopic_mirror]
  exact fun hiso => h (exists_of_isotopic_mirror hiso)

end

end Submission.Symmetry
