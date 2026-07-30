import Submission.PesinFullEndpointBlock
import Submission.PesinStructuralCarrier
import Submission.SecantLinearization

namespace Submission.Helpers

open LeanEval.Dynamics

lemma norm_lyapunovStableComponent_le_of_mem_fullShadowingBlock
    (T T_inv : EucPlane → EucPlane) {lam1 lam2 eta : ℝ} {C : ℕ}
    {x : EucPlane}
    (hx : x ∈ pesinFullShadowingBlock T T_inv lam1 lam2 eta C) :
    ‖lyapunovStableComponent T T_inv x‖ ≤ C := by
  simpa using (hx.1.1.1.1.1.2 0).1

lemma norm_lyapunovUnstableComponent_le_of_mem_fullShadowingBlock
    (T T_inv : EucPlane → EucPlane) {lam1 lam2 eta : ℝ} {C : ℕ}
    {x : EucPlane}
    (hx : x ∈ pesinFullShadowingBlock T T_inv lam1 lam2 eta C) :
    ‖lyapunovUnstableComponent T T_inv x‖ ≤ C := by
  simpa using (hx.1.1.1.1.1.2 0).2.1

lemma norm_stable_derivative_segment_le_of_leftFullEndpoint
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hcov : ∀ z ∈ carrier,
      lyapunovStableComponent T T_inv (T z) ∘L fderiv ℝ T z =
        fderiv ℝ T z ∘L lyapunovStableComponent T T_inv z)
    {lam1 lam2 eta : ℝ} {C : ℕ} {x : EucPlane} {n : ℕ}
    (hxcarrier : x ∈ carrier)
    (hxLeft : x ∈ pesinFullShadowingBlock T T_inv lam1 lam2 eta C) :
    ‖lyapunovStableComponent T T_inv (T^[n] x) ∘L
        fderiv ℝ (T^[n]) x‖ ≤
      C * Real.exp ((lam2 + 6 * eta) * n) := by
  rw [stableComponent_fderiv_iterate_covariant_on_structuralCarrier
    T hT_smooth (lyapunovStableComponent T T_inv) hcarrier hcov
      hxcarrier n]
  exact (hxLeft.1.1.1.1.1.1 n).1

lemma norm_unstable_inverse_segment_le_of_rightFullEndpoint
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hcov : ∀ z ∈ carrier,
      lyapunovUnstableComponent T T_inv (T z) ∘L fderiv ℝ T z =
        fderiv ℝ T z ∘L lyapunovUnstableComponent T T_inv z)
    {lam1 lam2 eta : ℝ} {C : ℕ} {x : EucPlane} {n : ℕ}
    (hxcarrier : x ∈ carrier)
    (hxRight : T^[n] x ∈
      pesinFullShadowingBlock T T_inv lam1 lam2 eta C) :
    ‖lyapunovUnstableComponent T T_inv x ∘L
        fderiv ℝ (T_inv^[n]) (T^[n] x)‖ ≤
      C * Real.exp ((-lam1 + 6 * eta) * n) := by
  let D := fderiv ℝ (T^[n]) x
  let R := fderiv ℝ (T_inv^[n]) (T^[n] x)
  let U₀ := lyapunovUnstableComponent T T_inv x
  let Uₙ := lyapunovUnstableComponent T T_inv (T^[n] x)
  have hcovn : Uₙ ∘L D = D ∘L U₀ := by
    exact stableComponent_fderiv_iterate_covariant_on_structuralCarrier
      T hT_smooth (lyapunovUnstableComponent T T_inv) hcarrier hcov
        hxcarrier n
  have hRD : R ∘L D = ContinuousLinearMap.id ℝ EucPlane := by
    rw [show R = D.inverse by
      exact (fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x).symm]
    exact fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
  have hDR : D ∘L R = ContinuousLinearMap.id ℝ EucPlane := by
    rw [show R = D.inverse by
      exact (fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x).symm]
    exact fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
  have heq : U₀ ∘L R = R ∘L Uₙ := by
    calc
      U₀ ∘L R = (R ∘L D) ∘L (U₀ ∘L R) := by rw [hRD]; simp
      _ = R ∘L (D ∘L U₀) ∘L R := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L (Uₙ ∘L D) ∘L R := by rw [hcovn]
      _ = (R ∘L Uₙ) ∘L (D ∘L R) := by
        simp only [ContinuousLinearMap.comp_assoc]
      _ = R ∘L Uₙ := by rw [hDR]; simp
  rw [heq]
  exact (hxRight.1.1.1.1.1.1 n).2

/-- A secant segment based at a full Pesin endpoint inherits the stable
contraction of its derivative, up to the operator error of the secant
product. -/
lemma norm_stable_orbit_displacement_le_of_secant_error
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hcov : ∀ z ∈ carrier,
      lyapunovStableComponent T T_inv (T z) ∘L fderiv ℝ T z =
        fderiv ℝ T z ∘L lyapunovStableComponent T T_inv z)
    {lam1 lam2 eta e : ℝ} {C : ℕ} {x y : EucPlane} {n : ℕ}
    (hxcarrier : x ∈ carrier)
    (hxLeft : x ∈ pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
    (hxRight : T^[n] x ∈
      pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
    (herror :
      ‖clmPrefixProduct (orbitSecantStep T x y) n -
          fderiv ℝ (T^[n]) x‖ ≤ e) :
    ‖lyapunovStableComponent T T_inv (T^[n] x)
        (T^[n] y - T^[n] x)‖ ≤
      (C * Real.exp ((lam2 + 6 * eta) * n) + C * e) * ‖y - x‖ := by
  let A := clmPrefixProduct (orbitSecantStep T x y) n
  let D := fderiv ℝ (T^[n]) x
  let S := lyapunovStableComponent T T_inv (T^[n] x)
  have hAxy : A (y - x) = T^[n] y - T^[n] x :=
    clmPrefixProduct_orbitSecantStep_apply T x y n
  have hsegment : ‖S ∘L D‖ ≤
      C * Real.exp ((lam2 + 6 * eta) * n) := by
    simpa [S, D] using
      norm_stable_derivative_segment_le_of_leftFullEndpoint
        T T_inv hT_smooth hcarrier hcov hxcarrier hxLeft
  have hSnorm : ‖S‖ ≤ C := by
    simpa [S] using
      norm_lyapunovStableComponent_le_of_mem_fullShadowingBlock
        T T_inv hxRight
  calc
    ‖lyapunovStableComponent T T_inv (T^[n] x)
        (T^[n] y - T^[n] x)‖ = ‖S (A (y - x))‖ := by
      rw [hAxy]
    _ = ‖(S ∘L D) (y - x) + S ((A - D) (y - x))‖ := by
      congr 1
      change S (A (y - x)) = S (D (y - x)) +
        S (A (y - x) - D (y - x))
      rw [S.map_sub]
      abel
    _ ≤ ‖(S ∘L D) (y - x)‖ + ‖S ((A - D) (y - x))‖ :=
      norm_add_le _ _
    _ ≤ ‖S ∘L D‖ * ‖y - x‖ + ‖S‖ * (‖A - D‖ * ‖y - x‖) := by
      exact add_le_add ((S ∘L D).le_opNorm (y - x))
        (S.le_opNorm _ |>.trans
          (mul_le_mul_of_nonneg_left ((A - D).le_opNorm (y - x))
            (norm_nonneg S)))
    _ ≤ (C * Real.exp ((lam2 + 6 * eta) * n)) * ‖y - x‖ +
          C * (e * ‖y - x‖) := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hsegment (norm_nonneg _))
        (mul_le_mul hSnorm
          (mul_le_mul_of_nonneg_right herror (norm_nonneg _))
          (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (Nat.cast_nonneg C))
    _ = (C * Real.exp ((lam2 + 6 * eta) * n) + C * e) * ‖y - x‖ := by
      ring

/-- The inverse derivative segment based at a full right endpoint controls the
unstable component at the left endpoint.  Replacing the derivative by the
secant product introduces one relative error term. -/
lemma norm_unstable_orbit_displacement_le_of_secant_error
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {carrier : Set EucPlane} (hcarrier : T '' carrier = carrier)
    (hcov : ∀ z ∈ carrier,
      lyapunovUnstableComponent T T_inv (T z) ∘L fderiv ℝ T z =
        fderiv ℝ T z ∘L lyapunovUnstableComponent T T_inv z)
    {lam1 lam2 eta e : ℝ} {C : ℕ} {x y : EucPlane} {n : ℕ}
    (hxcarrier : x ∈ carrier)
    (hxRight : T^[n] x ∈
      pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
    (herror :
      ‖clmPrefixProduct (orbitSecantStep T x y) n -
          fderiv ℝ (T^[n]) x‖ ≤ e) :
    ‖lyapunovUnstableComponent T T_inv x (y - x)‖ ≤
      C * Real.exp ((-lam1 + 6 * eta) * n) *
        (‖T^[n] y - T^[n] x‖ + e * ‖y - x‖) := by
  let A := clmPrefixProduct (orbitSecantStep T x y) n
  let D := fderiv ℝ (T^[n]) x
  let R := fderiv ℝ (T_inv^[n]) (T^[n] x)
  let U := lyapunovUnstableComponent T T_inv x
  have hAxy : A (y - x) = T^[n] y - T^[n] x :=
    clmPrefixProduct_orbitSecantStep_apply T x y n
  have hRD : R ∘L D = ContinuousLinearMap.id ℝ EucPlane := by
    rw [show R = D.inverse by
      exact (fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x).symm]
    exact fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right n x
  have hrecover : y - x = R (A (y - x) - (A - D) (y - x)) := by
    have hrecoverD := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L (y - x)) hRD
    rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply] at hrecoverD
    calc
      y - x = R (D (y - x)) := hrecoverD.symm
      _ = R (A (y - x) - (A - D) (y - x)) := by
        congr 1
        rw [sub_apply]
        abel
  have hsegment : ‖U ∘L R‖ ≤
      C * Real.exp ((-lam1 + 6 * eta) * n) := by
    simpa [U, R] using
      norm_unstable_inverse_segment_le_of_rightFullEndpoint
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right hcarrier hcov
          hxcarrier hxRight
  calc
    ‖lyapunovUnstableComponent T T_inv x (y - x)‖ =
        ‖(U ∘L R) (A (y - x) - (A - D) (y - x))‖ := by
      apply congrArg norm
      calc
        lyapunovUnstableComponent T T_inv x (y - x) = U (y - x) := rfl
        _ = U (R (A (y - x) - (A - D) (y - x))) := congrArg U hrecover
        _ = (U ∘L R) (A (y - x) - (A - D) (y - x)) := rfl
    _ ≤ ‖U ∘L R‖ * ‖A (y - x) - (A - D) (y - x)‖ :=
      (U ∘L R).le_opNorm _
    _ ≤ ‖U ∘L R‖ *
        (‖A (y - x)‖ + ‖(A - D) (y - x)‖) := by
      gcongr
      exact norm_sub_le _ _
    _ ≤ (C * Real.exp ((-lam1 + 6 * eta) * n)) *
        (‖T^[n] y - T^[n] x‖ + e * ‖y - x‖) := by
      apply mul_le_mul hsegment
      · rw [hAxy]
        exact add_le_add le_rfl
          ((A - D).le_opNorm _ |>.trans
            (mul_le_mul_of_nonneg_right herror (norm_nonneg _)))
      · positivity
      · positivity

end Submission.Helpers
