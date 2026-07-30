import Submission.LyapunovComponentOrbit
import Submission.LyapunovComponentContraction
import Submission.PlaneProjectionSplitting
import Mathlib.LinearAlgebra.Matrix.Adjugate

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory

lemma planeAdjugate_comp_map
    (A B : EucPlane →L[ℝ] EucPlane) :
    planeAdjugate (A ∘L B) = planeAdjugate B ∘L planeAdjugate A := by
  apply ContinuousLinearMap.ext
  intro x
  simp only [planeAdjugate, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.comp_apply]
  simp

lemma toMatrix_planeAdjugate (A : EucPlane →L[ℝ] EucPlane) :
    (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis)
        (planeAdjugate A).toLinearMap =
      Matrix.adjugate
        ((LinearMap.toMatrix
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
          (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis) A.toLinearMap) := by
  classical
  rw [show (planeAdjugate A).toLinearMap =
      planeQuarterTurn.symm.toLinearEquiv.toLinearMap ∘ₗ
        (A.adjoint.toLinearMap ∘ₗ
          planeQuarterTurn.toLinearEquiv.toLinearMap) by rfl]
  rw [LinearMap.toMatrix_comp
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [LinearMap.toMatrix_comp
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
    (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis]
  rw [toMatrix_planeQuarterTurn_symm, toMatrix_planeQuarterTurn]
  rw [← ContinuousLinearMap.adjoint_toLinearMap A]
  rw [LinearMap.toMatrix_adjoint, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two]

lemma matrix_adjugate_eq_complement
    (S U : Matrix (Fin 2) (Fin 2) ℝ)
    (hsum : S + U = 1) (hSdet : S.det = 0) (hUdet : U.det = 0) :
    S.adjugate = U := by
  have hU : U = 1 - S := by
    rw [← hsum]
    module
  subst U
  rw [Matrix.det_fin_two] at hSdet hUdet
  rw [Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp at hSdet hUdet ⊢ <;> nlinarith

lemma planeAdjugate_eq_complement
    (S U : EucPlane →L[ℝ] EucPlane)
    (hsum : S + U = ContinuousLinearMap.id ℝ EucPlane)
    (hSdet : S.det = 0) (hUdet : U.det = 0) :
    planeAdjugate S = U := by
  apply ContinuousLinearMap.ext
  intro x
  have hlin : (planeAdjugate S).toLinearMap = U.toLinearMap := by
    apply (LinearMap.toMatrix
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis
      (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis).injective
    rw [toMatrix_planeAdjugate]
    apply matrix_adjugate_eq_complement
    · ext i j
      have hpoint := congrArg
        (fun L : EucPlane →L[ℝ] EucPlane =>
          L (EuclideanSpace.basisFun (Fin 2) ℝ j)) hsum
      have hcoord := congrArg
        (fun y => (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.repr y i)
        hpoint
      simpa [LinearMap.toMatrix_apply, Matrix.one_apply] using hcoord
    · simpa using hSdet
    · simpa using hUdet
  exact LinearMap.congr_fun hlin x

lemma det_stableComponent_eq_zero
    (P U : EucPlane →L[ℝ] EucPlane)
    (hinv : (P + U).IsInvertible)
    (hP : P ∘L P = P) (hU : U ∘L U = U)
    (htransverse : ∀ z : EucPlane, P z = z → U z = z → z = 0)
    (hUnorm : ‖U‖ = 1) :
    (stableComponent P U).det = 0 := by
  have hUne : U ≠ 0 := by
    intro hUzero
    rw [hUzero, norm_zero] at hUnorm
    norm_num at hUnorm
  obtain ⟨v, hv⟩ : ∃ v : EucPlane, U v ≠ 0 := by
    by_contra h
    push Not at h
    apply hUne
    apply ContinuousLinearMap.ext
    intro w
    exact h w
  let z := U v
  have hzfixed : U z = z := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L v) hU
    simpa [z] using h
  have hzstable : stableComponent P U z = 0 :=
    (unstableComponent_apply_of_fixed P U hinv hP hU htransverse
      hzfixed).1
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  intro hker
  have hzmem : z ∈ (stableComponent P U).toLinearMap.ker := by
    simpa [LinearMap.mem_ker] using hzstable
  have hzbot : z ∈ (⊥ : Submodule ℝ EucPlane) := hker ▸ hzmem
  exact hv (by simpa [z] using hzbot)

lemma det_unstableComponent_eq_zero
    (P U : EucPlane →L[ℝ] EucPlane)
    (hinv : (P + U).IsInvertible)
    (hP : P ∘L P = P) (hU : U ∘L U = U)
    (htransverse : ∀ z : EucPlane, P z = z → U z = z → z = 0)
    (hPnorm : ‖P‖ = 1) :
    (unstableComponent P U).det = 0 := by
  have hPne : P ≠ 0 := by
    intro hPzero
    rw [hPzero, norm_zero] at hPnorm
    norm_num at hPnorm
  obtain ⟨v, hv⟩ : ∃ v : EucPlane, P v ≠ 0 := by
    by_contra h
    push Not at h
    apply hPne
    apply ContinuousLinearMap.ext
    intro w
    exact h w
  let z := P v
  have hzfixed : P z = z := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L v) hP
    simpa [z] using h
  have hzunstable : unstableComponent P U z = 0 :=
    (stableComponent_apply_of_fixed P U hinv hP hU htransverse
      hzfixed).2
  apply LinearMap.det_eq_zero_iff_ker_ne_bot.mpr
  intro hker
  have hzmem : z ∈ (unstableComponent P U).toLinearMap.ker := by
    simpa [LinearMap.mem_ker] using hzunstable
  have hzbot : z ∈ (⊥ : Submodule ℝ EucPlane) := hker ▸ hzmem
  exact hv (by simpa [z] using hzbot)

theorem ae_lyapunovComponents_det_zero
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu,
      (lyapunovStableComponent T T_inv x).det = 0 ∧
      (lyapunovUnstableComponent T T_inv x).det = 0 := by
  have hsource := ae_sourceSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hstable := ae_stableProjection_structure
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta (by linarith)
  have hunstable := ae_unstableProjection_structure
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta (by linarith)
  filter_upwards [hsource, hstable, hunstable]
    with x hxsource hxstable hxunstable
  unfold lyapunovStableComponent lyapunovUnstableComponent
  exact ⟨det_stableComponent_eq_zero
      (stableProjection T x) (stableProjection T_inv x)
      hxsource.invertible hxsource.stableIdempotent
      hxsource.unstableIdempotent hxsource.transverse hxunstable.2.2.1,
    det_unstableComponent_eq_zero
      (stableProjection T x) (stableProjection T_inv x)
      hxsource.invertible hxsource.stableIdempotent
      hxsource.unstableIdempotent hxsource.transverse hxstable.2.2.1⟩

lemma abs_det_mul_norm_inverse_comp_complement
    (D S₀ S₁ U₁ : EucPlane →L[ℝ] EucPlane)
    (hD : D.IsInvertible)
    (hsum₁ : S₁ + U₁ = ContinuousLinearMap.id ℝ EucPlane)
    (hS₁det : S₁.det = 0) (hU₁det : U₁.det = 0)
    (hcov : S₁ ∘L D = D ∘L S₀) :
    |D.det| * ‖D.inverse ∘L U₁‖ = ‖D ∘L S₀‖ := by
  have hleft : D.inverse ∘L D = ContinuousLinearMap.id ℝ EucPlane :=
    hD.inverse_comp_self
  have hadjD : planeAdjugate D = D.det • D.inverse :=
    planeAdjugate_eq_det_smul_inverse D D.inverse hleft
  have hadjS₁ : planeAdjugate S₁ = U₁ :=
    planeAdjugate_eq_complement S₁ U₁ hsum₁ hS₁det hU₁det
  have hmaps : planeAdjugate D ∘L U₁ =
      planeAdjugate (D ∘L S₀) := by
    calc
      planeAdjugate D ∘L U₁ =
          planeAdjugate D ∘L planeAdjugate S₁ := by rw [hadjS₁]
      _ = planeAdjugate (S₁ ∘L D) := by
        rw [planeAdjugate_comp_map]
      _ = planeAdjugate (D ∘L S₀) := by rw [hcov]
  calc
    |D.det| * ‖D.inverse ∘L U₁‖ =
        ‖(D.det • D.inverse) ∘L U₁‖ := by
      rw [ContinuousLinearMap.smul_comp, norm_smul, Real.norm_eq_abs]
    _ = ‖planeAdjugate D ∘L U₁‖ := by rw [hadjD]
    _ = ‖planeAdjugate (D ∘L S₀)‖ := by rw [hmaps]
    _ = ‖D ∘L S₀‖ := norm_planeAdjugate _

theorem ae_all_inverse_component_norm_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ n : ℕ,
      let D := fderiv ℝ (T^[n]) x
      |D.det| *
          ‖D.inverse ∘L lyapunovUnstableComponent T T_inv (T^[n] x)‖ =
          ‖D ∘L lyapunovStableComponent T T_inv x‖ ∧
        |D.det| *
          ‖D.inverse ∘L lyapunovStableComponent T T_inv (T^[n] x)‖ =
          ‖D ∘L lyapunovUnstableComponent T T_inv x‖ := by
  have hsource := ae_sourceSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hsource_all := ae_all_iterates_of_ae
    hT.quasiMeasurePreserving hsource
  have hdet := ae_lyapunovComponents_det_zero
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta
      hstable_neg hunstable_neg hrate
  have hdet_all := ae_all_iterates_of_ae
    hT.quasiMeasurePreserving hdet
  have hcov := ae_all_lyapunovComponents_fderiv_iterate_covariant
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  filter_upwards [hsource_all, hdet_all, hcov]
    with x hxsource hxdet hxcov
  intro n
  let D := fderiv ℝ (T^[n]) x
  have hD : D.IsInvertible := by
    apply ContinuousLinearMap.IsInvertible.of_inverse (g := D.inverse)
    · exact fderiv_iterate_comp_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x
    · exact fderiv_iterate_inverse_comp T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right n x
  have hsum := lyapunovComponents_add T T_inv (hxsource n)
  exact ⟨abs_det_mul_norm_inverse_comp_complement
      D (lyapunovStableComponent T T_inv x)
      (lyapunovStableComponent T T_inv (T^[n] x))
      (lyapunovUnstableComponent T T_inv (T^[n] x))
      hD hsum (hxdet n).1 (hxdet n).2 (hxcov n).1,
    abs_det_mul_norm_inverse_comp_complement
      D (lyapunovUnstableComponent T T_inv x)
      (lyapunovUnstableComponent T T_inv (T^[n] x))
      (lyapunovStableComponent T T_inv (T^[n] x))
      hD (by simpa [add_comm] using hsum)
      (hxdet n).2 (hxdet n).1 (hxcov n).2⟩

theorem ae_eventually_norm_fderiv_inverse_comp_futureUnstable_le_exp
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (K : Set EucPlane) (hK_compact : IsCompact K) (hK_inv : T '' K = K)
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    (hmu_supp : mu Kᶜ = 0)
    (hT : MeasurePreserving T mu mu) (hErg : Ergodic T mu)
    {lam1 lam2 eta : ℝ}
    (hlam1 : lam1 = ∫ x, lyapunovUpperAt T x ∂mu)
    (hlam2 : lam2 = ∫ x, lyapunovLowerAt T x ∂mu)
    (hlam1_pos : 0 < lam1) (hlam2_neg : lam2 < 0)
    (heta : 0 < eta)
    (hgap : 8 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, ∀ᶠ n : ℕ in atTop,
      ‖(fderiv ℝ (T^[n]) x).inverse ∘L
          lyapunovUnstableComponent T T_inv (T^[n] x)‖ ≤
        Real.exp ((-lam1 + 7 * eta) * n) := by
  have heq := ae_all_inverse_component_norm_eq
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hstable :=
    ae_eventually_norm_fderiv_comp_lyapunovStableComponent_le_exp
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
        hlam1 hlam2 hlam1_pos hlam2_neg heta
        hstable_neg hunstable_neg hrate
  have hjacobian := ae_tendsto_logJacobianIterate_div_integral
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      hK_compact mu hmu_supp hT hErg
  have hJ : (∫ x, logJacobian T x ∂mu) = lam1 + lam2 := by
    rw [integral_logJacobian_eq_integral_lyapunovUpper_add_lower
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg]
    rw [← hlam1, ← hlam2]
  filter_upwards [heq, hstable, hjacobian]
    with x hxeq hxstable hxjacobian
  have hdet := eventually_exp_sub_le_of_tendsto_log_div
    (a := fun n => |(fderiv ℝ (T^[n]) x).det|)
    (fun n : ℕ => n) tendsto_id
      (fun n => abs_pos.mpr (det_fderiv_iterate_ne_zero
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right n x))
      heta (by simpa [logJacobianIterate, hJ] using hxjacobian)
  filter_upwards [hxstable, hdet] with n hstable_n hdet_n
  let A := fderiv ℝ (T^[n]) x
  let U := lyapunovUnstableComponent T T_inv (T^[n] x)
  have hmul : Real.exp ((lam1 + lam2 - eta) * n) *
      ‖A.inverse ∘L U‖ ≤ Real.exp ((lam2 + 6 * eta) * n) := by
    calc
      Real.exp ((lam1 + lam2 - eta) * n) * ‖A.inverse ∘L U‖ ≤
          |A.det| * ‖A.inverse ∘L U‖ :=
        mul_le_mul_of_nonneg_right hdet_n (norm_nonneg _)
      _ = ‖A ∘L lyapunovStableComponent T T_inv x‖ :=
        (hxeq n).1
      _ ≤ Real.exp ((lam2 + 6 * eta) * n) := hstable_n
  have hdiv : ‖A.inverse ∘L U‖ ≤
      Real.exp ((lam2 + 6 * eta) * n) /
        Real.exp ((lam1 + lam2 - eta) * n) := by
    exact (le_div_iff₀ (Real.exp_pos _)).2 (by simpa [mul_comm] using hmul)
  calc
    ‖A.inverse ∘L U‖ ≤
        Real.exp ((lam2 + 6 * eta) * n) /
          Real.exp ((lam1 + lam2 - eta) * n) := hdiv
    _ = Real.exp ((-lam1 + 7 * eta) * n) := by
      rw [← Real.exp_sub]
      congr 1
      ring

end Submission.Helpers
