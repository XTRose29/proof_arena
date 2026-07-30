import Submission.LyapunovSplitting
import Submission.LyapunovCovariance

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

theorem ae_stableProjection_structure
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
    (heta : 0 < eta) (hgap : 2 * eta < lam1 - lam2) :
    ∀ᵐ x ∂mu,
      stableProjection T x ∘L stableProjection T x = stableProjection T x ∧
      (stableProjection T x).adjoint = stableProjection T x ∧
      ‖stableProjection T x‖ = 1 ∧
      stableProjection T x ∘L
          planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap =
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          (ContinuousLinearMap.id ℝ EucPlane - stableProjection T x) := by
  have hinputs := ae_tendsto_fderiv_rates_eq_integrals_and_map_mem
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg hlam1 hlam2
  filter_upwards [hinputs] with x hx
  have hP :=
    (tendsto_stableAlgebraicApproxProjection_of_lyapunov_limits
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_compact hK_inv hx.1 heta hgap hx.2.1.1 hx.2.1.2).2
  exact ⟨stableProjection_idempotent_of_tendsto hP,
    stableProjection_adjoint_of_tendsto hP,
    norm_stableProjection_of_tendsto hP,
    stableProjection_comp_quarterTurn_of_tendsto hP⟩

lemma ae_and_six_of_ae
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {p₁ p₂ p₃ p₄ p₅ p₆ : M → Prop}
    (h₁ : ∀ᵐ x ∂mu, p₁ x) (h₂ : ∀ᵐ x ∂mu, p₂ x)
    (h₃ : ∀ᵐ x ∂mu, p₃ x) (h₄ : ∀ᵐ x ∂mu, p₄ x)
    (h₅ : ∀ᵐ x ∂mu, p₅ x) (h₆ : ∀ᵐ x ∂mu, p₆ x) :
    ∀ᵐ x ∂mu, p₁ x ∧ p₂ x ∧ p₃ x ∧ p₄ x ∧ p₅ x ∧ p₆ x :=
  h₁.and (h₂.and (h₃.and (h₄.and (h₅.and h₆))))

lemma ae_comp_of_ae
    {M : Type*} [MeasurableSpace M] {mu : Measure M}
    {T : M → M} (hT : Measure.QuasiMeasurePreserving T mu mu)
    {p : M → Prop} (hp : ∀ᵐ x ∂mu, p x) :
    ∀ᵐ x ∂mu, p (T x) :=
  hT.tendsto_ae hp

structure UnstableCovarianceData
    (T T_inv : EucPlane → EucPlane) (x : EucPlane) : Prop where
  targetInvertible :
    (stableProjection T (T x) + stableProjection T_inv (T x)).IsInvertible
  sourceTransverse : ∀ z : EucPlane,
    stableProjection T x z = z →
    stableProjection T_inv x z = z → z = 0
  stableTargetIdempotent :
    stableProjection T (T x) ∘L stableProjection T (T x) =
      stableProjection T (T x)
  unstableTargetIdempotent :
    stableProjection T_inv (T x) ∘L stableProjection T_inv (T x) =
      stableProjection T_inv (T x)
  stableBackward : ∀ z : EucPlane,
    stableProjection T x
        (fderiv ℝ T_inv (T x) (stableProjection T (T x) z)) =
      fderiv ℝ T_inv (T x) (stableProjection T (T x) z)
  unstableBackward : ∀ z : EucPlane,
    stableProjection T_inv (T_inv (T x))
        (fderiv ℝ T_inv (T x) (stableProjection T_inv (T x) z)) =
      fderiv ℝ T_inv (T x) (stableProjection T_inv (T x) z)

theorem ae_unstableProjection_structure
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
    (heta : 0 < eta) (hgap : 2 * eta < lam1 - lam2) :
    ∀ᵐ x ∂mu,
      stableProjection T_inv x ∘L stableProjection T_inv x =
          stableProjection T_inv x ∧
      (stableProjection T_inv x).adjoint = stableProjection T_inv x ∧
      ‖stableProjection T_inv x‖ = 1 ∧
      stableProjection T_inv x ∘L
          planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap =
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap ∘L
          (ContinuousLinearMap.id ℝ EucPlane - stableProjection T_inv x) := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have hErg_inv : Ergodic T_inv mu :=
    ergodic_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hErg
  have hK_inv_inv : T_inv '' K = K :=
    inverse_image_eq_of_image_eq hT_left hK_inv
  have hupper_inv :=
    integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        K hK_compact hK_inv mu hmu_supp hT hErg
  have hupper_swap :=
    integral_lyapunovUpperAt_inverse_eq_neg_integral_lyapunovLowerAt
      T_inv T hT_inv_smooth hT_smooth hT_right hT_left
        K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
  have hlam1_inv : -lam2 = ∫ x, lyapunovUpperAt T_inv x ∂mu := by
    calc
      -lam2 = -∫ x, lyapunovLowerAt T x ∂mu := congrArg Neg.neg hlam2
      _ = ∫ x, lyapunovUpperAt T_inv x ∂mu := hupper_inv.symm
  have hlam2_inv : -lam1 = ∫ x, lyapunovLowerAt T_inv x ∂mu := by
    rw [← hlam1] at hupper_swap
    linarith
  exact ae_stableProjection_structure
    (lam1 := -lam2) (lam2 := -lam1)
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left
      K hK_compact hK_inv_inv mu hmu_supp hT_inv hErg_inv
      hlam1_inv hlam2_inv heta (by linarith)

structure TargetSplittingData
    (T T_inv : EucPlane → EucPlane) (x : EucPlane) : Prop where
  invertible :
    (stableProjection T (T x) + stableProjection T_inv (T x)).IsInvertible
  stableIdempotent :
    stableProjection T (T x) ∘L stableProjection T (T x) =
      stableProjection T (T x)
  unstableIdempotent :
    stableProjection T_inv (T x) ∘L stableProjection T_inv (T x) =
      stableProjection T_inv (T x)
  transverse : ∀ z : EucPlane,
    stableProjection T (T x) z = z →
    stableProjection T_inv (T x) z = z → z = 0

theorem ae_targetSplittingData
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
    (hgap : 2 * eta < lam1 - lam2)
    (hstable_neg : lam2 + 5 * eta < 0)
    (hunstable_neg : -lam1 + 5 * eta < 0)
    (hrate : 8 * eta < hyperbolicRate lam1 lam2) :
    ∀ᵐ x ∂mu, TargetSplittingData T T_inv x := by
  have htransverse := ae_stableProjection_inverse_transverse
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hP := ae_stableProjection_structure
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta hgap
  have hU := ae_unstableProjection_structure
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta hgap
  filter_upwards [ae_comp_of_ae hT.quasiMeasurePreserving htransverse,
      ae_comp_of_ae hT.quasiMeasurePreserving hP,
      ae_comp_of_ae hT.quasiMeasurePreserving hU]
    with x hxtransverse hxP hxU
  refine ⟨projection_sum_isInvertible_of_transverse
    (stableProjection T (T x)) (stableProjection T_inv (T x))
      hxP.1 hxU.1 hxP.2.1 hxU.2.1 hxP.2.2.2 hxU.2.2.2
      hxtransverse, hxP.1, hxU.1, hxtransverse⟩

theorem ae_unstableProjection_fderiv_inverse_at_image_fixed
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
    (heta : 0 < eta) (hgap : 7 * eta < lam1 - lam2) :
    ∀ᵐ x ∂mu, ∀ z : EucPlane,
      stableProjection T_inv (T_inv (T x))
          (fderiv ℝ T_inv (T x) (stableProjection T_inv (T x) z)) =
        fderiv ℝ T_inv (T x) (stableProjection T_inv (T x) z) := by
  have hback := ae_unstableProjection_fderiv_inverse_fixed
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta hgap
  exact ae_comp_of_ae hT.quasiMeasurePreserving hback

theorem ae_unstableCovarianceData
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
    ∀ᵐ x ∂mu, UnstableCovarianceData T T_inv x := by
  have htarget := ae_targetSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have htransverse := ae_stableProjection_inverse_transverse
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hstable_back := ae_stableProjection_fderiv_inverse_at_image_fixed
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta hgap
  have hunstable_back := ae_unstableProjection_fderiv_inverse_at_image_fixed
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta (by linarith)
  filter_upwards [htarget, htransverse, hstable_back, hunstable_back]
    with x hxtarget hxtransverse hxstable_back hxunstable_back
  exact ⟨hxtarget.invertible, hxtransverse, hxtarget.stableIdempotent,
    hxtarget.unstableIdempotent, hxstable_back, hxunstable_back⟩

theorem ae_unstableProjection_fderiv_fixed
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
    ∀ᵐ x ∂mu, ∀ z : EucPlane,
      stableProjection T_inv x z = z →
        stableProjection T_inv (T x) (fderiv ℝ T x z) =
          fderiv ℝ T x z := by
  have hdata := ae_unstableCovarianceData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap hstable_neg
      hunstable_neg hrate
  filter_upwards [hdata] with x hx
  intro z hz
  let P₀ := stableProjection T x
  let U₀ := stableProjection T_inv x
  let P₁ := stableProjection T (T x)
  let U₁ := stableProjection T_inv (T x)
  let D := fderiv ℝ T x
  let D_inv := fderiv ℝ T_inv (T x)
  have hD_inv_eq : D_inv = D.inverse := by
    dsimp [D, D_inv]
    symm
    simpa [Function.iterate_one] using
      (fderiv_iterate_inverse T T_inv hT_smooth hT_inv_smooth
        hT_left hT_right 1 x)
  have hD_left : D_inv ∘L D = ContinuousLinearMap.id ℝ EucPlane := by
    rw [hD_inv_eq]
    dsimp [D]
    exact fderiv_iterate_inverse_comp
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right 1 x
  have hD_right : D ∘L D_inv = ContinuousLinearMap.id ℝ EucPlane := by
    rw [hD_inv_eq]
    dsimp [D]
    exact fderiv_iterate_comp_inverse
      T T_inv hT_smooth hT_inv_smooth hT_left hT_right 1 x
  have hstable_back' : ∀ w, P₁ w = w → P₀ (D_inv w) = D_inv w := by
    intro w hw
    dsimp [P₀, P₁, D_inv] at hw ⊢
    rw [← hw]
    exact hx.stableBackward w
  have hunstable_back' : ∀ w, U₁ w = w → U₀ (D_inv w) = D_inv w := by
    intro w hw
    dsimp [U₀, U₁, D_inv] at hw ⊢
    rw [← hw]
    simpa [hT_left x] using hx.unstableBackward w
  exact unstable_fixed_of_backward_covariance
    P₀ U₀ P₁ U₁ D D_inv hx.targetInvertible
      hx.stableTargetIdempotent hx.unstableTargetIdempotent hx.sourceTransverse
      hD_left hD_right hstable_back' hunstable_back' hz

end Submission.Helpers
