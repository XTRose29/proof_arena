import Submission.LyapunovBundleCovariance

namespace Submission.Helpers

open LeanEval.Dynamics Filter MeasureTheory Topology

noncomputable def lyapunovStableComponent
    (T T_inv : EucPlane → EucPlane) (x : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  stableComponent (stableProjection T x) (stableProjection T_inv x)

noncomputable def lyapunovUnstableComponent
    (T T_inv : EucPlane → EucPlane) (x : EucPlane) :
    EucPlane →L[ℝ] EucPlane :=
  unstableComponent (stableProjection T x) (stableProjection T_inv x)

lemma measurable_lyapunovStableComponent
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    Measurable (lyapunovStableComponent T T_inv) := by
  have hP := (stronglyMeasurable_stableProjection
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right).measurable
  have hU := (stronglyMeasurable_stableProjection
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left).measurable
  have hinv := measurable_planeCLM_inverse.comp (hP.add hU)
  change Measurable fun x => stableProjection T x ∘L
    (stableProjection T x + stableProjection T_inv x).inverse
  exact (ContinuousLinearMap.compL ℝ EucPlane EucPlane EucPlane).continuous₂
    |>.measurable.comp (hP.prodMk hinv)

lemma measurable_lyapunovUnstableComponent
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T) :
    Measurable (lyapunovUnstableComponent T T_inv) := by
  have hP := (stronglyMeasurable_stableProjection
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right).measurable
  have hU := (stronglyMeasurable_stableProjection
    T_inv T hT_inv_smooth hT_smooth hT_right hT_left).measurable
  have hinv := measurable_planeCLM_inverse.comp (hP.add hU)
  change Measurable fun x => stableProjection T_inv x ∘L
    (stableProjection T x + stableProjection T_inv x).inverse
  exact (ContinuousLinearMap.compL ℝ EucPlane EucPlane EucPlane).continuous₂
    |>.measurable.comp (hU.prodMk hinv)

structure SourceSplittingData
    (T T_inv : EucPlane → EucPlane) (x : EucPlane) : Prop where
  invertible :
    (stableProjection T x + stableProjection T_inv x).IsInvertible
  stableIdempotent :
    stableProjection T x ∘L stableProjection T x = stableProjection T x
  unstableIdempotent :
    stableProjection T_inv x ∘L stableProjection T_inv x =
      stableProjection T_inv x
  transverse : ∀ z : EucPlane,
    stableProjection T x z = z →
    stableProjection T_inv x z = z → z = 0

theorem ae_sourceSplittingData
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
    ∀ᵐ x ∂mu, SourceSplittingData T T_inv x := by
  have hT_inv : MeasurePreserving T_inv mu mu :=
    measurePreserving_inverse T T_inv hT_smooth hT_inv_smooth
      hT_left hT_right mu hT
  have htarget := ae_targetSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  have hsource := ae_comp_of_ae hT_inv.quasiMeasurePreserving htarget
  filter_upwards [hsource] with x hx
  exact
    ⟨by simpa only [hT_right x] using hx.invertible,
      by simpa only [hT_right x] using hx.stableIdempotent,
      by simpa only [hT_right x] using hx.unstableIdempotent,
      by simpa only [hT_right x] using hx.transverse⟩

lemma stableComponent_comp_of_covariance
    (P₀ U₀ P₁ U₁ D : EucPlane →L[ℝ] EucPlane)
    (hinv₀ : (P₀ + U₀).IsInvertible)
    (hinv₁ : (P₁ + U₁).IsInvertible)
    (hP₀ : P₀ ∘L P₀ = P₀) (hU₀ : U₀ ∘L U₀ = U₀)
    (hP₁ : P₁ ∘L P₁ = P₁) (hU₁ : U₁ ∘L U₁ = U₁)
    (htransverse₁ : ∀ z : EucPlane, P₁ z = z → U₁ z = z → z = 0)
    (hstable : ∀ z : EucPlane, P₀ z = z → P₁ (D z) = D z)
    (hunstable : ∀ z : EucPlane, U₀ z = z → U₁ (D z) = D z) :
    stableComponent P₁ U₁ ∘L D = D ∘L stableComponent P₀ U₀ := by
  apply ContinuousLinearMap.ext
  intro z
  have hdecomp : stableComponent P₀ U₀ z +
      unstableComponent P₀ U₀ z = z := by
    simpa only [add_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
        (stableComponent_add_unstableComponent P₀ U₀ hinv₀)
  have hstable₀ : P₀ (stableComponent P₀ U₀ z) =
      stableComponent P₀ U₀ z := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
        (stableComponent_fixed P₀ U₀ hP₀)
  have hunstable₀ : U₀ (unstableComponent P₀ U₀ z) =
      unstableComponent P₀ U₀ z := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
        (unstableComponent_fixed P₀ U₀ hU₀)
  have hstableImage := hstable _ hstable₀
  have hunstableImage := hunstable _ hunstable₀
  have hstablePart := (stableComponent_apply_of_fixed
    P₁ U₁ hinv₁ hP₁ hU₁ htransverse₁ hstableImage).1
  have hunstablePart := (unstableComponent_apply_of_fixed
    P₁ U₁ hinv₁ hP₁ hU₁ htransverse₁ hunstableImage).1
  simp only [ContinuousLinearMap.comp_apply]
  calc
    stableComponent P₁ U₁ (D z) =
        stableComponent P₁ U₁
          (D (stableComponent P₀ U₀ z + unstableComponent P₀ U₀ z)) :=
      congrArg (stableComponent P₁ U₁) (congrArg D hdecomp.symm)
    _ = stableComponent P₁ U₁ (D (stableComponent P₀ U₀ z)) +
        stableComponent P₁ U₁ (D (unstableComponent P₀ U₀ z)) := by
      rw [map_add, map_add]
    _ = D (stableComponent P₀ U₀ z) := by
      rw [hstablePart, hunstablePart, add_zero]

lemma unstableComponent_comp_of_covariance
    (P₀ U₀ P₁ U₁ D : EucPlane →L[ℝ] EucPlane)
    (hinv₀ : (P₀ + U₀).IsInvertible)
    (hinv₁ : (P₁ + U₁).IsInvertible)
    (hP₀ : P₀ ∘L P₀ = P₀) (hU₀ : U₀ ∘L U₀ = U₀)
    (hP₁ : P₁ ∘L P₁ = P₁) (hU₁ : U₁ ∘L U₁ = U₁)
    (htransverse₁ : ∀ z : EucPlane, P₁ z = z → U₁ z = z → z = 0)
    (hstable : ∀ z : EucPlane, P₀ z = z → P₁ (D z) = D z)
    (hunstable : ∀ z : EucPlane, U₀ z = z → U₁ (D z) = D z) :
    unstableComponent P₁ U₁ ∘L D =
      D ∘L unstableComponent P₀ U₀ := by
  apply ContinuousLinearMap.ext
  intro z
  have hdecomp : stableComponent P₀ U₀ z +
      unstableComponent P₀ U₀ z = z := by
    simpa only [add_apply, ContinuousLinearMap.id_apply]
      using congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
        (stableComponent_add_unstableComponent P₀ U₀ hinv₀)
  have hstable₀ : P₀ (stableComponent P₀ U₀ z) =
      stableComponent P₀ U₀ z := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
        (stableComponent_fixed P₀ U₀ hP₀)
  have hunstable₀ : U₀ (unstableComponent P₀ U₀ z) =
      unstableComponent P₀ U₀ z := by
    simpa only [ContinuousLinearMap.comp_apply] using
      congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
        (unstableComponent_fixed P₀ U₀ hU₀)
  have hstableImage := hstable _ hstable₀
  have hunstableImage := hunstable _ hunstable₀
  have hstablePart := (stableComponent_apply_of_fixed
    P₁ U₁ hinv₁ hP₁ hU₁ htransverse₁ hstableImage).2
  have hunstablePart := (unstableComponent_apply_of_fixed
    P₁ U₁ hinv₁ hP₁ hU₁ htransverse₁ hunstableImage).2
  simp only [ContinuousLinearMap.comp_apply]
  calc
    unstableComponent P₁ U₁ (D z) =
        unstableComponent P₁ U₁
          (D (stableComponent P₀ U₀ z + unstableComponent P₀ U₀ z)) :=
      congrArg (unstableComponent P₁ U₁) (congrArg D hdecomp.symm)
    _ = unstableComponent P₁ U₁ (D (stableComponent P₀ U₀ z)) +
        unstableComponent P₁ U₁ (D (unstableComponent P₀ U₀ z)) := by
      rw [map_add, map_add]
    _ = D (unstableComponent P₀ U₀ z) := by
      rw [hstablePart, hunstablePart, zero_add]

theorem ae_lyapunovComponents_fderiv_covariant
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
    ∀ᵐ x ∂mu,
      lyapunovStableComponent T T_inv (T x) ∘L fderiv ℝ T x =
          fderiv ℝ T x ∘L lyapunovStableComponent T T_inv x ∧
      lyapunovUnstableComponent T T_inv (T x) ∘L fderiv ℝ T x =
          fderiv ℝ T x ∘L lyapunovUnstableComponent T T_inv x := by
  have hsource := ae_sourceSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have htarget := ae_targetSplittingData
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta (by linarith)
      hstable_neg hunstable_neg hrate
  have hstable := ae_stableProjection_fderiv_fixed
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 heta (by linarith)
  have hunstable := ae_unstableProjection_fderiv_fixed
    T T_inv hT_smooth hT_inv_smooth hT_left hT_right
      K hK_compact hK_inv mu hmu_supp hT hErg
      hlam1 hlam2 hlam1_pos hlam2_neg heta hgap
      hstable_neg hunstable_neg hrate
  filter_upwards [hsource, htarget, hstable, hunstable]
    with x hxsource hxtarget hxstable hxunstable
  have hxstable' : ∀ z : EucPlane,
      stableProjection T x z = z →
        stableProjection T (T x) (fderiv ℝ T x z) = fderiv ℝ T x z := by
    intro z hz
    rw [← hz]
    exact hxstable z
  have hxunstable' : ∀ z : EucPlane,
      stableProjection T_inv x z = z →
        stableProjection T_inv (T x) (fderiv ℝ T x z) = fderiv ℝ T x z := by
    exact hxunstable
  exact ⟨stableComponent_comp_of_covariance
      (stableProjection T x) (stableProjection T_inv x)
      (stableProjection T (T x)) (stableProjection T_inv (T x))
      (fderiv ℝ T x) hxsource.invertible hxtarget.invertible
      hxsource.stableIdempotent hxsource.unstableIdempotent
      hxtarget.stableIdempotent hxtarget.unstableIdempotent
      hxtarget.transverse hxstable' hxunstable',
    unstableComponent_comp_of_covariance
      (stableProjection T x) (stableProjection T_inv x)
      (stableProjection T (T x)) (stableProjection T_inv (T x))
      (fderiv ℝ T x) hxsource.invertible hxtarget.invertible
      hxsource.stableIdempotent hxsource.unstableIdempotent
      hxtarget.stableIdempotent hxtarget.unstableIdempotent
      hxtarget.transverse hxstable' hxunstable'⟩

end Submission.Helpers
