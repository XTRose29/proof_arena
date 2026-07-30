import Submission.LyapunovTransversality

namespace Submission.Helpers

open LeanEval.Dynamics

lemma inner_projection_apply_self_eq_norm_sq
    (P : EucPlane →L[ℝ] EucPlane)
    (hidempotent : P ∘L P = P) (hadjoint : P.adjoint = P)
    (z : EucPlane) :
    inner ℝ (P z) z = ‖P z‖ ^ 2 := by
  have hnorm := P.apply_norm_sq_eq_inner_adjoint_left z
  rw [hadjoint, hidempotent] at hnorm
  simpa using hnorm.symm

lemma projection_sum_injective_of_transverse
    (P U : EucPlane →L[ℝ] EucPlane)
    (hP_idempotent : P ∘L P = P) (hU_idempotent : U ∘L U = U)
    (hP_adjoint : P.adjoint = P) (hU_adjoint : U.adjoint = U)
    (hP_quarter : P ∘L
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap =
      planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.id ℝ EucPlane - P))
    (hU_quarter : U ∘L
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap =
      planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.id ℝ EucPlane - U))
    (htransverse : ∀ z : EucPlane, P z = z → U z = z → z = 0) :
    Function.Injective (P + U) := by
  intro z w hzw
  suffices z - w = 0 by exact sub_eq_zero.mp this
  let v := z - w
  have hv : (P + U) v = 0 := by
    dsimp [v]
    rw [map_sub, hzw, sub_self]
  have hsum : ‖P v‖ ^ 2 + ‖U v‖ ^ 2 = 0 := by
    calc
      ‖P v‖ ^ 2 + ‖U v‖ ^ 2 =
          inner ℝ (P v) v + inner ℝ (U v) v := by
        rw [inner_projection_apply_self_eq_norm_sq P hP_idempotent
          hP_adjoint, inner_projection_apply_self_eq_norm_sq U
            hU_idempotent hU_adjoint]
      _ = inner ℝ ((P + U) v) v := by simp [inner_add_left]
      _ = 0 := by rw [hv]; simp
  have hPnorm : ‖P v‖ = 0 := by
    nlinarith [sq_nonneg ‖P v‖, sq_nonneg ‖U v‖,
      norm_nonneg (P v), norm_nonneg (U v)]
  have hUnorm : ‖U v‖ = 0 := by
    nlinarith [sq_nonneg ‖P v‖, sq_nonneg ‖U v‖,
      norm_nonneg (P v), norm_nonneg (U v)]
  have hPv : P v = 0 := norm_eq_zero.mp hPnorm
  have hUv : U v = 0 := norm_eq_zero.mp hUnorm
  let J := planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap
  have hPJ : P (J v) = J v := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L v) hP_quarter
    simpa [J, hPv] using h
  have hUJ : U (J v) = J v := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L v) hU_quarter
    simpa [J, hUv] using h
  have hJv : J v = 0 := htransverse (J v) hPJ hUJ
  change v = 0
  apply planeQuarterTurn.injective
  simpa [J] using hJv

lemma projection_sum_isInvertible_of_transverse
    (P U : EucPlane →L[ℝ] EucPlane)
    (hP_idempotent : P ∘L P = P) (hU_idempotent : U ∘L U = U)
    (hP_adjoint : P.adjoint = P) (hU_adjoint : U.adjoint = U)
    (hP_quarter : P ∘L
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap =
      planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.id ℝ EucPlane - P))
    (hU_quarter : U ∘L
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap =
      planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap ∘L
        (ContinuousLinearMap.id ℝ EucPlane - U))
    (htransverse : ∀ z : EucPlane, P z = z → U z = z → z = 0) :
    (P + U).IsInvertible := by
  have hinj : Function.Injective (P + U) :=
    projection_sum_injective_of_transverse P U hP_idempotent hU_idempotent
      hP_adjoint hU_adjoint hP_quarter hU_quarter htransverse
  let e := ContinuousLinearEquiv.ofBijective (P + U)
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr
      (LinearMap.surjective_of_injective hinj))
  exact ⟨e, rfl⟩

lemma planeCLM_isInvertible_of_det_ne_zero
    (A : EucPlane →L[ℝ] EucPlane) (hdet : A.det ≠ 0) :
    A.IsInvertible := by
  have hinj : Function.Injective A := by
    apply LinearMap.ker_eq_bot.mp
    by_contra hker
    exact hdet (LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hker)
  let e := ContinuousLinearEquiv.ofBijective A
    (LinearMap.ker_eq_bot.mpr hinj)
    (LinearMap.range_eq_top.mpr
      (LinearMap.surjective_of_injective hinj))
  exact ⟨e, rfl⟩

lemma planeCLM_inverse_eq_inv_smul_adjugate
    (A : EucPlane →L[ℝ] EucPlane) :
    A.inverse = A.det⁻¹ • planeAdjugate A := by
  by_cases hA : A.IsInvertible
  · have hdet : A.det ≠ 0 := by
      intro hzero
      have hker : A.toLinearMap.ker ≠ ⊥ :=
        LinearMap.det_eq_zero_iff_ker_ne_bot.mp hzero
      exact hker (LinearMap.ker_eq_bot.mpr hA.injective)
    rw [planeAdjugate_eq_det_smul_inverse A A.inverse
      hA.inverse_comp_self]
    simp [smul_smul, hdet]
  · have hdet : A.det = 0 := by
      by_contra hdet
      exact hA (planeCLM_isInvertible_of_det_ne_zero A hdet)
    rw [A.inverse_of_not_isInvertible hA, hdet]
    rw [inv_zero]
    module

lemma continuous_planeAdjugate :
    Continuous (planeAdjugate :
      (EucPlane →L[ℝ] EucPlane) → EucPlane →L[ℝ] EucPlane) := by
  change Continuous fun A : EucPlane →L[ℝ] EucPlane =>
    planeQuarterTurn.symm.toContinuousLinearEquiv.toContinuousLinearMap ∘L
      (A.adjoint ∘L
        planeQuarterTurn.toContinuousLinearEquiv.toContinuousLinearMap)
  exact continuous_const.clm_comp
    (ContinuousLinearMap.adjoint.continuous.clm_comp continuous_const)

lemma measurable_planeCLM_inverse :
    Measurable (ContinuousLinearMap.inverse :
      (EucPlane →L[ℝ] EucPlane) → EucPlane →L[ℝ] EucPlane) := by
  have hdet : Measurable fun A : EucPlane →L[ℝ] EucPlane => A.det⁻¹ :=
    ContinuousLinearMap.continuous_det.measurable.inv
  have hadj : Measurable (planeAdjugate :
      (EucPlane →L[ℝ] EucPlane) → EucPlane →L[ℝ] EucPlane) :=
    continuous_planeAdjugate.measurable
  convert hdet.smul hadj using 1
  funext A
  exact planeCLM_inverse_eq_inv_smul_adjugate A

noncomputable def stableComponent
    (P U : EucPlane →L[ℝ] EucPlane) : EucPlane →L[ℝ] EucPlane :=
  P ∘L (P + U).inverse

noncomputable def unstableComponent
    (P U : EucPlane →L[ℝ] EucPlane) : EucPlane →L[ℝ] EucPlane :=
  U ∘L (P + U).inverse

lemma stableComponent_add_unstableComponent
    (P U : EucPlane →L[ℝ] EucPlane)
    (hinv : (P + U).IsInvertible) :
    stableComponent P U + unstableComponent P U =
      ContinuousLinearMap.id ℝ EucPlane := by
  rw [stableComponent, unstableComponent, ← ContinuousLinearMap.add_comp]
  exact hinv.self_comp_inverse

lemma stableComponent_fixed
    (P U : EucPlane →L[ℝ] EucPlane)
    (hP : P ∘L P = P) :
    P ∘L stableComponent P U = stableComponent P U := by
  rw [stableComponent, ← ContinuousLinearMap.comp_assoc, hP]

lemma unstableComponent_fixed
    (P U : EucPlane →L[ℝ] EucPlane)
    (hU : U ∘L U = U) :
    U ∘L unstableComponent P U = unstableComponent P U := by
  rw [unstableComponent, ← ContinuousLinearMap.comp_assoc, hU]

lemma norm_stableComponent_le
    (P U : EucPlane →L[ℝ] EucPlane) (hP : ‖P‖ = 1) :
    ‖stableComponent P U‖ ≤ ‖(P + U).inverse‖ := by
  calc
    ‖stableComponent P U‖ ≤ ‖P‖ * ‖(P + U).inverse‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖(P + U).inverse‖ := by rw [hP, one_mul]

lemma norm_unstableComponent_le
    (P U : EucPlane →L[ℝ] EucPlane) (hU : ‖U‖ = 1) :
    ‖unstableComponent P U‖ ≤ ‖(P + U).inverse‖ := by
  calc
    ‖unstableComponent P U‖ ≤ ‖U‖ * ‖(P + U).inverse‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ = ‖(P + U).inverse‖ := by rw [hU, one_mul]

lemma stableComponent_apply_of_fixed
    (P U : EucPlane →L[ℝ] EucPlane)
    (hinv : (P + U).IsInvertible)
    (hP : P ∘L P = P) (hU : U ∘L U = U)
    (htransverse : ∀ z : EucPlane, P z = z → U z = z → z = 0)
    {z : EucPlane} (hz : P z = z) :
    stableComponent P U z = z ∧ unstableComponent P U z = 0 := by
  have hdecomp : stableComponent P U z + unstableComponent P U z = z := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
      (stableComponent_add_unstableComponent P U hinv)
    simpa using h
  have hstable_fixed : P (stableComponent P U z) = stableComponent P U z := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
      (stableComponent_fixed P U hP)
    simpa using h
  have hunstable_fixed : U (unstableComponent P U z) =
      unstableComponent P U z := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
      (unstableComponent_fixed P U hU)
    simpa using h
  have hunstable_stable : P (unstableComponent P U z) =
      unstableComponent P U z := by
    have heq : unstableComponent P U z = z - stableComponent P U z := by
      calc
        unstableComponent P U z =
            (stableComponent P U z + unstableComponent P U z) -
              stableComponent P U z := by abel
        _ = z - stableComponent P U z := by rw [hdecomp]
    rw [heq, map_sub, hz, hstable_fixed]
  have hunstable_zero := htransverse (unstableComponent P U z)
    hunstable_stable hunstable_fixed
  constructor
  · simpa [hunstable_zero] using hdecomp
  · exact hunstable_zero

lemma unstableComponent_apply_of_fixed
    (P U : EucPlane →L[ℝ] EucPlane)
    (hinv : (P + U).IsInvertible)
    (hP : P ∘L P = P) (hU : U ∘L U = U)
    (htransverse : ∀ z : EucPlane, P z = z → U z = z → z = 0)
    {z : EucPlane} (hz : U z = z) :
    stableComponent P U z = 0 ∧ unstableComponent P U z = z := by
  have hdecomp : stableComponent P U z + unstableComponent P U z = z := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
      (stableComponent_add_unstableComponent P U hinv)
    simpa using h
  have hstable_fixed : P (stableComponent P U z) = stableComponent P U z := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
      (stableComponent_fixed P U hP)
    simpa using h
  have hunstable_fixed : U (unstableComponent P U z) =
      unstableComponent P U z := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z)
      (unstableComponent_fixed P U hU)
    simpa using h
  have hstable_unstable : U (stableComponent P U z) =
      stableComponent P U z := by
    have heq : stableComponent P U z = z - unstableComponent P U z := by
      calc
        stableComponent P U z =
            (stableComponent P U z + unstableComponent P U z) -
              unstableComponent P U z := by abel
        _ = z - unstableComponent P U z := by rw [hdecomp]
    rw [heq, map_sub, hz, hunstable_fixed]
  have hstable_zero := htransverse (stableComponent P U z)
    hstable_fixed hstable_unstable
  constructor
  · exact hstable_zero
  · simpa [hstable_zero] using hdecomp

lemma unstable_fixed_of_backward_covariance
    (P₀ U₀ P₁ U₁ D D_inv : EucPlane →L[ℝ] EucPlane)
    (hinv₁ : (P₁ + U₁).IsInvertible)
    (hP₁ : P₁ ∘L P₁ = P₁) (hU₁ : U₁ ∘L U₁ = U₁)
    (htransverse₀ : ∀ z : EucPlane, P₀ z = z → U₀ z = z → z = 0)
    (hD_left : D_inv ∘L D = ContinuousLinearMap.id ℝ EucPlane)
    (hD_right : D ∘L D_inv = ContinuousLinearMap.id ℝ EucPlane)
    (hstable_back : ∀ z, P₁ z = z → P₀ (D_inv z) = D_inv z)
    (hunstable_back : ∀ z, U₁ z = z → U₀ (D_inv z) = D_inv z)
    {z : EucPlane} (hz : U₀ z = z) :
    U₁ (D z) = D z := by
  let w := D z
  let s := stableComponent P₁ U₁ w
  let u := unstableComponent P₁ U₁ w
  have hdecomp : s + u = w := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L w)
      (stableComponent_add_unstableComponent P₁ U₁ hinv₁)
    simpa [s, u] using h
  have hs_fixed : P₁ s = s := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L w)
      (stableComponent_fixed P₁ U₁ hP₁)
    simpa [s] using h
  have hu_fixed : U₁ u = u := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L w)
      (unstableComponent_fixed P₁ U₁ hU₁)
    simpa [u] using h
  have hDs_stable : P₀ (D_inv s) = D_inv s := hstable_back s hs_fixed
  have hDu_unstable : U₀ (D_inv u) = D_inv u := hunstable_back u hu_fixed
  have hsum_pullback : D_inv s + D_inv u = z := by
    calc
      D_inv s + D_inv u = D_inv (s + u) := (map_add D_inv s u).symm
      _ = D_inv w := by rw [hdecomp]
      _ = z := by
        dsimp [w]
        exact congrArg (fun L : EucPlane →L[ℝ] EucPlane => L z) hD_left
  have hDs_unstable : U₀ (D_inv s) = D_inv s := by
    have heq : D_inv s = z - D_inv u := by
      calc
        D_inv s = (D_inv s + D_inv u) - D_inv u := by abel
        _ = z - D_inv u := by rw [hsum_pullback]
    rw [heq, map_sub, hz, hDu_unstable]
  have hDs_zero : D_inv s = 0 :=
    htransverse₀ (D_inv s) hDs_stable hDs_unstable
  have hs_zero : s = 0 := by
    have h := congrArg (fun L : EucPlane →L[ℝ] EucPlane => L s) hD_right
    simpa [hDs_zero] using h.symm
  have hwu : w = u := by
    simpa [hs_zero] using hdecomp.symm
  change U₁ w = w
  rw [hwu]
  exact hu_fixed

end Submission.Helpers
