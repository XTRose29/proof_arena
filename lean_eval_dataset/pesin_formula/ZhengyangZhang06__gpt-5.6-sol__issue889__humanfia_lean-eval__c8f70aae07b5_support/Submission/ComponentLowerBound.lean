import Submission.ComponentAdjugate

namespace Submission.Helpers

open LeanEval.Dynamics

lemma one_le_norm_stableComponent
    (P U : EucPlane →L[ℝ] EucPlane)
    (hinv : (P + U).IsInvertible)
    (hP : P ∘L P = P) (hU : U ∘L U = U)
    (htransverse : ∀ z : EucPlane, P z = z → U z = z → z = 0)
    (hPnorm : ‖P‖ = 1) :
    1 ≤ ‖stableComponent P U‖ := by
  have hPne : P ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hPnorm
    norm_num at hPnorm
  obtain ⟨v, hv⟩ : ∃ v : EucPlane, P v ≠ 0 := by
    by_contra h
    push Not at h
    apply hPne
    apply ContinuousLinearMap.ext
    exact h
  let z := P v
  have hzfixed : P z = z := by
    have h := congrArg (fun A : EucPlane →L[ℝ] EucPlane => A v) hP
    simpa [z] using h
  have hzstable : stableComponent P U z = z :=
    (stableComponent_apply_of_fixed P U hinv hP hU htransverse hzfixed).1
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa [z] using hv)
  have hop := (stableComponent P U).le_opNorm z
  rw [hzstable] at hop
  exact (le_mul_iff_one_le_left hzpos).mp hop

lemma one_le_norm_unstableComponent
    (P U : EucPlane →L[ℝ] EucPlane)
    (hinv : (P + U).IsInvertible)
    (hP : P ∘L P = P) (hU : U ∘L U = U)
    (htransverse : ∀ z : EucPlane, P z = z → U z = z → z = 0)
    (hUnorm : ‖U‖ = 1) :
    1 ≤ ‖unstableComponent P U‖ := by
  have hUne : U ≠ 0 := by
    intro hzero
    rw [hzero, norm_zero] at hUnorm
    norm_num at hUnorm
  obtain ⟨v, hv⟩ : ∃ v : EucPlane, U v ≠ 0 := by
    by_contra h
    push Not at h
    apply hUne
    apply ContinuousLinearMap.ext
    exact h
  let z := U v
  have hzfixed : U z = z := by
    have h := congrArg (fun A : EucPlane →L[ℝ] EucPlane => A v) hU
    simpa [z] using h
  have hzunstable : unstableComponent P U z = z :=
    (unstableComponent_apply_of_fixed P U hinv hP hU htransverse hzfixed).2
  have hzpos : 0 < ‖z‖ := norm_pos_iff.mpr (by simpa [z] using hv)
  have hop := (unstableComponent P U).le_opNorm z
  rw [hzunstable] at hop
  exact (le_mul_iff_one_le_left hzpos).mp hop

lemma one_le_norm_mul_norm_inverse_comp
    (D U : EucPlane →L[ℝ] EucPlane)
    (hD : D.IsInvertible) (hU : 1 ≤ ‖U‖) :
    1 ≤ ‖D‖ * ‖D.inverse ∘L U‖ := by
  calc
    1 ≤ ‖U‖ := hU
    _ = ‖(D ∘L D.inverse) ∘L U‖ := by rw [hD.self_comp_inverse]; simp
    _ = ‖D ∘L (D.inverse ∘L U)‖ := by
      rw [ContinuousLinearMap.comp_assoc]
    _ ≤ ‖D‖ * ‖D.inverse ∘L U‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _

lemma exp_sub_le_norm_of_adjugate_eq
    (D U : EucPlane →L[ℝ] EucPlane)
    (hD : D.IsInvertible) (hU : 1 ≤ ‖U‖)
    {target detRate normRate : ℝ}
    (heq : |D.det| * ‖D.inverse ∘L U‖ = target)
    (hdet : Real.exp detRate ≤ |D.det|)
    (hnorm : ‖D‖ ≤ Real.exp normRate) :
    Real.exp (detRate - normRate) ≤ target := by
  let x := ‖D.inverse ∘L U‖
  have hx : 0 ≤ x := norm_nonneg _
  have hproduct : 1 ≤ Real.exp normRate * x := by
    calc
      1 ≤ ‖D‖ * x := one_le_norm_mul_norm_inverse_comp D U hD hU
      _ ≤ Real.exp normRate * x :=
        mul_le_mul_of_nonneg_right hnorm hx
  have hratio : 1 / Real.exp normRate ≤ x := by
    apply (div_le_iff₀ (Real.exp_pos normRate)).2
    simpa [mul_comm] using hproduct
  calc
    Real.exp (detRate - normRate) =
        Real.exp detRate * (1 / Real.exp normRate) := by
      rw [Real.exp_sub]
      ring
    _ ≤ |D.det| * x :=
      mul_le_mul hdet hratio (by positivity) (abs_nonneg _)
    _ = target := heq

lemma exp_sub_le_norm_component_of_adjugate
    (D S₀ S₁ U₁ : EucPlane →L[ℝ] EucPlane)
    (hD : D.IsInvertible)
    (hsum₁ : S₁ + U₁ = ContinuousLinearMap.id ℝ EucPlane)
    (hS₁det : S₁.det = 0) (hU₁det : U₁.det = 0)
    (hcov : S₁ ∘L D = D ∘L S₀)
    (hU₁ : 1 ≤ ‖U₁‖)
    {detRate normRate : ℝ}
    (hdet : Real.exp detRate ≤ |D.det|)
    (hnorm : ‖D‖ ≤ Real.exp normRate) :
    Real.exp (detRate - normRate) ≤ ‖D ∘L S₀‖ := by
  apply exp_sub_le_norm_of_adjugate_eq D U₁ hD hU₁
    (abs_det_mul_norm_inverse_comp_complement
      D S₀ S₁ U₁ hD hsum₁ hS₁det hU₁det hcov)
    hdet hnorm

end Submission.Helpers
