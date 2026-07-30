import Submission.Existence

namespace Submission.Factorization

open Filter Function Set
open scoped Topology

noncomputable section

/-- The quotient left after removing the invertible linear part of a function at a point. -/
def linearQuotient (F : ℂ → ℂ) (x : ℂ) (A : ℂ ≃L[ℝ] ℂ) (z : ℂ) : ℂ :=
  1 + (F z - F x - A (z - x)) / A (z - x)

@[simp]
theorem linearQuotient_self (F : ℂ → ℂ) (x : ℂ) (A : ℂ ≃L[ℝ] ℂ) :
    linearQuotient F x A x = 1 := by
  simp [linearQuotient]

theorem continuous_linearQuotient (F : ℂ → ℂ) (x : ℂ) (A : ℂ ≃L[ℝ] ℂ)
    (hF : Continuous F) (hderiv : HasFDerivAt F (A : ℂ →L[ℝ] ℂ) x) :
    Continuous (linearQuotient F x A) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hzx : z = x
  · subst z
    have hsmall :
        (fun y ↦ F y - F x - A (y - x)) =o[𝓝 x]
          (fun y ↦ A (y - x)) :=
      hderiv.isLittleO.trans_isBigO (A.isBigO_sub_rev (𝓝 x) x)
    have hratio :
        Tendsto (fun y ↦ (F y - F x - A (y - x)) / A (y - x))
          (𝓝 x) (𝓝 0) :=
      hsmall.tendsto_div_nhds_zero
    have hratio' :
        ContinuousAt (fun y ↦ (F y - F x - A (y - x)) / A (y - x)) x := by
      change Tendsto (fun y ↦ (F y - F x - A (y - x)) / A (y - x))
        (𝓝 x) (𝓝 ((F x - F x - A (x - x)) / A (x - x)))
      simpa using hratio
    exact continuousAt_const.add hratio'
  · have hdenom : A (z - x) ≠ 0 :=
      by simpa only [map_zero] using A.injective.ne (sub_ne_zero.mpr hzx)
    exact continuousAt_const.add
      (((hF.continuousAt.sub continuousAt_const).sub
          (A.continuous.comp (continuous_id.sub continuous_const)).continuousAt).div₀
        (A.continuous.comp (continuous_id.sub continuous_const)).continuousAt hdenom)

theorem linearQuotient_mul (F : ℂ → ℂ) (x : ℂ) (A : ℂ ≃L[ℝ] ℂ)
    (hFx : F x = 0) (z : ℂ) :
    linearQuotient F x A z * A (z - x) = F z := by
  by_cases hzx : z = x
  · subst z
    simp [hFx]
  · have hdenom : A (z - x) ≠ 0 :=
      by simpa only [map_zero] using A.injective.ne (sub_ne_zero.mpr hzx)
    dsimp [linearQuotient]
    rw [hFx, sub_zero]
    field_simp
    ring

/-- The product of the chosen invertible linear factors at a finite set of points. -/
def linearProduct (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ) (z : ℂ) : ℂ :=
  ∏ x ∈ S, A x (z - x)

/-- The product of all linear factors except the one based at `x`. -/
def remainingProduct (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ) (x z : ℂ) : ℂ :=
  ∏ y ∈ S.erase x, A y (z - y)

theorem continuous_linearProduct (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ) :
    Continuous (linearProduct S A) := by
  apply continuous_finsetProd
  intro x _hx
  exact (A x).continuous.comp (continuous_id.sub continuous_const)

theorem linearProduct_ne_zero (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ)
    {z : ℂ} (hz : z ∉ S) : linearProduct S A z ≠ 0 := by
  rw [linearProduct, Finset.prod_ne_zero_iff]
  intro x hx
  have hzx : z ≠ x := by
    intro h
    apply hz
    rwa [h]
  simpa only [map_zero] using
    (A x).injective.ne (sub_ne_zero.mpr hzx)

theorem linearProduct_eq_zero (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ)
    {z : ℂ} (hz : z ∈ S) : linearProduct S A z = 0 := by
  apply Finset.prod_eq_zero hz
  simp

theorem linearProduct_eq_mul_remaining (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ)
    {x : ℂ} (hx : x ∈ S) (z : ℂ) :
    linearProduct S A z = A x (z - x) * remainingProduct S A x z := by
  exact (Finset.mul_prod_erase S (fun y ↦ A y (z - y)) hx).symm

theorem continuous_remainingProduct (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ) (x : ℂ) :
    Continuous (remainingProduct S A x) :=
  continuous_linearProduct (S.erase x) A

theorem remainingProduct_ne_zero (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ)
    {x : ℂ} : remainingProduct S A x x ≠ 0 :=
  linearProduct_ne_zero (S.erase x) A (by simp)

/-- The residual factor obtained after dividing out every regular zero. At a zero it is
defined by the removable-singularity value. -/
def residual (F : ℂ → ℂ) (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ) (z : ℂ) : ℂ :=
  if z ∈ S then
    (remainingProduct S A z z)⁻¹
  else
    F z / linearProduct S A z

/-- A continuous local formula for the residual near one of the zeros. -/
def localResidual (F : ℂ → ℂ) (S : Finset ℂ) (A : ℂ → ℂ ≃L[ℝ] ℂ)
    (x z : ℂ) : ℂ :=
  linearQuotient F x (A x) z / remainingProduct S A x z

theorem continuousAt_localResidual (F : ℂ → ℂ) (S : Finset ℂ)
    (A : ℂ → ℂ ≃L[ℝ] ℂ) {x : ℂ} (hF : Continuous F)
    (hderiv : HasFDerivAt F (A x : ℂ →L[ℝ] ℂ) x) :
    ContinuousAt (localResidual F S A x) x := by
  exact (continuous_linearQuotient F x (A x) hF hderiv).continuousAt.div₀
    (continuous_remainingProduct S A x).continuousAt
    (remainingProduct_ne_zero S A)

theorem residual_eventuallyEq_localResidual (F : ℂ → ℂ) (S : Finset ℂ)
    (A : ℂ → ℂ ≃L[ℝ] ℂ) {x : ℂ} (hx : x ∈ S) (hFx : F x = 0) :
    residual F S A =ᶠ[𝓝 x] localResidual F S A x := by
  have hnear : ((S.erase x : Finset ℂ) : Set ℂ)ᶜ ∈ 𝓝 x :=
    (S.erase x).isClosed.compl_mem_nhds (by simp)
  filter_upwards [hnear] with z hz
  have hznot : z ∉ S.erase x := by
    intro h
    exact hz h
  by_cases hzx : z = x
  · subst z
    simp [residual, localResidual, hx]
  · have hzS : z ∉ S := by
      intro hzS
      exact hznot (Finset.mem_erase.mpr ⟨hzx, hzS⟩)
    have hlinear : A x (z - x) ≠ 0 := by
      simpa only [map_zero] using
        (A x).injective.ne (sub_ne_zero.mpr hzx)
    have hremaining : remainingProduct S A x z ≠ 0 := by
      exact linearProduct_ne_zero (S.erase x) A hznot
    rw [residual, if_neg hzS, localResidual,
      linearProduct_eq_mul_remaining S A hx,
      ← linearQuotient_mul F x (A x) hFx z]
    field_simp

theorem continuous_residual (F : ℂ → ℂ) (S : Finset ℂ)
    (A : ℂ → ℂ ≃L[ℝ] ℂ) (hF : Continuous F)
    (hzeros : ∀ z, F z = 0 ↔ z ∈ S)
    (hderiv : ∀ x ∈ S, HasFDerivAt F (A x : ℂ →L[ℝ] ℂ) x) :
    Continuous (residual F S A) := by
  rw [continuous_iff_continuousAt]
  intro z
  by_cases hz : z ∈ S
  · exact (continuousAt_localResidual F S A hF (hderiv z hz)).congr
      (residual_eventuallyEq_localResidual F S A hz ((hzeros z).mpr hz)).symm
  · have hnear : ((S : Set ℂ)ᶜ : Set ℂ) ∈ 𝓝 z :=
      S.isClosed.compl_mem_nhds hz
    have hquot : ContinuousAt (fun w ↦ F w / linearProduct S A w) z :=
      hF.continuousAt.div₀ (continuous_linearProduct S A).continuousAt
        (linearProduct_ne_zero S A hz)
    apply hquot.congr
    filter_upwards [hnear] with w hw
    have hwS : w ∉ S := by
      intro h
      exact hw h
    rw [residual, if_neg hwS]

theorem residual_ne_zero (F : ℂ → ℂ) (S : Finset ℂ)
    (A : ℂ → ℂ ≃L[ℝ] ℂ) (hzeros : ∀ z, F z = 0 ↔ z ∈ S) (z : ℂ) :
    residual F S A z ≠ 0 := by
  by_cases hz : z ∈ S
  · rw [residual, if_pos hz]
    exact inv_ne_zero (remainingProduct_ne_zero S A)
  · rw [residual, if_neg hz]
    exact div_ne_zero (fun h ↦ hz ((hzeros z).mp h))
      (linearProduct_ne_zero S A hz)

theorem residual_mul_linearProduct (F : ℂ → ℂ) (S : Finset ℂ)
    (A : ℂ → ℂ ≃L[ℝ] ℂ) (hzeros : ∀ z, F z = 0 ↔ z ∈ S) (z : ℂ) :
    residual F S A z * linearProduct S A z = F z := by
  by_cases hz : z ∈ S
  · rw [linearProduct_eq_zero S A hz, mul_zero, (hzeros z).mpr hz]
  · rw [residual, if_neg hz, div_mul_cancel₀ _ (linearProduct_ne_zero S A hz)]

end

end Submission.Factorization
