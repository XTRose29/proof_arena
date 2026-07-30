import Submission.ZeroMass
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter InnerProductSpace Metric Real Set

namespace Submission.ZeroDensity

open Submission.ZeroMass

open MeasureTheory

private noncomputable def logKernel {α : Type*}
    (a w : α → ℝ) (R : ℝ) (x : α) (t : ℝ) : ℝ :=
  (Ioo (a x) R).indicator (fun t => w x * t⁻¹) t

private lemma logKernel_integrable {α : Type*}
    (a w : α → ℝ) {R : ℝ} {x : α} (ha : 0 < a x) :
    Integrable (logKernel a w R x) := by
  unfold logKernel
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
  have hcont : ContinuousOn (fun t : ℝ => w x * t⁻¹) (Icc (a x) R) :=
    continuousOn_const.mul <| continuousOn_inv₀.mono <| by
      intro t ht
      exact ne_of_gt (ha.trans_le ht.1)
  exact hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self

private lemma integral_logKernel {α : Type*}
    (a w : α → ℝ) {R : ℝ} {x : α} (ha : 0 < a x) (hR : 0 < R)
    (haR : a x ≤ R) :
    ∫ t, logKernel a w R x t = w x * Real.log (R / a x) := by
  unfold logKernel
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le haR]
  rw [intervalIntegral.integral_const_mul, integral_inv_of_pos ha hR]

lemma weighted_log_sum_le
    {α : Type*} [DecidableEq α] (S : Finset α) (a w : α → ℝ)
    {B R : ℝ} (hR : 0 < R)
    (ha : ∀ x ∈ S, 0 < a x) (haR : ∀ x ∈ S, a x ≤ R)
    (hcount : ∀ t ∈ Ioo (0 : ℝ) R,
      ∑ x ∈ S with a x < t, w x ≤ B * t) :
    ∑ x ∈ S, w x * Real.log (R / a x) ≤ B * R := by
  let g : ℝ → ℝ := fun t => ∑ x ∈ S, logKernel a w R x t
  have hgInt : Integrable g := by
    dsimp [g]
    apply integrable_finsetSum
    intro x hx
    exact logKernel_integrable a w (ha x hx)
  have hpoint : ∀ t : ℝ, g t ≤ (Ioo (0 : ℝ) R).indicator (fun _ => B) t := by
    intro t
    by_cases ht : t ∈ Ioo (0 : ℝ) R
    · rw [Set.indicator_of_mem ht]
      dsimp [g, logKernel]
      have hsum :
          ∑ x ∈ S, (Ioo (a x) R).indicator (fun t => w x * t⁻¹) t =
            (∑ x ∈ S with a x < t, w x) * t⁻¹ := by
        rw [Finset.sum_filter, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxt : a x < t
        · rw [if_pos hxt, Set.indicator_of_mem]
          exact ⟨hxt, ht.2⟩
        · rw [if_neg hxt, Set.indicator_of_notMem
            (fun (hmem : t ∈ Ioo (a x) R) => hxt hmem.1)]
          simp
      rw [hsum]
      have hcount' := hcount t ht
      have ht0 : 0 < t := ht.1
      calc
        (∑ x ∈ S with a x < t, w x) * t⁻¹ ≤ (B * t) * t⁻¹ :=
          mul_le_mul_of_nonneg_right hcount' (inv_nonneg.mpr ht0.le)
        _ = B := by field_simp
    · rw [Set.indicator_of_notMem ht]
      dsimp [g, logKernel]
      apply Finset.sum_nonpos
      intro x hx
      rw [Set.indicator_of_notMem]
      intro hmem
      apply ht
      exact ⟨(ha x hx).trans hmem.1, hmem.2⟩
  have hmajorInt : Integrable ((Ioo (0 : ℝ) R).indicator (fun _ => B)) := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    exact integrableOn_const (by simp [Real.volume_Ioo])
  have hint := integral_mono hgInt hmajorInt hpoint
  have hleft : ∫ t, g t = ∑ x ∈ S, w x * Real.log (R / a x) := by
    dsimp [g]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro x hx
      exact integral_logKernel a w (ha x hx) hR (haR x hx)
    · intro x hx
      exact logKernel_integrable a w (ha x hx)
  have hright : ∫ t, (Ioo (0 : ℝ) R).indicator (fun _ => B) t = B * R := by
    rw [integral_indicator measurableSet_Ioo]
    simp [hR.le, mul_comm]
  rwa [hleft, hright] at hint

noncomputable def shiftedZeroCount (R : ℝ) : ℝ :=
  ∑ᶠ u, (shiftedZeroDivisor R u : ℝ)

lemma shiftedZeroCount_nonneg (R : ℝ) :
    0 ≤ shiftedZeroCount R := by
  unfold shiftedZeroCount
  apply finsum_nonneg
  intro u
  exact_mod_cast shiftedZeroDivisor_nonneg R u

lemma sum_shiftedZeroDivisor_filter_norm_lt
    {R t : ℝ} (htR : t < R) :
    ∑ u ∈ (shiftedZeroDivisor_support_finite R).toFinset with ‖u‖ < t,
        (shiftedZeroDivisor R u : ℝ) = shiftedZeroCount t := by
  let S := (shiftedZeroDivisor_support_finite R).toFinset
  have hsupport : Function.support (fun u => (shiftedZeroDivisor t u : ℝ)) ⊆ S := by
    intro u hu
    have hdivt : shiftedZeroDivisor t u ≠ 0 := by
      simpa [Function.mem_support] using hu
    have hut : u ∈ ball (0 : ℂ) t :=
      (shiftedZeroDivisor t).supportWithinDomain hdivt
    have huR : u ∈ ball (0 : ℂ) R := by
      exact ball_subset_ball (show t ≤ R from htR.le) hut
    have heq : shiftedZeroDivisor R u = shiftedZeroDivisor t u := by
      unfold shiftedZeroDivisor
      rw [MeromorphicOn.divisor_apply
          (fun z _hz => meromorphic_shiftedChiFourXi z) huR,
        MeromorphicOn.divisor_apply
          (fun z _hz => meromorphic_shiftedChiFourXi z) hut]
    exact (shiftedZeroDivisor_support_finite R).mem_toFinset.mpr <| by
      change shiftedZeroDivisor R u ≠ 0
      rw [heq]
      exact hdivt
  unfold shiftedZeroCount
  rw [finsum_eq_finsetSum_of_support_subset _ hsupport]
  change (∑ u ∈ S with ‖u‖ < t, (shiftedZeroDivisor R u : ℝ)) =
    ∑ u ∈ S, (shiftedZeroDivisor t u : ℝ)
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro u hu
  by_cases hut : ‖u‖ < t
  · simp only [hut, if_true]
    have hutBall : u ∈ ball (0 : ℂ) t := by
      simpa [mem_ball_iff_norm] using hut
    have huRBall : u ∈ ball (0 : ℂ) R :=
      ball_subset_ball htR.le hutBall
    unfold shiftedZeroDivisor
    rw [MeromorphicOn.divisor_apply
        (fun z _hz => meromorphic_shiftedChiFourXi z) huRBall,
      MeromorphicOn.divisor_apply
        (fun z _hz => meromorphic_shiftedChiFourXi z) hutBall]
  · simp only [hut, if_false]
    have hzero : shiftedZeroDivisor t u = 0 := by
      by_contra hdiv
      have huBall := (shiftedZeroDivisor t).supportWithinDomain hdiv
      exact hut (by simpa [mem_ball_iff_norm] using huBall)
    rw [hzero]
    simp

lemma shiftedLogCounting_le_of_count_bound
    {B R : ℝ} (hR : 0 < R)
    (hcount : ∀ t : ℝ, 0 < t → shiftedZeroCount t ≤ B * t) :
    ∑ u ∈ (shiftedZeroDivisor_support_finite R).toFinset,
        (shiftedZeroDivisor R u : ℝ) * Real.log (R / ‖u‖) ≤ B * R := by
  apply weighted_log_sum_le
  · exact hR
  · intro u hu
    have hdiv : shiftedZeroDivisor R u ≠ 0 :=
      (shiftedZeroDivisor_support_finite R).mem_toFinset.mp hu
    have hu0 : u ≠ 0 := by
      intro h
      subst u
      exact hdiv (shiftedZeroDivisor_zero hR)
    exact norm_pos_iff.mpr hu0
  · intro u hu
    have hdiv : shiftedZeroDivisor R u ≠ 0 :=
      (shiftedZeroDivisor_support_finite R).mem_toFinset.mp hu
    have huBall := (shiftedZeroDivisor R).supportWithinDomain hdiv
    have huNorm : ‖u‖ < R := by
      simpa [mem_ball_iff_norm] using huBall
    exact huNorm.le
  · intro t ht
    rw [sum_shiftedZeroDivisor_filter_norm_lt ht.2]
    exact hcount t ht.1

private noncomputable def invSqKernel {α : Type*}
    (a w : α → ℝ) (r R : ℝ) (x : α) (t : ℝ) : ℝ :=
  (Ioo (a x) R).indicator (fun t => w x * (2 * r ^ 2 * t ^ (-3 : ℤ))) t

private lemma invSqKernel_integrable {α : Type*}
    (a w : α → ℝ) {r R : ℝ} {x : α} (ha : 0 < a x) :
    Integrable (invSqKernel a w r R x) := by
  unfold invSqKernel
  apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
  have hcont : ContinuousOn
      (fun t : ℝ => w x * (2 * r ^ 2 * t ^ (-3 : ℤ))) (Icc (a x) R) := by
    apply continuousOn_const.mul
    apply continuousOn_const.mul
    exact (continuousOn_zpow₀ (-3)).mono <| by
      intro t ht
      exact ne_of_gt (ha.trans_le ht.1)
  exact hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self

private lemma integral_invSqKernel {α : Type*}
    (a w : α → ℝ) {r R : ℝ} {x : α} (ha : 0 < a x) (hR : 0 < R)
    (haR : a x ≤ R) :
    ∫ t, invSqKernel a w r R x t =
      w x * (r ^ 2 / (a x) ^ 2 - r ^ 2 / R ^ 2) := by
  unfold invSqKernel
  rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le haR]
  rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [integral_zpow (n := (-3 : ℤ)) (Or.inr ⟨by norm_num,
    notMem_uIcc_of_lt ha hR⟩)]
  have hcore :
      2 * r ^ 2 *
          ((R ^ ((-3 : ℤ) + 1) - (a x) ^ ((-3 : ℤ) + 1)) /
            (((-3 : ℤ) : ℝ) + 1)) =
        r ^ 2 / (a x) ^ 2 - r ^ 2 / R ^ 2 := by
    norm_num [zpow_neg]
    field_simp [ha.ne', hR.ne']
    ring
  rw [hcore]

lemma weighted_invSq_tail_le
    {α : Type*} [DecidableEq α] (S : Finset α) (a w : α → ℝ)
    {B r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hB : 0 ≤ B)
    (ha : ∀ x ∈ S, r ≤ a x) (haR : ∀ x ∈ S, a x ≤ R)
    (hcount : ∀ t ∈ Ioo r R,
      ∑ x ∈ S with a x < t, w x ≤ B * t)
    (hcountR : ∑ x ∈ S, w x ≤ B * R) :
    ∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2) ≤ 3 * B * r := by
  have hR : 0 < R := hr.trans_le hrR
  let g : ℝ → ℝ := fun t => ∑ x ∈ S, invSqKernel a w r R x t
  have hgInt : Integrable g := by
    dsimp [g]
    apply integrable_finsetSum
    intro x hx
    exact invSqKernel_integrable a w (hr.trans_le (ha x hx))
  have hmajorInt : Integrable
      ((Ioo r R).indicator (fun t => 2 * B * r ^ 2 * t ^ (-2 : ℤ))) := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    have hcont : ContinuousOn
        (fun t : ℝ => 2 * B * r ^ 2 * t ^ (-2 : ℤ)) (Icc r R) := by
      apply continuousOn_const.mul
      exact (continuousOn_zpow₀ (-2)).mono <| by
        intro t ht
        exact ne_of_gt (hr.trans_le ht.1)
    exact hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hpoint : ∀ t : ℝ, g t ≤
      (Ioo r R).indicator (fun t => 2 * B * r ^ 2 * t ^ (-2 : ℤ)) t := by
    intro t
    by_cases ht : t ∈ Ioo r R
    · rw [Set.indicator_of_mem ht]
      dsimp [g, invSqKernel]
      have hsum :
          ∑ x ∈ S,
              (Ioo (a x) R).indicator
                (fun t => w x * (2 * r ^ 2 * t ^ (-3 : ℤ))) t =
            (∑ x ∈ S with a x < t, w x) *
              (2 * r ^ 2 * t ^ (-3 : ℤ)) := by
        rw [Finset.sum_filter, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxt : a x < t
        · rw [if_pos hxt, Set.indicator_of_mem
            (show t ∈ Ioo (a x) R from ⟨hxt, ht.2⟩)]
        · rw [if_neg hxt, Set.indicator_of_notMem
            (fun hmem : t ∈ Ioo (a x) R => hxt hmem.1)]
          simp
      rw [hsum]
      have ht0 : 0 < t := hr.trans ht.1
      have htPow : 0 ≤ t ^ (-3 : ℤ) := zpow_nonneg ht0.le _
      have hkNonneg : 0 ≤ 2 * r ^ 2 * t ^ (-3 : ℤ) := by positivity
      have hmul := mul_le_mul_of_nonneg_right (hcount t ht) hkNonneg
      calc
        (∑ x ∈ S with a x < t, w x) * (2 * r ^ 2 * t ^ (-3 : ℤ)) ≤
            (B * t) * (2 * r ^ 2 * t ^ (-3 : ℤ)) := hmul
        _ = 2 * B * r ^ 2 * t ^ (-2 : ℤ) := by
          field_simp [ht.1.ne']
    · rw [Set.indicator_of_notMem ht]
      dsimp [g, invSqKernel]
      apply Finset.sum_nonpos
      intro x hx
      rw [Set.indicator_of_notMem]
      intro hmem
      apply ht
      exact ⟨(ha x hx).trans_lt hmem.1, hmem.2⟩
  have hint := integral_mono hgInt hmajorInt hpoint
  have hleft : ∫ t, g t =
      ∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2 - r ^ 2 / R ^ 2) := by
    dsimp [g]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro x hx
      exact integral_invSqKernel a w (hr.trans_le (ha x hx)) hR (haR x hx)
    · intro x hx
      exact invSqKernel_integrable a w (hr.trans_le (ha x hx))
  have hright :
      ∫ t, (Ioo r R).indicator (fun t => 2 * B * r ^ 2 * t ^ (-2 : ℤ)) t ≤
        2 * B * r := by
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hrR]
    rw [intervalIntegral.integral_const_mul, integral_zpow (n := (-2 : ℤ))
      (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hr hR⟩)]
    norm_num [zpow_neg]
    have heq :
        2 * B * r ^ 2 * ((R⁻¹ - r⁻¹) / -1) =
          2 * B * r * (1 - r / R) := by
      field_simp [hr.ne', hR.ne']
      ring
    rw [heq]
    have hfactor : 0 ≤ 2 * B * r := by positivity
    apply mul_le_of_le_one_right hfactor
    exact sub_le_self 1 (div_nonneg hr.le hR.le)
  have hint' :
      ∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2 - r ^ 2 / R ^ 2) ≤
        2 * B * r := by
    rw [← hleft]
    exact hint.trans hright
  have hboundary :
      ∑ x ∈ S, w x * (r ^ 2 / R ^ 2) ≤ B * r := by
    rw [← Finset.sum_mul]
    have hfactor : 0 ≤ r ^ 2 / R ^ 2 := by positivity
    calc
      (∑ x ∈ S, w x) * (r ^ 2 / R ^ 2) ≤
          (B * R) * (r ^ 2 / R ^ 2) :=
        mul_le_mul_of_nonneg_right hcountR hfactor
      _ ≤ B * r := by
        have hBR : 0 ≤ B * r := mul_nonneg hB hr.le
        field_simp [hR.ne']
        nlinarith
  calc
    ∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2) =
        (∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2 - r ^ 2 / R ^ 2)) +
          ∑ x ∈ S, w x * (r ^ 2 / R ^ 2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ 2 * B * r + B * r := add_le_add hint' hboundary
    _ = 3 * B * r := by ring

/-- A version of `weighted_invSq_tail_le` adapted to a counting function of
order `t * sqrt t`.  The important feature is that the bound is uniform in
the outer radius. -/
lemma weighted_invSq_tail_le_threeHalves
    {α : Type*} [DecidableEq α] (S : Finset α) (a w : α → ℝ)
    {B r R : ℝ} (hr : 0 < r) (hrR : r ≤ R) (hB : 0 ≤ B)
    (ha : ∀ x ∈ S, r ≤ a x) (haR : ∀ x ∈ S, a x ≤ R)
    (hcount : ∀ t ∈ Ioo r R,
      ∑ x ∈ S with a x < t, w x ≤ B * t * Real.sqrt t)
    (hcountR : ∑ x ∈ S, w x ≤ B * R * Real.sqrt R) :
    ∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2) ≤
      5 * B * r ^ 2 / Real.sqrt r := by
  have hR : 0 < R := hr.trans_le hrR
  let g : ℝ → ℝ := fun t => ∑ x ∈ S, invSqKernel a w r R x t
  have hgInt : Integrable g := by
    dsimp [g]
    apply integrable_finsetSum
    intro x hx
    exact invSqKernel_integrable a w (hr.trans_le (ha x hx))
  let major : ℝ → ℝ := fun t => 2 * B * r ^ 2 * t ^ (-3 / 2 : ℝ)
  have hmajorInt : Integrable ((Ioo r R).indicator major) := by
    apply IntegrableOn.integrable_indicator _ measurableSet_Ioo
    have hcont : ContinuousOn major (Icc r R) := by
      intro t ht
      apply ContinuousAt.continuousWithinAt
      dsimp [major]
      apply ContinuousAt.mul continuousAt_const
      exact Real.continuousAt_rpow_const t _
        (Or.inl (ne_of_gt (hr.trans_le ht.1)))
    exact hcont.integrableOn_Icc.mono_set Ioo_subset_Icc_self
  have hpoint : ∀ t : ℝ, g t ≤ (Ioo r R).indicator major t := by
    intro t
    by_cases ht : t ∈ Ioo r R
    · rw [Set.indicator_of_mem ht]
      dsimp [g, invSqKernel, major]
      have hsum :
          ∑ x ∈ S,
              (Ioo (a x) R).indicator
                (fun t => w x * (2 * r ^ 2 * t ^ (-3 : ℤ))) t =
            (∑ x ∈ S with a x < t, w x) *
              (2 * r ^ 2 * t ^ (-3 : ℤ)) := by
        rw [Finset.sum_filter, Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro x hx
        by_cases hxt : a x < t
        · rw [if_pos hxt, Set.indicator_of_mem
            (show t ∈ Ioo (a x) R from ⟨hxt, ht.2⟩)]
        · rw [if_neg hxt, Set.indicator_of_notMem
            (fun hmem : t ∈ Ioo (a x) R => hxt hmem.1)]
          simp
      rw [hsum]
      have ht0 : 0 < t := hr.trans ht.1
      have hkNonneg : 0 ≤ 2 * r ^ 2 * t ^ (-3 : ℤ) := by positivity
      have hmul := mul_le_mul_of_nonneg_right (hcount t ht) hkNonneg
      calc
        (∑ x ∈ S with a x < t, w x) * (2 * r ^ 2 * t ^ (-3 : ℤ)) ≤
            (B * t * Real.sqrt t) * (2 * r ^ 2 * t ^ (-3 : ℤ)) := hmul
        _ = 2 * B * r ^ 2 * t ^ (-3 / 2 : ℝ) := by
          have hpow : t * Real.sqrt t * t ^ (-3 : ℤ) =
              t ^ (-3 / 2 : ℝ) := by
            rw [Real.sqrt_eq_rpow]
            rw [show t ^ (-3 : ℤ) = t ^ (-3 : ℝ) by norm_num]
            calc
              t * t ^ (1 / 2 : ℝ) * t ^ (-3 : ℝ) =
                  t ^ (1 : ℝ) * t ^ (1 / 2 : ℝ) * t ^ (-3 : ℝ) := by
                rw [Real.rpow_one]
              _ = t ^ ((1 : ℝ) + 1 / 2) * t ^ (-3 : ℝ) := by
                congr 1
                exact (Real.rpow_add ht0 _ _).symm
              _ = t ^ ((1 : ℝ) + 1 / 2 + (-3 : ℝ)) := by
                exact (Real.rpow_add ht0 _ _).symm
              _ = t ^ (-3 / 2 : ℝ) := by norm_num
          rw [← hpow]
          ring
    · rw [Set.indicator_of_notMem ht]
      dsimp [g, invSqKernel]
      apply Finset.sum_nonpos
      intro x hx
      rw [Set.indicator_of_notMem]
      intro hmem
      apply ht
      exact ⟨(ha x hx).trans_lt hmem.1, hmem.2⟩
  have hint := integral_mono hgInt hmajorInt hpoint
  have hleft : ∫ t, g t =
      ∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2 - r ^ 2 / R ^ 2) := by
    dsimp [g]
    rw [integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro x hx
      exact integral_invSqKernel a w (hr.trans_le (ha x hx)) hR (haR x hx)
    · intro x hx
      exact invSqKernel_integrable a w (hr.trans_le (ha x hx))
  have hrSqrt : 0 < Real.sqrt r := Real.sqrt_pos.2 hr
  have hRSqrt : 0 < Real.sqrt R := Real.sqrt_pos.2 hR
  have hright : ∫ t, (Ioo r R).indicator major t ≤
      4 * B * r ^ 2 / Real.sqrt r := by
    rw [integral_indicator measurableSet_Ioo, ← integral_Ioc_eq_integral_Ioo,
      ← intervalIntegral.integral_of_le hrR]
    dsimp [major]
    rw [intervalIntegral.integral_const_mul,
      integral_rpow (r := (-3 / 2 : ℝ))
        (Or.inr ⟨by norm_num, notMem_uIcc_of_lt hr hR⟩)]
    have hrpow : r ^ (-1 / 2 : ℝ) = (Real.sqrt r)⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hr.le, ← Real.sqrt_eq_rpow]
    have hRpow : R ^ (-1 / 2 : ℝ) = (Real.sqrt R)⁻¹ := by
      rw [show (-1 / 2 : ℝ) = -(1 / 2 : ℝ) by ring,
        Real.rpow_neg hR.le, ← Real.sqrt_eq_rpow]
    rw [show (-3 / 2 : ℝ) + 1 = -1 / 2 by ring, hrpow, hRpow]
    have hInv : (Real.sqrt R)⁻¹ ≤ (Real.sqrt r)⁻¹ := by
      exact inv_anti₀ hrSqrt (Real.sqrt_le_sqrt hrR)
    field_simp [hrSqrt.ne', hRSqrt.ne']
    nlinarith [hB, Real.sqrt_nonneg r, Real.sqrt_nonneg R]
  have hint' :
      ∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2 - r ^ 2 / R ^ 2) ≤
        4 * B * r ^ 2 / Real.sqrt r := by
    rw [← hleft]
    exact hint.trans hright
  have hboundary :
      ∑ x ∈ S, w x * (r ^ 2 / R ^ 2) ≤
        B * r ^ 2 / Real.sqrt r := by
    rw [← Finset.sum_mul]
    have hfactor : 0 ≤ r ^ 2 / R ^ 2 := by positivity
    calc
      (∑ x ∈ S, w x) * (r ^ 2 / R ^ 2) ≤
          (B * R * Real.sqrt R) * (r ^ 2 / R ^ 2) :=
        mul_le_mul_of_nonneg_right hcountR hfactor
      _ = B * r ^ 2 / Real.sqrt R := by
        field_simp [hR.ne', hRSqrt.ne']
        nlinarith [Real.sq_sqrt hR.le]
      _ ≤ B * r ^ 2 / Real.sqrt r := by
        gcongr
  calc
    ∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2) =
        (∑ x ∈ S, w x * (r ^ 2 / (a x) ^ 2 - r ^ 2 / R ^ 2)) +
          ∑ x ∈ S, w x * (r ^ 2 / R ^ 2) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      ring
    _ ≤ 4 * B * r ^ 2 / Real.sqrt r +
        B * r ^ 2 / Real.sqrt r := add_le_add hint' hboundary
    _ = 5 * B * r ^ 2 / Real.sqrt r := by ring

lemma sum_shiftedZeroDivisor_eq_count (R : ℝ) :
    ∑ u ∈ (shiftedZeroDivisor_support_finite R).toFinset,
        (shiftedZeroDivisor R u : ℝ) = shiftedZeroCount R := by
  unfold shiftedZeroCount
  apply (finsum_eq_finsetSum_of_support_subset _ ?_).symm
  intro u hu
  have hdiv : shiftedZeroDivisor R u ≠ 0 := by
    simpa [Function.mem_support] using hu
  exact (shiftedZeroDivisor_support_finite R).mem_toFinset.mpr hdiv

lemma shiftedInvSqTail_le_of_count_bound
    {B r R : ℝ} (hr : 0 < r) (hrR : r ≤ R)
    (hcount : ∀ t : ℝ, 0 < t → shiftedZeroCount t ≤ B * t) :
    ∑ u ∈ (shiftedZeroDivisor_support_finite R).toFinset with r ≤ ‖u‖,
        (shiftedZeroDivisor R u : ℝ) * (r ^ 2 / ‖u‖ ^ 2) ≤ 3 * B * r := by
  let S := (shiftedZeroDivisor_support_finite R).toFinset
  let T := S.filter fun u => r ≤ ‖u‖
  have hB : 0 ≤ B := by
    have hnonneg := shiftedZeroCount_nonneg 1
    have hupper := hcount 1 (by norm_num)
    linarith
  change ∑ u ∈ T, (shiftedZeroDivisor R u : ℝ) * (r ^ 2 / ‖u‖ ^ 2) ≤
    3 * B * r
  apply weighted_invSq_tail_le T norm (fun u => (shiftedZeroDivisor R u : ℝ))
  · exact hr
  · exact hrR
  · exact hB
  · intro u hu
    exact (Finset.mem_filter.mp hu).2
  · intro u hu
    have hdiv : shiftedZeroDivisor R u ≠ 0 := by
      exact (shiftedZeroDivisor_support_finite R).mem_toFinset.mp
        (Finset.mem_filter.mp hu).1
    have huBall := (shiftedZeroDivisor R).supportWithinDomain hdiv
    have huNorm : ‖u‖ < R := by
      simpa [mem_ball_iff_norm] using huBall
    exact huNorm.le
  · intro t ht
    let U := S.filter fun u => ‖u‖ < t
    have hsub : T.filter (fun u => ‖u‖ < t) ⊆ U := by
      intro u hu
      have hu' := Finset.mem_filter.mp hu
      have huT := Finset.mem_filter.mp hu'.1
      exact Finset.mem_filter.mpr ⟨huT.1, hu'.2⟩
    calc
      ∑ u ∈ T with ‖u‖ < t, (shiftedZeroDivisor R u : ℝ) ≤
          ∑ u ∈ U, (shiftedZeroDivisor R u : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsub
        intro u huU huT
        exact_mod_cast shiftedZeroDivisor_nonneg R u
      _ = shiftedZeroCount t := by
        dsimp [U, S]
        exact sum_shiftedZeroDivisor_filter_norm_lt ht.2
      _ ≤ B * t := hcount t (hr.trans ht.1)
  · calc
      ∑ u ∈ T, (shiftedZeroDivisor R u : ℝ) ≤
          ∑ u ∈ S, (shiftedZeroDivisor R u : ℝ) := by
        have hTS : T ⊆ S := by
          intro u hu
          exact (Finset.mem_filter.mp hu).1
        apply Finset.sum_le_sum_of_subset_of_nonneg hTS
        intro u huS huT
        exact_mod_cast shiftedZeroDivisor_nonneg R u
      _ = shiftedZeroCount R := by
        dsimp [S]
        exact sum_shiftedZeroDivisor_eq_count R
      _ ≤ B * R := hcount R (hr.trans_le hrR)

private lemma norm_canonicalFactor_zero {R : ℝ} (hR : 0 < R) {u : ℂ}
    (hu0 : u ≠ 0) :
    ‖Complex.canonicalFactor R u 0‖ = R / ‖u‖ := by
  rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
  simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  field_simp [hR.ne', norm_ne_zero_iff.mpr hu0]

private lemma canonical_pair_ratio_le
    {R r : ℝ} {u : ℂ} (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / 2)
    (huBall : u ∈ ball (0 : ℂ) R) (hu0 : u ≠ 0)
    (hru : (r : ℂ) ≠ u) (hnegu : (-r : ℂ) ≠ u) :
    ‖Complex.canonicalFactor R u 0‖ ^ 2 /
        (‖Complex.canonicalFactor R u (r : ℂ)‖ *
          ‖Complex.canonicalFactor R u (-r : ℂ)‖) ≤
      (1 + r ^ 2 / ‖u‖ ^ 2) /
        (1 - ‖u‖ ^ 2 * r ^ 2 / R ^ 4) := by
  let a := ‖u‖
  let dp := ‖(r : ℂ) - u‖
  let dm := ‖(-r : ℂ) - u‖
  let np := ‖((R : ℂ) ^ 2) - (starRingEnd ℂ) u * (r : ℂ)‖
  let nm := ‖((R : ℂ) ^ 2) - (starRingEnd ℂ) u * (-r : ℂ)‖
  have ha : 0 < a := by
    dsimp [a]
    exact norm_pos_iff.mpr hu0
  have haR : a < R := by
    simpa [a, mem_ball_iff_norm] using huBall
  have hdp : 0 < dp := by
    dsimp [dp]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hru)
  have hdm : 0 < dm := by
    dsimp [dm]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hnegu)
  have hD : dp * dm ≤ a ^ 2 + r ^ 2 := by
    calc
      dp * dm = ‖((r : ℂ) - u) * ((-r : ℂ) - u)‖ := by
        simp [dp, dm]
      _ = ‖u ^ 2 - (r : ℂ) ^ 2‖ := by
        congr 1
        ring
      _ ≤ ‖u ^ 2‖ + ‖(r : ℂ) ^ 2‖ := norm_sub_le _ _
      _ = a ^ 2 + r ^ 2 := by
        simp [a, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
  have hN : R ^ 4 - a ^ 2 * r ^ 2 ≤ np * nm := by
    have hprod : np * nm =
        ‖((R : ℂ) ^ 4) - ((starRingEnd ℂ) u * (r : ℂ)) ^ 2‖ := by
      calc
        np * nm =
            ‖(((R : ℂ) ^ 2) - (starRingEnd ℂ) u * (r : ℂ)) *
              (((R : ℂ) ^ 2) - (starRingEnd ℂ) u * (-r : ℂ))‖ := by
          rw [norm_mul]
        _ = ‖((R : ℂ) ^ 4) - ((starRingEnd ℂ) u * (r : ℂ)) ^ 2‖ := by
          congr 1
          ring
    rw [hprod]
    have hrev := norm_sub_norm_le ((R : ℂ) ^ 4)
      (((starRingEnd ℂ) u * (r : ℂ)) ^ 2)
    calc
      R ^ 4 - a ^ 2 * r ^ 2 =
          ‖((R : ℂ) ^ 4)‖ - ‖((starRingEnd ℂ) u * (r : ℂ)) ^ 2‖ := by
        simp [a, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos hR, abs_of_nonneg hr0]
        ring
      _ ≤ ‖((R : ℂ) ^ 4) - ((starRingEnd ℂ) u * (r : ℂ)) ^ 2‖ := hrev
  have hgap : 0 < R ^ 4 - a ^ 2 * r ^ 2 := by
    have har : a ^ 2 * r ^ 2 ≤ R ^ 2 * (R / 2) ^ 2 := by
      gcongr
    nlinarith [sq_pos_of_pos hR]
  have hnp : 0 < np := by
    have : 0 < np * nm := hgap.trans_le hN
    exact pos_of_mul_pos_left this (norm_nonneg _)
  have hnm : 0 < nm := by
    have : 0 < np * nm := hgap.trans_le hN
    exact pos_of_mul_pos_right this (norm_nonneg _)
  have hcfp :
      ‖Complex.canonicalFactor R u (r : ℂ)‖ = np / (R * dp) := by
    rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rfl
  have hcfm :
      ‖Complex.canonicalFactor R u (-r : ℂ)‖ = nm / (R * dm) := by
    rw [Complex.canonicalFactor_apply, norm_div, norm_mul]
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rfl
  have hden : 0 < 1 - a ^ 2 * r ^ 2 / R ^ 4 := by
    rw [sub_pos, div_lt_one (by positivity : 0 < R ^ 4)]
    exact sub_pos.mp hgap
  rw [norm_canonicalFactor_zero hR hu0, hcfp, hcfm]
  change (R / a) ^ 2 / ((np / (R * dp)) * (nm / (R * dm))) ≤
    (1 + r ^ 2 / a ^ 2) / (1 - a ^ 2 * r ^ 2 / R ^ 4)
  rw [div_le_div_iff₀ (by positivity : 0 < (np / (R * dp)) * (nm / (R * dm))) hden]
  field_simp [hR.ne', ha.ne', hnp.ne', hnm.ne', hdp.ne', hdm.ne']
  have hcross :
      dp * dm * (R ^ 4 - a ^ 2 * r ^ 2) ≤
        (a ^ 2 + r ^ 2) * (np * nm) := by
    calc
      dp * dm * (R ^ 4 - a ^ 2 * r ^ 2) ≤
          (a ^ 2 + r ^ 2) * (R ^ 4 - a ^ 2 * r ^ 2) :=
        mul_le_mul_of_nonneg_right hD hgap.le
      _ ≤ (a ^ 2 + r ^ 2) * (np * nm) :=
        mul_le_mul_of_nonneg_left hN (by positivity)
  nlinarith [hcross]

private lemma neg_log_one_sub_le_two_mul
    {y : ℝ} (hy0 : 0 ≤ y) (hy : y ≤ 1 / 2) :
    -Real.log (1 - y) ≤ 2 * y := by
  have hden : 0 < 1 - y := by linarith
  have hinv : (1 - y)⁻¹ - 1 ≤ 2 * y := by
    have heq : (1 - y)⁻¹ - 1 = y / (1 - y) := by
      field_simp [hden.ne']
      ring
    rw [heq]
    apply (div_le_iff₀ hden).2
    nlinarith
  have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr hden)
  rw [Real.log_inv] at hlog
  linarith

private lemma canonicalFactor_log_pair_le
    {R r : ℝ} {u : ℂ} (hR : 0 < R) (hr0 : 0 ≤ r) (hr : r ≤ R / 2)
    (huBall : u ∈ ball (0 : ℂ) R) (hu0 : u ≠ 0)
    (hru : (r : ℂ) ≠ u) (hnegu : (-r : ℂ) ≠ u) :
    2 * Real.log ‖Complex.canonicalFactor R u 0‖ -
        Real.log ‖Complex.canonicalFactor R u (r : ℂ)‖ -
        Real.log ‖Complex.canonicalFactor R u (-r : ℂ)‖ ≤
      Real.log (1 + r ^ 2 / ‖u‖ ^ 2) +
        2 * (‖u‖ ^ 2 * r ^ 2 / R ^ 4) := by
  have hrLe : r ≤ R := by linarith
  have hrClosed : (r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hrLe
  have hnegClosed : (-r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, norm_neg, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg hr0]
    exact hrLe
  have hzeroClosed : (0 : ℂ) ∈ closedBall (0 : ℂ) R :=
    mem_closedBall_self hR.le
  have hcf0 : Complex.canonicalFactor R u 0 ≠ 0 :=
    Complex.canonicalFactor_ne_zero huBall hzeroClosed (Ne.symm hu0)
  have hcfp : Complex.canonicalFactor R u (r : ℂ) ≠ 0 :=
    Complex.canonicalFactor_ne_zero huBall hrClosed hru
  have hcfm : Complex.canonicalFactor R u (-r : ℂ) ≠ 0 :=
    Complex.canonicalFactor_ne_zero huBall hnegClosed hnegu
  let x := r ^ 2 / ‖u‖ ^ 2
  let y := ‖u‖ ^ 2 * r ^ 2 / R ^ 4
  have hx : 0 ≤ x := by dsimp [x]; positivity
  have hy0 : 0 ≤ y := by dsimp [y]; positivity
  have huNorm : ‖u‖ < R := by
    simpa [mem_ball_iff_norm] using huBall
  have hy : y ≤ 1 / 2 := by
    dsimp [y]
    apply (div_le_iff₀ (by positivity : 0 < R ^ 4)).2
    have huSq : ‖u‖ ^ 2 ≤ R ^ 2 := by
      nlinarith [norm_nonneg u, sq_nonneg (R - ‖u‖)]
    have hrSq : r ^ 2 ≤ (R / 2) ^ 2 := by
      nlinarith [sq_nonneg (R / 2 - r)]
    nlinarith [mul_le_mul huSq hrSq (sq_nonneg r) (sq_nonneg R)]
  have hden : 0 < 1 - y := by linarith
  have hratio := canonical_pair_ratio_le hR hr0 hr huBall hu0 hru hnegu
  change ‖Complex.canonicalFactor R u 0‖ ^ 2 /
      (‖Complex.canonicalFactor R u (r : ℂ)‖ *
        ‖Complex.canonicalFactor R u (-r : ℂ)‖) ≤
    (1 + x) / (1 - y) at hratio
  have hratioPos :
      0 < ‖Complex.canonicalFactor R u 0‖ ^ 2 /
        (‖Complex.canonicalFactor R u (r : ℂ)‖ *
          ‖Complex.canonicalFactor R u (-r : ℂ)‖) := by positivity
  have hlog := Real.log_le_log hratioPos hratio
  rw [Real.log_div (pow_ne_zero 2 (norm_ne_zero_iff.mpr hcf0))
      (mul_ne_zero (norm_ne_zero_iff.mpr hcfp) (norm_ne_zero_iff.mpr hcfm)),
    Real.log_pow, Real.log_mul (norm_ne_zero_iff.mpr hcfp)
      (norm_ne_zero_iff.mpr hcfm),
    Real.log_div (by positivity : 1 + x ≠ 0) hden.ne'] at hlog
  have hyLog := neg_log_one_sub_le_two_mul hy0 hy
  dsimp [x, y] at hlog hyLog ⊢
  linarith

private lemma shiftedCanonicalProduct_mulSupport_finite (R : ℝ) :
    Function.HasFiniteMulSupport
      (fun u => (Complex.canonicalFactor R u) ^ (-shiftedZeroDivisor R u)) := by
  apply (shiftedZeroDivisor_support_finite R).subset
  intro u hu
  rw [Function.mem_support]
  intro hdiv
  simp [hdiv] at hu

private lemma log_norm_shiftedCanonicalProduct_eq_sum
    {R : ℝ} {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) R)
    (hfz : shiftedChiFourXi z ≠ 0) :
    Real.log ‖shiftedCanonicalProduct R z‖ =
      ∑ u ∈ (shiftedZeroDivisor_support_finite R).toFinset,
        Real.log ‖Complex.canonicalFactor R u z ^ (-shiftedZeroDivisor R u)‖ := by
  unfold shiftedCanonicalProduct
  rw [finprod_apply (shiftedCanonicalProduct_mulSupport_finite R) z]
  simp only [Pi.pow_apply]
  have hmulSubset : Function.mulSupport
      (fun u => Complex.canonicalFactor R u z ^ (-shiftedZeroDivisor R u)) ⊆
      (shiftedZeroDivisor R).support := by
    intro u hu
    rw [Function.mem_support]
    intro hdiv
    simp [hdiv] at hu
  rw [finprod_eq_prod_of_mulSupport_subset_of_finite _ hmulSubset
    (shiftedZeroDivisor_support_finite R)]
  rw [norm_prod]
  apply Real.log_prod
  intro u hu
  apply norm_ne_zero_iff.mpr
  apply zpow_ne_zero
  have hdiv : shiftedZeroDivisor R u ≠ 0 :=
    (shiftedZeroDivisor_support_finite R).mem_toFinset.mp hu
  have huBall : u ∈ ball (0 : ℂ) R :=
    (shiftedZeroDivisor R).supportWithinDomain hdiv
  have hzDiv := shiftedZeroDivisor_eq_zero_of_ne_zero hz hfz
  have hzu : z ≠ u := by
    intro h
    subst u
    exact hdiv hzDiv
  exact Complex.canonicalFactor_ne_zero huBall hz hzu

private lemma log_one_add_sq_div_le_two_log
    {a r : ℝ} (ha : 0 < a) (hr : 0 < r) (har : a ≤ r) :
    Real.log (1 + r ^ 2 / a ^ 2) ≤ 2 * Real.log (2 * r / a) := by
  have hx : 1 ≤ r ^ 2 / a ^ 2 := by
    apply (one_le_div (sq_pos_of_pos ha)).2
    nlinarith
  have harg : 0 < 1 + r ^ 2 / a ^ 2 := by positivity
  have hright : 0 < 2 * r / a := by positivity
  have hle : 1 + r ^ 2 / a ^ 2 ≤ (2 * r / a) ^ 2 := by
    field_simp [ha.ne']
    nlinarith [sq_nonneg (r - a)]
  have hlog := Real.log_le_log harg hle
  rw [Real.log_pow] at hlog
  exact hlog

lemma log_norm_shiftedCanonicalProduct_pair_le_count
    {B R r : ℝ} (hR : 0 < R) (hr : 0 < r) (h2rR : 2 * r < R)
    (hf : shiftedChiFourXi (r : ℂ) ≠ 0)
    (hcount : ∀ t : ℝ, 0 < t → shiftedZeroCount t ≤ B * t) :
    Real.log ‖shiftedCanonicalProduct R (r : ℂ)‖ +
        Real.log ‖shiftedCanonicalProduct R (-r : ℂ)‖ -
        2 * Real.log ‖shiftedCanonicalProduct R 0‖ ≤
      9 * B * r := by
  let S := (shiftedZeroDivisor_support_finite R).toFinset
  let I := S.filter fun u => ‖u‖ < r
  let O := S.filter fun u => r ≤ ‖u‖
  have hr0 : 0 ≤ r := hr.le
  have hrHalf : r ≤ R / 2 := by linarith
  have hB : 0 ≤ B := by
    have hnonneg := shiftedZeroCount_nonneg 1
    have hupper := hcount 1 (by norm_num)
    linarith
  have hrNorm : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hnegNorm : ‖(-r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hrClosed : (r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hrNorm]
    linarith
  have hnegClosed : (-r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hnegNorm]
    linarith
  have hzeroClosed : (0 : ℂ) ∈ closedBall (0 : ℂ) R :=
    mem_closedBall_self hR.le
  have hfneg : shiftedChiFourXi (-r : ℂ) ≠ 0 := by
    simpa [shiftedChiFourXi_neg] using hf
  rw [log_norm_shiftedCanonicalProduct_eq_sum hrClosed hf,
    log_norm_shiftedCanonicalProduct_eq_sum hnegClosed hfneg,
    log_norm_shiftedCanonicalProduct_eq_sum hzeroClosed shiftedChiFourXi_zero_ne]
  have hsumRewrite :
      (∑ u ∈ S,
          Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖) +
          (∑ u ∈ S,
            Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖) -
          2 * (∑ u ∈ S,
            Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖) =
        ∑ u ∈ S,
          (Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖ +
            Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖ -
            2 * Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
  change
    (∑ u ∈ S,
        Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖) +
        (∑ u ∈ S,
          Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖) -
        2 * (∑ u ∈ S,
          Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖) ≤
      9 * B * r
  rw [hsumRewrite]
  have hbase (u : ℂ) (hu : u ∈ S) :
      2 * Real.log ‖Complex.canonicalFactor R u 0‖ -
          Real.log ‖Complex.canonicalFactor R u (r : ℂ)‖ -
          Real.log ‖Complex.canonicalFactor R u (-r : ℂ)‖ ≤
        Real.log (1 + r ^ 2 / ‖u‖ ^ 2) +
          2 * (‖u‖ ^ 2 * r ^ 2 / R ^ 4) := by
    have hdiv : shiftedZeroDivisor R u ≠ 0 :=
      (shiftedZeroDivisor_support_finite R).mem_toFinset.mp hu
    have huBall := (shiftedZeroDivisor R).supportWithinDomain hdiv
    have hu0 : u ≠ 0 := by
      intro h
      subst u
      exact hdiv (shiftedZeroDivisor_zero hR)
    have hru : (r : ℂ) ≠ u := by
      intro h
      subst u
      exact hdiv (shiftedZeroDivisor_eq_zero_of_ne_zero hrClosed hf)
    have hnegu : (-r : ℂ) ≠ u := by
      intro h
      subst u
      exact hdiv (shiftedZeroDivisor_eq_zero_of_ne_zero hnegClosed hfneg)
    exact canonicalFactor_log_pair_le hR hr0 hrHalf huBall hu0 hru hnegu
  have hterm (u : ℂ) (hu : u ∈ S) :
      Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖ +
          Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖ -
          2 * Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖ ≤
        (shiftedZeroDivisor R u : ℝ) *
          (Real.log (1 + r ^ 2 / ‖u‖ ^ 2) +
            2 * (‖u‖ ^ 2 * r ^ 2 / R ^ 4)) := by
    have hm : 0 ≤ (shiftedZeroDivisor R u : ℝ) := by
      exact_mod_cast shiftedZeroDivisor_nonneg R u
    have hmul := mul_le_mul_of_nonneg_left (hbase u hu) hm
    simp only [norm_zpow, Real.log_zpow, Int.cast_neg] at ⊢
    ring_nf at hmul ⊢
    exact hmul
  calc
    ∑ u ∈ S,
        (Real.log ‖Complex.canonicalFactor R u (r : ℂ) ^ (-shiftedZeroDivisor R u)‖ +
          Real.log ‖Complex.canonicalFactor R u (-r : ℂ) ^ (-shiftedZeroDivisor R u)‖ -
          2 * Real.log ‖Complex.canonicalFactor R u 0 ^ (-shiftedZeroDivisor R u)‖) ≤
        ∑ u ∈ S, (shiftedZeroDivisor R u : ℝ) *
          (Real.log (1 + r ^ 2 / ‖u‖ ^ 2) +
            2 * (‖u‖ ^ 2 * r ^ 2 / R ^ 4)) :=
      Finset.sum_le_sum fun u hu => hterm u hu
    _ = (∑ u ∈ S, (shiftedZeroDivisor R u : ℝ) *
          Real.log (1 + r ^ 2 / ‖u‖ ^ 2)) +
        ∑ u ∈ S, (shiftedZeroDivisor R u : ℝ) *
          (2 * (‖u‖ ^ 2 * r ^ 2 / R ^ 4)) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro u hu
      ring
    _ ≤ (7 * B * r) + 2 * B * r := by
      apply add_le_add
      · have hinnerLog :
            ∑ u ∈ I, (shiftedZeroDivisor R u : ℝ) * Real.log (2 * r / ‖u‖) ≤
              B * (2 * r) := by
          apply weighted_log_sum_le I norm
            (fun u => (shiftedZeroDivisor R u : ℝ)) (R := 2 * r)
          · positivity
          · intro u hu
            have hdiv : shiftedZeroDivisor R u ≠ 0 :=
              (shiftedZeroDivisor_support_finite R).mem_toFinset.mp
                (Finset.mem_filter.mp hu).1
            exact norm_pos_iff.mpr <| by
              intro h
              subst u
              exact hdiv (shiftedZeroDivisor_zero hR)
          · intro u hu
            exact (Finset.mem_filter.mp hu).2.le.trans (by linarith)
          · intro t ht
            let U := S.filter fun u => ‖u‖ < t
            have hsub : I.filter (fun u => ‖u‖ < t) ⊆ U := by
              intro u hu
              have hu' := Finset.mem_filter.mp hu
              have huI := Finset.mem_filter.mp hu'.1
              exact Finset.mem_filter.mpr ⟨huI.1, hu'.2⟩
            calc
              ∑ u ∈ I with ‖u‖ < t, (shiftedZeroDivisor R u : ℝ) ≤
                  ∑ u ∈ U, (shiftedZeroDivisor R u : ℝ) := by
                apply Finset.sum_le_sum_of_subset_of_nonneg hsub
                intro u huU huI
                exact_mod_cast shiftedZeroDivisor_nonneg R u
              _ = shiftedZeroCount t := by
                dsimp [U, S]
                exact sum_shiftedZeroDivisor_filter_norm_lt
                  (ht.2.trans h2rR)
              _ ≤ B * t := hcount t ht.1
        have hinner :
            ∑ u ∈ I, (shiftedZeroDivisor R u : ℝ) *
                Real.log (1 + r ^ 2 / ‖u‖ ^ 2) ≤ 4 * B * r := by
          calc
            ∑ u ∈ I, (shiftedZeroDivisor R u : ℝ) *
                Real.log (1 + r ^ 2 / ‖u‖ ^ 2) ≤
                ∑ u ∈ I, (shiftedZeroDivisor R u : ℝ) *
                  (2 * Real.log (2 * r / ‖u‖)) := by
              apply Finset.sum_le_sum
              intro u hu
              have hm : 0 ≤ (shiftedZeroDivisor R u : ℝ) := by
                exact_mod_cast shiftedZeroDivisor_nonneg R u
              apply mul_le_mul_of_nonneg_left _ hm
              have huPos : 0 < ‖u‖ := by
                have hdiv : shiftedZeroDivisor R u ≠ 0 :=
                  (shiftedZeroDivisor_support_finite R).mem_toFinset.mp
                    (Finset.mem_filter.mp hu).1
                exact norm_pos_iff.mpr <| by
                  intro h
                  subst u
                  exact hdiv (shiftedZeroDivisor_zero hR)
              exact log_one_add_sq_div_le_two_log huPos hr
                (Finset.mem_filter.mp hu).2.le
            _ = 2 * ∑ u ∈ I, (shiftedZeroDivisor R u : ℝ) *
                  Real.log (2 * r / ‖u‖) := by
              rw [Finset.mul_sum]
              apply Finset.sum_congr rfl
              intro u hu
              ring
            _ ≤ 2 * (B * (2 * r)) := mul_le_mul_of_nonneg_left hinnerLog (by norm_num)
            _ = 4 * B * r := by ring
        have houter :
            ∑ u ∈ O, (shiftedZeroDivisor R u : ℝ) *
                Real.log (1 + r ^ 2 / ‖u‖ ^ 2) ≤ 3 * B * r := by
          calc
            ∑ u ∈ O, (shiftedZeroDivisor R u : ℝ) *
                Real.log (1 + r ^ 2 / ‖u‖ ^ 2) ≤
                ∑ u ∈ O, (shiftedZeroDivisor R u : ℝ) *
                  (r ^ 2 / ‖u‖ ^ 2) := by
              apply Finset.sum_le_sum
              intro u hu
              have hm : 0 ≤ (shiftedZeroDivisor R u : ℝ) := by
                exact_mod_cast shiftedZeroDivisor_nonneg R u
              apply mul_le_mul_of_nonneg_left _ hm
              have hxPos : 0 < 1 + r ^ 2 / ‖u‖ ^ 2 := by positivity
              simpa using Real.log_le_sub_one_of_pos hxPos
            _ ≤ 3 * B * r := by
              dsimp [O, S]
              exact shiftedInvSqTail_le_of_count_bound hr (by linarith) hcount
        have hpartition : S = I ∪ O := by
          ext u
          simp only [I, O, Finset.mem_union, Finset.mem_filter]
          constructor
          · intro hu
            by_cases hur : ‖u‖ < r
            · exact Or.inl ⟨hu, hur⟩
            · exact Or.inr ⟨hu, le_of_not_gt hur⟩
          · exact fun hu => hu.elim And.left And.left
        have hdisjoint : Disjoint I O := by
          rw [Finset.disjoint_left]
          intro u huI huO
          exact (not_lt_of_ge (Finset.mem_filter.mp huO).2)
            (Finset.mem_filter.mp huI).2
        rw [hpartition, Finset.sum_union hdisjoint]
        calc
          (∑ u ∈ I, (shiftedZeroDivisor R u : ℝ) *
              Real.log (1 + r ^ 2 / ‖u‖ ^ 2)) +
              ∑ u ∈ O, (shiftedZeroDivisor R u : ℝ) *
                Real.log (1 + r ^ 2 / ‖u‖ ^ 2) ≤
              4 * B * r + 3 * B * r := add_le_add hinner houter
          _ = 7 * B * r := by ring
      · have hcountR := hcount R hR
        have hsumCount :
            ∑ u ∈ S, (shiftedZeroDivisor R u : ℝ) = shiftedZeroCount R := by
          dsimp [S]
          exact sum_shiftedZeroDivisor_eq_count R
        have hnorm : ∀ u ∈ S, ‖u‖ ≤ R := by
          intro u hu
          have hdiv : shiftedZeroDivisor R u ≠ 0 :=
            (shiftedZeroDivisor_support_finite R).mem_toFinset.mp hu
          have huBall := (shiftedZeroDivisor R).supportWithinDomain hdiv
          have huNorm : ‖u‖ < R := by
            simpa [mem_ball_iff_norm] using huBall
          exact huNorm.le
        calc
          ∑ u ∈ S, (shiftedZeroDivisor R u : ℝ) *
              (2 * (‖u‖ ^ 2 * r ^ 2 / R ^ 4)) ≤
              ∑ u ∈ S, (shiftedZeroDivisor R u : ℝ) *
                (2 * (R ^ 2 * r ^ 2 / R ^ 4)) := by
            apply Finset.sum_le_sum
            intro u hu
            have hm : 0 ≤ (shiftedZeroDivisor R u : ℝ) := by
              exact_mod_cast shiftedZeroDivisor_nonneg R u
            apply mul_le_mul_of_nonneg_left _ hm
            gcongr
            exact hnorm u hu
          _ = (∑ u ∈ S, (shiftedZeroDivisor R u : ℝ)) *
                (2 * (R ^ 2 * r ^ 2 / R ^ 4)) := by rw [Finset.sum_mul]
          _ ≤ (B * R) * (2 * (R ^ 2 * r ^ 2 / R ^ 4)) := by
            apply mul_le_mul_of_nonneg_right
            · rw [hsumCount]
              exact hcountR
            · positivity
          _ ≤ 2 * B * r := by
            have hrR : r ≤ R := by linarith
            have hBR : 0 ≤ B * r := by positivity
            field_simp [hR.ne']
            nlinarith
    _ = 9 * B * r := by ring

lemma log_norm_shiftedChiFourXi_pair_le_count
    {B R r : ℝ} {g : ℂ → ℂ} (hR : 0 < R) (hr : 0 < r) (h2rR : 2 * r < R)
    (hg : Complex.CanonicalDecomp shiftedChiFourXi g R)
    (hfree : ∀ z ∈ sphere (0 : ℂ) R, shiftedChiFourXi z ≠ 0)
    (hf : shiftedChiFourXi (r : ℂ) ≠ 0)
    (hcount : ∀ t : ℝ, 0 < t → shiftedZeroCount t ≤ B * t) :
    Real.log ‖shiftedChiFourXi (r : ℂ)‖ +
        Real.log ‖shiftedChiFourXi (-r : ℂ)‖ -
        2 * Real.log ‖shiftedChiFourXi 0‖ ≤
      9 * B * r +
        16 * (r / R) ^ 2 *
          (Real.log (shiftedGrowthMajorant R) - Real.log ‖shiftedChiFourXi 0‖) := by
  have hr0 : 0 ≤ r := hr.le
  have hrHalf : r ≤ R / 2 := by linarith
  have hrLe : r ≤ R := by linarith
  have hrNorm : ‖(r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hnegNorm : ‖(-r : ℂ)‖ = r := by
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr]
  have hrClosed : (r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hrNorm]
    exact hrLe
  have hnegClosed : (-r : ℂ) ∈ closedBall (0 : ℂ) R := by
    rw [mem_closedBall_iff_norm, sub_zero, hnegNorm]
    exact hrLe
  have hzeroClosed : (0 : ℂ) ∈ closedBall (0 : ℂ) R :=
    mem_closedBall_self hR.le
  have hfneg : shiftedChiFourXi (-r : ℂ) ≠ 0 := by
    simpa [shiftedChiFourXi_neg] using hf
  have hgNe := shiftedCanonicalDecomp_ne_zero_closedBall hR hg hfree
  have hEqPlus := shiftedCanonicalDecomp_eq_of_ne_zero hR hg hrClosed hf
  have hEqNeg := shiftedCanonicalDecomp_eq_of_ne_zero hR hg hnegClosed hfneg
  have hEqZero := shiftedCanonicalDecomp_eq_of_ne_zero hR hg hzeroClosed
    shiftedChiFourXi_zero_ne
  have hPPlus := shiftedCanonicalProduct_ne_zero_of_ne_zero hrClosed hf
  have hPNeg := shiftedCanonicalProduct_ne_zero_of_ne_zero hnegClosed hfneg
  have hPZero := shiftedCanonicalProduct_ne_zero_of_ne_zero hzeroClosed
    shiftedChiFourXi_zero_ne
  have hsplitPlus :
      Real.log ‖shiftedChiFourXi (r : ℂ)‖ =
        Real.log ‖shiftedCanonicalProduct R (r : ℂ)‖ + Real.log ‖g (r : ℂ)‖ := by
    rw [hEqPlus, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hPPlus)
        (norm_ne_zero_iff.mpr (hgNe (r : ℂ) hrClosed))]
  have hsplitNeg :
      Real.log ‖shiftedChiFourXi (-r : ℂ)‖ =
        Real.log ‖shiftedCanonicalProduct R (-r : ℂ)‖ + Real.log ‖g (-r : ℂ)‖ := by
    rw [hEqNeg, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hPNeg)
        (norm_ne_zero_iff.mpr (hgNe (-r : ℂ) hnegClosed))]
  have hsplitZero :
      Real.log ‖shiftedChiFourXi 0‖ =
        Real.log ‖shiftedCanonicalProduct R 0‖ + Real.log ‖g 0‖ := by
    rw [hEqZero, norm_mul,
      Real.log_mul (norm_ne_zero_iff.mpr hPZero)
        (norm_ne_zero_iff.mpr (hgNe 0 hzeroClosed))]
  have hP := log_norm_shiftedCanonicalProduct_pair_le_count hR hr h2rR hf hcount
  have hgLog := canonicalRemainder_log_pair_le hR hr0 hrHalf hg hfree
  rw [hsplitZero] at hgLog
  rw [hsplitPlus, hsplitNeg, hsplitZero]
  ring_nf at hP hgLog ⊢
  linarith

lemma norm_shiftedChiFourXi_le_exp_of_count_bound
    {B r : ℝ} (hr : 1 ≤ r)
    (hcount : ∀ t : ℝ, 0 < t → shiftedZeroCount t ≤ B * t)
    (hf : shiftedChiFourXi (r : ℂ) ≠ 0) :
    ‖shiftedChiFourXi (r : ℂ)‖ ≤
      Real.exp (9 / 2 * B * r + zeroMassErrorConstant / 2 +
        Real.log ‖shiftedChiFourXi 0‖) := by
  obtain ⟨R, hRint, hfree⟩ :=
    exists_shiftedChiFourXi_zero_free_radius ((r + 1) ^ 8)
  have hRpos : 0 < R :=
    lt_of_lt_of_le (by positivity : 0 < (r + 1) ^ 8) hRint.1.le
  have ht : 1 ≤ r + 1 := by linarith
  have ht2le8 : (r + 1) ^ 2 ≤ (r + 1) ^ 8 :=
    pow_le_pow_right₀ ht (by norm_num)
  have h2r : 2 * r ≤ (r + 1) ^ 2 := by nlinarith
  have h2rR : 2 * r < R := (h2r.trans ht2le8).trans_lt hRint.1
  obtain ⟨g, hg⟩ := exists_shiftedCanonicalDecomp R
  have hpair := log_norm_shiftedChiFourXi_pair_le_count hRpos
    (zero_lt_one.trans_le hr) h2rR hg hfree hf hcount
  have heven : shiftedChiFourXi (-r : ℂ) = shiftedChiFourXi (r : ℂ) := by
    simpa using shiftedChiFourXi_neg (r : ℂ)
  rw [heven] at hpair
  have herror := poisson_error_le_zeroMassErrorConstant hr hRint
  have hlog : Real.log ‖shiftedChiFourXi (r : ℂ)‖ ≤
      9 / 2 * B * r + zeroMassErrorConstant / 2 +
        Real.log ‖shiftedChiFourXi 0‖ := by
    linarith
  have hnormPos : 0 < ‖shiftedChiFourXi (r : ℂ)‖ := norm_pos_iff.mpr hf
  rw [← Real.exp_log hnormPos]
  exact Real.exp_le_exp.mpr hlog

theorem shiftedZeroCount_div_unbounded (B : ℝ) :
    ∃ R : ℝ, 0 < R ∧ B * R < shiftedZeroCount R := by
  by_contra hbounded
  push Not at hbounded
  have hcount : ∀ t : ℝ, 0 < t → shiftedZeroCount t ≤ B * t := by
    intro t ht
    exact hbounded t ht
  let rate : ℝ := 9 * B
  let offset : ℝ := 9 / 4 * B + zeroMassErrorConstant / 2 +
    Real.log ‖shiftedChiFourXi 0‖
  obtain ⟨A, hA⟩ := exists_nat_gt (Real.exp offset)
  obtain ⟨C, hC⟩ := exists_nat_gt (Real.exp rate)
  have hevent := Nat.eventually_mul_pow_lt_factorial_sub (4 * A) C 0
  obtain ⟨N, hN⟩ := eventually_atTop.mp hevent
  let n := max N 1
  have hnN : N ≤ n := le_max_left N 1
  have hnOne : 1 ≤ n := le_max_right N 1
  have hfacNat : 4 * A * C ^ n < (n - 0).factorial := hN n hnN
  have hfac : (4 : ℝ) * A * C ^ n < (n.factorial : ℝ) := by
    exact_mod_cast (by simpa using hfacNat)
  have hlower := norm_shiftedChiFourXi_odd_lower n hnOne
  have hfacPos : 0 < (n.factorial : ℝ) / 4 := by positivity
  have hnormPos : 0 < ‖shiftedChiFourXi (shiftedOddPoint n)‖ :=
    hfacPos.trans_le hlower
  have hf : shiftedChiFourXi (shiftedOddPoint n) ≠ 0 :=
    norm_pos_iff.mp hnormPos
  have hrOne : 1 ≤ shiftedOddPoint n := by
    unfold shiftedOddPoint
    have hnCast : (1 : ℝ) ≤ n := by exact_mod_cast hnOne
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
    linarith
  have huRaw := norm_shiftedChiFourXi_le_exp_of_count_bound hrOne hcount hf
  have hu : ‖shiftedChiFourXi (shiftedOddPoint n)‖ ≤
      Real.exp (rate * n + offset) := by
    convert huRaw using 1
    congr 1
    dsimp [rate, offset, shiftedOddPoint]
    ring
  have hexpOffset : Real.exp offset ≤ (A : ℝ) := hA.le
  have hexpRate : Real.exp rate ≤ (C : ℝ) := hC.le
  have hexpUpper : Real.exp (rate * n + offset) ≤ (A : ℝ) * C ^ n := by
    rw [Real.exp_add, mul_comm rate (n : ℝ), Real.exp_nat_mul]
    rw [mul_comm (Real.exp rate ^ n) (Real.exp offset)]
    exact mul_le_mul hexpOffset (pow_le_pow_left₀ (Real.exp_nonneg _) hexpRate n)
      (by positivity) (by positivity)
  have hACstrict : (A : ℝ) * C ^ n < (n.factorial : ℝ) / 4 := by
    apply (lt_div_iff₀ (by norm_num : (0 : ℝ) < 4)).2
    simpa [mul_comm, mul_left_comm, mul_assoc] using hfac
  have hstrict : ‖shiftedChiFourXi (shiftedOddPoint n)‖ <
      (n.factorial : ℝ) / 4 :=
    hu.trans_lt (hexpUpper.trans_lt hACstrict)
  exact (not_lt_of_ge hlower) hstrict

lemma meromorphicOrderAt_shiftedChiFourXi_neg (u : ℂ) :
    meromorphicOrderAt shiftedChiFourXi (-u) =
      meromorphicOrderAt shiftedChiFourXi u := by
  have hcomp := meromorphicOrderAt_comp_of_deriv_ne_zero
    (f := shiftedChiFourXi) (g := fun z : ℂ => -z) (x := -u)
    (by fun_prop) (by simp)
  have heq : shiftedChiFourXi ∘ (fun z : ℂ => -z) = shiftedChiFourXi := by
    funext z
    exact shiftedChiFourXi_neg z
  rw [heq] at hcomp
  simpa using hcomp

lemma shiftedZeroDivisor_neg (R : ℝ) (u : ℂ) :
    shiftedZeroDivisor R (-u) = shiftedZeroDivisor R u := by
  by_cases hu : u ∈ ball (0 : ℂ) R
  · have hnegu : -u ∈ ball (0 : ℂ) R := by
      simpa [mem_ball_iff_norm] using hu
    unfold shiftedZeroDivisor
    rw [MeromorphicOn.divisor_apply
        (fun z _hz => meromorphic_shiftedChiFourXi z) hnegu,
      MeromorphicOn.divisor_apply
        (fun z _hz => meromorphic_shiftedChiFourXi z) hu,
      meromorphicOrderAt_shiftedChiFourXi_neg]
  · have hnegu : -u ∉ ball (0 : ℂ) R := by
      simpa [mem_ball_iff_norm] using hu
    have hzero (z : ℂ) (hz : z ∉ ball (0 : ℂ) R) :
        shiftedZeroDivisor R z = 0 := by
      by_contra h
      exact hz ((shiftedZeroDivisor R).supportWithinDomain h)
    rw [hzero u hu, hzero (-u) hnegu]

end Submission.ZeroDensity
