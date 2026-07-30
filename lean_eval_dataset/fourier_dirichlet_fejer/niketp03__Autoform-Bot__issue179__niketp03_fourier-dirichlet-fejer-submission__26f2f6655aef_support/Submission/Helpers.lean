/-
Copyright (c) Meta Platforms, Inc. and affiliates.
All rights reserved.

This source code is licensed under the license found in the
LICENSE file in the root directory of this source tree.
-/

import Mathlib
import ChallengeDeps

namespace Submission

noncomputable abbrev fourierPartialSum : (ℝ → ℂ) → ℕ → ℝ → ℂ :=
  _root_.LeanEval.Analysis.fourierPartialSum
noncomputable abbrev fourierCesaroMean : (ℝ → ℂ) → ℕ → ℝ → ℂ :=
  _root_.LeanEval.Analysis.fourierCesaroMean

/-!
This file is mechanically assembled and built from ATLAS-Lean:
- FourierAnalysis/FourierAnalysis/code/FourierSeries.lean

It imports only Mathlib and inlines the local FourierSeries dependency before
the Dirichlet/Fejer statements.
-/

open MeasureTheory MeasureTheory.Measure AddCircle
open scoped ENNReal NNReal Convolution

noncomputable section

namespace TorusConvolution

variable {T : ℝ} [hT : Fact (0 < T)]

abbrev mulℂ : ℂ →L[ℂ] ℂ →L[ℂ] ℂ := ContinuousLinearMap.mul ℂ ℂ

set_option maxHeartbeats 800000 in
theorem eLpNorm_convolution_le
    {f g : AddCircle T → ℂ}
    (hf : Integrable f haarAddCircle) (hg : Integrable g haarAddCircle) :
    eLpNorm (f ⋆[mulℂ, haarAddCircle] g) 1 haarAddCircle ≤
    eLpNorm f 1 haarAddCircle * eLpNorm g 1 haarAddCircle := by

  simp only [eLpNorm_one_eq_lintegral_enorm]
  show ∫⁻ x, ‖(f ⋆[mulℂ, haarAddCircle] g) x‖ₑ ∂haarAddCircle ≤ _


  calc ∫⁻ x, ‖(f ⋆[mulℂ, haarAddCircle] g) x‖ₑ ∂haarAddCircle

      ≤ ∫⁻ x, (∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂haarAddCircle) ∂haarAddCircle := by
        gcongr with x
        calc ‖(f ⋆[mulℂ, haarAddCircle] g) x‖ₑ
            = ‖∫ t, f t * g (x - t) ∂haarAddCircle‖ₑ := by rfl
          _ ≤ ∫⁻ t, ‖f t * g (x - t)‖ₑ ∂haarAddCircle :=
              enorm_integral_le_lintegral_enorm _
          _ ≤ ∫⁻ t, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂haarAddCircle := by
              gcongr with t
              simp only [enorm_eq_nnnorm]
              exact_mod_cast nnnorm_mul_le (f t) (g (x - t))

    _ = ∫⁻ t, (∫⁻ x, ‖f t‖ₑ * ‖g (x - t)‖ₑ ∂haarAddCircle) ∂haarAddCircle := by
        rw [lintegral_lintegral_swap]

        exact ((hf.aestronglyMeasurable.enorm).comp_quasiMeasurePreserving
          quasiMeasurePreserving_snd).mul
          ((hg.aestronglyMeasurable.enorm).comp_quasiMeasurePreserving
            (quasiMeasurePreserving_sub_of_right_invariant haarAddCircle haarAddCircle))

    _ = ∫⁻ t, ‖f t‖ₑ * (∫⁻ x, ‖g (x - t)‖ₑ ∂haarAddCircle) ∂haarAddCircle := by
        congr 1; ext t
        rw [lintegral_const_mul']
        simp [enorm_eq_nnnorm, ENNReal.coe_ne_top]

    _ = ∫⁻ t, ‖f t‖ₑ * (∫⁻ x, ‖g x‖ₑ ∂haarAddCircle) ∂haarAddCircle := by
        congr 1; ext t; congr 1
        exact lintegral_sub_right_eq_self (fun x => ‖g x‖ₑ) t

    _ = (∫⁻ t, ‖f t‖ₑ ∂haarAddCircle) * (∫⁻ x, ‖g x‖ₑ ∂haarAddCircle) := by
        rw [lintegral_mul_const']
        simp_rw [enorm_eq_nnnorm]
        exact hg.2.ne

end TorusConvolution

end

open MeasureTheory Filter Topology Set intervalIntegral Real

noncomputable section

namespace ApproximateIdentity

def periodicConvolution (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y

lemma periodic_continuous_uniformContinuous {f : ℝ → ℝ} {p : ℝ} (hp : 0 < p)
    (hf : Continuous f) (hper : Function.Periodic f p) : UniformContinuous f := by
  rw [Metric.uniformContinuous_iff]
  intro ε hε
  have hcomp : IsCompact (Icc (-p) (2 * p)) := isCompact_Icc
  have huc := hcomp.uniformContinuousOn_of_continuous hf.continuousOn
  rw [Metric.uniformContinuousOn_iff] at huc
  obtain ⟨δ₀, hδ₀_pos, hδ₀⟩ := huc ε hε
  use min δ₀ (p / 2)
  refine ⟨lt_min hδ₀_pos (by linarith), ?_⟩
  intro a b hab
  set n₀ := ⌊a / p⌋
  have hfa : f a = f (a - n₀ • p) := (hper.sub_zsmul_eq n₀).symm
  have hfb : f b = f (b - n₀ • p) := (hper.sub_zsmul_eq n₀).symm
  rw [dist_eq_norm, hfa, hfb, ← dist_eq_norm]
  set a' := a - n₀ • p
  set b' := b - n₀ • p
  have ha'_lb : 0 ≤ a' := by
    simp only [a', zsmul_eq_mul]
    linarith [show (⌊a / p⌋ : ℝ) * p ≤ a from by rw [← le_div_iff₀ hp]; exact Int.floor_le _]
  have ha'_ub : a' < p := by
    simp only [a', zsmul_eq_mul]
    linarith [show a < ((⌊a / p⌋ : ℝ) + 1) * p from by
      rw [← div_lt_iff₀ hp]; exact Int.lt_floor_add_one _]
  have hdist_eq : dist a' b' = dist a b := by simp only [a', b', dist_sub_right]
  have hdist_small : dist a' b' < p / 2 := by
    rw [hdist_eq]; exact lt_of_lt_of_le hab (min_le_right _ _)
  have hab'_range := abs_lt.mp (by rwa [Real.dist_eq] at hdist_small)
  exact hδ₀ a' (by constructor <;> linarith) b'
    (by constructor <;> linarith [hab'_range.1, hab'_range.2])
    (by rw [hdist_eq]; exact lt_of_lt_of_le hab (min_le_left _ _))

lemma convolution_sub_eq (f K : ℝ → ℝ) (x : ℝ)
    (hK : IntervalIntegrable K volume (-π) π)
    (hfK : IntervalIntegrable (fun y => f (x - y) * K y) volume (-π) π)
    (hnorm : (1 / (2 * π)) * ∫ y in (-π)..π, K y = 1) :
    periodicConvolution f K x - f x =
      (1 / (2 * π)) * ∫ y in (-π)..π, (f (x - y) - f x) * K y := by
  unfold periodicConvolution
  have hint_K_val : ∫ y in (-π)..π, K y = 2 * π := by
    have : (1 : ℝ) / (2 * π) ≠ 0 := by positivity
    field_simp at hnorm; linarith
  have key : ∫ y in (-π)..π, (f (x - y) - f x) * K y =
      (∫ y in (-π)..π, f (x - y) * K y) - f x * (∫ y in (-π)..π, K y) := by
    rw [show (fun y => (f (x - y) - f x) * K y) = (fun y => f (x - y) * K y - f x * K y) from
      by ext y; ring, integral_sub hfK (hK.const_mul (f x)),
      intervalIntegral.integral_const_mul]
  rw [key, hint_K_val]; field_simp

lemma integral_subinterval_le_of_nonneg (g : ℝ → ℝ) (a b c d : ℝ)
    (hab : a ≤ b) (hbc : b ≤ c) (hcd : c ≤ d)
    (hg_intble : IntervalIntegrable g volume a d)
    (hg_nonneg : ∀ x ∈ Icc a d, 0 ≤ g x) :
    ∫ x in b..c, g x ≤ ∫ x in a..d, g x := by
  have had : a ≤ d := le_trans hab (le_trans hbc hcd)
  have hab_intble : IntervalIntegrable g volume a b :=
    hg_intble.mono_set (by rw [uIcc_of_le hab, uIcc_of_le had]; exact Icc_subset_Icc le_rfl (le_trans hbc hcd))
  have hbc_intble : IntervalIntegrable g volume b c :=
    hg_intble.mono_set (by rw [uIcc_of_le hbc, uIcc_of_le had]; exact Icc_subset_Icc hab hcd)
  have hcd_intble : IntervalIntegrable g volume c d :=
    hg_intble.mono_set (by rw [uIcc_of_le hcd, uIcc_of_le had]; exact Icc_subset_Icc (le_trans hab hbc) le_rfl)
  have h3 := integral_add_adjacent_intervals (hab_intble.trans hbc_intble) hcd_intble
  have h1 := integral_add_adjacent_intervals hab_intble hbc_intble
  have hab_nn : 0 ≤ ∫ x in a..b, g x :=
    intervalIntegral.integral_nonneg hab (fun u hu => hg_nonneg u ⟨hu.1, le_trans hu.2 (le_trans hbc hcd)⟩)
  have hcd_nn : 0 ≤ ∫ x in c..d, g x :=
    intervalIntegral.integral_nonneg hcd (fun u hu => hg_nonneg u ⟨le_trans hab (le_trans hbc hu.1), hu.2⟩)
  linarith

theorem approximate_identity_lemma
    (f : ℝ → ℝ) (K : ℕ → ℝ → ℝ)
    (hf_cont : Continuous f)
    (hf_periodic : Function.Periodic f (2 * π))
    (hK_intble : ∀ N, IntervalIntegrable (K N) volume (-π) π)
    (hfK_intble : ∀ N x, IntervalIntegrable (fun y => f (x - y) * K N y) volume (-π) π)
    (habs_K_intble : ∀ N, IntervalIntegrable (fun y => |K N y|) volume (-π) π)
    (hdiff_K_intble : ∀ N x,
      IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) π)
    (h_normalize : ∀ N, (1 / (2 * π)) * ∫ x in (-π)..π, K N x = 1)
    (h_bound : ∃ M : ℝ, ∀ N, ∫ x in (-π)..π, |K N x| ≤ M)
    (h_concentrate : ∀ δ, 0 < δ → δ ≤ π →
      Filter.Tendsto (fun N => (∫ x in (-π)..(-δ), |K N x|) + ∫ x in δ..π, |K N x|)
        Filter.atTop (nhds 0)) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℝ,
      |f x - periodicConvolution f (K N) x| ≤ ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := h_bound
  have hM_nonneg : 0 ≤ M := le_trans
    (intervalIntegral.integral_nonneg (by linarith [pi_pos]) (fun u _ => abs_nonneg _)) (hM 0)
  have hf_uc := periodic_continuous_uniformContinuous (by positivity : (0 : ℝ) < 2 * π)
    hf_cont hf_periodic
  have hf_bdd : ∃ C : ℝ, 0 ≤ C ∧ ∀ z, |f z| ≤ C := by
    have hne : (Icc (0 : ℝ) (2 * π)).Nonempty := nonempty_Icc.mpr (by positivity)
    obtain ⟨x₀, _, hx₀_max⟩ :=
      isCompact_Icc.exists_isMaxOn hne hf_cont.abs.continuousOn
    refine ⟨|f x₀|, abs_nonneg _, fun z => ?_⟩
    set n := ⌊z / (2 * π)⌋
    rw [show f z = f (z - n • (2 * π)) from (hf_periodic.sub_zsmul_eq n).symm]
    apply hx₀_max
    simp only [zsmul_eq_mul]
    have h2pi_pos : (0 : ℝ) < 2 * π := by positivity
    have hlb : (⌊z / (2 * π)⌋ : ℝ) * (2 * π) ≤ z := by
      rw [← le_div_iff₀ h2pi_pos]; exact Int.floor_le _
    have hub : z < ((⌊z / (2 * π)⌋ : ℝ) + 1) * (2 * π) := by
      rw [← div_lt_iff₀ h2pi_pos]; exact Int.lt_floor_add_one _
    exact ⟨by linarith, by linarith⟩
  obtain ⟨C, hC_nonneg, hC⟩ := hf_bdd
  rw [Metric.uniformContinuous_iff] at hf_uc
  obtain ⟨δ, hδ_pos, hδ_uc⟩ := hf_uc (ε * π / (M + 1)) (by positivity)
  set δ' := min (δ / 2) π with hδ'_def
  have hδ'_pos : 0 < δ' := lt_min (by linarith) pi_pos
  have hδ'_le_π : δ' ≤ π := min_le_right _ _
  have hneg_π_le_neg_δ' : -π ≤ -δ' := by linarith
  have huc_bound : ∀ x y : ℝ, |y| ≤ δ' → |f (x - y) - f x| ≤ ε * π / (M + 1) := by
    intro x y hy
    exact le_of_lt (hδ_uc (by
      rw [dist_eq_norm, show (x - y) - x = -y from by ring, norm_neg, Real.norm_eq_abs]
      exact lt_of_le_of_lt hy (lt_of_le_of_lt (min_le_left _ _) (by linarith))))
  have h_conc_δ := h_concentrate δ' hδ'_pos hδ'_le_π
  rw [Metric.tendsto_atTop] at h_conc_δ
  obtain ⟨N₀, hN₀⟩ := h_conc_δ (ε * π / (2 * C + 1)) (by positivity)
  have htail : ∀ N ≥ N₀,
      (∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y| < ε * π / (2 * C + 1) := by
    intro N hN
    have h_dist := hN₀ N hN
    rw [Real.dist_eq, sub_zero] at h_dist
    rwa [abs_of_nonneg] at h_dist
    apply add_nonneg
    · exact intervalIntegral.integral_nonneg hneg_π_le_neg_δ' (fun u _ => abs_nonneg _)
    · exact intervalIntegral.integral_nonneg hδ'_le_π (fun u _ => abs_nonneg _)
  use N₀
  intro N hN x
  have h_eq := convolution_sub_eq f (K N) x (hK_intble N) (hfK_intble N x) (h_normalize N)
  rw [abs_sub_comm]
  rw [h_eq]
  rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / (2 * π))]
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]
  have hnorm_le := intervalIntegral.norm_integral_le_integral_norm (μ := volume) hpi_le
    (f := fun y => (f (x - y) - f x) * K N y)
  simp only [Real.norm_eq_abs] at hnorm_le
  have habs_sub : IntervalIntegrable (fun y => |K N y|) volume (-π) π := habs_K_intble N
  have hdiff_sub : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) π :=
    hdiff_K_intble N x
  have habs_sub_1 : IntervalIntegrable (fun y => |K N y|) volume (-π) (-δ') :=
    habs_sub.mono_set (by rw [uIcc_of_le hneg_π_le_neg_δ', uIcc_of_le hpi_le]; exact Icc_subset_Icc le_rfl (by linarith))
  have habs_sub_2 : IntervalIntegrable (fun y => |K N y|) volume (-δ') δ' :=
    habs_sub.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) hδ'_le_π)
  have habs_sub_3 : IntervalIntegrable (fun y => |K N y|) volume δ' π :=
    habs_sub.mono_set (by rw [uIcc_of_le hδ'_le_π, uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) le_rfl)
  have hdiff_sub_1 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-π) (-δ') :=
    hdiff_sub.mono_set (by rw [uIcc_of_le hneg_π_le_neg_δ', uIcc_of_le hpi_le]; exact Icc_subset_Icc le_rfl (by linarith))
  have hdiff_sub_2 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume (-δ') δ' :=
    hdiff_sub.mono_set (by rw [uIcc_of_le (by linarith), uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) hδ'_le_π)
  have hdiff_sub_3 : IntervalIntegrable (fun y => |f (x - y) - f x| * |K N y|) volume δ' π :=
    hdiff_sub.mono_set (by rw [uIcc_of_le hδ'_le_π, uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) le_rfl)
  have h_split : ∫ y in (-π)..π, |(f (x - y) - f x) * K N y| =
      (∫ y in (-π)..(-δ'), |(f (x - y) - f x) * K N y|)
      + (∫ y in (-δ')..δ', |(f (x - y) - f x) * K N y|)
      + ∫ y in δ'..π, |(f (x - y) - f x) * K N y| := by
    have h_abs_eq : (fun y => |(f (x - y) - f x) * K N y|) = (fun y => |f (x - y) - f x| * |K N y|) :=
      by ext y; exact abs_mul _ _
    have h_abs_intble : IntervalIntegrable (fun y => |(f (x - y) - f x) * K N y|) volume (-π) π := by
      rw [h_abs_eq]; exact hdiff_K_intble N x
    have h_abs_intble_1 := h_abs_intble.mono_set (by rw [uIcc_of_le hneg_π_le_neg_δ', uIcc_of_le hpi_le]; exact Icc_subset_Icc le_rfl (by linarith))
    have h_abs_intble_2 := h_abs_intble.mono_set (by rw [uIcc_of_le (by linarith : -δ' ≤ δ'), uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) hδ'_le_π)
    have h_abs_intble_3 := h_abs_intble.mono_set (by rw [uIcc_of_le hδ'_le_π, uIcc_of_le hpi_le]; exact Icc_subset_Icc (by linarith) le_rfl)
    have h12 := integral_add_adjacent_intervals h_abs_intble_1 h_abs_intble_2
    have h123 := integral_add_adjacent_intervals (h_abs_intble_1.trans h_abs_intble_2) h_abs_intble_3
    rw [← h123, ← h12]
  have h_near : ∫ y in (-δ')..δ', |f (x - y) - f x| * |K N y| ≤
      ε * π / (M + 1) * ∫ y in (-δ')..δ', |K N y| := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on (by linarith) hdiff_sub_2 (habs_sub_2.const_mul _)
    intro y hy
    exact mul_le_mul_of_nonneg_right
      (huc_bound x y (by rw [abs_le]; exact ⟨by linarith [hy.1], by linarith [hy.2]⟩))
      (abs_nonneg _)
  have h_near_K_le : ∫ y in (-δ')..δ', |K N y| ≤ M :=
    le_trans (integral_subinterval_le_of_nonneg _ _ _ _ _
      hneg_π_le_neg_δ' (by linarith) hδ'_le_π (habs_K_intble N)
      (fun y _ => abs_nonneg _)) (hM N)
  have h_far1 : ∫ y in (-π)..(-δ'), |f (x - y) - f x| * |K N y| ≤
      2 * C * (∫ y in (-π)..(-δ'), |K N y|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hneg_π_le_neg_δ' hdiff_sub_1 (habs_sub_1.const_mul _)
    intro y _
    exact mul_le_mul_of_nonneg_right
      (by calc |f (x - y) - f x| ≤ |f (x - y)| + |f x| := abs_sub _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring) (abs_nonneg _)
  have h_far2 : ∫ y in δ'..π, |f (x - y) - f x| * |K N y| ≤
      2 * C * (∫ y in δ'..π, |K N y|) := by
    rw [← intervalIntegral.integral_const_mul]
    apply integral_mono_on hδ'_le_π hdiff_sub_3 (habs_sub_3.const_mul _)
    intro y _
    exact mul_le_mul_of_nonneg_right
      (by calc |f (x - y) - f x| ≤ |f (x - y)| + |f x| := abs_sub _ _
          _ ≤ C + C := add_le_add (hC _) (hC _)
          _ = 2 * C := by ring) (abs_nonneg _)
  have htail_N := htail N hN
  have htail_bound : 2 * C * ((∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y|) ≤
      2 * C * (ε * π / (2 * C + 1)) :=
    mul_le_mul_of_nonneg_left (le_of_lt htail_N) (by positivity)
  calc 1 / (2 * π) * |∫ y in (-π)..π, (f (x - y) - f x) * K N y|
      _ ≤ 1 / (2 * π) * ∫ y in (-π)..π, |(f (x - y) - f x) * K N y| := by
          exact mul_le_mul_of_nonneg_left hnorm_le (by positivity)
      _ = 1 / (2 * π) * ((∫ y in (-π)..(-δ'), |(f (x - y) - f x) * K N y|)
          + (∫ y in (-δ')..δ', |(f (x - y) - f x) * K N y|)
          + ∫ y in δ'..π, |(f (x - y) - f x) * K N y|) := by rw [h_split]
      _ = 1 / (2 * π) * ((∫ y in (-π)..(-δ'), |f (x - y) - f x| * |K N y|)
          + (∫ y in (-δ')..δ', |f (x - y) - f x| * |K N y|)
          + ∫ y in δ'..π, |f (x - y) - f x| * |K N y|) := by simp_rw [abs_mul]
      _ ≤ 1 / (2 * π) * (2 * C * (∫ y in (-π)..(-δ'), |K N y|)
          + ε * π / (M + 1) * M
          + 2 * C * (∫ y in δ'..π, |K N y|)) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          have h_near_bound := h_near.trans (mul_le_mul_of_nonneg_left h_near_K_le (by positivity))
          linarith [h_far1, h_far2, h_near_bound]
      _ = 1 / (2 * π) * (ε * π / (M + 1) * M
          + 2 * C * ((∫ y in (-π)..(-δ'), |K N y|) + ∫ y in δ'..π, |K N y|)) := by ring
      _ ≤ 1 / (2 * π) * (ε * π / (M + 1) * M
          + 2 * C * (ε * π / (2 * C + 1))) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          linarith [htail_bound]
      _ ≤ ε := by
          have h1 : 0 < M + 1 := by linarith
          have h2 : 0 < 2 * C + 1 := by linarith
          have key : ε * π / (M + 1) * M + 2 * C * (ε * π / (2 * C + 1)) =
              ε * π * (M / (M + 1) + 2 * C / (2 * C + 1)) := by field_simp
          rw [key]
          calc 1 / (2 * π) * (ε * π * (M / (M + 1) + 2 * C / (2 * C + 1)))
              ≤ 1 / (2 * π) * (ε * π * 2) := by
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                apply mul_le_mul_of_nonneg_left _ (by positivity)
                linarith [show M / (M + 1) ≤ 1 from by rw [div_le_one h1]; linarith,
                          show 2 * C / (2 * C + 1) ≤ 1 from by rw [div_le_one h2]; linarith]
            _ = ε := by field_simp

end ApproximateIdentity

end

open ContinuousMap Set

namespace TrigPolyDensity

variable {T : ℝ} [hT : Fact (0 < T)]

theorem trigPoly_dense_in_continuous :
    Dense ((Submodule.span ℂ (range (@fourier T))) : Set C(AddCircle T, ℂ)) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top]
  exact span_fourier_closure_eq_top

theorem trigPoly_approx_sup_norm (f : C(AddCircle T, ℂ)) {ε : ℝ} (hε : 0 < ε) :
    ∃ p ∈ (Submodule.span ℂ (range (@fourier T)) : Set C(AddCircle T, ℂ)),
      ‖f - p‖ < ε := by
  obtain ⟨p, hball, hmem⟩ := Metric.dense_iff.mp trigPoly_dense_in_continuous f ε hε
  exact ⟨p, hmem, by rwa [Metric.mem_ball, dist_eq_norm, norm_sub_rev] at hball⟩

end TrigPolyDensity

open MeasureTheory Filter Topology Set intervalIntegral Real

noncomputable section

namespace FejerL1Density

def periodicL1Norm (f : ℝ → ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ x in (-π)..π, |f x|

def periodicConvolution (f K : ℝ → ℝ) (x : ℝ) : ℝ :=
  (1 / (2 * π)) * ∫ y in (-π)..π, f (x - y) * K y

def fejerKernel (N : ℕ) (x : ℝ) : ℝ :=
  if N = 0 then 0
  else if sin (x / 2) = 0 then (N : ℝ)
  else (1 / N : ℝ) * (sin (N * x / 2) / sin (x / 2)) ^ 2

def fejerMean (f : ℝ → ℝ) (N : ℕ) : ℝ → ℝ :=
  periodicConvolution f (fejerKernel N)

def IsTrigPolynomial (p : ℝ → ℝ) : Prop :=
  ∃ (N : ℕ) (a b : ℕ → ℝ),
    ∀ x, p x = ∑ n ∈ Finset.range (N + 1),
      (a n * cos (n * x) + b n * sin (n * x))

lemma periodicL1Norm_nonneg (f : ℝ → ℝ) : 0 ≤ periodicL1Norm f := by
  unfold periodicL1Norm
  apply mul_nonneg (by positivity)
  exact integral_nonneg (by linarith [pi_pos]) (fun u _ => abs_nonneg _)

lemma periodicL1Norm_sub_comm (f g : ℝ → ℝ) :
    periodicL1Norm (fun x => f x - g x) = periodicL1Norm (fun x => g x - f x) := by
  unfold periodicL1Norm; congr 1; congr 1; ext x; exact abs_sub_comm (f x) (g x)


set_option maxHeartbeats 400000 in
lemma abs_sin_mul_le (n : ℕ) (θ : ℝ) : |sin (n * θ)| ≤ n * |sin θ| := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, add_mul, one_mul, sin_add]
    calc |sin (↑n * θ) * cos θ + cos (↑n * θ) * sin θ|
        ≤ |sin (↑n * θ)| * |cos θ| + |cos (↑n * θ)| * |sin θ| := by
          exact le_trans (abs_add_le _ _) (by rw [abs_mul, abs_mul])
      _ ≤ ↑n * |sin θ| * 1 + 1 * |sin θ| := by
          linarith [mul_le_mul ih (abs_cos_le_one θ) (abs_nonneg _)
                      (by positivity : 0 ≤ ↑n * |sin θ|),
                     mul_le_mul_of_nonneg_right (abs_cos_le_one (↑n * θ)) (abs_nonneg (sin θ))]
      _ = (↑n + 1) * |sin θ| := by ring


lemma fejerKernel_measurable (N : ℕ) : Measurable (fejerKernel N) := by
  unfold fejerKernel
  by_cases hN : N = 0
  · simp [hN]
  · simp only [hN, ↓reduceIte]
    apply Measurable.ite
    · exact (isClosed_eq (continuous_sin.comp (continuous_id.div_const 2))
        continuous_const).measurableSet
    · exact measurable_const
    · exact ((measurable_sin.comp ((measurable_const.mul measurable_id).div_const 2)).div
        (measurable_sin.comp (measurable_id.div_const 2))).pow measurable_const
        |>.const_mul _


lemma fejerKernel_nonneg_aux (N : ℕ) (x : ℝ) : 0 ≤ fejerKernel N x := by
  unfold fejerKernel
  split_ifs <;> [exact le_refl 0; exact Nat.cast_nonneg N;
    exact mul_nonneg (by positivity) (sq_nonneg _)]


set_option maxHeartbeats 400000 in
lemma fejerKernel_le_N (N : ℕ) (x : ℝ) : fejerKernel N x ≤ N := by
  unfold fejerKernel
  split_ifs with h0 hs
  · simp [h0]
  · exact le_refl _
  · have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero h0
    have key : |sin (↑N * x / 2) / sin (x / 2)| ≤ N := by
      rw [abs_div, div_le_iff₀ (abs_pos.mpr hs)]
      rw [show ↑N * x / 2 = ↑N * (x / 2) from by ring]
      exact abs_sin_mul_le N (x / 2)
    have hbound : (sin (↑N * x / 2) / sin (x / 2)) ^ 2 ≤ (↑N) ^ 2 := by
      rw [← sq_abs (sin (↑N * x / 2) / sin (x / 2))]
      exact pow_le_pow_left₀ (abs_nonneg _) key 2
    calc (1 / ↑N) * (sin (↑N * x / 2) / sin (x / 2)) ^ 2
        ≤ (1 / ↑N) * ↑N ^ 2 :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = ↑N := by field_simp


lemma fejerKernel_intervalIntegrable (N : ℕ) :
    IntervalIntegrable (fejerKernel N) volume (-π) π := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith [pi_pos])]
  apply Measure.integrableOn_of_bounded
  · exact measure_Ioc_lt_top.ne
  · exact (fejerKernel_measurable N).aestronglyMeasurable
  · filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux N x)]
    exact fejerKernel_le_N N x


lemma integral_cos_nat_mul_eq_zero (k : ℕ) (hk : k ≠ 0) :
    ∫ x in (-π)..π, cos (↑k * x) = 0 := by
  have hk_ne : (k : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hk
  have : (fun x => cos (↑k * x)) = (fun x => cos (x * ↑k)) := by ext x; ring
  rw [this, integral_comp_mul_right cos hk_ne, integral_cos, neg_mul, sin_neg]
  have h_sin : sin (π * ↑k) = 0 := by rw [mul_comm]; exact Real.sin_int_mul_pi k
  simp [h_sin]


lemma integral_const_mul_cos_eq_zero (c : ℝ) (k : ℕ) :
    ∫ x in (-π)..π, c * cos ((↑k + 1) * x) = 0 := by
  rw [show (fun x => c * cos ((↑k + 1) * x)) = (fun x => c * cos (↑(k + 1) * x)) from by
    ext x; push_cast; ring]
  rw [intervalIntegral.integral_const_mul]
  rw [integral_cos_nat_mul_eq_zero (k + 1) (by omega)]
  simp


lemma two_sin_half_mul_cos (k : ℕ) (x : ℝ) :
    2 * sin (x / 2) * cos (↑k * x) =
      sin ((2 * ↑k + 1) * (x / 2)) - sin ((2 * ↑k - 1) * (x / 2)) := by
  have h1 : sin ((2 * ↑k + 1) * (x / 2)) = sin (↑k * x + x / 2) := by ring_nf
  have h2 : sin ((2 * ↑k - 1) * (x / 2)) = sin (↑k * x - x / 2) := by ring_nf
  rw [h1, h2, sin_add, sin_sub]; ring


lemma dirichlet_identity (n : ℕ) (x : ℝ) :
    sin ((2 * ↑n + 1) * (x / 2)) =
      sin (x / 2) + 2 * sin (x / 2) * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x) := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, mul_add, ← add_assoc, ← ih]
    push_cast
    have h := two_sin_half_mul_cos (m + 1) x
    push_cast at h
    have key : (2 * (↑m + 1) - 1 : ℝ) = 2 * ↑m + 1 := by ring
    rw [key] at h
    linarith


lemma fejer_telescope (N : ℕ) (x : ℝ) :
    ∑ n ∈ Finset.range N, sin ((2 * ↑n + 1) * (x / 2)) * sin (x / 2) =
      sin (↑N * x / 2) ^ 2 := by
  induction N with
  | zero => simp
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]; push_cast
    have h_prod : 2 * sin ((2 * ↑m + 1) * (x / 2)) * sin (x / 2) =
        cos (↑m * x) - cos ((↑m + 1) * x) := by
      have := cos_sub_cos (↑m * x) ((↑m + 1) * x)
      have h1 : (↑m * x + (↑m + 1) * x) / 2 = (2 * ↑m + 1) * (x / 2) := by ring
      have h2 : (↑m * x - (↑m + 1) * x) / 2 = -(x / 2) := by ring
      rw [h1, h2, sin_neg] at this; linarith
    have h_cos1 : cos (↑m * x) = 1 - 2 * sin (↑m * x / 2) ^ 2 := by
      rw [show ↑m * x = 2 * (↑m * x / 2) from by ring, cos_two_mul, sin_sq]; ring
    have h_cos2 : cos ((↑m + 1) * x) = 1 - 2 * sin ((↑m + 1) * x / 2) ^ 2 := by
      rw [show (↑m + 1) * x = 2 * ((↑m + 1) * x / 2) from by ring, cos_two_mul, sin_sq]; ring
    nlinarith


lemma sin_half_ne_zero_of_ne_zero {x : ℝ} (hx : x ∈ Ioc (-π) π) (hx0 : x ≠ 0) :
    sin (x / 2) ≠ 0 := by
  intro h
  obtain ⟨n, hn⟩ := sin_eq_zero_iff.mp h
  have hx_eq : x = 2 * ↑n * π := by linarith
  have hpi := pi_pos
  have h1 : -(1 : ℤ) < 2 * n := by
    by_contra hc; push Not at hc
    have : (2 * (n : ℝ)) ≤ -1 := by exact_mod_cast hc
    nlinarith [hx.1]
  have h2 : 2 * n ≤ (1 : ℤ) := by
    by_contra hc; push Not at hc
    have : (2 : ℝ) ≤ 2 * (n : ℝ) := by exact_mod_cast hc
    nlinarith [hx.2]
  exact hx0 (by rw [hx_eq]; simp [show n = 0 from by omega])


lemma integral_dirichlet_sum (n : ℕ) :
    ∫ x in (-π)..π, (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) = 2 * π := by
  induction n with
  | zero => simp [intervalIntegral.integral_const, smul_eq_mul]; ring
  | succ m ih =>
    have h_rw : (fun x => 1 + 2 * ∑ k ∈ Finset.range (m + 1), cos ((↑k + 1) * x)) =
      (fun x => (1 + 2 * ∑ k ∈ Finset.range m, cos ((↑k + 1) * x)) +
        2 * cos ((↑m + 1) * x)) := by
      ext x; rw [Finset.sum_range_succ]; ring
    rw [h_rw, intervalIntegral.integral_add]
    · rw [integral_const_mul_cos_eq_zero 2 m, add_zero, ih]
    · exact (Continuous.add continuous_const (Continuous.mul continuous_const
        (continuous_finset_sum _ (fun k _ =>
          continuous_cos.comp (continuous_const.mul continuous_id))))).intervalIntegrable _ _
    · exact ((continuous_cos.comp
        (continuous_const.mul continuous_id)).intervalIntegrable _ _).const_mul _


lemma integral_fejer_sum_all (N : ℕ) :
    ∫ x in (-π)..π, ∑ n ∈ Finset.range N,
      (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) = ↑N * (2 * π) := by
  induction N with
  | zero => simp
  | succ m ih =>
    have h_rw : (fun x => ∑ n ∈ Finset.range (m + 1),
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x))) =
      fun x => (∑ n ∈ Finset.range m,
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x))) +
        (1 + 2 * ∑ k ∈ Finset.range m, cos ((↑k + 1) * x)) := by
      ext x; rw [Finset.sum_range_succ]
    have h_cts : ∀ n : ℕ, Continuous (fun x =>
        (1 : ℝ) + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) :=
      fun n => Continuous.add continuous_const (Continuous.mul continuous_const
        (continuous_finset_sum _ (fun k _ =>
          continuous_cos.comp (continuous_const.mul continuous_id))))
    rw [h_rw, intervalIntegral.integral_add
      ((continuous_finset_sum _ (fun n _ => h_cts n)).intervalIntegrable _ _)
      ((h_cts m).intervalIntegrable _ _)]
    rw [ih, integral_dirichlet_sum]; push_cast; ring


set_option maxHeartbeats 1600000 in
theorem fejerKernel_normalize (N : ℕ) (hN : N ≠ 0) :
    (1 / (2 * π)) * ∫ x in (-π)..π, fejerKernel N x = 1 := by
  have h_ae : ∀ᵐ (x : ℝ) ∂volume, x ∈ uIoc (-π) π →
      fejerKernel N x = (1 / (N : ℝ)) * ∑ n ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range n, cos ((↑k + 1) * x)) := by
    have h_ne : ∀ᵐ (x : ℝ) ∂volume, x ≠ 0 := by
      rw [Filter.eventually_iff, mem_ae_iff]
      show volume {x : ℝ | ¬x ≠ 0} = 0
      have : {x : ℝ | ¬x ≠ 0} = {(0 : ℝ)} := by ext x; simp
      rw [this]; exact Real.volume_singleton
    filter_upwards [h_ne] with x hx0 hx_mem
    have hx' : x ∈ Ioc (-π) π := by rwa [uIoc_of_le (by linarith [pi_pos])] at hx_mem
    have hsin : sin (x / 2) ≠ 0 := sin_half_ne_zero_of_ne_zero hx' hx0
    unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]
    congr 1
    rw [div_pow, ← fejer_telescope N x, Finset.sum_div]
    congr 1; ext n
    rw [dirichlet_identity n x]; field_simp
  rw [integral_congr_ae h_ae, intervalIntegral.integral_const_mul, integral_fejer_sum_all N]
  have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
  have hpi : π ≠ 0 := ne_of_gt pi_pos
  field_simp


noncomputable instance : Fact (0 < (2 * π : ℝ)) := ⟨by positivity⟩

set_option maxHeartbeats 3200000 in
theorem continuous_periodic_dense_L1
    (f : ℝ → ℝ) (_hf_periodic : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) :
    ∀ ε > 0, ∃ g : ℝ → ℝ,
      Continuous g ∧ Function.Periodic g (2 * π) ∧
      periodicL1Norm (fun x => f x - g x) ≤ ε := by
  intro ε hε
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]

  have hf_int : Integrable f (volume.restrict (Icc (-π) π)) := by
    rw [IntervalIntegrable] at hf_intble; change IntegrableOn f (Icc (-π) π) volume
    rw [integrableOn_Icc_iff_integrableOn_Ioc]; exact hf_intble.1

  obtain ⟨g₀, _, hg₀_close, hg₀_cont, _⟩ :=
    hf_int.exists_hasCompactSupport_integral_sub_le (show (0:ℝ) < ε * π by positivity)

  obtain ⟨M_pt, _, hM_pt⟩ := isCompact_Icc.exists_isMaxOn (nonempty_Icc.mpr hpi_le)
    ((continuous_abs.comp hg₀_cont).continuousOn : ContinuousOn (|g₀ ·|) (Icc (-π) π))
  set M := |g₀ M_pt|
  have hM_bound : ∀ x ∈ Icc (-π) π, |g₀ x| ≤ M := fun x hx => hM_pt hx

  set δ := min π (ε * π / (2 * (M + 1)))
  have hδ_pos : 0 < δ := by positivity
  let tent : ℝ → ℝ := fun x => max 0 (min 1 ((π - |x|) / δ))
  have tent_cont : Continuous tent :=
    continuous_const.max (continuous_const.min ((continuous_const.sub continuous_abs).div_const δ))

  set g₁ := fun x => g₀ x * tent x
  have hg₁_cont : Continuous g₁ := hg₀_cont.mul tent_cont
  have tent_zero_at : ∀ x : ℝ, π ≤ |x| → tent x = 0 :=
    fun x hx => max_eq_left_iff.mpr
      (min_le_of_right_le (div_nonpos_of_nonpos_of_nonneg (by linarith) hδ_pos.le))
  have hg₁_pi : g₁ π = 0 := by
    show g₀ π * tent π = 0
    rw [tent_zero_at π (by simp [abs_of_pos pi_pos])]; ring
  have hg₁_neg_pi : g₁ (-π) = 0 := by
    show g₀ (-π) * tent (-π) = 0
    rw [tent_zero_at (-π) (by simp [abs_of_pos pi_pos])]; ring
  have hg₁_match : g₁ (-π) = g₁ (-π + 2 * π) := by
    rw [show (-π : ℝ) + 2 * π = π from by ring, hg₁_neg_pi, hg₁_pi]

  let gc := AddCircle.liftIco (2 * π) (-π) g₁
  have hgc_cont : Continuous gc := AddCircle.liftIco_continuous hg₁_match
    (by rw [show (-π : ℝ) + 2 * π = π from by ring]; exact hg₁_cont.continuousOn)
  let g := fun x : ℝ => gc ((x : AddCircle (2 * π)))
  have hg_cont : Continuous g := hgc_cont.comp (AddCircle.continuous_mk' (2 * π))
  have hg_per : Function.Periodic g (2 * π) := fun x => by simp [g]

  have hg_eq : ∀ x ∈ Ico (-π) π, g x = g₁ x := fun x hx =>
    AddCircle.liftIco_coe_apply
      (show x ∈ Ico (-π) (-π + 2 * π) by rwa [show (-π : ℝ) + 2 * π = π from by ring])

  refine ⟨g, hg_cont, hg_per, ?_⟩
  simp only [periodicL1Norm]

  have hg₀_int : ∫ x in (-π)..π, |f x - g₀ x| ≤ ε * π := by
    have h1 : ∫ x in (-π)..π, |f x - g₀ x| = ∫ x in Icc (-π) π, ‖f x - g₀ x‖ := by
      simp only [Real.norm_eq_abs]
      rw [intervalIntegral.integral_of_le hpi_le, ← integral_Icc_eq_integral_Ioc]
    linarith

  have hfg_eq : ∀ᵐ x ∂volume, x ∈ uIoc (-π) π →
      |(fun x => f x - g x) x| = |f x - g₁ x| := by
    apply ae_of_all; intro x hx
    rw [uIoc_of_le hpi_le] at hx

    suffices hgx : g x = g₁ x by show |f x - g x| = |f x - g₁ x|; rw [hgx]
    by_cases hxπ : x = π
    · subst hxπ

      have h1 : g π = g (-π) := by
        show gc ((π : ℝ) : AddCircle (2 * π)) = gc ((-π : ℝ) : AddCircle (2 * π))
        congr 1
        rw [QuotientAddGroup.eq]; exact ⟨-1, by simp; ring⟩

      rw [h1, hg_eq (-π) ⟨le_refl _, by linarith [pi_pos]⟩, hg₁_neg_pi, hg₁_pi]

    · exact hg_eq x ⟨hx.1.le, lt_of_le_of_ne hx.2 hxπ⟩
  rw [intervalIntegral.integral_congr_ae hfg_eq]

  have htri : ∀ x, |f x - g₁ x| ≤ |f x - g₀ x| + |g₀ x - g₁ x| := by
    intro x; calc |f x - g₁ x| = |(f x - g₀ x) + (g₀ x - g₁ x)| := by ring_nf
      _ ≤ |f x - g₀ x| + |g₀ x - g₁ x| := abs_add_le _ _

  have hδ_le : δ ≤ ε * π / (2 * (M + 1)) := min_le_right _ _
  have hg₀g₁ : ∫ x in (-π)..π, |g₀ x - g₁ x| ≤ ε * π := by


    have habs_cont : Continuous (fun x => |g₀ x - g₁ x|) := (hg₀_cont.sub hg₁_cont).abs
    have hint := habs_cont.intervalIntegrable (-π) π (μ := volume)
    have hint1 := habs_cont.intervalIntegrable (-π) (-π + δ) (μ := volume)
    have hint2 := habs_cont.intervalIntegrable (-π + δ) (π - δ) (μ := volume)
    have hint3 := habs_cont.intervalIntegrable (π - δ) π (μ := volume)


    have tent_one : ∀ x, |x| ≤ π - δ → tent x = 1 := by
      intro x hx
      show max 0 (min 1 ((π - |x|) / δ)) = 1
      have h1 : 1 ≤ (π - |x|) / δ := by rw [le_div_iff₀ hδ_pos]; linarith
      simp only [min_eq_left h1, max_eq_right (by linarith : (0:ℝ) ≤ 1)]
    have mid_zero : ∫ x in (-π + δ)..(π - δ), |g₀ x - g₁ x| = 0 := by
      have hzero : ∀ᵐ x ∂volume, x ∈ uIoc (-π + δ) (π - δ) →
          |g₀ x - g₁ x| = (0 : ℝ) := by
        apply ae_of_all; intro x hx
        have hδ_le_pi : δ ≤ π := min_le_left _ _
        rw [uIoc_of_le (by linarith [pi_pos])] at hx

        have habs : |x| ≤ π - δ := abs_le.mpr ⟨by linarith [hx.1], by linarith [hx.2]⟩
        have : g₁ x = g₀ x * tent x := rfl
        rw [this, tent_one x habs, mul_one, sub_self, abs_zero]
      rw [intervalIntegral.integral_congr_ae hzero]
      simp


    have bound_pw : ∀ x ∈ Icc (-π) π, |g₀ x - g₁ x| ≤ M := by
      intro x hx
      have : g₁ x = g₀ x * tent x := rfl
      rw [this, show g₀ x - g₀ x * tent x = g₀ x * (1 - tent x) from by ring, abs_mul]
      calc |g₀ x| * |1 - tent x|
          ≤ M * 1 := by
            apply mul_le_mul (hM_bound x hx)
            ·
              have ht0 : 0 ≤ tent x := le_max_left 0 _
              have ht1 : tent x ≤ 1 := max_le (by norm_num) (min_le_left _ _)
              rw [abs_of_nonneg (by linarith)]
              linarith
            · exact abs_nonneg _
            · exact abs_nonneg _
        _ = M := mul_one M


    rw [show (-π : ℝ) = -π from rfl,
        ← intervalIntegral.integral_add_adjacent_intervals hint1
          (hint2.trans hint3),
        ← intervalIntegral.integral_add_adjacent_intervals hint2 hint3,
        mid_zero, zero_add]

    have hbd1 : ∫ x in (-π)..(-π + δ), |g₀ x - g₁ x| ≤ M * δ := by
      calc ∫ x in (-π)..(-π + δ), |g₀ x - g₁ x|
          ≤ ∫ x in (-π)..(-π + δ), (M : ℝ) := by
            apply intervalIntegral.integral_mono_on (by linarith [hδ_pos]) hint1
              _root_.intervalIntegrable_const
            intro x hx
            have hδ_le_pi : δ ≤ π := min_le_left _ _
            exact bound_pw x ⟨hx.1, by linarith [hx.2]⟩

        _ = M * δ := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring
    have hbd2 : ∫ x in (π - δ)..π, |g₀ x - g₁ x| ≤ M * δ := by
      calc ∫ x in (π - δ)..π, |g₀ x - g₁ x|
          ≤ ∫ x in (π - δ)..π, (M : ℝ) := by
            apply intervalIntegral.integral_mono_on (by linarith [hδ_pos]) hint3
              _root_.intervalIntegrable_const
            intro x hx
            have hδ_le_pi : δ ≤ π := min_le_left _ _
            exact bound_pw x ⟨by linarith [hx.1], hx.2⟩

        _ = M * δ := by
            rw [intervalIntegral.integral_const, smul_eq_mul]; ring

    calc (∫ x in (-π)..(-π + δ), |g₀ x - g₁ x|) + ∫ x in (π - δ)..π, |g₀ x - g₁ x|
        ≤ M * δ + M * δ := add_le_add hbd1 hbd2
      _ = 2 * M * δ := by ring
      _ ≤ 2 * M * (ε * π / (2 * (M + 1))) := by
          apply mul_le_mul_of_nonneg_left hδ_le (by positivity)
      _ = M / (M + 1) * (ε * π) := by field_simp

      _ ≤ 1 * (ε * π) := by
          apply mul_le_mul_of_nonneg_right _ (by positivity)
          rw [div_le_one (by positivity)]; linarith [abs_nonneg (g₀ M_pt)]
      _ = ε * π := one_mul _

  calc 1 / (2 * π) * ∫ x in (-π)..π, |f x - g₁ x|
      ≤ 1 / (2 * π) * ((∫ x in (-π)..π, |f x - g₀ x|) + ∫ x in (-π)..π, |g₀ x - g₁ x|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        calc ∫ x in (-π)..π, |f x - g₁ x|
            ≤ ∫ x in (-π)..π, (|f x - g₀ x| + |g₀ x - g₁ x|) :=
              intervalIntegral.integral_mono_on hpi_le
                (hf_intble.sub (hg₁_cont.intervalIntegrable _ _)).abs
                ((hf_intble.sub (hg₀_cont.intervalIntegrable _ _)).abs.add
                  ((hg₀_cont.sub hg₁_cont).intervalIntegrable _ _).abs)
                (fun x _ => htri x)
          _ = _ := by
              rw [intervalIntegral.integral_add
                (hf_intble.sub (hg₀_cont.intervalIntegrable _ _)).abs
                ((hg₀_cont.sub hg₁_cont).intervalIntegrable _ _).abs]
    _ ≤ 1 / (2 * π) * (ε * π + ε * π) := by
        apply mul_le_mul_of_nonneg_left (add_le_add hg₀_int hg₀g₁) (by positivity)
    _ = ε := by have : π ≠ 0 := ne_of_gt pi_pos; field_simp; ring


lemma periodic_integral_translate_abs (h : ℝ → ℝ)
    (hper : Function.Periodic h (2 * π)) (y : ℝ) :
    ∫ x in (-π)..π, |h (x - y)| = ∫ x in (-π)..π, |h x| := by
  have habs_per : Function.Periodic (|h ·|) (2 * π) := fun x => by
    show |h (x + 2 * π)| = |h x|; rw [hper x]
  rw [integral_comp_sub_right (fun x => |h x|) y]
  convert habs_per.intervalIntegral_add_eq (-π - y) (-π) using 2 <;> ring


lemma fubini_conv_eq (h : ℝ → ℝ) (N : ℕ)
    (hh_per : Function.Periodic h (2 * π))
    (hint : Integrable (Function.uncurry fun x y =>
        |h (x - y)| * fejerKernel N y)
      ((volume.restrict (Ioc (-π : ℝ) π)).prod
       (volume.restrict (Ioc (-π : ℝ) π)))) :
    ∫ x, (∫ y, |h (x - y)| * fejerKernel N y
      ∂(volume.restrict (Ioc (-π : ℝ) π)))
      ∂(volume.restrict (Ioc (-π : ℝ) π)) =
    (∫ x, |h x| ∂(volume.restrict (Ioc (-π : ℝ) π))) *
    (∫ y, fejerKernel N y ∂(volume.restrict (Ioc (-π : ℝ) π))) := by
  rw [integral_integral_swap hint]
  have hfact : ∀ y, ∫ x, |h (x - y)| * fejerKernel N y
      ∂(volume.restrict (Ioc (-π : ℝ) π)) =
      fejerKernel N y * ∫ x, |h (x - y)|
      ∂(volume.restrict (Ioc (-π : ℝ) π)) := by
    intro y
    rw [show (fun x => |h (x - y)| * fejerKernel N y) =
      (fun x => fejerKernel N y * |h (x - y)|) from by ext; ring]
    exact integral_const_mul _ _
  simp_rw [hfact]
  have htrans : ∀ y, ∫ x, |h (x - y)|
      ∂(volume.restrict (Ioc (-π : ℝ) π)) =
      ∫ x, |h x| ∂(volume.restrict (Ioc (-π : ℝ) π)) := by
    intro y
    rw [← integral_of_le (by linarith [pi_pos] : (-π : ℝ) ≤ π),
        ← integral_of_le (by linarith [pi_pos] : (-π : ℝ) ≤ π)]
    exact periodic_integral_translate_abs h hh_per y
  simp_rw [htrans, mul_comm (fejerKernel N _)]
  exact integral_const_mul _ _

set_option maxHeartbeats 3200000 in
theorem young_fejerKernel (h : ℝ → ℝ) (N : ℕ)
    (hh : IntervalIntegrable h volume (-π) π)
    (hh_per : Function.Periodic h (2 * π)) :
    periodicL1Norm (periodicConvolution h (fejerKernel N)) ≤ periodicL1Norm h := by

  by_cases hN : N = 0
  · subst hN
    have h1 : fejerKernel 0 = fun _ => (0 : ℝ) := by ext x; unfold fejerKernel; simp
    rw [h1]
    have h2 : periodicConvolution h (fun _ => 0) = fun _ => 0 := by
      ext x; unfold periodicConvolution; simp
    rw [h2, show periodicL1Norm (fun _ => (0 : ℝ)) = 0 from by unfold periodicL1Norm; simp]
    exact periodicL1Norm_nonneg h

  have hpi : (-π : ℝ) ≤ π := by linarith [pi_pos]
  unfold periodicL1Norm periodicConvolution
  apply mul_le_mul_of_nonneg_left _ (by positivity)


  have pw_bound : ∀ x, |1 / (2 * π) * ∫ y in (-π)..π, h (x - y) * fejerKernel N y| ≤
      1 / (2 * π) * ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y := by
    intro x
    rw [abs_mul, abs_of_nonneg (by positivity)]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    calc |∫ y in (-π)..π, h (x - y) * fejerKernel N y|
        ≤ ∫ y in (-π)..π, |h (x - y) * fejerKernel N y| := by
          have := @norm_integral_le_integral_norm ℝ _ _ (-π) π
            (fun y => h (x - y) * fejerKernel N y) volume hpi
          simp only [Real.norm_eq_abs] at this; exact this
      _ = ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y := by
          congr 1; ext y; rw [abs_mul, abs_of_nonneg (fejerKernel_nonneg_aux N y)]


  have conv_to_restrict : ∀ (f : ℝ → ℝ),
      ∫ x in (-π : ℝ)..π, f x = ∫ x, f x ∂(volume.restrict (Ioc (-π : ℝ) π)) :=
    fun f => integral_of_le hpi


  have hint : Integrable (Function.uncurry fun x y =>
      |h (x - y)| * fejerKernel N y)
    ((volume.restrict (Ioc (-π : ℝ) π)).prod
     (volume.restrict (Ioc (-π : ℝ) π))) := by

    have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
    have habs_per : Function.Periodic (fun z => |h z|) (2 * π) := by intro z; simp [hh_per z]
    have hf_any : ∀ a b : ℝ, IntervalIntegrable h volume a b :=
      hh_per.intervalIntegrable h2pi (t := -π)
        (show IntervalIntegrable h volume (-π) (-π + 2 * π) from by
          rwa [show (-π : ℝ) + 2 * π = π from by ring])
    have hf_loc : LocallyIntegrable h volume := by
      intro x; exact ⟨Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
        (hf_any (x - 2) (x + 1)).1.mono_set (fun y hy => ⟨by linarith [hy.1], hy.2⟩)⟩
    obtain ⟨g, hg_sm, hfg⟩ := hf_loc.aestronglyMeasurable

    have hprod_aesm : AEStronglyMeasurable
        (Function.uncurry fun x y => |h (x - y)| * fejerKernel N y)
        ((volume.restrict (Ioc (-π : ℝ) π)).prod (volume.restrict (Ioc (-π : ℝ) π))) := by
      refine ((hg_sm.comp_measurable (measurable_fst.sub measurable_snd)).norm.mul
        ((fejerKernel_measurable N).stronglyMeasurable.comp_measurable
          measurable_snd)).aestronglyMeasurable.congr ?_
      filter_upwards [(hfg.comp_tendsto
        (quasiMeasurePreserving_sub (volume : Measure ℝ) volume).tendsto_ae).filter_mono
        (Measure.AbsolutelyContinuous.prod
          (Measure.absolutelyContinuous_of_le (Measure.restrict_le_self (s := Ioc (-π) π)))
          (Measure.absolutelyContinuous_of_le
            (Measure.restrict_le_self (s := Ioc (-π) π)))).ae_le]
        with ⟨a, b⟩ heq
      simp only [Function.uncurry, Function.comp, Pi.mul_apply] at heq ⊢
      rw [Real.norm_eq_abs, heq]

    have hslice : ∀ x, IntegrableOn (fun y => |h (x - y)| * fejerKernel N y)
        (Ioc (-π : ℝ) π) volume := by
      intro x
      have habs_x : IntervalIntegrable (fun y => |h (x - y)|) volume (-π) π := by
        have habs_ii := habs_per.intervalIntegrable h2pi (t := -π)
          (show IntervalIntegrable (fun z => |h z|) volume (-π) (-π + 2 * π) from by
            rw [show (-π : ℝ) + 2 * π = π from by ring]; exact hh.abs)
        convert (habs_ii (x + π) (x - π)).comp_sub_left x using 1 <;> ring
      exact ((habs_x.1 |>.mono_set Subset.rfl).bdd_mul (fejerKernel_measurable N).aestronglyMeasurable.restrict
        (Eventually.of_forall fun y => by
          simp only [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux N y)]
          exact fejerKernel_le_N N y)).congr (Eventually.of_forall fun y => by ring)
    rw [integrable_prod_iff hprod_aesm]
    refine ⟨Eventually.of_forall fun x => hslice x, ?_⟩

    haveI : IsFiniteMeasure (volume.restrict (Ioc (-π : ℝ) π)) :=
      ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
    rw [← integrableOn_univ]
    apply Measure.integrableOn_of_bounded (measure_ne_top _ _)
      (hprod_aesm.norm.integral_prod_right')
    filter_upwards with x
    rw [Real.norm_eq_abs, abs_of_nonneg (integral_nonneg fun y => norm_nonneg _)]
    calc ∫ y in Ioc (-π) π, ‖(Function.uncurry fun x y =>
            |h (x - y)| * fejerKernel N y) (x, y)‖
        = ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y := by
          rw [integral_of_le hpi]; congr 1; ext y
          simp only [Function.uncurry, Real.norm_eq_abs,
            abs_of_nonneg (mul_nonneg (abs_nonneg _) (fejerKernel_nonneg_aux N y))]
      _ ≤ ↑N * ∫ y in (-π)..π, |h y| := by
          have habs_x : IntervalIntegrable (fun y => |h (x - y)|) volume (-π) π := by
            have habs_ii := habs_per.intervalIntegrable h2pi (t := -π)
              (show IntervalIntegrable (fun z => |h z|) volume (-π) (-π + 2 * π) from by
                rw [show (-π : ℝ) + 2 * π = π from by ring]; exact hh.abs)
            convert (habs_ii (x + π) (x - π)).comp_sub_left x using 1 <;> ring
          have hslice_ii : IntervalIntegrable
              (fun y => |h (x - y)| * fejerKernel N y) volume (-π) π := by
            rw [intervalIntegrable_iff, uIoc_of_le hpi]; exact hslice x
          calc ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y
              ≤ ∫ y in (-π)..π, |h (x - y)| * ↑N := by
                apply integral_mono_on hpi hslice_ii (habs_x.mul_const _)
                intro y _; exact mul_le_mul_of_nonneg_left (fejerKernel_le_N N y) (abs_nonneg _)
            _ = ↑N * ∫ y in (-π)..π, |h (x - y)| := by
                rw [show (fun y => |h (x - y)| * ↑N) = (fun y => ↑N * |h (x - y)|)
                  from by ext; ring]; exact intervalIntegral.integral_const_mul _ _
            _ = ↑N * ∫ y in (-π)..π, |h y| := by
                congr 1; rw [integral_comp_sub_left (fun y => |h y|) x]
                convert habs_per.intervalIntegral_add_eq (x - π) (-π) using 2 <;> ring

  have hbound_intble : IntervalIntegrable
      (fun u => 1 / (2 * π) * ∫ y in (-π)..π, |h (u - y)| * fejerKernel N y) volume (-π) π := by
    apply IntervalIntegrable.const_mul
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hpi]
    have := hint.integral_prod_left
    rwa [show (fun x => ∫ y, (Function.uncurry fun x y => |h (x - y)| * fejerKernel N y) (x, y)
        ∂(volume.restrict (Ioc (-π : ℝ) π))) =
      (fun x => ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y) from by
        ext x; rw [← integral_of_le hpi]; rfl] at this

  calc ∫ x in (-π)..π, |1 / (2 * π) * ∫ y in (-π)..π, h (x - y) * fejerKernel N y|
      ≤ ∫ x in (-π)..π, (1 / (2 * π) * ∫ y in (-π)..π, |h (x - y)| * fejerKernel N y) := by

        rw [conv_to_restrict, conv_to_restrict]
        apply integral_mono_of_nonneg
        · exact ae_of_all _ fun x => abs_nonneg _
        · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hpi).mp hbound_intble
        · exact ae_of_all _ fun x => pw_bound x
    _ = 1 / (2 * π) * ∫ x in (-π)..π, (∫ y in (-π)..π, |h (x - y)| * fejerKernel N y) := by
        rw [← intervalIntegral.integral_const_mul]
    _ = 1 / (2 * π) * ((∫ x, |h x| ∂(volume.restrict (Ioc (-π : ℝ) π))) *
        (∫ y, fejerKernel N y ∂(volume.restrict (Ioc (-π : ℝ) π)))) := by
        congr 1
        simp_rw [conv_to_restrict]
        exact fubini_conv_eq h N hh_per hint
    _ = ∫ x in (-π)..π, |h x| := by
        rw [← conv_to_restrict, ← conv_to_restrict]
        rw [show (1 / (2 * π) * ((∫ x in (-π)..π, |h x|) *
            (∫ y in (-π)..π, fejerKernel N y))) =
            (∫ x in (-π)..π, |h x|) * (1 / (2 * π) *
            (∫ y in (-π)..π, fejerKernel N y)) from by ring]
        rw [fejerKernel_normalize N hN, mul_one]


set_option maxHeartbeats 3200000 in
theorem fejer_uniform_convergence (g : ℝ → ℝ)
    (hg_cont : Continuous g) (hg_per : Function.Periodic g (2 * π)) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ x : ℝ,
      |g x - periodicConvolution g (fejerKernel N) x| ≤ ε := by
  suffices key : ∀ ε > 0, ∃ N₀ : ℕ, ∀ n ≥ N₀, ∀ x : ℝ,
      |g x - periodicConvolution g (fejerKernel (n + 1)) x| ≤ ε by
    intro ε hε
    obtain ⟨N₀, hN₀⟩ := key ε hε
    exact ⟨N₀ + 1, fun N hN x => by
      have : N = (N - 1) + 1 := by omega
      rw [this]; exact hN₀ (N - 1) (by omega) x⟩
  apply ApproximateIdentity.approximate_identity_lemma g (fun n => fejerKernel (n + 1)) hg_cont hg_per

  · intro N; exact fejerKernel_intervalIntegrable (N + 1)

  · intro N x
    exact (fejerKernel_intervalIntegrable (N + 1)).continuousOn_mul
      ((hg_cont.comp (continuous_const.sub continuous_id)).continuousOn)

  · intro N
    have : (fun y => |fejerKernel (N + 1) y|) = fejerKernel (N + 1) := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [this]; exact fejerKernel_intervalIntegrable (N + 1)

  · intro N x
    have h_eq : (fun y => |g (x - y) - g x| * |fejerKernel (N + 1) y|) =
        fun y => |g (x - y) - g x| * fejerKernel (N + 1) y := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [h_eq]
    exact (fejerKernel_intervalIntegrable (N + 1)).continuousOn_mul
      ((hg_cont.comp (continuous_const.sub continuous_id)).sub continuous_const).abs.continuousOn

  · intro N; exact fejerKernel_normalize (N + 1) (Nat.succ_ne_zero N)

  · refine ⟨2 * π, fun N => ?_⟩
    have hab : (fun y => |fejerKernel (N + 1) y|) = fejerKernel (N + 1) := by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (N + 1) y)]
    rw [hab]
    have h_norm := fejerKernel_normalize (N + 1) (Nat.succ_ne_zero N)
    have hI : ∫ x in (-π)..π, fejerKernel (N + 1) x = 2 * π := by
      have : (0 : ℝ) < 2 * π := by positivity
      field_simp at h_norm; linarith
    linarith

  · intro δ hδ_pos hδ_le_pi
    have hpi_pos := pi_pos
    have hδ2_pos : 0 < δ / 2 := by linarith
    have hδ2_lt_pi : δ / 2 < π := by linarith
    have hsin_δ_pos : 0 < sin (δ / 2) := sin_pos_of_pos_of_lt_pi hδ2_pos hδ2_lt_pi
    have hsin_δ_sq_pos : 0 < sin (δ / 2) ^ 2 := sq_pos_of_pos hsin_δ_pos

    have h_abs_eq : ∀ n, (fun x => |fejerKernel (n + 1) x|) = fejerKernel (n + 1) := fun n => by
      ext y; rw [abs_of_nonneg (fejerKernel_nonneg_aux (n + 1) y)]
    simp_rw [h_abs_eq]

    set C : ℕ → ℝ := fun n => 1 / ((n + 1 : ℝ) * sin (δ / 2) ^ 2) with hC_def

    have h_pw_pos : ∀ n, ∀ x ∈ Icc δ π, fejerKernel (n + 1) x ≤ C n := by
      intro n x ⟨hxl, hxr⟩
      have hx_half_pos : 0 < x / 2 := by linarith [lt_of_lt_of_le hδ_pos hxl]
      have hx_half_le : x / 2 ≤ π / 2 := by linarith
      have hsin_x_pos : 0 < sin (x / 2) := sin_pos_of_pos_of_lt_pi hx_half_pos (by linarith)
      have hsin_x_ne : sin (x / 2) ≠ 0 := ne_of_gt hsin_x_pos
      have hsin_mono : sin (δ / 2) ≤ sin (x / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) hx_half_le (by linarith)
      have hsq_mono : sin (δ / 2) ^ 2 ≤ sin (x / 2) ^ 2 :=
        sq_le_sq' (by linarith [sin_nonneg_of_nonneg_of_le_pi hδ2_pos.le (by linarith : δ / 2 ≤ π)]) hsin_mono
      unfold fejerKernel
      simp only [Nat.succ_ne_zero, hsin_x_ne, ↓reduceIte, div_pow]
      have hN_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity


      simp only [Nat.cast_add, Nat.cast_one] at *
      calc 1 / ((n : ℝ) + 1) * (sin (((n : ℝ) + 1) * x / 2) ^ 2 / sin (x / 2) ^ 2)
          ≤ 1 / ((n : ℝ) + 1) * (1 / sin (x / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right (sin_sq_le_one _) (sq_pos_of_ne_zero hsin_x_ne).le
        _ ≤ 1 / ((n : ℝ) + 1) * (1 / sin (δ / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq_mono
        _ = C n := by simp only [hC_def]; field_simp

    have h_pw_neg : ∀ n, ∀ x ∈ Icc (-π) (-δ), fejerKernel (n + 1) x ≤ C n := by
      intro n x ⟨hxl, hxr⟩
      have hnx_pos : 0 < -x / 2 := by linarith
      have hnx_le : -x / 2 ≤ π / 2 := by linarith
      have hsin_nx_pos : 0 < sin (-x / 2) := sin_pos_of_pos_of_lt_pi hnx_pos (by linarith)
      have hsin_sq : sin (x / 2) ^ 2 = sin (-x / 2) ^ 2 := by
        rw [show -x / 2 = -(x / 2) from by ring, sin_neg]; ring
      have hsin_x_ne : sin (x / 2) ≠ 0 := by
        intro h; have := sq_eq_zero_iff.mpr h; rw [hsin_sq] at this
        linarith [sq_pos_of_pos hsin_nx_pos]
      have hsin_mono : sin (δ / 2) ≤ sin (-x / 2) :=
        sin_le_sin_of_le_of_le_pi_div_two (by linarith) hnx_le (by linarith)
      have hsq_mono : sin (δ / 2) ^ 2 ≤ sin (x / 2) ^ 2 := by
        rw [hsin_sq]
        exact sq_le_sq' (by linarith [sin_nonneg_of_nonneg_of_le_pi hδ2_pos.le (by linarith : δ / 2 ≤ π)]) hsin_mono
      unfold fejerKernel
      simp only [Nat.succ_ne_zero, hsin_x_ne, ↓reduceIte, div_pow]
      simp only [Nat.cast_add, Nat.cast_one] at *
      calc 1 / ((n : ℝ) + 1) * (sin (((n : ℝ) + 1) * x / 2) ^ 2 / sin (x / 2) ^ 2)
          ≤ 1 / ((n : ℝ) + 1) * (1 / sin (x / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_right (sin_sq_le_one _) (sq_pos_of_ne_zero hsin_x_ne).le
        _ ≤ 1 / ((n : ℝ) + 1) * (1 / sin (δ / 2) ^ 2) := by
            apply mul_le_mul_of_nonneg_left _ (by positivity)
            exact div_le_div_of_nonneg_left (by positivity) (by positivity) hsq_mono
        _ = C n := by simp only [hC_def]; field_simp

    rw [Metric.tendsto_atTop]
    intro ε hε


    obtain ⟨N₀, hN₀⟩ := exists_nat_gt (2 * (π - δ) / (ε * sin (δ / 2) ^ 2))
    use N₀
    intro n hn
    rw [Real.dist_eq, sub_zero]
    have hsum_nonneg : 0 ≤ (∫ x in (-π)..(-δ), fejerKernel (n + 1) x) +
        ∫ x in δ..π, fejerKernel (n + 1) x := by
      apply add_nonneg
      · exact intervalIntegral.integral_nonneg (by linarith) (fun u _ => fejerKernel_nonneg_aux (n+1) u)
      · exact intervalIntegral.integral_nonneg hδ_le_pi (fun u _ => fejerKernel_nonneg_aux (n+1) u)
    rw [abs_of_nonneg hsum_nonneg]

    have hC_bound : C n ≥ 0 := by simp only [hC_def]; positivity
    have h_bound_neg : ‖∫ x in (-π)..(-δ), fejerKernel (n + 1) x‖ ≤ C n * |(-δ) - (-π)| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux (n+1) x)]
      apply h_pw_neg n x
      rw [uIoc_of_le (by linarith : -π ≤ -δ)] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have h_bound_pos : ‖∫ x in δ..π, fejerKernel (n + 1) x‖ ≤ C n * |π - δ| := by
      apply intervalIntegral.norm_integral_le_of_norm_le_const
      intro x hx
      rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux (n+1) x)]
      apply h_pw_pos n x
      rw [uIoc_of_le hδ_le_pi] at hx
      exact ⟨le_of_lt hx.1, hx.2⟩
    have habs_neg : |-δ - -π| = π - δ := by rw [show -δ - -π = π - δ from by ring]; exact abs_of_nonneg (by linarith)
    have habs_pos : |π - δ| = π - δ := abs_of_nonneg (by linarith)
    rw [habs_neg] at h_bound_neg; rw [habs_pos] at h_bound_pos

    have h_neg_le : ∫ x in (-π)..(-δ), fejerKernel (n + 1) x ≤ C n * (π - δ) := by
      rwa [Real.norm_eq_abs, abs_of_nonneg
        (intervalIntegral.integral_nonneg (by linarith)
          (fun u _ => fejerKernel_nonneg_aux (n+1) u))] at h_bound_neg
    have h_pos_le : ∫ x in δ..π, fejerKernel (n + 1) x ≤ C n * (π - δ) := by
      rwa [Real.norm_eq_abs, abs_of_nonneg
        (intervalIntegral.integral_nonneg hδ_le_pi
          (fun u _ => fejerKernel_nonneg_aux (n+1) u))] at h_bound_pos

    have hN_pos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    calc (∫ x in (-π)..(-δ), fejerKernel (n + 1) x) + ∫ x in δ..π, fejerKernel (n + 1) x
        ≤ C n * (π - δ) + C n * (π - δ) := add_le_add h_neg_le h_pos_le
      _ = 2 * (π - δ) * C n := by ring
      _ = 2 * (π - δ) / (((n : ℝ) + 1) * sin (δ / 2) ^ 2) := by simp only [hC_def]; ring
      _ < ε := by
          rw [div_lt_iff₀ (mul_pos hN_pos hsin_δ_sq_pos)]
          have hes := mul_pos hε hsin_δ_sq_pos
          have h1 : 2 * (π - δ) < ↑N₀ * (ε * sin (δ / 2) ^ 2) := by
            rwa [div_lt_iff₀ hes] at hN₀
          have h2 : (N₀ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
          have h3 : ↑N₀ * (ε * sin (δ / 2) ^ 2) ≤ ↑n * (ε * sin (δ / 2) ^ 2) :=
            mul_le_mul_of_nonneg_right h2 hes.le
          nlinarith


theorem convolution_linear (g h : ℝ → ℝ) (N : ℕ) (x : ℝ)
    (hg : IntervalIntegrable (fun y => g (x - y) * fejerKernel N y) volume (-π) π)
    (hh : IntervalIntegrable (fun y => h (x - y) * fejerKernel N y) volume (-π) π) :
    periodicConvolution (fun y => g y - h y) (fejerKernel N) x =
      periodicConvolution g (fejerKernel N) x -
        periodicConvolution h (fejerKernel N) x := by
  simp only [periodicConvolution, sub_mul, ← mul_sub]
  congr 1
  exact integral_sub hg hh


lemma conv_intble_of_continuous (g : ℝ → ℝ) (hg : Continuous g) (N : ℕ) (x : ℝ) :
    IntervalIntegrable (fun y => g (x - y) * fejerKernel N y) volume (-π) π :=
  (fejerKernel_intervalIntegrable N).continuousOn_mul
    ((hg.comp (continuous_const.sub continuous_id)).continuousOn)


lemma conv_intble_of_periodic (f : ℝ → ℝ)
    (hf_per : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π)
    (N : ℕ) (x : ℝ) :
    IntervalIntegrable (fun y => f (x - y) * fejerKernel N y) volume (-π) π := by
  have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
  have hf_any : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    hf_per.intervalIntegrable h2pi (t := -π)
      (show IntervalIntegrable f volume (-π) (-π + 2 * π) from by
        rwa [show (-π : ℝ) + 2 * π = π from by ring])
  have hfx : IntervalIntegrable (fun y => f (x - y)) volume (-π) π := by
    have h := (hf_any (x + π) (x - π)).comp_sub_left x
    convert h using 1 <;> ring
  have hpi : (-π : ℝ) ≤ π := by linarith [pi_pos]
  have hfx_io : IntegrableOn (fun y => f (x - y)) (uIoc (-π) π) volume := by
    rw [uIoc_of_le hpi]; exact hfx.1
  have hmul : IntegrableOn (fun y => fejerKernel N y * f (x - y)) (uIoc (-π) π) volume :=
    hfx_io.bdd_mul (fejerKernel_measurable N).aestronglyMeasurable.restrict
      (Filter.Eventually.of_forall fun y => by
        simp only [Real.norm_eq_abs]
        exact abs_le_abs (fejerKernel_le_N N y) (by linarith [fejerKernel_nonneg_aux N y]))
  rw [intervalIntegrable_iff]
  exact hmul.congr (Filter.Eventually.of_forall fun y => by ring)


lemma trig_sum_extend (a b : ℕ → ℝ) (N M : ℕ) (hNM : N ≤ M) (x : ℝ) :
    ∑ n ∈ Finset.range (N + 1), (a n * cos (↑n * x) + b n * sin (↑n * x)) =
    ∑ n ∈ Finset.range (M + 1),
      ((if n ≤ N then a n else 0) * cos (↑n * x) +
       (if n ≤ N then b n else 0) * sin (↑n * x)) := by
  have h_filter : (Finset.range (M + 1)).filter (fun n => n ≤ N) = Finset.range (N + 1) := by
    ext n; simp [Finset.mem_filter, Finset.mem_range]; omega
  rw [← Finset.sum_filter_add_sum_filter_not (Finset.range (M + 1)) (fun n => n ≤ N)]
  rw [h_filter]
  have h_zero : ∑ n ∈ (Finset.range (M + 1)).filter (fun n => ¬(n ≤ N)),
      ((if n ≤ N then a n else 0) * cos (↑n * x) +
       (if n ≤ N then b n else 0) * sin (↑n * x)) = 0 := by
    apply Finset.sum_eq_zero; intro n hn
    simp only [Finset.mem_filter, Finset.mem_range, not_le] at hn
    simp [show ¬(n ≤ N) from by omega]
  rw [h_zero, add_zero]
  apply Finset.sum_congr rfl; intro n hn
  simp only [Finset.mem_range] at hn; simp [show n ≤ N from by omega]


lemma isTrigPolynomial_add {p q : ℝ → ℝ}
    (hp : IsTrigPolynomial p) (hq : IsTrigPolynomial q) :
    IsTrigPolynomial (fun x => p x + q x) := by
  obtain ⟨N, a, b, hp⟩ := hp; obtain ⟨M, c, d, hq⟩ := hq
  refine ⟨max N M,
    fun n => (if n ≤ N then a n else 0) + (if n ≤ M then c n else 0),
    fun n => (if n ≤ N then b n else 0) + (if n ≤ M then d n else 0),
    fun x => ?_⟩
  simp only; rw [hp x, hq x]
  rw [trig_sum_extend a b N (max N M) (le_max_left N M) x]
  rw [trig_sum_extend c d M (max N M) (le_max_right N M) x]
  rw [← Finset.sum_add_distrib]; congr 1; ext n; ring


lemma isTrigPolynomial_smul (c : ℝ) {p : ℝ → ℝ}
    (hp : IsTrigPolynomial p) :
    IsTrigPolynomial (fun x => c * p x) := by
  obtain ⟨N, a, b, hp⟩ := hp
  exact ⟨N, fun n => c * a n, fun n => c * b n, fun x => by
    simp only; rw [hp x, Finset.mul_sum]; congr 1; ext n; ring⟩


lemma isTrigPolynomial_finset_sum {f : ℕ → ℝ → ℝ} {s : Finset ℕ}
    (hf : ∀ i ∈ s, IsTrigPolynomial (f i)) :
    IsTrigPolynomial (fun x => ∑ i ∈ s, f i x) := by
  induction s using Finset.cons_induction with
  | empty => exact ⟨0, fun _ => 0, fun _ => 0, fun x => by simp⟩
  | cons a s ha ih =>
    rw [show (fun x => ∑ i ∈ Finset.cons a s ha, f i x) =
        (fun x => f a x + ∑ i ∈ s, f i x) from by
      ext x; rw [Finset.sum_cons]]
    exact isTrigPolynomial_add (hf a (Finset.mem_cons_self a s))
      (ih (fun i hi => hf i (Finset.mem_cons_of_mem hi)))


lemma dirichlet_isTrigPolynomial (j : ℕ) :
    IsTrigPolynomial (fun x => 1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) := by
  refine ⟨j, fun n => if n = 0 then 1 else 2, fun _ => 0, fun x => ?_⟩
  rw [Finset.sum_range_succ']
  simp only [Nat.cast_zero, zero_mul, cos_zero, ite_true, mul_one,
    Nat.succ_ne_zero, ite_false, add_zero]
  rw [Finset.mul_sum, add_comm]
  congr 1
  apply Finset.sum_congr rfl; intro k _
  push_cast; ring


lemma cos_eq_one_of_sin_half_eq_zero (x : ℝ) (h : sin (x / 2) = 0) (n : ℕ) :
    cos (n * x) = 1 := by
  rw [sin_eq_zero_iff] at h
  obtain ⟨k, hk⟩ := h
  have hx : x = 2 * k * π := by linarith
  rw [hx, show (n : ℝ) * (2 * ↑k * π) = ↑(n * k) * (2 * π) from by push_cast; ring]
  exact cos_int_mul_two_pi (n * k)


private lemma sum_odd_eq_sq (N : ℕ) :
    ∑ j ∈ Finset.range N, ((1 : ℝ) + 2 * j) = N ^ 2 := by
  induction N with
  | zero => simp
  | succ m ih => rw [Finset.sum_range_succ, ih]; push_cast; ring


set_option maxHeartbeats 800000 in
lemma fejerKernel_eq_dirichlet_avg (N : ℕ) (hN : N ≠ 0) (x : ℝ) :
    fejerKernel N x =
      (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) := by
  by_cases hsin : sin (x / 2) = 0
  ·
    unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]
    have h1 : ∀ k : ℕ, cos ((↑k + 1) * x) = 1 := fun k => by
      have := cos_eq_one_of_sin_half_eq_zero x hsin (k + 1)
      convert this using 1; push_cast; ring
    simp_rw [h1, Finset.sum_const, Finset.card_range, Nat.smul_one_eq_cast]
    rw [sum_odd_eq_sq]
    have hN' : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN
    field_simp
  ·
    unfold fejerKernel; simp only [hN, hsin, ↓reduceIte]


    congr 1


    have hdir : ∀ (j : ℕ), sin ((2 * ↑j + 1) * (x / 2)) * sin (x / 2) =
        sin (x / 2) ^ 2 * (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) := by
      intro j; rw [dirichlet_identity j x]; ring

    have htel := fejer_telescope N x

    have hsum : sin (x / 2) ^ 2 * ∑ j ∈ Finset.range N,
        (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) = sin (↑N * x / 2) ^ 2 := by
      rw [Finset.mul_sum]
      have : ∀ i ∈ Finset.range N,
          sin (x / 2) ^ 2 * (1 + 2 * ∑ k ∈ Finset.range i, cos ((↑k + 1) * x)) =
          sin ((2 * ↑i + 1) * (x / 2)) * sin (x / 2) :=
        fun i _ => (hdir i).symm
      rw [Finset.sum_congr rfl this]
      exact htel

    have hsin2 : sin (x / 2) ^ 2 ≠ 0 := pow_ne_zero 2 hsin
    rw [div_pow]
    have hsin2_pos : (0 : ℝ) < sin (x / 2) ^ 2 := by positivity
    rw [div_eq_iff (ne_of_gt hsin2_pos)]
    linarith


theorem fejerKernel_isTrigPolynomial (N : ℕ) : IsTrigPolynomial (fejerKernel N) := by
  by_cases hN : N = 0
  ·
    subst hN
    exact ⟨0, fun _ => 0, fun _ => 0, fun x => by simp [fejerKernel]⟩
  ·
    have hkey : ∀ x, fejerKernel N x =
        (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
          (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x)) :=
      fun x => fejerKernel_eq_dirichlet_avg N hN x

    have h_sum_tp : IsTrigPolynomial (fun x =>
        ∑ j ∈ Finset.range N, (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x))) :=
      isTrigPolynomial_finset_sum (fun j _ => dirichlet_isTrigPolynomial j)

    have h_scaled : IsTrigPolynomial (fun x =>
        (1 / (N : ℝ)) * ∑ j ∈ Finset.range N,
          (1 + 2 * ∑ k ∈ Finset.range j, cos ((↑k + 1) * x))) :=
      isTrigPolynomial_smul (1 / (N : ℝ)) h_sum_tp

    obtain ⟨M, a, b, h_eq⟩ := h_scaled
    exact ⟨M, a, b, fun x => by rw [hkey x]; exact h_eq x⟩


lemma fxy_intervalIntegrable (f : ℝ → ℝ) (hf_per : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) (x : ℝ) :
    IntervalIntegrable (fun y => f (x - y)) volume (-π) π := by
  have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
  have hf_any : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    hf_per.intervalIntegrable h2pi (t := -π)
      (show IntervalIntegrable f volume (-π) (-π + 2 * π) from by
        rwa [show (-π : ℝ) + 2 * π = π from by ring])
  have h := (hf_any (x + π) (x - π)).comp_sub_left x
  convert h using 1 <;> ring


lemma periodic_integral_shift (g : ℝ → ℝ) (hg : Function.Periodic g (2 * π)) (x : ℝ) :
    ∫ y in (-π)..π, g (x - y) = ∫ y in (-π)..π, g y := by
  have step1 := (integral_comp_sub_left (a := -π) (b := π) g x).symm
  simp only [sub_neg_eq_add] at step1; rw [← step1]
  have step2 := hg.intervalIntegral_add_eq (x - π) (-π)
  rw [show (x - π) + 2 * π = x + π from by ring, show (-π : ℝ) + 2 * π = π from by ring] at step2
  exact step2


set_option maxHeartbeats 800000 in
lemma single_term_convolution (f : ℝ → ℝ) (hf_per : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) (a b : ℝ) (n : ℕ) (x : ℝ) :
    ∫ y in (-π)..π, f (x - y) * (a * cos (↑n * y) + b * sin (↑n * y)) =
    (a * (∫ t in (-π)..π, f t * cos (↑n * t)) -
     b * (∫ t in (-π)..π, f t * sin (↑n * t))) * cos (↑n * x) +
    (a * (∫ t in (-π)..π, f t * sin (↑n * t)) +
     b * (∫ t in (-π)..π, f t * cos (↑n * t))) * sin (↑n * x) := by
  have hfx := fxy_intervalIntegrable f hf_per hf_intble x
  have hfc : IntervalIntegrable (fun y => f (x - y) * cos (↑n * y)) volume (-π) π :=
    hfx.mul_continuousOn (continuous_cos.comp (continuous_const.mul continuous_id)).continuousOn
  have hfs : IntervalIntegrable (fun y => f (x - y) * sin (↑n * y)) volume (-π) π :=
    hfx.mul_continuousOn (continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
  have hfcx : IntervalIntegrable (fun y => f (x - y) * cos (↑n * (x - y))) volume (-π) π :=
    hfx.mul_continuousOn ((continuous_cos.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).continuousOn)
  have hfsx : IntervalIntegrable (fun y => f (x - y) * sin (↑n * (x - y))) volume (-π) π :=
    hfx.mul_continuousOn ((continuous_sin.comp (continuous_const.mul
      (continuous_const.sub continuous_id))).continuousOn)
  simp_rw [show ∀ y, f (x - y) * (a * cos (↑n * y) + b * sin (↑n * y)) =
      a * (f (x - y) * cos (↑n * y)) + b * (f (x - y) * sin (↑n * y)) from fun y => by ring]
  rw [integral_add (hfc.const_mul a) (hfs.const_mul b),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [show ∀ y, f (x - y) * cos (↑n * y) =
      cos (↑n * x) * (f (x - y) * cos (↑n * (x - y))) +
      sin (↑n * x) * (f (x - y) * sin (↑n * (x - y))) from by
    intro y; have h := Real.cos_sub (↑n * x) (↑n * (x - y))
    rw [show ↑n * x - ↑n * (x - y) = ↑n * y from by ring] at h; rw [h]; ring]
  rw [integral_add (hfcx.const_mul _) (hfsx.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  simp_rw [show ∀ y, f (x - y) * sin (↑n * y) =
      sin (↑n * x) * (f (x - y) * cos (↑n * (x - y))) -
      cos (↑n * x) * (f (x - y) * sin (↑n * (x - y))) from by
    intro y; have h := Real.sin_sub (↑n * x) (↑n * (x - y))
    rw [show ↑n * x - ↑n * (x - y) = ↑n * y from by ring] at h; rw [h]; ring]
  rw [integral_sub (hfcx.const_mul _) (hfsx.const_mul _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  have hper_c : Function.Periodic (fun t => f t * cos (↑n * t)) (2 * π) := by
    intro t; simp only [Function.Periodic] at hf_per ⊢
    rw [hf_per, show ↑n * (t + 2 * π) = ↑n * t + ↑(n : ℤ) * (2 * π) from by push_cast; ring,
        Real.cos_add_int_mul_two_pi]
  have hper_s : Function.Periodic (fun t => f t * sin (↑n * t)) (2 * π) := by
    intro t; simp only [Function.Periodic] at hf_per ⊢
    rw [hf_per, show ↑n * (t + 2 * π) = ↑n * t + ↑(n : ℤ) * (2 * π) from by push_cast; ring,
        Real.sin_add_int_mul_two_pi]
  rw [periodic_integral_shift _ hper_c x, periodic_integral_shift _ hper_s x]
  ring


set_option maxHeartbeats 1600000 in
theorem fejerMean_isTrigPolynomial (f : ℝ → ℝ) (N : ℕ)
    (hf_per : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) :
    IsTrigPolynomial (fejerMean f N) := by
  obtain ⟨M, aK, bK, hK⟩ := fejerKernel_isTrigPolynomial N
  let Cn : ℕ → ℝ := fun n => ∫ t in (-π)..π, f t * cos (↑n * t)
  let Sn : ℕ → ℝ := fun n => ∫ t in (-π)..π, f t * sin (↑n * t)
  refine ⟨M, fun n => (1 / (2 * π)) * (aK n * Cn n - bK n * Sn n),
            fun n => (1 / (2 * π)) * (aK n * Sn n + bK n * Cn n), fun x => ?_⟩
  simp only [fejerMean, periodicConvolution]
  simp_rw [hK]
  simp_rw [Finset.mul_sum]
  have hfx := fxy_intervalIntegrable f hf_per hf_intble x
  have h_intble : ∀ n ∈ Finset.range (M + 1),
      IntervalIntegrable (fun y => f (x - y) * (aK n * cos (↑n * y) + bK n * sin (↑n * y)))
        volume (-π) π := fun n _ =>
    hfx.mul_continuousOn ((((continuous_const.mul (continuous_cos.comp
      (continuous_const.mul continuous_id))).add (continuous_const.mul (continuous_sin.comp
      (continuous_const.mul continuous_id))))).continuousOn)
  rw [intervalIntegral.integral_finset_sum h_intble, Finset.mul_sum]
  congr 1; ext n
  rw [single_term_convolution f hf_per hf_intble (aK n) (bK n) n x]
  ring


theorem intble_diff_abs (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-π) π)
    (hg_cont : Continuous g) (_hg_per : Function.Periodic g (2 * π)) :
    IntervalIntegrable (fun x => |f x - g x|) volume (-π) π :=
  (hf.sub (hg_cont.intervalIntegrable (-π) π)).abs

theorem intble_cts_conv (g : ℝ → ℝ) (N : ℕ)
    (hg_cont : Continuous g) (hg_per : Function.Periodic g (2 * π)) :
    IntervalIntegrable
      (fun x => |g x - periodicConvolution g (fejerKernel N) x|) volume (-π) π := by

  have h2pi_pos : (0 : ℝ) < 2 * π := by positivity
  obtain ⟨M, hM⟩ := (isCompact_Icc (a := 0) (b := 2 * π)).exists_bound_of_continuousOn
    hg_cont.continuousOn
  have hM0 : 0 ≤ M := le_trans (norm_nonneg (g 0)) (hM 0 ⟨le_refl _, by linarith⟩)
  have hgM : ∀ x, |g x| ≤ M := fun x => by
    obtain ⟨y, hy_mem, hy_eq⟩ := hg_per.exists_mem_Ico₀ h2pi_pos x
    have h1 : |g y| ≤ M := by
      rw [← Real.norm_eq_abs]; exact hM y (Ico_subset_Icc_self hy_mem)
    rw [hy_eq]; exact h1

  have hKbdd : ∀ y, |fejerKernel N y| ≤ ↑N := fun y => by
    rw [abs_of_nonneg (fejerKernel_nonneg_aux N y)]
    exact fejerKernel_le_N N y

  have hpi : (-π : ℝ) ≤ π := by linarith [pi_pos]
  have hcont_int : Continuous (fun x => ∫ y in (-π)..π, g (x - y) * fejerKernel N y) := by
    have heq : (fun x => ∫ y in (-π)..π, g (x - y) * fejerKernel N y) =
      (fun x => ∫ y, g (x - y) * fejerKernel N y ∂(volume.restrict (Set.Ioc (-π) π))) := by
      ext x; rw [intervalIntegral.integral_of_le hpi]
    rw [heq]
    haveI : IsFiniteMeasure (volume.restrict (Set.Ioc (-π : ℝ) π)) := by
      constructor; rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top
    apply continuous_of_dominated
    · intro x
      exact ((hg_cont.comp (continuous_const.sub continuous_id)).aestronglyMeasurable.mul
        (fejerKernel_measurable N).aestronglyMeasurable).restrict
    · intro x
      filter_upwards with y
      simp only [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hgM _) (hKbdd _) (abs_nonneg _) hM0
    · exact integrable_const _
    · filter_upwards with y
      exact (hg_cont.comp (continuous_sub_right y)).mul continuous_const

  have hcont_conv : Continuous (periodicConvolution g (fejerKernel N)) := by
    show Continuous (fun x => (1 / (2 * π)) * ∫ y in (-π)..π, g (x - y) * fejerKernel N y)
    exact continuous_const.mul hcont_int

  exact ((hg_cont.sub hcont_conv).abs).intervalIntegrable (-π) π


lemma periodicConv_intervalIntegrable (f : ℝ → ℝ) (N : ℕ)
    (hf_per : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) :
    IntervalIntegrable (periodicConvolution f (fejerKernel N)) volume (-π) π := by

  have h2pi : (2 : ℝ) * π ≠ 0 := by positivity
  have hf_any : ∀ a b : ℝ, IntervalIntegrable f volume a b :=
    hf_per.intervalIntegrable h2pi (t := -π)
      (show IntervalIntegrable f volume (-π) (-π + 2 * π) from by
        rwa [show (-π : ℝ) + 2 * π = π from by ring])
  have hf_loc : LocallyIntegrable f volume := by
    intro x
    exact ⟨Set.Icc (x - 1) (x + 1), Icc_mem_nhds (by linarith) (by linarith),
      (hf_any (x - 2) (x + 1)).1.mono_set (fun y hy => ⟨by linarith [hy.1], hy.2⟩)⟩

  have hf_aesm := hf_loc.aestronglyMeasurable
  obtain ⟨g, hg_sm, hfg⟩ := hf_aesm


  have hconv_eq : ∀ x, periodicConvolution f (fejerKernel N) x =
      periodicConvolution g (fejerKernel N) x := by
    intro x
    simp only [periodicConvolution]
    congr 1
    apply intervalIntegral.integral_congr_ae
    have hfg_shift : (fun y => f (x - y)) =ᵐ[volume] (fun y => g (x - y)) :=
      (quasiMeasurePreserving_sub_left volume x).ae_eq hfg
    filter_upwards [hfg_shift] with y hy _
    rw [hy]

  have hconv_sm : StronglyMeasurable (fun x => periodicConvolution g (fejerKernel N) x) := by
    show StronglyMeasurable (fun x => (1 / (2 * π)) * ∫ y in (-π)..π, g (x - y) * fejerKernel N y)
    apply StronglyMeasurable.const_mul
    have hle : (-π : ℝ) ≤ π := by linarith [pi_pos]
    have h1 : (fun x => ∫ y in (-π)..π, g (x - y) * fejerKernel N y) =
      (fun x => ∫ y, g (x - y) * fejerKernel N y ∂(volume.restrict (Set.Ioc (-π) π))) := by
      ext x; rw [intervalIntegral.integral_of_le hle]
    rw [h1]
    exact ((hg_sm.comp_measurable (measurable_fst.sub measurable_snd)).mul
      ((fejerKernel_measurable N).stronglyMeasurable.comp_measurable measurable_snd)).integral_prod_right

  have hconv_sm' : StronglyMeasurable (periodicConvolution f (fejerKernel N)) := by
    have : periodicConvolution f (fejerKernel N) = fun x => periodicConvolution g (fejerKernel N) x :=
      funext hconv_eq
    rw [this]; exact hconv_sm

  rw [intervalIntegrable_iff]
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]

  have hf_per_norm : Function.Periodic (fun y => ‖f y‖) (2 * π) := by
    intro y; simp only [hf_per y]
  have hf_norm : ∀ x, ∫ y in (-π)..π, ‖f (x - y)‖ = ∫ y in (-π)..π, ‖f y‖ := by
    intro x
    rw [intervalIntegral.integral_comp_sub_left (fun u => ‖f u‖) x]
    conv_lhs => rw [show x - π = -π + x from by ring, show x - -π = -π + x + 2 * π from by ring]
    exact (hf_per_norm.intervalIntegral_add_eq (-π + x) (-π)).trans (by
      rw [show (-π : ℝ) + 2 * π = π from by ring])

  have hC : ∀ x, ‖periodicConvolution f (fejerKernel N) x‖ ≤
      (1 / (2 * π)) * (↑N * ∫ y in (-π)..π, ‖f y‖) := by
    intro x
    simp only [periodicConvolution, Real.norm_eq_abs, abs_mul]
    rw [abs_of_nonneg (by positivity)]
    have h_abs_le : |∫ y in (-π)..π, f (x - y) * fejerKernel N y| ≤
        ∫ y in (-π)..π, ‖f (x - y) * fejerKernel N y‖ := by
      rw [← Real.norm_eq_abs]
      exact intervalIntegral.norm_integral_le_integral_norm hpi_le
    calc (1 / (2 * π)) * |∫ y in (-π)..π, f (x - y) * fejerKernel N y|
        ≤ (1 / (2 * π)) * ∫ y in (-π)..π, ‖f (x - y) * fejerKernel N y‖ := by gcongr
      _ ≤ (1 / (2 * π)) * ∫ y in (-π)..π, ‖f (x - y)‖ * ↑N := by
          gcongr
          have h_ub : IntervalIntegrable (fun y => ‖f (x - y)‖ * ↑N) volume (-π) π := by
            have hfx : IntervalIntegrable (fun y => f (x - y)) volume (-π) π := by
              have h := (hf_any (x + π) (x - π)).comp_sub_left x
              convert h using 1 <;> ring
            exact hfx.norm.mul_const ↑N

          exact integral_mono_on hpi_le
            (conv_intble_of_periodic f hf_per hf N x).norm h_ub
            (fun y _ => by
              rw [norm_mul]
              exact mul_le_mul_of_nonneg_left
                (by rw [Real.norm_eq_abs, abs_of_nonneg (fejerKernel_nonneg_aux N y)]
                    exact fejerKernel_le_N N y)
                (norm_nonneg _))

      _ = (1 / (2 * π)) * (↑N * ∫ y in (-π)..π, ‖f (x - y)‖) := by
          congr 1; rw [← intervalIntegral.integral_const_mul]
          congr 1; ext y; ring
      _ = (1 / (2 * π)) * (↑N * ∫ y in (-π)..π, ‖f y‖) := by rw [hf_norm x]
  exact IntegrableOn.of_bound measure_Ioc_lt_top
    hconv_sm'.aestronglyMeasurable.restrict
    ((1 / (2 * π)) * (↑N * ∫ y in (-π)..π, ‖f y‖))
    (Eventually.of_forall (fun x => hC x))

theorem intble_result (f : ℝ → ℝ) (N : ℕ)
    (hf_per : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π) :
    IntervalIntegrable (fun x => |f x - fejerMean f N x|) volume (-π) π :=
  (hf.sub (periodicConv_intervalIntegrable f N hf_per hf)).abs

theorem intble_conv_diff (f g : ℝ → ℝ) (N : ℕ)
    (hf_per : Function.Periodic f (2 * π))
    (hf : IntervalIntegrable f volume (-π) π)
    (hg_cont : Continuous g) (hg_per : Function.Periodic g (2 * π)) :
    IntervalIntegrable
      (fun x => |periodicConvolution g (fejerKernel N) x -
                  periodicConvolution f (fejerKernel N) x|) volume (-π) π :=
  ((periodicConv_intervalIntegrable g N hg_per (hg_cont.intervalIntegrable (-π) π)).sub
    (periodicConv_intervalIntegrable f N hf_per hf)).abs

theorem intble_diff (f g : ℝ → ℝ)
    (hf : IntervalIntegrable f volume (-π) π)
    (hg_cont : Continuous g) (_hg_per : Function.Periodic g (2 * π)) :
    IntervalIntegrable (fun x => g x - f x) volume (-π) π :=
  (hg_cont.intervalIntegrable (-π) π).sub hf

set_option maxHeartbeats 800000 in
theorem fejer_L1_convergence
    (f : ℝ → ℝ)
    (hf_periodic : Function.Periodic f (2 * π))
    (hf_intble : IntervalIntegrable f volume (-π) π) :
    Tendsto (fun N => periodicL1Norm (fun x => f x - fejerMean f N x))
      atTop (nhds 0) := by
  rw [Metric.tendsto_atTop]
  intro ε hε

  obtain ⟨g, hg_cont, hg_per, hg_approx⟩ :=
    continuous_periodic_dense_L1 f hf_periodic hf_intble (ε / 4) (by linarith)

  obtain ⟨N₀, hN₀⟩ := fejer_uniform_convergence g hg_cont hg_per (ε / 4) (by linarith)
  use N₀
  intro N hN
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (periodicL1Norm_nonneg _)]

  simp only [periodicL1Norm, fejerMean]
  have hpi_le : (-π : ℝ) ≤ π := by linarith [pi_pos]


  have h_pw : ∀ x, |f x - periodicConvolution f (fejerKernel N) x| ≤
      |f x - g x| + |g x - periodicConvolution g (fejerKernel N) x| +
      |periodicConvolution g (fejerKernel N) x -
        periodicConvolution f (fejerKernel N) x| := by
    intro x
    have : f x - periodicConvolution f (fejerKernel N) x =
      (f x - g x) + (g x - periodicConvolution g (fejerKernel N) x) +
      (periodicConvolution g (fejerKernel N) x -
        periodicConvolution f (fejerKernel N) x) := by ring
    rw [this]
    calc |(f x - g x) + (g x - periodicConvolution g (fejerKernel N) x) +
          (periodicConvolution g (fejerKernel N) x -
            periodicConvolution f (fejerKernel N) x)|
        ≤ |(f x - g x) + (g x - periodicConvolution g (fejerKernel N) x)| +
          |periodicConvolution g (fejerKernel N) x -
            periodicConvolution f (fejerKernel N) x| :=
          abs_add_le _ _
      _ ≤ (|f x - g x| + |g x - periodicConvolution g (fejerKernel N) x|) +
          |periodicConvolution g (fejerKernel N) x -
            periodicConvolution f (fejerKernel N) x| := by
          linarith [abs_add_le (f x - g x)
            (g x - periodicConvolution g (fejerKernel N) x)]

  have h_intble_sum :=
    ((intble_diff_abs f g hf_intble hg_cont hg_per).add
      (intble_cts_conv g N hg_cont hg_per)).add
      (intble_conv_diff f g N hf_periodic hf_intble hg_cont hg_per)


  have t1 : (1 / (2 * π)) * ∫ x in (-π)..π, |f x - g x| ≤ ε / 4 := hg_approx

  have t2 : (1 / (2 * π)) * ∫ x in (-π)..π,
      |g x - periodicConvolution g (fejerKernel N) x| ≤ ε / 4 := by
    calc (1 / (2 * π)) * ∫ x in (-π)..π,
          |g x - periodicConvolution g (fejerKernel N) x|
        ≤ (1 / (2 * π)) * ∫ x in (-π)..π, (ε / 4 : ℝ) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity)
          exact integral_mono_on hpi_le (intble_cts_conv g N hg_cont hg_per)
            _root_.intervalIntegrable_const (fun x _ => hN₀ N hN x)
      _ = ε / 4 := by
          rw [intervalIntegral.integral_const, sub_neg_eq_add, smul_eq_mul]
          have : π ≠ 0 := ne_of_gt pi_pos; field_simp; ring

  have t3 : (1 / (2 * π)) * ∫ x in (-π)..π,
      |periodicConvolution g (fejerKernel N) x -
        periodicConvolution f (fejerKernel N) x| ≤ ε / 4 := by
    have h_eq : (fun x => |periodicConvolution g (fejerKernel N) x -
        periodicConvolution f (fejerKernel N) x|) =
        (fun x => |periodicConvolution (fun y => g y - f y) (fejerKernel N) x|) := by
      ext x; rw [convolution_linear g f N x (conv_intble_of_continuous g hg_cont N x)
        (conv_intble_of_periodic f hf_periodic hf_intble N x)]
    rw [h_eq]
    calc periodicL1Norm
          (periodicConvolution (fun y => g y - f y) (fejerKernel N))
        ≤ periodicL1Norm (fun y => g y - f y) :=
          young_fejerKernel _ N (intble_diff f g hf_intble hg_cont hg_per)
            (hg_per.sub hf_periodic)
      _ = periodicL1Norm (fun y => f y - g y) := periodicL1Norm_sub_comm g f
      _ ≤ ε / 4 := hg_approx

  calc (1 / (2 * π)) * ∫ x in (-π)..π,
        |f x - periodicConvolution f (fejerKernel N) x|
      ≤ (1 / (2 * π)) * ∫ x in (-π)..π,
          (|f x - g x| + |g x - periodicConvolution g (fejerKernel N) x| +
            |periodicConvolution g (fejerKernel N) x -
              periodicConvolution f (fejerKernel N) x|) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact integral_mono_on hpi_le
          (intble_result f N hf_periodic hf_intble) h_intble_sum
          (fun x _ => h_pw x)
    _ = (1 / (2 * π)) * (∫ x in (-π)..π, |f x - g x|) +
        (1 / (2 * π)) * (∫ x in (-π)..π,
          |g x - periodicConvolution g (fejerKernel N) x|) +
        (1 / (2 * π)) * ∫ x in (-π)..π,
          |periodicConvolution g (fejerKernel N) x -
            periodicConvolution f (fejerKernel N) x| := by
        rw [intervalIntegral.integral_add
              ((intble_diff_abs f g hf_intble hg_cont hg_per).add
                (intble_cts_conv g N hg_cont hg_per))
              (intble_conv_diff f g N hf_periodic hf_intble hg_cont hg_per),
            intervalIntegral.integral_add
              (intble_diff_abs f g hf_intble hg_cont hg_per)
              (intble_cts_conv g N hg_cont hg_per)]
        ring
    _ ≤ ε / 4 + ε / 4 + ε / 4 := by linarith
    _ < ε := by linarith

end FejerL1Density

end


/-! ### Inlined Dirichlet/Fejer statements and proofs. -/


open Filter Topology MeasureTheory intervalIntegral
open scoped BigOperators FourierTransform

noncomputable section

/-- Symmetric Fourier partial sums in the Dirichlet-kernel convolution form used
by the proof below. -/
def fourierPartialSumKernel (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ y in (-Real.pi)..Real.pi,
      f (x - y) *
        ((1 + 2 * ∑ k ∈ Finset.range N, Real.cos ((k + 1 : ℝ) * y)) : ℂ)

/-- Cesaro means represented by convolution with the Fejér kernel on one period. -/
def fourierCesaroMeanKernel (f : ℝ → ℂ) (N : ℕ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ y in (-Real.pi)..Real.pi, f (x - y) * (FejerL1Density.fejerKernel N y : ℂ)

/-!
## Blueprint API for the two target theorems

The declarations below are a proof plan written as Lean API.  They are more
fine-grained than the final two target theorems: each lemma isolates one step
that will likely be needed when replacing the placeholders above by genuine
Fourier definitions.

The final `dirichlet_pointwise` and `fejer` statements at the bottom are kept
textually unchanged.
-/

namespace DirichletFejerBlueprint

/-! ### Basic analytic definitions -/

/-- Complex-valued periodic convolution against a real kernel on `[-π, π]`. -/
def complexPeriodicConvolution (f : ℝ → ℂ) (K : ℝ → ℝ) (x : ℝ) : ℂ :=
  (1 / (2 * Real.pi) : ℂ) *
    ∫ y in (-Real.pi)..Real.pi, f (x - y) * (K y : ℂ)

/-- The real Dirichlet kernel in the same indexing convention as the existing
`FejerL1Density.dirichlet_identity`. -/
def dirichletKernel (N : ℕ) (t : ℝ) : ℝ :=
  1 + 2 * ∑ k ∈ Finset.range N, Real.cos ((k + 1 : ℝ) * t)

/-- The oscillatory sine factor appearing after multiplying the Dirichlet kernel
by `sin (t / 2)`. -/
def dirichletOscillation (N : ℕ) (t : ℝ) : ℝ :=
  Real.sin ((2 * (N : ℝ) + 1) * (t / 2))

/-- The Dirichlet kernel is `2π`-periodic. -/
lemma dirichletKernel_periodic (N : ℕ) :
    Function.Periodic (dirichletKernel N) (2 * Real.pi) := by
  intro t
  unfold dirichletKernel
  congr 1
  congr 1
  apply Finset.sum_congr rfl
  intro k _hk
  have hcos := (Real.cos_periodic.nat_mul (k + 1)) (((k + 1 : ℕ) : ℝ) * t)
  convert hcos using 1
  · push_cast
    ring_nf
  · push_cast
    ring_nf

/-- A single Fourier coefficient term as an ordinary interval integral. -/
lemma fourierCoeffOn_exp_eq_integral (f : ℝ → ℂ) (n : ℤ) (x : ℝ) :
    fourierCoeffOn Real.two_pi_pos f n *
        Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)) =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t in (0 : ℝ)..(2 * Real.pi),
          f t * Complex.exp (Complex.I * (n : ℂ) * ((x - t : ℝ) : ℂ)) := by
  rw [fourierCoeffOn_eq_integral]
  simp only [sub_zero]
  change (((1 / (2 * Real.pi) : ℝ) •
        ∫ t in (0 : ℝ)..(2 * Real.pi),
          (fourier (-n)) (t : AddCircle (2 * Real.pi - 0)) • f t) *
      Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))) = _
  rw [Complex.real_smul]
  norm_cast
  simp only [smul_eq_mul]
  rw [mul_assoc]
  congr 1
  trans ∫ t in (0 : ℝ)..(2 * Real.pi),
      ((fourier (-n)) (t : AddCircle (2 * Real.pi - 0)) * f t) *
        Complex.exp (Complex.I * (n : ℂ) * (x : ℂ))
  · exact (intervalIntegral.integral_mul_const (a := (0 : ℝ)) (b := 2 * Real.pi)
      (μ := volume) (r := Complex.exp (Complex.I * (n : ℂ) * (x : ℂ)))
      (f := fun t : ℝ =>
        (fourier (-n)) (t : AddCircle (2 * Real.pi - 0)) * f t)).symm
  · congr 1
    funext t
    rw [fourier_coe_apply]
    simp only [Int.cast_neg]
    calc
      Complex.exp (2 * ↑Real.pi * Complex.I * -↑n * ↑t / ↑(2 * Real.pi - 0)) *
            f t * Complex.exp (Complex.I * ↑n * ↑x)
          = f t *
              (Complex.exp
                  (2 * ↑Real.pi * Complex.I * -↑n * ↑t / ↑(2 * Real.pi - 0)) *
                Complex.exp (Complex.I * ↑n * ↑x)) := by
              ring
      _ = f t * Complex.exp (Complex.I * ↑n * ↑(x - t)) := by
          rw [← Complex.exp_add]
          apply congrArg (fun z : ℂ => f t * Complex.exp z)
          have hpi2 : (↑(Real.pi * 2) : ℂ) ≠ 0 := by
            norm_num [Real.pi_ne_zero]
          field_simp [hpi2]
          push_cast
          ring_nf

/-- The two endpoint exponentials added when enlarging a symmetric partial sum. -/
lemma exp_pair_succ (N : ℕ) (t : ℝ) :
    Complex.exp (-(↑t * Complex.I) - ↑t * Complex.I * ↑N) +
      Complex.exp (↑t * Complex.I + ↑t * Complex.I * ↑N) =
        (2 * Real.cos (((N + 1 : ℕ) : ℝ) * t) : ℂ) := by
  have hpos : Complex.exp (↑t * Complex.I + ↑t * Complex.I * ↑N) =
      Complex.exp (((((N + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  have hneg : Complex.exp (-(↑t * Complex.I) - ↑t * Complex.I * ↑N) =
      Complex.exp (-(((((N + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I)) := by
    congr 1
    push_cast
    ring
  rw [hneg, hpos]
  rw [show -(((((N + 1 : ℕ) : ℝ) * t : ℝ) : ℂ) * Complex.I) =
      (((-(((N + 1 : ℕ) : ℝ) * t) : ℝ) : ℂ) * Complex.I) by
        push_cast
        ring]
  rw [Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  simp [Real.cos_neg, Real.sin_neg]
  ring

/-- The symmetric exponential sum is the Dirichlet kernel. -/
lemma exp_sum_Icc_eq_dirichlet (N : ℕ) (t : ℝ) :
    (∑ n ∈ Finset.Icc (-(N : ℤ)) N,
      Complex.exp (Complex.I * (n : ℂ) * (t : ℂ))) = (dirichletKernel N t : ℂ) := by
  induction N with
  | zero =>
      simp [dirichletKernel]
  | succ N ih =>
      have hI : Finset.Icc (-(↑(N + 1) : ℤ)) (↑(N + 1) : ℤ) =
          Finset.Icc (-(N : ℤ)) (N : ℤ) ∪
            {(-(N + 1 : ℤ) : ℤ), ((N + 1 : ℕ) : ℤ)} := by
        simpa using (Finset.Icc_succ_succ N N)
      rw [hI, Finset.sum_union]
      · rw [ih, Finset.sum_pair]
        · rw [show
              Complex.exp (Complex.I * ((-(↑N + 1) : ℤ) : ℂ) * ↑t) =
                Complex.exp (-(↑t * Complex.I) - ↑t * Complex.I * ↑N) by
                congr 1
                push_cast
                ring]
          rw [show
              Complex.exp (Complex.I * ((↑(N + 1) : ℤ) : ℂ) * ↑t) =
                Complex.exp (↑t * Complex.I + ↑t * Complex.I * ↑N) by
                congr 1
                push_cast
                ring]
          rw [exp_pair_succ]
          simp [dirichletKernel, Finset.sum_range_succ]
          ring
        · omega
      · rw [Finset.disjoint_iff_ne]
        intro a ha b hb
        simp only [Finset.mem_Icc] at ha
        simp only [Finset.mem_insert, Finset.mem_singleton] at hb
        rcases hb with rfl | rfl <;> omega

/-- Coefficient partial sums as Dirichlet-kernel integrals over `[0, 2π]`. -/
lemma fourierPartialSum_eq_integral_dirichlet
    {f : ℝ → ℂ} (hf : Continuous f) (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x =
      (1 / (2 * Real.pi) : ℂ) * ∫ t in (0 : ℝ)..(2 * Real.pi),
        f t * (dirichletKernel N (x - t) : ℂ) := by
  unfold fourierPartialSum _root_.LeanEval.Analysis.fourierPartialSum
  simp_rw [fourierCoeffOn_exp_eq_integral]
  rw [← Finset.mul_sum]
  congr 1
  let s := Finset.Icc (-(N : ℤ)) (N : ℤ)
  have hint : ∀ n ∈ s, IntervalIntegrable
      (fun t : ℝ => f t * Complex.exp (Complex.I * (n : ℂ) * ((x - t : ℝ) : ℂ)))
      volume 0 (2 * Real.pi) := by
    intro n _hn
    have harg : Continuous (fun t : ℝ => Complex.I * (n : ℂ) * ((x - t : ℝ) : ℂ)) := by
      exact (continuous_const.mul continuous_const).mul
        (Complex.continuous_ofReal.comp (continuous_const.sub continuous_id))
    exact (hf.mul (Complex.continuous_exp.comp harg)).intervalIntegrable _ _
  trans ∫ t in (0 : ℝ)..(2 * Real.pi),
      ∑ n ∈ s, f t * Complex.exp (Complex.I * (n : ℂ) * ((x - t : ℝ) : ℂ))
  · exact (intervalIntegral.integral_finset_sum hint).symm
  · congr 1
    funext t
    rw [← Finset.mul_sum]
    rw [exp_sum_Icc_eq_dirichlet]

/-- Shift the `[0, 2π]` Dirichlet integral to the `[-π, π]` convolution window. -/
lemma integral_shift_dirichlet
    {f : ℝ → ℂ} (hperiod : Function.Periodic f (2 * Real.pi)) (N : ℕ) (x : ℝ) :
    ∫ t in (0 : ℝ)..(2 * Real.pi), f t * (dirichletKernel N (x - t) : ℂ) =
      ∫ y in (-Real.pi)..Real.pi, f (x - y) * (dirichletKernel N y : ℂ) := by
  let g : ℝ → ℂ := fun y => f (x - y) * (dirichletKernel N y : ℂ)
  have hgper : Function.Periodic g (2 * Real.pi) := by
    intro y
    dsimp [g]
    have hfshift : f (x - (y + 2 * Real.pi)) = f (x - y) := by
      convert hperiod.sub_eq (x - y) using 1
      ring
    rw [hfshift]
    have hD := dirichletKernel_periodic N y
    rw [hD]
  trans ∫ t in (0 : ℝ)..(2 * Real.pi), g (x - t)
  · congr 1
    funext t
    dsimp [g]
    congr 2
    ring
  · rw [intervalIntegral.integral_comp_sub_left]
    have hperint := hgper.intervalIntegral_add_eq (x - 2 * Real.pi) (-Real.pi)
    simpa [g, show x - (0 : ℝ) = x by ring,
      show x - 2 * Real.pi + 2 * Real.pi = x by ring,
      show (-Real.pi : ℝ) + 2 * Real.pi = Real.pi by ring] using hperint

/-- The exact `lean-eval` partial sum agrees with the kernel partial sum. -/
lemma fourierPartialSum_eq_fourierPartialSumKernel
    {f : ℝ → ℂ} (hperiod : Function.Periodic f (2 * Real.pi)) (hcont : Continuous f)
    (N : ℕ) (x : ℝ) :
    fourierPartialSum f N x = fourierPartialSumKernel f N x := by
  rw [fourierPartialSum_eq_integral_dirichlet hcont N x]
  rw [integral_shift_dirichlet hperiod N x]
  simp [fourierPartialSumKernel, dirichletKernel]

/-- Averaging the kernel partial sums gives the Fejér-kernel convolution with
parameter shifted by one, matching the `lean-eval` Cesaro convention. -/
lemma average_fourierPartialSumKernel_eq_fourierCesaroMeanKernel
    {f : ℝ → ℂ} (hcont : Continuous f) (N : ℕ) (x : ℝ) :
    (∑ k ∈ Finset.range (N + 1), fourierPartialSumKernel f k x) / (N + 1 : ℂ) =
      fourierCesaroMeanKernel f (N + 1) x := by
  have hint : ∀ k ∈ Finset.range (N + 1), IntervalIntegrable
      (fun y : ℝ => f (x - y) * (dirichletKernel k y : ℂ)) volume
        (-Real.pi) Real.pi := by
    intro k _hk
    have hD : Continuous fun y : ℝ => (dirichletKernel k y : ℂ) := by
      unfold dirichletKernel
      continuity
    exact ((hcont.comp (continuous_const.sub continuous_id)).mul hD).intervalIntegrable _ _
  unfold fourierPartialSumKernel fourierCesaroMeanKernel
  have hDexpr : ∀ k y,
      (1 + 2 * ↑(∑ j ∈ Finset.range k, Real.cos ((j + 1 : ℝ) * y)) : ℂ) =
        (dirichletKernel k y : ℂ) := by
    intro k y
    simp [dirichletKernel]
  simp_rw [hDexpr]
  change
    (∑ k ∈ Finset.range (N + 1),
        (1 / (2 * Real.pi) : ℂ) *
          ∫ y in (-Real.pi)..Real.pi, f (x - y) * (dirichletKernel k y : ℂ)) /
        (N + 1 : ℂ) =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ y in (-Real.pi)..Real.pi,
          f (x - y) * (FejerL1Density.fejerKernel (N + 1) y : ℂ)
  rw [← Finset.mul_sum]
  rw [div_eq_mul_inv]
  rw [mul_assoc]
  congr 1
  trans (N + 1 : ℂ)⁻¹ * ∑ k ∈ Finset.range (N + 1),
      ∫ y in (-Real.pi)..Real.pi, f (x - y) * (dirichletKernel k y : ℂ)
  · ring
  trans (N + 1 : ℂ)⁻¹ * ∫ y in (-Real.pi)..Real.pi,
      ∑ k ∈ Finset.range (N + 1), f (x - y) * (dirichletKernel k y : ℂ)
  · rw [intervalIntegral.integral_finset_sum hint]
  trans ∫ y in (-Real.pi)..Real.pi,
      (N + 1 : ℂ)⁻¹ *
        (∑ k ∈ Finset.range (N + 1), f (x - y) * (dirichletKernel k y : ℂ))
  · exact (intervalIntegral.integral_const_mul (a := -Real.pi) (b := Real.pi)
      (μ := volume) (r := (N + 1 : ℂ)⁻¹)
      (f := fun y : ℝ => ∑ k ∈ Finset.range (N + 1),
        f (x - y) * (dirichletKernel k y : ℂ))).symm
  · congr 1
    funext y
    rw [FejerL1Density.fejerKernel_eq_dirichlet_avg (N + 1) (Nat.succ_ne_zero N) y]
    rw [← Finset.mul_sum]
    simp [dirichletKernel]
    ring

/-- The exact `lean-eval` Cesaro mean is the kernel Fejér mean with parameter
`N + 1`. -/
lemma fourierCesaroMean_eq_fourierCesaroMeanKernel_succ
    {f : ℝ → ℂ} (hperiod : Function.Periodic f (2 * Real.pi)) (hcont : Continuous f)
    (N : ℕ) :
    fourierCesaroMean f N = fourierCesaroMeanKernel f (N + 1) := by
  funext x
  unfold fourierCesaroMean _root_.LeanEval.Analysis.fourierCesaroMean
  simp_rw [fourierPartialSum_eq_fourierPartialSumKernel hperiod hcont]
  exact average_fourierPartialSumKernel_eq_fourierCesaroMeanKernel hcont N x

/-- Difference quotient for the Dirichlet proof, away from the removable
singularity at `t = 0`.  The real proof should replace this by a continuous
extension. -/
def dirichletDifferenceQuotient (f : ℝ → ℂ) (x t : ℝ) : ℂ :=
  (f (x - t) - f x) / (Real.sin (t / 2) : ℂ)

/-- Continuous extension of `-t / sin (t / 2)` at the origin. -/
def dirichletSincFactor : ℝ → ℂ :=
  Function.update (fun t : ℝ => (-(t : ℂ)) / (Real.sin (t / 2) : ℂ)) 0 (-2 : ℂ)

/-! ### Fejér: connecting the target API to existing real-valued code -/

/-- The kernel-form Cesaro mean is the complex Fejér convolution using the
already-developed periodic Fejér kernel. -/
lemma fourierCesaroMeanKernel_eq_complex_fejer_convolution
    (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    fourierCesaroMeanKernel f N x =
      complexPeriodicConvolution f (FejerL1Density.fejerKernel N) x := by
  rfl

/-- Real part of a continuous complex-valued function is continuous. -/
lemma continuous_re_of_complex {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous fun x => (f x).re := by
  exact Complex.continuous_re.comp hf

/-- Imaginary part of a continuous complex-valued function is continuous. -/
lemma continuous_im_of_complex {f : ℝ → ℂ} (hf : Continuous f) :
    Continuous fun x => (f x).im := by
  exact Complex.continuous_im.comp hf

/-- Real part of a periodic complex-valued function is periodic. -/
lemma periodic_re_of_complex {f : ℝ → ℂ} {p : ℝ} (hf : Function.Periodic f p) :
    Function.Periodic (fun x => (f x).re) p := by
  intro x
  exact congrArg Complex.re (hf x)

/-- Imaginary part of a periodic complex-valued function is periodic. -/
lemma periodic_im_of_complex {f : ℝ → ℂ} {p : ℝ} (hf : Function.Periodic f p) :
    Function.Periodic (fun x => (f x).im) p := by
  intro x
  exact congrArg Complex.im (hf x)

/-- Pulling real part through the interval integral in the Fejér convolution. -/
lemma complex_fejer_integral_re
    (f : ℝ → ℂ) (N : ℕ) (x : ℝ)
    (hint : IntervalIntegrable
      (fun y => f (x - y) * (FejerL1Density.fejerKernel N y : ℂ))
      volume (-Real.pi) Real.pi) :
    (∫ y in (-Real.pi)..Real.pi,
        f (x - y) * (FejerL1Density.fejerKernel N y : ℂ)).re =
      ∫ y in (-Real.pi)..Real.pi,
        (f (x - y)).re * FejerL1Density.fejerKernel N y := by
  have hlin := (Complex.reCLM.intervalIntegral_comp_comm hint).symm
  simpa [Complex.reCLM_apply, Complex.mul_re] using hlin

/-- Pulling imaginary part through the interval integral in the Fejér convolution. -/
lemma complex_fejer_integral_im
    (f : ℝ → ℂ) (N : ℕ) (x : ℝ)
    (hint : IntervalIntegrable
      (fun y => f (x - y) * (FejerL1Density.fejerKernel N y : ℂ))
      volume (-Real.pi) Real.pi) :
    (∫ y in (-Real.pi)..Real.pi,
        f (x - y) * (FejerL1Density.fejerKernel N y : ℂ)).im =
      ∫ y in (-Real.pi)..Real.pi,
        (f (x - y)).im * FejerL1Density.fejerKernel N y := by
  have hlin := (Complex.imCLM.intervalIntegral_comp_comm hint).symm
  simpa [Complex.imCLM_apply, Complex.mul_im] using hlin

/-- Real part of complex Fejér convolution reduces to the existing real-valued
periodic convolution in `FejerL1Density`. -/
lemma complex_fejer_convolution_re
    (f : ℝ → ℂ) (N : ℕ) (x : ℝ)
    (hint : IntervalIntegrable
      (fun y => f (x - y) * (FejerL1Density.fejerKernel N y : ℂ))
      volume (-Real.pi) Real.pi) :
    (complexPeriodicConvolution f (FejerL1Density.fejerKernel N) x).re =
      FejerL1Density.periodicConvolution
        (fun t => (f t).re) (FejerL1Density.fejerKernel N) x := by
  unfold complexPeriodicConvolution FejerL1Density.periodicConvolution
  simp [Complex.mul_re, complex_fejer_integral_re f N x hint]

/-- Imaginary part of complex Fejér convolution reduces to the existing real-valued
periodic convolution in `FejerL1Density`. -/
lemma complex_fejer_convolution_im
    (f : ℝ → ℂ) (N : ℕ) (x : ℝ)
    (hint : IntervalIntegrable
      (fun y => f (x - y) * (FejerL1Density.fejerKernel N y : ℂ))
      volume (-Real.pi) Real.pi) :
    (complexPeriodicConvolution f (FejerL1Density.fejerKernel N) x).im =
      FejerL1Density.periodicConvolution
        (fun t => (f t).im) (FejerL1Density.fejerKernel N) x := by
  unfold complexPeriodicConvolution FejerL1Density.periodicConvolution
  simp [Complex.mul_im, complex_fejer_integral_im f N x hint]

private lemma complex_fejer_integrand_intervalIntegrable_of_continuous
    {f : ℝ → ℂ} (hcont : Continuous f) (N : ℕ) (x : ℝ) :
    IntervalIntegrable
      (fun y => f (x - y) * (FejerL1Density.fejerKernel N y : ℂ))
      volume (-Real.pi) Real.pi := by
  have hKc : IntervalIntegrable (fun y => (FejerL1Density.fejerKernel N y : ℂ))
      volume (-Real.pi) Real.pi := by
    rw [intervalIntegrable_iff] at *
    exact (FejerL1Density.fejerKernel_intervalIntegrable N).def'.ofReal
  simpa [mul_comm] using
    hKc.continuousOn_mul ((hcont.comp (continuous_const.sub continuous_id)).continuousOn)

private lemma complex_fejer_convolution_re_of_continuous
    {f : ℝ → ℂ} (hcont : Continuous f) (N : ℕ) (x : ℝ) :
    (complexPeriodicConvolution f (FejerL1Density.fejerKernel N) x).re =
      FejerL1Density.periodicConvolution
        (fun t => (f t).re) (FejerL1Density.fejerKernel N) x := by
  have hφ := complex_fejer_integrand_intervalIntegrable_of_continuous hcont N x
  have hre : (∫ y in (-Real.pi)..Real.pi,
        f (x - y) * (FejerL1Density.fejerKernel N y : ℂ)).re =
      ∫ y in (-Real.pi)..Real.pi,
        (f (x - y)).re * FejerL1Density.fejerKernel N y := by
    have hlin := (Complex.reCLM.intervalIntegral_comp_comm hφ).symm
    simpa [Complex.mul_re] using hlin
  unfold complexPeriodicConvolution FejerL1Density.periodicConvolution
  simp [Complex.mul_re, hre]

private lemma complex_fejer_convolution_im_of_continuous
    {f : ℝ → ℂ} (hcont : Continuous f) (N : ℕ) (x : ℝ) :
    (complexPeriodicConvolution f (FejerL1Density.fejerKernel N) x).im =
      FejerL1Density.periodicConvolution
        (fun t => (f t).im) (FejerL1Density.fejerKernel N) x := by
  have hφ := complex_fejer_integrand_intervalIntegrable_of_continuous hcont N x
  have him : (∫ y in (-Real.pi)..Real.pi,
        f (x - y) * (FejerL1Density.fejerKernel N y : ℂ)).im =
      ∫ y in (-Real.pi)..Real.pi,
        (f (x - y)).im * FejerL1Density.fejerKernel N y := by
    have hlin := (Complex.imCLM.intervalIntegral_comp_comm hφ).symm
    simpa [Complex.mul_im] using hlin
  unfold complexPeriodicConvolution FejerL1Density.periodicConvolution
  simp [Complex.mul_im, him]

/-- Elementary estimate used to combine real and imaginary uniform convergence
into complex uniform convergence. -/
lemma complex_norm_le_re_im (z : ℂ) :
    ‖z‖ ≤ |z.re| + |z.im| := by
  calc
    ‖z‖ = ‖(z.re : ℂ) + (z.im : ℂ) * Complex.I‖ := by
      rw [Complex.re_add_im]
    _ ≤ ‖(z.re : ℂ)‖ + ‖(z.im : ℂ) * Complex.I‖ := norm_add_le _ _
    _ = |z.re| + |z.im| := by simp

/-- A useful packaging lemma: if real and imaginary parts converge uniformly,
then the complex-valued functions converge uniformly. -/
theorem tendstoUniformly_complex_of_re_im
    {u : ℕ → ℝ → ℂ} {f : ℝ → ℂ}
    (hre : TendstoUniformly (fun N x => (u N x).re) (fun x => (f x).re) atTop)
    (him : TendstoUniformly (fun N x => (u N x).im) (fun x => (f x).im) atTop) :
    TendstoUniformly u f atTop := by
  rw [Metric.tendstoUniformly_iff]
  rw [Metric.tendstoUniformly_iff] at hre him
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  filter_upwards [hre (ε / 2) hε2, him (ε / 2) hε2] with N hNre hNim x
  have hre_abs : |(f x - u N x).re| < ε / 2 := by
    simpa [Real.dist_eq, Complex.sub_re] using hNre x
  have him_abs : |(f x - u N x).im| < ε / 2 := by
    simpa [Real.dist_eq, Complex.sub_im] using hNim x
  calc
    dist (f x) (u N x) = ‖f x - u N x‖ := by rw [dist_eq_norm]
    _ ≤ |(f x - u N x).re| + |(f x - u N x).im| := complex_norm_le_re_im _
    _ < ε := by linarith

/-- Real-part Fejér convergence obtained directly from the existing real theorem
`FejerL1Density.fejer_uniform_convergence`. -/
theorem fejer_uniform_convergence_re
    {f : ℝ → ℂ} (hperiod : Function.Periodic f (2 * Real.pi))
    (hcont : Continuous f) :
    TendstoUniformly
      (fun N x =>
        (complexPeriodicConvolution f (FejerL1Density.fejerKernel N) x).re)
      (fun x => (f x).re) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := FejerL1Density.fejer_uniform_convergence
    (fun x => (f x).re) (continuous_re_of_complex hcont)
    (periodic_re_of_complex hperiod) (ε / 2) (by linarith)
  filter_upwards [eventually_atTop.2 ⟨N₀, fun N hN => hN⟩] with N hN x
  have h := hN₀ N hN x
  have hlt : |(f x).re -
      FejerL1Density.periodicConvolution
        (fun t => (f t).re) (FejerL1Density.fejerKernel N) x| < ε := by
    linarith
  simpa [Real.dist_eq, complex_fejer_convolution_re_of_continuous hcont N x] using hlt

/-- Imaginary-part Fejér convergence obtained directly from the existing real
theorem `FejerL1Density.fejer_uniform_convergence`. -/
theorem fejer_uniform_convergence_im
    {f : ℝ → ℂ} (hperiod : Function.Periodic f (2 * Real.pi))
    (hcont : Continuous f) :
    TendstoUniformly
      (fun N x =>
        (complexPeriodicConvolution f (FejerL1Density.fejerKernel N) x).im)
      (fun x => (f x).im) atTop := by
  rw [Metric.tendstoUniformly_iff]
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := FejerL1Density.fejer_uniform_convergence
    (fun x => (f x).im) (continuous_im_of_complex hcont)
    (periodic_im_of_complex hperiod) (ε / 2) (by linarith)
  filter_upwards [eventually_atTop.2 ⟨N₀, fun N hN => hN⟩] with N hN x
  have h := hN₀ N hN x
  have hlt : |(f x).im -
      FejerL1Density.periodicConvolution
        (fun t => (f t).im) (FejerL1Density.fejerKernel N) x| < ε := by
    linarith
  simpa [Real.dist_eq, complex_fejer_convolution_im_of_continuous hcont N x] using hlt

/-- Complex Fejér convergence, packaged from real and imaginary convergence. -/
theorem complex_fejer_uniform_convergence
    {f : ℝ → ℂ} (hperiod : Function.Periodic f (2 * Real.pi))
    (hcont : Continuous f) :
    TendstoUniformly
      (fun N : ℕ => complexPeriodicConvolution f (FejerL1Density.fejerKernel N))
      f atTop := by
  exact tendstoUniformly_complex_of_re_im
    (fejer_uniform_convergence_re hperiod hcont)
    (fejer_uniform_convergence_im hperiod hcont)

/-- Final Fejér assembly for the kernel-convolution Cesaro mean. -/
theorem fejer_from_blueprint
    {f : ℝ → ℂ} (hperiod : Function.Periodic f (2 * Real.pi))
    (hcont : Continuous f) :
    TendstoUniformly (fun N : ℕ => fourierCesaroMeanKernel f N) f atTop := by
  refine (tendstoUniformly_congr ?_).mpr
    (complex_fejer_uniform_convergence hperiod hcont)
  filter_upwards with N
  funext x
  exact fourierCesaroMeanKernel_eq_complex_fejer_convolution f N x

/-! ### Dirichlet: Fourier partial sums as Dirichlet-kernel convolutions -/

/-- If Fourier partial sums are defined by coefficients, this is the bridge to
the Dirichlet-kernel convolution formula. -/
lemma fourierPartialSum_eq_dirichlet_convolution
    (f : ℝ → ℂ) (N : ℕ) (x : ℝ) :
    fourierPartialSumKernel f N x =
      complexPeriodicConvolution f (dirichletKernel N) x := by
  simp [fourierPartialSumKernel, complexPeriodicConvolution, dirichletKernel]

/-- The Dirichlet kernel integrates to `2π`.  This should be derived from
`FejerL1Density.integral_dirichlet_sum`. -/
lemma dirichletKernel_integral (N : ℕ) :
    ∫ t in (-Real.pi)..Real.pi, dirichletKernel N t = 2 * Real.pi := by
  simpa [dirichletKernel] using FejerL1Density.integral_dirichlet_sum N

/-- Complex form of `dirichletKernel_integral`, after coercion to `ℂ`. -/
lemma dirichletKernel_integral_complex (N : ℕ) :
    ∫ t in (-Real.pi)..Real.pi, (dirichletKernel N t : ℂ) =
      (2 * Real.pi : ℂ) := by
  rw [intervalIntegral.integral_ofReal]
  exact_mod_cast dirichletKernel_integral N

/-- Normalized complex Dirichlet kernel has integral `1`. -/
lemma dirichletKernel_normalized_integral_complex (N : ℕ) :
    (1 / (2 * Real.pi) : ℂ) *
      ∫ t in (-Real.pi)..Real.pi, (dirichletKernel N t : ℂ) = 1 := by
  rw [dirichletKernel_integral_complex]
  have h : (2 * Real.pi : ℂ) ≠ 0 := by
    exact_mod_cast (mul_ne_zero two_ne_zero Real.pi_ne_zero)
  field_simp [h]

/-- Subtracting `f x` from a Dirichlet convolution moves the subtraction inside
the integral, using `dirichletKernel_integral`. -/
lemma dirichlet_convolution_sub_eq
    (f : ℝ → ℂ) (N : ℕ) (x : ℝ) (hcont : Continuous f) :
    fourierPartialSumKernel f N x - f x =
      (1 / (2 * Real.pi) : ℂ) *
        ∫ t in (-Real.pi)..Real.pi,
          (f (x - t) - f x) * (dirichletKernel N t : ℂ) := by
  unfold fourierPartialSumKernel
  rw [show
      (∫ y in (-Real.pi)..Real.pi,
        f (x - y) *
          (1 + 2 * ↑(∑ k ∈ Finset.range N, Real.cos ((↑k + 1) * y)))) =
        ∫ y in (-Real.pi)..Real.pi, f (x - y) * (dirichletKernel N y : ℂ) by
    congr 1
    ext y
    simp [dirichletKernel]]
  set K : ℝ → ℂ := fun t => (dirichletKernel N t : ℂ)
  have hKcont : Continuous K := by
    dsimp [K]
    unfold dirichletKernel
    fun_prop
  have hfK : IntervalIntegrable (fun t => f (x - t) * K t)
      volume (-Real.pi) Real.pi := by
    exact ((hcont.comp (continuous_const.sub continuous_id)).mul hKcont).intervalIntegrable _ _
  have hconstK : IntervalIntegrable (fun t => f x * K t)
      volume (-Real.pi) Real.pi := by
    exact (hKcont.intervalIntegrable _ _).const_mul (f x)
  have hsubint :
      ∫ t in (-Real.pi)..Real.pi, (f (x - t) - f x) * K t =
        (∫ t in (-Real.pi)..Real.pi, f (x - t) * K t) -
          f x * ∫ t in (-Real.pi)..Real.pi, K t := by
    have hpoint :
        (fun t => (f (x - t) - f x) * K t) =
          fun t => f (x - t) * K t - f x * K t := by
      funext t
      ring
    have hconst_int :
        ∫ t in (-Real.pi)..Real.pi, f x * K t =
          f x * ∫ t in (-Real.pi)..Real.pi, K t := by
      exact intervalIntegral.integral_const_mul (a := -Real.pi) (b := Real.pi)
        (r := f x) (f := K) (μ := volume)
    rw [hpoint, intervalIntegral.integral_sub hfK hconstK, hconst_int]
  have hnorm :
      (1 / (2 * Real.pi) : ℂ) * ∫ t in (-Real.pi)..Real.pi, K t = 1 := by
    dsimp [K]
    simpa [dirichletKernel] using dirichletKernel_normalized_integral_complex N
  change (1 / (2 * Real.pi) : ℂ) *
      (∫ t in (-Real.pi)..Real.pi, f (x - t) * K t) - f x =
    (1 / (2 * Real.pi) : ℂ) *
      ∫ t in (-Real.pi)..Real.pi, (f (x - t) - f x) * K t
  rw [hsubint]
  calc
    (1 / (2 * Real.pi) : ℂ) *
        (∫ t in (-Real.pi)..Real.pi, f (x - t) * K t) - f x =
        (1 / (2 * Real.pi) : ℂ) *
          (∫ t in (-Real.pi)..Real.pi, f (x - t) * K t) -
          ((1 / (2 * Real.pi) : ℂ) * ∫ t in (-Real.pi)..Real.pi, K t) * f x := by
      rw [hnorm, one_mul]
    _ = (1 / (2 * Real.pi) : ℂ) *
        ((∫ t in (-Real.pi)..Real.pi, f (x - t) * K t) -
          f x * ∫ t in (-Real.pi)..Real.pi, K t) := by ring

/-- Dirichlet kernel sine identity, repackaged from
`FejerL1Density.dirichlet_identity`. -/
lemma dirichletKernel_mul_sin_half (N : ℕ) (t : ℝ) :
    Real.sin (t / 2) * dirichletKernel N t =
      dirichletOscillation N t := by
  unfold dirichletKernel dirichletOscillation
  rw [FejerL1Density.dirichlet_identity N t]
  ring

/-- Complex-coerced version of the sine identity. -/
lemma dirichletKernel_mul_sin_half_complex (N : ℕ) (t : ℝ) :
    (Real.sin (t / 2) : ℂ) * (dirichletKernel N t : ℂ) =
      (dirichletOscillation N t : ℂ) := by
  exact_mod_cast dirichletKernel_mul_sin_half N t

/-- Away from the removable singularities, the Dirichlet kernel is the usual
sine quotient. -/
lemma dirichletKernel_eq_sin_ratio
    (N : ℕ) {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    dirichletKernel N t =
      dirichletOscillation N t / Real.sin (t / 2) := by
  exact (eq_div_iff ht).2 (by
    rw [mul_comm]
    exact dirichletKernel_mul_sin_half N t)

/-- The only zeros of `sin (t / 2)` on the open interval `(-π, π)` occur at
`t = 0`.  This isolates endpoint/singularity bookkeeping for Dirichlet. -/
lemma sin_half_ne_zero_of_mem_Ioo_ne_zero
    {t : ℝ} (ht : t ∈ Set.Ioo (-Real.pi) Real.pi) (h0 : t ≠ 0) :
    Real.sin (t / 2) ≠ 0 := by
  exact FejerL1Density.sin_half_ne_zero_of_ne_zero ⟨ht.1, le_of_lt ht.2⟩ h0

/-- On the closed Dirichlet interval, the only zero of `sin (t / 2)` is
`t = 0`. -/
lemma sin_half_ne_zero_of_mem_Icc_ne_zero
    {t : ℝ} (ht : t ∈ Set.Icc (-Real.pi) Real.pi) (h0 : t ≠ 0) :
    Real.sin (t / 2) ≠ 0 := by
  by_cases hleft : t = -Real.pi
  · subst t
    rw [neg_div, Real.sin_neg, Real.sin_pi_div_two]
    norm_num
  · have ht_left : -Real.pi < t := lt_of_le_of_ne ht.1 (Ne.symm hleft)
    exact FejerL1Density.sin_half_ne_zero_of_ne_zero ⟨ht_left, ht.2⟩ h0

/-- The singleton singularity has measure zero, so integral rewrites may ignore
`t = 0`. -/
lemma ae_ne_zero_on_interval :
    ∀ᵐ t ∂volume.restrict (Set.Icc (-Real.pi) Real.pi), t ≠ 0 := by
  rw [MeasureTheory.ae_iff]
  simp [Set.setOf_eq_eq_singleton,
    (MeasureTheory.NoAtoms.measure_singleton
      (μ := volume.restrict (Set.Icc (-Real.pi) Real.pi)) (0 : ℝ))]

/-! ### Dirichlet: quotient extension from `C¹` regularity -/

/-- The raw quotient equals the desired factorization away from `t = 0`. -/
lemma dirichletDifferenceQuotient_mul_sin_half
    (f : ℝ → ℂ) (x : ℝ) {t : ℝ} (ht : Real.sin (t / 2) ≠ 0) :
    f (x - t) - f x =
      dirichletDifferenceQuotient f x t * (Real.sin (t / 2) : ℂ) := by
  unfold dirichletDifferenceQuotient
  rw [div_mul_cancel₀]
  exact_mod_cast ht

/-- The map `t ↦ f (x - t) - f x` is differentiable at zero under `C¹`
regularity. -/
lemma hasDerivAt_dirichlet_numerator_zero
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) :
    HasDerivAt (fun t : ℝ => f (x - t) - f x) (-deriv f x) 0 := by
  have hf : HasDerivAt f (deriv f x) x := by
    exact ((hC1.differentiable (by norm_num : (1 : WithTop ℕ∞) ≠ 0)) x).hasDerivAt
  have hf0 : HasDerivAt f (deriv f x) (x - 0) := by
    simpa using hf
  have hcomp : HasDerivAt (fun t : ℝ => f (x - t)) (-deriv f x) 0 := by
    simpa using hf0.comp_const_sub x (0 : ℝ)
  change HasDerivAt ((fun t : ℝ => f (x - t)) - fun _ : ℝ => f x)
    (-deriv f x) 0
  simpa using hcomp.sub (hasDerivAt_const (0 : ℝ) (f x))

/-- `sin (t / 2)` has derivative `1 / 2` at zero. -/
lemma hasDerivAt_sin_half_zero :
    HasDerivAt (fun t : ℝ => Real.sin (t / 2)) (1 / 2) 0 := by
  have hdiv : HasDerivAt (fun t : ℝ => t / (2 : ℝ)) (1 / (2 : ℝ)) (0 : ℝ) := by
    simpa using ((hasDerivAt_id (0 : ℝ)).div_const (2 : ℝ))
  simpa using (Real.hasDerivAt_sin (((fun t : ℝ => t / (2 : ℝ)) 0))).comp (0 : ℝ) hdiv

private lemma tendsto_dirichletSincFactor_raw_zero :
    Tendsto (fun t : ℝ => (-(t : ℂ)) / (Real.sin (t / 2) : ℂ))
      (𝓝[≠] 0) (𝓝 (-2 : ℂ)) := by
  have hslope := hasDerivAt_sin_half_zero.tendsto_slope_zero
  have hsin_over_t :
      Tendsto (fun t : ℝ => Real.sin (t / 2) / t) (𝓝[≠] 0) (𝓝 (1 / 2 : ℝ)) := by
    simpa [smul_eq_mul, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hslope
  have ht_over_sin :
      Tendsto (fun t : ℝ => t / Real.sin (t / 2)) (𝓝[≠] 0) (𝓝 (2 : ℝ)) := by
    have h := hsin_over_t.inv₀ (by norm_num : (1 / 2 : ℝ) ≠ 0)
    simpa [one_div, div_eq_mul_inv] using h
  have hneg : Tendsto (fun t : ℝ => -(t / Real.sin (t / 2))) (𝓝[≠] 0) (𝓝 (-2 : ℝ)) :=
    ht_over_sin.neg
  convert hneg.ofReal using 1
  · ext t
    simp [Complex.ofReal_div, neg_div]
  · norm_num

private lemma continuousAt_dirichletSincFactor_zero :
    ContinuousAt dirichletSincFactor 0 := by
  simpa [dirichletSincFactor] using
    (continuousAt_update_same.mpr tendsto_dirichletSincFactor_raw_zero)

private lemma continuousAt_dirichletSincFactor_of_sin_ne_zero
    {t : ℝ} (ht : t ≠ 0) (hsin : Real.sin (t / 2) ≠ 0) :
    ContinuousAt dirichletSincFactor t := by
  have hraw : ContinuousAt (fun u : ℝ => (-(u : ℂ)) / (Real.sin (u / 2) : ℂ)) t := by
    exact (Complex.continuous_ofReal.comp continuous_id).neg.continuousAt.div
      ((Complex.continuous_ofReal.comp
        (Real.continuous_sin.comp (continuous_id.div_const (2 : ℝ)))).continuousAt)
      (by exact_mod_cast hsin)
  simpa [dirichletSincFactor] using (continuousAt_update_of_ne ht).2 hraw

private lemma continuousOn_dirichletSincFactor :
    ContinuousOn dirichletSincFactor (Set.Icc (-Real.pi) Real.pi) := by
  intro t ht
  by_cases h0 : t = 0
  · subst h0
    exact continuousAt_dirichletSincFactor_zero.continuousWithinAt
  · exact (continuousAt_dirichletSincFactor_of_sin_ne_zero h0
      (sin_half_ne_zero_of_mem_Icc_ne_zero ht h0)).continuousWithinAt

private lemma continuous_dslope_comp
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) :
    Continuous (fun t : ℝ => dslope f x (x - t)) := by
  have hdiff : DifferentiableAt ℝ f x :=
    (hC1.contDiffAt.differentiableAt (by norm_num : (1 : WithTop ℕ∞) ≠ 0))
  have hds_on : ContinuousOn (dslope f x) Set.univ := by
    exact (continuousOn_dslope (f := f) (a := x) (s := Set.univ)
      (isOpen_univ.mem_nhds trivial)).2 ⟨hC1.continuous.continuousOn, hdiff⟩
  have hds : Continuous (dslope f x) := continuousOn_univ.mp hds_on
  exact hds.comp (continuous_const.sub continuous_id)

/-- The quotient has the expected limit at the removable singularity. -/
lemma tendsto_dirichletDifferenceQuotient_zero
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) :
    Tendsto (dirichletDifferenceQuotient f x) (𝓝[≠] 0)
      (𝓝 ((-2 : ℂ) * deriv f x)) := by
  let g : ℝ → ℂ := fun t => f (x - t) - f x
  let s : ℝ → ℝ := fun t => Real.sin (t / 2)
  have hg : HasDerivAt g (-deriv f x) 0 := by
    simpa [g] using hasDerivAt_dirichlet_numerator_zero hC1 x
  have hs : HasDerivAt s (1 / 2) 0 := by
    simpa [s] using hasDerivAt_sin_half_zero
  have hgSlope : Tendsto (slope g 0) (𝓝[≠] (0 : ℝ)) (𝓝 (-deriv f x)) :=
    hg.tendsto_slope
  have hsSlopeReal : Tendsto (slope s 0) (𝓝[≠] (0 : ℝ)) (𝓝 (1 / 2 : ℝ)) :=
    hs.tendsto_slope
  have hsSlope : Tendsto (fun t => (slope s 0 t : ℂ)) (𝓝[≠] (0 : ℝ))
      (𝓝 (((1 / 2 : ℝ) : ℂ))) := by
    exact Filter.tendsto_ofReal_iff.mpr hsSlopeReal
  have hquot : Tendsto (fun t => slope g 0 t / ((slope s 0 t : ℂ)))
      (𝓝[≠] (0 : ℝ)) (𝓝 ((-deriv f x) / (((1 / 2 : ℝ) : ℂ)))) := by
    exact hgSlope.div hsSlope (by norm_num)
  have hquot' : Tendsto (fun t => slope g 0 t / ((slope s 0 t : ℂ)))
      (𝓝[≠] (0 : ℝ)) (𝓝 ((-2 : ℂ) * deriv f x)) := by
    have hconst : (-deriv f x) / (((1 / 2 : ℝ) : ℂ)) =
        (-2 : ℂ) * deriv f x := by
      norm_num
      ring
    convert hquot using 2
    exact hconst.symm
  refine hquot'.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have ht0 : t ≠ 0 := by simpa using ht
  have htc : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
  unfold dirichletDifferenceQuotient
  change slope g 0 t / ((slope s 0 t : ℂ)) =
      (f (x - t) - f x) / (Real.sin (t / 2) : ℂ)
  rw [slope_def_module, slope_def_field]
  simp only [g, s]
  simp only [sub_self, sub_zero, zero_div, Real.sin_zero, Complex.ofReal_div]
  change (algebraMap ℝ ℂ t⁻¹ * (f (x - t) - f x)) /
        ((Real.sin (t / 2) : ℂ) / (t : ℂ)) =
      (f (x - t) - f x) / (Real.sin (t / 2) : ℂ)
  rw [map_inv₀]
  field_simp [htc]
  simp [Complex.coe_algebraMap]
  ring

/-- A concrete continuous extension of the quotient. -/
def dirichletQuotientExtension (f : ℝ → ℂ) (x t : ℝ) : ℂ :=
  dirichletSincFactor t * dslope f x (x - t)

/-- The quotient extension is continuous at the removable singularity. -/
lemma continuousAt_dirichletQuotientExtension_zero
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) :
    ContinuousAt (dirichletQuotientExtension f x) 0 := by
  exact continuousAt_dirichletSincFactor_zero.mul
    ((continuous_dslope_comp hC1 x).continuousAt)

private lemma continuousAt_dirichletDifferenceQuotient_of_sin_half_ne_zero
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) {t : ℝ}
    (hsin : Real.sin (t / 2) ≠ 0) :
    ContinuousAt (dirichletDifferenceQuotient f x) t := by
  have hfcont : Continuous f := hC1.continuous
  have hnum : ContinuousAt (fun u : ℝ => f (x - u) - f x) t := by
    fun_prop
  have hden : ContinuousAt (fun u : ℝ => (Real.sin (u / 2) : ℂ)) t := by
    have hdiv : ContinuousAt (fun u : ℝ => u / (2 : ℝ)) t := by
      simpa using (continuousAt_id.div_const (2 : ℝ))
    simpa [Function.comp_def] using
      (Complex.continuous_ofReal.continuousAt.comp
        (Real.continuous_sin.continuousAt.comp hdiv))
  have hsinC : ((Real.sin (t / 2) : ℂ) ≠ 0) := by exact_mod_cast hsin
  unfold dirichletDifferenceQuotient
  change ContinuousAt (fun u : ℝ =>
    (f (x - u) - f x) / (Real.sin (u / 2) : ℂ)) t
  exact hnum.div₀ hden hsinC

private lemma continuousAt_dirichletQuotientExtension_of_sin_half_ne_zero
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) {t : ℝ}
    (ht : t ≠ 0) (hsin : Real.sin (t / 2) ≠ 0) :
    ContinuousAt (dirichletQuotientExtension f x) t := by
  exact (continuousAt_dirichletSincFactor_of_sin_ne_zero ht hsin).mul
    ((continuous_dslope_comp hC1 x).continuousAt)

/-- The quotient extension is continuous away from the removable singularity. -/
lemma continuousAt_dirichletQuotientExtension_ne_zero
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) {t : ℝ}
    (ht : t ≠ 0) (hsin : Real.sin (t / 2) ≠ 0) :
    ContinuousAt (dirichletQuotientExtension f x) t := by
  exact continuousAt_dirichletQuotientExtension_of_sin_half_ne_zero hC1 x ht hsin

/-- The quotient extension is continuous on `[-π, π]`. -/
lemma continuousOn_dirichletQuotientExtension
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) :
    ContinuousOn (dirichletQuotientExtension f x) (Set.Icc (-Real.pi) Real.pi) := by
  intro t ht
  by_cases h0 : t = 0
  · subst t
    exact (continuousAt_dirichletQuotientExtension_zero hC1 x).continuousWithinAt
  · exact (continuousAt_dirichletQuotientExtension_of_sin_half_ne_zero hC1 x h0
      (sin_half_ne_zero_of_mem_Icc_ne_zero ht h0)).continuousWithinAt

/-- Away from zero, the quotient extension still factors the numerator. -/
lemma dirichletQuotientExtension_mul_sin_half
    (f : ℝ → ℂ) (x : ℝ) {t : ℝ} (ht : t ≠ 0)
    (hsin : Real.sin (t / 2) ≠ 0) :
    f (x - t) - f x =
      dirichletQuotientExtension f x t * (Real.sin (t / 2) : ℂ) := by
  have hds := sub_smul_dslope f x (x - t)
  set s : ℂ := (Real.sin (t / 2) : ℂ)
  set d : ℂ := dslope f x (x - t)
  have hsinC : s ≠ 0 := by
    dsimp [s]
    exact_mod_cast hsin
  have hds' : (-(t : ℂ)) * d = f (x - t) - f x := by
    dsimp [d]
    have hxt : x - t - x = -t := by ring
    simpa [hxt, Complex.real_smul] using hds
  rw [dirichletQuotientExtension, dirichletSincFactor]
  rw [Function.update_of_ne ht]
  change f (x - t) - f x = ((-(t : ℂ)) / s * d) * s
  calc
    f (x - t) - f x = (-(t : ℂ)) * d := hds'.symm
    _ = ((-(t : ℂ)) / s * d) * s := by
      field_simp [hsinC]

/-- Packaged version of the quotient-extension input used by the final proof. -/
theorem exists_continuous_dirichlet_quotient
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) :
    ∃ φ : ℝ → ℂ,
      ContinuousOn φ (Set.Icc (-Real.pi) Real.pi) ∧
        ∀ t ∈ Set.Icc (-Real.pi) Real.pi,
          t ≠ 0 →
            f (x - t) - f x = φ t * (Real.sin (t / 2) : ℂ) := by
  refine ⟨dirichletQuotientExtension f x,
    continuousOn_dirichletQuotientExtension hC1 x, ?_⟩
  intro t ht h0
  exact dirichletQuotientExtension_mul_sin_half f x h0
    (sin_half_ne_zero_of_mem_Icc_ne_zero ht h0)

/-! ### Dirichlet: replacing the kernel integral by an oscillatory integral -/

/-- Pointwise integrand rewrite away from the removable singularity. -/
lemma dirichlet_integrand_eq_oscillatory_integrand
    {f φ : ℝ → ℂ} {x t : ℝ} (N : ℕ)
    (hfac : f (x - t) - f x = φ t * (Real.sin (t / 2) : ℂ)) :
    (f (x - t) - f x) * (dirichletKernel N t : ℂ) =
      φ t * (dirichletOscillation N t : ℂ) := by
  rw [hfac]
  rw [mul_assoc, dirichletKernel_mul_sin_half_complex]

/-- Integral rewrite from Dirichlet-kernel form to oscillatory-integral form.
The proof should use the quotient factorization away from `t = 0`, the sine
identity, and the fact that the singular point has measure zero. -/
lemma dirichlet_error_integral_eq_oscillatory_integral
    {f φ : ℝ → ℂ} (x : ℝ) (N : ℕ)
    (hfac : ∀ t ∈ Set.Icc (-Real.pi) Real.pi,
      t ≠ 0 → f (x - t) - f x = φ t * (Real.sin (t / 2) : ℂ)) :
    ∫ t in (-Real.pi)..Real.pi,
        (f (x - t) - f x) * (dirichletKernel N t : ℂ) =
      ∫ t in (-Real.pi)..Real.pi,
        φ t * (dirichletOscillation N t : ℂ) := by
  have hsub : Set.uIoc (-Real.pi) Real.pi ⊆ Set.Icc (-Real.pi) Real.pi := by
    intro t ht
    rw [Set.uIoc_of_le (by linarith [Real.pi_pos])] at ht
    exact Set.Ioc_subset_Icc_self ht
  have hne :
      ∀ᵐ t ∂volume.restrict (Set.uIoc (-Real.pi) Real.pi), t ≠ 0 :=
    ae_restrict_of_ae_restrict_of_subset hsub ae_ne_zero_on_interval
  refine intervalIntegral.integral_congr_ae ?_
  filter_upwards [ae_imp_of_ae_restrict hne] with t ht0 htmem
  exact dirichlet_integrand_eq_oscillatory_integrand N
    (hfac t (hsub htmem) (ht0 htmem))

/-! ### Dirichlet: Riemann-Lebesgue / oscillatory decay -/

private lemma tendsto_oscillatory_exp_neg_interval
    (φ : ℝ → ℂ) :
    Tendsto
      (fun N : ℕ =>
        ∫ t in (-Real.pi)..Real.pi,
          Complex.exp (-((((2 * (N : ℝ) + 1) * (t / 2) : ℝ) : ℂ) * Complex.I)) * φ t)
      atTop (𝓝 0) := by
  let s : Set ℝ := Set.Ioc (-Real.pi) Real.pi
  let g : ℝ → ℂ := s.indicator φ
  let w : ℕ → ℝ := fun N => (2 * (N : ℝ) + 1) / (4 * Real.pi)
  have hpi : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hw_atTop : Tendsto w atTop atTop := by
    have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => (2 : ℝ) * (N : ℝ)) atTop atTop :=
      hnat.const_mul_atTop (by norm_num)
    have h21 : Tendsto (fun N : ℕ => (2 : ℝ) * (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 h2
    have hscale :
        Tendsto (fun N : ℕ => (4 * Real.pi)⁻¹ * ((2 : ℝ) * (N : ℝ) + 1))
          atTop atTop :=
      h21.const_mul_atTop (by positivity)
    simpa [w, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscale
  have hw_cocompact : Tendsto w atTop (cocompact ℝ) :=
    hw_atTop.mono_right atTop_le_cocompact
  have hRL : Tendsto (fun N : ℕ => ∫ v : ℝ, 𝐞 (-(v * w N)) • g v) atTop (𝓝 0) :=
    (Real.tendsto_integral_exp_smul_cocompact g).comp hw_cocompact
  refine hRL.congr' ?_
  filter_upwards with N
  dsimp [g, s, w]
  rw [intervalIntegral.integral_of_le hpi]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Eventually.of_forall ?_)
  intro t
  by_cases ht : t ∈ Set.Ioc (-Real.pi) Real.pi
  · simp only [Set.indicator_of_mem ht, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    congr 1
    field_simp [Real.pi_ne_zero]
    norm_num
    ring
  · simp [Set.indicator_of_notMem ht]

private lemma tendsto_oscillatory_exp_pos_interval
    (φ : ℝ → ℂ) :
    Tendsto
      (fun N : ℕ =>
        ∫ t in (-Real.pi)..Real.pi,
          Complex.exp ((((2 * (N : ℝ) + 1) * (t / 2) : ℝ) : ℂ) * Complex.I) * φ t)
      atTop (𝓝 0) := by
  let s : Set ℝ := Set.Ioc (-Real.pi) Real.pi
  let g : ℝ → ℂ := s.indicator φ
  let w : ℕ → ℝ := fun N => -((2 * (N : ℝ) + 1) / (4 * Real.pi))
  have hpi : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hw_base_atTop :
      Tendsto (fun N : ℕ => (2 * (N : ℝ) + 1) / (4 * Real.pi)) atTop atTop := by
    have hnat : Tendsto (fun N : ℕ => (N : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => (2 : ℝ) * (N : ℝ)) atTop atTop :=
      hnat.const_mul_atTop (by norm_num)
    have h21 : Tendsto (fun N : ℕ => (2 : ℝ) * (N : ℝ) + 1) atTop atTop :=
      tendsto_atTop_add_const_right atTop 1 h2
    have hscale :
        Tendsto (fun N : ℕ => (4 * Real.pi)⁻¹ * ((2 : ℝ) * (N : ℝ) + 1))
          atTop atTop :=
      h21.const_mul_atTop (by positivity)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using hscale
  have hw_atBot' :
      Tendsto (fun N : ℕ => -((2 * (N : ℝ) + 1) / (4 * Real.pi))) atTop atBot :=
    tendsto_neg_atTop_atBot.comp hw_base_atTop
  have hw_atBot : Tendsto w atTop atBot := by
    simpa [w] using hw_atBot'
  have hw_cocompact : Tendsto w atTop (cocompact ℝ) :=
    hw_atBot.mono_right atBot_le_cocompact
  have hRL : Tendsto (fun N : ℕ => ∫ v : ℝ, 𝐞 (-(v * w N)) • g v) atTop (𝓝 0) :=
    (Real.tendsto_integral_exp_smul_cocompact g).comp hw_cocompact
  refine hRL.congr' ?_
  filter_upwards with N
  dsimp [g, s, w]
  rw [intervalIntegral.integral_of_le hpi]
  rw [← MeasureTheory.integral_indicator measurableSet_Ioc]
  refine integral_congr_ae (Eventually.of_forall ?_)
  intro t
  by_cases ht : t ∈ Set.Ioc (-Real.pi) Real.pi
  · simp only [Set.indicator_of_mem ht, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul]
    congr 1
    field_simp [Real.pi_ne_zero]
    norm_num
    ring
  · simp [Set.indicator_of_notMem ht]

private lemma oscillatory_integral_eq_exp_combo
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Set.Icc (-Real.pi) Real.pi)) (N : ℕ) :
    (∫ t in (-Real.pi)..Real.pi, φ t * (dirichletOscillation N t : ℂ)) =
      (Complex.I / 2) *
        ((∫ t in (-Real.pi)..Real.pi,
          Complex.exp (-((((2 * (N : ℝ) + 1) * (t / 2) : ℝ) : ℂ) * Complex.I)) * φ t) -
        (∫ t in (-Real.pi)..Real.pi,
          Complex.exp ((((2 * (N : ℝ) + 1) * (t / 2) : ℝ) : ℂ) * Complex.I) * φ t)) := by
  have hpi : (-Real.pi : ℝ) ≤ Real.pi := by linarith [Real.pi_pos]
  have hφu : ContinuousOn φ (Set.uIcc (-Real.pi) Real.pi) := by
    simpa [Set.uIcc_of_le hpi] using hφ
  let eneg : ℝ → ℂ := fun t =>
    Complex.exp (-((((2 * (N : ℝ) + 1) * (t / 2) : ℝ) : ℂ) * Complex.I)) * φ t
  let epos : ℝ → ℂ := fun t =>
    Complex.exp ((((2 * (N : ℝ) + 1) * (t / 2) : ℝ) : ℂ) * Complex.I) * φ t
  have hcont_neg : ContinuousOn eneg (Set.uIcc (-Real.pi) Real.pi) := by
    dsimp [eneg]
    exact ((Complex.continuous_exp.comp (by fun_prop)).continuousOn).mul hφu
  have hcont_pos : ContinuousOn epos (Set.uIcc (-Real.pi) Real.pi) := by
    dsimp [epos]
    exact ((Complex.continuous_exp.comp (by fun_prop)).continuousOn).mul hφu
  have hneg_int : IntervalIntegrable eneg volume (-Real.pi) Real.pi :=
    hcont_neg.intervalIntegrable
  have hpos_int : IntervalIntegrable epos volume (-Real.pi) Real.pi :=
    hcont_pos.intervalIntegrable
  have hpoint :
      (fun t => φ t * (dirichletOscillation N t : ℂ)) =
        fun t => (Complex.I / 2) * (eneg t - epos t) := by
    funext t
    dsimp [dirichletOscillation, eneg, epos]
    rw [Complex.ofReal_sin]
    unfold Complex.sin
    ring
  calc
    (∫ t in (-Real.pi)..Real.pi, φ t * (dirichletOscillation N t : ℂ))
        = ∫ t in (-Real.pi)..Real.pi, (Complex.I / 2) * (eneg t - epos t) := by
          rw [hpoint]
    _ = (Complex.I / 2) * ∫ t in (-Real.pi)..Real.pi, (eneg t - epos t) :=
        intervalIntegral.integral_const_mul (a := -Real.pi) (b := Real.pi)
          (r := Complex.I / 2) (f := fun t : ℝ => eneg t - epos t) (μ := volume)
    _ = (Complex.I / 2) *
        ((∫ t in (-Real.pi)..Real.pi, eneg t) -
          (∫ t in (-Real.pi)..Real.pi, epos t)) := by
          rw [intervalIntegral.integral_sub hneg_int hpos_int]
    _ = _ := by rfl

private theorem tendsto_oscillatory_integral_of_continuousOn
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Set.Icc (-Real.pi) Real.pi)) :
    Tendsto
      (fun N : ℕ =>
        ∫ t in (-Real.pi)..Real.pi, φ t * (dirichletOscillation N t : ℂ))
      atTop (𝓝 0) := by
  have hneg := tendsto_oscillatory_exp_neg_interval φ
  have hpos := tendsto_oscillatory_exp_pos_interval φ
  have hcombo :
      Tendsto
        (fun N : ℕ =>
          (Complex.I / 2) *
            ((∫ t in (-Real.pi)..Real.pi,
              Complex.exp (-((((2 * (N : ℝ) + 1) * (t / 2) : ℝ) : ℂ) * Complex.I)) *
                φ t) -
            (∫ t in (-Real.pi)..Real.pi,
              Complex.exp ((((2 * (N : ℝ) + 1) * (t / 2) : ℝ) : ℂ) * Complex.I) *
                φ t)))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul (hneg.sub hpos))
  exact hcombo.congr fun N => (oscillatory_integral_eq_exp_combo hφ N).symm

/-- Oscillatory integral vanishes for a constant amplitude. -/
lemma tendsto_oscillatory_integral_const
    (c : ℂ) :
    Tendsto
      (fun N : ℕ =>
        ∫ t in (-Real.pi)..Real.pi, c * (dirichletOscillation N t : ℂ))
      atTop (𝓝 0) := by
  simpa using
    (tendsto_oscillatory_integral_of_continuousOn
      (φ := fun _ : ℝ => c) continuousOn_const)

/-- Oscillatory integral vanishes for one complex exponential mode. -/
lemma tendsto_oscillatory_integral_exp_mode
    (m : ℤ) :
    Tendsto
      (fun N : ℕ =>
        ∫ t in (-Real.pi)..Real.pi,
          Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)) *
            (dirichletOscillation N t : ℂ))
      atTop (𝓝 0) := by
  have hcont :
      ContinuousOn (fun t : ℝ => Complex.exp (Complex.I * (m : ℂ) * (t : ℂ)))
        (Set.Icc (-Real.pi) Real.pi) := by
    exact (Complex.continuous_exp.comp (by fun_prop)).continuousOn
  simpa using
    (tendsto_oscillatory_integral_of_continuousOn
      (φ := fun t : ℝ => Complex.exp (Complex.I * (m : ℂ) * (t : ℂ))) hcont)

/-- Oscillatory integral vanishes for trigonometric polynomials. -/
lemma tendsto_oscillatory_integral_trig_polynomial
    {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc (-Real.pi) Real.pi))
    (_hφ_trig : FejerL1Density.IsTrigPolynomial (fun t => ‖φ t‖)) :
    Tendsto
      (fun N : ℕ =>
        ∫ t in (-Real.pi)..Real.pi, φ t * (dirichletOscillation N t : ℂ))
      atTop (𝓝 0) := by
  exact tendsto_oscillatory_integral_of_continuousOn hφ

/-- Uniform approximation transfers oscillatory decay from an approximant to the
original amplitude. -/
lemma tendsto_oscillatory_integral_of_uniform_approx
    {φ : ℝ → ℂ}
    (hφ : ContinuousOn φ (Set.Icc (-Real.pi) Real.pi))
    (_happrox : ∀ ε > 0, ∃ ψ : ℝ → ℂ,
      (∀ x, ‖φ x - ψ x‖ ≤ ε) ∧
        Tendsto
          (fun N : ℕ =>
            ∫ t in (-Real.pi)..Real.pi, ψ t * (dirichletOscillation N t : ℂ))
          atTop (𝓝 0)) :
    Tendsto
      (fun N : ℕ =>
        ∫ t in (-Real.pi)..Real.pi, φ t * (dirichletOscillation N t : ℂ))
      atTop (𝓝 0) := by
  exact tendsto_oscillatory_integral_of_continuousOn hφ

/-- Riemann-Lebesgue/oscillatory integral input for the final Dirichlet argument. -/
theorem tendsto_oscillatory_integral_sin_half
    {φ : ℝ → ℂ} (hφ : ContinuousOn φ (Set.Icc (-Real.pi) Real.pi)) :
    Tendsto
      (fun N : ℕ =>
        ∫ t in (-Real.pi)..Real.pi, φ t * (dirichletOscillation N t : ℂ))
      atTop (𝓝 0) := by
  exact tendsto_oscillatory_integral_of_continuousOn hφ

/-! ### Dirichlet: final assembly -/

/-- If the partial-sum error tends to zero, the partial sums converge pointwise. -/
lemma tendsto_of_sub_tendsto_zero
    {u : ℕ → ℂ} {a : ℂ} (h : Tendsto (fun N => u N - a) atTop (𝓝 0)) :
    Tendsto u atTop (𝓝 a) := by
  have h' := h.add (tendsto_const_nhds (x := a))
  simpa [sub_eq_add_neg, add_assoc] using h'

/-- The Dirichlet error tends to zero after rewriting it as an oscillatory
integral. -/
lemma dirichlet_error_tendsto_zero
    {f : ℝ → ℂ} (hC1 : ContDiff ℝ 1 f) (x : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSumKernel f N x - f x) atTop (𝓝 0) := by
  obtain ⟨φ, hφ_cont, hfac⟩ := exists_continuous_dirichlet_quotient hC1 x
  have hosc := tendsto_oscillatory_integral_sin_half hφ_cont
  have hscaled :
      Tendsto
        (fun N : ℕ =>
          (1 / (2 * Real.pi) : ℂ) *
            ∫ t in (-Real.pi)..Real.pi, φ t * (dirichletOscillation N t : ℂ))
        atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hosc)
  exact hscaled.congr fun N => by
    rw [dirichlet_convolution_sub_eq f N x hC1.continuous,
      dirichlet_error_integral_eq_oscillatory_integral x N hfac]

/-- Blueprint assembly lemma: once the convolution identity, quotient extension,
and oscillatory integral lemma are available, Dirichlet pointwise convergence
follows. -/
theorem dirichlet_pointwise_from_blueprint
    {f : ℝ → ℂ} (hperiod : Function.Periodic f (2 * Real.pi))
    (hC1 : ContDiff ℝ 1 f) (x : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSumKernel f N x) atTop (𝓝 (f x)) := by
  let _ := hperiod
  exact tendsto_of_sub_tendsto_zero (dirichlet_error_tendsto_zero hC1 x)

end DirichletFejerBlueprint

/-- **Dirichlet's pointwise convergence theorem** (§46). For every `C¹`
2π-periodic complex function `f`, the symmetric Fourier partial sums `S_N(f)(x)`
converge to `f(x)` at every point `x ∈ ℝ`. -/
theorem dirichlet_pointwise
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hC1 : ContDiff ℝ 1 f)
    (x : ℝ) :
    Tendsto (fun N : ℕ => fourierPartialSum f N x) atTop (𝓝 (f x)) := by
  exact (DirichletFejerBlueprint.dirichlet_pointwise_from_blueprint _hperiod _hC1 x).congr'
    (Eventually.of_forall fun N =>
      (DirichletFejerBlueprint.fourierPartialSum_eq_fourierPartialSumKernel
        _hperiod _hC1.continuous N x).symm)

/-- **Fejér's theorem** (§46). For every *continuous* 2π-periodic complex
function `f` — without the `C¹` hypothesis of Dirichlet's theorem — the Cesaro
means `σ_N(f)` of the symmetric Fourier partial sums converge to `f` uniformly
on `ℝ`. -/
theorem fejer
    {f : ℝ → ℂ} (_hperiod : Function.Periodic f (2 * Real.pi)) (_hcont : Continuous f) :
    TendstoUniformly (fun N : ℕ => fourierCesaroMean f N) f atTop := by
  have hkernel := DirichletFejerBlueprint.fejer_from_blueprint _hperiod _hcont
  have hshift : TendstoUniformly
      (fun N : ℕ => fourierCesaroMeanKernel f (N + 1)) f atTop := by
    intro u hu
    exact (Filter.tendsto_add_atTop_nat 1) (hkernel u hu)
  exact (tendstoUniformly_congr (Eventually.of_forall fun N => by
    exact DirichletFejerBlueprint.fourierCesaroMean_eq_fourierCesaroMeanKernel_succ
      _hperiod _hcont N)).mpr hshift

end
end Submission
