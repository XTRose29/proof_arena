import Submission.GoodSetHausdorff

namespace Submission.Helpers

open Filter
open scoped ENNReal

lemma exists_exponential_entropy_tail_bound
    (u : ℕ → ℝ) {h delta R : ℝ}
    (hu : Tendsto (fun n => u n / n) atTop (nhds h))
    (hdelta : 0 < delta) (d : NNReal)
    (hrate : h / delta < R * (d : ℝ)) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ ∀ N,
      (∑' n : {n : ℕ // N ≤ n},
        ENNReal.ofReal (Real.exp (u n.1 / delta + 1)) *
          ENNReal.ofReal (Real.exp (-R * n.1)) ^ (d : ℝ)) ≤ C := by
  let margin := (R * (d : ℝ) - h / delta) / 2
  have hmargin : 0 < margin := by
    dsimp [margin]
    linarith
  have hu_eventually : ∀ᶠ n : ℕ in atTop,
      u n / n < h + delta * margin := by
    apply (tendsto_order.1 hu).2
    dsimp [margin]
    nlinarith
  obtain ⟨N0, hN0⟩ := eventually_atTop.1
    (hu_eventually.and (eventually_gt_atTop 0))
  let f : ℕ → ℝ≥0∞ := fun n =>
    ENNReal.ofReal (Real.exp (u n / delta + 1)) *
      ENNReal.ofReal (Real.exp (-R * n)) ^ (d : ℝ)
  let q : ℝ≥0∞ := ENNReal.ofReal (Real.exp (-margin))
  let K : ℝ≥0∞ := ENNReal.ofReal (Real.exp 1)
  let g : ℕ → ℝ≥0∞ := fun n => K * q ^ n
  have hfg (n : ℕ) (hn : N0 ≤ n) : f n ≤ g n := by
    obtain ⟨hun, hnpos⟩ := hN0 n hn
    have hnpos_real : (0 : ℝ) < n := by exact_mod_cast hnpos
    have hu_mul : u n < (h + delta * margin) * n :=
      (div_lt_iff₀ hnpos_real).mp hun
    have hu_div : u n / delta < (h / delta + margin) * n := by
      apply (div_lt_iff₀ hdelta).2
      calc
        u n < (h + delta * margin) * n := hu_mul
        _ = ((h / delta + margin) * n) * delta := by
          field_simp
    have hexponent :
        u n / delta + 1 + (-R * n) * (d : ℝ) ≤ 1 - margin * n := by
      have hmargin_eq : R * (d : ℝ) - h / delta = 2 * margin := by
        dsimp [margin]
        ring
      nlinarith
    have hf_eq : f n = ENNReal.ofReal
        (Real.exp (u n / delta + 1 + (-R * n) * (d : ℝ))) := by
      dsimp [f]
      rw [ENNReal.ofReal_rpow_of_pos (Real.exp_pos _)]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [Real.rpow_def_of_pos (Real.exp_pos _), Real.log_exp]
      rw [← Real.exp_add]
    have hg_eq : g n = ENNReal.ofReal (Real.exp (1 - margin * n)) := by
      dsimp [g, K, q]
      rw [← ENNReal.ofReal_pow (Real.exp_nonneg _)]
      rw [← ENNReal.ofReal_mul (Real.exp_nonneg _)]
      rw [← Real.exp_nat_mul, ← Real.exp_add]
      congr 2
      ring
    rw [hf_eq, hg_eq]
    exact ENNReal.ofReal_le_ofReal (Real.exp_le_exp.mpr hexponent)
  have hq_lt_one : q < 1 := by
    rw [show (1 : ℝ≥0∞) = ENNReal.ofReal 1 by simp]
    apply (ENNReal.ofReal_lt_ofReal_iff zero_lt_one).2
    exact Real.exp_lt_one_iff.mpr (neg_neg_of_pos hmargin)
  have hg_tsum : (∑' n, g n) = K * (1 - q)⁻¹ := by
    dsimp [g]
    rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
  let C : ℝ≥0∞ :=
    (∑ n ∈ Finset.range N0, f n) + K * (1 - q)⁻¹
  have hC : C ≠ ⊤ := by
    apply ENNReal.add_ne_top.mpr
    constructor
    · apply ENNReal.sum_ne_top.mpr
      intro n hn
      dsimp [f]
      exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.rpow_ne_top_of_nonneg (by exact_mod_cast d.coe_nonneg)
          ENNReal.ofReal_ne_top)
    · exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top
        (ENNReal.inv_ne_top.mpr (tsub_pos_iff_lt.mpr hq_lt_one).ne')
  have htail :
      (∑' n : ↥((Finset.range N0 : Set ℕ)ᶜ), f n.1) ≤ ∑' n, g n := by
    calc
      (∑' n : ↥((Finset.range N0 : Set ℕ)ᶜ), f n.1) ≤
          ∑' n : ↥((Finset.range N0 : Set ℕ)ᶜ), g n.1 := by
        apply ENNReal.tsum_le_tsum
        intro n
        apply hfg n.1
        exact le_of_not_gt fun hnlt => n.2 (Finset.mem_range.mpr hnlt)
      _ ≤ ∑' n, g n := by
        rw [tsum_subtype]
        exact ENNReal.tsum_le_tsum fun n => Set.indicator_le_self _ _ n
  have htotal : (∑' n, f n) ≤ C := by
    rw [← ENNReal.sum_add_tsum_compl (Finset.range N0) f]
    dsimp [C]
    exact add_le_add (le_refl _) (htail.trans_eq hg_tsum)
  refine ⟨C, hC, fun N => ?_⟩
  change (∑' n : {n : ℕ // N ≤ n}, f n.1) ≤ C
  calc
    (∑' n : {n : ℕ // N ≤ n}, f n.1) ≤ ∑' n, f n := by
      exact Summable.tsum_le_tsum_of_inj
        (fun n : {n : ℕ // N ≤ n} => n.1) Subtype.coe_injective
        (fun _n _hn => bot_le) (fun _n => le_rfl)
        ENNReal.summable ENNReal.summable
    _ ≤ C := htotal

end Submission.Helpers
