import Submission.EntropyLightEventually

namespace Submission.Helpers

open MeasureTheory
open scoped ENNReal

lemma lintegral_annulus_measure_le
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (center : M) {a b delta : ℝ} (_hdelta : 0 ≤ delta) :
    (∫⁻ r in Set.Icc a b,
        mu {x | |dist x center - r| ≤ delta} ∂volume) ≤
      ENNReal.ofReal (2 * delta) * mu Set.univ := by
  let S : Set (ℝ × M) :=
    {p | p.1 ∈ Set.Icc a b ∧ |dist p.2 center - p.1| ≤ delta}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  let f : ℝ → M → ℝ≥0∞ := fun r x =>
    S.indicator (fun _ => 1) (r, x)
  have hf : Measurable (Function.uncurry f) := by
    dsimp [f]
    exact measurable_const.indicator hS
  calc
    (∫⁻ r in Set.Icc a b,
        mu {x | |dist x center - r| ≤ delta} ∂volume) =
        ∫⁻ r, ∫⁻ x, f r x ∂mu ∂volume := by
      rw [← lintegral_indicator measurableSet_Icc]
      apply lintegral_congr
      intro r
      by_cases hr : r ∈ Set.Icc a b
      · have hfiber : (fun x => f r x) =
            {x | |dist x center - r| ≤ delta}.indicator (fun _ => 1) := by
          funext x
          simp only [f, Set.indicator_apply]
          change (if r ∈ Set.Icc a b ∧ |dist x center - r| ≤ delta then 1 else 0) =
            if |dist x center - r| ≤ delta then 1 else 0
          simp [hr]
        have hstrip : MeasurableSet {x | |dist x center - r| ≤ delta} := by
          measurability
        rw [Set.indicator_of_mem hr, hfiber]
        exact (lintegral_indicator_one (μ := mu) hstrip).symm
      · have hfiber : (fun x => f r x) = fun _ => (0 : ℝ≥0∞) := by
          funext x
          simp only [f]
          rw [Set.indicator_of_notMem]
          intro hmem
          exact hr hmem.1
        rw [Set.indicator_of_notMem hr, hfiber]
        simp
    _ = ∫⁻ x, ∫⁻ r, f r x ∂volume ∂mu :=
      lintegral_lintegral_swap hf.aemeasurable
    _ ≤ ∫⁻ _x : M, ENNReal.ofReal (2 * delta) ∂mu := by
      apply lintegral_mono
      intro x
      let R : Set ℝ :=
        {r | r ∈ Set.Icc a b ∧ |dist x center - r| ≤ delta}
      have hR : MeasurableSet R := by
        dsimp [R]
        measurability
      have hR_subset : R ⊆ Set.Icc (dist x center - delta) (dist x center + delta) := by
        intro r hr
        have habs := (abs_le.mp hr.2)
        constructor <;> linarith
      calc
        (∫⁻ r, f r x ∂volume) = volume R := by
          rw [← lintegral_indicator_one hR]
          apply lintegral_congr
          intro r
          simp only [f, Set.indicator_apply]
          change
            (if r ∈ Set.Icc a b ∧ |dist x center - r| ≤ delta then 1 else 0) =
              if r ∈ R then 1 else 0
          rfl
        _ ≤ volume (Set.Icc (dist x center - delta) (dist x center + delta)) :=
          measure_mono hR_subset
        _ = ENNReal.ofReal (2 * delta) := by
          rw [Real.volume_Icc]
          congr 1
          ring
    _ = ENNReal.ofReal (2 * delta) * mu Set.univ := by simp

lemma measurable_boundaryStrip_measure
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] (center : M) (delta : ℝ) :
    Measurable fun r : ℝ => mu {x | |dist x center - r| ≤ delta} := by
  let S : Set (ℝ × M) :=
    {p | |dist p.2 center - p.1| ≤ delta}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  simpa [S] using
    (measurable_measure_prodMk_left_finite (ν := mu) hS)

lemma lintegral_boundaryStrip_measure_le
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu]
    (center : M) {delta : ℝ} (_hdelta : 0 ≤ delta) :
    (∫⁻ r : ℝ, mu {x | |dist x center - r| ≤ delta} ∂volume) ≤
      ENNReal.ofReal (2 * delta) * mu Set.univ := by
  let S : Set (ℝ × M) :=
    {p | |dist p.2 center - p.1| ≤ delta}
  have hS : MeasurableSet S := by
    dsimp [S]
    measurability
  let f : ℝ → M → ℝ≥0∞ := fun r x =>
    S.indicator (fun _ => 1) (r, x)
  have hf : Measurable (Function.uncurry f) := by
    dsimp [f]
    exact measurable_const.indicator hS
  calc
    (∫⁻ r : ℝ, mu {x | |dist x center - r| ≤ delta} ∂volume) =
        ∫⁻ r, ∫⁻ x, f r x ∂mu ∂volume := by
      apply lintegral_congr
      intro r
      have hfiber : (fun x => f r x) =
          {x | |dist x center - r| ≤ delta}.indicator (fun _ => 1) := by
        funext x
        simp only [f, Set.indicator_apply]
        rfl
      have hstrip : MeasurableSet {x | |dist x center - r| ≤ delta} := by
        measurability
      rw [hfiber]
      exact (lintegral_indicator_one (μ := mu) hstrip).symm
    _ = ∫⁻ x, ∫⁻ r, f r x ∂volume ∂mu :=
      lintegral_lintegral_swap hf.aemeasurable
    _ ≤ ∫⁻ _x : M, ENNReal.ofReal (2 * delta) ∂mu := by
      apply lintegral_mono
      intro x
      let R : Set ℝ := {r | |dist x center - r| ≤ delta}
      have hR : MeasurableSet R := by
        dsimp [R]
        measurability
      have hR_subset :
          R ⊆ Set.Icc (dist x center - delta) (dist x center + delta) := by
        intro r hr
        change |dist x center - r| ≤ delta at hr
        have habs := abs_le.mp hr
        constructor <;> linarith
      calc
        (∫⁻ r, f r x ∂volume) = volume R := by
          rw [← lintegral_indicator_one hR]
          apply lintegral_congr
          intro r
          simp only [f, Set.indicator_apply]
          change (if |dist x center - r| ≤ delta then 1 else 0) =
            if r ∈ R then 1 else 0
          rfl
        _ ≤ volume (Set.Icc (dist x center - delta) (dist x center + delta)) :=
          measure_mono hR_subset
        _ = ENNReal.ofReal (2 * delta) := by
          rw [Real.volume_Icc]
          congr 1
          ring
    _ = ENNReal.ofReal (2 * delta) * mu Set.univ := by simp

lemma exists_radius_weighted_boundaryStrip_tsum_ne_top
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M] [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] (center : M)
    {a b : ℝ} (hab : a < b)
    (weight : ℕ → ℝ≥0∞) (delta : ℕ → ℝ)
    (hdelta : ∀ n, 0 ≤ delta n)
    (hsum :
      (∑' n, weight n * ENNReal.ofReal (2 * delta n) * mu Set.univ) ≠ ⊤) :
    ∃ r ∈ Set.Ioo a b,
      (∑' n, weight n * mu {x | |dist x center - r| ≤ delta n}) ≠ ⊤ := by
  let g : ℕ → ℝ → ℝ≥0∞ := fun n r =>
    weight n * mu {x | |dist x center - r| ≤ delta n}
  have hg_measurable (n : ℕ) : Measurable (g n) := by
    dsimp [g]
    exact measurable_const.mul
      (measurable_boundaryStrip_measure mu center (delta n))
  have hg_integral (n : ℕ) :
      (∫⁻ r, g n r ∂volume) ≤
        weight n * ENNReal.ofReal (2 * delta n) * mu Set.univ := by
    calc
      (∫⁻ r, g n r ∂volume) =
          weight n *
            (∫⁻ r : ℝ, mu {x | |dist x center - r| ≤ delta n} ∂volume) := by
        exact lintegral_const_mul (weight n)
          (measurable_boundaryStrip_measure mu center (delta n))
      _ ≤ weight n *
          (ENNReal.ofReal (2 * delta n) * mu Set.univ) :=
        mul_le_mul_right
          (lintegral_boundaryStrip_measure_le mu center (hdelta n)) _
      _ = weight n * ENNReal.ofReal (2 * delta n) * mu Set.univ := by
        rw [mul_assoc]
  have htotal_integral :
      (∫⁻ r, ∑' n, g n r ∂volume) ≤
        ∑' n, weight n * ENNReal.ofReal (2 * delta n) * mu Set.univ := by
    rw [lintegral_tsum fun n => (hg_measurable n).aemeasurable]
    exact ENNReal.tsum_le_tsum hg_integral
  have htotal_ne_top : (∫⁻ r, ∑' n, g n r ∂volume) ≠ ⊤ :=
    ne_top_of_le_ne_top hsum htotal_integral
  have htotal_measurable : Measurable fun r => ∑' n, g n r :=
    Measurable.tsum hg_measurable
  have hae : ∀ᵐ r ∂volume, (∑' n, g n r) < ⊤ :=
    ae_lt_top htotal_measurable htotal_ne_top
  have hIoo_ne_zero : volume (Set.Ioo a b) ≠ 0 := by
    rw [Real.volume_Ioo]
    exact ne_of_gt (ENNReal.ofReal_pos.mpr (sub_pos.mpr hab))
  have hexists : ∃ r ∈ Set.Ioo a b, (∑' n, g n r) < ⊤ := by
    by_contra hnone
    have hsubset :
        Set.Ioo a b ⊆ {r | ¬(∑' n, g n r) < ⊤} := by
      intro r hr hfinite
      exact hnone ⟨r, hr, hfinite⟩
    exact hIoo_ne_zero (measure_mono_null hsubset (mem_ae_iff.mp hae))
  obtain ⟨r, hr, hfinite⟩ := hexists
  exact ⟨r, hr, by
    simpa [g] using hfinite.ne⟩

end Submission.Helpers
