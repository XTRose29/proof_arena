import Submission.WeightedCenteredNameStability

namespace Submission.Helpers

open LeanEval.Dynamics
open MeasureTheory Filter
open scoped ENNReal

noncomputable def geometricBoundaryScale (q : NNReal) (L : ℕ) : ℝ :=
  (q ^ (L + 1) / (L + 1) : NNReal)

lemma geometricBoundaryScale_pos
    {q : NNReal} (hq : 0 < q) (L : ℕ) :
    0 < geometricBoundaryScale q L := by
  rw [geometricBoundaryScale]
  positivity

lemma geometric_boundary_cost_tsum_ne_top
    {M : Type*} [MeasurableSpace M]
    (mu : Measure M) [IsProbabilityMeasure mu]
    (q : NNReal) (hq : q < 1) :
    (∑' L : ℕ, (L + 1 : ℝ≥0∞) *
      ENNReal.ofReal (2 * geometricBoundaryScale q L) * mu Set.univ) ≠ ⊤ := by
  have hterm (L : ℕ) :
      (L + 1 : ℝ≥0∞) *
          ENNReal.ofReal (2 * geometricBoundaryScale q L) * mu Set.univ =
        2 * (q : ℝ≥0∞) ^ (L + 1) := by
    rw [measure_univ, mul_one]
    simp only [geometricBoundaryScale, NNReal.coe_div, NNReal.coe_pow]
    rw [ENNReal.ofReal_mul (by positivity)]
    rw [ENNReal.ofReal_div_of_pos (by positivity)]
    rw [ENNReal.ofReal_pow q.coe_nonneg]
    simp only [ENNReal.ofReal_ofNat, ENNReal.ofReal_coe_nnreal]
    rw [show (L : ℝ≥0∞) + 1 = (L + 1 : ℕ) by norm_num]
    rw [show ((↑(↑L + 1 : NNReal) : ℝ≥0∞)) = (L + 1 : ℕ) by norm_num]
    calc
      (L + 1 : ℕ) *
          (2 * ((q : ℝ≥0∞) ^ (L + 1) / (L + 1 : ℕ))) =
          2 * ((L + 1 : ℕ) *
            ((q : ℝ≥0∞) ^ (L + 1) / (L + 1 : ℕ))) := by
        ac_rfl
      _ = 2 * (q : ℝ≥0∞) ^ (L + 1) := by
        rw [ENNReal.mul_div_cancel] <;> simp
  simp_rw [hterm]
  rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric_add_one]
  have hq' : (q : ℝ≥0∞) < 1 := by exact_mod_cast hq
  have hsub : 1 - (q : ℝ≥0∞) ≠ 0 := (tsub_pos_iff_lt.mpr hq').ne'
  exact ENNReal.mul_ne_top (by simp)
    (ENNReal.mul_ne_top (by simp) (ENNReal.inv_ne_top.mpr hsub))

lemma exists_small_geometric_boundary_ball_partition
    (mu : Measure EucPlane) [IsProbabilityMeasure mu]
    {K s : Set EucPlane} (hK_compact : IsCompact K)
    (hs_measurable : MeasurableSet s) (hmu_s : mu sᶜ = 0) (hsK : s ⊆ K)
    {e : ℝ} (he : 0 < e)
    (q : NNReal) (hq_pos : 0 < q) (hq_lt_one : q < 1) :
    ∃ n : ℕ, ∃ center : Fin n → EucPlane, ∃ radius : Fin n → ℝ,
      ∃ P : Finset (Set EucPlane),
        (∀ i, e < radius i ∧ radius i < 2 * e ∧
          (∑' L : ℕ, (L + 1 : ℝ≥0∞) *
            mu {x | |dist x (center i) - radius i| ≤
              geometricBoundaryScale q L}) ≠ ⊤) ∧
        s ⊆ ⋃ i, Metric.ball (center i) (radius i) ∧
        IsMeasurablePartition mu P ∧
        (∀ A ∈ P, A ⊆ s) ∧
        (∀ A ∈ P, Metric.ediam A ≤ 2 * ENNReal.ofReal (2 * e)) ∧
        ∀ {x y}, x ∈ s → y ∈ s →
          (∀ i, x ∈ Metric.ball (center i) (radius i) ↔
            y ∈ Metric.ball (center i) (radius i)) →
          ∀ A ∈ P, x ∈ A ↔ y ∈ A := by
  exact exists_small_weighted_boundary_ball_partition
    mu hK_compact hs_measurable hmu_s hsK he
      (fun L => (L : ℝ≥0∞) + 1) (geometricBoundaryScale q)
      (fun L => (geometricBoundaryScale_pos hq_pos L).le)
      (geometric_boundary_cost_tsum_ne_top mu q hq_lt_one)

lemma ae_eventually_avoids_geometric_centeredBoundaries
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] {p : ℕ}
    (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (center : Fin p → M) (radius : Fin p → ℝ)
    (q : NNReal) (m n : ℕ → ℕ) (hsplit : ∀ L, m L + n L = L)
    (hsum : ∀ i,
      (∑' L : ℕ, (L + 1 : ℝ≥0∞) *
        mu {x | |dist x (center i) - radius i| ≤
          geometricBoundaryScale q L}) ≠ ⊤) :
    ∀ᵐ x ∂mu, ∀ᶠ L in atTop,
      x ∉ centeredBoundaryBadReal T T_inv center radius
        (geometricBoundaryScale q L) (m L) (n L) := by
  apply exists_ae_eventually_avoids_weighted_centeredBoundaries
    mu T T_inv hT hT_inv center radius (geometricBoundaryScale q) m n
  intro i
  apply ne_top_of_le_ne_top (hsum i)
  apply ENNReal.tsum_le_tsum
  intro L
  gcongr
  rw [hsplit L]
  exact_mod_cast Nat.le_add_right L 1

end Submission.Helpers
