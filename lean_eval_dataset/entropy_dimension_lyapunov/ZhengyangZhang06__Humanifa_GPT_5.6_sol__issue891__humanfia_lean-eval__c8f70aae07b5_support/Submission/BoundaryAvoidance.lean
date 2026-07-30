import Submission.NullBoundaryPartition

namespace Submission.Helpers

open MeasureTheory Filter Topology
open scoped ENNReal

def ballBoundaryNeighborhood
    {M : Type*} [PseudoMetricSpace M] {n : ℕ}
    (center : Fin n → M) (radius : Fin n → ℝ) (k : ℕ) : Set M :=
  ⋃ i, {x | |dist x (center i) - radius i| ≤ 1 / ((k : ℝ) + 1)}

lemma measurableSet_ballBoundaryNeighborhood
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M] {n : ℕ}
    (center : Fin n → M) (radius : Fin n → ℝ) (k : ℕ) :
    MeasurableSet (ballBoundaryNeighborhood center radius k) := by
  apply MeasurableSet.iUnion
  intro i
  apply measurableSet_le
  · fun_prop
  · fun_prop

lemma antitone_ballBoundaryNeighborhood
    {M : Type*} [PseudoMetricSpace M] {n : ℕ}
    (center : Fin n → M) (radius : Fin n → ℝ) :
    Antitone (ballBoundaryNeighborhood center radius) := by
  intro k l hkl x hx
  obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hx
  apply Set.mem_iUnion_of_mem i
  change |dist x (center i) - radius i| ≤ 1 / ((l : ℝ) + 1) at hxi
  change |dist x (center i) - radius i| ≤ 1 / ((k : ℝ) + 1)
  exact hxi.trans (by
    apply one_div_le_one_div_of_le
    · positivity
    · have hkl' : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
      linarith)

lemma iInter_closed_ballBoundaryStrip
    {M : Type*} [PseudoMetricSpace M] (center : M) (radius : ℝ) :
    (⋂ k : ℕ,
      {x : M | |dist x center - radius| ≤ 1 / ((k : ℝ) + 1)}) =
        Metric.sphere center radius := by
  ext x
  constructor
  · intro hx
    have hbound : ∀ k : ℕ,
        |dist x center - radius| ≤ 1 / ((k : ℝ) + 1) := by
      intro k
      exact Set.mem_iInter.mp hx k
    have hnonpos : |dist x center - radius| ≤ 0 :=
      ge_of_tendsto tendsto_one_div_add_atTop_nhds_zero_nat
        (Filter.Eventually.of_forall hbound)
    have hzero : dist x center = radius := by
      have habs : |dist x center - radius| = 0 :=
        le_antisymm hnonpos (abs_nonneg _)
      exact sub_eq_zero.mp (abs_eq_zero.mp habs)
    exact Metric.mem_sphere.mpr hzero
  · intro hx
    have hzero : dist x center - radius = 0 :=
      sub_eq_zero.mpr (Metric.mem_sphere.mp hx)
    apply Set.mem_iInter.mpr
    intro k
    rw [Set.mem_setOf_eq, hzero, abs_zero]
    positivity

lemma iInter_ballBoundaryNeighborhood
    {M : Type*} [PseudoMetricSpace M] {n : ℕ}
    (center : Fin n → M) (radius : Fin n → ℝ) :
    (⋂ k : ℕ, ballBoundaryNeighborhood center radius k) =
      ⋃ i, Metric.sphere (center i) (radius i) := by
  unfold ballBoundaryNeighborhood
  rw [Set.iInter_iUnion_of_antitone]
  · congr 1
    funext i
    exact iInter_closed_ballBoundaryStrip (center i) (radius i)
  · intro i k l hkl x hx
    change |dist x (center i) - radius i| ≤ 1 / ((l : ℝ) + 1) at hx
    change |dist x (center i) - radius i| ≤ 1 / ((k : ℝ) + 1)
    exact hx.trans (by
      apply one_div_le_one_div_of_le
      · positivity
      · have hkl' : (k : ℝ) ≤ (l : ℝ) := by exact_mod_cast hkl
        linarith)

lemma tendsto_measure_ballBoundaryNeighborhood_zero
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] {n : ℕ}
    (center : Fin n → M) (radius : Fin n → ℝ)
    (hboundary : ∀ i, mu (Metric.sphere (center i) (radius i)) = 0) :
    Tendsto (fun k => mu (ballBoundaryNeighborhood center radius k))
      atTop (nhds 0) := by
  have hinter_zero :
      mu (⋂ k : ℕ, ballBoundaryNeighborhood center radius k) = 0 := by
    rw [iInter_ballBoundaryNeighborhood]
    exact measure_iUnion_null hboundary
  have htend := tendsto_measure_iInter_atTop
    (μ := mu)
    (fun k => (measurableSet_ballBoundaryNeighborhood center radius k).nullMeasurableSet)
    (antitone_ballBoundaryNeighborhood center radius)
    ⟨0, measure_ne_top mu _⟩
  rw [hinter_zero] at htend
  simpa [Function.comp_def] using htend

lemma exists_ballBoundaryNeighborhood_measure_lt
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] {n : ℕ}
    (center : Fin n → M) (radius : Fin n → ℝ)
    (hboundary : ∀ i, mu (Metric.sphere (center i) (radius i)) = 0)
    {eta : ℝ≥0∞} (heta : 0 < eta) :
    ∃ k, mu (ballBoundaryNeighborhood center radius k) < eta := by
  have htend := tendsto_measure_ballBoundaryNeighborhood_zero
    mu center radius hboundary
  exact ((tendsto_order.mp htend).2 eta heta).exists

lemma mem_ball_iff_of_dist_lt_boundaryNeighborhood
    {M : Type*} [PseudoMetricSpace M] {n : ℕ}
    (center : Fin n → M) (radius : Fin n → ℝ)
    {k : ℕ} {x y : M}
    (hx : x ∉ ballBoundaryNeighborhood center radius k)
    (hxy : dist x y < 1 / ((k : ℝ) + 1)) (i : Fin n) :
    x ∈ Metric.ball (center i) (radius i) ↔
      y ∈ Metric.ball (center i) (radius i) := by
  have hmargin :
      1 / ((k : ℝ) + 1) < |dist x (center i) - radius i| := by
    apply lt_of_not_ge
    intro hnear
    apply hx
    exact Set.mem_iUnion_of_mem i hnear
  constructor
  · intro hxball
    rw [Metric.mem_ball] at hxball ⊢
    by_contra hyball
    have hyradius : radius i ≤ dist y (center i) := le_of_not_gt hyball
    have hxradius : dist x (center i) ≤ radius i := hxball.le
    rw [abs_of_nonpos (sub_nonpos.mpr hxradius)] at hmargin
    have hdiff : dist y (center i) - dist x (center i) ≤ dist x y := by
      calc
        dist y (center i) - dist x (center i) ≤
            |dist y (center i) - dist x (center i)| := le_abs_self _
        _ ≤ dist y x := abs_dist_sub_le y x (center i)
        _ = dist x y := dist_comm _ _
    linarith
  · intro hyball
    rw [Metric.mem_ball] at hyball ⊢
    by_contra hxball
    have hxradii : radius i ≤ dist x (center i) := le_of_not_gt hxball
    rw [abs_of_nonneg (sub_nonneg.mpr hxradii)] at hmargin
    have hdiff : dist x (center i) - dist y (center i) ≤ dist x y := by
      calc
        dist x (center i) - dist y (center i) ≤
            |dist x (center i) - dist y (center i)| := le_abs_self _
        _ ≤ dist x y := abs_dist_sub_le x y (center i)
    linarith

def centeredBoundaryBad
    {M : Type*} [PseudoMetricSpace M] {p : ℕ}
    (T T_inv : M → M) (center : Fin p → M) (radius : Fin p → ℝ)
    (k m n : ℕ) : Set M :=
  (⋃ j : Fin n,
      T^[j.val] ⁻¹' ballBoundaryNeighborhood center radius k) ∪
    ⋃ q : Fin m,
      T_inv^[q.val + 1] ⁻¹' ballBoundaryNeighborhood center radius k

lemma measurableSet_centeredBoundaryBad
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M] {p : ℕ}
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (center : Fin p → M) (radius : Fin p → ℝ) (k m n : ℕ) :
    MeasurableSet (centeredBoundaryBad T T_inv center radius k m n) := by
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro j
    exact (measurableSet_ballBoundaryNeighborhood center radius k).preimage
      (hT.iterate j.val)
  · apply MeasurableSet.iUnion
    intro q
    exact (measurableSet_ballBoundaryNeighborhood center radius k).preimage
      (hT_inv.iterate (q.val + 1))

lemma measure_centeredBoundaryBad_le
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] {p : ℕ}
    (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (center : Fin p → M) (radius : Fin p → ℝ) (k m n : ℕ) :
    mu (centeredBoundaryBad T T_inv center radius k m n) ≤
      (m + n) * mu (ballBoundaryNeighborhood center radius k) := by
  let U := ballBoundaryNeighborhood center radius k
  have hU : MeasurableSet U :=
    measurableSet_ballBoundaryNeighborhood center radius k
  have hforward :
      mu (⋃ j : Fin n, T^[j.val] ⁻¹' U) ≤ n * mu U := by
    calc
      mu (⋃ j : Fin n, T^[j.val] ⁻¹' U) ≤
          ∑' j : Fin n, mu (T^[j.val] ⁻¹' U) := measure_iUnion_le _
      _ = n * mu U := by
        simp_rw [(hT.iterate _).measure_preimage hU.nullMeasurableSet]
        simp
  have hbackward :
      mu (⋃ q : Fin m, T_inv^[q.val + 1] ⁻¹' U) ≤ m * mu U := by
    calc
      mu (⋃ q : Fin m, T_inv^[q.val + 1] ⁻¹' U) ≤
          ∑' q : Fin m, mu (T_inv^[q.val + 1] ⁻¹' U) := measure_iUnion_le _
      _ = m * mu U := by
        simp_rw [(hT_inv.iterate _).measure_preimage hU.nullMeasurableSet]
        simp
  calc
    mu (centeredBoundaryBad T T_inv center radius k m n) ≤
        mu (⋃ j : Fin n, T^[j.val] ⁻¹' U) +
          mu (⋃ q : Fin m, T_inv^[q.val + 1] ⁻¹' U) :=
      measure_union_le _ _
    _ ≤ n * mu U + m * mu U := add_le_add hforward hbackward
    _ = (m + n) * mu U := by
      ring

lemma exists_ae_eventually_avoids_centeredBoundaries
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] {p : ℕ}
    (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (center : Fin p → M) (radius : Fin p → ℝ)
    (hboundary : ∀ i, mu (Metric.sphere (center i) (radius i)) = 0)
    (m n : ℕ → ℕ) (hsplit : ∀ L, m L + n L = L) :
    ∃ k : ℕ → ℕ,
      (∀ᵐ x ∂mu, ∀ᶠ L in atTop,
        x ∉ centeredBoundaryBad T T_inv center radius (k L) (m L) (n L)) := by
  let eta : ℕ → ℝ≥0∞ := fun L =>
    (2⁻¹ : ℝ≥0∞) ^ (L + 1) / (L + 1)
  have heta (L : ℕ) : 0 < eta L := by
    dsimp [eta]
    apply ENNReal.div_pos
    · simp
    · simp
  choose k hk using fun L =>
    exists_ballBoundaryNeighborhood_measure_lt
      mu center radius hboundary (heta L)
  let bad : ℕ → Set M := fun L =>
    centeredBoundaryBad T T_inv center radius (k L) (m L) (n L)
  have hbad (L : ℕ) : mu (bad L) < (2⁻¹ : ℝ≥0∞) ^ (L + 1) := by
    by_cases hL : L = 0
    · subst L
      have hmeasure_zero : mu (bad 0) = 0 := by
        have hsplit_zero :
            (m 0 : ℝ≥0∞) + (n 0 : ℝ≥0∞) = 0 := by
          exact_mod_cast hsplit 0
        apply nonpos_iff_eq_zero.mp
        calc
          mu (bad 0) ≤ (m 0 + n 0) *
              mu (ballBoundaryNeighborhood center radius (k 0)) :=
            measure_centeredBoundaryBad_le
              mu T T_inv hT hT_inv center radius (k 0) (m 0) (n 0)
          _ = 0 := by rw [hsplit_zero, zero_mul]
      rw [hmeasure_zero]
      simp
    · have hLpos : (0 : ℝ≥0∞) < L := by
        exact_mod_cast Nat.pos_of_ne_zero hL
      have hsplit_cast :
          (m L : ℝ≥0∞) + (n L : ℝ≥0∞) = (L : ℝ≥0∞) := by
        exact_mod_cast hsplit L
      calc
        mu (bad L) ≤ (m L + n L) *
            mu (ballBoundaryNeighborhood center radius (k L)) :=
          measure_centeredBoundaryBad_le
            mu T T_inv hT hT_inv center radius (k L) (m L) (n L)
        _ = L * mu (ballBoundaryNeighborhood center radius (k L)) := by
          rw [hsplit_cast]
        _ < L * eta L := by
          simpa [mul_comm] using ENNReal.mul_lt_mul_left
            hLpos.ne' (ENNReal.natCast_ne_top L) (hk L)
        _ ≤ (L + 1) * eta L := by
          exact mul_le_mul_left (le_add_of_nonneg_right zero_le_one) _
        _ = (2⁻¹ : ℝ≥0∞) ^ (L + 1) := by
          dsimp [eta]
          exact ENNReal.mul_div_cancel (by simp) (by simp)
  have hsum : (∑' L, mu (bad L)) ≠ ⊤ := by
    apply ne_top_of_le_ne_top
      (show (∑' L : ℕ, (2⁻¹ : ℝ≥0∞) ^ (L + 1)) ≠ ⊤ by
        rw [ENNReal.tsum_geometric_add_one]
        norm_num)
    exact ENNReal.tsum_le_tsum fun L => (hbad L).le
  exact ⟨k, by
    simpa [bad] using ae_eventually_notMem hsum⟩

end Submission.Helpers
