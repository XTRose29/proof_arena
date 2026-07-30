import Submission.WeightedBoundaryPartition

namespace Submission.Helpers

open MeasureTheory Filter
open scoped ENNReal

def ballBoundaryNeighborhoodReal
    {M : Type*} [PseudoMetricSpace M] {p : ℕ}
    (center : Fin p → M) (radius : Fin p → ℝ) (delta : ℝ) : Set M :=
  ⋃ i, {x | |dist x (center i) - radius i| ≤ delta}

lemma measurableSet_ballBoundaryNeighborhoodReal
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M] {p : ℕ}
    (center : Fin p → M) (radius : Fin p → ℝ) (delta : ℝ) :
    MeasurableSet (ballBoundaryNeighborhoodReal center radius delta) := by
  apply MeasurableSet.iUnion
  intro i
  apply measurableSet_le
  · fun_prop
  · fun_prop

def centeredBoundaryBadReal
    {M : Type*} [PseudoMetricSpace M] {p : ℕ}
    (T T_inv : M → M) (center : Fin p → M) (radius : Fin p → ℝ)
    (delta : ℝ) (m n : ℕ) : Set M :=
  (⋃ j : Fin n,
      T^[j.val] ⁻¹' ballBoundaryNeighborhoodReal center radius delta) ∪
    ⋃ q : Fin m,
      T_inv^[q.val + 1] ⁻¹' ballBoundaryNeighborhoodReal center radius delta

lemma measurableSet_centeredBoundaryBadReal
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M] {p : ℕ}
    (T T_inv : M → M) (hT : Measurable T) (hT_inv : Measurable T_inv)
    (center : Fin p → M) (radius : Fin p → ℝ)
    (delta : ℝ) (m n : ℕ) :
    MeasurableSet (centeredBoundaryBadReal T T_inv center radius delta m n) := by
  apply MeasurableSet.union
  · apply MeasurableSet.iUnion
    intro j
    exact (measurableSet_ballBoundaryNeighborhoodReal center radius delta).preimage
      (hT.iterate j.val)
  · apply MeasurableSet.iUnion
    intro q
    exact (measurableSet_ballBoundaryNeighborhoodReal center radius delta).preimage
      (hT_inv.iterate (q.val + 1))

lemma measure_centeredBoundaryBadReal_le
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] {p : ℕ}
    (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (center : Fin p → M) (radius : Fin p → ℝ)
    (delta : ℝ) (m n : ℕ) :
    mu (centeredBoundaryBadReal T T_inv center radius delta m n) ≤
      (m + n) * mu (ballBoundaryNeighborhoodReal center radius delta) := by
  let U := ballBoundaryNeighborhoodReal center radius delta
  have hU : MeasurableSet U :=
    measurableSet_ballBoundaryNeighborhoodReal center radius delta
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
    mu (centeredBoundaryBadReal T T_inv center radius delta m n) ≤
        mu (⋃ j : Fin n, T^[j.val] ⁻¹' U) +
          mu (⋃ q : Fin m, T_inv^[q.val + 1] ⁻¹' U) :=
      measure_union_le _ _
    _ ≤ n * mu U + m * mu U := add_le_add hforward hbackward
    _ = (m + n) * mu U := by ring

lemma exists_ae_eventually_avoids_weighted_centeredBoundaries
    {M : Type*} [PseudoMetricSpace M] [MeasurableSpace M]
    [BorelSpace M]
    (mu : Measure M) [IsFiniteMeasure mu] {p : ℕ}
    (T T_inv : M → M)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    (center : Fin p → M) (radius : Fin p → ℝ)
    (delta : ℕ → ℝ) (m n : ℕ → ℕ)
    (hsum : ∀ i,
      (∑' L, (m L + n L : ℕ) *
        mu {x | |dist x (center i) - radius i| ≤ delta L}) ≠ ⊤) :
    ∀ᵐ x ∂mu, ∀ᶠ L in atTop,
      x ∉ centeredBoundaryBadReal
        T T_inv center radius (delta L) (m L) (n L) := by
  let strip : Fin p → ℕ → Set M := fun i L =>
    {x | |dist x (center i) - radius i| ≤ delta L}
  let bad : ℕ → Set M := fun L =>
    centeredBoundaryBadReal T T_inv center radius (delta L) (m L) (n L)
  have hneighborhood (L : ℕ) :
      mu (ballBoundaryNeighborhoodReal center radius (delta L)) ≤
        ∑' i : Fin p, mu (strip i L) := by
    exact measure_iUnion_le _
  have hbad (L : ℕ) :
      mu (bad L) ≤
        ∑' i : Fin p, (m L + n L : ℕ) * mu (strip i L) := by
    calc
      mu (bad L) ≤ (m L + n L) *
          mu (ballBoundaryNeighborhoodReal center radius (delta L)) :=
        measure_centeredBoundaryBadReal_le
          mu T T_inv hT hT_inv center radius (delta L) (m L) (n L)
      _ ≤ (m L + n L) * ∑' i : Fin p, mu (strip i L) :=
        mul_le_mul_right (hneighborhood L) _
      _ = ∑' i : Fin p, (m L + n L : ℕ) * mu (strip i L) := by
        simp only [Nat.cast_add]
        rw [ENNReal.tsum_mul_left]
  have htotal_le :
      (∑' L, mu (bad L)) ≤
        ∑' i : Fin p, ∑' L, (m L + n L : ℕ) * mu (strip i L) := by
    calc
      (∑' L, mu (bad L)) ≤
          ∑' L, ∑' i : Fin p,
            (m L + n L : ℕ) * mu (strip i L) :=
        ENNReal.tsum_le_tsum hbad
      _ = ∑' i : Fin p, ∑' L,
          (m L + n L : ℕ) * mu (strip i L) := ENNReal.tsum_comm
  have htotal_rhs :
      (∑' i : Fin p, ∑' L,
        (m L + n L : ℕ) * mu (strip i L)) ≠ ⊤ := by
    rw [tsum_fintype]
    exact ENNReal.sum_ne_top.2 fun i _hi => by
      simpa [strip] using hsum i
  have htotal : (∑' L, mu (bad L)) ≠ ⊤ :=
    ne_top_of_le_ne_top htotal_rhs htotal_le
  simpa [bad] using ae_eventually_notMem htotal

end Submission.Helpers
