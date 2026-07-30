import Submission.SparsePatternCover

namespace Submission.Helpers

open LeanEval.Dynamics

/-- For one centered partition atom, first split according to the good/bad
coarse-grid pattern and then apply the finite refinement attached to the
nonempty pattern fiber. -/
noncomputable def sparsePatternPieces
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ)
    (goodSet A : Set EucPlane) (m n H D : ℕ) :
    Finset (Set EucPlane) := by
  classical
  exact (gridPatterns H (m + n)).biUnion fun p =>
    if hbase :
        (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty then
      sparseEdgePieces T T_inv G F R m n H D
        (sparsePatternReference T T_inv G goodSet A m n H p hbase)
        (sparsePatternBase T T_inv G goodSet A m n H p)
    else
      ∅

lemma measurableSet_of_mem_sparsePatternPieces
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    {G goodSet A : Set EucPlane}
    (hG : MeasurableSet G) (hgood : MeasurableSet goodSet)
    (hA : MeasurableSet A)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ)
    {B : Set EucPlane}
    (hB : B ∈ sparsePatternPieces
      T T_inv G F R goodSet A m n H D) :
    MeasurableSet B := by
  classical
  rw [sparsePatternPieces] at hB
  obtain ⟨p, _hp, hBp⟩ := Finset.mem_biUnion.mp hB
  split_ifs at hBp with hbase
  · exact measurableSet_of_mem_sparseEdgePieces
      T T_inv hT hT_inv G F R m n H D
        (sparsePatternReference T T_inv G goodSet A m n H p hbase)
        (measurableSet_sparsePatternBase
          T T_inv hT hT_inv hG hgood hA m n H p) hBp
  · simp at hBp

lemma card_sparsePatternPieces_le
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ)
    (goodSet A : Set EucPlane) (m n : ℕ)
    {H : ℕ} (hH : 0 < H) (D B : ℕ)
    (hF : 0 < F.card)
    (hbad : ∀ c ∈ goodSet,
      sparseCenteredBadCount T T_inv G m n c ≤ B) :
    (sparsePatternPieces
        T T_inv G F R goodSet A m n H D).card ≤
      2 ^ (gridIndexSet H (m + n)).card *
        F.card ^ (4 * D * H * B) := by
  classical
  rw [sparsePatternPieces]
  calc
    ((gridPatterns H (m + n)).biUnion fun p =>
        if hbase :
            (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty then
          sparseEdgePieces T T_inv G F R m n H D
            (sparsePatternReference T T_inv G goodSet A m n H p hbase)
            (sparsePatternBase T T_inv G goodSet A m n H p)
        else ∅).card ≤
        ∑ p ∈ gridPatterns H (m + n),
          (if hbase :
              (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty then
            sparseEdgePieces T T_inv G F R m n H D
              (sparsePatternReference
                T T_inv G goodSet A m n H p hbase)
              (sparsePatternBase T T_inv G goodSet A m n H p)
          else ∅).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ gridPatterns H (m + n),
          F.card ^ (4 * D * H * B) := by
      apply Finset.sum_le_sum
      intro p _hp
      split_ifs with hbase
      · let c :=
          sparsePatternReference T T_inv G goodSet A m n H p hbase
        have hcbase :
            c ∈ sparsePatternBase T T_inv G goodSet A m n H p :=
          sparsePatternReference_mem
            T T_inv G goodSet A m n H p hbase
        have hdepth :
            (∑ k : Fin
                ((sparseSelectedSet T T_inv G m n H c).card - 1),
              sparseEdgeDepth T T_inv G m n H D c k) ≤
              4 * D * H * B := by
          calc
            _ ≤ 4 * D * H *
                (badGridIndices H (m + n)
                  (centeredOrbitGoodTime T T_inv G m n c)).card :=
              sum_sparseEdgeDepth_le_badGrid
                T T_inv G m n hH D c
            _ ≤ 4 * D * H *
                finiteBadCountNat
                  (centeredOrbitGoodTime T T_inv G m n c) (m + n) := by
              gcongr
              exact card_badGridIndices_le_finiteBadCountNat
                hH (centeredOrbitGoodTime T T_inv G m n c)
            _ = 4 * D * H *
                sparseCenteredBadCount T T_inv G m n c := by
              rw [finiteBadCountNat_centeredOrbitGoodTime]
            _ ≤ 4 * D * H * B := by
              gcongr
              exact hbad c hcbase.1.2
        exact (card_sparseEdgePieces_le
          T T_inv G F R m n H D c
            (sparsePatternBase T T_inv G goodSet A m n H p)).trans
          (Nat.pow_le_pow_right hF hdepth)
      · simp
    _ = (gridPatterns H (m + n)).card *
          F.card ^ (4 * D * H * B) := by simp
    _ = 2 ^ (gridIndexSet H (m + n)).card *
          F.card ^ (4 * D * H * B) := by
      rw [card_gridPatterns]

lemma sparsePatternPieces_cover
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane)
    (hF : ∀ u : EucPlane, ‖u‖ ≤ 1 → ∃ f ∈ F, dist u f < 1 / 4)
    {R : ℝ} (hR : 0 < R)
    (goodSet A : Set EucPlane) (m n H D : ℕ)
    (hclose : ∀ x ∈ A, ∀ y ∈ A, ∀ i : Fin (m + n),
      dist (centeredOrbit T T_inv m n x i)
        (centeredOrbit T T_inv m n y i) ≤ R) :
    A ∩ goodSet ⊆
      ⋃ B ∈ sparsePatternPieces
        T T_inv G F R goodSet A m n H D, B := by
  classical
  intro x hx
  let p := centeredGridPattern T T_inv G m n H x
  let base := sparsePatternBase T T_inv G goodSet A m n H p
  have hxbase : x ∈ base := by
    exact ⟨hx, mem_centeredGridPatternFiber_self T T_inv G m n H x⟩
  have hbase : base.Nonempty := ⟨x, hxbase⟩
  let c :=
    sparsePatternReference T T_inv G goodSet A m n H p hbase
  have hcbase : c ∈ base :=
    sparsePatternReference_mem T T_inv G goodSet A m n H p hbase
  have hbaseR : ∀ y ∈ base,
      ∀ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
        dist
          (centeredOrbit T T_inv m n y
            ⟨H * sparseNodeIndex T T_inv G m n H c
              (sparseEdgeLeft T T_inv G m n H c k),
              sparseNodeIndex_lt T T_inv G m n H c _⟩)
          (sparseEdgeStart T T_inv G m n H c k) ≤ R := by
    intro y hy k
    exact hclose y hy.1.1 c hcbase.1.1 _
  have hxcover := sparseEdgePieces_cover
    T T_inv G F hF hR m n H D c base hbaseR hxbase
  simp only [Set.mem_iUnion] at hxcover ⊢
  obtain ⟨B, hB, hxB⟩ := hxcover
  refine ⟨B, ?_, hxB⟩
  rw [sparsePatternPieces]
  apply Finset.mem_biUnion.mpr
  refine ⟨p, centeredGridPattern_mem_gridPatterns
    T T_inv G m n H x, ?_⟩
  simpa [base, c, hbase] using hB

/-- The pattern family restricted to fibers whose sampled bad times satisfy a
prescribed weighted budget.  The restriction is made at the finite-pattern
level, so measurability of the underlying point set is unchanged. -/
noncomputable def sparseBoundedPatternPieces
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ)
    (goodSet A : Set EucPlane) (m n H D B : ℕ) :
    Finset (Set EucPlane) := by
  classical
  exact (gridPatterns H (m + n)).biUnion fun p =>
    if hbase :
        (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty then
      if H * (badGridIndices H (m + n)
          (centeredOrbitGoodTime T T_inv G m n
            (sparsePatternReference
              T T_inv G goodSet A m n H p hbase))).card ≤ B then
        sparseEdgePieces T T_inv G F R m n H D
          (sparsePatternReference T T_inv G goodSet A m n H p hbase)
          (sparsePatternBase T T_inv G goodSet A m n H p)
      else
        ∅
    else
      ∅

lemma measurableSet_of_mem_sparseBoundedPatternPieces
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    {G goodSet A : Set EucPlane}
    (hG : MeasurableSet G) (hgood : MeasurableSet goodSet)
    (hA : MeasurableSet A)
    (F : Finset EucPlane) (R : ℝ) (m n H D B : ℕ)
    {U : Set EucPlane}
    (hU : U ∈ sparseBoundedPatternPieces
      T T_inv G F R goodSet A m n H D B) :
    MeasurableSet U := by
  classical
  rw [sparseBoundedPatternPieces] at hU
  obtain ⟨p, _hp, hUp⟩ := Finset.mem_biUnion.mp hU
  split_ifs at hUp with hbase hbound
  · exact measurableSet_of_mem_sparseEdgePieces
      T T_inv hT hT_inv G F R m n H D
        (sparsePatternReference T T_inv G goodSet A m n H p hbase)
        (measurableSet_sparsePatternBase
          T T_inv hT hT_inv hG hgood hA m n H p) hUp
  · simp at hUp
  · simp at hUp

lemma exists_sparseEdgePiece_of_mem_sparseBoundedPatternPieces
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ)
    (goodSet A : Set EucPlane) (m n H D B : ℕ)
    {U : Set EucPlane}
    (hU : U ∈ sparseBoundedPatternPieces
      T T_inv G F R goodSet A m n H D B) :
    ∃ p, ∃ hbase :
        (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty,
      H * (badGridIndices H (m + n)
          (centeredOrbitGoodTime T T_inv G m n
            (sparsePatternReference
              T T_inv G goodSet A m n H p hbase))).card ≤ B ∧
      ∃ label ∈ sparseEdgeLabels T T_inv G F R m n H D
          (sparsePatternReference
            T T_inv G goodSet A m n H p hbase),
        U = sparseEdgePiece T T_inv G m n H
          (sparsePatternReference
            T T_inv G goodSet A m n H p hbase)
          (sparsePatternBase T T_inv G goodSet A m n H p) label := by
  classical
  rw [sparseBoundedPatternPieces] at hU
  obtain ⟨p, _hp, hUp⟩ := Finset.mem_biUnion.mp hU
  split_ifs at hUp with hbase hbound
  · obtain ⟨label, hlabel, hEq⟩ := Finset.mem_image.mp hUp
    exact ⟨p, hbase, hbound, label, hlabel, hEq.symm⟩
  · simp at hUp
  · simp at hUp

lemma card_sparseBoundedPatternPieces_le
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ)
    (goodSet A : Set EucPlane) (m n : ℕ)
    {H : ℕ} (hH : 0 < H) (D B : ℕ)
    (hF : 0 < F.card) :
    (sparseBoundedPatternPieces
        T T_inv G F R goodSet A m n H D B).card ≤
      2 ^ (gridIndexSet H (m + n)).card *
        F.card ^ (4 * D * B) := by
  classical
  rw [sparseBoundedPatternPieces]
  calc
    ((gridPatterns H (m + n)).biUnion fun p =>
        if hbase :
            (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty then
          if H * (badGridIndices H (m + n)
              (centeredOrbitGoodTime T T_inv G m n
                (sparsePatternReference
                  T T_inv G goodSet A m n H p hbase))).card ≤ B then
            sparseEdgePieces T T_inv G F R m n H D
              (sparsePatternReference
                T T_inv G goodSet A m n H p hbase)
              (sparsePatternBase T T_inv G goodSet A m n H p)
          else ∅
        else ∅).card ≤
        ∑ p ∈ gridPatterns H (m + n),
          (if hbase :
              (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty then
            if H * (badGridIndices H (m + n)
                (centeredOrbitGoodTime T T_inv G m n
                  (sparsePatternReference
                    T T_inv G goodSet A m n H p hbase))).card ≤ B then
              sparseEdgePieces T T_inv G F R m n H D
                (sparsePatternReference
                  T T_inv G goodSet A m n H p hbase)
                (sparsePatternBase T T_inv G goodSet A m n H p)
            else ∅
          else ∅).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ gridPatterns H (m + n),
          F.card ^ (4 * D * B) := by
      apply Finset.sum_le_sum
      intro p _hp
      split_ifs with hbase hbound
      · let c :=
          sparsePatternReference T T_inv G goodSet A m n H p hbase
        have hdepth :
            (∑ k : Fin
                ((sparseSelectedSet T T_inv G m n H c).card - 1),
              sparseEdgeDepth T T_inv G m n H D c k) ≤
              4 * D * B := by
          calc
            _ ≤ 4 * D * H *
                (badGridIndices H (m + n)
                  (centeredOrbitGoodTime T T_inv G m n c)).card :=
              sum_sparseEdgeDepth_le_badGrid
                T T_inv G m n hH D c
            _ = 4 * D * (H *
                (badGridIndices H (m + n)
                  (centeredOrbitGoodTime T T_inv G m n c)).card) := by
              ring
            _ ≤ 4 * D * B := Nat.mul_le_mul_left (4 * D) hbound
        exact (card_sparseEdgePieces_le
          T T_inv G F R m n H D c
            (sparsePatternBase T T_inv G goodSet A m n H p)).trans
          (Nat.pow_le_pow_right hF hdepth)
      · simp
      · simp
    _ = (gridPatterns H (m + n)).card *
          F.card ^ (4 * D * B) := by simp
    _ = 2 ^ (gridIndexSet H (m + n)).card *
          F.card ^ (4 * D * B) := by
      rw [card_gridPatterns]

lemma sparseBoundedPatternPieces_cover
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane)
    (hF : ∀ u : EucPlane, ‖u‖ ≤ 1 → ∃ f ∈ F, dist u f < 1 / 4)
    {R : ℝ} (hR : 0 < R)
    (goodSet A : Set EucPlane) (m n H D B : ℕ)
    (hclose : ∀ x ∈ A, ∀ y ∈ A, ∀ i : Fin (m + n),
      dist (centeredOrbit T T_inv m n x i)
        (centeredOrbit T T_inv m n y i) ≤ R) :
    {x | x ∈ A ∩ goodSet ∧
      H * (badGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n x)).card ≤ B} ⊆
      ⋃ U ∈ sparseBoundedPatternPieces
        T T_inv G F R goodSet A m n H D B, U := by
  classical
  intro x hx
  let p := centeredGridPattern T T_inv G m n H x
  let base := sparsePatternBase T T_inv G goodSet A m n H p
  have hxbase : x ∈ base := by
    exact ⟨hx.1, mem_centeredGridPatternFiber_self T T_inv G m n H x⟩
  have hbase : base.Nonempty := ⟨x, hxbase⟩
  let c :=
    sparsePatternReference T T_inv G goodSet A m n H p hbase
  have hcbase : c ∈ base :=
    sparsePatternReference_mem T T_inv G goodSet A m n H p hbase
  have hbadEq :
      badGridIndices H (m + n)
          (centeredOrbitGoodTime T T_inv G m n c) =
        badGridIndices H (m + n)
          (centeredOrbitGoodTime T T_inv G m n x) :=
    badGridIndices_eq_of_mem_sparsePatternBase
      T T_inv G goodSet A m n H p hcbase hxbase
  have hbound : H * (badGridIndices H (m + n)
      (centeredOrbitGoodTime T T_inv G m n c)).card ≤ B := by
    rw [hbadEq]
    exact hx.2
  have hbaseR : ∀ y ∈ base,
      ∀ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
        dist
          (centeredOrbit T T_inv m n y
            ⟨H * sparseNodeIndex T T_inv G m n H c
              (sparseEdgeLeft T T_inv G m n H c k),
              sparseNodeIndex_lt T T_inv G m n H c _⟩)
          (sparseEdgeStart T T_inv G m n H c k) ≤ R := by
    intro y hy k
    exact hclose y hy.1.1 c hcbase.1.1 _
  have hxcover := sparseEdgePieces_cover
    T T_inv G F hF hR m n H D c base hbaseR hxbase
  simp only [Set.mem_iUnion] at hxcover ⊢
  obtain ⟨U, hU, hxU⟩ := hxcover
  refine ⟨U, ?_, hxU⟩
  rw [sparseBoundedPatternPieces]
  apply Finset.mem_biUnion.mpr
  refine ⟨p, centeredGridPattern_mem_gridPatterns
    T T_inv G m n H x, ?_⟩
  simpa [base, c, hbase, hbound] using hU

end Submission.Helpers
