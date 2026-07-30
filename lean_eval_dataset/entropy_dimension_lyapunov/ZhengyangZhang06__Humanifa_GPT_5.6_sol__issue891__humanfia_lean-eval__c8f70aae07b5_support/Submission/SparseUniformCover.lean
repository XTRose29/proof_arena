import Submission.SparsePathRate
import Submission.PesinStructuralCarrier
import Submission.UniformMultiplicityHausdorff
import Submission.SmallPartitions

namespace Submission.Helpers

open LeanEval.Dynamics MeasureTheory
open scoped ENNReal

def orbitWindowPreimage
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m j : ℕ) : Set EucPlane :=
  (fun x => T^[j] (T_inv^[m] x)) ⁻¹' G

lemma measurableSet_orbitWindowPreimage
    (T T_inv : EucPlane → EucPlane)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    {G : Set EucPlane} (hG : MeasurableSet G) (m j : ℕ) :
    MeasurableSet (orbitWindowPreimage T T_inv G m j) := by
  exact hG.preimage ((hT.iterate j).comp (hT_inv.iterate m))

lemma measureReal_compl_orbitWindowPreimage
    (mu : Measure EucPlane)
    (T T_inv : EucPlane → EucPlane)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    {G : Set EucPlane} (hG : MeasurableSet G) (m j : ℕ) :
    mu.real (orbitWindowPreimage T T_inv G m j)ᶜ = mu.real Gᶜ := by
  rw [measureReal_def, measureReal_def]
  change ENNReal.toReal
    (mu ((T_inv^[m]) ⁻¹' ((T^[j]) ⁻¹' Gᶜ))) = _
  rw [(hT_inv.iterate m).measure_preimage
      (hG.compl.preimage (hT.iterate j).measurable).nullMeasurableSet,
    (hT.iterate j).measure_preimage hG.compl.nullMeasurableSet]

def sparseWindowGoodSet
    (T T_inv : EucPlane → EucPlane)
    (carrier G : Set EucPlane) (q : ℝ)
    (m n H : ℕ) : Set EucPlane :=
  (((carrier ∩ orbitWindowPreimage T T_inv
      (maximalForwardBadPrefixBlock (T^[H]) G q) m 0) ∩
      orbitWindowPreimage T T_inv G m 0) ∩
    orbitWindowPreimage T T_inv G m (H * (m / H))) ∩
  orbitWindowPreimage T T_inv G m (H * ((m + n - 1) / H))

lemma measurableSet_sparseWindowGoodSet
    (T T_inv : EucPlane → EucPlane)
    (hT : Measurable T) (hT_inv : Measurable T_inv)
    {carrier G : Set EucPlane}
    (hcarrier : MeasurableSet carrier) (hG : MeasurableSet G)
    (q : ℝ) (m n H : ℕ) :
    MeasurableSet (sparseWindowGoodSet T T_inv carrier G q m n H) := by
  exact (((hcarrier.inter
      (measurableSet_orbitWindowPreimage T T_inv hT hT_inv
        (measurableSet_maximalForwardBadPrefixBlock
          (hT.iterate H) hG q) m 0)).inter
    (measurableSet_orbitWindowPreimage T T_inv hT hT_inv hG m 0)).inter
    (measurableSet_orbitWindowPreimage T T_inv hT hT_inv hG
      m (H * (m / H)))).inter
    (measurableSet_orbitWindowPreimage T T_inv hT hT_inv hG
      m (H * ((m + n - 1) / H)))

lemma measureReal_compl_inter_le
    (mu : Measure EucPlane) (A B : Set EucPlane) :
    mu.real (A ∩ B)ᶜ ≤ mu.real Aᶜ + mu.real Bᶜ := by
  rw [Set.compl_inter]
  exact measureReal_union_le _ _

lemma measureReal_compl_sparseWindowGoodSet_le
    (mu : Measure EucPlane)
    (T T_inv : EucPlane → EucPlane)
    (hT : MeasurePreserving T mu mu)
    (hT_inv : MeasurePreserving T_inv mu mu)
    {carrier G : Set EucPlane}
    (hcarrier_full : mu carrierᶜ = 0) (hG : MeasurableSet G)
    {q gammaPrefix gammaG : ℝ} (m n H : ℕ)
    (hprefix :
      mu.real (maximalForwardBadPrefixBlock (T^[H]) G q)ᶜ ≤ gammaPrefix)
    (hGcompl : mu.real Gᶜ ≤ gammaG) :
    mu.real (sparseWindowGoodSet T T_inv carrier G q m n H)ᶜ ≤
      gammaPrefix + 3 * gammaG := by
  have hcarrier_real : mu.real carrierᶜ = 0 := by
    simp [measureReal_def, hcarrier_full]
  have horbit (j : ℕ) :
      mu.real (orbitWindowPreimage T T_inv G m j)ᶜ ≤ gammaG := by
    rw [measureReal_compl_orbitWindowPreimage
      mu T T_inv hT hT_inv hG]
    exact hGcompl
  have hcarrierPrefix :
      mu.real (carrier ∩
        orbitWindowPreimage T T_inv
          (maximalForwardBadPrefixBlock (T^[H]) G q) m 0)ᶜ ≤
        gammaPrefix := by
    have hprefixMeasurable :
        MeasurableSet (maximalForwardBadPrefixBlock (T^[H]) G q) :=
      measurableSet_maximalForwardBadPrefixBlock
        (hT.measurable.iterate H) hG q
    have hprefixOrbit :
        mu.real (orbitWindowPreimage T T_inv
          (maximalForwardBadPrefixBlock (T^[H]) G q) m 0)ᶜ ≤
          gammaPrefix := by
      rw [measureReal_compl_orbitWindowPreimage
        mu T T_inv hT hT_inv hprefixMeasurable]
      exact hprefix
    calc
      mu.real (carrier ∩
          orbitWindowPreimage T T_inv
            (maximalForwardBadPrefixBlock (T^[H]) G q) m 0)ᶜ ≤
        mu.real carrierᶜ +
          mu.real (orbitWindowPreimage T T_inv
            (maximalForwardBadPrefixBlock (T^[H]) G q) m 0)ᶜ :=
        measureReal_compl_inter_le _ _ _
      _ ≤ 0 + gammaPrefix := add_le_add hcarrier_real.le hprefixOrbit
      _ = gammaPrefix := zero_add _
  unfold sparseWindowGoodSet
  calc
    mu.real
        (((carrier ∩ orbitWindowPreimage T T_inv
            (maximalForwardBadPrefixBlock (T^[H]) G q) m 0) ∩
          orbitWindowPreimage T T_inv G m 0) ∩
          orbitWindowPreimage T T_inv G m (H * (m / H)) ∩
          orbitWindowPreimage T T_inv G m
            (H * ((m + n - 1) / H)))ᶜ ≤
        mu.real
            (((carrier ∩ orbitWindowPreimage T T_inv
                (maximalForwardBadPrefixBlock (T^[H]) G q) m 0) ∩
              orbitWindowPreimage T T_inv G m 0) ∩
              orbitWindowPreimage T T_inv G m (H * (m / H)))ᶜ +
          mu.real (orbitWindowPreimage T T_inv G m
            (H * ((m + n - 1) / H)))ᶜ :=
      measureReal_compl_inter_le _ _ _
    _ ≤ (mu.real
          ((carrier ∩ orbitWindowPreimage T T_inv
              (maximalForwardBadPrefixBlock (T^[H]) G q) m 0) ∩
            orbitWindowPreimage T T_inv G m 0)ᶜ +
          mu.real
            (orbitWindowPreimage T T_inv G m (H * (m / H)))ᶜ) +
        mu.real (orbitWindowPreimage T T_inv G m
          (H * ((m + n - 1) / H)))ᶜ := by
      gcongr
      exact measureReal_compl_inter_le _ _ _
    _ ≤ ((mu.real
          (carrier ∩ orbitWindowPreimage T T_inv
            (maximalForwardBadPrefixBlock (T^[H]) G q) m 0)ᶜ +
          mu.real (orbitWindowPreimage T T_inv G m 0)ᶜ) +
        mu.real (orbitWindowPreimage T T_inv G m (H * (m / H)))ᶜ) +
        mu.real (orbitWindowPreimage T T_inv G m
          (H * ((m + n - 1) / H)))ᶜ := by
      gcongr
      exact measureReal_compl_inter_le _ _ _
    _ ≤ ((gammaPrefix + gammaG) + gammaG) + gammaG :=
      add_le_add
        (add_le_add
          (add_le_add hcarrierPrefix (horbit 0))
          (horbit (H * (m / H))))
        (horbit (H * ((m + n - 1) / H)))
    _ = gammaPrefix + 3 * gammaG := by ring

lemma sum_sparseEdgeLongTime_le_badGrid
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    {m n H : ℕ} (hH : 0 < H) (c : EucPlane)
    (hpath : 0 < (sparseSelectedSet T T_inv G m n H c).card) :
    (∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
      if 1 < sparseEdgeIndexGap T T_inv G m n H c k then
        sparseEdgeTimeGap T T_inv G m n H c k else 0) ≤
      2 * H * (badGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c)).card := by
  simp only [sparseSelectedSet, sparseEdgeIndexGap, sparseEdgeTimeGap,
    sparseNodeIndex, sparseEdgeLeft, sparseEdgeRight,
    selectedGridIndex] at hpath ⊢
  let M := (selectedGridIndices H (m + n)
    (centeredOrbitGoodTime T T_inv G m n c)).card
  let N := M - 1
  have hcard : M = N + 1 := by
    dsimp [N]
    omega
  have hmain := selectedGridLongGapSum_le_bad hH
    (centeredOrbitGoodTime T T_inv G m n c) hcard
  convert hmain using 1
  apply Finset.sum_congr rfl
  intro k _hk
  simp only [M, N]
  congr 3

lemma sum_sparseEdgeDepth_le_badGrid
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    {m n H D : ℕ} (hH : 0 < H) (c : EucPlane)
    (hpath : 0 < (sparseSelectedSet T T_inv G m n H c).card) :
    (∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
      sparseEdgeDepth T T_inv G m n H D c k) ≤
      4 * D * H * (badGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c)).card := by
  have hpoint
      (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
      sparseEdgeDepth T T_inv G m n H D c k ≤
        2 * D *
          (if 1 < sparseEdgeIndexGap T T_inv G m n H c k then
            sparseEdgeTimeGap T T_inv G m n H c k else 0) := by
    by_cases hlong : 1 < sparseEdgeIndexGap T T_inv G m n H c k
    · rw [sparseEdgeDepth, if_pos hlong, if_pos hlong]
      rw [show 2 * D * sparseEdgeTimeGap T T_inv G m n H c k =
        D * (2 * sparseEdgeTimeGap T T_inv G m n H c k) by ring]
      apply Nat.mul_le_mul_left D
      have htime_pos :
          0 < sparseEdgeTimeGap T T_inv G m n H c k := by
        rw [sparseEdgeTimeGap]
        exact Nat.mul_pos hH (by omega)
      omega
    · simp [sparseEdgeDepth, hlong]
  calc
    (∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
        sparseEdgeDepth T T_inv G m n H D c k) ≤
        ∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
          2 * D *
            (if 1 < sparseEdgeIndexGap T T_inv G m n H c k then
              sparseEdgeTimeGap T T_inv G m n H c k else 0) :=
      Finset.sum_le_sum fun k _hk => hpoint k
    _ = 2 * D *
        (∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
          if 1 < sparseEdgeIndexGap T T_inv G m n H c k then
            sparseEdgeTimeGap T T_inv G m n H c k else 0) := by
      rw [Finset.mul_sum]
    _ ≤ 2 * D * (2 * H * (badGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c)).card) :=
      Nat.mul_le_mul_left (2 * D)
        (sum_sparseEdgeLongTime_le_badGrid
          T T_inv G hH c hpath)
    _ = 4 * D * H * (badGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c)).card := by ring

noncomputable def sparseBadBudget (q : ℝ) (H L : ℕ) : ℕ :=
  ⌈q * (((L / H + 1 : ℕ) : ℝ))⌉₊

lemma badGrid_card_le_sparseBadBudget
    (T T_inv : EucPlane → EucPlane)
    (G : Set EucPlane) {q : ℝ} {m n H : ℕ}
    (hH : 0 < H)
    {c : EucPlane}
    (hc : T_inv^[m] c ∈
      maximalForwardBadPrefixBlock (T^[H]) G q) :
    (badGridIndices H (m + n)
      (centeredOrbitGoodTime T T_inv G m n c)).card ≤
      sparseBadBudget q H (m + n) := by
  classical
  let N := (m + n) / H + 1
  let badCoarse :=
    (Finset.range N).filter fun j =>
      ¬(T^[H])^[j] (T_inv^[m] c) ∈ G
  have hsubset :
      badGridIndices H (m + n)
          (centeredOrbitGoodTime T T_inv G m n c) ⊆
        badCoarse := by
    intro j hj
    have hj' := mem_badGridIndices_iff.mp hj
    have hjN : j < N := by
      dsimp [N]
      rw [Nat.lt_add_one_iff]
      exact (Nat.le_div_iff_mul_le hH).2 (by
        simpa [Nat.mul_comm] using hj'.2.1.le)
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_range.mpr hjN, ?_⟩
    intro hjgood
    apply hj'.2.2
    refine ⟨hj'.2.1, ?_⟩
    simpa only [centeredOrbit, Function.iterate_mul] using hjgood
  have hgrid := Finset.card_le_card hsubset
  have hbadCount :
      ((badCoarse.card : ℕ) : ℝ) =
        badCount
          (fun j => (T^[H])^[j] (T_inv^[m] c) ∈ G) 0 N := by
    dsimp [badCoarse]
    rw [badCount, Finset.card_eq_sum_ones]
    push_cast
    simp only [Finset.sum_filter, Nat.zero_add]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hgood : (T^[H])^[j] (T_inv^[m] c) ∈ G <;>
      simp [hgood]
  have hprefix :=
    (mem_maximalForwardBadPrefixBlock_iff
      (T^[H]) G q (T_inv^[m] c)).mp hc N
  have hgrid_real :
      ((badGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c)).card : ℝ) ≤
        badCount
          (fun j => (T^[H])^[j] (T_inv^[m] c) ∈ G) 0 N := by
    calc
      ((badGridIndices H (m + n)
          (centeredOrbitGoodTime T T_inv G m n c)).card : ℝ) ≤
          (badCoarse.card : ℕ) := by
        exact_mod_cast hgrid
      _ = _ := hbadCount
  have hreal :
      ((badGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c)).card : ℝ) ≤
        q * ((((m + n) / H + 1 : ℕ) : ℝ)) := by
    exact hgrid_real.trans hprefix
  have hceil :
      ((badGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c)).card : ℝ) ≤
        (sparseBadBudget q H (m + n) : ℕ) :=
    hreal.trans (by
      dsimp [sparseBadBudget]
      simpa only [Nat.cast_add, Nat.cast_one] using
        (Nat.le_ceil (q * (((m + n) / H : ℕ) + 1))))
  exact_mod_cast hceil

noncomputable def sparsePieceMultiplicity
    (Fcard H D : ℕ) (q : ℝ) (L : ℕ) : ℕ :=
  (gridPatterns H L).card *
    Fcard ^ (4 * D * H * sparseBadBudget q H L)

noncomputable def sparsePatternPieces
    (T T_inv : EucPlane → EucPlane) (G goodSet A : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ)
    (p : ↥(gridIndexSet H (m + n)) → Bool) :
    Finset (Set EucPlane) := by
  classical
  exact
    if hbase : (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty then
      sparseEdgePieces T T_inv G F R m n H D
        (sparsePatternReference T T_inv G goodSet A m n H p hbase)
        (sparsePatternBase T T_inv G goodSet A m n H p)
    else
      ∅

noncomputable def sparseWindowPieces
    (T T_inv : EucPlane → EucPlane) (G goodSet A : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ) :
    Finset (Set EucPlane) :=
  (gridPatterns H (m + n)).biUnion fun p =>
    sparsePatternPieces T T_inv G goodSet A F R m n H D p

lemma measurableSet_of_mem_sparsePatternPieces
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    {G goodSet A : Set EucPlane}
    (hG : MeasurableSet G) (hgood : MeasurableSet goodSet)
    (hA : MeasurableSet A)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ)
    (p : ↥(gridIndexSet H (m + n)) → Bool)
    {B : Set EucPlane}
    (hB : B ∈ sparsePatternPieces
      T T_inv G goodSet A F R m n H D p) :
    MeasurableSet B := by
  classical
  by_cases hbase :
      (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty
  · rw [sparsePatternPieces, dif_pos hbase] at hB
    exact measurableSet_of_mem_sparseEdgePieces
      T T_inv hT hT_inv G F R m n H D
        (sparsePatternReference T T_inv G goodSet A m n H p hbase)
        (measurableSet_sparsePatternBase
          T T_inv hT hT_inv hG hgood hA m n H p) hB
  · rw [sparsePatternPieces, dif_neg hbase] at hB
    simp at hB

lemma measurableSet_of_mem_sparseWindowPieces
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    {G goodSet A : Set EucPlane}
    (hG : MeasurableSet G) (hgood : MeasurableSet goodSet)
    (hA : MeasurableSet A)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ)
    {B : Set EucPlane}
    (hB : B ∈ sparseWindowPieces
      T T_inv G goodSet A F R m n H D) :
    MeasurableSet B := by
  classical
  obtain ⟨p, _hp, hBp⟩ := Finset.mem_biUnion.mp hB
  exact measurableSet_of_mem_sparsePatternPieces
    T T_inv hT hT_inv hG hgood hA F R m n H D p hBp

lemma sparsePatternReference_mem_A
    (T T_inv : EucPlane → EucPlane) (G goodSet A : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool)
    (hbase : (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty) :
    sparsePatternReference T T_inv G goodSet A m n H p hbase ∈ A :=
  (sparsePatternReference_mem
    T T_inv G goodSet A m n H p hbase).1.1

lemma sparsePatternReference_mem_goodSet
    (T T_inv : EucPlane → EucPlane) (G goodSet A : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool)
    (hbase : (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty) :
    sparsePatternReference T T_inv G goodSet A m n H p hbase ∈ goodSet :=
  (sparsePatternReference_mem
    T T_inv G goodSet A m n H p hbase).1.2

lemma sparsePatternBase_selected_orbit_mem
    (T T_inv : EucPlane → EucPlane) (G goodSet A : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool)
    {c y : EucPlane}
    (hc : c ∈ sparsePatternBase T T_inv G goodSet A m n H p)
    (hy : y ∈ sparsePatternBase T T_inv G goodSet A m n H p)
    (i : Fin (sparseSelectedSet T T_inv G m n H c).card) :
    centeredOrbit T T_inv m n y
      ⟨H * sparseNodeIndex T T_inv G m n H c i,
        sparseNodeIndex_lt T T_inv G m n H c i⟩ ∈ G := by
  let j := sparseNodeIndex T T_inv G m n H c i
  have hjselected :
      j ∈ selectedGridIndices H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c) :=
    selectedGridIndex_mem H (m + n)
      (centeredOrbitGoodTime T T_inv G m n c) i
  have hjgrid : j ∈ gridIndexSet H (m + n) := by
    have hj := mem_selectedGridIndices_iff.mp hjselected
    exact mem_gridIndexSet_iff.mpr ⟨hj.1, hj.2.1⟩
  have hcgood :
      centeredOrbitGoodTime T T_inv G m n c (H * j) :=
    selectedGridIndex_good H (m + n)
      (centeredOrbitGoodTime T T_inv G m n c) i
  have hygood :
      centeredOrbitGoodTime T T_inv G m n y (H * j) :=
    (same_centeredGridPattern_goodTime_iff
      T T_inv G m n H p hc.2 hy.2 hjgrid).mp hcgood
  exact (centeredOrbitGoodTime_iff T T_inv G m n y
    (sparseNodeIndex_lt T T_inv G m n H c i)).mp hygood

lemma zero_mem_sparseSelectedSet_of_mem_sparseWindowGoodSet
    (T T_inv : EucPlane → EucPlane) (carrier G : Set EucPlane)
    (q : ℝ) {m n H : ℕ} (hn : 0 < n) {c : EucPlane}
    (hc : c ∈ sparseWindowGoodSet T T_inv carrier G q m n H) :
    0 ∈ sparseSelectedSet T T_inv G m n H c := by
  apply mem_selectedGridIndices_iff.mpr
  have hL : 0 < m + n := by omega
  refine ⟨hL, by simpa using hL, ?_⟩
  exact ⟨hL, by
    simpa [orbitWindowPreimage, centeredOrbit] using hc.1.1.2⟩

lemma center_mem_sparseSelectedSet_of_mem_sparseWindowGoodSet
    (T T_inv : EucPlane → EucPlane) (carrier G : Set EucPlane)
    (q : ℝ) {m n H : ℕ} (hn : 0 < n) {c : EucPlane}
    (hc : c ∈ sparseWindowGoodSet T T_inv carrier G q m n H) :
    m / H ∈ sparseSelectedSet T T_inv G m n H c := by
  apply mem_selectedGridIndices_iff.mpr
  have htime : H * (m / H) < m + n :=
    (Nat.mul_div_le m H).trans_lt (by omega)
  refine ⟨(Nat.div_le_self m H).trans_lt (by omega), htime, ?_⟩
  exact ⟨htime, by
    simpa [orbitWindowPreimage, centeredOrbit] using hc.1.2⟩

lemma last_mem_sparseSelectedSet_of_mem_sparseWindowGoodSet
    (T T_inv : EucPlane → EucPlane) (carrier G : Set EucPlane)
    (q : ℝ) {m n H : ℕ} (hn : 0 < n) {c : EucPlane}
    (hc : c ∈ sparseWindowGoodSet T T_inv carrier G q m n H) :
    (m + n - 1) / H ∈ sparseSelectedSet T T_inv G m n H c := by
  have hL : 0 < m + n := by omega
  have htime : H * ((m + n - 1) / H) < m + n :=
    (Nat.mul_div_le (m + n - 1) H).trans_lt (by omega)
  apply mem_selectedGridIndices_iff.mpr
  refine ⟨(Nat.div_le_self (m + n - 1) H).trans_lt (by omega),
    htime, ?_⟩
  exact ⟨htime, by
    simpa [orbitWindowPreimage, centeredOrbit] using hc.2⟩

lemma sparseSelectedSet_card_pos_of_mem_sparseWindowGoodSet
    (T T_inv : EucPlane → EucPlane) (carrier G : Set EucPlane)
    (q : ℝ) {m n H : ℕ} (hn : 0 < n) {c : EucPlane}
    (hc : c ∈ sparseWindowGoodSet T T_inv carrier G q m n H) :
    0 < (sparseSelectedSet T T_inv G m n H c).card :=
  Finset.card_pos.mpr
    ⟨0, zero_mem_sparseSelectedSet_of_mem_sparseWindowGoodSet
      T T_inv carrier G q hn hc⟩

lemma sparseWindowPieces_cover
    (T T_inv : EucPlane → EucPlane)
    (G carrier : Set EucPlane) (q : ℝ)
    (P : Finset (Set EucPlane))
    {delta R : ℝ} (hdelta : 0 ≤ delta) (hdeltaR : delta ≤ R)
    (hP_diam : ∀ A ∈ P, Metric.ediam A ≤ ENNReal.ofReal delta)
    {A : Set EucPlane} {m n H D : ℕ}
    (hA : A ∈ centeredJoin T T_inv P m n)
    (F : Finset EucPlane)
    (hF : ∀ u : EucPlane, ‖u‖ ≤ 1 →
      ∃ f ∈ F, dist u f < 1 / 4)
    (hR : 0 < R) :
    A ∩ sparseWindowGoodSet T T_inv carrier G q m n H ⊆
      ⋃ B ∈ sparseWindowPieces T T_inv G
        (sparseWindowGoodSet T T_inv carrier G q m n H)
        A F R m n H D, B := by
  classical
  rintro y ⟨hyA, hygood⟩
  let p := centeredGridPattern T T_inv G m n H y
  have hp : p ∈ gridPatterns H (m + n) :=
    centeredGridPattern_mem_gridPatterns T T_inv G m n H y
  have hybase : y ∈ sparsePatternBase T T_inv G
      (sparseWindowGoodSet T T_inv carrier G q m n H)
      A m n H p :=
    ⟨⟨hyA, hygood⟩,
      mem_centeredGridPatternFiber_self T T_inv G m n H y⟩
  have hbase : (sparsePatternBase T T_inv G
      (sparseWindowGoodSet T T_inv carrier G q m n H)
      A m n H p).Nonempty :=
    ⟨y, hybase⟩
  let c := sparsePatternReference T T_inv G
    (sparseWindowGoodSet T T_inv carrier G q m n H)
    A m n H p hbase
  have hcA : c ∈ A :=
    sparsePatternReference_mem_A T T_inv G
      (sparseWindowGoodSet T T_inv carrier G q m n H)
      A m n H p hbase
  have hbaseR :
      ∀ z ∈ sparsePatternBase T T_inv G
          (sparseWindowGoodSet T T_inv carrier G q m n H)
          A m n H p,
        ∀ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
          dist
            (centeredOrbit T T_inv m n z
              ⟨H * sparseNodeIndex T T_inv G m n H c
                (sparseEdgeLeft T T_inv G m n H c k),
                sparseNodeIndex_lt T T_inv G m n H c _⟩)
            (sparseEdgeStart T T_inv G m n H c k) ≤ R := by
    intro z hz k
    have hnorm :=
      norm_sparseSelected_orbit_sub_le_of_mem_centeredJoin_atom
        T T_inv G P hdelta hP_diam c hA hcA hz.1.1
          (sparseEdgeLeft T T_inv G m n H c k)
    simpa [sparseEdgeStart, centeredOrbit, dist_eq_norm] using
      hnorm.trans hdeltaR
  have hycover := sparseEdgePieces_cover
    T T_inv G F hF hR m n H D c
      (sparsePatternBase T T_inv G
        (sparseWindowGoodSet T T_inv carrier G q m n H)
        A m n H p) hbaseR hybase
  simp only [Set.mem_iUnion] at hycover
  obtain ⟨B, hB, hyB⟩ := hycover
  have hBwindow : B ∈ sparseWindowPieces T T_inv G
      (sparseWindowGoodSet T T_inv carrier G q m n H)
      A F R m n H D := by
    apply Finset.mem_biUnion.mpr
    refine ⟨p, hp, ?_⟩
    rw [sparsePatternPieces, dif_pos hbase]
    exact hB
  exact Set.mem_iUnion_of_mem B
    (Set.mem_iUnion_of_mem hBwindow hyB)

lemma card_sparsePatternPieces_le
    (T T_inv : EucPlane → EucPlane)
    (G carrier : Set EucPlane) {q R : ℝ}
    (A : Set EucPlane) (F : Finset EucPlane)
    {m n H D : ℕ} (hH : 0 < H) (hn : 0 < n)
    (hF : F.Nonempty)
    (p : ↥(gridIndexSet H (m + n)) → Bool) :
    (sparsePatternPieces T T_inv G
      (sparseWindowGoodSet T T_inv carrier G q m n H)
      A F R m n H D p).card ≤
      F.card ^ (4 * D * H * sparseBadBudget q H (m + n)) := by
  classical
  by_cases hbase : (sparsePatternBase T T_inv G
      (sparseWindowGoodSet T T_inv carrier G q m n H)
      A m n H p).Nonempty
  · rw [sparsePatternPieces, dif_pos hbase]
    let c := sparsePatternReference T T_inv G
      (sparseWindowGoodSet T T_inv carrier G q m n H)
      A m n H p hbase
    have hcgood :
        c ∈ sparseWindowGoodSet T T_inv carrier G q m n H :=
      sparsePatternReference_mem_goodSet T T_inv G
        (sparseWindowGoodSet T T_inv carrier G q m n H)
        A m n H p hbase
    have hpath : 0 < (sparseSelectedSet T T_inv G m n H c).card :=
      sparseSelectedSet_card_pos_of_mem_sparseWindowGoodSet
        T T_inv carrier G q hn hcgood
    have hdepth :
        (∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
          sparseEdgeDepth T T_inv G m n H D c k) ≤
          4 * D * H * (badGridIndices H (m + n)
            (centeredOrbitGoodTime T T_inv G m n c)).card :=
      sum_sparseEdgeDepth_le_badGrid T T_inv G hH c hpath
    have hbad :
        (badGridIndices H (m + n)
          (centeredOrbitGoodTime T T_inv G m n c)).card ≤
          sparseBadBudget q H (m + n) := by
      have hprefix :
          T_inv^[m] c ∈ maximalForwardBadPrefixBlock (T^[H]) G q := by
        simpa [orbitWindowPreimage] using hcgood.1.1.1.2
      exact badGrid_card_le_sparseBadBudget
        T T_inv G hH hprefix
    have hFcard : 0 < F.card := Finset.card_pos.mpr hF
    calc
      (sparseEdgePieces T T_inv G F R m n H D c
          (sparsePatternBase T T_inv G
            (sparseWindowGoodSet T T_inv carrier G q m n H)
            A m n H p)).card ≤
          F.card ^
            ∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
              sparseEdgeDepth T T_inv G m n H D c k :=
        card_sparseEdgePieces_le T T_inv G F R m n H D c _
      _ ≤ F.card ^ (4 * D * H *
          (badGridIndices H (m + n)
            (centeredOrbitGoodTime T T_inv G m n c)).card) :=
        Nat.pow_le_pow_right hFcard hdepth
      _ ≤ F.card ^ (4 * D * H * sparseBadBudget q H (m + n)) :=
        Nat.pow_le_pow_right hFcard
          (Nat.mul_le_mul_left (4 * D * H) hbad)
  · rw [sparsePatternPieces, dif_neg hbase]
    exact Nat.zero_le _

lemma card_sparseWindowPieces_le
    (T T_inv : EucPlane → EucPlane)
    (G carrier : Set EucPlane) {q R : ℝ}
    (A : Set EucPlane) (F : Finset EucPlane)
    {m n H D : ℕ} (hH : 0 < H) (hn : 0 < n)
    (hF : F.Nonempty) :
    (sparseWindowPieces T T_inv G
      (sparseWindowGoodSet T T_inv carrier G q m n H)
      A F R m n H D).card ≤
      sparsePieceMultiplicity F.card H D q (m + n) := by
  classical
  calc
    (sparseWindowPieces T T_inv G
        (sparseWindowGoodSet T T_inv carrier G q m n H)
        A F R m n H D).card ≤
        ∑ p ∈ gridPatterns H (m + n),
          (sparsePatternPieces T T_inv G
            (sparseWindowGoodSet T T_inv carrier G q m n H)
            A F R m n H D p).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _p ∈ gridPatterns H (m + n),
        F.card ^ (4 * D * H * sparseBadBudget q H (m + n)) := by
      apply Finset.sum_le_sum
      intro p _hp
      exact card_sparsePatternPieces_le
        T T_inv G carrier A F hH hn hF p
    _ = sparsePieceMultiplicity F.card H D q (m + n) := by
      simp [sparsePieceMultiplicity]

set_option maxHeartbeats 4000000 in
lemma ediam_of_mem_sparsePatternPieces_balanced
    (T T_inv : EucPlane → EucPlane)
    (hT_smooth : ContDiff ℝ 2 T) (hT_inv_smooth : ContDiff ℝ 2 T_inv)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    {K S carrier G : Set EucPlane}
    (hK_inv : T '' K = K) (hKS : K ⊆ S) (hS_convex : Convex ℝ S)
    (hcarrier : T '' carrier = carrier) (hcarrierK : carrier ⊆ K)
    (hsource : ∀ z ∈ carrier, SourceSplittingData T T_inv z)
    (hcov : ∀ z ∈ carrier,
      lyapunovStableComponent T T_inv (T z) ∘L fderiv ℝ T z =
          fderiv ℝ T z ∘L lyapunovStableComponent T T_inv z ∧
      lyapunovUnstableComponent T T_inv (T z) ∘L fderiv ℝ T z =
          fderiv ℝ T z ∘L lyapunovUnstableComponent T T_inv z)
    {Lip : ℝ} (hLip : 1 ≤ Lip)
    (hT_lipschitz : ∀ x ∈ K, ∀ y ∈ K,
      dist (T x) (T y) ≤ Lip * dist x y)
    (hderiv : ∀ x ∈ K, ‖fderiv ℝ T x‖ ≤ Lip)
    (hderiv_lipschitz : ∀ x ∈ S, ∀ y ∈ S,
      ‖fderiv ℝ T x - fderiv ℝ T y‖ ≤ Lip * dist x y)
    (P : Finset (Set EucPlane)) {delta : ℝ} (hdelta : 0 ≤ delta)
    (hP_diam : ∀ A ∈ P, Metric.ediam A ≤ ENNReal.ofReal delta)
    {lam1 lam2 eta qbad rho R : ℝ} {C H D L : ℕ}
    (hlam1 : 0 < lam1) (hlam2 : lam2 < 0)
    (heta : 0 ≤ eta) (hH : 0 < H)
    (hn : 0 < balancedForward lam1 lam2 L)
    (hR : 0 < R) (hrho : 1 ≤ rho)
    (hG : G = pesinFullShadowingBlock T T_inv lam1 lam2 eta C)
    (hab : lam2 + 6 * eta + (-lam1 + 6 * eta) < 0)
    (hAq : (4 * C : ℝ) / rho ≤ 1 / 4)
    (hcrossH : (4 * C : ℝ) * rho *
      Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) ≤ 1 / 4)
    (hunstableH : (C : ℝ) *
      Real.exp ((lam2 + 6 * eta + (-lam1 + 6 * eta)) * H) ≤ 1 / 2)
    (hshort_small : Lip ^ H * delta ≤ 1)
    (hshort_error :
      (H : ℝ) * (Lip * (Lip ^ H * delta)) * (2 * Lip) ^ (H + 1) ≤
        Real.exp ((lam2 + 6 * eta) * H))
    (hscaleR : 2 * R ≤ (4 : ℝ) ^ D)
    (hscaleLip : Lip ≤ (4 : ℝ) ^ D)
    (hscaleConst : 4 * R * Lip ^ 2 ≤ (4 : ℝ) ^ D)
    (hscaleRate :
      4 * Lip ^ 2 * Real.exp (-(lam2 + 6 * eta)) ≤ (4 : ℝ) ^ D)
    (hlog : Real.log rho ≤ eta * H)
    (hconstant :
      Lip ^ H * delta * 2 *
          Real.exp ((-lam2) * (H + 1) + lam1 * H + eta * H) ≤
        Real.exp (eta * L))
    {A : Set EucPlane}
    (hA : A ∈ centeredJoin T T_inv P
      (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L))
    (F : Finset EucPlane)
    (p : ↥(gridIndexSet H
      (balancedBackward lam1 lam2 L + balancedForward lam1 lam2 L)) → Bool)
    {B : Set EucPlane}
    (hB : B ∈ sparsePatternPieces T T_inv G
      (sparseWindowGoodSet T T_inv carrier G qbad
        (balancedBackward lam1 lam2 L) (balancedForward lam1 lam2 L) H)
      A F R (balancedBackward lam1 lam2 L)
        (balancedForward lam1 lam2 L) H D p) :
    Metric.ediam B ≤ ENNReal.ofReal
      (Real.exp (-(hyperbolicRate lam1 lam2 - 8 * eta) * L)) := by
  classical
  let m := balancedBackward lam1 lam2 L
  let n := balancedForward lam1 lam2 L
  have hmn : m + n = L :=
    balancedBackward_add_balancedForward hlam1 hlam2 L
  by_cases hbase : (sparsePatternBase T T_inv G
      (sparseWindowGoodSet T T_inv carrier G qbad m n H)
      A m n H p).Nonempty
  · rw [sparsePatternPieces, dif_pos hbase] at hB
    let c := sparsePatternReference T T_inv G
      (sparseWindowGoodSet T T_inv carrier G qbad m n H)
      A m n H p hbase
    have hcbase : c ∈ sparsePatternBase T T_inv G
        (sparseWindowGoodSet T T_inv carrier G qbad m n H)
        A m n H p :=
      sparsePatternReference_mem
        T T_inv G _ A m n H p hbase
    have hcgood :
        c ∈ sparseWindowGoodSet T T_inv carrier G qbad m n H :=
      hcbase.1.2
    have hpath : 0 < (sparseSelectedSet T T_inv G m n H c).card :=
      sparseSelectedSet_card_pos_of_mem_sparseWindowGoodSet
        T T_inv carrier G qbad hn hcgood
    have hzeroMem : 0 ∈ sparseSelectedSet T T_inv G m n H c :=
      zero_mem_sparseSelectedSet_of_mem_sparseWindowGoodSet
        T T_inv carrier G qbad hn hcgood
    have hcenterMem : m / H ∈ sparseSelectedSet T T_inv G m n H c :=
      center_mem_sparseSelectedSet_of_mem_sparseWindowGoodSet
        T T_inv carrier G qbad hn hcgood
    have hlastMem : (m + n - 1) / H ∈
        sparseSelectedSet T T_inv G m n H c :=
      last_mem_sparseSelectedSet_of_mem_sparseWindowGoodSet
        T T_inv carrier G qbad hn hcgood
    let ic : Fin (sparseSelectedSet T T_inv G m n H c).card :=
      selectedGridRank H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c) hcenterMem
    have hcenter :
        sparseNodeIndex T T_inv G m n H c ic = m / H :=
      selectedGridIndex_selectedGridRank H (m + n)
        (centeredOrbitGoodTime T T_inv G m n c) hcenterMem
    have hzero :
        sparseNodeIndex T T_inv G m n H c (cardPathZero hpath) = 0 :=
      selectedGridIndex_cardPathZero_eq_zero hpath hzeroMem
    have hlast :
        sparseNodeIndex T T_inv G m n H c (cardPathLast hpath) =
          (m + n - 1) / H :=
      selectedGridIndex_cardPathLast_eq_div_pred hH (by omega)
        hpath hlastMem
    obtain ⟨label, hlabel, rfl⟩ := Finset.mem_image.mp hB
    have hpathDiameter :=
      ediam_sparseEdgePiece_le_path_bound
        T T_inv hT_smooth hT_inv_smooth hT_left hT_right
        hK_inv hKS hS_convex hcarrier hcarrierK hsource hcov
        hLip hT_lipschitz hderiv hderiv_lipschitz
        P hdelta hP_diam hH hR (lt_of_lt_of_le zero_lt_one hrho)
        hG hab hAq hcrossH hunstableH hshort_small hshort_error
        hscaleR hscaleLip hscaleConst hscaleRate hA
        (fun y hy => hy.1.1)
        (fun y hy => hy.1.2.1.1.1.1)
        F c label hlabel hpath ic hcenter hzero hlast
        (fun y hy i =>
          sparsePatternBase_selected_orbit_mem
            T T_inv G _ A m n H p hcbase hy i)
    have hcard :
        (sparseSelectedSet T T_inv G m n H c).card ≤ L / H + 1 := by
      calc
        (sparseSelectedSet T T_inv G m n H c).card ≤
            (gridIndexSet H (m + n)).card := by
          apply Finset.card_le_card
          intro j hj
          have hj' := mem_selectedGridIndices_iff.mp hj
          exact mem_gridIndexSet_iff.mpr ⟨hj'.1, hj'.2.1⟩
        _ ≤ (m + n) / H + 1 := card_gridIndexSet_le_div_add_one hH
        _ = L / H + 1 := by rw [hmn]
    have htm : H * (m / H) ≤ m := Nat.mul_div_le m H
    have hmtH : m ≤ H * (m / H) + H := by
      have hmod := Nat.mod_lt m hH
      have hdecomp := Nat.mod_add_div m H
      omega
    have htL : H * (m / H) ≤ L := htm.trans (by omega)
    have hcenterLast :
        H * (m / H) ≤ H * ((m + n - 1) / H) := by
      apply Nat.mul_le_mul_left
      apply Nat.div_le_div_right
      omega
    have hlastApprox :
        L ≤ H * ((m + n - 1) / H) + H := by
      have hmod := Nat.mod_lt (m + n - 1) hH
      have hdecomp := Nat.mod_add_div (m + n - 1) H
      omega
    have hnGap :
        n ≤ H * ((m + n - 1) / H) - H * (m / H) + H := by
      omega
    have hgapL :
        H * ((m + n - 1) / H) - H * (m / H) ≤ L := by
      have hlastLe :
          H * ((m + n - 1) / H) ≤ L :=
        (Nat.mul_div_le (m + n - 1) H).trans (by omega)
      omega
    have hcenterLastL :
        H * (m / H) ≤ H * ((L - 1) / H) := by
      calc
        H * (m / H) ≤ H * ((m + n - 1) / H) := hcenterLast
        _ = H * ((L - 1) / H) := by rw [hmn]
    have hrateBound :=
      finite_sparse_path_rate_bound ic hlam1 hlam2 heta hLip hdelta hrho hlog
        hcard htm hmtH htL hnGap hgapL
        (hyperbolicRate_mul_sub_stable_le_backward_budget
          hlam1 hlam2 L)
        (hyperbolicRate_mul_le_forward_budget hlam1 hlam2 L)
        hconstant
    rw [hmn] at hrateBound
    rw [Nat.cast_sub hcenterLastL] at hrateBound
    exact hpathDiameter.trans
      (ENNReal.ofReal_le_ofReal (by
        simpa [m, n, hcenter, hmn, Nat.cast_mul] using hrateBound))
  · rw [sparsePatternPieces, dif_neg hbase] at hB
    simp at hB

end Submission.Helpers
