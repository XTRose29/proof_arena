import Submission.CenteredOrbitReindex
import Submission.PesinHyperbolicPrefixBlock
import Submission.SparseGrid
import Submission.SparseSecantControl

namespace Submission.Helpers

open LeanEval.Dynamics MeasureTheory

noncomputable def sparseCenteredBadCount
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n : ℕ) (x : EucPlane) : ℕ := by
  classical
  exact ∑ i : Fin (m + n),
    if centeredOrbit T T_inv m n x i ∈ G then 0 else 1

lemma sparseCenteredBadCount_eq
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (G : Set EucPlane) (m n : ℕ) (hn : 0 < n) (x : EucPlane) :
    (sparseCenteredBadCount T T_inv G m n x : ℝ) =
      badCount (fun k => T^[k] x ∈ G) 0 n +
        badCount (fun k => T_inv^[k] x ∈ G) 1 m := by
  classical
  have hforward (j : Fin n) :
      centeredOrbit T T_inv m n x (Fin.natAdd m j) = T^[j.val] x := by
    simp only [centeredOrbit]
    exact iterate_after_inverse_cancel hT_right m j.val x
  have hbackward (j : Fin m) :
    centeredOrbit T T_inv m n x (Fin.castAdd n j) =
        T_inv^[m - j.val] x := by
    have hcenter := centeredOrbit_center T T_inv hT_right
      (m := m) hn x
    have hmain := centeredOrbit_backward T T_inv hT_left x
      (⟨m, by omega⟩ : Fin (m + n)) (m - j.val) (by
        change m - j.val ≤ m
        exact Nat.sub_le m j.val)
    let k : Fin (m + n) := ⟨m - (m - j.val), by omega⟩
    have hk : Fin.castAdd n j = k := by
      apply Fin.ext
      dsimp [k]
      omega
    have hmain' :
        T_inv^[m - j.val]
            (centeredOrbit T T_inv m n x ⟨m, by omega⟩) =
          centeredOrbit T T_inv m n x k := by
      simpa [k] using hmain
    calc
      centeredOrbit T T_inv m n x (Fin.castAdd n j) =
          centeredOrbit T T_inv m n x k := congrArg _ hk
      _ = T_inv^[m - j.val]
          (centeredOrbit T T_inv m n x ⟨m, by omega⟩) := hmain'.symm
      _ = T_inv^[m - j.val] x := congrArg _ hcenter
  have hbackward_sum :
      (∑ j : Fin m,
          (if centeredOrbit T T_inv m n x (Fin.castAdd n j) ∈ G
            then 0 else 1 : ℕ)) =
        ∑ j : Fin m,
          (if T_inv^[1 + j.val] x ∈ G then 0 else 1 : ℕ) := by
    calc
      (∑ j : Fin m,
          (if centeredOrbit T T_inv m n x (Fin.castAdd n j) ∈ G
            then 0 else 1 : ℕ)) =
          ∑ j : Fin m,
            (if centeredOrbit T T_inv m n x
              (Fin.castAdd n (Fin.rev j)) ∈ G then 0 else 1 : ℕ) :=
        (Equiv.sum_comp Fin.revPerm _).symm
      _ = ∑ j : Fin m,
          (if T_inv^[1 + j.val] x ∈ G then 0 else 1 : ℕ) := by
        apply Fintype.sum_congr
        intro j
        rw [hbackward]
        congr 2
        congr 2
        simp only [Fin.val_rev]
        omega
  have hnat : sparseCenteredBadCount T T_inv G m n x =
      (∑ j : Fin m, (if T_inv^[1 + j.val] x ∈ G then 0 else 1 : ℕ)) +
        ∑ j : Fin n, (if T^[j.val] x ∈ G then 0 else 1 : ℕ) := by
    rw [sparseCenteredBadCount, Fin.sum_univ_add, hbackward_sum]
    congr 1
    apply Fintype.sum_congr
    intro j
    rw [hforward]
  rw [hnat, Nat.cast_add, Nat.cast_sum, Nat.cast_sum]
  simp only [Nat.cast_ite, Nat.cast_zero, Nat.cast_one]
  change
    (∑ j : Fin m, (if T_inv^[1 + j.val] x ∈ G then 0 else 1 : ℝ)) +
      (∑ j : Fin n, (if T^[j.val] x ∈ G then 0 else 1 : ℝ)) = _
  rw [Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if T_inv^[1 + j] x ∈ G then 0 else 1 : ℝ)) m,
    Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (if T^[j] x ∈ G then 0 else 1 : ℝ)) n]
  simp only [badCount, Nat.zero_add]
  rw [add_comm]

lemma sparseCenteredBadCount_le_of_twoSidedBadPrefixBlock
    (T T_inv : EucPlane → EucPlane)
    (hT_left : Function.LeftInverse T_inv T)
    (hT_right : Function.RightInverse T_inv T)
    (G : Set EucPlane) {q : ℝ} {m n : ℕ} (hn : 0 < n) {x : EucPlane}
    (hx : x ∈ maximalTwoSidedBadPrefixBlock T T_inv G q) :
    (sparseCenteredBadCount T T_inv G m n x : ℝ) ≤
      q * (m + n + 1) := by
  rw [sparseCenteredBadCount_eq T T_inv hT_left hT_right G m n hn x]
  have hpref := (mem_maximalTwoSidedBadPrefixBlock_iff
    T T_inv G q x).mp hx
  have hf := hpref.1 n
  have hb := hpref.2 (m + 1)
  have htail : badCount (fun k => T_inv^[k] x ∈ G) 1 m ≤
      badCount (fun k => T_inv^[k] x ∈ G) 0 (m + 1) := by
    simpa using badCount_tail_le (fun k => T_inv^[k] x ∈ G)
      0 (m := m + 1) (n := 1) (by omega)
  calc
    badCount (fun k => T^[k] x ∈ G) 0 n +
        badCount (fun k => T_inv^[k] x ∈ G) 1 m ≤
      q * n + q * (m + 1) := add_le_add hf (htail.trans (by
        simpa only [Nat.cast_add, Nat.cast_one] using hb))
    _ = q * (m + n + 1) := by
      ring

/-- All good/bad patterns on the coarse grid. -/
noncomputable def gridPatterns (H L : ℕ) :
    Finset (↥(gridIndexSet H L) → Bool) := by
  classical
  exact Fintype.piFinset fun _ => {false, true}

lemma card_gridPatterns (H L : ℕ) :
    (gridPatterns H L).card = 2 ^ (gridIndexSet H L).card := by
  classical
  rw [gridPatterns, Fintype.card_piFinset]
  simp

/-- The good/bad pattern of a centered orbit on the coarse grid. -/
noncomputable def centeredGridPattern
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (x : EucPlane) :
    ↥(gridIndexSet H (m + n)) → Bool := by
  classical
  exact fun j => decide (centeredOrbit T T_inv m n x
    ⟨H * j.1, (mem_gridIndexSet_iff.mp j.2).2⟩ ∈ G)

lemma centeredGridPattern_mem_gridPatterns
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (x : EucPlane) :
    centeredGridPattern T T_inv G m n H x ∈ gridPatterns H (m + n) := by
  classical
  simp [gridPatterns]

/-- Points realizing one prescribed good/bad pattern on the coarse centered
grid. -/
def centeredGridPatternFiber
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool) :
    Set EucPlane :=
  ⋂ j : ↥(gridIndexSet H (m + n)),
    if p j then
      (fun x => centeredOrbit T T_inv m n x
        ⟨H * j.1, (mem_gridIndexSet_iff.mp j.2).2⟩) ⁻¹' G
    else
      (fun x => centeredOrbit T T_inv m n x
        ⟨H * j.1, (mem_gridIndexSet_iff.mp j.2).2⟩) ⁻¹' Gᶜ

lemma measurable_centeredOrbit_eval
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    (m n : ℕ) (i : Fin (m + n)) :
    Measurable fun x => centeredOrbit T T_inv m n x i := by
  exact (hT.iterate i.val).measurable.comp
    ((hT_inv.iterate m).measurable)

lemma measurableSet_centeredGridPatternFiber
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    {G : Set EucPlane} (hG : MeasurableSet G)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool) :
    MeasurableSet (centeredGridPatternFiber T T_inv G m n H p) := by
  apply MeasurableSet.iInter
  intro j
  split_ifs
  · exact hG.preimage (measurable_centeredOrbit_eval T T_inv hT hT_inv _ _ _)
  · exact hG.compl.preimage
      (measurable_centeredOrbit_eval T T_inv hT hT_inv _ _ _)

lemma mem_centeredGridPatternFiber_iff
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool)
    (x : EucPlane) :
    x ∈ centeredGridPatternFiber T T_inv G m n H p ↔
      ∀ j : ↥(gridIndexSet H (m + n)),
        (p j = true ↔ centeredOrbit T T_inv m n x
          ⟨H * j.1, (mem_gridIndexSet_iff.mp j.2).2⟩ ∈ G) := by
  classical
  simp only [centeredGridPatternFiber, Set.mem_iInter]
  constructor
  · intro hx j
    have hj := hx j
    by_cases hp : p j = true
    · simp [hp] at hj ⊢
      exact hj
    · have hpfalse : p j = false := Bool.eq_false_of_not_eq_true hp
      simp [hpfalse] at hj ⊢
      exact hj
  · intro hx j
    have hj := hx j
    by_cases hp : p j = true
    · simpa [hp] using hj.mp hp
    · have hpfalse : p j = false := Bool.eq_false_of_not_eq_true hp
      simp [hpfalse]
      exact fun h => hp (hj.mpr h)

lemma mem_centeredGridPatternFiber_self
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (x : EucPlane) :
    x ∈ centeredGridPatternFiber T T_inv G m n H
      (centeredGridPattern T T_inv G m n H x) := by
  rw [mem_centeredGridPatternFiber_iff]
  intro j
  simp [centeredGridPattern]

/-- The total good predicate for a centered orbit; outside its finite time
window it is false. -/
def centeredOrbitGoodTime
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n : ℕ) (x : EucPlane) (t : ℕ) : Prop :=
  ∃ ht : t < m + n,
    centeredOrbit T T_inv m n x ⟨t, ht⟩ ∈ G

lemma centeredOrbitGoodTime_iff
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n : ℕ) (x : EucPlane) {t : ℕ} (ht : t < m + n) :
    centeredOrbitGoodTime T T_inv G m n x t ↔
      centeredOrbit T T_inv m n x ⟨t, ht⟩ ∈ G := by
  constructor
  · rintro ⟨ht', hx⟩
    simpa only [Fin.mk.injEq] using hx
  · intro hx
    exact ⟨ht, hx⟩

lemma finiteBadCountNat_centeredOrbitGoodTime
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n : ℕ) (x : EucPlane) :
    finiteBadCountNat (centeredOrbitGoodTime T T_inv G m n x) (m + n) =
      sparseCenteredBadCount T T_inv G m n x := by
  classical
  have hsparse : sparseCenteredBadCount T T_inv G m n x =
      ∑ i : Fin (m + n),
        if centeredOrbitGoodTime T T_inv G m n x i.val then 0 else 1 := by
    rw [sparseCenteredBadCount]
    apply Fintype.sum_congr
    intro i
    rw [centeredOrbitGoodTime_iff T T_inv G m n x i.isLt]
  rw [hsparse, Fin.sum_univ_eq_sum_range
    (fun t : ℕ => if centeredOrbitGoodTime T T_inv G m n x t then 0 else 1)
      (m + n)]
  unfold finiteBadCountNat
  rw [Finset.card_eq_sum_ones]
  simp only [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro t ht
  have ht' := Finset.mem_range.mp ht
  rw [centeredOrbitGoodTime_iff T T_inv G m n x ht']
  by_cases hgood : centeredOrbit T T_inv m n x ⟨t, ht'⟩ ∈ G <;>
    simp [hgood]

lemma same_centeredGridPattern_goodTime_iff
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool)
    {x y : EucPlane}
    (hx : x ∈ centeredGridPatternFiber T T_inv G m n H p)
    (hy : y ∈ centeredGridPatternFiber T T_inv G m n H p)
    {j : ℕ} (hj : j ∈ gridIndexSet H (m + n)) :
    centeredOrbitGoodTime T T_inv G m n x (H * j) ↔
      centeredOrbitGoodTime T T_inv G m n y (H * j) := by
  let jf : ↥(gridIndexSet H (m + n)) := ⟨j, hj⟩
  have htime := (mem_gridIndexSet_iff.mp hj).2
  rw [centeredOrbitGoodTime_iff T T_inv G m n x htime,
    centeredOrbitGoodTime_iff T T_inv G m n y htime]
  have hxp := (mem_centeredGridPatternFiber_iff
    T T_inv G m n H p x).mp hx jf
  have hyp := (mem_centeredGridPatternFiber_iff
    T T_inv G m n H p y).mp hy jf
  exact hxp.symm.trans hyp

def sparsePatternBase
    (T T_inv : EucPlane → EucPlane) (G goodSet A : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool) :
    Set EucPlane :=
  (A ∩ goodSet) ∩ centeredGridPatternFiber T T_inv G m n H p

lemma measurableSet_sparsePatternBase
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    {G goodSet A : Set EucPlane}
    (hG : MeasurableSet G) (hgood : MeasurableSet goodSet)
    (hA : MeasurableSet A) (m n H : ℕ)
    (p : ↥(gridIndexSet H (m + n)) → Bool) :
    MeasurableSet (sparsePatternBase T T_inv G goodSet A m n H p) :=
  (hA.inter hgood).inter
    (measurableSet_centeredGridPatternFiber
      T T_inv hT hT_inv hG m n H p)

noncomputable def sparsePatternReference
    (T T_inv : EucPlane → EucPlane) (G goodSet A : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool)
    (hbase : (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty) :
    EucPlane :=
  hbase.choose

lemma sparsePatternReference_mem
    (T T_inv : EucPlane → EucPlane) (G goodSet A : Set EucPlane)
    (m n H : ℕ) (p : ↥(gridIndexSet H (m + n)) → Bool)
    (hbase : (sparsePatternBase T T_inv G goodSet A m n H p).Nonempty) :
    sparsePatternReference T T_inv G goodSet A m n H p hbase ∈
      sparsePatternBase T T_inv G goodSet A m n H p :=
  hbase.choose_spec

noncomputable def sparseSelectedSet
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane) : Finset ℕ :=
  selectedGridIndices H (m + n)
    (centeredOrbitGoodTime T T_inv G m n c)

noncomputable def sparseNodeIndex
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (i : Fin (sparseSelectedSet T T_inv G m n H c).card) : ℕ :=
  selectedGridIndex H (m + n)
    (centeredOrbitGoodTime T T_inv G m n c) i

lemma sparseNodeIndex_lt
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (i : Fin (sparseSelectedSet T T_inv G m n H c).card) :
    H * sparseNodeIndex T T_inv G m n H c i < m + n := by
  exact selectedGridIndex_lt H (m + n)
    (centeredOrbitGoodTime T T_inv G m n c) i

lemma sparseNodeIndex_good
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (i : Fin (sparseSelectedSet T T_inv G m n H c).card) :
    centeredOrbitGoodTime T T_inv G m n c
      (H * sparseNodeIndex T T_inv G m n H c i) := by
  exact selectedGridIndex_good H (m + n)
    (centeredOrbitGoodTime T T_inv G m n c) i

noncomputable def sparseEdgeLeft
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
    Fin (sparseSelectedSet T T_inv G m n H c).card :=
  ⟨k.val, by omega⟩

noncomputable def sparseEdgeRight
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
    Fin (sparseSelectedSet T T_inv G m n H c).card :=
  ⟨k.val + 1, by omega⟩

noncomputable def sparseEdgeIndexGap
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) : ℕ :=
  sparseNodeIndex T T_inv G m n H c
      (sparseEdgeRight T T_inv G m n H c k) -
    sparseNodeIndex T T_inv G m n H c
      (sparseEdgeLeft T T_inv G m n H c k)

noncomputable def sparseEdgeTimeGap
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) : ℕ :=
  H * sparseEdgeIndexGap T T_inv G m n H c k

noncomputable def sparseEdgeDepth
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H D : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) : ℕ :=
  if 1 < sparseEdgeIndexGap T T_inv G m n H c k then
    D * (sparseEdgeTimeGap T T_inv G m n H c k + 1)
  else 0

noncomputable def sparseEdgeStart
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
    EucPlane :=
  centeredOrbit T T_inv m n c
    ⟨H * sparseNodeIndex T T_inv G m n H c
      (sparseEdgeLeft T T_inv G m n H c k),
      sparseNodeIndex_lt T T_inv G m n H c _⟩

noncomputable def sparseEdgeBalls
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ) (c : EucPlane)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
    Finset (Set EucPlane) :=
  scaledNetBalls F (sparseEdgeStart T T_inv G m n H c k) R
    (sparseEdgeDepth T T_inv G m n H D c k)

noncomputable def sparseEdgeLabels
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ) (c : EucPlane) :
    Finset
      ((k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) →
        Set EucPlane) :=
  Fintype.piFinset fun k => sparseEdgeBalls T T_inv G F R m n H D c k

def sparseEdgePiece
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane) (base : Set EucPlane)
    (label : (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) →
      Set EucPlane) : Set EucPlane :=
  base ∩ ⋂ k,
    (fun z => centeredOrbit T T_inv m n z
      ⟨H * sparseNodeIndex T T_inv G m n H c
        (sparseEdgeLeft T T_inv G m n H c k),
        sparseNodeIndex_lt T T_inv G m n H c _⟩) ⁻¹' label k

noncomputable def sparseEdgePieces
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ) (c : EucPlane)
    (base : Set EucPlane) : Finset (Set EucPlane) :=
  (sparseEdgeLabels T T_inv G F R m n H D c).image fun label =>
    sparseEdgePiece T T_inv G m n H c base label

lemma measurableSet_sparseEdgePiece
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    (G : Set EucPlane) (m n H : ℕ) (c : EucPlane)
    {base : Set EucPlane} (hbase : MeasurableSet base)
    (label : (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) →
      Set EucPlane)
    (hlabel : ∀ k, MeasurableSet (label k)) :
    MeasurableSet (sparseEdgePiece T T_inv G m n H c base label) := by
  apply hbase.inter
  apply MeasurableSet.iInter
  intro k
  exact (hlabel k).preimage
    (measurable_centeredOrbit_eval T T_inv hT hT_inv _ _ _)

lemma measurableSet_of_mem_sparseEdgePieces
    (T T_inv : EucPlane → EucPlane)
    (hT : Continuous T) (hT_inv : Continuous T_inv)
    (G : Set EucPlane) (F : Finset EucPlane) (R : ℝ)
    (m n H D : ℕ) (c : EucPlane)
    {base : Set EucPlane} (hbase : MeasurableSet base)
    {B : Set EucPlane}
    (hB : B ∈ sparseEdgePieces T T_inv G F R m n H D c base) :
    MeasurableSet B := by
  obtain ⟨label, hlabel, rfl⟩ := Finset.mem_image.mp hB
  apply measurableSet_sparseEdgePiece T T_inv hT hT_inv G m n H c hbase label
  intro k
  exact measurableSet_of_mem_scaledNetBalls
    (Fintype.mem_piFinset.mp hlabel k)

lemma card_sparseEdgePieces_le
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane) (R : ℝ) (m n H D : ℕ) (c : EucPlane)
    (base : Set EucPlane) :
    (sparseEdgePieces T T_inv G F R m n H D c base).card ≤
      F.card ^
        ∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
          sparseEdgeDepth T T_inv G m n H D c k := by
  classical
  calc
    (sparseEdgePieces T T_inv G F R m n H D c base).card ≤
        (sparseEdgeLabels T T_inv G F R m n H D c).card :=
      Finset.card_image_le
    _ = ∏ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
        (sparseEdgeBalls T T_inv G F R m n H D c k).card := by
      rw [sparseEdgeLabels, Fintype.card_piFinset]
    _ ≤ ∏ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
        F.card ^ sparseEdgeDepth T T_inv G m n H D c k := by
      apply Finset.prod_le_prod'
      intro k _hk
      exact card_scaledNetBalls_le _ _ _ _
    _ = F.card ^
        ∑ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
          sparseEdgeDepth T T_inv G m n H D c k := by
      exact Finset.prod_pow_eq_pow_sum _ _ _

lemma sparseEdgePieces_cover
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (F : Finset EucPlane)
    (hF : ∀ u : EucPlane, ‖u‖ ≤ 1 → ∃ f ∈ F, dist u f < 1 / 4)
    {R : ℝ} (hR : 0 < R) (m n H D : ℕ) (c : EucPlane)
    (base : Set EucPlane)
    (hbaseR : ∀ y ∈ base,
      ∀ k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1),
        dist
          (centeredOrbit T T_inv m n y
            ⟨H * sparseNodeIndex T T_inv G m n H c
              (sparseEdgeLeft T T_inv G m n H c k),
              sparseNodeIndex_lt T T_inv G m n H c _⟩)
          (sparseEdgeStart T T_inv G m n H c k) ≤ R) :
    base ⊆ ⋃ B ∈ sparseEdgePieces T T_inv G F R m n H D c base, B := by
  classical
  intro y hy
  have hchoice : ∀ k : Fin
      ((sparseSelectedSet T T_inv G m n H c).card - 1),
      ∃ B ∈ sparseEdgeBalls T T_inv G F R m n H D c k,
        centeredOrbit T T_inv m n y
          ⟨H * sparseNodeIndex T T_inv G m n H c
            (sparseEdgeLeft T T_inv G m n H c k),
            sparseNodeIndex_lt T T_inv G m n H c _⟩ ∈ B := by
    intro k
    have hyball : centeredOrbit T T_inv m n y
        ⟨H * sparseNodeIndex T T_inv G m n H c
          (sparseEdgeLeft T T_inv G m n H c k),
          sparseNodeIndex_lt T T_inv G m n H c _⟩ ∈
        Metric.closedBall (sparseEdgeStart T T_inv G m n H c k) R :=
      Metric.mem_closedBall.mpr (hbaseR y hy k)
    have hcover := scaledNetBalls_cover_closedBall F hF
      (sparseEdgeStart T T_inv G m n H c k) hR
      (sparseEdgeDepth T T_inv G m n H D c k) hyball
    simp only [Set.mem_iUnion] at hcover
    obtain ⟨B, hB, hyB⟩ := hcover
    exact ⟨B, hB, hyB⟩
  let label : (k : Fin
      ((sparseSelectedSet T T_inv G m n H c).card - 1)) →
      Set EucPlane := fun k => (hchoice k).choose
  have hlabel : label ∈ sparseEdgeLabels T T_inv G F R m n H D c := by
    apply Fintype.mem_piFinset.mpr
    intro k
    exact (hchoice k).choose_spec.1
  have hypiece :
      y ∈ sparseEdgePiece T T_inv G m n H c base label := by
    refine ⟨hy, Set.mem_iInter.mpr fun k => ?_⟩
    exact (hchoice k).choose_spec.2
  have hpiece : sparseEdgePiece T T_inv G m n H c base label ∈
      sparseEdgePieces T T_inv G F R m n H D c base :=
    Finset.mem_image.mpr ⟨label, hlabel, rfl⟩
  exact Set.mem_iUnion_of_mem _ (Set.mem_iUnion_of_mem hpiece hypiece)

lemma mem_sparseEdgePiece_base
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane) (base : Set EucPlane)
    (label : (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) →
      Set EucPlane) {y : EucPlane}
    (hy : y ∈ sparseEdgePiece T T_inv G m n H c base label) :
    y ∈ base :=
  hy.1

lemma mem_sparseEdgePiece_label
    (T T_inv : EucPlane → EucPlane) (G : Set EucPlane)
    (m n H : ℕ) (c : EucPlane) (base : Set EucPlane)
    (label : (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) →
      Set EucPlane) {y : EucPlane}
    (hy : y ∈ sparseEdgePiece T T_inv G m n H c base label)
    (k : Fin ((sparseSelectedSet T T_inv G m n H c).card - 1)) :
    centeredOrbit T T_inv m n y
      ⟨H * sparseNodeIndex T T_inv G m n H c
        (sparseEdgeLeft T T_inv G m n H c k),
        sparseNodeIndex_lt T T_inv G m n H c _⟩ ∈ label k :=
  Set.mem_iInter.mp hy.2 k

end Submission.Helpers
