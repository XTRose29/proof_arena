import Submission.EarRemoval

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.CleanEar

/-!
Some fields of `EarRemoval.IsEarAtOne` are consequences of simpler
incidence data.  In particular, once the prospective diagonal meets the
old boundary only at its endpoints, the old polygon's simplicity forces
the ear triangle itself to be simple.
-/

/-- The diagonal used when removing vertex `1`. -/
def diagonal {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) : Set (ℝ × ℝ) :=
  segment ℝ (toPlane (v 0))
    (toPlane (v ⟨2, by omega⟩))

/-- The first vertex after `0` really is its cyclic successor. -/
theorem finRotate_zero {n : ℕ} (hn : 3 ≤ n) :
    finRotate (n + 1) (0 : Fin (n + 1)) =
      (⟨1, by omega⟩ : Fin (n + 1)) := by
  have hne :
      (0 : Fin (n + 1)) ≠ Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero, Fin.val_last] at hval
    omega
  apply Fin.ext
  rw [coe_finRotate_of_ne_last hne]
  rfl

/-- The vertex with index `2` really is the cyclic successor of index `1`. -/
theorem finRotate_one {n : ℕ} (hn : 3 ≤ n) :
    finRotate (n + 1)
        (⟨1, by omega⟩ : Fin (n + 1)) =
      (⟨2, by omega⟩ : Fin (n + 1)) := by
  have hne :
      (⟨1, by omega⟩ : Fin (n + 1)) ≠
        Fin.last n := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_last] at hval
    omega
  apply Fin.ext
  rw [coe_finRotate_of_ne_last hne]

/-- The same successor calculation at index `0` for the reduced index
type, whose cardinality is not syntactically presented as a successor. -/
theorem finRotate_reduced_zero
    {n : ℕ} (hn : 3 ≤ n) :
    finRotate n (⟨0, by omega⟩ : Fin n) =
      (⟨1, by omega⟩ : Fin n) := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hne :
      (⟨0, by omega⟩ : Fin (m + 1)) ≠ Fin.last m := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_last] at hval
    omega
  apply Fin.ext
  rw [coe_finRotate_of_ne_last hne]

/-- Vertex `2` is the right endpoint of old edge `1`. -/
theorem endpoint_two_mem_edge_one
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    toPlane (v ⟨2, by omega⟩) ∈
      (latPoly v).edgeSet ℝ
        (⟨1, by omega⟩ : Fin (n + 1)) := by
  change
    toPlane (v ⟨2, by omega⟩) ∈
      affineSegment ℝ
        (toPlane (v ⟨1, by omega⟩))
        (toPlane
          (v (finRotate (n + 1)
            (⟨1, by omega⟩ : Fin (n + 1)))))
  rw [finRotate_one hn]
  exact right_mem_affineSegment ℝ _ _

/-- Original vertex `0` cannot lie on old edge `1`. -/
theorem endpoint_zero_not_mem_edge_one
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    toPlane (v 0) ∉
      (latPoly v).edgeSet ℝ
        (⟨1, by omega⟩ : Fin (n + 1)) := by
  intro hmem
  have hp :
      (latPoly v) (0 : Fin (n + 1)) ∈
        (latPoly v).edgeSet ℝ 0 ∩
          (latPoly v).edgeSet ℝ
            (finRotate (n + 1) (0 : Fin (n + 1))) := by
    refine ⟨left_mem_affineSegment ℝ _ _, ?_⟩
    rw [finRotate_zero hn]
    exact hmem
  rw [hsimple.2.2 (0 : Fin (n + 1))] at hp
  exact
    hsimple.1 (0 : Fin (n + 1))
      (Set.mem_singleton_iff.mp hp)

/-- Original vertex `2` cannot lie on old edge `0`. -/
theorem endpoint_two_not_mem_edge_zero
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    toPlane (v ⟨2, by omega⟩) ∉
      (latPoly v).edgeSet ℝ 0 := by
  intro hmem
  have hp :
      (latPoly v) (⟨2, by omega⟩ : Fin (n + 1)) ∈
        (latPoly v).edgeSet ℝ 0 ∩
          (latPoly v).edgeSet ℝ
            (finRotate (n + 1) (0 : Fin (n + 1))) := by
    refine ⟨hmem, ?_⟩
    rw [finRotate_zero hn]
    exact endpoint_two_mem_edge_one hn v
  rw [hsimple.2.2 (0 : Fin (n + 1))] at hp
  have heq :
      (latPoly v) (⟨2, by omega⟩ : Fin (n + 1)) =
        (latPoly v) (⟨1, by omega⟩ : Fin (n + 1)) := by
    rw [finRotate_zero hn] at hp
    exact Set.mem_singleton_iff.mp hp
  apply hsimple.1 (⟨1, by omega⟩ : Fin (n + 1))
  rw [finRotate_one hn]
  exact heq.symm

/-- Among old edges with index at least `2`, only the last edge is
adjacent to old edge `0`. -/
theorem adjacent_zero_of_two_le
    {n : ℕ} (hn : 3 ≤ n)
    (j : Fin (n + 1)) (hj : 2 ≤ j.val)
    (hadj : Adjacent (0 : Fin (n + 1)) j) :
    j = Fin.last n := by
  rcases hadj with hforward | hbackward
  · rw [finRotate_zero hn] at hforward
    have hval := congrArg Fin.val hforward
    simp only at hval
    omega
  · have hsymm :=
      congrArg (finRotate (n + 1)).symm hbackward
    apply Fin.ext
    have hval := congrArg Fin.val hsymm
    simpa using hval

/-- Among old edges with index at least `2`, only edge `2` is adjacent to
old edge `1`. -/
theorem adjacent_one_of_two_le
    {n : ℕ} (hn : 3 ≤ n)
    (j : Fin (n + 1)) (hj : 2 ≤ j.val)
    (hadj :
      Adjacent (⟨1, by omega⟩ : Fin (n + 1)) j) :
    j = (⟨2, by omega⟩ : Fin (n + 1)) := by
  rcases hadj with hforward | hbackward
  · rw [finRotate_one hn] at hforward
    exact hforward.symm
  · have hjzero :
        j = (0 : Fin (n + 1)) := by
      apply (finRotate (n + 1)).injective
      rw [hbackward, finRotate_zero hn]
    have hval := congrArg Fin.val hjzero
    simp only [Fin.val_zero] at hval
    omega

/-- The three selected original vertices remain pairwise distinct after
embedding them as the ear triangle. -/
theorem earTriangle_vertex_injective
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    Function.Injective
      (latPoly (EarRemoval.earTriangle hn v)) := by
  intro i j hij
  let i' : Fin (n + 1) :=
    ⟨i.val, i.isLt.trans_le (hn.trans (Nat.le_succ n))⟩
  let j' : Fin (n + 1) :=
    ⟨j.val, j.isLt.trans_le (hn.trans (Nat.le_succ n))⟩
  have hvertices :
      (latPoly v) i' = (latPoly v) j' := by
    exact hij
  have hindices : i' = j' :=
    Helpers.vertex_injective_of_isSimple hsimple hvertices
  apply Fin.ext
  simpa [i', j'] using congrArg Fin.val hindices

/-- A clean diagonal forces the prospective ear triangle to be simple. -/
theorem triangleSimple_of_outerBoundaryInter
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (houter :
      (latPoly v).boundary (R := ℝ) ∩ diagonal hn v =
        {toPlane (v 0), toPlane (v ⟨2, by omega⟩)}) :
    IsSimple (latPoly (EarRemoval.earTriangle hn v)) := by
  let t := latPoly (EarRemoval.earTriangle hn v)
  have htInjective : Function.Injective t :=
    earTriangle_vertex_injective hn v hsimple
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact htInjective.ne
      (Triangle.finRotate_three_ne_self i).symm
  · intro i j hij hnotAdjacent
    fin_cases i <;> fin_cases j <;>
      simp [Adjacent] at hij hnotAdjacent
  · intro i
    rcases Triangle.fin_three_eq_zero_or_one_or_two i with
      rfl | rfl | rfl
    · change
        (latPoly (EarRemoval.earTriangle hn v)).edgeSet ℝ 0 ∩
            (latPoly (EarRemoval.earTriangle hn v)).edgeSet ℝ 1 =
          {toPlane (v ⟨1, by omega⟩)}
      rw [EarRemoval.ear_edge_zero hn v,
        EarRemoval.ear_edge_one hn v]
      have hinter :=
        hsimple.2.2 (0 : Fin (n + 1))
      rw [finRotate_zero hn] at hinter
      exact hinter
    · change
        (latPoly (EarRemoval.earTriangle hn v)).edgeSet ℝ 1 ∩
            (latPoly (EarRemoval.earTriangle hn v)).edgeSet ℝ 2 =
          {toPlane (v ⟨2, by omega⟩)}
      rw [EarRemoval.ear_edge_one hn v,
        EarRemoval.ear_edge_two hn v]
      apply Set.Subset.antisymm
      · intro p hp
        have hpouter :
            p ∈ (latPoly v).boundary (R := ℝ) ∩
              diagonal hn v := by
          refine
            ⟨Set.mem_iUnion.mpr
                ⟨(⟨1, by omega⟩ : Fin (n + 1)), hp.1⟩,
              hp.2⟩
        rw [houter] at hpouter
        rcases hpouter with hpzero | hptwo
        · exact
            (endpoint_zero_not_mem_edge_one hn v hsimple
              (hpzero ▸ hp.1)).elim
        · exact hptwo
      · intro p hp
        have hpeq :
            p = toPlane (v ⟨2, by omega⟩) :=
          Set.mem_singleton_iff.mp hp
        subst p
        exact
          ⟨endpoint_two_mem_edge_one hn v,
            right_mem_segment ℝ _ _⟩
    · change
        (latPoly (EarRemoval.earTriangle hn v)).edgeSet ℝ 2 ∩
            (latPoly (EarRemoval.earTriangle hn v)).edgeSet ℝ 0 =
          {toPlane (v 0)}
      rw [EarRemoval.ear_edge_two hn v,
        EarRemoval.ear_edge_zero hn v]
      apply Set.Subset.antisymm
      · intro p hp
        have hpouter :
            p ∈ (latPoly v).boundary (R := ℝ) ∩
              diagonal hn v := by
          refine
            ⟨Set.mem_iUnion.mpr
                ⟨(0 : Fin (n + 1)), hp.2⟩,
              hp.1⟩
        rw [houter] at hpouter
        rcases hpouter with hpzero | hptwo
        · exact hpzero
        · exact
            (endpoint_two_not_mem_edge_zero hn v hsimple
              (hptwo ▸ hp.2)).elim
      · intro p hp
        have hpeq : p = toPlane (v 0) :=
          Set.mem_singleton_iff.mp hp
        subst p
        exact
          ⟨left_mem_segment ℝ _ _,
            left_mem_affineSegment ℝ _ _⟩

/-- Original simplicity alone forces the two child boundaries to meet
exactly along their common diagonal. -/
theorem childBoundaryInter_of_isSimple
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    (latPoly (EarRemoval.earTriangle hn v)).boundary (R := ℝ) ∩
        (latPoly (EarRemoval.removeSecond v)).boundary (R := ℝ) =
      diagonal hn v := by
  apply Set.Subset.antisymm
  · intro p hp
    have htriangle := hp.1
    have hreduced := hp.2
    rw [Polygon.boundary] at htriangle hreduced
    rcases Set.mem_iUnion.mp htriangle with ⟨i, hi⟩
    rcases Set.mem_iUnion.mp hreduced with ⟨r, hr⟩
    by_cases hrzero : r.val = 0
    · have hrindex :
          r = (⟨0, by omega⟩ : Fin n) :=
        Fin.ext hrzero
      rw [hrindex, EarRemoval.reduced_edge_zero hn v] at hr
      exact hr
    · rw [EarRemoval.reduced_edge_of_ne_zero hn v r hrzero] at hr
      let j : Fin (n + 1) := EarRemoval.reducedIndex r
      change p ∈ (latPoly v).edgeSet ℝ j at hr
      have hjtwo : 2 ≤ j.val := by
        dsimp [j]
        rw [EarRemoval.reducedIndex_of_val_ne_zero r hrzero]
        simp only
        omega
      rcases Triangle.fin_three_eq_zero_or_one_or_two i with
        rfl | rfl | rfl
      · rw [EarRemoval.ear_edge_zero hn v] at hi
        by_cases hadj :
            Adjacent (0 : Fin (n + 1)) j
        · have hjlast :=
            adjacent_zero_of_two_le hn j hjtwo hadj
          rw [hjlast] at hr
          have hmem :
              p ∈
                (latPoly v).edgeSet ℝ (Fin.last n) ∩
                  (latPoly v).edgeSet ℝ
                    (finRotate (n + 1) (Fin.last n)) := by
            refine ⟨hr, ?_⟩
            simpa using hi
          rw [hsimple.2.2 (Fin.last n)] at hmem
          rw [finRotate_last] at hmem
          have hpzero :
              p = (latPoly v) (0 : Fin (n + 1)) := by
            exact Set.mem_singleton_iff.mp hmem
          rw [hpzero]
          exact left_mem_segment ℝ _ _
        · have hne :
              (0 : Fin (n + 1)) ≠ j := by
            intro h
            have hval := congrArg Fin.val h
            simp only [Fin.val_zero] at hval
            omega
          have hdisjoint :=
            hsimple.2.1 (0 : Fin (n + 1)) j
              hne hadj
          exact
            (Set.disjoint_left.mp hdisjoint hi hr).elim
      · rw [EarRemoval.ear_edge_one hn v] at hi
        by_cases hadj :
            Adjacent
              (⟨1, by omega⟩ : Fin (n + 1)) j
        · have hjtwoIndex :=
            adjacent_one_of_two_le hn j hjtwo hadj
          rw [hjtwoIndex] at hr
          have hmem :
              p ∈
                (latPoly v).edgeSet ℝ
                    (⟨1, by omega⟩ : Fin (n + 1)) ∩
                  (latPoly v).edgeSet ℝ
                    (finRotate (n + 1)
                      (⟨1, by omega⟩ : Fin (n + 1))) := by
            refine ⟨hi, ?_⟩
            rw [finRotate_one hn]
            exact hr
          rw [hsimple.2.2
            (⟨1, by omega⟩ : Fin (n + 1))] at hmem
          have hptwo :
              p =
                (latPoly v)
                  (⟨2, by omega⟩ : Fin (n + 1)) := by
            rw [finRotate_one hn] at hmem
            exact Set.mem_singleton_iff.mp hmem
          rw [hptwo]
          exact right_mem_segment ℝ _ _
        · have hne :
              (⟨1, by omega⟩ : Fin (n + 1)) ≠ j := by
            intro h
            have hval := congrArg Fin.val h
            simp only at hval
            omega
          have hdisjoint :=
            hsimple.2.1
              (⟨1, by omega⟩ : Fin (n + 1)) j
              hne hadj
          exact
            (Set.disjoint_left.mp hdisjoint hi hr).elim
      · rw [EarRemoval.ear_edge_two hn v] at hi
        exact hi
  · intro p hp
    constructor
    · rw [Polygon.boundary]
      refine Set.mem_iUnion.mpr ⟨(2 : Fin 3), ?_⟩
      rw [EarRemoval.ear_edge_two hn v]
      exact hp
    · rw [Polygon.boundary]
      refine
        Set.mem_iUnion.mpr
          ⟨(⟨0, by omega⟩ : Fin n), ?_⟩
      rw [EarRemoval.reduced_edge_zero hn v]
      exact hp

/-- The index embedding which skips original vertex `1` is injective. -/
theorem reducedIndex_injective
    {n : ℕ} (hn : 3 ≤ n) :
    Function.Injective (@EarRemoval.reducedIndex n) := by
  have hnpos : 0 < n :=
    lt_of_lt_of_le (by decide : 0 < 3) hn
  letI : NeZero n := ⟨hnpos.ne'⟩
  intro i j hij
  by_cases hi : i.val = 0
  · by_cases hj : j.val = 0
    · exact Fin.ext (hi.trans hj.symm)
    · have hiIndex :
          EarRemoval.reducedIndex i =
            (0 : Fin (n + 1)) := by
        simp [EarRemoval.reducedIndex, hi]
      rw [hiIndex,
        EarRemoval.reducedIndex_of_val_ne_zero j hj] at hij
      have hval := congrArg Fin.val hij
      simp only [Fin.val_zero] at hval
      omega
  · by_cases hj : j.val = 0
    · have hjIndex :
          EarRemoval.reducedIndex j =
            (0 : Fin (n + 1)) := by
        simp [EarRemoval.reducedIndex, hj]
      rw [EarRemoval.reducedIndex_of_val_ne_zero i hi,
        hjIndex] at hij
      have hval := congrArg Fin.val hij
      simp only [Fin.val_zero] at hval
      omega
    · rw [EarRemoval.reducedIndex_of_val_ne_zero i hi,
        EarRemoval.reducedIndex_of_val_ne_zero j hj] at hij
      apply Fin.ext
      have hval := congrArg Fin.val hij
      simp only at hval
      omega

/-- Adjacency of two embedded noninitial reduced edges reflects back to
adjacency in the reduced polygon. -/
theorem adjacent_of_reducedIndex_adjacent
    {n : ℕ} (hn : 3 ≤ n)
    (i j : Fin n) (hi : i.val ≠ 0)
    (hj : j.val ≠ 0)
    (hadj :
      Adjacent (EarRemoval.reducedIndex i)
        (EarRemoval.reducedIndex j)) :
    Adjacent i j := by
  rcases hadj with hforward | hbackward
  · left
    apply reducedIndex_injective hn
    rw [EarRemoval.reducedIndex_rotate_of_ne_zero hn i hi]
    exact hforward
  · right
    apply reducedIndex_injective hn
    rw [EarRemoval.reducedIndex_rotate_of_ne_zero hn j hj]
    exact hbackward

/-- Reduced nonadjacency to edge `0` excludes adjacency between the
corresponding old edge and old edge `0`. -/
theorem parentZero_not_adjacent_reducedIndex
    {n : ℕ} (hn : 3 ≤ n)
    (j : Fin n) (hj : j.val ≠ 0)
    (hnot :
      ¬ Adjacent (⟨0, by omega⟩ : Fin n) j) :
    ¬ Adjacent (0 : Fin (n + 1))
      (EarRemoval.reducedIndex j) := by
  letI : NeZero n := ⟨by omega⟩
  intro hadj
  have hjtwo :
      2 ≤ (EarRemoval.reducedIndex j).val := by
    rw [EarRemoval.reducedIndex_of_val_ne_zero j hj]
    simp only
    omega
  have hjlast :=
    adjacent_zero_of_two_le hn
      (EarRemoval.reducedIndex j) hjtwo hadj
  have hrotate :
      EarRemoval.reducedIndex (finRotate n j) =
        (0 : Fin (n + 1)) := by
    rw [EarRemoval.reducedIndex_rotate_of_ne_zero hn j hj,
      hjlast, finRotate_last]
  have hzero :
      EarRemoval.reducedIndex (0 : Fin n) =
        (0 : Fin (n + 1)) := by
    simp [EarRemoval.reducedIndex]
  have hback :
      finRotate n j = (0 : Fin n) := by
    apply reducedIndex_injective hn
    rw [hrotate, hzero]
  exact hnot (Or.inr hback)

/-- Reduced nonadjacency to edge `0` also excludes adjacency between the
corresponding old edge and old edge `1`. -/
theorem parentOne_not_adjacent_reducedIndex
    {n : ℕ} (hn : 3 ≤ n)
    (j : Fin n) (hj : j.val ≠ 0)
    (hnot :
      ¬ Adjacent (⟨0, by omega⟩ : Fin n) j) :
    ¬ Adjacent (⟨1, by omega⟩ : Fin (n + 1))
      (EarRemoval.reducedIndex j) := by
  letI : NeZero n := ⟨by omega⟩
  intro hadj
  have hjtwo :
      2 ≤ (EarRemoval.reducedIndex j).val := by
    rw [EarRemoval.reducedIndex_of_val_ne_zero j hj]
    simp only
    omega
  have hindex :=
    adjacent_one_of_two_le hn
      (EarRemoval.reducedIndex j) hjtwo hadj
  have hrotateZero :=
    EarRemoval.reducedIndex_rotate_zero hn
  have hzero :
      (0 : Fin n) =
        (⟨0, by omega⟩ : Fin n) :=
    Fin.ext (by simp)
  have hjnext :
      finRotate n (0 : Fin n) = j := by
    apply reducedIndex_injective hn
    rw [hzero, hrotateZero, hindex]
  exact hnot (Or.inl hjnext)

/-- Replacing edges `0` and `1` by a diagonal preserves simplicity whenever
that diagonal meets the old boundary only at its endpoints. -/
theorem reducedSimple_of_outerBoundaryInter
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (houter :
      (latPoly v).boundary (R := ℝ) ∩ diagonal hn v =
        {toPlane (v 0), toPlane (v ⟨2, by omega⟩)}) :
    IsSimple (latPoly (EarRemoval.removeSecond v)) := by
  letI : NeZero n := ⟨by omega⟩
  have hindexInjective := reducedIndex_injective hn
  have hdiagonalDisjoint :
      ∀ (j : Fin n), j.val ≠ 0 →
        ¬ Adjacent (0 : Fin n) j →
        Disjoint
          (diagonal hn v)
          ((latPoly v).edgeSet ℝ
            (EarRemoval.reducedIndex j)) := by
    intro j hj hnot
    rw [Set.disjoint_left]
    intro p hpDiagonal hpEdge
    have hpOuter :
        p ∈ (latPoly v).boundary (R := ℝ) ∩
          diagonal hn v := by
      exact
        ⟨Set.mem_iUnion.mpr
            ⟨EarRemoval.reducedIndex j, hpEdge⟩,
          hpDiagonal⟩
    rw [houter] at hpOuter
    rcases hpOuter with hpZero | hpTwo
    · have hne :
          (0 : Fin (n + 1)) ≠
            EarRemoval.reducedIndex j := by
        intro h
        rw [EarRemoval.reducedIndex_of_val_ne_zero j hj] at h
        have hval := congrArg Fin.val h
        simp only [Fin.val_zero] at hval
        omega
      have hdisjoint :=
        hsimple.2.1 (0 : Fin (n + 1))
          (EarRemoval.reducedIndex j) hne
          (parentZero_not_adjacent_reducedIndex hn j hj hnot)
      have hpInitial :
          toPlane (v 0) ∈
            (latPoly v).edgeSet ℝ
              (0 : Fin (n + 1)) := by
        change
          toPlane (v 0) ∈
            affineSegment ℝ (toPlane (v 0))
              (toPlane
                (v (finRotate (n + 1)
                  (0 : Fin (n + 1)))))
        exact left_mem_affineSegment ℝ _ _
      have hpMapped :
          toPlane (v 0) ∈
            (latPoly v).edgeSet ℝ
              (EarRemoval.reducedIndex j) := by
        exact hpZero ▸ hpEdge
      exact
        Set.disjoint_left.mp hdisjoint
          hpInitial hpMapped
    · have hne :
          (⟨1, by omega⟩ : Fin (n + 1)) ≠
            EarRemoval.reducedIndex j := by
        intro h
        rw [EarRemoval.reducedIndex_of_val_ne_zero j hj] at h
        have hval := congrArg Fin.val h
        simp only at hval
        omega
      have hdisjoint :=
        hsimple.2.1
          (⟨1, by omega⟩ : Fin (n + 1))
          (EarRemoval.reducedIndex j) hne
          (parentOne_not_adjacent_reducedIndex hn j hj hnot)
      exact
        Set.disjoint_left.mp hdisjoint
          (endpoint_two_mem_edge_one hn v)
          (hpTwo ▸ hpEdge)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val = 0
    · have hieq :
          i = (⟨0, by omega⟩ : Fin n) :=
        Fin.ext hi
      rw [hieq]
      change
        (latPoly v)
            (EarRemoval.reducedIndex
              (⟨0, by omega⟩ : Fin n)) ≠
          (latPoly v)
            (EarRemoval.reducedIndex
              (finRotate n
                (⟨0, by omega⟩ : Fin n)))
      rw [EarRemoval.reducedIndex_rotate_zero hn]
      have hzero :
          EarRemoval.reducedIndex
              (⟨0, by omega⟩ : Fin n) =
            (0 : Fin (n + 1)) := by
        simp [EarRemoval.reducedIndex]
      rw [hzero]
      exact
        (Helpers.vertex_injective_of_isSimple hsimple).ne
          (by
            intro h
            have hval := congrArg Fin.val h
            simp only [Fin.val_zero] at hval
            omega)
    · change
        (latPoly v) (EarRemoval.reducedIndex i) ≠
          (latPoly v)
            (EarRemoval.reducedIndex (finRotate n i))
      rw [EarRemoval.reducedIndex_rotate_of_ne_zero hn i hi]
      exact hsimple.1 (EarRemoval.reducedIndex i)
  · intro i j hij hnot
    by_cases hi : i.val = 0
    · have hieq :
          i = (⟨0, by omega⟩ : Fin n) :=
        Fin.ext hi
      rw [hieq] at hij hnot ⊢
      have hj : j.val ≠ 0 := by
        intro hj
        exact hij (Fin.ext hj.symm)
      rw [EarRemoval.reduced_edge_zero hn v,
        EarRemoval.reduced_edge_of_ne_zero hn v j hj]
      exact hdiagonalDisjoint j hj hnot
    · by_cases hj : j.val = 0
      · have hjeq :
            j = (⟨0, by omega⟩ : Fin n) :=
          Fin.ext hj
        rw [hjeq] at hij hnot ⊢
        have hnot' :
            ¬ Adjacent (0 : Fin n) i := by
          intro hadj
          apply hnot
          simpa [Adjacent, or_comm] using hadj
        rw [EarRemoval.reduced_edge_of_ne_zero hn v i hi,
          EarRemoval.reduced_edge_zero hn v]
        exact (hdiagonalDisjoint i hi hnot').symm
      · rw [EarRemoval.reduced_edge_of_ne_zero hn v i hi,
          EarRemoval.reduced_edge_of_ne_zero hn v j hj]
        apply hsimple.2.1
        · intro hindex
          exact hij (hindexInjective hindex)
        · intro hadj
          exact hnot
            (adjacent_of_reducedIndex_adjacent hn i j hi hj hadj)
  · intro i
    by_cases hi : i.val = 0
    · have hieq :
          i = (⟨0, by omega⟩ : Fin n) :=
        Fin.ext hi
      rw [hieq]
      have hrotateNe :
          (finRotate n
            (⟨0, by omega⟩ : Fin n)).val ≠ 0 := by
        rw [finRotate_reduced_zero hn]
        simp
      rw [EarRemoval.reduced_edge_zero hn v,
        EarRemoval.reduced_edge_of_ne_zero hn v
          (finRotate n
            (⟨0, by omega⟩ : Fin n)) hrotateNe,
        EarRemoval.reducedIndex_rotate_zero hn]
      have hvertex :
          (latPoly (EarRemoval.removeSecond v))
              (finRotate n
                (⟨0, by omega⟩ : Fin n)) =
            toPlane (v ⟨2, by omega⟩) := by
        change
          toPlane
              (v (EarRemoval.reducedIndex
                (finRotate n
                  (⟨0, by omega⟩ : Fin n)))) =
            toPlane (v ⟨2, by omega⟩)
        rw [EarRemoval.reducedIndex_rotate_zero hn]
      rw [hvertex]
      apply Set.Subset.antisymm
      · intro p hp
        have hpOuter :
            p ∈ (latPoly v).boundary (R := ℝ) ∩
              diagonal hn v := by
          exact
            ⟨Set.mem_iUnion.mpr
                ⟨(⟨2, by omega⟩ : Fin (n + 1)), hp.2⟩,
              hp.1⟩
        rw [houter] at hpOuter
        rcases hpOuter with hpZero | hpTwo
        · have hnotAdjacent :
              ¬ Adjacent (0 : Fin (n + 1))
                (⟨2, by omega⟩ : Fin (n + 1)) := by
            intro hadj
            have hlast :=
              adjacent_zero_of_two_le hn
                (⟨2, by omega⟩ : Fin (n + 1))
                (by simp) hadj
            have hval := congrArg Fin.val hlast
            simp only [Fin.val_last] at hval
            omega
          have hdisjoint :=
            hsimple.2.1 (0 : Fin (n + 1))
              (⟨2, by omega⟩ : Fin (n + 1))
              (by
                intro h
                have hval := congrArg Fin.val h
                simp only [Fin.val_zero] at hval
                omega)
              hnotAdjacent
          have hpAtZero :
              (latPoly v) (0 : Fin (n + 1)) ∈
                (latPoly v).edgeSet ℝ
                  (⟨2, by omega⟩ : Fin (n + 1)) := by
            change
              toPlane (v 0) ∈
                (latPoly v).edgeSet ℝ
                  (⟨2, by omega⟩ : Fin (n + 1))
            simpa [hpZero] using hp.2
          exact
            (Set.disjoint_left.mp hdisjoint
              (left_mem_affineSegment ℝ _ _)
              hpAtZero).elim
        · exact hpTwo
      · intro p hp
        have hpEq :
            p = toPlane (v ⟨2, by omega⟩) :=
          Set.mem_singleton_iff.mp hp
        subst p
        refine ⟨right_mem_segment ℝ _ _, ?_⟩
        change
          toPlane (v ⟨2, by omega⟩) ∈
            affineSegment ℝ
              (toPlane (v ⟨2, by omega⟩))
              (toPlane
                (v (finRotate (n + 1)
                  (⟨2, by omega⟩ : Fin (n + 1)))))
        exact left_mem_affineSegment ℝ _ _
    · rw [EarRemoval.reduced_edge_of_ne_zero hn v i hi]
      by_cases hrotate :
          (finRotate n i).val = 0
      · have hrotateEq :
            finRotate n i =
              (⟨0, by omega⟩ : Fin n) :=
          Fin.ext hrotate
        rw [hrotateEq, EarRemoval.reduced_edge_zero hn v]
        have hparentRotate :
            finRotate (n + 1)
                (EarRemoval.reducedIndex i) =
              (0 : Fin (n + 1)) := by
          rw [←
            EarRemoval.reducedIndex_rotate_of_ne_zero hn i hi,
            hrotateEq]
          simp [EarRemoval.reducedIndex]
        have hlast :
            EarRemoval.reducedIndex i = Fin.last n := by
          apply (finRotate (n + 1)).injective
          rw [hparentRotate, finRotate_last]
        rw [hlast]
        apply Set.Subset.antisymm
        · intro p hp
          have hpOuter :
              p ∈ (latPoly v).boundary (R := ℝ) ∩
                diagonal hn v := by
            exact
              ⟨Set.mem_iUnion.mpr
                  ⟨Fin.last n, hp.1⟩,
                hp.2⟩
          rw [houter] at hpOuter
          rcases hpOuter with hpZero | hpTwo
          · exact hpZero
          · have hnotAdjacent :
                ¬ Adjacent
                  (⟨1, by omega⟩ : Fin (n + 1))
                  (Fin.last n) := by
              intro hadj
              have hlastTwo :=
                adjacent_one_of_two_le hn (Fin.last n)
                  (by simp; omega) hadj
              have hval := congrArg Fin.val hlastTwo
              simp only [Fin.val_last] at hval
              omega
            have hdisjoint :=
              hsimple.2.1
                (⟨1, by omega⟩ : Fin (n + 1))
                (Fin.last n)
                (by
                  intro h
                  have hval := congrArg Fin.val h
                  simp only [Fin.val_last] at hval
                  omega)
                hnotAdjacent
            exact
              (Set.disjoint_left.mp hdisjoint
                (endpoint_two_mem_edge_one hn v)
                (hpTwo ▸ hp.1)).elim
        · intro p hp
          have hpEq :
              p = toPlane (v 0) :=
            Set.mem_singleton_iff.mp hp
          subst p
          refine ⟨?_, left_mem_segment ℝ _ _⟩
          change
            toPlane (v 0) ∈
              affineSegment ℝ
                (toPlane (v (Fin.last n)))
                (toPlane
                  (v (finRotate (n + 1) (Fin.last n))))
          rw [finRotate_last]
          exact right_mem_affineSegment ℝ _ _
      · rw [EarRemoval.reduced_edge_of_ne_zero hn v
          (finRotate n i) hrotate]
        change
          (latPoly v).edgeSet ℝ
                (EarRemoval.reducedIndex i) ∩
              (latPoly v).edgeSet ℝ
                (EarRemoval.reducedIndex (finRotate n i)) =
            {(latPoly v)
              (EarRemoval.reducedIndex (finRotate n i))}
        rw [EarRemoval.reducedIndex_rotate_of_ne_zero hn i hi]
        exact hsimple.2.2 (EarRemoval.reducedIndex i)

/-- The asserted interior partition already says that every point of the
open diagonal lies off the old boundary.  Adding the two boundary endpoints
recovers the exact outer-boundary intersection needed by ear removal. -/
theorem outerBoundaryInter_of_insidePartition
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (insidePartition :
      inside ((latPoly v).boundary (R := ℝ)) =
        (inside
            ((latPoly (EarRemoval.earTriangle hn v)).boundary
              (R := ℝ)) ∪
          inside
            ((latPoly (EarRemoval.removeSecond v)).boundary
              (R := ℝ))) ∪
          openSegment ℝ (toPlane (v 0))
            (toPlane (v ⟨2, by omega⟩))) :
    (latPoly v).boundary (R := ℝ) ∩ diagonal hn v =
      {toPlane (v 0), toPlane (v ⟨2, by omega⟩)} := by
  have hindices :
      (0 : Fin (n + 1)) ≠
        (⟨2, by omega⟩ : Fin (n + 1)) := by
    intro h
    have hval := congrArg Fin.val h
    simp only [Fin.val_zero] at hval
    omega
  have hvertices :
      v 0 ≠ v ⟨2, by omega⟩ :=
    (Helpers.lattice_vertex_injective_of_isSimple hsimple).ne
      hindices
  have hverticesPlane :
      toPlane (v 0) ≠
        toPlane (v ⟨2, by omega⟩) := by
    intro h
    exact hvertices
      (LatticeTriangle.toPlaneIntLinear_injective h)
  have hopenDisjoint :
      Disjoint
        ((latPoly v).boundary (R := ℝ))
        (openSegment ℝ (toPlane (v 0))
          (toPlane (v ⟨2, by omega⟩))) := by
    rw [Set.disjoint_left]
    intro p hpBoundary hpOpen
    have hpInside :
        p ∈ inside ((latPoly v).boundary (R := ℝ)) := by
      rw [insidePartition]
      exact Or.inr hpOpen
    exact hpInside.1 hpBoundary
  apply Set.Subset.antisymm
  · intro p hp
    by_cases hpEndpoints :
        p ∈
          ({toPlane (v 0),
            toPlane (v ⟨2, by omega⟩)} :
            Set (ℝ × ℝ))
    · exact hpEndpoints
    · have hpOpen :
          p ∈ openSegment ℝ (toPlane (v 0))
            (toPlane (v ⟨2, by omega⟩)) := by
        rw [Diagonal.openSegment_eq_segment_sdiff
          hverticesPlane]
        exact ⟨hp.2, hpEndpoints⟩
      exact
        (Set.disjoint_left.mp hopenDisjoint
          hp.1 hpOpen).elim
  · intro p hp
    simp only [Set.mem_insert_iff,
      Set.mem_singleton_iff] at hp
    rcases hp with hp | hp
    · rw [hp]
      refine ⟨?_, left_mem_segment ℝ _ _⟩
      rw [Polygon.boundary]
      exact
        Set.mem_iUnion.mpr
          ⟨(0 : Fin (n + 1)),
            left_mem_affineSegment ℝ _ _⟩
    · rw [hp]
      refine ⟨?_, right_mem_segment ℝ _ _⟩
      rw [Polygon.boundary]
      exact
        Set.mem_iUnion.mpr
          ⟨(⟨1, by omega⟩ : Fin (n + 1)),
            endpoint_two_mem_edge_one hn v⟩

/-- Once the two child boundaries meet along the diagonal, neither child
interior can contain a point of the open diagonal. -/
theorem seamDisjoint_of_childBoundaryInter
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hchild :
      (latPoly (EarRemoval.earTriangle hn v)).boundary (R := ℝ) ∩
          (latPoly (EarRemoval.removeSecond v)).boundary (R := ℝ) =
        diagonal hn v) :
    Disjoint
      (inside
          ((latPoly (EarRemoval.earTriangle hn v)).boundary
            (R := ℝ)) ∪
        inside
          ((latPoly (EarRemoval.removeSecond v)).boundary
            (R := ℝ)))
      (openSegment ℝ (toPlane (v 0))
        (toPlane (v ⟨2, by omega⟩))) := by
  rw [Set.disjoint_left]
  intro p hpinside hpseam
  have hpdiagonal : p ∈ diagonal hn v :=
    openSegment_subset_segment ℝ _ _ hpseam
  have hpchildren :
      p ∈
        (latPoly (EarRemoval.earTriangle hn v)).boundary (R := ℝ) ∩
          (latPoly (EarRemoval.removeSecond v)).boundary (R := ℝ) := by
    rw [hchild]
    exact hpdiagonal
  rcases hpinside with htriangle | hreduced
  · exact htriangle.1 hpchildren.1
  · exact hreduced.1 hpchildren.2

/-- Constructor for the full ear certificate in which triangle simplicity
and seam disjointness are discharged automatically from incidence data. -/
theorem isEarAtOneOfCore
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (insidePartition :
      inside ((latPoly v).boundary (R := ℝ)) =
        (inside
            ((latPoly (EarRemoval.earTriangle hn v)).boundary
              (R := ℝ)) ∪
          inside
            ((latPoly (EarRemoval.removeSecond v)).boundary
              (R := ℝ))) ∪
          openSegment ℝ (toPlane (v 0))
            (toPlane (v ⟨2, by omega⟩)))
    (interiorsDisjoint :
      Disjoint
        (inside
          ((latPoly (EarRemoval.earTriangle hn v)).boundary
            (R := ℝ)))
        (inside
          ((latPoly (EarRemoval.removeSecond v)).boundary
            (R := ℝ)))) :
    EarRemoval.IsEarAtOne hn v := by
  have outerBoundaryInter :=
    outerBoundaryInter_of_insidePartition hn v hsimple
      insidePartition
  exact
    { triangleSimple :=
        triangleSimple_of_outerBoundaryInter hn v hsimple
          outerBoundaryInter
      reducedSimple :=
        reducedSimple_of_outerBoundaryInter hn v hsimple
          outerBoundaryInter
      insidePartition := insidePartition
      interiorsDisjoint := interiorsDisjoint
      seamDisjoint :=
        seamDisjoint_of_childBoundaryInter hn v
          (childBoundaryInter_of_isSimple hn v hsimple)
      childBoundaryInter :=
        childBoundaryInter_of_isSimple hn v hsimple
      outerBoundaryInter := outerBoundaryInter }

/-- The genuinely independent data needed for an internal ear.  Simplicity
of both children and seam disjointness are reconstructed above. -/
structure CoreIsEarAtOne
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) : Prop where
  insidePartition :
    inside ((latPoly v).boundary (R := ℝ)) =
      (inside
          ((latPoly (EarRemoval.earTriangle hn v)).boundary
            (R := ℝ)) ∪
        inside
          ((latPoly (EarRemoval.removeSecond v)).boundary
            (R := ℝ))) ∪
        openSegment ℝ (toPlane (v 0))
          (toPlane (v ⟨2, by omega⟩))
  interiorsDisjoint :
    Disjoint
      (inside
        ((latPoly (EarRemoval.earTriangle hn v)).boundary
          (R := ℝ)))
      (inside
        ((latPoly (EarRemoval.removeSecond v)).boundary
          (R := ℝ)))

/-- Convert the reduced core data into the full certificate consumed by
ear removal. -/
theorem CoreIsEarAtOne.toIsEarAtOne
    {n : ℕ} {hn : 3 ≤ n}
    {v : Fin (n + 1) → ℤ × ℤ}
    (core : CoreIsEarAtOne hn v)
    (hsimple : IsSimple (latPoly v)) :
    EarRemoval.IsEarAtOne hn v :=
  isEarAtOneOfCore hn v hsimple core.insidePartition
    core.interiorsDisjoint

end Submission.CleanEar
