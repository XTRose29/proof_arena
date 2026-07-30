import Submission.VisibleDiagonal

open LeanEval.Geometry.PicksTheorem

namespace Submission.FrontSubpolygon

/-- Embed the consecutive index interval `1, ..., q` into the original
cyclic index set. -/
def frontIndex
    {n : ℕ} (q : Fin (n + 1))
    (i : Fin q.val) :
    Fin (n + 1) :=
  ⟨i.val + 1, by omega⟩

@[simp]
theorem frontIndex_val
    {n : ℕ} (q : Fin (n + 1))
    (i : Fin q.val) :
    (frontIndex q i).val = i.val + 1 :=
  rfl

/-- The consecutive interval embedding is injective. -/
theorem frontIndex_injective
    {n : ℕ} (q : Fin (n + 1)) :
    Function.Injective (frontIndex q) := by
  intro i j h
  apply Fin.ext
  have hval := congrArg Fin.val h
  simp only [frontIndex_val] at hval
  omega

/-- The front subpolygon starts at original vertex `1`. -/
theorem frontIndex_zero
    {n : ℕ} (q : Fin (n + 1))
    (hq : 0 < q.val) :
    frontIndex q (⟨0, hq⟩ : Fin q.val) =
      (⟨1, by omega⟩ : Fin (n + 1)) := by
  apply Fin.ext
  rfl

/-- Its last index maps to original vertex `q`. -/
theorem frontIndex_last
    {n : ℕ} (q : Fin (n + 1))
    (hq : 0 < q.val) :
    frontIndex q
        (⟨q.val - 1, by omega⟩ : Fin q.val) =
      q := by
  apply Fin.ext
  simp [frontIndex]
  omega

/-- Cyclic rotation sends the last front index back to its first index. -/
theorem finRotate_frontLast
    {n : ℕ} (q : Fin (n + 1))
    (hq : 0 < q.val) :
    finRotate q.val
        (⟨q.val - 1, by omega⟩ : Fin q.val) =
      (⟨0, hq⟩ : Fin q.val) := by
  rw [finRotate_apply]
  apply Fin.ext
  simp [Fin.add_def]
  have hqeq : q.val - 1 + 1 = q.val := by
    omega
  rw [hqeq, Nat.mod_self]

/-- Away from the closing edge, cyclic successors commute with the interval
embedding. -/
theorem frontIndex_rotate_of_lt
    {n : ℕ} (q : Fin (n + 1))
    (i : Fin q.val)
    (hi : i.val + 1 < q.val) :
    frontIndex q (finRotate q.val i) =
      finRotate (n + 1) (frontIndex q i) := by
  rw [finRotate_apply, finRotate_apply]
  apply Fin.ext
  simp [frontIndex, Fin.add_def,
    Nat.mod_eq_of_lt hi]
  have hparent :
      i.val + 2 < n + 1 := by
    omega
  rw [Nat.mod_eq_of_lt hparent]

/-- Numerical form of the preceding successor correspondence. -/
theorem finRotate_val_of_lt
    {n : ℕ} (q : Fin (n + 1))
    (i : Fin q.val)
    (hi : i.val + 1 < q.val) :
    (finRotate q.val i).val = i.val + 1 := by
  rw [finRotate_apply]
  simp [Fin.add_def, Nat.mod_eq_of_lt hi]

/-- The consecutive front subpolygon cut off by the chord from `q` back to
vertex `1`. -/
def vertices
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1)) :
    Fin q.val → ℤ × ℤ :=
  fun i => v (frontIndex q i)

@[simp]
theorem vertices_apply
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (i : Fin q.val) :
    vertices v q i = v (frontIndex q i) :=
  rfl

/-- Every nonclosing edge of the front subpolygon is the corresponding
original polygon edge. -/
theorem edge_of_lt
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (i : Fin q.val)
    (hi : i.val + 1 < q.val) :
    (latPoly (vertices v q)).edgeSet ℝ i =
      (latPoly v).edgeSet ℝ (frontIndex q i) := by
  change
    affineSegment ℝ
        (toPlane (v (frontIndex q i)))
        (toPlane
          (v (frontIndex q (finRotate q.val i)))) =
      affineSegment ℝ
        (toPlane (v (frontIndex q i)))
        (toPlane
          (v
            (finRotate (n + 1)
              (frontIndex q i))))
  rw [frontIndex_rotate_of_lt q i hi]

/-- The first front-subpolygon edge is original edge `1`. -/
theorem edge_zero
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    (latPoly (vertices v q)).edgeSet ℝ
        (⟨0, by omega⟩ : Fin q.val) =
      (latPoly v).edgeSet ℝ
        (⟨1, by omega⟩ : Fin (n + 1)) := by
  let zero : Fin q.val :=
    ⟨0, by omega⟩
  have hzeroLt : zero.val + 1 < q.val := by
    dsimp [zero]
    omega
  calc
    (latPoly (vertices v q)).edgeSet ℝ
          (⟨0, by omega⟩ : Fin q.val) =
        (latPoly v).edgeSet ℝ
          (frontIndex q
            zero) := by
      simpa [zero] using
        edge_of_lt v q zero hzeroLt
    _ =
        (latPoly v).edgeSet ℝ
          (⟨1, by omega⟩ : Fin (n + 1)) := by
      rw [frontIndex_zero q (by omega)]

/-- The final front-subpolygon edge is precisely the clean chord, with
orientation from `q` back to vertex `1`. -/
theorem edge_last
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 0 < q.val) :
    (latPoly (vertices v q)).edgeSet ℝ
        (⟨q.val - 1, by omega⟩ : Fin q.val) =
      segment ℝ
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))))
        (toPlane (v q)) := by
  let last : Fin q.val :=
    ⟨q.val - 1, by omega⟩
  have hlastIndex :
      frontIndex q last = q := by
    simpa [last] using frontIndex_last q hq
  have hrotateLast :
      finRotate q.val last =
        (⟨0, hq⟩ : Fin q.val) := by
    simpa [last] using finRotate_frontLast q hq
  have hzeroIndex :
      frontIndex q (⟨0, hq⟩ : Fin q.val) =
        (⟨1, by omega⟩ : Fin (n + 1)) :=
    frontIndex_zero q hq
  change
    affineSegment ℝ
        (toPlane (v (frontIndex q last)))
        (toPlane
          (v
            (frontIndex q
              (finRotate q.val last)))) =
      segment ℝ
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))))
        (toPlane (v q))
  rw [hlastIndex, hrotateLast, hzeroIndex,
    affineSegment_eq_segment, segment_symm]

/-- The clean closing chord is disjoint from every inherited edge that is
not adjacent to it in the front subpolygon. -/
theorem diagonal_disjoint_inherited_edge
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val)
    (hclean :
      (latPoly v).boundary (R := ℝ) ∩
          segment ℝ
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))
            (toPlane (v q)) =
        {toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))),
          toPlane (v q)})
    (j : Fin q.val)
    (hj : j.val + 1 < q.val)
    (hjlast :
      j ≠
        (⟨q.val - 1, by omega⟩ :
          Fin q.val))
    (hnotAdjacent :
      ¬ Adjacent
        (⟨q.val - 1, by omega⟩ :
          Fin q.val)
        j) :
    Disjoint
      (segment ℝ
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))))
        (toPlane (v q)))
      ((latPoly v).edgeSet ℝ (frontIndex q j)) := by
  let last : Fin q.val :=
    ⟨q.val - 1, by omega⟩
  let zero : Fin q.val :=
    ⟨0, by omega⟩
  let oneParent : Fin (n + 1) :=
    ⟨1, by omega⟩
  have hlastIndex :
      frontIndex q last = q := by
    simpa [last] using
      frontIndex_last q (by omega)
  have hzeroIndex :
      frontIndex q zero = oneParent := by
    simpa [zero, oneParent] using
      frontIndex_zero q (by omega)
  have hrotateLast :
      finRotate q.val last = zero := by
    simpa [last, zero] using
      finRotate_frontLast q (by omega)
  have hpNotEdge :
      toPlane (v oneParent) ∉
        (latPoly v).edgeSet ℝ (frontIndex q j) := by
    intro hp
    have hcases :=
      (PolygonIncidence.vertex_mem_edgeSet_iff
        (latPoly v) hsimple oneParent
          (frontIndex q j)).mp hp
    rcases hcases with hone | hone
    · have hfront :
          frontIndex q zero = frontIndex q j := by
        rw [hzeroIndex, hone]
      have hjzero :
          j = zero :=
        frontIndex_injective q hfront.symm
      apply hnotAdjacent
      exact Or.inl <| by
        rw [hrotateLast, hjzero]
    · have hrotateIndex :
          frontIndex q (finRotate q.val j) =
            finRotate (n + 1) (frontIndex q j) :=
        frontIndex_rotate_of_lt q j hj
      have hfront :
          frontIndex q zero =
            frontIndex q (finRotate q.val j) := by
        rw [hzeroIndex, hrotateIndex, hone]
      have hrotateZero :
          finRotate q.val j = zero :=
        frontIndex_injective q hfront.symm
      have hjlast' : j = last := by
        apply (finRotate q.val).injective
        rw [hrotateZero, hrotateLast]
      exact hjlast hjlast'
  have hqNotEdge :
      toPlane (v q) ∉
        (latPoly v).edgeSet ℝ (frontIndex q j) := by
    intro hqmem
    have hcases :=
      (PolygonIncidence.vertex_mem_edgeSet_iff
        (latPoly v) hsimple q
          (frontIndex q j)).mp hqmem
    rcases hcases with hqeq | hqeq
    · have hfront :
          frontIndex q last = frontIndex q j := by
        exact hlastIndex.trans hqeq
      exact hjlast <|
        frontIndex_injective q hfront.symm
    · have hrotateIndex :
          frontIndex q (finRotate q.val j) =
            finRotate (n + 1) (frontIndex q j) :=
        frontIndex_rotate_of_lt q j hj
      have hfront :
          frontIndex q last =
            frontIndex q (finRotate q.val j) := by
        exact
          hlastIndex.trans
            (hqeq.trans hrotateIndex.symm)
      have hrotateEq :
          finRotate q.val j = last :=
        frontIndex_injective q hfront.symm
      apply hnotAdjacent
      exact Or.inr hrotateEq
  rw [Set.disjoint_left]
  intro x hxDiagonal hxEdge
  have hxBoundary :
      x ∈ (latPoly v).boundary (R := ℝ) := by
    rw [Polygon.boundary]
    exact
      Set.mem_iUnion.mpr
        ⟨frontIndex q j, hxEdge⟩
  have hxBoth :
      x ∈
        (latPoly v).boundary (R := ℝ) ∩
          segment ℝ
            (toPlane (v oneParent))
            (toPlane (v q)) :=
    ⟨hxBoundary, by simpa [oneParent] using hxDiagonal⟩
  rw [hclean] at hxBoth
  rcases hxBoth with hp | hqeq
  · exact hpNotEdge <|
      by simpa [oneParent] using hp ▸ hxEdge
  · exact hqNotEdge (hqeq ▸ hxEdge)

/-- The inherited edge immediately preceding `q` meets the closing chord
only at `q`. -/
theorem predecessor_edge_inter_diagonal
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val)
    (hclean :
      (latPoly v).boundary (R := ℝ) ∩
          segment ℝ
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))
            (toPlane (v q)) =
        {toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))),
          toPlane (v q)}) :
    (latPoly v).edgeSet ℝ
          (frontIndex q
            (⟨q.val - 2, by omega⟩ :
              Fin q.val)) ∩
        segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v q)) =
      {toPlane (v q)} := by
  let pred : Fin q.val :=
    ⟨q.val - 2, by omega⟩
  let last : Fin q.val :=
    ⟨q.val - 1, by omega⟩
  let oneParent : Fin (n + 1) :=
    ⟨1, by omega⟩
  have hpredLt : pred.val + 1 < q.val := by
    dsimp [pred]
    omega
  have hrotatePred :
      finRotate q.val pred = last := by
    apply Fin.ext
    rw [finRotate_val_of_lt q pred hpredLt]
    dsimp [pred, last]
    omega
  have hlastIndex :
      frontIndex q last = q := by
    simpa [last] using
      frontIndex_last q (by omega)
  have hpNotEdge :
      toPlane (v oneParent) ∉
        (latPoly v).edgeSet ℝ (frontIndex q pred) := by
    intro hp
    have hcases :=
      (PolygonIncidence.vertex_mem_edgeSet_iff
        (latPoly v) hsimple oneParent
          (frontIndex q pred)).mp hp
    rcases hcases with hone | hone
    · have hval := congrArg Fin.val hone
      simp [oneParent, pred, frontIndex] at hval
      omega
    · rw [← frontIndex_rotate_of_lt q pred hpredLt,
        hrotatePred, hlastIndex] at hone
      have hval := congrArg Fin.val hone
      simp [oneParent] at hval
      omega
  apply Set.Subset.antisymm
  · intro x hx
    have hxBoundary :
        x ∈ (latPoly v).boundary (R := ℝ) := by
      rw [Polygon.boundary]
      exact
        Set.mem_iUnion.mpr
          ⟨frontIndex q pred, hx.1⟩
    have hxBoth :
        x ∈
          (latPoly v).boundary (R := ℝ) ∩
            segment ℝ
              (toPlane (v oneParent))
              (toPlane (v q)) :=
      ⟨hxBoundary, by simpa [oneParent] using hx.2⟩
    rw [hclean] at hxBoth
    rcases hxBoth with hp | hqeq
    · exact False.elim <|
        hpNotEdge <|
          by simpa [oneParent] using hp ▸ hx.1
    · simpa using hqeq
  · intro x hx
    have hxq : x = toPlane (v q) := by
      simpa using hx
    subst x
    constructor
    · change
        toPlane (v q) ∈
          affineSegment ℝ
            (toPlane (v (frontIndex q pred)))
            (toPlane
              (v
                (finRotate (n + 1)
                  (frontIndex q pred))))
      rw [← frontIndex_rotate_of_lt q pred hpredLt,
        hrotatePred, hlastIndex]
      exact right_mem_affineSegment ℝ _ _
    · exact right_mem_segment ℝ _ _

/-- The closing chord meets the first inherited edge only at original
vertex `1`. -/
theorem diagonal_inter_first_edge
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val)
    (hclean :
      (latPoly v).boundary (R := ℝ) ∩
          segment ℝ
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))
            (toPlane (v q)) =
        {toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))),
          toPlane (v q)}) :
    segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v q)) ∩
        (latPoly v).edgeSet ℝ
          (⟨1, by omega⟩ : Fin (n + 1)) =
      {toPlane
        (v
          (⟨1, by omega⟩ :
            Fin (n + 1)))} := by
  let oneParent : Fin (n + 1) :=
    ⟨1, by omega⟩
  have hn : 3 ≤ n := by
    omega
  have hrotateOne :
      finRotate (n + 1) oneParent =
        (⟨2, by omega⟩ : Fin (n + 1)) := by
    simpa [oneParent] using CleanEar.finRotate_one hn
  have hqNotEdge :
      toPlane (v q) ∉
        (latPoly v).edgeSet ℝ oneParent := by
    intro hqmem
    have hcases :=
      (PolygonIncidence.vertex_mem_edgeSet_iff
        (latPoly v) hsimple q oneParent).mp hqmem
    rcases hcases with hqone | hqtwo
    · have hval := congrArg Fin.val hqone
      simp [oneParent] at hval
      omega
    · rw [hrotateOne] at hqtwo
      have hval := congrArg Fin.val hqtwo
      simp only at hval
      omega
  apply Set.Subset.antisymm
  · intro x hx
    have hxBoundary :
        x ∈ (latPoly v).boundary (R := ℝ) := by
      rw [Polygon.boundary]
      exact Set.mem_iUnion.mpr ⟨oneParent, hx.2⟩
    have hxBoth :
        x ∈
          (latPoly v).boundary (R := ℝ) ∩
            segment ℝ
              (toPlane (v oneParent))
              (toPlane (v q)) :=
      ⟨hxBoundary, by simpa [oneParent] using hx.1⟩
    rw [hclean] at hxBoth
    rcases hxBoth with hp | hqeq
    · simpa [oneParent] using hp
    · exact False.elim <|
        hqNotEdge (hqeq ▸ hx.2)
  · intro x hx
    have hxp : x = toPlane (v oneParent) := by
      simpa [oneParent] using hx
    subst x
    constructor
    · exact left_mem_segment ℝ _ _
    · exact left_mem_affineSegment ℝ _ _

/-- A clean visible chord closes the consecutive chain `1, ..., q` into a
strictly smaller simple polygon. -/
theorem isSimple_vertices_of_clean
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val)
    (hclean :
      (latPoly v).boundary (R := ℝ) ∩
          segment ℝ
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))
            (toPlane (v q)) =
        {toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))),
          toPlane (v q)}) :
    IsSimple (latPoly (vertices v q)) := by
  let last : Fin q.val :=
    ⟨q.val - 1, by omega⟩
  let pred : Fin q.val :=
    ⟨q.val - 2, by omega⟩
  let zero : Fin q.val :=
    ⟨0, by omega⟩
  have hlastIndex :
      frontIndex q last = q := by
    simpa [last] using
      frontIndex_last q (by omega)
  have hzeroIndex :
      frontIndex q zero =
        (⟨1, by omega⟩ : Fin (n + 1)) := by
    simpa [zero] using
      frontIndex_zero q (by omega)
  have hrotateLast :
      finRotate q.val last = zero := by
    simpa [last, zero] using
      finRotate_frontLast q (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro i
    by_cases hi : i.val + 1 < q.val
    · change
        toPlane (v (frontIndex q i)) ≠
          toPlane
            (v
              (frontIndex q
                (finRotate q.val i)))
      rw [frontIndex_rotate_of_lt q i hi]
      exact hsimple.1 (frontIndex q i)
    · have hilast : i = last := by
        apply Fin.ext
        dsimp [last]
        omega
      subst i
      change
        toPlane (v (frontIndex q last)) ≠
          toPlane
            (v
              (frontIndex q
                (finRotate q.val last)))
      rw [hlastIndex, hrotateLast, hzeroIndex]
      exact
        (Helpers.vertex_injective_of_isSimple hsimple).ne
          (by
            intro h
            have hval := congrArg Fin.val h
            simp only at hval
            omega)
  · intro i j hij hnotAdjacent
    by_cases hi : i.val + 1 < q.val
    · by_cases hj : j.val + 1 < q.val
      · rw [edge_of_lt v q i hi,
          edge_of_lt v q j hj]
        apply hsimple.2.1
        · intro hindex
          exact hij (frontIndex_injective q hindex)
        · intro hadj
          apply hnotAdjacent
          rcases hadj with hforward | hbackward
          · left
            apply frontIndex_injective q
            rw [frontIndex_rotate_of_lt q i hi,
              hforward]
          · right
            apply frontIndex_injective q
            rw [frontIndex_rotate_of_lt q j hj,
              hbackward]
      · have hjlast : j = last := by
          apply Fin.ext
          dsimp [last]
          omega
        subst j
        rw [edge_of_lt v q i hi,
          edge_last v q (by omega)]
        have hilast : i ≠ last := by
          exact hij
        have hnot' :
            ¬ Adjacent last i := by
          intro hadj
          apply hnotAdjacent
          simpa [Adjacent, or_comm] using hadj
        exact
          (diagonal_disjoint_inherited_edge
            v hsimple q hq hclean i hi
              hilast hnot').symm
    · have hilast : i = last := by
        apply Fin.ext
        dsimp [last]
        omega
      subst i
      by_cases hj : j.val + 1 < q.val
      · rw [edge_last v q (by omega),
          edge_of_lt v q j hj]
        have hjlast : j ≠ last := by
          intro h
          exact hij h.symm
        exact
          diagonal_disjoint_inherited_edge
            v hsimple q hq hclean j hj
              hjlast hnotAdjacent
      · have hjlast : j = last := by
          apply Fin.ext
          dsimp [last]
          omega
        exact False.elim (hij hjlast.symm)
  · intro i
    by_cases hi : i.val + 1 < q.val
    · by_cases hi2 : i.val + 2 < q.val
      · have hrotateLt :
            (finRotate q.val i).val + 1 < q.val := by
          rw [finRotate_val_of_lt q i hi]
          omega
        rw [edge_of_lt v q i hi,
          edge_of_lt v q (finRotate q.val i)
            hrotateLt]
        have hmap :
            frontIndex q (finRotate q.val i) =
              finRotate (n + 1) (frontIndex q i) :=
          frontIndex_rotate_of_lt q i hi
        change
          (latPoly v).edgeSet ℝ (frontIndex q i) ∩
              (latPoly v).edgeSet ℝ
                (frontIndex q (finRotate q.val i)) =
            {toPlane
              (v (frontIndex q (finRotate q.val i)))}
        rw [hmap]
        exact hsimple.2.2 (frontIndex q i)
      · have hipred : i = pred := by
          apply Fin.ext
          dsimp [pred]
          omega
        subst i
        have hpredLt : pred.val + 1 < q.val := by
          dsimp [pred]
          omega
        have hrotatePred :
            finRotate q.val pred = last := by
          apply Fin.ext
          rw [finRotate_val_of_lt q pred hpredLt]
          dsimp [pred, last]
          omega
        rw [edge_of_lt v q pred hpredLt,
          hrotatePred, edge_last v q (by omega)]
        change
          (latPoly v).edgeSet ℝ (frontIndex q pred) ∩
              segment ℝ
                (toPlane
                  (v
                    (⟨1, by omega⟩ :
                      Fin (n + 1))))
                (toPlane (v q)) =
            {toPlane (v (frontIndex q last))}
        rw [hlastIndex]
        simpa [pred] using
          predecessor_edge_inter_diagonal
            v hsimple q hq hclean
    · have hilast : i = last := by
        apply Fin.ext
        dsimp [last]
        omega
      subst i
      have hzeroLt : zero.val + 1 < q.val := by
        dsimp [zero]
        omega
      rw [hrotateLast, edge_last v q (by omega),
        edge_of_lt v q zero hzeroLt]
      change
        segment ℝ
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))
              (toPlane (v q)) ∩
            (latPoly v).edgeSet ℝ (frontIndex q zero) =
          {toPlane (v (frontIndex q zero))}
      rw [hzeroIndex]
      exact
        diagonal_inter_first_edge
          v hsimple q hq hclean

end Submission.FrontSubpolygon
