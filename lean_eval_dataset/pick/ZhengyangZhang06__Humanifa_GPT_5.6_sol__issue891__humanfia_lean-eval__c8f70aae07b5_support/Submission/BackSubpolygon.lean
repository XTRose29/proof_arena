import Submission.FrontSubpolygon

open LeanEval.Geometry.PicksTheorem

namespace Submission.BackSubpolygon

/-- Number of vertices on the complementary consecutive chain
`q, ..., n, 0, 1`. -/
def size {n : ℕ} (q : Fin (n + 1)) : ℕ :=
  n + 3 - q.val

/-- Rotate the original array until `q` occupies index `1`. -/
def rotated
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1)) :
    Fin (n + 1) → ℤ × ℤ :=
  Rotate.rotatePow (q.val - 1) v

/-- In the rotated array, this is the index of original vertex `1`. -/
def endpoint
    {n : ℕ} (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    Fin (n + 1) :=
  ⟨size q, by
    dsimp [size]
    omega⟩

@[simp]
theorem endpoint_val
    {n : ℕ} (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    (endpoint q hq).val = size q :=
  rfl

/-- After rotation, index `1` is original vertex `q`. -/
theorem rotated_one
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    rotated v q
        (⟨1, by omega⟩ : Fin (n + 1)) =
      v q := by
  let shift : Fin (n + 1) :=
    ⟨q.val - 1, by omega⟩
  change
    Rotate.rotatePow shift.val v
        (⟨1, by omega⟩ : Fin (n + 1)) =
      v q
  rw [Rotate.rotatePow_apply,
    ← finCycle_eq_finRotate_iterate (k := shift),
    finCycle_apply]
  congr 1
  apply Fin.ext
  change
    (1 + (q.val - 1)) % (n + 1) = q.val
  rw [Nat.mod_eq_of_lt] <;> omega

/-- The terminal front-chain index in the rotated array is original
vertex `1`. -/
theorem rotated_endpoint
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    rotated v q (endpoint q hq) =
      v (⟨1, by omega⟩ : Fin (n + 1)) := by
  let shift : Fin (n + 1) :=
    ⟨q.val - 1, by omega⟩
  change
    Rotate.rotatePow shift.val v (endpoint q hq) =
      v (⟨1, by omega⟩ : Fin (n + 1))
  rw [Rotate.rotatePow_apply,
    ← finCycle_eq_finRotate_iterate (k := shift),
    finCycle_apply]
  congr 1
  apply Fin.ext
  change
    (size q + (q.val - 1)) % (n + 1) = 1
  have hsum :
      size q + (q.val - 1) = n + 2 := by
    dsimp [size]
    omega
  rw [hsum, Nat.mod_eq_sub_mod (by omega)]
  rw [Nat.mod_eq_of_lt] <;> omega

/-- The complementary subpolygon, represented as a front subpolygon of
the rotated original array. -/
def vertices
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    Fin (size q) → ℤ × ℤ :=
  FrontSubpolygon.vertices
    (rotated v q) (endpoint q hq)

/-- Original parent edge index corresponding to a nonclosing edge of the
complementary subpolygon. -/
def parentIndex
    {n : ℕ} (q : Fin (n + 1))
    (i : Fin (size q)) :
    Fin (n + 1) :=
  ⟨(q.val + i.val) % (n + 1),
    Nat.mod_lt _ (by omega)⟩

@[simp]
theorem parentIndex_val
    {n : ℕ} (q : Fin (n + 1))
    (i : Fin (size q)) :
    (parentIndex q i).val =
      (q.val + i.val) % (n + 1) :=
  rfl

/-- Every nonclosing complementary edge is the corresponding parent edge. -/
theorem edge_of_lt
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val)
    (i : Fin (size q))
    (hi : i.val + 1 < size q) :
    (latPoly (vertices v q hq)).edgeSet ℝ i =
      (latPoly v).edgeSet ℝ
        (parentIndex q i) := by
  let shift : Fin (n + 1) :=
    ⟨q.val - 1, by omega⟩
  have hi' :
      i.val + 1 < (endpoint q hq).val := by
    simpa using hi
  change
    (latPoly
      (FrontSubpolygon.vertices
        (rotated v q) (endpoint q hq))).edgeSet ℝ i =
        (latPoly v).edgeSet ℝ
          (parentIndex q i)
  rw [FrontSubpolygon.edge_of_lt
    (rotated v q) (endpoint q hq) i hi']
  change
    (latPoly
      (Rotate.rotatePow (q.val - 1) v)).edgeSet ℝ
        (FrontSubpolygon.frontIndex (endpoint q hq) i) =
      (latPoly v).edgeSet ℝ (parentIndex q i)
  rw [Rotate.edge_rotatePow]
  congr 1
  rw [← finCycle_eq_finRotate_iterate (k := shift),
    finCycle_apply]
  apply Fin.ext
  change
    (i.val + 1 + (q.val - 1)) %
        (n + 1) =
      (q.val + i.val) % (n + 1)
  congr 1
  omega

/-- The complementary subpolygon starts at original vertex `q`. -/
theorem vertices_zero
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    vertices v q hq
        (⟨0, by
          dsimp [size]
          omega⟩ :
          Fin (size q)) =
      v q := by
  let zero : Fin (size q) :=
    ⟨0, by
      dsimp [size]
      omega⟩
  change
    rotated v q
        (FrontSubpolygon.frontIndex
          (endpoint q hq)
          zero) =
      v q
  have hzero :
      FrontSubpolygon.frontIndex
          (endpoint q hq) zero =
        (⟨1, by omega⟩ : Fin (n + 1)) := by
    apply Fin.ext
    rfl
  rw [hzero]
  exact rotated_one v q hq

/-- The final complementary-subpolygon vertex is original vertex `1`. -/
theorem vertices_last
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    vertices v q hq
        (⟨size q - 1, by
          dsimp [size]
          omega⟩ : Fin (size q)) =
      v (⟨1, by omega⟩ : Fin (n + 1)) := by
  have hsize : 0 < size q := by
    dsimp [size]
    omega
  change
    rotated v q
        (FrontSubpolygon.frontIndex
          (endpoint q hq)
          (⟨size q - 1, by
            dsimp [size]
            omega⟩ : Fin (size q))) =
      v (⟨1, by omega⟩ : Fin (n + 1))
  have hlast :
      FrontSubpolygon.frontIndex
          (endpoint q hq)
          (⟨size q - 1, by
            dsimp [size]
            omega⟩ : Fin (size q)) =
        endpoint q hq := by
    simpa using
      FrontSubpolygon.frontIndex_last
        (endpoint q hq) hsize
  rw [hlast]
  exact rotated_endpoint v q hq

/-- The cyclic successor of the penultimate complementary index is its
final index. -/
theorem finRotate_predecessor_last
    {n : ℕ}
    (q : Fin (n + 1))
    (_hq : 3 ≤ q.val) :
    finRotate (size q)
        (⟨size q - 2, by
          dsimp [size]
          omega⟩ : Fin (size q)) =
      (⟨size q - 1, by
        dsimp [size]
        omega⟩ : Fin (size q)) := by
  rw [finRotate_apply]
  apply Fin.ext
  simp [Fin.add_def]
  rw [Nat.mod_eq_of_lt] <;>
    dsimp [size] <;> omega

/-- The predecessor of the final complementary index is its penultimate
index. -/
theorem previous_last
    {n : ℕ}
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    (finRotate (size q)).symm
        (⟨size q - 1, by
          dsimp [size]
          omega⟩ : Fin (size q)) =
      (⟨size q - 2, by
        dsimp [size]
        omega⟩ : Fin (size q)) := by
  apply (finRotate (size q)).injective
  rw [(finRotate (size q)).apply_symm_apply,
    finRotate_predecessor_last q hq]

/-- The edge immediately before the final complementary vertex is original
edge `0`. -/
theorem edge_predecessor_last
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    (latPoly (vertices v q hq)).edgeSet ℝ
        (⟨size q - 2, by
          dsimp [size]
          omega⟩ : Fin (size q)) =
      (latPoly v).edgeSet ℝ 0 := by
  let pred : Fin (size q) :=
    ⟨size q - 2, by
      dsimp [size]
      omega⟩
  let last : Fin (size q) :=
    ⟨size q - 1, by
      dsimp [size]
      omega⟩
  have hpredRotate :
      finRotate (size q) pred = last := by
    simpa [pred, last] using
      finRotate_predecessor_last q hq
  have hlastVertex :
      vertices v q hq last =
        v (⟨1, by omega⟩ : Fin (n + 1)) := by
    simpa [last] using vertices_last v q hq
  have hpredVertex :
      vertices v q hq pred = v 0 := by
    let shift : Fin (n + 1) :=
      ⟨q.val - 1, by omega⟩
    change
      Rotate.rotatePow shift.val v
          (FrontSubpolygon.frontIndex
            (endpoint q hq) pred) =
        v 0
    rw [Rotate.rotatePow_apply,
      ← finCycle_eq_finRotate_iterate (k := shift),
      finCycle_apply]
    congr 1
    apply Fin.ext
    have hsum :
        size q - 1 + (q.val - 1) =
          n + 1 := by
      dsimp [size]
      omega
    simp [FrontSubpolygon.frontIndex, pred,
      shift, Fin.add_def]
    have hpred :
        size q - 2 + 1 = size q - 1 := by
      dsimp [size]
      omega
    rw [hpred, hsum, Nat.mod_self]
  change
    affineSegment ℝ
        (toPlane (vertices v q hq pred))
        (toPlane
          (vertices v q hq
            (finRotate (size q) pred))) =
      affineSegment ℝ
        (toPlane (v 0))
        (toPlane (v (finRotate (n + 1) 0)))
  rw [hpredVertex, hpredRotate, hlastVertex,
    CleanEar.finRotate_zero hn]

/-- The final complementary-subpolygon edge is the clean chord from original
vertex `1` to `q`. -/
theorem edge_last
    {n : ℕ} (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    (latPoly (vertices v q hq)).edgeSet ℝ
        (⟨size q - 1, by
          dsimp [size]
          omega⟩ : Fin (size q)) =
      segment ℝ
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))))
        (toPlane (v q)) := by
  have hsize : 0 < size q := by
    dsimp [size]
    omega
  have hr : 0 < (endpoint q hq).val := by
    simpa using hsize
  have h :
      (latPoly (vertices v q hq)).edgeSet ℝ
          (⟨size q - 1, by
            dsimp [size]
            omega⟩ : Fin (size q)) =
        segment ℝ
          (toPlane
            (rotated v q
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane
            (rotated v q (endpoint q hq))) := by
    simpa [vertices, endpoint] using
      FrontSubpolygon.edge_last
        (rotated v q) (endpoint q hq) hr
  rw [h]
  rw [rotated_one v q hq,
    rotated_endpoint v q hq,
    segment_symm]

/-- The complementary chain contains at least three vertices. -/
theorem three_le_size
    {n : ℕ} (q : Fin (n + 1))
    (_hq : 3 ≤ q.val) :
    3 ≤ size q := by
  dsimp [size]
  omega

/-- Both chains cut out by a nonadjacent chord are strictly smaller than
the original polygon. -/
theorem size_lt_parent
    {n : ℕ} (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    size q < n + 1 := by
  dsimp [size]
  omega

/-- A clean visible chord also closes the complementary consecutive chain
into a strictly smaller simple polygon. -/
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
    IsSimple (latPoly (vertices v q hq)) := by
  let w := rotated v q
  let r := endpoint q hq
  have hwSimple : IsSimple (latPoly w) :=
    Rotate.isSimple_rotatePow (q.val - 1) hsimple
  have hr : 3 ≤ r.val := by
    simpa [r] using three_le_size q hq
  have hwOne :
      w (⟨1, by omega⟩ : Fin (n + 1)) = v q := by
    simpa [w] using rotated_one v q hq
  have hwEndpoint :
      w r =
        v (⟨1, by omega⟩ : Fin (n + 1)) := by
    simpa [w, r] using rotated_endpoint v q hq
  have hwBoundary :
      (latPoly w).boundary (R := ℝ) =
        (latPoly v).boundary (R := ℝ) := by
    simpa [w, rotated] using
      Rotate.boundary_rotatePow (q.val - 1) v
  have hwClean :
      (latPoly w).boundary (R := ℝ) ∩
          segment ℝ
            (toPlane
              (w
                (⟨1, by omega⟩ :
                  Fin (n + 1))))
            (toPlane (w r)) =
        {toPlane
            (w
              (⟨1, by omega⟩ :
                Fin (n + 1))),
          toPlane (w r)} := by
    rw [hwBoundary, hwOne, hwEndpoint,
      segment_symm]
    simpa [Set.pair_comm] using hclean
  change
    IsSimple
      (latPoly
        (FrontSubpolygon.vertices w r))
  exact
    FrontSubpolygon.isSimple_vertices_of_clean
      w hwSimple r hr hwClean

end Submission.BackSubpolygon
