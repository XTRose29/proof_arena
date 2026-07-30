import Submission.EarRemoval

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.Rotate

/-- Rotate a cyclic vertex array forward by one vertex. -/
def rotateVertices {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    Fin n → ℤ × ℤ :=
  fun i => v (finRotate n i)

/-- Rotating vertices merely reindexes polygon edges. -/
theorem edge_rotateVertices {n : ℕ}
    (v : Fin n → ℤ × ℤ) (i : Fin n) :
    (latPoly (rotateVertices v)).edgeSet ℝ i =
      (latPoly v).edgeSet ℝ (finRotate n i) :=
  rfl

/-- Cyclic vertex rotation leaves the polygonal boundary unchanged. -/
theorem boundary_rotateVertices {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    (latPoly (rotateVertices v)).boundary (R := ℝ) =
      (latPoly v).boundary (R := ℝ) := by
  ext p
  simp only [Polygon.boundary, Set.mem_iUnion]
  constructor
  · rintro ⟨i, hi⟩
    exact ⟨finRotate n i, by
      rw [← edge_rotateVertices v i]
      exact hi⟩
  · rintro ⟨j, hj⟩
    let i : Fin n := (finRotate n).symm j
    refine ⟨i, ?_⟩
    rw [edge_rotateVertices]
    rw [show finRotate n i = j by
      exact (finRotate n).apply_symm_apply j]
    exact hj

/-- Cyclic rotation preserves the challenge's area. -/
theorem area_rotateVertices {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    area ((latPoly (rotateVertices v)).boundary (R := ℝ)) =
      area ((latPoly v).boundary (R := ℝ)) := by
  rw [boundary_rotateVertices]

/-- Cyclic rotation preserves boundary lattice-point count. -/
theorem boundaryPts_rotateVertices {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    boundaryPts (rotateVertices v) = boundaryPts v := by
  unfold boundaryPts
  rw [boundary_rotateVertices]

/-- Cyclic rotation preserves interior lattice-point count. -/
theorem interiorPts_rotateVertices {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    interiorPts (rotateVertices v) = interiorPts v := by
  unfold interiorPts
  rw [boundary_rotateVertices]

/-- Cyclic adjacency is invariant under simultaneous cyclic rotation. -/
theorem adjacent_rotate_iff {n : ℕ}
    (i j : Fin n) :
    Adjacent (finRotate n i) (finRotate n j) ↔
      Adjacent i j := by
  unfold Adjacent
  constructor
  · rintro (hforward | hbackward)
    · exact Or.inl ((finRotate n).injective hforward)
    · exact Or.inr ((finRotate n).injective hbackward)
  · rintro (hforward | hbackward)
    · exact Or.inl (congrArg (finRotate n) hforward)
    · exact Or.inr (congrArg (finRotate n) hbackward)

/-- The supplied simplicity predicate is invariant under cyclic vertex
rotation. -/
theorem isSimple_rotateVertices {n : ℕ}
    {v : Fin n → ℤ × ℤ}
    (hsimple : IsSimple (latPoly v)) :
    IsSimple (latPoly (rotateVertices v)) := by
  rcases hsimple with
    ⟨hnondegenerate, hdisjoint, hintersection⟩
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact hnondegenerate (finRotate n i)
  · intro i j hij hnotAdjacent
    rw [edge_rotateVertices, edge_rotateVertices]
    apply hdisjoint (finRotate n i) (finRotate n j)
    · exact fun h => hij ((finRotate n).injective h)
    · exact fun h =>
        hnotAdjacent
          ((adjacent_rotate_iff i j).mp h)
  · intro i
    rw [edge_rotateVertices, edge_rotateVertices]
    exact hintersection (finRotate n i)

/-- Rotate a cyclic vertex array `k` times. -/
def rotatePow {n : ℕ} :
    ℕ → (Fin n → ℤ × ℤ) → (Fin n → ℤ × ℤ)
  | 0, v => v
  | k + 1, v => rotateVertices (rotatePow k v)

@[simp]
theorem rotatePow_zero {n : ℕ}
    (v : Fin n → ℤ × ℤ) :
    rotatePow 0 v = v :=
  rfl

@[simp]
theorem rotatePow_succ {n : ℕ} (k : ℕ)
    (v : Fin n → ℤ × ℤ) :
    rotatePow (k + 1) v =
      rotateVertices (rotatePow k v) :=
  rfl

/-- Pointwise, rotating a vertex array `k` times precomposes it with the
`k`-fold iterate of `finRotate`. -/
theorem rotatePow_apply {n : ℕ} (k : ℕ)
    (v : Fin n → ℤ × ℤ) (i : Fin n) :
    rotatePow k v i =
      v (((finRotate n)^[k]) i) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
      change
        rotatePow k v (finRotate n i) =
          v (((finRotate n)^[k + 1]) i)
      rw [ih]
      simpa only [Nat.succ_eq_add_one] using
        congrArg v
          (Function.iterate_succ_apply
            (finRotate n) k i).symm

/-- Arbitrary cyclic rotation reindexes each edge by the corresponding
iterate of `finRotate`. -/
theorem edge_rotatePow {n : ℕ} (k : ℕ)
    (v : Fin n → ℤ × ℤ) (i : Fin n) :
    (latPoly (rotatePow k v)).edgeSet ℝ i =
      (latPoly v).edgeSet ℝ
        (((finRotate n)^[k]) i) := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
      change
        (latPoly (rotatePow k v)).edgeSet ℝ
            (finRotate n i) =
          (latPoly v).edgeSet ℝ
            (((finRotate n)^[k + 1]) i)
      rw [ih]
      congr 1

/-- Any number of cyclic rotations leaves the polygonal boundary
unchanged. -/
theorem boundary_rotatePow {n : ℕ} (k : ℕ)
    (v : Fin n → ℤ × ℤ) :
    (latPoly (rotatePow k v)).boundary (R := ℝ) =
      (latPoly v).boundary (R := ℝ) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rotatePow_succ, boundary_rotateVertices, ih]

/-- Any selected vertex can be moved to ear position `1` by a cyclic
rotation. -/
theorem exists_rotatePow_one_eq
    {n : ℕ} (hn : 2 ≤ n)
    (v : Fin n → ℤ × ℤ) (i : Fin n) :
    ∃ k : ℕ,
      rotatePow k v (⟨1, by omega⟩ : Fin n) =
        v i := by
  letI : NeZero n := ⟨by omega⟩
  let shift : Fin n := i - 1
  refine ⟨shift.val, ?_⟩
  rw [rotatePow_apply,
    ← finCycle_eq_finRotate_iterate (k := shift)]
  rw [finCycle_apply]
  change
    v ((⟨1, by omega⟩ : Fin n) + shift) = v i
  congr 1
  have hone :
      (⟨1, by omega⟩ : Fin n) = 1 := by
    apply Fin.ext
    change 1 = 1 % n
    rw [Nat.mod_eq_of_lt (by omega)]
  rw [hone, add_comm]
  simp [shift]

/-- Any number of cyclic rotations preserves area. -/
theorem area_rotatePow {n : ℕ} (k : ℕ)
    (v : Fin n → ℤ × ℤ) :
    area ((latPoly (rotatePow k v)).boundary (R := ℝ)) =
      area ((latPoly v).boundary (R := ℝ)) := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rotatePow_succ, area_rotateVertices, ih]

/-- Any number of cyclic rotations preserves interior lattice count. -/
theorem interiorPts_rotatePow {n : ℕ} (k : ℕ)
    (v : Fin n → ℤ × ℤ) :
    interiorPts (rotatePow k v) = interiorPts v := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rotatePow_succ, interiorPts_rotateVertices, ih]

/-- Any number of cyclic rotations preserves boundary lattice count. -/
theorem boundaryPts_rotatePow {n : ℕ} (k : ℕ)
    (v : Fin n → ℤ × ℤ) :
    boundaryPts (rotatePow k v) = boundaryPts v := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [rotatePow_succ, boundaryPts_rotateVertices, ih]

/-- Any number of cyclic rotations preserves simplicity. -/
theorem isSimple_rotatePow {n : ℕ} (k : ℕ)
    {v : Fin n → ℤ × ℤ}
    (hsimple : IsSimple (latPoly v)) :
    IsSimple (latPoly (rotatePow k v)) := by
  induction k with
  | zero => exact hsimple
  | succ k ih =>
      exact isSimple_rotateVertices ih

/-- Transport a checked decomposition back across any number of cyclic
rotations. -/
noncomputable def unrotateDecomposition {n : ℕ}
    (k : ℕ) (v : Fin n → ℤ × ℤ)
    (decomposition :
      Dissection.PickDecomposition (rotatePow k v)) :
    Dissection.PickDecomposition v :=
  Dissection.PickDecomposition.transport v (rotatePow k v)
    (area_rotatePow k v).symm
    (interiorPts_rotatePow k v).symm
    (boundaryPts_rotatePow k v).symm
    decomposition

end Submission.Rotate
