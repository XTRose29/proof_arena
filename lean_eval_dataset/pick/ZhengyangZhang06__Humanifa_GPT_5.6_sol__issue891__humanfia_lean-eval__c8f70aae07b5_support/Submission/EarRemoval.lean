import Submission.Diagonal

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.EarRemoval

/-- The embedding of the reduced index set into the original index set that
omits original vertex `1`. -/
def reducedIndex {n : ℕ} (i : Fin n) : Fin (n + 1) :=
  if i.val = 0 then 0
  else ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩

@[simp]
theorem reducedIndex_zero {n : ℕ} [NeZero n] :
    reducedIndex (0 : Fin n) = 0 := by
  simp [reducedIndex]

theorem reducedIndex_of_val_ne_zero {n : ℕ}
    (i : Fin n) (hi : i.val ≠ 0) :
    reducedIndex i =
      ⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ := by
  simp [reducedIndex, hi]

/-- The reduced index embedding omits precisely the removed original
position `1`. -/
theorem reducedIndex_ne_one
    {n : ℕ} (hn : 1 ≤ n) (i : Fin n) :
    reducedIndex i ≠
      (⟨1, by omega⟩ : Fin (n + 1)) := by
  intro h
  have hval := congrArg Fin.val h
  by_cases hi : i.val = 0
  · simp [reducedIndex, hi] at hval
  · rw [reducedIndex_of_val_ne_zero i hi] at h
    have hval := congrArg Fin.val h
    simp only at hval
    omega

/-- Remove original vertex `1` from a cyclic vertex array. -/
def removeSecond {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ) :
    Fin n → ℤ × ℤ :=
  fun i => v (reducedIndex i)

/-- The triangle cut off at original vertex `1`. -/
def earTriangle {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    Fin 3 → ℤ × ℤ :=
  fun i => v ⟨i.val, i.isLt.trans_le (hn.trans (Nat.le_succ n))⟩

@[simp]
theorem earTriangle_zero {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    earTriangle hn v 0 = v 0 :=
  rfl

@[simp]
theorem earTriangle_one {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    earTriangle hn v 1 = v ⟨1, by omega⟩ :=
  rfl

@[simp]
theorem earTriangle_two {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    earTriangle hn v 2 = v ⟨2, by omega⟩ :=
  rfl

theorem reducedIndex_rotate_of_ne_zero
    {n : ℕ} (hn : 3 ≤ n) (i : Fin n)
    (hi : i.val ≠ 0) :
    reducedIndex (finRotate n i) =
      finRotate (n + 1) (reducedIndex i) := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  by_cases hilast : i = Fin.last m
  · subst i
    have hm : m ≠ 0 := by omega
    have hindex :
        reducedIndex (Fin.last m) =
          Fin.last (m + 1) := by
      apply Fin.ext
      simp [reducedIndex, hm]
    rw [finRotate_last, reducedIndex_zero, hindex,
      finRotate_last]
  · have hrotateVal :
        (finRotate (m + 1) i).val = i.val + 1 :=
      coe_finRotate_of_ne_last hilast
    have hrotateNe :
        (finRotate (m + 1) i).val ≠ 0 := by
      omega
    rw [reducedIndex_of_val_ne_zero _ hrotateNe,
      reducedIndex_of_val_ne_zero i hi]
    have hiLt : i.val < m :=
      Fin.val_lt_last hilast
    have hindexNotLast :
        (⟨i.val + 1, Nat.succ_lt_succ i.isLt⟩ :
          Fin (m + 2)) ≠ Fin.last (m + 1) := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_last] at hval
      omega
    apply Fin.ext
    rw [coe_finRotate_of_ne_last hindexNotLast]
    simp only [hrotateVal]

theorem reducedIndex_rotate_zero
    {n : ℕ} (hn : 3 ≤ n) :
    reducedIndex (finRotate n (⟨0, by omega⟩ : Fin n)) =
      (⟨2, by omega⟩ : Fin (n + 1)) := by
  obtain ⟨m, rfl⟩ :=
    Nat.exists_eq_succ_of_ne_zero (by omega : n ≠ 0)
  have hmpos : 0 < m := by omega
  letI : NeZero m := ⟨hmpos.ne'⟩
  have hrotate :
      finRotate (m + 1) (0 : Fin (m + 1)) =
        (1 : Fin (m + 1)) :=
    finRotate_apply_zero
  change
    reducedIndex (finRotate (m + 1) (0 : Fin (m + 1))) =
      (⟨2, by omega⟩ : Fin (m + 2))
  rw [hrotate]
  apply Fin.ext
  simp [reducedIndex,
    Nat.mod_eq_of_lt (by omega : 1 < m + 1)]

/-- Every noninitial edge of the reduced polygon is the corresponding edge
of the original polygon. -/
theorem reduced_edge_of_ne_zero
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (i : Fin n) (hi : i.val ≠ 0) :
    (latPoly (removeSecond v)).edgeSet ℝ i =
      (latPoly v).edgeSet ℝ (reducedIndex i) := by
  change
    affineSegment ℝ
      (toPlane (v (reducedIndex i)))
      (toPlane (v (reducedIndex (finRotate n i)))) =
    affineSegment ℝ
      (toPlane (v (reducedIndex i)))
      (toPlane (v (finRotate (n + 1) (reducedIndex i))))
  rw [reducedIndex_rotate_of_ne_zero hn i hi]

/-- The initial edge of the reduced polygon is the new diagonal from
original vertex `0` to original vertex `2`. -/
theorem reduced_edge_zero
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    (latPoly (removeSecond v)).edgeSet ℝ
        (⟨0, by omega⟩ : Fin n) =
      segment ℝ (toPlane (v 0))
        (toPlane (v ⟨2, by omega⟩)) := by
  change
    affineSegment ℝ
      (toPlane (v (reducedIndex (⟨0, by omega⟩ : Fin n))))
      (toPlane
        (v (reducedIndex
          (finRotate n (⟨0, by omega⟩ : Fin n))))) =
      segment ℝ (toPlane (v 0))
        (toPlane (v ⟨2, by omega⟩))
  rw [affineSegment_eq_segment, reducedIndex_rotate_zero hn]
  have hzero :
      reducedIndex (⟨0, by omega⟩ : Fin n) =
        (0 : Fin (n + 1)) := by
    apply Fin.ext
    simp [reducedIndex]
  rw [hzero]

/-- Ear edge `0` is original edge `0`. -/
theorem ear_edge_zero
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    (latPoly (earTriangle hn v)).edgeSet ℝ 0 =
      (latPoly v).edgeSet ℝ 0 := by
  change
    affineSegment ℝ
      (toPlane (v ⟨0, by omega⟩))
      (toPlane (v ⟨1, by omega⟩)) =
    affineSegment ℝ
      (toPlane (v 0))
      (toPlane (v (finRotate (n + 1) 0)))
  have hrotate :
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
  rw [hrotate]
  have hzero :
      (⟨0, by omega⟩ : Fin (n + 1)) = 0 := by
    apply Fin.ext
    rfl
  rw [hzero]

/-- Ear edge `1` is original edge `1`. -/
theorem ear_edge_one
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    (latPoly (earTriangle hn v)).edgeSet ℝ 1 =
      (latPoly v).edgeSet ℝ ⟨1, by omega⟩ := by
  have hrotate :
      finRotate (n + 1) (⟨1, by omega⟩ : Fin (n + 1)) =
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
  change
    affineSegment ℝ
      (toPlane (v ⟨1, by omega⟩))
      (toPlane (v ⟨2, by omega⟩)) =
    affineSegment ℝ
      (toPlane (v ⟨1, by omega⟩))
      (toPlane
        (v (finRotate (n + 1) (⟨1, by omega⟩ :
          Fin (n + 1)))))
  rw [hrotate]

/-- Ear edge `2` is the new diagonal, with the opposite orientation. -/
theorem ear_edge_two
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    (latPoly (earTriangle hn v)).edgeSet ℝ 2 =
      segment ℝ (toPlane (v 0))
        (toPlane (v ⟨2, by omega⟩)) := by
  change
    affineSegment ℝ
      (toPlane (v ⟨2, by omega⟩))
      (toPlane (v ⟨0, by omega⟩)) =
    segment ℝ (toPlane (v 0))
      (toPlane (v ⟨2, by omega⟩))
  rw [affineSegment_eq_segment, segment_symm]
  have hzero :
      (⟨0, by omega⟩ : Fin (n + 1)) = 0 := by
    apply Fin.ext
    rfl
  rw [hzero]

/-- Removing ear vertex `1` replaces its two incident boundary edges by the
diagonal from vertex `0` to vertex `2`.  Thus the union of the two child
boundaries is the original boundary together with that diagonal. -/
theorem child_boundaries_union
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) :
    (latPoly (earTriangle hn v)).boundary (R := ℝ) ∪
        (latPoly (removeSecond v)).boundary (R := ℝ) =
      (latPoly v).boundary (R := ℝ) ∪
        segment ℝ (toPlane (v 0))
          (toPlane (v ⟨2, by omega⟩)) := by
  ext p
  constructor
  · rintro (hear | hreduced)
    · rw [Polygon.boundary] at hear
      rcases Set.mem_iUnion.mp hear with ⟨i, hi⟩
      fin_cases i
      · change
          p ∈ (latPoly (earTriangle hn v)).edgeSet ℝ 0 at hi
        rw [ear_edge_zero hn v] at hi
        exact Or.inl <| Set.mem_iUnion.mpr ⟨0, hi⟩
      · change
          p ∈ (latPoly (earTriangle hn v)).edgeSet ℝ 1 at hi
        rw [ear_edge_one hn v] at hi
        exact Or.inl <| Set.mem_iUnion.mpr
          ⟨⟨1, by omega⟩, hi⟩
      · change
          p ∈ (latPoly (earTriangle hn v)).edgeSet ℝ 2 at hi
        rw [ear_edge_two hn v] at hi
        exact Or.inr hi
    · rw [Polygon.boundary] at hreduced
      rcases Set.mem_iUnion.mp hreduced with ⟨i, hi⟩
      by_cases hizero : i.val = 0
      · have hiIndex :
            i = (⟨0, by omega⟩ : Fin n) :=
          Fin.ext hizero
        rw [hiIndex, reduced_edge_zero hn v] at hi
        exact Or.inr hi
      · rw [reduced_edge_of_ne_zero hn v i hizero] at hi
        exact Or.inl <| Set.mem_iUnion.mpr
          ⟨reducedIndex i, hi⟩
  · rintro (horiginal | hdiagonal)
    · rw [Polygon.boundary] at horiginal
      rcases Set.mem_iUnion.mp horiginal with ⟨i, hi⟩
      by_cases hizero : i.val = 0
      · have hiIndex : i = (0 : Fin (n + 1)) :=
          Fin.ext hizero
        rw [hiIndex] at hi
        exact Or.inl <| Set.mem_iUnion.mpr
          ⟨0, by
            rw [ear_edge_zero hn v]
            exact hi⟩
      · by_cases hione : i.val = 1
        · have hiIndex :
              i = (⟨1, by omega⟩ : Fin (n + 1)) :=
            Fin.ext hione
          rw [hiIndex] at hi
          exact Or.inl <| Set.mem_iUnion.mpr
            ⟨1, by
              rw [ear_edge_one hn v]
              exact hi⟩
        · let j : Fin n :=
            ⟨i.val - 1, by omega⟩
          have hjzero : j.val ≠ 0 := by
            dsimp [j]
            omega
          have hindex : reducedIndex j = i := by
            apply Fin.ext
            simp [reducedIndex, j, hjzero]
            omega
          exact Or.inr <| Set.mem_iUnion.mpr
            ⟨j, by
              rw [reduced_edge_of_ne_zero hn v j hjzero,
                hindex]
              exact hi⟩
    · exact Or.inl <| Set.mem_iUnion.mpr
        ⟨2, by
          rw [ear_edge_two hn v]
          exact hdiagonal⟩

/-- The geometric facts that make original vertex `1` an ear.  The
combinatorial boundary-union identity is automatic; these fields state the
separation and bounded-component facts specific to the chosen diagonal. -/
structure IsEarAtOne
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ) : Prop where
  triangleSimple :
    IsSimple (latPoly (earTriangle hn v))
  reducedSimple :
    IsSimple (latPoly (removeSecond v))
  insidePartition :
    inside ((latPoly v).boundary (R := ℝ)) =
      (inside
          ((latPoly (earTriangle hn v)).boundary (R := ℝ)) ∪
        inside
          ((latPoly (removeSecond v)).boundary (R := ℝ))) ∪
        openSegment ℝ (toPlane (v 0))
          (toPlane (v ⟨2, by omega⟩))
  interiorsDisjoint :
    Disjoint
      (inside
        ((latPoly (earTriangle hn v)).boundary (R := ℝ)))
      (inside
        ((latPoly (removeSecond v)).boundary (R := ℝ)))
  seamDisjoint :
    Disjoint
      (inside
          ((latPoly (earTriangle hn v)).boundary (R := ℝ)) ∪
        inside
          ((latPoly (removeSecond v)).boundary (R := ℝ)))
      (openSegment ℝ (toPlane (v 0))
        (toPlane (v ⟨2, by omega⟩)))
  childBoundaryInter :
    (latPoly (earTriangle hn v)).boundary (R := ℝ) ∩
        (latPoly (removeSecond v)).boundary (R := ℝ) =
      segment ℝ (toPlane (v 0))
        (toPlane (v ⟨2, by omega⟩))
  outerBoundaryInter :
    (latPoly v).boundary (R := ℝ) ∩
        segment ℝ (toPlane (v 0))
          (toPlane (v ⟨2, by omega⟩)) =
      {toPlane (v 0), toPlane (v ⟨2, by omega⟩)}

/-- The coordinatewise lattice embedding pulls a pair of embedded lattice
points back to the original pair. -/
theorem preimage_toPlane_pair (a b : ℤ × ℤ) :
    toPlane ⁻¹' {toPlane a, toPlane b} = {a, b} := by
  ext z
  simp only [Set.mem_preimage, Set.mem_insert_iff,
    Set.mem_singleton_iff]
  constructor
  · rintro (hza | hzb)
    · exact Or.inl
        (LatticeTriangle.toPlaneIntLinear_injective hza)
    · exact Or.inr
        (LatticeTriangle.toPlaneIntLinear_injective hzb)
  · rintro (rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- A geometric ear and decompositions of its two children produce a
decomposition of the original polygon. -/
noncomputable def decomposition_of_ear
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (hear : IsEarAtOne hn v)
    (triangleDecomposition :
      Dissection.PickDecomposition (earTriangle hn v))
    (reducedDecomposition :
      Dissection.PickDecomposition (removeSecond v)) :
    Dissection.PickDecomposition v := by
  let diagonal :=
    Diagonal.closedLatticeSegment (v 0)
      (v ⟨2, by omega⟩)
  let diagonalInterior :=
    Diagonal.openLatticeSegment (v 0)
      (v ⟨2, by omega⟩)
  have hindex :
      (0 : Fin (n + 1)) ≠
        (⟨2, by omega⟩ : Fin (n + 1)) := by
    intro h
    have hval := congrArg Fin.val h
    norm_num at hval
  have hv :
      v 0 ≠ v ⟨2, by omega⟩ :=
    (Helpers.lattice_vertex_injective_of_isSimple hsimple).ne
      hindex
  have hvPlane :
      toPlane (v 0) ≠ toPlane (v ⟨2, by omega⟩) := by
    intro h
    exact hv (LatticeTriangle.toPlaneIntLinear_injective h)
  have harea :
      area ((latPoly v).boundary (R := ℝ)) =
        area
            ((latPoly (earTriangle hn v)).boundary (R := ℝ)) +
          area
            ((latPoly (removeSecond v)).boundary (R := ℝ)) :=
    Split.area_add_of_inside_partition v
      (earTriangle hn v) (removeSecond v)
      (openSegment ℝ (toPlane (v 0))
        (toPlane (v ⟨2, by omega⟩)))
      hear.insidePartition hear.interiorsDisjoint
      hear.seamDisjoint
      (Diagonal.measurableSet_openSegment_real hvPlane)
      (Diagonal.volume_openSegment_real _ _)
  have hinterior :
      Split.interiorLatticeSet v =
        (Split.interiorLatticeSet (earTriangle hn v) ∪
          Split.interiorLatticeSet (removeSecond v)) ∪
          diagonalInterior := by
    unfold Split.interiorLatticeSet diagonalInterior
      Diagonal.openLatticeSegment
    change
      toPlane ⁻¹'
          inside ((latPoly v).boundary (R := ℝ)) =
        (toPlane ⁻¹'
            inside
              ((latPoly (earTriangle hn v)).boundary (R := ℝ)) ∪
          toPlane ⁻¹'
            inside
              ((latPoly (removeSecond v)).boundary (R := ℝ))) ∪
          toPlane ⁻¹'
            openSegment ℝ (toPlane (v 0))
              (toPlane (v ⟨2, by omega⟩))
    rw [hear.insidePartition, Set.preimage_union,
      Set.preimage_union]
  have hinteriorLeftRight :
      Disjoint
        (Split.interiorLatticeSet (earTriangle hn v))
        (Split.interiorLatticeSet (removeSecond v)) := by
    rw [Set.disjoint_left]
    intro z hzTriangle hzReduced
    exact
      Set.disjoint_left.mp hear.interiorsDisjoint
        hzTriangle hzReduced
  have hinteriorDiagonal :
      Disjoint
        (Split.interiorLatticeSet (earTriangle hn v) ∪
          Split.interiorLatticeSet (removeSecond v))
        diagonalInterior := by
    rw [Set.disjoint_left]
    intro z hzChildren hzDiagonal
    exact
      Set.disjoint_left.mp hear.seamDisjoint
        hzChildren hzDiagonal
  have hboundary :
      Split.boundaryLatticeSet (earTriangle hn v) ∪
          Split.boundaryLatticeSet (removeSecond v) =
        Split.boundaryLatticeSet v ∪ diagonal := by
    unfold Split.boundaryLatticeSet diagonal
      Diagonal.closedLatticeSegment
    change
      toPlane ⁻¹'
          ((latPoly (earTriangle hn v)).boundary (R := ℝ) ∪
            (latPoly (removeSecond v)).boundary (R := ℝ)) =
        toPlane ⁻¹'
          ((latPoly v).boundary (R := ℝ) ∪
            segment ℝ (toPlane (v 0))
              (toPlane (v ⟨2, by omega⟩)))
    rw [child_boundaries_union hn v]
  have hboundaryInter :
      Split.boundaryLatticeSet (earTriangle hn v) ∩
          Split.boundaryLatticeSet (removeSecond v) =
        diagonal := by
    unfold Split.boundaryLatticeSet diagonal
      Diagonal.closedLatticeSegment
    change
      toPlane ⁻¹'
          ((latPoly (earTriangle hn v)).boundary (R := ℝ) ∩
            (latPoly (removeSecond v)).boundary (R := ℝ)) =
        toPlane ⁻¹'
          segment ℝ (toPlane (v 0))
            (toPlane (v ⟨2, by omega⟩))
    rw [hear.childBoundaryInter]
  have houterSet :
      Split.boundaryLatticeSet v ∩ diagonal =
        {v 0, v ⟨2, by omega⟩} := by
    unfold Split.boundaryLatticeSet diagonal
      Diagonal.closedLatticeSegment
    change
      toPlane ⁻¹'
          ((latPoly v).boundary (R := ℝ) ∩
            segment ℝ (toPlane (v 0))
              (toPlane (v ⟨2, by omega⟩))) =
        {v 0, v ⟨2, by omega⟩}
    rw [hear.outerBoundaryInter,
      preimage_toPlane_pair]
  have hboundaryEndpoints :
      (Split.boundaryLatticeSet v ∩ diagonal).ncard = 2 := by
    rw [houterSet]
    simp [hv]
  apply Split.glueDecompositions v
    (earTriangle hn v) (removeSecond v)
    diagonal diagonalInterior harea hinterior
    hinteriorLeftRight hinteriorDiagonal
  · exact Diagonal.finite_openLatticeSegment _ _
  · exact Diagonal.ncard_open_add_two hv
  · exact hboundary
  · exact hboundaryInter
  · exact hboundaryEndpoints
  · exact Diagonal.finite_closedLatticeSegment _ _
  · exact triangleDecomposition
  · exact reducedDecomposition

end Submission.EarRemoval
