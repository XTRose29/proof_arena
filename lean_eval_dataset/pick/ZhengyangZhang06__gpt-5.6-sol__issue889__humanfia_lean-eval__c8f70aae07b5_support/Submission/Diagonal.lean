import Submission.Split

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.Diagonal

/-- Lattice points on the closed segment joining two lattice points. -/
def closedLatticeSegment (a b : ℤ × ℤ) :
    Set (ℤ × ℤ) :=
  {z |
    toPlane z ∈
      segment ℝ (toPlane a) (toPlane b)}

/-- Lattice points in the relative interior of the segment joining two
lattice points. -/
def openLatticeSegment (a b : ℤ × ℤ) :
    Set (ℤ × ℤ) :=
  {z |
    toPlane z ∈
      openSegment ℝ (toPlane a) (toPlane b)}

/-- The real segment between two points is compact. -/
theorem isCompact_segment_real (a b : ℝ × ℝ) :
    IsCompact (segment ℝ a b) := by
  rw [segment_eq_image]
  exact isCompact_Icc.image (by fun_prop)

/-- The graph of a measurable real function has planar Lebesgue measure
zero. -/
theorem volume_graph_eq_zero (f : ℝ → ℝ)
    (hf : Measurable f) :
    volume {p : ℝ × ℝ | p.2 = f p.1} = 0 := by
  have hmeas :
      MeasurableSet {p : ℝ × ℝ | p.2 = f p.1} :=
    measurableSet_eq_fun measurable_snd
      (hf.comp measurable_fst)
  rw [Measure.volume_eq_prod, Measure.prod_apply hmeas]
  simp

/-- Likewise, a graph over the second coordinate has planar measure zero. -/
theorem volume_verticalGraph_eq_zero (f : ℝ → ℝ)
    (hf : Measurable f) :
    volume {p : ℝ × ℝ | p.1 = f p.2} = 0 := by
  have hmeas :
      MeasurableSet {p : ℝ × ℝ | p.1 = f p.2} :=
    measurableSet_eq_fun measurable_fst
      (hf.comp measurable_snd)
  rw [Measure.volume_eq_prod, Measure.prod_apply_symm hmeas]
  simp

/-- Every real line segment has planar Lebesgue measure zero. -/
theorem volume_segment_real (a b : ℝ × ℝ) :
    volume (segment ℝ a b) = 0 := by
  by_cases hvertical : a.1 = b.1
  · apply measure_mono_null
      (t := {p : ℝ × ℝ | p.1 = a.1})
    · intro p hp
      rw [segment_eq_image] at hp
      rcases hp with ⟨t, _, rfl⟩
      simp [hvertical]
      ring
    · exact volume_verticalGraph_eq_zero (fun _ => a.1)
        measurable_const
  · let slope : ℝ := (b.2 - a.2) / (b.1 - a.1)
    let line : ℝ → ℝ :=
      fun x => a.2 + slope * (x - a.1)
    apply measure_mono_null
      (t := {p : ℝ × ℝ | p.2 = line p.1})
    · intro p hp
      rw [segment_eq_image] at hp
      rcases hp with ⟨t, _, rfl⟩
      change
        (1 - t) * a.2 + t * b.2 =
          a.2 +
            (b.2 - a.2) / (b.1 - a.1) *
              ((1 - t) * a.1 + t * b.1 - a.1)
      field_simp
      ring
    · exact volume_graph_eq_zero line (by
        dsimp [line, slope]
        fun_prop)

/-- A nondegenerate open segment is the closed segment with its endpoints
removed. -/
theorem openSegment_eq_segment_sdiff
    {a b : ℝ × ℝ} (hab : a ≠ b) :
    openSegment ℝ a b =
      segment ℝ a b \ {a, b} := by
  ext p
  constructor
  · intro hp
    refine
      ⟨openSegment_subset_segment ℝ a b hp, ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    constructor
    · intro hpa
      subst p
      exact hab (left_mem_openSegment_iff.mp hp)
    · intro hpb
      subst p
      exact hab (right_mem_openSegment_iff.mp hp)
  · rintro ⟨hpsegment, hpends⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] at hpends
    exact
      mem_openSegment_of_ne_left_right
        (Ne.symm hpends.1) (Ne.symm hpends.2) hpsegment

/-- A nondegenerate open segment is Lebesgue measurable. -/
theorem measurableSet_openSegment_real
    {a b : ℝ × ℝ} (hab : a ≠ b) :
    MeasurableSet (openSegment ℝ a b) := by
  rw [openSegment_eq_segment_sdiff hab]
  exact
    (isCompact_segment_real a b).isClosed.measurableSet.diff
      ((measurableSet_singleton b).insert a)

/-- Every real open segment has planar Lebesgue measure zero. -/
theorem volume_openSegment_real (a b : ℝ × ℝ) :
    volume (openSegment ℝ a b) = 0 :=
  measure_mono_null
    (openSegment_subset_segment ℝ a b)
    (volume_segment_real a b)

/-- A closed lattice segment contains finitely many lattice points. -/
theorem finite_closedLatticeSegment (a b : ℤ × ℤ) :
    (closedLatticeSegment a b).Finite :=
  Helpers.finite_latticePoints_of_isBounded
    (isCompact_segment_real (toPlane a) (toPlane b)).isBounded

/-- The open lattice segment is a subset of the closed one. -/
theorem openLatticeSegment_subset_closed
    (a b : ℤ × ℤ) :
    openLatticeSegment a b ⊆ closedLatticeSegment a b := by
  intro z hz
  exact
    openSegment_subset_segment ℝ (toPlane a) (toPlane b) hz

/-- An open lattice segment contains finitely many lattice points. -/
theorem finite_openLatticeSegment (a b : ℤ × ℤ) :
    (openLatticeSegment a b).Finite :=
  (finite_closedLatticeSegment a b).subset
    (openLatticeSegment_subset_closed a b)

/-- The closed segment is the open segment together with its two lattice
endpoints. -/
theorem closedLatticeSegment_eq_insert
    (a b : ℤ × ℤ) :
    closedLatticeSegment a b =
      insert a (insert b (openLatticeSegment a b)) := by
  ext z
  change
    toPlane z ∈ segment ℝ (toPlane a) (toPlane b) ↔
      z = a ∨ z = b ∨
        toPlane z ∈ openSegment ℝ (toPlane a) (toPlane b)
  rw [← insert_endpoints_openSegment]
  simp only [Set.mem_insert_iff]
  constructor
  · rintro (hza | hzb | hzopen)
    · exact Or.inl
        (LatticeTriangle.toPlaneIntLinear_injective hza)
    · exact Or.inr <| Or.inl
        (LatticeTriangle.toPlaneIntLinear_injective hzb)
    · exact Or.inr <| Or.inr hzopen
  · rintro (rfl | rfl | hzopen)
    · exact Or.inl rfl
    · exact Or.inr <| Or.inl rfl
    · exact Or.inr <| Or.inr hzopen

/-- Passing from a nondegenerate open lattice segment to its closure adds
exactly its two endpoints. -/
theorem ncard_open_add_two
    {a b : ℤ × ℤ} (hab : a ≠ b) :
    (openLatticeSegment a b).ncard + 2 =
      (closedLatticeSegment a b).ncard := by
  have habPlane : toPlane a ≠ toPlane b := by
    intro h
    exact hab (LatticeTriangle.toPlaneIntLinear_injective h)
  have hbOpen :
      b ∉ openLatticeSegment a b := by
    change
      toPlane b ∉ openSegment ℝ (toPlane a) (toPlane b)
    simpa only [right_mem_openSegment_iff] using habPlane
  have haInsert :
      a ∉ insert b (openLatticeSegment a b) := by
    simp only [Set.mem_insert_iff, not_or]
    refine ⟨hab, ?_⟩
    change
      toPlane a ∉ openSegment ℝ (toPlane a) (toPlane b)
    simpa only [left_mem_openSegment_iff] using habPlane
  rw [closedLatticeSegment_eq_insert,
    Set.ncard_insert_of_notMem haInsert
      (hs :=
        (finite_openLatticeSegment a b).insert b),
    Set.ncard_insert_of_notMem hbOpen
      (hs := finite_openLatticeSegment a b)]

end Submission.Diagonal
