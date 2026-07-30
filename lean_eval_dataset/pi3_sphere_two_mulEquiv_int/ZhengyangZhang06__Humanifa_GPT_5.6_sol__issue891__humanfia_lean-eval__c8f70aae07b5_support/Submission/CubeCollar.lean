import Mathlib

open scoped unitInterval Topology

noncomputable section

namespace Submission.CubeCollar

open Set

/-- Collapse the outer quarters of the unit interval to its endpoints. -/
def coordinate (t : I) : I :=
  projIcc 0 1 zero_le_one (2 * (t : ℝ) - 1 / 2)

@[continuity, fun_prop]
theorem continuous_coordinate : Continuous coordinate :=
  continuous_projIcc.comp (by fun_prop)

theorem coordinate_eq_zero_of_le {t : I} (ht : (t : ℝ) ≤ 1 / 4) :
    coordinate t = 0 := by
  simpa [coordinate] using
    (projIcc_of_le_left (a := (0 : ℝ)) (b := 1) (h := zero_le_one)
      (x := 2 * (t : ℝ) - 1 / 2) (by linarith))

theorem coordinate_eq_one_of_le {t : I} (ht : 3 / 4 ≤ (t : ℝ)) :
    coordinate t = 1 := by
  simpa [coordinate] using
    (projIcc_of_right_le (a := (0 : ℝ)) (b := 1) (h := zero_le_one)
      (x := 2 * (t : ℝ) - 1 / 2) (by linarith))

@[simp]
theorem coordinate_zero : coordinate 0 = 0 :=
  coordinate_eq_zero_of_le (by norm_num)

@[simp]
theorem coordinate_one : coordinate 1 = 1 :=
  coordinate_eq_one_of_le (by norm_num)

/-- Apply the collar collapse in every cubical coordinate. -/
def cubeMap {N : Type*} (t : N → I) : N → I :=
  fun i => coordinate (t i)

@[continuity, fun_prop]
theorem continuous_cubeMap {N : Type*} : Continuous (@cubeMap N) := by
  unfold cubeMap
  fun_prop

theorem cubeMap_mem_boundary {N : Type*} {t : N → I}
    (ht : t ∈ Cube.boundary N) :
    cubeMap t ∈ Cube.boundary N := by
  obtain ⟨i, hi | hi⟩ := ht
  · exact ⟨i, Or.inl (by simp [cubeMap, hi])⟩
  · exact ⟨i, Or.inr (by simp [cubeMap, hi])⟩

/-- Interpolate inside the cube from the identity to `cubeMap`. -/
def cubeHomotopy {N : Type*} (z : I × (N → I)) : N → I :=
  fun i => Icc.convexComb (z.2 i) (cubeMap z.2 i) z.1

@[continuity, fun_prop]
theorem continuous_cubeHomotopy {N : Type*} :
    Continuous (@cubeHomotopy N) := by
  unfold cubeHomotopy cubeMap
  fun_prop

@[simp]
theorem cubeHomotopy_zero {N : Type*} (t : N → I) :
    cubeHomotopy (0, t) = t := by
  ext i
  simp [cubeHomotopy]

@[simp]
theorem cubeHomotopy_one {N : Type*} (t : N → I) :
    cubeHomotopy (1, t) = cubeMap t := by
  ext i
  simp [cubeHomotopy]

theorem cubeHomotopy_mem_boundary {N : Type*} (s : I) {t : N → I}
    (ht : t ∈ Cube.boundary N) :
    cubeHomotopy (s, t) ∈ Cube.boundary N := by
  obtain ⟨i, hi | hi⟩ := ht
  · exact ⟨i, Or.inl (by simp [cubeHomotopy, cubeMap, hi])⟩
  · exact ⟨i, Or.inr (by simp [cubeHomotopy, cubeMap, hi])⟩

variable {N X : Type*} [TopologicalSpace X] {x : X}

/-- Reparametrize a generalized loop so that it is constant on a collar of
the cubical boundary. -/
def collared (p : GenLoop N X x) : GenLoop N X x :=
  ⟨p.1.comp ⟨cubeMap, continuous_cubeMap⟩,
    fun t ht => p.property (cubeMap t) (cubeMap_mem_boundary ht)⟩

/-- The collar reparametrization does not change a generalized-loop
homotopy class. -/
def collarHomotopy (p : GenLoop N X x) :
    p.1.HomotopyRel (collared p).1 (Cube.boundary N) where
  toFun z := p (cubeHomotopy z)
  continuous_toFun := p.1.continuous.comp continuous_cubeHomotopy
  map_zero_left t := by simp
  map_one_left t := by simp [collared]
  prop' s t ht := by
    calc
      p (cubeHomotopy (s, t)) = x :=
        p.property _ (cubeHomotopy_mem_boundary s ht)
      _ = p t := (p.property t ht).symm

theorem homotopic_collared (p : GenLoop N X x) :
    GenLoop.Homotopic p (collared p) :=
  ⟨collarHomotopy p⟩

/-- An open collar of the cubical boundary. -/
def neighborhood (N : Type*) : Set (N → I) :=
  {t | ∃ i, (t i : ℝ) < 1 / 4 ∨ 3 / 4 < (t i : ℝ)}

theorem isOpen_neighborhood (N : Type*) : IsOpen (neighborhood N) := by
  rw [show neighborhood N =
      ⋃ i, {t : N → I | (t i : ℝ) < 1 / 4} ∪
        {t : N → I | 3 / 4 < (t i : ℝ)} by
    ext t
    simp [neighborhood]]
  apply isOpen_iUnion
  intro i
  have hi : Continuous (fun t : N → I => (t i : ℝ)) :=
    continuous_subtype_val.comp (continuous_apply i)
  exact (isOpen_lt hi continuous_const).union (isOpen_lt continuous_const hi)

theorem boundary_subset_neighborhood (N : Type*) :
    Cube.boundary N ⊆ neighborhood N := by
  rintro t ⟨i, hi | hi⟩
  · exact ⟨i, Or.inl (by norm_num [hi])⟩
  · exact ⟨i, Or.inr (by norm_num [hi])⟩

theorem collared_eq_basepoint_on_neighborhood (p : GenLoop N X x)
    {t : N → I} (ht : t ∈ neighborhood N) :
    collared p t = x := by
  obtain ⟨i, hi | hi⟩ := ht
  · apply p.property
    exact ⟨i, Or.inl <| coordinate_eq_zero_of_le hi.le⟩
  · apply p.property
    exact ⟨i, Or.inr <| coordinate_eq_one_of_le hi.le⟩

end Submission.CubeCollar
