import Submission.ConvexEar
import Submission.Rotate

open LeanEval.Geometry.PicksTheorem

namespace Submission.ExtremeVertex

/-- A weighted lexicographic height on lattice points. -/
def latticeHeight (M : ℤ) (z : ℤ × ℤ) : ℤ :=
  M * z.1 + z.2

/-- The corresponding real supporting functional, with sign chosen so that
a lattice-height minimum is a functional maximum. -/
def exposingFunctional (M : ℤ) :
    (ℝ × ℝ) →L[ℝ] ℝ :=
  -((M : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ +
    ContinuousLinearMap.snd ℝ ℝ ℝ)

@[simp]
theorem exposingFunctional_toPlane
    (M : ℤ) (z : ℤ × ℤ) :
    exposingFunctional M (toPlane z) =
      -(M * z.1 + z.2 : ℤ) := by
  simp [exposingFunctional, toPlane]

/-- A strict linear-functional bound at every vertex holds on every polygon
edge, since an open linear half-space is convex. -/
theorem continuousLinearMap_lt_on_boundary
    {n : ℕ}
    (v : Fin n → ℤ × ℤ)
    (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (c : ℝ)
    (hvertices :
      ∀ i : Fin n, L (toPlane (v i)) < c) :
    ∀ x ∈ (latPoly v).boundary (R := ℝ),
      L x < c := by
  intro x hx
  rw [Polygon.boundary] at hx
  obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
  have hhalfspace :
      Convex ℝ {y : ℝ × ℝ | L y < c} :=
    convex_halfSpace_lt L.toLinearMap.isLinear c
  exact
    hhalfspace.segment_subset
      (hvertices i)
      (hvertices (finRotate n i))
      (by
        simpa only [Polygon.edgeSet,
          affineSegment_eq_segment, latPoly] using hi)

/-- If original vertex `1` is strictly exposed, the entire boundary after
removing that vertex lies in the strict lower half-space. -/
theorem exposingFunctional_lt_on_reduced_boundary
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (M : ℤ)
    (hvertices :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          exposingFunctional M (toPlane (v j)) <
            exposingFunctional M
              (toPlane
                (v (⟨1, by omega⟩ : Fin (n + 1))))) :
    ∀ x ∈
        (latPoly (EarRemoval.removeSecond v)).boundary
          (R := ℝ),
      exposingFunctional M x <
        exposingFunctional M
          (toPlane
            (v (⟨1, by omega⟩ : Fin (n + 1)))) := by
  apply continuousLinearMap_lt_on_boundary
  intro i
  exact
    hvertices (EarRemoval.reducedIndex i)
      (EarRemoval.reducedIndex_ne_one
        (by omega) i)

/-- A finite injective lattice vertex array has a vertex uniquely exposed by
an integral linear functional.  Lexicographic minimization selects the
vertex; a finite bound on second-coordinate variation makes the first
coordinate dominate. -/
theorem exists_strict_latticeHeight_min
    {n : ℕ} [NeZero n]
    (v : Fin n → ℤ × ℤ)
    (hinjective : Function.Injective v) :
    ∃ (i : Fin n) (M : ℤ),
      0 < M ∧
        ∀ j : Fin n, j ≠ i →
          latticeHeight M (v i) <
            latticeHeight M (v j) := by
  obtain ⟨i, _, hi⟩ :=
    Finset.exists_min_image
      Finset.univ
      (fun j : Fin n =>
        (toLex (v j) : ℤ ×ₗ ℤ))
      Finset.univ_nonempty
  obtain ⟨C, hC⟩ :=
    Finite.exists_le
      (fun j : Fin n =>
        |(v j).2 - (v i).2|)
  have hCnonneg : 0 ≤ C := by
    simpa using hC i
  refine ⟨i, C + 1, by omega, ?_⟩
  intro j hji
  have hlex :
      (toLex (v i) : ℤ ×ₗ ℤ) ≤
        toLex (v j) :=
    hi j (Finset.mem_univ j)
  rcases Prod.Lex.toLex_le_toLex.mp hlex with
    hfirst | ⟨hfirst, hsecond⟩
  · have hfirstGap :
        1 ≤ (v j).1 - (v i).1 := by
      omega
    have hweightedGap :
        C + 1 ≤
          (C + 1) * ((v j).1 - (v i).1) :=
      by
        simpa using
          (mul_le_mul_of_nonneg_left
            (a := C + 1) hfirstGap
            (show 0 ≤ C + 1 by omega))
    have hsecondGap :
        -C ≤ (v j).2 - (v i).2 :=
      neg_le_of_abs_le (hC j)
    have hpositive :
        0 <
          (C + 1) * ((v j).1 - (v i).1) +
            ((v j).2 - (v i).2) := by
      linarith
    apply sub_pos.mp
    calc
      latticeHeight (C + 1) (v j) -
          latticeHeight (C + 1) (v i) =
        (C + 1) * ((v j).1 - (v i).1) +
          ((v j).2 - (v i).2) := by
            simp [latticeHeight]
            ring
      _ > 0 := hpositive
  · have hvaluesNe : v i ≠ v j :=
      hinjective.ne (Ne.symm hji)
    have hsecondNe :
        (v i).2 ≠ (v j).2 := by
      intro hs
      apply hvaluesNe
      exact Prod.ext hfirst hs
    have hsecondStrict :
        (v i).2 < (v j).2 :=
      lt_of_le_of_ne hsecond hsecondNe
    simp [latticeHeight, hfirst]
    exact hsecondStrict

/-- The exposed lattice vertex is equivalently a strict maximum of a
continuous real linear functional on all other vertices. -/
theorem exists_strictly_exposed_vertex
    {n : ℕ} [NeZero n]
    (v : Fin n → ℤ × ℤ)
    (hinjective : Function.Injective v) :
    ∃ (i : Fin n) (M : ℤ),
      0 < M ∧
        ∀ j : Fin n, j ≠ i →
          exposingFunctional M (toPlane (v j)) <
            exposingFunctional M (toPlane (v i)) := by
  obtain ⟨i, M, hM, hi⟩ :=
    exists_strict_latticeHeight_min v hinjective
  refine ⟨i, M, hM, ?_⟩
  intro j hji
  have hheight := hi j hji
  rw [exposingFunctional_toPlane,
    exposingFunctional_toPlane]
  exact_mod_cast (neg_lt_neg hheight)

/-- After a cyclic reindexing, a strictly exposed lattice vertex occupies the
distinguished ear position `1`. -/
theorem exists_rotation_strictly_exposed_at_one
    {n : ℕ} [NeZero n]
    (hn : 2 ≤ n)
    (v : Fin n → ℤ × ℤ)
    (hinjective : Function.Injective v) :
    ∃ (k : ℕ) (M : ℤ),
      0 < M ∧
        ∀ j : Fin n,
          j ≠ (⟨1, by omega⟩ : Fin n) →
            exposingFunctional M
                (toPlane (Rotate.rotatePow k v j)) <
              exposingFunctional M
                (toPlane
                  (Rotate.rotatePow k v
                    (⟨1, by omega⟩ : Fin n))) := by
  obtain ⟨i, M, hM, hi⟩ :=
    exists_strictly_exposed_vertex v hinjective
  obtain ⟨k, hk⟩ :=
    Rotate.exists_rotatePow_one_eq hn v i
  have hsource :
      ((finRotate n)^[k])
          (⟨1, by omega⟩ : Fin n) = i := by
    apply hinjective
    simpa only [Rotate.rotatePow_apply] using hk
  have hiterate :
      Function.Injective ((finRotate n)^[k]) :=
    Function.Injective.iterate (finRotate n).injective k
  refine ⟨k, M, hM, ?_⟩
  intro j hj
  rw [Rotate.rotatePow_apply, Rotate.rotatePow_apply,
    hsource]
  apply hi
  intro hji
  apply hj
  exact hiterate (hji.trans hsource.symm)

end Submission.ExtremeVertex
