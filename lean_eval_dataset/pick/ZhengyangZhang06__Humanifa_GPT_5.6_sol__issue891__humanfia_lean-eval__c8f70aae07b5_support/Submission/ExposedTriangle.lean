import Submission.ExtremeVertex

open LeanEval.Geometry.PicksTheorem

namespace Submission.ExposedTriangle

/-- If the middle of three points is strictly higher than both endpoints for
a linear functional, and the two incident segments meet only there, the
three points are affinely independent. -/
theorem affineIndependent_of_middle_strictMax
    (a p c : ℝ × ℝ)
    (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (ha : L a < L p)
    (hc : L c < L p)
    (hinter :
      affineSegment ℝ a p ∩
          affineSegment ℝ p c =
        {p}) :
    AffineIndependent ℝ ![a, p, c] := by
  rw [affineIndependent_iff_not_collinear]
  intro hcollinear
  have hrange :
      Set.range ![a, p, c] =
        ({a, p, c} : Set (ℝ × ℝ)) := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i <;> simp
    · intro hx
      simp only [Set.mem_insert_iff,
        Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
      · exact ⟨2, rfl⟩
  rw [hrange] at hcollinear
  rcases hcollinear.wbtw_or_wbtw_or_wbtw with
    hbetween | hbetween | hbetween
  · have hhalfspace :
        Convex ℝ {x : ℝ × ℝ | L x < L p} :=
      convex_halfSpace_lt L.toLinearMap.isLinear (L p)
    have hpp : L p < L p :=
      hhalfspace.segment_subset ha hc hbetween.mem_segment
    exact (lt_irrefl _ hpp)
  · have hcInter :
        c ∈
          affineSegment ℝ a p ∩
            affineSegment ℝ p c :=
      ⟨hbetween.symm,
        right_mem_affineSegment ℝ _ _⟩
    rw [hinter] at hcInter
    have hcp : c = p := by
      simpa using hcInter
    exact (lt_irrefl (L p)) (hcp ▸ hc)
  · have haInter :
        a ∈
          affineSegment ℝ a p ∩
            affineSegment ℝ p c :=
      ⟨left_mem_affineSegment ℝ _ _,
        hbetween.symm⟩
    rw [hinter] at haInter
    have hap : a = p := by
      simpa using haInter
    exact (lt_irrefl (L p)) (hap ▸ ha)

/-- Strict exposure at the distinguished vertex makes its two incident
neighbors into a nondegenerate triangle. -/
theorem earTriangle_simple_of_strictlyExposed
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (L : (ℝ × ℝ) →L[ℝ] ℝ)
    (hvertices :
      ∀ j : Fin (n + 1),
        j ≠ (⟨1, by omega⟩ : Fin (n + 1)) →
          L (toPlane (v j)) <
            L
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))) :
    IsSimple
      (latPoly (EarRemoval.earTriangle hn v)) := by
  have hrotateZero :
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
  have hrotateOne :
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
  have hinter :
      affineSegment ℝ
            (toPlane (v 0))
            (toPlane
              (v (⟨1, by omega⟩ :
                Fin (n + 1)))) ∩
          affineSegment ℝ
            (toPlane
              (v (⟨1, by omega⟩ :
                Fin (n + 1))))
            (toPlane
              (v (⟨2, by omega⟩ :
                Fin (n + 1)))) =
        {toPlane
          (v (⟨1, by omega⟩ :
            Fin (n + 1)))} := by
    simpa only [Polygon.edgeSet, latPoly,
      hrotateZero, hrotateOne] using
      hsimple.2.2 (0 : Fin (n + 1))
  apply Triangle.isSimple_of_affineIndependent
  have hverticesEq :
      (latPoly
        (EarRemoval.earTriangle hn v)).vertices =
        ![toPlane (v 0),
          toPlane
            (v (⟨1, by omega⟩ : Fin (n + 1))),
          toPlane
            (v (⟨2, by omega⟩ : Fin (n + 1)))] := by
    funext i
    fin_cases i <;> rfl
  rw [hverticesEq]
  apply affineIndependent_of_middle_strictMax
  · exact
      hvertices 0 (by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_zero] at hval
        omega)
  · exact
      hvertices ⟨2, by omega⟩ (by
        intro h
        have hval := congrArg Fin.val h
        simp only at hval
        omega)
  · exact hinter

end Submission.ExposedTriangle
