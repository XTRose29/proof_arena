import Submission.VisibleOutside

open LeanEval.Geometry.PicksTheorem

namespace Submission.VisibleBoundary

/-- Membership in the front-child boundary is membership in either its
closing chord or one inherited parent edge. -/
theorem mem_frontBoundary_iff
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val)
    (x : ℝ × ℝ) :
    x ∈
        (latPoly
          (FrontSubpolygon.vertices v q)).boundary
            (R := ℝ) ↔
      x ∈
          segment ℝ
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))
            (toPlane (v q)) ∨
        ∃ i : Fin q.val,
          i.val + 1 < q.val ∧
            x ∈
              (latPoly v).edgeSet ℝ
                (FrontSubpolygon.frontIndex q i) := by
  constructor
  · intro hx
    rw [Polygon.boundary] at hx
    rcases Set.mem_iUnion.mp hx with
      ⟨i, hxEdge⟩
    by_cases hi : i.val + 1 < q.val
    · exact
        Or.inr
          ⟨i, hi, by
            rwa [FrontSubpolygon.edge_of_lt
              v q i hi] at hxEdge⟩
    · left
      have hilast :
          i =
            (⟨q.val - 1, by omega⟩ :
              Fin q.val) := by
        apply Fin.ext
        change i.val = q.val - 1
        omega
      rw [hilast, FrontSubpolygon.edge_last
        v q (by omega)] at hxEdge
      exact hxEdge
  · rintro (hxChord | ⟨i, hi, hxEdge⟩)
    · rw [Polygon.boundary]
      refine
        Set.mem_iUnion.mpr
          ⟨(⟨q.val - 1, by omega⟩ :
            Fin q.val), ?_⟩
      rwa [FrontSubpolygon.edge_last
        v q (by omega)]
    · rw [Polygon.boundary]
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rwa [FrontSubpolygon.edge_of_lt
        v q i hi]

/-- Membership in the complementary-child boundary has the analogous
description. -/
theorem mem_backBoundary_iff
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val)
    (x : ℝ × ℝ) :
    x ∈
        (latPoly
          (BackSubpolygon.vertices v q hq)).boundary
            (R := ℝ) ↔
      x ∈
          segment ℝ
            (toPlane
              (v
                (⟨1, by omega⟩ :
                  Fin (n + 1))))
            (toPlane (v q)) ∨
        ∃ i : Fin (BackSubpolygon.size q),
          i.val + 1 < BackSubpolygon.size q ∧
            x ∈
              (latPoly v).edgeSet ℝ
                (BackSubpolygon.parentIndex q i) := by
  constructor
  · intro hx
    rw [Polygon.boundary] at hx
    rcases Set.mem_iUnion.mp hx with
      ⟨i, hxEdge⟩
    by_cases hi :
        i.val + 1 < BackSubpolygon.size q
    · exact
        Or.inr
          ⟨i, hi, by
            rwa [BackSubpolygon.edge_of_lt
              v q hq i hi] at hxEdge⟩
    · left
      have hilast :
          i =
            (⟨BackSubpolygon.size q - 1, by
              have :=
                BackSubpolygon.three_le_size q hq
              omega⟩ :
              Fin (BackSubpolygon.size q)) := by
        apply Fin.ext
        change i.val = BackSubpolygon.size q - 1
        have :=
          BackSubpolygon.three_le_size q hq
        omega
      rw [hilast, BackSubpolygon.edge_last
        v q hq] at hxEdge
      exact hxEdge
  · rintro (hxChord | ⟨i, hi, hxEdge⟩)
    · rw [Polygon.boundary]
      refine
        Set.mem_iUnion.mpr
          ⟨(⟨BackSubpolygon.size q - 1, by
            have :=
              BackSubpolygon.three_le_size q hq
            omega⟩ :
            Fin (BackSubpolygon.size q)), ?_⟩
      rwa [BackSubpolygon.edge_last
        v q hq]
    · rw [Polygon.boundary]
      refine Set.mem_iUnion.mpr ⟨i, ?_⟩
      rwa [BackSubpolygon.edge_of_lt
        v q hq i hi]

/-- The two child boundaries are obtained from the parent boundary by adding
their common closing chord. -/
theorem childBoundaries_union
    {n : ℕ}
    (v : Fin (n + 1) → ℤ × ℤ)
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    (latPoly
          (FrontSubpolygon.vertices v q)).boundary
          (R := ℝ) ∪
        (latPoly
          (BackSubpolygon.vertices v q hq)).boundary
          (R := ℝ) =
      (latPoly v).boundary (R := ℝ) ∪
        segment ℝ
          (toPlane
            (v
              (⟨1, by omega⟩ :
                Fin (n + 1))))
          (toPlane (v q)) := by
  ext x
  constructor
  · rintro (hxFront | hxBack)
    · rcases
          (mem_frontBoundary_iff v q hq x).mp hxFront with
        hxChord | ⟨i, hi, hxEdge⟩
      · exact Or.inr hxChord
      · left
        rw [Polygon.boundary]
        exact
          Set.mem_iUnion.mpr
            ⟨FrontSubpolygon.frontIndex q i, hxEdge⟩
    · rcases
          (mem_backBoundary_iff v q hq x).mp hxBack with
        hxChord | ⟨i, hi, hxEdge⟩
      · exact Or.inr hxChord
      · left
        rw [Polygon.boundary]
        exact
          Set.mem_iUnion.mpr
            ⟨BackSubpolygon.parentIndex q i, hxEdge⟩
  · rintro (hxParent | hxChord)
    · rw [Polygon.boundary] at hxParent
      obtain ⟨i, hxEdge⟩ := Set.mem_iUnion.mp hxParent
      by_cases hfront : 1 ≤ i.val ∧ i.val < q.val
      · let j : Fin q.val :=
          ⟨i.val - 1, by omega⟩
        have hj : j.val + 1 < q.val := by
          dsimp [j]
          omega
        have hindex :
            FrontSubpolygon.frontIndex q j = i := by
          apply Fin.ext
          dsimp [FrontSubpolygon.frontIndex, j]
          omega
        left
        apply
          (mem_frontBoundary_iff v q hq x).mpr
        right
        refine ⟨j, hj, ?_⟩
        rwa [hindex]
      · right
        apply
          (mem_backBoundary_iff v q hq x).mpr
        right
        by_cases hizero : i.val = 0
        · let j : Fin (BackSubpolygon.size q) :=
            ⟨n + 1 - q.val, by
              dsimp [BackSubpolygon.size]
              omega⟩
          have hj :
              j.val + 1 < BackSubpolygon.size q := by
            dsimp [j, BackSubpolygon.size]
            omega
          have hindex :
              BackSubpolygon.parentIndex q j = i := by
            apply Fin.ext
            simp [BackSubpolygon.parentIndex, j, hizero]
          refine ⟨j, hj, ?_⟩
          rwa [hindex]
        · have hiq : q.val ≤ i.val := by
            omega
          let j : Fin (BackSubpolygon.size q) :=
            ⟨i.val - q.val, by
              dsimp [BackSubpolygon.size]
              omega⟩
          have hj :
              j.val + 1 < BackSubpolygon.size q := by
            dsimp [j, BackSubpolygon.size]
            omega
          have hindex :
              BackSubpolygon.parentIndex q j = i := by
            apply Fin.ext
            simp [BackSubpolygon.parentIndex, j]
            rw [Nat.mod_eq_of_lt] <;> omega
          refine ⟨j, hj, ?_⟩
          rwa [hindex]
    · left
      exact
        (mem_frontBoundary_iff v q hq x).mpr
          (Or.inl hxChord)

private theorem back_parentIndex_zero_or_ge
    {n : ℕ}
    (q : Fin (n + 1))
    (i : Fin (BackSubpolygon.size q))
    (hi : i.val + 1 < BackSubpolygon.size q) :
    (BackSubpolygon.parentIndex q i).val = 0 ∨
      q.val ≤
        (BackSubpolygon.parentIndex q i).val := by
  have hsum :
      q.val + i.val ≤ n + 1 := by
    dsimp [BackSubpolygon.size] at hi
    omega
  by_cases heq : q.val + i.val = n + 1
  · left
    simp [BackSubpolygon.parentIndex, heq]
  · right
    rw [BackSubpolygon.parentIndex_val,
      Nat.mod_eq_of_lt (by omega)]
    omega

/-- The two child polygonal boundaries meet exactly in their common clean
chord. -/
theorem childBoundaries_inter
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin (n + 1) → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v))
    (q : Fin (n + 1))
    (hq : 3 ≤ q.val) :
    (latPoly
          (FrontSubpolygon.vertices v q)).boundary
          (R := ℝ) ∩
        (latPoly
          (BackSubpolygon.vertices v q hq)).boundary
          (R := ℝ) =
      segment ℝ
        (toPlane
          (v
            (⟨1, by omega⟩ :
              Fin (n + 1))))
        (toPlane (v q)) := by
  let chord :=
    segment ℝ
      (toPlane
        (v
          (⟨1, by omega⟩ :
            Fin (n + 1))))
      (toPlane (v q))
  apply Set.Subset.antisymm
  · rintro x ⟨hxFront, hxBack⟩
    by_cases hxChord : x ∈ chord
    · exact hxChord
    · have hxFrontData :=
        (mem_frontBoundary_iff
          v q hq x).mp hxFront
      have hxBackData :=
        (mem_backBoundary_iff
          v q hq x).mp hxBack
      rcases hxFrontData with
        hxFrontChord | ⟨i, hi, hxFrontEdge⟩
      · exact False.elim <|
          hxChord (by simpa [chord] using hxFrontChord)
      rcases hxBackData with
        hxBackChord | ⟨j, hj, hxBackEdge⟩
      · exact False.elim <|
          hxChord (by simpa [chord] using hxBackChord)
      let fi : Fin (n + 1) :=
        FrontSubpolygon.frontIndex q i
      let bj : Fin (n + 1) :=
        BackSubpolygon.parentIndex q j
      have hfiLower : 1 ≤ fi.val := by
        dsimp [fi, FrontSubpolygon.frontIndex]
        omega
      have hfiUpper : fi.val < q.val := by
        dsimp [fi, FrontSubpolygon.frontIndex]
        omega
      have hbj :
          bj.val = 0 ∨ q.val ≤ bj.val := by
        simpa [bj] using
          back_parentIndex_zero_or_ge q j hj
      have hfibj : fi ≠ bj := by
        intro h
        have hval := congrArg Fin.val h
        rcases hbj with hbjZero | hbjGe
        · omega
        · omega
      by_cases hadj : Adjacent fi bj
      · rcases hadj with hforward | hbackward
        · have hfiNotLast :
              fi ≠ Fin.last n := by
            intro h
            have hval := congrArg Fin.val h
            dsimp [fi, FrontSubpolygon.frontIndex] at hval
            omega
          have hrotateVal :
              (finRotate (n + 1) fi).val =
                fi.val + 1 := by
            exact coe_finRotate_of_ne_last hfiNotLast
          have hbjEq : bj = q := by
            apply Fin.ext
            have hval := congrArg Fin.val hforward
            rw [hrotateVal] at hval
            rcases hbj with hbjZero | hbjGe
            · omega
            · omega
          have hxInter :
              x ∈
                (latPoly v).edgeSet ℝ fi ∩
                  (latPoly v).edgeSet ℝ
                    (finRotate (n + 1) fi) := by
            rw [hforward]
            exact ⟨hxFrontEdge, hxBackEdge⟩
          rw [hsimple.2.2 fi] at hxInter
          have hxq :
              x = toPlane (v q) := by
            rw [hforward, hbjEq] at hxInter
            simpa [latPoly] using hxInter
          simpa [chord, hxq] using
            right_mem_segment ℝ
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))
              (toPlane (v q))
        · have hbjEqZero : bj = 0 := by
            apply Fin.ext
            rcases hbj with hbjZero | hbjGe
            · exact hbjZero
            · by_cases hbjLast : bj = Fin.last n
              · rw [hbjLast, finRotate_last] at hbackward
                have hval := congrArg Fin.val hbackward
                simp only [Fin.val_zero] at hval
                omega
              · have hrotateVal :
                    (finRotate (n + 1) bj).val =
                      bj.val + 1 :=
                  coe_finRotate_of_ne_last hbjLast
                have hval := congrArg Fin.val hbackward
                rw [hrotateVal] at hval
                omega
          have hfiEqOne :
              fi =
                (⟨1, by omega⟩ :
                  Fin (n + 1)) := by
            rw [hbjEqZero,
              CleanEar.finRotate_zero hn] at hbackward
            exact hbackward.symm
          have hxInter :
              x ∈
                (latPoly v).edgeSet ℝ bj ∩
                  (latPoly v).edgeSet ℝ
                    (finRotate (n + 1) bj) := by
            rw [hbackward]
            exact ⟨hxBackEdge, hxFrontEdge⟩
          rw [hsimple.2.2 bj] at hxInter
          have hxTip :
              x =
                toPlane
                  (v
                    (⟨1, by omega⟩ :
                      Fin (n + 1))) := by
            rw [hbackward, hfiEqOne] at hxInter
            simpa [latPoly] using hxInter
          simpa [chord, hxTip] using
            left_mem_segment ℝ
              (toPlane
                (v
                  (⟨1, by omega⟩ :
                    Fin (n + 1))))
              (toPlane (v q))
      · exact False.elim <|
          Set.disjoint_left.mp
            (hsimple.2.1 fi bj hfibj hadj)
            hxFrontEdge hxBackEdge
  · intro x hxChord
    constructor
    · exact
        (mem_frontBoundary_iff
          v q hq x).mpr
            (Or.inl (by simpa [chord] using hxChord))
    · exact
        (mem_backBoundary_iff
          v q hq x).mpr
            (Or.inl (by simpa [chord] using hxChord))

end Submission.VisibleBoundary
