import Submission.ChainCoordinates

open Set Geometry

namespace Submission.RankGrid

open GridDeformation GridComplex Polytope Polytope.ExposedFace ChainCoordinates

variable {k n : ℕ}

/-- The coordinate face whose nonzero coordinates are the affine ranks of
faces in a fixed chain. -/
def rankFace (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S)) :
    Set (WeightSpace k) :=
  stdSimplex ℝ (Fin (k + 1)) ∩
    {w | ∀ j, (∀ F ∈ c, rankIndex S F ≠ j) → w j = 0}

theorem mem_rankFace_iff (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : WeightSpace k) :
    w ∈ rankFace S c ↔
      w ∈ stdSimplex ℝ (Fin (k + 1)) ∧
        ∀ j, (∀ F ∈ c, rankIndex S F ≠ j) → w j = 0 :=
  Iff.rfl

theorem rankWeights_mem_rankFace (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) (w : stdSimplex ℝ c) :
    (rankWeights S c w : WeightSpace k) ∈ rankFace S c := by
  refine ⟨(rankWeights S c w).2, ?_⟩
  intro j hj
  apply rankWeights_eq_zero_of_not_rank S c w j
  intro F
  exact hj F.1 F.2

theorem convex_rankFace (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) : Convex ℝ (rankFace S c) := by
  intro x hx y hy a b ha hb hab
  refine ⟨(convex_stdSimplex ℝ (Fin (k + 1))) hx.1 hy.1 ha hb hab, ?_⟩
  intro j hj
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, hx.2 j hj, hy.2 j hj, smul_zero,
    smul_zero, add_zero]

theorem isExtreme_rankFace (S : Finset (Fin k → ℝ))
    (c : Finset (ExposedFace S)) :
    IsExtreme ℝ (stdSimplex ℝ (Fin (k + 1))) (rankFace S c) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hxseg
  refine ⟨hx, ?_⟩
  intro j hj
  have hzj : z j = 0 := hz.2 j hj
  obtain ⟨a, b, ha, hb, hab, hcombo⟩ := hxseg
  have hcoord := congrArg (fun w : WeightSpace k => w j) hcombo
  change a * x j + b * y j = z j at hcoord
  have hxj := hx.1 j
  have hyj := hy.1 j
  nlinarith

theorem isExtreme_weightCell_inter_rankFace
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (b : GridCell k n) :
    IsExtreme ℝ (weightCell b) (weightCell b ∩ rankFace S c) := by
  refine ⟨inter_subset_left, ?_⟩
  intro x hx y hy z hz hxseg
  have hxstd : x ∈ stdSimplex ℝ (Fin (k + 1)) :=
    (mem_weightCell_iff b x).mp hx |>.1
  have hystd : y ∈ stdSimplex ℝ (Fin (k + 1)) :=
    (mem_weightCell_iff b y).mp hy |>.1
  have hxrank : x ∈ rankFace S c :=
    (isExtreme_rankFace S c).left_mem_of_mem_openSegment hxstd hystd hz.2 hxseg
  exact ⟨hx, hxrank⟩

/-- The subcomplex of the global grid triangulation carried by a chain's
rank-supported coordinate face. -/
noncomputable def rankSubcomplex (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S)) :
    SimplicialComplex ℝ (WeightSpace k) where
  faces := {s | s ∈ (gridComplex hn).faces ∧ (s : Set (WeightSpace k)) ⊆ rankFace S c}
  isRelLowerSet_faces := by
    intro s hs
    refine ⟨(gridComplex hn).nonempty_of_mem_faces hs.1, ?_⟩
    intro t hts ht
    refine ⟨(gridComplex hn).down_closed hs.1 hts ht, ?_⟩
    intro x hx
    exact hs.2 (Finset.mem_coe.mpr (hts (Finset.mem_coe.mp hx)))
  indep := by
    intro s hs
    exact (gridComplex hn).indep hs.1
  inter_subset_convexHull := by
    intro s t hs ht
    exact (gridComplex hn).inter_subset_convexHull hs.1 ht.1

@[simp]
theorem mem_rankSubcomplex_faces (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S))
    (s : Finset (WeightSpace k)) :
    s ∈ (rankSubcomplex hn S c).faces ↔
      s ∈ (gridComplex hn).faces ∧ (s : Set (WeightSpace k)) ⊆ rankFace S c :=
  Iff.rfl

theorem rankSubcomplex_faces_finite (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S)) :
    (rankSubcomplex hn S c).faces.Finite :=
  (gridComplex_faces_finite hn).subset fun _ hs => hs.1

@[simp]
theorem rankSubcomplex_space (hn : 0 < n)
    (S : Finset (Fin k → ℝ)) (c : Finset (ExposedFace S)) :
    (rankSubcomplex hn S c).space = rankFace S c := by
  apply Subset.antisymm
  · intro x hx
    rw [SimplicialComplex.mem_space_iff] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    have hs' := (mem_rankSubcomplex_faces hn S c s).mp hs
    exact convexHull_min hs'.2 (convex_rankFace S c) hxs
  · intro x hx
    let w : stdSimplex ℝ (Fin (k + 1)) := ⟨x, hx.1⟩
    obtain ⟨b, hwb⟩ := exists_mem_gridCell hn w
    have hxcell : x ∈ weightCell b := (mem_weightCell_coe_iff b w).mpr hwb
    let H : ExposedFace (cellVertices hn b) :=
      { carrier := weightCell b ∩ rankFace S c
        nonempty := ⟨x, hxcell, hx⟩
        convex_carrier := (convex_weightCell b).inter (convex_rankFace S c)
        extreme_carrier := by
          rw [convexHull_cellVertices hn b]
          exact isExtreme_weightCell_inter_rankFace S c b }
    have hxlocal : x ∈ (barycentricComplex (cellVertices hn b)).space := by
      rw [barycentricComplex_space, convexHull_cellVertices hn b]
      exact hxcell
    rw [SimplicialComplex.mem_space_iff] at hxlocal
    obtain ⟨s, hs, hxs⟩ := hxlocal
    obtain ⟨q, hq, rfl⟩ := hs
    let sH := chainVerticesInFace (cellVertices hn b) H q
    have hxrestricted : x ∈ convexHull ℝ (sH : Set (WeightSpace k)) := by
      rw [← convexHull_chainVertices_inter_face (cellVertices hn b) H q]
      exact ⟨hxs, ⟨hxcell, hx⟩⟩
    have hsHne : sH.Nonempty := convexHull_nonempty_iff.mp ⟨x, hxrestricted⟩
    have hsHcell : sH ∈ (barycentricComplex (cellVertices hn b)).faces := by
      exact (barycentricComplex (cellVertices hn b)).down_closed
        ⟨q, hq, rfl⟩
        (by
          intro z hz
          exact (mem_chainVerticesInFace (cellVertices hn b) H q z).mp hz |>.1)
        hsHne
    have hsHgrid : sH ∈ (gridComplex hn).faces :=
      (mem_gridComplex_faces hn sH).mpr ⟨b, hsHcell⟩
    have hsHrank : (sH : Set (WeightSpace k)) ⊆ rankFace S c := by
      intro z hz
      have hzH : z ∈ H.carrier :=
        (mem_chainVerticesInFace (cellVertices hn b) H q z).mp
          (Finset.mem_coe.mp hz) |>.2
      exact hzH.2
    rw [SimplicialComplex.mem_space_iff]
    exact ⟨sH, (mem_rankSubcomplex_faces hn S c sH).mpr ⟨hsHgrid, hsHrank⟩,
      hxrestricted⟩

end Submission.RankGrid
