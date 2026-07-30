import Submission.GridDeformation
import Submission.Polytope

open Set Geometry

namespace Submission.GridComplex

open GridDeformation Polytope
open Polytope.ExposedFace

abbrev WeightSpace (m : ℕ) := Fin (m + 1) → ℝ

noncomputable def localComplex {m n : ℕ} (hn : 0 < n) (c : GridCell m n) :
    SimplicialComplex ℝ (WeightSpace m) :=
  barycentricComplex (cellVertices hn c)

theorem convexHull_chainVertices_subset_weightCell {m n : ℕ} (hn : 0 < n)
    (c : GridCell m n) (q : Finset (ExposedFace (cellVertices hn c))) :
    convexHull ℝ (chainVertices (cellVertices hn c) q : Set (WeightSpace m)) ⊆
      weightCell c := by
  apply convexHull_min
  · intro x hx
    obtain ⟨F, _hFq, rfl⟩ :=
      (mem_chainVertices (cellVertices hn c) q x).mp (Finset.mem_coe.mp hx)
    have hcenter := F.extreme_carrier.subset (F.center_mem (cellVertices hn c))
    rwa [convexHull_cellVertices hn c] at hcenter
  · exact convex_weightCell c

theorem faceVertices_cellIntersection_eq {m n : ℕ} (hn : 0 < n)
    (c d : GridCell m n) :
    faceVertices (cellVertices hn c) (weightCell c ∩ weightCell d) =
      faceVertices (cellVertices hn d) (weightCell c ∩ weightCell d) := by
  classical
  let H := weightCell c ∩ weightCell d
  have hHC : IsExtreme ℝ (weightCell c) H :=
    (isExposed_inter_weightCell_left hn c d).isExtreme
  have hHD : IsExtreme ℝ (weightCell d) H :=
    (isExposed_inter_weightCell_right hn c d).isExtreme
  ext x
  rw [mem_faceVertices, mem_faceVertices]
  have hcvert : x ∈ cellVertices hn c ↔ x ∈ (weightCell c).extremePoints ℝ := by
    change x ∈ (cellVertices hn c : Set (WeightSpace m)) ↔ _
    rw [coe_cellVertices]
  have hdvert : x ∈ cellVertices hn d ↔ x ∈ (weightCell d).extremePoints ℝ := by
    change x ∈ (cellVertices hn d : Set (WeightSpace m)) ↔ _
    rw [coe_cellVertices]
  rw [hcvert, hdvert]
  constructor
  · rintro ⟨hxC, hxH⟩
    have hxextH : x ∈ H.extremePoints ℝ := by
      rw [hHC.extremePoints_eq]
      exact ⟨hxH, hxC⟩
    rw [hHD.extremePoints_eq] at hxextH
    exact ⟨hxextH.2, hxextH.1⟩
  · rintro ⟨hxD, hxH⟩
    have hxextH : x ∈ H.extremePoints ℝ := by
      rw [hHD.extremePoints_eq]
      exact ⟨hxH, hxD⟩
    rw [hHC.extremePoints_eq] at hxextH
    exact ⟨hxextH.2, hxextH.1⟩

theorem cross_inter_subset {m n : ℕ} (hn : 0 < n)
    (c d : GridCell m n)
    {s t : Finset (WeightSpace m)}
    (hs : s ∈ (localComplex hn c).faces)
    (ht : t ∈ (localComplex hn d).faces) :
    convexHull ℝ (s : Set (WeightSpace m)) ∩ convexHull ℝ (t : Set (WeightSpace m)) ⊆
      convexHull ℝ (s ∩ t : Set (WeightSpace m)) := by
  obtain ⟨cs, hcs, rfl⟩ := hs
  obtain ⟨ct, hct, rfl⟩ := ht
  let S := cellVertices hn c
  let T := cellVertices hn d
  let H : Set (WeightSpace m) := weightCell c ∩ weightCell d
  by_cases hHne : H.Nonempty
  · let HS : ExposedFace S :=
      { carrier := H
        nonempty := hHne
        convex_carrier := (convex_weightCell c).inter (convex_weightCell d)
        extreme_carrier := by
          dsimp [S, H]
          rw [convexHull_cellVertices hn c]
          exact (isExposed_inter_weightCell_left hn c d).isExtreme }
    let HT : ExposedFace T :=
      { carrier := H
        nonempty := hHne
        convex_carrier := (convex_weightCell c).inter (convex_weightCell d)
        extreme_carrier := by
          dsimp [T, H]
          rw [convexHull_cellVertices hn d]
          exact (isExposed_inter_weightCell_right hn c d).isExtreme }
    let sH := chainVerticesInFace S HS cs
    let tH := chainVerticesInFace T HT ct
    have hgen : faceVertices S HS.carrier = faceVertices T HT.carrier := by
      dsimp [S, T, HS, HT, H]
      exact faceVertices_cellIntersection_eq hn c d
    intro x hx
    have hscell := convexHull_chainVertices_subset_weightCell hn c cs hx.1
    have htcell := convexHull_chainVertices_subset_weightCell hn d ct hx.2
    have hxH : x ∈ H := ⟨hscell, htcell⟩
    have hxsH : x ∈ convexHull ℝ (sH : Set (WeightSpace m)) := by
      rw [← convexHull_chainVertices_inter_face S HS cs]
      exact ⟨hx.1, hxH⟩
    have hxtH : x ∈ convexHull ℝ (tH : Set (WeightSpace m)) := by
      rw [← convexHull_chainVertices_inter_face T HT ct]
      exact ⟨hx.2, hxH⟩
    have hsHne : sH.Nonempty := by
      exact convexHull_nonempty_iff.mp ⟨x, hxsH⟩
    have htHne : tH.Nonempty := by
      exact convexHull_nonempty_iff.mp ⟨x, hxtH⟩
    have hsHface : sH ∈ (barycentricComplex (faceVertices S HS.carrier)).faces :=
      chainVerticesInFace_mem_barycentricComplex_faces S HS cs hcs hsHne
    have htHface : tH ∈ (barycentricComplex (faceVertices S HS.carrier)).faces := by
      have h := chainVerticesInFace_mem_barycentricComplex_faces T HT ct hct htHne
      rwa [hgen] at hsHface ⊢
    have hsmall := (barycentricComplex (faceVertices S HS.carrier)).inter_subset_convexHull
      hsHface htHface ⟨hxsH, hxtH⟩
    have hinter : sH ∩ tH = chainVertices S cs ∩ chainVertices T ct := by
      classical
      ext y
      simp only [Finset.mem_inter, sH, tH, mem_chainVerticesInFace]
      constructor
      · rintro ⟨⟨hys, _hyH⟩, hyt, _⟩
        exact ⟨hys, hyt⟩
      · rintro ⟨hys, hyt⟩
        have hyC : y ∈ weightCell c :=
          convexHull_chainVertices_subset_weightCell hn c cs
            (subset_convexHull ℝ _ (Finset.mem_coe.mpr hys))
        have hyD : y ∈ weightCell d :=
          convexHull_chainVertices_subset_weightCell hn d ct
            (subset_convexHull ℝ _ (Finset.mem_coe.mpr hyt))
        exact ⟨⟨hys, hyC, hyD⟩, hyt, hyC, hyD⟩
    rw [← Finset.coe_inter, hinter, Finset.coe_inter] at hsmall
    exact hsmall
  · intro x hx
    have hscell := convexHull_chainVertices_subset_weightCell hn c cs hx.1
    have htcell := convexHull_chainVertices_subset_weightCell hn d ct hx.2
    exact (hHne ⟨x, hscell, htcell⟩).elim

/-- The compatible union of the barycentric subdivisions of all uniform
prefix-grid cells. -/
noncomputable def gridComplex {m n : ℕ} (hn : 0 < n) :
    SimplicialComplex ℝ (WeightSpace m) where
  faces := ⋃ c : GridCell m n, (localComplex hn c).faces
  isRelLowerSet_faces := by
    intro s hs
    obtain ⟨c, hsc⟩ := Set.mem_iUnion.mp hs
    have hrel := (localComplex hn c).isRelLowerSet_faces hsc
    refine ⟨hrel.1, ?_⟩
    intro t hts ht
    exact Set.mem_iUnion.mpr ⟨c, hrel.2 hts ht⟩
  indep := by
    intro s hs
    obtain ⟨c, hsc⟩ := Set.mem_iUnion.mp hs
    exact (localComplex hn c).indep hsc
  inter_subset_convexHull := by
    intro s t hs ht
    obtain ⟨c, hsc⟩ := Set.mem_iUnion.mp hs
    obtain ⟨d, htd⟩ := Set.mem_iUnion.mp ht
    exact cross_inter_subset hn c d hsc htd

@[simp]
theorem mem_gridComplex_faces {m n : ℕ} (hn : 0 < n) (s : Finset (WeightSpace m)) :
    s ∈ (gridComplex hn).faces ↔ ∃ c : GridCell m n, s ∈ (localComplex hn c).faces := by
  simp [gridComplex]

theorem gridComplex_faces_finite {m n : ℕ} (hn : 0 < n) :
    (gridComplex hn : SimplicialComplex ℝ (WeightSpace m)).faces.Finite := by
  rw [gridComplex]
  exact Set.finite_iUnion fun c => barycentricComplex_faces_finite (cellVertices hn c)

@[simp]
theorem gridComplex_space {m n : ℕ} (hn : 0 < n) :
    (gridComplex hn : SimplicialComplex ℝ (WeightSpace m)).space =
      stdSimplex ℝ (Fin (m + 1)) := by
  apply Subset.antisymm
  · intro x hx
    rw [SimplicialComplex.mem_space_iff] at hx
    obtain ⟨s, hs, hxs⟩ := hx
    obtain ⟨c, hsc⟩ := (mem_gridComplex_faces hn s).mp hs
    have hxcell : x ∈ weightCell c := by
      rw [← convexHull_cellVertices hn c, ← barycentricComplex_space]
      exact (localComplex hn c).convexHull_subset_space hsc hxs
    exact (mem_weightCell_iff c x).mp hxcell |>.1
  · intro x hx
    let w : stdSimplex ℝ (Fin (m + 1)) := ⟨x, hx⟩
    obtain ⟨c, hwc⟩ := exists_mem_gridCell hn w
    have hxcell : x ∈ weightCell c := (mem_weightCell_coe_iff c w).mpr hwc
    have hxlocal : x ∈ (localComplex hn c).space := by
      rw [localComplex, barycentricComplex_space, convexHull_cellVertices hn c]
      exact hxcell
    rw [SimplicialComplex.mem_space_iff] at hxlocal ⊢
    obtain ⟨s, hs, hxs⟩ := hxlocal
    exact ⟨s, (mem_gridComplex_faces hn s).mpr ⟨c, hs⟩, hxs⟩

end Submission.GridComplex
