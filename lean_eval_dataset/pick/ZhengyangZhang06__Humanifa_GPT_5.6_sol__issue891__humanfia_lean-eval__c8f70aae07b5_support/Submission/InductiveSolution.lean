import Submission.CleanDescent
import Submission.EmptyDisk
import Submission.VisibleDecomposition

open LeanEval.Geometry.PicksTheorem
open MeasureTheory

namespace Submission.InductiveSolution

/-- The two pieces of information propagated through clean-diagonal descent:
disk-like filled-region topology and a checked arithmetic dissection. -/
structure Certificate {n : ℕ}
    (v : Fin n → ℤ × ℤ) : Type where
  disk : DiskData.Holds v
  decomposition : Dissection.PickDecomposition v

/-- Disk data transports back across cyclic reindexing. -/
theorem unrotateDisk
    {n : ℕ} (k : ℕ)
    (v : Fin n → ℤ × ℤ)
    (rotated : DiskData.Holds (Rotate.rotatePow k v)) :
    DiskData.Holds v := by
  have hboundary :=
    Rotate.boundary_rotatePow k v
  refine
    { regular := ?_
      interiorPreconnected := ?_
      boundary_eq_frontier := ?_
      edgeAttachable := ?_ }
  · simpa [DiskData.region, hboundary] using
      rotated.regular
  · simpa [DiskData.region, hboundary] using
      rotated.interiorPreconnected
  · simpa [DiskData.region, hboundary] using
      rotated.boundary_eq_frontier
  · intro i
    obtain ⟨j, hj⟩ :=
      (finRotate n).surjective.iterate k i
    have h := rotated.edgeAttachable j
    rw [Rotate.edge_rotatePow k v j, hj] at h
    simpa [DiskData.region, hboundary] using h

/-- Every simple lattice polygon has both the disk data used by the gluing
argument and a checked Pick dissection. -/
theorem exists_certificate
    {m : ℕ} (hm : 3 ≤ m)
    (v : Fin m → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    Nonempty (Certificate v) := by
  apply
    CleanDescent.all_of_reduction_steps
      (P := fun {_} w => Nonempty (Certificate w))
  · intro w hw
    exact
      ⟨{ disk := DiskData.triangle w hw
         decomposition :=
           Dissection.PickDecomposition.triangle w hw }⟩
  · intro r k w hrotated
    obtain ⟨rotated⟩ := hrotated
    exact
      ⟨{ disk := unrotateDisk k w rotated.disk
         decomposition :=
           Rotate.unrotateDecomposition
             k w rotated.decomposition }⟩
  · intro n hn w hw M hvertices htriangle hempty houter
      hreduced
    obtain ⟨reduced⟩ := hreduced
    have hseam :
        CleanEar.diagonal hn w \
            (latPoly w).boundary (R := ℝ) ⊆
          interior
            (FilledRegion.fill
                  ((latPoly
                    (EarRemoval.earTriangle hn w)).boundary
                      (R := ℝ)) ∪
              FilledRegion.fill
                ((latPoly
                  (EarRemoval.removeSecond w)).boundary
                    (R := ℝ))) :=
      EmptyEarSeam.diagonal_sdiff_parent_subset_interior
        hn w hw M hvertices htriangle hempty houter
          reduced.disk.regular
    have hcompl :
        IsPreconnected
          (FilledRegion.fill
                ((latPoly
                  (EarRemoval.earTriangle hn w)).boundary
                    (R := ℝ)) ∪
            FilledRegion.fill
              ((latPoly
                (EarRemoval.removeSecond w)).boundary
                  (R := ℝ)))ᶜ :=
      EmptyEarExterior.childFill_compl_isPreconnected
        hn w hw M hvertices htriangle hempty
    have hcore :
        CleanEar.CoreIsEarAtOne hn w :=
      EmptyEar.coreIsEarAtOne_of_vertexEmpty_of_local
        hn w hw M hvertices htriangle hempty houter
          hseam hcompl
    have hear :
        EarRemoval.IsEarAtOne hn w :=
      hcore.toIsEarAtOne hw
    exact
      ⟨{ disk :=
           EmptyDisk.holds
             hn w hw M hvertices htriangle hempty houter
               reduced.disk
         decomposition :=
           EarRemoval.decomposition_of_ear
             hn w hw hear
               (Dissection.PickDecomposition.triangle
                 (EarRemoval.earTriangle hn w) htriangle)
               reduced.decomposition }⟩
  · intro n hn w hw M hvertices htriangle visible hq
      hfrontCertificate hbackCertificate
    obtain ⟨frontCertificate⟩ := hfrontCertificate
    obtain ⟨backCertificate⟩ := hbackCertificate
    have hfront :
        IsSimple
          (latPoly
            (FrontSubpolygon.vertices w visible.q)) :=
      FrontSubpolygon.isSimple_vertices_of_clean
        w hw visible.q hq visible.boundary_inter
    have hback :
        IsSimple
          (latPoly
            (BackSubpolygon.vertices w visible.q hq)) :=
      BackSubpolygon.isSimple_vertices_of_clean
        w hw visible.q hq visible.boundary_inter
    exact
      ⟨{ disk :=
           VisibleDisk.holds
             hn w hw M hvertices htriangle visible hq
               hfront hback frontCertificate.disk
               backCertificate.disk
         decomposition :=
           VisibleDecomposition.glue
             hn w hw M hvertices htriangle visible hq
               hfront hback frontCertificate.disk
               backCertificate.disk
               frontCertificate.decomposition
               backCertificate.decomposition }⟩
  · exact hm
  · exact hsimple

/-- Pick's formula follows from the checked dissection produced by clean
diagonal descent. -/
theorem pick
    {n : ℕ} (hn : 3 ≤ n)
    (v : Fin n → ℤ × ℤ)
    (hsimple : IsSimple (latPoly v)) :
    area ((latPoly v).boundary (R := ℝ)) =
      (interiorPts v : ℝ) +
        (boundaryPts v : ℝ) / 2 - 1 := by
  obtain ⟨certificate⟩ :=
    exists_certificate hn v hsimple
  exact certificate.decomposition.pick

end Submission.InductiveSolution
