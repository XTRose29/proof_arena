import Submission.OddOrder.MathlibSupport.CyclicOrbitFourierFamily

/-!
Global span preservation for Fourier-transformed cyclic orbit families.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {W : Type v} {J : Type w}
variable [Field k] [AddCommGroup W] [Module k W]

/-- Fourier-transforming every independent cyclic orbit preserves the span of
the complete family, including the swap from orbit-first to weight-first
indexing. -/
theorem span_cyclicOrbitFourierFamily_global_eq
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h)
    (v : J -> ZMod h -> W)
    (hv : LinearIndependent k (fun p : J × ZMod h => v p.1 p.2)) :
    Submodule.span k
        (Set.range (fun p : ZMod h × J =>
          cyclicOrbitFourierFamily homega v p.1 p.2)) =
      Submodule.span k
        (Set.range (fun p : J × ZMod h => v p.1 p.2)) := by
  have hslice (j : J) : LinearIndependent k (v j) :=
    linearIndependent_weight_slice v hv j
  have hlocal (j : J) :
      indexedWeightBlock (k := k)
          (fun j i => cyclicOrbitFourierFamily homega v i j) j =
        indexedWeightBlock (k := k) v j :=
    span_cyclicOrbitFourierFamily_eq homega (v j) (hslice j)
  have hrange :
      Set.range (fun p : ZMod h × J =>
          cyclicOrbitFourierFamily homega v p.1 p.2) =
        Set.range (fun p : J × ZMod h =>
          cyclicOrbitFourierFamily homega v p.2 p.1) := by
    ext x
    constructor
    · rintro ⟨⟨i, j⟩, rfl⟩
      exact ⟨(j, i), rfl⟩
    · rintro ⟨⟨j, i⟩, rfl⟩
      exact ⟨(i, j), rfl⟩
  rw [hrange,
    ← iSup_indexedWeightBlock (k := k)
      (fun j : J => fun i : ZMod h => cyclicOrbitFourierFamily homega v i j),
    show (⨆ j, indexedWeightBlock (k := k)
      (fun j i => cyclicOrbitFourierFamily homega v i j) j) =
        ⨆ j, indexedWeightBlock (k := k) v j by
      exact iSup_congr hlocal,
    iSup_indexedWeightBlock (k := k) v]

end Submission.OddOrder.MathlibSupport
