import Submission.OddOrder.MathlibSupport.IndependentWeightBlocks

/-!
Primitive-root conjugation rank drops from independent weighted vectors.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {V : Type v} {J : Type w}
variable [Field k] [AddCommGroup V] [Module k V]

/-- An independent rectangular family of conjugation eigenvectors, together
with the scalar identity line and the tight ambient dimension, forces the
one-rank drop away from primitive-root weight zero. -/
theorem primitiveRoot_conjugation_rank_drop_of_independent_vectors
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [FiniteDimensional k V] [Nontrivial V]
    [Fintype J]
    (f : V ≃ₗ[k] V)
    (v : ZMod h -> J -> Module.End k V)
    (hv_independent :
      LinearIndependent k (fun p : ZMod h × J => v p.1 p.2))
    (hv_eigen : ∀ i j,
      v i j ∈ Module.End.eigenspace (linearEquivConjugation f)
        (primitiveRootUnitWeight homega i : k))
    (hone_not_mem :
      (1 : Module.End k V) ∉ indexedWeightBlock (k := k) v 0)
    (hspan :
      endomorphismScalarLine (k := k) (V := V) ⊔
        Submodule.span k
          (Set.range (fun p : ZMod h × J => v p.1 p.2)) = ⊤)
    (hambient :
      Module.finrank k (Module.End k V) = h * Fintype.card J + 1) :
    ∀ m : ZMod h, m ≠ 0 ->
      Module.finrank k
          (Module.End.eigenspace (linearEquivConjugation f)
            (primitiveRootUnitWeight homega 0 : k)) =
        Module.finrank k
            (Module.End.eigenspace (linearEquivConjugation f)
              (primitiveRootUnitWeight homega m : k)) + 1 := by
  apply primitiveRoot_conjugation_rank_drop_of_scalar_blocks homega f
    (Fintype.card J) (indexedWeightBlock (k := k) v)
  · exact indexedWeightBlock_le v
      (fun i => Module.End.eigenspace (linearEquivConjugation f)
        (primitiveRootUnitWeight homega i : k)) hv_eigen
  · exact finrank_indexedWeightBlock v hv_independent
  · exact hone_not_mem
  · exact sup_iSup_indexedWeightBlock_eq_top v
      (endomorphismScalarLine (k := k) (V := V)) hspan
  · exact hambient

end Submission.OddOrder.MathlibSupport
