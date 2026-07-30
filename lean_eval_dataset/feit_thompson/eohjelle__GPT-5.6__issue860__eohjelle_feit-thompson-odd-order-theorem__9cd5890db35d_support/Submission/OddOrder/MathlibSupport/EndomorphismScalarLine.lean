import Submission.OddOrder.MathlibSupport.PrimitiveRootConjugationBlockRankDrop

/-!
The scalar identity line in the endomorphism conjugation eigenspace.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- The line of scalar multiples of the identity endomorphism. -/
def endomorphismScalarLine : Submodule k (Module.End k V) :=
  k ∙ (1 : Module.End k V)

@[simp]
theorem primitiveRootUnitWeight_zero
    {h : Nat} {omega : kˣ} (homega : IsPrimitiveRoot omega h) :
    primitiveRootUnitWeight homega 0 = 1 := by
  apply Units.ext
  simp [primitiveRootUnitWeight]

@[simp]
theorem linearEquivConjugation_one (f : V ≃ₗ[k] V) :
    linearEquivConjugation f (1 : Module.End k V) = 1 := by
  ext x
  simp [linearEquivConjugation, Module.End.mul_apply]

/-- Scalar endomorphisms lie in the eigenvalue-one conjugation eigenspace. -/
theorem endomorphismScalarLine_le_conjugation_eigenspace_one
    (f : V ≃ₗ[k] V) :
    endomorphismScalarLine (k := k) (V := V) ≤
      Module.End.eigenspace (linearEquivConjugation f) 1 := by
  rw [endomorphismScalarLine, Submodule.span_singleton_le_iff_mem,
    Module.End.mem_eigenspace_iff]
  rw [linearEquivConjugation_one, one_smul]

/-- On a nonzero module, the scalar identity line has dimension one. -/
theorem finrank_endomorphismScalarLine [Nontrivial V] :
    Module.finrank k (endomorphismScalarLine (k := k) (V := V)) = 1 := by
  rw [endomorphismScalarLine]
  exact finrank_span_singleton one_ne_zero

/-- Equal-rank primitive-root blocks spanning together with the scalar
identity line force the exact one-rank drop away from weight zero. -/
theorem primitiveRoot_conjugation_rank_drop_of_scalar_blocks
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [FiniteDimensional k V] [Nontrivial V]
    (f : V ≃ₗ[k] V) (c : Nat)
    (B : ZMod h -> Submodule k (Module.End k V))
    (hB_le : ∀ i : ZMod h,
      B i ≤ Module.End.eigenspace (linearEquivConjugation f)
        (primitiveRootUnitWeight homega i : k))
    (hB_rank : ∀ i : ZMod h, Module.finrank k (B i) = c)
    (hone_not_mem : (1 : Module.End k V) ∉ B 0)
    (hblocks_span :
      endomorphismScalarLine (k := k) (V := V) ⊔ ⨆ i, B i = ⊤)
    (hambient : Module.finrank k (Module.End k V) = h * c + 1) :
    ∀ m : ZMod h, m ≠ 0 ->
      Module.finrank k
          (Module.End.eigenspace (linearEquivConjugation f)
            (primitiveRootUnitWeight homega 0 : k)) =
        Module.finrank k
            (Module.End.eigenspace (linearEquivConjugation f)
              (primitiveRootUnitWeight homega m : k)) + 1 := by
  apply primitiveRoot_conjugation_rank_drop_of_blocks homega f c B
    hB_le hB_rank (endomorphismScalarLine (k := k) (V := V))
  · simpa using endomorphismScalarLine_le_conjugation_eigenspace_one
      (k := k) f
  · exact finrank_endomorphismScalarLine (k := k) (V := V)
  · exact (Submodule.disjoint_span_singleton_of_notMem hone_not_mem).symm
  · exact hblocks_span
  · exact hambient

end Submission.OddOrder.MathlibSupport
