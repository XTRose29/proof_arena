import Mathlib.Algebra.DirectSum.Module
import Mathlib.LinearAlgebra.Dimension.Free
import Submission.OddOrder.MathlibSupport.CyclicRankCorrelation
import Submission.OddOrder.MathlibSupport.EigenbasisConjugationMatrix
import Submission.OddOrder.MathlibSupport.IndependentSubmoduleFinrank
import Submission.OddOrder.MathlibSupport.PrimitiveRootMatrixConjugation

/-!
Coordinate-free conjugation eigenspace dimensions from a primitive-root
eigenspace decomposition.
-/

namespace Submission.OddOrder.MathlibSupport

open Module
open scoped BigOperators

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- The scalar values of the primitive-root character are injective. -/
theorem primitiveRootUnitWeight_val_injective
    {h : Nat} {omega : kˣ} (homega : IsPrimitiveRoot omega h) :
    Function.Injective
      (fun i : ZMod h => (primitiveRootUnitWeight homega i : k)) :=
  Units.val_injective.comp (primitiveRootUnitWeight_injective homega)

/-- In a complete primitive-root eigenspace decomposition, the `m`-th
eigenspace of inverse conjugation has finrank equal to the cyclic
autocorrelation of the original eigenspace finranks. -/
theorem finrank_linearEquivConjugation_primitiveRoot
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [FiniteDimensional k V]
    (f : V ≃ₗ[k] V)
    (hspan :
      ⨆ i : ZMod h,
        Module.End.eigenspace f.toLinearMap
          (primitiveRootUnitWeight homega i : k) = ⊤)
    (m : ZMod h) :
    Module.finrank k
      (Module.End.eigenspace (linearEquivConjugation f)
        (primitiveRootUnitWeight homega m : k)) =
      ∑ i : ZMod h,
        Module.finrank k
            (Module.End.eigenspace f.toLinearMap
              (primitiveRootUnitWeight homega i : k)) *
          Module.finrank k
            (Module.End.eigenspace f.toLinearMap
              (primitiveRootUnitWeight homega (i + m) : k)) := by
  let U : ZMod h -> Submodule k V := fun i =>
    Module.End.eigenspace f.toLinearMap
      (primitiveRootUnitWeight homega i : k)
  have hindependent : iSupIndep U := by
    change iSupIndep
      (Module.End.eigenspace f.toLinearMap ∘
        fun i : ZMod h => (primitiveRootUnitWeight homega i : k))
    exact (Module.End.eigenspaces_iSupIndep f.toLinearMap).comp
      (primitiveRootUnitWeight_val_injective homega)
  let hinternal : DirectSum.IsInternal U :=
    DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top
      hindependent hspan
  let fiber : ZMod h -> Type := fun i =>
    Fin (Module.finrank k (U i))
  let blockBasis : ∀ i, Basis (fiber i) k (U i) := fun i =>
    Module.finBasis k (U i)
  let b : Basis (Σ i, fiber i) k V :=
    hinternal.collectedBasis blockBasis
  let d : (Σ i, fiber i) -> kˣ := fun p =>
    primitiveRootUnitWeight homega p.1
  have happly (p : Σ i, fiber i) :
      f (b p) = (d p : k) • b p := by
    exact Module.End.mem_eigenspace_iff.mp
      (hinternal.collectedBasis_mem blockBasis p)
  calc
    Module.finrank k
        (Module.End.eigenspace (linearEquivConjugation f)
          (primitiveRootUnitWeight homega m : k)) =
        Module.finrank k
          (Module.End.eigenspace
            (matrixEntrywiseScale
              (primitiveRootConjugationEntryWeight homega fiber))
            (primitiveRootUnitWeight homega m : k)) := by
      change Module.finrank k
          (Module.End.eigenspace (linearEquivConjugation f)
            (primitiveRootUnitWeight homega m : k)) =
        Module.finrank k
          (Module.End.eigenspace
            (matrixEntrywiseScale
              (fun p : (Σ i, fiber i) × (Σ i, fiber i) =>
                ↑((primitiveRootUnitWeight homega p.1.1)⁻¹ *
                  primitiveRootUnitWeight homega p.2.1)))
            (primitiveRootUnitWeight homega m : k))
      simpa [d] using
        finrank_linearEquivConjugation_eigenspace_eq_entrywise
          b f d happly (primitiveRootUnitWeight homega m : k)
    _ = ∑ i : ZMod h,
          Nat.card (fiber i) * Nat.card (fiber (i + m)) :=
      finrank_primitiveRootConjugationEntryWeight_eigenspace
        homega fiber m
    _ = ∑ i : ZMod h,
          Module.finrank k (U i) * Module.finrank k (U (i + m)) := by
      simp [fiber]
    _ = ∑ i : ZMod h,
          Module.finrank k
              (Module.End.eigenspace f.toLinearMap
                (primitiveRootUnitWeight homega i : k)) *
            Module.finrank k
              (Module.End.eigenspace f.toLinearMap
                (primitiveRootUnitWeight homega (i + m) : k)) := rfl

/-- Correlation-form restatement of
`finrank_linearEquivConjugation_primitiveRoot`. -/
theorem finrank_linearEquivConjugation_eq_cyclicRankCorrelation
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [FiniteDimensional k V]
    (f : V ≃ₗ[k] V)
    (hspan :
      ⨆ i : ZMod h,
        Module.End.eigenspace f.toLinearMap
          (primitiveRootUnitWeight homega i : k) = ⊤)
    (m : ZMod h) :
    Module.finrank k
      (Module.End.eigenspace (linearEquivConjugation f)
        (primitiveRootUnitWeight homega m : k)) =
      cyclicRankCorrelation
        (fun i : ZMod h =>
          Module.finrank k
            (Module.End.eigenspace f.toLinearMap
              (primitiveRootUnitWeight homega i : k))) m := by
  exact finrank_linearEquivConjugation_primitiveRoot homega f hspan m

end Submission.OddOrder.MathlibSupport
