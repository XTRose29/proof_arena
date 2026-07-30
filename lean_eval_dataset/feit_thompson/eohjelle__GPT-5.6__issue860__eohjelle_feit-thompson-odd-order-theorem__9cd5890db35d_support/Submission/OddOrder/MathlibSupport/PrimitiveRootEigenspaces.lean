import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
Independent eigenspaces indexed by powers of a primitive root.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- The first `h` powers of a primitive `h`-th root are pairwise distinct. -/
theorem primitiveRoot_pow_injective_fin {omega : k} {h : Nat}
    (homega : IsPrimitiveRoot omega h) :
    Function.Injective (fun i : Fin h => omega ^ (i : Nat)) := by
  intro i j hij
  exact Fin.ext (homega.pow_inj i.isLt j.isLt hij)

/-- Eigenspaces indexed by the powers of a primitive root form an
independent family. -/
theorem primitiveRoot_pow_eigenspaces_iSupIndep
    (f : Module.End k V) {omega : k} {h : Nat}
    (homega : IsPrimitiveRoot omega h) :
    iSupIndep (fun i : Fin h => Module.End.eigenspace f (omega ^ (i : Nat))) := by
  change iSupIndep (f.eigenspace ∘ fun i : Fin h => omega ^ (i : Nat))
  exact f.eigenspaces_iSupIndep.comp (primitiveRoot_pow_injective_fin homega)

/-- Distinct powers of a primitive root give disjoint eigenspaces. -/
theorem primitiveRoot_pow_eigenspaces_disjoint
    (f : Module.End k V) {omega : k} {h : Nat}
    (homega : IsPrimitiveRoot omega h) {i j : Fin h} (hij : i ≠ j) :
    Disjoint (Module.End.eigenspace f (omega ^ (i : Nat)))
      (Module.End.eigenspace f (omega ^ (j : Nat))) :=
  (primitiveRoot_pow_eigenspaces_iSupIndep f homega).pairwiseDisjoint hij

end Submission.OddOrder.MathlibSupport
