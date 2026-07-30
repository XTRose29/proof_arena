import Mathlib.LinearAlgebra.Eigenspace.Basic
import Mathlib.RepresentationTheory.Invariants
import Submission.OddOrder.MathlibSupport.EndomorphismConjugationInvariants

/-!
Eigenspaces at a generator of a cyclic representation.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- If `z` generates the group, its eigenvalue-one eigenspace is the
invariant subspace of the representation. -/
theorem invariants_eq_eigenspace_one_of_forall_mem_zpowers
    (rho : Representation k G V) (z : G)
    (hz : ∀ g : G, g ∈ Subgroup.zpowers z) :
    rho.invariants = Module.End.eigenspace (rho z) 1 := by
  ext x
  rw [Representation.mem_invariants_iff_of_forall_mem_zpowers rho z hz x,
    Module.End.mem_eigenspace_iff]
  simp

/-- For an irreducible representation, the eigenvalue-one eigenspace of a
generator acting by conjugation on `End(V)` is one-dimensional. -/
theorem finrank_endomorphismConjugation_eigenspace_one_of_forall_mem_zpowers
    [IsAlgClosed k] [FiniteDimensional k V]
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (z : G) (hz : ∀ g : G, g ∈ Subgroup.zpowers z) :
    Module.finrank k
      (Module.End.eigenspace
        (endomorphismConjugationRepresentation rho z) 1) = 1 := by
  rw [← invariants_eq_eigenspace_one_of_forall_mem_zpowers
    (endomorphismConjugationRepresentation rho) z hz]
  exact finrank_endomorphismConjugation_invariants rho

end Submission.OddOrder.MathlibSupport
