import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Invariants

/-!
Invariant vectors for cyclic representations as a single kernel.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [CommRing F] [Group G] [IsCyclic G]
  [AddCommGroup V] [Module F V]

/-- For a cyclic group, common invariant vectors are the kernel of the
generator minus the identity. -/
theorem exists_invariants_eq_ker_sub_one (rho : Representation F G V) :
    ∃ z : G, rho.invariants = LinearMap.ker (rho z - 1) := by
  obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := G)
  refine ⟨z, ?_⟩
  ext x
  rw [Representation.mem_invariants_iff_of_forall_mem_zpowers rho z hz x]
  simp [LinearMap.mem_ker, sub_eq_zero]

/-- Kernel criterion for a nonzero fixed space of a cyclic representation. -/
theorem exists_invariants_ne_bot_iff_not_injective_sub_one
    (rho : Representation F G V) :
    ∃ z : G, rho.invariants ≠ ⊥ ↔
      ¬Function.Injective (rho z - 1 : Module.End F V) := by
  obtain ⟨z, hz⟩ := exists_invariants_eq_ker_sub_one rho
  refine ⟨z, ?_⟩
  rw [hz, ne_eq, LinearMap.ker_eq_bot]

end Submission.OddOrder.MathlibSupport
