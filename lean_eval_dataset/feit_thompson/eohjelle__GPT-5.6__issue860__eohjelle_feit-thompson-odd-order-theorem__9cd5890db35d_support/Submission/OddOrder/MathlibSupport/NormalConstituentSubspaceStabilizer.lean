import Mathlib.GroupTheory.Index
import Submission.OddOrder.MathlibSupport.NormalConstituentOrbitFinset

/-!
The ambient group action on normal-restriction subrepresentations and the
stabilizer of an actual constituent subspace.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Ambient translation defines a group action on the subrepresentation
lattice of a normal restriction. -/
@[reducible]
def normalRestrictionSubrepresentationMulAction
    (rho : Representation k G V) (N : Subgroup G) [N.Normal] :
    MulAction G (Subrepresentation (rho.comp N.subtype)) where
  smul := conjugateNormalSubrepresentation rho N
  one_smul := conjugateNormalSubrepresentation_one rho N
  mul_smul := conjugateNormalSubrepresentation_mul rho N

/-- Elements of the normal subgroup fix every subrepresentation of its own
restricted representation. -/
theorem conjugateNormalSubrepresentation_subgroupElement
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (n : N) :
    conjugateNormalSubrepresentation rho N (n : G) U = U := by
  apply SetLike.ext
  intro v
  rw [mem_conjugateNormalSubrepresentation_iff]
  constructor
  · intro hv
    have hnv := U.apply_mem_toSubmodule n hv
    change v ∈ U.toSubmodule
    simpa using hnv
  · intro hv
    exact U.apply_mem_toSubmodule n⁻¹ hv

/-- The stabilizer of an actual constituent subspace under ambient
translation. This is narrower than the Clifford inertia group, which only
stabilizes the constituent's isomorphism class. -/
def normalConstituentSubspaceStabilizer
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) : Subgroup G := by
  letI := normalRestrictionSubrepresentationMulAction rho N
  exact MulAction.stabilizer G U

theorem mem_normalConstituentSubspaceStabilizer_iff
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) (g : G) :
    g ∈ normalConstituentSubspaceStabilizer rho N U ↔
      conjugateNormalSubrepresentation rho N g U = U := by
  rfl

/-- The normal subgroup is contained in every constituent-subspace
stabilizer. -/
theorem normal_le_normalConstituentSubspaceStabilizer
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) :
    N ≤ normalConstituentSubspaceStabilizer rho N U := by
  intro g hg
  rw [mem_normalConstituentSubspaceStabilizer_iff]
  exact conjugateNormalSubrepresentation_subgroupElement rho N U ⟨g, hg⟩

/-- Orbit-stabilizer identifies the index of the subspace stabilizer with the
number of distinct translated constituent subspaces. -/
theorem normalConstituentSubspaceStabilizer_index
    [Finite G]
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) :
    (normalConstituentSubspaceStabilizer rho N U).index =
      (normalConstituentOrbitFinset rho N U).card := by
  classical
  letI := Fintype.ofFinite G
  letI := normalRestrictionSubrepresentationMulAction rho N
  change (MulAction.stabilizer G U).index = _
  rw [MulAction.index_stabilizer]
  have horbit : MulAction.orbit G U =
      ((normalConstituentOrbitFinset rho N U :
          Finset (Subrepresentation (rho.comp N.subtype))) :
        Set (Subrepresentation (rho.comp N.subtype))) := by
    ext X
    rw [MulAction.mem_orbit_iff]
    change (∃ x : G, x • U = X) ↔ X ∈ normalConstituentOrbitFinset rho N U
    rw [mem_normalConstituentOrbitFinset_iff]
    rfl
  rw [horbit, Set.ncard_coe_finset]

end Submission.OddOrder.MathlibSupport
