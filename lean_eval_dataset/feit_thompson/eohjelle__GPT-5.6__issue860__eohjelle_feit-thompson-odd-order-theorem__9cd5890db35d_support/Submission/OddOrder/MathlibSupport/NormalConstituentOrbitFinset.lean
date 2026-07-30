import Submission.OddOrder.MathlibSupport.NormalConstituentOrbit

/-!
The finite set of distinct translates of a simple normal-restriction
constituent.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Finite G] [AddCommGroup V] [Module k V]

/-- The finite set of distinct ambient translates of a normal-restriction
subrepresentation. -/
noncomputable def normalConstituentOrbitFinset
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) :
    Finset (Subrepresentation (rho.comp N.subtype)) := by
  classical
  letI := Fintype.ofFinite G
  exact Finset.univ.image (fun g ↦ conjugateNormalSubrepresentation rho N g U)

theorem mem_normalConstituentOrbitFinset_iff
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U X : Subrepresentation (rho.comp N.subtype)) :
    X ∈ normalConstituentOrbitFinset rho N U ↔
      ∃ g : G, conjugateNormalSubrepresentation rho N g U = X := by
  classical
  letI := Fintype.ofFinite G
  simp [normalConstituentOrbitFinset]

/-- Every member of the orbit of a simple constituent is an atom. -/
theorem isAtom_of_mem_normalConstituentOrbitFinset
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U X : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    (hX : X ∈ normalConstituentOrbitFinset rho N U) : IsAtom X := by
  obtain ⟨g, rfl⟩ := (mem_normalConstituentOrbitFinset_iff rho N U X).mp hX
  exact (isAtom_conjugateNormalSubrepresentation_iff rho N g U).mpr
    ((irreducible_toRepresentation_iff_isAtom _ U).mp inferInstance)

/-- Two distinct simple constituents in the ambient orbit are disjoint. -/
theorem normalConstituentOrbitFinset_pairwiseDisjoint
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation] :
    ((normalConstituentOrbitFinset rho N U :
        Finset (Subrepresentation (rho.comp N.subtype))) :
      Set (Subrepresentation (rho.comp N.subtype))).PairwiseDisjoint id := by
  intro X hX Y hY hXY
  exact (isAtom_of_mem_normalConstituentOrbitFinset rho N U X hX).disjoint_of_ne
    (isAtom_of_mem_normalConstituentOrbitFinset rho N U Y hY) hXY

/-- Taking the supremum over the deduplicated orbit gives the same orbit span
as taking the supremum over all ambient elements. -/
theorem normalConstituentOrbitFinset_sup
    (rho : Representation k G V) (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype)) :
    (normalConstituentOrbitFinset rho N U).sup id =
      normalConstituentOrbitSup rho N U := by
  classical
  letI := Fintype.ofFinite G
  simp [normalConstituentOrbitFinset, normalConstituentOrbitSup]

end Submission.OddOrder.MathlibSupport
