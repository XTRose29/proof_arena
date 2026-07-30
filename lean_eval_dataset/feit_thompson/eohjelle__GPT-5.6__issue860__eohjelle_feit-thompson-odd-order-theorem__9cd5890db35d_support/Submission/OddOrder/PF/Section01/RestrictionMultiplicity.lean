import Submission.OddOrder.PF.Section01.NormalInduceRestrictTwistSum

/-!
# Natural multiplicities in restricted characters

This file bundles restriction of an `FDRep` to a subgroup and records the
natural-number multiplicity of an irreducible character in that restriction.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u

namespace FDRep

variable {G k : Type u} [Group G] [Field k]

/-- Restriction of a bundled finite-dimensional representation to a
subgroup. -/
def restrictToSubgroup (K : Subgroup G) (V : FDRep k G) : FDRep k K :=
  FDRep.of (V.ρ.comp K.subtype)

@[simp]
theorem ofRepresentation_restrictToSubgroup
    (K : Subgroup G) (V : FDRep k G) :
    ClassFunction.ofRepresentation (restrictToSubgroup K V).ρ =
      ClassFunction.restrict K (ClassFunction.ofRepresentation V.ρ) := by
  ext h
  rfl

end FDRep

namespace IrreducibleCharacter

variable {G k : Type u} [Group G] [Field k] [Fintype G] [CharZero k]

/-- Multiplicity of an irreducible subgroup character in the restriction of
an ambient irreducible character. -/
def restrictionMultiplicity (K : Subgroup G)
    (psi : IrreducibleCharacter G k)
    (xi : IrreducibleCharacter K k) : ℕ :=
  xi.multiplicity (FDRep.restrictToSubgroup K psi.representation)

omit [Fintype G] in
/-- The cast of a restriction multiplicity is the corresponding character
pairing. -/
theorem characterPairing_restrict_eq_restrictionMultiplicity
    (K : Subgroup G) [Fintype K] (psi : IrreducibleCharacter G k)
    (xi : IrreducibleCharacter K k) :
    characterPairing
        (ClassFunction.restrict K (psi : ClassFunction G k))
        (xi : ClassFunction K k) =
      (restrictionMultiplicity K psi xi : k) := by
  rw [← psi.ofRepresentation_representation,
    ← FDRep.ofRepresentation_restrictToSubgroup]
  exact xi.characterPairing_ofRepresentation_eq_multiplicity
    (FDRep.restrictToSubgroup K psi.representation)

end IrreducibleCharacter

end

end Submission.OddOrder.PF
