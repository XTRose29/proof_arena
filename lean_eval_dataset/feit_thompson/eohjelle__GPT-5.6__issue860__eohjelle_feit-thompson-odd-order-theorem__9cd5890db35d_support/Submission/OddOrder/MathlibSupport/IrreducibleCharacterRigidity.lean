import Mathlib.RepresentationTheory.Character

/-!
Character rigidity for irreducible representations of finite groups.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v w x

variable {k : Type u} {G : Type v} {V : Type w} {W : Type x}
variable [Field k] [IsAlgClosed k]
variable [Group G] [Finite G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]
variable [AddCommGroup W] [Module k W] [FiniteDimensional k W]

/-- Two irreducible representations with the same character are equivalent
whenever the group order is nonzero in the coefficient field. -/
theorem nonempty_representationEquiv_of_irreducible_character_eq_of_card_ne_zero
    (rho : Representation k G V) (sigma : Representation k G W)
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible sigma]
    (hcard : (Nat.card G : k) ≠ 0)
    (hchar : rho.character = sigma.character) :
    Nonempty (rho.Equiv sigma) := by
  letI := Fintype.ofFinite G
  letI : Invertible (Nat.card G : k) := invertibleOfNonzero hcard
  classical
  by_contra hnone
  have hnone' : ¬Nonempty (sigma.Equiv rho) := by
    rintro ⟨e⟩
    exact hnone ⟨e.symm⟩
  have hself := rho.char_orthonormal rho
  have hcross := rho.char_orthonormal sigma
  have hrefl : Nonempty (rho.Equiv rho) :=
    ⟨Representation.Equiv.refl rho⟩
  rw [if_pos hrefl] at hself
  rw [if_neg hnone'] at hcross
  rw [← hchar] at hcross
  exact one_ne_zero (hself.symm.trans hcross)

/-- Two irreducible finite-dimensional representations with the same ordinary
character are equivalent. -/
theorem nonempty_representationEquiv_of_irreducible_character_eq
    [CharZero k]
    (rho : Representation k G V) (sigma : Representation k G W)
    [Representation.IsIrreducible rho]
    [Representation.IsIrreducible sigma]
    (hchar : rho.character = sigma.character) :
    Nonempty (rho.Equiv sigma) := by
  have hcardne : (Nat.card G : k) ≠ 0 := by
    rw [Nat.cast_ne_zero]
    exact Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩
  exact nonempty_representationEquiv_of_irreducible_character_eq_of_card_ne_zero
    rho sigma hcardne hchar

end Submission.OddOrder.MathlibSupport
