import Mathlib.RepresentationTheory.Maschke
import Submission.OddOrder.MathlibSupport.NormalConstituentCharacterStabilizer
import Submission.OddOrder.MathlibSupport.NormalConstituentOrbitFinset
import Submission.OddOrder.MathlibSupport.RepresentationIsotypic

/-!
Full character inertia makes the restriction of an irreducible
representation to a finite normal subgroup isotypic.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [CharZero k]
variable [Group G] [Finite G] [AddCommGroup V] [Module k V]
variable [FiniteDimensional k V]

/-- If a simple constituent has full character inertia, every simple
constituent of the normal restriction is equivalent to it. -/
theorem normalRestriction_isRepresentationIsotypic_of_characterStabilizer_eq_top
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    (N : Subgroup G) [N.Normal]
    (U : Subrepresentation (rho.comp N.subtype))
    [Representation.IsIrreducible U.toRepresentation]
    (hinertia : normalConstituentCharacterStabilizer rho N U = ⊤) :
    IsRepresentationIsotypic (rho.comp N.subtype) := by
  letI := Fintype.ofFinite N
  letI : NeZero (Nat.card N) :=
    ⟨Nat.card_ne_zero.mpr ⟨inferInstance, inferInstance⟩⟩
  letI : NeZero (Nat.card N : k) := NeZero.charZero
  let rhoN : Representation k N V := rho.comp N.subtype
  letI : IsSemisimpleModule k[N] rhoN.asModule := by
    infer_instance
  have hU_ne : U ≠ ⊥ :=
    ((irreducible_toRepresentation_iff_isAtom _ U).mp inferInstance).1
  have horbit_top : (normalConstituentOrbitFinset rho N U).sup id = ⊤ := by
    rw [normalConstituentOrbitFinset_sup]
    exact normalConstituentOrbitSup_eq_top rho N U hU_ne
  have horbit_simple : ∀ X ∈ normalConstituentOrbitFinset rho N U,
      Representation.IsIrreducible X.toRepresentation := by
    intro X hX
    exact (irreducible_toRepresentation_iff_isAtom _ X).mpr
      (isAtom_of_mem_normalConstituentOrbitFinset rho N U X hX)
  have hequiv_to_U (W : Subrepresentation (rho.comp N.subtype))
      (hW : Representation.IsIrreducible W.toRepresentation) :
      Nonempty (Representation.Equiv W.toRepresentation U.toRepresentation) := by
    obtain ⟨X, hX, ⟨eWX⟩⟩ := exists_equiv_finset_of_sup_eq_top
      (rho.comp N.subtype) W hW (normalConstituentOrbitFinset rho N U)
      horbit_simple horbit_top
    obtain ⟨g, rfl⟩ := (mem_normalConstituentOrbitFinset_iff rho N U X).mp hX
    have hg : g ∈ normalConstituentCharacterStabilizer rho N U := by
      rw [hinertia]
      exact Subgroup.mem_top g
    obtain ⟨eUg⟩ :=
      (mem_normalConstituentCharacterStabilizer_iff_nonempty_equiv_translate
        rho N U g).mp hg
    exact ⟨eWX.trans eUg.symm⟩
  intro W₁ W₂ hW₁ hW₂
  obtain ⟨e₁⟩ := hequiv_to_U W₁ hW₁
  obtain ⟨e₂⟩ := hequiv_to_U W₂ hW₂
  exact ⟨e₁.trans e₂.symm⟩

end Submission.OddOrder.MathlibSupport
