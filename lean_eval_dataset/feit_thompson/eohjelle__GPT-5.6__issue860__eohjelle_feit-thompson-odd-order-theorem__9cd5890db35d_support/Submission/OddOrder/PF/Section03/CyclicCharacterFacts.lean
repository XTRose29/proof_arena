import Mathlib.GroupTheory.SpecificGroups.Cyclic
import Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionFDRep
import Submission.OddOrder.PF.Section01.BrauerPermutation

/-!
# Irreducible characters of cyclic groups

This file collects the elementary cyclic-character facts used in Peterfalvi
Section 3.  Every irreducible representation of a cyclic group is
one-dimensional, and completeness identifies the irreducible characters with
a basis indexed by the conjugacy classes.  Since conjugacy classes in a
cyclic group are singletons, their number is the order of the group.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped IsMulCommutative

universe u

namespace IrreducibleCharacter

variable {C k : Type u} [Group C] [IsCyclic C]
  [Field k] [IsAlgClosed k]

/-- Every irreducible representation of a cyclic group has degree one. -/
@[simp]
theorem representation_finrank_eq_one_of_isCyclic
    (chi : IrreducibleCharacter C k) :
    Module.finrank k chi.representation = 1 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
      chi.representation
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    chi.representation.ρ

/-- Every irreducible character of a cyclic group has value one at the
identity. -/
@[simp]
theorem apply_one_eq_one_of_isCyclic (chi : IrreducibleCharacter C k) :
    chi 1 = 1 := by
  rw [← chi.representation_character, FDRep.char_one,
    representation_finrank_eq_one_of_isCyclic]
  norm_num

section Finite

variable [Fintype C] [CharZero k]

local instance : Invertible (Nat.card C : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

local instance : Fintype (ConjClasses C) := Fintype.ofFinite _

/-- A finite cyclic group has as many irreducible characters as elements. -/
theorem card_eq_natCard_of_isCyclic :
    Fintype.card (IrreducibleCharacter C k) = Nat.card C := by
  let basis : Module.Basis (IrreducibleCharacter C k) k
      (ClassFunction C k) :=
    Module.Basis.mk linearIndependent (by
      rw [irreducibleCharacter_span_eq_top])
  calc
    Fintype.card (IrreducibleCharacter C k) =
        Module.finrank k (ClassFunction C k) :=
      (Module.finrank_eq_card_basis basis).symm
    _ = Module.finrank k (ConjClasses C → k) :=
      (ClassFunction.conjClassesLinearEquiv (G := C) (k := k)).finrank_eq
    _ = Fintype.card (ConjClasses C) :=
      Module.finrank_fintype_fun_eq_card k
    _ = Fintype.card C :=
      Fintype.card_congr (ConjClasses.mkEquiv (α := C)).symm
    _ = Nat.card C := Fintype.card_eq_nat_card

/-- A nontrivial finite cyclic group has a nontrivial irreducible character. -/
theorem exists_ne_trivial_of_one_lt_card (hC : 1 < Nat.card C) :
    ∃ chi : IrreducibleCharacter C k, chi ≠ trivial := by
  apply Fintype.exists_ne_of_one_lt_card
  rw [card_eq_natCard_of_isCyclic]
  exact hC

end Finite

end IrreducibleCharacter

section OddDual

variable {G k : Type u} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- A nontrivial irreducible character of a finite odd-order group is not
fixed by contragredient duality. -/
theorem dual_ne_self_of_odd_of_ne_trivial
    (hodd : Odd (Nat.card G)) {chi : IrreducibleCharacter G k}
    (hchi : chi ≠ IrreducibleCharacter.trivial) :
    IrreducibleCharacter.dual chi ≠ chi := by
  intro hdual
  exact hchi ((odd_eq_conj_irr1 hodd chi).mp hdual)

end OddDual

end

end Submission.OddOrder.PF
