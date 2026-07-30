import Submission.OddOrder.PF.Section01.MultiplicityNormRigidity

/-!
# Nonvanishing of induced irreducible representations

The norm-rigidity step in Peterfalvi 1.7(a) needs the endomorphism space of
each induced constituent to have positive dimension.  We prove this without
assuming the desired irreducibility: a simple representation is nonzero,
and its induction has nonzero character value at the identity.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical
open CategoryTheory

universe u

namespace FDRep

variable {A k : Type u} [Group A] [Field k]

/-- The underlying vector space of a simple bundled representation is
nontrivial. -/
theorem nontrivial_of_simple (V : FDRep k A) [CategoryTheory.Simple V] :
    Nontrivial V := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  apply CategoryTheory.id_nonzero V
  apply ConcreteCategory.hom_ext
  intro v
  change v = 0
  exact Subsingleton.elim _ _

/-- A nonzero representation has a positive-dimensional endomorphism
space, since its identity endomorphism is nonzero. -/
theorem finrank_end_pos_of_nontrivial (V : FDRep k A) [Nontrivial V] :
    0 < Module.finrank k (V ⟶ V) := by
  rw [Module.finrank_pos_iff_exists_ne_zero]
  refine ⟨𝟙 V, ?_⟩
  intro hzero
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  have hval := ConcreteCategory.congr_hom hzero v
  change v = (0 : V) at hval
  exact hval

variable {G : Type u} [Group G] [Fintype G] [CharZero k]

/-- Induction from a subgroup of the representation realizing an
irreducible character is nonzero. -/
theorem induceFromSubgroup_nontrivial
    (S : Subgroup G) (psi : IrreducibleCharacter S k) :
    Nontrivial (induceFromSubgroup S psi.representation) := by
  let V := psi.representation
  letI : CategoryTheory.Simple V := psi.representation_simple
  letI : Nontrivial V := nontrivial_of_simple V
  let W := induceFromSubgroup S V
  have hpsiOne : (psi : ClassFunction S k) 1 =
      (Module.finrank k V : k) := by
    rw [← psi.representation_character, FDRep.char_one]
  have hpsiOne_ne : (psi : ClassFunction S k) 1 ≠ 0 := by
    rw [hpsiOne]
    exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hindOne : ClassFunction.induce S (psi : ClassFunction S k) 1 =
      (Nat.card S : k)⁻¹ * (Nat.card G : k) *
        (psi : ClassFunction S k) 1 := by
    rw [ClassFunction.induce_apply_formula]
    have hsum :
        (∑ x : G, if hx : x⁻¹ * 1 * x ∈ S then
          (psi : ClassFunction S k) ⟨x⁻¹ * 1 * x, hx⟩ else 0) =
          ∑ _x : G, (psi : ClassFunction S k) 1 := by
      apply Fintype.sum_congr
      intro x
      rw [dif_pos (by simp)]
      apply congrArg (psi : S → k)
      apply Subtype.ext
      simp
    rw [hsum, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_eq_nat_card]
    ring
  have hindOne_ne : ClassFunction.induce S
      (psi : ClassFunction S k) 1 ≠ 0 := by
    rw [hindOne]
    exact mul_ne_zero
      (mul_ne_zero (inv_ne_zero (Nat.cast_ne_zero.mpr Nat.card_pos.ne'))
        (Nat.cast_ne_zero.mpr Nat.card_pos.ne')) hpsiOne_ne
  have hcompat : ClassFunction.ofRepresentation W.ρ =
      ClassFunction.induce S (psi : ClassFunction S k) := by
    exact (ClassFunction.ofRepresentation_induceFromSubgroup_general S V).trans
      (congrArg (ClassFunction.induce S)
        psi.ofRepresentation_representation)
  have hWdim_ne : (Module.finrank k W : k) ≠ 0 := by
    intro hzero
    apply hindOne_ne
    rw [← hcompat]
    change W.character 1 = 0
    rw [FDRep.char_one, hzero]
  have hWdim : 0 < Module.finrank k W :=
    Nat.pos_of_ne_zero (Nat.cast_ne_zero.mp hWdim_ne)
  exact Module.finrank_pos_iff.mp hWdim

/-- The endomorphism multiplicity of an induced irreducible character is
positive. -/
theorem finrank_end_induceFromSubgroup_pos
    (S : Subgroup G) (psi : IrreducibleCharacter S k) :
    0 < Module.finrank k
      (induceFromSubgroup S psi.representation ⟶
        induceFromSubgroup S psi.representation) := by
  letI : Nontrivial (induceFromSubgroup S psi.representation) :=
    induceFromSubgroup_nontrivial S psi
  exact finrank_end_pos_of_nontrivial _

end FDRep

end

end Submission.OddOrder.PF
