import Submission.OddOrder.PF.Section01.NormalSubgroupInductionKernel
import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence

/-!
# Kernels of irreducible constituents

This file continues Peterfalvi 1.6 after `cfInd_irr_eq1`.  We introduce the
character-theoretic constituent predicate used by the source and prove that
the kernel of a realized character is contained in the kernel of each of its
irreducible constituents.  The proof identifies the character pairing with
the dimension of an equivariant Hom-space, chooses a nonzero intertwiner, and
uses simplicity to make it injective.

Frobenius reciprocity then identifies constituents of restriction with
constituents of induction.  Combined with 1.6(a), this gives the two adjacent
source kernel equivalences `sub_cfker_constt_Res_irr` and
`sub_cfker_constt_Ind_irr` in the normal-subgroup setting used by the current
induced-character compatibility layer.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

open CategoryTheory

universe u v

namespace IrreducibleCharacter

variable {G : Type u} {k : Type v} [Group G] [Field k] [Fintype G]

/-- An irreducible character is a constituent of a class function when its
character pairing with that class function is nonzero. -/
def IsConstituent (chi : IrreducibleCharacter G k)
    (f : ClassFunction G k) : Prop :=
  characterPairing f (chi : ClassFunction G k) ≠ 0

/-- Frobenius reciprocity identifies constituents of restriction with
constituents of induction. -/
theorem isConstituent_restrict_iff_induce [CharZero k]
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    (H : Subgroup Gamma) [Fintype H]
    (psi : IrreducibleCharacter H k)
    (chi : IrreducibleCharacter Gamma k) :
    psi.IsConstituent
        (ClassFunction.restrict H (chi : ClassFunction Gamma k)) ↔
      chi.IsConstituent
        (ClassFunction.induce H (psi : ClassFunction H k)) := by
  unfold IsConstituent
  rw [ClassFunction.frobeniusReciprocity]
  rw [characterPairing_comm
    (ClassFunction.restrict H (chi : ClassFunction Gamma k))
    (psi : ClassFunction H k)]

end IrreducibleCharacter

namespace FDRep

variable {G k : Type u} [Group G] [Field k] [Fintype G] [CharZero k]

/-- A nonzero constituent pairing produces a nonzero equivariant map from
the chosen irreducible realization into the realized character. -/
theorem exists_hom_ne_zero_of_isConstituent
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent (ClassFunction.ofRepresentation V.ρ)) :
    ∃ f : chi.representation ⟶ V, f ≠ 0 := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hpair :
      characterPairing (ClassFunction.ofRepresentation V.ρ)
          (chi : ClassFunction G k) =
        (Module.finrank k (chi.representation ⟶ V) : k) := by
    have hhom :=
      FDRep.scalar_product_char_eq_finrank_equivariant chi.representation V
    have hcharV (g : G) :
        V.character g = _root_.Representation.character V.ρ g := rfl
    simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
      IrreducibleCharacter.representation_character, invOf_eq_inv,
      smul_eq_mul, Fintype.card_eq_nat_card, hcharV] using hhom
  have hcast : (Module.finrank k (chi.representation ⟶ V) : k) ≠ 0 := by
    rw [← hpair]
    exact hchi
  have hfin : Module.finrank k (chi.representation ⟶ V) ≠ 0 := by
    intro hzero
    apply hcast
    simp [hzero]
  exact (Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hfin))

/-- The kernel of a realized character lies in the kernel of every
irreducible constituent.  This is the representation-theoretic content of
the source lemma `cfker_constt`. -/
theorem ker_le_irreducible_ker_of_isConstituent
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent (ClassFunction.ofRepresentation V.ρ)) :
    V.ρ.ker ≤ chi.representation.ρ.ker := by
  obtain ⟨f, hf⟩ := exists_hom_ne_zero_of_isConstituent V chi hchi
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Mono f := CategoryTheory.mono_of_nonzero_from_simple hf
  let fR := (forget₂ (FDRep k G) (Rep k G)).map f
  have hfR : Function.Injective fR.hom :=
    (Rep.mono_iff_injective fR).mp inferInstance
  intro g hg
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro x
  apply hfR
  change fR.hom (chi.representation.ρ g x) = fR.hom x
  have hinter :=
    _root_.Representation.IntertwiningMap.isIntertwining
      (ρ := ((forget₂ (FDRep k G) (Rep k G)).obj
        chi.representation).ρ)
      (σ := ((forget₂ (FDRep k G) (Rep k G)).obj V).ρ)
      (f := fR.hom) g x
  change fR.hom (chi.representation.ρ g x) =
    V.ρ g (fR.hom x) at hinter
  have hfix : V.ρ g (fR.hom x) = fR.hom x := by
    rw [MonoidHom.mem_ker.mp hg]
    rfl
  exact hinter.trans hfix

end FDRep

namespace IrreducibleCharacter

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [CharZero k]

/-- Source `sub_cfker_constt_Res_irr`: for a normal inducing subgroup,
an ambient-normal subgroup lies in the kernel of a constituent of a
restricted irreducible character exactly when it lies in the kernel of the
ambient irreducible character. -/
theorem sub_ker_constituent_restrict_iff
    (H A : Subgroup G) [H.Normal] [A.Normal] [Fintype H]
    (hAH : A ≤ H)
    (chi : IrreducibleCharacter G k)
    (psi : IrreducibleCharacter H k)
    (hpsi : psi.IsConstituent
      (ClassFunction.restrict H (chi : ClassFunction G k))) :
    A.subgroupOf H ≤ psi.representation.ρ.ker ↔
      A ≤ chi.representation.ρ.ker := by
  let R : FDRep k H :=
    FDRep.of (chi.representation.ρ.comp H.subtype)
  have hcharR : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict H (chi : ClassFunction G k) := by
    rw [FDRep.of_ρ', ← ClassFunction.restrict_ofRepresentation,
      chi.ofRepresentation_representation]
  have hpsiR : psi.IsConstituent
      (ClassFunction.ofRepresentation R.ρ) := by
    rwa [hcharR]
  have hkerRpsi : R.ρ.ker ≤ psi.representation.ρ.ker :=
    FDRep.ker_le_irreducible_ker_of_isConstituent R psi hpsiR
  constructor
  · intro hApsi
    have hAind : A ≤
        (FDRep.induceFromSubgroup H psi.representation).ρ.ker :=
      (FDRep.sub_ker_induceFromSubgroup_iff H A hAH
        psi.representation).2 hApsi
    have hchiInd : chi.IsConstituent
        (ClassFunction.ofRepresentation
          (FDRep.induceFromSubgroup H psi.representation).ρ) := by
      rw [ClassFunction.ofRepresentation_induceFromSubgroup]
      rw [psi.ofRepresentation_representation]
      exact (psi.isConstituent_restrict_iff_induce H chi).1 hpsi
    exact hAind.trans
      (FDRep.ker_le_irreducible_ker_of_isConstituent
        (FDRep.induceFromSubgroup H psi.representation) chi hchiInd)
  · intro hAchi h hh
    apply hkerRpsi
    rw [MonoidHom.mem_ker]
    change chi.representation.ρ (h : G) = 1
    exact MonoidHom.mem_ker.mp (hAchi hh)

/-- Source `sub_cfker_constt_Ind_irr`: the same kernel equivalence when the
ambient irreducible character is presented as a constituent of induction. -/
theorem sub_ker_constituent_induce_iff
    (H A : Subgroup G) [H.Normal] [A.Normal] [Fintype H]
    (hAH : A ≤ H)
    (chi : IrreducibleCharacter G k)
    (psi : IrreducibleCharacter H k)
    (hchi : chi.IsConstituent
      (ClassFunction.induce H (psi : ClassFunction H k))) :
    A.subgroupOf H ≤ psi.representation.ρ.ker ↔
      A ≤ chi.representation.ρ.ker := by
  apply sub_ker_constituent_restrict_iff H A hAH chi psi
  exact (psi.isConstituent_restrict_iff_induce H chi).2 hchi

end IrreducibleCharacter

end

end Submission.OddOrder.PF
