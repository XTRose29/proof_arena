import Submission.OddOrder.PF.Section01.VirtualCharacterPullback
import Submission.OddOrder.PF.Section01.VirtualCharacterInduction
import Submission.OddOrder.PF.Section02.DadeExpansionRestriction
import Submission.OddOrder.PF.Section02.DadeInductionRestrictionConjugation

/-!
# Virtual characters for the induced terms in the Dade expansion

The restriction term attached to a nonempty Dade subset is first transported
to the corresponding subgroup of `G`, then induced to `G`.  Pullback along
the subgroup equivalence and induction from an arbitrary subgroup both act on
the integral lattice of virtual characters, so the resulting pointwise term
is again the realization of an explicit virtual character.

No compatibility with character pairings or star operations is asserted.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

variable {Γ : Type u} [Group Γ]

local instance dadeInducedVirtualCharacterInvertibleCard
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [CharZero k] : Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! The project-level virtual-character pullback and induction wrappers
currently identify the group and coefficient-field universes.  These private
helpers keep their existing constructions while allowing the two universes
to vary independently. -/

private theorem characterPairing_ofRepresentation_eq_finrank_hom_split
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [CharZero k] (V W : FDRep k G) :
    characterPairing (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) =
      (Module.finrank k (W ⟶ V) : k) := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hhom := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcharV (g : G) :
      V.character g = Representation.character V.ρ g := rfl
  have hcharW (g : G) :
      W.character g = Representation.character W.ρ g := rfl
  simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
    invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
    hcharV, hcharW] using hhom

private noncomputable def dadeInducedVirtualCharacterOfFDRep
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (V : FDRep k G) : VirtualCharacter G k :=
  Finsupp.equivFunOnFinite.symm fun chi : IrreducibleCharacter G k =>
    (Module.finrank k (chi.representation ⟶ V) : ℤ)

private theorem realize_dadeInducedVirtualCharacterOfFDRep
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (V : FDRep k G) :
    VirtualCharacter.realize (dadeInducedVirtualCharacterOfFDRep V) =
      ClassFunction.ofRepresentation V.ρ := by
  rw [dadeInducedVirtualCharacterOfFDRep,
    Finsupp.equivFunOnFinite_symm_eq_sum, map_sum]
  simp only [VirtualCharacter.realize_single, Int.cast_natCast]
  rw [← irreducibleCharacterExpansion_eq
    (ClassFunction.ofRepresentation V.ρ), irreducibleCharacterExpansion]
  apply Finset.sum_congr rfl
  intro chi _
  rw [characterPairing_comm, ← chi.ofRepresentation_representation]
  apply congrArg (fun a : k =>
    a • ClassFunction.ofRepresentation chi.representation.ρ)
  exact (characterPairing_ofRepresentation_eq_finrank_hom_split
    V chi.representation).symm

private noncomputable def dadeInducedVirtualCharacterComap
    {H G : Type u} {k : Type v} [Group H] [Group G] [Fintype H]
    [Field k] [IsAlgClosed k] [CharZero k]
    (q : H →* G) : VirtualCharacter G k →+ VirtualCharacter H k :=
  Finsupp.liftAddHom fun chi : IrreducibleCharacter G k =>
    (smulAddHom ℤ (VirtualCharacter H k)).flip
      (dadeInducedVirtualCharacterOfFDRep
        (FDRep.of (chi.representation.ρ.comp q)))

@[simp]
private theorem dadeInducedVirtualCharacterComap_single
    {H G : Type u} {k : Type v} [Group H] [Group G] [Fintype H]
    [Field k] [IsAlgClosed k] [CharZero k]
    (q : H →* G) (chi : IrreducibleCharacter G k) (z : ℤ) :
    dadeInducedVirtualCharacterComap q (Finsupp.single chi z) =
      z • dadeInducedVirtualCharacterOfFDRep
        (FDRep.of (chi.representation.ρ.comp q)) := by
  rw [dadeInducedVirtualCharacterComap, Finsupp.liftAddHom_apply_single]
  rfl

private theorem realize_dadeInducedVirtualCharacterComap
    {H G : Type u} {k : Type v} [Group H] [Group G] [Fintype H]
    [Field k] [IsAlgClosed k] [CharZero k]
    (q : H →* G) (f : VirtualCharacter G k) :
    VirtualCharacter.realize (dadeInducedVirtualCharacterComap q f) =
      ClassFunction.comap q (VirtualCharacter.realize f) := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add chi z f hchi hz ih =>
      have hsingle :
          VirtualCharacter.realize
              (dadeInducedVirtualCharacterComap q
                (Finsupp.single chi z)) =
            ClassFunction.comap q
              (VirtualCharacter.realize (Finsupp.single chi z)) := by
        rw [dadeInducedVirtualCharacterComap_single, map_zsmul,
          realize_dadeInducedVirtualCharacterOfFDRep,
          VirtualCharacter.realize_single,
          ← Int.cast_smul_eq_zsmul k, map_smul]
        congr 1
        rw [← chi.ofRepresentation_representation]
        ext h
        rfl
      calc
        VirtualCharacter.realize
              (dadeInducedVirtualCharacterComap q
                (Finsupp.single chi z + f)) =
            VirtualCharacter.realize
                (dadeInducedVirtualCharacterComap q
                  (Finsupp.single chi z)) +
              VirtualCharacter.realize
                (dadeInducedVirtualCharacterComap q f) := by
                  rw [map_add, map_add]
        _ = ClassFunction.comap q
              (VirtualCharacter.realize (Finsupp.single chi z)) +
            ClassFunction.comap q (VirtualCharacter.realize f) := by
              rw [hsingle, ih]
        _ = ClassFunction.comap q
              (VirtualCharacter.realize (Finsupp.single chi z + f)) := by
                rw [← map_add (ClassFunction.comap q),
                  map_add VirtualCharacter.realize]

private def dadeInducedMultiplicity
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) (chi : IrreducibleCharacter H k)
    (psi : IrreducibleCharacter G k) : ℕ :=
  Module.finrank k
    (FDRep.of (psi.representation.ρ.comp H.subtype) ⟶ chi.representation)

private theorem dadeInducedMultiplicity_cast
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) (chi : IrreducibleCharacter H k)
    (psi : IrreducibleCharacter G k) :
    characterPairing (psi : ClassFunction G k)
        (ClassFunction.induce H (chi : ClassFunction H k)) =
      (dadeInducedMultiplicity H chi psi : k) := by
  letI : Fintype H := Fintype.ofFinite _
  rw [characterPairing_comm, ClassFunction.frobeniusReciprocity H,
    ← chi.ofRepresentation_representation,
    ← psi.ofRepresentation_representation,
    ClassFunction.restrict_ofRepresentation]
  exact characterPairing_ofRepresentation_eq_finrank_hom_split
    chi.representation
    (FDRep.of (psi.representation.ρ.comp H.subtype))

private noncomputable def dadeInduceIrreducible
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) (chi : IrreducibleCharacter H k) :
    VirtualCharacter G k :=
  Finsupp.equivFunOnFinite.symm fun psi : IrreducibleCharacter G k =>
    (dadeInducedMultiplicity H chi psi : ℤ)

private theorem realize_dadeInduceIrreducible
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) (chi : IrreducibleCharacter H k) :
    VirtualCharacter.realize (dadeInduceIrreducible H chi) =
      ClassFunction.induce H (chi : ClassFunction H k) := by
  rw [dadeInduceIrreducible,
    Finsupp.equivFunOnFinite_symm_eq_sum, map_sum]
  simp only [VirtualCharacter.realize_single, Int.cast_natCast]
  rw [← irreducibleCharacterExpansion_eq
    (ClassFunction.induce H (chi : ClassFunction H k)),
    irreducibleCharacterExpansion]
  apply Finset.sum_congr rfl
  intro psi _
  rw [dadeInducedMultiplicity_cast]

private noncomputable def dadeInduceIrreducibleHom
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) (chi : IrreducibleCharacter H k) :
    ℤ →+ VirtualCharacter G k where
  toFun z := z • dadeInduceIrreducible H chi
  map_zero' := zero_zsmul _
  map_add' := fun m n => add_zsmul (dadeInduceIrreducible H chi) m n

private noncomputable def dadeInducedVirtualCharacterInduce
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) : VirtualCharacter H k →+ VirtualCharacter G k :=
  Finsupp.liftAddHom fun chi => dadeInduceIrreducibleHom H chi

@[simp]
private theorem dadeInducedVirtualCharacterInduce_single
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) (chi : IrreducibleCharacter H k) (z : ℤ) :
    dadeInducedVirtualCharacterInduce H (Finsupp.single chi z) =
      z • dadeInduceIrreducible H chi := by
  simp [dadeInducedVirtualCharacterInduce, dadeInduceIrreducibleHom]

private theorem realize_dadeInducedVirtualCharacterInduce
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (H : Subgroup G) (f : VirtualCharacter H k) :
    VirtualCharacter.realize (dadeInducedVirtualCharacterInduce H f) =
      ClassFunction.induce H (VirtualCharacter.realize f) := by
  classical
  induction f using Finsupp.induction with
  | zero => simp
  | single_add chi z f hchi hz ih =>
      calc
        VirtualCharacter.realize
              (dadeInducedVirtualCharacterInduce H
                (Finsupp.single chi z + f)) =
            VirtualCharacter.realize
                (dadeInducedVirtualCharacterInduce H
                  (Finsupp.single chi z)) +
              VirtualCharacter.realize
                (dadeInducedVirtualCharacterInduce H f) := by
                  rw [map_add, map_add]
        _ = ClassFunction.induce H
              (VirtualCharacter.realize
                (Finsupp.single chi z : VirtualCharacter H k)) +
            ClassFunction.induce H (VirtualCharacter.realize f) := by
              rw [dadeInducedVirtualCharacterInduce_single,
                map_zsmul, VirtualCharacter.realize_single,
                realize_dadeInduceIrreducible,
                ← Int.cast_smul_eq_zsmul k, map_smul, ih]
        _ = ClassFunction.induce H
              (VirtualCharacter.realize
                  (Finsupp.single chi z : VirtualCharacter H k) +
                VirtualCharacter.realize f) := by
                  rw [map_add (ClassFunction.induce H)]
        _ = ClassFunction.induce H
              (VirtualCharacter.realize
                (Finsupp.single chi z + f)) := by
                  rw [map_add VirtualCharacter.realize]

/-- The virtual restriction term, transported from the set normalizer to its
copy as a subgroup of `G`. -/
noncomputable def Dade_inducing_vchar_restriction
    [Fintype Γ]
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : VirtualCharacter L k)
    (B : DadeSubset A) :
    VirtualCharacter ((DadeSetNormalizer ddA B).subgroupOf G) k := by
  letI : Fintype ((DadeSetNormalizer ddA B).subgroupOf G) :=
    Fintype.ofFinite _
  exact dadeInducedVirtualCharacterComap
    (Subgroup.subgroupOfEquivOfLe
      (Dade_set_normalizer_le ddA B)).toMonoidHom
    (Dade_vchar_restriction ddA B alpha)

/-- The virtual character of `G` obtained by inducing the transported
restriction term attached to `B`. -/
noncomputable def Dade_ind_vchar_restriction
    [Fintype Γ]
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : VirtualCharacter L k)
    (B : DadeSubset A) : VirtualCharacter G k := by
  classical
  let H : Subgroup G := (DadeSetNormalizer ddA B).subgroupOf G
  letI : Fintype H := Fintype.ofFinite _
  exact dadeInducedVirtualCharacterInduce H
    (Dade_inducing_vchar_restriction ddA alpha B)

/-- The induced Dade restriction term of a realized virtual character is the
realization of the explicitly induced virtual character above. -/
theorem Dade_ind_restriction_vchar
    [Fintype Γ]
    {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : VirtualCharacter L k)
    (B : DadeSubset A) :
    Dade_ind_restriction ddA (VirtualCharacter.realize alpha) B =
      VirtualCharacter.realize
        (Dade_ind_vchar_restriction ddA alpha B) := by
  classical
  let H : Subgroup G := (DadeSetNormalizer ddA B).subgroupOf G
  let e : H ≃* DadeSetNormalizer ddA B :=
    Subgroup.subgroupOfEquivOfLe (Dade_set_normalizer_le ddA B)
  letI : Fintype H := Fintype.ofFinite _
  have hrestr :
      Dade_inducing_restriction ddA
          (VirtualCharacter.realize alpha) B =
      VirtualCharacter.realize
        (Dade_inducing_vchar_restriction ddA alpha B) := by
    change ClassFunction.comap e.toMonoidHom
        (Dade_cfun_restriction ddA B
          (VirtualCharacter.realize alpha)) =
      VirtualCharacter.realize
        (dadeInducedVirtualCharacterComap e.toMonoidHom
          (Dade_vchar_restriction ddA B alpha))
    rw [realize_dadeInducedVirtualCharacterComap]
    rw [Dade_restriction_vchar]
  simpa only [Dade_ind_restriction, Dade_ind_vchar_restriction, H,
      hrestr] using
    (realize_dadeInducedVirtualCharacterInduce H
      (Dade_inducing_vchar_restriction ddA alpha B)).symm

end

end Submission.OddOrder.PF
