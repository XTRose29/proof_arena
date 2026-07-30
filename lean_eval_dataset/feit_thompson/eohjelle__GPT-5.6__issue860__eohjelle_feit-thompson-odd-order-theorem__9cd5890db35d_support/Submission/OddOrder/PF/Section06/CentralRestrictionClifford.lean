import Submission.OddOrder.MathlibSupport.IrreducibleCenterScalar
import Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionFDRep
import Submission.OddOrder.PF.Section01.CharacterCompleteness
import Submission.OddOrder.PF.Section01.FiniteAbelianMulCharacters
import Submission.OddOrder.PF.Section01.Induction

/-!
# Restriction of an irreducible character to a central subgroup

These are the central-subgroup cases of the Clifford-theory interfaces used
in Peterfalvi Section 6.  Schur's lemma supplies the degree-one character on
the central subgroup, and Frobenius reciprocity identifies it from any
nonzero induced-character pairing.

They provide the reusable Lean counterparts needed for the source lemmas
`cfcenter_Res` and `Clifford_Res_sum_cfclass` in the Case-B argument.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical IsMulCommutative

universe u

open Submission.OddOrder.MathlibSupport

/-- The complex scalar representation attached to a multiplicative
character.  This specialization keeps the finite group in universe `u`
while fixing the coefficient field to `ℂ`. -/
private def centralScalarCharacterRepresentation
    {T Q : Type u} [Group T] [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) :
    Representation ℂ T ℂ where
  toFun t := lambda (q t) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro x
    simp
  map_mul' x y := by
    apply LinearMap.ext
    intro z
    simp only [map_mul, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      Module.End.mul_apply]
    ring

@[simp]
private theorem centralScalarCharacterRepresentation_character
    {T Q : Type u} [Group T] [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) (t : T) :
    (FDRep.of (centralScalarCharacterRepresentation q lambda)).character t =
      lambda (q t) := by
  change LinearMap.trace ℂ ℂ
    (lambda (q t) • LinearMap.id) = lambda (q t)
  rw [map_smul, LinearMap.trace_id]
  simp

/-- A universe-polymorphic complex irreducible character realized by a
scalar character line. -/
private noncomputable def irreducibleCharacterOfMulCharComplex
    {T Q : Type u} [Group T] [Fintype T]
    [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) :
    IrreducibleCharacter T ℂ := by
  let rho : Representation ℂ T ℂ :=
    centralScalarCharacterRepresentation q lambda
  letI : Representation.IsIrreducible rho := by
    refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
    · refine ⟨⊥, ⊤, fun h ↦ ?_⟩
      have hone : (1 : ℂ) ∈ (⊥ : Subrepresentation rho) := by
        rw [h]
        trivial
      change (1 : ℂ) = 0 at hone
      exact one_ne_zero hone
    · intro U
      rcases eq_bot_or_eq_top U.toSubmodule with hU | hU
      · left
        apply Subrepresentation.toSubmodule_injective
        change U.toSubmodule = (⊥ : Submodule ℂ ℂ)
        exact hU
      · right
        apply Subrepresentation.toSubmodule_injective
        change U.toSubmodule = (⊤ : Submodule ℂ ℂ)
        exact hU
  let V : FDRep ℂ T := FDRep.of rho
  letI : CategoryTheory.Simple V := simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep V

@[simp]
private theorem irreducibleCharacterOfMulCharComplex_apply
    {T Q : Type u} [Group T] [Fintype T]
    [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) (t : T) :
    irreducibleCharacterOfMulCharComplex q lambda t = lambda (q t) := by
  change (FDRep.of
    (centralScalarCharacterRepresentation q lambda)).character t = _
  exact centralScalarCharacterRepresentation_character q lambda t

/-- Universe-polymorphic complex form of the standard pairing/Hom-space
dimension identity. -/
private theorem characterPairing_ofRepresentation_eq_finrank_hom_complex
    {A : Type u} [Group A] [Fintype A] (V W : FDRep ℂ A) :
    characterPairing (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) =
      (Module.finrank ℂ (W ⟶ V) : ℂ) := by
  letI : Invertible (Nat.card A : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card A : ℂ) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hhom := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcharV (a : A) :
      V.character a = _root_.Representation.character V.ρ a := rfl
  have hcharW (a : A) :
      W.character a = _root_.Representation.character W.ρ a := rfl
  simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
    invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
    hcharV, hcharW] using hhom

namespace IrreducibleCharacter

/-- Multiplicity of `phi` in the restriction of `theta` to `Z`.

This is the universe-polymorphic complex specialization of
`phi.multiplicity (FDRep.of (theta.representation.ρ.comp Z.subtype))`;
the Hom-space definition is unfolded here because the Section 1 wrapper
currently puts the group and coefficient field in one universe. -/
def centralRestrictionMultiplicity
    {K : Type u} [Group K] (Z : Subgroup K)
    (theta : IrreducibleCharacter K ℂ)
    (phi : IrreducibleCharacter Z ℂ) : ℕ :=
  Module.finrank ℂ
    (phi.representation ⟶
      FDRep.of (theta.representation.ρ.comp Z.subtype))

/-- The cast of the central restriction multiplicity is its character
pairing. -/
theorem characterPairing_restrict_eq_centralRestrictionMultiplicity
    {K : Type u} [Group K] [Fintype K] (Z : Subgroup K)
    (theta : IrreducibleCharacter K ℂ)
    (phi : IrreducibleCharacter Z ℂ) :
    characterPairing
        (ClassFunction.restrict Z (theta : ClassFunction K ℂ))
        (phi : ClassFunction Z ℂ) =
      (centralRestrictionMultiplicity Z theta phi : ℂ) := by
  let R : FDRep ℂ Z :=
    FDRep.of (theta.representation.ρ.comp Z.subtype)
  have hR : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict Z (theta : ClassFunction K ℂ) := by
    calc
      ClassFunction.ofRepresentation R.ρ =
          ClassFunction.restrict Z
            (ClassFunction.ofRepresentation theta.representation.ρ) := by
        rfl
      _ = ClassFunction.restrict Z (theta : ClassFunction K ℂ) := by
        rw [theta.ofRepresentation_representation]
  rw [← hR, ← phi.ofRepresentation_representation]
  simpa only [centralRestrictionMultiplicity, R] using
    characterPairing_ofRepresentation_eq_finrank_hom_complex
      R phi.representation

/-- The restriction of an irreducible character to a central subgroup is
its degree times a degree-one irreducible character. -/
theorem exists_central_restriction_eq_degree_smul
    {K : Type u} [Group K] [Fintype K]
    (Z : Subgroup K) (hZcenter : Z ≤ Subgroup.center K)
    (theta : IrreducibleCharacter K ℂ) :
    ∃ (a : ℕ) (phi : IrreducibleCharacter Z ℂ),
      theta 1 = (a : ℂ) ∧
      phi 1 = 1 ∧
      ClassFunction.restrict Z (theta : ClassFunction K ℂ) =
        (a : ℂ) • (phi : ClassFunction Z ℂ) := by
  letI : IsMulCommutative Z := by
    apply isMulCommutative_iff.mpr
    intro x y
    apply Subtype.ext
    exact
      (Subgroup.mem_center_iff.mp (hZcenter x.property) (y : K)).symm
  let V := theta.representation
  let rho : Representation ℂ K V := V.ρ
  letI : CategoryTheory.Simple V := theta.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep V
  let centerHom : Z →* Subgroup.center K :=
    Z.subtype.codRestrict (Subgroup.center K) fun z ↦
      hZcenter z.property
  let lambda : MulChar Z ℂ :=
    { toMonoidHom :=
        (Units.coeHom ℂ).comp
          ((schurCenterScalarCharacter rho).comp centerHom)
      map_nonunit' := by
        intro z hz
        exact (hz (Group.isUnit z)).elim }
  let phi : IrreducibleCharacter Z ℂ :=
    irreducibleCharacterOfMulCharComplex (MonoidHom.id Z) lambda
  let a : ℕ := Module.finrank ℂ V
  have hlambda (z : Z) :
      lambda z =
        (schurCenterScalarCharacter rho (centerHom z) : ℂ) := by
    rfl
  have hphi (z : Z) :
      phi z =
        (schurCenterScalarCharacter rho (centerHom z) : ℂ) := by
    rw [show phi = irreducibleCharacterOfMulCharComplex
      (MonoidHom.id Z) lambda by rfl,
      irreducibleCharacterOfMulCharComplex_apply, MonoidHom.id_apply]
    exact hlambda z
  have hthetaOne : theta 1 = (a : ℂ) := by
    calc
      theta 1 = V.character 1 := by
        simpa only [V] using (theta.representation_character 1).symm
      _ = (Module.finrank ℂ V : ℂ) := FDRep.char_one V
      _ = (a : ℂ) := rfl
  have hphiOne : phi 1 = 1 := by
    rw [hphi]
    simp
  refine ⟨a, phi, hthetaOne, hphiOne, ?_⟩
  ext z
  simp only [ClassFunction.restrict_apply, ClassFunction.smul_apply,
    smul_eq_mul]
  calc
    theta (z : K) = rho.character (centerHom z) := by
      have hcenterHom : (centerHom z : K) = (z : K) := rfl
      rw [hcenterHom]
      change theta (z : K) = V.character (z : K)
      simpa only [V] using
        (theta.representation_character (z : K)).symm
    _ = (Module.finrank ℂ V : ℂ) *
          (schurCenterScalarCharacter rho (centerHom z) : ℂ) :=
      character_center_eq_finrank_mul_schurCenterScalarCharacter
        rho (centerHom z)
    _ = (a : ℂ) * phi z := by rw [hphi]

/-- If a degree-one central character has nonzero pairing after induction,
then it is the central character selected by Schur's lemma.  Consequently
its restriction multiplicity is the ambient irreducible degree. -/
theorem central_restriction_eq_multiplicity_smul_of_induce_pairing_ne_zero
    {K : Type u} [Group K] [Fintype K]
    (Z : Subgroup K) (hZcenter : Z ≤ Subgroup.center K)
    (theta : IrreducibleCharacter K ℂ)
    (phi : IrreducibleCharacter Z ℂ)
    (hpair :
      characterPairing
          (ClassFunction.induce Z (phi : ClassFunction Z ℂ))
          (theta : ClassFunction K ℂ) ≠ 0) :
    theta 1 =
        (IrreducibleCharacter.centralRestrictionMultiplicity Z theta phi : ℂ) ∧
      phi 1 = 1 ∧
      ClassFunction.restrict Z (theta : ClassFunction K ℂ) =
        (IrreducibleCharacter.centralRestrictionMultiplicity Z theta phi : ℂ) •
          (phi : ClassFunction Z ℂ) ∧
      characterPairing
          (ClassFunction.induce Z (phi : ClassFunction Z ℂ))
          (theta : ClassFunction K ℂ) =
        (IrreducibleCharacter.centralRestrictionMultiplicity Z theta phi : ℂ) := by
  letI : Invertible (Nat.card Z : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨a, psi, hthetaOne, hpsiOne, hres⟩ :=
    exists_central_restriction_eq_degree_smul Z hZcenter theta
  have hphiPsiPair :
      characterPairing
          (phi : ClassFunction Z ℂ) (psi : ClassFunction Z ℂ) ≠ 0 := by
    intro hzero
    apply hpair
    rw [ClassFunction.frobeniusReciprocity, hres,
      characterPairing_smul_right, hzero, mul_zero]
  have hphiPsi : phi = psi := by
    by_contra hne
    exact hphiPsiPair
      (IrreducibleCharacter.characterPairing_eq_zero hne)
  subst psi
  have hmultCast :
      (IrreducibleCharacter.centralRestrictionMultiplicity Z theta phi : ℂ) =
        (a : ℂ) := by
    rw [← IrreducibleCharacter.characterPairing_restrict_eq_centralRestrictionMultiplicity,
      hres, characterPairing_smul_left,
      IrreducibleCharacter.characterPairing_self, mul_one]
  have hmult :
      IrreducibleCharacter.centralRestrictionMultiplicity Z theta phi = a :=
    Nat.cast_injective hmultCast
  have hinducePair :
      characterPairing
          (ClassFunction.induce Z (phi : ClassFunction Z ℂ))
          (theta : ClassFunction K ℂ) = (a : ℂ) := by
    rw [ClassFunction.frobeniusReciprocity, hres,
      characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_self, mul_one]
  refine ⟨?_, hpsiOne, ?_, ?_⟩
  · simpa only [hmult] using hthetaOne
  · simpa only [hmult] using hres
  · simpa only [hmult] using hinducePair

end IrreducibleCharacter

end

end Submission.OddOrder.PF
