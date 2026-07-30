import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Complex
import Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic
import Submission.OddOrder.PF.Section01.VirtualCharacterIsometry
import Submission.OddOrder.PF.Section02.DadeAutomorphism
import Submission.OddOrder.PF.Section02.DadeReciprocity
import Submission.OddOrder.PF.Section02.DadeVirtualCharacter
import Submission.OddOrder.PF.Section05.CoherenceBasics
import Submission.OddOrder.PF.Section05.SeqIndGlobal

/-!
# Coherent Dade maps and coefficient automorphisms

This file ports Peterfalvi 5.9, the block of `PFsection5.v` containing
`cfAut_Dade_coherent`, `cfConjC_Dade_coherent`, and
`Dade_irr_sub_conjC` (source lines 1501--1605).

The source counts the irreducible members of a duplicate-free sequence.  In
the set-based coherence interface used here, the first theorem takes the
equivalent datum needed for its chosen irreducible: a distinct irreducible
member of the same family.  The `seqIndD` specialization obtains that datum
from the contragredient pair supplied by odd order.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical Pointwise
open Submission.OddOrder.MathlibSupport

universe u

local instance dadeAutomorphismCoherenceInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- Split-universe form of the degree-at-one identity.  The public helper
currently gives the group and coefficient field the same universe. -/
private theorem irreducibleCharacter_apply_one_eq_finrank
    {H : Type u} [Group H] [Fintype H]
    (chi : IrreducibleCharacter H ℂ) :
    chi 1 = (Module.finrank ℂ chi.representation : ℂ) := by
  rw [← chi.representation_character, FDRep.char_one]

private theorem characterPairing_neg_right_dade
    {H : Type u} [Group H] [Fintype H]
    (phi psi : ClassFunction H ℂ) :
    characterPairing phi (-psi) = -characterPairing phi psi := by
  calc
    characterPairing phi (-psi) =
        characterPairing phi ((-1 : ℂ) • psi) := by
      rw [neg_one_smul ℂ psi]
    _ = (-1 : ℂ) * characterPairing phi psi :=
      characterPairing_smul_right (-1 : ℂ) phi psi
    _ = -characterPairing phi psi := neg_one_mul _

private theorem characterPairing_sub_right_dade
    {H : Type u} [Group H] [Fintype H]
    (phi psi theta : ClassFunction H ℂ) :
    characterPairing phi (psi - theta) =
      characterPairing phi psi - characterPairing phi theta := by
  rw [sub_eq_add_neg, characterPairing_add_right,
    characterPairing_neg_right_dade, sub_eq_add_neg]

/-- Complex conjugation as a coefficient-field automorphism. -/
abbrev complexConjugation : ℂ ≃+* ℂ :=
  Complex.conjAe.toRingEquiv

/-- Pointwise complex conjugation of a complex class function. -/
def cfConjC {H : Type u} [Group H] :
    ClassFunction H ℂ →+ ClassFunction H ℂ :=
  ClassFunction.mapRingHom complexConjugation.toRingHom

@[simp]
theorem cfConjC_apply {H : Type u} [Group H]
    (phi : ClassFunction H ℂ) (x : H) :
    cfConjC phi x = star (phi x) :=
  rfl

@[simp]
theorem cfConjC_involutive {H : Type u} [Group H]
    (phi : ClassFunction H ℂ) :
    cfConjC (cfConjC phi) = phi := by
  ext x
  simp [cfConjC]

@[simp]
theorem cfConjC_irreducible {H : Type u} [Group H] [Fintype H]
    (chi : IrreducibleCharacter H ℂ) :
    cfConjC (chi : ClassFunction H ℂ) =
      (IrreducibleCharacter.mapRingEquiv complexConjugation chi :
        ClassFunction H ℂ) := by
  exact ClassFunction.mapRingHom_irreducible complexConjugation chi

private theorem mapRingHom_smul
    {H : Type u} [Group H] (sigma : ℂ ≃+* ℂ)
    (a : ℂ) (phi : ClassFunction H ℂ) :
    ClassFunction.mapRingHom sigma.toRingHom (a • phi) =
      sigma a • ClassFunction.mapRingHom sigma.toRingHom phi := by
  ext x
  simp [map_mul]

private theorem cfConjC_intCast_smul
    {H : Type u} [Group H] (n : ℤ) (phi : ClassFunction H ℂ) :
    cfConjC ((n : ℂ) • phi) = (n : ℂ) • cfConjC phi := by
  ext x
  simp [cfConjC, map_mul]

private theorem irreducibleCharacter_finrank_pos
    {H : Type u} [Group H] [Fintype H]
    (chi : IrreducibleCharacter H ℂ) :
    0 < Module.finrank ℂ chi.representation := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  exact Module.finrank_pos

private theorem coherent_image_signed_irreducible
    {L G : Type u} [Group L] [Fintype L] [Group G] [Fintype G]
    {S : Set (ClassFunction L ℂ)}
    {tau nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hnu : coherent_with S (nonidentitySet L) tau nu)
    (chi : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈ S) :
    ∃ (psi : IrreducibleCharacter G ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        nu (chi : ClassFunction L ℂ) =
          (epsilon : ℂ) • (psi : ClassFunction G ℂ) := by
  have hspan : (chi : ClassFunction L ℂ) ∈ AddSubgroup.closure S :=
    AddSubgroup.subset_closure hchi
  obtain ⟨z, hz⟩ := hnu.mapsToVirtual _ hspan
  have hpair :
      characterPairing (VirtualCharacter.realize z)
          (VirtualCharacter.realize z) = 1 := by
    rw [hz, hnu.isometry _ hspan _ hspan,
      IrreducibleCharacter.characterPairing_self]
  have hnorm : normSq z = 1 := by
    apply Int.cast_injective (α := ℂ)
    calc
      (normSq z : ℂ) =
          characterPairing (VirtualCharacter.realize z)
            (VirtualCharacter.realize z) := by
        simpa [normSq] using
          (VirtualCharacter.characterPairing_realize z z).symm
      _ = (1 : ℂ) := hpair
      _ = ((1 : ℤ) : ℂ) := by norm_num
  obtain ⟨psi, epsilon, hepsilon, hsingle⟩ :=
    eq_signed_single_of_normSq_eq_one z hnorm
  refine ⟨psi, epsilon, hepsilon, ?_⟩
  calc
    nu (chi : ClassFunction L ℂ) = VirtualCharacter.realize z := hz.symm
    _ = (epsilon : ℂ) • (psi : ClassFunction G ℂ) := by
      rw [hsingle, VirtualCharacter.realize_single]

private def weightedIrreducibleDifference
    {H : Type u} [Group H] [Fintype H]
    (chi eta : IrreducibleCharacter H ℂ) : ClassFunction H ℂ :=
  (Module.finrank ℂ eta.representation : ℂ) •
      (chi : ClassFunction H ℂ) -
    (Module.finrank ℂ chi.representation : ℂ) •
      (eta : ClassFunction H ℂ)

private theorem weightedIrreducibleDifference_mem_closure
    {H : Type u} [Group H] [Fintype H]
    {S : Set (ClassFunction H ℂ)}
    {chi eta : IrreducibleCharacter H ℂ}
    (hchi : (chi : ClassFunction H ℂ) ∈ S)
    (heta : (eta : ClassFunction H ℂ) ∈ S) :
    weightedIrreducibleDifference chi eta ∈ AddSubgroup.closure S := by
  rw [weightedIrreducibleDifference]
  apply (AddSubgroup.closure S).sub_mem
  · rw [Nat.cast_smul_eq_nsmul]
    exact (AddSubgroup.closure S).nsmul_mem
      (AddSubgroup.subset_closure hchi) _
  · rw [Nat.cast_smul_eq_nsmul]
    exact (AddSubgroup.closure S).nsmul_mem
      (AddSubgroup.subset_closure heta) _

private theorem weightedIrreducibleDifference_supported
    {H : Type u} [Group H] [Fintype H]
    (chi eta : IrreducibleCharacter H ℂ) :
    weightedIrreducibleDifference chi eta ∈
      ClassFunction.supportedOn (nonidentitySet H) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hx1 : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp [weightedIrreducibleDifference,
    irreducibleCharacter_apply_one_eq_finrank, mul_comm]

private theorem coherent_weightedIrreducibleDifference
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L : Subgroup Gamma} {A : Set Gamma}
    (ddA : DadeHypothesis G L A)
    {S : Set (ClassFunction L ℂ)}
    {nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hnu : coherent_with S (nonidentitySet L) (Dade ddA) nu)
    (chi eta : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈ S)
    (heta : (eta : ClassFunction L ℂ) ∈ S) :
    nu (weightedIrreducibleDifference chi eta) =
      Dade ddA (weightedIrreducibleDifference chi eta) :=
  hnu.agrees _
    (weightedIrreducibleDifference_mem_closure hchi heta)
    (weightedIrreducibleDifference_supported chi eta)

private theorem coherent_signed_images_same_sign
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L : Subgroup Gamma} {A : Set Gamma}
    (ddA : DadeHypothesis G L A)
    {S : Set (ClassFunction L ℂ)}
    {nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hnu : coherent_with S (nonidentitySet L) (Dade ddA) nu)
    {chi eta : IrreducibleCharacter L ℂ}
    (hchi : (chi : ClassFunction L ℂ) ∈ S)
    (heta : (eta : ClassFunction L ℂ) ∈ S)
    {alpha beta : IrreducibleCharacter G ℂ}
    {epsilon delta : ℤ}
    (hepsilon : IsSign epsilon) (hdelta : IsSign delta)
    (hchiImage : nu (chi : ClassFunction L ℂ) =
      (epsilon : ℂ) • (alpha : ClassFunction G ℂ))
    (hetaImage : nu (eta : ClassFunction L ℂ) =
      (delta : ℂ) • (beta : ClassFunction G ℂ)) :
    epsilon = delta := by
  have hzero :
      (nu (weightedIrreducibleDifference chi eta)) (1 : G) = 0 := by
    rw [coherent_weightedIrreducibleDifference ddA hnu chi eta hchi heta,
      Dade1]
  simp only [weightedIrreducibleDifference, map_sub, map_smul,
    hchiImage, hetaImage, ClassFunction.sub_apply,
    ClassFunction.smul_apply, smul_eq_mul,
    irreducibleCharacter_apply_one_eq_finrank] at hzero
  have hsumPos :
      0 < Module.finrank ℂ eta.representation *
            Module.finrank ℂ alpha.representation +
          Module.finrank ℂ chi.representation *
            Module.finrank ℂ beta.representation :=
    Nat.add_pos_left
      (Nat.mul_pos (irreducibleCharacter_finrank_pos eta)
        (irreducibleCharacter_finrank_pos alpha)) _
  rcases hepsilon with rfl | rfl <;>
    rcases hdelta with rfl | rfl
  · rfl
  · exfalso
    have hcast :
        ((Module.finrank ℂ eta.representation *
              Module.finrank ℂ alpha.representation +
            Module.finrank ℂ chi.representation *
              Module.finrank ℂ beta.representation : ℕ) : ℂ) = 0 := by
      simpa only [Int.cast_one, Int.cast_neg, one_mul, neg_mul,
        mul_neg, sub_neg_eq_add, Nat.cast_add, Nat.cast_mul] using hzero
    exact (Nat.cast_ne_zero.mpr hsumPos.ne') hcast
  · exfalso
    have hcast :
        -((Module.finrank ℂ eta.representation *
              Module.finrank ℂ alpha.representation +
            Module.finrank ℂ chi.representation *
              Module.finrank ℂ beta.representation : ℕ) : ℂ) = 0 := by
      simpa only [Int.cast_one, Int.cast_neg, one_mul, neg_mul,
        mul_neg, sub_eq_add_neg, neg_add, Nat.cast_add,
        Nat.cast_mul] using hzero
    exact (Nat.cast_ne_zero.mpr hsumPos.ne') (neg_eq_zero.mp hcast)
  · rfl

private theorem coherent_signed_images_distinct
    {L G : Type u} [Group L] [Fintype L] [Group G] [Fintype G]
    {S : Set (ClassFunction L ℂ)}
    {tau nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hnu : coherent_with S (nonidentitySet L) tau nu)
    {chi eta : IrreducibleCharacter L ℂ}
    (hchi : (chi : ClassFunction L ℂ) ∈ S)
    (heta : (eta : ClassFunction L ℂ) ∈ S)
    (hchiEta : chi ≠ eta)
    {alpha beta : IrreducibleCharacter G ℂ} {epsilon : ℤ}
    (hepsilon : IsSign epsilon)
    (hchiImage : nu (chi : ClassFunction L ℂ) =
      (epsilon : ℂ) • (alpha : ClassFunction G ℂ))
    (hetaImage : nu (eta : ClassFunction L ℂ) =
      (epsilon : ℂ) • (beta : ClassFunction G ℂ)) :
    alpha ≠ beta := by
  intro hab
  subst beta
  have hpair := hnu.isometry _ (AddSubgroup.subset_closure hchi)
    _ (AddSubgroup.subset_closure heta)
  rw [hchiImage, hetaImage] at hpair
  rcases hepsilon with rfl | rfl <;>
    norm_num [characterPairing_smul_left, characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_eq_ite, hchiEta] at hpair

private theorem mapRingEquiv_finrank
    {H : Type u} [Group H] [Fintype H]
    (sigma : ℂ ≃+* ℂ) (chi : IrreducibleCharacter H ℂ) :
    Module.finrank ℂ
        (IrreducibleCharacter.mapRingEquiv sigma chi).representation =
      Module.finrank ℂ chi.representation := by
  apply Nat.cast_injective (R := ℂ)
  calc
    (Module.finrank ℂ
        (IrreducibleCharacter.mapRingEquiv sigma chi).representation : ℂ) =
        IrreducibleCharacter.mapRingEquiv sigma chi 1 := by
      rw [irreducibleCharacter_apply_one_eq_finrank]
    _ = sigma (chi 1) := IrreducibleCharacter.mapRingEquiv_apply sigma chi 1
    _ = (Module.finrank ℂ chi.representation : ℂ) := by
      rw [irreducibleCharacter_apply_one_eq_finrank, map_natCast]

private theorem mapRingHom_weightedIrreducibleDifference
    {H : Type u} [Group H] [Fintype H]
    (sigma : ℂ ≃+* ℂ)
    (chi eta : IrreducibleCharacter H ℂ) :
    ClassFunction.mapRingHom sigma.toRingHom
        (weightedIrreducibleDifference chi eta) =
      weightedIrreducibleDifference
        (IrreducibleCharacter.mapRingEquiv sigma chi)
        (IrreducibleCharacter.mapRingEquiv sigma eta) := by
  ext x
  simp [weightedIrreducibleDifference, map_mul,
    mapRingEquiv_finrank, IrreducibleCharacter.mapRingEquiv_apply]

private theorem cfAut_coherent_weighted_difference
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L : Subgroup Gamma} {A : Set Gamma}
    (ddA : DadeHypothesis G L A)
    {S : Set (ClassFunction L ℂ)}
    {nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hnu : coherent_with S (nonidentitySet L) (Dade ddA) nu)
    (sigma : ℂ ≃+* ℂ)
    (chi eta : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈ S)
    (heta : (eta : ClassFunction L ℂ) ∈ S)
    (hchiSigma :
      (IrreducibleCharacter.mapRingEquiv sigma chi :
        ClassFunction L ℂ) ∈ S)
    (hetaSigma :
      (IrreducibleCharacter.mapRingEquiv sigma eta :
        ClassFunction L ℂ) ∈ S) :
    ClassFunction.mapRingHom sigma.toRingHom
        (nu (weightedIrreducibleDifference chi eta)) =
      nu (weightedIrreducibleDifference
        (IrreducibleCharacter.mapRingEquiv sigma chi)
        (IrreducibleCharacter.mapRingEquiv sigma eta)) := by
  calc
    ClassFunction.mapRingHom sigma.toRingHom
        (nu (weightedIrreducibleDifference chi eta)) =
        ClassFunction.mapRingHom sigma.toRingHom
          (Dade ddA (weightedIrreducibleDifference chi eta)) := by
      rw [coherent_weightedIrreducibleDifference ddA hnu chi eta hchi heta]
    _ = Dade ddA
        (ClassFunction.mapRingHom sigma.toRingHom
          (weightedIrreducibleDifference chi eta)) :=
      (Dade_aut ddA sigma.toRingHom
        (weightedIrreducibleDifference chi eta)).symm
    _ = Dade ddA (weightedIrreducibleDifference
        (IrreducibleCharacter.mapRingEquiv sigma chi)
        (IrreducibleCharacter.mapRingEquiv sigma eta)) := by
      rw [mapRingHom_weightedIrreducibleDifference]
    _ = nu (weightedIrreducibleDifference
        (IrreducibleCharacter.mapRingEquiv sigma chi)
        (IrreducibleCharacter.mapRingEquiv sigma eta)) :=
      (coherent_weightedIrreducibleDifference ddA hnu _ _
        hchiSigma hetaSigma).symm

private theorem first_eq_of_weighted_irreducible_difference_eq
    {H : Type u} [Group H] [Fintype H]
    (m n : ℕ) (hm : 0 < m) (hn : 0 < n)
    {alpha beta gamma delta : IrreducibleCharacter H ℂ}
    (hab : alpha ≠ beta)
    (heq :
      (m : ℂ) • (alpha : ClassFunction H ℂ) -
          (n : ℂ) • (beta : ClassFunction H ℂ) =
        (m : ℂ) • (gamma : ClassFunction H ℂ) -
          (n : ℂ) • (delta : ClassFunction H ℂ)) :
    alpha = gamma := by
  have hpair := congrArg
    (fun phi : ClassFunction H ℂ ↦
      characterPairing (alpha : ClassFunction H ℂ) phi) heq
  rw [characterPairing_sub_right_dade, characterPairing_sub_right_dade,
    characterPairing_smul_right, characterPairing_smul_right,
    characterPairing_smul_right, characterPairing_smul_right,
    IrreducibleCharacter.characterPairing_self,
    IrreducibleCharacter.characterPairing_eq_zero hab] at hpair
  simp only [mul_one, mul_zero, sub_zero] at hpair
  by_contra hac
  have hac0 := IrreducibleCharacter.characterPairing_eq_zero hac
  by_cases had : alpha = delta
  · subst delta
    rw [hac0, IrreducibleCharacter.characterPairing_self] at hpair
    simp only [mul_zero, mul_one, zero_sub] at hpair
    have hcast : ((m + n : ℕ) : ℂ) = 0 := by
      rw [Nat.cast_add]
      exact eq_neg_iff_add_eq_zero.mp hpair
    exact (Nat.cast_ne_zero.mpr (Nat.add_pos_left hm n).ne') hcast
  · have had0 := IrreducibleCharacter.characterPairing_eq_zero had
    rw [hac0, had0] at hpair
    simp only [mul_zero, sub_self] at hpair
    exact (Nat.cast_ne_zero.mpr hm.ne') hpair

/-- Peterfalvi 5.9(a).  A coherent extension of the Dade isometry commutes
with a coefficient automorphism on every irreducible member of a
nontrivial automorphism-stable family. -/
theorem cfAut_Dade_coherent
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L : Subgroup Gamma} {A : Set Gamma}
    (ddA : DadeHypothesis G L A)
    {S : Set (ClassFunction L ℂ)}
    {nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hnu : coherent_with S (nonidentitySet L) (Dade ddA) nu)
    (sigma : ℂ ≃+* ℂ)
    (chi : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈ S)
    (hnontrivial : ∃ eta : IrreducibleCharacter L ℂ,
      (eta : ClassFunction L ℂ) ∈ S ∧ eta ≠ chi)
    (hclosed : ∀ phi ∈ S,
      ClassFunction.mapRingHom sigma.toRingHom phi ∈ S) :
    ClassFunction.mapRingHom sigma.toRingHom
        (nu (chi : ClassFunction L ℂ)) =
      nu (IrreducibleCharacter.mapRingEquiv sigma chi :
        ClassFunction L ℂ) := by
  obtain ⟨eta, heta, hetaChi⟩ := hnontrivial
  have hchiSigma :
      (IrreducibleCharacter.mapRingEquiv sigma chi :
        ClassFunction L ℂ) ∈ S := by
    rw [← ClassFunction.mapRingHom_irreducible]
    exact hclosed _ hchi
  have hetaSigma :
      (IrreducibleCharacter.mapRingEquiv sigma eta :
        ClassFunction L ℂ) ∈ S := by
    rw [← ClassFunction.mapRingHom_irreducible]
    exact hclosed _ heta
  obtain ⟨alpha, epsilon, hepsilon, hchiImage⟩ :=
    coherent_image_signed_irreducible hnu chi hchi
  obtain ⟨beta, delta, hdelta, hetaImage⟩ :=
    coherent_image_signed_irreducible hnu eta heta
  have hepsilonDelta := coherent_signed_images_same_sign ddA hnu
    hchi heta hepsilon hdelta hchiImage hetaImage
  subst delta
  obtain ⟨gamma, epsilonGamma, hepsilonGamma, hchiSigmaImage⟩ :=
    coherent_image_signed_irreducible hnu
      (IrreducibleCharacter.mapRingEquiv sigma chi) hchiSigma
  have hepsilonGammaEq := coherent_signed_images_same_sign ddA hnu
    hchiSigma hchi hepsilonGamma hepsilon hchiSigmaImage hchiImage
  subst epsilonGamma
  obtain ⟨delta, epsilonDelta, hepsilonDelta, hetaSigmaImage⟩ :=
    coherent_image_signed_irreducible hnu
      (IrreducibleCharacter.mapRingEquiv sigma eta) hetaSigma
  have hepsilonDeltaEq := coherent_signed_images_same_sign ddA hnu
    hetaSigma hchi hepsilonDelta hepsilon hetaSigmaImage hchiImage
  subst epsilonDelta
  have hab : alpha ≠ beta :=
    coherent_signed_images_distinct hnu hchi heta hetaChi.symm
      hepsilon hchiImage hetaImage
  have hcompat := cfAut_coherent_weighted_difference ddA hnu sigma
    chi eta hchi heta hchiSigma hetaSigma
  have htarget :
      (Module.finrank ℂ eta.representation : ℂ) •
          (IrreducibleCharacter.mapRingEquiv sigma alpha :
            ClassFunction G ℂ) -
        (Module.finrank ℂ chi.representation : ℂ) •
          (IrreducibleCharacter.mapRingEquiv sigma beta :
            ClassFunction G ℂ) =
      (Module.finrank ℂ eta.representation : ℂ) •
          (gamma : ClassFunction G ℂ) -
        (Module.finrank ℂ chi.representation : ℂ) •
          (delta : ClassFunction G ℂ) := by
    have hepsilon' := hepsilon
    ext x
    have hx := congrArg (fun phi : ClassFunction G ℂ ↦ phi x) hcompat
    rcases hepsilon' with rfl | rfl
    · simpa [weightedIrreducibleDifference, hchiImage, hetaImage,
        hchiSigmaImage, hetaSigmaImage,
        ClassFunction.mapRingHom_apply,
        IrreducibleCharacter.mapRingEquiv_apply,
        mapRingEquiv_finrank, map_mul] using hx
    · have hxneg := congrArg Neg.neg hx
      simpa [weightedIrreducibleDifference, hchiImage, hetaImage,
        hchiSigmaImage, hetaSigmaImage,
        ClassFunction.mapRingHom_apply,
        IrreducibleCharacter.mapRingEquiv_apply,
        mapRingEquiv_finrank, map_mul, sub_eq_add_neg,
        add_comm] using hxneg
  have habSigma :
      IrreducibleCharacter.mapRingEquiv sigma alpha ≠
        IrreducibleCharacter.mapRingEquiv sigma beta := by
    intro h
    apply hab
    exact (IrreducibleCharacter.equivOfRingEquiv sigma).injective h
  have hfirst :
      IrreducibleCharacter.mapRingEquiv sigma alpha = gamma :=
    first_eq_of_weighted_irreducible_difference_eq
      (Module.finrank ℂ eta.representation)
      (Module.finrank ℂ chi.representation)
      (irreducibleCharacter_finrank_pos eta)
      (irreducibleCharacter_finrank_pos chi) habSigma htarget
  rw [hchiImage, hchiSigmaImage, mapRingHom_smul,
    ClassFunction.mapRingHom_irreducible, hfirst]
  simp

/-- Peterfalvi 5.9(a), specialized to complex conjugation on an odd-order
normally induced family. -/
theorem cfConjC_Dade_coherent
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L : Subgroup Gamma} {A : Set Gamma}
    (ddA : DadeHypothesis G L A)
    (K : Subgroup L) [K.Normal] [Fintype K]
    (H M : Subgroup K)
    {nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ}
    (hnu : coherent_with
      (↑(seqIndD (k := ℂ) K H M) : Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    (hoddG : Odd (Nat.card G))
    (chi : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈ seqIndD (k := ℂ) K H M) :
    cfConjC (nu (chi : ClassFunction L ℂ)) =
      nu (IrreducibleCharacter.mapRingEquiv complexConjugation chi :
        ClassFunction L ℂ) := by
  have hoddL : Odd (Nat.card L) :=
    Odd.of_dvd_nat hoddG (Subgroup.card_dvd_of_le ddA.2.1)
  apply cfAut_Dade_coherent ddA hnu complexConjugation chi hchi
  · refine ⟨IrreducibleCharacter.dual chi, ?_, ?_⟩
    · rw [← ClassFunction.inverseLinear_irreducible]
      exact seqInd_inverse_mem (k := ℂ) K H M hchi
    · intro heq
      apply seqInd_conjC_neq (k := ℂ) K hoddL H M hchi
      rw [ClassFunction.inverseLinear_irreducible, heq]
  · intro phi hphi
    exact cfAut_seqInd (k := ℂ) complexConjugation K H M hphi

/-- A complex character takes conjugate values on inverse elements.  This
is the finite-order trace argument needed to compare the source's star
pairing with the inverse-argument pairing used by the Lean character API. -/
private theorem representation_character_inv_eq_star
    {H : Type u} {V : Type*} [Group H] [Fintype H]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ H V) (x : H) :
    rho.character x⁻¹ = star (rho.character x) := by
  let n := Nat.card H
  have hn : n ≠ 0 := Nat.card_pos.ne'
  letI : NeZero n := ⟨hn⟩
  let omega₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have homega₀ : IsPrimitiveRoot omega₀ n := by
    simpa only [omega₀] using Complex.isPrimitiveRoot_exp n hn
  let omega : ℂˣ := Units.mk0 omega₀ (homega₀.ne_zero hn)
  have homega : IsPrimitiveRoot omega n := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [omega] using homega₀
  have homegaNorm : ‖(omega : ℂ)‖ = 1 := by
    simpa [omega] using homega₀.norm'_eq_one hn
  have homegaPow : (omega : ℂ) ^ n = 1 := by
    exact congrArg (fun z : ℂˣ ↦ (z : ℂ)) homega.pow_eq_one
  have hpow : (rho x) ^ n = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hxinvPow : x⁻¹ = x ^ (n - 1) := by
    exact inv_eq_of_mul_eq_one_right (by
      rw [mul_pow_sub_one hn, pow_card_eq_one'])
  have hinvPow : rho x⁻¹ = (rho x) ^ (n - 1) := by
    rw [hxinvPow, map_pow]
  have hweight (i : ZMod n) :
      (primitiveRootUnitWeight homega i : ℂ) =
        (omega : ℂ) ^ i.val := by
    conv_lhs =>
      rw [← ZMod.natCast_zmod_val i,
        primitiveRootUnitWeight_natCast]
    rfl
  have hweightStar (i : ZMod n) :
      (starRingEnd ℂ) (primitiveRootUnitWeight homega i : ℂ) =
        (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) := by
    let w : ℂ := primitiveRootUnitWeight homega i
    have hwNorm : ‖w‖ = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        norm_pow, homegaNorm, one_pow]
    have hwPow : w ^ n = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        ← pow_mul, Nat.mul_comm, pow_mul, homegaPow, one_pow]
    have hwInv : w⁻¹ = w ^ (n - 1) :=
      inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, hwPow])
    change (starRingEnd ℂ) w = w ^ (n - 1)
    rw [← Complex.inv_eq_conj hwNorm, hwInv]
  have htraceOne :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho x) hpow 1
  have htracePred :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho x) hpow (n - 1)
  simp only [pow_one] at htraceOne
  calc
    rho.character x⁻¹ = LinearMap.trace ℂ V (rho x⁻¹) := rfl
    _ = LinearMap.trace ℂ V ((rho x) ^ (n - 1)) := by rw [hinvPow]
    _ = ∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho x)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) :=
      htracePred
    _ = star (∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho x)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ)) := by
      change _ = (starRingEnd ℂ) (∑ i : ZMod n,
        (Module.finrank ℂ
            (Module.End.eigenspace (rho x)
              (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
          (primitiveRootUnitWeight homega i : ℂ))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_natCast, hweightStar]
    _ = star (LinearMap.trace ℂ V (rho x)) := by rw [htraceOne]
    _ = star (rho.character x) := rfl

private theorem irreducibleCharacter_apply_inv_eq_star
    {H : Type u} [Group H] [Fintype H]
    (chi : IrreducibleCharacter H ℂ) (x : H) :
    chi x⁻¹ = star (chi x) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representation_character_inv_eq_star
    chi.representation.ρ x

private theorem star_realize_apply_eq_inverse
    {H : Type u} [Group H] [Fintype H]
    (z : VirtualCharacter H ℂ) (x : H) :
    star (VirtualCharacter.realize z x) =
      VirtualCharacter.realize z x⁻¹ := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add chi n z hchi hn ih =>
      rw [VirtualCharacter.realize_add,
        VirtualCharacter.realize_single]
      change (starRingEnd ℂ) ((n : ℂ) * chi.val x +
          VirtualCharacter.realize z x) =
        (n : ℂ) * chi.val x⁻¹ +
          VirtualCharacter.realize z x⁻¹
      have hchiStar :=
        (irreducibleCharacter_apply_inv_eq_star chi x).symm
      change (starRingEnd ℂ) (chi.val x) = chi.val x⁻¹ at hchiStar
      have ih' := ih
      change (starRingEnd ℂ) (VirtualCharacter.realize z x) =
        VirtualCharacter.realize z x⁻¹ at ih'
      rw [map_add, map_mul, map_intCast, ih', hchiStar]

private theorem starCharacterPairing_realize_eq_characterPairing
    {H : Type u} [Group H] [Fintype H]
    (z w : VirtualCharacter H ℂ) :
    starCharacterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) =
      characterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) := by
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  exact star_realize_apply_eq_inverse w

private theorem coeffSum_eq_zero_of_normSq_eq_two_of_realize_one_eq_zero
    {H : Type u} [Group H] [Fintype H]
    (z : VirtualCharacter H ℂ) (hnorm : normSq z = 2)
    (hone : VirtualCharacter.realize z 1 = 0) :
    coeffSum z = 0 := by
  obtain ⟨chi, psi, epsilon, delta, hne, hepsilon, hdelta, rfl⟩ :=
    eq_sum_signed_singles_of_normSq_eq_two z hnorm
  have hchi :
      chi 1 = (Module.finrank ℂ chi.representation : ℂ) :=
    irreducibleCharacter_apply_one_eq_finrank chi
  have hpsi :
      psi 1 = (Module.finrank ℂ psi.representation : ℂ) :=
    irreducibleCharacter_apply_one_eq_finrank psi
  have hpos :
      0 < Module.finrank ℂ chi.representation +
        Module.finrank ℂ psi.representation :=
    Nat.add_pos_left (irreducibleCharacter_finrank_pos chi) _
  rcases hepsilon with rfl | rfl <;>
    rcases hdelta with rfl | rfl
  · exfalso
    simp only [VirtualCharacter.realize_add,
      VirtualCharacter.realize_single, ClassFunction.add_apply,
      ClassFunction.smul_apply, Int.cast_one, one_smul,
      hchi, hpsi] at hone
    have hcast :
        ((Module.finrank ℂ chi.representation +
          Module.finrank ℂ psi.representation : ℕ) : ℂ) = 0 := by
      simpa only [Nat.cast_add] using hone
    exact (Nat.cast_ne_zero.mpr hpos.ne') hcast
  · simp [coeffSum_add, coeffSum_neg, coeffSum_single]
  · simp [coeffSum_add, coeffSum_neg, coeffSum_single]
  · exfalso
    simp only [VirtualCharacter.realize_add,
      VirtualCharacter.realize_single, ClassFunction.add_apply,
      ClassFunction.smul_apply, Int.cast_neg, Int.cast_one,
      neg_smul, one_smul, Pi.neg_apply, hchi, hpsi] at hone
    have hcast :
        -((Module.finrank ℂ chi.representation +
          Module.finrank ℂ psi.representation : ℕ) : ℂ) = 0 := by
      simpa only [Nat.cast_add, neg_add] using hone
    exact (neg_ne_zero.mpr (Nat.cast_ne_zero.mpr hpos.ne')) hcast

private theorem cfConjC_first_eq_second_of_anti
    {H : Type u} [Group H] [Fintype H]
    (alpha beta : IrreducibleCharacter H ℂ) (hab : alpha ≠ beta)
    (hanti : cfConjC
        ((alpha : ClassFunction H ℂ) -
          (beta : ClassFunction H ℂ)) =
      -((alpha : ClassFunction H ℂ) -
          (beta : ClassFunction H ℂ))) :
    IrreducibleCharacter.mapRingEquiv complexConjugation alpha = beta := by
  have habConj :
      IrreducibleCharacter.mapRingEquiv complexConjugation alpha ≠
        IrreducibleCharacter.mapRingEquiv complexConjugation beta := by
    intro h
    apply hab
    exact (IrreducibleCharacter.equivOfRingEquiv
      complexConjugation).injective h
  have hdiff :
      (IrreducibleCharacter.mapRingEquiv complexConjugation alpha :
          ClassFunction H ℂ) -
        (IrreducibleCharacter.mapRingEquiv complexConjugation beta :
          ClassFunction H ℂ) =
      (beta : ClassFunction H ℂ) -
        (alpha : ClassFunction H ℂ) := by
    simpa only [map_sub, cfConjC_irreducible, neg_sub] using hanti
  have hpair := congrArg
    (fun phi : ClassFunction H ℂ ↦
      characterPairing
        (IrreducibleCharacter.mapRingEquiv complexConjugation alpha :
          ClassFunction H ℂ) phi) hdiff
  rw [characterPairing_sub_right_dade, characterPairing_sub_right_dade,
    IrreducibleCharacter.characterPairing_self,
    IrreducibleCharacter.characterPairing_eq_zero habConj] at hpair
  simp only [sub_zero] at hpair
  by_contra haBeta
  have hbetaZero :=
    IrreducibleCharacter.characterPairing_eq_zero haBeta
  by_cases haAlpha :
      IrreducibleCharacter.mapRingEquiv complexConjugation alpha = alpha
  · rw [hbetaZero, haAlpha,
      IrreducibleCharacter.characterPairing_self] at hpair
    norm_num at hpair
  · have halphaZero :=
      IrreducibleCharacter.characterPairing_eq_zero haAlpha
    rw [hbetaZero, halphaZero] at hpair
    norm_num at hpair

private theorem cancel_cfConjC_sign_anti
    {H : Type u} [Group H]
    {phi : ClassFunction H ℂ} {epsilon : ℤ}
    (hepsilon : IsSign epsilon)
    (hanti : cfConjC ((epsilon : ℂ) • phi) =
      -((epsilon : ℂ) • phi)) :
    cfConjC phi = -phi := by
  rcases hepsilon with rfl | rfl
  · simpa [cfConjC_intCast_smul] using hanti
  · have hneg : -cfConjC phi = phi := by
      rw [cfConjC_intCast_smul] at hanti
      have hanti' :
          (-1 : ℂ) • cfConjC phi = -((-1 : ℂ) • phi) := by
        simpa only [Int.cast_neg, Int.cast_one] using hanti
      calc
        -cfConjC phi = (-1 : ℂ) • cfConjC phi :=
          (neg_one_smul ℂ (cfConjC phi)).symm
        _ = -((-1 : ℂ) • phi) := hanti'
        _ = -(-phi) := congrArg Neg.neg (neg_one_smul ℂ phi)
        _ = phi := neg_neg phi
    simpa using congrArg Neg.neg hneg

/-- Peterfalvi 5.9(b).  The Dade image of the difference between an
irreducible character and its complex conjugate is again such an oriented
difference. -/
theorem Dade_irr_sub_conjC
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    {G L : Subgroup Gamma} {A : Set Gamma}
    (ddA : DadeHypothesis G L A)
    (chi : IrreducibleCharacter L ℂ)
    (hchi : (chi : ClassFunction L ℂ) ∈
      ClassFunction.supportedOn
        ({1} ∪ {x : L | (x : Gamma) ∈ A})) :
    ∃ psi : IrreducibleCharacter G ℂ,
      Dade ddA
          ((chi : ClassFunction L ℂ) -
            cfConjC (chi : ClassFunction L ℂ)) =
        (psi : ClassFunction G ℂ) -
          cfConjC (psi : ClassFunction G ℂ) := by
  let phi : ClassFunction L ℂ :=
    (chi : ClassFunction L ℂ) -
      cfConjC (chi : ClassFunction L ℂ)
  by_cases hself :
      cfConjC (chi : ClassFunction L ℂ) =
        (chi : ClassFunction L ℂ)
  · refine ⟨IrreducibleCharacter.trivial, ?_⟩
    have htrivial : cfConjC
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) =
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) := by
      ext x
      simp [cfConjC, IrreducibleCharacter.trivial_apply]
    rw [hself, sub_self, map_zero, htrivial, sub_self]
  · let chiConj : IrreducibleCharacter L ℂ :=
      IrreducibleCharacter.mapRingEquiv complexConjugation chi
    have hchiConj :
        cfConjC (chi : ClassFunction L ℂ) =
          (chiConj : ClassFunction L ℂ) := by
      exact cfConjC_irreducible chi
    have hne : chi ≠ chiConj := by
      intro heq
      apply hself
      rw [hchiConj, ← heq]
    let zSource : VirtualCharacter L ℂ :=
      Finsupp.single chi 1 - Finsupp.single chiConj 1
    have hrealizeSource : VirtualCharacter.realize zSource = phi := by
      simp [zSource, phi, hchiConj]
    have hsourceSupport :
        phi ∈ ClassFunction.supportedOn
          {x : L | (x : Gamma) ∈ A} := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hxA
      by_cases hx1 : x = 1
      · subst x
        simp [phi, cfConjC,
          irreducibleCharacter_apply_one_eq_finrank]
      · have hxOutside : x ∉ ({1} ∪ {y : L | (y : Gamma) ∈ A}) := by
          simp [hx1, hxA]
        have hzero := ClassFunction.eq_zero_of_mem_supportedOn
          hchi hxOutside
        simp [phi, hzero]
    have hnormSource : normSq zSource = 2 := by
      simp [zSource, normSq, coeffDot_single_sub_single, hne, hne.symm]
    let zTarget : VirtualCharacter G ℂ :=
      Dade_virtualCharacter ddA zSource
    have hrealizeTarget :
        Dade ddA phi = VirtualCharacter.realize zTarget := by
      rw [← hrealizeSource]
      exact Dade_vchar ddA zSource (by simpa [hrealizeSource] using hsourceSupport)
    have hpairTarget :
        characterPairing (VirtualCharacter.realize zTarget)
            (VirtualCharacter.realize zTarget) = 2 := by
      calc
        characterPairing (VirtualCharacter.realize zTarget)
            (VirtualCharacter.realize zTarget) =
            starCharacterPairing (VirtualCharacter.realize zTarget)
              (VirtualCharacter.realize zTarget) :=
          (starCharacterPairing_realize_eq_characterPairing
            zTarget zTarget).symm
        _ = starCharacterPairing (Dade ddA phi) (Dade ddA phi) := by
          rw [hrealizeTarget]
        _ = starCharacterPairing phi phi :=
          Dade_isometry ddA phi phi hsourceSupport hsourceSupport
        _ = starCharacterPairing (VirtualCharacter.realize zSource)
            (VirtualCharacter.realize zSource) := by
          rw [hrealizeSource]
        _ = characterPairing (VirtualCharacter.realize zSource)
            (VirtualCharacter.realize zSource) :=
          starCharacterPairing_realize_eq_characterPairing zSource zSource
        _ = (normSq zSource : ℂ) := by
          simpa [normSq] using
            VirtualCharacter.characterPairing_realize zSource zSource
        _ = 2 := by rw [hnormSource]; norm_num
    have hnormTarget : normSq zTarget = 2 := by
      apply Int.cast_injective (α := ℂ)
      calc
        (normSq zTarget : ℂ) =
            characterPairing (VirtualCharacter.realize zTarget)
              (VirtualCharacter.realize zTarget) := by
          simpa [normSq] using
            (VirtualCharacter.characterPairing_realize zTarget zTarget).symm
        _ = (2 : ℂ) := hpairTarget
        _ = ((2 : ℤ) : ℂ) := by norm_num
    have htargetOne : VirtualCharacter.realize zTarget 1 = 0 := by
      rw [← hrealizeTarget, Dade1]
    have hcoeffSumTarget : coeffSum zTarget = 0 :=
      coeffSum_eq_zero_of_normSq_eq_two_of_realize_one_eq_zero
        zTarget hnormTarget htargetOne
    obtain ⟨alpha, beta, epsilon, hab, hepsilon, htargetSigned⟩ :=
      VirtualCharacter.realize_eq_signed_irreducible_difference_of_normSq_eq_two
        zTarget hnormTarget hcoeffSumTarget
    have hphiConj : cfConjC phi = -phi := by
      unfold phi
      rw [map_sub, cfConjC_involutive]
      abel
    have htargetAnti :
        cfConjC (VirtualCharacter.realize zTarget) =
          -VirtualCharacter.realize zTarget := by
      calc
        cfConjC (VirtualCharacter.realize zTarget) =
            cfConjC (Dade ddA phi) := by rw [hrealizeTarget]
        _ = Dade ddA (cfConjC phi) :=
          (Dade_aut ddA complexConjugation.toRingHom phi).symm
        _ = Dade ddA (-phi) := by rw [hphiConj]
        _ = -Dade ddA phi := map_neg (Dade ddA) phi
        _ = -VirtualCharacter.realize zTarget := by rw [hrealizeTarget]
    have hbaseAnti :
        cfConjC
            ((alpha : ClassFunction G ℂ) -
              (beta : ClassFunction G ℂ)) =
          -((alpha : ClassFunction G ℂ) -
              (beta : ClassFunction G ℂ)) := by
      apply cancel_cfConjC_sign_anti hepsilon
      rw [← htargetSigned]
      exact htargetAnti
    have halphaConj :
        IrreducibleCharacter.mapRingEquiv complexConjugation alpha = beta :=
      cfConjC_first_eq_second_of_anti alpha beta hab hbaseAnti
    have hswapAnti :
        cfConjC
            ((beta : ClassFunction G ℂ) -
              (alpha : ClassFunction G ℂ)) =
          -((beta : ClassFunction G ℂ) -
              (alpha : ClassFunction G ℂ)) := by
      have hswap :
          (beta : ClassFunction G ℂ) -
              (alpha : ClassFunction G ℂ) =
            -((alpha : ClassFunction G ℂ) -
              (beta : ClassFunction G ℂ)) := by
        abel
      rw [hswap, map_neg, hbaseAnti]
    have hbetaConj :
        IrreducibleCharacter.mapRingEquiv complexConjugation beta = alpha :=
      cfConjC_first_eq_second_of_anti beta alpha hab.symm hswapAnti
    rcases hepsilon with rfl | rfl
    · refine ⟨alpha, ?_⟩
      rw [hrealizeTarget, htargetSigned]
      simp only [Int.cast_one, one_smul, cfConjC_irreducible,
        halphaConj]
    · refine ⟨beta, ?_⟩
      rw [hrealizeTarget, htargetSigned]
      simp only [Int.cast_neg, Int.cast_one,
        cfConjC_irreducible, hbetaConj]
      exact (neg_one_smul ℂ
        ((alpha : ClassFunction G ℂ) -
          (beta : ClassFunction G ℂ))).trans (neg_sub _ _)

end

end Submission.OddOrder.PF
