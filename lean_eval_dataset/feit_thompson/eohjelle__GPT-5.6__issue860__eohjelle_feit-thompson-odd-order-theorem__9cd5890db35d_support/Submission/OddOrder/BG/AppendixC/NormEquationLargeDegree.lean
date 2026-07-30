import Mathlib.LinearAlgebra.Dimension.Free
import Submission.OddOrder.BG.AppendixC.FrobeniusKernelSetup
import Submission.OddOrder.BG.AppendixC.SemidirectNormCounting
import Submission.OddOrder.BG.Section03.FrobeniusPartition
import Submission.OddOrder.MathlibSupport.InternalSemidirectProjection
import Submission.OddOrder.PF.Section01.IrreducibleCharacterTranslationKernel
import Submission.OddOrder.PF.Section01.NormalSubgroupInductionConsequences

/-!
# Appendix C: the source-specific large-degree character calculation

This file supplies the remaining `q > 4` calculation in Bender--Glauberman
Appendix C.  The distinguished element `s` of the Frobenius kernel is the
preimage of `1` under the finite-field coordinate.  Its conjugacy class is
the orbit of the norm-one complement, so the coefficient of the class of
`s^2` in the square of the class of `s` is exactly the cardinality of the
two-norm equation set.

The character calculation then splits the irreducible characters of the
Frobenius group into those trivial on the kernel and those induced from a
nontrivial kernel character.  The former are in bijection with the
irreducible characters of the cyclic complement; every latter character
has degree the complement order.  After this split, column orthogonality
and `classCoefficient_distance_le` give the estimate packaged by
`LargeDegreeCharacterObligation`.

The project-level induced-representation compatibility currently puts the
coefficient field and group in one universe.  Since the coefficient field
here is `ℂ` and the ambient finite group is universe-polymorphic, the one
place where irreducibility of induction is needed is instead proved at the
class-function level: the norm-one formula, character completeness, and
the natural multiplicities in a restricted representation force the
induced class function to equal its nonzero irreducible constituent.
-/

namespace Submission.OddOrder.BG.AppendixC

noncomputable section

open scoped BigOperators Classical IsMulCommutative MonoidAlgebra

open CategoryTheory
open Submission.OddOrder.BG.Section03
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF

universe u v

local instance normEquationLargeDegreeComplexGroupCardInvertible
    {A : Type u} [Group A] [Fintype A] :
    Invertible (Nat.card A : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Universe-polymorphic character preliminaries -/

private theorem irreducibleCharacter_apply_one_eq_finrank
    {A : Type u} {k : Type v} [Group A] [Field k]
    (chi : IrreducibleCharacter A k) :
    chi 1 = (Module.finrank k chi.representation : k) := by
  rw [← chi.representation_character, FDRep.char_one]

private theorem characterPairing_ofRepresentation_eq_finrank_hom
    {A : Type u} {k : Type v} [Group A] [Fintype A]
    [Field k] [CharZero k] (V W : FDRep k A) :
    characterPairing (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) =
      (Module.finrank k (W ⟶ V) : k) := by
  letI : Invertible (Nat.card A : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card A : k) := by
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

private def restrictionMultiplicity
    {A : Type u} {k : Type v} [Group A] [Field k]
    (N : Subgroup A) (chi : IrreducibleCharacter A k)
    (theta : IrreducibleCharacter N k) : ℕ :=
  Module.finrank k
    (theta.representation ⟶
      FDRep.of (chi.representation.ρ.comp N.subtype))

private theorem characterPairing_restrict_eq_restrictionMultiplicity
    {A : Type u} {k : Type v} [Group A] [Fintype A]
    [Field k] [CharZero k]
    (N : Subgroup A) [Fintype N]
    (chi : IrreducibleCharacter A k)
    (theta : IrreducibleCharacter N k) :
    characterPairing
        (ClassFunction.restrict N (chi : ClassFunction A k))
        (theta : ClassFunction N k) =
      (restrictionMultiplicity N chi theta : k) := by
  let R : FDRep k N :=
    FDRep.of (chi.representation.ρ.comp N.subtype)
  have hR : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict N (chi : ClassFunction A k) := by
    calc
      ClassFunction.ofRepresentation R.ρ =
          ClassFunction.restrict N
            (ClassFunction.ofRepresentation chi.representation.ρ) := by
        rfl
      _ = ClassFunction.restrict N (chi : ClassFunction A k) := by
        rw [chi.ofRepresentation_representation]
  rw [← hR, ← theta.ofRepresentation_representation]
  exact characterPairing_ofRepresentation_eq_finrank_hom R
    theta.representation

private theorem exists_irreducible_constituent_restrict
    {A : Type u} {k : Type v} [Group A] [Fintype A]
    [Field k] [IsAlgClosed k] [CharZero k]
    (N : Subgroup A) [Fintype N]
    (chi : IrreducibleCharacter A k) :
    ∃ theta : IrreducibleCharacter N k,
      theta.IsConstituent
        (ClassFunction.restrict N (chi : ClassFunction A k)) := by
  letI : Invertible (Nat.card N : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let f : ClassFunction N k :=
    ClassFunction.restrict N (chi : ClassFunction A k)
  have hfne : f ≠ 0 := by
    intro hf
    have hone := congrArg (fun z : ClassFunction N k ↦ z 1) hf
    change chi 1 = 0 at hone
    rw [irreducibleCharacter_apply_one_eq_finrank] at hone
    letI : CategoryTheory.Simple chi.representation :=
      chi.representation_simple
    letI : Nontrivial chi.representation := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hsub
      apply CategoryTheory.id_nonzero chi.representation
      apply CategoryTheory.ConcreteCategory.hom_ext
      intro x
      exact Subsingleton.elim _ _
    exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') hone
  by_contra hex
  push_neg at hex
  apply hfne
  apply classFunction_eq_zero_of_forall_irreducible_pairing_eq_zero
  intro theta
  rw [characterPairing_comm]
  exact not_ne_iff.mp (hex theta)

private theorem induce_eq_irreducible_of_inertia_le_of_constituent
    {A : Type u} {k : Type v} [Group A] [Fintype A]
    [Field k] [IsAlgClosed k] [CharZero k]
    (N : Subgroup A) [N.Normal] [Fintype N]
    (theta : IrreducibleCharacter N k)
    (hI : ClassFunction.inertia N
      (theta : ClassFunction N k) ≤ N)
    (chi : IrreducibleCharacter A k)
    (hconst : theta.IsConstituent
      (ClassFunction.restrict N (chi : ClassFunction A k))) :
    ClassFunction.induce N (theta : ClassFunction N k) =
      (chi : ClassFunction A k) := by
  classical
  letI : Invertible (Nat.card A : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card N : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let f : ClassFunction A k :=
    ClassFunction.induce N (theta : ClassFunction N k)
  let m : IrreducibleCharacter A k → ℕ :=
    fun psi ↦ restrictionMultiplicity N psi theta
  have hcoeff (psi : IrreducibleCharacter A k) :
      characterPairing (psi : ClassFunction A k) f = (m psi : k) := by
    calc
      characterPairing (psi : ClassFunction A k) f =
          characterPairing f (psi : ClassFunction A k) :=
        characterPairing_comm _ _
      _ = characterPairing (theta : ClassFunction N k)
          (ClassFunction.restrict N (psi : ClassFunction A k)) :=
        ClassFunction.frobeniusReciprocity N _ _
      _ = characterPairing
          (ClassFunction.restrict N (psi : ClassFunction A k))
          (theta : ClassFunction N k) :=
        characterPairing_comm _ _
      _ = (m psi : k) :=
        characterPairing_restrict_eq_restrictionMultiplicity N psi theta
  have hnorm : characterPairing f f = 1 := by
    exact ClassFunction.inertia_Ind_norm_one N theta hI
  have hparseval :
      characterPairing f f =
        ∑ psi : IrreducibleCharacter A k,
          characterPairing (psi : ClassFunction A k) f *
            characterPairing (psi : ClassFunction A k) f := by
    calc
      characterPairing f f =
          characterPairing
            (irreducibleCharacterExpansion f) f := by
        rw [irreducibleCharacterExpansion_eq]
      _ = ∑ psi : IrreducibleCharacter A k,
          characterPairing (psi : ClassFunction A k) f *
            characterPairing (psi : ClassFunction A k) f := by
        change characterPairingRight f
            (irreducibleCharacterExpansion f) = _
        rw [irreducibleCharacterExpansion, map_sum]
        apply Finset.sum_congr rfl
        intro psi _
        rw [map_smul]
        rfl
  have hsumCast :
      ((∑ psi : IrreducibleCharacter A k,
          m psi * m psi : ℕ) : k) = 1 := by
    rw [← hnorm, hparseval]
    simp_rw [hcoeff]
    simp only [Nat.cast_sum, Nat.cast_mul]
  have hsumNat :
      (∑ psi : IrreducibleCharacter A k, m psi * m psi) = 1 :=
    Nat.cast_injective (by simpa only [Nat.cast_one] using hsumCast)
  have hmchi_ne : m chi ≠ 0 := by
    intro hm
    apply hconst
    rw [characterPairing_restrict_eq_restrictionMultiplicity N chi theta]
    change (m chi : k) = 0
    rw [hm, Nat.cast_zero]
  have hmchi_pos : 0 < m chi := Nat.pos_of_ne_zero hmchi_ne
  have hmchi_sq_le : m chi * m chi ≤ 1 := by
    rw [← hsumNat]
    exact Finset.single_le_sum
      (fun psi _ ↦ Nat.zero_le (m psi * m psi))
      (Finset.mem_univ chi)
  have hmchi_le : m chi ≤ 1 := by
    by_contra hle
    have htwo : 2 ≤ m chi := by omega
    nlinarith
  have hmchi : m chi = 1 := by omega
  have hsumErase :
      ∑ psi ∈ (Finset.univ : Finset (IrreducibleCharacter A k)).erase chi,
          m psi * m psi = 0 := by
    have hsplit := Finset.sum_erase_add
      (s := (Finset.univ : Finset (IrreducibleCharacter A k)))
      (f := fun psi ↦ m psi * m psi) (Finset.mem_univ chi)
    rw [hsumNat, hmchi] at hsplit
    omega
  have hmzero {psi : IrreducibleCharacter A k} (hne : psi ≠ chi) :
      m psi = 0 := by
    have hmem : psi ∈
        (Finset.univ : Finset (IrreducibleCharacter A k)).erase chi :=
      Finset.mem_erase.mpr ⟨hne, Finset.mem_univ psi⟩
    have hle : m psi * m psi ≤ 0 := by
      rw [← hsumErase]
      exact Finset.single_le_sum
        (fun z _ ↦ Nat.zero_le (m z * m z)) hmem
    have hsquare : m psi * m psi = 0 := Nat.eq_zero_of_le_zero hle
    rcases Nat.mul_eq_zero.mp hsquare with h | h
    · exact h
    · exact h
  calc
    f = irreducibleCharacterExpansion f :=
      (irreducibleCharacterExpansion_eq f).symm
    _ = ∑ psi : IrreducibleCharacter A k,
        (m psi : k) • (psi : ClassFunction A k) := by
      rw [irreducibleCharacterExpansion]
      apply Finset.sum_congr rfl
      intro psi _
      rw [hcoeff]
    _ = (chi : ClassFunction A k) := by
      rw [Finset.sum_eq_single chi]
      · rw [hmchi, Nat.cast_one, one_smul]
      · intro psi _ hne
        rw [hmzero hne, Nat.cast_zero, zero_smul]
      · simp

private theorem irreducibleCharacter_finrank_eq_one_of_isMulCommutative
    {A : Type u} {k : Type v} [Group A] [IsMulCommutative A]
    [Field k] [IsAlgClosed k]
    (chi : IrreducibleCharacter A k) :
    Module.finrank k chi.representation = 1 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
    chi.representation.ρ

private theorem representation_eq_of_character_eq_of_finrank_one
    {A : Type u} {k : Type v} [Group A] [Field k]
    {V : Type v} [AddCommGroup V] [Module k V]
    [FiniteDimensional k V]
    (rho : Representation k A V) (hdim : Module.finrank k V = 1)
    {a b : A} (hchar : rho.character a = rho.character b) :
    rho a = rho b := by
  obtain ⟨ca, hca, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (rho a)
  obtain ⟨cb, hcb, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (rho b)
  have hscalar : ca = cb := by
    change LinearMap.trace k V (rho a) =
      LinearMap.trace k V (rho b) at hchar
    rw [hca, hcb, map_smul, map_smul, LinearMap.trace_id, hdim] at hchar
    simpa using hchar
  rw [hca, hcb, hscalar]

private theorem translationKernel_irreducibleCharacter'
    {A : Type u} {k : Type v} [Group A]
    [Field k] [IsAlgClosed k]
    (chi : IrreducibleCharacter A k) :
    ClassFunction.translationKernel (chi : ClassFunction A k) =
      chi.representation.ρ.ker := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker]
    let rho : Representation k A chi.representation :=
      chi.representation.ρ
    letI : CategoryTheory.Simple chi.representation :=
      chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      representation_isIrreducible_of_simple_fdRep chi.representation
    have htraceGroup (g : A) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho g) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← rho.map_mul]
      change rho.character (a * g) - rho.character g = 0
      dsimp only [rho]
      change chi.representation.character (a * g) -
        chi.representation.character g = 0
      rw [chi.representation_character, chi.representation_character]
      exact sub_eq_zero.mpr (ha g)
    have htraceAlgebra (z : k[A]) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho.asAlgebraHom z) = 0 := by
      induction z using MonoidAlgebra.induction_on with
      | hM g =>
          simpa only [Representation.asAlgebraHom_of] using htraceGroup g
      | hadd x y hx hy =>
          simp only [map_add, mul_add, hx, hy, add_zero]
      | hsmul c x hx =>
          simp only [map_smul, mul_smul_comm, hx, smul_zero]
    have htraceEnd (X : Module.End k chi.representation) :
        LinearMap.trace k chi.representation ((rho a - 1) * X) = 0 := by
      obtain ⟨z, rfl⟩ :=
        Representation.IsIrreducible.asAlgebraHom_surjective rho X
      exact htraceAlgebra z
    have hzero : rho a - 1 = 0 := by
      let b := Module.finBasis k chi.representation
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_zero]
      apply (Matrix.ext_iff_trace_mul_right).2
      intro X
      have hX := htraceEnd ((LinearMap.toMatrixAlgEquiv b).symm X)
      rw [LinearMap.trace_eq_matrix_trace k b] at hX
      change
        ((LinearMap.toMatrixAlgEquiv b)
            ((rho a - 1) * (LinearMap.toMatrixAlgEquiv b).symm X)).trace = 0
        at hX
      simpa only [map_mul, AlgEquiv.apply_symm_apply, Matrix.zero_mul,
        Matrix.trace_zero] using hX
    exact sub_eq_zero.mp hzero
  · intro a ha g
    rw [← chi.representation_character,
      ← chi.representation_character]
    change LinearMap.trace k chi.representation
        (chi.representation.ρ (a * g)) =
      LinearMap.trace k chi.representation (chi.representation.ρ g)
    rw [chi.representation.ρ.map_mul, MonoidHom.mem_ker.mp ha, one_mul]

private noncomputable def classFunctionLinearEquivFunOfIsMulCommutative
    {A : Type u} {k : Type v} [Group A] [IsMulCommutative A]
    [Field k] :
    ClassFunction A k ≃ₗ[k] (A → k) where
  toFun f := f
  invFun f :=
    ⟨f, by
      intro x g
      congr 1
      rw [mul_comm x g, mul_assoc, mul_inv_cancel, mul_one]⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

private theorem irreducibleCharacter_card_eq_natCard_of_isCyclic
    {C : Type u} {k : Type v} [Group C] [Fintype C] [IsCyclic C]
    [Field k] [IsAlgClosed k] [CharZero k]
    [Invertible (Nat.card C : k)] :
    Fintype.card (IrreducibleCharacter C k) = Nat.card C := by
  let basis : Module.Basis (IrreducibleCharacter C k) k
      (ClassFunction C k) :=
    Module.Basis.mk IrreducibleCharacter.linearIndependent (by
      rw [irreducibleCharacter_span_eq_top])
  calc
    Fintype.card (IrreducibleCharacter C k) =
        Module.finrank k (ClassFunction C k) :=
      (Module.finrank_eq_card_basis basis).symm
    _ = Module.finrank k (C → k) :=
      classFunctionLinearEquivFunOfIsMulCommutative.finrank_eq
    _ = Fintype.card C :=
      Module.finrank_fintype_fun_eq_card k
    _ = Nat.card C := Fintype.card_eq_nat_card

/-! ## Characters of an internal Frobenius semidirect product -/

private theorem representation_irreducible_comp_surjective
    {A B : Type u} {k : Type v} [Group A] [Group B] [Field k]
    {V : Type v} [AddCommGroup V] [Module k V]
    (rho : Representation k B V) [Representation.IsIrreducible rho]
    (f : A →* B) (hf : Function.Surjective f) :
    Representation.IsIrreducible (rho.comp f) := by
  let tau : Representation k A V := rho.comp f
  have hbot_ne_top : (⊥ : Subrepresentation tau) ≠ ⊤ := by
    intro h
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation rho)
    apply SetLike.ext
    intro v
    have hv := congrArg (fun U : Subrepresentation tau ↦ v ∈ U) h
    change (v ∈ (⊥ : Submodule k V)) =
      (v ∈ (⊤ : Submodule k V)) at hv
    exact iff_of_eq hv
  letI : Nontrivial (Subrepresentation tau) :=
    ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  let U' : Subrepresentation rho :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule b v hv := by
        obtain ⟨a, rfl⟩ := hf b
        exact U.apply_mem_toSubmodule a hv }
  have hU' : U' ≠ ⊥ := by
    intro hbot
    apply hU
    apply SetLike.ext
    intro v
    have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) hbot
    change (v ∈ U.toSubmodule) =
      (v ∈ (⊥ : Submodule k V)) at hv
    exact iff_of_eq hv
  have htop : U' = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'
  apply SetLike.ext
  intro v
  have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) htop
  change (v ∈ U.toSubmodule) =
    (v ∈ (⊤ : Submodule k V)) at hv
  exact iff_of_eq hv

private theorem complement_restriction_isIrreducible
    {A : Type u} {k : Type v} [Group A] [Field k]
    {K R : Subgroup A} [K.Normal]
    (hsemi : K.IsComplement' R)
    (chi : IrreducibleCharacter A k)
    (hker : K ≤ chi.representation.ρ.ker) :
    Representation.IsIrreducible
      (chi.representation.ρ.comp R.subtype) := by
  let rho := chi.representation.ρ
  let tau : Representation k R chi.representation :=
    rho.comp R.subtype
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  let liftSub (W : Subrepresentation tau) : Subrepresentation rho :=
    { toSubmodule := W.toSubmodule
      apply_mem_toSubmodule := by
        intro a v hv
        obtain ⟨⟨x, r⟩, hxr⟩ := hsemi.2 a
        have hx : rho (x : A) = 1 :=
          MonoidHom.mem_ker.mp (hker x.property)
        rw [← hxr, map_mul, hx, one_mul]
        exact W.apply_mem_toSubmodule r hv }
  change Representation.IsIrreducible tau
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, fun hEq ↦ ?_⟩
    have hEq' := congrArg Subrepresentation.toSubmodule hEq
    apply (show (⊥ : Subrepresentation rho) ≠ ⊤ from bot_ne_top)
    apply Subrepresentation.toSubmodule_injective
    exact hEq'
  · intro W
    rcases eq_bot_or_eq_top (liftSub W) with hW | hW
    · left
      have hW' := congrArg Subrepresentation.toSubmodule hW
      change W.toSubmodule =
        (⊥ : Submodule k chi.representation) at hW'
      exact Subrepresentation.toSubmodule_injective hW'
    · right
      have hW' := congrArg Subrepresentation.toSubmodule hW
      change W.toSubmodule =
        (⊤ : Submodule k chi.representation) at hW'
      exact Subrepresentation.toSubmodule_injective hW'

private def KernelTrivialCharacter
    {A : Type u} [Group A] (K : Subgroup A) (k : Type v)
    [Field k] :=
  {chi : IrreducibleCharacter A k //
    K ≤ chi.representation.ρ.ker}

private noncomputable def restrictKernelTrivialCharacter
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    [IsAlgClosed k] [CharZero k]
    {K R : Subgroup A} [K.Normal]
    (hsemi : K.IsComplement' R)
    (chi : KernelTrivialCharacter K k) :
    IrreducibleCharacter R k := by
  let tau : Representation k R chi.1.representation :=
    chi.1.representation.ρ.comp R.subtype
  letI : Representation.IsIrreducible tau :=
    complement_restriction_isIrreducible hsemi chi.1 chi.2
  let V : FDRep k R := FDRep.of tau
  letI : CategoryTheory.Simple V :=
    simple_fdRep_of_isIrreducible tau
  exact IrreducibleCharacter.ofFDRep V

@[simp]
private theorem restrictKernelTrivialCharacter_apply
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    [IsAlgClosed k] [CharZero k]
    {K R : Subgroup A} [K.Normal]
    (hsemi : K.IsComplement' R)
    (chi : KernelTrivialCharacter K k) (r : R) :
    restrictKernelTrivialCharacter hsemi chi r = chi.1 (r : A) := by
  simp only [restrictKernelTrivialCharacter,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.1.representation.character (r : A) = chi.1 (r : A)
  exact chi.1.representation_character _

private noncomputable def inflateComplementCharacter
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    [IsAlgClosed k] [CharZero k]
    {K R : Subgroup A} [K.Normal]
    (hsemi : K.IsComplement' R)
    (xi : IrreducibleCharacter R k) :
    IrreducibleCharacter A k := by
  let proj : A →* R := hsemi.rightProjection
  let tau : Representation k A xi.representation :=
    xi.representation.ρ.comp proj
  letI : CategoryTheory.Simple xi.representation :=
    xi.representation_simple
  letI : Representation.IsIrreducible xi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep xi.representation
  have hsurj : Function.Surjective proj := fun r ↦
    ⟨(r : A), hsemi.rightProjection_apply_right r⟩
  letI : Representation.IsIrreducible tau :=
    representation_irreducible_comp_surjective
      xi.representation.ρ proj hsurj
  let V : FDRep k A := FDRep.of tau
  letI : CategoryTheory.Simple V :=
    simple_fdRep_of_isIrreducible tau
  exact IrreducibleCharacter.ofFDRep V

@[simp]
private theorem inflateComplementCharacter_apply
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    [IsAlgClosed k] [CharZero k]
    {K R : Subgroup A} [K.Normal]
    (hsemi : K.IsComplement' R)
    (xi : IrreducibleCharacter R k) (a : A) :
    inflateComplementCharacter hsemi xi a =
      xi (hsemi.rightProjection a) := by
  simp only [inflateComplementCharacter,
    IrreducibleCharacter.ofFDRep_apply]
  change xi.representation.character (hsemi.rightProjection a) =
    xi (hsemi.rightProjection a)
  exact xi.representation_character _

private theorem inflateComplementCharacter_kernel
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    [IsAlgClosed k] [CharZero k]
    {K R : Subgroup A} [K.Normal]
    (hsemi : K.IsComplement' R)
    (xi : IrreducibleCharacter R k) :
    K ≤ (inflateComplementCharacter hsemi xi).representation.ρ.ker := by
  rw [← translationKernel_irreducibleCharacter']
  intro a ha
  intro g
  rw [inflateComplementCharacter_apply,
    inflateComplementCharacter_apply, map_mul,
    hsemi.rightProjection_apply_left ⟨a, ha⟩, one_mul]

private noncomputable def kernelTrivialCharacterEquiv
    {A : Type u} {k : Type v} [Group A] [Fintype A] [Field k]
    [IsAlgClosed k] [CharZero k]
    {K R : Subgroup A} [K.Normal]
    (hsemi : K.IsComplement' R) :
    KernelTrivialCharacter K k ≃ IrreducibleCharacter R k where
  toFun := restrictKernelTrivialCharacter hsemi
  invFun xi :=
    ⟨inflateComplementCharacter hsemi xi,
      inflateComplementCharacter_kernel hsemi xi⟩
  left_inv chi0 := by
    rcases chi0 with ⟨chi, hchi⟩
    apply Subtype.ext
    apply IrreducibleCharacter.ext
    intro a
    rw [inflateComplementCharacter_apply,
      restrictKernelTrivialCharacter_apply]
    obtain ⟨⟨x, r⟩, hxr⟩ := hsemi.2 a
    subst a
    have hx : chi.representation.ρ (x : A) = 1 :=
      MonoidHom.mem_ker.mp (hchi x.property)
    rw [hsemi.rightProjection_apply_mul,
      ← chi.representation_character,
      ← chi.representation_character]
    change LinearMap.trace k chi.representation
      (chi.representation.ρ (r : A)) =
        LinearMap.trace k chi.representation
          (chi.representation.ρ ((x : A) * (r : A)))
    rw [map_mul, hx, one_mul]
  right_inv xi := by
    apply IrreducibleCharacter.ext
    intro r
    rw [restrictKernelTrivialCharacter_apply,
      inflateComplementCharacter_apply,
      hsemi.rightProjection_apply_right]

private theorem kernelTrivialCharacter_card_eq_complement
    {A : Type u} {k : Type v} [Group A] [Fintype A]
    [Field k] [IsAlgClosed k] [CharZero k]
    [Invertible (Nat.card A : k)]
    {K R : Subgroup A} [K.Normal] [IsCyclic R]
    [Fintype (KernelTrivialCharacter K k)]
    (hsemi : K.IsComplement' R) :
    Fintype.card (KernelTrivialCharacter K k) = Nat.card R := by
  letI : Invertible (Nat.card R : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  calc
    Fintype.card (KernelTrivialCharacter K k) =
        Fintype.card (IrreducibleCharacter R k) :=
      Fintype.card_congr (kernelTrivialCharacterEquiv hsemi)
    _ = Nat.card R := irreducibleCharacter_card_eq_natCard_of_isCyclic

private theorem kernelTrivialCharacter_finrank_eq_one
    {A : Type u} {k : Type v} [Group A] [Field k]
    [IsAlgClosed k] [CharZero k]
    {K R : Subgroup A} [K.Normal] [IsCyclic R]
    (hsemi : K.IsComplement' R)
    (chi : KernelTrivialCharacter K k) :
    Module.finrank k chi.1.representation = 1 := by
  let tau : Representation k R chi.1.representation :=
    chi.1.representation.ρ.comp R.subtype
  letI : Representation.IsIrreducible tau :=
    complement_restriction_isIrreducible hsemi chi.1 chi.2
  exact Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative tau

private theorem kernelTrivialCharacter_apply_kernel
    {A : Type u} {k : Type v} [Group A] [Field k]
    [IsAlgClosed k] [CharZero k]
    {K R : Subgroup A} [K.Normal] [IsCyclic R]
    (hsemi : K.IsComplement' R)
    (chi : KernelTrivialCharacter K k) (x : K) :
    chi.1 (x : A) = 1 := by
  rw [← chi.1.representation_character]
  change LinearMap.trace k chi.1.representation
    (chi.1.representation.ρ (x : A)) = 1
  rw [MonoidHom.mem_ker.mp (chi.2 x.property),
    LinearMap.trace_one, kernelTrivialCharacter_finrank_eq_one hsemi chi]
  simp

private theorem kernel_le_of_constituent_restrict_kernel
    {A : Type u} {k : Type v} [Group A] [Fintype A]
    [Field k] [IsAlgClosed k] [CharZero k]
    (N : Subgroup A) [N.Normal] [Fintype N]
    (chi : IrreducibleCharacter A k)
    (theta : IrreducibleCharacter N k)
    (hconst : theta.IsConstituent
      (ClassFunction.restrict N (chi : ClassFunction A k)))
    (htheta : (⊤ : Subgroup N) ≤ theta.representation.ρ.ker) :
    N ≤ chi.representation.ρ.ker := by
  let R : FDRep k N :=
    FDRep.of (chi.representation.ρ.comp N.subtype)
  have hRchar : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict N (chi : ClassFunction A k) := by
    calc
      ClassFunction.ofRepresentation R.ρ =
          ClassFunction.restrict N
            (ClassFunction.ofRepresentation chi.representation.ρ) := by
        rfl
      _ = ClassFunction.restrict N (chi : ClassFunction A k) := by
        rw [chi.ofRepresentation_representation]
  have hpair : characterPairing (ClassFunction.ofRepresentation R.ρ)
      (theta : ClassFunction N k) ≠ 0 := by
    rwa [hRchar]
  have hfin : Module.finrank k (theta.representation ⟶ R) ≠ 0 := by
    intro hzero
    apply hpair
    calc
      characterPairing (ClassFunction.ofRepresentation R.ρ)
          (theta : ClassFunction N k) =
          characterPairing (ClassFunction.ofRepresentation R.ρ)
            (ClassFunction.ofRepresentation theta.representation.ρ) := by
        rw [theta.ofRepresentation_representation]
      _ = (Module.finrank k (theta.representation ⟶ R) : k) :=
        characterPairing_ofRepresentation_eq_finrank_hom R
          theta.representation
      _ = 0 := by rw [hzero, Nat.cast_zero]
  obtain ⟨f, hf⟩ :=
    Module.finrank_pos_iff_exists_ne_zero.mp (Nat.pos_of_ne_zero hfin)
  letI : CategoryTheory.Simple theta.representation :=
    theta.representation_simple
  letI : Mono f := CategoryTheory.mono_of_nonzero_from_simple hf
  let fR := (forget₂ (FDRep k N) (Rep k N)).map f
  have hfinj : Function.Injective fR.hom :=
    (Rep.mono_iff_injective fR).mp inferInstance
  let fLinear : theta.representation →ₗ[k] chi.representation :=
    f.hom.hom.hom
  have hfinjLinear : Function.Injective fLinear := by
    exact hfinj
  letI : Nontrivial theta.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero theta.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  obtain ⟨v, hv⟩ := exists_ne (0 : theta.representation)
  let w : chi.representation := fLinear v
  have hw : w ≠ 0 := by
    intro hw0
    exact hv ((fLinear.map_eq_zero_iff hfinjLinear).mp hw0)
  let rho := chi.representation.ρ
  let tau : Representation k N chi.representation := rho.comp N.subtype
  have hwfix : w ∈ tau.invariants := by
    rw [Representation.mem_invariants]
    intro n
    have hinter := _root_.Representation.IntertwiningMap.isIntertwining
      (ρ := ((forget₂ (FDRep k N) (Rep k N)).obj
        theta.representation).ρ)
      (σ := ((forget₂ (FDRep k N) (Rep k N)).obj R).ρ)
      (f := fR.hom) n v
    change fLinear (theta.representation.ρ n v) =
      rho (n : A) (fLinear v) at hinter
    rw [MonoidHom.mem_ker.mp (htheta (Subgroup.mem_top n))] at hinter
    change rho (n : A) (fLinear v) = fLinear v
    calc
      rho (n : A) (fLinear v) =
          fLinear ((1 : Module.End k theta.representation) v) := hinter.symm
      _ = fLinear v := by rfl
  let fixed : Subrepresentation rho :=
    { toSubmodule := tau.invariants
      apply_mem_toSubmodule := by
        intro a z hz
        rw [Representation.mem_invariants] at hz ⊢
        intro n
        let n' : N :=
          ⟨a⁻¹ * (n : A) * a,
            by
              simpa using (inferInstance : N.Normal).conj_mem
                (n : A) n.property a⁻¹⟩
        calc
          rho (n : A) (rho a z) =
              (rho (n : A) * rho a) z := rfl
          _ = rho ((n : A) * a) z := by rw [map_mul]
          _ = rho (a * (n' : A)) z := by
            congr 2
            dsimp only [n']
            group
          _ = (rho a * rho (n' : A)) z := by rw [map_mul]
          _ = rho a (rho (n' : A) z) := rfl
          _ = rho a z := by
            have hz' : rho (n' : A) z = z := hz n'
            rw [hz'] }
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  have hfixed_ne : fixed ≠ ⊥ := by
    intro hbot
    have hwbot : w ∈ (⊥ : Submodule k chi.representation) := by
      have : w ∈ fixed := hwfix
      rw [hbot] at this
      exact this
    exact hw ((Submodule.mem_bot k).mp hwbot)
  have hfixed : fixed = ⊤ :=
    (eq_bot_or_eq_top fixed).resolve_left hfixed_ne
  intro n hn
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro z
  have hz : z ∈ fixed := by rw [hfixed]; trivial
  exact hz ⟨n, hn⟩

private theorem inertia_le_kernel_of_nontrivial_character
    {A : Type u} [Group A] [Finite A]
    {K R : Subgroup A} [K.Normal] [IsMulCommutative K]
    (h : IsFrobeniusDecomposition K R)
    (theta : IrreducibleCharacter K ℂ)
    (hnontrivial : ¬ (⊤ : Subgroup K) ≤ theta.representation.ρ.ker) :
    ClassFunction.inertia K (theta : ClassFunction K ℂ) ≤ K := by
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype R := Fintype.ofFinite R
  letI := h.conjugationAction
  intro a ha
  obtain ⟨⟨x, r⟩, hxr⟩ := h.isComplement.2 a
  have hxI : (x : A) ∈
      ClassFunction.inertia K (theta : ClassFunction K ℂ) :=
    ClassFunction.le_inertia K _ x.property
  have hrI : (r : A) ∈
      ClassFunction.inertia K (theta : ClassFunction K ℂ) := by
    have hprod :=
      (ClassFunction.inertia K (theta : ClassFunction K ℂ)).mul_mem
        ((ClassFunction.inertia K
          (theta : ClassFunction K ℂ)).inv_mem hxI) ha
    simpa [← hxr] using hprod
  by_cases hr : r = 1
  · rw [← hxr, hr]
    simpa using x.property
  · exfalso
    apply hnontrivial
    intro y _hy
    rw [MonoidHom.mem_ker]
    obtain ⟨z, hz⟩ := h.kernelCommutatorMap_surjective r hr y
    have hrInv : ((r : A)⁻¹) ∈
        ClassFunction.inertia K (theta : ClassFunction K ℂ) :=
      (ClassFunction.inertia K
        (theta : ClassFunction K ℂ)).inv_mem hrI
    have hinv :=
      (ClassFunction.mem_inertia_iff K
        (theta : ClassFunction K ℂ) ((r : A)⁻¹)).mp hrInv
    have hvalue := congrArg (fun f : ClassFunction K ℂ ↦ f z) hinv
    rw [ClassFunction.normalConjugate_apply] at hvalue
    have harg : (MulAut.conjNormal ((r : A)⁻¹)).symm z = r • z := by
      apply Subtype.ext
      rw [MulAut.conjNormal_symm_apply, h.coe_smul]
      simp
    rw [harg] at hvalue
    have hdim : Module.finrank ℂ theta.representation = 1 :=
      irreducibleCharacter_finrank_eq_one_of_isMulCommutative theta
    have hrho : theta.representation.ρ (r • z) =
        theta.representation.ρ z := by
      apply representation_eq_of_character_eq_of_finrank_one
        theta.representation.ρ hdim
      change theta.representation.character (r • z) =
        theta.representation.character z
      simpa only [theta.representation_character] using hvalue
    rw [MonoidHom.commutatorMap_apply] at hz
    rw [← hz]
    calc
      theta.representation.ρ (z / r • z) =
          theta.representation.ρ z *
            theta.representation.ρ ((r • z)⁻¹) := by
        rw [div_eq_mul_inv, map_mul]
      _ = theta.representation.ρ (r • z) *
            theta.representation.ρ ((r • z)⁻¹) := by
        rw [hrho]
      _ = theta.representation.ρ ((r • z) * (r • z)⁻¹) := by
        rw [map_mul]
      _ = 1 := by simp

private theorem nonlinearCharacter_finrank_eq_complement_card
    {A : Type u} [Group A] [Finite A]
    {K R : Subgroup A} [IsMulCommutative K]
    (h : IsFrobeniusDecomposition K R)
    (chi : IrreducibleCharacter A ℂ)
    (hnontrivial : ¬ K ≤ chi.representation.ρ.ker) :
    Module.finrank ℂ chi.representation = Nat.card R := by
  letI : Fintype A := Fintype.ofFinite A
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype R := Fintype.ofFinite R
  letI : K.Normal := h.kernel_normal
  obtain ⟨theta, htheta⟩ :=
    exists_irreducible_constituent_restrict K chi
  have hthetaNontrivial :
      ¬ (⊤ : Subgroup K) ≤ theta.representation.ρ.ker := by
    intro hker
    exact hnontrivial
      (kernel_le_of_constituent_restrict_kernel K chi theta htheta hker)
  have hI : ClassFunction.inertia K
      (theta : ClassFunction K ℂ) ≤ K :=
    inertia_le_kernel_of_nontrivial_character h theta hthetaNontrivial
  have hind : ClassFunction.induce K (theta : ClassFunction K ℂ) =
      (chi : ClassFunction A ℂ) :=
    induce_eq_irreducible_of_inertia_le_of_constituent
      K theta hI chi htheta
  have hone := congrArg (fun f : ClassFunction A ℂ ↦ f 1) hind
  rw [ClassFunction.induce_one,
    irreducibleCharacter_apply_one_eq_finrank,
    irreducibleCharacter_apply_one_eq_finrank] at hone
  have hthetaOne : Module.finrank ℂ theta.representation = 1 :=
    irreducibleCharacter_finrank_eq_one_of_isMulCommutative theta
  rw [hthetaOne, Nat.cast_one, mul_one] at hone
  have hindex : K.index = Nat.card R :=
    h.isComplement.symm.index_eq_card
  rw [hindex] at hone
  exact Nat.cast_injective hone.symm

/-! ## Conjugacy classes in the Frobenius kernel -/

private theorem conjugacyClassCard_eq_complement_card
    {A : Type u} [Group A] [Fintype A]
    {K R : Subgroup A} [IsMulCommutative K]
    (h : IsFrobeniusDecomposition K R)
    (x : K) (hx : x ≠ 1) :
    conjugacyClassCard (x : A) = Nat.card R := by
  letI : Fintype K := Fintype.ofFinite K
  letI : Fintype R := Fintype.ofFinite R
  let orbit : R → A := fun r ↦ (r : A)⁻¹ * (x : A) * (r : A)
  have horbitConj (r : R) : IsConj (orbit r) (x : A) := by
    rw [isConj_iff]
    refine ⟨(r : A), ?_⟩
    dsimp only [orbit]
    group
  have horbitInj : Function.Injective orbit := by
    intro r t hrt
    let a : R := r * t⁻¹
    have hcomm : (x : A) * (a : A) = (a : A) * (x : A) := by
      dsimp only [orbit] at hrt
      dsimp only [a]
      calc
        (x : A) * ((r : A) * (t : A)⁻¹) =
            (r : A) * ((r : A)⁻¹ * (x : A) * (r : A)) *
              (t : A)⁻¹ := by group
        _ = (r : A) * ((t : A)⁻¹ * (x : A) * (t : A)) *
              (t : A)⁻¹ := by rw [hrt]
        _ = ((r : A) * (t : A)⁻¹) * (x : A) := by group
    have hfix : (a : A) * (x : A) * (a : A)⁻¹ = (x : A) := by
      calc
        (a : A) * (x : A) * (a : A)⁻¹ =
            (x : A) * (a : A) * (a : A)⁻¹ := by rw [← hcomm]
        _ = (x : A) := by simp
    have ha : a = 1 := by
      by_contra ha
      exact hx (h.fixedPointFree a ha x hfix)
    apply Subtype.ext
    have haA := congrArg (fun z : R ↦ (z : A)) ha
    dsimp only [a] at haA
    exact mul_inv_eq_one.mp haA
  have horbitSurj : Function.Surjective
      (fun r : R ↦ (⟨orbit r, horbitConj r⟩ :
        {y : A // IsConj y (x : A)})) := by
    rintro ⟨y, hy⟩
    obtain ⟨a, ha⟩ := isConj_iff.mp hy
    obtain ⟨⟨z, r⟩, hzr⟩ := h.isComplement.2 a
    have hzcomm : (z : A)⁻¹ * (x : A) * (z : A) = (x : A) := by
      have hzx : (z : A) * (x : A) = (x : A) * (z : A) :=
        congrArg Subtype.val (mul_comm z x)
      calc
        (z : A)⁻¹ * (x : A) * (z : A) =
            (z : A)⁻¹ * ((x : A) * (z : A)) := by rw [mul_assoc]
        _ = (z : A)⁻¹ * ((z : A) * (x : A)) := by rw [hzx]
        _ = (x : A) := by simp
    refine ⟨r, ?_⟩
    apply Subtype.ext
    change orbit r = y
    have hyform : y = a⁻¹ * (x : A) * a := by
      calc
        y = a⁻¹ * (a * y * a⁻¹) * a := by group
        _ = a⁻¹ * (x : A) * a := by rw [ha]
    rw [hyform, ← hzr]
    change (r : A)⁻¹ * (x : A) * (r : A) =
      ((z : A) * (r : A))⁻¹ * (x : A) * ((z : A) * (r : A))
    calc
      (r : A)⁻¹ * (x : A) * (r : A) =
          (r : A)⁻¹ * ((z : A)⁻¹ * (x : A) * (z : A)) *
            (r : A) := by rw [hzcomm]
      _ = ((z : A) * (r : A))⁻¹ * (x : A) *
          ((z : A) * (r : A)) := by group
  let e : R ≃ {y : A // IsConj y (x : A)} :=
    Equiv.ofBijective
      (fun r : R ↦ (⟨orbit r, horbitConj r⟩ :
        {y : A // IsConj y (x : A)}))
      ⟨fun r t hrt ↦ horbitInj (congrArg Subtype.val hrt), horbitSurj⟩
  change (Finset.univ.filter (fun y : A ↦ IsConj y (x : A))).card =
    Nat.card R
  rw [← Fintype.card_subtype]
  simpa only [Fintype.card_eq_nat_card] using Fintype.card_congr e.symm

/-! ## The norm equation as a class-product coefficient -/

/-- A class-product coefficient counts the corresponding ordered-pair set.

Keeping this finite counting argument separate from the source-specific
norm-equation bijection also keeps its elaboration independent of the much
larger semidirect-product calculation below. -/
private theorem classProductCoefficient_eq_solutionSet_ncard
    {H : Type u} [Group H] [Fintype H] (a b c : H) :
    classProductCoefficient a b c =
      ({xy : H × H |
        IsConj xy.1 a ∧ IsConj xy.2 b ∧ xy.1 * xy.2 = c} :
        Set (H × H)).ncard := by
  classical
  let pred : H × H → Prop := fun xy ↦
    IsConj xy.1 a ∧ IsConj xy.2 b ∧ xy.1 * xy.2 = c
  let f : H × H → ℕ := fun xy ↦ if pred xy then 1 else 0
  have hcoefficient : classProductCoefficient a b c =
      ∑ x : H, ∑ y : H, f (x, y) := by
    rw [classProductCoefficient]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hp : IsConj x a ∧ IsConj y b ∧ x * y = c
    · simp only [f, pred, hp, if_true]
    · simp only [f, pred, hp, if_false]
  have hsumFilter :
      (∑ xy : H × H, f xy) =
        ((Finset.univ : Finset (H × H)).filter pred).card := by
    rw [Finset.card_filter]
  calc
    classProductCoefficient a b c =
        ∑ x : H, ∑ y : H, f (x, y) := hcoefficient
    _ = ∑ xy : H × H, f xy := (Fintype.sum_prod_type f).symm
    _ = ((Finset.univ : Finset (H × H)).filter pred).card := hsumFilter
    _ = Fintype.card {xy : H × H // pred xy} :=
      (Fintype.card_subtype pred).symm
    _ = Nat.card {xy : H × H // pred xy} :=
      Fintype.card_eq_nat_card
    _ = ({xy : H × H | pred xy} : Set (H × H)).ncard := by
      rfl
    _ = ({xy : H × H |
        IsConj xy.1 a ∧ IsConj xy.2 b ∧ xy.1 * xy.2 = c} :
          Set (H × H)).ncard := by rfl

private theorem normEquationSet_ncard_eq_classProductCoefficient
    {G : Type u} [Group G] [Fintype G]
    {p q : ℕ} [Fact p.Prime]
    {H P P0 U : Subgroup G}
    (hfield : FiniteFieldImage P P0 U)
    [Algebra (ZMod p) hfield.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardP : Nat.card P = p ^ q)
    (hcardU : Nat.card U = nU p q) :
    (normEquationSet (ZMod p) hfield.F).ncard =
      classProductCoefficient
        (⟨(hfield.onePreimage : G),
          hPH hfield.onePreimage.property⟩ : H)
        (⟨(hfield.onePreimage : G),
          hPH hfield.onePreimage.property⟩ : H)
        ((⟨(hfield.onePreimage : G),
          hPH hfield.onePreimage.property⟩ : H) ^ 2) := by
  classical
  let s : P := hfield.onePreimage
  let sH : H := ⟨(s : G), hPH s.property⟩
  let orbitP (u : U) : P := rightConjugate P U hUP s u
  let orbitH (u : U) : H :=
    ⟨(orbitP u : G), hPH (orbitP u).property⟩
  let C : Set (U × U) :=
    {uv | hfield.psiValue uv.1 + hfield.psiValue uv.2 = 2}
  let B : Set (H × H) :=
    {xy | IsConj xy.1 sH ∧ IsConj xy.2 sH ∧
      xy.1 * xy.2 = sH ^ 2}
  have hPcomm (x y : P) : x * y = y * x := by
    have hadd : Additive.ofMul (x * y) = Additive.ofMul (y * x) := by
      apply hfield.sigma.injective
      calc
        hfield.sigma (Additive.ofMul (x * y)) =
            hfield.sigma (Additive.ofMul x) +
              hfield.sigma (Additive.ofMul y) := hfield.sigma_mul x y
        _ = hfield.sigma (Additive.ofMul y) +
              hfield.sigma (Additive.ofMul x) := add_comm _ _
        _ = hfield.sigma (Additive.ofMul (y * x)) :=
          (hfield.sigma_mul y x).symm
    exact congrArg Additive.toMul hadd
  have hE : normEquationSet (ZMod p) hfield.F =
      (fun uv : U × U ↦ hfield.psiValue uv.1) '' C := by
    ext x
    constructor
    · intro hx
      obtain ⟨u, hu⟩ :=
        (hfield.im_psi hcardP hcardU x).2 hx.1
      obtain ⟨v, hv⟩ :=
        (hfield.im_psi hcardP hcardU (2 - x)).2 hx.2
      refine ⟨(u, v), ?_, hu⟩
      change hfield.psiValue u + hfield.psiValue v = 2
      rw [hu, hv]
      ring
    · rintro ⟨⟨u, v⟩, huv, rfl⟩
      change hfield.psiValue u + hfield.psiValue v = 2 at huv
      constructor
      · exact (hfield.im_psi hcardP hcardU _).1 ⟨u, rfl⟩
      · apply (hfield.im_psi hcardP hcardU _).1
        refine ⟨v, ?_⟩
        change hfield.psiValue v = 2 - hfield.psiValue u
        rw [eq_sub_iff_add_eq]
        simpa only [add_comm] using huv
  have hfstInj : Set.InjOn
      (fun uv : U × U ↦ hfield.psiValue uv.1) C := by
    rintro ⟨u, v⟩ huv ⟨u', v'⟩ huv' heq
    change hfield.psiValue u + hfield.psiValue v = 2 at huv
    change hfield.psiValue u' + hfield.psiValue v' = 2 at huv'
    have hu : u = u' := hfield.psiValue_injective heq
    subst u'
    have hvpsi : hfield.psiValue v = hfield.psiValue v' := by
      apply add_left_cancel (a := hfield.psiValue u)
      exact huv.trans huv'.symm
    exact Prod.ext rfl (hfield.psiValue_injective hvpsi)
  have hEC : (normEquationSet (ZMod p) hfield.F).ncard = C.ncard := by
    rw [hE]
    exact hfstInj.ncard_image
  have hconjOrbit (x : H) :
      IsConj x sH ↔ ∃ u : U, orbitH u = x := by
    constructor
    · intro hx
      obtain ⟨z, hz⟩ := isConj_iff.mp hx
      obtain ⟨⟨a, u⟩, hau⟩ := hsemi.2 z
      let uU : U := ⟨((u : H) : G), u.property⟩
      let aP : P := ⟨((a : H) : G), a.property⟩
      have haCentral : (a : H)⁻¹ * sH * (a : H) = sH := by
        apply Subtype.ext
        change (aP : G)⁻¹ * (s : G) * (aP : G) = (s : G)
        have hacomm : (aP : G) * (s : G) = (s : G) * (aP : G) :=
          congrArg Subtype.val (hPcomm aP s)
        calc
          (aP : G)⁻¹ * (s : G) * (aP : G) =
              (aP : G)⁻¹ * ((s : G) * (aP : G)) := by
            rw [mul_assoc]
          _ = (aP : G)⁻¹ * ((aP : G) * (s : G)) := by
            rw [hacomm]
          _ = (s : G) := by simp
      have hxform : x = z⁻¹ * sH * z := by
        calc
          x = z⁻¹ * (z * x * z⁻¹) * z := by group
          _ = z⁻¹ * sH * z := by rw [hz]
      refine ⟨uU, ?_⟩
      apply Subtype.ext
      change ((orbitP uU : P) : G) = (x : G)
      rw [coe_rightConjugate]
      have hxformG : (x : G) = (z : G)⁻¹ * (s : G) * (z : G) :=
        congrArg Subtype.val hxform
      rw [hxformG]
      have hauG : (a : G) * (u : G) = (z : G) :=
        congrArg Subtype.val hau
      rw [← hauG]
      have haCentralG : (a : G)⁻¹ * (s : G) * (a : G) = (s : G) :=
        congrArg Subtype.val haCentral
      change (u : G)⁻¹ * (s : G) * (u : G) =
        ((a : G) * (u : G))⁻¹ * (s : G) * ((a : G) * (u : G))
      calc
        (u : G)⁻¹ * (s : G) * (u : G) =
            (u : G)⁻¹ * ((a : G)⁻¹ * (s : G) * (a : G)) *
              (u : G) := by rw [haCentralG]
        _ = ((a : G) * (u : G))⁻¹ * (s : G) *
            ((a : G) * (u : G)) := by group
    · rintro ⟨u, rfl⟩
      rw [isConj_iff]
      let uH : H := ⟨(u : G), hUH u.property⟩
      refine ⟨uH, ?_⟩
      apply Subtype.ext
      change (u : G) * (orbitP u : G) * (u : G)⁻¹ = (s : G)
      rw [coe_rightConjugate]
      group
  have horbitInj : Function.Injective orbitH := by
    intro u v huv
    apply hfield.psiValue_injective
    rw [hfield.psiValue_eq_sigma_rightConjugate hUP s
        hfield.sigma_onePreimage,
      hfield.psiValue_eq_sigma_rightConjugate hUP s
        hfield.sigma_onePreimage]
    congr 1
    apply Subtype.ext
    exact congrArg (fun z : H ↦ (z : G)) huv
  have hsigmaOrbitMul (u v : U) :
      hfield.sigma (Additive.ofMul (orbitP u * orbitP v)) =
        hfield.psiValue u + hfield.psiValue v := by
    calc
      hfield.sigma (Additive.ofMul (orbitP u * orbitP v)) =
          hfield.sigma (Additive.ofMul (orbitP u)) +
            hfield.sigma (Additive.ofMul (orbitP v)) :=
        hfield.sigma_mul _ _
      _ = hfield.psiValue u + hfield.psiValue v := by
        rw [← hfield.psiValue_eq_sigma_rightConjugate hUP s
          hfield.sigma_onePreimage,
          ← hfield.psiValue_eq_sigma_rightConjugate hUP s
            hfield.sigma_onePreimage]
  have hsigmaSquare :
      hfield.sigma (Additive.ofMul (s ^ 2)) = 2 := by
    have hsigmaS : hfield.sigma (Additive.ofMul s) = 1 := by
      simpa only [s] using hfield.sigma_onePreimage
    calc
      hfield.sigma (Additive.ofMul (s ^ 2)) =
          2 • hfield.sigma (Additive.ofMul s) := hfield.sigma_pow s 2
      _ = 2 := by
        simp only [hsigmaS, two_nsmul,
          one_add_one_eq_two]
  have hCmul (u v : U) :
      (u, v) ∈ C ↔ orbitH u * orbitH v = sH ^ 2 := by
    constructor
    · intro huv
      change hfield.psiValue u + hfield.psiValue v = 2 at huv
      apply Subtype.ext
      have hP : orbitP u * orbitP v = s ^ 2 := by
        have hadd : Additive.ofMul (orbitP u * orbitP v) =
            Additive.ofMul (s ^ 2) := by
          apply hfield.sigma.injective
          rw [hsigmaOrbitMul, hsigmaSquare, huv]
        exact congrArg Additive.toMul hadd
      exact congrArg (fun z : P ↦ (z : G)) hP
    · intro huv
      have hP : orbitP u * orbitP v = s ^ 2 := by
        apply Subtype.ext
        exact congrArg (fun z : H ↦ (z : G)) huv
      have hsigma :
          hfield.sigma (Additive.ofMul (orbitP u * orbitP v)) =
            hfield.sigma (Additive.ofMul (s ^ 2)) :=
        congrArg (fun z : P ↦ hfield.sigma (Additive.ofMul z)) hP
      change hfield.psiValue u + hfield.psiValue v = 2
      calc
        hfield.psiValue u + hfield.psiValue v =
            hfield.sigma (Additive.ofMul (orbitP u * orbitP v)) :=
          (hsigmaOrbitMul u v).symm
        _ = hfield.sigma (Additive.ofMul (s ^ 2)) := hsigma
        _ = 2 := hsigmaSquare
  let pairOrbit : U × U → H × H := Prod.map orbitH orbitH
  have hB : B = pairOrbit '' C := by
    ext xy
    constructor
    · rintro ⟨hx, hy, hxy⟩
      obtain ⟨u, hu⟩ := (hconjOrbit xy.1).1 hx
      obtain ⟨v, hv⟩ := (hconjOrbit xy.2).1 hy
      refine ⟨(u, v), (hCmul u v).2 ?_, ?_⟩
      · simpa [hu, hv] using hxy
      · exact Prod.ext hu hv
    · rintro ⟨⟨u, v⟩, huv, rfl⟩
      exact ⟨(hconjOrbit _).2 ⟨u, rfl⟩,
        (hconjOrbit _).2 ⟨v, rfl⟩, (hCmul u v).1 huv⟩
  have hpairOrbitInj : Function.Injective pairOrbit :=
    horbitInj.prodMap horbitInj
  have hBC : B.ncard = C.ncard := by
    rw [hB]
    exact Set.ncard_image_of_injective C hpairOrbitInj
  have hcoef :
      classProductCoefficient sH sH (sH ^ 2) = B.ncard := by
    simpa only [B] using
      classProductCoefficient_eq_solutionSet_ncard sH sH (sH ^ 2)
  have hfinal : (normEquationSet (ZMod p) hfield.F).ncard =
      classProductCoefficient sH sH (sH ^ 2) := by
    calc
      (normEquationSet (ZMod p) hfield.F).ncard = C.ncard := hEC
      _ = B.ncard := hBC.symm
      _ = classProductCoefficient sH sH (sH ^ 2) := hcoef.symm
  simpa only [sH, s] using hfinal

/-! ## The large-degree estimate -/

/-- The missing source-specific `q > 4` calculation in Appendix C.

The strict inequality `q < p` is the contradiction-branch hypothesis in
the source.  It is used here only to ensure that the first two powers of
the distinguished kernel element are nonidentity, as required for the two
column-orthogonality bounds. -/
theorem largeDegreeCharacterObligation
    {G : Type u} [Group G] [Finite G]
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime]
    {H P P0 U : Subgroup G}
    (hfield : FiniteFieldImage P P0 U)
    [Algebra (ZMod p) hfield.F]
    (hPH : P ≤ H) (hUH : U ≤ H)
    (hsemi : (P.subgroupOf H).IsComplement' (U.subgroupOf H))
    (hUP : U ≤ Subgroup.normalizer (P : Set G))
    (hcardP : Nat.card P = p ^ q)
    (hcardU : Nat.card U = nU p q)
    (hqp : q < p) (_hq4 : 4 < q) :
    LargeDegreeCharacterObligation (p := p) (q := q) hfield.F := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  let PH : Subgroup H := P.subgroupOf H
  let UH : Subgroup H := U.subgroupOf H
  let hfrob : IsFrobeniusDecomposition PH UH :=
    hfield.frobH hPH hUH hsemi hUP hcardU
  letI : PH.Normal := hfrob.kernel_normal
  letI : IsMulCommutative P := by
    refine ⟨⟨fun x y ↦ ?_⟩⟩
    have hadd : Additive.ofMul (x * y) = Additive.ofMul (y * x) := by
      apply hfield.sigma.injective
      calc
        hfield.sigma (Additive.ofMul (x * y)) =
            hfield.sigma (Additive.ofMul x) +
              hfield.sigma (Additive.ofMul y) := hfield.sigma_mul x y
        _ = hfield.sigma (Additive.ofMul y) +
              hfield.sigma (Additive.ofMul x) := add_comm _ _
        _ = hfield.sigma (Additive.ofMul (y * x)) :=
          (hfield.sigma_mul y x).symm
    exact congrArg Additive.toMul hadd
  let ePH : PH ≃* P := Subgroup.subgroupOfEquivOfLe hPH
  let eUH : UH ≃* U := Subgroup.subgroupOfEquivOfLe hUH
  letI : IsMulCommutative PH := by
    rw [isMulCommutative_iff]
    intro x y
    apply ePH.injective
    exact mul_comm (ePH x) (ePH y)
  letI : IsCyclic U := hfield.actingGroup_isCyclic
  letI : IsCyclic UH :=
    isCyclic_of_injective eUH.toMonoidHom eUH.injective
  have hcardPH : Nat.card PH = p ^ q := by
    rw [Nat.card_congr ePH.toEquiv, hcardP]
  have hcardUH : Nat.card UH = nU p q := by
    rw [Nat.card_congr eUH.toEquiv, hcardU]
  have hcardH : Nat.card H = p ^ q * nU p q := by
    rw [← hcardPH, ← hcardUH]
    exact hfrob.card_mul_card.symm
  let sP : P := hfield.onePreimage
  let sH : H := ⟨(sP : G), hPH sP.property⟩
  let sPH : PH := ⟨sH, sP.property⟩
  have hsPH : sPH ≠ 1 := by
    intro hs
    apply hfield.onePreimage_ne_one
    apply Subtype.ext
    exact congrArg (fun z : PH ↦ ((z : H) : G)) hs
  have hp2 : 2 < p := lt_trans (by omega : 2 < q) hqp
  have hchar : CharP hfield.F p := by
    rw [← Algebra.charP_iff (ZMod p) hfield.F p]
    exact ZMod.charP p
  letI : CharP hfield.F p := hchar
  have htwo : (2 : hfield.F) ≠ 0 := by
    intro hzero
    have hpdiv : p ∣ 2 :=
      (CharP.cast_eq_zero_iff hfield.F p 2).mp hzero
    have := Nat.le_of_dvd (by omega : 0 < 2) hpdiv
    omega
  have hsPH2 : sPH ^ 2 ≠ 1 := by
    intro hs
    have hsigma := congrArg
      (fun z : P ↦ hfield.sigma (Additive.ofMul z))
      (show sP ^ 2 = 1 by
        apply Subtype.ext
        exact congrArg (fun z : PH ↦ ((z : H) : G)) hs)
    rw [hfield.sigma_pow, hfield.sigma_onePreimage,
      hfield.sigma_one] at hsigma
    exact htwo (by simpa using hsigma)
  let e : ℕ := classProductCoefficient sH sH (sH ^ 2)
  have hnormCard :
      (normEquationSet (ZMod p) hfield.F).ncard = e := by
    exact normEquationSet_ncard_eq_classProductCoefficient
      hfield hPH hUH hsemi hUP hcardP hcardU
  let Nonlinear :=
    {chi : IrreducibleCharacter H ℂ //
      ¬ PH ≤ chi.representation.ρ.ker}
  let raw (chi : IrreducibleCharacter H ℂ) : ℂ :=
    chi sH ^ 2 * star (chi (sH ^ 2))
  letI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype (IrreducibleCharacter H ℂ) := inferInstance
  letI : Fintype (KernelTrivialCharacter PH ℂ) := by
    change Fintype
      {chi : IrreducibleCharacter H ℂ //
        PH ≤ chi.representation.ρ.ker}
    infer_instance
  have hlinCard :
      Fintype.card (KernelTrivialCharacter PH ℂ) = nU p q := by
    rw [kernelTrivialCharacter_card_eq_complement
        (A := H) (k := ℂ) (K := PH) (R := UH) hfrob.isComplement,
      hcardUH]
  have hclassS : conjugacyClassCard sH = nU p q := by
    change conjugacyClassCard (sPH : H) = nU p q
    rw [conjugacyClassCard_eq_complement_card hfrob sPH hsPH,
      hcardUH]
  have hclassSinv : conjugacyClassCard sH⁻¹ = nU p q := by
    let x : PH := sPH⁻¹
    have hx : x ≠ 1 := inv_ne_one.mpr hsPH
    change conjugacyClassCard (x : H) = nU p q
    rw [conjugacyClassCard_eq_complement_card hfrob x hx, hcardUH]
  have hclassS2inv : conjugacyClassCard (sH ^ 2)⁻¹ = nU p q := by
    let x : PH := (sPH ^ 2)⁻¹
    have hx : x ≠ 1 := inv_ne_one.mpr hsPH2
    change conjugacyClassCard (x : H) = nU p q
    rw [conjugacyClassCard_eq_complement_card hfrob x hx, hcardUH]
  have hlinearTerm (chi : IrreducibleCharacter H ℂ)
      (hchi : PH ≤ chi.representation.ρ.ker) :
      chi sH * chi sH * chi (sH ^ 2)⁻¹ / chi 1 = 1 := by
    let chiLin : KernelTrivialCharacter PH ℂ := ⟨chi, hchi⟩
    have hs : chi sH = 1 :=
      kernelTrivialCharacter_apply_kernel hfrob.isComplement chiLin sPH
    have hs2 : chi (sH ^ 2)⁻¹ = 1 := by
      have := kernelTrivialCharacter_apply_kernel
        hfrob.isComplement chiLin ((sPH ^ 2)⁻¹)
      exact this
    have hone : chi 1 = 1 := by
      rw [irreducibleCharacter_apply_one_eq_finrank,
        kernelTrivialCharacter_finrank_eq_one
          hfrob.isComplement chiLin]
      norm_num
    rw [hs, hs2, hone]
    norm_num
  have hnonlinearTerm (chi : IrreducibleCharacter H ℂ)
      (hchi : ¬ PH ≤ chi.representation.ρ.ker) :
      chi sH * chi sH * chi (sH ^ 2)⁻¹ / chi 1 =
        (nU p q : ℂ)⁻¹ * raw chi := by
    have hdegree : Module.finrank ℂ chi.representation = nU p q := by
      rw [← hcardUH]
      exact nonlinearCharacter_finrank_eq_complement_card hfrob chi hchi
    rw [irreducibleCharacter_apply_one_eq_finrank, hdegree,
      irreducibleCharacter_apply_inv_eq_conj]
    dsimp only [raw]
    ring
  have hsum :
      (∑ chi : IrreducibleCharacter H ℂ,
          chi sH * chi sH * chi (sH ^ 2)⁻¹ / chi 1) =
        (nU p q : ℂ) + (nU p q : ℂ)⁻¹ *
          ∑ i : Nonlinear, raw i.1 := by
    let lin : IrreducibleCharacter H ℂ → Prop :=
      fun chi ↦ PH ≤ chi.representation.ρ.ker
    have hcardLin :
        ((Finset.univ : Finset (IrreducibleCharacter H ℂ)).filter
          lin).card = Fintype.card (KernelTrivialCharacter PH ℂ) := by
      change _ = Fintype.card
        {chi : IrreducibleCharacter H ℂ //
          PH ≤ chi.representation.ρ.ker}
      simpa only [lin] using (Fintype.card_subtype lin).symm
    calc
      (∑ chi : IrreducibleCharacter H ℂ,
          chi sH * chi sH * chi (sH ^ 2)⁻¹ / chi 1) =
          (∑ chi ∈ (Finset.univ :
              Finset (IrreducibleCharacter H ℂ)).filter lin,
              chi sH * chi sH * chi (sH ^ 2)⁻¹ / chi 1) +
            ∑ chi ∈ (Finset.univ :
              Finset (IrreducibleCharacter H ℂ)).filter
                (fun chi ↦ ¬ lin chi),
              chi sH * chi sH * chi (sH ^ 2)⁻¹ / chi 1 := by
        rw [← Finset.sum_filter_add_sum_filter_not
          (Finset.univ : Finset (IrreducibleCharacter H ℂ)) lin]
      _ = (∑ _chi ∈ (Finset.univ :
              Finset (IrreducibleCharacter H ℂ)).filter lin, (1 : ℂ)) +
            ∑ chi ∈ (Finset.univ :
              Finset (IrreducibleCharacter H ℂ)).filter
                (fun chi ↦ ¬ lin chi),
              (nU p q : ℂ)⁻¹ * raw chi := by
        congr 1
        · apply Finset.sum_congr rfl
          intro chi hmem
          rw [Finset.mem_filter] at hmem
          exact hlinearTerm chi hmem.2
        · apply Finset.sum_congr rfl
          intro chi hmem
          rw [Finset.mem_filter] at hmem
          exact hnonlinearTerm chi hmem.2
      _ = (Fintype.card (KernelTrivialCharacter PH ℂ) : ℂ) +
          (nU p q : ℂ)⁻¹ * ∑ i : Nonlinear, raw i.1 := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_one, Finset.mul_sum]
        congr 1
        · rw [hcardLin]
        · rw [Finset.sum_subtype
            (p := fun chi : IrreducibleCharacter H ℂ ↦ ¬ lin chi)
            ((Finset.univ : Finset (IrreducibleCharacter H ℂ)).filter
              (fun chi ↦ ¬ lin chi)) (by
                intro chi
                simp [Nonlinear, lin])]
      _ = (nU p q : ℂ) + (nU p q : ℂ)⁻¹ *
          ∑ i : Nonlinear, raw i.1 := by rw [hlinCard]
  have hcoefFormula :=
    classProductCoefficient_eq_characterSum sH sH (sH ^ 2)
  have heq : (e : ℂ) =
      (((nU p q : ℂ) * (nU p q : ℂ)) /
        ((p ^ q : ℂ) * (nU p q : ℂ))) *
        ((nU p q : ℂ) + (nU p q : ℂ)⁻¹ *
          ∑ i : Nonlinear, raw i.1) := by
    simpa only [e, hclassS, hcardH, Nat.cast_mul, Nat.cast_pow, hsum]
      using hcoefFormula
  have hPne : (p ^ q : ℂ) ≠ 0 := by
    have hpprime : p.Prime := Fact.out
    exact pow_ne_zero q (Nat.cast_ne_zero.mpr hpprime.ne_zero)
  have hUne : (nU p q : ℂ) ≠ 0 := by
    rw [← hcardUH]
    exact Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hidentity :
      ((((p ^ q) * e : ℕ) : ℂ) - ((nU p q : ℂ) ^ 2)) =
        ∑ i : Nonlinear, raw i.1 := by
    push_cast
    rw [heq]
    field_simp [hPne, hUne]
    ring
  have hcolumn (x : H)
      (hclass : conjugacyClassCard x⁻¹ = nU p q) :
      (∑ chi : IrreducibleCharacter H ℂ, ‖chi x‖ ^ 2) =
        (p ^ q : ℝ) := by
    have horth := conjugacyClassCard_mul_characterColumn_normSq x
    rw [hclass, hcardH] at horth
    push_cast at horth
    have hUpos : (0 : ℝ) < nU p q := by
      rw [← hcardUH]
      exact_mod_cast (Nat.card_pos : 0 < Nat.card UH)
    nlinarith
  have hsubtypeColumn (x : H)
      (hclass : conjugacyClassCard x⁻¹ = nU p q) :
      (∑ i : Nonlinear, ‖i.1 x‖ ^ 2) ≤ (p ^ q : ℝ) := by
    calc
      (∑ i : Nonlinear, ‖i.1 x‖ ^ 2) =
          ∑ chi ∈ (Finset.univ :
              Finset (IrreducibleCharacter H ℂ)).filter
                (fun chi ↦ ¬ PH ≤ chi.representation.ρ.ker),
            ‖chi x‖ ^ 2 := by
        rw [Finset.sum_subtype
          (p := fun chi : IrreducibleCharacter H ℂ ↦
            ¬ PH ≤ chi.representation.ρ.ker)
          ((Finset.univ : Finset (IrreducibleCharacter H ℂ)).filter
            (fun chi ↦ ¬ PH ≤ chi.representation.ρ.ker)) (by
              intro chi
              simp [Nonlinear])]
      _ ≤ ∑ chi : IrreducibleCharacter H ℂ, ‖chi x‖ ^ 2 := by
        apply Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
        intro chi _ _
        positivity
      _ = (p ^ q : ℝ) := hcolumn x hclass
  have hdist :
      ‖((((p ^ q) * e : ℕ) : ℂ) - ((nU p q : ℂ) ^ 2))‖ ≤
        (p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ) := by
    have hdist' := classCoefficient_distance_le
      (p ^ q) (nU p q) e
      (fun i : Nonlinear ↦ i.1 sH)
      (fun i : Nonlinear ↦ i.1 (sH ^ 2))
      (by simpa only [raw] using hidentity)
      (by simpa only [Nat.cast_pow] using
        hsubtypeColumn sH hclassSinv)
      (by simpa only [Nat.cast_pow] using
        hsubtypeColumn (sH ^ 2) hclassS2inv)
    simpa only [Nat.cast_pow] using hdist'
  exact ⟨e, hnormCard, hdist⟩

end

end Submission.OddOrder.BG.AppendixC
