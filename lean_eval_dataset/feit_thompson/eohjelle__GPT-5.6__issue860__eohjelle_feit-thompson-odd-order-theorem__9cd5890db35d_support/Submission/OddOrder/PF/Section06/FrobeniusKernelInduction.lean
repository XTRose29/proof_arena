import Submission.OddOrder.BG.Section03.FrobeniusBasic
import Submission.OddOrder.PF.Section01.InducedCharacterCompatibility
import Submission.OddOrder.PF.Section01.VirtualCharacter
import Submission.OddOrder.PF.Section04.PrimeTIInductionCases

/-!
# Induction from a Frobenius kernel

This file ports the two Frobenius-kernel results from `inertia.v`, lines
1550--1595 (Isaacs, Theorem 6.34(a)).  Brauer's permutation lemma shows that
a nonprincipal irreducible character of the kernel cannot be fixed by a
nonidentity complement element: after passing to a prime-order power, the
only invariant conjugacy class has the identity as representative.  The
inertia subgroup is therefore the kernel, and Peterfalvi (1.5)(b) makes its
induction irreducible.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.MathlibSupport
open CategoryTheory
open scoped Classical

universe u

/-!
The transport and induced-representation wrappers available earlier in the
port put the group and coefficient field in one universe.  The two local
constructions below are the universe-polymorphic forms needed here, where the
ambient finite group may live in `Type u` while ordinary characters take
values in `ℂ : Type`.
-/

namespace FrobeniusKernelInductionAux

universe v

variable {A : Type u} [Group A] [Fintype A]
variable {H : Subgroup A} [H.Normal]
variable {k : Type v} [Field k] [IsAlgClosed k] [CharZero k]

local instance : Fintype (ConjClasses H) := Fintype.ofFinite _
local instance : DecidableEq (ConjClasses H) := Classical.decEq _
local instance : DecidableEq (IrreducibleCharacter H k) := Classical.decEq _
local instance irreducibleCardInvertible : Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
local instance irreducibleCharacterFinite :
    Finite (IrreducibleCharacter H k) :=
  IrreducibleCharacter.linearIndependent.finite
local instance irreducibleCharacterFintype :
    Fintype (IrreducibleCharacter H k) :=
  Fintype.ofFinite _

/-- The permutation of irreducible characters induced by ambient
conjugation.  Unlike `equivOfMulEquiv`, this construction keeps the group and
coefficient universes independent. -/
def irreducibleConjPerm (a : A) :
    Equiv.Perm (IrreducibleCharacter H k) := by
  letI := IrreducibleCharacter.normalConjugationMulAction (k := k) H
  exact MulAction.toPerm a

@[simp]
theorem irreducibleConjPerm_apply (a : A)
    (chi : IrreducibleCharacter H k) :
    irreducibleConjPerm (H := H) (k := k) a chi =
      chi.normalConjugate H a :=
  rfl

/-- The matching permutation of conjugacy classes. -/
def conjugacyClassPerm (a : A) : Equiv.Perm (ConjClasses H) :=
  PrimeTIInductionCasesAux.conjClassesEquiv (MulAut.conjNormal a)

@[simp]
theorem conjugacyClassPerm_mk (a : A) (h : H) :
    conjugacyClassPerm (H := H) a (ConjClasses.mk h) =
      ConjClasses.mk (MulAut.conjNormal a h) :=
  rfl

/-- Pullback of class functions along the inner automorphism itself. -/
private def classFunctionConjLinear (a : A) :
    ClassFunction H k →ₗ[k] ClassFunction H k where
  toFun f :=
    ⟨fun h ↦ f (MulAut.conjNormal a h), fun x h ↦ by
      change f (MulAut.conjNormal a (x * h * x⁻¹)) =
        f (MulAut.conjNormal a h)
      rw [map_mul, map_mul, map_inv]
      exact ClassFunction.conj_apply f (MulAut.conjNormal a x)
        (MulAut.conjNormal a h)⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

@[simp]
private theorem classFunctionConjLinear_apply (a : A)
    (f : ClassFunction H k) (h : H) :
    classFunctionConjLinear (H := H) (k := k) a f h =
      f (MulAut.conjNormal a h) :=
  rfl

/-- Permutation operator on irreducible-character coordinates. -/
private def irreducibleConjPermutationLinear (a : A) :
    (IrreducibleCharacter H k → k) →ₗ[k]
      (IrreducibleCharacter H k → k) := by
  exact Matrix.toLin'
    (Equiv.Perm.permMatrix k
      (irreducibleConjPerm (H := H) (k := k) a))

@[simp]
private theorem irreducibleConjPermutationLinear_apply (a : A)
    (c : IrreducibleCharacter H k → k)
    (chi : IrreducibleCharacter H k) :
    irreducibleConjPermutationLinear (H := H) (k := k) a c chi =
      c (irreducibleConjPerm (H := H) (k := k) a chi) := by
  rw [irreducibleConjPermutationLinear, Matrix.toLin'_apply,
    Matrix.permMatrix_mulVec]
  rfl

/-- Permutation operator on conjugacy-class coordinates. -/
private def conjugacyClassPermutationLinear (a : A) :
    (ConjClasses H → k) →ₗ[k] (ConjClasses H → k) := by
  exact Matrix.toLin'
    (Equiv.Perm.permMatrix k (conjugacyClassPerm (H := H) a))

@[simp]
private theorem conjugacyClassPermutationLinear_apply (a : A)
    (c : ConjClasses H → k) (C : ConjClasses H) :
    conjugacyClassPermutationLinear (H := H) (k := k) a c C =
      c (conjugacyClassPerm (H := H) a C) := by
  rw [conjugacyClassPermutationLinear, Matrix.toLin'_apply,
    Matrix.permMatrix_mulVec]
  rfl

private theorem conjClassesLinearEquiv_conj_conjLinear (a : A) :
    (ClassFunction.conjClassesLinearEquiv (G := H) (k := k)).conj
        (classFunctionConjLinear (H := H) (k := k) a) =
      conjugacyClassPermutationLinear (H := H) (k := k) a := by
  apply LinearMap.ext
  intro f
  funext C
  obtain ⟨h, rfl⟩ := ConjClasses.mk_surjective C
  rw [conjugacyClassPermutationLinear_apply]
  rfl

private theorem irreducibleCharacterSynthesis_conj (a : A)
    (c : IrreducibleCharacter H k → k) :
    irreducibleCharacterSynthesis
        (irreducibleConjPermutationLinear (H := H) (k := k) a c) =
      classFunctionConjLinear (H := H) (k := k) a
        (irreducibleCharacterSynthesis c) := by
  ext h
  simp only [irreducibleCharacterSynthesis,
    Fintype.linearCombination_apply,
    irreducibleConjPermutationLinear_apply,
    classFunctionConjLinear_apply, ClassFunction.finset_sum_apply,
    ClassFunction.smul_apply, smul_eq_mul]
  apply Fintype.sum_equiv
    (irreducibleConjPerm (H := H) (k := k) a)
  intro chi
  change
    c (chi.normalConjugate H a) * chi h =
      c (chi.normalConjugate H a) *
        chi.normalConjugate H a (MulAut.conjNormal a h)
  rw [IrreducibleCharacter.coe_normalConjugate,
    ClassFunction.normalConjugate_apply]
  simp

private theorem irreducibleCharacterSynthesisEquiv_conj_conjLinear
    (a : A) :
    (irreducibleCharacterSynthesisEquiv
        (irreducibleCharacterComplete (G := H) (k := k))).conj
        (irreducibleConjPermutationLinear (H := H) (k := k) a) =
      classFunctionConjLinear (H := H) (k := k) a := by
  ext f h
  let c := (irreducibleCharacterSynthesisEquiv
    (irreducibleCharacterComplete (G := H) (k := k))).symm f
  have hc := irreducibleCharacterSynthesis_conj
    (H := H) (k := k) a c
  simpa [irreducibleCharacterSynthesisEquiv, c,
    LinearEquiv.conj_apply_apply] using
      congrArg (fun q : ClassFunction H k ↦ q h) hc

/-- Brauer permutation for inner automorphisms, with independent universes
for the finite group and the character field. -/
theorem brauerPermutationCardinality_inner (a : A) :
    (Function.fixedPoints
        (irreducibleConjPerm (H := H) (k := k) a)).ncard =
      (Function.fixedPoints (conjugacyClassPerm (H := H) a)).ncard := by
  have hrow :
      LinearMap.trace k (IrreducibleCharacter H k → k)
          (irreducibleConjPermutationLinear (H := H) (k := k) a) =
        ((Function.fixedPoints
          (irreducibleConjPerm (H := H) (k := k) a)).ncard : k) := by
    rw [irreducibleConjPermutationLinear, Matrix.trace_toLin'_eq,
      Matrix.trace_permutation]
  have hclass :
      LinearMap.trace k (ConjClasses H → k)
          (conjugacyClassPermutationLinear (H := H) (k := k) a) =
        ((Function.fixedPoints
          (conjugacyClassPerm (H := H) a)).ncard : k) := by
    rw [conjugacyClassPermutationLinear, Matrix.trace_toLin'_eq,
      Matrix.trace_permutation]
  have htrace₁ := LinearMap.trace_conj'
    (R := k) (classFunctionConjLinear (H := H) (k := k) a)
      (ClassFunction.conjClassesLinearEquiv (G := H) (k := k))
  rw [conjClassesLinearEquiv_conj_conjLinear
    (H := H) (k := k) a] at htrace₁
  have htrace₂ := LinearMap.trace_conj'
    (R := k)
      (irreducibleConjPermutationLinear (H := H) (k := k) a)
      (irreducibleCharacterSynthesisEquiv
        (irreducibleCharacterComplete (G := H) (k := k)))
  rw [irreducibleCharacterSynthesisEquiv_conj_conjLinear
    (H := H) (k := k) a] at htrace₂
  have hcast :
      ((Function.fixedPoints
        (irreducibleConjPerm (H := H) (k := k) a)).ncard : k) =
        ((Function.fixedPoints
          (conjugacyClassPerm (H := H) a)).ncard : k) := by
    rw [← hrow, ← hclass, htrace₁, htrace₂]
  exact Nat.cast_injective hcast

/-! A universe-polymorphic restriction multiplicity. -/

private def restrictFDRep (S : Subgroup A) (V : FDRep k A) : FDRep k S :=
  FDRep.of (V.ρ.comp S.subtype)

@[simp]
private theorem ofRepresentation_restrictFDRep
    (S : Subgroup A) (V : FDRep k A) :
    ClassFunction.ofRepresentation (restrictFDRep S V).ρ =
      ClassFunction.restrict S (ClassFunction.ofRepresentation V.ρ) := by
  ext s
  rfl

private theorem characterPairing_ofRepresentation_eq_finrank_hom
    {B : Type u} [Group B] [Fintype B]
    (V W : FDRep k B) :
    characterPairing (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) =
      (Module.finrank k (W ⟶ V) : k) := by
  letI : Invertible (Nat.card B : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card B : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hhom := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcharV (b : B) :
      V.character b = _root_.Representation.character V.ρ b := rfl
  have hcharW (b : B) :
      W.character b = _root_.Representation.character W.ρ b := rfl
  simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
    invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
    hcharV, hcharW] using hhom

private def restrictionMultiplicity (S : Subgroup A)
    (psi : IrreducibleCharacter A k)
    (theta : IrreducibleCharacter S k) : ℕ :=
  Module.finrank k
    (theta.representation ⟶ restrictFDRep S psi.representation)

private theorem characterPairing_restrict_eq_restrictionMultiplicity
    (S : Subgroup A) (psi : IrreducibleCharacter A k)
    (theta : IrreducibleCharacter S k) :
    characterPairing
        (ClassFunction.restrict S (psi : ClassFunction A k))
        (theta : ClassFunction S k) =
      (restrictionMultiplicity S psi theta : k) := by
  rw [← psi.ofRepresentation_representation,
    ← ofRepresentation_restrictFDRep,
    ← theta.ofRepresentation_representation]
  exact characterPairing_ofRepresentation_eq_finrank_hom
    (restrictFDRep S psi.representation) theta.representation

/-- Peterfalvi's inertia criterion, proved without the same-universe
induced-representation wrapper.  Frobenius reciprocity shows that induction
has nonnegative integral coefficients in the ambient irreducible basis; its
inertia norm is one, so that integral vector is a single positive basis
vector. -/
theorem irreducible_induce_of_inertia
    (theta : IrreducibleCharacter H k)
    (hI : ClassFunction.inertia H (theta : ClassFunction H k) ≤ H) :
    IsIrreducibleCharacter A k
      (ClassFunction.induce H (theta : ClassFunction H k)) := by
  classical
  letI : Invertible (Nat.card H : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card A : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Finite (IrreducibleCharacter A k) :=
    IrreducibleCharacter.linearIndependent.finite
  letI : Fintype (IrreducibleCharacter A k) :=
    Fintype.ofFinite _
  let multiplicity (psi : IrreducibleCharacter A k) : ℕ :=
    restrictionMultiplicity H psi theta
  let F : VirtualCharacter A k :=
    ∑ psi : IrreducibleCharacter A k,
      Finsupp.single psi (multiplicity psi : ℤ)
  have hFdef : F = ∑ psi : IrreducibleCharacter A k,
      Finsupp.single psi (multiplicity psi : ℤ) := rfl
  have hFcoeff (psi : IrreducibleCharacter A k) :
      F psi = (multiplicity psi : ℤ) := by
    have heval : F psi = ∑ c : IrreducibleCharacter A k,
        (Finsupp.single c (multiplicity c : ℤ)) psi := by
      calc
        F psi =
            (Finsupp.lapply psi :
              VirtualCharacter A k →ₗ[ℤ] ℤ) F := by
          rw [Finsupp.lapply_apply]
        _ = (Finsupp.lapply psi :
              VirtualCharacter A k →ₗ[ℤ] ℤ)
              (∑ c : IrreducibleCharacter A k,
                Finsupp.single c (multiplicity c : ℤ)) :=
          congrArg (Finsupp.lapply psi :
            VirtualCharacter A k →ₗ[ℤ] ℤ) hFdef
        _ = ∑ c : IrreducibleCharacter A k,
              (Finsupp.lapply psi :
                VirtualCharacter A k →ₗ[ℤ] ℤ)
                (Finsupp.single c (multiplicity c : ℤ)) := by
          rw [map_sum]
        _ = ∑ c : IrreducibleCharacter A k,
              (Finsupp.single c (multiplicity c : ℤ)) psi := by
          apply Finset.sum_congr rfl
          intro c _
          rw [Finsupp.lapply_apply]
    rw [heval]
    rw [Finset.sum_eq_single psi, Finsupp.single_eq_same]
    · intro c _ hc
      exact Finsupp.single_eq_of_ne hc.symm
    · intro hpsi
      exact (hpsi (Finset.mem_univ psi)).elim
  have hIndPair (psi : IrreducibleCharacter A k) :
      characterPairing (psi : ClassFunction A k)
          (ClassFunction.induce H (theta : ClassFunction H k)) =
        (multiplicity psi : k) := by
    calc
      characterPairing (psi : ClassFunction A k)
          (ClassFunction.induce H (theta : ClassFunction H k)) =
          characterPairing
            (ClassFunction.induce H (theta : ClassFunction H k))
            (psi : ClassFunction A k) := characterPairing_comm _ _
      _ = characterPairing (theta : ClassFunction H k)
          (ClassFunction.restrict H (psi : ClassFunction A k)) :=
        ClassFunction.frobeniusReciprocity H _ _
      _ = characterPairing
          (ClassFunction.restrict H (psi : ClassFunction A k))
          (theta : ClassFunction H k) := characterPairing_comm _ _
      _ = (multiplicity psi : k) := by
        exact characterPairing_restrict_eq_restrictionMultiplicity
          H psi theta
  have hFPair (psi : IrreducibleCharacter A k) :
      characterPairing (psi : ClassFunction A k)
          (VirtualCharacter.realize F) =
        (multiplicity psi : k) := by
    rw [VirtualCharacter.characterPairing_irreducible_realize, hFcoeff]
    simp
  have hreal :
      VirtualCharacter.realize F =
        ClassFunction.induce H (theta : ClassFunction H k) := by
    apply sub_eq_zero.mp
    apply classFunction_eq_zero_of_forall_irreducible_pairing_eq_zero
    intro psi
    have hpairEq :
        characterPairing (psi : ClassFunction A k)
            (VirtualCharacter.realize F) =
          characterPairing (psi : ClassFunction A k)
            (ClassFunction.induce H (theta : ClassFunction H k)) :=
      (hFPair psi).trans (hIndPair psi).symm
    change (IrreducibleCharacter.pairingLeft (psi : ClassFunction A k))
      (VirtualCharacter.realize F -
        ClassFunction.induce H (theta : ClassFunction H k)) = 0
    calc
      _ = characterPairing (psi : ClassFunction A k)
            (VirtualCharacter.realize F) -
          characterPairing (psi : ClassFunction A k)
            (ClassFunction.induce H (theta : ClassFunction H k)) :=
        map_sub (IrreducibleCharacter.pairingLeft
          (psi : ClassFunction A k)) _ _
      _ = 0 := sub_eq_zero.mpr hpairEq
  have hpairF :
      characterPairing (VirtualCharacter.realize F)
          (VirtualCharacter.realize F) = 1 := by
    rw [hreal]
    exact ClassFunction.inertia_Ind_norm_one H theta hI
  have hnormCast : (normSq F : k) = 1 := by
    simpa only [normSq] using
      (VirtualCharacter.characterPairing_realize F F).symm.trans hpairF
  have hnorm : normSq F = 1 := by
    exact_mod_cast hnormCast
  obtain ⟨psi, epsilon, hepsilon, hsingle⟩ :=
    eq_signed_single_of_normSq_eq_one F hnorm
  have hepsilonNat : epsilon = (multiplicity psi : ℤ) := by
    have hcoeff := congrArg
      (fun q : VirtualCharacter A k ↦ q psi) hsingle
    rw [hFcoeff] at hcoeff
    simpa using hcoeff.symm
  have hepsilonOne : epsilon = 1 := by
    rcases hepsilon with hepsilon | hepsilon
    · exact hepsilon
    · rw [hepsilon] at hepsilonNat
      have hnonneg : 0 ≤ (multiplicity psi : ℤ) := by positivity
      omega
  have hrealSingle :
      VirtualCharacter.realize F = (psi : ClassFunction A k) := by
    calc
      VirtualCharacter.realize F =
          VirtualCharacter.realize
            (Finsupp.single psi epsilon : VirtualCharacter A k) :=
        congrArg VirtualCharacter.realize hsingle
      _ = (epsilon : k) • (psi : ClassFunction A k) :=
        VirtualCharacter.realize_single psi epsilon
      _ = (psi : ClassFunction A k) := by rw [hepsilonOne]; simp
  have hind :
      ClassFunction.induce H (theta : ClassFunction H k) =
        (psi : ClassFunction A k) :=
    hreal.symm.trans hrealSingle
  rw [hind]
  exact psi.property

end FrobeniusKernelInductionAux

/-! ## Isaacs 6.34(a1) -/

/-- `inertia.v: inertia_Frobenius_ker`.

The inertia subgroup of a nonprincipal irreducible character of a
Frobenius kernel is the kernel itself. -/
theorem inertia_Frobenius_ker
    {A : Type u} [Group A] [Fintype A]
    {K R : Subgroup A}
    (hFrob : IsFrobeniusDecomposition K R)
    (theta : IrreducibleCharacter K ℂ)
    (htheta : theta ≠ IrreducibleCharacter.trivial) :
    @ClassFunction.inertia A ℂ _ _ K hFrob.kernel_normal
        (theta : ClassFunction K ℂ) = K := by
  classical
  letI : K.Normal := hFrob.kernel_normal
  apply le_antisymm
  · intro g hg
    obtain ⟨⟨x, r⟩, hxr⟩ := hFrob.isComplement.2 g
    have hxI : (x : A) ∈
        ClassFunction.inertia K (theta : ClassFunction K ℂ) :=
      ClassFunction.le_inertia K _ x.property
    have hrI : (r : A) ∈
        ClassFunction.inertia K (theta : ClassFunction K ℂ) := by
      have hprod :=
        (ClassFunction.inertia K (theta : ClassFunction K ℂ)).mul_mem
          ((ClassFunction.inertia K
            (theta : ClassFunction K ℂ)).inv_mem hxI) hg
      simpa only [← hxr, inv_mul_cancel_left] using hprod
    by_cases hr : r = 1
    · rw [← hxr, hr]
      simpa using x.property
    · exfalso
      have hrOrderNe : orderOf r ≠ 1 := by
        intro hord
        exact hr (orderOf_eq_one_iff.mp hord)
      obtain ⟨p, hp, hpOrder⟩ := Nat.exists_prime_and_dvd hrOrderNe
      let m : ℕ := orderOf r / p
      let a : R := r ^ m
      have haOrder : orderOf a = p := by
        exact orderOf_pow_orderOf_div (orderOf_pos r).ne' hpOrder
      have haNe : a ≠ 1 := by
        intro ha
        have : orderOf a = 1 := orderOf_eq_one_iff.mpr ha
        rw [haOrder] at this
        exact hp.ne_one this
      have haI : (a : A) ∈
          ClassFunction.inertia K (theta : ClassFunction K ℂ) := by
        exact (ClassFunction.inertia K
          (theta : ClassFunction K ℂ)).pow_mem hrI m
      have hatheta : theta.normalConjugate K (a : A) = theta := by
        apply Subtype.ext
        exact (ClassFunction.mem_inertia_iff K
          (theta : ClassFunction K ℂ) (a : A)).mp haI

      let e : K ≃* K := MulAut.conjNormal (a : A)
      let rowPerm :
          IrreducibleCharacter K ℂ ≃ IrreducibleCharacter K ℂ :=
        FrobeniusKernelInductionAux.irreducibleConjPerm
          (H := K) (k := ℂ) (a : A)
      let classPerm : ConjClasses K ≃ ConjClasses K :=
        FrobeniusKernelInductionAux.conjugacyClassPerm
          (H := K) (a : A)
      let FixedIrr := Function.fixedPoints rowPerm
      let FixedClass := Function.fixedPoints classPerm
      have hbrauer : Nat.card FixedIrr = Nat.card FixedClass := by
        exact
          FrobeniusKernelInductionAux.brauerPermutationCardinality_inner
            (H := K) (k := ℂ) (a : A)

      have haOrderA : orderOf (a : A) = p := by
        exact (Subgroup.orderOf_coe a).trans haOrder
      have hpR : p ∣ Nat.card R := by
        rw [← haOrderA]
        exact R.orderOf_dvd_natCard a.property
      have hpKcop : p.Coprime (Nat.card K) :=
        (hFrob.natCard_coprime.coprime_dvd_right hpR).symm
      let fixedClassRep (C : FixedClass) : K := Classical.choose
        (PrimeTIInductionCasesAux.exists_fixed_conjugacy_representative
          K (a : A) (by simpa only [haOrderA] using hp)
          (by simpa only [haOrderA] using hpKcop) C.1 C.2)
      have fixedClassRep_spec (C : FixedClass) :
          ConjClasses.mk (fixedClassRep C) = C.1 ∧
            MulAut.conjNormal (a : A) (fixedClassRep C) =
              fixedClassRep C :=
        Classical.choose_spec
          (PrimeTIInductionCasesAux.exists_fixed_conjugacy_representative
            K (a : A) (by simpa only [haOrderA] using hp)
            (by simpa only [haOrderA] using hpKcop) C.1 C.2)
      have fixedClassRep_eq_one (C : FixedClass) :
          fixedClassRep C = 1 := by
        apply hFrob.fixedPointFree a haNe
        have hfix := congrArg (fun y : K ↦ (y : A))
          (fixedClassRep_spec C).2
        simpa only [MulAut.conjNormal_apply] using hfix
      let fixedOne : FixedClass :=
        ⟨ConjClasses.mk (1 : K), by
          change FrobeniusKernelInductionAux.conjugacyClassPerm
              (H := K) (a : A)
              (ConjClasses.mk (1 : K)) = ConjClasses.mk (1 : K)
          change ConjClasses.mk (e 1) = ConjClasses.mk (1 : K)
          simp⟩
      letI : Subsingleton FixedClass :=
        ⟨by
          intro C D
          apply Subtype.ext
          calc
            C.1 = ConjClasses.mk (fixedClassRep C) :=
              (fixedClassRep_spec C).1.symm
            _ = ConjClasses.mk (1 : K) :=
              congrArg ConjClasses.mk (fixedClassRep_eq_one C)
            _ = ConjClasses.mk (fixedClassRep D) :=
              congrArg ConjClasses.mk (fixedClassRep_eq_one D).symm
            _ = D.1 := (fixedClassRep_spec D).1⟩
      letI : Nonempty FixedClass := ⟨fixedOne⟩
      have hcardFixedClass : Nat.card FixedClass = 1 := Nat.card_unique
      have hcardFixedIrr : Nat.card FixedIrr = 1 :=
        hbrauer.trans hcardFixedClass
      letI : Subsingleton FixedIrr :=
        (Nat.card_eq_one_iff_unique.mp hcardFixedIrr).1

      let thetaFixed : FixedIrr :=
        ⟨theta, by
          change theta.normalConjugate K (a : A) = theta
          exact hatheta⟩
      let trivialFixed : FixedIrr :=
        ⟨IrreducibleCharacter.trivial, by
          change IrreducibleCharacter.trivial.normalConjugate K (a : A) =
            IrreducibleCharacter.trivial
          apply IrreducibleCharacter.ext
          intro y
          change (IrreducibleCharacter.trivial :
            IrreducibleCharacter K ℂ)
              ((MulAut.conjNormal (a : A)).symm y) =
            IrreducibleCharacter.trivial y
          simp⟩
      apply htheta
      exact congrArg (fun q : FixedIrr ↦ q.1)
        (Subsingleton.elim thetaFixed trivialFixed)
  · exact ClassFunction.le_inertia K _

/-! ## Isaacs 6.34(a2) -/

/-- `inertia.v: irr_induced_Frobenius_ker`.

Induction of a nonprincipal irreducible character from a Frobenius kernel
is irreducible. -/
theorem irr_induced_Frobenius_ker
    {A : Type u} [Group A] [Fintype A]
    {K R : Subgroup A}
    (hFrob : IsFrobeniusDecomposition K R)
    (theta : IrreducibleCharacter K ℂ)
    (htheta : theta ≠ IrreducibleCharacter.trivial) :
    IsIrreducibleCharacter A ℂ
      (ClassFunction.induce K (theta : ClassFunction K ℂ)) := by
  letI : K.Normal := hFrob.kernel_normal
  letI : Invertible (Nat.card K : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  apply FrobeniusKernelInductionAux.irreducible_induce_of_inertia
    (H := K) theta
  rw [inertia_Frobenius_ker hFrob theta htheta]

end

end Submission.OddOrder.PF
