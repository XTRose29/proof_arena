import Mathlib.Algebra.Group.ConjFinite
import Mathlib.GroupTheory.OrderOfElement
import Submission.OddOrder.PF.Section01.IrreducibleCharacter

/-!
Peterfalvi 1.1: conjugate irreducible characters of groups of odd order.

The conjugate character in the source is the character of the contragredient
representation.  Over an algebraically closed field of characteristic zero it
is again irreducible, and its value at `g` is the original character's value
at `g⁻¹`.

The last input in the source proof is Brauer's permutation lemma: inversion has
the same number of fixed points on conjugacy classes and on irreducible
characters.  Mathlib does not yet contain that theorem.  This file packages
the dual-character API, proves the entire odd-order group-theoretic argument,
and isolates Brauer's lemma as the single explicit hypothesis of
`odd_eq_conj_irr1_of_brauer`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators

universe u v w

variable {G : Type u} {k : Type v} [Group G] [Field k]

open CategoryTheory Limits

/-- Split-universe analogue of Mathlib's injectivity instance for finite-group
representations in characteristic prime to the group order. -/
private instance repInjectiveGeneral
    {G : Type u} {k : Type v} [Group G] [Finite G] [Field k]
    [NeZero (Nat.card G : k)] (V : Rep.{w} k G) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

/-- Split-universe analogue of Mathlib's injectivity instance for bundled
finite-dimensional representations. -/
private instance fdRepInjectiveGeneral
    {G : Type u} {k : Type v} [Group G] [Finite G] [Field k]
    [NeZero (Nat.card G : k)] (V : FDRep k G) : Injective V :=
  (forget₂ (FDRep k G) (Rep k G)).injective_of_map_injective inferInstance

/-- Universe-polymorphic version of Mathlib's
`FDRep.simple_iff_end_is_rank_one`.  The Mathlib declaration currently puts
the group and coefficient field in the same universe, although its proof does
not depend on that restriction. -/
private theorem simple_iff_end_is_rank_one_general
    {G : Type u} {k : Type v} [Group G] [Finite G] [Field k]
    [IsAlgClosed k] [NeZero (Nat.card G : k)] (V : FDRep k G) :
    Simple V ↔ Module.finrank k (V ⟶ V) = 1 where
  mp h := finrank_endomorphism_simple_eq_one k V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ :=
      ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := k)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set ι := Abelian.image.ι f
      set φ := Injective.factorThru (𝟙 _) ι
      have hφι : φ ≫ ι ≠ 0 := by
        intro habs
        have hιφ : 𝟙 _ = ι ≫ φ := (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : ∃ c : k, c • _ = 𝟙 V :=
        (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

/-- Universe-polymorphic version of Mathlib's
`FDRep.simple_iff_char_is_norm_one`. -/
private theorem simple_iff_char_is_norm_one_general
    {G : Type u} {k : Type v} [Group G] [Fintype G] [Field k]
    [IsAlgClosed k] [CharZero k] (V : FDRep k G) :
    Simple V ↔ ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G where
  mp h := by
    have : NeZero (Nat.card G : k) := by
      rw [← @Fintype.card_eq_nat_card G (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
    have := invertibleOfNonzero (NeZero.ne (Fintype.card G : k))
    classical
    have : ⅟(Nat.card G : k) •
        ∑ g, V.character g * V.character g⁻¹ = 1 := by
      simpa only [Nonempty.intro (Iso.refl V), ↓reduceIte,
        Fintype.card_eq_nat_card] using FDRep.char_orthonormal V V
    apply_fun (· * (Fintype.card G : k)) at this
    rwa [mul_comm, ← smul_eq_mul, smul_smul, Fintype.card_eq_nat_card,
      mul_invOf_self, smul_eq_mul, one_mul, one_mul] at this
  mpr h := by
    have : NeZero (Nat.card G : k) := by
      rw [← @Fintype.card_eq_nat_card G (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Fintype.card G : k))
    have := invertibleOfNonzero (NeZero.ne (Nat.card G : k))
    have eq := FDRep.scalar_product_char_eq_finrank_equivariant V V
    rw [h] at eq
    simp only [invOf_eq_inv, smul_eq_mul, inv_mul_cancel_of_invertible,
      Fintype.card_eq_nat_card] at eq
    rw [simple_iff_end_is_rank_one_general, ← Nat.cast_inj (R := k),
      ← eq, Nat.cast_one]

namespace IrreducibleCharacter

section Dual

variable [Fintype G] [IsAlgClosed k] [CharZero k]

private theorem dualFDRep_simple (V : FDRep k G) [CategoryTheory.Simple V] :
    CategoryTheory.Simple (FDRep.of (Representation.dual V.ρ)) := by
  rw [simple_iff_char_is_norm_one_general]
  have h := (simple_iff_char_is_norm_one_general V).mp (by infer_instance)
  simpa only [FDRep.char_dual, inv_inv, mul_comm] using h

/-- The dual (contragredient, or source `conjC`) of an irreducible character. -/
def dual (chi : IrreducibleCharacter G k) : IrreducibleCharacter G k := by
  letI : CategoryTheory.Simple chi.representation := chi.representation_simple
  letI : CategoryTheory.Simple
      (FDRep.of (Representation.dual chi.representation.ρ)) :=
    dualFDRep_simple chi.representation
  exact ofFDRep (FDRep.of (Representation.dual chi.representation.ρ))

@[simp]
theorem dual_apply (chi : IrreducibleCharacter G k) (g : G) :
    dual chi g = chi g⁻¹ := by
  letI : CategoryTheory.Simple chi.representation := chi.representation_simple
  change (FDRep.of (Representation.dual chi.representation.ρ)).character g = chi g⁻¹
  rw [FDRep.char_dual, representation_character]

@[simp]
theorem dual_dual (chi : IrreducibleCharacter G k) : dual (dual chi) = chi := by
  ext g
  simp

/-- Duality is a permutation of the finite set of irreducible characters. -/
def dualEquiv : IrreducibleCharacter G k ≃ IrreducibleCharacter G k where
  toFun := dual
  invFun := dual
  left_inv := dual_dual
  right_inv := dual_dual

private theorem trivialFDRep_simple :
    CategoryTheory.Simple
      (FDRep.of (Representation.trivial k G k)) := by
  rw [simple_iff_char_is_norm_one_general]
  simp [FDRep.character]

/-- The irreducible character of the one-dimensional trivial representation. -/
def trivial : IrreducibleCharacter G k := by
  letI : CategoryTheory.Simple
      (FDRep.of (Representation.trivial k G k)) :=
    trivialFDRep_simple
  exact ofFDRep (FDRep.of (Representation.trivial k G k))

@[simp]
theorem trivial_apply (g : G) : (trivial : IrreducibleCharacter G k) g = 1 := by
  change LinearMap.trace k k LinearMap.id = 1
  simp

@[simp]
theorem dual_trivial : dual (trivial : IrreducibleCharacter G k) = trivial := by
  ext g
  simp

end Dual

end IrreducibleCharacter

namespace ConjClasses

/-- Inversion on conjugacy classes. -/
def inverse (C : ConjClasses G) : ConjClasses G :=
  Quotient.lift (fun g : G ↦ ConjClasses.mk g⁻¹)
    (fun a b hab ↦ by
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      obtain ⟨x, hx⟩ := isConj_iff.mp hab
      apply isConj_iff.mpr
      refine ⟨x, ?_⟩
      rw [← hx, conj_inv]) C

@[simp]
theorem inverse_mk (g : G) : inverse (ConjClasses.mk g) = ConjClasses.mk g⁻¹ :=
  rfl

@[simp]
theorem inverse_inverse (C : ConjClasses G) : inverse (inverse C) = C := by
  induction C using Quotient.inductionOn with
  | _ g =>
      change ConjClasses.mk (g⁻¹)⁻¹ = ConjClasses.mk g
      rw [inv_inv]

/-- Inversion is an involutive permutation of conjugacy classes. -/
def inverseEquiv : ConjClasses G ≃ ConjClasses G where
  toFun := inverse
  invFun := inverse
  left_inv := inverse_inverse
  right_inv := inverse_inverse

end ConjClasses

/-- In a finite group of odd order, an element conjugate to its inverse is the
identity.  This is the group-theoretic core of the Coq proof of Peterfalvi
1.1. -/
theorem eq_one_of_isConj_inv_self [Finite G] (hodd : Odd (Nat.card G))
    {g : G} (hg : IsConj g⁻¹ g) : g = 1 := by
  have hcop : (Nat.card G).Coprime 2 := hodd.coprime_two_right
  obtain ⟨x, hx⟩ := isConj_iff.mp hg
  have hx' : x * g * x⁻¹ = g⁻¹ := by
    have := congrArg Inv.inv hx
    rw [conj_inv, inv_inv] at this
    exact this
  have hxg : x * g = g⁻¹ * x :=
    (mul_inv_eq_iff_eq_mul).mp hx'
  have hxginv : x * g⁻¹ = g * x :=
    (mul_inv_eq_iff_eq_mul).mp hx
  have hcommSq : Commute (x ^ 2) g := by
    rw [commute_iff_eq, pow_two]
    calc
      x * x * g = x * (x * g) := by rw [mul_assoc]
      _ = x * (g⁻¹ * x) := by rw [hxg]
      _ = (x * g⁻¹) * x := by rw [mul_assoc]
      _ = g * x * x := by rw [hxginv]
      _ = g * (x * x) := by rw [mul_assoc]
  have hxpow : (x ^ 2) ^ (Nat.card G).gcdB 2 = x := by
    change (powCoprime hcop).symm (powCoprime hcop x) = x
    exact (powCoprime hcop).symm_apply_apply x
  have hcomm : Commute x g := by
    rw [← hxpow]
    exact hcommSq.zpow_left ((Nat.card G).gcdB 2)
  have hginv : g⁻¹ = g := by
    rw [← hx']
    exact hcomm.mul_inv_cancel
  have hgsq : g ^ 2 = 1 := by
    calc
      g ^ 2 = g * g := pow_two g
      _ = g⁻¹ * g := congrArg (fun z : G ↦ z * g) hginv.symm
      _ = 1 := inv_mul_cancel g
  apply hcop.pow_left_bijective.injective
  change g ^ 2 = (1 : G) ^ 2
  simpa using hgsq

section BrauerReduction

variable [Fintype G] [IsAlgClosed k] [CharZero k]

local instance : Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- Irreducible characters fixed by contragredient duality. -/
abbrev SelfDualIrreducibleCharacter :=
  {chi : IrreducibleCharacter G k // IrreducibleCharacter.dual chi = chi}

/-- Conjugacy classes fixed by inversion. -/
abbrev InverseFixedConjugacyClass :=
  {C : ConjClasses G // ConjClasses.inverse C = C}

/-- The precise form of Brauer's permutation lemma needed for Peterfalvi 1.1.

The Coq source obtains this equality from `card_afix_irr_classes`.  This is the
only character-theoretic ingredient of PF 1.1 not currently available in
Mathlib. -/
def BrauerPermutationCardinality : Prop :=
  Nat.card (SelfDualIrreducibleCharacter (G := G) (k := k)) =
    Nat.card (InverseFixedConjugacyClass (G := G))

/-- Odd-order inversion-fixed conjugacy classes are the identity class. -/
theorem inverseFixedConjugacyClass_eq_one (hodd : Odd (Nat.card G))
    (C : ConjClasses G) (hC : ConjClasses.inverse C = C) : C = 1 := by
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective C
  change ConjClasses.mk g⁻¹ = ConjClasses.mk g at hC
  have hg : IsConj g⁻¹ g :=
    ConjClasses.mk_eq_mk_iff_isConj.mp hC
  rw [eq_one_of_isConj_inv_self hodd hg]
  rfl

theorem card_inverseFixedConjugacyClass (hodd : Odd (Nat.card G)) :
    Nat.card (InverseFixedConjugacyClass (G := G)) = 1 := by
  let C₁ : InverseFixedConjugacyClass (G := G) :=
    ⟨1, by
      change ConjClasses.inverse (ConjClasses.mk (1 : G)) = ConjClasses.mk 1
      simp⟩
  letI : Nonempty (InverseFixedConjugacyClass (G := G)) := ⟨C₁⟩
  letI : Subsingleton (InverseFixedConjugacyClass (G := G)) :=
    ⟨fun C D ↦ by
      apply Subtype.ext
      exact (inverseFixedConjugacyClass_eq_one hodd C.1 C.2).trans
        (inverseFixedConjugacyClass_eq_one hodd D.1 D.2).symm⟩
  exact Nat.card_unique

/-- Peterfalvi 1.1, reduced exactly to Brauer's permutation lemma.

Once `BrauerPermutationCardinality` is supplied, the remaining proof is the
source argument: oddness leaves only the identity inverse-fixed conjugacy
class, so duality leaves only the trivial irreducible character fixed. -/
theorem odd_eq_conj_irr1_of_brauer
    (hBrauer : BrauerPermutationCardinality (G := G) (k := k))
    (hodd : Odd (Nat.card G)) (chi : IrreducibleCharacter G k) :
    IrreducibleCharacter.dual chi = chi ↔
      chi = IrreducibleCharacter.trivial := by
  constructor
  · intro hchi
    have hcard : Nat.card (SelfDualIrreducibleCharacter (G := G) (k := k)) = 1 :=
      hBrauer.trans (card_inverseFixedConjugacyClass (G := G) hodd)
    have hsub : Subsingleton (SelfDualIrreducibleCharacter (G := G) (k := k)) :=
      (Nat.card_eq_one_iff_unique.mp hcard).1
    have heq :
        (⟨chi, hchi⟩ : SelfDualIrreducibleCharacter (G := G) (k := k)) =
          ⟨IrreducibleCharacter.trivial,
            IrreducibleCharacter.dual_trivial⟩ :=
      hsub.elim _ _
    exact congrArg Subtype.val heq
  · rintro rfl
    exact IrreducibleCharacter.dual_trivial

end BrauerReduction

end

end Submission.OddOrder.PF
