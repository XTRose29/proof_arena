import Submission.OddOrder.PF.Section01.BrauerPermutation
import Submission.OddOrder.PF.Section01.ClassFunctionRingHom
import Mathlib.LinearAlgebra.Basis.Basic
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# Irreducible characters of a direct product

This file supplies the character-theoretic direct-product API used in
Peterfalvi Section 3.  The construction is the external tensor product of
representations.  Its irreducibility is proved from character orthogonality,
and completeness of irreducible characters is then used to prove that every
irreducible character of a product occurs in this way.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

open CategoryTheory Limits

universe u v w

namespace ClassFunction

variable {A B : Type u} {R : Type v}
  [Group A] [Group B] [CommRing R]

/-- The external product of two class functions. -/
def externalProduct (f : ClassFunction A R) (g : ClassFunction B R) :
    ClassFunction (A × B) R where
  val x := f x.1 * g x.2
  property x y := by
    change f (x.1 * y.1 * x.1⁻¹) * g (x.2 * y.2 * x.2⁻¹) =
      f y.1 * g y.2
    rw [ClassFunction.conj_apply f, ClassFunction.conj_apply g]

@[simp]
theorem externalProduct_apply (f : ClassFunction A R)
    (g : ClassFunction B R) (a : A) (b : B) :
    externalProduct f g (a, b) = f a * g b :=
  rfl

@[simp]
theorem externalProduct_zero_left (g : ClassFunction B R) :
    externalProduct (0 : ClassFunction A R) g = 0 := by
  ext x
  change 0 * g x.2 = 0
  simp

@[simp]
theorem externalProduct_zero_right (f : ClassFunction A R) :
    externalProduct f (0 : ClassFunction B R) = 0 := by
  ext x
  change f x.1 * 0 = 0
  simp

@[simp]
theorem externalProduct_add_left (f₁ f₂ : ClassFunction A R)
    (g : ClassFunction B R) :
    externalProduct (f₁ + f₂) g =
      externalProduct f₁ g + externalProduct f₂ g := by
  ext x
  change (f₁ x.1 + f₂ x.1) * g x.2 =
    f₁ x.1 * g x.2 + f₂ x.1 * g x.2
  exact add_mul _ _ _

@[simp]
theorem externalProduct_add_right (f : ClassFunction A R)
    (g₁ g₂ : ClassFunction B R) :
    externalProduct f (g₁ + g₂) =
      externalProduct f g₁ + externalProduct f g₂ := by
  ext x
  change f x.1 * (g₁ x.2 + g₂ x.2) =
    f x.1 * g₁ x.2 + f x.1 * g₂ x.2
  exact mul_add _ _ _

/-- Pointwise coefficient maps commute with external products. -/
theorem mapRingHom_externalProduct
    {S : Type w} [CommRing S] (sigma : R →+* S)
    (f : ClassFunction A R) (g : ClassFunction B R) :
    mapRingHom sigma (externalProduct f g) =
      externalProduct (mapRingHom sigma f) (mapRingHom sigma g) := by
  ext x
  exact sigma.map_mul (f x.1) (g x.2)

end ClassFunction

namespace FDRep

variable {A B : Type u} {k : Type v} [Group A] [Group B] [Field k]

/-- The external tensor product of finite-dimensional representations. -/
def externalProduct (V : FDRep k A) (W : FDRep k B) : FDRep k (A × B) :=
  FDRep.of
    (Representation.tprod (V.ρ.comp (MonoidHom.fst A B))
      (W.ρ.comp (MonoidHom.snd A B)))

@[simp]
theorem externalProduct_character (V : FDRep k A) (W : FDRep k B)
    (a : A) (b : B) :
    (externalProduct V W).character (a, b) =
      V.character a * W.character b := by
  change (Representation.tprod (V.ρ.comp (MonoidHom.fst A B))
      (W.ρ.comp (MonoidHom.snd A B))).character (a, b) = _
  rw [Representation.char_tensor]
  rfl

variable {G : Type u} [Group G]

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
`FDRep.simple_iff_end_is_rank_one`. -/
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

/-- Twist the matrix coefficients of a representation by a coefficient-field
automorphism.  A basis is chosen only to construct the representation; its
character, and hence the irreducible character defined below, is independent
of that choice. -/
def coefficientTwist (sigma : k ≃+* k) (V : FDRep k G) : FDRep k G :=
  let b := Module.finBasis k V
  FDRep.of
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp
      (sigma.mapMatrix.toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp V.ρ)))

@[simp]
theorem coefficientTwist_character (sigma : k ≃+* k)
    (V : FDRep k G) (g : G) :
    (coefficientTwist sigma V).character g = sigma (V.character g) := by
  let b := Module.finBasis k V
  change LinearMap.trace k _
      (Matrix.toLinAlgEquiv'
        (sigma.mapMatrix (LinearMap.toMatrixAlgEquiv b (V.ρ g)))) =
    sigma (LinearMap.trace k V (V.ρ g))
  change LinearMap.trace k _
      (Matrix.toLin'
        (sigma.mapMatrix (LinearMap.toMatrixAlgEquiv b (V.ρ g)))) = _
  rw [Matrix.trace_toLin'_eq,
    LinearMap.trace_eq_matrix_trace k b,
    AddMonoidHom.map_trace]
  rfl

variable [Fintype G] [IsAlgClosed k] [CharZero k]

/-- Coefficient twisting preserves simplicity. -/
theorem coefficientTwist_simple (sigma : k ≃+* k)
    (V : FDRep k G) [CategoryTheory.Simple V] :
    CategoryTheory.Simple (coefficientTwist sigma V) := by
  rw [simple_iff_char_is_norm_one_general]
  have hV := (simple_iff_char_is_norm_one_general V).mp (by infer_instance)
  simp only [coefficientTwist_character, ← map_mul, ← map_sum, hV]
  exact map_natCast sigma (Nat.card G)

end FDRep

namespace IrreducibleCharacter

section CoefficientAutomorphisms

variable {G : Type u} {k : Type v}
  [Group G] [Fintype G] [Field k] [IsAlgClosed k] [CharZero k]

/-- Apply a coefficient-field automorphism to an irreducible character. -/
def mapRingEquiv (sigma : k ≃+* k) (chi : IrreducibleCharacter G k) :
    IrreducibleCharacter G k := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : CategoryTheory.Simple
      (FDRep.coefficientTwist sigma chi.representation) :=
    FDRep.coefficientTwist_simple sigma chi.representation
  exact ofFDRep (FDRep.coefficientTwist sigma chi.representation)

@[simp]
theorem mapRingEquiv_apply (sigma : k ≃+* k)
    (chi : IrreducibleCharacter G k) (g : G) :
    mapRingEquiv sigma chi g = sigma (chi g) := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : CategoryTheory.Simple
      (FDRep.coefficientTwist sigma chi.representation) :=
    FDRep.coefficientTwist_simple sigma chi.representation
  simp only [mapRingEquiv, ofFDRep_apply,
    FDRep.coefficientTwist_character, representation_character]

@[simp]
theorem mapRingEquiv_symm (sigma : k ≃+* k)
    (chi : IrreducibleCharacter G k) :
    mapRingEquiv sigma.symm (mapRingEquiv sigma chi) = chi := by
  ext g
  simp

/-- A coefficient-field automorphism permutes the irreducible characters. -/
def equivOfRingEquiv (sigma : k ≃+* k) :
    IrreducibleCharacter G k ≃ IrreducibleCharacter G k where
  toFun := mapRingEquiv sigma
  invFun := mapRingEquiv sigma.symm
  left_inv := mapRingEquiv_symm sigma
  right_inv := mapRingEquiv_symm sigma.symm

@[simp]
theorem equivOfRingEquiv_apply (sigma : k ≃+* k)
    (chi : IrreducibleCharacter G k) :
    equivOfRingEquiv sigma chi = mapRingEquiv sigma chi :=
  rfl

@[simp]
theorem mapRingEquiv_trivial (sigma : k ≃+* k) :
    mapRingEquiv sigma (trivial : IrreducibleCharacter G k) = trivial := by
  ext g
  simp [trivial_apply]

end CoefficientAutomorphisms

variable {A B k : Type u}
  [Group A] [Group B] [Fintype A] [Fintype B]
  [Field k] [IsAlgClosed k] [CharZero k]

local instance invertibleCardOfFintype
    {G : Type u} [Group G] [Fintype G] :
    Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem externalProductFDRep_simple
    (chi : IrreducibleCharacter A k)
    (psi : IrreducibleCharacter B k) :
    CategoryTheory.Simple
      (FDRep.externalProduct chi.representation psi.representation) := by
  rw [FDRep.simple_iff_char_is_norm_one]
  have hchi :=
    (FDRep.simple_iff_char_is_norm_one chi.representation).mp
      chi.representation_simple
  have hpsi :=
    (FDRep.simple_iff_char_is_norm_one psi.representation).mp
      psi.representation_simple
  rw [Fintype.sum_prod_type]
  calc
    (∑ a : A, ∑ b : B,
        (FDRep.externalProduct chi.representation psi.representation).character
            (a, b) *
          (FDRep.externalProduct chi.representation psi.representation).character
            (a, b)⁻¹) =
        (∑ a : A,
          chi.representation.character a *
            chi.representation.character a⁻¹) *
          (∑ b : B,
            psi.representation.character b *
              psi.representation.character b⁻¹) := by
      rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      simp only [FDRep.externalProduct_character, Prod.inv_mk]
      ring
    _ = (Nat.card A : k) * (Nat.card B : k) := by rw [hchi, hpsi]
    _ = (Nat.card (A × B) : k) := by
      rw [Nat.card_prod, Nat.cast_mul]

/-- The external product of two irreducible characters. -/
def externalProduct (chi : IrreducibleCharacter A k)
    (psi : IrreducibleCharacter B k) :
    IrreducibleCharacter (A × B) k := by
  letI : CategoryTheory.Simple
      (FDRep.externalProduct chi.representation psi.representation) :=
    externalProductFDRep_simple chi psi
  exact ofFDRep
    (FDRep.externalProduct chi.representation psi.representation)

@[simp]
theorem externalProduct_apply (chi : IrreducibleCharacter A k)
    (psi : IrreducibleCharacter B k) (a : A) (b : B) :
    externalProduct chi psi (a, b) = chi a * psi b := by
  letI : CategoryTheory.Simple
      (FDRep.externalProduct chi.representation psi.representation) :=
    externalProductFDRep_simple chi psi
  simp only [externalProduct, ofFDRep_apply,
    FDRep.externalProduct_character, representation_character]

theorem coe_externalProduct (chi : IrreducibleCharacter A k)
    (psi : IrreducibleCharacter B k) :
    (externalProduct chi psi : ClassFunction (A × B) k) =
      ClassFunction.externalProduct
        (chi : ClassFunction A k) (psi : ClassFunction B k) := by
  ext x
  exact externalProduct_apply chi psi x.1 x.2

/-- The character pairing factors across an external product. -/
theorem characterPairing_externalProduct
    (chi₁ chi₂ : IrreducibleCharacter A k)
    (psi₁ psi₂ : IrreducibleCharacter B k) :
    characterPairing
        (externalProduct chi₁ psi₁ : ClassFunction (A × B) k)
        (externalProduct chi₂ psi₂ : ClassFunction (A × B) k) =
      characterPairing (chi₁ : ClassFunction A k)
          (chi₂ : ClassFunction A k) *
        characterPairing (psi₁ : ClassFunction B k)
          (psi₂ : ClassFunction B k) := by
  rw [coe_externalProduct chi₁ psi₁, coe_externalProduct chi₂ psi₂]
  unfold characterPairing
  rw [Fintype.sum_prod_type]
  rw [Nat.card_prod, Nat.cast_mul]
  simp only [Prod.inv_mk]
  simp_rw [ClassFunction.externalProduct_apply]
  change
    ((Nat.card A : k) * (Nat.card B : k))⁻¹ *
          ∑ a : A, ∑ b : B,
            (chi₁ a * psi₁ b) * (chi₂ a⁻¹ * psi₂ b⁻¹) =
      ((Nat.card A : k)⁻¹ * ∑ a : A, chi₁ a * chi₂ a⁻¹) *
        ((Nat.card B : k)⁻¹ * ∑ b : B, psi₁ b * psi₂ b⁻¹)
  calc
    ((Nat.card A : k) * (Nat.card B : k))⁻¹ *
          ∑ a : A, ∑ b : B,
            (chi₁ a * psi₁ b) * (chi₂ a⁻¹ * psi₂ b⁻¹) =
        ((Nat.card A : k) * (Nat.card B : k))⁻¹ *
          ((∑ a : A, chi₁ a * chi₂ a⁻¹) *
            ∑ b : B, psi₁ b * psi₂ b⁻¹) := by
      congr 1
      rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro a _
      apply Finset.sum_congr rfl
      intro b _
      ring
    _ = ((Nat.card A : k)⁻¹ * ∑ a : A, chi₁ a * chi₂ a⁻¹) *
          ((Nat.card B : k)⁻¹ * ∑ b : B, psi₁ b * psi₂ b⁻¹) := by
      rw [mul_inv_rev]
      ring

/-- External products are injective in the pair of character indices. -/
theorem externalProduct_injective :
    Function.Injective
      (fun p : IrreducibleCharacter A k × IrreducibleCharacter B k ↦
        externalProduct p.1 p.2) := by
  rintro ⟨chi₁, psi₁⟩ ⟨chi₂, psi₂⟩ h
  have hpair :
      characterPairing
          (externalProduct chi₁ psi₁ : ClassFunction (A × B) k)
          (externalProduct chi₂ psi₂ : ClassFunction (A × B) k) = 1 := by
    have h' : externalProduct chi₁ psi₁ = externalProduct chi₂ psi₂ := h
    rw [h']
    exact characterPairing_self _
  rw [characterPairing_externalProduct] at hpair
  have hchi : chi₁ = chi₂ := by
    by_contra hne
    rw [characterPairing_eq_zero hne, zero_mul] at hpair
    exact zero_ne_one hpair
  have hpsi : psi₁ = psi₂ := by
    by_contra hne
    rw [characterPairing_eq_zero hne, hchi,
      characterPairing_self, one_mul] at hpair
    exact zero_ne_one hpair
  subst chi₂
  subst psi₂
  rfl

private def conjClassesProdEquiv :
    ConjClasses (A × B) ≃ ConjClasses A × ConjClasses B where
  toFun := Quotient.lift
    (fun x : A × B ↦ (ConjClasses.mk x.1, ConjClasses.mk x.2))
    (fun x y hxy ↦ by
      apply Prod.ext
      · apply ConjClasses.mk_eq_mk_iff_isConj.mpr
        exact (MonoidHom.fst A B).map_isConj hxy
      · apply ConjClasses.mk_eq_mk_iff_isConj.mpr
        exact (MonoidHom.snd A B).map_isConj hxy)
  invFun := fun p ↦ Quotient.liftOn₂ p.1 p.2
    (fun a b ↦ ConjClasses.mk (a, b))
    (fun a₁ b₁ a₂ b₂ ha hb ↦ by
      apply ConjClasses.mk_eq_mk_iff_isConj.mpr
      change IsConj a₁ a₂ at ha
      change IsConj b₁ b₂ at hb
      obtain ⟨x, hx⟩ := isConj_iff.mp ha
      obtain ⟨y, hy⟩ := isConj_iff.mp hb
      rw [isConj_iff]
      exact ⟨(x, y), by ext <;> simp [hx, hy]⟩)
  left_inv := by
    intro C
    induction C using Quotient.inductionOn with
    | _ x => rfl
  right_inv := by
    rintro ⟨CA, CB⟩
    induction CA using Quotient.inductionOn with
    | _ a =>
      induction CB using Quotient.inductionOn with
      | _ b => rfl

private theorem card_irreducibleCharacter_eq_conjClasses
    {G : Type u} [Group G] [Fintype G] :
    Fintype.card (IrreducibleCharacter G k) =
      Fintype.card (ConjClasses G) := by
  let basis : Module.Basis (IrreducibleCharacter G k) k (ClassFunction G k) :=
    Module.Basis.mk IrreducibleCharacter.linearIndependent (by
      rw [irreducibleCharacter_span_eq_top])
  calc
    Fintype.card (IrreducibleCharacter G k) =
        Module.finrank k (ClassFunction G k) :=
      (Module.finrank_eq_card_basis basis).symm
    _ = Module.finrank k (ConjClasses G → k) :=
      (ClassFunction.conjClassesLinearEquiv (G := G) (k := k)).finrank_eq
    _ = Fintype.card (ConjClasses G) :=
      Module.finrank_fintype_fun_eq_card k

set_option maxHeartbeats 800000 in
private theorem externalProduct_card_eq :
    Fintype.card
        (IrreducibleCharacter A k × IrreducibleCharacter B k) =
      Fintype.card (IrreducibleCharacter (A × B) k) := by
  have hAB :
      Fintype.card (IrreducibleCharacter (A × B) k) =
        Fintype.card (ConjClasses (A × B)) := by
    let basis : Module.Basis
        (IrreducibleCharacter (A × B) k) k
        (ClassFunction (A × B) k) :=
      Module.Basis.mk IrreducibleCharacter.linearIndependent (by
        rw [irreducibleCharacter_span_eq_top])
    calc
      Fintype.card (IrreducibleCharacter (A × B) k) =
          Module.finrank k (ClassFunction (A × B) k) :=
        (Module.finrank_eq_card_basis basis).symm
      _ = Module.finrank k (ConjClasses (A × B) → k) :=
        (ClassFunction.conjClassesLinearEquiv
          (G := A × B) (k := k)).finrank_eq
      _ = Fintype.card (ConjClasses (A × B)) :=
        Module.finrank_fintype_fun_eq_card k
  calc
    Fintype.card
          (IrreducibleCharacter A k × IrreducibleCharacter B k) =
        Fintype.card (IrreducibleCharacter A k) *
          Fintype.card (IrreducibleCharacter B k) :=
      Fintype.card_prod _ _
    _ = Fintype.card (ConjClasses A) * Fintype.card (ConjClasses B) :=
      congrArg₂ (· * ·)
        (card_irreducibleCharacter_eq_conjClasses (k := k) (G := A))
        (card_irreducibleCharacter_eq_conjClasses (k := k) (G := B))
    _ = Fintype.card (ConjClasses A × ConjClasses B) :=
      (Fintype.card_prod _ _).symm
    _ = Fintype.card (ConjClasses (A × B)) :=
      Fintype.card_congr (conjClassesProdEquiv (A := A) (B := B)).symm
    _ = Fintype.card (IrreducibleCharacter (A × B) k) :=
      hAB.symm

/-- Every irreducible character of a direct product is an external product. -/
theorem externalProduct_surjective :
    Function.Surjective
      (fun p : IrreducibleCharacter A k × IrreducibleCharacter B k ↦
        externalProduct p.1 p.2) :=
  ((Fintype.bijective_iff_injective_and_card _).2
    ⟨externalProduct_injective, externalProduct_card_eq⟩).2

/-- Irreducible characters of a direct product are exactly pairs of
irreducible characters of its factors. -/
def externalProductEquiv :
    IrreducibleCharacter A k × IrreducibleCharacter B k ≃
      IrreducibleCharacter (A × B) k :=
  Equiv.ofBijective
    (fun p ↦ externalProduct p.1 p.2)
    ⟨externalProduct_injective, externalProduct_surjective⟩

@[simp]
theorem externalProductEquiv_apply
    (p : IrreducibleCharacter A k × IrreducibleCharacter B k) :
    externalProductEquiv p = externalProduct p.1 p.2 :=
  rfl

@[simp]
theorem externalProduct_trivial :
    externalProduct
        (trivial : IrreducibleCharacter A k)
        (trivial : IrreducibleCharacter B k) =
      (trivial : IrreducibleCharacter (A × B) k) := by
  ext x
  rcases x with ⟨a, b⟩
  rw [externalProduct_apply, trivial_apply, trivial_apply, trivial_apply,
    mul_one]

/-- Coefficient-field automorphisms commute with the external-product
classification of irreducible characters. -/
theorem externalProduct_mapRingEquiv (sigma : k ≃+* k)
    (chi : IrreducibleCharacter A k)
    (psi : IrreducibleCharacter B k) :
    externalProduct (mapRingEquiv sigma chi) (mapRingEquiv sigma psi) =
      mapRingEquiv sigma (externalProduct chi psi) := by
  ext x
  rcases x with ⟨a, b⟩
  simp only [externalProduct_apply, mapRingEquiv_apply, map_mul]

/-- Equivalently, the direct-product equivalence intertwines the diagonal
coefficient-automorphism actions. -/
theorem externalProductEquiv_mapRingEquiv (sigma : k ≃+* k)
    (p : IrreducibleCharacter A k × IrreducibleCharacter B k) :
    externalProductEquiv
        (mapRingEquiv sigma p.1, mapRingEquiv sigma p.2) =
      mapRingEquiv sigma (externalProductEquiv p) := by
  simpa only [externalProductEquiv_apply] using
    externalProduct_mapRingEquiv sigma p.1 p.2

/-- Compatibility of the external-product formula with a coefficient-ring
endomorphism.  This statement deliberately lives at the class-function level:
it can be used with any later permutation of irreducible rows induced by a
coefficient automorphism. -/
theorem mapRingHom_coe_externalProduct (sigma : k →+* k)
    (chi : IrreducibleCharacter A k)
    (psi : IrreducibleCharacter B k) :
    ClassFunction.mapRingHom sigma
        (externalProduct chi psi : ClassFunction (A × B) k) =
      ClassFunction.externalProduct
        (ClassFunction.mapRingHom sigma (chi : ClassFunction A k))
        (ClassFunction.mapRingHom sigma (psi : ClassFunction B k)) := by
  rw [coe_externalProduct,
    ClassFunction.mapRingHom_externalProduct]

end IrreducibleCharacter

end

end Submission.OddOrder.PF
