import Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure

/-!
# Peterfalvi Section 9: coordinate characters in the non-Galois case

This module constructs the linear characters attached to the direct-product
decomposition supplied by the non-Galois alternative.  It also records the
coordinate actions and the two finite indexing sets used by the later
character-family arguments.

The implementation details live in a module-specific internal namespace.  The
three subgroup models at the end are the source-facing declarations of this
phase.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative

open Submission.OddOrder.MathlibSupport

universe u v

local instance (priority := 10) pTypeFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

namespace PTypeNonGaloisCoordinateCoreInternal

/-! ## Scalar characters and internal direct products -/

/-- The scalar representation underlying a pulled-back multiplicative
character.  This implementation detail is kept private. -/
private def pTypeScalarCharacterRepresentation
    {T Q : Type u} [Group T] [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) :
    Representation ℂ T ℂ where
  toFun t := lambda (q t) • LinearMap.id
  map_one' := by
    apply LinearMap.ext
    intro z
    simp
  map_mul' x y := by
    apply LinearMap.ext
    intro z
    simp only [map_mul, LinearMap.smul_apply, LinearMap.id_coe, id_eq,
      Module.End.mul_apply]
    ring

@[simp]
private theorem pTypeScalarCharacterRepresentation_character
    {T Q : Type u} [Group T] [Fintype T]
    [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) (t : T) :
    (FDRep.of (pTypeScalarCharacterRepresentation q lambda)).character t =
      lambda (q t) := by
  change LinearMap.trace ℂ ℂ
    (lambda (q t) • LinearMap.id) = lambda (q t)
  rw [map_smul, LinearMap.trace_id]
  simp

/-- The irreducible degree-one character obtained by pulling back a complex
multiplicative character. -/
noncomputable def pTypeIrreducibleCharacterOfMulChar
    {T Q : Type u} [Group T] [Fintype T]
    [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) :
    IrreducibleCharacter T ℂ := by
  let rho : Representation ℂ T ℂ :=
    pTypeScalarCharacterRepresentation q lambda
  letI : Representation.IsIrreducible rho :=
    { toNontrivial := by
        exact ⟨⊥, ⊤, fun h ↦ by
          have hone : (1 : ℂ) ∈ (⊥ : Subrepresentation rho) := by
            rw [h]
            trivial
          change (1 : ℂ) = 0 at hone
          exact one_ne_zero hone⟩
      eq_bot_or_eq_top := by
        intro V
        rcases eq_bot_or_eq_top V.toSubmodule with hV | hV
        · left
          apply Subrepresentation.toSubmodule_injective
          change V.toSubmodule = (⊥ : Submodule ℂ ℂ)
          exact hV
        · right
          apply Subrepresentation.toSubmodule_injective
          change V.toSubmodule = (⊤ : Submodule ℂ ℂ)
          exact hV }
  let V : FDRep ℂ T := FDRep.of rho
  letI : CategoryTheory.Simple V := simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep V

@[simp]
theorem pTypeIrreducibleCharacterOfMulChar_apply
    {T Q : Type u} [Group T] [Fintype T]
    [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) (t : T) :
    pTypeIrreducibleCharacterOfMulChar q lambda t = lambda (q t) := by
  change (FDRep.of
    (pTypeScalarCharacterRepresentation q lambda)).character t = _
  exact pTypeScalarCharacterRepresentation_character q lambda t

@[simp]
theorem pTypeIrreducibleCharacterOfMulChar_degree
    {T Q : Type u} [Group T] [Fintype T]
    [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) :
    pTypeIrreducibleDegree
      (pTypeIrreducibleCharacterOfMulChar q lambda) = 1 := by
  apply Nat.cast_injective (R := ℂ)
  unfold pTypeIrreducibleDegree
  rw [← IrreducibleCharacter.apply_one_eq_finrank]
  simp

/-- Multiplication of characters on a dependent finite product. -/
private def pTypeDependentPiMulChar
    {I : Type u} [Fintype I]
    {Q : I → Type u} [∀ i, Group (Q i)]
    [∀ i, IsMulCommutative (Q i)]
    (f : ∀ i, MulChar (Q i) ℂ) :
    MulChar ((i : I) → Q i) ℂ where
  toFun x := ∏ i, f i (x i)
  map_one' := by simp
  map_mul' x y := by
    simp only [Pi.mul_apply, map_mul]
    exact Finset.prod_mul_distrib
  map_nonunit' x hx := (hx (Group.isUnit x)).elim

@[simp]
private theorem pTypeDependentPiMulChar_apply
    {I : Type u} [Fintype I]
    {Q : I → Type u} [∀ i, Group (Q i)]
    [∀ i, IsMulCommutative (Q i)]
    (f : ∀ i, MulChar (Q i) ℂ) (x : (i : I) → Q i) :
    pTypeDependentPiMulChar f x = ∏ i, f i (x i) :=
  rfl

@[simp]
private theorem pTypeDependentPiMulChar_apply_mulSingle
    {I : Type u} [Fintype I]
    {Q : I → Type u} [∀ i, Group (Q i)]
    [∀ i, IsMulCommutative (Q i)]
    (f : ∀ i, MulChar (Q i) ℂ) (i : I) (x : Q i) :
    pTypeDependentPiMulChar f (Pi.mulSingle i x) = f i x := by
  classical
  rw [pTypeDependentPiMulChar_apply, Finset.prod_eq_single i]
  · rw [Pi.mulSingle_eq_same]
  · intro j _hj hji
    rw [Pi.mulSingle_eq_of_ne hji, map_one]
  · simp

/-- Composition for `MulChar`; current `MulChar.comp` forgets the
nonunit field and returns a plain monoid homomorphism. -/
private def pTypeMulCharComp
    {A B : Type u}
    [Group A] [IsMulCommutative A]
    [Group B] [IsMulCommutative B]
    (lambda : MulChar B ℂ) (f : A →* B) : MulChar A ℂ where
  toMonoidHom := lambda.toMonoidHom.comp f
  map_nonunit' x hx := (hx (Group.isUnit x)).elim

@[simp]
private theorem pTypeMulCharComp_apply
    {A B : Type u}
    [Group A] [IsMulCommutative A]
    [Group B] [IsMulCommutative B]
    (lambda : MulChar B ℂ) (f : A →* B) (x : A) :
    pTypeMulCharComp lambda f x = lambda (f x) :=
  rfl

/-- Pairwise commutativity in the shape expected by `noncommPiCoprod`. -/
private theorem pTypeInternalDirectProductCommute
    {I H : Type u} [Fintype I] [Group H]
    (A : I → Subgroup H) (hA : IsInternalDirectProductFamily A) :
    Pairwise fun i j : I ↦
      ∀ x y : H, x ∈ A i → y ∈ A j → Commute x y := by
  intro i j hij x y hx hy
  exact hA.2.2 i j hij x hx y hy

/-- The multiplicative equivalence associated to an internal direct product. -/
private noncomputable def pTypeInternalDirectProductEquiv
    {I H : Type u} [Fintype I] [Group H]
    (A : I → Subgroup H) (hA : IsInternalDirectProductFamily A) :
    ((i : I) → A i) ≃* H := by
  let phi : ((i : I) → A i) →* H :=
    Subgroup.noncommPiCoprod (pTypeInternalDirectProductCommute A hA)
  refine MulEquiv.ofBijective phi ⟨?_, ?_⟩
  · exact Subgroup.injective_noncommPiCoprod_of_iSupIndep hA.2.1
  · rw [← MonoidHom.range_eq_top, Subgroup.noncommPiCoprod_range]
    exact hA.1

/-- Multiply coordinate scalar characters through an internal direct-product
decomposition. -/
noncomputable def pTypeInternalDirectProductMulChar
    {I H : Type u} [Fintype I] [Group H] [IsMulCommutative H]
    (A : I → Subgroup H) (hA : IsInternalDirectProductFamily A)
    (f : ∀ i, MulChar (A i) ℂ) : MulChar H ℂ where
  toFun x := pTypeDependentPiMulChar f
    ((pTypeInternalDirectProductEquiv A hA).symm x)
  map_one' := by simp only [map_one]
  map_mul' x y := by simp only [map_mul]
  map_nonunit' x hx := (hx (Group.isUnit x)).elim

@[simp]
private theorem pTypeInternalDirectProductMulChar_apply
    {I H : Type u} [Fintype I] [Group H] [IsMulCommutative H]
    (A : I → Subgroup H) (hA : IsInternalDirectProductFamily A)
    (f : ∀ i, MulChar (A i) ℂ) (x : H) :
    pTypeInternalDirectProductMulChar A hA f x =
      pTypeDependentPiMulChar f
        ((pTypeInternalDirectProductEquiv A hA).symm x) :=
  rfl

private theorem pTypeInternalDirectProductMulChar_injective
    {I H : Type u} [Fintype I] [Group H] [IsMulCommutative H]
    (A : I → Subgroup H) (hA : IsInternalDirectProductFamily A) :
    Function.Injective (pTypeInternalDirectProductMulChar A hA) := by
  intro f g hfg
  funext i
  apply MulChar.ext'
  intro x
  let z : (j : I) → A j := Pi.mulSingle i x
  have hvalue := congrArg
    (fun mu : MulChar H ℂ ↦
      mu (pTypeInternalDirectProductEquiv A hA z)) hfg
  simp only [pTypeInternalDirectProductMulChar_apply,
    MulEquiv.symm_apply_apply] at hvalue
  simpa only [z, pTypeDependentPiMulChar_apply_mulSingle] using hvalue

@[simp]
private theorem pTypeInternalDirectProductMulChar_apply_coordinate
    {I H : Type u} [Fintype I] [Group H] [IsMulCommutative H]
    (A : I → Subgroup H) (hA : IsInternalDirectProductFamily A)
    (f : ∀ i, MulChar (A i) ℂ) (i : I) (x : A i) :
    pTypeInternalDirectProductMulChar A hA f (x : H) = f i x := by
  let z : (j : I) → A j := Pi.mulSingle i x
  have he : pTypeInternalDirectProductEquiv A hA z = (x : H) := by
    change Subgroup.noncommPiCoprod
      (pTypeInternalDirectProductCommute A hA) z = (x : H)
    exact Subgroup.noncommPiCoprod_mulSingle i x
  rw [← he]
  simp only [pTypeInternalDirectProductMulChar_apply,
    MulEquiv.symm_apply_apply, z,
    pTypeDependentPiMulChar_apply_mulSingle]

/-- Transport a scalar character from a selected constituent to its
`w`-conjugate. -/
noncomputable def pTypeActionConjugateMulChar
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (H₁ : Subgroup Hbar) (w : W₁) (lambda : MulChar H₁ ℂ) :
    MulChar (actionConjugate D.W₁_action H₁ w) ℂ :=
  pTypeMulCharComp lambda
    ((D.W₁_action w).subgroupMap H₁).symm.toMonoidHom

@[simp]
private theorem pTypeActionConjugateMulChar_apply
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (H₁ : Subgroup Hbar) (w : W₁) (lambda : MulChar H₁ ℂ)
    (x : actionConjugate D.W₁_action H₁ w) :
    pTypeActionConjugateMulChar D H₁ w lambda x =
      lambda (((D.W₁_action w).subgroupMap H₁).symm x) :=
  rfl

@[simp]
private theorem pTypeActionConjugateMulChar_one
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (H₁ : Subgroup Hbar) (w : W₁) :
    pTypeActionConjugateMulChar D H₁ w (1 : MulChar H₁ ℂ) = 1 := by
  apply MulChar.ext
  intro x
  let y : H₁ˣ := Units.map
    ((D.W₁_action w).subgroupMap H₁).symm.toMonoidHom x
  change (1 : MulChar H₁ ℂ) (y : H₁) =
    (1 : MulChar (actionConjugate D.W₁_action H₁ w) ℂ)
      (x : actionConjugate D.W₁_action H₁ w)
  rw [MulChar.one_apply_coe, MulChar.one_apply_coe]

private theorem pTypeActionConjugateMulChar_injective
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (H₁ : Subgroup Hbar) (w : W₁) :
    Function.Injective (pTypeActionConjugateMulChar D H₁ w) := by
  intro lambda mu hlm
  ext x
  have hvalue := congrArg
    (fun chi : MulChar (actionConjugate D.W₁_action H₁ w) ℂ ↦
      chi ((D.W₁_action w).subgroupMap H₁ x)) hlm
  simpa only [pTypeActionConjugateMulChar_apply,
    MulEquiv.symm_apply_apply] using hvalue

/-! ## Coordinate characters -/

/-- The linear irreducible character associated to a family of scalar
characters on the conjugate direct-product factors. -/
noncomputable def pTypeNonGaloisCoordinateCharacter
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : W₁ → MulChar data.H₁ ℂ) :
    IrreducibleCharacter Hbar ℂ :=
  let A := fun w : W₁ ↦ actionConjugate D.W₁_action data.H₁ w
  let mu := pTypeInternalDirectProductMulChar A data.conjugates_direct
    (fun w ↦ pTypeActionConjugateMulChar D data.H₁ w (lambda w))
  pTypeIrreducibleCharacterOfMulChar (MonoidHom.id Hbar) mu

/-- Evaluation on one direct-product coordinate. -/
@[simp]
theorem pTypeNonGaloisCoordinateCharacter_apply_coordinate
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : W₁ → MulChar data.H₁ ℂ) (w : W₁)
    (x : actionConjugate D.W₁_action data.H₁ w) :
    pTypeNonGaloisCoordinateCharacter D data lambda (x : Hbar) =
      pTypeActionConjugateMulChar D data.H₁ w (lambda w) x := by
  let A := fun v : W₁ ↦ actionConjugate D.W₁_action data.H₁ v
  simp only [pTypeNonGaloisCoordinateCharacter,
    pTypeIrreducibleCharacterOfMulChar_apply, MonoidHom.id_apply]
  exact pTypeInternalDirectProductMulChar_apply_coordinate
    A data.conjugates_direct _ w x

@[simp]
theorem pTypeNonGaloisCoordinateCharacter_degree
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : W₁ → MulChar data.H₁ ℂ) :
    pTypeIrreducibleDegree
      (pTypeNonGaloisCoordinateCharacter D data lambda) = 1 :=
  pTypeIrreducibleCharacterOfMulChar_degree _ _

/-- A nonprincipal coordinate is detected by the resulting character. -/
theorem pTypeNonGaloisCoordinateCharacter_not_le_translationKernel
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : W₁ → MulChar data.H₁ ℂ) (w : W₁)
    (hlambda : lambda w ≠ 1) :
    ¬ actionConjugate D.W₁_action data.H₁ w ≤
      ClassFunction.translationKernel
        (pTypeNonGaloisCoordinateCharacter D data lambda :
          ClassFunction Hbar ℂ) := by
  intro hkernel
  apply hlambda
  apply pTypeActionConjugateMulChar_injective D data.H₁ w
  apply MulChar.ext
  intro x
  let xA : actionConjugate D.W₁_action data.H₁ w := x
  change pTypeActionConjugateMulChar D data.H₁ w (lambda w) xA =
    pTypeActionConjugateMulChar D data.H₁ w 1 xA
  have hxkernel := hkernel xA.property
  rw [ClassFunction.mem_translationKernel_iff] at hxkernel
  have hxvalue := hxkernel (1 : Hbar)
  calc
    pTypeActionConjugateMulChar D data.H₁ w (lambda w)
          xA =
        pTypeNonGaloisCoordinateCharacter D data lambda
          (xA : Hbar) :=
      (pTypeNonGaloisCoordinateCharacter_apply_coordinate
        D data lambda w xA).symm
    _ = pTypeNonGaloisCoordinateCharacter D data lambda 1 := by
      simpa only [mul_one] using hxvalue
    _ = 1 := by
      simp only [pTypeNonGaloisCoordinateCharacter,
        pTypeIrreducibleCharacterOfMulChar_apply,
        map_one]
    _ = pTypeActionConjugateMulChar D data.H₁ w
        (1 : MulChar data.H₁ ℂ)
          xA := by
      rw [pTypeActionConjugateMulChar_one]
      exact (MulChar.one_apply_coe x).symm

/-! ### A representation-theoretic fixed-point detector -/

private theorem pTypeRepresentation_eq_of_character_eq_of_finrank_one
    {A : Type u} [Group A]
    {V : Type v} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (rho : Representation ℂ A V)
    (hdim : Module.finrank ℂ V = 1)
    {a b : A} (hchar : rho.character a = rho.character b) :
    rho a = rho b := by
  obtain ⟨ca, hca, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (rho a)
  obtain ⟨cb, hcb, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hdim (rho b)
  have hscalar : ca = cb := by
    change LinearMap.trace ℂ V (rho a) =
      LinearMap.trace ℂ V (rho b) at hchar
    rw [hca, hcb, map_smul, map_smul,
      LinearMap.trace_id, hdim] at hchar
    simpa using hchar
  rw [hca, hcb, hscalar]

private theorem pTypeMemPointwiseActionKernel_of_character_fixed
    {A B : Type u} [Group A] [Finite A]
    [Group B] [Finite B]
    (rho : A →* MulAut B) (L : Subgroup B)
    (hL : IsInvariantSubgroup rho L)
    (hLprime : (Nat.card L).Prime)
    (chi : IrreducibleCharacter B ℂ)
    (hdim : Module.finrank ℂ chi.representation = 1)
    (hnontrivial : ¬ L ≤ ClassFunction.translationKernel
      (chi : ClassFunction B ℂ))
    (a : A)
    (ha : ∀ b : B, chi (rho a b) = chi b) :
    a ∈ pointwiseActionKernel rho L := by
  let sigma : Representation ℂ L chi.representation :=
    chi.representation.ρ.comp L.subtype
  letI : Fact (Nat.card L).Prime := ⟨hLprime⟩
  have hker_ne_top : sigma.ker ≠ ⊤ := by
    intro htop
    apply hnontrivial
    intro x hx
    rw [ClassFunction.mem_translationKernel_iff]
    intro g
    let xL : L := ⟨x, hx⟩
    have hxker : xL ∈ sigma.ker := by
      rw [htop]
      trivial
    have hrho : chi.representation.ρ x = 1 := hxker
    rw [← chi.representation_character (x * g),
      ← chi.representation_character g]
    change LinearMap.trace ℂ chi.representation
        (chi.representation.ρ (x * g)) =
      LinearMap.trace ℂ chi.representation
        (chi.representation.ρ g)
    rw [map_mul, hrho, one_mul]
  have hker_bot : sigma.ker = ⊥ :=
    sigma.ker.eq_bot_or_eq_top_of_prime_card.resolve_right hker_ne_top
  have hsigma_injective : Function.Injective sigma :=
    sigma.ker_eq_bot_iff.mp hker_bot
  rw [mem_pointwiseActionKernel_iff]
  intro b hb
  let bL : L := ⟨b, hb⟩
  let abL : L := ⟨rho a b, hL.mem a hb⟩
  have hrho : chi.representation.ρ (abL : B) =
      chi.representation.ρ (bL : B) := by
    apply pTypeRepresentation_eq_of_character_eq_of_finrank_one
      chi.representation.ρ hdim
    exact (chi.representation_character (abL : B)).trans
      ((ha b).trans (chi.representation_character (bL : B)).symm)
  have hab : abL = bL := hsigma_injective hrho
  exact congrArg Subtype.val hab

/-- A coordinate family nonprincipal everywhere has stabilizer exactly `C`. -/
theorem pTypeNonGaloisCoordinateCharacter_fixed_iff_mem_C
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : W₁ → MulChar data.H₁ ℂ)
    (hlambda : ∀ w, lambda w ≠ 1) (x : U) :
    (∀ h : Hbar,
        pTypeNonGaloisCoordinateCharacter D data lambda
            (D.U_action x h) =
          pTypeNonGaloisCoordinateCharacter D data lambda h) ↔
      x ∈ D.C := by
  constructor
  · intro hfixed
    rw [D.C_eq_iInf_pointwiseActionKernel_of_iSup_eq_top
      data.H₁ data.conjugates_direct.1, Subgroup.mem_iInf]
    intro w
    let A : Subgroup Hbar :=
      actionConjugate D.W₁_action data.H₁ w
    have hcard : Nat.card A = D.p := by
      change Nat.card
        (data.H₁.map (D.W₁_action w).toMonoidHom) = D.p
      exact (Nat.card_congr
        ((D.W₁_action w).subgroupMap data.H₁).toEquiv).symm.trans
          data.card_H₁
    have hprime : (Nat.card A).Prime := by
      rw [hcard]
      exact D.p_prime
    apply pTypeMemPointwiseActionKernel_of_character_fixed
      D.U_action A
      (D.actionConjugate_U_invariant data.H₁_normalized w)
      hprime (pTypeNonGaloisCoordinateCharacter D data lambda)
      (pTypeNonGaloisCoordinateCharacter_degree D data lambda)
      (pTypeNonGaloisCoordinateCharacter_not_le_translationKernel
        D data lambda w (hlambda w)) x hfixed
  · intro hx h
    rw [(D.mem_C_iff x).mp hx h]

/-- Distinct coordinate families determine distinct irreducible characters. -/
theorem pTypeNonGaloisCoordinateCharacter_injective
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D) :
    Function.Injective (pTypeNonGaloisCoordinateCharacter D data) := by
  intro lambda mu hlm
  let A := fun w : W₁ ↦ actionConjugate D.W₁_action data.H₁ w
  have hproducts :
      pTypeInternalDirectProductMulChar A data.conjugates_direct
          (fun w ↦ pTypeActionConjugateMulChar D data.H₁ w (lambda w)) =
        pTypeInternalDirectProductMulChar A data.conjugates_direct
          (fun w ↦ pTypeActionConjugateMulChar D data.H₁ w (mu w)) := by
    ext x
    have hvalue := congrArg
      (fun chi : IrreducibleCharacter Hbar ℂ ↦ chi x) hlm
    simpa only [pTypeNonGaloisCoordinateCharacter,
      pTypeIrreducibleCharacterOfMulChar_apply,
      MonoidHom.id_apply] using hvalue
  have hcoordinates :=
    pTypeInternalDirectProductMulChar_injective
      A data.conjugates_direct hproducts
  funext w
  exact pTypeActionConjugateMulChar_injective D data.H₁ w
    (congrFun hcoordinates w)

/-! ## Coordinate actions -/

private noncomputable def pTypeMulCharComapMulEquiv
    {Q : Type u} [Group Q] [IsMulCommutative Q]
    (e : Q ≃* Q) (lambda : MulChar Q ℂ) : MulChar Q ℂ where
  toFun x := lambda (e x)
  map_one' := by simp only [map_one]
  map_mul' x y := by simp only [map_mul]
  map_nonunit' x hx := (hx (Group.isUnit x)).elim

@[simp]
private theorem pTypeMulCharComapMulEquiv_apply
    {Q : Type u} [Group Q] [IsMulCommutative Q]
    (e : Q ≃* Q) (lambda : MulChar Q ℂ) (x : Q) :
    pTypeMulCharComapMulEquiv e lambda x = lambda (e x) :=
  rfl

/-- The coordinate family obtained after translation by `u : U`. -/
noncomputable def pTypeNonGaloisUTranslateCoordinateFamily
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (u : U) (lambda : W₁ → MulChar data.H₁ ℂ) :
    W₁ → MulChar data.H₁ ℂ := fun w ↦
  pTypeMulCharComapMulEquiv
    (restrictMulAutHom data.H₁ D.U_action data.H₁_normalized
      (D.W₁_action_U w⁻¹ u)) (lambda w)

@[simp]
private theorem pTypeNonGaloisUTranslateCoordinateFamily_apply
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (u : U) (lambda : W₁ → MulChar data.H₁ ℂ)
    (w : W₁) (x : data.H₁) :
    pTypeNonGaloisUTranslateCoordinateFamily D data u lambda w x =
      lambda w
        (restrictMulAutHom data.H₁ D.U_action data.H₁_normalized
          (D.W₁_action_U w⁻¹ u) x) :=
  rfl

/-- Translation by `U` is computed independently in every coordinate. -/
theorem pTypeNonGaloisCoordinateCharacter_U_translate
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (u : U) (lambda : W₁ → MulChar data.H₁ ℂ) (h : Hbar) :
    pTypeNonGaloisCoordinateCharacter D data
        (pTypeNonGaloisUTranslateCoordinateFamily D data u lambda) h =
      pTypeNonGaloisCoordinateCharacter D data lambda
        (D.U_action u h) := by
  let A : W₁ → Subgroup Hbar := fun w ↦
    actionConjugate D.W₁_action data.H₁ w
  let mu : MulChar Hbar ℂ :=
    pTypeInternalDirectProductMulChar A data.conjugates_direct
      (fun w ↦ pTypeActionConjugateMulChar D data.H₁ w (lambda w))
  let nu : MulChar Hbar ℂ :=
    pTypeInternalDirectProductMulChar A data.conjugates_direct
      (fun w ↦ pTypeActionConjugateMulChar D data.H₁ w
        (pTypeNonGaloisUTranslateCoordinateFamily D data u lambda w))
  let E : Subgroup Hbar :=
    (mu.toMonoidHom.comp (D.U_action u).toMonoidHom).eqLocus
      nu.toMonoidHom
  have hAE (w : W₁) : A w ≤ E := by
    intro x hx
    let xv : A w := ⟨x, hx⟩
    let u' : U := D.W₁_action_U w⁻¹ u
    let a : data.H₁ :=
      ⟨(D.W₁_action w).symm x,
        (mem_actionConjugate_iff D.W₁_action data.H₁ w x).mp hx⟩
    have hu' : D.W₁_action_U w u' = u := by simp [u']
    have harg :
        (D.W₁_action w).symm (D.U_action u x) =
          D.U_action u' ((D.W₁_action w).symm x) := by
      have hcompat := D.action_compatibility u' w
        ((D.W₁_action w).symm x)
      have hcompat' := congrArg (D.W₁_action w).symm hcompat
      simpa [hu'] using hcompat'
    let uxv : A w := ⟨D.U_action u x, by
      rw [mem_actionConjugate_iff, harg]
      exact (restrictMulAutHom data.H₁ D.U_action
        data.H₁_normalized u' a).property⟩
    have hsub :
        ((D.W₁_action w).subgroupMap data.H₁).symm uxv =
          restrictMulAutHom data.H₁ D.U_action
            data.H₁_normalized u' a := by
      apply Subtype.ext
      exact harg
    change mu (D.U_action u x) = nu x
    calc
      mu (D.U_action u x) =
          pTypeActionConjugateMulChar D data.H₁ w (lambda w) uxv :=
        pTypeInternalDirectProductMulChar_apply_coordinate
          A data.conjugates_direct _ w uxv
      _ = lambda w
          (restrictMulAutHom data.H₁ D.U_action
            data.H₁_normalized u' a) := by
        simp only [pTypeActionConjugateMulChar_apply, hsub]
      _ = pTypeActionConjugateMulChar D data.H₁ w
          (pTypeNonGaloisUTranslateCoordinateFamily
            D data u lambda w) xv := by
        rfl
      _ = nu x :=
        (pTypeInternalDirectProductMulChar_apply_coordinate
          A data.conjugates_direct
            (fun v ↦ pTypeActionConjugateMulChar D data.H₁ v
              (pTypeNonGaloisUTranslateCoordinateFamily
                D data u lambda v)) w xv).symm
  have htop : (⊤ : Subgroup Hbar) ≤ E := by
    rw [← data.conjugates_direct.1]
    exact iSup_le hAE
  have hh : h ∈ E := htop (Subgroup.mem_top h)
  change mu (D.U_action u h) = nu h at hh
  simpa only [pTypeNonGaloisCoordinateCharacter,
    pTypeIrreducibleCharacterOfMulChar_apply, MonoidHom.id_apply,
    A, mu, nu] using hh.symm

/-- Translation by `U` preserves nonprincipality in each coordinate. -/
theorem pTypeNonGaloisUTranslateCoordinateFamily_ne_one
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (u : U) (lambda : W₁ → MulChar data.H₁ ℂ)
    (hlambda : ∀ w, lambda w ≠ 1) :
    ∀ w, pTypeNonGaloisUTranslateCoordinateFamily
      D data u lambda w ≠ 1 := by
  intro w htranslated
  apply hlambda w
  apply MulChar.ext
  intro x
  let alpha : MulEquiv data.H₁ data.H₁ :=
    restrictMulAutHom data.H₁ D.U_action data.H₁_normalized
      (D.W₁_action_U w⁻¹ u)
  let y : data.H₁ˣ := Units.map alpha.symm.toMonoidHom x
  have hy : alpha (y : data.H₁) = (x : data.H₁) :=
    alpha.apply_symm_apply (x : data.H₁)
  have hvalue := congrArg
    (fun chi : MulChar data.H₁ ℂ ↦ chi (y : data.H₁)) htranslated
  change lambda w (alpha (y : data.H₁)) =
    (1 : MulChar data.H₁ ℂ) (y : data.H₁) at hvalue
  rw [MulChar.one_apply_coe, hy] at hvalue
  rw [MulChar.one_apply_coe]
  exact hvalue

/-- Conjugation by `w : W₁` shifts a coordinate family by left
multiplication. -/
private noncomputable def pTypeNonGaloisW₁TranslateCoordinateFamily
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (lambda : W₁ → MulChar data.H₁ ℂ) :
    W₁ → MulChar data.H₁ ℂ :=
  fun v ↦ lambda (w * v)

private theorem pTypeNonGaloisCoordinateCharacter_W₁_translate
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (w : W₁) (lambda : W₁ → MulChar data.H₁ ℂ) (h : Hbar) :
    pTypeNonGaloisCoordinateCharacter D data lambda
        (D.W₁_action w h) =
      pTypeNonGaloisCoordinateCharacter D data
        (pTypeNonGaloisW₁TranslateCoordinateFamily data w lambda) h := by
  let A : W₁ → Subgroup Hbar := fun v ↦
    actionConjugate D.W₁_action data.H₁ v
  let f : ∀ v, MulChar (A v) ℂ := fun v ↦
    pTypeActionConjugateMulChar D data.H₁ v (lambda v)
  let lambda' := pTypeNonGaloisW₁TranslateCoordinateFamily data w lambda
  let f' : ∀ v, MulChar (A v) ℂ := fun v ↦
    pTypeActionConjugateMulChar D data.H₁ v (lambda' v)
  let mu : MulChar Hbar ℂ :=
    pTypeInternalDirectProductMulChar A data.conjugates_direct f
  let nu : MulChar Hbar ℂ :=
    pTypeInternalDirectProductMulChar A data.conjugates_direct f'
  let E : Subgroup Hbar :=
    (mu.toMonoidHom.comp (D.W₁_action w).toMonoidHom).eqLocus
      nu.toMonoidHom
  have hAE (v : W₁) : A v ≤ E := by
    intro x hx
    let xv : A v := ⟨x, hx⟩
    let xwv : A (w * v) := ⟨D.W₁_action w x, by
      rw [show A (w * v) =
        actionConjugate D.W₁_action (A v) w from
          actionConjugate_mul D.W₁_action data.H₁ w v]
      exact ⟨x, hx, rfl⟩⟩
    change mu (D.W₁_action w x) = nu x
    calc
      mu (D.W₁_action w x) =
          pTypeActionConjugateMulChar D data.H₁ (w * v)
            (lambda (w * v)) xwv :=
        pTypeInternalDirectProductMulChar_apply_coordinate
          A data.conjugates_direct f (w * v) xwv
      _ = pTypeActionConjugateMulChar D data.H₁ v
          (lambda' v) xv := by
        simp only [pTypeActionConjugateMulChar_apply, lambda',
          pTypeNonGaloisW₁TranslateCoordinateFamily]
        apply congrArg (lambda (w * v))
        apply Subtype.ext
        change (D.W₁_action (w * v)).symm (D.W₁_action w x) =
          (D.W₁_action v).symm x
        rw [map_mul]
        rw [← MulAut.inv_apply, ← MulAut.inv_apply, mul_inv_rev,
          MulAut.mul_apply, MulAut.inv_apply_self]
      _ = nu x :=
        (pTypeInternalDirectProductMulChar_apply_coordinate
          A data.conjugates_direct f' v xv).symm
  have htop : (⊤ : Subgroup Hbar) ≤ E := by
    rw [← data.conjugates_direct.1]
    exact iSup_le hAE
  have hh : h ∈ E := htop (Subgroup.mem_top h)
  change mu (D.W₁_action w h) = nu h at hh
  simpa only [pTypeNonGaloisCoordinateCharacter,
    pTypeIrreducibleCharacterOfMulChar_apply, MonoidHom.id_apply,
    A, f, f', mu, nu, lambda'] using hh

/-- A character supported on the selected coordinate cannot be carried to a
selected-coordinate character by a nonidentity outer action. -/
theorem pTypeNonGaloisSingleCoordinate_outer_support_rigidity
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda mu : MulChar data.H₁ ℂ) (hlambda : lambda ≠ 1)
    (u : U) (w : W₁)
    (hfixed : ∀ z : Hbar,
      pTypeNonGaloisCoordinateCharacter D data
          (fun v ↦ if v = 1 then lambda else 1)
          (D.U_action u (D.W₁_action w z)) =
        pTypeNonGaloisCoordinateCharacter D data
          (fun v ↦ if v = 1 then mu else 1) z) :
    w = 1 := by
  let family : W₁ → MulChar data.H₁ ℂ :=
    fun v ↦ if v = 1 then lambda else 1
  let target : W₁ → MulChar data.H₁ ℂ :=
    fun v ↦ if v = 1 then mu else 1
  let familyU := pTypeNonGaloisUTranslateCoordinateFamily
    D data u family
  have hcharacters : pTypeNonGaloisCoordinateCharacter D data
        (pTypeNonGaloisW₁TranslateCoordinateFamily data w familyU) =
      pTypeNonGaloisCoordinateCharacter D data target := by
    ext z
    calc
      pTypeNonGaloisCoordinateCharacter D data
          (pTypeNonGaloisW₁TranslateCoordinateFamily data w familyU) z =
        pTypeNonGaloisCoordinateCharacter D data familyU
          (D.W₁_action w z) :=
        (pTypeNonGaloisCoordinateCharacter_W₁_translate
          D data w familyU z).symm
      _ = pTypeNonGaloisCoordinateCharacter D data family
          (D.U_action u (D.W₁_action w z)) :=
        pTypeNonGaloisCoordinateCharacter_U_translate
          D data u family (D.W₁_action w z)
      _ = pTypeNonGaloisCoordinateCharacter D data target z := hfixed z
  have hfamilies :=
    pTypeNonGaloisCoordinateCharacter_injective D data hcharacters
  by_contra hw
  have hwinv : w⁻¹ ≠ 1 := inv_ne_one.mpr hw
  have hleft := congrFun hfamilies w⁻¹
  have hfamilyUOne : familyU 1 ≠ 1 := by
    intro hone
    apply hlambda
    apply MulChar.ext
    intro x
    let alpha : MulEquiv data.H₁ data.H₁ :=
      restrictMulAutHom data.H₁ D.U_action data.H₁_normalized
        (D.W₁_action_U (1 : W₁)⁻¹ u)
    let y : data.H₁ˣ := Units.map alpha.symm.toMonoidHom x
    have hy : alpha (y : data.H₁) = (x : data.H₁) :=
      alpha.apply_symm_apply (x : data.H₁)
    have hvalue := congrArg
      (fun chi : MulChar data.H₁ ℂ ↦ chi (y : data.H₁)) hone
    change pTypeNonGaloisUTranslateCoordinateFamily
      D data u family 1 (y : data.H₁) =
        (1 : MulChar data.H₁ ℂ) (y : data.H₁) at hvalue
    rw [pTypeNonGaloisUTranslateCoordinateFamily_apply] at hvalue
    simp only [family, if_pos] at hvalue
    rw [MulChar.one_apply_coe, hy] at hvalue
    rw [MulChar.one_apply_coe]
    exact hvalue
  have hleftNontrivial :
      pTypeNonGaloisW₁TranslateCoordinateFamily data w familyU w⁻¹ ≠
        1 := by
    simpa [pTypeNonGaloisW₁TranslateCoordinateFamily] using hfamilyUOne
  apply hleftNontrivial
  rw [hleft]
  simp [target, hwinv]

/-! ## Constant families -/

/-- The character obtained by using the same scalar character in every
coordinate. -/
noncomputable def pTypeNonGaloisConstantCoordinateCharacter
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) :
    IrreducibleCharacter Hbar ℂ :=
  pTypeNonGaloisCoordinateCharacter D data (fun _ ↦ lambda)

/-- A constant coordinate character is invariant under `W₁`. -/
theorem pTypeNonGaloisConstantCoordinateCharacter_W₁_fixed
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (lambda : MulChar data.H₁ ℂ) (w : W₁) (h : Hbar) :
    pTypeNonGaloisConstantCoordinateCharacter D data lambda
        (D.W₁_action w h) =
      pTypeNonGaloisConstantCoordinateCharacter D data lambda h := by
  let A : W₁ → Subgroup Hbar := fun v ↦
    actionConjugate D.W₁_action data.H₁ v
  let f : ∀ v, MulChar (A v) ℂ := fun v ↦
    pTypeActionConjugateMulChar D data.H₁ v lambda
  let mu : MulChar Hbar ℂ :=
    pTypeInternalDirectProductMulChar A data.conjugates_direct f
  let E : Subgroup Hbar :=
    (mu.toMonoidHom.comp (D.W₁_action w).toMonoidHom).eqLocus
      mu.toMonoidHom
  have hAE (v : W₁) : A v ≤ E := by
    intro x hx
    let xv : A v := ⟨x, hx⟩
    let xwv : A (w * v) := ⟨D.W₁_action w x, by
      rw [show A (w * v) =
        actionConjugate D.W₁_action (A v) w from
          actionConjugate_mul D.W₁_action data.H₁ w v]
      exact ⟨x, hx, rfl⟩⟩
    change mu (D.W₁_action w x) = mu x
    change pTypeInternalDirectProductMulChar
        A data.conjugates_direct f (xwv : Hbar) =
      pTypeInternalDirectProductMulChar
        A data.conjugates_direct f (xv : Hbar)
    rw [pTypeInternalDirectProductMulChar_apply_coordinate,
      pTypeInternalDirectProductMulChar_apply_coordinate]
    simp only [f, pTypeActionConjugateMulChar]
    apply congrArg lambda
    apply Subtype.ext
    change (D.W₁_action (w * v)).symm (D.W₁_action w x) =
      (D.W₁_action v).symm x
    rw [map_mul]
    rw [← MulAut.inv_apply, ← MulAut.inv_apply, mul_inv_rev,
      MulAut.mul_apply, MulAut.inv_apply_self]
  have htop : (⊤ : Subgroup Hbar) ≤ E := by
    rw [← data.conjugates_direct.1]
    exact iSup_le hAE
  have hh : h ∈ E := htop (Subgroup.mem_top h)
  change mu (D.W₁_action w h) = mu h at hh
  simpa only [pTypeNonGaloisConstantCoordinateCharacter,
    pTypeNonGaloisCoordinateCharacter,
    pTypeIrreducibleCharacterOfMulChar_apply,
    MonoidHom.id_apply, A, f, mu] using hh

/-- Two nonprincipal constant-coordinate characters in the same `U`-orbit
are equal. -/
theorem pTypeNonGaloisConstantCoordinateCharacter_eq_of_U_translate
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (hD : PTypeFactorActionHypotheses D)
    (data : TypePGaloisNonConclusion D)
    (lambda mu : MulChar data.H₁ ℂ)
    (hlambda : lambda ≠ 1) (u : U)
    (horbit : ∀ h : Hbar,
      pTypeNonGaloisConstantCoordinateCharacter D data lambda
          (D.U_action u h) =
        pTypeNonGaloisConstantCoordinateCharacter D data mu h) :
    lambda = mu := by
  let theta := pTypeNonGaloisConstantCoordinateCharacter D data lambda
  let eta := pTypeNonGaloisConstantCoordinateCharacter D data mu
  have hW₁_nontrivial : 1 < Nat.card W₁ := by
    rw [D.card_W₁]
    exact D.q_prime.one_lt
  letI : Nontrivial W₁ :=
    Finite.one_lt_card_iff_nontrivial.mp hW₁_nontrivial
  obtain ⟨w, hw⟩ := exists_ne (1 : W₁)
  let delta : U := D.W₁_action_U w⁻¹ u * u⁻¹
  have hdeltaFixed : ∀ z : Hbar,
      theta (D.U_action delta z) = theta z := by
    intro z
    let h : Hbar := D.U_action u⁻¹ z
    have huz : D.U_action u h = z := by
      simpa only [h, map_inv] using
        MulAut.apply_inv_self Hbar (D.U_action u) z
    have hdeltaAction : D.U_action delta z =
        D.U_action (D.W₁_action_U w⁻¹ u) h := by
      calc
        D.U_action delta z =
            D.U_action delta (D.U_action u h) := by rw [huz]
        _ = D.U_action (delta * u) h := by
          exact (congrArg (fun a : MulAut Hbar ↦ a h)
            (map_mul D.U_action delta u)).symm
        _ = D.U_action (D.W₁_action_U w⁻¹ u) h := by
          rw [show delta * u = D.W₁_action_U w⁻¹ u by
            dsimp only [delta]
            group]
    rw [hdeltaAction]
    calc
      theta (D.U_action (D.W₁_action_U w⁻¹ u) h) =
          theta (D.W₁_action w
            (D.U_action (D.W₁_action_U w⁻¹ u) h)) :=
        (pTypeNonGaloisConstantCoordinateCharacter_W₁_fixed
          D data lambda w _).symm
      _ = theta (D.U_action u (D.W₁_action w h)) := by
        rw [← D.action_compatibility
          (D.W₁_action_U w⁻¹ u) w h]
        simp
      _ = eta (D.W₁_action w h) := horbit _
      _ = eta h :=
        pTypeNonGaloisConstantCoordinateCharacter_W₁_fixed
          D data mu w h
      _ = theta (D.U_action u h) := (horbit h).symm
      _ = theta z := by rw [huz]
  have hdeltaC : delta ∈ D.C :=
    (pTypeNonGaloisCoordinateCharacter_fixed_iff_mem_C
      D data (fun _ ↦ lambda) (fun _ ↦ hlambda) delta).mp hdeltaFixed
  have huC : u ∈ D.C :=
    hD.fixed_coset_trivial w⁻¹ (inv_ne_one.mpr hw) u hdeltaC
  have huAction : ∀ h : Hbar, D.U_action u h = h :=
    (D.mem_C_iff u).mp huC
  have htheta :
      pTypeNonGaloisConstantCoordinateCharacter D data lambda =
        pTypeNonGaloisConstantCoordinateCharacter D data mu := by
    ext h
    rw [← horbit h, huAction h]
  have hfamilies :=
    pTypeNonGaloisCoordinateCharacter_injective D data htheta
  exact congrFun hfamilies (1 : W₁)

/-! ## Finite coordinate-family indices -/

/-- The nonprincipal complex multiplicative characters of a finite abelian
group. -/
noncomputable def pTypeNontrivialMulChars
    (Q : Type u) [Group Q] [Finite Q] [IsMulCommutative Q] :
    Finset (MulChar Q ℂ) := by
  exact Finset.univ.erase 1

@[simp]
theorem mem_pTypeNontrivialMulChars
    {Q : Type u} [Group Q] [Finite Q] [IsMulCommutative Q]
    (lambda : MulChar Q ℂ) :
    lambda ∈ pTypeNontrivialMulChars Q ↔ lambda ≠ 1 := by
  simp [pTypeNontrivialMulChars]

private theorem pTypeNontrivialMulChars_card
    (Q : Type u) [Group Q] [Finite Q] [IsMulCommutative Q] :
    (pTypeNontrivialMulChars Q).card = Nat.card Q - 1 := by
  rw [pTypeNontrivialMulChars,
    Finset.card_erase_of_mem (Finset.mem_univ (1 : MulChar Q ℂ)),
    Finset.card_univ, ← Nat.card_eq_fintype_card]
  apply congrArg (fun n : ℕ ↦ n - 1)
  calc
    Nat.card (MulChar Q ℂ) = Nat.card Qˣ :=
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity Q ℂ
    _ = Nat.card Q := Nat.card_congr toUnits.toEquiv.symm

@[simp]
theorem natCard_pTypeNontrivialMulChars
    (Q : Type u) [Group Q] [Finite Q] [IsMulCommutative Q] :
    Nat.card ↑(pTypeNontrivialMulChars Q) = Nat.card Q - 1 := by
  simpa only [Nat.card_eq_fintype_card, Fintype.card_coe] using
    pTypeNontrivialMulChars_card Q

/-- At every conjugate factor, choose one nonprincipal scalar character. -/
abbrev PTypeNonGaloisCoordinateFamilyIndex
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    {D : PTypeFactorActionData Hbar U W₁}
    (data : TypePGaloisNonConclusion D) :=
  (w : W₁) → ↑(pTypeNontrivialMulChars data.H₁)

/-- The all-nonprincipal coordinate index has cardinality `(p - 1)^q`. -/
theorem pTypeNonGaloisCoordinateFamilyIndex_card
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    {D : PTypeFactorActionData Hbar U W₁}
    (hD : PTypeFactorActionHypotheses D)
    (data : TypePGaloisNonConclusion D) :
    letI : IsMulCommutative Hbar := hD.elementary.commutative
    Nat.card (PTypeNonGaloisCoordinateFamilyIndex data) =
      (D.p - 1) ^ D.q := by
  letI : IsMulCommutative Hbar := hD.elementary.commutative
  letI : IsMulCommutative data.H₁ := inferInstance
  calc
    Nat.card (PTypeNonGaloisCoordinateFamilyIndex data) =
        ∏ _w : W₁, Nat.card ↑(pTypeNontrivialMulChars data.H₁) :=
      Nat.card_pi
    _ = ∏ _w : W₁, (D.p - 1) := by
      simp only [natCard_pTypeNontrivialMulChars, data.card_H₁]
    _ = (D.p - 1) ^ D.q := by
      rw [Finset.prod_const, Finset.card_univ,
        ← Nat.card_eq_fintype_card, D.card_W₁]

end PTypeNonGaloisCoordinateCoreInternal

/-! ## Canonical subgroup models used by the next phase -/

/-- Source `HC`, formed inside the derived subgroup `HU`. -/
def pTypeHCInDerived
    {Gamma : Type u} [Group Gamma]
    (L K H U W₁ : Subgroup Gamma)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) :
    Subgroup (pTypeHUInMaximal L K) :=
  pTypeHInDerived L K H ⊔
    ((D.C.map U.subtype).subgroupOf L).subgroupOf
      (pTypeHUInMaximal L K)

/-- Source `H₀U'`, formed inside the derived subgroup `HU`. -/
def pTypeH0DerivedComplementInDerived
    {Gamma : Type u} [Group Gamma]
    (L K H₀ U : Subgroup Gamma) :
    Subgroup (pTypeHUInMaximal L K) :=
  pTypeH0InDerived L K H₀ ⊔
    (pTypeDerivedComplementInMaximal
      (U.subgroupOf L).subtype).subgroupOf (pTypeHUInMaximal L K)

/-- Source `HC`, formed in the maximal subgroup type. -/
def pTypeHCInMaximal
    {Gamma : Type u} [Group Gamma]
    (L H U W₁ : Subgroup Gamma)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) :
    Subgroup L :=
  H.subgroupOf L ⊔
    (D.C.map U.subtype).subgroupOf L

end

end Submission.OddOrder.PF
