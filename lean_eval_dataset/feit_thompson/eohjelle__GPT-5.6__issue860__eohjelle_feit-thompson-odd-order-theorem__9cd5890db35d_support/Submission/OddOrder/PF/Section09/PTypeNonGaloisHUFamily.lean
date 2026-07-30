import Submission.OddOrder.PF.Section09.PTypeNonGaloisHCProjection

/-!
# Peterfalvi Section 9: non-Galois character families on `HU`

Starting from the coordinate characters on the normal subgroup `HC`, this
module constructs the family indexed by coordinatewise nonprincipal scalar
characters, identifies its inertia in `HU`, and packages the irreducible
inductions to `HU`.  It also records the constant-coordinate subfamily and the
kernel-layer facts used by the next phases.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative MonoidAlgebra

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF.internal
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open PTypeNonGaloisCoordinateCoreInternal
open PTypeNonGaloisHCProjectionInternal
open CategoryTheory

universe u v

namespace PTypeNonGaloisHUFamilyInternal

/-! ## Character-kernel transport -/

private theorem translationKernel_irreducibleCharacter_general
    {G : Type u} {k : Type v} [Group G]
    [Field k] [IsAlgClosed k]
    (chi : IrreducibleCharacter G k) :
    ClassFunction.translationKernel (chi : ClassFunction G k) =
      chi.representation.ρ.ker := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker]
    let rho : Representation k G chi.representation :=
      chi.representation.ρ
    letI : CategoryTheory.Simple chi.representation :=
      chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      representation_isIrreducible_of_simple_fdRep chi.representation
    have htraceGroup (g : G) :
        LinearMap.trace k chi.representation
            ((rho a - 1) * rho g) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← rho.map_mul]
      change rho.character (a * g) - rho.character g = 0
      dsimp only [rho]
      change chi.representation.character (a * g) -
        chi.representation.character g = 0
      rw [chi.representation_character, chi.representation_character]
      exact sub_eq_zero.mpr (ha g)
    have htraceAlgebra (z : k[G]) :
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

private theorem exists_hom_ne_zero_of_isConstituent_general
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    ∃ f : chi.representation ⟶ V, f ≠ 0 := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := G)).ne')
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hpair :
      characterPairing (ClassFunction.ofRepresentation V.ρ)
          (chi : ClassFunction G k) =
        (Module.finrank k (chi.representation ⟶ V) : k) := by
    have hhom :=
      FDRep.scalar_product_char_eq_finrank_equivariant
        chi.representation V
    have hcharV (g : G) :
        V.character g = _root_.Representation.character V.ρ g := rfl
    simpa only [characterPairing,
      ClassFunction.ofRepresentation_apply,
      IrreducibleCharacter.representation_character, invOf_eq_inv,
      smul_eq_mul, Fintype.card_eq_nat_card, hcharV] using hhom
  have hcast : (Module.finrank k (chi.representation ⟶ V) : k) ≠ 0 := by
    rw [← hpair]
    exact hchi
  have hfin : Module.finrank k (chi.representation ⟶ V) ≠ 0 := by
    intro hzero
    apply hcast
    simp [hzero]
  exact Module.finrank_pos_iff_exists_ne_zero.mp
    (Nat.pos_of_ne_zero hfin)

private theorem fdRep_kernel_le_constituent_kernel_general
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (V : FDRep k G) (chi : IrreducibleCharacter G k)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    V.ρ.ker ≤ chi.representation.ρ.ker := by
  obtain ⟨f, hf⟩ :=
    exists_hom_ne_zero_of_isConstituent_general V chi hchi
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

private theorem subgroupOf_le_constituent_kernel_of_induce_general
    {G : Type u} {k : Type v} [Group G] [Field k]
    [Fintype G] [CharZero k]
    (H A : Subgroup G) (hAH : A ≤ H)
    (chi : IrreducibleCharacter G k)
    (psi : IrreducibleCharacter H k)
    (hchi : chi.IsConstituent
      (ClassFunction.induce H (psi : ClassFunction H k)))
    (hAchi : A ≤ chi.representation.ρ.ker) :
    A.subgroupOf H ≤ psi.representation.ρ.ker := by
  have hpsi : psi.IsConstituent
      (ClassFunction.restrict H (chi : ClassFunction G k)) :=
    (psi.isConstituent_restrict_iff_induce H chi).2 hchi
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
    fdRep_kernel_le_constituent_kernel_general R psi hpsiR
  intro h hh
  apply hkerRpsi
  rw [MonoidHom.mem_ker]
  change chi.representation.ρ (h : G) = 1
  exact MonoidHom.mem_ker.mp (hAchi hh)

/-! ## The canonical complement decomposition of `HU` -/

private theorem pTypeHInHU_isComplement
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (((Fitting_core M).subgroupOf M).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M))).IsComplement'
      ((U.subgroupOf M).subgroupOf
        (pTypeHUInMaximal M (derivedWithin M))) := by
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  let eHU : HU ≃* derivedWithin M :=
    Subgroup.subgroupOfEquivOfLe hDerM
  have hmapped := pTypeIsComplement_map_mulEquiv
    ctx.typeP.2.1.2.2.2.2.2.2 eHU.symm
  have hmapH :
      ((Fitting_core M).subgroupOf (derivedWithin M)).map
          eHU.symm.toMonoidHom = H := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨eHU x, hx, ?_⟩
      exact eHU.symm_apply_apply x
  have hmapU :
      (U.subgroupOf (derivedWithin M)).map
          eHU.symm.toMonoidHom = UHU := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      refine ⟨eHU x, hx, ?_⟩
      exact eHU.symm_apply_apply x
  rw [hmapH, hmapU] at hmapped
  exact hmapped

/-! ## The all-nonprincipal source family on `HC` -/

/-- The coordinate character associated to an all-nonprincipal family. -/
private noncomputable def fullCoordinateCharacter
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D)
    (f : PTypeNonGaloisCoordinateFamilyIndex data) :
    IrreducibleCharacter Hbar ℂ :=
  pTypeNonGaloisCoordinateCharacter D data
    (fun w ↦ (f w : MulChar data.H₁ ℂ))

private theorem fullCoordinateCharacter_injective
    {Hbar U W₁ : Type u}
    [Group Hbar] [Group U] [Group W₁]
    [Finite Hbar] [Finite U] [Finite W₁]
    [IsMulCommutative Hbar]
    (D : PTypeFactorActionData Hbar U W₁)
    (data : TypePGaloisNonConclusion D) :
    Function.Injective (fullCoordinateCharacter D data) := by
  intro f g hfg
  have hfamilies :=
    pTypeNonGaloisCoordinateCharacter_injective D data hfg
  funext w
  exact Subtype.ext (congrFun hfamilies w)

/-- Bundle an all-nonprincipal coordinate choice as a character of the
nested copy `HC ≤ HU`. -/
noncomputable def pTypeNonGaloisFullHCCharacterInHUFromIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    PTypeNonGaloisCoordinateFamilyIndex data →
      IrreducibleCharacter
        ((pTypeHCInMaximal M (Fitting_core M) U W₁ D).subgroupOf
          (pTypeHUInMaximal M (derivedWithin M))) ℂ := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro f
  exact pTypeNonGaloisHCCoordinateCharacterInHU
    ctx facts not_Galois (fun w ↦ (f w : MulChar data.H₁ ℂ))

/-- Transport to the nested copy of `HC` does not forget the coordinate
family. -/
theorem pTypeNonGaloisFullHCCharacterInHUFromIndex_injective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    Function.Injective
      (pTypeNonGaloisFullHCCharacterInHUFromIndex
        ctx facts not_Galois) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  let eHC : HCN ≃* HC := Subgroup.subgroupOfEquivOfLe
    (pTypeNonGaloisHCInMaximal_le_HU ctx facts)
  dsimp only
  intro f g hfg
  apply fullCoordinateCharacter_injective D data
  apply Subtype.ext
  ext z
  obtain ⟨x, hx⟩ := pTypeHCProjection_surjective ctx facts z
  let y : HCN := eHC.symm x
  have hvalue := congrArg
    (fun chi : IrreducibleCharacter HCN ℂ ↦ chi y) hfg
  calc
    fullCoordinateCharacter D data f z =
        pTypeNonGaloisHCCoordinateCharacter ctx facts not_Galois
          (fun w ↦ (f w : MulChar data.H₁ ℂ)) x := by
      change pTypeNonGaloisCoordinateCharacter D data
          (fun w ↦ (f w : MulChar data.H₁ ℂ)) z = _
      rw [pTypeNonGaloisHCCoordinateCharacter_apply, hx]
    _ = pTypeNonGaloisFullHCCharacterInHUFromIndex
          ctx facts not_Galois f y := by
      change _ = pTypeNonGaloisHCCoordinateCharacterInHU
        ctx facts not_Galois
          (fun w ↦ (f w : MulChar data.H₁ ℂ)) y
      rw [pTypeNonGaloisHCCoordinateCharacterInHU_apply,
        show eHC y = x from eHC.apply_symm_apply x]
    _ = pTypeNonGaloisFullHCCharacterInHUFromIndex
          ctx facts not_Galois g y := hvalue
    _ = pTypeNonGaloisHCCoordinateCharacter ctx facts not_Galois
          (fun w ↦ (g w : MulChar data.H₁ ℂ)) x := by
      change pTypeNonGaloisHCCoordinateCharacterInHU
          ctx facts not_Galois
            (fun w ↦ (g w : MulChar data.H₁ ℂ)) y = _
      rw [pTypeNonGaloisHCCoordinateCharacterInHU_apply,
        show eHC y = x from eHC.apply_symm_apply x]
    _ = fullCoordinateCharacter D data g z := by
      change _ = pTypeNonGaloisCoordinateCharacter D data
        (fun w ↦ (g w : MulChar data.H₁ ℂ)) z
      rw [pTypeNonGaloisHCCoordinateCharacter_apply, hx]

/-- The finite source family of all coordinatewise nonprincipal characters. -/
noncomputable def pTypeNonGaloisFullHCCharacterInHUFamily
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Finset (IrreducibleCharacter
      ((pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts)).subgroupOf
          (pTypeHUInMaximal M (derivedWithin M))) ℂ) := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  exact Finset.univ.image
    (pTypeNonGaloisFullHCCharacterInHUFromIndex
      ctx facts not_Galois)

/-- The source family has cardinality `(p - 1)^q`. -/
theorem pTypeNonGaloisFullHCCharacterInHUFamily_card
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    (pTypeNonGaloisFullHCCharacterInHUFamily
      ctx facts not_Galois).card =
        ((Ptype_factor_action ctx facts).p - 1) ^
          (Ptype_factor_action ctx facts).q := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  rw [pTypeNonGaloisFullHCCharacterInHUFamily,
    Finset.card_image_of_injective _
      (pTypeNonGaloisFullHCCharacterInHUFromIndex_injective
        ctx facts not_Galois),
    Finset.card_univ, ← Nat.card_eq_fintype_card]
  exact pTypeNonGaloisCoordinateFamilyIndex_card hD data

private theorem fullHCCharacter_normalConjugate_exists
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let HCN := HC.subgroupOf HU
    ∀ (f : PTypeNonGaloisCoordinateFamilyIndex data) (x : HU),
      ∃ g : PTypeNonGaloisCoordinateFamilyIndex data,
        ClassFunction.normalConjugate HCN x
            (pTypeNonGaloisFullHCCharacterInHUFromIndex
              ctx facts not_Galois f : ClassFunction HCN ℂ) =
          (pTypeNonGaloisFullHCCharacterInHUFromIndex
            ctx facts not_Galois g : ClassFunction HCN ℂ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  have hcomp : H.IsComplement' UHU := pTypeHInHU_isComplement ctx
  have hHHCN : H ≤ HCN := by
    intro y hy
    exact (le_sup_left :
      (Fitting_core M).subgroupOf M ≤
        (Fitting_core M).subgroupOf M ⊔
          (D.C.map U.subtype).subgroupOf M) hy
  dsimp only
  intro f x
  obtain ⟨⟨n, v⟩, hnv⟩ := hcomp.2 x
  change (n : HU) * (v : HU) = x at hnv
  let nHC : HCN := ⟨(n : HU), hHHCN n.property⟩
  let u : U := ⟨((v : HU) : M), v.property⟩
  let lambda : W₁ → MulChar data.H₁ ℂ :=
    fun w ↦ (f w : MulChar data.H₁ ℂ)
  have hlambda : ∀ w, lambda w ≠ 1 := fun w ↦ by
    change (f w : MulChar data.H₁ ℂ) ≠ 1
    exact (mem_pTypeNontrivialMulChars
      (Q := data.H₁) (f w : MulChar data.H₁ ℂ)).mp (f w).property
  let g : PTypeNonGaloisCoordinateFamilyIndex data := fun w ↦
    ⟨pTypeNonGaloisUTranslateCoordinateFamily
        D data u⁻¹ lambda w,
      (mem_pTypeNontrivialMulChars
        (Q := data.H₁)
        (pTypeNonGaloisUTranslateCoordinateFamily
          D data u⁻¹ lambda w)).mpr
        (pTypeNonGaloisUTranslateCoordinateFamily_ne_one
          D data u⁻¹ lambda hlambda w)⟩
  refine ⟨g, ?_⟩
  calc
    ClassFunction.normalConjugate HCN x
        (pTypeNonGaloisFullHCCharacterInHUFromIndex
          ctx facts not_Galois f : ClassFunction HCN ℂ) =
      ClassFunction.normalConjugate HCN (n : HU)
        (ClassFunction.normalConjugate HCN (v : HU)
          (pTypeNonGaloisFullHCCharacterInHUFromIndex
            ctx facts not_Galois f : ClassFunction HCN ℂ)) := by
      rw [← ClassFunction.normalConjugate_mul, hnv]
    _ = ClassFunction.normalConjugate HCN (v : HU)
        (pTypeNonGaloisFullHCCharacterInHUFromIndex
          ctx facts not_Galois f : ClassFunction HCN ℂ) :=
      ClassFunction.normalConjugate_coe HCN _ nHC
    _ = (pTypeNonGaloisFullHCCharacterInHUFromIndex
          ctx facts not_Galois g : ClassFunction HCN ℂ) := by
      exact pTypeNonGaloisHCCoordinateCharacterInHU_normalConjugate_U
        ctx facts not_Galois lambda v

/-- The all-nonprincipal source family is stable under conjugation by `HU`. -/
theorem pTypeNonGaloisFullHCCharacterInHUFamily_stable
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)
    let HCN := HC.subgroupOf HU
    ∀ chi ∈ pTypeNonGaloisFullHCCharacterInHUFamily
        ctx facts not_Galois,
      ∀ x : HU, chi.normalConjugate HCN x ∈
        pTypeNonGaloisFullHCCharacterInHUFamily
          ctx facts not_Galois := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  dsimp only
  intro chi hchi x
  rw [pTypeNonGaloisFullHCCharacterInHUFamily] at hchi ⊢
  obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hchi
  obtain ⟨g, hg⟩ :=
    fullHCCharacter_normalConjugate_exists ctx facts not_Galois f x
  exact Finset.mem_image.mpr ⟨g, Finset.mem_univ g, by
    apply Subtype.ext
    exact hg.symm⟩

/-! ## Exact inertia and induction to `HU` -/

/-- If every coordinate is nonprincipal, the inertia in `HU` is contained
in the nested `HC`. -/
theorem pTypeNonGaloisHCCoordinateCharacterInHU_inertia_le
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)
    let HCN := HC.subgroupOf HU
    let xi := pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois lambda
    ClassFunction.inertia HCN (xi : ClassFunction HCN ℂ) ≤ HCN := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  let eHC : HCN ≃* HC := Subgroup.subgroupOfEquivOfLe hHC
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  let thetaBar : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ :=
    pTypeNonGaloisCoordinateCharacter D data lambda
  let xiHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois lambda
  let xi : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois lambda
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  have hcomp : H.IsComplement' UHU := pTypeHInHU_isComplement ctx
  have hHHCN : H ≤ HCN := by
    intro y hy
    exact (le_sup_left :
      (Fitting_core M).subgroupOf M ≤
        (Fitting_core M).subgroupOf M ⊔
          (D.C.map U.subtype).subgroupOf M) hy
  change ClassFunction.inertia HCN
      (xi : ClassFunction HCN ℂ) ≤ HCN
  intro x hx
  obtain ⟨⟨n, v⟩, hnv⟩ := hcomp.2 x
  change (n : HU) * (v : HU) = x at hnv
  let nHC : HCN := ⟨(n : HU), hHHCN n.property⟩
  have hxFixed : ClassFunction.normalConjugate HCN x
      (xi : ClassFunction HCN ℂ) = (xi : ClassFunction HCN ℂ) :=
    (ClassFunction.mem_inertia_iff HCN
      (xi : ClassFunction HCN ℂ) x).mp hx
  have hvFixed : ClassFunction.normalConjugate HCN (v : HU)
      (xi : ClassFunction HCN ℂ) = (xi : ClassFunction HCN ℂ) := by
    calc
      ClassFunction.normalConjugate HCN (v : HU)
          (xi : ClassFunction HCN ℂ) =
        ClassFunction.normalConjugate HCN (nHC : HU)
          (ClassFunction.normalConjugate HCN (v : HU)
            (xi : ClassFunction HCN ℂ)) :=
        (ClassFunction.normalConjugate_coe HCN _ nHC).symm
      _ = ClassFunction.normalConjugate HCN
          ((n : HU) * (v : HU)) (xi : ClassFunction HCN ℂ) :=
        (ClassFunction.normalConjugate_mul HCN
          (n : HU) (v : HU) (xi : ClassFunction HCN ℂ)).symm
      _ = ClassFunction.normalConjugate HCN x
          (xi : ClassFunction HCN ℂ) := by rw [hnv]
      _ = (xi : ClassFunction HCN ℂ) := hxFixed
  have hvMem : (v : HU) ∈ ClassFunction.inertia HCN
      (xi : ClassFunction HCN ℂ) :=
    (ClassFunction.mem_inertia_iff HCN
      (xi : ClassFunction HCN ℂ) (v : HU)).mpr hvFixed
  have hvInvFixed :
      ClassFunction.normalConjugate HCN (v : HU)⁻¹
          (xi : ClassFunction HCN ℂ) =
        (xi : ClassFunction HCN ℂ) :=
    (ClassFunction.mem_inertia_iff HCN
      (xi : ClassFunction HCN ℂ) (v : HU)⁻¹).mp
        ((ClassFunction.inertia HCN
          (xi : ClassFunction HCN ℂ)).inv_mem hvMem)
  let u : U := ⟨((v : HU) : M), v.property⟩
  let uM : M := ⟨(u : Gamma), hUM u.property⟩
  have huFixed : ∀ z : ptypeFCoreFactor ctx,
      thetaBar (D.U_action u z) = thetaBar z := by
    intro z
    let N : Subgroup (Fitting_core M) :=
      (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N z
    let hHCelt : HC := pTypeFCoreToHC ctx facts h
    let hHU : HU := ⟨(hHCelt : M), hHC hHCelt.property⟩
    let y : HCN := ⟨hHU, hHCelt.property⟩
    let zeta : HCN := MulAut.conjNormal (v : HU) y
    have hvalue := congrArg
      (fun f : ClassFunction HCN ℂ ↦ f y) hvInvFixed
    rw [ClassFunction.normalConjugate_apply] at hvalue
    have harg :
        (MulAut.conjNormal (v : HU)⁻¹).symm y = zeta := by
      apply Subtype.ext
      simp only [zeta, MulAut.conjNormal_symm_apply,
        MulAut.conjNormal_apply, inv_inv]
    rw [harg] at hvalue
    have hy : eHC y = hHCelt := rfl
    have hz : eHC zeta = MulAut.conjNormal uM hHCelt := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have hproj := pTypeHCProjection_conj_Fcore ctx facts u h
    have hzvalue : xi zeta =
        thetaBar (D.U_action u (QuotientGroup.mk' N h)) := by
      calc
        xi zeta = xiHC (eHC zeta) :=
          pTypeNonGaloisHCCoordinateCharacterInHU_apply
            ctx facts not_Galois lambda zeta
        _ = xiHC (MulAut.conjNormal uM hHCelt) := by rw [hz]
        _ = thetaBar
            (pTypeHCProjection ctx facts
              (MulAut.conjNormal uM hHCelt)) :=
          pTypeExtendFCoreFactorCharacterToHC_apply
            ctx facts thetaBar _
        _ = thetaBar
            (D.U_action u
              (pTypeHCProjection ctx facts hHCelt)) := by rw [hproj]
        _ = thetaBar
            (D.U_action u (QuotientGroup.mk' N h)) := by
          rw [pTypeHCProjection_apply_Fcore]
    have hyvalue : xi y = thetaBar (QuotientGroup.mk' N h) := by
      calc
        xi y = xiHC (eHC y) :=
          pTypeNonGaloisHCCoordinateCharacterInHU_apply
            ctx facts not_Galois lambda y
        _ = xiHC hHCelt := by rw [hy]
        _ = thetaBar (QuotientGroup.mk' N h) :=
          pTypeNonGaloisHCCoordinateCharacter_apply_Fcore
            ctx facts not_Galois lambda h
    exact hzvalue.symm.trans (hvalue.trans hyvalue)
  have huC : u ∈ D.C :=
    (pTypeNonGaloisCoordinateCharacter_fixed_iff_mem_C
      D data lambda hlambda u).mp huFixed
  have hvHC : (v : HU) ∈ HCN := by
    change ((v : HU) : M) ∈
      (Fitting_core M).subgroupOf M ⊔
        (D.C.map U.subtype).subgroupOf M
    exact (le_sup_right :
      (D.C.map U.subtype).subgroupOf M ≤
        (Fitting_core M).subgroupOf M ⊔
          (D.C.map U.subtype).subgroupOf M) ⟨u, huC, rfl⟩
  rw [← hnv]
  exact HCN.mul_mem (hHHCN n.property) hvHC

/-- The intermediate induction `HC → HU` is irreducible for every
all-nonprincipal coordinate family. -/
theorem pTypeNonGaloisHCCoordinateCharacterInHU_induce_irreducible
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
      (Ptype_factor_action ctx facts)
    let HCN := HC.subgroupOf HU
    let xi := pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois lambda
    IsIrreducibleCharacter HU ℂ
      (ClassFunction.induce HCN (xi : ClassFunction HCN ℂ)) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  exact FrobeniusKernelInductionAux.irreducible_induce_of_inertia _
    (pTypeNonGaloisHCCoordinateCharacterInHU_inertia_le
      ctx facts not_Galois lambda hlambda)

/-- The irreducible character of `HU` induced by an all-nonprincipal
coordinate family. -/
noncomputable def pTypeNonGaloisHUCoordinateCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    (lambda : W₁ → MulChar data.H₁ ℂ) →
    (∀ w, lambda w ≠ 1) →
      IrreducibleCharacter (pTypeHUInMaximal M (derivedWithin M)) ℂ := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
    (Ptype_factor_action ctx facts)
  let HCN := HC.subgroupOf HU
  let xi := pTypeNonGaloisHCCoordinateCharacterInHU
    ctx facts not_Galois lambda
  exact ⟨ClassFunction.induce HCN (xi : ClassFunction HCN ℂ),
    pTypeNonGaloisHCCoordinateCharacterInHU_induce_irreducible
      ctx facts not_Galois lambda hlambda⟩

@[simp]
theorem pTypeNonGaloisHUCoordinateCharacter_coe
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
    (pTypeNonGaloisHUCoordinateCharacter
        ctx facts not_Galois lambda hlambda :
      ClassFunction (pTypeHUInMaximal M (derivedWithin M)) ℂ) =
      ClassFunction.induce
        ((pTypeHCInMaximal M (Fitting_core M) U W₁
          (Ptype_factor_action ctx facts)).subgroupOf
            (pTypeHUInMaximal M (derivedWithin M)))
        (pTypeNonGaloisHCCoordinateCharacterInHU
          ctx facts not_Galois lambda) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  exact fun _lambda _hlambda ↦ rfl

/-! ## Constant coordinates and the induced finite families -/

/-- A constant-coordinate `HC` character is fixed by the outer complement
`W₁`. -/
theorem pTypeNonGaloisConstantHCCoordinateCharacter_W₁_fixed
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : MulChar data.H₁ ℂ) (w : W₁),
      let D := Ptype_factor_action ctx facts
      let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
      let wM : M := ⟨(w : Gamma), ctx.typeP.1.2.1.1 w.property⟩
      let xi := pTypeNonGaloisHCCoordinateCharacter
        ctx facts not_Galois (fun _ ↦ lambda)
      ClassFunction.normalConjugate HC wM
          (xi : ClassFunction HC ℂ) =
        (xi : ClassFunction HC ℂ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda w
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : Gamma), hW₁M w.property⟩
  let wInvM : M := ⟨(w⁻¹ : Gamma), hW₁M w⁻¹.property⟩
  let xi := pTypeNonGaloisHCCoordinateCharacter
    ctx facts not_Galois (fun _ ↦ lambda)
  change ClassFunction.normalConjugate HC wM
      (pTypeNonGaloisHCCoordinateCharacter
        ctx facts not_Galois (fun _ ↦ lambda) : ClassFunction HC ℂ) =
    (pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois (fun _ ↦ lambda) : ClassFunction HC ℂ)
  ext x
  rw [ClassFunction.normalConjugate_apply]
  have harg : (MulAut.conjNormal wM).symm x =
      MulAut.conjNormal wInvM x := by
    apply Subtype.ext
    apply Subtype.ext
    rfl
  rw [pTypeNonGaloisHCCoordinateCharacter_apply,
    pTypeNonGaloisHCCoordinateCharacter_apply, harg]
  have hproj : pTypeHCProjection ctx facts
        (MulAut.conjNormal wInvM x) =
      D.W₁_action w⁻¹ (pTypeHCProjection ctx facts x) := by
    change pTypeHCProjection ctx facts
        (MulAut.conjNormal
          (⟨(w⁻¹ : Gamma), ctx.typeP.1.2.1.1 w⁻¹.property⟩ : M) x) = _
    exact pTypeHCProjection_conj_W₁ ctx facts w⁻¹ x
  rw [hproj]
  exact pTypeNonGaloisConstantCoordinateCharacter_W₁_fixed
    D data lambda w⁻¹ (pTypeHCProjection ctx facts x)

/-- A constant-coordinate `HC` character cannot induce irreducibly to `M`. -/
theorem pTypeNonGaloisConstantHCCoordinateCharacter_induce_reducible
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ lambda : MulChar data.H₁ ℂ,
      let D := Ptype_factor_action ctx facts
      let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
      let xi := pTypeNonGaloisHCCoordinateCharacter
        ctx facts not_Galois (fun _ ↦ lambda)
      ¬ IsIrreducibleCharacter M ℂ
        (ClassFunction.induce HC (xi : ClassFunction HC ℂ)) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let xi := pTypeNonGaloisHCCoordinateCharacter
    ctx facts not_Galois (fun _ ↦ lambda)
  change ¬ IsIrreducibleCharacter M ℂ
    (ClassFunction.induce HC (xi : ClassFunction HC ℂ))
  intro hirr
  letI : Invertible (Nat.card HC : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HC)).ne')
  have hInertia : ClassFunction.inertia HC
      (xi : ClassFunction HC ℂ) = HC :=
    ClassFunction.inertia_eq_of_induce_isIrreducible HC xi hirr
  have hW₁_nontrivial : 1 < Nat.card W₁ := by
    rw [D.card_W₁]
    exact D.q_prime.one_lt
  letI : Nontrivial W₁ :=
    Finite.one_lt_card_iff_nontrivial.mp hW₁_nontrivial
  obtain ⟨w, hw⟩ := exists_ne (1 : W₁)
  have hW₁M : W₁ ≤ M := ctx.typeP.1.2.1.1
  let wM : M := ⟨(w : Gamma), hW₁M w.property⟩
  have hwInertia : wM ∈ ClassFunction.inertia HC
      (xi : ClassFunction HC ℂ) :=
    (ClassFunction.mem_inertia_iff HC
      (xi : ClassFunction HC ℂ) wM).mpr
        (pTypeNonGaloisConstantHCCoordinateCharacter_W₁_fixed
          ctx facts not_Galois lambda w)
  have hwHC : wM ∈ HC := by
    rw [← hInertia]
    exact hwInertia
  have hwDer : wM ∈ (derivedWithin M).subgroupOf M :=
    pTypeNonGaloisHCInMaximal_le_HU ctx facts hwHC
  have hwW₁ : wM ∈ W₁.subgroupOf M := w.property
  have hwBot : wM ∈ (⊥ : Subgroup M) :=
    ctx.typeP.1.2.2.2.2.2.2.disjoint.le_bot ⟨hwDer, hwW₁⟩
  have hwMone : wM = (1 : M) := Subgroup.mem_bot.mp hwBot
  apply hw
  apply Subtype.ext
  exact congrArg (fun z : M ↦ (z : Gamma)) hwMone

/-- Every member of the full source family induces irreducibly to `HU`. -/
theorem pTypeNonGaloisFullHCCharacterInHUFamily_induce_irreducible
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeHUInMaximal M (derivedWithin M)
    let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
    let HCN := HC.subgroupOf HU
    ∀ chi ∈ pTypeNonGaloisFullHCCharacterInHUFamily
        ctx facts not_Galois,
      IsIrreducibleCharacter HU ℂ
        (ClassFunction.induce HCN (chi : ClassFunction HCN ℂ)) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  dsimp only
  intro chi hchi
  rw [pTypeNonGaloisFullHCCharacterInHUFamily] at hchi
  obtain ⟨f, _hf, rfl⟩ := Finset.mem_image.mp hchi
  exact pTypeNonGaloisHCCoordinateCharacterInHU_induce_irreducible
    ctx facts not_Galois (fun w ↦ (f w : MulChar data.H₁ ℂ))
      (fun w ↦
        (mem_pTypeNontrivialMulChars
          (Q := data.H₁) (f w : MulChar data.H₁ ℂ)).mp
            (f w).property)

/-- The image in `Irr(HU)` of the full stable source family. -/
noncomputable def pTypeNonGaloisFullHUCoordinateFamily
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Finset (IrreducibleCharacter
      (pTypeHUInMaximal M (derivedWithin M)) ℂ) := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  let X := pTypeNonGaloisFullHCCharacterInHUFamily
    ctx facts not_Galois
  let hInd := pTypeNonGaloisFullHCCharacterInHUFamily_induce_irreducible
    ctx facts not_Galois
  exact Finset.univ.image
    (ClassFunction.induceIrreducibleOn HCN X hInd)

/-- The irreducible `HU` character attached to a nonprincipal constant
coordinate. -/
noncomputable def pTypeNonGaloisConstantHUCharacter
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : MulChar data.H₁ ℂ), lambda ≠ 1 →
      IrreducibleCharacter (pTypeHUInMaximal M (derivedWithin M)) ℂ := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  exact pTypeNonGaloisHUCoordinateCharacter ctx facts not_Galois
    (fun _ ↦ lambda) (fun _ ↦ hlambda)

/-- Distinct nonprincipal constant coordinates give distinct irreducible
characters of `HU`. -/
theorem pTypeNonGaloisConstantHUCharacter_eq
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda mu : MulChar data.H₁ ℂ)
      (hlambda : lambda ≠ 1) (hmu : mu ≠ 1),
      pTypeNonGaloisConstantHUCharacter
          ctx facts not_Galois lambda hlambda =
        pTypeNonGaloisConstantHUCharacter
          ctx facts not_Galois mu hmu →
      lambda = mu := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda mu hlambda hmu heq
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  let eHC : HCN ≃* HC := Subgroup.subgroupOfEquivOfLe hHC
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let UHU : Subgroup HU := (U.subgroupOf M).subgroupOf HU
  let thetaLambda : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ :=
    pTypeNonGaloisConstantCoordinateCharacter D data lambda
  let thetaMu : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ :=
    pTypeNonGaloisConstantCoordinateCharacter D data mu
  let xiLambdaHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois (fun _ ↦ lambda)
  let xiMuHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois (fun _ ↦ mu)
  let xiLambda : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois (fun _ ↦ lambda)
  let xiMu : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois (fun _ ↦ mu)
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hUM : U ≤ M := hUder.trans hDerM
  have hcomp : H.IsComplement' UHU := pTypeHInHU_isComplement ctx
  have hHHCN : H ≤ HCN := by
    intro y hy
    exact (le_sup_left :
      (Fitting_core M).subgroupOf M ≤
        (Fitting_core M).subgroupOf M ⊔
          (D.C.map U.subtype).subgroupOf M) hy
  have hInd : ClassFunction.induce HCN
        (xiLambda : ClassFunction HCN ℂ) =
      ClassFunction.induce HCN
        (xiMu : ClassFunction HCN ℂ) := by
    calc
      ClassFunction.induce HCN (xiLambda : ClassFunction HCN ℂ) =
          (pTypeNonGaloisConstantHUCharacter
            ctx facts not_Galois lambda hlambda :
              ClassFunction HU ℂ) :=
        (pTypeNonGaloisHUCoordinateCharacter_coe
          ctx facts not_Galois (fun _ ↦ lambda)
            (fun _ ↦ hlambda)).symm
      _ = (pTypeNonGaloisConstantHUCharacter
            ctx facts not_Galois mu hmu :
              ClassFunction HU ℂ) :=
        congrArg (fun chi : IrreducibleCharacter HU ℂ ↦
          (chi : ClassFunction HU ℂ)) heq
      _ = ClassFunction.induce HCN
          (xiMu : ClassFunction HCN ℂ) :=
        pTypeNonGaloisHUCoordinateCharacter_coe
          ctx facts not_Galois (fun _ ↦ mu) (fun _ ↦ hmu)
  letI : Invertible (Nat.card HCN : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HCN)).ne')
  obtain ⟨x, hxOrbit⟩ :=
    (ClassFunction.cfclass_Ind_eq_iff HCN xiLambda xiMu).mp hInd
  obtain ⟨⟨n, v⟩, hnv⟩ := hcomp.2 x
  change (n : HU) * (v : HU) = x at hnv
  let nHC : HCN := ⟨(n : HU), hHHCN n.property⟩
  have hvOrbit : ClassFunction.normalConjugate HCN (v : HU)
        (xiLambda : ClassFunction HCN ℂ) =
      (xiMu : ClassFunction HCN ℂ) := by
    calc
      ClassFunction.normalConjugate HCN (v : HU)
          (xiLambda : ClassFunction HCN ℂ) =
        ClassFunction.normalConjugate HCN (nHC : HU)
          (ClassFunction.normalConjugate HCN (v : HU)
            (xiLambda : ClassFunction HCN ℂ)) :=
        (ClassFunction.normalConjugate_coe HCN _ nHC).symm
      _ = ClassFunction.normalConjugate HCN
          ((n : HU) * (v : HU))
          (xiLambda : ClassFunction HCN ℂ) :=
        (ClassFunction.normalConjugate_mul HCN
          (n : HU) (v : HU)
          (xiLambda : ClassFunction HCN ℂ)).symm
      _ = ClassFunction.normalConjugate HCN x
          (xiLambda : ClassFunction HCN ℂ) := by rw [hnv]
      _ = (xiMu : ClassFunction HCN ℂ) := hxOrbit
  let u : U := ⟨((v : HU) : M), v.property⟩
  let uInvM : M := ⟨(u⁻¹ : Gamma), hUM u⁻¹.property⟩
  have hfactorOrbit : ∀ z : ptypeFCoreFactor ctx,
      thetaLambda (D.U_action u⁻¹ z) = thetaMu z := by
    intro z
    let N : Subgroup (Fitting_core M) :=
      (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N z
    let hHCelt : HC := pTypeFCoreToHC ctx facts h
    let hHU : HU := ⟨(hHCelt : M), hHC hHCelt.property⟩
    let y : HCN := ⟨hHU, hHCelt.property⟩
    let zeta : HCN := (MulAut.conjNormal (v : HU)).symm y
    have hvalue : xiLambda zeta = xiMu y := by
      have hvalue' := congrArg
        (fun f : ClassFunction HCN ℂ ↦ f y) hvOrbit
      rw [ClassFunction.normalConjugate_apply] at hvalue'
      exact hvalue'
    have hy : eHC y = hHCelt := rfl
    have hz : eHC zeta = MulAut.conjNormal uInvM hHCelt := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    have hproj : pTypeHCProjection ctx facts
          (MulAut.conjNormal uInvM hHCelt) =
        D.U_action u⁻¹ (pTypeHCProjection ctx facts hHCelt) := by
      change pTypeHCProjection ctx facts
          (MulAut.conjNormal
            (⟨(u⁻¹ : Gamma),
              (ctx.typeP.2.1.2.2.2.2.1.trans
                (Subgroup.map_subtype_le (_root_.commutator M)))
                u⁻¹.property⟩ : M)
            (pTypeFCoreToHC ctx facts h)) = _
      exact pTypeHCProjection_conj_Fcore ctx facts u⁻¹ h
    have hzvalue : xiLambda zeta =
        thetaLambda
          (D.U_action u⁻¹ (QuotientGroup.mk' N h)) := by
      calc
        xiLambda zeta = xiLambdaHC (eHC zeta) :=
          pTypeNonGaloisHCCoordinateCharacterInHU_apply
            ctx facts not_Galois (fun _ ↦ lambda) zeta
        _ = xiLambdaHC (MulAut.conjNormal uInvM hHCelt) := by
          rw [hz]
        _ = thetaLambda
            (pTypeHCProjection ctx facts
              (MulAut.conjNormal uInvM hHCelt)) :=
          pTypeExtendFCoreFactorCharacterToHC_apply
            ctx facts thetaLambda _
        _ = thetaLambda
            (D.U_action u⁻¹
              (pTypeHCProjection ctx facts hHCelt)) := by rw [hproj]
        _ = thetaLambda
            (D.U_action u⁻¹ (QuotientGroup.mk' N h)) := by
          rw [pTypeHCProjection_apply_Fcore]
    have hyvalue : xiMu y = thetaMu (QuotientGroup.mk' N h) := by
      calc
        xiMu y = xiMuHC (eHC y) :=
          pTypeNonGaloisHCCoordinateCharacterInHU_apply
            ctx facts not_Galois (fun _ ↦ mu) y
        _ = xiMuHC hHCelt := by rw [hy]
        _ = thetaMu (QuotientGroup.mk' N h) :=
          pTypeNonGaloisHCCoordinateCharacter_apply_Fcore
            ctx facts not_Galois (fun _ ↦ mu) h
    exact hzvalue.symm.trans (hvalue.trans hyvalue)
  exact pTypeNonGaloisConstantCoordinateCharacter_eq_of_U_translate
    D hD data lambda mu hlambda u⁻¹ hfactorOrbit

/-- Bundle a nonprincipal constant scalar character as a character of `HU`. -/
noncomputable def pTypeNonGaloisConstantHUCharacterFromIndex
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ↑(pTypeNontrivialMulChars data.H₁) →
      IrreducibleCharacter (pTypeHUInMaximal M (derivedWithin M)) ℂ := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda
  exact pTypeNonGaloisConstantHUCharacter ctx facts not_Galois lambda
    ((mem_pTypeNontrivialMulChars
      (Q := data.H₁) (lambda : MulChar data.H₁ ℂ)).mp lambda.property)

theorem pTypeNonGaloisConstantHUCharacterFromIndex_injective
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    Function.Injective
      (pTypeNonGaloisConstantHUCharacterFromIndex
        ctx facts not_Galois) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda mu hlm
  apply Subtype.ext
  exact pTypeNonGaloisConstantHUCharacter_eq
    ctx facts not_Galois lambda mu
      ((mem_pTypeNontrivialMulChars
        (Q := data.H₁) (lambda : MulChar data.H₁ ℂ)).mp lambda.property)
      ((mem_pTypeNontrivialMulChars
        (Q := data.H₁) (mu : MulChar data.H₁ ℂ)).mp mu.property) hlm

/-- The finite subfamily of nonprincipal constant-coordinate characters. -/
noncomputable def pTypeNonGaloisConstantHUFamily
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Finset (IrreducibleCharacter
      (pTypeHUInMaximal M (derivedWithin M)) ℂ) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  exact Finset.univ.image
    (pTypeNonGaloisConstantHUCharacterFromIndex
      ctx facts not_Galois)

/-- The constant family has cardinality `p - 1`. -/
theorem pTypeNonGaloisConstantHUFamily_card
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    (pTypeNonGaloisConstantHUFamily
      ctx facts not_Galois).card =
        (Ptype_factor_action ctx facts).p - 1 := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  rw [pTypeNonGaloisConstantHUFamily,
    Finset.card_image_of_injective _
      (pTypeNonGaloisConstantHUCharacterFromIndex_injective
        ctx facts not_Galois),
    Finset.card_univ, ← Nat.card_eq_fintype_card,
    natCard_pTypeNontrivialMulChars, data.card_H₁]

/-- The constant subfamily is contained in the full `HU` family. -/
theorem pTypeNonGaloisConstantHUFamily_subset_full
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeNonGaloisConstantHUFamily ctx facts not_Galois ⊆
      pTypeNonGaloisFullHUCoordinateFamily
        ctx facts not_Galois := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  let X := pTypeNonGaloisFullHCCharacterInHUFamily
    ctx facts not_Galois
  let hInd := pTypeNonGaloisFullHCCharacterInHUFamily_induce_irreducible
    ctx facts not_Galois
  intro chi hchi
  rw [pTypeNonGaloisConstantHUFamily] at hchi
  obtain ⟨lambda, _hlambda, rfl⟩ := Finset.mem_image.mp hchi
  let f : PTypeNonGaloisCoordinateFamilyIndex data := fun _ ↦ lambda
  have hsource : pTypeNonGaloisFullHCCharacterInHUFromIndex
      ctx facts not_Galois f ∈ X := by
    change pTypeNonGaloisFullHCCharacterInHUFromIndex
      ctx facts not_Galois f ∈
        pTypeNonGaloisFullHCCharacterInHUFamily ctx facts not_Galois
    rw [pTypeNonGaloisFullHCCharacterInHUFamily]
    exact Finset.mem_image.mpr ⟨f, Finset.mem_univ f, rfl⟩
  let source : {psi // psi ∈ X} :=
    ⟨pTypeNonGaloisFullHCCharacterInHUFromIndex
      ctx facts not_Galois f, hsource⟩
  rw [pTypeNonGaloisFullHUCoordinateFamily]
  refine Finset.mem_image.mpr
    ⟨source, Finset.mem_univ source, ?_⟩
  apply Subtype.ext
  rfl

/-! ## Kernel-layer membership -/

private theorem fullHCCharacter_not_trivial_on_H
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
      let D := Ptype_factor_action ctx facts
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
      let HCN := HC.subgroupOf HU
      let H : Subgroup HU :=
        ((Fitting_core M).subgroupOf M).subgroupOf HU
      let xiHCN := pTypeNonGaloisHCCoordinateCharacterInHU
        ctx facts not_Galois lambda
      ¬ H.subgroupOf HCN ≤ xiHCN.representation.ρ.ker := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  let eHC : HCN ≃* HC := Subgroup.subgroupOfEquivOfLe hHC
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let theta : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ :=
    pTypeNonGaloisCoordinateCharacter D data lambda
  let xiHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter ctx facts not_Galois lambda
  let xiHCN : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois lambda
  intro hHKernel
  have hthetaOne : ∀ z : ptypeFCoreFactor ctx, theta z = 1 := by
    intro z
    let N : Subgroup (Fitting_core M) :=
      (Ptype_Fcore_kernel ctx).subgroupOf (Fitting_core M)
    obtain ⟨h, rfl⟩ := QuotientGroup.mk'_surjective N z
    let hHCelt : HC := pTypeFCoreToHC ctx facts h
    let hHU : HU := ⟨(hHCelt : M), hHC hHCelt.property⟩
    let y : HCN := ⟨hHU, hHCelt.property⟩
    have hyH : y ∈ H.subgroupOf HCN := h.property
    have hkerEq : ClassFunction.translationKernel
        (xiHCN : ClassFunction HCN ℂ) =
        xiHCN.representation.ρ.ker :=
      translationKernel_irreducibleCharacter_general xiHCN
    have hyKernel : y ∈ ClassFunction.translationKernel
        (xiHCN : ClassFunction HCN ℂ) := by
      rw [hkerEq]
      exact hHKernel hyH
    rw [ClassFunction.mem_translationKernel_iff] at hyKernel
    have hvalue := hyKernel (1 : HCN)
    have hyvalue : xiHCN y = theta (QuotientGroup.mk' N h) := by
      calc
        xiHCN y = xiHC (eHC y) :=
          pTypeNonGaloisHCCoordinateCharacterInHU_apply
            ctx facts not_Galois lambda y
        _ = xiHC hHCelt := by rfl
        _ = theta (QuotientGroup.mk' N h) :=
          pTypeNonGaloisHCCoordinateCharacter_apply_Fcore
            ctx facts not_Galois lambda h
    have hone : xiHCN 1 = 1 := by
      calc
        xiHCN 1 = xiHC (eHC 1) :=
          pTypeNonGaloisHCCoordinateCharacterInHU_apply
            ctx facts not_Galois lambda 1
        _ = theta (pTypeHCProjection ctx facts (eHC 1)) :=
          pTypeExtendFCoreFactorCharacterToHC_apply
            ctx facts theta _
        _ = theta 1 := by
          have harg : pTypeHCProjection ctx facts (eHC (1 : HCN)) = 1 := by
            rw [map_one, map_one]
          exact congrArg (fun z => (theta : ClassFunction _ ℂ) z) harg
        _ = ((pTypeIrreducibleDegree theta : ℕ) : ℂ) :=
          IrreducibleCharacter.apply_one_eq_finrank theta
        _ = 1 := by
          have hdegree : pTypeIrreducibleDegree theta = 1 := by
            change pTypeIrreducibleDegree
              (pTypeNonGaloisCoordinateCharacter D data lambda) = 1
            exact pTypeNonGaloisCoordinateCharacter_degree D data lambda
          rw [hdegree]
          norm_num
    rw [mul_one] at hvalue
    exact hyvalue.symm.trans (hvalue.trans hone)
  apply hlambda 1
  apply MulChar.ext'
  intro a
  let x : actionConjugate D.W₁_action data.H₁ (1 : W₁) :=
    ⟨(a : ptypeFCoreFactor ctx), by
      rw [actionConjugate_one]
      exact a.property⟩
  calc
    lambda 1 a =
        pTypeActionConjugateMulChar
          D data.H₁ (1 : W₁) (lambda 1) x := by
      change lambda 1 a =
        lambda 1 (((D.W₁_action (1 : W₁)).subgroupMap data.H₁).symm x)
      have hx : x =
          (D.W₁_action (1 : W₁)).subgroupMap data.H₁ a := by
        apply Subtype.ext
        change (a : ptypeFCoreFactor ctx) =
          D.W₁_action (1 : W₁) (a : ptypeFCoreFactor ctx)
        rw [map_one]
        rfl
      rw [hx, MulEquiv.symm_apply_apply]
    _ = theta (x : ptypeFCoreFactor ctx) :=
      (pTypeNonGaloisCoordinateCharacter_apply_coordinate
        D data lambda (1 : W₁) x).symm
    _ = 1 := hthetaOne (x : ptypeFCoreFactor ctx)
    _ = (1 : MulChar data.H₁ ℂ) a := by
      simpa only [val_toUnits_apply] using
        (MulChar.one_apply_coe (toUnits a)).symm

private theorem irreducibleCharacter_isConstituent_of_eq_induce
    {G : Type u} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (K : Subgroup G)
    (psi : IrreducibleCharacter K ℂ)
    (chi : IrreducibleCharacter G ℂ)
    (hchi : (chi : ClassFunction G ℂ) =
      ClassFunction.induce K (psi : ClassFunction K ℂ)) :
    chi.IsConstituent
      (ClassFunction.induce K (psi : ClassFunction K ℂ)) := by
  unfold IrreducibleCharacter.IsConstituent
  rw [← hchi, IrreducibleCharacter.characterPairing_self]
  exact one_ne_zero

private theorem le_representationKernel_of_le_translationKernel
    {G : Type u} [Group G]
    (A : Subgroup G)
    (chi : IrreducibleCharacter G ℂ)
    (hkernel : A ≤ ClassFunction.translationKernel
      (chi : ClassFunction G ℂ)) :
    A ≤ chi.representation.ρ.ker := by
  rw [← translationKernel_irreducibleCharacter_general chi]
  exact hkernel

private theorem not_le_representationKernel_of_constituent_induce
    {G : Type u} [Group G] [Fintype G]
    [Invertible (Nat.card G : ℂ)]
    (K A : Subgroup G) [K.Normal] [A.Normal]
    (hAK : A ≤ K)
    (psi : IrreducibleCharacter K ℂ)
    (chi : IrreducibleCharacter G ℂ)
    (hconstituent : chi.IsConstituent
      (ClassFunction.induce K (psi : ClassFunction K ℂ)))
    (hsource : ¬ A.subgroupOf K ≤ psi.representation.ρ.ker) :
    ¬ A ≤ chi.representation.ρ.ker := by
  intro hkernel
  apply hsource
  exact subgroupOf_le_constituent_kernel_of_induce_general
    K A hAK chi psi hconstituent hkernel

private theorem fullHUCharacter_not_trivial_on_H
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let xiHU := pTypeNonGaloisHUCoordinateCharacter
        ctx facts not_Galois lambda hlambda
      ¬ H ≤ ClassFunction.translationKernel
        (xiHU : ClassFunction HU ℂ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let HCN := HC.subgroupOf HU
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let xiHCN : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois lambda
  let xiHU : IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisHUCoordinateCharacter
      ctx facts not_Galois lambda hlambda
  have hHHCN : H ≤ HCN := by
    intro x hx
    exact (le_sup_left :
      (Fitting_core M).subgroupOf M ≤
        (Fitting_core M).subgroupOf M ⊔
          (D.C.map U.subtype).subgroupOf M) hx
  have hHCNNotKernel : ¬ H.subgroupOf HCN ≤
      xiHCN.representation.ρ.ker :=
    fullHCCharacter_not_trivial_on_H
      ctx facts not_Galois lambda hlambda
  letI : Invertible (Nat.card HU : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HU)).ne')
  have hconstituent : xiHU.IsConstituent
      (ClassFunction.induce HCN
        (xiHCN : ClassFunction HCN ℂ)) :=
    irreducibleCharacter_isConstituent_of_eq_induce HCN xiHCN xiHU
      (pTypeNonGaloisHUCoordinateCharacter_coe
        ctx facts not_Galois lambda hlambda)
  have hnotRepresentation : ¬ H ≤ xiHU.representation.ρ.ker :=
    not_le_representationKernel_of_constituent_induce
      HCN H hHHCN xiHCN xiHU hconstituent hHCNNotKernel
  intro hkernel
  apply hnotRepresentation
  exact le_representationKernel_of_le_translationKernel H xiHU hkernel

/-- Every all-nonprincipal `HU` coordinate character lies in the F-core
kernel layer `X_(H₀)`. -/
theorem pTypeNonGaloisHUCoordinateCharacter_mem_Iirr_kerD
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
      pTypeNonGaloisHUCoordinateCharacter
          ctx facts not_Galois lambda hlambda ∈
        Iirr_kerD (k := ℂ) H H₀ := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  let eHC : HCN ≃* HC := Subgroup.subgroupOfEquivOfLe hHC
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀ : Subgroup HU :=
    ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
  let theta : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ :=
    pTypeNonGaloisCoordinateCharacter D data lambda
  let xiHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois lambda
  let xiHCN : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois lambda
  let xiHU : IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisHUCoordinateCharacter
      ctx facts not_Galois lambda hlambda
  letI : H.Normal :=
    Subgroup.Normal.subgroupOf (Fcore_normal M) HU
  letI : H₀.Normal :=
    Subgroup.Normal.subgroupOf
      (Ptype_Fcore_kernel_normal_M ctx) HU
  have hHHCN : H ≤ HCN := by
    intro x hx
    exact (le_sup_left :
      (Fitting_core M).subgroupOf M ≤
        (Fitting_core M).subgroupOf M ⊔
          (D.C.map U.subtype).subgroupOf M) hx
  have hH₀HCN : H₀ ≤ HCN := by
    intro x hx
    exact (le_sup_left :
      (Fitting_core M).subgroupOf M ≤
        (Fitting_core M).subgroupOf M ⊔
          (D.C.map U.subtype).subgroupOf M)
      ((Ptype_Fcore_kernel_lt ctx).le hx)
  have hH₀NestedKernel : H₀.subgroupOf HCN ≤
      ClassFunction.translationKernel
        (xiHCN : ClassFunction HCN ℂ) := by
    intro x hx
    have hxH₀C : eHC x ∈
        pTypeH0CInHC M (Fitting_core M)
          (Ptype_Fcore_kernel ctx) U W₁ D := by
      exact (le_sup_left :
        (Ptype_Fcore_kernel ctx).subgroupOf M ≤
          (Ptype_Fcore_kernel ctx).subgroupOf M ⊔
            (D.C.map U.subtype).subgroupOf M) hx
    have hxKernel : eHC x ∈ ClassFunction.translationKernel
        (pTypeExtendFCoreFactorCharacterToHC
          ctx facts theta : ClassFunction HC ℂ) :=
      pTypeH0CInHC_le_extension_translationKernel
        ctx facts theta hxH₀C
    rw [ClassFunction.mem_translationKernel_iff] at hxKernel ⊢
    intro y
    calc
      xiHCN (x * y) = xiHC (eHC (x * y)) :=
        pTypeNonGaloisHCCoordinateCharacterInHU_apply
          ctx facts not_Galois lambda (x * y)
      _ = xiHC (eHC x * eHC y) := by rw [map_mul]
      _ = xiHC (eHC y) := hxKernel (eHC y)
      _ = xiHCN y :=
        (pTypeNonGaloisHCCoordinateCharacterInHU_apply
          ctx facts not_Galois lambda y).symm
  have hH₀Kernel : H₀ ≤ ClassFunction.translationKernel
      (xiHU : ClassFunction HU ℂ) := by
    change H₀ ≤ ClassFunction.translationKernel
      (ClassFunction.induce HCN
        (xiHCN : ClassFunction HCN ℂ))
    exact ClassFunction.le_translationKernel_induce
      H₀ HCN hH₀HCN (xiHCN : ClassFunction HCN ℂ)
        hH₀NestedKernel
  have hHNotKernel : ¬ H ≤ ClassFunction.translationKernel
      (xiHU : ClassFunction HU ℂ) :=
    fullHUCharacter_not_trivial_on_H
      ctx facts not_Galois lambda hlambda
  rw [mem_Iirr_kerD]
  exact ⟨hH₀Kernel, hHNotKernel⟩

/-- Every all-nonprincipal `HU` coordinate character also lies in the
smaller source layer cut out by `H₀C`. -/
theorem pTypeNonGaloisHUCoordinateCharacter_mem_Iirr_kerD_H0C
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
      let D := Ptype_factor_action ctx facts
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let H₀C := pTypeH0CInDerived M (derivedWithin M)
        (Ptype_Fcore_kernel ctx) U W₁ D
      pTypeNonGaloisHUCoordinateCharacter
          ctx facts not_Galois lambda hlambda ∈
        Iirr_kerD (k := ℂ) H H₀C := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  let eHC : HCN ≃* HC := Subgroup.subgroupOfEquivOfLe hHC
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀C : Subgroup HU := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  letI : H₀C.Normal := by
    change (pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D).Normal
    rw [pTypeH0CInDerived_eq_subgroupOf ctx facts]
    exact Subgroup.Normal.subgroupOf
      (pTypeH0CInMaximal_normal ctx facts) HU
  let theta : IrreducibleCharacter (ptypeFCoreFactor ctx) ℂ :=
    pTypeNonGaloisCoordinateCharacter D data lambda
  let xiHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter ctx facts not_Galois lambda
  let xiHCN : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois lambda
  let xiHU : IrreducibleCharacter HU ℂ :=
    pTypeNonGaloisHUCoordinateCharacter
      ctx facts not_Galois lambda hlambda
  have hH₀CHCN : H₀C ≤ HCN := by
    change pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D ≤ HC.subgroupOf HU
    rw [pTypeH0CInDerived_eq_subgroupOf ctx facts]
    exact Subgroup.subgroupOf_mono HU
      (pTypeH0CInMaximal_le_HC ctx facts)
  have hH₀CNestedKernel : H₀C.subgroupOf HCN ≤
      ClassFunction.translationKernel
        (xiHCN : ClassFunction HCN ℂ) := by
    intro x hx
    have hxRestricted : ((x : HCN) : HU) ∈
        (pTypeH0CInMaximal M (Ptype_Fcore_kernel ctx) U W₁ D).subgroupOf HU := by
      rw [← pTypeH0CInDerived_eq_subgroupOf ctx facts]
      exact hx
    have hxH₀C : eHC x ∈
        pTypeH0CInHC M (Fitting_core M)
          (Ptype_Fcore_kernel ctx) U W₁ D := hxRestricted
    have hxKernel : eHC x ∈ ClassFunction.translationKernel
        (pTypeExtendFCoreFactorCharacterToHC
          ctx facts theta : ClassFunction HC ℂ) :=
      pTypeH0CInHC_le_extension_translationKernel
        ctx facts theta hxH₀C
    rw [ClassFunction.mem_translationKernel_iff] at hxKernel ⊢
    intro y
    calc
      xiHCN (x * y) = xiHC (eHC (x * y)) :=
        pTypeNonGaloisHCCoordinateCharacterInHU_apply
          ctx facts not_Galois lambda (x * y)
      _ = xiHC (eHC x * eHC y) := by rw [map_mul]
      _ = xiHC (eHC y) := hxKernel (eHC y)
      _ = xiHCN y :=
        (pTypeNonGaloisHCCoordinateCharacterInHU_apply
          ctx facts not_Galois lambda y).symm
  have hH₀CKernel : H₀C ≤ ClassFunction.translationKernel
      (xiHU : ClassFunction HU ℂ) := by
    change H₀C ≤ ClassFunction.translationKernel
      (ClassFunction.induce HCN
        (xiHCN : ClassFunction HCN ℂ))
    exact ClassFunction.le_translationKernel_induce
      H₀C HCN hH₀CHCN (xiHCN : ClassFunction HCN ℂ)
        hH₀CNestedKernel
  have hHNotKernel : ¬ H ≤ ClassFunction.translationKernel
      (xiHU : ClassFunction HU ℂ) :=
    (mem_Iirr_kerD.mp
      (pTypeNonGaloisHUCoordinateCharacter_mem_Iirr_kerD
        ctx facts not_Galois lambda hlambda)).2
  rw [mem_Iirr_kerD]
  exact ⟨hH₀CKernel, hHNotKernel⟩

/-- Constant-coordinate specialization of the `H₀` kernel-layer result. -/
theorem pTypeNonGaloisConstantHUCharacter_mem_Iirr_kerD
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : MulChar data.H₁ ℂ) (hlambda : lambda ≠ 1),
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
      let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
      pTypeNonGaloisConstantHUCharacter
          ctx facts not_Galois lambda hlambda ∈
        Iirr_kerD (k := ℂ) H H₀ := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  exact pTypeNonGaloisHUCoordinateCharacter_mem_Iirr_kerD
    ctx facts not_Galois (fun _ ↦ lambda) (fun _ ↦ hlambda)

/-- Inducing the nested `HC` character through `HU` and then to `M` agrees
with direct induction from `HC`. -/
theorem pTypeNonGaloisHCCoordinateCharacter_induce_trans
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ lambda : W₁ → MulChar data.H₁ ℂ,
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts)
      let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
      let xi := pTypeNonGaloisHCCoordinateCharacter
        ctx facts not_Galois lambda
      ClassFunction.induce HU
          (ClassFunction.induce (HC.subgroupOf HU)
            (ClassFunction.toSubgroupOf HC HU hHC
              (xi : ClassFunction HC ℂ))) =
        ClassFunction.induce HC (xi : ClassFunction HC ℂ) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda
  exact ClassFunction.induce_trans _ _
    (pTypeNonGaloisHCInMaximal_le_HU ctx facts) _

private theorem pTypeNonGaloisHUCoordinateCharacter_ambientInduce_eq_nested
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts)
      let HCN := HC.subgroupOf HU
      ClassFunction.induce HU
          (pTypeNonGaloisHUCoordinateCharacter
            ctx facts not_Galois lambda hlambda : ClassFunction HU ℂ) =
        ClassFunction.induce HU
          (ClassFunction.induce HCN
            (pTypeNonGaloisHCCoordinateCharacterInHU
              ctx facts not_Galois lambda : ClassFunction HCN ℂ)) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
    (Ptype_factor_action ctx facts)
  let HCN := HC.subgroupOf HU
  rw [pTypeNonGaloisHUCoordinateCharacter_coe]

private theorem pTypeNonGaloisNestedHCCoordinateCharacter_induce_to_M
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ lambda : W₁ → MulChar data.H₁ ℂ,
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts)
      let HCN := HC.subgroupOf HU
      ClassFunction.induce HU
          (ClassFunction.induce HCN
            (pTypeNonGaloisHCCoordinateCharacterInHU
              ctx facts not_Galois lambda : ClassFunction HCN ℂ)) =
        ClassFunction.induce HC
          (pTypeNonGaloisHCCoordinateCharacter
            ctx facts not_Galois lambda : ClassFunction HC ℂ) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
    (Ptype_factor_action ctx facts)
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  have hNested :
      (pTypeNonGaloisHCCoordinateCharacterInHU
          ctx facts not_Galois lambda : ClassFunction HCN ℂ) =
        ClassFunction.toSubgroupOf HC HU hHC
          (pTypeNonGaloisHCCoordinateCharacter
            ctx facts not_Galois lambda : ClassFunction HC ℂ) := by
    ext x
    rw [pTypeNonGaloisHCCoordinateCharacterInHU_apply,
      ClassFunction.toSubgroupOf_apply]
  rw [hNested]
  exact ClassFunction.induce_trans HC HU
    hHC
    (pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois lambda : ClassFunction HC ℂ)

private theorem pTypeNonGaloisHUCoordinateCharacter_induce_to_M
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1),
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts)
      ClassFunction.induce HU
          (pTypeNonGaloisHUCoordinateCharacter
            ctx facts not_Galois lambda hlambda : ClassFunction HU ℂ) =
        ClassFunction.induce HC
          (pTypeNonGaloisHCCoordinateCharacter
            ctx facts not_Galois lambda : ClassFunction HC ℂ) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  exact (pTypeNonGaloisHUCoordinateCharacter_ambientInduce_eq_nested
    ctx facts not_Galois lambda hlambda).trans
    (pTypeNonGaloisNestedHCCoordinateCharacter_induce_to_M
      ctx facts not_Galois lambda)

private theorem nestedCoordinateInduce_eq_of_HCInduce_eq_constant
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (mu : MulChar data.H₁ ℂ),
      (let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
          (Ptype_factor_action ctx facts)
       ClassFunction.induce HC
            (pTypeNonGaloisHCCoordinateCharacter
              ctx facts not_Galois (fun _ ↦ mu) : ClassFunction HC ℂ) =
          ClassFunction.induce HC
            (pTypeNonGaloisHCCoordinateCharacter
              ctx facts not_Galois lambda : ClassFunction HC ℂ)) →
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
        (Ptype_factor_action ctx facts)
      let HCN := HC.subgroupOf HU
      ClassFunction.induce HCN
          (pTypeNonGaloisHCCoordinateCharacterInHU
            ctx facts not_Galois (fun _ ↦ mu) : ClassFunction HCN ℂ) =
        ClassFunction.induce HCN
          (pTypeNonGaloisHCCoordinateCharacterInHU
            ctx facts not_Galois lambda : ClassFunction HCN ℂ) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda mu heqHC
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁ D
  let hHC : HC ≤ HU := pTypeNonGaloisHCInMaximal_le_HU ctx facts
  let HCN := HC.subgroupOf HU
  letI : HCN.Normal := Subgroup.Normal.subgroupOf
    (pTypeNonGaloisHCInMaximal_normal ctx facts) HU
  let eHC : HCN ≃* HC := Subgroup.subgroupOfEquivOfLe hHC
  let xiHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter ctx facts not_Galois lambda
  let xiMuHC : IrreducibleCharacter HC ℂ :=
    pTypeNonGaloisHCCoordinateCharacter
      ctx facts not_Galois (fun _ ↦ mu)
  let xiHCN : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois lambda
  let xiMuHCN : IrreducibleCharacter HCN ℂ :=
    pTypeNonGaloisHCCoordinateCharacterInHU
      ctx facts not_Galois (fun _ ↦ mu)
  let W₁M : Subgroup M := W₁.subgroupOf M
  have houter : HU.IsComplement' W₁M :=
    ctx.typeP.1.2.2.2.2.2.2
  letI : Invertible (Nat.card HC : ℂ) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HC)).ne')
  obtain ⟨x, hxOrbit⟩ :=
    (ClassFunction.cfclass_Ind_eq_iff HC xiMuHC xiHC).mp heqHC
  obtain ⟨⟨d, wM⟩, hdw⟩ := houter.2 x
  change (d : M) * (wM : M) = x at hdw
  let w : W₁ := ⟨((wM : M) : Gamma), wM.property⟩
  have hwFixed : ClassFunction.normalConjugate HC (wM : M)
        (xiMuHC : ClassFunction HC ℂ) =
      (xiMuHC : ClassFunction HC ℂ) := by
    simpa [w] using
      (pTypeNonGaloisConstantHCCoordinateCharacter_W₁_fixed
        ctx facts not_Galois mu w)
  have hdOrbit : ClassFunction.normalConjugate HC (d : M)
        (xiMuHC : ClassFunction HC ℂ) =
      (xiHC : ClassFunction HC ℂ) := by
    calc
      ClassFunction.normalConjugate HC (d : M)
          (xiMuHC : ClassFunction HC ℂ) =
        ClassFunction.normalConjugate HC (d : M)
          (ClassFunction.normalConjugate HC (wM : M)
            (xiMuHC : ClassFunction HC ℂ)) := by rw [hwFixed]
      _ = ClassFunction.normalConjugate HC
          ((d : M) * (wM : M))
          (xiMuHC : ClassFunction HC ℂ) :=
        (ClassFunction.normalConjugate_mul HC
          (d : M) (wM : M) (xiMuHC : ClassFunction HC ℂ)).symm
      _ = ClassFunction.normalConjugate HC x
          (xiMuHC : ClassFunction HC ℂ) := by rw [hdw]
      _ = (xiHC : ClassFunction HC ℂ) := hxOrbit
  have hdOrbitNested : ClassFunction.normalConjugate HCN (d : HU)
        (xiMuHCN : ClassFunction HCN ℂ) =
      (xiHCN : ClassFunction HCN ℂ) := by
    ext y
    rw [ClassFunction.normalConjugate_apply]
    have harg : eHC ((MulAut.conjNormal (d : HU)).symm y) =
        (MulAut.conjNormal (d : M)).symm (eHC y) := by
      apply Subtype.ext
      apply Subtype.ext
      rfl
    rw [pTypeNonGaloisHCCoordinateCharacterInHU_apply,
      pTypeNonGaloisHCCoordinateCharacterInHU_apply, harg]
    have hvalue := congrArg
      (fun f : ClassFunction HC ℂ ↦ f (eHC y)) hdOrbit
    rw [ClassFunction.normalConjugate_apply] at hvalue
    exact hvalue
  calc
    ClassFunction.induce HCN (xiMuHCN : ClassFunction HCN ℂ) =
        ClassFunction.induce HCN
          (ClassFunction.normalConjugate HCN (d : HU)
            (xiMuHCN : ClassFunction HCN ℂ)) :=
      (ClassFunction.induce_normalConjugate HCN (d : HU)
        (xiMuHCN : ClassFunction HCN ℂ)).symm
    _ = ClassFunction.induce HCN
        (xiHCN : ClassFunction HCN ℂ) := by rw [hdOrbitNested]

/-- Equality of ambient inductions with a constant-coordinate character
already forces equality of the irreducible characters on `HU`. -/
theorem pTypeNonGaloisHUCoordinateCharacter_eq_constant_of_ambientInduce_eq
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : W₁ → MulChar data.H₁ ℂ)
      (hlambda : ∀ w, lambda w ≠ 1)
      (mu : MulChar data.H₁ ℂ) (hmu : mu ≠ 1),
      (let HU := pTypeHUInMaximal M (derivedWithin M)
       ClassFunction.induce HU
            (pTypeNonGaloisHUCoordinateCharacter
              ctx facts not_Galois lambda hlambda : ClassFunction HU ℂ) =
          ClassFunction.induce HU
            (pTypeNonGaloisConstantHUCharacter
              ctx facts not_Galois mu hmu : ClassFunction HU ℂ)) →
      pTypeNonGaloisHUCoordinateCharacter
          ctx facts not_Galois lambda hlambda =
        pTypeNonGaloisConstantHUCharacter
          ctx facts not_Galois mu hmu := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda mu hmu heq
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
    (Ptype_factor_action ctx facts)
  let HCN := HC.subgroupOf HU
  have heqHC : ClassFunction.induce HC
        (pTypeNonGaloisHCCoordinateCharacter
          ctx facts not_Galois (fun _ ↦ mu) : ClassFunction HC ℂ) =
      ClassFunction.induce HC
        (pTypeNonGaloisHCCoordinateCharacter
          ctx facts not_Galois lambda : ClassFunction HC ℂ) := by
    have hGenericDirect :=
      pTypeNonGaloisHUCoordinateCharacter_induce_to_M
        ctx facts not_Galois lambda hlambda
    have hConstantDirect :=
      pTypeNonGaloisHUCoordinateCharacter_induce_to_M
        ctx facts not_Galois (fun _ ↦ mu) (fun _ ↦ hmu)
    exact hConstantDirect.symm.trans (heq.symm.trans hGenericDirect)
  have hindHU : ClassFunction.induce HCN
        (pTypeNonGaloisHCCoordinateCharacterInHU
          ctx facts not_Galois (fun _ ↦ mu) : ClassFunction HCN ℂ) =
      ClassFunction.induce HCN
        (pTypeNonGaloisHCCoordinateCharacterInHU
          ctx facts not_Galois lambda : ClassFunction HCN ℂ) :=
    nestedCoordinateInduce_eq_of_HCInduce_eq_constant
      ctx facts not_Galois lambda mu heqHC
  apply Subtype.ext
  exact hindHU.symm

/-- A nonprincipal constant-coordinate irreducible character of `HU`
induces reducibly to `M`. -/
theorem pTypeNonGaloisConstantHUCoordinateCharacter_induce_reducible
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let hD := Ptype_factor_action_hypotheses ctx facts
    let data := typeP_Galois_Pn hD not_Galois
    letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
      hD.elementary.commutative
    ∀ (lambda : MulChar data.H₁ ℂ) (hlambda : lambda ≠ 1),
      let HU := pTypeHUInMaximal M (derivedWithin M)
      let family : W₁ → MulChar data.H₁ ℂ := fun _ ↦ lambda
      let hfamily : ∀ w, family w ≠ 1 := fun _ ↦ hlambda
      let xiHU := pTypeNonGaloisHUCoordinateCharacter
        ctx facts not_Galois family hfamily
      ¬ IsIrreducibleCharacter M ℂ
        (ClassFunction.induce HU (xiHU : ClassFunction HU ℂ)) := by
  let hD := Ptype_factor_action_hypotheses ctx facts
  let data := typeP_Galois_Pn hD not_Galois
  letI : IsMulCommutative (ptypeFCoreFactor ctx) :=
    hD.elementary.commutative
  dsimp only
  intro lambda hlambda
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let HC := pTypeHCInMaximal M (Fitting_core M) U W₁
    (Ptype_factor_action ctx facts)
  let family : W₁ → MulChar data.H₁ ℂ := fun _ ↦ lambda
  have hfamily : ∀ w, family w ≠ 1 := fun _ ↦ hlambda
  let xiHC := pTypeNonGaloisHCCoordinateCharacter
    ctx facts not_Galois family
  let xiHU := pTypeNonGaloisHUCoordinateCharacter
    ctx facts not_Galois family hfamily
  have hFinal : ClassFunction.induce HU
        (xiHU : ClassFunction HU ℂ) =
      ClassFunction.induce HC (xiHC : ClassFunction HC ℂ) :=
    pTypeNonGaloisHUCoordinateCharacter_induce_to_M
      ctx facts not_Galois family hfamily
  intro hirr
  apply pTypeNonGaloisConstantHCCoordinateCharacter_induce_reducible
    ctx facts not_Galois lambda
  rw [← hFinal]
  exact hirr

end PTypeNonGaloisHUFamilyInternal

end

end Submission.OddOrder.PF
