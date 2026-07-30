import Mathlib.GroupTheory.Abelianization.Finite
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.ChiefFactor
import Submission.OddOrder.MathlibSupport.NilpotentNormalCenter
import Submission.OddOrder.MathlibSupport.RepresentationModuleEquiv
import Submission.OddOrder.PF.Section01.IrreducibleDegreeQuotientBound
import Submission.OddOrder.PF.Section01.MulCharacterTwist
import Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter
import Submission.OddOrder.PF.Section05.CoherenceExtension
import Submission.OddOrder.PF.Section05.SeqIndGlobal

/-!
# Bounded coherence for induced kernel layers

This file ports the opening of `PFsection6.v`, through Peterfalvi's
Theorem (6.3).  Kernel bounds are subgroups of the normal inducing subgroup
`K`; when ambient normality is needed, it is expressed by normality of their
images under `K.subtype`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical IsMulCommutative MonoidAlgebra Pointwise

universe u

local instance boundedSeqIndCoherenceInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-- Ambient normality of the image of a subgroup of `K` supplies the
internal normality needed to form literal subgroup quotients. -/
local instance normalOfNormalMapSubtype
    {X : Type u} [Group X] {K : Subgroup X} {M : Subgroup K}
    [((M.map K.subtype : Subgroup X)).Normal] : M.Normal :=
  Subgroup.Normal.of_map_subtype inferInstance

/-! `MulCharacterTwist` currently uses one universe for both the group and
the coefficient field.  The following one-dimensional specialization keeps
the finite group in universe `u` while fixing the coefficient field to
`ℂ`. -/

private def scalarCharacterRepresentation
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
private theorem scalarCharacterRepresentation_character
    {T Q : Type u} [Group T] [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) (t : T) :
    (FDRep.of (scalarCharacterRepresentation q lambda)).character t =
      lambda (q t) := by
  change LinearMap.trace ℂ ℂ
    (lambda (q t) • LinearMap.id) = lambda (q t)
  rw [map_smul, LinearMap.trace_id]
  simp

private noncomputable def irreducibleCharacterOfMulChar
    {T Q : Type u} [Group T] [Fintype T]
    [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) :
    IrreducibleCharacter T ℂ := by
  let rho : Representation ℂ T ℂ :=
    scalarCharacterRepresentation q lambda
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
  letI : CategoryTheory.Simple V :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep V

@[simp]
private theorem irreducibleCharacterOfMulChar_apply
    {T Q : Type u} [Group T] [Fintype T]
    [Group Q] [IsMulCommutative Q]
    (q : T →* Q) (lambda : MulChar Q ℂ) (t : T) :
    irreducibleCharacterOfMulChar q lambda t = lambda (q t) := by
  change (FDRep.of
    (scalarCharacterRepresentation q lambda)).character t = _
  exact scalarCharacterRepresentation_character q lambda t

/-! Universe lifts let us use Mathlib's universe-polymorphic unbundled
induction adjunction while the chosen irreducible realizations remain in
the coefficient-field universe. -/

private def representationULift
    {T : Type u} {V : Type 0} [Monoid T]
    [AddCommMonoid V] [Module ℂ V]
    (rho : Representation ℂ T V) :
    Representation ℂ T (ULift.{u} V) :=
  (((ULift.moduleEquiv (R := ℂ) (M := V)).symm).conjRingEquiv
    ).toMonoidHom.comp rho

private def representationULiftEquiv
    {T : Type u} {V : Type 0} [Monoid T]
    [AddCommMonoid V] [Module ℂ V]
    (rho : Representation ℂ T V) :
    (representationULift rho).Equiv rho := by
  apply Representation.Equiv.mk
    (ULift.moduleEquiv (R := ℂ) (M := V))
  intro t
  ext v
  rfl

private theorem representationULift_isIrreducible
    {T : Type u} {V : Type 0} [Monoid T]
    [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ T V) [rho.IsIrreducible] :
    (representationULift rho).IsIrreducible := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact IsSimpleModule.congr
    (representationEquivLinearEquivAsModule
      (representationULiftEquiv rho))

private def intertwiningMapULift
    {T : Type u} {V W : Type 0} [Monoid T]
    [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W]
    {rho : Representation ℂ T V}
    {sigma : Representation ℂ T W}
    (f : rho.IntertwiningMap sigma) :
    (representationULift rho).IntertwiningMap
      (representationULift sigma) :=
  (representationULiftEquiv sigma).symm.toIntertwiningMap.comp
    (f.comp (representationULiftEquiv rho).toIntertwiningMap)

@[simp]
private theorem intertwiningMapULift_up
    {T : Type u} {V W : Type 0} [Monoid T]
    [AddCommMonoid V] [Module ℂ V]
    [AddCommMonoid W] [Module ℂ W]
    {rho : Representation ℂ T V}
    {sigma : Representation ℂ T W}
    (f : rho.IntertwiningMap sigma) (v : V) :
    intertwiningMapULift f (ULift.up v) = ULift.up (f v) :=
  rfl

private theorem existsNonzeroHomOfIsConstituentComplex
    {T : Type u} [Group T] [Fintype T]
    (V : FDRep ℂ T) (chi : IrreducibleCharacter T ℂ)
    (hchi : chi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    ∃ f : chi.representation ⟶ V, f ≠ 0 := by
  letI : Invertible (Fintype.card T : ℂ) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hpair :
      characterPairing (ClassFunction.ofRepresentation V.ρ)
          (chi : ClassFunction T ℂ) =
        (Module.finrank ℂ (chi.representation ⟶ V) : ℂ) := by
    have hhom :=
      FDRep.scalar_product_char_eq_finrank_equivariant
        chi.representation V
    have hcharV (t : T) :
        V.character t = Representation.character V.ρ t := rfl
    simpa only [characterPairing,
      ClassFunction.ofRepresentation_apply,
      IrreducibleCharacter.representation_character,
      invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
      hcharV] using hhom
  have hcast :
      (Module.finrank ℂ (chi.representation ⟶ V) : ℂ) ≠ 0 := by
    rw [← hpair]
    exact hchi
  have hfin : Module.finrank ℂ (chi.representation ⟶ V) ≠ 0 := by
    intro hzero
    apply hcast
    simp [hzero]
  exact Module.finrank_pos_iff_exists_ne_zero.mp
    (Nat.pos_of_ne_zero hfin)

/-- Restriction of a complex finite-dimensional representation without
identifying the universe of the coefficient field with that of the finite
group. -/
private def restrictFDRepComplex
    {T : Type u} [Group T] (C : Subgroup T) (V : FDRep ℂ T) :
    FDRep ℂ C :=
  FDRep.of (V.ρ.comp C.subtype)

/-- The character of the universe-polymorphic complex restriction is the
restriction of the original representation character. -/
private theorem ofRepresentation_restrictFDRepComplex
    {T : Type u} [Group T] (C : Subgroup T) (V : FDRep ℂ T) :
    ClassFunction.ofRepresentation (restrictFDRepComplex C V).ρ =
      ClassFunction.restrict C
        (ClassFunction.ofRepresentation V.ρ) := by
  rfl

private theorem nontrivialFDRepOfSimpleComplex
    {T : Type u} [Group T]
    (V : FDRep ℂ T) [CategoryTheory.Simple V] : Nontrivial V := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  apply CategoryTheory.id_nonzero V
  apply CategoryTheory.ConcreteCategory.hom_ext
  intro v
  change v = 0
  exact Subsingleton.elim _ _

/-! The induction adjunction used below lives in the universe of the
finite group.  Keeping the construction of its nonzero quotient map and
its dimension calculation in separate declarations both exposes the two
ingredients and keeps elaboration of the final numerical bound local. -/

private theorem existsSurjectiveInducedHomComplex
    {T : Type u} [Group T] [Fintype T]
    (C : Subgroup T) [Fintype C]
    (chi : IrreducibleCharacter T ℂ)
    (psi : IrreducibleCharacter C ℂ)
    (hpsiRes : psi.IsConstituent
      (ClassFunction.restrict C (chi : ClassFunction T ℂ))) :
    ∃ F : Rep.ind C.subtype
          (Rep.of (representationULift psi.representation.ρ)) ⟶
        Rep.of (representationULift chi.representation.ρ),
      Function.Surjective F.hom := by
  let R : FDRep ℂ C :=
    restrictFDRepComplex C chi.representation
  have hRchar : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict C (chi : ClassFunction T ℂ) := by
    calc
      ClassFunction.ofRepresentation R.ρ =
          ClassFunction.restrict C
            (ClassFunction.ofRepresentation
              chi.representation.ρ) := by
        simpa only [R] using
          ofRepresentation_restrictFDRepComplex C chi.representation
      _ = ClassFunction.restrict C
          (chi : ClassFunction T ℂ) := by
        rw [chi.ofRepresentation_representation]
  have hpsiR : psi.IsConstituent
      (ClassFunction.ofRepresentation R.ρ) := by
    rwa [hRchar]
  obtain ⟨f0, hf0⟩ :=
    existsNonzeroHomOfIsConstituentComplex R psi hpsiR
  let forgetFD := CategoryTheory.forget₂ (FDRep ℂ C) (Rep ℂ C)
  let fRep := forgetFD.map f0
  have hfRep : fRep ≠ 0 := by
    intro hzero
    apply hf0
    apply forgetFD.map_injective
    simpa [fRep] using hzero
  let fLinearR : psi.representation →ₗ[ℂ] R :=
    fRep.hom.toLinearMap
  have hfLinearR : fLinearR ≠ 0 := by
    intro hzero
    apply hfRep
    apply Rep.hom_ext
    apply Representation.IntertwiningMap.ext
    apply LinearMap.ext
    intro v
    change fLinearR v = 0
    exact LinearMap.congr_fun hzero v
  let fBaseR : Representation.IntertwiningMap
      psi.representation.ρ R.ρ :=
    fRep.hom
  let eR : R ≃ₗ[ℂ] chi.representation :=
    { toFun := fun v ↦ v
      invFun := fun v ↦ v
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  let eMap : Representation.IntertwiningMap R.ρ
      (chi.representation.ρ.comp C.subtype) :=
    { toLinearMap := eR.toLinearMap
      isIntertwining' := fun _ ↦ by
        apply LinearMap.ext
        intro v
        rfl }
  let fLinear : psi.representation →ₗ[ℂ] chi.representation :=
    eR.toLinearMap.comp fLinearR
  have hfLinear : fLinear ≠ 0 := by
    intro hzero
    apply hfLinearR
    apply LinearMap.ext
    intro v
    apply eR.injective
    have hv := LinearMap.congr_fun hzero v
    simpa [fLinear] using hv
  let fBase : Representation.IntertwiningMap
      psi.representation.ρ
      (chi.representation.ρ.comp C.subtype) :=
    eMap.comp fBaseR
  have hfBase : fBase ≠ 0 := by
    intro hzero
    apply hfLinear
    apply LinearMap.ext
    intro v
    have hv := congrArg (fun f ↦ f v) hzero
    change fLinear v = 0 at hv
    exact hv
  let fLiftBase := intertwiningMapULift fBase
  have hfLiftBase : fLiftBase ≠ 0 := by
    intro hzero
    apply hfBase
    ext v
    have hv := congrArg (fun f ↦ f (ULift.up v)) hzero
    have hv' := congrArg ULift.down hv
    simpa [fLiftBase] using hv'
  let fLiftRes : Representation.IntertwiningMap
      (representationULift psi.representation.ρ)
      ((representationULift chi.representation.ρ).comp C.subtype) :=
    { toLinearMap := fLiftBase.toLinearMap
      isIntertwining' := fun g ↦ by
        simpa only [representationULift, MonoidHom.comp_assoc] using
          fLiftBase.isIntertwining' g }
  have hfLiftRes : fLiftRes ≠ 0 := by
    intro hzero
    apply hfLiftBase
    apply Representation.IntertwiningMap.ext
    have hlinear := congrArg
      (fun f ↦ f.toLinearMap) hzero
    simpa only [fLiftRes,
      Representation.IntertwiningMap.zero_toLinearMap] using hlinear
  let ARep : Rep.{u} ℂ C :=
    Rep.of (representationULift psi.representation.ρ)
  let BRep : Rep.{u} ℂ T :=
    Rep.of (representationULift chi.representation.ρ)
  let fRes : ARep ⟶ Rep.res C.subtype BRep :=
    Rep.ofHom fLiftRes
  have hfRes : fRes ≠ 0 := by
    intro hzero
    apply hfLiftRes
    have hh := congrArg (fun f ↦ f.hom) hzero
    simpa [fRes] using hh
  let W : Rep.{u} ℂ T := Rep.ind C.subtype ARep
  let F : W ⟶ BRep :=
    (Rep.indResHomEquiv C.subtype ARep BRep).symm fRes
  have hF : F ≠ 0 := by
    intro hzero
    apply hfRes
    apply Rep.hom_ext
    have hh := congrArg
      (fun f : W ⟶ BRep ↦
        (Rep.indResHomEquiv C.subtype ARep BRep f).hom) hzero
    simpa only [F, LinearEquiv.apply_symm_apply, map_zero] using hh
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible BRep.ρ := by
    dsimp only [BRep]
    exact representationULift_isIrreducible chi.representation.ρ
  have hFrange : F.hom.range = ⊤ := by
    rcases eq_bot_or_eq_top F.hom.range with hrange | hrange
    · exfalso
      apply hF
      apply Rep.hom_ext
      apply Representation.IntertwiningMap.ext
      apply LinearMap.ext
      intro w
      have hw : F.hom w ∈ F.hom.range := ⟨w, rfl⟩
      rw [hrange] at hw
      change F.hom w = 0 at hw
      simpa using hw
    · exact hrange
  have hFsurj : Function.Surjective (F.hom : W → BRep) := by
    intro w
    apply (Representation.IntertwiningMap.mem_range
      (A := ℂ) (G := T) (V := W) (W := BRep)
      (ρ := W.ρ) (σ := BRep.ρ) F.hom w).mp
    rw [hFrange]
    trivial
  exact ⟨F, hFsurj⟩

private theorem finrankInducedULiftComplex
    {T : Type u} [Group T] [Fintype T]
    (C : Subgroup T)
    {V : Type 0} [AddCommGroup V] [Module ℂ V]
    [Module.Free ℂ V] [Module.Finite ℂ V]
    (rho : Representation ℂ C V) :
    Module.finrank ℂ
        (Rep.ind C.subtype (Rep.of (representationULift rho))) =
      C.index * Module.finrank ℂ V := by
  let ARep : Rep.{u} ℂ C := Rep.of (representationULift rho)
  let W : Rep.{u} ℂ T := Rep.ind C.subtype ARep
  letI : Fintype (InducedCharacterCompatibility.Cosets C) :=
    Fintype.ofFinite _
  let eIndCoind :
      W ≃ₗ[ℂ] Representation.coindV C.subtype ARep.ρ :=
    CategoryTheory.Iso.toLinearEquiv
      ((CategoryTheory.forget₂
          (Rep.{u} ℂ T) (ModuleCat.{u} ℂ)).mapIso
        (Rep.indCoindIso ARep))
  let eW : W ≃ₗ[ℂ]
      (InducedCharacterCompatibility.Cosets C → ULift.{u} V) :=
    eIndCoind.trans
      (InducedCharacterCompatibility.coindVEquivPi C ARep.ρ)
  letI : Module.Free ℂ W := Module.Free.of_equiv eW.symm
  letI : Module.Finite ℂ W := Module.Finite.equiv eW.symm
  change Module.finrank ℂ W = _
  calc
    Module.finrank ℂ W =
        Module.finrank ℂ
          (InducedCharacterCompatibility.Cosets C → ULift.{u} V) :=
      eW.finrank_eq
    _ = ∑ _ : InducedCharacterCompatibility.Cosets C,
        Module.finrank ℂ (ULift.{u} V) :=
      Module.finrank_pi_fintype ℂ
    _ = Fintype.card (InducedCharacterCompatibility.Cosets C) *
        Module.finrank ℂ V := by simp
    _ = C.index * Module.finrank ℂ V := by
      have hcard :
          Fintype.card (InducedCharacterCompatibility.Cosets C) =
            C.index := by
        calc
          Fintype.card (InducedCharacterCompatibility.Cosets C) =
              Nat.card (InducedCharacterCompatibility.Cosets C) :=
            Fintype.card_eq_nat_card
          _ = Nat.card (T ⧸ C) :=
            Nat.card_congr
              (QuotientGroup.quotientRightRelEquivQuotientLeftRel C)
          _ = C.index := C.index_eq_card.symm
      rw [hcard]

private theorem finrank_le_index_mul_of_isConstituent_restrictComplex
    {T : Type u} [Group T] [Fintype T]
    (C : Subgroup T) [Fintype C]
    (chi : IrreducibleCharacter T ℂ)
    (psi : IrreducibleCharacter C ℂ)
    (hpsiRes : psi.IsConstituent
      (ClassFunction.restrict C (chi : ClassFunction T ℂ))) :
    Module.finrank ℂ chi.representation ≤
      C.index * Module.finrank ℂ psi.representation := by
  obtain ⟨F, hFsurj⟩ :=
    existsSurjectiveInducedHomComplex C chi psi hpsiRes
  let ARep : Rep.{u} ℂ C :=
    Rep.of (representationULift psi.representation.ρ)
  let BRep : Rep.{u} ℂ T :=
    Rep.of (representationULift chi.representation.ρ)
  let W : Rep.{u} ℂ T := Rep.ind C.subtype ARep
  have hdegreeLift : Module.finrank ℂ BRep ≤ Module.finrank ℂ W :=
    F.hom.toLinearMap.finrank_le_finrank_of_surjective hFsurj
  calc
    Module.finrank ℂ chi.representation =
        Module.finrank ℂ BRep := by simp [BRep]
    _ ≤ Module.finrank ℂ W := hdegreeLift
    _ = C.index * Module.finrank ℂ psi.representation :=
      finrankInducedULiftComplex C psi.representation.ρ

/-! The two Section 1 degree-bound lemmas currently put the finite group
and coefficient field in one universe.  These local specializations retain
their proofs while fixing the coefficient field to `ℂ`. -/

private theorem translationKernelIrreducibleCharacterComplex
    {T : Type u} [Group T]
    (chi : IrreducibleCharacter T ℂ) :
    ClassFunction.translationKernel (chi : ClassFunction T ℂ) =
      chi.representation.ρ.ker := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker]
    let rho : Representation ℂ T chi.representation :=
      chi.representation.ρ
    letI : CategoryTheory.Simple chi.representation :=
      chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      representation_isIrreducible_of_simple_fdRep
        chi.representation
    have htraceGroup (g : T) :
        LinearMap.trace ℂ chi.representation
            ((rho a - 1) * rho g) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← rho.map_mul]
      change rho.character (a * g) - rho.character g = 0
      dsimp only [rho]
      change chi.representation.character (a * g) -
        chi.representation.character g = 0
      rw [chi.representation_character, chi.representation_character]
      exact sub_eq_zero.mpr (ha g)
    have htraceAlgebra (z : ℂ[T]) :
        LinearMap.trace ℂ chi.representation
            ((rho a - 1) * rho.asAlgebraHom z) = 0 := by
      induction z using MonoidAlgebra.induction_on with
      | hM g =>
          simpa only [Representation.asAlgebraHom_of] using
            htraceGroup g
      | hadd x y hx hy =>
          simp only [map_add, mul_add, hx, hy, add_zero]
      | hsmul c x hx =>
          simp only [map_smul, mul_smul_comm, hx, smul_zero]
    have htraceEnd (X : Module.End ℂ chi.representation) :
        LinearMap.trace ℂ chi.representation
            ((rho a - 1) * X) = 0 := by
      obtain ⟨z, rfl⟩ :=
        Representation.IsIrreducible.asAlgebraHom_surjective
          rho X
      exact htraceAlgebra z
    have hzero : rho a - 1 = 0 := by
      let b := Module.finBasis ℂ chi.representation
      apply (LinearMap.toMatrixAlgEquiv b).injective
      rw [map_zero]
      apply (Matrix.ext_iff_trace_mul_right).2
      intro X
      have hX := htraceEnd ((LinearMap.toMatrixAlgEquiv b).symm X)
      rw [LinearMap.trace_eq_matrix_trace ℂ b] at hX
      change
        ((LinearMap.toMatrixAlgEquiv b)
            ((rho a - 1) *
              (LinearMap.toMatrixAlgEquiv b).symm X)).trace = 0 at hX
      simpa only [map_mul, AlgEquiv.apply_symm_apply, Matrix.zero_mul,
        Matrix.trace_zero] using hX
    exact sub_eq_zero.mp hzero
  · intro a ha g
    rw [← chi.representation_character,
      ← chi.representation_character]
    change LinearMap.trace ℂ chi.representation
        (chi.representation.ρ (a * g)) =
      LinearMap.trace ℂ chi.representation (chi.representation.ρ g)
    rw [chi.representation.ρ.map_mul, MonoidHom.mem_ker.mp ha, one_mul]

private theorem existsRestrictionConstituentComplex
    {T : Type u} [Group T] [Fintype T]
    (C : Subgroup T) [Fintype C]
    (chi : IrreducibleCharacter T ℂ) :
    ∃ psi : IrreducibleCharacter C ℂ,
      psi.IsConstituent (ClassFunction.ofRepresentation
          (restrictFDRepComplex C chi.representation).ρ) ∧
        psi.IsConstituent
          (ClassFunction.restrict C (chi : ClassFunction T ℂ)) := by
  let R : FDRep ℂ C :=
    restrictFDRepComplex C chi.representation
  letI : Invertible (Nat.card C : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation :=
    nontrivialFDRepOfSimpleComplex chi.representation
  letI : Nontrivial R := by
    dsimp only [R, restrictFDRepComplex]
    infer_instance
  obtain ⟨psi, hpsiR⟩ :=
    ClassFunction.exists_irreducible_constituent_of_nontrivial R
  have hRchar : ClassFunction.ofRepresentation R.ρ =
      ClassFunction.restrict C (chi : ClassFunction T ℂ) := by
    calc
      ClassFunction.ofRepresentation R.ρ =
          ClassFunction.restrict C
            (ClassFunction.ofRepresentation
              chi.representation.ρ) := by
        simpa only [R] using
          ofRepresentation_restrictFDRepComplex C chi.representation
      _ = ClassFunction.restrict C
          (chi : ClassFunction T ℂ) := by
        rw [chi.ofRepresentation_representation]
  have hpsiRes : psi.IsConstituent
      (ClassFunction.restrict C (chi : ClassFunction T ℂ)) := by
    rwa [← hRchar]
  exact ⟨psi, hpsiR, hpsiRes⟩

private theorem restrictionKernelLeRestrictedComplex
    {T : Type u} [Group T] [Fintype T]
    (B C : Subgroup T) (_hBC : B ≤ C)
    (chi : IrreducibleCharacter T ℂ)
    (hBker : B ≤ ClassFunction.translationKernel
      (chi : ClassFunction T ℂ)) :
    B.subgroupOf C ≤
      (restrictFDRepComplex C chi.representation).ρ.ker := by
  have hBrep : B ≤ chi.representation.ρ.ker := by
    rw [← translationKernelIrreducibleCharacterComplex chi]
    exact hBker
  intro b hb
  rw [MonoidHom.mem_ker]
  change chi.representation.ρ ((b : C) : T) = 1
  exact MonoidHom.mem_ker.mp (hBrep hb)

private theorem kerLeIrreducibleKernelOfIsConstituentComplex
    {T : Type u} [Group T] [Fintype T]
    (V : FDRep ℂ T) (psi : IrreducibleCharacter T ℂ)
    (hpsi : psi.IsConstituent
      (ClassFunction.ofRepresentation V.ρ)) :
    V.ρ.ker ≤ psi.representation.ρ.ker := by
  obtain ⟨f, hf⟩ :=
    existsNonzeroHomOfIsConstituentComplex V psi hpsi
  letI : CategoryTheory.Simple psi.representation :=
    psi.representation_simple
  letI : CategoryTheory.Mono f :=
    CategoryTheory.mono_of_nonzero_from_simple hf
  let fR :=
    (CategoryTheory.forget₂ (FDRep ℂ T) (Rep ℂ T)).map f
  have hfR : Function.Injective fR.hom :=
    (Rep.mono_iff_injective fR).mp inferInstance
  intro g hg
  rw [MonoidHom.mem_ker]
  apply LinearMap.ext
  intro x
  apply hfR
  change fR.hom (psi.representation.ρ g x) = fR.hom x
  have hinter :=
    Representation.IntertwiningMap.isIntertwining
      (ρ := ((CategoryTheory.forget₂
        (FDRep ℂ T) (Rep ℂ T)).obj psi.representation).ρ)
      (σ := ((CategoryTheory.forget₂
        (FDRep ℂ T) (Rep ℂ T)).obj V).ρ)
      (f := fR.hom) g x
  change fR.hom (psi.representation.ρ g x) =
    V.ρ g (fR.hom x) at hinter
  have hfix : V.ρ g (fR.hom x) = fR.hom x := by
    rw [MonoidHom.mem_ker.mp hg]
    rfl
  exact hinter.trans hfix

private theorem restrictionConstituentKernelLeComplex
    {T : Type u} [Group T] [Fintype T]
    (C : Subgroup T) [Fintype C]
    (chi : IrreducibleCharacter T ℂ)
    (psi : IrreducibleCharacter C ℂ)
    (hpsiR : psi.IsConstituent (ClassFunction.ofRepresentation
      (restrictFDRepComplex C chi.representation).ρ)) :
    (restrictFDRepComplex C chi.representation).ρ.ker ≤
      psi.representation.ρ.ker := by
  exact kerLeIrreducibleKernelOfIsConstituentComplex
    (restrictFDRepComplex C chi.representation) psi hpsiR

private theorem restrictionKernelLeOfIsConstituentComplex
    {T : Type u} [Group T] [Fintype T]
    (B C : Subgroup T) (hBC : B ≤ C) [Fintype C]
    (chi : IrreducibleCharacter T ℂ)
    (psi : IrreducibleCharacter C ℂ)
    (hBker : B ≤ ClassFunction.translationKernel
      (chi : ClassFunction T ℂ))
    (hpsiR : psi.IsConstituent (ClassFunction.ofRepresentation
      (restrictFDRepComplex C chi.representation).ρ)) :
    B.subgroupOf C ≤ psi.representation.ρ.ker := by
  exact (restrictionKernelLeRestrictedComplex
    B C hBC chi hBker).trans
      (restrictionConstituentKernelLeComplex C chi psi hpsiR)

private theorem existsRestrictionConstituentKernelComplex
    {T : Type u} [Group T] [Fintype T]
    (B C : Subgroup T) (hBC : B ≤ C) [Fintype C]
    (chi : IrreducibleCharacter T ℂ)
    (hBker : B ≤ ClassFunction.translationKernel
      (chi : ClassFunction T ℂ)) :
    ∃ psi : IrreducibleCharacter C ℂ,
      psi.IsConstituent
          (ClassFunction.restrict C (chi : ClassFunction T ℂ)) ∧
        B.subgroupOf C ≤ psi.representation.ρ.ker := by
  obtain ⟨psi, hpsiR, hpsiRes⟩ :=
    existsRestrictionConstituentComplex C chi
  exact ⟨psi, hpsiRes,
    restrictionKernelLeOfIsConstituentComplex
      B C hBC chi psi hBker hpsiR⟩

private theorem existsRestrictionConstituentSqLeIndexComplex
    {T : Type u} [Group T] [Fintype T]
    (B C D : Subgroup T)
    (hBC : B ≤ C) [Fintype C]
    [hBnC : (B.subgroupOf C).Normal]
    (_hBD : B ≤ D) (_hDC : D ≤ C)
    (chi : IrreducibleCharacter T ℂ)
    (hBker : B ≤ ClassFunction.translationKernel
      (chi : ClassFunction T ℂ))
    (hcenter :
      (D.subgroupOf C).map
          (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (C ⧸ B.subgroupOf C)) :
    ∃ psi : IrreducibleCharacter C ℂ,
      psi.IsConstituent
          (ClassFunction.restrict C (chi : ClassFunction T ℂ)) ∧
        Module.finrank ℂ psi.representation ^ 2 ≤
          (D.subgroupOf C).index := by
  let K := B.subgroupOf C
  let D' := D.subgroupOf C
  obtain ⟨psi, hpsiRes, hKkerPsi⟩ :=
    existsRestrictionConstituentKernelComplex B C hBC chi hBker
  letI : CategoryTheory.Simple psi.representation :=
    psi.representation_simple
  letI : Representation.IsIrreducible psi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep
      psi.representation
  have hscalar : ∀ d : D', ∃ c : ℂ,
      psi.representation.ρ (d : C) =
        c • (1 : Module.End ℂ psi.representation) :=
    subgroup_acts_scalar_of_map_le_quotient_center
      K D' psi.representation.ρ hKkerPsi hcenter
  have hpsiSq : Module.finrank ℂ psi.representation ^ 2 ≤ D'.index :=
    Representation.IsIrreducible.finrank_sq_le_index_of_scalar_subgroup
      psi.representation.ρ D' hscalar
  exact ⟨psi, hpsiRes, hpsiSq⟩

private theorem natDegreeLeIndexMulSqrt
    {a b q d : ℕ} (hdegree : a ≤ q * b) (hsq : b ^ 2 ≤ d) :
    (a : ℝ) ≤ (q : ℝ) * Real.sqrt (d : ℝ) := by
  have hdegreeReal : (a : ℝ) ≤ (q : ℝ) * (b : ℝ) := by
    exact_mod_cast hdegree
  have hsqReal : (b : ℝ) ^ 2 ≤ (d : ℝ) := by
    exact_mod_cast hsq
  have hsqrtSq : Real.sqrt (d : ℝ) ^ 2 = (d : ℝ) :=
    Real.sq_sqrt (by positivity)
  have hbSqrt : (b : ℝ) ≤ Real.sqrt (d : ℝ) := by
    have hbNonneg : 0 ≤ (b : ℝ) := by positivity
    have hsqrtNonneg : 0 ≤ Real.sqrt (d : ℝ) := Real.sqrt_nonneg _
    nlinarith
  exact hdegreeReal.trans
    (mul_le_mul_of_nonneg_left hbSqrt (by positivity))

private theorem irr1BoundQuoComplex
    {T : Type u} [Group T] [Fintype T]
    (B C D : Subgroup T)
    (hBC : B ≤ C) [hBnC : (B.subgroupOf C).Normal]
    (hBD : B ≤ D) (hDC : D ≤ C)
    (chi : IrreducibleCharacter T ℂ)
    (hBker : B ≤ ClassFunction.translationKernel
      (chi : ClassFunction T ℂ))
    (hcenter :
      (D.subgroupOf C).map
          (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (C ⧸ B.subgroupOf C)) :
    (Module.finrank ℂ chi.representation : ℝ) ≤
      (C.index : ℝ) *
        Real.sqrt ((D.subgroupOf C).index : ℝ) := by
  letI hC : Fintype C := Fintype.ofFinite _
  obtain ⟨psi, hpsiRes, hpsiSq⟩ :=
    existsRestrictionConstituentSqLeIndexComplex
      B C D hBC hBD hDC chi hBker hcenter
  have hdegree :=
    finrank_le_index_mul_of_isConstituent_restrictComplex
      C chi psi hpsiRes
  exact natDegreeLeIndexMulSqrt hdegree hpsiSq

/-! ## A linear member of a proper solvable kernel layer -/

/-- Source `exists_linInd`.  A proper normal quotient of a finite solvable
group has a nontrivial scalar character.  Inflating it and inducing to the
ambient group produces a member of the corresponding kernel layer whose
degree is exactly the subgroup index. -/
theorem exists_linInd
    {L : Type u} [Group L] [Fintype L]
    (K : Subgroup L) [IsSolvable K]
    (M : Subgroup K) [M.Normal] (hM : M < ⊤) :
    ∃ phi : ClassFunction L ℂ,
      phi ∈ seqIndD K (⊤ : Subgroup K) M ∧
        phi 1 = (K.index : ℂ) := by
  let Q := K ⧸ M
  letI : Nontrivial Q :=
    QuotientGroup.nontrivial_iff.mpr hM.ne
  letI : Fintype Q := Fintype.ofFinite Q
  letI : IsSolvable Q := inferInstance
  have hcomm : _root_.commutator Q < (⊤ : Subgroup Q) :=
    IsSolvable.commutator_lt_top_of_nontrivial Q
  let A := Abelianization Q
  letI : Nontrivial A := by
    change Nontrivial (Q ⧸ _root_.commutator Q)
    exact QuotientGroup.nontrivial_iff.mpr hcomm.ne
  letI : Fintype A := Fintype.ofFinite A
  obtain ⟨a, ha⟩ := exists_ne (1 : A)
  obtain ⟨lambda : MulChar A ℂ, hlambda⟩ :=
    MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity A ℂ ha
  obtain ⟨q, rfl⟩ :=
    QuotientGroup.mk'_surjective (_root_.commutator Q) a
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective M q
  let pi : K →* A :=
    Abelianization.of.comp (QuotientGroup.mk' M)
  let chi : IrreducibleCharacter K ℂ :=
    irreducibleCharacterOfMulChar pi lambda
  let phi : ClassFunction L ℂ :=
    ClassFunction.induce K (chi : ClassFunction K ℂ)
  have hMker :
      M ≤ ClassFunction.translationKernel
        (chi : ClassFunction K ℂ) := by
    intro m hm y
    simp only [chi, irreducibleCharacterOfMulChar_apply, map_mul]
    have hpi : pi m = 1 := by
      simp only [pi, MonoidHom.coe_comp, Function.comp_apply]
      rw [show QuotientGroup.mk' M m = 1 from
        (QuotientGroup.eq_one_iff m).mpr hm, map_one]
    rw [hpi, map_one, one_mul]
  have htopKer :
      ¬(⊤ : Subgroup K) ≤
        ClassFunction.translationKernel (chi : ClassFunction K ℂ) := by
    intro htop
    have hx := htop (show x ∈ (⊤ : Subgroup K) by trivial) 1
    simp only [chi, irreducibleCharacterOfMulChar_apply, mul_one] at hx
    have hpix :
        pi x = (QuotientGroup.mk' (_root_.commutator Q)
          (QuotientGroup.mk' M x) : A) := by
      change Abelianization.of (QuotientGroup.mk' M x) =
        QuotientGroup.mk' (_root_.commutator Q)
          (QuotientGroup.mk' M x)
      exact (Abelianization.mk_eq_of _).symm
    apply hlambda
    rw [← hpix]
    simpa only [map_one] using hx
  refine ⟨phi, ?_, ?_⟩
  · apply seqIndP.mpr
    refine ⟨chi, ?_, rfl⟩
    rw [mem_Iirr_kerD]
    exact ⟨hMker, htopKer⟩
  · simp only [phi, ClassFunction.induce_one,
      chi, irreducibleCharacterOfMulChar_apply, map_one, mul_one]

/-! ## Peterfalvi (6.2) -/

/-- Source `coherent_seqIndD_bound`, Peterfalvi (6.2).  Starting with a
coherent upper kernel layer, either the lower layer is coherent as well or
the indicated subgroup-index bound holds. -/
theorem coherent_seqIndD_bound
    {L G : Type u} [Group L] [Fintype L] [Group G] [Fintype G]
    (K : Subgroup L) [K.Normal] [IsSolvable K]
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ))
    (hsub : subcoherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) :
        Set (ClassFunction L ℂ))
      tau R)
    (A B C D : Subgroup K)
    [((A.map K.subtype : Subgroup L)).Normal]
    [((B.map K.subtype : Subgroup L)).Normal]
    [((C.map K.subtype : Subgroup L)).Normal]
    [((D.map K.subtype : Subgroup L)).Normal]
    (hAK : A < ⊤) (hBD : B ≤ D) (hDC : D ≤ C)
    (hcenter :
      (D.subgroupOf C).map
          (QuotientGroup.mk' (B.subgroupOf C)) ≤
        Subgroup.center (C ⧸ B.subgroupOf C))
    (hcohA : coherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) A) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) tau) :
    coherent
        (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) B) :
          Set (ClassFunction L ℂ))
        (nonidentitySet L) tau ∨
      (A.index : ℝ) - 1 ≤
        2 * ((C.map K.subtype : Subgroup L).index : ℝ) *
          Real.sqrt ((D.subgroupOf C).index : ℝ) := by
  classical
  let calS : Set (ClassFunction L ℂ) :=
    ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥)
  let SA : Set (ClassFunction L ℂ) :=
    ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) A)
  let SB : Set (ClassFunction L ℂ) :=
    ↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) B)
  letI : A.Normal := Subgroup.Normal.of_map_subtype
    (inferInstance : (A.map K.subtype : Subgroup L).Normal)
  letI : B.Normal := Subgroup.Normal.of_map_subtype
    (inferInstance : (B.map K.subtype : Subgroup L).Normal)
  letI : C.Normal := Subgroup.Normal.of_map_subtype
    (inferInstance : (C.map K.subtype : Subgroup L).Normal)
  letI : D.Normal := Subgroup.Normal.of_map_subtype
    (inferInstance : (D.map K.subtype : Subgroup L).Normal)
  letI : (B.subgroupOf C).Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : B.Normal) C
  letI : (((⊤ : Subgroup K).map K.subtype : Subgroup L)).Normal := by
    rw [← MonoidHom.range_eq_map, K.range_subtype]
    infer_instance
  have hSAcal : SA ⊆ calS := by
    exact seqInd_sub K (⊤ : Subgroup K) A
  have hSBcal : SB ⊆ calS := by
    exact seqInd_sub K (⊤ : Subgroup K) B
  have hSAclosed : cfConjC_closed SA := by
    intro phi hphi
    exact seqInd_inverse_mem K (⊤ : Subgroup K) A hphi
  have hSAcf : cfConjC_subset SA calS := ⟨hSAcal, hSAclosed⟩
  have hweightRe
      {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      coherenceDegreeWeight xi =
        Complex.re (xi 1 ^ 2 / characterPairing xi xi) := by
    obtain ⟨d, hd⟩ := Cnat_seqInd1 K hxi
    obtain ⟨n, hn⟩ :=
      (hsub.source_character xi hxi).isVirtual.exists_nat_norm
    rw [coherenceDegreeWeight, hd, hn]
    norm_num [pow_two, Complex.mul_re]
  have hweightNonneg
      {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      0 ≤ coherenceDegreeWeight xi := by
    obtain ⟨d, hd⟩ :=
      (hsub.source_character xi hxi).exists_nat_degree
    obtain ⟨n, hn⟩ :=
      (hsub.source_character xi hxi).isVirtual.exists_nat_norm
    have hn0 : n ≠ 0 := by
      intro hnzero
      have hzero : characterPairing xi xi = 0 := by
        rw [hn, hnzero]
        simp
      exact (cfnorm_seqInd_neq0 K hxi) hzero
    rw [coherenceDegreeWeight, hd, hn]
    norm_num
    exact div_nonneg (sq_nonneg (d : ℝ)) (Nat.cast_nonneg n)
  have hsumA :
      coherenceDegreeSum SA (hsub.finite.subset hSAcal) =
        (K.index : ℝ) * ((A.index : ℝ) - 1) := by
    let hfin : SA.Finite := hsub.finite.subset hSAcal
    have hto : hfin.toFinset = seqIndD K (⊤ : Subgroup K) A := by
      ext xi
      simp [SA]
    rw [coherenceDegreeSum, hto]
    have hsumComplex :=
      sum_seqIndD_square (k := ℂ) K (⊤ : Subgroup K) A le_top
    have hsumReal := congrArg Complex.re hsumComplex
    simp only [Complex.mul_re, Complex.natCast_re,
      Complex.natCast_im, zero_mul, sub_zero] at hsumReal
    calc
      ∑ xi ∈ seqIndD K (⊤ : Subgroup K) A,
          coherenceDegreeWeight xi =
          ∑ xi ∈ seqIndD K (⊤ : Subgroup K) A,
            Complex.re (xi 1 ^ 2 / characterPairing xi xi) := by
              apply Finset.sum_congr rfl
              intro xi hxi
              exact hweightRe (hSAcal hxi)
      _ = (K.index : ℝ) * ((A.index : ℝ) - 1) := by
        simpa using hsumReal
  by_cases hcohB : coherent SB (nonidentitySet L) tau
  · exact Or.inl hcohB
  right
  by_contra hbound
  have hlarge :
      2 * ((C.map K.subtype : Subgroup L).index : ℝ) *
          Real.sqrt ((D.subgroupOf C).index : ℝ) <
        (A.index : ℝ) - 1 :=
    lt_of_not_ge hbound
  apply hcohB
  obtain ⟨phi, hphiA, hphi1⟩ := exists_linInd K A hAK
  have hphiCal : phi ∈ calS := hSAcal hphiA
  have hbuild : ∀ T : Finset (ClassFunction L ℂ),
      T ⊆ seqIndD K (⊤ : Subgroup K) B →
      ∃ S1 : Set (ClassFunction L ℂ),
        cfConjC_subset S1 calS ∧ SA ⊆ S1 ∧
          (↑T : Set (ClassFunction L ℂ)) ⊆ S1 ∧
          coherent S1 (nonidentitySet L) tau := by
    intro T hTB
    induction T using Finset.induction_on with
    | empty =>
        exact ⟨SA, hSAcf, fun _ h ↦ h, by simp, hcohA⟩
    | @insert psi T hpsiT ih =>
        have hpsiB : psi ∈ seqIndD K (⊤ : Subgroup K) B :=
          hTB (Finset.mem_insert_self psi T)
        have hTB' : T ⊆ seqIndD K (⊤ : Subgroup K) B := by
          intro xi hxi
          exact hTB (Finset.mem_insert_of_mem hxi)
        obtain ⟨S1, hS1cf, hAS1, hTS1, hcoh1⟩ := ih hTB'
        by_cases hpsi1 : psi ∈ S1
        · refine ⟨S1, hS1cf, hAS1, ?_, hcoh1⟩
          intro xi hxi
          rcases Finset.mem_insert.mp hxi with rfl | hxi
          · exact hpsi1
          · exact hTS1 hxi
        · have hpsiCal : psi ∈ calS := hSBcal hpsiB
          let S2 : Set (ClassFunction L ℂ) :=
            {psi, ClassFunction.inverseLinear psi} ∪ S1
          have hS2sub : S2 ⊆ calS := by
            intro xi hxi
            rcases hxi with hxi | hxi
            · rcases hxi with rfl | rfl
              · exact hpsiCal
              · exact hsub.inverse_mem psi hpsiCal
            · exact hS1cf.1 hxi
          have hS2closed : cfConjC_closed S2 := by
            intro xi hxi
            rcases hxi with hxi | hxi
            · rcases hxi with rfl | rfl
              · exact Or.inl (Or.inr rfl)
              · left
                left
                ext x
                simp
            · exact Or.inr (hS1cf.2 xi hxi)
          have hS2cf : cfConjC_subset S2 calS :=
            ⟨hS2sub, hS2closed⟩
          obtain ⟨chi, hchi, hpsi⟩ := seqIndP.mp hpsiB
          have hdiv : ∃ a : ℕ, psi 1 = (a : ℂ) * phi 1 := by
            refine ⟨Module.finrank ℂ chi.representation, ?_⟩
            rw [hpsi, ClassFunction.induce_one,
              IrreducibleCharacter.apply_one_eq_finrank, hphi1]
            ring
          have hirr :
              (Module.finrank ℂ chi.representation : ℝ) ≤
                (C.index : ℝ) *
                  Real.sqrt ((D.subgroupOf C).index : ℝ) := by
            exact irr1BoundQuoComplex B C D
              (hBD.trans hDC) hBD hDC chi
              (mem_Iirr_kerD.mp hchi).1 hcenter
          have hcore :
              2 * (K.index : ℝ) *
                  (Module.finrank ℂ chi.representation : ℝ) <
                (A.index : ℝ) - 1 := by
            calc
              2 * (K.index : ℝ) *
                    (Module.finrank ℂ chi.representation : ℝ) ≤
                  2 * (K.index : ℝ) *
                    ((C.index : ℝ) *
                      Real.sqrt ((D.subgroupOf C).index : ℝ)) := by
                        gcongr
              _ = 2 * ((C.map K.subtype : Subgroup L).index : ℝ) *
                    Real.sqrt ((D.subgroupOf C).index : ℝ) := by
                      rw [Subgroup.index_map_subtype, Nat.cast_mul]
                      ring
              _ < (A.index : ℝ) - 1 := hlarge
          have hdegreeSmall :
              2 * (psi 1).re * (phi 1).re <
                (K.index : ℝ) * ((A.index : ℝ) - 1) := by
            have hKindexPos : 0 < (K.index : ℝ) := by
              exact_mod_cast
                Nat.pos_of_ne_zero K.index_ne_zero_of_finite
            have hscaled := mul_lt_mul_of_pos_left hcore
              hKindexPos
            rw [hpsi, ClassFunction.induce_one,
              IrreducibleCharacter.apply_one_eq_finrank, hphi1]
            norm_num at hscaled ⊢
            nlinarith
          have hsumMono :
              coherenceDegreeSum SA (hsub.finite.subset hSAcal) ≤
                coherenceDegreeSum S1
                  (hsub.finite.subset hS1cf.1) := by
            unfold coherenceDegreeSum
            apply Finset.sum_le_sum_of_subset_of_nonneg
              ((hsub.finite.subset hSAcal).toFinset_mono hAS1)
            intro xi hxi _
            apply hweightNonneg
            exact hS1cf.1
              ((hsub.finite.subset hS1cf.1).mem_toFinset.mp hxi)
          have hextBound :
              2 * (psi 1).re * (phi 1).re <
                coherenceDegreeSum S1
                  (hsub.finite.subset hS1cf.1) := by
            calc
              2 * (psi 1).re * (phi 1).re <
                  coherenceDegreeSum SA
                    (hsub.finite.subset hSAcal) := by
                      rw [hsumA]
                      exact hdegreeSmall
              _ ≤ coherenceDegreeSum S1
                    (hsub.finite.subset hS1cf.1) := hsumMono
          have hcoh2 : coherent S2 (nonidentitySet L) tau := by
            exact extend_coherent hsub hS1cf (hAS1 hphiA) hpsiCal
              hpsi1 hcoh1 hdiv hextBound
          refine ⟨S2, hS2cf, ?_, ?_, hcoh2⟩
          · intro xi hxi
            exact Or.inr (hAS1 hxi)
          · intro xi hxi
            rcases Finset.mem_insert.mp hxi with rfl | hxi
            · exact Or.inl (Or.inl rfl)
            · exact Or.inr (hTS1 hxi)
  obtain ⟨S1, _, _, hBS1, hcoh1⟩ :=
    hbuild (seqIndD K (⊤ : Subgroup K) B) (fun _ h ↦ h)
  exact subset_coherent hBS1 hcoh1

/-! ## The maximal normal step used in Peterfalvi (6.3) -/

/-- A maximal proper ambient-normal subgroup gives a chief factor.  The
maximality formulation is convenient here because the lower subgroup is
chosen inside `A`, rather than the upper subgroup being chosen above a fixed
lower one. -/
private theorem isChiefFactor_of_maximal_normal
    {X : Type u} [Group X] [Finite X]
    {B A : Subgroup X}
    (hAnormal : A.Normal) (hBA : B < A)
    (hBnormal : B.Normal)
    (hmax : ∀ N : Subgroup X,
      N.Normal → N < A → B ≤ N → N ≤ B) :
    @IsChiefFactor X _ B A hBnormal := by
  letI : B.Normal := hBnormal
  let q : X →* X ⧸ B := QuotientGroup.mk' B
  have hqsurj : Function.Surjective q :=
    QuotientGroup.mk'_surjective B
  refine ⟨hBA.le, hAnormal, ?_⟩
  refine ⟨?_, Subgroup.Normal.map hAnormal q hqsurj, ?_⟩
  · intro hmap
    have hAB : A ≤ B := by
      have hker : A ≤ q.ker :=
        (Subgroup.map_eq_bot_iff A).mp hmap
      simpa [q, QuotientGroup.ker_mk'] using hker
    exact (not_le_of_gt hBA) hAB
  · intro N hNnormal hNA hNne
    let D : Subgroup X := N.comap q
    have hDnormal : D.Normal := by
      dsimp [D]
      exact Subgroup.Normal.comap hNnormal q
    have hBD : B ≤ D := by
      dsimp [D, q]
      exact QuotientGroup.le_comap_mk' B N
    have hDA : D ≤ A := by
      have hkerA : q.ker ≤ A := by
        simpa [q, QuotientGroup.ker_mk'] using hBA.le
      calc
        D ≤ (A.map q).comap q := Subgroup.comap_mono hNA
        _ = A := Subgroup.comap_map_eq_self hkerA
    by_contra hAN
    have hnotAD : ¬ A ≤ D := by
      intro hAD
      apply hAN
      exact Subgroup.map_le_iff_le_comap.mpr hAD
    have hDltA : D < A :=
      lt_of_le_of_ne hDA (fun hDA' ↦ hnotAD hDA'.ge)
    have hDB : D ≤ B := hmax D hDnormal hDltA hBD
    have hDB_eq : D = B := le_antisymm hDB hBD
    apply hNne
    calc
      N = D.map q :=
        (Subgroup.map_comap_eq_self_of_surjective hqsurj N).symm
      _ = B.map q := congrArg (fun Y : Subgroup X ↦ Y.map q) hDB_eq
      _ = ⊥ := QuotientGroup.map_mk'_self B

/-- In a nilpotent normal overgroup, the upper member of an ambient chief
factor is central modulo its lower member.  This is the minimal-normal/
nontrivial-center argument in the middle of Peterfalvi (6.3). -/
private theorem chiefFactor_le_center_of_nilpotent
    {X : Type u} [Group X] [Finite X]
    {B A H : Subgroup X} [B.Normal]
    (hchief : IsChiefFactor B A)
    (hAH : A ≤ H) (hHnormal : H.Normal)
    (hnil : Group.IsNilpotent (H ⧸ B.subgroupOf H)) :
    (A.subgroupOf H).map
        (QuotientGroup.mk' (B.subgroupOf H)) ≤
      Subgroup.center (H ⧸ B.subgroupOf H) := by
  classical
  let q : X →* X ⧸ B := QuotientGroup.mk' B
  let Hq : Subgroup (X ⧸ B) := H.map q
  let Aq : Subgroup (X ⧸ B) := A.map q
  have hAqHq : Aq ≤ Hq := Subgroup.map_mono hAH
  letI : Hq.Normal :=
    Subgroup.Normal.map hHnormal q (QuotientGroup.mk'_surjective B)
  letI : Aq.Normal :=
    Subgroup.Normal.map hchief.upper_normal q
      (QuotientGroup.mk'_surjective B)
  let eH : (H ⧸ B.subgroupOf H) ≃* Hq :=
    ClassFunction.subgroupQuotientEquivImage B H
      (hchief.le.trans hAH)
  letI : Group.IsNilpotent Hq := by
    letI : Group.IsNilpotent (H ⧸ B.subgroupOf H) := hnil
    exact Group.nilpotent_of_mulEquiv eH
  let AHq : Subgroup Hq := Aq.subgroupOf Hq
  letI : AHq.Normal :=
    Subgroup.Normal.subgroupOf (inferInstance : Aq.Normal) Hq
  have hAHqne : AHq ≠ ⊥ := by
    intro hbot
    apply hchief.quotient_minimal_normal.ne_bot
    have hmapped := congrArg
      (fun Y : Subgroup Hq ↦ Y.map Hq.subtype) hbot
    simpa [AHq, Aq, q,
      Subgroup.map_subgroupOf_eq_of_le hAqHq] using hmapped
  let Zq : Subgroup (X ⧸ B) :=
    (Subgroup.center Hq).map Hq.subtype
  have hZqnormal : Zq.Normal := by
    constructor
    intro z hz x
    exact characteristic_map_subtype_invariant_under_normalizer
      Hq ⊤ (Subgroup.center Hq) (by
        rw [Hq.normalizer_eq_top]) x trivial z hz
  letI : Zq.Normal := hZqnormal
  let Cq : Subgroup (X ⧸ B) := Aq ⊓ Zq
  letI : Cq.Normal := by
    dsimp [Cq]
    infer_instance
  let Mq : Subgroup Hq := AHq ⊓ Subgroup.center Hq
  have hMqne : Mq ≠ ⊥ := by
    dsimp [Mq]
    exact nilpotent_normal_inf_center_ne_bot AHq hAHqne
  have hmapMq : Mq.map Hq.subtype = Cq := by
    dsimp [Mq, Cq, Zq, AHq]
    rw [Subgroup.map_inf _ _ _ Hq.subtype_injective,
      Subgroup.map_subgroupOf_eq_of_le hAqHq]
  have hCqne : Cq ≠ ⊥ := by
    rw [← hmapMq]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      Mq Hq.subtype_injective)).mpr hMqne
  have hCqAq : Cq = Aq :=
    hchief.quotient_minimal_normal.eq_of_normal_le
      (inferInstance : Cq.Normal) inf_le_left hCqne
  have hAqZq : Aq ≤ Zq := by
    rw [← hCqAq]
    exact inf_le_right
  intro x hx
  have hexAq : (eH x : X ⧸ B) ∈ Aq := by
    rcases hx with ⟨a, ha, rfl⟩
    change q (a : X) ∈ Aq
    exact ⟨(a : X), ha, rfl⟩
  have hexCenter : eH x ∈ Subgroup.center Hq := by
    have hxZ := hAqZq hexAq
    change (eH x : X ⧸ B) ∈
      (Subgroup.center Hq).map Hq.subtype at hxZ
    rcases hxZ with ⟨z, hz, hzx⟩
    have hzx' : z = eH x := Subtype.ext hzx
    rwa [← hzx']
  rw [Subgroup.mem_center_iff] at hexCenter ⊢
  intro y
  apply eH.injective
  simpa only [map_mul] using hexCenter (eH y)

/-! ## Peterfalvi (6.3) -/

/-- Source `bounded_seqIndD_coherence`, Peterfalvi (6.3).  A sufficiently
large nilpotent section lets coherence descend all the way from `H1` to
`M`. -/
theorem bounded_seqIndD_coherence
    {L G : Type u} [Group L] [Fintype L] [Group G] [Fintype G]
    (K : Subgroup L) [K.Normal] [IsSolvable K]
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ))
    (hsub : subcoherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) ⊥) :
        Set (ClassFunction L ℂ))
      tau R)
    (M H1 H : Subgroup K)
    [((M.map K.subtype : Subgroup L)).Normal]
    [((H1.map K.subtype : Subgroup L)).Normal]
    [((H.map K.subtype : Subgroup L)).Normal]
    (hMH1 : M ≤ H1) (hH1H : H1 ≤ H)
    (hnil : Group.IsNilpotent (H ⧸ M.subgroupOf H))
    (hcoh : coherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) H1) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) tau)
    (hlarge : 4 * K.index ^ 2 + 1 < H1.relIndex H) :
    coherent
      (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) M) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) tau := by
  classical
  let P : ℕ → Prop := fun n ↦
    ∀ A : Subgroup K, Nat.card A = n →
      ∀ hAnormal : (A.map K.subtype : Subgroup L).Normal,
      M ≤ A → A ≤ H →
      coherent
        (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) A) :
          Set (ClassFunction L ℂ))
        (nonidentitySet L) tau →
      4 * K.index ^ 2 + 1 < A.relIndex H →
      coherent
        (↑(seqIndD (k := ℂ) K (⊤ : Subgroup K) M) :
          Set (ClassFunction L ℂ))
        (nonidentitySet L) tau
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        intro A hcardA hAnormal hMA hAH hcohA hlargeA
        letI : (A.map K.subtype : Subgroup L).Normal := hAnormal
        by_cases hAM : A = M
        · subst A
          exact hcohA
        have hMAproper : M < A :=
          lt_of_le_of_ne hMA (Ne.symm hAM)
        have hAneH : A ≠ H := by
          intro hAH'
          subst A
          simp at hlargeA
        have hAHproper : A < H :=
          lt_of_le_of_ne hAH hAneH
        have hAtop : A < (⊤ : Subgroup K) :=
          hAHproper.trans_le le_top

        let ML : Subgroup L := M.map K.subtype
        let AL : Subgroup L := A.map K.subtype
        let HL : Subgroup L := H.map K.subtype
        letI : ML.Normal :=
          (inferInstance : (M.map K.subtype : Subgroup L).Normal)
        letI : AL.Normal := hAnormal
        letI : HL.Normal :=
          (inferInstance : (H.map K.subtype : Subgroup L).Normal)
        have hMLAL : ML < AL := by
          exact (Subgroup.map_lt_map_iff_of_injective
            K.subtype_injective).2 hMAproper
        let Good : Subgroup L → Prop := fun N ↦
          N.Normal ∧ ML ≤ N ∧ N < AL
        have hMLGood : Good ML :=
          ⟨inferInstance, le_rfl, hMLAL⟩
        obtain ⟨BL, hMLBL, hBLgood, hBLmax⟩ :=
          Finite.exists_le_maximal (p := Good) hMLGood
        letI : BL.Normal := hBLgood.1
        have hBLAL : BL < AL := hBLgood.2.2
        have hBLK : BL ≤ (K : Subgroup L) :=
          hBLAL.le.trans (Subgroup.map_subtype_le A)
        let B : Subgroup K := BL.subgroupOf K
        have hBmap : B.map K.subtype = BL := by
          exact Subgroup.map_subgroupOf_eq_of_le hBLK
        have hMB : M ≤ B := by
          rw [← Subgroup.map_subtype_le_map_subtype, hBmap]
          exact hMLBL
        have hBA : B < A := by
          rw [← Subgroup.map_subtype_lt_map_subtype, hBmap]
          exact hBLAL
        letI : (B.map K.subtype : Subgroup L).Normal := by
          rw [hBmap]
          infer_instance
        letI : B.Normal := Subgroup.Normal.of_map_subtype
          (inferInstance : (B.map K.subtype : Subgroup L).Normal)
        have hchiefBL : IsChiefFactor BL AL :=
          isChiefFactor_of_maximal_normal
            (inferInstance : AL.Normal) hBLAL
            (inferInstance : BL.Normal)
            (fun N hNnormal hNlt hBLN ↦
              hBLmax ⟨hNnormal, hMLBL.trans hBLN, hNlt⟩ hBLN)

        have hBLHL : BL ≤ HL :=
          hBLAL.le.trans (Subgroup.map_mono hAH)
        letI : (BL.subgroupOf HL).Normal :=
          Subgroup.Normal.subgroupOf
            (inferInstance : BL.Normal) HL
        let eH0 : H →* HL := K.subtype.subgroupMap H
        let qHL : HL →* HL ⧸ BL.subgroupOf HL :=
          QuotientGroup.mk' (BL.subgroupOf HL)
        let f0 : H →* HL ⧸ BL.subgroupOf HL :=
          qHL.comp eH0
        have hf0 : Function.Surjective f0 :=
          (QuotientGroup.mk'_surjective (BL.subgroupOf HL)).comp
            (K.subtype.subgroupMap_surjective H)
        letI : M.Normal := Subgroup.Normal.of_map_subtype
          (inferInstance : (M.map K.subtype : Subgroup L).Normal)
        letI : (M.subgroupOf H).Normal :=
          Subgroup.Normal.subgroupOf (inferInstance : M.Normal) H
        have hMker : M.subgroupOf H ≤ f0.ker := by
          intro m hm
          change qHL (eH0 m) = 1
          apply (QuotientGroup.eq_one_iff (eH0 m)).mpr
          change ((m : K) : L) ∈ BL
          apply hMLBL
          exact ⟨(m : K), hm, rfl⟩
        let f : (H ⧸ M.subgroupOf H) →*
            (HL ⧸ BL.subgroupOf HL) :=
          QuotientGroup.lift (M.subgroupOf H) f0 hMker
        have hf : Function.Surjective f :=
          QuotientGroup.lift_surjective_of_surjective
            (M.subgroupOf H) f0 hf0 hMker
        have hnilHL : Group.IsNilpotent
            (HL ⧸ BL.subgroupOf HL) := by
          letI : Group.IsNilpotent (H ⧸ M.subgroupOf H) := hnil
          exact Group.nilpotent_of_surjective f hf
        have hcenterL :
            (AL.subgroupOf HL).map
                (QuotientGroup.mk' (BL.subgroupOf HL)) ≤
              Subgroup.center (HL ⧸ BL.subgroupOf HL) :=
          chiefFactor_le_center_of_nilpotent hchiefBL
            (Subgroup.map_mono hAH)
            (inferInstance : HL.Normal) hnilHL

        have hBH : B ≤ H := hBA.le.trans hAH
        letI : (B.subgroupOf H).Normal :=
          Subgroup.Normal.subgroupOf (inferInstance : B.Normal) H
        let eH : H ≃* HL :=
          H.equivMapOfInjective K.subtype K.subtype_injective
        have hBquotMap :
            (B.subgroupOf H).map eH.toMonoidHom =
              BL.subgroupOf HL := by
          apply Subgroup.map_injective HL.subtype_injective
          calc
            ((B.subgroupOf H).map eH.toMonoidHom).map HL.subtype =
                ((B.subgroupOf H).map H.subtype).map K.subtype := by
                  rw [Subgroup.map_map, Subgroup.map_map]
                  apply congrArg
                  ext x
                  rfl
            _ = B.map K.subtype := by
              rw [Subgroup.map_subgroupOf_eq_of_le hBH]
            _ = BL := hBmap
            _ = (BL.subgroupOf HL).map HL.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hBLHL).symm
        let eQ : (H ⧸ B.subgroupOf H) ≃*
            (HL ⧸ BL.subgroupOf HL) :=
          QuotientGroup.congr (B.subgroupOf H) (BL.subgroupOf HL)
            eH hBquotMap
        have hcenter :
            (A.subgroupOf H).map
                (QuotientGroup.mk' (B.subgroupOf H)) ≤
              Subgroup.center (H ⧸ B.subgroupOf H) := by
          intro x hx
          rcases hx with ⟨a, ha, rfl⟩
          have haL : eH a ∈ AL.subgroupOf HL := by
            change ((a : K) : L) ∈ AL
            exact ⟨(a : K), ha, rfl⟩
          have hqaL :
              QuotientGroup.mk' (BL.subgroupOf HL) (eH a) ∈
                (AL.subgroupOf HL).map
                  (QuotientGroup.mk' (BL.subgroupOf HL)) :=
            ⟨eH a, haL, rfl⟩
          have hcentralL := hcenterL hqaL
          rw [Subgroup.mem_center_iff] at hcentralL ⊢
          intro y
          apply eQ.injective
          simpa [eQ] using hcentralL (eQ y)

        rcases coherent_seqIndD_bound K tau R hsub A B H A
            hAtop hBA.le hAH hcenter hcohA with hcohB | hub
        · have hcardBA : Nat.card B < n := by
            rw [← hcardA]
            simpa using
              (Set.toFinite (A : Set K)).card_lt_card hBA
          have hrelBA : A.relIndex H ≤ B.relIndex H :=
            Subgroup.relIndex_le_of_le_left hBA.le
              (B.subgroupOf H).index_ne_zero_of_finite
          exact ih (Nat.card B) hcardBA B rfl
            (inferInstance : (B.map K.subtype : Subgroup L).Normal)
            hMB hBH hcohB (hlargeA.trans_le hrelBA)
        · have hub' :
              (A.relIndex H : ℝ) * (H.index : ℝ) - 1 ≤
                2 * (K.index : ℝ) * (H.index : ℝ) *
                  Real.sqrt (A.relIndex H : ℝ) := by
            rw [← A.relIndex_mul_index hAH, Nat.cast_mul] at hub
            rw [Subgroup.index_map_subtype, Nat.cast_mul] at hub
            change
              ((A.subgroupOf H).index : ℝ) * (H.index : ℝ) - 1 ≤
                2 * (K.index : ℝ) * (H.index : ℝ) *
                  Real.sqrt ((A.subgroupOf H).index : ℝ)
            simp only [Subgroup.relIndex] at hub
            convert hub using 1
            all_goals ring
          have hqNat : 0 < H.index :=
            Nat.pos_of_ne_zero H.index_ne_zero_of_finite
          have hqOne : (1 : ℝ) ≤ (H.index : ℝ) := by
            exact_mod_cast hqNat
          have hqPos : (0 : ℝ) < (H.index : ℝ) := by
            exact_mod_cast hqNat
          have hscaled :
              (H.index : ℝ) * ((A.relIndex H : ℝ) - 1) ≤
                (H.index : ℝ) *
                  (2 * (K.index : ℝ) *
                    Real.sqrt (A.relIndex H : ℝ)) := by
            calc
              (H.index : ℝ) * ((A.relIndex H : ℝ) - 1) ≤
                  (A.relIndex H : ℝ) * (H.index : ℝ) - 1 := by
                    nlinarith [hqOne]
              _ ≤ 2 * (K.index : ℝ) * (H.index : ℝ) *
                    Real.sqrt (A.relIndex H : ℝ) := hub'
              _ = (H.index : ℝ) *
                    (2 * (K.index : ℝ) *
                      Real.sqrt (A.relIndex H : ℝ)) := by ring
          have hsmall :
              (A.relIndex H : ℝ) - 1 ≤
                2 * (K.index : ℝ) *
                  Real.sqrt (A.relIndex H : ℝ) :=
            (mul_le_mul_iff_right₀ hqPos).mp hscaled
          have hlargeR :
              (4 : ℝ) * (K.index : ℝ) ^ 2 + 2 ≤
                (A.relIndex H : ℝ) := by
            exact_mod_cast Nat.succ_le_of_lt hlargeA
          have hrNonneg : (0 : ℝ) ≤ (A.relIndex H : ℝ) := by
            positivity
          have hrOne : (1 : ℝ) ≤ (A.relIndex H : ℝ) := by
            nlinarith [hlargeR, sq_nonneg (K.index : ℝ)]
          have hsqrtNonneg :
              (0 : ℝ) ≤ Real.sqrt (A.relIndex H : ℝ) :=
            Real.sqrt_nonneg _
          have hrightNonneg :
              (0 : ℝ) ≤ 2 * (K.index : ℝ) *
                Real.sqrt (A.relIndex H : ℝ) := by
            positivity
          have hsquare :
              ((A.relIndex H : ℝ) - 1) ^ 2 ≤
                (2 * (K.index : ℝ) *
                  Real.sqrt (A.relIndex H : ℝ)) ^ 2 :=
            (sq_le_sq₀ (sub_nonneg.mpr hrOne) hrightNonneg).2 hsmall
          have hsqrtSq :
              Real.sqrt (A.relIndex H : ℝ) ^ 2 =
                (A.relIndex H : ℝ) :=
            Real.sq_sqrt hrNonneg
          have hpoly :
              (0 : ℝ) ≤ (A.relIndex H : ℝ) *
                ((A.relIndex H : ℝ) -
                  (4 * (K.index : ℝ) ^ 2 + 2)) :=
            mul_nonneg hrNonneg (sub_nonneg.mpr hlargeR)
          nlinarith [hsquare, hsqrtSq, hpoly]
  exact hP (Nat.card H1) H1 rfl
    (inferInstance : (H1.map K.subtype : Subgroup L).Normal)
    hMH1 hH1H hcoh hlarge

end

end Submission.OddOrder.PF
