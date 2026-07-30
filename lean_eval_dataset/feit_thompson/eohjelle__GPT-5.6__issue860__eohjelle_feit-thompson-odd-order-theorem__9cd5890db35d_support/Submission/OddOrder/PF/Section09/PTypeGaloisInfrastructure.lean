import Submission.OddOrder.BG.Section03.FrobeniusBasic
import Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary
import Submission.OddOrder.PF.Section01.InductionTransitivity
import Submission.OddOrder.PF.Section04.PrimeTIReducedCharacters
import Submission.OddOrder.PF.Section05.SeqIndGlobal
import Submission.OddOrder.PF.Section06.FrobeniusKernelInduction
import Submission.OddOrder.PF.Section08.FTSupportPartition
import Submission.OddOrder.PF.Section09.PTypeGaloisAction
import Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure

/-!
# Peterfalvi Section 9: Galois-character infrastructure

This module packages the quotient, inertia, Clifford-theory, and subgroup
infrastructure used by the Galois character phases of Peterfalvi (9.9).  It
stops before the character-arithmetic arguments.
-/

namespace Submission.OddOrder.PF

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open CategoryTheory Limits
open scoped BigOperators Classical IsMulCommutative Pointwise MonoidAlgebra

noncomputable section

universe u v w

/-! ## Quotient notation -/

/-- The image of a subgroup in the quotient by `H₀`. -/
abbrev ptypeQuotientImage
    {Q : Type u} [Group Q]
    (H₀ H : Subgroup Q) [H₀.Normal] : Subgroup (Q ⧸ H₀) :=
  H.map (QuotientGroup.mk' H₀)

namespace internal

/-! The built character-orthogonality criteria currently place the group and
coefficient field in one universe.  These private split-universe forms support
the exported complex-character adapters below. -/

private instance pTypeRepInjectiveGeneral
    {G : Type u} {k : Type v} [Group G] [Finite G] [Field k]
    [NeZero (Nat.card G : k)] (V : Rep.{w} k G) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

private instance pTypeFDRepInjectiveGeneral
    {G : Type u} {k : Type v} [Group G] [Finite G] [Field k]
    [NeZero (Nat.card G : k)] (V : FDRep k G) : Injective V :=
  (forget₂ (FDRep k G) (Rep k G)).injective_of_map_injective inferInstance

private theorem pTypeSimple_iff_end_is_rank_one_general
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
        have hιφ : 𝟙 _ = ι ≫ φ :=
          (Injective.comp_factorThru (𝟙 _) ι).symm
        apply_fun (· ≫ ι) at hιφ
        simp_all
      obtain ⟨c, hc⟩ : ∃ c : k, c • _ = 𝟙 V :=
        (finrank_eq_one_iff_of_nonzero' _ hφι).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

private theorem pTypeSimple_iff_char_is_norm_one_general
    {G : Type u} {k : Type v} [Group G] [Fintype G] [Field k]
    [IsAlgClosed k] [CharZero k] (V : FDRep k G) :
    Simple V ↔
      ∑ g : G, V.character g * V.character g⁻¹ = Nat.card G where
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
    rw [pTypeSimple_iff_end_is_rank_one_general, ← Nat.cast_inj (R := k),
      ← eq, Nat.cast_one]

/-! ## Inertia and inflation through a local quotient -/

/-- Conjugating an inflated class function is the inflation of the
conjugated quotient-image class function. -/
theorem pTypeNormalConjugate_comap_subgroupMap
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (T : Subgroup A) [T.Normal]
    (theta : ClassFunction (T.map f) ℂ) (x : A) :
    letI : (T.map f).Normal :=
      Subgroup.Normal.map (inferInstance : T.Normal) f hf
    ClassFunction.normalConjugate T x
        (ClassFunction.comap (f.subgroupMap T) theta) =
      ClassFunction.comap (f.subgroupMap T)
        (ClassFunction.normalConjugate (T.map f) (f x) theta) := by
  letI : (T.map f).Normal :=
    Subgroup.Normal.map (inferInstance : T.Normal) f hf
  ext t
  simp only [ClassFunction.normalConjugate_apply,
    ClassFunction.comap_apply]
  apply congrArg theta
  apply Subtype.ext
  change f (↑((MulAut.conjNormal x).symm t) : A) =
    ↑((MulAut.conjNormal (f x)).symm ((f.subgroupMap T) t))
  simp only [MulAut.conjNormal_symm_apply]
  have hmap : (↑((f.subgroupMap T) t) : B) = f (t : A) := rfl
  rw [hmap, map_mul, map_mul, map_inv]

/-- Inertia commutes with inflation along a finite surjection. -/
theorem pTypeInertia_comap_subgroupMap
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (T : Subgroup A) [T.Normal]
    (theta : ClassFunction (T.map f) ℂ) :
    letI : (T.map f).Normal :=
      Subgroup.Normal.map (inferInstance : T.Normal) f hf
    ClassFunction.inertia T
        (ClassFunction.comap (f.subgroupMap T) theta) =
      (ClassFunction.inertia (T.map f) theta).comap f := by
  letI : (T.map f).Normal :=
    Subgroup.Normal.map (inferInstance : T.Normal) f hf
  ext x
  change
    (ClassFunction.normalConjugate T x
        (ClassFunction.comap (f.subgroupMap T) theta) =
      ClassFunction.comap (f.subgroupMap T) theta) ↔
    (ClassFunction.normalConjugate (T.map f) (f x) theta = theta)
  constructor
  · intro hx
    apply ClassFunction.comap_injective
      (f.subgroupMap T) (f.subgroupMap_surjective T)
    calc
      ClassFunction.comap (f.subgroupMap T)
          (ClassFunction.normalConjugate (T.map f) (f x) theta) =
          ClassFunction.normalConjugate T x
            (ClassFunction.comap (f.subgroupMap T) theta) :=
        (pTypeNormalConjugate_comap_subgroupMap
          f hf T theta x).symm
      _ = ClassFunction.comap (f.subgroupMap T) theta := hx
  · intro hx
    calc
      ClassFunction.normalConjugate T x
          (ClassFunction.comap (f.subgroupMap T) theta) =
          ClassFunction.comap (f.subgroupMap T)
            (ClassFunction.normalConjugate (T.map f) (f x) theta) :=
        pTypeNormalConjugate_comap_subgroupMap f hf T theta x
      _ = ClassFunction.comap (f.subgroupMap T) theta := by rw [hx]

/-- A nonprincipal irreducible character of a Frobenius kernel, inflated
through a local quotient image, has the expected inertia subgroup. -/
theorem pTypeInertia_inflated_FrobeniusKernel
    {A : Type u} [Group A] [Fintype A]
    (N T R : Subgroup A) [N.Normal] [T.Normal]
    (hFrob : IsFrobeniusDecomposition
      (T.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N)))
    (theta : IrreducibleCharacter
      (T.map (QuotientGroup.mk' N)) ℂ)
    (htheta : theta ≠ IrreducibleCharacter.trivial) :
    ClassFunction.inertia T
        (ClassFunction.comap
          ((QuotientGroup.mk' N).subgroupMap T)
          (theta : ClassFunction
            (T.map (QuotientGroup.mk' N)) ℂ)) =
      T ⊔ N := by
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  letI : (T.map q).Normal :=
    Subgroup.Normal.map (inferInstance : T.Normal) q
      (QuotientGroup.mk'_surjective N)
  rw [pTypeInertia_comap_subgroupMap q
      (QuotientGroup.mk'_surjective N) T,
    inertia_Frobenius_ker hFrob theta htheta,
    Subgroup.comap_map_eq, QuotientGroup.ker_mk']

/-! ## Irreducible descent and inflation -/

/-- Split-universe form of the equality between the translation kernel of an
irreducible character and the kernel of its realizing representation. -/
theorem pTypeGaloisTranslationKernel_irreducibleCharacter
    {A : Type u} [Group A]
    (chi : IrreducibleCharacter A ℂ) :
    ClassFunction.translationKernel (chi : ClassFunction A ℂ) =
      chi.representation.ρ.ker := by
  apply le_antisymm
  · intro a ha
    rw [MonoidHom.mem_ker]
    let rho : Representation ℂ A chi.representation :=
      chi.representation.ρ
    letI : CategoryTheory.Simple chi.representation :=
      chi.representation_simple
    letI : Representation.IsIrreducible rho :=
      representation_isIrreducible_of_simple_fdRep chi.representation
    have htraceGroup (g : A) :
        LinearMap.trace ℂ chi.representation
            ((rho a - 1) * rho g) = 0 := by
      rw [sub_mul, one_mul, map_sub, ← rho.map_mul]
      change rho.character (a * g) - rho.character g = 0
      dsimp only [rho]
      change chi.representation.character (a * g) -
        chi.representation.character g = 0
      rw [chi.representation_character, chi.representation_character]
      exact sub_eq_zero.mpr (ha g)
    have htraceAlgebra (z : ℂ[A]) :
        LinearMap.trace ℂ chi.representation
            ((rho a - 1) * rho.asAlgebraHom z) = 0 := by
      induction z using MonoidAlgebra.induction_on with
      | hM g =>
          simpa only [Representation.asAlgebraHom_of] using htraceGroup g
      | hadd x y hx hy =>
          simp only [map_add, mul_add, hx, hy, add_zero]
      | hsmul c x hx =>
          simp only [map_smul, mul_smul_comm, hx, smul_zero]
    have htraceEnd (X : Module.End ℂ chi.representation) :
        LinearMap.trace ℂ chi.representation ((rho a - 1) * X) = 0 := by
      obtain ⟨z, rfl⟩ :=
        MathlibSupport.Representation.IsIrreducible.asAlgebraHom_surjective
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
            ((rho a - 1) * (LinearMap.toMatrixAlgEquiv b).symm X)).trace = 0
        at hX
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

/-- A representation remains irreducible after pullback along a surjective
group homomorphism.  The representation space has its own universe. -/
private theorem representationIrreducibleCompSurjective
    {A B : Type u} {V : Type v}
    [Group A] [Group B] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ B V) [Representation.IsIrreducible rho]
    (f : A →* B) (hf : Function.Surjective f) :
    Representation.IsIrreducible (rho.comp f) := by
  let sigma : Representation ℂ A V := rho.comp f
  have hbot_ne_top : (⊥ : Subrepresentation sigma) ≠ ⊤ := by
    intro h
    apply IsSimpleOrder.bot_ne_top (α := Subrepresentation rho)
    apply SetLike.ext
    intro x
    have hx := congrArg (fun U : Subrepresentation sigma ↦ x ∈ U) h
    change (x ∈ (⊥ : Submodule ℂ V)) =
      (x ∈ (⊤ : Submodule ℂ V)) at hx
    exact iff_of_eq hx
  letI : Nontrivial (Subrepresentation sigma) :=
    ⟨⟨⊥, ⊤, hbot_ne_top⟩⟩
  refine IsSimpleOrder.of_forall_eq_top fun U hU ↦ ?_
  let U' : Subrepresentation rho :=
    { toSubmodule := U.toSubmodule
      apply_mem_toSubmodule b x hx := by
        obtain ⟨a, rfl⟩ := hf b
        exact U.apply_mem_toSubmodule a hx }
  have hU' : U' ≠ ⊥ := by
    intro hbot
    apply hU
    apply SetLike.ext
    intro x
    have hx := congrArg (fun W : Subrepresentation rho ↦ x ∈ W) hbot
    change (x ∈ U.toSubmodule) =
      (x ∈ (⊥ : Submodule ℂ V)) at hx
    exact iff_of_eq hx
  have htop : U' = ⊤ :=
    (IsSimpleOrder.eq_bot_or_eq_top U').resolve_left hU'
  apply SetLike.ext
  intro x
  have hx := congrArg (fun W : Subrepresentation rho ↦ x ∈ W) htop
  change (x ∈ U.toSubmodule) =
    (x ∈ (⊤ : Submodule ℂ V)) at hx
  exact iff_of_eq hx

/-- Universe-polymorphic pullback of an irreducible complex character along
a group equivalence. -/
noncomputable def pTypeGaloisComapMulEquiv
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) (chi : IrreducibleCharacter B ℂ) :
    IrreducibleCharacter A ℂ := by
  let rho : Representation ℂ A chi.representation :=
    chi.representation.ρ.comp e.toMonoidHom
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible rho :=
    representationIrreducibleCompSurjective
      chi.representation.ρ e.toMonoidHom e.surjective
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
theorem pTypeGaloisComapMulEquiv_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) (chi : IrreducibleCharacter B ℂ) (a : A) :
    pTypeGaloisComapMulEquiv e chi a = chi (e a) := by
  simp only [pTypeGaloisComapMulEquiv,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (e a) = chi (e a)
  exact chi.representation_character (e a)

private theorem pTypeGaloisExternalProductFDRep_simple
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (chi : IrreducibleCharacter A ℂ)
    (psi : IrreducibleCharacter B ℂ) :
    CategoryTheory.Simple
      (FDRep.externalProduct chi.representation psi.representation) := by
  letI : Invertible (Nat.card A : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card B : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card (A × B) : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [pTypeSimple_iff_char_is_norm_one_general]
  have hchi :=
    (pTypeSimple_iff_char_is_norm_one_general chi.representation).mp
      chi.representation_simple
  have hpsi :=
    (pTypeSimple_iff_char_is_norm_one_general psi.representation).mp
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
    _ = (Nat.card A : ℂ) * (Nat.card B : ℂ) := by rw [hchi, hpsi]
    _ = (Nat.card (A × B) : ℂ) := by
      rw [Nat.card_prod, Nat.cast_mul]

/-- The external product of complex irreducibles, generalized to groups in
an arbitrary universe. -/
noncomputable def pTypeGaloisExternalProduct
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (chi : IrreducibleCharacter A ℂ)
    (psi : IrreducibleCharacter B ℂ) :
    IrreducibleCharacter (A × B) ℂ := by
  letI : CategoryTheory.Simple
      (FDRep.externalProduct chi.representation psi.representation) :=
    pTypeGaloisExternalProductFDRep_simple chi psi
  exact IrreducibleCharacter.ofFDRep
    (FDRep.externalProduct chi.representation psi.representation)

@[simp]
theorem pTypeGaloisExternalProduct_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (chi : IrreducibleCharacter A ℂ)
    (psi : IrreducibleCharacter B ℂ) (a : A) (b : B) :
    pTypeGaloisExternalProduct chi psi (a, b) = chi a * psi b := by
  letI : CategoryTheory.Simple
      (FDRep.externalProduct chi.representation psi.representation) :=
    pTypeGaloisExternalProductFDRep_simple chi psi
  simp only [pTypeGaloisExternalProduct,
    IrreducibleCharacter.ofFDRep_apply,
    FDRep.externalProduct_character, chi.representation_character,
    psi.representation_character]

/-- Descend an irreducible character through a normal subgroup contained in
its translation kernel. -/
noncomputable def pTypeGaloisQuotientDescendIrreducible
    {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) :
    IrreducibleCharacter (A ⧸ N) ℂ := by
  have hNrho : N ≤ chi.representation.ρ.ker := by
    rw [← pTypeGaloisTranslationKernel_irreducibleCharacter chi]
    exact hN
  let rhoQ : Representation ℂ (A ⧸ N) chi.representation :=
    QuotientGroup.lift N chi.representation.ρ hNrho
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  have hrhoQcomp : rhoQ.comp q = chi.representation.ρ := by
    ext a v
    rfl
  letI : Representation.IsIrreducible (rhoQ.comp q) := by
    rw [hrhoQcomp]
    infer_instance
  letI : Representation.IsIrreducible rhoQ :=
    representation_isIrreducible_of_comp rhoQ q
  letI : CategoryTheory.Simple (FDRep.of rhoQ) :=
    simple_fdRep_of_isIrreducible rhoQ
  exact IrreducibleCharacter.ofFDRep (FDRep.of rhoQ)

@[simp]
theorem pTypeGaloisQuotientDescendIrreducible_mk_apply
    {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) (a : A) :
    pTypeGaloisQuotientDescendIrreducible N chi hN
        (QuotientGroup.mk' N a) = chi a := by
  simp only [pTypeGaloisQuotientDescendIrreducible,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character a = chi a
  exact chi.representation_character a

/-- Descend an irreducible character along an arbitrary finite surjection. -/
noncomputable def pTypeGaloisDescendIrreducibleSurjective
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter A ℂ)
    (hker : f.ker ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) :
    IrreducibleCharacter B ℂ :=
  let chiQ := pTypeGaloisQuotientDescendIrreducible
    f.ker chi hker
  let e : (A ⧸ f.ker) ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  pTypeGaloisComapMulEquiv e.symm chiQ

@[simp]
theorem pTypeGaloisDescendIrreducibleSurjective_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter A ℂ)
    (hker : f.ker ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) (a : A) :
    pTypeGaloisDescendIrreducibleSurjective f hf chi hker (f a) =
      chi a := by
  let chiQ := pTypeGaloisQuotientDescendIrreducible
    f.ker chi hker
  let e : (A ⧸ f.ker) ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  change pTypeGaloisComapMulEquiv e.symm chiQ (f a) =
    chi a
  rw [pTypeGaloisComapMulEquiv_apply]
  have he : e (QuotientGroup.mk' f.ker a) = f a := rfl
  rw [← he, e.symm_apply_apply]
  exact pTypeGaloisQuotientDescendIrreducible_mk_apply
    f.ker chi hker a

/-- Inflation of the canonical descended irreducible is the original class
function. -/
theorem pTypeGalois_comap_descendIrreducibleSurjective
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter A ℂ)
    (hker : f.ker ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) :
    ClassFunction.comap f
        (pTypeGaloisDescendIrreducibleSurjective
          f hf chi hker : ClassFunction B ℂ) =
      (chi : ClassFunction A ℂ) := by
  ext a
  exact pTypeGaloisDescendIrreducibleSurjective_apply
    f hf chi hker a

/-- Inflate an irreducible character along a finite surjection. -/
noncomputable def pTypeGaloisInflateIrreducible
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) :
    IrreducibleCharacter A ℂ := by
  let rho : Representation ℂ A chi.representation :=
    chi.representation.ρ.comp f
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  letI : Representation.IsIrreducible rho :=
    representationIrreducibleCompSurjective
      chi.representation.ρ f hf
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
theorem pTypeGaloisInflateIrreducible_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) (a : A) :
    pTypeGaloisInflateIrreducible f hf chi a = chi (f a) := by
  simp only [pTypeGaloisInflateIrreducible,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (f a) = chi (f a)
  exact chi.representation_character (f a)

/-- Translation-kernel containment is reflected by a surjective pullback. -/
theorem pTypeTranslationKernel_comap_surjective_iff
    {A B : Type u} [Group A] [Group B]
    (f : A →* B) (hf : Function.Surjective f)
    (T : Subgroup A) (phi : ClassFunction B ℂ) :
    T ≤ ClassFunction.translationKernel
        (ClassFunction.comap f phi) ↔
      T.map f ≤ ClassFunction.translationKernel phi := by
  constructor
  · intro hT b hb y
    obtain ⟨t, ht, rfl⟩ := hb
    obtain ⟨x, rfl⟩ := hf y
    simpa only [ClassFunction.comap_apply, map_mul] using hT ht x
  · intro hT t ht x
    change phi (f (t * x)) = phi (f x)
    rw [map_mul]
    exact hT ⟨t, ht, rfl⟩ (f x)

/-- Inflation and canonical descent are inverse on irreducibles whose
translation kernel contains the kernel of the quotient map. -/
theorem pTypeGalois_inflate_descendIrreducibleSurjective
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter A ℂ)
    (hker : f.ker ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) :
    pTypeGaloisInflateIrreducible f hf
        (pTypeGaloisDescendIrreducibleSurjective
          f hf chi hker) = chi := by
  apply IrreducibleCharacter.ext
  intro a
  rw [pTypeGaloisInflateIrreducible_apply,
    pTypeGaloisDescendIrreducibleSurjective_apply]

/-- Two surjective images of the same group with a specified common kernel
are canonically equivalent. -/
noncomputable def pTypeGaloisImageEquivOfCommonKernel
    {A B C : Type u} [Group A] [Group B] [Group C]
    (N : Subgroup A) (f : A →* B) (g : A →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfker : f.ker = N) (hgker : g.ker = N) :
    B ≃* C := by
  let ef : (A ⧸ f.ker) ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  let eg : (A ⧸ g.ker) ≃* C :=
    QuotientGroup.quotientKerEquivOfSurjective g hg
  let eker : (A ⧸ f.ker) ≃* (A ⧸ g.ker) :=
    QuotientGroup.quotientMulEquivOfEq (hfker.trans hgker.symm)
  exact (ef.symm.trans eker).trans eg

@[simp]
theorem pTypeGaloisImageEquivOfCommonKernel_apply
    {A B C : Type u} [Group A] [Group B] [Group C]
    (N : Subgroup A) (f : A →* B) (g : A →* C)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (hfker : f.ker = N) (hgker : g.ker = N) (a : A) :
    pTypeGaloisImageEquivOfCommonKernel N f g hf hg hfker hgker
        (f a) = g a := by
  let ef : (A ⧸ f.ker) ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  let eg : (A ⧸ g.ker) ≃* C :=
    QuotientGroup.quotientKerEquivOfSurjective g hg
  let eker : (A ⧸ f.ker) ≃* (A ⧸ g.ker) :=
    QuotientGroup.quotientMulEquivOfEq (hfker.trans hgker.symm)
  change eg (eker (ef.symm (f a))) = g a
  have hef : ef (QuotientGroup.mk' f.ker a) = f a := rfl
  rw [← hef, ef.symm_apply_apply]
  rfl

/-! ## Linear characters and Clifford splicing -/

/-- Degree one is invariant under transport along a group equivalence. -/
theorem pTypeIsLinearCharacter_comapMulEquiv
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) (chi : IrreducibleCharacter B ℂ)
    (hchi : pTypeIsLinearCharacter chi) :
    pTypeIsLinearCharacter
      (pTypeGaloisComapMulEquiv e chi) := by
  rw [pTypeIsLinearCharacter] at hchi ⊢
  apply Nat.cast_injective (R := ℂ)
  change
    (Module.finrank ℂ
      (pTypeGaloisComapMulEquiv e chi).representation : ℂ) =
      ((1 : ℕ) : ℂ)
  calc
    (Module.finrank ℂ
        (pTypeGaloisComapMulEquiv e chi).representation : ℂ) =
        pTypeGaloisComapMulEquiv e chi 1 :=
      (IrreducibleCharacter.apply_one_eq_finrank _).symm
    _ = chi (e 1) := by rw [pTypeGaloisComapMulEquiv_apply]
    _ = chi 1 := by rw [map_one]
    _ = (Module.finrank ℂ chi.representation : ℂ) :=
      IrreducibleCharacter.apply_one_eq_finrank chi
    _ = ((1 : ℕ) : ℂ) := by exact_mod_cast hchi

/-- Nonprincipality is invariant under transport along a group equivalence. -/
theorem pTypeComapMulEquiv_ne_trivial
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) (chi : IrreducibleCharacter B ℂ)
    (hchi : chi ≠ IrreducibleCharacter.trivial) :
    pTypeGaloisComapMulEquiv e chi ≠
      IrreducibleCharacter.trivial := by
  intro htrivial
  apply hchi
  apply IrreducibleCharacter.ext
  intro b
  have hvalue := congrArg
    (fun psi : IrreducibleCharacter A ℂ ↦ psi (e.symm b)) htrivial
  simpa [pTypeGaloisComapMulEquiv_apply] using hvalue

/-- External products preserve degree one. -/
theorem pTypeIsLinearCharacter_externalProduct
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (chi : IrreducibleCharacter A ℂ)
    (psi : IrreducibleCharacter B ℂ)
    (hchi : pTypeIsLinearCharacter chi)
    (hpsi : pTypeIsLinearCharacter psi) :
    pTypeIsLinearCharacter
      (pTypeGaloisExternalProduct chi psi) := by
  rw [pTypeIsLinearCharacter] at hchi hpsi ⊢
  apply Nat.cast_injective (R := ℂ)
  change
    (Module.finrank ℂ
      (pTypeGaloisExternalProduct chi psi).representation : ℂ) =
      ((1 : ℕ) : ℂ)
  calc
    (Module.finrank ℂ
        (pTypeGaloisExternalProduct chi psi).representation : ℂ) =
        pTypeGaloisExternalProduct chi psi 1 :=
      (IrreducibleCharacter.apply_one_eq_finrank _).symm
    _ = chi 1 * psi 1 := by
      exact pTypeGaloisExternalProduct_apply
        chi psi (1 : A) (1 : B)
    _ = (Module.finrank ℂ chi.representation : ℂ) *
        (Module.finrank ℂ psi.representation : ℂ) := by
      rw [IrreducibleCharacter.apply_one_eq_finrank,
        IrreducibleCharacter.apply_one_eq_finrank]
    _ = ((1 : ℕ) : ℂ) := by
      exact_mod_cast congrArg₂ (· * ·) hchi hpsi

/-- Inflation preserves degree one. -/
theorem pTypeIsLinearCharacter_inflate
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ)
    (hchi : pTypeIsLinearCharacter chi) :
    pTypeIsLinearCharacter
      (pTypeGaloisInflateIrreducible f hf chi) := by
  rw [pTypeIsLinearCharacter] at hchi ⊢
  apply Nat.cast_injective (R := ℂ)
  change
    (Module.finrank ℂ
      (pTypeGaloisInflateIrreducible f hf chi).representation : ℂ) =
      ((1 : ℕ) : ℂ)
  calc
    (Module.finrank ℂ
        (pTypeGaloisInflateIrreducible f hf chi).representation : ℂ) =
        pTypeGaloisInflateIrreducible f hf chi 1 :=
      (IrreducibleCharacter.apply_one_eq_finrank _).symm
    _ = chi (f 1) := pTypeGaloisInflateIrreducible_apply f hf chi 1
    _ = chi 1 := by rw [map_one]
    _ = (Module.finrank ℂ chi.representation : ℂ) :=
      IrreducibleCharacter.apply_one_eq_finrank chi
    _ = ((1 : ℕ) : ℂ) := by exact_mod_cast hchi

/-- Inflation along a surjection reflects the principal character. -/
theorem pTypeGaloisInflate_ne_trivial
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ)
    (hchi : chi ≠ IrreducibleCharacter.trivial) :
    pTypeGaloisInflateIrreducible f hf chi ≠
      IrreducibleCharacter.trivial := by
  intro htrivial
  apply hchi
  apply IrreducibleCharacter.ext
  intro b
  obtain ⟨a, rfl⟩ := hf b
  have hvalue := congrArg
    (fun psi : IrreducibleCharacter A ℂ ↦ psi a) htrivial
  simpa [pTypeGaloisInflateIrreducible_apply] using hvalue

/-- A nonprincipal linear character cannot have full translation kernel. -/
theorem pTypeLinear_ne_trivial_not_top_le_kernel
    {A : Type u} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ)
    (hlinear : pTypeIsLinearCharacter chi)
    (hchi : chi ≠ IrreducibleCharacter.trivial) :
    ¬ (⊤ : Subgroup A) ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ) := by
  intro htop
  apply hchi
  apply IrreducibleCharacter.ext
  intro x
  have hx := htop (Subgroup.mem_top x)
  rw [ClassFunction.mem_translationKernel_iff] at hx
  have hvalue := hx 1
  have hone : chi 1 = 1 := by
    rw [IrreducibleCharacter.apply_one_eq_finrank]
    change ((pTypeIrreducibleDegree chi : ℕ) : ℂ) = 1
    rw [hlinear]
    norm_num
  simpa only [mul_one, hone,
    IrreducibleCharacter.trivial_apply] using hvalue

/-- Evaluation at the identity of a linear irreducible. -/
@[simp]
theorem pTypeLinear_apply_one
    {A : Type u} [Group A] [Fintype A]
    (chi : IrreducibleCharacter A ℂ)
    (hlinear : pTypeIsLinearCharacter chi) : chi 1 = 1 := by
  rw [IrreducibleCharacter.apply_one_eq_finrank]
  change ((pTypeIrreducibleDegree chi : ℕ) : ℂ) = 1
  rw [hlinear]
  norm_num

/-- Canonical descent preserves nonprincipality. -/
theorem pTypeGalois_descendIrreducibleSurjective_ne_trivial
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter A ℂ)
    (hker : f.ker ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ))
    (hchi : chi ≠ IrreducibleCharacter.trivial) :
    pTypeGaloisDescendIrreducibleSurjective f hf chi hker ≠
      IrreducibleCharacter.trivial := by
  intro hdesc
  apply hchi
  apply Subtype.ext
  ext a
  calc
    chi a = pTypeGaloisDescendIrreducibleSurjective
        f hf chi hker (f a) :=
      (pTypeGaloisDescendIrreducibleSurjective_apply
        f hf chi hker a).symm
    _ = (IrreducibleCharacter.trivial :
        IrreducibleCharacter B ℂ) (f a) := by rw [hdesc]
    _ = (IrreducibleCharacter.trivial :
        IrreducibleCharacter A ℂ) a := by simp

/-- Clifford correspondence in the exact inertia-subgroup form needed here.
This adapter is necessarily universe zero because the current built Clifford
API binds the group and coefficient field universes. -/
theorem pTypeGalois_induced_of_inertia_eq
    {A : Type} [Group A] [Fintype A]
    (H T : Subgroup A) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    (hT : ClassFunction.inertia H
      (theta : ClassFunction H ℂ) = T)
    (chi : IrreducibleCharacter A ℂ)
    (htheta : theta.IsConstituent
      (ClassFunction.restrict H
        (chi : ClassFunction A ℂ))) :
    ∃ xi : IrreducibleCharacter T ℂ,
      (chi : ClassFunction A ℂ) =
        ClassFunction.induce T (xi : ClassFunction T ℂ) := by
  subst T
  have hchiConst : chi ∈ ClassFunction.constituents
      (ClassFunction.induce H (theta : ClassFunction H ℂ)) := by
    rw [ClassFunction.mem_constituents_iff]
    exact (theta.isConstituent_restrict_iff_induce H chi).mp htheta
  rw [ClassFunction.inertiaConstituentMap_image H theta] at hchiConst
  obtain ⟨psi, _hpsiMem, hpsi⟩ :=
    Finset.mem_image.mp hchiConst
  refine ⟨psi.1, ?_⟩
  calc
    (chi : ClassFunction A ℂ) =
        (ClassFunction.inertiaConstituentMap H theta psi :
          ClassFunction A ℂ) := by rw [hpsi]
    _ = ClassFunction.induce
          (ClassFunction.inertia H
            (theta : ClassFunction H ℂ))
          (psi.1 : ClassFunction
            (ClassFunction.inertia H
              (theta : ClassFunction H ℂ)) ℂ) :=
      ClassFunction.coe_inertiaConstituentMap H theta psi

/-- Descent, Frobenius inertia, and Clifford correspondence in one splice. -/
theorem pTypeGalois_induced_from_localFrobenius
    {A : Type} [Group A] [Fintype A]
    (N H R : Subgroup A) [N.Normal] [H.Normal]
    (hFrob : IsFrobeniusDecomposition
      (H.map (QuotientGroup.mk' N))
      (R.map (QuotientGroup.mk' N)))
    (theta : IrreducibleCharacter H ℂ)
    (hker : ((QuotientGroup.mk' N).subgroupMap H).ker ≤
      ClassFunction.translationKernel
        (theta : ClassFunction H ℂ))
    (htheta : theta ≠ IrreducibleCharacter.trivial)
    (chi : IrreducibleCharacter A ℂ)
    (hconst : theta.IsConstituent
      (ClassFunction.restrict H
        (chi : ClassFunction A ℂ))) :
    ∃ xi : IrreducibleCharacter ↑(H ⊔ N) ℂ,
      (chi : ClassFunction A ℂ) =
        ClassFunction.induce (H ⊔ N)
          (xi : ClassFunction ↑(H ⊔ N) ℂ) := by
  let f : H →* H.map (QuotientGroup.mk' N) :=
    (QuotientGroup.mk' N).subgroupMap H
  have hf : Function.Surjective f :=
    (QuotientGroup.mk' N).subgroupMap_surjective H
  let thetaBar : IrreducibleCharacter
      (H.map (QuotientGroup.mk' N)) ℂ :=
    pTypeGaloisDescendIrreducibleSurjective
      f hf theta hker
  have hthetaInflate : ClassFunction.comap f
      (thetaBar : ClassFunction
        (H.map (QuotientGroup.mk' N)) ℂ) =
      (theta : ClassFunction H ℂ) :=
    pTypeGalois_comap_descendIrreducibleSurjective
      f hf theta hker
  have hthetaBar : thetaBar ≠ IrreducibleCharacter.trivial :=
    pTypeGalois_descendIrreducibleSurjective_ne_trivial
      f hf theta hker htheta
  have hinertia : ClassFunction.inertia H
      (theta : ClassFunction H ℂ) = H ⊔ N := by
    rw [← hthetaInflate]
    exact pTypeInertia_inflated_FrobeniusKernel
      N H R hFrob thetaBar hthetaBar
  exact pTypeGalois_induced_of_inertia_eq
    H (H ⊔ N) theta hinertia chi hconst

end internal

/-! ## Canonical Section 9 subgroups -/

/-- Source `U`, regarded as a subgroup of `HU = M'` inside the maximal
subgroup type. -/
abbrev pTypeUInDerived
    {Gamma : Type u} [Group Gamma]
    (M K U : Subgroup Gamma) : Subgroup (pTypeHUInMaximal M K) :=
  (U.subgroupOf M).subgroupOf (pTypeHUInMaximal M K)

/-- Source `C`, regarded as a subgroup of `HU = M'`. -/
def pTypeCInDerived
    {Gamma : Type u} [Group Gamma]
    (M K U W₁ : Subgroup Gamma)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) :
    Subgroup (pTypeHUInMaximal M K) :=
  ((D.C.map U.subtype).subgroupOf M).subgroupOf
    (pTypeHUInMaximal M K)

/-- Source `H₀C'`, formed in `HU`.  Here `C'` is the image in `M` of the
derived subgroup of the action kernel `D.C`. -/
def pTypeH0CPrimeInDerived
    {Gamma : Type u} [Group Gamma]
    (M K H₀ U W₁ : Subgroup Gamma)
    {Hbar : Type u} [Group Hbar] [Finite Hbar]
    [Finite U] [Finite W₁]
    (D : PTypeFactorActionData Hbar U W₁) :
    Subgroup (pTypeHUInMaximal M K) :=
  pTypeH0InDerived M K H₀ ⊔
    ((pTypeDerivedComplementInMaximal
      (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf
        (pTypeHUInMaximal M K)

/-- The selected F-core kernel remains normal after restricting from `M` to
`HU = M'`. -/
theorem pTypeH0InDerived_normal
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeH0InDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx)).Normal := by
  exact Subgroup.Normal.subgroupOf
    (Ptype_Fcore_kernel_normal_M ctx)
    (pTypeHUInMaximal M (derivedWithin M))

namespace internal

/-! ## Normality and derived-complement transport -/

/-- The Fitting core remains normal after restriction to `HU = M'`. -/
theorem pTypeHInDerived_normal
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (_ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeHInDerived M (derivedWithin M)
      (Fitting_core M)).Normal := by
  exact Subgroup.Normal.subgroupOf
    (Fcore_normal M)
    (pTypeHUInMaximal M (derivedWithin M))

/-- The canonical quotient kernel `H₀C` is normal in `HU`. -/
theorem pTypeH0CInDerived_normal
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁
      (Ptype_factor_action ctx facts)).Normal := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H₀a := Ptype_Fcore_kernel ctx
  let Cₐ := Ptype_Fcompl_kernel ctx
  let Kₐ : Subgroup Gamma := H₀a ⊔ Cₐ
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hH₀der : H₀a ≤ derivedWithin M :=
    (Ptype_Fcore_kernel_lt ctx).le.trans hHder
  have hCder : Cₐ ≤ derivedWithin M :=
    (Ptype_Fcompl_kernel_le ctx).trans hUder
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hH₀M : H₀a ≤ M := hH₀der.trans hDerM
  have hCM : Cₐ ≤ M := hCder.trans hDerM
  have hH₀HU : H₀a.subgroupOf M ≤ HU := by
    intro x hx
    exact hH₀der hx
  have hCHU : Cₐ.subgroupOf M ≤ HU := by
    intro x hx
    exact hCder hx
  letI : (Kₐ.subgroupOf M).Normal :=
    (Ptype_Fcore_extensions_normal ctx).H₀C_normal.2
  have hkernelEq :
      pTypeH0CInDerived M (derivedWithin M)
          H₀a U W₁ D =
        (Kₐ.subgroupOf M).subgroupOf HU := by
    change (H₀a.subgroupOf M).subgroupOf HU ⊔
        (((D.C.map U.subtype).subgroupOf M).subgroupOf HU) =
      (Kₐ.subgroupOf M).subgroupOf HU
    have hDC : D.C.map U.subtype = Cₐ := rfl
    rw [hDC, ← Subgroup.subgroupOf_sup hH₀HU hCHU,
      ← Subgroup.subgroupOf_sup hH₀M hCM]
  rw [hkernelEq]
  exact Subgroup.Normal.subgroupOf
    (inferInstance : (Kₐ.subgroupOf M).Normal) HU

/-- Mapping the derived subgroup of an acting subgroup directly into the
ambient group agrees with first mapping the subgroup and then taking its
ambient derived subgroup. -/
theorem pTypeDerivedComplementInMaximal_eq_derivedWithin_map
    {Gamma : Type u} [Group Gamma]
    {U : Subgroup Gamma} (C : Subgroup U) :
    pTypeDerivedComplementInMaximal
        (U.subtype.comp C.subtype) =
      derivedWithin (C.map U.subtype) := by
  change (_root_.commutator C).map
      (U.subtype.comp C.subtype) =
    (_root_.commutator (C.map U.subtype)).map
      (C.map U.subtype).subtype
  calc
    (_root_.commutator C).map (U.subtype.comp C.subtype) =
        ((_root_.commutator C).map C.subtype).map U.subtype :=
      (Subgroup.map_map _ _ _).symm
    _ = ⁅C, C⁆.map U.subtype := by
      rw [C.map_subtype_commutator]
    _ = ⁅C.map U.subtype, C.map U.subtype⁆ :=
      Subgroup.map_commutator C C U.subtype
    _ = (_root_.commutator (C.map U.subtype)).map
        (C.map U.subtype).subtype :=
      (C.map U.subtype).map_subtype_commutator.symm

/-- The canonical subgroup `HC` is normal in `HU`. -/
theorem pTypeHCInDerived_normal
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeHInDerived M (derivedWithin M) (Fitting_core M) ⊔
      pTypeCInDerived M (derivedWithin M) U W₁
        (Ptype_factor_action ctx facts)).Normal := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let Cₐ := Ptype_Fcompl_kernel ctx
  let Kₐ : Subgroup Gamma := Fitting_core M ⊔ Cₐ
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hCder : Cₐ ≤ derivedWithin M :=
    (Ptype_Fcompl_kernel_le ctx).trans hUder
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hHM : Fitting_core M ≤ M := hHder.trans hDerM
  have hCM : Cₐ ≤ M := hCder.trans hDerM
  have hHHU : (Fitting_core M).subgroupOf M ≤ HU := by
    intro x hx
    exact hHder hx
  have hCHU : Cₐ.subgroupOf M ≤ HU := by
    intro x hx
    exact hCder hx
  letI : (Kₐ.subgroupOf M).Normal :=
    (Ptype_Fcore_extensions_normal ctx).HC_normal.2
  have hkernelEq :
      pTypeHInDerived M (derivedWithin M) (Fitting_core M) ⊔
          pTypeCInDerived M (derivedWithin M) U W₁ D =
        (Kₐ.subgroupOf M).subgroupOf HU := by
    change ((Fitting_core M).subgroupOf M).subgroupOf HU ⊔
        (((D.C.map U.subtype).subgroupOf M).subgroupOf HU) =
      (Kₐ.subgroupOf M).subgroupOf HU
    have hDC : D.C.map U.subtype = Cₐ := rfl
    rw [hDC, ← Subgroup.subgroupOf_sup hHHU hCHU,
      ← Subgroup.subgroupOf_sup hHM hCM]
  rw [hkernelEq]
  exact Subgroup.Normal.subgroupOf
    (inferInstance : (Kₐ.subgroupOf M).Normal) HU

/-- The source kernel `H₀C'` is normal after restriction from `M` to
`HU`. -/
theorem pTypeH0CPrimeInDerived_normal
    {Gamma : Type u} [Group Gamma] [Finite Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeH0CPrimeInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁
      (Ptype_factor_action ctx facts)).Normal := by
  let D := Ptype_factor_action ctx facts
  let HU := pTypeHUInMaximal M (derivedWithin M)
  let H₀a := Ptype_Fcore_kernel ctx
  let Cₐ := Ptype_Fcompl_kernel ctx
  let Cₐ' := derivedWithin Cₐ
  let Kₐ : Subgroup Gamma := H₀a ⊔ Cₐ'
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hH₀der : H₀a ≤ derivedWithin M :=
    (Ptype_Fcore_kernel_lt ctx).le.trans hHder
  have hCder : Cₐ ≤ derivedWithin M :=
    (Ptype_Fcompl_kernel_le ctx).trans hUder
  have hCₐ'der : Cₐ' ≤ derivedWithin M :=
    (Subgroup.map_subtype_le (_root_.commutator Cₐ)).trans hCder
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  have hH₀M : H₀a ≤ M := hH₀der.trans hDerM
  have hCₐ'M : Cₐ' ≤ M := hCₐ'der.trans hDerM
  have hH₀HU : H₀a.subgroupOf M ≤ HU := by
    intro x hx
    exact hH₀der hx
  have hCₐ'HU : Cₐ'.subgroupOf M ≤ HU := by
    intro x hx
    exact hCₐ'der hx
  letI : (Kₐ.subgroupOf M).Normal :=
    (Ptype_Fcore_extensions_normal ctx).H₀C'_normal.2
  have hkernelEq :
      pTypeH0CPrimeInDerived M (derivedWithin M)
          H₀a U W₁ D =
        (Kₐ.subgroupOf M).subgroupOf HU := by
    change (H₀a.subgroupOf M).subgroupOf HU ⊔
        ((pTypeDerivedComplementInMaximal
          (U.subtype.comp D.C.subtype)).subgroupOf M).subgroupOf HU =
      (Kₐ.subgroupOf M).subgroupOf HU
    have hDC : D.C.map U.subtype = Cₐ := rfl
    rw [pTypeDerivedComplementInMaximal_eq_derivedWithin_map D.C,
      hDC, ← Subgroup.subgroupOf_sup hH₀HU hCₐ'HU,
      ← Subgroup.subgroupOf_sup hH₀M hCₐ'M]
  rw [hkernelEq]
  exact Subgroup.Normal.subgroupOf
    (inferInstance : (Kₐ.subgroupOf M).Normal) HU

end internal

/-- The second assertion in part (a) of Peterfalvi (9.9), for one
irreducible character of `HU`. -/
def PTypeCoreInduced
    {M : Type u} [Group M] [Fintype M]
    (HC : Subgroup M) (u : ℕ)
    (s : IrreducibleCharacter M ℂ) : Prop :=
  s 1 = (u : ℂ) ∧
    ∃ xi : IrreducibleCharacter HC ℂ,
      Module.finrank ℂ xi.representation = 1 ∧
        (s : ClassFunction M ℂ) =
          ClassFunction.induce HC (xi : ClassFunction HC ℂ)

end

end Submission.OddOrder.PF
