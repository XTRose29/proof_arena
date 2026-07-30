import Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure

/-!
# Peterfalvi Section 9: the reducible non-Galois character layer

This module proves the quotient-counting part of Peterfalvi (9.8).  It
identifies the reducible members of the Dade-induced family attached to the
F-core kernel, counts them, and shows that they already lie in the family
attached to the enlarged kernel `H₀C`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative MonoidAlgebra

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open CategoryTheory Limits

universe u v w x

/-! ## Coefficient-field transport

The prime-TI API presently places its coefficient field in the same universe
as the finite group.  We use a lifted copy of `ℂ` there and transport the
resulting irreducible characters back to ordinary complex characters. -/

namespace FDRep

variable {G : Type u} {k : Type v} {l : Type w}
  [Group G] [Field k] [Field l]

private instance pTypeReducibleRepInjective
    {A : Type u} {R : Type v} [Group A] [Finite A] [Field R]
    [NeZero (Nat.card A : R)] (V : Rep.{x} R A) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

private instance pTypeReducibleFDRepInjective
    {A : Type u} {R : Type v} [Group A] [Finite A] [Field R]
    [NeZero (Nat.card A : R)] (V : FDRep R A) : Injective V :=
  (forget₂ (FDRep R A) (Rep R A)).injective_of_map_injective inferInstance

private theorem pTypeReducibleSimple_iff_end_rank_one
    {A : Type u} {R : Type v} [Group A] [Finite A] [Field R]
    [IsAlgClosed R] [NeZero (Nat.card A : R)] (V : FDRep R A) :
    Simple V ↔ Module.finrank R (V ⟶ V) = 1 where
  mp h := finrank_endomorphism_simple_eq_one R V
  mpr h := by
    refine { mono_isIso_iff_nonzero {W} f _ :=
      ⟨fun hf habs ↦ ?_, fun hf ↦ ?_⟩ }
    · rw [habs, isIsoZero_iff_source_target_isZero] at hf
      obtain ⟨g, hg⟩ : ∃ g : V ⟶ V, g ≠ 0 :=
        (Module.finrank_pos_iff_exists_ne_zero (R := R)).mp (by grind)
      exact hg (hf.2.eq_zero_of_src g)
    · suffices Epi f by exact isIso_of_mono_of_epi f
      suffices Epi (Abelian.image.ι f) by
        rw [← Abelian.image.fac f]
        exact epi_comp _ _
      rw [← Abelian.image.fac f] at hf
      set iota := Abelian.image.ι f
      set phi := Injective.factorThru (𝟙 _) iota
      have hphi : phi ≫ iota ≠ 0 := by
        intro habs
        have hiota : 𝟙 _ = iota ≫ phi :=
          (Injective.comp_factorThru (𝟙 _) iota).symm
        apply_fun (· ≫ iota) at hiota
        simp_all
      obtain ⟨c, hc⟩ : ∃ c : R, c • _ = 𝟙 V :=
        (finrank_eq_one_iff_of_nonzero' _ hphi).mp h (𝟙 V)
      refine Preadditive.epi_of_cancel_zero _ (fun g hg ↦ ?_)
      apply_fun (· ≫ g) at hc
      simpa [hg] using hc.symm

private theorem pTypeReducibleSimple_iff_char_norm_one
    {A : Type u} {R : Type v} [Group A] [Fintype A] [Field R]
    [IsAlgClosed R] [CharZero R] (V : FDRep R A) :
    Simple V ↔ ∑ a : A, V.character a * V.character a⁻¹ = Nat.card A where
  mp h := by
    have : NeZero (Nat.card A : R) := by
      rw [← @Fintype.card_eq_nat_card A (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Nat.card A : R))
    have := invertibleOfNonzero (NeZero.ne (Fintype.card A : R))
    classical
    have hnorm : ⅟(Nat.card A : R) •
        ∑ a, V.character a * V.character a⁻¹ = 1 := by
      simpa only [Nonempty.intro (Iso.refl V), ↓reduceIte,
        Fintype.card_eq_nat_card] using FDRep.char_orthonormal V V
    apply_fun (· * (Fintype.card A : R)) at hnorm
    rwa [mul_comm, ← smul_eq_mul, smul_smul, Fintype.card_eq_nat_card,
      mul_invOf_self, smul_eq_mul, one_mul, one_mul] at hnorm
  mpr h := by
    have : NeZero (Nat.card A : R) := by
      rw [← @Fintype.card_eq_nat_card A (by assumption)]
      exact NeZero.charZero
    have := invertibleOfNonzero (NeZero.ne (Fintype.card A : R))
    have := invertibleOfNonzero (NeZero.ne (Nat.card A : R))
    have eq := FDRep.scalar_product_char_eq_finrank_equivariant V V
    rw [h] at eq
    simp only [invOf_eq_inv, smul_eq_mul, inv_mul_cancel_of_invertible,
      Fintype.card_eq_nat_card] at eq
    rw [pTypeReducibleSimple_iff_end_rank_one,
      ← Nat.cast_inj (R := R), ← eq, Nat.cast_one]

private def pTypeReducibleCoefficientTransport
    (sigma : k ≃+* l) (V : FDRep k G) : FDRep l G :=
  let b := Module.finBasis k V
  FDRep.of
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp
      (sigma.mapMatrix.toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp V.ρ)))

@[simp]
private theorem pTypeReducibleCoefficientTransport_character
    (sigma : k ≃+* l) (V : FDRep k G) (g : G) :
    (pTypeReducibleCoefficientTransport sigma V).character g =
      sigma (V.character g) := by
  let b := Module.finBasis k V
  change LinearMap.trace l _
      (Matrix.toLinAlgEquiv'
        (sigma.mapMatrix (LinearMap.toMatrixAlgEquiv b (V.ρ g)))) =
    sigma (LinearMap.trace k V (V.ρ g))
  change LinearMap.trace l _
      (Matrix.toLin'
        (sigma.mapMatrix (LinearMap.toMatrixAlgEquiv b (V.ρ g)))) = _
  rw [Matrix.trace_toLin'_eq,
    LinearMap.trace_eq_matrix_trace k b,
    AddMonoidHom.map_trace]
  rfl

variable [Fintype G] [IsAlgClosed k] [IsAlgClosed l]
  [CharZero k] [CharZero l]

private theorem pTypeReducibleCoefficientTransport_simple
    (sigma : k ≃+* l) (V : FDRep k G) [Simple V] :
    Simple (pTypeReducibleCoefficientTransport sigma V) := by
  rw [pTypeReducibleSimple_iff_char_norm_one]
  have hV :=
    (pTypeReducibleSimple_iff_char_norm_one V).mp (by infer_instance)
  simp only [pTypeReducibleCoefficientTransport_character,
    ← map_mul, ← map_sum, hV]
  exact map_natCast sigma (Nat.card G)

end FDRep

namespace IrreducibleCharacter

variable {G : Type u} {k : Type v} {l : Type w}
  [Group G] [Fintype G]
  [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
  [CharZero k] [CharZero l]

private noncomputable def pTypeReducibleMapCoefficient
    (sigma : k ≃+* l) (chi : IrreducibleCharacter G k) :
    IrreducibleCharacter G l := by
  letI : Simple chi.representation := chi.representation_simple
  letI : Simple
      (FDRep.pTypeReducibleCoefficientTransport sigma chi.representation) :=
    FDRep.pTypeReducibleCoefficientTransport_simple sigma chi.representation
  exact ofFDRep
    (FDRep.pTypeReducibleCoefficientTransport sigma chi.representation)

@[simp]
private theorem pTypeReducibleMapCoefficient_apply
    (sigma : k ≃+* l) (chi : IrreducibleCharacter G k) (g : G) :
    pTypeReducibleMapCoefficient sigma chi g = sigma (chi g) := by
  letI : Simple chi.representation := chi.representation_simple
  letI : Simple
      (FDRep.pTypeReducibleCoefficientTransport sigma chi.representation) :=
    FDRep.pTypeReducibleCoefficientTransport_simple sigma chi.representation
  simp only [pTypeReducibleMapCoefficient, ofFDRep_apply,
    FDRep.pTypeReducibleCoefficientTransport_character,
    representation_character]

end IrreducibleCharacter

private theorem pTypeReducibleIsAlgClosedOfRingEquiv
    {k : Type v} {l : Type w} [Field k] [Field l]
    (sigma : k ≃+* l) [IsAlgClosed l] : IsAlgClosed k := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hdegree : Polynomial.degree (p.map sigma.toRingHom) ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := l)
      (p.map sigma.toRingHom) hdegree with ⟨z, hz⟩
  use sigma.symm z
  rw [Polynomial.IsRoot] at hz
  apply sigma.injective
  rw [map_zero, ← hz]
  clear hz hdegree hp hmp
  induction p using Polynomial.induction_on <;> simp_all

private theorem pTypeReducibleMapRingHom_induce
    {G : Type u} {k : Type v} {l : Type w}
    [Group G] [Fintype G] [Field k] [Field l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (K : Subgroup G) (f : ClassFunction K k) :
    ClassFunction.mapRingHom sigma.toRingHom (ClassFunction.induce K f) =
      ClassFunction.induce K
        (ClassFunction.mapRingHom sigma.toRingHom f) := by
  classical
  ext g
  rw [ClassFunction.mapRingHom_apply,
    ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula]
  rw [map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y⁻¹ * g * y ∈ K
  · rw [dif_pos hy, dif_pos hy, ClassFunction.mapRingHom_apply]
  · rw [dif_neg hy, dif_neg hy, map_zero]

@[simp]
private theorem pTypeReducibleMapCoefficient_coe
    {G : Type u} {k : Type v} {l : Type w}
    [Group G] [Fintype G]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (chi : IrreducibleCharacter G k) :
    ClassFunction.mapRingHom sigma.toRingHom
        (chi : ClassFunction G k) =
      (IrreducibleCharacter.pTypeReducibleMapCoefficient sigma chi :
        ClassFunction G l) := by
  ext g
  simp

@[simp]
private theorem pTypeReducibleMapCoefficient_trivial
    {G : Type u} {k : Type v} {l : Type w}
    [Group G] [Fintype G]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) :
    IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
        (IrreducibleCharacter.trivial : IrreducibleCharacter G k) =
      (IrreducibleCharacter.trivial : IrreducibleCharacter G l) := by
  ext g
  simp

private theorem pTypeReducibleMapRingHom_injective
    {G : Type u} {k : Type v} {l : Type w}
    [Group G] [Field k] [Field l] (sigma : k ≃+* l) :
    Function.Injective
      (ClassFunction.mapRingHom sigma.toRingHom :
        ClassFunction G k → ClassFunction G l) := by
  intro f g h
  ext x
  apply sigma.injective
  exact congrArg (fun phi : ClassFunction G l ↦ phi x) h

private theorem pTypeReducibleTranslationKernel_mapRingEquiv
    {G : Type u} {k : Type v} {l : Type w}
    [Group G] [Field k] [Field l]
    (sigma : k ≃+* l) (f : ClassFunction G k) :
    ClassFunction.translationKernel
        (ClassFunction.mapRingHom sigma.toRingHom f) =
      ClassFunction.translationKernel f := by
  ext a
  simp only [ClassFunction.mem_translationKernel_iff,
    ClassFunction.mapRingHom_apply]
  constructor
  · intro h g
    apply sigma.injective
    exact h g
  · intro h g
    exact congrArg sigma (h g)

private theorem pTypeReducibleIsIrreducible_mapRingEquiv_iff
    {G : Type u} {k : Type v} {l : Type w}
    [Group G] [Fintype G]
    [Field k] [Field l] [IsAlgClosed k] [IsAlgClosed l]
    [CharZero k] [CharZero l]
    (sigma : k ≃+* l) (f : ClassFunction G k) :
    IsIrreducibleCharacter G l
        (ClassFunction.mapRingHom sigma.toRingHom f) ↔
      IsIrreducibleCharacter G k f := by
  constructor
  · intro h
    let chiL : IrreducibleCharacter G l :=
      ⟨ClassFunction.mapRingHom sigma.toRingHom f, h⟩
    let chiK : IrreducibleCharacter G k :=
      IrreducibleCharacter.pTypeReducibleMapCoefficient sigma.symm chiL
    have hchiK : (chiK : ClassFunction G k) = f := by
      ext g
      simp [chiK, chiL]
    rw [← hchiK]
    exact chiK.property
  · intro h
    let chiK : IrreducibleCharacter G k := ⟨f, h⟩
    let chiL : IrreducibleCharacter G l :=
      IrreducibleCharacter.pTypeReducibleMapCoefficient sigma chiK
    have hchiL : (chiL : ClassFunction G l) =
        ClassFunction.mapRingHom sigma.toRingHom f := by
      ext g
      simp [chiL, chiK]
    rw [← hchiL]
    exact chiL.property

/-! ## Concrete irreducible-character transport for the quotient argument -/

/-- A representation remains irreducible after pullback along a surjective
group homomorphism.  The representation space is allowed its own universe. -/
private theorem pTypeReducibleRepresentationIrreducibleCompSurjective
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

/-- Inflate an irreducible complex character along a finite surjection. -/
private noncomputable def pTypeReducibleInflateIrreducible
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
    pTypeReducibleRepresentationIrreducibleCompSurjective
      chi.representation.ρ f hf
  letI : CategoryTheory.Simple (FDRep.of rho) :=
    simple_fdRep_of_isIrreducible rho
  exact IrreducibleCharacter.ofFDRep (FDRep.of rho)

@[simp]
private theorem pTypeReducibleInflateIrreducible_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter B ℂ) (a : A) :
    pTypeReducibleInflateIrreducible f hf chi a = chi (f a) := by
  simp only [pTypeReducibleInflateIrreducible,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character (f a) = chi (f a)
  exact chi.representation_character (f a)

/-- Pull an irreducible complex character across a group equivalence.  This
local specialization avoids tying the coefficient and group universes. -/
private noncomputable def pTypeReducibleComapMulEquiv
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) (chi : IrreducibleCharacter B ℂ) :
    IrreducibleCharacter A ℂ :=
  pTypeReducibleInflateIrreducible e.toMonoidHom e.surjective chi

@[simp]
private theorem pTypeReducibleComapMulEquiv_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (e : A ≃* B) (chi : IrreducibleCharacter B ℂ) (a : A) :
    pTypeReducibleComapMulEquiv e chi a = chi (e a) :=
  pTypeReducibleInflateIrreducible_apply
    e.toMonoidHom e.surjective chi a

/-- Complex specialization of the identity between the translation kernel
of an irreducible character and the kernel of a realizing representation. -/
private theorem pTypeReducibleTranslationKernel_irreducibleCharacter
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
        Representation.IsIrreducible.asAlgebraHom_surjective rho X
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

/-- Descend an irreducible complex character through a normal subgroup in
its translation kernel. -/
private noncomputable def pTypeReducibleQuotientDescendIrreducible
    {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) :
    IrreducibleCharacter (A ⧸ N) ℂ := by
  have hNrho : N ≤ chi.representation.ρ.ker := by
    rw [← pTypeReducibleTranslationKernel_irreducibleCharacter chi]
    exact hN
  let rhoQ : Representation ℂ (A ⧸ N) chi.representation :=
    QuotientGroup.lift N chi.representation.ρ hNrho
  let q : A →* A ⧸ N := QuotientGroup.mk' N
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  have hcomp : rhoQ.comp q = chi.representation.ρ := by
    ext a x
    rfl
  letI : Representation.IsIrreducible (rhoQ.comp q) := by
    rw [hcomp]
    infer_instance
  letI : Representation.IsIrreducible rhoQ :=
    representation_isIrreducible_of_comp rhoQ q
  letI : CategoryTheory.Simple (FDRep.of rhoQ) :=
    simple_fdRep_of_isIrreducible rhoQ
  exact IrreducibleCharacter.ofFDRep (FDRep.of rhoQ)

@[simp]
private theorem pTypeReducibleQuotientDescendIrreducible_mk_apply
    {A : Type u} [Group A] [Fintype A]
    (N : Subgroup A) [N.Normal]
    (chi : IrreducibleCharacter A ℂ)
    (hN : N ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) (a : A) :
    pTypeReducibleQuotientDescendIrreducible N chi hN
        (QuotientGroup.mk' N a) = chi a := by
  simp only [pTypeReducibleQuotientDescendIrreducible,
    IrreducibleCharacter.ofFDRep_apply]
  change chi.representation.character a = chi a
  exact chi.representation_character a

/-- Descend an irreducible complex character along a finite surjection. -/
private noncomputable def pTypeReducibleDescendIrreducibleSurjective
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter A ℂ)
    (hker : f.ker ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) :
    IrreducibleCharacter B ℂ :=
  let chiQ := pTypeReducibleQuotientDescendIrreducible
    f.ker chi hker
  let e : (A ⧸ f.ker) ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  pTypeReducibleComapMulEquiv e.symm chiQ

@[simp]
private theorem pTypeReducibleDescendIrreducibleSurjective_apply
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (chi : IrreducibleCharacter A ℂ)
    (hker : f.ker ≤ ClassFunction.translationKernel
      (chi : ClassFunction A ℂ)) (a : A) :
    pTypeReducibleDescendIrreducibleSurjective f hf chi hker (f a) =
      chi a := by
  let chiQ := pTypeReducibleQuotientDescendIrreducible
    f.ker chi hker
  let e : (A ⧸ f.ker) ≃* B :=
    QuotientGroup.quotientKerEquivOfSurjective f hf
  change pTypeReducibleComapMulEquiv e.symm chiQ (f a) = chi a
  rw [pTypeReducibleComapMulEquiv_apply]
  have he : e (QuotientGroup.mk' f.ker a) = f a := rfl
  rw [← he, e.symm_apply_apply]
  exact pTypeReducibleQuotientDescendIrreducible_mk_apply
    f.ker chi hker a

/-- Irreducibility of a class function is reflected by pullback along a
finite surjection. -/
private theorem pTypeReducibleIrreducibleOfComapSurjective
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (f : A →* B) (hf : Function.Surjective f)
    (phi : ClassFunction B ℂ)
    (hirr : IsIrreducibleCharacter A ℂ
      (ClassFunction.comap f phi)) :
    IsIrreducibleCharacter B ℂ phi := by
  let chiA : IrreducibleCharacter A ℂ :=
    ⟨ClassFunction.comap f phi, hirr⟩
  let hker : f.ker ≤ ClassFunction.translationKernel
      (chiA : ClassFunction A ℂ) :=
    ClassFunction.ker_le_translationKernel_comap f phi
  let chiB : IrreducibleCharacter B ℂ :=
    pTypeReducibleDescendIrreducibleSurjective f hf chiA hker
  have hchiB : (chiB : ClassFunction B ℂ) = phi := by
    ext b
    obtain ⟨a, rfl⟩ := hf b
    exact pTypeReducibleDescendIrreducibleSurjective_apply
      f hf chiA hker a
  rw [← hchiB]
  exact chiB.property

/-- Induction is unchanged when the inducing subgroup is transported across
an equality. -/
private theorem pTypeReducibleInduce_subgroupCongr
    {A : Type u} [Group A] [Fintype A]
    (H K : Subgroup A) (hHK : H = K)
    (chi : IrreducibleCharacter K ℂ) :
    ClassFunction.induce H
        (pTypeReducibleComapMulEquiv
          (MulEquiv.subgroupCongr hHK) chi : ClassFunction H ℂ) =
      ClassFunction.induce K (chi : ClassFunction K ℂ) := by
  subst K
  apply congrArg (ClassFunction.induce H)
  ext x
  rw [pTypeReducibleComapMulEquiv_apply]
  apply congrArg (fun y : H ↦ chi y)
  apply Subtype.ext
  rfl

/-! ## Counting a quotient reducible layer -/

/-- If `K` cuts the F-core at `H₀`, its reducible induced layer is the
inflation of the nonprincipal quotient prime-TI columns. -/
private theorem pTypeReducibleLayer_card_of_quotient
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ K : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    [(K.subgroupOf M).Normal]
    (hKder : K ≤ derivedWithin M)
    (hKcap : K ⊓ Fitting_core M = Ptype_Fcore_kernel ctx) :
    let HU := (derivedWithin M).subgroupOf M
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let KHU := (K.subgroupOf M).subgroupOf HU
    (pTypeReducibleLayer HU H KHU).card =
      ptypeFactorPrime ctx - 1 := by
  classical
  let HU : Subgroup M := (derivedWithin M).subgroupOf M
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let KM : Subgroup M := K.subgroupOf M
  have hKMHU : KM ≤ HU := by
    intro x hx
    exact hKder hx
  let KHU : Subgroup HU := KM.subgroupOf HU
  change (pTypeReducibleLayer HU H KHU).card =
    ptypeFactorPrime ctx - 1
  let k : Type u := ULift.{u} ℂ
  let sigma : k ≃+* ℂ := ULift.ringEquiv
  letI : CharZero k :=
    CharZero.of_addMonoidHom sigma.symm.toAddMonoidHom
      sigma.symm.map_one sigma.symm.injective
  letI : IsAlgClosed k :=
    pTypeReducibleIsAlgClosedOfRingEquiv sigma
  let pd := FT_prDade_hypF ctx.defW ctx.maxM ctx.typeP
  let pti := pd.prDade_prTI
  let iso := pti.prime_cycTIhyp.cyclicTIIsometryData (k := k)
  let Q := primeTIQuotientGroup M K
  let q : M →* Q := QuotientGroup.mk' KM
  let Kq : Subgroup Q := primeTIQuotientImage M K (derivedWithin M)
  let KqT : Subgroup (⊤ : Subgroup Q) :=
    Kq.subgroupOf (⊤ : Subgroup Q)
  let W₂q : Subgroup Q := primeTIQuotientImage M K W₂
  letI : Invertible (Nat.card W₂q : k) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := W₂q)).ne')
  have hW₂qcard : Nat.card W₂q = ptypeFactorPrime ctx := by
    simpa only [W₂q, primeTIQuotientImage, KM] using
      ptypeW₂_quotient_image_card ctx hKder hKcap
  have hW₂qne : W₂q ≠ ⊥ := by
    apply W₂q.one_lt_card_iff_ne_bot.mp
    rw [hW₂qcard]
    exact (ptypeFactorPrime_prime ctx).one_lt
  obtain ⟨_defWq, ptiq⟩ :=
    PrimeTIHypothesis.quotient pti K hKder hW₂qne
  let isoq := ptiq.prime_cycTIhyp.cyclicTIIsometryData (k := k)
  let qT : M →* (⊤ : Subgroup Q) :=
    { toFun := fun x ↦ ⟨q x, Subgroup.mem_top _⟩
      map_one' := by
        apply Subtype.ext
        exact q.map_one
      map_mul' := by
        intro x y
        apply Subtype.ext
        exact q.map_mul x y }
  have hqTsurj : Function.Surjective qT := by
    intro y
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective KM (y : Q)
    exact ⟨x, Subtype.ext hx⟩
  have hqTkerHU : qT.ker ≤ HU := by
    intro x hx
    have hxq : q x = 1 := congrArg Subtype.val
      (MonoidHom.mem_ker.mp hx)
    have hxK : x ∈ KM := (QuotientGroup.eq_one_iff x).mp hxq
    exact hKder hxK
  have hKT : HU.map qT = KqT := by
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
    · rintro ⟨x, hx, hxy⟩
      exact ⟨x, hx, Subtype.ext hxy⟩
  let eKT : HU.map qT ≃* KqT := MulEquiv.subgroupCongr hKT
  let qK : HU →* HU.map qT := qT.subgroupMap HU
  have hqKsurj : Function.Surjective qK :=
    qT.subgroupMap_surjective HU
  have hqKker : qK.ker = KHU := by
    ext x
    constructor
    · intro hx
      have hxqT : qT x = 1 := congrArg Subtype.val
        (MonoidHom.mem_ker.mp hx)
      have hxq : q (x : M) = 1 := congrArg Subtype.val hxqT
      exact (QuotientGroup.eq_one_iff (x : M)).mp hxq
    · intro hx
      apply MonoidHom.mem_ker.mpr
      apply Subtype.ext
      apply Subtype.ext
      exact (QuotientGroup.eq_one_iff (x : M)).mpr hx
  let thetaQ (j : IrreducibleCharacter W₂q k) :
      IrreducibleCharacter KqT ℂ :=
    IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
      (ptiq.primeTI_Ires isoq j)
  let thetaMap (j : IrreducibleCharacter W₂q k) :
      IrreducibleCharacter (HU.map qT) ℂ :=
    pTypeReducibleComapMulEquiv eKT (thetaQ j)
  let thetaLift (j : IrreducibleCharacter W₂q k) :
      IrreducibleCharacter HU ℂ :=
    pTypeReducibleInflateIrreducible qK hqKsurj (thetaMap j)
  let muK (j : IrreducibleCharacter W₂q k) :
      ClassFunction M ℂ :=
    ClassFunction.comap qT
      (ClassFunction.mapRingHom sigma.toRingHom
        (ptiq.primeTIRed isoq j))
  have hthetaLiftClass (j : IrreducibleCharacter W₂q k) :
      ClassFunction.comap qK
          (thetaMap j : ClassFunction (HU.map qT) ℂ) =
        (thetaLift j : ClassFunction HU ℂ) := by
    ext x
    exact (pTypeReducibleInflateIrreducible_apply
      qK hqKsurj (thetaMap j) x).symm
  have hredDownInd (j : IrreducibleCharacter W₂q k) :
      ClassFunction.mapRingHom sigma.toRingHom
          (ptiq.primeTIRed isoq j) =
        ClassFunction.induce KqT
          (thetaQ j : ClassFunction KqT ℂ) := by
    rw [← ptiq.cfInd_prTIres isoq j,
      pTypeReducibleMapRingHom_induce,
      pTypeReducibleMapCoefficient_coe]
  have hmuKInd (j : IrreducibleCharacter W₂q k) :
      muK j = ClassFunction.induce HU
        (thetaLift j : ClassFunction HU ℂ) := by
    have hindTransport :
        ClassFunction.induce (HU.map qT)
            (thetaMap j : ClassFunction (HU.map qT) ℂ) =
          ClassFunction.induce KqT
            (thetaQ j : ClassFunction KqT ℂ) := by
      simpa only [thetaMap, eKT] using
        pTypeReducibleInduce_subgroupCongr
          (HU.map qT) KqT hKT (thetaQ j)
    change ClassFunction.comap qT
        (ClassFunction.mapRingHom sigma.toRingHom
          (ptiq.primeTIRed isoq j)) = _
    rw [hredDownInd, ← hindTransport,
      ClassFunction.comap_induce_surjective qT hqTsurj HU hqTkerHU,
      hthetaLiftClass]
  have hcomapInjective : Function.Injective
      (ClassFunction.comap qT :
        ClassFunction (⊤ : Subgroup Q) ℂ →
          ClassFunction M ℂ) :=
    ClassFunction.comap_injective qT hqTsurj
  have hmuKInjective : Function.Injective muK := by
    intro i j hij
    apply ptiq.prTIred_inj isoq
    apply pTypeReducibleMapRingHom_injective sigma
    apply hcomapInjective
    exact hij
  have hthetaLift_trivial :
      thetaLift
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂q k) =
        (IrreducibleCharacter.trivial : IrreducibleCharacter HU ℂ) := by
    have hthetaQ0 :
        thetaQ
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂q k) =
          (IrreducibleCharacter.trivial :
            IrreducibleCharacter KqT ℂ) := by
      change IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
          (ptiq.primeTI_Ires isoq
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂q k)) = _
      rw [ptiq.prTIres0 isoq,
        pTypeReducibleMapCoefficient_trivial]
    have hthetaMap0 :
        thetaMap
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂q k) =
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter (HU.map qT) ℂ) := by
      apply IrreducibleCharacter.ext
      intro y
      change pTypeReducibleComapMulEquiv eKT
          (thetaQ (IrreducibleCharacter.trivial :
            IrreducibleCharacter W₂q k)) y = _
      rw [hthetaQ0, pTypeReducibleComapMulEquiv_apply]
      simp
    apply IrreducibleCharacter.ext
    intro x
    change pTypeReducibleInflateIrreducible qK hqKsurj
        (thetaMap (IrreducibleCharacter.trivial :
          IrreducibleCharacter W₂q k)) x = _
    rw [pTypeReducibleInflateIrreducible_apply, hthetaMap0]
    simp
  have hred_muK (j : IrreducibleCharacter W₂q k) :
      ¬ IsIrreducibleCharacter M ℂ (muK j) := by
    intro hirr
    have hirrComap : IsIrreducibleCharacter M ℂ
        (ClassFunction.comap qT
          (ClassFunction.mapRingHom sigma.toRingHom
            (ptiq.primeTIRed isoq j))) := by
      simpa only [muK] using hirr
    have hirrDown : IsIrreducibleCharacter (⊤ : Subgroup Q) ℂ
        (ClassFunction.mapRingHom sigma.toRingHom
          (ptiq.primeTIRed isoq j)) :=
      pTypeReducibleIrreducibleOfComapSurjective
        qT hqTsurj _ hirrComap
    exact ptiq.prTIred_not_irr isoq j
      ((pTypeReducibleIsIrreducible_mapRingEquiv_iff sigma _).mp
        hirrDown)
  have hsignalizer : pd.signalizerInKernel = H := rfl
  have hthetaLift_mem
      (j : IrreducibleCharacter W₂q k)
      (hj : j ≠ IrreducibleCharacter.trivial) :
      thetaLift j ∈ Iirr_kerD (k := ℂ) H KHU := by
    rw [mem_Iirr_kerD]
    constructor
    · rw [← hqKker, ← hthetaLiftClass]
      exact ClassFunction.ker_le_translationKernel_comap qK _
    · intro hHker
      let thetaHigh : IrreducibleCharacter HU k :=
        IrreducibleCharacter.pTypeReducibleMapCoefficient sigma.symm
          (thetaLift j)
      have hthetaHighDown :
          IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
              thetaHigh = thetaLift j := by
        apply IrreducibleCharacter.ext
        intro g
        simp only [thetaHigh,
          IrreducibleCharacter.pTypeReducibleMapCoefficient_apply]
        exact sigma.apply_symm_apply _
      rcases pti.prTIres_irr_cases iso thetaHigh with
        ⟨j₁, hj₁⟩ | ⟨hirr, _⟩
      · have hj₁down : thetaLift j =
            IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
              (pti.primeTI_Ires iso j₁) := by
          rw [← hthetaHighDown, hj₁]
        have hj₁ne : j₁ ≠ IrreducibleCharacter.trivial := by
          intro hj₁0
          apply hj
          apply hmuKInjective
          calc
            muK j = ClassFunction.induce HU
                (thetaLift j : ClassFunction HU ℂ) := hmuKInd j
            _ = ClassFunction.induce HU
                (IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
                  (pti.primeTI_Ires iso j₁) :
                    ClassFunction HU ℂ) := by rw [hj₁down]
            _ = ClassFunction.mapRingHom sigma.toRingHom
                (ClassFunction.induce HU
                  (pti.primeTI_Ires iso j₁ : ClassFunction HU k)) := by
                    rw [pTypeReducibleMapRingHom_induce,
                      pTypeReducibleMapCoefficient_coe]
            _ = ClassFunction.mapRingHom sigma.toRingHom
                (pti.primeTIRed iso j₁) := by
                  rw [pti.cfInd_prTIres iso j₁]
            _ = ClassFunction.mapRingHom sigma.toRingHom
                (pti.primeTIRed iso
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂ k)) := by rw [hj₁0]
            _ = ClassFunction.mapRingHom sigma.toRingHom
                (ClassFunction.induce HU
                ((IrreducibleCharacter.trivial :
                  IrreducibleCharacter HU k) : ClassFunction HU k)) := by
                    rw [← pti.cfInd_prTIres iso, pti.prTIres0 iso]
            _ = ClassFunction.induce HU
                ((IrreducibleCharacter.trivial :
                  IrreducibleCharacter HU ℂ) : ClassFunction HU ℂ) := by
                    rw [pTypeReducibleMapRingHom_induce,
                      pTypeReducibleMapCoefficient_coe,
                      pTypeReducibleMapCoefficient_trivial]
            _ = ClassFunction.induce HU
                (thetaLift
                  (IrreducibleCharacter.trivial :
                    IrreducibleCharacter W₂q k) :
                      ClassFunction HU ℂ) := by rw [hthetaLift_trivial]
            _ = muK
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂q k) := (hmuKInd _).symm
        have hselectedKer : pd.signalizerInKernel ≤
            ClassFunction.translationKernel
              (pti.primeTI_Ires iso j₁ : ClassFunction HU k) := by
          rw [hsignalizer,
            ← pTypeReducibleTranslationKernel_mapRingEquiv sigma,
            pTypeReducibleMapCoefficient_coe,
            ← hj₁down]
          exact hHker
        exact pd.cfker_prTIres iso j₁ hj₁ne hselectedKer
      · have hirrDown : IsIrreducibleCharacter M ℂ
            (ClassFunction.mapRingHom sigma.toRingHom
              (ClassFunction.induce HU
                (thetaHigh : ClassFunction HU k))) :=
          (pTypeReducibleIsIrreducible_mapRingEquiv_iff sigma _).mpr hirr
        rw [pTypeReducibleMapRingHom_induce,
          pTypeReducibleMapCoefficient_coe, hthetaHighDown] at hirrDown
        apply hred_muK j
        rw [hmuKInd j]
        exact hirrDown
  have himage_subset :
      Finset.image muK
          (Finset.univ.erase
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂q k)) ⊆
        pTypeReducibleLayer HU H KHU := by
    intro phi hphi
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hphi
    have hjne : j ≠ IrreducibleCharacter.trivial :=
      (Finset.mem_erase.mp hj).1
    rw [pTypeReducibleLayer, Finset.mem_filter]
    refine ⟨seqIndP.mpr ⟨thetaLift j,
      hthetaLift_mem j hjne, hmuKInd j⟩, hred_muK j⟩
  have hlayer_subset :
      pTypeReducibleLayer HU H KHU ⊆
        Finset.image muK
          (Finset.univ.erase
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂q k)) := by
    intro phi hphi
    rw [pTypeReducibleLayer, Finset.mem_filter] at hphi
    obtain ⟨hphiSeq, hphiRed⟩ := hphi
    obtain ⟨theta, htheta, hphiInd⟩ := seqIndP.mp hphiSeq
    have hqKkerTheta : qK.ker ≤
        ClassFunction.translationKernel
          (theta : ClassFunction HU ℂ) := by
      rw [hqKker]
      exact (mem_Iirr_kerD.mp htheta).1
    let thetaMapCF : ClassFunction (HU.map qT) ℂ :=
      ClassFunction.descend qK hqKsurj
        (theta : ClassFunction HU ℂ) hqKkerTheta
    have hcomapTheta : ClassFunction.comap qK thetaMapCF =
        (theta : ClassFunction HU ℂ) :=
      ClassFunction.comap_descend qK hqKsurj
        (theta : ClassFunction HU ℂ) hqKkerTheta
    have hthetaMapIrr : IsIrreducibleCharacter (HU.map qT) ℂ
        thetaMapCF := by
      apply pTypeReducibleIrreducibleOfComapSurjective qK hqKsurj
      rw [hcomapTheta]
      exact theta.property
    let thetaMap' : IrreducibleCharacter (HU.map qT) ℂ :=
      ⟨thetaMapCF, hthetaMapIrr⟩
    let thetaQ' : IrreducibleCharacter KqT ℂ :=
      pTypeReducibleComapMulEquiv eKT.symm thetaMap'
    have hthetaRoundtrip :
        pTypeReducibleComapMulEquiv eKT thetaQ' = thetaMap' := by
      apply IrreducibleCharacter.ext
      intro y
      simp only [thetaQ', pTypeReducibleComapMulEquiv_apply,
        eKT.symm_apply_apply]
    have hindTransport :
        ClassFunction.induce (HU.map qT)
            (thetaMap' : ClassFunction (HU.map qT) ℂ) =
          ClassFunction.induce KqT
            (thetaQ' : ClassFunction KqT ℂ) := by
      rw [← hthetaRoundtrip]
      exact pTypeReducibleInduce_subgroupCongr
        (HU.map qT) KqT hKT thetaQ'
    have hinflateInd :
        ClassFunction.comap qT
            (ClassFunction.induce KqT
              (thetaQ' : ClassFunction KqT ℂ)) =
          ClassFunction.induce HU
            (theta : ClassFunction HU ℂ) := by
      rw [← hindTransport,
        ClassFunction.comap_induce_surjective qT hqTsurj HU hqTkerHU]
      change ClassFunction.induce HU
          (ClassFunction.comap qK
            (thetaMap' : ClassFunction (HU.map qT) ℂ)) =
        ClassFunction.induce HU (theta : ClassFunction HU ℂ)
      rw [show (thetaMap' : ClassFunction (HU.map qT) ℂ) =
          thetaMapCF from rfl, hcomapTheta]
    let thetaQHigh' : IrreducibleCharacter KqT k :=
      IrreducibleCharacter.pTypeReducibleMapCoefficient sigma.symm thetaQ'
    have hthetaQHighDown :
        IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
            thetaQHigh' = thetaQ' := by
      apply IrreducibleCharacter.ext
      intro g
      simp only [thetaQHigh',
        IrreducibleCharacter.pTypeReducibleMapCoefficient_apply]
      exact sigma.apply_symm_apply _
    rcases ptiq.prTIres_irr_cases isoq thetaQHigh' with
      ⟨j, hj⟩ | ⟨hirrQ, _⟩
    · have hthetaQSelected : thetaQ' = thetaQ j := by
        calc
          thetaQ' =
              IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
                thetaQHigh' := hthetaQHighDown.symm
          _ = IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
                (ptiq.primeTI_Ires isoq j) := by rw [hj]
          _ = thetaQ j := rfl
      have hjne : j ≠ IrreducibleCharacter.trivial := by
        intro hj0
        have hthetaQ0 : thetaQ' =
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter KqT ℂ) := by
          rw [hthetaQSelected, hj0]
          change IrreducibleCharacter.pTypeReducibleMapCoefficient sigma
              (ptiq.primeTI_Ires isoq
                (IrreducibleCharacter.trivial :
                  IrreducibleCharacter W₂q k)) = _
          rw [ptiq.prTIres0 isoq,
            pTypeReducibleMapCoefficient_trivial]
        have hthetaMap0 : thetaMap' =
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter (HU.map qT) ℂ) := by
          rw [← hthetaRoundtrip, hthetaQ0]
          apply IrreducibleCharacter.ext
          intro y
          rw [pTypeReducibleComapMulEquiv_apply]
          simp
        have htheta0 : theta =
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter HU ℂ) := by
          apply IrreducibleCharacter.ext
          intro x
          have hx := congrArg
            (fun f : ClassFunction HU ℂ ↦ f x) hcomapTheta
          have hx0 := congrArg
            (fun chi : IrreducibleCharacter (HU.map qT) ℂ ↦ chi (qK x))
            hthetaMap0
          change thetaMapCF (qK x) = _ at hx0
          exact hx.symm.trans hx0
        apply (mem_Iirr_kerD.mp htheta).2
        rw [htheta0]
        intro x hx y
        simp
      apply Finset.mem_image.mpr
      refine ⟨j, Finset.mem_erase.mpr
        ⟨hjne, Finset.mem_univ j⟩, ?_⟩
      calc
        muK j = ClassFunction.comap qT
            (ClassFunction.induce KqT
              (thetaQ j : ClassFunction KqT ℂ)) := by
                change ClassFunction.comap qT
                    (ClassFunction.mapRingHom sigma.toRingHom
                      (ptiq.primeTIRed isoq j)) = _
                rw [hredDownInd]
        _ = ClassFunction.comap qT
            (ClassFunction.induce KqT
              (thetaQ' : ClassFunction KqT ℂ)) := by
                rw [hthetaQSelected]
        _ = ClassFunction.induce HU
            (theta : ClassFunction HU ℂ) := hinflateInd
        _ = phi := hphiInd.symm
    · have hirrQDown : IsIrreducibleCharacter (⊤ : Subgroup Q) ℂ
          (ClassFunction.mapRingHom sigma.toRingHom
            (ClassFunction.induce KqT
              (thetaQHigh' : ClassFunction KqT k))) :=
        (pTypeReducibleIsIrreducible_mapRingEquiv_iff sigma _).mpr hirrQ
      rw [pTypeReducibleMapRingHom_induce,
        pTypeReducibleMapCoefficient_coe,
        hthetaQHighDown] at hirrQDown
      have hirrComap : IsIrreducibleCharacter M ℂ
          (ClassFunction.comap qT
            (ClassFunction.induce KqT
              (thetaQ' : ClassFunction KqT ℂ))) := by
        let chiQ : IrreducibleCharacter (⊤ : Subgroup Q) ℂ :=
          ⟨ClassFunction.induce KqT
              (thetaQ' : ClassFunction KqT ℂ), hirrQDown⟩
        let chiM : IrreducibleCharacter M ℂ :=
          pTypeReducibleInflateIrreducible qT hqTsurj chiQ
        have hchiM : (chiM : ClassFunction M ℂ) =
            ClassFunction.comap qT
              (ClassFunction.induce KqT
                (thetaQ' : ClassFunction KqT ℂ)) := by
          ext x
          exact pTypeReducibleInflateIrreducible_apply
            qT hqTsurj chiQ x
        rw [← hchiM]
        exact chiM.property
      exfalso
      apply hphiRed
      rw [hphiInd, ← hinflateInd]
      exact hirrComap
  have himage :
      Finset.image muK
          (Finset.univ.erase
            (IrreducibleCharacter.trivial :
              IrreducibleCharacter W₂q k)) =
        pTypeReducibleLayer HU H KHU :=
    Finset.Subset.antisymm himage_subset hlayer_subset
  rw [← himage,
    Finset.card_image_iff.mpr
      (Set.injOn_of_injective hmuKInjective),
    Finset.card_erase_of_mem (Finset.mem_univ
      (IrreducibleCharacter.trivial :
        IrreducibleCharacter W₂q k)),
    Finset.card_univ]
  letI : IsCyclic W₂q := ptiq.fixed_cyclic
  rw [IrreducibleCharacter.card_eq_natCard_of_isCyclic, hW₂qcard]

/-! ## The F-core kernel and the enlarged kernel -/

/-- The reducible layer for the selected F-core kernel has size `p - 1`. -/
private theorem pTypeReducibleLayer_card_FcoreKernel
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂) :
    (pTypeReducibleLayer
      ((derivedWithin M).subgroupOf M)
      (((Fitting_core M).subgroupOf M).subgroupOf
        ((derivedWithin M).subgroupOf M))
      (((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf
        ((derivedWithin M).subgroupOf M))).card =
      ptypeFactorPrime ctx - 1 := by
  letI : ((Ptype_Fcore_kernel ctx).subgroupOf M).Normal :=
    Ptype_Fcore_kernel_normal_M ctx
  have hH₀H : Ptype_Fcore_kernel ctx ≤ Fitting_core M :=
    (Ptype_Fcore_kernel_lt ctx).le
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  exact pTypeReducibleLayer_card_of_quotient ctx
    (hH₀H.trans hHder) (inf_eq_left.mpr hH₀H)

/-- The same count, expressed using the canonical action datum. -/
private theorem pTypeReducibleLayer_card_action
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    (pTypeReducibleLayer
      ((derivedWithin M).subgroupOf M)
      (((Fitting_core M).subgroupOf M).subgroupOf
        ((derivedWithin M).subgroupOf M))
      (((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf
        ((derivedWithin M).subgroupOf M))).card =
      (Ptype_factor_action ctx facts).p - 1 := by
  simpa only [Ptype_factor_action_p] using
    pTypeReducibleLayer_card_FcoreKernel ctx

/-- Every reducible member of the `H₀` layer belongs to the Dade-induced
family for the enlarged kernel `H₀C`. -/
private theorem pTypeReducibleLayer_subset_H0CSeqInd
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := (derivedWithin M).subgroupOf M
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    ∀ phi ∈ pTypeReducibleLayer HU H H₀,
      phi ∈ seqIndD (k := ℂ) HU H H₀C := by
  classical
  let D := Ptype_factor_action ctx facts
  let HU : Subgroup M := (derivedWithin M).subgroupOf M
  let H : Subgroup HU :=
    ((Fitting_core M).subgroupOf M).subgroupOf HU
  let H₀a := Ptype_Fcore_kernel ctx
  let C := Ptype_Fcompl_kernel ctx
  let Ka : Subgroup Gamma := H₀a ⊔ C
  let H₀ : Subgroup HU := (H₀a.subgroupOf M).subgroupOf HU
  let H₀C : Subgroup HU := pTypeH0CInDerived M (derivedWithin M)
    H₀a U W₁ D
  change ∀ phi ∈ pTypeReducibleLayer HU H H₀,
    phi ∈ seqIndD (k := ℂ) HU H H₀C
  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hH₀H : H₀a ≤ Fitting_core M :=
    (Ptype_Fcore_kernel_lt ctx).le
  have hH₀der : H₀a ≤ derivedWithin M := hH₀H.trans hHder
  have hCder : C ≤ derivedWithin M :=
    (Ptype_Fcompl_kernel_le ctx).trans hUder
  have hKder : Ka ≤ derivedWithin M := sup_le hH₀der hCder
  have hKaM : Ka ≤ M :=
    (Ptype_Fcore_extensions_normal ctx).H₀C_normal.1
  letI : (Ka.subgroupOf M).Normal :=
    (Ptype_Fcore_extensions_normal ctx).H₀C_normal.2
  have hH₀M : H₀a ≤ M := hH₀der.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  have hCM : C ≤ M := hCder.trans
    (Subgroup.map_subtype_le (_root_.commutator M))
  have hH₀HU : H₀a.subgroupOf M ≤ HU := by
    intro x hx
    exact hH₀der hx
  have hCHU : C.subgroupOf M ≤ HU := by
    intro x hx
    exact hCder hx
  have hH₀Ceq : H₀C = (Ka.subgroupOf M).subgroupOf HU := by
    change (H₀a.subgroupOf M).subgroupOf HU ⊔
        (((D.C.map U.subtype).subgroupOf M).subgroupOf HU) =
      (Ka.subgroupOf M).subgroupOf HU
    have hDC : D.C.map U.subtype = C := rfl
    rw [hDC, ← Subgroup.subgroupOf_sup hH₀HU hCHU,
      ← Subgroup.subgroupOf_sup hH₀M hCM]
  have hcard₀ : (pTypeReducibleLayer HU H H₀).card =
      ptypeFactorPrime ctx - 1 := by
    simpa only [HU, H, H₀, H₀a] using
      pTypeReducibleLayer_card_FcoreKernel ctx
  have hcardC : (pTypeReducibleLayer HU H H₀C).card =
      ptypeFactorPrime ctx - 1 := by
    have hcard := pTypeReducibleLayer_card_of_quotient ctx hKder
      (internal.pTypeFcoreKernel_sup_complKernel_inf_Fcore ctx)
    rw [hH₀Ceq]
    exact hcard
  have hCsub₀ : pTypeReducibleLayer HU H H₀C ⊆
      pTypeReducibleLayer HU H H₀ := by
    intro phi hphi
    rw [pTypeReducibleLayer, Finset.mem_filter] at hphi ⊢
    refine ⟨seqIndS HU
      (Iirr_kerDS (k := ℂ) (A₁ := H₀C) (A₂ := H₀)
        (B₁ := H) (B₂ := H) le_sup_left le_rfl) hphi.1,
      hphi.2⟩
  have heq : pTypeReducibleLayer HU H H₀C =
      pTypeReducibleLayer HU H H₀ :=
    Finset.eq_of_subset_of_card_le hCsub₀ (by
      rw [hcardC, hcard₀])
  intro phi hphi
  have hphiC : phi ∈ pTypeReducibleLayer HU H H₀C := by
    rw [heq]
    exact hphi
  exact (Finset.mem_filter.mp hphiC).1

/-- The source endpoint `nb_redM_H0`: the reducible `H₀` layer has
cardinality `p - 1`, and all its members already belong to `S_(H₀C)`. -/
theorem pType_nb_redM_H0
    {Gamma : Type u} [Group Gamma] [Fintype Gamma]
    [IsMinSimpleOddGroup Gamma]
    {M U W W₁ W₂ : Subgroup Gamma}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx) :
    let D := Ptype_factor_action ctx facts
    let HU := (derivedWithin M).subgroupOf M
    let H := ((Fitting_core M).subgroupOf M).subgroupOf HU
    let H₀ := ((Ptype_Fcore_kernel ctx).subgroupOf M).subgroupOf HU
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    (pTypeReducibleLayer HU H H₀).card = D.p - 1 ∧
      ∀ phi ∈ pTypeReducibleLayer HU H H₀,
        phi ∈ seqIndD (k := ℂ) HU H H₀C := by
  exact ⟨pTypeReducibleLayer_card_action ctx facts,
    pTypeReducibleLayer_subset_H0CSeqInd ctx facts⟩

end

end Submission.OddOrder.PF
