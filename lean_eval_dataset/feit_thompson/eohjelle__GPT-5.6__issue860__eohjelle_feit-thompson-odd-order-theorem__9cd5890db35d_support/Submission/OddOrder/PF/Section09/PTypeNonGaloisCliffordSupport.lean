import Submission.OddOrder.PF.Section09.PTypeNonGaloisInertiaExtensions

/-!
# Peterfalvi Section 9: split-universe Clifford support

The Section 1 Clifford APIs place the finite group and coefficient field in
one universe.  This module lifts `ℂ` to the group universe, transports the
character operations needed by the non-Galois twist argument, invokes the
same-universe Clifford theorems, and descends their conclusions.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

open CategoryTheory Limits

universe u v w x

namespace PTypeNonGaloisCliffordSupportInternal

/-! ## Minimal coefficient transport -/

namespace FDRep

private instance pTypeUliftCliffordRepInjective
    {A : Type u} {R : Type v} [Group A] [Finite A] [Field R]
    [NeZero (Nat.card A : R)] (V : Rep.{x} R A) : Injective V := by
  rw [← Rep.equivalenceModuleMonoidAlgebra.map_injective_iff,
    ← Module.injective_iff_injective_object]
  exact Module.injective_of_isSemisimpleRing _ _

private instance pTypeUliftCliffordFDRepInjective
    {A : Type u} {R : Type v} [Group A] [Finite A] [Field R]
    [NeZero (Nat.card A : R)] (V : FDRep R A) : Injective V :=
  (forget₂ (FDRep R A) (Rep R A)).injective_of_map_injective inferInstance

private theorem pTypeUliftCliffordSimple_iff_end_rank_one
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

private theorem pTypeUliftCliffordSimple_iff_char_norm_one
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
    rw [pTypeUliftCliffordSimple_iff_end_rank_one,
      ← Nat.cast_inj (R := R), ← eq, Nat.cast_one]

private def pTypeUliftCliffordCoefficientTransport
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Field R] [Field S]
    (σ : R ≃+* S) (V : FDRep R A) : FDRep S A :=
  let b := Module.finBasis R V
  FDRep.of
    (Matrix.toLinAlgEquiv'.toMonoidHom.comp
      (σ.mapMatrix.toMonoidHom.comp
        ((LinearMap.toMatrixAlgEquiv b).toMonoidHom.comp V.ρ)))

@[simp] private theorem pTypeUliftCliffordCoefficientTransport_character
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Field R] [Field S]
    (σ : R ≃+* S) (V : FDRep R A) (a : A) :
    (pTypeUliftCliffordCoefficientTransport σ V).character a =
      σ (V.character a) := by
  let b := Module.finBasis R V
  change LinearMap.trace S _
      (Matrix.toLinAlgEquiv'
        (σ.mapMatrix (LinearMap.toMatrixAlgEquiv b (V.ρ a)))) =
    σ (LinearMap.trace R V (V.ρ a))
  change LinearMap.trace S _
      (Matrix.toLin'
        (σ.mapMatrix (LinearMap.toMatrixAlgEquiv b (V.ρ a)))) = _
  rw [Matrix.trace_toLin'_eq,
    LinearMap.trace_eq_matrix_trace R b,
    AddMonoidHom.map_trace]
  rfl

private theorem pTypeUliftCliffordCoefficientTransport_simple
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A]
    [Field R] [Field S] [IsAlgClosed R] [IsAlgClosed S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (V : FDRep R A) [Simple V] :
    Simple (pTypeUliftCliffordCoefficientTransport σ V) := by
  rw [pTypeUliftCliffordSimple_iff_char_norm_one]
  have hV :=
    (pTypeUliftCliffordSimple_iff_char_norm_one V).mp (by infer_instance)
  simp only [pTypeUliftCliffordCoefficientTransport_character,
    ← map_mul, ← map_sum, hV]
  exact map_natCast σ (Nat.card A)

end FDRep

private noncomputable def pTypeUliftCliffordMapCoefficient
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A]
    [Field R] [Field S] [IsAlgClosed R] [IsAlgClosed S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (chi : IrreducibleCharacter A R) :
    IrreducibleCharacter A S := by
  letI : Simple chi.representation := chi.representation_simple
  letI : Simple
      (FDRep.pTypeUliftCliffordCoefficientTransport
        σ chi.representation) :=
    FDRep.pTypeUliftCliffordCoefficientTransport_simple
      σ chi.representation
  exact IrreducibleCharacter.ofFDRep
    (FDRep.pTypeUliftCliffordCoefficientTransport σ chi.representation)

@[simp] private theorem pTypeUliftCliffordMapCoefficient_apply
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A]
    [Field R] [Field S] [IsAlgClosed R] [IsAlgClosed S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (chi : IrreducibleCharacter A R) (a : A) :
    pTypeUliftCliffordMapCoefficient σ chi a = σ (chi a) := by
  letI : Simple chi.representation := chi.representation_simple
  letI : Simple
      (FDRep.pTypeUliftCliffordCoefficientTransport
        σ chi.representation) :=
    FDRep.pTypeUliftCliffordCoefficientTransport_simple
      σ chi.representation
  simp only [pTypeUliftCliffordMapCoefficient,
    IrreducibleCharacter.ofFDRep_apply,
    FDRep.pTypeUliftCliffordCoefficientTransport_character,
    IrreducibleCharacter.representation_character]

private theorem pTypeUliftCliffordIsAlgClosedOfRingEquiv
    {R : Type v} {S : Type w} [Field R] [Field S]
    (σ : R ≃+* S) [IsAlgClosed S] : IsAlgClosed R := by
  apply IsAlgClosed.of_exists_root
  intro p hmp hp
  have hdegree : Polynomial.degree (p.map σ.toRingHom) ≠ 0 := by
    rw [Polynomial.degree_map]
    exact ne_of_gt (Polynomial.degree_pos_of_irreducible hp)
  rcases IsAlgClosed.exists_root (k := S)
      (p.map σ.toRingHom) hdegree with ⟨z, hz⟩
  use σ.symm z
  rw [Polynomial.IsRoot] at hz
  apply σ.injective
  rw [map_zero, ← hz]
  clear hz hdegree hp hmp
  induction p using Polynomial.induction_on <;> simp_all

private theorem pTypeUliftCliffordMapRingHom_induce
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A] [Field R] [Field S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (K : Subgroup A) (f : ClassFunction K R) :
    ClassFunction.mapRingHom σ.toRingHom (ClassFunction.induce K f) =
      ClassFunction.induce K
        (ClassFunction.mapRingHom σ.toRingHom f) := by
  classical
  ext a
  rw [ClassFunction.mapRingHom_apply,
    ClassFunction.induce_apply_formula,
    ClassFunction.induce_apply_formula,
    map_mul, map_inv₀, map_natCast, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro y _
  by_cases hy : y⁻¹ * a * y ∈ K
  · rw [dif_pos hy, dif_pos hy, ClassFunction.mapRingHom_apply]
  · rw [dif_neg hy, dif_neg hy, map_zero]

private theorem pTypeUliftCliffordMapRingHom_restrict
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Field R] [Field S]
    (σ : R ≃+* S) (K : Subgroup A) (f : ClassFunction A R) :
    ClassFunction.mapRingHom σ.toRingHom
        (ClassFunction.restrict K f) =
      ClassFunction.restrict K
        (ClassFunction.mapRingHom σ.toRingHom f) := by
  ext x
  rfl

private theorem pTypeUliftCliffordMapRingHom_normalConjugate
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Field R] [Field S]
    (σ : R ≃+* S) (K : Subgroup A) [K.Normal]
    (a : A) (f : ClassFunction K R) :
    ClassFunction.mapRingHom σ.toRingHom
        (ClassFunction.normalConjugate K a f) =
      ClassFunction.normalConjugate K a
        (ClassFunction.mapRingHom σ.toRingHom f) := by
  ext x
  rfl

private theorem pTypeUliftCliffordCharacterPairing_mapRingEquiv
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A] [Field R] [Field S]
    (σ : R ≃+* S) (f g : ClassFunction A R) :
    characterPairing
        (ClassFunction.mapRingHom σ.toRingHom f)
        (ClassFunction.mapRingHom σ.toRingHom g) =
      σ (characterPairing f g) := by
  simp only [characterPairing, ClassFunction.mapRingHom_apply,
    map_mul, map_inv₀, map_natCast, map_sum]
  rfl

@[simp] private theorem pTypeUliftCliffordMapCoefficient_coe
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A]
    [Field R] [Field S] [IsAlgClosed R] [IsAlgClosed S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (chi : IrreducibleCharacter A R) :
    ClassFunction.mapRingHom σ.toRingHom
        (chi : ClassFunction A R) =
      (pTypeUliftCliffordMapCoefficient σ chi : ClassFunction A S) := by
  ext a
  simp

private theorem pTypeUliftCliffordMapRingHom_isIrreducible
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A]
    [Field R] [Field S] [IsAlgClosed R] [IsAlgClosed S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (f : ClassFunction A R)
    (hf : IsIrreducibleCharacter A R f) :
    IsIrreducibleCharacter A S
      (ClassFunction.mapRingHom σ.toRingHom f) := by
  let chi : IrreducibleCharacter A R := ⟨f, hf⟩
  change IsIrreducibleCharacter A S
    (ClassFunction.mapRingHom σ.toRingHom
      (chi : ClassFunction A R))
  rw [pTypeUliftCliffordMapCoefficient_coe]
  exact (pTypeUliftCliffordMapCoefficient σ chi).property

private theorem pTypeUliftCliffordMapRingHom_injective
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Field R] [Field S] (σ : R ≃+* S) :
    Function.Injective
      (ClassFunction.mapRingHom σ.toRingHom :
        ClassFunction A R → ClassFunction A S) := by
  intro f g h
  ext a
  apply σ.injective
  exact congrArg (fun q : ClassFunction A S ↦ q a) h

private theorem pTypeUliftCliffordMapCoefficient_isConstituent
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A]
    [Field R] [Field S] [IsAlgClosed R] [IsAlgClosed S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (chi : IrreducibleCharacter A R)
    (f : ClassFunction A R) (hchi : chi.IsConstituent f) :
    (pTypeUliftCliffordMapCoefficient σ chi).IsConstituent
      (ClassFunction.mapRingHom σ.toRingHom f) := by
  unfold IrreducibleCharacter.IsConstituent at hchi ⊢
  rw [← pTypeUliftCliffordMapCoefficient_coe,
    pTypeUliftCliffordCharacterPairing_mapRingEquiv]
  exact σ.map_ne_zero_iff.mpr hchi

private theorem pTypeUliftCliffordMapCoefficient_inertia
    {A : Type u} {R : Type v} {S : Type w}
    [Group A] [Fintype A]
    [Field R] [Field S] [IsAlgClosed R] [IsAlgClosed S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (H : Subgroup A) [H.Normal]
    (theta : IrreducibleCharacter H R) :
    ClassFunction.inertia H
        (pTypeUliftCliffordMapCoefficient σ theta : ClassFunction H S) =
      ClassFunction.inertia H (theta : ClassFunction H R) := by
  ext a
  rw [ClassFunction.mem_inertia_iff, ClassFunction.mem_inertia_iff]
  constructor
  · intro ha
    apply ClassFunction.ext
    intro h
    have hh := congrArg
      (fun f : ClassFunction H S ↦ f h) ha
    change pTypeUliftCliffordMapCoefficient σ theta
        ((MulAut.conjNormal a).symm h) =
      pTypeUliftCliffordMapCoefficient σ theta h at hh
    rw [pTypeUliftCliffordMapCoefficient_apply,
      pTypeUliftCliffordMapCoefficient_apply] at hh
    exact σ.injective hh
  · intro ha
    apply ClassFunction.ext
    intro h
    have hh := congrArg
      (fun f : ClassFunction H R ↦ f h) ha
    change theta ((MulAut.conjNormal a).symm h) = theta h at hh
    change pTypeUliftCliffordMapCoefficient σ theta
        ((MulAut.conjNormal a).symm h) =
      pTypeUliftCliffordMapCoefficient σ theta h
    rw [pTypeUliftCliffordMapCoefficient_apply,
      pTypeUliftCliffordMapCoefficient_apply]
    exact congrArg σ hh

private theorem pTypeUliftCliffordInduceComapSubgroupCongr
    {A R : Type u}
    [Group A] [Fintype A] [Field R] [IsAlgClosed R] [CharZero R]
    (H K : Subgroup A) (hHK : H = K)
    (chi : IrreducibleCharacter K R) :
    ClassFunction.induce H
        (IrreducibleCharacter.comapMulEquiv
          (MulEquiv.subgroupCongr hHK) chi : ClassFunction H R) =
      ClassFunction.induce K (chi : ClassFunction K R) := by
  subst K
  apply congrArg (ClassFunction.induce H)
  ext x
  rw [IrreducibleCharacter.comapMulEquiv_apply]
  apply congrArg (fun y : H ↦ chi y)
  apply Subtype.ext
  rfl

private theorem pTypeUliftCliffordInduceComapSubgroupCongrClassFunction
    {A : Type u} {R : Type v}
    [Group A] [Fintype A] [Field R] [CharZero R]
    (H K : Subgroup A) (hHK : H = K) (f : ClassFunction K R) :
    ClassFunction.induce H
        (ClassFunction.comap
          (MulEquiv.subgroupCongr hHK).toMonoidHom f) =
      ClassFunction.induce K f := by
  subst K
  apply congrArg (ClassFunction.induce H)
  ext x
  rfl

private def pTypeUliftCliffordTransportIrreducible
    {A : Type u} {R : Type v}
    [Group A] [Field R]
    (H K : Subgroup A) (hHK : H = K)
    (chi : IrreducibleCharacter H R) :
    IrreducibleCharacter K R :=
  hHK ▸ chi

private theorem pTypeUliftCliffordInduceTransportIrreducible
    {A : Type u} {R : Type v}
    [Group A] [Fintype A] [Field R]
    (H K : Subgroup A) (hHK : H = K)
    (chi : IrreducibleCharacter H R) :
    ClassFunction.induce H (chi : ClassFunction H R) =
      ClassFunction.induce K
        (pTypeUliftCliffordTransportIrreducible
          H K hHK chi : ClassFunction K R) := by
  subst K
  rfl

/-! ## Same-universe character consequences used after lifting -/

private theorem pTypeUliftCliffordVirtualCharacter_ofFDRep_apply
    {A R : Type u} [Group A] [Fintype A]
    [Field R] [IsAlgClosed R] [CharZero R]
    (V : FDRep R A) (chi : IrreducibleCharacter A R) :
    VirtualCharacter.ofFDRep V chi = (chi.multiplicity V : ℤ) := by
  simp [VirtualCharacter.ofFDRep]

private theorem pTypeUliftCliffordConstituents_disjoint_of_pairing_eq_zero
    {A R : Type u} [Group A] [Fintype A]
    [Field R] [IsAlgClosed R] [CharZero R]
    (V W : FDRep R A)
    (hpair : characterPairing
      (ClassFunction.ofRepresentation V.ρ)
      (ClassFunction.ofRepresentation W.ρ) = 0) :
    Disjoint
      (ClassFunction.constituents
        (ClassFunction.ofRepresentation V.ρ) :
          Set (IrreducibleCharacter A R))
      (ClassFunction.constituents
        (ClassFunction.ofRepresentation W.ρ) :
          Set (IrreducibleCharacter A R)) := by
  rw [Set.disjoint_left]
  intro chi hchiV hchiW
  let zV := VirtualCharacter.ofFDRep V
  let zW := VirtualCharacter.ofFDRep W
  have hmultV : 0 < chi.multiplicity V :=
    (chi.isConstituent_ofRepresentation_iff_multiplicity_pos V).mp
      ((ClassFunction.mem_constituents_iff _ _).mp hchiV)
  have hmultW : 0 < chi.multiplicity W :=
    (chi.isConstituent_ofRepresentation_iff_multiplicity_pos W).mp
      ((ClassFunction.mem_constituents_iff _ _).mp hchiW)
  have hchiSupport : chi ∈ zV.support := by
    rw [Finsupp.mem_support_iff]
    simpa [zV, pTypeUliftCliffordVirtualCharacter_ofFDRep_apply] using
      hmultV.ne'
  have htermPos : 0 < zV chi * zW chi := by
    rw [pTypeUliftCliffordVirtualCharacter_ofFDRep_apply,
      pTypeUliftCliffordVirtualCharacter_ofFDRep_apply]
    exact mul_pos (by exact_mod_cast hmultV) (by exact_mod_cast hmultW)
  have htermsNonneg : ∀ eta ∈ zV.support,
      0 ≤ zV eta * zW eta := by
    intro eta _
    rw [pTypeUliftCliffordVirtualCharacter_ofFDRep_apply,
      pTypeUliftCliffordVirtualCharacter_ofFDRep_apply]
    positivity
  have hdotPos : 0 < coeffDot zV zW := by
    unfold coeffDot
    change 0 < ∑ eta ∈ zV.support, zV eta * zW eta
    exact lt_of_lt_of_le htermPos
      (Finset.single_le_sum htermsNonneg hchiSupport)
  have hdotCast : (coeffDot zV zW : R) = 0 := by
    have hrealize := VirtualCharacter.characterPairing_realize zV zW
    rw [VirtualCharacter.realize_ofFDRep,
      VirtualCharacter.realize_ofFDRep, hpair] at hrealize
    exact hrealize.symm
  have hdotZero : coeffDot zV zW = 0 := by
    apply Int.cast_injective (α := R)
    simpa only [Int.cast_zero] using hdotCast
  omega

private theorem pTypeUliftCliffordInertiaConstituent_of_restrict
    {A R : Type u} [Group A] [Fintype A]
    [Field R] [IsAlgClosed R] [CharZero R]
    (H : Subgroup A) [H.Normal]
    (theta : IrreducibleCharacter H R)
    (psi : IrreducibleCharacter
      (ClassFunction.inertia H (theta : ClassFunction H R)) R)
    (hrestrict :
      let I := ClassFunction.inertia H (theta : ClassFunction H R)
      let HI := H.subgroupOf I
      ClassFunction.restrict HI (psi : ClassFunction I R) =
        (ClassFunction.inertiaSubgroupCharacter H theta :
          ClassFunction HI R)) :
    psi ∈ ClassFunction.inertiaConstituents H theta := by
  let I := ClassFunction.inertia H (theta : ClassFunction H R)
  let HI := H.subgroupOf I
  let thetaI := ClassFunction.inertiaSubgroupCharacter H theta
  let V : FDRep R I :=
    FDRep.induceFromSubgroup HI thetaI.representation
  let F : ClassFunction I R := ClassFunction.ofRepresentation V.ρ
  have hF : F = ClassFunction.induce HI
      (thetaI : ClassFunction HI R) := by
    dsimp only [F, V]
    exact (ClassFunction.ofRepresentation_induceFromSubgroup_general
      HI thetaI.representation).trans
        (congrArg (ClassFunction.induce HI)
          thetaI.ofRepresentation_representation)
  letI : Invertible (Nat.card HI : R) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := HI)).ne')
  have hpair : characterPairing F (psi : ClassFunction I R) = 1 := by
    rw [hF, ClassFunction.frobeniusReciprocity HI, hrestrict]
    exact IrreducibleCharacter.characterPairing_self thetaI
  apply (ClassFunction.mem_constituents_iff F psi).2
  unfold IrreducibleCharacter.IsConstituent
  rw [hpair]
  exact one_ne_zero

/-! ## Restriction transport across the equality of inertia subgroups -/

private theorem pTypeUliftCliffordMapCoefficient_inertiaExtension_restrict
    {A S : Type u} {R : Type v}
    [Group A] [Fintype A]
    [Field R] [Field S] [IsAlgClosed R] [IsAlgClosed S]
    [CharZero R] [CharZero S]
    (σ : R ≃+* S) (H : Subgroup A) [H.Normal]
    (theta : IrreducibleCharacter H R)
    (psi : IrreducibleCharacter
      (ClassFunction.inertia H (theta : ClassFunction H R)) R)
    (hrestrict :
      let I := ClassFunction.inertia H (theta : ClassFunction H R)
      let HI := H.subgroupOf I
      ClassFunction.restrict HI (psi : ClassFunction I R) =
        ClassFunction.comap
          (Subgroup.subgroupOfEquivOfLe
            (ClassFunction.le_inertia H _)).toMonoidHom
          (theta : ClassFunction H R)) :
    let thetaS := pTypeUliftCliffordMapCoefficient σ theta
    let IS := ClassFunction.inertia H (thetaS : ClassFunction H S)
    let I := ClassFunction.inertia H (theta : ClassFunction H R)
    let eI : IS ≃* I := MulEquiv.subgroupCongr
      (pTypeUliftCliffordMapCoefficient_inertia σ H theta)
    let psiS : IrreducibleCharacter IS S :=
      IrreducibleCharacter.comapMulEquiv eI
        (pTypeUliftCliffordMapCoefficient σ psi)
    ClassFunction.restrict (H.subgroupOf IS)
        (psiS : ClassFunction IS S) =
      (ClassFunction.inertiaSubgroupCharacter H thetaS :
        ClassFunction (H.subgroupOf IS) S) := by
  dsimp only at hrestrict
  let I := ClassFunction.inertia H (theta : ClassFunction H R)
  let thetaS := pTypeUliftCliffordMapCoefficient σ theta
  let IS := ClassFunction.inertia H (thetaS : ClassFunction H S)
  have hIS : IS = I :=
    pTypeUliftCliffordMapCoefficient_inertia σ H theta
  let eI : IS ≃* I := MulEquiv.subgroupCongr hIS
  let psiS : IrreducibleCharacter IS S :=
    IrreducibleCharacter.comapMulEquiv eI
      (pTypeUliftCliffordMapCoefficient σ psi)
  change ClassFunction.restrict (H.subgroupOf IS)
      (psiS : ClassFunction IS S) =
    (ClassFunction.inertiaSubgroupCharacter H thetaS :
      ClassFunction (H.subgroupOf IS) S)
  ext h
  let a : A := h
  have haIS : a ∈ IS := (h : IS).property
  have haI : a ∈ I := by
    simpa only [hIS] using haIS
  have haH : a ∈ H := h.property
  let hLow : H.subgroupOf I := ⟨⟨a, haI⟩, haH⟩
  have hvalue : psi (hLow : I) =
      theta (Subgroup.subgroupOfEquivOfLe
        (ClassFunction.le_inertia H _) hLow) := by
    have heval := congrArg
      (fun f : ClassFunction (H.subgroupOf I) R ↦ f hLow) hrestrict
    simpa only [ClassFunction.restrict_apply,
      ClassFunction.comap_apply, MulEquiv.coe_toMonoidHom] using heval
  change IrreducibleCharacter.comapMulEquiv eI
      (pTypeUliftCliffordMapCoefficient σ psi) (h : IS) =
    ClassFunction.inertiaSubgroupCharacter H
      (pTypeUliftCliffordMapCoefficient σ theta) h
  rw [IrreducibleCharacter.comapMulEquiv_apply,
    pTypeUliftCliffordMapCoefficient_apply,
    ClassFunction.inertiaSubgroupCharacter_apply,
    pTypeUliftCliffordMapCoefficient_apply]
  apply congrArg σ
  calc
    psi (eI (h : IS)) = psi (hLow : I) := by
      apply congrArg psi
      apply Subtype.ext
      exact MulEquiv.subgroupCongr_apply hIS (h : IS)
    _ = theta (Subgroup.subgroupOfEquivOfLe
          (ClassFunction.le_inertia H _) hLow) := hvalue
    _ = theta (Subgroup.subgroupOfEquivOfLe
          (ClassFunction.le_inertia H _) h) := by
      apply congrArg theta
      apply Subtype.ext
      rfl

/-! ## The two split-universe Clifford bridges -/

/-- A common direct constituent of two inductions from a normal subgroup
forces the two inducing irreducibles to be ambient-conjugate. -/
theorem pTypeTwistCommonInducedConstituent_conjugate
    {A : Type u} [Group A] [Fintype A]
    (H : Subgroup A) [H.Normal]
    (theta eta : IrreducibleCharacter H ℂ)
    (zeta : IrreducibleCharacter A ℂ)
    (htheta : zeta.IsConstituent
      (ClassFunction.induce H (theta : ClassFunction H ℂ)))
    (heta : zeta.IsConstituent
      (ClassFunction.induce H (eta : ClassFunction H ℂ))) :
    ∃ a : A, ClassFunction.normalConjugate H a
        (theta : ClassFunction H ℂ) =
      (eta : ClassFunction H ℂ) := by
  classical
  let R : Type u := ULift.{u} ℂ
  let σ : R ≃+* ℂ := ULift.ringEquiv
  letI : CharZero R :=
    charZero_of_injective_ringHom
      (f := σ.symm.toRingHom) σ.symm.injective
  letI : IsAlgClosed R :=
    pTypeUliftCliffordIsAlgClosedOfRingEquiv σ
  let thetaR : IrreducibleCharacter H R :=
    pTypeUliftCliffordMapCoefficient σ.symm theta
  let etaR : IrreducibleCharacter H R :=
    pTypeUliftCliffordMapCoefficient σ.symm eta
  let zetaR : IrreducibleCharacter A R :=
    pTypeUliftCliffordMapCoefficient σ.symm zeta
  have hthetaR : zetaR.IsConstituent
      (ClassFunction.induce H (thetaR : ClassFunction H R)) := by
    have hmapped := pTypeUliftCliffordMapCoefficient_isConstituent
      σ.symm zeta
      (ClassFunction.induce H (theta : ClassFunction H ℂ)) htheta
    rw [pTypeUliftCliffordMapRingHom_induce,
      pTypeUliftCliffordMapCoefficient_coe] at hmapped
    exact hmapped
  have hetaR : zetaR.IsConstituent
      (ClassFunction.induce H (etaR : ClassFunction H R)) := by
    have hmapped := pTypeUliftCliffordMapCoefficient_isConstituent
      σ.symm zeta
      (ClassFunction.induce H (eta : ClassFunction H ℂ)) heta
    rw [pTypeUliftCliffordMapRingHom_induce,
      pTypeUliftCliffordMapCoefficient_coe] at hmapped
    exact hmapped
  letI : Invertible (Nat.card H : R) :=
    invertibleOfNonzero
      (Nat.cast_ne_zero.mpr (Nat.card_pos (α := H)).ne')
  rcases ClassFunction.cfclass_Ind_cases H thetaR etaR with horbit | hortho
  · obtain ⟨a, ha⟩ := horbit.1
    refine ⟨a, ?_⟩
    apply pTypeUliftCliffordMapRingHom_injective σ.symm
    rw [pTypeUliftCliffordMapRingHom_normalConjugate,
      pTypeUliftCliffordMapCoefficient_coe,
      pTypeUliftCliffordMapCoefficient_coe]
    exact ha
  · exfalso
    let V : FDRep R A :=
      FDRep.induceFromSubgroup H thetaR.representation
    let W : FDRep R A :=
      FDRep.induceFromSubgroup H etaR.representation
    have hV : ClassFunction.ofRepresentation V.ρ =
        ClassFunction.induce H (thetaR : ClassFunction H R) := by
      dsimp only [V]
      exact (ClassFunction.ofRepresentation_induceFromSubgroup_general
        H thetaR.representation).trans
          (congrArg (ClassFunction.induce H)
            thetaR.ofRepresentation_representation)
    have hW : ClassFunction.ofRepresentation W.ρ =
        ClassFunction.induce H (etaR : ClassFunction H R) := by
      dsimp only [W]
      exact (ClassFunction.ofRepresentation_induceFromSubgroup_general
        H etaR.representation).trans
          (congrArg (ClassFunction.induce H)
            etaR.ofRepresentation_representation)
    have hdis :=
      pTypeUliftCliffordConstituents_disjoint_of_pairing_eq_zero
        V W (by simpa only [hV, hW] using hortho.2)
    have hzetaV : zetaR ∈ ClassFunction.constituents
        (ClassFunction.ofRepresentation V.ρ) := by
      rw [ClassFunction.mem_constituents_iff, hV]
      exact hthetaR
    have hzetaW : zetaR ∈ ClassFunction.constituents
        (ClassFunction.ofRepresentation W.ρ) := by
      rw [ClassFunction.mem_constituents_iff, hW]
      exact hetaR
    exact (Set.disjoint_left.mp hdis) hzetaV hzetaW

/-- Clifford correspondence transported across coefficient universes: an
ambient irreducible lying over `theta` is induced from its exact inertia
subgroup. -/
theorem pTypeCliffordInduced_of_inertia_eq
    {A : Type u} [Group A] [Fintype A]
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
  classical
  let R : Type u := ULift.{u} ℂ
  let σ : R ≃+* ℂ := ULift.ringEquiv
  letI : CharZero R :=
    charZero_of_injective_ringHom
      (f := σ.symm.toRingHom) σ.symm.injective
  letI : IsAlgClosed R :=
    pTypeUliftCliffordIsAlgClosedOfRingEquiv σ
  let thetaR : IrreducibleCharacter H R :=
    pTypeUliftCliffordMapCoefficient σ.symm theta
  let chiR : IrreducibleCharacter A R :=
    pTypeUliftCliffordMapCoefficient σ.symm chi
  let IR := ClassFunction.inertia H (thetaR : ClassFunction H R)
  have hIR : IR = T := by
    exact (pTypeUliftCliffordMapCoefficient_inertia
      σ.symm H theta).trans hT
  have hthetaR : thetaR.IsConstituent
      (ClassFunction.restrict H (chiR : ClassFunction A R)) := by
    have hmapped := pTypeUliftCliffordMapCoefficient_isConstituent
      σ.symm theta
      (ClassFunction.restrict H (chi : ClassFunction A ℂ)) htheta
    simpa only [thetaR, chiR,
      pTypeUliftCliffordMapRingHom_restrict,
      pTypeUliftCliffordMapCoefficient_coe] using hmapped
  have hchiConstR : chiR ∈ ClassFunction.constituents
      (ClassFunction.induce H (thetaR : ClassFunction H R)) := by
    rw [ClassFunction.mem_constituents_iff]
    exact (thetaR.isConstituent_restrict_iff_induce H chiR).mp hthetaR
  rw [ClassFunction.inertiaConstituentMap_image H thetaR] at hchiConstR
  obtain ⟨psiIndex, _hpsiMem, hpsi⟩ :=
    Finset.mem_image.mp hchiConstR
  let psiR : IrreducibleCharacter IR R := psiIndex.1
  have hhigh : (chiR : ClassFunction A R) =
      ClassFunction.induce IR (psiR : ClassFunction IR R) := by
    calc
      (chiR : ClassFunction A R) =
          (ClassFunction.inertiaConstituentMap H thetaR psiIndex :
            ClassFunction A R) := by rw [hpsi]
      _ = ClassFunction.induce IR
          (psiIndex.1 : ClassFunction IR R) :=
        ClassFunction.coe_inertiaConstituentMap H thetaR psiIndex
  let psiLow : IrreducibleCharacter IR ℂ :=
    pTypeUliftCliffordMapCoefficient σ psiR
  let xi : IrreducibleCharacter T ℂ :=
    pTypeUliftCliffordTransportIrreducible IR T hIR psiLow
  have hchiRound :
      pTypeUliftCliffordMapCoefficient σ chiR = chi := by
    apply IrreducibleCharacter.ext
    intro a
    simp only [chiR, pTypeUliftCliffordMapCoefficient_apply]
    exact σ.apply_symm_apply _
  have hlow : (chi : ClassFunction A ℂ) =
      ClassFunction.induce IR (psiLow : ClassFunction IR ℂ) := by
    calc
      (chi : ClassFunction A ℂ) =
          (pTypeUliftCliffordMapCoefficient σ chiR :
            ClassFunction A ℂ) := by
        exact congrArg
          (fun q : IrreducibleCharacter A ℂ ↦
            (q : ClassFunction A ℂ)) hchiRound.symm
      _ = ClassFunction.mapRingHom σ.toRingHom
          (chiR : ClassFunction A R) :=
        (pTypeUliftCliffordMapCoefficient_coe σ chiR).symm
      _ = ClassFunction.mapRingHom σ.toRingHom
          (ClassFunction.induce IR
            (psiR : ClassFunction IR R)) := by
        exact congrArg
          (ClassFunction.mapRingHom σ.toRingHom) hhigh
      _ = ClassFunction.induce IR
          (ClassFunction.mapRingHom σ.toRingHom
            (psiR : ClassFunction IR R)) :=
        pTypeUliftCliffordMapRingHom_induce
          σ IR (psiR : ClassFunction IR R)
      _ = ClassFunction.induce IR
          (psiLow : ClassFunction IR ℂ) :=
        congrArg (ClassFunction.induce IR)
          (pTypeUliftCliffordMapCoefficient_coe σ psiR)
  refine ⟨xi, hlow.trans ?_⟩
  exact pTypeUliftCliffordInduceTransportIrreducible
    IR T hIR psiLow

/-- An irreducible extension to the exact inertia subgroup induces to a
constituent of the original normal-subgroup induction. -/
theorem pTypeTwistExtension_induced_isConstituent
    {A : Type u} [Group A] [Fintype A]
    (H : Subgroup A) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    (psi : IrreducibleCharacter
      (ClassFunction.inertia H (theta : ClassFunction H ℂ)) ℂ)
    (hrestrict :
      let I := ClassFunction.inertia H (theta : ClassFunction H ℂ)
      let HI := H.subgroupOf I
      ClassFunction.restrict HI (psi : ClassFunction I ℂ) =
        ClassFunction.comap
          (Subgroup.subgroupOfEquivOfLe
            (ClassFunction.le_inertia H _)).toMonoidHom
          (theta : ClassFunction H ℂ))
    (zeta : IrreducibleCharacter A ℂ)
    (hzeta : (zeta : ClassFunction A ℂ) =
      ClassFunction.induce
        (ClassFunction.inertia H (theta : ClassFunction H ℂ))
        (psi : ClassFunction
          (ClassFunction.inertia H (theta : ClassFunction H ℂ)) ℂ)) :
    zeta.IsConstituent
      (ClassFunction.induce H (theta : ClassFunction H ℂ)) := by
  classical
  let I := ClassFunction.inertia H (theta : ClassFunction H ℂ)
  let R : Type u := ULift.{u} ℂ
  let σ : R ≃+* ℂ := ULift.ringEquiv
  letI : CharZero R :=
    charZero_of_injective_ringHom
      (f := σ.symm.toRingHom) σ.symm.injective
  letI : IsAlgClosed R :=
    pTypeUliftCliffordIsAlgClosedOfRingEquiv σ
  let thetaR : IrreducibleCharacter H R :=
    pTypeUliftCliffordMapCoefficient σ.symm theta
  let IR := ClassFunction.inertia H (thetaR : ClassFunction H R)
  have hIR : IR = I :=
    pTypeUliftCliffordMapCoefficient_inertia σ.symm H theta
  let eI : IR ≃* I := MulEquiv.subgroupCongr hIR
  let psiLift : IrreducibleCharacter I R :=
    pTypeUliftCliffordMapCoefficient σ.symm psi
  let psiR : IrreducibleCharacter IR R :=
    IrreducibleCharacter.comapMulEquiv eI psiLift
  let zetaR : IrreducibleCharacter A R :=
    pTypeUliftCliffordMapCoefficient σ.symm zeta
  have hrestrictR : ClassFunction.restrict (H.subgroupOf IR)
        (psiR : ClassFunction IR R) =
      (ClassFunction.inertiaSubgroupCharacter H thetaR :
        ClassFunction (H.subgroupOf IR) R) := by
    simpa only [thetaR, IR, I, eI, psiLift, psiR,
      ClassFunction.inertiaSubgroupCharacter] using
      (pTypeUliftCliffordMapCoefficient_inertiaExtension_restrict
        σ.symm H theta psi hrestrict)
  have hpsiMem : psiR ∈
      ClassFunction.inertiaConstituents H thetaR :=
    pTypeUliftCliffordInertiaConstituent_of_restrict
      H thetaR psiR hrestrictR
  let psiIndex : ClassFunction.InertiaConstituentIndex H thetaR :=
    ⟨psiR, hpsiMem⟩
  have hzetaR : (zetaR : ClassFunction A R) =
      ClassFunction.induce IR (psiR : ClassFunction IR R) := by
    calc
      (zetaR : ClassFunction A R) =
          ClassFunction.mapRingHom σ.symm.toRingHom
            (zeta : ClassFunction A ℂ) :=
        (pTypeUliftCliffordMapCoefficient_coe σ.symm zeta).symm
      _ = ClassFunction.mapRingHom σ.symm.toRingHom
          (ClassFunction.induce I (psi : ClassFunction I ℂ)) := by
        exact congrArg
          (ClassFunction.mapRingHom σ.symm.toRingHom) hzeta
      _ = ClassFunction.induce I (psiLift : ClassFunction I R) := by
        rw [pTypeUliftCliffordMapRingHom_induce,
          pTypeUliftCliffordMapCoefficient_coe]
      _ = ClassFunction.induce IR (psiR : ClassFunction IR R) :=
        (pTypeUliftCliffordInduceComapSubgroupCongr
          IR I hIR psiLift).symm
  have hmap : ClassFunction.inertiaConstituentMap H thetaR psiIndex =
      zetaR := by
    apply IrreducibleCharacter.ext
    intro a
    change ClassFunction.induce IR (psiR : ClassFunction IR R) a =
      zetaR a
    exact congrArg (fun f : ClassFunction A R ↦ f a) hzetaR.symm
  have hzetaMem : zetaR ∈ ClassFunction.constituents
      (ClassFunction.induce H (thetaR : ClassFunction H R)) := by
    rw [ClassFunction.inertiaConstituentMap_image H thetaR]
    exact Finset.mem_image.mpr
      ⟨psiIndex, Finset.mem_univ psiIndex, hmap⟩
  have hhigh : zetaR.IsConstituent
      (ClassFunction.induce H (thetaR : ClassFunction H R)) :=
    (ClassFunction.mem_constituents_iff _ _).mp hzetaMem
  have hdown := pTypeUliftCliffordMapCoefficient_isConstituent
    σ zetaR (ClassFunction.induce H
      (thetaR : ClassFunction H R)) hhigh
  have hzetaRound : pTypeUliftCliffordMapCoefficient σ zetaR = zeta := by
    apply IrreducibleCharacter.ext
    intro a
    simp only [zetaR, pTypeUliftCliffordMapCoefficient_apply]
    exact σ.apply_symm_apply _
  have hthetaRound :
      pTypeUliftCliffordMapCoefficient σ thetaR = theta := by
    apply IrreducibleCharacter.ext
    intro h
    simp only [thetaR, pTypeUliftCliffordMapCoefficient_apply]
    exact σ.apply_symm_apply _
  simpa only [pTypeUliftCliffordMapRingHom_induce,
    pTypeUliftCliffordMapCoefficient_coe,
    hzetaRound, hthetaRound] using hdown

/-- An irreducible extension to the exact inertia subgroup induces
irreducibly to the ambient group. -/
theorem pTypeTwistExtension_induce_isIrreducible
    {A : Type u} [Group A] [Fintype A]
    (H : Subgroup A) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    (psi : IrreducibleCharacter
      (ClassFunction.inertia H (theta : ClassFunction H ℂ)) ℂ)
    (hrestrict :
      let I := ClassFunction.inertia H (theta : ClassFunction H ℂ)
      let HI := H.subgroupOf I
      ClassFunction.restrict HI (psi : ClassFunction I ℂ) =
        ClassFunction.comap
          (Subgroup.subgroupOfEquivOfLe
            (ClassFunction.le_inertia H _)).toMonoidHom
          (theta : ClassFunction H ℂ)) :
    IsIrreducibleCharacter A ℂ
      (ClassFunction.induce
        (ClassFunction.inertia H (theta : ClassFunction H ℂ))
        (psi : ClassFunction
          (ClassFunction.inertia H (theta : ClassFunction H ℂ)) ℂ)) := by
  classical
  let I := ClassFunction.inertia H (theta : ClassFunction H ℂ)
  let R : Type u := ULift.{u} ℂ
  let σ : R ≃+* ℂ := ULift.ringEquiv
  letI : CharZero R :=
    charZero_of_injective_ringHom
      (f := σ.symm.toRingHom) σ.symm.injective
  letI : IsAlgClosed R :=
    pTypeUliftCliffordIsAlgClosedOfRingEquiv σ
  let thetaR : IrreducibleCharacter H R :=
    pTypeUliftCliffordMapCoefficient σ.symm theta
  let IR := ClassFunction.inertia H (thetaR : ClassFunction H R)
  have hIR : IR = I :=
    pTypeUliftCliffordMapCoefficient_inertia σ.symm H theta
  let eI : IR ≃* I := MulEquiv.subgroupCongr hIR
  let psiLift : IrreducibleCharacter I R :=
    pTypeUliftCliffordMapCoefficient σ.symm psi
  let psiR : IrreducibleCharacter IR R :=
    IrreducibleCharacter.comapMulEquiv eI psiLift
  have hrestrictR : ClassFunction.restrict (H.subgroupOf IR)
        (psiR : ClassFunction IR R) =
      (ClassFunction.inertiaSubgroupCharacter H thetaR :
        ClassFunction (H.subgroupOf IR) R) := by
    simpa only [thetaR, IR, I, eI, psiLift, psiR,
      ClassFunction.inertiaSubgroupCharacter] using
      (pTypeUliftCliffordMapCoefficient_inertiaExtension_restrict
        σ.symm H theta psi hrestrict)
  have hpsiMem : psiR ∈
      ClassFunction.inertiaConstituents H thetaR :=
    pTypeUliftCliffordInertiaConstituent_of_restrict
      H thetaR psiR hrestrictR
  have hirrHigh : IsIrreducibleCharacter A R
      (ClassFunction.induce IR (psiR : ClassFunction IR R)) :=
    ClassFunction.inertiaConstituent_induce_isIrreducible
      H thetaR psiR hpsiMem
  have hirrMapped : IsIrreducibleCharacter A ℂ
      (ClassFunction.mapRingHom σ.toRingHom
        (ClassFunction.induce IR (psiR : ClassFunction IR R))) :=
    pTypeUliftCliffordMapRingHom_isIrreducible σ _ hirrHigh
  have hpsiMapped :
      ClassFunction.mapRingHom σ.toRingHom
          (psiR : ClassFunction IR R) =
        ClassFunction.comap eI.toMonoidHom
          (psi : ClassFunction I ℂ) := by
    ext x
    simp only [ClassFunction.mapRingHom_apply, psiR,
      IrreducibleCharacter.comapMulEquiv_apply, psiLift,
      pTypeUliftCliffordMapCoefficient_apply,
      ClassFunction.comap_apply, MulEquiv.coe_toMonoidHom]
    exact σ.apply_symm_apply _
  have hindMapped :
      ClassFunction.mapRingHom σ.toRingHom
          (ClassFunction.induce IR (psiR : ClassFunction IR R)) =
        ClassFunction.induce I (psi : ClassFunction I ℂ) := by
    calc
      _ = ClassFunction.induce IR
          (ClassFunction.mapRingHom σ.toRingHom
            (psiR : ClassFunction IR R)) :=
        pTypeUliftCliffordMapRingHom_induce
          σ IR (psiR : ClassFunction IR R)
      _ = ClassFunction.induce IR
          (ClassFunction.comap eI.toMonoidHom
            (psi : ClassFunction I ℂ)) :=
        congrArg (ClassFunction.induce IR) hpsiMapped
      _ = ClassFunction.induce I (psi : ClassFunction I ℂ) := by
        simpa only [eI] using
          (pTypeUliftCliffordInduceComapSubgroupCongrClassFunction
            IR I hIR (psi : ClassFunction I ℂ))
  rw [hindMapped] at hirrMapped
  exact hirrMapped

/-- Induction from the exact inertia subgroup is injective on irreducible
extensions which restrict exactly to the transported normal-subgroup
character. -/
theorem pTypeTwistExtension_induce_injective
    {A : Type u} [Group A] [Fintype A]
    (H : Subgroup A) [H.Normal]
    (theta : IrreducibleCharacter H ℂ)
    (psi phi : IrreducibleCharacter
      (ClassFunction.inertia H (theta : ClassFunction H ℂ)) ℂ)
    (hpsi :
      let I := ClassFunction.inertia H (theta : ClassFunction H ℂ)
      let HI := H.subgroupOf I
      ClassFunction.restrict HI (psi : ClassFunction I ℂ) =
        ClassFunction.comap
          (Subgroup.subgroupOfEquivOfLe
            (ClassFunction.le_inertia H _)).toMonoidHom
          (theta : ClassFunction H ℂ))
    (hphi :
      let I := ClassFunction.inertia H (theta : ClassFunction H ℂ)
      let HI := H.subgroupOf I
      ClassFunction.restrict HI (phi : ClassFunction I ℂ) =
        ClassFunction.comap
          (Subgroup.subgroupOfEquivOfLe
            (ClassFunction.le_inertia H _)).toMonoidHom
          (theta : ClassFunction H ℂ))
    (hInd : ClassFunction.induce
        (ClassFunction.inertia H (theta : ClassFunction H ℂ))
        (psi : ClassFunction
          (ClassFunction.inertia H (theta : ClassFunction H ℂ)) ℂ) =
      ClassFunction.induce
        (ClassFunction.inertia H (theta : ClassFunction H ℂ))
        (phi : ClassFunction
          (ClassFunction.inertia H (theta : ClassFunction H ℂ)) ℂ)) :
    psi = phi := by
  classical
  let I := ClassFunction.inertia H (theta : ClassFunction H ℂ)
  let R : Type u := ULift.{u} ℂ
  let σ : R ≃+* ℂ := ULift.ringEquiv
  letI : CharZero R :=
    charZero_of_injective_ringHom
      (f := σ.symm.toRingHom) σ.symm.injective
  letI : IsAlgClosed R :=
    pTypeUliftCliffordIsAlgClosedOfRingEquiv σ
  let thetaR : IrreducibleCharacter H R :=
    pTypeUliftCliffordMapCoefficient σ.symm theta
  let IR := ClassFunction.inertia H (thetaR : ClassFunction H R)
  have hIR : IR = I :=
    pTypeUliftCliffordMapCoefficient_inertia σ.symm H theta
  let eI : IR ≃* I := MulEquiv.subgroupCongr hIR
  let psiLift : IrreducibleCharacter I R :=
    pTypeUliftCliffordMapCoefficient σ.symm psi
  let phiLift : IrreducibleCharacter I R :=
    pTypeUliftCliffordMapCoefficient σ.symm phi
  let psiR : IrreducibleCharacter IR R :=
    IrreducibleCharacter.comapMulEquiv eI psiLift
  let phiR : IrreducibleCharacter IR R :=
    IrreducibleCharacter.comapMulEquiv eI phiLift
  have hpsiR : ClassFunction.restrict (H.subgroupOf IR)
        (psiR : ClassFunction IR R) =
      (ClassFunction.inertiaSubgroupCharacter H thetaR :
        ClassFunction (H.subgroupOf IR) R) := by
    simpa only [thetaR, IR, I, eI, psiLift, psiR,
      ClassFunction.inertiaSubgroupCharacter] using
      (pTypeUliftCliffordMapCoefficient_inertiaExtension_restrict
        σ.symm H theta psi hpsi)
  have hphiR : ClassFunction.restrict (H.subgroupOf IR)
        (phiR : ClassFunction IR R) =
      (ClassFunction.inertiaSubgroupCharacter H thetaR :
        ClassFunction (H.subgroupOf IR) R) := by
    simpa only [thetaR, IR, I, eI, phiLift, phiR,
      ClassFunction.inertiaSubgroupCharacter] using
      (pTypeUliftCliffordMapCoefficient_inertiaExtension_restrict
        σ.symm H theta phi hphi)
  have hpsiMem : psiR ∈
      ClassFunction.inertiaConstituents H thetaR :=
    pTypeUliftCliffordInertiaConstituent_of_restrict
      H thetaR psiR hpsiR
  have hphiMem : phiR ∈
      ClassFunction.inertiaConstituents H thetaR :=
    pTypeUliftCliffordInertiaConstituent_of_restrict
      H thetaR phiR hphiR
  let psiIndex : ClassFunction.InertiaConstituentIndex H thetaR :=
    ⟨psiR, hpsiMem⟩
  let phiIndex : ClassFunction.InertiaConstituentIndex H thetaR :=
    ⟨phiR, hphiMem⟩
  have hIndLift : ClassFunction.induce I
        (psiLift : ClassFunction I R) =
      ClassFunction.induce I (phiLift : ClassFunction I R) := by
    have hmapped := congrArg
      (ClassFunction.mapRingHom σ.symm.toRingHom) hInd
    simpa only [I, psiLift, phiLift,
      pTypeUliftCliffordMapRingHom_induce,
      pTypeUliftCliffordMapCoefficient_coe] using hmapped
  have hIndR : ClassFunction.induce IR
        (psiR : ClassFunction IR R) =
      ClassFunction.induce IR (phiR : ClassFunction IR R) := by
    calc
      ClassFunction.induce IR (psiR : ClassFunction IR R) =
          ClassFunction.induce I (psiLift : ClassFunction I R) :=
        pTypeUliftCliffordInduceComapSubgroupCongr
          IR I hIR psiLift
      _ = ClassFunction.induce I (phiLift : ClassFunction I R) := hIndLift
      _ = ClassFunction.induce IR (phiR : ClassFunction IR R) :=
        (pTypeUliftCliffordInduceComapSubgroupCongr
          IR I hIR phiLift).symm
  have hmap : ClassFunction.inertiaConstituentMap H thetaR psiIndex =
      ClassFunction.inertiaConstituentMap H thetaR phiIndex := by
    apply IrreducibleCharacter.ext
    intro a
    change ClassFunction.induce IR (psiR : ClassFunction IR R) a =
      ClassFunction.induce IR (phiR : ClassFunction IR R) a
    exact congrArg (fun f : ClassFunction A R ↦ f a) hIndR
  have hindex : psiIndex = phiIndex :=
    ClassFunction.inertiaConstituentMap_injective H thetaR hmap
  have hpsiRphiR : psiR = phiR := congrArg Subtype.val hindex
  have hLift : psiLift = phiLift := by
    apply IrreducibleCharacter.ext
    intro i
    have hi := congrArg
      (fun chi : IrreducibleCharacter IR R ↦ chi (eI.symm i))
      hpsiRphiR
    simpa only [psiR, phiR,
      IrreducibleCharacter.comapMulEquiv_apply,
      MulEquiv.apply_symm_apply] using hi
  apply IrreducibleCharacter.ext
  intro i
  have hi := congrArg
    (fun chi : IrreducibleCharacter I R ↦ chi i) hLift
  simp only [psiLift, phiLift,
    pTypeUliftCliffordMapCoefficient_apply] at hi
  exact σ.symm.injective hi

end PTypeNonGaloisCliffordSupportInternal

end

end Submission.OddOrder.PF
