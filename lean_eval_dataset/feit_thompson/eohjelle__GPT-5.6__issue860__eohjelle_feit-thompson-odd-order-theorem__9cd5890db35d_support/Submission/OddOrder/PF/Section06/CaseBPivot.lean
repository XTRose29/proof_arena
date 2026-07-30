import Mathlib.NumberTheory.Niven
import Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism
import Submission.OddOrder.PF.Section01.ConstituentExpansion
import Submission.OddOrder.PF.Section01.PiCharacterAutomorphism
import Submission.OddOrder.PF.Section01.VirtualCharacterPullback
import Submission.OddOrder.PF.Section03.CyclicCharacterFacts
import Submission.OddOrder.PF.Section05.DadeAutomorphismCoherence
import Submission.OddOrder.PF.Section05.SubcoherentProperties
import Submission.OddOrder.PF.Section06.CentralRestrictionClifford
import Submission.OddOrder.PF.Section06.ConstantIrrModTISylow

/-!
# The common pivot in Sibley's Case B

This file isolates the character calculation in the second branch of
Peterfalvi (6.8), `PFsection6.v`, lines 947--1278.  The calculation has two
natural interfaces.

* Lines 955--1078 use the prime-Dade automorphisms and
  `constant_irr_mod_TI_Sylow` to obtain an integral coefficient `x` whose
  squared-coefficient sum is less than two.  The elementary integral
  argument below then shows that the resulting target is either
  `tau₁ eta₁`, or, in the two-member exceptional family, its dual.
* Lines 1114--1263 expand a constituent over the central subgroup, split its
  target with subcoherence, and force the remaining virtual character to
  have norm zero.  `sibley_caseB_pivot` performs that forcing internally and
  returns the decomposition needed by the final pivot-coherence lemma.

The explicit context below records only hypotheses available before the
Case-B character calculation: subcoherence, the already constructed
coherence on `Y`, source and target embeddings of the central section,
ordinary Frobenius reciprocity, the inputs from which prime-Dade constancy
is proved below, the exact `constant_irr_mod_TI_Sylow` consequence, the
kernel description of `X`, and the numerical index inequality supplied by
the Case-B Frobenius decomposition.  It contains neither a pivot norm bound
nor a target decomposition for a member of `X`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical IsMulCommutative
open CategoryTheory

universe u

local instance caseBPivotInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Source-side notation and prerequisites -/

/-- The explicit common target used in the Case-B calculation.

In the source this is
`- \sum_(eta <- Y) (x - (eta == eta1)) *: tau1 eta`.
-/
def sibleyCaseBPivotCandidate
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (Y : Finset (ClassFunction L ℂ))
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ) (x : ℤ) :
    ClassFunction G ℂ :=
  -∑ eta ∈ Y,
    ((x : ℂ) - if eta = eta₁ then 1 else 0) • tau₁ eta

/-- All genuine prerequisites of the Case-B pivot calculation.

The prime-Dade constancy conclusion of source lines 955--981 is derived
below from the coefficient-automorphism and Dade restriction identities.
Every field occurs before the calculations in source lines 982--1278 and is
discharged directly at the `Sibley_coherence` call site.
-/
structure SibleyCaseBContext
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) (Z : Subgroup K)
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ) where
  /-- The ambient subcoherent source family and its target columns. -/
  sourceFamily : Set (ClassFunction L ℂ)
  targetColumns : ClassFunction L ℂ → Finset (ClassFunction G ℂ)
  source_subcoherent : subcoherent sourceFamily tau targetColumns
  X_family : cfConjC_subset
    (↑X : Set (ClassFunction L ℂ)) sourceFamily
  Y_family : cfConjC_subset
    (↑Y : Set (ClassFunction L ℂ)) sourceFamily

  /-- The already completed uniform-degree coherence calculation on `Y`. -/
  eta₁_mem : eta₁ ∈ Y
  Y_closed : cfConjC_closed (↑Y : Set (ClassFunction L ℂ))
  Y_coherent : coherent_with
    (↑Y : Set (ClassFunction L ℂ)) (nonidentitySet L) tau tau₁
  Y_orthonormal : ∀ eta ∈ Y, ∀ zeta ∈ Y,
    characterPairing eta zeta = if eta = zeta then 1 else 0
  Y_degree : ∀ eta ∈ Y, eta 1 = (K.index : ℂ)
  two_le_card_Y : 2 ≤ Y.card

  /-- Orthogonality/disjointness of the two source blocks. -/
  X_Y_disjoint : ∀ xi ∈ X, ∀ eta ∈ Y, eta ≠ xi

  /-- Source central subgroup and induced description of `X`. -/
  Z_nontrivial : Z ≠ ⊥
  Z_prime : Nat.Prime (Nat.card Z)
  Z_cyclic : IsCyclic Z
  Z_central : Z ≤ Subgroup.center K
  Z_central_in_L : Z.map K.subtype ≤ Subgroup.center L
  X_induced : ∀ xi ∈ X,
    ∃ theta : IrreducibleCharacter K ℂ,
      xi = ClassFunction.induce K (theta : ClassFunction K ℂ)
  X_characterization : ∀ theta : IrreducibleCharacter K ℂ,
    (ClassFunction.induce K (theta : ClassFunction K ℂ) ∈ X ↔
      ¬ Z ≤ ClassFunction.translationKernel
        (theta : ClassFunction K ℂ))

  /-- Literal induction from `Z ≤ K ≤ L`.  The present induction API
  expresses transitivity through `subgroupOf`; these equations are the
  transport adapter needed to use that API with the literal source type
  `Z`.  None mentions the pivot or a target decomposition. -/
  centralInduce :
    IrreducibleCharacter Z ℂ → ClassFunction L ℂ
  centralInduce_eq_induce : ∀ i,
    centralInduce i =
      ClassFunction.induce K
        (ClassFunction.induce Z (i : ClassFunction Z ℂ))
  centralInduce_virtual : ∀ i,
    ClassFunction.IsVirtual (centralInduce i)
  centralInduce_mem_X_span : ∀ i,
    i ≠ IrreducibleCharacter.trivial →
      centralInduce i ∈
        AddSubgroup.closure
          (↑X : Set (ClassFunction L ℂ))
  centralInduce_one : ∀ i,
    centralInduce i 1 = ((K.index * Z.index : ℕ) : ℂ)
  centralInduce_self : ∀ i,
    characterPairing (centralInduce i) (centralInduce i) =
      ((K.index * Z.index : ℕ) : ℂ)

  /-- The literal copy of `L` in the target and the central-section map.
  These turn restriction into ordinary `ClassFunction.comap`. -/
  embedLtoG : L →* G
  embedLtoG_injective : Function.Injective embedLtoG
  zToG : Z →* G
  zToG_injective : Function.Injective zToG
  zToG_eq : zToG =
    embedLtoG.comp (K.subtype.comp Z.subtype)
  frobenius_reciprocity : ∀ (f : ClassFunction L ℂ)
      (g : ClassFunction G ℂ),
    characterPairing (tau f) g =
      characterPairing f (ClassFunction.comap embedLtoG g)
  centralInduce_pairing : ∀ (i : IrreducibleCharacter Z ℂ)
      (g : ClassFunction G ℂ),
    characterPairing (tau (centralInduce i)) g =
      characterPairing (i : ClassFunction Z ℂ)
        (ClassFunction.comap zToG g)

  /-- The target copy of `Z` used by `constant_irr_mod_TI_Sylow`. -/
  ZG : Subgroup G
  ZG_nontrivial : ZG ≠ ⊥
  ZG_prime : Nat.Prime (Nat.card ZG)
  ZG_cyclic : IsCyclic ZG
  zToG_range : zToG.range = ZG

  /-- Elementary power transitivity of a prime cyclic group. -/
  Z_power_transitive : ∀ (x y : Z), x ≠ 1 → y ≠ 1 →
    ∃ k : ℕ, k.Coprime (Nat.card Z) ∧ y = x ^ k

  /-- Coefficient automorphisms preserve the selected source family. -/
  Y_coefficient_closed : ∀ (sigma : ℂ ≃+* ℂ) eta, eta ∈ Y →
    ClassFunction.mapRingHom sigma.toRingHom eta ∈ Y

  /-- The output of `cfAut_Dade_coherent`, before specializing to powers
  of elements of `Z`. -/
  coefficient_automorphism_commutes :
    ∀ (sigma : ℂ ≃+* ℂ) eta, eta ∈ Y →
      ClassFunction.mapRingHom sigma.toRingHom (tau₁ eta) =
        tau₁ (ClassFunction.mapRingHom sigma.toRingHom eta)

  /-- The Dade restriction identity for the twist difference.  This is the
  exact compatibility used in source lines 976--981, not the resulting
  constancy statement. -/
  dade_twist_vanishes_on_Z :
    ∀ (sigma : ℂ ≃+* ℂ) eta, eta ∈ Y →
      ∀ z : Z, z ≠ 1 →
        tau₁
          (eta - ClassFunction.mapRingHom sigma.toRingHom eta)
          (zToG z) = 0

  /-- The exact local consequence of `constant_irr_mod_TI_Sylow` used at the
  Case-B call site. -/
  constant_irreducible_mod :
    ∀ (phi : IrreducibleCharacter G ℂ),
      (∀ (x y : G),
        x ∈ ZG → x ≠ 1 → y ∈ ZG → y ≠ 1 →
          phi x = phi y) →
      ∀ (x : G), x ∈ ZG → x ≠ 1 →
        (∃ n : ℤ, phi x = (n : ℂ)) ∧
          IsIntegralModEq (Nat.card K : ℂ) (phi x) (phi 1)

  /-- The sole numerical input from the Case-B Frobenius decomposition.
  It is used at source line 1057, before the character-norm calculation. -/
  kernel_index_lt_central_index : K.index < Z.index

/-! ## Integral and virtual-character cleanup -/

private theorem caseB_pairing_neg_left
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing (-f) g = -characterPairing f g := by
  rw [← neg_one_smul ℂ f, characterPairing_smul_left]
  ring

private theorem caseB_pairing_neg_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing f (-g) = -characterPairing f g := by
  rw [← neg_one_smul ℂ g, characterPairing_smul_right]
  ring

private theorem caseB_pairing_sub_left
    {Q : Type u} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    characterPairing (f - g) h =
      characterPairing f h - characterPairing g h := by
  rw [sub_eq_add_neg, characterPairing_add_left,
    caseB_pairing_neg_left, sub_eq_add_neg]

private theorem caseB_pairing_sub_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    characterPairing f (g - h) =
      characterPairing f g - characterPairing f h := by
  rw [sub_eq_add_neg, characterPairing_add_right,
    caseB_pairing_neg_right, sub_eq_add_neg]

private theorem pairing_self_sub_of_orthogonal_caseB
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ)
    (hfg : characterPairing f g = 0) :
    characterPairing (f - g) (f - g) =
      characterPairing f f + characterPairing g g := by
  rw [caseB_pairing_sub_left, caseB_pairing_sub_right,
    caseB_pairing_sub_right, hfg, characterPairing_comm g f, hfg]
  ring

private theorem caseB_pairing_finset_sum_left
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (g : ClassFunction Q ℂ) :
    characterPairing (∑ i ∈ s, f i) g =
      ∑ i ∈ s, characterPairing (f i) g := by
  exact map_sum (characterPairingRight g) f s

private theorem caseB_pairing_finset_sum_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) {I : Type*}
    (s : Finset I) (g : I → ClassFunction Q ℂ) :
    characterPairing f (∑ i ∈ s, g i) =
      ∑ i ∈ s, characterPairing f (g i) := by
  exact map_sum (characterPairingLeft f) g s

private theorem caseB_virtual_pairing_eq_int
    {Q : Type u} [Group Q] [Fintype Q]
    {f g : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f)
    (hg : ClassFunction.IsVirtual g) :
    ∃ n : ℤ, characterPairing f g = (n : ℂ) := by
  obtain ⟨v, rfl⟩ := hf
  obtain ⟨w, rfl⟩ := hg
  exact ⟨coeffDot v w,
    VirtualCharacter.characterPairing_realize v w⟩

private theorem caseB_exists_signed_irreducible
    {Q : Type u} [Group Q] [Fintype Q]
    {f : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f)
    (hnorm : characterPairing f f = 1) :
    ∃ (chi : IrreducibleCharacter Q ℂ) (epsilon : ℤ),
      IsSign epsilon ∧
        f = (epsilon : ℂ) • (chi : ClassFunction Q ℂ) := by
  obtain ⟨v, hv⟩ := hf
  have hvnorm : normSq v = 1 := by
    apply Int.cast_injective (α := ℂ)
    calc
      ((normSq v : ℤ) : ℂ) =
          characterPairing (VirtualCharacter.realize v)
            (VirtualCharacter.realize v) :=
        (VirtualCharacter.characterPairing_realize v v).symm
      _ = characterPairing f f := by rw [hv]
      _ = (1 : ℂ) := hnorm
      _ = ((1 : ℤ) : ℂ) := by norm_num
  obtain ⟨chi, epsilon, hepsilon, heq⟩ :=
    eq_signed_single_of_normSq_eq_one v hvnorm
  refine ⟨chi, epsilon, hepsilon, ?_⟩
  rw [← hv, heq, VirtualCharacter.realize_single]

/-- Universe-polymorphic complex specialization of the character/Hom-space
dimension identity.  The generic project wrapper currently puts the group
and coefficient field in the same universe, whereas the Case-B groups are
universe-polymorphic and the coefficient field is literally `ℂ`. -/
private theorem caseB_pairing_ofRepresentation_eq_finrank_hom
    {Q : Type u} [Group Q] [Fintype Q] (V W : FDRep ℂ Q) :
    characterPairing (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) =
      (Module.finrank ℂ (W ⟶ V) : ℂ) := by
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card Q : ℂ) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hhom := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcharV (q : Q) :
      V.character q = _root_.Representation.character V.ρ q := rfl
  have hcharW (q : Q) :
      W.character q = _root_.Representation.character W.ρ q := rfl
  simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
    invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
    hcharV, hcharW] using hhom

/-- The virtual character of a complex finite-dimensional representation,
with the group universe independent of the fixed coefficient universe. -/
private noncomputable def caseBVirtualCharacterOfFDRep
    {Q : Type u} [Group Q] [Fintype Q] (V : FDRep ℂ Q) :
    VirtualCharacter Q ℂ := by
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact Finsupp.equivFunOnFinite.symm
    (fun chi : IrreducibleCharacter Q ℂ ↦
      (Module.finrank ℂ (chi.representation ⟶ V) : ℤ))

private theorem caseB_realize_virtualCharacterOfFDRep
    {Q : Type u} [Group Q] [Fintype Q] (V : FDRep ℂ Q) :
    VirtualCharacter.realize (caseBVirtualCharacterOfFDRep V) =
      ClassFunction.ofRepresentation V.ρ := by
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [caseBVirtualCharacterOfFDRep,
    Finsupp.equivFunOnFinite_symm_eq_sum, map_sum]
  simp only [VirtualCharacter.realize_single, Int.cast_natCast]
  rw [← irreducibleCharacterExpansion_eq
    (ClassFunction.ofRepresentation V.ρ)]
  rw [irreducibleCharacterExpansion]
  apply Finset.sum_congr rfl
  intro chi _
  apply congrArg (fun c : ℂ ↦ c • (chi : ClassFunction Q ℂ))
  rw [characterPairing_comm,
    ← chi.ofRepresentation_representation,
    caseB_pairing_ofRepresentation_eq_finrank_hom]

private noncomputable def caseBVirtualComap
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B] (q : A →* B) :
    VirtualCharacter B ℂ →+ VirtualCharacter A ℂ :=
  Finsupp.liftAddHom fun chi : IrreducibleCharacter B ℂ ↦
    (smulAddHom ℤ (VirtualCharacter A ℂ)).flip
      (caseBVirtualCharacterOfFDRep
        (FDRep.of (chi.representation.ρ.comp q)))

@[simp] private theorem caseBVirtualComap_single
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B] (q : A →* B)
    (chi : IrreducibleCharacter B ℂ) (z : ℤ) :
    caseBVirtualComap q (Finsupp.single chi z) =
      z • caseBVirtualCharacterOfFDRep
        (FDRep.of (chi.representation.ρ.comp q)) := by
  rw [caseBVirtualComap, Finsupp.liftAddHom_apply_single]
  rfl

private theorem caseB_realize_virtualComap
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B] (q : A →* B)
    (v : VirtualCharacter B ℂ) :
    VirtualCharacter.realize (caseBVirtualComap q v) =
      ClassFunction.comap q (VirtualCharacter.realize v) := by
  classical
  induction v using Finsupp.induction with
  | zero => simp
  | single_add chi z v hchi hz ih =>
      have hsingle :
          VirtualCharacter.realize
              (caseBVirtualComap q (Finsupp.single chi z)) =
            ClassFunction.comap q
              (VirtualCharacter.realize
                (Finsupp.single chi z : VirtualCharacter B ℂ)) := by
        rw [caseBVirtualComap_single, map_zsmul,
          caseB_realize_virtualCharacterOfFDRep,
          VirtualCharacter.realize_single,
          ← Int.cast_smul_eq_zsmul ℂ, map_smul]
        congr 1
        rw [← chi.ofRepresentation_representation]
        ext a
        rfl
      calc
        VirtualCharacter.realize
            (caseBVirtualComap q (Finsupp.single chi z + v)) =
            VirtualCharacter.realize
                (caseBVirtualComap q (Finsupp.single chi z)) +
              VirtualCharacter.realize (caseBVirtualComap q v) := by
                rw [map_add, map_add]
        _ = ClassFunction.comap q
                (VirtualCharacter.realize
                  (Finsupp.single chi z : VirtualCharacter B ℂ)) +
              ClassFunction.comap q (VirtualCharacter.realize v) := by
                rw [hsingle, ih]
        _ = ClassFunction.comap q
              (VirtualCharacter.realize
                (Finsupp.single chi z + v)) := by
                rw [← map_add (ClassFunction.comap q),
                  map_add VirtualCharacter.realize]

private theorem caseB_virtual_comap
    {A B : Type u} [Group A] [Fintype A]
    [Group B] [Fintype B]
    (q : A →* B) {f : ClassFunction B ℂ}
    (hf : ClassFunction.IsVirtual f) :
    ClassFunction.IsVirtual (ClassFunction.comap q f) := by
  obtain ⟨v, hv⟩ := hf
  refine ⟨caseBVirtualComap q v, ?_⟩
  rw [caseB_realize_virtualComap, hv]

/-- The finite support of the irreducible-character expansion, specialized
to literal complex coefficients so that its universe is independent of the
group universe. -/
private noncomputable def caseBConstituents
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) :
    Finset (IrreducibleCharacter Q ℂ) := by
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  exact Finset.univ.filter fun chi ↦ chi.IsConstituent f

@[simp] private theorem caseB_mem_constituents_iff
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) (chi : IrreducibleCharacter Q ℂ) :
    chi ∈ caseBConstituents f ↔ chi.IsConstituent f := by
  classical
  simp [caseBConstituents]

private theorem caseB_sum_constituents_eq
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) :
    (∑ chi ∈ caseBConstituents f,
        characterPairing (chi : ClassFunction Q ℂ) f •
          (chi : ClassFunction Q ℂ)) = f := by
  letI : Invertible (Nat.card Q : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  calc
    _ = irreducibleCharacterExpansion f := by
      rw [irreducibleCharacterExpansion, caseBConstituents,
        Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro chi _
      by_cases hchi : chi.IsConstituent f
      · simp only [hchi, if_true]
      · have hzeroRight :
            characterPairing f (chi : ClassFunction Q ℂ) = 0 :=
          not_ne_iff.mp hchi
        have hzeroLeft :
            characterPairing (chi : ClassFunction Q ℂ) f = 0 :=
          (characterPairing_comm (chi : ClassFunction Q ℂ) f).trans
            hzeroRight
        simp only [hchi, if_false, hzeroLeft, zero_smul]
    _ = f := irreducibleCharacterExpansion_eq f

private theorem caseB_irreducible_apply_one_eq_one_of_isCyclic
    {C : Type u} [Group C] [IsCyclic C]
    (chi : IrreducibleCharacter C ℂ) : chi 1 = 1 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Representation.IsIrreducible chi.representation.ρ :=
    Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
      chi.representation
  have hdim : Module.finrank ℂ chi.representation = 1 :=
    Representation.IsIrreducible.finrank_eq_one_of_isMulCommutative
      chi.representation.ρ
  rw [← chi.representation_character, FDRep.char_one, hdim]
  norm_num

private theorem caseB_irreducible_card_eq_natCard_of_isCyclic
    {C : Type u} [Group C] [Fintype C] [IsCyclic C] :
    Fintype.card (IrreducibleCharacter C ℂ) = Nat.card C := by
  letI : Invertible (Nat.card C : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Fintype (ConjClasses C) := Fintype.ofFinite _
  let basis : Module.Basis (IrreducibleCharacter C ℂ) ℂ
      (ClassFunction C ℂ) :=
    Module.Basis.mk IrreducibleCharacter.linearIndependent (by
      rw [irreducibleCharacter_span_eq_top])
  calc
    Fintype.card (IrreducibleCharacter C ℂ) =
        Module.finrank ℂ (ClassFunction C ℂ) :=
      (Module.finrank_eq_card_basis basis).symm
    _ = Module.finrank ℂ (ConjClasses C → ℂ) :=
      (ClassFunction.conjClassesLinearEquiv (G := C) (k := ℂ)).finrank_eq
    _ = Fintype.card (ConjClasses C) :=
      Module.finrank_fintype_fun_eq_card ℂ
    _ = Fintype.card C :=
      Fintype.card_congr (ConjClasses.mkEquiv (α := C)).symm
    _ = Nat.card C := Fintype.card_eq_nat_card

private theorem caseB_exists_irreducible_ne_trivial_of_one_lt_card
    {C : Type u} [Group C] [Fintype C] [IsCyclic C]
    (hC : 1 < Nat.card C) :
    ∃ chi : IrreducibleCharacter C ℂ,
      chi ≠ IrreducibleCharacter.trivial := by
  apply Fintype.exists_ne_of_one_lt_card
  rw [caseB_irreducible_card_eq_natCard_of_isCyclic]
  exact hC

/-- Source lines 955--981.  The only Dade-specific inputs are the two
coefficient-automorphism compatibility fields in `SibleyCaseBContext`; the
power automorphism itself is constructed here by `make_pi_cfAut`. -/
private theorem caseB_primeDade_constant_on_Z
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) (Z : Subgroup K)
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ)
    (ctx : SibleyCaseBContext K Z X Y tau tau₁ eta₁) :
    ∀ eta ∈ Y, ∀ (x y : G),
      x ∈ ctx.ZG → x ≠ 1 →
      y ∈ ctx.ZG → y ≠ 1 →
        tau₁ eta x = tau₁ eta y := by
  classical
  intro eta heta x y hxZ hx hyZ hy
  rw [← ctx.zToG_range] at hxZ hyZ
  rcases hxZ with ⟨zx, rfl⟩
  rcases hyZ with ⟨zy, rfl⟩
  have hzx : zx ≠ 1 := by
    intro h
    apply hx
    rw [h, map_one]
  have hzy : zy ≠ 1 := by
    intro h
    apply hy
    rw [h, map_one]
  obtain ⟨k, hk, hpow⟩ := ctx.Z_power_transitive zx zy hzx hzy
  obtain ⟨sigma, hsigmaPower, _⟩ :=
    make_pi_cfAut_complex G (Nat.card Z) k hk
  obtain ⟨v, hv⟩ :=
    ctx.Y_coherent.mapsToVirtual eta
      (AddSubgroup.subset_closure heta)
  have horder : orderOf (ctx.zToG zx) ∣ Nat.card Z :=
    (orderOf_map_dvd ctx.zToG zx).trans (orderOf_dvd_natCard zx)
  have hpower := hsigmaPower v (ctx.zToG zx) horder
  rw [hv] at hpower
  have hcomm := ctx.coefficient_automorphism_commutes
    sigma.toRingEquiv eta heta
  have hvanish := ctx.dade_twist_vanishes_on_Z
    sigma.toRingEquiv eta heta zx hzx
  have hfixed :
      sigma (tau₁ eta (ctx.zToG zx)) =
        tau₁ eta (ctx.zToG zx) := by
    have hcommAt := congrArg
      (fun f : ClassFunction G ℂ ↦ f (ctx.zToG zx)) hcomm
    simp only [ClassFunction.mapRingHom_apply] at hcommAt
    rw [map_sub] at hvanish
    simp only [ClassFunction.sub_apply] at hvanish
    rw [← hcommAt] at hvanish
    exact (sub_eq_zero.mp hvanish).symm
  calc
    tau₁ eta (ctx.zToG zx) =
        sigma (tau₁ eta (ctx.zToG zx)) := hfixed.symm
    _ = tau₁ eta ((ctx.zToG zx) ^ k) := hpower
    _ = tau₁ eta (ctx.zToG (zx ^ k)) := by rw [map_pow]
    _ = tau₁ eta (ctx.zToG zy) := by rw [← hpow]

private def caseBRegularClassFunction
    (Q : Type u) [Group Q] [Fintype Q] : ClassFunction Q ℂ where
  val x := if x = 1 then (Nat.card Q : ℂ) else 0
  property g x := by
    by_cases hx : x = 1
    · subst x
      simp
    · have hconj : g * x * g⁻¹ ≠ 1 := by
        intro h
        apply hx
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by rw [h]; simp
      simp [hx, hconj]

private theorem caseB_pairing_regular
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    characterPairing (chi : ClassFunction Q ℂ)
        (caseBRegularClassFunction Q) = chi 1 := by
  rw [characterPairing]
  simp only [caseBRegularClassFunction, inv_eq_one,
    mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ,
    if_true]
  have hcard : (Nat.card Q : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcard]

private theorem caseB_pairing_trivial_of_ne
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ)
    (hchi : chi ≠ IrreducibleCharacter.trivial) :
    characterPairing (chi : ClassFunction Q ℂ)
        ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
          ClassFunction Q ℂ) = 0 := by
  rw [IrreducibleCharacter.characterPairing_eq_ite, if_neg hchi]

/-- Source lines 982--1000: the constant restriction coefficient is an
integral multiple of `[K : Z]`. -/
private theorem caseB_restriction_integer_factor
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) (Z : Subgroup K)
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ)
    (ctx : SibleyCaseBContext K Z X Y tau tau₁ eta₁)
    (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ)
    (hepsilon : IsSign epsilon)
    (himage : tau₁ eta₁ =
      (epsilon : ℂ) • (chi : ClassFunction G ℂ))
    (z₀ : Z) (hz₀ : z₀ ≠ 1) :
    ∃ x₀ : ℤ,
      ClassFunction.comap ctx.zToG (tau₁ eta₁) =
        ((Z.index : ℤ) * x₀ : ℂ) •
            caseBRegularClassFunction Z +
          (tau₁ eta₁ (ctx.zToG z₀)) •
            ((IrreducibleCharacter.trivial : IrreducibleCharacter Z ℂ) :
              ClassFunction Z ℂ) := by
  classical
  let psi₁ := tau₁ eta₁
  let b : ℂ := psi₁ (ctx.zToG z₀)
  have hconstant := caseB_primeDade_constant_on_Z
    K Z X Y tau tau₁ eta₁ ctx
  have hchiConstant : ∀ (x y : G),
      x ∈ ctx.ZG → x ≠ 1 →
      y ∈ ctx.ZG → y ≠ 1 → chi x = chi y := by
    intro x y hxZ hx hyZ hy
    have htau := hconstant eta₁ ctx.eta₁_mem x y hxZ hx hyZ hy
    have hxImage := congrArg
      (fun f : ClassFunction G ℂ ↦ f x) himage
    have hyImage := congrArg
      (fun f : ClassFunction G ℂ ↦ f y) himage
    simp only [ClassFunction.smul_apply, smul_eq_mul] at hxImage hyImage
    have heps : (epsilon : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (isSign_ne_zero hepsilon)
    apply mul_left_cancel₀ heps
    calc
      (epsilon : ℂ) * chi x = psi₁ x := hxImage.symm
      _ = psi₁ y := htau
      _ = (epsilon : ℂ) * chi y := hyImage
  have hzTarget : ctx.zToG z₀ ∈ ctx.ZG := by
    rw [← ctx.zToG_range]
    exact ⟨z₀, rfl⟩
  have hz₀TargetNe : ctx.zToG z₀ ≠ 1 := by
    intro h
    apply hz₀
    exact ctx.zToG_injective (h.trans (map_one ctx.zToG).symm)
  obtain ⟨⟨n, hn⟩, hmod⟩ :=
    ctx.constant_irreducible_mod chi hchiConstant
      (ctx.zToG z₀) hzTarget hz₀TargetNe
  let t : ℂ := Classical.choose hmod
  have htIntegral : IsIntegral ℤ t := (Classical.choose_spec hmod).1
  have ht : chi (ctx.zToG z₀) - chi 1 = (Nat.card K : ℂ) * t :=
    (Classical.choose_spec hmod).2
  let d : ℕ := Module.finrank ℂ chi.representation
  have hchiOne : chi 1 = (d : ℂ) := by
    exact IrreducibleCharacter.apply_one_eq_finrank chi
  have htRat : ∃ q : ℚ, t = (q : ℂ) := by
    refine ⟨((n : ℚ) - (d : ℚ)) / (Nat.card K : ℚ), ?_⟩
    have hcard : (Nat.card K : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    apply (mul_left_cancel₀ hcard)
    rw [← ht]
    rw [hn, hchiOne]
    push_cast
    field_simp [hcard]
  obtain ⟨q₀, hq₀⟩ :=
    (IsIntegral.exists_int_iff_exists_rat htIntegral).mp htRat
  let x₀ : ℤ := -epsilon * q₀
  have hdiff : psi₁ 1 - b =
      (Nat.card K : ℂ) * (x₀ : ℂ) := by
    have hAtOne := congrArg
      (fun f : ClassFunction G ℂ ↦ f 1) himage
    have hAtZ := congrArg
      (fun f : ClassFunction G ℂ ↦ f (ctx.zToG z₀)) himage
    simp only [ClassFunction.smul_apply, smul_eq_mul] at hAtOne hAtZ
    dsimp only [psi₁, b]
    rw [hAtOne, hAtZ]
    rw [hq₀] at ht
    dsimp only [x₀]
    push_cast at ht ⊢
    linear_combination -(epsilon : ℂ) * ht
  refine ⟨x₀, ?_⟩
  ext z
  by_cases hz : z = 1
  · subst z
    simp only [map_one, ClassFunction.comap_apply,
      ClassFunction.add_apply, ClassFunction.smul_apply,
      caseBRegularClassFunction, if_pos, smul_eq_mul,
      IrreducibleCharacter.trivial_apply, one_mul]
    push_cast at hdiff ⊢
    dsimp only [psi₁, b] at hdiff ⊢
    have hcardCast : (Nat.card Z : ℂ) * (Z.index : ℂ) =
        (Nat.card K : ℂ) := by
      exact_mod_cast Z.card_mul_index
    rw [show (Z.index : ℂ) * (x₀ : ℂ) * (Nat.card Z : ℂ) =
        (Nat.card K : ℂ) * (x₀ : ℂ) by
      rw [← hcardCast]
      ring]
    linear_combination hdiff
  · have hzTarget : ctx.zToG z ∈ ctx.ZG := by
      rw [← ctx.zToG_range]
      exact ⟨z, rfl⟩
    have hzTargetNe : ctx.zToG z ≠ 1 := by
      intro h
      apply hz
      exact ctx.zToG_injective (h.trans (map_one ctx.zToG).symm)
    have hvalue := hconstant eta₁ ctx.eta₁_mem
      (ctx.zToG z) (ctx.zToG z₀)
      hzTarget hzTargetNe
      (by rw [← ctx.zToG_range]; exact ⟨z₀, rfl⟩)
      hz₀TargetNe
    simp only [ClassFunction.comap_apply, ClassFunction.add_apply,
      ClassFunction.smul_apply, caseBRegularClassFunction, hz,
      if_false, zero_mul, zero_add, smul_eq_mul,
      IrreducibleCharacter.trivial_apply, mul_one]
    simpa only [mul_zero, zero_add] using hvalue

private theorem caseB_Xspan_pairing_Y_zero
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) (Z : Subgroup K)
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ)
    (ctx : SibleyCaseBContext K Z X Y tau tau₁ eta₁)
    {f : ClassFunction L ℂ}
    (hf : f ∈ AddSubgroup.closure
      (↑X : Set (ClassFunction L ℂ)))
    {eta : ClassFunction L ℂ} (heta : eta ∈ Y) :
    characterPairing f eta = 0 := by
  induction hf using AddSubgroup.closure_induction with
  | mem xi hxi =>
      exact ctx.source_subcoherent.pairwise_orthogonal
        (ctx.X_family.1 hxi) (ctx.Y_family.1 heta)
        (ctx.X_Y_disjoint xi hxi eta heta).symm
  | zero => simp
  | add f g _ _ hf hg =>
      rw [characterPairing_add_left, hf, hg, add_zero]
  | neg f _ hf =>
      rw [caseB_pairing_neg_left, hf, neg_zero]

private theorem caseB_candidate_pairing_self
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (Y : Finset (ClassFunction L ℂ))
    (tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ) (x : ℤ)
    (heta₁ : eta₁ ∈ Y)
    (horth : ∀ eta ∈ Y, ∀ zeta ∈ Y,
      characterPairing (tau₁ eta) (tau₁ zeta) =
        if eta = zeta then 1 else 0) :
    characterPairing
        (sibleyCaseBPivotCandidate Y tau₁ eta₁ x)
        (sibleyCaseBPivotCandidate Y tau₁ eta₁ x) =
      (((x - 1) ^ 2 +
        ((Y.card - 1 : ℕ) : ℤ) * x ^ 2 : ℤ) : ℂ) := by
  classical
  let c : ClassFunction L ℂ → ℂ := fun eta ↦
    (x : ℂ) - if eta = eta₁ then 1 else 0
  have hdiag :
      characterPairing
          (sibleyCaseBPivotCandidate Y tau₁ eta₁ x)
          (sibleyCaseBPivotCandidate Y tau₁ eta₁ x) =
        ∑ eta ∈ Y, c eta ^ 2 := by
    simp only [sibleyCaseBPivotCandidate]
    rw [caseB_pairing_neg_left, caseB_pairing_neg_right, neg_neg]
    rw [caseB_pairing_finset_sum_left]
    apply Finset.sum_congr rfl
    intro eta heta
    rw [characterPairing_smul_left,
      caseB_pairing_finset_sum_right]
    rw [Finset.sum_eq_single eta]
    · rw [characterPairing_smul_right,
        horth eta heta eta heta, if_pos rfl]
      simp only [mul_one, c]
      ring
    · intro zeta hzeta hne
      rw [characterPairing_smul_right,
        horth eta heta zeta hzeta, if_neg hne.symm, mul_zero]
    · exact fun h ↦ (h heta).elim
  rw [hdiag, ← Y.add_sum_erase (fun eta ↦ c eta ^ 2) heta₁]
  have hrest : ∑ eta ∈ Y.erase eta₁, c eta ^ 2 =
      (Y.card - 1 : ℕ) * (x : ℂ) ^ 2 := by
    calc
      ∑ eta ∈ Y.erase eta₁, c eta ^ 2 =
          ∑ _eta ∈ Y.erase eta₁, (x : ℂ) ^ 2 := by
        apply Finset.sum_congr rfl
        intro eta heta
        have hne := (Finset.mem_erase.mp heta).1
        simp [c, hne]
      _ = (Y.erase eta₁).card * (x : ℂ) ^ 2 := by simp
      _ = (Y.card - 1 : ℕ) * (x : ℂ) ^ 2 := by
        rw [Finset.card_erase_of_mem heta₁]
  rw [hrest]
  simp only [c, if_pos]
  push_cast
  ring

private theorem caseB_coefficient_dichotomy
    (x : ℤ) (m : ℕ) (hm : 2 ≤ m)
    (hbound :
      (x - 1) ^ 2 + ((m - 1 : ℕ) : ℤ) * x ^ 2 < 2) :
    x = 0 ∨ (x = 1 ∧ m = 2) := by
  by_cases hx0 : x = 0
  · exact Or.inl hx0
  by_cases hx1 : x = 1
  · right
    refine ⟨hx1, ?_⟩
    subst x
    norm_num at hbound
    omega
  · have hxm : 1 ≤ m - 1 := by omega
    have hxmCast : (1 : ℤ) ≤ ((m - 1 : ℕ) : ℤ) := by
      exact_mod_cast hxm
    have hxSqPos : 0 < x ^ 2 := sq_pos_of_ne_zero hx0
    have hxOneSqPos : 0 < (x - 1) ^ 2 := by
      exact sq_pos_of_ne_zero (sub_ne_zero.mpr hx1)
    have hxSqOne : (1 : ℤ) ≤ x ^ 2 := by omega
    have hxOneSqOne : (1 : ℤ) ≤ (x - 1) ^ 2 := by omega
    have hxSqNonneg : (0 : ℤ) ≤ x ^ 2 := sq_nonneg x
    have hproduct :
        x ^ 2 ≤ ((m - 1 : ℕ) : ℤ) * x ^ 2 := by
      nlinarith
    have htwo :
        (2 : ℤ) ≤
          (x - 1) ^ 2 + ((m - 1 : ℕ) : ℤ) * x ^ 2 := by
      nlinarith
    exact (not_lt_of_ge htwo hbound).elim

private theorem irreducibleCharacter_apply_one_ne_zero_caseB
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) : chi 1 ≠ 0 := by
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation := by
    rw [← not_subsingleton_iff_nontrivial]
    intro hsub
    apply CategoryTheory.id_nonzero chi.representation
    apply CategoryTheory.ConcreteCategory.hom_ext
    intro x
    exact Subsingleton.elim _ _
  rw [← chi.representation_character, FDRep.char_one]
  exact Nat.cast_ne_zero.mpr Module.finrank_pos.ne'

private theorem virtual_eq_zero_of_pairing_self_eq_zero_caseB
    {Q : Type u} [Group Q] [Fintype Q]
    {phi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hzero : characterPairing phi phi = 0) : phi = 0 := by
  obtain ⟨z, hz⟩ := hphi
  have hcast : ((normSq z : ℤ) : ℂ) = 0 := by
    rw [← VirtualCharacter.characterPairing_realize_self, hz]
    exact hzero
  have hnorm0 : normSq z = 0 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_zero] using hcast
  have hz0 : z = 0 := (normSq_eq_zero_iff z).mp hnorm0
  rw [← hz, hz0]
  simp

private theorem caseB_inverseLinear_involutive
    {Q : Type u} [Group Q] (f : ClassFunction Q ℂ) :
    ClassFunction.inverseLinear (ClassFunction.inverseLinear f) = f := by
  ext x
  simp

private theorem caseB_inverse_sub_supported
    {Q : Type u} [Group Q] (f : ClassFunction Q ℂ) :
    f - ClassFunction.inverseLinear f ∈
      ClassFunction.supportedOn (nonidentitySet Q) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  have hx1 : x = 1 := by
    simpa [nonidentitySet] using not_not.mp hx
  subst x
  simp

private theorem caseB_virtual_intCast_smul
    {Q : Type u} [Group Q]
    {f : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f) (n : ℤ) :
    ClassFunction.IsVirtual ((n : ℂ) • f) := by
  obtain ⟨v, hv⟩ := hf
  refine ⟨n • v, ?_⟩
  calc
    VirtualCharacter.realize (n • v) =
        n • VirtualCharacter.realize v := by rw [map_zsmul]
    _ = (n : ℂ) • f := by
      rw [hv, ← Int.cast_smul_eq_zsmul ℂ]

/-- The data attached to one constituent of `Ind_Z^K phi`, before the
global weighted sum forces its coefficient to be the Clifford
multiplicity. -/
private structure CaseBCliffordTermData
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (tau : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (chi eta : ClassFunction L ℂ)
    (m : ℕ) (Y₁ : ClassFunction G ℂ) where
  coefficient : ℤ
  mainPart : ClassFunction G ℂ
  residual : ClassFunction G ℂ
  residualNorm : ℕ
  coefficient_le : coefficient ≤ (m : ℤ)
  mainPart_orthogonal : characterPairing mainPart Y₁ = 0
  residual_orthogonal : characterPairing residual Y₁ = 0
  residual_virtual : ClassFunction.IsVirtual residual
  residual_norm :
    characterPairing residual residual = (residualNorm : ℂ)
  norm_bound :
    coefficient ^ 2 + (residualNorm : ℤ) ≤ (m : ℤ) ^ 2
  decomposition :
    tau (chi - (m : ℂ) • eta) =
      mainPart - (coefficient : ℂ) • Y₁ + residual

/-- A nontrivial central restriction character prevents the ambient
irreducible from having the central subgroup in its translation kernel. -/
private theorem caseB_not_le_kernel_of_central_character_ne_trivial
    {K : Type u} [Group K] [Fintype K]
    (Z : Subgroup K) (theta : IrreducibleCharacter K ℂ)
    (phi : IrreducibleCharacter Z ℂ) (m : ℕ)
    (hm : 0 < m)
    (hdegree : theta 1 = (m : ℂ))
    (hrestrict :
      ClassFunction.restrict Z (theta : ClassFunction K ℂ) =
        (m : ℂ) • (phi : ClassFunction Z ℂ))
    (hphi : phi ≠ IrreducibleCharacter.trivial) :
    ¬Z ≤ ClassFunction.translationKernel
      (theta : ClassFunction K ℂ) := by
  intro hkernel
  apply hphi
  apply Subtype.ext
  ext z
  have hzKernel := hkernel z.property (1 : K)
  have hzRestrict := congrArg
    (fun f : ClassFunction Z ℂ ↦ f z) hrestrict
  simp only [ClassFunction.restrict_apply, ClassFunction.smul_apply,
    smul_eq_mul] at hzRestrict
  have hm0 : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm.ne'
  apply mul_left_cancel₀ hm0
  calc
    (m : ℂ) * phi z = theta (z : K) := hzRestrict.symm
    _ = theta 1 := by simpa using hzKernel
    _ = (m : ℂ) *
        (IrreducibleCharacter.trivial : IrreducibleCharacter Z ℂ) z := by
      rw [hdegree]
      simp

/-- If the central character in a scalar central restriction were trivial,
then the central subgroup would act trivially.  This is the one direction
needed to show that the character selected from a member of `X` is
nontrivial. -/
private theorem caseB_central_character_ne_trivial
    {K : Type u} [Group K] [Fintype K]
    (Z : Subgroup K) (hZcentral : Z ≤ Subgroup.center K)
    (theta : IrreducibleCharacter K ℂ)
    (a : ℕ) (ha : 0 < a)
    (hdegree : theta 1 = (a : ℂ))
    (phi : IrreducibleCharacter Z ℂ)
    (hrestrict :
      ClassFunction.restrict Z (theta : ClassFunction K ℂ) =
        (a : ℂ) • (phi : ClassFunction Z ℂ))
    (hnotKernel :
      ¬Z ≤ ClassFunction.translationKernel
        (theta : ClassFunction K ℂ)) :
    phi ≠ IrreducibleCharacter.trivial := by
  intro hphi
  apply hnotKernel
  intro z hz
  let zc : Subgroup.center K := ⟨z, hZcentral hz⟩
  let rho : Representation ℂ K theta.representation :=
    theta.representation.ρ
  letI : CategoryTheory.Simple theta.representation :=
    theta.representation_simple
  letI : Representation.IsIrreducible rho :=
    Submission.OddOrder.MathlibSupport.representation_isIrreducible_of_simple_fdRep
      theta.representation
  have hdim : (Module.finrank ℂ theta.representation : ℂ) = (a : ℂ) := by
    rw [← IrreducibleCharacter.apply_one_eq_finrank, hdegree]
  have hzRestrict := congrArg
    (fun f : ClassFunction Z ℂ ↦ f ⟨z, hz⟩) hrestrict
  simp only [ClassFunction.restrict_apply, ClassFunction.smul_apply,
    smul_eq_mul, hphi, IrreducibleCharacter.trivial_apply, mul_one]
      at hzRestrict
  have hcenter :=
    character_center_eq_finrank_mul_schurCenterScalarCharacter rho zc
  have hscalar :
      (schurCenterScalarCharacter rho zc : ℂ) = 1 := by
    have ha0 : (a : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr ha.ne'
    apply mul_left_cancel₀ ha0
    calc
      (a : ℂ) * (schurCenterScalarCharacter rho zc : ℂ) =
          rho.character zc := by rw [← hdim, hcenter]
      _ = theta z := by
        change theta.representation.character z = theta z
        exact theta.representation_character z
      _ = (a : ℂ) := hzRestrict
      _ = (a : ℂ) * 1 := by ring
  have hzrho : rho z = 1 := by
    apply LinearMap.ext
    intro v
    change rho z v = v
    calc
      rho z v = rho zc v := rfl
      _ = (schurCenterScalarCharacter rho zc : ℂ) • v :=
        schurCenterScalarCharacter_smul rho zc v
      _ = v := by rw [hscalar, one_smul]
  rw [ClassFunction.mem_translationKernel_iff]
  intro g
  rw [← theta.representation_character,
    ← theta.representation_character]
  change LinearMap.trace ℂ theta.representation (rho (z * g)) =
    LinearMap.trace ℂ theta.representation (rho g)
  rw [map_mul, hzrho, one_mul]

/-- Source lines 1148--1239 for one Clifford constituent.  Projection onto
the subcoherent target column gives `P - V`; projecting `V` further onto the
common pivot gives the integer coefficient and the residual.  The first
half of `subcoherent_norm` supplies the squared-norm inequality. -/
private noncomputable def caseB_clifford_term
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) (Z : Subgroup K)
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ)
    (ctx : SibleyCaseBContext K Z X Y tau tau₁ eta₁)
    (phi : IrreducibleCharacter Z ℂ)
    (hphi : phi ≠ IrreducibleCharacter.trivial)
    (i : IrreducibleCharacter K ℂ)
    (hi : i ∈ caseBConstituents
      (ClassFunction.induce Z (phi : ClassFunction Z ℂ)))
    (Y₁ : ClassFunction G ℂ)
    (hY₁Virtual : ClassFunction.IsVirtual Y₁)
    (hY₁Norm : characterPairing Y₁ Y₁ = 1)
    (hY₁Span : ∃ v ∈ AddSubgroup.closure
      (↑Y : Set (ClassFunction L ℂ)), tau₁ v = Y₁) :
    let m := IrreducibleCharacter.centralRestrictionMultiplicity Z i phi
    let chi := ClassFunction.induce K (i : ClassFunction K ℂ)
    CaseBCliffordTermData tau chi eta₁ m Y₁ := by
  classical
  let F : ClassFunction K ℂ :=
    ClassFunction.induce Z (phi : ClassFunction Z ℂ)
  let m : ℕ :=
    IrreducibleCharacter.centralRestrictionMultiplicity Z i phi
  have hpairNe : characterPairing F (i : ClassFunction K ℂ) ≠ 0 := by
    exact (caseB_mem_constituents_iff F i).mp hi
  obtain ⟨hiDegree, hphiDegree, hiRestrict, hiPair⟩ :=
    IrreducibleCharacter.central_restriction_eq_multiplicity_smul_of_induce_pairing_ne_zero
      Z ctx.Z_central i phi hpairNe
  have hmPos : 0 < m := by
    apply Nat.pos_of_ne_zero
    intro hm0
    have hm0' :
        IrreducibleCharacter.centralRestrictionMultiplicity Z i phi = 0 := by
      simpa only [m] using hm0
    apply irreducibleCharacter_apply_one_ne_zero_caseB i
    rw [hiDegree, hm0']
    norm_num
  let chi : ClassFunction L ℂ :=
    ClassFunction.induce K (i : ClassFunction K ℂ)
  have hiNotKernel :
      ¬Z ≤ ClassFunction.translationKernel
        (i : ClassFunction K ℂ) :=
    caseB_not_le_kernel_of_central_character_ne_trivial
      Z i phi m hmPos hiDegree hiRestrict hphi
  have hchiX : chi ∈ X := by
    exact (ctx.X_characterization i).2 hiNotKernel
  have hchiS : chi ∈ ctx.sourceFamily := ctx.X_family.1 hchiX
  have hchiNotY : chi ∉ (↑Y : Set (ClassFunction L ℂ)) := by
    intro hchiY
    exact ctx.X_Y_disjoint chi hchiX chi hchiY rfl
  have hetaS : eta₁ ∈ ctx.sourceFamily :=
    ctx.Y_family.1 ctx.eta₁_mem
  have hchiEta : characterPairing chi eta₁ = 0 :=
    ctx.source_subcoherent.pairwise_orthogonal hchiS hetaS
      (ctx.X_Y_disjoint chi hchiX eta₁ ctx.eta₁_mem).symm
  let chic : ClassFunction L ℂ := ClassFunction.inverseLinear chi
  have hchicS : chic ∈ ctx.sourceFamily :=
    ctx.source_subcoherent.inverse_mem chi hchiS
  have hchicNotY : chic ∉ (↑Y : Set (ClassFunction L ℂ)) := by
    intro hchicY
    have hchiY := ctx.Y_family.2 chic hchicY
    rw [caseB_inverseLinear_involutive] at hchiY
    exact hchiNotY hchiY
  have hchicEta : characterPairing chic eta₁ = 0 :=
    ctx.source_subcoherent.pairwise_orthogonal hchicS hetaS
      (by
        intro heq
        exact hchicNotY (heq.symm ▸ ctx.eta₁_mem))
  let psi : ClassFunction L ℂ := (m : ℂ) • eta₁
  let beta : ClassFunction L ℂ := chi - psi
  have hetaVirtual : ClassFunction.IsVirtual eta₁ :=
    ctx.source_subcoherent.source_virtual eta₁ hetaS
  have hpsiVirtual : ClassFunction.IsVirtual psi := by
    simpa only [psi] using hetaVirtual.natCast_smul m
  have hchiPsi : characterPairing chi psi = 0 := by
    simp only [psi, characterPairing_smul_right, hchiEta, mul_zero]
  have hchicPsi : characterPairing chic psi = 0 := by
    simp only [psi, characterPairing_smul_right, hchicEta, mul_zero]
  have hbetaSpan : beta ∈ AddSubgroup.closure ctx.sourceFamily := by
    apply (AddSubgroup.closure ctx.sourceFamily).sub_mem
      (AddSubgroup.subset_closure hchiS)
    simpa only [psi, Nat.cast_smul_eq_nsmul] using
      (AddSubgroup.closure ctx.sourceFamily).nsmul_mem
        (AddSubgroup.subset_closure hetaS) m
  have hchiDegree : chi 1 = (m : ℂ) * eta₁ 1 := by
    simp only [chi]
    rw [ClassFunction.induce_one, hiDegree,
      ctx.Y_degree eta₁ ctx.eta₁_mem]
    push_cast
    ring
  have hbetaOff : beta ∈
      ClassFunction.supportedOn (nonidentitySet L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hx1 : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [beta, psi, ClassFunction.sub_apply,
      ClassFunction.smul_apply, smul_eq_mul, hchiDegree, sub_self]
  have htauBetaVirtual : ClassFunction.IsVirtual (tau beta) :=
    ctx.source_subcoherent.tau_virtual beta hbetaSpan hbetaOff
  let splitExists :=
    subcoherent_split ctx.source_subcoherent hchiS htauBetaVirtual
  let P : ClassFunction G ℂ := Classical.choose splitExists
  have hPspec := Classical.choose_spec splitExists
  have hPSpan := hPspec.1
  have hPVirtual := hPspec.2.1
  let vExists := hPspec.2.2
  let V : ClassFunction G ℂ := Classical.choose vExists
  have hVspec := Classical.choose_spec vExists
  have hVVirtual := hVspec.1
  have hsplit := hVspec.2.1
  have hPV := hVspec.2.2.1
  have hVR := hVspec.2.2.2
  let vY : ClassFunction L ℂ := Classical.choose hY₁Span
  have hvYspec := Classical.choose_spec hY₁Span
  have hvY := hvYspec.1
  have hvYeq := hvYspec.2
  have hPY₁ : characterPairing P Y₁ = 0 := by
    rw [← hvYeq, characterPairing_comm]
    have horth := coherent_ortho_supp
      ctx.source_subcoherent ctx.Y_family ctx.Y_coherent
      hchiS hchiNotY
    have horthSpan (p : ClassFunction G ℂ)
        (hp : p ∈ AddSubgroup.closure
          (↑(ctx.targetColumns chi) : Set (ClassFunction G ℂ))) :
        characterPairing (tau₁ vY) p = 0 := by
      induction hp using AddSubgroup.closure_induction with
      | mem alpha halpha =>
          exact horth (tau₁ vY) ⟨vY, hvY, rfl⟩ alpha halpha
      | zero => simp
      | add f g _ _ hf hg =>
          rw [characterPairing_add_right, hf, hg, add_zero]
      | neg f _ hf =>
          rw [caseB_pairing_neg_right, hf, neg_zero]
    exact horthSpan P hPSpan
  let bExists := caseB_virtual_pairing_eq_int hVVirtual hY₁Virtual
  let b : ℤ := Classical.choose bExists
  have hb := Classical.choose_spec bExists
  let residual : ClassFunction G ℂ := (b : ℂ) • Y₁ - V
  have hresVirtual : ClassFunction.IsVirtual residual := by
    exact (caseB_virtual_intCast_smul hY₁Virtual b).sub hVVirtual
  have hresY₁ : characterPairing residual Y₁ = 0 := by
    simp only [residual]
    rw [caseB_pairing_sub_left, characterPairing_smul_left,
      hY₁Norm, hb]
    ring
  let nExists := hresVirtual.exists_nat_norm
  let n : ℕ := Classical.choose nExists
  have hn := Classical.choose_spec nExists
  have htermDecomp :
      tau (chi - (m : ℂ) • eta₁) =
        P - (b : ℂ) • Y₁ + residual := by
    change tau beta = _
    rw [hsplit]
    simp only [residual]
    abel
  let S0 : Set (ClassFunction L ℂ) :=
    {beta, chi - chic}
  have hS0Span : AddSubgroup.closure S0 ≤
      AddSubgroup.closure ctx.sourceFamily := by
    refine (AddSubgroup.closure_le
      (AddSubgroup.closure ctx.sourceFamily)).2 ?_
    intro f hf
    rcases hf with (rfl | rfl)
    · exact hbetaSpan
    · exact (AddSubgroup.closure ctx.sourceFamily).sub_mem
        (AddSubgroup.subset_closure hchiS)
        (AddSubgroup.subset_closure hchicS)
  have hS0Off : ∀ f ∈ AddSubgroup.closure S0,
      f ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    intro f hf
    induction hf using AddSubgroup.closure_induction with
    | mem f hf =>
        rcases hf with (rfl | rfl)
        · exact hbetaOff
        · simpa only [chic] using caseB_inverse_sub_supported chi
    | zero =>
        exact (ClassFunction.supportedOn
          (R := ℂ) (nonidentitySet L)).zero_mem
    | add f g _ _ hf hg =>
        exact (ClassFunction.supportedOn
          (R := ℂ) (nonidentitySet L)).add_mem hf hg
    | neg f _ hf =>
        exact (ClassFunction.supportedOn
          (R := ℂ) (nonidentitySet L)).neg_mem hf
  have hnorm := subcoherent_norm ctx.source_subcoherent hchiS
    hpsiVirtual hchiPsi hchicPsi tau
    (fun f hf g hg ↦
      ctx.source_subcoherent.tau_isometry f (hS0Span hf) (hS0Off f hf)
        g (hS0Span hg) (hS0Off g hg))
    (fun f hf ↦
      ctx.source_subcoherent.tau_virtual f (hS0Span hf) (hS0Off f hf))
    rfl hPVirtual hVVirtual
    (by simpa only [beta, psi] using hsplit) hPV hVR
  let gapExists := hnorm.1
  let gap : ℕ := Classical.choose gapExists
  have hgap := Classical.choose_spec gapExists
  have hetaNorm : characterPairing eta₁ eta₁ = 1 := by
    rw [ctx.Y_orthonormal eta₁ ctx.eta₁_mem eta₁ ctx.eta₁_mem,
      if_pos rfl]
  have hsourceNorm : characterPairing beta beta =
      characterPairing chi chi + (m : ℂ) ^ 2 := by
    simp only [beta, psi]
    rw [pairing_self_sub_of_orthogonal_caseB chi ((m : ℂ) • eta₁)
      (by rw [characterPairing_smul_right, hchiEta, mul_zero]),
      characterPairing_smul_left, characterPairing_smul_right,
      hetaNorm]
    ring
  have htargetNorm : characterPairing (tau beta) (tau beta) =
      characterPairing P P + characterPairing V V := by
    rw [hsplit, pairing_self_sub_of_orthogonal_caseB P V hPV]
  have hisoNorm : characterPairing (tau beta) (tau beta) =
      characterPairing beta beta :=
    ctx.source_subcoherent.tau_isometry beta hbetaSpan hbetaOff
      beta hbetaSpan hbetaOff
  have hresComm : characterPairing ((b : ℂ) • Y₁) residual = 0 := by
    rw [characterPairing_smul_left, characterPairing_comm Y₁ residual,
      hresY₁, mul_zero]
  have hVNorm : characterPairing V V =
      (b : ℂ) ^ 2 + (n : ℂ) := by
    have hVeq : V = (b : ℂ) • Y₁ - residual := by
      simp only [residual]
      abel
    rw [hVeq, pairing_self_sub_of_orthogonal_caseB
      ((b : ℂ) • Y₁) residual hresComm,
      characterPairing_smul_left, characterPairing_smul_right,
      hY₁Norm, hn]
    ring
  have hbalanceCast :
      ((b ^ 2 + (n : ℤ) + (gap : ℤ) : ℤ) : ℂ) =
        (((m : ℤ) ^ 2 : ℤ) : ℂ) := by
    rw [Int.cast_add, Int.cast_add, Int.cast_pow,
      Int.cast_natCast, Int.cast_natCast, Int.cast_pow]
    rw [hgap] at htargetNorm
    rw [hisoNorm, hsourceNorm, hVNorm] at htargetNorm
    linear_combination -htargetNorm
  have hbalance :
      b ^ 2 + (n : ℤ) + (gap : ℤ) = (m : ℤ) ^ 2 := by
    exact Int.cast_injective hbalanceCast
  have hbound : b ^ 2 + (n : ℤ) ≤ (m : ℤ) ^ 2 := by
    have hgap0 : (0 : ℤ) ≤ (gap : ℤ) := by exact_mod_cast gap.zero_le
    nlinarith
  have hble : b ≤ (m : ℤ) := by
    have hn0 : (0 : ℤ) ≤ (n : ℤ) := by exact_mod_cast n.zero_le
    nlinarith [sq_nonneg (b + (m : ℤ))]
  exact
    { coefficient := b
      mainPart := P
      residual := residual
      residualNorm := n
      coefficient_le := hble
      mainPart_orthogonal := hPY₁
      residual_orthogonal := hresY₁
      residual_virtual := hresVirtual
      residual_norm := hn
      norm_bound := hbound
      decomposition := htermDecomp }

private theorem caseB_common_pivot
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) (Z : Subgroup K)
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ)
    (ctx : SibleyCaseBContext K Z X Y tau tau₁ eta₁) :
    ∃ (x : ℤ) (Y₁ : ClassFunction G ℂ),
      Y₁ = sibleyCaseBPivotCandidate Y tau₁ eta₁ x ∧
      ClassFunction.IsVirtual Y₁ ∧
      characterPairing Y₁ Y₁ = 1 ∧
      (∃ v ∈ AddSubgroup.closure
        (↑Y : Set (ClassFunction L ℂ)), tau₁ v = Y₁) ∧
      ∀ i : IrreducibleCharacter Z ℂ,
        i ≠ IrreducibleCharacter.trivial →
        ∃ X₂ : ClassFunction G ℂ,
          characterPairing X₂ Y₁ = 0 ∧
          tau (ctx.centralInduce i - (Z.index : ℂ) • eta₁) =
            X₂ - (Z.index : ℂ) • Y₁ := by
  classical
  letI : IsCyclic Z := ctx.Z_cyclic
  have hetaTauVirtual : ClassFunction.IsVirtual (tau₁ eta₁) :=
    ctx.Y_coherent.mapsToVirtual eta₁
      (AddSubgroup.subset_closure ctx.eta₁_mem)
  have hetaTauNorm :
      characterPairing (tau₁ eta₁) (tau₁ eta₁) = 1 := by
    rw [ctx.Y_coherent.isometry eta₁
      (AddSubgroup.subset_closure ctx.eta₁_mem)
      eta₁ (AddSubgroup.subset_closure ctx.eta₁_mem),
      ctx.Y_orthonormal eta₁ ctx.eta₁_mem eta₁ ctx.eta₁_mem,
      if_pos rfl]
  obtain ⟨chi, epsilon, hepsilon, himage⟩ :=
    caseB_exists_signed_irreducible hetaTauVirtual hetaTauNorm
  obtain ⟨z₀, hz₀⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp ctx.Z_nontrivial
  obtain ⟨x₀, hrestriction⟩ :=
    caseB_restriction_integer_factor K Z X Y tau tau₁ eta₁ ctx
      chi epsilon hepsilon himage z₀ hz₀
  let psiL : ClassFunction L ℂ :=
    ClassFunction.comap ctx.embedLtoG (tau₁ eta₁)
  have hpsiLVirtual : ClassFunction.IsVirtual psiL :=
    caseB_virtual_comap ctx.embedLtoG hetaTauVirtual
  have hetaVirtual : ClassFunction.IsVirtual eta₁ :=
    ctx.source_subcoherent.source_virtual eta₁
      (ctx.Y_family.1 ctx.eta₁_mem)
  obtain ⟨s, hs⟩ :=
    caseB_virtual_pairing_eq_int hetaVirtual hpsiLVirtual
  let x : ℤ := x₀ + 1 - s
  let ySource : ClassFunction L ℂ :=
    -∑ eta ∈ Y,
      ((x : ℂ) - if eta = eta₁ then 1 else 0) • eta
  let Y₁ : ClassFunction G ℂ := tau₁ ySource
  have hySourceSpan : ySource ∈ AddSubgroup.closure
      (↑Y : Set (ClassFunction L ℂ)) := by
    dsimp only [ySource]
    apply (AddSubgroup.closure
      (↑Y : Set (ClassFunction L ℂ))).neg_mem
    apply AddSubgroup.sum_mem
    intro eta heta
    by_cases heq : eta = eta₁
    · subst eta
      have hmem := (AddSubgroup.closure
        (↑Y : Set (ClassFunction L ℂ))).zsmul_mem
          (AddSubgroup.subset_closure heta) (x - 1)
      rw [← Int.cast_smul_eq_zsmul ℂ] at hmem
      simpa only [if_pos rfl, if_true, Int.cast_sub, Int.cast_one]
        using hmem
    · have hmem := (AddSubgroup.closure
        (↑Y : Set (ClassFunction L ℂ))).zsmul_mem
          (AddSubgroup.subset_closure heta) x
      rw [← Int.cast_smul_eq_zsmul ℂ] at hmem
      simpa only [if_neg heq, sub_zero] using hmem
  have hY₁Candidate :
      Y₁ = sibleyCaseBPivotCandidate Y tau₁ eta₁ x := by
    dsimp only [Y₁, ySource, sibleyCaseBPivotCandidate]
    rw [map_neg, map_sum]
    apply congrArg Neg.neg
    apply Finset.sum_congr rfl
    intro eta heta
    rw [map_smul]
  have hY₁Virtual : ClassFunction.IsVirtual Y₁ :=
    ctx.Y_coherent.mapsToVirtual ySource hySourceSpan
  have hYtauOrth : ∀ eta ∈ Y, ∀ zeta ∈ Y,
      characterPairing (tau₁ eta) (tau₁ zeta) =
        if eta = zeta then 1 else 0 := by
    intro eta heta zeta hzeta
    rw [ctx.Y_coherent.isometry eta
      (AddSubgroup.subset_closure heta)
      zeta (AddSubgroup.subset_closure hzeta)]
    exact ctx.Y_orthonormal eta heta zeta hzeta
  have hY₁NormFormula : characterPairing Y₁ Y₁ =
      ((((x - 1) ^ 2 +
        ((Y.card - 1 : ℕ) : ℤ) * x ^ 2 : ℤ)) : ℂ) := by
    rw [hY₁Candidate]
    exact caseB_candidate_pairing_self Y tau₁ eta₁ x
      ctx.eta₁_mem hYtauOrth
  have hcommonBridge : ∀ i : IrreducibleCharacter Z ℂ,
      i ≠ IrreducibleCharacter.trivial →
      ∃ X₂ : ClassFunction G ℂ,
        characterPairing X₂ Y₁ = 0 ∧
        tau (ctx.centralInduce i - (Z.index : ℂ) • eta₁) =
          X₂ - (Z.index : ℂ) • Y₁ := by
    intro i hi
    let gamma : ClassFunction L ℂ :=
      ctx.centralInduce i - (Z.index : ℂ) • eta₁
    let X₂ : ClassFunction G ℂ :=
      tau gamma + (Z.index : ℂ) • Y₁
    have hiDegree : i 1 = 1 :=
      caseB_irreducible_apply_one_eq_one_of_isCyclic i
    have hpairInd : characterPairing
        (tau (ctx.centralInduce i)) (tau₁ eta₁) =
          ((Z.index : ℤ) * x₀ : ℂ) := by
      rw [ctx.centralInduce_pairing i (tau₁ eta₁), hrestriction,
        characterPairing_add_right, characterPairing_smul_right,
        characterPairing_smul_right,
        caseB_pairing_regular i,
        caseB_pairing_trivial_of_ne i hi, hiDegree]
      ring
    have hpairGammaEta₁ :
        characterPairing (tau gamma) (tau₁ eta₁) =
          (Z.index : ℂ) * ((x₀ : ℂ) - (s : ℂ)) := by
      dsimp only [gamma]
      rw [map_sub, map_smul, caseB_pairing_sub_left,
        characterPairing_smul_left, hpairInd,
        ctx.frobenius_reciprocity eta₁ (tau₁ eta₁)]
      change characterPairing eta₁ psiL = (s : ℂ) at hs
      rw [hs]
      push_cast
      ring
    have hY₁Eta₁ :
        characterPairing Y₁ (tau₁ eta₁) =
          (1 : ℂ) - (x : ℂ) := by
      rw [hY₁Candidate]
      simp only [sibleyCaseBPivotCandidate]
      rw [caseB_pairing_neg_left, caseB_pairing_finset_sum_left]
      rw [Finset.sum_eq_single eta₁]
      · rw [characterPairing_smul_left,
          hYtauOrth eta₁ ctx.eta₁_mem eta₁ ctx.eta₁_mem,
          if_pos rfl]
        simp
      · intro eta heta hne
        rw [characterPairing_smul_left,
          hYtauOrth eta heta eta₁ ctx.eta₁_mem,
          if_neg hne, mul_zero]
      · exact fun h ↦ (h ctx.eta₁_mem).elim
    have hX₂Eta₁ : characterPairing X₂ (tau₁ eta₁) = 0 := by
      dsimp only [X₂]
      rw [characterPairing_add_left, characterPairing_smul_left,
        hpairGammaEta₁, hY₁Eta₁]
      dsimp only [x]
      push_cast
      ring
    have hX₂Each : ∀ eta ∈ Y,
        characterPairing X₂ (tau₁ eta) = 0 := by
      intro eta heta
      by_cases heq : eta = eta₁
      · subst eta
        exact hX₂Eta₁
      · let d := eta - eta₁
        have hdSpanY : d ∈ AddSubgroup.closure
            (↑Y : Set (ClassFunction L ℂ)) :=
          (AddSubgroup.closure
            (↑Y : Set (ClassFunction L ℂ))).sub_mem
              (AddSubgroup.subset_closure heta)
              (AddSubgroup.subset_closure ctx.eta₁_mem)
        have hdSpanS : d ∈ AddSubgroup.closure ctx.sourceFamily :=
          AddSubgroup.closure_mono ctx.Y_family.1 hdSpanY
        have hdOff : d ∈ ClassFunction.supportedOn
            (nonidentitySet L) := by
          rw [ClassFunction.mem_supportedOn_iff]
          intro g hg
          have hg1 : g = 1 := by
            simpa [nonidentitySet] using not_not.mp hg
          subst g
          simp only [d, ClassFunction.sub_apply]
          rw [ctx.Y_degree eta heta,
            ctx.Y_degree eta₁ ctx.eta₁_mem, sub_self]
        have hgammaSpanX : ctx.centralInduce i ∈
            AddSubgroup.closure
              (↑X : Set (ClassFunction L ℂ)) :=
          ctx.centralInduce_mem_X_span i hi
        have hgammaSpanS : gamma ∈
            AddSubgroup.closure ctx.sourceFamily := by
          dsimp only [gamma]
          apply (AddSubgroup.closure ctx.sourceFamily).sub_mem
          · exact AddSubgroup.closure_mono ctx.X_family.1 hgammaSpanX
          · rw [Nat.cast_smul_eq_nsmul]
            exact (AddSubgroup.closure ctx.sourceFamily).nsmul_mem
              (AddSubgroup.subset_closure
                (ctx.Y_family.1 ctx.eta₁_mem)) Z.index
        have hgammaOff : gamma ∈ ClassFunction.supportedOn
            (nonidentitySet L) := by
          rw [ClassFunction.mem_supportedOn_iff]
          intro g hg
          have hg1 : g = 1 := by
            simpa [nonidentitySet] using not_not.mp hg
          subst g
          simp only [gamma, ClassFunction.sub_apply,
            ClassFunction.smul_apply, smul_eq_mul]
          rw [ctx.centralInduce_one i,
            ctx.Y_degree eta₁ ctx.eta₁_mem]
          push_cast
          ring
        have hagree : tau₁ d = tau d :=
          ctx.Y_coherent.agrees d hdSpanY hdOff
        have hiso := ctx.source_subcoherent.tau_isometry
          gamma hgammaSpanS hgammaOff d hdSpanS hdOff
        have hsourcePair : characterPairing gamma d = (Z.index : ℂ) := by
          dsimp only [gamma, d]
          rw [caseB_pairing_sub_left, caseB_pairing_sub_right,
            caseB_pairing_sub_right,
            characterPairing_smul_left,
            characterPairing_smul_left,
            caseB_Xspan_pairing_Y_zero K Z X Y tau tau₁ eta₁ ctx
              hgammaSpanX heta,
            caseB_Xspan_pairing_Y_zero K Z X Y tau tau₁ eta₁ ctx
              hgammaSpanX ctx.eta₁_mem,
            ctx.Y_orthonormal eta₁ ctx.eta₁_mem eta heta,
            ctx.Y_orthonormal eta₁ ctx.eta₁_mem eta₁ ctx.eta₁_mem,
            if_neg (fun h ↦ heq h.symm), if_pos rfl]
          ring
        have hGammaDiff : characterPairing (tau gamma)
            (tau₁ eta - tau₁ eta₁) = (Z.index : ℂ) := by
          rw [← map_sub, show eta - eta₁ = d by rfl, hagree, hiso,
            hsourcePair]
        have hY₁Diff : characterPairing Y₁
            (tau₁ eta - tau₁ eta₁) = -1 := by
          let c : ClassFunction L ℂ → ℂ := fun zeta ↦
            (x : ℂ) - if zeta = eta₁ then 1 else 0
          have hsum (w : ClassFunction L ℂ) (hw : w ∈ Y) :
              characterPairing
                  (∑ zeta ∈ Y, c zeta • tau₁ zeta) (tau₁ w) =
                c w := by
            rw [caseB_pairing_finset_sum_left]
            rw [Finset.sum_eq_single w]
            · rw [characterPairing_smul_left,
                hYtauOrth w hw w hw, if_pos rfl, mul_one]
            · intro zeta hzeta hne
              rw [characterPairing_smul_left,
                hYtauOrth zeta hzeta w hw, if_neg hne, mul_zero]
            · exact fun h ↦ (h hw).elim
          rw [hY₁Candidate]
          change characterPairing
              (-∑ zeta ∈ Y, c zeta • tau₁ zeta)
              (tau₁ eta - tau₁ eta₁) = -1
          rw [caseB_pairing_neg_left, caseB_pairing_sub_right,
            hsum eta heta, hsum eta₁ ctx.eta₁_mem]
          simp only [c, if_neg heq, if_pos]
          ring
        have hX₂Diff : characterPairing X₂
            (tau₁ eta - tau₁ eta₁) = 0 := by
          dsimp only [X₂]
          rw [characterPairing_add_left, characterPairing_smul_left,
            hGammaDiff, hY₁Diff]
          ring
        rw [← sub_add_cancel (tau₁ eta) (tau₁ eta₁),
          characterPairing_add_right, hX₂Diff, hX₂Eta₁,
          zero_add]
    have hX₂Y₁ : characterPairing X₂ Y₁ = 0 := by
      rw [hY₁Candidate]
      simp only [sibleyCaseBPivotCandidate]
      rw [caseB_pairing_neg_right, caseB_pairing_finset_sum_right]
      apply neg_eq_zero.mpr
      apply Finset.sum_eq_zero
      intro eta heta
      rw [characterPairing_smul_right, hX₂Each eta heta, mul_zero]
    refine ⟨X₂, hX₂Y₁, ?_⟩
    dsimp only [X₂, gamma]
    abel
  have hY₁Norm : characterPairing Y₁ Y₁ = 1 := by
    obtain ⟨i, hi⟩ :=
      caseB_exists_irreducible_ne_trivial_of_one_lt_card
        (Z.one_lt_card_iff_ne_bot.mpr ctx.Z_nontrivial)
    obtain ⟨X₂, hX₂Y₁, hdecomp⟩ := hcommonBridge i hi
    let gamma : ClassFunction L ℂ :=
      ctx.centralInduce i - (Z.index : ℂ) • eta₁
    have hgammaVirtual : ClassFunction.IsVirtual gamma :=
      (ctx.centralInduce_virtual i).sub
        (hetaVirtual.natCast_smul Z.index)
    have hYscaledVirtual : ClassFunction.IsVirtual
        ((Z.index : ℂ) • Y₁) :=
      hY₁Virtual.natCast_smul Z.index
    have hX₂Virtual : ClassFunction.IsVirtual X₂ := by
      rw [show X₂ = tau gamma + (Z.index : ℂ) • Y₁ by
        rw [hdecomp]; abel]
      exact (ctx.source_subcoherent.tau_virtual gamma
        (by
          apply (AddSubgroup.closure ctx.sourceFamily).sub_mem
          · exact AddSubgroup.closure_mono ctx.X_family.1
              (ctx.centralInduce_mem_X_span i hi)
          · rw [Nat.cast_smul_eq_nsmul]
            exact (AddSubgroup.closure ctx.sourceFamily).nsmul_mem
              (AddSubgroup.subset_closure
                (ctx.Y_family.1 ctx.eta₁_mem)) Z.index)
        (by
          rw [ClassFunction.mem_supportedOn_iff]
          intro g hg
          have hg1 : g = 1 := by
            simpa [nonidentitySet] using not_not.mp hg
          subst g
          simp only [gamma, ClassFunction.sub_apply,
            ClassFunction.smul_apply, smul_eq_mul]
          rw [ctx.centralInduce_one i,
            ctx.Y_degree eta₁ ctx.eta₁_mem]
          push_cast
          ring)).add hYscaledVirtual
    obtain ⟨nX, hnX⟩ := hX₂Virtual.exists_nat_norm
    obtain ⟨nY, hnY⟩ := hY₁Virtual.exists_nat_norm
    have hgammaNorm : characterPairing (tau gamma) (tau gamma) =
        ((K.index * Z.index + Z.index ^ 2 : ℕ) : ℂ) := by
      have hspan : gamma ∈ AddSubgroup.closure ctx.sourceFamily := by
        apply (AddSubgroup.closure ctx.sourceFamily).sub_mem
        · exact AddSubgroup.closure_mono ctx.X_family.1
            (ctx.centralInduce_mem_X_span i hi)
        · rw [Nat.cast_smul_eq_nsmul]
          exact (AddSubgroup.closure ctx.sourceFamily).nsmul_mem
            (AddSubgroup.subset_closure
              (ctx.Y_family.1 ctx.eta₁_mem)) Z.index
      have hoff : gamma ∈ ClassFunction.supportedOn
          (nonidentitySet L) := by
        rw [ClassFunction.mem_supportedOn_iff]
        intro g hg
        have hg1 : g = 1 := by
          simpa [nonidentitySet] using not_not.mp hg
        subst g
        simp only [gamma, ClassFunction.sub_apply,
          ClassFunction.smul_apply, smul_eq_mul]
        rw [ctx.centralInduce_one i,
          ctx.Y_degree eta₁ ctx.eta₁_mem]
        push_cast
        ring
      rw [ctx.source_subcoherent.tau_isometry gamma hspan hoff
        gamma hspan hoff]
      dsimp only [gamma]
      rw [caseB_pairing_sub_left, caseB_pairing_sub_right,
        caseB_pairing_sub_right, characterPairing_smul_left,
        characterPairing_smul_left,
        characterPairing_smul_right, characterPairing_smul_right,
        ctx.centralInduce_self i,
        caseB_Xspan_pairing_Y_zero K Z X Y tau tau₁ eta₁ ctx
          (ctx.centralInduce_mem_X_span i hi) ctx.eta₁_mem,
        characterPairing_comm eta₁ (ctx.centralInduce i),
        caseB_Xspan_pairing_Y_zero K Z X Y tau tau₁ eta₁ ctx
          (ctx.centralInduce_mem_X_span i hi) ctx.eta₁_mem,
        ctx.Y_orthonormal eta₁ ctx.eta₁_mem eta₁ ctx.eta₁_mem,
        if_pos rfl]
      push_cast
      ring
    have hnormEquation :
        K.index * Z.index + Z.index ^ 2 =
          nX + Z.index ^ 2 * nY := by
      have htarget := hgammaNorm
      rw [hdecomp, pairing_self_sub_of_orthogonal_caseB
        X₂ ((Z.index : ℂ) • Y₁)
        (by rw [characterPairing_smul_right, hX₂Y₁, mul_zero]),
        hnX, characterPairing_smul_left,
        characterPairing_smul_right, hnY] at htarget
      have htargetNat :
          nX + Z.index * (Z.index * nY) =
            K.index * Z.index + Z.index ^ 2 := by
        exact_mod_cast htarget
      calc
        K.index * Z.index + Z.index ^ 2 =
            nX + Z.index * (Z.index * nY) := htargetNat.symm
        _ = nX + Z.index ^ 2 * nY := by ring
    have hnYlt : nY < 2 := by
      by_contra hnot
      have hnYtwo : 2 ≤ nY := by omega
      have hleft : K.index * Z.index < Z.index ^ 2 := by
        have hZpos : 0 < Z.index :=
          Nat.pos_of_ne_zero Z.index_ne_zero_of_finite
        nlinarith [ctx.kernel_index_lt_central_index]
      have hright : 2 * Z.index ^ 2 ≤
          nX + Z.index ^ 2 * nY := by
        nlinarith
      omega
    have hformulaInt :
        (x - 1) ^ 2 +
          ((Y.card - 1 : ℕ) : ℤ) * x ^ 2 = (nY : ℤ) := by
      apply Int.cast_injective (α := ℂ)
      rw [← hY₁NormFormula, hnY]
      norm_num
    have hformulaLt :
        (x - 1) ^ 2 +
          ((Y.card - 1 : ℕ) : ℤ) * x ^ 2 < 2 := by
      rw [hformulaInt]
      exact_mod_cast hnYlt
    obtain hx | ⟨hx, hcard⟩ :=
      caseB_coefficient_dichotomy x Y.card ctx.two_le_card_Y hformulaLt
    · rw [hY₁NormFormula, hx]
      norm_num
    · rw [hY₁NormFormula, hx, hcard]
      norm_num
  exact ⟨x, Y₁, hY₁Candidate, hY₁Virtual, hY₁Norm,
    ⟨ySource, hySourceSpan, rfl⟩, hcommonBridge⟩

/-- Source lines 1114--1263.  All Clifford constituents are split using the
public subcoherence projection.  Pairing their weighted sum with the common
pivot forces every nonnegative weighted defect to vanish, in particular the
defect of the originally selected constituent. -/
private theorem caseB_force_clifford_decomposition
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) (Z : Subgroup K)
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ)
    (ctx : SibleyCaseBContext K Z X Y tau tau₁ eta₁)
    (Y₁ : ClassFunction G ℂ)
    (hY₁Virtual : ClassFunction.IsVirtual Y₁)
    (hY₁Norm : characterPairing Y₁ Y₁ = 1)
    (hY₁Span : ∃ v ∈ AddSubgroup.closure
      (↑Y : Set (ClassFunction L ℂ)), tau₁ v = Y₁)
    (hcommonBridge : ∀ i : IrreducibleCharacter Z ℂ,
      i ≠ IrreducibleCharacter.trivial →
      ∃ X₂ : ClassFunction G ℂ,
        characterPairing X₂ Y₁ = 0 ∧
        tau (ctx.centralInduce i - (Z.index : ℂ) • eta₁) =
          X₂ - (Z.index : ℂ) • Y₁)
    (xi : ClassFunction L ℂ) (hxi : xi ∈ X)
    (theta : IrreducibleCharacter K ℂ)
    (hxiTheta :
      xi = ClassFunction.induce K (theta : ClassFunction K ℂ))
    (a : ℕ) (phi : IrreducibleCharacter Z ℂ)
    (ha : 0 < a)
    (hthetaDegree : theta 1 = (a : ℂ))
    (hphiDegree : phi 1 = 1)
    (hthetaRestrict :
      ClassFunction.restrict Z (theta : ClassFunction K ℂ) =
        (a : ℂ) • (phi : ClassFunction Z ℂ)) :
    ∃ X₁ : ClassFunction G ℂ,
      characterPairing X₁ Y₁ = 0 ∧
      tau (xi - (a : ℂ) • eta₁) =
        X₁ - (a : ℂ) • Y₁ := by
  classical
  have hthetaX :
      ClassFunction.induce K (theta : ClassFunction K ℂ) ∈ X := by
    simpa only [← hxiTheta] using hxi
  have hthetaNotKernel :
      ¬Z ≤ ClassFunction.translationKernel
        (theta : ClassFunction K ℂ) :=
    (ctx.X_characterization theta).1 hthetaX
  have hphiNe : phi ≠ IrreducibleCharacter.trivial :=
    caseB_central_character_ne_trivial Z ctx.Z_central theta
      a ha hthetaDegree phi hthetaRestrict hthetaNotKernel
  let F : ClassFunction K ℂ :=
    ClassFunction.induce Z (phi : ClassFunction Z ℂ)
  let rp : Finset (IrreducibleCharacter K ℂ) :=
    caseBConstituents F
  let m : IrreducibleCharacter K ℂ → ℕ := fun i ↦
    IrreducibleCharacter.centralRestrictionMultiplicity Z i phi
  let chi : IrreducibleCharacter K ℂ → ClassFunction L ℂ := fun i ↦
    ClassFunction.induce K (i : ClassFunction K ℂ)
  have hclifford (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      i 1 = (m i : ℂ) ∧
      phi 1 = 1 ∧
      ClassFunction.restrict Z (i : ClassFunction K ℂ) =
        (m i : ℂ) • (phi : ClassFunction Z ℂ) ∧
      characterPairing F (i : ClassFunction K ℂ) = (m i : ℂ) := by
    apply IrreducibleCharacter.central_restriction_eq_multiplicity_smul_of_induce_pairing_ne_zero
      Z ctx.Z_central i phi
    exact (caseB_mem_constituents_iff F i).mp hi
  have hmPos (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      0 < m i := by
    apply Nat.pos_of_ne_zero
    intro hm0
    apply irreducibleCharacter_apply_one_ne_zero_caseB i
    rw [(hclifford i hi).1, hm0]
    norm_num
  have hthetaPairNe :
      characterPairing F (theta : ClassFunction K ℂ) ≠ 0 := by
    simp only [F]
    rw [ClassFunction.frobeniusReciprocity, hthetaRestrict,
      characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_self, mul_one]
    exact Nat.cast_ne_zero.mpr ha.ne'
  have hthetaRp : theta ∈ rp := by
    exact (caseB_mem_constituents_iff F theta).2 hthetaPairNe
  have hmTheta : m theta = a := by
    apply Nat.cast_injective (R := ℂ)
    rw [← (hclifford theta hthetaRp).1, hthetaDegree]
  have hFExpansion :
      (∑ i ∈ rp, (m i : ℂ) • (i : ClassFunction K ℂ)) = F := by
    calc
      (∑ i ∈ rp, (m i : ℂ) • (i : ClassFunction K ℂ)) =
          ∑ i ∈ rp,
            characterPairing (i : ClassFunction K ℂ) F •
              (i : ClassFunction K ℂ) := by
        apply Finset.sum_congr rfl
        intro i hi
        apply congrArg (fun c : ℂ ↦ c • (i : ClassFunction K ℂ))
        rw [characterPairing_comm]
        exact (hclifford i hi).2.2.2.symm
      _ = F := by
        simpa only [rp] using caseB_sum_constituents_eq F
  have hmSquaresCast :
      (((∑ i ∈ rp, (m i) ^ 2 : ℕ) : ℕ) : ℂ) = (Z.index : ℂ) := by
    calc
      (((∑ i ∈ rp, (m i) ^ 2 : ℕ) : ℕ) : ℂ) =
          (∑ i ∈ rp,
            (m i : ℂ) • (i : ClassFunction K ℂ)) 1 := by
        rw [ClassFunction.finset_sum_apply]
        push_cast
        apply Finset.sum_congr rfl
        intro i hi
        change (m i : ℂ) ^ 2 = (m i : ℂ) * i 1
        rw [(hclifford i hi).1]
        ring
      _ = F 1 := congrArg (fun f : ClassFunction K ℂ ↦ f 1) hFExpansion
      _ = (Z.index : ℂ) := by
        simp only [F]
        rw [ClassFunction.induce_one, hphiDegree, mul_one]
  have hmSquares : ∑ i ∈ rp, (m i) ^ 2 = Z.index := by
    exact Nat.cast_injective hmSquaresCast
  have hcentralExpansion :
      ctx.centralInduce phi =
        ∑ i ∈ rp, (m i : ℂ) • chi i := by
    rw [ctx.centralInduce_eq_induce phi]
    change ClassFunction.induce K F = _
    rw [← hFExpansion]
    simp only [chi, map_sum, map_smul]
  have hsourceExpansion :
      ctx.centralInduce phi - (Z.index : ℂ) • eta₁ =
        ∑ i ∈ rp,
          (m i : ℂ) • (chi i - (m i : ℂ) • eta₁) := by
    rw [hcentralExpansion, ← hmSquares]
    push_cast
    simp only [smul_sub, smul_smul, Finset.sum_sub_distrib,
      Finset.sum_smul, pow_two]
  let data (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      CaseBCliffordTermData tau (chi i) eta₁ (m i) Y₁ :=
    caseB_clifford_term K Z X Y tau tau₁ eta₁ ctx
      phi hphiNe i hi Y₁ hY₁Virtual hY₁Norm hY₁Span
  let b : IrreducibleCharacter K ℂ → ℤ := fun i ↦
    if hi : i ∈ rp then (data i hi).coefficient else 0
  let P : IrreducibleCharacter K ℂ → ClassFunction G ℂ := fun i ↦
    if hi : i ∈ rp then (data i hi).mainPart else 0
  let E : IrreducibleCharacter K ℂ → ClassFunction G ℂ := fun i ↦
    if hi : i ∈ rp then (data i hi).residual else 0
  let n : IrreducibleCharacter K ℂ → ℕ := fun i ↦
    if hi : i ∈ rp then (data i hi).residualNorm else 0
  have hbLe (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      b i ≤ (m i : ℤ) := by
    simp only [b, dif_pos hi]
    exact (data i hi).coefficient_le
  have hPorth (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      characterPairing (P i) Y₁ = 0 := by
    simp only [P, dif_pos hi]
    exact (data i hi).mainPart_orthogonal
  have hEorth (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      characterPairing (E i) Y₁ = 0 := by
    simp only [E, dif_pos hi]
    exact (data i hi).residual_orthogonal
  have hEvirtual (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      ClassFunction.IsVirtual (E i) := by
    simp only [E, dif_pos hi]
    exact (data i hi).residual_virtual
  have hEnorm (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      characterPairing (E i) (E i) = (n i : ℂ) := by
    simp only [E, n, dif_pos hi]
    exact (data i hi).residual_norm
  have hnormBound (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      b i ^ 2 + (n i : ℤ) ≤ (m i : ℤ) ^ 2 := by
    simp only [b, n, dif_pos hi]
    exact (data i hi).norm_bound
  have htermDecomp (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      tau (chi i - (m i : ℂ) • eta₁) =
        P i - (b i : ℂ) • Y₁ + E i := by
    simpa only [P, b, E, dif_pos hi] using (data i hi).decomposition
  have htermPair (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      characterPairing
          (tau (chi i - (m i : ℂ) • eta₁)) Y₁ = -(b i : ℂ) := by
    rw [htermDecomp i hi, characterPairing_add_left,
      caseB_pairing_sub_left, characterPairing_smul_left,
      hPorth i hi, hEorth i hi, hY₁Norm]
    ring
  obtain ⟨X₂, hX₂orth, hbridge⟩ := hcommonBridge phi hphiNe
  have hglobalPair :
      characterPairing
          (tau (∑ i ∈ rp,
            (m i : ℂ) • (chi i - (m i : ℂ) • eta₁))) Y₁ =
        -(Z.index : ℂ) := by
    rw [← hsourceExpansion, hbridge, caseB_pairing_sub_left,
      characterPairing_smul_left, hX₂orth, hY₁Norm]
    ring
  let B : ℤ := ∑ i ∈ rp, (m i : ℤ) * b i
  have hglobalPair' :
      characterPairing
          (tau (∑ i ∈ rp,
            (m i : ℂ) • (chi i - (m i : ℂ) • eta₁))) Y₁ =
        -(B : ℂ) := by
    rw [map_sum, caseB_pairing_finset_sum_left]
    simp only [map_smul, characterPairing_smul_left]
    rw [show (∑ i ∈ rp,
        (m i : ℂ) * characterPairing
          (tau (chi i - (m i : ℂ) • eta₁)) Y₁) =
        ∑ i ∈ rp, -((m i : ℂ) * (b i : ℂ)) by
      apply Finset.sum_congr rfl
      intro i hi
      rw [htermPair i hi]
      ring]
    rw [Finset.sum_neg_distrib]
    simp only [B]
    push_cast
    rfl
  have hB : B = Z.index := by
    apply Int.cast_injective (α := ℂ)
    have h := hglobalPair'.symm.trans hglobalPair
    exact neg_inj.mp h
  have hdefectZero :
      ∑ i ∈ rp,
        (m i : ℤ) * ((m i : ℤ) - b i) = 0 := by
    calc
      ∑ i ∈ rp, (m i : ℤ) * ((m i : ℤ) - b i) =
          (∑ i ∈ rp, ((m i : ℤ) ^ 2)) - B := by
        simp only [B, mul_sub, pow_two, Finset.sum_sub_distrib]
      _ = (Z.index : ℤ) - (Z.index : ℤ) := by
        rw [hB]
        exact congrArg (fun z : ℤ ↦ z - (Z.index : ℤ)) (by
          exact_mod_cast hmSquares)
      _ = 0 := sub_self _
  have hdefectNonneg (i : IrreducibleCharacter K ℂ) (hi : i ∈ rp) :
      0 ≤ (m i : ℤ) * ((m i : ℤ) - b i) := by
    exact mul_nonneg (by exact_mod_cast (m i).zero_le)
      (sub_nonneg.mpr (hbLe i hi))
  have hthetaDefect :
      (m theta : ℤ) * ((m theta : ℤ) - b theta) = 0 := by
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hdefectNonneg).mp
      hdefectZero
    exact hz theta hthetaRp
  have hbTheta : b theta = (a : ℤ) := by
    have hmTheta0 : (m theta : ℤ) ≠ 0 := by
      rw [hmTheta]
      exact_mod_cast ha.ne'
    have hdiff := (mul_eq_zero.mp hthetaDefect).resolve_left hmTheta0
    rw [sub_eq_zero] at hdiff
    exact hdiff.symm.trans (congrArg Int.ofNat hmTheta)
  have hnTheta : n theta = 0 := by
    have hbound := hnormBound theta hthetaRp
    rw [hbTheta, hmTheta] at hbound
    omega
  have hEThetaZero : E theta = 0 := by
    apply virtual_eq_zero_of_pairing_self_eq_zero_caseB
      (hEvirtual theta hthetaRp)
    rw [hEnorm theta hthetaRp, hnTheta]
    norm_num
  refine ⟨P theta, hPorth theta hthetaRp, ?_⟩
  rw [hxiTheta]
  have hselected := htermDecomp theta hthetaRp
  rw [hmTheta, hbTheta, hEThetaZero, add_zero] at hselected
  exact hselected

/-! ## The public Case-B interface -/

/-- Peterfalvi (6.8), Case B, source lines 947--1278: construction of the
single signed `Y`-pivot and all balanced `X`-decompositions consumed by the
final call to `coherent_union_of_sibley_pivot`.
-/
theorem sibley_caseB_pivot
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K : Subgroup L) (Z : Subgroup K)
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (eta₁ : ClassFunction L ℂ)
    (ctx : SibleyCaseBContext K Z X Y tau tau₁ eta₁) :
    ∃ Y₁ : ClassFunction G ℂ,
      (Y₁ = tau₁ eta₁ ∨
        Y.card = 2 ∧ Y₁ = dual_iso tau₁ eta₁) ∧
      ∀ xi ∈ X, ∃ (a : ℕ) (X₁ : ClassFunction G ℂ),
        xi 1 = (a : ℂ) * eta₁ 1 ∧
        characterPairing X₁ Y₁ = 0 ∧
        tau (xi - (a : ℂ) • eta₁) =
          X₁ - (a : ℂ) • Y₁ := by
  classical
  obtain ⟨x, Y₁, hY₁Candidate, hY₁Virtual, hY₁Norm,
      hY₁Span, hcommonBridge⟩ :=
    caseB_common_pivot K Z X Y tau tau₁ eta₁ ctx
  have hYtauOrth : ∀ eta ∈ Y, ∀ zeta ∈ Y,
      characterPairing (tau₁ eta) (tau₁ zeta) =
        if eta = zeta then 1 else 0 := by
    intro eta heta zeta hzeta
    rw [ctx.Y_coherent.isometry eta
      (AddSubgroup.subset_closure heta)
      zeta (AddSubgroup.subset_closure hzeta)]
    exact ctx.Y_orthonormal eta heta zeta hzeta
  have hformulaCast :
      ((((x - 1) ^ 2 +
        ((Y.card - 1 : ℕ) : ℤ) * x ^ 2 : ℤ)) : ℂ) = 1 := by
    rw [← caseB_candidate_pairing_self Y tau₁ eta₁ x
      ctx.eta₁_mem hYtauOrth, ← hY₁Candidate, hY₁Norm]
  have hformulaEq :
      (x - 1) ^ 2 + ((Y.card - 1 : ℕ) : ℤ) * x ^ 2 = 1 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [Int.cast_one] using hformulaCast
  have hcoefficient := caseB_coefficient_dichotomy
    x Y.card ctx.two_le_card_Y (by rw [hformulaEq]; norm_num)
  have hY₁alt :
      Y₁ = tau₁ eta₁ ∨
        Y.card = 2 ∧ Y₁ = dual_iso tau₁ eta₁ := by
    rcases hcoefficient with hx | ⟨hx, hYcard⟩
    · left
      rw [hY₁Candidate]
      simp only [sibleyCaseBPivotCandidate]
      rw [hx, Finset.sum_eq_single eta₁]
      · simp only [if_pos rfl, if_true]
        rw [show (((0 : ℤ) : ℂ) - 1) = -1 by norm_num]
        ext g
        simp only [ClassFunction.neg_apply, ClassFunction.smul_apply,
          smul_eq_mul]
        ring
      · intro eta heta hne
        simp [hne]
      · exact fun hnot ↦ (hnot ctx.eta₁_mem).elim
    · right
      refine ⟨hYcard, ?_⟩
      let etaInv : ClassFunction L ℂ :=
        ClassFunction.inverseLinear eta₁
      have hetaInvY : etaInv ∈ Y :=
        ctx.Y_closed eta₁ ctx.eta₁_mem
      have hetaInvNe : etaInv ≠ eta₁ :=
        ctx.source_subcoherent.inverse_ne eta₁
          (ctx.Y_family.1 ctx.eta₁_mem)
      have hpairSub :
          ({eta₁, etaInv} : Finset (ClassFunction L ℂ)) ⊆ Y := by
        intro eta heta
        simp only [Finset.mem_insert, Finset.mem_singleton] at heta
        rcases heta with rfl | rfl
        · exact ctx.eta₁_mem
        · exact hetaInvY
      have hpairCard :
          ({eta₁, etaInv} : Finset (ClassFunction L ℂ)).card = 2 := by
        simp [hetaInvNe.symm]
      have hpairEq :
          ({eta₁, etaInv} : Finset (ClassFunction L ℂ)) = Y :=
        Finset.eq_of_subset_of_card_le hpairSub (by
          rw [hYcard, hpairCard])
      rw [hY₁Candidate]
      simp only [sibleyCaseBPivotCandidate]
      rw [← hpairEq, hx, dual_iso_apply]
      simp [etaInv, hetaInvNe, hetaInvNe.symm]
  refine ⟨Y₁, hY₁alt, ?_⟩
  intro xi hxi
  obtain ⟨theta, hxiTheta⟩ := ctx.X_induced xi hxi
  obtain ⟨a, phi, hthetaDegree, hphiDegree, hthetaRestrict⟩ :=
    IrreducibleCharacter.exists_central_restriction_eq_degree_smul
      Z ctx.Z_central theta
  have haNe : a ≠ 0 := by
    intro ha
    apply irreducibleCharacter_apply_one_ne_zero_caseB theta
    rw [hthetaDegree, ha]
    norm_num
  have haPos : 0 < a := Nat.pos_of_ne_zero haNe
  have hdegree : xi 1 = (a : ℂ) * eta₁ 1 := by
    rw [hxiTheta, ClassFunction.induce_one, hthetaDegree,
      ctx.Y_degree eta₁ ctx.eta₁_mem]
    ring
  obtain ⟨X₁, hX₁Orth, hX₁Decomp⟩ :=
    caseB_force_clifford_decomposition K Z X Y tau tau₁ eta₁ ctx
      Y₁ hY₁Virtual hY₁Norm hY₁Span hcommonBridge
      xi hxi theta hxiTheta a phi haPos
      hthetaDegree hphiDegree hthetaRestrict
  exact ⟨a, X₁, hdegree, hX₁Orth, hX₁Decomp⟩

end

end Submission.OddOrder.PF
