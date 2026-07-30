import Submission.OddOrder.PF.Section01.ClassFunctionSupport
import Submission.OddOrder.PF.Section01.IrreducibleCharacterTranslationKernel
import Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent
import Submission.OddOrder.PF.Section01.NormalSubgroupInductionConsequences
import Submission.OddOrder.PF.Section01.VirtualCharacterInduction
import Submission.OddOrder.PF.Section03.DirectProductCharacters

/-!
# Induced irreducible-character families

This file ports the generic opening of Peterfalvi Section 5, corresponding to
`PFsection5.v`, lines 57--261.  MathComp's finite sets and duplicate-free
sequences are represented by `Finset`s.  The source lattice notation
`'Z[S]` is made explicit as the free integral lattice on the members of the
finite family `S`, together with its realization map into class functions.

The principal source declarations covered here are `Iirr_ker`,
`Iirr_kerD`, `seqInd`, `seqIndP`, the support and orthogonality lemmas for
`seqInd`, `zcharD1_seqInd`, `zcharD1_seqInd_Dade`,
`dvd_index_seqInd1`, `sub_seqInd_zchar`, and the four lemmas in the source
`Beta` subsection.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical
open CategoryTheory

universe u v

local instance inducedIrreduciblesInvertibleCard
    {G : Type u} {k : Type v} [Group G] [Fintype G] [Field k] [CharZero k] :
    Invertible (Nat.card G : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## Irreducibles with a prescribed subgroup in their kernel -/

/-- Source `Iirr_ker`: irreducible characters whose translation kernel
contains `A`. -/
def Iirr_ker {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (A : Subgroup G) : Finset (IrreducibleCharacter G k) :=
  Finset.univ.filter fun chi =>
    A ≤ ClassFunction.translationKernel (chi : ClassFunction G k)

@[simp]
theorem mem_Iirr_ker {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    {A : Subgroup G} {chi : IrreducibleCharacter G k} :
    chi ∈ Iirr_ker (k := k) A ↔
      A ≤ ClassFunction.translationKernel (chi : ClassFunction G k) := by
  simp [Iirr_ker]

/-- Source `Iirr_kerS`: enlarging the prescribed kernel subgroup shrinks
the corresponding family of irreducibles. -/
theorem Iirr_kerS {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    {A B : Subgroup G} (hBA : B ≤ A) :
    Iirr_ker (k := k) A ⊆ Iirr_ker (k := k) B := by
  intro chi hchi
  rw [mem_Iirr_ker] at hchi ⊢
  exact hBA.trans hchi

/-- Source `Iirr_kerD`: characters whose kernel contains `A` but does not
contain `B`. -/
def Iirr_kerD {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (B A : Subgroup G) : Finset (IrreducibleCharacter G k) :=
  Iirr_ker (k := k) A \ Iirr_ker (k := k) B

@[simp]
theorem mem_Iirr_kerD {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    {A B : Subgroup G} {chi : IrreducibleCharacter G k} :
    chi ∈ Iirr_kerD (k := k) B A ↔
      A ≤ ClassFunction.translationKernel (chi : ClassFunction G k) ∧
      ¬B ≤ ClassFunction.translationKernel (chi : ClassFunction G k) := by
  simp [Iirr_kerD]

/-- A coefficient-field automorphism does not change the translation
kernel of an irreducible character.  This is the kernel calculation behind
source `Iirr_ker_aut`. -/
theorem translationKernel_mapRingEquiv {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (sigma : k ≃+* k) (chi : IrreducibleCharacter G k) :
    ClassFunction.translationKernel
        (IrreducibleCharacter.mapRingEquiv sigma chi : ClassFunction G k) =
      ClassFunction.translationKernel (chi : ClassFunction G k) := by
  ext a
  simp only [ClassFunction.mem_translationKernel_iff]
  constructor
  · intro h x
    apply sigma.injective
    simpa only [IrreducibleCharacter.mapRingEquiv_apply] using h x
  · intro h x
    simpa only [IrreducibleCharacter.mapRingEquiv_apply] using
      congrArg sigma (h x)

/-- Source `Iirr_ker_aut`: coefficient automorphisms preserve membership in
`Iirr_ker`. -/
theorem Iirr_ker_aut {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (sigma : k ≃+* k) (A : Subgroup G)
    (chi : IrreducibleCharacter G k) :
    IrreducibleCharacter.mapRingEquiv sigma chi ∈ Iirr_ker (k := k) A ↔
      chi ∈ Iirr_ker (k := k) A := by
  simp only [mem_Iirr_ker, translationKernel_mapRingEquiv]

/-- Source `Iirr_ker_conjg`: ambient conjugation by an element normalizing
`A` preserves the condition that `A` lies in the character kernel. -/
theorem Iirr_ker_conjg {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K A : Subgroup G) [K.Normal] (hAK : A ≤ K)
    (x : G) (hx : x ∈ Subgroup.normalizer A)
    (chi : IrreducibleCharacter K k) :
    chi.normalConjugate K x ∈ Iirr_ker (k := k) (A.subgroupOf K) ↔
      chi ∈ Iirr_ker (k := k) (A.subgroupOf K) := by
  rw [mem_Iirr_ker, mem_Iirr_ker]
  constructor
  · intro h a ha y
    let ax : K :=
      ⟨x * (a : G) * x⁻¹,
        (inferInstance : K.Normal).conj_mem (a : G) (hAK ha) x⟩
    let yx : K :=
      ⟨x * (y : G) * x⁻¹,
        (inferInstance : K.Normal).conj_mem (y : G) y.property x⟩
    have haxA : ax ∈ A.subgroupOf K := by
      exact (Subgroup.mem_normalizer_iff.mp hx (a : G)).mp ha
    have heq := h haxA yx
    change chi ((MulAut.conjNormal x).symm (ax * yx)) =
      chi ((MulAut.conjNormal x).symm yx) at heq
    rw [map_mul] at heq
    have hax : (MulAut.conjNormal x).symm ax = a := by
      apply Subtype.ext
      simp [ax, MulAut.conjNormal_symm_apply, mul_assoc]
    have hyx : (MulAut.conjNormal x).symm yx = y := by
      apply Subtype.ext
      simp [yx, MulAut.conjNormal_symm_apply, mul_assoc]
    simpa only [hax, hyx] using heq
  · intro h a ha y
    let ax : K :=
      ⟨x⁻¹ * (a : G) * x,
        by simpa using
          (inferInstance : K.Normal).conj_mem (a : G) (hAK ha) x⁻¹⟩
    let yx : K :=
      ⟨x⁻¹ * (y : G) * x,
        by simpa using
          (inferInstance : K.Normal).conj_mem (y : G) y.property x⁻¹⟩
    have hx' : x ∈ Subgroup.normalizer (A : Set G) := hx
    have hxinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hx'
    have haxA : ax ∈ A.subgroupOf K := by
      have ha' := (Subgroup.mem_normalizer_iff.mp hxinv (a : G)).mp ha
      change (ax : G) ∈ A
      change x⁻¹ * (a : G) * x ∈ A
      simpa using ha'
    have heq := h haxA yx
    change chi ((MulAut.conjNormal x).symm (a * y)) =
      chi ((MulAut.conjNormal x).symm y)
    rw [map_mul]
    have hax : (MulAut.conjNormal x).symm a = ax := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_symm_apply]
      rfl
    have hyx : (MulAut.conjNormal x).symm y = yx := by
      apply Subtype.ext
      simp only [MulAut.conjNormal_symm_apply]
      rfl
    simpa only [hax, hyx] using heq

/-- Source `Iirr_kerDS`: simultaneous monotonicity of the two kernel bounds. -/
theorem Iirr_kerDS {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    {A₁ A₂ B₁ B₂ : Subgroup G} (hA : A₂ ≤ A₁) (hB : B₁ ≤ B₂) :
    Iirr_kerD (k := k) B₁ A₁ ⊆ Iirr_kerD (k := k) B₂ A₂ := by
  intro chi hchi
  rw [mem_Iirr_kerD] at hchi ⊢
  exact ⟨hA.trans hchi.1, fun hB₂ => hchi.2 (hB.trans hB₂)⟩

/-- Source `Iirr_kerDY`: once `A` is already in the kernel, excluding
`A ⊔ B` is the same as excluding `B`. -/
theorem Iirr_kerDY {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (B A : Subgroup G) :
    Iirr_kerD (k := k) (A ⊔ B) A = Iirr_kerD (k := k) B A := by
  ext chi
  simp only [mem_Iirr_kerD, sup_le_iff]
  aesop

/-! ## Duplicate-free families of induced irreducible characters -/

/-- Source `seqInd`: the duplicate-free finite family of class functions
induced from the irreducibles in `calX`. -/
def seqInd {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (calX : Finset (IrreducibleCharacter K k)) :
    Finset (ClassFunction G k) :=
  Finset.image
    (fun chi : IrreducibleCharacter K k =>
      ClassFunction.induce K (chi : ClassFunction K k))
    calX

/-- Source `seqInd_uniq`: the `Finset` representation is duplicate-free by
construction. -/
theorem seqInd_uniq {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (calX : Finset (IrreducibleCharacter K k)) :
    (seqInd K calX).val.Nodup :=
  (seqInd K calX).nodup

/-- Source `seqIndP`: membership in `seqInd` is witnessed by an inducing
irreducible character. -/
theorem seqIndP {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    {K : Subgroup G} {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} :
    phi ∈ seqInd K calX ↔
      ∃ chi ∈ calX,
        phi = ClassFunction.induce K (chi : ClassFunction K k) := by
  constructor
  · intro hphi
    change phi ∈ Finset.image
      (fun chi : IrreducibleCharacter K k =>
        ClassFunction.induce K (chi : ClassFunction K k)) calX at hphi
    obtain ⟨chi, hchi, heq⟩ := Finset.mem_image.mp hphi
    exact ⟨chi, hchi, heq.symm⟩
  · rintro ⟨chi, hchi, rfl⟩
    change ClassFunction.induce K (chi : ClassFunction K k) ∈ Finset.image
      (fun eta : IrreducibleCharacter K k =>
        ClassFunction.induce K (eta : ClassFunction K k)) calX
    exact Finset.mem_image.mpr ⟨chi, hchi, rfl⟩

/-- Source `seqInd_on`: induction from a normal subgroup vanishes outside
that subgroup. -/
theorem seqInd_on {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    phi ∈ ClassFunction.supportedOn (K : Set G) := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  rw [ClassFunction.mem_supportedOn_iff]
  intro g hg
  rw [ClassFunction.induce_apply_formula]
  apply mul_eq_zero_of_right
  apply Finset.sum_eq_zero
  intro x _
  rw [dif_neg]
  intro hx
  apply hg
  have hx' := (inferInstance : K.Normal).conj_mem
    (x⁻¹ * g * x) hx x
  simpa [mul_assoc] using hx'

/-! The project-level bundled induction wrapper currently identifies the
group and coefficient-field universes.  The following elementary finite-sum
construction gives the split-universe realization needed in this file. -/

private def fdRepZero {G : Type u} {k : Type v} [Group G] [Field k] :
    FDRep k G :=
  FDRep.of (Representation.trivial k G (Fin 0 → k))

@[simp]
private theorem fdRepZero_character {G : Type u} {k : Type v}
    [Group G] [Field k] (g : G) :
    (fdRepZero : FDRep k G).character g = 0 := by
  change LinearMap.trace k (Fin 0 → k) LinearMap.id = 0
  simp

private def fdRepSum {G : Type u} {k : Type v} [Group G] [Field k]
    (V W : FDRep k G) : FDRep k G :=
  FDRep.of (Representation.prod V.ρ W.ρ)

@[simp]
private theorem fdRepSum_character {G : Type u} {k : Type v}
    [Group G] [Field k] (V W : FDRep k G) (g : G) :
    (fdRepSum V W).character g = V.character g + W.character g := by
  change LinearMap.trace k (V × W) ((V.ρ g).prodMap (W.ρ g)) = _
  exact LinearMap.trace_prodMap' (V.ρ g) (W.ρ g)

private def fdRepCopies {G : Type u} {k : Type v} [Group G] [Field k]
    (V : FDRep k G) : ℕ → FDRep k G
  | 0 => fdRepZero
  | n + 1 => fdRepSum V (fdRepCopies V n)

@[simp]
private theorem fdRepCopies_character {G : Type u} {k : Type v}
    [Group G] [Field k] (V : FDRep k G) (n : ℕ) (g : G) :
    (fdRepCopies V n).character g = (n : k) * V.character g := by
  induction n with
  | zero => simp [fdRepCopies]
  | succ n ih =>
      rw [fdRepCopies, fdRepSum_character, ih, Nat.cast_succ]
      ring

private theorem exists_fdRep_irreducible_sum
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (S : Finset (IrreducibleCharacter G k))
    (m : IrreducibleCharacter G k → ℕ) :
    ∃ V : FDRep k G,
      ClassFunction.ofRepresentation V.ρ =
        ∑ psi ∈ S, (m psi : k) • (psi : ClassFunction G k) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
      refine ⟨fdRepZero, ?_⟩
      ext g
      exact fdRepZero_character g
  | @insert psi S hpsi ih =>
      obtain ⟨V, hV⟩ := ih
      let W := fdRepCopies psi.representation (m psi)
      refine ⟨fdRepSum W V, ?_⟩
      rw [Finset.sum_insert hpsi, ← hV]
      ext g
      change (fdRepSum W V).character g =
        (m psi : k) * psi g + V.character g
      rw [fdRepSum_character]
      dsimp only [W]
      rw [fdRepCopies_character,
        IrreducibleCharacter.representation_character]

private theorem characterPairing_ofRepresentation_eq_finrank_hom_general
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [CharZero k] (V W : FDRep k G) :
    characterPairing (ClassFunction.ofRepresentation V.ρ)
        (ClassFunction.ofRepresentation W.ρ) =
      (Module.finrank k (W ⟶ V) : k) := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Fintype.card G : k) := by
    rw [Fintype.card_eq_nat_card]
    infer_instance
  have hhom := FDRep.scalar_product_char_eq_finrank_equivariant W V
  have hcharV (g : G) :
      V.character g = Representation.character V.ρ g := rfl
  have hcharW (g : G) :
      W.character g = Representation.character W.ρ g := rfl
  simpa only [characterPairing, ClassFunction.ofRepresentation_apply,
    invOf_eq_inv, smul_eq_mul, Fintype.card_eq_nat_card,
    hcharV, hcharW] using hhom

private def inducedMultiplicity
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (chi : IrreducibleCharacter K k)
    (psi : IrreducibleCharacter G k) : ℕ :=
  Module.finrank k
    (FDRep.of (psi.representation.ρ.comp K.subtype) ⟶ chi.representation)

private theorem inducedMultiplicity_cast
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (chi : IrreducibleCharacter K k)
    (psi : IrreducibleCharacter G k) :
    characterPairing (psi : ClassFunction G k)
        (ClassFunction.induce K (chi : ClassFunction K k)) =
      (inducedMultiplicity K chi psi : k) := by
  rw [characterPairing_comm,
    ClassFunction.frobeniusReciprocity K,
    ← chi.ofRepresentation_representation,
    ← psi.ofRepresentation_representation,
    ClassFunction.restrict_ofRepresentation]
  exact characterPairing_ofRepresentation_eq_finrank_hom_general
    chi.representation (FDRep.of (psi.representation.ρ.comp K.subtype))

/-- Source `seqInd_char`: every member of `seqInd` is the ordinary
character of an induced finite-dimensional representation. -/
theorem seqInd_char {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    ∃ V : FDRep k G, ClassFunction.ofRepresentation V.ρ = phi := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  obtain ⟨V, hV⟩ := exists_fdRep_irreducible_sum
    (Finset.univ : Finset (IrreducibleCharacter G k))
    (inducedMultiplicity K chi)
  refine ⟨V, hV.trans ?_⟩
  rw [← irreducibleCharacterExpansion_eq
    (ClassFunction.induce K (chi : ClassFunction K k)),
    irreducibleCharacterExpansion]
  apply Finset.sum_congr rfl
  intro psi hpsi
  rw [inducedMultiplicity_cast]

/-- Source `Cnat_seqInd1`: the degree of an induced character is a natural
number in the coefficient field. -/
theorem Cnat_seqInd1 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    ∃ n : ℕ, phi 1 = (n : k) := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  refine ⟨K.index * Module.finrank k chi.representation, ?_⟩
  rw [ClassFunction.induce_one K,
    IrreducibleCharacter.apply_one_eq_finrank, Nat.cast_mul]

/-- Source `Cint_seqInd1`: the same degree is also an integer in the
coefficient field. -/
theorem Cint_seqInd1 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    ∃ z : ℤ, phi 1 = (z : k) := by
  obtain ⟨n, hn⟩ := Cnat_seqInd1 K hphi
  exact ⟨n, by simpa using hn⟩

private theorem nontrivial_of_simple_general
    {G : Type u} {k : Type v} [Group G] [Field k]
    (V : FDRep k G) [CategoryTheory.Simple V] : Nontrivial V := by
  rw [← not_subsingleton_iff_nontrivial]
  intro hsub
  apply CategoryTheory.id_nonzero V
  apply ConcreteCategory.hom_ext
  intro x
  change x = 0
  exact Subsingleton.elim _ _

/-- Source `seqInd_neq0`: an induced irreducible character is nonzero. -/
theorem seqInd_neq0 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    phi ≠ 0 := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation :=
    nontrivial_of_simple_general chi.representation
  intro hzero
  have hone := congrArg (fun f : ClassFunction G k => f 1) hzero
  rw [ClassFunction.induce_one K,
    IrreducibleCharacter.apply_one_eq_finrank] at hone
  have hindex : (K.index : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite
  have hdegree : (Module.finrank k chi.representation : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Module.finrank_pos.ne')
  exact (mul_ne_zero hindex hdegree) (by simpa using hone)

/-- Source `seqInd1_neq0`: the degree of a member of `seqInd` is nonzero. -/
theorem seqInd1_neq0 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    phi 1 ≠ 0 := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  letI : CategoryTheory.Simple chi.representation :=
    chi.representation_simple
  letI : Nontrivial chi.representation :=
    nontrivial_of_simple_general chi.representation
  rw [ClassFunction.induce_one K,
    IrreducibleCharacter.apply_one_eq_finrank]
  exact mul_ne_zero
    (Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite)
    (Nat.cast_ne_zero.mpr (Module.finrank_pos.ne'))

/-- Source `cfnorm_seqInd_neq0`: every member of `seqInd` has nonzero
self-pairing. -/
theorem cfnorm_seqInd_neq0 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] [Fintype K]
    {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    characterPairing phi phi ≠ 0 := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  rw [ClassFunction.cfnorm_Ind_irr K chi]
  exact Nat.cast_ne_zero.mpr
    (ClassFunction.inertiaIndex_pos K (chi : ClassFunction K k)).ne'

/-- Source `seqInd_ortho`: distinct members of the duplicate-free induced
family are orthogonal. -/
theorem seqInd_ortho {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] [Fintype K]
    {calX : Finset (IrreducibleCharacter K k)}
    {phi psi : ClassFunction G k}
    (hphi : phi ∈ seqInd K calX) (hpsi : psi ∈ seqInd K calX)
    (hne : phi ≠ psi) :
    characterPairing phi psi = 0 := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  obtain ⟨xi, hxi, rfl⟩ := seqIndP.mp hpsi
  apply ClassFunction.not_cfclass_Ind_ortho K chi xi
  intro horbit
  apply hne
  exact (ClassFunction.cfclass_Ind_irrP K chi xi).1 horbit

/-- Source `seqInd_orthogonal`, in set-pairwise form. -/
theorem seqInd_orthogonal {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] [Fintype K]
    (calX : Finset (IrreducibleCharacter K k)) :
    Set.Pairwise (↑(seqInd K calX) : Set (ClassFunction G k))
      fun phi psi => characterPairing phi psi = 0 := by
  intro phi hphi psi hpsi hne
  exact seqInd_ortho K hphi hpsi hne

/-- Source `seqInd_free`: the distinct members of `seqInd` are linearly
independent. -/
theorem seqInd_free {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] [Fintype K]
    (calX : Finset (IrreducibleCharacter K k)) :
    LinearIndependent k
      (fun phi : {phi : ClassFunction G k // phi ∈ seqInd K calX} =>
        (phi.1 : ClassFunction G k)) := by
  let v := fun phi : {phi : ClassFunction G k // phi ∈ seqInd K calX} =>
    (phi.1 : ClassFunction G k)
  let dual := fun phi : {phi : ClassFunction G k // phi ∈ seqInd K calX} =>
    (characterPairing phi.1 phi.1)⁻¹ •
      IrreducibleCharacter.pairingLeft (phi.1 : ClassFunction G k)
  apply LinearIndependent.of_pairwise_dual_eq_zero_one v dual
  · intro phi psi hne
    have hval : phi.1 ≠ psi.1 := fun h => hne (Subtype.ext h)
    change (characterPairing phi.1 phi.1)⁻¹ *
        characterPairing phi.1 psi.1 = 0
    rw [seqInd_ortho K phi.property psi.property hval, mul_zero]
  · intro phi
    change (characterPairing phi.1 phi.1)⁻¹ *
        characterPairing phi.1 phi.1 = 1
    exact inv_mul_cancel₀ (cfnorm_seqInd_neq0 K phi.property)

/-- The inducing irreducibles whose induced class function is one of the
ambient irreducibles in `S`.  This is the finite set counted on the
right-hand side of source `size_irr_subseq_seqInd`. -/
def inducingIrrsOf {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (S : Finset (IrreducibleCharacter G k)) :
    Finset (IrreducibleCharacter K k) :=
  Finset.univ.filter fun chi =>
    ∃ psi ∈ S,
      ClassFunction.induce K (chi : ClassFunction K k) =
        (psi : ClassFunction G k)

@[simp]
theorem mem_inducingIrrsOf {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    {K : Subgroup G} {S : Finset (IrreducibleCharacter G k)}
    {chi : IrreducibleCharacter K k} :
    chi ∈ inducingIrrsOf K S ↔
      ∃ psi ∈ S,
        ClassFunction.induce K (chi : ClassFunction K k) =
          (psi : ClassFunction G k) := by
  simp [inducingIrrsOf]

/-- Source `size_irr_subseq_seqInd`: an irreducible subfamily of `seqInd`
has `K.index` inducing irreducibles over each of its members. -/
theorem size_irr_subseq_seqInd {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal] [Fintype K]
    (calX : Finset (IrreducibleCharacter K k))
    (S : Finset (IrreducibleCharacter G k))
    (hS : ∀ psi ∈ S, (psi : ClassFunction G k) ∈ seqInd K calX) :
    K.index * S.card = (inducingIrrsOf K S).card := by
  let X := inducingIrrsOf K S
  have hInd : ∀ chi ∈ X, IsIrreducibleCharacter G k
      (ClassFunction.induce K (chi : ClassFunction K k)) := by
    intro chi hchi
    obtain ⟨psi, hpsi, heq⟩ := mem_inducingIrrsOf.mp hchi
    rw [heq]
    exact psi.property
  have hstable : ∀ chi ∈ X, ∀ x : G,
      chi.normalConjugate K x ∈ X := by
    intro chi hchi x
    obtain ⟨psi, hpsi, heq⟩ := mem_inducingIrrsOf.mp hchi
    apply mem_inducingIrrsOf.mpr
    refine ⟨psi, hpsi, ?_⟩
    exact (ClassFunction.induce_normalConjugate K x
      (chi : ClassFunction K k)).trans heq
  let F : {chi // chi ∈ X} → IrreducibleCharacter G k :=
    ClassFunction.induceIrreducibleOn K X hInd
  have himage : Finset.univ.image F = S := by
    ext psi
    constructor
    · intro hpsi
      obtain ⟨chi, hchi, hF⟩ := Finset.mem_image.mp hpsi
      obtain ⟨eta, heta, heq⟩ := mem_inducingIrrsOf.mp chi.property
      have hval := congrArg Subtype.val hF
      have hpsiEta : psi = eta := by
        apply Subtype.ext
        exact hval.symm.trans heq
      simpa [hpsiEta] using heta
    · intro hpsi
      obtain ⟨chi, hchi, heq⟩ := seqIndP.mp (hS psi hpsi)
      have hchiX : chi ∈ X :=
        mem_inducingIrrsOf.mpr ⟨psi, hpsi, heq.symm⟩
      let chiX : {chi // chi ∈ X} := ⟨chi, hchiX⟩
      apply Finset.mem_image.mpr
      refine ⟨chiX, Finset.mem_univ _, ?_⟩
      apply Subtype.ext
      exact heq.symm
  have hcard := ClassFunction.card_imset_Ind_irr K X hInd hstable
  change X.card = K.index * (Finset.univ.image F).card at hcard
  rw [himage] at hcard
  exact hcard.symm

/-! ## The integral lattice on a `seqInd` family -/

/-- The source lattice `'Z[S]` for an induced family `S`. -/
abbrev SeqIndLattice {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (calX : Finset (IrreducibleCharacter K k)) :=
  IntegralLattice {phi : ClassFunction G k // phi ∈ seqInd K calX}

/-- Realization of an integral combination of members of `seqInd`. -/
def seqIndRealize {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (calX : Finset (IrreducibleCharacter K k)) :
    SeqIndLattice K calX →+ ClassFunction G k :=
  Finsupp.liftAddHom fun phi =>
    { toFun := fun z => z • (phi.1 : ClassFunction G k)
      map_zero' := zero_zsmul _
      map_add' := fun m n => add_zsmul (phi.1 : ClassFunction G k) m n }

@[simp]
theorem seqIndRealize_single {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (calX : Finset (IrreducibleCharacter K k))
    (phi : {phi : ClassFunction G k // phi ∈ seqInd K calX}) (z : ℤ) :
    seqIndRealize K calX (Finsupp.single phi z) =
      z • (phi.1 : ClassFunction G k) := by
  simp [seqIndRealize]

/-- Source `seqInd_zcharW`: each member of `seqInd` belongs to its integral
span. -/
theorem seqInd_zcharW {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    ∃ z : SeqIndLattice K calX, seqIndRealize K calX z = phi := by
  let p : {psi : ClassFunction G k // psi ∈ seqInd K calX} := ⟨phi, hphi⟩
  refine ⟨Finsupp.single p 1, ?_⟩
  simp [p]

private noncomputable def virtualCharacterOfFDRepGeneral
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (V : FDRep k G) : VirtualCharacter G k :=
  Finsupp.equivFunOnFinite.symm fun chi : IrreducibleCharacter G k =>
    (Module.finrank k (chi.representation ⟶ V) : ℤ)

private theorem realize_virtualCharacterOfFDRepGeneral
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (V : FDRep k G) :
    VirtualCharacter.realize (virtualCharacterOfFDRepGeneral V) =
      ClassFunction.ofRepresentation V.ρ := by
  rw [virtualCharacterOfFDRepGeneral,
    Finsupp.equivFunOnFinite_symm_eq_sum, map_sum]
  simp only [VirtualCharacter.realize_single, Int.cast_natCast]
  rw [← irreducibleCharacterExpansion_eq
    (ClassFunction.ofRepresentation V.ρ), irreducibleCharacterExpansion]
  apply Finset.sum_congr rfl
  intro chi hchi
  rw [characterPairing_comm, ← chi.ofRepresentation_representation]
  apply congrArg (fun a : k =>
    a • ClassFunction.ofRepresentation chi.representation.ρ)
  exact (characterPairing_ofRepresentation_eq_finrank_hom_general
    V chi.representation).symm

/-- Source `seqInd_vcharW`: every induced member is a virtual character of
the ambient group. -/
theorem seqInd_vcharW {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    ∃ z : VirtualCharacter G k, VirtualCharacter.realize z = phi := by
  obtain ⟨V, hV⟩ := seqInd_char K hphi
  exact ⟨virtualCharacterOfFDRepGeneral V,
    (realize_virtualCharacterOfFDRepGeneral V).trans hV⟩

/-- Source `seqInd_vchar`: every member is a virtual character supported on
the normal inducing subgroup. -/
theorem seqInd_vchar {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    ∃ z : VirtualCharacter G k,
      VirtualCharacter.realize z = phi ∧
      VirtualCharacter.realize z ∈ ClassFunction.supportedOn (K : Set G) := by
  obtain ⟨z, hz⟩ := seqInd_vcharW K hphi
  exact ⟨z, hz, hz.symm ▸ seqInd_on K hphi⟩

/-- Source `seqInd_zchar`: every integral combination of induced members is
supported on the normal inducing subgroup. -/
theorem seqInd_zchar {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (calX : Finset (IrreducibleCharacter K k))
    (z : SeqIndLattice K calX) :
    seqIndRealize K calX z ∈ ClassFunction.supportedOn (K : Set G) := by
  classical
  induction z using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add phi n z hphi hn ih =>
      rw [map_add, seqIndRealize_single]
      exact Submodule.add_mem _
        (zsmul_mem (seqInd_on K phi.property) n) ih

/-- The nonidentity elements of a group. -/
def nonidentitySet (G : Type u) [Group G] : Set G :=
  {g | g ≠ 1}

/-- The nonidentity elements lying in a subgroup. -/
def subgroupNonidentity {G : Type u} [Group G] (K : Subgroup G) : Set G :=
  (K : Set G) ∩ nonidentitySet G

@[simp]
theorem mem_nonidentitySet {G : Type u} [Group G] {g : G} :
    g ∈ nonidentitySet G ↔ g ≠ 1 :=
  Iff.rfl

@[simp]
theorem mem_subgroupNonidentity {G : Type u} [Group G]
    {K : Subgroup G} {g : G} :
    g ∈ subgroupNonidentity K ↔ g ∈ K ∧ g ≠ 1 :=
  Iff.rfl

/-- Source `zcharD1_seqInd`: for the integral span of a normally induced
family, support off the ambient identity is equivalent to support on the
nonidentity elements of the inducing subgroup. -/
theorem zcharD1_seqInd {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (calX : Finset (IrreducibleCharacter K k))
    (z : SeqIndLattice K calX) :
    seqIndRealize K calX z ∈ ClassFunction.supportedOn (nonidentitySet G) ↔
      seqIndRealize K calX z ∈
        ClassFunction.supportedOn (subgroupNonidentity K) := by
  constructor
  · intro h x hx
    by_cases hxK : x ∈ K
    · apply h
      intro hxne
      exact hx ⟨hxK, hxne⟩
    · exact ClassFunction.eq_zero_of_mem_supportedOn
        (seqInd_zchar K calX z) hxK
  · intro h x hx
    apply ClassFunction.eq_zero_of_mem_supportedOn h
    intro hxK
    exact hx hxK.2

/-- Source `zcharD1_seqInd_on`: the corresponding support consequence. -/
theorem zcharD1_seqInd_on {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    (calX : Finset (IrreducibleCharacter K k))
    (z : SeqIndLattice K calX)
    (hz : seqIndRealize K calX z ∈
      ClassFunction.supportedOn (nonidentitySet G)) :
    seqIndRealize K calX z ∈
      ClassFunction.supportedOn (subgroupNonidentity K) :=
  (zcharD1_seqInd K calX z).mp hz

/-- Integral combinations inherit a common support bound on the generators. -/
private theorem seqIndRealize_mem_supportedOn_of_generators
    {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (calX : Finset (IrreducibleCharacter K k))
    (A : Set G)
    (hA : ∀ phi ∈ seqInd K calX, phi ∈ ClassFunction.supportedOn A)
    (z : SeqIndLattice K calX) :
    seqIndRealize K calX z ∈ ClassFunction.supportedOn A := by
  classical
  induction z using Finsupp.induction with
  | zero => exact Submodule.zero_mem _
  | single_add phi n z hphi hn ih =>
      rw [map_add, seqIndRealize_single]
      exact Submodule.add_mem _
        (zsmul_mem (hA phi.1 phi.property) n) ih

/-- Source `zcharD1_seqInd_Dade`: if all generators are supported on
`{1} ∪ A` and `1 ∉ A`, then support off the identity is equivalent to
support on `A`. -/
theorem zcharD1_seqInd_Dade {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) (calX : Finset (IrreducibleCharacter K k))
    (A : Set G) (hone : (1 : G) ∉ A)
    (hA : ∀ phi ∈ seqInd K calX,
      phi ∈ ClassFunction.supportedOn ({1} ∪ A))
    (z : SeqIndLattice K calX) :
    seqIndRealize K calX z ∈ ClassFunction.supportedOn (nonidentitySet G) ↔
      seqIndRealize K calX z ∈ ClassFunction.supportedOn A := by
  have hsupport :=
    seqIndRealize_mem_supportedOn_of_generators K calX ({1} ∪ A) hA z
  constructor
  · intro hoff x hxA
    by_cases hx1 : x = 1
    · apply ClassFunction.eq_zero_of_mem_supportedOn hoff
      simpa [nonidentitySet, hx1]
    · apply ClassFunction.eq_zero_of_mem_supportedOn hsupport
      simpa [hx1, hxA]
  · intro hA' x hxoff
    have hx1 : x = 1 := not_ne_iff.mp hxoff
    apply ClassFunction.eq_zero_of_mem_supportedOn hA'
    simpa [hx1] using hone

/-- Source `dvd_index_seqInd1`: the degree of a normally induced member,
divided by the subgroup index, is a natural number. -/
theorem dvd_index_seqInd1 {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) {calX : Finset (IrreducibleCharacter K k)}
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    ∃ n : ℕ, phi 1 / (K.index : k) = (n : k) := by
  obtain ⟨chi, hchi, rfl⟩ := seqIndP.mp hphi
  refine ⟨Module.finrank k chi.representation, ?_⟩
  rw [ClassFunction.induce_one K,
    IrreducibleCharacter.apply_one_eq_finrank]
  exact mul_div_cancel_left₀ _
    (Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite)

/-- Source `sub_seqInd_on`: the degree-weighted difference of two members
of `seqInd` is supported on the nonidentity elements of the inducing
subgroup. -/
theorem sub_seqInd_on {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    {calX : Finset (IrreducibleCharacter K k)}
    {phi psi : ClassFunction G k}
    (hphi : phi ∈ seqInd K calX) (hpsi : psi ∈ seqInd K calX) :
    (psi 1) • phi - (phi 1) • psi ∈
      ClassFunction.supportedOn (subgroupNonidentity K) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  by_cases hxK : x ∈ K
  · have hx1 : x = 1 := by
      by_contra hx1
      exact hx ⟨hxK, hx1⟩
    subst x
    change psi 1 * phi 1 - phi 1 * psi 1 = 0
    rw [mul_comm, sub_self]
  · have hphi0 := ClassFunction.eq_zero_of_mem_supportedOn
      (seqInd_on K hphi) hxK
    have hpsi0 := ClassFunction.eq_zero_of_mem_supportedOn
      (seqInd_on K hpsi) hxK
    simp [hphi0, hpsi0]

/-- Source `sub_seqInd_zchar`: the same weighted difference has an explicit
preimage in the integral lattice on `seqInd`. -/
theorem sub_seqInd_zchar {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    {calX : Finset (IrreducibleCharacter K k)}
    {phi psi : ClassFunction G k}
    (hphi : phi ∈ seqInd K calX) (hpsi : psi ∈ seqInd K calX) :
    ∃ z : SeqIndLattice K calX,
      seqIndRealize K calX z = (psi 1) • phi - (phi 1) • psi ∧
      seqIndRealize K calX z ∈
        ClassFunction.supportedOn (subgroupNonidentity K) := by
  obtain ⟨m, hm⟩ := Cnat_seqInd1 K hphi
  obtain ⟨n, hn⟩ := Cnat_seqInd1 K hpsi
  let p : {xi : ClassFunction G k // xi ∈ seqInd K calX} := ⟨phi, hphi⟩
  let q : {xi : ClassFunction G k // xi ∈ seqInd K calX} := ⟨psi, hpsi⟩
  let z : SeqIndLattice K calX :=
    (n : ℤ) • Finsupp.single p 1 -
      (m : ℤ) • Finsupp.single q 1
  refine ⟨z, ?_, ?_⟩
  · simp only [z, map_sub, map_zsmul, seqIndRealize_single,
      one_zsmul, p, q]
    rw [← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k]
    simpa only [Int.cast_natCast, hm, hn]
  · rw [show seqIndRealize K calX z =
        (psi 1) • phi - (phi 1) • psi by
      simp only [z, map_sub, map_zsmul, seqIndRealize_single,
        one_zsmul, p, q]
      rw [← Int.cast_smul_eq_zsmul k, ← Int.cast_smul_eq_zsmul k]
      simpa only [Int.cast_natCast, hm, hn]]
    exact sub_seqInd_on K hphi hpsi

/-! ## The source `Beta` subsection -/

/-- Source `cfInd1_sub_lin_on`: if `xi(1) = [G:K]`, then the difference
between the induced trivial character and `xi` is supported on `K^#`. -/
theorem cfInd1_sub_lin_on {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    {calX : Finset (IrreducibleCharacter K k)}
    {xi : ClassFunction G k} (hxi : xi ∈ seqInd K calX)
    (hxi1 : xi 1 = (K.index : k)) :
    ClassFunction.induce K
          ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
            ClassFunction K k) - xi ∈
      ClassFunction.supportedOn (subgroupNonidentity K) := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  by_cases hxK : x ∈ K
  · have hx1 : x = 1 := by
      by_contra hx1
      exact hx ⟨hxK, hx1⟩
    subst x
    simp only [ClassFunction.sub_apply]
    rw [ClassFunction.induce_one K,
      IrreducibleCharacter.trivial_apply, mul_one, hxi1, sub_self]
  · have hind0 : ClassFunction.induce K
        ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
          ClassFunction K k) x = 0 := by
      apply ClassFunction.eq_zero_of_mem_supportedOn
        (seqInd_on K (calX := {IrreducibleCharacter.trivial})
          (show ClassFunction.induce K
              ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
                ClassFunction K k) ∈
              seqInd K ({IrreducibleCharacter.trivial} :
                Finset (IrreducibleCharacter K k)) by
            apply seqIndP.mpr
            exact ⟨IrreducibleCharacter.trivial, by simp, rfl⟩))
        hxK
    have hxi0 := ClassFunction.eq_zero_of_mem_supportedOn
      (seqInd_on K hxi) hxK
    simp [hind0, hxi0]

/-- Source `cfInd1_sub_lin_vchar`: the preceding difference is a virtual
character as well as being supported on `K^#`. -/
theorem cfInd1_sub_lin_vchar {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    {calX : Finset (IrreducibleCharacter K k)}
    {xi : ClassFunction G k} (hxi : xi ∈ seqInd K calX)
    (hxi1 : xi 1 = (K.index : k)) :
    ∃ z : VirtualCharacter G k,
      VirtualCharacter.realize z =
        ClassFunction.induce K
          ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
            ClassFunction K k) - xi ∧
      VirtualCharacter.realize z ∈
        ClassFunction.supportedOn (subgroupNonidentity K) := by
  have htriv : ClassFunction.induce K
        ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
          ClassFunction K k) ∈
      seqInd K ({IrreducibleCharacter.trivial} :
        Finset (IrreducibleCharacter K k)) := by
    apply seqIndP.mpr
    exact ⟨IrreducibleCharacter.trivial, by simp, rfl⟩
  obtain ⟨ztriv, hztriv⟩ := seqInd_vcharW K htriv
  obtain ⟨zxi, hzxi⟩ := seqInd_vcharW K hxi
  let z : VirtualCharacter G k := ztriv - zxi
  refine ⟨z, ?_, ?_⟩
  · simp only [z, VirtualCharacter.realize_sub, hztriv, hzxi]
  · rw [show VirtualCharacter.realize z =
        ClassFunction.induce K
          ((IrreducibleCharacter.trivial : IrreducibleCharacter K k) :
            ClassFunction K k) -
          xi by
      simp only [z, VirtualCharacter.realize_sub, hztriv, hzxi]]
    exact cfInd1_sub_lin_on K hxi hxi1

/-- Source `seqInd_sub_lin_on`: subtracting the natural index quotient of
`xi` from any member of `seqInd` is supported on `K^#`. -/
theorem seqInd_sub_lin_on {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    {calX : Finset (IrreducibleCharacter K k)}
    {xi : ClassFunction G k} (hxi : xi ∈ seqInd K calX)
    (hxi1 : xi 1 = (K.index : k))
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    phi - (phi 1 / (K.index : k)) • xi ∈
      ClassFunction.supportedOn (subgroupNonidentity K) := by
  obtain ⟨n, hn⟩ := dvd_index_seqInd1 K hphi
  rw [hn]
  rw [ClassFunction.mem_supportedOn_iff]
  intro x hx
  by_cases hxK : x ∈ K
  · have hx1 : x = 1 := by
      by_contra hx1
      exact hx ⟨hxK, hx1⟩
    subst x
    simp only [ClassFunction.sub_apply, ClassFunction.smul_apply, smul_eq_mul]
    rw [hxi1]
    have hindex : (K.index : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite
    have hphi1 : phi 1 = (n : k) * (K.index : k) := by
      calc
        phi 1 = (phi 1 / (K.index : k)) * (K.index : k) :=
          (div_mul_cancel₀ _ hindex).symm
        _ = (n : k) * (K.index : k) := by rw [hn]
    rw [hphi1, sub_self]
  · have hphi0 := ClassFunction.eq_zero_of_mem_supportedOn
      (seqInd_on K hphi) hxK
    have hxi0 := ClassFunction.eq_zero_of_mem_supportedOn
      (seqInd_on K hxi) hxK
    simp [hphi0, hxi0]

/-- Source `seqInd_sub_lin_vchar`: the preceding normalized difference has
an explicit preimage in the integral lattice on `seqInd`. -/
theorem seqInd_sub_lin_vchar {G : Type u} {k : Type v} [Group G] [Fintype G]
    [Field k] [IsAlgClosed k] [CharZero k]
    (K : Subgroup G) [K.Normal]
    {calX : Finset (IrreducibleCharacter K k)}
    {xi : ClassFunction G k} (hxi : xi ∈ seqInd K calX)
    (hxi1 : xi 1 = (K.index : k))
    {phi : ClassFunction G k} (hphi : phi ∈ seqInd K calX) :
    ∃ z : SeqIndLattice K calX,
      seqIndRealize K calX z =
        phi - (phi 1 / (K.index : k)) • xi ∧
      seqIndRealize K calX z ∈
        ClassFunction.supportedOn (subgroupNonidentity K) := by
  obtain ⟨n, hn⟩ := dvd_index_seqInd1 K hphi
  let p : {eta : ClassFunction G k // eta ∈ seqInd K calX} := ⟨phi, hphi⟩
  let q : {eta : ClassFunction G k // eta ∈ seqInd K calX} := ⟨xi, hxi⟩
  let z : SeqIndLattice K calX :=
    Finsupp.single p 1 - (n : ℤ) • Finsupp.single q 1
  refine ⟨z, ?_, ?_⟩
  · simp only [z, map_sub, map_zsmul, seqIndRealize_single,
      one_zsmul, p, q]
    rw [← Int.cast_smul_eq_zsmul k]
    simpa only [Int.cast_natCast, hn]
  · rw [show seqIndRealize K calX z =
        phi - (phi 1 / (K.index : k)) • xi by
      simp only [z, map_sub, map_zsmul, seqIndRealize_single,
        one_zsmul, p, q]
      rw [← Int.cast_smul_eq_zsmul k]
      simpa only [Int.cast_natCast, hn]]
    exact seqInd_sub_lin_on K hxi hxi1 hphi

end

end Submission.OddOrder.PF
