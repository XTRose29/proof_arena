import Mathlib.NumberTheory.Niven
import Submission.OddOrder.MathlibSupport.OneDimensionalEndomorphism
import Submission.OddOrder.MathlibSupport.RepresentationDeterminant
import Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter
import Submission.OddOrder.PF.Section05.SubcoherentProperties
import Submission.OddOrder.PF.Section06.ConstantIrrModTISylow

/-!
# The Case-A alignment calculation in Sibley's theorem

This file isolates the calculation in `PFsection6.v`, lines 773--945.  Its
input record deliberately stops before the conclusion of the calculation.
It contains the two coherence witnesses, the two orthogonal source
families, the central section, the regular-minus-quotient-regular identity,
and the consequence of `constant_irr_mod_TI_Sylow` used in the source.

The result remembers both exceptional choices in the Coq proof.  If the
integer norm equation has its exceptional solution, the witness on `Y` is
dualized and `Y` has at most two elements.  A second signed-irreducible
comparison can independently dualize the witness on `X`, again only when
`X` has at most two elements.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open CategoryTheory
open scoped BigOperators Classical MonoidAlgebra commutatorElement

universe u

local instance caseAAlignmentInvertibleCard
    {Q : Type u} [Group Q] [Fintype Q] :
    Invertible (Nat.card Q : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

/-! ## The regular-minus-quotient-regular class function -/

/-- Universe-polymorphic specialization to complex characters of the
translation-kernel/representation-kernel identity. -/
private theorem caseATranslationKernelIrreducibleCharacterComplex
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
      representation_isIrreducible_of_simple_fdRep chi.representation
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
          simpa only [Representation.asAlgebraHom_of] using htraceGroup g
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

/-- The difference between the regular class function of `Q` and the
inflation of the regular class function of `Q / Z`.

It is `|Q| - [Q : Z]` at `1`, `-[Q : Z]` on `Z \ {1}`, and zero outside
`Z`.  This pointwise presentation avoids choosing an explicit quotient
equivalence in every application. -/
def regularQuotientDifference
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal] : ClassFunction Q ℂ where
  val x :=
    if x = 1 then (Nat.card Q : ℂ) - (Z.index : ℂ)
    else if x ∈ Z then -(Z.index : ℂ) else 0
  property g x := by
    have hmem : g * x * g⁻¹ ∈ Z ↔ x ∈ Z :=
      IsConjStable.normal Z g x
    by_cases hx : x = 1
    · subst x
      simp
    · have hconj : g * x * g⁻¹ ≠ 1 := by
        intro h
        apply hx
        calc
          x = g⁻¹ * (g * x * g⁻¹) * g := by group
          _ = 1 := by rw [h]; simp
      simp only [hconj, hx, if_false, hmem]

@[simp]
theorem regularQuotientDifference_one
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal] :
    regularQuotientDifference Z 1 =
      (Nat.card Q : ℂ) - (Z.index : ℂ) := by
  simp [regularQuotientDifference]

theorem regularQuotientDifference_apply_of_mem_ne_one
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal]
    {z : Q} (hzZ : z ∈ Z) (hz : z ≠ 1) :
    regularQuotientDifference Z z = -(Z.index : ℂ) := by
  simp [regularQuotientDifference, hz, hzZ]

theorem regularQuotientDifference_sub_one_of_mem_ne_one
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal]
    {z : Q} (hzZ : z ∈ Z) (hz : z ≠ 1) :
    regularQuotientDifference Z z -
        regularQuotientDifference Z 1 = -(Nat.card Q : ℂ) := by
  rw [regularQuotientDifference_apply_of_mem_ne_one Z hzZ hz,
    regularQuotientDifference_one]
  ring

private def regularClassFunction
    {Q : Type u} [Group Q] [Fintype Q] : ClassFunction Q ℂ where
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

private def inflatedQuotientRegular
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal] : ClassFunction Q ℂ where
  val x := if x ∈ Z then (Z.index : ℂ) else 0
  property g x := by
    exact if_congr (IsConjStable.normal Z g x) rfl rfl

@[simp]
private theorem inflatedQuotientRegular_apply
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal] (x : Q) :
    inflatedQuotientRegular Z x =
      if x ∈ Z then (Z.index : ℂ) else 0 :=
  rfl

private theorem regularQuotientDifference_eq
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal] :
    regularQuotientDifference Z =
      regularClassFunction - inflatedQuotientRegular Z := by
  ext x
  by_cases hx : x = 1
  · subst x
    simp [regularQuotientDifference, regularClassFunction]
  · by_cases hxZ : x ∈ Z
    · simp [regularQuotientDifference, regularClassFunction, hx, hxZ]
    · simp [regularQuotientDifference, regularClassFunction, hx, hxZ]

private theorem pairing_inflatedQuotientRegular_eq_finrank
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal]
    (chi : IrreducibleCharacter Q ℂ) :
    characterPairing (chi : ClassFunction Q ℂ)
        (inflatedQuotientRegular Z) =
      (Module.finrank ℂ
        (Representation.invariants
          (chi.representation.ρ.comp Z.subtype)) : ℂ) := by
  let rhoZ : Representation ℂ Z chi.representation :=
    chi.representation.ρ.comp Z.subtype
  have hchar (z : Z) : rhoZ.character z = chi z := by
    change chi.representation.character (z : Q) = chi (z : Q)
    exact chi.representation_character (z : Q)
  have hsum :
      (∑ x : Q, chi x * inflatedQuotientRegular Z x⁻¹) =
        ∑ z : Z, chi z * (Z.index : ℂ) := by
    calc
      (∑ x : Q, chi x * inflatedQuotientRegular Z x⁻¹) =
          ∑ x : Q, if x ∈ Z then chi x * (Z.index : ℂ) else 0 := by
        apply Finset.sum_congr rfl
        intro x _
        by_cases hx : x ∈ Z
        · rw [inflatedQuotientRegular_apply,
            if_pos (Z.inv_mem hx), if_pos hx]
        · have hxinv : x⁻¹ ∉ Z := by simpa using hx
          rw [inflatedQuotientRegular_apply, if_neg hxinv,
            mul_zero, if_neg hx]
      _ = ∑ z : Z, chi z * (Z.index : ℂ) := by
        rw [← Finset.sum_filter]
        apply Finset.sum_subtype
        intro x
        simp
  have hpairAverage :
      characterPairing (chi : ClassFunction Q ℂ)
          (inflatedQuotientRegular Z) =
        (Nat.card Z : ℂ)⁻¹ * ∑ z : Z, chi z := by
    rw [characterPairing, hsum, ← Finset.sum_mul]
    rw [← Z.card_mul_index, Nat.cast_mul]
    have hZcard : (Nat.card Z : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hindex : (Z.index : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Z.index_ne_zero_of_finite
    field_simp [hZcard, hindex]
  have havg := rhoZ.card_inv_mul_sum_char_eq_finrank
  rw [hpairAverage]
  simpa only [hchar] using havg

private theorem pairing_inflatedQuotientRegular
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal]
    (chi : IrreducibleCharacter Q ℂ) :
    characterPairing (chi : ClassFunction Q ℂ)
        (inflatedQuotientRegular Z) =
      if Z ≤ ClassFunction.translationKernel
          (chi : ClassFunction Q ℂ) then chi 1 else 0 := by
  let rho : Representation ℂ Q chi.representation := chi.representation.ρ
  letI : Simple chi.representation := chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep chi.representation
  rw [pairing_inflatedQuotientRegular_eq_finrank]
  by_cases hker : Z ≤ ClassFunction.translationKernel
      (chi : ClassFunction Q ℂ)
  · rw [if_pos hker]
    have hinvariants :
        Representation.invariants (rho.comp Z.subtype) = ⊤ := by
      apply top_unique
      intro v _
      rw [Representation.mem_invariants]
      intro z
      have hz : (z : Q) ∈ chi.representation.ρ.ker := by
        rw [← caseATranslationKernelIrreducibleCharacterComplex chi]
        exact hker z.property
      exact DFunLike.congr_fun (MonoidHom.mem_ker.mp hz) v
    rw [show chi.representation.ρ = rho from rfl, hinvariants,
      finrank_top, ← IrreducibleCharacter.apply_one_eq_finrank]
  · rw [if_neg hker]
    have hinvariants :
        Representation.invariants (rho.comp Z.subtype) = ⊥ := by
      let U : Subrepresentation rho :=
        { toSubmodule := Representation.invariants (rho.comp Z.subtype)
          apply_mem_toSubmodule g :=
            Representation.le_comap_invariants rho Z g }
      rcases IsSimpleOrder.eq_bot_or_eq_top U with hU | hU
      · apply SetLike.ext
        intro v
        have hv := congrArg (fun W : Subrepresentation rho ↦ v ∈ W) hU
        change
          (v ∈ Representation.invariants (rho.comp Z.subtype)) =
            (v ∈ (⊥ : Submodule ℂ chi.representation)) at hv
        exact iff_of_eq hv
      · exfalso
        apply hker
        rw [caseATranslationKernelIrreducibleCharacterComplex chi]
        intro z hz
        rw [MonoidHom.mem_ker]
        ext v
        have hv : v ∈ U := by
          rw [hU]
          trivial
        exact (Representation.mem_invariants _ _).mp hv ⟨z, hz⟩
    rw [show chi.representation.ρ = rho from rfl, hinvariants,
      finrank_bot, Nat.cast_zero]

private theorem pairing_regularClassFunction
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) :
    characterPairing (chi : ClassFunction Q ℂ)
      (regularClassFunction : ClassFunction Q ℂ) = chi 1 := by
  rw [characterPairing]
  rw [Finset.sum_eq_single (1 : Q)]
  · simp only [inv_one, regularClassFunction, if_pos]
    field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne']
  · intro x _ hx
    have hxinv : x⁻¹ ≠ 1 := by simpa using hx
    simp [regularClassFunction, hxinv]
  · simp

private theorem pairing_regularQuotientDifference
    {Q : Type u} [Group Q] [Fintype Q]
    (Z : Subgroup Q) [Z.Normal]
    (chi : IrreducibleCharacter Q ℂ) :
    characterPairing (chi : ClassFunction Q ℂ)
        (regularQuotientDifference Z) =
      if Z ≤ ClassFunction.translationKernel
          (chi : ClassFunction Q ℂ) then 0 else chi 1 := by
  rw [regularQuotientDifference_eq, sub_eq_add_neg,
    characterPairing_add_right, ← neg_one_smul ℂ,
    characterPairing_smul_right,
    pairing_regularClassFunction,
    pairing_inflatedQuotientRegular]
  split_ifs <;> simp

/-! ## Small algebraic helpers -/

private theorem pairing_neg_left
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing (-f) g = -characterPairing f g := by
  rw [← neg_one_smul ℂ f, characterPairing_smul_left]
  ring

private theorem pairing_neg_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f g : ClassFunction Q ℂ) :
    characterPairing f (-g) = -characterPairing f g := by
  rw [← neg_one_smul ℂ g, characterPairing_smul_right]
  ring

private theorem pairing_sub_left
    {Q : Type u} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    characterPairing (f - g) h =
      characterPairing f h - characterPairing g h := by
  rw [sub_eq_add_neg, characterPairing_add_left,
    pairing_neg_left, sub_eq_add_neg]

private theorem pairing_sub_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f g h : ClassFunction Q ℂ) :
    characterPairing f (g - h) =
      characterPairing f g - characterPairing f h := by
  rw [sub_eq_add_neg, characterPairing_add_right,
    pairing_neg_right, sub_eq_add_neg]

private theorem pairing_finset_sum_left
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (g : ClassFunction Q ℂ) :
    characterPairing (∑ i ∈ s, f i) g =
      ∑ i ∈ s, characterPairing (f i) g := by
  exact map_sum (characterPairingRight g) f s

private theorem pairing_finset_sum_right
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) {I : Type*}
    (s : Finset I) (g : I → ClassFunction Q ℂ) :
    characterPairing f (∑ i ∈ s, g i) =
      ∑ i ∈ s, characterPairing f (g i) := by
  exact map_sum (characterPairingLeft f) g s

private theorem virtual_pairing_eq_int
    {Q : Type u} [Group Q] [Fintype Q]
    {f g : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f)
    (hg : ClassFunction.IsVirtual g) :
    ∃ n : ℤ, characterPairing f g = (n : ℂ) := by
  obtain ⟨v, rfl⟩ := hf
  obtain ⟨w, rfl⟩ := hg
  exact ⟨coeffDot v w,
    VirtualCharacter.characterPairing_realize v w⟩

private theorem virtual_self_pairing_eq_nat
    {Q : Type u} [Group Q] [Fintype Q]
    {f : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f) :
    ∃ n : ℕ, characterPairing f f = (n : ℂ) := by
  obtain ⟨v, rfl⟩ := hf
  refine ⟨Int.toNat (normSq v), ?_⟩
  rw [VirtualCharacter.characterPairing_realize]
  have hnonneg : 0 ≤ normSq v := normSq_nonneg v
  exact_mod_cast (Int.toNat_of_nonneg hnonneg).symm

private theorem exists_signed_irreducible_of_virtual_pairing_one
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

private theorem virtual_natCast_smul
    {Q : Type u} [Group Q]
    {f : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f) (n : ℕ) :
    ClassFunction.IsVirtual ((n : ℂ) • f) :=
  hf.natCast_smul n

private theorem virtual_intCast_smul
    {Q : Type u} [Group Q]
    {f : ClassFunction Q ℂ}
    (hf : ClassFunction.IsVirtual f) (n : ℤ) :
    ClassFunction.IsVirtual ((n : ℂ) • f) := by
  have h := hf.zsmul n
  rw [← Int.cast_smul_eq_zsmul ℂ] at h
  exact h

private theorem virtual_finset_sum
    {Q : Type u} [Group Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (hf : ∀ i ∈ s, ClassFunction.IsVirtual (f i)) :
    ClassFunction.IsVirtual (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using
      (ClassFunction.IsVirtual.zero :
        ClassFunction.IsVirtual (0 : ClassFunction Q ℂ))
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi]
      exact (hf i (Finset.mem_insert_self i s)).add
        (ih fun j hj ↦ hf j (Finset.mem_insert_of_mem hj))

/-- The elementary integer rigidity used at Coq lines 716--727 and
891--907. -/
private theorem integer_norm_coefficient_dichotomy
    (m : ℕ) (q : ℤ) (hm : 2 ≤ m)
    (hsmall : q ^ 2 * (m : ℤ) + 1 - 2 * q < 2) :
    q = 0 ∨ q = 1 ∧ m = 2 := by
  have hmZ : (2 : ℤ) ≤ (m : ℤ) := by exact_mod_cast hm
  have hqSq : 0 ≤ q ^ 2 := sq_nonneg q
  have htwoSq : 2 * q ^ 2 ≤ (m : ℤ) * q ^ 2 :=
    mul_le_mul_of_nonneg_right hmZ hqSq
  have htwoSq' : 2 * q ^ 2 ≤ q ^ 2 * (m : ℤ) := by
    simpa [mul_comm] using htwoSq
  by_cases hq0 : q = 0
  · exact Or.inl hq0
  by_cases hq1 : q = 1
  · right
    refine ⟨hq1, ?_⟩
    subst q
    norm_num at hsmall
    omega
  have hqCases : q ≤ -1 ∨ 2 ≤ q := by omega
  rcases hqCases with hqNeg | hqPos
  · have hsqOne : 1 ≤ q ^ 2 := by nlinarith [sq_nonneg (q + 1)]
    nlinarith
  · have hsqFour : 4 ≤ q ^ 2 := by nlinarith [sq_nonneg (q - 2)]
    nlinarith

private theorem regular_projection_from_characterization
    {L : Type u} [Group L] [Fintype L]
    (Z : Subgroup L) [Z.Normal]
    (X : Finset (ClassFunction L ℂ))
    (hXchar : ∀ chi : IrreducibleCharacter L ℂ,
      ((chi : ClassFunction L ℂ) ∈ X ↔
        ¬ Z ≤ ClassFunction.translationKernel
          (chi : ClassFunction L ℂ)))
    (hXirr : ∀ xi ∈ X, IsIrreducibleCharacter L ℂ xi)
    (hXorth : ∀ xi ∈ X, ∀ zeta ∈ X,
      characterPairing xi zeta = if xi = zeta then 1 else 0)
    (xi₁ : ClassFunction L ℂ) (hxi₁Ne : xi₁ 1 ≠ 0)
    (d : ClassFunction L ℂ → ℕ)
    (hd : ∀ xi ∈ X, xi 1 = (d xi : ℂ) * xi₁ 1) :
    (∑ xi ∈ X, (d xi : ℂ) • xi) =
      (xi₁ 1)⁻¹ • regularQuotientDifference Z := by
  let lhs : ClassFunction L ℂ := ∑ xi ∈ X, (d xi : ℂ) • xi
  let rhs : ClassFunction L ℂ :=
    (xi₁ 1)⁻¹ • regularQuotientDifference Z
  have hpair (chi : IrreducibleCharacter L ℂ) :
      characterPairing (chi : ClassFunction L ℂ) lhs =
        characterPairing (chi : ClassFunction L ℂ) rhs := by
    by_cases hker : Z ≤ ClassFunction.translationKernel
        (chi : ClassFunction L ℂ)
    · have hchiNotX : (chi : ClassFunction L ℂ) ∉ X := by
        exact fun h ↦ (hXchar chi).mp h hker
      have hlhs : characterPairing (chi : ClassFunction L ℂ) lhs = 0 := by
        dsimp only [lhs]
        rw [pairing_finset_sum_right]
        apply Finset.sum_eq_zero
        intro xi hxi
        let xiI : IrreducibleCharacter L ℂ := ⟨xi, hXirr xi hxi⟩
        have hne : chi ≠ xiI := by
          intro heq
          apply hchiNotX
          rw [heq]
          exact hxi
        rw [characterPairing_smul_right,
          show characterPairing (chi : ClassFunction L ℂ) xi = 0 by
            simpa only [xiI] using
              (IrreducibleCharacter.characterPairing_eq_ite chi xiI).trans
                (if_neg hne), mul_zero]
      have hrhs : characterPairing (chi : ClassFunction L ℂ) rhs = 0 := by
        dsimp only [rhs]
        rw [characterPairing_smul_right,
          pairing_regularQuotientDifference Z chi, if_pos hker,
          mul_zero]
      rw [hlhs, hrhs]
    · have hchiX : (chi : ClassFunction L ℂ) ∈ X :=
        (hXchar chi).2 hker
      have hlhs : characterPairing (chi : ClassFunction L ℂ) lhs =
          (d (chi : ClassFunction L ℂ) : ℂ) := by
        dsimp only [lhs]
        rw [pairing_finset_sum_right]
        rw [Finset.sum_eq_single (chi : ClassFunction L ℂ)]
        · rw [characterPairing_smul_right,
            hXorth (chi : ClassFunction L ℂ) hchiX
              (chi : ClassFunction L ℂ) hchiX,
            if_pos rfl, mul_one]
        · intro xi hxi hne
          rw [characterPairing_smul_right,
            hXorth (chi : ClassFunction L ℂ) hchiX xi hxi,
            if_neg hne.symm, mul_zero]
        · exact fun h ↦ (h hchiX).elim
      have hrhs : characterPairing (chi : ClassFunction L ℂ) rhs =
          (d (chi : ClassFunction L ℂ) : ℂ) := by
        dsimp only [rhs]
        rw [characterPairing_smul_right,
          pairing_regularQuotientDifference Z chi, if_neg hker,
          hd (chi : ClassFunction L ℂ) hchiX]
        field_simp [hxi₁Ne]
      rw [hlhs, hrhs]
  have hzero : lhs - rhs = 0 :=
    classFunction_eq_zero_of_forall_irreducible_pairing_eq_zero
      (lhs - rhs) (fun chi ↦ by
        rw [pairing_sub_right, hpair chi, sub_self])
  exact sub_eq_zero.mp hzero

private theorem irreducible_commutator_le_translationKernel_of_degree_one
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) (hdegree : chi 1 = 1) :
    _root_.commutator Q ≤ ClassFunction.translationKernel
      (chi : ClassFunction Q ℂ) := by
  let rho : Representation ℂ Q chi.representation := chi.representation.ρ
  have hfinrank : Module.finrank ℂ chi.representation = 1 := by
    rw [IrreducibleCharacter.apply_one_eq_finrank] at hdegree
    exact_mod_cast hdegree
  let f : Q →* chi.representation ≃ₗ[ℂ] chi.representation :=
    representationLinearEquivHom rho
  have hcomm : _root_.commutator Q ≤ f.ker := by
    rw [commutator_eq_closure, Subgroup.closure_le]
    rintro q ⟨x, y, rfl⟩
    change f ⁅x, y⁆ = 1
    rw [map_commutatorElement,
      commutatorElement_eq_one_iff_commute, commute_iff_eq]
    apply LinearEquiv.toLinearMap_injective
    exact (endomorphisms_commute_of_finrank_eq_one hfinrank
      (rho x) (rho y)).eq
  rw [caseATranslationKernelIrreducibleCharacterComplex]
  intro q hq
  rw [MonoidHom.mem_ker]
  have hqOne := MonoidHom.mem_ker.mp (hcomm hq)
  apply LinearMap.ext
  intro v
  exact DFunLike.congr_fun hqOne v

/-! ## Explicit upstream context -/

/-- The genuine upstream data used by the Case-A calculation.

The regular-minus-quotient-regular identity at Coq line 829 is proved above
from `x_characterization`.  `constant_mod` is exactly the consequence of
`constant_irr_mod_TI_Sylow` after rewriting the Sylow cardinality as
`|K|`.  Neither field contains a coherence alignment or a rank-one target
decomposition. -/
structure CaseAAlignmentContext
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K Z : Subgroup L)
    (S : Set (ClassFunction L ℂ))
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ))
    (eta₁ : ClassFunction L ℂ) where
  kernel_normal : K.Normal
  central_le_kernel : Z ≤ K
  central_normal : Z.Normal
  central_ne_bot : Z ≠ ⊥
  central_le_center : Z ≤ centerWithin K
  central_le_commutator :
    Z ≤ (_root_.commutator K).map K.subtype
  subcoherent_data : subcoherent S tau R
  x_family : cfConjC_subset (↑X : Set (ClassFunction L ℂ)) S
  y_family : cfConjC_subset (↑Y : Set (ClassFunction L ℂ)) S
  y_disjoint_x :
    (↑Y : Set (ClassFunction L ℂ)) ⊆
      (↑X : Set (ClassFunction L ℂ))ᶜ
  x_irreducible : ∀ xi ∈ X, IsIrreducibleCharacter L ℂ xi
  x_induced : ∀ xi ∈ X, ∃ theta : IrreducibleCharacter K ℂ,
    xi = ClassFunction.induce K (theta : ClassFunction K ℂ)
  x_characterization : ∀ chi : IrreducibleCharacter L ℂ,
    ((chi : ClassFunction L ℂ) ∈ X ↔
      ¬ Z ≤ ClassFunction.translationKernel
        (chi : ClassFunction L ℂ))
  x_orthonormal : ∀ xi ∈ X, ∀ zeta ∈ X,
    characterPairing xi zeta = if xi = zeta then 1 else 0
  y_orthonormal : ∀ eta ∈ Y, ∀ zeta ∈ Y,
    characterPairing eta zeta = if eta = zeta then 1 else 0
  xy_orthogonal : ∀ xi ∈ X, ∀ eta ∈ Y,
    characterPairing xi eta = 0
  y_coherence : coherent_with
    (↑Y : Set (ClassFunction L ℂ))
    (nonidentitySet L) tau tau₁
  eta_mem : eta₁ ∈ Y
  y_degree : ∀ eta ∈ Y, eta 1 = (K.index : ℂ)
  y_card_two : 2 ≤ Y.card
  restriction : ClassFunction G ℂ →ₗ[ℂ] ClassFunction L ℂ
  restriction_virtual : ∀ f : ClassFunction G ℂ,
    ClassFunction.IsVirtual f →
      ClassFunction.IsVirtual (restriction f)
  frobenius_reciprocity : ∀ (f : ClassFunction L ℂ)
      (g : ClassFunction G ℂ),
    characterPairing (tau f) g =
      characterPairing f (restriction g)
  embed : L →* G
  embed_injective : Function.Injective embed
  restriction_apply : ∀ (f : ClassFunction G ℂ) (x : L),
    restriction f x = f (embed x)
  targetCentral : Subgroup G
  targetCentral_eq_map : Z.map embed = targetCentral
  constant_mod : ∀ (chi : IrreducibleCharacter G ℂ),
    (∀ {x y : G},
      x ∈ targetCentral → x ≠ 1 →
      y ∈ targetCentral → y ≠ 1 →
        chi x = chi y) →
    ∀ {x : G}, x ∈ targetCentral → x ≠ 1 →
      (∃ n : ℤ, chi x = (n : ℂ)) ∧
        IsIntegralModEq (Nat.card K : ℂ) (chi x) (chi 1)

/-! ## Virtual characters orthogonal to `X` kill the central section -/

private theorem virtual_orthogonal_constant_on_central
    {L : Type u} [Group L] [Fintype L]
    {Z : Subgroup L} {X : Finset (ClassFunction L ℂ)}
    (hXirr : ∀ xi ∈ X, IsIrreducibleCharacter L ℂ xi)
    (hXchar : ∀ chi : IrreducibleCharacter L ℂ,
      ((chi : ClassFunction L ℂ) ∈ X ↔
        ¬ Z ≤ ClassFunction.translationKernel
          (chi : ClassFunction L ℂ)))
    {f : ClassFunction L ℂ} (hf : ClassFunction.IsVirtual f)
    (horth : ∀ xi ∈ X, characterPairing f xi = 0) :
    ∀ z ∈ Z, f z = f 1 := by
  obtain ⟨v, rfl⟩ := hf
  intro z hzZ
  induction v using Finsupp.induction with
  | zero => simp
  | @single_add chi n v hchi hn ih =>
      have hchiNotX : (chi : ClassFunction L ℂ) ∉ X := by
        intro hchiX
        have hpair := horth (chi : ClassFunction L ℂ) hchiX
        have htail :
            characterPairing (VirtualCharacter.realize v)
              (chi : ClassFunction L ℂ) = 0 := by
          have hvchi : v chi = 0 := by
            simpa [Finsupp.mem_support_iff] using hchi
          rw [characterPairing_comm,
            VirtualCharacter.characterPairing_irreducible_realize,
            hvchi, Int.cast_zero]
        rw [map_add, VirtualCharacter.realize_single,
          characterPairing_add_left,
          characterPairing_smul_left,
          IrreducibleCharacter.characterPairing_self,
          htail, mul_one, add_zero] at hpair
        apply hn
        exact_mod_cast hpair
      have hker : Z ≤ ClassFunction.translationKernel
          (chi : ClassFunction L ℂ) := by
        exact Classical.byContradiction
          (fun h ↦ hchiNotX ((hXchar chi).2 h))
      have hchiValue : chi z = chi 1 := by
        have hzker := hker hzZ (1 : L)
        simpa using hzker
      have htailOrth : ∀ xi ∈ X,
          characterPairing (VirtualCharacter.realize v) xi = 0 := by
        intro xi hxi
        have hwhole := horth xi hxi
        have hchiXi :
            characterPairing (chi : ClassFunction L ℂ) xi = 0 := by
          let xiI : IrreducibleCharacter L ℂ := ⟨xi, hXirr xi hxi⟩
          have hne : chi ≠ xiI := by
            intro heq
            apply hchiNotX
            rw [heq]
            exact hxi
          simpa only [xiI] using
            (IrreducibleCharacter.characterPairing_eq_ite chi xiI).trans
              (if_neg hne)
        rw [map_add, VirtualCharacter.realize_single,
          characterPairing_add_left,
          characterPairing_smul_left, hchiXi, mul_zero,
          zero_add] at hwhole
        exact hwhole
      have htailValue := ih htailOrth
      simp only [map_add, VirtualCharacter.realize_single,
        ClassFunction.add_apply, ClassFunction.smul_apply, smul_eq_mul]
      rw [hchiValue, htailValue]

/-! ## The Case-A calculation -/

set_option maxHeartbeats 800000 in
/-- Faithful Lean form of the Case-A calculation in `PFsection6.v`,
lines 773--945. -/
theorem caseA_alignment
    {L G : Type u} [Group L] [Fintype L]
    [Group G] [Fintype G]
    (K Z : Subgroup L)
    (S : Set (ClassFunction L ℂ))
    (X Y : Finset (ClassFunction L ℂ))
    (tau tau₁ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (R : ClassFunction L ℂ → Finset (ClassFunction G ℂ))
    (eta₁ : ClassFunction L ℂ)
    (ctx : CaseAAlignmentContext K Z S X Y tau tau₁ R eta₁)
    (tau₂ : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (hcohX : coherent_with
      (↑X : Set (ClassFunction L ℂ))
      (nonidentitySet L) tau tau₂)
    (xi₁ : ClassFunction L ℂ) (hxi₁X : xi₁ ∈ X)
    (hdiv : ∀ xi ∈ X, ∃ d : ℕ,
      xi 1 = (d : ℂ) * xi₁ 1)
    (a : ℕ) (hdegree : xi₁ 1 = (a : ℂ) * eta₁ 1) :
    ∃ (tauX tauY :
        ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ),
      (tauX = tau₂ ∨
        (X.card ≤ 2 ∧ tauX = dual_iso tau₂)) ∧
      (tauY = tau₁ ∨
        (Y.card ≤ 2 ∧ tauY = dual_iso tau₁)) ∧
      tau (xi₁ - (a : ℂ) • eta₁) =
        tauX xi₁ - (a : ℂ) • tauY eta₁ := by
  classical
  letI : K.Normal := ctx.kernel_normal
  letI : Z.Normal := ctx.central_normal

  let d : ClassFunction L ℂ → ℕ := fun xi ↦
    if hxi : xi ∈ X then Classical.choose (hdiv xi hxi) else 0
  have hd (xi : ClassFunction L ℂ) (hxi : xi ∈ X) :
      xi 1 = (d xi : ℂ) * xi₁ 1 := by
    simpa only [d, dif_pos hxi] using
      Classical.choose_spec (hdiv xi hxi)
  have hxi₁DegreeNe : xi₁ 1 ≠ 0 :=
    ctx.subcoherent_data.degree_ne_zero xi₁
      (ctx.x_family.1 hxi₁X)
  have hdXi₁ : d xi₁ = 1 := by
    have hcast : (d xi₁ : ℂ) = 1 := by
      apply mul_right_cancel₀ hxi₁DegreeNe
      simpa using (hd xi₁ hxi₁X).symm
    exact_mod_cast hcast
  have heta₁Degree : eta₁ 1 = (K.index : ℂ) :=
    ctx.y_degree eta₁ ctx.eta_mem
  have heta₁DegreeNe : eta₁ 1 ≠ 0 := by
    rw [heta₁Degree]
    exact Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite
  have haNe : a ≠ 0 := by
    intro ha
    apply hxi₁DegreeNe
    rw [hdegree, ha, Nat.cast_zero, zero_mul]
  have haOne : a ≠ 1 := by
    intro ha
    obtain ⟨theta, hxiInd⟩ := ctx.x_induced xi₁ hxi₁X
    have hthetaDegree : theta 1 = 1 := by
      have hindexNe : (K.index : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite
      apply mul_left_cancel₀ hindexNe
      calc
        (K.index : ℂ) * theta 1 =
            (ClassFunction.induce K
              (theta : ClassFunction K ℂ)) 1 := by
          rw [ClassFunction.induce_one]
        _ = xi₁ 1 := congrArg (fun f : ClassFunction L ℂ ↦ f 1) hxiInd.symm
        _ = (K.index : ℂ) := by
          rw [hdegree, ha, Nat.cast_one, one_mul, heta₁Degree]
        _ = (K.index : ℂ) * 1 := by simp
    let D : Subgroup L := (_root_.commutator K).map K.subtype
    have hDK : D ≤ K := by
      rintro x ⟨k, _hk, rfl⟩
      exact k.property
    have hDnormal : D.Normal := by
      dsimp only [D]
      infer_instance
    letI : D.Normal := hDnormal
    have hDsubK : D.subgroupOf K = _root_.commutator K := by
      dsimp only [D]
      exact Subgroup.comap_map_eq_self_of_injective
        K.subtype_injective (_root_.commutator K)
    have hDtheta : D.subgroupOf K ≤
        ClassFunction.translationKernel
          (theta : ClassFunction K ℂ) := by
      rw [hDsubK]
      exact irreducible_commutator_le_translationKernel_of_degree_one
        theta hthetaDegree
    have hDinduced : D ≤ ClassFunction.translationKernel
        (ClassFunction.induce K
          (theta : ClassFunction K ℂ) : ClassFunction L ℂ) :=
      ClassFunction.le_translationKernel_induce D K hDK
        (theta : ClassFunction K ℂ) hDtheta
    let xiI : IrreducibleCharacter L ℂ :=
      ⟨xi₁, ctx.x_irreducible xi₁ hxi₁X⟩
    have hnotZ := (ctx.x_characterization xiI).mp (by
      simpa only [xiI] using hxi₁X)
    apply hnotZ
    have hZinduced := ctx.central_le_commutator.trans hDinduced
    simpa only [xiI, hxiInd] using hZinduced
  have haTwo : 2 ≤ a := by omega

  let psi₁ : ClassFunction L ℂ := xi₁ - (a : ℂ) • eta₁
  have hxi₁Span : xi₁ ∈ AddSubgroup.closure S :=
    AddSubgroup.subset_closure (ctx.x_family.1 hxi₁X)
  have heta₁Span : eta₁ ∈ AddSubgroup.closure S :=
    AddSubgroup.subset_closure (ctx.y_family.1 ctx.eta_mem)
  have hpsi₁Span : psi₁ ∈ AddSubgroup.closure S := by
    apply (AddSubgroup.closure S).sub_mem hxi₁Span
    simpa only [Nat.cast_smul_eq_nsmul] using
      (AddSubgroup.closure S).nsmul_mem heta₁Span a
  have hpsi₁Off :
      psi₁ ∈ ClassFunction.supportedOn (nonidentitySet L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro x hx
    have hxOne : x = 1 := by
      simpa [nonidentitySet] using not_not.mp hx
    subst x
    simp only [psi₁, ClassFunction.sub_apply,
      ClassFunction.smul_apply, smul_eq_mul]
    exact sub_eq_zero.mpr hdegree
  have hbetaVirtual : ClassFunction.IsVirtual (tau psi₁) :=
    ctx.subcoherent_data.tau_virtual psi₁ hpsi₁Span hpsi₁Off
  have heta₁TauVirtual : ClassFunction.IsVirtual (tau₁ eta₁) :=
    ctx.y_coherence.mapsToVirtual eta₁
      (AddSubgroup.subset_closure ctx.eta_mem)

  have horthTauXY : orthogonalFamilies
      (tau₂ '' AddSubgroup.closure
        (↑X : Set (ClassFunction L ℂ)))
      (tau₁ '' AddSubgroup.closure
        (↑Y : Set (ClassFunction L ℂ))) :=
    coherent_ortho ctx.subcoherent_data ctx.x_family hcohX
      ctx.y_family ctx.y_coherence ctx.y_disjoint_x

  let sumY : ClassFunction G ℂ := ∑ eta ∈ Y, tau₁ eta
  have hsumYVirtual : ClassFunction.IsVirtual sumY := by
    exact virtual_finset_sum Y (fun eta ↦ tau₁ eta)
      (fun eta heta ↦ ctx.y_coherence.mapsToVirtual eta
        (AddSubgroup.subset_closure heta))

  let proj : ClassFunction G ℂ :=
    ∑ eta ∈ Y,
      characterPairing (tau psi₁) (tau₁ eta) • tau₁ eta
  let X₁ : ClassFunction G ℂ := tau psi₁ - proj
  have hprojOrth : ∀ eta ∈ Y,
      characterPairing X₁ (tau₁ eta) = 0 := by
    intro eta heta
    dsimp only [X₁, proj]
    rw [pairing_sub_left, pairing_finset_sum_left]
    rw [Finset.sum_eq_single eta]
    · rw [characterPairing_smul_left,
        ctx.y_coherence.isometry eta
          (AddSubgroup.subset_closure heta)
          eta (AddSubgroup.subset_closure heta),
        ctx.y_orthonormal eta heta eta heta,
        if_pos rfl, mul_one, sub_self]
    · intro zeta hzeta hne
      rw [characterPairing_smul_left,
        ctx.y_coherence.isometry zeta
          (AddSubgroup.subset_closure hzeta)
          eta (AddSubgroup.subset_closure heta),
        ctx.y_orthonormal zeta hzeta eta heta,
        if_neg hne, mul_zero]
    · exact fun h ↦ (h heta).elim
  have hprojVirtual : ClassFunction.IsVirtual proj := by
    exact virtual_finset_sum Y
      (fun eta ↦
        characterPairing (tau psi₁) (tau₁ eta) • tau₁ eta)
      (fun eta heta ↦ by
        obtain ⟨n, hn⟩ := virtual_pairing_eq_int hbetaVirtual
          (ctx.y_coherence.mapsToVirtual eta
            (AddSubgroup.subset_closure heta))
        rw [hn]
        exact virtual_intCast_smul
          (ctx.y_coherence.mapsToVirtual eta
            (AddSubgroup.subset_closure heta)) n)
  have hX₁Virtual : ClassFunction.IsVirtual X₁ :=
    hbetaVirtual.sub hprojVirtual

  obtain ⟨r, hr⟩ :=
    virtual_pairing_eq_int hbetaVirtual heta₁TauVirtual
  let b : ℤ := r + a
  have hbPair :
      characterPairing (tau psi₁) (tau₁ eta₁) =
        (b : ℂ) - (a : ℂ) := by
    dsimp only [b]
    rw [hr]
    push_cast
    ring

  have hcoefficient (eta : ClassFunction L ℂ) (heta : eta ∈ Y) :
      characterPairing (tau psi₁) (tau₁ eta) =
        if eta = eta₁ then (b : ℂ) - (a : ℂ) else (b : ℂ) := by
    by_cases heq : eta = eta₁
    · subst eta
      rw [if_pos rfl, hbPair]
    · rw [if_neg heq]
      have hdiffSpan : eta - eta₁ ∈
          AddSubgroup.closure (↑Y : Set (ClassFunction L ℂ)) :=
        (AddSubgroup.closure
          (↑Y : Set (ClassFunction L ℂ))).sub_mem
          (AddSubgroup.subset_closure heta)
          (AddSubgroup.subset_closure ctx.eta_mem)
      have hdiffSpanS : eta - eta₁ ∈ AddSubgroup.closure S :=
        (AddSubgroup.closure_mono ctx.y_family.1) hdiffSpan
      have hdiffOff : eta - eta₁ ∈
          ClassFunction.supportedOn (nonidentitySet L) := by
        rw [ClassFunction.mem_supportedOn_iff]
        intro x hx
        have hxOne : x = 1 := by
          simpa [nonidentitySet] using not_not.mp hx
        subst x
        simp only [ClassFunction.sub_apply]
        rw [ctx.y_degree eta heta,
          ctx.y_degree eta₁ ctx.eta_mem, sub_self]
      have hagree := ctx.y_coherence.agrees
        (eta - eta₁) hdiffSpan hdiffOff
      have hpairDiff :
          characterPairing (tau psi₁) (tau₁ (eta - eta₁)) =
            (a : ℂ) := by
        rw [hagree]
        rw [ctx.subcoherent_data.tau_isometry psi₁ hpsi₁Span
          hpsi₁Off (eta - eta₁) hdiffSpanS hdiffOff]
        dsimp only [psi₁]
        rw [pairing_sub_left, pairing_sub_right,
          pairing_sub_right, characterPairing_smul_left,
          characterPairing_smul_left,
          ctx.xy_orthogonal xi₁ hxi₁X eta heta,
          ctx.xy_orthogonal xi₁ hxi₁X eta₁ ctx.eta_mem,
          characterPairing_comm eta₁ eta,
          ctx.y_orthonormal eta heta eta₁ ctx.eta_mem,
          if_neg heq,
          ctx.y_orthonormal eta₁ ctx.eta_mem eta₁ ctx.eta_mem,
          if_pos rfl]
        ring
      rw [show tau₁ (eta - eta₁) = tau₁ eta - tau₁ eta₁ by
          exact map_sub tau₁ eta eta₁,
        pairing_sub_right, hbPair] at hpairDiff
      linear_combination hpairDiff

  have hprojFormula :
      proj = (b : ℂ) • sumY - (a : ℂ) • tau₁ eta₁ := by
    dsimp only [proj, sumY]
    have hsplitLeft :
        (∑ eta ∈ Y,
            characterPairing (tau psi₁) (tau₁ eta) • tau₁ eta) =
          characterPairing (tau psi₁) (tau₁ eta₁) • tau₁ eta₁ +
            ∑ eta ∈ Y \ {eta₁},
              characterPairing (tau psi₁) (tau₁ eta) • tau₁ eta := by
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem ctx.eta_mem]
    have hsplitRight :
        (∑ eta ∈ Y, tau₁ eta) =
          tau₁ eta₁ + ∑ eta ∈ Y \ {eta₁}, tau₁ eta := by
      rw [Finset.sum_eq_add_sum_sdiff_singleton_of_mem ctx.eta_mem]
    have hrest :
        ∑ eta ∈ Y \ {eta₁},
            characterPairing (tau psi₁) (tau₁ eta) • tau₁ eta =
          (b : ℂ) • ∑ eta ∈ Y \ {eta₁}, tau₁ eta := by
      rw [Finset.smul_sum]
      apply Finset.sum_congr rfl
      intro eta heta
      have hetaY : eta ∈ Y := (Finset.mem_sdiff.mp heta).1
      have hetaNe : eta ≠ eta₁ := by
        simpa using (Finset.mem_sdiff.mp heta).2
      rw [hcoefficient eta hetaY, if_neg hetaNe]
    rw [hsplitLeft, hsplitRight,
      hcoefficient eta₁ ctx.eta_mem, if_pos rfl, hrest]
    module
  have hbetaDecomp :
      tau psi₁ = X₁ - (a : ℂ) • tau₁ eta₁ +
        (b : ℂ) • sumY := by
    dsimp only [X₁]
    rw [hprojFormula]
    module

  let psi : ClassFunction L ℂ := ctx.restriction (tau₁ eta₁)
  have hpsiVirtual : ClassFunction.IsVirtual psi :=
    ctx.restriction_virtual (tau₁ eta₁) heta₁TauVirtual
  obtain ⟨c, hc⟩ := virtual_pairing_eq_int hpsiVirtual
    (ctx.subcoherent_data.source_virtual xi₁
      (ctx.x_family.1 hxi₁X))
  let sumXd : ClassFunction L ℂ :=
    ∑ xi ∈ X, (d xi : ℂ) • xi
  let xi₂ : ClassFunction L ℂ := psi - (c : ℂ) • sumXd
  have hxi₂Virtual : ClassFunction.IsVirtual xi₂ := by
    have hsumXdVirtual : ClassFunction.IsVirtual sumXd := by
      exact virtual_finset_sum X
        (fun xi ↦ (d xi : ℂ) • xi)
        (fun xi hxi ↦ virtual_natCast_smul
          (ctx.subcoherent_data.source_virtual xi
            (ctx.x_family.1 hxi)) (d xi))
    exact hpsiVirtual.sub (virtual_intCast_smul hsumXdVirtual c)
  have hxi₂Orth : ∀ xi ∈ X,
      characterPairing xi₂ xi = 0 := by
    intro xi hxi
    have hdiffSpan : xi - (d xi : ℂ) • xi₁ ∈
        AddSubgroup.closure (↑X : Set (ClassFunction L ℂ)) := by
      apply (AddSubgroup.closure
        (↑X : Set (ClassFunction L ℂ))).sub_mem
        (AddSubgroup.subset_closure hxi)
      simpa only [Nat.cast_smul_eq_nsmul] using
        (AddSubgroup.closure
          (↑X : Set (ClassFunction L ℂ))).nsmul_mem
            (AddSubgroup.subset_closure hxi₁X) (d xi)
    have hdiffOff : xi - (d xi : ℂ) • xi₁ ∈
        ClassFunction.supportedOn (nonidentitySet L) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      have hxOne : x = 1 := by
        simpa [nonidentitySet] using not_not.mp hx
      subst x
      simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
        smul_eq_mul, hd xi hxi, sub_self]
    have hagree := hcohX.agrees
      (xi - (d xi : ℂ) • xi₁) hdiffSpan hdiffOff
    have htargetOrth :
        characterPairing
          (tau₂ (xi - (d xi : ℂ) • xi₁))
          (tau₁ eta₁) = 0 := by
      exact horthTauXY
        (tau₂ (xi - (d xi : ℂ) • xi₁))
        ⟨xi - (d xi : ℂ) • xi₁, hdiffSpan, rfl⟩
        (tau₁ eta₁)
        ⟨eta₁, AddSubgroup.subset_closure ctx.eta_mem, rfl⟩
    rw [hagree] at htargetOrth
    have hresDiff :
        characterPairing
          (xi - (d xi : ℂ) • xi₁) psi = 0 := by
      rw [← ctx.frobenius_reciprocity]
      exact htargetOrth
    have hpsiPair : characterPairing psi xi = (d xi : ℂ) * (c : ℂ) := by
      rw [pairing_sub_left, characterPairing_smul_left,
        characterPairing_comm xi psi,
        characterPairing_comm xi₁ psi, hc] at hresDiff
      linear_combination hresDiff
    dsimp only [xi₂]
    rw [pairing_sub_left, hpsiPair,
      characterPairing_smul_left, pairing_finset_sum_left]
    rw [Finset.sum_eq_single xi]
    · rw [characterPairing_smul_left,
        ctx.x_orthonormal xi hxi xi hxi,
        if_pos rfl, mul_one]
      ring
    · intro zeta hzeta hne
      rw [characterPairing_smul_left,
        ctx.x_orthonormal zeta hzeta xi hxi,
        if_neg hne, mul_zero]
    · exact fun h ↦ (h hxi).elim
  have hxi₂Constant : ∀ z ∈ Z, xi₂ z = xi₂ 1 :=
    virtual_orthogonal_constant_on_central ctx.x_irreducible
      ctx.x_characterization hxi₂Virtual hxi₂Orth

  have hsumXdFormula :
      sumXd = (xi₁ 1)⁻¹ • regularQuotientDifference Z := by
    exact regular_projection_from_characterization Z X
      ctx.x_characterization ctx.x_irreducible ctx.x_orthonormal
      xi₁ hxi₁DegreeNe d hd
  have htauEtaCentral (z : L) (hzZ : z ∈ Z) (hz : z ≠ 1) :
      tau₁ eta₁ (ctx.embed z) - tau₁ eta₁ 1 =
        -((c : ℂ) * (Nat.card K : ℂ) / (a : ℂ)) := by
    have hpsiZ : psi z - psi 1 =
        (c : ℂ) * (sumXd z - sumXd 1) := by
      dsimp only [xi₂] at hxi₂Constant
      have hconst := hxi₂Constant z hzZ
      rw [ClassFunction.sub_apply, ClassFunction.smul_apply,
        smul_eq_mul, ClassFunction.sub_apply,
        ClassFunction.smul_apply, smul_eq_mul] at hconst
      linear_combination hconst
    have hsumDiff : sumXd z - sumXd 1 =
        -(Nat.card L : ℂ) / xi₁ 1 := by
      rw [hsumXdFormula]
      simp only [ClassFunction.smul_apply, smul_eq_mul]
      rw [← mul_sub,
        regularQuotientDifference_sub_one_of_mem_ne_one Z hzZ hz]
      field_simp [hxi₁DegreeNe]
    rw [ctx.restriction_apply, ctx.restriction_apply] at hpsiZ
    simp only [map_one] at hpsiZ
    rw [hsumDiff] at hpsiZ
    have hcard : Nat.card L = Nat.card K * K.index := by
      exact K.card_mul_index.symm
    rw [hcard, hdegree, heta₁Degree] at hpsiZ
    push_cast at hpsiZ
    field_simp [Nat.cast_ne_zero.mpr haNe,
      Nat.cast_ne_zero.mpr K.index_ne_zero_of_finite] at hpsiZ ⊢
    linear_combination hpsiZ

  obtain ⟨chi, epsilon, hepsilon, htauEtaSigned⟩ :=
    exists_signed_irreducible_of_virtual_pairing_one heta₁TauVirtual
      (ctx.y_coherence.isometry eta₁
        (AddSubgroup.subset_closure ctx.eta_mem)
        eta₁ (AddSubgroup.subset_closure ctx.eta_mem) |>.trans
          (ctx.y_orthonormal eta₁ ctx.eta_mem eta₁ ctx.eta_mem |>.trans
            (if_pos rfl)))
  have hchiConstant : ∀ {x y : G},
      x ∈ ctx.targetCentral → x ≠ 1 →
      y ∈ ctx.targetCentral → y ≠ 1 →
        chi x = chi y := by
    intro x y hxZ hx hyZ hy
    rw [← ctx.targetCentral_eq_map] at hxZ hyZ
    rcases hxZ with ⟨zx, hzxZ, rfl⟩
    rcases hyZ with ⟨zy, hzyZ, rfl⟩
    have hzx : zx ≠ 1 := by
      intro h
      apply hx
      rw [h, map_one]
    have hzy : zy ≠ 1 := by
      intro h
      apply hy
      rw [h, map_one]
    have hxFormula := htauEtaCentral zx hzxZ hzx
    have hyFormula := htauEtaCentral zy hzyZ hzy
    rw [htauEtaSigned, ClassFunction.smul_apply,
      ClassFunction.smul_apply, smul_eq_mul, smul_eq_mul] at hxFormula hyFormula
    have hepsilonC : (epsilon : ℂ) ≠ 0 :=
      Int.cast_ne_zero.mpr (isSign_ne_zero hepsilon)
    apply (mul_left_cancel₀ hepsilonC)
    linear_combination hxFormula - hyFormula

  obtain ⟨z, hz⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp ctx.central_ne_bot
  have hzEmbed : ctx.embed (z : L) ≠ 1 := by
    intro h
    apply hz
    apply Subtype.ext
    apply ctx.embed_injective
    simpa using h
  have hzTarget : ctx.embed (z : L) ∈ ctx.targetCentral := by
    rw [← ctx.targetCentral_eq_map]
    exact Subgroup.mem_map_of_mem ctx.embed z.property
  obtain ⟨_, hmod⟩ :=
    ctx.constant_mod chi hchiConstant hzTarget hzEmbed
  obtain ⟨t, htIntegral, ht⟩ := hmod
  have hcentralAtZ := htauEtaCentral (z : L) z.property
    (fun h ↦ hz (Subtype.ext h))
  have hsignAtZ := congrArg
    (fun f : ClassFunction G ℂ ↦
      f (ctx.embed (z : L)) - f 1) htauEtaSigned
  simp only [ClassFunction.smul_apply, smul_eq_mul] at hsignAtZ
  have hfactor :
      -((c : ℂ) / (a : ℂ)) = (epsilon : ℂ) * t := by
    have hcardK : (Nat.card K : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    apply (mul_right_cancel₀ hcardK)
    calc
      (-((c : ℂ) / (a : ℂ))) * (Nat.card K : ℂ) =
          -((c : ℂ) * (Nat.card K : ℂ) / (a : ℂ)) := by ring
      _ = tau₁ eta₁ (ctx.embed (z : L)) - tau₁ eta₁ 1 :=
        hcentralAtZ.symm
      _ = (epsilon : ℂ) * (chi (ctx.embed (z : L)) - chi 1) := by
        linear_combination hsignAtZ
      _ = (epsilon : ℂ) * ((Nat.card K : ℂ) * t) := by rw [ht]
      _ = ((epsilon : ℂ) * t) * (Nat.card K : ℂ) := by ring
  have hcDivIntegral : IsIntegral ℤ ((c : ℂ) / (a : ℂ)) := by
    have hrhs : IsIntegral ℤ ((epsilon : ℂ) * t) :=
      (isIntegral_intCast epsilon).mul htIntegral
    have hneg : IsIntegral ℤ (-((c : ℂ) / (a : ℂ))) := by
      rw [hfactor]
      exact hrhs
    simpa using hneg.neg
  have hcDivRat : ∃ q : ℚ,
      (c : ℂ) / (a : ℂ) = (q : ℂ) := by
    refine ⟨(c : ℚ) / (a : ℚ), ?_⟩
    norm_cast
  obtain ⟨q₀, hq₀⟩ :=
    (IsIntegral.exists_int_iff_exists_rat hcDivIntegral).mp hcDivRat
  have hcFactor : (c : ℂ) = (a : ℂ) * (q₀ : ℂ) := by
    field_simp [Nat.cast_ne_zero.mpr haNe] at hq₀ ⊢
    exact hq₀

  have hpairPsiPsi₁ : characterPairing psi psi₁ =
      (b : ℂ) - (a : ℂ) := by
    rw [characterPairing_comm]
    dsimp only [psi]
    rw [← ctx.frobenius_reciprocity psi₁ (tau₁ eta₁), hbPair]
  obtain ⟨s, hs⟩ := virtual_pairing_eq_int hpsiVirtual
    (ctx.subcoherent_data.source_virtual eta₁
      (ctx.y_family.1 ctx.eta_mem))
  have hbcCast : (b : ℂ) - (c : ℂ) =
      (a : ℂ) * ((1 : ℂ) - (s : ℂ)) := by
    dsimp only [psi₁] at hpairPsiPsi₁
    rw [pairing_sub_right, hc,
      characterPairing_smul_right, hs] at hpairPsiPsi₁
    linear_combination -hpairPsiPsi₁
  have hbc : b - c = (a : ℤ) * (1 - s) := by
    apply Int.cast_injective (α := ℂ)
    push_cast
    exact hbcCast
  let q : ℤ := q₀ + (1 - s)
  have hbFactor : b = (a : ℤ) * q := by
    have hcInt : c = (a : ℤ) * q₀ := by
      apply Int.cast_injective (α := ℂ)
      push_cast
      exact hcFactor
    have hbEq : b = c + (a : ℤ) * (1 - s) := by omega
    rw [hbEq, hcInt]
    dsimp only [q]
    ring

  have hpsi₁Norm : characterPairing psi₁ psi₁ =
      (1 + a ^ 2 : ℕ) := by
    dsimp only [psi₁]
    rw [pairing_sub_left, pairing_sub_right, pairing_sub_right,
      characterPairing_smul_left, characterPairing_smul_left,
      characterPairing_smul_right, characterPairing_smul_right,
      ctx.xy_orthogonal xi₁ hxi₁X eta₁ ctx.eta_mem,
      characterPairing_comm eta₁ xi₁,
      ctx.xy_orthogonal xi₁ hxi₁X eta₁ ctx.eta_mem,
      ctx.x_orthonormal xi₁ hxi₁X xi₁ hxi₁X,
      if_pos rfl,
      ctx.y_orthonormal eta₁ ctx.eta_mem eta₁ ctx.eta_mem,
      if_pos rfl]
    push_cast
    ring
  have hbetaNorm : characterPairing (tau psi₁) (tau psi₁) =
      (1 + a ^ 2 : ℕ) := by
    rw [ctx.subcoherent_data.tau_isometry psi₁ hpsi₁Span hpsi₁Off
      psi₁ hpsi₁Span hpsi₁Off, hpsi₁Norm]

  have hsumYPair : characterPairing sumY sumY = (Y.card : ℂ) := by
    dsimp only [sumY]
    rw [pairing_finset_sum_left]
    calc
      (∑ eta ∈ Y,
          characterPairing (tau₁ eta) (∑ zeta ∈ Y, tau₁ zeta)) =
          ∑ _eta ∈ Y, (1 : ℂ) := by
        apply Finset.sum_congr rfl
        intro eta heta
        rw [pairing_finset_sum_right]
        rw [Finset.sum_eq_single eta]
        · rw [ctx.y_coherence.isometry eta
              (AddSubgroup.subset_closure heta)
              eta (AddSubgroup.subset_closure heta),
            ctx.y_orthonormal eta heta eta heta, if_pos rfl]
        · intro zeta hzeta hne
          rw [ctx.y_coherence.isometry eta
              (AddSubgroup.subset_closure heta)
              zeta (AddSubgroup.subset_closure hzeta),
            ctx.y_orthonormal eta heta zeta hzeta,
            if_neg hne.symm]
        · exact fun h ↦ (h heta).elim
      _ = (Y.card : ℂ) := by simp
  have hsumYEta : characterPairing sumY (tau₁ eta₁) = 1 := by
    dsimp only [sumY]
    rw [pairing_finset_sum_left, Finset.sum_eq_single eta₁]
    · rw [ctx.y_coherence.isometry eta₁
          (AddSubgroup.subset_closure ctx.eta_mem)
          eta₁ (AddSubgroup.subset_closure ctx.eta_mem),
        ctx.y_orthonormal eta₁ ctx.eta_mem eta₁ ctx.eta_mem,
        if_pos rfl]
    · intro eta heta hne
      rw [ctx.y_coherence.isometry eta
          (AddSubgroup.subset_closure heta)
          eta₁ (AddSubgroup.subset_closure ctx.eta_mem),
        ctx.y_orthonormal eta heta eta₁ ctx.eta_mem,
        if_neg hne]
    · exact fun h ↦ (h ctx.eta_mem).elim
  have hetaSumY : characterPairing (tau₁ eta₁) sumY = 1 := by
    rw [characterPairing_comm, hsumYEta]
  have hetaTauNorm :
      characterPairing (tau₁ eta₁) (tau₁ eta₁) = 1 := by
    exact ctx.y_coherence.isometry eta₁
      (AddSubgroup.subset_closure ctx.eta_mem)
      eta₁ (AddSubgroup.subset_closure ctx.eta_mem) |>.trans
        (ctx.y_orthonormal eta₁ ctx.eta_mem eta₁ ctx.eta_mem |>.trans
          (if_pos rfl))
  have hX₁SumY : characterPairing X₁ sumY = 0 := by
    dsimp only [sumY]
    rw [pairing_finset_sum_right]
    exact Finset.sum_eq_zero fun eta heta ↦ hprojOrth eta heta
  have hsumYX₁ : characterPairing sumY X₁ = 0 := by
    rw [characterPairing_comm, hX₁SumY]
  have hX₁Eta : characterPairing X₁ (tau₁ eta₁) = 0 :=
    hprojOrth eta₁ ctx.eta_mem
  have hEtaX₁ : characterPairing (tau₁ eta₁) X₁ = 0 := by
    rw [characterPairing_comm, hX₁Eta]

  obtain ⟨nX₁, hnX₁⟩ := virtual_self_pairing_eq_nat hX₁Virtual
  have hnormEquation :
      (1 + a ^ 2 : ℤ) = (nX₁ : ℤ) +
        (a : ℤ) ^ 2 *
          (q ^ 2 * (Y.card : ℤ) + 1 - 2 * q) := by
    have hnormC :
        characterPairing
            (X₁ - (a : ℂ) • tau₁ eta₁ + (b : ℂ) • sumY)
            (X₁ - (a : ℂ) • tau₁ eta₁ + (b : ℂ) • sumY) =
          (1 + a ^ 2 : ℕ) := by
      calc
        _ = characterPairing (tau psi₁) (tau psi₁) :=
          (congrArg₂
            (fun f g : ClassFunction G ℂ ↦ characterPairing f g)
            hbetaDecomp hbetaDecomp).symm
        _ = (1 + a ^ 2 : ℕ) := hbetaNorm
    simp only [characterPairing_add_left, characterPairing_add_right,
      pairing_sub_left, pairing_sub_right,
      characterPairing_smul_left, characterPairing_smul_right,
      hnX₁, hX₁Eta, hEtaX₁, hX₁SumY, hsumYX₁,
      hetaTauNorm, hsumYPair, hsumYEta, hetaSumY] at hnormC
    rw [show (b : ℂ) = (a : ℂ) * (q : ℂ) by
      exact_mod_cast hbFactor] at hnormC
    have hcomplex :
        (1 : ℂ) + (a : ℂ) ^ 2 =
          (nX₁ : ℂ) + (a : ℂ) ^ 2 *
            ((q : ℂ) ^ 2 * (Y.card : ℂ) + 1 - 2 * (q : ℂ)) := by
      calc
        (1 : ℂ) + (a : ℂ) ^ 2 = ((1 + a ^ 2 : ℕ) : ℂ) := by
          push_cast
          ring
        _ = _ := hnormC.symm
        _ = (nX₁ : ℂ) + (a : ℂ) ^ 2 *
            ((q : ℂ) ^ 2 * (Y.card : ℂ) + 1 - 2 * (q : ℂ)) := by
          ring
    exact_mod_cast hcomplex
  have hsmall : q ^ 2 * (Y.card : ℤ) + 1 - 2 * q < 2 := by
    have hnXnonneg : (0 : ℤ) ≤ nX₁ := by omega
    have haSq : (1 : ℤ) < (a : ℤ) ^ 2 := by
      exact_mod_cast (show 1 < a ^ 2 by nlinarith)
    by_contra hnot
    let w : ℤ := q ^ 2 * (Y.card : ℤ) + 1 - 2 * q
    have htwo : (2 : ℤ) ≤ w := by
      dsimp only [w]
      omega
    have hprod : (a : ℤ) ^ 2 * 2 ≤ (a : ℤ) ^ 2 * w :=
      mul_le_mul_of_nonneg_left htwo (sq_nonneg (a : ℤ))
    have hlarge : 2 * (a : ℤ) ^ 2 ≤
        (nX₁ : ℤ) + (a : ℤ) ^ 2 * w := by
      calc
        2 * (a : ℤ) ^ 2 = (a : ℤ) ^ 2 * 2 := by ring
        _ ≤ (a : ℤ) ^ 2 * w := hprod
        _ ≤ (nX₁ : ℤ) + (a : ℤ) ^ 2 * w := by omega
    have heq : (1 + a ^ 2 : ℤ) =
        (nX₁ : ℤ) + (a : ℤ) ^ 2 * w := by
      simpa only [w] using hnormEquation
    rw [← heq] at hlarge
    omega
  obtain ⟨tauY, htauY,
      hbetaCanonical : tau psi₁ =
        X₁ - (a : ℂ) • tauY eta₁⟩ :
      ∃ tauY : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ,
        (tauY = tau₁ ∨
          (Y.card ≤ 2 ∧ tauY = dual_iso tau₁)) ∧
        tau psi₁ = X₁ - (a : ℂ) • tauY eta₁ := by
    rcases integer_norm_coefficient_dichotomy
        Y.card q ctx.y_card_two hsmall with hqZero | ⟨hqOne, hYcard⟩
    · refine ⟨tau₁, Or.inl rfl, ?_⟩
      rw [hbetaDecomp, show (b : ℂ) = 0 by
        rw [hbFactor, hqZero]; norm_num]
      simp
    · refine ⟨dual_iso tau₁,
        Or.inr ⟨by omega, rfl⟩, ?_⟩
      have hYeq : Y = {eta₁,
          ClassFunction.inverseLinear eta₁} := by
        have hinvMem := ctx.y_family.2 eta₁ ctx.eta_mem
        have htwoSubset :
            ({eta₁, ClassFunction.inverseLinear eta₁} :
              Finset (ClassFunction L ℂ)) ⊆ Y := by
          intro zeta hzeta
          simp only [Finset.mem_insert, Finset.mem_singleton] at hzeta
          exact hzeta.elim (fun h ↦ h ▸ ctx.eta_mem)
            (fun h ↦ h ▸ hinvMem)
        have hcardPair :
            ({eta₁, ClassFunction.inverseLinear eta₁} :
              Finset (ClassFunction L ℂ)).card = 2 := by
          exact Finset.card_pair
            (ctx.subcoherent_data.inverse_ne eta₁
              (ctx.y_family.1 ctx.eta_mem)).symm
        exact (Finset.eq_of_subset_of_card_le htwoSubset
          (by rw [hYcard, hcardPair])).symm
      have hsumYTwo : sumY = tau₁ eta₁ +
          tau₁ (ClassFunction.inverseLinear eta₁) := by
        dsimp only [sumY]
        rw [hYeq]
        rw [Finset.sum_insert (by
          simpa using (ctx.subcoherent_data.inverse_ne eta₁
            (ctx.y_family.1 ctx.eta_mem)).symm),
          Finset.sum_singleton]
      rw [hbetaDecomp,
        show (b : ℂ) = (a : ℂ) by
          rw [hbFactor, hqOne]; norm_num,
        hsumYTwo, dual_iso_apply]
      module

  have htauYcoh : coherent_with
      (↑Y : Set (ClassFunction L ℂ))
      (nonidentitySet L) tau tauY := by
    rcases htauY with rfl | ⟨hcard, rfl⟩
    · exact ctx.y_coherence
    · have hncard :
          (↑Y : Set (ClassFunction L ℂ)).ncard ≤ 2 := by
        simpa using hcard
      exact dual_coherence
        (subset_subcoherent ctx.subcoherent_data ctx.y_family)
        ctx.y_coherence hncard

  have hX₁Norm : characterPairing X₁ X₁ = 1 := by
    have hnormC :
        characterPairing
            (X₁ - (a : ℂ) • tauY eta₁)
            (X₁ - (a : ℂ) • tauY eta₁) =
          (1 + a ^ 2 : ℕ) := by
      calc
        _ = characterPairing (tau psi₁) (tau psi₁) :=
          (congrArg₂
            (fun f g : ClassFunction G ℂ ↦ characterPairing f g)
            hbetaCanonical hbetaCanonical).symm
        _ = (1 + a ^ 2 : ℕ) := hbetaNorm
    have hX₁TauY : characterPairing X₁ (tauY eta₁) = 0 := by
      rcases htauY with rfl | ⟨_, rfl⟩
      · exact hX₁Eta
      · rw [dual_iso_apply, pairing_neg_right]
        exact neg_eq_zero.mpr
          (hprojOrth (ClassFunction.inverseLinear eta₁)
            (ctx.y_family.2 eta₁ ctx.eta_mem))
    have hTauYX₁ : characterPairing (tauY eta₁) X₁ = 0 := by
      rw [characterPairing_comm, hX₁TauY]
    have hTauYNorm :
        characterPairing (tauY eta₁) (tauY eta₁) = 1 := by
      exact htauYcoh.isometry eta₁
        (AddSubgroup.subset_closure ctx.eta_mem)
        eta₁ (AddSubgroup.subset_closure ctx.eta_mem) |>.trans
          (ctx.y_orthonormal eta₁ ctx.eta_mem eta₁ ctx.eta_mem |>.trans
            (if_pos rfl))
    simp only [pairing_sub_left, pairing_sub_right,
      characterPairing_smul_left, characterPairing_smul_right,
      hX₁TauY, hTauYX₁, hTauYNorm] at hnormC
    push_cast at hnormC
    linear_combination hnormC

  have hX₁Signed :=
    exists_signed_irreducible_of_virtual_pairing_one hX₁Virtual hX₁Norm
  have htau₂Signed (xi : ClassFunction L ℂ) (hxi : xi ∈ X) :
      ∃ (chi : IrreducibleCharacter G ℂ) (epsilon : ℤ),
        IsSign epsilon ∧
          tau₂ xi = (epsilon : ℂ) • (chi : ClassFunction G ℂ) := by
    apply exists_signed_irreducible_of_virtual_pairing_one
    · exact hcohX.mapsToVirtual xi (AddSubgroup.subset_closure hxi)
    · exact hcohX.isometry xi (AddSubgroup.subset_closure hxi)
        xi (AddSubgroup.subset_closure hxi) |>.trans
          (ctx.x_orthonormal xi hxi xi hxi |>.trans (if_pos rfl))

  have hcompare (xi : ClassFunction L ℂ) (hxi : xi ∈ X) (hne : xi ≠ xi₁) :
      characterPairing
          ((d xi : ℂ) • tau₂ xi₁ - tau₂ xi) X₁ =
        (d xi : ℂ) := by
    have hdiffSpan : xi - (d xi : ℂ) • xi₁ ∈
        AddSubgroup.closure (↑X : Set (ClassFunction L ℂ)) := by
      apply (AddSubgroup.closure
        (↑X : Set (ClassFunction L ℂ))).sub_mem
        (AddSubgroup.subset_closure hxi)
      simpa only [Nat.cast_smul_eq_nsmul] using
        (AddSubgroup.closure
          (↑X : Set (ClassFunction L ℂ))).nsmul_mem
            (AddSubgroup.subset_closure hxi₁X) (d xi)
    have hdiffOff : xi - (d xi : ℂ) • xi₁ ∈
        ClassFunction.supportedOn (nonidentitySet L) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      have hxOne : x = 1 := by
        simpa [nonidentitySet] using not_not.mp hx
      subst x
      simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
        smul_eq_mul, hd xi hxi, sub_self]
    have hagree := hcohX.agrees
      (xi - (d xi : ℂ) • xi₁) hdiffSpan hdiffOff
    have horthY : characterPairing
        (tau₂ (xi - (d xi : ℂ) • xi₁))
        (tauY eta₁) = 0 := by
      rcases htauY with htauYeq | ⟨_, htauYeq⟩
      · rw [htauYeq]
        exact horthTauXY
          (tau₂ (xi - (d xi : ℂ) • xi₁))
          ⟨xi - (d xi : ℂ) • xi₁, hdiffSpan, rfl⟩
          (tau₁ eta₁)
          ⟨eta₁, AddSubgroup.subset_closure ctx.eta_mem, rfl⟩
      · rw [htauYeq, dual_iso_apply, pairing_neg_right]
        apply neg_eq_zero.mpr
        exact horthTauXY
          (tau₂ (xi - (d xi : ℂ) • xi₁))
          ⟨xi - (d xi : ℂ) • xi₁, hdiffSpan, rfl⟩
          (tau₁ (ClassFunction.inverseLinear eta₁))
          ⟨ClassFunction.inverseLinear eta₁,
            AddSubgroup.subset_closure
              (ctx.y_family.2 eta₁ ctx.eta_mem), rfl⟩
    rw [hagree] at horthY
    have hpairBeta : characterPairing
        (tau (xi - (d xi : ℂ) • xi₁)) (tau psi₁) =
        characterPairing
          (xi - (d xi : ℂ) • xi₁) psi₁ := by
      have hdiffSpanS := (AddSubgroup.closure_mono ctx.x_family.1) hdiffSpan
      exact ctx.subcoherent_data.tau_isometry
        (xi - (d xi : ℂ) • xi₁) hdiffSpanS hdiffOff
        psi₁ hpsi₁Span hpsi₁Off
    rw [hbetaCanonical, pairing_sub_right,
      characterPairing_smul_right, horthY, mul_zero, sub_zero] at hpairBeta
    rw [map_sub, map_smul] at hpairBeta
    have hagreeExpanded := hagree
    rw [map_sub, map_smul, map_sub, map_smul] at hagreeExpanded
    rw [← hagreeExpanded] at hpairBeta
    rw [show (d xi : ℂ) • tau₂ xi₁ - tau₂ xi =
          -(tau₂ xi - (d xi : ℂ) • tau₂ xi₁) by module,
      pairing_neg_left, hpairBeta]
    dsimp only [psi₁]
    rw [pairing_sub_left, pairing_sub_right,
      pairing_sub_right, characterPairing_smul_left,
      characterPairing_smul_left, characterPairing_smul_right,
      characterPairing_smul_right,
      ctx.xy_orthogonal xi hxi eta₁ ctx.eta_mem,
      ctx.xy_orthogonal xi₁ hxi₁X eta₁ ctx.eta_mem,
      ctx.x_orthonormal xi hxi xi₁ hxi₁X, if_neg hne,
      ctx.x_orthonormal xi₁ hxi₁X xi₁ hxi₁X, if_pos rfl]
    ring

  let xi₃ : ClassFunction L ℂ := ClassFunction.inverseLinear xi₁
  have hxi₃X : xi₃ ∈ X := ctx.x_family.2 xi₁ hxi₁X
  have hxi₃Ne : xi₃ ≠ xi₁ :=
    ctx.subcoherent_data.inverse_ne xi₁ (ctx.x_family.1 hxi₁X)
  have hdXi₃ : d xi₃ = 1 := by
    have hdegreeInv : xi₃ 1 = xi₁ 1 := by
      simp [xi₃]
    have hcast : (d xi₃ : ℂ) = 1 := by
      have hdDegree := hd xi₃ hxi₃X
      rw [hdegreeInv] at hdDegree
      apply mul_right_cancel₀ hxi₁DegreeNe
      simpa using hdDegree.symm
    exact_mod_cast hcast

  have hX₁Alternatives : X₁ = tau₂ xi₁ ∨ X₁ = -tau₂ xi₃ := by
    have hpair := hcompare xi₃ hxi₃X hxi₃Ne
    rw [hdXi₃, Nat.cast_one, one_smul] at hpair
    obtain ⟨chi₁, e₁, he₁, htau₁⟩ := htau₂Signed xi₁ hxi₁X
    obtain ⟨chi₃, e₃, he₃, htau₃⟩ := htau₂Signed xi₃ hxi₃X
    obtain ⟨rho, er, her, hX₁r⟩ := hX₁Signed
    rw [htau₁, htau₃, hX₁r,
      pairing_sub_left, characterPairing_smul_left,
      characterPairing_smul_left, characterPairing_smul_right,
      characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_eq_ite,
      IrreducibleCharacter.characterPairing_eq_ite] at hpair
    by_cases h₁ : chi₁ = rho
    · by_cases h₃ : chi₃ = rho
      · rw [if_pos h₁, if_pos h₃] at hpair
        exfalso
        rcases he₁ with rfl | rfl <;>
          rcases he₃ with rfl | rfl <;>
          rcases her with rfl | rfl <;>
          norm_num at hpair
      · left
        rw [if_pos h₁, if_neg h₃] at hpair
        norm_num at hpair
        have herEq : er = e₁ := by
          have hprod : e₁ * er = 1 := by exact_mod_cast hpair
          calc
            er = 1 * er := by ring
            _ = e₁ ^ 2 * er := by rw [isSign_iff_sq_eq_one.mp he₁]
            _ = e₁ * (e₁ * er) := by ring
            _ = e₁ := by rw [hprod]; ring
        rw [hX₁r, htau₁, h₁, herEq]
    · by_cases h₃ : chi₃ = rho
      · right
        rw [if_neg h₁, if_pos h₃] at hpair
        norm_num at hpair
        have herEq : er = -e₃ := by
          have hnegProd : -(e₃ * er) = 1 := by exact_mod_cast hpair
          have hprod : e₃ * er = -1 := by omega
          calc
            er = 1 * er := by ring
            _ = e₃ ^ 2 * er := by rw [isSign_iff_sq_eq_one.mp he₃]
            _ = e₃ * (e₃ * er) := by ring
            _ = -e₃ := by rw [hprod]; ring
        rw [hX₁r, htau₃, h₃, herEq, Int.cast_neg]
        module
      · rw [if_neg h₁, if_neg h₃] at hpair
        norm_num at hpair

  rcases hX₁Alternatives with hX₁eq | hX₁eq
  · refine ⟨tau₂, tauY, Or.inl rfl, htauY, ?_⟩
    rw [← hX₁eq]
    exact hbetaCanonical
  · have hXsubset : X ⊆ {xi₁, xi₃} := by
      intro xi hxi
      by_cases hxiOne : xi = xi₁
      · simp [hxiOne]
      by_cases hxiThree : xi = xi₃
      · simp [hxiThree]
      exfalso
      have hpair := hcompare xi hxi hxiOne
      rw [hX₁eq, pairing_sub_left,
        characterPairing_smul_left, pairing_neg_right,
        pairing_neg_right,
        hcohX.isometry xi₁ (AddSubgroup.subset_closure hxi₁X)
          xi₃ (AddSubgroup.subset_closure hxi₃X),
        hcohX.isometry xi (AddSubgroup.subset_closure hxi)
          xi₃ (AddSubgroup.subset_closure hxi₃X),
        ctx.x_orthonormal xi₁ hxi₁X xi₃ hxi₃X,
        if_neg hxi₃Ne.symm,
        ctx.x_orthonormal xi hxi xi₃ hxi₃X,
        if_neg hxiThree] at hpair
      norm_num at hpair
      have hdPos : d xi ≠ 0 := by
        intro hd0
        apply ctx.subcoherent_data.degree_ne_zero xi
          (ctx.x_family.1 hxi)
        rw [hd xi hxi, hd0, Nat.cast_zero, zero_mul]
      exact hdPos (by exact_mod_cast hpair.symm)
    have hXcard : X.card ≤ 2 := by
      calc
        X.card ≤ ({xi₁, xi₃} :
            Finset (ClassFunction L ℂ)).card :=
          Finset.card_le_card hXsubset
        _ ≤ 2 := Finset.card_le_two
    refine ⟨dual_iso tau₂, tauY,
      Or.inr ⟨hXcard, rfl⟩, htauY, ?_⟩
    rw [dual_iso_apply]
    change tau psi₁ =
      -tau₂ xi₃ - (a : ℂ) • tauY eta₁
    rw [← hX₁eq]
    exact hbetaCanonical

end

end Submission.OddOrder.PF
