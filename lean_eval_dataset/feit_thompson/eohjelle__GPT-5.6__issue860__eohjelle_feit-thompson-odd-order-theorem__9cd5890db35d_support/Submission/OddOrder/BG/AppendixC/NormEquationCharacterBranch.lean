import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Complex
import Submission.OddOrder.BG.AppendixC.Arithmetic
import Submission.OddOrder.BG.AppendixC.NormEquationBound
import Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic
import Submission.OddOrder.MathlibSupport.IrreducibleCharacterDegreeDivides
import Submission.OddOrder.PF.Section01.CharacterCompleteness
import Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent
import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence

/-!
# Appendix C, Lemma C.2: the `q > 4` character branch

This file ports the character-theoretic branch of Coq `BGappendixC.v`,
lines 287--386.  The proof has four logically independent parts:

* the class-product coefficient and its irreducible-character expansion;
* the Frobenius-kernel split into quotient-linear and induced characters;
* the two column-orthogonality bounds and the resulting distance estimate;
* the elementary `q > 4` comparison which forces the coefficient to be
  positive.

The generic analytic and arithmetic pieces below deliberately retain the
source normalizations.  In particular, `Pcard`, `Ucard`, and `e` stand for
`#|P|`, `#|U|`, and the class-product coefficient in the Coq proof.
-/

namespace Submission.OddOrder.BG.AppendixC

noncomputable section

open scoped BigOperators ComplexConjugate MonoidAlgebra

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF

universe u v

local instance complexGroupCardInvertible
    {G : Type u} [Group G] [Fintype G] :
    Invertible (Nat.card G : ℂ) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

private theorem classFunction_fintype_sum_apply
    {G : Type u} [Group G] {I : Type*} [Fintype I]
    (F : I → ClassFunction G ℂ) (g : G) :
    (∑ i, F i) g = ∑ i, F i g := by
  classical
  change (Finset.univ.sum F) g =
    Finset.univ.sum (fun i ↦ F i g)
  induction (Finset.univ : Finset I) using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, ih]

/-! ## Generic class-product coefficients -/

/-- The combinatorial class-product coefficient

`#{(x,y) | x ~ a, y ~ b, x*y = c}`.

This is the direct Lean analogue of MathComp's
`gring_classM_coef_set`. -/
def classProductCoefficient
    {G : Type u} [Group G] [Fintype G] (a b c : G) : ℕ :=
  ∑ x : G, ∑ y : G,
    @ite ℕ (IsConj x a ∧ IsConj y b ∧ x * y = c)
      (Classical.propDecidable _) 1 0

/-- Simultaneous conjugation of both factors conjugates the target and does
not change the class-product coefficient. -/
theorem classProductCoefficient_conj
    {G : Type u} [Group G] [Fintype G] (a b c z : G) :
    classProductCoefficient a b (z * c * z⁻¹) =
      classProductCoefficient a b c := by
  classical
  let e : G ≃ G := (MulAut.conj z).toEquiv
  calc
    classProductCoefficient a b (z * c * z⁻¹) =
        ∑ x : G, ∑ y : G,
          @ite ℕ (IsConj (e x) a ∧ IsConj (e y) b ∧
              e x * e y = z * c * z⁻¹)
            (Classical.propDecidable _) 1 0 := by
      rw [classProductCoefficient]
      refine Fintype.sum_equiv e.symm _ _ fun x ↦ ?_
      refine Fintype.sum_equiv e.symm _ _ fun y ↦ ?_
      simp only [Equiv.apply_symm_apply]
      by_cases h : IsConj x a ∧ IsConj y b ∧
        x * y = z * c * z⁻¹ <;> simp only [h]
    _ = classProductCoefficient a b c := by
      rw [classProductCoefficient]
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      have hxa : IsConj (e x) a ↔ IsConj x a := by
        have hx : IsConj x (e x) := isConj_iff.mpr ⟨z, rfl⟩
        exact ⟨fun h ↦ hx.trans h, fun h ↦ hx.symm.trans h⟩
      have hyb : IsConj (e y) b ↔ IsConj y b := by
        have hy : IsConj y (e y) := isConj_iff.mpr ⟨z, rfl⟩
        exact ⟨fun h ↦ hy.trans h, fun h ↦ hy.symm.trans h⟩
      have hmul : e x * e y = z * c * z⁻¹ ↔ x * y = c := by
        change (MulAut.conj z) x * (MulAut.conj z) y =
          (MulAut.conj z) c ↔ x * y = c
        constructor <;> intro h
        · apply (MulAut.conj z).injective
          rw [map_mul]
          exact h
        · rw [← map_mul]
          exact congrArg (MulAut.conj z) h
      by_cases h : IsConj x a ∧ IsConj y b ∧ x * y = c <;>
        simp only [hxa, hyb, hmul, h]

/-- The class function whose value at `g` is the coefficient of `g⁻¹` in
the product of the classes of `a` and `b`.  The inverse is chosen so that
the project's inverse-argument character pairing produces the usual class
multiplication formula without an extra dualization. -/
def classProductInverseCount
    {G : Type u} [Group G] [Fintype G] (a b : G) :
    ClassFunction G ℂ where
  val g := (classProductCoefficient a b g⁻¹ : ℂ)
  property z g := by
    change (classProductCoefficient a b (z * g * z⁻¹)⁻¹ : ℂ) =
      (classProductCoefficient a b g⁻¹ : ℂ)
    rw [conj_inv]
    exact congrArg (fun n : ℕ ↦ (n : ℂ))
      (classProductCoefficient_conj a b g⁻¹ z)

@[simp]
theorem classProductInverseCount_apply
    {G : Type u} [Group G] [Fintype G] (a b g : G) :
    classProductInverseCount a b g =
      (classProductCoefficient a b g⁻¹ : ℂ) :=
  rfl

/-- Summing a function against the class-product coefficients is the same
as summing it over the two input conjugacy classes. -/
theorem sum_mul_classProductCoefficient
    {G : Type u} [Group G] [Fintype G]
    (a b : G) (f : G → ℂ) :
    (∑ g : G, f g * (classProductCoefficient a b g : ℂ)) =
      ∑ x : G, ∑ y : G,
        @ite ℂ (IsConj x a ∧ IsConj y b)
          (Classical.propDecidable _) (f (x * y)) 0 := by
  classical
  simp only [classProductCoefficient, Nat.cast_sum, Nat.cast_ite,
    Nat.cast_one, Nat.cast_zero, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxy : IsConj x a ∧ IsConj y b
  · simp only [hxy, true_and, if_true]
    simp
  · have hnone : ∀ g : G,
        ¬ (IsConj x a ∧ IsConj y b ∧ x * y = g) := by
      intro g h
      exact hxy ⟨h.1, h.2.1⟩
    simp only [hxy, if_false, hnone, mul_zero, Finset.sum_const_zero]

/-- The double character sum over two conjugacy classes is the trace of the
product of the corresponding class-sum endomorphisms. -/
theorem sum_character_classProduct_eq_trace
    {G : Type u} {V : Type v} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (a b : G) :
    (∑ x : G, ∑ y : G,
        @ite ℂ (IsConj x a ∧ IsConj y b)
          (Classical.propDecidable _) (rho.character (x * y)) 0) =
      LinearMap.trace ℂ V
        (conjugacyClassEnd rho a * conjugacyClassEnd rho b) := by
  classical
  rw [conjugacyClassEnd, conjugacyClassEnd, Finset.sum_mul, map_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [Finset.mul_sum, map_sum]
  apply Finset.sum_congr rfl
  intro y _
  by_cases hxa : IsConj x a <;> by_cases hyb : IsConj y b
  · rw [if_pos ⟨hxa, hyb⟩, if_pos hxa, if_pos hyb]
    simp only [Representation.character, map_mul]
  · rw [if_neg (fun h ↦ hyb h.2), if_pos hxa, if_neg hyb,
      mul_zero, map_zero]
  · rw [if_neg (fun h ↦ hxa h.1), if_neg hxa, if_pos hyb,
      zero_mul, map_zero]
  · rw [if_neg (fun h ↦ hxa h.1), if_neg hxa, if_neg hyb,
      zero_mul, map_zero]

/-- Schur's lemma computes the trace of a product of two conjugacy-class
sums.  This is the scalar calculation at the heart of
`gring_classM_coef_sum_eq`. -/
theorem trace_conjugacyClassEnd_mul
    {G : Type u} {V : Type v} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) [Representation.IsIrreducible rho]
    (a b : G) :
    LinearMap.trace ℂ V
        (conjugacyClassEnd rho a * conjugacyClassEnd rho b) =
      (conjugacyClassCard a : ℂ) * (conjugacyClassCard b : ℂ) *
        rho.character a * rho.character b /
          (Module.finrank ℂ V : ℂ) := by
  obtain ⟨ca, _hcaIntegral, hca⟩ :=
    exists_integral_scalar_conjugacyClassEnd rho a
  obtain ⟨cb, _hcbIntegral, hcb⟩ :=
    exists_integral_scalar_conjugacyClassEnd rho b
  letI : Nontrivial rho.asModule :=
    IsSimpleModule.nontrivial ℂ[G] rho.asModule
  letI : Nontrivial V := inferInstanceAs (Nontrivial rho.asModule)
  have hd : (Module.finrank ℂ V : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  have hcaTrace := congrArg (LinearMap.trace ℂ V) hca
  have hcbTrace := congrArg (LinearMap.trace ℂ V) hcb
  have hca' :
      (conjugacyClassCard a : ℂ) * rho.character a =
        ca * (Module.finrank ℂ V : ℂ) := by
    rw [trace_conjugacyClassEnd] at hcaTrace
    simpa using hcaTrace
  have hcb' :
      (conjugacyClassCard b : ℂ) * rho.character b =
        cb * (Module.finrank ℂ V : ℂ) := by
    rw [trace_conjugacyClassEnd] at hcbTrace
    simpa using hcbTrace
  rw [hca, hcb]
  have htraceScalar :
      LinearMap.trace ℂ V
          ((ca • (1 : Module.End ℂ V)) *
            (cb • (1 : Module.End ℂ V))) =
        ca * cb * (Module.finrank ℂ V : ℂ) := by
    simp [mul_assoc, mul_left_comm]
  rw [htraceScalar]
  field_simp [hd]
  calc
    ca * cb * (Module.finrank ℂ V : ℂ) ^ 2 =
        (ca * (Module.finrank ℂ V : ℂ)) *
          (cb * (Module.finrank ℂ V : ℂ)) := by ring
    _ = ((conjugacyClassCard a : ℂ) * rho.character a) *
          ((conjugacyClassCard b : ℂ) * rho.character b) := by
      rw [hca', hcb']
    _ = (conjugacyClassCard a : ℂ) * (conjugacyClassCard b : ℂ) *
          rho.character a * rho.character b := by ring

/-- Pairing an irreducible character with the inverse class-product count
has the usual central-character value. -/
theorem characterPairing_classProductInverseCount
    {G : Type u} [Group G] [Fintype G]
    (chi : IrreducibleCharacter G ℂ) (a b : G) :
    characterPairing (chi : ClassFunction G ℂ)
        (classProductInverseCount a b) =
      (Nat.card G : ℂ)⁻¹ *
        ((conjugacyClassCard a : ℂ) *
          (conjugacyClassCard b : ℂ) * chi a * chi b /
            chi 1) := by
  classical
  let V := chi.representation
  let rho : Representation ℂ G V := V.ρ
  letI : CategoryTheory.Simple V := chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep V
  have hrho (g : G) : rho.character g = chi g := by
    change _root_.Representation.character chi.representation.ρ g = chi g
    have h := congrArg (fun F : ClassFunction G ℂ ↦ F g)
      chi.ofRepresentation_representation
    exact h
  rw [characterPairing]
  have hsum :
      (∑ g : G, chi g *
          classProductInverseCount a b g⁻¹) =
        LinearMap.trace ℂ V
          (conjugacyClassEnd rho a * conjugacyClassEnd rho b) := by
    rw [show (∑ g : G, chi g * classProductInverseCount a b g⁻¹) =
        ∑ g : G, chi g * (classProductCoefficient a b g : ℂ) by simp]
    rw [sum_mul_classProductCoefficient]
    rw [← sum_character_classProduct_eq_trace (V := V) rho a b]
    apply Finset.sum_congr rfl
    intro x _
    apply Finset.sum_congr rfl
    intro y _
    by_cases hxy : IsConj x a ∧ IsConj y b
    · rw [if_pos hxy, if_pos hxy, hrho]
    · rw [if_neg hxy, if_neg hxy]
  rw [hsum, trace_conjugacyClassEnd_mul (V := V) rho a b]
  have hdegree : chi 1 = (Module.finrank ℂ chi.representation : ℂ) := by
    rw [← chi.representation_character, FDRep.char_one]
  rw [hrho a, hrho b, ← hdegree]

/-- Isaacs' class-multiplication coefficient formula, in the precise
inverse-value convention corresponding to Coq
`gring_classM_coef_sum_eq`. -/
theorem classProductCoefficient_eq_characterSum
    {G : Type u} [Group G] [Fintype G] (a b c : G) :
    (classProductCoefficient a b c : ℂ) =
      ((conjugacyClassCard a : ℂ) *
          (conjugacyClassCard b : ℂ) / (Nat.card G : ℂ)) *
        ∑ chi : IrreducibleCharacter G ℂ,
          chi a * chi b * chi c⁻¹ / chi 1 := by
  classical
  let f := classProductInverseCount a b
  have hexp := irreducibleCharacterExpansion_eq (G := G) (k := ℂ) f
  have hvalueRaw := congrArg (fun F : ClassFunction G ℂ ↦ F c⁻¹) hexp
  rw [irreducibleCharacterExpansion] at hvalueRaw
  have hvalue :
    (∑ chi : IrreducibleCharacter G ℂ,
        characterPairing (chi : ClassFunction G ℂ) f * chi c⁻¹) =
      (classProductCoefficient a b c : ℂ) := by
    rw [classFunction_fintype_sum_apply] at hvalueRaw
    simpa only [ClassFunction.smul_apply,
      smul_eq_mul, f, classProductInverseCount_apply, inv_inv] using hvalueRaw
  rw [← hvalue]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro chi _
  rw [characterPairing_classProductInverseCount chi a b]
  ring

/-! ## Complex conjugation and column orthogonality -/

/-- For a complex representation of a finite group, the character value at
the inverse is the complex conjugate of the original value.  MathComp uses
this silently when changing `chi(g⁻¹)` into `chi(g)^*`.

The proof diagonalizes the finite-order operator by the same primitive-root
trace formula already used by `CharacterValueCyclotomic`. -/
theorem representation_character_inv_eq_conj
    {G : Type u} {V : Type v} [Group G] [Fintype G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ G V) (g : G) :
    rho.character g⁻¹ = star (rho.character g) := by
  let n := Nat.card G
  have hn : n ≠ 0 := Nat.card_pos.ne'
  letI : NeZero n := ⟨hn⟩
  let omega0 : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have homega0 : IsPrimitiveRoot omega0 n := by
    simpa only [omega0] using Complex.isPrimitiveRoot_exp n hn
  let omega : ℂˣ := Units.mk0 omega0 (homega0.ne_zero hn)
  have homega : IsPrimitiveRoot omega n := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [omega] using homega0
  have homegaNorm : ‖(omega : ℂ)‖ = 1 := by
    simpa [omega] using homega0.norm'_eq_one hn
  have homegaPow : (omega : ℂ) ^ n = 1 := by
    exact congrArg (fun z : ℂˣ ↦ (z : ℂ)) homega.pow_eq_one
  have hpow : (rho g) ^ n = 1 := by
    rw [← map_pow, pow_card_eq_one', map_one]
  have hginvPow : g⁻¹ = g ^ (n - 1) := by
    exact inv_eq_of_mul_eq_one_right (by
      rw [mul_pow_sub_one hn, pow_card_eq_one'])
  have hinvPow : rho g⁻¹ = (rho g) ^ (n - 1) := by
    rw [hginvPow, map_pow]
  have hweight (i : ZMod n) :
      (primitiveRootUnitWeight homega i : ℂ) =
        (omega : ℂ) ^ i.val := by
    conv_lhs =>
      rw [← ZMod.natCast_zmod_val i,
        primitiveRootUnitWeight_natCast]
    rfl
  have hweightConj (i : ZMod n) :
      (starRingEnd ℂ) (primitiveRootUnitWeight homega i : ℂ) =
        (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) := by
    let w : ℂ := primitiveRootUnitWeight homega i
    have hwNorm : ‖w‖ = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        norm_pow, homegaNorm, one_pow]
    have hwPow : w ^ n = 1 := by
      rw [show w = (omega : ℂ) ^ i.val by exact hweight i,
        ← pow_mul, Nat.mul_comm, pow_mul, homegaPow, one_pow]
    have hwInv : w⁻¹ = w ^ (n - 1) :=
      inv_eq_of_mul_eq_one_right (by rw [mul_pow_sub_one hn, hwPow])
    change (starRingEnd ℂ) w = w ^ (n - 1)
    rw [← Complex.inv_eq_conj hwNorm, hwInv]
  have htraceOne :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho g) hpow 1
  have htracePred :=
    trace_pow_eq_sum_primitiveRootUnitWeight homega (rho g) hpow (n - 1)
  simp only [pow_one] at htraceOne
  calc
    rho.character g⁻¹ = LinearMap.trace ℂ V (rho g⁻¹) := rfl
    _ = LinearMap.trace ℂ V ((rho g) ^ (n - 1)) := by rw [hinvPow]
    _ = ∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho g)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ) ^ (n - 1) :=
      htracePred
    _ = star (∑ i : ZMod n,
          (Module.finrank ℂ
              (Module.End.eigenspace (rho g)
                (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
            (primitiveRootUnitWeight homega i : ℂ)) := by
      change _ = (starRingEnd ℂ) (∑ i : ZMod n,
        (Module.finrank ℂ
            (Module.End.eigenspace (rho g)
              (primitiveRootUnitWeight homega i : ℂ)) : ℂ) *
          (primitiveRootUnitWeight homega i : ℂ))
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, map_natCast, hweightConj]
    _ = star (LinearMap.trace ℂ V (rho g)) := by rw [htraceOne]
    _ = star (rho.character g) := rfl

/-- Irreducible-character specialization of
`representation_character_inv_eq_conj`. -/
theorem irreducibleCharacter_apply_inv_eq_conj
    {G : Type u} [Group G] [Fintype G]
    (chi : IrreducibleCharacter G ℂ) (g : G) :
    chi g⁻¹ = star (chi g) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representation_character_inv_eq_conj
    (V := chi.representation) chi.representation.ρ g

/-- Column orthogonality in a denominator-free form.  The cardinality is
that of the inverse conjugacy class because this is the class indicator
selected by the project's inverse-argument pairing. -/
theorem conjugacyClassCard_mul_characterColumn
    {G : Type u} [Group G] [Fintype G] (x : G) :
    (conjugacyClassCard x⁻¹ : ℂ) *
        (∑ chi : IrreducibleCharacter G ℂ, chi x * chi x⁻¹) =
      (Nat.card G : ℂ) := by
  classical
  let f : ClassFunction G ℂ := ClassFunction.conjugacyIndicator x⁻¹
  have hexp := irreducibleCharacterExpansion_eq (G := G) (k := ℂ) f
  have hvalueRaw := congrArg (fun F : ClassFunction G ℂ ↦ F x⁻¹) hexp
  rw [irreducibleCharacterExpansion] at hvalueRaw
  have hcardNe : (Nat.card G : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hvalue :
    (∑ chi : IrreducibleCharacter G ℂ,
        characterPairing (chi : ClassFunction G ℂ) f * chi x⁻¹) = 1 := by
    rw [classFunction_fintype_sum_apply] at hvalueRaw
    simpa only [ClassFunction.smul_apply,
      smul_eq_mul, f, ClassFunction.conjugacyIndicator_apply,
      IsConj.refl, if_true] using hvalueRaw
  have hcoeff (chi : IrreducibleCharacter G ℂ) :
      characterPairing (chi : ClassFunction G ℂ) f =
        (Nat.card G : ℂ)⁻¹ *
          (conjugacyClassCard x⁻¹ : ℂ) * chi x := by
    rw [characterPairing_comm]
    change characterPairing (ClassFunction.conjugacyIndicator x⁻¹)
      (chi : ClassFunction G ℂ) = _
    have hvalueAt (y : G) (hy : IsConj y x⁻¹) : chi y⁻¹ = chi x := by
      obtain ⟨z, hz⟩ := isConj_iff.mp hy
      have hinv : z * y⁻¹ * z⁻¹ = x := by
        calc
          z * y⁻¹ * z⁻¹ = (z * y * z⁻¹)⁻¹ := conj_inv.symm
          _ = (x⁻¹)⁻¹ := congrArg Inv.inv hz
          _ = x := inv_inv x
      calc
        chi y⁻¹ = chi (z * y⁻¹ * z⁻¹) :=
          (ClassFunction.conj_apply (chi : ClassFunction G ℂ) z y⁻¹).symm
        _ = chi x := by rw [hinv]
    have hsum :
        (∑ y : G, ClassFunction.conjugacyIndicator (k := ℂ) x⁻¹ y *
            chi y⁻¹) =
          ∑ y : G, if IsConj y x⁻¹ then chi x else 0 := by
      apply Finset.sum_congr rfl
      intro y _
      by_cases hy : IsConj y x⁻¹
      · rw [ClassFunction.conjugacyIndicator_apply, if_pos hy, one_mul,
          if_pos hy, hvalueAt y hy]
      · rw [ClassFunction.conjugacyIndicator_apply, if_neg hy, zero_mul,
          if_neg hy]
    have hsum' :
        (∑ y : G, if IsConj y x⁻¹ then chi x else 0) =
          (conjugacyClassCard x⁻¹ : ℂ) * chi x := by
      rw [conjugacyClassCard, ← Finset.sum_filter]
      simp [Finset.sum_const, nsmul_eq_mul]
    unfold characterPairing
    rw [hsum, hsum']
    simp only [mul_assoc]
  simp_rw [hcoeff] at hvalue
  have hvalue' :
      (Nat.card G : ℂ)⁻¹ * (conjugacyClassCard x⁻¹ : ℂ) *
          (∑ chi : IrreducibleCharacter G ℂ, chi x * chi x⁻¹) = 1 := by
    rw [Finset.mul_sum]
    simpa only [mul_assoc] using hvalue
  field_simp [hcardNe] at hvalue'
  exact hvalue'

/-- Real norm-square form of column orthogonality. -/
theorem conjugacyClassCard_mul_characterColumn_normSq
    {G : Type u} [Group G] [Fintype G] (x : G) :
    (conjugacyClassCard x⁻¹ : ℝ) *
        (∑ chi : IrreducibleCharacter G ℂ, ‖chi x‖ ^ 2) =
      (Nat.card G : ℝ) := by
  have h := conjugacyClassCard_mul_characterColumn x
  simp_rw [irreducibleCharacter_apply_inv_eq_conj] at h
  simp_rw [Complex.star_def, Complex.mul_conj, ← Complex.sq_norm] at h
  exact_mod_cast h

/-! ## The analytic estimate from the two character columns -/

/-- The exact post-splitting identity used in Coq lines 361--371 implies the
distance bound.  `I` is the set of irreducible characters nontrivial on the
Frobenius kernel, `a i` is the value at `s`, and `b i` the value at `s²`.

The two hypotheses are precisely the restrictions of second orthogonality
to those rows. -/
theorem classCoefficient_distance_le
    {I : Type*} [Fintype I]
    (Pcard Ucard e : ℕ) (a b : I → ℂ)
    (hidentity :
      ((Pcard * e : ℕ) : ℂ) - ((Ucard : ℂ) ^ 2) =
        ∑ i : I, a i ^ 2 * star (b i))
    (hcolA : ∑ i : I, ‖a i‖ ^ 2 ≤ Pcard)
    (hcolB : ∑ i : I, ‖b i‖ ^ 2 ≤ Pcard) :
    ‖((Pcard * e : ℕ) : ℂ) - ((Ucard : ℂ) ^ 2)‖ ≤
      (Pcard : ℝ) * Real.sqrt Pcard := by
  classical
  rw [hidentity]
  calc
    ‖∑ i : I, a i ^ 2 * star (b i)‖ ≤
        ∑ i : I, ‖a i ^ 2 * star (b i)‖ := norm_sum_le _ _
    _ = ∑ i : I, ‖a i‖ ^ 2 * ‖b i‖ := by
      apply Finset.sum_congr rfl
      intro i _
      rw [norm_mul, norm_pow, norm_star]
    _ ≤ ∑ i : I, ‖a i‖ ^ 2 * Real.sqrt Pcard := by
      apply Finset.sum_le_sum
      intro i _
      apply mul_le_mul_of_nonneg_left _ (sq_nonneg ‖a i‖)
      have hib : ‖b i‖ ^ 2 ≤ Pcard :=
        le_trans (Finset.single_le_sum
          (fun j _ ↦ sq_nonneg ‖b j‖) (Finset.mem_univ i)) hcolB
      exact (Real.le_sqrt (norm_nonneg _) (by positivity)).2 (by
        simpa [pow_two] using hib)
    _ = (∑ i : I, ‖a i‖ ^ 2) * Real.sqrt Pcard := by
      rw [Finset.sum_mul]
    _ ≤ (Pcard : ℝ) * Real.sqrt Pcard := by
      exact mul_le_mul_of_nonneg_right hcolA (Real.sqrt_nonneg _)

/-! ## The `q > 4` numerical comparison -/

/-- The last term of the geometric series is a lower bound for `nU`. -/
theorem pow_pred_le_nU {p q : ℕ} (hq : 0 < q) :
    p ^ (q - 1) ≤ nU p q := by
  rw [nU]
  apply Finset.single_le_sum (fun i _ ↦ Nat.zero_le (p ^ i))
  simp only [Finset.mem_range]
  omega

/-- The strict comparison used in the last twelve lines of the Coq `q > 4`
branch.  The source proves it by a chain of exponent rewrites.  Here we use
`1 + sqrt(P) ≤ 2*sqrt(P)` and then square; the remaining natural-number
inequality is `4*p^(3*q) < p^(4*(q-1))`. -/
theorem card_mul_one_add_sqrt_lt_nU_sq
    {p q : ℕ} (hp : p.Prime) (hp4 : 4 < p) (hq4 : 4 < q) :
    (p ^ q : ℝ) * (1 + Real.sqrt (p ^ q : ℝ)) <
      (nU p q : ℝ) ^ 2 := by
  have hp1 : 1 < p := hp.one_lt
  have hq0 : 0 < q := by omega
  have hqdiff : 1 ≤ q - 4 := by omega
  have hpPow : 4 < p ^ (q - 4) := by
    exact lt_of_lt_of_le hp4 (by
      simpa only [pow_one] using
        (pow_le_pow_right₀ hp1.le hqdiff : p ^ 1 ≤ p ^ (q - 4)))
  have hbasePos : 0 < p ^ (3 * q) := pow_pos hp.pos _
  have hpowNat : 4 * p ^ (3 * q) < p ^ (4 * (q - 1)) := by
    calc
      4 * p ^ (3 * q) < p ^ (q - 4) * p ^ (3 * q) :=
        Nat.mul_lt_mul_of_pos_right hpPow hbasePos
      _ = p ^ (4 * (q - 1)) := by
        rw [← pow_add]
        congr 1
        omega
  have hlast : (p ^ (q - 1) : ℝ) ≤ nU p q := by
    exact_mod_cast pow_pred_le_nU (p := p) hq0
  have hPone : (1 : ℝ) ≤ (p ^ q : ℝ) := by
    exact_mod_cast (one_le_pow₀ hp1.le)
  have hsqrtOne : (1 : ℝ) ≤ Real.sqrt (p ^ q : ℝ) := by
    exact Real.one_le_sqrt.mpr hPone
  have hcoarse :
      (p ^ q : ℝ) * (1 + Real.sqrt (p ^ q : ℝ)) ≤
        2 * ((p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ)) := by
    nlinarith [show 0 ≤ (p ^ q : ℝ) by positivity]
  have hsquares :
      (2 * ((p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ))) ^ 2 <
        ((p ^ (q - 1) : ℝ) ^ 2) ^ 2 := by
    have hleft :
        (2 * ((p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ))) ^ 2 =
          ((4 * p ^ (3 * q) : ℕ) : ℝ) := by
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (show 0 ≤ (p ^ q : ℝ) by positivity)]
      push_cast
      norm_num
      rw [show 3 * q = q * 3 by omega, pow_mul]
      ring
    have hright :
        ((p ^ (q - 1) : ℝ) ^ 2) ^ 2 =
          ((p ^ (4 * (q - 1)) : ℕ) : ℝ) := by
      push_cast
      rw [← pow_mul, ← pow_mul]
      congr 1
      omega
    rw [hleft, hright]
    exact_mod_cast hpowNat
  have hstrict :
      2 * ((p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ)) <
        (p ^ (q - 1) : ℝ) ^ 2 := by
    nlinarith [show 0 ≤ (p ^ q : ℝ) *
      Real.sqrt (p ^ q : ℝ) by positivity]
  exact lt_of_le_of_lt hcoarse
    (lt_of_lt_of_le hstrict (pow_le_pow_left₀ (by positivity) hlast 2))

/-- The numerical conclusion of the `q > 4` branch: the character estimate
forces the class-product coefficient to be positive. -/
theorem classCoefficient_pos_of_q_gt_four
    {p q e : ℕ} (hp : p.Prime) (hp4 : 4 < p) (hq4 : 4 < q)
    (hdist :
      ‖(((p ^ q) * e : ℕ) : ℂ) - ((nU p q : ℂ) ^ 2)‖ ≤
        (p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ)) :
    1 < e := by
  by_contra he
  have he1 : e ≤ 1 := Nat.le_of_not_gt he
  let z : ℂ :=
    (((p ^ q) * e : ℕ) : ℂ) - ((nU p q : ℂ) ^ 2)
  have hzre : z.re =
      (p ^ q : ℝ) * e - (nU p q : ℝ) ^ 2 := by
    simp only [z, Complex.sub_re, pow_two, Complex.mul_re,
      Complex.natCast_re, Complex.natCast_im, mul_zero, sub_zero]
    push_cast
    ring
  have hzbound : |z.re| ≤
      (p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ) :=
    (Complex.abs_re_le_norm z).trans (by simpa only [z] using hdist)
  have hreal :
      (nU p q : ℝ) ^ 2 - (p ^ q : ℝ) * e ≤
        (p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ) := by
    rw [hzre] at hzbound
    nlinarith [neg_le_abs ((p ^ q : ℝ) * e - (nU p q : ℝ) ^ 2)]
  have hPe : (p ^ q : ℝ) * e ≤ (p ^ q : ℝ) := by
    exact mul_le_of_le_one_right (by positivity) (by exact_mod_cast he1)
  have hstrict := card_mul_one_add_sqrt_lt_nU_sq hp hp4 hq4
  nlinarith

/-- Source-facing cardinality form.  Once the class-product coefficient is
identified with the norm-equation set, positivity gives the desired second
element because `1` is already in that set. -/
theorem one_lt_normEquationSet_ncard_of_q_gt_four
    {p q e : ℕ} [Fact p.Prime]
    (F : Type u) [Field F] [Finite F]
    [Algebra (ZMod p) F]
    (hqp : q < p) (hq4 : 4 < q)
    (hcard : (normEquationSet (ZMod p) F).ncard = e)
    (hdist :
      ‖(((p ^ q) * e : ℕ) : ℂ) - ((nU p q : ℂ) ^ 2)‖ ≤
        (p ^ q : ℝ) * Real.sqrt (p ^ q : ℝ)) :
    1 < (normEquationSet (ZMod p) F).ncard := by
  have hp4 : 4 < p := lt_trans hq4 hqp
  have hepos : 1 < e :=
    classCoefficient_pos_of_q_gt_four Fact.out hp4 hq4 hdist
  simpa only [hcard] using hepos

end

end Submission.OddOrder.BG.AppendixC
