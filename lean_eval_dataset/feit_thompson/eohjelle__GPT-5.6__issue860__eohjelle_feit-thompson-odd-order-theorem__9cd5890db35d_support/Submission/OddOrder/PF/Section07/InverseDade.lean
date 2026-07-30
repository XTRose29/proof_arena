import Submission.OddOrder.PF.Section01.OddConjugateIrreducible
import Submission.OddOrder.PF.Section02.DadeReciprocity

/-!
# Peterfalvi Section 7: the inverse Dade operator

This file ports the opening of `PFsection7.v`, through Peterfalvi (7.3).
For a class function on `G`, `invDade` averages its values on the coset
`DadeSignalizer ddA a * a`.  The Dade reciprocity formula says precisely
that this averaging operator is the adjoint of `Dade` on functions supported
on the Dade set.  Consequently it is a left inverse there, is norm
decreasing, and equality is characterized by constancy on signalizer cosets.

The Coq development compares complex self-pairings with `leC`.  In Lean we
make the real quantity explicit as `classFunctionNormSq`; it is the real part
of the star character pairing and has the usual normalized sum-of-squares
formula.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

universe u

variable {Γ : Type u} [Group Γ]

/-! ## Normalized squared norms -/

/-- The normalized squared norm of a complex class function. -/
def classFunctionNormSq
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) : ℝ :=
  (Nat.card Q : ℝ)⁻¹ * ∑ x : Q, Complex.normSq (phi x)

/-- The normalized sum of squared values on the global Dade support. -/
def dadeSupportNormSq
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) : ℝ :=
  (Nat.card G : ℝ)⁻¹ *
    ∑ g ∈ Finset.univ.filter (fun g : G ↦ (g : Γ) ∈ Dade_support ddA),
      Complex.normSq (chi g)

/-- The sum-of-squares norm is the real part of the star pairing. -/
theorem classFunctionNormSq_eq_re_starCharacterPairing
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) :
    classFunctionNormSq phi =
      (starCharacterPairing phi phi).re := by
  simp only [classFunctionNormSq, starCharacterPairing,
    twistedCharacterPairing, Complex.star_def, Complex.mul_conj]
  simp

/-- The self star-pairing is the complex cast of the real squared norm. -/
theorem starCharacterPairing_self_eq_classFunctionNormSq
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) :
    starCharacterPairing phi phi = (classFunctionNormSq phi : ℂ) := by
  simp only [classFunctionNormSq, starCharacterPairing,
    twistedCharacterPairing, Complex.star_def, Complex.mul_conj]
  simp

/-- Positivity of the normalized squared norm. -/
theorem classFunctionNormSq_nonneg
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) :
    0 ≤ classFunctionNormSq phi := by
  unfold classFunctionNormSq
  exact mul_nonneg
    (inv_nonneg.mpr (Nat.cast_nonneg (Nat.card Q)))
    (Finset.sum_nonneg fun x _ ↦ Complex.normSq_nonneg (phi x))

/-- Positive definiteness of the normalized squared norm. -/
theorem classFunctionNormSq_eq_zero_iff
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) :
    classFunctionNormSq phi = 0 ↔ phi = 0 := by
  constructor
  · intro hnorm
    have hcard : 0 < (Nat.card Q : ℝ) :=
      Nat.cast_pos.mpr Nat.card_pos
    have hsumNonneg :
        0 ≤ ∑ x : Q, Complex.normSq (phi x) :=
      Finset.sum_nonneg fun x _ ↦ Complex.normSq_nonneg (phi x)
    have hsum : ∑ x : Q, Complex.normSq (phi x) = 0 := by
      unfold classFunctionNormSq at hnorm
      have hinv : 0 < (Nat.card Q : ℝ)⁻¹ := inv_pos.mpr hcard
      nlinarith
    apply ClassFunction.ext
    intro x
    simp only [ClassFunction.zero_apply]
    have hx : Complex.normSq (phi x) = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg
        (fun y _ ↦ Complex.normSq_nonneg (phi y))).mp
          hsum x (Finset.mem_univ x)
    exact Complex.normSq_eq_zero.mp hx
  · rintro rfl
    simp [classFunctionNormSq]

/-! ## Definition of the inverse Dade map -/

/-- The element `x * a` of `G` used in the signalizer average. -/
private def dadeCosetElement
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a : L)
    (x : DadeSignalizer ddA (a : Γ)) : G :=
  ⟨(x : Γ) * (a : Γ),
    G.mul_mem (Dade_signalizer_sub ddA (a : Γ) x.property)
      (ddA.2.1 a.property)⟩

/-- The pointwise signalizer average underlying `invDade`. -/
private def invDadeValue
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (chi : ClassFunction G ℂ) (a : L) : ℂ :=
  if ha : (a : Γ) ∈ A then
    (Nat.card (DadeSignalizer ddA (a : Γ)) : ℂ)⁻¹ *
      ∑ x : DadeSignalizer ddA (a : Γ),
        chi (dadeCosetElement ddA a x)
  else
    0

/-- Peterfalvi's `invDade_subproof`: the signalizer average is constant on
`L`-conjugacy classes. -/
theorem invDade_subproof
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (chi : ClassFunction G ℂ) (y a : L) :
    invDadeValue ddA chi (y * a * y⁻¹) = invDadeValue ddA chi a := by
  let b : Γ := (y : Γ) * (a : Γ) * (y : Γ)⁻¹
  have hbval : ((y * a * y⁻¹ : L) : Γ) = b := rfl
  have hAiff : b ∈ A ↔ (a : Γ) ∈ A := by
    have hnorm := Subgroup.mem_set_normalizer_iff''.mp
      (ddA.1.2 (L.inv_mem y.property)) (a : Γ)
    simpa [b, mul_assoc] using hnorm.symm
  by_cases ha : (a : Γ) ∈ A
  · have hb : b ∈ A := hAiff.mpr ha
    let e : Γ ≃* Γ := MulAut.conj (y : Γ)
    have hJ :
        DadeSignalizer ddA b =
          (DadeSignalizer ddA (a : Γ)).map e.toMonoidHom := by
      simpa [b, e, mul_assoc] using
        DadeJ ddA (a : Γ) (y : Γ)⁻¹ (L.inv_mem y.property)
    let eH : DadeSignalizer ddA (a : Γ) ≃ DadeSignalizer ddA b :=
      { toFun := fun x ↦ ⟨e x, by
          rw [hJ]
          exact Subgroup.mem_map_equiv.mpr (by simpa using x.property)⟩
        invFun := fun z ↦ ⟨e.symm z, by
          have hz : (z : Γ) ∈
              (DadeSignalizer ddA (a : Γ)).map e.toMonoidHom := by
            rw [← hJ]
            exact z.property
          exact Subgroup.mem_map_equiv.mp hz⟩
        left_inv := fun x ↦ by
          apply Subtype.ext
          exact e.symm_apply_apply (x : Γ)
        right_inv := fun z ↦ by
          apply Subtype.ext
          exact e.apply_symm_apply (z : Γ) }
    have hcard :
        Nat.card (DadeSignalizer ddA b) =
          Nat.card (DadeSignalizer ddA (a : Γ)) :=
      Nat.card_congr eH.symm
    have hcard' :
        Nat.card (DadeSignalizer ddA ((y * a * y⁻¹ : L) : Γ)) =
          Nat.card (DadeSignalizer ddA (a : Γ)) := by
      simpa [b] using hcard
    have hsum :
        (∑ z : DadeSignalizer ddA b,
            chi (dadeCosetElement ddA (y * a * y⁻¹) z)) =
          ∑ x : DadeSignalizer ddA (a : Γ),
            chi (dadeCosetElement ddA a x) := by
      calc
        _ = ∑ x : DadeSignalizer ddA (a : Γ),
            chi (dadeCosetElement ddA (y * a * y⁻¹) (eH x)) :=
          (Equiv.sum_comp eH
            (fun z : DadeSignalizer ddA b ↦
              chi (dadeCosetElement ddA (y * a * y⁻¹) z))).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro x _
          let yG : G := ⟨y, ddA.2.1 y.property⟩
          have heq :
              dadeCosetElement ddA (y * a * y⁻¹) (eH x) =
                yG * dadeCosetElement ddA a x * yG⁻¹ := by
            apply Subtype.ext
            simp [dadeCosetElement, eH, e, b, yG, mul_assoc]
          rw [heq]
          exact ClassFunction.conj_apply chi yG (dadeCosetElement ddA a x)
    have hsum' :
        (∑ z : DadeSignalizer ddA ((y * a * y⁻¹ : L) : Γ),
            chi (dadeCosetElement ddA (y * a * y⁻¹) z)) =
          ∑ x : DadeSignalizer ddA (a : Γ),
            chi (dadeCosetElement ddA a x) := by
      simpa [b] using hsum
    unfold invDadeValue
    rw [dif_pos ha, dif_pos (hbval.symm ▸ hb)]
    rw [hcard', hsum']
  · have hb : b ∉ A := fun hb ↦ ha (hAiff.mp hb)
    unfold invDadeValue
    rw [dif_neg ha, dif_neg (hbval.symm ▸ hb)]

/-- Peterfalvi (7.1): the right adjoint of the Dade isometry, obtained by
averaging over the canonical signalizers. -/
noncomputable def invDade
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    ClassFunction G ℂ →ₗ[ℂ] ClassFunction L ℂ where
  toFun chi :=
    ⟨invDadeValue ddA chi, invDade_subproof ddA chi⟩
  map_add' chi psi := by
    apply ClassFunction.ext
    intro a
    by_cases ha : (a : Γ) ∈ A
    · simp only [invDadeValue, dif_pos ha, ClassFunction.add_apply]
      rw [Finset.sum_add_distrib, mul_add]
    · simp [invDadeValue, ha]
  map_smul' c chi := by
    apply ClassFunction.ext
    intro a
    by_cases ha : (a : Γ) ∈ A
    · simp only [invDadeValue, dif_pos ha, ClassFunction.smul_apply,
        smul_eq_mul, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro x _
      simp [mul_comm, mul_left_comm, mul_assoc]
    · simp [invDadeValue, ha]

@[simp]
theorem invDade_apply
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (chi : ClassFunction G ℂ) (a : L) :
    invDade ddA chi a = invDadeValue ddA chi a :=
  rfl

/-- Linearity of the inverse Dade operator. -/
theorem invDade_is_linear
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    IsLinearMap ℂ (invDade ddA) :=
  (invDade ddA).isLinear

/-- The inverse Dade average is supported on the Dade set. -/
theorem invDade_on
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    invDade ddA chi ∈
      ClassFunction.supportedOn {a : L | (a : Γ) ∈ A} := by
  rw [ClassFunction.mem_supportedOn_iff]
  intro a ha
  change (a : Γ) ∉ A at ha
  simp [invDade_apply, invDadeValue, ha]

/-- The characteristic class function of the Dade set `A` in `L`. -/
noncomputable def DadeSetIndicator
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) : ClassFunction L ℂ where
  val a := if (a : Γ) ∈ A then 1 else 0
  property := by
    intro y a
    have hiff :
        (((y * a * y⁻¹ : L) : Γ) ∈ A) ↔ (a : Γ) ∈ A := by
      have hnorm := Subgroup.mem_set_normalizer_iff''.mp
        (ddA.1.2 (L.inv_mem y.property)) (a : Γ)
      simpa [mul_assoc] using hnorm.symm
    exact if_congr hiff rfl rfl

@[simp]
theorem DadeSetIndicator_apply
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (a : L) :
    DadeSetIndicator ddA a = if (a : Γ) ∈ A then 1 else 0 :=
  rfl

private theorem invDade_eq_of_constant
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ)
    {a : Γ} (ha : a ∈ A)
    (hconst : ∀ x : DadeSignalizer ddA a,
      chi ⟨(x : Γ) * a,
        G.mul_mem (Dade_signalizer_sub ddA a x.property)
          (ddA.2.1 (ddA.1.1 ha))⟩ =
      chi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩) :
    invDade ddA chi ⟨a, ddA.1.1 ha⟩ =
      chi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ := by
  rw [invDade_apply]
  unfold invDadeValue
  rw [dif_pos ha]
  have hsum :
      (∑ x : DadeSignalizer ddA a,
          chi (dadeCosetElement ddA ⟨a, ddA.1.1 ha⟩ x)) =
        ∑ _x : DadeSignalizer ddA a,
          chi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ := by
    apply Finset.sum_congr rfl
    intro x _
    exact hconst x
  rw [hsum]
  simp only [Finset.sum_const, nsmul_eq_mul,
    Finset.card_univ, Nat.card_eq_fintype_card]
  have hcard :
      ((Fintype.card (DadeSignalizer ddA a) : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr (Fintype.card_pos.ne')
  field_simp [hcard]

/-- The inverse Dade map sends the trivial character to the characteristic
function of `A`. -/
theorem invDade_cfun1
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    invDade ddA
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) =
      DadeSetIndicator ddA := by
  apply ClassFunction.ext
  intro a
  by_cases ha : (a : Γ) ∈ A
  · have hconst : ∀ x : DadeSignalizer ddA (a : Γ),
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ)
            (dadeCosetElement ddA a x) =
          ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
            ClassFunction G ℂ)
            ⟨a, ddA.2.1 a.property⟩ := by
      intro x
      simp
    rw [invDade_eq_of_constant ddA
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) ha hconst]
    simp [DadeSetIndicator_apply, ha]
  · rw [ClassFunction.eq_zero_of_mem_supportedOn (invDade_on ddA _) ha]
    simp [DadeSetIndicator_apply, ha]

/-! ## Reciprocity and the left-inverse identity -/

/-- Peterfalvi (2.7), restated with the inverse Dade operator. -/
theorem invDade_reciprocity
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (chi : ClassFunction G ℂ) (alpha : ClassFunction L ℂ)
    (halpha : alpha ∈
      ClassFunction.supportedOn {a : L | (a : Γ) ∈ A}) :
    starCharacterPairing (Dade ddA alpha) chi =
      starCharacterPairing alpha (invDade ddA chi) := by
  apply general_Dade_reciprocity ddA alpha chi (invDade ddA chi) halpha
  intro a ha
  rw [invDade_apply]
  simp [invDadeValue, ha, dadeCosetElement]

/-- Peterfalvi (7.2)(a): `invDade` is a left inverse to `Dade` on class
functions supported on `A`. -/
theorem DadeK
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (alpha : ClassFunction L ℂ)
    (halpha : alpha ∈
      ClassFunction.supportedOn {a : L | (a : Γ) ∈ A}) :
    invDade ddA (Dade ddA alpha) = alpha := by
  apply ClassFunction.ext
  intro a
  by_cases ha : (a : Γ) ∈ A
  · change invDade ddA (Dade ddA alpha) ⟨(a : Γ), ddA.1.1 ha⟩ = alpha a
    rw [← Dade_id ddA alpha ha]
    apply invDade_eq_of_constant ddA (Dade ddA alpha) ha
    intro x
    calc
      _ = alpha ⟨(a : Γ), ddA.1.1 ha⟩ :=
        DadeE ddA alpha ha _
          (mem_Dade_support1 ddA ha x.property)
      _ = _ := (Dade_id ddA alpha ha).symm
  · rw [ClassFunction.eq_zero_of_mem_supportedOn (invDade_on ddA _) ha,
      ClassFunction.eq_zero_of_mem_supportedOn halpha ha]

/-! ## Norm comparison -/

private theorem starCharacterPairing_sub_right
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi xi : ClassFunction Q ℂ) :
    starCharacterPairing phi (psi - xi) =
      starCharacterPairing phi psi - starCharacterPairing phi xi := by
  simp [sub_eq_add_neg, starCharacterPairing, twistedCharacterPairing,
    mul_add, Finset.sum_add_distrib]

/-- Peterfalvi (7.2)(b): the inverse Dade operator is norm decreasing, and
equality holds exactly on the image of `Dade`. -/
theorem leC_norm_invDade
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    classFunctionNormSq (invDade ddA chi) ≤ classFunctionNormSq chi ∧
      (classFunctionNormSq (invDade ddA chi) =
          classFunctionNormSq chi ↔
        chi = Dade ddA (invDade ddA chi)) := by
  let rho : ClassFunction L ℂ := invDade ddA chi
  let chi₁ : ClassFunction G ℂ := Dade ddA rho
  let mu : ClassFunction G ℂ := chi - chi₁
  have hrho : rho ∈
      ClassFunction.supportedOn {a : L | (a : Γ) ∈ A} :=
    invDade_on ddA chi
  have hisometry :
      classFunctionNormSq chi₁ = classFunctionNormSq rho := by
    rw [classFunctionNormSq_eq_re_starCharacterPairing,
      classFunctionNormSq_eq_re_starCharacterPairing]
    exact congrArg Complex.re (Dade_isometry ddA rho rho hrho hrho)
  have hcross : starCharacterPairing chi₁ mu = 0 := by
    rw [show mu = chi - chi₁ by rfl,
      starCharacterPairing_sub_right]
    change starCharacterPairing (Dade ddA rho) chi -
        starCharacterPairing (Dade ddA rho) (Dade ddA rho) = 0
    rw [invDade_reciprocity ddA chi rho hrho,
      Dade_isometry ddA rho rho hrho hrho]
    simp [rho]
  have hcross' : starCharacterPairing mu chi₁ = 0 := by
    rw [starCharacterPairing_conj_symm]
    rw [hcross]
    simp
  have hchi : chi₁ + mu = chi := by
    simp [mu]
  have hdecomp :
      classFunctionNormSq chi =
        classFunctionNormSq chi₁ + classFunctionNormSq mu := by
    rw [classFunctionNormSq_eq_re_starCharacterPairing,
      classFunctionNormSq_eq_re_starCharacterPairing,
      classFunctionNormSq_eq_re_starCharacterPairing]
    rw [← hchi, starCharacterPairing_add_left,
      starCharacterPairing_add_right, starCharacterPairing_add_right,
      hcross, hcross']
    simp
  have hmuNonneg := classFunctionNormSq_nonneg mu
  constructor
  · rw [← hisometry]
    linarith
  · constructor
    · intro heq
      have hmuZero : classFunctionNormSq mu = 0 := by
        rw [← hisometry] at heq
        linarith
      have hmuzero : mu = 0 :=
        (classFunctionNormSq_eq_zero_iff mu).mp hmuZero
      change chi = chi₁
      rw [← hchi, hmuzero, add_zero]
    · intro heq
      change chi = chi₁ at heq
      rw [← hisometry, heq]

/-! ## Restriction to the Dade support -/

private theorem DadeSupport_isConjStable
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    IsConjStable {g : G | (g : Γ) ∈ Dade_support ddA} := by
  intro x g
  have hnorm := Subgroup.mem_set_normalizer_iff.mp
    (Dade_support_norm ddA x.property) (g : Γ)
  simpa using hnorm.symm

/-- Cut a class function down to the global Dade support. -/
private noncomputable def DadeSupportPart
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    ClassFunction G ℂ :=
  ClassFunction.indicator {g : G | (g : Γ) ∈ Dade_support ddA}
    (DadeSupport_isConjStable ddA) chi

private theorem DadeSupportPart_norm
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    classFunctionNormSq (DadeSupportPart ddA chi) =
      dadeSupportNormSq ddA chi := by
  unfold classFunctionNormSq dadeSupportNormSq
  congr 1
  calc
    (∑ g : G, Complex.normSq (DadeSupportPart ddA chi g)) =
        ∑ g : G, if (g : Γ) ∈ Dade_support ddA then
          Complex.normSq (chi g) else 0 := by
      apply Finset.sum_congr rfl
      intro g _
      by_cases hg : (g : Γ) ∈ Dade_support ddA <;>
        simp [DadeSupportPart, hg]
    _ = ∑ g ∈ Finset.univ.filter
          (fun g : G ↦ (g : Γ) ∈ Dade_support ddA),
          Complex.normSq (chi g) := by
      rw [Finset.sum_filter]

private theorem invDade_DadeSupportPart
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    invDade ddA (DadeSupportPart ddA chi) = invDade ddA chi := by
  apply ClassFunction.ext
  intro a
  by_cases ha : (a : Γ) ∈ A
  · rw [invDade_apply, invDade_apply]
    unfold invDadeValue
    rw [dif_pos ha, dif_pos ha]
    congr 1
    apply Finset.sum_congr rfl
    intro x _
    apply ClassFunction.indicator_apply_of_mem
    exact ⟨(a : Γ), ha,
      mem_Dade_support1 ddA ha x.property⟩
  · rw [ClassFunction.eq_zero_of_mem_supportedOn
        (invDade_on ddA (DadeSupportPart ddA chi)) ha,
      ClassFunction.eq_zero_of_mem_supportedOn (invDade_on ddA chi) ha]

private theorem DadeSupportPart_eq_Dade_invDade_iff
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    DadeSupportPart ddA chi = Dade ddA (invDade ddA chi) ↔
      ∀ {a : Γ} (ha : a ∈ A) (x : DadeSignalizer ddA a),
        chi ⟨(x : Γ) * a,
          G.mul_mem (Dade_signalizer_sub ddA a x.property)
            (ddA.2.1 (ddA.1.1 ha))⟩ =
          chi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ := by
  constructor
  · intro heq a ha x
    let xa : G :=
      ⟨(x : Γ) * a,
        G.mul_mem (Dade_signalizer_sub ddA a x.property)
          (ddA.2.1 (ddA.1.1 ha))⟩
    let aG : G := ⟨a, ddA.2.1 (ddA.1.1 ha)⟩
    have hxaSupport : (xa : Γ) ∈ Dade_support ddA :=
      ⟨a, ha, mem_Dade_support1 ddA ha x.property⟩
    have haSupport : (aG : Γ) ∈ Dade_support ddA :=
      ⟨a, ha, by
        simpa using mem_Dade_support1 ddA ha
          (DadeSignalizer ddA a).one_mem⟩
    calc
      chi xa = DadeSupportPart ddA chi xa := by
        symm
        exact ClassFunction.indicator_apply_of_mem _ _ _ hxaSupport
      _ = Dade ddA (invDade ddA chi) xa := congrFun (congrArg Subtype.val heq) xa
      _ = invDade ddA chi ⟨a, ddA.1.1 ha⟩ :=
        DadeE ddA (invDade ddA chi) ha xa
          (mem_Dade_support1 ddA ha x.property)
      _ = Dade ddA (invDade ddA chi) aG :=
        (Dade_id ddA (invDade ddA chi) ha).symm
      _ = DadeSupportPart ddA chi aG :=
        congrFun (congrArg Subtype.val heq.symm) aG
      _ = chi aG :=
        ClassFunction.indicator_apply_of_mem _ _ _ haSupport
  · intro hconst
    apply ClassFunction.ext
    intro g
    by_cases hg : (g : Γ) ∈ Dade_support ddA
    · rcases hg with ⟨a, ha, hga⟩
      rcases hga with ⟨z, hz, y, hyG, hzyg⟩
      rcases Set.mem_mul.mp hz with ⟨x, hx, b, hb, hxab⟩
      have hbEq : b = a := Set.mem_singleton_iff.mp hb
      subst b
      let xH : DadeSignalizer ddA a := ⟨x, hx⟩
      let xa : G :=
        ⟨x * a,
          G.mul_mem (Dade_signalizer_sub ddA a hx)
            (ddA.2.1 (ddA.1.1 ha))⟩
      let yG : G := ⟨y, hyG⟩
      have hconj : yG⁻¹ * xa * yG = g := by
        apply Subtype.ext
        rw [← hzyg, ← hxab]
        rfl
      have hchiConj : chi g = chi xa := by
        rw [← hconj]
        simpa only [inv_inv] using
          ClassFunction.conj_apply chi yG⁻¹ xa
      have hrho :
          invDade ddA chi ⟨a, ddA.1.1 ha⟩ =
            chi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ :=
        invDade_eq_of_constant ddA chi ha (hconst ha)
      calc
        DadeSupportPart ddA chi g = chi g :=
          ClassFunction.indicator_apply_of_mem _ _ _
            (show (g : Γ) ∈ Dade_support ddA from
              ⟨a, ha, ⟨z, hz, y, hyG, hzyg⟩⟩)
        _ = chi xa := hchiConj
        _ = chi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩ := hconst ha xH
        _ = invDade ddA chi ⟨a, ddA.1.1 ha⟩ := hrho.symm
        _ = Dade ddA (invDade ddA chi) g :=
          (DadeE ddA (invDade ddA chi) ha g
            ⟨z, hz, y, hyG, hzyg⟩).symm
    · change (ClassFunction.indicator
          {g : G | (g : Γ) ∈ Dade_support ddA}
          (DadeSupport_isConjStable ddA) chi) g = _
      rw [ClassFunction.indicator_apply_of_notMem
          {g : G | (g : Γ) ∈ Dade_support ddA}
          (DadeSupport_isConjStable ddA) chi hg,
        Dade_eq_zero_of_not_mem ddA (invDade ddA chi) g hg]

/-- Peterfalvi (7.3): the inverse norm is bounded by the norm on the Dade
support.  Equality says exactly that `chi` is constant on every canonical
signalizer coset. -/
theorem leC_cfnorm_invDade_support
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    classFunctionNormSq (invDade ddA chi) ≤
        dadeSupportNormSq ddA chi ∧
      (classFunctionNormSq (invDade ddA chi) =
          dadeSupportNormSq ddA chi ↔
        ∀ {a : Γ} (ha : a ∈ A) (x : DadeSignalizer ddA a),
          chi ⟨(x : Γ) * a,
            G.mul_mem (Dade_signalizer_sub ddA a x.property)
              (ddA.2.1 (ddA.1.1 ha))⟩ =
            chi ⟨a, ddA.2.1 (ddA.1.1 ha)⟩) := by
  let chiS := DadeSupportPart ddA chi
  have hinv : invDade ddA chiS = invDade ddA chi :=
    invDade_DadeSupportPart ddA chi
  have hnorm : classFunctionNormSq chiS = dadeSupportNormSq ddA chi :=
    DadeSupportPart_norm ddA chi
  have hle := leC_norm_invDade ddA chiS
  constructor
  · rw [← hinv, ← hnorm]
    exact hle.1
  · rw [← hinv, ← hnorm]
    calc
      classFunctionNormSq (invDade ddA chiS) =
            classFunctionNormSq chiS ↔
          chiS = Dade ddA (invDade ddA chiS) := hle.2
      _ ↔ DadeSupportPart ddA chi =
            Dade ddA (invDade ddA chi) := by rw [hinv]
      _ ↔ _ := DadeSupportPart_eq_Dade_invDade_iff ddA chi

/-- The norm expansion for `invDade`, embedded in Peterfalvi (7.3). -/
theorem cfnormE_invDade
    [Fintype Γ] {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    classFunctionNormSq (invDade ddA chi) =
      (Nat.card L : ℝ)⁻¹ *
        ∑ a ∈ Finset.univ.filter (fun a : L ↦ (a : Γ) ∈ A),
          Complex.normSq (invDade ddA chi a) := by
  unfold classFunctionNormSq
  congr 1
  calc
    (∑ a : L, Complex.normSq (invDade ddA chi a)) =
        ∑ a : L, if (a : Γ) ∈ A then
          Complex.normSq (invDade ddA chi a) else 0 := by
      apply Finset.sum_congr rfl
      intro a _
      by_cases ha : (a : Γ) ∈ A
      · simp [ha]
      · have hz : invDade ddA chi a = 0 :=
          ClassFunction.eq_zero_of_mem_supportedOn (invDade_on ddA chi) ha
        simp [ha, hz]
    _ = ∑ a ∈ Finset.univ.filter (fun a : L ↦ (a : Γ) ∈ A),
          Complex.normSq (invDade ddA chi a) := by
      rw [Finset.sum_filter]

end

end Submission.OddOrder.PF
