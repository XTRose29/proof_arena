import Submission.OddOrder.PF.Section02.DadeVirtualCharacter
import Submission.OddOrder.PF.Section05.CoherenceBasics
import Submission.OddOrder.PF.Section05.SeqIndGlobal
import Submission.OddOrder.PF.Section07.InverseDade
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.RingTheory.RootsOfUnity.Complex
import Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic

/-!
# Peterfalvi Section 7: a Dade cover and the first linear subtraction

This file ports `PFsection7.v`, lines 167--500.  It contains Peterfalvi's
cover inequality (7.5), the inverse-Dade expansion on a full family of
normally induced characters (7.7), and the linear-subtraction calculation
(7.8).

The Coq development orders the real subfield of `algC`.  In Lean the ordered
statements use the real norm `classFunctionNormSq`; character identities and
the coefficients in the sequential-induction expansion remain in `ℂ`.
Duplicate-free source sequences are represented by `Finset`s.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.MathlibSupport
open scoped BigOperators Classical Pointwise

set_option maxHeartbeats 1000000

universe u

variable {Γ : Type u} [Group Γ] [Fintype Γ]

/-! ## Peterfalvi (7.4)--(7.5): the cover inequality -/

/-- The part of `G` not covered by a finite family of global Dade supports. -/
def DadeCoverComplement
    {I : Type*} [Fintype I]
    {G : Subgroup Γ} {L : I → Subgroup Γ} {A : I → Set Γ}
    (ddA : ∀ i, DadeHypothesis G (L i) (A i)) : Set Γ :=
  (G : Set Γ) \ ⋃ i, Dade_support (ddA i)

/-- Normalized squared mass of a class function on the uncovered part. -/
def dadeCoverComplementNormSq
    {I : Type*} [Fintype I]
    {G : Subgroup Γ} {L : I → Subgroup Γ} {A : I → Set Γ}
    (ddA : ∀ i, DadeHypothesis G (L i) (A i))
    (chi : ClassFunction G ℂ) : ℝ :=
  (Nat.card G : ℝ)⁻¹ *
    ∑ g : G,
      if (g : Γ) ∈ DadeCoverComplement ddA then
        Complex.normSq (chi g)
      else 0

private def restrictedClassFunctionNormSq
    {G : Subgroup Γ} (S : Set Γ) (chi : ClassFunction G ℂ) : ℝ :=
  (Nat.card G : ℝ)⁻¹ *
    ∑ g : G, if (g : Γ) ∈ S then Complex.normSq (chi g) else 0

private theorem dadeSupportNormSq_eq_restricted
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) (chi : ClassFunction G ℂ) :
    dadeSupportNormSq ddA chi =
      restrictedClassFunctionNormSq (Dade_support ddA) chi := by
  unfold dadeSupportNormSq restrictedClassFunctionNormSq
  congr 1
  rw [← Finset.sum_filter]

private theorem dadeCoverComplementNormSq_eq_restricted
    {I : Type*} [Fintype I]
    {G : Subgroup Γ} {L : I → Subgroup Γ} {A : I → Set Γ}
    (ddA : ∀ i, DadeHypothesis G (L i) (A i))
    (chi : ClassFunction G ℂ) :
    dadeCoverComplementNormSq ddA chi =
      restrictedClassFunctionNormSq (DadeCoverComplement ddA) chi :=
  rfl

/-- A point belongs to at most one member of a pairwise-disjoint family. -/
private theorem disjoint_family_indicator_sum
    {I : Type*} [Fintype I]
    (S : I → Set Γ)
    (hdis : ∀ i j, i ≠ j → Disjoint (S i) (S j))
    (x : Γ) (r : ℝ) :
    (if x ∈ (Set.univ \ ⋃ i, S i) then r else 0) +
        ∑ i : I, (if x ∈ S i then r else 0) = r := by
  classical
  by_cases hx : ∃ i, x ∈ S i
  · obtain ⟨i, hxi⟩ := hx
    have hxUnion : x ∈ ⋃ i, S i := Set.mem_iUnion.mpr ⟨i, hxi⟩
    have hxComp : x ∉ Set.univ \ ⋃ i, S i := fun h ↦ h.2 hxUnion
    rw [if_neg hxComp]
    simp only [zero_add]
    rw [Finset.sum_eq_single i]
    · simp [hxi]
    · intro j _ hji
      have hxj : x ∉ S j := by
        intro hxj
        exact Set.disjoint_left.mp (hdis i j hji.symm) hxi hxj
      simp [hxj]
    · simp
  · have hxNone : ∀ i, x ∉ S i := by
      intro i hxi
      exact hx ⟨i, hxi⟩
    have hxComp : x ∈ Set.univ \ ⋃ i, S i := by
      refine ⟨Set.mem_univ x, ?_⟩
      intro hxUnion
      obtain ⟨i, hxi⟩ := Set.mem_iUnion.mp hxUnion
      exact hxNone i hxi
    simp [hxComp, hxNone]

/-- The uncovered mass and the masses on disjoint Dade supports partition
the full squared norm. -/
private theorem dade_cover_norm_partition
    {I : Type*} [Fintype I]
    {G : Subgroup Γ} {L : I → Subgroup Γ} {A : I → Set Γ}
    (ddA : ∀ i, DadeHypothesis G (L i) (A i))
    (hdis : ∀ i j, i ≠ j →
      Disjoint (Dade_support (ddA i)) (Dade_support (ddA j)))
    (chi : ClassFunction G ℂ) :
    dadeCoverComplementNormSq ddA chi +
        ∑ i : I, dadeSupportNormSq (ddA i) chi =
      classFunctionNormSq chi := by
  classical
  rw [dadeCoverComplementNormSq_eq_restricted]
  simp_rw [dadeSupportNormSq_eq_restricted]
  unfold restrictedClassFunctionNormSq classFunctionNormSq
  rw [← Finset.mul_sum]
  rw [← mul_add]
  congr 1
  rw [Finset.sum_comm]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro g _
  by_cases hg : ∃ i, (g : Γ) ∈ Dade_support (ddA i)
  · obtain ⟨i, hgi⟩ := hg
    have hgUnion : (g : Γ) ∈ ⋃ i, Dade_support (ddA i) :=
      Set.mem_iUnion.mpr ⟨i, hgi⟩
    have hgComp : (g : Γ) ∉ DadeCoverComplement ddA := by
      intro hcomp
      exact hcomp.2 hgUnion
    rw [if_neg hgComp, zero_add, Finset.sum_eq_single i]
    · simp [hgi]
    · intro j _ hji
      have hgj : (g : Γ) ∉ Dade_support (ddA j) := by
        intro hgj
        exact Set.disjoint_left.mp (hdis i j hji.symm) hgi hgj
      simp [hgj]
    · simp
  · have hgNone : ∀ i, (g : Γ) ∉ Dade_support (ddA i) := by
      intro i hgi
      exact hg ⟨i, hgi⟩
    have hgComp : (g : Γ) ∈ DadeCoverComplement ddA := by
      refine ⟨g.property, ?_⟩
      intro hgUnion
      obtain ⟨i, hgi⟩ := Set.mem_iUnion.mp hgUnion
      exact hgNone i hgi
    simp [hgComp, hgNone]

private theorem DadeSetIndicator_norm
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    classFunctionNormSq (DadeSetIndicator ddA) =
      (A.ncard : ℝ) / (Nat.card L : ℝ) := by
  let oneG : ClassFunction G ℂ :=
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)
  have hone : invDade ddA oneG = DadeSetIndicator ddA :=
    invDade_cfun1 ddA
  rw [← hone, cfnormE_invDade, hone]
  have hcard :
      (Finset.univ.filter (fun a : L ↦ (a : Γ) ∈ A)).card = A.ncard := by
    calc
      _ = ((↑(Finset.univ.filter
            (fun a : L ↦ (a : Γ) ∈ A)) : Set L)).ncard :=
        (Set.ncard_coe_finset _).symm
      _ = ({a : L | (a : Γ) ∈ A} : Set L).ncard := by
        congr 1
        ext a
        simp
      _ = (A ∩ (L : Set Γ)).ncard := Set.ncard_subtype _ A
      _ = A.ncard := by rw [Set.inter_eq_left.mpr ddA.1.1]
  have hsum :
      (∑ a ∈ Finset.univ.filter (fun a : L ↦ (a : Γ) ∈ A),
          Complex.normSq (DadeSetIndicator ddA a)) =
        ((Finset.univ.filter
          (fun a : L ↦ (a : Γ) ∈ A)).card : ℝ) := by
    calc
      _ = ∑ _a ∈ Finset.univ.filter (fun a : L ↦ (a : Γ) ∈ A),
          (1 : ℝ) := by
        apply Finset.sum_congr rfl
        intro a ha
        have haA := (Finset.mem_filter.mp ha).2
        simp [DadeSetIndicator_apply, haA]
      _ = _ := by simp
  rw [hsum, hcard]
  ring

private theorem trivial_dadeSupportNormSq
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) :
    dadeSupportNormSq ddA
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) =
      (A.ncard : ℝ) / (Nat.card L : ℝ) := by
  rw [← DadeSetIndicator_norm ddA, ← invDade_cfun1 ddA]
  exact ((leC_cfnorm_invDade_support ddA
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)).2.mpr (by
      intro a ha x
      simp [IrreducibleCharacter.trivial_apply])).symm

private theorem trivial_dadeCoverComplementNormSq
    {I : Type*} [Fintype I]
    {G : Subgroup Γ} {L : I → Subgroup Γ} {A : I → Set Γ}
    (ddA : ∀ i, DadeHypothesis G (L i) (A i)) :
    dadeCoverComplementNormSq ddA
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) =
      ((DadeCoverComplement ddA).ncard : ℝ) /
        (Nat.card G : ℝ) := by
  unfold dadeCoverComplementNormSq
  have hcard :
      (Finset.univ.filter
        (fun g : G ↦ (g : Γ) ∈ DadeCoverComplement ddA)).card =
        (DadeCoverComplement ddA).ncard := by
    calc
      _ = ((↑(Finset.univ.filter
            (fun g : G ↦ (g : Γ) ∈ DadeCoverComplement ddA)) :
              Set G)).ncard :=
        (Set.ncard_coe_finset _).symm
      _ = ({g : G | (g : Γ) ∈ DadeCoverComplement ddA} : Set G).ncard := by
        congr 1
        ext g
        simp
      _ = ((DadeCoverComplement ddA) ∩ (G : Set Γ)).ncard :=
        Set.ncard_subtype _ _
      _ = (DadeCoverComplement ddA).ncard := by
        apply congrArg Set.ncard
        exact Set.inter_eq_left.mpr (fun x hx ↦ hx.1)
  rw [← Finset.sum_filter]
  simp only [IrreducibleCharacter.trivial_apply, Complex.normSq_one,
    Finset.sum_const, nsmul_eq_mul, Nat.cast_ofNat, mul_one, hcard]
  ring

/-- Peterfalvi (7.5), generalized as in the source from irreducible
characters to all class functions of norm one. -/
theorem Dade_cover_inequality
    {I : Type*} [Fintype I]
    {G : Subgroup Γ} {L : I → Subgroup Γ} {A : I → Set Γ}
    (ddA : ∀ i, DadeHypothesis G (L i) (A i))
    (hdis : ∀ i j, i ≠ j →
      Disjoint (Dade_support (ddA i)) (Dade_support (ddA j)))
    (chi : ClassFunction G ℂ)
    (hchi : classFunctionNormSq chi = 1) :
    (Nat.card G : ℝ)⁻¹ *
        ((∑ g : G,
            if (g : Γ) ∈ DadeCoverComplement ddA then
              Complex.normSq (chi g)
            else 0) - (DadeCoverComplement ddA).ncard) +
      ∑ i : I,
        (classFunctionNormSq (invDade (ddA i) chi) -
          (A i).ncard / (Nat.card (L i) : ℝ)) ≤ 0 := by
  have hle (i : I) :
      classFunctionNormSq (invDade (ddA i) chi) ≤
        dadeSupportNormSq (ddA i) chi :=
    (leC_cfnorm_invDade_support (ddA i) chi).1
  have hpart := dade_cover_norm_partition ddA hdis chi
  have hpartOne := dade_cover_norm_partition ddA hdis
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)
  have hnormOne :
      classFunctionNormSq
        ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
          ClassFunction G ℂ) = 1 := by
    unfold classFunctionNormSq
    simp [IrreducibleCharacter.trivial_apply,
      Nat.cast_ne_zero.mpr Nat.card_pos.ne']
  have hcomp := trivial_dadeCoverComplementNormSq ddA
  have hsupp (i : I) := trivial_dadeSupportNormSq (ddA i)
  have hsumle :
      ∑ i : I, classFunctionNormSq (invDade (ddA i) chi) ≤
        ∑ i : I, dadeSupportNormSq (ddA i) chi :=
    Finset.sum_le_sum fun i _ ↦ hle i
  rw [hchi] at hpart
  rw [hnormOne] at hpartOne
  simp_rw [hsupp] at hpartOne
  rw [hcomp] at hpartOne
  have hcardG : 0 < (Nat.card G : ℝ) := Nat.cast_pos.mpr Nat.card_pos
  calc
    _ = dadeCoverComplementNormSq ddA chi -
          dadeCoverComplementNormSq ddA
            ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
              ClassFunction G ℂ) +
        (∑ i : I, classFunctionNormSq (invDade (ddA i) chi) -
          ∑ i : I, dadeSupportNormSq (ddA i)
            ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
              ClassFunction G ℂ)) := by
      simp_rw [trivial_dadeSupportNormSq]
      rw [trivial_dadeCoverComplementNormSq]
      unfold dadeCoverComplementNormSq
      rw [Finset.sum_sub_distrib]
      ring
    _ ≤ dadeCoverComplementNormSq ddA chi -
          dadeCoverComplementNormSq ddA
            ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
              ClassFunction G ℂ) +
        (∑ i : I, dadeSupportNormSq (ddA i) chi -
          ∑ i : I, dadeSupportNormSq (ddA i)
            ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
              ClassFunction G ℂ)) := by
      linarith
    _ = 0 := by
      simp_rw [hsupp]
      linarith

/-! ## Peterfalvi (7.6)--(7.7): inverse Dade and sequential induction -/

/- The inverse-value identity used below was private to the earlier PF4
module.  Keep a local copy here so this file does not depend on another
file's implementation detail. -/
private theorem representation_character_inv_eq_star_cover
    {Q : Type u} {V : Type*} [Group Q] [Fintype Q]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (rho : Representation ℂ Q V) (g : Q) :
    rho.character g⁻¹ = star (rho.character g) := by
  let n := Nat.card Q
  have hn : n ≠ 0 := Nat.card_pos.ne'
  letI : NeZero n := ⟨hn⟩
  let omega₀ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have homega₀ : IsPrimitiveRoot omega₀ n := by
    simpa only [omega₀] using Complex.isPrimitiveRoot_exp n hn
  let omega : ℂˣ := Units.mk0 omega₀ (homega₀.ne_zero hn)
  have homega : IsPrimitiveRoot omega n := by
    apply IsPrimitiveRoot.coe_units_iff.mp
    simpa [omega] using homega₀
  have homegaNorm : ‖(omega : ℂ)‖ = 1 := by
    simpa [omega] using homega₀.norm'_eq_one hn
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
  have hweightStar (i : ZMod n) :
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
      rw [map_mul, map_natCast, hweightStar]
    _ = star (LinearMap.trace ℂ V (rho g)) := by rw [htraceOne]
    _ = star (rho.character g) := rfl

private theorem irreducibleCharacter_apply_inv_eq_star_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (chi : IrreducibleCharacter Q ℂ) (g : Q) :
    chi g⁻¹ = star (chi g) := by
  rw [← chi.representation_character,
    ← chi.representation_character]
  exact representation_character_inv_eq_star_cover
    chi.representation.ρ g

private theorem star_realize_apply_eq_inverse_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (z : VirtualCharacter Q ℂ) (x : Q) :
    star (VirtualCharacter.realize z x) =
      VirtualCharacter.realize z x⁻¹ := by
  classical
  induction z using Finsupp.induction with
  | zero => simp
  | single_add chi n z hchi hn ih =>
      rw [VirtualCharacter.realize_add, VirtualCharacter.realize_single]
      change (starRingEnd ℂ) ((n : ℂ) * chi.val x +
          VirtualCharacter.realize z x) =
        (n : ℂ) * chi.val x⁻¹ + VirtualCharacter.realize z x⁻¹
      have hchiStar :=
        (irreducibleCharacter_apply_inv_eq_star_cover chi x).symm
      change (starRingEnd ℂ) (chi.val x) = chi.val x⁻¹ at hchiStar
      change (starRingEnd ℂ) (VirtualCharacter.realize z x) =
        VirtualCharacter.realize z x⁻¹ at ih
      rw [map_add, map_mul, map_intCast, ih, hchiStar]

private theorem starCharacterPairing_realize_eq_characterPairing_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (z w : VirtualCharacter Q ℂ) :
    starCharacterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) =
      characterPairing (VirtualCharacter.realize z)
        (VirtualCharacter.realize w) := by
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  exact star_realize_apply_eq_inverse_cover w

private theorem starCharacterPairing_sub_left_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    starCharacterPairing (phi - psi) theta =
      starCharacterPairing phi theta -
        starCharacterPairing psi theta := by
  simp [sub_eq_add_neg, starCharacterPairing,
    twistedCharacterPairing, add_mul, Finset.sum_add_distrib]
  ring

private theorem starCharacterPairing_sub_right_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi theta : ClassFunction Q ℂ) :
    starCharacterPairing phi (psi - theta) =
      starCharacterPairing phi psi -
        starCharacterPairing phi theta := by
  simp [sub_eq_add_neg, starCharacterPairing,
    twistedCharacterPairing, mul_add, Finset.sum_add_distrib]

private theorem starCharacterPairing_finset_sum_left_cover
    {Q : Type u} [Group Q] [Fintype Q]
    {I : Type*} (s : Finset I) (f : I → ClassFunction Q ℂ)
    (psi : ClassFunction Q ℂ) :
    starCharacterPairing (∑ i ∈ s, f i) psi =
      ∑ i ∈ s, starCharacterPairing (f i) psi := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_left, ih,
        Finset.sum_insert hi]

private theorem starCharacterPairing_finset_sum_right_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (phi : ClassFunction Q ℂ) {I : Type*}
    (s : Finset I) (f : I → ClassFunction Q ℂ) :
    starCharacterPairing phi (∑ i ∈ s, f i) =
      ∑ i ∈ s, starCharacterPairing phi (f i) := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
      rw [Finset.sum_insert hi, starCharacterPairing_add_right, ih,
        Finset.sum_insert hi]

/-- The degree-normalized difference used in the source proof of (7.7). -/
def invDadeSeqIndAdjusted
    {L : Type*} [Group L] (xi0 xi : ClassFunction L ℂ) :
    ClassFunction L ℂ :=
  xi - (xi 1 / xi0 1) • xi0

/-- The reciprocal Dade coefficient `c xi` in Peterfalvi (7.7). -/
def invDadeSeqIndCoefficient
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A)
    (xi0 : ClassFunction L ℂ) (chi : ClassFunction G ℂ)
    (xi : ClassFunction L ℂ) : ℂ :=
  starCharacterPairing (Dade ddA (invDadeSeqIndAdjusted xi0 xi)) chi

/-- The coefficient `u xi mu` in the norm identity of Peterfalvi (7.7). -/
def invDadeSeqIndU
    {G L : Subgroup Γ} (H : Subgroup L)
    {A : Set Γ} (ddA : DadeHypothesis G L A)
    (xi0 : ClassFunction L ℂ) (chi : ClassFunction G ℂ)
    (xi mu : ClassFunction L ℂ) : ℂ :=
  let c := invDadeSeqIndCoefficient ddA xi0 chi
  (star (c xi) * c mu /
      (starCharacterPairing xi xi * starCharacterPairing mu mu)) *
    (starCharacterPairing xi mu -
      xi 1 * star (mu 1) /
        ((H.index : ℂ) * (Nat.card H : ℂ)))

/-- Source `is_invDade_seqInd_sum`.  The first field is the pointwise
expansion on `H^#`; the second is the corresponding exact self-pairing
identity. -/
structure IsInvDadeSeqIndSum
    {G L : Subgroup Γ} (H : Subgroup L)
    (ddA : DadeHypothesis G L
      (subgroupNonidentity (H.map L.subtype)))
    (xi0 : ClassFunction L ℂ) (S : Finset (ClassFunction L ℂ))
    (chi : ClassFunction G ℂ) : Prop where
  value_on_support :
    ∀ a : L,
      (a : Γ) ∈ subgroupNonidentity (H.map L.subtype) →
      invDade ddA chi a =
        ∑ xi ∈ S,
          (star (invDadeSeqIndCoefficient ddA xi0 chi xi) /
              starCharacterPairing xi xi) * xi a
  pairing_norm :
    starCharacterPairing (invDade ddA chi) (invDade ddA chi) =
      ∑ xi ∈ S, ∑ mu ∈ S,
        invDadeSeqIndU H ddA xi0 chi xi mu

private theorem seqInd_starPairing_eq_characterPairing
    {L : Type u} [Group L] [Fintype L]
    (H : Subgroup L) [H.Normal]
    {phi psi : ClassFunction L ℂ}
    (hphi : phi ∈ seqIndT (k := ℂ) H)
    (hpsi : psi ∈ seqIndT (k := ℂ) H) :
    starCharacterPairing phi psi = characterPairing phi psi := by
  obtain ⟨z, hz⟩ := seqInd_vcharW H hphi
  obtain ⟨w, hw⟩ := seqInd_vcharW H hpsi
  rw [← hz, ← hw]
  exact starCharacterPairing_realize_eq_characterPairing_cover z w

private theorem seqIndT_star_orthogonal
    {L : Type u} [Group L] [Fintype L]
    (H : Subgroup L) [H.Normal]
    {phi psi : ClassFunction L ℂ}
    (hphi : phi ∈ seqIndT (k := ℂ) H)
    (hpsi : psi ∈ seqIndT (k := ℂ) H)
    (hne : phi ≠ psi) :
    starCharacterPairing phi psi = 0 := by
  rw [seqInd_starPairing_eq_characterPairing H hphi hpsi]
  exact seqInd_ortho H hphi hpsi hne

private theorem supported_mem_span_seqIndT
    {L : Type u} [Group L] [Fintype L]
    (H : Subgroup L) [H.Normal]
    (phi : ClassFunction L ℂ)
    (hphi : phi ∈ ClassFunction.supportedOn (H : Set L)) :
    phi ∈ Submodule.span ℂ
      (↑(seqIndT (k := ℂ) H) : Set (ClassFunction L ℂ)) := by
  have hrecover :
      phi = (H.index : ℂ)⁻¹ •
        ClassFunction.induce H (ClassFunction.restrict H phi) := by
    apply ClassFunction.ext
    intro x
    by_cases hx : x ∈ H
    · rw [ClassFunction.smul_apply,
        ClassFunction.induce_apply_formula]
      have hconj (y : L) : y⁻¹ * x * y ∈ H := by
        simpa only [inv_inv] using
          (inferInstance : H.Normal).conj_mem x hx y⁻¹
      simp_rw [dif_pos (hconj _), ClassFunction.restrict_apply]
      have hvalue (y : L) :
          phi (y⁻¹ * x * y) = phi x := by
        simpa only [inv_inv] using ClassFunction.conj_apply phi y⁻¹ x
      simp_rw [hvalue]
      simp only [Finset.sum_const, nsmul_eq_mul, smul_eq_mul]
      have hHcard : (Nat.card H : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr Nat.card_pos.ne'
      have hindex : (H.index : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
      field_simp [hHcard, hindex]
      have hcardC :
          (H.index : ℂ) * (Nat.card H : ℂ) = (Nat.card L : ℂ) := by
        exact_mod_cast H.index_mul_card
      rw [mul_assoc, hcardC]
      simp [Nat.card_eq_fintype_card]
    · have hphi0 :=
        ClassFunction.eq_zero_of_mem_supportedOn hphi hx
      rw [hphi0, ClassFunction.smul_apply,
        ClassFunction.induce_apply_formula]
      have hnot (y : L) : y⁻¹ * x * y ∉ H := by
        intro hy
        apply hx
        have := (inferInstance : H.Normal).conj_mem
          (y⁻¹ * x * y) hy y
        simpa [mul_assoc] using this
      simp [hnot]
  rw [hrecover]
  apply Submodule.smul_mem
  rw [← irreducibleCharacterExpansion_eq
    (ClassFunction.restrict H phi)]
  unfold irreducibleCharacterExpansion
  rw [map_sum]
  apply Submodule.sum_mem
  intro xi _
  rw [LinearMap.map_smul]
  apply Submodule.smul_mem
  exact Submodule.subset_span (mem_seqIndT H xi)

private theorem mem_adjusted_span_of_mem_seqIndT_span
    {L : Type u} [Group L] [Fintype L]
    (xi0 : ClassFunction L ℂ) (S : Finset (ClassFunction L ℂ))
    (hxi0S : xi0 ∉ S) (hxi01 : xi0 1 ≠ 0)
    (phi : ClassFunction L ℂ)
    (hspan : phi ∈ Submodule.span ℂ (↑(insert xi0 S) :
      Set (ClassFunction L ℂ)))
    (hphi1 : phi 1 = 0) :
    phi ∈ Submodule.span ℂ
      (invDadeSeqIndAdjusted xi0 '' (↑S : Set (ClassFunction L ℂ))) := by
  classical
  obtain ⟨z, hz, hsum⟩ := Submodule.mem_span_finset.mp hspan
  have heval := congrArg (fun f : ClassFunction L ℂ ↦ f 1) hsum
  rw [Finset.sum_insert hxi0S] at hsum heval
  simp only [ClassFunction.add_apply, ClassFunction.finset_sum_apply,
    ClassFunction.smul_apply, smul_eq_mul, hphi1] at heval
  have hz0 :
      z xi0 = -(∑ xi ∈ S, z xi * xi 1) / xi0 1 := by
    apply (eq_div_iff hxi01).2
    exact eq_neg_of_add_eq_zero_left heval
  have hadjusted :
      phi = ∑ xi ∈ S, z xi • invDadeSeqIndAdjusted xi0 xi := by
    rw [← hsum, hz0]
    unfold invDadeSeqIndAdjusted
    simp only [smul_sub, smul_smul]
    rw [Finset.sum_sub_distrib]
    rw [← Finset.sum_smul]
    apply ClassFunction.ext
    intro x
    simp only [ClassFunction.add_apply, ClassFunction.sub_apply,
      ClassFunction.finset_sum_apply, ClassFunction.smul_apply, smul_eq_mul]
    have hcoeff :
        (∑ xi ∈ S, z xi * (xi 1 / xi0 1)) =
          (∑ xi ∈ S, z xi * xi 1) / xi0 1 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro xi _
      ring
    rw [hcoeff]
    ring
  rw [hadjusted]
  apply Submodule.sum_mem
  intro xi hxi
  apply Submodule.smul_mem
  exact Submodule.subset_span ⟨xi, hxi, rfl⟩

private theorem starPairing_seqIndT_subgroupNonidentity
    {L : Type u} [Group L] [Fintype L]
    (H : Subgroup L) [H.Normal]
    {xi mu : ClassFunction L ℂ}
    (hxi : xi ∈ seqIndT (k := ℂ) H)
    (hmu : mu ∈ seqIndT (k := ℂ) H) :
    starCharacterPairing xi mu =
      (Nat.card L : ℂ)⁻¹ *
        (xi 1 * star (mu 1) +
          ∑ x ∈ Finset.univ.filter
              (fun x : L ↦ x ∈ subgroupNonidentity H),
            xi x * star (mu x)) := by
  classical
  unfold starCharacterPairing twistedCharacterPairing
  congr 1
  let t : Finset L :=
    Finset.univ.filter (fun x : L ↦ x ∈ subgroupNonidentity H)
  have hone : (1 : L) ∉ t := by simp [t, subgroupNonidentity]
  have houtside :
      ∀ x ∈ Finset.univ, x ∉ insert 1 t →
        xi x * star (mu x) = 0 := by
    intro x _ hx
    have hxH : x ∉ H := by
      intro hxH
      have hx1 : x ≠ 1 := by
        intro hx1
        exact hx (by simp [hx1])
      exact hx (by simp [t, subgroupNonidentity, hxH, hx1])
    have hz := ClassFunction.eq_zero_of_mem_supportedOn
      (seqInd_on H hxi) hxH
    simp [hz]
  calc
    (∑ x : L, xi x * star (mu x)) =
        ∑ x ∈ insert 1 t, xi x * star (mu x) := by
      symm
      exact Finset.sum_subset (Finset.subset_univ _) houtside
    _ = xi 1 * star (mu 1) +
        ∑ x ∈ t, xi x * star (mu x) := by
      rw [Finset.sum_insert hone]
    _ = _ := by rfl

/-- Peterfalvi (7.7).  The explicit `xi0 ∉ S` premise records the
duplicate-free cons in the source `perm_eq calT (xi0 :: S)`. -/
theorem invDade_seqInd_sum
    {G L : Subgroup Γ} (H : Subgroup L) [H.Normal]
    (ddA : DadeHypothesis G L
      (subgroupNonidentity (H.map L.subtype)))
    (xi0 : ClassFunction L ℂ) (S : Finset (ClassFunction L ℂ))
    (chi : ClassFunction G ℂ)
    (hcalT : seqIndT (k := ℂ) H = insert xi0 S)
    (hxi0S : xi0 ∉ S) :
    IsInvDadeSeqIndSum H ddA xi0 S chi := by
  classical
  let A : Set Γ := subgroupNonidentity (H.map L.subtype)
  let rho : ClassFunction L ℂ := invDade ddA chi
  let c : ClassFunction L ℂ → ℂ :=
    invDadeSeqIndCoefficient ddA xi0 chi
  let chi0 : ClassFunction L ℂ :=
    ∑ xi ∈ S,
      (star (c xi) / starCharacterPairing xi xi) • xi
  have hxi0T : xi0 ∈ seqIndT (k := ℂ) H := by
    rw [hcalT]
    simp
  have hST : ∀ {xi}, xi ∈ S → xi ∈ seqIndT (k := ℂ) H := by
    intro xi hxi
    rw [hcalT]
    exact Finset.mem_insert_of_mem hxi
  have hxi01 : xi0 1 ≠ 0 := seqInd1_neq0 H hxi0T
  have hmapMem (a : L) :
      (a : Γ) ∈ H.map L.subtype ↔ a ∈ H := by
    constructor
    · rintro ⟨h, hh, heq⟩
      have hEq : h = a := Subtype.ext heq
      simpa [hEq] using hh
    · intro ha
      exact ⟨a, ha, rfl⟩
  have hadjustedOn {xi : ClassFunction L ℂ}
      (hxi : xi ∈ seqIndT (k := ℂ) H) :
      invDadeSeqIndAdjusted xi0 xi ∈
        ClassFunction.supportedOn {a : L | (a : Γ) ∈ A} := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro a ha
    by_cases haH : a ∈ H
    · have ha1 : a = 1 := by
        by_contra ha1
        exact ha ⟨(hmapMem a).mpr haH,
          (by simpa [nonidentitySet] using ha1)⟩
      subst a
      simp [invDadeSeqIndAdjusted, hxi01]
    · have hxi0 := ClassFunction.eq_zero_of_mem_supportedOn
        (seqInd_on H hxi0T) haH
      have hx := ClassFunction.eq_zero_of_mem_supportedOn
        (seqInd_on H hxi) haH
      simp [invDadeSeqIndAdjusted, hx, hxi0]
  have hprojection {xi : ClassFunction L ℂ} (hxiS : xi ∈ S) :
      starCharacterPairing (invDadeSeqIndAdjusted xi0 xi) chi0 = c xi := by
    have hxiT := hST hxiS
    unfold chi0
    rw [starCharacterPairing_finset_sum_right_cover]
    rw [Finset.sum_eq_single xi]
    · rw [starCharacterPairing_smul_right]
      unfold invDadeSeqIndAdjusted
      rw [starCharacterPairing_sub_left_cover]
      rw [starCharacterPairing_smul_left]
      rw [seqIndT_star_orthogonal H hxi0T hxiT (by
        intro heq
        exact hxi0S (heq ▸ hxiS))]
      rw [seqInd_starPairing_eq_characterPairing H hxiT hxiT]
      have hnorm := cfnorm_seqInd_neq0 H hxiT
      have hstarNorm :
          star (characterPairing xi xi) = characterPairing xi xi := by
        rw [← seqInd_starPairing_eq_characterPairing H hxiT hxiT,
          starCharacterPairing_self_eq_classFunctionNormSq]
        simp
      change (starRingEnd ℂ)
          (star (c xi) / characterPairing xi xi) *
            (characterPairing xi xi - xi 1 / xi0 1 * 0) = c xi
      have hcStarStar : (starRingEnd ℂ) (star (c xi)) = c xi := by
        change star (star (c xi)) = c xi
        rw [star_star]
      change (starRingEnd ℂ) (characterPairing xi xi) =
        characterPairing xi xi at hstarNorm
      rw [map_div₀, hcStarStar, hstarNorm]
      field_simp
      ring
    · intro mu hmuS hne
      have hmuT := hST hmuS
      rw [starCharacterPairing_smul_right]
      unfold invDadeSeqIndAdjusted
      rw [starCharacterPairing_sub_left_cover]
      rw [starCharacterPairing_smul_left]
      rw [seqIndT_star_orthogonal H hxiT hmuT hne.symm]
      rw [seqIndT_star_orthogonal H hxi0T hmuT (by
        intro heq
        exact hxi0S (heq ▸ hmuS))]
      simp
    · simp [hxiS]
  have hpairAdjusted {xi : ClassFunction L ℂ} (hxiS : xi ∈ S) :
      starCharacterPairing (invDadeSeqIndAdjusted xi0 xi)
        (rho - chi0) = 0 := by
    rw [starCharacterPairing_sub_right_cover]
    have hrecip := invDade_reciprocity ddA chi
      (invDadeSeqIndAdjusted xi0 xi) (hadjustedOn (hST hxiS))
    change c xi = _ at hrecip
    rw [← hrecip, hprojection hxiS, sub_self]
  let phi : ClassFunction L ℂ :=
    ClassFunction.pointwiseMul (rho - chi0) (DadeSetIndicator ddA)
  have hphiOnH : phi ∈ ClassFunction.supportedOn (H : Set L) := by
    rw [ClassFunction.mem_supportedOn_iff]
    intro a haH
    have haA : (a : Γ) ∉ A := by
      intro haA
      exact haH ((hmapMem a).mp haA.1)
    change (rho a - chi0 a) * DadeSetIndicator ddA a = 0
    rw [DadeSetIndicator_apply, if_neg haA, mul_zero]
  have hphi1 : phi 1 = 0 := by
    have hnotA : ((1 : L) : Γ) ∉
        subgroupNonidentity (H.map L.subtype) := by
      simpa using ddA.2.2.1
    change (rho 1 - chi0 1) * DadeSetIndicator ddA 1 = 0
    rw [DadeSetIndicator_apply, if_neg hnotA, mul_zero]
  have hphiSpanT :
      phi ∈ Submodule.span ℂ
        (↑(insert xi0 S) : Set (ClassFunction L ℂ)) := by
    rw [← hcalT]
    exact supported_mem_span_seqIndT H phi hphiOnH
  have hphiAdjusted :
      phi ∈ Submodule.span ℂ
        (invDadeSeqIndAdjusted xi0 ''
          (↑S : Set (ClassFunction L ℂ))) :=
    mem_adjusted_span_of_mem_seqIndT_span xi0 S hxi0S hxi01
      phi hphiSpanT hphi1
  have hphiOrth : starCharacterPairing phi (rho - chi0) = 0 := by
    refine Submodule.span_induction ?_ ?_ ?_ ?_ hphiAdjusted
    · intro eta heta
      obtain ⟨xi, hxiS, rfl⟩ := heta
      exact hpairAdjusted hxiS
    · exact starCharacterPairing_zero_left _
    · intro x y _ _ hx hy
      rw [starCharacterPairing_add_left, hx, hy, add_zero]
    · intro a x _ hx
      rw [starCharacterPairing_smul_left, hx, mul_zero]
  have hphiSelf : starCharacterPairing phi phi = 0 := by
    rw [← hphiOrth]
    unfold starCharacterPairing twistedCharacterPairing
    congr 1
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : (a : Γ) ∈ A
    · change
        ((rho a - chi0 a) * (if (a : Γ) ∈ A then 1 else 0)) *
            star ((rho a - chi0 a) *
              (if (a : Γ) ∈ A then 1 else 0)) =
          ((rho a - chi0 a) * (if (a : Γ) ∈ A then 1 else 0)) *
            star (rho a - chi0 a)
      rw [if_pos ha]
      simp
    · change
        ((rho a - chi0 a) * (if (a : Γ) ∈ A then 1 else 0)) *
            star ((rho a - chi0 a) *
              (if (a : Γ) ∈ A then 1 else 0)) =
          ((rho a - chi0 a) * (if (a : Γ) ∈ A then 1 else 0)) *
            star (rho a - chi0 a)
      rw [if_neg ha]
      simp
  have hphiNorm : classFunctionNormSq phi = 0 := by
    rw [starCharacterPairing_self_eq_classFunctionNormSq] at hphiSelf
    exact Complex.ofReal_injective hphiSelf
  have hphiZero : phi = 0 :=
    (classFunctionNormSq_eq_zero_iff phi).mp hphiNorm
  have part_a :
      ∀ a : L, (a : Γ) ∈ A →
        rho a =
          ∑ xi ∈ S,
            (star (c xi) / starCharacterPairing xi xi) * xi a := by
    intro a ha
    have hz := congrFun (congrArg Subtype.val hphiZero) a
    change
      (rho a - chi0 a) * (if (a : Γ) ∈ A then 1 else 0) = 0 at hz
    rw [if_pos ha, mul_one] at hz
    rw [sub_eq_zero.mp hz]
    simp [chi0]
  refine ⟨?_, ?_⟩
  · intro a ha
    exact part_a a ha
  · rw [starCharacterPairing_eq_sum_of_mem_supportedOn (invDade_on ddA chi)]
    have hsumExpand :
        (∑ a ∈ Finset.univ.filter (fun a : L ↦ (a : Γ) ∈ A),
            rho a * star (rho a)) =
          ∑ a ∈ Finset.univ.filter (fun a : L ↦ (a : Γ) ∈ A),
            (∑ xi ∈ S,
                (star (c xi) / starCharacterPairing xi xi) * xi a) *
              star (∑ mu ∈ S,
                (star (c mu) / starCharacterPairing mu mu) * mu a) := by
      apply Finset.sum_congr rfl
      intro a ha
      have haA := (Finset.mem_filter.mp ha).2
      rw [part_a a haA]
    change (Nat.card L : ℂ)⁻¹ *
      (∑ a ∈ Finset.univ.filter (fun a : L ↦ (a : Γ) ∈ A),
        rho a * star (rho a)) = _
    rw [hsumExpand]
    rw [Finset.mul_sum]
    simp only [Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    simp only [star_sum, star_mul, star_div₀]
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro xi hxi
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro mu hmu
    have hxiT := hST hxi
    have hmuT := hST hmu
    have hmuPairStar :
        star (starCharacterPairing mu mu) =
          starCharacterPairing mu mu := by
      rw [starCharacterPairing_self_eq_classFunctionNormSq]
      simp
    rw [star_star, hmuPairStar]
    have hfilter :
        Finset.univ.filter (fun x : L ↦ (x : Γ) ∈ A) =
          Finset.univ.filter
            (fun x : L ↦ x ∈ subgroupNonidentity H) := by
      ext x
      simp [A, subgroupNonidentity, hmapMem]
    rw [hfilter]
    unfold invDadeSeqIndU
    simp only [c, A]
    have hcard :
        ((H.index : ℂ) * (Nat.card H : ℂ)) =
          (Nat.card L : ℂ) := by exact_mod_cast H.index_mul_card
    rw [hcard,
      starPairing_seqIndT_subgroupNonidentity H hxiT hmuT]
    calc
      _ = ∑ x ∈ Finset.univ.filter
            (fun x : L ↦ x ∈ subgroupNonidentity H),
          ((Nat.card L : ℂ)⁻¹ *
              star (invDadeSeqIndCoefficient ddA xi0 chi xi) *
              (starCharacterPairing xi xi)⁻¹ *
              invDadeSeqIndCoefficient ddA xi0 chi mu *
              (starCharacterPairing mu mu)⁻¹) *
            (xi x * star (mu x)) := by
        apply Finset.sum_congr rfl
        intro x _
        ring
      _ = ((Nat.card L : ℂ)⁻¹ *
              star (invDadeSeqIndCoefficient ddA xi0 chi xi) *
              (starCharacterPairing xi xi)⁻¹ *
              invDadeSeqIndCoefficient ddA xi0 chi mu *
              (starCharacterPairing mu mu)⁻¹) *
            (∑ x ∈ Finset.univ.filter
              (fun x : L ↦ x ∈ subgroupNonidentity H),
                xi x * star (mu x)) := by
        rw [Finset.mul_sum]
      _ = _ := by ring

/-! ## Peterfalvi (7.8): subtracting a linear induced character -/

/-- The character induced from the trivial character of `H`. -/
def dadeInducedTrivial
    {L : Subgroup Γ} (H : Subgroup L) : ClassFunction L ℂ :=
  ClassFunction.induce H
    ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
      ClassFunction H ℂ)

/-- The Dade image denoted `beta` in Peterfalvi (7.8). -/
def dadeInd1Beta
    {G L : Subgroup Γ} (H : Subgroup L)
    (ddA : DadeHypothesis G L
      (subgroupNonidentity (H.map L.subtype)))
    (zeta : ClassFunction L ℂ) : ClassFunction G ℂ :=
  Dade ddA (dadeInducedTrivial H - zeta)

/-- The weighted coherent sum `sumSnu` occurring in (7.8). -/
def dadeInd1CoherentSum
    {G L : Subgroup Γ} (H : Subgroup L)
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ) :
    ClassFunction G ℂ :=
  ∑ xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥,
    (xi 1 / (H.index : ℂ) / characterPairing xi xi) • nu xi

/-- Orthogonality to the image of the nontrivial sequential-induction
family. -/
def OrthogonalToSeqIndImage
    {G L : Subgroup Γ} (H : Subgroup L)
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (psi : ClassFunction G ℂ) : Prop :=
  ∀ xi ∈ seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥,
    starCharacterPairing (nu xi) psi = 0

/-- The full conclusion of Peterfalvi (7.8).  The integer field is the
source coefficient `a`; its coercion to `ℂ` is used in `decomposition`.
The two ordered conclusions use the real squared norm. -/
structure DadeInd1SubLinConclusion
    {G L : Subgroup Γ} (H : Subgroup L)
    (ddA : DadeHypothesis G L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (zeta : IrreducibleCharacter L ℂ) : Type (u + 1) where
  image_orthogonal_one :
    OrthogonalToSeqIndImage H nu
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ)
  beta_pairing_one :
    starCharacterPairing
      (dadeInd1Beta H ddA (zeta : ClassFunction L ℂ))
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) = 1
  beta_virtual :
    ClassFunction.IsVirtual
      (dadeInd1Beta H ddA (zeta : ClassFunction L ℂ))
  gamma : ClassFunction G ℂ
  image_orthogonal_gamma : OrthogonalToSeqIndImage H nu gamma
  gamma_pairing_one :
    starCharacterPairing gamma
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) = 0
  coefficient : ℤ
  decomposition :
    dadeInd1Beta H ddA (zeta : ClassFunction L ℂ) =
      ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
        ClassFunction G ℂ) - nu (zeta : ClassFunction L ℂ) +
        (coefficient : ℂ) • dadeInd1CoherentSum H nu + gamma
  norm_bounds :
    (H.index : ℝ) ≤ ((Nat.card H : ℝ) - 1) / 2 →
      1 - (H.index : ℝ) / (Nat.card H : ℝ) ≤
          classFunctionNormSq
              (invDade ddA (nu (zeta : ClassFunction L ℂ))) ∧
        classFunctionNormSq gamma ≤ (H.index : ℝ) - 1
  orthogonal_irreducible :
    ∀ chi : IrreducibleCharacter G ℂ,
      OrthogonalToSeqIndImage H nu (chi : ClassFunction G ℂ) →
      (∀ a : L,
          (a : Γ) ∈ subgroupNonidentity (H.map L.subtype) →
          invDade ddA (chi : ClassFunction G ℂ) a =
            starCharacterPairing
              (dadeInd1Beta H ddA (zeta : ClassFunction L ℂ)) chi) ∧
        classFunctionNormSq (invDade ddA (chi : ClassFunction G ℂ)) =
          ((subgroupNonidentity (H.map L.subtype)).ncard : ℝ) /
              (Nat.card L : ℝ) *
            Complex.normSq
              (starCharacterPairing
                (dadeInd1Beta H ddA (zeta : ClassFunction L ℂ)) chi)

private theorem virtual_pairing_isInt_cover
    {Q : Type u} [Group Q] [Fintype Q]
    {phi psi : ClassFunction Q ℂ}
    (hphi : ClassFunction.IsVirtual phi)
    (hpsi : ClassFunction.IsVirtual psi) :
    ∃ z : ℤ, starCharacterPairing phi psi = (z : ℂ) := by
  obtain ⟨v, rfl⟩ := hphi
  obtain ⟨w, rfl⟩ := hpsi
  rw [starCharacterPairing_realize_eq_characterPairing_cover]
  exact ⟨coeffDot v w, VirtualCharacter.characterPairing_realize v w⟩

private theorem pairing_self_sub_of_orthogonal_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ)
    (horth : starCharacterPairing phi psi = 0) :
    classFunctionNormSq (phi - psi) =
      classFunctionNormSq phi + classFunctionNormSq psi := by
  have horth' : starCharacterPairing psi phi = 0 := by
    calc
      starCharacterPairing psi phi =
          star (starCharacterPairing phi psi) :=
        starCharacterPairing_conj_symm psi phi
      _ = 0 := by simp [horth]
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing]
  rw [starCharacterPairing_sub_left_cover,
    starCharacterPairing_sub_right_cover,
    starCharacterPairing_sub_right_cover, horth, horth']
  simp

private theorem classFunctionNormSq_add_of_orthogonal_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (phi psi : ClassFunction Q ℂ)
    (horth : starCharacterPairing phi psi = 0) :
    classFunctionNormSq (phi + psi) =
      classFunctionNormSq phi + classFunctionNormSq psi := by
  have horth' : starCharacterPairing psi phi = 0 := by
    calc
      starCharacterPairing psi phi =
          star (starCharacterPairing phi psi) :=
        starCharacterPairing_conj_symm psi phi
      _ = 0 := by rw [horth]; simp
  rw [classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing,
    classFunctionNormSq_eq_re_starCharacterPairing]
  rw [starCharacterPairing_add_left,
    starCharacterPairing_add_right,
    starCharacterPairing_add_right, horth, horth']
  simp

private theorem classFunctionNormSq_smul_cover
    {Q : Type u} [Group Q] [Fintype Q]
    (a : ℂ) (phi : ClassFunction Q ℂ) :
    classFunctionNormSq (a • phi) =
      Complex.normSq a * classFunctionNormSq phi := by
  unfold classFunctionNormSq
  simp only [ClassFunction.smul_apply, smul_eq_mul, Complex.normSq_mul,
    Finset.mul_sum]
  ring

private theorem starCharacterPairing_trivial_right_eq_characterPairing
    {Q : Type u} [Group Q] [Fintype Q]
    (f : ClassFunction Q ℂ) :
    starCharacterPairing f
        ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
          ClassFunction Q ℂ) =
      characterPairing f
        ((IrreducibleCharacter.trivial : IrreducibleCharacter Q ℂ) :
          ClassFunction Q ℂ) := by
  apply starCharacterPairing_eq_characterPairing_of_star_apply_eq_inv
  intro x
  simp [IrreducibleCharacter.trivial_apply]

private theorem starCharacterPairing_DadeSetIndicator_eq_trivial
    {G L : Subgroup Γ} {A : Set Γ}
    (ddA : DadeHypothesis G L A) {f : ClassFunction L ℂ}
    (hf : f ∈ ClassFunction.supportedOn {a : L | (a : Γ) ∈ A}) :
    starCharacterPairing f (DadeSetIndicator ddA) =
      starCharacterPairing f
        ((IrreducibleCharacter.trivial : IrreducibleCharacter L ℂ) :
          ClassFunction L ℂ) := by
  rw [starCharacterPairing_eq_sum_of_mem_supportedOn hf,
    starCharacterPairing_eq_sum_of_mem_supportedOn hf]
  congr 1
  apply Finset.sum_congr rfl
  intro a ha
  have haA : (a : Γ) ∈ A := (Finset.mem_filter.mp ha).2
  simp [DadeSetIndicator_apply, haA,
    IrreducibleCharacter.trivial_apply]

/-- Peterfalvi (7.8).  Bundling `zeta` as an irreducible character replaces
the source's separate `zeta ∈ irr L` premise. -/
noncomputable def Dade_Ind1_sub_lin
    {G L : Subgroup Γ} (H : Subgroup L) [H.Normal]
    (ddA : DadeHypothesis G L
      (subgroupNonidentity (H.map L.subtype)))
    (nu : ClassFunction L ℂ →ₗ[ℂ] ClassFunction G ℂ)
    (zeta : IrreducibleCharacter L ℂ)
    (hcoh : coherent_with
      (↑(seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥) :
        Set (ClassFunction L ℂ))
      (nonidentitySet L) (Dade ddA) nu)
    (hcalS : 1 < (seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥).card)
    (hzeta : (zeta : ClassFunction L ℂ) ∈
      seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥)
    (hzeta1 : zeta 1 = (H.index : ℂ)) :
    DadeInd1SubLinConclusion H ddA nu zeta := by
  classical
  letI : Invertible (Nat.card G : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card L : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card H : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  let calS : Finset (ClassFunction L ℂ) :=
    seqIndD (k := ℂ) H (⊤ : Subgroup H) ⊥
  let calT : Finset (ClassFunction L ℂ) := seqIndT (k := ℂ) H
  let ind1 : ClassFunction L ℂ := dadeInducedTrivial H
  let beta : ClassFunction G ℂ :=
    dadeInd1Beta H ddA (zeta : ClassFunction L ℂ)
  let sumSnu : ClassFunction G ℂ := dadeInd1CoherentSum H nu
  let oneG : ClassFunction G ℂ :=
    ((IrreducibleCharacter.trivial : IrreducibleCharacter G ℂ) :
      ClassFunction G ℂ)
  have hcalST : calS ⊆ calT := by
    intro xi hxi
    exact seqInd_subT H _ hxi
  have hcalSOrth : Set.Pairwise (↑calS : Set (ClassFunction L ℂ))
      (fun phi psi ↦ characterPairing phi psi = 0) := by
    exact seqInd_orthogonal H _
  have hmemClosure {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      xi ∈ AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ)) :=
    AddSubgroup.subset_closure hxi
  have hnuVirtual {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      ClassFunction.IsVirtual (nu xi) :=
    hcoh.mapsToVirtual xi (hmemClosure hxi)
  have hnuPair {xi mu : ClassFunction L ℂ}
      (hxi : xi ∈ calS) (hmu : mu ∈ calS) :
      starCharacterPairing (nu xi) (nu mu) =
        characterPairing xi mu := by
    obtain ⟨v, hv⟩ := hnuVirtual hxi
    obtain ⟨w, hw⟩ := hnuVirtual hmu
    rw [← hv, ← hw,
      starCharacterPairing_realize_eq_characterPairing_cover]
    rw [hv, hw]
    exact hcoh.isometry xi (hmemClosure hxi) mu (hmemClosure hmu)
  have hnuNorm {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      classFunctionNormSq (nu xi) =
        (characterPairing xi xi).re := by
    rw [classFunctionNormSq_eq_re_starCharacterPairing, hnuPair hxi hxi]
  have hexistsOther :
      ∃ eta ∈ calS, eta ≠ (zeta : ClassFunction L ℂ) := by
    obtain ⟨x, hx, y, hy, hxy⟩ := Finset.one_lt_card.mp hcalS
    by_cases hxz : x = (zeta : ClassFunction L ℂ)
    · refine ⟨y, hy, ?_⟩
      intro hyz
      exact hxy (hxz.trans hyz.symm)
    · exact ⟨x, hx, hxz⟩
  have hbetaVirtual : ClassFunction.IsVirtual beta := by
    obtain ⟨z, hz, hzOn⟩ := cfInd1_sub_lin_vchar H
      (hcalST hzeta)
      hzeta1
    have hzA : VirtualCharacter.realize z ∈
        ClassFunction.supportedOn
          {a : L |
            (a : Γ) ∈ subgroupNonidentity (H.map L.subtype)} := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro a ha
      apply ClassFunction.eq_zero_of_mem_supportedOn hzOn
      intro haH
      apply ha
      have ha1 : (a : Γ) ≠ 1 := by
        intro ha1
        apply haH.2
        exact Subtype.ext ha1
      refine ⟨?_, ha1⟩
      exact ⟨a, haH.1, rfl⟩
    refine ⟨Dade_virtualCharacter ddA z, ?_⟩
    change VirtualCharacter.realize (Dade_virtualCharacter ddA z) = beta
    rw [← Dade_vchar ddA z hzA, hz]
    rfl
  have hbetaOne : starCharacterPairing beta oneG = 1 := by
    have hmuOn : ind1 - (zeta : ClassFunction L ℂ) ∈
        ClassFunction.supportedOn
          {a : L |
            (a : Γ) ∈ subgroupNonidentity (H.map L.subtype)} := by
      obtain ⟨z, hz, hzOn⟩ := cfInd1_sub_lin_vchar H
        (hcalST hzeta) hzeta1
      change
        ClassFunction.induce H
            ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
              ClassFunction H ℂ) - (zeta : ClassFunction L ℂ) ∈
          ClassFunction.supportedOn
            {a : L |
              (a : Γ) ∈ subgroupNonidentity (H.map L.subtype)}
      rw [← hz]
      rw [ClassFunction.mem_supportedOn_iff]
      intro a ha
      apply ClassFunction.eq_zero_of_mem_supportedOn hzOn
      intro haH
      apply ha
      have ha1 : (a : Γ) ≠ 1 := by
        intro ha1
        apply haH.2
        exact Subtype.ext ha1
      exact ⟨⟨a, haH.1, rfl⟩, ha1⟩
    rw [show beta = Dade ddA (ind1 - (zeta : ClassFunction L ℂ)) by rfl]
    rw [invDade_reciprocity ddA oneG _ hmuOn, invDade_cfun1]
    rw [starCharacterPairing_DadeSetIndicator_eq_trivial ddA hmuOn]
    rw [starCharacterPairing_trivial_right_eq_characterPairing]
    unfold ind1 dadeInducedTrivial
    simp only [sub_eq_add_neg, characterPairing_add_left]
    rw [ClassFunction.frobeniusReciprocity H]
    have hrestrict :
        ClassFunction.restrict H
            ((IrreducibleCharacter.trivial : IrreducibleCharacter L ℂ) :
              ClassFunction L ℂ) =
          ((IrreducibleCharacter.trivial : IrreducibleCharacter H ℂ) :
            ClassFunction H ℂ) := by
      apply ClassFunction.ext
      intro x
      simp [IrreducibleCharacter.trivial_apply]
    rw [hrestrict, IrreducibleCharacter.characterPairing_self]
    have hzetaOrth := seqInd_ortho_1 H (⊤ : Subgroup H) ⊥ hzeta
    have hnegOrth :
        characterPairing (-(zeta : ClassFunction L ℂ))
          ((IrreducibleCharacter.trivial : IrreducibleCharacter L ℂ) :
            ClassFunction L ℂ) = 0 := by
      rw [← neg_one_smul ℂ (zeta : ClassFunction L ℂ)]
      rw [characterPairing_smul_left, hzetaOrth, mul_zero]
    exact add_eq_left.mpr hnegOrth
  have hsupportEq :
      {a : L |
          (a : Γ) ∈ subgroupNonidentity (H.map L.subtype)} =
        subgroupNonidentity H := by
    ext a
    constructor
    · rintro ⟨⟨b, hb, hba⟩, ha1⟩
      have hbaL : b = a := Subtype.ext hba
      subst a
      refine ⟨hb, ?_⟩
      intro hb1
      apply ha1
      simpa using congrArg Subtype.val hb1
    · rintro ⟨haH, ha1⟩
      refine ⟨⟨a, haH, rfl⟩, ?_⟩
      intro haGamma
      apply ha1
      exact Subtype.ext haGamma
  have hdotOne {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
      starCharacterPairing (nu xi) oneG =
        (xi 1 / (H.index : ℂ)) *
          starCharacterPairing (nu (zeta : ClassFunction L ℂ)) oneG := by
    have hxiClosure := hmemClosure hxi
    have hxiOn :
        xi - (xi 1 / (H.index : ℂ)) • (zeta : ClassFunction L ℂ) ∈
          ClassFunction.supportedOn (nonidentitySet L) := by
      rw [ClassFunction.mem_supportedOn_iff]
      intro x hx
      have hx1 : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
      subst x
      simp [hzeta1, Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite]
    have hxiOnA :
        xi - (xi 1 / (H.index : ℂ)) • (zeta : ClassFunction L ℂ) ∈
          ClassFunction.supportedOn
            {a : L |
              (a : Γ) ∈ subgroupNonidentity (H.map L.subtype)} := by
      rw [hsupportEq]
      exact seqInd_sub_lin_on H hzeta hzeta1 hxi
    have hdiffClosure :
        xi - (xi 1 / (H.index : ℂ)) • (zeta : ClassFunction L ℂ) ∈
          AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ)) := by
      obtain ⟨n, hn⟩ := dvd_index_seqInd1 H hxi
      rw [hn]
      exact (AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ))).sub_mem
        hxiClosure (by
          have hm := (AddSubgroup.closure
            (↑calS : Set (ClassFunction L ℂ))).nsmul_mem
              (hmemClosure hzeta) n
          rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n
            (zeta : ClassFunction L ℂ)] at hm
          exact hm)
    have hagree := hcoh.agrees _ hdiffClosure hxiOn
    have hdot :
        starCharacterPairing
          (nu xi - (xi 1 / (H.index : ℂ)) •
            nu (zeta : ClassFunction L ℂ)) oneG = 0 := by
      rw [← map_smul, ← map_sub, hagree]
      rw [invDade_reciprocity ddA oneG _ hxiOnA, invDade_cfun1]
      rw [starCharacterPairing_DadeSetIndicator_eq_trivial ddA hxiOnA]
      rw [starCharacterPairing_sub_left_cover,
        starCharacterPairing_smul_left]
      simp only [starCharacterPairing_trivial_right_eq_characterPairing]
      rw [seqInd_ortho_1 H (⊤ : Subgroup H) ⊥ hxi,
        seqInd_ortho_1 H (⊤ : Subgroup H) ⊥ hzeta]
      simp
    rw [starCharacterPairing_sub_left_cover,
      starCharacterPairing_smul_left] at hdot
    exact sub_eq_zero.mp hdot
  have hzetaDotZero :
      starCharacterPairing (nu (zeta : ClassFunction L ℂ)) oneG = 0 := by
    by_contra hzetaDot
    obtain ⟨vz, hvz⟩ := hnuVirtual hzeta
    have hvzPair :
        characterPairing (VirtualCharacter.realize vz)
            (VirtualCharacter.realize vz) = 1 := by
      calc
        characterPairing (VirtualCharacter.realize vz)
            (VirtualCharacter.realize vz) =
          starCharacterPairing (VirtualCharacter.realize vz)
            (VirtualCharacter.realize vz) :=
              (starCharacterPairing_realize_eq_characterPairing_cover vz vz).symm
        _ = starCharacterPairing
            (nu (zeta : ClassFunction L ℂ))
            (nu (zeta : ClassFunction L ℂ)) := by rw [hvz]
        _ = characterPairing (zeta : ClassFunction L ℂ)
            (zeta : ClassFunction L ℂ) := hnuPair hzeta hzeta
        _ = 1 := IrreducibleCharacter.characterPairing_self zeta
    have hvzNorm : normSq vz = 1 := by
      apply Int.cast_injective (α := ℂ)
      calc
        (normSq vz : ℂ) =
            characterPairing (VirtualCharacter.realize vz)
              (VirtualCharacter.realize vz) := by
          simpa [normSq] using
            (VirtualCharacter.characterPairing_realize vz vz).symm
        _ = (1 : ℂ) := hvzPair
        _ = ((1 : ℤ) : ℂ) := by norm_num
    obtain ⟨eta, epsilon, hepsilon, hvzSingle⟩ :=
      eq_signed_single_of_normSq_eq_one vz hvzNorm
    have hnuZeta :
        nu (zeta : ClassFunction L ℂ) =
          (epsilon : ℂ) • (eta : ClassFunction G ℂ) := by
      calc
        nu (zeta : ClassFunction L ℂ) =
            VirtualCharacter.realize vz := hvz.symm
        _ = (epsilon : ℂ) • (eta : ClassFunction G ℂ) := by
          rw [hvzSingle, VirtualCharacter.realize_single]
    have hetaTrivial : eta = IrreducibleCharacter.trivial := by
      by_contra hetaNe
      apply hzetaDot
      rw [hnuZeta, starCharacterPairing_smul_left,
        starCharacterPairing_trivial_right_eq_characterPairing,
        IrreducibleCharacter.characterPairing_eq_zero hetaNe]
      simp
    obtain ⟨phi, hphi, hphiNe⟩ := hexistsOther
    have horthNu := hnuPair hphi hzeta
    rw [hcalSOrth hphi hzeta hphiNe] at horthNu
    rw [hnuZeta, hetaTrivial,
      starCharacterPairing_smul_right] at horthNu
    have hphiOne : starCharacterPairing (nu phi) oneG = 0 := by
      rcases hepsilon with hepsilon | hepsilon
      · subst epsilon
        simpa using horthNu
      · subst epsilon
        simpa using horthNu
    have hrelation := hdotOne hphi
    rw [hphiOne] at hrelation
    have hphiDegree : phi 1 ≠ 0 := seqInd1_neq0 H (hcalST hphi)
    have hindex : (H.index : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
    exact hzetaDot ((mul_eq_zero.mp hrelation.symm).resolve_left
      (div_ne_zero hphiDegree hindex))
  have himageOne : OrthogonalToSeqIndImage H nu oneG := by
    intro xi hxi
    rw [hdotOne hxi, hzetaDotZero, mul_zero]
  let X : ClassFunction G ℂ :=
    ∑ xi ∈ calS,
      (starCharacterPairing (beta - oneG) (nu xi) /
          starCharacterPairing (nu xi) (nu xi)) • nu xi
  let gamma : ClassFunction G ℂ := beta - oneG - X
  have hgammaImage : OrthogonalToSeqIndImage H nu gamma := by
    intro xi hxi
    change xi ∈ calS at hxi
    unfold gamma X
    rw [starCharacterPairing_sub_right_cover,
      starCharacterPairing_finset_sum_right_cover]
    rw [Finset.sum_eq_single xi]
    · rw [starCharacterPairing_smul_right]
      have hnz : starCharacterPairing (nu xi) (nu xi) ≠ 0 := by
        rw [hnuPair hxi hxi]
        exact cfnorm_seqInd_neq0 H hxi
      have hselfStar :
          star (starCharacterPairing (nu xi) (nu xi)) =
            starCharacterPairing (nu xi) (nu xi) := by
        rw [starCharacterPairing_self_eq_classFunctionNormSq]
        simp
      change (starRingEnd ℂ) (starCharacterPairing (nu xi) (nu xi)) =
        starCharacterPairing (nu xi) (nu xi) at hselfStar
      have hquot :
          star (starCharacterPairing (beta - oneG) (nu xi) /
              starCharacterPairing (nu xi) (nu xi)) =
            star (starCharacterPairing (beta - oneG) (nu xi)) /
              starCharacterPairing (nu xi) (nu xi) := by
        change (starRingEnd ℂ)
            (starCharacterPairing (beta - oneG) (nu xi) /
              starCharacterPairing (nu xi) (nu xi)) =
          (starRingEnd ℂ)
              (starCharacterPairing (beta - oneG) (nu xi)) /
            starCharacterPairing (nu xi) (nu xi)
        rw [map_div₀, hselfStar]
      rw [starCharacterPairing_conj_symm, hquot]
      field_simp <;> ring
    · intro eta heta hne
      rw [starCharacterPairing_smul_right, hnuPair hxi heta]
      rw [hcalSOrth hxi heta hne.symm]
      simp
    · intro hnot
      exact (hnot hxi).elim
  have hgammaOne : starCharacterPairing gamma oneG = 0 := by
    have honePair : starCharacterPairing oneG oneG = 1 := by
      unfold oneG starCharacterPairing twistedCharacterPairing
      simp [IrreducibleCharacter.trivial_apply,
        Nat.cast_ne_zero.mpr Nat.card_pos.ne']
    unfold gamma X
    rw [starCharacterPairing_sub_left_cover,
      starCharacterPairing_sub_left_cover, hbetaOne, honePair,
      sub_self, zero_sub]
    rw [starCharacterPairing_finset_sum_left_cover]
    apply neg_eq_zero.mpr
    apply Finset.sum_eq_zero
    intro xi hxi
    rw [starCharacterPairing_smul_left, himageOne xi hxi, mul_zero]
  let aC : ℂ := starCharacterPairing beta
    (nu (zeta : ClassFunction L ℂ)) + 1
  have haExists : ∃ z : ℤ,
      starCharacterPairing beta (nu (zeta : ClassFunction L ℂ)) =
        (z : ℂ) :=
    virtual_pairing_isInt_cover hbetaVirtual (hnuVirtual hzeta)
  have haNonempty : Nonempty {z : ℤ //
      starCharacterPairing beta (nu (zeta : ClassFunction L ℂ)) =
        (z : ℂ)} := by
    rcases haExists with ⟨z, hz⟩
    exact ⟨⟨z, hz⟩⟩
  let aData := Classical.choice haNonempty
  let a : ℤ := aData.1
  have ha : starCharacterPairing beta
      (nu (zeta : ClassFunction L ℂ)) = (a : ℂ) :=
    aData.2
  have haC : aC = ((a + 1 : ℤ) : ℂ) := by
    simp [aC, ha]
  let coeff : ℤ := a + 1
  have hX : X = -nu (zeta : ClassFunction L ℂ) +
      (coeff : ℂ) • sumSnu := by
    have hmuOnA :
        ind1 - (zeta : ClassFunction L ℂ) ∈
          ClassFunction.supportedOn
            {x : L |
              (x : Γ) ∈ subgroupNonidentity (H.map L.subtype)} := by
      rw [hsupportEq]
      unfold ind1 dadeInducedTrivial
      exact cfInd1_sub_lin_on H (hcalST hzeta) hzeta1
    have hindT : ind1 ∈ seqIndT (k := ℂ) H := by
      unfold ind1 dadeInducedTrivial
      exact mem_seqIndT H IrreducibleCharacter.trivial
    have hzetaNeInd : (zeta : ClassFunction L ℂ) ≠ ind1 := by
      have hzetaFilter := hzeta
      rw [seqIndC1_rem] at hzetaFilter
      simpa [ind1, dadeInducedTrivial] using
        (Finset.mem_erase.mp hzetaFilter).1
    unfold X sumSnu dadeInd1CoherentSum coeff
    apply ClassFunction.ext
    intro g
    simp only [ClassFunction.add_apply, ClassFunction.neg_apply,
      ClassFunction.finset_sum_apply, ClassFunction.smul_apply, smul_eq_mul]
    have hnegEval :
        -(nu (zeta : ClassFunction L ℂ)) g =
          ∑ xi ∈ calS,
            if xi = (zeta : ClassFunction L ℂ) then
              -(nu xi) g
            else 0 := by
      rw [Finset.sum_eq_single (zeta : ClassFunction L ℂ)]
      · simp
      · intro xi _ hne
        simp [hne]
      · intro hnot
        exact (hnot hzeta).elim
    rw [Finset.mul_sum, hnegEval, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro xi hxi
    by_cases hix : xi = (zeta : ClassFunction L ℂ)
    · subst xi
      have honeZeta :
          starCharacterPairing oneG
              (nu (zeta : ClassFunction L ℂ)) = 0 := by
        rw [starCharacterPairing_conj_symm, hzetaDotZero]
        simp
      rw [starCharacterPairing_sub_left_cover, honeZeta, sub_zero, ha,
        hnuPair hzeta hzeta,
        IrreducibleCharacter.characterPairing_self, hzeta1]
      have hindex : (H.index : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
      field_simp [hindex]
      push_cast
      ring
    · have horth := hcalSOrth hxi hzeta hix
      have hadjusted := hcoh.agrees
        (xi - (xi 1 / (H.index : ℂ)) • (zeta : ClassFunction L ℂ))
        (by
          obtain ⟨n, hn⟩ := dvd_index_seqInd1 H hxi
          rw [hn]
          exact (AddSubgroup.closure (↑calS : Set (ClassFunction L ℂ))).sub_mem
            (hmemClosure hxi)
            (by
              have hm := (AddSubgroup.closure
                (↑calS : Set (ClassFunction L ℂ))).nsmul_mem
                  (hmemClosure hzeta) n
              rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n
                (zeta : ClassFunction L ℂ)] at hm
              exact hm))
        (by
          rw [ClassFunction.mem_supportedOn_iff]
          intro x hx
          have hx1 : x = 1 := by simpa [nonidentitySet] using not_not.mp hx
          subst x
          simp [hzeta1, Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite])
      have hadjustedOnA :
          xi - (xi 1 / (H.index : ℂ)) • (zeta : ClassFunction L ℂ) ∈
            ClassFunction.supportedOn
              {x : L |
                (x : Γ) ∈ subgroupNonidentity (H.map L.subtype)} := by
        rw [hsupportEq]
        exact seqInd_sub_lin_on H hzeta hzeta1 hxi
      have hqStar : star (xi 1 / (H.index : ℂ)) =
          xi 1 / (H.index : ℂ) := by
        obtain ⟨n, hn⟩ := dvd_index_seqInd1 H hxi
        rw [hn]
        simp
      have hxiNeInd : xi ≠ ind1 := by
        have hxiFilter := hxi
        unfold calS at hxiFilter
        rw [seqIndC1_rem] at hxiFilter
        simpa [ind1, dadeInducedTrivial] using
          (Finset.mem_erase.mp hxiFilter).1
      have hpairAdjusted :
          starCharacterPairing beta
              (nu (xi - (xi 1 / (H.index : ℂ)) •
                (zeta : ClassFunction L ℂ))) =
            xi 1 / (H.index : ℂ) := by
        rw [hadjusted]
        change starCharacterPairing
            (Dade ddA (ind1 - (zeta : ClassFunction L ℂ)))
            (Dade ddA (xi - (xi 1 / (H.index : ℂ)) •
              (zeta : ClassFunction L ℂ))) = _
        rw [Dade_isometry ddA _ _ hmuOnA hadjustedOnA]
        rw [starCharacterPairing_sub_left_cover,
          starCharacterPairing_sub_right_cover,
          starCharacterPairing_sub_right_cover,
          starCharacterPairing_smul_right,
          starCharacterPairing_smul_right, hqStar]
        rw [seqIndT_star_orthogonal H hindT (hcalST hxi) hxiNeInd.symm,
          seqIndT_star_orthogonal H hindT (hcalST hzeta) hzetaNeInd.symm,
          seqIndT_star_orthogonal H (hcalST hzeta) (hcalST hxi)
            (Ne.symm hix),
          seqInd_starPairing_eq_characterPairing H
            (hcalST hzeta) (hcalST hzeta),
          IrreducibleCharacter.characterPairing_self]
        ring
      rw [map_sub, map_smul, starCharacterPairing_sub_right_cover,
        starCharacterPairing_smul_right, hqStar] at hpairAdjusted
      have hcoefficient :
          starCharacterPairing beta (nu xi) =
            (xi 1 / (H.index : ℂ)) *
              (starCharacterPairing beta
                (nu (zeta : ClassFunction L ℂ)) + 1) := by
        linear_combination hpairAdjusted
      have honeXi : starCharacterPairing oneG (nu xi) = 0 := by
        rw [starCharacterPairing_conj_symm, himageOne xi hxi]
        simp
      rw [starCharacterPairing_sub_left_cover, honeXi, sub_zero,
        hnuPair hxi hxi, hcoefficient, ha, if_neg hix]
      push_cast
      ring
  have hdecomp :
      beta = oneG - nu (zeta : ClassFunction L ℂ) +
        (coeff : ℂ) • sumSnu + gamma := by
    unfold gamma
    rw [hX]
    abel
  have hindOne : ind1 1 = (H.index : ℂ) := by
    unfold ind1 dadeInducedTrivial
    rw [ClassFunction.induce_one]
    simp [IrreducibleCharacter.trivial_apply]
  have hindT : ind1 ∈ seqIndT (k := ℂ) H := by
    unfold ind1 dadeInducedTrivial
    exact mem_seqIndT H IrreducibleCharacter.trivial
  have hindValue {x : L} (hx : x ∈ H) :
      ind1 x = (H.index : ℂ) := by
    unfold ind1 dadeInducedTrivial
    rw [ClassFunction.induce_apply_formula]
    have hconj (y : L) : y⁻¹ * x * y ∈ H := by
      simpa only [inv_inv] using
        (inferInstance : H.Normal).conj_mem x hx y⁻¹
    simp_rw [dif_pos (hconj _)]
    simp only [IrreducibleCharacter.trivial_apply, Finset.sum_const,
      nsmul_eq_mul, mul_one, Finset.card_univ,
      Nat.card_eq_fintype_card]
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    have hHcard : (Nat.card H : ℂ) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hcard :
        (H.index : ℂ) * (Nat.card H : ℂ) =
          (Nat.card L : ℂ) := by
      exact_mod_cast H.index_mul_card
    rw [← hcard]
    field_simp
  have hindNorm :
      starCharacterPairing ind1 ind1 = (H.index : ℂ) := by
    rw [seqInd_starPairing_eq_characterPairing H hindT hindT]
    unfold ind1 dadeInducedTrivial
    rw [ClassFunction.frobeniusReciprocity H]
    have hrestrictInd :
        ClassFunction.restrict H
            (ClassFunction.induce H
              ((IrreducibleCharacter.trivial :
                  IrreducibleCharacter H ℂ) : ClassFunction H ℂ)) =
          (H.index : ℂ) •
            ((IrreducibleCharacter.trivial :
                IrreducibleCharacter H ℂ) : ClassFunction H ℂ) := by
      apply ClassFunction.ext
      intro x
      simpa only [ClassFunction.restrict_apply,
        ClassFunction.smul_apply, IrreducibleCharacter.trivial_apply,
        smul_eq_mul, mul_one, ind1, dadeInducedTrivial] using
          (hindValue (x := (x : L)) x.property)
    rw [hrestrictInd, characterPairing_smul_right,
      IrreducibleCharacter.characterPairing_self, mul_one]
  have hbounds :
      (H.index : ℝ) ≤ ((Nat.card H : ℝ) - 1) / 2 →
        1 - (H.index : ℝ) / (Nat.card H : ℝ) ≤
            classFunctionNormSq
                (invDade ddA (nu (zeta : ClassFunction L ℂ))) ∧
          classFunctionNormSq gamma ≤ (H.index : ℝ) - 1 := by
    intro he
    obtain ⟨phi, hphi, hphiNe⟩ := hexistsOther
    have hphiT := hcalST hphi
    have hzetaT := hcalST hzeta
    have hindT : ind1 ∈ calT := by
      unfold calT ind1 dadeInducedTrivial
      exact mem_seqIndT H IrreducibleCharacter.trivial
    have hphiNeInd : phi ≠ ind1 := by
      have hphiFilter := hphi
      unfold calS at hphiFilter
      rw [seqIndC1_rem] at hphiFilter
      simpa [ind1, dadeInducedTrivial] using
        (Finset.mem_erase.mp hphiFilter).1
    have hzetaNeInd : (zeta : ClassFunction L ℂ) ≠ ind1 := by
      have hzetaFilter := hzeta
      rw [seqIndC1_rem] at hzetaFilter
      simpa [ind1, dadeInducedTrivial] using
        (Finset.mem_erase.mp hzetaFilter).1
    let S1 := ((calT.erase ind1).erase
      (zeta : ClassFunction L ℂ)).erase phi
    have hcalTsplit : calT = insert phi (insert ind1
        (insert (zeta : ClassFunction L ℂ) S1)) := by
      ext xi
      simp only [Finset.mem_insert]
      constructor
      · intro hxi
        by_cases hxphi : xi = phi
        · exact Or.inl hxphi
        by_cases hxind : xi = ind1
        · exact Or.inr (Or.inl hxind)
        by_cases hxzeta : xi = (zeta : ClassFunction L ℂ)
        · exact Or.inr (Or.inr (Or.inl hxzeta))
        · exact Or.inr (Or.inr (Or.inr (by
            apply Finset.mem_erase.mpr
            refine ⟨hxphi, ?_⟩
            apply Finset.mem_erase.mpr
            refine ⟨hxzeta, ?_⟩
            exact Finset.mem_erase.mpr ⟨hxind, hxi⟩)))
      · rintro (rfl | rfl | rfl | hxi)
        · exact hphiT
        · exact hindT
        · exact hzetaT
        · exact (Finset.mem_erase.mp
            (Finset.mem_erase.mp (Finset.mem_erase.mp hxi).2).2).2
    have hphiS1 : phi ∉ insert ind1 (insert (zeta : ClassFunction L ℂ) S1) := by
      simp [S1, hphiNeInd, hphiNe]
    have hexp := invDade_seqInd_sum H ddA phi
      (insert ind1 (insert (zeta : ClassFunction L ℂ) S1))
      (nu (zeta : ClassFunction L ℂ)) hcalTsplit hphiS1
    have hphiDegree : phi 1 ≠ 0 := seqInd1_neq0 H hphiT
    have hDadeAdjusted {xi : ClassFunction L ℂ} (hxiS : xi ∈ calS) :
        Dade ddA (invDadeSeqIndAdjusted phi xi) =
          nu (invDadeSeqIndAdjusted phi xi) := by
      let pi : ClassFunction L ℂ :=
        (phi 1) • xi - (xi 1) • phi
      have hpiClosure :
          pi ∈ AddSubgroup.closure
            (↑calS : Set (ClassFunction L ℂ)) := by
        obtain ⟨m, hm⟩ := Cnat_seqInd1 H hphi
        obtain ⟨n, hn⟩ := Cnat_seqInd1 H hxiS
        unfold pi
        rw [hm, hn]
        have hmMem := (AddSubgroup.closure
          (↑calS : Set (ClassFunction L ℂ))).nsmul_mem
            (hmemClosure hxiS) m
        have hnMem := (AddSubgroup.closure
          (↑calS : Set (ClassFunction L ℂ))).nsmul_mem
            (hmemClosure hphi) n
        rw [← Nat.cast_smul_eq_nsmul (R := ℂ) m xi] at hmMem
        rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n phi] at hnMem
        exact (AddSubgroup.closure
          (↑calS : Set (ClassFunction L ℂ))).sub_mem hmMem hnMem
      have hpiOn : pi ∈
          ClassFunction.supportedOn (nonidentitySet L) := by
        have hraw := sub_seqInd_on H hxiS hphi
        rw [ClassFunction.mem_supportedOn_iff] at hraw ⊢
        intro x hx
        apply hraw
        intro hxSharp
        apply hx
        simpa [nonidentitySet] using hxSharp.2
      have hagreePi := hcoh.agrees pi hpiClosure hpiOn
      have hscaled :
          invDadeSeqIndAdjusted phi xi = (phi 1)⁻¹ • pi := by
        unfold invDadeSeqIndAdjusted pi
        apply ClassFunction.ext
        intro x
        simp only [ClassFunction.sub_apply, ClassFunction.smul_apply,
          smul_eq_mul]
        field_simp [hphiDegree]
      rw [hscaled, map_smul, map_smul, hagreePi]
    have hcCal {xi : ClassFunction L ℂ} (hxiS : xi ∈ calS) :
        invDadeSeqIndCoefficient ddA phi
            (nu (zeta : ClassFunction L ℂ)) xi =
          characterPairing xi (zeta : ClassFunction L ℂ) := by
      unfold invDadeSeqIndCoefficient
      rw [hDadeAdjusted hxiS]
      unfold invDadeSeqIndAdjusted
      rw [map_sub, map_smul, starCharacterPairing_sub_left_cover,
        starCharacterPairing_smul_left,
        hnuPair hxiS hzeta, hnuPair hphi hzeta,
        hcalSOrth hphi hzeta hphiNe, mul_zero, sub_zero]
    have hcZeta :
        invDadeSeqIndCoefficient ddA phi
            (nu (zeta : ClassFunction L ℂ))
            (zeta : ClassFunction L ℂ) = 1 := by
      rw [hcCal hzeta, IrreducibleCharacter.characterPairing_self]
    have hcTail {xi : ClassFunction L ℂ} (hxi : xi ∈ S1) :
        invDadeSeqIndCoefficient ddA phi
            (nu (zeta : ClassFunction L ℂ)) xi = 0 := by
      have hxiErasePhi := Finset.mem_erase.mp hxi
      have hxiEraseZeta := Finset.mem_erase.mp hxiErasePhi.2
      have hxiEraseInd := Finset.mem_erase.mp hxiEraseZeta.2
      have hxiS : xi ∈ calS := by
        unfold calS
        rw [seqIndC1_filter]
        refine Finset.mem_filter.mpr ⟨?_, ?_⟩
        · exact hxiEraseInd.2
        · simpa [ind1, dadeInducedTrivial] using hxiEraseInd.1
      rw [hcCal hxiS]
      exact hcalSOrth hxiS hzeta hxiEraseZeta.1
    have hcInd :
        invDadeSeqIndCoefficient ddA phi
            (nu (zeta : ClassFunction L ℂ)) ind1 =
          (coeff : ℂ) := by
      have hadjusted :
          invDadeSeqIndAdjusted phi ind1 =
            (ind1 - (zeta : ClassFunction L ℂ)) +
              invDadeSeqIndAdjusted phi
                (zeta : ClassFunction L ℂ) := by
        unfold invDadeSeqIndAdjusted
        apply ClassFunction.ext
        intro x
        simp only [ClassFunction.add_apply, ClassFunction.sub_apply,
          ClassFunction.smul_apply, smul_eq_mul, hindOne, hzeta1]
        ring
      unfold invDadeSeqIndCoefficient
      rw [hadjusted, map_add, starCharacterPairing_add_left]
      change starCharacterPairing beta
          (nu (zeta : ClassFunction L ℂ)) +
        invDadeSeqIndCoefficient ddA phi
          (nu (zeta : ClassFunction L ℂ))
          (zeta : ClassFunction L ℂ) = (coeff : ℂ)
      rw [ha, hcZeta]
      simp [coeff]
    let av : ℝ := (coeff : ℝ)
    let h : ℝ := Nat.card H
    let e : ℝ := H.index
    let v : ℝ := h⁻¹
    let u : ℝ := e⁻¹ * (1 - v)
    have hinvNorm :
        classFunctionNormSq
            (invDade ddA (nu (zeta : ClassFunction L ℂ))) =
          u * av ^ 2 - v * (2 * av) + (1 - e / h) := by
      have hzetaNorm :
          starCharacterPairing (zeta : ClassFunction L ℂ)
              (zeta : ClassFunction L ℂ) = 1 := by
        rw [seqInd_starPairing_eq_characterPairing H hzetaT hzetaT,
          IrreducibleCharacter.characterPairing_self]
      have hindZeta :
          starCharacterPairing ind1 (zeta : ClassFunction L ℂ) = 0 :=
        seqIndT_star_orthogonal H hindT hzetaT hzetaNeInd.symm
      have hzetaInd :
          starCharacterPairing (zeta : ClassFunction L ℂ) ind1 = 0 :=
        seqIndT_star_orthogonal H hzetaT hindT hzetaNeInd
      have hindNot :
          ind1 ∉ insert (zeta : ClassFunction L ℂ) S1 := by
        simp [S1, hzetaNeInd.symm]
      have hzetaNot : (zeta : ClassFunction L ℂ) ∉ S1 := by
        simp [S1]
      have hUleft {xi : ClassFunction L ℂ} (hxi : xi ∈ S1)
          (mu : ClassFunction L ℂ) :
          invDadeSeqIndU H ddA phi
              (nu (zeta : ClassFunction L ℂ)) xi mu = 0 := by
        dsimp only [invDadeSeqIndU]
        rw [hcTail hxi]
        simp
      have hUright (xi : ClassFunction L ℂ)
          {mu : ClassFunction L ℂ} (hmu : mu ∈ S1) :
          invDadeSeqIndU H ddA phi
              (nu (zeta : ClassFunction L ℂ)) xi mu = 0 := by
        dsimp only [invDadeSeqIndU]
        rw [hcTail hmu]
        simp
      have htailRight (xi : ClassFunction L ℂ) :
          (∑ mu ∈ S1,
            invDadeSeqIndU H ddA phi
              (nu (zeta : ClassFunction L ℂ)) xi mu) = 0 := by
        apply Finset.sum_eq_zero
        intro mu hmu
        exact hUright xi hmu
      have hinner (xi : ClassFunction L ℂ) :
          (∑ mu ∈ insert ind1
              (insert (zeta : ClassFunction L ℂ) S1),
            invDadeSeqIndU H ddA phi
              (nu (zeta : ClassFunction L ℂ)) xi mu) =
            invDadeSeqIndU H ddA phi
                (nu (zeta : ClassFunction L ℂ)) xi ind1 +
              invDadeSeqIndU H ddA phi
                (nu (zeta : ClassFunction L ℂ)) xi
                  (zeta : ClassFunction L ℂ) := by
        rw [Finset.sum_insert hindNot, Finset.sum_insert hzetaNot,
          htailRight xi, add_zero]
      have htailOuter :
          (∑ xi ∈ S1,
            ∑ mu ∈ insert ind1
                (insert (zeta : ClassFunction L ℂ) S1),
              invDadeSeqIndU H ddA phi
                (nu (zeta : ClassFunction L ℂ)) xi mu) = 0 := by
        apply Finset.sum_eq_zero
        intro xi hxi
        apply Finset.sum_eq_zero
        intro mu _
        exact hUleft hxi mu
      have hsumCore :
          (∑ xi ∈ insert ind1
              (insert (zeta : ClassFunction L ℂ) S1),
            ∑ mu ∈ insert ind1
                (insert (zeta : ClassFunction L ℂ) S1),
              invDadeSeqIndU H ddA phi
                (nu (zeta : ClassFunction L ℂ)) xi mu) =
            invDadeSeqIndU H ddA phi
                (nu (zeta : ClassFunction L ℂ)) ind1 ind1 +
              invDadeSeqIndU H ddA phi
                (nu (zeta : ClassFunction L ℂ)) ind1
                  (zeta : ClassFunction L ℂ) +
              invDadeSeqIndU H ddA phi
                (nu (zeta : ClassFunction L ℂ))
                  (zeta : ClassFunction L ℂ) ind1 +
              invDadeSeqIndU H ddA phi
                (nu (zeta : ClassFunction L ℂ))
                  (zeta : ClassFunction L ℂ)
                  (zeta : ClassFunction L ℂ) := by
        rw [Finset.sum_insert hindNot, Finset.sum_insert hzetaNot,
          hinner ind1, hinner (zeta : ClassFunction L ℂ), htailOuter]
        ring
      have hp := hexp.pairing_norm
      rw [starCharacterPairing_self_eq_classFunctionNormSq] at hp
      rw [hsumCore] at hp
      simp [invDadeSeqIndU, hcInd, hcZeta, hindNorm, hzetaNorm,
        hindZeta, hzetaInd, hindOne, hzeta1] at hp
      simp only [← Nat.card_eq_fintype_card] at hp
      apply Complex.ofReal_injective
      rw [hp]
      push_cast
      dsimp [u, v, av, h, e]
      push_cast
      field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne',
        Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite] <;> ring
    have hbetaNorm : classFunctionNormSq beta = (H.index : ℝ) + 1 := by
      rw [classFunctionNormSq_eq_re_starCharacterPairing]
      rw [show beta = Dade ddA (ind1 - (zeta : ClassFunction L ℂ)) by rfl]
      have hmuOn : ind1 - (zeta : ClassFunction L ℂ) ∈
          ClassFunction.supportedOn
            {a : L |
              (a : Γ) ∈ subgroupNonidentity (H.map L.subtype)} := by
        rw [hsupportEq]
        unfold ind1 dadeInducedTrivial
        exact cfInd1_sub_lin_on H (hcalST hzeta) hzeta1
      rw [Dade_isometry ddA _ _ hmuOn hmuOn]
      have hindZeta :
          starCharacterPairing ind1 (zeta : ClassFunction L ℂ) = 0 :=
        seqIndT_star_orthogonal H hindT (hcalST hzeta) hzetaNeInd.symm
      have hzetaInd :
          starCharacterPairing (zeta : ClassFunction L ℂ) ind1 = 0 :=
        seqIndT_star_orthogonal H (hcalST hzeta) hindT hzetaNeInd
      have hzetaNorm :
          starCharacterPairing (zeta : ClassFunction L ℂ)
              (zeta : ClassFunction L ℂ) = 1 := by
        rw [seqInd_starPairing_eq_characterPairing H
          (hcalST hzeta) (hcalST hzeta),
          IrreducibleCharacter.characterPairing_self]
      rw [starCharacterPairing_sub_left_cover,
        starCharacterPairing_sub_right_cover,
        starCharacterPairing_sub_right_cover,
        hindNorm, hindZeta, hzetaInd, hzetaNorm]
      norm_num
    have hgammaNorm :
        classFunctionNormSq gamma =
          (H.index : ℝ) - 1 -
            (Nat.card H : ℝ) *
              (u * av ^ 2 - v * (2 * av)) := by
      have hdegreeStar {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
          star (xi 1) = xi 1 := by
        obtain ⟨n, hn⟩ := Cnat_seqInd1 H hxi
        rw [hn]
        simp
      have hpairStar {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
          star (characterPairing xi xi) = characterPairing xi xi := by
        rw [← seqInd_starPairing_eq_characterPairing H
          (hcalST hxi) (hcalST hxi),
          starCharacterPairing_self_eq_classFunctionNormSq]
        simp
      have hquotStar {xi : ClassFunction L ℂ} (hxi : xi ∈ calS) :
          star (xi 1 / (H.index : ℂ) / characterPairing xi xi) =
            xi 1 / (H.index : ℂ) / characterPairing xi xi := by
        change (starRingEnd ℂ)
            (xi 1 / (H.index : ℂ) / characterPairing xi xi) = _
        have hdegreeStar' := hdegreeStar hxi
        have hpairStar' := hpairStar hxi
        change (starRingEnd ℂ) (xi 1) = xi 1 at hdegreeStar'
        change (starRingEnd ℂ) (characterPairing xi xi) =
          characterPairing xi xi at hpairStar'
        rw [map_div₀, map_div₀, hdegreeStar', hpairStar']
        simp
      have hsumSelf :
          starCharacterPairing sumSnu sumSnu =
            ((Nat.card H : ℂ) - 1) / (H.index : ℂ) := by
        unfold sumSnu dadeInd1CoherentSum
        rw [starCharacterPairing_finset_sum_left_cover]
        simp only [starCharacterPairing_finset_sum_right_cover,
          starCharacterPairing_smul_left,
          starCharacterPairing_smul_right]
        calc
          _ = ∑ xi ∈ calS,
              (xi 1 / (H.index : ℂ) / characterPairing xi xi) *
                star (xi 1 / (H.index : ℂ) /
                  characterPairing xi xi) *
                characterPairing xi xi := by
            apply Finset.sum_congr rfl
            intro xi hxi
            rw [Finset.sum_eq_single xi]
            · rw [hnuPair hxi hxi]
              ring
            · intro mu hmu hne
              rw [hnuPair hxi hmu,
                hcalSOrth hxi hmu hne.symm]
              simp
            · intro hnot
              exact (hnot hxi).elim
          _ = (H.index : ℂ)⁻¹ ^ 2 *
              (∑ xi ∈ calS,
                xi 1 ^ 2 / characterPairing xi xi) := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro xi hxi
            rw [hquotStar hxi]
            have hpairNe : characterPairing xi xi ≠ 0 :=
              cfnorm_seqInd_neq0 H hxi
            have hindex : (H.index : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
            field_simp [hpairNe, hindex]
          _ = ((Nat.card H : ℂ) - 1) / (H.index : ℂ) := by
            rw [sum_seqIndC1_square (k := ℂ) H]
            have hindex : (H.index : ℂ) ≠ 0 :=
              Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
            field_simp [hindex]
      have hzetaSum :
          starCharacterPairing
              (nu (zeta : ClassFunction L ℂ)) sumSnu = 1 := by
        unfold sumSnu dadeInd1CoherentSum
        rw [starCharacterPairing_finset_sum_right_cover]
        rw [Finset.sum_eq_single (zeta : ClassFunction L ℂ)]
        · rw [starCharacterPairing_smul_right,
            hnuPair hzeta hzeta,
            IrreducibleCharacter.characterPairing_self, hzeta1]
          have hindex : (H.index : ℂ) ≠ 0 :=
            Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
          simp [hindex]
        · intro xi hxi hne
          rw [starCharacterPairing_smul_right,
            hnuPair hzeta hxi,
            hcalSOrth hzeta hxi hne.symm]
          simp
        · intro hnot
          exact (hnot hzeta).elim
      have hsumZeta :
          starCharacterPairing sumSnu
              (nu (zeta : ClassFunction L ℂ)) = 1 := by
        calc
          starCharacterPairing sumSnu
              (nu (zeta : ClassFunction L ℂ)) =
              star (starCharacterPairing
                (nu (zeta : ClassFunction L ℂ)) sumSnu) :=
            starCharacterPairing_conj_symm _ _
          _ = 1 := by rw [hzetaSum]; simp
      have hzetaSelf :
          starCharacterPairing
              (nu (zeta : ClassFunction L ℂ))
              (nu (zeta : ClassFunction L ℂ)) = 1 := by
        rw [hnuPair hzeta hzeta,
          IrreducibleCharacter.characterPairing_self]
      have hcoeffStar : star ((coeff : ℂ)) = (coeff : ℂ) := by
        simp
      have hXSelf :
          starCharacterPairing X X =
            1 + (((Nat.card H : ℂ) - 1) / (H.index : ℂ)) *
                (coeff : ℂ) ^ 2 - 2 * (coeff : ℂ) := by
        have hX' : X = (coeff : ℂ) • sumSnu -
            nu (zeta : ClassFunction L ℂ) := by
          rw [hX]
          abel
        rw [hX', starCharacterPairing_sub_left_cover,
          starCharacterPairing_sub_right_cover,
          starCharacterPairing_sub_right_cover]
        simp only [starCharacterPairing_smul_left,
          starCharacterPairing_smul_right]
        rw [hsumSelf, hsumZeta, hzetaSum, hzetaSelf, hcoeffStar]
        ring
      have hXNormReal :
          classFunctionNormSq X =
            1 + (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) *
                av ^ 2 - 2 * av := by
        apply Complex.ofReal_injective
        change (classFunctionNormSq X : ℂ) =
          ((1 + (((Nat.card H : ℝ) - 1) / (H.index : ℝ)) *
              av ^ 2 - 2 * av : ℝ) : ℂ)
        rw [← starCharacterPairing_self_eq_classFunctionNormSq, hXSelf]
        simp only [av]
        push_cast
        rfl
      have hXNorm :
          classFunctionNormSq X =
            1 + (Nat.card H : ℝ) *
              (u * av ^ 2 - v * (2 * av)) := by
        rw [hXNormReal]
        dsimp [u, v, h, e]
        have hcard : (Nat.card H : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr Nat.card_pos.ne'
        have hindex : (H.index : ℝ) ≠ 0 :=
          Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
        field_simp [hcard, hindex] <;> ring
      have honePair : starCharacterPairing oneG oneG = 1 := by
        unfold oneG starCharacterPairing twistedCharacterPairing
        simp [IrreducibleCharacter.trivial_apply,
          Nat.cast_ne_zero.mpr Nat.card_pos.ne']
      have honeBeta : starCharacterPairing oneG beta = 1 := by
        calc
          starCharacterPairing oneG beta =
              star (starCharacterPairing beta oneG) :=
            starCharacterPairing_conj_symm _ _
          _ = 1 := by rw [hbetaOne]; simp
      have hbetaSelfRe :
          (starCharacterPairing beta beta).re =
            (H.index : ℝ) + 1 := by
        rw [← classFunctionNormSq_eq_re_starCharacterPairing]
        exact hbetaNorm
      have hbetaMinusOneNorm :
          classFunctionNormSq (beta - oneG) = (H.index : ℝ) := by
        rw [classFunctionNormSq_eq_re_starCharacterPairing,
          starCharacterPairing_sub_left_cover,
          starCharacterPairing_sub_right_cover,
          starCharacterPairing_sub_right_cover,
          hbetaOne, honeBeta, honePair]
        simp only [Complex.sub_re, Complex.one_re, sub_self, sub_zero]
        rw [hbetaSelfRe]
        ring
      have horthGX : starCharacterPairing gamma X = 0 := by
        unfold X
        rw [starCharacterPairing_finset_sum_right_cover]
        apply Finset.sum_eq_zero
        intro xi hxi
        have hgammaNu :
            starCharacterPairing gamma (nu xi) = 0 := by
          calc
            starCharacterPairing gamma (nu xi) =
                star (starCharacterPairing (nu xi) gamma) :=
              starCharacterPairing_conj_symm _ _
            _ = 0 := by rw [hgammaImage xi hxi]; simp
        rw [starCharacterPairing_smul_right, hgammaNu]
        simp
      have hnormDecomp := classFunctionNormSq_add_of_orthogonal_cover
        gamma X horthGX
      have hsum : gamma + X = beta - oneG := by
        unfold gamma
        abel
      rw [hsum, hbetaMinusOneNorm, hXNorm] at hnormDecomp
      linarith
    have hh : 0 < h := by
      dsimp [h]
      exact Nat.cast_pos.mpr Nat.card_pos
    have he0 : 0 < e := by
      dsimp [e]
      exact Nat.cast_pos.mpr
        (Nat.pos_of_ne_zero H.index_ne_zero_of_finite)
    have he' : e ≤ (h - 1) / 2 := by
      simpa [e, h] using he
    have hvForm : v = 1 / h := by
      simp [v]
    have huForm : u = (h - 1) / (e * h) := by
      dsimp [u, v]
      field_simp [hh.ne', he0.ne']
    have heTwo : 2 * e ≤ h - 1 := by
      nlinarith
    have huv : 2 * v ≤ u := by
      rw [hvForm, huForm]
      rw [show 2 * (1 / h) = 2 / h by ring]
      apply (div_le_div_iff₀ hh (mul_pos he0 hh)).2
      have hmul := mul_le_mul_of_nonneg_right heTwo hh.le
      nlinarith
    have hv0 : 0 ≤ v := by
      rw [hvForm]
      positivity
    have hu0 : 0 ≤ u := by
      nlinarith
    have hquadratic : 0 ≤ u * av ^ 2 - v * (2 * av) := by
      by_cases hc : coeff = 0
      · have hav0 : av = 0 := by simp [av, hc]
        rw [hav0]
        norm_num
      · rcases Int.cast_le_neg_one_or_one_le_cast_of_ne_zero ℝ hc with
          hneg | hpos
        · have hneg' : av ≤ -1 := by simpa [av] using hneg
          have hnegav : 0 ≤ -av := by linarith
          have hterm1 : 0 ≤ u * av ^ 2 :=
            mul_nonneg hu0 (sq_nonneg av)
          have hterm2 : 0 ≤ (2 * v) * (-av) :=
            mul_nonneg (by nlinarith) hnegav
          nlinarith
        · have hpos' : 1 ≤ av := by simpa [av] using hpos
          have hua : 2 * v ≤ u * av := by
            calc
              2 * v ≤ u := huv
              _ ≤ u * av := by
                have hm := mul_le_mul_of_nonneg_left hpos' hu0
                simpa using hm
          have hprod : 0 ≤ av * (u * av - 2 * v) :=
            mul_nonneg (by linarith) (sub_nonneg.mpr hua)
          nlinarith
    constructor
    · change 1 - e / h ≤
        classFunctionNormSq
          (invDade ddA (nu (zeta : ClassFunction L ℂ)))
      calc
        1 - e / h ≤
            u * av ^ 2 - v * (2 * av) + (1 - e / h) := by
          nlinarith
        _ = classFunctionNormSq
            (invDade ddA (nu (zeta : ClassFunction L ℂ))) :=
          hinvNorm.symm
    · change classFunctionNormSq gamma ≤ e - 1
      calc
        classFunctionNormSq gamma =
            e - 1 - h * (u * av ^ 2 - v * (2 * av)) := by
          simpa [e, h] using hgammaNorm
        _ ≤ e - 1 := by
          nlinarith [mul_nonneg hh.le hquadratic]
  have hirr :
      ∀ chi : IrreducibleCharacter G ℂ,
        OrthogonalToSeqIndImage H nu (chi : ClassFunction G ℂ) →
        (∀ a : L,
            (a : Γ) ∈ subgroupNonidentity (H.map L.subtype) →
            invDade ddA (chi : ClassFunction G ℂ) a =
              starCharacterPairing beta chi) ∧
          classFunctionNormSq (invDade ddA (chi : ClassFunction G ℂ)) =
            ((subgroupNonidentity (H.map L.subtype)).ncard : ℝ) /
                (Nat.card L : ℝ) *
              Complex.normSq (starCharacterPairing beta chi) := by
    intro chi hchiOrth
    let S1 := calT.erase ind1 |>.erase (zeta : ClassFunction L ℂ)
    have hzetaNeInd : (zeta : ClassFunction L ℂ) ≠ ind1 := by
      have hzetaFilter := hzeta
      rw [seqIndC1_rem] at hzetaFilter
      simpa [ind1, dadeInducedTrivial] using
        (Finset.mem_erase.mp hzetaFilter).1
    have hsplit : calT = insert (zeta : ClassFunction L ℂ) (insert ind1 S1) := by
      ext xi
      simp only [Finset.mem_insert]
      constructor
      · intro hxi
        by_cases hxzeta : xi = (zeta : ClassFunction L ℂ)
        · exact Or.inl hxzeta
        by_cases hxind : xi = ind1
        · exact Or.inr (Or.inl hxind)
        · exact Or.inr (Or.inr (by
            apply Finset.mem_erase.mpr
            refine ⟨hxzeta, ?_⟩
            exact Finset.mem_erase.mpr ⟨hxind, hxi⟩))
      · rintro (rfl | rfl | hxi)
        · exact hcalST hzeta
        · exact hindT
        · exact (Finset.mem_erase.mp
            (Finset.mem_erase.mp hxi).2).2
    have hzetaTail : (zeta : ClassFunction L ℂ) ∉ insert ind1 S1 := by
      simp [S1, hzetaNeInd]
    have hexp := invDade_seqInd_sum H ddA
      (zeta : ClassFunction L ℂ) (insert ind1 S1)
      (chi : ClassFunction G ℂ) hsplit hzetaTail
    have hcTail {xi : ClassFunction L ℂ}
        (hxi : xi ∈ S1) :
        invDadeSeqIndCoefficient ddA (zeta : ClassFunction L ℂ)
          (chi : ClassFunction G ℂ) xi = 0 := by
      have hxiS : xi ∈ calS := by
        have hxiEraseZeta := Finset.mem_erase.mp hxi
        have hxiEraseInd := Finset.mem_erase.mp hxiEraseZeta.2
        unfold calS
        rw [seqIndC1_filter]
        refine Finset.mem_filter.mpr ⟨hxiEraseInd.2, ?_⟩
        simpa [ind1, dadeInducedTrivial] using hxiEraseInd.1
      have hadjustedClosure :
          invDadeSeqIndAdjusted (zeta : ClassFunction L ℂ) xi ∈
            AddSubgroup.closure
              (↑calS : Set (ClassFunction L ℂ)) := by
        obtain ⟨n, hn⟩ := dvd_index_seqInd1 H hxiS
        unfold invDadeSeqIndAdjusted
        rw [hzeta1, hn]
        exact (AddSubgroup.closure
          (↑calS : Set (ClassFunction L ℂ))).sub_mem
            (hmemClosure hxiS) (by
              have hm := (AddSubgroup.closure
                (↑calS : Set (ClassFunction L ℂ))).nsmul_mem
                  (hmemClosure hzeta) n
              rw [← Nat.cast_smul_eq_nsmul (R := ℂ) n
                (zeta : ClassFunction L ℂ)] at hm
              exact hm)
      have hadjustedOn :
          invDadeSeqIndAdjusted (zeta : ClassFunction L ℂ) xi ∈
            ClassFunction.supportedOn (nonidentitySet L) := by
        unfold invDadeSeqIndAdjusted
        rw [ClassFunction.mem_supportedOn_iff]
        intro x hx
        have hx1 : x = 1 := by
          simpa [nonidentitySet] using not_not.mp hx
        subst x
        simp [hzeta1, Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite]
      have hagree := hcoh.agrees _ hadjustedClosure hadjustedOn
      unfold invDadeSeqIndCoefficient
      rw [← hagree]
      unfold invDadeSeqIndAdjusted
      rw [map_sub, map_smul, starCharacterPairing_sub_left_cover,
        starCharacterPairing_smul_left]
      rw [hchiOrth xi hxiS,
        hchiOrth (zeta : ClassFunction L ℂ) hzeta]
      simp
    have hcInd :
        invDadeSeqIndCoefficient ddA (zeta : ClassFunction L ℂ)
          (chi : ClassFunction G ℂ) ind1 =
        starCharacterPairing beta chi := by
      have hindex : (H.index : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
      unfold invDadeSeqIndCoefficient invDadeSeqIndAdjusted
      change starCharacterPairing
        (Dade ddA
          (ind1 - (ind1 1 / (zeta : ClassFunction L ℂ) 1) •
            (zeta : ClassFunction L ℂ))) chi =
        starCharacterPairing
          (Dade ddA (ind1 - (zeta : ClassFunction L ℂ))) chi
      rw [hindOne, hzeta1, div_self hindex, one_smul]
    have hchiVirtual :
        ClassFunction.IsVirtual (chi : ClassFunction G ℂ) := by
      refine ⟨Finsupp.single chi 1, ?_⟩
      simp
    have hcStar :
        star (starCharacterPairing beta chi) =
          starCharacterPairing beta chi := by
      obtain ⟨m, hm⟩ :=
        virtual_pairing_isInt_cover hbetaVirtual hchiVirtual
      rw [hm]
      simp
    have hvalueConst :
        ∀ x : L,
          (x : Γ) ∈ subgroupNonidentity (H.map L.subtype) →
          invDade ddA (chi : ClassFunction G ℂ) x =
            starCharacterPairing beta chi := by
      intro x hx
      have hxHsharp : x ∈ subgroupNonidentity H := by
        rw [← hsupportEq]
        exact hx
      have hv := hexp.value_on_support x hx
      have hindNot : ind1 ∉ S1 := by simp [S1]
      rw [Finset.sum_insert hindNot] at hv
      have htailZero :
          (∑ xi ∈ S1,
            (star (invDadeSeqIndCoefficient ddA
                (zeta : ClassFunction L ℂ) (chi : ClassFunction G ℂ) xi) /
              starCharacterPairing xi xi) * xi x) = 0 := by
        apply Finset.sum_eq_zero
        intro xi hxi
        rw [hcTail hxi]
        simp
      rw [htailZero, add_zero, hcInd, hcStar, hindNorm,
        hindValue hxHsharp.1] at hv
      have hindex : (H.index : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.mpr H.index_ne_zero_of_finite
      simpa [hindex] using hv
    constructor
    · exact hvalueConst
    · rw [cfnormE_invDade]
      have hcard :
          (Finset.univ.filter
            (fun a : L ↦
              (a : Γ) ∈ subgroupNonidentity (H.map L.subtype))).card =
            (subgroupNonidentity (H.map L.subtype)).ncard := by
        calc
          _ = ((↑(Finset.univ.filter
                (fun a : L ↦
                  (a : Γ) ∈ subgroupNonidentity (H.map L.subtype))) :
                Set L)).ncard := (Set.ncard_coe_finset _).symm
          _ = ({a : L |
              (a : Γ) ∈ subgroupNonidentity (H.map L.subtype)} :
                Set L).ncard := by
            congr 1
            ext a
            simp
          _ = (subgroupNonidentity (H.map L.subtype) ∩
                (L : Set Γ)).ncard :=
            Set.ncard_subtype _ _
          _ = (subgroupNonidentity (H.map L.subtype)).ncard := by
            apply congrArg Set.ncard
            exact Set.inter_eq_left.mpr (fun x hx ↦ ddA.1.1 hx)
      have hsum :
          (∑ x ∈ Finset.univ.filter
              (fun x : L ↦
                (x : Γ) ∈ subgroupNonidentity (H.map L.subtype)),
              Complex.normSq (invDade ddA (chi : ClassFunction G ℂ) x)) =
            ((Finset.univ.filter
              (fun x : L ↦
                (x : Γ) ∈ subgroupNonidentity
                  (H.map L.subtype))).card : ℝ) *
              Complex.normSq (starCharacterPairing beta chi) := by
        calc
          _ = ∑ _x ∈ Finset.univ.filter
                (fun x : L ↦
                  (x : Γ) ∈ subgroupNonidentity (H.map L.subtype)),
                Complex.normSq (starCharacterPairing beta chi) := by
              apply Finset.sum_congr rfl
              intro x hx
              rw [hvalueConst x (Finset.mem_filter.mp hx).2]
          _ = _ := by simp
      rw [hsum, hcard]
      ring
  refine
    { image_orthogonal_one := himageOne
      beta_pairing_one := hbetaOne
      beta_virtual := hbetaVirtual
      gamma := gamma
      image_orthogonal_gamma := hgammaImage
      gamma_pairing_one := hgammaOne
      coefficient := coeff
      decomposition := hdecomp
      norm_bounds := hbounds
      orthogonal_irreducible := hirr }

end

end Submission.OddOrder.PF
