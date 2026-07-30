import Submission.OddOrder.PF.Section01.InductionTransitivity

/-!
# Induced-character compatibility for arbitrary subgroups

The initial character-compatibility theorem was specialized to normal
subgroups, which suffices through Peterfalvi 1.6.  In Section 1.7 the
inducing subgroup is an inertia subgroup and need not be normal.  This file
proves the general coinduced trace formula, regroups the explicit induction
sum by right cosets, and identifies the two characters without a normality
hypothesis.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v w

namespace InducedCharacterCompatibility

variable {k : Type u} [Field k] {G : Type v} [Group G]
  (H : Subgroup G) {V : Type w} [AddCommGroup V] [Module k V]
  (rho : Representation k H V)

/-- A right coset is fixed by right multiplication by `g` exactly when the
corresponding conjugate of `g` lies in the subgroup. -/
theorem cosetMk_mul_eq_iff (q : Cosets H) (g : G) :
    cosetMk H (q.out * g) = q ↔ q.out * g * q.out⁻¹ ∈ H := by
  have hq : cosetMk H q.out = q := Quotient.out_eq q
  constructor
  · intro hfix
    have hrel := Quotient.exact (hfix.trans hq.symm)
    have hinv : (q.out * g * q.out⁻¹)⁻¹ ∈ H := by
      simpa [mul_inv_rev, mul_assoc] using
        (QuotientGroup.rightRel_apply.mp hrel)
    exact H.inv_mem_iff.mp hinv
  · intro hmem
    calc
      cosetMk H (q.out * g) = cosetMk H q.out := by
        apply Quotient.sound
        change (QuotientGroup.rightRel H) (q.out * g) q.out
        apply QuotientGroup.rightRel_apply.mpr
        simpa [mul_inv_rev, mul_assoc] using H.inv_mem hmem
      _ = q := hq

/-- Character formula for coinduction from an arbitrary subgroup. -/
theorem coind_character_formula [Fintype G] [Fintype (Cosets H)]
    [FiniteDimensional k V] (g : G) :
    Representation.character (Representation.coind H.subtype rho) g =
      ∑ q : Cosets H,
        if hq : q.out * g * q.out⁻¹ ∈ H then
          Representation.character rho ⟨q.out * g * q.out⁻¹, hq⟩
        else 0 := by
  classical
  have htrace := LinearMap.trace_conj'
    (Representation.coind H.subtype rho g) (coindVEquivPi H rho)
  rw [coindVEquivPi_conj, trace_weightedReindexEnd] at htrace
  change (LinearMap.trace k (Representation.coindV H.subtype rho)
      (Representation.coind H.subtype rho g)) = _
  rw [← htrace]
  apply Fintype.sum_congr
  intro q
  by_cases hmem : q.out * g * q.out⁻¹ ∈ H
  · have hfix : cosetMk H (q.out * g) = q :=
      (cosetMk_mul_eq_iff H q g).2 hmem
    rw [if_pos hfix, dif_pos hmem]
    apply congrArg (Representation.character rho)
    apply Subtype.ext
    have hout := congrArg Quotient.out hfix
    simp [cosetFactor, hout]
  · have hfix : cosetMk H (q.out * g) ≠ q :=
      (cosetMk_mul_eq_iff H q g).not.mpr hmem
    rw [if_neg hfix, dif_neg hmem]

/-- On each right-coset fiber, an induction summand is the corresponding
fixed-coset character term. -/
theorem inductionKernel_eq_cosetTerm [Fintype G]
    (f : ClassFunction H k) (g : G) (q : Cosets H)
    (x : {x : G // inverseCosetMap H x = q}) :
    ClassFunction.inductionKernel H f x g =
      if hq : q.out * g * q.out⁻¹ ∈ H then
        f ⟨q.out * g * q.out⁻¹, hq⟩
      else 0 := by
  let h : H := (subgroupEquivInverseCosetFiber H q).symm x
  have hh : (h : G) = q.out * (x : G) := rfl
  have hmem : (x : G)⁻¹ * g * x ∈ H ↔
      q.out * g * q.out⁻¹ ∈ H := by
    constructor
    · intro hx
      have hm := H.mul_mem (H.mul_mem h.property hx) (H.inv_mem h.property)
      convert hm using 1
      simp only [hh]
      group
    · intro hq
      have hm := H.mul_mem (H.mul_mem (H.inv_mem h.property) hq) h.property
      convert hm using 1
      simp only [hh]
      group
  by_cases hq : q.out * g * q.out⁻¹ ∈ H
  · have hx := hmem.2 hq
    rw [ClassFunction.inductionKernel_of_mem _ _ _ _ hx, dif_pos hq]
    let t : H := ⟨q.out * g * q.out⁻¹, hq⟩
    have harg :
        (⟨(x : G)⁻¹ * g * x, hx⟩ : H) = h⁻¹ * t * (h⁻¹)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, t, hh]
      group
    rw [harg]
    exact ClassFunction.conj_apply f h⁻¹ t
  · have hx := hmem.not.mpr hq
    rw [ClassFunction.inductionKernel_of_notMem _ _ _ _ hx, dif_neg hq]

/-- Regroup the explicit induction sum over right-coset fibers. -/
theorem sum_inductionKernel_eq_card_smul_sum_cosets
    [Fintype G] [Fintype H] [Fintype (Cosets H)]
    (f : ClassFunction H k) (g : G) :
    (∑ x : G, ClassFunction.inductionKernel H f x g) =
      Nat.card H •
        ∑ q : Cosets H,
          if hq : q.out * g * q.out⁻¹ ∈ H then
            f ⟨q.out * g * q.out⁻¹, hq⟩
          else 0 := by
  classical
  rw [← Fintype.sum_fiberwise (inverseCosetMap H)
    (fun x : G ↦ ClassFunction.inductionKernel H f x g)]
  rw [Finset.smul_sum]
  apply Fintype.sum_congr
  intro q
  let C : k := if hq : q.out * g * q.out⁻¹ ∈ H then
    f ⟨q.out * g * q.out⁻¹, hq⟩ else 0
  calc
    (∑ x : {x : G // inverseCosetMap H x = q},
        ClassFunction.inductionKernel H f x g) =
        ∑ _x : {x : G // inverseCosetMap H x = q}, C := by
      apply Fintype.sum_congr
      intro x
      exact inductionKernel_eq_cosetTerm H f g q x
    _ = Fintype.card {x : G // inverseCosetMap H x = q} • C := by simp
    _ = Nat.card H • C := by
      have hcard : Fintype.card {x : G // inverseCosetMap H x = q} =
          Nat.card H := by
        rw [Nat.card_eq_fintype_card]
        exact Fintype.card_congr (subgroupEquivInverseCosetFiber H q).symm
      rw [hcard]

/-- The explicit class-function induction formula is the character of the
coinduced representation for every subgroup. -/
theorem classFunction_induce_eq_coind_character_general
    [Fintype G] [Fintype H] [Fintype (Cosets H)]
    [FiniteDimensional k V] [CharZero k] (g : G) :
    ClassFunction.induce H (ClassFunction.ofRepresentation rho) g =
      Representation.character (Representation.coind H.subtype rho) g := by
  rw [ClassFunction.induce_apply_formula, coind_character_formula H rho]
  change (Nat.card H : k)⁻¹ *
      (∑ x : G, ClassFunction.inductionKernel H
        (ClassFunction.ofRepresentation rho) x g) = _
  rw [sum_inductionKernel_eq_card_smul_sum_cosets H
    (ClassFunction.ofRepresentation rho) g]
  rw [← Nat.cast_smul_eq_nsmul k, smul_eq_mul]
  field_simp [Nat.cast_ne_zero.mpr Nat.card_pos.ne']
  rfl

end InducedCharacterCompatibility

namespace ClassFunction

variable {K Γ : Type u} [Field K] [Group Γ] [Fintype Γ]

/-- Character compatibility for induction from an arbitrary subgroup. -/
theorem ofRepresentation_induceFromSubgroup_general [CharZero K]
    (S : Subgroup Γ) (V₀ : FDRep K S) :
    ofRepresentation (FDRep.induceFromSubgroup S V₀).ρ =
      induce S (ofRepresentation V₀.ρ) := by
  classical
  letI : Fintype (InducedCharacterCompatibility.Cosets S) := Fintype.ofFinite _
  letI : DecidableRel (QuotientGroup.rightRel S) := Classical.decRel _
  ext g
  have hcoind :=
    InducedCharacterCompatibility.classFunction_induce_eq_coind_character_general
      S V₀.ρ g
  let A : Rep K S := Rep.of V₀.ρ
  have hchar := congrFun
    (Representation.char_iso
      (Representation.equivOfIso (Rep.indCoindIso A))) g
  change Representation.character (FDRep.induceFromSubgroup S V₀).ρ g =
    induce S (ofRepresentation V₀.ρ) g
  rw [FDRep.induceFromSubgroup_ρ]
  exact hchar.trans hcoind.symm

/-- Induction of a realized character is realized for every subgroup. -/
theorem induce_ofRepresentation_general [CharZero K]
    (S : Subgroup Γ) (V₀ : FDRep K S) :
    induce S (ofRepresentation V₀.ρ) =
      ofRepresentation (FDRep.induceFromSubgroup S V₀).ρ :=
  (ofRepresentation_induceFromSubgroup_general S V₀).symm

end ClassFunction

end

end Submission.OddOrder.PF
