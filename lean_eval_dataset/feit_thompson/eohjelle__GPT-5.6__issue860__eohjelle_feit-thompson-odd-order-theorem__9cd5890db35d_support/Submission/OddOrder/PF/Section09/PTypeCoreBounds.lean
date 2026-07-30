import Submission.OddOrder.PF.Section09.PTypeCoreContext
import Submission.OddOrder.PF.Section09.PTypeNonGaloisConclusion

/-!
# Peterfalvi Section 9: finite families and numerical weights for the core bound

This module introduces the finite slices and real-valued degree sums used in
Peterfalvi (9.11.1).  The definitions are kept independent of the subsequent
rigidity argument so that every later phase uses one canonical formulation of
the source families and their numerical weights.
-/

namespace Submission.OddOrder.PF

noncomputable section

open PTypeCoreContextInternal
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open scoped BigOperators Classical

universe u

local instance (priority := 10) pTypeCoreBoundsFintypeOfFinite
    (X : Type u) [Finite X] : Fintype X :=
  Fintype.ofFinite X

/-! ## Finite character families -/

/-- The members of `S` whose value at the identity is the natural degree
`d`.  This is the source family `S1`. -/
def pTypeCoreDegreeSlice
    {M : Type u} [Group M] [Fintype M]
    (S : Finset (ClassFunction M ℂ)) (d : ℕ) :
    Finset (ClassFunction M ℂ) :=
  S.filter fun chi ↦ chi 1 = (d : ℂ)

/-- The complement of the current subfamily `S₂` inside the ambient core
family `S₀`; this is source `S3`. -/
def pTypeCoreRemainder
    {M : Type u} [Group M] [Fintype M]
    (S₀ S₂ : Finset (ClassFunction M ℂ)) :
    Finset (ClassFunction M ℂ) :=
  S₀.filter fun chi ↦ chi ∉ S₂

/-- The irreducible members of `S₃` which also belong to the smaller core
layer `S_(H₀C)`; this is source `S4`. -/
def pTypeCoreIrreducibleRemainder
    {M : Type u} [Group M] [Fintype M]
    (HU : Subgroup M) (H H₀C : Subgroup HU)
    (S₃ : Finset (ClassFunction M ℂ)) :
    Finset (ClassFunction M ℂ) :=
  S₃.filter fun chi ↦
    chi ∈ pTypeCoreFamily HU H H₀C ∧
      IsIrreducibleCharacter M ℂ chi

/-- Conjugation of an ambient subgroup, used for the TI intersection in
Peterfalvi (9.11.2). -/
def pTypeConjugateSubgroup
    {M : Type u} [Group M]
    (U₁ : Subgroup M) (w : M) : Subgroup M :=
  U₁.map (MulAut.conj w).toMonoidHom

/-! ## Real degree sums -/

/-- The real part of a class function's value at the identity. -/
def pTypeCoreDegreeReal
    {M : Type u} [Group M] [Fintype M]
    (chi : ClassFunction M ℂ) : ℝ :=
  (chi 1).re

/-- The real part of the self-pairing of a class function. -/
def pTypeCoreNormReal
    {M : Type u} [Group M] [Fintype M]
    (chi : ClassFunction M ℂ) : ℝ :=
  (characterPairing chi chi).re

/-- Source `Snorm chi = chi(1)^2 / [chi]`. -/
def pTypeCoreDegreeWeight
    {M : Type u} [Group M] [Fintype M]
    (chi : ClassFunction M ℂ) : ℝ :=
  pTypeCoreDegreeReal chi ^ 2 / pTypeCoreNormReal chi

/-- The finite degree-weight sum `sumnS S`. -/
def pTypeCoreDegreeSum
    {M : Type u} [Group M] [Fintype M]
    (S : Finset (ClassFunction M ℂ)) : ℝ :=
  ∑ chi ∈ S, pTypeCoreDegreeWeight chi

/-- The norm value of the virtual character `alpha` computed in
Peterfalvi (9.11.4). -/
def pTypeCoreAlphaNorm (q u a : ℕ) : ℝ :=
  (a : ℝ) + 1 + (((q - 1) * a ^ 2 : ℕ) : ℝ) / (u : ℝ)

/-!
The rest of this module is a narrow cross-phase interface.  It records the
rigid equality case of (9.11.1), together with the lower-slice estimates from
which that case is obtained.  These declarations are implementation support,
not additional source-facing hypotheses.
-/

namespace PTypeCoreBoundsInternal

/-! ## The lower degree slice -/

/-- The irreducible degree-`q * a` part of the larger `H₀U'` layer.  Its
cardinality is the count appearing in clause (9.8d). -/
def pTypeCoreLowerSlice
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    Finset (ClassFunction M ℂ) :=
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀UPrime := pTypeH0DerivedComplementInDerived M
    (derivedWithin M) (Ptype_Fcore_kernel ctx) U
  (seqIndD (k := ℂ) HU H H₀UPrime).filter
    (pTypeIsIrreducibleOfDegree
      (D.q * pTypeNonGaloisIndex hD not_Galois))

/-- The cardinality of the lower slice is definitionally the non-Galois
degree count. -/
@[simp] theorem pTypeCoreLowerSlice_card
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    (pTypeCoreLowerSlice ctx facts not_Galois).card =
      pTypeNonGaloisDegreeCount
        (pTypeCoreDerived M) (pTypeCoreFitting M)
        (pTypeH0DerivedComplementInDerived M (derivedWithin M)
          (Ptype_Fcore_kernel ctx) U)
        (Ptype_factor_action ctx facts).q
        (pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois) := by
  rfl

set_option maxHeartbeats 800000 in
/-- The lower slice is contained in the corresponding slice of the canonical
core family. -/
theorem pTypeCoreLowerSlice_subset_degreeSlice
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeCoreLowerSlice ctx facts not_Galois ⊆
      pTypeCoreDegreeSlice (pTypeCoreFamilyOfContext ctx)
        ((Ptype_factor_action ctx facts).q *
          pTypeNonGaloisIndex
            (Ptype_factor_action_hypotheses ctx facts) not_Galois) := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  let H₀UPrime := pTypeH0DerivedComplementInDerived M
    (derivedWithin M) (Ptype_Fcore_kernel ctx) U
  intro chi hchi
  rcases Finset.mem_filter.mp hchi with ⟨hchiU, hirrDegree⟩
  have hCU : H₀CPrime ≤ H₀UPrime :=
    pTypeCoreKernelDerivedComplement_le_H0UPrime ctx facts
  have hchiCoreRaw : chi ∈ seqIndD (k := ℂ) HU H H₀CPrime :=
    seqIndS HU
      (Iirr_kerDS (k := ℂ)
        (A₁ := H₀UPrime) (A₂ := H₀CPrime)
        (B₁ := H) (B₂ := H) hCU le_rfl) hchiU
  have hchiCore : chi ∈ pTypeCoreFamilyOfContext ctx := by
    convert hchiCoreRaw using 1
    unfold pTypeCoreFamilyOfContext
    congr 1 <;> apply Subsingleton.elim
  obtain ⟨zeta, hzeta, hdegree⟩ := hirrDegree
  apply Finset.mem_filter.mpr
  refine ⟨hchiCore, ?_⟩
  rw [← hzeta, IrreducibleCharacter.apply_one_eq_finrank,
    show Module.finrank ℂ zeta.representation =
      D.q * pTypeNonGaloisIndex hD not_Galois from hdegree]

/-- Every member of the lower slice is irreducible. -/
theorem pTypeCoreLowerSlice_irreducible
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {chi : ClassFunction M ℂ}
    (hchi : chi ∈ pTypeCoreLowerSlice ctx facts not_Galois) :
    IsIrreducibleCharacter M ℂ chi := by
  obtain ⟨zeta, hzeta, _⟩ := (Finset.mem_filter.mp hchi).2
  rw [← hzeta]
  exact zeta.property

/-! ## Clause (9.8d) in core notation -/

/-- Normalize the quotient in clause (9.8d) to
`(p - 1) * [U : U'] / a²`. -/
theorem pTypeCore_lowerQuotient_eq
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let hUM : U ≤ M :=
      ctx.typeP.2.1.2.2.2.2.1.trans
        (Subgroup.map_subtype_le (_root_.commutator M))
    pTypeNonGaloisLowerNumerator D.p (U.subgroupOf M) /
        pTypeNonGaloisLowerDenominator
          (pTypeNonGaloisIndex hD not_Galois)
          (pTypeDerivedComplementInMaximal (Subgroup.inclusion hUM)) =
      ((D.p - 1) * (_root_.commutator U).index) /
        pTypeNonGaloisIndex hD not_Galois ^ 2 := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let hUM : U ≤ M :=
    ctx.typeP.2.1.2.2.2.2.1.trans
      (Subgroup.map_subtype_le (_root_.commutator M))
  let UPrime := _root_.commutator U
  unfold pTypeNonGaloisLowerNumerator
    pTypeNonGaloisLowerDenominator
    pTypeDerivedComplementInMaximal
  rw [Subgroup.card_map_of_injective
      (Subgroup.inclusion_injective hUM),
    natCard_subgroupOf_eq hUM]
  change ((D.p - 1) * Nat.card U) /
      (pTypeNonGaloisIndex hD not_Galois ^ 2 * Nat.card UPrime) = _
  rw [← UPrime.index_mul_card]
  calc
    ((D.p - 1) * (UPrime.index * Nat.card UPrime)) /
        (pTypeNonGaloisIndex hD not_Galois ^ 2 * Nat.card UPrime) =
      (Nat.card UPrime * ((D.p - 1) * UPrime.index)) /
        (Nat.card UPrime *
          pTypeNonGaloisIndex hD not_Galois ^ 2) := by
            congr 1 <;> ring
    _ = ((D.p - 1) * UPrime.index) /
        pTypeNonGaloisIndex hD not_Galois ^ 2 :=
      Nat.mul_div_mul_left _ _ Nat.card_pos

/-- Clause (9.8d), expressed as a lower bound on the lower slice. -/
theorem pTypeCoreLowerSlice_card_lower_bound
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    (((Ptype_factor_action ctx facts).p - 1) *
        (_root_.commutator U).index) /
      pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois ^ 2 ≤
        (pTypeCoreLowerSlice ctx facts not_Galois).card := by
  have hchars := typeP_nonGalois_characters ctx not_Galois
  have hlower := hchars.lower_count_bound
  rw [pTypeCore_lowerQuotient_eq ctx facts not_Galois,
    ← pTypeCoreLowerSlice_card ctx facts not_Galois] at hlower
  exact hlower

/-- The square of the selected index divides the numerator of the normalized
lower bound. -/
theorem pTypeCore_indexSquare_dvd_primePred_mul_derivedIndex
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeNonGaloisIndex
        (Ptype_factor_action_hypotheses ctx facts) not_Galois ^ 2 ∣
      ((Ptype_factor_action ctx facts).p - 1) *
        (_root_.commutator U).index := by
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let UPrime := _root_.commutator U
  have hden := pTypeNonGaloisLowerDenominator_dvd_internal hD not_Galois
  have hden' : a ^ 2 * Nat.card UPrime ∣
      ((D.p - 1) * UPrime.index) * Nat.card UPrime := by
    change a ^ 2 * Nat.card UPrime ∣
      (D.p - 1) * Nat.card U at hden
    rw [← UPrime.index_mul_card] at hden
    simpa only [mul_assoc] using hden
  exact Nat.dvd_of_mul_dvd_mul_right Nat.card_pos
    (by simpa only [mul_assoc] using hden')

/-- Multiplying the lower cardinal by the common degree-square weight gives
the source quantity `lb3`. -/
theorem pTypeCore_lowerCard_mul_degreeSq
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let a := pTypeNonGaloisIndex hD not_Galois
    let v := (_root_.commutator U).index
    ((((D.p - 1) * v) / a ^ 2 : ℕ) : ℝ) *
        (((D.q * a : ℕ) : ℝ) ^ 2) =
      (((D.p - 1) * D.q ^ 2 * v : ℕ) : ℝ) := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let v := (_root_.commutator U).index
  have hdvd : a ^ 2 ∣ (D.p - 1) * v :=
    pTypeCore_indexSquare_dvd_primePred_mul_derivedIndex
      ctx facts not_Galois
  have hcancel : ((D.p - 1) * v) / a ^ 2 * a ^ 2 =
      (D.p - 1) * v := Nat.div_mul_cancel hdvd
  have hnat : ((D.p - 1) * v) / a ^ 2 * (D.q * a) ^ 2 =
      (D.p - 1) * D.q ^ 2 * v := by
    calc
      ((D.p - 1) * v) / a ^ 2 * (D.q * a) ^ 2 =
          D.q ^ 2 * (((D.p - 1) * v) / a ^ 2 * a ^ 2) := by
            ring
      _ = D.q ^ 2 * ((D.p - 1) * v) := by rw [hcancel]
      _ = (D.p - 1) * D.q ^ 2 * v := by ring
  exact_mod_cast hnat

/-! ## Degree weights and finite sums -/

/-- A virtual character with zero self-pairing is the zero class function. -/
private theorem pTypeCore_virtual_eq_zero_of_pairing_self_eq_zero
    {M : Type u} [Group M] [Fintype M]
    {chi : ClassFunction M ℂ}
    (hchi : ClassFunction.IsVirtual chi)
    (hpair : characterPairing chi chi = 0) :
    chi = 0 := by
  obtain ⟨v, rfl⟩ := hchi
  have hv : normSq v = 0 := by
    apply Int.cast_injective (α := ℂ)
    simpa only [normSq, Int.cast_zero] using
      (VirtualCharacter.characterPairing_realize v v).symm.trans hpair
  rw [(normSq_eq_zero_iff v).mp hv]
  simp

/-- Every member of a subcoherent source family has strictly positive degree
weight. -/
theorem pTypeCore_degreeWeight_pos
    {M G : Type u}
    [Group M] [Fintype M] [Group G] [Fintype G]
    {S : Set (ClassFunction M ℂ)}
    {tau : ClassFunction M ℂ →ₗ[ℂ] ClassFunction G ℂ}
    {R : ClassFunction M ℂ → Finset (ClassFunction G ℂ)}
    (hsub : subcoherent S tau R)
    {chi : ClassFunction M ℂ} (hchi : chi ∈ S) :
    0 < pTypeCoreDegreeWeight chi := by
  obtain ⟨d, hd⟩ :=
    (hsub.source_character chi hchi).exists_nat_degree
  obtain ⟨n, hn⟩ :=
    (hsub.source_virtual chi hchi).exists_nat_norm
  have hdPos : 0 < d := by
    by_contra hdNot
    have hdZero : d = 0 := Nat.eq_zero_of_not_pos hdNot
    apply hsub.degree_ne_zero chi hchi
    rw [hd, hdZero]
    simp
  have hnPos : 0 < n := by
    by_contra hnNot
    have hnZero : n = 0 := Nat.eq_zero_of_not_pos hnNot
    have hpairZero : characterPairing chi chi = 0 := by
      rw [hn, hnZero]
      simp
    have hchiZero := pTypeCore_virtual_eq_zero_of_pairing_self_eq_zero
      (hsub.source_virtual chi hchi) hpairZero
    exact hsub.zero_not_mem (hchiZero ▸ hchi)
  rw [pTypeCoreDegreeWeight, pTypeCoreDegreeReal,
    pTypeCoreNormReal, hd, hn]
  norm_num
  positivity

/-- An irreducible character of degree `d` contributes exactly `d²`. -/
theorem pTypeCore_degreeWeight_of_irreducible_degree
    {M : Type u} [Group M] [Fintype M]
    {chi : ClassFunction M ℂ} {d : ℕ}
    (hchi : pTypeIsIrreducibleOfDegree d chi) :
    pTypeCoreDegreeWeight chi = (d : ℝ) ^ 2 := by
  obtain ⟨zeta, hzeta, hdegree⟩ := hchi
  letI : Invertible (Nat.card M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hdegree' : Module.finrank ℂ zeta.representation = d := by
    simpa only [pTypeIrreducibleDegree] using hdegree
  rw [← hzeta, pTypeCoreDegreeWeight, pTypeCoreDegreeReal,
    pTypeCoreNormReal,
    IrreducibleCharacter.apply_one_eq_finrank,
    IrreducibleCharacter.characterPairing_self,
    hdegree']
  norm_num

/-- The set-based coherence sum and the local finset sum agree for a coerced
finset. -/
theorem pTypeCore_coherenceDegreeSum_eq
    {M : Type u} [Group M] [Fintype M]
    (S : Finset (ClassFunction M ℂ))
    (hS : (↑S : Set (ClassFunction M ℂ)).Finite) :
    coherenceDegreeSum (↑S : Set (ClassFunction M ℂ)) hS =
      pTypeCoreDegreeSum S := by
  have hto : hS.toFinset = S := by
    ext chi
    simp
  rw [coherenceDegreeSum, hto, pTypeCoreDegreeSum]
  apply Finset.sum_congr rfl
  intro chi _
  rfl

/-- The lower-slice degree sum is its cardinality times the common squared
degree. -/
theorem pTypeCoreLowerSlice_degreeSum
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    pTypeCoreDegreeSum (pTypeCoreLowerSlice ctx facts not_Galois) =
      ((pTypeCoreLowerSlice ctx facts not_Galois).card : ℝ) *
        (((Ptype_factor_action ctx facts).q *
          pTypeNonGaloisIndex
            (Ptype_factor_action_hypotheses ctx facts) not_Galois : ℕ) : ℝ) ^ 2 := by
  rw [pTypeCoreDegreeSum]
  calc
    (∑ chi ∈ pTypeCoreLowerSlice ctx facts not_Galois,
        pTypeCoreDegreeWeight chi) =
      ∑ _chi ∈ pTypeCoreLowerSlice ctx facts not_Galois,
        (((Ptype_factor_action ctx facts).q *
          pTypeNonGaloisIndex
            (Ptype_factor_action_hypotheses ctx facts) not_Galois : ℕ) : ℝ) ^ 2 := by
      apply Finset.sum_congr rfl
      intro chi hchi
      exact pTypeCore_degreeWeight_of_irreducible_degree
        (Finset.mem_filter.mp hchi).2
    _ = ((pTypeCoreLowerSlice ctx facts not_Galois).card : ℝ) *
        (((Ptype_factor_action ctx facts).q *
          pTypeNonGaloisIndex
            (Ptype_factor_action_hypotheses ctx facts) not_Galois : ℕ) : ℝ) ^ 2 := by
      simp

/-- For positive weights, equality of sums along an inclusion forces the
reverse inclusion. -/
theorem pTypeCore_subset_of_degreeSum_eq
    {M : Type u} [Group M] [Fintype M]
    {A B : Finset (ClassFunction M ℂ)}
    (hAB : A ⊆ B)
    (hpos : ∀ chi ∈ B, 0 < pTypeCoreDegreeWeight chi)
    (hsum : pTypeCoreDegreeSum A = pTypeCoreDegreeSum B) :
    B ⊆ A := by
  intro chi hchiB
  by_contra hchiA
  have hlt : pTypeCoreDegreeSum A < pTypeCoreDegreeSum B := by
    rw [pTypeCoreDegreeSum, pTypeCoreDegreeSum]
    exact Finset.sum_lt_sum_of_subset hAB hchiB hchiA
      (hpos chi hchiB)
      (fun z hzB _hzA ↦ (hpos z hzB).le)
  exact (ne_of_lt hlt) hsum

/-- The cardinal lower bound, after weighting, gives `lb3`; equality is
equivalent to equality in the cardinal bound. -/
theorem pTypeCore_lb3_le_lowerSliceDegreeSum
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let a := pTypeNonGaloisIndex hD not_Galois
    let v := (_root_.commutator U).index
    let lower := ((D.p - 1) * v) / a ^ 2
    (((D.p - 1) * D.q ^ 2 * v : ℕ) : ℝ) ≤
        pTypeCoreDegreeSum
          (pTypeCoreLowerSlice ctx facts not_Galois) ∧
      ((((D.p - 1) * D.q ^ 2 * v : ℕ) : ℝ) =
          pTypeCoreDegreeSum
            (pTypeCoreLowerSlice ctx facts not_Galois) ↔
        (pTypeCoreLowerSlice ctx facts not_Galois).card = lower) := by
  dsimp only
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let v := (_root_.commutator U).index
  let lower := ((D.p - 1) * v) / a ^ 2
  let X := pTypeCoreLowerSlice ctx facts not_Galois
  let w : ℝ := (((D.q * a : ℕ) : ℝ) ^ 2)
  have hcard : lower ≤ X.card :=
    pTypeCoreLowerSlice_card_lower_bound ctx facts not_Galois
  have hcardReal : (lower : ℝ) ≤ (X.card : ℝ) := by
    exact_mod_cast hcard
  have haPos : 0 < a :=
    Nat.zero_lt_of_lt (one_lt_pTypeNonGaloisIndex hD not_Galois)
  have hqPos : 0 < D.q := D.q_prime.pos
  have hwPos : 0 < w := by
    dsimp [w]
    positivity
  have hsum : pTypeCoreDegreeSum X = (X.card : ℝ) * w :=
    pTypeCoreLowerSlice_degreeSum ctx facts not_Galois
  have hlower : (((D.p - 1) * D.q ^ 2 * v : ℕ) : ℝ) =
      (lower : ℝ) * w :=
    (pTypeCore_lowerCard_mul_degreeSq ctx facts not_Galois).symm
  rw [hsum, hlower]
  refine ⟨by nlinarith, ?_⟩
  constructor
  · intro heq
    have hcast : (X.card : ℝ) = (lower : ℝ) := by
      nlinarith
    exact_mod_cast hcast
  · intro heq
    rw [heq]

/-- A current family containing the whole degree slice has at least the lower
slice's degree sum.  Equality forces it back into the lower slice. -/
theorem pTypeCore_lowerSlice_degreeSum_le_current
    {G Q : Type u}
    [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    [Group Q] [Fintype Q]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (S₂ : Finset (ClassFunction M ℂ))
    (tau : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ))
    (hsub : subcoherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)) tau R)
    (hbase : (↑(pTypeCoreDegreeSlice (pTypeCoreFamilyOfContext ctx)
        ((Ptype_factor_action ctx facts).q *
          pTypeNonGaloisIndex
            (Ptype_factor_action_hypotheses ctx facts) not_Galois)) :
          Set (ClassFunction M ℂ)) ⊆
        (↑S₂ : Set (ClassFunction M ℂ)))
    (hS₂ : (↑S₂ : Set (ClassFunction M ℂ)) ⊆
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ))) :
    pTypeCoreDegreeSum (pTypeCoreLowerSlice ctx facts not_Galois) ≤
        pTypeCoreDegreeSum S₂ ∧
      (pTypeCoreDegreeSum (pTypeCoreLowerSlice ctx facts not_Galois) =
          pTypeCoreDegreeSum S₂ →
        (↑S₂ : Set (ClassFunction M ℂ)) ⊆
          (↑(pTypeCoreLowerSlice ctx facts not_Galois) :
            Set (ClassFunction M ℂ))) := by
  let X := pTypeCoreLowerSlice ctx facts not_Galois
  have hXS₂ : X ⊆ S₂ := by
    intro chi hchi
    exact hbase
      (pTypeCoreLowerSlice_subset_degreeSlice ctx facts not_Galois hchi)
  have hpos : ∀ chi ∈ S₂, 0 < pTypeCoreDegreeWeight chi := by
    intro chi hchi
    exact pTypeCore_degreeWeight_pos hsub (hS₂ hchi)
  constructor
  · rw [pTypeCoreDegreeSum, pTypeCoreDegreeSum]
    exact Finset.sum_le_sum_of_subset_of_nonneg hXS₂
      (fun chi hchi _ ↦ (hpos chi hchi).le)
  · intro hsum
    exact pTypeCore_subset_of_degreeSum_eq hXS₂ hpos hsum

/-! ## The rigid equality package -/

/-- The conclusions forced when every inequality in Peterfalvi (9.11.1) is
an equality.  Later phases consume this package instead of repeating the
degree-slice bookkeeping. -/
structure PTypeCoreRigidFacts
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (S₂ : Finset (ClassFunction M ℂ)) : Prop where
  current_eq_slice :
    S₂ = pTypeCoreDegreeSlice (pTypeCoreFamilyOfContext ctx)
      ((Ptype_factor_action ctx facts).q *
        pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois)
  slice_irreducible :
    ∀ chi ∈ S₂, IsIrreducibleCharacter M ℂ chi
  slice_small_kernel :
    ∀ chi ∈ S₂,
      chi ∈ pTypeCoreFamily
        (pTypeCoreDerived M) (pTypeCoreFitting M)
        (pTypeH0CInDerived M (derivedWithin M)
          (Ptype_Fcore_kernel ctx) U W₁
          (Ptype_factor_action ctx facts))
  index_eq_half_prime_pred :
    pTypeNonGaloisIndex
        (Ptype_factor_action_hypotheses ctx facts) not_Galois =
      ((Ptype_factor_action ctx facts).p - 1) / 2
  action_kernel_eq_commutator :
    (Ptype_factor_action ctx facts).C = _root_.commutator U
  remainder_degree :
    ∀ chi ∈ pTypeCoreRemainder (pTypeCoreFamilyOfContext ctx) S₂,
      chi 1 =
        (((Ptype_factor_action ctx facts).q *
          pTypeActionFactorCard (Ptype_factor_action ctx facts) : ℕ) : ℂ)
  forced_degrees_ne :
    (Ptype_factor_action ctx facts).q *
        pTypeActionFactorCard (Ptype_factor_action ctx facts) ≠
      (Ptype_factor_action ctx facts).q *
        pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois
  slice_card :
    S₂.card =
      (((Ptype_factor_action ctx facts).p - 1) *
          pTypeActionFactorCard (Ptype_factor_action ctx facts)) /
        pTypeNonGaloisIndex
            (Ptype_factor_action_hypotheses ctx facts) not_Galois ^ 2
  slice_card_two :
    S₂.card =
      (2 * pTypeActionFactorCard (Ptype_factor_action ctx facts)) /
        pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois

namespace PTypeCoreRigidFacts

/-- Every core-family member has one of the two degrees distinguished by the
rigid equality case. -/
theorem degree_cases
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    {ctx : PTypeFCoreContext M U W W₁ W₂}
    {facts : PTypeFCoreFactorFacts ctx}
    {not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts)}
    {S₂ : Finset (ClassFunction M ℂ)}
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂) :
    ∀ chi ∈ pTypeCoreFamilyOfContext ctx,
      chi 1 =
          (((Ptype_factor_action ctx facts).q *
            pTypeActionFactorCard (Ptype_factor_action ctx facts) : ℕ) : ℂ) ∨
        chi 1 =
          (((Ptype_factor_action ctx facts).q *
            pTypeNonGaloisIndex
              (Ptype_factor_action_hypotheses ctx facts) not_Galois : ℕ) : ℂ) := by
  intro chi hchi
  by_cases hchi₂ : chi ∈ S₂
  · right
    have hslice : chi ∈
        pTypeCoreDegreeSlice (pTypeCoreFamilyOfContext ctx)
          ((Ptype_factor_action ctx facts).q *
            pTypeNonGaloisIndex
              (Ptype_factor_action_hypotheses ctx facts) not_Galois) := by
      rw [← rigid.current_eq_slice]
      exact hchi₂
    exact (Finset.mem_filter.mp hslice).2
  · left
    exact rigid.remainder_degree chi
      (Finset.mem_filter.mpr ⟨hchi, hchi₂⟩)

end PTypeCoreRigidFacts

end PTypeCoreBoundsInternal

end

end Submission.OddOrder.PF
