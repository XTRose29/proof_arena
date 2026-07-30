import Submission.OddOrder.PF.Section09.PTypeCoreActionKernel
import Submission.OddOrder.PF.Section09.PTypeNonGaloisConclusion

/-!
# Peterfalvi Section 9: the non-Galois core dichotomy

This module isolates the numerical part of Peterfalvi (9.11).  Either the
current coherent family can be enlarged immediately, or every intervening
degree estimate is an equality.  In the latter case we obtain the rigid
degree package, count the irreducible remainder, and prove that this remainder
is larger than the norm needed by the subsequent extension argument.

Only the dichotomy and the final strict remainder bound are exported through
`PTypeCoreNonGaloisDichotomyInternal`; the degree-sum and arithmetic lemmas are
local implementation details.
-/

namespace Submission.OddOrder.PF

noncomputable section

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.BG.Section16
open Submission.OddOrder.MathlibSupport
open PTypeCoreContextInternal
open PTypeCoreBoundsInternal
open PTypeCoreActionKernelInternal
open scoped BigOperators Classical

universe u

namespace PTypeCoreNonGaloisDichotomyInternal

set_option maxHeartbeats 2500000

/-! ## The short arm of (9.11.1) -/

/-- Clause (9.8a) makes every degree in the full core family a natural
multiple of the distinguished degree `q * a`. -/
private theorem degree_multiple_of_rigid_slice
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    {chi psi : ClassFunction M ℂ}
    (hchi : chi ∈ pTypeCoreFamilyOfContext ctx)
    (hpsi : psi ∈ pTypeCoreDegreeSlice
      (pTypeCoreFamilyOfContext ctx)
      ((Ptype_factor_action ctx facts).q *
        pTypeNonGaloisIndex
          (Ptype_factor_action_hypotheses ctx facts) not_Galois)) :
    ∃ n : ℕ, chi 1 = (n : ℂ) * psi 1 := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀ := pTypeCoreKernel ctx
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  have hchiInduced : chi ∈ seqIndD (k := ℂ) HU H H₀CPrime := by
    convert hchi using 1
    unfold pTypeCoreFamilyOfContext
    congr 1 <;> apply Subsingleton.elim
  obtain ⟨s, hs, rfl⟩ := seqIndP.mp hchiInduced
  have hH₀Prime : H₀ ≤ H₀CPrime := by
    dsimp [H₀, H₀CPrime, pTypeCoreKernelDerivedComplement,
      pTypeH0CPrimeInDerived]
    exact le_sup_left
  have hs₀ : s ∈ Iirr_kerD (k := ℂ) H H₀ :=
    Iirr_kerDS (k := ℂ)
      (A₁ := H₀CPrime) (A₂ := H₀)
      (B₁ := H) (B₂ := H) hH₀Prime le_rfl hs
  have hfixed :=
    (typeP_nonGalois_characters ctx not_Galois).fixed_degree_divisibility
  change ∀ zeta ∈ Iirr_kerD (k := ℂ) H H₀,
    pTypeNonGaloisIndex hD not_Galois ∣
      pTypeIrreducibleDegree zeta at hfixed
  obtain ⟨n, hn⟩ := hfixed s hs₀
  have hpsiDegree := (Finset.mem_filter.mp hpsi).2
  refine ⟨n, ?_⟩
  change Module.finrank ℂ s.representation =
      pTypeNonGaloisIndex hD not_Galois * n at hn
  calc
    ClassFunction.induce HU (s : ClassFunction HU ℂ) 1 =
        (HU.index : ℂ) * s 1 := ClassFunction.induce_one HU _
    _ = (D.q : ℂ) *
        (Module.finrank ℂ s.representation : ℂ) := by
      rw [pTypeCore_index_eq_q ctx facts,
        IrreducibleCharacter.apply_one_eq_finrank]
    _ = (n : ℂ) *
        (((D.q * pTypeNonGaloisIndex hD not_Galois : ℕ) : ℂ)) := by
      rw [hn]
      push_cast
      ring
    _ = (n : ℂ) * psi 1 := by rw [hpsiDegree]

/-- Convert the strict numerical arm directly into Peterfalvi's coherence
extension theorem. -/
private theorem extend_from_strict_degree_sum
    {M Q : Type u}
    [Group M] [Fintype M] [Group Q] [Fintype Q]
    {S₀ S₂ : Finset (ClassFunction M ℂ)}
    {tau : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ}
    {R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ)}
    (hsub : subcoherent (↑S₀ : Set (ClassFunction M ℂ)) tau R)
    (hS₂ : cfConjC_subset
      (↑S₂ : Set (ClassFunction M ℂ))
      (↑S₀ : Set (ClassFunction M ℂ)))
    (hcoh₂ : coherent (↑S₂ : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau)
    {chi phi : ClassFunction M ℂ}
    (hphi : phi ∈ S₂) (hchi : chi ∈ S₀) (hchiNot : chi ∉ S₂)
    (hdiv : ∃ n : ℕ, chi 1 = (n : ℂ) * phi 1)
    (hstrict :
      2 * (chi 1).re * (phi 1).re <
        coherenceDegreeSum (↑S₂ : Set (ClassFunction M ℂ))
          (hsub.finite.subset hS₂.1)) :
    coherent
      ({chi, ClassFunction.inverseLinear chi} ∪
        (↑S₂ : Set (ClassFunction M ℂ)))
      (nonidentitySet M) tau :=
  extend_coherent hsub hS₂ hphi hchi hchiNot hcoh₂ hdiv hstrict

/-! ## The equality dichotomy -/

/-- Peterfalvi (9.11.1).  Either a member outside `S₂` gives an immediate
coherent extension, or all degree estimates are sharp and `S₂` carries the
rigid equality package used in the remaining non-Galois argument. -/
theorem pTypeCore_nonGalois_early_or_rigid
    {G Q : Type u}
    [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    [Group Q] [Fintype Q]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (S₂ : Finset (ClassFunction M ℂ))
    (tau tau₂ : ClassFunction M ℂ →ₗ[ℂ] ClassFunction Q ℂ)
    (R : ClassFunction M ℂ → Finset (ClassFunction Q ℂ))
    (hsub : subcoherent
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)) tau R)
    (hbase :
      (↑(pTypeCoreDegreeSlice (pTypeCoreFamilyOfContext ctx)
        ((Ptype_factor_action ctx facts).q *
          pTypeNonGaloisIndex
            (Ptype_factor_action_hypotheses ctx facts) not_Galois)) :
          Set (ClassFunction M ℂ)) ⊆
        (↑S₂ : Set (ClassFunction M ℂ)))
    (hS₂ : cfConjC_subset
      (↑S₂ : Set (ClassFunction M ℂ))
      (↑(pTypeCoreFamilyOfContext ctx) : Set (ClassFunction M ℂ)))
    (hcohWith₂ : coherent_with
      (↑S₂ : Set (ClassFunction M ℂ))
      (nonidentitySet M) tau tau₂)
    (hremaining : ∃ chi ∈ pTypeCoreFamilyOfContext ctx, chi ∉ S₂) :
    (∃ chi : ClassFunction M ℂ,
        chi ∈ pTypeCoreFamilyOfContext ctx ∧ chi ∉ S₂ ∧
          coherent
            ({chi, ClassFunction.inverseLinear chi} ∪
              (↑S₂ : Set (ClassFunction M ℂ)))
            (nonidentitySet M) tau) ∨
      PTypeCoreRigidFacts ctx facts not_Galois S₂ := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let u₀ := pTypeActionFactorCard D
  let v := (_root_.commutator U).index
  let S₀ := pTypeCoreFamilyOfContext ctx
  let S₁ := pTypeCoreDegreeSlice S₀ (D.q * a)
  let S₃ := pTypeCoreRemainder S₀ S₂
  let X := pTypeCoreLowerSlice ctx facts not_Galois
  let lower := ((D.p - 1) * v) / a ^ 2
  let lowerAtDegree (d : ℕ) : ℝ := ((2 * D.q * a * d : ℕ) : ℝ)
  let lowerIndex : ℝ := ((2 * a * D.q ^ 2 * u₀ : ℕ) : ℝ)
  let lowerPrime : ℝ := (((D.p - 1) * D.q ^ 2 * u₀ : ℕ) : ℝ)
  let lowerDerived : ℝ := (((D.p - 1) * D.q ^ 2 * v : ℕ) : ℝ)

  obtain ⟨chi₀, hchi₀, hchi₂⟩ := hremaining
  have hchi₃ : chi₀ ∈ S₃ :=
    Finset.mem_filter.mpr ⟨hchi₀, hchi₂⟩
  obtain ⟨chi, hchi₃, hselected⟩ :
      ∃ chi ∈ S₃,
        chi 1 = ((D.q * u₀ : ℕ) : ℂ) →
          ∀ z ∈ S₃, z 1 = ((D.q * u₀ : ℕ) : ℂ) := by
    by_cases hall : ∀ z ∈ S₃,
        z 1 = ((D.q * u₀ : ℕ) : ℂ)
    · exact ⟨chi₀, hchi₃, fun _ ↦ hall⟩
    · push Not at hall
      obtain ⟨chi, hchi, hdegree⟩ := hall
      exact ⟨chi, hchi, fun h ↦ (hdegree h).elim⟩
  have hchi₀' : chi ∈ S₀ := (Finset.mem_filter.mp hchi₃).1
  have hchi₂' : chi ∉ S₂ := (Finset.mem_filter.mp hchi₃).2
  obtain ⟨d, hd⟩ :=
    (hsub.source_character chi hchi₀').exists_nat_degree
  have hdLe : d ≤ D.q * u₀ := by
    have hbound := pTypeCore_member_degree_le_q_mul_factorCard
      ctx facts hchi₀'
    rw [hd] at hbound
    norm_num at hbound
    have hbound' : (d : ℝ) ≤ (D.q : ℝ) * (u₀ : ℝ) := by
      simpa only [D, u₀, Ptype_factor_action_q,
        Nat.card_eq_fintype_card] using hbound
    exact_mod_cast hbound'
  have haPos : 0 < a :=
    Nat.zero_lt_of_lt (one_lt_pTypeNonGaloisIndex hD not_Galois)
  have hqPos : 0 < D.q := D.q_prime.pos
  have huPos : 0 < u₀ := by
    dsimp [u₀, pTypeActionFactorCard]
    exact Nat.card_pos
  have hvPos : 0 < v :=
    Nat.pos_of_ne_zero
      (_root_.commutator U).index_ne_zero_of_finite
  have hpPredPos : 0 < D.p - 1 :=
    Nat.sub_pos_of_lt D.p_prime.one_lt

  have hdegreeStep : lowerAtDegree d ≤ lowerIndex := by
    dsimp [lowerAtDegree, lowerIndex]
    have hnat : 2 * D.q * a * d ≤ 2 * a * D.q ^ 2 * u₀ := by
      calc
        2 * D.q * a * d ≤ 2 * D.q * a * (D.q * u₀) :=
          Nat.mul_le_mul_left (2 * D.q * a) hdLe
        _ = 2 * a * D.q ^ 2 * u₀ := by ring
    exact_mod_cast hnat
  have htwice := pTypeCore_twice_index_le_prime_pred
    ctx facts not_Galois
  have hindexStep : lowerIndex ≤ lowerPrime := by
    have htwice' : (2 * a : ℕ) ≤ D.p - 1 := htwice.1
    dsimp [lowerIndex, lowerPrime]
    have hnat : 2 * a * D.q ^ 2 * u₀ ≤
        (D.p - 1) * D.q ^ 2 * u₀ := by
      calc
        2 * a * D.q ^ 2 * u₀ =
            (2 * a) * (D.q ^ 2 * u₀) := by ring
        _ ≤ (D.p - 1) * (D.q ^ 2 * u₀) :=
          Nat.mul_le_mul_right (D.q ^ 2 * u₀) htwice'
        _ = (D.p - 1) * D.q ^ 2 * u₀ := by ring
    exact_mod_cast hnat
  have hfactor := pTypeCore_factorCard_le_derivedIndex D hD
  have hderivedStep : lowerPrime ≤ lowerDerived := by
    dsimp [lowerPrime, lowerDerived]
    exact_mod_cast Nat.mul_le_mul_left ((D.p - 1) * D.q ^ 2)
      hfactor.1
  have hlowerData := pTypeCore_lb3_le_lowerSliceDegreeSum
    ctx facts not_Galois
  have hlowerSlice : lowerDerived ≤ pTypeCoreDegreeSum X := by
    simpa only [D, hD, a, v, X, lowerDerived] using hlowerData.1
  have hcurrentData := pTypeCore_lowerSlice_degreeSum_le_current
    ctx facts not_Galois S₂ tau R hsub hbase hS₂.1
  have hsliceCurrent : pTypeCoreDegreeSum X ≤
      pTypeCoreDegreeSum S₂ := by
    simpa only [X] using hcurrentData.1

  by_cases hstrict : lowerAtDegree d < pTypeCoreDegreeSum S₂
  · left
    have hdenDvd : a ^ 2 ∣ (D.p - 1) * v :=
      pTypeCore_indexSquare_dvd_primePred_mul_derivedIndex
        ctx facts not_Galois
    have hlowerPos : 0 < lower := by
      have hnumerPos : 0 < (D.p - 1) * v :=
        Nat.mul_pos hpPredPos hvPos
      have hcancel : lower * a ^ 2 = (D.p - 1) * v := by
        simpa only [lower] using Nat.div_mul_cancel hdenDvd
      by_contra hnot
      have hzero : lower = 0 := Nat.eq_zero_of_not_pos hnot
      rw [hzero, zero_mul] at hcancel
      omega
    have hcardLower : lower ≤ X.card := by
      simpa only [lower, X] using
        pTypeCoreLowerSlice_card_lower_bound ctx facts not_Galois
    obtain ⟨phi, hphiX⟩ :=
      Finset.card_pos.mp (hlowerPos.trans_le hcardLower)
    have hphiSlice : phi ∈ S₁ :=
      pTypeCoreLowerSlice_subset_degreeSlice
        ctx facts not_Galois hphiX
    have hphi₂ : phi ∈ S₂ := hbase hphiSlice
    have hphiDegree : phi 1 = ((D.q * a : ℕ) : ℂ) :=
      (Finset.mem_filter.mp hphiSlice).2
    have hdiv := degree_multiple_of_rigid_slice
      ctx facts not_Galois hchi₀' hphiSlice
    have hstrict' :
        2 * (chi 1).re * (phi 1).re <
          coherenceDegreeSum (↑S₂ : Set (ClassFunction M ℂ))
            (hsub.finite.subset hS₂.1) := by
      rw [pTypeCore_coherenceDegreeSum_eq S₂
        (hsub.finite.subset hS₂.1)]
      rw [hd, hphiDegree]
      norm_num
      dsimp [lowerAtDegree] at hstrict
      norm_num only [Nat.cast_mul] at hstrict
      nlinarith
    exact ⟨chi, hchi₀', hchi₂',
      extend_from_strict_degree_sum hsub hS₂ ⟨tau₂, hcohWith₂⟩
        hphi₂ hchi₀' hchi₂' hdiv hstrict'⟩
  · right
    have hsumLeDegree : pTypeCoreDegreeSum S₂ ≤ lowerAtDegree d :=
      le_of_not_gt hstrict
    have hindexLeSum : lowerIndex ≤ pTypeCoreDegreeSum S₂ :=
      hindexStep.trans
        (hderivedStep.trans (hlowerSlice.trans hsliceCurrent))
    have hprimeLeSum : lowerPrime ≤ pTypeCoreDegreeSum S₂ :=
      hderivedStep.trans (hlowerSlice.trans hsliceCurrent)
    have hderivedLeSum : lowerDerived ≤ pTypeCoreDegreeSum S₂ :=
      hlowerSlice.trans hsliceCurrent
    have hdegreeEq : lowerAtDegree d = lowerIndex :=
      le_antisymm hdegreeStep (hindexLeSum.trans hsumLeDegree)
    have hindexEq : lowerIndex = lowerPrime :=
      le_antisymm hindexStep
        (hprimeLeSum.trans (hsumLeDegree.trans hdegreeStep))
    have hderivedEq : lowerPrime = lowerDerived :=
      le_antisymm hderivedStep
        (hderivedLeSum.trans
          (hsumLeDegree.trans (hdegreeStep.trans hindexStep)))
    have hlowerEq : lowerDerived = pTypeCoreDegreeSum X :=
      le_antisymm hlowerSlice
        (hsliceCurrent.trans
          (hsumLeDegree.trans
            (hdegreeStep.trans (hindexStep.trans hderivedStep))))
    have hcurrentEq : pTypeCoreDegreeSum X =
        pTypeCoreDegreeSum S₂ :=
      le_antisymm hsliceCurrent
        (hsumLeDegree.trans
          (hdegreeStep.trans
            (hindexStep.trans (hderivedStep.trans hlowerSlice))))

    have hdEqNat : d = D.q * u₀ := by
      dsimp [lowerAtDegree, lowerIndex] at hdegreeEq
      norm_num only [Nat.cast_mul, Nat.cast_pow] at hdegreeEq
      have hdegreeEqNat : 2 * D.q * a * d =
          2 * a * D.q ^ 2 * u₀ := by
        exact_mod_cast hdegreeEq
      have hmul : (2 * D.q * a) * d =
          (2 * D.q * a) * (D.q * u₀) := by
        calc
          (2 * D.q * a) * d = 2 * D.q * a * d := by ring
          _ = 2 * a * D.q ^ 2 * u₀ := hdegreeEqNat
          _ = (2 * D.q * a) * (D.q * u₀) := by ring
      exact Nat.mul_left_cancel
        (Nat.mul_pos (Nat.mul_pos (by omega) hqPos) haPos) hmul
    have hdEq : d = D.q * u₀ := hdEqNat
    have hchiDegree : chi 1 = ((D.q * u₀ : ℕ) : ℂ) := by
      rw [hd, hdEq]
    have htwiceEq : (2 * a : ℕ) = D.p - 1 := by
      dsimp [lowerIndex, lowerPrime] at hindexEq
      norm_num only [Nat.cast_mul, Nat.cast_pow] at hindexEq
      have hindexEqNat : 2 * a * D.q ^ 2 * u₀ =
          (D.p - 1) * D.q ^ 2 * u₀ := by
        exact_mod_cast hindexEq
      have hmul : (2 * a) * (D.q ^ 2 * u₀) =
          (D.p - 1) * (D.q ^ 2 * u₀) := by
        simpa only [mul_assoc] using hindexEqNat
      exact Nat.mul_right_cancel
        (Nat.mul_pos (pow_pos hqPos 2) huPos) hmul
    have haHalf : a = (D.p - 1) / 2 := htwice.2.mp htwiceEq
    have hfactorEqNat : u₀ = v := by
      dsimp [lowerPrime, lowerDerived] at hderivedEq
      norm_num only [Nat.cast_mul, Nat.cast_pow] at hderivedEq
      have hderivedEqNat : (D.p - 1) * D.q ^ 2 * u₀ =
          (D.p - 1) * D.q ^ 2 * v := by
        exact_mod_cast hderivedEq
      have hmul : ((D.p - 1) * D.q ^ 2) * u₀ =
          ((D.p - 1) * D.q ^ 2) * v := by
        simpa only [mul_assoc] using hderivedEqNat
      exact Nat.mul_left_cancel
        (Nat.mul_pos hpPredPos (pow_pos hqPos 2)) hmul
    have hfactorEq : u₀ = v := hfactorEqNat
    have hCeq : D.C = _root_.commutator U :=
      hfactor.2.mp hfactorEq
    have hcardX : X.card = lower := by
      apply hlowerData.2.mp
      simpa only [D, hD, a, v, X, lowerDerived] using hlowerEq
    have hS₂X : S₂ ⊆ X := by
      apply hcurrentData.2
      simpa only [X] using hcurrentEq
    have hXS₂ : X ⊆ S₂ := by
      intro z hz
      exact hbase (pTypeCoreLowerSlice_subset_degreeSlice
        ctx facts not_Galois hz)
    have hS₂Xeq : S₂ = X := Finset.Subset.antisymm hS₂X hXS₂
    have hcurrent : S₂ = S₁ := by
      apply Finset.Subset.antisymm
      · intro z hz
        rw [hS₂Xeq] at hz
        exact pTypeCoreLowerSlice_subset_degreeSlice
          ctx facts not_Galois hz
      · exact hbase
    have hirr : ∀ z ∈ S₂, IsIrreducibleCharacter M ℂ z := by
      intro z hz
      exact pTypeCoreLowerSlice_irreducible
        (ctx := ctx) (facts := facts) (not_Galois := not_Galois)
        (hS₂X hz)
    have hsmall : ∀ z ∈ S₂,
        z ∈ pTypeCoreFamily
          (pTypeCoreDerived M) (pTypeCoreFitting M)
          (pTypeH0CInDerived M (derivedWithin M)
            (Ptype_Fcore_kernel ctx) U W₁ D) := by
      intro z hz
      have hzX : z ∈ X := by rw [← hS₂Xeq]; exact hz
      have hzLower := (Finset.mem_filter.mp hzX).1
      have hkernelEq :=
        pTypeCoreH0C_eq_H0UPrime_of_C_eq_commutator
          ctx facts hCeq
      change z ∈ pTypeCoreFamily
        (pTypeCoreDerived M) (pTypeCoreFitting M)
        (pTypeH0CInDerived M (derivedWithin M)
          (Ptype_Fcore_kernel ctx) U W₁ D)
      rw [hkernelEq]
      exact hzLower
    have hremainder : ∀ z ∈ S₃,
        z 1 = ((D.q * u₀ : ℕ) : ℂ) :=
      hselected hchiDegree
    have hdegreesNe : D.q * u₀ ≠ D.q * a := by
      intro heq
      apply hchi₂'
      apply hbase
      apply Finset.mem_filter.mpr
      refine ⟨hchi₀', ?_⟩
      rw [← heq]
      exact hchiDegree
    have hsliceCard : S₂.card = ((D.p - 1) * u₀) / a ^ 2 := by
      rw [hS₂Xeq, hcardX]
      simpa only [lower, hfactorEq]
    have haDvdU := pTypeCore_nonGalois_index_dvd_factorCard
      ctx facts not_Galois
    have hquotient : ((D.p - 1) * u₀) / a ^ 2 =
        (2 * u₀) / a := by
      obtain ⟨m, hm⟩ := haDvdU
      change u₀ = a * m at hm
      rw [htwiceEq.symm, hm]
      calc
        (2 * a * (a * m)) / a ^ 2 =
            (a ^ 2 * (2 * m)) / a ^ 2 := by ring
        _ = 2 * m := by
          simpa only [mul_comm] using
            Nat.mul_div_left (2 * m) (pow_pos haPos 2)
        _ = (a * (2 * m)) / a := by
          symm
          simpa only [mul_comm] using
            Nat.mul_div_left (2 * m) haPos
        _ = (2 * (a * m)) / a := by ring
    refine
      { current_eq_slice := ?_
        slice_irreducible := hirr
        slice_small_kernel := ?_
        index_eq_half_prime_pred := ?_
        action_kernel_eq_commutator := ?_
        remainder_degree := ?_
        forced_degrees_ne := ?_
        slice_card := ?_
        slice_card_two := ?_ }
    · simpa only [S₀, S₁, D, hD, a] using hcurrent
    · simpa only [D] using hsmall
    · simpa only [D, hD, a] using haHalf
    · simpa only [D] using hCeq
    · simpa only [S₀, S₃, D, u₀] using hremainder
    · simpa only [D, hD, a, u₀] using hdegreesNe
    · simpa only [D, hD, a, u₀] using hsliceCard
    · simpa only [D, hD, a, u₀] using hsliceCard.trans hquotient

/-! ## The rigid degree-square count -/

/-- Peterfalvi (9.11.3).  Split the `H₀C` layer into the rigid slice, the
irreducible remainder, and the reducible layer, then compare their weighted
degree sums with the global `seqIndD` identity. -/
private theorem rigid_remainder_count
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (S₂ : Finset (ClassFunction M ℂ))
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂) :
    let D := Ptype_factor_action ctx facts
    let HU := pTypeCoreDerived M
    let H := pTypeCoreFitting M
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let S₃ := pTypeCoreRemainder
      (pTypeCoreFamilyOfContext ctx) S₂
    let S₄ := pTypeCoreIrreducibleRemainder HU H H₀C S₃
    D.q * pTypeActionFactorCard D * S₄.card +
        (D.p - 1) * (D.q + pTypeActionFactorCard D) =
      D.p ^ D.q - 1 := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let u₀ := pTypeActionFactorCard D
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀ := pTypeCoreKernel ctx
  let C := pTypeCInDerived M (derivedWithin M) U W₁ D
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let HC := pTypeHCInDerived M (derivedWithin M)
    (Fitting_core M) U W₁ D
  let H₀CPrime := pTypeCoreKernelDerivedComplement ctx
  let S₀ := pTypeCoreFamilyOfContext ctx
  let S₃ := pTypeCoreRemainder S₀ S₂
  let S₄ := pTypeCoreIrreducibleRemainder HU H H₀C S₃
  let mu := pTypeReducibleLayer HU H H₀
  let X := pTypeCoreFamily HU H H₀C
  letI : Invertible (Nat.card M : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr (Nat.card_pos (α := M)).ne')

  have hH₀H : H₀ ≤ H := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M (Ptype_Fcore_kernel_lt ctx).le)
  have hH₀CPrimeC : H₀CPrime ≤ H₀C :=
    pTypeCoreKernelDerivedComplement_le_H0C ctx facts
  have hS₀eq : S₀ = seqIndD (k := ℂ) HU H H₀CPrime := by
    dsimp only [S₀]
    unfold pTypeCoreFamilyOfContext
    congr 1 <;> apply Subsingleton.elim
  have hXsubS₀ : X ⊆ S₀ := by
    intro phi hphi
    obtain ⟨s, hs, rfl⟩ := seqIndP.mp hphi
    rw [hS₀eq]
    exact seqIndP.mpr ⟨s, Iirr_kerDS (k := ℂ)
      (A₁ := H₀C) (A₂ := H₀CPrime)
      (B₁ := H) (B₂ := H) hH₀CPrimeC le_rfl hs, rfl⟩
  have hXsubH₀ : X ⊆ seqIndD (k := ℂ) HU H H₀ := by
    intro phi hphi
    obtain ⟨s, hs, rfl⟩ := seqIndP.mp hphi
    apply seqIndP.mpr
    exact ⟨s, Iirr_kerDS (k := ℂ)
      (A₁ := H₀C) (A₂ := H₀)
      (B₁ := H) (B₂ := H) le_sup_left le_rfl hs, rfl⟩
  have hpartition : X = (S₂ ∪ S₄) ∪ mu := by
    ext phi
    rw [Finset.mem_union, Finset.mem_union]
    constructor
    · intro hphiX
      by_cases hirr : IsIrreducibleCharacter M ℂ phi
      · by_cases hphi₂ : phi ∈ S₂
        · exact Or.inl (Or.inl hphi₂)
        · apply Or.inl
          apply Or.inr
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_filter.mpr ⟨hXsubS₀ hphiX, hphi₂⟩,
            hphiX, hirr⟩
      · apply Or.inr
        exact Finset.mem_filter.mpr ⟨hXsubH₀ hphiX, hirr⟩
    · rintro ((hphi₂ | hphi₄) | hphiMu)
      · simpa only [X, pTypeCoreFamily, HU, H, H₀C, D] using
          rigid.slice_small_kernel phi hphi₂
      · exact (Finset.mem_filter.mp hphi₄).2.1
      · simpa only [X, pTypeCoreFamily, mu, HU, H, H₀, H₀C, D] using
          (pType_nb_redM_H0 ctx facts).2 phi hphiMu
  have hS₂S₄ : Disjoint S₂ S₄ := by
    apply Finset.disjoint_left.mpr
    intro phi hphi₂ hphi₄
    exact (Finset.mem_filter.mp
      (Finset.mem_filter.mp hphi₄).1).2 hphi₂
  have hS₂Mu : Disjoint S₂ mu := by
    apply Finset.disjoint_left.mpr
    intro phi hphi₂ hphiMu
    exact (Finset.mem_filter.mp hphiMu).2
      (rigid.slice_irreducible phi hphi₂)
  have hS₄Mu : Disjoint S₄ mu := by
    apply Finset.disjoint_left.mpr
    intro phi hphi₄ hphiMu
    exact (Finset.mem_filter.mp hphiMu).2
      (Finset.mem_filter.mp hphi₄).2.2
  have hsumPartition :
      (∑ phi ∈ X, phi 1 ^ 2 / characterPairing phi phi) =
        (∑ phi ∈ S₂, phi 1 ^ 2 / characterPairing phi phi) +
        (∑ phi ∈ S₄, phi 1 ^ 2 / characterPairing phi phi) +
        (∑ phi ∈ mu, phi 1 ^ 2 / characterPairing phi phi) := by
    rw [hpartition,
      Finset.sum_union
        (Finset.disjoint_union_left.mpr ⟨hS₂Mu, hS₄Mu⟩),
      Finset.sum_union hS₂S₄]

  have hsumS₂ :
      (∑ phi ∈ S₂, phi 1 ^ 2 / characterPairing phi phi) =
        (S₂.card : ℂ) * (((D.q * a : ℕ) : ℂ) ^ 2) := by
    calc
      _ = ∑ _phi ∈ S₂, (((D.q * a : ℕ) : ℂ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro phi hphi
        have hslice : phi ∈ pTypeCoreDegreeSlice S₀ (D.q * a) := by
          rw [← rigid.current_eq_slice]
          exact hphi
        have hdegree : phi 1 = ((D.q * a : ℕ) : ℂ) :=
          (Finset.mem_filter.mp hslice).2
        let chi : IrreducibleCharacter M ℂ :=
          ⟨phi, rigid.slice_irreducible phi hphi⟩
        have hnorm : characterPairing phi phi = 1 :=
          IrreducibleCharacter.characterPairing_self chi
        rw [hdegree, hnorm, div_one]
      _ = _ := by simp
  have hsumS₄ :
      (∑ phi ∈ S₄, phi 1 ^ 2 / characterPairing phi phi) =
        (S₄.card : ℂ) * (((D.q * u₀ : ℕ) : ℂ) ^ 2) := by
    calc
      _ = ∑ _phi ∈ S₄, (((D.q * u₀ : ℕ) : ℂ) ^ 2) := by
        apply Finset.sum_congr rfl
        intro phi hphi
        have hphi₃ : phi ∈ S₃ := (Finset.mem_filter.mp hphi).1
        have hirr : IsIrreducibleCharacter M ℂ phi :=
          (Finset.mem_filter.mp hphi).2.2
        have hdegree : phi 1 = ((D.q * u₀ : ℕ) : ℂ) :=
          rigid.remainder_degree phi hphi₃
        let chi : IrreducibleCharacter M ℂ := ⟨phi, hirr⟩
        have hnorm : characterPairing phi phi = 1 :=
          IrreducibleCharacter.characterPairing_self chi
        rw [hdegree, hnorm, div_one]
      _ = _ := by simp
  have hsumMu :
      (∑ phi ∈ mu, phi 1 ^ 2 / characterPairing phi phi) =
        (mu.card : ℂ) * ((D.q * u₀ ^ 2 : ℕ) : ℂ) := by
    calc
      _ = ∑ _phi ∈ mu, ((D.q * u₀ ^ 2 : ℕ) : ℂ) := by
        apply Finset.sum_congr rfl
        intro phi hphi
        have hind :=
          (typeP_nonGalois_characters ctx not_Galois).reducible_layer_induced
            phi hphi
        have hdegree : phi 1 = ((D.q * u₀ : ℕ) : ℂ) := by
          simpa only [D, HU, H, H₀, u₀] using hind.1
        have hnorm : characterPairing phi phi = (D.q : ℂ) := by
          simpa only [mu, HU, H, H₀, D] using
            pTypeCore_reducibleLayer_norm_eq_q ctx facts hphi
        rw [hdegree, hnorm]
        norm_num only [Nat.cast_mul, Nat.cast_pow]
        field_simp [Nat.cast_ne_zero.mpr D.q_prime.ne_zero]
        <;> ring
      _ = _ := by simp

  have hHder : Fitting_core M ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.1
  have hUder : U ≤ derivedWithin M :=
    ctx.typeP.2.1.2.2.2.2.1
  have hDerM : derivedWithin M ≤ M :=
    Subgroup.map_subtype_le (_root_.commutator M)
  let Cₐ := Ptype_Fcompl_kernel ctx
  let H₀a := Ptype_Fcore_kernel ctx
  let K₀a : Subgroup G := H₀a ⊔ Cₐ
  let KCa : Subgroup G := Fitting_core M ⊔ Cₐ
  have hCder : Cₐ ≤ derivedWithin M :=
    (Ptype_Fcompl_kernel_le ctx).trans hUder
  have hH₀der : H₀a ≤ derivedWithin M :=
    (Ptype_Fcore_kernel_lt ctx).le.trans hHder
  have hH₀M : H₀a ≤ M := hH₀der.trans hDerM
  have hCM : Cₐ ≤ M := hCder.trans hDerM
  have hHM : Fitting_core M ≤ M := hHder.trans hDerM
  have hH₀HU : H₀a.subgroupOf M ≤ HU := by
    intro x hx
    exact hH₀der hx
  have hCHU : Cₐ.subgroupOf M ≤ HU := by
    intro x hx
    exact hCder hx
  have hHHU : (Fitting_core M).subgroupOf M ≤ HU := by
    intro x hx
    exact hHder hx
  have hK₀HU : K₀a.subgroupOf M ≤ HU := by
    change (H₀a ⊔ Cₐ).subgroupOf M ≤ HU
    rw [Subgroup.subgroupOf_sup hH₀M hCM]
    exact sup_le hH₀HU hCHU
  have hKCHU : KCa.subgroupOf M ≤ HU := by
    change (Fitting_core M ⊔ Cₐ).subgroupOf M ≤ HU
    rw [Subgroup.subgroupOf_sup hHM hCM]
    exact sup_le hHHU hCHU
  have hDC : D.C.map U.subtype = Cₐ := rfl
  have hH₀Ceq : H₀C = (K₀a.subgroupOf M).subgroupOf HU := by
    change (H₀a.subgroupOf M).subgroupOf HU ⊔
        (((D.C.map U.subtype).subgroupOf M).subgroupOf HU) =
      (K₀a.subgroupOf M).subgroupOf HU
    rw [hDC, ← Subgroup.subgroupOf_sup hH₀HU hCHU,
      ← Subgroup.subgroupOf_sup hH₀M hCM]
  have hHCeq : HC = (KCa.subgroupOf M).subgroupOf HU := by
    change ((Fitting_core M).subgroupOf M).subgroupOf HU ⊔
        (((D.C.map U.subtype).subgroupOf M).subgroupOf HU) =
      (KCa.subgroupOf M).subgroupOf HU
    rw [hDC, ← Subgroup.subgroupOf_sup hHHU hCHU,
      ← Subgroup.subgroupOf_sup hHM hCM]
  letI : HU.Normal :=
    Submission.OddOrder.BG.Section16.TypeSpecInternal.derivedWithin_normal16 M
  letI : H.Normal := pTypeCoreH_normal ctx
  letI : H₀.Normal := pTypeH0InDerived_normal ctx
  letI : H₀C.Normal := pTypeCoreH0C_normal ctx facts
  letI : (H₀C.map HU.subtype).Normal := by
    rw [hH₀Ceq, Subgroup.map_subgroupOf_eq_of_le hK₀HU]
    exact (Ptype_Fcore_extensions_normal ctx).H₀C_normal.2
  letI : (HC.map HU.subtype).Normal := by
    rw [hHCeq, Subgroup.map_subgroupOf_eq_of_le hKCHU]
    exact (Ptype_Fcore_extensions_normal ctx).HC_normal.2
  have hH₀CHC : H₀C ≤ HC := by
    change H₀ ⊔ C ≤ H ⊔ C
    exact sup_le_sup hH₀H le_rfl
  have hupper : H₀C ⊔ H = HC := by
    apply le_antisymm
    · apply sup_le
      · exact sup_le (hH₀H.trans le_sup_left) le_sup_right
      · exact le_sup_left
    · apply sup_le
      · exact le_sup_right
      · exact (show C ≤ H₀C from le_sup_right).trans le_sup_left
  have hseq : seqIndD (k := ℂ) HU HC H₀C = X := by
    calc
      seqIndD (k := ℂ) HU HC H₀C =
          seqIndD (k := ℂ) HU (H₀C ⊔ H) H₀C := by rw [hupper]
      _ = seqIndD (k := ℂ) HU H H₀C := seqIndDY HU H H₀C
      _ = X := rfl
  let UHU : Subgroup HU := pTypeUInDerived M (derivedWithin M) U
  have hcomp : H.IsComplement' UHU := pTypeCoreH_isComplement_U ctx
  have hCU : C ≤ UHU := by
    exact Subgroup.subgroupOf_mono HU
      (Subgroup.subgroupOf_mono M (Subgroup.map_subtype_le D.C))
  have hinter : H₀C ⊓ H = H₀ := by
    rw [inf_comm]
    exact (pTypeCore_inf_sup_eq_of_complement
      H UHU H₀ C hcomp hH₀H hCU).1
  have hsup : H ⊔ H₀C = HC := by rw [sup_comm, hupper]
  have hrel : H₀C.relIndex HC = D.p ^ D.q := by
    calc
      H₀C.relIndex HC = H₀C.relIndex (H ⊔ H₀C) := by rw [hsup]
      _ = H₀C.relIndex H := Subgroup.relIndex_sup_right H H₀C
      _ = (H₀C ⊓ H).relIndex H :=
        (Subgroup.inf_relIndex_right H₀C H).symm
      _ = H₀.relIndex H := by rw [hinter]
      _ = D.p ^ D.q := pTypeCore_H0_relIndex_H_eq_factorCard ctx facts
  have hsumGlobal :
      (∑ phi ∈ X, phi 1 ^ 2 / characterPairing phi phi) =
        (D.q : ℂ) * (u₀ : ℂ) *
          (((D.p ^ D.q : ℕ) : ℂ) - 1) := by
    have hsum := sum_seqIndD_square (k := ℂ) HU HC H₀C hH₀CHC
    rw [hseq, pTypeCore_index_eq_q ctx facts,
      pTypeCore_HC_index_eq_factorCard ctx facts, hrel] at hsum
    simpa only [D, u₀, mul_assoc] using hsum
  have hweighted :
      (S₂.card : ℂ) * (((D.q * a : ℕ) : ℂ) ^ 2) +
          (S₄.card : ℂ) * (((D.q * u₀ : ℕ) : ℂ) ^ 2) +
          (mu.card : ℂ) * ((D.q * u₀ ^ 2 : ℕ) : ℂ) =
        (D.q : ℂ) * (u₀ : ℂ) *
          (((D.p ^ D.q : ℕ) : ℂ) - 1) := by
    rw [← hsumS₂, ← hsumS₄, ← hsumMu]
    exact hsumPartition.symm.trans hsumGlobal
  have huIndex : u₀ = (_root_.commutator U).index := by
    calc
      u₀ = D.C.index := pTypeCore_actionFactorCard_eq_C_index D
      _ = (_root_.commutator U).index :=
        congrArg Subgroup.index rigid.action_kernel_eq_commutator
  have hdvd : a ^ 2 ∣ (D.p - 1) * u₀ := by
    have h := pTypeCore_indexSquare_dvd_primePred_mul_derivedIndex
      ctx facts not_Galois
    rwa [← huIndex] at h
  have hsliceMul : S₂.card * a ^ 2 = (D.p - 1) * u₀ := by
    rw [rigid.slice_card]
    exact Nat.div_mul_cancel hdvd
  have hsliceMulC :
      (S₂.card : ℂ) * (a : ℂ) ^ 2 =
        ((D.p - 1 : ℕ) : ℂ) * (u₀ : ℂ) := by
    exact_mod_cast hsliceMul
  have hsliceContribution :
      (S₂.card : ℂ) * (((D.q * a : ℕ) : ℂ) ^ 2) =
        (D.q : ℂ) ^ 2 *
          (((D.p - 1 : ℕ) : ℂ) * (u₀ : ℂ)) := by
    norm_num only [Nat.cast_mul]
    calc
      (S₂.card : ℂ) * ((D.q : ℂ) * (a : ℂ)) ^ 2 =
          (D.q : ℂ) ^ 2 *
            ((S₂.card : ℂ) * (a : ℂ) ^ 2) := by ring
      _ = _ := by rw [hsliceMulC]
  have hmuCard : mu.card = D.p - 1 := by
    simpa only [mu, HU, H, H₀, D] using
      (pType_nb_redM_H0 ctx facts).1
  have hfactored :
      (D.q : ℂ) * (u₀ : ℂ) *
          ((D.q : ℂ) * (u₀ : ℂ) * (S₄.card : ℂ) +
            ((D.p - 1 : ℕ) : ℂ) *
              ((D.q : ℂ) + (u₀ : ℂ))) =
        (D.q : ℂ) * (u₀ : ℂ) *
          (((D.p ^ D.q : ℕ) : ℂ) - 1) := by
    calc
      _ = (S₂.card : ℂ) * (((D.q * a : ℕ) : ℂ) ^ 2) +
          (S₄.card : ℂ) * (((D.q * u₀ : ℕ) : ℂ) ^ 2) +
          (mu.card : ℂ) * ((D.q * u₀ ^ 2 : ℕ) : ℂ) := by
        rw [hsliceContribution, hmuCard]
        norm_num only [Nat.cast_mul, Nat.cast_pow]
        ring
      _ = _ := hweighted
  have hquNe : (D.q : ℂ) * (u₀ : ℂ) ≠ 0 := by
    apply mul_ne_zero
    · exact Nat.cast_ne_zero.mpr D.q_prime.ne_zero
    · apply Nat.cast_ne_zero.mpr
      exact Nat.ne_of_gt (by
        dsimp [u₀, pTypeActionFactorCard]
        exact Nat.card_pos)
  have hinside := mul_left_cancel₀ hquNe hfactored
  have hpowOne : 1 ≤ D.p ^ D.q := one_le_pow₀ D.p_prime.one_lt.le
  have hcast :
      ((D.q * u₀ * S₄.card +
          (D.p - 1) * (D.q + u₀) : ℕ) : ℂ) =
        ((D.p ^ D.q - 1 : ℕ) : ℂ) := by
    calc
      _ = (D.q : ℂ) * (u₀ : ℂ) * (S₄.card : ℂ) +
          ((D.p - 1 : ℕ) : ℂ) *
            ((D.q : ℂ) + (u₀ : ℂ)) := by
        norm_num only [Nat.cast_add, Nat.cast_mul]
      _ = (((D.p ^ D.q : ℕ) : ℂ) - 1) := hinside
      _ = ((D.p ^ D.q - 1 : ℕ) : ℂ) := by
        rw [Nat.cast_sub hpowOne]
        norm_num
  exact_mod_cast hcast

/-! ## The strict remainder bound -/

/-- The elementary exponential inequality needed for (9.11.5). -/
private theorem rigid_power_bound
    (a q : ℕ) (ha : 0 < a) (hq : 3 ≤ q) :
    (q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1 <
      (2 * a + 1) ^ q := by
  induction q, hq using Nat.le_induction with
  | base =>
      norm_num
      nlinarith [pow_pos ha 2, pow_pos ha 3]
  | succ q hq ih =>
      have hbasePos : 0 < 2 * a + 1 := by omega
      have hscaled :
          ((q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1) *
              (2 * a + 1) <
            (2 * a + 1) ^ q * (2 * a + 1) :=
        (Nat.mul_lt_mul_right hbasePos).2 ih
      rw [pow_succ]
      apply lt_of_le_of_lt _ hscaled
      have haPow : a ^ 2 ≤ a ^ 3 := by
        rw [pow_succ]
        exact Nat.le_mul_of_pos_right (a ^ 2) ha
      have hcoef : 2 * q + 2 ≤ 2 * q ^ 2 := by
        nlinarith
      have hcore : a ^ 3 + (2 * q + 1) * a ^ 2 ≤
          2 * q ^ 2 * a ^ 3 := by
        calc
          a ^ 3 + (2 * q + 1) * a ^ 2 ≤
              a ^ 3 + (2 * q + 1) * a ^ 3 :=
            Nat.add_le_add_left
              (Nat.mul_le_mul_left (2 * q + 1) haPow) _
          _ = (2 * q + 2) * a ^ 3 := by ring
          _ ≤ (2 * q ^ 2) * a ^ 3 :=
            Nat.mul_le_mul_right (a ^ 3) hcoef
          _ = 2 * q ^ 2 * a ^ 3 := by ring
      have hpolyLower : q ^ 2 * a ^ 2 + 1 ≤
          (q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1 := by
        omega
      have hincrement :
          a ^ 3 + (2 * q + 1) * a ^ 2 + 2 * a ≤
            2 * a *
              ((q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1) := by
        calc
          a ^ 3 + (2 * q + 1) * a ^ 2 + 2 * a ≤
              2 * q ^ 2 * a ^ 3 + 2 * a :=
            Nat.add_le_add_right hcore (2 * a)
          _ = 2 * a * (q ^ 2 * a ^ 2 + 1) := by ring
          _ ≤ 2 * a *
              ((q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1) :=
            Nat.mul_le_mul_left (2 * a) hpolyLower
      calc
        (q + 1 + 2) * a ^ 3 + (q + 1) ^ 2 * a ^ 2 +
              2 * (q + 1) * a + 1 =
            ((q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1) +
              (a ^ 3 + (2 * q + 1) * a ^ 2 + 2 * a) := by ring
        _ ≤ ((q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1) +
              2 * a *
                ((q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1) :=
          Nat.add_le_add_left hincrement _
        _ = ((q + 2) * a ^ 3 + q ^ 2 * a ^ 2 + 2 * q * a + 1) *
              (2 * a + 1) := by ring

/-- Peterfalvi (9.11.5).  In the rigid branch, the number of irreducible
characters left outside the current slice is strictly larger than the norm
of the auxiliary virtual character `alpha`; in particular the remainder is
nonempty. -/
theorem pTypeCore_nonGalois_rigid_remainder_gt_alphaNorm
    {G : Type u} [Group G] [Fintype G] [IsMinSimpleOddGroup G]
    {M U W W₁ W₂ : Subgroup G}
    (ctx : PTypeFCoreContext M U W W₁ W₂)
    (facts : PTypeFCoreFactorFacts ctx)
    (not_Galois : ¬ typeP_Galois (Ptype_factor_action ctx facts))
    (S₂ : Finset (ClassFunction M ℂ))
    (rigid : PTypeCoreRigidFacts ctx facts not_Galois S₂) :
    let D := Ptype_factor_action ctx facts
    let hD := Ptype_factor_action_hypotheses ctx facts
    let a := pTypeNonGaloisIndex hD not_Galois
    let u₀ := pTypeActionFactorCard D
    let HU := pTypeCoreDerived M
    let H := pTypeCoreFitting M
    let H₀C := pTypeH0CInDerived M (derivedWithin M)
      (Ptype_Fcore_kernel ctx) U W₁ D
    let S₃ := pTypeCoreRemainder
      (pTypeCoreFamilyOfContext ctx) S₂
    let S₄ := pTypeCoreIrreducibleRemainder HU H H₀C S₃
    (S₄.card : ℝ) > pTypeCoreAlphaNorm D.q u₀ a ∧ 0 < S₄.card := by
  classical
  let D := Ptype_factor_action ctx facts
  let hD := Ptype_factor_action_hypotheses ctx facts
  let a := pTypeNonGaloisIndex hD not_Galois
  let u₀ := pTypeActionFactorCard D
  let HU := pTypeCoreDerived M
  let H := pTypeCoreFitting M
  let H₀C := pTypeH0CInDerived M (derivedWithin M)
    (Ptype_Fcore_kernel ctx) U W₁ D
  let S₃ := pTypeCoreRemainder
    (pTypeCoreFamilyOfContext ctx) S₂
  let S₄ := pTypeCoreIrreducibleRemainder HU H H₀C S₃
  change (S₄.card : ℝ) > pTypeCoreAlphaNorm D.q u₀ a ∧
    0 < S₄.card
  have hcount :
      D.q * u₀ * S₄.card + (D.p - 1) * (D.q + u₀) =
        D.p ^ D.q - 1 := by
    simpa only [D, u₀, HU, H, H₀C, S₃, S₄] using
      rigid_remainder_count ctx facts not_Galois S₂ rigid
  have haPos : 0 < a :=
    Nat.zero_lt_of_lt (one_lt_pTypeNonGaloisIndex hD not_Galois)
  have huPos : 0 < u₀ := by
    dsimp [u₀, pTypeActionFactorCard]
    exact Nat.card_pos
  have huLe : u₀ ≤ a ^ 2 := by
    simpa only [D, hD, a, u₀] using
      PTypeCoreActionKernelInternal.PTypeCoreRigidFacts.factorCard_le_index_sq
        rigid
  have hpPred : 2 * a = D.p - 1 :=
    (pTypeCore_twice_index_le_prime_pred
      ctx facts not_Galois).2.mpr rigid.index_eq_half_prime_pred
  have hpEq : D.p = 2 * a + 1 := by
    have hpPos : 0 < D.p := D.p_prime.pos
    omega
  have hqOdd : Odd D.q := by
    rw [← D.card_W₁]
    exact odd_natCard_subgroup W₁ IsMinSimpleOddGroup.odd_card
  have hqThree : 3 ≤ D.q :=
    (Nat.Prime.odd_iff D.q_prime).mp hqOdd
  have hpowerRaw := rigid_power_bound a D.q haPos hqThree
  have hpower :
      (D.q + 2) * a ^ 3 + D.q ^ 2 * a ^ 2 + 2 * D.q * a <
        D.p ^ D.q - 1 := by
    rw [hpEq]
    omega
  have hmulA :
      (D.q + 2) * a * u₀ ≤ (D.q + 2) * a * a ^ 2 :=
    Nat.mul_le_mul_left ((D.q + 2) * a) huLe
  have hmulQ : D.q * u₀ ≤ D.q * a ^ 2 :=
    Nat.mul_le_mul_left D.q huLe
  have hqSub : D.q - 1 + 1 = D.q :=
    Nat.sub_add_cancel D.q_prime.one_le
  have hactualLe :
      (D.p - 1) * (D.q + u₀) +
          (D.q * u₀ * (a + 1) +
            D.q * (D.q - 1) * a ^ 2) ≤
        (D.q + 2) * a ^ 3 + D.q ^ 2 * a ^ 2 +
          2 * D.q * a := by
    calc
      _ = 2 * D.q * a + (D.q + 2) * a * u₀ +
          D.q * u₀ + D.q * (D.q - 1) * a ^ 2 := by
        rw [← hpPred]
        ring
      _ ≤ 2 * D.q * a + (D.q + 2) * a * a ^ 2 +
          D.q * a ^ 2 + D.q * (D.q - 1) * a ^ 2 := by
        exact add_le_add
          (add_le_add (add_le_add le_rfl hmulA) hmulQ) le_rfl
      _ = 2 * D.q * a + (D.q + 2) * a ^ 3 +
          D.q * (D.q - 1 + 1) * a ^ 2 := by ring
      _ = _ := by rw [hqSub]; ring
  have hactualLt :
      (D.p - 1) * (D.q + u₀) +
          (D.q * u₀ * (a + 1) +
            D.q * (D.q - 1) * a ^ 2) <
        D.p ^ D.q - 1 :=
    hactualLe.trans_lt hpower
  have hscaledNat :
      D.q * u₀ * (a + 1) + D.q * (D.q - 1) * a ^ 2 <
        D.q * u₀ * S₄.card := by
    rw [← hcount] at hactualLt
    omega
  have hqPosR : 0 < (D.q : ℝ) := by
    exact_mod_cast D.q_prime.pos
  have huPosR : 0 < (u₀ : ℝ) := by
    exact_mod_cast huPos
  have hquPos : 0 < (D.q : ℝ) * (u₀ : ℝ) :=
    mul_pos hqPosR huPosR
  have huNeR : (u₀ : ℝ) ≠ 0 := ne_of_gt huPosR
  have hleft :
      (D.q : ℝ) * (u₀ : ℝ) *
          pTypeCoreAlphaNorm D.q u₀ a =
        ((D.q * u₀ * (a + 1) +
          D.q * (D.q - 1) * a ^ 2 : ℕ) : ℝ) := by
    rw [pTypeCoreAlphaNorm]
    norm_num only [Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
      Nat.cast_one, Nat.cast_sub D.q_prime.one_le]
    field_simp [huNeR]
    <;> ring
  have hmulAlpha :
      (D.q : ℝ) * (u₀ : ℝ) *
          pTypeCoreAlphaNorm D.q u₀ a <
        (D.q : ℝ) * (u₀ : ℝ) * (S₄.card : ℝ) := by
    calc
      _ = ((D.q * u₀ * (a + 1) +
          D.q * (D.q - 1) * a ^ 2 : ℕ) : ℝ) := hleft
      _ < ((D.q * u₀ * S₄.card : ℕ) : ℝ) := by
        exact_mod_cast hscaledNat
      _ = _ := by norm_num only [Nat.cast_mul]
  have hsAlpha : pTypeCoreAlphaNorm D.q u₀ a < (S₄.card : ℝ) :=
    lt_of_mul_lt_mul_left hmulAlpha hquPos.le
  have hnormNonneg : 0 ≤ pTypeCoreAlphaNorm D.q u₀ a := by
    unfold pTypeCoreAlphaNorm
    positivity
  have hsCardReal : 0 < (S₄.card : ℝ) :=
    hnormNonneg.trans_lt hsAlpha
  have hsCard : 0 < S₄.card := by exact_mod_cast hsCardReal
  exact ⟨hsAlpha, hsCard⟩

end PTypeCoreNonGaloisDichotomyInternal

end

end Submission.OddOrder.PF
