import Mathlib.NumberTheory.Niven
import Submission.OddOrder.BG.AppendixC.NormEquationCharacterBranch
import Submission.OddOrder.MathlibSupport.AlgebraicIntegerCongruence
import Submission.OddOrder.MathlibSupport.FreeOrbitCardinality
import Submission.OddOrder.MathlibSupport.NormalizedTI
import Submission.OddOrder.MathlibSupport.PElementCyclic
import Submission.OddOrder.PF.Section01.OddConjugateIrreducible
import Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset
import Submission.OddOrder.PF.Section06.OddFrobeniusQuotient

/-!
# A constant irreducible character on a central TI section

This file ports Peterfalvi's lemma immediately preceding Theorem (6.8),
Coq `PFsection6.v`, lines 391--565.  The source proves the congruence by
expanding products in the class algebra.  Here the same counting argument is
organized directly on pairs of conjugates.  Simultaneous conjugation by the
Sylow subgroup is free on the pairs whose product lies outside the conjugacy
saturation of `Z \ {1}`.  Traces of products of conjugacy-class sums compare
the remaining terms.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

open CategoryTheory
open Submission.OddOrder.BG.AppendixC
open Submission.OddOrder.MathlibSupport

universe u v

private def classPairSource
    {G : Type u} [Group G] (a b : G) (q : G × G) : Prop :=
  IsConj q.1 a ∧ IsConj q.2 b

private def meetsNonidentityClass
    {G : Type u} [Group G] (Z : Subgroup G) (g : G) : Prop :=
  ∃ z : G, z ∈ Z ∧ z ≠ 1 ∧ IsConj g z

private def classPairOne
    {G : Type u} [Group G] (a b : G) (q : G × G) : Prop :=
  classPairSource a b q ∧ q.1 * q.2 = 1

private def classPairRelevant
    {G : Type u} [Group G] (Z : Subgroup G) (a b : G)
    (q : G × G) : Prop :=
  classPairSource a b q ∧ q.1 * q.2 ≠ 1 ∧
    meetsNonidentityClass Z (q.1 * q.2)

private def classPairBad
    {G : Type u} [Group G] (Z : Subgroup G) (a b : G)
    (q : G × G) : Prop :=
  classPairSource a b q ∧ q.1 * q.2 ≠ 1 ∧
    ¬ meetsNonidentityClass Z (q.1 * q.2)

private def classPairOneCount
    {G : Type u} [Group G] [Fintype G] (a b : G) : ℕ :=
  (Finset.univ.filter (classPairOne a b)).card

private def classPairRelevantCount
    {G : Type u} [Group G] [Fintype G]
    (Z : Subgroup G) (a b : G) : ℕ :=
  (Finset.univ.filter (classPairRelevant Z a b)).card

private def classPairBadSum
    {G : Type u} [Group G] [Fintype G]
    (Z : Subgroup G) (a b : G) (f : G → ℂ) : ℂ :=
  ∑ q ∈ Finset.univ.filter (classPairBad Z a b), f (q.1 * q.2)

private def classPairCharacterSum
    {G : Type u} [Group G] [Fintype G]
    (chi : IrreducibleCharacter G ℂ) (a b : G) : ℂ :=
  ∑ q : G × G,
    if classPairSource a b q then chi (q.1 * q.2) else 0

private theorem conjugacyClassCard_inv
    {G : Type u} [Group G] [Fintype G] (x : G) :
    conjugacyClassCard x⁻¹ = conjugacyClassCard x := by
  classical
  rw [conjugacyClassCard, ← Fintype.card_subtype]
  rw [conjugacyClassCard, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact
    { toFun := fun y ↦ ⟨y.1⁻¹, by
        obtain ⟨g, hg⟩ := isConj_iff.mp y.2
        apply isConj_iff.mpr
        refine ⟨g, ?_⟩
        calc
          g * y.1⁻¹ * g⁻¹ = (g * y.1 * g⁻¹)⁻¹ := conj_inv.symm
          _ = x := by simpa using congrArg Inv.inv hg⟩
      invFun := fun y ↦ ⟨y.1⁻¹, by
        obtain ⟨g, hg⟩ := isConj_iff.mp y.2
        apply isConj_iff.mpr
        refine ⟨g, ?_⟩
        calc
          g * y.1⁻¹ * g⁻¹ = (g * y.1 * g⁻¹)⁻¹ := conj_inv.symm
          _ = x⁻¹ := congrArg Inv.inv hg⟩
      left_inv := fun y ↦ by ext; simp
      right_inv := fun y ↦ by ext; simp }

private theorem classPairCharacterSum_eq_formula
    {G : Type u} [Group G] [Fintype G]
    (chi : IrreducibleCharacter G ℂ) (a b : G) :
    classPairCharacterSum chi a b =
      (conjugacyClassCard a : ℂ) * (conjugacyClassCard b : ℂ) *
        chi a * chi b / chi 1 := by
  classical
  let V := chi.representation
  let rho : Representation ℂ G V := V.ρ
  letI : Simple V := chi.representation_simple
  letI : Representation.IsIrreducible rho :=
    representation_isIrreducible_of_simple_fdRep V
  have hrho (g : G) : rho.character g = chi g := by
    change _root_.Representation.character chi.representation.ρ g = chi g
    exact chi.representation_character g
  calc
    classPairCharacterSum chi a b =
        ∑ x : G, ∑ y : G,
          if IsConj x a ∧ IsConj y b then chi (x * y) else 0 := by
      rw [classPairCharacterSum, Fintype.sum_prod_type]
      simp only [classPairSource]
    _ = LinearMap.trace ℂ V
          (conjugacyClassEnd rho a * conjugacyClassEnd rho b) := by
      simpa only [hrho] using
        (sum_character_classProduct_eq_trace (V := V) rho a b)
    _ = (conjugacyClassCard a : ℂ) * (conjugacyClassCard b : ℂ) *
          chi a * chi b / chi 1 := by
      rw [trace_conjugacyClassEnd_mul (V := V) rho a b,
        hrho a, hrho b, IrreducibleCharacter.apply_one_eq_finrank]

private theorem classPairCharacterSum_self_eq_inv
    {G : Type u} [Group G] [Fintype G]
    (chi : IrreducibleCharacter G ℂ) (z : G)
    (hchi : chi z⁻¹ = chi z) :
    classPairCharacterSum chi z z =
      classPairCharacterSum chi z z⁻¹ := by
  rw [classPairCharacterSum_eq_formula,
    classPairCharacterSum_eq_formula, conjugacyClassCard_inv, hchi]

private theorem classPairOneCount_self_eq_zero
    {G : Type u} [Group G] [Fintype G]
    {z : G} (hnot : ¬ IsConj z⁻¹ z) :
    classPairOneCount z z = 0 := by
  classical
  rw [classPairOneCount, Finset.card_eq_zero,
    Finset.filter_eq_empty_iff]
  intro q _ hq
  rcases hq with ⟨⟨hqu, hqv⟩, huv⟩
  have hv : q.2 = q.1⁻¹ := by
    exact eq_inv_of_mul_eq_one_right huv
  have hquInv : IsConj q.1⁻¹ z⁻¹ := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hqu
    apply isConj_iff.mpr
    refine ⟨g, ?_⟩
    calc
      g * q.1⁻¹ * g⁻¹ = (g * q.1 * g⁻¹)⁻¹ := conj_inv.symm
      _ = z⁻¹ := congrArg Inv.inv hg
  exact hnot (hquInv.symm.trans (hv ▸ hqv))

private theorem classPairOneCount_inv_eq_classCard
    {G : Type u} [Group G] [Fintype G] (z : G) :
    classPairOneCount z z⁻¹ = conjugacyClassCard z := by
  classical
  rw [classPairOneCount, ← Fintype.card_subtype]
  rw [conjugacyClassCard, ← Fintype.card_subtype]
  apply Fintype.card_congr
  exact
    { toFun := fun q ↦ ⟨q.1.1, q.2.1.1⟩
      invFun := fun x ↦ ⟨(x.1, x.1⁻¹), by
        refine ⟨⟨x.2, ?_⟩, mul_inv_cancel x.1⟩
        obtain ⟨g, hg⟩ := isConj_iff.mp x.2
        apply isConj_iff.mpr
        refine ⟨g, ?_⟩
        calc
          g * x.1⁻¹ * g⁻¹ = (g * x.1 * g⁻¹)⁻¹ := conj_inv.symm
          _ = z⁻¹ := congrArg Inv.inv hg⟩
      left_inv := fun q ↦ by
        apply Subtype.ext
        apply Prod.ext
        · rfl
        · exact (eq_inv_of_mul_eq_one_right q.2.2).symm
      right_inv := fun x ↦ by ext; rfl }

private theorem classPairCharacterSum_split
    {G : Type u} [Group G] [Fintype G]
    (Z : Subgroup G) (chi : IrreducibleCharacter G ℂ)
    (a b z : G)
    (hrel : ∀ g : G, meetsNonidentityClass Z g → chi g = chi z) :
    classPairCharacterSum chi a b =
      (classPairOneCount a b : ℂ) * chi 1 +
        (classPairRelevantCount Z a b : ℂ) * chi z +
          classPairBadSum Z a b chi := by
  classical
  have hpoint (q : G × G) :
      (if classPairSource a b q then chi (q.1 * q.2) else 0) =
        (if classPairOne a b q then chi 1 else 0) +
          (if classPairRelevant Z a b q then chi z else 0) +
            (if classPairBad Z a b q then chi (q.1 * q.2) else 0) := by
    by_cases hs : classPairSource a b q
    · by_cases hone : q.1 * q.2 = 1
      · have hnrel : ¬ meetsNonidentityClass Z (q.1 * q.2) := by
          rw [hone]
          rintro ⟨w, _hwZ, hw, hwc⟩
          exact hw (isConj_one_right.mp hwc)
        simp [classPairOne, classPairRelevant, classPairBad,
          hs, hone, hnrel]
      · by_cases hr : meetsNonidentityClass Z (q.1 * q.2)
        · have hv := hrel (q.1 * q.2) hr
          simp [classPairOne, classPairRelevant, classPairBad,
            hs, hone, hr, hv]
        · simp [classPairOne, classPairRelevant, classPairBad,
            hs, hone, hr]
    · simp [classPairOne, classPairRelevant, classPairBad, hs]
  have honeSum :
      (∑ q : G × G,
          if classPairOne a b q then chi 1 else 0) =
        (classPairOneCount a b : ℂ) * chi 1 := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  have hrelSum :
      (∑ q : G × G,
          if classPairRelevant Z a b q then chi z else 0) =
        (classPairRelevantCount Z a b : ℂ) * chi z := by
    rw [← Finset.sum_filter]
    rw [Finset.sum_const, nsmul_eq_mul]
    rfl
  have hbadSum :
      (∑ q : G × G,
          if classPairBad Z a b q then chi (q.1 * q.2) else 0) =
        classPairBadSum Z a b chi := by
    rw [← Finset.sum_filter]
    rfl
  rw [classPairCharacterSum]
  calc
    (∑ q : G × G,
        if classPairSource a b q then chi (q.1 * q.2) else 0) =
        ∑ q : G × G,
          ((if classPairOne a b q then chi 1 else 0) +
            (if classPairRelevant Z a b q then chi z else 0) +
              (if classPairBad Z a b q then chi (q.1 * q.2) else 0)) := by
      apply Finset.sum_congr rfl
      intro q _
      exact hpoint q
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
        honeSum, hrelSum, hbadSum]

private theorem sum_mod_card_of_free_subMulAction
    {A : Type u} {X : Type v}
    [Group A] [Fintype A] [Fintype X] [MulAction A X]
    (S : SubMulAction A X) (f : X → ℂ)
    (hf : ∀ x : S, IsIntegral ℤ (f x.1))
    (hinv : ∀ (a : A) (x : S), f (a • x.1) = f x.1)
    (hfree : ∀ (a : A) (x : S), a • x = x → a = 1) :
    IsIntegralModEq (Nat.card A : ℂ) (∑ x : S, f x.1) 0 := by
  classical
  let Q := MulAction.orbitRel.Quotient A S
  letI : Fintype Q := Fintype.ofFinite Q
  have hstab (x : S) : MulAction.stabilizer A x = ⊥ :=
    stabilizer_eq_bot_of_smul_eq_imp_eq_one x (fun a ha ↦ hfree a x ha)
  have horbit (q : Q) :
      (∑ x : MulAction.orbitRel.Quotient.orbit q, f x.1.1) =
        (Nat.card A : ℂ) * f q.out.1 := by
    have hvalue (x : MulAction.orbitRel.Quotient.orbit q) :
        f x.1.1 = f q.out.1 := by
      have hx : x.1 ∈ MulAction.orbit A q.out := by
        rw [← MulAction.orbitRel.Quotient.orbit_eq_orbit_out q
          Quotient.out_eq']
        exact x.2
      obtain ⟨a, ha⟩ := hx
      rw [← ha]
      exact hinv a q.out
    have hcard : Nat.card (MulAction.orbitRel.Quotient.orbit q) = Nat.card A := by
      rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out q
        Quotient.out_eq']
      exact natCard_orbit_eq_natCard_of_stabilizer_eq_bot q.out
        (hstab q.out)
    calc
      (∑ x : MulAction.orbitRel.Quotient.orbit q, f x.1.1) =
          ∑ _x : MulAction.orbitRel.Quotient.orbit q, f q.out.1 := by
        apply Finset.sum_congr rfl
        intro x _
        exact hvalue x
      _ = (Nat.card (MulAction.orbitRel.Quotient.orbit q) : ℂ) * f q.out.1 := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
          Fintype.card_eq_nat_card]
      _ = (Nat.card A : ℂ) * f q.out.1 := by rw [hcard]
  have hdecomp :
      (∑ x : S, f x.1) =
        ∑ q : Q, ∑ x : MulAction.orbitRel.Quotient.orbit q, f x.1.1 := by
    calc
      (∑ x : S, f x.1) =
          ∑ y : Σ q : Q, MulAction.orbitRel.Quotient.orbit q, f y.2.1 := by
        apply Fintype.sum_equiv (MulAction.selfEquivSigmaOrbits' A S)
        intro x
        rfl
      _ = ∑ q : Q, ∑ x : MulAction.orbitRel.Quotient.orbit q, f x.1.1 := by
        rw [Fintype.sum_sigma]
  rw [hdecomp]
  simp_rw [horbit]
  rw [← Finset.mul_sum]
  refine ⟨∑ q : Q, f q.out.1, ?_, by simp⟩
  exact IsIntegral.sum _ (fun q _ ↦ hf q.out)

private theorem classPairBadSum_mod_card
    {G : Type u} [Group G] [Fintype G]
    (P : Subgroup G) (Z : Subgroup G) (a b : G) (f : G → ℂ)
    (haZ : a ∈ Z) (ha : a ≠ 1)
    (hbZ : b ∈ Z) (hb : b ≠ 1)
    (hf : ∀ g : G, IsIntegral ℤ (f g))
    (hclass : ∀ (t : P) (g : G),
      f ((t : G) * g * (t : G)⁻¹) = f g)
    (hfixed : ∀ (t : P), t ≠ 1 → ∀ g : G,
      (t : G) * g * (t : G)⁻¹ = g →
      meetsNonidentityClass Z g → g ∈ Z) :
    IsIntegralModEq (Nat.card P : ℂ) (classPairBadSum Z a b f) 0 := by
  classical
  let conjugationAction := subgroupConjugationActionOnAmbient P
  letI : SMul P G := conjugationAction.toSMul
  letI : MulAction P G := conjugationAction.toMulAction
  have hsmul (t : P) (g : G) :
      t • g = (t : G) * g * (t : G)⁻¹ := rfl
  have hsmul_mul (t : P) (x y : G) :
      t • (x * y) = (t • x) * (t • y) := by
    simp only [hsmul]
    group
  let productAction : MulAction P (G × G) := Prod.mulAction
  letI : SMul P (G × G) := productAction.toSMul
  letI : MulAction P (G × G) := productAction
  have hprod_fst (t : P) (q : G × G) : (t • q).1 = t • q.1 := by
    rfl
  have hprod_snd (t : P) (q : G × G) : (t • q).2 = t • q.2 := by
    rfl
  let bad : SubMulAction P (G × G) :=
    { carrier := {q | classPairBad Z a b q}
      smul_mem' := fun t q hq ↦ by
        rcases hq with ⟨⟨hqa, hqb⟩, hqne, hqout⟩
        have hq1 : IsConj q.1 (t • q.1) := by
          apply isConj_iff.mpr
          exact ⟨(t : G), (hsmul t q.1).symm⟩
        have hq2 : IsConj q.2 (t • q.2) := by
          apply isConj_iff.mpr
          exact ⟨(t : G), (hsmul t q.2).symm⟩
        refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
        · simpa only [hprod_fst] using hq1.symm.trans hqa
        · simpa only [hprod_snd] using hq2.symm.trans hqb
        · intro hone
          have hone' : t • (q.1 * q.2) = 1 := by
            rw [hsmul_mul]
            simpa only [hprod_fst, hprod_snd] using hone
          have := congrArg (fun g : G ↦ t⁻¹ • g) hone'
          apply hqne
          simpa using this
        · rintro ⟨z, hzZ, hz, hconj⟩
          apply hqout
          refine ⟨z, hzZ, hz, ?_⟩
          have hp : IsConj (q.1 * q.2) (t • (q.1 * q.2)) := by
            apply isConj_iff.mpr
            exact ⟨(t : G), (hsmul t (q.1 * q.2)).symm⟩
          exact hp.trans (by
            rw [hsmul_mul]
            simpa only [hprod_fst, hprod_snd] using hconj) }
  have hfree (t : P) (q : bad) (htq : t • q = q) : t = 1 := by
    by_contra ht
    have hpair : t • q.1 = q.1 := congrArg Subtype.val htq
    have hq1 : t • q.1.1 = q.1.1 := by
      simpa only [hprod_fst] using congrArg Prod.fst hpair
    have hq2 : t • q.1.2 = q.1.2 := by
      simpa only [hprod_snd] using congrArg Prod.snd hpair
    have huZ : q.1.1 ∈ Z :=
      hfixed t ht q.1.1 (by simpa only [hsmul] using hq1)
        ⟨a, haZ, ha, q.2.1.1⟩
    have hvZ : q.1.2 ∈ Z :=
      hfixed t ht q.1.2 (by simpa only [hsmul] using hq2)
        ⟨b, hbZ, hb, q.2.1.2⟩
    apply q.2.2.2
    exact ⟨q.1.1 * q.1.2, Z.mul_mem huZ hvZ, q.2.2.1,
      IsConj.refl _⟩
  have hsum := sum_mod_card_of_free_subMulAction
    (A := P) (X := G × G) bad
    (fun q : G × G ↦ f (q.1 * q.2))
    (fun q ↦ hf (q.1.1 * q.1.2))
    (fun t q ↦ by
      have hcomponent :
          f ((t • q.1.1) * (t • q.1.2)) = f (q.1.1 * q.1.2) := by
        rw [← hsmul_mul]
        simpa only [hsmul] using hclass t (q.1.1 * q.1.2)
      simpa only [hprod_fst, hprod_snd] using hcomponent)
    hfree
  have hbadEq :
      (∑ q : bad, f (q.1.1 * q.1.2)) = classPairBadSum Z a b f := by
    change (∑ q : {q : G × G // classPairBad Z a b q},
      f (q.1.1 * q.1.2)) = _
    rw [classPairBadSum]
    simpa using
      (Finset.sum_subtype_eq_sum_filter
        (p := classPairBad Z a b)
        (s := (Finset.univ : Finset (G × G)))
        (fun q : G × G ↦ f (q.1 * q.2)))
  rwa [hbadEq] at hsum

private theorem classPairReduction
    {G : Type u} [Group G] [Fintype G]
    (P : Subgroup G) (Z : Subgroup G)
    (chi : IrreducibleCharacter G ℂ) (a b z : G)
    (haZ : a ∈ Z) (ha : a ≠ 1)
    (hbZ : b ∈ Z) (hb : b ≠ 1)
    (hrel : ∀ g : G, meetsNonidentityClass Z g → chi g = chi z)
    (hfixed : ∀ (t : P), t ≠ 1 → ∀ g : G,
      (t : G) * g * (t : G)⁻¹ = g →
      meetsNonidentityClass Z g → g ∈ Z) :
    IsIntegralModEq (Nat.card P : ℂ)
      (classPairCharacterSum chi a b)
      ((classPairOneCount a b : ℂ) * chi 1 +
        (classPairRelevantCount Z a b : ℂ) * chi z) := by
  have hsplit := classPairCharacterSum_split Z chi a b z hrel
  have hbad :
      IsIntegralModEq (Nat.card P : ℂ)
        (classPairBadSum Z a b chi) 0 := by
    apply classPairBadSum_mod_card P Z a b chi haZ ha hbZ hb
    · intro g
      rw [← chi.representation_character]
      exact representation_character_isIntegral chi.representation.ρ g
    · intro t g
      rw [← chi.representation_character,
        ← chi.representation_character]
      exact chi.representation.char_conj g (t : G)
    · exact hfixed
  let base : ℂ :=
    (classPairOneCount a b : ℂ) * chi 1 +
      (classPairRelevantCount Z a b : ℂ) * chi z
  have hadd : IsIntegralModEq (Nat.card P : ℂ)
      (base + classPairBadSum Z a b chi) base := by
    simpa only [add_zero] using IsIntegralModEq.add_left base hbad
  exact (IsIntegralModEq.of_eq hsplit).trans hadd

private theorem normalizedTI_sylow_le
    {G : Type u} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L : Subgroup G)
    (hTI : IsNormalizedTI
      (subgroupNonidentity (P : Subgroup G)) ⊤ L) :
    (P : Subgroup G) ≤ L := by
  obtain ⟨a, ha⟩ := (isNormalizedTI_iff_mem_conj.mp hTI).1
  intro x hxP
  apply ((isNormalizedTI_iff_mem_conj.mp hTI).2.2 ha trivial).mp
  refine ⟨P.mul_mem (P.mul_mem (P.inv_mem hxP) ha.1) hxP, ?_⟩
  intro hconj
  apply ha.2
  have := congrArg (fun y : G ↦ x * y * x⁻¹) hconj
  simpa [mul_assoc] using this

private theorem normalizedTI_le_normalizer_sylow
    {G : Type u} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L : Subgroup G)
    (hTI : IsNormalizedTI
      (subgroupNonidentity (P : Subgroup G)) ⊤ L) :
    L ≤ Subgroup.normalizer (P : Set G) := by
  intro x hxL
  apply Subgroup.mem_set_normalizer_iff.mpr
  intro y
  constructor
  · intro hyP
    by_cases hy : y = 1
    · subst y
      simp
    · have hxN : x ∈ Subgroup.normalizer
          (subgroupNonidentity (P : Subgroup G)) := (hTI.2.1 hxL).2
      exact ((Subgroup.mem_set_normalizer_iff.mp hxN y).mp ⟨hyP, hy⟩).1
  · intro hxyP
    have hxiL : x⁻¹ ∈ L := L.inv_mem hxL
    by_cases hxy : x * y * x⁻¹ = 1
    · have := congrArg (fun w : G ↦ x⁻¹ * w * x) hxy
      have hy : y = 1 := by simpa [mul_assoc] using this
      simp [hy]
    · have hxiN : x⁻¹ ∈ Subgroup.normalizer
          (subgroupNonidentity (P : Subgroup G)) := (hTI.2.1 hxiL).2
      have hback := (Subgroup.mem_set_normalizer_iff.mp hxiN
        (x * y * x⁻¹)).mp ⟨hxyP, hxy⟩
      simpa [mul_assoc] using hback.1

private theorem fixed_conjugate_mem_normal_subgroup
    {G : Type u} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (hTI : IsNormalizedTI
      (subgroupNonidentity (P : Subgroup G)) ⊤ L)
    (hPL : (P : Subgroup G) ≤ L)
    (hPnormal : (P.subgroupOf L).Normal)
    (hZL : Z ≤ L) (hZnormal : (Z.subgroupOf L).Normal)
    (hZP : Z ≤ centerWithin (P : Subgroup G))
    (t : P) (ht : t ≠ 1) (y : G)
    (hty : (t : G) * y * (t : G)⁻¹ = y)
    (hyclass : meetsNonidentityClass Z y) :
    y ∈ Z := by
  have htG : (t : G) ≠ 1 := fun h ↦ ht (Subtype.ext h)
  have htPnon : (t : G) ∈ subgroupNonidentity (P : Subgroup G) :=
    ⟨t.2, htG⟩
  have hcomm : (t : G) * y = y * (t : G) :=
    (mul_inv_eq_iff_eq_mul.mp hty)
  have hyL : y ∈ L := by
    apply ((isNormalizedTI_iff_mem_conj.mp hTI).2.2 htPnon trivial).mp
    have : y⁻¹ * (t : G) * y = (t : G) := by
      calc
        y⁻¹ * (t : G) * y = y⁻¹ * ((t : G) * y) := by rw [mul_assoc]
        _ = y⁻¹ * (y * (t : G)) := by rw [hcomm]
        _ = t := by simp
    rw [this]
    exact htPnon
  obtain ⟨a, haZ, ha, hya⟩ := hyclass
  have haP : a ∈ (P : Subgroup G) := (hZP haZ).1
  have haPelt : IsPElement p a := by
    obtain ⟨n, hn⟩ := P.isPGroup' ⟨a, haP⟩
    refine ⟨n, ?_⟩
    exact congrArg Subtype.val hn
  have hyPelt : IsPElement p y := by
    obtain ⟨g, hg⟩ := isConj_iff.mp hya
    have hback : g⁻¹ * a * g = y := by
      calc
        g⁻¹ * a * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [hg]
        _ = y := by simp [mul_assoc]
    rw [← hback]
    simpa only [inv_inv] using haPelt.conj g⁻¹
  let PL : Sylow p L := P.subtype hPL
  let yL : L := ⟨y, hyL⟩
  have hyPeltL : IsPElement p yL :=
    IsPElement.of_map_of_injective L.subtype Subtype.coe_injective (by
      change IsPElement p y
      exact hyPelt)
  letI : (PL : Subgroup L).Normal := by
    change (P.subgroupOf L).Normal
    exact hPnormal
  have hYp : IsPGroup p (Subgroup.zpowers yL) := hyPeltL.zpowers_isPGroup
  have hsup := IsPGroup.to_sup_of_normal_left
      (H := (PL : Subgroup L)) (K := (Subgroup.zpowers yL : Subgroup L))
      PL.isPGroup' hYp
  have hsupEq := PL.is_maximal' hsup le_sup_left
  have hyPL : yL ∈ (PL : Subgroup L) := by
    rw [← hsupEq]
    exact
      (show (Subgroup.zpowers yL : Subgroup L) ≤ _ from le_sup_right)
        (Subgroup.mem_zpowers yL)
  have hyP : y ∈ (P : Subgroup G) := hyPL
  obtain ⟨g, hg⟩ := isConj_iff.mp hya
  have hback : g⁻¹ * a * g = y := by
    calc
      g⁻¹ * a * g = g⁻¹ * (g * y * g⁻¹) * g := by rw [hg]
      _ = y := by simp [mul_assoc]
  have hgL : g ∈ L := by
    apply ((isNormalizedTI_iff_mem_conj.mp hTI).2.2
      ⟨haP, ha⟩ trivial).mp
    rw [hback]
    exact ⟨hyP, fun hy ↦ ha (isConj_one_right.mp (hy ▸ hya))⟩
  let aL : L := ⟨a, hZL haZ⟩
  let gL : L := ⟨g, hgL⟩
  have hnormal : gL⁻¹ * aL * gL ∈ Z.subgroupOf L :=
    hZnormal.conj_mem' aL (by exact haZ) gL
  change g⁻¹ * a * g ∈ Z at hnormal
  simpa only [hback] using hnormal

private theorem not_isConj_inv_of_normalizedTI_odd
    {G : Type u} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (hoddL : Odd (Nat.card L))
    (hTI : IsNormalizedTI
      (subgroupNonidentity (P : Subgroup G)) ⊤ L)
    (hZP : Z ≤ centerWithin (P : Subgroup G))
    {z : G} (hzZ : z ∈ Z) (hz : z ≠ 1) :
    ¬ IsConj z⁻¹ z := by
  intro hconj
  obtain ⟨g, hg⟩ := isConj_iff.mp hconj
  have hzP : z ∈ (P : Subgroup G) := (hZP hzZ).1
  have hzinvP : z⁻¹ ∈ (P : Subgroup G) := P.inv_mem hzP
  have hgInvL : g⁻¹ ∈ L := by
    apply ((isNormalizedTI_iff_mem_conj.mp hTI).2.2
      ⟨hzinvP, inv_ne_one.mpr hz⟩ trivial).mp
    simpa only [inv_inv] using
      (show g * z⁻¹ * g⁻¹ ∈ subgroupNonidentity (P : Subgroup G) by
        rw [hg]
        exact ⟨hzP, hz⟩)
  have hgL : g ∈ L := by simpa using L.inv_mem hgInvL
  let zL : L := ⟨z, (normalizedTI_sylow_le P L hTI) hzP⟩
  let gL : L := ⟨g, hgL⟩
  have hconjL : IsConj zL⁻¹ zL := by
    apply isConj_iff.mpr
    exact ⟨gL, Subtype.ext hg⟩
  have := eq_one_of_isConj_inv_self hoddL hconjL
  exact hz (congrArg Subtype.val this)

private theorem conjugacyClassCard_eq_stabilizerIndex
    {G : Type u} [Group G] [Fintype G] (z : G) :
    conjugacyClassCard z =
      (MulAction.stabilizer (ConjAct G) z).index := by
  classical
  rw [MulAction.index_stabilizer, conjugacyClassCard]
  let S : Set G := {g | IsConj g z}
  have horbit : MulAction.orbit (ConjAct G) z = S := by
    ext g
    simp [S]
  rw [horbit, Set.ncard_eq_toFinset_card S (Set.toFinite S)]
  apply congrArg Finset.card
  ext g
  simp [S]

private theorem conjugacyClassCard_coprime_sylowCard
    {G : Type u} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) {z : G}
    (hzcentral : z ∈ centerWithin (P : Subgroup G)) :
    (conjugacyClassCard z).Coprime (Nat.card P) := by
  let e : G ≃* ConjAct G := ConjAct.toConjAct
  let PC : Subgroup (ConjAct G) := (P : Subgroup G).map e
  have hPC : PC ≤ MulAction.stabilizer (ConjAct G) z := by
    rintro t ⟨g, hgP, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change g * z * g⁻¹ = z
    have hcomm : g * z = z * g := hzcentral.2 g hgP
    calc
      g * z * g⁻¹ = z * (g * g⁻¹) := by rw [hcomm, mul_assoc]
      _ = z := by simp
  have hdvd : conjugacyClassCard z ∣ P.index := by
    rw [conjugacyClassCard_eq_stabilizerIndex]
    have := Subgroup.index_dvd_of_le hPC
    simpa only [PC, Subgroup.index_map_equiv] using this
  exact P.card_coprime_index.symm.coprime_dvd_left hdvd

private theorem cancel_nat_factor_mod
    {m c : ℕ} {x y : ℂ}
    (hcop : c.Coprime m)
    (hx : IsIntegral ℤ x) (hy : IsIntegral ℤ y)
    (hxy : IsIntegralModEq (m : ℂ) ((c : ℂ) * x) ((c : ℂ) * y)) :
    IsIntegralModEq (m : ℂ) x y := by
  obtain ⟨z, hz, hfactor⟩ := hxy
  let a : ℤ := c.gcdA m
  let b : ℤ := c.gcdB m
  have hbez : (c : ℤ) * a + (m : ℤ) * b = 1 := by
    change (c : ℤ) * c.gcdA m + (m : ℤ) * c.gcdB m = 1
    rw [← Nat.gcd_eq_gcd_ab, hcop.gcd_eq_one]
    rfl
  have hbezC : (c : ℂ) * (a : ℂ) + (m : ℂ) * (b : ℂ) = 1 := by
    exact_mod_cast hbez
  have hcx : (c : ℂ) * (x - y) = (m : ℂ) * z := by
    calc
      (c : ℂ) * (x - y) = (c : ℂ) * x - (c : ℂ) * y := by ring
      _ = (m : ℂ) * z := hfactor
  refine ⟨(a : ℂ) * z + (b : ℂ) * (x - y), ?_, ?_⟩
  · exact ((isIntegral_intCast a).mul hz).add
      ((isIntegral_intCast b).mul (hx.sub hy))
  · calc
      x - y =
          ((c : ℂ) * (a : ℂ) + (m : ℂ) * (b : ℂ)) * (x - y) := by
        rw [hbezC, one_mul]
      _ = (a : ℂ) * ((c : ℂ) * (x - y)) +
          (m : ℂ) * (b : ℂ) * (x - y) := by ring
      _ = (a : ℂ) * ((m : ℂ) * z) +
          (m : ℂ) * (b : ℂ) * (x - y) := by rw [hcx]
      _ = (m : ℂ) * ((a : ℂ) * z + (b : ℂ) * (x - y)) := by ring

private theorem integer_value_of_constant_on_subgroupNonidentity
    {G : Type u} [Group G] [Fintype G]
    (Z : Subgroup G) (hZne : Z ≠ ⊥)
    (chi : IrreducibleCharacter G ℂ)
    {z : G} (hzZ : z ∈ Z) (hz : z ≠ 1)
    (hconstant : ∀ ⦃x y : G⦄,
      x ∈ Z → x ≠ 1 → y ∈ Z → y ≠ 1 → chi x = chi y) :
    ∃ n : ℤ, chi z = (n : ℂ) := by
  classical
  have hchiIntegral : IsIntegral ℤ (chi z) := by
    rw [← chi.representation_character]
    exact representation_character_isIntegral chi.representation.ρ z
  apply (IsIntegral.exists_int_iff_exists_rat hchiIntegral).mp
  let rhoZ : Representation ℂ Z chi.representation :=
    chi.representation.ρ.comp Z.subtype
  letI : Invertible (Nat.card Z : ℂ) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hchar (x : Z) : rhoZ.character x = chi x := by
    change chi.representation.character (x : G) = chi (x : G)
    exact chi.representation_character (x : G)
  have hsum :
      (∑ x : Z, chi (x : G)) =
        chi 1 + ((Nat.card Z - 1 : ℕ) : ℂ) * chi z := by
    rw [Fintype.sum_eq_add_sum_subtype_ne
      (fun x : Z ↦ chi (x : G)) (1 : Z)]
    simp only [Subgroup.coe_one]
    congr 1
    calc
      (∑ x : {x : Z // x ≠ 1}, chi (x.1 : G)) =
          ∑ _x : {x : Z // x ≠ 1}, chi z := by
        apply Finset.sum_congr rfl
        intro x _
        apply hconstant x.1.2
        · intro hx
          apply x.2
          exact Subtype.ext hx
        · exact hzZ
        · exact hz
      _ = ((Nat.card Z - 1 : ℕ) : ℂ) * chi z := by
        have hcardNon : Fintype.card {x : Z // x ≠ 1} = Nat.card Z - 1 := by
          calc
            Fintype.card {x : Z // x ≠ 1} = Fintype.card Z - 1 :=
              Set.card_ne_eq _
            _ = Nat.card Z - 1 := by rw [Fintype.card_eq_nat_card]
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, hcardNon]
  have havg := rhoZ.card_inv_mul_sum_char_eq_finrank
  have havg' :
      (Nat.card Z : ℂ)⁻¹ *
          (chi 1 + ((Nat.card Z - 1 : ℕ) : ℂ) * chi z) =
        (Module.finrank ℂ (Representation.invariants rhoZ) : ℂ) := by
    rw [← hsum]
    simpa only [hchar] using havg
  rw [IrreducibleCharacter.apply_one_eq_finrank] at havg'
  have hZcard : 1 < Nat.card Z := Z.one_lt_card_iff_ne_bot.mpr hZne
  have hcardC : (Nat.card Z : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  have hpred : Nat.card Z - 1 ≠ 0 := Nat.sub_ne_zero_of_lt hZcard
  have hpredC : ((Nat.card Z - 1 : ℕ) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.mpr hpred
  have havg'' :
      (Module.finrank ℂ chi.representation : ℂ) +
          ((Nat.card Z - 1 : ℕ) : ℂ) * chi z =
        (Nat.card Z : ℂ) *
          (Module.finrank ℂ (Representation.invariants rhoZ) : ℂ) :=
    (inv_mul_eq_iff_eq_mul₀ hcardC).mp havg'
  let q : ℚ :=
    ((Nat.card Z : ℚ) *
        (Module.finrank ℂ (Representation.invariants rhoZ) : ℚ) -
      (Module.finrank ℂ chi.representation : ℚ)) /
        (Nat.card Z - 1 : ℕ)
  refine ⟨q, ?_⟩
  have hzFormula :
      chi z =
        ((Nat.card Z : ℂ) *
            (Module.finrank ℂ (Representation.invariants rhoZ) : ℂ) -
          (Module.finrank ℂ chi.representation : ℂ)) /
            ((Nat.card Z - 1 : ℕ) : ℂ) := by
    apply (eq_div_iff hpredC).mpr
    linear_combination havg''
  rw [hzFormula]
  simp [q]

/-- Peterfalvi, Section 6, the lemma immediately preceding Theorem (6.8).

If an irreducible character is constant on the nonidentity elements of a
nontrivial subgroup `Z` lying in the center of a TI Sylow subgroup `P`, then
that common value is an integer and is congruent to the degree modulo `|P|`
in the algebraic integers.

The source also assumes that the relative centralizers in `L` of the
nonidentity elements of `Z` have constant order.  The class-pair proof below
retains that hypothesis verbatim, although it only compares `z` with `z⁻¹`;
their class sizes agree without the full regularity assumption. -/
theorem constant_irr_mod_TI_Sylow
    {G : Type u} [Group G] [Fintype G]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (L Z : Subgroup G)
    (hoddL : Odd (Nat.card L))
    (hTI : IsNormalizedTI
      (subgroupNonidentity (P : Subgroup G)) ⊤ L)
    (hZL : Z ≤ L)
    (hZnormal : (Z.subgroupOf L).Normal)
    (hZne : Z ≠ ⊥)
    (hZcenter : Z ≤ centerWithin (P : Subgroup G))
    (hcentralizer : ∀ ⦃x y : G⦄,
      x ∈ Z → x ≠ 1 → y ∈ Z → y ≠ 1 →
      Nat.card (centralizerWithin L (Subgroup.zpowers x)) =
        Nat.card (centralizerWithin L (Subgroup.zpowers y)))
    (phi : IrreducibleCharacter G ℂ)
    (hconstant : ∀ ⦃x y : G⦄,
      x ∈ Z → x ≠ 1 → y ∈ Z → y ≠ 1 → phi x = phi y) :
    ∀ ⦃x : G⦄, x ∈ Z → x ≠ 1 →
      (∃ n : ℤ, phi x = (n : ℂ)) ∧
        IsIntegralModEq (Nat.card P : ℂ) (phi x) (phi 1) := by
  classical
  have hPL : (P : Subgroup G) ≤ L := normalizedTI_sylow_le P L hTI
  have hLnormP : L ≤ Subgroup.normalizer (P : Set G) :=
    normalizedTI_le_normalizer_sylow P L hTI
  have hPnormal : (P.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPL).mpr hLnormP
  intro z hzZ hz
  refine ⟨integer_value_of_constant_on_subgroupNonidentity
    Z hZne phi hzZ hz hconstant, ?_⟩
  have hzinvZ : z⁻¹ ∈ Z := Z.inv_mem hzZ
  have hzinv : z⁻¹ ≠ 1 := inv_ne_one.mpr hz
  have _hcentralizerInv :
      Nat.card (centralizerWithin L (Subgroup.zpowers z)) =
        Nat.card (centralizerWithin L (Subgroup.zpowers z⁻¹)) :=
    hcentralizer hzZ hz hzinvZ hzinv
  have hphiInv : phi z⁻¹ = phi z :=
    hconstant hzinvZ hzinv hzZ hz
  have hnotConj : ¬ IsConj z⁻¹ z :=
    not_isConj_inv_of_normalizedTI_odd P L Z hoddL hTI hZcenter hzZ hz
  have honeSelf : classPairOneCount z z = 0 :=
    classPairOneCount_self_eq_zero hnotConj
  have honeInv : classPairOneCount z z⁻¹ = conjugacyClassCard z :=
    classPairOneCount_inv_eq_classCard z
  have hrelPhi (g : G) (hg : meetsNonidentityClass Z g) : phi g = phi z := by
    obtain ⟨w, hwZ, hw, hgw⟩ := hg
    calc
      phi g = phi w := by
        obtain ⟨a, ha⟩ := isConj_iff.mp hgw
        rw [← phi.representation_character,
          ← phi.representation_character, ← ha]
        exact (phi.representation.char_conj g a).symm
      _ = phi z := hconstant hwZ hw hzZ hz
  have hfixed : ∀ (t : (P : Subgroup G)), t ≠ 1 → ∀ g : G,
      (t : G) * g * (t : G)⁻¹ = g →
      meetsNonidentityClass Z g → g ∈ Z := by
    intro t ht g htg hg
    exact fixed_conjugate_mem_normal_subgroup P L Z hTI hPL
      hPnormal hZL hZnormal hZcenter t ht g htg hg
  have hredSelf := classPairReduction (P : Subgroup G) Z phi z z z
    hzZ hz hzZ hz hrelPhi hfixed
  have hredInv := classPairReduction (P : Subgroup G) Z phi z z⁻¹ z
    hzZ hz hzinvZ hzinv hrelPhi hfixed
  rw [honeSelf, Nat.cast_zero, zero_mul, zero_add] at hredSelf
  rw [honeInv] at hredInv
  have hsumPhi : classPairCharacterSum phi z z =
      classPairCharacterSum phi z z⁻¹ :=
    classPairCharacterSum_self_eq_inv phi z hphiInv
  have hphiCompare :
      IsIntegralModEq (Nat.card P : ℂ)
        ((classPairRelevantCount Z z z : ℂ) * phi z)
        ((conjugacyClassCard z : ℂ) * phi 1 +
          (classPairRelevantCount Z z z⁻¹ : ℂ) * phi z) :=
    hredSelf.symm.trans
      ((IsIntegralModEq.of_eq hsumPhi).trans hredInv)
  let oneChi : IrreducibleCharacter G ℂ := IrreducibleCharacter.trivial
  have hrelOne (g : G) (_hg : meetsNonidentityClass Z g) : oneChi g = oneChi z := by
    simp [oneChi, IrreducibleCharacter.trivial_apply]
  have hredOneSelf := classPairReduction (P : Subgroup G) Z oneChi z z z
    hzZ hz hzZ hz hrelOne hfixed
  have hredOneInv := classPairReduction (P : Subgroup G) Z oneChi z z⁻¹ z
    hzZ hz hzinvZ hzinv hrelOne hfixed
  simp only [oneChi, IrreducibleCharacter.trivial_apply, mul_one,
    honeSelf, Nat.cast_zero, zero_add, honeInv] at hredOneSelf hredOneInv
  have hsumOne : classPairCharacterSum oneChi z z =
      classPairCharacterSum oneChi z z⁻¹ :=
    classPairCharacterSum_self_eq_inv oneChi z (by
      simp [oneChi, IrreducibleCharacter.trivial_apply])
  have hcountCompare :
      IsIntegralModEq (Nat.card P : ℂ)
        (classPairRelevantCount Z z z : ℂ)
        ((conjugacyClassCard z : ℂ) +
          (classPairRelevantCount Z z z⁻¹ : ℂ)) :=
    hredOneSelf.symm.trans
      ((IsIntegralModEq.of_eq hsumOne).trans hredOneInv)
  have hphiIntegral : IsIntegral ℤ (phi z) := by
    rw [← phi.representation_character]
    exact representation_character_isIntegral phi.representation.ρ z
  have hcountPhi := hcountCompare.mul_right hphiIntegral
  have hcombined := hcountPhi.symm.trans hphiCompare
  have hsubtract := hcombined.sub
    (IsIntegralModEq.refl (Nat.card P : ℂ)
      ((classPairRelevantCount Z z z⁻¹ : ℂ) * phi z))
  have hclassFactor :
      IsIntegralModEq (Nat.card P : ℂ)
        ((conjugacyClassCard z : ℂ) * phi z)
        ((conjugacyClassCard z : ℂ) * phi 1) := by
    convert hsubtract using 1 <;> push_cast <;> ring
  have hdegreeIntegral : IsIntegral ℤ (phi 1) := by
    rw [← phi.representation_character]
    exact representation_character_isIntegral phi.representation.ρ 1
  exact cancel_nat_factor_mod
    (conjugacyClassCard_coprime_sylowCard P (hZcenter hzZ))
    hphiIntegral hdegreeIntegral hclassFactor

end

end Submission.OddOrder.PF
