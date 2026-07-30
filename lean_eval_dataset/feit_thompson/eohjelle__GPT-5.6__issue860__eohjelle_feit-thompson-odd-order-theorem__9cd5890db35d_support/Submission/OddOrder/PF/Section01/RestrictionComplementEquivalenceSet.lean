import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence

/-!
Restriction to the complement of a stable set, after Peterfalvi (1.3)(a)-(b).

`RestrictionComplementEquivalence` states the result for the underlying set
of a normal subgroup.  The character-theoretic applications in PF Section 3
use instead a union of conjugacy-stable subsets (and its complement).  This
file records the set-valued form of the same argument.  Conjugation stability
is exactly what is needed to cut class functions into supported pieces, while
inverse stability makes those pieces orthogonal for the pairing convention
used in this development.
-/

namespace Submission.OddOrder.PF

noncomputable section

universe u v

namespace ClassFunction

variable {G : Type u} {k : Type v} [Group G] [Field k]

/-- A conjugacy-class indicator based at a point of a conjugation-stable set
is supported on that set. -/
theorem conjugacyIndicator_mem_supportedOn_set (A : Set G)
    (hA : IsConjStable A) {x : G} (hx : x ∈ A) :
    conjugacyIndicator (k := k) x ∈ supportedOn A := by
  classical
  rw [mem_supportedOn_iff]
  intro y hy
  rw [conjugacyIndicator_apply]
  split_ifs with hconj
  · exfalso
    apply hy
    obtain ⟨z, hz⟩ := isConj_iff.mp hconj.symm
    rw [← hz]
    exact (hA z x).2 hx
  · rfl

end ClassFunction

section PairingBasics

variable {G : Type u} {k : Type v} [Group G] [Field k] [Fintype G]

/-- The class-function pairing is nondegenerate on the functions supported by
a conjugation-stable, inverse-stable set. -/
theorem eq_zero_of_mem_supportedOn_set_of_pairing_eq_zero [CharZero k]
    (A : Set G) (hConj : IsConjStable A) (hInv : IsInvStable A)
    {f : ClassFunction G k} (hf : f ∈ ClassFunction.supportedOn A)
    (horth : ∀ g ∈ ClassFunction.supportedOn A,
      characterPairing g f = 0) :
    f = 0 := by
  classical
  apply ClassFunction.ext
  intro x
  simp only [ClassFunction.zero_apply]
  by_cases hx : x ∈ A
  · have hxinv : x⁻¹ ∈ A := (hInv x).2 hx
    let e := ClassFunction.conjugacyIndicator (k := k) x⁻¹
    have he : e ∈ ClassFunction.supportedOn A :=
      ClassFunction.conjugacyIndicator_mem_supportedOn_set A hConj hxinv
    have hzero := horth e he
    rw [characterPairing_conjugacyIndicator_inv] at hzero
    have hcardG : (Nat.card G : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    have hclassPos :
        0 < (Finset.univ.filter fun y : G ↦ IsConj y x⁻¹).card := by
      rw [Finset.card_pos]
      exact ⟨x⁻¹, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, IsConj.refl _⟩⟩
    have hclass :
        ((Finset.univ.filter fun y : G ↦ IsConj y x⁻¹).card : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr hclassPos.ne'
    exact (mul_eq_zero.mp hzero).resolve_left
      (mul_ne_zero (inv_ne_zero hcardG) hclass)
  · exact ClassFunction.eq_zero_of_mem_supportedOn hf hx

/-- Orthogonality to an arbitrary basis of the functions supported on a
conjugation-stable, inverse-stable set detects support on its complement. -/
theorem mem_supportedOn_compl_iff_pairing_basis_eq_zero_set [CharZero k]
    (A : Set G) (hConj : IsConjStable A) (hInv : IsInvStable A)
    {β : Type*} [Fintype β]
    (Phi : Module.Basis β k (ClassFunction.supportedOn A))
    (D : ClassFunction G k) :
    D ∈ ClassFunction.supportedOn Aᶜ ↔
      ∀ j, characterPairing (Phi j).val D = 0 := by
  classical
  constructor
  · intro hD j
    apply characterPairing_eq_zero_of_inverseDisjoint_supportedOn
      (hf := (Phi j).property) (hg := hD)
    intro x hxA hxAc
    exact hxAc ((hInv x).2 hxA)
  · intro horth
    obtain ⟨fA, hfA, fAc, hfAc, hsum⟩ :=
      ClassFunction.exists_add_supportedOn_compl A hConj D
    have hPhi (j : β) :
        characterPairing (Phi j).val fA = 0 := by
      have hcomp : characterPairing (Phi j).val fAc = 0 := by
        apply characterPairing_eq_zero_of_inverseDisjoint_supportedOn
          (hf := (Phi j).property) (hg := hfAc)
        intro x hxA hxAc
        exact hxAc ((hInv x).2 hxA)
      have htotal := horth j
      rw [← hsum, characterPairing_add_right, hcomp, add_zero] at htotal
      exact htotal
    have hfAzero : fA = 0 := by
      apply eq_zero_of_mem_supportedOn_set_of_pairing_eq_zero
        A hConj hInv hfA
      intro g hg
      let gs : ClassFunction.supportedOn (R := k) A := ⟨g, hg⟩
      have hreprSub :
          ∑ j, (Phi.repr gs j) • Phi j = gs := Phi.sum_repr gs
      have hrepr :
          ∑ j, (Phi.repr gs j) • (Phi j).val = g := by
        have h := congrArg
          (ClassFunction.supportedOn (R := k) A).subtype hreprSub
        simpa only [map_sum, map_smul, Submodule.subtype_apply] using h
      change characterPairingRight fA g = 0
      rw [← hrepr, map_sum]
      apply Finset.sum_eq_zero
      intro j _
      rw [map_smul]
      change (Phi.repr gs j) *
        characterPairing (Phi j).val fA = 0
      rw [hPhi, mul_zero]
    rw [hfAzero, zero_add] at hsum
    rw [← hsum]
    exact hfAc

/-- Peterfalvi (1.3)(a) for a conjugation-stable, inverse-stable set:
agreement on `A` is equivalent to the coefficient identities obtained by
pairing an arbitrary support basis with a finite character expansion and
applying Frobenius reciprocity. -/
theorem equiv_restrict_compl_set [CharZero k]
    (H : Subgroup G) [Fintype H] (A : Set H)
    (hConj : IsConjStable A) (hInv : IsInvStable A)
    {β ι : Type*} [Fintype β] [Fintype ι]
    (Phi : Module.Basis β k (ClassFunction.supportedOn A))
    (chi : ι → ClassFunction H k) (mu : ClassFunction G k) (d : ι → k) :
    Set.EqOn (↑(ClassFunction.restrict H mu) : H → k)
        (↑(∑ i, d i • chi i : ClassFunction H k) : H → k) A ↔
      ∀ j, (∑ i, d i * characterPairing (Phi j).val (chi i)) =
        characterPairing (ClassFunction.induce H (Phi j).val) mu := by
  classical
  let total : ClassFunction H k := ∑ i, d i • chi i
  let D : ClassFunction H k := ClassFunction.restrict H mu - total
  have hpairD (j : β) :
      characterPairing (Phi j).val D =
        characterPairing (Phi j).val (ClassFunction.restrict H mu) -
          ∑ i, d i * characterPairing (Phi j).val (chi i) := by
    change characterPairingLeft (Phi j).val D = _
    rw [show D = ClassFunction.restrict H mu - total by rfl, map_sub]
    change characterPairing (Phi j).val (ClassFunction.restrict H mu) -
      characterPairingLeft (Phi j).val total = _
    rw [show total = ∑ i, d i • chi i by rfl, map_sum]
    simp only [map_smul, smul_eq_mul, characterPairingLeft]
    rfl
  calc
    Set.EqOn (↑(ClassFunction.restrict H mu) : H → k)
        (↑(∑ i, d i • chi i : ClassFunction H k) : H → k) A ↔
        D ∈ ClassFunction.vanishingOn A := by
      simpa only [total, D] using
        (ClassFunction.eqOn_iff_sub_mem_vanishingOn
          (A := A) (ClassFunction.restrict H mu) total)
    _ ↔ D ∈ ClassFunction.supportedOn Aᶜ := by
      rw [ClassFunction.vanishingOn_eq_supportedOn_compl]
    _ ↔ ∀ j, characterPairing (Phi j).val D = 0 :=
      mem_supportedOn_compl_iff_pairing_basis_eq_zero_set
        A hConj hInv Phi D
    _ ↔ ∀ j, (∑ i, d i * characterPairing (Phi j).val (chi i)) =
        characterPairing (ClassFunction.induce H (Phi j).val) mu := by
      constructor
      · intro hzero j
        have hreciprocity := ClassFunction.frobeniusReciprocity H (Phi j).val mu
        have hrestrict :
            characterPairing (Phi j).val (ClassFunction.restrict H mu) =
              ∑ i, d i * characterPairing (Phi j).val (chi i) := by
          rw [← sub_eq_zero, ← hpairD]
          exact hzero j
        exact hrestrict.symm.trans hreciprocity.symm
      · intro heq j
        rw [hpairD, sub_eq_zero]
        have hreciprocity := ClassFunction.frobeniusReciprocity H (Phi j).val mu
        exact hreciprocity.symm.trans (heq j).symm

/-- Peterfalvi (1.3)(b) for a conjugation-stable, inverse-stable set: an
orthonormal ambient family with the prescribed induction formulas restricts
to the original family on `A`; every ambient class function orthogonal to that
family vanishes on `A`. -/
theorem equiv_restrict_compl_ortho_set [CharZero k]
    (H : Subgroup G) [Fintype H] (A : Set H)
    (hConj : IsConjStable A) (hInv : IsInvStable A)
    {β ι : Type*} [Fintype β] [Fintype ι] [DecidableEq ι]
    (Phi : Module.Basis β k (ClassFunction.supportedOn A))
    (chi : ι → ClassFunction H k) (mu : ι → ClassFunction G k)
    (horth : ∀ i j, characterPairing (mu i) (mu j) =
      if i = j then 1 else 0)
    (hinduce : ∀ j, ClassFunction.induce H (Phi j).val =
      ∑ i, characterPairing (Phi j).val (chi i) • mu i) :
    (∀ i, Set.EqOn (↑(ClassFunction.restrict H (mu i)) : H → k)
      (↑(chi i) : H → k) A) ∧
      ∀ nu : ClassFunction G k,
        (∀ i, characterPairing nu (mu i) = 0) →
          ClassFunction.restrict H nu ∈ ClassFunction.vanishingOn A := by
  classical
  constructor
  · intro i
    let d : ι → k := fun q ↦ if q = i then 1 else 0
    have hsumChi : (∑ q, d q • chi q) = chi i := by
      simp [d]
    rw [← hsumChi]
    apply (equiv_restrict_compl_set H A hConj hInv Phi chi (mu i) d).2
    intro j
    have hpair :
        characterPairing (ClassFunction.induce H (Phi j).val) (mu i) =
          characterPairing (Phi j).val (chi i) := by
      rw [hinduce j]
      change characterPairingRight (mu i)
        (∑ q, characterPairing (Phi j).val (chi q) • mu q) = _
      rw [map_sum]
      simp only [map_smul, smul_eq_mul]
      change (∑ q, characterPairing (Phi j).val (chi q) *
        characterPairing (mu q) (mu i)) =
          characterPairing (Phi j).val (chi i)
      simp [horth]
    simpa [d] using hpair.symm
  · intro nu hnu
    have hinduceZero (j : β) :
        characterPairing (ClassFunction.induce H (Phi j).val) nu = 0 := by
      rw [hinduce j]
      change characterPairingRight nu
        (∑ i, characterPairing (Phi j).val (chi i) • mu i) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro i _
      rw [map_smul]
      change characterPairing (Phi j).val (chi i) *
        characterPairing (mu i) nu = 0
      have hz : characterPairing (mu i) nu = 0 :=
        (characterPairing_comm (mu i) nu).trans (hnu i)
      rw [hz, mul_zero]
    have heq :
        Set.EqOn (↑(ClassFunction.restrict H nu) : H → k)
          (↑(∑ _i : ι, (0 : k) • chi _i : ClassFunction H k) : H → k)
          A := by
      apply (equiv_restrict_compl_set H A hConj hInv Phi chi nu
        (fun _ ↦ 0)).2
      intro j
      simp only [zero_mul, Finset.sum_const_zero]
      exact (hinduceZero j).symm
    rw [ClassFunction.mem_vanishingOn_iff]
    intro x hx
    have := heq hx
    simpa using this

end PairingBasics

end

end Submission.OddOrder.PF
