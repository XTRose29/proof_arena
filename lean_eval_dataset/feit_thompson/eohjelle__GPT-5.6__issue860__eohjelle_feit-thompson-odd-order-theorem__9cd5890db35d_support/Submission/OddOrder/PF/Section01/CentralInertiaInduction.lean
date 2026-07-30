import Submission.OddOrder.PF.Section01.InertiaUniformMultiplicity

/-!
# Peterfalvi 1.7(b): induction with abelian inertia quotient

This file assembles the common-multiplicity result with the Clifford
correspondence of 1.7(a).  It gives the unweighted ambient constituent sum,
the number of its constituents, and their common degree.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- Peterfalvi 1.7(b), source `cfInd_central_Inertia`. -/
theorem cfInd_central_inertia
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k)
    [IsMulCommutative
      ((inertia H (theta : ClassFunction H k)) ⧸
        H.subgroupOf (inertia H (theta : ClassFunction H k)))] :
    let T := inertia H (theta : ClassFunction H k)
    let K := H.subgroupOf T
    let thetaT := inertiaSubgroupCharacter H theta
    let V : FDRep k T := FDRep.induceFromSubgroup K thetaT.representation
    let calA := inertiaConstituents H theta
    let calB := constituents (induce H (theta : ClassFunction H k))
    ∃ e : ℕ, 0 < e ∧
      (∀ psi ∈ calA, psi.multiplicity V = e) ∧
      induce H (theta : ClassFunction H k) =
        (e : k) • ∑ chi ∈ calB, (chi : ClassFunction G k) ∧
      (calB.card : k) =
        ((Nat.card T / Nat.card H : ℕ) : k) / (e : k) ^ 2 ∧
      ∀ chi ∈ calB,
        chi 1 = (T.index : k) * (e : k) * theta 1 := by
  dsimp only
  let T := inertia H (theta : ClassFunction H k)
  let K := H.subgroupOf T
  let thetaT := inertiaSubgroupCharacter H theta
  let V : FDRep k T := FDRep.induceFromSubgroup K thetaT.representation
  let F : ClassFunction T k := ofRepresentation V.ρ
  let calA := inertiaConstituents H theta
  let calB := constituents (induce H (theta : ClassFunction H k))
  let AtoB := inertiaConstituentMap H theta
  let m := fun psi : IrreducibleCharacter T k ↦ psi.multiplicity V
  letI : Fintype K := Fintype.ofFinite _
  letI : Invertible (Nat.card K : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card T : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  obtain ⟨e, he, huniform⟩ :=
    inertiaConstituents_uniform_multiplicity H theta
  change ∀ psi ∈ calA,
    m psi = e ∧ psi 1 = (e : k) * thetaT 1 at huniform
  have hF : F = induce K (thetaT : ClassFunction K k) := by
    dsimp only [F, V]
    exact (ofRepresentation_induceFromSubgroup_general
      K thetaT.representation).trans
        (congrArg (induce K) thetaT.ofRepresentation_representation)
  have hcoeff (psi : IrreducibleCharacter T k) :
      characterPairing (psi : ClassFunction T k) F = (m psi : k) := by
    rw [characterPairing_comm]
    exact psi.characterPairing_ofRepresentation_eq_multiplicity V
  have h17a := cfInd_sum_inertia H theta
  dsimp only at h17a
  obtain ⟨_, _, hinj, himage, hexp⟩ := h17a
  change Function.Injective AtoB at hinj
  change Finset.univ.image AtoB = calB at himage
  change induce H (theta : ClassFunction H k) =
    ∑ psi ∈ calA,
      characterPairing (psi : ClassFunction T k) F •
        induce T (psi : ClassFunction T k) at hexp
  have hsumA :
      (∑ psi ∈ calA,
          induce T (psi : ClassFunction T k)) =
        ∑ chi ∈ calB, (chi : ClassFunction G k) := by
    calc
      (∑ psi ∈ calA,
          induce T (psi : ClassFunction T k)) =
          ∑ psi : InertiaConstituentIndex H theta,
            induce T (psi.1 : ClassFunction T k) := by
        change (∑ psi ∈ inertiaConstituents H theta,
            induce T (psi : ClassFunction T k)) = _
        rw [Finset.sum_subtype (inertiaConstituents H theta)
          (fun _ ↦ Iff.rfl)]
        rfl
      _ = ∑ psi : InertiaConstituentIndex H theta,
          (AtoB psi : ClassFunction G k) := by rfl
      _ = ∑ chi ∈ Finset.univ.image AtoB,
          (chi : ClassFunction G k) := by
        symm
        rw [Finset.sum_image]
        intro psi _ phi _ heq
        exact hinj heq
      _ = ∑ chi ∈ calB, (chi : ClassFunction G k) := by
        rw [himage]
  have hInd :
      induce H (theta : ClassFunction H k) =
        (e : k) • ∑ chi ∈ calB, (chi : ClassFunction G k) := by
    rw [hexp]
    calc
      (∑ psi ∈ calA,
          characterPairing (psi : ClassFunction T k) F •
            induce T (psi : ClassFunction T k)) =
          ∑ psi ∈ calA,
            (e : k) • induce T (psi : ClassFunction T k) := by
        apply Finset.sum_congr rfl
        intro psi hpsi
        rw [hcoeff, (huniform psi hpsi).1]
      _ = (e : k) • ∑ psi ∈ calA,
          induce T (psi : ClassFunction T k) := by
        rw [Finset.smul_sum]
      _ = (e : k) • ∑ chi ∈ calB,
          (chi : ClassFunction G k) := by rw [hsumA]
  have hcardAB : calB.card = calA.card := by
    rw [← himage, Finset.card_image_of_injective _ hinj]
    rw [Finset.card_univ]
    change Fintype.card {psi // psi ∈ inertiaConstituents H theta} =
      (inertiaConstituents H theta).card
    exact Fintype.card_coe _
  have hnorm : characterPairing F F =
      ((Nat.card T / Nat.card H : ℕ) : k) := by
    rw [hF]
    exact inertiaSubgroupCharacter_induce_norm H theta
  have hsumsqCast :
      (((∑ psi ∈ calA, m psi * m psi : ℕ) : k)) =
        ((Nat.card T / Nat.card H : ℕ) : k) := by
    exact (realized_selfPairing_eq_sum_sq_multiplicity V).symm.trans hnorm
  have hsumsq :
      (∑ psi ∈ calA, m psi * m psi : ℕ) =
        Nat.card T / Nat.card H := by
    exact_mod_cast hsumsqCast
  have hcardRatio :
      calB.card * (e * e) = Nat.card T / Nat.card H := by
    calc
      calB.card * (e * e) = calA.card * (e * e) := by rw [hcardAB]
      _ = ∑ _psi ∈ calA, e * e := by simp
      _ = ∑ psi ∈ calA, m psi * m psi := by
        apply Finset.sum_congr rfl
        intro psi hpsi
        rw [(huniform psi hpsi).1]
      _ = Nat.card T / Nat.card H := hsumsq
  have hcard :
      (calB.card : k) =
        ((Nat.card T / Nat.card H : ℕ) : k) / (e : k) ^ 2 := by
    apply (eq_div_iff (pow_ne_zero 2
      (Nat.cast_ne_zero.mpr he.ne'))).2
    simpa only [pow_two, Nat.cast_mul] using
      congrArg (fun n : ℕ ↦ (n : k)) hcardRatio
  have hdegree : ∀ chi ∈ calB,
      chi 1 = (T.index : k) * (e : k) * theta 1 := by
    intro chi hchi
    rw [← himage] at hchi
    obtain ⟨psi, _, rfl⟩ := Finset.mem_image.mp hchi
    change induce T (psi.1 : ClassFunction T k) 1 =
      (T.index : k) * (e : k) * theta 1
    rw [induce_one]
    have hpsiDegree := (huniform psi.1 psi.2).2
    rw [hpsiDegree]
    have hthetaOne : thetaT 1 = theta 1 := by
      simp [thetaT, inertiaSubgroupCharacter_apply]
    rw [hthetaOne]
    ring
  exact ⟨e, he, fun psi hpsi ↦ (huniform psi hpsi).1,
    hInd, hcard, hdegree⟩

end ClassFunction

end

end Submission.OddOrder.PF
