import Submission.OddOrder.PF.Section01.QuotientTwistRestriction

/-!
# Uniform multiplicity over an abelian inertia quotient

When the inertia quotient is abelian, quotient-character twists act
transitively on the irreducible constituents lying above the fixed normal
subgroup character.  Consequently all such constituents have one common
positive multiplicity, and their degrees have the corresponding common
value.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- The inertia constituents have a common positive multiplicity and common
degree when the inertia quotient is abelian. -/
theorem inertiaConstituents_uniform_multiplicity
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k)
    [IsMulCommutative
      ((inertia H (theta : ClassFunction H k)) ⧸
        H.subgroupOf (inertia H (theta : ClassFunction H k)))] :
    let T := inertia H (theta : ClassFunction H k)
    let K := H.subgroupOf T
    let thetaT := inertiaSubgroupCharacter H theta
    let V : FDRep k T := FDRep.induceFromSubgroup K thetaT.representation
    let calA := inertiaConstituents H theta
    ∃ e : ℕ, 0 < e ∧
      ∀ psi ∈ calA,
        psi.multiplicity V = e ∧
          psi 1 = (e : k) * thetaT 1 := by
  dsimp only
  let T := inertia H (theta : ClassFunction H k)
  let K := H.subgroupOf T
  let thetaT := inertiaSubgroupCharacter H theta
  let V : FDRep k T := FDRep.induceFromSubgroup K thetaT.representation
  let F : ClassFunction T k := ofRepresentation V.ρ
  let s := constituents F
  let m := fun chi : IrreducibleCharacter T k ↦ chi.multiplicity V
  letI : Fintype K := Fintype.ofFinite _
  letI : Invertible (Nat.card K : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  letI : Invertible (Nat.card T : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hF : F = induce K (thetaT : ClassFunction K k) := by
    dsimp only [F, V]
    exact (ofRepresentation_induceFromSubgroup_general
      K thetaT.representation).trans
        (congrArg (induce K) thetaT.ofRepresentation_representation)
  have hcoeff (chi : IrreducibleCharacter T k) :
      characterPairing (chi : ClassFunction T k) F = (m chi : k) := by
    rw [characterPairing_comm]
    exact chi.characterPairing_ofRepresentation_eq_multiplicity V
  have hmpos (chi : IrreducibleCharacter T k) (hchi : chi ∈ s) :
      0 < m chi := by
    apply (chi.isConstituent_ofRepresentation_iff_multiplicity_pos V).mp
    exact (mem_constituents_iff F chi).mp hchi
  have hs : s.Nonempty := by
    letI : Nontrivial V := FDRep.induceFromSubgroup_nontrivial K thetaT
    have hFne : F ≠ 0 := by
      intro hzero
      have hone := congrArg (fun f : ClassFunction T k ↦ f 1) hzero
      change V.character 1 = 0 at hone
      rw [FDRep.char_one] at hone
      exact (Nat.cast_ne_zero.mpr Module.finrank_pos.ne') hone
    by_contra hsempty
    rw [Finset.not_nonempty_iff_eq_empty] at hsempty
    apply hFne
    have hexp := sum_constituents_eq F
    rw [show constituents F = s by rfl, hsempty] at hexp
    simpa using hexp.symm
  have hmultPair (chi : IrreducibleCharacter T k) :
      characterPairing (thetaT : ClassFunction K k)
          (restrict K (chi : ClassFunction T k)) = (m chi : k) := by
    calc
      characterPairing (thetaT : ClassFunction K k)
          (restrict K (chi : ClassFunction T k)) =
          characterPairing
            (induce K (thetaT : ClassFunction K k))
            (chi : ClassFunction T k) :=
        (frobeniusReciprocity K (thetaT : ClassFunction K k)
          (chi : ClassFunction T k)).symm
      _ = characterPairing F (chi : ClassFunction T k) := by rw [hF]
      _ = characterPairing (chi : ClassFunction T k) F :=
        characterPairing_comm F (chi : ClassFunction T k)
      _ = (m chi : k) := hcoeff chi
  have hmEq (psi phi : IrreducibleCharacter T k)
      (hpsi : psi ∈ s) (hphi : phi ∈ s) : m psi = m phi := by
    have hresPsi :=
      inertiaConstituent_restrict_eq_multiplicity_smul H theta psi hpsi
    have hindScale :
        induce K (restrict K (psi : ClassFunction T k)) =
          (m psi : k) • F := by
      rw [hresPsi, map_smul, ← hF]
    have hpairne :
        characterPairing
            (induce K (restrict K (psi : ClassFunction T k)))
            (phi : ClassFunction T k) ≠ 0 := by
      rw [hindScale, characterPairing_smul_left,
        characterPairing_comm, hcoeff]
      exact mul_ne_zero
        (Nat.cast_ne_zero.mpr (hmpos psi hpsi).ne')
        (Nat.cast_ne_zero.mpr (hmpos phi hphi).ne')
    have htwist : ∃ chi : MulChar (T ⧸ K) k,
        IrreducibleCharacter.mulCharacterTwist
          (QuotientGroup.mk' K) chi psi = phi := by
      by_contra hnone
      push Not at hnone
      apply hpairne
      rw [induce_restrict_eq_sum_mulCharacterTwist]
      change characterPairingRight (phi : ClassFunction T k)
        (∑ chi : MulChar (T ⧸ K) k,
          (IrreducibleCharacter.mulCharacterTwist
            (QuotientGroup.mk' K) chi psi : ClassFunction T k)) = 0
      rw [map_sum]
      apply Finset.sum_eq_zero
      intro chi _
      exact IrreducibleCharacter.characterPairing_eq_zero (hnone chi)
    obtain ⟨chi, hchi⟩ := htwist
    have hrest :
        restrict K (phi : ClassFunction T k) =
          restrict K (psi : ClassFunction T k) := by
      rw [← hchi, restrict_mulCharacterTwist_quotient]
    apply Nat.cast_injective (R := k)
    calc
      (m psi : k) = characterPairing (thetaT : ClassFunction K k)
          (restrict K (psi : ClassFunction T k)) := (hmultPair psi).symm
      _ = characterPairing (thetaT : ClassFunction K k)
          (restrict K (phi : ClassFunction T k)) := by rw [hrest]
      _ = (m phi : k) := hmultPair phi
  obtain ⟨psi0, hpsi0⟩ := hs
  refine ⟨m psi0, hmpos psi0 hpsi0, ?_⟩
  intro psi hpsi
  have hmeq : m psi = m psi0 := hmEq psi psi0 hpsi hpsi0
  refine ⟨hmeq, ?_⟩
  have hres :=
    inertiaConstituent_restrict_eq_multiplicity_smul H theta psi hpsi
  have hone := congrArg (fun f : ClassFunction K k ↦ f 1) hres
  simp only [restrict_apply, smul_apply, smul_eq_mul] at hone
  change psi 1 = (m psi : k) * thetaT 1 at hone
  rw [hmeq] at hone
  exact hone

end ClassFunction

end

end Submission.OddOrder.PF
