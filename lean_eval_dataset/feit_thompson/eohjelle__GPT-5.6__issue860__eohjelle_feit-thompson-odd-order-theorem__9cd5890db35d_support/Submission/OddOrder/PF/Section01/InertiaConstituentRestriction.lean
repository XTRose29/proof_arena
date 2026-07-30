import Submission.OddOrder.PF.Section01.RestrictionMultiplicity

/-!
# Restriction of inertia constituents

Every irreducible constituent of induction to the inertia subgroup restricts
homogeneously to the original irreducible character.  Its homogeneous
multiplicity is the same natural multiplicity with which it occurs in the
induced character.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Fintype G]
  [Field k] [IsAlgClosed k] [CharZero k]

/-- An inertia constituent restricts to its induction multiplicity times the
original character.  This is the source equality `Dpsi1H`, uniformly for all
constituents. -/
theorem inertiaConstituent_restrict_eq_multiplicity_smul
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k)
    (psi : IrreducibleCharacter
      (inertia H (theta : ClassFunction H k)) k)
    (hpsi : psi ∈ inertiaConstituents H theta) :
    let T := inertia H (theta : ClassFunction H k)
    let K := H.subgroupOf T
    let thetaT := inertiaSubgroupCharacter H theta
    let V : FDRep k T := FDRep.induceFromSubgroup K thetaT.representation
    restrict K (psi : ClassFunction T k) =
      (psi.multiplicity V : k) • (thetaT : ClassFunction K k) := by
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
  have hthetaConj (x : T) (h : K) :
      thetaT ⟨x⁻¹ * (h : T) * x, by
        simpa using (inferInstance : K.Normal).conj_mem (h : T) h.property x⁻¹⟩ =
        thetaT h := by
    have hx : x ∈ inertia K (thetaT : ClassFunction K k) := by
      rw [inertia_inertiaSubgroupCharacter_eq_top H theta]
      exact Subgroup.mem_top x
    have heq := (mem_inertia_iff K (thetaT : ClassFunction K k) x).mp hx
    have heval := congrArg (fun f : ClassFunction K k ↦ f h) heq
    rw [normalConjugate_apply] at heval
    convert heval using 1
    apply congrArg (fun z : K ↦ thetaT z)
    apply Subtype.ext
    simp [MulAut.conjNormal_symm_apply]
  have hrestrictF :
      restrict K F =
        (Nat.card (T ⧸ K) : k) • (thetaT : ClassFunction K k) := by
    rw [hF]
    ext h
    rw [restrict_apply, induce_apply_formula]
    have hmem (x : T) : x⁻¹ * (h : T) * x ∈ K := by
      simpa using (inferInstance : K.Normal).conj_mem
        (h : T) h.property x⁻¹
    simp_rw [dif_pos (hmem _), hthetaConj]
    simp only [Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
      Fintype.card_eq_nat_card]
    rw [smul_apply, smul_eq_mul]
    change (Nat.card K : k)⁻¹ * ((Nat.card T : k) * thetaT h) =
      (Nat.card (T ⧸ K) : k) * thetaT h
    rw [K.card_eq_card_quotient_mul_card_subgroup, Nat.cast_mul]
    have hK : (Nat.card K : k) ≠ 0 :=
      Nat.cast_ne_zero.mpr Nat.card_pos.ne'
    field_simp [hK]
  have hFexp :
      F = ∑ chi ∈ s, (m chi : k) • (chi : ClassFunction T k) := by
    symm
    calc
      (∑ chi ∈ s, (m chi : k) • (chi : ClassFunction T k)) =
          ∑ chi ∈ s,
            characterPairing (chi : ClassFunction T k) F •
              (chi : ClassFunction T k) := by
        apply Finset.sum_congr rfl
        intro chi _
        rw [hcoeff]
      _ = F := sum_constituents_eq F
  have hrestrictExp :
      restrict K F =
        ∑ chi ∈ s, (m chi : k) •
          restrict K (chi : ClassFunction T k) := by
    rw [hFexp]
    simp
  have hmpos : 0 < m psi := by
    apply (psi.isConstituent_ofRepresentation_iff_multiplicity_pos V).mp
    exact (mem_constituents_iff F psi).mp hpsi
  have hthetaCoeff :
      characterPairing (thetaT : ClassFunction K k)
          (restrict K (psi : ClassFunction T k)) = (m psi : k) := by
    calc
      characterPairing (thetaT : ClassFunction K k)
          (restrict K (psi : ClassFunction T k)) =
          characterPairing
            (induce K (thetaT : ClassFunction K k))
            (psi : ClassFunction T k) :=
        (frobeniusReciprocity K (thetaT : ClassFunction K k)
          (psi : ClassFunction T k)).symm
      _ = characterPairing F (psi : ClassFunction T k) := by rw [hF]
      _ = characterPairing (psi : ClassFunction T k) F :=
        characterPairing_comm F (psi : ClassFunction T k)
      _ = (m psi : k) := hcoeff psi
  have hoffdiag (xi : IrreducibleCharacter K k) (hxi : xi ≠ thetaT) :
      IrreducibleCharacter.restrictionMultiplicity K psi xi = 0 := by
    have hsumCast :
        (((∑ chi ∈ s,
          m chi * IrreducibleCharacter.restrictionMultiplicity K chi xi : ℕ) : k)) =
          0 := by
      calc
        (((∑ chi ∈ s,
            m chi * IrreducibleCharacter.restrictionMultiplicity K chi xi : ℕ) : k)) =
            ∑ chi ∈ s, (m chi : k) *
              (IrreducibleCharacter.restrictionMultiplicity K chi xi : k) := by
          simp only [Nat.cast_sum, Nat.cast_mul]
        _ = ∑ chi ∈ s, (m chi : k) *
              characterPairing (xi : ClassFunction K k)
                (restrict K (chi : ClassFunction T k)) := by
          apply Finset.sum_congr rfl
          intro chi _
          rw [characterPairing_comm,
            IrreducibleCharacter.characterPairing_restrict_eq_restrictionMultiplicity]
        _ = characterPairing (xi : ClassFunction K k)
              (∑ chi ∈ s, (m chi : k) •
                restrict K (chi : ClassFunction T k)) := by
          change (∑ chi ∈ s, (m chi : k) *
              characterPairing (xi : ClassFunction K k)
                (restrict K (chi : ClassFunction T k))) =
            IrreducibleCharacter.pairingLeft (xi : ClassFunction K k)
              (∑ chi ∈ s, (m chi : k) •
                restrict K (chi : ClassFunction T k))
          rw [map_sum]
          apply Finset.sum_congr rfl
          intro chi _
          rw [map_smul]
          rfl
        _ = characterPairing (xi : ClassFunction K k) (restrict K F) := by
          rw [hrestrictExp]
        _ = characterPairing (xi : ClassFunction K k)
              ((Nat.card (T ⧸ K) : k) •
                (thetaT : ClassFunction K k)) := by rw [hrestrictF]
        _ = 0 := by
          rw [characterPairing_smul_right,
            IrreducibleCharacter.characterPairing_eq_zero hxi]
          simp
    have hsumNat :
        (∑ chi ∈ s,
          m chi * IrreducibleCharacter.restrictionMultiplicity K chi xi) = 0 := by
      exact_mod_cast hsumCast
    have hterm :
        m psi * IrreducibleCharacter.restrictionMultiplicity K psi xi = 0 :=
      (Finset.sum_eq_zero_iff.mp hsumNat) psi hpsi
    exact (Nat.mul_eq_zero.mp hterm).resolve_left hmpos.ne'
  have hexp := irreducibleCharacterExpansion_eq
    (restrict K (psi : ClassFunction T k))
  calc
    restrict K (psi : ClassFunction T k) =
        irreducibleCharacterExpansion
          (restrict K (psi : ClassFunction T k)) := hexp.symm
    _ = (m psi : k) • (thetaT : ClassFunction K k) := by
      rw [irreducibleCharacterExpansion]
      rw [Finset.sum_eq_single thetaT]
      · rw [hthetaCoeff]
      · intro xi _ hxi
        have hzero := hoffdiag xi hxi
        have hpair :
            characterPairing (xi : ClassFunction K k)
                (restrict K (psi : ClassFunction T k)) = 0 := by
          rw [characterPairing_comm,
            IrreducibleCharacter.characterPairing_restrict_eq_restrictionMultiplicity,
            hzero, Nat.cast_zero]
        rw [hpair, zero_smul]
      · simp

end ClassFunction

end

end Submission.OddOrder.PF
