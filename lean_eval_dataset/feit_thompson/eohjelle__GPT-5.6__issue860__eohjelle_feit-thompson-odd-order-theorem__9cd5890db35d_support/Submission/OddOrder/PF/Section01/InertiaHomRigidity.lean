import Submission.OddOrder.PF.Section01.MultiplicityNormExpansion

/-!
# Hom-space rigidity for inertia induction

The norm comparison in Peterfalvi 1.7(a) shows that induction from the
inertia subgroup takes each constituent to an object with one-dimensional
endomorphism space, while distinct constituents have no morphisms between
their induced objects.  This is the representation-theoretic core of the
Clifford correspondence used below.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- The induced inertia constituents have identity Hom Gram matrix. -/
theorem inertia_induced_hom_rigidity
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    let T := inertia H (theta : ClassFunction H k)
    let thetaT := inertiaSubgroupCharacter H theta
    let V : FDRep k T :=
      FDRep.induceFromSubgroup (H.subgroupOf T) thetaT.representation
    let F : ClassFunction T k := ofRepresentation V.ρ
    let s := constituents F
    let W := fun psi : IrreducibleCharacter T k ↦
      FDRep.induceFromSubgroup T psi.representation
    (∀ psi ∈ s, Module.finrank k (W psi ⟶ W psi) = 1) ∧
      ∀ psi ∈ s, ∀ phi ∈ s, psi ≠ phi →
        Module.finrank k (W phi ⟶ W psi) = 0 := by
  dsimp only
  let T := inertia H (theta : ClassFunction H k)
  let thetaT := inertiaSubgroupCharacter H theta
  let V : FDRep k T :=
    FDRep.induceFromSubgroup (H.subgroupOf T) thetaT.representation
  let F : ClassFunction T k := ofRepresentation V.ρ
  let s := constituents F
  let m := fun psi : IrreducibleCharacter T k ↦ psi.multiplicity V
  let W := fun psi : IrreducibleCharacter T k ↦
    FDRep.induceFromSubgroup T psi.representation
  have hF : F = induce (H.subgroupOf T) (thetaT : ClassFunction
      (H.subgroupOf T) k) := by
    dsimp only [F, V]
    exact (ofRepresentation_induceFromSubgroup_general
      (H.subgroupOf T) thetaT.representation).trans
        (congrArg (induce (H.subgroupOf T))
          thetaT.ofRepresentation_representation)
  have hW (psi : IrreducibleCharacter T k) :
      ofRepresentation (W psi).ρ = induce T (psi : ClassFunction T k) := by
    dsimp only [W]
    exact (ofRepresentation_induceFromSubgroup_general T
      psi.representation).trans
        (congrArg (induce T) psi.ofRepresentation_representation)
  have hm : ∀ psi ∈ s, 0 < m psi := by
    intro psi hpsi
    apply (psi.isConstituent_ofRepresentation_iff_multiplicity_pos V).mp
    exact (mem_constituents_iff F psi).mp hpsi
  have hd : ∀ psi ∈ s,
      0 < Module.finrank k (W psi ⟶ W psi) := by
    intro psi _
    dsimp only [W]
    exact FDRep.finrank_end_induceFromSubgroup_pos T psi
  have hsourceExpansion :
      characterPairing F F =
        (((∑ psi ∈ s, m psi * m psi : ℕ) : k)) := by
    exact realized_selfPairing_eq_sum_sq_multiplicity V
  have hcoeff (psi : IrreducibleCharacter T k) :
      characterPairing (psi : ClassFunction T k) F = (m psi : k) := by
    rw [characterPairing_comm]
    exact psi.characterPairing_ofRepresentation_eq_multiplicity V
  have hambientExpansion :
      induce H (theta : ClassFunction H k) =
        ∑ psi ∈ s, (m psi : k) • ofRepresentation (W psi).ρ := by
    have hexp := cfInd_sum_inertia_expansion H theta
    change induce H (theta : ClassFunction H k) =
      ∑ psi ∈ constituents
          (induce (H.subgroupOf T) (thetaT : ClassFunction
            (H.subgroupOf T) k)),
        characterPairing (psi : ClassFunction T k)
            (induce (H.subgroupOf T) (thetaT : ClassFunction
              (H.subgroupOf T) k)) •
          induce T (psi : ClassFunction T k) at hexp
    rw [← hF] at hexp
    rw [hexp]
    apply Finset.sum_congr rfl
    intro psi _
    rw [hcoeff, hW]
  have hambientExpansionNorm :
      characterPairing (induce H (theta : ClassFunction H k))
          (induce H (theta : ClassFunction H k)) =
        (((∑ psi ∈ s, ∑ phi ∈ s,
          m psi * m phi * Module.finrank k (W phi ⟶ W psi) : ℕ) : k)) := by
    rw [hambientExpansion]
    exact selfPairing_sum_realized s m W
  have hsourceNorm : characterPairing F F =
      ((Nat.card T / Nat.card H : ℕ) : k) := by
    rw [hF]
    exact inertiaSubgroupCharacter_induce_norm H theta
  letI : Invertible (Nat.card H : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  have hambientNorm :
      characterPairing (induce H (theta : ClassFunction H k))
          (induce H (theta : ClassFunction H k)) =
        ((Nat.card T / Nat.card H : ℕ) : k) := by
    simpa only [inertiaIndex, T] using cfnorm_Ind_irr H theta
  have heq : (∑ psi ∈ s, m psi * m psi) =
      ∑ psi ∈ s, ∑ phi ∈ s,
        m psi * m phi * Module.finrank k (W phi ⟶ W psi) := by
    apply Nat.cast_injective (R := k)
    exact hsourceExpansion.symm.trans
      (hsourceNorm.trans
        (hambientNorm.symm.trans hambientExpansionNorm))
  exact positiveMultiplicity_norm_rigidity s m
    (fun psi phi ↦ Module.finrank k (W phi ⟶ W psi)) hm hd heq

end ClassFunction

end

end Submission.OddOrder.PF
