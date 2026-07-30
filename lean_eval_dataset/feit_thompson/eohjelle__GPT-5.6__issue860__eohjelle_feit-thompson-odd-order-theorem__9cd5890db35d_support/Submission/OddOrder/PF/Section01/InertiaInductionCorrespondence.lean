import Submission.OddOrder.PF.Section01.InertiaConstituentCorrespondence

/-!
# Peterfalvi 1.7(a): induction from the inertia subgroup

This file assembles the five clauses of source lemma `cfInd_sum_Inertia`:
induced inertia constituents are irreducible, the bundled map is induction,
the map is injective, its image is the ambient constituent set, and the
ambient induced character has the corresponding weighted sum expansion.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- Peterfalvi 1.7(a), the Clifford correspondence over the inertia
subgroup together with its induced-character expansion. -/
theorem cfInd_sum_inertia
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    let T := inertia H (theta : ClassFunction H k)
    let thetaT := inertiaSubgroupCharacter H theta
    let V : FDRep k T :=
      FDRep.induceFromSubgroup (H.subgroupOf T) thetaT.representation
    let F : ClassFunction T k := ofRepresentation V.ρ
    let calA := inertiaConstituents H theta
    let calB := constituents (induce H (theta : ClassFunction H k))
    let AtoB := inertiaConstituentMap H theta
    (∀ psi ∈ calA,
        IsIrreducibleCharacter G k
          (induce T (psi : ClassFunction T k))) ∧
      (∀ psi : InertiaConstituentIndex H theta,
        (AtoB psi : ClassFunction G k) =
          induce T (psi.1 : ClassFunction T k)) ∧
      Function.Injective AtoB ∧
      Finset.univ.image AtoB = calB ∧
      induce H (theta : ClassFunction H k) =
        ∑ psi ∈ calA,
          characterPairing (psi : ClassFunction T k) F •
            induce T (psi : ClassFunction T k) := by
  dsimp only
  constructor
  · intro psi hpsi
    exact inertiaConstituent_induce_isIrreducible H theta psi hpsi
  constructor
  · intro psi
    exact coe_inertiaConstituentMap H theta psi
  constructor
  · exact inertiaConstituentMap_injective H theta
  constructor
  · exact (inertiaConstituentMap_image H theta).symm
  · let T := inertia H (theta : ClassFunction H k)
    let thetaT := inertiaSubgroupCharacter H theta
    let V : FDRep k T :=
      FDRep.induceFromSubgroup (H.subgroupOf T) thetaT.representation
    let F : ClassFunction T k := ofRepresentation V.ρ
    have hF : F = induce (H.subgroupOf T) (thetaT : ClassFunction
        (H.subgroupOf T) k) := by
      dsimp only [F, V]
      exact (ofRepresentation_induceFromSubgroup_general
        (H.subgroupOf T) thetaT.representation).trans
          (congrArg (induce (H.subgroupOf T))
            thetaT.ofRepresentation_representation)
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
    exact hexp

end ClassFunction

end

end Submission.OddOrder.PF
