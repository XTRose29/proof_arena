import Submission.OddOrder.PF.Section01.ConstituentsOfInjectiveSum

/-!
# The inertia constituent correspondence

The injective induction map from inertia constituents has image exactly the
irreducible constituents of the character induced to the ambient group.
This is the fourth clause of Peterfalvi 1.7(a).
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- The image of induction on inertia constituents is precisely the ambient
constituent set. -/
theorem inertiaConstituentMap_image
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    constituents (induce H (theta : ClassFunction H k)) =
      Finset.univ.image (inertiaConstituentMap H theta) := by
  let T := inertia H (theta : ClassFunction H k)
  let thetaT := inertiaSubgroupCharacter H theta
  let V : FDRep k T :=
    FDRep.induceFromSubgroup (H.subgroupOf T) thetaT.representation
  let F : ClassFunction T k := ofRepresentation V.ρ
  let s := constituents F
  let m := fun psi : IrreducibleCharacter T k ↦ psi.multiplicity V
  have hF : F = induce (H.subgroupOf T) (thetaT : ClassFunction
      (H.subgroupOf T) k) := by
    dsimp only [F, V]
    exact (ofRepresentation_induceFromSubgroup_general
      (H.subgroupOf T) thetaT.representation).trans
        (congrArg (induce (H.subgroupOf T))
          thetaT.ofRepresentation_representation)
  have hcoeff (psi : IrreducibleCharacter T k) :
      characterPairing (psi : ClassFunction T k) F = (m psi : k) := by
    rw [characterPairing_comm]
    exact psi.characterPairing_ofRepresentation_eq_multiplicity V
  have hambientExpansion :
      induce H (theta : ClassFunction H k) =
        ∑ psi ∈ s, (m psi : k) •
          induce T (psi : ClassFunction T k) := by
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
    rw [hcoeff]
  have hambientSubtype :
      induce H (theta : ClassFunction H k) =
        ∑ psi : InertiaConstituentIndex H theta,
          (m psi.1 : k) •
            (inertiaConstituentMap H theta psi : ClassFunction G k) := by
    rw [hambientExpansion]
    rw [Finset.sum_subtype s (fun _ ↦ Iff.rfl)]
    rfl
  have hm : ∀ psi : InertiaConstituentIndex H theta,
      (m psi.1 : k) ≠ 0 := by
    intro psi
    apply Nat.cast_ne_zero.mpr
    exact ((psi.1.isConstituent_ofRepresentation_iff_multiplicity_pos V).mp
      ((mem_constituents_iff F psi.1).mp psi.2)).ne'
  rw [hambientSubtype]
  exact constituents_sum_injective_irreducibles
    (inertiaConstituentMap H theta)
    (inertiaConstituentMap_injective H theta) (fun psi ↦ (m psi.1 : k)) hm

end ClassFunction

end

end Submission.OddOrder.PF
