import Submission.OddOrder.PF.Section01.InertiaSubgroupSetup

/-!
# The induced-character sum over inertia constituents

This file proves the sum identity in Peterfalvi 1.7(a): expand induction to
the inertia subgroup over its irreducible constituents, then use linearity
and transitivity of induction to obtain the ambient induced character.
The remaining Clifford-correspondence part of 1.7(a) identifies the induced
summands as distinct ambient irreducibles.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- Inducing first to the inertia subgroup and then to the ambient group is
the original induction. -/
theorem induce_inertiaSubgroup_induce
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    let T := inertia H (theta : ClassFunction H k)
    induce T
        (induce (H.subgroupOf T)
          (inertiaSubgroupCharacter H theta : ClassFunction (H.subgroupOf T) k)) =
      induce H (theta : ClassFunction H k) := by
  dsimp only
  rw [coe_inertiaSubgroupCharacter]
  exact induce_trans H (inertia H (theta : ClassFunction H k))
    (le_inertia H _) (theta : ClassFunction H k)

/-- The final character-sum identity of source `cfInd_sum_Inertia`. -/
theorem cfInd_sum_inertia_expansion
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    let T := inertia H (theta : ClassFunction H k)
    let thetaT := inertiaSubgroupCharacter H theta
    let F : ClassFunction T k :=
      induce (H.subgroupOf T) (thetaT : ClassFunction (H.subgroupOf T) k)
    induce H (theta : ClassFunction H k) =
      ∑ psi ∈ constituents F,
        characterPairing (psi : ClassFunction T k) F •
          induce T (psi : ClassFunction T k) := by
  dsimp only
  let T := inertia H (theta : ClassFunction H k)
  let thetaT := inertiaSubgroupCharacter H theta
  let F : ClassFunction T k :=
    induce (H.subgroupOf T) (thetaT : ClassFunction (H.subgroupOf T) k)
  have htrans : induce T F = induce H (theta : ClassFunction H k) := by
    exact induce_inertiaSubgroup_induce H theta
  calc
    induce H (theta : ClassFunction H k) = induce T F := htrans.symm
    _ = induce T
        (∑ psi ∈ constituents F,
          characterPairing (psi : ClassFunction T k) F •
            (psi : ClassFunction T k)) := by
      exact congrArg (induce T) (sum_constituents_eq F).symm
    _ = ∑ psi ∈ constituents F,
        characterPairing (psi : ClassFunction T k) F •
          induce T (psi : ClassFunction T k) := by
      simp

end ClassFunction

end

end Submission.OddOrder.PF
