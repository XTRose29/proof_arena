import Submission.OddOrder.PF.Section01.CharacterMultiplicity

/-!
# The inducing character on its inertia subgroup

For Peterfalvi 1.7, an irreducible character of a normal subgroup is first
transported to the copy of that subgroup inside its inertia group.  This
file bundles the transported character, proves that its inertia there is
the whole inertia group, and computes the norm of its induction.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- The inducing character transported to the copy of `H` inside its
inertia subgroup. -/
def inertiaSubgroupCharacter
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    IrreducibleCharacter
      (H.subgroupOf (inertia H (theta : ClassFunction H k))) k :=
  IrreducibleCharacter.comapMulEquiv
    (Subgroup.subgroupOfEquivOfLe (le_inertia H _)) theta

@[simp]
theorem inertiaSubgroupCharacter_apply
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k)
    (h : H.subgroupOf (inertia H (theta : ClassFunction H k))) :
    inertiaSubgroupCharacter H theta h =
      theta (Subgroup.subgroupOfEquivOfLe (le_inertia H _) h) :=
  IrreducibleCharacter.comapMulEquiv_apply _ theta h

theorem coe_inertiaSubgroupCharacter
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    (inertiaSubgroupCharacter H theta : ClassFunction
      (H.subgroupOf (inertia H (theta : ClassFunction H k))) k) =
      toSubgroupOf H (inertia H (theta : ClassFunction H k))
        (le_inertia H _) (theta : ClassFunction H k) := by
  ext h
  rw [inertiaSubgroupCharacter_apply, toSubgroupOf_apply]

/-- Inside its own inertia subgroup, the transported inducing character has
full inertia. -/
theorem inertia_inertiaSubgroupCharacter_eq_top
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    inertia (H.subgroupOf (inertia H (theta : ClassFunction H k)))
        (inertiaSubgroupCharacter H theta : ClassFunction
          (H.subgroupOf (inertia H (theta : ClassFunction H k))) k) =
      ⊤ := by
  apply top_unique
  intro x _
  rw [mem_inertia_iff]
  have hambient : normalConjugate H (x : G)
      (theta : ClassFunction H k) = (theta : ClassFunction H k) :=
    (mem_inertia_iff H (theta : ClassFunction H k) (x : G)).1 x.property
  ext h
  have hvalue := congrArg
    (fun f : ClassFunction H k ↦
      f (Subgroup.subgroupOfEquivOfLe (le_inertia H _) h)) hambient
  rw [normalConjugate_apply, inertiaSubgroupCharacter_apply,
    inertiaSubgroupCharacter_apply]
  rw [normalConjugate_apply] at hvalue
  calc
    theta (Subgroup.subgroupOfEquivOfLe (le_inertia H _)
        ((MulAut.conjNormal x).symm h)) =
        theta ((MulAut.conjNormal (x : G)).symm
          (Subgroup.subgroupOfEquivOfLe (le_inertia H _) h)) := by
      apply congrArg theta
      apply Subtype.ext
      simp [Subgroup.subgroupOfEquivOfLe,
        MulAut.conjNormal_symm_apply]
    _ = theta (Subgroup.subgroupOfEquivOfLe (le_inertia H _) h) := hvalue

/-- The induction of the transported character to its inertia subgroup has
norm equal to the inertia index. -/
theorem inertiaSubgroupCharacter_induce_norm
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    let T := inertia H (theta : ClassFunction H k)
    characterPairing
        (induce (H.subgroupOf T)
          (inertiaSubgroupCharacter H theta : ClassFunction (H.subgroupOf T) k))
        (induce (H.subgroupOf T)
          (inertiaSubgroupCharacter H theta : ClassFunction (H.subgroupOf T) k)) =
      ((Nat.card T / Nat.card H : ℕ) : k) := by
  dsimp only
  letI : Invertible (Nat.card (H.subgroupOf
      (inertia H (theta : ClassFunction H k))) : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  rw [cfnorm_Ind_irr]
  rw [inertiaIndex, inertia_inertiaSubgroupCharacter_eq_top,
    Subgroup.card_top]
  have hcard : Nat.card
      (H.subgroupOf (inertia H (theta : ClassFunction H k))) = Nat.card H :=
    Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe (le_inertia H _)).toEquiv
  rw [hcard]

end ClassFunction

end

end Submission.OddOrder.PF
