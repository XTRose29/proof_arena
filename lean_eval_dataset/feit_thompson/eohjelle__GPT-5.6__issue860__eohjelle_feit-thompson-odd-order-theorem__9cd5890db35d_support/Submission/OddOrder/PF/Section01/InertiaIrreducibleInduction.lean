import Submission.OddOrder.PF.Section01.InertiaHomRigidity

/-!
# Irreducible induction from the inertia subgroup

This file upgrades the rank-one conclusion of the norm-rigidity argument to
simplicity, and packages induction of every inertia constituent as an
ambient irreducible character.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- The constituents of the character induced from the normal subgroup to
the inertia subgroup. -/
def inertiaConstituents
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    Finset (IrreducibleCharacter
      (inertia H (theta : ClassFunction H k)) k) :=
  let T := inertia H (theta : ClassFunction H k)
  let thetaT := inertiaSubgroupCharacter H theta
  let V : FDRep k T :=
    FDRep.induceFromSubgroup (H.subgroupOf T) thetaT.representation
  constituents (ofRepresentation V.ρ)

/-- Every constituent over the inertia subgroup induces irreducibly to the
ambient group. -/
theorem inertiaConstituent_induce_isIrreducible
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k)
    (psi : IrreducibleCharacter
      (inertia H (theta : ClassFunction H k)) k)
    (hpsi : psi ∈ inertiaConstituents H theta) :
    IsIrreducibleCharacter G k
      (induce (inertia H (theta : ClassFunction H k))
        (psi : ClassFunction
          (inertia H (theta : ClassFunction H k)) k)) := by
  let T := inertia H (theta : ClassFunction H k)
  let W : FDRep k G := FDRep.induceFromSubgroup T psi.representation
  have hrig := inertia_induced_hom_rigidity H theta
  dsimp only at hrig
  have hpsi' : psi ∈ constituents
      (ofRepresentation
        (FDRep.induceFromSubgroup
          (H.subgroupOf T)
          (inertiaSubgroupCharacter H theta).representation).ρ) := by
    exact hpsi
  have hend : Module.finrank k (W ⟶ W) = 1 := by
    exact hrig.1 psi hpsi'
  letI : NeZero (Nat.card G : k) :=
    ⟨Nat.cast_ne_zero.mpr Nat.card_pos.ne'⟩
  have hsimple : CategoryTheory.Simple W :=
    (FDRep.simple_iff_end_is_rank_one W).mpr hend
  refine ⟨W, hsimple, ?_⟩
  exact (ofRepresentation_induceFromSubgroup_general T
    psi.representation).trans
      (congrArg (induce T) psi.ofRepresentation_representation)

/-- The finite indexing type of inertia constituents. -/
def InertiaConstituentIndex
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :=
  {psi // psi ∈ inertiaConstituents H theta}

instance inertiaConstituentIndexFintype
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    Fintype (InertiaConstituentIndex H theta) := by
  unfold InertiaConstituentIndex
  infer_instance

/-- Induction, bundled as a map from inertia constituents to ambient
irreducible characters. -/
def inertiaConstituentMap
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    InertiaConstituentIndex H theta → IrreducibleCharacter G k :=
  fun psi ↦
    ⟨induce (inertia H (theta : ClassFunction H k))
        (psi.1 : ClassFunction
          (inertia H (theta : ClassFunction H k)) k),
      inertiaConstituent_induce_isIrreducible H theta psi.1 psi.2⟩

@[simp]
theorem coe_inertiaConstituentMap
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k)
    (psi : InertiaConstituentIndex H theta) :
    (inertiaConstituentMap H theta psi : ClassFunction G k) =
      induce (inertia H (theta : ClassFunction H k))
        (psi.1 : ClassFunction
          (inertia H (theta : ClassFunction H k)) k) :=
  rfl

end ClassFunction

end

end Submission.OddOrder.PF
