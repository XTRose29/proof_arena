import Submission.OddOrder.PF.Section01.InertiaIrreducibleInduction

/-!
# Injectivity of induction on inertia constituents

Distinct constituents over the inertia subgroup have zero Hom space after
induction, whereas every induced constituent has a one-dimensional
endomorphism space.  Consequently their bundled ambient irreducible
characters are distinct.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped Classical

universe u

namespace ClassFunction

variable {G k : Type u} [Group G] [Field k] [Fintype G]
  [IsAlgClosed k] [CharZero k]

/-- Induction is injective on the constituents over the inertia subgroup. -/
theorem inertiaConstituentMap_injective
    (H : Subgroup G) [H.Normal] (theta : IrreducibleCharacter H k) :
    Function.Injective (inertiaConstituentMap H theta) := by
  letI : Invertible (Nat.card G : k) :=
    invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')
  intro psi phi hmap
  apply Subtype.ext
  by_contra hne
  let T := inertia H (theta : ClassFunction H k)
  let W := fun xi : IrreducibleCharacter T k ↦
    FDRep.induceFromSubgroup T xi.representation
  have hrig := inertia_induced_hom_rigidity H theta
  dsimp only at hrig
  have hpsi : psi.1 ∈ constituents
      (ofRepresentation
        (FDRep.induceFromSubgroup
          (H.subgroupOf T)
          (inertiaSubgroupCharacter H theta).representation).ρ) := by
    exact psi.2
  have hphi : phi.1 ∈ constituents
      (ofRepresentation
        (FDRep.induceFromSubgroup
          (H.subgroupOf T)
          (inertiaSubgroupCharacter H theta).representation).ρ) := by
    exact phi.2
  have hzero : Module.finrank k (W phi.1 ⟶ W psi.1) = 0 :=
    hrig.2 psi.1 hpsi phi.1 hphi hne
  have hW (xi : IrreducibleCharacter T k) :
      ofRepresentation (W xi).ρ = induce T (xi : ClassFunction T k) := by
    dsimp only [W]
    exact (ofRepresentation_induceFromSubgroup_general T
      xi.representation).trans
        (congrArg (induce T) xi.ofRepresentation_representation)
  have hpairZero :
      characterPairing
          (inertiaConstituentMap H theta psi : ClassFunction G k)
          (inertiaConstituentMap H theta phi : ClassFunction G k) = 0 := by
    rw [coe_inertiaConstituentMap, coe_inertiaConstituentMap,
      ← hW psi.1, ← hW phi.1,
      FDRep.characterPairing_ofRepresentation_eq_finrank_hom,
      hzero, Nat.cast_zero]
  have hpairOne :
      characterPairing
          (inertiaConstituentMap H theta psi : ClassFunction G k)
          (inertiaConstituentMap H theta phi : ClassFunction G k) = 1 := by
    rw [hmap]
    exact IrreducibleCharacter.characterPairing_self _
  exact zero_ne_one (hpairZero.symm.trans hpairOne)

end ClassFunction

end

end Submission.OddOrder.PF
