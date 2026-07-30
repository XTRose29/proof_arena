import Submission.OddOrder.MathlibSupport.CentralizerConjugationOrbit

/-!
Orbit-quotient classes for actions that are fixed-point-free away from one.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulDistribMulAction G X]

/-- The orbit of the identity under an automorphism action is a singleton. -/
theorem orbit_one_eq_singleton : MulAction.orbit G (1 : X) = {1} := by
  ext x
  constructor
  · rintro ⟨g, rfl⟩
    simp
  · intro hx
    rw [Set.mem_singleton_iff] at hx
    subst x
    exact MulAction.mem_orbit_self 1

/-- The distinguished orbit-quotient class of the identity has a singleton
orbit. -/
theorem orbitRel_quotient_one_orbit_eq_singleton :
    MulAction.orbitRel.Quotient.orbit
      (⟦1⟧ : MulAction.orbitRel.Quotient G X) = {1} := by
  rw [MulAction.orbitRel.Quotient.orbit_mk]
  exact orbit_one_eq_singleton

/-- Any orbit-quotient class other than the class of the identity has the full
cardinality of the acting group. -/
theorem natCard_orbitRel_quotient_orbit_eq_natCard_of_ne_one
    [Finite G]
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ x : X, g • x = x -> x = 1)
    (omega : MulAction.orbitRel.Quotient G X)
    (homega : omega ≠ (⟦1⟧ : MulAction.orbitRel.Quotient G X)) :
    Nat.card omega.orbit = Nat.card G := by
  have hout : omega.out ≠ (1 : X) := by
    intro hout
    apply homega
    rw [← Quotient.out_eq' omega, hout]
  rw [MulAction.orbitRel.Quotient.orbit_eq_orbit_out omega Quotient.out_eq']
  exact natCard_orbit_eq_natCard_of_ne_one_of_fixed_point_free
    omega.out hout hfixed

end Submission.OddOrder.MathlibSupport
