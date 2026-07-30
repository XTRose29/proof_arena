import Submission.OddOrder.MathlibSupport.FreeOrbitCardinality

/-!
Full-size orbits for actions whose nonidentity elements fix only the identity.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulAction G X]

/-- A nonidentity point has no nonidentity stabilizer when every nonidentity
acting element fixes only the identity. -/
theorem smul_eq_imp_eq_one_of_ne_one_of_fixed_point_free
    (x : X) (hx : x ≠ 1)
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ y : X, g • y = y -> y = 1) :
    ∀ g : G, g • x = x -> g = 1 := by
  intro g hg
  by_contra hgne
  exact hx (hfixed g hgne x hg)

/-- Under a fixed-point-free-away-from-one action, every nonidentity point has
trivial stabilizer. -/
theorem stabilizer_eq_bot_of_ne_one_of_fixed_point_free
    (x : X) (hx : x ≠ 1)
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ y : X, g • y = y -> y = 1) :
    MulAction.stabilizer G x = ⊥ :=
  stabilizer_eq_bot_of_smul_eq_imp_eq_one x
    (smul_eq_imp_eq_one_of_ne_one_of_fixed_point_free x hx hfixed)

/-- Every nonidentity point in a finite fixed-point-free-away-from-one action
has an orbit with the cardinality of the acting group. -/
theorem natCard_orbit_eq_natCard_of_ne_one_of_fixed_point_free
    [Finite G] (x : X) (hx : x ≠ 1)
    (hfixed : ∀ g : G, g ≠ 1 -> ∀ y : X, g • y = y -> y = 1) :
    Nat.card (MulAction.orbit G x) = Nat.card G :=
  natCard_orbit_eq_natCard_of_smul_eq_imp_eq_one x
    (smul_eq_imp_eq_one_of_ne_one_of_fixed_point_free x hx hfixed)

/-- Set-valued fixed-point hypotheses provide the pointwise condition used by
the orbit-cardinality theorem. -/
theorem natCard_orbit_eq_natCard_of_ne_one_of_fixedBy_eq_singleton
    [Finite G] (x : X) (hx : x ≠ 1)
    (hfixed : ∀ g : G, g ≠ 1 -> MulAction.fixedBy X g = {1}) :
    Nat.card (MulAction.orbit G x) = Nat.card G := by
  apply natCard_orbit_eq_natCard_of_ne_one_of_fixed_point_free x hx
  intro g hg y hy
  have hy' : y ∈ MulAction.fixedBy X g := hy
  rw [hfixed g hg] at hy'
  simpa using hy'

end Submission.OddOrder.MathlibSupport
