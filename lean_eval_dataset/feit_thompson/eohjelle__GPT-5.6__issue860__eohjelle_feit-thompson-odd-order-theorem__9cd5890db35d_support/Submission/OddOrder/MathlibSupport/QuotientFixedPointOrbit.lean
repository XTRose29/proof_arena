import Submission.OddOrder.MathlibSupport.FixedPointFreeOrbit

/-!
Fixed-point-free orbit cardinality for actions descending to quotient groups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [Group X] [MulDistribMulAction G X]
variable (N : Subgroup X) [N.Normal] [MulAction.QuotientAction G N]

omit [N.Normal] in
/-- A representative criterion for a coset to be fixed by the descended
action. -/
theorem smul_quotient_mk_eq_iff (g : G) (x : X) :
    g • (x : X ⧸ N) = (x : X ⧸ N) ↔ (g • x)⁻¹ * x ∈ N := by
  rw [MulAction.Quotient.smul_coe]
  exact QuotientGroup.eq

/-- If every fixed coset representative lies in the quotient subgroup, then a
nonidentity acting element fixes only the identity coset. -/
theorem quotient_fixedBy_eq_singleton_of_fixed_rep_mem
    (g : G) (_hg : g ≠ 1)
    (hlift : ∀ x : X, (g • x)⁻¹ * x ∈ N -> x ∈ N) :
    MulAction.fixedBy (X ⧸ N) g = {1} := by
  ext q
  constructor
  · intro hq
    rw [Set.mem_singleton_iff]
    induction q using QuotientGroup.induction_on with
    | _ x =>
        apply (QuotientGroup.eq_one_iff x).2
        apply hlift x
        apply (smul_quotient_mk_eq_iff N g x).1
        exact hq
  · intro hq
    rw [Set.mem_singleton_iff] at hq
    subst q
    change g • ((1 : X) : X ⧸ N) = ((1 : X) : X ⧸ N)
    rw [MulAction.Quotient.smul_coe]
    simp

/-- A quotient action has full-size nonidentity orbits once fixed cosets lift
only from the quotient subgroup. -/
theorem natCard_quotient_orbit_eq_natCard_of_fixed_rep_mem
    [Finite G] (q : X ⧸ N) (hq : q ≠ 1)
    (hlift : ∀ g : G, g ≠ 1 -> ∀ x : X, (g • x)⁻¹ * x ∈ N -> x ∈ N) :
    Nat.card (MulAction.orbit G q) = Nat.card G := by
  apply natCard_orbit_eq_natCard_of_ne_one_of_fixedBy_eq_singleton q hq
  intro g hg
  exact quotient_fixedBy_eq_singleton_of_fixed_rep_mem N g hg (hlift g hg)

end Submission.OddOrder.MathlibSupport
