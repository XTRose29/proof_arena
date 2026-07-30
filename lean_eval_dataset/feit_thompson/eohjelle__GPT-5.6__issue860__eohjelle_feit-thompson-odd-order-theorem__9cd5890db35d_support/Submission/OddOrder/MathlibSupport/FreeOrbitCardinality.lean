import Mathlib.GroupTheory.GroupAction.Quotient
import Submission.OddOrder.MathlibSupport.CyclicOrbitConjugationRankDrop

/-!
Cardinality of orbits with trivial stabilizer under a finite group action.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {X : Type v}
variable [Group G] [MulAction G X]

/-- If only the identity fixes a point, its stabilizer is trivial. -/
theorem stabilizer_eq_bot_of_smul_eq_imp_eq_one
    (x : X) (hfree : ∀ g : G, g • x = x -> g = 1) :
    MulAction.stabilizer G x = ⊥ := by
  ext g
  constructor
  · intro hg
    have hfix : g • x = x := by
      simpa [MulAction.mem_stabilizer_iff] using hg
    simp [hfree g hfix]
  · intro hg
    subst g
    simp

/-- An orbit with trivial stabilizer has the full cardinality of the finite
acting group. -/
theorem natCard_orbit_eq_natCard_of_stabilizer_eq_bot
    [Finite G] (x : X) (hstab : MulAction.stabilizer G x = ⊥) :
    Nat.card (MulAction.orbit G x) = Nat.card G := by
  letI := Fintype.ofFinite G
  letI : Fintype (MulAction.orbit G x) :=
    (Set.finite_range fun g : G => g • x).fintype
  letI := Fintype.ofFinite (MulAction.stabilizer G x)
  have hcard_stabilizer : Fintype.card (MulAction.stabilizer G x) = 1 := by
    rw [Fintype.card_eq_one_iff]
    refine ⟨⟨1, by simp⟩, ?_⟩
    intro g
    apply Subtype.ext
    have hg : (g : G) ∈ (⊥ : Subgroup G) := by
      rw [← hstab]
      exact g.property
    simpa using hg
  have horbit :=
    MulAction.card_orbit_mul_card_stabilizer_eq_card_group G x
  simpa [Nat.card_eq_fintype_card, hcard_stabilizer] using horbit

/-- A point fixed by no nonidentity element has an orbit of size `|G|`. -/
theorem natCard_orbit_eq_natCard_of_smul_eq_imp_eq_one
    [Finite G] (x : X) (hfree : ∀ g : G, g • x = x -> g = 1) :
    Nat.card (MulAction.orbit G x) = Nat.card G :=
  natCard_orbit_eq_natCard_of_stabilizer_eq_bot x
    (stabilizer_eq_bot_of_smul_eq_imp_eq_one x hfree)

end Submission.OddOrder.MathlibSupport
