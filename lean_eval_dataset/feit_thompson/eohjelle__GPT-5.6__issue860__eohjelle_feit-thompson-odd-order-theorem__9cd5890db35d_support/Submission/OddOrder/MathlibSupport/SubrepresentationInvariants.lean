import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RepresentationTheory.Subrepresentation

/-!
Fixed spaces of subrepresentations and prime-order kernel intersections.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- A zero fixed space remains zero after restricting the representation to
an invariant subspace. -/
theorem subrepresentation_invariants_eq_bot
    (rho : Representation k G V) (R : Subgroup G)
    (U : Subrepresentation rho)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥) :
    Representation.invariants
      (U.toRepresentation.comp R.subtype :
        Representation k R U.toSubmodule) = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  change x = 0
  apply Subtype.ext
  have hxambient : (x : V) ∈ Representation.invariants
      (rho.comp R.subtype : Representation k R V) := by
    rw [Representation.mem_invariants]
    intro r
    exact congrArg Subtype.val
      ((Representation.mem_invariants _ _).mp hx r)
  have hxzero : (x : V) = 0 := by
    have hxbot : (x : V) ∈ (⊥ : Submodule k V) := by
      rw [← hfix]
      exact hxambient
    simpa using hxbot
  exact hxzero

/-- If a prime-order subgroup has zero fixed space, it intersects the
representation kernel trivially. -/
theorem representation_ker_disjoint_prime_subgroup_of_invariants_eq_bot
    [Nontrivial V]
    (rho : Representation k G V) (R : Subgroup G)
    (hRprime : (Nat.card R).Prime)
    (hfix : Representation.invariants
      (rho.comp R.subtype : Representation k R V) = ⊥) :
    Disjoint rho.ker R := by
  let I : Subgroup R := rho.ker.comap R.subtype
  letI : Fact (Nat.card R).Prime := ⟨hRprime⟩
  rcases I.eq_bot_or_eq_top_of_prime_card with hI | hI
  · rw [disjoint_iff_inf_le]
    intro g hg
    apply Subgroup.mem_bot.mpr
    have hgI : (⟨g, hg.2⟩ : R) ∈ I := hg.1
    have hgone : (⟨g, hg.2⟩ : R) = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hI]
      exact hgI
    exact congrArg Subtype.val hgone
  · have hRker : R ≤ rho.ker := by
      intro r hr
      have hrI : (⟨r, hr⟩ : R) ∈ I := by
        rw [hI]
        trivial
      exact hrI
    letI : Representation.IsTrivial
        (rho.comp R.subtype : Representation k R V) :=
      { out := fun r ↦ MonoidHom.mem_ker.mp (hRker r.property) }
    have htop : Representation.invariants
        (rho.comp R.subtype : Representation k R V) = ⊤ :=
      Representation.invariants_eq_top _
    exfalso
    exact (bot_ne_top : (⊥ : Submodule k V) ≠ ⊤) (hfix.symm.trans htop)

end Submission.OddOrder.MathlibSupport
