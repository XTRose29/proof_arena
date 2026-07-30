import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
import Submission.OddOrder.MathlibSupport.IrreducibleCenterCharacter

/-!
Faithfulness criteria detected by the prime-order center of an extraspecial
group.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {A : Type u} {B : Type v}

/-- A homomorphism out of a finite group of prime order is injective exactly
when it is not the trivial homomorphism. -/
theorem monoidHom_injective_iff_ne_one_of_prime_card
    [Group A] [Finite A] [Group B] [Fact (Nat.card A).Prime]
    (f : A →* B) : Function.Injective f ↔ f ≠ 1 := by
  letI : Nontrivial A :=
    Finite.one_lt_card_iff_nontrivial.mp
      (Fact.out : (Nat.card A).Prime).one_lt
  constructor
  · intro hinjective htrivial
    have hbot : f.ker = ⊥ := f.ker_eq_bot_iff.mpr hinjective
    have htop : f.ker = ⊤ := f.ker_eq_top_iff.mpr htrivial
    exact bot_ne_top (hbot.symm.trans htop)
  · intro hnontrivial
    rw [← f.ker_eq_bot_iff]
    exact f.ker.eq_bot_or_eq_top_of_prime_card.resolve_right fun htop ↦
      hnontrivial (f.ker_eq_top_iff.mp htop)

/-- A homomorphism is nontrivial exactly when one of its values is
nonidentity. -/
theorem monoidHom_ne_one_iff_exists_apply_ne_one
    [Group A] [Group B] (f : A →* B) :
    f ≠ 1 ↔ ∃ a : A, f a ≠ 1 := by
  constructor
  · intro hnontrivial
    contrapose! hnontrivial
    ext a
    simpa using hnontrivial a
  · rintro ⟨a, ha⟩ htrivial
    apply ha
    rw [htrivial]
    rfl

variable {k : Type u} {G : Type v} {V : Type w}
variable [CommRing k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V]
variable {p : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- For an extraspecial `p`-group, a representation is faithful exactly when
its Schur center character is nontrivial. -/
theorem representation_injective_iff_schurCenterCharacter_ne_one
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (rho : Representation k G V) :
    Function.Injective rho ↔ schurCenterCharacter rho ≠ 1 := by
  letI : Fact (Nat.card (Subgroup.center G)).Prime :=
    ⟨hG.center_card_prime⟩
  rw [IsPGroup.representation_injective_iff_schurCenterCharacter hpG rho,
    monoidHom_injective_iff_ne_one_of_prime_card]

/-- Equivalently, faithfulness is witnessed by one nonidentity central
Schur-character value. -/
theorem representation_injective_iff_exists_schurCenterCharacter_ne_one
    (hG : IsExtraspecial G) (hpG : IsPGroup p G)
    (rho : Representation k G V) :
    Function.Injective rho ↔
      ∃ z : Subgroup.center G, schurCenterCharacter rho z ≠ 1 := by
  rw [hG.representation_injective_iff_schurCenterCharacter_ne_one hpG rho,
    monoidHom_ne_one_iff_exists_apply_ne_one]

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
