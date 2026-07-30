import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Submission.OddOrder.MathlibSupport.FiniteSchurField
import Submission.OddOrder.MathlibSupport.IrreducibleCenterCharacter

/-!
Primitive central-character values for faithful representations of
extraspecial `p`-groups.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Finite G]
variable [AddCommGroup V] [Module k V]
variable {p : ℕ} [Fact p.Prime]

namespace IsExtraspecial

/-- Every central-character value has `p`th power one. -/
theorem schurCenterCharacter_pow_prime (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) (rho : Representation k G V)
    (z : Subgroup.center G) : schurCenterCharacter rho z ^ p = 1 := by
  rw [← map_pow, hG.center_pow_prime hpG z, map_one]

/-- In a faithful representation, the value at a nonidentity central element
has order exactly `p`. -/
theorem orderOf_schurCenterCharacter_eq_prime (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) (rho : Representation k G V)
    (hrho : Function.Injective rho) {z : Subgroup.center G} (hz : z ≠ 1) :
    orderOf (schurCenterCharacter rho z) = p := by
  apply orderOf_eq_prime (hG.schurCenterCharacter_pow_prime hpG rho z)
  intro hvalue
  apply hz
  apply schurCenterCharacter_injective_of_injective rho hrho
  simpa using hvalue

/-- Over the finite Schur field of an irreducible representation, every
nonidentity central value is a primitive `p`th root. -/
theorem schurCenterCharacter_isPrimitiveRoot (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) (rho : Representation k G V)
    [Representation.IsIrreducible rho] [Finite V]
    (hrho : Function.Injective rho) {z : Subgroup.center G} (hz : z ≠ 1) :
    letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
    IsPrimitiveRoot (schurCenterCharacter rho z) p := by
  letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
  rw [IsPrimitiveRoot.iff_orderOf]
  exact hG.orderOf_schurCenterCharacter_eq_prime hpG rho hrho hz

/-- A faithful irreducible representation of an extraspecial `p`-group has a
primitive `p`th root among its central Schur-character values. -/
theorem exists_primitive_schurCenterCharacter (hG : IsExtraspecial G)
    (hpG : IsPGroup p G) (rho : Representation k G V)
    [Representation.IsIrreducible rho] [Finite V]
    (hrho : Function.Injective rho) :
    letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
    ∃ z : Subgroup.center G,
      IsPrimitiveRoot (schurCenterCharacter rho z) p := by
  letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
  letI : Nontrivial (Subgroup.center G) :=
    (Subgroup.nontrivial_iff_ne_bot _).mpr hG.center_ne_bot
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center G)
  exact ⟨z, hG.schurCenterCharacter_isPrimitiveRoot hpG rho hrho hz⟩

end IsExtraspecial

end Submission.OddOrder.MathlibSupport
