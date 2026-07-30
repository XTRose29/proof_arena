import Submission.OddOrder.MathlibSupport.ExtraspecialCommutatorPairing
import Submission.OddOrder.MathlibSupport.IrreducibleCenterScalar

/-!
Vanishing away from the center for faithful irreducible characters of special
groups.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra commutatorElement

universe u v w

variable {G : Type v} [Group G]

namespace IsSpecial

/-- A noncentral element of a special group has a conjugate obtained by
multiplying it by a nonidentity central commutator. -/
theorem exists_conjugate_eq_center_mul_of_not_mem_center
    (hG : IsSpecial G) {x : G} (hx : x ∉ Subgroup.center G) :
    ∃ (y : G) (z : Subgroup.center G),
      z ≠ 1 ∧ MulAut.conj y x = (z : G) * x := by
  classical
  rw [Subgroup.mem_center_iff] at hx
  simp only [not_forall] at hx
  obtain ⟨y, hy⟩ := hx
  let z : Subgroup.center G := hG.commutatorPairing y x
  refine ⟨y, z, ?_, ?_⟩
  · intro hz
    apply hy
    apply commutatorElement_eq_one_iff_commute.mp
    exact congrArg Subtype.val hz
  · exact conj_eq_commutatorElement_mul

variable {k : Type u} {V : Type w}
variable [Field k] [IsAlgClosed k]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- The character of a faithful irreducible representation of a special group
vanishes on every noncentral element. -/
theorem character_eq_zero_of_not_mem_center
    (hG : IsSpecial G) (rho : Representation k G V)
    [Representation.IsIrreducible rho] (hrho : Function.Injective rho)
    {x : G} (hx : x ∉ Subgroup.center G) : rho.character x = 0 := by
  obtain ⟨y, z, hz, hconj⟩ :=
    hG.exists_conjugate_eq_center_mul_of_not_mem_center hx
  have hscalarInjective :
      Function.Injective (schurCenterScalarCharacter rho) :=
    (schurCenterScalarCharacter_injective_iff rho).mpr
      (schurCenterCharacter_injective_of_injective rho hrho)
  have hscalar : (schurCenterScalarCharacter rho z : k) ≠ 1 := by
    intro hvalue
    apply hz
    apply hscalarInjective
    apply Units.ext
    simpa using hvalue
  have hlinear : rho ((z : G) * x) =
      (schurCenterScalarCharacter rho z : k) • rho x := by
    rw [rho.map_mul]
    ext v
    simp
  have hchar_mul : rho.character ((z : G) * x) =
      (schurCenterScalarCharacter rho z : k) * rho.character x := by
    rw [Representation.character, hlinear, map_smul]
    rfl
  have hfixed : rho.character x =
      (schurCenterScalarCharacter rho z : k) * rho.character x := by
    rw [← hchar_mul, ← hconj]
    exact (rho.char_conj x y).symm
  have hfactor :
      (1 - (schurCenterScalarCharacter rho z : k)) * rho.character x = 0 := by
    linear_combination hfixed
  rcases mul_eq_zero.mp hfactor with hcoefficient | hcharacter
  · exact (hscalar (sub_eq_zero.mp hcoefficient).symm).elim
  · exact hcharacter

end IsSpecial

end Submission.OddOrder.MathlibSupport
