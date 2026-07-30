import Mathlib.Algebra.Ring.Commute
import Mathlib.RepresentationTheory.Basic

/-!
The subgroup centralizing a fixed endomorphism under a representation.
-/

namespace Submission.OddOrder.MathlibSupport

variable {k G V : Type*} [Semiring k] [Group G]
variable [AddCommMonoid V] [Module k V]

theorem commute_representation_inv
    (rho : Representation k G V) (A : Module.End k V) {g : G}
    (hg : Commute (rho g) A) : Commute (rho g⁻¹) A := by
  rw [commute_iff_eq] at hg ⊢
  have hmul : rho g * rho g⁻¹ = 1 := by
    rw [← map_mul]
    simp
  have hinvMul : rho g⁻¹ * rho g = 1 := by
    rw [← map_mul]
    simp
  calc
    rho g⁻¹ * A = (rho g⁻¹ * A) * (rho g * rho g⁻¹) := by
      rw [hmul, mul_one]
    _ = rho g⁻¹ * (A * rho g) * rho g⁻¹ := by
      simp only [mul_assoc]
    _ = rho g⁻¹ * (rho g * A) * rho g⁻¹ := by rw [← hg]
    _ = (rho g⁻¹ * rho g) * (A * rho g⁻¹) := by
      simp only [mul_assoc]
    _ = A * rho g⁻¹ := by rw [hinvMul, one_mul]

/-- Elements whose representation images commute with `A`. -/
def representationCentralizerSubgroup
    (rho : Representation k G V) (A : Module.End k V) : Subgroup G where
  carrier := {g | Commute (rho g) A}
  one_mem' := by
    change Commute (rho 1) A
    rw [map_one]
    exact Commute.one_left A
  mul_mem' := by
    intro x y hx hy
    change Commute (rho (x * y)) A
    rw [map_mul]
    exact hx.mul_left hy
  inv_mem' := by
    intro x hx
    change Commute (rho x⁻¹) A
    exact commute_representation_inv rho A hx

@[simp]
theorem mem_representationCentralizerSubgroup
    (rho : Representation k G V) (A : Module.End k V) (g : G) :
    g ∈ representationCentralizerSubgroup rho A ↔ Commute (rho g) A :=
  Iff.rfl

end Submission.OddOrder.MathlibSupport
