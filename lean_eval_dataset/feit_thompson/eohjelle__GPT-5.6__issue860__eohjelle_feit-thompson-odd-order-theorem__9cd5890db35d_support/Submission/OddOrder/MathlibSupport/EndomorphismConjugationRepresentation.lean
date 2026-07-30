import Mathlib.RepresentationTheory.Invariants

/-!
The conjugation representation on the endomorphism space of a represented
module.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- Conjugation by `rho g` as a linear endomorphism of `End_k(V)`. -/
def endomorphismConjugationLinearMap
    (rho : Representation k G V) (g : G) :
    Module.End k (Module.End k V) where
  toFun T := rho g * T * rho g⁻¹
  map_add' A B := by
    ext v
    simp [Module.End.mul_apply]
  map_smul' c A := by
    ext v
    simp [Module.End.mul_apply]

/-- The ambient group acts linearly on `End_k(V)` by conjugation through a
representation. -/
def endomorphismConjugationRepresentation
    (rho : Representation k G V) :
    Representation k G (Module.End k V) where
  toFun := endomorphismConjugationLinearMap rho
  map_one' := by
    ext T v
    simp [endomorphismConjugationLinearMap]
  map_mul' g h := by
    ext T v
    simp [endomorphismConjugationLinearMap, Module.End.mul_apply]

@[simp]
theorem endomorphismConjugationRepresentation_apply
    (rho : Representation k G V) (g : G) (T : Module.End k V) :
    endomorphismConjugationRepresentation rho g T =
      rho g * T * rho g⁻¹ := rfl

/-- Scalar endomorphisms are fixed by conjugation. -/
@[simp]
theorem endomorphismConjugationRepresentation_smul_one
    (rho : Representation k G V) (g : G) (c : k) :
    endomorphismConjugationRepresentation rho g
        (c • (1 : Module.End k V)) =
      c • (1 : Module.End k V) := by
  ext v
  simp [endomorphismConjugationRepresentation,
    endomorphismConjugationLinearMap, Module.End.mul_apply]

/-- Fixed points of the conjugation representation are precisely
endomorphisms commuting with every represented group element. -/
theorem mem_endomorphismConjugation_invariants_iff
    (rho : Representation k G V) (T : Module.End k V) :
    T ∈ (endomorphismConjugationRepresentation rho).invariants ↔
      ∀ g : G, Commute T (rho g) := by
  rw [Representation.mem_invariants]
  constructor
  · intro h g
    rw [Commute]
    have hg := h g
    change rho g * T * rho g⁻¹ = T at hg
    calc
      T * rho g = (rho g * T * rho g⁻¹) * rho g := by rw [hg]
      _ = rho g * T := by
        rw [mul_assoc, mul_assoc, ← rho.map_mul]
        simp
  · intro h g
    change rho g * T * rho g⁻¹ = T
    calc
      rho g * T * rho g⁻¹ = T * rho g * rho g⁻¹ := by rw [h g]
      _ = T := by
        rw [mul_assoc, ← rho.map_mul]
        simp

end Submission.OddOrder.MathlibSupport
