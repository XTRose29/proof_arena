import Mathlib.RepresentationTheory.Character
import Submission.OddOrder.MathlibSupport.IrreducibleCenterCharacter

/-!
Scalar central characters for irreducible representations over algebraically
closed fields.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [IsAlgClosed k] [Group G]
variable [AddCommGroup V] [Module k V] [FiniteDimensional k V]

/-- Schur's lemma identifies the intertwining algebra of an irreducible
representation over an algebraically closed field with the base field. -/
noncomputable def irreducibleIntertwiningScalarEquiv
    (rho : Representation k G V) [Representation.IsIrreducible rho] :
    Representation.IntertwiningMap rho rho ≃ₐ[k] k :=
  (AlgEquiv.ofBijective
    (Algebra.ofId k (Representation.IntertwiningMap rho rho))
    Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed).symm

/-- The corresponding scalar identification of group-algebra endomorphisms. -/
noncomputable def irreducibleEndScalarEquiv
    (rho : Representation k G V) [Representation.IsIrreducible rho] :
    Module.End k[G] rho.asModule ≃ₐ[k] k :=
  (Representation.IntertwiningMap.equivAlgEnd rho).symm.trans
    (irreducibleIntertwiningScalarEquiv rho)

/-- The scalar-valued Schur center character of an irreducible
representation. -/
noncomputable def schurCenterScalarCharacter
    (rho : Representation k G V) [Representation.IsIrreducible rho] :
    Subgroup.center G →* kˣ :=
  (Units.map (irreducibleEndScalarEquiv rho).toMonoidHom).comp
    (schurCenterCharacter rho)

variable (rho : Representation k G V) [Representation.IsIrreducible rho]

/-- Mapping a scalar center-character value back into the endomorphism algebra
recovers the original central action. -/
theorem algebraMap_schurCenterScalarCharacter
    (z : Subgroup.center G) :
    algebraMap k (Module.End k[G] rho.asModule)
        (schurCenterScalarCharacter rho z : k) =
      centralActionEnd rho z := by
  apply (irreducibleEndScalarEquiv rho).injective
  simp [schurCenterScalarCharacter]
  rfl

/-- A central group element acts by its scalar Schur-character value. -/
@[simp]
theorem schurCenterScalarCharacter_smul
    (z : Subgroup.center G) (x : V) :
    rho z x = (schurCenterScalarCharacter rho z : k) • x := by
  have h := congrArg
    (fun f : Module.End k[G] rho.asModule ↦
      rho.asModuleEquiv (f (rho.asModuleEquiv.symm x)))
    (algebraMap_schurCenterScalarCharacter rho z)
  simpa [Representation.IntertwiningMap.algebraMap_apply] using h.symm

/-- On the center, the ordinary character is the representation degree times
the scalar Schur character. -/
theorem character_center_eq_finrank_mul_schurCenterScalarCharacter
    (z : Subgroup.center G) :
    rho.character z =
      (Module.finrank k V : k) * (schurCenterScalarCharacter rho z : k) := by
  have hlinear :
      rho z = (schurCenterScalarCharacter rho z : k) •
        (1 : Module.End k V) := by
    ext x
    simp
  rw [Representation.character, hlinear, map_smul, LinearMap.trace_one]
  ring

/-- Passing from the endomorphism-valued center character to its scalar form
preserves injectivity. -/
theorem schurCenterScalarCharacter_injective_iff :
    Function.Injective (schurCenterScalarCharacter rho) ↔
      Function.Injective (schurCenterCharacter rho) := by
  let hmap : Function.Injective
      (Units.map (irreducibleEndScalarEquiv rho).toMonoidHom) :=
    Units.map_injective (irreducibleEndScalarEquiv rho).injective
  constructor
  · intro hscalar z w hzw
    apply hscalar
    change Units.map (irreducibleEndScalarEquiv rho).toMonoidHom
        (schurCenterCharacter rho z) =
      Units.map (irreducibleEndScalarEquiv rho).toMonoidHom
        (schurCenterCharacter rho w)
    rw [hzw]
  · intro hcenter z w hzw
    apply hcenter
    apply hmap
    exact hzw

/-- For an irreducible representation of a finite `p`-group, faithfulness is
equivalent to injectivity of the scalar center character. -/
theorem IsPGroup.representation_injective_iff_schurCenterScalarCharacter
    [Finite G] {p : ℕ} [Fact p.Prime] (hpG : IsPGroup p G) :
    Function.Injective rho ↔
      Function.Injective (schurCenterScalarCharacter rho) := by
  rw [IsPGroup.representation_injective_iff_schurCenterCharacter hpG rho,
    schurCenterScalarCharacter_injective_iff]

end Submission.OddOrder.MathlibSupport
