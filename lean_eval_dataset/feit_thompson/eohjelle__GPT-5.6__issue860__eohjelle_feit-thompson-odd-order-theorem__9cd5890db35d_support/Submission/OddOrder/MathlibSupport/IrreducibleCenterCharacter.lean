import Mathlib.RepresentationTheory.Intertwining
import Submission.OddOrder.MathlibSupport.ExtraspecialNormal

/-!
The central character of a representation, valued in its group-algebra
endomorphism ring.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [CommRing k] [Group G] [AddCommGroup V] [Module k V]

/-- A central group element, acting as an endomorphism of the group-algebra
module associated to a representation. -/
noncomputable def centralActionEnd (rho : Representation k G V)
    (z : Subgroup.center G) : Module.End k[G] rho.asModule :=
  Representation.IntertwiningMap.equivLinearMapAsModule rho rho
    (Representation.IntertwiningMap.centralMul rho z (by
      rw [Submonoid.mem_center_iff]
      exact Subgroup.mem_center_iff.mp z.property))

@[simp]
theorem centralActionEnd_apply (rho : Representation k G V)
    (z : Subgroup.center G) (x : rho.asModule) :
    rho.asModuleEquiv (centralActionEnd rho z x) =
      rho z (rho.asModuleEquiv x) :=
  rfl

/-- The invertible central action associated to a central group element. -/
noncomputable def centralActionUnit (rho : Representation k G V)
    (z : Subgroup.center G) : (Module.End k[G] rho.asModule)ˣ where
  val := centralActionEnd rho z
  inv := centralActionEnd rho z⁻¹
  val_inv := by
    apply LinearMap.ext
    intro x
    apply rho.asModuleEquiv.injective
    simp [centralActionEnd_apply]
  inv_val := by
    apply LinearMap.ext
    intro x
    apply rho.asModuleEquiv.injective
    simp [centralActionEnd_apply]

/-- The central character of a representation, valued in the units of its
group-algebra endomorphism ring. -/
noncomputable def schurCenterCharacter (rho : Representation k G V) :
    Subgroup.center G →* (Module.End k[G] rho.asModule)ˣ where
  toFun := centralActionUnit rho
  map_one' := by
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply rho.asModuleEquiv.injective
    change rho.asModuleEquiv (centralActionEnd rho 1 x) =
      rho.asModuleEquiv x
    rw [centralActionEnd_apply]
    simp
  map_mul' := by
    intro z w
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply rho.asModuleEquiv.injective
    change rho.asModuleEquiv (centralActionEnd rho (z * w) x) =
      rho.asModuleEquiv
        (centralActionEnd rho z (centralActionEnd rho w x))
    rw [centralActionEnd_apply, centralActionEnd_apply,
      centralActionEnd_apply]
    change rho ((z : G) * (w : G)) (rho.asModuleEquiv x) =
      rho z (rho w (rho.asModuleEquiv x))
    rw [rho.map_mul]
    rfl

@[simp]
theorem schurCenterCharacter_val_apply (rho : Representation k G V)
    (z : Subgroup.center G) (x : rho.asModule) :
    rho.asModuleEquiv
        ((schurCenterCharacter rho z : Module.End k[G] rho.asModule) x) =
      rho z (rho.asModuleEquiv x) :=
  rfl

/-- A faithful representation has injective central character. -/
theorem schurCenterCharacter_injective_of_injective
    (rho : Representation k G V) (hrho : Function.Injective rho) :
    Function.Injective (schurCenterCharacter rho) := by
  intro z w hzw
  apply Subtype.ext
  apply hrho
  apply DFunLike.ext _ _
  intro x
  have hx := congrArg
    (fun u : (Module.End k[G] rho.asModule)ˣ ↦
      rho.asModuleEquiv
        ((u : Module.End k[G] rho.asModule) (rho.asModuleEquiv.symm x))) hzw
  simpa using hx

/-- For a finite `p`-group, faithfulness is equivalent to injectivity of the
central character. -/
theorem IsPGroup.representation_injective_iff_schurCenterCharacter
    [Finite G] {p : ℕ} [Fact p.Prime] (hpG : IsPGroup p G)
    (rho : Representation k G V) :
    Function.Injective rho ↔
      Function.Injective (schurCenterCharacter rho) := by
  constructor
  · exact schurCenterCharacter_injective_of_injective rho
  · intro hcenter
    apply (IsPGroup.monoidHom_injective_iff_center_restrict hpG rho).mpr
    intro z w hzw
    apply hcenter
    apply Units.ext
    apply LinearMap.ext
    intro x
    apply rho.asModuleEquiv.injective
    simp only [schurCenterCharacter_val_apply]
    exact DFunLike.congr_fun hzw (rho.asModuleEquiv x)

end Submission.OddOrder.MathlibSupport
