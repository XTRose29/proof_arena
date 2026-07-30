import Submission.OddOrder.MathlibSupport.NormalInvariantSubspaceTranslate

/-!
The ambient group action on the module underlying a subgroup restriction.
-/

namespace Submission.OddOrder.MathlibSupport

variable {F G V : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V]

/-- Ambient represented elements act as linear equivalences on the module
underlying any subgroup restriction. -/
def subgroupModuleAmbientLinearEquivHom
    (rho : Representation F G V) (N : Subgroup G) :
    G →* ((subgroupRepresentation rho N).asModule ≃ₗ[F]
      (subgroupRepresentation rho N).asModule) where
  toFun := subgroupModuleAmbientLinearEquiv rho N
  map_one' := by
    apply LinearEquiv.ext
    intro u
    apply (subgroupRepresentation rho N).asModuleEquiv.injective
    simp
  map_mul' y z := by
    apply LinearEquiv.ext
    intro u
    apply (subgroupRepresentation rho N).asModuleEquiv.injective
    simp [subgroupModuleAmbientLinearEquiv]

@[simp]
theorem subgroupModuleAmbientLinearEquivHom_apply
    (rho : Representation F G V) (N : Subgroup G) (y : G) :
    subgroupModuleAmbientLinearEquivHom rho N y =
      subgroupModuleAmbientLinearEquiv rho N y :=
  rfl

end Submission.OddOrder.MathlibSupport
