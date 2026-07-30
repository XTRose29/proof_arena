import Mathlib.LinearAlgebra.Dimension.Finrank
import Submission.OddOrder.MathlibSupport.RepresentationDeterminant
import Submission.OddOrder.MathlibSupport.RepresentationLineDeterminant

/-!
Translating invariant subspaces for a normal subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {F G V : Type*} [Field F] [Group G]
  [AddCommGroup V] [Module F V]

/-- Restriction of a representation to a subgroup. -/
def subgroupRepresentation
    (rho : Representation F G V) (N : Subgroup G) :
    Representation F N V :=
  rho.comp N.subtype

/-- An ambient represented group element acting on the module underlying a
subgroup restriction. -/
def subgroupModuleAmbientLinearEquiv
    (rho : Representation F G V) (N : Subgroup G) (y : G) :
    (subgroupRepresentation rho N).asModule ≃ₗ[F]
      (subgroupRepresentation rho N).asModule :=
  (subgroupRepresentation rho N).asModuleEquiv |>.trans
    (representationLinearEquiv rho y) |>.trans
    (subgroupRepresentation rho N).asModuleEquiv.symm

@[simp]
theorem subgroupModuleAmbientLinearEquiv_apply
    (rho : Representation F G V) (N : Subgroup G) (y : G)
    (u : (subgroupRepresentation rho N).asModule) :
    subgroupModuleAmbientLinearEquiv rho N y u =
      (subgroupRepresentation rho N).asModuleEquiv.symm
        (rho y ((subgroupRepresentation rho N).asModuleEquiv u)) :=
  rfl

@[simp]
theorem subgroupModuleAmbientLinearEquiv_toLinearMap_apply
    (rho : Representation F G V) (N : Subgroup G) (y : G)
    (u : (subgroupRepresentation rho N).asModule) :
    (subgroupModuleAmbientLinearEquiv rho N y).toLinearMap u =
      (subgroupRepresentation rho N).asModuleEquiv.symm
        (rho y ((subgroupRepresentation rho N).asModuleEquiv u)) :=
  rfl

/-- Translate the underlying `F`-subspace of an `N`-invariant submodule by
an ambient represented group element. -/
noncomputable def translateRestrictedInvariantSubspace
    (rho : Representation F G V) (N : Subgroup G)
    (m : Submodule F[N] (subgroupRepresentation rho N).asModule) (y : G) :
    Submodule F (subgroupRepresentation rho N).asModule :=
  (m.restrictScalars F).map
    (subgroupModuleAmbientLinearEquiv rho N y).toLinearMap

/-- Translation by a represented group element preserves finrank. -/
theorem finrank_translateRestrictedInvariantSubspace
    (rho : Representation F G V) (N : Subgroup G)
    (m : Submodule F[N] (subgroupRepresentation rho N).asModule) (y : G) :
    Module.finrank F (translateRestrictedInvariantSubspace rho N m y) =
      Module.finrank F (m.restrictScalars F) :=
  (subgroupModuleAmbientLinearEquiv rho N y).finrank_map_eq
    (m.restrictScalars F)

/-- If `N` is normal, every ambient translate of an `N`-invariant subspace
is still invariant under each element of `N`. -/
theorem translateRestrictedInvariantSubspace_le_comap
    (rho : Representation F G V) (N : Subgroup G) (hN : N.Normal)
    (m : Submodule F[N] (subgroupRepresentation rho N).asModule)
    (y : G) (x : N) :
    translateRestrictedInvariantSubspace rho N m y ≤
      (translateRestrictedInvariantSubspace rho N m y).comap
        (asModuleGroupAction (subgroupRepresentation rho N) x) := by
  rintro _ ⟨u, hu, rfl⟩
  let z : N := ⟨y⁻¹ * (x : G) * y, hN.conj_mem' x x.property y⟩
  have hzu : asModuleGroupAction (subgroupRepresentation rho N) z u ∈ m := by
    change MonoidAlgebra.of F N z • u ∈ m
    exact m.smul_mem _ hu
  refine ⟨asModuleGroupAction (subgroupRepresentation rho N) z u, hzu, ?_⟩
  apply (subgroupRepresentation rho N).asModuleEquiv.injective
  simp only [subgroupModuleAmbientLinearEquiv_toLinearMap_apply,
    LinearEquiv.apply_symm_apply, asModuleEquiv_asModuleGroupAction]
  change rho y (rho (y⁻¹ * (x : G) * y) u) =
    rho (x : G) (rho y u)
  simp only [← Module.End.mul_apply, ← map_mul]
  congr 2
  group

end Submission.OddOrder.MathlibSupport
