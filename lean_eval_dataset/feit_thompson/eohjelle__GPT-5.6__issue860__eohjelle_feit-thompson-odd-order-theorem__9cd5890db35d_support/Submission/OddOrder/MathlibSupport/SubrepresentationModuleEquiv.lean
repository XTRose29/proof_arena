import Mathlib.RepresentationTheory.Irreducible
import Submission.OddOrder.MathlibSupport.RepresentationModuleEquiv

/-!
The module of a subrepresentation agrees with the corresponding submodule of
the ambient representation module.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- The module attached to the representation on a subrepresentation is
linearly equivalent over the monoid algebra to the corresponding ambient
submodule. -/
noncomputable def subrepresentationModuleEquiv
    (rho : Representation k G V) (U : Subrepresentation rho) :
    U.toRepresentation.asModule ≃ₗ[k[G]] U.asSubmodule where
  toFun x :=
    let u := U.toRepresentation.asModuleEquiv x
    ⟨u.1, u.2⟩
  invFun x := U.toRepresentation.asModuleEquiv.symm ⟨x.1, x.2⟩
  left_inv x := by
    apply U.toRepresentation.asModuleEquiv.injective
    rfl
  right_inv x := by
    apply Subtype.ext
    rfl
  map_add' x y := by
    apply Subtype.ext
    rfl
  map_smul' c x := by
    apply Subtype.ext
    change (U.toRepresentation.asModuleEquiv (c • x) : V) =
      rho.asModuleEquiv (c • rho.asModuleEquiv.symm
        (U.toRepresentation.asModuleEquiv x : V))
    rw [rho.asModuleEquiv_map_smul, U.toRepresentation.asModuleEquiv_map_smul]
    simp only [LinearEquiv.apply_symm_apply]
    induction c using MonoidAlgebra.induction_linear with
    | zero => simp
    | add a b ha hb => simp [map_add, ha, hb]
    | single g a =>
        simp only [Representation.asAlgebraHom_single]
        rfl

/-- Irreducibility of a subrepresentation is simplicity of its corresponding
ambient monoid-algebra submodule. -/
theorem irreducible_toRepresentation_iff_isSimpleModule_asSubmodule
    (rho : Representation k G V) (U : Subrepresentation rho) :
    Representation.IsIrreducible U.toRepresentation ↔
      IsSimpleModule k[G] U.asSubmodule := by
  rw [Representation.irreducible_iff_isSimpleModule_asModule]
  exact (subrepresentationModuleEquiv rho U).isSimpleModule_iff

/-- Equivalence of two subrepresentations is equivalent to module equivalence
of their corresponding ambient submodules. -/
theorem nonempty_subrepresentationEquiv_iff_nonempty_submoduleEquiv
    (rho : Representation k G V) (U W : Subrepresentation rho) :
    Nonempty (Representation.Equiv U.toRepresentation W.toRepresentation) ↔
      Nonempty (U.asSubmodule ≃ₗ[k[G]] W.asSubmodule) := by
  constructor
  · rintro ⟨e⟩
    exact ⟨(subrepresentationModuleEquiv rho U).symm |>.trans
      (representationEquivLinearEquivAsModule e) |>.trans
      (subrepresentationModuleEquiv rho W)⟩
  · rintro ⟨e⟩
    apply nonempty_representationEquiv_iff_nonempty_linearEquivAsModule.mpr
    exact ⟨(subrepresentationModuleEquiv rho U) |>.trans e |>.trans
      (subrepresentationModuleEquiv rho W).symm⟩

end Submission.OddOrder.MathlibSupport
