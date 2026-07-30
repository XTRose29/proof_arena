import Submission.OddOrder.MathlibSupport.ComplementaryLineDeterminant
import Submission.OddOrder.MathlibSupport.InvariantLineScalar

/-!
Determinants from scalar actions on invariant representation lines.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {F H V : Type*} [Field F] [Group H]
  [AddCommGroup V] [Module F V]

/-- The action of a represented group element on the monoid-algebra module. -/
noncomputable def asModuleGroupAction
    (rho : Representation F H V) (h : H) :
    Module.End F rho.asModule :=
  Algebra.lsmul F F rho.asModule (MonoidAlgebra.of F H h)

@[simp]
theorem asModuleEquiv_asModuleGroupAction
    (rho : Representation F H V) (h : H) (x : rho.asModule) :
    rho.asModuleEquiv (asModuleGroupAction rho h x) =
      rho h (rho.asModuleEquiv x) := by
  change rho.asModuleEquiv (MonoidAlgebra.of F H h • x) = _
  rw [Representation.asModuleEquiv_map_smul]
  exact LinearMap.congr_fun (Representation.asAlgebraHom_of rho h)
    (rho.asModuleEquiv x)

/-- Passing between a representation and its monoid-algebra module does not
change the determinant of a represented group element. -/
theorem det_asModuleGroupAction
    [FiniteDimensional F V] (rho : Representation F H V) (h : H) :
    (asModuleGroupAction rho h).det = (rho h).det := by
  rw [← LinearMap.det_conj (asModuleGroupAction rho h) rho.asModuleEquiv]
  congr 1
  ext x
  simp

/-- If a represented element acts by scalars on two complementary invariant
lines, then its determinant is the product of those scalars. -/
theorem representation_det_eq_mul_of_complementary_invariant_lines
    [FiniteDimensional F V] (rho : Representation F H V)
    (m n : Submodule F[H] rho.asModule) (hmn : IsCompl m n)
    (h : H) (a b : F)
    (hma : invariantLineAction rho m h = a • LinearMap.id)
    (hna : invariantLineAction rho n h = b • LinearMap.id)
    (hmdim : Module.finrank F (m.restrictScalars F) = 1)
    (hndim : Module.finrank F (n.restrictScalars F) = 1) :
    (rho h).det = a * b := by
  let f := asModuleGroupAction rho h
  have hmnF : IsCompl (m.restrictScalars F) (n.restrictScalars F) :=
    (Submodule.isCompl_restrictScalars_iff F).mpr hmn
  have hm : m.restrictScalars F ≤ (m.restrictScalars F).comap f := by
    intro x hx
    exact m.smul_mem (MonoidAlgebra.of F H h) hx
  have hn : n.restrictScalars F ≤ (n.restrictScalars F).comap f := by
    intro x hx
    exact n.smul_mem (MonoidAlgebra.of F H h) hx
  have hfm : f.restrict hm = invariantLineAction rho m h := by
    ext x
    rfl
  have hfn : f.restrict hn = invariantLineAction rho n h := by
    ext x
    rfl
  rw [← det_asModuleGroupAction rho h]
  exact det_eq_mul_of_complementary_lines
    (m.restrictScalars F) (n.restrictScalars F) hmnF f hm hn a b
    (hfm.trans hma) (hfn.trans hna) hmdim hndim

end Submission.OddOrder.MathlibSupport
