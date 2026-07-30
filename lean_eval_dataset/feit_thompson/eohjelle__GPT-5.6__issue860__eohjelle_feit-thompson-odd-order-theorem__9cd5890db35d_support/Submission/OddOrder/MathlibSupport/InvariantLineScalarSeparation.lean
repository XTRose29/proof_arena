import Submission.OddOrder.MathlibSupport.ComplementarySubspaceIdentity
import Submission.OddOrder.MathlibSupport.InvariantLineScalarPower
import Submission.OddOrder.MathlibSupport.RepresentationLineDeterminant

/-!
Distinct scalar actions on complementary invariant lines.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {F H V : Type*} [Field F] [Group H]
  [AddCommGroup V] [Module F V]

/-- An element whose square and an odd power are both one is itself one. -/
theorem eq_one_of_mul_self_eq_one_of_odd_pow_eq_one
    (a : F) {n : ℕ} (hn : Odd n)
    (hsq : a * a = 1) (hpow : a ^ n = 1) :
    a = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have haexp : a ^ (2 * k + 1) = a := by
    rw [pow_add, pow_one, pow_mul, pow_two, hsq]
    simp
  exact haexp.symm.trans hpow

/-- For a faithful representation, a nonidentity odd-order element cannot act
by the same scalar on two complementary invariant lines when the product of
the scalars is one. -/
theorem invariantLineScalars_ne_of_odd
    (rho : Representation F H V) (hrho : Function.Injective rho)
    (m n : Submodule F[H] rho.asModule) (hmn : IsCompl m n)
    (h : H) (hh : h ≠ 1) {k : ℕ} (hkodd : Odd k) (hkpow : h ^ k = 1)
    (a b : F)
    (hma : invariantLineAction rho m h = a • LinearMap.id)
    (hna : invariantLineAction rho n h = b • LinearMap.id)
    (hmdim : Module.finrank F (m.restrictScalars F) = 1)
    (hab : a * b = 1) :
    a ≠ b := by
  intro heq
  have hapow : a ^ k = 1 :=
    invariantLineScalar_pow_eq_one rho m hmdim h k hkpow a hma
  have haa : a * a = 1 := by simpa [← heq] using hab
  have haone : a = 1 :=
    eq_one_of_mul_self_eq_one_of_odd_pow_eq_one a hkodd haa hapow
  have hbone : b = 1 := heq.symm.trans haone
  have hmaId : invariantLineAction rho m h = LinearMap.id := by
    simpa [haone] using hma
  have hnaId : invariantLineAction rho n h = LinearMap.id := by
    simpa [hbone] using hna
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
  have hfId : f = LinearMap.id :=
    eq_id_of_restrict_eq_id_of_isCompl
      (m.restrictScalars F) (n.restrictScalars F) hmnF f hm hn
      (hfm.trans hmaId) (hfn.trans hnaId)
  have hrhoh : rho h = (1 : Module.End F V) := by
    apply LinearMap.ext
    intro v
    let x : rho.asModule := rho.asModuleEquiv.symm v
    have hx := LinearMap.congr_fun hfId x
    have hx' := congrArg rho.asModuleEquiv hx
    simpa [f, x] using hx'
  apply hh
  apply hrho
  simpa using hrhoh

end Submission.OddOrder.MathlibSupport
