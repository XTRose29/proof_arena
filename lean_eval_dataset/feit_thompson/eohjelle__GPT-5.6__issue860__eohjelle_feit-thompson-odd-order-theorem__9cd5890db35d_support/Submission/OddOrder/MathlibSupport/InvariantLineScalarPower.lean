import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Submission.OddOrder.MathlibSupport.InvariantLineScalar

/-!
Power relations for scalar actions on invariant lines.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra

variable {F H V : Type*} [Field F] [Group H]
  [AddCommGroup V] [Module F V]

/-- The representation induced on an invariant monoid-algebra submodule. -/
noncomputable def invariantSubmoduleRepresentation
    (rho : Representation F H V) (m : Submodule F[H] rho.asModule) :
    Representation F H (m.restrictScalars F) :=
  (Algebra.lsmul F F (m.restrictScalars F)).toMonoidHom.comp
    (MonoidAlgebra.of F H)

@[simp]
theorem invariantSubmoduleRepresentation_apply
    (rho : Representation F H V) (m : Submodule F[H] rho.asModule)
    (h : H) :
    invariantSubmoduleRepresentation rho m h = invariantLineAction rho m h :=
  rfl

/-- If an element has exponent dividing `n`, then its scalar on an invariant
line also has exponent dividing `n`. -/
theorem invariantLineScalar_pow_eq_one
    (rho : Representation F H V) (m : Submodule F[H] rho.asModule)
    (hm : Module.finrank F (m.restrictScalars F) = 1)
    (h : H) (n : ℕ) (hpow : h ^ n = 1) (a : F)
    (ha : invariantLineAction rho m h = a • LinearMap.id) :
    a ^ n = 1 := by
  letI : Nontrivial (m.restrictScalars F) :=
    Module.nontrivial_of_finrank_eq_succ hm
  have haction :
      invariantLineAction rho m h ^ n =
        invariantLineAction rho m (h ^ n) := by
    simpa using
      (map_pow (invariantSubmoduleRepresentation rho m) h n).symm
  have hone : invariantLineAction rho m (1 : H) =
      (1 : Module.End F (m.restrictScalars F)) := by
    exact map_one (invariantSubmoduleRepresentation rho m)
  rw [ha, hpow, hone] at haction
  obtain ⟨x, hx⟩ := exists_ne (0 : m.restrictScalars F)
  have hxscalar := LinearMap.congr_fun haction x
  simp only [smul_pow, Module.End.id_pow, LinearMap.smul_apply,
    Module.End.one_apply] at hxscalar
  change a ^ n • x = x at hxscalar
  apply smul_left_injective F hx
  simpa only [one_smul] using hxscalar

end Submission.OddOrder.MathlibSupport
