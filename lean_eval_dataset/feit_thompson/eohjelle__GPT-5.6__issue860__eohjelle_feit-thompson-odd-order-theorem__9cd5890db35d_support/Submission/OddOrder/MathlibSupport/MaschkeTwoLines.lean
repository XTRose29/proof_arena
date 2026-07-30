import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Submission.OddOrder.MathlibSupport.MaschkeSimpleLine

/-!
Maschke decomposition of a two-dimensional abelian representation into two
invariant lines.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped MonoidAlgebra IsMulCommutative

variable {F H V : Type*} [Field F] [IsAlgClosed F]
  [Group H] [Finite H] [IsMulCommutative H]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]
  [NeZero (Nat.card H : F)]

/-- A two-dimensional representation of a finite abelian group splits as a
complementary pair of invariant one-dimensional subspaces. -/
theorem exists_complementary_simpleLine_finrank_one
    (rho : Representation F H V) (hdim : Module.finrank F V = 2) :
    ∃ m n : Submodule F[H] rho.asModule,
      IsSimpleModule F[H] m ∧ IsCompl m n ∧
        Module.finrank F (m.restrictScalars F) = 1 ∧
        Module.finrank F (n.restrictScalars F) = 1 := by
  obtain ⟨m, hm, hmrank⟩ := exists_simpleSubmodule_finrank_one rho
  letI : IsSemisimpleModule F[H] rho.asModule := by infer_instance
  obtain ⟨n, hmn⟩ := exists_isCompl m
  have hmnF : IsCompl (m.restrictScalars F) (n.restrictScalars F) :=
    (Submodule.isCompl_restrictScalars_iff F).mpr hmn
  have hdimM : Module.finrank F rho.asModule = 2 :=
    rho.asModuleEquiv.finrank_eq.trans hdim
  have hadd :
      Module.finrank F (m.restrictScalars F) +
        Module.finrank F (n.restrictScalars F) = 2 := by
    rw [← hdimM]
    exact Submodule.finrank_add_eq_of_isCompl hmnF
  have hnrank : Module.finrank F (n.restrictScalars F) = 1 := by
    omega
  exact ⟨m, n, hm, hmn, hmrank, hnrank⟩

end Submission.OddOrder.MathlibSupport
