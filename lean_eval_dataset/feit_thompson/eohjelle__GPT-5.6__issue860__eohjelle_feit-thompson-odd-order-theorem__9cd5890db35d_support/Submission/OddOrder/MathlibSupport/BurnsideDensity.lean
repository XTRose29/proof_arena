import Mathlib.RepresentationTheory.AlgebraRepresentation.Basic
import Mathlib.RingTheory.SimpleModule.Basic

/-!
Burnside's density theorem for finite-dimensional simple modules over an
algebraically closed field.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {R : Type v} {M : Type w}
variable [Field k] [Ring R] [Algebra k R]
variable [AddCommGroup M] [Module k M] [Module R M] [IsScalarTower k R M]
variable [IsSimpleModule R M] [FiniteDimensional k M] [IsAlgClosed k]

/-- The action of an algebra on a finite-dimensional simple module over an
algebraically closed field realizes every linear endomorphism. -/
theorem isSimpleModule_toModuleEnd_surjective :
    Function.Surjective (Module.toModuleEnd k (S := R) M) := by
  let D := Module.End R M
  have hscalar : Function.Bijective (algebraMap k D) :=
    IsSimpleModule.algebraMap_end_bijective_of_isAlgClosed k
  letI : Module.Finite D M :=
    Module.Finite.of_restrictScalars_finite k D M
  intro f
  let fD : Module.End D M :=
    { toFun := f
      map_add' := f.map_add'
      map_smul' := by
        intro d m
        obtain ⟨a, rfl⟩ := hscalar.2 d
        simp }
  obtain ⟨r, hr⟩ :=
    Module.Finite.toModuleEnd_moduleEnd_surjective (R := R) (M := M) fD
  refine ⟨r, ?_⟩
  ext m
  exact DFunLike.congr_fun hr m

end Submission.OddOrder.MathlibSupport
