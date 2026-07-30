import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.LinearAlgebra.TensorProduct.Basic
import Mathlib.LinearAlgebra.TensorProduct.Tower
import Mathlib.RepresentationTheory.Basic
import Mathlib.RepresentationTheory.Invariants
import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
import Submission.OddOrder.MathlibSupport.CyclicInvariantKernel

/-!
Scalar extension of representations along field extensions.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped TensorProduct

universe u v w x

variable {F : Type v} {A : Type x} {G : Type u} {V : Type w}
  [Field F] [Field A] [Algebra F A] [Group G]
  [AddCommGroup V] [Module F V]

/-- Extension of scalars of a representation to `A ⊗[F] V`. -/
def representationBaseChange (rho : Representation F G V) :
    Representation A G (A ⊗[F] V) :=
  (Module.End.baseChangeHom F A V).toMonoidHom.comp rho

@[simp]
theorem representationBaseChange_apply
    (rho : Representation F G V) (g : G) :
    representationBaseChange (A := A) rho g = (rho g).baseChange A :=
  rfl

/-- Base change of endomorphisms along a field extension is injective. -/
theorem moduleEnd_baseChangeHom_injective :
    Function.Injective (Module.End.baseChangeHom F A V) := by
  intro f g hfg
  apply LinearMap.ext
  intro v
  have htensor := LinearMap.congr_fun hfg ((1 : A) ⊗ₜ[F] v)
  change f.baseChange A ((1 : A) ⊗ₜ[F] v) =
    g.baseChange A ((1 : A) ⊗ₜ[F] v) at htensor
  simp only [LinearMap.baseChange_tmul] at htensor
  apply sub_eq_zero.mp
  rw [← Module.FaithfullyFlat.one_tmul_eq_zero_iff
    (R := F) (A := A) (M := V)]
  rw [TensorProduct.tmul_sub, htensor, sub_self]

/-- A faithful representation remains faithful after extending scalars. -/
theorem representationBaseChange_injective
    (rho : Representation F G V) (hrho : Function.Injective rho) :
    Function.Injective (representationBaseChange (A := A) rho) := by
  intro g h hgh
  apply hrho
  apply moduleEnd_baseChangeHom_injective (F := F) (A := A)
  exact hgh

/-- Scalar extension preserves finite dimension. -/
theorem finrank_representationBaseChange
    [FiniteDimensional F V] :
    Module.finrank A (A ⊗[F] V) = Module.finrank F V :=
  Module.finrank_baseChange

/-- Extending scalars preserves injectivity of a finite-dimensional linear
endomorphism. -/
theorem linearMap_baseChange_injective_of_injective
    [FiniteDimensional F V] (f : Module.End F V)
    (hf : Function.Injective f) :
    Function.Injective (f.baseChange A) := by
  have hsurjective : Function.Surjective f :=
    LinearMap.surjective_of_injective hf
  let e : V ≃ₗ[F] V := LinearEquiv.ofBijective f ⟨hf, hsurjective⟩
  apply Function.LeftInverse.injective
    (g := e.symm.toLinearMap.baseChange A)
  intro x
  have hleft : e.symm.toLinearMap ∘ₗ f = LinearMap.id := by
    ext v
    simp [e]
  calc
    e.symm.toLinearMap.baseChange A (f.baseChange A x) =
        (e.symm.toLinearMap.baseChange A ∘ₗ f.baseChange A) x := rfl
    _ = ((e.symm.toLinearMap ∘ₗ f).baseChange A) x := by
      rw [LinearMap.baseChange_comp]
    _ = x := by rw [hleft, LinearMap.baseChange_id, LinearMap.id_apply]

/-- For a cyclic group, a zero fixed space remains zero after extending
scalars. -/
theorem representationBaseChange_invariants_eq_bot_of_cyclic
    [FiniteDimensional F V] [IsCyclic G]
    (rho : Representation F G V) (hfix : rho.invariants = ⊥) :
    (representationBaseChange (A := A) rho).invariants = ⊥ := by
  obtain ⟨z, hz⟩ :=
    Submission.OddOrder.MathlibSupport.exists_invariants_eq_ker_sub_one rho
  have hinjective : Function.Injective (rho z - 1 : Module.End F V) := by
    rw [← LinearMap.ker_eq_bot]
    rw [← hz, hfix]
  have hinjectiveA : Function.Injective
      ((rho z - 1 : Module.End F V).baseChange A) :=
    linearMap_baseChange_injective_of_injective (A := A) _ hinjective
  apply eq_bot_iff.mpr
  intro x hx
  have hzfixed :=
    (Representation.mem_invariants _ _).mp hx z
  apply hinjectiveA
  change ((rho z - 1 : Module.End F V).baseChange A) x =
    ((rho z - 1 : Module.End F V).baseChange A) 0
  have hzero : (rho z).baseChange A x - x = 0 :=
    sub_eq_zero.mpr hzfixed
  simpa using hzero

end Submission.OddOrder.MathlibSupport
