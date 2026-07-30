import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Projection

/-!
Determinants of endomorphisms preserving complementary lines.
-/

namespace Submission.OddOrder.MathlibSupport

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- An endomorphism acting by scalars `a` and `b` on two complementary
one-dimensional subspaces has determinant `a * b`. -/
theorem det_eq_mul_of_complementary_lines
    (U W : Submodule F V) (hcompl : IsCompl U W)
    (f : Module.End F V)
    (hU : U ≤ U.comap f) (hW : W ≤ W.comap f)
    (a b : F)
    (hfa : f.restrict hU = a • LinearMap.id)
    (hfb : f.restrict hW = b • LinearMap.id)
    (hUdim : Module.finrank F U = 1)
    (hWdim : Module.finrank F W = 1) :
    f.det = a * b := by
  let e := Submodule.prodEquivOfIsCompl U W hcompl
  let g := (f.restrict hU).prodMap (f.restrict hW)
  have hg : g = e.symm.conj f := by
    apply LinearMap.ext
    intro x
    apply e.injective
    have hxU : f (x.1 : V) ∈ U := hU x.1.property
    have hxW : f (x.2 : V) ∈ W := hW x.2.property
    simp [g, e, LinearEquiv.conj_apply,
      Submodule.projection_apply_of_mem_left hcompl hxU,
      Submodule.projection_apply_of_mem_right hcompl hxW,
      Submodule.projection_apply_of_mem_left hcompl.symm hxW,
      Submodule.projection_apply_of_mem_right hcompl.symm hxU]
  have hdet : g.det = f.det := by
    rw [hg]
    exact LinearMap.det_conj f e.symm
  rw [← hdet, LinearMap.det_prodMap, hfa, hfb, LinearMap.det_smul,
    LinearMap.det_smul, hUdim, hWdim]
  simp

end Submission.OddOrder.MathlibSupport
