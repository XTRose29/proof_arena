import Mathlib.LinearAlgebra.Projection

/-!
Endomorphisms determined by their restrictions to complementary subspaces.
-/

namespace Submission.OddOrder.MathlibSupport

variable {F V : Type*} [Ring F] [AddCommGroup V] [Module F V]

/-- An endomorphism that restricts to the identity on two complementary
subspaces is the identity on the ambient module. -/
theorem eq_id_of_restrict_eq_id_of_isCompl
    (U W : Submodule F V) (hcompl : IsCompl U W)
    (f : Module.End F V)
    (hU : U ≤ U.comap f) (hW : W ≤ W.comap f)
    (hfU : f.restrict hU = LinearMap.id)
    (hfW : f.restrict hW = LinearMap.id) :
    f = LinearMap.id := by
  let e := Submodule.prodEquivOfIsCompl U W hcompl
  apply LinearMap.ext
  intro x
  change f x = x
  let y := e.symm x
  have hxy : x = (y.1 : V) + (y.2 : V) := by
    simpa [e, y] using (e.apply_symm_apply x).symm
  have hfyU : f (y.1 : V) = y.1 := by
    exact congrArg Subtype.val (LinearMap.congr_fun hfU y.1)
  have hfyW : f (y.2 : V) = y.2 := by
    exact congrArg Subtype.val (LinearMap.congr_fun hfW y.2)
  calc
    f x = f ((y.1 : V) + (y.2 : V)) := by rw [hxy]
    _ = f y.1 + f y.2 := f.map_add _ _
    _ = (y.1 : V) + (y.2 : V) := by rw [hfyU, hfyW]
    _ = x := hxy.symm

end Submission.OddOrder.MathlibSupport
