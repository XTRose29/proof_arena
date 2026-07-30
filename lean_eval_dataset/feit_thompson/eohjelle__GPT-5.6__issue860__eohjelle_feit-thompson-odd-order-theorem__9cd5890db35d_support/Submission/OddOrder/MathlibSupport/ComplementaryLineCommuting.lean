import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection

/-!
Commuting endomorphisms preserving complementary lines.
-/

namespace Submission.OddOrder.MathlibSupport

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- Any two endomorphisms preserving the same pair of complementary
one-dimensional subspaces commute. -/
theorem commute_of_preserves_complementary_lines
    (U W : Submodule F V) (hcompl : IsCompl U W)
    (hUdim : Module.finrank F U = 1)
    (hWdim : Module.finrank F W = 1)
    (f g : Module.End F V)
    (hfU : U ≤ U.comap f) (hfW : W ≤ W.comap f)
    (hgU : U ≤ U.comap g) (hgW : W ≤ W.comap g) :
    Commute f g := by
  obtain ⟨a, hfa, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hUdim (f.restrict hfU)
  obtain ⟨b, hfb, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hWdim (f.restrict hfW)
  obtain ⟨c, hgc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hUdim (g.restrict hgU)
  obtain ⟨d, hgd, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hWdim (g.restrict hgW)
  have hfu (u : U) : f (u : V) = a • (u : V) :=
    congrArg Subtype.val (LinearMap.congr_fun hfa u)
  have hfw (w : W) : f (w : V) = b • (w : V) :=
    congrArg Subtype.val (LinearMap.congr_fun hfb w)
  have hgu (u : U) : g (u : V) = c • (u : V) :=
    congrArg Subtype.val (LinearMap.congr_fun hgc u)
  have hgw (w : W) : g (w : V) = d • (w : V) :=
    congrArg Subtype.val (LinearMap.congr_fun hgd w)
  have hcommU (u : U) : f (g (u : V)) = g (f (u : V)) := by
    rw [hgu, f.map_smul, hfu, g.map_smul, hgu]
    simp [smul_smul, mul_comm]
  have hcommW (w : W) : f (g (w : V)) = g (f (w : V)) := by
    rw [hgw, f.map_smul, hfw, g.map_smul, hgw]
    simp [smul_smul, mul_comm]
  apply LinearMap.ext
  intro x
  change f (g x) = g (f x)
  let e := Submodule.prodEquivOfIsCompl U W hcompl
  let y := e.symm x
  have hxy : (y.1 : V) + (y.2 : V) = x := by
    simpa [e, y] using e.apply_symm_apply x
  rw [← hxy, g.map_add, f.map_add, f.map_add, g.map_add,
    hcommU y.1, hcommW y.2]

end Submission.OddOrder.MathlibSupport
