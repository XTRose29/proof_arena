import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.LinearAlgebra.Projection

/-!
Invariant lines for an operator with two distinct complementary eigenlines.
-/

namespace Submission.OddOrder.MathlibSupport

variable {F V : Type*} [Field F] [AddCommGroup V] [Module F V]

/-- An eigenvector of an operator acting by distinct scalars on complementary
subspaces lies in one of those subspaces. -/
theorem eigenvector_mem_left_or_right_of_complementary_scalar_actions
    (U W : Submodule F V) (hcompl : IsCompl U W)
    (f : Module.End F V)
    (hU : U ≤ U.comap f) (hW : W ≤ W.comap f)
    (a b : F)
    (hfa : f.restrict hU = a • LinearMap.id)
    (hfb : f.restrict hW = b • LinearMap.id)
    (hab : a ≠ b) (v : V) (c : F) (hv : f v = c • v) :
    v ∈ U ∨ v ∈ W := by
  by_contra hvUW
  have hvU : v ∉ U := fun hvU => hvUW (Or.inl hvU)
  have hvW : v ∉ W := fun hvW => hvUW (Or.inr hvW)
  let e := Submodule.prodEquivOfIsCompl U W hcompl
  let y := e.symm v
  have hy1 : y.1 ≠ 0 := by
    intro hy1
    apply hvW
    apply (Submodule.prodEquivOfIsCompl_symm_apply_fst_eq_zero U W hcompl).mp
    simpa [e, y] using hy1
  have hy2 : y.2 ≠ 0 := by
    intro hy2
    apply hvU
    apply (Submodule.prodEquivOfIsCompl_symm_apply_snd_eq_zero U W hcompl).mp
    simpa [e, y] using hy2
  have hxy : (y.1 : V) + (y.2 : V) = v := by
    simpa [e, y] using e.apply_symm_apply v
  have hfy1 : f (y.1 : V) = a • (y.1 : V) := by
    exact congrArg Subtype.val (LinearMap.congr_fun hfa y.1)
  have hfy2 : f (y.2 : V) = b • (y.2 : V) := by
    exact congrArg Subtype.val (LinearMap.congr_fun hfb y.2)
  have heqV :
      a • (y.1 : V) + b • (y.2 : V) =
        c • (y.1 : V) + c • (y.2 : V) := by
    calc
      a • (y.1 : V) + b • (y.2 : V) =
          f ((y.1 : V) + (y.2 : V)) := by rw [f.map_add, hfy1, hfy2]
      _ = f v := by rw [hxy]
      _ = c • v := hv
      _ = c • ((y.1 : V) + (y.2 : V)) := by rw [hxy]
      _ = c • (y.1 : V) + c • (y.2 : V) := smul_add _ _ _
  have hcoords := congrArg e.symm heqV
  have hcoords' :
      (a • y.1, b • y.2) = (c • y.1, c • y.2) := by
    simpa [e, map_add, map_smul,
      Submodule.prodEquivOfIsCompl_symm_apply_left,
      Submodule.prodEquivOfIsCompl_symm_apply_right] using hcoords
  have hac : a = c :=
    (smul_left_injective F hy1) (congrArg Prod.fst hcoords')
  have hbc : b = c :=
    (smul_left_injective F hy2) (congrArg Prod.snd hcoords')
  exact hab (hac.trans hbc.symm)

/-- A one-dimensional invariant subspace of an operator with two distinct
complementary eigenlines is contained in one of those eigenlines. -/
theorem invariantLine_le_left_or_right_of_complementary_scalar_actions
    [FiniteDimensional F V]
    (U W : Submodule F V) (hcompl : IsCompl U W)
    (f : Module.End F V)
    (hU : U ≤ U.comap f) (hW : W ≤ W.comap f)
    (a b : F)
    (hfa : f.restrict hU = a • LinearMap.id)
    (hfb : f.restrict hW = b • LinearMap.id)
    (hab : a ≠ b) (L : Submodule F V) (hL : L ≤ L.comap f)
    (hLdim : Module.finrank F L = 1) :
    L ≤ U ∨ L ≤ W := by
  letI : Nontrivial L := Module.nontrivial_of_finrank_eq_succ hLdim
  obtain ⟨x, hx⟩ := exists_ne (0 : L)
  obtain ⟨c, hc, _⟩ :=
    LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hLdim (f.restrict hL)
  have hfx : f (x : V) = c • (x : V) := by
    exact congrArg Subtype.val (LinearMap.congr_fun hc x)
  have hxUW : (x : V) ∈ U ∨ (x : V) ∈ W :=
    eigenvector_mem_left_or_right_of_complementary_scalar_actions
      U W hcompl f hU hW a b hfa hfb hab x c hfx
  have hxV : (x : V) ≠ 0 := by
    intro hx0
    exact hx (Subtype.ext hx0)
  have hspanL : F ∙ (x : V) = L := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem (x : V) L).mpr x.property
    · rw [finrank_span_singleton hxV, hLdim]
  rcases hxUW with hxU | hxW
  · left
    rw [← hspanL]
    exact (Submodule.span_singleton_le_iff_mem (x : V) U).mpr hxU
  · right
    rw [← hspanL]
    exact (Submodule.span_singleton_le_iff_mem (x : V) W).mpr hxW

end Submission.OddOrder.MathlibSupport
