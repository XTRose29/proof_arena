import Mathlib.RepresentationTheory.FinGroupCharZero
import Mathlib.RepresentationTheory.Irreducible

/-!
# Simple bundled representations and unbundled irreducibility

The Peterfalvi character layer stores a categorical `Simple` witness on an
`FDRep`, whereas the projective-intertwiner layer uses
`Representation.IsIrreducible`.  This file supplies the missing direction
between those two formulations.
-/

namespace Submission.OddOrder.MathlibSupport

open CategoryTheory

universe u v

variable {k : Type u} {G : Type v} [Field k] [Group G]

/-- The underlying unbundled representation of a simple finite-dimensional
bundled representation is irreducible. -/
theorem representation_isIrreducible_of_simple_fdRep
    (V : FDRep k G) [Simple V] : Representation.IsIrreducible V.ρ := by
  refine { toNontrivial := ?_, eq_bot_or_eq_top := ?_ }
  · refine ⟨⊥, ⊤, fun h ↦ ?_⟩
    apply id_nonzero V
    apply Action.Hom.ext
    apply InducedCategory.hom_ext
    apply ModuleCat.hom_ext
    ext x
    have hx : x = 0 := by
      have hmem : x ∈ (⊥ : Subrepresentation V.ρ).toSubmodule := by
        rw [h]
        exact Submodule.mem_top
      exact hmem
    simp [hx]
  · intro U
    let W : FDRep k G := FDRep.of U.toRepresentation
    let i : W ⟶ V :=
      { hom := InducedCategory.homMk
          (ModuleCat.ofHom U.toSubmodule.subtype)
        comm := fun g ↦ by
          ext x
          rfl }
    let F := forget₂ (FDRep k G) (Rep k G)
    have hFi : Function.Injective (F.map i).hom := by
      intro x y hxy
      exact Subtype.ext hxy
    letI : Mono (F.map i) := (Rep.mono_iff_injective (F.map i)).2 hFi
    letI : Mono i :=
      F.mono_of_mono_map (show Mono (F.map i) from inferInstance)
    by_cases hi : i = 0
    · left
      apply SetLike.ext
      intro x
      constructor
      · intro hx
        let y : W := ⟨x, hx⟩
        have hy := ConcreteCategory.congr_hom hi y
        change x = 0 at hy
        rw [hy]
        exact Submodule.zero_mem _
      · intro hx
        have hx0 : x = 0 := hx
        rw [hx0]
        exact Submodule.zero_mem _
    · right
      haveI : IsIso i := (Simple.mono_isIso_iff_nonzero i).2 hi
      apply SetLike.ext
      intro x
      constructor
      · intro _
        exact Submodule.mem_top
      · intro _
        let y : W := (inv i) x
        have hy := ConcreteCategory.congr_hom (IsIso.inv_hom_id i) x
        change (y : V) = x at hy
        exact hy ▸ y.property

end Submission.OddOrder.MathlibSupport
