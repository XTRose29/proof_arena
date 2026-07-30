import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
# Restricting the Fitting rank obstruction

The Fitting core of a normal subgroup, viewed in the ambient group, lies in
the ambient Fitting core.  Consequently an elementary-abelian rank
obstruction on the latter restricts to the former.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- The Fitting core of a normal subgroup is contained in the ambient
Fitting core after applying the subtype embedding. -/
theorem fittingWithin_le_fittingCore_of_normal
    [Finite G] {N : Subgroup G} [N.Normal] :
    fittingWithin N ≤ fittingCore G := by
  apply nilpotent_normal_le_fittingCore
  · dsimp [fittingWithin]
    infer_instance
  · infer_instance

/-- Absence of an elementary-abelian subgroup of rank three in the ambient
Fitting core passes to the Fitting core of a normal subgroup. -/
theorem no_elementaryAbelian_rank_three_fittingCore_of_normal
    [Finite G] {N : Subgroup G} [N.Normal] {p : ℕ}
    (hRank : ¬ ∃ E : Subgroup (fittingCore G),
      IsElementaryAbelianOfRank p 3 E) :
    ¬ ∃ E : Subgroup (fittingCore N),
      IsElementaryAbelianOfRank p 3 E := by
  rintro ⟨E, hE⟩
  let inclusion : fittingCore N →* G :=
    N.subtype.comp (fittingCore N).subtype
  have hinclusion (x : fittingCore N) : inclusion x ∈ fittingCore G := by
    apply fittingWithin_le_fittingCore_of_normal (N := N)
    exact ⟨x, x.property, rfl⟩
  let f : fittingCore N →* fittingCore G :=
    inclusion.codRestrict (fittingCore G) hinclusion
  have hf : Function.Injective f := by
    intro x y hxy
    have hxy' : (f x : G) = (f y : G) :=
      congrArg (fun z : fittingCore G ↦ (z : G)) hxy
    change inclusion x = inclusion y at hxy'
    apply Subtype.ext
    exact N.subtype_injective hxy'
  apply hRank
  exact ⟨E.map f, hE.map_of_injective f hf⟩

end Submission.OddOrder.MathlibSupport
