import Submission.OddOrder.MathlibSupport.CyclicQuotientGenerator
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Two lifted cyclic generators for Huppert's central-extension argument.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- If `T ≤ X ◁ G`, both `X / T` and `G / X` are cyclic, then there are
ambient elements `x ∈ X` and `y ∈ G` which generate the two successive
cyclic factors. -/
theorem exists_two_generators_of_cyclic_tower
    (T X : Subgroup G) [T.Normal] [X.Normal] (hTX : T ≤ X)
    [IsCyclic (X ⧸ T.subgroupOf X)] [IsCyclic (G ⧸ X)] :
    ∃ x y : G,
      x ∈ X ∧
      Subgroup.zpowers x ⊔ T = X ∧
      Subgroup.zpowers y ⊔ X = ⊤ := by
  let TX : Subgroup X := T.subgroupOf X
  letI : TX.Normal := by dsimp [TX]; infer_instance
  obtain ⟨x, hx⟩ :=
    exists_zpowers_sup_eq_top_of_quotient_isCyclic TX
  obtain ⟨y, hy⟩ :=
    exists_zpowers_sup_eq_top_of_quotient_isCyclic X
  refine ⟨x, y, x.property, ?_, hy⟩
  have hmap := congrArg (Subgroup.map X.subtype) hx
  rw [Subgroup.map_sup, MonoidHom.map_zpowers,
    Subgroup.map_subgroupOf_eq_of_le hTX,
    ← MonoidHom.range_eq_map, X.range_subtype] at hmap
  exact hmap

end Submission.OddOrder.MathlibSupport
