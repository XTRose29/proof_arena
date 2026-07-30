import Submission.OddOrder.BG.AppendixAB.TwoGenerator

/-!
Transport of two-generator subgroups along subgroup inclusions.
-/

namespace Submission.OddOrder.MathlibSupport

open Submission.OddOrder.BG.AppendixAB

variable {G K : Type*} [Group G] [Group K]

theorem pairGenerated_map_hom (f : G →* K) (x y : G) :
    (pairGenerated x y).map f = pairGenerated (f x) (f y) := by
  rw [pairGenerated, pairGenerated, Subgroup.map_sup,
    MonoidHom.map_zpowers, MonoidHom.map_zpowers]

theorem pairGenerated_subtype {H : Subgroup G} (x y : H) :
    pairGenerated x y =
      (pairGenerated (x : G) (y : G)).comap H.subtype := by
  apply (Subgroup.map_injective H.subtype_injective)
  rw [pairGenerated_map_hom, Subgroup.comap_subtype,
    Subgroup.subgroupOf_map_subtype]
  exact (inf_eq_left.mpr
    (pairGenerated_le_iff.mpr ⟨x.property, y.property⟩)).symm

theorem pairGenerated_subtype_isPGroup {p : ℕ} {H : Subgroup G} (x y : H)
    (hxy : IsPGroup p (pairGenerated (x : G) (y : G))) :
    IsPGroup p (pairGenerated x y) := by
  rw [pairGenerated_subtype]
  exact hxy.comap_subtype

end Submission.OddOrder.MathlibSupport
