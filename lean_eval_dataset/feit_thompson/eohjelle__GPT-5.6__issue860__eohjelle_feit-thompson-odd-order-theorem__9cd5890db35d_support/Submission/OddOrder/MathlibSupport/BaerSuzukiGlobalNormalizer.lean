import Submission.OddOrder.MathlibSupport.BaerSuzukiMaximalContaining

/-!
The globally normalized candidate branch of the Baer-Suzuki argument.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- If a Baer-Suzuki candidate containing `x` is normalized by the whole
ambient group, then `x` belongs to the ambient p-core. -/
theorem mem_pCore_of_isBaerSuzukiCandidate_of_le_normalizer [Finite G]
    {p : ℕ} {x : G} {P D : Subgroup G}
    (hD : IsBaerSuzukiCandidate p x P D) (hxD : x ∈ D)
    (hDG : (⊤ : Subgroup G) ≤ Subgroup.normalizer (D : Set G)) :
    x ∈ pCore p G := by
  obtain ⟨_, _, y, _, _, hB⟩ := hD
  have hDp : IsPGroup p D :=
    hB.to_le (show D ≤ Subgroup.zpowers y ⊔ D from le_sup_right)
  have hnormalizer : Subgroup.normalizer (D : Set G) = ⊤ :=
    top_unique hDG
  haveI : D.Normal := Subgroup.normalizer_eq_top_iff.mp hnormalizer
  exact le_pCore hDp (by infer_instance) hxD

end Submission.OddOrder.MathlibSupport
