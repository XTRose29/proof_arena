import Submission.OddOrder.MathlibSupport.BaerSuzukiSetNormalizer

/-!
The globally normalized set-candidate branch of Baer-Suzuki.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- If the whole ambient group normalizes a set candidate containing `x`,
then the closure of that candidate is a normal p-subgroup containing `x`. -/
theorem mem_pCore_of_isBaerSuzukiSetCandidate_of_le_normalizer
    {p : ℕ} {x : G} {P : Subgroup G} {D : Set G}
    (hD : IsBaerSuzukiSetCandidate p x P D) (hxD : x ∈ D)
    (hDG : (⊤ : Subgroup G) ≤ Subgroup.normalizer D) :
    x ∈ pCore p G := by
  obtain ⟨_, y, _, _, hB⟩ := hD
  let C : Subgroup G := Subgroup.closure D
  have hCB : C ≤ Subgroup.closure (Set.insert y D) :=
    Subgroup.closure_mono (Set.subset_insert y D)
  have hCp : IsPGroup p C := hB.to_le hCB
  have hCnormalizer : Subgroup.normalizer (C : Set G) = ⊤ := by
    apply top_unique
    exact hDG.trans (Subgroup.normalizer_le_normalizer_closure D)
  haveI : C.Normal := Subgroup.normalizer_eq_top_iff.mp hCnormalizer
  exact le_pCore hCp (by infer_instance) (Subgroup.subset_closure hxD)

end Submission.OddOrder.MathlibSupport
