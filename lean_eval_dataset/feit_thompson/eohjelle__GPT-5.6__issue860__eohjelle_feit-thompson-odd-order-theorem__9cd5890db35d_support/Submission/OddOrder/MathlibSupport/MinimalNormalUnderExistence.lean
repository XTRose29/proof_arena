import Submission.OddOrder.MathlibSupport.MinimalNormalUnder

/-!
Existence of minimal nontrivial subgroups normalized by a prescribed acting
subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- Every nontrivial finite subgroup normalized by `H` contains a subgroup
that is minimal normal under `H`. -/
theorem exists_minimalNormalUnder_le {E H : Subgroup G}
    (hE : E ≠ ⊥)
    (hH : H ≤ Subgroup.normalizer (E : Set G)) :
    ∃ M : Subgroup G, M ≤ E ∧ IsMinimalNormalUnder M H := by
  let P : Subgroup G → Prop := fun M ↦
    M ≤ E ∧ M ≠ ⊥ ∧ H ≤ Subgroup.normalizer (M : Set G)
  have hPE : P E := ⟨le_rfl, hE, hH⟩
  obtain ⟨M, _, hMmin⟩ := Finite.exists_le_minimal hPE
  refine ⟨M, hMmin.1.1, hMmin.1.2.1, hMmin.1.2.2, ?_⟩
  intro D hDM hD hDinv
  have hPD : P D :=
    ⟨hDM.trans hMmin.1.1, hD, Subgroup.le_normalizer_iff.mpr hDinv⟩
  exact (hMmin.eq_of_ge hPD hDM).le

end Submission.OddOrder.MathlibSupport
