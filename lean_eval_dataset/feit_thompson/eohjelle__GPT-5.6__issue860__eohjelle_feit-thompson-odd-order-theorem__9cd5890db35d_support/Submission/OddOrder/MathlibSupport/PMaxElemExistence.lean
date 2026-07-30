import Submission.OddOrder.MathlibSupport.PMaxElem

/-!
Existence of maximal elementary-abelian subgroups above a prescribed one.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

/-- Every elementary-abelian `p`-subgroup of `A` is contained in one that is
maximal among the elementary-abelian `p`-subgroups of `A`.  This is the
existence content of MathComp's `pmaxElem_exists`. -/
theorem exists_isPMaxElem_ge
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {A E : Subgroup G}
    (hE : IsPElementaryIn p A E) :
    ∃ A₀ : Subgroup G,
      IsPMaxElem p A A₀ ∧ E ≤ A₀ := by
  classical
  letI : Finite (Subgroup G) :=
    Finite.of_injective (fun F : Subgroup G ↦ (F : Set G))
      SetLike.coe_injective
  let candidates : Set (Subgroup G) :=
    {F | IsPElementaryIn p A F ∧ E ≤ F}
  have hcandidates : candidates.Nonempty := ⟨E, hE, le_rfl⟩
  obtain ⟨A₀, hA₀, hA₀max⟩ :=
    candidates.toFinite.exists_maximal hcandidates
  refine ⟨A₀, ⟨hA₀.1, ?_⟩, hA₀.2⟩
  intro F hF hA₀F
  apply le_antisymm
  · exact hA₀max ⟨hF, hA₀.2.trans hA₀F⟩ hA₀F
  · exact hA₀F

end Submission.OddOrder.MathlibSupport
