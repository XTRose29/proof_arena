import Submission.OddOrder.MathlibSupport.PMaxElem

/-!
Transport of maximal elementary-abelian subgroups to a subgroup subtype.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

namespace IsPMaxElem

variable {G : Type u} [Group G] {p : ℕ} {A E : Subgroup G}

/-- A subgroup maximal elementary abelian inside `A`, when viewed as a
subgroup of the group `A`, is maximal elementary abelian in the whole subtype.
-/
theorem subgroupOf_top (hE : IsPMaxElem p A E) :
    IsPMaxElem p (⊤ : Subgroup A) (E.subgroupOf A) := by
  apply isPMaxElem_iff_pTorsionCentralizerWithin.mpr
  have hEeq : pTorsionCentralizerWithin p A E = (E : Set G) :=
    isPMaxElem_iff_pTorsionCentralizerWithin.mp hE
  ext x
  constructor
  · intro hx
    have hxAmbient : (x : G) ∈ pTorsionCentralizerWithin p A E := by
      refine ⟨x.property, ?_, ?_⟩
      · rw [Subgroup.mem_centralizer_iff]
        intro y hy
        let yA : A := ⟨y, hE.le hy⟩
        have hyE : yA ∈ E.subgroupOf A := hy
        exact congrArg Subtype.val
          (Subgroup.mem_centralizer_iff.mp hx.2.1 yA hyE)
      · simpa using congrArg Subtype.val hx.2.2
    rw [hEeq] at hxAmbient
    exact hxAmbient
  · intro hx
    have hxAmbient : (x : G) ∈ pTorsionCentralizerWithin p A E := by
      rw [hEeq]
      exact hx
    refine ⟨Subgroup.mem_top x, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      exact Subgroup.mem_centralizer_iff.mp hxAmbient.2.1 (y : G) hy
    · apply Subtype.ext
      exact hxAmbient.2.2

end IsPMaxElem

end Submission.OddOrder.MathlibSupport
