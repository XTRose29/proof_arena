import Mathlib
import Submission.Thompson

namespace Submission.Helpers

theorem exists_finite_presentation_of (G : Type*) [Group G]
    [Group.IsFinitelyPresented G] [IsSimpleGroup G] [Infinite G] :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ IsSimpleGroup (PresentedGroup rels) ∧
        Infinite (PresentedGroup rels) := by
  obtain ⟨n, φ, hφ, rels, hrels, hclosure⟩ :=
    Group.IsFinitelyPresented.out (G := G)
  let e : PresentedGroup rels ≃* G := by
    change (FreeGroup (Fin n) ⧸ Subgroup.normalClosure rels) ≃* G
    exact (QuotientGroup.quotientMulEquivOfEq hclosure).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  exact ⟨n, rels, hrels, e.isSimpleGroup, e.toEquiv.infinite_iff.mpr inferInstance⟩

end Submission.Helpers
