import Mathlib
import Submission.Presentation

namespace Submission

theorem higman_infinite_simple :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ IsSimpleGroup (PresentedGroup rels) ∧
        Infinite (PresentedGroup rels) := by
  refine ⟨4, Thompson.Tree.Presentation.relations,
    Thompson.Tree.Presentation.relations_finite, ?_, ?_⟩
  · exact Thompson.Tree.Presentation.presentationEquiv.isSimpleGroup
  · exact Thompson.Tree.Presentation.presentationEquiv.toEquiv.infinite_iff.mpr
      inferInstance

end Submission
