import ChallengeDeps

open LeanEval.Dynamics.HyperbolicShadowingProblem
open scoped Topology

namespace Submission.Helpers

variable {d : ℕ}

theorem hasShadowing_empty (T : E d ≃ₜ E d) :
    HasShadowing (T : E d → E d) (∅ : Set (E d)) := by
  refine ⟨∅, isOpen_empty, ?_, ?_⟩
  · intro _ h
    exact False.elim h
  · intro _δ _hδ
    refine ⟨1, by norm_num, ?_⟩
    intro x hx _hp
    exact False.elim (hx 0)

theorem hasShadowing_of_eq_empty (T : E d ≃ₜ E d) (K : Set (E d)) (hK : K = ∅) :
    HasShadowing (T : E d → E d) K := by
  subst K
  exact hasShadowing_empty T

end Submission.Helpers
