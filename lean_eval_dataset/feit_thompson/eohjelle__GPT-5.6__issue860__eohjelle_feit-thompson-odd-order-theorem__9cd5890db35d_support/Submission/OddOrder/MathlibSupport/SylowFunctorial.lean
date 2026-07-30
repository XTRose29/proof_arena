import Mathlib.GroupTheory.Sylow

/-!
Small functorial consequences for Sylow subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K] [Finite G]

/-- A Sylow subgroup maps onto a surjective `p`-group target. -/
theorem Sylow.map_eq_top_of_surjective_of_isPGroup {p : ℕ} [Fact p.Prime]
    (P : Sylow p G) (f : G →* K) (hf : Function.Surjective f)
    (hK : IsPGroup p K) : (P : Subgroup G).map f = ⊤ := by
  let Q : Sylow p K := P.mapSurjective hf
  have hQtop : (Q : Subgroup K) = ⊤ :=
    (Q.is_maximal' (hK.to_subgroup ⊤) le_top).symm
  simpa [Q] using hQtop

end Submission.OddOrder.MathlibSupport
