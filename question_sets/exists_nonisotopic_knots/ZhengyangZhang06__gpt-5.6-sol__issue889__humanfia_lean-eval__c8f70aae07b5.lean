import ChallengeDeps
import Submission.RootCover

open LeanEval.KnotTheory

namespace Submission

theorem exists_nonisotopic_knots : ∃ K₁ K₂ : Knot, ¬ K₁.Isotopic K₂ := by
  refine ⟨Helpers.roundCircle, AlgebraicTrefoil.knot, ?_⟩
  intro hisotopic
  have htrefoil :=
    (Compactification.isotopic_compact_hasAbelianFundamentalGroups_iff hisotopic).mp
      Unknot.roundCompactComplement_hasAbelianFundamentalGroups
  exact RootCover.trefoilCompactComplement_not_hasAbelianFundamentalGroups htrefoil

end Submission
