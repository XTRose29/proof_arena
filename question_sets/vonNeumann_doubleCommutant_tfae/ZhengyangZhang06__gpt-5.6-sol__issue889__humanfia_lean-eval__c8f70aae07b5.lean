import Mathlib
import Submission.Helpers

namespace Submission

theorem vonNeumann_doubleCommutant_tfae {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (S : StarSubalgebra ℂ (H →L[ℂ] H)) :
    List.TFAE
      [ Set.centralizer (Set.centralizer (S : Set (H →L[ℂ] H))) = S
      , IsClosed
          (ContinuousLinearMapWOT.ofCLM '' (S : Set (H →L[ℂ] H)))
      , IsClosed
          (ContinuousLinearMap.toPointwiseConvergenceCLM ℂ (RingHom.id ℂ) H H ''
            (S : Set (H →L[ℂ] H))) ] := by
  tfae_have 1 → 2 := Helpers.isClosed_wot_of_doubleCentralizer_eq S
  tfae_have 2 → 3 := Helpers.isClosed_pointwise_of_isClosed_wot S
  tfae_have 3 → 1 := Helpers.doubleCentralizer_eq_of_isClosed_pointwise S
  tfae_finish

end Submission
