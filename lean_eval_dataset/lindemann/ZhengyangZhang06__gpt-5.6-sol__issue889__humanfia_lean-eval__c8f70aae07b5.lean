import Submission.Explore

namespace Submission

theorem lindemann :
    Transcendental ℤ (Real.exp 1) ∧ Transcendental ℤ Real.pi :=
  ⟨Helpers.exp_one_transcendental, pi_transcendental⟩

end Submission
