import ChallengeDeps
import Submission.AffineCertificate

open LeanEval.GroupTheory.NovikovUnsolvableProblem

namespace Submission

theorem novikov_unsolvable :
    ∃ (n : ℕ) (rels : Set (FreeGroup (Fin n))),
      rels.Finite ∧ ¬ WordProblemSolvable (PresentedGroup.mk rels) := by
  exact
    Submission.SubgroupReduction.SubgroupMembershipCertificate.sound
      AffineCertificate.certificate

end Submission
