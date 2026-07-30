import Submission.Correspondence

open LeanEval.ProgramVerification

namespace Submission

open Submission.Helpers
open Submission.Correspondence

theorem minRearrange_correct {arr : Array Nat} :
    arr.Perm (1...=arr.size).toArray →
      (∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray), Unimodal x ∧ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector = minRearrange arr) ∧
      (∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray), Unimodal x → minRearrange arr ≤ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector) := by
  intro harr
  let k := minRearrange.lis (sortedCandidateOrdinates arr)
  have hlnds : IsLNDSLength (sortedCandidateOrdinates arr).toList k :=
    lis_isLNDSLength _
  have hmax : MaximumCandidateChain arr k :=
    maximumCandidateChain_of_lnds hlnds
  have hopt : OptimalAgreements arr k :=
    optimalAgreements_of_maximumCandidateChain harr hmax
  exact correctness_of_optimal_agreements
    (minRearrange_eq_size_sub_lis arr) hopt

end Submission
