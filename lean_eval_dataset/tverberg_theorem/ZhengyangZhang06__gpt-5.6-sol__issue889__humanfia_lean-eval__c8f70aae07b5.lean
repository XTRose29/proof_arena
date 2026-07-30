import ChallengeDeps
import Submission.Helpers
import Submission.Tverberg

open LeanEval.Combinatorics.Tverberg
open scoped BigOperators

namespace Submission

theorem tverberg_theorem (d r : ℕ) (hr : 1 ≤ r)
    (f : Fin ((r - 1) * (d + 1) + 1) → Space d) :
    HasTverbergPartition (r := r) f := by
  cases r with
  | zero => omega
  | succ q =>
      simpa only [Nat.succ_sub_one, Nat.succ_eq_add_one] using
        tverberg_succ d q f

end Submission
