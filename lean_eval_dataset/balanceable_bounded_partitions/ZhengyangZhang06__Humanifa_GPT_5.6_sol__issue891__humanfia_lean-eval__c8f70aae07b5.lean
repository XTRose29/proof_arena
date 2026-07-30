import ChallengeDeps
import Submission.Helpers
import Submission.Upper

open LeanEval.Combinatorics

namespace Submission

theorem minimal_balanceable_of_bounded (k : ℕ) (hk : 0 < k) :
    Minimal (fun n => 0 < n ∧ ∀ p : n.Partition, Bounded k p → Balanceable p) (2 * (Finset.Icc 1 k).lcm id) := by
  refine ⟨⟨Nat.mul_pos zero_lt_two (Helpers.lcm_Icc_pos k hk), ?_⟩, ?_⟩
  · intro p hp
    obtain ⟨s, hs, hsum⟩ := Upper.exists_submultiset_sum_lcm_of_bounded
      k hk (fun _ hx => p.parts_pos hx) hp p.parts_sum
    exact Helpers.balanceable_of_submultiset_sum hs hsum
  · intro n hn _hnle
    exact Helpers.lower_bound_of_bounded_balanceable hk hn.1 hn.2

end Submission
