import ChallengeDeps
import Submission.Helpers
import Submission.HigherOrder

open LeanEval.Analysis.SobolevMorreyProblem
open MeasureTheory
open scoped ENNReal NNReal

namespace Submission

theorem sobolev_embedding {n k r : ℕ} {α p : ℝ}
    (_hp : (n : ℝ) < p) (_hα : 0 < α) (_hα1 : α ≤ 1)
    (_hgap : (r : ℝ) + α < (k : ℝ) - n / p)
    (f : E n → ℝ) (_hf : MemSobolevWk k (ENNReal.ofReal p) f) :
    ∃ g : E n → ℝ, f =ᵐ[volume] g ∧ MemHolder r α g := by
  cases n with
  | zero =>
      exact ⟨f, Filter.EventuallyEq.rfl, Helpers.memHolder_zero_dim f⟩
  | succ n =>
      have hn : 0 < n + 1 := Nat.succ_pos n
      have hk : r + 1 ≤ k :=
        Helpers.succ_le_of_morrey_gap _hp _hα _hgap
      refine ⟨HigherOrder.regularRep _hf (fun _ ↦ 0), ?_, ?_⟩
      · exact HigherOrder.ae_eq_regularRep_zero hn _hp _hf (by omega)
      · exact HigherOrder.regularRep_memHolder
          hn _hp _hα _hα1 _hgap _hf

end Submission
