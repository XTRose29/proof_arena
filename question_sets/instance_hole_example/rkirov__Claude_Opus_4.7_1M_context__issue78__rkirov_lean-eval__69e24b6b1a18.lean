/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: instance_hole_example
user: rkirov
model: Claude Opus 4.7 (1M context)
submission_repo: rkirov/lean-eval
submission_ref: 69e24b6b1a18117485ef55663d4773900655e033
issue_number: 78
-/
import Mathlib
import Submission.Helpers
/-!
Minimal example exercising `instance` holes in the multi-hole
eval-problem pipeline. The carrier type is itself a hole so the source
has no non-hole declarations and the generator does not need a
`ChallengeDeps` split.
-/

namespace Submission

def WidgetCarrier : Type := Unit
instance instInhabitedWidget : Inhabited WidgetCarrier := ⟨()⟩

end Submission
