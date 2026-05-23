/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: instance_hole_example
user: sqrt-of-2
model: GPT 5.5
submission_repo: sqrt-of-2/794ce5843ce2e4c48c4634707b2d9eda
submission_ref: 83d78b11e91327432f4d6216dc028cf925757b41
issue_number: 175
-/
import Mathlib
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
