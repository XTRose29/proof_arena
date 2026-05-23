/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: instance_hole_example
user: sqrt-of-2
model: Leanstral-2603
submission_repo: sqrt-of-2/f17c25e2257bc0b3ae8e58f7f10b01a0
submission_ref: e24429fdb84b7184095ce5e3a9c5fec0d9ccce5f
issue_number: 203
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
