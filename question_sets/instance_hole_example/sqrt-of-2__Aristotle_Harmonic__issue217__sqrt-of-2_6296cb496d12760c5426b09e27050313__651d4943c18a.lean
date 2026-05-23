/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: instance_hole_example
user: sqrt-of-2
model: Aristotle (Harmonic)
submission_repo: sqrt-of-2/6296cb496d12760c5426b09e27050313
submission_ref: 651d4943c18ae1620f5d0be19502aea2ec828542
issue_number: 217
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
