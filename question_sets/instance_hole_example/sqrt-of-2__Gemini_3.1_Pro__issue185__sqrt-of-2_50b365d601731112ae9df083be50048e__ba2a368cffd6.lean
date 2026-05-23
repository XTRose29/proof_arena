/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: instance_hole_example
user: sqrt-of-2
model: Gemini 3.1 Pro
submission_repo: sqrt-of-2/50b365d601731112ae9df083be50048e
submission_ref: ba2a368cffd6304f06b7a4cffd913b643f76d144
issue_number: 185
-/
import Mathlib
/-!
Minimal example exercising `instance` holes in the multi-hole
eval-problem pipeline. The carrier type is itself a hole so the source
has no non-hole declarations and the generator does not need a
`ChallengeDeps` split.
-/

namespace Submission

def WidgetCarrier : Type := Nat
instance instInhabitedWidget : Inhabited WidgetCarrier := ⟨(0 : Nat)⟩

end Submission
