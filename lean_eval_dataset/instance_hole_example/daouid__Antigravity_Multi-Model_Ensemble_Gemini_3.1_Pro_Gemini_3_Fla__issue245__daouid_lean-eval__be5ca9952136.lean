/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: instance_hole_example
user: daouid
model: Antigravity (Multi-Model Ensemble: Gemini 3.1 Pro, Gemini 3 Flash, Claude 4.6 Sonnet/Opus)
submission_repo: daouid/lean-eval
submission_ref: be5ca99521362ea9131eca9a2d95d91ec6fff0f4
issue_number: 245
-/
import Mathlib

namespace Submission

/-!
Minimal example exercising `instance` holes in the multi-hole
eval-problem pipeline. The carrier type is itself a hole so the source
has no non-hole declarations and the generator does not need a
`ChallengeDeps` split.
-/
def WidgetCarrier : Type := Unit

instance instInhabitedWidget : Inhabited WidgetCarrier := ⟨()⟩

end Submission