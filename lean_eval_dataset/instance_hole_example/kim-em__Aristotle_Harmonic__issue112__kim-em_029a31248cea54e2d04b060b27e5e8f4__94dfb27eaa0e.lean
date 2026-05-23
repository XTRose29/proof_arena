/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: instance_hole_example
user: kim-em
model: Aristotle (Harmonic)
submission_repo: kim-em/029a31248cea54e2d04b060b27e5e8f4
submission_ref: 94dfb27eaa0edf18ce51da4591aa4b09d21a89e0
issue_number: 112
-/
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
