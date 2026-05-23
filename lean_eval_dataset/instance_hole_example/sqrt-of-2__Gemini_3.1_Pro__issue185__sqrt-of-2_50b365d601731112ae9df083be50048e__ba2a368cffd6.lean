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
