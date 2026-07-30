import Mathlib
import Submission.Helpers

namespace Submission

def WidgetCarrier : Type := Unit

instance instInhabitedWidget : Inhabited WidgetCarrier :=
  inferInstanceAs (Inhabited Unit)

end Submission
