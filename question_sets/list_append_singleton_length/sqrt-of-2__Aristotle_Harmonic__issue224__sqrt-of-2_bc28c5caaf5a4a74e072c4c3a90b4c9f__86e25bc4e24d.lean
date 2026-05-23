import Mathlib

namespace Submission

theorem list_append_singleton_length :
    (([1, 2] : List Nat).append [3]).length = 3 := by
  -- The length of the list [1, 2, 3] is indeed 3.
  simp [List.length]

end Submission
