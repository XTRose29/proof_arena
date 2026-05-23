import Mathlib

/-!
# Gap arithmetic for WellFormedConstraints
-/

namespace Submission.GapArith

/-- gap_lower: ⌈f1/2⌉ ≤ f2/2 when f1 ≤ f2 and f1=f2 implies f1 even. -/
lemma gap_lower_arith (f1 f2 : Nat) (hle : f1 ≤ f2)
    (h_same_even : f1 = f2 → f1 % 2 = 0) :
    f1 / 2 + (if decide (f1 % 2 = 1) = true then 1 else 0) ≤ f2 / 2 := by
  grind

/-
gap_upper from pairLe + NDS + odd sums.
    Extra condition: when both f are even, s must strictly increase.
-/
lemma gap_upper_arith (f1 s1 f2 s2 : Nat)
    (h_odd1 : (f1 + s1) % 2 = 1) (h_odd2 : (f2 + s2) % 2 = 1)
    (h_sum_lt : f1 + s1 < f2 + s2)
    (hfle : f1 ≤ f2) (hsle : s1 ≤ s2)
    (h_even_strict : f1 % 2 = 0 → f2 % 2 = 0 → s1 < s2) :
    f2 / 2 + (f1 + s1) / 2 + 1 ≤
      f1 / 2 + (if decide (f1 % 2 = 1) = true then 1 else 0) + (f2 + s2) / 2 := by
  grind

/-- counts ≤ vals: f/2 ≤ (f+s)/2 -/
lemma count_le_val_arith (f s : Nat) : f / 2 ≤ (f + s) / 2 := by
  exact Nat.div_le_div_right ( Nat.le_add_right _ _ )

end Submission.GapArith