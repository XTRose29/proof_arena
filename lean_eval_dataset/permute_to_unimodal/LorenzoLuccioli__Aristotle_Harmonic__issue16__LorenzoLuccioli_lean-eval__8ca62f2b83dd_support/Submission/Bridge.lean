import ChallengeDeps
import Submission.LisSound

/-!
# Bridge lemmas connecting standalone definitions to ChallengeDeps
-/

namespace Submission.Bridge

open LeanEval.ProgramVerification
open Submission.LisSound

/-
The two go functions are equal
-/
lemma go_eq (needle : Nat) (arr : Array Nat) (lo hi : Nat) (hhi : hi ≤ arr.size)
    (hhi' : hi ≤ arr.size := by omega) :
    minRearrange.go needle arr lo hi hhi = Submission.LisSound.go needle arr lo hi hhi' := by
  -- By induction on the difference between hi and lo, we can show that the two functions are equal.
  induction' h : hi - lo using Nat.strong_induction_on with d ih generalizing lo hi;
  unfold minRearrange.go go;
  grind

/-
The two upperBound functions are equal
-/
lemma upperBound_eq (needle : Nat) (arr : Array Nat) :
    minRearrange.upperBound needle arr = Submission.LisSound.upperBound needle arr := by
  -- Both functions are defined as go with lo=0, hi=arr.size. Use go_eq.
  apply go_eq

/-
The two loop functions are equal
-/
lemma loop_eq (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) :
    minRearrange.loop arr ans i dp hi = Submission.LisSound.lisLoop arr ans i dp hi := by
  induction' n : arr.size - i using Nat.strong_induction_on with n ih generalizing i ans dp;
  unfold minRearrange.loop lisLoop;
  split_ifs <;> simp_all +decide [ upperBound_eq ];
  exact ih _ ( by omega ) _ _ _ _ rfl

/-
Array.max equals foldl Nat.max 0 for non-empty arrays
-/
lemma array_max_eq_foldl (arr : Array Nat) (h : arr ≠ #[]) :
    arr.max h = arr.foldl Nat.max 0 := by
  have hfold := Array.foldl_max_eq_max (xs := arr) h (a := 0)
  simpa using hfold.symm

/-
The two lis functions are equal
-/
lemma lis_eq (arr : Array Nat) :
    minRearrange.lis arr = Submission.LisSound.lis arr := by
  unfold minRearrange.lis lis;
  split_ifs <;> simp_all +decide [ array_max_eq_foldl ]
  exact loop_eq arr 0 0 _ _

/-- Key soundness result for minRearrange.lis -/
theorem minRearrange_lis_ge_nds (arr : Array Nat) (indices : List Nat)
    (h_sorted : indices.Pairwise (· < ·))
    (h_bound : ∀ i ∈ indices, i < arr.size)
    (h_nondec : indices.Pairwise (fun i j => arr[i]! ≤ arr[j]!)) :
    indices.length ≤ minRearrange.lis arr := by
  rw [lis_eq]
  exact Submission.LisSound.lis_ge_nds arr indices h_sorted h_bound h_nondec

end Submission.Bridge
