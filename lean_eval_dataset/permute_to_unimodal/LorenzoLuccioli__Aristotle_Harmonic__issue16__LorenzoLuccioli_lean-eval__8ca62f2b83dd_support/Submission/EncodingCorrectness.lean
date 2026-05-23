import Mathlib
import Submission.UnimodalProps

/-!
# Encoding correctness for the lower bound

Shows that agreement positions of a unimodal permutation can be mapped to a
non-decreasing subsequence of the encoded sequence.
-/

namespace Submission.EncodingCorrectness

open Submission.UnimodalProps

/-- A unimodal array splits into increasing prefix b and decreasing suffix b' -/
def IsUnimodal (arr : Array Nat) : Prop :=
  ∃ b b', arr = b ++ b' ∧ b.toList.Pairwise (· < ·) ∧ b'.toList.Pairwise (· > ·)

/-- The "raw" encoded pairs (before sorting) -/
def rawPairs (arr : Array Nat) : Array (Nat × Nat) :=
  let n := arr.size
  (arr.zipIdx.filter (fun (a, i) => i + 1 ≤ a)).map (fun (a, i) => (2 * i + 1, 2 * (a - i - 1))) ++
  (arr.zipIdx.filter (fun (a, i) => n ≤ a + i)).map (fun (a, i) => (2 * (a + i - n), 2 * (n - i) - 1))

/-- The sorted pairs -/
def sortedPairs (arr : Array Nat) : Array (Nat × Nat) :=
  ((rawPairs arr).toList.mergeSort (le := fun a b => a = b ∨ Prod.Lex (· < ·) (· < ·) a b)).toArray

/-- The encoded sequence (second components of sorted pairs) -/
def encodedSeq (arr : Array Nat) : Array Nat :=
  (sortedPairs arr).map (·.2)

/-
For a position i in the increasing prefix with value a ≥ i+1,
    the pair (2i+1, 2(a-i-1)) is in rawPairs
-/
lemma pair_in_rawPairs_filter1 (arr : Array Nat) (i : Nat) (hi : i < arr.size)
    (hfilt : i + 1 ≤ arr[i]) :
    (2 * i + 1, 2 * (arr[i] - i - 1)) ∈ (rawPairs arr).toList := by
  unfold rawPairs;
  simp +zetaDelta at *;
  grind

/-
For a position i in the decreasing suffix with value a where a+i ≥ n,
    the pair (2(a+i-n), 2(n-i)-1) is in rawPairs
-/
lemma pair_in_rawPairs_filter2 (arr : Array Nat) (i : Nat) (hi : i < arr.size)
    (hfilt : arr.size ≤ arr[i] + i) :
    (2 * (arr[i] + i - arr.size), 2 * (arr.size - i) - 1) ∈ (rawPairs arr).toList := by
  -- Since `i` satisfies the condition for the second part of the raw pairs, the pair `(arr[i], i)` is included in the second part of the raw pairs.
  have h_pair_in_second_part : (arr[i], i) ∈ (arr.zipIdx.filter (fun (a, i) => arr.size ≤ a + i)).toList := by
    grind;
  unfold rawPairs; aesop;

/-
In the increasing part, if positions i < j both have a ≥ pos+1 and
    gaps are non-decreasing (a-pos non-decreasing), the encoded second
    components are non-decreasing
-/
lemma increasing_part_nds {a₁ a₂ i₁ i₂ : Nat}
    (hi : i₁ < i₂)
    (ha : a₁ < a₂)
    (hgap : a₁ - i₁ ≤ a₂ - i₂) :
    2 * (a₁ - i₁ - 1) ≤ 2 * (a₂ - i₂ - 1) := by
  omega

/-
In the decreasing part, the entries have non-decreasing second components
    in the sorted sequence (because positions are reversed)
-/
lemma decreasing_part_nds {b₁ b₂ j₁ j₂ n : Nat}
    (hj : j₁ < j₂)
    (hb : b₂ < b₁)
    (hgap : j₂ - j₁ ≤ b₁ - b₂)
    (hn₁ : n ≤ b₁ + j₁) (hn₂ : n ≤ b₂ + j₂) :
    -- second component of j₂'s entry ≤ second component of j₁'s entry
    2 * (n - j₂) - 1 ≤ 2 * (n - j₁) - 1 := by
  omega

end Submission.EncodingCorrectness