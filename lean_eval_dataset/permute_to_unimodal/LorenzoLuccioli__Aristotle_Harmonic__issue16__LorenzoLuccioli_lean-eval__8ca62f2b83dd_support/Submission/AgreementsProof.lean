import Mathlib
import Submission.SortedSubperm
import Submission.UnimodalCounting

/-!
# NDS lemmas for encoded agreement pairs

Shows that for any two agreement pairs from a unimodal permutation,
if the first pair ≤ second pair in lexicographic order, then
the second component of the first ≤ second component of the second.
-/

namespace Submission.AgreementsProof

open Submission.SortedSubperm
open Submission.UnimodalCounting

lemma typeI_nds {vals : List Nat} {n p : Nat}
    (hinc : (vals.take p).Pairwise (· < ·))
    (hlen : vals.length = n) (hp : p ≤ n)
    {i₁ i₂ : Nat} (hi₁ : i₁ < p) (hi₂ : i₂ < p) (hlt : i₁ < i₂)
    (hfilt₁ : i₁ + 1 ≤ vals[i₁]!) (hfilt₂ : i₂ + 1 ≤ vals[i₂]!) :
    2 * (vals[i₁]! - i₁ - 1) ≤ 2 * (vals[i₂]! - i₂ - 1) := by
  -- Since `vals` is strictly increasing in the first `p` elements, we can apply `increasing_gap`.
  have h_gap : (vals.take p)[i₁]! + (i₂ - i₁) ≤ (vals.take p)[i₂]! := by
    convert increasing_gap _ _ _ _;
    any_goals exact hinc;
    grind;
    grind;
    · grind +locals;
    · grind;
    · linarith;
  grind

lemma typeII_nds {vals : List Nat} {n p : Nat}
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hlen : vals.length = n) (hp : p ≤ n)
    {j₁ j₂ : Nat} (hj₁ : p ≤ j₁) (hj₂ : p ≤ j₂) (hjn₁ : j₁ < n) (hjn₂ : j₂ < n)
    (hfirst : vals[j₁]! + j₁ < vals[j₂]! + j₂) :
    2 * (n - j₁) - 1 ≤ 2 * (n - j₂) - 1 := by
  contrapose! hfirst
  have := decreasing_gap hdec (show j₁ - p < (List.drop p vals).length from by
    rw [List.length_drop, hlen]; omega) (show j₂ - p < (List.drop p vals).length from by
    rw [List.length_drop, hlen]; omega) (by omega)
  grind

lemma typeI_before_typeII {vals : List Nat} {n p : Nat}
    (hlen : vals.length = n) (hnodup : vals.Nodup)
    (hvals : ∀ v ∈ vals, 1 ≤ v ∧ v ≤ n)
    (hinc : (vals.take p).Pairwise (· < ·))
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hp : p ≤ n)
    {i j : Nat} (hi : i < p) (hj : p ≤ j) (hjn : j < n)
    (horder : i + 1 ≤ vals[j]! + j - n) :
    2 * (vals[i]! - i - 1) ≤ 2 * (n - j) - 1 := by
  have h_cross : vals[i]! + j ≤ n + i :=
    cross_bound_case3 hlen hnodup hvals hinc hdec hp hi hj hjn horder
  omega

lemma typeII_before_typeI {vals : List Nat} {n p : Nat}
    (hlen : vals.length = n) (hnodup : vals.Nodup)
    (hvals : ∀ v ∈ vals, 1 ≤ v ∧ v ≤ n)
    (hinc : (vals.take p).Pairwise (· < ·))
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hp : p ≤ n)
    {i j : Nat} (hi : i < p) (hj : p ≤ j) (hjn : j < n)
    (horder : vals[j]! + j ≤ n + i) :
    2 * (n - j) - 1 ≤ 2 * (vals[i]! - i - 1) := by
  have h_cross : n + i + 1 ≤ vals[i]! + j :=
    cross_bound_case4 hlen hnodup hvals hinc hdec hp hi hj hjn horder
  grind

end Submission.AgreementsProof