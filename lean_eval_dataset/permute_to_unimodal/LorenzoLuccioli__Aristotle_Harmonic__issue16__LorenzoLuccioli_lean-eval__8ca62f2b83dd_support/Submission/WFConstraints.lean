import Mathlib
import Submission.FillLemma
import Submission.EncodingCorrectness
import Submission.SortedSubperm
import Submission.GapArith

/-!
# WellFormedConstraints from NDS pairs - decomposed helpers
-/

set_option maxHeartbeats 800000

namespace Submission.WFConstraints

open Submission.FillLemma
open Submission.EncodingCorrectness
open Submission.SortedSubperm (pairLe)
open Submission.GapArith

/-- Helper: extract pairLe between consecutive NDS entries. -/
lemma nds_consecutive_pairle (sp_list : List (Nat × Nat))
    (h_sp_sorted : sp_list.Pairwise pairLe)
    (nds_idx : List Nat) (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < sp_list.length)
    (k : Nat) (hk : k + 1 < nds_idx.length) :
    pairLe (sp_list[nds_idx[k]!]!) (sp_list[nds_idx[k + 1]!]!) := by
  have h_pairwise : ∀ (i j : ℕ), i < j → i < sp_list.length → j < sp_list.length → pairLe sp_list[i]! sp_list[j]! := by
    intros i j hij hi hj
    have h_pairwise : ∀ (l : List (ℕ × ℕ)), List.Pairwise pairLe l → ∀ (i j : ℕ), i < j → i < l.length → j < l.length → pairLe l[i]! l[j]! := by
      intros l hl i j hij hi hj
      induction' l with hd tl ih generalizing i j;
      · contradiction;
      · rcases i with ( _ | i ) <;> rcases j with ( _ | j ) <;> simp_all +decide [ List.pairwise_cons ];
    exact h_pairwise sp_list h_sp_sorted i j hij hi hj;
  have h_pairwise : nds_idx[k]! < nds_idx[k + 1]! := by
    have := List.pairwise_iff_get.mp h_sorted;
    convert this ⟨ k, by linarith ⟩ ⟨ k + 1, by linarith ⟩ ( Nat.lt_succ_self _ ) using 1 <;> simp +decide [ List.getElem?_eq_getElem, hk ];
    rw [ List.getElem?_eq_getElem ] ; aesop;
  grind

lemma nds_consecutive_ne (sp_list : List (Nat × Nat))
    (h_nodup : sp_list.Nodup)
    (nds_idx : List Nat) (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < sp_list.length)
    (k : Nat) (hk : k + 1 < nds_idx.length) :
    sp_list[nds_idx[k]!]! ≠ sp_list[nds_idx[k + 1]!]! := by
  grind +suggestions

lemma nds_consecutive_snd_le (sp_list : List (Nat × Nat))
    (nds_idx : List Nat)
    (h_nondec : nds_idx.Pairwise (fun i j => sp_list[i]!.2 ≤ sp_list[j]!.2))
    (k : Nat) (hk : k + 1 < nds_idx.length) :
    sp_list[nds_idx[k]!]!.2 ≤ sp_list[nds_idx[k + 1]!]!.2 := by
  rw [ List.pairwise_iff_get ] at h_nondec;
  convert h_nondec ⟨ k, by linarith ⟩ ⟨ k + 1, by linarith ⟩ ( Nat.lt_succ_self k ) using 1;
  · grind
  · grind

lemma nds_consecutive_fst_le (sp_list : List (Nat × Nat))
    (h_sp_sorted : sp_list.Pairwise pairLe)
    (nds_idx : List Nat) (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < sp_list.length)
    (h_nondec : nds_idx.Pairwise (fun i j => sp_list[i]!.2 ≤ sp_list[j]!.2))
    (k : Nat) (hk : k + 1 < nds_idx.length) :
    sp_list[nds_idx[k]!]!.1 ≤ sp_list[nds_idx[k + 1]!]!.1 := by
  have h_pairLe : pairLe (sp_list[nds_idx[k]!]!) (sp_list[nds_idx[k + 1]!]!) := by
    apply nds_consecutive_pairle sp_list h_sp_sorted nds_idx h_sorted h_bound k hk;
  cases h_pairLe <;> simp_all +decide [ Prod.lex_def ]; grind

lemma rawPairs_same_fst_eq_or_even (arr : Array Nat) (p q : Nat × Nat)
    (hp : p ∈ (rawPairs arr).toList) (hq : q ∈ (rawPairs arr).toList)
    (hfst : p.1 = q.1) :
    p = q ∨ p.1 % 2 = 0 := by
  contrapose! hfst; simp_all +decide [ rawPairs ] ; grind +extAll

lemma rawPairs_same_fst_diff_snd (arr : Array Nat) (p q : Nat × Nat)
    (hp : p ∈ (rawPairs arr).toList) (hq : q ∈ (rawPairs arr).toList)
    (hfst : p.1 = q.1) (hne : p ≠ q) :
    p.2 ≠ q.2 := by
  grind

end Submission.WFConstraints
