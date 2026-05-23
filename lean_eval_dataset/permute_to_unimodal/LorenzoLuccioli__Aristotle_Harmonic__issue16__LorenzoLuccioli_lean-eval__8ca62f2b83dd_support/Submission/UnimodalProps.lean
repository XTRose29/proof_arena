import Mathlib

/-!
# Properties of unimodal permutations

Key structural lemmas for strictly increasing/decreasing lists.
-/

namespace Submission.UnimodalProps

/-
In a strictly increasing list of positive naturals, the i-th element is ≥ i + first_element
-/
lemma increasing_lower_bound {l : List Nat} (hpw : l.Pairwise (· < ·))
    {i : Nat} (hi : i < l.length) :
    l[0]'(by omega) + i ≤ l[i] := by
  induction i <;> simp_all +arith +decide [ List.pairwise_iff_get ];
  exact lt_of_le_of_lt ( by solve_by_elim [ Nat.lt_of_succ_lt ] ) ( hpw ⟨ _, by linarith ⟩ ⟨ _, by linarith ⟩ ( Nat.lt_succ_self _ ) )

/-
In a strictly increasing list with all elements ≥ 1, the i-th element is ≥ i + 1
-/
lemma increasing_ge_succ {l : List Nat} (hpw : l.Pairwise (· < ·))
    (hmin : ∀ x ∈ l, 1 ≤ x) {i : Nat} (hi : i < l.length) :
    i + 1 ≤ l[i] := by
  induction' i with i ih;
  · exact hmin _ ( by simp );
  · exact Nat.lt_of_le_of_lt ( ih ( Nat.lt_of_succ_lt hi ) ) ( List.pairwise_iff_get.mp hpw _ _ ( by aesop ) )

/-
In a strictly decreasing list with all elements ≥ 1, l[i] ≥ l.length - i
-/
lemma decreasing_ge {l : List Nat} (hpw : l.Pairwise (· > ·))
    (hmin : ∀ x ∈ l, 1 ≤ x) {i : Nat} (hi : i < l.length) :
    l.length - i ≤ l[i] := by
  induction' i with i ih generalizing l;
  · rcases l with ( _ | ⟨ x, _ | ⟨ y, l ⟩ ⟩ ) <;> simp_all +arith +decide;
    have h_ind : ∀ i < l.length, l[i]! ≥ l.length - i := by
      intro i hi;
      induction' h : l.length - i using Nat.strong_induction_on with k ih generalizing i;
      by_cases h_cases : i + 1 < l.length;
      · grind +suggestions;
      · cases lt_or_eq_of_le ( Nat.le_of_not_lt h_cases ) <;> aesop;
    rcases l with ( _ | ⟨ z, l ⟩ ) <;> simp_all +arith +decide;
    · linarith;
    · grind +splitIndPred;
  · grind +splitIndPred

/-
Consecutive strictly increasing elements have a-i non-decreasing:
    if i < j and l[i] < l[j] with i, j positions in an increasing list,
    then l[j] - j ≥ l[i] - i
-/
lemma increasing_gap_nondec {l : List Nat} (hpw : l.Pairwise (· < ·))
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l[i] - i ≤ l[j] - j := by
  -- By increasing_lower_bound applied to the sublist starting at position i: l[j] ≥ l[i] + (j - i).
  have h_sublist : l[j] ≥ l[i] + (j - i) := by
    induction hij <;> simp_all +arith +decide;
    · exact List.pairwise_iff_get.mp hpw _ _ ( by aesop );
    · have := List.pairwise_iff_get.mp hpw;
      rename_i k hk₁ hk₂;
      specialize this ⟨ k, by linarith ⟩ ⟨ k + 1, by linarith ⟩ ; simp_all +decide [ Nat.succ_sub ( by linarith : i ≤ k ) ];
      grind;
  omega

/-
In a strictly decreasing list, if i < j then l[i] - l[j] ≥ j - i
-/
lemma decreasing_gap {l : List Nat} (hpw : l.Pairwise (· > ·))
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i < j) :
    l[j] + (j - i) ≤ l[i] := by
  induction hij <;> simp_all +arith +decide [ List.pairwise_cons ];
  · exact List.pairwise_iff_get.mp hpw _ _ ( by aesop );
  · grind +suggestions

end Submission.UnimodalProps