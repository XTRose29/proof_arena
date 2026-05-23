import Mathlib
import ChallengeDeps
import Submission.SortedSubperm
import Submission.EncodingCorrectness
import Submission.UnimodalProps
import Submission.UnimodalCounting
import Submission.AgreementsProof
import Submission.AgreementsNDS

/-!
# Agreement sublist construction

Constructs the sublist of sortedPairs from agreement positions.
-/

namespace Submission.AgreementSublist

open LeanEval.ProgramVerification
open Submission.SortedSubperm
open Submission.EncodingCorrectness
open Submission.UnimodalProps
open Submission.UnimodalCounting
open Submission.AgreementsProof

/-- For position k in the increasing part of a unimodal permutation of 1..n,
    x[k] ≥ k+1. -/
lemma unimodal_inc_ge {x : Array Nat} {n : Nat}
    (hx : x.Perm (1...=n).toArray) (hx_size : x.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hinc : b.toList.Pairwise (· < ·))
    {k : Nat} (hk : k < b.size) (hkn : k < n) :
    k + 1 ≤ x[k]'(by omega) := by
  have h_b_ge : k + 1 ≤ b[k] := by
    have h_b_ge : ∀ v ∈ b, 1 ≤ v := by
      intro v hv
      have h_perm : v ∈ (1...=n).toArray := by
        grind +suggestions;
      simp_all +decide [ Finset.mem_range, List.mem_toFinset ];
      rw [ List.mem_toArray ] at h_perm;
      rw [ List.mem_iff_get ] at h_perm;
      obtain ⟨ i, hi ⟩ := h_perm; rw [ ← hi ] ;
      simp +decide [ List.get ];
    convert increasing_ge_succ hinc ( fun v hv => h_b_ge v <| by simpa using hv ) ( by simpa using hk ) using 1;
  grind

/-- For position k in the decreasing part of a unimodal permutation of 1..n,
    x[k] + k ≥ n. -/
lemma unimodal_dec_ge {x : Array Nat} {n : Nat}
    (hx : x.Perm (1...=n).toArray) (hx_size : x.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hdec : b'.toList.Pairwise (· > ·))
    {k : Nat} (hk : b.size ≤ k) (hkn : k < n) :
    n ≤ x[k]'(by omega) + k := by
  have h_perm : ∀ v ∈ b'.toList, 1 ≤ v := by
    intro v hv
    have hv_perm : v ∈ (1...=n).toArray := by
      grind +splitImp;
    simp_all +decide [ Nat.one_le_iff_ne_zero ];
    rw [ List.mem_toArray ] at hv_perm;
    rw [ List.mem_iff_get ] at hv_perm; aesop;
  have h_b'_ge : b'[k - b.size]'(by grind) ≥ b'.size - (k - b.size) := by
    all_goals generalize_proofs at *;
    exact decreasing_ge hdec h_perm ‹_›
  generalize_proofs at *;
  grind

/-- rawPairs have no duplicate entries. -/
lemma rawPairs_nodup (arr : Array Nat) : (rawPairs arr).toList.Nodup := by
  simp +decide [ rawPairs ];
  rw [ List.nodup_append ];
  constructor;
  · rw [ List.nodup_map_iff_inj_on ];
    · simp +contextual [ Prod.ext_iff ];
      intros; omega;
    · refine' List.Nodup.filter _ _;
      exact List.nodup_iff_injective_get.mpr ( by intros a b; aesop );
  · rw [ List.nodup_map_iff_inj_on ];
    · grind +splitIndPred;
    · refine' List.Nodup.filter _ _;
      exact List.nodup_iff_injective_get.mpr ( by intros a b; aesop )

/-- sortedPairs is sorted -/
lemma sortedPairs_sorted (arr : Array Nat) :
    (sortedPairs arr).toList.Pairwise pairLe := by
  convert mergeSort_pairwise _ using 1

/-- sortedPairs is nodup (since rawPairs is nodup and mergeSort is a perm) -/
lemma sortedPairs_nodup (arr : Array Nat) : (sortedPairs arr).toList.Nodup :=
  (mergeSort_perm (rawPairs arr).toList).nodup_iff.mpr (rawPairs_nodup arr)

/-- Any element of rawPairs is in sortedPairs -/
lemma mem_rawPairs_sortedPairs (arr : Array Nat) (p : Nat × Nat) :
    p ∈ (rawPairs arr).toList → p ∈ (sortedPairs arr).toList :=
  (mergeSort_perm (rawPairs arr).toList).mem_iff.mpr

/-! ## Helper: encoding agreement pairs -/

/-- The encoded pair for an agreement position k. -/
noncomputable def agreePair (arr : Array Nat) (n p k : Nat) : Nat × Nat :=
  if k < p then
    (2 * k + 1, 2 * (arr[k]! - k - 1))
  else
    (2 * (arr[k]! + k - n), 2 * (n - k) - 1)

/-
Each agreement pair at position k < p (increasing part) is in rawPairs.
-/
lemma agreePair_inc_mem_rawPairs (arr : Array Nat) {n p k : Nat}
    (harr_size : arr.size = n) (hk : k < p) (hkn : k < n)
    (hfilt : k + 1 ≤ arr[k]'(by omega)) :
    agreePair arr n p k ∈ (rawPairs arr).toList := by
  unfold agreePair;
  convert pair_in_rawPairs_filter1 arr k ( by linarith ) ( by linarith ) using 1;
  grind +suggestions

/-
Each agreement pair at position k ≥ p (decreasing part) is in rawPairs.
-/
lemma agreePair_dec_mem_rawPairs (arr : Array Nat) {n p k : Nat}
    (harr_size : arr.size = n) (hk : p ≤ k) (hkn : k < n)
    (hfilt : n ≤ arr[k]'(by omega) + k) :
    agreePair arr n p k ∈ (rawPairs arr).toList := by
  unfold agreePair; split_ifs <;> simp_all +decide [ pair_in_rawPairs_filter2 ] ;
  · grind;
  · convert pair_in_rawPairs_filter2 arr k ( by linarith ) ( by linarith ) using 1;
    · aesop;
    · grind

/-
Case 1: Both Type I (i < p, j < p).
-/
lemma nds_case_II {arr x : Array Nat} {n p : Nat}
    (hx : x.Perm (1...=n).toArray)
    (hx_size : x.size = n) (harr_size : arr.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hinc : b.toList.Pairwise (· < ·))
    (hp : p = b.size)
    {i j : Nat} (hi : i < n) (hj : j < n)
    (hxi : x[i]'(by omega) = arr[i]'(by omega))
    (hxj : x[j]'(by omega) = arr[j]'(by omega))
    (hip : i < p) (hjp : j < p)
    (hpairle : pairLe (agreePair arr n p i) (agreePair arr n p j)) :
    (agreePair arr n p i).2 ≤ (agreePair arr n p j).2 := by
  unfold pairLe at hpairle;
  unfold agreePair at *;
  split_ifs at * ; simp_all +decide [ Prod.lex_def ];
  rcases hpairle with ( ⟨ rfl, h ⟩ | h | ⟨ rfl, h ⟩ ) <;> simp_all +decide [ Nat.sub_sub ];
  · omega;
  · have := increasing_gap_nondec hinc ( show i < List.length b.toList from by simpa ) ( show j < List.length b.toList from by simpa ) h; simp_all +decide [ List.getElem?_eq_getElem ] ;
    omega

/-
Case 2: Both Type II (i ≥ p, j ≥ p).
-/
lemma nds_case_DD {arr x : Array Nat} {n p : Nat}
    (hx : x.Perm (1...=n).toArray)
    (hx_size : x.size = n) (harr_size : arr.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hdec : b'.toList.Pairwise (· > ·))
    (hp : p = b.size)
    {i j : Nat} (hi : i < n) (hj : j < n)
    (hxi : x[i]'(by omega) = arr[i]'(by omega))
    (hxj : x[j]'(by omega) = arr[j]'(by omega))
    (hip : ¬(i < p)) (hjp : ¬(j < p))
    (hfilt_i : n ≤ arr[i]'(by omega) + i)
    (hfilt_j : n ≤ arr[j]'(by omega) + j)
    (hpairle : pairLe (agreePair arr n p i) (agreePair arr n p j)) :
    (agreePair arr n p i).2 ≤ (agreePair arr n p j).2 := by
  unfold pairLe at hpairle;
  unfold agreePair at *;
  split_ifs at * ; simp_all +decide [ Prod.lex_def ];
  contrapose! hpairle;
  have := decreasing_gap ( show List.Pairwise ( · > · ) ( b'.toList ) from hdec ) ( show i - b.size < b'.size from by
                                                                                      grind ) ( show j - b.size < b'.size from by
                                                                                                                                  grind ) ( show i - b.size ≤ j - b.size from by
                                                                                                                                                                              lia ) ; simp_all +decide [ Nat.sub_sub ];
  exact ⟨ fun h => by omega, by omega, fun h => by omega ⟩

/-
Case 3: Type I then Type II (i < p, j ≥ p).
-/
lemma nds_case_ID {arr x : Array Nat} {n p : Nat}
    (hx : x.Perm (1...=n).toArray) (harr : arr.Perm (1...=n).toArray)
    (hx_size : x.size = n) (harr_size : arr.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hinc : b.toList.Pairwise (· < ·))
    (hdec : b'.toList.Pairwise (· > ·))
    (hp : p = b.size)
    {i j : Nat} (hi : i < n) (hj : j < n)
    (hxi : x[i]'(by omega) = arr[i]'(by omega))
    (hxj : x[j]'(by omega) = arr[j]'(by omega))
    (hip : i < p) (hjp : ¬(j < p))
    (hfilt_j : n ≤ arr[j]'(by omega) + j)
    (hpairle : pairLe (agreePair arr n p i) (agreePair arr n p j)) :
    (agreePair arr n p i).2 ≤ (agreePair arr n p j).2 := by
  -- Since x is a permutation of 1..n, we can convert the array x to a list and apply the lemmas.
  have hx_list : x.toList.Perm (List.range' 1 n) := by
    convert hx.toList using 1;
    refine' List.ext_get _ _ <;> simp +decide;
  have := Submission.AgreementsProof.typeI_before_typeII ( show x.toList.length = n from by simpa [ hx_size ] ) ( show x.toList.Nodup from by
                                                                                                                    exact hx_list.nodup_iff.mpr ( by simp +decide [ List.nodup_range' ] ) ) ( show ∀ v ∈ x.toList, 1 ≤ v ∧ v ≤ n from by
                                                                                                                                                          grind ) ( show ( x.toList.take p ).Pairwise ( · < · ) from by
                                                                                                                                                                                                              simp_all +decide [ List.take_append ] ) ( show ( x.toList.drop p ).Pairwise ( · > · ) from by
                                                                                                                                                                                                                                                                            simp_all +decide [ List.drop_append ] ) ( show p ≤ n from by
                                                                                                                                                                                                                                                                                                                                          grind ) ( show i < p from by
                                                                                                                                                                                                                                                                                                                                                                        linarith ) ( show p ≤ j from by
                                                                                                                                                                                                                                                                                                                                                                                                    linarith ) ( show j < n from by
                                                                                                                                                                                                                                                                                                                                                                                                                                  linarith ) ( show i + 1 ≤ x.toList[j]! + j - n from by
                                                                                                                                                                                                                                                                                                                                                                                                                                                              unfold agreePair at hpairle; simp_all +decide [ pairLe ] ;
                                                                                                                                                                                                                                                                                                                                                                                                                                                              grind +splitIndPred );
  grind +locals

/-
Case 4: Type II then Type I (i ≥ p, j < p).
-/
lemma nds_case_DI {arr x : Array Nat} {n p : Nat}
    (hx : x.Perm (1...=n).toArray) (harr : arr.Perm (1...=n).toArray)
    (hx_size : x.size = n) (harr_size : arr.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hinc : b.toList.Pairwise (· < ·))
    (hdec : b'.toList.Pairwise (· > ·))
    (hp : p = b.size)
    {i j : Nat} (hi : i < n) (hj : j < n)
    (hxi : x[i]'(by omega) = arr[i]'(by omega))
    (hxj : x[j]'(by omega) = arr[j]'(by omega))
    (hip : ¬(i < p)) (hjp : j < p)
    (hfilt_i : n ≤ arr[i]'(by omega) + i)
    (hpairle : pairLe (agreePair arr n p i) (agreePair arr n p j)) :
    (agreePair arr n p i).2 ≤ (agreePair arr n p j).2 := by
  have h_lex : arr[i]! + i ≤ n + j := by
    unfold pairLe at hpairle;
    unfold agreePair at hpairle;
    grind;
  have h_vals : x.toList.Nodup ∧ (∀ v ∈ x.toList, 1 ≤ v ∧ v ≤ n) := by
    have h_vals : x.toList.Perm (List.range' 1 n) := by
      convert hx.toList using 1;
      refine' List.ext_get _ _ <;> simp +decide [ List.get ];
    grind +extAll;
  have := typeII_before_typeI ( show x.toList.length = n from by simp +decide [ hx_size ] ) h_vals.1 h_vals.2 ( show ( x.toList.take p ).Pairwise ( · < · ) from by
                                                                                                                  aesop ) ( show ( x.toList.drop p ).Pairwise ( · > · ) from by
                                                                                                                                                                                simp_all +decide [ List.drop_append ] ) ( by
                                                                                                                                                                                grind ) ( show j < p from hjp ) ( show p ≤ i from by
                                                                                                                                                                                                                                                                                  linarith ) ( by
                                                                                                                                                                                                                                                                                  grind ) ( by
                                                                                                                                                                                                                                                                                  grind ) ; simp_all +decide [ agreePair ] ;
  grind +qlia

/-- For any two agreement pairs, pairLe ordering implies NDS of second components. -/
lemma agreePairs_pairLe_nds {arr x : Array Nat} {n p : Nat}
    (hx : x.Perm (1...=n).toArray) (harr : arr.Perm (1...=n).toArray)
    (hx_size : x.size = n) (harr_size : arr.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hinc : b.toList.Pairwise (· < ·))
    (hdec : b'.toList.Pairwise (· > ·))
    (hp : p = b.size)
    {i j : Nat} (hi : i < n) (hj : j < n)
    (hxi : x[i]'(by omega) = arr[i]'(by omega))
    (hxj : x[j]'(by omega) = arr[j]'(by omega))
    (hfilt_i : if i < p then i + 1 ≤ arr[i]'(by omega) else n ≤ arr[i]'(by omega) + i)
    (hfilt_j : if j < p then j + 1 ≤ arr[j]'(by omega) else n ≤ arr[j]'(by omega) + j)
    (hpairle : pairLe (agreePair arr n p i) (agreePair arr n p j)) :
    (agreePair arr n p i).2 ≤ (agreePair arr n p j).2 := by
  have get_filt_i : ¬(i < p) → n ≤ arr[i]'(by omega) + i := by split_ifs at hfilt_i <;> omega
  have get_filt_j : ¬(j < p) → n ≤ arr[j]'(by omega) + j := by split_ifs at hfilt_j <;> omega
  by_cases hip : i < p <;> by_cases hjp : j < p
  · exact nds_case_II hx hx_size harr_size b b' hx_eq hinc hp hi hj hxi hxj hip hjp hpairle
  · exact nds_case_ID hx harr hx_size harr_size b b' hx_eq hinc hdec hp hi hj hxi hxj hip hjp (get_filt_j hjp) hpairle
  · exact nds_case_DI hx harr hx_size harr_size b b' hx_eq hinc hdec hp hi hj hxi hxj hip hjp (get_filt_i hip) hpairle
  · exact nds_case_DD hx hx_size harr_size b b' hx_eq hdec hp hi hj hxi hxj hip hjp (get_filt_i hip) (get_filt_j hjp) hpairle

/-
Agreement pairs for distinct positions are distinct.
-/
lemma agreePair_injective (arr : Array Nat) {n p : Nat}
    (harr_size : arr.size = n)
    {i j : Nat} (hi : i < n) (hj : j < n) (hij : i ≠ j)
    (hfilt_i : if i < p then i + 1 ≤ arr[i]'(by omega) else n ≤ arr[i]'(by omega) + i)
    (hfilt_j : if j < p then j + 1 ≤ arr[j]'(by omega) else n ≤ arr[j]'(by omega) + j) :
    agreePair arr n p i ≠ agreePair arr n p j := by
  unfold agreePair;
  grind

end Submission.AgreementSublist