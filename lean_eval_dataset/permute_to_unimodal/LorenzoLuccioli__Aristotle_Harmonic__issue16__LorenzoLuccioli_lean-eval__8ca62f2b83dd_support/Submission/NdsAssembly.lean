import Mathlib
import Submission.NdsAgreement
import Submission.AgreementSublist
import Submission.LisComplete

/-!
# Assembly: NDS to agreements and exists_good_split
-/

set_option maxHeartbeats 1600000

namespace Submission.NdsAssembly

open Submission.FillLemma
open Submission.MkUnimodal
open Submission.EncodingCorrectness
open Submission.SortedSubperm (pairLe mergeSort_perm)
open Submission.AchievabilityGlue
open Submission.NdsAgreement
open LeanEval.ProgramVerification

/-- Position bound: pairPos of a sortedPairs entry < n -/
lemma pairPos_lt_n (arr : Array Nat) (n : Nat) (harr_size : arr.size = n)
    (p : Nat × Nat) (hp : p ∈ (rawPairs arr).toList) :
    pairPos arr.size p < n := by
  have := (rawPairs_decode arr p hp).1; omega

/-
arr elements are bounded by arr.size when arr is a perm of 1..n
-/
lemma arr_bounded_of_perm {n : Nat} (arr : Array Nat)
    (harr : arr.Perm (1...=n).toArray) (harr_size : arr.size = n) :
    ∀ i, i < arr.size → arr[i]! ≤ arr.size := by
  -- Since `arr` is a permutation of `(1...=n).toArray`, its elements are also within the range `[1, n]`.
  have h_range : ∀ a ∈ arr, 1 ≤ a ∧ a ≤ n := by
    have h_range : ∀ a ∈ (1...=n).toArray, 1 ≤ a ∧ a ≤ n := by
      simp +decide [ Nat.one_le_iff_ne_zero ];
      -- The array (1...=n).toArray contains exactly the numbers from 1 to n.
      have h_array : (1...=n).toArray = Array.ofFn (fun i : Fin n => i.val + 1) := by
        refine' Array.ext _ _ <;> simp +decide [ Array.ofFn_succ ];
        exact fun i hi => add_comm _ _;
      grind;
    grind;
  grind

/-
sortedPairs entries are in rawPairs
-/
lemma sortedPairs_entry_in_rawPairs (arr : Array Nat) (i : Nat)
    (hi : i < (sortedPairs arr).toList.length) :
    (sortedPairs arr).toList[i]! ∈ (rawPairs arr).toList := by
  -- Since the lists are permutations of each other, their elements are the same. Therefore, the element at position i in the sortedPairs list must be in the rawPairs list.
  have h_perm : List.Perm (sortedPairs arr).toList (rawPairs arr).toList := by
    convert mergeSort_perm ( rawPairs arr |> Array.toList ) using 1;
  grind

/-
Given an NDS of the encoded sequence, construct S with enough agreements.
-/
lemma nds_to_agreements {n : Nat} (arr : Array Nat)
    (harr : arr.Perm (1...=n).toArray) (harr_size : arr.size = n)
    (nds_idx : List Nat)
    (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < (sortedPairs arr).size)
    (h_nondec : nds_idx.Pairwise (fun i j =>
      (sortedPairs arr).toList[i]!.2 ≤ (sortedPairs arr).toList[j]!.2)) :
    ∃ S : Finset (Fin n),
      ((List.finRange n).filter (fun i =>
        (mkUnimodal n S).toArray[i.val]'(by simp [List.toArray, mkUnimodal_size]) =
        arr[i.val]'(by omega))).length ≥ nds_idx.length := by
  -- Auxiliary facts about sortedPairs
  have h_nodup := Submission.AgreementSublist.sortedPairs_nodup arr
  have h_sp_sorted := Submission.AgreementSublist.sortedPairs_sorted arr
  have h_in_raw : ∀ i ∈ nds_idx, (sortedPairs arr).toList[i]! ∈ (rawPairs arr).toList :=
    fun i hi => sortedPairs_entry_in_rawPairs arr i (by simp; exact h_bound i hi)
  -- Build constraints list
  set cs := nds_idx.map (fun i => pairToConstraint ((sortedPairs arr).toList[i]!)) with cs_def
  have hwf : WellFormedConstraints n cs :=
    nds_wf_constraints arr n harr harr_size nds_idx h_sorted h_bound h_nondec h_nodup h_sp_sorted h_in_raw
  -- Build S
  set S := Finset.filter (fun v : Fin n => inFillSet v.val cs 0 0) Finset.univ with S_def
  use S
  -- Position bounds
  have h_pos_lt : ∀ i ∈ nds_idx, pairPos arr.size ((sortedPairs arr).toList[i]!) < n :=
    fun i hi => pairPos_lt_n arr n harr_size _ (h_in_raw i hi)
  -- Build positions
  set positions : List (Fin n) :=
    nds_idx.attach.map (fun ⟨i, hi⟩ => ⟨pairPos arr.size ((sortedPairs arr).toList[i]!), h_pos_lt i hi⟩) with pos_def
  -- positions.length = nds_idx.length
  have h_len : positions.length = nds_idx.length := by
    simp [pos_def]
  -- Positions nodup
  have h_arr_bounded := arr_bounded_of_perm arr harr harr_size
  have h_pos_nodup : positions.Nodup := by
    rw [ List.nodup_map_iff_inj_on ];
    · intro x hx y hy hxy;
      have := nds_positions_nodup arr n harr_size nds_idx h_sorted h_bound h_nondec h_nodup h_sp_sorted h_in_raw h_arr_bounded;
      rw [ List.nodup_map_iff_inj_on ] at this;
      · exact Subtype.ext <| this _ x.2 _ y.2 <| by injection hxy;
      · exact List.Pairwise.nodup h_sorted;
    · exact List.Nodup.attach ( List.Pairwise.imp_of_mem ( fun x y hxy => by aesop ) h_sorted )
  -- Each position has agreement
  have h_agree : ∀ p ∈ positions, (mkUnimodal n S).toArray[p.val]'(by simp [List.toArray, mkUnimodal_size]) = arr[p.val]'(by omega) := by
    intro p hp;
    obtain ⟨i, hi, rfl⟩ : ∃ i hi, p = ⟨pairPos arr.size (sortedPairs arr).toList[i]!, h_pos_lt i hi⟩ := by
      rw [ List.mem_map ] at hp; obtain ⟨ ⟨ i, hi ⟩, _, rfl ⟩ := hp; exact ⟨ i, by simpa using hi, rfl ⟩ ;
    -- Apply the nds_single_agreement lemma with the given parameters.
    apply nds_single_agreement arr harr harr_size cs hwf S S_def (sortedPairs arr).toList[i]! (h_in_raw i hi);
    any_goals exact List.idxOf i nds_idx;
    · grind +splitImp;
    · grind +locals;
    · exact h_pos_lt i hi
  -- Apply filter_ge_of_nodup_agreements
  calc ((List.finRange n).filter _).length
      ≥ positions.length := filter_ge_of_nodup_agreements positions h_pos_nodup _ h_agree
    _ = nds_idx.length := h_len

/-! ## Main theorem -/

theorem exists_good_split {n : Nat} (arr : Array Nat)
    (harr : arr.Perm (1...=n).toArray) (harr_size : arr.size = n) :
    ∃ S : Finset (Fin n),
      ((List.finRange n).filter (fun i =>
        (mkUnimodal n S).toArray[i.val]'(by simp [List.toArray, mkUnimodal_size]) =
        arr[i.val]'(by omega))).length ≥
      Submission.LisSound.lis (Submission.LowerBound.encodedSeq arr) := by
  have h_lis_le_exists_nds : ∃ indices : List Nat,
      indices.Pairwise (· < ·) ∧
      (∀ i ∈ indices, i < (Submission.LowerBound.encodedSeq arr).size) ∧
      indices.Pairwise (fun i j => (Submission.LowerBound.encodedSeq arr)[i]! ≤ (Submission.LowerBound.encodedSeq arr)[j]!) ∧
      indices.length = Submission.LisSound.lis (Submission.LowerBound.encodedSeq arr) := by
        apply Submission.LisComplete.lis_le_exists_nds
  convert nds_to_agreements arr harr harr_size _ _ _ _ using 1
  rotate_left
  exact h_lis_le_exists_nds.choose.map fun i => i
  · simpa using h_lis_le_exists_nds.choose_spec.1
  · convert h_lis_le_exists_nds.choose_spec.2.1 using 1
    simp +decide [Submission.LowerBound.encodedSeq]
    unfold sortedPairs; simp +decide [rawPairs]
  · have := h_lis_le_exists_nds.choose_spec.2.2.1; simp_all +decide [List.pairwise_map]
    rw [List.pairwise_iff_get] at *
    grind +suggestions
  · grind +splitImp

end Submission.NdsAssembly