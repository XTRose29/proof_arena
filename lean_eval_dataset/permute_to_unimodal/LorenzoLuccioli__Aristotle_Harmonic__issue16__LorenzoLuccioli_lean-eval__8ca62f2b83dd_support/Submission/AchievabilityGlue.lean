import Mathlib
import Submission.FillLemma
import Submission.LisComplete
import Submission.MkUnimodal
import Submission.EncodingCorrectness
import Submission.LowerBound
import Submission.SortedSubperm
import Submission.GapArith
import Submission.WFConstraints
import Submission.WFFields

/-!
# Glue: connecting NDS from patience sorting to achievability
-/

set_option maxHeartbeats 800000

namespace Submission.AchievabilityGlue

open Submission.FillLemma
open Submission.MkUnimodal
open Submission.EncodingCorrectness
open Submission.LisComplete
open Submission.LisSound
open Submission.SortedSubperm (pairLe)
open LeanEval.ProgramVerification

/-! ## Pair decoding -/

def pairPos (n : Nat) (p : Nat × Nat) : Nat :=
  if p.1 % 2 = 1 then p.1 / 2 else n - (p.2 + 1) / 2

def pairVal (p : Nat × Nat) : Nat := (p.1 + p.2) / 2

def pairToConstraint (p : Nat × Nat) : Nat × Nat × Bool :=
  (pairVal p, p.1 / 2, decide (p.1 % 2 = 1))

/-! ## rawPairs properties -/

lemma rawPairs_fst_add_snd_odd (arr : Array Nat) (p : Nat × Nat)
    (hp : p ∈ (rawPairs arr).toList) :
    (p.1 + p.2) % 2 = 1 := by
  unfold rawPairs at hp; simp_all +decide [ Finset.mem_filter ] ; grind

lemma rawPairs_decode (arr : Array Nat) (p : Nat × Nat)
    (hp : p ∈ (rawPairs arr).toList) :
    pairPos arr.size p < arr.size ∧
    arr[pairPos arr.size p]! = pairVal p + 1 := by
  unfold rawPairs at hp;
  simp +zetaDelta at *;
  rcases hp with ( ⟨ a, b, ⟨ h₁, h₂ ⟩, rfl ⟩ | ⟨ a, b, ⟨ h₁, h₂ ⟩, rfl ⟩ ) <;>
    simp_all +decide [ pairPos, pairVal ]
  · grind
  · grind +extAll

lemma sortedPairs_decode (arr : Array Nat) (p : Nat × Nat)
    (hp : p ∈ (sortedPairs arr).toList) :
    pairPos arr.size p < arr.size ∧
    arr[pairPos arr.size p]! = pairVal p + 1 :=
  rawPairs_decode arr p ((Submission.SortedSubperm.mergeSort_perm _).mem_iff.mp hp)

lemma rawPairs_same_pos_pairle_nds_eq (arr : Array Nat) (p q : Nat × Nat)
    (hp : p ∈ (rawPairs arr).toList) (hq : q ∈ (rawPairs arr).toList)
    (hpos : pairPos arr.size p = pairPos arr.size q)
    (hpairle : pairLe p q) (hnds : p.2 ≤ q.2)
    (harr_perm : ∀ i, i < arr.size → arr[i]! ≤ arr.size) :
    p = q := by
  have h_eq : arr[pairPos arr.size p]! = pairVal p + 1 ∧ arr[pairPos arr.size q]! = pairVal q + 1 := by
    exact ⟨ rawPairs_decode arr p hp |>.2, rawPairs_decode arr q hq |>.2 ⟩
  unfold pairVal at *; simp_all +decide [ Nat.add_mod, Nat.mul_mod ]
  unfold pairLe at hpairle; simp_all +decide [ Prod.ext_iff ]
  grind +suggestions

/-! ## Agreement from fill -/

lemma fill_agreement_type_I (n : Nat) (S : Finset (Fin n))
    (pos val : Nat) (hpos : pos < n) (hval : val < n)
    (h_in_S : (⟨val, hval⟩ : Fin n) ∈ S)
    (h_count : (S.filter (fun w => w.val < val)).card = pos)
    (h_pos_lt_S : pos < (S.sort (· ≤ ·)).length) :
    (mkUnimodal n S).toArray[pos]'(by simp [List.toArray, mkUnimodal_size]; exact hpos) = val + 1 := by
  convert congr_arg ( fun x : Fin n => ( x : ℕ ) + 1 ) ( sort_at_count S _ h_in_S _ h_count _ ) using 1
  swap; convert h_pos_lt_S using 1; unfold mkUnimodal; grind

lemma fill_agreement_type_II (n : Nat) (S : Finset (Fin n))
    (pos val : Nat) (hpos : pos < n) (hval : val < n)
    (h_not_in_S : (⟨val, hval⟩ : Fin n) ∉ S)
    (h_compl_count : ((Finset.univ \ S).filter (fun w : Fin n => w.val < val)).card = n - 1 - pos)
    (h_pos_ge_S : (S.sort (· ≤ ·)).length ≤ pos) :
    (mkUnimodal n S).toArray[pos]'(by simp [List.toArray, mkUnimodal_size]; exact hpos) = val + 1 := by
  convert fill_agreement_type_I n ( Finset.univ \ S ) ( n - 1 - pos ) val _ _ _ _ using 1 <;> norm_num
  all_goals norm_num [ mkUnimodal ]
  any_goals omega
  rw [ List.getElem_append, List.getElem_append ] ; norm_num
  simp_all +decide [ Finset.card_sdiff, Finset.card_singleton ]; grind

/-! ## Key arithmetic lemmas -/

/-- pairLe + NDS gives strictly increasing f+s. -/
lemma pairle_nds_sum_lt (p q : Nat × Nat)
    (hpairle : pairLe p q) (hnds : p.2 ≤ q.2) (hne : p ≠ q) :
    p.1 + p.2 < q.1 + q.2 := by
  cases hpairle <;> simp_all +decide [ pairLe ]; grind

/-
val < n for sortedPairs entries when arr is perm of 1..n.
-/
lemma pairVal_lt_of_perm (arr : Array Nat) (n : Nat) (p : Nat × Nat)
    (harr : arr.Perm (1...=n).toArray) (harr_size : arr.size = n)
    (hp : p ∈ (sortedPairs arr).toList) :
    pairVal p < n := by
  -- By `sortedPairs_decode`, we know that `arr[pairPos arr.size p]! = pairVal p + 1`.
  obtain ⟨h_pair_pos, h_arr_val⟩ := sortedPairs_decode arr p hp;
  have h_arr_le_n : ∀ i, i < arr.size → arr[i]! ≤ n := by
    have h_arr_le_n : ∀ x ∈ arr, x ≤ n := by
      intro x hx
      have h_mem : x ∈ (1...=n).toArray := by
        grind;
      simp +zetaDelta at *;
      rw [ List.mem_toArray ] at h_mem;
      rw [ List.mem_iff_get ] at h_mem;
      obtain ⟨ k, hk ⟩ := h_mem; rw [ ← hk ] ;
      simp +decide [ List.get ];
      linarith [ Fin.is_lt k, show ( 1...=n ).toArray.toList.length = n from by simp +decide [ List.length ] ];
    cases arr ; aesop;
  grind

/-- WellFormedConstraints for constraints derived from NDS of sortedPairs. -/
lemma nds_wf_constraints (arr : Array Nat) (n : Nat)
    (harr : arr.Perm (1...=n).toArray) (harr_size : arr.size = n)
    (nds_idx : List Nat)
    (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < (sortedPairs arr).size)
    (h_nondec : nds_idx.Pairwise (fun i j =>
      (sortedPairs arr).toList[i]!.2 ≤ (sortedPairs arr).toList[j]!.2))
    (h_nodup : (sortedPairs arr).toList.Nodup)
    (h_sp_sorted : (sortedPairs arr).toList.Pairwise pairLe)
    (h_in_raw : ∀ i ∈ nds_idx, (sortedPairs arr).toList[i]! ∈ (rawPairs arr).toList) :
    WellFormedConstraints n
      (nds_idx.map (fun i => pairToConstraint ((sortedPairs arr).toList[i]!))) :=
  ⟨WFFields.wf_vals_lt_n arr n harr harr_size nds_idx h_bound h_in_raw,
   WFFields.wf_vals_increasing arr n nds_idx h_sorted h_bound h_nondec h_nodup h_sp_sorted h_in_raw,
   WFFields.wf_counts_le_vals arr nds_idx,
   WFFields.wf_gap_lower arr nds_idx h_sorted h_bound h_nondec h_nodup h_sp_sorted h_in_raw,
   WFFields.wf_gap_upper arr nds_idx h_sorted h_bound h_nondec h_nodup h_sp_sorted h_in_raw⟩

/-! ## Connecting NDS to S with agreement positions -/

/-
Given a list of positions with agreements and no duplicates,
    the filter length is at least the list length.
-/
lemma filter_ge_of_nodup_agreements {n : Nat}
    (positions : List (Fin n)) (h_nodup : positions.Nodup)
    (f : Fin n → Prop) [DecidablePred f]
    (h_agree : ∀ p ∈ positions, f p) :
    ((List.finRange n).filter (fun i => f i)).length ≥ positions.length := by
  have h_filter : List.toFinset positions ⊆ List.toFinset (List.filter (fun i => f i) (List.finRange n)) := by
    intro p hp; aesop;
  exact le_trans ( by rw [ List.toFinset_card_of_nodup h_nodup ] ) ( List.toFinset_card_le _ |> le_trans ( Finset.card_mono h_filter ) )

end Submission.AchievabilityGlue