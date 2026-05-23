import Mathlib
import Submission.FillLemma
import Submission.MkUnimodal
import Submission.EncodingCorrectness
import Submission.SortedSubperm
import Submission.GapArith
import Submission.WFConstraints
import Submission.WFFields
import Submission.AchievabilityGlue

/-!
# Single NDS entry agreement and position distinctness
-/

set_option maxHeartbeats 1200000

namespace Submission.NdsAgreement

open Submission.FillLemma
open Submission.MkUnimodal
open Submission.EncodingCorrectness
open Submission.SortedSubperm (pairLe mergeSort_perm)
open Submission.AchievabilityGlue
open LeanEval.ProgramVerification

/-! ## Finset counting helpers -/

/-- Complement count below val = val - S_count -/
lemma compl_count_below_val {n : Nat} (val count : Nat)
    (hval : val < n) (hcount : count ≤ val)
    (S : Finset (Fin n))
    (h_count : (S.filter (fun w => w.val < val)).card = count) :
    ((Finset.univ \ S).filter (fun w : Fin n => w.val < val)).card = val - count := by
  have h_card : (Finset.filter (fun w : Fin n => w.val < val) Finset.univ).card = val := by
    rw [ Finset.card_eq_of_bijective ];
    use fun i hi => Fin.mk i (by linarith);
    · grind;
    · grind;
    · grind;
  have h_split : (Finset.filter (fun w : Fin n => w.val < val) Finset.univ).card = (Finset.filter (fun w : Fin n => w.val < val) S).card + (Finset.filter (fun w : Fin n => w.val < val) (Finset.univ \ S)).card := by
    rw [ ← Finset.card_union_of_disjoint ];
    · congr with w ; by_cases hw : w ∈ S <;> aesop;
    · exact Finset.disjoint_left.mpr fun x hx₁ hx₂ => Finset.mem_sdiff.mp ( Finset.mem_filter.mp hx₂ |>.1 ) |>.2 ( Finset.mem_filter.mp hx₁ |>.1 );
  grind

/-- If val ∈ S and count of S below val = pos, then pos < S.sort.length -/
lemma sort_len_gt_pos {n : Nat} (S : Finset (Fin n))
    (val pos : Nat) (hval : val < n)
    (h_in_S : (⟨val, hval⟩ : Fin n) ∈ S)
    (h_count : (S.filter (fun w => w.val < val)).card = pos) :
    pos < (S.sort (· ≤ ·)).length := by
  simp [h_count, Finset.length_sort];
  exact h_count ▸ Finset.card_lt_card ( Finset.filter_ssubset.mpr ⟨ ⟨ val, hval ⟩, h_in_S, by simpa ⟩ )

/-- Sort length bound for Type II -/
lemma sort_len_le_pos {n : Nat} (S : Finset (Fin n))
    (val pos count : Nat) (hval : val < n) (hpos : pos < n)
    (h_not_in_S : (⟨val, hval⟩ : Fin n) ∉ S)
    (h_count : (S.filter (fun w => w.val < val)).card = count)
    (h_bound : count + n ≤ val + 1 + pos) :
    (S.sort (· ≤ ·)).length ≤ pos := by
  simp +zetaDelta at *;
  have h_card_le : S.card ≤ (S.filter (fun w => w.val < val)).card + (S.filter (fun w => w.val > val)).card := by
    rw [ ← Finset.card_union_of_disjoint ];
    · exact Finset.card_le_card fun x hx => by cases lt_or_gt_of_ne ( show ( x : ℕ ) ≠ val from fun h => h_not_in_S <| by aesop ) <;> aesop;
    · exact Finset.disjoint_filter.mpr fun _ _ _ _ => by linarith;
  have h_card_le' : (S.filter (fun w => w.val > val)).card ≤ (Finset.filter (fun w : Fin n => w.val > val) Finset.univ).card := by
    exact Finset.card_le_card fun x hx => by aesop;
  rw [ show ( Finset.filter ( fun w : Fin n => ( w : ℕ ) > val ) Finset.univ ).card = n - val - 1 from ?_ ] at h_card_le';
  · omega;
  · rw [ show ( Finset.filter ( fun w : Fin n => ( w : ℕ ) > val ) Finset.univ ) = Finset.Ioi ⟨ val, hval ⟩ by ext; aesop ] ; simp +decide [ Nat.sub_sub ];
    ring

/-- S count below val from fill -/
lemma fill_count_below_val {n : Nat} (cs : List (Nat × Nat × Bool))
    (hwf : WellFormedConstraints n cs)
    (S : Finset (Fin n))
    (hS : S = Finset.filter (fun v : Fin n => inFillSet v.val cs 0 0) Finset.univ)
    (k : Nat) (hk : k < cs.length) :
    (S.filter (fun w => w.val < cs[k]!.1)).card = cs[k]!.2.1 := by
  have := inFillSet_count_below n cs hwf k hk
  rw [hS]
  simp only [Finset.filter_filter]
  convert this using 2

/-! ## Main agreement lemma -/

/-- For a single NDS entry at index k, mkUnimodal agrees with arr at the decoded position. -/
lemma nds_single_agreement {n : Nat} (arr : Array Nat)
    (harr : arr.Perm (1...=n).toArray) (harr_size : arr.size = n)
    (cs : List (Nat × Nat × Bool))
    (hwf : WellFormedConstraints n cs)
    (S : Finset (Fin n))
    (hS : S = Finset.filter (fun v : Fin n => inFillSet v.val cs 0 0) Finset.univ)
    (p : Nat × Nat)
    (hp_raw : p ∈ (rawPairs arr).toList)
    (k : Nat) (hk : k < cs.length)
    (h_cs_k : cs[k]! = pairToConstraint p) :
    let pos := pairPos arr.size p
    let val := pairVal p
    (hpos : pos < n) →
    (mkUnimodal n S).toArray[pos]'(by simp [List.toArray, mkUnimodal_size]; exact hpos) =
    arr[pos]'(by rw [harr_size]; exact hpos) := by
  intro pos val hpos
  show (mkUnimodal n S).toArray[pos]'_ = arr[pos]'_
  -- Extract key facts
  have h_odd_sum : (p.1 + p.2) % 2 = 1 := rawPairs_fst_add_snd_odd arr p hp_raw
  have h_decode := rawPairs_decode arr p hp_raw
  have h_pos_lt : pairPos arr.size p < arr.size := h_decode.1
  have h_arr_eq : arr[pairPos arr.size p]! = pairVal p + 1 := h_decode.2
  have hp_sp : p ∈ (sortedPairs arr).toList :=
    (mergeSort_perm _).mem_iff.mpr hp_raw
  have h_val_lt_n : pairVal p < n := pairVal_lt_of_perm arr n p harr harr_size hp_sp
  -- Extract constraint fields
  have h_cs_val : cs[k]!.1 = pairVal p := by
    unfold pairToConstraint at h_cs_k; simp [h_cs_k]
  have h_cs_count : cs[k]!.2.1 = p.1 / 2 := by
    unfold pairToConstraint at h_cs_k; simp [h_cs_k]
  have h_cs_inc : cs[k]!.2.2 = decide (p.1 % 2 = 1) := by
    unfold pairToConstraint at h_cs_k; simp [h_cs_k]
  -- InFillSet at the constraint value
  have h_fill_at : inFillSet (pairVal p) cs 0 0 = decide (p.1 % 2 = 1) := by
    rw [← h_cs_val, ← h_cs_inc]
    exact inFillSet_at_constraint cs hwf.vals_increasing 0 0 (Nat.zero_le _) k hk
  -- S count below val
  have h_S_count : (S.filter (fun w => w.val < pairVal p)).card = p.1 / 2 := by
    rw [← h_cs_count, ← h_cs_val]
    exact fill_count_below_val cs hwf S hS k hk
  -- Convert arr[pos]! to arr[pos]
  have h_arr_getelem : arr[pairPos arr.size p] = pairVal p + 1 := by
    rw [show arr[pairPos arr.size p] = arr[pairPos arr.size p]! from
      (getElem!_pos arr _ h_pos_lt).symm]
    exact h_arr_eq
  rw [h_arr_getelem]
  -- Now need: mkUnimodal[pos] = pairVal p + 1
  -- Case split on p.1 % 2
  by_cases h_odd : p.1 % 2 = 1
  · -- Type I: p.1 is odd, pos = p.1 / 2
    have h_pos_eq : pairPos arr.size p = p.1 / 2 := by
      simp [pairPos, h_odd]
    have h_in_S : (⟨pairVal p, h_val_lt_n⟩ : Fin n) ∈ S := by
      simp [hS, Finset.mem_filter]; rw [h_fill_at]; simp [h_odd]
    have h_count_eq : (S.filter (fun w => w.val < pairVal p)).card = pairPos arr.size p := by
      rw [h_S_count, h_pos_eq]
    have h_pos_lt_sort : pairPos arr.size p < (S.sort (· ≤ ·)).length :=
      sort_len_gt_pos S (pairVal p) (pairPos arr.size p) h_val_lt_n h_in_S h_count_eq
    exact fill_agreement_type_I n S (pairPos arr.size p) (pairVal p) hpos h_val_lt_n
      h_in_S h_count_eq h_pos_lt_sort
  · -- Type II: p.1 is even, pos = n - (p.2 + 1) / 2
    have h_even : p.1 % 2 = 0 := by omega
    have h_pos_eq : pairPos arr.size p = n - (p.2 + 1) / 2 := by
      simp [pairPos, h_odd, harr_size]
    have h_not_in_S : (⟨pairVal p, h_val_lt_n⟩ : Fin n) ∉ S := by
      simp [hS, Finset.mem_filter]; rw [h_fill_at]; simp [h_odd]
    -- Complement count = val - count = (p.1+p.2)/2 - p.1/2
    have h_count_le_val : p.1 / 2 ≤ pairVal p := by unfold pairVal; omega
    have h_compl := compl_count_below_val (pairVal p) (p.1 / 2) h_val_lt_n
      h_count_le_val S h_S_count
    -- Show compl count = n - 1 - pos
    have h_compl_eq : pairVal p - p.1 / 2 = n - 1 - pairPos arr.size p := by
      unfold pairVal pairPos at *; simp [h_odd] at *; omega
    rw [h_compl_eq] at h_compl
    -- Sort length bound
    have h_bound : p.1 / 2 + n ≤ pairVal p + 1 + pairPos arr.size p := by
      unfold pairVal pairPos at *; simp [h_odd] at *; omega
    have h_sort_le := sort_len_le_pos S (pairVal p) (pairPos arr.size p) (p.1 / 2)
      h_val_lt_n hpos h_not_in_S h_S_count h_bound
    exact fill_agreement_type_II n S (pairPos arr.size p) (pairVal p) hpos h_val_lt_n
      h_not_in_S h_compl h_sort_le

/-! ## Position distinctness -/

lemma nds_positions_nodup (arr : Array Nat) (n : Nat)
    (harr_size : arr.size = n)
    (nds_idx : List Nat)
    (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < (sortedPairs arr).size)
    (h_nondec : nds_idx.Pairwise (fun i j =>
      (sortedPairs arr).toList[i]!.2 ≤ (sortedPairs arr).toList[j]!.2))
    (h_nodup : (sortedPairs arr).toList.Nodup)
    (h_sp_sorted : (sortedPairs arr).toList.Pairwise pairLe)
    (h_in_raw : ∀ i ∈ nds_idx, (sortedPairs arr).toList[i]! ∈ (rawPairs arr).toList)
    (harr_perm : ∀ i, i < arr.size → arr[i]! ≤ arr.size) :
    (nds_idx.map (fun i => pairPos arr.size ((sortedPairs arr).toList[i]!))).Nodup := by
  have h_inj : ∀ i j, i ∈ nds_idx → j ∈ nds_idx → i ≠ j → pairPos arr.size ((sortedPairs arr).toList[i]!) ≠ pairPos arr.size ((sortedPairs arr).toList[j]!) := by
    intros i j hi hj hij h_eq_pos
    have h_eq_sp : (sortedPairs arr).toList[i]! = (sortedPairs arr).toList[j]! := by
      nontriviality;
      have h_eq_sp : pairLe ((sortedPairs arr).toList[i]!) ((sortedPairs arr).toList[j]!) ∧ ((sortedPairs arr).toList[i]!).2 ≤ ((sortedPairs arr).toList[j]!).2 ∨ pairLe ((sortedPairs arr).toList[j]!) ((sortedPairs arr).toList[i]!) ∧ ((sortedPairs arr).toList[j]!).2 ≤ ((sortedPairs arr).toList[i]!).2 := by
        cases lt_or_gt_of_ne hij <;> simp_all +decide [ List.pairwise_iff_get ];
        · obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hi; obtain ⟨ l, hl ⟩ := List.mem_iff_get.mp hj; simp_all +decide [ Fin.ext_iff ] ;
          have h_eq_sp : k < l := by
            grind;
          have := h_sp_sorted ⟨ i, by aesop ⟩ ⟨ j, by aesop ⟩ ; aesop;
        · obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp hi; obtain ⟨ l, hl ⟩ := List.mem_iff_get.mp hj; simp_all +decide [ Fin.ext_iff ] ;
          have h_eq_sp : l < k := by
            exact lt_of_not_ge fun h => by linarith [ h_sorted _ _ ( lt_of_le_of_ne h ( Ne.symm <| by aesop ) ) ] ;
          have := h_sp_sorted ⟨ nds_idx[l], by aesop ⟩ ⟨ nds_idx[k], by aesop ⟩ ( by aesop ) ; aesop;
      nontriviality;
      have h_eq_sp : ∀ p q : Nat × Nat, p ∈ (rawPairs arr).toList → q ∈ (rawPairs arr).toList → pairPos arr.size p = pairPos arr.size q → pairLe p q → p.2 ≤ q.2 → p = q := by
        intros p q hp hq h_eq_pos h_pairLe h_snd_le
        apply rawPairs_same_pos_pairle_nds_eq arr p q hp hq h_eq_pos h_pairLe h_snd_le harr_perm;
      grind;
    have := List.nodup_iff_injective_get.mp h_nodup; have := @this ⟨ i, by aesop ⟩ ⟨ j, by aesop ⟩ ; aesop;
  rw [ List.nodup_map_iff_inj_on ];
  · exact fun i hi j hj hij => Classical.not_not.1 fun hij' => h_inj i j hi hj hij' hij;
  · exact List.Pairwise.nodup h_sorted

end Submission.NdsAgreement
