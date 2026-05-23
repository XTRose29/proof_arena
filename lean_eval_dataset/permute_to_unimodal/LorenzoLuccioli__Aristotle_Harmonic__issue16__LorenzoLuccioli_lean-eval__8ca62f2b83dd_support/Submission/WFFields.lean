import Mathlib
import Submission.FillLemma
import Submission.EncodingCorrectness
import Submission.SortedSubperm
import Submission.GapArith
import Submission.WFConstraints

/-!
# Individual WellFormedConstraints fields
-/

set_option maxHeartbeats 800000

namespace Submission.WFFields

open Submission.FillLemma
open Submission.EncodingCorrectness
open Submission.SortedSubperm (pairLe)
open Submission.GapArith
open Submission.WFConstraints

/-- pairVal = (p.1 + p.2) / 2 -/
def pairVal (p : Nat × Nat) : Nat := (p.1 + p.2) / 2

/-- pairToConstraint p = (pairVal p, p.1 / 2, decide (p.1 % 2 = 1)) -/
def pairToConstraint (p : Nat × Nat) : Nat × Nat × Bool :=
  (pairVal p, p.1 / 2, decide (p.1 % 2 = 1))

/-
vals_lt_n field: each val < n.
-/
lemma wf_vals_lt_n (arr : Array Nat) (n : Nat)
    (harr : arr.Perm (1...=n).toArray) (harr_size : arr.size = n)
    (nds_idx : List Nat)
    (h_bound : ∀ i ∈ nds_idx, i < (sortedPairs arr).size)
    (h_in_raw : ∀ i ∈ nds_idx, (sortedPairs arr).toList[i]! ∈ (rawPairs arr).toList) :
    ∀ c ∈ nds_idx.map (fun i => pairToConstraint ((sortedPairs arr).toList[i]!)),
      c.1 < n := by
  intro c hc;
  -- By definition of `rawPairs`, each element in `rawPairs arr` corresponds to a unique position in `arr`.
  have h_rawPairs_pos : ∀ p ∈ (rawPairs arr).toList, p.1 + p.2 < 2 * n := by
    intro p hp
    have h_pos : ∃ i, i < arr.size ∧ arr[i]! = (p.1 + p.2) / 2 + 1 ∧ (p.1 = 2 * i + 1 ∨ p.1 = 2 * (arr[i]! + i - arr.size)) := by
      unfold rawPairs at hp;
      simp +zetaDelta at *;
      grind;
    have h_arr_le_n : ∀ i < arr.size, arr[i]! ≤ n := by
      intro i hi
      have h_arr_le_n : arr[i]! ∈ (1...=n).toArray := by
        grind;
      rw [ List.mem_toArray ] at h_arr_le_n;
      rw [ List.mem_iff_get ] at h_arr_le_n;
      obtain ⟨ k, hk ⟩ := h_arr_le_n;
      exact hk ▸ Nat.le_of_lt_succ ( by { have := k.2; simp_all +decide ; omega } );
    grind;
  unfold pairToConstraint at hc;
  unfold pairVal at hc; simp_all +arith +decide;
  grind

/-
vals_increasing field: constraint vals are strictly increasing.
-/
lemma wf_vals_increasing (arr : Array Nat) (_n : Nat)
    (nds_idx : List Nat)
    (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < (sortedPairs arr).size)
    (h_nondec : nds_idx.Pairwise (fun i j =>
      (sortedPairs arr).toList[i]!.2 ≤ (sortedPairs arr).toList[j]!.2))
    (h_nodup : (sortedPairs arr).toList.Nodup)
    (h_sp_sorted : (sortedPairs arr).toList.Pairwise pairLe)
    (h_in_raw : ∀ i ∈ nds_idx, (sortedPairs arr).toList[i]! ∈ (rawPairs arr).toList) :
    (nds_idx.map (fun i => pairToConstraint ((sortedPairs arr).toList[i]!))).Pairwise
      (fun c₁ c₂ => c₁.1 < c₂.1) := by
  have h_contradiction : ∀ i ∈ nds_idx, (sortedPairs arr).toList[i]!.1 + (sortedPairs arr).toList[i]!.2 ≡ 1 [MOD 2] := by
    intro i hi; specialize h_in_raw i hi; simp_all +decide [ Nat.ModEq ] ;
    have h_contradiction : ∀ p ∈ rawPairs arr, (p.1 + p.2) % 2 = 1 := by
      unfold rawPairs; simp +decide [ Nat.add_mod ] ;
      grind +suggestions;
    exact h_contradiction _ h_in_raw;
  have h_contradiction : ∀ i j, i ∈ nds_idx → j ∈ nds_idx → i < j → (sortedPairs arr).toList[i]!.1 + (sortedPairs arr).toList[i]!.2 < (sortedPairs arr).toList[j]!.1 + (sortedPairs arr).toList[j]!.2 := by
    intros i j hi hj hij
    have h_pairle : pairLe (sortedPairs arr).toList[i]! (sortedPairs arr).toList[j]! := by
      have := List.pairwise_iff_get.mp h_sp_sorted;
      convert this ⟨ i, by simpa using h_bound i hi ⟩ ⟨ j, by simpa using h_bound j hj ⟩ hij using 1 <;> aesop
    have h_snd_le : (sortedPairs arr).toList[i]!.2 ≤ (sortedPairs arr).toList[j]!.2 := by
      have := List.pairwise_iff_get.mp h_nondec;
      obtain ⟨k, rfl⟩ : ∃ k : Fin nds_idx.length, nds_idx.get k = i := by
        exact List.mem_iff_get.mp hi
      obtain ⟨l, rfl⟩ : ∃ l : Fin nds_idx.length, nds_idx.get l = j := by
        exact List.mem_iff_get.mp hj
      have hkl : k < l := by
        have hval : nds_idx.get k < nds_idx.get l := hij
        by_contra hnot
        have hle : l ≤ k := le_of_not_gt hnot
        obtain rfl | hlt := eq_or_lt_of_le hle
        · omega
        · have hsorted_val := h_sorted.rel_get_of_lt hlt
          omega
      have := this k l hkl
      aesop
    have h_ne : (sortedPairs arr).toList[i]! ≠ (sortedPairs arr).toList[j]! := by
      have := List.nodup_iff_injective_get.mp h_nodup; have := @this ⟨ i, by aesop ⟩ ⟨ j, by aesop ⟩ ; aesop;
    exact (by
    nontriviality;
    cases h_pairle <;> simp_all +decide [ Nat.ModEq ];
    grind +revert);
  have h_contradiction : ∀ i j, i ∈ nds_idx → j ∈ nds_idx → i < j → ((sortedPairs arr).toList[i]!.1 + (sortedPairs arr).toList[i]!.2) / 2 < ((sortedPairs arr).toList[j]!.1 + (sortedPairs arr).toList[j]!.2) / 2 := by
    grind +suggestions;
  rw [ List.pairwise_map ];
  exact List.Pairwise.imp_of_mem ( fun i j hij => by aesop ) h_sorted

/-
counts_le_vals field.
-/
lemma wf_counts_le_vals (arr : Array Nat) (nds_idx : List Nat) :
    ∀ c ∈ nds_idx.map (fun i => pairToConstraint ((sortedPairs arr).toList[i]!)),
      c.2.1 ≤ c.1 := by
  grind +locals

/-
gap_lower field.
-/
lemma wf_gap_lower (arr : Array Nat) (nds_idx : List Nat)
    (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < (sortedPairs arr).size)
    (h_nondec : nds_idx.Pairwise (fun i j =>
      (sortedPairs arr).toList[i]!.2 ≤ (sortedPairs arr).toList[j]!.2))
    (h_nodup : (sortedPairs arr).toList.Nodup)
    (h_sp_sorted : (sortedPairs arr).toList.Pairwise pairLe)
    (h_in_raw : ∀ i ∈ nds_idx, (sortedPairs arr).toList[i]! ∈ (rawPairs arr).toList) :
    let cs := nds_idx.map (fun i => pairToConstraint ((sortedPairs arr).toList[i]!))
    ∀ i, i + 1 < cs.length →
      cs[i]!.2.1 + (if cs[i]!.2.2 then 1 else 0) ≤ cs[i + 1]!.2.1 := by
  intro cs i hi
  have h_fst_le : (sortedPairs arr).toList[nds_idx[i]!]!.1 ≤ (sortedPairs arr).toList[nds_idx[i + 1]!]!.1 := by
    apply nds_consecutive_fst_le;
    · assumption;
    · assumption;
    · aesop;
    · assumption;
    · grind;
  nontriviality;
  have h_fst_eq_or_even : (sortedPairs arr).toList[nds_idx[i]!]!.1 = (sortedPairs arr).toList[nds_idx[i + 1]!]!.1 → (sortedPairs arr).toList[nds_idx[i]!]!.1 % 2 = 0 := by
    intros h_eq_fst
    have h_eq_or_even : (sortedPairs arr).toList[nds_idx[i]!]! = (sortedPairs arr).toList[nds_idx[i + 1]!]! ∨ (sortedPairs arr).toList[nds_idx[i]!]!.1 % 2 = 0 := by
      apply rawPairs_same_fst_eq_or_even;
      convert h_in_raw _ _;
      · grind;
      · grind;
      · exact h_eq_fst;
    have := nds_consecutive_ne ( sortedPairs arr |> Array.toList ) h_nodup nds_idx h_sorted ( fun i hi => h_bound i hi ) i ( by
      aesop ) ; aesop;
  grind +locals

/-
gap_upper field.
-/
lemma wf_gap_upper (arr : Array Nat) (nds_idx : List Nat)
    (h_sorted : nds_idx.Pairwise (· < ·))
    (h_bound : ∀ i ∈ nds_idx, i < (sortedPairs arr).size)
    (h_nondec : nds_idx.Pairwise (fun i j =>
      (sortedPairs arr).toList[i]!.2 ≤ (sortedPairs arr).toList[j]!.2))
    (h_nodup : (sortedPairs arr).toList.Nodup)
    (h_sp_sorted : (sortedPairs arr).toList.Pairwise pairLe)
    (h_in_raw : ∀ i ∈ nds_idx, (sortedPairs arr).toList[i]! ∈ (rawPairs arr).toList) :
    let cs := nds_idx.map (fun i => pairToConstraint ((sortedPairs arr).toList[i]!))
    ∀ i, i + 1 < cs.length →
      cs[i + 1]!.2.1 + cs[i]!.1 + 1 ≤
        cs[i]!.2.1 + (if cs[i]!.2.2 then 1 else 0) + cs[i + 1]!.1 := by
  simp +zetaDelta at *;
  intro i hi
  have h_pairle : pairLe ((sortedPairs arr)[nds_idx[i]!]!) ((sortedPairs arr)[nds_idx[i + 1]!]!) := by
    convert nds_consecutive_pairle ( sortedPairs arr |> Array.toList ) h_sp_sorted nds_idx h_sorted h_bound i ( by linarith ) using 1;
    · grind;
    · grind
  have h_snd_le : ((sortedPairs arr)[nds_idx[i]!]!).2 ≤ ((sortedPairs arr)[nds_idx[i + 1]!]!).2 := by
    have := List.pairwise_iff_get.mp h_nondec;
    convert this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self i ) using 1 <;> simp +decide ;
    · grind;
    · grind
  have h_ne : ((sortedPairs arr)[nds_idx[i]!]!) ≠ ((sortedPairs arr)[nds_idx[i + 1]!]!) := by
    have h_ne : List.Nodup (List.map (fun i => ((sortedPairs arr)[i]!)) nds_idx) := by
      rw [ List.nodup_map_iff_inj_on ];
      · intro x hx y hy hxy;
        have := List.nodup_iff_injective_get.mp h_nodup; have := @this ⟨ x, by aesop ⟩ ⟨ y, by aesop ⟩ ; aesop;
      · exact List.Pairwise.nodup h_sorted;
    rw [ List.nodup_iff_injective_get ] at h_ne;
    intro h; have := @h_ne ⟨ i, by simp +decide; linarith ⟩ ⟨ i + 1, by simp +decide; linarith ⟩ ; simp_all +decide ;
    grind
  have h_fst_le : ((sortedPairs arr)[nds_idx[i]!]!).1 ≤ ((sortedPairs arr)[nds_idx[i + 1]!]!).1 := by
    cases h_pairle;
    · contradiction;
    · grind
  have h_sum_lt : ((sortedPairs arr)[nds_idx[i]!]!).1 + ((sortedPairs arr)[nds_idx[i]!]!).2 < ((sortedPairs arr)[nds_idx[i + 1]!]!).1 + ((sortedPairs arr)[nds_idx[i + 1]!]!).2 := by
    grind +qlia
  have h_odd1 : ((sortedPairs arr)[nds_idx[i]!]!).1 + ((sortedPairs arr)[nds_idx[i]!]!).2 ≡ 1 [MOD 2] := by
    have h_odd1 : ∀ p ∈ (rawPairs arr).toList, p.1 + p.2 ≡ 1 [MOD 2] := by
      unfold rawPairs; simp +decide [ Nat.ModEq ] ;
      grind;
    grind +suggestions
  have h_odd2 : ((sortedPairs arr)[nds_idx[i + 1]!]!).1 + ((sortedPairs arr)[nds_idx[i + 1]!]!).2 ≡ 1 [MOD 2] := by
    have h_odd2 : ∀ p ∈ (rawPairs arr).toList, p.1 + p.2 ≡ 1 [MOD 2] := by
      unfold rawPairs; simp +decide [ Nat.ModEq ] ;
      grind;
    grind +qlia
  have h_even_strict : ((sortedPairs arr)[nds_idx[i]!]!).1 % 2 = 0 → ((sortedPairs arr)[nds_idx[i + 1]!]!).1 % 2 = 0 → ((sortedPairs arr)[nds_idx[i]!]!).2 < ((sortedPairs arr)[nds_idx[i + 1]!]!).2 := by
    have h_eq : ((sortedPairs arr)[nds_idx[i]!]!) ∈ (rawPairs arr).toList ∧ ((sortedPairs arr)[nds_idx[i + 1]!]!) ∈ (rawPairs arr).toList := by
      grind;
    unfold rawPairs at h_eq; simp_all +decide [ List.mem_append, List.mem_map ] ;
    grind +splitImp;
  unfold pairToConstraint; simp +decide [ * ] ;
  unfold pairVal; simp_all +decide [ Nat.ModEq ] ;
  grind +ring

end Submission.WFFields
