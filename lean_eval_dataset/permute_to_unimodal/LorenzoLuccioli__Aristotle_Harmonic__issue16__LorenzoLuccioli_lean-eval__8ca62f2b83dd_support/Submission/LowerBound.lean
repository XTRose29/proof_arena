import ChallengeDeps
import Submission.Bridge
import Submission.SortedSubperm
import Submission.AgreementsNDS
import Submission.EncodingCorrectness
import Submission.UnimodalProps
import Submission.UnimodalCounting
import Submission.AgreementsProof
import Submission.AgreementSublist

/-!
# Lower bound: minRearrange ≤ differences for any unimodal permutation
-/

namespace Submission.LowerBound

open LeanEval.ProgramVerification
open Submission.SortedSubperm
open Submission.EncodingCorrectness
open Submission.UnimodalProps

def encodedSeq (arr : Array Nat) : Array Nat :=
  let n := arr.size
  let v :=
    (arr.zipIdx.filter (fun (a, i) => i + 1 ≤ a)).map (fun (a, i) => (2 * i + 1, 2 * (a - i - 1))) ++
    (arr.zipIdx.filter (fun (a, i) => n ≤ a + i)).map (fun (a, i) => (2 * (a + i - n), 2 * (n - i) - 1))
  let vv := (v.toList.mergeSort (le := fun a b => a = b ∨ Prod.Lex (· < ·) (· < ·) a b)).toArray
  vv.map (·.2)

lemma encodedSeq_eq (arr : Array Nat) :
    encodedSeq arr = (sortedPairs arr).map (·.2) := by
  simp [encodedSeq, sortedPairs, rawPairs, SortedSubperm.pairLeBool]

lemma minRearrange_eq (arr : Array Nat) :
    minRearrange arr = arr.size - minRearrange.lis (encodedSeq arr) := by
  unfold minRearrange encodedSeq; aesop

lemma agreements_plus_differences {n : Nat} (a b : Vector Nat n) :
    ((List.finRange n).filter (fun i => a[i] = b[i])).length +
    differences a b = n := by
  have h_partition : Finset.card (Finset.filter (fun i => a[i] = b[i]) (Finset.univ : Finset (Fin n))) + Finset.card (Finset.filter (fun i => a[i] ≠ b[i]) (Finset.univ : Finset (Fin n))) = n := by
    rw [Finset.card_filter_add_card_filter_not, Finset.card_fin]
  convert h_partition using 1

/-- The mergeSort comparison used in the encoding equals pairLeBool -/
lemma encoding_le_eq_pairLeBool :
    (fun (a b : Nat × Nat) => decide (a = b ∨ Prod.Lex (· < ·) (· < ·) a b)) =
    SortedSubperm.pairLeBool := by rfl

/-
sortedPairs is pairwise sorted by pairLe
-/
lemma sortedPairs_pairwise (arr : Array Nat) :
    (sortedPairs arr).toList.Pairwise pairLe := by
  convert mergeSort_pairwise _ using 1

/-
Every element of rawPairs is in sortedPairs
-/
lemma mem_rawPairs_mem_sortedPairs (arr : Array Nat) (p : Nat × Nat) :
    p ∈ (rawPairs arr).toList → p ∈ (sortedPairs arr).toList := by
  exact fun h => ( Submission.SortedSubperm.mergeSort_perm _ ).mem_iff.mpr h

/-
For a unimodal permutation x = b ++ b' of 1..n, if position k < b.size
    and x[k] = arr[k], then k+1 ≤ arr[k] (increasing part filter condition).
-/
lemma inc_filter_cond {x arr : Array Nat} {n : Nat}
    (hx : x.Perm (1...=n).toArray) (hx_size : x.size = n)
    (harr_size : arr.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hinc : b.toList.Pairwise (· < ·))
    {k : Nat} (hk : k < b.size) (hkn : k < n) :
    k + 1 ≤ x[k]'(by omega) := by
  -- Since x = b ++ b' and k < b.size, we have x[k] = b[k].
  have hxk : x[k] = b[k] := by
    grind;
  have h_b_ge : ∀ v ∈ b.toList, 1 ≤ v := by
    intro v hv
    have h_v_in_x : v ∈ x := by
      aesop;
    have h_v_in_range : v ∈ (1...=n).toArray := by
      grind +splitImp;
    have := Array.mem_iff_getElem.mp h_v_in_range; aesop;
  exact hxk.symm ▸ increasing_ge_succ hinc h_b_ge ( by simpa using hk )

/-
For a unimodal permutation x = b ++ b' of 1..n, if position k ≥ b.size
    and x[k] = arr[k], then n ≤ arr[k]+k (decreasing part filter condition).
-/
lemma dec_filter_cond {x arr : Array Nat} {n : Nat}
    (hx : x.Perm (1...=n).toArray) (hx_size : x.size = n)
    (b b' : Array Nat) (hx_eq : x = b ++ b')
    (hdec : b'.toList.Pairwise (· > ·))
    {k : Nat} (hk : b.size ≤ k) (hkn : k < n) :
    n ≤ x[k]'(by omega) + k := by
  -- Since $k \geq b.size$, we can write $k = b.size + m$ for some $m$ where $0 \leq m < b'.size$.
  obtain ⟨m, hm⟩ : ∃ m, k = b.size + m ∧ m < b'.size := by
    exact ⟨ k - b.size, by rw [ Nat.add_sub_cancel' hk ], by rw [ tsub_lt_iff_left hk ] ; linarith [ show x.size = b.size + b'.size from by simp +decide [ hx_eq ] ] ⟩;
  have h_b'_ge : ∀ i < b'.size, b'[i]! + i ≥ b'.size := by
    have h_b'_ge : ∀ i < b'.size, b'[i]! ≥ b'.size - i := by
      intro i hi
      have h_b'_ge_i : ∀ j < b'.size, j ≥ i → b'[j]! ≤ b'[i]! := by
        intros j hj_lt hj_ge_i
        have h_b'_ge_i : ∀ {l : List ℕ}, List.Pairwise (· > ·) l → ∀ i j, i < j → j < l.length → l[j]! ≤ l[i]! := by
          intros l hl i j hij hj_lt; induction' hij with i j hij ih <;> simp_all +decide [ List.getElem?_eq_getElem ] ;
          · have := List.pairwise_iff_get.mp hl;
            exact le_of_lt ( by simpa [ List.getElem?_eq_getElem ( by linarith : i < l.length ) ] using this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self _ ) );
          · have := List.pairwise_iff_get.mp hl;
            exact le_trans ( le_of_lt ( this ⟨ i, by linarith ⟩ ⟨ i + 1, by linarith ⟩ ( Nat.lt_succ_self _ ) ) ) ( hij ( by linarith ) );
        cases hj_ge_i.eq_or_lt <;> simp_all +decide [ List.getElem?_eq_getElem ];
        specialize h_b'_ge_i hdec i j ‹_› ; aesop
      have h_b'_ge_i : Finset.card (Finset.image (fun j => b'[j]!) (Finset.Ico i b'.size)) = b'.size - i := by
        rw [ Finset.card_image_of_injOn, Nat.card_Ico ];
        intro j hj k hk h_eq; simp_all +decide [ Finset.mem_Ico ] ;
        have := List.pairwise_iff_get.mp hdec; simp_all +decide [ List.get ] ;
        exact le_antisymm ( le_of_not_gt fun h => by have := this ⟨ k, by linarith ⟩ ⟨ j, by linarith ⟩ h; aesop ) ( le_of_not_gt fun h => by have := this ⟨ j, by linarith ⟩ ⟨ k, by linarith ⟩ h; aesop );
      have h_b'_ge_i : Finset.image (fun j => b'[j]!) (Finset.Ico i b'.size) ⊆ Finset.Icc 1 (b'[i]!) := by
        have h_b'_ge_i : ∀ j < b'.size, 1 ≤ b'[j]! := by
          have h_b'_ge_i : ∀ j < b'.size, b'[j]! ∈ (1...=n).toArray.toList := by
            grind;
          intro j hj; specialize h_b'_ge_i j hj; simp_all +decide [ List.mem_iff_get ] ;
          exact h_b'_ge_i.choose_spec ▸ Nat.le_add_right _ _;
        exact Finset.image_subset_iff.mpr fun j hj => Finset.mem_Icc.mpr ⟨ h_b'_ge_i j ( Finset.mem_Ico.mp hj |>.2 ), by aesop ⟩;
      have := Finset.card_le_card h_b'_ge_i; aesop;
    grind +splitIndPred;
  grind

open Submission.AgreementSublist in
/-- The agreement pairs form a sublist of sortedPairs with NDS second components. -/
lemma agreement_sublist {arr x : Array Nat} {n : Nat}
    (harr : arr.Perm (1...=n).toArray) (hx : x.Perm (1...=n).toArray)
    (harr_size : arr.size = n) (hx_size : x.size = n)
    (huni : Unimodal x) :
    ∃ (sub : List (Nat × Nat)),
      sub.Sublist (sortedPairs arr).toList ∧
      sub.Pairwise (fun a b => a.2 ≤ b.2) ∧
      sub.length = ((List.finRange n).filter (fun i =>
        x[i.val]'(by omega) = arr[i.val]'(by omega))).length := by
  obtain ⟨b, b', hx_eq, hinc, hdec⟩ := huni
  set p := b.size
  set agreeIdx := (List.finRange n).filter (fun i => x[i.val]'(by omega) = arr[i.val]'(by omega))
  set ap := agreeIdx.map (fun i => agreePair arr n p i.val)
  set sap := ap.mergeSort pairLeBool
  -- Filter conditions
  have hfilt : ∀ i : Fin n, x[i.val]'(by omega) = arr[i.val]'(by omega) →
      (if i.val < p then i.val + 1 ≤ arr[i.val]'(by omega)
       else n ≤ arr[i.val]'(by omega) + i.val) := by
    intro i heq; split
    · have h := inc_filter_cond hx hx_size harr_size b b' hx_eq hinc ‹_› (i.isLt)
      rw [← heq]; exact h
    · have h := dec_filter_cond (arr := arr) hx hx_size b b' hx_eq hdec (by omega) (i.isLt)
      rw [← heq]; exact h
  -- agreeIdx membership helper
  have hagree_mem : ∀ i ∈ agreeIdx, x[i.val]'(by omega) = arr[i.val]'(by omega) := by
    intro i hi
    have := List.of_mem_filter hi
    simpa using this
  -- Each ap element is in rawPairs
  have hap_in_raw : ∀ q ∈ ap, q ∈ (rawPairs arr).toList := by
    intro q hq; obtain ⟨i, hi_mem, rfl⟩ := List.mem_map.mp hq
    have hi_agree := hagree_mem i hi_mem
    have hfi := hfilt i hi_agree
    by_cases hip : i.val < p
    · exact agreePair_inc_mem_rawPairs arr harr_size hip i.isLt (by split_ifs at hfi <;> omega)
    · exact agreePair_dec_mem_rawPairs arr harr_size (by omega) i.isLt (by split_ifs at hfi <;> omega)
  -- Each ap element is in sortedPairs
  have hap_in_sorted : ∀ q ∈ ap, q ∈ (sortedPairs arr).toList :=
    fun q hq => Submission.AgreementSublist.mem_rawPairs_sortedPairs arr q (hap_in_raw q hq)
  -- ap is nodup
  have hap_nodup : ap.Nodup := by
    rw [List.nodup_map_iff_inj_on (List.Nodup.filter _ (List.nodup_finRange _))]
    intro a ha c hc heq
    have ha' := hagree_mem a ha; have hc' := hagree_mem c hc
    by_contra h
    have hne : a.val ≠ c.val := fun h2 => h (Fin.ext h2)
    exact agreePair_injective arr harr_size a.isLt c.isLt hne (hfilt a ha') (hfilt c hc') heq
  -- sap properties
  have hsap_perm : sap.Perm ap := mergeSort_perm ap
  have hsap_sorted : sap.Pairwise pairLe := mergeSort_pairwise ap
  have hsap_nodup : sap.Nodup := hsap_perm.nodup_iff.mpr hap_nodup
  have hsap_in_sorted : ∀ q ∈ sap, q ∈ (sortedPairs arr).toList :=
    fun q hq => hap_in_sorted q (hsap_perm.mem_iff.mp hq)
  -- Subperm → Sublist
  have hsap_subperm : sap.Subperm (sortedPairs arr).toList :=
    List.subperm_of_subset hsap_nodup hsap_in_sorted
  have hsap_sublist : sap.Sublist (sortedPairs arr).toList :=
    sorted_subperm_sublist sap (sortedPairs arr).toList hsap_subperm hsap_sorted (sortedPairs_pairwise arr)
  -- NDS: every element of sap came from an agreement position
  have hsap_origin : ∀ q ∈ sap, ∃ i : Fin n,
      x[i.val]'(by omega) = arr[i.val]'(by omega) ∧ q = agreePair arr n p i.val := by
    intro q hq
    have hq_ap := hsap_perm.mem_iff.mp hq
    obtain ⟨i, hi_mem, rfl⟩ := List.mem_map.mp hq_ap
    exact ⟨i, hagree_mem i hi_mem, rfl⟩
  have hsap_nds : sap.Pairwise (fun a b => a.2 ≤ b.2) := by
    rw [List.pairwise_iff_getElem] at hsap_sorted ⊢
    intro i j hi hj hij
    obtain ⟨fi, hfi_agree, hfi_eq⟩ := hsap_origin _ (List.getElem_mem hi)
    obtain ⟨fj, hfj_agree, hfj_eq⟩ := hsap_origin _ (List.getElem_mem hj)
    rw [hfi_eq, hfj_eq]
    apply agreePairs_pairLe_nds hx harr hx_size harr_size b b' hx_eq hinc hdec rfl
      fi.isLt fj.isLt hfi_agree hfj_agree (hfilt fi hfi_agree) (hfilt fj hfj_agree)
    rw [← hfi_eq, ← hfj_eq]
    exact hsap_sorted i j hi hj hij
  -- Length
  have hsap_len : sap.length = agreeIdx.length := by
    rw [show sap.length = ap.length from hsap_perm.length_eq, List.length_map]
  exact ⟨sap, hsap_sublist, hsap_nds, hsap_len⟩

/-
Core encoding lemma
-/
lemma agreements_form_nds {arr x : Array Nat} {n : Nat}
    (harr : arr.Perm (1...=n).toArray) (hx : x.Perm (1...=n).toArray)
    (harr_size : arr.size = n) (hx_size : x.size = n)
    (huni : Unimodal x) :
    ∃ (indices : List Nat),
      indices.Pairwise (· < ·) ∧
      (∀ i ∈ indices, i < (encodedSeq arr).size) ∧
      indices.Pairwise (fun i j => (encodedSeq arr)[i]! ≤ (encodedSeq arr)[j]!) ∧
      indices.length = ((List.finRange n).filter (fun i =>
        x[i.val]'(by omega) = arr[i.val]'(by omega))).length := by
  obtain ⟨sub, h_sublist, h_nds, h_len⟩ := agreement_sublist harr hx harr_size hx_size huni
  obtain ⟨indices, hi_sorted, hi_bound, hi_nds, hi_len⟩ :=
    Submission.AgreementsNDS.sublist_to_nds_indices
      (sortedPairs arr).toList
      (sortedPairs_pairwise arr)
      sub h_sublist h_nds
  refine ⟨indices, hi_sorted, ?_, ?_, hi_len.trans h_len⟩
  · intro i hi
    rw [encodedSeq_eq]
    simp [Array.size_map]
    exact hi_bound i hi
  · rw [List.pairwise_iff_getElem] at hi_nds ⊢
    intro i j hij hj hlt
    rw [encodedSeq_eq]
    grind

theorem lower_bound {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) :
    ∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
      Unimodal x → minRearrange arr ≤ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector := by
  intro x hx huni
  have harr_size : arr.size = arr.size := rfl
  have hx_size : x.size = arr.size := by simpa using hx.size_eq
  obtain ⟨indices, h_sorted, h_bound, h_nondec, h_len⟩ :=
    agreements_form_nds harr hx harr_size hx_size huni
  have h_lis := Bridge.minRearrange_lis_ge_nds (encodedSeq arr) indices h_sorted h_bound h_nondec
  rw [h_len] at h_lis
  have h_comp := agreements_plus_differences
    (Vector.mk x (by simpa using hx.size_eq)) arr.toVector
  rw [minRearrange_eq]
  suffices h : (List.filter (fun i => decide ((Vector.mk x (by simpa using hx.size_eq))[i] = arr.toVector[i])) (List.finRange arr.size)).length ≤
    minRearrange.lis (encodedSeq arr) by omega
  convert h_lis using 2

end Submission.LowerBound