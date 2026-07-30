import Submission.Helpers

namespace Submission.Unimodal

open LeanEval.ProgramVerification
open Submission.Helpers

theorem idxOf_eq_length_filter_lt {l : List Nat} {a : Nat}
    (hsorted : l.Pairwise (· < ·)) (ha : a ∈ l) :
    l.idxOf a = (l.filter (· < a)).length := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.pairwise_cons] at hsorted
      by_cases hba : b = a
      · subst b
        have hfilter : l.filter (· < a) = [] := by
          rw [List.filter_eq_nil_iff]
          intro c hc
          simpa only [decide_eq_true_eq] using (hsorted.1 c hc).not_gt
        simp [hfilter]
      · have hal : a ∈ l := by simpa [Ne.symm hba] using ha
        have hblt : b < a := hsorted.1 a hal
        simp [List.idxOf_cons_ne l hba, hblt, ih hsorted.2 hal]

theorem idxOf_reverse_of_nodup {l : List Nat} {a : Nat}
    (hnodup : l.Nodup) (ha : a ∈ l) :
    l.reverse.idxOf a = l.length - l.idxOf a - 1 := by
  induction l with
  | nil => simp at ha
  | cons b l ih =>
      rw [List.nodup_cons] at hnodup
      by_cases hba : b = a
      · subst b
        rw [List.reverse_cons, List.idxOf_append_of_notMem]
        · simp
        · simpa using hnodup.1
      · have hal : a ∈ l := by simpa [Ne.symm hba] using ha
        rw [List.reverse_cons, List.idxOf_append_of_mem (by simpa using hal),
          List.idxOf_cons_ne l hba, ih hnodup.2 hal]
        simp only [List.length_cons]
        omega

theorem valueList_succ (n : Nat) :
    valueList (n + 1) = valueList n ++ [n + 1] := by
  simp only [valueList]
  rw [← List.range'_append (s := 1) (m := n) (n := 1) (step := 1)]
  simp [Nat.add_comm]

theorem filterValueList_length (n : Nat) (left : Nat → Bool) :
    ((valueList n).filter left).length =
      ((Finset.range n).filter fun k => left (k + 1)).card := by
  induction n with
  | zero => simp [valueList]
  | succ n ih =>
      cases h : left (n + 1) <;>
        simp [valueList_succ, Finset.range_add_one, Finset.filter_insert,
          h, ih]

theorem filterValueList_lt_length {n a : Nat} (left : Nat → Bool)
    (ha : 1 ≤ a) (han : a ≤ n) :
    ((valueList n).filter (fun b => left b && b < a)).length =
      leftBefore left a := by
  have heq :
      (valueList n).filter (fun b => left b && b < a) =
        (valueList (a - 1)).filter left := by
    apply ((valueList_pairwise n).filter _).eq_of_mem_iff
      ((valueList_pairwise (a - 1)).filter _)
    intro b
    cases hleft : left b
    · simp [valueList, hleft]
    · simp [valueList, hleft]
      omega
  rw [heq, filterValueList_length]
  simp only [leftBefore]

theorem idxOf_orientedList_of_left {n a : Nat} (left : Nat → Bool)
    (ha : 1 ≤ a) (han : a ≤ n) (hleft : left a = true) :
    (orientedList (valueList n) left).idxOf a = leftBefore left a := by
  have haValue : a ∈ valueList n := by
    simp [valueList]
    omega
  have haLeft : a ∈ (valueList n).filter left := by simp [haValue, hleft]
  rw [orientedList, List.idxOf_append_of_mem haLeft,
    idxOf_eq_length_filter_lt ((valueList_pairwise n).filter left) haLeft]
  have hfilter :
      ((valueList n).filter left).filter (· < a) =
        (valueList n).filter (fun b => left b && b < a) := by
    simp [List.filter_filter, Bool.and_comm]
  rw [hfilter, filterValueList_lt_length left ha han]

theorem idxOf_orientedList_of_right {n a : Nat} (left : Nat → Bool)
    (ha : 1 ≤ a) (han : a ≤ n) (hleft : left a = false) :
    (orientedList (valueList n) left).idxOf a =
      n - rightBefore left a - 1 := by
  let rights := (valueList n).filter (!left ·)
  have haValue : a ∈ valueList n := by
    simp [valueList]
    omega
  have haRight : a ∈ rights := by simp [rights, haValue, hleft]
  have haNotLeft : a ∉ (valueList n).filter left := by simp [hleft]
  have hrightsNodup : rights.Nodup :=
    ((valueList_pairwise n).filter (!left ·)).nodup
  have hrightBefore : rights.idxOf a = rightBefore left a := by
    rw [idxOf_eq_length_filter_lt ((valueList_pairwise n).filter (!left ·)) haRight]
    have hfilter :
        rights.filter (· < a) =
          (valueList n).filter (fun b => (!left b) && b < a) := by
      simp [rights, List.filter_filter, Bool.and_comm]
    rw [hfilter, filterValueList_lt_length (!left ·) ha han]
    simp [leftBefore, rightBefore]
  have htotal :
      ((valueList n).filter left).length + rights.length = n := by
    have hlen := (orientedList_perm (valueList n) left).length_eq
    simpa [orientedList, rights, valueList] using hlen
  rw [orientedList, List.idxOf_append_of_notMem haNotLeft,
    idxOf_reverse_of_nodup hrightsNodup haRight, hrightBefore]
  have hrightLt : rightBefore left a < rights.length := by
    rw [← hrightBefore]
    exact List.idxOf_lt_length_iff.mpr haRight
  omega

def orientedIndex (n : Nat) (left : Nat → Bool) (a : Nat) : Nat :=
  if left a then leftBefore left a else n - rightBefore left a - 1

theorem idxOf_orientedList {n a : Nat} (left : Nat → Bool)
    (ha : 1 ≤ a) (han : a ≤ n) :
    (orientedList (valueList n) left).idxOf a = orientedIndex n left a := by
  cases hleft : left a
  · simpa [orientedIndex, hleft] using
      idxOf_orientedList_of_right left ha han hleft
  · simpa [orientedIndex, hleft] using
      idxOf_orientedList_of_left left ha han hleft

theorem getElem_eq_iff_idxOf_eq {l₁ l₂ : List Nat}
    (hnodup₁ : l₁.Nodup) (hnodup₂ : l₂.Nodup)
    {i : Nat} (hi₁ : i < l₁.length) (hi₂ : i < l₂.length) :
    l₁[i] = l₂[i] ↔ l₁.idxOf l₂[i] = l₂.idxOf l₂[i] := by
  have hidx₂ : l₂.idxOf l₂[i] = i := hnodup₂.idxOf_getElem i hi₂
  rw [hidx₂]
  constructor
  · intro h
    rw [← h]
    exact hnodup₁.idxOf_getElem i hi₁
  · intro h
    have hmem : l₂[i] ∈ l₁ := by
      rw [← List.idxOf_lt_length_iff]
      omega
    have hget := List.getElem_idxOf
      (xs := l₁) (x := l₂[i]) (List.idxOf_lt_length_iff.mpr hmem)
    simpa [h] using hget

theorem canonical_oriented_array {n : Nat} {x : Array Nat}
    (hx : x.Perm (1...=n).toArray) (hunimodal : Unimodal x) :
    ∃ left : Nat → Bool, x = orientedArray (valueList n) left := by
  obtain ⟨b, b', hdecomp, hb, hb'⟩ := hunimodal
  let l := b.toList
  let r := b'.toList
  have hpArray : (b ++ b').Perm (valueList n).toArray := by
    rw [valueList_toArray]
    simpa [hdecomp] using hx
  have hp : List.Perm (l ++ r) (valueList n) := by
    simpa [l, r] using Array.perm_iff_toList_perm.mp hpArray
  have hnodup : (l ++ r).Nodup :=
    (List.Perm.nodup_iff hp).2 (valueList_pairwise n).nodup
  have hdisjoint : List.Disjoint l r := hnodup.disjoint
  let left : Nat → Bool := fun a => decide (a ∈ l)
  have hl : l = (valueList n).filter left := by
    apply hb.eq_of_mem_iff ((valueList_pairwise n).filter left)
    intro a
    simp only [List.mem_filter, left, decide_eq_true_eq]
    constructor
    · intro ha
      have hal : a ∈ l := by simpa [l] using ha
      exact ⟨hp.mem_iff.mp (List.mem_append_left r hal), hal⟩
    · exact fun ha => ha.2
  have hreverse : r.reverse.Pairwise (· < ·) := by
    simpa [List.pairwise_reverse] using hb'.reverse
  have hrReverse : r.reverse = (valueList n).filter (!left ·) := by
    apply hreverse.eq_of_mem_iff ((valueList_pairwise n).filter (!left ·))
    intro a
    simp only [List.mem_reverse, List.mem_filter]
    constructor
    · intro ha
      refine ⟨hp.mem_iff.mp (List.mem_append_right l ha), ?_⟩
      have hnot : a ∉ l := fun hal => hdisjoint hal ha
      simp [left, hnot]
    · rintro ⟨haValue, haNotLeft⟩
      have hnot : a ∉ l := by
        intro hal
        have hleftTrue : left a = true := by simp [left, hal]
        simp [hleftTrue] at haNotLeft
      have haAppend : a ∈ l ++ r := hp.mem_iff.mpr haValue
      exact (List.mem_append.mp haAppend).resolve_left hnot
  have hr : r = ((valueList n).filter (!left ·)).reverse := by
    have h := congrArg List.reverse hrReverse
    simpa using h
  refine ⟨left, ?_⟩
  apply Array.ext'
  simp [hdecomp, orientedArray, orientedList, l, r, hl, hr]

end Submission.Unimodal
