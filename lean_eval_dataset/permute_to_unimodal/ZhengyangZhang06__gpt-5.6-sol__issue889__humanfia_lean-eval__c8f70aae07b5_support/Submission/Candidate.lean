import Submission.Path

namespace Submission.Candidate

open Submission.Helpers
open Submission.Path

def CandidateWitness (arr : Array Nat) (p : Nat × Nat) : Prop :=
  (∃ (i : Nat) (hi : i < arr.size), i + 1 ≤ arr[i] ∧
      p = LeftPoint i arr[i]) ∨
    ∃ (i : Nat) (hi : i < arr.size), arr.size ≤ arr[i] + i ∧
      p = RightPoint arr.size i arr[i]

theorem mem_zipIdx_iff {arr : Array Nat} {a i : Nat} :
    (a, i) ∈ arr.zipIdx ↔
      ∃ hi : i < arr.size, arr[i] = a := by
  rw [Array.mem_iff_getElem]
  constructor
  · rintro ⟨j, hj, hget⟩
    simp only [Array.getElem_zipIdx] at hget
    have hji : j = i := by simpa using congrArg Prod.snd hget
    subst j
    exact ⟨by simpa using hj, congrArg Prod.fst hget⟩
  · rintro ⟨hi, hvalue⟩
    refine ⟨i, by simpa using hi, ?_⟩
    simp [hvalue]

theorem mem_candidatePoints_iff {arr : Array Nat} {p : Nat × Nat} :
    p ∈ candidatePoints arr ↔ CandidateWitness arr p := by
  simp only [candidatePoints, Array.mem_append, Array.mem_map, Array.mem_filter]
  constructor
  · rintro (⟨⟨a, i⟩, ⟨hzip, hcond⟩, rfl⟩ |
      ⟨⟨a, i⟩, ⟨hzip, hcond⟩, rfl⟩)
    · obtain ⟨hi, rfl⟩ := mem_zipIdx_iff.mp hzip
      exact Or.inl ⟨i, hi, by simpa only [decide_eq_true_eq] using hcond, rfl⟩
    · obtain ⟨hi, rfl⟩ := mem_zipIdx_iff.mp hzip
      exact Or.inr ⟨i, hi, by simpa only [decide_eq_true_eq] using hcond, rfl⟩
  · rintro (⟨i, hi, hcond, rfl⟩ | ⟨i, hi, hcond, rfl⟩)
    · exact Or.inl ⟨(arr[i], i), ⟨mem_zipIdx_iff.mpr ⟨hi, rfl⟩,
        by simpa only [decide_eq_true_eq] using hcond⟩, rfl⟩
    · exact Or.inr ⟨(arr[i], i), ⟨mem_zipIdx_iff.mpr ⟨hi, rfl⟩,
        by simpa only [decide_eq_true_eq] using hcond⟩, rfl⟩

theorem mem_sortedCandidatePoints_iff {arr : Array Nat} {p : Nat × Nat} :
    p ∈ sortedCandidatePoints arr ↔ CandidateWitness arr p := by
  rw [sortedCandidatePoints,
    (List.mergeSort_perm (l := (candidatePoints arr).toList)
      (le := LexLEB)).mem_iff]
  simpa using mem_candidatePoints_iff

theorem value_bounds {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) {i : Nat}
    (hi : i < arr.size) :
    1 ≤ arr[i] ∧ arr[i] ≤ arr.size := by
  have hmem : arr[i] ∈ arr := by simp
  have hrange := harr.mem_iff.mp hmem
  rw [← valueList_toArray] at hrange
  simp [valueList] at hrange
  omega

theorem candidate_valid {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) {p : Nat × Nat}
    (hp : CandidateWitness arr p) :
    ValidStep arr.size p := by
  rcases hp with ⟨i, hi, hcond, rfl⟩ | ⟨i, hi, hcond, rfl⟩
  · have habounds := value_bounds harr hi
    have hia : i < arr[i] := by omega
    constructor
    · have hbit : stepBit (LeftPoint i arr[i]) = true := by
        simp [stepBit, leftPoint_fst_odd]
      simp only [EncodedStep, hbit, ↓reduceIte]
      rw [pointBefore_leftPoint hia]
      rfl
    · refine ⟨arr[i], habounds.1, habounds.2, ?_⟩
      rw [pointBefore_leftPoint hia]
      omega
  · have habounds := value_bounds harr hi
    constructor
    · have hbit : stepBit (RightPoint arr.size i arr[i]) = false := by
        simp [stepBit, rightPoint_fst_even]
      simp only [EncodedStep, hbit, Bool.false_eq_true, ↓reduceIte]
      rw [pointBefore_rightPoint hi hcond]
      unfold RightPoint
      apply Prod.ext
      · rfl
      · omega
    · refine ⟨arr[i], habounds.1, habounds.2, ?_⟩
      rw [pointBefore_rightPoint hi hcond]
      omega

theorem arr_toList_nodup {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) :
    arr.toList.Nodup := by
  have harr' : arr.Perm (valueList arr.size).toArray := by
    rw [valueList_toArray]
    exact harr
  have hp := Array.perm_iff_toList_perm.mp harr'
  exact (hp.nodup_iff).2 (valueList_pairwise arr.size).nodup

theorem index_eq_of_value_eq {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray)
    {i j : Nat} (hi : i < arr.size) (hj : j < arr.size)
    (hvalue : arr[i] = arr[j]) :
    i = j := by
  apply (arr_toList_nodup harr).getElem_inj_iff.mp
  rw [Array.getElem_toList, Array.getElem_toList]
  exact hvalue

theorem candidate_fits_of_ne {arr : Array Nat}
    {p q : Nat × Nat} (hp : CandidateWitness arr p)
    (hq : CandidateWitness arr q) (hcomp : ComponentLE p q)
    (hne : p ≠ q) :
    FitsAfter p q := by
  rcases hp with ⟨i, hi, hpi, rfl⟩ | ⟨i, hi, hpi, rfl⟩
  · rcases hq with ⟨j, hj, hpj, rfl⟩ | ⟨j, hj, hpj, rfl⟩
    · apply fitsAfter_left_left (by omega) (by omega) hcomp
      intro hij
      subst j
      exact hne rfl
    · exact fitsAfter_left_right (by omega) hj hpj hcomp
  · rcases hq with ⟨j, hj, hpj, rfl⟩ | ⟨j, hj, hpj, rfl⟩
    · exact fitsAfter_right_left hi hpi (by omega) hcomp
    · apply fitsAfter_right_right hi hj hpi hpj hcomp
      intro hij
      subst j
      exact hne rfl

theorem zipIdx_toList_nodup (arr : Array Nat) :
    arr.zipIdx.toList.Nodup := by
  apply List.Nodup.of_map Prod.snd
  simpa using List.nodup_zipIdx_map_snd arr.toList

theorem leftCandidates_nodup (arr : Array Nat) :
    ((arr.zipIdx.filter (fun (a, i) => i + 1 ≤ a)).map
      (fun (a, i) => LeftPoint i a)).toList.Nodup := by
  simp only [Array.toList_map, Array.toList_filter]
  apply ((zipIdx_toList_nodup arr).filter _).map_on
  rintro ⟨a, i⟩ hi ⟨b, j⟩ hj heq
  simp only [List.mem_filter] at hi hj
  have hia : i + 1 ≤ a := by
    simpa only [decide_eq_true_eq] using hi.2
  have hjb : j + 1 ≤ b := by
    simpa only [decide_eq_true_eq] using hj.2
  simp only [LeftPoint, Prod.mk.injEq] at heq
  apply Prod.ext <;> simp only
  · omega
  · omega

theorem rightCandidates_nodup (arr : Array Nat) :
    ((arr.zipIdx.filter (fun (a, i) => arr.size ≤ a + i)).map
      (fun (a, i) => RightPoint arr.size i a)).toList.Nodup := by
  simp only [Array.toList_map, Array.toList_filter]
  apply ((zipIdx_toList_nodup arr).filter _).map_on
  rintro ⟨a, i⟩ hi ⟨b, j⟩ hj heq
  simp only [List.mem_filter] at hi hj
  have hiMem : (a, i) ∈ arr.zipIdx :=
    Array.mem_toList_iff.mp hi.1
  have hjMem : (b, j) ∈ arr.zipIdx :=
    Array.mem_toList_iff.mp hj.1
  have hiSize : i < arr.size :=
    (mem_zipIdx_iff.mp hiMem).choose
  have hjSize : j < arr.size :=
    (mem_zipIdx_iff.mp hjMem).choose
  have hia : arr.size ≤ a + i := by
    simpa only [decide_eq_true_eq] using hi.2
  have hjb : arr.size ≤ b + j := by
    simpa only [decide_eq_true_eq] using hj.2
  simp only [RightPoint, Prod.mk.injEq] at heq
  apply Prod.ext <;> simp only
  · omega
  · omega

theorem left_right_disjoint (arr : Array Nat) :
    List.Disjoint
      ((arr.zipIdx.filter (fun (a, i) => i + 1 ≤ a)).map
        (fun (a, i) => LeftPoint i a)).toList
      ((arr.zipIdx.filter (fun (a, i) => arr.size ≤ a + i)).map
        (fun (a, i) => RightPoint arr.size i a)).toList := by
  rw [List.disjoint_left]
  intro p hp hq
  simp only [Array.toList_map, Array.toList_filter, List.mem_map] at hp hq
  obtain ⟨⟨a, i⟩, _, rfl⟩ := hp
  obtain ⟨⟨b, j⟩, _, heq⟩ := hq
  have hodd := leftPoint_fst_odd i a
  have heven := rightPoint_fst_even arr.size j b
  have heq' : RightPoint arr.size j b = LeftPoint i a := by
    simpa using heq
  rw [heq'] at heven
  omega

theorem candidatePoints_nodup (arr : Array Nat) :
    (candidatePoints arr).toList.Nodup := by
  rw [candidatePoints, Array.toList_append]
  exact (leftCandidates_nodup arr).append (rightCandidates_nodup arr)
    (left_right_disjoint arr)

theorem sortedCandidatePoints_nodup (arr : Array Nat) :
    (sortedCandidatePoints arr).Nodup := by
  exact ((List.mergeSort_perm (l := (candidatePoints arr).toList)
    (le := LexLEB)).nodup_iff).2 (candidatePoints_nodup arr)

theorem subchain_valid_and_fits {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray)
    {points : List (Nat × Nat)}
    (hsub : points.Sublist (sortedCandidatePoints arr))
    (hcomp : points.Pairwise ComponentLE) :
    (∀ p ∈ points, ValidStep arr.size p) ∧
      points.Pairwise FitsAfter := by
  have hnodup : points.Nodup :=
    (sortedCandidatePoints_nodup arr).sublist hsub
  constructor
  · intro p hp
    exact candidate_valid harr
      (mem_sortedCandidatePoints_iff.mp (hsub.mem hp))
  · induction points with
    | nil => simp
    | cons p ps ih =>
        rw [List.pairwise_cons] at hcomp ⊢
        rw [List.nodup_cons] at hnodup
        constructor
        · intro q hq
          exact candidate_fits_of_ne
            (mem_sortedCandidatePoints_iff.mp (hsub.mem (by simp)))
            (mem_sortedCandidatePoints_iff.mp (hsub.mem (by simp [hq])))
            (hcomp.1 q hq) (fun hpq => hnodup.1 (hpq ▸ hq))
        · exact ih ((List.sublist_cons_self p ps).trans hsub) hcomp.2 hnodup.2

end Submission.Candidate
