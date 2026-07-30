import Submission.Candidate
import Submission.Unimodal

namespace Submission.Correspondence

open LeanEval.ProgramVerification
open Submission.Helpers
open Submission.Path
open Submission.Candidate
open Submission.Unimodal

def fixedIndices (arr : Array Nat) (left : Nat → Bool) :
    List (Fin arr.size) :=
  (List.finRange arr.size).filter fun i =>
    orientedIndex arr.size left arr[i] = i

def fixedValues (arr : Array Nat) (left : Nat → Bool) : List Nat :=
  (valueList arr.size).filter fun a =>
    arr.toList.idxOf a = orientedIndex arr.size left a

def fixedPoints (arr : Array Nat) (left : Nat → Bool) :
    List (Nat × Nat) :=
  (fixedValues arr left).map (pathMidpoint left)

theorem orientedValueArray_size (n : Nat) (left : Nat → Bool) :
    (orientedArray (valueList n) left).size = n := by
  have h := (orientedValueArray_perm n left).size_eq
  simpa using h

theorem orientedList_getElem_eq_iff {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool)
    {i : Nat} (hi : i < arr.size) :
    (orientedList (valueList arr.size) left)[i]'(by
      have hlen :=
        (orientedList_perm (valueList arr.size) left).length_eq
      rw [hlen]
      simpa [valueList] using hi) =
        arr.toList[i]'(by simpa using hi) ↔
      orientedIndex arr.size left arr[i] = i := by
  have hleftNodup :
      (orientedList (valueList arr.size) left).Nodup :=
    ((orientedList_perm (valueList arr.size) left).nodup_iff).2
      (valueList_pairwise arr.size).nodup
  have harrNodup := arr_toList_nodup harr
  have hiLeft : i < (orientedList (valueList arr.size) left).length := by
    have hlen := (orientedList_perm (valueList arr.size) left).length_eq
    rw [hlen]
    simpa [valueList] using hi
  have habounds := value_bounds harr hi
  rw [getElem_eq_iff_idxOf_eq hleftNodup harrNodup hiLeft
    (by simpa using hi)]
  simp only [Array.getElem_toList]
  rw [idxOf_orientedList left habounds.1 habounds.2]
  have hidx : arr.toList.idxOf arr[i] = i := by
    have hidxList := harrNodup.idxOf_getElem i (by simpa using hi)
    simpa only [Array.getElem_toList] using hidxList
  rw [hidx]

theorem orientedArray_getElem_eq_iff {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool)
    {i : Nat} (hi : i < arr.size) :
    (orientedArray (valueList arr.size) left)[i]'(by
      simpa [orientedValueArray_size] using hi) = arr[i] ↔
      orientedIndex arr.size left arr[i] = i := by
  simpa [orientedArray] using orientedList_getElem_eq_iff harr left hi

theorem agreements_oriented_eq_fixedIndices {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool) :
    agreements
        (Vector.mk (orientedArray (valueList arr.size) left)
          (orientedValueArray_size arr.size left))
        arr.toVector =
      (fixedIndices arr left).length := by
  unfold agreements fixedIndices
  apply congrArg List.length
  apply List.filter_congr
  intro i _
  simpa using orientedArray_getElem_eq_iff harr left i.isLt

theorem fixedIndexValues_nodup {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool) :
    ((fixedIndices arr left).map fun i => arr[i]).Nodup := by
  apply ((List.nodup_finRange arr.size).filter _).map_on
  intro i _ j _ hij
  apply Fin.ext
  exact index_eq_of_value_eq harr i.isLt j.isLt hij

theorem fixedValues_nodup (arr : Array Nat) (left : Nat → Bool) :
    (fixedValues arr left).Nodup :=
  (valueList_pairwise arr.size).nodup.filter _

theorem mem_fixedIndexValues_iff {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool)
    (a : Nat) :
    a ∈ (fixedIndices arr left).map (fun i => arr[i]) ↔
      a ∈ fixedValues arr left := by
  have harrNodup := arr_toList_nodup harr
  constructor
  · intro hmem
    obtain ⟨i, hiFixed, hia⟩ := List.mem_map.mp hmem
    have hfixed :
        orientedIndex arr.size left arr[i] = i := by
      simpa [fixedIndices] using hiFixed
    have hvalue : arr[i] ∈ valueList arr.size := by
      have hvalueArray : arr[i] ∈ (valueList arr.size).toArray := by
        rw [valueList_toArray]
        exact harr.mem_iff.mp (show arr[i] ∈ arr by simp)
      simpa using hvalueArray
    simp only [fixedValues, List.mem_filter, decide_eq_true_eq]
    refine ⟨by simpa only [← hia] using hvalue, ?_⟩
    rw [← hia]
    have hidx : arr.toList.idxOf arr[i] = i := by
      have hidxList := harrNodup.idxOf_getElem i i.isLt
      simpa only [Array.getElem_toList, Fin.getElem_fin] using hidxList
    rw [hidx]
    exact hfixed.symm
  · intro ha
    simp only [fixedValues, List.mem_filter, decide_eq_true_eq] at ha
    have haRange : a ∈ (1...=arr.size).toArray := by
      rw [← valueList_toArray]
      simpa using ha.1
    have haArr : a ∈ arr := harr.mem_iff.mpr haRange
    have haList : a ∈ arr.toList := Array.mem_toList_iff.mpr haArr
    have hiList : arr.toList.idxOf a < arr.toList.length :=
      List.idxOf_lt_length_iff.mpr haList
    have hi : arr.toList.idxOf a < arr.size := by
      simpa using hiList
    let i : Fin arr.size := ⟨arr.toList.idxOf a, hi⟩
    have hget : arr[i] = a := by
      have hgetList := List.getElem_idxOf
        (xs := arr.toList) (x := a) hiList
      have hgetNat : arr[arr.toList.idxOf a] = a := by
        simpa only [Array.getElem_toList] using hgetList
      simpa only [i, Fin.getElem_fin] using hgetNat
    refine List.mem_map.mpr ⟨i, ?_, hget⟩
    simp only [fixedIndices, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    simpa only [i, hget] using ha.2.symm

theorem fixedIndexValues_perm_fixedValues {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool) :
    List.Perm ((fixedIndices arr left).map fun i => arr[i])
      (fixedValues arr left) := by
  apply (List.perm_ext_iff_of_nodup
    (fixedIndexValues_nodup harr left)
    (fixedValues_nodup arr left)).2
  exact mem_fixedIndexValues_iff harr left

theorem fixedValues_length_eq_agreements {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool) :
    (fixedValues arr left).length =
      agreements
        (Vector.mk (orientedArray (valueList arr.size) left)
          (orientedValueArray_size arr.size left))
        arr.toVector := by
  rw [agreements_oriented_eq_fixedIndices harr left]
  have hlen := (fixedIndexValues_perm_fixedValues harr left).length_eq
  simpa using hlen.symm

theorem candidate_of_fixedValue {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool)
    {a : Nat} (ha : a ∈ fixedValues arr left) :
    CandidateWitness arr (pathMidpoint left a) := by
  simp only [fixedValues, List.mem_filter, decide_eq_true_eq] at ha
  have haRange : a ∈ (1...=arr.size).toArray := by
    rw [← valueList_toArray]
    simpa using ha.1
  have haArr : a ∈ arr := harr.mem_iff.mpr haRange
  have haList : a ∈ arr.toList := Array.mem_toList_iff.mpr haArr
  have hiList : arr.toList.idxOf a < arr.toList.length :=
    List.idxOf_lt_length_iff.mpr haList
  have hi : arr.toList.idxOf a < arr.size := by
    simpa using hiList
  let i := arr.toList.idxOf a
  have hvalue : arr[i] = a := by
    have hgetList := List.getElem_idxOf
      (xs := arr.toList) (x := a) hiList
    simpa only [i, Array.getElem_toList] using hgetList
  have habounds : 1 ≤ a ∧ a ≤ arr.size := by
    have haValue := ha.1
    simp [valueList] at haValue
    omega
  have hsum := leftBefore_add_rightBefore left a
  cases hleft : left a
  · right
    refine ⟨i, by simpa [i] using hi, ?_, ?_⟩
    · have hfixed : i =
          arr.size - rightBefore left a - 1 := by
        simpa [i, orientedIndex, hleft] using ha.2
      rw [hvalue]
      omega
    · rw [hvalue]
      apply pathMidpoint_eq_rightPoint left hleft (by simpa [i] using hi)
      have hfixed : i =
          arr.size - rightBefore left a - 1 := by
        simpa [i, orientedIndex, hleft] using ha.2
      omega
  · left
    refine ⟨i, by simpa [i] using hi, ?_, ?_⟩
    · have hfixed : i = leftBefore left a := by
        simpa [i, orientedIndex, hleft] using ha.2
      rw [hvalue]
      omega
    · rw [hvalue]
      apply pathMidpoint_eq_leftPoint left hleft
      have hfixed : i = leftBefore left a := by
        simpa [i, orientedIndex, hleft] using ha.2
      exact hfixed.symm

theorem fixedPoints_pairwise (arr : Array Nat) (left : Nat → Bool) :
    (fixedPoints arr left).Pairwise ComponentLE := by
  rw [fixedPoints, List.pairwise_map]
  apply List.Pairwise.imp_of_mem _
    ((valueList_pairwise arr.size).filter fun a =>
      arr.toList.idxOf a = orientedIndex arr.size left a)
  intro a b ha _ hab
  apply pathMidpoint_mono left
  · simp [valueList] at ha
    exact ha.1.1
  · exact hab

theorem hasCandidateChain_of_left {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) (left : Nat → Bool) :
    HasCandidateChain arr
      (agreements
        (Vector.mk (orientedArray (valueList arr.size) left)
          (orientedValueArray_size arr.size left))
        arr.toVector) := by
  let points := fixedPoints arr left
  have hcomp : points.Pairwise ComponentLE := fixedPoints_pairwise arr left
  have hsubset : points ⊆ sortedCandidatePoints arr := by
    intro p hp
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hp
    exact mem_sortedCandidatePoints_iff.mpr
      (candidate_of_fixedValue harr left ha)
  have hnodup : points.Nodup := by
    apply (fixedValues_nodup arr left).map_on
    intro a ha b hb hp
    simp only [fixedValues, List.mem_filter] at ha hb
    have haBounds : 1 ≤ a := by
      have haValue := ha.1
      simp [valueList] at haValue
      omega
    have hbBounds : 1 ≤ b := by
      have hbValue := hb.1
      simp [valueList] at hbValue
      omega
    have hda := pathMidpoint_diagonal left haBounds
    have hdb := pathMidpoint_diagonal left hbBounds
    rw [hp] at hda
    omega
  have hsubperm : List.Subperm points (sortedCandidatePoints arr) :=
    hnodup.subperm hsubset
  have hlex : points.Pairwise LexLE :=
    hcomp.imp fun hpq => componentLE_lexLE hpq
  letI : Std.Antisymm LexLE := ⟨fun _ _ => lexLE_antisymm⟩
  refine ⟨points,
    List.sublist_of_subperm_of_pairwise hsubperm hlex
      (sortedCandidatePoints_pairwise arr),
    hcomp, ?_⟩
  rw [show points.length = (fixedValues arr left).length by
    simp [points, fixedPoints]]
  exact fixedValues_length_eq_agreements harr left

theorem forced_candidate_index {arr : Array Nat} (left : Nat → Bool)
    {p : Nat × Nat} (hp : CandidateWitness arr p)
    {a : Nat} (ha : 1 ≤ a) (hpath : pathMidpoint left a = p) :
    ∃ (i : Nat) (hi : i < arr.size),
      pathMidpoint left arr[i] = p ∧
      orientedIndex arr.size left arr[i] = i := by
  rcases hp with ⟨i, hi, hcond, rfl⟩ | ⟨i, hi, hcond, rfl⟩
  · have hdiag := pathMidpoint_diagonal left ha
    rw [hpath, leftPoint_diagonal (by omega)] at hdiag
    have havalue : a = arr[i] := by omega
    subst a
    cases hleft : left arr[i]
    · have hfst := congrArg Prod.fst hpath
      simp [pathMidpoint, hleft, LeftPoint] at hfst
      omega
    · refine ⟨i, hi, hpath, ?_⟩
      have hfst := congrArg Prod.fst hpath
      simp [pathMidpoint, hleft, LeftPoint] at hfst
      simp [orientedIndex, hleft]
      omega
  · have hdiag := pathMidpoint_diagonal left ha
    rw [hpath, rightPoint_diagonal hi hcond] at hdiag
    have havalue : a = arr[i] := by omega
    subst a
    cases hleft : left arr[i]
    · refine ⟨i, hi, hpath, ?_⟩
      have hsnd := congrArg Prod.snd hpath
      simp [pathMidpoint, hleft, RightPoint] at hsnd
      simp [orientedIndex, hleft]
      omega
    · have hfst := congrArg Prod.fst hpath
      simp [pathMidpoint, hleft, RightPoint] at hfst
      omega

theorem chain_length_le_agreements {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray)
    {points : List (Nat × Nat)}
    (hsub : points.Sublist (sortedCandidatePoints arr))
    (hcomp : points.Pairwise ComponentLE) :
    ∃ left : Nat → Bool,
      points.length ≤
        agreements
          (Vector.mk (orientedArray (valueList arr.size) left)
            (orientedValueArray_size arr.size left))
          arr.toVector := by
  classical
  obtain ⟨hvalid, hfits⟩ := subchain_valid_and_fits harr hsub hcomp
  obtain ⟨left, hforced⟩ := exists_left_for_steps hvalid hfits
  have hnodup : points.Nodup :=
    (sortedCandidatePoints_nodup arr).sublist hsub
  have hwitness (p : {p // p ∈ points}) :
      ∃ (i : Nat) (hi : i < arr.size),
        pathMidpoint left arr[i] = p.1 ∧
        orientedIndex arr.size left arr[i] = i := by
    obtain ⟨a, ha, _, hpath⟩ := hforced p p.2
    exact forced_candidate_index left
      (mem_sortedCandidatePoints_iff.mp (hsub.mem p.2)) ha hpath
  let index : {p // p ∈ points} → Fin arr.size := fun p =>
    ⟨Classical.choose (hwitness p),
      (Classical.choose_spec (hwitness p)).1⟩
  have hindex (p : {p // p ∈ points}) :
      pathMidpoint left arr[index p] = p.1 ∧
        orientedIndex arr.size left arr[index p] = index p := by
    exact (Classical.choose_spec (hwitness p)).2
  let selected := points.attach.map index
  have hindexInjective : Function.Injective index := by
    intro p q hpq
    apply Subtype.ext
    calc
      p.1 = pathMidpoint left arr[index p] := (hindex p).1.symm
      _ = pathMidpoint left arr[index q] := by rw [hpq]
      _ = q.1 := (hindex q).1
  have hselectedNodup : selected.Nodup := by
    exact hnodup.attach.map hindexInjective
  have hsubset : selected ⊆ fixedIndices arr left := by
    intro i hi
    obtain ⟨p, _, hip⟩ := List.mem_map.mp hi
    rw [← hip]
    simp only [fixedIndices, List.mem_filter, List.mem_finRange, true_and,
      decide_eq_true_eq]
    exact (hindex p).2
  refine ⟨left, ?_⟩
  have hlen := (hselectedNodup.subperm hsubset).length_le
  rw [agreements_oriented_eq_fixedIndices harr left]
  simpa [selected] using hlen

theorem optimalAgreements_of_maximumCandidateChain {arr : Array Nat} {k : Nat}
    (harr : arr.Perm (1...=arr.size).toArray)
    (hmax : MaximumCandidateChain arr k) :
    OptimalAgreements arr k := by
  constructor
  · obtain ⟨points, hsub, hcomp, hlen⟩ := hmax.1
    obtain ⟨left, hlower⟩ :=
      chain_length_le_agreements harr hsub hcomp
    let x := orientedArray (valueList arr.size) left
    have hx : x.Perm (1...=arr.size).toArray :=
      orientedValueArray_perm arr.size left
    have hchain :=
      hasCandidateChain_of_left harr left
    have hupper := hmax.2 hchain
    have hagree :
        agreements (Vector.mk x (by simpa [x] using hx.size_eq))
          arr.toVector = k := by
      change agreements
        (Vector.mk (orientedArray (valueList arr.size) left)
          (orientedValueArray_size arr.size left)) arr.toVector = k
      omega
    exact ⟨x, hx, orientedValueArray_unimodal arr.size left, hagree⟩
  · intro x hx hunimodal
    obtain ⟨left, rfl⟩ := canonical_oriented_array hx hunimodal
    exact hmax.2 (hasCandidateChain_of_left harr left)

end Submission.Correspondence
