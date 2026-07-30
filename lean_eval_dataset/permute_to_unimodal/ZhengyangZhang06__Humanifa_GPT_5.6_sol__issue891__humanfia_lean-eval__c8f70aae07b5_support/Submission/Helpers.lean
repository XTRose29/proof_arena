import Submission.LIS

namespace Submission.Helpers

open LeanEval.ProgramVerification

/-!
The implementation in `ChallengeDeps` turns each position/value pair into the
midpoint of a step in a monotone lattice path.  A left-of-the-peak value is a
horizontal step and a right-of-the-peak value is a vertical step.  These small
definitions make that encoding explicit for the correctness proof.
-/

def LeftPoint (i a : Nat) : Nat × Nat :=
  (2 * i + 1, 2 * (a - i - 1))

def RightPoint (n i a : Nat) : Nat × Nat :=
  (2 * (a + i - n), 2 * (n - i) - 1)

def LexLEB (p q : Nat × Nat) : Bool :=
  p = q ∨ Prod.Lex (· < ·) (· < ·) p q

def LexLE (p q : Nat × Nat) : Prop :=
  LexLEB p q = true

def IsNDSubseq (s l : List Nat) : Prop :=
  s.Sublist l ∧ s.Pairwise (· ≤ ·)

def agreements {n : Nat} (a b : Vector Nat n) : Nat :=
  (List.finRange n).filter (fun i => a[i] = b[i]) |>.length

def orientedList (values : List Nat) (left : Nat → Bool) : List Nat :=
  values.filter left ++ (values.filter (!left ·)).reverse

def orientedArray (values : List Nat) (left : Nat → Bool) : Array Nat :=
  (orientedList values left).toArray

def valueList (n : Nat) : List Nat :=
  List.range' 1 n

def candidatePoints (arr : Array Nat) : Array (Nat × Nat) :=
  (arr.zipIdx.filter (fun (a, i) => i + 1 ≤ a)).map
      (fun (a, i) => LeftPoint i a) ++
    (arr.zipIdx.filter (fun (a, i) => arr.size ≤ a + i)).map
      (fun (a, i) => RightPoint arr.size i a)

def sortedCandidatePoints (arr : Array Nat) : List (Nat × Nat) :=
  (candidatePoints arr).toList.mergeSort (le := LexLEB)

def sortedCandidateOrdinates (arr : Array Nat) : Array Nat :=
  (sortedCandidatePoints arr).toArray.map (·.2)

def leftBefore (left : Nat → Bool) (a : Nat) : Nat :=
  ((Finset.range (a - 1)).filter fun k => left (k + 1)).card

def rightBefore (left : Nat → Bool) (a : Nat) : Nat :=
  ((Finset.range (a - 1)).filter fun k => ¬left (k + 1)).card

def pathMidpoint (left : Nat → Bool) (a : Nat) : Nat × Nat :=
  if left a then
    (2 * leftBefore left a + 1, 2 * rightBefore left a)
  else
    (2 * leftBefore left a, 2 * rightBefore left a + 1)

def ComponentLE (p q : Nat × Nat) : Prop :=
  p.1 ≤ q.1 ∧ p.2 ≤ q.2

def pointBefore (p : Nat × Nat) : Nat × Nat :=
  (p.1 / 2, p.2 / 2)

def pointAfter (p : Nat × Nat) : Nat × Nat :=
  ((p.1 + 1) / 2, (p.2 + 1) / 2)

def FitsAfter (p q : Nat × Nat) : Prop :=
  ComponentLE (pointAfter p) (pointBefore q)

def HasCandidateChain (arr : Array Nat) (k : Nat) : Prop :=
  ∃ points : List (Nat × Nat),
    points.Sublist (sortedCandidatePoints arr) ∧
    points.Pairwise ComponentLE ∧
    points.length = k

def MaximumCandidateChain (arr : Array Nat) (k : Nat) : Prop :=
  HasCandidateChain arr k ∧
    ∀ {m : Nat}, HasCandidateChain arr m → m ≤ k

def IsLNDSLength (l : List Nat) (k : Nat) : Prop :=
  (∃ s : List Nat, IsNDSubseq s l ∧ s.length = k) ∧
    ∀ {s : List Nat}, IsNDSubseq s l → s.length ≤ k

def OptimalAgreements (arr : Array Nat) (k : Nat) : Prop :=
  (∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
      Unimodal x ∧
        agreements (Vector.mk x (by simpa using hx.size_eq)) arr.toVector = k) ∧
    ∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
      Unimodal x →
        agreements (Vector.mk x (by simpa using hx.size_eq)) arr.toVector ≤ k

theorem lis_isLNDSLength (arr : Array Nat) :
    IsLNDSLength arr.toList (minRearrange.lis arr) := by
  simpa [IsLNDSLength, IsNDSubseq, Submission.LIS.IsLNDSLength,
    Submission.LIS.IsNDSubseq] using Submission.LIS.lis_returns_lnds arr

theorem minRearrange_eq_size_sub_lis (arr : Array Nat) :
    minRearrange arr =
      arr.size - minRearrange.lis (sortedCandidateOrdinates arr) :=
  rfl

theorem lexLE_iff_toLex_le (p q : Nat × Nat) :
    LexLE p q ↔ toLex p ≤ toLex q := by
  rw [Prod.Lex.toLex_le_toLex]
  simp only [LexLE, LexLEB, Prod.lex_def, Prod.ext_iff,
    decide_eq_true_eq]
  omega

theorem lexLE_trans {p q r : Nat × Nat} : LexLE p q → LexLE q r → LexLE p r := by
  simpa only [lexLE_iff_toLex_le] using
    (show toLex p ≤ toLex q →
        toLex q ≤ toLex r →
        toLex p ≤ toLex r from le_trans)

theorem lexLE_total (p q : Nat × Nat) : LexLE p q ∨ LexLE q p := by
  simpa only [lexLE_iff_toLex_le] using
    (le_total (toLex p) (toLex q))

theorem lexLE_antisymm {p q : Nat × Nat} : LexLE p q → LexLE q p → p = q := by
  intro hpq hqp
  have h : toLex p = toLex q :=
    le_antisymm
      ((lexLE_iff_toLex_le p q).mp hpq)
      ((lexLE_iff_toLex_le q p).mp hqp)
  simpa using congrArg ofLex h

theorem pairwise_mergeSort_lexLE (l : List (Nat × Nat)) :
    (l.mergeSort (le := LexLEB)).Pairwise LexLE := by
  classical
  letI : IsTrans (Nat × Nat) LexLE := ⟨fun _ _ _ => lexLE_trans⟩
  letI : Std.Total LexLE := ⟨lexLE_total⟩
  simpa [LexLE] using List.pairwise_mergeSort' LexLE l

theorem sortedCandidatePoints_pairwise (arr : Array Nat) :
    (sortedCandidatePoints arr).Pairwise LexLE :=
  pairwise_mergeSort_lexLE _

theorem lexLE_fst {p q : Nat × Nat} (h : LexLE p q) : p.1 ≤ q.1 := by
  have h' : p = q ∨ Prod.Lex (· < ·) (· < ·) p q := by
    simpa [LexLE, LexLEB] using h
  rcases h' with rfl | h
  · exact le_rfl
  · rcases Prod.lex_def.mp h with h | ⟨h, _⟩
    · exact h.le
    · exact h.le

theorem componentLE_lexLE {p q : Nat × Nat} (h : ComponentLE p q) : LexLE p q := by
  apply (lexLE_iff_toLex_le p q).2
  rw [Prod.Lex.toLex_le_toLex]
  rcases h with ⟨h₁, h₂⟩
  rcases h₁.eq_or_lt with h₁ | h₁
  · exact Or.inr ⟨h₁, h₂⟩
  · exact Or.inl h₁

theorem leftPoint_diagonal {i a : Nat} (h : i < a) :
    (LeftPoint i a).1 + (LeftPoint i a).2 = 2 * a - 1 := by
  simp only [LeftPoint]
  omega

theorem rightPoint_diagonal {n i a : Nat} (hi : i < n) (h : n ≤ a + i) :
    (RightPoint n i a).1 + (RightPoint n i a).2 = 2 * a - 1 := by
  simp only [RightPoint]
  omega

theorem leftPoint_fst_odd (i a : Nat) : (LeftPoint i a).1 % 2 = 1 := by
  simp [LeftPoint]

theorem rightPoint_fst_even (n i a : Nat) : (RightPoint n i a).1 % 2 = 0 := by
  simp [RightPoint]

theorem pointBefore_leftPoint {i a : Nat} (_h : i < a) :
    pointBefore (LeftPoint i a) = (i, a - i - 1) := by
  simp [pointBefore, LeftPoint]
  omega

theorem pointAfter_leftPoint {i a : Nat} (_h : i < a) :
    pointAfter (LeftPoint i a) = (i + 1, a - i - 1) := by
  simp [pointAfter, LeftPoint]
  omega

theorem pointBefore_rightPoint {n i a : Nat} (hi : i < n) (_h : n ≤ a + i) :
    pointBefore (RightPoint n i a) = (a + i - n, n - i - 1) := by
  simp [pointBefore, RightPoint]
  omega

theorem pointAfter_rightPoint {n i a : Nat} (hi : i < n) (_h : n ≤ a + i) :
    pointAfter (RightPoint n i a) = (a + i - n, n - i) := by
  simp [pointAfter, RightPoint]
  omega

theorem fitsAfter_left_left {i a j b : Nat} (hia : i < a) (hjb : j < b)
    (hcomp : ComponentLE (LeftPoint i a) (LeftPoint j b)) (hne : i ≠ j) :
    FitsAfter (LeftPoint i a) (LeftPoint j b) := by
  rw [FitsAfter, pointAfter_leftPoint hia, pointBefore_leftPoint hjb]
  unfold ComponentLE at hcomp ⊢
  simp only [LeftPoint] at hcomp
  omega

theorem fitsAfter_right_right {n i a j b : Nat}
    (hi : i < n) (hj : j < n) (hia : n ≤ a + i) (hjb : n ≤ b + j)
    (hcomp : ComponentLE (RightPoint n i a) (RightPoint n j b)) (hne : i ≠ j) :
    FitsAfter (RightPoint n i a) (RightPoint n j b) := by
  rw [FitsAfter, pointAfter_rightPoint hi hia, pointBefore_rightPoint hj hjb]
  unfold ComponentLE at hcomp ⊢
  simp only [RightPoint] at hcomp
  omega

theorem fitsAfter_left_right {n i a j b : Nat}
    (hia : i < a) (hj : j < n) (hjb : n ≤ b + j)
    (hcomp : ComponentLE (LeftPoint i a) (RightPoint n j b)) :
    FitsAfter (LeftPoint i a) (RightPoint n j b) := by
  rw [FitsAfter, pointAfter_leftPoint hia, pointBefore_rightPoint hj hjb]
  unfold ComponentLE at hcomp ⊢
  simp only [LeftPoint, RightPoint] at hcomp
  omega

theorem fitsAfter_right_left {n i a j b : Nat}
    (hi : i < n) (hia : n ≤ a + i) (hjb : j < b)
    (hcomp : ComponentLE (RightPoint n i a) (LeftPoint j b)) :
    FitsAfter (RightPoint n i a) (LeftPoint j b) := by
  rw [FitsAfter, pointAfter_rightPoint hi hia, pointBefore_leftPoint hjb]
  unfold ComponentLE at hcomp ⊢
  simp only [LeftPoint, RightPoint] at hcomp
  omega

theorem leftBefore_add_rightBefore (left : Nat → Bool) (a : Nat) :
    leftBefore left a + rightBefore left a = a - 1 := by
  simpa [leftBefore, rightBefore] using
    (Finset.card_filter_add_card_filter_not
      (s := Finset.range (a - 1)) (fun k => left (k + 1)))

theorem leftBefore_mono (left : Nat → Bool) : Monotone (leftBefore left) := by
  intro a b hab
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono (Nat.sub_le_sub_right hab 1)

theorem rightBefore_mono (left : Nat → Bool) : Monotone (rightBefore left) := by
  intro a b hab
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.range_mono (Nat.sub_le_sub_right hab 1)

theorem leftBefore_succ (left : Nat → Bool) (r : Nat) :
    leftBefore left (r + 2) =
      leftBefore left (r + 1) + if left (r + 1) then 1 else 0 := by
  simp only [leftBefore]
  have h₁ : r + 2 - 1 = r + 1 := by omega
  have h₂ : r + 1 - 1 = r := by omega
  rw [h₁, h₂, Finset.range_add_one, Finset.filter_insert]
  cases h : left (r + 1) <;>
    simp [h, Finset.card_insert_of_notMem, add_comm]

theorem rightBefore_succ (left : Nat → Bool) (r : Nat) :
    rightBefore left (r + 2) =
      rightBefore left (r + 1) + if left (r + 1) then 0 else 1 := by
  simp only [rightBefore]
  have h₁ : r + 2 - 1 = r + 1 := by omega
  have h₂ : r + 1 - 1 = r := by omega
  rw [h₁, h₂, Finset.range_add_one, Finset.filter_insert]
  cases h : left (r + 1) <;>
    simp [h, Finset.card_insert_of_notMem, add_comm]

theorem valueList_pairwise (n : Nat) : (valueList n).Pairwise (· < ·) := by
  exact (List.sortedLT_range' 1 n Nat.one_ne_zero).pairwise

theorem pathMidpoint_diagonal (left : Nat → Bool) {a : Nat} (ha : 1 ≤ a) :
    (pathMidpoint left a).1 + (pathMidpoint left a).2 = 2 * a - 1 := by
  have hsum := leftBefore_add_rightBefore left a
  simp only [pathMidpoint]
  split <;> omega

theorem pathMidpoint_mono (left : Nat → Bool) {a b : Nat}
    (ha : 1 ≤ a) (hab : a < b) :
    (pathMidpoint left a).1 ≤ (pathMidpoint left b).1 ∧
      (pathMidpoint left a).2 ≤ (pathMidpoint left b).2 := by
  have hlstep : leftBefore left (a + 1) =
      leftBefore left a + if left a then 1 else 0 := by
    have ha₁ : a - 1 + 1 = a := by omega
    have ha₂ : a - 1 + 2 = a + 1 := by omega
    simpa only [ha₁, ha₂] using leftBefore_succ left (a - 1)
  have hrstep : rightBefore left (a + 1) =
      rightBefore left a + if left a then 0 else 1 := by
    have ha₁ : a - 1 + 1 = a := by omega
    have ha₂ : a - 1 + 2 = a + 1 := by omega
    simpa only [ha₁, ha₂] using rightBefore_succ left (a - 1)
  have hlmono := leftBefore_mono left (show a + 1 ≤ b by omega)
  have hrmono := rightBefore_mono left (show a + 1 ≤ b by omega)
  cases hla : left a <;> cases hlb : left b <;>
    simp [hla] at hlstep hrstep <;>
    simp [pathMidpoint, hla, hlb] <;> omega

theorem componentLE_of_sorted_subseq {points sorted : List (Nat × Nat)}
    (hsorted : sorted.Pairwise LexLE) (hsub : points.Sublist sorted)
    (hsnd : (points.map (·.2)).Pairwise (· ≤ ·)) :
    points.Pairwise ComponentLE := by
  have hx : points.Pairwise (fun p q => p.1 ≤ q.1) :=
    (hsorted.sublist hsub).imp fun h => lexLE_fst h
  rw [List.pairwise_map] at hsnd
  clear hsub hsorted
  revert hx hsnd
  induction points with
  | nil => simp
  | cons p ps ih =>
      intro hx hsnd
      simp only [List.pairwise_cons] at hx hsnd ⊢
      constructor
      · intro q hq
        exact ⟨hsnd.1 q hq, hx.1 q hq⟩
      · exact ih hx.2 hsnd.2

theorem pathMidpoint_eq_leftPoint (left : Nat → Bool) {a i : Nat}
    (hleft : left a = true) (hi : leftBefore left a = i) :
    pathMidpoint left a = LeftPoint i a := by
  have hsum := leftBefore_add_rightBefore left a
  simp [pathMidpoint, LeftPoint, hleft]
  omega

theorem pathMidpoint_eq_rightPoint (left : Nat → Bool) {n a i : Nat}
    (hleft : left a = false) (hi : i < n)
    (hpos : rightBefore left a + 1 = n - i) :
    pathMidpoint left a = RightPoint n i a := by
  have hsum := leftBefore_add_rightBefore left a
  simp [pathMidpoint, RightPoint, hleft]
  omega

theorem lift_isNDSubseq_map {α : Type*} {f : α → Nat} {s : List Nat} {l : List α}
    (h : IsNDSubseq s (l.map f)) :
    ∃ t : List α, t.Sublist l ∧ t.map f = s ∧ s.Pairwise (· ≤ ·) := by
  obtain ⟨t, ht, rfl⟩ := List.sublist_map_iff.mp h.1
  exact ⟨t, ht, rfl, h.2⟩

theorem lift_sortedCandidateOrdinates {arr : Array Nat} {s : List Nat}
    (h : IsNDSubseq s (sortedCandidateOrdinates arr).toList) :
    ∃ points : List (Nat × Nat),
      points.Sublist (sortedCandidatePoints arr) ∧
      points.map (·.2) = s ∧
      points.Pairwise ComponentLE := by
  have h' : IsNDSubseq s ((sortedCandidatePoints arr).map (·.2)) := by
    simpa [sortedCandidateOrdinates] using h
  obtain ⟨points, hpoints, hmap, hs⟩ := lift_isNDSubseq_map h'
  refine ⟨points, hpoints, hmap, ?_⟩
  apply componentLE_of_sorted_subseq (sortedCandidatePoints_pairwise arr) hpoints
  simpa [hmap] using hs

theorem maximumCandidateChain_of_lnds {arr : Array Nat} {k : Nat}
    (h : IsLNDSLength (sortedCandidateOrdinates arr).toList k) :
    MaximumCandidateChain arr k := by
  constructor
  · obtain ⟨s, hs, hlen⟩ := h.1
    obtain ⟨points, hsub, hmap, hcomp⟩ := lift_sortedCandidateOrdinates hs
    refine ⟨points, hsub, hcomp, ?_⟩
    have := congrArg List.length hmap
    simpa [hlen] using this
  · rintro m ⟨points, hsub, hcomp, rfl⟩
    have hnd : IsNDSubseq (points.map (·.2))
        (sortedCandidateOrdinates arr).toList := by
      constructor
      · simpa [sortedCandidateOrdinates] using hsub.map (fun p => p.2)
      · rw [List.pairwise_map]
        exact hcomp.imp fun hpq => hpq.2
    simpa using h.2 hnd

theorem filter_append_filter_not_perm {α : Type*} (p : α → Bool) (l : List α) :
    List.Perm (l.filter p ++ l.filter (!p ·)) l := by
  induction l with
  | nil => simp
  | cons a l ih =>
      by_cases ha : p a
      · simpa [ha] using ih.cons a
      · have hm := List.perm_middle (a := a)
          (l₁ := l.filter p) (l₂ := l.filter (!p ·))
        exact (by simpa [ha] using hm.trans (ih.cons a))

theorem orientedList_perm (values : List Nat) (left : Nat → Bool) :
    List.Perm (orientedList values left) values := by
  unfold orientedList
  exact (List.Perm.append_left _ (values.filter (!left ·)).reverse_perm).trans
    (filter_append_filter_not_perm left values)

theorem orientedArray_unimodal {values : List Nat} (hvalues : values.Pairwise (· < ·))
    (left : Nat → Bool) :
    Unimodal (orientedArray values left) := by
  refine ⟨(values.filter left).toArray,
    ((values.filter (!left ·)).reverse).toArray, ?_, ?_, ?_⟩
  · simp [orientedArray, orientedList]
  · simpa using hvalues.filter left
  · simpa [List.pairwise_reverse] using (hvalues.filter (!left ·)).reverse

theorem orientedValueArray_unimodal (n : Nat) (left : Nat → Bool) :
    Unimodal (orientedArray (valueList n) left) :=
  orientedArray_unimodal (valueList_pairwise n) left

theorem valueList_toArray (n : Nat) :
    (valueList n).toArray = (1...=n).toArray := by
  apply Array.ext
  · simp [valueList]
  · intro i hi₁ hi₂
    simp [valueList]

theorem orientedValueArray_perm (n : Nat) (left : Nat → Bool) :
    (orientedArray (valueList n) left).Perm (1...=n).toArray := by
  rw [← valueList_toArray]
  simpa [orientedArray] using
    (orientedList_perm (valueList n) left).toArray

theorem differences_add_agreements {n : Nat} (a b : Vector Nat n) :
    differences a b + agreements a b = n := by
  have h := (List.finRange n).length_eq_length_filter_add
    (fun i => decide (a[i] = b[i]))
  calc
    differences a b + agreements a b =
        agreements a b + differences a b := Nat.add_comm _ _
    _ = n := by simpa [differences, agreements] using h.symm

theorem differences_eq_sub_agreements {n : Nat} (a b : Vector Nat n) :
    differences a b = n - agreements a b := by
  have h := differences_add_agreements a b
  omega

theorem correctness_of_optimal_agreements {arr : Array Nat} {k : Nat}
    (hmin : minRearrange arr = arr.size - k)
    (hopt : OptimalAgreements arr k) :
    (∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
        Unimodal x ∧
          differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector =
            minRearrange arr) ∧
      (∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
        Unimodal x →
          minRearrange arr ≤
            differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector) := by
  constructor
  · obtain ⟨x, hx, hunimodal, hagree⟩ := hopt.1
    refine ⟨x, hx, hunimodal, ?_⟩
    rw [differences_eq_sub_agreements, hagree, hmin]
  · intro x hx hunimodal
    have hagree := hopt.2 x hx hunimodal
    rw [hmin, differences_eq_sub_agreements]
    omega

end Submission.Helpers
