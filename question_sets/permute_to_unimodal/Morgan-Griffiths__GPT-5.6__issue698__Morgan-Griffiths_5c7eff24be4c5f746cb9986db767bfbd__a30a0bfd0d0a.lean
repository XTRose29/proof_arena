import ChallengeDeps
import Submission.Helpers

namespace Submission

namespace SourceDefinitions
namespace LeanEval
namespace ProgramVerification

/-!
Given an array `arr` which is a permutation of the numbers from `1` to `arr.size`,
`minRearrange` computes the size of the smallest subset of indices within the array
that may be permuted such that the array becomes first increasing and then decreasing.
For example, `minRearrange #[1, 6, 4, 3, 2, 5] = 2` since we can swap the first and
the last element to achieve the desired property.

The given efficient implementation computes the answer in `O(n log n)`.

Examples:
* `minRearrange #[] = 0`
* `minRearrange #[1, 6, 4, 3, 2, 5] = 2`
* `minRearrange #[4, 3, 2, 1, 5] = 4`
* `minRearrange #[1, 2, 4, 3] = 0`
* `minRearrange #[1, 2, 7, 4, 5, 6, 3, 8, 9, 10] = 2`
-/

def minRearrange (arr : Array Nat) : Nat :=
  let n := arr.size
  let v :=
    (arr.zipIdx.filter (fun (a, i) => i + 1 ≤ a)).map (fun (a, i) => (2 * i + 1, 2 * (a - i - 1))) ++
    (arr.zipIdx.filter (fun (a, i) => n ≤ a + i)).map (fun (a, i) => (2 * (a + i - n), 2 * (n - i) - 1))
  let vv := (v.toList.mergeSort (le := fun a b => a = b ∨ Prod.Lex (· < ·) (· < ·) a b)).toArray
  n - lis (vv.map (·.2))
where
  lis (arr : Array Nat) : Nat :=
    if h : arr = #[] then
      0
    else
      let dp := Array.replicate arr.size (arr.max h + 1)
      loop arr 0 0 dp (by grind)
  loop (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) : Nat :=
    if hi' : i = arr.size then
      ans
    else
      let pos := upperBound arr[i] dp
      loop arr (max ans (pos + 1)) (i + 1) (dp.set! pos (arr[i])) (by grind)
  upperBound (needle : Nat) (arr : Array Nat) : Nat :=
    go needle arr 0 arr.size
  go (needle : Nat) (arr : Array Nat) (lo hi : Nat) (hhi : hi ≤ arr.size := by omega) : Nat :=
    if h : lo < hi then
      let mid := lo + (hi - lo) / 2
      if arr[mid] ≤ needle then
        go needle arr (mid + 1) hi
      else
        go needle arr lo mid
    else lo

/--
Property stating that the array can be decomposed into a strictly increasing and a strictly
decreasing part.
-/
def Unimodal (arr : Array Nat) : Prop :=
  ∃ b b', arr = b ++ b' ∧ b.toList.Pairwise (· < ·) ∧ b'.toList.Pairwise (· > ·)

/--
The number of indices at which the two given vectors differ
-/
def differences {n : Nat} (a b : Vector Nat n) : Nat :=
  (List.finRange n).filter (fun i => a[i] ≠ b[i]) |>.length



end ProgramVerification
end LeanEval
end SourceDefinitions

open LeanEval.ProgramVerification
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/

namespace LeanEval.ProgramVerification
/-- Elementary bounds for the binary search used by `minRearrange`.  No sortedness
assumption is needed for these bounds.  Having this explicitly is useful because
`set!` in the patience-sorting loop only changes an entry when the returned
position is inside the table. -/
theorem mr_go_bounds (needle : Nat) (arr : Array Nat) (lo hi : Nat)
    (hhi : hi ≤ arr.size := by omega) (hlo : lo ≤ hi) :
    lo ≤ minRearrange.go needle arr lo hi hhi ∧
      minRearrange.go needle arr lo hi hhi ≤ hi := by
  generalize hd : hi - lo = d
  induction d using Nat.strong_induction_on generalizing lo hi with
  | h d ih =>
    rw [minRearrange.go.eq_1]
    split <;> rename_i hlt
    · dsimp
      -- the midpoint of a nonempty half-open interval is in that interval
      have hmlo : lo ≤ lo + (hi - lo) / 2 := by omega
      have hmhi : lo + (hi - lo) / 2 < hi := by omega
      split <;> rename_i hcmp
      · have hd' : hi - (lo + (hi - lo) / 2 + 1) < d := by omega
        have hrec := ih _ hd' (lo + (hi - lo) / 2 + 1) hi hhi (by omega) (by rfl)
        constructor
        · exact le_trans (by omega) hrec.1
        · exact hrec.2
      · have hhmid : lo + (hi - lo) / 2 ≤ arr.size := by omega
        have hd' : (lo + (hi - lo) / 2) - lo < d := by omega
        have hrec := ih _ hd' lo (lo + (hi - lo) / 2) hhmid (by omega) (by rfl)
        constructor
        · exact hrec.1
        · exact le_trans hrec.2 (by omega)
    · simpa


/-- A convenient Prop formulation of sortedness of an array.  It mentions just the
entries and their bounds, rather than a particular list representation. -/
def MRSorted (a : Array Nat) : Prop :=
  ∀ (i j : Nat) (hi : i < a.size) (hj : j < a.size), i ≤ j → a[i] ≤ a[j]

/-- Partition property of `go` (the upper-bound binary search).  It is phrased on a
half open subinterval; this lets it be used also on the recursive calls. -/
theorem mr_go_partition (needle : Nat) (arr : Array Nat) (lo hi : Nat)
    (hhi : hi ≤ arr.size := by omega) (hs : MRSorted arr) (hlo : lo ≤ hi) :
    let p := minRearrange.go needle arr lo hi hhi
    (∀ (j : Nat) (hj : j < arr.size), lo ≤ j → j < p → arr[j] ≤ needle) ∧
    (∀ (j : Nat) (hj : j < arr.size), p ≤ j → j < hi → needle < arr[j]) := by
  dsimp
  generalize hd : hi - lo = d
  induction d using Nat.strong_induction_on generalizing lo hi with
  | h d ih =>
    rw [minRearrange.go.eq_1]
    split <;> rename_i hlt
    · dsimp
      have hmlo : lo ≤ lo + (hi - lo) / 2 := by omega
      have hmhi : lo + (hi - lo) / 2 < hi := by omega
      have hmsz : lo + (hi - lo) / 2 < arr.size := by omega
      split <;> rename_i hcmp
      · -- the midpoint, and everything before it, are small
        have hd' : hi - (lo + (hi - lo) / 2 + 1) < d := by omega
        have hrec := ih _ hd' (lo + (hi - lo) / 2 + 1) hi hhi (by omega) (by rfl)
        -- we will also need that the recursive answer is in the right interval
        have hb := mr_go_bounds needle arr (lo + (hi - lo) / 2 + 1) hi hhi (by omega)
        constructor
        · intro j hj hjlo hjp
          by_cases hjmid : j ≤ lo + (hi - lo) / 2
          · exact le_trans (hs _ _ hj hmsz hjmid) hcmp
          · have hjlow : lo + (hi - lo) / 2 + 1 ≤ j := by omega
            exact hrec.1 j hj hjlow hjp
        · intro j hj hjp hjhi'
          exact hrec.2 j hj hjp hjhi'
      · -- the midpoint is already too large
        have hhmid : lo + (hi - lo) / 2 ≤ arr.size := by omega
        have hd' : (lo + (hi - lo) / 2) - lo < d := by omega
        have hrec := ih _ hd' lo (lo + (hi - lo) / 2) hhmid (by omega) (by rfl)
        have hb := mr_go_bounds needle arr lo (lo + (hi - lo) / 2) hhmid (by omega)
        constructor
        · intro j hj hjlo hjp
          exact hrec.1 j hj hjlo hjp
        · intro j hj hjp hjhi'
          by_cases hjmid : j < lo + (hi - lo) / 2
          · exact hrec.2 j hj hjp hjmid
          · have hle : lo + (hi - lo) / 2 ≤ j := by omega
            have hmle : arr[lo + (hi - lo) / 2] ≤ arr[j] := hs _ _ hmsz hj hle
            -- `¬ arr[mid] ≤ needle` is the branch we are in
            exact lt_of_lt_of_le (by omega : needle < arr[lo + (hi - lo) / 2]) hmle
    · constructor <;> intro j hj h1 h2 <;> omega


/-- Usual whole-array upper bound: it is in the array and cuts it into values
`≤ needle` and values `> needle`. -/
theorem mr_upperBound_spec (needle : Nat) (arr : Array Nat) (hs : MRSorted arr) :
    let p := minRearrange.upperBound needle arr
    p ≤ arr.size ∧
    (∀ (j : Nat) (hj : j < arr.size), j < p → arr[j] ≤ needle) ∧
    (∀ (j : Nat) (hj : j < arr.size), p ≤ j → needle < arr[j]) := by
  dsimp
  rw [minRearrange.upperBound.eq_1]
  have hb := mr_go_bounds needle arr 0 arr.size (by omega) (by omega)
  have hp := mr_go_partition needle arr 0 arr.size (by omega) hs (by omega)
  exact ⟨hb.2, (by
    constructor
    · intro j hj hjp
      exact hp.1 j hj (by omega) hjp
    · intro j hj hjp
      exact hp.2 j hj hjp hj)⟩


/-- Replacing a cell between its two neighbours preserves sortedness.  This version
uses `set!`, the exact operation in the executable loop, so its simple size and
out-of-bounds behaviour need not be hidden in a later invariant. -/
theorem mr_sorted_setBang (a : Array Nat) (p v : Nat) (hs : MRSorted a)
    (hl : ∀ (i : Nat) (hi : i < a.size), i < p → a[i] ≤ v)
    (hr : ∀ (j : Nat) (hj : j < a.size), p ≤ j → v ≤ a[j]) :
    MRSorted (a.set! p v) := by
  intro i j hi hj hij
  have hi' : i < a.size := by
    simpa using (show i < (a.set! p v).size from hi)
  have hj' : j < a.size := by
    simpa using (show j < (a.set! p v).size from hj)
  -- rewriting the size proofs first avoids casts on `GetElem`
  have ei : (a.set! p v)[i]'hi = (if p = i then v else a[i]) := by
    simpa [Array.set!] using (Array.getElem_setIfInBounds (xs:=a) (i:=p) (a:=v) hi')
  have ej : (a.set! p v)[j]'hj = (if p = j then v else a[j]) := by
    simpa [Array.set!] using (Array.getElem_setIfInBounds (xs:=a) (i:=p) (a:=v) hj')
  rw [ei, ej]
  split <;> rename_i hpi
  · split <;> rename_i hpj
    · exact le_rfl
    · exact hr _ hj' (by omega)
  · split <;> rename_i hpj
    · exact hl _ hi' (by omega)
    · exact hs _ _ hi' hj' hij

/-- In particular it is valid to insert the needle at its upper bound. -/
theorem mr_sorted_insert (needle : Nat) (a : Array Nat)
    (hs : MRSorted a) :
    MRSorted (a.set! (minRearrange.upperBound needle a) needle) := by
  have hp := mr_upperBound_spec needle a hs
  apply mr_sorted_setBang a (minRearrange.upperBound needle a) needle hs
  · intro i hi hip
    exact hp.2.1 _ hi hip
  · intro j hj hjp
    exact Nat.le_of_lt (hp.2.2 _ hj hjp)


/-- Every entry of a non-empty array of naturals is below `Array.max`. -/
theorem mr_get_le_max (arr : Array Nat) (hne : arr ≠ #[]) (i : Nat) (hi : i < arr.size) :
    arr[i] ≤ arr.max hne := by
  have hn : arr.toList ≠ [] := by
    intro h
    have : arr = #[] := Array.toList_eq_nil_iff.mp h
    contradiction
  have hm : arr[i] ∈ arr.toList := by
    simpa using (List.getElem_mem (l:=arr.toList) (n:=i) (by simpa using hi))
  have hl : arr[i] ≤ arr.toList.max hn := List.le_max_of_mem hm
  exact le_trans hl (le_of_eq (Array.max_toList (xs:=arr) (h:=hn)))

/-- A weak (but often handy) invariant of the patience loop: starting with a
sorted table filled by a sentinel above every input, the returned answer never
exceeds the size of the input.  The proof keeps the untouched sentinel tail and
so also justifies that `set!` really writes a cell on every iteration. -/
theorem mr_loop_le_size (arr : Array Nat) (hne : arr ≠ #[])
    (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size)
    (hsize : dp.size = arr.size)
    (hs : MRSorted dp)
    (htail : ∀ (j : Nat) (hj : j < dp.size), i ≤ j → dp[j] = arr.max hne + 1)
    (ha : ans ≤ i) :
    minRearrange.loop arr ans i dp hi ≤ arr.size := by
  generalize hd : arr.size - i = fuel
  induction fuel using Nat.strong_induction_on generalizing ans i dp with
  | h fuel ih =>
    rw [minRearrange.loop.eq_1]
    split <;> rename_i done
    · -- final test
      omega
    · dsimp
      have hii : i < arr.size := by omega
      have hi_dp : i < dp.size := by omega
      have hneedle : arr[i] < arr.max hne + 1 := by
        have := mr_get_le_max arr hne i hii
        omega
      let p : Nat := minRearrange.upperBound arr[i] dp
      have hpSpec := mr_upperBound_spec arr[i] dp hs
      have hpbound : p ≤ i := by
        by_contra hn
        have hip : i < p := by omega
        have hle : dp[i] ≤ arr[i] := hpSpec.2.1 i hi_dp hip
        have heq : dp[i] = arr.max hne + 1 := htail i hi_dp (by omega)
        rw [heq] at hle
        omega
      have hp_lt : p < dp.size := by omega
      have hnewsize : (dp.set! p arr[i]).size = arr.size := by simpa using hsize
      have hnewsort : MRSorted (dp.set! p arr[i]) := by
        simpa [p] using (mr_sorted_insert arr[i] dp hs)
      have hnewtail : ∀ (j : Nat) (hj : j < (dp.set! p arr[i]).size),
          i + 1 ≤ j → (dp.set! p arr[i])[j] = arr.max hne + 1 := by
        intro j hj hjij
        have hjold : j < dp.size := by simpa using hj
        have hnepj : p ≠ j := by omega
        have ej : (dp.set! p arr[i])[j]'hj = dp[j] := by
          simpa [Array.set!, hnepj] using
            (Array.getElem_setIfInBounds (xs:=dp) (i:=p) (a:=arr[i]) hjold)
        rw [ej]
        exact htail j hjold (by omega)
      have hnewans : max ans (p + 1) ≤ i + 1 := by omega
      have hfuel : arr.size - (i + 1) < fuel := by omega
      exact ih _ hfuel (max ans (p+1)) (i+1) (dp.set! p arr[i])
        (by omega) hnewsize hnewsort hnewtail hnewans (by omega)


/-- Even without the optimality argument, the executable LIS routine has the
essential size bound. -/
theorem mr_lis_le_size (a : Array Nat) : minRearrange.lis a ≤ a.size := by
  rw [minRearrange.lis.eq_1]
  split <;> rename_i hne
  · omega
  · let d : Array Nat := Array.replicate a.size (a.max hne + 1)
    have hdsize : d.size = a.size := by simp [d]
    have hdsort : MRSorted d := by
      intro i j hi hj hij
      simp [d, Array.getElem_replicate]
    have hdtail : ∀ (j : Nat) (hj : j < d.size),
        0 ≤ j → d[j] = a.max hne + 1 := by
      intro j hj _
      exact Array.getElem_replicate hj
    exact mr_loop_le_size a hne 0 0 d (by omega) hdsize hdsort hdtail (by omega)


/-- Complement lengths for a Boolean filter (arrays and lists in the executable
code use Boolean predicates). -/
theorem mr_filter_compl_length {α : Type} (l : List α) (p : α → Bool) :
    (l.filter p).length + (l.filter (fun x => ! p x)).length = l.length := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    cases hp : p x <;> simp [List.filter, hp]
    · omega
    · omega

/-- Complement form of `differences`: the positions it counts are just the
complement (inside `finRange`) of the fixed positions. -/
theorem mr_differences_compl {n : Nat} (a b : Vector Nat n) :
    differences a b =
      n - (((List.finRange n).filter (fun i => a[i] = b[i])).length) := by
  unfold differences
  let p : (Fin n → Bool) := fun i => decide (a[i] ≠ b[i])
  have hc := mr_filter_compl_length (List.finRange n) p
  have heq : (fun i : Fin n => ! p i) = (fun i => decide (a[i] = b[i])) := by
    funext i
    by_cases h : a[i] = b[i]
    · have h' : a[ i.val ] = b[ i.val ] := by simpa using h
      simp [p, h, h']
    · have h' : a[ i.val ] ≠ b[ i.val ] := by
        intro e; exact h (by simpa using e)
      simp [p, h, h']
  rw [heq] at hc
  change ((List.finRange n).filter p).length = _
  have hlen : (List.finRange n).length = n := by simp
  rw [hlen] at hc
  omega


/-- Get-element form of the elementary spacing fact for a strictly increasing
list of naturals.  Stating it with a movable lower bound makes the induction on
the first element transparent. -/
theorem mr_inc_get_lower (l : List Nat) (B : Nat)
    (hp : l.Pairwise (fun a b : Nat => a < b))
    (hb : ∀ x ∈ l, B ≤ x) (i : Nat) (hi : i < l.length) :
    B + i ≤ l[i] := by
  induction l generalizing B i with
  | nil => simp at hi
  | cons x xs ih =>
    have hh := (List.pairwise_cons.mp hp)
    cases i with
    | zero =>
      simpa using (hb x (by simp))
    | succ i =>
      have hit : i < xs.length := by simpa using hi
      have hb' : ∀ y ∈ xs, B + 1 ≤ y := by
        intro y hy
        have hxy : x < y := hh.1 y hy
        have hx : B ≤ x := hb x (by simp)
        omega
      have hz := ih (B+1) hh.2 hb' i hit
      simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hz

/-- The same spacing fact read from the right for decreasing lists. -/
theorem mr_dec_get_lower (l : List Nat) (B : Nat)
    (hp : l.Pairwise (fun a b : Nat => a > b))
    (hb : ∀ x ∈ l, B ≤ x) (i : Nat) (hi : i < l.length) :
    B + (l.length - i - 1) ≤ l[i] := by
  -- reverse it and appeal to the increasing lemma
  let r := l.reverse
  have hr : r.Pairwise (fun a b : Nat => a < b) := by
    -- pairwise on the reverse switches the relation
    rw [List.pairwise_reverse]
    simpa [Function.swap_def] using hp
  have hrb : ∀ x ∈ r, B ≤ x := by
    intro x hx; apply hb x
    simpa [r] using hx
  have hir : l.length - 1 - i < r.length := by
    dsimp [r]
    simp
    omega
  have hget := mr_inc_get_lower r B hr hrb (l.length - 1 - i) hir
  have heq : r[l.length - 1 - i]'hir = l[i] := by
    -- standard getElem rule for reverse; the indices here are equal by `omega`
    simp [r, List.getElem_reverse]
    congr 1 <;> omega
  rw [heq] at hget
  have heqidx : l.length - 1 - i = l.length - i - 1 := by omega
  simpa [heqidx] using hget


/-- Positivity and monotonicity already give the elementary capacity tests used
when creating points: entries on the left meet their left index, entries on the
right meet their distance from the end. -/
theorem mr_unimodal_eligible (x : Array Nat) (hu : Unimodal x)
    (hpos : ∀ (i : Nat) (hi : i < x.size), 1 ≤ x[i]) :
    ∃ k, k ≤ x.size ∧
      (∀ (i : Nat) (hi : i < x.size), i < k → i + 1 ≤ x[i]) ∧
      (∀ (i : Nat) (hi : i < x.size), k ≤ i → x.size ≤ x[i] + i) := by
  rcases hu with ⟨b, c, hx, hb, hc⟩
  subst x
  have hbpos : ∀ y ∈ b.toList, 1 ≤ y := by
    intro y hy
    rcases List.getElem_of_mem hy with ⟨t, ht, he⟩
    have ht' : t < b.size := by simpa using ht
    have htall : t < (b ++ c).size := by simp; omega
    have hv := hpos t htall
    rw [Array.getElem_append_left (h:=htall) ht'] at hv
    have hbe : b[t]'ht' = y := by simpa using he
    rwa [hbe] at hv
  have hcpos : ∀ y ∈ c.toList, 1 ≤ y := by
    intro y hy
    rcases List.getElem_of_mem hy with ⟨t, ht, he⟩
    have ht' : t < c.size := by simpa using ht
    have htall : b.size + t < (b ++ c).size := by simp; omega
    have hv := hpos (b.size+t) htall
    rw [Array.getElem_append_right (h:=htall) (by omega : b.size ≤ b.size+t)] at hv
    have hsub : b.size + t - b.size = t := by omega
    simp [hsub] at hv
    have hec : (c)[t] = y := by simpa using he
    -- all get-element proof arguments are irrelevant
    rw [hec] at hv
    exact hv
  refine ⟨b.size, ?_, ?_, ?_⟩
  · simp
  · intro i hi hik
    have hi' : i < b.size := hik
    have hv := mr_inc_get_lower b.toList 1 hb hbpos i (by simpa using hi')
    have he : (b ++ c)[i]'hi = b.toList[i] := by
      rw [Array.getElem_append_left (h:=hi) hi']
      simp [Array.getElem_toList]
    rw [he]
    simpa [Nat.add_comm] using hv
  · intro i hi hki
    have hisum : i < b.size + c.size := by simpa using hi
    have hilen : i - b.size < c.size := by omega
    have hv := mr_dec_get_lower c.toList 1 hc hcpos (i-b.size) (by simpa using hilen)
    have he : (b ++ c)[i]'hi = c.toList[i-b.size] := by
      rw [Array.getElem_append_right (h:=hi) hki]
      simp [Array.getElem_toList]
    rw [he]
    simp only [Array.size_append]
    have hv' : 1 + (c.size - (i-b.size) - 1) ≤ c.toList[i-b.size] := by
      simpa using hv
    omega


/-- A single value which is eligible for both sides of the peak can never be
counted twice.  Its right-hand point is strictly *before* its left-hand point
in the first coordinate, but strictly *after* it in the second.  This small
arithmetic fact (using the parity offsets from the construction) is useful in
relating chains of points to fixed entries. -/
theorem mr_two_points_cross (n i a : Nat) (hi : i < n) (ha : a ≤ n)
    (hl : i + 1 ≤ a) (hr : n ≤ a + i) :
    2 * (a + i - n) < 2*i + 1 ∧
      2 * (a - i - 1) < 2 * (n-i) - 1 := by
  omega

/-- On the left arm, increasing indices have nondecreasing second coordinates
exactly when enough values have been skipped to fill the gap. -/
theorem mr_left_gap {i j a b : Nat} (hi : i + 1 ≤ a) (hj : j + 1 ≤ b)
    (hij : i ≤ j) :
    a - i - 1 ≤ b - j - 1 ↔ a + (j - i) ≤ b := by
  omega

/-- Analogous gap arithmetic when the right arm is read backwards. -/
theorem mr_right_gap {n i j a b : Nat} (hi : i ≤ n) (hj : j ≤ n)
    (ha : n ≤ a + i) (hb : n ≤ b + j) (hji : j ≤ i) :
    a + i - n ≤ b + j - n ↔ a + (i-j) ≤ b := by
  omega


/-- Off-by-one range bounds for an entry of a permutation of `1...=n`. -/
theorem mr_perm_entry_bounds {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) (i : Nat) (hi : i < a.size) :
    1 ≤ a[i] ∧ a[i] ≤ a.size := by
  have hm : a[i] ∈ a.toList := by
    simpa using (List.getElem_mem (l:=a.toList) (n:=i) (by simpa using hi))
  have hm' : a[i] ∈ ((1...=a.size).toArray).toList :=
    (hp.toList.mem_iff).mp hm
  have hm'' : a[i] ∈ (1...=a.size).toArray := (Array.mem_def).2 hm'
  have hmr : a[i] ∈ (1...=a.size) :=
    (Std.Rcc.mem_toArray_iff_mem).mp hm''
  exact (Std.Rcc.mem_iff.mp hmr)

/-- Consequently the capacity lemma applies to every unimodal permutation of
the range, with the right 1-based constants. -/
theorem mr_perm_unimodal_eligible {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) (hu : Unimodal a) :
    ∃ k, k ≤ a.size ∧
      (∀ (i : Nat) (hi : i < a.size), i < k → i + 1 ≤ a[i]) ∧
      (∀ (i : Nat) (hi : i < a.size), k ≤ i → a.size ≤ a[i] + i) := by
  apply mr_unimodal_eligible a hu
  intro i hi
  exact (mr_perm_entry_bounds hp i hi).1


/-- A list of indices witnessing a (weakly) increasing subsequence in the
first `pref` cells of `a`.  The algorithm uses `upperBound`, so equal values
are allowed.  `getD` is used only to keep the relation on indices simple; all
indices in a witness are in range. -/
def MRNSub (a : Array Nat) (pref : Nat) (s : List Nat) : Prop :=
  (∀ q ∈ s, q < pref) ∧
  s.Pairwise (fun q r : Nat => q < r) ∧
  s.Pairwise (fun q r : Nat => a.getD q 0 ≤ a.getD r 0)

/-- In a globally pairwise nondecreasing list every entry is below the last
one.  Using `dropLast ++ [getLast]` makes this independent of any adjacent
form of sortedness. -/
theorem mr_pairwise_le_last {α : Type} (f : α → Nat) (l : List α)
    (hn : l ≠ []) (hp : l.Pairwise (fun x y => f x ≤ f y)) :
    ∀ x ∈ l, f x ≤ f (l.getLast hn) := by
  intro x hx
  have he := List.dropLast_append_getLast hn
  have hx' : x ∈ l.dropLast ++ [l.getLast hn] := by simpa [he]
  have hp' : (l.dropLast ++ [l.getLast hn]).Pairwise
      (fun x y => f x ≤ f y) := by
    rw [he]
    exact hp
  have hpa := List.pairwise_append.mp hp'
  rcases (List.mem_append.mp hx') with hfront | htail
  · exact hpa.2.2 x hfront (l.getLast hn) (by simp)
  · have ex : x = l.getLast hn := by simpa using htail
    subst x
    exact le_rfl

/-- The same useful observation for strictly increasing lists of indices. -/
theorem mr_index_le_last (l : List Nat) (hn : l ≠ [])
    (hp : l.Pairwise (fun x y : Nat => x < y)) :
    ∀ x ∈ l, x ≤ l.getLast hn := by
  have hp' : l.Pairwise (fun x y : Nat => x ≤ y) :=
    hp.imp (by intro x y h; exact Nat.le_of_lt h)
  simpa using (mr_pairwise_le_last (fun z : Nat => z) l hn hp')

/-- Forgetting one cell of future scope only changes the bound-condition on
indices. -/
theorem mr_nsub_weaken_succ {a : Array Nat} {i : Nat} {s : List Nat}
    (h : MRNSub a i s) : MRNSub a (i+1) s := by
  rcases h with ⟨hb, hp, hv⟩
  exact ⟨(by intro q hq; have h' := hb q hq; omega), hp, hv⟩

/-- The semantic invariant of the patience table. `ans` is the number of
real tails; at every shorter length the table contains a witnessing smallest
last value among subsequences of the prefix. -/
def MRTails (a : Array Nat) (hne : a ≠ #[]) (i ans : Nat)
    (dp : Array Nat) : Prop :=
  dp.size = a.size ∧
  MRSorted dp ∧
  ans ≤ i ∧
  (∀ (j : Nat) (hj : j < dp.size), j < ans → dp[j] < a.max hne + 1) ∧
  (∀ (j : Nat) (hj : j < dp.size), ans ≤ j → dp[j] = a.max hne + 1) ∧
  (∀ (t : Nat), t < ans →
    ∃ (ht : t < dp.size) (s : List Nat) (hn : s ≠ []),
      MRNSub a i s ∧ s.length = t+1 ∧
        a.getD (s.getLast hn) 0 = dp[t]'ht) ∧
  (∀ (s : List Nat) (hn : s ≠ []), MRNSub a i s →
    ∃ (ht : s.length - 1 < dp.size),
       s.length - 1 < ans ∧
         dp[s.length-1]'ht ≤ a.getD (s.getLast hn) 0)

@[simp] theorem mr_getD_in {a : Array Nat} {i : Nat} (h : i < a.size) :
    a.getD i 0 = a[i] := by
  simp [Array.getD, h]

/-- Reading an unchanged cell of `set!`. -/
theorem mr_setBang_ne {a : Array Nat} {p v j : Nat} (hj : j < a.size)
    (hne : p ≠ j) :
    (a.set! p v)[j]'(by simpa using hj) = a[j] := by
  simpa [Array.set!, hne] using
    (Array.getElem_setIfInBounds (xs:=a) (i:=p) (a:=v) hj)

/-- Reading the cell just written by `set!` at an in range index. -/
theorem mr_setBang_eq {a : Array Nat} {p v : Nat} (hp : p < a.size) :
    (a.set! p v)[p]'(by simpa using hp) = v := by
  simpa [Array.set!] using
    (Array.getElem_setIfInBounds (xs:=a) (i:=p) (a:=v) hp)


/-- One update of the table preserves the full minimal-tail invariant. -/
theorem mr_tails_step (a : Array Nat) (hne : a ≠ #[]) (i ans : Nat)
    (dp : Array Nat) (hi : i < a.size)
    (ht : MRTails a hne i ans dp) :
    MRTails a hne (i+1) (max ans (minRearrange.upperBound a[i] dp + 1))
      (dp.set! (minRearrange.upperBound a[i] dp) a[i]) := by
  rcases ht with ⟨hsize, hs, hans, hreal, hsent, hwit, hminimal⟩
  let p : Nat := minRearrange.upperBound a[i] dp
  have hneedle : a[i] < a.max hne + 1 := by
    have h := mr_get_le_max a hne i hi
    omega
  have hpSpec := mr_upperBound_spec a[i] dp hs
  have hp_le : p ≤ ans := by
    by_contra hh
    have hap : ans < p := by omega
    have haold : ans < dp.size := by omega
    have hsmall := hpSpec.2.1 ans haold hap
    have he := hsent ans haold (by omega)
    rw [he] at hsmall
    omega
  have hp_lt : p < dp.size := by omega
  have hnewsize : (dp.set! p a[i]).size = a.size := by
    simpa using hsize
  have hnewsort : MRSorted (dp.set! p a[i]) := by
    simpa [p] using (mr_sorted_insert a[i] dp hs)
  change MRTails a hne (i+1) (max ans (p+1)) (dp.set! p a[i])
  refine ⟨hnewsize, hnewsort, (by omega), ?_, ?_, ?_, ?_⟩
  · intro j hj hjq
    have hjold : j < dp.size := by simpa using hj
    by_cases heq : p = j
    · subst j
      have he : (dp.set! p a[i])[p]'hj = a[i] := by
        simpa using (mr_setBang_eq (a:=dp) (p:=p) (v:=a[i]) hp_lt)
      rw [he]
      exact hneedle
    · have hjans : j < ans := by omega
      have he : (dp.set! p a[i])[j]'hj = dp[j] := by
        simpa using (mr_setBang_ne (a:=dp) (p:=p) (v:=a[i])
          (j:=j) hjold heq)
      rw [he]
      exact hreal j hjold hjans
  · intro j hj hjq
    have hjold : j < dp.size := by simpa using hj
    have hpne : p ≠ j := by omega
    have he : (dp.set! p a[i])[j]'hj = dp[j] := by
      simpa using (mr_setBang_ne (a:=dp) (p:=p) (v:=a[i])
        (j:=j) hjold hpne)
    rw [he]
    exact hsent j hjold (by omega)
  · intro t htq
    by_cases htp : t = p
    · subst t
      have htpnew : p < (dp.set! p a[i]).size := by simpa using hp_lt
      by_cases hp0 : p = 0
      · let u : List Nat := [i]
        have hun : u ≠ [] := by simp [u]
        refine ⟨htpnew, u, hun, ?_, ?_, ?_⟩
        · -- singleton subsequence ending in the current element
          constructor
          · intro z hz
            simp [u] at hz
            subst z
            omega
          constructor <;> simp [u]
        · simp [u, hp0]
        · have he : (dp.set! p a[i])[p]'htpnew = a[i] := by
            simpa using (mr_setBang_eq (a:=dp) (p:=p) (v:=a[i]) hp_lt)
          -- its last index is `i`
          simpa [u, mr_getD_in hi] using he.symm
      · have hpPos : 0 < p := by omega
        have hrans : p - 1 < ans := by omega
        rcases hwit (p-1) hrans with ⟨hrdp, s, sn, sh, slen, slast⟩
        have hslen : s.length = p := by omega
        have hsmall : dp[p-1]'hrdp ≤ a[i] := by
          exact hpSpec.2.1 (p-1) (by omega) (by omega)
        rcases sh with ⟨sbnd, sind, sval⟩
        have hall : ∀ z ∈ s, a.getD z 0 ≤ a.getD i 0 := by
          intro z hz
          have hh := mr_pairwise_le_last (fun q : Nat => a.getD q 0)
            s sn sval z hz
          have hlastbd : a.getD (s.getLast sn) 0 ≤ a[i] := by
            rw [slast]
            exact hsmall
          have hvz : a.getD z 0 ≤ a[i] := le_trans hh hlastbd
          simpa [mr_getD_in hi] using hvz
        let u : List Nat := s ++ [i]
        have hun : u ≠ [] := by simp [u]
        refine ⟨htpnew, u, hun, ?_, ?_, ?_⟩
        · constructor
          · intro z hz
            have hz' : z ∈ s ++ [i] := by simpa [u] using hz
            rcases (List.mem_append.mp hz') with hzs | hzlast
            · have := sbnd z hzs
              omega
            · have hz' : z = i := by simpa using hzlast
              subst z; omega
          constructor
          · apply List.pairwise_append.mpr
            refine ⟨sind, (by simp), ?_⟩
            intro z hz w hw
            have hw' : w = i := by simpa using hw
            subst w
            have := sbnd z hz
            omega
          · apply List.pairwise_append.mpr
            refine ⟨sval, (by simp), ?_⟩
            intro z hz w hw
            have hw' : w = i := by simpa using hw
            subst w
            exact hall z hz
        · simp [u, hslen]
        · have he : (dp.set! p a[i])[p]'htpnew = a[i] := by
            simpa using (mr_setBang_eq (a:=dp) (p:=p) (v:=a[i]) hp_lt)
          simpa [u, mr_getD_in hi] using he.symm
    · have htans : t < ans := by omega
      rcases hwit t htans with ⟨htold, s, sn, sh, slen, slast⟩
      have htnew : t < (dp.set! p a[i]).size := by simpa using htold
      refine ⟨htnew, s, sn, mr_nsub_weaken_succ sh, slen, ?_⟩
      have hnept : p ≠ t := by intro e; exact htp e.symm
      have he : (dp.set! p a[i])[t]'htnew = dp[t]'htold := by
        simpa using (mr_setBang_ne (a:=dp) (p:=p) (v:=a[i])
          (j:=t) htold hnept)
      rw [he]
      exact slast
  · intro s sn sh
    rcases sh with ⟨sbnd, sind, sval⟩
    have slmem : s.getLast sn ∈ s := List.getLast_mem sn
    have slbd : s.getLast sn < i+1 := sbnd _ slmem
    have slle : s.getLast sn ≤ i := by omega
    by_cases hlast : s.getLast sn = i
    · -- subsequences ending at the newly scanned cell
      let u : List Nat := s.dropLast
      have hul : u.length = s.length - 1 := by simp [u]
      have hindapp : (s.dropLast ++ [s.getLast sn]).Pairwise
          (fun x y : Nat => x < y) := by
        rw [List.dropLast_append_getLast sn]
        exact sind
      have hvalapp : (s.dropLast ++ [s.getLast sn]).Pairwise
          (fun x y : Nat => a.getD x 0 ≤ a.getD y 0) := by
        rw [List.dropLast_append_getLast sn]
        exact sval
      have hubnd : ∀ z ∈ u, z < i := by
        intro z hz
        have hz' : z ∈ s.dropLast := by simpa [u] using hz
        have hh := (List.pairwise_append.mp hindapp).2.2 z hz'
          (s.getLast sn) (by simp)
        simpa [hlast] using hh
      have huind : u.Pairwise (fun x y : Nat => x < y) := by
        simpa [u] using (List.pairwise_append.mp hindapp).1
      have huval : u.Pairwise (fun x y : Nat => a.getD x 0 ≤ a.getD y 0) := by
        simpa [u] using (List.pairwise_append.mp hvalapp).1
      have hsubu : MRNSub a i u := ⟨hubnd, huind, huval⟩
      have hlasti : a.getD (s.getLast sn) 0 = a[i] := by
        simp [hlast, mr_getD_in hi]
      by_cases hu : u = []
      · have hspos : 0 < s.length := List.length_pos_of_ne_nil sn
        have hu0 : u.length = 0 := by simp [hu]
        have hslen : s.length = 1 := by omega
        have hd0 : 0 < dp.size := by omega
        have hn0 : 0 < (dp.set! p a[i]).size := by simpa using hd0
        refine ⟨(by simpa [hslen] using hn0), (by omega), ?_⟩
        have hbound : (dp.set! p a[i])[0]'hn0 ≤ a[i] := by
          by_cases hpz : p = 0
          · have hpnew : p < (dp.set! p a[i]).size := by simpa using hp_lt
            have he : (dp.set! p a[i])[p]'hpnew = a[i] := by
              simpa using (mr_setBang_eq (a:=dp) (p:=p) (v:=a[i]) hp_lt)
            have he0 : (dp.set! p a[i])[0]'hn0 = a[i] := by
              simpa [hpz] using he
            rw [he0]
          · have hpzlt : 0 < p := by omega
            have hsm : dp[0]'hd0 ≤ a[i] := hpSpec.2.1 0 hd0 hpzlt
            have he : (dp.set! p a[i])[0]'hn0 = dp[0]'hd0 := by
              simpa using (mr_setBang_ne (a:=dp) (p:=p) (v:=a[i])
                (j:=0) hd0 hpz)
            rw [he]
            exact hsm
        simpa [hslen, hlasti] using hbound
      · rcases hminimal u hu hsubu with ⟨hrdp, hrans, hrval⟩
        have hcval : ∀ z ∈ u, a.getD z 0 ≤ a.getD (s.getLast sn) 0 := by
          intro z hz
          have hz' : z ∈ s.dropLast := by simpa [u] using hz
          exact (List.pairwise_append.mp hvalapp).2.2 z hz'
            (s.getLast sn) (by simp)
        have humem : u.getLast hu ∈ u := List.getLast_mem hu
        have hulastv : a.getD (u.getLast hu) 0 ≤ a[i] := by
          have := hcval (u.getLast hu) humem
          simpa [hlasti] using this
        have hprev : dp[u.length-1]'hrdp ≤ a[i] :=
          le_trans hrval hulastv
        have hrlt : u.length - 1 < p := by
          by_contra hh
          have hpge : p ≤ u.length - 1 := by omega
          have hbig := hpSpec.2.2 (u.length-1) hrdp hpge
          omega
        have hupos : 0 < u.length := List.length_pos_of_ne_nil hu
        have htle : s.length - 1 ≤ p := by omega
        have htold : s.length - 1 < dp.size := by omega
        have htnew : s.length - 1 < (dp.set! p a[i]).size := by
          simpa using htold
        refine ⟨htnew, (by omega), ?_⟩
        have hbound : (dp.set! p a[i])[s.length-1]'htnew ≤ a[i] := by
          by_cases heq : s.length - 1 = p
          · have hpnew : p < (dp.set! p a[i]).size := by simpa using hp_lt
            have he : (dp.set! p a[i])[p]'hpnew = a[i] := by
              simpa using (mr_setBang_eq (a:=dp) (p:=p) (v:=a[i]) hp_lt)
            have he' : (dp.set! p a[i])[s.length-1]'htnew = a[i] := by
              simpa [heq] using he
            rw [he']
          · have hlt : s.length - 1 < p := by omega
            have hsm : dp[s.length-1]'htold ≤ a[i] :=
              hpSpec.2.1 (s.length-1) htold hlt
            have hneidx : p ≠ s.length - 1 := by
              intro e; exact heq e.symm
            have he : (dp.set! p a[i])[s.length-1]'htnew =
                dp[s.length-1]'htold := by
              simpa using (mr_setBang_ne (a:=dp) (p:=p) (v:=a[i])
                (j:=s.length-1) htold hneidx)
            rw [he]
            exact hsm
        rw [hlasti]
        exact hbound
    · have hlastlt : s.getLast sn < i := by omega
      have sbold : ∀ z ∈ s, z < i := by
        intro z hz
        have hzle := mr_index_le_last s sn sind z hz
        omega
      have shold : MRNSub a i s := ⟨sbold, sind, sval⟩
      rcases hminimal s sn shold with ⟨htold, htans, htval⟩
      have htnew : s.length - 1 < (dp.set! p a[i]).size := by
        simpa using htold
      refine ⟨htnew, (by omega), ?_⟩
      by_cases hteq : s.length - 1 = p
      · -- if this length was improved, the improvement only lowered it
        have hleold : a[i] ≤ dp[s.length-1]'htold := by
          have hstrict := hpSpec.2.2 p hp_lt (by omega)
          exact Nat.le_of_lt (by simpa [hteq] using hstrict)
        have hppn : p < (dp.set! p a[i]).size := by simpa using hp_lt
        have he' : (dp.set! p a[i])[p]'hppn = a[i] := by
          simpa using (mr_setBang_eq (a:=dp) (p:=p) (v:=a[i]) hp_lt)
        have he : (dp.set! p a[i])[s.length-1]'htnew = a[i] := by
          simpa [hteq] using he' 
        rw [he]
        exact le_trans hleold htval
      · have hneidx : p ≠ s.length - 1 := by
          intro e; exact hteq e.symm
        have he : (dp.set! p a[i])[s.length-1]'htnew =
            dp[s.length-1]'htold := by
          simpa using (mr_setBang_ne (a:=dp) (p:=p) (v:=a[i])
            (j:=s.length-1) htold hneidx)
        rw [he]
        exact htval


/-- Before any input is scanned all tails are sentinels. -/
theorem mr_tails_init (a : Array Nat) (hne : a ≠ #[]) :
    MRTails a hne 0 0 (Array.replicate a.size (a.max hne + 1)) := by
  let d := Array.replicate a.size (a.max hne + 1)
  change MRTails a hne 0 0 d
  have hdsize : d.size = a.size := by simp [d]
  refine ⟨hdsize, ?_, (by omega), ?_, ?_, ?_, ?_⟩
  · intro x y hx hy hxy
    simp [d, Array.getElem_replicate]
  · intro j hj hh
    omega
  · intro j hj hh
    exact Array.getElem_replicate hj
  · intro t ht
    omega
  · intro s sn sh
    rcases sh with ⟨hb, hi, hv⟩
    have he := hb (s.getLast sn) (List.getLast_mem sn)
    omega

/-- Semantic reading of a longest weakly increasing subsequence. -/
def MRLongest (a : Array Nat) (L : Nat) : Prop :=
  (L = 0 ∨ ∃ (s : List Nat) (sn : s ≠ []),
      MRNSub a a.size s ∧ s.length = L) ∧
  (∀ (s : List Nat), MRNSub a a.size s → s.length ≤ L)

/-- Reading off the table at its final prefix returns witnesses for the longest
length and a bound for every other subsequence. -/
theorem mr_tails_longest (a : Array Nat) (hne : a ≠ #[]) (ans : Nat)
    (dp : Array Nat) (ht : MRTails a hne a.size ans dp) :
    MRLongest a ans := by
  rcases ht with ⟨hd, hs, ha, hr, hz, hw, hm⟩
  constructor
  · by_cases h0 : ans = 0
    · exact Or.inl h0
    · right
      have hp : ans - 1 < ans := by omega
      rcases hw (ans-1) hp with ⟨hidx, s, sn, sh, sl, sv⟩
      refine ⟨s, sn, sh, ?_⟩
      omega
  · intro s sh
    by_cases sn0 : s = []
    · simp [sn0]
    · rcases hm s sn0 sh with ⟨hidx, hh, hv⟩
      have hpos : 0 < s.length := List.length_pos_of_ne_nil sn0
      omega


/-- The recursive loop, when started from a semantically valid table, returns
an actual longest weakly increasing subsequence length of the whole input. -/
theorem mr_loop_longest (a : Array Nat) (hne : a ≠ #[])
    (ans i : Nat) (dp : Array Nat) (hi : i ≤ a.size)
    (ht : MRTails a hne i ans dp) :
    MRLongest a (minRearrange.loop a ans i dp hi) := by
  generalize hfuel : a.size - i = fuel
  induction fuel using Nat.strong_induction_on generalizing ans i dp with
  | h fuel ih =>
    rw [minRearrange.loop.eq_1]
    split <;> rename_i done
    · subst i
      exact mr_tails_longest a hne ans dp ht
    · dsimp
      have hii : i < a.size := by omega
      let p : Nat := minRearrange.upperBound a[i] dp
      have htnew : MRTails a hne (i+1) (max ans (p+1)) (dp.set! p a[i]) := by
        simpa [p] using (mr_tails_step a hne i ans dp hii ht)
      have hlt : a.size - (i+1) < fuel := by omega
      exact ih _ hlt (max ans (p+1)) (i+1) (dp.set! p a[i])
        (by omega) htnew (by omega)


/-- Thus the executable `lis` really is the maximum length of a
nondecreasing subsequence (not just a number bounded by the input size). -/
theorem mr_lis_longest (a : Array Nat) :
    MRLongest a (minRearrange.lis a) := by
  rw [minRearrange.lis.eq_1]
  split <;> rename_i h0
  · constructor
    · exact Or.inl rfl
    · intro s sh
      rcases sh with ⟨hb, hp, hv⟩
      have hasz : a.size = 0 := by
        have := congrArg Array.size h0
        simpa using this
      by_cases sn : s = []
      · simp [sn]
      · have hh := hb (s.getLast sn) (List.getLast_mem sn)
        omega
  · let d : Array Nat := Array.replicate a.size (a.max h0 + 1)
    have ht : MRTails a h0 0 0 d := by
      simpa [d] using (mr_tails_init a h0)
    exact mr_loop_longest a h0 0 0 d (by omega) ht

/-- Maximum, in the literal witnesses/all-witnesses form.  Empty witness
covers the zero case.  Thus no abstract supremum is hidden in the statement:
subsequences are just finite increasing lists of in-range indices. -/
theorem mr_lis_is_max (a : Array Nat) :
    (∃ (s : List Nat), MRNSub a a.size s ∧
        s.length = minRearrange.lis a) ∧
    (∀ (s : List Nat), MRNSub a a.size s →
        s.length ≤ minRearrange.lis a) := by
  have h := mr_lis_longest a
  rcases h with ⟨hw, hb⟩
  constructor
  · rcases hw with hz | hw
    · refine ⟨[], ?_, ?_⟩
      · simp [MRNSub]
      · simpa [hz]
    · rcases hw with ⟨s, sn, sh, sl⟩
      exact ⟨s, sh, sl⟩
  · exact hb


 theorem mr_range_zero : (1...=(0:Nat)).toArray = (#[] : Array Nat) := by
   have hl := (Std.Rcc.length_toList (r := (1...=(0:Nat))))
   have hz : (1...=(0:Nat)).size = 0 := by decide
   rw [hz] at hl
   have hs : ((1...=(0:Nat)).toArray).size = 0 := by
     rw [← Array.length_toList, Std.Rcc.toList_toArray]
     exact hl
   exact Array.eq_empty_of_size_eq_zero hs
 theorem mr_min_empty : minRearrange (#[] : Array Nat) = 0 := by
   rw [minRearrange.eq_1]
   simp

 theorem mr_min_le_size (a : Array Nat) : minRearrange a ≤ a.size := by
   rw [minRearrange.eq_1]
   exact Nat.sub_le _ _


/-- The two sorts of grid edges made by a fixed entry.  Horizonal edges
are left-of-the-peak choices, vertical edges are right-of-the-peak choices.
Their sum of coordinates is always twice the value minus one. -/
def MRLP (i a : Nat) : Nat × Nat := (2*i+1, 2*(a-i-1))
def MRRP (n i a : Nat) : Nat × Nat := (2*(a+i-n), 2*(n-i)-1)

def MRPoints (a : Array Nat) : Array (Nat × Nat) :=
  (a.zipIdx.filter (fun (x,i) => i+1 ≤ x)).map (fun (x,i) => MRLP i x) ++
  (a.zipIdx.filter (fun (x,i) => a.size ≤ x+i)).map
    (fun (x,i) => MRRP a.size i x)

def MRPointLe (u v : Nat × Nat) : Prop :=
  u = v ∨ Prod.Lex (fun a b : Nat => a < b) (fun a b : Nat => a < b) u v

instance mr_point_decidable : DecidableRel MRPointLe := by
  intro u v; unfold MRPointLe; infer_instance

/-- In coordinates the test used by mergeSort is ordinary lexicographic
non-strict order.  This normal form is much easier to use than the `Prod.Lex`
constructors, especially when two vertical edges have the same abscissa. -/
theorem mr_pointLe_iff (u v : Nat × Nat) :
    MRPointLe u v ↔ u.1 < v.1 ∨ (u.1 = v.1 ∧ u.2 ≤ v.2) := by
  rcases u with ⟨u,x⟩
  rcases v with ⟨v,y⟩
  constructor
  · intro h
    rcases h with h | h
    · cases h; exact Or.inr ⟨rfl, le_rfl⟩
    · cases h with
      | left _ _ hlt => exact Or.inl hlt
      | right _ hlt => exact Or.inr ⟨rfl, Nat.le_of_lt hlt⟩
  · intro h
    rcases h with h | ⟨e,h⟩
    · exact Or.inr (Prod.Lex.left _ _ h)
    · simp at e
      subst v
      by_cases q : x = y
      · subst y; exact Or.inl rfl
      · exact Or.inr (Prod.Lex.right _ (Nat.lt_of_le_of_ne h q))

instance mr_point_total : Std.Total MRPointLe :=
  ⟨by
    intro u v
    rcases u with ⟨u,x⟩
    rcases v with ⟨v,y⟩
    by_cases q : u < v
    · left; apply (mr_pointLe_iff _ _).2; exact Or.inl q
    · by_cases q' : v < u
      · right; apply (mr_pointLe_iff _ _).2; exact Or.inl q'
      · have e : u = v := by omega
        subst v
        by_cases t : x ≤ y
        · left; apply (mr_pointLe_iff _ _).2; exact Or.inr ⟨rfl,t⟩
        · right; apply (mr_pointLe_iff _ _).2
          exact Or.inr ⟨rfl, by omega⟩⟩
instance mr_point_trans : IsTrans (Nat × Nat) MRPointLe :=
  ⟨by
    intro u v w h h'
    have h := (mr_pointLe_iff _ _).1 h
    have h' := (mr_pointLe_iff _ _).1 h'
    apply (mr_pointLe_iff _ _).2
    rcases h with h | ⟨e,h⟩ <;> rcases h' with h' | ⟨e',h'⟩
    · exact Or.inl (lt_trans h h')
    · exact Or.inl (by simpa [e'] using h)
    · exact Or.inl (by simpa [e] using h')
    · exact Or.inr ⟨e.trans e', le_trans h h'⟩⟩
instance mr_point_antisymm : Std.Antisymm MRPointLe :=
  ⟨by
    intro u v h h'
    have h := (mr_pointLe_iff _ _).1 h
    have h' := (mr_pointLe_iff _ _).1 h'
    rcases u with ⟨u,x⟩
    rcases v with ⟨v,y⟩
    simp at h h'
    have e : u = v := by omega
    subst v
    simp_all
    have ee : x = y := by omega
    subst y
    rfl⟩

def MRPointSort (a : Array Nat) : Array (Nat × Nat) :=
  ((MRPoints a).toList.mergeSort
      (le := fun u v => decide (MRPointLe u v))).toArray

def MRPointY (a : Array Nat) : Array Nat := (MRPointSort a).map (fun z => z.2)

/-- These abbreviations really spell the vector produced in `minRearrange`.
Keeping them reducible lets later lemmas talk about the executable code without
repeating the rather long zip/filter expression. -/
theorem mr_points_eq (a : Array Nat) :
    MRPoints a =
     (a.zipIdx.filter (fun (x,i) => i + 1 ≤ x)).map
        (fun (x,i) => (2*i+1,2*(x-i-1))) ++
     (a.zipIdx.filter (fun (x,i) => a.size ≤ x+i)).map
        (fun (x,i) => (2*(x+i-a.size),2*(a.size-i)-1)) := by
  rfl

/-- Exact membership statement for the unsorted points.  In particular the
index attached by `zipIdx` is the real (zero-based) index of the element, not
an arbitrary enumeration. -/
theorem mr_mem_points (a : Array Nat) (z : Nat × Nat) :
    z ∈ MRPoints a ↔
      (∃ i : Nat, ∃ hi : i < a.size, i+1 ≤ a[i] ∧ z = MRLP i a[i]) ∨
      (∃ i : Nat, ∃ hi : i < a.size, a.size ≤ a[i]+i ∧
          z = MRRP a.size i a[i]) := by
  constructor
  · intro hz
    have hz' : z ∈
        (a.zipIdx.filter (fun (x,i) => i+1 ≤ x)).map
            (fun (x,i) => MRLP i x) ∨
        z ∈ (a.zipIdx.filter (fun (x,i) => a.size ≤ x+i)).map
            (fun (x,i) => MRRP a.size i x) := by
      exact (Array.mem_append.mp hz)
    rcases hz' with h | h
    · have hm := (Array.mem_map.1 h)
      rcases hm with ⟨q,hq,eq⟩
      rcases q with ⟨x,i⟩
      have hf := (Array.mem_filter.1 hq)
      rcases hf with ⟨hin, htest⟩
      have hzip := Array.mem_zipIdx hin
      rcases hzip with ⟨_,hb, hx⟩
      have hi : i < a.size := by simpa using hb
      have hx' : x = a[i] := by simpa using hx
      have hcap : i+1 ≤ a[i] := by
        -- the Boolean filter has coerced this inequality with `decide`
        have : i+1 ≤ x := by exact of_decide_eq_true htest
        simpa [hx'] using this
      left
      refine ⟨i, hi, hcap, ?_⟩
      simpa [hx'] using eq.symm
    · have hm := (Array.mem_map.1 h)
      rcases hm with ⟨q,hq,eq⟩
      rcases q with ⟨x,i⟩
      have hf := (Array.mem_filter.1 hq)
      rcases hf with ⟨hin, htest⟩
      have hzip := Array.mem_zipIdx hin
      rcases hzip with ⟨_,hb,hx⟩
      have hi : i < a.size := by simpa using hb
      have hx' : x = a[i] := by simpa using hx
      have hcap : a.size ≤ a[i]+i := by
        have : a.size ≤ x+i := by exact of_decide_eq_true htest
        simpa [hx'] using this
      right
      refine ⟨i, hi, hcap, ?_⟩
      simpa [hx'] using eq.symm
  · intro h
    rcases h with h | h
    · rcases h with ⟨i,hi,hcap,rfl⟩
      apply Array.mem_append_left
      apply (Array.mem_map).2
      refine ⟨(a[i],i), ?_, rfl⟩
      apply (Array.mem_filter).2
      constructor
      · have hz : i < (a.zipIdx).size := by simpa using hi
        have hm : (a.zipIdx)[i] ∈ a.zipIdx := by
          have hm' : (a.zipIdx)[i] ∈ (a.zipIdx).toList := by
            simpa using (List.getElem_mem (l:=(a.zipIdx).toList)
              (n:=i) (by simpa using hz))
          exact (Array.mem_def).2 hm'
        simpa [Array.getElem_zipIdx] using hm
      · exact decide_eq_true hcap
    · rcases h with ⟨i,hi,hcap,rfl⟩
      apply Array.mem_append_right
      apply (Array.mem_map).2
      refine ⟨(a[i],i), ?_, rfl⟩
      apply (Array.mem_filter).2
      constructor
      · have hz : i < (a.zipIdx).size := by simpa using hi
        have hm : (a.zipIdx)[i] ∈ a.zipIdx := by
          have : (a.zipIdx)[i] ∈ (a.zipIdx).toList := by
            simpa using (List.getElem_mem (l:=(a.zipIdx).toList)
              (n:=i) (by simpa using hz))
          exact (Array.mem_def).2 this
        simpa [Array.getElem_zipIdx] using hm
      · exact decide_eq_true hcap

/-- Eliminating the local lets in the program. -/
theorem mr_min_points (a : Array Nat) :
    minRearrange a = a.size - minRearrange.lis (MRPointY a) := by
  rw [minRearrange.eq_1]
  rfl

/-- The order of the merge-sort table. -/
theorem mr_pointSort_pairwise (a : Array Nat) :
    (MRPointSort a).toList.Pairwise MRPointLe := by
  change ((MRPoints a).toList.mergeSort
      (le := fun u v => decide (MRPointLe u v))).Pairwise MRPointLe
  exact List.pairwise_mergeSort' MRPointLe _

theorem mr_mem_pointSort (a : Array Nat) (z : Nat × Nat) :
    z ∈ MRPointSort a ↔ z ∈ MRPoints a := by
  change z ∈ ((MRPoints a).toList.mergeSort
      (le := fun u v => decide (MRPointLe u v))).toArray ↔ _
  rw [Array.mem_def, List.mem_mergeSort]
  exact (Array.mem_def.symm)

/-- No two indices of a permutation contain the same value.  A short, useful
form of the no-duplicates part of the input promise. -/
theorem mr_perm_injective {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray)
    {i j : Nat} (hi : i < a.size) (hj : j < a.size)
    (he : a[i] = a[j]) : i = j := by
  have hrnode : (1...=a.size).toList.Nodup := by
    -- `Rcc` has the usual no-duplicates enumeration
    exact (Std.Rcc.nodup_toList (a := (1:Nat)) (b := a.size))
  have hnod : a.toList.Nodup := by
    have ht : a.toList.Perm ((1...=a.size).toArray).toList := hp.toList
    -- duplicates are invariant under a permutation
    exact (List.Perm.nodup_iff ht).2 (by
      simpa [Std.Rcc.toList_toArray] using hrnode)
  have he' : a.toList[i] = a.toList[j] := by
    simpa [Array.getElem_toList] using he
  exact (hnod.getElem_inj_iff).1 he' 

/-- Midpoints are on the diagonal numbered by their value.  The hypotheses
are exactly those used by the filters and discharge Nat subtraction. -/
theorem mr_LP_diag {i x : Nat} (h : i+1 ≤ x) :
    (MRLP i x).1 + (MRLP i x).2 = 2*x-1 := by
  dsimp [MRLP]
  omega

theorem mr_RP_diag {n i x : Nat} (hi : i < n) (hx : n ≤ x+i)
    (xpos : 1 ≤ x) :
    (MRRP n i x).1 + (MRRP n i x).2 = 2*x-1 := by
  dsimp [MRRP]
  omega

/-- Distinct values occupy distinct diagonals.  Opposite orientations also
have different parity in the first coordinate.  Hence the point array of a
permutation is a *set*: the later increasing subsequence can never pick the
same edge twice. -/
theorem mr_points_eq_sources {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray)
    {i j : Nat} (hi : i < a.size) (hj : j < a.size) :
    (i+1 ≤ a[i] → j+1 ≤ a[j] → MRLP i a[i] = MRLP j a[j] → i = j) ∧
    (a.size ≤ a[i]+i → a.size ≤ a[j]+j →
        MRRP a.size i a[i] = MRRP a.size j a[j] → i = j) ∧
    (i+1 ≤ a[i] → a.size ≤ a[j]+j → MRLP i a[i] ≠ MRRP a.size j a[j]) := by
  have ai := (mr_perm_entry_bounds hp i hi)
  have aj := (mr_perm_entry_bounds hp j hj)
  constructor
  · intro _ _ he
    have hx : 2*i+1 = 2*j+1 := congrArg Prod.fst he
    omega
  constructor
  · intro ei ej he
    have hs : 2*a[i]-1 = 2*a[j]-1 := by
      calc
        2*a[i]-1 = (MRRP a.size i a[i]).1 +
            (MRRP a.size i a[i]).2 := (mr_RP_diag hi ei ai.1).symm
        _ = (MRRP a.size j a[j]).1 +
            (MRRP a.size j a[j]).2 := by rw [he]
        _ = 2*a[j]-1 := (mr_RP_diag hj ej aj.1)
    have hv : a[i] = a[j] := by omega
    exact mr_perm_injective hp hi hj hv
  · intro _ _ he
    have hx : 2*i+1 = 2*(a[j]+j-a.size) := congrArg Prod.fst he
    -- an odd natural cannot equal an even one
    omega

/-- Enumeration by zipIdx has no repetitions already before the filters. -/
theorem mr_zipIdx_nodup {α : Type} (v : Array α) : v.zipIdx.toList.Nodup := by
  have h := List.nodup_zipIdx_map_snd v.toList
  -- converting via the pairwise characterization avoids any instances on α
  rw [List.nodup_iff_pairwise_ne, List.pairwise_map] at h
  rw [Array.toList_zipIdx]
  rw [List.nodup_iff_pairwise_ne]
  exact h.imp (by
    intro u w hn e
    apply hn
    simpa [e])

/-- No duplicate points for a permutation.  Along the left side odd first
coordinates recover the index; along the right side the diagonal recovers the
value and then the permutation recovers the index.  Between the two lists
parity separates the first coordinates. -/
theorem mr_points_nodup {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) : (MRPoints a).toList.Nodup := by
  let L := a.zipIdx.filter (fun (x,i) => i+1 ≤ x)
  let R := a.zipIdx.filter (fun (x,i) => a.size ≤ x+i)
  have hz : a.zipIdx.toList.Nodup := mr_zipIdx_nodup a
  have lnod0 : L.toList.Nodup := by
    dsimp [L]
    rw [Array.toList_filter]
    exact hz.filter _
  have rnod0 : R.toList.Nodup := by
    dsimp [R]
    rw [Array.toList_filter]
    exact hz.filter _
  have lnod : (L.map (fun (x,i) => MRLP i x)).toList.Nodup := by
    rw [Array.toList_map]
    apply lnod0.map_on
    intro u hu w hw eq
    rcases u with ⟨x,i⟩
    rcases w with ⟨y,j⟩
    have hi0 : (x,i) ∈ a.zipIdx :=
      (Array.mem_filter.1 ((Array.mem_def).2 hu)).1
    have hj0 : (y,j) ∈ a.zipIdx :=
      (Array.mem_filter.1 ((Array.mem_def).2 hw)).1
    rcases Array.mem_zipIdx hi0 with ⟨_,hi,hx⟩
    rcases Array.mem_zipIdx hj0 with ⟨_,hj,hy⟩
    have hi' : i < a.size := by simpa using hi
    have hj' : j < a.size := by simpa using hj
    have hx' : x = a[i] := by simpa using hx
    have hy' : y = a[j] := by simpa using hy
    have ei : i+1 ≤ a[i] := by
      have hf := (Array.mem_filter.1 ((Array.mem_def).2 hu)).2
      have : i+1 ≤ x := of_decide_eq_true hf
      simpa [hx'] using this
    have ej : j+1 ≤ a[j] := by
      have hf := (Array.mem_filter.1 ((Array.mem_def).2 hw)).2
      have : j+1 ≤ y := of_decide_eq_true hf
      simpa [hy'] using this
    have idx : i = j :=
      (mr_points_eq_sources hp hi' hj').1 ei ej (by simpa [hx',hy'] using eq)
    subst j
    simp_all
  have rnod : (R.map (fun (x,i) => MRRP a.size i x)).toList.Nodup := by
    rw [Array.toList_map]
    apply rnod0.map_on
    intro u hu w hw eq
    rcases u with ⟨x,i⟩
    rcases w with ⟨y,j⟩
    have hi0 : (x,i) ∈ a.zipIdx :=
      (Array.mem_filter.1 ((Array.mem_def).2 hu)).1
    have hj0 : (y,j) ∈ a.zipIdx :=
      (Array.mem_filter.1 ((Array.mem_def).2 hw)).1
    rcases Array.mem_zipIdx hi0 with ⟨_,hi,hx⟩
    rcases Array.mem_zipIdx hj0 with ⟨_,hj,hy⟩
    have hi' : i < a.size := by simpa using hi
    have hj' : j < a.size := by simpa using hj
    have hx' : x = a[i] := by simpa using hx
    have hy' : y = a[j] := by simpa using hy
    have ei : a.size ≤ a[i]+i := by
      have hf := (Array.mem_filter.1 ((Array.mem_def).2 hu)).2
      have : a.size ≤ x+i := of_decide_eq_true hf
      simpa [hx'] using this
    have ej : a.size ≤ a[j]+j := by
      have hf := (Array.mem_filter.1 ((Array.mem_def).2 hw)).2
      have : a.size ≤ y+j := of_decide_eq_true hf
      simpa [hy'] using this
    have idx : i = j :=
      (mr_points_eq_sources hp hi' hj').2.1 ei ej (by simpa [hx',hy'] using eq)
    subst j
    simp_all
  change ( (L.map (fun (x,i) => MRLP i x) ++
      R.map (fun (x,i) => MRRP a.size i x)).toList).Nodup
  rw [Array.toList_append, List.nodup_append]
  refine ⟨lnod, rnod, ?_⟩
  intro z hzL w hzR eq
  rcases (Array.mem_map.1 ((Array.mem_def).2 hzL)) with
    ⟨u,hu,huv⟩
  rcases (Array.mem_map.1 ((Array.mem_def).2 hzR)) with
    ⟨t,ht,htv⟩
  rcases u with ⟨x,i⟩
  rcases t with ⟨y,j⟩
  have hi0 : (x,i) ∈ a.zipIdx :=
    (Array.mem_filter.1 hu).1
  have hj0 : (y,j) ∈ a.zipIdx :=
    (Array.mem_filter.1 ht).1
  rcases Array.mem_zipIdx hi0 with ⟨_,hi,hx⟩
  rcases Array.mem_zipIdx hj0 with ⟨_,hj,hy⟩
  have hi' : i < a.size := by simpa using hi
  have hj' : j < a.size := by simpa using hj
  have hx' : x = a[i] := by simpa using hx
  have hy' : y = a[j] := by simpa using hy
  have ei : i+1 ≤ a[i] := by
    have h := (Array.mem_filter.1 hu).2
    have : i+1 ≤ x := of_decide_eq_true h
    simpa [hx'] using this
  have ej : a.size ≤ a[j]+j := by
    have h := (Array.mem_filter.1 ht).2
    have : a.size ≤ y+j := of_decide_eq_true h
    simpa [hy'] using this
  have bad := (mr_points_eq_sources hp hi' hj').2.2 ei ej
  apply bad
  calc
    MRLP i a[i] = z := by simpa [hx'] using huv
    _ = w := eq
    _ = MRRP a.size j a[j] := by simpa [hy'] using htv.symm

theorem mr_pointSort_nodup {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) :
    (MRPointSort a).toList.Nodup := by
  change ((MRPoints a).toList.mergeSort
      (le := fun u v => decide (MRPointLe u v))).Nodup
  exact ((List.mergeSort_perm _ _).nodup_iff).2 (mr_points_nodup hp)

/-- A sublist can be addressed by an increasing list of concrete indices in
its superlist.  We use `getD` so the statement composes with `Array.getD` in
`MRNSub` without Fin casts. -/
theorem mr_sublist_indices {α : Type} [Inhabited α]
    {u v : List α} (h : u.Sublist v) :
    ∃ t : List Nat,
      t.length = u.length ∧
      (∀ k ∈ t, k < v.length) ∧
      t.Pairwise (fun k q : Nat => k < q) ∧
      (t.map (fun k => v.getD k default) = u) := by
  induction h with
  | slnil =>
      refine ⟨[], rfl, ?_, (by simp), (by simp)⟩
      intro k hk; simpa using hk
  | @cons a u v h ih =>
      rcases ih with ⟨t,tl,tb,tinc,tval⟩
      refine ⟨t.map Nat.succ, (by simp [tl]), ?_, ?_, ?_⟩
      · intro k hk
        rcases List.mem_map.1 hk with ⟨q,hq,rfl⟩
        have hlt := tb q hq
        simp
        omega
      · exact tinc.map _ (by intro i j hh; omega)
      · -- all addresses shifted by one
        simpa [Function.comp_def, List.map_map, List.getD] using tval
  | @cons_cons a u v h ih =>
      rcases ih with ⟨t,tl,tb,tinc,tval⟩
      refine ⟨0 :: t.map Nat.succ, (by simp [tl]), ?_, ?_, ?_⟩
      · intro k hk
        rcases (List.mem_cons.1 hk) with rfl | hk
        · simp
        · rcases List.mem_map.1 hk with ⟨q,hq,rfl⟩
          have hlt := tb q hq
          simp
          omega
      · apply List.pairwise_cons.2
        constructor
        · intro q hq
          rcases List.mem_map.1 hq with ⟨j,hj,rfl⟩
          omega
        · exact tinc.map _ (by intro i j hh; omega)
      · simpa [Function.comp_def, List.map_map, List.getD] using
          congrArg (fun z => v :: z) tval

@[simp] theorem mr_pointY_size (a : Array Nat) :
    (MRPointY a).size = (MRPointSort a).size := by simp [MRPointY]

/-- A coordinate read in bounds is unaffected by the intermediate array map. -/
theorem mr_pointY_at (a : Array Nat) (i : Nat)
    (h : i < (MRPointSort a).toList.length) :
    (MRPointY a).getD i 0 =
       ((MRPointSort a).toList.getD i (default : Nat × Nat)).2 := by
  have ha : i < (MRPointSort a).size := by simpa using h
  have hy : i < (MRPointY a).size := by simpa using ha
  rw [mr_getD_in hy]
  change ((MRPointSort a).map (fun z => z.2))[i] = _
  rw [Array.getElem_map]
  -- on either container `getD` is an in bounds read
  simp [List.getD, ha, Array.getElem_toList]

def MRChain (a : Array Nat) (c : List (Nat × Nat)) : Prop :=
  (∀ z ∈ c, z ∈ MRPoints a) ∧
  c.Pairwise MRPointLe ∧
  c.Pairwise (fun u v : Nat × Nat => u.2 ≤ v.2) ∧
  c.Nodup

/-- A product-chain can be selected as a weak subsequence of the sorted table.
This is the small but slightly fiddly connection between the patience routine,
which talks only about *indices* of an array, and the usual geometric picture.
No choices about values have happened yet. -/
theorem mr_chain_to_nsub {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) {c : List (Nat × Nat)}
    (hc : MRChain a c) :
    ∃ t : List Nat, MRNSub (MRPointY a) (MRPointY a).size t ∧
        t.length = c.length := by
  rcases hc with ⟨hmem, hlex, hinc, hnd⟩
  let v : List (Nat × Nat) := (MRPointSort a).toList
  have hvsort : v.Pairwise MRPointLe := by
    dsimp [v]
    exact mr_pointSort_pairwise a
  have hvnd : v.Nodup := by
    dsimp [v]
    exact mr_pointSort_nodup hp
  have hsubperm : c.Subperm v :=
    List.subperm_of_subset hnd (by
      intro z hz
      have hz' := hmem z hz
      have : z ∈ MRPointSort a := (mr_mem_pointSort a z).2 hz'
      exact (Array.mem_def.1 this))
  have hsub : c.Sublist v :=
    List.sublist_of_subperm_of_pairwise hsubperm hlex hvsort
  rcases mr_sublist_indices hsub with ⟨t, tl,tb,tord,tval⟩
  refine ⟨t, ?_, tl⟩
  constructor
  · intro k hk
    have := tb k hk
    simpa [v, MRPointY] using this
  constructor
  · exact tord
  · -- compare last coordinates using equality with the sublist
    have eqc : (t.map (fun k => (v.getD k (default : Nat × Nat)).2)) =
          c.map (fun z : Nat × Nat => z.2) := by
      calc
        t.map (fun k => (v.getD k (default : Nat × Nat)).2) =
            (t.map (fun k => v.getD k (default : Nat × Nat))).map
               (fun z : Nat × Nat => z.2) := by
                 simp [List.map_map, Function.comp_def]
        _ = _ := by
          have e := congrArg (fun w : List (Nat × Nat) =>
             w.map (fun z : Nat × Nat => z.2)) tval
          simpa using e
    have hcmap : (c.map (fun z : Nat × Nat => z.2)).Pairwise
        (fun x y : Nat => x ≤ y) :=
      hinc.map _ (by intro x y h; exact h)
    have hc' : (t.map (fun k => (v.getD k (default : Nat × Nat)).2)).Pairwise
        (fun x y : Nat => x ≤ y) := by rw [eqc]; exact hcmap
    -- expose it back as getD in the array of ordinates
    apply (List.pairwise_map).1 at hc'
    exact hc'.imp_of_mem (by
      intro i j hi hj hle
      have ib := tb i hi; have jb := tb j hj
      simpa [v, mr_pointY_at a i (by simpa [v] using ib),
             mr_pointY_at a j (by simpa [v] using jb)] using hle)

/-- Conversely a subsequence of ordinates really is a chain of actual
edges.  `Nodup` here is where the permutation promise is needed; for an array
with duplicate values the same edge could occur twice in the merge sort. -/
theorem mr_nsub_to_chain {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) {t : List Nat}
    (ht : MRNSub (MRPointY a) (MRPointY a).size t) :
    ∃ c : List (Nat × Nat), MRChain a c ∧ c.length = t.length := by
  rcases ht with ⟨tbd, tinc, tval⟩
  let v : List (Nat × Nat) := (MRPointSort a).toList
  have tbd' : ∀ k ∈ t, k < v.length := by
    intro k hk
    have hh := tbd k hk
    simpa [v, MRPointY] using hh
  let c := t.map (fun k => v.getD k (default : Nat × Nat))
  have vnd : v.Nodup := by
    dsimp [v]
    exact mr_pointSort_nodup hp
  have vsort : v.Pairwise MRPointLe := by
    dsimp [v]
    exact mr_pointSort_pairwise a
  have cmem : ∀ z ∈ c, z ∈ MRPoints a := by
    intro z hz
    rcases List.mem_map.1 hz with ⟨k,hk,rfl⟩
    have kb := tbd' k hk
    have hmem : v.getD k (default : Nat × Nat) ∈ v := by
      have := List.getElem_mem (l:=v) (n:=k) kb
      simpa [List.getD, kb] using this
    have : v.getD k (default : Nat × Nat) ∈ MRPointSort a :=
      (Array.mem_def).2 (by simpa [v] using hmem)
    exact (mr_mem_pointSort a _).1 this
  have cnd : c.Nodup := by
    have tnd : t.Nodup :=
      (List.nodup_iff_pairwise_ne).2
        (tinc.imp (by intro x y h e; omega))
    dsimp [c]
    apply tnd.map_on
    intro i hi j hj he
    have ib : i < v.length := tbd' i hi
    have jb : j < v.length := tbd' j hj
    have he' : v[i] = v[j] := by
      simpa [List.getD, ib, jb] using he
    exact (vnd.getElem_inj_iff).1 he'
  have clex : c.Pairwise MRPointLe := by
    dsimp [c]
    apply (List.pairwise_map).2
    -- the merge sort is pairwise ordered, so any two increasing indices are
    -- in lexicographic order
    refine tinc.imp_of_mem ?_
    intro i j hi hj hij
    have ib : i < v.length := tbd' i hi
    have jb : j < v.length := tbd' j hj
    have hv := (List.pairwise_iff_getElem.1 vsort)
       i j ib jb hij
    simpa [List.getD, ib, jb] using hv
  have cy : c.Pairwise (fun u w : Nat × Nat => u.2 ≤ w.2) := by
    dsimp [c]
    apply (List.pairwise_map).2
    refine tval.imp_of_mem ?_
    intro i j hi hj hle
    have ib := tbd' i hi; have jb := tbd' j hj
    have heyI := mr_pointY_at a i (by simpa [v] using ib)
    have heyJ := mr_pointY_at a j (by simpa [v] using jb)
    -- `tval` is stated with array getD
    simpa [heyI, heyJ, v] using hle
  refine ⟨c, ⟨cmem, clex, cy, cnd⟩, ?_⟩
  simp [c]

/-- The LIS computed by the program is now literally the largest possible
number of compatible edges.  This isolates all facts about sorting stability,
indices and the executable `lis`; the rest of the correctness proof may work
entirely with finite chains in the grid. -/
theorem mr_lis_chains {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) :
    (∃ c : List (Nat × Nat), MRChain a c ∧
        c.length = minRearrange.lis (MRPointY a)) ∧
    (∀ c : List (Nat × Nat), MRChain a c →
        c.length ≤ minRearrange.lis (MRPointY a)) := by
  rcases mr_lis_is_max (MRPointY a) with ⟨hmax, hall⟩
  constructor
  · rcases hmax with ⟨t, ht, tl⟩
    rcases mr_nsub_to_chain hp ht with ⟨c,hc,cl⟩
    refine ⟨c,hc, ?_⟩
    omega
  · intro c hc
    rcases mr_chain_to_nsub hp hc with ⟨t,ht,tl⟩
    have hb := hall t ht
    omega

/-- Number of positions one hopes to leave untouched.  Unlike a rearrangement
itself this lives on the original index type, so no casts enter its filter. -/
def MRKeep (a x : Array Nat) : Nat :=
  (List.finRange a.size |>.filter
       (fun i => decide (a[i] = x.getD i.val 0))).length

theorem mr_keep_diff {a x : Array Nat} (hxs : x.size = a.size) :
    differences (Vector.mk x hxs) a.toVector = a.size - MRKeep a x := by
  have h := mr_differences_compl (Vector.mk x hxs) a.toVector
  rw [h]
  unfold MRKeep
  congr 1
  -- The two equalities have their arguments reversed.  All accesses to x
  -- are in bounds by the common length.
  apply congrArg List.length
    (List.filter_congr (l := List.finRange a.size) (by
      intro i hi
      have ix : i.val < x.size := by simpa [hxs] using i.isLt
      have ge : x.getD i.val 0 = x[i.val] := mr_getD_in ix
      change (decide ((Vector.mk x hxs)[i] = a.toVector[i])) =
          (decide (a[i] = x.getD i.val 0))
      simp [Vector.getElem_mk, Array.toVector, ge, eq_comm]))

/-- Completing any Boolean choice of left values yields a unimodal
permutation.  This is the explicit construction used on the completion side
of the grid lemma; no search over arrays is involved. -/
theorem mr_split_values (n : Nat) (p : Nat → Bool) :
    let vals := (1...=n).toList
    let l := vals.filter p
    let r := vals.filter (fun x => !p x)
    let out := (l ++ r.reverse).toArray
    out.Perm (1...=n).toArray ∧ Unimodal out := by
  dsimp
  let vals : List Nat := (1...=n).toList
  let l : List Nat := vals.filter p
  let r : List Nat := vals.filter (fun x => !p x)
  have hv : vals.Pairwise (fun x y : Nat => x < y) := by
    dsimp [vals]
    exact Std.Rcc.pairwise_toList_lt
  have hl : l.Pairwise (fun x y : Nat => x < y) := by
    exact hv.filter _
  have hr : r.Pairwise (fun x y : Nat => x < y) := by
    exact hv.filter _
  have hrr : r.reverse.Pairwise (fun x y : Nat => x > y) := by
    rw [List.pairwise_reverse]
    simpa using hr
  have hperm : (l ++ r.reverse).Perm vals := by
    have hboth := List.filter_append_perm p vals
    have hrev : r.reverse.Perm r := List.reverse_perm _
    exact (List.Perm.append_left l hrev).trans hboth
  constructor
  · exact (Array.perm_iff_toList_perm.2 (by
        simpa [Std.Rcc.toList_toArray] using hperm))
  · refine ⟨l.toArray, r.reverse.toArray, ?_, ?_, ?_⟩
    · change (l ++ r.reverse).toArray = l.toArray ++ r.reverse.toArray
      rw [Array.toArray_append]
    · simpa using hl
    · simpa using hrr


/-- Counts of left steps in a finite word; a word is indexed by the values
    `1,2,...`.  Keeping the elementary bookkeeping in lists avoids Fin casts. -/
def MRTrue (b : List Bool) : Nat := (b.filter id).length
def MRBefore (b : List Bool) (k : Nat) : Nat := MRTrue (b.take k)

@[simp] theorem mr_true_append (u v : List Bool) :
    MRTrue (u ++ v) = MRTrue u + MRTrue v := by
  simp [MRTrue, List.filter_append]
@[simp] theorem mr_true_nil : MRTrue [] = 0 := by simp [MRTrue]
@[simp] theorem mr_true_one (e : Bool) :
    MRTrue [e] = if e then 1 else 0 := by cases e <;> decide
@[simp] theorem mr_true_replicate_true (k : Nat) :
    MRTrue (List.replicate k true) = k := by simp [MRTrue]
@[simp] theorem mr_true_replicate_false (k : Nat) :
    MRTrue (List.replicate k false) = 0 := by simp [MRTrue]

/-- Looking at the `k` previous cells of the range through a word really is
just counting the true cells of the prefix. -/
theorem mr_filter_prefix_word (n : Nat) (b : List Bool) (hb : b.length = n)
    (k : Nat) (hk : k ≤ n) :
    let p : Nat → Bool := fun v => b.getD (v-1) false
    (((1...=n).toList.take k).filter p).length = MRBefore b k := by
  dsimp
  unfold MRBefore
  induction k with
  | zero => simp [MRTrue]
  | succ k ih =>
    have kn : k < n := by omega
    have hvlen : (1...=n).toList.length = n := by
      simpa using (Nat.length_toList_rcc (a:=1) (b:=n))
    have kv : k < (1...=n).toList.length := by simpa [hvlen] using kn
    have kb : k < b.length := by simpa [hb] using kn
    rw [List.take_succ_eq_append_getElem kv,
        List.take_succ_eq_append_getElem kb,
        List.filter_append]
    have vget : (1...=n).toList[k]'kv = k+1 := by
      calc
        _ = 1 + k := Nat.getElem_toList_rcc (m:=1) (n:=n) (i:=k) kv
        _ = k+1 := by omega
    have pget : b.getD ((k+1)-1) false = b[k]'kb := by
      have hh := List.getD_eq_getElem b false kb
      have ee : (k+1)-1 = k := by omega
      simpa [ee] using hh
    simp only [List.length_append]
    rw [ih (by omega)]
    rw [vget]
    -- only the singleton boolean remains
    change MRTrue (b.take k) +
        (([k+1].filter (fun v => b.getD (v-1) false)).length) =
          MRTrue (b.take k ++ [b[k]])
    rw [mr_true_append]
    cases e : b[k]'kb
    · have pv : b.getD ((k+1)-1) false = false := pget.trans e
      -- expose the Boolean test of the singleton
      simp only [List.filter_cons, pv, List.filter_nil, List.length_nil,
        List.length_cons]
      simp [MRTrue, e]
    · have pv : b.getD ((k+1)-1) false = true := pget.trans e
      simp only [List.filter_cons, pv, List.filter_nil, List.length_nil,
        List.length_cons]
      simp [MRTrue, e]

/-- Split the sorted range immediately before value `k+1`. -/
theorem mr_vals_split (n k : Nat) (hk : k < n) :
    (1...=n).toList =
      (1...=n).toList.take k ++ (k+1) :: (1...=n).toList.drop (k+1) := by
  have hv : k < (1...=n).toList.length := by
    simpa [Nat.length_toList_rcc] using hk
  have hh := List.take_append_drop k (1...=n).toList
  rw [List.drop_eq_getElem_cons hv] at hh
  have he : (1...=n).toList[k]'hv = k+1 := by
    calc
      _ = 1+k := Nat.getElem_toList_rcc (m:=1) (n:=n) (i:=k) hv
      _ = k+1 := by omega
  simpa [he] using hh.symm

/-- Where a value is found in the split increasing/decreasing list.  The
formula only mentions the number of true cells before it. -/
theorem mr_split_get (n : Nat) (b : List Bool) (hb : b.length = n)
    (k : Nat) (hk : k < n) :
    let p : Nat → Bool := fun v => b.getD (v-1) false
    let l := (1...=n).toList.filter p
    let r := (1...=n).toList.filter (fun v => ! p v)
    let out := l ++ r.reverse
    (p (k+1) = true →
       ∃ hpos : MRBefore b k < out.length, out[MRBefore b k]'hpos = k+1) ∧
    (p (k+1) = false →
       ∃ hpos : n-1-(k-MRBefore b k) < out.length,
         out[n-1-(k-MRBefore b k)]'hpos = k+1) := by
  dsimp
  let p : Nat → Bool := fun v => b.getD (v-1) false
  let pre := (1...=n).toList.take k
  let suf := (1...=n).toList.drop (k+1)
  have vs := mr_vals_split n k hk
  have lp := mr_filter_prefix_word n b hb k (by omega)
  change (((pre.filter p).length = MRBefore b k)) at lp
  have plen : pre.length = k := by
    simp [pre, Nat.length_toList_rcc, hk.le]
  have comp := mr_filter_compl_length pre p
  have rp : (pre.filter (fun v => ! p v)).length = k - MRBefore b k := by
    omega
  have allcomp := mr_filter_compl_length (1...=n).toList p
  have vlen : (1...=n).toList.length = n := by
    simpa using (Nat.length_toList_rcc (a:=1) (b:=n))
  have pkconv : p (k+1) = b.getD k false := by
    dsimp [p]
  constructor
  · intro pk
    have pk' : p (k+1) = true := by simpa [pkconv]
    have ldecomp : (1...=n).toList.filter p =
        pre.filter p ++ (k+1) :: suf.filter p := by
      rw [vs]
      simp [List.filter_append, pk', pre, suf] 
    have rdecomp : (1...=n).toList.filter (fun v => ! p v) =
        pre.filter (fun v => ! p v) ++ suf.filter (fun v => ! p v) := by
      rw [vs]
      simp [List.filter_append, pk', pre, suf] 
    let l := (1...=n).toList.filter p
    let r := (1...=n).toList.filter (fun v => ! p v)
    have posL : MRBefore b k < l.length := by
      dsimp [l]; rw [ldecomp]; simp [lp]
    have posO : MRBefore b k < (l ++ r.reverse).length := by
      simp; omega
    refine ⟨posO, ?_⟩
    rw [List.getElem_append_left posL]
    -- avoid dependent rewrites by passing through getD
    have lval : l.getD (MRBefore b k) 0 = k+1 := by
      dsimp [l]
      rw [ldecomp]
      have hh : MRBefore b k = (pre.filter p).length := lp.symm
      let T := pre.filter p
      let U := suf.filter p
      change (T ++ (k+1)::U).getD (MRBefore b k) 0 = k+1
      rw [hh]
      have hpos : T.length < (T ++ (k+1)::U).length := by simp
      rw [List.getD_eq_getElem _ _ hpos]
      rw [List.getElem_append_right (by omega)]
      simp
    exact (List.getD_eq_getElem l 0 posL).symm.trans lval

  · intro pk
    have pk' : p (k+1) = false := by
      simpa [pkconv]
    have ldecomp : (1...=n).toList.filter p =
        pre.filter p ++ suf.filter p := by
      rw [vs]
      simp [List.filter_append, pk', pre, suf] 
    have rdecomp : (1...=n).toList.filter (fun v => ! p v) =
        pre.filter (fun v => ! p v) ++ (k+1) ::
          suf.filter (fun v => ! p v) := by
      rw [vs]
      simp [List.filter_append, pk', pre, suf] 
    let l := (1...=n).toList.filter p
    let r := (1...=n).toList.filter (fun v => ! p v)
    have lr : l.length + r.length = n := by
      dsimp [l,r]
      omega
    have rb : k - MRBefore b k < r.length := by
      dsimp [r]
      rw [rdecomp]
      simp [rp]
    let idx := n-1-(k-MRBefore b k)
    have idxform : idx = l.length + (r.length-1-(k-MRBefore b k)) := by
      dsimp [idx]
      omega
    have idxO : idx < (l ++ r.reverse).length := by
      simp only [List.length_append, List.length_reverse]
      rw [idxform]
      omega
    have outputval : (l ++ r.reverse).getD idx 0 = k+1 := by
      have q : r.length - 1 - (k-MRBefore b k) < r.reverse.length := by simp; omega
      have rid : r[k-MRBefore b k]'rb = k+1 := by
        -- entry after the filtered prefix in the increasing right list
        have rv : r.getD (k-MRBefore b k) 0 = k+1 := by
          dsimp [r]
          rw [rdecomp]
          let T := pre.filter (fun v => ! p v)
          let U := suf.filter (fun v => ! p v)
          have hh : k-MRBefore b k = T.length := by
            dsimp [T]
            omega
          change (T ++ (k+1)::U).getD (k-MRBefore b k) 0 = k+1
          rw [hh]
          have hpos : T.length < (T ++ (k+1)::U).length := by simp
          rw [List.getD_eq_getElem _ _ hpos]
          rw [List.getElem_append_right (by omega)]
          simp
        exact (List.getD_eq_getElem r 0 rb).symm.trans rv
      have revv : r.reverse[r.length-1-(k-MRBefore b k)]'q = k+1 := by
        rw [List.getElem_reverse]
        have heq : r.length - 1 - (r.length-1-(k-MRBefore b k)) =
            k-MRBefore b k := by omega
        simpa [heq] using rid
      have q' : l.length ≤ idx := by rw [idxform]; omega
      rw [List.getD_eq_getElem _ _ idxO]
      rw [List.getElem_append_right q']
      have sub : idx - l.length = r.length-1-(k-MRBefore b k) := by
        rw [idxform]; omega
      simpa [sub] using revv
    refine ⟨?_, ?_⟩
    · change idx < (( (1...=n).toList.filter p) ++
          ((1...=n).toList.filter (fun v => ! p v)).reverse).length
      simpa [l, r] using idxO
    · change (l ++ r.reverse)[idx]'idxO = k+1
      exact (List.getD_eq_getElem _ _ idxO).symm.trans outputval



/-- Elementary prefix-count bookkeeping. -/
theorem mr_before_succ (b : List Bool) {k : Nat} (hk : k < b.length) :
    MRBefore b (k+1) = MRBefore b k + (if b[k] then 1 else 0) := by
  unfold MRBefore
  rw [List.take_succ_eq_append_getElem hk, mr_true_append]
  simp

theorem mr_before_le (b : List Bool) (k : Nat) : MRBefore b k ≤ k := by
  unfold MRBefore MRTrue
  exact le_trans (List.length_filter_le _ _) (by simp)

theorem mr_before_mono (b : List Bool) {u v : Nat}
    (h : u ≤ v) : MRBefore b u ≤ MRBefore b v := by
  unfold MRBefore MRTrue
  have hs0 := List.take_sublist u (b.take v)
  have eq : (b.take v).take u = b.take u := by
    simp [List.take_take, Nat.min_eq_left h]
  have hs : b.take u |>.Sublist (b.take v) := by simpa [eq] using hs0
  have hf := hs.filter (fun x => x)
  exact List.Sublist.length_le hf

/-- Both sorts of steps are monotone; after taking the current step the
corresponding coordinate has advanced. -/
theorem mr_before_gap (b : List Bool) {k j : Nat}
    (hj : j ≤ b.length) (h : k < j) :
    MRBefore b k + (if b.getD k false then 1 else 0) ≤ MRBefore b j ∧
      k - MRBefore b k + (if b.getD k false then 0 else 1) ≤
          j - MRBefore b j := by
  have hk : k < b.length := by omega
  have hs := mr_before_succ b hk
  have hm := mr_before_mono b (show k+1 ≤ j by omega)
  have one : b.getD k false = b[k] := List.getD_eq_getElem b false hk
  rw [one]
  have up : MRBefore b j ≤ MRBefore b (k+1) + (j-(k+1)) := by
    -- at most one new true per extra cell; use complement count symmetry
    unfold MRBefore MRTrue
    -- sublist prefix difference in length; a crude length argument via takes
    have eqt : b.take j = b.take (k+1) ++ (b.take j).drop (k+1) := by
      have := List.take_append_drop (k+1) (b.take j)
      have eq : (b.take j).take (k+1) = b.take (k+1) := by
        simp [List.take_take, Nat.min_eq_left (by omega : k+1 ≤ j)]
      simpa [eq] using this.symm
    rw [eqt, List.filter_append, List.length_append]
    have lenrest : ((b.take j).drop (k+1)).length ≤ j-(k+1) := by
      have jl : (b.take j).length = j := by simp; omega
      simp [List.length_drop, jl]
    have ff := List.length_filter_le id ((b.take j).drop (k+1))
    omega
  constructor
  · rw [hs] at hm
    simpa [one] using hm
  · rw [hs] at up
    cases e : b[k] <;> simp [e] at up ⊢ <;>
      have bk := mr_before_le b k <;>
      have bj := mr_before_le b j <;> omega

def MREdge (n : Nat) (b : List Bool) (k : Nat) : Nat × Nat :=
  if b.getD k false then
    MRLP (MRBefore b k) (k+1)
  else
    MRRP n (n-1-(k-MRBefore b k)) (k+1)

theorem mr_edge_coords {n : Nat} {b : List Bool} (hb : b.length = n)
    {k : Nat} (hk : k < n) :
    MREdge n b k =
      if b.getD k false then (2*(MRBefore b k)+1, 2*(k-MRBefore b k))
      else (2*(MRBefore b k), 2*(k-MRBefore b k)+1) := by
  have lb := mr_before_le b k
  have kb : k < b.length := by omega
  unfold MREdge MRLP MRRP
  split <;> rename_i q
  · simp
    omega
  · simp
    omega

theorem mr_edge_pair {n : Nat} {b : List Bool} (hb : b.length = n)
    {k j : Nat} (hk : k < j) (hj : j < n) :
    MRPointLe (MREdge n b k) (MREdge n b j) ∧
       (MREdge n b k).2 ≤ (MREdge n b j).2 := by
  have kg : k < n := by omega
  have gap := mr_before_gap b (show j ≤ b.length by omega) hk
  rw [mr_edge_coords hb kg, mr_edge_coords hb hj]
  have bl := mr_before_le b k
  have bl' := mr_before_le b j
  split <;> rename_i e <;> split <;> rename_i f
  · change (MRBefore b k + (if b.getD k false then 1 else 0) ≤ MRBefore b j ∧
        k - MRBefore b k + (if b.getD k false then 0 else 1) ≤ j - MRBefore b j) at gap
    simp only [e, Bool.false_eq_true, Bool.not_false, ite_true, ite_false] at gap
    constructor
    · apply (mr_pointLe_iff _ _).2; left; omega
    · omega
  · change (MRBefore b k + (if b.getD k false then 1 else 0) ≤ MRBefore b j ∧
        k - MRBefore b k + (if b.getD k false then 0 else 1) ≤ j - MRBefore b j) at gap
    simp only [e, Bool.false_eq_true, Bool.not_false, ite_true, ite_false] at gap
    constructor
    · apply (mr_pointLe_iff _ _).2; left; omega
    · omega
  · change (MRBefore b k + (if b.getD k false then 1 else 0) ≤ MRBefore b j ∧
        k - MRBefore b k + (if b.getD k false then 0 else 1) ≤ j - MRBefore b j) at gap
    simp only [e, Bool.false_eq_true, Bool.not_false, ite_true, ite_false] at gap
    constructor
    · apply (mr_pointLe_iff _ _).2
      left
      omega
    · omega
  · change (MRBefore b k + (if b.getD k false then 1 else 0) ≤ MRBefore b j ∧
        k - MRBefore b k + (if b.getD k false then 0 else 1) ≤ j - MRBefore b j) at gap
    simp only [e, Bool.false_eq_true, Bool.not_false, ite_true, ite_false] at gap
    constructor
    · apply (mr_pointLe_iff _ _).2
      by_cases x : MRBefore b k < MRBefore b j
      · left; omega
      · right; constructor <;> omega
    · omega

/-- The output of a word has the advertised edge at every value. -/
theorem mr_word_fixed {a : Array Nat} (b : List Bool)
    (hb : b.length = a.size) {k : Nat} (hk : k < a.size) :
    let p : Nat → Bool := fun v => b.getD (v-1) false
    let out := (((1...=a.size).toList.filter p) ++
       ((1...=a.size).toList.filter (fun v => ! p v)).reverse).toArray
    let idx := if b.getD k false then MRBefore b k else
                  a.size-1-(k-MRBefore b k)
    out[idx]? = some (k+1) := by
  dsimp
  have hh := mr_split_get a.size b hb k hk
  have eqp : b.getD (k+1-1) false = b.getD k false := by congr 1
  by_cases q : b.getD k false
  · have pp : (fun v => b.getD (v-1) false) (k+1) = true := by simpa [eqp]
    rcases hh.1 pp with ⟨hpos, hv⟩
    have hv' :
        (((1...=a.size).toList.filter fun v => b.getD (v-1) false) ++
          ((1...=a.size).toList.filter fun v => ! b.getD (v-1) false).reverse)[MRBefore b k]? =
             some (k+1) := by
      rw [List.getElem?_eq_getElem hpos]
      exact congrArg some hv
    -- do not let simp unfold getD in the conditional
    change _[if b.getD k false then MRBefore b k else a.size-1-(k-MRBefore b k)]? = _
    simpa only [q, ite_true, List.getElem?_toArray] using hv' 
  · have q' : b.getD k false = false := by cases e:b.getD k false <;> simp_all
    have pp : (fun v => b.getD (v-1) false) (k+1) = false := by simpa [eqp, q']
    rcases hh.2 pp with ⟨hpos, hv⟩
    have hv' :
        (((1...=a.size).toList.filter fun v => b.getD (v-1) false) ++
          ((1...=a.size).toList.filter fun v => ! b.getD (v-1) false).reverse)[a.size-1-(k-MRBefore b k)]? =
             some (k+1) := by
      rw [List.getElem?_eq_getElem hpos]
      exact congrArg some hv
    change _[if b.getD k false then MRBefore b k else a.size-1-(k-MRBefore b k)]? = _
    simpa only [q', Bool.false_eq_true, ite_false, List.getElem?_toArray] using hv' 


/-- If the position associated to a word step is already correct in the old
array, its midpoint is one of the program points. -/
theorem mr_edge_mem {a : Array Nat} {b : List Bool}
    (hb : b.length = a.size) {k : Nat} (hk : k < a.size)
    (ha : a.getD (if b.getD k false then MRBefore b k
                  else a.size-1-(k-MRBefore b k)) 0 = k+1) :
    MREdge a.size b k ∈ MRPoints a := by
  have lc := mr_before_le b k
  by_cases q : b.getD k false
  · have idxlt : MRBefore b k < a.size := by omega
    have aval : a[MRBefore b k]'idxlt = k+1 := by
      have hh := ha
      simp only [q, ite_true] at hh
      simpa [mr_getD_in idxlt] using hh
    apply (mr_mem_points a _).2
    left
    refine ⟨MRBefore b k, idxlt, ?_, ?_⟩
    · rw [aval]; omega
    · simp only [MREdge, q, ite_true, aval]
  · have q' : b.getD k false = false := by cases h:b.getD k false <;> simp_all
    let r := k - MRBefore b k
    have rl : r ≤ k := by dsimp [r]; omega
    let idx := a.size-1-r
    have idxlt : idx < a.size := by dsimp [idx,r]; omega
    have ir : a.size-1-idx = r := by dsimp [idx]; omega
    have aval : a[idx]'idxlt = k+1 := by
      have hh := ha
      simp only [q', Bool.false_eq_true, ite_false] at hh
      simpa [idx, r, mr_getD_in idxlt] using hh
    apply (mr_mem_points a _).2
    right
    refine ⟨idx, idxlt, ?_, ?_⟩
    · rw [aval]
      dsimp [idx,r]
      omega
    · rw [aval]
      unfold MREdge
      simp only [q', Bool.false_eq_true, ite_false]
      congr 2 <;> dsimp [idx,r] <;> omega

theorem mr_edge_diag {n : Nat} {b : List Bool} (hb : b.length = n)
    {k : Nat} (hk : k < n) :
    (MREdge n b k).1 + (MREdge n b k).2 = 2*k+1 := by
  rw [mr_edge_coords hb hk]
  have le := mr_before_le b k
  split <;> omega

/-- The already-correct steps of an arbitrary left/right word form a chain.
This is the order-theoretic half of the path argument; it is independent of
how the word was completed. -/
theorem mr_word_chain {a : Array Nat}
    {b : List Bool} (hb : b.length = a.size) :
    let idx : Nat → Nat := fun k =>
       if b.getD k false then MRBefore b k else a.size-1-(k-MRBefore b k)
    let good : List Nat := (List.range a.size).filter
       (fun k => decide (a.getD (idx k) 0 = k+1))
    MRChain a (good.map (MREdge a.size b)) := by
  dsimp
  let ix : Nat → Nat := fun k =>
       if b.getD k false then MRBefore b k else a.size-1-(k-MRBefore b k)
  let g : List Nat := (List.range a.size).filter
       (fun k => decide (a.getD (ix k) 0 = k+1))
  change MRChain a (g.map (MREdge a.size b))
  have gb : ∀ k ∈ g, k < a.size := by
    intro k hk
    have h := (List.mem_filter.1 hk).1
    simpa using (List.mem_range.1 h)
  have gok : ∀ k ∈ g, a.getD (ix k) 0 = k+1 := by
    intro k hk
    exact of_decide_eq_true (List.mem_filter.1 hk).2
  have gp : g.Pairwise (fun u v : Nat => u < v) := by
    exact (List.Pairwise.sublist (List.filter_sublist)
       (List.pairwise_lt_range))
  constructor
  · intro z hz
    rcases List.mem_map.1 hz with ⟨k,hk,rfl⟩
    have ok := gok k hk
    change a.getD (if b.getD k false then MRBefore b k else
          a.size-1-(k-MRBefore b k)) 0 = k+1 at ok
    exact mr_edge_mem hb (gb k hk) ok
  constructor
  · apply (List.pairwise_map).2
    refine gp.imp_of_mem ?_
    intro k j hk hj lt
    exact (mr_edge_pair hb lt (gb j hj)).1
  · constructor
    · apply (List.pairwise_map).2
      refine gp.imp_of_mem ?_
      intro k j hk hj lt
      exact (mr_edge_pair hb lt (gb j hj)).2
    · -- distinct diagonals make the map injective
      have gn : g.Nodup := (by dsimp [g]; exact (List.nodup_range.filter _))
      apply gn.map_on
      intro u hu v hv eq
      have eu := mr_edge_diag hb (gb u hu)
      have ev := mr_edge_diag hb (gb v hv)
      rw [eq] at eu
      omega



/-- Midpoint of the `k`-th step of an abstract left/right word, if `t` of the
values before it have gone to the left.  This nondependent normal form is handy
when interpolating a path: its other count is literally `k-t`. -/
def MRSCoord (t k : Nat) (e : Bool) : Nat × Nat :=
  if e then (2*t+1, 2*(k-t)) else (2*t, 2*(k-t)+1)

/-- The semantic requirement carried by a program point, without mentioning
`MRLP` or `MRRP`: the old array really has the value `k+1` in the place
which this step of a word would fill. -/
def MRReq (a : Array Nat) (k t : Nat) (e : Bool) : Prop :=
  k < a.size ∧ t ≤ k ∧
    a.getD (if e then t else a.size-1-(k-t)) 0 = k+1

@[simp] theorem mr_scoord_true (t k : Nat) :
    MRSCoord t k true = (2*t+1, 2*(k-t)) := by simp [MRSCoord]
@[simp] theorem mr_scoord_false (t k : Nat) :
    MRSCoord t k false = (2*t, 2*(k-t)+1) := by simp [MRSCoord]

/-- Decoding a point in the unsorted table.  On a permutation its diagonal
is a unique value `k+1`; the first (respectively second) half-coordinate is the
number of already-left (respectively already-right) choices. -/
theorem mr_point_decode {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) {z : Nat × Nat}
    (hz : z ∈ MRPoints a) :
    ∃ k t : Nat, ∃ e : Bool, MRReq a k t e ∧ z = MRSCoord t k e := by
  rcases (mr_mem_points a z).1 hz with h | h
  · rcases h with ⟨i,hi,hel,rfl⟩
    have bd := mr_perm_entry_bounds hp i hi
    let k := a[i]-1
    have kk : k + 1 = a[i] := by dsimp [k]; omega
    have kl : k < a.size := by dsimp [k]; omega
    have il : i ≤ k := by dsimp [k]; omega
    refine ⟨k, i, true, ?_, ?_⟩
    · refine ⟨kl, il, ?_⟩
      have gi : a.getD i 0 = a[i] := mr_getD_in hi
      simp [gi, kk]
    · -- expose the harmless Nat subtractions
      dsimp [MRLP]
      simp [MRSCoord]
      omega
  · rcases h with ⟨i,hi,hel,rfl⟩
    have bd := mr_perm_entry_bounds hp i hi
    let k := a[i]-1
    let r := a.size-1-i
    have kk : k + 1 = a[i] := by dsimp [k]; omega
    have kl : k < a.size := by dsimp [k]; omega
    have rk : r ≤ k := by dsimp [r,k]; omega
    let t := k-r
    have tk : t ≤ k := by dsimp [t]; omega
    have kt : k - t = r := by dsimp [t]; omega
    have pos : a.size - 1 - (k-t) = i := by rw [kt]; dsimp [r]; omega
    refine ⟨k, t, false, ?_, ?_⟩
    · refine ⟨kl, tk, ?_⟩
      simp only [Bool.false_eq_true, ite_false, pos]
      exact (mr_getD_in hi).trans kk.symm
    · -- vertical midpoint: `r` is the number of previous right choices
      simp [MRSCoord, MRRP]
      constructor
      · dsimp [t, k, r]
        omega
      · dsimp [t, k, r]
        omega

/-- Midpoint coordinates dominate one another only in chronological order.
More precisely the previous completed counts fit in the next prefix.  The
slightly non-obvious equal-coordinate cases use the actual fixed cell of the
permutation: two horizontal steps with the same left count would address the
same cell, as would two vertical steps with the same right count. -/
theorem mr_req_gap {a : Array Nat} {k t j u : Nat} {e f : Bool}
    (hk : MRReq a k t e) (hj : MRReq a j u f)
    (hne : MRSCoord t k e ≠ MRSCoord u j f)
    (hl : MRPointLe (MRSCoord t k e) (MRSCoord u j f))
    (hy : (MRSCoord t k e).2 ≤ (MRSCoord u j f).2) :
    k < j ∧ t + (if e then 1 else 0) ≤ u ∧
       (k-t) + (if e then 0 else 1) ≤ j-u := by
  rcases hk with ⟨kb, tk, kv⟩
  rcases hj with ⟨jb, uj, jv⟩
  have hx : (MRSCoord t k e).1 ≤ (MRSCoord u j f).1 := by
    rcases (mr_pointLe_iff _ _).1 hl with h | ⟨q,_⟩
    · exact Nat.le_of_lt h
    · exact le_of_eq q
  cases e <;> cases f
  · -- two vertical steps
    simp [MRSCoord] at hx hy hne ⊢
    -- equal right count would address the same place of `a`
    have ltK : k < j := by
      have leK : k ≤ j := by omega
      have neK : k ≠ j := by
        intro eq; subst j
        have tu : t = u := by omega
        exact (hne tu) (by rw [tu])
      omega
    have strictR : k - t < j - u := by
      have leR : k - t ≤ j - u := by omega
      have neR : k - t ≠ j - u := by
        intro er
        have ps : a.size - 1 - (k-t) = a.size - 1 - (j-u) := by rw [er]
        -- both requests read the very same cell
        have vv : k+1 = j+1 := by
          calc
            k+1 = a.getD (a.size-1-(k-t)) 0 := kv.symm
            _ = a.getD (a.size-1-(j-u)) 0 := by rw [ps]
            _ = j+1 := jv
        omega
      omega
    refine ⟨ltK, ?_, ?_⟩ <;> omega
  · -- vertical then horizontal
    simp [MRSCoord] at hx hy hne ⊢
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · -- horizontal then vertical
    simp [MRSCoord] at hx hy hne ⊢
    refine ⟨?_, ?_, ?_⟩ <;> omega
  · -- two horizontal steps: equal `t` is the same position
    simp [MRSCoord] at hx hy hne ⊢
    have ltK : k < j := by
      have leK : k ≤ j := by omega
      have neK : k ≠ j := by
        intro eq; subst j
        have tu : t = u := by omega
        exact (hne tu) (by rw [tu])
      omega
    have strictT : t < u := by
      have leT : t ≤ u := by omega
      have neT : t ≠ u := by
        intro et
        have vv : k+1 = j+1 := by
          calc
            k+1 = a.getD t 0 := kv.symm
            _ = a.getD u 0 := by rw [et]
            _ = j+1 := jv
        omega
      omega
    refine ⟨ltK, ?_, ?_⟩ <;> omega

/-- Counts of an explicit block with a prescribed number of lefts.  It will
be convenient to append such blocks while filling the gaps of a partial
path. -/
def MRBlock (x y : Nat) : List Bool :=
  List.replicate x true ++ List.replicate y false

@[simp] theorem mr_block_length (x y : Nat) :
    (MRBlock x y).length = x+y := by simp [MRBlock]
@[simp] theorem mr_true_block (x y : Nat) :
    MRTrue (MRBlock x y) = x := by simp [MRBlock]


/-- A finite path constraint. The `k`-th value is placed after exactly `t`
left values; `e` says whether it itself goes left. -/
structure MRDatum where
  k : Nat
  t : Nat
  e : Bool

def MRFit (d q : MRDatum) : Prop :=
  d.k < q.k ∧
  d.t + (if d.e then 1 else 0) ≤ q.t ∧
  (d.k-d.t) + (if d.e then 0 else 1) ≤ q.k-q.t

def MRValid (n : Nat) (d : MRDatum) : Prop := d.k < n ∧ d.t ≤ d.k

/-- Extending a prefix through a list of compatible step specifications.  This
is the pedestrian interpolation argument for the grid.  At each step the
missing true cells, then the missing false cells, are appended; doing it in
that fixed order is convenient and loses nothing. -/
theorem mr_fill_data_aux (n cur T : Nat) (pre : List Bool) (ds : List MRDatum)
    (plen : pre.length = cur) (ptrue : MRTrue pre = T)
    (tc : T ≤ cur) (cn : cur ≤ n)
    (vd : ∀ d ∈ ds, MRValid n d)
    (front : ∀ d ∈ ds, cur ≤ d.k ∧ T ≤ d.t ∧ cur-T ≤ d.k-d.t)
    (ord : ds.Pairwise MRFit) :
    ∃ b : List Bool, (∃ w, b = pre ++ w) ∧ b.length = n ∧
      (∀ d ∈ ds, MRBefore b d.k = d.t ∧ b.getD d.k false = d.e) := by
  induction ds generalizing cur T pre with
  | nil =>
      let w : List Bool := List.replicate (n-cur) false
      refine ⟨pre ++ w, ⟨w, rfl⟩, ?_, ?_⟩
      · dsimp [w]
        simp
        omega
      · intro d hd; simpa using hd
  | cons d rest ih =>
      have dv : MRValid n d := vd d (by simp)
      have df : cur ≤ d.k ∧ T ≤ d.t ∧ cur-T ≤ d.k-d.t :=
        front d (by simp)
      rcases df with ⟨cK, tT, fF⟩
      have dkbd : d.k < n := dv.1
      have dtk : d.t ≤ d.k := dv.2
      have dor : rest.Pairwise MRFit := (List.pairwise_cons.1 ord).2
      let x := d.t-T
      let y := (d.k-d.t) - (cur-T)
      let pk : List Bool := pre ++ MRBlock x y
      have pklen : pk.length = d.k := by
        dsimp [pk]
        rw [List.length_append, mr_block_length]
        rw [plen]
        dsimp [x,y]
        exact (by omega)
      have pktrue : MRTrue pk = d.t := by
        dsimp [pk]
        rw [mr_true_append, mr_true_block, ptrue]
        dsimp [x]
        omega
      let pre1 : List Bool := pk ++ [d.e]
      let cur1 : Nat := d.k + 1
      let T1 : Nat := d.t + (if d.e then 1 else 0)
      have pre1len : pre1.length = cur1 := by simp [pre1, cur1, pklen]
      have pre1true : MRTrue pre1 = T1 := by
        simp [pre1, T1, mr_true_append, pktrue, mr_true_one]
      have tc1 : T1 ≤ cur1 := by
        have hdk : d.t ≤ d.k := dv.2
        dsimp [T1, cur1]
        split <;> omega
      have cn1 : cur1 ≤ n := by dsimp [cur1]; omega
      have vd1 : ∀ z ∈ rest, MRValid n z := by
        intro z hz; exact vd z (by simp [hz])
      have front1 : ∀ z ∈ rest,
          cur1 ≤ z.k ∧ T1 ≤ z.t ∧ cur1 - T1 ≤ z.k-z.t := by
        intro z hz
        have hfit : MRFit d z := (List.pairwise_cons.1 ord).1 z hz
        rcases hfit with ⟨hkj, htt, hff⟩
        refine ⟨(by dsimp [cur1]; omega), ?_, ?_⟩
        · exact htt
        · dsimp [cur1, T1]
          cases de : d.e <;> simp [de] at htt hff ⊢ <;> omega
      rcases ih cur1 T1 pre1 pre1len pre1true tc1 cn1 vd1 front1 dor with
        ⟨b, ⟨w, be⟩, blen, bspec⟩
      refine ⟨b, ?_, blen, ?_⟩
      · refine ⟨MRBlock x y ++ [d.e] ++ w, ?_⟩
        -- just reassociate the extended prefix
        simp [be, pre1, pk, List.append_assoc]
      · intro z hz
        rcases List.mem_cons.1 hz with heq | hr
        · subst z
          -- the newly prescribed entry sits immediately after `pk`
          have kin1 : d.k < pre1.length := by rw [pre1len]; omega
          have bbefore : MRBefore b d.k = MRBefore pre1 d.k := by
            unfold MRBefore
            rw [be, List.take_append_of_le_length (by omega : d.k ≤ pre1.length)]
          have prebefore : MRBefore pre1 d.k = d.t := by
            unfold MRBefore
            rw [List.take_left' (l₁:=pk) (l₂:=[d.e]) pklen]
            exact pktrue
          have bget : b.getD d.k false = pre1.getD d.k false := by
            rw [be]
            exact List.getD_append pre1 w false d.k kin1
          have thisget : pre1.getD d.k false = d.e := by
            -- it is the singleton following `pk`
            rw [show pre1 = pk ++ [d.e] by rfl,
                List.getD_append_right pk [d.e] false d.k (by omega : pk.length ≤ d.k)]
            have kk : d.k - pk.length = 0 := by omega
            simp [kk]
          exact ⟨bbefore.trans prebefore, bget.trans thisget⟩
        · exact bspec z hr

/-- Version starting at the empty prefix. -/
theorem mr_fill_data (n : Nat) (ds : List MRDatum)
    (vd : ∀ d ∈ ds, MRValid n d)
    (ord : ds.Pairwise MRFit) :
    ∃ b : List Bool, b.length = n ∧
      (∀ d ∈ ds, MRBefore b d.k = d.t ∧ b.getD d.k false = d.e) := by
  have fr : ∀ d ∈ ds, 0 ≤ d.k ∧ 0 ≤ d.t ∧ 0-0 ≤ d.k-d.t := by
    intro d hd; omega
  rcases mr_fill_data_aux n 0 0 [] ds (by simp) (by simp) (by omega)
       (by omega) vd fr ord with ⟨b,_,h,hh⟩
  exact ⟨b,h,hh⟩


def MRDatum.coord (d : MRDatum) : Nat × Nat := MRSCoord d.t d.k d.e

def MRDatum.req (a : Array Nat) (d : MRDatum) : Prop := MRReq a d.k d.t d.e

/-- A finite chain of actual program points can first be decoded to compatible
abstract steps, and those steps can all be extended to a complete word.  This
isolates the interpolation (the easy grid part) from all later counting. -/
theorem mr_chain_word_data {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) {c : List (Nat × Nat)}
    (hc : MRChain a c) :
    ∃ ds : List MRDatum, ∃ b : List Bool,
      ds.length = c.length ∧ c = ds.map MRDatum.coord ∧
      b.length = a.size ∧ ds.Pairwise MRFit ∧
      (∀ d ∈ ds, MRDatum.req a d ∧
         MRBefore b d.k = d.t ∧ b.getD d.k false = d.e) := by
  classical
  rcases hc with ⟨hm, hl, hy, hn⟩
  have H : ∀ (z : Nat × Nat) (_h : z ∈ c),
      ∃ d : MRDatum, MRDatum.req a d ∧ z = d.coord := by
    intro z hz
    rcases mr_point_decode hp (hm z hz) with ⟨k,t,e,hq,eq⟩
    exact ⟨⟨k,t,e⟩, hq, eq⟩
  choose pick hpick using H
  let sel : (Nat × Nat) → MRDatum := fun z =>
    if h : z ∈ c then pick z h else ⟨0,0,false⟩
  have selspec : ∀ (z : Nat × Nat) (hz : z ∈ c),
       MRDatum.req a (sel z) ∧ z = (sel z).coord := by
    intro z hz
    dsimp [sel]
    split <;> rename_i q
    · exact hpick z q
    · exact False.elim (q hz)
  let ds : List MRDatum := c.map sel
  have dlen : ds.length = c.length := by simp [ds]
  have deq : c = ds.map MRDatum.coord := by
    have ee : c.map (fun z => (sel z).coord) = c.map (fun z => z) := by
      apply (List.map_inj_left).2
      intro z hz
      exact (selspec z hz).2.symm
    simpa [ds, List.map_map, Function.comp_def] using ee.symm
  have vd : ∀ d ∈ ds, MRValid a.size d := by
    intro d hd
    change d ∈ c.map sel at hd
    rcases List.mem_map.1 hd with ⟨z,hz,ze⟩
    rw [← ze]
    have hq := (selspec z hz).1
    exact ⟨hq.1, hq.2.1⟩
  have ord : ds.Pairwise MRFit := by
    dsimp [ds]
    apply (List.pairwise_map).2
    have hxy : c.Pairwise (fun z w => MRPointLe z w ∧ z.2 ≤ w.2) :=
      (List.pairwise_and_iff).2 ⟨hl, hy⟩
    have hne : c.Pairwise (fun z w : Nat × Nat => z ≠ w) :=
      (List.nodup_iff_pairwise_ne).1 hn
    have hall : c.Pairwise
        (fun z w => (MRPointLe z w ∧ z.2 ≤ w.2) ∧ z ≠ w) :=
      (List.pairwise_and_iff).2 ⟨hxy, hne⟩
    refine hall.imp_of_mem ?_
    intro z w hz hw hh
    rcases hh with ⟨⟨hle,hyy⟩,hzw⟩
    have sz := selspec z hz
    have sw := selspec w hw
    have nez : (sel z).coord ≠ (sel w).coord := by
      intro eq
      apply hzw
      calc
        z = (sel z).coord := sz.2
        _ = (sel w).coord := eq
        _ = w := sw.2.symm
    have le' : MRPointLe (sel z).coord (sel w).coord := by
      rw [← sz.2, ← sw.2]; exact hle
    have yy' : ((sel z).coord).2 ≤ ((sel w).coord).2 := by
      rw [← sz.2, ← sw.2]; exact hyy
    have gap := mr_req_gap (sz.1) (sw.1) nez le' yy'
    exact gap
  rcases mr_fill_data a.size ds vd ord with ⟨b, bl, bs⟩
  refine ⟨ds, b, dlen, deq, bl, ord, ?_⟩
  intro d hd
  have hq : d.req a := by
    have hd' := hd
    change d ∈ c.map sel at hd'
    rcases List.mem_map.1 hd' with ⟨z,hz,ze⟩
    rw [← ze]
    exact (selspec z hz).1
  rcases bs d hd with ⟨bb, be⟩
  exact ⟨hq, bb, be⟩

/-- Replacing the syntactic coordinates of a datum by the edge computed from
its interpolating word. -/
theorem mr_edge_of_data {a : Array Nat} (b : List Bool)
    (bl : b.length = a.size) (d : MRDatum)
    (dv : MRDatum.req a d)
    (dt : MRBefore b d.k = d.t) (de : b.getD d.k false = d.e) :
    MREdge a.size b d.k = d.coord := by
  have dk : d.k < a.size := dv.1
  rw [mr_edge_coords bl dk]
  unfold MRDatum.coord
  rw [dt, de]
  cases d.e <;> simp [MRSCoord]


/-- the first label in a compatible specification cannot occur twice -/
theorem mr_data_k_inj {l : List MRDatum} (h : l.Pairwise MRFit)
    {d q : MRDatum} (hd : d ∈ l) (hq : q ∈ l) (he : d.k = q.k) : d = q := by
  induction l generalizing d q with
  | nil => simp at hd
  | cons z zs ih =>
      have hp := (List.pairwise_cons.1 h)
      rcases List.mem_cons.1 hd with hd0 | hd1
      · subst d
        rcases List.mem_cons.1 hq with hq0 | hq1
        · simpa using hq0.symm
        · have gg := (hp.1 q hq1).1
          omega
      · rcases List.mem_cons.1 hq with hq0 | hq1
        · subst q
          have gg := (hp.1 d hd1).1
          omega
        · exact ih hp.2 hd1 hq1 he

/-- The completion side of the path argument, now that the interpolation has
been separated out.  A useful counting trick is to list the *addresses* of
specified steps as elements of `finRange`: distinct steps have distinct
addresses because the old permutation has just one copy of a value. -/
theorem mr_chain_complete {a : Array Nat}
    (hp : a.Perm (1...=a.size).toArray) {c : List (Nat × Nat)}
    (hc : MRChain a c) :
    ∃ x : Array Nat, x.Perm (1...=a.size).toArray ∧ Unimodal x ∧
       c.length ≤ MRKeep a x := by
  classical
  rcases mr_chain_word_data hp hc with ⟨ds,b,dl,ce,bl,ord,sp⟩
  let addr : MRDatum → Nat := fun d =>
    if b.getD d.k false then MRBefore b d.k
    else a.size-1-(d.k-MRBefore b d.k)
  have addrform : ∀ d ∈ ds,
      addr d = if d.e then d.t else a.size-1-(d.k-d.t) := by
    intro d hd
    rcases sp d hd with ⟨_,dt,de⟩
    dsimp [addr]
    rw [de, dt]
  have abnd : ∀ d ∈ ds, addr d < a.size := by
    intro d hd
    have rq := (sp d hd).1
    rw [addrform d hd]
    rcases rq with ⟨dk,tt,_⟩
    cases z : d.e <;> simp [z] <;> omega
  have aval : ∀ d ∈ ds, a.getD (addr d) 0 = d.k+1 := by
    intro d hd
    have rq := (sp d hd).1
    rw [addrform d hd]
    exact rq.2.2
  let p : Nat → Bool := fun v => b.getD (v-1) false
  let left := (1...=a.size).toList.filter p
  let right := (1...=a.size).toList.filter (fun v => !p v)
  let out : Array Nat := (left ++ right.reverse).toArray
  have outok := mr_split_values a.size p
  change out.Perm (1...=a.size).toArray ∧ Unimodal out at outok
  have os : out.size = a.size := by
    simpa using outok.1.size_eq
  have oval : ∀ d ∈ ds, out.getD (addr d) 0 = d.k+1 := by
    intro d hd
    have dk := (sp d hd).1.1
    have wh := mr_word_fixed (a:=a) b bl dk
    change
      ((((1...=a.size).toList.filter fun v => b.getD (v-1) false) ++
       ((1...=a.size).toList.filter fun v => !b.getD (v-1) false).reverse).toArray)[if b.getD d.k false then MRBefore b d.k else
            a.size-1-(d.k-MRBefore b d.k)]? = some (d.k+1) at wh
    have wh' : out[addr d]? = some (d.k+1) := by
      simpa [out, left, right, p, addr] using wh
    have ai : addr d < out.size := by rw [os]; exact abnd d hd
    rw [Array.getElem?_eq_getElem ai] at wh'
    have ev : out[addr d]'ai = d.k+1 := Option.some.inj wh'
    simpa [mr_getD_in ai] using ev
  -- attach the membership proofs, so `Fin` carries a genuine in-bounds address
  let faddr : {d // d ∈ ds} → Fin a.size := fun d =>
    ⟨addr d.1, abnd d.1 d.2⟩
  let inds : List (Fin a.size) := ds.attach.map faddr
  have dnod : ds.Nodup := by
    apply (List.nodup_iff_pairwise_ne).2
    exact ord.imp (by
      intro d q gg eq
      subst q
      exact (Nat.ne_of_lt gg.1) rfl)
  have inod : inds.Nodup := by
    dsimp [inds]
    apply (List.nodup_attach.2 dnod).map_on
    intro u hu v hv eqf
    apply Subtype.ext
    have ee : addr u.1 = addr v.1 := congrArg Fin.val eqf
    have kk : u.1.k = v.1.k := by
      have avu := aval u.1 u.2
      have avv := aval v.1 v.2
      rw [ee] at avu
      omega
    exact mr_data_k_inj ord u.2 v.2 kk
  have isub : inds ⊆ (List.finRange a.size).filter
          (fun i => decide (a[i] = out.getD i.val 0)) := by
    intro z hz
    change z ∈ ds.attach.map faddr at hz
    rcases List.mem_map.1 hz with ⟨d,_,eqz⟩
    subst z
    apply List.mem_filter.2
    constructor
    · exact List.mem_finRange _
    · apply decide_eq_true
      have av := aval d.1 d.2
      have ov := oval d.1 d.2
      have ii : addr d.1 < a.size := abnd d.1 d.2
      simpa [faddr, mr_getD_in ii] using av.trans ov.symm
  have ilen : inds.length ≤ ((List.finRange a.size).filter
          (fun i => decide (a[i] = out.getD i.val 0))).length :=
    (List.subperm_of_subset inod isub).length_le
  refine ⟨out, outok.1, outok.2, ?_⟩
  unfold MRKeep
  have elen : inds.length = ds.length := by simp [inds]
  omega


/-- Encoding the two arms of any unimodal permutation by a word on its
values. This is the other useful half of the path picture. -/
theorem mr_unimodal_word {n : Nat} {x : Array Nat}
    (hx : x.Perm (1...=n).toArray) (hu : Unimodal x) :
    ∃ b : List Bool, b.length = n ∧
      x = (((1...=n).toList.filter (fun v => b.getD (v-1) false)) ++
           ((1...=n).toList.filter (fun v => !b.getD (v-1) false)).reverse).toArray := by
  rcases hu with ⟨xlA, xrA, xe, xli, xri⟩
  let xl : List Nat := xlA.toList
  let xr : List Nat := xrA.toList
  let vals : List Nat := (1...=n).toList
  have perm : (xl ++ xr).Perm vals := by
    have h := hx.toList
    simpa [xe, xl, xr, vals, Array.toList_append,
      Std.Rcc.toList_toArray] using h
  have vlen : vals.length = n := by dsimp [vals]; simp
  have nod : (xl ++ xr).Nodup :=
    ((perm.nodup_iff).2 (by
      dsimp [vals]
      exact Std.Rcc.nodup_toList))
  have nd := (List.nodup_append.1 nod)
  let p : Nat → Bool := fun v => decide (v ∈ xl)
  have pl : xl.filter p = xl := by
    apply (List.filter_eq_self).2
    intro a ha; exact decide_eq_true ha
  have pr0 : xr.filter p = [] := by
    apply (List.filter_eq_nil_iff).2
    intro a ha
    have nm : a ∉ xl := by
      intro bad
      exact nd.2.2 a bad a ha rfl
    intro eq
    have yes : a ∈ xl := of_decide_eq_true eq
    exact nm yes
  have pl0 : xl.filter (fun v => !p v) = [] := by
    apply (List.filter_eq_nil_iff).2
    intro a ha
    have yy : p a = true := decide_eq_true ha
    simp [yy]
  have pr : xr.filter (fun v => !p v) = xr := by
    apply (List.filter_eq_self).2
    intro a ha
    have nm : a ∉ xl := by
      intro bad; exact nd.2.2 a bad a ha rfl
    have yy : p a = false := decide_eq_false nm
    simp [yy]
  have lperm : xl.Perm (vals.filter p) := by
    have ff := perm.filter p
    simpa [List.filter_append, pl, pr0] using ff
  have rperm : xr.Perm (vals.filter (fun v => !p v)) := by
    have ff := perm.filter (fun v => !p v)
    simpa [List.filter_append, pl0, pr] using ff
  have vord : vals.Pairwise (fun a b : Nat => a < b) := by
    exact Std.Rcc.pairwise_toList_lt
  have li : xl.Pairwise (fun a b : Nat => a < b) := by simpa [xl] using xli
  have ri : xr.reverse.Pairwise (fun a b : Nat => a < b) := by
    rw [List.pairwise_reverse]
    simpa [xr, Function.swap_def] using xri
  have leimp : ∀ {a b : Nat}, a < b → a ≤ b := by
    intro a b h; omega
  have lexl := li.imp leimp
  have lel := (vord.filter p).imp leimp
  have eqL : xl = vals.filter p :=
    List.Perm.eq_of_pairwise' lexl lel lperm
  have eqR0 : xr = (vals.filter (fun v => !p v)).reverse := by
    -- ascending order on the reversal of the descending suffix
    have pp : xr.reverse.Perm (vals.filter (fun v => !p v)) :=
      (List.reverse_perm xr).trans rperm
    have oo : (vals.filter (fun v => !p v)).Pairwise
        (fun a b : Nat => a ≤ b) := (vord.filter _).imp leimp
    have er : xr.reverse = (vals.filter (fun v => !p v)) :=
      List.Perm.eq_of_pairwise' (ri.imp leimp) oo pp
    -- what we need about the decreasing suffix
    -- give it in increasing-right-list form for the final reversal below
    -- `reverse` both sides
    have er' := congrArg List.reverse er
    simpa using er' 
  -- store the characteristic function as a finite word
  let b : List Bool := vals.map p
  have bl : b.length = n := by simp [b, vlen]
  have read : ∀ v ∈ vals, b.getD (v-1) false = p v := by
    intro v hv
    have bounds : 1 ≤ v ∧ v ≤ n := by
      have hmem : v ∈ (1...=n).toList := by simpa [vals] using hv
      have hr : v ∈ (1...=n) := (Std.Rcc.mem_toList_iff_mem).1 hmem
      exact Std.Rcc.mem_iff.mp hr
    have ki : v-1 < vals.length := by rw [vlen]; omega
    have kb : v-1 < b.length := by rw [bl]; omega
    have vg : vals[v-1]'ki = v := by
      dsimp [vals] at ki ⊢
      have E := Nat.getElem_toList_rcc (m:=1) (n:=n) (i:=v-1) ki
      simpa using (E.trans (by congr 1 <;> omega))
    rw [List.getD_eq_getElem b false kb]
    simp [b, List.getElem_map, vg]
  refine ⟨b, bl, ?_⟩
  -- the filters agree extensionally on `vals`
  have fL : vals.filter (fun v => b.getD (v-1) false) = vals.filter p := by
    apply List.filter_congr
    intro v hv
    exact read v hv
  have fR : vals.filter (fun v => !b.getD (v-1) false) =
      vals.filter (fun v => !p v) := by
    apply List.filter_congr
    intro v hv
    have rr := read v hv
    simpa [rr]
  -- tuple of arrays
  have xt : x = (xl++xr).toArray := by
    apply (Array.toList_inj).1
    simp [xe, xl, xr, Array.toList_append]
  rw [xt]
  change (xl ++ xr).toArray =
    (vals.filter (fun v => b.getD (v-1) false) ++
       (vals.filter (fun v => !b.getD (v-1) false)).reverse).toArray
  rw [fL, fR, ← eqL, ← eqR0]


/-- Empty partial paths need no interpolation. -/
theorem mr_empty_chain_fill (a : Array Nat) :
    ∃ x : Array Nat, x.Perm (1...=a.size).toArray ∧ Unimodal x ∧
       ([] : List (Nat × Nat)).length ≤ MRKeep a x := by
  let p : Nat → Bool := fun _ => false
  let vals := (1...=a.size).toList
  let l := vals.filter p
  let r := vals.filter (fun t => !p t)
  let out : Array Nat := (l ++ r.reverse).toArray
  have hu := mr_split_values a.size p
  change out.Perm (1...=a.size).toArray ∧ Unimodal out at hu
  exact ⟨out, hu.1, hu.2, (by simp)⟩

/-- The remaining, purely grid/path lemma.  A horizontal edge records the
(i+1)-st left choice at value `a[i]`; a vertical edge records the (n-i)-th
right choice. Compatible edges are exactly the fixed entries of some monotone
choice of left versus right values.  The second clause is deliberately `≤`:
a completion of a partial path may incidentally fix additional entries. -/
theorem mr_chains_fixed {a : Array Nat} (ha0 : a ≠ #[])
    (hp : a.Perm (1...=a.size).toArray) :
    ( (∀ x : Array Nat, x.Perm (1...=a.size).toArray → Unimodal x →
          ∃ c : List (Nat × Nat), MRChain a c ∧ MRKeep a x = c.length) ∧
      (∀ c : List (Nat × Nat), MRChain a c →
          ∃ x : Array Nat, x.Perm (1...=a.size).toArray ∧ Unimodal x ∧
             c.length ≤ MRKeep a x)) := by
  constructor
  · -- converting the number of fixed positions of an arbitrary word is the remaining direction
    intro x hx hu
    classical
    rcases mr_unimodal_word (n:=a.size) hx hu with ⟨b, bl, xe⟩
    have xs : x.size = a.size := by simpa using hx.size_eq
    have hpx : x.Perm (1...=x.size).toArray := by
      simpa [xs] using hx
    let ix : Nat → Nat := fun k =>
       if b.getD k false then MRBefore b k
       else a.size - 1 - (k - MRBefore b k)
    let g : List Nat := (List.range a.size).filter
       (fun k => decide (a.getD (ix k) 0 = k+1))
    let c : List (Nat × Nat) := g.map (MREdge a.size b)
    have gb : ∀ k ∈ g, k < a.size := by
      intro k hk
      have h := (List.mem_filter.1 hk).1
      exact (List.mem_range.1 h)
    have gok : ∀ k ∈ g, a.getD (ix k) 0 = k+1 := by
      intro k hk
      exact of_decide_eq_true (List.mem_filter.1 hk).2
    have ibound : ∀ {k : Nat}, k < a.size → ix k < a.size := by
      intro k hk
      have lb := mr_before_le b k
      dsimp [ix]
      by_cases q : b.getD k false
      · rw [if_pos q]
        omega
      · have q' : b.getD k false = false := by
          cases h:b.getD k false <;> simp_all
        rw [if_neg q]
        omega
    -- the word writes value `k+1` at precisely this address
    have xval : ∀ {k : Nat}, (hk : k < a.size) →
        x.getD (ix k) 0 = k+1 := by
      intro k hk
      have wh := mr_word_fixed (a:=a) b bl hk
      have wh' : x[ix k]? = some (k+1) := by
        simpa [ix, xe] using wh
      have ii : ix k < a.size := ibound hk
      have iix : ix k < x.size := by simpa [xs] using ii
      rw [Array.getElem?_eq_getElem iix] at wh'
      have ev : x[ix k]'iix = k+1 := Option.some.inj wh'
      exact (mr_getD_in iix).trans ev
    have hc0 : MRChain a c := by
      have hh := mr_word_chain (a:=a) (b:=b) bl
      simpa [ix, g, c] using hh
    refine ⟨c, hc0, ?_⟩
    -- compare the correct positions with the chronological value steps.
    let faddr : {k // k ∈ g} → Fin a.size := fun k =>
      ⟨ix k.1, ibound (gb k.1 k.2)⟩
    let inds : List (Fin a.size) := g.attach.map faddr
    let keep : List (Fin a.size) :=
      (List.finRange a.size).filter
        (fun i => decide (a[i] = x.getD i.val 0))
    have gn : g.Nodup := by
      dsimp [g]
      exact (List.nodup_range).filter _
    -- distinct values of the word have distinct addresses, since there is
    -- only one value of `x` at an address.
    have indn : inds.Nodup := by
      dsimp [inds]
      apply (List.nodup_attach.2 gn).map_on
      intro u hu v hv eqf
      apply Subtype.ext
      have ee : ix u.1 = ix v.1 := congrArg Fin.val eqf
      have uval := xval (gb u.1 u.2)
      have vval := xval (gb v.1 v.2)
      rw [ee] at uval
      omega
    have kn : keep.Nodup := by
      dsimp [keep]
      exact (List.nodup_finRange _).filter _
    have sub₁ : inds ⊆ keep := by
      intro z hz
      change z ∈ g.attach.map faddr at hz
      rcases List.mem_map.1 hz with ⟨u,hu,ez⟩
      subst z
      apply List.mem_filter.2
      constructor
      · exact List.mem_finRange _
      · apply decide_eq_true
        have ak := gok u.1 u.2
        have xv := xval (gb u.1 u.2)
        have ai : ix u.1 < a.size := ibound (gb u.1 u.2)
        -- on this address the old and the new arrays both read `u+1`
        simpa [faddr, mr_getD_in ai] using ak.trans xv.symm
    have sub₂ : keep ⊆ inds := by
      intro z hz
      have hz' : z ∈ (List.finRange a.size).filter
          (fun i => decide (a[i] = x.getD i.val 0)) := by
        simpa [keep] using hz
      have fixz : a[z.val] = x.getD z.val 0 :=
        of_decide_eq_true (List.mem_filter.1 hz').2
      let i : Nat := z.val
      have ia : i < a.size := z.isLt
      have iix : i < x.size := by simpa [xs] using ia
      have vl : 1 ≤ x.getD i 0 := by
        have hbd := (mr_perm_entry_bounds hpx i iix).1
        simpa [mr_getD_in iix] using hbd
      have vu : x.getD i 0 ≤ a.size := by
        have hbd := (mr_perm_entry_bounds hpx i iix).2
        simpa [xs, mr_getD_in iix] using hbd
      let k : Nat := x.getD i 0 - 1
      have kval : k + 1 = x.getD i 0 := by
        dsimp [k]
        omega
      have kb : k < a.size := by
        dsimp [k]
        omega
      have sameD : x.getD (ix k) 0 = x.getD i 0 := by
        have h := xval kb
        omega
      have ixold : ix k < a.size := ibound kb
      have ixx : ix k < x.size := by simpa [xs] using ixold
      have indeq : ix k = i := by
        have ee : x[ix k]'ixx = x[i]'iix := by
          simpa [mr_getD_in ixx, mr_getD_in iix] using sameD
        exact mr_perm_injective hpx ixx iix ee
      have kvalold : a.getD (ix k) 0 = k+1 := by
        calc
          a.getD (ix k) 0 = a.getD i 0 := by rw [indeq]
          _ = a[i] := mr_getD_in ia
          _ = x.getD i 0 := by simpa [i] using fixz
          _ = k+1 := kval.symm
      have km : k ∈ g := by
        apply (List.mem_filter).2
        refine ⟨(List.mem_range.2 kb), ?_⟩
        exact decide_eq_true kvalold
      change z ∈ g.attach.map faddr
      apply (List.mem_map).2
      let uk : {k // k ∈ g} := ⟨k, km⟩
      refine ⟨uk, ?_, ?_⟩
      · simp [uk]
      · apply Fin.ext
        change ix k = z.val
        simpa [i] using indeq
    have len₁ : inds.length ≤ keep.length :=
      (List.subperm_of_subset indn sub₁).length_le
    have len₂ : keep.length ≤ inds.length :=
      (List.subperm_of_subset kn sub₂).length_le
    have eqlen : keep.length = inds.length := Nat.le_antisymm len₂ len₁
    have ilen : inds.length = g.length := by simp [inds]
    have clen : c.length = g.length := by simp [c]
    have hkc : keep.length = c.length := by omega
    unfold MRKeep
    simpa [keep] using hkc
  · intro c hc
    exact mr_chain_complete hp hc


end LeanEval.ProgramVerification

/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem minRearrange_correct {arr : Array Nat} :
    arr.Perm (1...=arr.size).toArray →
      (∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray), Unimodal x ∧ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector = minRearrange arr) ∧
      (∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray), Unimodal x → minRearrange arr ≤ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector) :=
/-ResultProofBegin-/by
  intro harr
  by_cases hz : arr = #[]
  · subst arr
    -- a single (empty) witness, and every permutation of the empty range is it
    have hr : (1...=(#[] : Array Nat).size).toArray = (#[] : Array Nat) := by
      simpa using LeanEval.ProgramVerification.mr_range_zero
    have he : minRearrange (#[] : Array Nat) = 0 :=
      LeanEval.ProgramVerification.mr_min_empty
    constructor
    · refine ⟨#[], ?_, ?_, ?_⟩
      · -- permutation of the empty range
        rw [hr]
      · exact ⟨#[], #[], (by decide), (by decide), (by decide)⟩
      · -- there are no indices
        change differences (Vector.mk #[] _) _ = _
        simpa [differences] using he.symm
    · intro x hx hu
      have hxs : x.size = 0 := by
        have := hx.size_eq
        -- the range is empty
        simpa [hr] using this
      have hxe : x = #[] := Array.eq_empty_of_size_eq_zero hxs
      subst x
      simp [he]
  · -- In the nonempty case all sorting/`lis` details have been removed;
    -- we reason with chains of mid-edges in the n by n choice grid.
    have hgrid := LeanEval.ProgramVerification.mr_chains_fixed hz harr
    have hmax := LeanEval.ProgramVerification.mr_lis_chains harr
    have heq := LeanEval.ProgramVerification.mr_min_points arr
    let L : Nat := minRearrange.lis (LeanEval.ProgramVerification.MRPointY arr)
    have hupper : ∀ x : Array Nat,
        x.Perm (1...=arr.size).toArray → Unimodal x →
        LeanEval.ProgramVerification.MRKeep arr x ≤ L := by
      intro x hx hu
      rcases hgrid.1 x hx hu with ⟨c,hc,hlen⟩
      have hb := hmax.2 c hc
      dsimp [L]
      omega
    rcases hmax.1 with ⟨c,hc,cl⟩
    rcases hgrid.2 c hc with ⟨x,hx,xu,xkeep⟩
    have xall : LeanEval.ProgramVerification.MRKeep arr x ≤ L :=
      hupper x hx xu
    have xe : LeanEval.ProgramVerification.MRKeep arr x = L := by
      dsimp [L] at *
      omega
    have xs : x.size = arr.size := by simpa using hx.size_eq
    constructor
    · refine ⟨x,hx,xu, ?_⟩
      have hdiff := LeanEval.ProgramVerification.mr_keep_diff xs
      -- the program value is n minus the common optimum
      rw [hdiff, xe, heq]
    · intro y hy yu
      have ys : y.size = arr.size := by simpa using hy.size_eq
      have yb := hupper y hy yu
      have yd := LeanEval.ProgramVerification.mr_keep_diff ys
      rw [yd, heq]
      omega

/-ResultProofEnd-/
/-ResultEnd-/

end Submission
