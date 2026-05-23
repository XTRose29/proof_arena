import Mathlib

/-!
# Patience sorting soundness

The patience sorting algorithm `lis` gives an upper bound
on the length of any non-decreasing subsequence.
-/

namespace Submission.LisSound

/-- Binary search for upper bound -/
def go (needle : Nat) (arr : Array Nat) (lo hi : Nat) (hhi : hi ≤ arr.size := by omega) : Nat :=
  if h : lo < hi then
    let mid := lo + (hi - lo) / 2
    if arr[mid] ≤ needle then
      go needle arr (mid + 1) hi
    else
      go needle arr lo mid
  else lo
termination_by hi - lo

def upperBound (needle : Nat) (arr : Array Nat) : Nat :=
  go needle arr 0 arr.size

def lisLoop (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) : Nat :=
  if hi' : i = arr.size then
    ans
  else
    let pos := upperBound arr[i] dp
    lisLoop arr (max ans (pos + 1)) (i + 1) (dp.set! pos (arr[i])) (by omega)
termination_by arr.size - i

def lis (arr : Array Nat) : Nat :=
  if h : arr.size = 0 then
    0
  else
    let sentinel := arr.foldl Nat.max 0 + 1
    let dp := Array.replicate arr.size sentinel
    lisLoop arr 0 0 dp (by omega)

/-- Extended lisLoop returning final dp state -/
def lisLoopFull (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) :
    Nat × Array Nat :=
  if hi' : i = arr.size then (ans, dp)
  else
    let pos := upperBound arr[i] dp
    lisLoopFull arr (max ans (pos + 1)) (i + 1) (dp.set! pos (arr[i])) (by omega)
termination_by arr.size - i

lemma lisLoop_eq_fst (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) :
    lisLoop arr ans i dp hi = (lisLoopFull arr ans i dp hi).1 := by
  induction' h : arr.size - i with k ih generalizing ans i dp;
  · unfold lisLoop lisLoopFull;
    grind;
  · unfold lisLoop lisLoopFull;
    grind

lemma go_bounds (needle : Nat) (arr : Array Nat) (lo hi : Nat) (hhi : hi ≤ arr.size)
    (hlo : lo ≤ hi) :
    lo ≤ go needle arr lo hi hhi ∧ go needle arr lo hi hhi ≤ hi := by
  have h_go_upper : ∀ (lo hi : ℕ) (hhi : hi ≤ arr.size) (hlo : lo ≤ hi), go needle arr lo hi hhi ≤ hi := by
    intros lo hi hhi hlo; induction' h : hi - lo using Nat.strong_induction_on with k ih generalizing lo hi; unfold go; split_ifs <;> simp_all +decide ;
    split_ifs <;> [ exact ih _ ( by omega ) _ _ _ ( by omega ) rfl; exact ih _ ( by omega ) _ _ _ ( by omega ) rfl ];
    exact le_trans ( ih _ ( by omega ) _ _ ( by omega ) ( by omega ) rfl ) ( by omega );
  have h_go_lower : ∀ (lo hi : ℕ) (hhi : hi ≤ arr.size) (hlo : lo ≤ hi), lo ≤ go needle arr lo hi hhi := by
    intros lo hi hhi hlo; induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi; unfold go; split_ifs <;> simp_all +decide ;
    split_ifs <;> [ exact le_trans ( by omega ) ( ih _ ( by omega ) _ _ _ ( by omega ) rfl ) ; exact le_trans ( by omega ) ( ih _ ( by omega ) _ _ _ ( by omega ) rfl ) ]
  exact ⟨h_go_lower lo hi hhi hlo, h_go_upper lo hi hhi hlo⟩

lemma upperBound_le (needle : Nat) (arr : Array Nat) :
    upperBound needle arr ≤ arr.size := by
  exact go_bounds needle arr 0 _ ( by simp +decide ) ( by simp +decide ) |>.2

/-
For sorted arrays, all values before go result are ≤ needle
-/
lemma go_spec_left (needle : Nat) (arr : Array Nat) (lo hi : Nat) (hhi : hi ≤ arr.size)
    (hlo : lo ≤ hi)
    (hsorted : ∀ a b, lo ≤ a → a < b → b < hi → arr[a]! ≤ arr[b]!)
    (j : Nat) (hj_lo : lo ≤ j) (hj_go : j < go needle arr lo hi hhi) (hjb : j < arr.size) :
    arr[j]! ≤ needle := by
  contrapose! hj_go;
  induction' h : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi;
  unfold go;
  split_ifs <;> simp_all +decide [ Nat.sub_eq_iff_eq_add' hlo ];
  split_ifs;
  · convert ih ( n - ( n / 2 + 1 ) ) _ ( lo + n / 2 + 1 ) ( lo + n ) _ _ _ _ _ using 1;
    · omega;
    · omega;
    · exact fun a b ha hb hab => hsorted a b ( by omega ) ( by omega ) ( by omega );
    · by_cases h_cases : j < lo + n / 2;
      · grind;
      · grind;
    · omega;
  · apply ih (n / 2) (by
    omega) lo (lo + n / 2) (by
    omega) (by
    exact Nat.le_add_right _ _) (by
    exact fun a b ha hb hb' => hsorted a b ha hb ( by omega )) hj_lo (by
    rw [ Nat.add_sub_cancel_left ])

lemma upperBound_spec_left (needle : Nat) (dp : Array Nat)
    (hsorted : ∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]!)
    (j : Nat) (hj : j < upperBound needle dp) (hjb : j < dp.size) :
    dp[j]! ≤ needle := by
  apply go_spec_left needle dp 0 dp.size (by simp) (by simp) (by
  exact fun a b ha hb hb' => hsorted a b hb hb') j (by
  exact Nat.zero_le _) hj hjb

/-
go returns ≥ p when all dp values in [lo, p) are ≤ needle
-/
lemma go_lower_bound (needle : Nat) (arr : Array Nat) (lo hi p : Nat)
    (hhi : hi ≤ arr.size) (hlo : lo ≤ p) (hp : p ≤ hi)
    (h_below : ∀ k, lo ≤ k → k < p → arr[k]! ≤ needle) :
    p ≤ go needle arr lo hi hhi := by
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi;
  unfold go; split_ifs <;> norm_num at *;
  · split_ifs;
    · contrapose! ih;
      refine' ⟨ _, _, lo + ( hi - lo ) / 2 + 1, hi, hhi, _, _, _, rfl, ih ⟩ <;> try omega;
      · exact Nat.succ_le_of_lt ( lt_of_not_ge fun h => by have := go_bounds needle arr ( lo + ( hi - lo ) / 2 + 1 ) hi hhi ( by omega ) ; omega );
      · grind;
    · apply ih (lo + (hi - lo) / 2 - lo);
      · omega;
      · linarith;
      · grind;
      · assumption;
      · rfl;
  · linarith

lemma upperBound_ge (needle : Nat) (dp : Array Nat) (p : Nat) (hp : p ≤ dp.size)
    (h_below : ∀ k, k < p → dp[k]! ≤ needle) :
    p ≤ upperBound needle dp := by
  convert go_lower_bound needle dp 0 dp.size p _ _ _ using 1;
  exact ⟨ fun h => fun _ => h, fun h => h fun k _ hk => h_below k hk ⟩;
  · linarith;
  · exact Nat.zero_le _;
  · linarith

/-
For sorted arrays, the position returned by go has arr value > needle
-/
lemma go_spec_right (needle : Nat) (arr : Array Nat) (lo hi : Nat)
    (hhi : hi ≤ arr.size) (hlo : lo ≤ hi)
    (hsorted : ∀ a b, lo ≤ a → a < b → b < hi → arr[a]! ≤ arr[b]!)
    (h_pos : go needle arr lo hi hhi < hi) :
    needle < arr[go needle arr lo hi hhi]! := by
  revert needle arr;
  induction' n : hi - lo using Nat.strong_induction_on with n ih generalizing lo hi;
  unfold go;
  grind

lemma upperBound_spec_right (needle : Nat) (dp : Array Nat)
    (hsorted : ∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]!)
    (h_pos : upperBound needle dp < dp.size) :
    needle < dp[upperBound needle dp]! := by
  apply_rules [ go_spec_right ];
  · grobner;
  · exact fun a b _ hab h => hsorted a b hab h

/-
Filter helper: i ∉ indices means filter (· < i+1) = filter (· < i)
-/
lemma filter_lt_succ_not_mem {l : List Nat} {i : Nat}
    (_h_sorted : l.Pairwise (· < ·)) (h_not_mem : i ∉ l) :
    l.filter (· < i + 1) = l.filter (· < i) := by
  refine' List.filter_congr fun x hx => _;
  grind

/-
Filter helper: i ∈ indices means filter (· < i+1) = filter (· < i) ++ [i]
-/
lemma filter_lt_succ_mem {l : List Nat} {i : Nat}
    (h_sorted : l.Pairwise (· < ·)) (h_mem : i ∈ l) :
    l.filter (· < i + 1) = l.filter (· < i) ++ [i] := by
  have h_filter : ∀ {l : List ℕ}, List.Pairwise (· < ·) l → ∀ i, i ∈ l → List.filter (fun x => x < i + 1) l = List.filter (fun x => x < i) l ++ [i] := by
    intros l h_sorted i h_mem;
    induction' l with hd tl ih generalizing i;
    · decide +revert;
    · by_cases h : i = hd <;> simp_all +decide [ List.filter_cons ];
      · induction tl <;> simp_all +decide [ List.filter_cons ];
        grind;
      · exact le_of_lt ( h_sorted.1 i h_mem );
  exact h_filter h_sorted i h_mem

/-
Filter of all elements smaller than bound = identity when all elements < bound
-/
lemma filter_lt_of_all_lt {l : List Nat} {n : Nat}
    (h_bound : ∀ j ∈ l, j < n) :
    l.filter (· < n) = l := by
  exact List.filter_eq_self.mpr fun x hx => by simpa using h_bound x hx;

/-
Setting dp at upperBound position preserves sortedness
-/
lemma step_dp_sorted {dp : Array Nat} {needle : Nat}
    (h_dp_sorted : ∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]!) :
    ∀ a b, a < b → b < (dp.set! (upperBound needle dp) needle).size →
      (dp.set! (upperBound needle dp) needle)[a]! ≤
      (dp.set! (upperBound needle dp) needle)[b]! := by
  intro a b hab
  by_cases hpos : upperBound needle dp = a ∨ upperBound needle dp = b;
  · cases hpos <;> simp_all +decide [ Array.set! ];
    · intro hb
      have h_pos : needle ≤ dp[b] := by
        nontriviality;
        have h_pos : needle < dp[upperBound needle dp]! := by
          apply upperBound_spec_right needle dp (fun a b hab h => by
            grind +qlia) (by
          linarith [ upperBound_le needle dp ])
        generalize_proofs at *;
        grind
      generalize_proofs at *;
      grind;
    · intro hb
      have h_a_lt_b : a < upperBound needle dp := by
        grind;
      have h_a_lt_b : dp[a]! ≤ needle := by
        apply upperBound_spec_left;
        · aesop;
        · assumption;
        · grind;
      grind +splitIndPred;
  · grind

/-
lisLoop result is ≥ ans
-/
lemma lisLoop_ge_ans (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) :
    ans ≤ lisLoop arr ans i dp hi := by
  induction' n : arr.size - i using Nat.strong_induction_on with n ih generalizing i ans dp;
  unfold lisLoop;
  grind

/-
lisLoopFull preserves dp.size
-/
lemma lisLoopFull_size (arr : Array Nat) (ans i : Nat) (dp : Array Nat) (hi : i ≤ arr.size) :
    (lisLoopFull arr ans i dp hi).2.size = dp.size := by
  -- By definition of `lisLoopFull`, the size of the resulting array is preserved.
  have h_size_preserved : ∀ (ans i : ℕ) (dp : Array ℕ) (hi : i ≤ arr.size), (lisLoopFull arr ans i dp hi).2.size = dp.size := by
    intros ans i dp hi;
    induction' n : arr.size - i using Nat.strong_induction_on with n ih generalizing i ans dp;
    unfold lisLoopFull;
    grind;
  exact h_size_preserved ans i dp hi

/-
Elements in filter (· < i) are in indices and satisfy R with i
-/
lemma pairwise_filter_lt_val {l : List Nat} {i : Nat} {R : Nat → Nat → Prop}
    (h_sorted : l.Pairwise (· < ·))
    (h_pw : l.Pairwise R)
    (h_mem : i ∈ l)
    (j : Nat) (hj : j ∈ l.filter (· < i)) :
    R j i := by
  rw [ List.mem_filter ] at hj;
  obtain ⟨idxI, rfl⟩ := List.mem_iff_get.mp h_mem
  obtain ⟨idxJ, rfl⟩ := List.mem_iff_get.mp hj.1
  have hval : l.get idxJ < l.get idxI := of_decide_eq_true hj.2
  have hidx : idxJ < idxI := by
    by_contra hnot
    have hle : idxI ≤ idxJ := le_of_not_gt hnot
    obtain rfl | hlt := eq_or_lt_of_le hle
    · omega
    · have hsorted_val := h_sorted.rel_get_of_lt hlt
      omega
  exact h_pw.rel_get_of_lt hidx

/-
Step: dp tracking when i ∉ indices
-/
lemma step_dp_track_not_mem {arr dp : Array Nat} {i : Nat}
    {indices : List Nat}
    (h_sorted : indices.Pairwise (· < ·))
    (h_not_mem : i ∉ indices)
    (h_dp_sorted : ∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]!)
    (h_dp_size : dp.size = arr.size)
    (_hi_lt : i < arr.size)
    (processed : Nat)
    (h_proc_def : processed = (indices.filter (· < i)).length)
    (h_dp_track : ∀ k, k < processed →
      dp[k]! ≤ arr[(indices.filter (· < i))[k]!]!) :
    let pos := upperBound (arr[i]!) dp
    let dp' := dp.set! pos (arr[i]!)
    ∀ k, k < (indices.filter (· < i + 1)).length →
      dp'[k]! ≤ arr[(indices.filter (· < i + 1))[k]!]! := by
  -- Since i ∉ indices, by filter_lt_succ_not_mem, filter (· < i+1) = filter (· < i).
  have h_filter_eq : List.filter (· < i + 1) indices = List.filter (· < i) indices := by
    exact filter_lt_succ_not_mem h_sorted h_not_mem;
  by_cases h : upperBound arr[i]! dp < processed <;> simp_all +decide;
  · intro k hk; by_cases hk' : k = upperBound arr[i] dp <;> simp_all +decide [ Array.setIfInBounds ] ;
    · split_ifs <;> simp_all +decide [ Array.set ];
      have := upperBound_spec_right arr[i] dp ( by
        grind ) ( by
        lia );
      grind;
    · grind;
  · grind

/-
Step: dp tracking when i ∈ indices
-/
lemma step_dp_track_mem {arr dp : Array Nat} {i : Nat}
    {indices : List Nat}
    (h_sorted : indices.Pairwise (· < ·))
    (h_mem : i ∈ indices)
    (h_nondec : indices.Pairwise (fun a b => arr[a]! ≤ arr[b]!))
    (h_dp_sorted : ∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]!)
    (h_dp_size : dp.size = arr.size)
    (_hi_lt : i < arr.size)
    (h_bound : ∀ j ∈ indices, j < arr.size)
    (processed : Nat)
    (h_proc_def : processed = (indices.filter (· < i)).length)
    (h_dp_track : ∀ k, k < processed →
      dp[k]! ≤ arr[(indices.filter (· < i))[k]!]!) :
    let pos := upperBound (arr[i]!) dp
    let dp' := dp.set! pos (arr[i]!)
    ∀ k, k < (indices.filter (· < i + 1)).length →
      dp'[k]! ≤ arr[(indices.filter (· < i + 1))[k]!]! := by
  intro pos dp' hk_lt;
  by_cases hk : hk_lt < processed;
  · -- Since `hk_lt < processed`, we have `dp'[hk_lt]! = dp[hk_lt]!`.
    have h_eq : dp'[hk_lt]! = dp[hk_lt]! := by
      have h_eq : pos ≥ processed := by
        apply upperBound_ge;
        · have h_filter_length : (List.filter (fun x => x < i) indices).length ≤ indices.length := by
            exact List.length_filter_le _ _;
          have h_filter_length : indices.length ≤ arr.size := by
            have h_filter_length : indices.toFinset.card ≤ arr.size := by
              exact le_trans ( Finset.card_le_card ( show indices.toFinset ⊆ Finset.range arr.size from fun x hx => Finset.mem_range.mpr ( h_bound x ( List.mem_toFinset.mp hx ) ) ) ) ( by simp );
            rwa [ List.toFinset_card_of_nodup ( List.Pairwise.nodup h_sorted ) ] at h_filter_length;
          linarith;
        · have h_le : ∀ j ∈ List.filter (fun x => x < i) indices, arr[j]! ≤ arr[i]! := by
            intros j hj_mem
            have h_le : j < i := by
              rw [ List.mem_filter ] at hj_mem; aesop;
            have := List.pairwise_iff_get.mp h_nondec;
            obtain ⟨ k, hk ⟩ := List.mem_iff_get.mp ( List.mem_filter.mp hj_mem |>.1 ) ; obtain ⟨ l, hl ⟩ := List.mem_iff_get.mp h_mem; simp_all +decide ;
            have h_le : k < l := by
              have := List.pairwise_iff_get.mp h_sorted;
              exact lt_of_not_ge fun h => by linarith! [ this _ _ ( lt_of_le_of_ne h ( Ne.symm <| by aesop ) ) ] ;
            grind;
          grind;
      grind;
    rw [ filter_lt_succ_mem h_sorted h_mem ];
    grind;
  · intro hk_lt';
    rw [ show List.filter ( fun x => decide ( x < i + 1 ) ) indices = List.filter ( fun x => decide ( x < i ) ) indices ++ [ i ] from ?_ ] at hk_lt' ⊢;
    · simp_all +decide ;
      cases hk_lt'.eq_or_lt <;> first | linarith | simp_all +decide ;
      have h_pos_ge_processed : pos ≥ processed := by
        apply upperBound_ge;
        · have h_filter_length : (List.filter (fun x => x < i) indices).length ≤ List.length indices := by
            exact List.length_filter_le _ _;
          have h_filter_length : List.length indices ≤ arr.size := by
            have h_filter_length : List.toFinset indices ⊆ Finset.range arr.size := by
              exact fun x hx => Finset.mem_range.mpr ( h_bound x ( List.mem_toFinset.mp hx ) );
            have := Finset.card_le_card h_filter_length; simp_all +decide [ List.toFinset_card_of_nodup ( List.Pairwise.nodup h_sorted ) ] ;
          linarith;
        · grind +suggestions;
      cases h_pos_ge_processed.eq_or_lt <;> simp_all +decide ;
      · simp +zetaDelta at *;
        rw [ Array.setIfInBounds ] ; aesop;
      · have h_pos_ge_processed : dp[processed]! ≤ arr[i]! := by
          have h_pos_ge_processed : processed < pos := by
            linarith;
          apply upperBound_spec_left;
          · aesop;
          · assumption;
          · exact lt_of_lt_of_le h_pos_ge_processed ( upperBound_le _ _ ) |> lt_of_lt_of_le <| by simp +decide [ h_dp_size ] ;
        grind;
    · apply filter_lt_succ_mem;
      · assumption;
      · assumption;
    · grind +suggestions

/-
Step: ans update when i ∈ indices
-/
lemma step_ans_ge_mem {arr dp : Array Nat} {i : Nat}
    {indices : List Nat} {ans_init : Nat}
    (h_sorted : indices.Pairwise (· < ·))
    (h_mem : i ∈ indices)
    (h_nondec : indices.Pairwise (fun a b => arr[a]! ≤ arr[b]!))
    (_h_dp_sorted : ∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]!)
    (h_dp_size : dp.size = arr.size)
    (_hi_lt : i < arr.size)
    (h_bound : ∀ j ∈ indices, j < arr.size)
    (processed : Nat)
    (h_proc_def : processed = (indices.filter (· < i)).length)
    (h_ans_ge : processed ≤ ans_init)
    (h_dp_track : ∀ k, k < processed →
      dp[k]! ≤ arr[(indices.filter (· < i))[k]!]!) :
    (indices.filter (· < i + 1)).length ≤ max ans_init (upperBound (arr[i]!) dp + 1) := by
  have h_filter_lt_succ_mem : (List.filter (fun x => x < i + 1) indices).length = (List.filter (fun x => x < i) indices).length + 1 := by
    rw [ filter_lt_succ_mem h_sorted h_mem ] ; aesop;
  have h_upperBound_ge_processed : processed ≤ upperBound arr[i]! dp := by
    nontriviality;
    have h_upperBound_ge_processed : ∀ k < processed, dp[k]! ≤ arr[i]! := by
      intro k hk_lt_processed
      have h_filter_lt_i : (indices.filter (· < i))[k]! ∈ indices ∧ (indices.filter (· < i))[k]! < i := by
        grind;
      exact le_trans ( h_dp_track k hk_lt_processed ) ( pairwise_filter_lt_val h_sorted h_nondec h_mem _ ( by aesop ) );
    apply upperBound_ge;
    · exact h_proc_def.symm ▸ le_trans ( List.length_filter_le _ _ ) ( by simpa [ h_dp_size ] using List.toFinset_card_of_nodup ( List.Pairwise.nodup h_sorted ) ▸ Finset.card_le_card ( show indices.toFinset ⊆ Finset.range arr.size from fun x hx => Finset.mem_range.mpr ( h_bound x ( List.mem_toFinset.mp hx ) ) ) |> le_trans <| by simp +decide );
    · assumption;
  grind

/-
Core loop invariant: lisLoopFull result ≥ indices.length
-/
lemma lisLoopFull_nds_invariant (arr : Array Nat) (ans_init i : Nat) (dp : Array Nat)
    (hi : i ≤ arr.size)
    (indices : List Nat)
    (h_sorted : indices.Pairwise (· < ·))
    (h_bound : ∀ j ∈ indices, j < arr.size)
    (h_nondec : indices.Pairwise (fun a b => arr[a]! ≤ arr[b]!))
    (h_dp_size : dp.size = arr.size)
    (h_dp_sorted : ∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]!)
    (processed : Nat)
    (h_proc_def : processed = (indices.filter (· < i)).length)
    (h_ans_ge : processed ≤ ans_init)
    (h_dp_track : ∀ k, k < processed →
      dp[k]! ≤ arr[(indices.filter (· < i))[k]!]!) :
    (lisLoopFull arr ans_init i dp hi).1 ≥ indices.length := by
  induction' n : arr.size - i using Nat.strong_induction_on with n ih generalizing i ans_init dp indices processed;
  by_cases hi' : i = arr.size;
  · unfold lisLoopFull;
    nontriviality;
    rw [ List.filter_eq_self.mpr ] at h_proc_def <;> aesop;
  · by_cases hi'' : i ∈ indices;
    · -- Apply the induction hypothesis to the new indices and processed.
      have h_ind : (lisLoopFull arr (max ans_init (upperBound (arr[i]!) dp + 1)) (i + 1) (dp.set! (upperBound (arr[i]!) dp) (arr[i]!)) (by omega)).1 ≥ indices.length := by
        apply ih (arr.size - (i + 1));
        grind;
        any_goals tauto;
        · simp +decide [ h_dp_size ];
        · convert step_dp_sorted h_dp_sorted using 1;
        · convert step_ans_ge_mem h_sorted hi'' h_nondec h_dp_sorted h_dp_size ( Nat.lt_of_le_of_ne hi hi' ) h_bound processed h_proc_def h_ans_ge h_dp_track using 1;
        · convert step_dp_track_mem h_sorted hi'' h_nondec h_dp_sorted h_dp_size ( Nat.lt_of_le_of_ne hi hi' ) h_bound processed h_proc_def h_dp_track using 1;
      unfold lisLoopFull; simp +decide [ hi' ] ;
      grind;
    · unfold lisLoopFull;
      convert ih ( arr.size - ( i + 1 ) ) _ ( max ans_init ( upperBound arr[i] dp + 1 ) ) ( i + 1 ) ( dp.set! ( upperBound arr[i] dp ) arr[i] ) ( by omega ) indices h_sorted h_bound h_nondec _ _ _ _ _ _ using 1;
      lia;
      any_goals omega;
      · simp +decide [ h_dp_size ];
      · convert step_dp_sorted h_dp_sorted using 1;
      · rw [ h_proc_def, filter_lt_succ_not_mem h_sorted hi'' ];
      · convert step_dp_track_not_mem h_sorted hi'' h_dp_sorted h_dp_size ( Nat.lt_of_le_of_ne hi hi' ) processed h_proc_def h_dp_track using 1;
        grind +suggestions

/-
Patience sorting gives an upper bound on non-decreasing subsequences
-/
theorem lis_ge_nds (arr : Array Nat) (indices : List Nat)
    (h_sorted : indices.Pairwise (· < ·))
    (h_bound : ∀ i ∈ indices, i < arr.size)
    (h_nondec : indices.Pairwise (fun i j => arr[i]! ≤ arr[j]!)) :
    indices.length ≤ lis arr := by
  unfold lis;
  split_ifs <;> simp_all +decide ;
  · exact List.eq_nil_iff_forall_not_mem.mpr h_bound;
  · convert lisLoopFull_nds_invariant arr 0 0 ( Array.replicate arr.size ( Array.foldl Nat.max 0 arr + 1 ) ) ( by omega ) indices h_sorted h_bound h_nondec _ _ _ _ _ using 1;
    any_goals exact Nat.zero;
    · rw [ lisLoop_eq_fst ] ; aesop;
    · norm_num;
    · grind;
    · norm_num [ List.filter_eq ];
    · norm_num

end Submission.LisSound
