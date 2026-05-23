import Mathlib
import Submission.LisSound

/-!
# Patience sorting completeness

Shows there exists a non-decreasing subsequence of length `lis arr`.
-/

namespace Submission.LisComplete

open Submission.LisSound

/-- The NDS-existence invariant. -/
def NdsInv (arr dp : Array Nat) (ans i : Nat) : Prop :=
  dp.size = arr.size ∧
  ∀ k, k < ans → k < dp.size →
    ∃ nds : List Nat,
      nds.length = k + 1 ∧
      nds.Pairwise (· < ·) ∧
      (∀ j ∈ nds, j < i) ∧
      (∀ j ∈ nds, j < arr.size) ∧
      nds.Pairwise (fun a b => arr[a]! ≤ arr[b]!) ∧
      arr[nds[k]!]! ≤ dp[k]!

lemma ndsInv_init (arr : Array Nat) (sentinel : Nat) :
    NdsInv arr (Array.replicate arr.size sentinel) 0 0 := by
  exact ⟨by simp, fun k hk => absurd hk (by omega)⟩

lemma ndsInv_step (arr dp : Array Nat) (ans i pos : Nat)
    (hi : i < arr.size) (hinv : NdsInv arr dp ans i)
    (hpos_le : pos ≤ ans) (hpos_lt : pos < dp.size)
    (hub_le : ∀ j, j < pos → j < dp.size → dp[j]! ≤ arr[i]!) :
    NdsInv arr (dp.set! pos arr[i])
      (max ans (pos + 1)) (i + 1) := by
  refine' ⟨ _, fun k hk₁ hk₂ => _ ⟩;
  · exact hinv.1 ▸ by simp +decide [ Array.size_set! ] ;
  · by_cases hk : k = pos;
    · rcases pos with ( _ | pos ) <;> simp_all +decide;
      · use [i]; simp [hi];
      · obtain ⟨ nds, hnds₁, hnds₂, hnds₃, hnds₄, hnds₅, hnds₆ ⟩ := hinv.2 pos hpos_le ( by linarith );
        refine' ⟨ nds ++ [ i ], _, _, _, _, _, _ ⟩ <;> simp_all +decide [ List.pairwise_append ];
        · rintro j ( hj | rfl ) <;> [ exact le_of_lt ( hnds₃ _ hj ) ; exact le_rfl ];
        · rintro j ( hj | rfl ) <;> [ exact hnds₄ _ hj; exact hi ];
        · intro j hj; have := List.pairwise_iff_get.mp hnds₅; simp_all +decide [ List.get ] ;
          have := List.mem_iff_get.mp hj; obtain ⟨ k, hk ⟩ := this; simp_all +decide [ Fin.add_def, Nat.mod_eq_of_lt ] ;
          by_cases hk_pos : k.val < pos;
          · exact hk ▸ this ⟨ k, by linarith [ Fin.is_lt k ] ⟩ ⟨ pos, by linarith [ Fin.is_lt k ] ⟩ hk_pos |> le_trans <| hnds₆.trans <| by simpa [ Array.getElem?_eq_getElem, show pos < dp.size from by linarith ] using hub_le pos le_rfl ( by linarith ) ;
          · grind;
    · have := hinv.2 k ( by omega ) ( by
        rw [ Array.size_set! ] at hk₂ ; aesop );
      grind

/-
When ans ≤ dp.size, NdsInv implies ans ≤ i
-/
lemma ndsInv_ans_le (arr dp : Array Nat) (ans i : Nat)
    (hinv : NdsInv arr dp ans i) (hans : ans ≤ dp.size) : ans ≤ i := by
  contrapose! hinv;
  unfold NdsInv;
  simp +zetaDelta at *;
  intro h;
  use i;
  refine' ⟨ hinv, by linarith, _ ⟩;
  intro x hx₁ hx₂ hx₃ hx₄ hx₅; have := List.toFinset_card_of_nodup ( List.Pairwise.nodup hx₂ ) ; simp_all +decide ; simp_all +decide ;
  exact absurd this ( by exact ne_of_lt ( lt_of_le_of_lt ( Finset.card_le_card ( show x.toFinset ⊆ Finset.range i from fun x hx => Finset.mem_range.mpr ( hx₃ x ( List.mem_toFinset.mp hx ) ) ) ) ( by simp +arith +decide ) ) )

/-- Combined loop state predicate. -/
def LoopState (arr dp : Array Nat) (ans i : Nat) : Prop :=
  NdsInv arr dp ans i ∧
  (∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]!) ∧
  ans ≤ dp.size ∧
  (∀ k, ans ≤ k → k < dp.size → ∀ j, j < arr.size → arr[j]! < dp[k]!)

/-
Single step: LoopState is maintained through one iteration
-/
lemma loopState_step (arr : Array Nat) (ans i : Nat) (dp : Array Nat)
    (hi : i < arr.size) (hstate : LoopState arr dp ans i) :
    LoopState arr (dp.set! (upperBound arr[i] dp) arr[i])
      (max ans (upperBound arr[i] dp + 1)) (i + 1) := by
  have hinv : NdsInv arr dp ans i := hstate.left
  have hsorted : ∀ a b, a < b → b < dp.size → dp[a]! ≤ dp[b]! := hstate.right.left
  have hans : ans ≤ dp.size := hstate.right.right.left
  have hsentinel : ∀ k, ans ≤ k → k < dp.size → ∀ j, j < arr.size → arr[j]! < dp[k]! := hstate.right.right.right;
  have hpos_le : upperBound arr[i] dp ≤ ans := by
    contrapose! hsentinel;
    use upperBound arr[i] dp - 1;
    refine' ⟨ Nat.le_sub_one_of_lt hsentinel, _, _ ⟩;
    · exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hsentinel ) ) ( upperBound_le _ _ );
    · have := upperBound_spec_left arr[i] dp hsorted ( upperBound arr[i] dp - 1 ) ( Nat.sub_lt ( by linarith ) zero_lt_one ) ( by
        exact lt_of_lt_of_le ( Nat.pred_lt ( ne_bot_of_gt hsentinel ) ) ( upperBound_le _ _ ) ) ; aesop;
  have hpos_lt : upperBound arr[i] dp < dp.size := by
    refine' lt_of_le_of_lt hpos_le _;
    refine' lt_of_le_of_ne hans _;
    intro h; have := hinv.1; simp_all +decide ;
    exact absurd ( ndsInv_ans_le arr dp arr.size i hinv ( by linarith ) ) ( by linarith );
  have hsentinel' : ∀ k, max ans (upperBound arr[i] dp + 1) ≤ k → k < (dp.set! (upperBound arr[i] dp) arr[i]).size → ∀ j, j < arr.size → arr[j]! < (dp.set! (upperBound arr[i] dp) arr[i])[k]! := by
    simp_all +decide [ Array.set! ];
    grind;
  refine' ⟨ _, _, _, hsentinel' ⟩;
  · grind +suggestions;
  · convert step_dp_sorted hsorted using 1;
  · grind

/-
LoopState is maintained through lisLoopFull.
-/
lemma lisLoopFull_maintains_state (arr : Array Nat) (ans i : Nat) (dp : Array Nat)
    (hi : i ≤ arr.size) (hstate : LoopState arr dp ans i) :
    LoopState arr (lisLoopFull arr ans i dp hi).2
      (lisLoopFull arr ans i dp hi).1 arr.size := by
  induction' n : arr.size - i using Nat.strong_induction_on with n ih generalizing i ans dp;
  unfold lisLoopFull;
  split_ifs <;> simp_all +decide [ Nat.sub_succ ];
  convert ih _ _ _ _ _ _ ( loopState_step _ _ _ _ _ hstate ) rfl using 1;
  omega

/-
There exists a non-decreasing subsequence of length `lis arr`.
-/
theorem lis_le_exists_nds (arr : Array Nat) :
    ∃ indices : List Nat,
      indices.Pairwise (· < ·) ∧
      (∀ i ∈ indices, i < arr.size) ∧
      indices.Pairwise (fun i j => arr[i]! ≤ arr[j]!) ∧
      indices.length = lis arr := by
  have h_init_state : LoopState arr (Array.replicate arr.size (arr.foldl Nat.max 0 + 1)) 0 0 := by
    constructor;
    · exact ndsInv_init arr _;
    · refine' ⟨ _, _, _ ⟩ <;> norm_num;
      · grind +splitIndPred;
      · -- Since the sentinel value is greater than any element in the array, we have `arr[j]! < sentinel` for all `j`.
        have h_sentinel : ∀ j < arr.size, arr[j]! < arr.foldl Nat.max 0 + 1 := by
          have h_max : ∀ (l : List ℕ), ∀ (x : ℕ), x ∈ l → x ≤ List.foldl Nat.max 0 l := by
            intro l x hx; induction' l using List.reverseRecOn with l IH <;> aesop;
          cases arr ; aesop;
        grind;
  have h_final_state : LoopState arr (lisLoopFull arr 0 0 (Array.replicate arr.size (arr.foldl Nat.max 0 + 1)) (by omega)).2 (lis arr) arr.size := by
    have h_final_state : LoopState arr (lisLoopFull arr 0 0 (Array.replicate arr.size (arr.foldl Nat.max 0 + 1)) (by omega)).2 (lisLoopFull arr 0 0 (Array.replicate arr.size (arr.foldl Nat.max 0 + 1)) (by omega)).1 arr.size := by
      apply lisLoopFull_maintains_state;
      assumption;
    convert h_final_state;
    unfold lis;
    grind +suggestions;
  rcases h : lis arr with ( _ | k ) <;> simp_all +decide [ LoopState ];
  have := h_final_state.1.2 k ( by linarith ) ( by linarith [ h_final_state.1.1 ] );
  grind

end Submission.LisComplete