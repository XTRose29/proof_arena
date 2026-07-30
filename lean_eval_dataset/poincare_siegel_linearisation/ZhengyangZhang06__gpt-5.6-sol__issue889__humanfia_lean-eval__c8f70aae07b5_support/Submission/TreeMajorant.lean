import Submission.Helpers
import Submission.SmallDivisorTree

open Filter Finset

namespace Submission.Helpers.BinaryTree

/-- Sum of a numerical label over all internal nodes of a binary tree,
where a node is labelled by the number of leaves below it. -/
def levelSum (level : ℕ → ℕ) : BinaryTree Unit → ℕ
  | .nil => 0
  | tree@(.node _ left right) =>
      level tree.numLeaves + levelSum level left + levelSum level right

/-- Maximum of the same numerical labels. -/
def levelMax (level : ℕ → ℕ) : BinaryTree Unit → ℕ
  | .nil => 0
  | tree@(.node _ left right) =>
      max (level tree.numLeaves) (max (levelMax level left) (levelMax level right))

private theorem sum_range_indicator_lt (m N : ℕ) (hmN : m ≤ N) :
    ∑ k ∈ range N, (if k < m then 1 else 0) = m := by
  induction N generalizing m with
  | zero =>
      have : m = 0 := by omega
      subst m
      simp
  | succ N ih =>
      rw [sum_range_succ]
      by_cases hm : m ≤ N
      · rw [ih m hm]
        simp [not_lt_of_ge hm]
      · have : m = N + 1 := by omega
        subst m
        have hprev :
            ∑ k ∈ range N, (if k < N + 1 then 1 else 0) = N := by
          calc
            ∑ k ∈ range N, (if k < N + 1 then 1 else 0) =
                ∑ _k ∈ range N, 1 := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [Finset.mem_range] at hk
              simp [show k < N + 1 by omega]
            _ = N := by simp
        rw [hprev]
        simp

theorem sum_selectedNodeCount_of_levelMax_le
    (level : ℕ → ℕ) (tree : BinaryTree Unit) {N : ℕ}
    (hN : levelMax level tree ≤ N) :
    ∑ k ∈ range N, selectedNodeCount (fun n => k < level n) tree =
      levelSum level tree := by
  classical
  induction tree with
  | nil => simp [levelSum, selectedNodeCount]
  | node value left right ihleft ihrigh =>
      change
        max (level (BinaryTree.node value left right).numLeaves)
          (max (levelMax level left) (levelMax level right)) ≤ N at hN
      have hroot :
          level (BinaryTree.node value left right).numLeaves ≤ N :=
        (le_max_left _ _).trans hN
      have hleft : levelMax level left ≤ N :=
        ((le_max_left _ _).trans (le_max_right _ _)).trans hN
      have hright : levelMax level right ≤ N :=
        ((le_max_right _ _).trans (le_max_right _ _)).trans hN
      simp only [selectedNodeCount, levelSum, sum_add_distrib]
      rw [sum_range_indicator_lt _ _ hroot, ihleft hleft, ihrigh hright]

theorem sum_selectedNodeCount (level : ℕ → ℕ) (tree : BinaryTree Unit) :
    ∑ k ∈ range (levelMax level tree),
        selectedNodeCount (fun n => k < level n) tree =
      levelSum level tree :=
  sum_selectedNodeCount_of_levelMax_le level tree le_rfl

end Submission.Helpers.BinaryTree

namespace Submission

/-- The small divisor attached to an internal node with `n` leaves. -/
noncomputable def smallDivisor (lam : ℂ) (n : ℕ) : ℝ :=
  ‖lam ^ (n - 1) - 1‖

/-- The `k`-th dyadic threshold used to stratify small divisors. -/
noncomputable def dyadicThreshold (c : ℝ) (T k : ℕ) : ℝ :=
  c / (2 * ((2 : ℝ) ^ k) ^ T)

private theorem exists_dyadicThreshold_le
    {c d : ℝ} {T : ℕ} (_hc : 0 < c) (hd : 0 < d) (hT : T ≠ 0) :
    ∃ k, dyadicThreshold c T k ≤ d := by
  have hbase : 1 < (2 : ℝ) ^ T := by
    exact one_lt_pow₀ (by norm_num) hT
  obtain ⟨k, hk⟩ :=
    ((tendsto_pow_atTop_atTop_of_one_lt hbase).eventually_gt_atTop
      (c / (2 * d))).exists
  refine ⟨k, ?_⟩
  have hpow :
      ((2 : ℝ) ^ k) ^ T = ((2 : ℝ) ^ T) ^ k := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [dyadicThreshold, hpow]
  rw [div_lt_iff₀ (by positivity)] at hk
  apply le_of_lt
  apply (div_lt_iff₀ (by positivity)).2
  nlinarith

/-- First dyadic threshold lying below `d`, or zero if none exists. -/
noncomputable def firstBelow (threshold : ℕ → ℝ) (d : ℝ) : ℕ :=
  by
    classical
    exact if h : ∃ k, threshold k ≤ d then Nat.find h else 0

private theorem firstBelow_spec
    {threshold : ℕ → ℝ} {d : ℝ} (h : ∃ k, threshold k ≤ d) :
    threshold (firstBelow threshold d) ≤ d := by
  rw [firstBelow, dif_pos h]
  exact Nat.find_spec h

private theorem not_threshold_le_of_lt_firstBelow
    {threshold : ℕ → ℝ} {d : ℝ} (h : ∃ k, threshold k ≤ d)
    {k : ℕ} (hk : k < firstBelow threshold d) :
    ¬threshold k ≤ d := by
  intro hkd
  have hfind : firstBelow threshold d ≤ k := by
    rw [firstBelow, dif_pos h]
    exact Nat.find_min' h hkd
  omega

/-- Dyadic level of the small divisor attached to a subtree size. -/
noncomputable def divisorLevel (lam : ℂ) (c : ℝ) (T n : ℕ) : ℕ :=
  firstBelow (dyadicThreshold c T) (smallDivisor lam n)

private theorem divisorLevel_exists
    {lam : ℂ} {c : ℝ} {T n : ℕ}
    (hc : 0 < c) (hT : T ≠ 0)
    (hn : 2 ≤ n)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1) :
    ∃ k, dyadicThreshold c T k ≤ smallDivisor lam n := by
  apply exists_dyadicThreshold_le hc
  · rw [smallDivisor, norm_pos_iff]
    exact sub_ne_zero.mpr (hnonzero (n - 1) (by omega))
  · exact hT

private theorem smallDivisor_lt_threshold_of_lt_level
    {lam : ℂ} {c : ℝ} {T n k : ℕ}
    (hc : 0 < c) (hT : T ≠ 0)
    (hn : 2 ≤ n)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1)
    (hk : k < divisorLevel lam c T n) :
    smallDivisor lam n < dyadicThreshold c T k := by
  have hex := divisorLevel_exists hc hT hn hnonzero
  exact lt_of_not_ge
    (not_threshold_le_of_lt_firstBelow hex hk)

private theorem pow_lt_pow_from_common_dividend
    {c a b : ℝ} (hc : 0 < c) (ha : 0 < a) (hb : 0 < b)
    (h : c / a < c / b) :
    b < a := by
  rw [div_lt_div_iff₀ ha hb] at h
  exact lt_of_mul_lt_mul_left h hc.le

private theorem selected_large
    {lam : ℂ} {c : ℝ} {T k n : ℕ}
    (hc : 0 < c) (hT : T ≠ 0)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1)
    (hbound : ∀ r : ℕ, r ≠ 0 →
      c / (r : ℝ) ^ T ≤ ‖lam ^ r - 1‖)
    (hn : 2 ≤ n)
    (hk : k < divisorLevel lam c T n) :
    2 ^ k < n := by
  have hsmall :=
    smallDivisor_lt_threshold_of_lt_level hc hT hn hnonzero hk
  have hlower := hbound (n - 1) (by omega)
  have hfrac :
      c / ((n - 1 : ℕ) : ℝ) ^ T <
        c / (2 * ((2 : ℝ) ^ k) ^ T) :=
    hlower.trans_lt hsmall
  have hden :
      2 * ((2 : ℝ) ^ k) ^ T <
        ((n - 1 : ℕ) : ℝ) ^ T := by
    apply pow_lt_pow_from_common_dividend hc
    · apply pow_pos
      exact_mod_cast (show 0 < n - 1 by omega)
    · positivity
    · exact hfrac
  have hpows :
      ((2 : ℝ) ^ k) ^ T < (((n - 1 : ℕ) : ℝ)) ^ T :=
    by
      have hnonneg : 0 ≤ ((2 : ℝ) ^ k) ^ T := by positivity
      nlinarith
  have hcast :
      (2 : ℝ) ^ k < ((n - 1 : ℕ) : ℝ) :=
    lt_of_pow_lt_pow_left₀ T (by positivity) hpows
  have hnat : 2 ^ k < n - 1 := by
    exact_mod_cast hcast
  omega

private theorem norm_smallDivisor_sub_le
    {lam : ℂ} (hlam : ‖lam‖ = 1)
    {m n : ℕ} (hm : 2 ≤ m) (hmn : m < n) :
    ‖lam ^ (n - m) - 1‖ ≤
      smallDivisor lam n + smallDivisor lam m := by
  have hexp : (m - 1) + (n - m) = n - 1 := by omega
  have hmul :
      lam ^ (m - 1) * (lam ^ (n - m) - 1) =
        (lam ^ (n - 1) - 1) - (lam ^ (m - 1) - 1) := by
    rw [mul_sub, mul_one, ← pow_add, hexp]
    ring
  calc
    ‖lam ^ (n - m) - 1‖ =
        ‖lam ^ (m - 1) * (lam ^ (n - m) - 1)‖ := by
      rw [norm_mul, norm_pow, hlam, one_pow, one_mul]
    _ = ‖(lam ^ (n - 1) - 1) - (lam ^ (m - 1) - 1)‖ := by
      rw [hmul]
    _ ≤ ‖lam ^ (n - 1) - 1‖ + ‖lam ^ (m - 1) - 1‖ :=
      norm_sub_le _ _
    _ = smallDivisor lam n + smallDivisor lam m := rfl

private theorem selected_separated
    {lam : ℂ} {c : ℝ} {T k m n : ℕ}
    (hc : 0 < c) (hT : T ≠ 0) (hlam : ‖lam‖ = 1)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1)
    (hbound : ∀ r : ℕ, r ≠ 0 →
      c / (r : ℝ) ^ T ≤ ‖lam ^ r - 1‖)
    (hm : 2 ≤ m) (hkm : k < divisorLevel lam c T m)
    (hn : 2 ≤ n) (hkn : k < divisorLevel lam c T n)
    (hmn : m < n) :
    2 ^ k < n - m := by
  have hsmall_m :=
    smallDivisor_lt_threshold_of_lt_level hc hT hm hnonzero hkm
  have hsmall_n :=
    smallDivisor_lt_threshold_of_lt_level hc hT hn hnonzero hkn
  have hnorm :=
    norm_smallDivisor_sub_le hlam hm hmn
  have hupper :
      ‖lam ^ (n - m) - 1‖ <
        c / (((2 : ℝ) ^ k) ^ T) := by
    calc
      ‖lam ^ (n - m) - 1‖
          ≤ smallDivisor lam n + smallDivisor lam m := hnorm
      _ < dyadicThreshold c T k + dyadicThreshold c T k :=
        add_lt_add hsmall_n hsmall_m
      _ = c / (((2 : ℝ) ^ k) ^ T) := by
        rw [dyadicThreshold]
        field_simp
        ring
  have hlower := hbound (n - m) (by omega)
  have hfrac :
      c / ((n - m : ℕ) : ℝ) ^ T <
        c / (((2 : ℝ) ^ k) ^ T) :=
    hlower.trans_lt hupper
  have hpows :
      ((2 : ℝ) ^ k) ^ T <
        ((n - m : ℕ) : ℝ) ^ T :=
    pow_lt_pow_from_common_dividend hc
      (pow_pos (by exact_mod_cast (show 0 < n - m by omega)) _)
      (by positivity) hfrac
  have hcast :
      (2 : ℝ) ^ k < ((n - m : ℕ) : ℝ) :=
    lt_of_pow_lt_pow_left₀ T (by positivity) hpows
  exact_mod_cast hcast

/-- The total dyadic level in a binary expansion tree is linear in its
number of leaves. This is the counting core of Siegel's estimate. -/
theorem levelSum_divisorLevel_le
    {lam : ℂ} {c : ℝ} {T : ℕ}
    (hc : 0 < c) (hT : T ≠ 0) (hlam : ‖lam‖ = 1)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1)
    (hbound : ∀ r : ℕ, r ≠ 0 →
      c / (r : ℝ) ^ T ≤ ‖lam ^ r - 1‖)
    (tree : BinaryTree Unit) :
    Helpers.BinaryTree.levelSum (divisorLevel lam c T) tree ≤
      4 * tree.numLeaves := by
  classical
  let M := Helpers.BinaryTree.levelMax (divisorLevel lam c T) tree
  have hcount (k : ℕ) :
      2 ^ k *
          Helpers.BinaryTree.selectedNodeCount
            (fun n => 2 ≤ n ∧ k < divisorLevel lam c T n) tree ≤
        2 * tree.numLeaves := by
    apply Helpers.BinaryTree.mul_selectedNodeCount_le_two_mul_numLeaves
    · positivity
    · intro n hn
      exact selected_large hc hT hnonzero hbound hn.1 hn.2
    · intro m n hm hn hmn
      exact selected_separated hc hT hlam hnonzero hbound
        hm.1 hm.2 hn.1 hn.2 hmn
  have hcount_eq (k : ℕ) :
      Helpers.BinaryTree.selectedNodeCount
          (fun n => 2 ≤ n ∧ k < divisorLevel lam c T n) tree =
        Helpers.BinaryTree.selectedNodeCount
          (fun n => k < divisorLevel lam c T n) tree := by
    clear M hcount
    induction tree with
    | nil =>
        simp [Helpers.BinaryTree.selectedNodeCount]
    | node value left right ihleft ihrigh =>
        have hle : 2 ≤ left.numLeaves + right.numLeaves := by
          have hl := left.numLeaves_pos
          have hr := right.numLeaves_pos
          omega
        simp [Helpers.BinaryTree.selectedNodeCount,
          BinaryTree.numLeaves, hle, ihleft, ihrigh]
  have hterm (k : ℕ) :
      (Helpers.BinaryTree.selectedNodeCount
          (fun n => k < divisorLevel lam c T n) tree : ℝ) ≤
        2 * tree.numLeaves * (1 / 2 : ℝ) ^ k := by
    have hk := hcount k
    rw [hcount_eq k] at hk
    have hk' :
        (2 : ℝ) ^ k *
            (Helpers.BinaryTree.selectedNodeCount
              (fun n => k < divisorLevel lam c T n) tree : ℝ) ≤
          2 * (tree.numLeaves : ℝ) := by
      exact_mod_cast hk
    have hrewrite :
        2 * (tree.numLeaves : ℝ) * (1 / 2 : ℝ) ^ k =
          (2 * (tree.numLeaves : ℝ)) / (2 : ℝ) ^ k := by
      rw [div_pow]
      field_simp
      ring
    rw [hrewrite]
    apply (le_div_iff₀ (by positivity : 0 < (2 : ℝ) ^ k)).2
    simpa [mul_comm] using hk'
  have hsum :=
    Helpers.BinaryTree.sum_selectedNodeCount
      (divisorLevel lam c T) tree
  have hreal :
      (Helpers.BinaryTree.levelSum (divisorLevel lam c T) tree : ℝ) ≤
        4 * (tree.numLeaves : ℝ) := by
    calc
      (Helpers.BinaryTree.levelSum (divisorLevel lam c T) tree : ℝ) =
          ∑ k ∈ range M,
            (Helpers.BinaryTree.selectedNodeCount
              (fun n => k < divisorLevel lam c T n) tree : ℝ) := by
                exact_mod_cast hsum.symm
      _ ≤ ∑ k ∈ range M,
          2 * tree.numLeaves * (1 / 2 : ℝ) ^ k :=
        sum_le_sum fun k _ => hterm k
      _ = 2 * tree.numLeaves *
          ∑ k ∈ range M, (1 / 2 : ℝ) ^ k := by
        rw [mul_sum]
      _ ≤ 2 * tree.numLeaves * 2 := by
        gcongr
        exact sum_geometric_two_le M
      _ = 4 * tree.numLeaves := by ring
  exact_mod_cast hreal

/-- Product of the (truncated) inverse small divisors carried by the
internal nodes of a binary expansion tree. -/
noncomputable def binarySmallDivisorWeight (lam : ℂ) :
    BinaryTree Unit → ℝ
  | .nil => 1
  | tree@(.node _ left right) =>
      max 1 (smallDivisor lam tree.numLeaves)⁻¹ *
        binarySmallDivisorWeight lam left *
        binarySmallDivisorWeight lam right

private theorem binarySmallDivisorWeight_nonneg_tree (lam : ℂ) :
    ∀ tree : BinaryTree Unit, 0 ≤ binarySmallDivisorWeight lam tree := by
  intro tree
  induction tree with
  | nil => simp [binarySmallDivisorWeight]
  | node value left right ihleft ihrigh =>
      simp only [binarySmallDivisorWeight]
      exact mul_nonneg
        (mul_nonneg (zero_le_one.trans (le_max_left _ _)) ihleft)
        ihrigh

private theorem smallDivisor_factor_le
    {lam : ℂ} {c : ℝ} {T n : ℕ}
    (hc : 0 < c) (hT : T ≠ 0)
    (hn : 2 ≤ n)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1) :
    max 1 (smallDivisor lam n)⁻¹ ≤
      max 1 (2 / c) *
        ((2 : ℝ) ^ T) ^ divisorLevel lam c T n := by
  let d := smallDivisor lam n
  let L := divisorLevel lam c T n
  have hd : 0 < d := by
    dsimp [d, smallDivisor]
    rw [norm_pos_iff]
    exact sub_ne_zero.mpr (hnonzero (n - 1) (by omega))
  have hex := divisorLevel_exists hc hT hn hnonzero
  have hspec :
      dyadicThreshold c T L ≤ d := by
    simpa [L, d, divisorLevel] using firstBelow_spec hex
  have hspec' : c ≤ d * (2 * ((2 : ℝ) ^ L) ^ T) := by
    exact (div_le_iff₀ (by positivity)).mp hspec
  have hinv :
      d⁻¹ ≤ (2 / c) * ((2 : ℝ) ^ L) ^ T := by
    apply (inv_le_iff_one_le_mul₀ hd).2
    rw [show (2 / c) * ((2 : ℝ) ^ L) ^ T * d =
      (2 * ((2 : ℝ) ^ L) ^ T * d) / c by ring]
    rw [le_div_iff₀ hc]
    nlinarith
  have hpow :
      ((2 : ℝ) ^ L) ^ T = ((2 : ℝ) ^ T) ^ L := by
    rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  rw [hpow] at hinv
  change max 1 d⁻¹ ≤ max 1 (2 / c) * ((2 : ℝ) ^ T) ^ L
  apply max_le
  · calc
      1 ≤ max 1 (2 / c) := le_max_left _ _
      _ ≤ max 1 (2 / c) * ((2 : ℝ) ^ T) ^ L := by
        apply le_mul_of_one_le_right
        · exact zero_le_one.trans (le_max_left _ _)
        · exact one_le_pow₀ (one_le_pow₀ (by norm_num))
  · exact hinv.trans
      (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (by positivity))

private theorem binarySmallDivisorWeight_raw_bound
    {lam : ℂ} {c : ℝ} {T : ℕ}
    (hc : 0 < c) (hT : T ≠ 0)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1)
    (tree : BinaryTree Unit) :
    binarySmallDivisorWeight lam tree ≤
      (max 1 (2 / c)) ^ tree.numNodes *
        ((2 : ℝ) ^ T) ^
          Helpers.BinaryTree.levelSum (divisorLevel lam c T) tree := by
  induction tree with
  | nil =>
      simp [binarySmallDivisorWeight, Helpers.BinaryTree.levelSum]
  | node value left right ihleft ihrigh =>
      have hn : 2 ≤ (BinaryTree.node value left right).numLeaves := by
        have hl := left.numLeaves_pos
        have hr := right.numLeaves_pos
        simp only [BinaryTree.numLeaves]
        omega
      have hfactor :=
        smallDivisor_factor_le hc hT hn hnonzero
      have hleft_nonneg :=
        binarySmallDivisorWeight_nonneg_tree lam left
      have hright_nonneg :=
        binarySmallDivisorWeight_nonneg_tree lam right
      have hfactor_bound_nonneg :
          0 ≤ max 1 (2 / c) *
            ((2 : ℝ) ^ T) ^
              divisorLevel lam c T
                (BinaryTree.node value left right).numLeaves :=
        mul_nonneg (zero_le_one.trans (le_max_left _ _)) (by positivity)
      have hleft_bound_nonneg :
          0 ≤ (max 1 (2 / c)) ^ left.numNodes *
            ((2 : ℝ) ^ T) ^
              Helpers.BinaryTree.levelSum
                (divisorLevel lam c T) left := by positivity
      simp only [binarySmallDivisorWeight, Helpers.BinaryTree.levelSum,
        BinaryTree.numNodes]
      calc
        max 1
              (smallDivisor lam
                (BinaryTree.node value left right).numLeaves)⁻¹ *
            binarySmallDivisorWeight lam left *
            binarySmallDivisorWeight lam right
            ≤ (max 1 (2 / c) *
                  ((2 : ℝ) ^ T) ^
                    divisorLevel lam c T
                      (BinaryTree.node value left right).numLeaves) *
                ((max 1 (2 / c)) ^ left.numNodes *
                  ((2 : ℝ) ^ T) ^
                    Helpers.BinaryTree.levelSum
                      (divisorLevel lam c T) left) *
              ((max 1 (2 / c)) ^ right.numNodes *
                ((2 : ℝ) ^ T) ^
                  Helpers.BinaryTree.levelSum
                    (divisorLevel lam c T) right) := by
              calc
                max 1
                      (smallDivisor lam
                        (BinaryTree.node value left right).numLeaves)⁻¹ *
                    binarySmallDivisorWeight lam left *
                    binarySmallDivisorWeight lam right
                    ≤ (max 1 (2 / c) *
                          ((2 : ℝ) ^ T) ^
                            divisorLevel lam c T
                              (BinaryTree.node value left right).numLeaves) *
                        binarySmallDivisorWeight lam left *
                        binarySmallDivisorWeight lam right :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_right hfactor hleft_nonneg)
                    hright_nonneg
                _ ≤ (max 1 (2 / c) *
                          ((2 : ℝ) ^ T) ^
                            divisorLevel lam c T
                              (BinaryTree.node value left right).numLeaves) *
                        ((max 1 (2 / c)) ^ left.numNodes *
                          ((2 : ℝ) ^ T) ^
                            Helpers.BinaryTree.levelSum
                              (divisorLevel lam c T) left) *
                        binarySmallDivisorWeight lam right :=
                  mul_le_mul_of_nonneg_right
                    (mul_le_mul_of_nonneg_left ihleft
                      hfactor_bound_nonneg)
                    hright_nonneg
                _ ≤ _ :=
                  mul_le_mul_of_nonneg_left ihrigh
                    (mul_nonneg hfactor_bound_nonneg
                      hleft_bound_nonneg)
        _ = (max 1 (2 / c)) ^ (left.numNodes + right.numNodes + 1) *
              ((2 : ℝ) ^ T) ^
                (divisorLevel lam c T
                    (BinaryTree.node value left right).numLeaves +
                  Helpers.BinaryTree.levelSum
                    (divisorLevel lam c T) left +
                  Helpers.BinaryTree.levelSum
                    (divisorLevel lam c T) right) := by
              rw [pow_add, pow_add]
              ring

/-- Siegel's tree estimate: the complete product of small divisors in
any binary expansion tree grows at most exponentially in its leaves. -/
theorem binarySmallDivisorWeight_le_pow
    {lam : ℂ} {c : ℝ} {T : ℕ}
    (hc : 0 < c) (hT : T ≠ 0) (hlam : ‖lam‖ = 1)
    (hnonzero : ∀ r : ℕ, r ≠ 0 → lam ^ r ≠ 1)
    (hbound : ∀ r : ℕ, r ≠ 0 →
      c / (r : ℝ) ^ T ≤ ‖lam ^ r - 1‖)
    (tree : BinaryTree Unit) :
    binarySmallDivisorWeight lam tree ≤
      (max 1 (2 / c) * (((2 : ℝ) ^ T) ^ 4)) ^ tree.numLeaves := by
  let A : ℝ := max 1 (2 / c)
  let B : ℝ := (2 : ℝ) ^ T
  have hA : 1 ≤ A := le_max_left _ _
  have hB : 1 ≤ B := one_le_pow₀ (by norm_num)
  have hnodes : tree.numNodes ≤ tree.numLeaves := by
    rw [BinaryTree.numLeaves_eq_numNodes_succ]
    omega
  have hlevels :=
    levelSum_divisorLevel_le hc hT hlam hnonzero hbound tree
  calc
    binarySmallDivisorWeight lam tree ≤
        A ^ tree.numNodes *
          B ^ Helpers.BinaryTree.levelSum
            (divisorLevel lam c T) tree :=
      binarySmallDivisorWeight_raw_bound hc hT hnonzero tree
    _ ≤ A ^ tree.numLeaves * B ^ (4 * tree.numLeaves) := by
      exact mul_le_mul
        (pow_le_pow_right₀ hA hnodes)
        (pow_le_pow_right₀ hB hlevels)
        (by positivity) (by positivity)
    _ = (A * B ^ 4) ^ tree.numLeaves := by
      rw [mul_pow, ← pow_mul]
      ring

end Submission
