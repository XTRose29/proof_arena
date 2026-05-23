import Mathlib

/-!
# Counting argument for unimodal permutations

Key lemmas about how values in a unimodal permutation of {1,...,n}
distribute across the increasing and decreasing parts.
-/

namespace Submission.UnimodalCounting

/-- In a strictly increasing list of naturals, l[j] ≥ l[i] + (j - i). -/
lemma increasing_gap {l : List Nat} (hpw : l.Pairwise (· < ·))
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l[i] + (j - i) ≤ l[j] := by
  induction hij <;> simp_all +arith +decide [List.pairwise_iff_getElem]
  grind

/-- In a strictly decreasing list, l[i] ≥ l[j] + (j - i). -/
lemma decreasing_gap {l : List Nat} (hpw : l.Pairwise (· > ·))
    {i j : Nat} (hi : i < l.length) (hj : j < l.length) (hij : i ≤ j) :
    l[j] + (j - i) ≤ l[i] := by
  induction hij <;> simp_all +decide [List.pairwise_iff_getElem]
  grind

/-
In a strictly increasing list, l[k] ≤ l[i] ↔ k ≤ i.
-/
lemma increasing_le_iff {l : List Nat} (hpw : l.Pairwise (· < ·))
    {i k : Nat} (hi : i < l.length) (hk : k < l.length) :
    l[k] ≤ l[i] ↔ k ≤ i := by
  rw [ List.pairwise_iff_getElem ] at hpw;
  grind

/-
In a strictly decreasing list, if l[j] > t for some t, then l[k] > t for all k ≤ j.
-/
lemma decreasing_above_prefix {l : List Nat} (hpw : l.Pairwise (· > ·))
    {j k t : Nat} (hj : j < l.length) (hk : k < l.length) (hkj : k ≤ j)
    (ht : l[j] > t) : l[k] > t := by
  exact ht.trans_le ( by linarith [ decreasing_gap hpw hk hj hkj ] )

/-
Main cross-bound: in a unimodal permutation of {1,...,n}, for i in the
    increasing part and j in the decreasing part with vals[j] > vals[i],
    we have vals[i] + j ≤ n + i.

    Proof sketch: Count values ≤ vals[i] in the whole permutation.
    There are vals[i] such values. In the increasing part, exactly i+1 are
    at positions 0..i. The remaining vals[i]-i-1 are in the decreasing part
    and form a suffix (positions n-(vals[i]-i-1)..n-1). Since vals[j] > vals[i],
    position j is not in this suffix, so j < n-(vals[i]-i-1) = n-vals[i]+i+1,
    giving vals[i]+j ≤ n+i.
-/
lemma cross_bound_main
    {vals : List Nat} {n p : Nat}
    (hlen : vals.length = n)
    (hnodup : vals.Nodup)
    (hvals : ∀ v ∈ vals, 1 ≤ v ∧ v ≤ n)
    (hinc : (vals.take p).Pairwise (· < ·))
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hp : p ≤ n)
    {i j : Nat} (hi : i < p) (hj : p ≤ j) (hjn : j < n)
    (hgt : vals[j]! > vals[i]!) :
    vals[i]! + j ≤ n + i := by
  -- By counting values ≤ vals[i]! in the entire permutation, we find that there are exactly vals[i]! such values.
  have h_count : (Finset.filter (fun k => vals[k]! ≤ vals[i]!) (Finset.range n)).card = vals[i]! := by
    have h_count : Finset.image (fun k => vals[k]!) (Finset.range n) = Finset.Icc 1 n := by
      fapply Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
      · grind;
      · rw [ Finset.card_image_of_injOn ];
        · norm_num +decide;
        · intro k hk l hl hkl; have := List.nodup_iff_injective_get.mp hnodup; simp_all +decide [ Finset.mem_range ] ;
          have := @this ⟨ k, by linarith ⟩ ⟨ l, by linarith ⟩ ; aesop;
    have h_count : (Finset.filter (fun k => vals[k]! ≤ vals[i]!) (Finset.range n)).card = (Finset.filter (fun x => x ≤ vals[i]!) (Finset.Icc 1 n)).card := by
      rw [ ← h_count, Finset.card_filter, Finset.card_filter ];
      rw [ Finset.sum_image ];
      intro k hk l hl hkl; have := Finset.card_image_iff.mp ( by aesop : Finset.card ( Finset.image ( fun k => vals[k]! ) ( Finset.range n ) ) = Finset.card ( Finset.range n ) ) ; aesop;
    rw [ h_count ];
    rw [ show { x ∈ Finset.Icc 1 n | x ≤ vals[i]! } = Finset.Icc 1 ( vals[i]! ) from ?_ ];
    · norm_num;
    · grind +splitImp;
  -- In the increasing part (positions 0..p-1), the values ≤ vals[i]! are exactly at positions 0..i (by increasing_le_iff, since vals.take p is pairwise <). That's i+1 positions.
  have h_inc_count : (Finset.filter (fun k => vals[k]! ≤ vals[i]!) (Finset.range p)).card = i + 1 := by
    rw [ show Finset.filter ( fun k => vals[k]! ≤ vals[i]! ) ( Finset.range p ) = Finset.Icc 0 i from ?_ ];
    · simp +arith +decide;
    · ext k;
      constructor;
      · have := List.pairwise_iff_get.mp hinc;
        contrapose! this;
        use ⟨ i, by
          grind ⟩, ⟨ k, by
          grind ⟩
        generalize_proofs at *;
        grind;
      · intro hk;
        have := List.pairwise_iff_get.mp hinc;
        by_cases hk' : k < p <;> by_cases hi' : i < p <;> simp_all +decide [ List.getElem?_eq_getElem ];
        · by_cases hk'' : k < List.length vals <;> by_cases hi'' : i < List.length vals <;> simp_all +decide [ List.getElem?_eq_none ];
          · exact le_of_not_gt fun h => by have := this ⟨ k, by simpa [ List.length_take, hlen ] using by omega ⟩ ⟨ i, by simpa [ List.length_take, hlen ] using by omega ⟩ ( show k < i from lt_of_le_of_ne hk ( by aesop_cat ) ) ; linarith;
          · linarith;
        · grind;
  -- In the decreasing part, values > vals[i]! form a prefix (by decreasing_above_prefix). Since vals[j]! > vals[i]! (hypothesis hgt) and j ≥ p, position j is in this prefix. All positions p, p+1, ..., j have values > vals[i]!.
  have h_dec_prefix : ∀ k ∈ Finset.Icc p j, vals[k]! > vals[i]! := by
    have h_dec_prefix : ∀ k ∈ Finset.Icc p j, vals[k]! ≥ vals[j]! := by
      have h_dec_prefix : ∀ k l : ℕ, k ≤ l → l < vals.length → k ≥ p → l ≥ p → vals[k]! ≥ vals[l]! := by
        intros k l hkl hl hk hl'; have := List.pairwise_iff_get.mp hdec; simp_all +decide [ List.get ] ;
        by_cases h_cases : k < p + (List.drop p vals).length ∧ l < p + (List.drop p vals).length;
        · by_cases h_cases : k = l;
          · grind;
          · have := this ⟨ k - p, by omega ⟩ ⟨ l - p, by omega ⟩ ( by exact Nat.sub_lt_sub_right ( by omega ) ( lt_of_le_of_ne hkl h_cases ) ) ; simp_all +decide [ add_tsub_cancel_of_le hk, add_tsub_cancel_of_le hl' ] ;
            grind;
        · grind;
      exact fun k hk => h_dec_prefix k j ( Finset.mem_Icc.mp hk |>.2 ) ( by linarith ) ( Finset.mem_Icc.mp hk |>.1 ) hj;
    exact fun k hk => lt_of_lt_of_le hgt ( h_dec_prefix k hk );
  -- So the positions in [p, n) with values ≤ vals[i]! are all at positions > j. That means there are at most n - 1 - j positions with values ≤ vals[i]! in [j+1, n).
  have h_dec_count : (Finset.filter (fun k => vals[k]! ≤ vals[i]!) (Finset.Ico p n)).card ≤ n - 1 - j := by
    have h_dec_count : (Finset.filter (fun k => vals[k]! ≤ vals[i]!) (Finset.Ico p n)).card ≤ Finset.card (Finset.Ico (j + 1) n) := by
      exact Finset.card_le_card fun x hx => Finset.mem_Ico.mpr ⟨ Nat.lt_of_not_ge fun hx' => not_lt_of_ge ( Finset.mem_filter.mp hx |>.2 ) ( h_dec_prefix x ( Finset.mem_Icc.mpr ⟨ by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) ], by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) ] ⟩ ) ), by linarith [ Finset.mem_Ico.mp ( Finset.mem_filter.mp hx |>.1 ) ] ⟩;
    exact h_dec_count.trans ( by simp +arith +decide [ Nat.sub_sub, add_comm ] );
  -- By combining the counts from the increasing and decreasing parts, we get the total count of values ≤ vals[i]! in the entire permutation.
  have h_total_count : (Finset.filter (fun k => vals[k]! ≤ vals[i]!) (Finset.range n)).card = (Finset.filter (fun k => vals[k]! ≤ vals[i]!) (Finset.range p)).card + (Finset.filter (fun k => vals[k]! ≤ vals[i]!) (Finset.Ico p n)).card := by
    rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
    rw [ Finset.sum_range_add_sum_Ico _ hp ];
  omega

/-
The ordering condition vals[j]+j-n ≥ i+1 implies vals[i] < vals[j]
    in a unimodal permutation.

    Proof sketch: Total values > vals[j] is n-vals[j]. In the decreasing part,
    j-p values (at positions p..j-1) are > vals[j]. So n-vals[j]-(j-p) = p-c
    values > vals[j] in the increasing part, where c = vals[j]+j-n. These
    occupy the last p-c positions (c..p-1). Since i < c (from horder),
    vals[i] ≤ vals[j]. Distinct positions ⇒ vals[i] < vals[j].
-/
lemma ordering_implies_lt
    {vals : List Nat} {n p : Nat}
    (hlen : vals.length = n)
    (hnodup : vals.Nodup)
    (hvals : ∀ v ∈ vals, 1 ≤ v ∧ v ≤ n)
    (hinc : (vals.take p).Pairwise (· < ·))
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hp : p ≤ n)
    {i j : Nat} (hi : i < p) (hj : p ≤ j) (hjn : j < n)
    (horder : i + 1 ≤ vals[j]! + j - n) :
    vals[i]! < vals[j]! := by
  refine lt_of_le_of_ne ?_ ?_;
  · -- Since vals is nodup, there are exactly n - vals[j]! values greater than vals[j]! in the permutation.
    have h_count : (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.range n)).card = n - vals[j]! := by
      have h_count : (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.range n)).card = Finset.card (Finset.filter (fun v => v > vals[j]!) (List.toFinset vals)) := by
        refine' Finset.card_bij ( fun k hk => vals[k]! ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_range ];
        · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; have := List.nodup_iff_injective_get.mp hnodup; have := @this ⟨ a₁, by linarith ⟩ ⟨ a₂, by linarith ⟩ ; aesop;
        · intro b hb hb'; obtain ⟨ k, hk ⟩ := List.mem_iff_getElem.mp hb; use k; aesop;
      have h_count : Finset.filter (fun v => v > vals[j]!) (List.toFinset vals) = Finset.Icc (vals[j]! + 1) n := by
        have h_count : List.toFinset vals = Finset.Icc 1 n := by
          exact Finset.eq_of_subset_of_card_le ( fun x hx => Finset.mem_Icc.mpr <| hvals x <| List.mem_toFinset.mp hx ) ( by rw [ Finset.card_eq_sum_ones ] ; rw [ List.toFinset_card_of_nodup hnodup ] ; aesop );
        grind;
      aesop;
    -- Since vals is nodup, there are exactly j - p values greater than vals[j]! in the decreasing part.
    have h_decreasing_count : (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.Ico p j)).card = j - p := by
      rw [ Finset.filter_true_of_mem ];
      · norm_num;
      · have := List.pairwise_iff_get.mp hdec;
        simp_all +decide [ List.get ];
        intro x hx₁ hx₂; specialize this ⟨ x - p, by
          grind ⟩ ⟨ j - p, by
          grind ⟩ ( by
          exact Nat.sub_lt_sub_right hx₁ hx₂ ) ; simp_all +decide [ add_tsub_cancel_of_le hx₁, add_tsub_cancel_of_le hj ] ;
        grind;
    -- Since vals is nodup, there are exactly n - vals[j]! - (j - p) values greater than vals[j]! in the increasing part.
    have h_increasing_count : (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.range p)).card = n - vals[j]! - (j - p) := by
      have h_increasing_count : (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.range n)).card = (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.range p)).card + (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.Ico p j)).card + (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.Ico j n)).card := by
        rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter, Finset.card_filter ];
        rw [ Finset.sum_range_add_sum_Ico _ ( by linarith ), Finset.sum_range_add_sum_Ico _ ( by linarith ) ];
      have h_decreasing_count : (Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.Ico j n)).card = 0 := by
        simp_all +decide [ Finset.ext_iff ];
        intros a ha hb₂; have := List.pairwise_iff_get.mp hdec; simp_all +decide [ List.getElem?_eq_getElem ] ;
        specialize this ⟨ j - p, by
          grind ⟩ ⟨ a - p, by
          grind ⟩ ; simp_all +decide [ Nat.add_sub_of_le hj, Nat.add_sub_of_le ( show p ≤ a from by linarith ) ];
        lia;
      grind +revert;
    -- Since vals is nodup, the values greater than vals[j]! in the increasing part are exactly the last n - vals[j]! - (j - p) positions.
    have h_increasing_positions : Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.range p) = Finset.Ico (p - (n - vals[j]! - (j - p))) p := by
      have h_increasing_positions : ∀ k l : ℕ, k < l → l < p → vals[k]! > vals[j]! → vals[l]! > vals[j]! := by
        intros k l hkl hlp hkj
        have h_increasing : vals[k]! < vals[l]! := by
          have := List.pairwise_iff_get.mp hinc;
          convert this ⟨ k, by
            grind ⟩ ⟨ l, by
            grind ⟩ hkl using 1
          all_goals generalize_proofs at *;
          · grind;
          · grind;
        linarith;
      refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
      · have h_increasing_positions : Finset.filter (fun k => vals[k]! > vals[j]!) (Finset.range p) ⊇ Finset.Ico x p := by
          grind +extAll;
        have := Finset.card_mono h_increasing_positions; simp_all +decide ;
        grind;
      · simp_all +decide [ Nat.sub_sub ];
        omega;
    replace h_increasing_positions := Finset.ext_iff.mp h_increasing_positions i ; simp_all +decide;
    omega;
  · have h_distinct : ∀ (i j : ℕ), i < j → i < vals.length → j < vals.length → vals[i]! ≠ vals[j]! := by
      intro i j hij hi hj; have := List.nodup_iff_injective_get.mp hnodup; have := @this ⟨ i, hi ⟩ ⟨ j, hj ⟩ ; aesop;
    grind +qlia

/-- Cross-bound case 3: combining ordering_implies_lt and cross_bound_main. -/
lemma cross_bound_case3
    {vals : List Nat} {n p : Nat}
    (hlen : vals.length = n)
    (hnodup : vals.Nodup)
    (hvals : ∀ v ∈ vals, 1 ≤ v ∧ v ≤ n)
    (hinc : (vals.take p).Pairwise (· < ·))
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hp : p ≤ n)
    {i j : Nat} (hi : i < p) (hj : p ≤ j) (hjn : j < n)
    (horder : i + 1 ≤ vals[j]! + j - n) :
    vals[i]! + j ≤ n + i :=
  cross_bound_main hlen hnodup hvals hinc hdec hp hi hj hjn
    (ordering_implies_lt hlen hnodup hvals hinc hdec hp hi hj hjn horder)

/-
In the decreasing part of a unimodal permutation of {1,...,n},
    vals[j] ≥ n - j for j ≥ p. Equivalently vals[j]+j ≥ n.
-/
lemma dec_val_lower_bound
    {vals : List Nat} {n p : Nat}
    (hlen : vals.length = n)
    (hvals : ∀ v ∈ vals, 1 ≤ v ∧ v ≤ n)
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hp : p ≤ n)
    {j : Nat} (hj : p ≤ j) (hjn : j < n) :
    n ≤ vals[j]! + j := by
  -- By Lemma 2, in the decreasing part, vals[j] ≥ n - j for j ≥ p.
  have h_decr_bound : (vals.drop p)[j - p]! ≥ (vals.drop p)[(n - p) - 1]! + ((n - p) - 1 - (j - p)) := by
    have h_decr_bound : ∀ i j : ℕ, i < (vals.drop p).length → j < (vals.drop p).length → i ≤ j → (vals.drop p)[j]! + (j - i) ≤ (vals.drop p)[i]! := by
      intros i j hi hj hij;
      convert decreasing_gap hdec hi hj hij using 1;
      · grind +locals;
      · grind;
    exact h_decr_bound _ _ ( by simpa [ hlen ] using by omega ) ( by simpa [ hlen ] using by omega ) ( by omega );
  have h_last_ge_one : (vals.drop p)[(n - p) - 1]! ≥ 1 := by
    convert hvals _ _ |>.1;
    grind;
  grind

/-
If c ≤ i and positions c..p-1 in the increasing part have values > vals[j]!,
    then vals[i]! > vals[j]!.
-/
lemma reverse_ordering_implies_gt
    {vals : List Nat} {n p : Nat}
    (hlen : vals.length = n)
    (hnodup : vals.Nodup)
    (hvals : ∀ v ∈ vals, 1 ≤ v ∧ v ≤ n)
    (hinc : (vals.take p).Pairwise (· < ·))
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hp : p ≤ n)
    {i j : Nat} (hi : i < p) (hj : p ≤ j) (hjn : j < n)
    (horder : vals[j]! + j - n ≤ i) :
    vals[i]! > vals[j]! := by
  -- By the ordering condition, we have that there are exactly `p - c` values greater than `vals[j]!` in the increasing part.
  have h_count : Finset.card (Finset.filter (fun x => vals[x]! > vals[j]!) (Finset.range p)) = p - (vals[j]! + j - n) := by
    have h_count : Finset.card (Finset.filter (fun x => vals[x]! > vals[j]!) (Finset.range n)) = n - vals[j]! := by
      have h_count : Finset.card (Finset.filter (fun x => vals[x]! > vals[j]!) (Finset.range n)) = Finset.card (Finset.filter (fun x => x > vals[j]!) (vals.toFinset)) := by
        refine' Finset.card_bij ( fun x hx => vals[x]! ) _ _ _ <;> simp_all +decide [ Finset.mem_filter, Finset.mem_range ];
        · intro a₁ ha₁ ha₂ a₂ ha₃ ha₄ h; have := List.nodup_iff_injective_get.mp hnodup; have := @this ⟨ a₁, by linarith ⟩ ⟨ a₂, by linarith ⟩ ; aesop;
        · intro b hb hb'; obtain ⟨ k, hk ⟩ := List.mem_iff_get.1 hb; use k; aesop;
      have h_count : Finset.filter (fun x => x > vals[j]!) (vals.toFinset) = Finset.Icc (vals[j]! + 1) n := by
        have h_count : vals.toFinset = Finset.Icc 1 n := by
          exact Finset.eq_of_subset_of_card_le ( fun x hx => by aesop ) ( by rw [ List.toFinset_card_of_nodup hnodup ] ; aesop );
        grind;
      aesop;
    have h_count_dec : Finset.card (Finset.filter (fun x => vals[x]! > vals[j]!) (Finset.Ico p n)) = j - p := by
      rw [ show Finset.filter ( fun x => vals[x]! > vals[j]! ) ( Finset.Ico p n ) = Finset.Ico p j from ?_ ];
      · norm_num;
      · ext x;
        simp +zetaDelta at *;
        constructor <;> intro h;
        · have := List.pairwise_iff_get.mp hdec;
          contrapose! this;
          use ⟨ j - p, by
            grind ⟩, ⟨ x - p, by
            rw [ List.length_drop, hlen ] ; omega ⟩
          generalize_proofs at *;
          grind +splitImp;
        · have := List.pairwise_iff_get.mp hdec;
          specialize this ⟨ x - p, by
            grind ⟩ ⟨ j - p, by
            grind ⟩ ; simp_all +decide [ List.getElem?_eq_getElem ];
          grind;
    have h_count_inc : Finset.card (Finset.filter (fun x => vals[x]! > vals[j]!) (Finset.range n)) = Finset.card (Finset.filter (fun x => vals[x]! > vals[j]!) (Finset.range p)) + Finset.card (Finset.filter (fun x => vals[x]! > vals[j]!) (Finset.Ico p n)) := by
      rw [ Finset.card_filter, Finset.card_filter, Finset.card_filter ];
      rw [ Finset.sum_range_add_sum_Ico _ hp ];
    grind;
  -- Since $c \leq i$, we have that the set of indices in the increasing part that are greater than $vals[j]!$ is exactly $\{c, c+1, \ldots, p-1\}$.
  have h_filter_eq : Finset.filter (fun x => vals[x]! > vals[j]!) (Finset.range p) = Finset.Ico (vals[j]! + j - n) p := by
    refine' Finset.eq_of_subset_of_card_le ( fun x hx => _ ) _;
    · have h_filter_eq : ∀ x ∈ Finset.range p, ∀ y ∈ Finset.range p, x < y → vals[x]! < vals[y]! := by
        intros x hx y hy hxy;
        have := List.pairwise_iff_get.mp hinc;
        convert this ⟨ x, by
          grind ⟩ ⟨ y, by
          grind ⟩ hxy using 1
        all_goals generalize_proofs at *;
        · grind +revert;
        · grind;
      grind +suggestions;
    · aesop;
  replace h_filter_eq := Finset.ext_iff.mp h_filter_eq i; aesop;

/-
Cross-bound case 4: if vals[j]+j ≤ n+i, then vals[i]+j ≥ n+i+1.
-/
lemma cross_bound_case4
    {vals : List Nat} {n p : Nat}
    (hlen : vals.length = n)
    (hnodup : vals.Nodup)
    (hvals : ∀ v ∈ vals, 1 ≤ v ∧ v ≤ n)
    (hinc : (vals.take p).Pairwise (· < ·))
    (hdec : (vals.drop p).Pairwise (· > ·))
    (hp : p ≤ n)
    {i j : Nat} (hi : i < p) (hj : p ≤ j) (hjn : j < n)
    (horder : vals[j]! + j ≤ n + i) :
    n + i + 1 ≤ vals[i]! + j := by
  -- From `horder` and `dec_val_lower_bound`, we derive that `vals[j]! + j = n + c` where `c ≤ i`.
  obtain ⟨c, hc⟩ : ∃ c, vals[j]! + j = n + c ∧ c ≤ i := by
    exact ⟨ vals[j]! + j - n, by rw [ Nat.add_sub_cancel' ( by linarith [ dec_val_lower_bound hlen hvals hdec hp hj hjn ] ) ], Nat.sub_le_of_le_add <| by linarith ⟩;
  -- By `reverse_ordering_implies_gt` at `c`, we have `vals[c]! > vals[j]!`, so `vals[c]! ≥ vals[j]! + 1`.
  have h_gt_c : vals[c]! > vals[j]! := by
    apply reverse_ordering_implies_gt hlen hnodup hvals hinc hdec hp;
    · linarith;
    · linarith;
    · linarith;
    · omega;
  have := increasing_gap ( show List.Pairwise ( · < · ) ( List.take p vals ) from hinc ) ( show c < List.length ( List.take p vals ) from by
                                                                                            grind ) ( show i < List.length ( List.take p vals ) from by
                                                                                                                                                        grind +extAll ) ( by linarith );
  grind

end Submission.UnimodalCounting