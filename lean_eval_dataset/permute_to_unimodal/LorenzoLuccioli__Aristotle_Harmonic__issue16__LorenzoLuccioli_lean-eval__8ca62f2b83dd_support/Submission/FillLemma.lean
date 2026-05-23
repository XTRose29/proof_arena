import Mathlib

/-!
# Filling Lemma for the achievability proof
-/

set_option maxHeartbeats 400000

namespace Submission.FillLemma

/-- The fill predicate determines membership in S greedily. -/
def inFillSet (v : Nat) : List (Nat × Nat × Bool) → Nat → Nat → Bool
  | [], _, _ => false
  | (val, count, inc) :: rest, running, start =>
    if v < val then
      decide (start ≤ v ∧ v < start + (count - running))
    else if v = val then inc
    else
      let new_running := count + (if inc then 1 else 0)
      inFillSet v rest new_running (val + 1)

/-- Well-formedness conditions -/
structure WellFormedConstraints (n : Nat) (cs : List (Nat × Nat × Bool)) : Prop where
  vals_lt_n : ∀ c ∈ cs, c.1 < n
  vals_increasing : cs.Pairwise (fun c₁ c₂ => c₁.1 < c₂.1)
  counts_le_vals : ∀ c ∈ cs, c.2.1 ≤ c.1
  gap_lower : ∀ i, i + 1 < cs.length →
    cs[i]!.2.1 + (if cs[i]!.2.2 then 1 else 0) ≤ cs[i + 1]!.2.1
  gap_upper : ∀ i, i + 1 < cs.length →
    cs[i + 1]!.2.1 + cs[i]!.1 + 1 ≤ cs[i]!.2.1 + (if cs[i]!.2.2 then 1 else 0) + cs[i + 1]!.1

lemma inFillSet_lt (val count : Nat) (inc : Bool) (rest : List (Nat × Nat × Bool))
    (running start v : Nat) (hv : v < val) :
    inFillSet v ((val, count, inc) :: rest) running start =
      decide (start ≤ v ∧ v < start + (count - running)) := by
  simp [inFillSet, hv]

lemma inFillSet_eq (val count : Nat) (inc : Bool) (rest : List (Nat × Nat × Bool))
    (running start : Nat) :
    inFillSet val ((val, count, inc) :: rest) running start = inc := by
  simp [inFillSet]

lemma inFillSet_gt (val count : Nat) (inc : Bool) (rest : List (Nat × Nat × Bool))
    (running start v : Nat) (hv : val < v) :
    inFillSet v ((val, count, inc) :: rest) running start =
      inFillSet v rest (count + if inc then 1 else 0) (val + 1) := by
  simp [inFillSet, Nat.not_lt.mpr (Nat.le_of_lt hv), Nat.ne_of_gt hv]

lemma inFillSet_at_constraint (cs : List (Nat × Nat × Bool))
    (h_inc : cs.Pairwise (fun c₁ c₂ => c₁.1 < c₂.1))
    (running start : Nat) (h_start : start ≤ cs.head!.1)
    (k : Nat) (hk : k < cs.length) :
    inFillSet cs[k]!.1 cs running start = cs[k]!.2.2 := by
  induction' k with k ih generalizing cs running start
  · cases cs <;> simp_all +decide [inFillSet]
  · rcases cs with (_ | ⟨c, _ | ⟨d, cs⟩⟩) <;> simp_all +decide
    specialize ih (d :: cs) (by simp_all +decide [List.pairwise_cons]; exact h_inc.2.1)
      (c.2.1 + (if c.2.2 then 1 else 0)) (c.1 + 1) (by exact Nat.succ_le_of_lt h_inc.1.1) (by grind)
    grind +locals

lemma sort_at_count {α : Type*} [LinearOrder α] [DecidableEq α] (S : Finset α) (v : α) (hv : v ∈ S)
    (k : Nat) (hk : (S.filter (fun w => w < v)).card = k)
    (hk2 : k < (S.sort (· ≤ ·)).length) :
    (S.sort (· ≤ ·))[k] = v := by
  have h_sorted : List.Pairwise (· < ·) (S.sort (· ≤ ·)) := by
    convert Finset.sortedLT_sort S using 1; grind +splitIndPred
  have h_lt_count : ∀ (l : List α), List.Pairwise (· < ·) l → ∀ (x : α), x ∈ l →
      (List.filter (· < x) l).length = List.idxOf x l := by
    intro l hl x hx; induction l <;> simp_all +decide [List.pairwise_cons]
    cases hx <;> simp_all +decide [List.filter_cons]
    · exact fun x hx => le_of_lt (hl.1 x hx)
    · grind
  have h2 : List.length (List.filter (· < v) (S.sort (· ≤ ·))) = k := by
    rw [← hk, ← Multiset.coe_card]
    rw [← Multiset.toFinset_card_of_nodup] <;> norm_num [Finset.nodup_toList]
    exact List.Nodup.filter _ (Finset.sort_nodup _ _)
  have h3 : List.idxOf v (S.sort (· ≤ ·)) = k := by aesop
  grind

lemma fin_filter_count_interval (n : Nat) (lo hi : Nat)
    (hlo_hi : lo ≤ hi) (hhi : hi ≤ n) :
    (Finset.filter (fun w : Fin n => lo ≤ w.val ∧ w.val < hi) Finset.univ).card = hi - lo := by
  convert Finset.card_range (hi - lo) using 1
  refine' Finset.card_bij (fun x hx => x - lo) _ _ _ <;> simp_all +decide
  · exact fun a ha₁ ha₂ => by omega
  · grind
  · exact fun b hb => ⟨⟨lo + b, by linarith [Nat.sub_add_cancel hlo_hi]⟩,
      ⟨by linarith, by linarith [Nat.sub_add_cancel hlo_hi]⟩, by simp +decide⟩

/-
Key recursion: inFillSet skips past k constraints when v > all their values
-/
lemma inFillSet_skip (cs : List (Nat × Nat × Bool))
    (h_inc : cs.Pairwise (fun c₁ c₂ => c₁.1 < c₂.1))
    (v running start : Nat)
    (k : Nat) (hk : k < cs.length)
    (hv : cs[k]!.1 < v) :
    inFillSet v cs running start =
      inFillSet v (cs.drop (k + 1))
        (cs[k]!.2.1 + if cs[k]!.2.2 then 1 else 0)
        (cs[k]!.1 + 1) := by
  have h_ind_step : ∀ {cs : List (Nat × Nat × Bool)}
      (h_inc : cs.Pairwise (fun c₁ c₂ => c₁.1 < c₂.1))
      (running : Nat) (start : Nat) (v : Nat)  (k : Nat) (hk : k < cs.length) (hv : v > cs[k]!.1),
      inFillSet v cs running start = inFillSet v (List.drop (k + 1) cs)
        (cs[k]!.2.1 + (if cs[k]!.2.2 then 1 else 0)) (cs[k]!.1 + 1) := by
          intros cs h_inc running start v k hk hv;
          induction' k with k ih generalizing cs running start v;
          · rcases cs with ( _ | ⟨ ⟨ val, count, inc ⟩, cs ⟩ ) <;> simp_all +decide;
            exact inFillSet_gt _ _ _ _ _ _ _ hv;
          · rcases cs with ( _ | ⟨ c, cs ⟩ ) <;> simp_all +arith +decide;
            by_cases h : v < c.1 <;> by_cases h' : v = c.1 <;> simp_all +decide [ inFillSet ];
            · grind;
            · grind +revert;
  exact h_ind_step h_inc running start v k hk hv

/-
Main count lemma
-/
lemma inFillSet_count_below (n : Nat) (cs : List (Nat × Nat × Bool))
    (hwf : WellFormedConstraints n cs)
    (k : Nat) (hk : k < cs.length) :
    (Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val < cs[k]!.1) Finset.univ).card
      = cs[k]!.2.1 := by
  by_contra h_contra;
  -- Apply induction on $k$.
  induction' k with k ih ih;
  · rcases cs <;> simp_all +decide [ WellFormedConstraints ];
    refine' h_contra _;
    convert fin_filter_count_interval n 0 ( ‹ℕ × ℕ × Bool›.2.1 ) ( by linarith ) ( by linarith [ hwf.vals_lt_n _ ( List.mem_cons_self ), hwf.counts_le_vals _ ( List.mem_cons_self ) ] ) using 1;
    refine' Finset.card_bij ( fun x hx => x ) _ _ _ <;> simp +decide [ Finset.mem_filter ];
    · intro a ha ha'; rw [ inFillSet_lt ] at ha <;> aesop;
    · intro b hb; have := hwf.counts_le_vals; simp_all +decide [ WellFormedConstraints ] ;
      grind +locals;
  · have h_split : Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val < cs[k + 1]!.1) Finset.univ =
      Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val < cs[k]!.1) Finset.univ ∪
      Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val = cs[k]!.1) Finset.univ ∪
      Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ cs[k]!.1 < w.val ∧ w.val < cs[k + 1]!.1) Finset.univ := by
        grind +splitIndPred;
    have h_card_A : (Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val < cs[k]!.1) Finset.univ).card = cs[k]!.2.1 := by
      exact Classical.not_not.1 fun h => ih ( Nat.lt_of_succ_lt hk ) h
    have h_card_B : (Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val = cs[k]!.1) Finset.univ).card = (if cs[k]!.2.2 then 1 else 0) := by
      have h_card_B : ∀ w : Fin n, inFillSet w.val cs 0 0 ∧ w.val = cs[k]!.1 ↔ w.val = cs[k]!.1 ∧ cs[k]!.2.2 := by
        have := inFillSet_at_constraint cs hwf.vals_increasing 0 0 (by
        exact Nat.zero_le _) k (by
        linarith);
        grind;
      split_ifs <;> simp_all +decide [ Finset.card_eq_one ];
      have := hwf.vals_lt_n ( cs[k]! ) ?_ <;> simp_all +decide [ Fin.ext_iff ];
      · exact ⟨ ⟨ _, this ⟩, by ext; aesop ⟩;
      · grind
    have h_card_C : (Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ cs[k]!.1 < w.val ∧ w.val < cs[k + 1]!.1) Finset.univ).card = cs[k + 1]!.2.1 - (cs[k]!.2.1 + (if cs[k]!.2.2 then 1 else 0)) := by
      have h_card_C : ∀ w : Fin n, cs[k]!.1 < w.val ∧ w.val < cs[k + 1]!.1 → inFillSet w.val cs 0 0 = decide (cs[k]!.1 + 1 ≤ w.val ∧ w.val < cs[k]!.1 + 1 + (cs[k + 1]!.2.1 - (cs[k]!.2.1 + (if cs[k]!.2.2 then 1 else 0)))) := by
        intros w hw
        have h_skip : inFillSet w.val cs 0 0 = inFillSet w.val (cs.drop (k + 1)) (cs[k]!.2.1 + (if cs[k]!.2.2 then 1 else 0)) (cs[k]!.1 + 1) := by
          apply inFillSet_skip;
          · exact hwf.vals_increasing;
          · grind;
          · grind;
        rw [h_skip];
        convert inFillSet_lt _ _ _ _ _ _ _ _ using 1;
        rotate_left;
        exact cs[k + 1]!.1;
        exact cs[k + 1]!.2.2;
        exact List.drop ( k + 2 ) cs;
        · linarith;
        · rw [ List.drop_eq_getElem_cons ];
          grind;
          linarith;
      have h_card_C : (Finset.filter (fun w : Fin n => cs[k]!.1 + 1 ≤ w.val ∧ w.val < cs[k]!.1 + 1 + (cs[k + 1]!.2.1 - (cs[k]!.2.1 + (if cs[k]!.2.2 then 1 else 0))) ∧ cs[k]!.1 < w.val ∧ w.val < cs[k + 1]!.1) Finset.univ).card = cs[k + 1]!.2.1 - (cs[k]!.2.1 + (if cs[k]!.2.2 then 1 else 0)) := by
        have h_card_C : (Finset.filter (fun w : Fin n => cs[k]!.1 + 1 ≤ w.val ∧ w.val < cs[k]!.1 + 1 + (cs[k + 1]!.2.1 - (cs[k]!.2.1 + (if cs[k]!.2.2 then 1 else 0)))) Finset.univ).card = cs[k + 1]!.2.1 - (cs[k]!.2.1 + (if cs[k]!.2.2 then 1 else 0)) := by
          convert fin_filter_count_interval n ( cs[k]!.1 + 1 ) ( cs[k]!.1 + 1 + ( cs[k + 1]!.2.1 - ( cs[k]!.2.1 + if cs[k]!.2.2 = true then 1 else 0 ) ) ) _ _ using 1;
          · rw [ Nat.add_sub_cancel_left ];
          · exact Nat.le_add_right _ _;
          · grind +splitIndPred;
        convert h_card_C using 2;
        ext w; simp [Finset.mem_filter, Finset.mem_univ];
        intro hw₁ hw₂; have := hwf.gap_upper k; simp_all +decide [ Nat.lt_succ_iff ] ;
        grind;
      convert h_card_C using 2;
      grind;
    have h_card_union : (Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val < cs[k + 1]!.1) Finset.univ).card =
        (Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val < cs[k]!.1) Finset.univ).card +
        (Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ w.val = cs[k]!.1) Finset.univ).card +
        (Finset.filter (fun w : Fin n => inFillSet w.val cs 0 0 ∧ cs[k]!.1 < w.val ∧ w.val < cs[k + 1]!.1) Finset.univ).card := by
          rw [ h_split, Finset.card_union_of_disjoint, Finset.card_union_of_disjoint ] <;> simp +contextual [ Finset.disjoint_left ];
          · exact fun _ _ _ => ne_of_lt ‹_›;
          · grind;
    have := hwf.gap_lower k hk; have := hwf.gap_upper k hk; simp_all +decide [ Finset.ext_iff ] ;

end Submission.FillLemma