import Mathlib

set_option maxHeartbeats 400000

/-! ## Multiset halving for fixed-point-free involutions

If a multiset is invariant under a fixed-point-free involution,
then it can be split into two halves. -/

open Multiset

lemma Multiset.halving {α : Type*} [DecidableEq α] (S : Multiset α) (f : α → α)
    (hf_invol : ∀ a, f (f a) = a)
    (hf_fp_free : ∀ a ∈ S, f a ≠ a)
    (hf_closed : ∀ a ∈ S, f a ∈ S)
    (hf_count : ∀ a ∈ S, S.count a = S.count (f a)) :
    ∃ T : Multiset α, S = T + T.map f ∧ 2 * T.card = S.card := by
  revert hf_closed hf_count hf_fp_free hf_invol S f;
  -- We prove this by strong induction on $S.card$.
  intro S f hf_invol hf_fp_free hf_closed hf_count
  induction' n : Multiset.card S using Nat.strong_induction_on with n ih generalizing S f;
  by_cases hS : S = 0;
  · exact ⟨ 0, by simp +decide [ ← n, hS ] ⟩;
  · obtain ⟨a, ha⟩ : ∃ a ∈ S, f a ≠ a := by
      exact Exists.elim ( Multiset.exists_mem_of_ne_zero hS ) fun x hx => ⟨ x, hx, hf_fp_free x hx ⟩;
    -- Define S' = S - {a} - {f(a)}.
    obtain ⟨S', hS'⟩ : ∃ S' : Multiset α, S = S' + {a} + {f a} := by
      obtain ⟨S', hS'⟩ : ∃ S' : Multiset α, S = S' + {a} := by
        exact ⟨ S.erase a, by rw [ add_comm, Multiset.singleton_add, Multiset.cons_erase ha.1 ] ⟩;
      specialize hf_count a ; simp_all +decide [ Multiset.count_singleton ];
      exact ⟨ S' - { f a }, by rw [ add_right_comm, tsub_add_cancel_of_le ( Multiset.singleton_le.mpr ( Multiset.count_pos.mp ( by linarith ) ) ) ] ⟩;
    -- By the induction hypothesis, there exists a multiset $T'$ such that $S' = T' + T'.map f$ and $2 * T'.card = S'.card$.
    obtain ⟨T', hT'⟩ : ∃ T' : Multiset α, S' = T' + T'.map f ∧ 2 * T'.card = S'.card := by
      apply ih (Multiset.card S');
      all_goals norm_num [ hS' ] at *;
      · linarith;
      · exact hf_invol;
      · exact fun x hx => hf_fp_free x ( Or.inl ( Or.inl hx ) );
      · grind +suggestions;
      · intro x hx; specialize hf_count x; simp_all +decide [ Multiset.count_singleton ] ;
        grind;
    use T' + {a};
    simp_all +decide [ add_comm, add_left_comm, add_assoc ];
    linarith
