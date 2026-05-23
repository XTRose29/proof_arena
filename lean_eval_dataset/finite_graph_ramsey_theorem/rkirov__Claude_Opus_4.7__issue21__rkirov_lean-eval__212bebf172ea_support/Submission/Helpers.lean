import Mathlib

namespace Submission.Helpers

open SimpleGraph Finset

/-- A pair of distinct adjacent vertices is a 2-clique. -/
lemma isNClique_pair_of_adj {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {a b : V} (h : G.Adj a b) : G.IsNClique 2 ({a, b} : Finset V) := by
  have h1 : G.IsNClique 1 ({b} : Finset V) := by simp
  simpa using h1.insert (a := a) (by simp [h])

/-- Existence of Ramsey numbers, parametrised by a bound on `r + s`. The IH
proceeds by ordinary induction on `k` so we can decrement either coordinate. -/
private theorem ramsey_aux : ∀ (k r s : ℕ), r + s ≤ k → 2 ≤ r → 2 ≤ s →
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset V),
      N ≤ T.card →
      (∃ K : Finset V, K ⊆ T ∧ G.IsNClique r K) ∨
        (∃ K : Finset V, K ⊆ T ∧ Gᶜ.IsNClique s K) := by
  intro k
  induction k with
  | zero =>
    intro r s _ hr hs; omega
  | succ k ih =>
    intro r s hrs hr hs
    rcases hr.eq_or_lt with hr2 | hr3
    · -- Base case: r = 2
      refine ⟨s, ?_⟩
      intro V _ G T hT
      by_cases hex : ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ G.Adj a b
      · left
        obtain ⟨a, ha, b, hb, hab, hadj⟩ := hex
        refine ⟨{a, b}, ?_, ?_⟩
        · intro x hx
          rw [mem_insert, mem_singleton] at hx
          rcases hx with rfl | rfl
          exacts [ha, hb]
        · simpa [← hr2] using isNClique_pair_of_adj hadj
      · right
        push Not at hex
        obtain ⟨K, hKT, hKcard⟩ := Finset.exists_subset_card_eq hT
        refine ⟨K, hKT, ?_, hKcard⟩
        intro a ha b hb hab
        rw [SimpleGraph.compl_adj]
        refine ⟨hab, hex a (hKT ha) b (hKT hb) hab⟩
    · rcases hs.eq_or_lt with hs2 | hs3
      · -- Base case: s = 2 (symmetric to r = 2)
        refine ⟨r, ?_⟩
        intro V _ G T hT
        by_cases hex : ∃ a ∈ T, ∃ b ∈ T, a ≠ b ∧ Gᶜ.Adj a b
        · right
          obtain ⟨a, ha, b, hb, hab, hadj⟩ := hex
          refine ⟨{a, b}, ?_, ?_⟩
          · intro x hx
            rw [mem_insert, mem_singleton] at hx
            rcases hx with rfl | rfl
            exacts [ha, hb]
          · simpa [← hs2] using isNClique_pair_of_adj hadj
        · left
          push Not at hex
          obtain ⟨K, hKT, hKcard⟩ := Finset.exists_subset_card_eq hT
          refine ⟨K, hKT, ?_, hKcard⟩
          intro a ha b hb hab
          have h := hex a (hKT ha) b (hKT hb) hab
          rw [SimpleGraph.compl_adj] at h
          push Not at h
          exact h hab
      · -- Inductive step: r ≥ 3, s ≥ 3
        have hr1 : 2 ≤ r - 1 := by omega
        have hs1 : 2 ≤ s - 1 := by omega
        have hsum1 : (r - 1) + s ≤ k := by omega
        have hsum2 : r + (s - 1) ≤ k := by omega
        obtain ⟨n₁, hn₁⟩ := ih (r - 1) s hsum1 hr1 hs
        obtain ⟨n₂, hn₂⟩ := ih r (s - 1) hsum2 hr hs1
        refine ⟨n₁ + n₂, ?_⟩
        intro V _ G T hT
        classical
        -- T is nonempty.
        have hTpos : 0 < T.card := by
          by_contra hzero
          push Not at hzero
          have hcardz : T.card = 0 := Nat.le_zero.mp hzero
          have hempty : T = ∅ := Finset.card_eq_zero.mp hcardz
          have hn1le : n₁ ≤ T.card := by omega
          rcases hn₁ G T hn1le with ⟨K, hK, hcl⟩ | ⟨K, hK, hcl⟩
          · subst hempty
            rw [Finset.subset_empty] at hK
            subst hK
            have := hcl.card_eq
            simp at this
            omega
          · subst hempty
            rw [Finset.subset_empty] at hK
            subst hK
            have := hcl.card_eq
            simp at this
            omega
        obtain ⟨v, hv⟩ : T.Nonempty := Finset.card_pos.mp hTpos
        -- Split T \ {v} into G-neighbours and G-non-neighbours of v.
        let TN : Finset V := (T.erase v).filter (fun x => G.Adj v x)
        let TM : Finset V := (T.erase v).filter (fun x => ¬ G.Adj v x)
        have hTN_sub : TN ⊆ T := fun x hx =>
          (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
        have hTM_sub : TM ⊆ T := fun x hx =>
          (Finset.mem_erase.mp (Finset.mem_filter.mp hx).1).2
        have hTN_no_v : v ∉ TN := fun hv' =>
          (Finset.mem_erase.mp (Finset.mem_filter.mp hv').1).1 rfl
        have hTM_no_v : v ∉ TM := fun hv' =>
          (Finset.mem_erase.mp (Finset.mem_filter.mp hv').1).1 rfl
        have hsplit : TN.card + TM.card = T.card - 1 := by
          have hpart : TN.card + TM.card = (T.erase v).card :=
            Finset.card_filter_add_card_filter_not (s := T.erase v) (fun x => G.Adj v x)
          rw [hpart, Finset.card_erase_of_mem hv]
        have hsum : T.card - 1 ≥ n₁ + n₂ - 1 := by omega
        by_cases hcase : n₁ ≤ TN.card
        · -- |TN| ≥ n₁: apply IH at (r - 1, s) on TN.
          rcases hn₁ G TN hcase with ⟨K, hKsub, hKcl⟩ | ⟨K, hKsub, hKcl⟩
          · -- (r-1)-clique in G inside TN: extend with v.
            left
            refine ⟨insert v K, ?_, ?_⟩
            · intro x hx
              rw [Finset.mem_insert] at hx
              rcases hx with rfl | hxK
              · exact hv
              · exact hTN_sub (hKsub hxK)
            · have hadj : ∀ b ∈ K, G.Adj v b := by
                intro b hb
                have := hKsub hb
                exact (Finset.mem_filter.mp this).2
              have := hKcl.insert hadj
              -- IsNClique ((r-1)+1) (insert v K) = IsNClique r (insert v K)
              have hreq : r - 1 + 1 = r := by omega
              rw [hreq] at this
              exact this
          · -- s-clique in Gᶜ inside TN ⊆ T.
            right
            exact ⟨K, hKsub.trans hTN_sub, hKcl⟩
        · -- |TN| < n₁, so |TM| ≥ n₂.
          have hTM_ge : n₂ ≤ TM.card := by omega
          rcases hn₂ G TM hTM_ge with ⟨K, hKsub, hKcl⟩ | ⟨K, hKsub, hKcl⟩
          · -- r-clique in G inside TM ⊆ T.
            left
            exact ⟨K, hKsub.trans hTM_sub, hKcl⟩
          · -- (s-1)-clique in Gᶜ inside TM: extend with v.
            right
            refine ⟨insert v K, ?_, ?_⟩
            · intro x hx
              rw [Finset.mem_insert] at hx
              rcases hx with rfl | hxK
              · exact hv
              · exact hTM_sub (hKsub hxK)
            · have hadj : ∀ b ∈ K, Gᶜ.Adj v b := by
                intro b hb
                have hbTM := hKsub hb
                rw [Finset.mem_filter] at hbTM
                obtain ⟨hbE, hbnotadj⟩ := hbTM
                rw [Finset.mem_erase] at hbE
                rw [SimpleGraph.compl_adj]
                exact ⟨fun heq => hbE.1 heq.symm, hbnotadj⟩
              have := hKcl.insert hadj
              have hreq : s - 1 + 1 = s := by omega
              rw [hreq] at this
              exact this

/-- The promised Ramsey existence statement: for `r, s ≥ 2` there is `N` such that
any graph on a finite set of size `≥ N` contains an `r`-clique in `G` or an
`s`-clique in `Gᶜ`. -/
theorem ramsey_subset (r s : ℕ) (hr : 2 ≤ r) (hs : 2 ≤ s) :
    ∃ N : ℕ, ∀ {V : Type} [DecidableEq V] (G : SimpleGraph V) (T : Finset V),
      N ≤ T.card →
      (∃ K : Finset V, K ⊆ T ∧ G.IsNClique r K) ∨
        (∃ K : Finset V, K ⊆ T ∧ Gᶜ.IsNClique s K) :=
  ramsey_aux (r + s) r s le_rfl hr hs

end Submission.Helpers
