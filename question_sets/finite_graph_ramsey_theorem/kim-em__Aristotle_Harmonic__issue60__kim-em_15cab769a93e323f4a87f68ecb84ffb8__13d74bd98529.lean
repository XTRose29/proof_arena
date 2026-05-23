/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: finite_graph_ramsey_theorem
user: kim-em
model: Aristotle (Harmonic)
submission_repo: kim-em/15cab769a93e323f4a87f68ecb84ffb8
submission_ref: 13d74bd985294975f54a1457633364117c38f840
issue_number: 60
-/
import Mathlib

open SimpleGraph

namespace Submission

set_option maxHeartbeats 800000 in
theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r s hr hs;
  by_contra! h;
  -- We proceed by strong induction on $r + s$.
  induction' r using Nat.strong_induction_on with r ih generalizing s;
  induction' s using Nat.strong_induction_on with s ih';
  -- Consider the graph $G$ on $n = n_1 + n_2$ vertices, where $n_1$ and $n_2$ are the witnesses for $r-1$ and $s$, and $r$ and $s-1$ respectively.
  obtain ⟨n1, hn1⟩ : ∃ n1, ∀ G : SimpleGraph (Fin n1), ¬G.CliqueFree (r - 1) ∨ ¬Gᶜ.CliqueFree s := by
    by_cases hr1 : r - 1 ≥ 2;
    · exact not_forall_not.mp fun contra => ih ( r - 1 ) ( Nat.pred_lt ( ne_bot_of_gt hr ) ) s hr1 hs fun n => by aesop;
    · interval_cases _ : r - 1 <;> simp_all +decide;
      exact ⟨ 1, fun G => Or.inl ⟨ 0 ⟩ ⟩
  obtain ⟨n2, hn2⟩ : ∃ n2, ∀ G : SimpleGraph (Fin n2), ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree (s - 1) := by
    by_cases hs' : 2 ≤ s - 1;
    · exact not_forall_not.mp fun contra => ih' ( s - 1 ) ( Nat.sub_lt ( by linarith ) ( by linarith ) ) hs' fun n => by push Not at *; tauto;
    · interval_cases _ : s - 1 <;> simp_all +decide;
      exact ⟨ 1, fun G => Or.inr ⟨ 0 ⟩ ⟩
  set n := n1 + n2 + 1 with hn_def;
  obtain ⟨ G, hG₁, hG₂ ⟩ := h n;
  -- Consider the vertex $v$ in $G$ with the maximum degree.
  obtain ⟨v, hv⟩ : ∃ v : Fin n, (G.neighborFinset v).card ≥ n1 ∨ (Gᶜ.neighborFinset v).card ≥ n2 := by
    have h_deg : ∀ v : Fin n, (G.neighborFinset v).card + (Gᶜ.neighborFinset v).card = n - 1 := by
      intro v; rw [ ← Finset.card_union_of_disjoint ];
      · convert Finset.card_erase_of_mem ( Finset.mem_univ v ) using 2 ; ext w ; by_cases hw : G.Adj v w <;> aesop;
        simp +decide [ hn_def ];
      · simp +contextual [ Finset.disjoint_left, SimpleGraph.neighborFinset ];
    exact ⟨ ⟨ 0, Nat.succ_pos _ ⟩, Classical.or_iff_not_imp_left.2 fun h => by linarith [ h_deg ⟨ 0, Nat.succ_pos _ ⟩, Nat.sub_add_cancel ( show 1 ≤ n from Nat.succ_pos _ ) ] ⟩;
  cases' hv with hv hv;
  · -- Let $A$ be the set of neighbors of $v$ in $G$.
    obtain ⟨A, hA⟩ : ∃ A : Finset (Fin n), A ⊆ G.neighborFinset v ∧ A.card = n1 := by
      exact Finset.le_card_iff_exists_subset_card.mp hv;
    -- Consider the subgraph $G[A]$ induced by $A$.
    set GA : SimpleGraph (Fin n1) := SimpleGraph.fromRel (fun i j => G.Adj (A.orderEmbOfFin hA.right i) (A.orderEmbOfFin hA.right j)) with hGA_def;
    cases' hn1 GA with hGA hGA <;> simp_all +decide [ SimpleGraph.CliqueFree ];
    · obtain ⟨ x, hx ⟩ := hGA;
      refine' hG₁ ( Finset.image ( fun i => A.orderEmbOfFin hA.2 i ) x ∪ { v } ) _;
      simp_all +decide [ SimpleGraph.isNClique_iff ];
      refine' ⟨ ⟨ _, _ ⟩, _ ⟩;
      · intro a ha b hb hab; simp_all +decide [ SimpleGraph.isClique_iff, SimpleGraph.fromRel ] ;
        obtain ⟨ i, hi, rfl ⟩ := ha; obtain ⟨ j, hj, rfl ⟩ := hb; specialize hx; have := hx.1 hi hj; simp_all +decide [ SimpleGraph.adj_comm ] ;
      · exact fun i hi hi' => by have := hA.1 ( Finset.orderEmbOfFin_mem A hA.2 i ) ; aesop;
      · rw [ Finset.card_insert_of_notMem ] <;> norm_num [ hx.2 ];
        · rw [ Finset.card_image_of_injective _ fun i j hij => by simpa [ Fin.ext_iff ] using hij, hx.2, Nat.sub_add_cancel ( by linarith ) ];
        · intro i hi; have := hA.1 ( Finset.orderEmbOfFin_mem A hA.2 i ) ; aesop;
    · obtain ⟨ t, ht ⟩ := hGA;
      refine' hG₂ ( Finset.image ( fun i => A.orderEmbOfFin hA.2 i ) t ) _;
      simp_all +decide [ SimpleGraph.isNIndepSet_iff ];
      simp_all +decide [ SimpleGraph.IsIndepSet, Finset.card_image_of_injective, Function.Injective ];
      intro x hx y hy hxy; simp_all +decide [ SimpleGraph.adj_comm ] ;
      obtain ⟨ i, hi, rfl ⟩ := hx; obtain ⟨ j, hj, rfl ⟩ := hy; specialize ht; have := ht.1 hi hj; aesop;
  · -- Consider the subgraph $H$ of $G$ induced by the neighbors of $v$ in $Gᶜ$.
    obtain ⟨H, hH⟩ : ∃ H : Finset (Fin n), H.card = n2 ∧ ∀ u ∈ H, u ≠ v ∧ Gᶜ.Adj u v := by
      obtain ⟨ H, hH ⟩ := Finset.exists_subset_card_eq hv;
      exact ⟨ H, hH.2, fun u hu => ⟨ by rintro rfl; exact absurd ( hH.1 hu ) ( by simp +decide [ SimpleGraph.neighborFinset_def ] ), by simpa [ SimpleGraph.adj_comm ] using hH.1 hu ⟩ ⟩;
    obtain ⟨H', hH'⟩ : ∃ H' : SimpleGraph (Fin n2), (H'.CliqueFree r ∧ H'ᶜ.CliqueFree (s - 1)) := by
      have h_subgraph : ∃ f : Fin n2 → Fin n, Function.Injective f ∧ ∀ i, f i ∈ H := by
        exact ⟨ fun i => H.orderEmbOfFin ( by aesop ) i, by aesop_cat, fun i => by aesop ⟩
      obtain ⟨ f, hf₁, hf₂ ⟩ := h_subgraph;
      use SimpleGraph.comap f G;
      constructor;
      · intro t ht;
        have := hG₁ ( Finset.image f t ) ?_;
        · exact this;
        · simp_all +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective _ hf₁ ];
          intro x hx y hy; aesop;
      · intro t ht;
        have h_clique : (SimpleGraph.comap f G)ᶜ.IsNClique (s - 1) t → Gᶜ.IsNClique (s - 1) (Finset.image f t) := by
          simp +decide [ SimpleGraph.isNClique_iff, Finset.card_image_of_injective _ hf₁ ];
          simp +decide [ SimpleGraph.IsIndepSet, Set.Pairwise ];
          exact fun h₁ h₂ => ⟨ fun x hx y hy hxy => h₁ hx hy ( by simpa [ hf₁.eq_iff ] using hxy ), h₂ ⟩;
        have h_clique : Gᶜ.IsNClique s (Finset.image f t ∪ {v}) := by
          simp_all +decide [ SimpleGraph.isNClique_iff ];
          simp_all +decide [ SimpleGraph.IsIndepSet, Set.Pairwise ];
          exact ⟨ fun x hx hx' => by have := hH.2 ( f x ) ( hf₂ x ) ; tauto, Nat.succ_pred_eq_of_pos ( pos_of_gt hs ) ⟩;
        exact hG₂ _ h_clique;
    cases hn2 H' <;> tauto

end Submission