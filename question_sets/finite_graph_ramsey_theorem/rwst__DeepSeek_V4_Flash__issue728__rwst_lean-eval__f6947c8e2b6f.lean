import Mathlib
import Submission.Helpers

open SimpleGraph
open Finset
open Classical

namespace Submission

theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  -- Base case r = 2: take n = s
  have h2r : ∀ s, 2 ≤ s → ∃ n, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree 2 ∨ ¬ Gᶜ.CliqueFree s := by
    intro s hs
    refine ⟨s, λ G => ?_⟩
    by_cases h : G.CliqueFree 2
    · right
      have h_no_edges : ∀ v w : Fin s, v ≠ w → ¬ G.Adj v w := by
        intro v w hne
        have hp : Set.univ.Pairwise (G.Adjᶜ) :=
          ((cliqueFreeOn_two (G := G) (s := Set.univ)).mp (by rwa [cliqueFreeOn_univ]))
        exact hp (Set.mem_univ v) (Set.mem_univ w) hne
      have h_compl_complete : Gᶜ = ⊤ := by
        ext v w
        rw [compl_adj, top_adj]
        constructor
        · intro ⟨hne, _⟩; exact hne
        · intro hne; exact ⟨hne, h_no_edges v w hne⟩
      have h_s_clique : (⊤ : SimpleGraph (Fin s)).IsNClique s (univ : Finset (Fin s)) := by
        rw [isNClique_iff]
        constructor
        · intro a ha b hb hne; simp [top_adj, hne]
        · simp
      have : Gᶜ.IsNClique s (univ : Finset (Fin s)) := by
        rw [h_compl_complete]
        exact h_s_clique
      intro hGc; apply hGc; exact this
    · left; exact h
  -- Base case s = 2: take n = r
  have h2s : ∀ r, 2 ≤ r → ∃ n, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree 2 := by
    intro r hr
    refine ⟨r, λ G => ?_⟩
    by_cases h : Gᶜ.CliqueFree 2
    · left
      have h_no_edges : ∀ v w : Fin r, v ≠ w → ¬ Gᶜ.Adj v w := by
        intro v w hne
        have hp : Set.univ.Pairwise ((Gᶜ).Adjᶜ) :=
          ((cliqueFreeOn_two (G := Gᶜ) (s := Set.univ)).mp (by rwa [cliqueFreeOn_univ]))
        exact hp (Set.mem_univ v) (Set.mem_univ w) hne
      have h_complete : G = ⊤ := by
        ext v w
        rw [top_adj]
        constructor
        · intro hG; exact hG.ne
        · intro hne
          have h_adj : ¬ Gᶜ.Adj v w := h_no_edges v w hne
          rw [compl_adj] at h_adj
          by_cases hG_adj : G.Adj v w
          · exact hG_adj
          · exfalso; apply h_adj; exact ⟨hne, hG_adj⟩
      have h_r_clique : (⊤ : SimpleGraph (Fin r)).IsNClique r (univ : Finset (Fin r)) := by
        rw [isNClique_iff]
        constructor
        · intro a ha b hb hne; simp [top_adj, hne]
        · simp
      have : G.IsNClique r (univ : Finset (Fin r)) := by
        rw [h_complete]
        exact h_r_clique
      intro hGr; apply hGr; exact this
    · right; exact h
  let induce_compl_embedding (V : Type) (G : SimpleGraph V) (s : Set V) : (G.induce s)ᶜ ↪g Gᶜ := {
    toFun := Subtype.val
    inj' := Subtype.val_injective
    map_rel_iff' := by
      intro x y
      simp [compl_adj, Subtype.val_injective.eq_iff]
  }
  intro r s hr hs
  -- Main induction: strong induction on r + s using the recurrence R(r,s) ≤ R(r-1,s) + R(r,s-1)
  let P (k : ℕ) : Prop := ∀ (r' s' : ℕ), 2 ≤ r' → 2 ≤ s' → r' + s' = k → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r' ∨ ¬ Gᶜ.CliqueFree s'
  have hP_base : P 0 := by
    intro r' s' hr' hs' hsum
    omega
  have hP_step : ∀ k, (∀ m < k, P m) → P k := by
    intro k IH r' s' hr' hs' hsum
    by_cases h2r' : r' = 2
    · subst h2r'; exact h2r s' hs'
    · by_cases h2s' : s' = 2
      · subst h2s'; exact h2s r' hr'
      · have h_rminus1_ge2 : 2 ≤ r' - 1 := by omega
        have h_sminus1_ge2 : 2 ≤ s' - 1 := by omega
        have h_lt1 : (r' - 1) + s' < k := by
          omega
        have h_lt2 : r' + (s' - 1) < k := by
          omega
        rcases IH ((r' - 1) + s') h_lt1 (r' - 1) s' h_rminus1_ge2 hs' rfl with ⟨n₁, h₁⟩
        rcases IH (r' + (s' - 1)) h_lt2 r' (s' - 1) hr' h_sminus1_ge2 rfl with ⟨n₂, h₂⟩
        have hpos : n₁ + n₂ ≠ 0 := by
          intro hzero
          have hn1_zero : n₁ = 0 := by omega
          subst hn1_zero
          let G0 : SimpleGraph (Fin 0) := ⊥
          rcases h₁ G0 with (h' | h')
          · apply h'
            intro t ht
            have hcard0 : t.card = 0 := by
              have huniv0 : (univ : Finset (Fin 0)).card = 0 := by simp
              have hle : t.card ≤ (univ : Finset (Fin 0)).card :=
                Finset.card_le_card (Finset.subset_univ _)
              omega
            have : t.card = r' - 1 := ht.card_eq
            omega
          · apply h'
            intro t ht
            have hcard0 : t.card = 0 := by
              have huniv0 : (univ : Finset (Fin 0)).card = 0 := by simp
              have hle : t.card ≤ (univ : Finset (Fin 0)).card :=
                Finset.card_le_card (Finset.subset_univ _)
              omega
            have : t.card = s' := ht.card_eq
            omega
        have hpos' : 0 < n₁ + n₂ := by omega
        refine ⟨n₁ + n₂, λ G => ?_⟩
        let v : Fin (n₁ + n₂) := ⟨0, hpos'⟩
        let N : Finset (Fin (n₁ + n₂)) := G.neighborFinset v
        let M : Finset (Fin (n₁ + n₂)) := ((univ : Finset (Fin (n₁ + n₂))).erase v).filter (λ u => ¬ G.Adj v u)
        have hcard_NM_add : N.card + M.card = n₁ + n₂ - 1 := by
          have hdisj : N ∩ M = ∅ := by
            ext u; simp [N, M, mem_inter, mem_filter, mem_erase, mem_neighborFinset]; tauto
          have hcover : N ∪ M = (univ : Finset (Fin (n₁ + n₂))).erase v := by
            ext u
            constructor
            · intro h
              rcases mem_union.mp h with (huN | huM)
              · rw [mem_neighborFinset] at huN
                have hne : u ≠ v := G.ne_of_adj huN.symm
                simp [hne, mem_erase, mem_univ]
              · rcases mem_filter.mp huM with ⟨hu_erase, hu_non_adj⟩
                simpa using hu_erase
            · intro h
              rcases mem_erase.mp h with ⟨hne, hu_univ⟩
              by_cases h_adj : G.Adj v u
              · apply mem_union_left; rw [mem_neighborFinset]; exact h_adj
              · apply mem_union_right; apply mem_filter.mpr
                exact ⟨mem_erase.mpr ⟨hne, mem_univ _⟩, h_adj⟩
          have hcard_union : (N ∪ M).card = N.card + M.card := by
            have hcard_eq := card_union_add_card_inter N M
            rw [hdisj, card_empty, add_zero] at hcard_eq
            omega
          calc
            N.card + M.card = (N ∪ M).card := by rw [hcard_union]
            _ = ((univ : Finset (Fin (n₁ + n₂))).erase v).card := by rw [hcover]
            _ = n₁ + n₂ - 1 := by simp
        by_cases hN_large : n₁ ≤ N.card
        · rcases exists_subset_card_eq hN_large with ⟨N', hN'_sub, hN'_card⟩
          have h_adj_all : ∀ u ∈ N', G.Adj v u := by
            intro u hu
            have huN : u ∈ N := hN'_sub hu
            dsimp [N] at huN; rw [mem_neighborFinset] at huN; exact huN
          let s_set : Set (Fin (n₁ + n₂)) := N'
          have hcard_s' : Fintype.card s_set = n₁ := by
            simpa [s_set] using hN'_card
          have : Fintype.card s_set = N'.card := by
            simp [s_set]
          have hcard_s'_finset : N'.card = n₁ := hN'_card
          let e : s_set ≃ Fin n₁ :=
            (Fintype.equivFin s_set).trans (Equiv.cast (by rw [hcard_s']))
          have e_inj : Function.Injective e.symm := e.symm.injective
          let H₁ : SimpleGraph (Fin n₁) := SimpleGraph.comap e.symm (G.induce s_set)
          rcases h₁ H₁ with (hH₁ | hH₁c)
          · have h_not_cf : ¬ H₁.CliqueFree (r' - 1) := hH₁
            have h_exists : ∃ t, H₁.IsNClique (r' - 1) t := by
              simpa [CliqueFree] using h_not_cf
            rcases h_exists with ⟨t, ht⟩
            have hinduce_clique : (G.induce s_set).IsNClique (r' - 1) (t.map ⟨e.symm, e_inj⟩) := by
              rw [isNClique_iff]
              rcases ht with ⟨ht_clique, ht_card⟩
              constructor
              · intro a ha b hb hne
                rcases mem_map.mp ha with ⟨x, hx, rfl⟩
                rcases mem_map.mp hb with ⟨y, hy, rfl⟩
                have hxy_ne : x ≠ y := by
                  intro h; apply hne; simp [h]
                have hxy_adj : H₁.Adj x y := ht_clique (by simpa using hx) (by simpa using hy) hxy_ne
                simpa [H₁, SimpleGraph.comap_adj] using hxy_adj
              · simp [ht_card]
            have hG_clique : G.IsNClique (r' - 1) ((t.map ⟨e.symm, e_inj⟩).map (.subtype _)) := by
              rw [← isNClique_induce_iff s_set (t.map ⟨e.symm, e_inj⟩) (r' - 1)]
              exact hinduce_clique
            have h_adj_all' : ∀ b ∈ ((t.map ⟨e.symm, e_inj⟩).map (.subtype _)), G.Adj v b := by
              intro b hb
              rcases mem_map.mp hb with ⟨a, ha, rfl⟩
              have ha_val_N' : (a : Fin (n₁ + n₂)) ∈ N' := by
                simpa [s_set] using a.property
              exact h_adj_all (a : Fin (n₁ + n₂)) ha_val_N'
            have hv_not_mem : v ∉ ((t.map ⟨e.symm, e_inj⟩).map (.subtype _)) := by
              intro hmem
              rcases mem_map.mp hmem with ⟨a, ha, ha_eq⟩
              have ha_val_N' : (a : Fin (n₁ + n₂)) ∈ N' := by
                simpa [s_set] using a.property
              have hv_not_N' : v ∉ N' := by
                intro hvN'
                have h_adj_vv : G.Adj v v := h_adj_all v hvN'
                exact G.loopless.irrefl v h_adj_vv
              apply hv_not_N'
              rw [← ha_eq]
              exact ha_val_N'
            have h_r_clique : G.IsNClique r' (insert v ((t.map ⟨e.symm, e_inj⟩).map (.subtype _))) := by
              have : (r' - 1) + 1 = r' := by omega
              have h_insert := hG_clique.insert (by
                intro b hb
                have : b ∈ ((t.map ⟨e.symm, e_inj⟩).map (.subtype _)) := by
                  simpa [mem_insert, hv_not_mem] using hb
                exact h_adj_all' b this)
              simpa [this] using h_insert
            left
            intro hG_cf; apply hG_cf; exact h_r_clique
          · have h_not_cf : ¬ H₁ᶜ.CliqueFree s' := hH₁c
            have h_exists : ∃ t, H₁ᶜ.IsNClique s' t := by
              simpa [CliqueFree] using h_not_cf
            rcases h_exists with ⟨t, ht⟩
            have hinduce_compl_clique : (G.induce s_set)ᶜ.IsNClique s' (t.map ⟨e.symm, e_inj⟩) := by
              rw [isNClique_iff]
              rcases ht with ⟨ht_clique, ht_card⟩
              constructor
              · intro a ha b hb hne
                rcases mem_map.mp ha with ⟨x, hx, rfl⟩
                rcases mem_map.mp hb with ⟨y, hy, rfl⟩
                have hxy_ne : x ≠ y := by
                  intro h; apply hne; simp [h]
                have hxy_adj : H₁ᶜ.Adj x y := ht_clique (by simpa using hx) (by simpa using hy) hxy_ne
                simpa [H₁, SimpleGraph.comap_adj, compl_adj, induce_adj, Subtype.val_injective.eq_iff]
                  using hxy_adj
              · simp [ht_card]
            let emb : (G.induce s_set)ᶜ ↪g Gᶜ := induce_compl_embedding _ G s_set
            have hGc_clique : Gᶜ.IsNClique s' ((t.map ⟨e.symm, e_inj⟩).map emb.toEmbedding) := by
              rw [isNClique_iff]
              rcases hinduce_compl_clique with ⟨hclique, hcard⟩
              constructor
              · intro a ha b hb hne
                rcases mem_map.mp ha with ⟨x, hx, rfl⟩
                rcases mem_map.mp hb with ⟨y, hy, rfl⟩
                have hxy_ne : x ≠ y := by
                  intro h; apply hne; simp [h]
                have hxy_adj : (G.induce s_set)ᶜ.Adj x y := hclique (by simpa using hx) (by simpa using hy) hxy_ne
                simpa using (emb.map_rel_iff'.mpr hxy_adj)
              · simp [hcard, Finset.card_map emb.toEmbedding]
            right
            intro hGc_cf; apply hGc_cf; exact hGc_clique
        · have hM_large : n₂ ≤ M.card := by
            by_contra! hM_small
            omega
          rcases exists_subset_card_eq hM_large with ⟨M', hM'_sub, hM'_card⟩
          have h_non_adj_all : ∀ u ∈ M', ¬ G.Adj v u := by
            intro u hu
            have huM : u ∈ M := hM'_sub hu
            dsimp [M] at huM
            rcases mem_filter.mp huM with ⟨hu_erase, hu_non_adj⟩
            exact hu_non_adj
          let t_set : Set (Fin (n₁ + n₂)) := M'
          have hcard_t' : Fintype.card t_set = n₂ := by
            simpa [t_set] using hM'_card
          have : Fintype.card t_set = M'.card := by
            simp [t_set]
          let e : t_set ≃ Fin n₂ :=
            (Fintype.equivFin t_set).trans (Equiv.cast (by rw [hcard_t']))
          have e_inj : Function.Injective e.symm := e.symm.injective
          let H₂ : SimpleGraph (Fin n₂) := SimpleGraph.comap e.symm (G.induce t_set)
          rcases h₂ H₂ with (hH₂ | hH₂c)
          · have h_not_cf : ¬ H₂.CliqueFree r' := hH₂
            have h_exists : ∃ cl, H₂.IsNClique r' cl := by
              simpa [CliqueFree] using h_not_cf
            rcases h_exists with ⟨cl, hcl⟩
            have hinduce_clique : (G.induce t_set).IsNClique r' (cl.map ⟨e.symm, e_inj⟩) := by
              rw [isNClique_iff]
              rcases hcl with ⟨hcl_clique, hcl_card⟩
              constructor
              · intro a ha b hb hne
                rcases mem_map.mp ha with ⟨x, hx, rfl⟩
                rcases mem_map.mp hb with ⟨y, hy, rfl⟩
                have hxy_ne : x ≠ y := by
                  intro h; apply hne; simp [h]
                have hxy_adj : H₂.Adj x y := hcl_clique (by simpa using hx) (by simpa using hy) hxy_ne
                simpa [H₂, SimpleGraph.comap_adj] using hxy_adj
              · simp [hcl_card]
            have hG_clique : G.IsNClique r' ((cl.map ⟨e.symm, e_inj⟩).map (.subtype _)) := by
              rw [← isNClique_induce_iff t_set (cl.map ⟨e.symm, e_inj⟩) r']
              exact hinduce_clique
            left
            intro hG_cf; apply hG_cf; exact hG_clique
          · have h_not_cf : ¬ H₂ᶜ.CliqueFree (s' - 1) := hH₂c
            have h_exists : ∃ cl, H₂ᶜ.IsNClique (s' - 1) cl := by
              simpa [CliqueFree] using h_not_cf
            rcases h_exists with ⟨cl, hcl⟩
            have hinduce_compl_clique : (G.induce t_set)ᶜ.IsNClique (s' - 1) (cl.map ⟨e.symm, e_inj⟩) := by
              rw [isNClique_iff]
              rcases hcl with ⟨hcl_clique, hcl_card⟩
              constructor
              · intro a ha b hb hne
                rcases mem_map.mp ha with ⟨x, hx, rfl⟩
                rcases mem_map.mp hb with ⟨y, hy, rfl⟩
                have hxy_ne : x ≠ y := by
                  intro h; apply hne; simp [h]
                have hxy_adj : H₂ᶜ.Adj x y := hcl_clique (by simpa using hx) (by simpa using hy) hxy_ne
                simpa [H₂, SimpleGraph.comap_adj, compl_adj, induce_adj, Subtype.val_injective.eq_iff]
                  using hxy_adj
              · simp [hcl_card]
            let emb : (G.induce t_set)ᶜ ↪g Gᶜ := induce_compl_embedding _ G t_set
            let cl0 : Finset (Fin (n₁ + n₂)) := (cl.map ⟨e.symm, e_inj⟩).map emb.toEmbedding
            have hGc_clique : Gᶜ.IsNClique (s' - 1) cl0 := by
              rw [isNClique_iff]
              rcases hinduce_compl_clique with ⟨hclique, hcard⟩
              constructor
              · intro a ha b hb hne
                rcases mem_map.mp ha with ⟨x, hx, rfl⟩
                rcases mem_map.mp hb with ⟨y, hy, rfl⟩
                have hxy_ne : x ≠ y := by
                  intro h; apply hne; simp [h]
                have hxy_adj : (G.induce t_set)ᶜ.Adj x y := hclique (by simpa using hx) (by simpa using hy) hxy_ne
                simpa using (emb.map_rel_iff'.mpr hxy_adj)
              · simp [cl0, hcard, Finset.card_map emb.toEmbedding]
            have hv_not_M' : v ∉ M' := by
              intro hvM'
              have hvM : v ∈ M := hM'_sub hvM'
              dsimp [M] at hvM
              rcases mem_filter.mp hvM with ⟨hv_erase, hv_non_adj⟩
              have : v ≠ v := (mem_erase.mp hv_erase).1
              exact this rfl
            have h_adj_compl_all : ∀ u ∈ cl0, Gᶜ.Adj v u := by
              intro u hu
              rcases mem_map.mp hu with ⟨a, ha, rfl⟩
              have ha_val_M' : (a : Fin (n₁ + n₂)) ∈ M' := by
                simpa [t_set] using a.property
              have h_non_adj : ¬ G.Adj v (a : Fin (n₁ + n₂)) := h_non_adj_all (a : Fin (n₁ + n₂)) ha_val_M'
              have ha_ne_v : (a : Fin (n₁ + n₂)) ≠ v := by
                intro h; apply hv_not_M'; rw [← h]; exact ha_val_M'
              rw [compl_adj]
              have h_eq : emb.toEmbedding a = (a : Fin (n₁ + n₂)) := by
                dsimp [emb]
                rfl
              rw [h_eq]
              exact ⟨ha_ne_v.symm, h_non_adj⟩
            have hv_not_mem_cl0 : v ∉ cl0 := by
              intro hmem
              rcases mem_map.mp hmem with ⟨a, ha, ha_eq⟩
              have ha_val_M' : (a : Fin (n₁ + n₂)) ∈ M' := by
                simpa [t_set] using a.property
              apply hv_not_M'
              rw [← ha_eq]
              have h_eq : emb.toEmbedding a = (a : Fin (n₁ + n₂)) := by
                dsimp [emb]
                rfl
              rw [h_eq]
              exact ha_val_M'
            have h_s_clique : Gᶜ.IsNClique s' (insert v cl0) := by
              have : (s' - 1) + 1 = s' := by omega
              have h_insert := hGc_clique.insert (by
                intro b hb
                have : b ∈ cl0 := by
                  simpa [mem_insert, hv_not_mem_cl0] using hb
                exact h_adj_compl_all b this)
              simpa [this] using h_insert
            right
            intro hGc_cf; apply hGc_cf; exact h_s_clique
  have h_all : ∀ k, P k := λ k =>
    Nat.strong_induction_on k (λ m IH => hP_step m IH)
  exact h_all (r + s) r s hr hs rfl

end Submission
