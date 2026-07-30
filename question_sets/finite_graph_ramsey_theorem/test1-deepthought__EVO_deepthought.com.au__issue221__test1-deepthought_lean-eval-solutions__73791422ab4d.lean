import Mathlib
open SimpleGraph
open Finset

set_option autoImplicit false

namespace Submission

theorem finite_graph_ramsey_theorem : ∀ (r s : ℕ), 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r s hr hs
  let P (k : ℕ) : Prop :=
    ∀ (r' s' : ℕ), r' + s' = k → 2 ≤ r' → 2 ≤ s' → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r' ∨ ¬ Gᶜ.CliqueFree s'
  
  have hP : ∀ (k : ℕ), (∀ m < k, P m) → P k := by
    intro k IH r' s' hsum hr' hs'
    by_cases hsum4 : r' + s' = 4
    · have hr2 : r' = 2 := by omega
      have hs2 : s' = 2 := by omega
      subst hr2 hs2
      refine ⟨2, λ G => ?_⟩
      by_cases hG : G.CliqueFree 2
      · right
        rw [SimpleGraph.cliqueFree_compl]
        intro hind
        have h0_ne_1 : (0 : Fin 2) ≠ 1 := by decide
        have hind_pair : G.IsNIndepSet 2 ({(0 : Fin 2), 1} : Finset (Fin 2)) := by
          apply SimpleGraph.IsNIndepSet.mk
          · rw [SimpleGraph.isIndepSet_iff]
            intro x hx y hy hne
            intro hadj
            apply hG ({x, y} : Finset (Fin 2))
            refine SimpleGraph.IsNClique.mk ?_ ?_
            · rw [SimpleGraph.isClique_iff]
              intro u hu v hv hne''
              have hu_cases : u = x ∨ u = y := by simpa using hu
              have hv_cases : v = x ∨ v = y := by simpa using hv
              rcases hu_cases with (rfl|rfl)
              · rcases hv_cases with (rfl|rfl)
                · exfalso; exact hne'' rfl
                · exact hadj
              · rcases hv_cases with (rfl|rfl)
                · exact hadj.symm
                · exfalso; exact hne'' rfl
            · simp [hne]
          · simp
        exact hind ({(0 : Fin 2), 1}) hind_pair
      · left; exact hG
    · by_cases hr2 : r' = 2
      · subst hr2
        refine ⟨s', λ G => ?_⟩
        by_cases hG : G.CliqueFree 2
        · right
          rw [SimpleGraph.cliqueFree_compl]
          intro hind
          have h_indep_univ : G.IsNIndepSet s' (Finset.univ : Finset (Fin s')) := by
            apply SimpleGraph.IsNIndepSet.mk
            · rw [SimpleGraph.isIndepSet_iff]
              intro x hx y hy hne
              intro hadj
              apply hG ({x, y} : Finset (Fin s'))
              refine SimpleGraph.IsNClique.mk ?_ ?_
              · rw [SimpleGraph.isClique_iff]
                intro u hu v hv hne''
                have hu_cases : u = x ∨ u = y := by simpa using hu
                have hv_cases : v = x ∨ v = y := by simpa using hv
                rcases hu_cases with (rfl|rfl)
                · rcases hv_cases with (rfl|rfl)
                  · exfalso; exact hne'' rfl
                  · exact hadj
                · rcases hv_cases with (rfl|rfl)
                  · exact hadj.symm
                  · exfalso; exact hne'' rfl
              · simp [hne]
            · simp
          exact hind (Finset.univ : Finset (Fin s')) h_indep_univ
        · left; exact hG
      · by_cases hs2 : s' = 2
        · subst hs2
          refine ⟨r', λ G => ?_⟩
          by_cases hG : G.CliqueFree r'
          · right
            rw [SimpleGraph.cliqueFree_compl]
            intro hind
            have h_all_edges : ∀ (x y : Fin r'), x ≠ y → G.Adj x y := by
              intro x y hne
              by_contra! hadj
              apply hind ({x, y} : Finset (Fin r'))
              refine SimpleGraph.IsNIndepSet.mk ?_ ?_
              · rw [SimpleGraph.isIndepSet_iff]
                intro u hu v hv hne''
                have hu_cases : u = x ∨ u = y := by simpa using hu
                have hv_cases : v = x ∨ v = y := by simpa using hv
                rcases hu_cases with (rfl|rfl)
                · rcases hv_cases with (rfl|rfl)
                  · exfalso; exact hne'' rfl
                  · exact hadj
                · rcases hv_cases with (rfl|rfl)
                  · intro h; apply hadj; exact h.symm
                  · exfalso; exact hne'' rfl
              · simp [hne]
            have h_clique_univ : G.IsNClique r' (Finset.univ : Finset (Fin r')) := by
              refine SimpleGraph.IsNClique.mk ?_ ?_
              · rw [SimpleGraph.isClique_iff]
                intro x hx y hy hne
                exact h_all_edges x y hne
              · simp
            exact hG (Finset.univ : Finset (Fin r')) h_clique_univ
          · left; exact hG
        · have hrm1 : 2 ≤ r' - 1 := by omega
          have hsm1 : 2 ≤ s' - 1 := by omega
          have h_lt_rm1 : (r'-1) + s' < k := by rw [← hsum]; omega
          have h_lt_sm1 : r' + (s'-1) < k := by rw [← hsum]; omega
          have hP_rm1_s : P ((r'-1) + s') := IH ((r'-1) + s') h_lt_rm1
          have hP_r_sm1 : P (r' + (s'-1)) := IH (r' + (s'-1)) h_lt_sm1
          obtain ⟨n1, h1⟩ := hP_rm1_s (r'-1) s' (by omega) hrm1 hs'
          obtain ⟨n2, h2⟩ := hP_r_sm1 r' (s'-1) (by omega) hr' hsm1
          refine ⟨n1 + n2, λ G => ?_⟩
          
          have hpos : 0 < n1 + n2 := by
            by_contra! hzero
            have hn1 : n1 = 0 := by omega
            have hn2 : n2 = 0 := by omega
            subst hn1 hn2
            let G0 : SimpleGraph (Fin 0) := ⊥
            have h_cf : G0.CliqueFree (r'-1) := by
              intro t ht; exfalso
              have hcard : t.card = r'-1 := ht.card_eq
              have hcard0 : t.card = 0 := by
                have : t ⊆ (Finset.univ : Finset (Fin 0)) := Finset.subset_univ _
                have huniv0 : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
                have hle : t.card ≤ (Finset.univ : Finset (Fin 0)).card := Finset.card_le_card this
                omega
              omega
            have h_cf_compl : G0ᶜ.CliqueFree s' := by
              intro t ht; exfalso
              have hcard : t.card = s' := ht.card_eq
              have hcard0 : t.card = 0 := by
                have : t ⊆ (Finset.univ : Finset (Fin 0)) := Finset.subset_univ _
                have huniv0 : (Finset.univ : Finset (Fin 0)).card = 0 := by simp
                have hle : t.card ≤ (Finset.univ : Finset (Fin 0)).card := Finset.card_le_card this
                omega
              omega
            rcases h1 G0 with (h | h)
            · exact h h_cf
            · exact h h_cf_compl
          
          let v : Fin (n1 + n2) := ⟨0, hpos⟩
          classical
          let A : Finset (Fin (n1 + n2)) := filter (λ u => G.Adj v u) (Finset.univ.erase v)
          let B : Finset (Fin (n1 + n2)) := filter (λ u => ¬G.Adj v u) (Finset.univ.erase v)
          
          have h_union : A ∪ B = Finset.univ.erase v := by
            apply Finset.Subset.antisymm
            · apply Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
            · intro u hu
              have hne : u ≠ v := (Finset.mem_erase.mp hu).1
              by_cases hadj : G.Adj v u
              · apply Finset.mem_union_left; apply Finset.mem_filter.mpr; exact ⟨hu, hadj⟩
              · apply Finset.mem_union_right; apply Finset.mem_filter.mpr; exact ⟨hu, hadj⟩
          
          have h_disjoint : A ∩ B = ∅ := by
            apply Finset.not_nonempty_iff_eq_empty.mp
            intro h_nonempty
            obtain ⟨u, hu⟩ := h_nonempty
            have huA : u ∈ A := (Finset.mem_inter.mp hu).left
            have huB : u ∈ B := (Finset.mem_inter.mp hu).right
            have hadj : G.Adj v u := (Finset.mem_filter.mp huA).2
            have h_not_adj : ¬G.Adj v u := (Finset.mem_filter.mp huB).2
            exact h_not_adj hadj
          
          have h_total : (Finset.univ.erase v).card = n1 + n2 - 1 := by simp
          
          have h_card_A_B : A.card + B.card = n1 + n2 - 1 := by
            have hcard_union : (A ∪ B).card = A.card + B.card := by
              have h := Finset.card_union_add_card_inter A B
              rw [h_disjoint, Finset.card_empty, add_zero] at h
              omega
            calc
              A.card + B.card = (A ∪ B).card := by rw [hcard_union]
              _ = (Finset.univ.erase v).card := by rw [h_union]
              _ = n1 + n2 - 1 := h_total
          
          by_cases hA : A.card ≥ n1
          · obtain ⟨A', hA'_sub, hA'_card⟩ := Finset.exists_subset_card_eq hA
            let f_emb : Fin n1 ↪ Fin (n1 + n2) :=
              (Finset.orderEmbOfFin A' hA'_card).toEmbedding
            let H : SimpleGraph (Fin n1) := SimpleGraph.comap f_emb G
            
            have h1H : ¬ H.CliqueFree (r'-1) ∨ ¬ Hᶜ.CliqueFree s' := h1 H
            rcases h1H with (hH | hH_compl)
            · have hH_clique : ∃ (t : Finset (Fin n1)), H.IsNClique (r'-1) t := by
                rw [SimpleGraph.CliqueFree] at hH; push Not at hH; exact hH
              obtain ⟨t, ht⟩ := hH_clique
              have h_clique_img : G.IsNClique (r'-1) (image f_emb t) := by
                refine SimpleGraph.IsNClique.mk ?_ ?_
                · rw [SimpleGraph.isClique_iff]
                  intro x hx y hy hne
                  obtain ⟨a, ha, rfl⟩ := mem_image.mp (by simpa using hx)
                  obtain ⟨b, hb, rfl⟩ := mem_image.mp (by simpa using hy)
                  have hne_ab : a ≠ b := by
                    intro h_eq; apply hne; rw [h_eq]
                  have h_clique := ht.isClique
                  rw [SimpleGraph.isClique_iff] at h_clique
                  have hadj : H.Adj a b := h_clique ha hb hne_ab
                  simpa [H, SimpleGraph.comap] using hadj
                · calc
                    (image f_emb t).card = t.card := Finset.card_image_of_injective _ f_emb.injective
                    _ = r'-1 := ht.card_eq
              have h_adj_all : ∀ x ∈ image f_emb t, G.Adj v x := by
                intro x hx
                obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
                have hi_A' : f_emb i ∈ A' := Finset.orderEmbOfFin_mem _ _ _
                have hi_A : f_emb i ∈ A := hA'_sub hi_A'
                simp [A] at hi_A; exact hi_A.2
              have hv_not_mem : v ∉ image f_emb t := by
                intro h
                obtain ⟨i, hi, h_eq⟩ := mem_image.mp h
                have hi_A' : f_emb i ∈ A' := Finset.orderEmbOfFin_mem _ _ _
                have hi_A : f_emb i ∈ A := hA'_sub hi_A'
                simp [A] at hi_A
                have hne : f_emb i ≠ v := hi_A.1
                exact hne (h_eq.symm ▸ rfl)
              have h_clique_v : G.IsNClique r' (insert v (image f_emb t)) := by
                refine SimpleGraph.IsNClique.mk ?_ ?_
                · rw [SimpleGraph.isClique_iff]
                  intro x hx y hy hne
                  have hx_cases : x = v ∨ x ∈ (image f_emb t : Set (Fin (n1 + n2))) := by
                    simpa using hx
                  have hy_cases : y = v ∨ y ∈ (image f_emb t : Set (Fin (n1 + n2))) := by
                    simpa using hy
                  rcases hx_cases with (rfl | hx_img)
                  · rcases hy_cases with (rfl | hy_img)
                    · exfalso; exact hne rfl
                    · exact h_adj_all y (by simpa using hy_img)
                  · rcases hy_cases with (rfl | hy_img)
                    · exact (h_adj_all x (by simpa using hx_img)).symm
                    · have h_clique := h_clique_img.isClique
                      rw [SimpleGraph.isClique_iff] at h_clique
                      exact h_clique (by simpa using hx_img) (by simpa using hy_img) hne
                · have hcard : (image f_emb t).card = r'-1 := h_clique_img.card_eq
                  simp [hcard, hv_not_mem]
                  omega
              left
              exact λ hG_cf => hG_cf (insert v (image f_emb t)) h_clique_v
            · have hH_compl_clique : ∃ (t : Finset (Fin n1)), Hᶜ.IsNClique s' t := by
                rw [SimpleGraph.CliqueFree] at hH_compl; push Not at hH_compl; exact hH_compl
              obtain ⟨t, ht⟩ := hH_compl_clique
              have h_clique_compl_img : Gᶜ.IsNClique s' (image f_emb t) := by
                refine SimpleGraph.IsNClique.mk ?_ ?_
                · rw [SimpleGraph.isClique_iff]
                  intro x hx y hy hne
                  obtain ⟨a, ha, rfl⟩ := mem_image.mp (by simpa using hx)
                  obtain ⟨b, hb, rfl⟩ := mem_image.mp (by simpa using hy)
                  have hne_ab : a ≠ b := by
                    intro h_eq; apply hne; rw [h_eq]
                  have h_clique := ht.isClique
                  rw [SimpleGraph.isClique_iff] at h_clique
                  have hadj : Hᶜ.Adj a b := h_clique ha hb hne_ab
                  rw [SimpleGraph.compl_adj] at hadj
                  obtain ⟨hne_ab', h_not_adj⟩ := hadj
                  rw [SimpleGraph.compl_adj]
                  refine ⟨by
                    intro h_eq_f; apply hne_ab'; exact f_emb.injective h_eq_f, h_not_adj⟩
                · calc
                    (image f_emb t).card = t.card := Finset.card_image_of_injective _ f_emb.injective
                    _ = s' := ht.card_eq
              right
              exact λ hG_cf => hG_cf (image f_emb t) h_clique_compl_img
          
          · have hB : B.card ≥ n2 := by
              have : A.card + B.card = n1 + n2 - 1 := h_card_A_B
              omega
            obtain ⟨B', hB'_sub, hB'_card⟩ := Finset.exists_subset_card_eq hB
            let f_emb : Fin n2 ↪ Fin (n1 + n2) :=
              (Finset.orderEmbOfFin B' hB'_card).toEmbedding
            let H : SimpleGraph (Fin n2) := SimpleGraph.comap f_emb G
            
            have h2H : ¬ H.CliqueFree r' ∨ ¬ Hᶜ.CliqueFree (s'-1) := h2 H
            rcases h2H with (hH | hH_compl)
            · have hH_clique : ∃ (t : Finset (Fin n2)), H.IsNClique r' t := by
                rw [SimpleGraph.CliqueFree] at hH; push Not at hH; exact hH
              obtain ⟨t, ht⟩ := hH_clique
              have h_clique_img : G.IsNClique r' (image f_emb t) := by
                refine SimpleGraph.IsNClique.mk ?_ ?_
                · rw [SimpleGraph.isClique_iff]
                  intro x hx y hy hne
                  obtain ⟨a, ha, rfl⟩ := mem_image.mp (by simpa using hx)
                  obtain ⟨b, hb, rfl⟩ := mem_image.mp (by simpa using hy)
                  have hne_ab : a ≠ b := by
                    intro h_eq; apply hne; rw [h_eq]
                  have h_clique := ht.isClique
                  rw [SimpleGraph.isClique_iff] at h_clique
                  have hadj : H.Adj a b := h_clique ha hb hne_ab
                  simpa [H, SimpleGraph.comap] using hadj
                · calc
                    (image f_emb t).card = t.card := Finset.card_image_of_injective _ f_emb.injective
                    _ = r' := ht.card_eq
              left
              exact λ hG_cf => hG_cf (image f_emb t) h_clique_img
            · have hH_compl_clique : ∃ (t : Finset (Fin n2)), Hᶜ.IsNClique (s'-1) t := by
                rw [SimpleGraph.CliqueFree] at hH_compl; push Not at hH_compl; exact hH_compl
              obtain ⟨t, ht⟩ := hH_compl_clique
              have h_clique_compl_img : Gᶜ.IsNClique (s'-1) (image f_emb t) := by
                refine SimpleGraph.IsNClique.mk ?_ ?_
                · rw [SimpleGraph.isClique_iff]
                  intro x hx y hy hne
                  obtain ⟨a, ha, rfl⟩ := mem_image.mp (by simpa using hx)
                  obtain ⟨b, hb, rfl⟩ := mem_image.mp (by simpa using hy)
                  have hne_ab : a ≠ b := by
                    intro h_eq; apply hne; rw [h_eq]
                  have h_clique := ht.isClique
                  rw [SimpleGraph.isClique_iff] at h_clique
                  have hadj : Hᶜ.Adj a b := h_clique ha hb hne_ab
                  rw [SimpleGraph.compl_adj] at hadj
                  obtain ⟨hne_ab', h_not_adj⟩ := hadj
                  rw [SimpleGraph.compl_adj]
                  refine ⟨by
                    intro h_eq_f; apply hne_ab'; exact f_emb.injective h_eq_f, h_not_adj⟩
                · calc
                    (image f_emb t).card = t.card := Finset.card_image_of_injective _ f_emb.injective
                    _ = s'-1 := ht.card_eq
              have h_non_adj_all : ∀ x ∈ image f_emb t, ¬ G.Adj v x := by
                intro x hx
                obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
                have hi_B' : f_emb i ∈ B' := Finset.orderEmbOfFin_mem _ _ _
                have hi_B : f_emb i ∈ B := hB'_sub hi_B'
                simp [B] at hi_B; exact hi_B.2
              have hv_not_mem : v ∉ image f_emb t := by
                intro h
                obtain ⟨i, hi, h_eq⟩ := mem_image.mp h
                have hi_B' : f_emb i ∈ B' := Finset.orderEmbOfFin_mem _ _ _
                have hi_B : f_emb i ∈ B := hB'_sub hi_B'
                simp [B] at hi_B
                have hne : f_emb i ≠ v := hi_B.1
                exact hne (h_eq.symm ▸ rfl)
              have h_indep_img : G.IsNIndepSet (s'-1) (image f_emb t) := by
                rw [← SimpleGraph.isNClique_compl]; exact h_clique_compl_img
              have h_indep_v : G.IsNIndepSet s' (insert v (image f_emb t)) := by
                apply SimpleGraph.IsNIndepSet.mk
                · rw [SimpleGraph.isIndepSet_iff]
                  intro x hx y hy hne
                  have hx_cases : x = v ∨ x ∈ (image f_emb t : Set (Fin (n1 + n2))) := by
                    simpa using hx
                  have hy_cases : y = v ∨ y ∈ (image f_emb t : Set (Fin (n1 + n2))) := by
                    simpa using hy
                  rcases hx_cases with (rfl | hx_img)
                  · rcases hy_cases with (rfl | hy_img)
                    · exfalso; exact hne rfl
                    · exact h_non_adj_all y (by simpa using hy_img)
                  · rcases hy_cases with (rfl | hy_img)
                    · intro h; apply h_non_adj_all x (by simpa using hx_img); exact h.symm
                    · have h_indep := h_indep_img.isIndepSet
                      rw [SimpleGraph.isIndepSet_iff] at h_indep
                      exact h_indep (by simpa using hx_img) (by simpa using hy_img) hne
                · have hcard : (image f_emb t).card = s'-1 := h_clique_compl_img.card_eq
                  simp [hcard, hv_not_mem]
                  omega
              right
              intro hG_cf
              rw [SimpleGraph.cliqueFree_compl] at hG_cf
              apply hG_cf; exact h_indep_v
  
  have h_total : P (r + s) := Nat.strong_induction_on (r + s) hP
  exact h_total r s rfl hr hs

end Submission