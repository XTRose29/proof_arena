import Mathlib.Combinatorics.SimpleGraph.Clique
import Mathlib.Combinatorics.SimpleGraph.Finite
import Submission.Helpers

open SimpleGraph

namespace Submission

/-! ### Finite graph Ramsey theorem

Every pair `r, s ≥ 2` admits an `n` such that any graph on `n` vertices has a clique of size `r`
or an independent set of size `s`. Proof: induction on `r + s` with
`R(r, s) ≤ R(r - 1, s) + R(r, s - 1)`.
-/

/-- Ramsey property at size `n`, for arbitrary finite vertex types. -/
def IsRamsey (n r s : ℕ) : Prop :=
  ∀ {α : Type*} [Fintype α], n ≤ Fintype.card α →
    ∀ (G : SimpleGraph α), ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree s

private lemma not_cliqueFree_top_of_le_card {α : Type*} [Fintype α] {n : ℕ}
    (h : n ≤ Fintype.card α) : ¬(⊤ : SimpleGraph α).CliqueFree n := by
  classical
  obtain ⟨t, -, ht⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset α)) h
  exact (⟨fun _ _ _ _ hab ↦ hab, ht⟩ : (⊤ : SimpleGraph α).IsNClique n t).not_cliqueFree

/-- `R(2, s) ≤ s`. -/
private lemma isRamsey_two_left (s : ℕ) (_hs : 2 ≤ s) : IsRamsey s 2 s := by
  intro α _ hα G
  by_cases hG : G = ⊥
  · right; simpa [hG, compl_bot] using not_cliqueFree_top_of_le_card hα
  · left; exact mt cliqueFree_two.mp hG

/-- `R(r, 2) ≤ r`. -/
private lemma isRamsey_two_right (r : ℕ) (_hr : 2 ≤ r) : IsRamsey r r 2 := by
  intro α _ hα G
  by_cases hG : G = ⊤
  · left; simpa [hG] using not_cliqueFree_top_of_le_card hα
  · right
    refine mt cliqueFree_two.mp fun hc ↦ hG ?_
    rw [← compl_compl G, hc, compl_bot]

private lemma not_cliqueFree_of_not_cliqueFree_induce
    {α : Type*} {G : SimpleGraph α} {s : Set α} {n : ℕ}
    (h : ¬(G.induce s).CliqueFree n) : ¬G.CliqueFree n :=
  mt (CliqueFree.comap ⟨(Embedding.induce s).toCopy⟩) h

/-- An `r`-clique among neighbors of `v` extends to an `(r + 1)`-clique. -/
private lemma not_cliqueFree_of_not_cliqueFree_induce_neighbor
    {α : Type*} {G : SimpleGraph α} {v : α} {r : ℕ}
    (h : ¬(G.induce (G.neighborSet v)).CliqueFree r) : ¬G.CliqueFree (r + 1) := by
  classical
  obtain ⟨t, ht⟩ : ∃ t, (G.induce (G.neighborSet v)).IsNClique r t := by
    simpa [CliqueFree] using h
  have ht' : G.IsNClique r (t.map ⟨Subtype.val, Subtype.val_injective⟩) :=
    (isNClique_induce_iff _ _ _).1 ht
  exact (ht'.insert fun b hb ↦ by
    obtain ⟨b', _, rfl⟩ := Finset.mem_map.1 hb
    exact b'.property).not_cliqueFree

private lemma induce_compl {α : Type*} (G : SimpleGraph α) (s : Set α) :
    (G.induce s)ᶜ = Gᶜ.induce s := by
  ext u v
  simp only [compl_adj, induce_adj]
  exact ⟨fun ⟨hne, hna⟩ ↦ ⟨Subtype.coe_injective.ne hne, hna⟩,
    fun ⟨hne, hna⟩ ↦ ⟨fun h ↦ hne (congrArg Subtype.val h), hna⟩⟩

private lemma not_cliqueFree_compl_of_not_cliqueFree_induce_compl
    {α : Type*} {G : SimpleGraph α} {s : Set α} {n : ℕ}
    (h : ¬(G.induce s)ᶜ.CliqueFree n) : ¬Gᶜ.CliqueFree n := by
  rw [induce_compl] at h
  exact not_cliqueFree_of_not_cliqueFree_induce (G := Gᶜ) h

private lemma exists_isRamsey : ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n ≥ 2, IsRamsey n r s := by
  intro r s hr hs
  have : ∀ k r s, r + s = k → 2 ≤ r → 2 ≤ s → ∃ n ≥ 2, IsRamsey n r s := by
    intro k
    induction k using Nat.strong_induction_on with
    | _ k ih =>
      intro r s hsum hr hs
      by_cases hr2 : r = 2
      · subst hr2; exact ⟨s, hs, isRamsey_two_left s hs⟩
      by_cases hs2 : s = 2
      · subst hs2; exact ⟨r, hr, isRamsey_two_right r hr⟩
      obtain ⟨n₁, hn₁ge, hn₁⟩ :=
        ih (r - 1 + s) (by omega) (r - 1) s (by omega) (by omega) hs
      obtain ⟨n₂, hn₂ge, hn₂⟩ :=
        ih (r + (s - 1)) (by omega) r (s - 1) (by omega) hr (by omega)
      refine ⟨n₁ + n₂, by omega, ?_⟩
      intro α _ hα G
      classical
      haveI : Nonempty α := Fintype.card_pos_iff.mp (by omega)
      let v : α := Classical.arbitrary α
      letI : DecidableRel G.Adj := Classical.decRel _
      letI : Fintype (G.neighborSet v) := inferInstance
      letI : Fintype (Gᶜ.neighborSet v) := inferInstance
      have hdeg : G.degree v + Gᶜ.degree v = Fintype.card α - 1 := by
        rw [degree_compl]
        exact Nat.add_sub_of_le (Nat.le_sub_one_of_lt (G.degree_lt_card_verts v))
      rcases le_or_gt n₁ (G.degree v) with hN | hN
      · have hcardN : n₁ ≤ Fintype.card (G.neighborSet v) := by
          rwa [card_neighborSet_eq_degree]
        rcases hn₁ hcardN (G.induce (G.neighborSet v)) with hcl | hind
        · left
          convert not_cliqueFree_of_not_cliqueFree_induce_neighbor hcl using 2
          omega
        · right
          exact not_cliqueFree_compl_of_not_cliqueFree_induce_compl hind
      · have hM : n₂ ≤ Gᶜ.degree v := by omega
        have hcardM : n₂ ≤ Fintype.card (Gᶜ.neighborSet v) := by
          rwa [card_neighborSet_eq_degree]
        rcases hn₂ hcardM (G.induce (Gᶜ.neighborSet v)) with hcl | hind
        · left
          exact not_cliqueFree_of_not_cliqueFree_induce hcl
        · right
          rw [induce_compl] at hind
          convert not_cliqueFree_of_not_cliqueFree_induce_neighbor (G := Gᶜ) hind using 2
          omega
  exact this (r + s) r s rfl hr hs

theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n),
      ¬G.CliqueFree r ∨ ¬Gᶜ.CliqueFree s := by
  intro r s hr hs
  obtain ⟨n, -, hn⟩ := exists_isRamsey r s hr hs
  exact ⟨n, fun G ↦ hn (by simp) G⟩

end Submission
