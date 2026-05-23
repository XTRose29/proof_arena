/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: finite_graph_ramsey_theorem
user: sqrt-of-2
model: GPT-5.5
submission_repo: sqrt-of-2/e19d4e2ed5a4ecad14dbf0b429842bc9
submission_ref: bfd5b5deffe9e82a180ec3dee0aa66d00f689d63
issue_number: 152
-/
import Mathlib

open SimpleGraph

namespace Submission

lemma cliqueFree_induce_of_cliqueFreeOn {α : Type*} {G : SimpleGraph α} {S : Set α} {n : ℕ}
    (h : G.CliqueFreeOn S n) : (G.induce S).CliqueFree n := by
  intro t ht
  apply h (t := t.map ⟨Subtype.val, Subtype.coe_injective⟩)
  · intro x hx
    simp only [Finset.mem_coe, Finset.mem_map] at hx
    rcases hx with ⟨y, hy, rfl⟩
    exact y.property
  · rw [SimpleGraph.isNClique_iff] at ht ⊢
    constructor
    · intro x hx y hy hxy
      simp only [Finset.mem_coe, Finset.mem_map] at hx hy
      rcases hx with ⟨x', hx', rfl⟩
      rcases hy with ⟨y', hy', rfl⟩
      have hxy' : x' ≠ y' := by
        intro h
        exact hxy (congrArg Subtype.val h)
      exact SimpleGraph.induce_adj.mp (ht.1 hx' hy' hxy')
    · rw [Finset.card_map, ht.2]

lemma neighbor_induce_cliqueFree_of_cliqueFree_succ {α : Type*} {G : SimpleGraph α} {r : ℕ}
    (v : α) (h : G.CliqueFree (r + 1)) : (G.induce (G.neighborSet v)).CliqueFree r := by
  have hOn : G.CliqueFreeOn (Set.univ ∩ G.neighborSet v) r :=
    SimpleGraph.CliqueFreeOn.of_succ G ((SimpleGraph.cliqueFreeOn_univ G).2 h) (by simp)
  rw [Set.univ_inter] at hOn
  exact cliqueFree_induce_of_cliqueFreeOn hOn

def complInduceEmbedding {α : Type*} (G : SimpleGraph α) (S : Set α) :
    (G.induce S)ᶜ ↪g Gᶜ where
  toFun x := x.1
  inj' := by intro x y h; exact Subtype.ext h
  map_rel_iff' := by
    intro x y
    rw [SimpleGraph.compl_adj, SimpleGraph.compl_adj]
    dsimp
    constructor
    · intro h
      exact ⟨fun hxy => h.1 (congrArg Subtype.val hxy), h.2⟩
    · intro h
      exact ⟨fun hxy => h.1 (Subtype.ext hxy), h.2⟩

lemma not_cliqueFree_of_embedding {α β : Type*} {G : SimpleGraph α} {H : SimpleGraph β} {n : ℕ}
    (e : H ↪g G) (h : ¬ H.CliqueFree n) : ¬ G.CliqueFree n := by
  intro hG
  exact h (SimpleGraph.CliqueFree.comap e.isContained hG)

lemma neighbor_or_compl_large {α : Type*} [Fintype α] (G : SimpleGraph α) (v : α)
    (n₁ n₂ : ℕ) (hcard : n₁ + n₂ + 1 ≤ Fintype.card α) :
    n₁ ≤ (G.neighborSet v).ncard ∨ n₂ ≤ (Gᶜ.neighborSet v).ncard := by
  classical
  by_contra hneg
  push Not at hneg
  have hdisj : Disjoint (G.neighborSet v) (Gᶜ.neighborSet v) :=
    G.compl_neighborSet_disjoint v
  have hunion : (G.neighborSet v ∪ Gᶜ.neighborSet v).ncard = Fintype.card α - 1 := by
    rw [Set.ncard_eq_toFinset_card]
    simpa using G.card_neighborSet_union_compl_neighborSet v
  have hsum : (G.neighborSet v).ncard + (Gᶜ.neighborSet v).ncard = Fintype.card α - 1 := by
    rw [← Set.ncard_union_eq hdisj]
    exact hunion
  have hlt : Fintype.card α - 1 < n₁ + n₂ := by
    rw [← hsum]
    exact Nat.add_lt_add hneg.1 hneg.2
  have hle : n₁ + n₂ ≤ Fintype.card α - 1 := by omega
  omega

def RamseyPair (r s : ℕ) : Prop :=
  ∃ n : ℕ, ∀ {α : Type*} [Fintype α], n ≤ Fintype.card α →
    ∀ G : SimpleGraph α, ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s

lemma ramseyPair_zero_left (s : ℕ) : RamseyPair 0 s := by
  refine ⟨0, ?_⟩
  intro α _ hcard G
  exact Or.inl SimpleGraph.not_cliqueFree_zero

lemma ramseyPair_one_left (s : ℕ) : RamseyPair 1 s := by
  refine ⟨1, ?_⟩
  intro α _ hcard G
  left
  intro hcf
  have hne : Nonempty α := Fintype.card_pos_iff.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hcard)
  have hempty : IsEmpty α := SimpleGraph.cliqueFree_one.mp hcf
  rcases hne with ⟨a⟩
  exact IsEmpty.false a

lemma ramseyPair_zero_right (r : ℕ) : RamseyPair r 0 := by
  refine ⟨0, ?_⟩
  intro α _ hcard G
  exact Or.inr SimpleGraph.not_cliqueFree_zero

lemma ramseyPair_one_right (r : ℕ) : RamseyPair r 1 := by
  refine ⟨1, ?_⟩
  intro α _ hcard G
  right
  intro hcf
  have hne : Nonempty α := Fintype.card_pos_iff.mp (Nat.lt_of_lt_of_le Nat.zero_lt_one hcard)
  have hempty : IsEmpty α := SimpleGraph.cliqueFree_one.mp hcf
  rcases hne with ⟨a⟩
  exact IsEmpty.false a

lemma finite_graph_ramsey_pair : ∀ r s : ℕ, RamseyPair r s := by
  intro r s
  have hmain : ∀ m : ℕ, ∀ r s : ℕ, r + s = m → RamseyPair r s := by
    intro m
    induction m using Nat.strong_induction_on with
    | h m ih =>
      intro r s hrs
      rcases r with _ | r
      · exact ramseyPair_zero_left s
      rcases r with _ | r
      · exact ramseyPair_one_left s
      rcases s with _ | s
      · exact ramseyPair_zero_right (r + 2)
      rcases s with _ | s
      · exact ramseyPair_one_right (r + 2)
      obtain ⟨n₁, hn₁⟩ := ih (r.succ + s.succ.succ) (by omega) r.succ s.succ.succ rfl
      obtain ⟨n₂, hn₂⟩ := ih (s.succ + r.succ.succ) (by omega) s.succ r.succ.succ rfl
      refine ⟨n₁ + n₂ + 1, ?_⟩
      intro α _ hcard G
      classical
      have hpos : 0 < Fintype.card α := by omega
      obtain ⟨v⟩ := Fintype.card_pos_iff.mp hpos
      cases neighbor_or_compl_large G v n₁ n₂ hcard with
      | inl hlarge =>
        have hcard' : n₁ ≤ Fintype.card (G.neighborSet v) := by
          rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hlarge
          exact hlarge
        cases hn₁ hcard' (G.induce (G.neighborSet v)) with
        | inl hcl =>
          left
          intro hG
          exact hcl (neighbor_induce_cliqueFree_of_cliqueFree_succ (G := G) (r := r.succ) v hG)
        | inr hacl =>
          right
          exact not_cliqueFree_of_embedding (complInduceEmbedding G (G.neighborSet v)) hacl
      | inr hlarge =>
        have hcard' : n₂ ≤ Fintype.card (Gᶜ.neighborSet v) := by
          rw [Set.ncard_eq_toFinset_card', Set.toFinset_card] at hlarge
          exact hlarge
        cases hn₂ hcard' (Gᶜ.induce (Gᶜ.neighborSet v)) with
        | inl hcl =>
          right
          intro hGc
          exact hcl (neighbor_induce_cliqueFree_of_cliqueFree_succ (G := Gᶜ) (r := s.succ) v hGc)
        | inr hacl =>
          left
          intro hG
          have hGG : (Gᶜ)ᶜ.CliqueFree (r.succ.succ) := by simpa using hG
          exact hacl (SimpleGraph.CliqueFree.comap
            (complInduceEmbedding Gᶜ (Gᶜ.neighborSet v)).isContained hGG)
  exact hmain (r + s) r s rfl

theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s := by
  intro r s hr hs
  obtain ⟨n, hn⟩ := finite_graph_ramsey_pair r s
  refine ⟨n, ?_⟩
  intro G
  exact hn (by simp) G

end Submission
