import Mathlib
import Submission.Helpers

open SimpleGraph

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem finite_graph_ramsey_theorem :
    ∀ r s : ℕ, 2 ≤ r → 2 ≤ s → ∃ n : ℕ, ∀ G : SimpleGraph (Fin n), ¬ G.CliqueFree r ∨ ¬ Gᶜ.CliqueFree s :=  by
  classical
  -- a convenient (slightly non-sharp) Ramsey bound, formulated for a finite set
  have bound : ∀ r : ℕ, ∀ s : ℕ, ∃ b : ℕ,
      ∀ (α : Type) (G : SimpleGraph α) (T : Finset α),
        G.CliqueFreeOn (↑T : Set α) r →
        Gᶜ.CliqueFreeOn (↑T : Set α) s → T.card < b := by
    intro r
    induction r with
    | zero =>
      intro s
      refine ⟨0, ?_⟩
      intro α G T hR hS
      exfalso
      have hnot : ¬ G.IsNClique 0 (∅ : Finset α) :=
        hR (t := (∅ : Finset α)) (by simp)
      exact hnot (by simpa using (G.isNClique_empty.mpr rfl))
    | succ r ihr =>
      intro s
      induction s with
      | zero =>
        refine ⟨0, ?_⟩
        intro α G T hR hS
        exfalso
        have hnot : ¬ (Gᶜ).IsNClique 0 (∅ : Finset α) :=
          hS (t := (∅ : Finset α)) (by simp)
        exact hnot (by simpa using ((Gᶜ).isNClique_empty.mpr rfl))
      | succ s ihs =>
        obtain ⟨b₁, hb₁⟩ := ihr (Nat.succ s)
        obtain ⟨b₂, hb₂⟩ := ihs
        refine ⟨b₁ + b₂ + 1, ?_⟩
        intro α G T hR hS
        by_cases hne : T.Nonempty
        · obtain ⟨a, ha⟩ := hne
          let U : Finset α := T.erase a
          let A : Finset α := U.filter (fun x => G.Adj a x)
          let B : Finset α := U.filter (fun x => ¬ G.Adj a x)
          have haT : a ∈ (↑T : Set α) := by simpa using ha
          have hRred : G.CliqueFreeOn ((↑T : Set α) ∩ G.neighborSet a) r :=
            SimpleGraph.CliqueFreeOn.of_succ G hR haT
          have hSred : (Gᶜ).CliqueFreeOn ((↑T : Set α) ∩ (Gᶜ).neighborSet a) s :=
            SimpleGraph.CliqueFreeOn.of_succ (Gᶜ) hS haT
          have hAT : (↑A : Set α) ⊆ (↑T : Set α) := by
            intro x hx
            have hx' : x ∈ A := hx
            have hxU : x ∈ U := (Finset.mem_filter.mp hx').1
            exact (by
              have hxeras : x ∈ T.erase a := by simpa [U] using hxU
              exact (show x ∈ T from Finset.mem_of_mem_erase hxeras))
          have hBT : (↑B : Set α) ⊆ (↑T : Set α) := by
            intro x hx
            have hx' : x ∈ B := hx
            have hxU : x ∈ U := (Finset.mem_filter.mp hx').1
            have hxeras : x ∈ T.erase a := by simpa [U] using hxU
            exact (show x ∈ T from Finset.mem_of_mem_erase hxeras)
          have hAint : (↑A : Set α) ⊆ ((↑T : Set α) ∩ G.neighborSet a) := by
            intro x hx
            refine ⟨hAT hx, ?_⟩
            have hx' : x ∈ A := hx
            have hadj : G.Adj a x := (Finset.mem_filter.mp hx').2
            exact (SimpleGraph.mem_neighborSet _ _ _).2 hadj
          have hBint : (↑B : Set α) ⊆ ((↑T : Set α) ∩ (Gᶜ).neighborSet a) := by
            intro x hx
            refine ⟨hBT hx, ?_⟩
            have hx' : x ∈ B := hx
            have hxU : x ∈ U := (Finset.mem_filter.mp hx').1
            have hnotadj : ¬ G.Adj a x := (Finset.mem_filter.mp hx').2
            have hxeras : x ∈ T.erase a := by simpa [U] using hxU
            have hxa : x ≠ a := (Finset.mem_erase.mp hxeras).1
            -- membership in the complement neighbor set
            exact (SimpleGraph.mem_neighborSet _ _ _).2
              ((SimpleGraph.compl_adj _ _ _).2 ⟨Ne.symm hxa, hnotadj⟩)
          have hAcard : A.card < b₁ :=
            hb₁ α G A
              (SimpleGraph.CliqueFreeOn.subset G hAint hRred)
              (SimpleGraph.CliqueFreeOn.subset (Gᶜ) hAT hS)
          have hBcard : B.card < b₂ :=
            hb₂ α G B
              (SimpleGraph.CliqueFreeOn.subset G hBT hR)
              (SimpleGraph.CliqueFreeOn.subset (Gᶜ) hBint hSred)
          have hpart : A.card + B.card = U.card := by
            simpa [A, B] using
              (Finset.card_filter_add_card_filter_not (s := U) (p := fun x : α => G.Adj a x))
          have hU : U.card + 1 = T.card := by
            simpa [U] using (Finset.card_erase_add_one ha)
          calc
            T.card = A.card + B.card + 1 := by omega
            _ < b₁ + b₂ + 1 := Nat.add_lt_add_right (Nat.add_lt_add hAcard hBcard) _
        · have hzero : T.card = 0 := Finset.card_eq_zero.mpr (by
              exact (Finset.not_nonempty_iff_eq_empty.mp hne))
          simp [hzero]
    
  intro r s hr hs
  obtain ⟨b, hb⟩ := bound r s
  refine ⟨b, ?_⟩
  intro G
  by_cases hR : G.CliqueFree r
  · by_cases hS : Gᶜ.CliqueFree s
    · have hlt : (Finset.univ : Finset (Fin b)).card < b :=
        hb (Fin b) G (Finset.univ : Finset (Fin b))
          (by simpa using (hR.cliqueFreeOn (s := (Set.univ : Set (Fin b)))))
          (by simpa using (hS.cliqueFreeOn (s := (Set.univ : Set (Fin b)))))
      have : ¬ b < b := Nat.lt_irrefl b
      exfalso
      exact this (by simpa using hlt)
    · exact Or.inr hS
  · exact Or.inl hR


end Submission
