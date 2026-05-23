import Mathlib

/-!
# Helper for agreements_form_nds

Shows that a sublist of a sorted list with non-decreasing second components
corresponds to valid NDS indices.
-/

namespace Submission.AgreementsNDS

/-
Given a sorted list and a sublist with non-decreasing second components,
    the elements of the sublist can be mapped to indices in the sorted list
    with the required properties.
-/
lemma sublist_to_nds_indices
    (sorted_list : List (Nat × Nat))
    (h_sorted : sorted_list.Pairwise (fun a b => a = b ∨ Prod.Lex (· < ·) (· < ·) a b))
    (sub : List (Nat × Nat))
    (h_sub : sub.Sublist sorted_list)
    (h_nds : sub.Pairwise (fun a b => a.2 ≤ b.2)) :
    ∃ (indices : List Nat),
      indices.Pairwise (· < ·) ∧
      (∀ i ∈ indices, i < sorted_list.length) ∧
      indices.Pairwise (fun i j => (sorted_list.map Prod.snd)[i]! ≤ (sorted_list.map Prod.snd)[j]!) ∧
      indices.length = sub.length := by
  have h_sublist : ∀ {l1 l2 : List (ℕ × ℕ)}, l1.Sublist l2 → ∃ (indices : List ℕ), List.Pairwise (· < ·) indices ∧ (∀ i ∈ indices, i < l2.length) ∧ (List.map (fun i => (l2[i]!)) indices) = l1 ∧ indices.length = l1.length := by
    intros l1 l2 h_sublist
    induction' h_sublist with l1 l2 h_sublist ih;
    · exists [ ];
    · obtain ⟨ indices, hindices₁, hindices₂, hindices₃, hindices₄ ⟩ := ‹_›; use indices.map ( fun i => i + 1 ) ; simp_all +decide [ List.pairwise_map ] ;
      convert hindices₃ using 1;
    · obtain ⟨ indices, hindices₁, hindices₂, hindices₃, hindices₄ ⟩ := ‹_›; use 0 :: indices.map ( fun i => i + 1 ) ; simp_all +decide [ List.pairwise_cons ] ;
      simp_all +decide [ List.pairwise_map, Function.comp ];
      convert hindices₃ using 1;
  obtain ⟨ indices, hindices₁, hindices₂, hindices₃, hindices₄ ⟩ := h_sublist h_sub; use indices; simp_all +decide [ List.pairwise_map ] ;
  rw [ List.pairwise_iff_get ] at *;
  intro i j hij; specialize hindices₁ i j hij; specialize h_nds ⟨ i, by linarith [ Fin.is_lt i, Fin.is_lt j ] ⟩ ⟨ j, by linarith [ Fin.is_lt i, Fin.is_lt j ] ⟩ hij; aesop;

end Submission.AgreementsNDS