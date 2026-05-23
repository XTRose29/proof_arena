import Mathlib

/-!
# Sorted subperm → sublist, and related helpers for the lower bound proof

Key facts about the lexicographic comparison used in the encoding, and
the general principle that a sorted sub-multiset of a sorted list is a sublist.
-/

namespace Submission.SortedSubperm

/-- The comparison used in the encoding: lexicographic order on Nat × Nat -/
def pairLe (a b : Nat × Nat) : Prop := a = b ∨ Prod.Lex (· < ·) (· < ·) a b

instance pairLe_decidable (a b : Nat × Nat) : Decidable (pairLe a b) :=
  inferInstanceAs (Decidable (a = b ∨ Prod.Lex (· < ·) (· < ·) a b))

/-- pairLe is antisymmetric -/
instance : Std.Antisymm (fun (a b : Nat × Nat) => pairLe a b) where
  antisymm := by
    intro ⟨a1, a2⟩ ⟨b1, b2⟩ hab hba
    simp only [pairLe, Prod.lex_def, Prod.mk.injEq] at hab hba
    rcases hab with ⟨rfl, rfl⟩ | h1 | ⟨h1, h2⟩
    · rfl
    · rcases hba with ⟨rfl, rfl⟩ | h2 | ⟨h2, _⟩ <;> omega
    · rcases hba with ⟨rfl, rfl⟩ | h3 | ⟨h3, h4⟩ <;> omega

/-
pairLe is transitive
-/
lemma pairLe_trans : ∀ a b c : Nat × Nat, pairLe a b → pairLe b c → pairLe a c := by
  simp [pairLe]; (
  grind);

/-
pairLe is total
-/
lemma pairLe_total : ∀ a b : Nat × Nat, pairLe a b ∨ pairLe b a := by
  unfold pairLe;
  grind +splitIndPred

/-- The Bool function used in ChallengeDeps for mergeSort -/
abbrev pairLeBool (a b : Nat × Nat) : Bool := decide (pairLe a b)

/-
mergeSort with pairLeBool produces a sorted list (Pairwise pairLe)
-/
lemma mergeSort_pairwise (l : List (Nat × Nat)) :
    (l.mergeSort pairLeBool).Pairwise pairLe := by
  -- Apply the lemma that states merge sort produces a sorted list with respect to the comparison function.
  have h_mergeSort_sorted : List.Pairwise (fun a b => decide (pairLe a b)) (l.mergeSort pairLeBool) := by
    apply_rules [ List.pairwise_mergeSort ];
    · simp +zetaDelta at *;
      exact fun a b c d e f h₁ h₂ => pairLe_trans _ _ _ h₁ h₂;
    · exact fun a b => by simpa using pairLe_total a b;;
  aesop

/-- mergeSort with pairLeBool is a permutation -/
lemma mergeSort_perm (l : List (Nat × Nat)) :
    (l.mergeSort pairLeBool).Perm l :=
  List.mergeSort_perm l _

/-- The Bool function used in ChallengeDeps equals pairLeBool -/
lemma challengeLe_eq_pairLeBool :
    (fun (a b : Nat × Nat) => decide (a = b ∨ Prod.Lex (· < ·) (· < ·) a b)) = pairLeBool := by
  rfl

/-- Sorted subperm of sorted list → sublist -/
lemma sorted_subperm_sublist (l₁ l₂ : List (Nat × Nat))
    (h_sub : l₁.Subperm l₂)
    (h1 : l₁.Pairwise pairLe)
    (h2 : l₂.Pairwise pairLe) :
    l₁.Sublist l₂ :=
  List.sublist_of_subperm_of_pairwise h_sub h1 h2

end Submission.SortedSubperm