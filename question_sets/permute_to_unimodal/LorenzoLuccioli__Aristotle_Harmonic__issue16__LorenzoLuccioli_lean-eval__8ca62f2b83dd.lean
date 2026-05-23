/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: permute_to_unimodal
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 8ca62f2b83dde51613a3dd3ea14e1fc581db5293
issue_number: 16
-/
import ChallengeDeps
import Submission.LowerBound
import Submission.Achievability

open LeanEval.ProgramVerification

namespace Submission

-- Optimality: every unimodal perm has at least minRearrange differences
lemma unimodal_lower_bound {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) :
    ∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
      Unimodal x → minRearrange arr ≤ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector :=
  LowerBound.lower_bound harr

-- Achievability: there exists a unimodal permutation with at most minRearrange differences.
private lemma achievability {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) :
    ∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
      Unimodal x ∧ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector ≤ minRearrange arr :=
  Achievability.achievability harr

-- Existence: there exists a unimodal perm achieving exactly minRearrange differences
lemma exists_unimodal_achieving_min {arr : Array Nat}
    (harr : arr.Perm (1...=arr.size).toArray) :
    ∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray),
      Unimodal x ∧ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector = minRearrange arr := by
  obtain ⟨x, hx, huni, hle⟩ := achievability harr
  exact ⟨x, hx, huni, Nat.le_antisymm hle (unimodal_lower_bound harr x hx huni)⟩

theorem minRearrange_correct {arr : Array Nat} :
    arr.Perm (1...=arr.size).toArray →
      (∃ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray), Unimodal x ∧ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector = minRearrange arr) ∧
      (∀ (x : Array Nat) (hx : x.Perm (1...=arr.size).toArray), Unimodal x → minRearrange arr ≤ differences (Vector.mk x (by simpa using hx.size_eq)) arr.toVector) := by
  intro harr
  exact ⟨exists_unimodal_achieving_min harr, unimodal_lower_bound harr⟩

end Submission
