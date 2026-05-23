/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: brauer_character_in_cyclotomic
user: LorenzoLuccioli
model: Aristotle (Harmonic)
submission_repo: LorenzoLuccioli/lean-eval
submission_ref: 00b32807abe0d286c4638daf888c739e1bb4b90c
issue_number: 172
-/
import Mathlib
import Submission.Helpers

namespace Submission

open Polynomial Matrix Module Submission.Helpers

noncomputable def cyclotomicEmbedding (n : ℕ) : CyclotomicField n ℚ →ₐ[ℚ] ℂ :=
  IsAlgClosed.lift (R := ℚ)

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  let n := Monoid.exponent G
  let ψ := cyclotomicEmbedding n
  let φ : CyclotomicField n ℚ →+* ℂ := ψ.toRingHom
  refine ⟨φ, fun V _ _ _ ρ g => ?_⟩
  have hn : 0 < n := Nat.pos_of_neZero n
  have hf : (ρ g) ^ n = 1 := by
    rw [← map_pow, Monoid.pow_exponent_eq_one, map_one]
  rw [trace_eq_charpoly_roots_sum (ρ g)]
  apply Multiset.sum_induction (fun x => x ∈ φ.range) (ρ g).charpoly.roots
  · intro a b ha hb; exact φ.range.add_mem ha hb
  · exact ⟨0, map_zero _⟩
  · intro r hr
    exact root_of_unity_in_range n hn ψ r (charpoly_root_isNthRootOfUnity (ρ g) n hn hf r hr)

end Submission
