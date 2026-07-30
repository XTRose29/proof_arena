import ChallengeDeps
import Submission.Helpers

open LeanEval.Combinatorics.FangXiaTilingProblem
open scoped BigOperators

namespace Submission

theorem fang_xia_partition_transitive_of_tiling {n : ℕ} {Y : Set (Equiv.Perm (Fin n))}
    (hTiling : IsTiling (transpositionsWithOne n) Y) :
    ∀ lam : PartitionShape n, 0 ≤ lam.contentSum → IsPartitionTransitive Y lam := by
  intro lam hcontent
  classical
  by_cases hpart : Nonempty (OrderedSetPartition lam)
  · let P₀ := hpart.some
    obtain ⟨p, _, _⟩ := hTiling (1 : Equiv.Perm (Fin n))
    let y : Equiv.Perm (Fin n) := p.2
    let Q₀ := Helpers.actPartition y P₀
    let r := {σ : Equiv.Perm (Fin n) |
      σ ∈ Y ∧ SendsPartition σ P₀ Q₀}.ncard
    refine ⟨r, ?_, ?_⟩
    · exact (Set.ncard_pos).2
        ⟨y, p.2.property, (Helpers.sendsPartition_iff y P₀ Q₀).mpr rfl⟩
    · intro P Q
      have hcount := Helpers.yCount_uniform hTiling hcontent P Q P₀ Q₀
      rw [Helpers.yCount_eq_ncard, Helpers.yCount_eq_ncard] at hcount
      exact_mod_cast hcount
  · exact ⟨1, by simp, fun P _ => (hpart ⟨P⟩).elim⟩

end Submission
