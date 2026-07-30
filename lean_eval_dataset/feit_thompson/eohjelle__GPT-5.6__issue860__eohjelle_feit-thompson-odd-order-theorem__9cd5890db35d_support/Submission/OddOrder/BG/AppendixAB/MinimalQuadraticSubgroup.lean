import Submission.OddOrder.BG.AppendixAB.TwoGenerator
import Submission.OddOrder.MathlibSupport.MinimalNormalUnderExistence

/-!
Selection of a minimal invariant subgroup for a quadratic pair.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- Quadraticity restricts from a subgroup to every smaller subgroup. -/
theorem IsQuadraticPElement.of_le {p : ℕ} {M E : Subgroup G} {x : G}
    (hx : IsQuadraticPElement p E x) (hME : M ≤ E) :
    IsQuadraticPElement p M x := by
  refine ⟨hx.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro d hd
  exact Subgroup.mem_centralizer_iff.mp hx.2 d
    (Subgroup.commutator_mono hME le_rfl hd)

/-- A nontrivial finite p-subgroup normalized by a quadratic pair contains a
minimal invariant p-subgroup on which the same pair remains quadratic. -/
theorem exists_minimalNormalUnder_quadratic_pair [Finite G]
    {p : ℕ} {E : Subgroup G} {x y : G}
    (hE : E ≠ ⊥) (hP : IsPGroup p E)
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y) :
    ∃ M : Subgroup G,
      M ≤ E ∧ IsPGroup p M ∧
      x ∈ Subgroup.normalizer (M : Set G) ∧
      y ∈ Subgroup.normalizer (M : Set G) ∧
      IsQuadraticPElement p M x ∧
      IsQuadraticPElement p M y ∧
      IsMinimalNormalUnder M (pairGenerated x y) := by
  obtain ⟨M, hME, hmin⟩ := exists_minimalNormalUnder_le hE
    (pairGenerated_le_normalizer hxN hyN)
  refine ⟨M, hME, hP.to_le hME, ?_, ?_, hx.of_le hME, hy.of_le hME, hmin⟩
  · exact hmin.le_normalizer (mem_pairGenerated_left x y)
  · exact hmin.le_normalizer (mem_pairGenerated_right x y)

end Submission.OddOrder.BG.AppendixAB
