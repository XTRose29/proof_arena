import Submission.OddOrder.BG.AppendixAB.LocalMinimalNormalPairOddBranch
import Submission.OddOrder.BG.AppendixAB.MinimalQuadraticSubgroup

/-!
Selection and discharge of the minimal-invariant quadratic branch.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- From a nontrivial quadratic p-subgroup, select a minimal invariant
subgroup whose local quotient pair has p-primary commutator. -/
theorem exists_minimal_quadratic_local_commutator_isPGroup
    [Finite G] {p : ℕ} [Fact p.Prime]
    {E : Subgroup G} {x y : G}
    (hE : E ≠ ⊥) (hP : IsPGroup p E)
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y)
    (hodd : Odd (Nat.card (pairGenerated x y))) :
    ∃ (M : Subgroup G) (_hME : M ≤ E)
      (hxNM : x ∈ Subgroup.normalizer (M : Set G))
      (hyNM : y ∈ Subgroup.normalizer (M : Set G)),
      IsPGroup p M ∧
      IsMinimalNormalUnder M (pairGenerated x y) ∧
      IsPGroup p
        (_root_.commutator (localQuotientPair M hxNM hyNM)) := by
  obtain ⟨M, hME, hMP, hxNM, hyNM, hxM, hyM, hmin⟩ :=
    exists_minimalNormalUnder_quadratic_pair
      hE hP hxN hyN hx hy
  refine ⟨M, hME, hxNM, hyNM, hMP, hmin, ?_⟩
  exact local_commutator_isPGroup_of_minimalNormalUnder_pair_odd
    M p hMP hxNM hyNM hxM hyM hodd hmin

end Submission.OddOrder.BG.AppendixAB
