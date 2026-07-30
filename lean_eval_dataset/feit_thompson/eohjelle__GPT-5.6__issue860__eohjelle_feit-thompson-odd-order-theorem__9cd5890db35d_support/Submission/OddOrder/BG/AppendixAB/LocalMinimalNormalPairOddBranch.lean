import Submission.OddOrder.BG.AppendixAB.LocalMinimalNormalPGroupBranch
import Submission.OddOrder.BG.AppendixAB.LocalQuotientPairOdd

/-!
The minimal-normal quadratic branch assuming only that the acting pair has
odd order.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The complete irreducible quadratic-pair branch needs oddness only of the
local quotient pair. -/
theorem local_commutator_isPGroup_of_irreducible_quadratic_pair_of_local_odd
    [Finite G] (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    [Finite (Additive E)] {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y)
    [Representation.IsIrreducible
      (localQuotientPairRepresentation E p hxN hyN)]
    (hodd : Odd (Nat.card (localQuotientPair E hxN hyN))) :
    IsPGroup p (_root_.commutator (localQuotientPair E hxN hyN)) := by
  let rho := localQuotientPairRepresentation E p hxN hyN
  let xQ := localQuotientPairLeft E hxN hyN
  let yQ := localQuotientPairRight E hxN hyN
  by_cases hcomm : Commute (rho xQ) (rho yQ)
  · apply local_commutator_isPGroup_of_commuting_representation
      E p hxN hyN
    have hxrep : rho xQ =
        centralizerQuotientConjugationRepresentation E p
          (QuotientGroup.mk' (normalizerCentralizer E) ⟨x, hxN⟩) := by
      apply LinearMap.ext
      exact localQuotientPairRepresentation_left_apply E p hxN hyN
    have hyrep : rho yQ =
        centralizerQuotientConjugationRepresentation E p
          (QuotientGroup.mk' (normalizerCentralizer E) ⟨y, hyN⟩) := by
      apply LinearMap.ext
      exact localQuotientPairRepresentation_right_apply E p hxN hyN
    rw [hxrep, hyrep] at hcomm
    exact hcomm
  · exact local_commutator_isPGroup_of_noncommuting_quadratic_pair
      E p hxN hyN hx hy hodd hcomm

/-- If the ambient pair-generated subgroup has odd order, a finite
p-subgroup minimal normal under that pair has p-primary local commutator. -/
theorem local_commutator_isPGroup_of_minimalNormalUnder_pair_odd
    [Finite G] (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hP : IsPGroup p E) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y)
    (hodd : Odd (Nat.card (pairGenerated x y)))
    (hmin : IsMinimalNormalUnder E (pairGenerated x y)) :
    IsPGroup p (_root_.commutator (localQuotientPair E hxN hyN)) := by
  have habel := hmin.isElementaryAbelian_of_isPGroup hP
  letI : IsMulCommutative E := habel.1
  letI : Module (ZMod p) (Additive E) :=
    elementaryAbelianZModModule E p habel.2
  letI : Representation.IsIrreducible
      (localQuotientPairRepresentation E p hxN hyN) :=
    localQuotientPairRepresentation_isIrreducible_of_isMinimalNormalUnder
      E p hxN hyN hmin
  exact local_commutator_isPGroup_of_irreducible_quadratic_pair_of_local_odd
    E p hxN hyN hx hy
      (odd_natCard_localQuotientPair_of_pairGenerated E hxN hyN hodd)

end Submission.OddOrder.BG.AppendixAB
