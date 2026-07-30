import Submission.OddOrder.BG.AppendixAB.CommutingRepresentationBranch
import Submission.OddOrder.BG.AppendixAB.LocalSchurNoncommutingBranch

/-!
The complete irreducible local quadratic-pair branch of odd p-stability.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- A local quotient pair inside an odd-order group again has odd order. -/
theorem odd_natCard_localQuotientPair [Finite G]
    (hodd : Odd (Nat.card G)) (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    Odd (Nat.card (localQuotientPair E hxN hyN)) := by
  have hnormalizer :
      Odd (Nat.card (Subgroup.normalizer (E : Set G))) :=
    odd_natCard_subgroup (Subgroup.normalizer (E : Set G)) hodd
  have hquotient : Odd (Nat.card
      ((Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E)) :=
    odd_natCard_quotient (normalizerCentralizer E) hnormalizer
  exact odd_natCard_subgroup (localQuotientPair E hxN hyN) hquotient

/-- For an irreducible elementary-abelian local action, both the commuting and
noncommuting quadratic-pair branches have p-primary commutator. -/
theorem local_commutator_isPGroup_of_irreducible_quadratic_pair
    [Finite G] (hodd : Odd (Nat.card G))
    (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    [Finite (Additive E)] {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y)
    [Representation.IsIrreducible
      (localQuotientPairRepresentation E p hxN hyN)] :
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
      E p hxN hyN hx hy
        (odd_natCard_localQuotientPair hodd E hxN hyN) hcomm

end Submission.OddOrder.BG.AppendixAB
