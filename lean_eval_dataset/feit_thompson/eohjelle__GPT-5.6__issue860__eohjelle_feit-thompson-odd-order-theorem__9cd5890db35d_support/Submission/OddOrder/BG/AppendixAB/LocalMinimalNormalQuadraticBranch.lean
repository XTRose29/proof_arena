import Submission.OddOrder.BG.AppendixAB.LocalQuotientPairHom
import Submission.OddOrder.BG.AppendixAB.LocalSchurQuadraticBranch
import Submission.OddOrder.MathlibSupport.MinimalNormalUnder
import Submission.OddOrder.MathlibSupport.RepresentationIrreducibleComp

/-!
The minimal-normal local quadratic-pair branch of Appendix A.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- Minimal normality under the ambient pair-generated subgroup makes the
faithful action of its local quotient pair irreducible. -/
theorem localQuotientPairRepresentation_isIrreducible_of_isMinimalNormalUnder
    (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative E] [Module (ZMod p) (Additive E)] {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hmin : IsMinimalNormalUnder E (pairGenerated x y)) :
    Representation.IsIrreducible
      (localQuotientPairRepresentation E p hxN hyN) := by
  let rho := localQuotientPairRepresentation E p hxN hyN
  let f := pairGeneratedToLocalQuotient E hxN hyN
  have hrestricted : Representation.IsIrreducible
      ((normalizerConjugationRepresentation E p).comp
        ((pairGenerated x y).subgroupOf
          (Subgroup.normalizer (E : Set G))).subtype) :=
    normalizerConjugation_isIrreducible_of_isMinimalNormalUnder
      E (pairGenerated x y) p hmin
  have hcomp : rho.comp f =
      (normalizerConjugationRepresentation E p).comp
        ((pairGenerated x y).subgroupOf
          (Subgroup.normalizer (E : Set G))).subtype :=
    localQuotientPairRepresentation_comp_pairGeneratedToLocalQuotient
      E p hxN hyN
  letI : Representation.IsIrreducible (rho.comp f) := by
    rw [hcomp]
    exact hrestricted
  exact representation_isIrreducible_of_comp rho f

/-- In an odd-order group, a quadratic pair acting minimally normally on an
elementary abelian p-subgroup has p-primary local commutator. -/
theorem local_commutator_isPGroup_of_minimalNormalUnder_quadratic_pair
    [Finite G] (hodd : Odd (Nat.card G))
    (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    [Finite (Additive E)] {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y)
    (hmin : IsMinimalNormalUnder E (pairGenerated x y)) :
    IsPGroup p (_root_.commutator (localQuotientPair E hxN hyN)) := by
  letI : Representation.IsIrreducible
      (localQuotientPairRepresentation E p hxN hyN) :=
    localQuotientPairRepresentation_isIrreducible_of_isMinimalNormalUnder
      E p hxN hyN hmin
  exact local_commutator_isPGroup_of_irreducible_quadratic_pair
    hodd E p hxN hyN hx hy

end Submission.OddOrder.BG.AppendixAB
