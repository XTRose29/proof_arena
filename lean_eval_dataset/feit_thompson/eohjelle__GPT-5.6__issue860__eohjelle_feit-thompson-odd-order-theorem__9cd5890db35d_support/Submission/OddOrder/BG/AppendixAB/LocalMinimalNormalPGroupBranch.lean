import Submission.OddOrder.BG.AppendixAB.LocalMinimalNormalQuadraticBranch
import Submission.OddOrder.MathlibSupport.MinimalNormalUnderElementaryAbelian

/-!
The structure-free minimal-normal p-group branch of Appendix A.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- A finite p-subgroup minimal normal under a quadratic pair automatically
has the elementary-abelian structure required by the local Schur argument. -/
theorem local_commutator_isPGroup_of_minimalNormalUnder
    [Finite G] (hodd : Odd (Nat.card G))
    (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    (hP : IsPGroup p E) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y)
    (hmin : IsMinimalNormalUnder E (pairGenerated x y)) :
    IsPGroup p (_root_.commutator (localQuotientPair E hxN hyN)) := by
  have habel := hmin.isElementaryAbelian_of_isPGroup hP
  letI : IsMulCommutative E := habel.1
  letI : Module (ZMod p) (Additive E) :=
    elementaryAbelianZModModule E p habel.2
  exact local_commutator_isPGroup_of_minimalNormalUnder_quadratic_pair
    hodd E p hxN hyN hx hy hmin

end Submission.OddOrder.BG.AppendixAB
