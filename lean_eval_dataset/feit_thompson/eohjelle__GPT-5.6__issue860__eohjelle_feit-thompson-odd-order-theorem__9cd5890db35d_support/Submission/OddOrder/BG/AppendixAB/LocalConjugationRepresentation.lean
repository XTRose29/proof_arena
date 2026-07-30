import Submission.OddOrder.BG.AppendixAB.TwoGenerator
import Submission.OddOrder.BG.Section01.PStability
import Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation
import Submission.OddOrder.MathlibSupport.FaithfulQuotientRepresentation

/-!
Faithful local conjugation representations for Appendix A.

For an elementary abelian subgroup `E`, conjugation descends from its
normalizer to `N(E) / C(E)`.  The resulting representation, and hence its
restriction to every local two-generator subgroup, is faithful.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The faithful conjugation representation of `N(E) / C(E)`. -/
def centralizerQuotientConjugationRepresentation
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] :
    Representation (ZMod p)
      ((Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E)
      (Additive E) :=
  QuotientGroup.lift (normalizerCentralizer E)
    (normalizerConjugationRepresentation E p) <| by
      exact le_of_eq (normalizerConjugationRepresentation_ker E p).symm

@[simp]
theorem centralizerQuotientConjugationRepresentation_mk_apply
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    (g : Subgroup.normalizer (E : Set G)) (x : Additive E) :
    centralizerQuotientConjugationRepresentation E p
        (g : (Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E) x =
      normalizerConjugationRepresentation E p g x := by
  simp [centralizerQuotientConjugationRepresentation]

theorem centralizerQuotientConjugationRepresentation_injective
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)] :
    Function.Injective (centralizerQuotientConjugationRepresentation E p) := by
  apply (QuotientGroup.injective_lift_iff
    (normalizerCentralizer E)
    (normalizerConjugationRepresentation E p) _).mpr
  exact (normalizerConjugationRepresentation_ker E p).symm

/-- Restriction of the quotient conjugation representation to a subgroup. -/
def localSubgroupConjugationRepresentation
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    (Q : Subgroup
      ((Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E)) :
    Representation (ZMod p) Q (Additive E) :=
  (centralizerQuotientConjugationRepresentation E p).comp Q.subtype

theorem localSubgroupConjugationRepresentation_injective
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    (Q : Subgroup
      ((Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E)) :
    Function.Injective (localSubgroupConjugationRepresentation E p Q) :=
  (centralizerQuotientConjugationRepresentation_injective E p).comp
    Q.subtype_injective

end Submission.OddOrder.BG.AppendixAB
