import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.PMaxElem
import Mathlib.GroupTheory.SpecificGroups.Cyclic

/-!
The opening definitions of Bender--Glauberman Section 5.

MathComp defines `p.-narrow A` using the numerical `p`-rank of `A`.  As in
the Section 4 port, the mathlib-facing formulation records the equivalent
finite-group data directly: if `A` contains an elementary-abelian subgroup
of rank three, it contains a maximal elementary-abelian subgroup of rank
two.

MathComp's internal direct-product equality `S \x C = 'C_A(S)` is unpacked
in `NarrowStructure`: the two factors commute and have trivial intersection,
and their supremum is the centralizer of `S` in `A`.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- `BGsection5.v: narrow`.

The antecedent is the cardinal-rank form of `'r_p(A) > 2`; the consequent is
the predicate form of `'E_p^2(A) :&: 'E*_p(A) != set0`. -/
def IsNarrow (p : ℕ) (A : Subgroup G) : Prop :=
  (∃ E : Subgroup G, E ≤ A ∧ IsElementaryAbelianOfRank p 3 E) →
    ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 2 E ∧ IsPMaxElem p A E

/-- `BGsection5.v: narrow_structure`.

This is the internal direct-product decomposition of the centralizer used in
the original Bender--Glauberman definition of a narrow group. -/
def NarrowStructure (p : ℕ) (A : Subgroup G) : Prop :=
  ∃ s c : Subgroup G,
    s ≤ A ∧
      c ≤ A ∧
        Nat.card s = p ∧
          IsCyclic c ∧
            Disjoint s c ∧
              (∀ x ∈ s, ∀ y ∈ c, Commute x y) ∧
                s ⊔ c = centralizerWithin A s

end Submission.OddOrder.BG.Section05
