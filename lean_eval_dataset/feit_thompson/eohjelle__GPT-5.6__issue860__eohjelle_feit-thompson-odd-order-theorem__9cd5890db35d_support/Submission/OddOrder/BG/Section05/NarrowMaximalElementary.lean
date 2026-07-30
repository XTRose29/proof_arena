import Submission.OddOrder.BG.Section05.Equivariance

/-!
The first consequence of narrowness in Bender--Glauberman Section 5.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]
variable {p : ℕ}

/-- `BGsection5.v: narrow_pmaxElem`.

Under the rank-three hypothesis, the implication in the definition of
narrowness supplies a maximal elementary-abelian subgroup of rank two. -/
theorem narrow_pmaxElem {A : Subgroup G} (hA : IsNarrow p A)
    (hRank3 : ∃ E : Subgroup G,
      E ≤ A ∧ IsElementaryAbelianOfRank p 3 E) :
    ∃ E : Subgroup G,
      IsElementaryAbelianOfRank p 2 E ∧ IsPMaxElem p A E :=
  hA hRank3

end Submission.OddOrder.BG.Section05
