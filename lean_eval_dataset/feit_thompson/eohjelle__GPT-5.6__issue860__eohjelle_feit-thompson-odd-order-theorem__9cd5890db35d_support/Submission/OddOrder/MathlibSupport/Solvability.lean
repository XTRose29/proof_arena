import Submission.OddOrder.MathlibSupport.Cardinality

/-!
Solvability wrappers used by the odd-order port.

The Coq development repeatedly moves solvability across inclusions,
quotients, images, and simple-group reductions.  This module gives those moves
stable local names while delegating the proofs to mathlib.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G K : Type*} [Group G] [Group K]

theorem isSolvable_subgroup_of_isSolvable (H : Subgroup G) [IsSolvable G] :
    IsSolvable H :=
  inferInstance

theorem isSolvable_quotient_of_isSolvable (H : Subgroup G) [H.Normal] [IsSolvable G] :
    IsSolvable (G ⧸ H) :=
  inferInstance

theorem isSolvable_of_surjective (f : G →* K) (hf : Function.Surjective f)
    [IsSolvable G] : IsSolvable K :=
  solvable_of_surjective (f := f) hf

theorem isSolvable_of_normal_subgroup_and_quotient (N : Subgroup G) [N.Normal]
    [IsSolvable N] [IsSolvable (G ⧸ N)] : IsSolvable G :=
  solvable_of_ker_le_range N.subtype (QuotientGroup.mk' N) (by
    rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isSolvable_of_injective (f : G →* K) (hf : Function.Injective f)
    [IsSolvable K] : IsSolvable G :=
  solvable_of_solvable_injective (f := f) hf

theorem isSolvable_of_comm (h : ∀ a b : G, a * b = b * a) : IsSolvable G :=
  _root_.isSolvable_of_comm h

theorem isSolvable_of_subsingleton [Subsingleton G] : IsSolvable G :=
  inferInstance

theorem simple_isSolvable_iff_comm [IsSimpleGroup G] :
    IsSolvable G ↔ ∀ a b : G, a * b = b * a :=
  IsSimpleGroup.comm_iff_isSolvable.symm

end Submission.OddOrder.MathlibSupport
