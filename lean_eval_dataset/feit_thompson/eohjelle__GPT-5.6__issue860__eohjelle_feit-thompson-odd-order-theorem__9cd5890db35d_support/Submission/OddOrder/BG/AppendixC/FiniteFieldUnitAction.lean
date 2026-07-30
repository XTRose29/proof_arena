import Submission.OddOrder.BG.AppendixC.FiniteFieldImage

/-!
# Cyclicity of the Appendix C unit action

This is the short block immediately preceding the norm calculation in
`BGappendixC.v`, lines 152--155.  Every subgroup of the unit group of a
finite field is cyclic.  The faithful unit-valued map in a
`FiniteFieldImage` therefore makes the acting group `U` cyclic, and hence
commutative.
-/

namespace Submission.OddOrder.BG.AppendixC

universe u v

variable {G : Type u} [Group G]

/-- `BGappendixC.v: cycFU`: every subgroup of the unit group of a finite
field is cyclic. -/
theorem finiteFieldUnitSubgroup_isCyclic
    (F : Type v) [Field F] [Fintype F] (S : Subgroup Fˣ) :
    IsCyclic S := by
  infer_instance

namespace FiniteFieldImage

variable {P P0 U : Subgroup G} (h : FiniteFieldImage P P0 U)

include h

/-- Faithfulness transports cyclicity of the finite-field unit group back
to the acting group `U`. -/
theorem actingGroup_isCyclic : IsCyclic U := by
  apply isCyclic_of_injective h.psi
  exact h.psi_injective

/-- `BGappendixC.v: cUU`: the acting group `U` is abelian. -/
theorem actingGroup_isMulCommutative : IsMulCommutative U := by
  letI : IsCyclic U := h.actingGroup_isCyclic
  infer_instance

end FiniteFieldImage

end Submission.OddOrder.BG.AppendixC
