import Mathlib.GroupTheory.Sylow
import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
The first alternating `p'`, `p` core layer.

MathComp's predicate `p.-length_1 G` is characterized by the assertion that
the `p`-core of `G / O_{p'}(G)` is a Sylow subgroup.  We use that
characterization as the Lean-facing definition.
-/

namespace Submission.OddOrder.MathlibSupport

variable (p : ℕ) (G : Type*) [Group G] [Finite G]

/-- A finite group has `p`-length at most one when the `p`-core after
quotienting by `O_{p'}` is a Sylow `p`-subgroup. -/
def IsPLengthOne : Prop :=
  ∃ P : Sylow p (G ⧸ pPrimeCore p G),
    (P : Subgroup (G ⧸ pPrimeCore p G)) =
      pCore p (G ⧸ pPrimeCore p G)

end Submission.OddOrder.MathlibSupport
