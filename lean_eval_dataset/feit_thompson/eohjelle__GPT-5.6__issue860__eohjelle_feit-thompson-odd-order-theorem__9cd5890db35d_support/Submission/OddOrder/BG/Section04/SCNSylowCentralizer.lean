import Submission.OddOrder.MathlibSupport.SCNCentralizer

/-!
Bender-Glauberman Proposition 4.4(b): the centralizer decomposition attached
to a self-centralizing normal abelian subgroup of a Sylow subgroup.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- `BGsection4.v: SCN_Sylow_cent_dprod` (Bender-Glauberman Proposition
4.4(b)). The Sylow subgroup of the full centralizer induced by `A` maps back
to `A`, and the `p'`-core of that centralizer is its complement. -/
theorem SCN_Sylow_cent_dprod
    (R : Sylow p G) (A : Subgroup G) (hA : IsSCN (R : Subgroup G) A) :
    let C := Subgroup.centralizer (A : Set G)
    let Q := scnSylowInCentralizer R A hA
    (Q : Subgroup C).map C.subtype = A ∧
      (pPrimeCore p C).IsComplement' (Q : Subgroup C) := by
  dsimp only
  exact ⟨map_scnSylowInCentralizer_eq R A hA,
    pPrimeCore_isComplement_scnSylowInCentralizer R A hA⟩

end Submission.OddOrder.BG.Section04
