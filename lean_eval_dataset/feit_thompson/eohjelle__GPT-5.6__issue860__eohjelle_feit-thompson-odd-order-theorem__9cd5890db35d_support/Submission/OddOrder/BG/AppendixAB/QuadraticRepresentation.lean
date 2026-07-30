import Submission.OddOrder.BG.AppendixAB.LocalConjugationRepresentation
import Submission.OddOrder.BG.AppendixAB.QuadraticElement

/-!
Square-zero operators arising from quadratic elements.

This is the basis-free form of the `Ax2` and `Ay2` calculations in
`BGappendixAB.odd_p_stable`.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative commutatorElement
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The deviation of conjugation by `g` from the identity on `E`. -/
def conjugationDeviation
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    (g : Subgroup.normalizer (E : Set G)) :
    Module.End (ZMod p) (Additive E) :=
  normalizerConjugationRepresentation E p g - 1

/-- A quadratic element acts with square-zero deviation from the identity. -/
theorem conjugationDeviation_mul_self_eq_zero
    (E : Subgroup G) (p : ℕ) [IsMulCommutative E]
    [Module (ZMod p) (Additive E)]
    {g : G} (hgN : g ∈ Subgroup.normalizer (E : Set G))
    (hg : IsQuadraticPElement p E g) :
    conjugationDeviation E p ⟨g, hgN⟩ *
        conjugationDeviation E p ⟨g, hgN⟩ = 0 := by
  let gn : Subgroup.normalizer (E : Set G) := ⟨g, hgN⟩
  let D := conjugationDeviation E p gn
  apply LinearMap.ext
  intro z
  change D (D z) = 0
  let d : Additive E := D z
  change D d = 0
  have hdcoe : d.toMul.1 = ⁅g, z.toMul.1⁆ := by
    dsimp [d, D, conjugationDeviation]
    change (g * z.toMul.1 * g⁻¹) / z.toMul.1 = ⁅g, z.toMul.1⁆
    rw [div_eq_mul_inv]
    rfl
  have hdmem : d.toMul.1 ∈
      (⁅E, Subgroup.zpowers g⁆ : Subgroup G) := by
    rw [hdcoe, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.mem_zpowers g) z.toMul.2
  have hcomm : g * d.toMul.1 = d.toMul.1 * g :=
    (Subgroup.mem_centralizer_iff.mp hg.2 d.toMul.1 hdmem).symm
  have hfix : normalizerConjugationRepresentation E p gn d = d := by
    apply congrArg Additive.ofMul
    apply Subtype.ext
    change g * d.toMul.1 * g⁻¹ = d.toMul.1
    rw [hcomm]
    simp
  simp [D, conjugationDeviation, hfix]

end Submission.OddOrder.BG.AppendixAB
