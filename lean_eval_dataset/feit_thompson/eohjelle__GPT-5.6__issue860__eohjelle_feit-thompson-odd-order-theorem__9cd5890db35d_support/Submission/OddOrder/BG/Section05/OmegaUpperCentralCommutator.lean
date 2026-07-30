import Submission.OddOrder.BG.Section05.OmegaUpperCentralSetup
import Mathlib.Tactic.Group

/-!
The central commutator calculation for the omega-one subgroup of the second
upper center.
-/

namespace Submission.OddOrder.BG.Section05

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement

universe u

variable {G : Type u} [Group G]

private theorem commutatorElement_pow_left_of_mem_center
    {a b : G} (hcentral : ⁅a, b⁆ ∈ Subgroup.center G) :
    ∀ n : ℕ, ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, _root_.commutatorElement_mul_left_eq_conj_mul,
        commutatorElement_pow_left_of_mem_center hcentral n]
      have hcomm := Subgroup.mem_center_iff.mp hcentral (a ^ n)
      rw [hcomm]
      group

/-- If `W = Ω₁(Z₂(G))` has exponent dividing `p`, then `[W,G]` lies in
`Z = Ω₁(Z(G))`.  This is the `sWRZ` step in `BGsection5.v`. -/
theorem commutator_omegaOneUpperCentralTwo_le_omegaOneCenter
    (p : ℕ)
    (hpow : ∀ w : omegaOneUpperCentralTwo p G, w ^ p = 1) :
    ⁅omegaOneUpperCentralTwo p G, (⊤ : Subgroup G)⁆ ≤
      omegaOneCenter p G := by
  rw [Subgroup.commutator_le]
  intro w hw g _hg
  have hwZ₂ : w ∈ Subgroup.upperCentralSeries G 2 :=
    omegaOneUpperCentralTwo_le_upperCentralSeries p hw
  have hcommCenter : ⁅w, g⁆ ∈ Subgroup.center G := by
    have hmem := (Subgroup.mem_upperCentralSeries_succ_iff
      (G := G) (n := 1) (x := w)).mp (by simpa using hwZ₂) g
    simpa using hmem
  have hwp : w ^ p = 1 :=
    congrArg Subtype.val (hpow ⟨w, hw⟩)
  have hcommPow : ⁅w, g⁆ ^ p = 1 := by
    rw [← commutatorElement_pow_left_of_mem_center hcommCenter p,
      hwp, commutatorElement_one_left]
  let c : Subgroup.center G := ⟨⁅w, g⁆, hcommCenter⟩
  have hcPow : c ^ p = 1 := by
    apply Subtype.ext
    exact hcommPow
  exact ⟨c, mem_omegaOne_of_pow_eq_one p hcPow, rfl⟩

end Submission.OddOrder.BG.Section05
