import Mathlib
import Submission.FrobeniusKernel

namespace Submission

theorem frobenius_kernel_isNormal (G X : Type) [Group G] [Fintype G] [Fintype X]
    [MulAction G X] [FaithfulSMul G X]
    (hcard : 2 ≤ Fintype.card X)
    (htrans : ∀ x y : X, ∃ g : G, g • x = y)
    (_hstab : ∀ x : X, MulAction.stabilizer G x ≠ ⊥)
    (hfrob : ∀ g : G, g ≠ 1 → ∀ x y : X, g • x = x → g • y = y → x = y) :
    ∃ N : Subgroup G, N.Normal ∧
      (N : Set G) = {1} ∪ {g : G | ∀ x : X, g • x ≠ x} := by
  classical
  have hX : Nonempty X := Fintype.card_pos_iff.mp (by omega)
  let D := Helpers.TransitiveActionData.ofTransitive G X hX.some htrans
  exact Helpers.exists_normal_frobeniusKernel D hfrob

end Submission
