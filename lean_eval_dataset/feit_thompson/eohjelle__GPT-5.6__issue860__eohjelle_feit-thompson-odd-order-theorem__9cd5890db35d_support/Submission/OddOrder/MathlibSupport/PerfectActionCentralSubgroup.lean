import Mathlib.GroupTheory.Commutator.Basic

/-!
The three-subgroups step used for characteristic subgroups under a perfect
coprime action.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]
variable {H K R : Subgroup G}

/-- If `H` is normalized by `K`, centralized by `R`, and `[R,K] = K`, then
`H` centralizes `K`. -/
theorem le_centralizer_of_normalized_of_centralized_of_perfect_action
    (hnormH : K ≤ Subgroup.normalizer (H : Set G))
    (hcentral : R ≤ Subgroup.centralizer (H : Set G))
    (hperfect : ⁅R, K⁆ = K) :
    H ≤ Subgroup.centralizer (K : Set G) := by
  have hKH : ⁅K, H⁆ ≤ H :=
    Subgroup.le_normalizer_iff_commutator_le_right.mp hnormH
  have hRH : ⁅R, H⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentral
  have hHR : ⁅H, R⁆ = ⊥ := by
    rw [Subgroup.commutator_comm]
    exact hRH
  have hKHR : ⁅⁅K, H⁆, R⁆ = ⊥ := by
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hKH.trans
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hHR)
  have hHRK : ⁅⁅H, R⁆, K⁆ = ⊥ := by simp [hHR]
  have hRKH : ⁅⁅R, K⁆, H⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hKHR hHRK
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.commutator_comm, ← hperfect]
  exact hRKH

end Submission.OddOrder.MathlibSupport
