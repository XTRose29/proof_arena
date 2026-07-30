import Mathlib.GroupTheory.Commutator.Basic
import Mathlib.GroupTheory.QuotientGroup.Basic

/-!
Commutator bounds modulo a normal subgroup, extended over generated subgroups.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]
variable {R H₁ H₂ K N : Subgroup G}

/-- If two subgroups centralize `R` modulo a normal subgroup, then their join
does too. -/
theorem commutator_sup_le_of_normal [N.Normal]
    (h₁ : ⁅R, H₁⁆ ≤ N) (h₂ : ⁅R, H₂⁆ ≤ N) :
    ⁅R, H₁ ⊔ H₂⁆ ≤ N := by
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  have hmap₁ : ⁅R.map q, H₁.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simpa [q, QuotientGroup.ker_mk'] using h₁
  have hmap₂ : ⁅R.map q, H₂.map q⁆ = ⊥ := by
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff]
    simpa [q, QuotientGroup.ker_mk'] using h₂
  rw [← QuotientGroup.ker_mk' N, ← Subgroup.map_eq_bot_iff,
    Subgroup.map_commutator, Subgroup.map_sup]
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer,
    Subgroup.sup_eq_closure, Subgroup.centralizer_closure]
  have hc₁ := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmap₁
  have hc₂ := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hmap₂
  intro r hr
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  rcases hx with hx | hx
  · exact Subgroup.mem_centralizer_iff.mp (hc₁ hr) x hx
  · exact Subgroup.mem_centralizer_iff.mp (hc₂ hr) x hx

/-- A subgroup contained in a generated pair centralizes `R` modulo a normal
subgroup when both generators do. -/
theorem commutator_le_of_le_sup_of_normal [N.Normal]
    (hK : K ≤ H₁ ⊔ H₂)
    (h₁ : ⁅R, H₁⁆ ≤ N) (h₂ : ⁅R, H₂⁆ ≤ N) :
    ⁅R, K⁆ ≤ N :=
  (Subgroup.commutator_mono le_rfl hK).trans
    (commutator_sup_le_of_normal h₁ h₂)

end Submission.OddOrder.MathlibSupport
