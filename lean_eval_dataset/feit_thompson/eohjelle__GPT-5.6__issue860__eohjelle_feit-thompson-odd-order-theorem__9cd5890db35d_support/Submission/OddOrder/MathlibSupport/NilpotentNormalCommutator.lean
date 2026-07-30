import Mathlib.GroupTheory.Nilpotent

/-!
Strict commutator descent for normal subgroups of nilpotent groups.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Group.IsNilpotent G]

/-- If `H` is a nontrivial normal subgroup of a nilpotent group, then
`[H,G]` is a proper subgroup of `H`. -/
theorem commutator_top_lt_of_normal_ne_bot {H : Subgroup G} [H.Normal]
    (hH : H ≠ ⊥) : ⁅H, (⊤ : Subgroup G)⁆ < H := by
  have hle : ⁅H, (⊤ : Subgroup G)⁆ ≤ H :=
    Subgroup.commutator_le_left H ⊤
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hfixed : ⁅H, (⊤ : Subgroup G)⁆ = H := heq
  have hseries : ∀ n : ℕ, H ≤
      (Subgroup.lowerCentralSeries (⊤ : Subgroup G) n) := by
    intro n
    induction n with
    | zero => exact le_top
    | succ n ih =>
        rw [Subgroup.lowerCentralSeries_succ, ← hfixed]
        exact Subgroup.commutator_mono ih le_rfl
  have hbot := Subgroup.lowerCentralSeries_nilpotencyClass (G := G)
  have : H ≤ ⊥ := hbot ▸ hseries (Group.nilpotencyClass G)
  exact hH (le_bot_iff.mp this)

end Submission.OddOrder.MathlibSupport
