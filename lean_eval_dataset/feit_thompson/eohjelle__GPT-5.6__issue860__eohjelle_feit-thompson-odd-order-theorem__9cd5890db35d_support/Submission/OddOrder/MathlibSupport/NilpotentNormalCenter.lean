import Mathlib.GroupTheory.Nilpotent

/-!
Nontrivial normal subgroups of nilpotent groups meet the center.
-/

namespace Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G]

/-- The relative lower central series obtained by repeatedly commuting a
normal subgroup with the ambient group. -/
private def relativeLowerCentralSeries (N : Subgroup G) : ℕ → Subgroup G
  | 0 => N
  | n + 1 => ⁅relativeLowerCentralSeries N n, (⊤ : Subgroup G)⁆

private theorem relativeLowerCentralSeries_le_lowerCentralSeries
    (N : Subgroup G) (n : ℕ) :
    relativeLowerCentralSeries N n ≤
      (⊤ : Subgroup G).lowerCentralSeries n := by
  induction n with
  | zero => exact le_top
  | succ n ih =>
      simpa [relativeLowerCentralSeries, Subgroup.lowerCentralSeries_succ] using
        Subgroup.commutator_mono ih le_rfl

private theorem relativeLowerCentralSeries_le
    (N : Subgroup G) [N.Normal] (n : ℕ) :
    relativeLowerCentralSeries N n ≤ N := by
  induction n with
  | zero => exact le_rfl
  | succ n ih =>
      exact (Subgroup.commutator_mono ih le_rfl).trans
        (Subgroup.commutator_le_left N (⊤ : Subgroup G))

/-- A nontrivial normal subgroup of a nilpotent group has nontrivial
intersection with the center. -/
theorem nilpotent_normal_inf_center_ne_bot [Group.IsNilpotent G]
    (N : Subgroup G) [N.Normal] (hN : N ≠ ⊥) :
    N ⊓ Subgroup.center G ≠ ⊥ := by
  classical
  obtain ⟨n, hn⟩ :=
    (Subgroup.nilpotent_iff_lowerCentralSeries (G := G)).mp
      (inferInstance : Group.IsNilpotent G)
  have hex : ∃ n, relativeLowerCentralSeries N n = ⊥ := by
    refine ⟨n, le_bot_iff.mp ?_⟩
    exact (relativeLowerCentralSeries_le_lowerCentralSeries N n).trans hn.le
  let m := Nat.find hex
  have hm : relativeLowerCentralSeries N m = ⊥ := Nat.find_spec hex
  have hm0 : m ≠ 0 := by
    intro hmzero
    apply hN
    simpa [m, hmzero, relativeLowerCentralSeries] using hm
  obtain ⟨d, hmEq⟩ := Nat.exists_eq_succ_of_ne_zero hm0
  have hd : relativeLowerCentralSeries N d ≠ ⊥ := by
    intro hdbot
    have hdlt : d < m := by rw [hmEq]; exact Nat.lt_succ_self d
    exact Nat.find_min hex hdlt hdbot
  have hcentral : relativeLowerCentralSeries N d ≤ Subgroup.center G := by
    have hcomm : ⁅relativeLowerCentralSeries N d, (⊤ : Subgroup G)⁆ = ⊥ := by
      simpa [hmEq, relativeLowerCentralSeries] using hm
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer] at hcomm
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subgroup.mem_centralizer_iff.mp (hcomm hx) y (Subgroup.mem_top y)
  intro hinf
  apply hd
  apply le_bot_iff.mp
  rw [← hinf]
  exact le_inf (relativeLowerCentralSeries_le N d) hcentral

end Submission.OddOrder.MathlibSupport
