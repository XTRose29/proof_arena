import Submission.OddOrder.MathlibSupport.Solvability

/-!
Bridge from the future simple-group odd-order core to the Lean Eval statement.

This module contains the standard minimal-counterexample reduction: if every
finite simple group of odd order is solvable, then every finite group of odd
order is solvable.  The still-missing mathematical core is isolated as the
proposition `OddOrderSimpleCore`.
-/

namespace Submission.OddOrder

open Submission.OddOrder.MathlibSupport

universe u

/-- The mathematical core left to the Bender-Glauberman/Peterfalvi port. -/
def OddOrderSimpleCore : Prop :=
  ∀ {G : Type u} [Group G] [Finite G] [IsSimpleGroup G],
    Odd (Nat.card G) → IsSolvable G

theorem natCard_subgroup_lt_natCard_of_ne_top {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : H ≠ ⊤) : Nat.card H < Nat.card G := by
  have hle : Nat.card H ≤ Nat.card G :=
    Nat.le_of_dvd (Nat.card_pos (α := G)) H.card_subgroup_dvd_card
  exact lt_of_le_of_ne hle fun hcard =>
    hH (Subgroup.eq_top_of_card_eq H hcard)

theorem natCard_quotient_lt_natCard_of_ne_bot {G : Type u} [Group G] [Finite G]
    (H : Subgroup G) (hH : H ≠ ⊥) : Nat.card (G ⧸ H) < Nat.card G := by
  have hHcard : 1 < Nat.card H :=
    (Subgroup.one_lt_card_iff_ne_bot H).2 hH
  calc
    Nat.card (G ⧸ H) < Nat.card (G ⧸ H) * Nat.card H :=
      lt_mul_of_one_lt_right (Nat.card_pos (α := G ⧸ H)) hHcard
    _ = Nat.card G := (Subgroup.card_eq_card_quotient_mul_card_subgroup H).symm

theorem exists_proper_nontrivial_normal_of_not_isSimpleGroup {G : Type u} [Group G]
    [Nontrivial G] (h : ¬ IsSimpleGroup G) :
    ∃ N : Subgroup G, N.Normal ∧ N ≠ ⊥ ∧ N ≠ ⊤ := by
  classical
  by_contra hnone
  apply h
  exact
    { eq_bot_or_eq_top_of_normal := by
        intro N hN
        by_cases hbot : N = ⊥
        · exact Or.inl hbot
        · by_cases htop : N = ⊤
          · exact Or.inr htop
          · exact False.elim (hnone ⟨N, hN, hbot, htop⟩) }

theorem isSolvable_of_odd_order_simple_core (hCore : OddOrderSimpleCore.{u})
    {G : Type u} [Group G] [Finite G] (hodd : Odd (Nat.card G)) :
    IsSolvable G := by
  classical
  let P : ℕ → Prop := fun n =>
    ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K = n → Odd (Nat.card K) → IsSolvable K
  suffices hP : P (Nat.card G) from hP rfl hodd
  exact Nat.strong_induction_on (p := P) (Nat.card G) fun n ih => by
    intro K _ _ hcard hoddK
    by_cases hsub : Subsingleton K
    · haveI : Subsingleton K := hsub
      infer_instance
    · haveI : Nontrivial K := not_subsingleton_iff_nontrivial.mp hsub
      by_cases hsimp : IsSimpleGroup K
      · haveI : IsSimpleGroup K := hsimp
        exact hCore hoddK
      · obtain ⟨N, hNnormal, hNnebot, hNnetop⟩ :=
          exists_proper_nontrivial_normal_of_not_isSimpleGroup (G := K) hsimp
        haveI : N.Normal := hNnormal
        have hNodd : Odd (Nat.card N) :=
          odd_natCard_subgroup N hoddK
        have hQodd : Odd (Nat.card (K ⧸ N)) :=
          odd_natCard_quotient N hoddK
        have hNlt : Nat.card N < n := by
          rw [← hcard]
          exact natCard_subgroup_lt_natCard_of_ne_top N hNnetop
        have hQlt : Nat.card (K ⧸ N) < n := by
          rw [← hcard]
          exact natCard_quotient_lt_natCard_of_ne_bot N hNnebot
        haveI : IsSolvable N :=
          ih (Nat.card N) hNlt rfl hNodd
        haveI : IsSolvable (K ⧸ N) :=
          ih (Nat.card (K ⧸ N)) hQlt rfl hQodd
        exact isSolvable_of_normal_subgroup_and_quotient N

end Submission.OddOrder
