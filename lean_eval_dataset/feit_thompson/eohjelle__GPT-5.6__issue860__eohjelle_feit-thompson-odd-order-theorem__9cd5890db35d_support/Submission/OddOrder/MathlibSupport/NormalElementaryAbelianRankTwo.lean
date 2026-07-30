import Submission.OddOrder.MathlibSupport.ElementaryAbelian
import Submission.OddOrder.MathlibSupport.NilpotentNormalCommutator
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Submission.OddOrder.MathlibSupport.UpperCentralDerived

/-!
Normal elementary abelian subgroups of rank two in finite `p`-groups.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped commutatorElement

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A normal subgroup of order `p²` in a finite `p`-group has vanishing
second mixed commutator. -/
theorem second_mixed_commutator_eq_bot_of_card_prime_sq
    (hG : IsPGroup p G) (S : Subgroup G) [S.Normal]
    (hcard : Nat.card S = p ^ 2) :
    ⁅⁅S, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ = ⊥ := by
  letI : Group.IsNilpotent G := hG.isNilpotent
  let T : Subgroup G := ⁅S, (⊤ : Subgroup G)⁆
  let U : Subgroup G := ⁅T, (⊤ : Subgroup G)⁆
  change U = ⊥
  have hSnon : S ≠ ⊥ := by
    apply S.one_lt_card_iff_ne_bot.mp
    rw [hcard]
    exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by decide : (2 : ℕ) ≠ 0)
  have hTlt : T < S := by
    exact commutator_top_lt_of_normal_ne_bot hSnon
  by_cases hTbot : T = ⊥
  · dsimp [U]
    rw [hTbot]
    simp
  have hpT : IsPGroup p T := hG.to_subgroup T
  obtain ⟨n, hncard⟩ := hpT.exists_card_eq
  have hTcardlt : Nat.card T < Nat.card S :=
    natCard_subgroup_lt_of_lt hTlt
  have hpownlt : p ^ n < p ^ 2 := by
    calc
      p ^ n = Nat.card T := hncard.symm
      _ < Nat.card S := hTcardlt
      _ = p ^ 2 := hcard
  have hnpos : 0 < n := by
    by_contra hn
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn
    apply hTbot
    apply Subgroup.eq_bot_of_card_eq
    rw [hncard, hnzero, pow_zero]
  have hnlt : n < 2 := by
    by_contra hn
    exact (not_lt_of_ge (Nat.pow_le_pow_right (Fact.out : p.Prime).pos
      (Nat.le_of_not_gt hn))) hpownlt
  have hn : n = 1 := by omega
  have hTcard : Nat.card T = p := by simpa [hn] using hncard
  letI : T.Normal := by
    dsimp [T]
    infer_instance
  letI : U.Normal := by
    dsimp [U]
    infer_instance
  by_contra hUbot
  have hUlt : U < T := by
    change ⁅T, (⊤ : Subgroup G)⁆ < T
    exact commutator_top_lt_of_normal_ne_bot hTbot
  have hpU : IsPGroup p U := hG.to_subgroup U
  obtain ⟨m, hmcard⟩ := hpU.exists_card_eq
  have hUcardlt : Nat.card U < Nat.card T :=
    natCard_subgroup_lt_of_lt hUlt
  have hpowmlt : p ^ m < p ^ 1 := by
    calc
      p ^ m = Nat.card U := hmcard.symm
      _ < Nat.card T := hUcardlt
      _ = p ^ 1 := by simpa using hTcard
  have hmpos : 0 < m := by
    by_contra hm
    have hmzero : m = 0 := Nat.eq_zero_of_not_pos hm
    apply hUbot
    apply Subgroup.eq_bot_of_card_eq
    rw [hmcard, hmzero, pow_zero]
  have hmone : 1 ≤ m := hmpos
  exact (not_lt_of_ge
    (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hmone)) hpowmlt

/-- A normal elementary abelian rank-two subgroup of a finite `p`-group
lies in `Z₂(G)`. -/
theorem normal_elementaryAbelian_rank_two_le_upperCentralSeries_two
    (hG : IsPGroup p G) (S : Subgroup G) [S.Normal]
    (hS : IsElementaryAbelianOfRank p 2 S) :
    S ≤ Subgroup.upperCentralSeries G 2 := by
  have htriple := second_mixed_commutator_eq_bot_of_card_prime_sq
    hG S hS.card_eq
  intro s hs
  rw [Subgroup.mem_upperCentralSeries_succ_iff]
  intro g
  rw [Subgroup.upperCentralSeries_one, Subgroup.mem_center_iff]
  intro y
  have hfirst : ⁅s, g⁆ ∈ ⁅S, (⊤ : Subgroup G)⁆ :=
    Subgroup.commutator_mem_commutator hs (Subgroup.mem_top g)
  have hsecond : ⁅⁅s, g⁆, y⁆ ∈
      ⁅⁅S, (⊤ : Subgroup G)⁆, (⊤ : Subgroup G)⁆ :=
    Subgroup.commutator_mem_commutator hfirst (Subgroup.mem_top y)
  have hone : ⁅⁅s, g⁆, y⁆ = 1 := by
    rw [htriple] at hsecond
    exact Subgroup.mem_bot.mp hsecond
  exact (commutatorElement_eq_one_iff_mul_comm.mp hone).symm

end Submission.OddOrder.MathlibSupport
