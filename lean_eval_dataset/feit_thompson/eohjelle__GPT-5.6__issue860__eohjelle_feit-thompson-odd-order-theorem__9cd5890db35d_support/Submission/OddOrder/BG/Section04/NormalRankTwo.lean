import Submission.OddOrder.MathlibSupport.Cardinality
import Submission.OddOrder.MathlibSupport.NormalSubgroupPowerSeries
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial

/-!
Normal elementary abelian rank-two subgroups in odd noncyclic finite
`p`-groups.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection4.v: ex_odd_normal_p2Elem` (Bender-Glauberman Lemma 4.5(a)). -/
theorem ex_odd_normal_p2Elem
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (hncyc : ¬ IsCyclic G) :
    ∃ S : Subgroup G, S.Normal ∧ IsElementaryAbelianOfRank p 2 S := by
  classical
  let P : Subgroup G → Prop := fun M ↦ M.Normal ∧ ¬ IsCyclic M
  have hPtop : P ⊤ := by
    refine ⟨inferInstance, ?_⟩
    intro hcyclic
    exact hncyc (Subgroup.topEquiv.isCyclic.mp hcyclic)
  obtain ⟨M, _, hMmin⟩ := Finite.exists_le_minimal hPtop
  have hPM : P M := hMmin.1
  have hMnormal : M.Normal := hPM.1
  have hncycM : ¬ IsCyclic M := hPM.2
  letI : M.Normal := hMnormal
  have hMG : IsPGroup p M := hG.to_subgroup M
  obtain ⟨n, hMcard⟩ := hMG.exists_card_eq
  have hn : n ≠ 0 := by
    intro hn
    apply hncycM
    have hMbot : M = ⊥ := by
      apply Subgroup.eq_bot_of_card_eq
      rw [hMcard, hn, pow_zero]
    rw [hMbot]
    infer_instance
  obtain ⟨e, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hn
  obtain ⟨N, hNM, hNnormal, hNcard⟩ :=
    exists_normal_subgroup_card_pow_le hG M hMcard (Nat.le_succ e)
  have hcardNM : Nat.card N < Nat.card M := by
    rw [hNcard, hMcard]
    exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt (Nat.lt_succ_self e)
  have hNMne : N ≠ M := by
    intro hNM'
    rw [hNM'] at hcardNM
    exact (Nat.lt_irrefl _ hcardNM)
  have hNcyc : IsCyclic N := by
    by_contra hncycN
    have hPN : P N := ⟨hNnormal, hncycN⟩
    have hMN : M = N := hMmin.eq_of_ge hPN hNM
    exact hNMne hMN.symm
  let NM : Subgroup M := N.subgroupOf M
  have hNMcyc : IsCyclic NM := by
    exact (Subgroup.subgroupOfEquivOfLe hNM).isCyclic.mpr hNcyc
  obtain ⟨x, hx⟩ :=
    (NM.isCyclic_iff_exists_zpowers_eq_top).mp hNMcyc
  have hNMcard : Nat.card NM = p ^ e := by
    exact (Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hNM).toEquiv).trans hNcard
  have hindex : (Subgroup.zpowers x).index = p := by
    rw [hx]
    apply Nat.mul_right_cancel (pow_pos (Fact.out : p.Prime).pos e)
    calc
      NM.index * p ^ e = NM.index * Nat.card NM := by rw [hNMcard]
      _ = Nat.card M := NM.index_mul_card
      _ = p ^ (e + 1) := hMcard
      _ = p * p ^ e := by rw [pow_succ, mul_comm]
  have hOmega : IsElementaryAbelianOfRank p 2 (omegaOne p M) :=
    omegaOne_isElementaryAbelian_rank_two_of_cyclic_subgroup_index_prime
      hMG (odd_natCard_subgroup M hodd) hncycM x hindex
  let S : Subgroup G := (omegaOne p M).map M.subtype
  have hSnormal : S.Normal := by
    dsimp [S]
    infer_instance
  have hSp : IsPGroup p S := by
    dsimp [S]
    exact hOmega.isPGroup.map M.subtype
  have hScomm : IsMulCommutative S := by
    letI : IsMulCommutative (omegaOne p M) := hOmega.commutative
    dsimp [S]
    infer_instance
  have hSpow : ∀ s : S, s ^ p = 1 := by
    rintro ⟨s, hs⟩
    apply Subtype.ext
    change s ^ p = 1
    dsimp [S] at hs
    obtain ⟨z, hz, rfl⟩ := hs
    simpa using congrArg (fun q : omegaOne p M ↦ ((q : M) : G))
      (hOmega.pow_eq_one ⟨z, hz⟩)
  have hScard : Nat.card S = p ^ 2 := by
    calc
      Nat.card S = Nat.card (omegaOne p M) := by
        dsimp [S]
        exact Subgroup.card_map_of_injective M.subtype_injective
      _ = p ^ 2 := hOmega.card_eq
  exact ⟨S, hSnormal,
    { isPGroup := hSp
      commutative := hScomm
      pow_eq_one := hSpow
      card_eq := hScard }⟩

end Submission.OddOrder.BG.Section04
