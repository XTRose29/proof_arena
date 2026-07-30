import Submission.OddOrder.BG.Section04.NormalRankTwo

/-!
Bender--Glauberman Proposition 4.6.

The rank-two subgroup from Lemma 4.5(a) can be chosen inside any prescribed
noncyclic normal subgroup of the ambient odd `p`-group.  The proof repeats the
minimal-normal argument with containment in the prescribed subgroup included
in the minimizing predicate.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- `BGsection4.v: odd_normal_p2Elem_exists` (Bender--Glauberman
Proposition 4.6). -/
theorem odd_normal_p2Elem_exists
    (hG : IsPGroup p G) (hodd : Odd (Nat.card G))
    (R : Subgroup G) [R.Normal] (hncyc : ¬ IsCyclic R) :
    ∃ E : Subgroup G,
      E ≤ R ∧ E.Normal ∧ IsElementaryAbelianOfRank p 2 E := by
  classical
  let P : Subgroup G → Prop := fun M ↦ M.Normal ∧ M ≤ R ∧ ¬ IsCyclic M
  have hPR : P R := ⟨inferInstance, le_rfl, hncyc⟩
  obtain ⟨M, hMR, hMmin⟩ := Finite.exists_le_minimal hPR
  have hPM : P M := hMmin.1
  have hMnormal : M.Normal := hPM.1
  have hncycM : ¬ IsCyclic M := hPM.2.2
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
    have hPN : P N :=
      ⟨hNnormal, hNM.trans hPM.2.1, hncycN⟩
    have hMN : M = N := hMmin.eq_of_ge hPN hNM
    exact hNMne hMN.symm
  let NM : Subgroup M := N.subgroupOf M
  have hNMcyc : IsCyclic NM :=
    (Subgroup.subgroupOfEquivOfLe hNM).isCyclic.mpr hNcyc
  obtain ⟨x, hx⟩ :=
    (NM.isCyclic_iff_exists_zpowers_eq_top).mp hNMcyc
  have hNMcard : Nat.card NM = p ^ e :=
    (Nat.card_congr
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
  let E : Subgroup G := (omegaOne p M).map M.subtype
  have hER : E ≤ R := by
    rintro y ⟨z, hz, rfl⟩
    exact hMR z.2
  have hEnormal : E.Normal := by
    dsimp [E]
    infer_instance
  have hEp : IsPGroup p E := by
    dsimp [E]
    exact hOmega.isPGroup.map M.subtype
  have hEcomm : IsMulCommutative E := by
    letI : IsMulCommutative (omegaOne p M) := hOmega.commutative
    dsimp [E]
    infer_instance
  have hEpow : ∀ y : E, y ^ p = 1 := by
    rintro ⟨y, hy⟩
    apply Subtype.ext
    change y ^ p = 1
    dsimp [E] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    simpa using congrArg (fun q : omegaOne p M ↦ ((q : M) : G))
      (hOmega.pow_eq_one ⟨z, hz⟩)
  have hEcard : Nat.card E = p ^ 2 := by
    calc
      Nat.card E = Nat.card (omegaOne p M) := by
        dsimp [E]
        exact Subgroup.card_map_of_injective M.subtype_injective
      _ = p ^ 2 := hOmega.card_eq
  exact ⟨E, hER, hEnormal,
    { isPGroup := hEp
      commutative := hEcomm
      pow_eq_one := hEpow
      card_eq := hEcard }⟩

end Submission.OddOrder.BG.Section04
