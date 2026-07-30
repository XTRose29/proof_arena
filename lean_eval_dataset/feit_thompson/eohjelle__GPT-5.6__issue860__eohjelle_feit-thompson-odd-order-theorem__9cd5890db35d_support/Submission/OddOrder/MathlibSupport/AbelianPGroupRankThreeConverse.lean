import Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree
import Submission.OddOrder.MathlibSupport.MetacyclicSubgroups

/-!
Recovering the generator-rank bound from an elementary-abelian subgroup of
cardinal rank three in a commutative finite group.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped IsMulCommutative

universe u

private theorem isMetacyclic_of_isMulCommutative_of_rank_le_two
    {G : Type u} [Group G] [Finite G]
    (hGcomm : IsMulCommutative G) (hRank : Group.rank G ≤ 2) :
    IsMetacyclic G := by
  classical
  letI : IsMulCommutative G := hGcomm
  obtain ⟨S, hScard, hSgen⟩ := Group.rank_spec G
  have hCard : S.card ≤ 2 := by omega
  interval_cases h : S.card
  · have hRankZero : Group.rank G = 0 := by omega
    haveI : Subsingleton G := Group.rank_eq_zero_iff.mp hRankZero
    exact isMetacyclic_of_isCyclic G isCyclic_of_subsingleton
  · obtain ⟨x, rfl⟩ := Finset.card_eq_one.mp h
    have hx : Subgroup.zpowers x = (⊤ : Subgroup G) := by
      rw [Subgroup.zpowers_eq_closure]
      simpa only [Finset.coe_singleton] using hSgen
    exact isMetacyclic_of_isMulCommutative_of_two_generators x 1 (by
      simp only [hx, Subgroup.zpowers_one_eq_bot, sup_bot_eq])
  · obtain ⟨x, y, _hxy, rfl⟩ := Finset.card_eq_two.mp h
    apply isMetacyclic_of_isMulCommutative_of_two_generators x y
    rw [Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    simpa only [Finset.coe_insert, Finset.coe_singleton,
      Set.singleton_union] using hSgen

private theorem not_isMetacyclic_of_elementaryAbelian_rank_three
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 3 E) :
    ¬ IsMetacyclic E := by
  classical
  rintro ⟨S, hSnormal, hScyclic, hQcyclic⟩
  letI : S.Normal := hSnormal
  letI : IsCyclic S := hScyclic
  letI : IsCyclic (E ⧸ S) := hQcyclic
  have hSpow : ∀ x : S, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    exact hE.pow_eq_one (x : E)
  have hScard : Nat.card S ≤ p := by
    letI := Fintype.ofFinite S
    rw [Nat.card_eq_fintype_card]
    simpa only [hSpow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le (α := S) (Fact.out : p.Prime).pos)
  have hQpow : ∀ x : E ⧸ S, x ^ p = 1 := by
    intro x
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective S x
    simpa only [map_pow, map_one] using
      congrArg (QuotientGroup.mk' S) (hE.pow_eq_one y)
  have hQcard : Nat.card (E ⧸ S) ≤ p := by
    letI := Fintype.ofFinite (E ⧸ S)
    rw [Nat.card_eq_fintype_card]
    simpa only [hQpow, Finset.filter_true, Finset.card_univ] using
      (IsCyclic.card_pow_eq_one_le
        (α := E ⧸ S) (Fact.out : p.Prime).pos)
  have hPowLe : p ^ 3 ≤ p ^ 2 := by
    rw [← hE.card_eq,
      Subgroup.card_eq_card_quotient_mul_card_subgroup S, pow_two]
    exact Nat.mul_le_mul hQcard hScard
  have : (3 : ℕ) ≤ 2 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hPowLe
  omega

/-- A commutative finite `p`-subgroup containing an elementary-abelian
subgroup of cardinal rank three has generator rank at least three. -/
theorem group_rank_ge_three_of_exists_elementaryAbelian_rank_three_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (A : Subgroup G)
    (_hAp : IsPGroup p A)
    (hAcomm : IsMulCommutative A)
    (hRank3 : ∃ E : Subgroup G,
      E ≤ A ∧ IsElementaryAbelianOfRank p 3 E) :
    3 ≤ Group.rank A := by
  classical
  by_contra hRank
  have hRankLe : Group.rank A ≤ 2 := by omega
  have hAmeta : IsMetacyclic A :=
    isMetacyclic_of_isMulCommutative_of_rank_le_two hAcomm hRankLe
  obtain ⟨E, hEA, hE⟩ := hRank3
  let EA : Subgroup A := E.subgroupOf A
  have hEAmeta : IsMetacyclic EA := isMetacyclic_subgroup hAmeta EA
  let e : EA ≃* E := Subgroup.subgroupOfEquivOfLe hEA
  have hEmeta : IsMetacyclic E :=
    isMetacyclic_of_mulEquiv E e.symm hEAmeta
  exact not_isMetacyclic_of_elementaryAbelian_rank_three hE hEmeta

end Submission.OddOrder.MathlibSupport
