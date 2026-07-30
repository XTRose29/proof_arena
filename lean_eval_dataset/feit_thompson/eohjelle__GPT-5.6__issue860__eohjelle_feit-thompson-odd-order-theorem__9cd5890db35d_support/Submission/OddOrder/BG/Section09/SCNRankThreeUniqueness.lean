import Submission.OddOrder.BG.Section09.SCNCommutatorUniqueMaximal

/-!
# Bender--Glauberman Lemma 9.5

The final contradiction in `BGsection9.v`: every SCN subgroup of rank at
least three in a Sylow subgroup of the minimal counterexample has a unique
maximal overgroup.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection9.v: SCN_3_Uniqueness` (Bender--Glauberman Lemma 9.5). -/
theorem SCN_3_Uniqueness
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : A ∈ minSimple_SCN_at (G := G) 3 p) :
    A ∈ minSimple_uniq_max_groups (G := G) := by
  classical
  rcases hA with ⟨P, hSCN, hRankA⟩
  by_contra hnotuniq

  have hAp : IsPGroup p A :=
    IsPGroup.to_le P.isPGroup' hSCN.le_sylow
  obtain ⟨E, hEA, hE⟩ :=
    exists_elementaryAbelian_rank_three_le_of_group_rank
      A hAp hSCN.commutative hRankA
  have hEne : E ≠ ⊥ := by
    apply E.one_lt_card_iff_ne_bot.mp
    rw [hE.card_eq]
    exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)
  have hAne : A ≠ ⊥ := by
    intro hAbot
    exact hEne (eq_bot_iff.mpr (hEA.trans hAbot.le))

  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  have hCproper : C < ⊤ := by
    simpa only [C] using mFT_cent_proper A hAne
  obtain ⟨M, hM, hCM⟩ := mmax_exists C hCproper

  have hCuniq : C ∈ minSimple_uniq_max_groups (G := G) := by
    apply (uniq_mmax_subset1 hM hCM).mpr
    intro L hL
    rw [Set.mem_singleton_iff]
    have hfamilyM :=
      normalizer_sylow_commutator_unique_maximal_of_scn_not_unique
        P hSCN hRankA hnotuniq hM (by simpa only [C] using hCM)
    have hfamilyL :=
      normalizer_sylow_commutator_unique_maximal_of_scn_not_unique
        P hSCN hRankA hnotuniq hL.1 (by
          intro x hx
          exact hL.2 hx)
    exact (Set.singleton_injective
      (hfamilyM.symm.trans hfamilyL)).symm

  have hAcentralC : A ≤ Subgroup.centralizer (C : Set G) := by
    apply Subgroup.le_centralizer_iff.mpr
    simpa only [C] using
      (le_rfl : Subgroup.centralizer (A : Set G) ≤
        Subgroup.centralizer (A : Set G))

  have htopCard : p ^ 2 ≤ Nat.card (⊤ : Subgroup E) := by
    rw [Subgroup.card_top, hE.card_eq]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  obtain ⟨B₀, _hB₀top, hB₀card⟩ :=
    Sylow.exists_subgroup_le_card_pow_prime_of_le_card
      (G := E) (Fact.out : p.Prime) hE.isPGroup htopCard
  letI : IsMulCommutative E := hE.commutative
  have hB₀ : IsElementaryAbelianOfRank p 2 B₀ := by
    refine
      { isPGroup := hE.isPGroup.to_subgroup B₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hB₀card }
    intro b
    apply Subtype.ext
    exact hE.pow_eq_one (b : E)
  let B : Subgroup G := B₀.map E.subtype
  have hB : IsElementaryAbelianOfRank p 2 B := by
    dsimp only [B]
    exact hB₀.map_of_injective E.subtype E.subtype_injective
  have hBA : B ≤ A := by
    dsimp only [B]
    exact (Subgroup.map_subtype_le B₀).trans hEA
  have hRankAtLeastTwo : HasElementaryAbelianRankAtLeast p 2 A :=
    ⟨B, hBA, hB⟩

  exact hnotuniq
    (cent_uniq_Uniqueness hCuniq hAcentralC
      ⟨p, Fact.out, hRankAtLeastTwo⟩)

end Submission.OddOrder.BG.Section09
