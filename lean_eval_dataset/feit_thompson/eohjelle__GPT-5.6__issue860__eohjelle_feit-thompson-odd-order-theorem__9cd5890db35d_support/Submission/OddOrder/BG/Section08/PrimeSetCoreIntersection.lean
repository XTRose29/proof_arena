import Submission.OddOrder.BG.Section07.NormedSubgroups
import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
# Bender--Glauberman, Section 8: intersecting prime-complement cores

This file ports the `bigcap_p'core` introduction step used in the proof of
Bender--Glauberman Theorem 8.1(a).
-/

namespace Submission.OddOrder.BG.Section08

open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.BG.Section07

universe u

/-- A subgroup contained in `X` and in every mapped `q`-prime core for
`q ∈ pi` lies in the `pi`-prime core of `X`. -/
theorem le_primeSetCore_compl_of_le_map_pPrimeCore
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {X Y : Subgroup G}
    (hYX : Y ≤ X)
    (hYcore : ∀ q, q ∈ pi →
      Y ≤ (pPrimeCore q X).map X.subtype) :
    Y ≤ primeSetCore piᶜ X := by
  let KX : Subgroup X := ⨅ q : pi, pPrimeCore (q : ℕ) X
  let K : Subgroup G := KX.map X.subtype
  have hYsubKX : Y.subgroupOf X ≤ KX := by
    dsimp [KX]
    refine le_iInf fun q => ?_
    apply (Subgroup.map_le_map_iff_of_injective X.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le hYX]
    exact hYcore q q.property
  have hYK : Y ≤ K := by
    dsimp [K]
    rw [← Subgroup.map_subgroupOf_eq_of_le hYX]
    exact Subgroup.map_mono hYsubKX
  have hKXambient : K ≤ X := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  have hKnormal : (K.subgroupOf X).Normal := by
    change ((KX.map X.subtype).comap X.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    dsimp [KX]
    exact Subgroup.normal_iInf_normal fun _ => inferInstance
  have hKcard : Nat.card K = Nat.card KX := by
    dsimp [K]
    exact Subgroup.card_map_of_injective X.subtype_injective
  have hKpi : IsPiNumber piᶜ (Nat.card K) := by
    intro q hqPrime hqK hqpi
    have hKXcore : KX ≤ pPrimeCore q X := by
      dsimp [KX]
      exact iInf_le_of_le ⟨q, hqpi⟩ le_rfl
    have hqKX : q ∣ Nat.card KX := by
      rw [← hKcard]
      exact hqK
    have hqCore : q ∣ Nat.card (pPrimeCore q X) :=
      hqKX.trans (Subgroup.card_dvd_of_le hKXcore)
    exact (hqPrime.coprime_iff_not_dvd.mp
      (pPrimeCore_coprime_card (G := X) (p := q))) hqCore
  have hKcore : K ≤ primeSetCore piᶜ X := by
    rw [primeSetCore]
    exact le_sSup ⟨hKXambient, hKnormal, hKpi⟩
  exact hYK.trans hKcore

end Submission.OddOrder.BG.Section08
