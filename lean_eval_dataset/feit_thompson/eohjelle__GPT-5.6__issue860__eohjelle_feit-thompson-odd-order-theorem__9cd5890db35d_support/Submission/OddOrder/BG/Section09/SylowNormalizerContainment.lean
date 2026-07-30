import Submission.OddOrder.BG.Section08.SCNFittingPuigCenter
import Submission.OddOrder.BG.Section09.NormalizedPrimeComplementCore

/-!
# Bender--Glauberman Section 9: Sylow normalizer containment

This is the normalizer-containment step at the start of Theorem 9.1(b).
When the local `p'`-core is nontrivial, its ambient image is the nontrivial
normal subgroup whose normalizer pins down the maximal subgroup.  In the
core-free case, the center of the Puig subgroup supplies that normal
subgroup instead.
-/

namespace Submission.OddOrder.BG.Section09

open Submission.OddOrder
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section08
open Submission.OddOrder.MathlibSupport

universe u

/-- The ambient normalizer of a mapped Sylow subgroup stays in a maximal
subgroup whenever every ambient `p'`-subgroup normalized by the fixed
nontrivial subgroup is forced back into that maximal subgroup. -/
theorem normalizer_map_sylow_le_maximal_of_closed_pPrime
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {p : ℕ} [Fact p.Prime]
    {M B : Subgroup G}
    (P : Sylow p M)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hBP : B ≤ (P : Subgroup M).map M.subtype)
    (hBne : B ≠ ⊥)
    (hclosed : ∀ K : Subgroup G,
      IsPPrimeSubgroup p K →
      B ≤ Subgroup.normalizer (K : Set G) →
      K ≤ M) :
    Subgroup.normalizer
      ((P : Subgroup M).map M.subtype : Set G) ≤ M := by
  let PM : Subgroup G := (P : Subgroup M).map M.subtype
  have hsolM : IsSolvable M := mmax_sol hM
  by_cases hcore : pPrimeCore p M = ⊥
  · let Z : Subgroup G := centerWithin (puig PM)
    have hZlePM : Z ≤ PM := by
      simpa only [Z, PM] using
        centerWithin_puig_map_sylow_le_map_sylow P
    have hZleM : Z ≤ M :=
      hZlePM.trans (Subgroup.map_subtype_le (P : Subgroup M))
    have hZnormal : (Z.subgroupOf M).Normal := by
      simpa only [Z, PM] using
        centerWithin_puig_map_sylow_normal_subgroupOf
          M P (mFT_odd M) hsolM hcore
    have hZne : Z ≠ ⊥ := by
      simpa only [Z, PM] using
        centerWithin_puig_map_sylow_ne_bot_of_le P hBP hBne
    have hnormalizerZ : Subgroup.normalizer (Z : Set G) = M :=
      mmax_normal hM hZleM hZnormal hZne
    have hnormalizers :
        Subgroup.normalizer (PM : Set G) ≤
          Subgroup.normalizer (Z : Set G) := by
      simpa only [PM, Z] using
        normalizer_map_sylow_le_normalizer_centerWithin_puig P
    change Subgroup.normalizer (PM : Set G) ≤ M
    rwa [hnormalizerZ] at hnormalizers
  · let O : Subgroup G := (pPrimeCore p M).map M.subtype
    have hOleM : O ≤ M :=
      Subgroup.map_subtype_le (pPrimeCore p M)
    have hOsubgroupOf : O.subgroupOf M = pPrimeCore p M := by
      change ((pPrimeCore p M).map M.subtype).comap M.subtype =
        pPrimeCore p M
      exact Subgroup.comap_map_eq_self_of_injective
        M.subtype_injective (pPrimeCore p M)
    have hOnormal : (O.subgroupOf M).Normal := by
      rw [hOsubgroupOf]
      infer_instance
    have hOne : O ≠ ⊥ := by
      intro hObot
      apply hcore
      exact (Subgroup.map_eq_bot_iff_of_injective
        (pPrimeCore p M) M.subtype_injective).mp hObot
    have hnormalizerO : Subgroup.normalizer (O : Set G) = M :=
      mmax_normal hM hOleM hOnormal hOne
    have hclosedPM : ∀ K : Subgroup G,
        IsPPrimeSubgroup p K →
        PM ≤ Subgroup.normalizer (K : Set G) →
        K ≤ M := by
      intro K hKprime hPMK
      exact hclosed K hKprime (hBP.trans hPMK)
    have hnormalizers :
        Subgroup.normalizer (PM : Set G) ≤
          Subgroup.normalizer (O : Set G) := by
      simpa only [PM, O] using
        normalizer_map_sylow_le_normalizer_map_pPrimeCore
          M P hsolM hclosedPM
    change Subgroup.normalizer (PM : Set G) ≤ M
    rwa [hnormalizerO] at hnormalizers

end Submission.OddOrder.BG.Section09
