import Submission.OddOrder.BG.Section07.CentralCoreAction
import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
# Bender--Glauberman, Section 7: singleton-complement prime-set cores

The prime-set core away from a single prime agrees with the usual
`p`-prime core, mapped from the ambient subgroup back into the full group.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G] {p : ℕ}

theorem primeSetCore_compl_singleton_eq_map_pPrimeCore
    [Fact p.Prime] (X : Subgroup G) :
    primeSetCore ({p} : Set ℕ)ᶜ X =
      (pPrimeCore p X).map X.subtype := by
  apply le_antisymm
  · rw [primeSetCore]
    refine sSup_le fun K hK => ?_
    have hKcop : Nat.Coprime p (Nat.card K) := by
      apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
      intro hpK
      have hpcompl : p ∈ ({p} : Set ℕ)ᶜ :=
        hK.2.2 (Fact.out : p.Prime) hpK
      exact hpcompl (by simp)
    have hsubcard : Nat.card (K.subgroupOf X) = Nat.card K :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK.1).toEquiv
    have hKsubprime : IsPPrimeSubgroup p (K.subgroupOf X) := by
      rw [IsPPrimeSubgroup, hsubcard]
      exact hKcop
    have hKsubcore : K.subgroupOf X ≤ pPrimeCore p X :=
      le_pPrimeCore hKsubprime hK.2.1
    rw [← Subgroup.map_subgroupOf_eq_of_le hK.1]
    exact Subgroup.map_mono hKsubcore
  · rw [primeSetCore]
    refine le_sSup ⟨Subgroup.map_subtype_le _, ?_, ?_⟩
    · change (((pPrimeCore p X).map X.subtype).comap X.subtype).Normal
      rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
      infer_instance
    · have hmapcard :
          Nat.card ((pPrimeCore p X).map X.subtype) =
            Nat.card (pPrimeCore p X) :=
        Subgroup.card_map_of_injective X.subtype_injective
      intro q _ hqmap hqsingleton
      have hqp : q = p := Set.mem_singleton_iff.mp hqsingleton
      subst q
      rw [hmapcard] at hqmap
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (G := X) (p := p))) hqmap

theorem centralPrimeComplementCore_eq_map_pPrimeCore
    [Fact p.Prime] (A : Subgroup G)
    (hsupport : primeSupport (Nat.card A) = {p}) :
    centralPrimeComplementCore A =
      (pPrimeCore p (Subgroup.centralizer (A : Set G))).map
        (Subgroup.centralizer (A : Set G)).subtype := by
  rw [centralPrimeComplementCore, hsupport]
  exact primeSetCore_compl_singleton_eq_map_pPrimeCore _

end Submission.OddOrder.BG.Section07
