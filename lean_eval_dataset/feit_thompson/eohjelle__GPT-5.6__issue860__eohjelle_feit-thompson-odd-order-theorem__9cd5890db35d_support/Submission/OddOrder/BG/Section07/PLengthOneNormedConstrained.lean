import Submission.OddOrder.BG.Section06.PLengthOneMaximalElementary
import Submission.OddOrder.BG.Section07.NormedSubgroups
import Submission.OddOrder.MathlibSupport.PGroupPrimeSupport
import Submission.OddOrder.MathlibSupport.PMaxElemSubtype

/-!
# Bender--Glauberman Proposition 7.5(a)

A nontrivial maximal elementary-abelian `p`-subgroup is normed constrained
when every proper subgroup has `p`-length one.
-/

namespace Submission.OddOrder.BG.Section07

open Submission.OddOrder.MathlibSupport

universe u

/-- `BGsection7.plength_1_normed_constrained`, Proposition 7.5(a). -/
theorem plength_1_normed_constrained
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    (p : ℕ) [Fact p.Prime]
    (A : Subgroup G) (hAne : A ≠ ⊥)
    (hAmax : IsPMaxElem p (⊤ : Subgroup G) A)
    (hpl : ∀ M : Subgroup G, M < ⊤ → IsPLengthOne p M) :
    NormedConstrained A := by
  classical
  have hAproper : A < ⊤ :=
    lt_of_le_of_lt
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        hAmax.elementary.commutative)
      (mFT_cent_proper A hAne)
  letI : Nontrivial A := A.nontrivial_iff_ne_bot.mpr hAne
  have hAp : IsPGroup p A := hAmax.elementary.isPGroup
  have hpodd : Odd p :=
    (mFT_odd A).of_dvd_nat
      (hAp.card_eq_or_dvd.resolve_left (Finite.one_lt_card.ne'))
  have hsupport : primeSupport (Nat.card A) = {p} :=
    hAp.primeSupport_natCard_eq_singleton
  refine
    { nontrivial := hAne
      proper := hAproper
      constrained := ?_ }
  intro X Y hAX hXproper hY
  rcases hY with ⟨hYX, hYpi, hAnormY⟩
  letI : IsSolvable X := mFT_sol hXproper

  have hAmaxInX : IsPMaxElem p X A :=
    hAmax.of_le le_top hAX
  have hAmaxX :
      IsPMaxElem p (⊤ : Subgroup X) (A.subgroupOf X) :=
    hAmaxInX.subgroupOf_top
  have hnormYX :
      A.subgroupOf X ≤
        Subgroup.normalizer (Y.subgroupOf X : Set X) := by
    have hsub : A.subgroupOf X ≤
        (Subgroup.normalizer (Y : Set G)).subgroupOf X :=
      Subgroup.subgroupOf_mono X hAnormY
    rwa [Subgroup.subgroupOf_normalizer_eq hYX] at hsub
  have hYcop : Nat.Coprime p (Nat.card Y) := by
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hpY
    have hpNotSupport : p ∈ (primeSupport (Nat.card A))ᶜ :=
      hYpi (Fact.out : p.Prime) hpY
    rw [hsupport] at hpNotSupport
    exact hpNotSupport (by simp)
  have hYXcard : Nat.card (Y.subgroupOf X) = Nat.card Y :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYX).toEquiv
  have hYXp : IsPPrimeSubgroup p (Y.subgroupOf X) := by
    rw [IsPPrimeSubgroup, hYXcard]
    exact hYcop
  have hYXcore :
      Y.subgroupOf X ≤ pPrimeCore p X :=
    Submission.OddOrder.BG.Section06.plength1_norm_pmaxElem
      hAmaxX hpodd (hpl X hXproper) hnormYX hYXp

  let K : Subgroup G := (pPrimeCore p X).map X.subtype
  have hYK : Y ≤ K := by
    dsimp [K]
    rw [← Subgroup.map_subgroupOf_eq_of_le hYX]
    exact Subgroup.map_mono hYXcore
  have hKX : K ≤ X := by
    dsimp [K]
    exact Subgroup.map_subtype_le _
  have hKnormal : (K.subgroupOf X).Normal := by
    change (((pPrimeCore p X).map X.subtype).comap X.subtype).Normal
    rw [Subgroup.comap_map_eq_self_of_injective X.subtype_injective]
    infer_instance
  have hKcard : Nat.card K = Nat.card (pPrimeCore p X) := by
    dsimp [K]
    exact Subgroup.card_map_of_injective X.subtype_injective
  have hKcop : Nat.Coprime p (Nat.card K) := by
    rw [hKcard]
    exact pPrimeCore_coprime_card
  have hKpi :
      IsPiNumber (primeSupport (Nat.card A))ᶜ (Nat.card K) := by
    intro q hq hqK
    rw [hsupport]
    intro hqp
    have hqpEq : q = p := Set.mem_singleton_iff.mp hqp
    subst q
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp hKcop) hqK
  have hKcore :
      K ≤ primeSetCore (primeSupport (Nat.card A))ᶜ X := by
    rw [primeSetCore]
    exact le_sSup ⟨hKX, hKnormal, hKpi⟩
  exact hYK.trans hKcore

end Submission.OddOrder.BG.Section07
