import Submission.OddOrder.BG.Section12.ComplementExistence
import Submission.OddOrder.BG.Section10.AlphaSigmaCore
import Submission.OddOrder.MathlibSupport.PiCore
import Submission.OddOrder.PF.Section02.DadeHypothesis

/-!
# Bender--Glauberman Section 12: sigma-complement decompositions

This file completes the introductory sigma-complement block of
`BGsection12.v`.  In addition to choosing the `tau2` Hall subgroup compatibly
with a fixed `tau1` Hall subgroup, it records the prime support and internal
semidirect-product structure of a sigma complement.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise

noncomputable section

universe u

/-- Restrict a Hall subgroup to an intermediate subgroup which contains it. -/
private theorem isHall_subgroupOf_of_le
    {G : Type u} [Group G] [Finite G]
    {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    {pi : Set ℕ} (hA : IsHall pi (A.subgroupOf C)) :
    IsHall pi (A.subgroupOf B) := by
  constructor
  · rw [natCard_subgroupOf_eq hAB]
    have hcard := hA.isPiNumber_card
    rwa [natCard_subgroupOf_eq (hAB.trans hBC)] at hcard
  · have hdvd : A.relIndex B ∣ A.relIndex C := by
      refine ⟨B.relIndex C, ?_⟩
      exact (A.relIndex_mul_relIndex B C hAB hBC).symm
    exact hA.isPiNumber_index.of_dvd hdvd

/-- Promote a Hall subgroup through a Hall intermediate subgroup. -/
private theorem isHall_of_isHall_subgroupOf
    {G : Type u} [Group G] [Finite G]
    {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    {pi rho : Set ℕ} (hpi : pi ⊆ rho)
    (hA : IsHall pi (A.subgroupOf B))
    (hB : IsHall rho (B.subgroupOf C)) :
    IsHall pi (A.subgroupOf C) := by
  constructor
  · rw [natCard_subgroupOf_eq (hAB.trans hBC)]
    have hcard := hA.isPiNumber_card
    rwa [natCard_subgroupOf_eq hAB] at hcard
  · have hBindex : IsPiNumber piᶜ (B.relIndex C) := by
      apply hB.isPiNumber_index.mono
      intro p hpNotRho
      change p ∉ pi
      intro hpPi
      exact hpNotRho (hpi hpPi)
    change IsPiNumber piᶜ (A.relIndex C)
    rw [← A.relIndex_mul_relIndex B C hAB hBC]
    exact hA.isPiNumber_index.mul hBindex

/-- Turn complementarity inside `K` into an equality of ambient carriers. -/
private theorem carrier_eq_mul_of_isComplement_subgroupOf
    {G : Type u} [Group G] {K H L : Subgroup G}
    (hHK : H ≤ K) (hLK : L ≤ K)
    (hcomp : (H.subgroupOf K).IsComplement' (L.subgroupOf K)) :
    (K : Set G) = (H : Set G) * (L : Set G) := by
  ext x
  constructor
  · intro hx
    obtain ⟨⟨h, l⟩, hmul⟩ := hcomp.2 (⟨x, hx⟩ : K)
    refine Set.mem_mul.mpr ⟨(h : K), ?_, (l : K), ?_, ?_⟩
    · exact h.property
    · exact l.property
    · simpa using congrArg Subtype.val hmul
  · rintro ⟨h, hh, l, hl, rfl⟩
    exact K.mul_mem (hHK hh) (hLK hl)

/-- `BGsection12.v: ex_tau2_compl`.

Given the two rank-one Hall factors of a sigma complement, one can choose the
`tau2` Hall factor so that its pointwise product with the `tau1` factor is the
carrier of a subgroup. -/
theorem ex_tau2_compl
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ E₃ : Subgroup G}
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hE₁E : E₁ ≤ E)
    (hHallE₁ : IsHall (tau1Primes M) (E₁.subgroupOf E))
    (hE₃E : E₃ ≤ E)
    (hHallE₃ : IsHall (tau3Primes M) (E₃.subgroupOf E)) :
    ∃ E₂ : Subgroup G, E₂ ≤ E ∧
      IsHall (tau2Primes M) (E₂.subgroupOf E) ∧
      sigma_complement M E E₁ E₂ E₃ := by
  let tau12 : Set ℕ := tau1Primes M ∪ tau2Primes M
  have hsolE : IsSolvable E := sigma_compl_sol hEM hHallE
  have hE₁tau12 : IsPiNumber tau12 (Nat.card E₁) := by
    have hcard := hHallE₁.isPiNumber_card
    rw [natCard_subgroupOf_eq hE₁E] at hcard
    exact hcard.mono Set.subset_union_left
  obtain ⟨E₂₁, hE₁E₂₁, hE₂₁E, hHallE₂₁⟩ :=
    exists_ambient_isHall_ge_of_isSolvable
      hE₁E hsolE tau12 hE₁tau12
  have hsolE₂₁ : IsSolvable E₂₁ := by
    letI : IsSolvable E := hsolE
    exact isSolvable_of_injective (Subgroup.inclusion hE₂₁E)
      (Subgroup.inclusion_injective hE₂₁E)
  obtain ⟨E₂, hE₂E₂₁, hHallE₂E₂₁⟩ :=
    exists_ambient_isHall_of_isSolvable hsolE₂₁ (tau2Primes M)
  have hHallE₁E₂₁ :
      IsHall (tau1Primes M) (E₁.subgroupOf E₂₁) :=
    isHall_subgroupOf_of_le hE₁E₂₁ hE₂₁E hHallE₁
  have hE₂E : E₂ ≤ E := hE₂E₂₁.trans hE₂₁E
  have hHallE₂E :
      IsHall (tau2Primes M) (E₂.subgroupOf E) :=
    isHall_of_isHall_subgroupOf hE₂E₂₁ hE₂₁E
      Set.subset_union_right hHallE₂E₂₁ hHallE₂₁
  let A : Subgroup E₂₁ := E₂.subgroupOf E₂₁
  let B : Subgroup E₂₁ := E₁.subgroupOf E₂₁
  have hAHall : IsHall (tau2Primes M) A := by
    simpa [A] using hHallE₂E₂₁
  have hBHall : IsHall (tau1Primes M) B := by
    simpa [B] using hHallE₁E₂₁
  have hE₂₁tau12 : IsPiNumber tau12 (Nat.card E₂₁) := by
    rw [← natCard_subgroupOf_eq hE₂₁E]
    exact hHallE₂₁.isPiNumber_card
  have hBindexTau2 : IsPiNumber (tau2Primes M) B.index := by
    intro p hp hpIndex
    have hpTau12 : p ∈ tau12 :=
      hE₂₁tau12 hp (hpIndex.trans B.index_dvd_card)
    change p ∈ tau1Primes M ∪ tau2Primes M at hpTau12
    rcases hpTau12 with hpTau1 | hpTau2
    · exact (hBHall.isPiNumber_index hp hpIndex hpTau1).elim
    · exact hpTau2
  have hBcardTau2Compl : IsPiNumber (tau2Primes M)ᶜ (Nat.card B) :=
    hBHall.isPiNumber_card.mono (tau2'1 M)
  have hcopAB : Nat.Coprime (Nat.card A) (Nat.card B) :=
    hAHall.isPiNumber_card.coprime_compl hBcardTau2Compl
  have hcopIndex : Nat.Coprime B.index A.index :=
    hBindexTau2.coprime_compl hAHall.isPiNumber_index
  have hAcard_dvd_Bindex : Nat.card A ∣ B.index := by
    apply hcopAB.dvd_of_dvd_mul_left
    rw [B.card_mul_index]
    exact A.card_subgroup_dvd_card
  have hBindex_dvd_Acard : B.index ∣ Nat.card A := by
    apply hcopIndex.dvd_of_dvd_mul_right
    rw [A.card_mul_index]
    exact B.index_dvd_card
  have hAcard : Nat.card A = B.index :=
    Nat.dvd_antisymm hAcard_dvd_Bindex hBindex_dvd_Acard
  have hcard : Nat.card A * Nat.card B = Nat.card E₂₁ := by
    rw [hAcard, B.index_mul_card]
  have hdis : Disjoint A B :=
    Subgroup.disjoint_of_coprime_natCard hcopAB
  have hcomp : A.IsComplement' B :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdis
  have hproduct :
      ∃ K : Subgroup G, (K : Set G) =
        (E₂ : Set G) * (E₁ : Set G) := by
    refine ⟨E₂₁, ?_⟩
    exact carrier_eq_mul_of_isComplement_subgroupOf
      hE₂E₂₁ hE₁E₂₁ (by simpa [A, B] using hcomp)
  refine ⟨E₂, hE₂E, hHallE₂E, ?_⟩
  exact
    { E_le_M := hEM
      hall_E := hHallE
      E₁_le_E := hE₁E
      hall_E₁ := hHallE₁
      E₂_le_E := hE₂E
      hall_E₂ := hHallE₂E
      E₃_le_E := hE₃E
      hall_E₃ := hHallE₃
      product_is_group := hproduct }

/-- `BGsection12.v: coprime_sigma_compl`.

The sigma core and every sigma complement have coprime orders.  Unlike the
source statement, this arithmetic fact does not require maximality of `M`. -/
theorem coprime_sigma_compl
    {G : Type u} [Group G] [Finite G]
    {M E : Subgroup G} (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    Nat.Coprime (Nat.card (sigmaCore M)) (Nat.card E) := by
  apply (sigmaCore_isPiNumber M).coprime_compl
  rw [← natCard_subgroupOf_eq hEM]
  exact hHall.isPiNumber_card

/-- `BGsection12.v: pi_sigma_compl`.

The primes occurring in a sigma complement are precisely the primes of `M`
outside `sigma(M)`.  This is the set-valued counterpart of MathComp's
`π(E) =i [predD π(M) & sigma(M)]`. -/
theorem pi_sigma_compl
    {G : Type u} [Group G] [Finite G]
    {M E : Subgroup G} (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    primeSupport (Nat.card E) =
      primeSupport (Nat.card M) \ sigmaPrimes M := by
  ext p
  constructor
  · rintro ⟨hp, hpE⟩
    have hpM : p ∣ Nat.card M :=
      hpE.trans (Subgroup.card_dvd_of_le hEM)
    have hpEsub : p ∣ Nat.card (E.subgroupOf M) := by
      rwa [natCard_subgroupOf_eq hEM]
    have hpNotSigma : p ∉ sigmaPrimes M := by
      exact hHall.isPiNumber_card hp hpEsub
    exact ⟨⟨hp, hpM⟩, hpNotSigma⟩
  · rintro ⟨⟨hp, hpM⟩, hpNotSigma⟩
    refine ⟨hp, ?_⟩
    have hpProduct :
        p ∣ Nat.card (E.subgroupOf M) * (E.subgroupOf M).index := by
      rw [(E.subgroupOf M).card_mul_index]
      exact hpM
    rcases hp.dvd_mul.mp hpProduct with hpE | hpIndex
    · rwa [natCard_subgroupOf_eq hEM] at hpE
    · have hpSigma : p ∈ sigmaPrimes M := by
        simpa only [compl_compl] using
          hHall.isPiNumber_index hp hpIndex
      exact (hpNotSigma hpSigma).elim

/-- `BGsection12.v: sdprod_sigma`.

For a maximal subgroup `M`, its sigma core is normal in `M` and every sigma
complement is an internal complement to that core. -/
theorem sdprod_sigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    IsInternalSemidirectProductIn (sigmaCore M) E M := by
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  let T : Subgroup M := E.subgroupOf M
  have hSHall : IsHall (sigmaPrimes M) S := by
    simpa [S] using Msigma_Hall hM
  have hTHall : IsHall (sigmaPrimes M)ᶜ T := by
    simpa [T] using hHall
  have hcopST : Nat.Coprime (Nat.card S) (Nat.card T) := by
    change Nat.Coprime
      (Nat.card ((sigmaCore M).subgroupOf M))
      (Nat.card (E.subgroupOf M))
    rw [natCard_subgroupOf_eq (sigmaCore_le M),
      natCard_subgroupOf_eq hEM]
    exact coprime_sigma_compl hEM hHall
  have hTindexSigma : IsPiNumber (sigmaPrimes M) T.index := by
    simpa only [compl_compl] using hTHall.isPiNumber_index
  have hcopIndex : Nat.Coprime S.index T.index :=
    (hTindexSigma.coprime_compl hSHall.isPiNumber_index).symm
  have hTcard_dvd_Sindex : Nat.card T ∣ S.index := by
    apply hcopST.symm.dvd_of_dvd_mul_left
    rw [S.card_mul_index]
    exact T.card_subgroup_dvd_card
  have hSindex_dvd_Tcard : S.index ∣ Nat.card T := by
    apply hcopIndex.dvd_of_dvd_mul_right
    rw [T.card_mul_index]
    exact S.index_dvd_card
  have hTcard : Nat.card T = S.index :=
    Nat.dvd_antisymm hTcard_dvd_Sindex hSindex_dvd_Tcard
  have hcard : Nat.card S * Nat.card T = Nat.card M := by
    rw [hTcard, S.card_mul_index]
  have hdis : Disjoint S T :=
    Subgroup.disjoint_of_coprime_natCard hcopST
  refine ⟨sigmaCore_le M, hEM, sigmaCore_normal M, ?_⟩
  exact Subgroup.isComplement'_of_card_mul_and_disjoint hcard hdis

end

end Submission.OddOrder.BG.Section12
