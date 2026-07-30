import Submission.OddOrder.BG.Section15.NonTIFittingAndSignalizer
import Submission.OddOrder.BG.Section06.PProdCoprime

namespace Submission.OddOrder.BG.Section15

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section11
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

private theorem nilpotent_normal_le_fittingWithin_15_8
    {A B : Subgroup G} (hAB : A ≤ B)
    (hAnormal : (A.subgroupOf B).Normal)
    (hAnil : Group.IsNilpotent A) :
    A ≤ fittingWithin B := by
  let AB : Subgroup B := A.subgroupOf B
  let eAB : AB ≃* A := Subgroup.subgroupOfEquivOfLe hAB
  letI : AB.Normal := by simpa only [AB] using hAnormal
  letI : Group.IsNilpotent AB :=
    Group.nilpotent_of_mulEquiv eAB.symm
  have hcore : AB ≤ fittingCore B :=
    nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
  rw [← Subgroup.map_subgroupOf_eq_of_le hAB]
  exact Subgroup.map_mono hcore

private theorem intermediate_eq_isHall_of_isPiNumber_15_8
    {pi : Set ℕ} {K E M : Subgroup G}
    (hKE : K ≤ E) (hEM : E ≤ M)
    (hK : IsHall pi (K.subgroupOf M))
    (hEpi : IsPiNumber pi (Nat.card E)) : E = K := by
  have hrelPi : IsPiNumber pi (K.relIndex E) :=
    hEpi.of_dvd (Subgroup.relIndex_dvd_card K E)
  have hrelCompl : IsPiNumber piᶜ (K.relIndex E) :=
    hK.isPiNumber_index.of_dvd (by
      have hsub : K.subgroupOf M ≤ E.subgroupOf M :=
        fun _ hx ↦ hKE hx
      simpa only [Subgroup.relIndex_subgroupOf hEM] using
        (Subgroup.relIndex_dvd_index_of_le hsub))
  have hone : K.relIndex E = 1 :=
    by simpa [Nat.Coprime] using hrelPi.coprime_compl hrelCompl
  exact le_antisymm (Subgroup.relIndex_eq_one.mp hone) hKE

/-- Every `tau2(H)` prime in the P2 signalizer configuration is the order
of `K`. -/
private theorem tau2Prime_eq_cardK_of_P2Signalizer
    {M Mstar U K R H : Subgroup G} {r p : ℕ} [Fact r.Prime]
    (hMP2 : M ∈ typeP2MaximalSubgroups (G := G))
    (hCompl : KappaComplement M U K)
    (hMstar : Mstar ∈ minSimple_max_groups_of (G := G)
      (Subgroup.centralizer (K : Set G) : Set G))
    (hR : IsSylowSubgroupOf r R U)
    (hH : H ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (R : Set G) : Set G))
    (hpTau : p ∈ tau2Primes H) :
    p = Nat.card K := by
  classical
  have subgroup_le_normal_isHall_local
      {K₀ : Type u} [Group K₀] [Finite K₀] {pi₀ : Set ℕ}
      {N₀ L₀ : Subgroup K₀} (hNnormal : N₀.Normal)
      (hNHall : IsHall pi₀ N₀)
      (hLpi : IsPiNumber pi₀ (Nat.card L₀)) : L₀ ≤ N₀ := by
    letI : N₀.Normal := hNnormal
    have hcop : (Nat.card L₀).Coprime N₀.index := by
      apply Nat.coprime_of_dvd
      intro ℓ hℓ hℓL hℓIndex
      exact hNHall.isPiNumber_index hℓ hℓIndex (hLpi hℓ hℓL)
    intro x hxL
    let quot : K₀ →* (K₀ ⧸ N₀) := QuotientGroup.mk' N₀
    have horderL : orderOf (quot x) ∣ Nat.card L₀ :=
      (orderOf_map_dvd quot x).trans (L₀.orderOf_dvd_natCard hxL)
    have horderIndex : orderOf (quot x) ∣ N₀.index := by
      simpa only [N₀.index_eq_card] using orderOf_dvd_natCard (quot x)
    have horderOne : orderOf (quot x) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
    exact (QuotientGroup.eq_one_iff x).mp
      (by simpa [quot] using orderOf_eq_one_iff.mp horderOne)
  have pSubgroups_centralize_of_nilpotent_local
      {H₀ A₀ B₀ : Subgroup G} {p₁ q₁ : ℕ}
      [Fact p₁.Prime] [Fact q₁.Prime]
      (hpq₁ : p₁ ≠ q₁) (hAp : IsPGroup p₁ A₀)
      (hBq : IsPGroup q₁ B₀) (hAH : A₀ ≤ H₀) (hBH : B₀ ≤ H₀)
      (hnil : Group.IsNilpotent H₀) :
      A₀ ≤ Subgroup.centralizer (B₀ : Set G) := by
    let AH : Subgroup H₀ := A₀.subgroupOf H₀
    let BH : Subgroup H₀ := B₀.subgroupOf H₀
    have hAHp : IsPGroup p₁ AH :=
      hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
    have hBHq : IsPGroup q₁ BH :=
      hBq.of_equiv (Subgroup.subgroupOfEquivOfLe hBH).symm
    obtain ⟨S, hAHS⟩ := hAHp.exists_le_sylow
    obtain ⟨T, hBHT⟩ := hBHq.exists_le_sylow
    letI : Group.IsNilpotent H₀ := hnil
    have hSnormal : (S : Subgroup H₀).Normal := by infer_instance
    have hTnormal : (T : Subgroup H₀).Normal := by infer_instance
    letI : (S : Subgroup H₀).Normal := hSnormal
    letI : (T : Subgroup H₀).Normal := hTnormal
    have hcop : Nat.Coprime (Nat.card (S : Subgroup H₀))
        (Nat.card (T : Subgroup H₀)) :=
      IsPGroup.coprime_card_of_ne p₁ q₁ hpq₁
        (S : Subgroup H₀) (T : Subgroup H₀) S.isPGroup' T.isPGroup'
    have hdis : Disjoint (S : Subgroup H₀) (T : Subgroup H₀) :=
      Subgroup.disjoint_of_coprime_natCard hcop
    have hcommBot :
        ⁅(S : Subgroup H₀), (T : Subgroup H₀)⁆ = (⊥ : Subgroup H₀) := by
      apply le_antisymm
      · exact (Subgroup.commutator_le_inf
          (H₁ := (S : Subgroup H₀)) (H₂ := (T : Subgroup H₀))).trans
            hdis.le_bot
      · exact bot_le
    have hcentST : (S : Subgroup H₀) ≤
        Subgroup.centralizer ((T : Subgroup H₀) : Set H₀) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    let aH : H₀ := ⟨a, hAH ha⟩
    let bH : H₀ := ⟨b, hBH hb⟩
    have haS : aH ∈ (S : Subgroup H₀) :=
      hAHS (show aH ∈ AH from ha)
    have hbT : bH ∈ (T : Subgroup H₀) :=
      hBHT (show bH ∈ BH from hb)
    exact congrArg Subtype.val
      (Subgroup.mem_centralizer_iff.mp (hcentST haS) bH hbT)
  have hMP : M ∈ typePMaximalSubgroups (G := G) := hMP2.1
  have hmaxH : H ∈ minSimple_max_groups (G := G) := hH.1
  have hmaxMstar : Mstar ∈ minSimple_max_groups (G := G) := hMstar.1
  let q := Nat.card K
  have hqPrime : q.Prime := by
    simpa only [q] using
      ((Ptype_structure hMP hCompl.K_le_M hCompl.hall_K).typeP2 hMP2).card_K_prime
  letI : Fact q.Prime := ⟨hqPrime⟩
  rcases P2type_signalizer hMP2 hCompl hMstar hR hH with
    ⟨hHF, hUH, hjoin, hnorm, hKfitD, hHallD⟩
  let D : Subgroup G := H ⊓ Mstar
  have hDH : D ≤ H := inf_le_left
  have hDMstar : D ≤ Mstar := inf_le_right
  have hpPrime : p.Prime := hpTau.1
  letI : Fact p.Prime := ⟨hpPrime⟩
  obtain ⟨A, hAD, hAH, hA⟩ :=
    ex_tau2Elem (M := H) hDH hHallD hpTau
  have hActx := tau2_compl_context hmaxH hDH hHallD hpTau hAD hA
  have hAfitD : A ≤ fittingWithin D :=
    nilpotent_normal_le_fittingWithin_15_8 hAD hActx.A_normal
      hA.isPGroup.isNilpotent
  have hFitDpi :
      IsPiNumber (sigmaPrimes H)ᶜ (Nat.card (fittingWithin D)) := by
    have hDpi : IsPiNumber (sigmaPrimes H)ᶜ (Nat.card D) := by
      simpa only [D, MathlibSupport.natCard_subgroupOf_eq hDH] using
        hHallD.isPiNumber_card
    exact hDpi.of_dvd (Subgroup.card_dvd_of_le (fittingWithin_le D))
  have hFitDcomm : IsMulCommutative (fittingWithin D) :=
    sigma'_nil_abelian hmaxH
      ((fittingWithin_le D).trans hDH) hFitDpi
      (fittingWithin_isNilpotent D)
  have hAcentK : A ≤ Subgroup.centralizer (K : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (congrArg Subtype.val
      (isMulCommutative_iff.mp hFitDcomm
        ⟨a, hAfitD ha⟩ ⟨k, hKfitD hk⟩)).symm
  have hAMstar : A ≤ Mstar := hAcentK.trans hMstar.2

  obtain ⟨Mpartner, hEmbed⟩ :=
    Ptype_embedding hMP hCompl.K_le_M hCompl.hall_K
  have hKline : RankOneLineIn q K K :=
    ⟨le_rfl, isElementaryAbelianOfRank_one_of_card_eq_prime rfl⟩
  have hPartnerUnique := hEmbed.rankOne_unique hqPrime hKline
  have hMstarEq : Mstar = Mpartner :=
    eq_uniq_mmax hPartnerUnique hmaxMstar hMstar.2
  subst Mpartner
  let Ks : Subgroup G := pTypePartner M K
  have hStarStruct := Ptype_structure hEmbed.Mstar_typeP
    hEmbed.Kstar_le_Mstar hEmbed.Kstar_hall_kappa
  have hKsigma : K ≤ sigmaCore Mstar := by
    rw [← hEmbed.doubleCentralizer]
    exact centralizerWithin_le_left _ _
  have hqSigma : q ∈ sigmaPrimes Mstar :=
    (sigmaCore_isPiNumber Mstar).of_dvd
      (Subgroup.card_dvd_of_le hKsigma) hqPrime (by simp [q])
  have hpSigma : p ∈ sigmaPrimes Mstar := by
    by_contra hpNotSigma
    have hApi :
        IsPiNumber (sigmaPrimes Mstar)ᶜ (Nat.card A) :=
      hA.isPGroup.isPiNumber_natCard (by simpa using hpNotSigma)
    obtain ⟨E, hAE, hEMstar, hHallE⟩ :=
      MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
        hAMstar (mmax_sol hmaxMstar) (sigmaPrimes Mstar)ᶜ hApi
    have hpTauStar :=
      sigmaPrime2Elem_tau2 hmaxMstar hEMstar hHallE hAE hA
    have hECtx :=
      tau2_compl_context hmaxMstar hEMstar hHallE hpTauStar hAE hA
    have hKcentA : K ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.le_centralizer_iff.mp hAcentK
    have hKE : K ≤ E := hKcentA.trans hECtx.centralizer_le_E
    have hqE : q ∣ Nat.card E :=
      (by simp [q] : q ∣ Nat.card K).trans
        (Subgroup.card_dvd_of_le hKE)
    have hqEMstar : q ∣ Nat.card (E.subgroupOf Mstar) := by
      simpa only [MathlibSupport.natCard_subgroupOf_eq hEMstar] using hqE
    exact (hHallE.isPiNumber_card hqPrime hqEMstar) hqSigma
  have hAsigma : A ≤ sigmaCore Mstar := by
    let AM : Subgroup Mstar := A.subgroupOf Mstar
    have hAMpi : IsPiNumber (sigmaPrimes Mstar) (Nat.card AM) := by
      rw [MathlibSupport.natCard_subgroupOf_eq hAMstar]
      exact hA.isPGroup.isPiNumber_natCard hpSigma
    have hle : AM ≤ (sigmaCore Mstar).subgroupOf Mstar :=
      subgroup_le_normal_isHall_local
        (by simpa using sigmaCore_normal Mstar)
        (Msigma_Hall hmaxMstar) hAMpi
    intro a ha
    exact hle (show (⟨a, hAMstar ha⟩ : Mstar) ∈ AM from ha)

  letI : IsSolvable Mstar := mmax_sol hmaxMstar
  have hSigmaSol : IsSolvable (sigmaCore Mstar) :=
    isSolvable_of_injective
      (Subgroup.inclusion (sigmaCore_le Mstar))
      (Subgroup.inclusion_injective (sigmaCore_le Mstar))
  obtain ⟨D₀, hD₀sigma, hHallD₀q⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      hSigmaSol ({q} : Set ℕ)ᶜ
  have hHallD₀ :
      IsHall ({Nat.card (kappaCentralizer Mstar Ks)} : Set ℕ)ᶜ
        (D₀.subgroupOf (sigmaCore Mstar)) := by
    simpa only [Ks, kappaCentralizer, hEmbed.doubleCentralizer, q] using
      hHallD₀q
  let Q : Subgroup G := pCoreWithin q Mstar
  have hQfit : Q ≤ fittingWithin Mstar := by
    change (pCore q Mstar).map Mstar.subtype ≤ fittingWithin Mstar
    exact (Subgroup.map_mono (pCore_le_fittingCore q)).trans
      (by rfl)
  have hAfit_and_Qsyl :
      A ≤ fittingWithin Mstar ∧ IsSylowSubgroupOf q Q Mstar := by
    by_cases hEq : Fitting_core Mstar = sigmaCore Mstar
    · have hAFcore : A ≤ Fitting_core Mstar := by
        simpa only [hEq] using hAsigma
      have hqFcore : q ∈ primeSupport (Nat.card (Fitting_core Mstar)) := by
        refine ⟨hqPrime, ?_⟩
        rw [hEq]
        exact (by simp [q] : q ∣ Nat.card K).trans
          (Subgroup.card_dvd_of_le hKsigma)
      exact ⟨hAFcore.trans (Fcore_sub_Fitting Mstar), by
        simpa only [Q, pCoreWithin] using
          Fcore_pcore_Sylow Mstar hqFcore⟩
    · have hn := (Fcore_structure hmaxMstar).nonnilpotent
        hEmbed.Kstar_le_Mstar hEmbed.Kstar_hall_kappa hEq
        hD₀sigma hHallD₀
      have hfac :
          factorCentralizerWithin (sigmaCore Mstar) K
              (centralizerWithin Q D₀) =
            (fittingWithin Mstar : Set G) := by
        simpa only [Ks, kappaCentralizer, hEmbed.doubleCentralizer,
          q, Q] using
            hn.fitting_descriptions.partner_factor_centralizer
      have hAfit : A ≤ fittingWithin Mstar := by
        intro a ha
        change a ∈ (fittingWithin Mstar : Set G)
        rw [← hfac]
        refine ⟨hAsigma ha, ?_⟩
        intro k hk
        have hka : k * a = a * k :=
          Subgroup.mem_centralizer_iff.mp (hAcentK ha) k hk
        rw [commutatorElement_eq_one_iff_mul_comm.mpr hka]
        exact Subgroup.one_mem _
      exact ⟨hAfit, by
        simpa only [Ks, kappaCentralizer, hEmbed.doubleCentralizer,
          q, Q] using hn.pcore_sylow⟩
  have hAfit := hAfit_and_Qsyl.1
  have hQsyl := hAfit_and_Qsyl.2
  have hpq : p = q := by
    by_contra hpq
    have hAcentQ : A ≤ Subgroup.centralizer (Q : Set G) :=
      pSubgroups_centralize_of_nilpotent_local hpq
        hA.isPGroup hQsyl.isPGroup hAfit hQfit
        (fittingWithin_isNilpotent Mstar)
    obtain ⟨Sq, hQSq⟩ := hQsyl
    have hqPartner :
        q ∈ primeSupport (Nat.card (pTypeCentralizer Mstar Ks)) := by
      simpa only [Ks, pTypeCentralizer, hEmbed.doubleCentralizer] using
        (show q ∈ primeSupport (Nat.card K) from
          ⟨hqPrime, by simp [q]⟩)
    have hQfamily :
        minSimple_max_groups_of (G := G) (Q : Set G) = {Mstar} := by
      rw [hQSq]
      exact (hStarStruct.Kstar_sylow_unique hqPartner Sq).1
    have hQuniq : Q ∈ minSimple_uniq_max_groups (G := G) :=
      (uniq_mmaxP Q).mpr ⟨Mstar, hQfamily⟩
    have hAuniq : A ∈ minSimple_uniq_max_groups (G := G) :=
      cent_uniq_Uniqueness hQuniq hAcentQ
        ⟨p, hpPrime, A, le_rfl, hA⟩
    have hAfamily :
        minSimple_max_groups_of (G := G) (A : Set G) = {H} :=
      def_uniq_mmax hAuniq hmaxH hAH
    have hMstarH : Mstar = H :=
      eq_uniq_mmax hAfamily hmaxMstar hAMstar
    have hpSigmaH : p ∈ sigmaPrimes H := by
      simpa only [hMstarH] using hpSigma
    exact hpTau.2.1 hpSigmaH
  simpa only [q] using hpq

/-- The `tau2` primes of the P2 signalizer maximal subgroup are exactly the
prime order of the P2 kernel, while the original maximal subgroup has
complementary `tau2`-support. -/
theorem tau2_P2type_signalizer
    {M Mstar U K R H : Subgroup G} {r : ℕ} [Fact r.Prime]
    (hMP2 : M ∈ typeP2MaximalSubgroups (G := G))
    (hCompl : KappaComplement M U K)
    (hMstar : Mstar ∈ minSimple_max_groups_of (G := G)
      (Subgroup.centralizer (K : Set G) : Set G))
    (hR : IsSylowSubgroupOf r R U)
    (hH : H ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (R : Set G) : Set G))
    (hnotTau2H : ¬ IsPiNumber (tau2Primes H)ᶜ (Nat.card H)) :
    Tau2P2TypeSignalizerConclusion M K H := by
  classical
  have subgroup_le_normal_isHall_local
      {K₀ : Type u} [Group K₀] [Finite K₀] {pi₀ : Set ℕ}
      {N₀ L₀ : Subgroup K₀} (hNnormal : N₀.Normal)
      (hNHall : IsHall pi₀ N₀)
      (hLpi : IsPiNumber pi₀ (Nat.card L₀)) : L₀ ≤ N₀ := by
    letI : N₀.Normal := hNnormal
    have hcop : (Nat.card L₀).Coprime N₀.index := by
      apply Nat.coprime_of_dvd
      intro ℓ hℓ hℓL hℓIndex
      exact hNHall.isPiNumber_index hℓ hℓIndex (hLpi hℓ hℓL)
    intro x hxL
    let quot : K₀ →* (K₀ ⧸ N₀) := QuotientGroup.mk' N₀
    have horderL : orderOf (quot x) ∣ Nat.card L₀ :=
      (orderOf_map_dvd quot x).trans (L₀.orderOf_dvd_natCard hxL)
    have horderIndex : orderOf (quot x) ∣ N₀.index := by
      simpa only [N₀.index_eq_card] using orderOf_dvd_natCard (quot x)
    have horderOne : orderOf (quot x) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
    exact (QuotientGroup.eq_one_iff x).mp
      (by simpa [quot] using orderOf_eq_one_iff.mp horderOne)
  have hMP : M ∈ typePMaximalSubgroups (G := G) := hMP2.1
  have hmaxM : M ∈ minSimple_max_groups (G := G) := hMP.1
  have hmaxH : H ∈ minSimple_max_groups (G := G) := hH.1
  have hmaxMstar : Mstar ∈ minSimple_max_groups (G := G) := hMstar.1
  let q := Nat.card K
  have hqPrime : q.Prime := by
    simpa only [q] using
      ((Ptype_structure hMP hCompl.K_le_M hCompl.hall_K).typeP2 hMP2).card_K_prime
  letI : Fact q.Prime := ⟨hqPrime⟩
  rcases P2type_signalizer hMP2 hCompl hMstar hR hH with
    ⟨hHF, hUH, hjoin, hnorm, hKfitD, hHallD⟩
  let D : Subgroup G := H ⊓ Mstar
  have hDH : D ≤ H := inf_le_left
  have hDMstar : D ≤ Mstar := inf_le_right

  obtain ⟨p₀, hp₀Support, hp₀Tau⟩ :=
    exists_primeSupport_inter_of_not_isPiNumber hnotTau2H
  have hp₀q : p₀ = q := by
    simpa only [q] using
      tau2Prime_eq_cardK_of_P2Signalizer
        hMP2 hCompl hMstar hR hH hp₀Tau
  have hqTau : q ∈ tau2Primes H := by
    simpa only [hp₀q] using hp₀Tau
  have hTauEq : tau2Primes H = {q} := by
    ext p
    simp only [Set.mem_singleton_iff]
    constructor
    · intro hpTau
      simpa only [q] using
        tau2Prime_eq_cardK_of_P2Signalizer
          hMP2 hCompl hMstar hR hH hpTau
    · rintro rfl
      exact hqTau

  obtain ⟨Mpartner, hEmbed⟩ :=
    Ptype_embedding hMP hCompl.K_le_M hCompl.hall_K
  have hKline : RankOneLineIn q K K :=
    ⟨le_rfl, isElementaryAbelianOfRank_one_of_card_eq_prime rfl⟩
  have hPartnerUnique := hEmbed.rankOne_unique hqPrime hKline
  have hMstarEq : Mstar = Mpartner :=
    eq_uniq_mmax hPartnerUnique hmaxMstar hMstar.2
  subst Mpartner
  let Ks : Subgroup G := pTypePartner M K
  have hStarStruct := Ptype_structure hEmbed.Mstar_typeP
    hEmbed.Kstar_le_Mstar hEmbed.Kstar_hall_kappa
  have hKsigma : K ≤ sigmaCore Mstar := by
    rw [← hEmbed.doubleCentralizer]
    exact centralizerWithin_le_left _ _
  have hqSigma : q ∈ sigmaPrimes Mstar :=
    (sigmaCore_isPiNumber Mstar).of_dvd
      (Subgroup.card_dvd_of_le hKsigma) hqPrime (by simp [q])
  have hqNotBetaTop : q ∉ betaPrimes (⊤ : Subgroup G) :=
    (tau2_not_beta hmaxH hqTau).1
  have hqNotBeta : q ∉ betaPrimes Mstar := by
    intro hqBeta
    have hpair :
        q ∈ sigmaPrimes Mstar ∩ betaPrimes (⊤ : Subgroup G) := by
      rw [predI_sigma_beta hmaxMstar]
      exact hqBeta
    exact hqNotBetaTop hpair.2
  have hMstarP1 : Mstar ∈ typeP1MaximalSubgroups (G := G) := by
    by_contra hnotP1
    have hP2 : Mstar ∈ typeP2MaximalSubgroups (G := G) :=
      ⟨hEmbed.Mstar_typeP, hnotP1⟩
    have heq := (hStarStruct.typeP2 hP2).sigma_eq_beta
    apply hqNotBeta
    rw [← heq]
    exact hqSigma

  letI : IsSolvable Mstar := mmax_sol hmaxMstar
  have hSigmaSol : IsSolvable (sigmaCore Mstar) :=
    isSolvable_of_injective
      (Subgroup.inclusion (sigmaCore_le Mstar))
      (Subgroup.inclusion_injective (sigmaCore_le Mstar))
  obtain ⟨D₀, hD₀sigma, hHallD₀q⟩ :=
    MathlibSupport.exists_ambient_isHall_of_isSolvable
      hSigmaSol ({q} : Set ℕ)ᶜ
  have hHallD₀ :
      IsHall ({Nat.card (kappaCentralizer Mstar Ks)} : Set ℕ)ᶜ
        (D₀.subgroupOf (sigmaCore Mstar)) := by
    simpa only [Ks, kappaCentralizer, hEmbed.doubleCentralizer, q] using
      hHallD₀q
  have hFcoreEq : Fitting_core Mstar = sigmaCore Mstar := by
    by_contra hne
    have hn := (Fcore_structure hmaxMstar).nonnilpotent
      hEmbed.Kstar_le_Mstar hEmbed.Kstar_hall_kappa hne
      hD₀sigma hHallD₀
    apply hqNotBeta
    simpa only [Ks, kappaCentralizer, hEmbed.doubleCentralizer, q] using
      hn.partner_prime_beta
  have hSigmaNil : Group.IsNilpotent (sigmaCore Mstar) :=
    (Fcore_eq_Msigma hmaxMstar).mp hFcoreEq
  have hKsne : Ks ≠ ⊥ := by
    intro hKsbot
    exact hEmbed.Mstar_typeP.2
      ((trivg_kappa hmaxMstar hEmbed.Kstar_le_Mstar
        hEmbed.Kstar_hall_kappa).mp hKsbot)
  obtain ⟨Us, hUsCompl⟩ :=
    ex_kappa_compl hmaxMstar hEmbed.Kstar_le_Mstar
      hEmbed.Kstar_hall_kappa
  have hUsbot : Us = ⊥ :=
    (trivg_kappa_compl hmaxMstar hUsCompl).2 hMstarP1
  have hSigmaDer : sigmaCore Mstar = derivedWithin Mstar := by
    have hdec := (kappa_structure hmaxMstar hUsCompl).derived_decomposition hKsne
    have htop := hdec.2.2.2.sup_eq_top
    have hSigmaTop :
        (sigmaCore Mstar).subgroupOf (derivedWithin Mstar) = ⊤ := by
      simpa only [hUsbot, Subgroup.bot_subgroupOf, sup_bot_eq] using htop
    exact le_antisymm hdec.1 (Subgroup.subgroupOf_eq_top.mp hSigmaTop)
  have hKsecond : K ≤ secondDerivedWithin Mstar := by
    simpa only [Ks, kappaCentralizer, hEmbed.doubleCentralizer] using
      (Ptype_cyclics hEmbed.Mstar_typeP hEmbed.Kstar_le_Mstar
        hEmbed.Kstar_hall_kappa).partner_le_secondDerived
  have hKderSigma : K ≤ derivedWithin (sigmaCore Mstar) := by
    simpa only [secondDerivedWithin, ← hSigmaDer] using hKsecond
  have hKne : K ≠ ⊥ := by
    exact K.one_lt_card_iff_ne_bot.mp (by simpa [q] using hqPrime.one_lt)

  let Q : Subgroup G := pCoreWithin q Mstar
  have hqFcore : q ∈ primeSupport (Nat.card (Fitting_core Mstar)) := by
    refine ⟨hqPrime, ?_⟩
    rw [hFcoreEq]
    exact (by simp [q] : q ∣ Nat.card K).trans
      (Subgroup.card_dvd_of_le hKsigma)
  have hQsyl : IsSylowSubgroupOf q Q Mstar := by
    simpa only [Q, pCoreWithin] using Fcore_pcore_Sylow Mstar hqFcore
  have hQMstar : Q ≤ Mstar := by
    obtain ⟨Sq, hQSq⟩ := hQsyl
    rw [hQSq]
    exact Subgroup.map_subtype_le (Sq : Subgroup Mstar)
  have hQsigma : Q ≤ sigmaCore Mstar := by
    let QM : Subgroup Mstar := Q.subgroupOf Mstar
    have hQMpi : IsPiNumber (sigmaPrimes Mstar) (Nat.card QM) := by
      rw [MathlibSupport.natCard_subgroupOf_eq
        hQMstar]
      exact hQsyl.isPGroup.isPiNumber_natCard hqSigma
    have hle : QM ≤ (sigmaCore Mstar).subgroupOf Mstar :=
      subgroup_le_normal_isHall_local
        (by simpa using sigmaCore_normal Mstar)
        (Msigma_Hall hmaxMstar) hQMpi
    intro x hx
    exact hle
      (show (⟨x, hQMstar hx⟩ : Mstar) ∈ QM from hx)

  have hQnoncomm : ¬ IsMulCommutative Q := by
    intro hQcomm
    let S : Subgroup G := sigmaCore Mstar
    let QS : Subgroup S := Q.subgroupOf S
    let KS : Subgroup S := K.subgroupOf S
    let CS : Subgroup S := pPrimeCore q S
    letI : Group.IsNilpotent S := by simpa only [S] using hSigmaNil
    have hQsylS : IsSylowSubgroupOf q Q S :=
      hQsyl.restrict_of_le hQsigma (sigmaCore_le Mstar)
    obtain ⟨Sq, hQSq⟩ := hQsylS
    have hQScore : QS = pCore q S := by
      have hQSylow : QS = (Sq : Subgroup S) := by
        change Q.comap S.subtype = (Sq : Subgroup S)
        rw [hQSq, Subgroup.comap_map_eq_self_of_injective
          S.subtype_injective]
      rw [hQSylow, pCore_eq_sylow_of_isNilpotent Sq]
    have hKq : IsPGroup q K := hKline.2.isPGroup
    have hKSq : IsPGroup q KS :=
      hKq.of_equiv (Subgroup.subgroupOfEquivOfLe hKsigma).symm
    have hKSQS : KS ≤ QS := by
      rw [hQScore]
      exact hKSq.le_pCore_of_isNilpotent
    have hKSder : KS ≤ _root_.commutator S := by
      intro x hx
      rcases hKderSigma hx with ⟨y, hy, hyx⟩
      have hyEq : y = x := Subtype.ext hyx
      have hxComm : (x : S) ∈ _root_.commutator S := hyEq ▸ hy
      exact hxComm
    have hQScomm : IsMulCommutative QS := by
      apply isMulCommutative_iff.mpr
      intro x y
      apply Subtype.ext
      apply Subtype.ext
      simpa using congrArg Subtype.val
        (isMulCommutative_iff.mp hQcomm
          ⟨((x : S) : G), x.property⟩
          ⟨((y : S) : G), y.property⟩)
    have hcommQS : ⁅QS, QS⁆ = (⊥ : Subgroup S) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
        (Subgroup.le_centralizer_iff_isMulCommutative.mpr hQScomm)
    have hsup : CS ⊔ QS = (⊤ : Subgroup S) := by
      rw [hQScore]
      simpa only [CS, sup_comm] using
        (sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := S) q)
    have hcop : Nat.Coprime (Nat.card CS) (Nat.card KS) := by
      have hc := (pPrimeCore_coprime_card (G := S) (p := q)).symm
      have hcardKS : Nat.card KS = Nat.card K := by
        simpa only [KS] using
          MathlibSupport.natCard_subgroupOf_eq hKsigma
      rw [hcardKS]
      simpa only [CS, q] using hc
    letI : CS.Normal := by infer_instance
    have hfocal :
        KS ⊓ _root_.commutator S = KS ⊓ ⁅QS, QS⁆ :=
      Section06.pprod_focal_coprime hsup hKSQS hcop
    have hKSbot : KS = ⊥ := by
      rw [inf_eq_left.mpr hKSder, hcommQS, inf_bot_eq] at hfocal
      exact hfocal
    apply hKne
    rw [← Subgroup.map_subgroupOf_eq_of_le hKsigma]
    rw [show K.subgroupOf S = ⊥ by simpa only [KS] using hKSbot]
    exact Subgroup.map_bot S.subtype

  obtain ⟨A, hAD, hAH, hA⟩ :=
    ex_tau2Elem (M := H) hDH hHallD hqTau
  have hNonab :=
    nonabelian_tau2 hmaxH hDH hHallD hqTau hAD hA
      hQsyl.isPGroup hQnoncomm
  let X : Subgroup G := centralizerWithin A (sigmaCore H)
  have hXcard : Nat.card X = q := by
    simpa only [X] using hNonab.A0_card
  have hHneMstar : H ≠ Mstar := by
    intro hEq
    apply hqTau.2.1
    simpa only [hEq] using hqSigma
  have hXneK : X ≠ K := by
    intro hXK
    have hKcentSigma : K ≤ Subgroup.centralizer (sigmaCore H : Set G) := by
      rw [← hXK]
      exact inf_le_right
    have hSigmaCentK : sigmaCore H ≤ Subgroup.centralizer (K : Set G) :=
      Subgroup.le_centralizer_iff.mp hKcentSigma
    have hSigmaMstar : sigmaCore H ≤ Mstar :=
      hSigmaCentK.trans hMstar.2
    have hsd := sdprod_sigma hmaxH hDH hHallD
    have hHMstar : H ≤ Mstar := by
      intro x hx
      obtain ⟨⟨s, d⟩, hsdEq⟩ := hsd.2.2.2.2 ⟨x, hx⟩
      have hsdG : (s : G) * (d : G) = x :=
        congrArg Subtype.val hsdEq
      rw [← hsdG]
      exact Mstar.mul_mem (hSigmaMstar s.property) (hDMstar d.property)
    exact hHneMstar (eq_mmax hmaxH hmaxMstar hHMstar)

  have hActx := tau2_compl_context hmaxH hDH hHallD hqTau hAD hA
  have hAfitD : A ≤ fittingWithin D :=
    nilpotent_normal_le_fittingWithin_15_8 hAD hActx.A_normal
      hA.isPGroup.isNilpotent
  have hFitDpi :
      IsPiNumber (sigmaPrimes H)ᶜ (Nat.card (fittingWithin D)) := by
    have hDpi : IsPiNumber (sigmaPrimes H)ᶜ (Nat.card D) := by
      simpa only [D, MathlibSupport.natCard_subgroupOf_eq hDH] using
        hHallD.isPiNumber_card
    exact hDpi.of_dvd (Subgroup.card_dvd_of_le (fittingWithin_le D))
  have hFitDcomm : IsMulCommutative (fittingWithin D) :=
    sigma'_nil_abelian hmaxH
      ((fittingWithin_le D).trans hDH) hFitDpi
      (fittingWithin_isNilpotent D)
  have hAcentK : A ≤ Subgroup.centralizer (K : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    exact (congrArg Subtype.val
      (isMulCommutative_iff.mp hFitDcomm
        ⟨a, hAfitD ha⟩ ⟨k, hKfitD hk⟩)).symm
  have hXnotM : ¬ X ≤ M := by
    intro hXM
    have hXq : IsPGroup q X :=
      (isElementaryAbelianOfRank_one_of_card_eq_prime hXcard).isPGroup
    have hKcentX : K ≤ Subgroup.centralizer (X : Set G) :=
      (Subgroup.le_centralizer_iff.mp hAcentK).trans
        (Subgroup.centralizer_le (centralizerWithin_le_left A (sigmaCore H)))
    have hKnormX : K ≤ Subgroup.normalizer (X : Set G) :=
      hKcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
    let J : Subgroup G := K ⊔ X
    have hJq : IsPGroup q J :=
      hKline.2.isPGroup.to_sup_of_normal_right' hXq hKnormX
    have hqKappa : q ∈ kappaPrimes M := by
      have hqKsub : q ∣ Nat.card (K.subgroupOf M) := by
        simp [q, MathlibSupport.natCard_subgroupOf_eq hCompl.K_le_M]
      exact hCompl.hall_K.isPiNumber_card hqPrime hqKsub
    have hJpi : IsPiNumber (kappaPrimes M) (Nat.card J) :=
      hJq.isPiNumber_natCard hqKappa
    have hJM : J ≤ M := sup_le hCompl.K_le_M hXM
    have hJK : J = K :=
      intermediate_eq_isHall_of_isPiNumber_15_8
        le_sup_left hJM hCompl.hall_K hJpi
    have hXK : X ≤ K := by
      exact le_sup_right.trans_eq hJK
    apply hXneK
    apply Subgroup.eq_of_le_of_card_ge hXK
    simpa only [hXcard, q] using (Nat.le_refl (Nat.card K))
  have hCentUNotM : ¬ Subgroup.centralizer (U : Set G) ≤ M := by
    intro hCentUM
    apply hXnotM
    exact inf_le_right.trans
      ((Subgroup.centralizer_le hUH).trans hCentUM)

  have hMcompl : IsPiNumber (tau2Primes M)ᶜ (Nat.card M) := by
    intro p hpPrime hpM
    simp only [Set.mem_compl_iff]
    intro hpTau
    letI : Fact p.Prime := ⟨hpPrime⟩
    have hCtx := kappa_compl_context hmaxM hCompl
    let E : Subgroup G := U ⊔ K
    obtain ⟨B, hBE, hBM, hB⟩ :=
      ex_tau2Elem (M := M) hCtx.U_sup_K_le_M
        hCtx.hall_sigma_complement hpTau
    have hBCtx := tau2_compl_context hmaxM hCtx.U_sup_K_le_M
      hCtx.hall_sigma_complement hpTau hBE hB
    have hpNotKappa : p ∉ kappaPrimes M := by
      intro hpKappa
      exact (rank_kappa hpKappa).2 ⟨B, hBM, hB⟩
    let pi : Set ℕ := (sigmaKappaPrimes M)ᶜ
    have hpPi : p ∈ pi := by
      intro hpSigmaKappa
      exact hpSigmaKappa.elim hpTau.2.1 hpNotKappa
    have hBpi : IsPiNumber pi (Nat.card B) :=
      hB.isPGroup.isPiNumber_natCard hpPi
    have hUpi : IsPiNumber pi (Nat.card U) := by
      simpa only [pi, MathlibSupport.natCard_subgroupOf_eq hCompl.U_le_M]
        using hCompl.hall_U.isPiNumber_card
    let BE : Subgroup E := B.subgroupOf E
    let UE : Subgroup E := U.subgroupOf E
    have hUE : U ≤ E := le_sup_left
    have hBEpi : IsPiNumber pi (Nat.card BE) := by
      change IsPiNumber pi (Nat.card (B.subgroupOf E))
      rw [MathlibSupport.natCard_subgroupOf_eq hBE]
      exact hBpi
    have hUEpi : IsPiNumber pi (Nat.card UE) := by
      simpa only [UE, MathlibSupport.natCard_subgroupOf_eq hUE] using hUpi
    have hSupPi : IsPiNumber pi (Nat.card (BE ⊔ UE : Subgroup E)) :=
      isPiNumber_card_sup_of_normal_left hBCtx.A_normal hBEpi hUEpi
    let J : Subgroup G := B ⊔ U
    have hJE : J ≤ E := sup_le hBE hUE
    have hJpi : IsPiNumber pi (Nat.card J) := by
      rw [← MathlibSupport.natCard_subgroupOf_eq hJE]
      rw [Subgroup.subgroupOf_sup hBE hUE]
      exact hSupPi
    have hJM : J ≤ M := hJE.trans hCtx.U_sup_K_le_M
    have hJU : J = U :=
      intermediate_eq_isHall_of_isPiNumber_15_8
        le_sup_right hJM hCompl.hall_U hJpi
    have hBU : B ≤ U := le_sup_left.trans_eq hJU
    apply hCentUNotM
    exact (Subgroup.centralizer_le hBU).trans
      (hBCtx.centralizer_le_E.trans hCtx.U_sup_K_le_M)
  exact ⟨by simpa only [q] using hqPrime,
    by simpa only [q] using hTauEq, hMcompl⟩

end

end Submission.OddOrder.BG.Section15
