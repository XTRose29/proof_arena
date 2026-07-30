import Submission.OddOrder.BG.Section16.SummaryA

/-!
# Bender--Glauberman Section 16: summary C

This phase packages and proves the eleven conclusions of summary C from the
interfaces already established by summary A and the preceding section modules.
-/

namespace Submission.OddOrder.BG.Section16

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.BG.Section13
open Submission.OddOrder.BG.Section14
open Submission.OddOrder.BG.Section15
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]

/-! ## The summary interface -/

/-- The eleven conclusions of Summary C for a nontrivial kappa complement. -/
structure BGSummaryC (M U K : Subgroup G) where
  U_abelian : IsMulCommutative U
  normalizer_U_not_le : ¬ Subgroup.normalizer (U : Set G) ≤ M
  partner_cyclic : IsCyclic (pTypePartner M K)
  partner_ne_bot : pTypePartner M K ≠ ⊥
  partner_le_Fcore : pTypePartner M K ≤ Fitting_core M
  Fcore_not_cyclic : ¬ IsCyclic (Fitting_core M)
  sigma_U_derived :
    IsInternalSemidirectProductIn (sigmaCore M) U (derivedWithin M)
  partner_le_secondDerived :
    pTypePartner M K ≤ secondDerivedWithin M
  Mstar : Subgroup G
  Mstar_typeP : Mstar ∈ typePMaximalSubgroups (G := G)
  doubleCentralizer :
    centralizerWithin (sigmaCore Mstar) (pTypePartner M K) = K
  partner_le_Mstar : pTypePartner M K ≤ Mstar
  partner_hall_kappa :
    IsHall (kappaPrimes Mstar) ((pTypePartner M K).subgroupOf Mstar)
  partner_unique : sigmaMaximalOvergroups (K : Set G) = {Mstar}
  partner_rankOne_unique : ∀ {p : ℕ}, p.Prime →
    ∀ {X : Subgroup G}, RankOneLineIn p (pTypePartner M K) X →
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {M}
  K_rankOne_unique : ∀ {p : ℕ}, p.Prime →
    ∀ {X : Subgroup G}, RankOneLineIn p K X →
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (X : Set G) : Set G) = {Mstar}
  inf_eq_join : M ⊓ Mstar = pTypeJoin M K
  join_direct :
    IsInternalDirectProductIn K (pTypePartner M K) (pTypeJoin M K)
  join_cyclic : IsCyclic (pTypeJoin M K)
  typeP2_or_partner_typeP2 :
    M ∈ typeP2MaximalSubgroups (G := G) ∨
      Mstar ∈ typeP2MaximalSubgroups (G := G)
  typeP_transitive : ∀ {H : Subgroup G},
    H ∈ typePMaximalSubgroups (G := G) →
      AreConjugateSubgroups M H ∨ AreConjugateSubgroups Mstar H
  join_difference_normalizedTI :
    IsNormalizedTI (pTypeTISet M K) ⊤ (pTypeJoin M K)
  outer_support_eq_classSupport :
    FTsupport0 M \ FTsupport M = classSupportWithin M (pTypeTISet M K)
  outer_support_normalizedTI :
    IsNormalizedTI (FTsupport0 M \ FTsupport M) ⊤ M
  nontrivial_U_case : U ≠ ⊥ →
    (Nat.card K).Prime ∧
      IsNormalizedTI (subgroupNonidentity (fittingWithin M)) ⊤ M ∧
      sigmaCore M ≤ fittingWithin M
  trivial_U_case : U = ⊥ → (Nat.card (pTypePartner M K)).Prime

/-! ## The unique sigma overgroup -/

/-- A nonidentity element of a finite subgroup contains a prime-order line in
its cyclic subgroup. -/
private theorem rankOneLine_below_zpowers
    {K : Subgroup G} {x : G} (hxK : x ∈ K) (hxne : x ≠ 1) :
    ∃ p : ℕ, p.Prime ∧ ∃ X : Subgroup G,
      RankOneLineIn p K X ∧ X ≤ Subgroup.zpowers x := by
  let C : Subgroup G := Subgroup.zpowers x
  have hC : C ≠ ⊥ := by
    intro hCbot
    have : x ∈ (⊥ : Subgroup G) := hCbot ▸ Subgroup.mem_zpowers x
    exact hxne (Subgroup.mem_bot.mp this)
  obtain ⟨p, hp, hpC⟩ :=
    Nat.exists_prime_and_dvd (C.one_lt_card_iff_ne_bot.mpr hC).ne'
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := C) p hpC
  let X : Subgroup G := Subgroup.zpowers (y : G)
  have hXC : X ≤ C := Subgroup.zpowers_le.mpr y.property
  have hXK : X ≤ K := hXC.trans (Subgroup.zpowers_le.mpr hxK)
  have hcard : Nat.card X = p := by
    change Nat.card (Subgroup.zpowers (y : G)) = p
    rw [Nat.card_zpowers]
    simpa using hy
  exact ⟨p, hp, X,
    ⟨hXK, isElementaryAbelianOfRank_one_of_card_eq_prime hcard⟩, hXC⟩

/-- The embedding witness is the sole sigma-maximal overgroup of the original
kappa complement. -/
private theorem sigmaOvergroups_eq_embeddingWitness
    {M K Mstar : Subgroup G}
    (hKne : K ≠ ⊥) (hEmbed : PTypeEmbedding M K Mstar) :
    sigmaMaximalOvergroups (K : Set G) = {Mstar} := by
  classical
  letI : IsCyclic (pTypeJoin M K) :=
    hEmbed.cyclicStructure.cyclic_join
  have hKcyclic : IsCyclic K :=
    Subgroup.isCyclic_of_le (H' := pTypeJoin M K) le_sup_left
  obtain ⟨x, hgen⟩ :=
    (K.isCyclic_iff_exists_zpowers_eq_top).mp hKcyclic
  have hxK : x ∈ K := by
    rw [← hgen]
    exact Subgroup.mem_zpowers x
  have hxne : x ≠ 1 := by
    intro hx
    apply hKne
    rw [← hgen, hx]
    simp
  have hKsigma : K ≤ sigmaCore Mstar := by
    rw [← hEmbed.doubleCentralizer]
    exact centralizerWithin_le_left _ _
  have hMstarK : Mstar ∈ sigmaMaximalOvergroups (K : Set G) :=
    ⟨hEmbed.Mstar_typeP.1, hKsigma⟩
  apply Set.eq_singleton_iff_unique_mem.mpr
  refine ⟨hMstarK, ?_⟩
  intro N hNK
  by_contra hN
  have hMstarX :
      Mstar ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) := by
    simpa [hgen] using hMstarK
  have hNX :
      N ∈ sigmaMaximalOvergroups (Subgroup.zpowers x : Set G) := by
    simpa [hgen] using hNK
  have hmany :
      1 < (sigmaMaximalOvergroups (Subgroup.zpowers x : Set G)).ncard :=
    (Set.one_lt_ncard).2 ⟨Mstar, hMstarX, N, hNX, Ne.symm hN⟩
  have hell : sigmaLength x = 1 :=
    Msigma_ell1 hEmbed.Mstar_typeP.1 (hKsigma hxK) hxne
  have hsignal := FT_signalizer_context hell
  have hlarge := hsignal.large hmany
  obtain ⟨p, hp, X, hXK, hXx⟩ :=
    rankOneLine_below_zpowers hxK hxne
  have hCentXle : Subgroup.centralizer (X : Set G) ≤ Mstar :=
    (mem_uniq_mmax (hEmbed.rankOne_unique hp hXK)).2
  let R : Subgroup G := ftSignalizer x
  let B : Subgroup G := ftSignalizerBase x
  have hover := hlarge.overgroup_context hMstarX
  have hRle : R ≤ elementCentralizerWithin (Mstar ⊓ B) x := by
    intro r hr
    have hrCentX : r ∈ Subgroup.centralizer (X : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hrFull : r ∈ elementCentralizer x :=
        hsignal.basic.R_le_centralizer hr
      exact Subgroup.mem_centralizer_iff.mp hrFull y (hXx hy)
    exact ⟨⟨hCentXle hrCentX, sigmaCore_le B hr.1⟩, hr.2⟩
  have hRbot : R = ⊥ := by
    apply le_antisymm
    · intro r hr
      have : r ∈ R ⊓ elementCentralizerWithin (Mstar ⊓ B) x :=
        ⟨hr, hRle hr⟩
      rw [hover.centralizer_disjoint] at this
      simpa using this
    · exact bot_le
  exact hlarge.signalizer_ne_bot hRbot

/-! ## The normalizer escape -/

/-- The `U`-normalizer cannot remain in its original maximal subgroup once
the kappa factor is nontrivial. -/
private theorem normalizer_U_escapes
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K) (hKne : K ≠ ⊥) :
    ¬ Subgroup.normalizer (U : Set G) ≤ M := by
  have hMP : M ∈ typePMaximalSubgroups (G := G) := by
    refine ⟨hM, ?_⟩
    intro hF
    exact hKne ((trivg_kappa hM hCompl.K_le_M hCompl.hall_K).2 hF)
  obtain ⟨L, hLmax, hCentKL⟩ :=
    mmax_exists (Subgroup.centralizer (K : Set G))
      (mFT_cent_proper K hKne)
  by_cases hUbot : U = ⊥
  · intro hnormal
    have hnormalizerBot :
        Subgroup.normalizer ((⊥ : Subgroup G) : Set G) = ⊤ :=
      Subgroup.normalizer_eq_top (⊥ : Subgroup G)
    rw [hUbot, hnormalizerBot] at hnormal
    have htopM : (⊤ : Subgroup G) ≤ M := hnormal
    exact (not_le_of_gt (mmax_proper hM)) htopM
  · have hMP2 : M ∈ typeP2MaximalSubgroups (G := G) :=
      ⟨hMP, fun hMP1 ↦ hUbot ((trivg_kappa_compl hM hCompl).2 hMP1)⟩
    obtain ⟨r, hr, hrU⟩ := Nat.exists_prime_and_dvd
      (U.one_lt_card_iff_ne_bot.mpr hUbot).ne'
    letI : Fact r.Prime := ⟨hr⟩
    let S : Sylow r U := Classical.choice Sylow.nonempty
    let R : Subgroup G := ambientSylow U S
    have hR : IsSylowSubgroupOf r R U := ⟨S, rfl⟩
    have hRne : R ≠ ⊥ := by
      intro hRbot
      have hSne : (S : Subgroup U) ≠ ⊥ := S.ne_bot_of_dvd_card hrU
      apply hSne
      exact (Subgroup.map_eq_bot_iff_of_injective
        (S : Subgroup U) U.subtype_injective).mp hRbot
    obtain ⟨H, hHmax, hNormRH⟩ :=
      mmax_exists (Subgroup.normalizer (R : Set G))
        (mFT_norm_proper R hRne (mFT_pgroup_proper R hR.isPGroup))
    have hsignal := P2type_signalizer hMP2 hCompl
      (show L ∈ minSimple_max_groups_of (G := G)
          (Subgroup.centralizer (K : Set G) : Set G) from
        ⟨hLmax, hCentKL⟩)
      hR
      (show H ∈ minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (R : Set G) : Set G) from
        ⟨hHmax, hNormRH⟩)
    intro hnormal
    exact hsignal.2.2.2.1 (inf_le_right.trans hnormal)

/-! ## Support and final assembly -/

/-- A normal Hall subgroup contains every ambient element whose order is
supported on its Hall prime set. -/
private theorem mem_normalHall_of_order_support
    {pi : Set ℕ} {C K : Subgroup G}
    (hKC : K ≤ C) (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    {x : G} (hxC : x ∈ C) (hxPi : IsPiNumber pi (orderOf x)) :
    x ∈ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  let xC : C := ⟨x, hxC⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have hxPiC : IsPiNumber pi (orderOf xC) := by
    simpa [xC] using hxPi
  have hpi : IsPiNumber pi (orderOf (qC xC)) :=
    hxPiC.of_dvd (orderOf_map_dvd qC xC)
  have hcompl : IsPiNumber piᶜ (orderOf (qC xC)) := by
    apply hKHall.isPiNumber_index.of_dvd
    have hdvd : orderOf (qC xC) ∣ KC.index := by
      rw [KC.index_eq_card]
      exact orderOf_dvd_natCard (qC xC)
    simpa only [KC] using hdvd
  have horderOne : orderOf (qC xC) = 1 := by
    simpa [Nat.Coprime] using hpi.coprime_compl hcompl
  have hq : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  change QuotientGroup.mk' KC xC = 1 at hq
  exact (QuotientGroup.eq_one_iff xC).mp hq

/-- Prime divisors of an element order are supported on the cardinality of
any finite subgroup containing it. -/
private theorem order_supported_on_subgroup_card
    {H : Subgroup G} {x : G} (hx : x ∈ H) :
    IsPiNumber (primeSupport (Nat.card H)) (orderOf x) := by
  intro p hp hpx
  exact ⟨hp, hpx.trans (by
    simpa using orderOf_dvd_natCard (⟨x, hx⟩ : H))⟩

/-- Saturating a normalized-TI set by an intermediate subgroup replaces its
relative normalizer by that subgroup. -/
private theorem normalizedTI_classSupportWithin
    {H : Type*} [Group H]
    {S : Set H} {D N L : Subgroup H}
    (hTI : IsNormalizedTI S D N) (hNL : N ≤ L) (hLD : L ≤ D) :
    IsNormalizedTI (classSupportWithin L S) D L := by
  rw [isNormalizedTI_iff_mem_conj]
  refine ⟨?_, hLD, ?_⟩
  · rcases hTI.1 with ⟨a, ha⟩
    exact ⟨a, a, ha, 1, L.one_mem, by simp⟩
  · intro a ha g hgD
    constructor
    · intro hga
      rcases ha with ⟨s, hs, y, hyL, hya⟩
      rcases hga with ⟨t, ht, z, hzL, hzg⟩
      let q : H := y * g * z⁻¹
      have hqD : q ∈ D :=
        D.mul_mem (D.mul_mem (hLD hyL) hgD) (D.inv_mem (hLD hzL))
      have hqConj : q⁻¹ * s * q = t := by
        change y⁻¹ * s * y = a at hya
        change z⁻¹ * t * z = g⁻¹ * a * g at hzg
        dsimp only [q]
        rw [show (y * g * z⁻¹)⁻¹ * s * (y * g * z⁻¹) =
            z * (g⁻¹ * (y⁻¹ * s * y) * g) * z⁻¹ by group,
          hya, ← hzg]
        group
      have hqN : q ∈ N :=
        ((isNormalizedTI_iff_mem_conj.mp hTI).2.2 hs hqD).mp (by
          rw [hqConj]
          exact ht)
      have hgEq : g = y⁻¹ * q * z := by
        dsimp only [q]
        group
      rw [hgEq]
      exact L.mul_mem (L.mul_mem (L.inv_mem hyL) (hNL hqN)) hzL
    · intro hgL
      exact (classSupportWithin_rightConj_iff
        (G := L) (S := S) (g := g) hgL).2 ha

/-- The mixed part of the type-P direct product is exactly the support outside
the ordinary Dade support. -/
private theorem outerSupport_package
    {M U K Mstar : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K)
    (hKne : K ≠ ⊥)
    (hEmbed : PTypeEmbedding M K Mstar)
    (hJoinDirect :
      IsInternalDirectProductIn K (pTypePartner M K) (pTypeJoin M K))
    (hFTder :
      IsInternalSemidirectProductIn (sigmaCore M) U (FTder M)) :
    FTsupport0 M \ FTsupport M =
        classSupportWithin M (pTypeTISet M K) ∧
      IsNormalizedTI (FTsupport0 M \ FTsupport M) ⊤ M := by
  classical
  let D : Subgroup G := FTder M
  let pi : Set ℕ := primeSupport (Nat.card D)
  let Ks : Subgroup G := pTypePartner M K
  let Z : Subgroup G := pTypeJoin M K
  let T : Set G := pTypeTISet M K
  have hP : M ∈ typePMaximalSubgroups (G := G) := by
    exact ⟨hM, by
      intro hF
      exact hKne
        ((trivg_kappa hM hCompl.K_le_M hCompl.hall_K).2 hF)⟩
  have htype : FTtype M ≠ 1 := (FTtype_Pmax hM).mp hP
  have hDderived : D = derivedWithin M := by
    simp [D, FTder, ftDerived, htype]
  have hcopDK : Nat.Coprime (Nat.card D) (Nat.card K) := by
    rw [hDderived]
    apply Nat.coprime_of_dvd
    intro p hp hpD hpK
    have hpKsub : p ∣ Nat.card (K.subgroupOf M) := by
      simpa only [MathlibSupport.natCard_subgroupOf_eq
        hEmbed.derived_sdprod.2.1] using hpK
    have hpKappa : p ∈ kappaPrimes M :=
      hCompl.hall_K.isPiNumber_card hp hpKsub
    have hpIndex : p ∣ (K.subgroupOf M).index := by
      rw [hEmbed.derived_sdprod.2.2.2.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hEmbed.derived_sdprod.1]
      exact hpD
    exact hCompl.hall_K.isPiNumber_index hp hpIndex hpKappa
  have hKpi : IsPiNumber piᶜ (Nat.card K) := by
    intro p hp hpK hpPi
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨p, hp, hpPi.2, hpK⟩) hcopDK
  have hKsD : Ks ≤ D :=
    (centralizerWithin_le_left (sigmaCore M) K).trans hFTder.1
  have hKspi : IsPiNumber pi (Nat.card Ks) :=
    IsPiNumber.primeSupport_self.of_dvd (Subgroup.card_dvd_of_le hKsD)
  have hKHallM : IsHall piᶜ (K.subgroupOf M) := by
    constructor
    · rw [MathlibSupport.natCard_subgroupOf_eq hCompl.K_le_M]
      exact hKpi
    · rw [hEmbed.derived_sdprod.2.2.2.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hEmbed.derived_sdprod.1]
      change IsPiNumber piᶜᶜ (Nat.card (derivedWithin M))
      rw [← hDderived]
      simpa only [compl_compl] using
        (IsPiNumber.primeSupport_self : IsPiNumber pi (Nat.card D))
  have hZM : Z ≤ M := by
    dsimp only [Z, pTypeJoin, Ks]
    exact sup_le hCompl.K_le_M
      ((centralizerWithin_le_left (sigmaCore M) K).trans (sigmaCore_le M))
  have hKHallZ : IsHall piᶜ (K.subgroupOf Z) := by
    change IsHall piᶜ (K.subgroupOf (pTypeJoin M K))
    constructor
    · rw [MathlibSupport.natCard_subgroupOf_eq hJoinDirect.left_le]
      exact hKpi
    · rw [hJoinDirect.complement.symm.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hJoinDirect.right_le]
      simpa only [compl_compl] using hKspi
  have hKsHallZ : IsHall pi (Ks.subgroupOf Z) := by
    change IsHall pi ((pTypePartner M K).subgroupOf (pTypeJoin M K))
    constructor
    · rw [MathlibSupport.natCard_subgroupOf_eq hJoinDirect.right_le]
      exact hKspi
    · rw [hJoinDirect.complement.index_eq_card,
        MathlibSupport.natCard_subgroupOf_eq hJoinDirect.left_le]
      exact hKpi
  letI : IsMulCommutative Z := by
    dsimp only [Z]
    exact hEmbed.cyclicStructure.cyclic_join.isMulCommutative
  have hKnormalZ : (K.subgroupOf Z).Normal := by infer_instance
  have hKsnormalZ : (Ks.subgroupOf Z).Normal := by infer_instance
  have hOuterEq :
      FTsupport0 M \ FTsupport M = classSupportWithin M T := by
    apply Set.Subset.antisymm
    · intro x hx
      change x ∈ FTsupport0 M ∧ x ∉ FTsupport M at hx
      rcases hx.1 with hxSupport | hxMixed
      · exact (hx.2 hxSupport).elim
      · let y : G := primeSetComplementComponent pi x
        have hsM : primeSetComponent pi x ∈ M :=
          (Subgroup.zpowers_le.mpr hxMixed.1)
            (primeSetComponent_spec pi x).1
        have hyM : y ∈ M := by
          change (primeSetComponent pi x)⁻¹ * x ∈ M
          exact M.mul_mem (M.inv_mem hsM) hxMixed.1
        have hy1 : y ≠ 1 := by
          intro hyOne
          have hcomponent : primeSetComponent pi x = x := by
            simpa [y, hyOne] using primeSetComponent_mul_complement pi x
          apply hxMixed.2.1
          rw [← hcomponent]
          exact primeSetComponent_isPiNumber pi x
        let A : Subgroup G := Subgroup.zpowers y
        have hAM : A ≤ M := Subgroup.zpowers_le.mpr hyM
        have hApi : IsPiNumber piᶜ (Nat.card A) := by
          simpa [A, y, Nat.card_zpowers] using
            (primeSetComplementComponent_isPiNumber pi x)
        obtain ⟨a, hAKa, _hKaM, _hHallKa,
            _hfit, _hdiv, _htransport⟩ :=
          exists_ambient_isHall_map_conj_ge_of_isSolvable
            (K := M) (A := A) (H := K)
            hAM hCompl.K_le_M (mmax_sol hM) hApi hKHallM
        let e₀ : G ≃* G := MulAut.conj (a : G)
        let e : G ≃* G := e₀.symm
        change A ≤ K.map e₀.toMonoidHom at hAKa
        have hyKmap : y ∈ K.map e₀.toMonoidHom :=
          hAKa (Subgroup.mem_zpowers y)
        have hycK : e y ∈ K := by
          simpa [e] using Subgroup.mem_map_equiv.mp hyKmap
        have hyc1 : e y ≠ 1 := by
          intro hycOne
          apply hy1
          apply e.injective
          simpa using hycOne
        have hxcM : e x ∈ M := by
          have : (a : G)⁻¹ * x * (a : G) ∈ M :=
            M.mul_mem (M.mul_mem (M.inv_mem a.property) hxMixed.1) a.property
          simpa [e, e₀, MulAut.conj_apply] using this
        have hxy : Commute x y := by
          rw [← primeSetComponent_mul_complement pi x]
          exact (primeSetComponent_commute_complement pi x).mul_left
            (Commute.refl y)
        have hxyc : Commute (e x) (e y) := hxy.map e.toMonoidHom
        have hxcCent :
            e x ∈ centralizerWithin M (Subgroup.zpowers (e y)) := by
          refine ⟨hxcM, ?_⟩
          intro z hz
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          exact (hxyc.zpow_right n).symm.eq
        have hxcZ : e x ∈ Z := by
          change e x ∈ pTypeJoin M K
          rw [← hEmbed.cyclicStructure.centralizer_left hycK hyc1]
          exact hxcCent
        have horder : orderOf (e x) = orderOf x :=
          orderOf_injective e.toMonoidHom e.injective x
        have hxcNotK : e x ∉ K := by
          intro hxcK
          have hpiC : IsPiNumber piᶜ (orderOf (e x)) :=
            hKpi.of_dvd (by
              simpa using orderOf_dvd_natCard (⟨e x, hxcK⟩ : K))
          rw [horder] at hpiC
          exact hxMixed.2.2 hpiC
        have hxcNotKs : e x ∉ Ks := by
          intro hxcKs
          have hpiC : IsPiNumber pi (orderOf (e x)) :=
            hKspi.of_dvd (by
              simpa using orderOf_dvd_natCard (⟨e x, hxcKs⟩ : Ks))
          rw [horder] at hpiC
          exact hxMixed.2.1 hpiC
        have hxcT : e x ∈ T :=
          ⟨hxcZ, by
            rintro (hxcK | hxcKs)
            · exact hxcNotK hxcK
            · exact hxcNotKs hxcKs⟩
        refine ⟨e x, hxcT, (a : G)⁻¹, M.inv_mem a.property, ?_⟩
        change ((a : G)⁻¹)⁻¹ * e x * (a : G)⁻¹ = x
        dsimp only [e, e₀]
        simp [MulAut.conj_symm_apply]
        group
    · rintro x ⟨y, hyT, a, haM, rfl⟩
      change y ∈ Z ∧ y ∉ (K : Set G) ∪ (Ks : Set G) at hyT
      have hyNotPi : ¬ IsPiNumber pi (orderOf y) := by
        intro hyPi
        have hyKs : y ∈ Ks := mem_normalHall_of_order_support
          hJoinDirect.right_le hKsnormalZ hKsHallZ hyT.1 hyPi
        exact hyT.2 (Or.inr hyKs)
      have hyNotPiCompl : ¬ IsPiNumber piᶜ (orderOf y) := by
        intro hyPi
        have hyK : y ∈ K := mem_normalHall_of_order_support
          hJoinDirect.left_le hKnormalZ hKHallZ hyT.1 hyPi
        exact hyT.2 (Or.inl hyK)
      let e : G ≃* G := MulAut.conj a⁻¹
      have hconjM : a⁻¹ * y * a ∈ M :=
        M.mul_mem (M.mul_mem (M.inv_mem haM) (hZM hyT.1)) haM
      have horder : orderOf (e y) = orderOf y :=
        orderOf_injective e.toMonoidHom e.injective y
      have horderConj : orderOf (a⁻¹ * y * a) = orderOf y := by
        simpa [e, MulAut.conj_apply] using horder
      have hnotPi : ¬ IsPiNumber pi (orderOf (a⁻¹ * y * a)) := by
        rw [horderConj]
        exact hyNotPi
      have hnotPiCompl :
          ¬ IsPiNumber piᶜ (orderOf (a⁻¹ * y * a)) := by
        rw [horderConj]
        exact hyNotPiCompl
      have hconj0 : a⁻¹ * y * a ∈ FTsupport0 M := by
        change a⁻¹ * y * a ∈ FTsupport M ∪
          {z : G | z ∈ M ∧
            ¬ IsPiNumber (primeSupport (Nat.card (FTder M))) (orderOf z) ∧
            ¬ IsPiNumber (primeSupport (Nat.card (FTder M)))ᶜ (orderOf z)}
        exact Or.inr ⟨hconjM,
          by simpa [pi, D] using hnotPi,
          by simpa [pi, D] using hnotPiCompl⟩
      refine ⟨hconj0, ?_⟩
      intro hconjSupport
      simp only [FTsupport, ftSupport, Set.mem_iUnion] at hconjSupport
      rcases hconjSupport with ⟨z, _hzCore, hconjCent⟩
      have hconjPi : IsPiNumber pi (orderOf (a⁻¹ * y * a)) := by
        simpa [pi, D] using
          (order_supported_on_subgroup_card hconjCent.1.1)
      exact hnotPi hconjPi
  have hClassTI : IsNormalizedTI (classSupportWithin M T) ⊤ M :=
    normalizedTI_classSupportWithin hEmbed.normalizedTI hZM le_top
  exact ⟨hOuterEq, by simpa [hOuterEq] using hClassTI⟩

/-- `BGsection16.v: BGsummaryC`. -/
noncomputable def BGsummaryC
    {M U K : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : KappaComplement M U K)
    (hKne : K ≠ ⊥) :
    BGSummaryC M U K := by
  classical
  have hMP : M ∈ typePMaximalSubgroups (G := G) := by
    refine ⟨hM, ?_⟩
    intro hF
    exact hKne ((trivg_kappa hM hCompl.K_le_M hCompl.hall_K).2 hF)
  have hkappa := kappa_structure hM hCompl
  have hpstruct := Ptype_structure hMP hCompl.K_le_M hCompl.hall_K
  have hcyclics := Ptype_cyclics hMP hCompl.K_le_M hCompl.hall_K
  have hsummaryA := BGsummaryA hM hCompl
  let hExists := Ptype_embedding hMP hCompl.K_le_M hCompl.hall_K
  let Mstar : Subgroup G := Classical.choose hExists
  have hEmbed : PTypeEmbedding M K Mstar := Classical.choose_spec hExists
  have hPartnerEq : pTypePartner M K = kappaCentralizer M K := rfl
  have hJoinDirect :
      IsInternalDirectProductIn K (pTypePartner M K) (pTypeJoin M K) := by
    obtain ⟨k, hkne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hKne
    have hkneG : (k : G) ≠ 1 := by
      intro hk
      exact hkne (Subtype.ext hk)
    have hdirect := hsummaryA.centralizer_direct k.property hkneG
    change IsInternalDirectProductIn K (pTypePartner M K)
      (centralizerWithin M (Subgroup.zpowers (k : G))) at hdirect
    rw [hEmbed.cyclicStructure.centralizer_left k.property hkneG] at hdirect
    exact hdirect
  have hOuter := outerSupport_package hM hCompl hKne hEmbed hJoinDirect
    (sdprod_FTder hM hCompl)
  refine
    { U_abelian := hkappa.U_abelian_of_K_ne_bot hKne
      normalizer_U_not_le := normalizer_U_escapes hM hCompl hKne
      partner_cyclic := by
        change IsCyclic (kappaCentralizer M K)
        exact hcyclics.partner_cyclic
      partner_ne_bot := by
        simpa [hPartnerEq] using hcyclics.partner_ne_bot
      partner_le_Fcore := by
        simpa [hPartnerEq] using hcyclics.partner_le_Fcore
      Fcore_not_cyclic := hcyclics.Fcore_not_cyclic
      sigma_U_derived := hkappa.derived_decomposition hKne
      partner_le_secondDerived := by
        simpa [hPartnerEq] using hcyclics.partner_le_secondDerived
      Mstar := Mstar
      Mstar_typeP := hEmbed.Mstar_typeP
      doubleCentralizer := hEmbed.doubleCentralizer
      partner_le_Mstar := hEmbed.Kstar_le_Mstar
      partner_hall_kappa := hEmbed.Kstar_hall_kappa
      partner_unique := sigmaOvergroups_eq_embeddingWitness hKne hEmbed
      partner_rankOne_unique := by
        intro p hp X hX
        letI : Fact p.Prime := ⟨hp⟩
        change RankOneLineIn p (pTypeCentralizer M K) X at hX
        exact hpstruct.Kstar_line_unique hX
      K_rankOne_unique := hEmbed.rankOne_unique
      inf_eq_join := hEmbed.cyclicStructure.inf_eq_join
      join_direct := hJoinDirect
      join_cyclic := hEmbed.cyclicStructure.cyclic_join
      typeP2_or_partner_typeP2 := by
        rcases hEmbed.typeP2_prime with hM2 | hMstar2
        · exact Or.inl hM2.1
        · exact Or.inr hMstar2.1
      typeP_transitive := hEmbed.typeP_transitive
      join_difference_normalizedTI := hEmbed.normalizedTI
      outer_support_eq_classSupport := hOuter.1
      outer_support_normalizedTI := hOuter.2
      nontrivial_U_case := by
        intro hUne
        have hMP2 : M ∈ typeP2MaximalSubgroups (G := G) :=
          ⟨hMP, fun hMP1 ↦ hUne ((trivg_kappa_compl hM hCompl).2 hMP1)⟩
        have hTI :
            IsNormalizedTI (subgroupNonidentity (fittingWithin M)) ⊤ M := by
          by_contra hnotTI
          rcases nonTI_Fitting_facts hM hnotTI with hF | hP1
          · exact hMP.2 hF
          · exact hMP2.2 hP1.1
        have hCoreEq : Fitting_core M = sigmaCore M := by
          by_contra hne
          exact hUne (hsummaryA.nonnilpotent_case hne).1
        exact ⟨(hpstruct.typeP2 hMP2).card_K_prime, hTI,
          hCoreEq ▸ Fcore_sub_Fitting M⟩
      trivial_U_case := by
        intro hUbot
        have hMP1 : M ∈ typeP1MaximalSubgroups (G := G) :=
          (trivg_kappa_compl hM hCompl).1 hUbot
        rcases hEmbed.typeP2_prime with hM2 | hMstar2
        · exact (hM2.1.2 hMP1).elim
        · exact hMstar2.2 }

end

end Submission.OddOrder.BG.Section16
