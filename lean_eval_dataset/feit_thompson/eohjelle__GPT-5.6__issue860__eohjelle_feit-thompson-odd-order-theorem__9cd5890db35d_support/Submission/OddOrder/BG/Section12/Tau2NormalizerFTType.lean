import Submission.OddOrder.BG.Section12.SigmaNilpotent
import Submission.OddOrder.BG.Section12.AbelianTau2
import Submission.OddOrder.BG.Section12.AbelianTau2CyclicFactor
import Submission.OddOrder.BG.Section12.Tau2CoprimeCyclicSplit
import Submission.OddOrder.BG.Section12.Tau2SelectedSylowAssembly
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal
import Submission.OddOrder.MathlibSupport.SCNCentralizer
import Submission.OddOrder.MathlibSupport.SylowIntersection

/-!
# Bender--Glauberman Section 12: normalizers of `tau2` elements and Type F

This file ports `BGsection12.v`, lines 1463--2015: Lemma 12.11 and the
generalized form of Theorem 12.12.  Quotient orders are represented by
subgroup indices, as in the preceding Section 12 module.

The source proofs contain several long local arguments.  Lemma 12.11 and both
halves of Theorem 12.12 are carried out in this file using the existing
Section 12 interfaces.  The cyclic Sylow factors used in the abelian branch
are constructed prime by prime and then assembled with a complementary Hall
subgroup.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped IsMulCommutative Pointwise

noncomputable section

universe u

/-! ## Hall and normal-containment adapters -/

/-- A `pi`-subgroup of a finite group lies in a normal `pi`-Hall
subgroup. -/
private theorem le_normal_isHall_of_isPiNumber_12_11
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {C K L : Subgroup G}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    (hLC : L ≤ C) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa [KC] using hKnormal
  have hcop : (Nat.card L).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    have hpPi : p ∈ pi := hLpi hp hpL
    have hpNotPi : p ∈ piᶜ := hKHall.isPiNumber_index hp hpIndex
    exact hpNotPi hpPi
  intro x hxL
  let xC : C := ⟨x, hLC hxL⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderL : orderOf (qC xC) ∣ Nat.card L :=
    (orderOf_map_dvd qC xC).trans (by
      simpa [xC] using L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (qC xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (qC xC)
  have hone : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp hone
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- A Sylow subgroup of a Hall subgroup maps to a Sylow subgroup of the
ambient finite group. -/
private theorem exists_sylow_eq_map_of_sylow_hall_12_11
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {H : Subgroup K} (hH : IsHall pi H) (hpPi : p ∈ pi)
    (P : Sylow p H) :
    ∃ Q : Sylow p K,
      (Q : Subgroup K) = (P : Subgroup H).map H.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let S : Subgroup K := (P : Subgroup H).map H.subtype
  have hSp : IsPGroup p S := P.isPGroup'.map H.subtype
  have hpHindex : ¬ p ∣ H.index := by
    intro hpIndex
    exact hH.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P.not_dvd_index hpHindex
  exact ⟨hSp.toSylow hpSindex, rfl⟩

/-- Transport a selected Sylow subgroup through a Hall inclusion while
preserving its carrier in the common ambient group. -/
private theorem exists_sylow_of_hall_with_same_ambient_12_12
    {G : Type u} [Group G] [Finite G]
    {H K : Subgroup G} {pi : Set ℕ} {p : ℕ}
    (hp : p.Prime) (hHK : H ≤ K)
    (hHall : IsHall pi (H.subgroupOf K)) (hpPi : p ∈ pi)
    (P : Sylow p H) :
    ∃ Q : Sylow p K, ambientSylow K Q = ambientSylow H P := by
  letI : Fact p.Prime := ⟨hp⟩
  let HK : Subgroup K := H.subgroupOf K
  let e : H ≃* HK := (Subgroup.subgroupOfEquivOfLe hHK).symm
  let PHK : Sylow p HK :=
    P.mapSurjective (f := e.toMonoidHom) e.surjective
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_eq_map_of_sylow_hall_12_11 hp hHall hpPi PHK
  refine ⟨Q, ?_⟩
  change (Q : Subgroup K).map K.subtype =
    (P : Subgroup H).map H.subtype
  rw [hQ, Subgroup.map_map]
  simp only [PHK, Sylow.coe_mapSurjective, Subgroup.map_map]
  apply congrArg (fun f : H →* G ↦ (P : Subgroup H).map f)
  ext x
  rfl

/-- Move an elementary-abelian rank witness into an ambiently represented
Sylow subgroup. -/
private theorem exists_elementaryAbelian_le_ambientSylow_12_12
    {G : Type u} [Group G] [Finite G]
    {H Q : Subgroup G} {p n : ℕ} [Fact p.Prime]
    (hQH : IsSylowSubgroupOf p Q H)
    (hRank : HasElementaryAbelianRankAtLeast p n H) :
    ∃ A : Subgroup G, A ≤ Q ∧
      IsElementaryAbelianOfRank p n A := by
  classical
  rcases hQH with ⟨P, hQP⟩
  rcases hRank with ⟨A, hAH, hA⟩
  let AH : Subgroup H := A.subgroupOf H
  have hAHrank : IsElementaryAbelianOfRank p n AH :=
    hA.subgroupOf hAH
  obtain ⟨R, hAHR⟩ := hAHrank.isPGroup.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H R P
  let B : Subgroup H :=
    AH.map (MulAut.conj h).toMonoidHom
  have hRB :
      (R : Subgroup H).map (MulAut.conj h).toMonoidHom =
        (P : Subgroup H) := by
    change MulAut.conj h • (R : Subgroup H) = (P : Subgroup H)
    rw [← Sylow.coe_subgroup_smul, hh]
  have hBP : B ≤ (P : Subgroup H) :=
    (Subgroup.map_mono hAHR).trans_eq hRB
  let BG : Subgroup G := B.map H.subtype
  refine ⟨BG, ?_, ?_⟩
  · rw [hQP]
    exact Subgroup.map_mono hBP
  · exact
      (hAHrank.map_of_injective (MulAut.conj h).toMonoidHom
        (MulAut.conj h).injective).map_of_injective
          H.subtype H.subtype_injective

/-- A characteristic subgroup of a subgroup is normalized by the ambient
normalizer. -/
private theorem characteristic_map_subtype_le_normalizer_12_11
    {K : Type*} [Group K] (S : Subgroup K)
    (R : Subgroup S) [R.Characteristic] :
    Subgroup.normalizer (S : Set K) ≤
      Subgroup.normalizer (R.map S.subtype : Set K) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl
      g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (S : Set K) :=
      (Subgroup.normalizer (S : Set K)).inv_mem hg
    have h := characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using h

/-- Conjugating a subgroup by one of its own elements fixes it. -/
private theorem map_conj_eq_self_of_mem_12_11
    {K : Type*} [Group K] (S : Subgroup K) {g : K} (hg : g ∈ S) :
    S.map (MulAut.conj g).toMonoidHom = S := by
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (Subgroup.le_normalizer hg)

/-- In a cyclic finite `p`-group, a subgroup of order `p` meets every
nontrivial subgroup.  This is the direct-product dichotomy used at the end
of Lemma 12.11(c). -/
private theorem disjoint_right_eq_bot_of_cyclic_pgroup_12_11
    {K : Type u} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {Q A B : Subgroup K}
    (hQp : IsPGroup p Q) (hQcyclic : IsCyclic Q)
    (hAQ : A ≤ Q) (hAcard : Nat.card A = p)
    (hBQ : B ≤ Q) (hdis : Disjoint A B) :
    B = ⊥ := by
  by_contra hBne
  have hAne : A ≠ ⊥ := by
    intro hA
    have : p = 1 := by simpa [hA] using hAcard.symm
    exact (Fact.out : p.Prime).ne_one this
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hAne
    apply le_bot_iff.mp
    rw [← hQ]
    exact hAQ
  have hBp : IsPGroup p B :=
    hQp.of_injective (Subgroup.inclusion hBQ)
      (Subgroup.inclusion_injective hBQ)
  have hpB : p ∣ Nat.card B :=
    hBp.card_eq_or_dvd.resolve_left
      ((B.one_lt_card_iff_ne_bot.mpr hBne).ne')
  obtain ⟨b, hbOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := B) p hpB
  let X : Subgroup K := (Subgroup.zpowers b).map B.subtype
  have hXB : X ≤ B := Subgroup.map_subtype_le _
  have hXcard : Nat.card X = p := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective B.subtype_injective,
      Nat.card_zpowers, hbOrder]
  have hXQ : X ≤ Q := hXB.trans hBQ
  let AQ : Subgroup Q := A.subgroupOf Q
  let XQ : Subgroup Q := X.subgroupOf Q
  letI : IsCyclic Q := hQcyclic
  have hQcard : Nat.card Q ≠ 1 := by
    intro hcard
    exact hQne (Subgroup.card_eq_one.mp hcard)
  have hOmegaCard : Nat.card (omegaOne p Q) = p :=
    card_omegaOne_of_isCyclic_isPGroup Fact.out hQp hQcard
  have hArank : IsElementaryAbelianOfRank p 1 A :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hAcard
  have hXrank : IsElementaryAbelianOfRank p 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hAQomega : AQ ≤ omegaOne p Q := by
    intro a ha
    apply mem_omegaOne_of_pow_eq_one p
    apply Q.subtype_injective
    change ((a : Q) : K) ^ p = 1
    exact congrArg Subtype.val
      (hArank.pow_eq_one ⟨((a : Q) : K), ha⟩)
  have hXQomega : XQ ≤ omegaOne p Q := by
    intro x hx
    apply mem_omegaOne_of_pow_eq_one p
    apply Q.subtype_injective
    change ((x : Q) : K) ^ p = 1
    exact congrArg Subtype.val
      (hXrank.pow_eq_one ⟨((x : Q) : K), hx⟩)
  have hAQeq : AQ = omegaOne p Q := by
    apply Subgroup.eq_of_le_of_card_ge hAQomega
    rw [hOmegaCard,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hAQ,
      hAcard]
  have hXQeq : XQ = omegaOne p Q := by
    apply Subgroup.eq_of_le_of_card_ge hXQomega
    rw [hOmegaCard,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hXQ,
      hXcard]
  have hAX : A = X := by
    have hAQXQ : AQ = XQ := hAQeq.trans hXQeq.symm
    have hmapped := congrArg (Subgroup.map Q.subtype) hAQXQ
    simpa only [AQ, XQ, Subgroup.map_subgroupOf_eq_of_le hAQ,
      Subgroup.map_subgroupOf_eq_of_le hXQ] using hmapped
  have hAleB : A ≤ B := hAX.le.trans hXB
  apply hAne
  apply le_bot_iff.mp
  intro a ha
  exact hdis.le_bot ⟨ha, hAleB ha⟩

/-! ## Lemma 12.11 -/

/-- The Sylow data in clause (c) of `primes_norm_tau2Elem`.

The normality assertion is made after viewing the ambient Sylow subgroup as
a subgroup of `Mstar`.  This is the direct Lean rendering of source notation
`P <| Mstar`. -/
structure PrimesNormTau2ElemCommonPrime
    {G : Type u} [Group G] [Finite G]
    (Mstar : Subgroup G) (p q : ℕ) where
  q_mem_tau2 : q ∈ tau2Primes Mstar
  pSylow : Sylow p G
  pSylow_le : (pSylow : Subgroup G) ≤ Mstar
  pSylow_normal :
    ((pSylow : Subgroup G).subgroupOf Mstar).Normal
  qSylow : Sylow q G
  qSylow_le : (qSylow : Subgroup G) ≤ Mstar
  qSylow_abelian : IsMulCommutative (qSylow : Subgroup G)

/-- The three source clauses of Bender--Glauberman Lemma 12.11.

The order of `E / C_E(A)` is the index of `C_E(A)` in `E`. -/
structure PrimesNormTau2ElemConclusion
    {G : Type u} [Group G] [Finite G]
    (M E A Mstar : Subgroup G) (p : ℕ) where
  tau2_classification :
    ∀ {q : ℕ}, q ∈ tau2Primes M →
      q ∈ sigmaPrimes Mstar ∧ q ∉ betaPrimes Mstar
  quotient_tau12 :
    IsPiNumber (tau1Primes Mstar ∪ tau2Primes Mstar)
      ((centralizerWithin E A).subgroupOf E).index
  common_prime_structure :
    ∀ {q : ℕ},
      q ∈ primeSupport ((centralizerWithin E A).subgroupOf E).index →
      q ∈ primeSupport (Nat.card (centralizerWithin E A)) →
        PrimesNormTau2ElemCommonPrime Mstar p q

/-- `BGsection12.v: primes_norm_tau2Elem`, clause (a) of Lemma 12.11.

The proof follows the source `part_a`: put `A` in a `tau2(M)`-Hall subgroup
of `E`, use its abelianness to manufacture a rank-two subgroup of
`C_G(A)` at every `q ∈ tau2(M)`, and rule out `q ∈ tau2(Mstar)` with the
regularity conclusion of `tau2_context`. -/
theorem primes_norm_tau2Elem_tau2_classification
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A Mstar : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hMstar : Mstar ∈ minSimple_max_groups (G := G))
    (hNormalizer : Subgroup.normalizer (A : Set G) ≤ Mstar) :
    ∀ {q : ℕ}, q ∈ tau2Primes M →
      q ∈ sigmaPrimes Mstar ∧ q ∉ betaPrimes Mstar := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  have hAMstar : A ≤ Mstar :=
    Subgroup.le_normalizer.trans hNormalizer
  have hpSigmaStar : p ∈ sigmaPrimes Mstar := by
    rcases prime_class_mmax_norm hMstar hA.isPGroup hNormalizer with
      hpSigma | hpTauStar
    · exact hpSigma
    · have hApi : IsPiNumber (sigmaPrimes Mstar)ᶜ (Nat.card A) :=
        hA.isPGroup.isPiNumber_natCard hpTauStar.2.1
      obtain ⟨F, hAF, hFMstar, hHallF⟩ :=
        exists_ambient_isHall_ge_of_isSolvable hAMstar
          (mmax_sol hMstar) (sigmaPrimes Mstar)ᶜ hApi
      have hTauStar := tau2_compl_context hMstar hFMstar hHallF
        hpTauStar hAF hA
      exact (hTauStar.normalizer_not_le_M hNormalizer).elim
  have hApiTau2 : IsPiNumber (tau2Primes M) (Nat.card A) :=
    hA.isPGroup.isPiNumber_natCard hpTau
  obtain ⟨E₂, hAE₂, hE₂E, hHallE₂⟩ :=
    exists_ambient_isHall_ge_of_isSolvable hAE
      (sigma_compl_sol hEM hHallE) (tau2Primes M) hApiTau2
  have hE₂comm : IsMulCommutative E₂ :=
    tau2_compl_abelian hM hEM hHallE hE₂E hHallE₂
  intro q hqTau
  letI : Fact q.Prime := ⟨hqTau.1⟩
  have hqNotBetaTop : q ∉ betaPrimes (⊤ : Subgroup G) :=
    (tau2_not_beta hM hqTau).1
  have hqNotBetaStar : q ∉ betaPrimes Mstar := by
    intro hqBetaStar
    have hqPair :
        q ∈ sigmaPrimes Mstar ∩ betaPrimes (⊤ : Subgroup G) := by
      rw [predI_sigma_beta hMstar]
      exact hqBetaStar
    exact hqNotBetaTop hqPair.2

  obtain ⟨B₀, hB₀E, _hB₀M, hB₀⟩ :=
    ex_tau2Elem hEM hHallE hqTau
  let E₂E : Subgroup E := E₂.subgroupOf E
  let P : Sylow q E₂E := Classical.choice Sylow.nonempty
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_eq_map_of_sylow_hall_12_11
      hqTau.1 hHallE₂ hqTau P
  obtain ⟨e, he⟩ :=
    exists_conjugate_le_sylow_map Q hB₀E hB₀.isPGroup
  let B : Subgroup G :=
    B₀.map (MulAut.conj (e : G)).toMonoidHom
  have hBQ : B ≤ (Q : Subgroup E).map E.subtype := by
    rintro b ⟨b₀, hb₀, rfl⟩
    exact he b₀ hb₀
  have hQE₂ : (Q : Subgroup E).map E.subtype ≤ E₂ := by
    rw [hQ]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨w, hw, rfl⟩
    exact w.property
  have hBE₂ : B ≤ E₂ := hBQ.trans hQE₂
  have hB : IsElementaryAbelianOfRank q 2 B := by
    dsimp only [B]
    exact hB₀.map_of_injective
      (MulAut.conj (e : G)).toMonoidHom
      (MulAut.conj (e : G)).injective
  have hBcentA : B ≤ Subgroup.centralizer (A : Set G) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp hE₂comm
        ⟨a, hAE₂ ha⟩ ⟨b, hBE₂ hb⟩)
  have hAcentB : A ≤ Subgroup.centralizer (B : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val
      (isMulCommutative_iff.mp hE₂comm
        ⟨b, hBE₂ hb⟩ ⟨a, hAE₂ ha⟩)
  have hBH : B ≤ Mstar :=
    hBcentA.trans
      ((Subgroup.centralizer_le_normalizer (A : Set G)).trans
        hNormalizer)
  have hqSigmaStar : q ∈ sigmaPrimes Mstar := by
    by_contra hqNotSigma
    have hqTauStar : q ∈ tau2Primes Mstar :=
      ⟨hqTau.1, hqNotSigma, ⟨B, hBH, hB⟩, fun hRankThree ↦
        hqNotSigma (alpha_sub_sigma hMstar
          ⟨hqTau.1, hRankThree⟩)⟩
    have hTauStar := tau2_context hMstar hqTauStar hBH hB
    have hASigma : A ≤ sigmaCore Mstar := by
      apply le_normal_isHall_of_isPiNumber_12_11
        (sigmaCore_normal Mstar) (Msigma_Hall hMstar) hAMstar
      exact hA.isPGroup.isPiNumber_natCard hpSigmaStar
    have hAcentWithin :
        A ≤ centralizerWithin (sigmaCore Mstar) B :=
      le_inf hASigma hAcentB
    apply hA.ne_bot
    apply le_antisymm
    · rw [← hTauStar.centralizerWithin_eq_bot]
      exact hAcentWithin
    · exact bot_le
  exact ⟨hqSigmaStar, hqNotBetaStar⟩

/-- The prime divisors of a sigma complement belong to one of the three
tau classes. -/
private theorem primeSupport_sigma_complement_subset_tau_12_11
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    primeSupport (Nat.card E) ⊆
      tau1Primes M ∪ tau2Primes M ∪ tau3Primes M := by
  intro r hrE
  have hr : r.Prime := hrE.1
  letI : Fact r.Prime := ⟨hr⟩
  have hrMcard : r ∣ Nat.card M :=
    hrE.2.trans (Subgroup.card_dvd_of_le hEM)
  have hrNotSigma : r ∉ sigmaPrimes M := by
    have hrEsub : r ∣ Nat.card (E.subgroupOf M) := by
      simpa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEM]
        using hrE.2
    exact hHall.isPiNumber_card hr hrEsub
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := M) r hrMcard
  let X : Subgroup G := (Subgroup.zpowers x).map M.subtype
  have hXcard : Nat.card X = r := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective M.subtype_injective,
      Nat.card_zpowers, hxorder]
  have hXrank : IsElementaryAbelianOfRank r 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hRankOne : HasElementaryAbelianRankAtLeast r 1 M :=
    ⟨X, Subgroup.map_subtype_le _, hXrank⟩
  by_cases hRankTwo : HasElementaryAbelianRankAtLeast r 2 M
  · have hNoRankThree :
        ¬ HasElementaryAbelianRankAtLeast r 3 M := by
      intro hRankThree
      exact hrNotSigma (alpha_sub_sigma hM ⟨hr, hRankThree⟩)
    exact Or.inl (Or.inr
      ⟨hr, hrNotSigma, hRankTwo, hNoRankThree⟩)
  · by_cases hrDer : r ∣ Nat.card (_root_.commutator M)
    · exact Or.inr
        ⟨hr, hrNotSigma, hRankOne, hRankTwo, hrDer⟩
    · exact Or.inl (Or.inl
        ⟨hr, hrNotSigma, hRankOne, hRankTwo, hrDer⟩)

/-- `BGsection12.v: primes_norm_tau2Elem`, clause (c) of Lemma 12.11.

The proof uses Frattini's argument in `N_G(A)`.  A characteristic subgroup
of order `q` in the cyclic Sylow subgroup of `C_G(A)` selects a maximal
overgroup `L`.  Parts (a) and (b), sigma transitivity, and the two `tau2`
structure theorems then identify `L` with `Mstar`, make the ambient
`p`-Sylow normal there, and force the ambient `q`-Sylow to be abelian. -/
private theorem exists_primes_norm_tau2Elem_common_prime_structure
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A Mstar : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hMstar : Mstar ∈ minSimple_max_groups (G := G))
    (hNormalizer : Subgroup.normalizer (A : Set G) ≤ Mstar)
    (hfactor : Tau1CentralizerFactor M E A)
    (hclassification : ∀ {r : ℕ}, r ∈ tau2Primes M →
      r ∈ sigmaPrimes Mstar ∧ r ∉ betaPrimes Mstar)
    (hquotientTransfer : ∀ {L : Subgroup G},
      L ∈ minSimple_max_groups (G := G) →
      Subgroup.normalizer (A : Set G) ≤ L →
      (∀ {r : ℕ}, r ∈ tau2Primes M →
        r ∈ sigmaPrimes L ∧ r ∉ betaPrimes L) →
      IsPiNumber (tau1Primes L ∪ tau2Primes L)
        ((centralizerWithin E A).subgroupOf E).index) :
    ∀ {q : ℕ},
      q ∈ primeSupport ((centralizerWithin E A).subgroupOf E).index →
      q ∈ primeSupport (Nat.card (centralizerWithin E A)) →
        Nonempty (PrimesNormTau2ElemCommonPrime Mstar p q) := by
  classical
  intro q hqIndex hqCentral
  letI : Fact p.Prime := ⟨hpTau.1⟩
  letI : Fact q.Prime := ⟨hqIndex.1⟩
  let N : Subgroup G := Subgroup.normalizer (A : Set G)
  let C : Subgroup G := Subgroup.centralizer (A : Set G)
  have hTau := tau2_compl_context hM hEM hHallE hpTau hAE hA
  have hCEq : centralizerWithin E A = C := by
    apply le_antisymm inf_le_right
    intro x hx
    exact ⟨hTau.centralizer_le_E hx, hx⟩
  have hqTau1M : q ∈ tau1Primes M :=
    hfactor.quotient_isPiNumber hqIndex.1 hqIndex.2
  have hqCcard : q ∣ Nat.card C := by
    rw [hCEq] at hqCentral
    exact hqCentral.2

  let CN : Subgroup N := centralizerInNormalizer A
  have hqCNcard : q ∣ Nat.card CN := by
    have hcard : Nat.card CN = Nat.card C :=
      Nat.card_congr (centralizerInNormalizerEquiv A).toEquiv
    rwa [hcard]
  let RN : Sylow q CN := Classical.choice Sylow.nonempty
  have hRNne : (RN : Subgroup CN) ≠ ⊥ :=
    RN.ne_bot_of_dvd_card hqCNcard
  let Rₙ : Subgroup N := (RN : Subgroup CN).map CN.subtype
  let R : Subgroup G := Rₙ.map N.subtype
  have hRₙp : IsPGroup q Rₙ := RN.isPGroup'.map CN.subtype
  have hRp : IsPGroup q R := hRₙp.map N.subtype
  have hRₙne : Rₙ ≠ ⊥ :=
    (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (RN : Subgroup CN) CN.subtype_injective)).mpr hRNne
  have hRC : R ≤ C := by
    rintro _ ⟨r, hr, rfl⟩
    change (r : G) ∈ C
    exact Subgroup.map_subtype_le (RN : Subgroup CN) hr
  have hRE : R ≤ E := hRC.trans hTau.centralizer_le_E
  have hRcyclic : IsCyclic R := by
    apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hRp (mFT_odd R)).mpr
    rintro ⟨X, hX⟩
    let XG : Subgroup G := X.map R.subtype
    apply hqTau1M.2.2.2.1
    exact ⟨XG,
      (Subgroup.map_subtype_le X).trans (hRE.trans hEM),
      hX.map_of_injective R.subtype R.subtype_injective⟩
  have hRₙcyclic : IsCyclic Rₙ := by
    let eR : Rₙ ≃* R :=
      Rₙ.equivMapOfInjective N.subtype N.subtype_injective
    letI : IsCyclic R := hRcyclic
    exact isCyclic_of_surjective eR.symm eR.symm.surjective
  letI : IsCyclic Rₙ := hRₙcyclic
  let Q₀N : Subgroup N := (omegaOne q Rₙ).map Rₙ.subtype
  let Q₀ : Subgroup G := Q₀N.map N.subtype
  have hRₙcard : Nat.card Rₙ ≠ 1 := by
    intro hcard
    exact hRₙne (Subgroup.card_eq_one.mp hcard)
  have hQ₀Ncard : Nat.card Q₀N = q := by
    dsimp only [Q₀N]
    rw [Subgroup.card_map_of_injective Rₙ.subtype_injective]
    exact card_omegaOne_of_isCyclic_isPGroup
      Fact.out hRₙp hRₙcard
  have hQ₀card : Nat.card Q₀ = q := by
    dsimp only [Q₀]
    rw [Subgroup.card_map_of_injective N.subtype_injective]
    exact hQ₀Ncard
  have hQ₀rank : IsElementaryAbelianOfRank q 1 Q₀ :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hQ₀card
  have hQ₀p : IsPGroup q Q₀ := hQ₀rank.isPGroup
  have hQ₀ne : Q₀ ≠ ⊥ := hQ₀rank.ne_bot
  have hQ₀R : Q₀ ≤ R := by
    dsimp only [Q₀, Q₀N, R]
    exact Subgroup.map_mono (Subgroup.map_subtype_le _)
  have hQ₀C : Q₀ ≤ C := hQ₀R.trans hRC

  have hNQ₀proper : Subgroup.normalizer (Q₀ : Set G) < ⊤ :=
    mFT_norm_proper Q₀ hQ₀ne (mFT_pgroup_proper Q₀ hQ₀p)
  obtain ⟨L, hL, hNQ₀L⟩ :=
    mmax_exists (Subgroup.normalizer (Q₀ : Set G)) hNQ₀proper
  have hCQ₀L : Subgroup.centralizer (Q₀ : Set G) ≤ L :=
    (Subgroup.centralizer_le_normalizer (Q₀ : Set G)).trans hNQ₀L
  have hAL : A ≤ L := by
    exact (Subgroup.le_centralizer_iff.mp hQ₀C).trans hCQ₀L
  have hCL : C ≤ L := (p2Elem_mmax hL hAL hA).1

  have hCharNorm :
      Subgroup.normalizer (Rₙ : Set N) ≤
        Subgroup.normalizer (Q₀N : Set N) := by
    simpa only [Q₀N] using
      characteristic_map_subtype_le_normalizer_12_11
        Rₙ (omegaOne q Rₙ)
  have hFrattini :
      Subgroup.normalizer (Rₙ : Set N) ⊔ CN = ⊤ := by
    simpa only [Rₙ] using RN.normalizer_sup_eq_top
  let LN : Subgroup N := L.comap N.subtype
  have hNormRₙLN : Subgroup.normalizer (Rₙ : Set N) ≤ LN := by
    intro x hx
    have hxQ₀N : x ∈ Subgroup.normalizer (Q₀N : Set N) :=
      hCharNorm hx
    have hxQ₀ : (x : G) ∈ Subgroup.normalizer (Q₀ : Set G) := by
      exact Subgroup.le_normalizer_map N.subtype
        ⟨x, hxQ₀N, rfl⟩
    exact hNQ₀L hxQ₀
  have hCNLN : CN ≤ LN := by
    intro x hx
    change (x : G) ∈ L
    exact hCL hx
  have hNL : N ≤ L := by
    have htopLN : (⊤ : Subgroup N) ≤ LN := by
      rw [← hFrattini]
      exact sup_le hNormRₙLN hCNLN
    intro x hx
    exact htopLN (show (⟨x, hx⟩ : N) ∈ (⊤ : Subgroup N) by simp)

  have hclassificationL : ∀ {r : ℕ}, r ∈ tau2Primes M →
      r ∈ sigmaPrimes L ∧ r ∉ betaPrimes L :=
    primes_norm_tau2Elem_tau2_classification hM hEM hHallE hpTau
      hAE hA hL hNL
  have hquotientL :
      IsPiNumber (tau1Primes L ∪ tau2Primes L)
        ((centralizerWithin E A).subgroupOf E).index :=
    hquotientTransfer hL hNL hclassificationL
  have hqTau2L : q ∈ tau2Primes L := by
    rcases prime_class_mmax_norm hL hQ₀p hNQ₀L with hqSigma | hqTau
    · rcases hquotientL hqIndex.1 hqIndex.2 with hq1 | hq2
      · exact (hq1.2.1 hqSigma).elim
      · exact (hq2.2.1 hqSigma).elim
    · exact hqTau

  have hQ₀E : Q₀ ≤ E := hQ₀C.trans hTau.centralizer_le_E
  let Q₀E : Subgroup E := Q₀.subgroupOf E
  have hQ₀Ep : IsPGroup q Q₀E := by
    exact hQ₀p.of_equiv
      (Subgroup.subgroupOfEquivOfLe hQ₀E).symm
  obtain ⟨QE, hQ₀QE⟩ := hQ₀Ep.exists_le_sylow
  let Q : Subgroup G := (QE : Subgroup E).map E.subtype
  have hQE : Q ≤ E := Subgroup.map_subtype_le _
  have hQq : IsPGroup q Q := QE.isPGroup'.map E.subtype
  have hQ₀Q : Q₀ ≤ Q := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hQ₀E]
    exact Subgroup.map_mono hQ₀QE
  have hQcyclic : IsCyclic Q := by
    apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hQq (mFT_odd Q)).mpr
    rintro ⟨X, hX⟩
    let XG : Subgroup G := X.map Q.subtype
    apply hqTau1M.2.2.2.1
    exact ⟨XG,
      (Subgroup.map_subtype_le X).trans (hQE.trans hEM),
      hX.map_of_injective Q.subtype Q.subtype_injective⟩
  have hQcomm : IsMulCommutative Q := by
    letI : IsCyclic Q := hQcyclic
    infer_instance
  have hQcentQ₀ : Q ≤ Subgroup.centralizer (Q₀ : Set G) := by
    apply Subgroup.le_centralizer_iff.mp
    exact hQ₀Q.trans
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hQcomm)
  have hQL : Q ≤ L := hQcentQ₀.trans hCQ₀L
  have hQpi : IsPiNumber (sigmaPrimes L)ᶜ (Nat.card Q) :=
    hQq.isPiNumber_natCard hqTau2L.2.1
  obtain ⟨F, hQF, hFL, hHallF⟩ :=
    exists_ambient_isHall_ge_of_isSolvable hQL
      (mmax_sol hL) (sigmaPrimes L)ᶜ hQpi
  obtain ⟨B, hBF, _hBL, hB⟩ := ex_tau2Elem hFL hHallF hqTau2L
  have hpSigmaL : p ∈ sigmaPrimes L := (hclassificationL hpTau).1
  have hpSigmaStar : p ∈ sigmaPrimes Mstar :=
    (hclassification hpTau).1
  have hAMstar : A ≤ Mstar := Subgroup.le_normalizer.trans hNormalizer
  have hComplL := tau2_compl_context hL hFL hHallF hqTau2L hBF hB
  have hconj : ∃ g : G,
      Mstar = L.map (MulAut.conj g).toMonoidHom := by
    by_contra hnot
    push_neg at hnot
    have hdis := hComplL.disjoint_sigma_of_nonconj hMstar hnot
    exact Set.disjoint_left.mp hdis.2 hpSigmaL hpSigmaStar
  have hLMstar : L = Mstar := by
    have htrans := (sigma_group_trans hL hpSigmaL hA.isPGroup).2.1
    obtain ⟨c, hcC, hc⟩ := htrans
      ⟨⟨1, (map_conj_eq_self_of_mem_12_11 L L.one_mem).symm⟩, hAL⟩
      ⟨hconj, hAMstar⟩
    have hcL : c ∈ L := hCL hcC
    rw [map_conj_eq_self_of_mem_12_11 L hcL] at hc
    exact hc.symm

  let PL : Sylow p L := Classical.choice Sylow.nonempty
  obtain ⟨PG, hPG⟩ := sigma_Sylow_G hL hpSigmaL PL
  have hPGL : (PG : Subgroup G) ≤ L := by
    rw [hPG]
    exact Subgroup.map_subtype_le _
  let PM : Subgroup L := (PG : Subgroup G).subgroupOf L
  let SM : Subgroup L := (sigmaCore L).subgroupOf L
  have hPGSigma : (PG : Subgroup G) ≤ sigmaCore L := by
    apply le_normal_isHall_of_isPiNumber_12_11
      (sigmaCore_normal L) (Msigma_Hall hL) hPGL
    exact PG.isPGroup'.isPiNumber_natCard hpSigmaL
  have hPMSM : PM ≤ SM := by
    intro x hx
    exact hPGSigma hx
  have hPMEq : PM = (PL : Subgroup L) := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hPGL]
    exact hPG
  let PS : Subgroup SM := PM.subgroupOf SM
  have hPSp : IsPGroup p PS := by
    let ePM : PM ≃* (PG : Subgroup G) :=
      Subgroup.subgroupOfEquivOfLe hPGL
    have hPMp : IsPGroup p PM := PG.isPGroup'.of_equiv ePM.symm
    let ePS : PS ≃* PM := Subgroup.subgroupOfEquivOfLe hPMSM
    exact hPMp.of_equiv ePS.symm
  have hpPSindex : ¬ p ∣ PS.index := by
    intro hpIndex
    apply PL.not_dvd_index
    have hpRel : p ∣ PM.relIndex SM := by
      change p ∣ (PM.subgroupOf SM).index
      exact hpIndex
    have hpPMindex : p ∣ PM.index :=
      hpRel.trans (Subgroup.relIndex_dvd_index_of_le hPMSM)
    rw [hPMEq] at hpPMindex
    exact hpPMindex
  let PSL : Sylow p SM := hPSp.toSylow hpPSindex
  have hSMnil : Group.IsNilpotent SM := by
    let eSM : SM ≃* sigmaCore L :=
      Subgroup.subgroupOfEquivOfLe (sigmaCore_le L)
    letI : Group.IsNilpotent (sigmaCore L) := tau2_Msigma_nil hL hqTau2L
    exact Group.nilpotent_of_mulEquiv eSM.symm
  have hPScore : pCore p SM = PS := by
    letI : Group.IsNilpotent SM := hSMnil
    simpa [PSL] using pCore_eq_sylow_of_isNilpotent PSL
  have hPSchar : PS.Characteristic := by
    rw [← hPScore]
    infer_instance
  have hSMnormal : SM.Normal := by
    simpa [SM] using sigmaCore_normal L
  letI : SM.Normal := hSMnormal
  letI : PS.Characteristic := hPSchar
  have hPMnormal : PM.Normal := by
    have : (PS.map SM.subtype).Normal := inferInstance
    simpa [PS, Subgroup.map_subgroupOf_eq_of_le hPMSM] using this

  obtain ⟨Q₁, hQQ₁⟩ := hQq.exists_le_sylow
  have hQ₁L : (Q₁ : Subgroup G) ≤ L := by
    by_cases hQ₁comm : IsMulCommutative (Q₁ : Subgroup G)
    · have hQ₀Q₁ : Q₀ ≤ (Q₁ : Subgroup G) :=
        hQ₀Q.trans hQQ₁
      have hQ₁centQ₀ :
          (Q₁ : Subgroup G) ≤ Subgroup.centralizer (Q₀ : Set G) := by
        apply Subgroup.le_centralizer_iff.mp
        exact hQ₀Q₁.trans
          (Subgroup.le_centralizer_iff_isMulCommutative.mpr hQ₁comm)
      exact hQ₁centQ₀.trans hCQ₀L
    · have hnon := nonabelian_tau2 hL hFL hHallF hqTau2L
          hBF hB Q₁.isPGroup' hQ₁comm
      let A₀ : Subgroup G := centralizerWithin B (sigmaCore L)
      have hQ₀line : RankOneLineIn q F Q₀ :=
        ⟨hQ₀Q.trans hQF, hQ₀rank⟩
      have hQ₀A₀ : Q₀ = A₀ := by
        by_contra hne
        exact (hnon.rankOne_control Q₀ hQ₀line hne).2
          hCQ₀L
      obtain ⟨E₀, hsd, _hreg⟩ := hnon.exists_complement
      let J : Subgroup G := E₀ ⊓ Q
      have hA₀Q : A₀ ≤ Q := hQ₀A₀ ▸ hQ₀Q
      have hQeq : Q = A₀ ⊔ J := by
        apply le_antisymm
        · intro x hxQ
          let xF : F := ⟨x, hQF hxQ⟩
          obtain ⟨⟨a, e⟩, hae⟩ := hsd.2.2.2.2 xF
          have haeG : (a : G) * (e : G) = x :=
            congrArg Subtype.val hae
          have heQ : (e : G) ∈ Q := by
            have heEq : (e : G) = (a : G)⁻¹ * x := by
              rw [← haeG]
              simp
            rw [heEq]
            exact Q.mul_mem (Q.inv_mem (hA₀Q a.property)) hxQ
          exact haeG ▸ Subgroup.mul_mem_sup
            (show (a : G) ∈ A₀ from a.property)
            (show (e : G) ∈ J from ⟨e.property, heQ⟩)
        · exact sup_le hA₀Q inf_le_right
      have hdisA₀J : Disjoint A₀ J := by
        rw [disjoint_iff_inf_le]
        intro x hx
        apply Subgroup.mem_bot.mpr
        let xF : F := ⟨x, hsd.1 hx.1⟩
        have hxA : xF ∈ A₀.subgroupOf F := hx.1
        have hxE : xF ∈ E₀.subgroupOf F := hx.2.1
        have hxBot : xF ∈ (⊥ : Subgroup F) :=
          hsd.2.2.2.disjoint.le_bot ⟨hxA, hxE⟩
        simpa [xF] using congrArg Subtype.val (Subgroup.mem_bot.mp hxBot)
      have hJbot : J = ⊥ :=
        disjoint_right_eq_bot_of_cyclic_pgroup_12_11
          hQq hQcyclic hA₀Q hnon.A0_card inf_le_right hdisA₀J
      have hQA₀ : Q = A₀ := by simpa [hJbot] using hQeq
      have hQC : Q ≤ C := by
        rw [hQA₀, ← hQ₀A₀]
        exact hQ₀C
      have hQECE : (QE : Subgroup E) ≤
          (centralizerWithin E A).subgroupOf E := by
        intro x hx
        exact ⟨x.property, hQC (Subgroup.mem_map_of_mem E.subtype hx)⟩
      exact (QE.not_dvd_index
        (hqIndex.2.trans (Subgroup.index_dvd_of_le hQECE))).elim
  have hQ₁comm : IsMulCommutative (Q₁ : Subgroup G) := by
    have hambient :
        ambientSylow L (Q₁.subtype hQ₁L) = (Q₁ : Subgroup G) := by
      dsimp [ambientSylow]
      exact Subgroup.map_subgroupOf_eq_of_le hQ₁L
    rw [← hambient]
    exact (tau2_context hL hqTau2L (hBF.trans hFL) hB).sylow_abelian
      (Q₁.subtype hQ₁L)
  subst Mstar
  exact ⟨
    { q_mem_tau2 := hqTau2L
      pSylow := PG
      pSylow_le := hPGL
      pSylow_normal := by simpa only [PM] using hPMnormal
      qSylow := Q₁
      qSylow_le := hQ₁L
      qSylow_abelian := hQ₁comm }⟩

/-- The source `sub_nilpotent_cent2` step used in clause (b) of Lemma 12.11.

The images of the two prime-power subgroups lie in distinct prime cores of
the nilpotent quotient `Mstar' / beta(Mstar)`.  Those normal prime cores
commute, so the original commutator lies in `beta(Mstar)`. -/
private theorem commutator_le_beta_of_derived_pgroups_12_11
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M X Y : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpq : p ≠ q)
    (hXp : IsPGroup p X)
    (hYq : IsPGroup q Y)
    (hXder : X ≤ (_root_.commutator M).map M.subtype)
    (hYder : Y ≤ (_root_.commutator M).map M.subtype) :
    ⁅X, Y⁆ ≤ betaCore M := by
  classical
  let D : Subgroup M := _root_.commutator M
  let B₀ : Subgroup M := (betaCore M).subgroupOf M
  have hB₀D : B₀ ≤ D := by
    intro x hx
    change (x : G) ∈ betaCore M at hx
    change x ∈ D
    obtain ⟨y, hy, hyx⟩ := Mbeta_der1 hM hx
    have hyx' : y = x := M.subtype_injective hyx
    simpa [hyx'] using hy
  have hB₀normal : B₀.Normal := by
    simpa [B₀] using betaCore_normal M
  letI : B₀.Normal := hB₀normal
  let B : Subgroup D := B₀.subgroupOf D
  have hBnormal : B.Normal := by
    dsimp [B]
    infer_instance
  letI : B.Normal := hBnormal

  have hXM : X ≤ M :=
    hXder.trans (Subgroup.map_subtype_le (_root_.commutator M))
  have hYM : Y ≤ M :=
    hYder.trans (Subgroup.map_subtype_le (_root_.commutator M))
  let XM : Subgroup M := X.subgroupOf M
  let YM : Subgroup M := Y.subgroupOf M
  have hXMD : XM ≤ D := by
    intro x hx
    change (x : G) ∈ X at hx
    obtain ⟨d, hd, hdx⟩ := hXder hx
    have hdx' : d = x := M.subtype_injective hdx
    simpa [hdx'] using hd
  have hYMD : YM ≤ D := by
    intro y hy
    change (y : G) ∈ Y at hy
    obtain ⟨d, hd, hdy⟩ := hYder hy
    have hdy' : d = y := M.subtype_injective hdy
    simpa [hdy'] using hd
  let XD : Subgroup D := XM.subgroupOf D
  let YD : Subgroup D := YM.subgroupOf D
  have hXMp : IsPGroup p XM := by
    dsimp [XM]
    exact hXp.comap_subtype
  have hYMp : IsPGroup q YM := by
    dsimp [YM]
    exact hYq.comap_subtype
  have hXDp : IsPGroup p XD := by
    dsimp [XD]
    exact hXMp.comap_subtype
  have hYDq : IsPGroup q YD := by
    dsimp [YD]
    exact hYMp.comap_subtype

  let Q := D ⧸ B
  let pi : D →* Q := QuotientGroup.mk' B
  letI : Group.IsNilpotent Q := by
    simpa [Q, D, B, B₀] using Mbeta_quo_nil hM
  let Xbar : Subgroup Q := XD.map pi
  let Ybar : Subgroup Q := YD.map pi
  have hXbarCore : Xbar ≤ pCore p Q :=
    (hXDp.map pi).le_pCore_of_isNilpotent
  have hYbarCore : Ybar ≤ pCore q Q :=
    (hYDq.map pi).le_pCore_of_isNilpotent
  have hCoreDisjoint : Disjoint (pCore p Q) (pCore q Q) :=
    IsPGroup.disjoint_of_ne p q hpq _ _
      (pCore_isPGroup (p := p) (G := Q))
      (pCore_isPGroup (p := q) (G := Q))
  have hCoreComm : ⁅pCore p Q, pCore q Q⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_of_disjoint hCoreDisjoint
  have hbarComm : ⁅Xbar, Ybar⁆ = ⊥ := by
    apply le_antisymm
    · rw [← hCoreComm]
      exact Subgroup.commutator_mono hXbarCore hYbarCore
    · exact bot_le
  have hmapComm : ⁅XD, YD⁆.map pi = ⊥ := by
    rw [Subgroup.map_commutator]
    exact hbarComm
  have hcommB : ⁅XD, YD⁆ ≤ B := by
    intro z hz
    have hzmap : pi z ∈ ⁅XD, YD⁆.map pi :=
      Subgroup.mem_map_of_mem pi hz
    rw [hmapComm] at hzmap
    exact (QuotientGroup.eq_one_iff z).mp
      (Subgroup.mem_bot.mp hzmap)

  have hcommMapD : ⁅XD, YD⁆.map D.subtype = ⁅XM, YM⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hXMD,
      Subgroup.map_subgroupOf_eq_of_le hYMD]
  have hcommB₀ : ⁅XM, YM⁆ ≤ B₀ := by
    rw [← hcommMapD,
      ← Subgroup.map_subgroupOf_eq_of_le hB₀D]
    exact Subgroup.map_mono hcommB
  have hcommMapM : ⁅XM, YM⁆.map M.subtype = ⁅X, Y⁆ := by
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hXM,
      Subgroup.map_subgroupOf_eq_of_le hYM]
  rw [← hcommMapM,
    ← Subgroup.map_subgroupOf_eq_of_le (betaCore_le M)]
  exact Subgroup.map_mono hcommB₀

/-- `BGsection12.v: primes_norm_tau2Elem`, clause (b) of Lemma 12.11.

This public source-facing form accepts clause (a) and the `tau1(M)` quotient
bound from Corollary 12.10(c), and concludes the corresponding
`tau1(Mstar) ∪ tau2(Mstar)` quotient bound. -/
theorem primes_norm_tau2Elem_quotient_tau12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A Mstar : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hMstar : Mstar ∈ minSimple_max_groups (G := G))
    (hNormalizer : Subgroup.normalizer (A : Set G) ≤ Mstar)
    (hclassification :
      ∀ {r : ℕ}, r ∈ tau2Primes M →
        r ∈ sigmaPrimes Mstar ∧ r ∉ betaPrimes Mstar)
    (hquotientTau1 :
      IsPiNumber (tau1Primes M)
        ((centralizerWithin E A).subgroupOf E).index) :
    IsPiNumber (tau1Primes Mstar ∪ tau2Primes Mstar)
      ((centralizerWithin E A).subgroupOf E).index := by
  classical
  let CE : Subgroup E := (centralizerWithin E A).subgroupOf E
  intro q hq hqIndex
  by_contra hqNotTau12
  letI : Fact p.Prime := ⟨hpTau.1⟩
  letI : Fact q.Prime := ⟨hq⟩
  have hqTau1M : q ∈ tau1Primes M :=
    hquotientTau1 hq hqIndex
  have hpq : p ≠ q := by
    intro hpq
    subst q
    exact (tau2'1 M hqTau1M) hpTau

  let QE : Sylow q E := Classical.choice Sylow.nonempty
  let Q : Subgroup G := (QE : Subgroup E).map E.subtype
  have hqEcard : q ∣ Nat.card E :=
    hqIndex.trans CE.index_dvd_card
  have hQEne : (QE : Subgroup E) ≠ ⊥ :=
    QE.ne_bot_of_dvd_card hqEcard
  have hQE : Q ≤ E := Subgroup.map_subtype_le _
  have hQq : IsPGroup q Q := QE.isPGroup'.map E.subtype
  have hqQ : q ∣ Nat.card Q := by
    rw [Subgroup.card_map_of_injective E.subtype_injective]
    exact QE.isPGroup'.card_eq_or_dvd.resolve_left
      (((QE : Subgroup E).one_lt_card_iff_ne_bot.mpr hQEne).ne')

  have hTauM := tau2_compl_context hM hEM hHallE hpTau hAE hA
  have hQnormA : Q ≤ Subgroup.normalizer (A : Set G) :=
    hQE.trans hTauM.A_normalizer_le
  have hQMstar : Q ≤ Mstar := hQnormA.trans hNormalizer
  have hcommA : ⁅A, Q⁆ ≤ A :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hQnormA
  have hcommNe : ⁅A, Q⁆ ≠ ⊥ := by
    intro hcommBot
    have hcommQA : ⁅Q, A⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, hcommBot]
    have hQcentA : Q ≤ Subgroup.centralizer (A : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommQA
    have hQECE : (QE : Subgroup E) ≤ CE := by
      intro x hx
      have hxQ : (x : G) ∈ Q :=
        Subgroup.mem_map_of_mem E.subtype hx
      exact ⟨x.property, hQcentA hxQ⟩
    exact QE.not_dvd_index
      (hqIndex.trans (Subgroup.index_dvd_of_le hQECE))

  have hpSigmaStar : p ∈ sigmaPrimes Mstar :=
    (hclassification hpTau).1
  have hAMstar : A ≤ Mstar :=
    Subgroup.le_normalizer.trans hNormalizer
  have hASigmaStar : A ≤ sigmaCore Mstar := by
    apply le_normal_isHall_of_isPiNumber_12_11
      (sigmaCore_normal Mstar) (Msigma_Hall hMstar) hAMstar
    exact hA.isPGroup.isPiNumber_natCard hpSigmaStar
  have hADerived :
      A ≤ (_root_.commutator Mstar).map Mstar.subtype :=
    hASigmaStar.trans (Msigma_der1 hMstar)
  have hQDerived :
      Q ≤ (_root_.commutator Mstar).map Mstar.subtype := by
    by_cases hqSigmaStar : q ∈ sigmaPrimes Mstar
    · have hQSigmaStar : Q ≤ sigmaCore Mstar := by
        apply le_normal_isHall_of_isPiNumber_12_11
          (sigmaCore_normal Mstar) (Msigma_Hall hMstar) hQMstar
        exact hQq.isPiNumber_natCard hqSigmaStar
      exact hQSigmaStar.trans (Msigma_der1 hMstar)
    · have hQcompl :
          IsPiNumber (sigmaPrimes Mstar)ᶜ (Nat.card Q) :=
        hQq.isPiNumber_natCard hqSigmaStar
      obtain ⟨F, hQF, hFMstar, hHallF⟩ :=
        exists_ambient_isHall_ge_of_isSolvable hQMstar
          (mmax_sol hMstar) (sigmaPrimes Mstar)ᶜ hQcompl
      have hqF : q ∈ primeSupport (Nat.card F) :=
        ⟨hq, hqQ.trans (Subgroup.card_dvd_of_le hQF)⟩
      rcases primeSupport_sigma_complement_subset_tau_12_11
          hMstar hFMstar hHallF hqF with (hqTau1 | hqTau2) | hqTau3
      · exact (hqNotTau12 (Or.inl hqTau1)).elim
      · exact (hqNotTau12 (Or.inr hqTau2)).elim
      · have hQpi3 : IsPiNumber (tau3Primes Mstar) (Nat.card Q) :=
          hQq.isPiNumber_natCard hqTau3
        obtain ⟨F₃, hQF₃, hF₃F, hHallF₃⟩ :=
          exists_ambient_isHall_ge_of_isSolvable hQF
            (sigma_compl_sol hFMstar hHallF)
            (tau3Primes Mstar) hQpi3
        obtain ⟨F₁, hF₁F, hHallF₁⟩ :=
          (ex_tau13_compl hFMstar hHallF).1
        obtain ⟨F₂, _hF₂F, _hHallF₂, hComplF⟩ :=
          ex_tau2_compl hFMstar hHallF hF₁F hHallF₁
            hF₃F hHallF₃
        have hFctx := sigma_compl_context hMstar hComplF
        calc
          Q ≤ F₃ := hQF₃
          _ ≤ (_root_.commutator F).map F.subtype :=
            hFctx.E₃_le_commutator
          _ = ⁅F, F⁆ := F.map_subtype_commutator
          _ ≤ ⁅Mstar, Mstar⁆ :=
            Subgroup.commutator_mono hFMstar hFMstar
          _ = (_root_.commutator Mstar).map Mstar.subtype :=
            Mstar.map_subtype_commutator.symm

  have hcommBeta : ⁅A, Q⁆ ≤ betaCore Mstar :=
    commutator_le_beta_of_derived_pgroups_12_11
      hMstar hpq hA.isPGroup hQq hADerived hQDerived
  let C : Subgroup G := ⁅A, Q⁆
  have hCp : IsPGroup p C := by
    exact hA.isPGroup.of_injective
      (Subgroup.inclusion hcommA)
      (Subgroup.inclusion_injective hcommA)
  have hCne : C ≠ ⊥ := by simpa [C] using hcommNe
  have hpC : p ∣ Nat.card C :=
    hCp.card_eq_or_dvd.resolve_left
      ((C.one_lt_card_iff_ne_bot.mpr hCne).ne')
  have hpBetaStar : p ∈ betaPrimes Mstar :=
    betaCore_isPiNumber Mstar hpTau.1
      (hpC.trans (Subgroup.card_dvd_of_le hcommBeta))
  exact (hclassification hpTau).2 hpBetaStar

/-- `BGsection12.v: primes_norm_tau2Elem`, Bender--Glauberman Lemma 12.11. -/
noncomputable def primes_norm_tau2Elem
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A Mstar : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hMstar : Mstar ∈ minSimple_max_groups (G := G))
    (hNormalizer : Subgroup.normalizer (A : Set G) ≤ Mstar) :
    PrimesNormTau2ElemConclusion M E A Mstar p := by
  letI : Fact p.Prime := ⟨hpTau.1⟩
  have hfactor : Tau1CentralizerFactor M E A :=
    tau1_cent_tau2Elem_factor hM hEM hHallE hpTau hAE hA
  have hclassification :
      ∀ {q : ℕ}, q ∈ tau2Primes M →
        q ∈ sigmaPrimes Mstar ∧ q ∉ betaPrimes Mstar :=
    primes_norm_tau2Elem_tau2_classification hM hEM hHallE hpTau
      hAE hA hMstar hNormalizer
  have hquotient :
      IsPiNumber (tau1Primes Mstar ∪ tau2Primes Mstar)
        ((centralizerWithin E A).subgroupOf E).index :=
    primes_norm_tau2Elem_quotient_tau12 hM hEM hHallE hpTau
      hAE hA hMstar hNormalizer hclassification
      hfactor.quotient_isPiNumber
  exact
    { tau2_classification := hclassification
      quotient_tau12 := hquotient
      common_prime_structure := by
        intro q hqIndex hqCentral
        exact Classical.choice
          (exists_primes_norm_tau2Elem_common_prime_structure
            hM hEM hHallE hpTau hAE hA hMstar hNormalizer
            hfactor hclassification
            (fun {L} hL hNL hclassificationL ↦
              primes_norm_tau2Elem_quotient_tau12
                hM hEM hHallE hpTau hAE hA hL hNL
                hclassificationL hfactor.quotient_isPiNumber)
            hqIndex hqCentral) }

/-! ## The generalized Theorem 12.12 -/

/-- The elementwise regularity assumption in Theorem 12.12.

It says that every nonidentity element of `U` whose order is supported on
`tau1(M) ∪ tau3(M)` acts fixed-point-freely on `M_sigma`. -/
def FTTypeFRegularity
    {G : Type u} [Group G] [Finite G]
    (M U : Subgroup G) : Prop :=
  ∀ {x : G}, x ∈ U → x ≠ 1 →
    IsPiNumber (tau1Primes M ∪ tau3Primes M) (orderOf x) →
      centralizerWithin (sigmaCore M) (Subgroup.zpowers x) = ⊥

/-! ### Prime support in the trivial `tau2`-intersection branch -/

/-- Intersecting a Hall subgroup with a normal subgroup gives a Hall
subgroup of the normal subgroup. -/
private theorem isHall_inf_normal_12_12
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {H N : Subgroup K}
    (hH : IsHall pi H) (hN : N.Normal) :
    IsHall pi ((H ⊓ N).subgroupOf N) := by
  letI : N.Normal := hN
  constructor
  · rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq inf_le_right]
    exact hH.isPiNumber_card.of_dvd
      (Subgroup.card_dvd_of_le inf_le_left)
  · intro p hp hpIndex hpPi
    letI : Fact p.Prime := ⟨hp⟩
    let PH : Sylow p H := Classical.choice Sylow.nonempty
    obtain ⟨P, hP⟩ :=
      exists_sylow_eq_map_of_sylow_hall_12_11 hp hH hpPi PH
    have hPH : (P : Subgroup K) ≤ H := by
      rw [hP]
      exact Subgroup.map_subtype_le _
    let R : Sylow p N := normalIntersectionSylow P N
    have hRmap :
        (R : Subgroup N).map N.subtype =
          (P : Subgroup K) ⊓ N := by
      simpa [R] using map_normalIntersectionSylow_eq_inf P N
    have hRI : (R : Subgroup N) ≤ (H ⊓ N).subgroupOf N := by
      intro x hx
      have hxMap : (x : K) ∈ (P : Subgroup K) ⊓ N := by
        rw [← hRmap]
        exact Subgroup.mem_map_of_mem N.subtype hx
      exact ⟨hPH hxMap.1, hxMap.2⟩
    exact R.not_dvd_index
      (hpIndex.trans (Subgroup.index_dvd_of_le hRI))

/-- Hall subgroups transport across a multiplicative equivalence. -/
private theorem isHall_map_mulEquiv_12_12
    {K L : Type u} [Group K] [Group L] [Finite K] [Finite L]
    {pi : Set ℕ} {H : Subgroup K} (e : K ≃* L)
    (hH : IsHall pi H) :
    IsHall pi (H.map e.toMonoidHom) := by
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hH.isPiNumber_card
  · have hindex : (H.map e.toMonoidHom).index = H.index :=
      Subgroup.index_map_equiv H e
    exact hindex.symm ▸ hH.isPiNumber_index

/-- Ambient form of intersection with a normal subgroup: both input and
output subgroups are represented in their original ambient group. -/
private theorem isHall_inf_normal_of_le_12_12
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {E H N : Subgroup G}
    (hHE : H ≤ E) (hNE : N ≤ E)
    (hH : IsHall pi (H.subgroupOf E))
    (hN : (N.subgroupOf E).Normal) :
    IsHall pi ((H ⊓ N).subgroupOf N) := by
  let HE : Subgroup E := H.subgroupOf E
  let NE : Subgroup E := N.subgroupOf E
  let eN : NE ≃* N := Subgroup.subgroupOfEquivOfLe hNE
  have hNested : IsHall pi ((HE ⊓ NE).subgroupOf NE) :=
    isHall_inf_normal_12_12 hH hN
  have hMapped := isHall_map_mulEquiv_12_12 eN hNested
  have hmap :
      ((HE ⊓ NE).subgroupOf NE).map eN.toMonoidHom =
        (H ⊓ N).subgroupOf N := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨hy.1, y.property⟩
    · intro hx
      refine ⟨⟨⟨(x : G), hNE x.property⟩, x.property⟩, ?_, rfl⟩
      exact ⟨hx.1, x.property⟩
  rwa [hmap] at hMapped

/-- If `H` is normal in `E`, then `H ∩ N`, represented inside an
intermediate subgroup `N ≤ E`, is normal in `N`. -/
private theorem normal_inf_subgroupOf_of_le_12_12
    {G : Type u} [Group G] {E H N : Subgroup G}
    (hHE : H ≤ E) (hNE : N ≤ E)
    (hHnormal : (H.subgroupOf E).Normal) :
    ((H ⊓ N).subgroupOf N).Normal := by
  have hEnormH : E ≤ Subgroup.normalizer (H : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hHE).mp hHnormal
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  intro n hn
  have hnH := Subgroup.mem_normalizer_iff.mp (hEnormH (hNE hn))
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact ⟨(hnH x).mp hx.1,
      N.mul_mem (N.mul_mem hn hx.2) (N.inv_mem hn)⟩
  · intro hx
    have hxN : x ∈ N := by
      have hconj : n⁻¹ * (n * x * n⁻¹) * n ∈ N :=
        N.mul_mem (N.mul_mem (N.inv_mem hn) hx.2) hn
      have heq : n⁻¹ * (n * x * n⁻¹) * n = x := by group
      simpa only [heq] using hconj
    exact ⟨(hnH x).mpr hx.1, hxN⟩

/-- A nontrivial Sylow subgroup of `E₂ ∩ U` has the same ambient
carrier as a Sylow subgroup of `G`.  The first transport uses normality of
`E₂` and the Hall property of `U`; the second uses that `E₂` is the
ambient `tau2` Hall subgroup. -/
private theorem exists_ambient_sylow_eq_of_tau2_inf_12_12
    {G : Type u} [Group G] [Finite G]
    {M E U E₂ : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hp : p.Prime)
    (hpTau : p ∈ tau2Primes M)
    (hE₂E : E₂ ≤ E)
    (hE₂normal : (E₂.subgroupOf E).Normal)
    (hE₂Hall : IsHall (tau2Primes M) E₂)
    (hUE : U ≤ E)
    (hHallU : IsHall (primeSupport (Nat.card U)) (U.subgroupOf E))
    (P : Sylow p (E₂ ⊓ U : Subgroup G))
    (hPne : (P : Subgroup (E₂ ⊓ U : Subgroup G)) ≠ ⊥) :
    ∃ S : Sylow p G,
      (S : Subgroup G) = ambientSylow (E₂ ⊓ U) P := by
  have hpP : p ∣ Nat.card P :=
    P.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hPne (Subgroup.card_eq_one.mp hcard))
  have hpU : p ∈ primeSupport (Nat.card U) :=
    ⟨hp, hpP.trans
      ((P : Subgroup (E₂ ⊓ U : Subgroup G)).card_subgroup_dvd_card.trans
        (Subgroup.card_dvd_of_le inf_le_right))⟩
  have hInfHallE₂ :
      IsHall (primeSupport (Nat.card U))
        ((E₂ ⊓ U).subgroupOf E₂) := by
    simpa only [inf_comm] using
      (isHall_inf_normal_of_le_12_12 hUE hE₂E hHallU hE₂normal)
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_of_hall_with_same_ambient_12_12 hp inf_le_left
      hInfHallE₂ hpU P
  obtain ⟨S, hS⟩ :=
    exists_sylow_eq_map_of_sylow_hall_12_11
      hp hE₂Hall hpTau Q
  exact ⟨S, hS.trans hQ⟩

/-- If the `tau2` Hall factor meets a normal subgroup trivially, all element
orders in that subgroup are supported on `tau1(M) ∪ tau3(M)`. -/
private theorem tau13_orderOf_of_tau2_inf_eq_bot_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hUnormal : (U.subgroupOf E).Normal)
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (htrivial : E₂ ⊓ U = ⊥)
    {x : G} (hxU : x ∈ U) :
    IsPiNumber (tau1Primes M ∪ tau3Primes M) (orderOf x) := by
  intro q hq hqOrder
  have hqU : q ∣ Nat.card U :=
    hqOrder.trans (U.orderOf_dvd_natCard hxU)
  have hqE : q ∈ primeSupport (Nat.card E) :=
    ⟨hq, hqU.trans (Subgroup.card_dvd_of_le hUE)⟩
  rcases primeSupport_sigma_complement_subset_tau_12_11
      hM hEM hHallE hqE with (hq1 | hq2) | hq3
  · exact Or.inl hq1
  · let E₂E : Subgroup E := E₂.subgroupOf E
    let UE : Subgroup E := U.subgroupOf E
    have hHallInf :
        IsHall (tau2Primes M) ((E₂E ⊓ UE).subgroupOf UE) := by
      simpa only [E₂E, UE] using
        (isHall_inf_normal_12_12 hCompl.hall_E₂ hUnormal)
    have hInfBot : E₂E ⊓ UE = ⊥ := by
      apply le_antisymm
      · intro y hy
        apply Subgroup.mem_bot.mpr
        apply Subtype.ext
        have hyAmbient : ((y : E) : G) ∈ E₂ ⊓ U :=
          ⟨hy.1, hy.2⟩
        rw [htrivial] at hyAmbient
        exact Subgroup.mem_bot.mp hyAmbient
      · exact bot_le
    have hqUE : q ∣ Nat.card UE := by
      simpa only [UE,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hUE]
        using hqU
    have hqIndex :
        q ∣ ((E₂E ⊓ UE).subgroupOf UE).index := by
      rw [hInfBot, Subgroup.bot_subgroupOf, Subgroup.index_bot]
      exact hqUE
    exact ((hHallInf.isPiNumber_index hq hqIndex) hq2).elim
  · exact Or.inr hq3

/-- Inside a sigma-complement, an element whose order avoids `tau2(M)` is
supported on the union of the `tau1(M)` and `tau3(M)` parts. -/
private theorem tau13_orderOf_of_tau2_complement_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    {x : G} (hxU : x ∈ U)
    (hxTau2c : IsPiNumber (tau2Primes M)ᶜ (orderOf x)) :
    IsPiNumber (tau1Primes M ∪ tau3Primes M) (orderOf x) := by
  intro q hq hqOrder
  have hqE : q ∈ primeSupport (Nat.card E) :=
    ⟨hq, hqOrder.trans
      ((U.orderOf_dvd_natCard hxU).trans
        (Subgroup.card_dvd_of_le hUE))⟩
  rcases primeSupport_sigma_complement_subset_tau_12_11
      hM hEM hHallE hqE with (hq1 | hq2) | hq3
  · exact Or.inl hq1
  · exact (hxTau2c hq hqOrder hq2).elim
  · exact Or.inr hq3

/-! ### Routine semidirect-product and action adapters -/

/-- A normalized disjoint pair is complementary in the subgroup it
generates. -/
private theorem subgroupOf_sup_isComplement_12_12
    {G : Type u} [Group G] {H R : Subgroup G}
    (hnorm : R ≤ Subgroup.normalizer (H : Set G))
    (hdis : Disjoint H R) :
    (H.subgroupOf (H ⊔ R)).IsComplement'
      (R.subgroupOf (H ⊔ R)) := by
  let K : Subgroup G := H ⊔ R
  let HK : Subgroup K := H.subgroupOf K
  let RK : Subgroup K := R.subgroupOf K
  have hKnormH : K ≤ Subgroup.normalizer (H : Set G) :=
    sup_le Subgroup.le_normalizer hnorm
  letI : HK.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hKnormH
  have hdisK : Disjoint HK RK := by
    rw [disjoint_iff_inf_le]
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxBot : ((x : K) : G) ∈ (⊥ : Subgroup G) :=
      hdis.le_bot ⟨hx.1, hx.2⟩
    exact Subgroup.mem_bot.mp hxBot
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisK
  have htop : HK ⊔ RK = ⊤ := by
    change H.subgroupOf K ⊔ R.subgroupOf K = ⊤
    rw [← Subgroup.subgroupOf_sup
      (show H ≤ K from le_sup_left)
      (show R ≤ K from le_sup_right)]
    exact Subgroup.subgroupOf_self K
  rw [← Subgroup.normal_mul HK RK, htop]
  rfl

/-- Restrict the sigma-core semidirect product from a full sigma complement
to any subgroup of that complement. -/
private theorem sigma_subgroup_semidirect_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E) :
    IsInternalSemidirectProductIn (sigmaCore M) U
      (sigmaCore M ⊔ U) := by
  have hFull := sdprod_sigma hM hEM hHallE
  have hMnormSigma :
      M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).mp
      (sigmaCore_normal M)
  have hUnormSigma :
      U ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (hUE.trans hEM).trans hMnormSigma
  have hdisSigmaE : Disjoint (sigmaCore M) E := by
    rw [disjoint_iff_inf_le]
    intro x hx
    apply Subgroup.mem_bot.mpr
    let xM : M := ⟨x, hEM hx.2⟩
    have hxSub :
        xM ∈ (sigmaCore M).subgroupOf M ⊓ E.subgroupOf M :=
      ⟨hx.1, hx.2⟩
    have hxBot : xM ∈ (⊥ : Subgroup M) :=
      hFull.2.2.2.disjoint.le_bot hxSub
    simpa [xM] using congrArg Subtype.val (Subgroup.mem_bot.mp hxBot)
  have hdisSigmaU : Disjoint (sigmaCore M) U :=
    Disjoint.mono le_rfl hUE hdisSigmaE
  have hnormal :
      ((sigmaCore M).subgroupOf (sigmaCore M ⊔ U)).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    exact sup_le Subgroup.le_normalizer hUnormSigma
  exact
    ⟨le_sup_left, le_sup_right, hnormal,
      subgroupOf_sup_isComplement_12_12 hUnormSigma hdisSigmaU⟩

/-- The element-centralizer form of fixed-point-freeness implies
semiregularity of the conjugation action. -/
private theorem semiregular_of_zpowers_centralizer_12_12
    {G : Type u} [Group G] {K A : Subgroup G}
    (hcent : ∀ {a : G}, a ∈ A → a ≠ 1 →
      centralizerWithin K (Subgroup.zpowers a) = ⊥) :
    IsSemiregularConjugation K A := by
  intro a ha x hax
  have haG : (a : G) ≠ 1 := by
    intro haOne
    apply ha
    exact Subtype.ext haOne
  have hxcent :
      (x : G) ∈ centralizerWithin K (Subgroup.zpowers (a : G)) := by
    refine ⟨x.property, ?_⟩
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : Commute (a : G) (x : G) := by
      rw [Commute]
      calc
        (a : G) * (x : G) =
            ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) := by
              simp [mul_assoc]
        _ = (x : G) * (a : G) := by rw [hax]
    exact hcomm.zpow_left n
  have hxBot : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← hcent a.property haG]
    exact hxcent
  apply Subtype.ext
  simpa using hxBot

private theorem isMulCommutative_of_le_12_12
    {G : Type u} [Group G] {A B : Subgroup G}
    (hAB : A ≤ B) (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  rw [isMulCommutative_iff] at hB ⊢
  intro x y
  apply A.subtype_injective
  change (x : G) * (y : G) = (y : G) * (x : G)
  exact congrArg Subtype.val
    (hB ⟨x, hAB x.property⟩ ⟨y, hAB y.property⟩)

/-- Pull exact elementary-abelian rank two back through the injective
ambient map of an omega-one subgroup. -/
private theorem omegaOne_rank_two_of_map_eq_12_12
    {G : Type u} [Group G] [Finite G]
    {S A : Subgroup G} {p : ℕ}
    (hSp : IsPGroup p S)
    (hScomm : IsMulCommutative S)
    (hOmegaA : (omegaOne p S).map S.subtype = A)
    (hA : IsElementaryAbelianOfRank p 2 A) :
    IsElementaryAbelianOfRank p 2 (omegaOne p S) := by
  letI : IsMulCommutative S := hScomm
  refine
    { isPGroup := hSp.to_subgroup (omegaOne p S)
      commutative := by infer_instance
      pow_eq_one := ?_
      card_eq := ?_ }
  · intro x
    apply Subtype.ext
    have hxker : (x : S) ∈ (powMonoidHom p : S →* S).ker := by
      rw [← omegaOne_eq_powMonoidHom_ker]
      exact x.property
    exact hxker
  · calc
      Nat.card (omegaOne p S) =
          Nat.card ((omegaOne p S).map S.subtype) :=
        (Subgroup.card_map_of_injective S.subtype_injective).symm
      _ = Nat.card A :=
        congrArg (fun H : Subgroup G ↦ Nat.card H) hOmegaA
      _ = p ^ 2 := hA.card_eq

/-- The omega-one subgroup of an ambient cyclic subgroup generated by an
exponent witness is generated by its last nonzero `p`-power. -/
private theorem map_omegaOne_zpowers_eq_lastPower_12_12
    {G : Type u} [Group G] [Finite G]
    {S : Subgroup G} {p n : ℕ} [Fact p.Prime]
    (z : S) (hz : orderOf z = p ^ (n + 1)) :
    (omegaOne p (Subgroup.zpowers (z : G))).map
        (Subgroup.zpowers (z : G)).subtype =
      (Subgroup.zpowers (z ^ (p ^ n))).map S.subtype := by
  let Z : Subgroup G := Subgroup.zpowers (z : G)
  let w : S := z ^ (p ^ n)
  have hzG : orderOf (z : G) = p ^ (n + 1) :=
    (orderOf_injective S.subtype S.subtype_injective z).trans hz
  have hZcard : Nat.card Z = p ^ (n + 1) := by
    simpa [Z, Nat.card_zpowers] using hzG
  have hZp : IsPGroup p Z := IsPGroup.of_card hZcard
  have hZcard_ne_one : Nat.card Z ≠ 1 := by
    rw [hZcard]
    exact (one_lt_pow₀ (Fact.out : p.Prime).one_lt
      (Nat.succ_ne_zero n)).ne'
  letI : IsCyclic Z := by
    dsimp [Z]
    infer_instance
  have hOmegaCard : Nat.card (omegaOne p Z) = p :=
    card_omegaOne_of_isCyclic_isPGroup
      (Fact.out : p.Prime) hZp hZcard_ne_one
  have hMapOmegaCard :
      Nat.card ((omegaOne p Z).map Z.subtype) = p := by
    rw [Subgroup.card_map_of_injective Z.subtype_injective,
      hOmegaCard]
  have hpow_ne : p ^ n ≠ 0 :=
    pow_ne_zero n (Fact.out : p.Prime).ne_zero
  have hpow_dvd : p ^ n ∣ orderOf z := by
    rw [hz, pow_succ]
    exact dvd_mul_right _ _
  have hwOrder : orderOf w = p := by
    dsimp [w]
    rw [orderOf_pow_of_dvd hpow_ne hpow_dvd, hz]
    simp [pow_succ, (Fact.out : p.Prime).ne_zero]
  have hRightCard :
      Nat.card ((Subgroup.zpowers w).map S.subtype) = p := by
    rw [Subgroup.card_map_of_injective S.subtype_injective,
      Nat.card_zpowers, hwOrder]
  let wZ : Z := ⟨((z : G) ^ (p ^ n)), by
    exact Subgroup.pow_mem Z (Subgroup.mem_zpowers (z : G)) (p ^ n)⟩
  have hwZpow : wZ ^ p = 1 := by
    apply Subtype.ext
    change ((z : G) ^ (p ^ n)) ^ p = 1
    rw [← pow_mul, ← pow_succ, ← hzG,
      pow_orderOf_eq_one]
  have hwMap : ((w : S) : G) ∈ (omegaOne p Z).map Z.subtype := by
    refine ⟨wZ, mem_omegaOne_of_pow_eq_one p hwZpow, ?_⟩
    rfl
  have hRightLe :
      (Subgroup.zpowers w).map S.subtype ≤
        (omegaOne p Z).map Z.subtype := by
    rw [MonoidHom.map_zpowers]
    exact Subgroup.zpowers_le.mpr hwMap
  have hEq :
      (Subgroup.zpowers w).map S.subtype =
        (omegaOne p Z).map Z.subtype :=
    Subgroup.eq_of_le_of_card_ge hRightLe (by
      rw [hMapOmegaCard, hRightCard])
  simpa [Z, w] using hEq.symm

/-- A nontrivial cyclic factor of a `tau2` Sylow subgroup is regular as
soon as the Sylow normalizer preserves its omega-one subgroup. -/
private theorem cyclic_tau2_factor_regular_of_normalizer_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A S Z : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hSp : IsPGroup p S)
    (hSE : S ≤ E)
    (hZS : Z ≤ S)
    (hZcyclic : IsCyclic Z)
    (hZne : Z ≠ ⊥)
    (hNSnotM : ¬ Subgroup.normalizer (S : Set G) ≤ M)
    (hNSNΩ :
      Subgroup.normalizer (S : Set G) ≤
        Subgroup.normalizer
          (((omegaOne p Z).map Z.subtype : Subgroup G) : Set G)) :
    centralizerWithin (sigmaCore M)
        ((omegaOne p Z).map Z.subtype) = ⊥ := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  letI : IsCyclic Z := hZcyclic
  let ΩZ : Subgroup G := (omegaOne p Z).map Z.subtype
  have hZp : IsPGroup p Z := hSp.to_le hZS
  have hZcard : Nat.card Z ≠ 1 := by
    intro hcard
    exact hZne (Subgroup.card_eq_one.mp hcard)
  have hΩcard : Nat.card ΩZ = p := by
    dsimp [ΩZ]
    rw [Subgroup.card_map_of_injective Z.subtype_injective]
    exact card_omegaOne_of_isCyclic_isPGroup
      hpTau.1 hZp hZcard
  have hΩline : IsElementaryAbelianOfRank p 1 ΩZ :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hΩcard
  have hΩE : ΩZ ≤ E :=
    (Subgroup.map_subtype_le (omegaOne p Z)).trans
      (hZS.trans hSE)
  by_contra hnonregular
  have hfamily :
      minSimple_max_groups_of (G := G)
        (Subgroup.centralizer (ΩZ : Set G) : Set G) = {M} :=
    (tau2_compl_context hM hEM hHallE hpTau hAE hA)
      |>.line_centralizer_unique hΩE hΩline hnonregular
  have hNΩproper : Subgroup.normalizer (ΩZ : Set G) < ⊤ :=
    mFT_norm_proper ΩZ hΩline.ne_bot
      (mFT_pgroup_proper ΩZ hΩline.isPGroup)
  apply hNSnotM
  exact hNSNΩ.trans
    (sub_uniq_mmax hfamily
      (Subgroup.centralizer_le_normalizer (ΩZ : Set G))
      hNΩproper)

/-- Every cyclic subgroup of a Sylow subgroup centralized by `U` is normal
in `U`. -/
private theorem zpowers_normal_of_le_centralizer_12_12
    {G : Type u} [Group G]
    {S U : Subgroup G} (hSU : S ≤ U)
    (hUScent : U ≤ Subgroup.centralizer (S : Set G))
    (z : S) :
    ((Subgroup.zpowers (z : G)).subgroupOf U).Normal := by
  have hZU : Subgroup.zpowers (z : G) ≤ U :=
    (Subgroup.zpowers_le.mpr z.property).trans hSU
  apply Subgroup.normal_subgroupOf_of_le_normalizer
  apply (show U ≤
      Subgroup.centralizer (Subgroup.zpowers (z : G) : Set G) by
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxS : x ∈ S :=
      (Subgroup.zpowers_le.mpr z.property) hx
    exact Subgroup.mem_centralizer_iff.mp (hUScent hu) x hxS)
    |>.trans
  exact Subgroup.centralizer_le_normalizer
    (Subgroup.zpowers (z : G) : Set G)

/-- Construct the exponent-preserving regular cyclic factor when `U`
centralizes the selected abelian `tau2` Sylow subgroup. -/
private theorem exists_cyclic_regular_factor_central_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U A : Subgroup G} {p : ℕ}
    (S : Sylow p G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hAS : A ≤ (S : Subgroup G))
    (hSE : (S : Subgroup G) ≤ E)
    (hSU : (S : Subgroup G) ≤ U)
    (hScomm : IsMulCommutative (S : Subgroup G))
    (hSne : (S : Subgroup G) ≠ ⊥)
    (hUScent : U ≤
      Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    ∃ Z : Subgroup G,
      Z ≤ (S : Subgroup G) ∧
      (Z.subgroupOf U).Normal ∧
      IsCyclic Z ∧
      centralizerWithin (sigmaCore M)
          ((omegaOne p Z).map Z.subtype) = ⊥ ∧
      Monoid.exponent Z = Monoid.exponent (S : Subgroup G) := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  letI : IsMulCommutative (S : Subgroup G) := hScomm
  letI : Nontrivial (S : Subgroup G) :=
    (S : Subgroup G).nontrivial_iff_ne_bot.mpr hSne
  let SM : Sylow p M := S.subtype (hSE.trans hEM)
  have hAmbientSM : ambientSylow M SM = (S : Subgroup G) := by
    change ((S : Subgroup G).subgroupOf M).map M.subtype =
      (S : Subgroup G)
    exact Subgroup.map_subgroupOf_eq_of_le (hSE.trans hEM)
  have hTau := tau2_context hM hpTau (hAE.trans hEM) hA
  have hOmegaA :
      (omegaOne p (S : Subgroup G)).map
          (S : Subgroup G).subtype = A := by
    calc
      (omegaOne p (S : Subgroup G)).map
          (S : Subgroup G).subtype =
          (omegaOne p (ambientSylow M SM)).map
            (ambientSylow M SM).subtype :=
        congrArg
          (fun P : Subgroup G ↦ (omegaOne p P).map P.subtype)
          hAmbientSM.symm
      _ = A := hTau.omegaOne_eq SM (hAS.trans hAmbientSM.ge)
  have hOmegaRank :
      IsElementaryAbelianOfRank p 2
        (omegaOne p (S : Subgroup G)) :=
    omegaOne_rank_two_of_map_eq_12_12 S.isPGroup'
      hScomm hOmegaA hA
  have hAbOmegaRank :
      IsElementaryAbelianOfRank p 2
        (abelianOmegaOne p (S : Subgroup G)) := by
    simpa [abelianOmegaOne, omegaOne_eq_powMonoidHom_ker] using
      hOmegaRank
  obtain ⟨n, hexpS⟩ :=
    S.isPGroup'.exists_exponent_eq_prime_pow_succ
  let L : Subgroup (S : Subgroup G) :=
    abelianPowerSubgroup p n (S : Subgroup G)
  let O : Subgroup (S : Subgroup G) :=
    abelianOmegaOne p (S : Subgroup G)
  have hLO : L ≤ O := by
    simpa [L, O] using
      (abelianPowerSubgroup_le_omegaOne
        (E := (S : Subgroup G)) n hexpS)
  rcases lt_or_eq_of_le hLO with hproper | heq
  · obtain ⟨z, hzexp⟩ :=
      Monoid.exists_orderOf_eq_exponent
        (Monoid.ExponentExists.of_finite
          (G := (S : Subgroup G)))
    let Z : Subgroup G := Subgroup.zpowers (z : G)
    have hzpow : orderOf z = p ^ (n + 1) := hzexp.trans hexpS
    have hlast :
        L = Subgroup.zpowers (z ^ (p ^ n)) := by
      simpa [L, O] using
        (lastPower_eq_zpowers_of_rankTwo_proper
          S.isPGroup' n hexpS hAbOmegaRank hproper hzexp)
    have hOmegaZ :
        (omegaOne p Z).map Z.subtype = L.map (S : Subgroup G).subtype := by
      calc
        (omegaOne p Z).map Z.subtype =
            (Subgroup.zpowers (z ^ (p ^ n))).map
              (S : Subgroup G).subtype := by
          simpa [Z] using
            (map_omegaOne_zpowers_eq_lastPower_12_12 z hzpow)
        _ = L.map (S : Subgroup G).subtype :=
          congrArg (fun R : Subgroup (S : Subgroup G) ↦
            R.map (S : Subgroup G).subtype) hlast.symm
    have hNSNΩ :
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.normalizer
            (((omegaOne p Z).map Z.subtype : Subgroup G) : Set G) := by
      rw [hOmegaZ]
      exact characteristic_map_subtype_le_normalizer_12_11
        (S : Subgroup G) L
    have hNSnotM :
        ¬ Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M := by
      simpa [hAmbientSM] using
        hTau.normalizer_sylow_not_le SM
          (hAS.trans hAmbientSM.ge)
    have hZle : Z ≤ (S : Subgroup G) := by
      exact Subgroup.zpowers_le.mpr z.property
    have hZcyclic : IsCyclic Z := by
      dsimp [Z]
      infer_instance
    have hZne : Z ≠ ⊥ := by
      intro hbot
      have hzOne : (z : G) = 1 := by
        apply Subgroup.mem_bot.mp
        rw [← hbot]
        exact Subgroup.mem_zpowers (z : G)
      have : orderOf z = 1 := by
        calc
          orderOf z = orderOf (z : G) :=
            (orderOf_injective (S : Subgroup G).subtype
              (S : Subgroup G).subtype_injective z).symm
          _ = 1 := orderOf_eq_one_iff.mpr hzOne
      rw [hzexp] at this
      exact (Monoid.one_lt_exponent (G := (S : Subgroup G))).ne' this
    have hregularZ :
        centralizerWithin (sigmaCore M)
          ((omegaOne p Z).map Z.subtype) = ⊥ :=
      cyclic_tau2_factor_regular_of_normalizer_12_12
        hM hEM hHallE hpTau hAE hA S.isPGroup' hSE
        hZle hZcyclic hZne hNSnotM hNSNΩ
    have hZexp : Monoid.exponent Z =
        Monoid.exponent (S : Subgroup G) := by
      letI : IsCyclic Z := hZcyclic
      calc
        Monoid.exponent Z = Nat.card Z := IsCyclic.exponent_eq_card
        _ = orderOf (z : G) := by simp [Z, Nat.card_zpowers]
        _ = orderOf z :=
          orderOf_injective (S : Subgroup G).subtype
            (S : Subgroup G).subtype_injective z
        _ = Monoid.exponent (S : Subgroup G) := hzexp
    exact ⟨Z, hZle,
      zpowers_normal_of_le_centralizer_12_12 hSU hUScent z,
      hZcyclic, hregularZ, hZexp⟩
  · obtain ⟨A₁, hA₁A, hA₁, hA₁regular⟩ :=
      hTau.exists_rankOne_regular
    have hpA₁ : p ∣ Nat.card A₁ := by
      rw [hA₁.card_eq]
      simp
    obtain ⟨a, haOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := A₁) p hpA₁
    let aS : S := ⟨(a : G), hAS (hA₁A a.property)⟩
    have haGOrder : orderOf (a : G) = p :=
      (orderOf_injective A₁.subtype A₁.subtype_injective a).trans
        haOrder
    have haSOrder : orderOf aS = p :=
      (orderOf_injective (S : Subgroup G).subtype
        (S : Subgroup G).subtype_injective aS).symm.trans haGOrder
    have haO : aS ∈ O := by
      change aS ^ p = 1
      exact orderOf_dvd_iff_pow_eq_one.mp (dvd_of_eq haSOrder)
    have haL : aS ∈ L := by
      rw [heq]
      exact haO
    obtain ⟨z, hzlast⟩ :=
      (mem_abelianPowerSubgroup_iff p n aS).mp haL
    have haSne : aS ≠ 1 := by
      intro haOne
      have : orderOf aS = 1 := by rw [haOne, orderOf_one]
      rw [haSOrder] at this
      exact hpTau.1.ne_one this
    have hznot : z ^ p ^ n ≠ 1 := by
      simpa [hzlast] using haSne
    have hzfin : z ^ p ^ (n + 1) = 1 := by
      rw [← hexpS]
      exact Monoid.pow_exponent_eq_one z
    have hzpow : orderOf z = p ^ (n + 1) :=
      orderOf_eq_prime_pow hznot hzfin
    have hzexp : orderOf z = Monoid.exponent (S : Subgroup G) :=
      hzpow.trans hexpS.symm
    let Z : Subgroup G := Subgroup.zpowers (z : G)
    have hOmegaLast :
        (omegaOne p Z).map Z.subtype =
          (Subgroup.zpowers (z ^ (p ^ n))).map
            (S : Subgroup G).subtype := by
      simpa [Z] using
        (map_omegaOne_zpowers_eq_lastPower_12_12 z hzpow)
    have hlastA₁ :
        (Subgroup.zpowers (z ^ (p ^ n))).map
            (S : Subgroup G).subtype = A₁ := by
      rw [hzlast, MonoidHom.map_zpowers]
      apply Subgroup.eq_of_le_of_card_ge
      · exact Subgroup.zpowers_le.mpr a.property
      · have haAmbientOrder :
            orderOf ((S : Subgroup G).subtype aS) = p := by
          simpa [aS] using haGOrder
        rw [Nat.card_zpowers, haAmbientOrder, hA₁.card_eq]
        simp
    have hregularZ :
        centralizerWithin (sigmaCore M)
          ((omegaOne p Z).map Z.subtype) = ⊥ := by
      rw [hOmegaLast, hlastA₁]
      exact hA₁regular
    have hZle : Z ≤ (S : Subgroup G) :=
      Subgroup.zpowers_le.mpr z.property
    have hZcyclic : IsCyclic Z := by
      dsimp [Z]
      infer_instance
    have hZexp : Monoid.exponent Z =
        Monoid.exponent (S : Subgroup G) := by
      letI : IsCyclic Z := hZcyclic
      calc
        Monoid.exponent Z = Nat.card Z := IsCyclic.exponent_eq_card
        _ = orderOf (z : G) := by simp [Z, Nat.card_zpowers]
        _ = orderOf z :=
          orderOf_injective (S : Subgroup G).subtype
            (S : Subgroup G).subtype_injective z
        _ = Monoid.exponent (S : Subgroup G) := hzexp
    exact ⟨Z, hZle,
      zpowers_normal_of_le_centralizer_12_12 hSU hUScent z,
      hZcyclic, hregularZ, hZexp⟩

/-- Turn the raw output of the noncentral coprime split into the factor
package consumed by the selected-Sylow assembly. -/
private noncomputable def cyclicRegularTau2Factor_of_coprimeSplit_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U U₂ A S : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p U₂)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hSE : S ≤ E)
    (hSambient : S = (P : Subgroup U₂).map U₂.subtype)
    (hNSnotM : ¬ Subgroup.normalizer (S : Set G) ≤ M)
    (W : CoprimeSplitWitness12_12 U S p) :
    CyclicRegularTau2Factor M U U₂ P := by
  let eP : P ≃* (P : Subgroup U₂).map U₂.subtype :=
    (P : Subgroup U₂).equivMapOfInjective
      U₂.subtype U₂.subtype_injective
  have hExpSP : Monoid.exponent S = Monoid.exponent P := by
    rw [hSambient]
    exact (Monoid.exponent_eq_of_mulEquiv eP).symm
  exact
    { Z := W.Z
      Z_le_sylow := hSambient ▸ W.Z_le_S
      Z_normal_U := W.Z_normal_U
      Z_cyclic := W.Z_cyclic
      omega_regular :=
        cyclic_tau2_factor_regular_of_normalizer_12_12
          hM hEM hHallE hpTau hAE hA
          (show IsPGroup p S from
            hSambient ▸ P.isPGroup'.map U₂.subtype)
          hSE W.Z_le_S W.Z_cyclic W.Z_ne_bot hNSnotM
          W.normalizer_le_normalizer_omega
      exponent_eq := W.exponent_eq.trans hExpSP }

/-- Package the central exponent-witness construction for an intrinsic
Sylow subgroup of `U₂`. -/
private theorem exists_cyclicRegularTau2Factor_of_central_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U U₂ A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (P : Sylow p U₂) (S : Sylow p G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hAS : A ≤ (S : Subgroup G))
    (hSE : (S : Subgroup G) ≤ E)
    (hSU : (S : Subgroup G) ≤ U)
    (hScomm : IsMulCommutative (S : Subgroup G))
    (hSne : (S : Subgroup G) ≠ ⊥)
    (hUScent : U ≤
      Subgroup.centralizer ((S : Subgroup G) : Set G))
    (hSambient : (S : Subgroup G) =
      (P : Subgroup U₂).map U₂.subtype) :
    Nonempty (CyclicRegularTau2Factor M U U₂ P) := by
  obtain ⟨Z, hZS, hZnormal, hZcyclic, hZregular, hZexp⟩ :=
    exists_cyclic_regular_factor_central_12_12 S hM hEM hHallE
      hpTau hAE hA hAS hSE hSU hScomm hSne hUScent
  let eP : P ≃* (P : Subgroup U₂).map U₂.subtype :=
    (P : Subgroup U₂).equivMapOfInjective
      U₂.subtype U₂.subtype_injective
  have hExpSP : Monoid.exponent (S : Subgroup G) =
      Monoid.exponent P := by
    rw [hSambient]
    exact (Monoid.exponent_eq_of_mulEquiv eP).symm
  exact ⟨
    { Z := Z
      Z_le_sylow := hSambient ▸ hZS
      Z_normal_U := hZnormal
      Z_cyclic := hZcyclic
      omega_regular := hZregular
      exponent_eq := hZexp.trans hExpSP }⟩

/-- Prime and Sylow data extracted from a noncentral action of `U` on an
abelian `tau2` Sylow subgroup.  The last two fields are exactly the common
prime hypotheses needed by Lemma 12.11(c). -/
private structure NoncentralTau2PrimeData12_12
    {G : Type u} [Group G] [Finite G]
    (M E U A S : Subgroup G) where
  q : ℕ
  q_prime : q.Prime
  Q₁ : Subgroup G
  Q₁_sylow_E : IsSylowSubgroupOf q Q₁ E
  Q₁_le_U : Q₁ ≤ U
  Q₁_not_central_S :
    ¬ Q₁ ≤ centralizerWithin U S
  q_mem_tau1 : q ∈ tau1Primes M
  q_mem_centralizer_index :
    q ∈ primeSupport
      ((centralizerWithin E A).subgroupOf E).index
  q_mem_centralizer_card :
    q ∈ primeSupport (Nat.card (centralizerWithin E A))

/-- The common prime used in the noncentral half of the abelian Sylow
argument.  This is the subgroup-form port of the calculation from
`q ∈ π(U / C_U(S))` through the two hypotheses of Lemma 12.11(c). -/
private theorem exists_noncentralTau2PrimeData_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U E₁ E₂ E₃ A : Subgroup G} {p : ℕ} [Fact p.Prime]
    (S : Sylow p G)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hHallU : IsHall (primeSupport (Nat.card U)) (U.subgroupOf E))
    (hUnormal : (U.subgroupOf E).Normal)
    (hregular : FTTypeFRegularity M U)
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hAS : A ≤ (S : Subgroup G))
    (hSE : (S : Subgroup G) ≤ E)
    (hSU : (S : Subgroup G) ≤ U)
    (hScomm : IsMulCommutative (S : Subgroup G))
    (hUnormS : U ≤
      Subgroup.normalizer ((S : Subgroup G) : Set G))
    (hOmegaA :
      (omegaOne p (S : Subgroup G)).map
        (S : Subgroup G).subtype = A)
    (habel : AbelianTau2Conclusion M E E₁ E₂ E₃ A
      (S : Subgroup G))
    (hnoncentral :
      ¬ U ≤ Subgroup.centralizer ((S : Subgroup G) : Set G)) :
    Nonempty (NoncentralTau2PrimeData12_12 M E U A
      (S : Subgroup G)) := by
  classical
  let C : Subgroup G :=
    centralizerWithin U (S : Subgroup G)
  have hCrelNe : C.relIndex U ≠ 1 := by
    intro hrel
    have hUC : U ≤ C := Subgroup.relIndex_eq_one.mp hrel
    apply hnoncentral
    intro u hu
    exact (hUC hu).2
  obtain ⟨q, hq, hqRel⟩ := Nat.exists_prime_and_dvd hCrelNe
  letI : Fact q.Prime := ⟨hq⟩
  have hqCindex : q ∣ (C.subgroupOf U).index := by
    simpa only [C, Subgroup.relIndex] using hqRel
  have hqU : q ∣ Nat.card U :=
    hqRel.trans (Subgroup.relIndex_dvd_card C U)
  let P₁ : Sylow q U := Classical.choice Sylow.nonempty
  have hP₁ne : (P₁ : Subgroup U) ≠ ⊥ :=
    P₁.ne_bot_of_dvd_card hqU
  let Q₁ : Subgroup G := ambientSylow U P₁
  have hQ₁U : Q₁ ≤ U := by
    exact Subgroup.map_subtype_le _
  have hQ₁q : IsPGroup q Q₁ := P₁.isPGroup'.map U.subtype
  have hQ₁ne : Q₁ ≠ ⊥ := by
    dsimp only [Q₁, ambientSylow]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (P₁ : Subgroup U) U.subtype_injective)).mpr hP₁ne
  have hQ₁notC : ¬ Q₁ ≤ C := by
    intro hQ₁C
    have hP₁CU : (P₁ : Subgroup U) ≤ C.subgroupOf U := by
      intro x hx
      exact hQ₁C (Subgroup.mem_map_of_mem U.subtype hx)
    exact P₁.not_dvd_index
      (hqCindex.trans (Subgroup.index_dvd_of_le hP₁CU))
  have hpq : p ≠ q := by
    intro hpq
    subst q
    let SU : Sylow p U := S.subtype hSU
    have hSnormalU : (SU : Subgroup U).Normal := by
      simpa only [SU, Sylow.coe_subtype] using
        (Subgroup.normal_subgroupOf_of_le_normalizer hUnormS)
    letI : Unique (Sylow p U) :=
      Sylow.unique_of_normal SU hSnormalU
    have hP₁SU : P₁ = SU := Subsingleton.elim _ _
    have hQ₁S : Q₁ = (S : Subgroup G) := by
      dsimp only [Q₁, ambientSylow]
      rw [hP₁SU, Sylow.coe_subtype,
        Subgroup.map_subgroupOf_eq_of_le hSU]
    apply hQ₁notC
    rw [hQ₁S]
    intro x hx
    refine ⟨hSU hx, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro y hy
    exact congrArg Subtype.val
      (mul_comm (⟨y, hy⟩ : S) (⟨x, hx⟩ : S))
  have hcopSQ₁ :
      (Nat.card (S : Subgroup G)).Coprime (Nat.card Q₁) :=
    IsPGroup.coprime_card_of_ne p q hpq
      (S : Subgroup G) Q₁ S.isPGroup' hQ₁q
  have hQ₁notA :
      ¬ Q₁ ≤ centralizerWithin E A := by
    intro hQ₁A
    have hQ₁centA : Q₁ ≤ Subgroup.centralizer (A : Set G) :=
      hQ₁A.trans inf_le_right
    have hQ₁centTorsion : Q₁ ≤ Subgroup.centralizer
        ({x : G | x ∈ (S : Subgroup G) ∧ x ^ p = 1} : Set G) := by
      intro a ha
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      let xS : S := ⟨x, hx.1⟩
      have hxSpow : xS ^ p = 1 := by
        apply Subtype.ext
        exact hx.2
      have hxOmega : xS ∈ omegaOne p (S : Subgroup G) :=
        mem_omegaOne_of_pow_eq_one p hxSpow
      have hxA : x ∈ A := by
        rw [← hOmegaA]
        exact ⟨xS, hxOmega, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp (hQ₁centA ha) x hxA
    have hQ₁centS :
        Q₁ ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) :=
      coprime_abelian_pGroup_centralized_of_pTorsion_centralized
        S.isPGroup' hScomm (hQ₁U.trans hUnormS)
          hcopSQ₁ hQ₁centTorsion
    exact hQ₁notC (le_inf hQ₁U hQ₁centS)
  have hqUprime : q ∈ primeSupport (Nat.card U) := ⟨hq, hqU⟩
  obtain ⟨Q₁E, hQ₁Eambient⟩ :=
    exists_sylow_of_hall_with_same_ambient_12_12
      hq hUE hHallU hqUprime P₁
  have hQ₁sylowE : IsSylowSubgroupOf q Q₁ E :=
    ⟨Q₁E, hQ₁Eambient.symm⟩

  have hfactor : Tau1CentralizerFactor M E A :=
    tau1_cent_tau2Elem_factor hM hEM hHallE hpTau hAE hA
  let CE : Subgroup E := (centralizerWithin E A).subgroupOf E
  letI : CE.Normal := by
    simpa only [CE] using hfactor.centralizer_normal
  let πCE : E →* E ⧸ CE := QuotientGroup.mk' CE
  let Qbar : Subgroup (E ⧸ CE) := (Q₁E : Subgroup E).map πCE
  have hQbarq : IsPGroup q Qbar := Q₁E.isPGroup'.map πCE
  have hQbarne : Qbar ≠ ⊥ := by
    intro hQbar
    apply hQ₁notA
    change ambientSylow U P₁ ≤ centralizerWithin E A
    rw [← hQ₁Eambient]
    rintro _ ⟨xE, hxE, rfl⟩
    have hxMap : πCE xE ∈ Qbar :=
      Subgroup.mem_map_of_mem πCE hxE
    have hxOne : πCE xE = 1 := by
      apply Subgroup.mem_bot.mp
      rw [← hQbar]
      exact hxMap
    exact (QuotientGroup.eq_one_iff xE).mp hxOne
  have hqQbar : q ∣ Nat.card Qbar :=
    hQbarq.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hQbarne (Subgroup.card_eq_one.mp hcard))
  have hqCEindex : q ∈ primeSupport CE.index := by
    refine ⟨hq, ?_⟩
    rw [CE.index_eq_card]
    exact hqQbar.trans Qbar.card_subgroup_dvd_card
  have hqTau1 : q ∈ tau1Primes M :=
    hfactor.quotient_isPiNumber hq hqCEindex.2

  have hQ₁cyclic : IsCyclic Q₁ := by
    apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hQ₁q (mFT_odd Q₁)).mpr
    rintro ⟨X, hX⟩
    let XG : Subgroup G := X.map Q₁.subtype
    apply hqTau1.2.2.2.1
    exact ⟨XG,
      (Subgroup.map_subtype_le X).trans (hQ₁U.trans (hUE.trans hEM)),
      hX.map_of_injective Q₁.subtype Q₁.subtype_injective⟩
  let L : Subgroup G := (omegaOne q Q₁).map Q₁.subtype
  have hQ₁card : Nat.card Q₁ ≠ 1 := by
    intro hcard
    exact hQ₁ne (Subgroup.card_eq_one.mp hcard)
  have hLcard : Nat.card L = q := by
    dsimp only [L]
    rw [Subgroup.card_map_of_injective Q₁.subtype_injective]
    exact card_omegaOne_of_isCyclic_isPGroup
      hq hQ₁q hQ₁card
  have hLrank : IsElementaryAbelianOfRank q 1 L :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hLcard
  have hLq : IsPGroup q L := hLrank.isPGroup
  have hLQ₁ : L ≤ Q₁ := Subgroup.map_subtype_le _
  have hLE : L ≤ E := hLQ₁.trans (hQ₁U.trans hUE)
  let E₁E : Subgroup E := E₁.subgroupOf E
  let R₁ : Sylow q E₁E := Classical.choice Sylow.nonempty
  obtain ⟨R, hR⟩ :=
    exists_sylow_eq_map_of_sylow_hall_12_11
      hq hCompl.hall_E₁ hqTau1 R₁
  obtain ⟨e, he⟩ := exists_conjugate_le_sylow_map R hLE hLq
  let X : Subgroup G := L.map (MulAut.conj (e : G)).toMonoidHom
  have hXR : X ≤ (R : Subgroup E).map E.subtype := by
    rintro x ⟨y, hy, rfl⟩
    exact he y hy
  have hRE₁ : (R : Subgroup E).map E.subtype ≤ E₁ := by
    rw [hR]
    rintro y ⟨z, hz, rfl⟩
    rcases hz with ⟨w, hw, rfl⟩
    exact w.property
  have hXE₁ : X ≤ E₁ := hXR.trans hRE₁
  have hXrank : IsElementaryAbelianOfRank q 1 X :=
    hLrank.map_of_injective (MulAut.conj (e : G)).toMonoidHom
      (MulAut.conj (e : G)).injective
  have heNormU : (e : G) ∈ Subgroup.normalizer (U : Set G) :=
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hUE).mp hUnormal)
      e.property
  have hUmap : U.map (MulAut.conj (e : G)).toMonoidHom = U :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp heNormU
  have hXU : X ≤ U := by
    exact (Subgroup.map_mono (hLQ₁.trans hQ₁U)).trans_eq hUmap
  have hXcard : Nat.card X = q := by
    rw [Subgroup.card_map_of_injective (MulAut.conj (e : G)).injective]
    exact hLcard
  have hqX : q ∣ Nat.card X := by rw [hXcard]
  obtain ⟨x, hxOrder⟩ :=
    exists_prime_orderOf_dvd_card' (G := X) q hqX
  have hxOrderG : orderOf (x : G) = q := by
    simpa using
      (orderOf_injective X.subtype X.subtype_injective x).trans
        hxOrder
  have hxne : (x : G) ≠ 1 := by
    intro hxOne
    have : orderOf (x : G) = 1 := orderOf_eq_one_iff.mpr hxOne
    rw [hxOrderG] at this
    exact hq.ne_one this
  have hxPi : IsPiNumber (tau1Primes M ∪ tau3Primes M)
      (orderOf (x : G)) := by
    intro r hr hrOrder
    rw [hxOrderG] at hrOrder
    rcases (Nat.dvd_prime hq).mp hrOrder with hrOne | hrq
    · exact (hr.ne_one hrOne).elim
    · subst r
      exact Or.inl hqTau1
  have hxRegular := hregular (hXU x.property) hxne hxPi
  have hcycleX : Subgroup.zpowers (x : G) = X := by
    apply Subgroup.eq_of_le_of_card_ge
    · exact Subgroup.zpowers_le.mpr x.property
    · rw [Nat.card_zpowers, hxOrderG, hXcard]
  have hXRegular :
      centralizerWithin (sigmaCore M) X = ⊥ := by
    rw [← hcycleX]
    exact hxRegular
  have hXcenter : X ≤ centerWithin E :=
    habel.regular_rank_one_central ⟨hXE₁, hXrank⟩ hXRegular
  have hXCE : X ≤ centralizerWithin E A := by
    intro x hx
    refine ⟨(hXcenter hx).1, ?_⟩
    apply Subgroup.mem_centralizer_iff.mpr
    intro a ha
    exact Subgroup.mem_centralizer_iff.mp (hXcenter hx).2 a (hAE ha)
  have hqCEcard : q ∈ primeSupport
      (Nat.card (centralizerWithin E A)) :=
    ⟨hq, by
      rw [← hXcard]
      exact Subgroup.card_dvd_of_le hXCE⟩
  exact ⟨
    { q := q
      q_prime := hq
      Q₁ := Q₁
      Q₁_sylow_E := hQ₁sylowE
      Q₁_le_U := hQ₁U
      Q₁_not_central_S := hQ₁notC
      q_mem_tau1 := hqTau1
      q_mem_centralizer_index := by simpa only [CE] using hqCEindex
      q_mem_centralizer_card := hqCEcard }⟩

/-- Construct the cyclic regular factor attached to one nontrivial Sylow
subgroup of `E₂ ⊓ U` in the abelian case. -/
private theorem exists_cyclicRegularTau2Factor_abelian_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hHallU : IsHall (primeSupport (Nat.card U)) (U.subgroupOf E))
    (hUnormal : (U.subgroupOf E).Normal)
    (hregular : FTTypeFRegularity M U)
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hE₂normal : (E₂.subgroupOf E).Normal)
    (hE₂comm : IsMulCommutative E₂)
    (hE₂Hall : IsHall (tau2Primes M) E₂)
    {p : ℕ} [Fact p.Prime] (P : Sylow p (E₂ ⊓ U : Subgroup G))
    (hPne : (P : Subgroup (E₂ ⊓ U : Subgroup G)) ≠ ⊥) :
    Nonempty (CyclicRegularTau2Factor M U (E₂ ⊓ U) P) := by
  classical
  have hpP : p ∣ Nat.card P :=
    P.isPGroup'.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hPne (Subgroup.card_eq_one.mp hcard))
  have hpU₂ : p ∣ Nat.card (E₂ ⊓ U : Subgroup G) :=
    hpP.trans (P : Subgroup (E₂ ⊓ U : Subgroup G)).card_subgroup_dvd_card
  have hpTau : p ∈ tau2Primes M := by
    apply hCompl.hall_E₂.isPiNumber_card Fact.out
    simpa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      hCompl.E₂_le_E] using
      hpU₂.trans (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨S, hSambient⟩ :=
    exists_ambient_sylow_eq_of_tau2_inf_12_12
      (M := M) (E := E) (U := U) (E₂ := E₂)
      Fact.out hpTau hCompl.E₂_le_E hE₂normal hE₂Hall
        hUE hHallU P hPne
  have hSE₂ : (S : Subgroup G) ≤ E₂ := by
    rw [hSambient]
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  have hSE : (S : Subgroup G) ≤ E := hSE₂.trans hCompl.E₂_le_E
  have hSU : (S : Subgroup G) ≤ U := by
    rw [hSambient]
    exact (Subgroup.map_subtype_le _).trans inf_le_right
  have hScomm : IsMulCommutative (S : Subgroup G) :=
    isMulCommutative_of_le_12_12 hSE₂ hE₂comm
  have hSne : (S : Subgroup G) ≠ ⊥ := by
    rw [hSambient]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (P : Subgroup (E₂ ⊓ U : Subgroup G))
      (E₂ ⊓ U).subtype_injective)).mpr hPne

  obtain ⟨A₀, hA₀E, _hA₀M, hA₀⟩ :=
    ex_tau2Elem hEM hHallE hpTau
  obtain ⟨R, hA₀R⟩ := hA₀.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R S
  let A : Subgroup G :=
    A₀.map (MulAut.conj g).toMonoidHom
  have hRmap :
      (R : Subgroup G).map (MulAut.conj g).toMonoidHom =
        (S : Subgroup G) := by
    change MulAut.conj g • (R : Subgroup G) = (S : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  have hAS : A ≤ (S : Subgroup G) := by
    dsimp only [A]
    exact (Subgroup.map_mono hA₀R).trans_eq hRmap
  have hAE : A ≤ E := hAS.trans hSE
  have hA : IsElementaryAbelianOfRank p 2 A :=
    hA₀.map_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective
  have habel :
      AbelianTau2Conclusion M E E₁ E₂ E₃ A (S : Subgroup G) :=
    abelian_tau2 S hM hCompl hpTau hAE hA hAS hScomm
  have hEnormE₂ :
      E ≤ Subgroup.normalizer (E₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCompl.E₂_le_E).mp
      hE₂normal
  have hEnormS :
      E ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
    rw [habel.normalizer_S_eq_E₂]
    exact hEnormE₂
  have hUnormS :
      U ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
    hUE.trans hEnormS
  let SM : Sylow p M := S.subtype (hSE.trans hEM)
  have hAmbientSM : ambientSylow M SM = (S : Subgroup G) := by
    dsimp only [SM, ambientSylow]
    rw [Sylow.coe_subtype,
      Subgroup.map_subgroupOf_eq_of_le (hSE.trans hEM)]
  have hTau := tau2_context hM hpTau (hAE.trans hEM) hA
  have hOmegaA :
      (omegaOne p (S : Subgroup G)).map
        (S : Subgroup G).subtype = A := by
    calc
      (omegaOne p (S : Subgroup G)).map
          (S : Subgroup G).subtype =
          (omegaOne p (ambientSylow M SM)).map
            (ambientSylow M SM).subtype :=
        congrArg
          (fun R : Subgroup G ↦
            (omegaOne p R).map R.subtype) hAmbientSM.symm
      _ = A := hTau.omegaOne_eq SM (hAS.trans hAmbientSM.ge)
  have hNSnotM :
      ¬ Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M := by
    simpa only [hAmbientSM] using
      hTau.normalizer_sylow_not_le SM
        (hAS.trans hAmbientSM.ge)
  have hRankTwoS :
      HasElementaryAbelianRankAtLeast p 2 (S : Subgroup G) :=
    ⟨A, hAS, hA⟩
  have hNoRankThreeS :
      ¬ HasElementaryAbelianRankAtLeast p 3 (S : Subgroup G) := by
    rintro ⟨B, hBS, hB⟩
    exact hpTau.2.2.2 ⟨B, hBS.trans (hSE.trans hEM), hB⟩

  by_cases hUScent :
      U ≤ Subgroup.centralizer ((S : Subgroup G) : Set G)
  · exact exists_cyclicRegularTau2Factor_of_central_12_12
      P S hM hEM hHallE hpTau hAE hA hAS hSE hSU
        hScomm hSne hUScent hSambient
  · obtain ⟨D⟩ :=
      exists_noncentralTau2PrimeData_12_12 S hM hEM hHallE hUE hHallU
        hUnormal hregular hCompl hpTau hAE hA hAS hSE hSU hScomm
          hUnormS hOmegaA habel hUScent
    let q : ℕ := D.q
    letI : Fact q.Prime := ⟨D.q_prime⟩
    have hqTau2HData : ∀ {H : Subgroup G},
        H ∈ minSimple_max_groups (G := G) →
        Subgroup.normalizer (A : Set G) ≤ H →
        PrimesNormTau2ElemCommonPrime H p q := by
      intro H hH hNAH
      exact (primes_norm_tau2Elem hM hEM hHallE hpTau hAE hA
        hH hNAH).common_prime_structure
          D.q_mem_centralizer_index D.q_mem_centralizer_card
    have hNAproper : Subgroup.normalizer (A : Set G) < ⊤ :=
      mFT_norm_proper A hA.ne_bot
        (mFT_pgroup_proper A hA.isPGroup)
    obtain ⟨H, hH, hNAH⟩ :=
      mmax_exists (Subgroup.normalizer (A : Set G)) hNAproper
    let common : PrimesNormTau2ElemCommonPrime H p q :=
      hqTau2HData hH hNAH
    have hNSH :
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ H := by
      rw [← habel.normalizer_A_eq_S]
      exact hNAH
    have hSH : (S : Subgroup G) ≤ H :=
      Subgroup.le_normalizer.trans hNSH
    have hpA : p ∣ Nat.card A := by
      rw [hA.card_eq]
      exact dvd_pow_self p (by omega)
    have hpG : p ∣ Nat.card G :=
      hpA.trans A.card_subgroup_dvd_card
    have hP₂ne : (common.pSylow : Subgroup G) ≠ ⊥ :=
      common.pSylow.ne_bot_of_dvd_card hpG
    let SH : Sylow p H := S.subtype hSH
    let P₂H : Sylow p H := common.pSylow.subtype common.pSylow_le
    have hP₂Hnormal : (P₂H : Subgroup H).Normal := by
      simpa only [P₂H, Sylow.coe_subtype] using common.pSylow_normal
    letI : Unique (Sylow p H) :=
      Sylow.unique_of_normal P₂H hP₂Hnormal
    have hSP₂ : S = common.pSylow := by
      apply Sylow.subtype_injective
      exact (Subsingleton.elim SH P₂H)
    have hNSH_eq :
        Subgroup.normalizer ((S : Subgroup G) : Set G) = H := by
      rw [hSP₂]
      exact mmax_normal hH common.pSylow_le
        common.pSylow_normal hP₂ne

    have hQ₁H : D.Q₁ ≤ H :=
      D.Q₁_le_U.trans (hUnormS.trans hNSH_eq.le)
    let Q₁H : Subgroup H := D.Q₁.subgroupOf H
    have hQ₁Hq : IsPGroup q Q₁H :=
      D.Q₁_sylow_E.isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe hQ₁H).symm
    obtain ⟨QH, hQ₁HQH⟩ := hQ₁Hq.exists_le_sylow
    let Q : Subgroup G := ambientSylow H QH
    have hQ₁Q : D.Q₁ ≤ Q := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hQ₁H]
      exact Subgroup.map_mono hQ₁HQH
    have hQHsub : Q ≤ H := Subgroup.map_subtype_le _
    have hQnormS :
        Q ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      hQHsub.trans hNSH_eq.ge
    have hQq : IsPGroup q Q := QH.isPGroup'.map H.subtype
    obtain ⟨Bq, hBqH, hBq⟩ := common.q_mem_tau2.2.2.1
    have hTauQ := tau2_context hH common.q_mem_tau2 hBqH hBq
    have hQcomm : IsMulCommutative Q := hTauQ.sylow_abelian QH
    have hQsylowH : IsSylowSubgroupOf q Q H := ⟨QH, rfl⟩
    obtain ⟨B, hBQ, hB⟩ :=
      exists_elementaryAbelian_le_ambientSylow_12_12
        hQsylowH common.q_mem_tau2.2.2.1
    have hQrank : HasElementaryAbelianRankAtLeast q 2 Q :=
      ⟨B, hBQ, hB⟩
    have hQ₁cyclic : IsCyclic D.Q₁ := by
      apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        D.Q₁_sylow_E.isPGroup (mFT_odd D.Q₁)).mpr
      rintro ⟨Y, hY⟩
      let YG : Subgroup G := Y.map D.Q₁.subtype
      apply D.q_mem_tau1.2.2.2.1
      exact ⟨YG,
        (Subgroup.map_subtype_le Y).trans
          (D.Q₁_le_U.trans (hUE.trans hEM)),
        hY.map_of_injective D.Q₁.subtype D.Q₁.subtype_injective⟩
    let Q₀ : Subgroup G := centralizerWithin Q (S : Subgroup G)
    have hfit := abelian_tau2_sub_Fitting S hM hEM hHallE hpTau
      hAE hA hAS hScomm
    have hQ₀E : Q₀ ≤ E := by
      exact inf_le_right.trans hfit.centralizer_le_complement
    rcases D.Q₁_sylow_E with ⟨Q₁E, hQ₁E⟩
    have hQinfE : Q ⊓ E = D.Q₁ := by
      let R : Subgroup E := (Q ⊓ E).subgroupOf E
      have hRq : IsPGroup q R :=
        (hQq.to_le inf_le_left).of_equiv
          (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
      have hQ₁inf : D.Q₁ ≤ Q ⊓ E :=
        le_inf hQ₁Q (by
          rw [hQ₁E]
          exact Subgroup.map_subtype_le _)
      have hQ₁ER : (Q₁E : Subgroup E) ≤ R := by
        intro x hx
        apply hQ₁inf
        rw [hQ₁E]
        exact Subgroup.mem_map_of_mem E.subtype hx
      have hREQ : R = (Q₁E : Subgroup E) :=
        Q₁E.is_maximal' hRq hQ₁ER
      calc
        Q ⊓ E = R.map E.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le inf_le_right).symm
        _ = (Q₁E : Subgroup E).map E.subtype :=
          congrArg (Subgroup.map E.subtype) hREQ
        _ = D.Q₁ := hQ₁E.symm
    have hQ₀Q₁ : Q₀ ≤ D.Q₁ := by
      rw [← hQinfE]
      exact le_inf inf_le_left hQ₀E
    have hQ₀ltQ₁ : Q₀ < D.Q₁ := by
      refine lt_of_le_of_ne hQ₀Q₁ ?_
      intro hEq
      apply D.Q₁_not_central_S
      rw [← hEq]
      exact le_inf (hQ₀Q₁.trans D.Q₁_le_U) inf_le_right
    have hSsol : IsSolvable (S : Subgroup G) :=
      Submission.OddOrder.MathlibSupport.isSolvable_of_comm
        (fun x y : S ↦ mul_comm x y)
    obtain ⟨X, hXQ, hcentX, hcommX⟩ :=
      exists_mixed_subgroup_of_rank_two_coprime_kernel_12_12
        hSsol hSne hQnormS hQq (mFT_odd Q) rfl
          hQ₀Q₁ hQ₁Q hQ₁cyclic hQ₀ltQ₁ hQrank
    have hXnormS :
        X ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) :=
      hXQ.trans hQnormS
    have hXq : IsPGroup q X := hQq.to_le hXQ
    have hpq : p ≠ q := by
      intro hpq
      apply (tau2'1 M D.q_mem_tau1)
      change q ∈ tau2Primes M
      rw [← hpq]
      exact hpTau
    have hcopSX :
        (Nat.card (S : Subgroup G)).Coprime (Nat.card X) :=
      IsPGroup.coprime_card_of_ne p q hpq
        (S : Subgroup G) X S.isPGroup' hXq
    obtain ⟨hCentNormal, hCommNormal⟩ :=
      abelian_tau2_norm_Sylow S hM hEM hHallE hpTau
        hAE hA hAS hScomm X hXnormS
    let NS : Subgroup G :=
      Subgroup.normalizer ((S : Subgroup G) : Set G)
    have hCentNS : centralizerWithin (S : Subgroup G) X ≤ NS :=
      (centralizerWithin_le_left (S : Subgroup G) X).trans
        Subgroup.le_normalizer
    have hCommS : ⁅(S : Subgroup G), X⁆ ≤ (S : Subgroup G) :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp hXnormS
    have hCommNS : ⁅(S : Subgroup G), X⁆ ≤ NS :=
      hCommS.trans Subgroup.le_normalizer
    have hNormCent :
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.normalizer
            (centralizerWithin (S : Subgroup G) X : Set G) := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCentNS).mp
        hCentNormal
    have hNormComm :
        Subgroup.normalizer ((S : Subgroup G) : Set G) ≤
          Subgroup.normalizer
            ((⁅(S : Subgroup G), X⁆ : Subgroup G) : Set G) := by
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCommNS).mp
        hCommNormal
    let W : CoprimeSplitWitness12_12 U (S : Subgroup G) p :=
      exists_coprime_split_witness_12_12 hSU hUnormS S.isPGroup'
        (mFT_odd (S : Subgroup G)) hScomm hRankTwoS hNoRankThreeS
          hXnormS hcopSX hcommX hcentX hNormComm hNormCent
    exact ⟨cyclicRegularTau2Factor_of_coprimeSplit_12_12
      P hM hEM hHallE hpTau hAE hA hSE hSambient hNSnotM W⟩

/-- Complementarity restricts from `E = A B` to any intermediate subgroup
`U` which contains `A`; the new right factor is `B ∩ U`. -/
private theorem isComplement_inf_right_12_12
    {G : Type u} [Group G]
    {A B E U : Subgroup G}
    (hAE : A ≤ E) (hBE : B ≤ E) (hUE : U ≤ E) (hAU : A ≤ U)
    (hcomp :
      (A.subgroupOf E).IsComplement' (B.subgroupOf E)) :
    (A.subgroupOf U).IsComplement'
      ((B ⊓ U).subgroupOf U) := by
  have hcompBij :=
    (Subgroup.isComplement_iff_bijective
      (A.subgroupOf E) (B.subgroupOf E)).mp hcomp
  apply (Subgroup.isComplement_iff_bijective
    (A.subgroupOf U) ((B ⊓ U).subgroupOf U)).mpr
  constructor
  · intro x y hxy
    let xE : A.subgroupOf E × B.subgroupOf E :=
      (⟨⟨((x.1 : U) : G), hAE x.1.property⟩, x.1.property⟩,
        ⟨⟨((x.2 : U) : G), hBE x.2.property.1⟩,
          x.2.property.1⟩)
    let yE : A.subgroupOf E × B.subgroupOf E :=
      (⟨⟨((y.1 : U) : G), hAE y.1.property⟩, y.1.property⟩,
        ⟨⟨((y.2 : U) : G), hBE y.2.property.1⟩,
          y.2.property.1⟩)
    have hxyE : (xE.1 : E) * (xE.2 : E) =
        (yE.1 : E) * (yE.2 : E) := by
      apply Subtype.ext
      exact congrArg (fun z : U ↦ (z : G)) hxy
    have heq : xE = yE := hcompBij.1 hxyE
    apply Prod.ext
    · apply Subtype.ext
      apply U.subtype_injective
      exact congrArg (fun z : A.subgroupOf E ↦ ((z : E) : G))
        (congrArg Prod.fst heq)
    · apply Subtype.ext
      apply U.subtype_injective
      exact congrArg (fun z : B.subgroupOf E ↦ ((z : E) : G))
        (congrArg Prod.snd heq)
  · intro u
    let uE : E := ⟨(u : G), hUE u.property⟩
    obtain ⟨⟨a, b⟩, hab⟩ := hcompBij.2 uE
    have habG : ((a : E) : G) * ((b : E) : G) = (u : G) :=
      congrArg (fun z : E ↦ (z : G)) hab
    have hbU : ((b : E) : G) ∈ U := by
      have hbEq : ((b : E) : G) = ((a : E) : G)⁻¹ * (u : G) := by
        rw [← habG]
        simp
      rw [hbEq]
      exact U.mul_mem (U.inv_mem (hAU a.property)) u.property
    let aU : A.subgroupOf U :=
      ⟨⟨((a : E) : G), hAU a.property⟩, a.property⟩
    let bU : (B ⊓ U).subgroupOf U :=
      ⟨⟨((b : E) : G), hbU⟩, b.property, hbU⟩
    refine ⟨(aU, bU), ?_⟩
    apply Subtype.ext
    exact habG

/-- If a prime-order normal factor is split off from a finite group, an
abelian Sylow subgroup prevents that split from lowering the exponent once
the complementary factor still has nontrivial `p`-part. -/
private theorem exponent_complement_eq_of_prime_kernel_12_12
    {K : Type u} [Group K] [Finite K]
    {A B : Subgroup K} {p : ℕ}
    (hp : p.Prime) (hAcard : Nat.card A = p)
    (hAnormal : A.Normal) (hcomp : A.IsComplement' B)
    (hpB : p ∣ Nat.card B)
    (hSylowComm : ∀ P : Sylow p K,
      IsMulCommutative (P : Subgroup K)) :
    Monoid.exponent B = Monoid.exponent K := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  letI : A.Normal := hAnormal
  letI : IsCyclic A := isCyclic_of_prime_card hAcard
  have hExpA : Monoid.exponent A = p :=
    IsCyclic.exponent_eq_card.trans hAcard
  have hBdK : Monoid.exponent B ∣ Monoid.exponent K :=
    Monoid.exponent_dvd_of_monoidHom B.subtype B.subtype_injective
  have hKdBp : Monoid.exponent K ∣ Monoid.exponent B * p := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro k
    obtain ⟨⟨a, b⟩, hab⟩ := hcomp.2 k
    have hqpow : k ^ Monoid.exponent B ∈ A := by
      let qA : K →* K ⧸ A := QuotientGroup.mk' A
      apply (QuotientGroup.eq_one_iff (N := A)
        (k ^ Monoid.exponent B)).mp
      change qA (k ^ Monoid.exponent B) = 1
      rw [map_pow, ← hab, map_mul]
      have haOne : qA (a : K) = 1 :=
        (QuotientGroup.eq_one_iff (N := A) (a : K)).2 a.property
      have hbpow : (b : K) ^ Monoid.exponent B = 1 :=
        B.pow_exponent_eq_one b.property
      rw [haOne, one_mul, ← map_pow, hbpow, map_one]
    rw [pow_mul]
    simpa [hExpA] using A.pow_exponent_eq_one hqpow

  let PB : Sylow p B := Classical.choice Sylow.nonempty
  let BP : Subgroup K := (PB : Subgroup B).map B.subtype
  have hBPp : IsPGroup p BP := PB.isPGroup'.map B.subtype
  have hBPB : BP ≤ B := Subgroup.map_subtype_le _
  have hpBP : p ∣ Nat.card BP := by
    dsimp only [BP]
    rw [Subgroup.card_map_of_injective B.subtype_injective]
    exact PB.dvd_card_of_dvd_card hpB
  have hAp : IsPGroup p A := by
    apply IsPGroup.of_card (n := 1)
    simpa [pow_one] using hAcard
  have hBPnormA : BP ≤ Subgroup.normalizer (A : Set K) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr hAnormal]
    exact le_top
  have hsupP : IsPGroup p (A ⊔ BP : Subgroup K) :=
    hAp.to_sup_of_normal_left' hBPp hBPnormA
  obtain ⟨P, hsupLeP⟩ := hsupP.exists_le_sylow
  have hAP : A ≤ (P : Subgroup K) := le_sup_left.trans hsupLeP
  have hBPP : BP ≤ (P : Subgroup K) := le_sup_right.trans hsupLeP
  let C : Subgroup K := B ⊓ (P : Subgroup K)
  have hBPC : BP ≤ C := le_inf hBPB hBPP
  have hpC : p ∣ Nat.card C :=
    hpBP.trans (Subgroup.card_dvd_of_le hBPC)
  have hpExpC : p ∣ Monoid.exponent C := by
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' (G := C) p hpC
    simpa [hc] using Monoid.order_dvd_exponent c

  let AP : Subgroup P := A.subgroupOf (P : Subgroup K)
  let CP : Subgroup P := C.subgroupOf (P : Subgroup K)
  have hcompP : AP.IsComplement' CP := by
    have hcompBij :=
      (Subgroup.isComplement_iff_bijective A B).mp hcomp
    apply (Subgroup.isComplement_iff_bijective AP CP).mpr
    constructor
    · intro x y hxy
      let xK : A × B :=
        (⟨((x.1 : P) : K), x.1.property⟩,
          ⟨((x.2 : P) : K), x.2.property.1⟩)
      let yK : A × B :=
        (⟨((y.1 : P) : K), y.1.property⟩,
          ⟨((y.2 : P) : K), y.2.property.1⟩)
      have hxyK : (xK.1 : K) * (xK.2 : K) =
          (yK.1 : K) * (yK.2 : K) := by
        exact congrArg (fun z : P ↦ (z : K)) hxy
      have heq : xK = yK := hcompBij.1 hxyK
      apply Prod.ext
      · apply Subtype.ext
        apply (P : Subgroup K).subtype_injective
        exact congrArg (fun z : A ↦ (z : K)) (congrArg Prod.fst heq)
      · apply Subtype.ext
        apply (P : Subgroup K).subtype_injective
        exact congrArg (fun z : B ↦ (z : K)) (congrArg Prod.snd heq)
    · intro x
      obtain ⟨⟨a, b⟩, hab⟩ := hcompBij.2 (x : K)
      have hbP : (b : K) ∈ (P : Subgroup K) := by
        have hbEq : (b : K) = (a : K)⁻¹ * (x : K) := by
          rw [← hab]
          simp
        rw [hbEq]
        exact (P : Subgroup K).mul_mem
          ((P : Subgroup K).inv_mem (hAP a.property)) x.property
      let aP : AP := ⟨⟨(a : K), hAP a.property⟩, a.property⟩
      let bP : CP := ⟨⟨(b : K), hbP⟩, b.property, hbP⟩
      refine ⟨(aP, bP), ?_⟩
      apply Subtype.ext
      exact hab
  letI : IsMulCommutative (P : Subgroup K) := hSylowComm P
  have hCPnormAP : CP ≤ Subgroup.normalizer (AP : Set P) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor <;> intro ha
    · simpa [mul_comm] using ha
    · simpa [mul_comm] using ha
  have hdirSup : IsInternalDirectProductIn AP CP (AP ⊔ CP) :=
    { left_le := le_sup_left
      right_le := le_sup_right
      complement :=
        subgroupOf_sup_isComplement_12_12 hCPnormAP hcompP.disjoint
      commute := fun x y ↦ by
        exact mul_comm (x : P) (y : P) }
  have hdir : IsInternalDirectProductIn AP CP (⊤ : Subgroup P) := by
    simpa only [hcompP.sup_eq_top] using hdirSup
  have hExpAP : Monoid.exponent AP = Monoid.exponent A :=
    Monoid.exponent_eq_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hAP)
  have hCPK : C ≤ (P : Subgroup K) := inf_le_right
  have hExpCP : Monoid.exponent CP = Monoid.exponent C :=
    Monoid.exponent_eq_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hCPK)
  have hExpP : Monoid.exponent P =
      Nat.lcm (Monoid.exponent A) (Monoid.exponent C) := by
    calc
      Monoid.exponent P = Monoid.exponent (⊤ : Subgroup P) :=
        Subgroup.exponent_top.symm
      _ = Monoid.exponent (AP × CP) :=
        (Monoid.exponent_eq_of_mulEquiv hdir.mulEquiv).symm
      _ = Nat.lcm (Monoid.exponent AP) (Monoid.exponent CP) :=
        Monoid.exponent_prod
      _ = Nat.lcm (Monoid.exponent A) (Monoid.exponent C) := by
        rw [hExpAP, hExpCP]
  have hExpP_eq : Monoid.exponent P = Monoid.exponent C := by
    rw [hExpP, hExpA]
    exact Nat.lcm_eq_right_iff_dvd.mpr hpExpC
  have hCdB : Monoid.exponent C ∣ Monoid.exponent B :=
    Monoid.exponent_dvd_of_monoidHom
      (Subgroup.inclusion inf_le_left)
      (Subgroup.inclusion_injective inf_le_left)
  have hPdB : Monoid.exponent P ∣ Monoid.exponent B := by
    rw [hExpP_eq]
    exact hCdB

  obtain ⟨g, hgOrder⟩ :=
    hp.exists_orderOf_eq_pow_factorization_exponent (G := K)
  have hgPelt : IsPElement p g := by
    refine ⟨(Monoid.exponent K).factorization p, ?_⟩
    apply orderOf_dvd_iff_pow_eq_one.mp
    rw [hgOrder]
  obtain ⟨Q, hgQ⟩ := hgPelt.zpowers_isPGroup.exists_le_sylow
  have hgmemQ : g ∈ (Q : Subgroup K) :=
    hgQ (Subgroup.mem_zpowers g)
  have hgOrderDvdQ : orderOf g ∣ Monoid.exponent Q := by
    have h := Monoid.order_dvd_exponent (⟨g, hgmemQ⟩ : Q)
    calc
      orderOf g = orderOf (⟨g, hgmemQ⟩ : Q) :=
        orderOf_injective (Q : Subgroup K).subtype
          (Q : Subgroup K).subtype_injective
          (⟨g, hgmemQ⟩ : Q)
      _ ∣ Monoid.exponent Q := h
  have hExpQP : Monoid.exponent Q = Monoid.exponent P :=
    Monoid.exponent_eq_of_mulEquiv (Sylow.equiv Q P)
  have hmaxPdB :
      p ^ (Monoid.exponent K).factorization p ∣ Monoid.exponent B := by
    calc
      p ^ (Monoid.exponent K).factorization p = orderOf g :=
        hgOrder.symm
      _ ∣ Monoid.exponent Q := hgOrderDvdQ
      _ = Monoid.exponent P := hExpQP
      _ ∣ Monoid.exponent B := hPdB

  obtain ⟨c, hc⟩ := hBdK
  have hcDp : c ∣ p := by
    rw [hc] at hKdBp
    exact (Nat.mul_dvd_mul_iff_left
      (Nat.pos_of_ne_zero
        (Monoid.exponent_ne_zero_of_finite (G := B)))).mp hKdBp
  rcases (Nat.dvd_prime hp).mp hcDp with hcOne | hcP
  · rw [hc, hcOne, mul_one]
  · exfalso
    subst c
    have hfac : (Monoid.exponent K).factorization p =
        (Monoid.exponent B).factorization p + 1 := by
      rw [hc, Nat.factorization_mul
        Monoid.exponent_ne_zero_of_finite hp.ne_zero]
      simp [hp]
    rw [hfac] at hmaxPdB
    exact Nat.pow_succ_factorization_not_dvd
      Monoid.exponent_ne_zero_of_finite hp hmaxPdB

/-- Clause (a) of the generalized Type-F conclusion. -/
structure FTTypeFFixedPointConclusion
    {G : Type u} [Group G]
    (M U : Subgroup G) where
  fixedPointSubgroup : Subgroup G
  fixedPoint_le_U : fixedPointSubgroup ≤ U
  fixedPoint_normal : (fixedPointSubgroup.subgroupOf U).Normal
  fixedPoint_abelian : IsMulCommutative fixedPointSubgroup
  fixedPoint_control :
    ∀ {x : G}, x ∈ sigmaCore M → x ≠ 1 →
      centralizerWithin U (Subgroup.zpowers x) ≤ fixedPointSubgroup

/-- Clause (b) of the generalized Type-F conclusion.

The displayed semidirect product and Frobenius decomposition together are
the Lean form of `[Frobenius M_sigma <*> U₀ = M_sigma ><| U₀]`. -/
structure FTTypeFFrobeniusComplement
    {G : Type u} [Group G]
    (M U : Subgroup G) where
  complement : Subgroup G
  complement_le_U : complement ≤ U
  exponent_eq : Monoid.exponent complement = Monoid.exponent U
  semidirect :
    IsInternalSemidirectProductIn (sigmaCore M) complement
      (sigmaCore M ⊔ complement)
  frobenius :
    IsFrobeniusDecomposition
      ((sigmaCore M).subgroupOf (sigmaCore M ⊔ complement))
      (complement.subgroupOf (sigmaCore M ⊔ complement))

/-- Package a same-exponent semiregular subgroup as the Type-F Frobenius
complement required by Theorem 12.12. -/
private noncomputable def FTtypeF_frobenius_of_semiregular_12_12
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U U₀ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hU₀U : U₀ ≤ U)
    (hExp : Monoid.exponent U₀ = Monoid.exponent U)
    (hreg : IsSemiregularConjugation (sigmaCore M) U₀)
    (hUne : U ≠ ⊥) :
    FTTypeFFrobeniusComplement M U := by
  have hU₀ne : U₀ ≠ ⊥ := by
    intro hbot
    have hExpU : Monoid.exponent U = 1 := by
      rw [← hExp, hbot]
      exact Monoid.exp_eq_one_of_subsingleton
    have hsub : Subsingleton U := Monoid.exp_eq_one_iff.mp hExpU
    apply hUne
    apply le_antisymm
    · intro u hu
      apply Subgroup.mem_bot.mpr
      exact congrArg Subtype.val
        (hsub.elim (⟨u, hu⟩ : U) 1)
    · exact bot_le
  have hMnormSigma :
      M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer
      (sigmaCore_le M)).mp (sigmaCore_normal M)
  have hU₀normSigma :
      U₀ ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (hU₀U.trans hUE).trans (hEM.trans hMnormSigma)
  exact
    { complement := U₀
      complement_le_U := hU₀U
      exponent_eq := hExp
      semidirect := sigma_subgroup_semidirect_12_12 hM hEM hHallE
        (hU₀U.trans hUE)
      frobenius := by
        have hF :=
          IsSemiregularConjugation.isFrobeniusDecomposition_sup
            hreg hU₀normSigma (Msigma_neq1 hM) hU₀ne
        rw [sup_comm U₀ (sigmaCore M)] at hF
        exact hF }

/-- The generalized conclusion of Bender--Glauberman Theorem 12.12.

The source assumes `U ≠ 1`.  Here that hypothesis is localized to the
Frobenius-complement clause, which is the form used by the later Section 15
port. -/
structure FTTypeFComplementConclusion
    {G : Type u} [Group G]
    (M U : Subgroup G) where
  fixedPoint : FTTypeFFixedPointConclusion M U
  frobenius : U ≠ ⊥ → FTTypeFFrobeniusComplement M U

/-- Clause (a) of Theorem 12.12 when the `tau2` Hall factor meets `U`
nontrivially. -/
private theorem exists_FTtypeF_nontrivial_fixedPoint
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hHallU : IsHall (primeSupport (Nat.card U)) (U.subgroupOf E))
    (hUnormal : (U.subgroupOf E).Normal)
    (hregular : FTTypeFRegularity M U)
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hnontrivial : E₂ ⊓ U ≠ ⊥) :
    Nonempty (FTTypeFFixedPointConclusion M U) := by
  classical
  let U₂ : Subgroup G := E₂ ⊓ U
  have hU₂card : Nat.card U₂ ≠ 1 := by
    intro hcard
    exact hnontrivial (Subgroup.card_eq_one.mp hcard)
  obtain ⟨p, hp, hpU₂⟩ := Nat.exists_prime_and_dvd hU₂card
  letI : Fact p.Prime := ⟨hp⟩
  have hpTau : p ∈ tau2Primes M := by
    apply hCompl.hall_E₂.isPiNumber_card hp
    simpa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      hCompl.E₂_le_E] using
      hpU₂.trans (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨A, hAE, _hAM, hA⟩ := ex_tau2Elem hEM hHallE hpTau
  obtain ⟨S, hAS⟩ := hA.isPGroup.exists_le_sylow
  by_cases hScomm : IsMulCommutative (S : Subgroup G)
  · have habel := abelian_tau2 S hM hCompl hpTau hAE hA hAS hScomm
    have hU₂normal : (U₂.subgroupOf U).Normal := by
      simpa only [U₂] using
        (normal_inf_subgroupOf_of_le_12_12
          hCompl.E₂_le_E hUE habel.E₂_normal)
    have hU₂Hall :
        IsHall (tau2Primes M) (U₂.subgroupOf U) := by
      simpa only [U₂] using
        (isHall_inf_normal_of_le_12_12
          hCompl.E₂_le_E hUE hCompl.hall_E₂ hUnormal)
    have hU₂comm : IsMulCommutative U₂ :=
      isMulCommutative_of_le_12_12 inf_le_left habel.E₂_abelian
    refine ⟨
      { fixedPointSubgroup := U₂
        fixedPoint_le_U := inf_le_right
        fixedPoint_normal := hU₂normal
        fixedPoint_abelian := hU₂comm
        fixedPoint_control := ?_ }⟩
    intro x hxSigma hxne
    let Cx : Subgroup G :=
      centralizerWithin U (Subgroup.zpowers x)
    have hCxPi : IsPiNumber (tau2Primes M) (Nat.card Cx) := by
      intro q hq hqCx
      have hqU : q ∣ Nat.card U :=
        hqCx.trans (Subgroup.card_dvd_of_le
          (centralizerWithin_le_left U (Subgroup.zpowers x)))
      have hqE : q ∈ primeSupport (Nat.card E) :=
        ⟨hq, hqU.trans (Subgroup.card_dvd_of_le hUE)⟩
      rcases primeSupport_sigma_complement_subset_tau_12_11
          hM hEM hHallE hqE with (hq1 | hq2) | hq3
      · exfalso
        letI : Fact q.Prime := ⟨hq⟩
        obtain ⟨y, hyOrder⟩ :=
          exists_prime_orderOf_dvd_card' (G := Cx) q hqCx
        have hyOrderG : orderOf (y : G) = q := by
          simpa using
            (orderOf_injective Cx.subtype Cx.subtype_injective y).trans
              hyOrder
        have hyne : (y : G) ≠ 1 := by
          intro hy
          have : orderOf (y : G) = 1 := orderOf_eq_one_iff.mpr hy
          rw [hyOrderG] at this
          exact hq.ne_one this
        have hyPi : IsPiNumber (tau1Primes M ∪ tau3Primes M)
            (orderOf (y : G)) := by
          intro r hr hrOrder
          have hrq : r = q :=
            Or.resolve_left
              ((Nat.dvd_prime hq).mp (by simpa [hyOrderG] using hrOrder))
              hr.ne_one
          subst r
          exact Or.inl hq1
        have hbot := hregular y.property.1 hyne hyPi
        have hxCent : x ∈
            centralizerWithin (sigmaCore M) (Subgroup.zpowers (y : G)) := by
          refine ⟨hxSigma, ?_⟩
          intro z hz
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          have hxy : Commute x (y : G) := by
            exact y.property.2 x (Subgroup.mem_zpowers x)
          exact hxy.symm.zpow_left n
        rw [hbot] at hxCent
        exact hxne (by simpa using hxCent)
      · exact hq2
      · exfalso
        letI : Fact q.Prime := ⟨hq⟩
        obtain ⟨y, hyOrder⟩ :=
          exists_prime_orderOf_dvd_card' (G := Cx) q hqCx
        have hyOrderG : orderOf (y : G) = q := by
          simpa using
            (orderOf_injective Cx.subtype Cx.subtype_injective y).trans
              hyOrder
        have hyne : (y : G) ≠ 1 := by
          intro hy
          have : orderOf (y : G) = 1 := orderOf_eq_one_iff.mpr hy
          rw [hyOrderG] at this
          exact hq.ne_one this
        have hyPi : IsPiNumber (tau1Primes M ∪ tau3Primes M)
            (orderOf (y : G)) := by
          intro r hr hrOrder
          have hrq : r = q :=
            Or.resolve_left
              ((Nat.dvd_prime hq).mp (by simpa [hyOrderG] using hrOrder))
              hr.ne_one
          subst r
          exact Or.inr hq3
        have hbot := hregular y.property.1 hyne hyPi
        have hxCent : x ∈
            centralizerWithin (sigmaCore M) (Subgroup.zpowers (y : G)) := by
          refine ⟨hxSigma, ?_⟩
          intro z hz
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          have hxy : Commute x (y : G) := by
            exact y.property.2 x (Subgroup.mem_zpowers x)
          exact hxy.symm.zpow_left n
        rw [hbot] at hxCent
        exact hxne (by simpa using hxCent)
    exact le_normal_isHall_of_isPiNumber_12_11
      hU₂normal hU₂Hall
      (centralizerWithin_le_left U (Subgroup.zpowers x)) hCxPi
  · have hnon := nonabelian_tau2 hM hEM hHallE hpTau
        hAE hA S.isPGroup' hScomm
    let A₀ : Subgroup G := centralizerWithin A (sigmaCore M)
    obtain ⟨E₀, hsd, hE₀regular⟩ := hnon.exists_complement
    have hpU : p ∈ primeSupport (Nat.card U) :=
      ⟨hp, hpU₂.trans (Subgroup.card_dvd_of_le inf_le_right)⟩
    have hA₀rank : IsElementaryAbelianOfRank p 1 A₀ :=
      isElementaryAbelianOfRank_one_of_card_eq_prime hnon.A0_card
    have hA₀U : A₀ ≤ U := by
      apply le_normal_isHall_of_isPiNumber_12_11 hUnormal hHallU
        hsd.1
      exact hA₀rank.isPGroup.isPiNumber_natCard hpU
    have hA₀normalU : (A₀.subgroupOf U).Normal := by
      apply Subgroup.normal_subgroupOf_of_le_normalizer
      have hEnormA₀ : E ≤ Subgroup.normalizer (A₀ : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hsd.1).mp hsd.2.2.1
      exact hUE.trans hEnormA₀
    have hA₀comm : IsMulCommutative A₀ :=
      isMulCommutative_of_le_12_12 inf_le_left hA.commutative
    have hE₀fix : ∀ {e x : G}, e ∈ E₀ ⊓ U →
        x ∈ sigmaCore M → x ≠ 1 →
        x * e = e * x → e = 1 := by
      intro e x he hxSigma hxne hxe
      by_cases heOne : e = 1
      · exact heOne
      · by_cases hePi :
            IsPiNumber (tau1Primes M ∪ tau3Primes M) (orderOf e)
        · have hbot := hregular he.2 heOne hePi
          have hxCent : x ∈
              centralizerWithin (sigmaCore M) (Subgroup.zpowers e) := by
            refine ⟨hxSigma, ?_⟩
            intro z hz
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
            exact (show Commute e x from hxe.symm).zpow_left n
          rw [hbot] at hxCent
          exact (hxne (by simpa using hxCent)).elim
        · exfalso
          have heCent : e ∈
              centralizerWithin E₀ (Subgroup.zpowers x) := by
            refine ⟨he.1, ?_⟩
            intro z hz
            obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
            exact (show Commute x e from hxe).zpow_left n
          have heTau1 : IsPiNumber (tau1Primes M) (orderOf e) := by
            intro q hq hqOrder
            apply hE₀regular x hxSigma hxne
            exact ⟨hq, hqOrder.trans
              ((centralizerWithin E₀ (Subgroup.zpowers x)).orderOf_dvd_natCard
                heCent)⟩
          exact hePi (heTau1.mono (fun _ hq1 ↦ Or.inl hq1))
    refine ⟨
      { fixedPointSubgroup := A₀
        fixedPoint_le_U := hA₀U
        fixedPoint_normal := hA₀normalU
        fixedPoint_abelian := hA₀comm
        fixedPoint_control := ?_ }⟩
    intro x hxSigma hxne u hu
    let uE : E := ⟨u, hUE hu.1⟩
    obtain ⟨⟨a, e⟩, hae⟩ := hsd.2.2.2.2 uE
    have haeG : (a : G) * (e : G) = u := congrArg Subtype.val hae
    have heU : (e : G) ∈ U := by
      have heEq : (e : G) = (a : G)⁻¹ * u := by
        rw [← haeG]
        simp
      rw [heEq]
      exact U.mul_mem (U.inv_mem (hA₀U a.property)) hu.1
    have hxu : x * u = u * x := hu.2 x (Subgroup.mem_zpowers x)
    have hxa : x * (a : G) = (a : G) * x :=
      a.property.2 x hxSigma
    have hxe : x * (e : G) = (e : G) * x := by
      apply mul_left_cancel (a := (a : G))
      calc
        (a : G) * (x * (e : G)) =
            (x * (a : G)) * (e : G) := by rw [hxa]; simp [mul_assoc]
        _ = x * u := by rw [← haeG, mul_assoc]
        _ = u * x := hxu
        _ = (a : G) * ((e : G) * x) := by rw [← haeG, mul_assoc]
    have heOne := hE₀fix ⟨e.property, heU⟩ hxSigma hxne hxe
    have heOneG : (e : G) = 1 := by simpa using heOne
    rw [← haeG, heOneG, mul_one]
    exact a.property

/-- Clause (b) of Theorem 12.12 in the nonabelian ambient Sylow case. -/
private theorem exists_FTtypeF_nontrivial_frobenius_nonabelian
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U E₁ E₂ E₃ A : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hHallU : IsHall (primeSupport (Nat.card U)) (U.subgroupOf E))
    (hUnormal : (U.subgroupOf E).Normal)
    (hregular : FTTypeFRegularity M U)
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hpTau : p ∈ tau2Primes M)
    (hpU : p ∣ Nat.card U)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (S : Sylow p G) (hAS : A ≤ (S : Subgroup G))
    (hSnoncomm : ¬ IsMulCommutative (S : Subgroup G))
    (hUne : U ≠ ⊥) :
    Nonempty (FTTypeFFrobeniusComplement M U) := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  let A₀ : Subgroup G := centralizerWithin A (sigmaCore M)
  have hnon := nonabelian_tau2 hM hEM hHallE hpTau
    hAE hA S.isPGroup' hSnoncomm
  obtain ⟨E₀, hsdE, hE₀regular⟩ := hnon.exists_complement
  have hpSupport : p ∈ primeSupport (Nat.card U) :=
    ⟨hpTau.1, hpU⟩
  have hA₀rank : IsElementaryAbelianOfRank p 1 A₀ :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hnon.A0_card
  have hA₀U : A₀ ≤ U := by
    apply le_normal_isHall_of_isPiNumber_12_11 hUnormal hHallU
      hsdE.1
    exact hA₀rank.isPGroup.isPiNumber_natCard hpSupport
  have hAU : A ≤ U := by
    apply le_normal_isHall_of_isPiNumber_12_11 hUnormal hHallU hAE
    exact hA.isPGroup.isPiNumber_natCard hpSupport
  let U₀ : Subgroup G := E₀ ⊓ U
  have hcompU :
      (A₀.subgroupOf U).IsComplement' (U₀.subgroupOf U) := by
    simpa only [U₀] using
      isComplement_inf_right_12_12 hsdE.1 hsdE.2.1 hUE hA₀U
        hsdE.2.2.2
  have hA₀normalU : (A₀.subgroupOf U).Normal := by
    apply Subgroup.normal_subgroupOf_of_le_normalizer
    have hEnormA₀ : E ≤ Subgroup.normalizer (A₀ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hsdE.1).mp
        hsdE.2.2.1
    exact hUE.trans hEnormA₀
  have hcardU : Nat.card A₀ * Nat.card U₀ = Nat.card U := by
    simpa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hA₀U,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        (show U₀ ≤ U from inf_le_right)] using
      hcompU.card_mul
  have hpSqU : p ^ 2 ∣ Nat.card U := by
    rw [← hA.card_eq]
    exact Subgroup.card_dvd_of_le hAU
  have hpU₀ : p ∣ Nat.card U₀ := by
    have h := hpSqU
    rw [← hcardU, hnon.A0_card, pow_two] at h
    exact (Nat.mul_dvd_mul_iff_left hpTau.1.pos).mp h
  let A₀U : Subgroup U := A₀.subgroupOf U
  let U₀U : Subgroup U := U₀.subgroupOf U
  have hA₀Ucard : Nat.card A₀U = p := by
    simpa [A₀U, A₀,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hA₀U]
      using hnon.A0_card
  have hSylowComm : ∀ P : Sylow p U,
      IsMulCommutative (P : Subgroup U) := by
    intro P
    let PG : Subgroup G := (P : Subgroup U).map U.subtype
    have hPGp : IsPGroup p PG := P.isPGroup'.map U.subtype
    have hPGM : PG ≤ M :=
      (Subgroup.map_subtype_le (P : Subgroup U)).trans (hUE.trans hEM)
    let PGM : Subgroup M := PG.subgroupOf M
    have hPGMp : IsPGroup p PGM := by
      let ePGM : PGM ≃* PG := Subgroup.subgroupOfEquivOfLe hPGM
      exact hPGp.of_equiv ePGM.symm
    obtain ⟨PM, hPGMPM⟩ := hPGMp.exists_le_sylow
    have hPGPM : PG ≤ ambientSylow M PM := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hPGM]
      exact Subgroup.map_mono hPGMPM
    have hPMcomm :=
      (tau2_context hM hpTau (hAE.trans hEM) hA).sylow_abelian PM
    have hPGcomm := isMulCommutative_of_le_12_12 hPGPM hPMcomm
    let ePG : P ≃* PG :=
      (P : Subgroup U).equivMapOfInjective
        U.subtype U.subtype_injective
    apply isMulCommutative_iff.mpr
    intro x y
    apply ePG.injective
    exact isMulCommutative_iff.mp hPGcomm (ePG x) (ePG y)
  have hExpU₀U : Monoid.exponent U₀U = Monoid.exponent U := by
    apply exponent_complement_eq_of_prime_kernel_12_12 hpTau.1
      hA₀Ucard hA₀normalU hcompU
    · simpa [U₀U,
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          (show U₀ ≤ U from inf_le_right)]
        using hpU₀
    · exact hSylowComm
  let eU₀ : U₀U ≃* U₀ :=
    Subgroup.subgroupOfEquivOfLe inf_le_right
  have hExpU₀sub : Monoid.exponent U₀U = Monoid.exponent U₀ :=
    Monoid.exponent_eq_of_mulEquiv eU₀
  have hExp : Monoid.exponent U₀ = Monoid.exponent U :=
    hExpU₀sub.symm.trans hExpU₀U
  have hcentral :
      ∀ {e : G}, e ∈ U₀ → e ≠ 1 →
        centralizerWithin (sigmaCore M) (Subgroup.zpowers e) = ⊥ := by
    intro e he heOne
    by_cases hePi :
        IsPiNumber (tau1Primes M ∪ tau3Primes M) (orderOf e)
    · exact hregular he.2 heOne hePi
    · apply le_antisymm ?_ bot_le
      intro x hx
      apply Subgroup.mem_bot.mpr
      by_contra hxne
      have heCent :
          e ∈ centralizerWithin E₀ (Subgroup.zpowers x) := by
        refine ⟨he.1, ?_⟩
        intro z hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        have hex : Commute e x :=
          hx.2 e (Subgroup.mem_zpowers e)
        exact hex.symm.zpow_left n
      have heTau1 : IsPiNumber (tau1Primes M) (orderOf e) := by
        intro q hq hqOrder
        apply hE₀regular x hx.1 hxne
        exact ⟨hq, hqOrder.trans
          ((centralizerWithin E₀ (Subgroup.zpowers x)).orderOf_dvd_natCard
            heCent)⟩
      exact (hePi (heTau1.mono (fun _ hq1 ↦ Or.inl hq1))).elim
  have hsemiregular :
      IsSemiregularConjugation (sigmaCore M) U₀ :=
    semiregular_of_zpowers_centralizer_12_12 hcentral
  exact ⟨FTtypeF_frobenius_of_semiregular_12_12
    hM hEM hHallE hUE inf_le_right hExp hsemiregular hUne⟩

/-- Complete the abelian `tau2` branch once the cyclic regular factors of
the nontrivial Sylow subgroups of `E₂ ⊓ U` have been constructed. -/
private theorem exists_FTtypeF_nontrivial_frobenius_abelian_of_factors
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hUnormal : (U.subgroupOf E).Normal)
    (hregular : FTTypeFRegularity M U)
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (factors : CyclicRegularTau2FactorFamily M U (E₂ ⊓ U))
    (hUne : U ≠ ⊥) :
    Nonempty (FTTypeFFrobeniusComplement M U) := by
  classical
  let U₂ : Subgroup G := E₂ ⊓ U
  have hHallU₂ : IsHall (tau2Primes M) (U₂.subgroupOf U) := by
    simpa only [U₂] using
      (isHall_inf_normal_of_le_12_12
        hCompl.E₂_le_E hUE hCompl.hall_E₂ hUnormal)
  have hUsolvable : IsSolvable U :=
    by
      letI : IsSolvable E := sigma_compl_sol hEM hHallE
      exact isSolvable_of_injective (Subgroup.inclusion hUE)
        (Subgroup.inclusion_injective hUE)
  have hoff : ∀ {e : G}, e ∈ U → e ≠ 1 →
      IsPiNumber (tau2Primes M)ᶜ (orderOf e) →
        centralizerWithin (sigmaCore M) (Subgroup.zpowers e) = ⊥ := by
    intro e heU heNe heTau2c
    exact hregular heU heNe
      (tau13_orderOf_of_tau2_complement_12_12
        hM hEM hHallE hUE heU heTau2c)
  have hFactors : CyclicRegularTau2FactorFamily M U U₂ := by
    simpa only [U₂] using factors
  obtain ⟨U₀, hU₀U, hExp, hsemiregular⟩ :=
    exists_tau2_selected_sylow_assembly_12_12
      (M := M) (U := U) (U₂ := U₂)
      (show U₂ ≤ U from inf_le_right) hHallU₂ hUsolvable hoff hFactors
  exact ⟨FTtypeF_frobenius_of_semiregular_12_12
    hM hEM hHallE hUE hU₀U hExp hsemiregular hUne⟩

/-- Clause (b) of Theorem 12.12 when the `tau2` Hall factor meets `U`
nontrivially.  The abelian Sylow case constructs one cyclic regular factor
at each prime and invokes the selected-Sylow assembly; the nonabelian case
uses the complement supplied by Theorem 12.7. -/
private theorem exists_FTtypeF_nontrivial_frobenius
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hHallU : IsHall (primeSupport (Nat.card U)) (U.subgroupOf E))
    (hUnormal : (U.subgroupOf E).Normal)
    (hregular : FTTypeFRegularity M U)
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hnontrivial : E₂ ⊓ U ≠ ⊥)
    (hUne : U ≠ ⊥) :
    Nonempty (FTTypeFFrobeniusComplement M U) := by
  classical
  let U₂ : Subgroup G := E₂ ⊓ U
  have hU₂card : Nat.card U₂ ≠ 1 := by
    intro hcard
    exact hnontrivial (Subgroup.card_eq_one.mp hcard)
  obtain ⟨p, hp, hpU₂⟩ := Nat.exists_prime_and_dvd hU₂card
  letI : Fact p.Prime := ⟨hp⟩
  have hpTau : p ∈ tau2Primes M := by
    apply hCompl.hall_E₂.isPiNumber_card hp
    simpa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      hCompl.E₂_le_E] using
      hpU₂.trans (Subgroup.card_dvd_of_le inf_le_left)
  obtain ⟨A, hAE, _hAM, hA⟩ := ex_tau2Elem hEM hHallE hpTau
  obtain ⟨S, hAS⟩ := hA.isPGroup.exists_le_sylow
  by_cases hScomm : IsMulCommutative (S : Subgroup G)
  · have habel := abelian_tau2 S hM hCompl hpTau hAE hA hAS hScomm
    have factors :
        CyclicRegularTau2FactorFamily M U (E₂ ⊓ U) := by
      intro q _ Q hQne
      exact Classical.choice
        (exists_cyclicRegularTau2Factor_abelian_12_12
          hM hEM hHallE hUE hHallU hUnormal hregular hCompl
            habel.E₂_normal habel.E₂_abelian habel.E₂_hall Q hQne)
    exact exists_FTtypeF_nontrivial_frobenius_abelian_of_factors
      hM hEM hHallE hUE hUnormal hregular hCompl factors hUne
  · exact exists_FTtypeF_nontrivial_frobenius_nonabelian
      hM hEM hHallE hUE hHallU hUnormal hregular hCompl
        hpTau (hpU₂.trans (Subgroup.card_dvd_of_le inf_le_right))
          hAE hA S hAS hScomm hUne

/-- `BGsection12.v: FTtypeF_complement`, the generalized
Bender--Glauberman Theorem 12.12.

The generalization allows `U` to be any normal Hall subgroup of the fixed
`sigma(M)'`-Hall subgroup `E`.  The source's nontriviality assumption is
needed only when the Frobenius complement is requested. -/
private theorem exists_FTtypeF_complement
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hHallU :
      IsHall (primeSupport (Nat.card U)) (U.subgroupOf E))
    (hUnormal : (U.subgroupOf E).Normal)
    (hregular : FTTypeFRegularity M U) :
    Nonempty (FTTypeFComplementConclusion M U) := by
  classical
  obtain ⟨⟨E₁, hE₁E, hHallE₁⟩,
      ⟨E₃, hE₃E, hHallE₃⟩⟩ := ex_tau13_compl hEM hHallE
  obtain ⟨E₂, _hE₂E, _hHallE₂, hCompl⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  by_cases htrivial : E₂ ⊓ U = ⊥
  · have hcentral :
        ∀ {x : G}, x ∈ U → x ≠ 1 →
          centralizerWithin (sigmaCore M) (Subgroup.zpowers x) = ⊥ := by
      intro x hxU hxne
      exact hregular hxU hxne
        (tau13_orderOf_of_tau2_inf_eq_bot_12_12
          hM hEM hHallE hUE hUnormal hCompl htrivial hxU)
    have hsemidirect :
        IsInternalSemidirectProductIn (sigmaCore M) U
          (sigmaCore M ⊔ U) :=
      sigma_subgroup_semidirect_12_12 hM hEM hHallE hUE
    have hMnormSigma :
        M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer
        (sigmaCore_le M)).mp (sigmaCore_normal M)
    have hUnormSigma :
        U ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
      (hUE.trans hEM).trans hMnormSigma
    have hsemiregular :
        IsSemiregularConjugation (sigmaCore M) U :=
      semiregular_of_zpowers_centralizer_12_12 hcentral
    refine ⟨
      { fixedPoint :=
          { fixedPointSubgroup := ⊥
            fixedPoint_le_U := bot_le
            fixedPoint_normal := by
              simpa using (inferInstance : (⊥ : Subgroup U).Normal)
            fixedPoint_abelian := by infer_instance
            fixedPoint_control := ?_ }
        frobenius := ?_ }⟩
    · intro x hxSigma hxne u hu
      apply Subgroup.mem_bot.mpr
      by_cases huOne : u = 1
      · exact huOne
      · have hbot := hcentral hu.1 huOne
        have hxCent : x ∈
            centralizerWithin (sigmaCore M) (Subgroup.zpowers u) := by
          refine ⟨hxSigma, ?_⟩
          intro z hz
          obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          have hux : Commute u x :=
            (hu.2 x (Subgroup.mem_zpowers x)).symm
          exact hux.zpow_left n
        rw [hbot] at hxCent
        exact (hxne (by simpa using hxCent)).elim
    · intro hU
      exact
        { complement := U
          complement_le_U := le_rfl
          exponent_eq := rfl
          semidirect := hsemidirect
          frobenius := by
            have hF :=
              IsSemiregularConjugation.isFrobeniusDecomposition_sup
                hsemiregular hUnormSigma (Msigma_neq1 hM) hU
            rw [sup_comm U (sigmaCore M)] at hF
            exact hF }
  · exact ⟨
      { fixedPoint := Classical.choice
          (exists_FTtypeF_nontrivial_fixedPoint hM hEM hHallE hUE
            hHallU hUnormal hregular hCompl htrivial)
        frobenius := fun hUne ↦ Classical.choice
          (exists_FTtypeF_nontrivial_frobenius hM hEM hHallE hUE
            hHallU hUnormal hregular hCompl htrivial hUne) }⟩

/-- `BGsection12.v: FTtypeF_complement`, the generalized
Bender--Glauberman Theorem 12.12. -/
noncomputable def FTtypeF_complement
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E U : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hUE : U ≤ E)
    (hHallU :
      IsHall (primeSupport (Nat.card U)) (U.subgroupOf E))
    (hUnormal : (U.subgroupOf E).Normal)
    (hregular : FTTypeFRegularity M U) :
    FTTypeFComplementConclusion M U :=
  Classical.choice
    (exists_FTtypeF_complement hM hEM hHallE hUE hHallU hUnormal hregular)

end

end Submission.OddOrder.BG.Section12
