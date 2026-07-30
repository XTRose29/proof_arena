import Submission.OddOrder.BG.Section12.Tau2Maximal
import Submission.OddOrder.BG.Section10.BasicMaximalStructure
import Submission.OddOrder.BG.Section10.SigmaDisjointness
import Submission.OddOrder.MathlibSupport.AmbientFitting
import Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable
import Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement
import Submission.OddOrder.MathlibSupport.FrattiniQuotientAutomorphism
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall
import Submission.OddOrder.PF.Section03.InternalDirectProduct

/-!
# Bender--Glauberman Section 12: the nonabelian `tau2` case

This file ports `BGsection12.v: nonabelian_tau2` (Theorem 12.7, lines
754--1002).  As in the source, a nonabelian ambient `p`-subgroup first
forces `tau2(M) = {p}`.  A distinguished rank-one subgroup is then selected
from the coprime centralizer generation of `M_sigma`; the rank-two Sylow
structure identifies it with `C_A(M_sigma)` and gives the remaining
centralizer and complement assertions.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section05
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

/-- The proposition-valued form of the five conclusions of
`BGsection12.v: nonabelian_tau2`. -/
structure NonabelianTau2Conclusion
    {G : Type u} [Group G] [Finite G]
    (M E : Subgroup G) (p : ℕ) (A₀ : Subgroup G) : Prop where
  tau2_eq : tau2Primes M = {p}
  A0_card : Nat.card A₀ = p
  fitting_decomposition :
    IsInternalDirectProductIn (sigmaCore M) A₀ (fittingWithin M)
  rankOne_control :
    ∀ X : Subgroup G, RankOneLineIn p E X → X ≠ A₀ →
      centralizerWithin (sigmaCore M) X = ⊥ ∧
        ¬ Subgroup.centralizer (X : Set G) ≤ M
  exists_complement :
    ∃ E₀ : Subgroup G,
      IsInternalSemidirectProductIn A₀ E₀ E ∧
        ∀ x ∈ sigmaCore M, x ≠ 1 →
          primeSupport
              (Nat.card
                (centralizerWithin E₀ (Subgroup.zpowers x))) ⊆
            tau1Primes M

/-! ## Hall--Sylow and equivariance adapters -/

/-- A Sylow subgroup of a Hall subgroup maps to a Sylow subgroup of the
ambient finite group. -/
private theorem exists_sylow_eq_map_of_sylow_hall_12_8
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

/-- Transport a fixed Sylow subgroup through a Hall inclusion without
changing its ambient carrier. -/
private theorem exists_sylow_of_hall_with_same_ambient
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
    exists_sylow_eq_map_of_sylow_hall_12_8 hp hHall hpPi PHK
  refine ⟨Q, ?_⟩
  change (Q : Subgroup K).map K.subtype =
    (P : Subgroup H).map H.subtype
  rw [hQ, Subgroup.map_map]
  simp only [PHK, Sylow.coe_mapSurjective, Subgroup.map_map]
  apply congrArg (fun f : H →* G ↦ (P : Subgroup H).map f)
  ext x
  rfl

/-- An ambient copy of a Sylow subgroup is maximal among ambient
`p`-subgroups contained in the same subgroup. -/
private theorem ambientSylow_eq_of_le
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {H : Subgroup G}
    (P : Sylow p H) {Q : Subgroup G}
    (hQp : IsPGroup p Q) (hQH : Q ≤ H)
    (hPQ : ambientSylow H P ≤ Q) :
    Q = ambientSylow H P := by
  let QH : Subgroup H := Q.subgroupOf H
  have hQHp : IsPGroup p QH :=
    hQp.of_equiv (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hPQH : (P : Subgroup H) ≤ QH := by
    intro x hx
    exact hPQ ⟨x, hx, rfl⟩
  have hQHP : QH = (P : Subgroup H) := P.is_maximal' hQHp hPQH
  calc
    Q = QH.map H.subtype :=
      (Subgroup.map_subgroupOf_eq_of_le hQH).symm
    _ = (P : Subgroup H).map H.subtype :=
      congrArg (Subgroup.map H.subtype) hQHP
    _ = ambientSylow H P := rfl

/-- Commutativity descends to a subgroup. -/
private theorem isMulCommutative_of_le_12_8
    {K : Type u} [Group K] {A B : Subgroup K}
    (hAB : A ≤ B) (hB : IsMulCommutative B) :
    IsMulCommutative A := by
  letI : IsMulCommutative B := hB
  apply isMulCommutative_iff.mpr
  intro x y
  apply Subtype.ext
  change (x : K) * (y : K) = (y : K) * (x : K)
  exact congrArg Subtype.val
    (mul_comm (⟨x, hAB x.2⟩ : B) (⟨y, hAB y.2⟩ : B))

/-- Commutativity is invariant under a multiplicative equivalence. -/
private theorem isMulCommutative_of_mulEquiv_12_8
    {H K : Type u} [Group H] [Group K]
    (hH : IsMulCommutative H) (e : H ≃* K) :
    IsMulCommutative K := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply e.symm.injective
  simpa only [map_mul] using
    (isMulCommutative_iff.mp hH (e.symm x) (e.symm y))

/-- Full centralizers commute with an ambient equivalence. -/
private theorem map_centralizer_equiv
    {G : Type u} [Group G] (X : Subgroup G) (e : G ≃* G) :
    (Subgroup.centralizer (X : Set G)).map e.toMonoidHom =
      Subgroup.centralizer (X.map e.toMonoidHom : Set G) := by
  ext y
  rw [Subgroup.mem_map_equiv]
  constructor
  · intro hy z hz
    have hz' : e.symm z ∈ X := Subgroup.mem_map_equiv.mp hz
    have hcomm := hy (e.symm z) hz'
    simpa using congrArg e hcomm
  · intro hy z hz
    have hzMap : e z ∈ X.map e.toMonoidHom :=
      (Subgroup.mem_map_iff_mem e.injective).mpr hz
    have hcomm := hy (e z) hzMap
    simpa using congrArg e.symm hcomm

/-- Cauchy's theorem in the rank-one subgroup language used below. -/
private theorem exists_rankOne_le_of_prime_dvd_natCard_12_8
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] {K : Subgroup G}
    (hqK : q ∣ Nat.card K) :
    ∃ Q : Subgroup G, Q ≤ K ∧
      IsElementaryAbelianOfRank q 1 Q := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) q hqK
  let Q : Subgroup G := (Subgroup.zpowers x).map K.subtype
  have hcardZ : Nat.card (Subgroup.zpowers x) = q := by
    rw [Nat.card_zpowers, hx]
  have hcardQ : Nat.card Q = q := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcardZ]
  exact ⟨Q, Subgroup.map_subtype_le _,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcardQ⟩

/-- A nonidentity element of a rank-two elementary-abelian group spans a
rank-one subgroup. -/
private theorem rankOneLineIn_zpowers_of_mem_12_8
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    {a : G} (ha : a ∈ A) (hane : a ≠ 1) :
    RankOneLineIn p A (Subgroup.zpowers a) := by
  have hapow : a ^ p = 1 := by
    exact congrArg Subtype.val (hA.pow_eq_one ⟨a, ha⟩)
  have haorder : orderOf a = p :=
    ((Nat.dvd_prime (Fact.out : p.Prime)).mp
      (orderOf_dvd_of_pow_eq_one hapow)).resolve_left
        (by simpa [orderOf_eq_one_iff] using hane)
  have hcard : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, haorder]
  exact ⟨Subgroup.zpowers_le.mpr ha,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcard⟩

/-- A characteristic subgroup, viewed in the original ambient group, is
preserved by the full ambient normalizer. -/
private theorem characteristic_map_subtype_le_normalizer_12_8
    {G : Type u} [Group G] (H : Subgroup G)
    (R : Subgroup H) [R.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (R.map H.subtype : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      H (Subgroup.normalizer (H : Set G)) R le_rfl g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    have hback := characteristic_map_subtype_invariant_under_normalizer
      H (Subgroup.normalizer (H : Set G)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using hback

/-- Ambient form of the defining maximality of the Fitting subgroup. -/
private theorem nilpotent_normal_le_fittingWithin_12_8
    {G : Type u} [Group G] [Finite G]
    {K H : Subgroup G} (hKH : K ≤ H)
    (hKnormal : (K.subgroupOf H).Normal)
    (hKnil : Group.IsNilpotent K) :
    K ≤ fittingWithin H := by
  let KH : Subgroup H := K.subgroupOf H
  let eKH : KH ≃* K := Subgroup.subgroupOfEquivOfLe hKH
  letI : KH.Normal := hKnormal
  letI : Group.IsNilpotent KH :=
    Group.nilpotent_of_mulEquiv eKH.symm
  have hcore : KH ≤ fittingCore H :=
    nilpotent_normal_le_fittingCore (by infer_instance) (by infer_instance)
  rw [← Subgroup.map_subgroupOf_eq_of_le hKH]
  exact Subgroup.map_mono hcore

/-- A `pi`-subgroup of a finite group lies in a normal `pi`-Hall
subgroup. -/
private theorem le_normal_isHall_of_isPiNumber_12_8
    {K : Type u} [Group K] [Finite K]
    {pi : Set ℕ} {N L : Subgroup K}
    (hNnormal : N.Normal) (hNHall : IsHall pi N)
    (hLpi : IsPiNumber pi (Nat.card L)) : L ≤ N := by
  letI : N.Normal := hNnormal
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro r hr hrL hrIndex
    exact hNHall.isPiNumber_index hr hrIndex (hLpi hr hrL)
  intro x hx
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hx)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have hone : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (orderOf_eq_one_iff.mp hone)

/-! ## Prime partition bridge -/

/-- The prime divisors of a sigma complement belong to exactly one of the
three tau classes. -/
private theorem primeSupport_sigma_complement_subset_tau
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    primeSupport (Nat.card E) ⊆
      tau1Primes M ∪ tau2Primes M ∪ tau3Primes M := by
  intro q hqE
  have hq : q.Prime := hqE.1
  letI : Fact q.Prime := ⟨hq⟩
  have hqM : q ∣ Nat.card M :=
    hqE.2.trans (Subgroup.card_dvd_of_le hEM)
  have hqNotSigma : q ∉ sigmaPrimes M := by
    have hqEsub : q ∣ Nat.card (E.subgroupOf M) := by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEM]
      exact hqE.2
    exact hHall.isPiNumber_card hq hqEsub
  obtain ⟨X, hXM, hX⟩ :=
    exists_rankOne_le_of_prime_dvd_natCard_12_8 (K := M) hqM
  have hRankOne : HasElementaryAbelianRankAtLeast q 1 M :=
    ⟨X, hXM, hX⟩
  by_cases hRankTwo : HasElementaryAbelianRankAtLeast q 2 M
  · have hNoRankThree :
        ¬ HasElementaryAbelianRankAtLeast q 3 M := by
      intro hRankThree
      exact hqNotSigma (alpha_sub_sigma hM ⟨hq, hRankThree⟩)
    exact Or.inl (Or.inr
      ⟨hq, hqNotSigma, hRankTwo, hNoRankThree⟩)
  · by_cases hqDer : q ∣ Nat.card (_root_.commutator M)
    · exact Or.inr
        ⟨hq, hqNotSigma, hRankOne, hRankTwo, hqDer⟩
    · exact Or.inl (Or.inl
        ⟨hq, hqNotSigma, hRankOne, hRankTwo, hqDer⟩)

/-! ## Internal-product adapters -/

/-- Complementarity after passing to a common ambient subgroup implies
ambient disjointness of the original factors. -/
private theorem disjoint_of_isComplement_subgroupOf_12_8
    {G : Type u} [Group G] {A B K : Subgroup G}
    (hAK : A ≤ K) (hBK : B ≤ K)
    (hcomp : (A.subgroupOf K).IsComplement' (B.subgroupOf K)) :
    Disjoint A B := by
  rw [disjoint_iff]
  apply le_antisymm ?_ bot_le
  intro x hx
  let xK : K := ⟨x, hAK hx.1⟩
  have hxInf : xK ∈
      A.subgroupOf K ⊓ B.subgroupOf K := ⟨hx.1, hx.2⟩
  have hxBot : xK ∈ (⊥ : Subgroup K) :=
    hcomp.disjoint.le_bot hxInf
  exact Subgroup.mem_bot.mpr
    (congrArg Subtype.val (Subgroup.mem_bot.mp hxBot))

/-- Complementarity inside `K` recovers the ambient equality of the two
factors' supremum with `K`. -/
private theorem sup_eq_of_isComplement_subgroupOf_12_8
    {G : Type u} [Group G] {A B K : Subgroup G}
    (hAK : A ≤ K) (hBK : B ≤ K)
    (hcomp : (A.subgroupOf K).IsComplement' (B.subgroupOf K)) :
    A ⊔ B = K := by
  calc
    A ⊔ B =
        (A.subgroupOf K ⊔ B.subgroupOf K).map K.subtype := by
      rw [Subgroup.map_sup,
        Subgroup.map_subgroupOf_eq_of_le hAK,
        Subgroup.map_subgroupOf_eq_of_le hBK]
    _ = (⊤ : Subgroup K).map K.subtype :=
      congrArg (Subgroup.map K.subtype) hcomp.sup_eq_top
    _ = K := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

/-- A disjoint normalized pair is complementary in the subgroup it
generates. -/
private theorem subgroupOf_sup_isComplement_12_8
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
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
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

/-! ## The prime-complement part of the Fitting subgroup -/

/-- Once `tau2(M)` is the singleton `{p}`, the `p'`-core of the Fitting
subgroup is exactly the sigma core.  This is the prime-class calculation in
the middle of the Coq proof of Theorem 12.7. -/
private theorem map_pPrimeCore_fittingWithin_eq_sigmaCore_12_8
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpTau : p ∈ tau2Primes M)
    (hTau : tau2Primes M = {p}) :
    (pPrimeCore p (fittingWithin M)).map
        (fittingWithin M).subtype = sigmaCore M := by
  let F : Subgroup G := fittingWithin M
  let K : Subgroup G :=
    (pPrimeCore p F).map F.subtype
  have hFM : F ≤ M := fittingWithin_le M
  have hMnormF : M ≤ Subgroup.normalizer (F : Set G) :=
    fittingWithin_le_normalizer M
  have hMnormK : M ≤ Subgroup.normalizer (K : Set G) := by
    dsimp [K]
    exact hMnormF.trans
      (characteristic_map_subtype_le_normalizer_12_8 F
        (pPrimeCore p F))
  have hKM : K ≤ M := (Subgroup.map_subtype_le _).trans hFM
  have hKnormalM : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr hMnormK
  have hKsigma : IsPiNumber (sigmaPrimes M) (Nat.card K) := by
    intro q hq hqK
    letI : Fact q.Prime := ⟨hq⟩
    have hqCore : q ∣ Nat.card (pPrimeCore p F) := by
      change q ∣ Nat.card ((pPrimeCore p F).map F.subtype) at hqK
      rwa [Subgroup.card_map_of_injective F.subtype_injective] at hqK
    have hqF : q ∣ Nat.card F :=
      hqK.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
    have hqnep : q ≠ p := by
      intro hqp
      subst q
      exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mp
        (pPrimeCore_coprime_card (G := F) (p := p))) hqCore
    let S : Sylow q F := Classical.choice Sylow.nonempty
    have hqS : q ∣ Nat.card (S : Subgroup F) := by
      have hprod : q ∣ Nat.card (S : Subgroup F) * S.index := by
        rwa [S.card_mul_index]
      exact (hq.dvd_mul.mp hprod).resolve_right S.not_dvd_index
    letI : Group.IsNilpotent F := fittingWithin_isNilpotent M
    have hqPCore : q ∣ Nat.card (pCore q F) := by
      rw [pCore_eq_sylow_of_isNilpotent S]
      exact hqS
    let Q : Subgroup G := (pCore q F).map F.subtype
    have hQq : IsPGroup q Q := pCore_isPGroup.map F.subtype
    have hQF : Q ≤ F := Subgroup.map_subtype_le _
    have hQne : Q ≠ ⊥ := by
      intro hQbot
      have hcardQ : Nat.card Q = 1 := by rw [hQbot]; simp
      have hqMap : q ∣ Nat.card Q := by
        change q ∣ Nat.card ((pCore q F).map F.subtype)
        rw [Subgroup.card_map_of_injective F.subtype_injective]
        exact hqPCore
      exact hq.not_dvd_one (hcardQ ▸ hqMap)
    have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
      dsimp [Q]
      exact hMnormF.trans
        (characteristic_map_subtype_le_normalizer_12_8 F (pCore q F))
    have hQM : Q ≤ M := hQF.trans hFM
    have hQnormalM : (Q.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hQM).mpr hMnormQ
    have hNQ : Subgroup.normalizer (Q : Set G) = M :=
      mmax_normal hM hQM hQnormalM hQne
    rcases prime_class_mmax_norm hM hQq (by rw [hNQ]) with
      hqSigma | hqTau
    · exact hqSigma
    · have hqp : q = p := by
        exact Set.mem_singleton_iff.mp (hTau ▸ hqTau)
      exact (hqnep hqp).elim
  have hKsigmaCore : K ≤ sigmaCore M := by
    change K ≤ primeSetCore (sigmaPrimes M) M
    exact le_sSup ⟨hKM, hKnormalM, hKsigma⟩
  have hSigmaNil : Group.IsNilpotent (sigmaCore M) :=
    tau2_Msigma_nil hM hpTau
  have hSigmaF : sigmaCore M ≤ F :=
    nilpotent_normal_le_fittingWithin_12_8
      (sigmaCore_le M) (sigmaCore_normal M) hSigmaNil
  have hSigmaNormalF :
      ((sigmaCore M).subgroupOf F).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hSigmaF).mpr
    exact hFM.trans <|
      (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).mp
        (sigmaCore_normal M)
  have hSigmaPrime : IsPPrimeSubgroup p ((sigmaCore M).subgroupOf F) := by
    rw [IsPPrimeSubgroup,
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hSigmaF]
    apply (Fact.out : p.Prime).coprime_iff_not_dvd.mpr
    intro hpCard
    exact hpTau.2.1 (sigmaCore_isPiNumber M Fact.out hpCard)
  have hSigmaSubCore :
      (sigmaCore M).subgroupOf F ≤ pPrimeCore p F :=
    le_pPrimeCore hSigmaPrime hSigmaNormalF
  have hSigmaK : sigmaCore M ≤ K := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hSigmaF]
    exact Subgroup.map_mono hSigmaSubCore
  exact le_antisymm hKsigmaCore hSigmaK

/-! ## Bender--Glauberman Theorem 12.7 -/

/-- `BGsection12.v: nonabelian_tau2`, Theorem 12.7.

The ambient nonabelian `p`-subgroup is used only to choose a nonabelian
Sylow subgroup of `G`; all remaining objects are intrinsic to the fixed
sigma complement. -/
theorem nonabelian_tau2
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E A P₀ : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hP₀p : IsPGroup p P₀)
    (hP₀noncomm : ¬ IsMulCommutative P₀) :
    NonabelianTau2Conclusion M E p
      (centralizerWithin A (sigmaCore M)) := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  have hAM : A ≤ M := hAE.trans hEM
  obtain ⟨⟨E₁, hE₁E, hHallE₁⟩, ⟨E₃, hE₃E, hHallE₃⟩⟩ :=
    ex_tau13_compl hEM hHall
  obtain ⟨E₂, hE₂E, hHallE₂, hCompl⟩ :=
    ex_tau2_compl hEM hHall hE₁E hHallE₁ hE₃E hHallE₃
  have hRegular := tau2_regular hM hCompl hpTau hAE hA
  have hTauCtx := tau2_context hM hpTau hAM hA
  have hComplCtx := tau2_compl_context hM hEM hHall hpTau hAE hA

  let AE₂ : Subgroup E₂ := A.subgroupOf E₂
  have hAE₂p : IsPGroup p AE₂ := by
    exact hA.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe hRegular.A_le_E₂).symm
  obtain ⟨P₂, hAP₂⟩ := hAE₂p.exists_le_sylow
  let P : Subgroup G := ambientSylow E₂ P₂
  have hPE₂ : P ≤ E₂ := Subgroup.map_subtype_le _
  have hPE : P ≤ E := hPE₂.trans hE₂E
  have hAP : A ≤ P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRegular.A_le_E₂]
    exact Subgroup.map_mono hAP₂
  obtain ⟨PE, hPEeq⟩ :=
    exists_sylow_of_hall_with_same_ambient hpTau.1 hE₂E
      hHallE₂ hpTau P₂
  obtain ⟨PM, hPMeq₀⟩ :=
    exists_sylow_of_hall_with_same_ambient hpTau.1 hEM hHall
      hpTau.2.1 PE
  have hPMeq : ambientSylow M PM = P := hPMeq₀.trans hPEeq
  have hPp : IsPGroup p P := P₂.isPGroup'.map E₂.subtype
  obtain ⟨S, hPS⟩ := hPp.exists_le_sylow
  have hPcomm : IsMulCommutative P := by
    have hPcomm' := hTauCtx.sylow_abelian PM
    rw [hPMeq] at hPcomm'
    exact hPcomm'
  obtain ⟨T, hP₀T⟩ := hP₀p.exists_le_sylow
  have hTnoncomm : ¬ IsMulCommutative (T : Subgroup G) := by
    intro hTcomm
    exact hP₀noncomm (isMulCommutative_of_le_12_8 hP₀T hTcomm)
  have hSnoncomm : ¬ IsMulCommutative (S : Subgroup G) := by
    intro hScomm
    exact hTnoncomm
      (isMulCommutative_of_mulEquiv_12_8 hScomm (Sylow.equiv S T))
  have hPSlt : P < (S : Subgroup G) := by
    refine lt_of_le_of_ne hPS ?_
    intro hEq
    exact hSnoncomm (hEq ▸ hPcomm)
  have hAmax : IsPMaxElem p (⊤ : Subgroup G) A :=
    (tau2_not_beta hM hpTau).2 hAM hA

  have hTauSingleton : tau2Primes M = {p} := by
    apply Set.Subset.antisymm
    · intro q hqTau
      by_cases hqp : q = p
      · simpa [hqp]
      have hpq : p ≠ q := Ne.symm hqp
      letI : Fact q.Prime := ⟨hqTau.1⟩
      obtain ⟨B, hBE, hBM, hB⟩ := ex_tau2Elem hEM hHall hqTau
      have hBCtx := tau2_compl_context hM hEM hHall hqTau hBE hB
      let AE' : Subgroup E := A.subgroupOf E
      let BE' : Subgroup E := B.subgroupOf E
      letI : AE'.Normal := by simpa [AE'] using hComplCtx.A_normal
      letI : BE'.Normal := by simpa [BE'] using hBCtx.A_normal
      have hcopAB : Nat.Coprime (Nat.card AE') (Nat.card BE') := by
        rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hAE,
          Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hBE,
          hA.card_eq, hB.card_eq]
        exact Nat.coprime_pow_primes 2 2 hpTau.1 hqTau.1 hpq
      have hdisAB : Disjoint AE' BE' :=
        Subgroup.disjoint_of_coprime_natCard hcopAB
      have hcommAB := Subgroup.commute_of_normal_of_disjoint
        AE' BE' (by infer_instance) (by infer_instance) hdisAB
      have hBcentA : B ≤ Subgroup.centralizer (A : Set G) := by
        intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro a ha
        let aE : E := ⟨a, hAE ha⟩
        let bE : E := ⟨b, hBE hb⟩
        exact congrArg Subtype.val
          (hcommAB aE bE ha hb).eq
      have hqCA : q ∣ Nat.card (Subgroup.centralizer (A : Set G)) := by
        have hqB : q ∣ Nat.card B := by
          rw [hB.card_eq]
          exact dvd_pow_self q (by omega)
        exact hqB.trans (Subgroup.card_dvd_of_le hBcentA)
      have hAnormB : A ≤ Subgroup.normalizer (B : Set G) := by
        exact hAE.trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hBE).mp
            hBCtx.A_normal)
      obtain ⟨Q, hQmax, hBQ⟩ :=
        max_normed_exists (A : Set G) ({q} : Set ℕ) B
          (hB.isPGroup.isPiNumber_natCard (Set.mem_singleton q)) hAnormB
      have hQnarrow : IsNarrow q Q := by
        intro _hRankThree
        refine ⟨B, hB, ?_⟩
        exact ((tau2_not_beta hM hqTau).2 hBM hB).of_le le_top hBQ
      obtain ⟨P₁, hAP₁, _hNprod, _hP₁der, hP₁cent⟩ :=
        max_normed_2Elem_signaliser hpq hA hAmax hQmax hqCA
      have hP₁E : (P₁ : Subgroup G) ≤ E := by
        exact (hP₁cent hQnarrow).trans
          ((Subgroup.centralizer_le hBQ).trans hBCtx.centralizer_le_E)
      let P₁E : Sylow p E := P₁.subtype hP₁E
      have hcardPPE : Nat.card P = Nat.card (PE : Subgroup E) := by
        change Nat.card (ambientSylow E₂ P₂) = Nat.card (PE : Subgroup E)
        calc
          Nat.card (ambientSylow E₂ P₂) =
              Nat.card (ambientSylow E PE) :=
            congrArg (fun H : Subgroup G => Nat.card H) hPEeq.symm
          _ = Nat.card (PE : Subgroup E) :=
            Subgroup.card_map_of_injective E.subtype_injective
      have hcardPEP₁E :
          Nat.card (PE : Subgroup E) = Nat.card (P₁E : Subgroup E) :=
        Nat.card_congr (Sylow.equiv PE P₁E).toEquiv
      have hcardP₁E :
          Nat.card (P₁E : Subgroup E) = Nat.card (P₁ : Subgroup G) := by
        exact Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe hP₁E).toEquiv
      have hcardP₁S :
          Nat.card (P₁ : Subgroup G) = Nat.card (S : Subgroup G) :=
        Nat.card_congr (Sylow.equiv P₁ S).toEquiv
      have hcardPS : Nat.card P = Nat.card (S : Subgroup G) :=
        hcardPPE.trans (hcardPEP₁E.trans (hcardP₁E.trans hcardP₁S))
      have hEqPS : P = (S : Subgroup G) :=
        Subgroup.eq_of_le_of_card_ge hPS (by rw [hcardPS])
      exact (hPSlt.ne hEqPS).elim
    · intro q hqp
      have hq : q = p := Set.mem_singleton_iff.mp hqp
      simpa [hq] using hpTau

  have hSigmaAcop :
      Nat.Coprime (Nat.card (sigmaCore M)) (Nat.card A) := by
    exact (sigmaCore_isPiNumber M).coprime_compl
      (hA.isPGroup.isPiNumber_natCard hpTau.2.1)
  have hAnormSigma :
      A ≤ Subgroup.normalizer (sigmaCore M : Set G) := by
    exact hAM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).mp
        (sigmaCore_normal M))
  have hSigmaSol : IsSolvable (sigmaCore M) := by
    letI : IsSolvable M := mmax_sol hM
    exact isSolvable_of_injective
      (Subgroup.inclusion (sigmaCore_le M))
      (Subgroup.inclusion_injective (sigmaCore_le M))
  obtain ⟨A₀, hA₀line, hA₀nonregular⟩ :
      ∃ A₀ : Subgroup G,
        RankOneLineIn p A A₀ ∧
          centralizerWithin (sigmaCore M) A₀ ≠ ⊥ := by
    by_contra hnone
    push_neg at hnone
    have hSigmaBot : sigmaCore M ≤ (⊥ : Subgroup G) :=
      le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
        hA.commutative (hA.not_isCyclic hpTau.1) hAnormSigma
        hSigmaAcop hSigmaSol (by
          intro a ha hane
          have hline := rankOneLineIn_zpowers_of_mem_12_8 hA ha hane
          rw [hnone (Subgroup.zpowers a) hline])
    exact Msigma_neq1 hM (le_antisymm hSigmaBot bot_le)
  have hA₀E : A₀ ≤ E := hA₀line.1.trans hAE
  have hUniqA₀ :
      minSimple_max_groups_of (G := G)
          (Subgroup.centralizer (A₀ : Set G) : Set G) = {M} :=
    hComplCtx.line_centralizer_unique hA₀E hA₀line.2
      hA₀nonregular
  have hCA₀M : Subgroup.centralizer (A₀ : Set G) ≤ M :=
    (mem_uniq_mmax hUniqA₀).2
  have hPM : P ≤ M := hPE.trans hEM
  have hSnotM : ¬ (S : Subgroup G) ≤ M := by
    intro hSM
    have hSPambient : (S : Subgroup G) = ambientSylow M PM :=
      ambientSylow_eq_of_le PM S.isPGroup' hSM (by
        rw [hPMeq]
        exact hPS)
    have hSP : (S : Subgroup G) = P := hSPambient.trans hPMeq
    exact hPSlt.ne hSP.symm
  have hSinM : (S : Subgroup G) ⊓ M = P := by
    let SM : Subgroup G := (S : Subgroup G) ⊓ M
    change SM = P
    have hSMleft : SM ≤ (S : Subgroup G) := by
      dsimp [SM]
      exact inf_le_left
    have hSMright : SM ≤ M := by
      dsimp [SM]
      exact inf_le_right
    have hInfp : IsPGroup p SM :=
      S.isPGroup'.to_le hSMleft
    have hInfAmbient : SM = ambientSylow M PM :=
      ambientSylow_eq_of_le PM hInfp hSMright (by
        rw [hPMeq]
        change P ≤ SM
        exact le_inf hPS hPM)
    exact hInfAmbient.trans hPMeq
  let Z₀ : Subgroup G := omegaOneCenterAmbient p (S : Subgroup G)
  have hBasic := basic_p2maxElem_structure hA hAmax S.isPGroup'
    (hAP.trans hPS) hSnoncomm
  change IsElementaryAbelianOfRank p 1 Z₀ ∧
      (∃ Y : Subgroup G, IsCyclic Y ∧ Z₀ ≤ Y ∧
        ∀ A₁, RankOneLineIn p A A₁ → A₁ ≠ Z₀ →
          Disjoint A₁ Y ∧
          (∀ a ∈ A₁, ∀ y ∈ Y, Commute a y) ∧
          A₁ ⊔ Y = centralizerWithin (S : Subgroup G) A) ∧
      (∀ A₁ A₂,
        RankOneLineIn p A A₁ → A₁ ≠ Z₀ →
        RankOneLineIn p A A₂ → A₂ ≠ Z₀ →
        ∃ x : G, x ∈ (S : Subgroup G) ⊓
            Subgroup.normalizer (A : Set G) ∧
          A₂ = A₁.map (MulAut.conj x⁻¹).toMonoidHom) at hBasic
  obtain ⟨hZ₀line, ⟨Y, hYcyclic, hZ₀Y, hYdecomp⟩, hTrans⟩ := hBasic
  have hZ₀center : Z₀ ≤ centerWithin (S : Subgroup G) :=
    omegaOneCenterAmbient_le_centerWithin p (S : Subgroup G)
  have hA₀neZ₀ : A₀ ≠ Z₀ := by
    intro hEq
    apply hSnotM
    exact (show (S : Subgroup G) ≤ Subgroup.centralizer (A₀ : Set G) by
      intro s hs
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact ((hZ₀center (hEq ▸ ha)).2 s hs).symm).trans hCA₀M
  obtain ⟨hA₀Ydis, hA₀Ycomm, hA₀Ysup⟩ :=
    hYdecomp A₀ hA₀line hA₀neZ₀
  have hCentSA : centralizerWithin (S : Subgroup G) A = P := by
    apply le_antisymm
    · intro x hx
      have hxM : x ∈ M :=
        hEM (hComplCtx.centralizer_le_E hx.2)
      have hxInf : x ∈ (S : Subgroup G) ⊓ M := ⟨hx.1, hxM⟩
      rw [hSinM] at hxInf
      exact hxInf
    · intro x hx
      refine ⟨hPS hx, ?_⟩
      intro a ha
      letI : IsMulCommutative P := hPcomm
      exact congrArg Subtype.val
        (mul_comm (⟨a, hAP ha⟩ : P) ⟨x, hx⟩)
  have hA₀YsupP : A₀ ⊔ Y = P := hA₀Ysup.trans hCentSA

  have hRankControl :
      ∀ X : Subgroup G, RankOneLineIn p E X → X ≠ A₀ →
        centralizerWithin (sigmaCore M) X = ⊥ ∧
          ¬ Subgroup.centralizer (X : Set G) ≤ M := by
    intro X hXE hXneA₀
    have hXA : RankOneLineIn p A X :=
      (hComplCtx.rankOne_iff X).mp hXE
    have hCentXnotM :
        ¬ Subgroup.centralizer (X : Set G) ≤ M := by
      by_cases hXZ : X ≤ centerWithin (S : Subgroup G)
      · intro hCentXM
        apply hSnotM
        intro s hs
        apply hCentXM
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact ((hXZ hx).2 s hs).symm
      · have hXneZ₀ : X ≠ Z₀ := by
          intro hEq
          exact hXZ (hEq ▸ hZ₀center)
        obtain ⟨g, hg, hXmap⟩ :=
          hTrans A₀ X hA₀line hA₀neZ₀ hXA hXneZ₀
        have hgNotNormM : g ∉ Subgroup.normalizer (M : Set G) := by
          intro hgNormM
          have hgM : g ∈ M := by
            rw [← norm_mmax hM]
            exact hgNormM
          have hgP : g ∈ P := by
            rw [← hSinM]
            exact ⟨hg.1, hgM⟩
          have hginvCent : g⁻¹ ∈ Subgroup.centralizer (A₀ : Set G) := by
            rw [Subgroup.mem_centralizer_iff]
            intro a ha
            letI : IsMulCommutative P := hPcomm
            exact congrArg Subtype.val
              (mul_comm (⟨a, hAP (hA₀line.1 ha)⟩ : P)
                ⟨g⁻¹, P.inv_mem hgP⟩)
          have hmapFix :
              A₀.map (MulAut.conj g⁻¹).toMonoidHom = A₀ :=
            Subgroup.mem_normalizer_iff_map_conj_eq.mp
              ((Subgroup.centralizer_le_normalizer (A₀ : Set G))
                hginvCent)
          exact hXneA₀ (hXmap.trans hmapFix)
        intro hCentXM
        let e : G ≃* G := MulAut.conj g⁻¹
        have hCentMap :
            (Subgroup.centralizer (A₀ : Set G)).map e.toMonoidHom =
              Subgroup.centralizer (X : Set G) := by
          rw [map_centralizer_equiv A₀ e]
          exact congrArg
            (fun H : Subgroup G => Subgroup.centralizer (H : Set G))
            hXmap.symm
        have htransport := def_uniq_mmaxJ e hUniqA₀
        rw [hCentMap] at htransport
        have hMmem : M ∈ minSimple_max_groups_of (G := G)
            (Subgroup.centralizer (X : Set G) : Set G) := ⟨hM, hCentXM⟩
        rw [htransport] at hMmem
        have hMeq : M = M.map e.toMonoidHom :=
          Set.mem_singleton_iff.mp hMmem
        have hginvNorm : g⁻¹ ∈ Subgroup.normalizer (M : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMeq.symm
        exact hgNotNormM (by
          simpa using (Subgroup.normalizer (M : Set G)).inv_mem hginvNorm)
    refine ⟨?_, hCentXnotM⟩
    by_contra hnonregular
    have hUniqueX := hComplCtx.line_centralizer_unique
      hXE.1 hXE.2 hnonregular
    exact hCentXnotM (mem_uniq_mmax hUniqueX).2

  have hSigmaCentA₀ :
      sigmaCore M ≤ Subgroup.centralizer (A₀ : Set G) :=
    le_of_centralizerWithin_zpowers_le_of_coprime_abelian_solvable
      hA.commutative (hA.not_isCyclic hpTau.1) hAnormSigma
      hSigmaAcop hSigmaSol (by
        intro a ha hane
        have hlineA := rankOneLineIn_zpowers_of_mem_12_8 hA ha hane
        by_cases hEq : Subgroup.zpowers a = A₀
        · rw [hEq]
          exact inf_le_right
        · have hlineE : RankOneLineIn p E (Subgroup.zpowers a) :=
            ⟨hlineA.1.trans hAE, hlineA.2⟩
          rw [(hRankControl (Subgroup.zpowers a) hlineE hEq).1]
          exact bot_le)
  have hA₀leCent : A₀ ≤ centralizerWithin A (sigmaCore M) := by
    exact le_inf hA₀line.1
      (Subgroup.le_centralizer_iff.mp hSigmaCentA₀)
  have hCentleA₀ : centralizerWithin A (sigmaCore M) ≤ A₀ := by
    intro x hx
    by_contra hxA₀
    have hxne : x ≠ 1 := by
      intro hxone
      exact hxA₀ (hxone ▸ A₀.one_mem)
    let X : Subgroup G := Subgroup.zpowers x
    have hXlineA : RankOneLineIn p A X :=
      rankOneLineIn_zpowers_of_mem_12_8 hA hx.1 hxne
    have hXlineE : RankOneLineIn p E X :=
      ⟨hXlineA.1.trans hAE, hXlineA.2⟩
    have hXneA₀ : X ≠ A₀ := by
      intro hEq
      exact hxA₀ (hEq ▸ Subgroup.mem_zpowers x)
    have hXcentSigma : X ≤
        Subgroup.centralizer (sigmaCore M : Set G) :=
      Subgroup.zpowers_le.mpr hx.2
    have hSigmaCentX : sigmaCore M ≤
        Subgroup.centralizer (X : Set G) :=
      Subgroup.le_centralizer_iff.mp hXcentSigma
    have hCentEq : centralizerWithin (sigmaCore M) X = sigmaCore M :=
      inf_eq_left.mpr hSigmaCentX
    have hbot := (hRankControl X hXlineE hXneA₀).1
    exact Msigma_neq1 hM (hCentEq.symm.trans hbot)
  have hDefA₀ : centralizerWithin A (sigmaCore M) = A₀ :=
    le_antisymm hCentleA₀ hA₀leCent
  have hA₀card : Nat.card A₀ = p := by
    simpa using hA₀line.2.card_eq

  have hSigmaSupE : sigmaCore M ⊔ E = M := by
    have hsd := sdprod_sigma hM hEM hHall
    have htop :
        (sigmaCore M).subgroupOf M ⊔ E.subgroupOf M =
          (⊤ : Subgroup M) := hsd.2.2.2.sup_eq_top
    calc
      sigmaCore M ⊔ E =
          ((sigmaCore M).subgroupOf M ⊔ E.subgroupOf M).map
            M.subtype := by
        rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le
          (sigmaCore_le M), Subgroup.map_subgroupOf_eq_of_le hEM]
      _ = (⊤ : Subgroup M).map M.subtype := congrArg _ htop
      _ = M := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hEnormA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mp
      hComplCtx.A_normal
  have hEnormSigma : E ≤
      Subgroup.normalizer (sigmaCore M : Set G) :=
    hEM.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).mp
        (sigmaCore_normal M))
  have hEnormCentSigma : E ≤
      Subgroup.normalizer
        (Subgroup.centralizer (sigmaCore M : Set G) : Set G) := by
    exact hEnormSigma.trans
      ((Subgroup.normal_subgroupOf_iff_le_normalizer
        (Subgroup.centralizer_le_normalizer (sigmaCore M : Set G))).mp
          (Subgroup.normal_subgroupOf_centralizer_normalizer
            (sigmaCore M : Set G)))
  have hEnormA₀ : E ≤ Subgroup.normalizer (A₀ : Set G) := by
    rw [← hDefA₀]
    exact (le_inf hEnormA hEnormCentSigma).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hSigmaNormA₀ : sigmaCore M ≤
      Subgroup.normalizer (A₀ : Set G) :=
    hSigmaCentA₀.trans
      (Subgroup.centralizer_le_normalizer (A₀ : Set G))
  have hMnormA₀ : M ≤ Subgroup.normalizer (A₀ : Set G) := by
    rw [← hSigmaSupE]
    exact sup_le hSigmaNormA₀ hEnormA₀
  have hA₀M : A₀ ≤ M := hA₀E.trans hEM
  have hA₀normalM : (A₀.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA₀M).mpr hMnormA₀

  have hYP : Y ≤ P := by rw [← hA₀YsupP]; exact le_sup_right
  have hA₀P : A₀ ≤ P := hA₀line.1.trans hAP
  let A₀P : Subgroup P := A₀.subgroupOf P
  let YP : Subgroup P := Y.subgroupOf P
  have hA₀YPdis : Disjoint A₀P YP := by
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxAmbient : (x : G) ∈ A₀ ⊓ Y := ⟨hx.1, hx.2⟩
    have hxone : (x : G) = 1 :=
      Subgroup.mem_bot.mp (hA₀Ydis.le_bot hxAmbient)
    exact Subgroup.mem_bot.mpr (Subtype.ext hxone)
  have hA₀YPsup : A₀P ⊔ YP = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hA₀P hYP, hA₀YsupP]
    simp
  have hA₀YPcomp : A₀P.IsComplement' YP := by
    letI : IsMulCommutative P := hPcomm
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hA₀YPdis
    rw [← Subgroup.normal_mul A₀P YP, hA₀YPsup]
    rfl
  have hDirectP : IsInternalDirectProductIn A₀ Y P :=
    { left_le := hA₀P
      right_le := hYP
      complement := by simpa [A₀P, YP] using hA₀YPcomp
      commute := by
        intro a y
        exact hA₀Ycomm a a.property y y.property }

  have hOmegaP :
      (omegaOne p P).map P.subtype = A := by
    have hAPM : A ≤ ambientSylow M PM := by
      rw [hPMeq]
      exact hAP
    have hOmega := hTauCtx.omegaOne_eq PM hAPM
    rw [hPMeq] at hOmega
    exact hOmega
  have hCentPSigma : centralizerWithin P (sigmaCore M) = A₀ := by
    apply le_antisymm
    · intro c hc
      let cP : P := ⟨c, hc.1⟩
      let a : A₀ := hDirectP.leftProjection cP
      let y : Y := hDirectP.rightProjection cP
      have hdecomp : (a : G) * (y : G) = c := by
        exact congrArg Subtype.val (hDirectP.mulEquiv_projections cP)
      by_contra hcA₀
      have hyne : (y : G) ≠ 1 := by
        intro hyone
        apply hcA₀
        have hca : c = (a : G) := by
          rw [← hdecomp, hyone, mul_one]
        exact hca ▸ a.property
      have haCent : (a : G) ∈
          Subgroup.centralizer (sigmaCore M : Set G) :=
        (Subgroup.le_centralizer_iff.mp hSigmaCentA₀) a.property
      have hyCent : (y : G) ∈
          Subgroup.centralizer (sigmaCore M : Set G) := by
        have hyeq : (y : G) = (a : G)⁻¹ * c := by
          rw [← hdecomp]
          group
        rw [hyeq]
        exact (Subgroup.centralizer (sigmaCore M : Set G)).mul_mem
          ((Subgroup.centralizer (sigmaCore M : Set G)).inv_mem haCent) hc.2
      let Z : Subgroup G := Subgroup.zpowers (y : G)
      have hZp : IsPGroup p Z := by
        have hYp : IsPGroup p Y := hPp.to_le hYP
        have hyPelt : IsPElement p (y : G) :=
          IsPElement.map Y.subtype (hYp y)
        exact hyPelt.zpowers_isPGroup
      have hZne : Z ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hyne
      have hpZ : p ∣ Nat.card Z :=
        hZp.card_eq_or_dvd.resolve_left
          ((Z.one_lt_card_iff_ne_bot.mpr hZne).ne')
      obtain ⟨z, hzorder⟩ :=
        exists_prime_orderOf_dvd_card' (G := Z) p hpZ
      have hzorderG : orderOf (z : G) = p :=
        (Subgroup.orderOf_coe z).trans hzorder
      let X : Subgroup G := Subgroup.zpowers (z : G)
      have hXcard : Nat.card X = p := by
        change Nat.card (Subgroup.zpowers (z : G)) = p
        rw [Nat.card_zpowers, hzorderG]
      have hXline : IsElementaryAbelianOfRank p 1 X :=
        isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
      have hZY : Z ≤ Y := Subgroup.zpowers_le.mpr y.property
      have hXZ : X ≤ Z := Subgroup.zpowers_le.mpr z.property
      have hXP : X ≤ P := hXZ.trans (hZY.trans hYP)
      have hXCentSigma : X ≤
          Subgroup.centralizer (sigmaCore M : Set G) := by
        exact hXZ.trans (Subgroup.zpowers_le.mpr hyCent)
      have hXA : X ≤ A := by
        intro x hx
        let xP : P := ⟨x, hXP hx⟩
        have hxpow : xP ^ p = 1 := by
          apply Subtype.ext
          change x ^ p = 1
          exact congrArg Subtype.val (hXline.pow_eq_one ⟨x, hx⟩)
        have hxOmega : xP ∈ omegaOne p P :=
          mem_omegaOne_of_pow_eq_one p hxpow
        have hxMap : x ∈ (omegaOne p P).map P.subtype :=
          ⟨xP, hxOmega, rfl⟩
        rwa [hOmegaP] at hxMap
      have hXneA₀ : X ≠ A₀ := by
        intro hEq
        have hA₀Y : A₀ ≤ Y := hEq ▸ hXZ.trans hZY
        have hA₀bot : A₀ = ⊥ := by
          apply le_bot_iff.mp
          rw [← disjoint_iff.mp hA₀Ydis]
          exact le_inf le_rfl hA₀Y
        exact hA₀line.2.ne_bot hA₀bot
      have hXlineE : RankOneLineIn p E X :=
        (hComplCtx.rankOne_iff X).mpr ⟨hXA, hXline⟩
      have hregular := (hRankControl X hXlineE hXneA₀).1
      have hSigmaCentX : sigmaCore M ≤
          Subgroup.centralizer (X : Set G) :=
        Subgroup.le_centralizer_iff.mp hXCentSigma
      have hEqCent : centralizerWithin (sigmaCore M) X = sigmaCore M :=
        inf_eq_left.mpr hSigmaCentX
      exact Msigma_neq1 hM (hEqCent.symm.trans hregular)
    · exact le_inf hA₀P
        (Subgroup.le_centralizer_iff.mp hSigmaCentA₀)

  let F : Subgroup G := fittingWithin M
  have hSigmaNil : Group.IsNilpotent (sigmaCore M) :=
    tau2_Msigma_nil hM hpTau
  have hSigmaF : sigmaCore M ≤ F :=
    nilpotent_normal_le_fittingWithin_12_8
      (sigmaCore_le M) (sigmaCore_normal M) hSigmaNil
  have hA₀F : A₀ ≤ F :=
    nilpotent_normal_le_fittingWithin_12_8 hA₀M hA₀normalM
      hA₀line.2.isPGroup.isNilpotent
  have hPrimePart :
      (pPrimeCore p F).map F.subtype = sigmaCore M := by
    simpa [F] using
      map_pPrimeCore_fittingWithin_eq_sigmaCore_12_8 hM hpTau
        hTauSingleton
  let R : Subgroup G := (pCore p F).map F.subtype
  have hRF : R ≤ F := Subgroup.map_subtype_le _
  have hRM : R ≤ M := hRF.trans (fittingWithin_le M)
  have hMnormR : M ≤ Subgroup.normalizer (R : Set G) := by
    exact (fittingWithin_le_normalizer M).trans
      (characteristic_map_subtype_le_normalizer_12_8 F (pCore p F))
  have hRnormalM : (R.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hRM).mpr hMnormR
  have hRMp : IsPGroup p (R.subgroupOf M) := by
    exact (pCore_isPGroup.map F.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hRM).symm
  have hRleP : R ≤ P := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hRM, ← hPMeq]
    exact Subgroup.map_mono <|
      (le_pCore hRMp hRnormalM).trans (pCore_le_sylow PM)
  have hRcentSigma : R ≤
      Subgroup.centralizer (sigmaCore M : Set G) := by
    intro r hr
    rcases hr with ⟨rF, hrCore, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hsMap : s ∈ (pPrimeCore p F).map F.subtype := by
      rw [hPrimePart]
      exact hs
    rcases hsMap with ⟨sF, hsCore, rfl⟩
    exact congrArg Subtype.val
      ((Subgroup.mem_centralizer_iff.mp
        (pCore_le_centralizer_pPrimeCore p hrCore)) sF hsCore)
  have hRleA₀ : R ≤ A₀ := by
    rw [← hCentPSigma]
    exact le_inf hRleP hRcentSigma
  have hA₀normalF : (A₀.subgroupOf F).Normal := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hA₀F).mpr
    exact (fittingWithin_le M).trans hMnormA₀
  have hA₀Fp : IsPGroup p (A₀.subgroupOf F) := by
    exact hA₀line.2.isPGroup.of_equiv
      (Subgroup.subgroupOfEquivOfLe hA₀F).symm
  have hA₀R : A₀ ≤ R := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hA₀F]
    exact Subgroup.map_mono (le_pCore hA₀Fp hA₀normalF)
  have hReqA₀ : R = A₀ := le_antisymm hRleA₀ hA₀R
  have hSigmaSubEq :
      (sigmaCore M).subgroupOf F = pPrimeCore p F := by
    apply Subgroup.map_injective F.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hSigmaF, hPrimePart]
  have hA₀SubEq : A₀.subgroupOf F = pCore p F := by
    apply Subgroup.map_injective F.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hA₀F]
    exact hReqA₀.symm
  letI : Group.IsNilpotent F := fittingWithin_isNilpotent M
  have hCoreComp :
      (pPrimeCore p F).IsComplement' (pCore p F) := by
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
      (disjoint_pCore_pPrimeCore (G := F) (p := p)).symm
    rw [← Subgroup.normal_mul, sup_comm,
      sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := F) p]
    rfl
  have hFittingDirect :
      IsInternalDirectProductIn (sigmaCore M) A₀ F :=
    { left_le := hSigmaF
      right_le := hA₀F
      complement := by
        simpa [hSigmaSubEq, hA₀SubEq] using hCoreComp
      commute := by
        intro s a
        let sF : F := ⟨s, hSigmaF s.property⟩
        let aF : F := ⟨a, hA₀F a.property⟩
        have hsPrime : sF ∈ pPrimeCore p F := by
          rw [← hSigmaSubEq]
          exact s.property
        have haCore : aF ∈ pCore p F := by
          rw [← hA₀SubEq]
          exact a.property
        exact congrArg Subtype.val
          ((Subgroup.commute_of_normal_of_disjoint
            (pPrimeCore p F) (pCore p F) (by infer_instance)
              (by infer_instance)
              (disjoint_pCore_pPrimeCore (G := F) (p := p)).symm)
            sF aF hsPrime haCore).eq }

  have hE₂p : IsPGroup p E₂ := by
    apply isPGroup_of_isPiNumber_singleton
    have hpi := hHallE₂.isPiNumber_card
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hE₂E,
      hTauSingleton] at hpi
    exact hpi
  have hE₂eqP : E₂ = P :=
    ambientSylow_eq_of_le P₂ hE₂p le_rfl hPE₂
  have hSigmaCtx := sigma_compl_context hM hCompl
  have hE₁normP : E₁ ≤ Subgroup.normalizer (P : Set G) := by
    have hnorm : E₁ ≤ Subgroup.normalizer (E₂ : Set G) :=
      hSigmaCtx.E₂₁_sdprod.2.1.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          hSigmaCtx.E₂₁_sdprod.1).mp
            hSigmaCtx.E₂₁_sdprod.2.2.1)
    rwa [hE₂eqP] at hnorm
  have hE₁normA₀ : E₁ ≤ Subgroup.normalizer (A₀ : Set G) :=
    hE₁E.trans (hEM.trans hMnormA₀)

  obtain ⟨Pcomp, hPcompP, hDirectPcomp, hE₁normPcomp⟩ :
      ∃ Pcomp : Subgroup G, Pcomp ≤ P ∧
        IsInternalDirectProductIn A₀ Pcomp P ∧
        E₁ ≤ Subgroup.normalizer (Pcomp : Set G) := by
    let j : E₁ →* Subgroup.normalizer (P : Set G) :=
      { toFun := fun e ↦ ⟨e, hE₁normP e.property⟩
        map_one' := rfl
        map_mul' := fun _ _ ↦ rfl }
    let f : E₁ →* MulAut P := P.normalizerMonoidHom.comp j
    let AP : Subgroup P := A₀.subgroupOf P
    have hAPinv : ∀ e : E₁, AP.map (f e).toMonoidHom = AP := by
      intro e
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨a, ha, rfl⟩
        have hconj : (e : G) * (a : G) * (e : G)⁻¹ ∈ A₀ :=
          (Subgroup.mem_normalizer_iff.mp (hE₁normA₀ e.property) a).mp ha
        exact hconj
      · exact (Subgroup.card_map_of_injective
          (K := AP)
          (f := (f e).toMonoidHom)
          (f e).injective).ge
    let Phi : Subgroup P := frattini P
    let Q := P ⧸ Phi
    let q : P →* Q := QuotientGroup.mk' Phi
    let fq : E₁ →* MulAut Q :=
      (frattiniQuotientMulAutHom P).comp f
    let U : Subgroup Q := AP.map q
    have hUinv : ∀ e : E₁, U.map (fq e).toMonoidHom = U := by
      intro e
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨_, ⟨a, ha, rfl⟩, rfl⟩
        have hfa : f e a ∈ AP := by
          have hmem : f e a ∈ AP.map (f e).toMonoidHom :=
            ⟨a, ha, rfl⟩
          rwa [hAPinv e] at hmem
        refine ⟨f e a, hfa, ?_⟩
        exact (frattiniQuotientMulAutHom_apply_mk (f e) a).symm
      · exact (Subgroup.card_map_of_injective
          (K := U)
          (f := (fq e).toMonoidHom)
          (fq e).injective).ge
    have hpE₁ : ¬ p ∣ Nat.card E₁ := by
      intro hpCard
      have hpCardSub : p ∣ Nat.card (E₁.subgroupOf E) := by
        rwa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hE₁E]
      have hpTau₁ : p ∈ tau1Primes M :=
        hHallE₁.isPiNumber_card hpTau.1 hpCardSub
      exact (tau2'1 M hpTau₁) hpTau
    letI : IsMulCommutative P := hPcomm
    letI : IsMulCommutative Q := inferInstance
    have hQpow : ∀ x : Q, x ^ p = 1 := by
      exact hPp.quotient_frattini_pow_prime
    obtain ⟨X, hUXcomp, hXinv⟩ :=
      exists_invariant_complement_of_coprime_mulAut_action
        hQpow fq hpE₁ U hUinv
    let Xpre : Subgroup P := X.comap q
    have hPhiLeXpre : Phi ≤ Xpre := by
      intro x hx
      change q x ∈ X
      have hqx : q x = 1 := by
        exact (QuotientGroup.eq_one_iff x).mpr hx
      rw [hqx]
      exact X.one_mem
    have hPhiA₀ : frattini A₀ = ⊥ := by
      letI : IsMulCommutative A₀ := hA₀line.2.commutative
      exact IsPGroup.frattini_eq_bot_of_isMulCommutative_of_pow_prime
        hA₀line.2.pow_eq_one
    have hleftSurj : Function.Surjective hDirectP.leftProjection := by
      intro a
      exact ⟨hDirectP.leftEmbedding a,
        hDirectP.leftProjection_leftEmbedding a⟩
    have hPhiProj : frattini P ≤
        (frattini A₀).comap hDirectP.leftProjection :=
      frattini_le_comap_frattini_of_surjective hleftSurj
    have hAPPhiDis : Disjoint AP Phi := by
      rw [disjoint_iff]
      apply le_antisymm ?_ bot_le
      intro x hx
      let a : A₀ := ⟨(x : G), hx.1⟩
      have hxLeft : hDirectP.leftEmbedding a = x := by
        apply Subtype.ext
        rfl
      have hprojBot : hDirectP.leftProjection x ∈ (⊥ : Subgroup A₀) := by
        rw [← hPhiA₀]
        exact hPhiProj hx.2
      have hprojOne : hDirectP.leftProjection x = 1 :=
        Subgroup.mem_bot.mp hprojBot
      have haOne : a = 1 := by
        rw [← hDirectP.leftProjection_leftEmbedding a, hxLeft]
        exact hprojOne
      have hxGOne : (x : G) = 1 :=
        congrArg (fun z : A₀ => (z : G)) haOne
      exact Subgroup.mem_bot.mpr (Subtype.ext hxGOne)
    have hAPXpreDis : Disjoint AP Xpre := by
      rw [disjoint_iff]
      apply le_antisymm ?_ bot_le
      intro x hx
      have hqxU : q x ∈ U := ⟨x, hx.1, rfl⟩
      have hqxX : q x ∈ X := hx.2
      have hqxBot : q x ∈ (⊥ : Subgroup Q) :=
        hUXcomp.1.le_bot ⟨hqxU, hqxX⟩
      have hqxOne : q x = 1 := Subgroup.mem_bot.mp hqxBot
      have hxPhi : x ∈ Phi :=
        (QuotientGroup.eq_one_iff x).mp hqxOne
      exact hAPPhiDis.le_bot ⟨hx.1, hxPhi⟩
    have hAPXpreSup : AP ⊔ Xpre = ⊤ := by
      have hmap : (AP ⊔ Xpre).map q = (⊤ : Subgroup Q) := by
        rw [Subgroup.map_sup]
        change U ⊔ Xpre.map q = ⊤
        rw [Subgroup.map_comap_eq_self_of_surjective
          (QuotientGroup.mk'_surjective Phi)]
        exact hUXcomp.2.eq_top
      have hcomap : AP ⊔ Xpre ⊔ Phi = ⊤ := by
        have hker : q.ker = Phi := by
          dsimp [q, Phi]
          exact QuotientGroup.ker_mk' (frattini P)
        rw [← hker, ← Subgroup.comap_map_eq q (AP ⊔ Xpre), hmap]
        rfl
      have hPhiLeSup : Phi ≤ AP ⊔ Xpre :=
        hPhiLeXpre.trans le_sup_right
      rwa [sup_eq_left.mpr hPhiLeSup] at hcomap
    have hAPXpreComp : AP.IsComplement' Xpre := by
      apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hAPXpreDis
      rw [← Subgroup.normal_mul AP Xpre, hAPXpreSup]
      rfl
    have hXpreInv : ∀ e : E₁,
        Xpre.map (f e).toMonoidHom = Xpre := by
      intro e
      apply Subgroup.eq_of_le_of_card_ge
      · rintro _ ⟨x, hx, rfl⟩
        change q (f e x) ∈ X
        have hmap : fq e (q x) ∈ X.map (fq e).toMonoidHom :=
          ⟨q x, hx, rfl⟩
        rw [hXinv e] at hmap
        have haction : fq e (q x) = q (f e x) := by
          change frattiniQuotientMulAutHom P (f e)
              (QuotientGroup.mk' (frattini P) x) =
            QuotientGroup.mk' (frattini P) (f e x)
          exact frattiniQuotientMulAutHom_apply_mk (f e) x
        rw [← haction]
        exact hmap
      · exact (Subgroup.card_map_of_injective
          (K := Xpre)
          (f := (f e).toMonoidHom)
          (f e).injective).ge
    let X₀ : Subgroup G := Xpre.map P.subtype
    have hX₀P : X₀ ≤ P := Subgroup.map_subtype_le _
    have hE₁normX₀ : E₁ ≤ Subgroup.normalizer (X₀ : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro e he x hx
      rcases hx with ⟨xP, hxP, rfl⟩
      have hfx : f ⟨e, he⟩ xP ∈ Xpre := by
        have hm : f ⟨e, he⟩ xP ∈
            Xpre.map (f ⟨e, he⟩).toMonoidHom :=
          ⟨xP, hxP, rfl⟩
        rwa [hXpreInv ⟨e, he⟩] at hm
      refine ⟨f ⟨e, he⟩ xP, hfx, ?_⟩
      simp [f, j, Subgroup.normalizerMonoidHom, HSMul.hSMul]
    refine ⟨X₀, hX₀P, ?_, hE₁normX₀⟩
    exact
      { left_le := hA₀P
        right_le := hX₀P
        complement := by
          have hcomap : X₀.subgroupOf P = Xpre := by
            exact Subgroup.comap_map_eq_self_of_injective
              P.subtype_injective Xpre
          simpa [AP, hcomap] using hAPXpreComp
        commute := by
          intro a x
          letI : IsMulCommutative P := hPcomm
          exact congrArg Subtype.val
            (mul_comm (⟨a, hA₀P a.property⟩ : P)
              ⟨x, hX₀P x.property⟩) }

  have hInner :
      IsInternalSemidirectProductIn P E₁ (P ⊔ E₁) := by
    simpa only [hE₂eqP] using hSigmaCtx.E₂₁_sdprod
  have hOuter :
      IsInternalSemidirectProductIn E₃ (P ⊔ E₁) E := by
    simpa only [hE₂eqP] using hSigmaCtx.E₃_E₂₁_sdprod
  have hPE₁dis : Disjoint P E₁ :=
    disjoint_of_isComplement_subgroupOf_12_8
      hInner.1 hInner.2.1 hInner.2.2.2
  have hA₀PcompDis : Disjoint A₀ Pcomp :=
    disjoint_of_isComplement_subgroupOf_12_8
      hDirectPcomp.left_le hDirectPcomp.right_le
        hDirectPcomp.complement

  let K₀ : Subgroup G := Pcomp ⊔ E₁
  have hPcompE : Pcomp ≤ E := hPcompP.trans hPE
  have hK₀E : K₀ ≤ E := sup_le hPcompE hE₁E
  have hK₀PE₁ : K₀ ≤ P ⊔ E₁ := by
    exact sup_le (hPcompP.trans le_sup_left) le_sup_right
  have hPcompE₁dis : Disjoint Pcomp E₁ :=
    hPE₁dis.mono hPcompP le_rfl
  have hPcompE₁comp :
      (Pcomp.subgroupOf K₀).IsComplement'
        (E₁.subgroupOf K₀) := by
    simpa [K₀] using
      subgroupOf_sup_isComplement_12_8 hE₁normPcomp hPcompE₁dis

  have hA₀K₀dis : Disjoint A₀ K₀ := by
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    let xK₀ : K₀ := ⟨x, hx.2⟩
    obtain ⟨⟨a, e⟩, hae⟩ := hPcompE₁comp.2 xK₀
    have haeG :
        ((a : K₀) : G) * ((e : K₀) : G) = x := by
      simpa [xK₀] using congrArg Subtype.val hae
    have heP : ((e : K₀) : G) ∈ P := by
      have heEq : ((e : K₀) : G) =
          ((a : K₀) : G)⁻¹ * x := by
        rw [← haeG]
        group
      rw [heEq]
      exact P.mul_mem (P.inv_mem (hPcompP a.property))
        (hA₀P hx.1)
    have heBot : ((e : K₀) : G) ∈ (⊥ : Subgroup G) :=
      hPE₁dis.le_bot ⟨heP, e.property⟩
    have heOne : ((e : K₀) : G) = 1 :=
      Subgroup.mem_bot.mp heBot
    have hxPcomp : x ∈ Pcomp := by
      have hxEq : x = ((a : K₀) : G) := by
        rw [← haeG, heOne, mul_one]
      rw [hxEq]
      exact a.property
    exact hA₀PcompDis.le_bot ⟨hx.1, hxPcomp⟩

  have hE₃PE₁dis : Disjoint E₃ (P ⊔ E₁) :=
    disjoint_of_isComplement_subgroupOf_12_8
      hOuter.1 hOuter.2.1 hOuter.2.2.2
  have hE₃K₀dis : Disjoint E₃ K₀ :=
    hE₃PE₁dis.mono le_rfl hK₀PE₁
  have hEnormE₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃E).mp
      hSigmaCtx.E₃_normal
  have hK₀normE₃ : K₀ ≤ Subgroup.normalizer (E₃ : Set G) :=
    hK₀E.trans hEnormE₃
  let E₀ : Subgroup G := E₃ ⊔ K₀
  have hE₀E : E₀ ≤ E := sup_le hE₃E hK₀E
  have hE₃K₀comp :
      (E₃.subgroupOf E₀).IsComplement'
        (K₀.subgroupOf E₀) := by
    simpa [E₀] using
      subgroupOf_sup_isComplement_12_8 hK₀normE₃ hE₃K₀dis

  have hA₀E₀dis : Disjoint A₀ E₀ := by
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    let xE₀ : E₀ := ⟨x, hx.2⟩
    obtain ⟨⟨e₃, k⟩, hek⟩ := hE₃K₀comp.2 xE₀
    have hekG :
        ((e₃ : E₀) : G) * ((k : E₀) : G) = x := by
      simpa [xE₀] using congrArg Subtype.val hek
    have he₃PE₁ : ((e₃ : E₀) : G) ∈ P ⊔ E₁ := by
      have he₃Eq : ((e₃ : E₀) : G) =
          x * ((k : E₀) : G)⁻¹ := by
        rw [← hekG]
        group
      rw [he₃Eq]
      have hxPE₁ : x ∈ P ⊔ E₁ :=
        (show P ≤ P ⊔ E₁ from le_sup_left) (hA₀P hx.1)
      exact (P ⊔ E₁).mul_mem
        hxPE₁
        ((P ⊔ E₁).inv_mem (hK₀PE₁ k.property))
    have he₃Bot : ((e₃ : E₀) : G) ∈ (⊥ : Subgroup G) :=
      hE₃PE₁dis.le_bot ⟨e₃.property, he₃PE₁⟩
    have he₃One : ((e₃ : E₀) : G) = 1 :=
      Subgroup.mem_bot.mp he₃Bot
    have hxK₀ : x ∈ K₀ := by
      have hxEq : x = ((k : E₀) : G) := by
        rw [← hekG, he₃One, one_mul]
      rw [hxEq]
      exact k.property
    exact hA₀K₀dis.le_bot ⟨hx.1, hxK₀⟩

  have hA₀PcompSup : A₀ ⊔ Pcomp = P :=
    sup_eq_of_isComplement_subgroupOf_12_8
      hDirectPcomp.left_le hDirectPcomp.right_le
        hDirectPcomp.complement
  have hE₃PE₁sup : E₃ ⊔ (P ⊔ E₁) = E :=
    sup_eq_of_isComplement_subgroupOf_12_8
      hOuter.1 hOuter.2.1 hOuter.2.2.2
  have hA₀E₀sup : A₀ ⊔ E₀ = E := by
    calc
      A₀ ⊔ E₀ = A₀ ⊔ (E₃ ⊔ (Pcomp ⊔ E₁)) := rfl
      _ = E₃ ⊔ ((A₀ ⊔ Pcomp) ⊔ E₁) := by ac_rfl
      _ = E₃ ⊔ (P ⊔ E₁) := by rw [hA₀PcompSup]
      _ = E := hE₃PE₁sup
  have hA₀normalE : (A₀.subgroupOf E).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hA₀E).mpr hEnormA₀
  have hE₀normA₀ : E₀ ≤ Subgroup.normalizer (A₀ : Set G) :=
    hE₀E.trans hEnormA₀
  have hA₀E₀comp :
      (A₀.subgroupOf E).IsComplement' (E₀.subgroupOf E) := by
    have hcomp :=
      subgroupOf_sup_isComplement_12_8 hE₀normA₀ hA₀E₀dis
    rw [hA₀E₀sup] at hcomp
    exact hcomp
  have hSemidirectE₀ :
      IsInternalSemidirectProductIn A₀ E₀ E :=
    ⟨hA₀E, hE₀E, hA₀normalE, hA₀E₀comp⟩

  have hPrimeControl :
      ∀ x ∈ sigmaCore M, x ≠ 1 →
        primeSupport
            (Nat.card
              (centralizerWithin E₀ (Subgroup.zpowers x))) ⊆
          tau1Primes M := by
    intro x hxSigma hxne q hqCent
    letI : Fact q.Prime := ⟨hqCent.1⟩
    have hqE : q ∈ primeSupport (Nat.card E) := by
      refine ⟨hqCent.1, hqCent.2.trans ?_⟩
      exact Subgroup.card_dvd_of_le (inf_le_left.trans hE₀E)
    rcases primeSupport_sigma_complement_subset_tau hM hEM hHall hqE with
      (hqTau₁ | hqTau₂) | hqTau₃
    · exact hqTau₁
    · have hqp : q = p :=
        Set.mem_singleton_iff.mp (hTauSingleton ▸ hqTau₂)
      subst q
      obtain ⟨z, hzorder⟩ :=
        exists_prime_orderOf_dvd_card'
          (G := centralizerWithin E₀ (Subgroup.zpowers x)) p
            hqCent.2
      have hzorderG : orderOf (z : G) = p :=
        (Subgroup.orderOf_coe z).trans hzorder
      have hzne : (z : G) ≠ 1 := by
        have horderNe : orderOf (z : G) ≠ 1 := by
          rw [hzorderG]
          exact hpTau.1.ne_one
        simpa [orderOf_eq_one_iff] using horderNe
      let X : Subgroup G := Subgroup.zpowers (z : G)
      have hXcard : Nat.card X = p := by
        change Nat.card (Subgroup.zpowers (z : G)) = p
        rw [Nat.card_zpowers, hzorderG]
      have hXline : RankOneLineIn p E X :=
        ⟨Subgroup.zpowers_le.mpr (hE₀E z.property.1),
          isElementaryAbelianOfRank_one_of_card_eq_prime hXcard⟩
      have hXneA₀ : X ≠ A₀ := by
        intro hEq
        have hzA₀ : (z : G) ∈ A₀ := by
          rw [← hEq]
          exact Subgroup.mem_zpowers (z : G)
        have hzBot : (z : G) ∈ (⊥ : Subgroup G) :=
          hA₀E₀dis.le_bot ⟨hzA₀, z.property.1⟩
        exact hzne (Subgroup.mem_bot.mp hzBot)
      have hXCentZx : X ≤
          Subgroup.centralizer (Subgroup.zpowers x : Set G) :=
        Subgroup.zpowers_le.mpr z.property.2
      have hZxCentX : Subgroup.zpowers x ≤
          Subgroup.centralizer (X : Set G) :=
        Subgroup.le_centralizer_iff.mp hXCentZx
      have hxWithin : x ∈ centralizerWithin (sigmaCore M) X :=
        ⟨hxSigma, hZxCentX (Subgroup.mem_zpowers x)⟩
      have hxBot : x ∈ (⊥ : Subgroup G) := by
        rw [← (hRankControl X hXline hXneA₀).1]
        exact hxWithin
      exact (hxne (Subgroup.mem_bot.mp hxBot)).elim
    · obtain ⟨z, hzorder⟩ :=
        exists_prime_orderOf_dvd_card'
          (G := centralizerWithin E₀ (Subgroup.zpowers x)) q
            hqCent.2
      have hzorderG : orderOf (z : G) = q :=
        (Subgroup.orderOf_coe z).trans hzorder
      have hzne : (z : G) ≠ 1 := by
        have horderNe : orderOf (z : G) ≠ 1 := by
          rw [hzorderG]
          exact hqCent.1.ne_one
        simpa [orderOf_eq_one_iff] using horderNe
      let Z : Subgroup G := Subgroup.zpowers (z : G)
      have hZE : Z ≤ E :=
        Subgroup.zpowers_le.mpr (hE₀E z.property.1)
      have hZcard : Nat.card Z = q := by
        change Nat.card (Subgroup.zpowers (z : G)) = q
        rw [Nat.card_zpowers, hzorderG]
      have hZq : IsPGroup q Z :=
        (isElementaryAbelianOfRank_one_of_card_eq_prime hZcard).isPGroup
      let ZE : Subgroup E := Z.subgroupOf E
      have hZEq : IsPGroup q ZE :=
        hZq.of_equiv (Subgroup.subgroupOfEquivOfLe hZE).symm
      have hZEpi : IsPiNumber (tau3Primes M) (Nat.card ZE) :=
        hZEq.isPiNumber_natCard hqTau₃
      have hZEE₃ : ZE ≤ E₃.subgroupOf E :=
        le_normal_isHall_of_isPiNumber_12_8
          hSigmaCtx.E₃_normal hHallE₃ hZEpi
      let zE : E := ⟨(z : G), hE₀E z.property.1⟩
      have hzZE : zE ∈ ZE := by
        exact Subgroup.mem_zpowers (z : G)
      have hzE₃ : (z : G) ∈ E₃ := hZEE₃ hzZE
      let zE₃ : E₃ := ⟨(z : G), hzE₃⟩
      let xSigma : sigmaCore M := ⟨x, hxSigma⟩
      have hcomm : Commute x (z : G) :=
        z.property.2 x (Subgroup.mem_zpowers x)
      have hconj :
          (zE₃ : G) * (xSigma : G) * (zE₃ : G)⁻¹ =
            (xSigma : G) := by
        change (z : G) * x * (z : G)⁻¹ = x
        rw [hcomm.eq.symm]
        simp
      have hxOne : xSigma = 1 :=
        hRegular.E₃_regular zE₃ (by simpa [zE₃] using hzne)
          xSigma hconj
      exact (hxne (congrArg Subtype.val hxOne)).elim

  rw [hDefA₀]
  exact
    { tau2_eq := hTauSingleton
      A0_card := hA₀card
      fitting_decomposition := hFittingDirect
      rankOne_control := hRankControl
      exists_complement := ⟨E₀, hSemidirectE₀, hPrimeControl⟩ }

end

end Submission.OddOrder.BG.Section12
