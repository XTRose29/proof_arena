import Submission.OddOrder.BG.Section15.FittingCore
import Submission.OddOrder.BG.Section15.FittingCoreStructure
import Submission.OddOrder.BG.Section02.ExtraspecialPrimeSemidirectCycle
import Submission.OddOrder.BG.Section14.PartitionAndSignalizers
import Submission.OddOrder.BG.Section14.PTypeEmbedding
import Submission.OddOrder.BG.Section12.NonabelianTau2
import Submission.OddOrder.BG.Section12.AbelianTau2
import Submission.OddOrder.BG.Section12.SigmaEmbedding
import Submission.OddOrder.BG.Section10.BasicMaximalStructure
import Submission.OddOrder.BG.Section03.FrobeniusBasic
import Submission.OddOrder.MathlibSupport.NormalizedTI
import Mathlib.GroupTheory.Exponent
import Mathlib.GroupTheory.SpecificGroups.ZGroup

/-!
# Bender--Glauberman Section 15: non-TI Fitting intersections and signalizers

This module proves Theorem 15.7 from `BGsection15.v` and exposes the shared
proposition-valued conclusion interfaces used by the separately split modules
for Theorems 15.8 and 15.9.
-/

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

def conjugateSubgroup15 (H : Subgroup G) (g : G) : Subgroup G :=
  H.map (MulAut.conj g).toMonoidHom

def nonTIFittingIntersection (M : Subgroup G) (g : G) : Subgroup G :=
  fittingWithin M ⊓ conjugateSubgroup15 (fittingWithin M) g

abbrev fittingSigmaComplement (M : Subgroup G) : Subgroup G :=
  fittingSigmaPrimeCore M

abbrev elementNormalizer15 (x : G) : Subgroup G :=
  ftSignalizerBase x

structure NonTISigmaComplementStructureData
    (E E₁ E₂ E₃ : Subgroup G) : Type u where
  E₃_eq_bot : E₃ = ⊥
  E₂_normal : (E₂.subgroupOf E).Normal
  quotient_equiv :
    letI := E₂_normal
    (E ⧸ E₂.subgroupOf E) ≃* E₁
  quotient_cyclic :
    letI := E₂_normal
    IsCyclic (E ⧸ E₂.subgroupOf E)

def NonTISigmaComplementStructure
    (E E₁ E₂ E₃ : Subgroup G) : Prop :=
  Nonempty (NonTISigmaComplementStructureData E E₁ E₂ E₃)

namespace NonTISigmaComplementStructure

noncomputable def witness
    {E E₁ E₂ E₃ : Subgroup G}
    (h : NonTISigmaComplementStructure E E₁ E₂ E₃) :
    NonTISigmaComplementStructureData E E₁ E₂ E₃ :=
  Classical.choice h

theorem E₃_eq_bot
    {E E₁ E₂ E₃ : Subgroup G}
    (h : NonTISigmaComplementStructure E E₁ E₂ E₃) : E₃ = ⊥ :=
  h.witness.E₃_eq_bot

theorem E₂_normal
    {E E₁ E₂ E₃ : Subgroup G}
    (h : NonTISigmaComplementStructure E E₁ E₂ E₃) :
    (E₂.subgroupOf E).Normal :=
  h.witness.E₂_normal

noncomputable def quotient_equiv
    {E E₁ E₂ E₃ : Subgroup G}
    (h : NonTISigmaComplementStructure E E₁ E₂ E₃) :
    letI := h.witness.E₂_normal
    (E ⧸ E₂.subgroupOf E) ≃* E₁ :=
  h.witness.quotient_equiv

theorem quotient_cyclic
    {E E₁ E₂ E₃ : Subgroup G}
    (h : NonTISigmaComplementStructure E E₁ E₂ E₃) :
    letI := h.witness.E₂_normal
    IsCyclic (E ⧸ E₂.subgroupOf E) :=
  h.witness.quotient_cyclic

end NonTISigmaComplementStructure

structure NonTIFittingAbelianCase (M : Subgroup G) : Prop where
  typeF : M ∈ typeFMaximalSubgroups (G := G)
  core_abelian : IsMulCommutative (Fitting_core M)
  rank_two : ∃ p : ℕ, p.Prime ∧
    HasElementaryAbelianRankAtLeast p 2 (Fitting_core M)
  rank_at_most_two : ∀ p : ℕ, p.Prime →
    ¬ HasElementaryAbelianRankAtLeast p 3 (Fitting_core M)

structure NonTIFittingNonabelianCase
    (M : Subgroup G) (g : G) : Prop where
  p_prime : (Nat.card (nonTIFittingIntersection M g)).Prime
  pcore_nonabelian :
    ¬ IsMulCommutative
      (pCore (Nat.card (nonTIFittingIntersection M g)) (Fitting_core M))
  pPrimeCore_cyclic :
    IsCyclic
      (pPrimeCore (Nat.card (nonTIFittingIntersection M g))
        (Fitting_core M))
  conclusion :
    (∀ q ∈ primeSupport (Nat.card (Fitting_core M)),
      Monoid.exponent
          (M ⧸ (Fitting_core M).subgroupOf M) ∣ q - 1) ∨
    (Nat.card
          (pCore (Nat.card (nonTIFittingIntersection M g))
            (Fitting_core M)) =
        Nat.card (nonTIFittingIntersection M g) ^ 3 ∧
      M ∈ typeP1MaximalSubgroups (G := G) ∧
      Nat.card (M ⧸ (Fitting_core M).subgroupOf M) ∣
        Nat.card (nonTIFittingIntersection M g) + 1)

structure NonTIFittingStructure (M : Subgroup G) (g : G) : Prop where
  typeF_or_typeP1 :
    M ∈ typeFMaximalSubgroups (G := G) ∨
      M ∈ typeP1MaximalSubgroups (G := G)
  core_eq_sigma : Fitting_core M = sigmaCore M
  intersection_le_core : nonTIFittingIntersection M g ≤ Fitting_core M
  intersection_cyclic : IsCyclic (nonTIFittingIntersection M g)
  commutator_le_fitting :
    (_root_.commutator M).map M.subtype ≤ fittingWithin M
  fitting_decomposition :
    IsInternalDirectProductIn (sigmaCore M)
      (fittingSigmaComplement M) (fittingWithin M)
  sigma_complement_structure :
    ∀ {E E₁ E₂ E₃ : Subgroup G},
      sigma_complement M E E₁ E₂ E₃ →
        NonTISigmaComplementStructure E E₁ E₂ E₃
  final_case :
    NonTIFittingAbelianCase M ∨ NonTIFittingNonabelianCase M g

structure Tau2P2TypeSignalizerConclusion
    (M K H : Subgroup G) : Prop where
  card_K_prime : (Nat.card K).Prime
  tau2_H_eq : tau2Primes H = {Nat.card K}
  M_tau2_complement :
    IsPiNumber (tau2Primes M)ᶜ (Nat.card M)

structure NonFTypeSignalizerBaseConclusionData
    (M : Subgroup G) (x : G) : Type u where
  M_typeF : M ∈ typeFMaximalSubgroups (G := G)
  normalizer_typeP2 :
    elementNormalizer15 x ∈ typeP2MaximalSubgroups (G := G)
  complement : Subgroup G
  complement_le : complement ≤ M
  complement_hall :
    IsHall (sigmaPrimes M)ᶜ (complement.subgroupOf M)
  complement_cyclic : IsCyclic complement
  frobenius :
    IsFrobeniusDecomposition
      ((sigmaCore M).subgroupOf M) (complement.subgroupOf M)

def NonFTypeSignalizerBaseConclusion
    (M : Subgroup G) (x : G) : Prop :=
  Nonempty (NonFTypeSignalizerBaseConclusionData M x)

namespace NonFTypeSignalizerBaseConclusion

noncomputable def witness
    {M : Subgroup G} {x : G}
    (h : NonFTypeSignalizerBaseConclusion M x) :
    NonFTypeSignalizerBaseConclusionData M x :=
  Classical.choice h

theorem M_typeF
    {M : Subgroup G} {x : G}
    (h : NonFTypeSignalizerBaseConclusion M x) :
    M ∈ typeFMaximalSubgroups (G := G) :=
  h.witness.M_typeF

theorem normalizer_typeP2
    {M : Subgroup G} {x : G}
    (h : NonFTypeSignalizerBaseConclusion M x) :
    elementNormalizer15 x ∈ typeP2MaximalSubgroups (G := G) :=
  h.witness.normalizer_typeP2

noncomputable abbrev complement
    {M : Subgroup G} {x : G}
    (h : NonFTypeSignalizerBaseConclusion M x) : Subgroup G :=
  h.witness.complement

theorem complement_le
    {M : Subgroup G} {x : G}
    (h : NonFTypeSignalizerBaseConclusion M x) :
    h.complement ≤ M := by
  simpa [complement] using h.witness.complement_le

theorem complement_hall
    {M : Subgroup G} {x : G}
    (h : NonFTypeSignalizerBaseConclusion M x) :
    IsHall (sigmaPrimes M)ᶜ (h.complement.subgroupOf M) := by
  simpa [complement] using h.witness.complement_hall

theorem complement_cyclic
    {M : Subgroup G} {x : G}
    (h : NonFTypeSignalizerBaseConclusion M x) :
    IsCyclic h.complement := by
  simpa [complement] using h.witness.complement_cyclic

theorem frobenius
    {M : Subgroup G} {x : G}
    (h : NonFTypeSignalizerBaseConclusion M x) :
    IsFrobeniusDecomposition
      ((sigmaCore M).subgroupOf M) (h.complement.subgroupOf M) := by
  simpa [complement] using h.witness.frobenius

end NonFTypeSignalizerBaseConclusion

/-! ## Local transport lemmas

The source moves repeatedly between intrinsic subgroups and their ambient
images.  Keeping those transports here makes the three theorem proofs read
in terms of the mathematical subgroups rather than subtype bookkeeping. -/

private theorem nonTIFittingIntersection_le_fitting
    (M : Subgroup G) (g : G) :
    nonTIFittingIntersection M g ≤ fittingWithin M :=
  inf_le_left

private theorem nonTIFittingIntersection_le_conjugate
    (M : Subgroup G) (g : G) :
    nonTIFittingIntersection M g ≤
      conjugateSubgroup15 (fittingWithin M) g :=
  inf_le_right

private theorem quotient_cyclic_of_equiv15
    {E E₁ E₂ : Subgroup G}
    (hE₂ : (E₂.subgroupOf E).Normal)
    (e : letI := hE₂; (E ⧸ E₂.subgroupOf E) ≃* E₁)
    (hcyc : IsCyclic E₁) :
    letI := hE₂
    IsCyclic (E ⧸ E₂.subgroupOf E) := by
  letI := hE₂
  exact e.isCyclic.mpr hcyc

private theorem semidirect_right_eq_ambient_of_left_eq_bot15
    {A B K : Subgroup G}
    (h : IsInternalSemidirectProductIn A B K)
    (hA : A = ⊥) : B = K := by
  apply le_antisymm h.2.1
  have hsup := h.2.2.2.sup_eq_top
  rw [hA, Subgroup.bot_subgroupOf, bot_sup_eq] at hsup
  exact Subgroup.subgroupOf_eq_top.mp hsup

private theorem semidirect_left_eq_ambient_of_right_eq_bot15
    {A B K : Subgroup G}
    (h : IsInternalSemidirectProductIn A B K)
    (hB : B = ⊥) : A = K := by
  apply le_antisymm h.1
  have hsup := h.2.2.2.sup_eq_top
  rw [hB, Subgroup.bot_subgroupOf, sup_bot_eq] at hsup
  exact Subgroup.subgroupOf_eq_top.mp hsup

private noncomputable def semidirectQuotientEquiv15
    {N A K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N A K) :
    letI := hsd.2.2.1
    K ⧸ N.subgroupOf K ≃* A := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  exact hsd.2.2.2.symm.QuotientMulEquiv.trans
    (Subgroup.subgroupOfEquivOfLe hsd.2.1)

private theorem semidirect_quotient_card15
    {N A K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N A K) :
    letI := hsd.2.2.1
    Nat.card (K ⧸ N.subgroupOf K) = Nat.card A := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  exact Nat.card_congr (semidirectQuotientEquiv15 hsd).toEquiv

private theorem semidirect_quotient_exponent15
    {N A K : Subgroup G}
    (hsd : IsInternalSemidirectProductIn N A K) :
    letI := hsd.2.2.1
    Monoid.exponent (K ⧸ N.subgroupOf K) = Monoid.exponent A := by
  letI : (N.subgroupOf K).Normal := hsd.2.2.1
  exact Monoid.exponent_eq_of_mulEquiv (semidirectQuotientEquiv15 hsd)

/-- A subgroup supported on `pi` lies in a normal `pi`-Hall subgroup. -/
private theorem subgroup_le_normal_isHall15
    {K : Type u} [Group K] [Finite K] {pi : Set ℕ}
    {N L : Subgroup K} (hNnormal : N.Normal)
    (hNHall : IsHall pi N) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ N := by
  letI : N.Normal := hNnormal
  have hcop : (Nat.card L).Coprime N.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hNHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let q : K →* (K ⧸ N) := QuotientGroup.mk' N
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp horderOne)

/-- An ambiently represented Sylow subgroup is a singleton Hall subgroup
inside the subgroup in which it is Sylow. -/
private theorem isHall_singleton_of_isSylowSubgroupOf15
    {p : ℕ} [Fact p.Prime] {S H : Subgroup G}
    (hS : IsSylowSubgroupOf p S H) :
    IsHall ({p} : Set ℕ) (S.subgroupOf H) := by
  have hSH : S ≤ H := by
    rcases hS with ⟨P, rfl⟩
    exact Subgroup.map_subtype_le _
  constructor
  · rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hSH]
    exact hS.isPGroup.isPiNumber_natCard (Set.mem_singleton p)
  · intro q hq hqIndex hqp
    have hqp' : q = p := Set.mem_singleton_iff.mp hqp
    subst q
    obtain ⟨P, hSP⟩ := hS
    have hindex : (S.subgroupOf H).index = P.index := by
      have hsubEq : S.subgroupOf H = (P : Subgroup H) := by
        rw [hSP]
        exact Subgroup.comap_map_eq_self_of_injective
          H.subtype_injective (P : Subgroup H)
      rw [hsubEq]
    rw [hindex] at hqIndex
    exact P.not_dvd_index hqIndex

/-- A Sylow subgroup of a Hall subgroup is Sylow in the whole ambient
group. -/
private theorem sylow_of_sylow_hall15
    {pi : Set ℕ} {p : ℕ} [Fact p.Prime] {S H : Subgroup G}
    (hS : IsSylowSubgroupOf p S H) (hH : IsHall pi H)
    (hp : p ∈ pi) :
    IsSylowSubgroupOf p S (⊤ : Subgroup G) := by
  have hpIndex : ¬ p ∣ (H.subgroupOf (⊤ : Subgroup G)).index := by
    intro hpIndex
    apply hH.isPiNumber_index (Fact.out : p.Prime) ?_ hp
    change p ∣ H.relIndex (⊤ : Subgroup G) at hpIndex
    simpa only [H.relIndex_top_right] using hpIndex
  exact hS.extend_of_not_dvd_index le_top hpIndex

/-- Move an elementary-abelian rank witness into an ambiently represented
Sylow subgroup. -/
private theorem exists_elementaryAbelian_le_ambientSylow15
    {H Q : Subgroup G} {p n : ℕ} [Fact p.Prime]
    (hQH : IsSylowSubgroupOf p Q H)
    (hRank : HasElementaryAbelianRankAtLeast p n H) :
    ∃ A : Subgroup G, A ≤ Q ∧ IsElementaryAbelianOfRank p n A := by
  classical
  rcases hQH with ⟨P, hQP⟩
  rcases hRank with ⟨A, hAH, hA⟩
  let AH : Subgroup H := A.subgroupOf H
  have hAHrank : IsElementaryAbelianOfRank p n AH :=
    hA.subgroupOf hAH
  obtain ⟨R, hAHR⟩ := hAHrank.isPGroup.exists_le_sylow
  obtain ⟨h, hh⟩ := MulAction.exists_smul_eq H R P
  let B : Subgroup H := AH.map (MulAut.conj h).toMonoidHom
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

/-- Cauchy's theorem packaged as an ambient rank-one line. -/
private theorem exists_rankOneLineIn_of_primeSupport15
    {K : Subgroup G} {p : ℕ}
    (hpK : p ∈ primeSupport (Nat.card K)) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElementaryAbelianOfRank p 1 P := by
  letI : Fact p.Prime := ⟨hpK.1⟩
  obtain ⟨x, hx⟩ :=
    exists_prime_orderOf_dvd_card' (G := K) p hpK.2
  let P : Subgroup G := (Subgroup.zpowers x).map K.subtype
  have hcardP : Nat.card P = p := by
    dsimp only [P]
    rw [Subgroup.card_map_of_injective K.subtype_injective,
      Nat.card_zpowers, hx]
  exact ⟨P, Subgroup.map_subtype_le _,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcardP⟩

/-- Distinct-prime subgroups of a finite nilpotent group centralize one
another. -/
private theorem pSubgroups_centralize_of_nilpotent15
    {H A B : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hpq : p ≠ q) (hAp : IsPGroup p A) (hBq : IsPGroup q B)
    (hAH : A ≤ H) (hBH : B ≤ H)
    (hnil : Group.IsNilpotent H) :
    A ≤ Subgroup.centralizer (B : Set G) := by
  let AH : Subgroup H := A.subgroupOf H
  let BH : Subgroup H := B.subgroupOf H
  have hAHp : IsPGroup p AH :=
    hAp.of_equiv (Subgroup.subgroupOfEquivOfLe hAH).symm
  have hBHq : IsPGroup q BH :=
    hBq.of_equiv (Subgroup.subgroupOfEquivOfLe hBH).symm
  obtain ⟨S, hAHS⟩ := hAHp.exists_le_sylow
  obtain ⟨T, hBHT⟩ := hBHq.exists_le_sylow
  letI : Group.IsNilpotent H := hnil
  have hSnormal : (S : Subgroup H).Normal := by infer_instance
  have hTnormal : (T : Subgroup H).Normal := by infer_instance
  letI : (S : Subgroup H).Normal := hSnormal
  letI : (T : Subgroup H).Normal := hTnormal
  have hcop : Nat.Coprime (Nat.card (S : Subgroup H))
      (Nat.card (T : Subgroup H)) :=
    IsPGroup.coprime_card_of_ne p q hpq
      (S : Subgroup H) (T : Subgroup H) S.isPGroup' T.isPGroup'
  have hdis : Disjoint (S : Subgroup H) (T : Subgroup H) :=
    Subgroup.disjoint_of_coprime_natCard hcop
  have hcommBot :
      ⁅(S : Subgroup H), (T : Subgroup H)⁆ = (⊥ : Subgroup H) := by
    apply le_antisymm
    · exact (Subgroup.commutator_le_inf
        (H₁ := (S : Subgroup H)) (H₂ := (T : Subgroup H))).trans
          hdis.le_bot
    · exact bot_le
  have hcentST : (S : Subgroup H) ≤
      Subgroup.centralizer ((T : Subgroup H) : Set H) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  let aH : H := ⟨a, hAH ha⟩
  let bH : H := ⟨b, hBH hb⟩
  have haS : aH ∈ (S : Subgroup H) :=
    hAHS (show aH ∈ AH from ha)
  have hbT : bH ∈ (T : Subgroup H) :=
    hBHT (show bH ∈ BH from hb)
  exact congrArg Subtype.val
    (Subgroup.mem_centralizer_iff.mp (hcentST haS) bH hbT)

/-- Characteristic subgroups, mapped from an ambient subgroup, are
normalized by the normalizer of that ambient subgroup. -/
private theorem characteristic_map_subtype_le_normalizer15
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
    have hback := characteristic_map_subtype_invariant_under_normalizer
      S (Subgroup.normalizer (S : Set K)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using hback

private theorem map_conj_inv_map_conj15
    {K : Type*} [Group K] (A : Subgroup K) (a : K) :
    (A.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom = A := by
  rw [Subgroup.map_map]
  convert A.map_id using 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem pCoreWithin_normal15 (p : ℕ) (M : Subgroup G) :
    ((pCoreWithin p M).subgroupOf M).Normal := by
  change (((pCore p M).map M.subtype).comap M.subtype).Normal
  rw [Subgroup.comap_map_eq_self_of_injective M.subtype_injective]
  infer_instance

private theorem isNilpotent_of_le15
    {A B : Subgroup G} (hB : Group.IsNilpotent B) (hAB : A ≤ B) :
    Group.IsNilpotent A := by
  letI : Group.IsNilpotent B := hB
  have hsub : Group.IsNilpotent (A.subgroupOf B) := by infer_instance
  letI : Group.IsNilpotent (A.subgroupOf B) := hsub
  exact Group.nilpotent_of_mulEquiv
    (Subgroup.subgroupOfEquivOfLe hAB)

private theorem isSolvable_of_le15
    {A B : Subgroup G} (hB : IsSolvable B) (hAB : A ≤ B) :
    IsSolvable A :=
  isSolvable_of_injective (Subgroup.inclusion hAB)
    (Subgroup.inclusion_injective hAB)

private theorem isMulCommutative_of_le15
    {K₀ : Type*} [Group K₀] {K L : Subgroup K₀}
    (hK : IsMulCommutative K) (hLK : L ≤ K) :
    IsMulCommutative L := by
  apply isMulCommutative_iff.mpr
  intro x y
  apply L.subtype_injective
  exact congrArg Subtype.val
    (isMulCommutative_iff.mp hK
      ⟨x, hLK x.2⟩ ⟨y, hLK y.2⟩)

/-- A finite nilpotent group is abelian when all its prime cores are. -/
private theorem nilpotent_isMulCommutative_of_pCores15
    {K : Type*} [Group K] [Finite K]
    (hnil : Group.IsNilpotent K)
    (hcores : ∀ p : ℕ, p.Prime →
      IsMulCommutative (pCore p K)) :
    IsMulCommutative K := by
  letI : Group.IsNilpotent K := hnil
  have hfitCenter : fittingCore K ≤ Subgroup.center K := by
    rw [fittingCore]
    apply iSup_le
    intro q
    letI : Fact (q : ℕ).Prime := ⟨q.property⟩
    let P : Subgroup K := pCore (q : ℕ) K
    let C : Subgroup K := pPrimeCore (q : ℕ) K
    have hPcomm : IsMulCommutative P := by
      simpa [P] using hcores q q.property
    have hPC : P ≤ Subgroup.centralizer (C : Set K) := by
      simpa [P, C] using
        (pCore_le_centralizer_pPrimeCore (G := K) (q : ℕ))
    have hsup : P ⊔ C = ⊤ := by
      simpa [P, C] using
        (sup_pCore_pPrimeCore_eq_top_of_isNilpotent
          (G := K) (q : ℕ))
    intro x hxP
    rw [Subgroup.mem_center_iff]
    intro y
    have hySup : y ∈ P ⊔ C := by rw [hsup]; trivial
    rcases Subgroup.mem_sup_of_normal_left.mp hySup with
      ⟨a, haP, b, hbC, hab⟩
    have hxa : Commute x a := by
      exact congrArg Subtype.val
        (isMulCommutative_iff.mp hPcomm ⟨x, hxP⟩ ⟨a, haP⟩)
    have hxb : Commute x b := by
      exact (Subgroup.mem_centralizer_iff.mp (hPC hxP) b hbC).symm
    rw [← hab]
    exact (hxa.mul_right hxb).eq.symm
  have htopNil : Group.IsNilpotent (⊤ : Subgroup K) :=
    Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm
  have htopFit : (⊤ : Subgroup K) ≤ fittingCore K :=
    nilpotent_normal_le_fittingCore (by infer_instance) htopNil
  apply Subgroup.center_eq_top_iff.mp
  exact top_unique (htopFit.trans hfitCenter)

/-- The ambient image of `Omega_1(Z(P))` is nontrivial in a nontrivial
finite `p`-group. -/
private theorem omegaOneCenterAmbient_ne_bot15
    {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {P : Subgroup K}
    (hPp : IsPGroup p P) (hPne : P ≠ ⊥) :
    omegaOneCenterAmbient p P ≠ ⊥ := by
  letI : Nontrivial P := P.nontrivial_iff_ne_bot.mpr hPne
  let Z : Subgroup P := Subgroup.center P
  have hZne : Z ≠ ⊥ := by
    letI : Group.IsNilpotent P := hPp.isNilpotent
    exact Group.IsNilpotent.center_ne_bot P
  have hZp : IsPGroup p Z := hPp.to_subgroup Z
  have hZcard : Nat.card Z ≠ 1 :=
    (Z.one_lt_card_iff_ne_bot.mpr hZne).ne'
  have hOmegaNe : omegaOne p Z ≠ ⊥ :=
    omegaOne_ne_bot_of_isPGroup hZp hZcard
  have hCenterOmegaNe :
      Submission.OddOrder.BG.Section05.omegaOneCenter p P ≠ ⊥ := by
    dsimp [Submission.OddOrder.BG.Section05.omegaOneCenter, Z]
    exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
      (omegaOne p (Subgroup.center P))
      (Subgroup.center P).subtype_injective)).mpr hOmegaNe
  dsimp [omegaOneCenterAmbient]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
    (Submission.OddOrder.BG.Section05.omegaOneCenter p P)
    P.subtype_injective)).mpr hCenterOmegaNe

/-- A proper elementary-abelian overgroup of a rank-two subgroup contains
an elementary-abelian rank-three subgroup. -/
private theorem exists_rankThree_of_rankTwo_lt15
    {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {A E : Subgroup K}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hE : IsElementaryAbelianGroup p E) (hAE : A < E) :
    ∃ F : Subgroup K, F ≤ E ∧ IsElementaryAbelianOfRank p 3 F := by
  obtain ⟨n, hEcard⟩ := hE.isPGroup.exists_card_eq
  have hpowlt : p ^ 2 < p ^ n := by
    simpa only [hA.card_eq, hEcard] using
      natCard_subgroup_lt_of_lt hAE
  have hn : 3 ≤ n := by
    by_contra hnot
    have hnle : n ≤ 2 := by omega
    exact (not_lt_of_ge
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle)) hpowlt
  have hpThreeLe : p ^ 3 ≤ Nat.card E := by
    rw [hEcard]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn
  obtain ⟨F₀, hF₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := E) (Fact.out : p.Prime) hE.isPGroup hpThreeLe
  have hF₀ : IsElementaryAbelianOfRank p 3 F₀ := by
    letI : IsMulCommutative E := hE.commutative
    refine
      { isPGroup := hE.isPGroup.to_subgroup F₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hF₀card }
    intro x
    apply Subtype.ext
    exact hE.pow_eq_one (x : E)
  let F : Subgroup K := F₀.map E.subtype
  exact ⟨F, Subgroup.map_subtype_le F₀,
    hF₀.map_of_injective E.subtype E.subtype_injective⟩

/-- A rank-one subgroup of a cyclic `p`-group is its omega-one subgroup. -/
private theorem rankOneLine_eq_omegaOne_of_cyclic_pgroup15
    {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {X L : Subgroup K}
    (hXcyclic : IsCyclic X) (hXp : IsPGroup p X)
    (hLX : L ≤ X) (hL : IsElementaryAbelianOfRank p 1 L) :
    L = (omegaOne p X).map X.subtype := by
  let A : Subgroup K := (omegaOne p X).map X.subtype
  have hLA : L ≤ A := by
    intro x hx
    let xX : X := ⟨x, hLX hx⟩
    have hxpow : xX ^ p = 1 := by
      apply Subtype.ext
      exact congrArg (fun y : L ↦ (y : K))
        (hL.pow_eq_one ⟨x, hx⟩)
    exact ⟨xX, mem_omegaOne_of_pow_eq_one p hxpow, rfl⟩
  have hXcard : Nat.card X ≠ 1 := by
    intro hcard
    have hLcard : Nat.card L = 1 := by
      apply Nat.eq_one_of_dvd_one
      rw [← hcard]
      exact Subgroup.card_dvd_of_le hLX
    rw [hL.card_eq, pow_one] at hLcard
    exact (Fact.out : p.Prime).ne_one hLcard
  letI : IsCyclic X := hXcyclic
  have hOmegaCard : Nat.card (omegaOne p X) = p :=
    card_omegaOne_of_isCyclic_isPGroup
      (Fact.out : p.Prime) hXp hXcard
  apply Subgroup.eq_of_le_of_card_ge hLA
  dsimp only [A]
  rw [hL.card_eq, pow_one,
    Subgroup.card_map_of_injective X.subtype_injective, hOmegaCard]

/-- Distinct subgroups of the same prime order are disjoint. -/
private theorem disjoint_of_card_eq_prime_of_ne15
    {K : Type*} [Group K] [Finite K]
    {p : ℕ} (hp : p.Prime) {A B : Subgroup K}
    (hAcard : Nat.card A = p) (hBcard : Nat.card B = p)
    (hne : A ≠ B) : Disjoint A B := by
  rw [disjoint_iff]
  by_contra hInf
  have hdiv : Nat.card (A ⊓ B : Subgroup K) ∣ p := by
    simpa [hAcard] using
      (Subgroup.card_dvd_of_le (show A ⊓ B ≤ A from inf_le_left))
  rcases (Nat.dvd_prime hp).mp hdiv with hcardOne | hcardP
  · exact hInf (Subgroup.eq_bot_of_card_eq (A ⊓ B) hcardOne)
  · have hInfA : A ⊓ B = A := by
      apply Subgroup.eq_of_le_of_card_ge inf_le_left
      rw [hcardP, hAcard]
    have hAB : A ≤ B := by
      intro x hx
      have hxInf : x ∈ A ⊓ B := by rw [hInfA]; exact hx
      exact hxInf.2
    exact hne (Subgroup.eq_of_le_of_card_ge hAB (by
      rw [hAcard, hBcard]))

private theorem disjoint_of_prime_cards_of_ne15
    {K : Type*} [Group K] [Finite K]
    {A B : Subgroup K}
    (hA : (Nat.card A).Prime) (hB : (Nat.card B).Prime)
    (hne : A ≠ B) : Disjoint A B := by
  rw [disjoint_iff]
  by_contra hInf
  have hdivA : Nat.card (A ⊓ B : Subgroup K) ∣ Nat.card A :=
    Subgroup.card_dvd_of_le (show A ⊓ B ≤ A from inf_le_left)
  rcases (Nat.dvd_prime hA).mp hdivA with hcardOne | hcardA
  · exact hInf (Subgroup.eq_bot_of_card_eq (A ⊓ B) hcardOne)
  have hInfA : A ⊓ B = A := by
    apply Subgroup.eq_of_le_of_card_ge inf_le_left
    rw [hcardA]
  have hAB : A ≤ B := by
    intro x hx
    have hxInf : x ∈ A ⊓ B := by rw [hInfA]; exact hx
    exact hxInf.2
  have hdivB : Nat.card A ∣ Nat.card B :=
    Subgroup.card_dvd_of_le hAB
  have hcardEq : Nat.card A = Nat.card B :=
    (Nat.dvd_prime hB).mp hdivB |>.resolve_left hA.ne_one
  exact hne (Subgroup.eq_of_le_of_card_ge hAB hcardEq.ge)

private theorem map_centralizerWithin_subgroupOf15
    {K : Type*} [Group K]
    {J V : Subgroup K} (hVJ : V ≤ J) (A : Subgroup J) :
    (centralizerWithin (V.subgroupOf J) A).map J.subtype =
      centralizerWithin V (A.map J.subtype) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hy.1, ?_⟩
    rintro _ ⟨a, ha, rfl⟩
    exact congrArg Subtype.val (hy.2 a ha)
  · intro hx
    let xJ : J := ⟨x, hVJ hx.1⟩
    refine ⟨xJ, ?_, rfl⟩
    refine ⟨hx.1, ?_⟩
    intro a ha
    apply Subtype.ext
    exact hx.2 (a : K) (Subgroup.mem_map_of_mem J.subtype ha)

private theorem subgroupOf_sup_isComplement15
    {K : Type*} [Group K] {H R : Subgroup K}
    (hnorm : R ≤ Subgroup.normalizer (H : Set K))
    (hdis : Disjoint H R) :
    (H.subgroupOf (H ⊔ R)).IsComplement'
      (R.subgroupOf (H ⊔ R)) := by
  let J : Subgroup K := H ⊔ R
  let HJ : Subgroup J := H.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  letI : HJ.Normal := by
    have hnormal :=
      Subgroup.normal_subgroupOf_sup_of_le_normalizer hnorm
    rw [sup_comm] at hnormal
    simpa [HJ, J] using hnormal
  have hdisJ : Disjoint HJ RJ := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxbot : ((x : J) : K) ∈ (⊥ : Subgroup K) := by
      rw [← disjoint_iff.mp hdis]
      exact ⟨hx.1, hx.2⟩
    exact Subgroup.mem_bot.mp hxbot
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisJ
  have hsup : HJ ⊔ RJ = ⊤ := by
    change H.subgroupOf J ⊔ R.subgroupOf J = ⊤
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self J
  rw [← Subgroup.normal_mul HJ RJ, hsup]
  rfl

private theorem omegaOne_eq_top_of_pow_eq_one15
    {K : Type*} [Group K] {p : ℕ}
    (hpow : ∀ x : K, x ^ p = 1) :
    omegaOne p K = ⊤ := by
  apply top_unique
  intro x _
  exact mem_omegaOne_of_pow_eq_one p (hpow x)

private theorem card_omegaOneCenterAmbient_of_cyclic_pgroup15
    {K : Type*} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime] {P : Subgroup K}
    (hPcyclic : IsCyclic P) (hPp : IsPGroup p P)
    (hPne : P ≠ ⊥) :
    Nat.card (omegaOneCenterAmbient p P) = p := by
  letI : IsCyclic P := hPcyclic
  have hPcomm : IsMulCommutative P := by infer_instance
  have hcenter : Subgroup.center P = ⊤ :=
    Subgroup.center_eq_top_iff.mpr hPcomm
  have hPcard : Nat.card P ≠ 1 :=
    (P.one_lt_card_iff_ne_bot.mpr hPne).ne'
  have hTopp : IsPGroup p (⊤ : Subgroup P) := hPp.to_subgroup ⊤
  have hTopcard : Nat.card (⊤ : Subgroup P) ≠ 1 := by
    simpa using hPcard
  calc
    Nat.card (omegaOneCenterAmbient p P) =
        Nat.card (Submission.OddOrder.BG.Section05.omegaOneCenter p P) :=
      Subgroup.card_map_of_injective P.subtype_injective
    _ = Nat.card (omegaOne p (Subgroup.center P)) :=
      Subgroup.card_map_of_injective
        (Subgroup.center P).subtype_injective
    _ = Nat.card (omegaOne p (⊤ : Subgroup P)) := by rw [hcenter]
    _ = p := card_omegaOne_of_isCyclic_isPGroup
      (Fact.out : p.Prime) hTopp hTopcard

private theorem semiregular_card_dvd_sub_one15
    {K : Type*} [Group K] [Finite K]
    {A R : Subgroup K}
    (hreg : IsSemiregularConjugation A R)
    (hnorm : R ≤ Subgroup.normalizer (A : Set K)) :
    Nat.card R ∣ Nat.card A - 1 := by
  letI := subgroupConjugationAction A R hnorm
  have hfixed : ∀ r : R, r ≠ 1 → ∀ a : A, r • a = a → a = 1 := by
    intro r hr a ha
    apply hreg r hr a
    simpa only [coe_subgroupConjugationAction_smul A R hnorm] using
      congrArg Subtype.val ha
  let t := Nat.card
    (nonidentityFixedOneOrbitQuotient (G := R) (X := A))
  have hcard : Nat.card A = 1 + t * Nat.card R := by
    simpa [t] using natCard_eq_one_add_fixedOneOrbits_mul_natCard
      (G := R) (X := A) (fun r ↦ smul_one r) hfixed
  refine ⟨t, ?_⟩
  rw [hcard]
  simp [Nat.mul_comm]

/-- Centralizing each of two factors is equivalent to centralizing their
join. -/
private theorem le_centralizer_sup15
    {K : Type*} [Group K] {X A B : Subgroup K}
    (hA : X ≤ Subgroup.centralizer (A : Set K))
    (hB : X ≤ Subgroup.centralizer (B : Set K)) :
    X ≤ Subgroup.centralizer ((A ⊔ B : Subgroup K) : Set K) := by
  apply Subgroup.le_centralizer_iff.mpr
  exact sup_le
    (Subgroup.le_centralizer_iff.mp hA)
    (Subgroup.le_centralizer_iff.mp hB)

/-- Form the sum of two ambient elementary-abelian subgroups inside a
common ambient `p`-subgroup. -/
private theorem isElementaryAbelianOfRank_sup_of_le_pgroup15
    {p m n : ℕ} [Fact p.Prime] {P A B : Subgroup G}
    (hP : IsPGroup p P) (hAP : A ≤ P) (hBP : B ≤ P)
    (hA : IsElementaryAbelianOfRank p m A)
    (hB : IsElementaryAbelianOfRank p n B)
    (hdis : Disjoint A B)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, Commute a b) :
    IsElementaryAbelianOfRank p (m + n) (A ⊔ B) := by
  let AP : Subgroup P := A.subgroupOf P
  let BP : Subgroup P := B.subgroupOf P
  have hAPRank : IsElementaryAbelianOfRank p m AP :=
    hA.subgroupOf hAP
  have hBPRank : IsElementaryAbelianOfRank p n BP :=
    hB.subgroupOf hBP
  have hdisP : Disjoint AP BP := by
    rw [disjoint_iff]
    apply le_antisymm ?_ bot_le
    intro x hx
    apply Subtype.ext
    have hxBot : (x : G) ∈ (⊥ : Subgroup G) :=
      hdis.le_bot ⟨hx.1, hx.2⟩
    exact Subgroup.mem_bot.mp hxBot
  have hcommP : ∀ a ∈ AP, ∀ b ∈ BP, Commute a b := by
    intro a ha b hb
    apply Subtype.ext
    exact (hcomm (a : G) ha (b : G) hb).eq
  have hsupP : IsElementaryAbelianOfRank p (m + n) (AP ⊔ BP) :=
    isElementaryAbelianOfRank_sup_of_disjoint_of_commute
      hP hAPRank hBPRank hdisP hcommP
  have hmap : (AP ⊔ BP).map P.subtype = A ⊔ B := by
    rw [Subgroup.map_sup]
    simpa [AP, BP] using congrArg₂ (· ⊔ ·)
      (Subgroup.map_subgroupOf_eq_of_le hAP)
      (Subgroup.map_subgroupOf_eq_of_le hBP)
  rw [← hmap]
  exact hsupP.map_of_injective P.subtype P.subtype_injective

/-! ## The non-TI witness -/

private theorem exists_nonTI_fitting_intersection
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hnonTI : ¬ IsNormalizedTI
      (subgroupNonidentity (fittingWithin M)) ⊤ M) :
    ∃ g : G, g ∉ M ∧ nonTIFittingIntersection M g ≠ ⊥ := by
  classical
  by_contra hnone
  push_neg at hnone
  apply hnonTI
  refine ⟨?_, ?_, ?_⟩
  · have hne := (Fcore_structure hM).Fcore_ne_bot
    rw [Subgroup.ne_bot_iff_exists_ne_one] at hne
    obtain ⟨x, hx1⟩ := hne
    refine ⟨(x : G), Fcore_sub_Fitting M x.property, ?_⟩
    intro hx
    exact hx1 (Subtype.ext hx)
  · intro g hgM
    refine ⟨trivial, ?_⟩
    apply Subgroup.mem_set_normalizer_iff''.mpr
    intro x
    have hgNorm : g ∈ Subgroup.normalizer (fittingWithin M : Set G) :=
      fittingWithin_le_normalizer M hgM
    constructor
    · intro hx
      refine ⟨((Subgroup.mem_set_normalizer_iff''.mp hgNorm) x).1 hx.1, ?_⟩
      intro heq
      exact hx.2 (by
        simpa [mul_assoc] using congrArg (fun z ↦ g * z * g⁻¹) heq)
    · intro hxg
      refine ⟨((Subgroup.mem_set_normalizer_iff''.mp hgNorm) x).2 hxg.1, ?_⟩
      intro hx1
      subst x
      simpa using hxg.2
  · intro g _ hoverlap
    by_contra hgM
    have hginvM : g⁻¹ ∉ M := by
      intro hginv
      exact hgM (by simpa using M.inv_mem hginv)
    rcases hoverlap with ⟨_, hxA, a, haA, rfl⟩
    have hmeet : g⁻¹ * a * g ∈
        nonTIFittingIntersection M g⁻¹ := by
      refine ⟨hxA.1, ?_⟩
      rw [conjugateSubgroup15]
      exact ⟨a, haA.1, by simp⟩
    have hconjNe : g⁻¹ * a * g ≠ 1 := by
      intro heq
      apply haA.2
      simpa [mul_assoc] using congrArg (fun z ↦ g * z * g⁻¹) heq
    have hmeetNe : nonTIFittingIntersection M g⁻¹ ≠ ⊥ := by
      rw [Subgroup.ne_bot_iff_exists_ne_one]
      refine ⟨⟨g⁻¹ * a * g, hmeet⟩, ?_⟩
      intro heq
      exact hconjNe (congrArg Subtype.val heq)
    exact hmeetNe (hnone g⁻¹ hginvM)

set_option maxHeartbeats 4000000 in
theorem nonTI_Fitting_structure
    {M : Subgroup G} {g : G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hg : g ∉ M)
    (hX : nonTIFittingIntersection M g ≠ ⊥) :
    NonTIFittingStructure M g := by
  classical
  let X : Subgroup G := nonTIFittingIntersection M g
  let H : Subgroup G := Fitting_core M
  have hFcore := Fcore_structure hM
  have hFitting := Fitting_structure hM
  have hnilH : Group.IsNilpotent H := by
    simpa [H] using Fcore_nil M
  have hHM : H ≤ M := by
    simpa [H] using Fcore_sub M
  have hHnormal : (H.subgroupOf M).Normal := by
    simpa [H] using Fcore_normal M

  /- If a prime core of `M` meeting `X` were cyclic, its unique subgroup of
  order `p` would have normalizer `M`.  Conjugating the same line through
  the second factor of `X` would then force `g` into `M`. -/
  have hpcoreNoncyclic : ∀ {p : ℕ}, p.Prime →
      p ∈ primeSupport (Nat.card X) →
      ¬ IsCyclic (pCoreWithin p M) := by
    intro p hp hpX hcyc
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨x, hxOrder⟩ :=
      exists_prime_orderOf_dvd_card' (G := X) p hpX.2
    have hxX : (x : G) ∈ X := x.property
    have hxF : (x : G) ∈ fittingWithin M := hxX.1
    have hxFg : (x : G) ∈ conjugateSubgroup15 (fittingWithin M) g :=
      hxX.2
    have normalizer_line {y : G}
        (hyF : y ∈ fittingWithin M) (hyOrder : orderOf y = p) :
        Subgroup.normalizer (Subgroup.zpowers y : Set G) = M := by
      let L : Subgroup G := Subgroup.zpowers y
      have hyPelt : IsPElement p y := by
        refine ⟨1, ?_⟩
        simpa [hyOrder] using pow_orderOf_eq_one y
      have hLp : IsPGroup p L := by
        simpa [L] using hyPelt.zpowers_isPGroup
      have hLF : L ≤ fittingWithin M :=
        Subgroup.zpowers_le.mpr hyF
      have hLFp : IsPGroup p (L.subgroupOf (fittingWithin M)) :=
        hLp.of_equiv
          (Subgroup.subgroupOfEquivOfLe hLF).symm
      letI : Group.IsNilpotent (fittingWithin M) :=
        fittingWithin_isNilpotent M
      have hLcoreF : L.subgroupOf (fittingWithin M) ≤
          pCore p (fittingWithin M) :=
        hLFp.le_pCore_of_isNilpotent
      let Q : Subgroup G := pCoreWithin p M
      have hLQ : L ≤ Q := by
        change L ≤ (pCore p M).map M.subtype
        rw [← map_pCore_fittingWithin_eq_map_pCore M p,
          ← Subgroup.map_subgroupOf_eq_of_le hLF]
        exact Subgroup.map_mono hLcoreF
      let O : Subgroup G := (omegaOne p Q).map Q.subtype
      let yQ : Q := ⟨y, hLQ (Subgroup.mem_zpowers y)⟩
      have hyQpow : yQ ^ p = 1 := by
        apply Subtype.ext
        simpa [yQ, hyOrder] using pow_orderOf_eq_one y
      have hyO : y ∈ O :=
        ⟨yQ, mem_omegaOne_of_pow_eq_one p hyQpow, rfl⟩
      have hLO : L ≤ O := Subgroup.zpowers_le.mpr hyO
      have hQp : IsPGroup p Q := by
        change IsPGroup p ((pCore p M).map M.subtype)
        exact pCore_isPGroup.map M.subtype
      have hQne : Q ≠ ⊥ := by
        intro hQbot
        have hLbot : L = ⊥ := le_bot_iff.mp (hLQ.trans_eq hQbot)
        have hy1 : y ≠ 1 := by
          intro hy
          subst y
          simp at hyOrder
          exact hp.ne_one hyOrder.symm
        exact (Subgroup.zpowers_ne_bot.mpr hy1) hLbot
      letI : IsCyclic Q := by simpa [Q] using hcyc
      have hcardO : Nat.card O = p := by
        change Nat.card ((omegaOne p Q).map Q.subtype) = p
        rw [Subgroup.card_map_of_injective Q.subtype_injective]
        exact card_omegaOne_of_isCyclic_isPGroup hp hQp
          ((Q.one_lt_card_iff_ne_bot.mpr hQne).ne')
      have hcardL : Nat.card L = p := by
        simp [L, Nat.card_zpowers, hyOrder]
      have hLOeq : L = O :=
        Subgroup.eq_of_le_of_card_ge hLO (by rw [hcardL, hcardO])
      have hQM : Q ≤ M := by
        simpa [Q, pCoreWithin] using
          (Subgroup.map_subtype_le (pCore p M))
      have hMnormQ : M ≤ Subgroup.normalizer (Q : Set G) := by
        simpa [Q, pCoreWithin] using
          (Subgroup.le_normalizer :
            M ≤ Subgroup.normalizer (M : Set G)).trans
              (characteristic_map_subtype_le_normalizer15
                M (pCore p M))
      have hMnormO : M ≤ Subgroup.normalizer (O : Set G) := by
        simpa [O] using hMnormQ.trans
          (characteristic_map_subtype_le_normalizer15
            Q (omegaOne p Q))
      have hOM : O ≤ M := (Subgroup.map_subtype_le _).trans hQM
      have hOnormal : (O.subgroupOf M).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hOM).mpr hMnormO
      have hLnormal : (L.subgroupOf M).Normal := by
        simpa [hLOeq] using hOnormal
      have hLne : L ≠ ⊥ := by
        rw [hLOeq]
        intro hObot
        have hcardObot : Nat.card O = 1 := by rw [hObot]; simp
        exact hp.ne_one (hcardO.symm.trans hcardObot)
      exact mmax_normal hM (hLF.trans (fittingWithin_le M))
        hLnormal hLne
    have hnormLine :
        Subgroup.normalizer (Subgroup.zpowers (x : G) : Set G) = M :=
      normalizer_line hxF (by simpa using hxOrder)
    let e : G ≃* G := MulAut.conj g
    have hxPreF : e.symm (x : G) ∈ fittingWithin M := by
      change (x : G) ∈
          (fittingWithin M).map e.toMonoidHom at hxFg
      rcases hxFg with ⟨y, hyF, hyx⟩
      rw [← hyx]
      change e.symm (e y) ∈ fittingWithin M
      simpa using hyF
    have hxPreOrder : orderOf (e.symm (x : G)) = p := by
      simpa using hxOrder
    have hnormConj :
        Subgroup.normalizer
            (Subgroup.zpowers (e.symm (x : G)) : Set G) = M :=
      normalizer_line hxPreF hxPreOrder
    have hlineMap :
        (Subgroup.zpowers (e.symm (x : G))).map e.toMonoidHom =
          Subgroup.zpowers (x : G) := by
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (e (e.symm (x : G))) =
        Subgroup.zpowers (x : G)
      rw [e.apply_symm_apply]
    have hMmap : M.map e.toMonoidHom = M := by
      calc
        M.map e.toMonoidHom =
            (Subgroup.normalizer
              (Subgroup.zpowers (e.symm (x : G)) : Set G)).map
                e.toMonoidHom := by rw [hnormConj]
        _ = Subgroup.normalizer
              ((Subgroup.zpowers (e.symm (x : G))).map
                e.toMonoidHom : Set G) :=
          Subgroup.map_normalizer_eq_of_bijective _ e.bijective
        _ = Subgroup.normalizer (Subgroup.zpowers (x : G) : Set G) := by
          rw [hlineMap]
        _ = M := hnormLine
    have hgNormM : g ∈ Subgroup.normalizer (M : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMmap
    rw [norm_mmax hM] at hgNormM
    exact hg hgNormM

  /- The direct-product description of `F(M)` makes every prime occurring
  in `X` a sigma prime: a nonsigma prime core would sit in the cyclic
  complementary factor, contradicting the preceding paragraph. -/
  have hXsigma : IsPiNumber (sigmaPrimes M) (Nat.card X) := by
    intro p hp hpX
    by_contra hpNotSigma
    letI : Fact p.Prime := ⟨hp⟩
    have hpCoreCyclic : IsCyclic (pCoreWithin p M) := by
      have hpCoreLe : pCoreWithin p M ≤
          fittingSigmaPrimeCore M := by
        have hIntrinsic : pCore p (fittingWithin M) ≤
            piCore (sigmaPrimes M)ᶜ (fittingWithin M) := by
          apply le_piCore (by infer_instance)
          exact pCore_isPGroup.isPiNumber_natCard hpNotSigma
        change (pCore p M).map M.subtype ≤
          (piCore (sigmaPrimes M)ᶜ (fittingWithin M)).map
            (fittingWithin M).subtype
        rw [← map_pCore_fittingWithin_eq_map_pCore M p]
        exact Subgroup.map_mono hIntrinsic
      letI : IsCyclic (fittingSigmaPrimeCore M) :=
        hFitting.sigmaPrimeCore_cyclic
      exact Subgroup.isCyclic_of_le hpCoreLe
    exact hpcoreNoncyclic hp ⟨hp, hpX⟩ hpCoreCyclic
  have hXM : X ≤ M :=
    (nonTIFittingIntersection_le_fitting M g).trans (fittingWithin_le M)
  have hXsigmaCore : X ≤ sigmaCore M := by
    let XM : Subgroup M := X.subgroupOf M
    have hXMpi : IsPiNumber (sigmaPrimes M) (Nat.card XM) := by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hXM]
      exact hXsigma
    have hle : XM ≤ (sigmaCore M).subgroupOf M :=
      subgroup_le_normal_isHall15
        (by simpa using sigmaCore_normal M) (Msigma_Hall hM) hXMpi
    intro x hx
    exact hle (show (⟨x, hXM hx⟩ : M) ∈ XM from hx)

  /- Choose a rank-one line in `X`.  Sigma transitivity shows that its
  centralizer in the normal-Sylow core is not uniquely maximal; the rank
  three uniqueness theorem and nonabelian uniqueness then force that
  centralizer to have rank at most two and to be abelian. -/
  let p := Nat.minFac (Nat.card X)
  have hpX : p ∈ primeSupport (Nat.card X) := by
    have hcardNe : Nat.card X ≠ 1 :=
      (X.one_lt_card_iff_ne_bot.mpr hX).ne'
    exact ⟨Nat.minFac_prime hcardNe, Nat.minFac_dvd (Nat.card X)⟩
  have hp : p.Prime := hpX.1
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨X₁, hX₁X, hX₁⟩ :=
    exists_rankOneLineIn_of_primeSupport15 hpX
  let C₁ : Subgroup G := centralizerWithin H X₁
  have hC₁ :
      C₁ ∉ minSimple_uniq_max_groups (G := G) ∧
        ¬ HasElementaryAbelianRankAtLeast p 3 C₁ ∧
        IsMulCommutative C₁ := by
    have hpSigma : p ∈ sigmaPrimes M := hXsigma hp hpX.2
    have hX₁p : IsPGroup p X₁ := hX₁.isPGroup
    have hX₁M : X₁ ≤ M := hX₁X.trans hXM
    have hX₁backM :
        X₁.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
      have hmapped := Subgroup.map_mono
        (hX₁X.trans (nonTIFittingIntersection_le_conjugate M g))
        (f := (MulAut.conj g⁻¹).toMonoidHom)
      rw [conjugateSubgroup15, map_conj_inv_map_conj15] at hmapped
      exact hmapped.trans (fittingWithin_le M)
    have hCentNotM :
        ¬ Subgroup.centralizer (X₁ : Set G) ≤ M := by
      intro hCentM
      obtain ⟨c, hcCent, m, hmM, hgmul⟩ :=
        (sigma_group_trans hM hpSigma hX₁p).1
          g hX₁M hX₁backM
      apply hg
      rw [hgmul]
      exact M.mul_mem (hCentM hcCent) hmM
    have hC₁M : C₁ ≤ M :=
      (centralizerWithin_le_left H X₁).trans hHM
    have hC₁Cent : C₁ ≤ Subgroup.centralizer (X₁ : Set G) :=
      inf_le_right
    have hCentProper : Subgroup.centralizer (X₁ : Set G) < ⊤ :=
      mFT_cent_proper X₁ hX₁.ne_bot
    have hC₁proper : C₁ < ⊤ :=
      lt_of_le_of_lt hC₁Cent hCentProper
    have hC₁nonuniq : C₁ ∉ minSimple_uniq_max_groups (G := G) := by
      intro huniq
      exact hCentNotM
        (sub_uniq_mmax (def_uniq_mmax huniq hM hC₁M)
          hC₁Cent hCentProper)
    have hC₁rank :
        ¬ HasElementaryAbelianRankAtLeast p 3 C₁ := by
      intro hRank
      exact hC₁nonuniq
        (rank3_Uniqueness hC₁proper ⟨p, hp, hRank⟩)
    have hC₁nil : Group.IsNilpotent C₁ :=
      isNilpotent_of_le15 hnilH (centralizerWithin_le_left H X₁)
    have hC₁comm : IsMulCommutative C₁ := by
      apply nilpotent_isMulCommutative_of_pCores15 hC₁nil
      intro r hr
      letI : Fact r.Prime := ⟨hr⟩
      by_contra hcoreNoncomm
      let P : Subgroup G := (pCore r C₁).map C₁.subtype
      have hPp : IsPGroup r P := by
        change IsPGroup r ((pCore r C₁).map C₁.subtype)
        exact pCore_isPGroup.map C₁.subtype
      have hPnoncomm : ¬ IsMulCommutative P := by
        intro hPcomm
        let eP : pCore r C₁ ≃* P :=
          (pCore r C₁).equivMapOfInjective C₁.subtype
            C₁.subtype_injective
        apply hcoreNoncomm
        apply isMulCommutative_iff.mpr
        intro a b
        apply eP.injective
        exact isMulCommutative_iff.mp hPcomm (eP a) (eP b)
      exact hC₁nonuniq
        (uniq_mmaxS (Subgroup.map_subtype_le _) hC₁proper
          (nonabelian_Uniqueness hPp hPnoncomm))
    exact ⟨hC₁nonuniq, hC₁rank, hC₁comm⟩
  have hC₁Cent : C₁ ≤ Subgroup.centralizer (X₁ : Set G) :=
    inf_le_right
  have hC₁proper : C₁ < ⊤ :=
    lt_of_le_of_lt hC₁Cent (mFT_cent_proper X₁ hX₁.ne_bot)
  have hC₁rankAll : ∀ r : ℕ, r.Prime →
      ¬ HasElementaryAbelianRankAtLeast r 3 C₁ := by
    intro r hr hRank
    exact hC₁.1
      (rank3_Uniqueness hC₁proper ⟨r, hr, hRank⟩)

  /- The same argument works for every prime-order line in `X`; retaining
  it parametrically avoids repeating the transitivity and uniqueness
  calculation in the nonabelian final case. -/
  have lineCentralizerComm : ∀ {q : ℕ}, q.Prime →
      q ∈ primeSupport (Nat.card X) →
      ∀ {Y : Subgroup G}, Y ≤ X →
        IsElementaryAbelianOfRank q 1 Y →
        IsMulCommutative (centralizerWithin H Y) := by
    intro q hq hqX Y hYX hY
    letI : Fact q.Prime := ⟨hq⟩
    let C : Subgroup G := centralizerWithin H Y
    have hqSigma : q ∈ sigmaPrimes M := hXsigma hq hqX.2
    have hYM : Y ≤ M := hYX.trans hXM
    have hYbackM :
        Y.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
      have hmapped := Subgroup.map_mono
        (hYX.trans (nonTIFittingIntersection_le_conjugate M g))
        (f := (MulAut.conj g⁻¹).toMonoidHom)
      rw [conjugateSubgroup15, map_conj_inv_map_conj15] at hmapped
      exact hmapped.trans (fittingWithin_le M)
    have hCentNotM :
        ¬ Subgroup.centralizer (Y : Set G) ≤ M := by
      intro hCentM
      obtain ⟨c, hc, m, hm, hgcm⟩ :=
        (sigma_group_trans hM hqSigma hY.isPGroup).1
          g hYM hYbackM
      apply hg
      rw [hgcm]
      exact M.mul_mem (hCentM hc) hm
    have hCM : C ≤ M :=
      (centralizerWithin_le_left H Y).trans hHM
    have hCCent : C ≤ Subgroup.centralizer (Y : Set G) := inf_le_right
    have hCentProper : Subgroup.centralizer (Y : Set G) < ⊤ :=
      mFT_cent_proper Y hY.ne_bot
    have hCproper : C < ⊤ := lt_of_le_of_lt hCCent hCentProper
    have hCnonuniq : C ∉ minSimple_uniq_max_groups (G := G) := by
      intro huniq
      exact hCentNotM
        (sub_uniq_mmax (def_uniq_mmax huniq hM hCM)
          hCCent hCentProper)
    have hCnil : Group.IsNilpotent C :=
      isNilpotent_of_le15 hnilH (centralizerWithin_le_left H Y)
    apply nilpotent_isMulCommutative_of_pCores15 hCnil
    intro r hr
    letI : Fact r.Prime := ⟨hr⟩
    by_contra hcoreNoncomm
    let R : Subgroup G := (pCore r C).map C.subtype
    have hRr : IsPGroup r R := by
      change IsPGroup r ((pCore r C).map C.subtype)
      exact pCore_isPGroup.map C.subtype
    have hRnoncomm : ¬ IsMulCommutative R := by
      intro hRcomm
      let eR : pCore r C ≃* R :=
        (pCore r C).equivMapOfInjective C.subtype
          C.subtype_injective
      apply hcoreNoncomm
      apply isMulCommutative_iff.mpr
      intro a b
      apply eR.injective
      exact isMulCommutative_iff.mp hRcomm (eR a) (eR b)
    exact hCnonuniq
      (uniq_mmaxS (Subgroup.map_subtype_le _) hCproper
        (nonabelian_Uniqueness hRr hRnoncomm))

  /- Embed `X` in the sigma-core/conjugate-maximal intersection from
  Lemma 12.17.  Its cyclicity descends to `X`, and the same containment
  shows that the chosen prime is outside `beta(M)`. -/
  obtain ⟨E, hEM, hHallE⟩ := ex_sigma_compl hM
  have hEmbed := sigma_compl_embedding hM hEM hHallE
  let T : Subgroup G := sigmaCore M ⊓
    M.map (MulAut.conj g).toMonoidHom
  have hXT : X ≤ T := by
    apply le_inf hXsigmaCore
    exact (nonTIFittingIntersection_le_conjugate M g).trans (by
      simpa [conjugateSubgroup15] using
        Subgroup.map_mono (fittingWithin_le M)
          (f := (MulAut.conj g).toMonoidHom))
  have hTstructure := hEmbed.2.2 g hg
  have hXcyclic : IsCyclic X := by
    letI : IsCyclic T := by simpa [T] using hTstructure.1
    exact Subgroup.isCyclic_of_le hXT
  have hpBetaCompl : p ∉ betaPrimes M := by
    have hTbeta : IsPiNumber (betaPrimes M)ᶜ (Nat.card T) := by
      simpa [T] using hTstructure.2.1
    exact hTbeta hp
      (hpX.2.trans (Subgroup.card_dvd_of_le hXT))

  /- Every prime of the F-core is beta-complementary.  A different prime
  yields a normal Sylow subgroup centralizing `X₁`; beta rank three would
  then contradict the rank bound on `C₁`. -/
  have hHbetaCompl :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card H) := by
    intro r hr hrH
    change r ∉ betaPrimes M
    intro hrBeta
    by_cases hrp : r = p
    · exact hpBetaCompl (hrp ▸ hrBeta)
    letI : Fact r.Prime := ⟨hr⟩
    let R : Subgroup G := pCoreWithin r M
    have hrFcore : r ∈ primeSupport (Nat.card (Fitting_core M)) := by
      simpa [H] using ⟨hr, hrH⟩
    have hRsyl : IsSylowSubgroupOf r R M := by
      simpa [R, pCoreWithin] using Fcore_pcore_Sylow M hrFcore
    have hRH : R ≤ H := by
      simpa [H] using normal_sylow_le_Fcore hRsyl
        (by simpa [R] using pCoreWithin_normal15 r M)
    have hRF : R ≤ fittingWithin M := by
      change (pCore r M).map M.subtype ≤
        (fittingCore M).map M.subtype
      exact Subgroup.map_mono (pCore_le_fittingCore r)
    have hX₁F : X₁ ≤ fittingWithin M :=
      hX₁X.trans (nonTIFittingIntersection_le_fitting M g)
    have hRr : IsPGroup r R := by
      change IsPGroup r ((pCore r M).map M.subtype)
      exact pCore_isPGroup.map M.subtype
    have hRCent : R ≤ Subgroup.centralizer (X₁ : Set G) :=
      pSubgroups_centralize_of_nilpotent15
        hrp hRr hX₁.isPGroup hRF hX₁F
          (fittingWithin_isNilpotent M)
    have hRC₁ : R ≤ C₁ := le_inf hRH hRCent
    have hRankM : HasElementaryAbelianRankAtLeast r 3 M :=
      (beta_sub_alpha M hrBeta).2
    obtain ⟨A, hAR, hA⟩ :=
      exists_elementaryAbelian_le_ambientSylow15 hRsyl hRankM
    exact hC₁rankAll r hr ⟨A, hAR.trans hRC₁, hA⟩

  /- Proposition 14.2 leaves only F and P1: in the P2 branch sigma and
  beta coincide, contradicting the prime just shown beta-complementary. -/
  have htype :
      M ∈ typeFMaximalSubgroups (G := G) ∨
        M ∈ typeP1MaximalSubgroups (G := G) := by
    by_cases hF : M ∈ typeFMaximalSubgroups (G := G)
    · exact Or.inl hF
    right
    have hP : M ∈ typePMaximalSubgroups (G := G) := ⟨hM, hF⟩
    by_cases hP1 : M ∈ typeP1MaximalSubgroups (G := G)
    · exact hP1
    have hP2 : M ∈ typeP2MaximalSubgroups (G := G) := ⟨hP, hP1⟩
    obtain ⟨K, hKM, hHallK⟩ :=
      Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
        (mmax_sol hM) (kappaPrimes M)
    have hTwo := (Ptype_structure hP hKM hHallK).typeP2 hP2
    have hpSigma : p ∈ sigmaPrimes M := hXsigma hp hpX.2
    exact (hpBetaCompl (hTwo.sigma_eq_beta ▸ hpSigma)).elim

  /- The beta-complementary support also kills the nonnilpotent alternative
  of Theorem 15.2, hence the F-core is exactly the sigma core. -/
  have hHsigma : H = sigmaCore M := by
    by_contra hne
    obtain ⟨K, hKM, hHallK⟩ :=
      Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
        (mmax_sol hM) (kappaPrimes M)
    let q := Nat.card (kappaCentralizer M K)
    obtain ⟨D, hDle, hHallD⟩ :=
      Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
        (isSolvable_of_le15 (mmax_sol hM) (sigmaCore_le M))
        ({q} : Set ℕ)ᶜ
    have hs := hFcore.nonnilpotent hKM hHallK hne hDle hHallD
    have hqH : Nat.card (kappaCentralizer M K) ∣ Nat.card H := by
      simpa [H] using hs.partner_prime_in_Fcore.2
    exact (hHbetaCompl hs.card_partner_prime hqH)
      hs.partner_prime_beta
  have hXH : X ≤ H := by
    simpa [hHsigma] using hXsigmaCore

  /- Since the beta core lies inside the beta-complementary F-core, it is
  trivial.  Lemma 10.8(b) therefore makes the derived subgroup nilpotent,
  hence it lies in `F(M)`. -/
  have hderivedFitting : derivedWithin M ≤ fittingWithin M := by
    have hBetaH : betaCore M ≤ H := by
      rw [hHsigma]
      exact betaCore_le_sigmaCore hM
    have hcop : Nat.Coprime (Nat.card (betaCore M)) (Nat.card H) :=
      (betaCore_isPiNumber M).coprime_compl hHbetaCompl
    have hBetaCard : Nat.card (betaCore M) = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
        (Subgroup.card_dvd_of_le hBetaH)
    have hBetaBot : betaCore M = ⊥ :=
      Subgroup.card_eq_one.mp hBetaCard
    let D : Subgroup M := _root_.commutator M
    let B₀ : Subgroup M := (betaCore M).subgroupOf M
    have hB₀bot : B₀ = ⊥ := by
      simp [B₀, hBetaBot]
    have hdenBot : B₀.subgroupOf D = ⊥ := by
      simpa only [hB₀bot] using Subgroup.bot_subgroupOf D
    have hDquot : Group.IsNilpotent (D ⧸ (⊥ : Subgroup D)) := by
      have hraw := Mbeta_quo_nil hM
      change Group.IsNilpotent (D ⧸ B₀.subgroupOf D) at hraw
      letI : Group.IsNilpotent (D ⧸ B₀.subgroupOf D) := hraw
      exact Group.nilpotent_of_mulEquiv
        (QuotientGroup.quotientMulEquivOfEq hdenBot)
    letI : Group.IsNilpotent (D ⧸ (⊥ : Subgroup D)) := hDquot
    have hDnil : Group.IsNilpotent D :=
      Group.nilpotent_of_mulEquiv
        (QuotientGroup.quotientBot (G := D))
    have hDfit : D ≤ fittingCore M :=
      nilpotent_normal_le_fittingCore (by infer_instance) hDnil
    exact Subgroup.map_mono hDfit
  have hnilSigma : Group.IsNilpotent (sigmaCore M) := by
    rw [← hHsigma]
    exact hnilH
  have hFitSigmaEq : fittingWithin (sigmaCore M) = sigmaCore M := by
    apply le_antisymm (fittingWithin_le (sigmaCore M))
    letI : Group.IsNilpotent (sigmaCore M) := hnilSigma
    have htopNil : Group.IsNilpotent
        (⊤ : Subgroup (sigmaCore M)) :=
      Group.nilpotent_of_mulEquiv Subgroup.topEquiv.symm
    have htopFit : (⊤ : Subgroup (sigmaCore M)) ≤
        fittingCore (sigmaCore M) :=
      nilpotent_normal_le_fittingCore (by infer_instance) htopNil
    intro x hx
    exact ⟨⟨x, hx⟩, htopFit trivial, rfl⟩
  have hfitDecomp :
      IsInternalDirectProductIn (sigmaCore M)
        (fittingSigmaComplement M) (fittingWithin M) := by
    rw [← hFitSigmaEq]
    simpa [fittingSigmaComplement] using
      hFitting.sigmaFitting_times_sigmaPrimeCore

  /- In any sigma complement, the tau3 factor lies simultaneously in the
  derived subgroup and in `F(M)`, whose support is sigma ∪ tau2.  Coprime
  cardinality makes that factor trivial.  The remaining semidirect product
  identifies the quotient by `E₂` with the cyclic `E₁`. -/
  have hCompl : ∀ {E E₁ E₂ E₃ : Subgroup G},
      sigma_complement M E E₁ E₂ E₃ →
        NonTISigmaComplementStructure E E₁ E₂ E₃ := by
    intro E E₁ E₂ E₃ hSigma
    have hctx := sigma_compl_context hM hSigma
    have hE₃bot : E₃ = ⊥ := by
      have hcommEM :
          (_root_.commutator E).map E.subtype ≤ derivedWithin M := by
        rw [E.map_subtype_commutator]
        change ⁅E, E⁆ ≤ (_root_.commutator M).map M.subtype
        rw [M.map_subtype_commutator]
        exact Subgroup.commutator_mono hSigma.E_le_M hSigma.E_le_M
      have hE₃F : E₃ ≤ fittingWithin M :=
        hctx.E₃_le_commutator.trans
          (hcommEM.trans hderivedFitting)
      have hE₃tau3 : IsPiNumber (tau3Primes M) (Nat.card E₃) := by
        simpa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          hSigma.E₃_le_E] using hSigma.hall_E₃.isPiNumber_card
      let rho : Set ℕ := sigmaPrimes M ∪ tau2Primes M
      have hFitSigmaTau2 :
          IsPiNumber rho (Nat.card (fittingWithin M)) := by
        have hleft : IsPiNumber rho
            (Nat.card (fittingWithin (sigmaCore M))) :=
          ((sigmaCore_isPiNumber M).of_dvd
            (Subgroup.card_dvd_of_le
              (fittingWithin_le (sigmaCore M)))).mono
                Set.subset_union_left
        have hright : IsPiNumber rho
            (Nat.card (fittingSigmaPrimeCore M)) :=
          hFitting.sigmaPrimeCore_tau2.mono Set.subset_union_right
        have hcard :
            Nat.card (fittingWithin (sigmaCore M)) *
                Nat.card (fittingSigmaPrimeCore M) =
              Nat.card (fittingWithin M) := by
          rw [hFitSigmaEq]
          simpa only [
            Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
              hfitDecomp.left_le,
            Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
              hfitDecomp.right_le] using
                hfitDecomp.complement.card_mul
        rw [← hcard]
        exact IsPiNumber.mul hleft hright
      have hFitTau3Compl :
          IsPiNumber (tau3Primes M)ᶜ (Nat.card (fittingWithin M)) :=
        hFitSigmaTau2.mono (by
          intro r hrho hrTau3
          rcases hrho with hrSigma | hrTau2
          · exact hrTau3.2.1 hrSigma
          · exact (tau3'2 M hrTau2) hrTau3)
      have hcop : Nat.Coprime (Nat.card E₃)
          (Nat.card (fittingWithin M)) :=
        hE₃tau3.coprime_compl hFitTau3Compl
      have hcardE₃ : Nat.card E₃ = 1 :=
        Nat.eq_one_of_dvd_coprimes hcop dvd_rfl
          (Subgroup.card_dvd_of_le hE₃F)
      exact Subgroup.card_eq_one.mp hcardE₃
    have hE₂normal : (E₂.subgroupOf E).Normal := by
      simpa [hE₃bot] using hctx.E₃₂_E₁_sdprod.2.2.1
    have hequiv :
        letI := hE₂normal
        (E ⧸ E₂.subgroupOf E) ≃* E₁ := by
      letI := hE₂normal
      have hcomp :
          (E₂.subgroupOf E).IsComplement' (E₁.subgroupOf E) := by
        simpa [hE₃bot] using hctx.E₃₂_E₁_sdprod.2.2.2
      exact hcomp.symm.QuotientMulEquiv.trans
        (Subgroup.subgroupOfEquivOfLe hSigma.E₁_le_E)
    exact ⟨
      { E₃_eq_bot := hE₃bot
        E₂_normal := hE₂normal
        quotient_equiv := hequiv
        quotient_cyclic :=
          quotient_cyclic_of_equiv15 hE₂normal hequiv hctx.E₁_cyclic }
    ⟩

  /- In the abelian branch, the P1 alternative contradicts the cyclicity
  restriction on its F-core.  The line-centralizer bound gives rank at most
  two, while noncyclicity of the relevant prime core supplies rank two. -/
  have hfinal :
      NonTIFittingAbelianCase M ∨ NonTIFittingNonabelianCase M g := by
    by_cases hHab : IsMulCommutative H
    · left
      have htypeF : M ∈ typeFMaximalSubgroups (G := G) := by
        rcases htype with hF | hP1
        · exact hF
        · obtain ⟨K, hKM, hHallK⟩ :=
            Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
              (mmax_sol hM) (kappaPrimes M)
          have hKne : K ≠ ⊥ := by
            intro hK
            exact hP1.1.2 ((trivg_kappa hM hKM hHallK).1 hK)
          obtain ⟨U, hKappaCompl⟩ :=
            ex_kappa_compl hM hKM hHallK
          have hUbot : U = ⊥ :=
            (trivg_kappa_compl hM hKappaCompl).2 hP1
          have hkappa := kappa_structure hM hKappaCompl
          have hSigmaDerived : sigmaCore M = derivedWithin M := by
            have hdecomp := hkappa.derived_decomposition hKne
            have htop := hdecomp.2.2.2.sup_eq_top
            have hSigmaTop :
                (sigmaCore M).subgroupOf (derivedWithin M) = ⊤ := by
              simpa [hUbot] using htop
            exact le_antisymm hdecomp.1
              (Subgroup.subgroupOf_eq_top.mp hSigmaTop)
          have hDerivedComm :
              IsMulCommutative (derivedWithin M) := by
            rw [← hSigmaDerived, ← hHsigma]
            exact hHab
          letI : IsMulCommutative (derivedWithin M) := hDerivedComm
          have hSecondBot : secondDerivedWithin M = ⊥ := by
            rw [secondDerivedWithin, derivedWithin,
              _root_.commutator_eq_bot, Subgroup.map_bot]
          have hcyclics := Ptype_cyclics hP1.1 hKM hHallK
          exact (hcyclics.partner_ne_bot
            (le_bot_iff.mp
              (hcyclics.partner_le_secondDerived.trans_eq hSecondBot))).elim
      have hX₁H : X₁ ≤ H := hX₁X.trans hXH
      have hHC : H ≤ Subgroup.centralizer (X₁ : Set G) := by
        intro a ha
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact congrArg Subtype.val
          (isMulCommutative_iff.mp hHab
            ⟨x, hX₁H hx⟩ ⟨a, ha⟩)
      have hC₁eqH : C₁ = H := by
        apply le_antisymm (centralizerWithin_le_left H X₁)
        exact le_inf le_rfl hHC
      have hRankAtMost : ∀ r : ℕ, r.Prime →
          ¬ HasElementaryAbelianRankAtLeast r 3 H := by
        intro r hr hRank
        exact hC₁rankAll r hr (hC₁eqH.symm ▸ hRank)
      have hRankTwo :
          ∃ r : ℕ, r.Prime ∧
            HasElementaryAbelianRankAtLeast r 2 H := by
        let P : Subgroup G := pCoreWithin p M
        have hPnoncyc : ¬ IsCyclic P := hpcoreNoncyclic hp hpX
        have hPp : IsPGroup p P := by
          change IsPGroup p ((pCore p M).map M.subtype)
          exact pCore_isPGroup.map M.subtype
        have hPline : ∃ A : Subgroup P,
            IsElementaryAbelianOfRank p 2 A := by
          by_contra hno
          apply hPnoncyc
          exact (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
            hPp (mFT_odd P)).2 hno
        obtain ⟨A, hA⟩ := hPline
        let AG : Subgroup G := A.map P.subtype
        have hPH : P ≤ H := by
          have hPsyl : IsSylowSubgroupOf p
              ((pCore p M).map M.subtype) M :=
            Fcore_pcore_Sylow M
              (show p ∈ primeSupport (Nat.card (Fitting_core M)) from by
                simpa [H] using ⟨hp, hpX.2.trans
                  (Subgroup.card_dvd_of_le hXH)⟩)
          simpa [H, P, pCoreWithin] using normal_sylow_le_Fcore hPsyl
            (by simpa [pCoreWithin] using pCoreWithin_normal15 p M)
        refine ⟨p, hp, AG, ?_, ?_⟩
        · exact (Subgroup.map_subtype_le A).trans hPH
        · exact hA.map_of_injective P.subtype P.subtype_injective
      exact
        { typeF := htypeF
          core_abelian := by simpa [H] using hHab
          rank_two := by simpa [H] using hRankTwo
          rank_at_most_two := by simpa [H] using hRankAtMost }
    · right
      have hPnonab :
          ¬ IsMulCommutative (pCore p H) := by
        intro hPcomm
        let P : Subgroup G := (pCore p H).map H.subtype
        let K : Subgroup G := (pPrimeCore p H).map H.subtype
        have hX₁H : X₁ ≤ H := hX₁X.trans hXH
        have hX₁Hp : IsPGroup p (X₁.subgroupOf H) :=
          hX₁.isPGroup.of_equiv
            (Subgroup.subgroupOfEquivOfLe hX₁H).symm
        letI : Group.IsNilpotent H := hnilH
        have hX₁core : X₁.subgroupOf H ≤ pCore p H :=
          hX₁Hp.le_pCore_of_isNilpotent
        have hX₁P : X₁ ≤ P := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hX₁H]
          exact Subgroup.map_mono hX₁core
        have hKC : K ≤ Subgroup.centralizer (X₁ : Set G) := by
          intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          rcases hk with ⟨kH, hkCore, rfl⟩
          have hxP : x ∈ P := hX₁P hx
          rcases hxP with ⟨xH, hxCore, hxval⟩
          have hcent := Subgroup.mem_centralizer_iff.mp
            ((pCore_le_centralizer_pPrimeCore (G := H) p) hxCore)
              kH hkCore
          exact hxval ▸ (congrArg Subtype.val hcent).symm
        have hKH : K ≤ H := Subgroup.map_subtype_le _
        have hKC₁ : K ≤ C₁ := le_inf hKH hKC
        have hKcomm : IsMulCommutative K :=
          isMulCommutative_of_le15 hC₁.2.2 hKC₁
        have hPrimeCoreComm :
            IsMulCommutative (pPrimeCore p H) := by
          let eK : pPrimeCore p H ≃* K :=
            (pPrimeCore p H).equivMapOfInjective H.subtype
              H.subtype_injective
          apply isMulCommutative_iff.mpr
          intro a b
          apply eK.injective
          exact isMulCommutative_iff.mp hKcomm (eK a) (eK b)
        apply hHab
        apply nilpotent_isMulCommutative_of_pCores15 hnilH
        intro q hq
        by_cases hqp : q = p
        · subst q
          exact hPcomm
        letI : Fact q.Prime := ⟨hq⟩
        exact isMulCommutative_of_le15 hPrimeCoreComm
          (pCore_le_pPrimeCore_of_ne (G := H) (p := p)
            (q := q) (fun hpq ↦ hqp hpq.symm))
      have hXp : IsPGroup p X := by
        apply IsPGroup.of_card
        apply Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
        intro q hq hqXcard
        have hqX : q ∈ primeSupport (Nat.card X) := ⟨hq, hqXcard⟩
        by_contra hqp
        letI : Fact q.Prime := ⟨hq⟩
        obtain ⟨Y, hYX, hY⟩ :=
          exists_rankOneLineIn_of_primeSupport15 hqX
        let C : Subgroup G := centralizerWithin H Y
        have hCcomm : IsMulCommutative C :=
          lineCentralizerComm hq hqX hYX hY
        let P : Subgroup G := (pCore p H).map H.subtype
        have hPp : IsPGroup p P := by
          change IsPGroup p ((pCore p H).map H.subtype)
          exact pCore_isPGroup.map H.subtype
        have hPH : P ≤ H := Subgroup.map_subtype_le _
        have hPnoncomm : ¬ IsMulCommutative P := by
          intro hPcomm
          let eP : pCore p H ≃* P :=
            (pCore p H).equivMapOfInjective H.subtype
              H.subtype_injective
          apply hPnonab
          apply isMulCommutative_iff.mpr
          intro a b
          apply eP.injective
          exact isMulCommutative_iff.mp hPcomm (eP a) (eP b)
        have hYH : Y ≤ H := hYX.trans hXH
        have hPYcent : P ≤ Subgroup.centralizer (Y : Set G) :=
          pSubgroups_centralize_of_nilpotent15
            (fun hpq ↦ hqp hpq.symm) hPp hY.isPGroup
              hPH hYH hnilH
        have hPC : P ≤ C := le_inf hPH hPYcent
        have hPcommAmbient : IsMulCommutative P :=
          isMulCommutative_of_le15 hCcomm hPC
        apply hPnonab
        let eP : pCore p H ≃* P :=
          (pCore p H).equivMapOfInjective H.subtype
            H.subtype_injective
        apply isMulCommutative_iff.mpr
        intro a b
        apply eP.injective
        exact isMulCommutative_iff.mp hPcommAmbient (eP a) (eP b)
      have hXeq_center :
          Nat.card X = p ∧
            IsElementaryAbelianOfRank p 1
              (omegaOneCenterAmbient p
                ((pCore p H).map H.subtype)) ∧
            ∃ B : Subgroup G,
              X₁ ≤ B ∧
              B ≤ (pCore p H).map H.subtype ∧
              IsElementaryAbelianOfRank p 2 B ∧
              IsPMaxElem p (⊤ : Subgroup G) B ∧
              IsSylowSubgroupOf p ((pCore p H).map H.subtype)
                (⊤ : Subgroup G) ∧
              ¬ X₁ ≤ omegaOneCenterAmbient p
                ((pCore p H).map H.subtype) := by
        let P : Subgroup G := (pCore p H).map H.subtype
        have hPp : IsPGroup p P := by
          change IsPGroup p ((pCore p H).map H.subtype)
          exact pCore_isPGroup.map H.subtype
        have hPnoncomm : ¬ IsMulCommutative P := by
          intro hPcomm
          let eP : pCore p H ≃* P :=
            (pCore p H).equivMapOfInjective H.subtype
              H.subtype_injective
          apply hPnonab
          apply isMulCommutative_iff.mpr
          intro a b
          apply eP.injective
          exact isMulCommutative_iff.mp hPcomm (eP a) (eP b)
        have hPH : P ≤ H := Subgroup.map_subtype_le _
        have hX₁H : X₁ ≤ H := hX₁X.trans hXH
        letI : Group.IsNilpotent H := hnilH
        have hX₁core : X₁.subgroupOf H ≤ pCore p H :=
          (hX₁.isPGroup.of_equiv
            (Subgroup.subgroupOfEquivOfLe hX₁H).symm).le_pCore_of_isNilpotent
        have hX₁P : X₁ ≤ P := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hX₁H]
          exact Subgroup.map_mono hX₁core
        have hXcore : X.subgroupOf H ≤ pCore p H :=
          (hXp.of_equiv
            (Subgroup.subgroupOfEquivOfLe hXH).symm).le_pCore_of_isNilpotent
        have hXP : X ≤ P := by
          rw [← Subgroup.map_subgroupOf_eq_of_le hXH]
          exact Subgroup.map_mono hXcore
        let Z₀ : Subgroup G := omegaOneCenterAmbient p P
        have hPne : P ≠ ⊥ := by
          intro hPbot
          apply hX₁.ne_bot
          apply le_antisymm
          · exact hX₁P.trans (le_of_eq hPbot)
          · exact bot_le
        have hZ₀ne : Z₀ ≠ ⊥ := by
          simpa [Z₀] using omegaOneCenterAmbient_ne_bot15 hPp hPne
        have hZ₀P : Z₀ ≤ P :=
          (omegaOneCenterAmbient_le_centerWithin p P).trans
            (centralizerWithin_le_left P P)
        have hZ₀p : IsPGroup p Z₀ := hPp.to_le hZ₀P
        have hpZ₀ : p ∣ Nat.card Z₀ :=
          hZ₀p.card_eq_or_dvd.resolve_left
            (fun hcard ↦ hZ₀ne (Subgroup.card_eq_one.mp hcard))
        obtain ⟨Z₁, hZ₁Z₀, hZ₁⟩ :=
          exists_rankOneLineIn_of_primeSupport15
            (show p ∈ primeSupport (Nat.card Z₀) from ⟨hp, hpZ₀⟩)
        have hX₁notZ₀ : ¬ X₁ ≤ Z₀ := by
          intro hX₁Z₀
          have hPCent : P ≤ Subgroup.centralizer (X₁ : Set G) := by
            intro a ha
            rw [Subgroup.mem_centralizer_iff]
            intro x hx
            exact ((omegaOneCenterAmbient_le_centerWithin p P
              (hX₁Z₀ hx)).2 a ha).symm
          have hPC₁ : P ≤ C₁ := le_inf hPH hPCent
          have hPcomm : IsMulCommutative P :=
            isMulCommutative_of_le15 hC₁.2.2 hPC₁
          exact hPnoncomm hPcomm
        have hX₁neZ₁ : X₁ ≠ Z₁ := by
          intro hEq
          apply hX₁notZ₀
          simpa [hEq] using hZ₁Z₀
        have hX₁card : Nat.card X₁ = p := by
          simpa using hX₁.card_eq
        have hZ₁card : Nat.card Z₁ = p := by
          simpa using hZ₁.card_eq
        have hdisX₁Z₁ : Disjoint X₁ Z₁ :=
          disjoint_of_card_eq_prime_of_ne15 hp hX₁card
            hZ₁card hX₁neZ₁
        have hX₁Z₁comm : ∀ x ∈ X₁, ∀ z ∈ Z₁, Commute x z := by
          intro x hx z hz
          exact ((omegaOneCenterAmbient_le_centerWithin p P
            (hZ₁Z₀ hz)).2 x (hX₁P hx))
        let B : Subgroup G := X₁ ⊔ Z₁
        have hBP : B ≤ P := sup_le hX₁P (hZ₁Z₀.trans hZ₀P)
        have hB : IsElementaryAbelianOfRank p 2 B := by
          simpa [B] using
            isElementaryAbelianOfRank_sup_of_le_pgroup15
              hPp hX₁P (hZ₁Z₀.trans hZ₀P)
                hX₁ hZ₁ hdisX₁Z₁ hX₁Z₁comm
        have hPsylH : IsSylowSubgroupOf p P H := by
          let S : Sylow p H := Classical.choice Sylow.nonempty
          refine ⟨S, ?_⟩
          dsimp [P]
          rw [pCore_eq_sylow_of_isNilpotent S]
        have hPsylSigma : IsSylowSubgroupOf p P (sigmaCore M) := by
          simpa [hHsigma] using hPsylH
        have hPsigma : P ≤ sigmaCore M := by
          obtain ⟨S, hPS⟩ := hPsylSigma
          rw [hPS]
          exact Subgroup.map_subtype_le _
        have hpSigma : p ∈ sigmaPrimes M := hXsigma hp hpX.2
        have hPsylG : IsSylowSubgroupOf p P (⊤ : Subgroup G) :=
          sylow_of_sylow_hall15 hPsylSigma (Msigma_Hall_G hM) hpSigma
        have hBmax : IsPMaxElem p (⊤ : Subgroup G) B := by
          refine ⟨⟨le_top, hB.toIsElementaryAbelianGroup⟩, ?_⟩
          intro E hE hBE
          apply le_antisymm ?_ hBE
          by_contra hnot
          have hBElt : B < E :=
            lt_of_le_of_ne hBE (fun hEq ↦ hnot hEq.ge)
          obtain ⟨F, hFE, hF⟩ :=
            exists_rankThree_of_rankTwo_lt15 hB hE.2 hBElt
          let ET : Subgroup (⊤ : Subgroup G) := E.subgroupOf ⊤
          have hETp : IsPGroup p ET :=
            hE.2.isPGroup.of_equiv
              (Subgroup.subgroupOfEquivOfLe le_top).symm
          obtain ⟨R, hETR⟩ := hETp.exists_le_sylow
          obtain ⟨S, hPS⟩ := hPsylG
          obtain ⟨a, ha⟩ :=
            MulAction.exists_smul_eq (⊤ : Subgroup G) R S
          let aG : G := a
          let Ea : Subgroup G :=
            E.map (MulAut.conj aG).toMonoidHom
          have hRS : (R : Subgroup (⊤ : Subgroup G)).map
              (MulAut.conj a).toMonoidHom =
              (S : Subgroup (⊤ : Subgroup G)) := by
            change MulAut.conj a • (R : Subgroup (⊤ : Subgroup G)) =
              (S : Subgroup (⊤ : Subgroup G))
            rw [← Sylow.coe_subgroup_smul, ha]
          have hEaP : Ea ≤ P := by
            intro y hy
            rcases hy with ⟨x, hxE, rfl⟩
            let xT : (⊤ : Subgroup G) := ⟨x, trivial⟩
            have hxET : xT ∈ ET := hxE
            have hxR : xT ∈ (R : Subgroup (⊤ : Subgroup G)) :=
              hETR hxET
            have hxaS : (MulAut.conj a) xT ∈
                (S : Subgroup (⊤ : Subgroup G)) := by
              rw [← hRS]
              exact Subgroup.mem_map_of_mem
                (MulAut.conj a).toMonoidHom hxR
            have hxaMap : ((MulAut.conj a) xT : G) ∈
                (S : Subgroup (⊤ : Subgroup G)).map
                  (⊤ : Subgroup G).subtype :=
              Subgroup.mem_map_of_mem (⊤ : Subgroup G).subtype hxaS
            rw [← hPS] at hxaMap
            simpa [aG, xT, MulAut.conj_apply] using hxaMap
          have hX₁B : X₁ ≤ B := le_sup_left
          have hX₁cyclic : IsCyclic X₁ :=
            isCyclic_of_prime_card hX₁card
          obtain ⟨x₁S, hx₁genMem⟩ := hX₁cyclic.exists_generator
          let x₁ : G := x₁S
          have hx₁X₁ : x₁ ∈ X₁ := x₁S.property
          have hx₁gen : Subgroup.zpowers x₁ = X₁ := by
            apply le_antisymm (Subgroup.zpowers_le.mpr hx₁X₁)
            intro y hy
            have hyPow : (⟨y, hy⟩ : X₁) ∈
                Subgroup.zpowers x₁S := hx₁genMem ⟨y, hy⟩
            rw [Subgroup.mem_zpowers_iff] at hyPow ⊢
            rcases hyPow with ⟨n, hn⟩
            exact ⟨n, congrArg Subtype.val hn⟩
          have hx₁P : x₁ ∈ P := hX₁P hx₁X₁
          have hx₁aP : (MulAut.conj aG) x₁ ∈ P :=
            hEaP (Subgroup.mem_map_of_mem
              (MulAut.conj aG).toMonoidHom
              (hBE (hX₁B hx₁X₁)))
          obtain ⟨b, hb, hab⟩ :=
            sigma_Hall_tame hM
              hPsigma
              (isHall_singleton_of_isSylowSubgroupOf15 hPsylSigma)
              hx₁P hx₁aP
          let c : G := b⁻¹ * aG
          have hcfix : (MulAut.conj c) x₁ = x₁ := by
            calc
              (MulAut.conj c) x₁ =
                  b⁻¹ * (MulAut.conj aG) x₁ * b := by
                simp [c, MulAut.conj_apply, mul_assoc]
              _ = b⁻¹ * (MulAut.conj b) x₁ * b := by rw [hab]
              _ = x₁ := by simp [MulAut.conj_apply, mul_assoc]
          have hX₁map :
              X₁.map (MulAut.conj c).toMonoidHom = X₁ := by
            rw [← hx₁gen, MonoidHom.map_zpowers]
            simpa using congrArg Subgroup.zpowers hcfix
          let Ec : Subgroup G :=
            E.map (MulAut.conj c).toMonoidHom
          have hEcP : Ec ≤ P := by
            intro y hy
            rcases hy with ⟨x, hxE, rfl⟩
            have hxaP : (MulAut.conj aG) x ∈ P :=
              hEaP (Subgroup.mem_map_of_mem
                (MulAut.conj aG).toMonoidHom hxE)
            have hbinvNorm : b⁻¹ ∈ Subgroup.normalizer (P : Set G) :=
              (Subgroup.normalizer (P : Set G)).inv_mem hb.2
            have hbinvP :
                (MulAut.conj b⁻¹) ((MulAut.conj aG) x) ∈ P := by
              have hmap := Subgroup.mem_map_of_mem
                (MulAut.conj b⁻¹).toMonoidHom hxaP
              have hmapP :
                  P.map (MulAut.conj b⁻¹).toMonoidHom = P :=
                Subgroup.mem_normalizer_iff_map_conj_eq.mp hbinvNorm
              rw [hmapP] at hmap
              exact hmap
            simpa [c, MulAut.conj_apply, mul_assoc] using hbinvP
          have hX₁Ec : X₁ ≤ Ec := by
            rw [← hX₁map]
            exact Subgroup.map_mono (hX₁B.trans hBE)
          have hEccomm : IsMulCommutative Ec := by
            let eE : E ≃* Ec :=
              E.equivMapOfInjective (MulAut.conj c).toMonoidHom
                (MulAut.conj c).injective
            apply isMulCommutative_iff.mpr
            intro x y
            apply eE.symm.injective
            simpa only [map_mul] using
              isMulCommutative_iff.mp hE.2.commutative
                (eE.symm x) (eE.symm y)
          have hEcCent : Ec ≤ Subgroup.centralizer (X₁ : Set G) := by
            intro y hy
            rw [Subgroup.mem_centralizer_iff]
            intro x hx
            exact congrArg Subtype.val
              (isMulCommutative_iff.mp hEccomm
                ⟨x, hX₁Ec hx⟩ ⟨y, hy⟩)
          have hEcC₁ : Ec ≤ C₁ :=
            le_inf (hEcP.trans hPH) hEcCent
          let Fc : Subgroup G :=
            F.map (MulAut.conj c).toMonoidHom
          have hFc : IsElementaryAbelianOfRank p 3 Fc :=
            hF.map_of_injective (MulAut.conj c).toMonoidHom
              (MulAut.conj c).injective
          have hFcC₁ : Fc ≤ C₁ :=
            (Subgroup.map_mono hFE).trans hEcC₁
          exact hC₁rankAll p hp ⟨Fc, hFcC₁, hFc⟩
        obtain ⟨hZ₀, hdecomp, _htrans⟩ :=
          basic_p2maxElem_structure hB hBmax hPp hBP hPnoncomm
        obtain ⟨Y, _hYcyclic, hZ₀Y, hY⟩ := hdecomp
        have hX₁line : RankOneLineIn p B X₁ := ⟨le_sup_left, hX₁⟩
        have hX₁neZ₀ : X₁ ≠ Z₀ := by
          intro hEq
          apply hX₁notZ₀
          rw [hEq]
        obtain ⟨hdisX₁Y, hX₁Ycomm, hX₁Ysup⟩ :=
          hY X₁ hX₁line hX₁neZ₀
        have hXcomm : IsMulCommutative X := by
          letI : IsCyclic X := hXcyclic
          infer_instance
        have hXX₁cent : X ≤ Subgroup.centralizer (X₁ : Set G) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact (congrArg Subtype.val
            (isMulCommutative_iff.mp hXcomm
              ⟨x, hx⟩ ⟨y, hX₁X hy⟩)).symm
        have hXZ₁cent : X ≤ Subgroup.centralizer (Z₁ : Set G) := by
          intro x hx
          rw [Subgroup.mem_centralizer_iff]
          intro z hz
          exact ((omegaOneCenterAmbient_le_centerWithin p P
            (hZ₁Z₀ hz)).2 x (hXP hx)).symm
        have hXBcent : X ≤ Subgroup.centralizer (B : Set G) := by
          simpa [B] using le_centralizer_sup15 hXX₁cent hXZ₁cent
        have hXC : X ≤ centralizerWithin P B :=
          le_inf hXP hXBcent
        have hXleSup : X ≤ X₁ ⊔ Y :=
          hXC.trans (le_of_eq hX₁Ysup.symm)
        let D : Subgroup G := Y ⊓ X
        have hdisX₁D : Disjoint X₁ D :=
          hdisX₁Y.mono_right inf_le_left
        have hDp : IsPGroup p D := hXp.to_le inf_le_right
        have hDbot : D = ⊥ := by
          by_contra hDne
          have hpD : p ∣ Nat.card D :=
            hDp.card_eq_or_dvd.resolve_left
              (fun hcard ↦ hDne (Subgroup.card_eq_one.mp hcard))
          obtain ⟨L, hLD, hL⟩ :=
            exists_rankOneLineIn_of_primeSupport15
              (show p ∈ primeSupport (Nat.card D) from ⟨hp, hpD⟩)
          have hX₁omega :=
            rankOneLine_eq_omegaOne_of_cyclic_pgroup15
              hXcyclic hXp hX₁X hX₁
          have hLomega :=
            rankOneLine_eq_omegaOne_of_cyclic_pgroup15
              hXcyclic hXp (hLD.trans inf_le_right) hL
          have hLX₁ : L ≤ X₁ := by
            rw [hLomega, hX₁omega]
          have hLbot : L ≤ (⊥ : Subgroup G) := by
            rw [← hdisX₁D.eq_bot]
            exact le_inf hLX₁ hLD
          exact hL.ne_bot (le_antisymm hLbot bot_le)
        have hXX₁ : X = X₁ := by
          apply le_antisymm ?_ hX₁X
          intro x hx
          have hX₁normY : X₁ ≤ Subgroup.normalizer (Y : Set G) := by
            intro a ha
            apply Subgroup.centralizer_le_normalizer (Y : Set G)
            rw [Subgroup.mem_centralizer_iff]
            intro y hy
            exact (hX₁Ycomm a ha y hy).eq.symm
          have hxProd : x ∈ (X₁ : Set G) * (Y : Set G) := by
            rw [← Subgroup.coe_mul_of_left_le_normalizer_right
              X₁ Y hX₁normY]
            exact hXleSup hx
          rcases hxProd with ⟨a, ha, y, hy, haxy⟩
          have hyX : y ∈ X := by
            have hmem : a⁻¹ * x ∈ X :=
              X.mul_mem (X.inv_mem (hX₁X ha)) hx
            rw [← haxy] at hmem
            simpa [mul_assoc] using hmem
          have hyD : y ∈ D := ⟨hy, hyX⟩
          have hyOne : y = 1 := by
            rw [hDbot] at hyD
            exact Subgroup.mem_bot.mp hyD
          subst y
          change a * 1 = x at haxy
          rw [← haxy]
          exact X₁.mul_mem ha X₁.one_mem
        refine ⟨?_, ?_, B, le_sup_left, ?_, hB, hBmax, ?_, ?_⟩
        · rw [hXX₁, hX₁.card_eq, pow_one]
        · simpa [Z₀, P] using hZ₀
        · simpa [P] using hBP
        · simpa [P] using hPsylG
        · simpa [Z₀, P] using hX₁notZ₀
      have hXeq : Nat.card X = p := hXeq_center.1
      have hZ₀rank : IsElementaryAbelianOfRank p 1
          (omegaOneCenterAmbient p ((pCore p H).map H.subtype)) :=
        hXeq_center.2.1
      obtain ⟨B, hX₁B, hBP, hB, hBmax, hPsylG, hX₁notZ₀⟩ :=
        hXeq_center.2.2
      have hpc :
          ¬ IsMulCommutative
            (pCore (Nat.card (nonTIFittingIntersection M g)) H) := by
        rw [show Nat.card (nonTIFittingIntersection M g) = p by
          simpa [X] using hXeq]
        simpa [H] using hPnonab
      have hp'cyc :
          IsCyclic
            (pPrimeCore (Nat.card (nonTIFittingIntersection M g)) H) := by
        let P : Subgroup G := (pCore p H).map H.subtype
        let K : Subgroup G := (pPrimeCore p H).map H.subtype
        have hPp : IsPGroup p P := by
          simpa [P] using pCore_isPGroup.map H.subtype
        have hPnoncomm : ¬ IsMulCommutative P := by
          intro hPcomm
          let eP : pCore p H ≃* P :=
            (pCore p H).equivMapOfInjective H.subtype
              H.subtype_injective
          apply hPnonab
          apply isMulCommutative_iff.mpr
          intro a b
          apply eP.injective
          exact isMulCommutative_iff.mp hPcomm (eP a) (eP b)
        have hKPcent : K ≤ Subgroup.centralizer (P : Set G) := by
          intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          rcases hk with ⟨kH, hkCore, rfl⟩
          rcases hx with ⟨xH, hxCore, hxval⟩
          have hcent := Subgroup.mem_centralizer_iff.mp
            ((pCore_le_centralizer_pPrimeCore (G := H) p) hxCore)
              kH hkCore
          exact hxval ▸ (congrArg Subtype.val hcent).symm
        have hKH : K ≤ H := Subgroup.map_subtype_le _
        have hX₁P : X₁ ≤ P := by
          have hX₁H : X₁ ≤ H := hX₁X.trans hXH
          letI : Group.IsNilpotent H := hnilH
          have hX₁core : X₁.subgroupOf H ≤ pCore p H :=
            (hX₁.isPGroup.of_equiv
              (Subgroup.subgroupOfEquivOfLe hX₁H).symm).le_pCore_of_isNilpotent
          rw [← Subgroup.map_subgroupOf_eq_of_le hX₁H]
          exact Subgroup.map_mono hX₁core
        have hKX₁cent : K ≤ Subgroup.centralizer (X₁ : Set G) := by
          intro k hk
          rw [Subgroup.mem_centralizer_iff]
          intro x hx
          exact Subgroup.mem_centralizer_iff.mp (hKPcent hk) x (hX₁P hx)
        have hKC₁ : K ≤ C₁ := le_inf hKH hKX₁cent
        have hPuniq : P ∈ minSimple_uniq_max_groups (G := G) :=
          nonabelian_Uniqueness hPp hPnoncomm
        have hNoRank : ∀ q : ℕ, q.Prime →
            ¬ HasElementaryAbelianRankAtLeast q 2 (pPrimeCore p H) := by
          intro q hq hRank
          rcases hRank with ⟨A, hAK, hA⟩
          let AG : Subgroup G := A.map H.subtype
          have hAGK : AG ≤ K := by
            exact Subgroup.map_mono hAK
          have hAG : IsElementaryAbelianOfRank q 2 AG :=
            hA.map_of_injective H.subtype H.subtype_injective
          have hKuniq : K ∈ minSimple_uniq_max_groups (G := G) :=
            cent_uniq_Uniqueness hPuniq hKPcent
              ⟨q, hq, AG, hAGK, hAG⟩
          exact hC₁.1 (uniq_mmaxS hKC₁ hC₁proper hKuniq)
        let K₀ : Subgroup H := pPrimeCore p H
        have hK₀Z : IsZGroup K₀ := by
          refine ⟨?_⟩
          intro q hq Q
          letI : Fact q.Prime := ⟨hq⟩
          let j : K₀ →* G := H.subtype.comp K₀.subtype
          let QG : Subgroup G := (Q : Subgroup K₀).map j
          have hj : Function.Injective j :=
            H.subtype_injective.comp K₀.subtype_injective
          have hcardQG :
              Nat.card QG = Nat.card (Q : Subgroup K₀) :=
            Subgroup.card_map_of_injective hj
          have hQodd : Odd (Nat.card (Q : Subgroup K₀)) := by
            rw [← hcardQG]
            exact mFT_odd QG
          apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
            Q.isPGroup' hQodd).2
          rintro ⟨A, hA⟩
          let AK : Subgroup K₀ := A.map (Q : Subgroup K₀).subtype
          have hAK : IsElementaryAbelianOfRank q 2 AK :=
            hA.map_of_injective (Q : Subgroup K₀).subtype
              (Q : Subgroup K₀).subtype_injective
          let AH : Subgroup H := AK.map K₀.subtype
          have hAH : IsElementaryAbelianOfRank q 2 AH :=
            hAK.map_of_injective K₀.subtype K₀.subtype_injective
          exact hNoRank q hq
            ⟨AH, Subgroup.map_subtype_le AK, hAH⟩
        letI : IsZGroup K₀ := hK₀Z
        letI : Group.IsNilpotent H := hnilH
        have hK₀nil : Group.IsNilpotent K₀ := by infer_instance
        letI : Group.IsNilpotent K₀ := hK₀nil
        rw [show Nat.card (nonTIFittingIntersection M g) = p by
          simpa [X] using hXeq]
        simpa [H, K₀] using (inferInstance : IsCyclic K₀)
      have halt :
          (∀ q ∈ primeSupport (Nat.card H),
              Monoid.exponent (M ⧸ H.subgroupOf M) ∣ q - 1) ∨
            (Nat.card (pCore p H) = p ^ 3 ∧
              M ∈ typeP1MaximalSubgroups (G := G) ∧
              Nat.card (M ⧸ H.subgroupOf M) ∣ p + 1) := by
        let P : Subgroup G := (pCore p H).map H.subtype
        have hPp : IsPGroup p P := by
          simpa [P] using pCore_isPGroup.map H.subtype
        have hPH : P ≤ H := Subgroup.map_subtype_le _
        have hPnoncomm : ¬ IsMulCommutative P := by
          intro hPcomm
          let eP : pCore p H ≃* P :=
            (pCore p H).equivMapOfInjective H.subtype
              H.subtype_injective
          apply hPnonab
          apply isMulCommutative_iff.mpr
          intro a b
          apply eP.injective
          exact isMulCommutative_iff.mp hPcomm (eP a) (eP b)
        have hpPrimeCyclic : IsCyclic (pPrimeCore p H) := by
          rw [← hXeq]
          simpa [X] using hp'cyc

        /- The characteristic family `Z(q) = Omega_1(Z(O_q(H)))` and its
        prime-order calculation are shared by the two type branches. -/
        let Z (q : ℕ) : Subgroup G :=
          omegaOneCenterAmbient q ((pCore q H).map H.subtype)
        have hMnormH : M ≤ Subgroup.normalizer (H : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hHM).mp hHnormal
        have hMnormZ (q : ℕ) :
            M ≤ Subgroup.normalizer (Z q : Set G) := by
          let Q : Subgroup G := (pCore q H).map H.subtype
          have hnormQ : Subgroup.normalizer (H : Set G) ≤
              Subgroup.normalizer (Q : Set G) := by
            simpa [Q] using
              (characteristic_map_subtype_le_normalizer15 H (pCore q H))
          have hnormZ : Subgroup.normalizer (Q : Set G) ≤
              Subgroup.normalizer (Z q : Set G) := by
            simpa [Q, Z, omegaOneCenterAmbient] using
              (characteristic_map_subtype_le_normalizer15 Q
                (Submission.OddOrder.BG.Section05.omegaOneCenter q Q))
          exact hMnormH.trans (hnormQ.trans hnormZ)
        have hZH (q : ℕ) : Z q ≤ H := by
          exact (omegaOneCenterAmbient_le_centerWithin q
            ((pCore q H).map H.subtype)).trans
              ((centralizerWithin_le_left _ _).trans
                (Subgroup.map_subtype_le _))
        have hZcard : ∀ q ∈ primeSupport (Nat.card H),
            Nat.card (Z q) = q := by
          intro q hqH
          have hq : q.Prime := hqH.1
          letI : Fact q.Prime := ⟨hq⟩
          by_cases hqp : q = p
          · subst q
            simpa [Z, P, pow_one] using hZ₀rank.card_eq
          · let Q₀ : Subgroup H := pCore q H
            let Q : Subgroup G := Q₀.map H.subtype
            have hQp : IsPGroup q Q := by
              simpa [Q, Q₀] using pCore_isPGroup.map H.subtype
            have hQ₀ne : Q₀ ≠ ⊥ := by
              letI : Group.IsNilpotent H := hnilH
              exact (pCore_ne_bot_iff_dvd_card_of_isNilpotent
                (G := H) q).2 hqH.2
            have hQne : Q ≠ ⊥ := by
              dsimp [Q]
              exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
                Q₀ H.subtype_injective)).mpr hQ₀ne
            have hQ₀le : Q₀ ≤ pPrimeCore p H :=
              pCore_le_pPrimeCore_of_ne (G := H) (p := p) (q := q)
                (fun hpq ↦ hqp hpq.symm)
            have hQ₀cyclic : IsCyclic Q₀ := by
              letI : IsCyclic (pPrimeCore p H) := hpPrimeCyclic
              exact Subgroup.isCyclic_of_le hQ₀le
            let eQ : Q₀ ≃* Q :=
              Q₀.equivMapOfInjective H.subtype H.subtype_injective
            have hQcyclic : IsCyclic Q := eQ.isCyclic.mp hQ₀cyclic
            simpa [Z, Q, Q₀] using
              card_omegaOneCenterAmbient_of_cyclic_pgroup15
                hQcyclic hQp hQne
        have regularZ_dvd_pred
            {A : Subgroup G} (hAM : A ≤ M)
            (q : ℕ) (hqH : q ∈ primeSupport (Nat.card H))
            (hreg : IsSemiregularConjugation (Z q) A) :
            Nat.card A ∣ q - 1 := by
          rw [← hZcard q hqH]
          exact semiregular_card_dvd_sub_one15 hreg
            (hAM.trans (hMnormZ q))

        obtain ⟨K, hKM, hHallK⟩ :=
          Submission.OddOrder.MathlibSupport.exists_ambient_isHall_of_isSolvable
            (mmax_sol hM) (kappaPrimes M)
        obtain ⟨U, hKUCompl⟩ := ex_kappa_compl hM hKM hHallK
        have hkappa := kappa_structure hM hKUCompl
        rcases htype with hF | hP₁
        · /- Type F: `K = 1`, and the same-exponent Frobenius
          complement furnished by Lemma 15.1 acts regularly on every
          `Z(q)`. -/
          left
          have hKbot : K = ⊥ :=
            (trivg_kappa hM hKM hHallK).2 hF
          have hUne : U ≠ ⊥ := by
            intro hUbot
            have hP₁bad : M ∈ typeP1MaximalSubgroups (G := G) :=
              (trivg_kappa_compl hM hKUCompl).1 hUbot
            exact hP₁bad.1.2 hF
          have hSigmaU : sigmaCore M ⊔ U = M :=
            semidirect_left_eq_ambient_of_right_eq_bot15
              hkappa.sigmaU_K_sdprod hKbot
          have hsdHU : IsInternalSemidirectProductIn H U M := by
            simpa [hHsigma, hSigmaU] using hkappa.sigma_U_sdprod
          letI : (H.subgroupOf M).Normal := hsdHU.2.2.1
          obtain ⟨U₀, hU₀U, hexp, _hsdU₀, hfrob⟩ :=
            hkappa.exponent_frobenius hUne
          have hregSigma :
              IsSemiregularConjugation (sigmaCore M) U₀ := by
            intro r hr z hfix
            let J₀ : Subgroup G := sigmaCore M ⊔ U₀
            let rJ : U₀.subgroupOf J₀ :=
              ⟨⟨r, (show U₀ ≤ J₀ from by simp [J₀]) r.property⟩,
                r.property⟩
            let zJ : (sigmaCore M).subgroupOf J₀ :=
              ⟨⟨z, (show sigmaCore M ≤ J₀ from by simp [J₀]) z.property⟩,
                z.property⟩
            have hrJ : rJ ≠ 1 := by
              intro hrOne
              apply hr
              apply Subtype.ext
              exact congrArg (fun x : U₀.subgroupOf J₀ ↦
                ((x : J₀) : G)) hrOne
            have hfixJ :
                (rJ : J₀) * (zJ : J₀) * (rJ : J₀)⁻¹ = zJ := by
              apply Subtype.ext
              exact hfix
            have hzOne := hfrob.fixedPointFree rJ hrJ zJ hfixJ
            apply Subtype.ext
            exact congrArg (fun x : (sigmaCore M).subgroupOf J₀ ↦
              ((x : J₀) : G)) hzOne
          intro q hqH
          have hZsigma : Z q ≤ sigmaCore M := by
            rw [← hHsigma]
            exact hZH q
          have hregZ : IsSemiregularConjugation (Z q) U₀ :=
            hregSigma.mono_left hZsigma
          have hcardDvd : Nat.card U₀ ∣ q - 1 :=
            regularZ_dvd_pred (hU₀U.trans hKUCompl.U_le_M)
              q hqH hregZ
          rw [semidirect_quotient_exponent15 hsdHU, ← hexp]
          exact Group.exponent_dvd_nat_card.trans hcardDvd

        · /- Type P1: `U = 1`, so `M = H ><| K`.  The centralizer
          `K* = C_H(K)` has order `p` and is contained in `P`. -/
          have hUbot : U = ⊥ :=
            (trivg_kappa_compl hM hKUCompl).2 hP₁
          have hKne : K ≠ ⊥ := by
            intro hKbot
            exact hP₁.1.2 ((trivg_kappa hM hKM hHallK).1 hKbot)
          have hsdHK : IsInternalSemidirectProductIn H K M := by
            simpa [hHsigma, hUbot] using hkappa.sigmaU_K_sdprod
          letI : (H.subgroupOf M).Normal := hsdHK.2.2.1
          have hquotCard : Nat.card (M ⧸ H.subgroupOf M) = Nat.card K :=
            semidirect_quotient_card15 hsdHK
          have hquotExp :
              Monoid.exponent (M ⧸ H.subgroupOf M) =
                Monoid.exponent K :=
            semidirect_quotient_exponent15 hsdHK
          have hPstruct := Ptype_structure hP₁.1 hKM hHallK
          have hprimeAction : IsPrimeAction H K := by
            simpa [hHsigma] using hPstruct.sigma_K_prime
          let Ks : Subgroup G := centralizerWithin H K
          obtain ⟨Mstar, hEmbed⟩ :=
            Ptype_embedding hP₁.1 hKM hHallK
          have hPartnerPrime :
              (Nat.card (pTypePartner M K)).Prime := by
            have hright := hEmbed.typeP2_prime.resolve_left (by
              intro hleft
              exact hleft.1.2 hP₁)
            exact hright.2
          have hKsPrime : (Nat.card Ks).Prime := by
            simpa [Ks, pTypePartner, hHsigma] using hPartnerPrime
          have hcyclics := Ptype_cyclics hP₁.1 hKM hHallK
          have hDerSd := hkappa.derived_decomposition hKne
          have hDerEq : derivedWithin M = H := by
            symm
            calc
              H = sigmaCore M := hHsigma
              _ = derivedWithin M :=
                semidirect_left_eq_ambient_of_right_eq_bot15
                  hDerSd hUbot
          letI : Group.IsNilpotent H := hnilH
          have hCoreComp :
              (pCore p H).IsComplement' (pPrimeCore p H) := by
            apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
              (disjoint_pCore_pPrimeCore (G := H) (p := p))
            rw [← Subgroup.normal_mul,
              sup_pCore_pPrimeCore_eq_top_of_isNilpotent (G := H) p]
            rfl
          have hQuotComm :
              IsMulCommutative (H ⧸ pCore p H) := by
            let e : (H ⧸ pCore p H) ≃* pPrimeCore p H :=
              hCoreComp.symm.QuotientMulEquiv
            have hPrimeComm : IsMulCommutative (pPrimeCore p H) := by
              letI : IsCyclic (pPrimeCore p H) := hpPrimeCyclic
              infer_instance
            apply isMulCommutative_iff.mpr
            intro a b
            apply e.injective
            simpa only [map_mul] using
              isMulCommutative_iff.mp hPrimeComm (e a) (e b)
          have hDerCore : _root_.commutator H ≤ pCore p H :=
            Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
              hQuotComm
          have hSecondP : secondDerivedWithin M ≤ P := by
            rw [secondDerivedWithin, hDerEq]
            exact Subgroup.map_mono hDerCore
          have hKsSecond : Ks ≤ secondDerivedWithin M := by
            simpa [Ks, kappaCentralizer, hHsigma] using
              hcyclics.partner_le_secondDerived
          have hKsP : Ks ≤ P := hKsSecond.trans hSecondP
          have hKsp : IsPGroup p Ks := hPp.to_le hKsP
          have hKsne : Ks ≠ ⊥ := by
            intro hbot
            apply hKsPrime.ne_one
            exact Subgroup.card_eq_one.mpr hbot
          have hpKs : p ∣ Nat.card Ks :=
            hKsp.card_eq_or_dvd.resolve_left
              (fun hcard ↦ hKsne (Subgroup.card_eq_one.mp hcard))
          have hKsCard : Nat.card Ks = p := by
            exact (((Nat.dvd_prime hKsPrime).mp hpKs).resolve_left
              hp.ne_one).symm
          have hKcyclic : IsCyclic K := hkappa.K_cyclic
          have hKnormP : K ≤ Subgroup.normalizer (P : Set G) := by
            exact hKM.trans (hMnormH.trans (by
              simpa [P] using
                (characteristic_map_subtype_le_normalizer15 H (pCore p H))))
          have hKpi : IsPiNumber (kappaPrimes M) (Nat.card K) := by
            simpa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hKM] using
              hHallK.isPiNumber_card
          have hKcop : Nat.Coprime p (Nat.card K) := by
            apply hp.coprime_iff_not_dvd.mpr
            intro hpK
            exact (kappa_sigma' M (hKpi hp hpK))
              (hXsigma hp hpX.2)

          by_cases hImp : Ks = Z p → Nat.card K ∣ p - 1
          · left
            intro q hqH
            have hq : q.Prime := hqH.1
            by_cases hKsZq : Ks = Z q
            · have hqp : q = p := by
                have hcardEq : p = q := by
                  rw [← hKsCard, hKsZq, hZcard q hqH]
                exact hcardEq.symm
              subst q
              rw [hquotExp]
              exact Group.exponent_dvd_nat_card.trans (hImp hKsZq)
            · have hdis : Disjoint Ks (Z q) :=
                disjoint_of_prime_cards_of_ne15
                  (by simpa [hKsCard] using hp)
                  (by simpa [hZcard q hqH] using hq) hKsZq
              have hreg : IsSemiregularConjugation (Z q) K := by
                intro k hk z hfix
                have hkG : (k : G) ≠ 1 := by
                  intro hkOne
                  apply hk
                  exact Subtype.ext hkOne
                let R : Subgroup G := Subgroup.zpowers (k : G)
                have hRK : R ≤ K :=
                  Subgroup.zpowers_le.mpr k.property
                have hRne : R ≠ ⊥ :=
                  Subgroup.zpowers_ne_bot.mpr hkG
                have hcentEq := hprimeAction.centralizer_eq hRK hRne
                have hcomm : (k : G) * (z : G) = (z : G) * (k : G) := by
                  calc
                    (k : G) * (z : G) =
                        ((k : G) * (z : G) * (k : G)⁻¹) * (k : G) := by
                      simp [mul_assoc]
                    _ = (z : G) * (k : G) := by rw [hfix]
                have hzCent : (z : G) ∈ centralizerWithin H R := by
                  refine ⟨hZH q z.property, ?_⟩
                  intro y hy
                  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
                  exact ((show Commute (k : G) (z : G) from hcomm).zpow_left n).eq
                have hzKs : (z : G) ∈ Ks := by
                  rw [hcentEq] at hzCent
                  exact hzCent
                have hzBot : (z : G) ∈ (⊥ : Subgroup G) := by
                  rw [← hdis.eq_bot]
                  exact ⟨hzKs, z.property⟩
                apply Subtype.ext
                exact Subgroup.mem_bot.mp hzBot
              have hcardDvd : Nat.card K ∣ q - 1 :=
                regularZ_dvd_pred hKM q hqH hreg
              rw [hquotExp]
              exact Group.exponent_dvd_nat_card.trans hcardDvd

          · /- The failed implication gives `K* = Z(p)` and excludes
            the `p - 1` divisor.  Faithfulness plus Theorem 5.5 rules out
            rank three in `P`; Corollary 10.7 then forces `|P| = p^3`. -/
            have hKsZ : Ks = Z p := by
              by_contra hne
              exact hImp (fun heq ↦ (hne heq).elim)
            have hnotKpred : ¬ Nat.card K ∣ p - 1 := by
              intro hdvd
              exact hImp (fun _ ↦ hdvd)
            have hX₁notKs : ¬ X₁ ≤ Ks := by
              intro hle
              apply hX₁notZ₀
              rw [hKsZ] at hle
              simpa [Z, P] using hle
            have hCKP : centralizerWithin K P = ⊥ := by
              apply le_bot_iff.mp
              intro k hk
              have hkOne : k = 1 := by
                by_contra hk1
                let R : Subgroup G := Subgroup.zpowers k
                have hRK : R ≤ K :=
                  Subgroup.zpowers_le.mpr hk.1
                have hRne : R ≠ ⊥ :=
                  Subgroup.zpowers_ne_bot.mpr hk1
                have hcentEq := hprimeAction.centralizer_eq hRK hRne
                apply hX₁notKs
                intro x hx
                have hxCent : x ∈ centralizerWithin H R := by
                  refine ⟨hX₁X.trans hXH hx, ?_⟩
                  intro y hy
                  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
                  have hkx : k * x = x * k :=
                    (hk.2 x (hBP (hX₁B hx))).symm
                  exact ((show Commute k x from hkx).zpow_left n).eq
                rw [hcentEq] at hxCent
                exact hxCent
              exact Subgroup.mem_bot.mpr hkOne
            let i : K →* Subgroup.normalizer (P : Set G) :=
              { toFun := fun k ↦ ⟨k, hKnormP k.property⟩
                map_one' := rfl
                map_mul' := fun _ _ ↦ rfl }
            let rho : K →* MulAut P := P.normalizerMonoidHom.comp i
            have hrho : Function.Injective rho := by
              rw [← MonoidHom.ker_eq_bot_iff]
              ext k
              change i k ∈ P.normalizerMonoidHom.ker ↔
                k ∈ (⊥ : Subgroup K)
              rw [Subgroup.normalizerMonoidHom_ker]
              constructor
              · intro hkCent
                have hkBot : (k : G) ∈ (⊥ : Subgroup G) := by
                  rw [← hCKP]
                  exact ⟨k.property, hkCent⟩
                exact Subgroup.mem_bot.mpr (by
                  apply Subtype.ext
                  exact Subgroup.mem_bot.mp hkBot)
              · intro hkBot
                have hkOne : k = 1 := Subgroup.mem_bot.mp hkBot
                subst k
                simp
            let A : Subgroup (MulAut P) := rho.range
            have hAsol : IsSolvable A := by
              letI : IsSolvable K :=
                mFT_sol (lt_of_le_of_lt hKM (mmax_proper hM))
              exact solvable_of_surjective rho.rangeRestrict_surjective
            have hAodd : Odd (Nat.card A) :=
              (mFT_odd K).of_dvd_nat (Subgroup.card_range_dvd rho)
            have hNarrow :
                Submission.OddOrder.BG.Section05.IsNarrow p
                  (⊤ : Subgroup P) := by
              intro _
              let BP : Subgroup P := B.subgroupOf P
              have hBmaxP : IsPMaxElem p P B :=
                hBmax.of_le le_top hBP
              exact ⟨BP, hB.subgroupOf hBP, hBmaxP.subgroupOf_top⟩
            have hNoRank :
                ¬ ∃ E : Subgroup P,
                  IsElementaryAbelianOfRank p 3 E := by
              intro hRank
              obtain ⟨_, _, horder⟩ :=
                Submission.OddOrder.BG.Section05.Aut_narrow
                  (show IsPGroup p P from hPp) (mFT_odd P) A
                    hNarrow hAsol hAodd
              obtain ⟨xK, hxgenMem⟩ := hKcyclic.exists_generator
              let x : G := xK
              have hxK : x ∈ K := xK.property
              have hxgen : Subgroup.zpowers x = K := by
                apply le_antisymm (Subgroup.zpowers_le.mpr hxK)
                intro y hy
                have hyPow : (⟨y, hy⟩ : K) ∈
                    Subgroup.zpowers xK := hxgenMem ⟨y, hy⟩
                rw [Subgroup.mem_zpowers_iff] at hyPow ⊢
                rcases hyPow with ⟨n, hn⟩
                exact ⟨n, congrArg Subtype.val hn⟩
              let ax : A := ⟨rho xK, ⟨xK, rfl⟩⟩
              have hxOrder : orderOf xK = Nat.card K := by
                calc
                  orderOf xK = orderOf x :=
                    (orderOf_injective K.subtype K.subtype_injective xK).symm
                  _ = Nat.card (Subgroup.zpowers x) :=
                    (Nat.card_zpowers x).symm
                  _ = Nat.card K := by rw [hxgen]
              have haxOrder : orderOf ax = Nat.card K := by
                calc
                  orderOf ax = orderOf (rho xK) :=
                    (orderOf_injective A.subtype A.subtype_injective ax).symm
                  _ = orderOf xK := orderOf_injective rho hrho xK
                  _ = Nat.card K := hxOrder
              have hcopAx : Nat.Coprime p (orderOf ax) := by
                rw [haxOrder]
                exact hKcop
              apply hnotKpred
              simpa [haxOrder] using horder hRank ax hcopAx
            obtain ⟨Pₜ, hPPₜ⟩ := hPsylG
            let eTop : (⊤ : Subgroup G) ≃* G := Subgroup.topEquiv
            let Pₛ : Sylow p G :=
              Pₜ.mapSurjective (f := eTop.toMonoidHom) eTop.surjective
            have hPPₛ : P = (Pₛ : Subgroup G) := by
              dsimp only [P]
              rw [hPPₜ]
              change (Pₜ : Subgroup (⊤ : Subgroup G)).map
                    (⊤ : Subgroup G).subtype =
                (Pₜ : Subgroup (⊤ : Subgroup G)).map eTop.toMonoidHom
              congr 1
            have hNoRankS :
                ¬ ∃ E : Subgroup Pₛ,
                  IsElementaryAbelianOfRank p 3 E := by
              rintro ⟨E, hE⟩
              let EG : Subgroup G := E.map (Pₛ : Subgroup G).subtype
              have hEGP : EG ≤ P := by
                rw [hPPₛ]
                exact Subgroup.map_subtype_le E
              let EP : Subgroup P := EG.subgroupOf P
              have hEG : IsElementaryAbelianOfRank p 3 EG :=
                hE.map_of_injective (Pₛ : Subgroup G).subtype
                  (Pₛ : Subgroup G).subtype_injective
              exact hNoRank ⟨EP, hEG.subgroupOf hEGP⟩
            have hPₛnoncomm : ¬ IsMulCommutative Pₛ := by
              intro hcomm
              apply hPnoncomm
              rw [hPPₛ]
              exact hcomm
            obtain ⟨S, C, hSnoncomm, hScard, _hSexp, hCcent,
                hSCsup, hCcyclic, hOmega⟩ :=
              mFT_rank2_Sylow_cprod Pₛ hNoRankS hPₛnoncomm

            /- Faithfulness on `P` promotes centralization of
            `Omega_1(Z(P)) = K*` to centralization of the whole center. -/
            let CP : Subgroup G := (Subgroup.center P).map P.subtype
            have hCPcenter : CP = centerWithin P := by
              simpa [CP] using map_center_eq_centerWithin P
            have hCPP : CP ≤ P := Subgroup.map_subtype_le _
            have hCPp : IsPGroup p CP := hPp.to_le hCPP
            have hKnormCP : K ≤ Subgroup.normalizer (CP : Set G) := by
              exact hKnormP.trans (by
                simpa [CP] using
                  (characteristic_map_subtype_le_normalizer15 P
                    (Subgroup.center P)))
            let eCP : Subgroup.center P ≃* CP :=
              (Subgroup.center P).equivMapOfInjective P.subtype
                P.subtype_injective
            have hOmegaCP :
                (omegaOne p CP).map CP.subtype =
                  omegaOneCenterAmbient p P := by
              rw [← map_omegaOne_equiv p eCP, Subgroup.map_map,
                omegaOneCenterAmbient,
                Submission.OddOrder.BG.Section05.omegaOneCenter,
                Subgroup.map_map]
              congr 1
            have hKsCentK : Ks ≤ Subgroup.centralizer (K : Set G) :=
              inf_le_right
            have hKCentKs : K ≤ Subgroup.centralizer (Ks : Set G) :=
              Subgroup.le_centralizer_iff.mp hKsCentK
            have hKCentOmega : K ≤ Subgroup.centralizer
                (((omegaOne p CP).map CP.subtype : Subgroup G) : Set G) := by
              have hKsAmbient : Ks = omegaOneCenterAmbient p P := by
                simpa [Z, P] using hKsZ
              have hKsOmega :
                  Ks = (omegaOne p CP).map CP.subtype :=
                hKsAmbient.trans hOmegaCP.symm
              rw [← hKsOmega]
              exact hKCentKs
            have hPcop : Nat.Coprime (Nat.card P) (Nat.card K) := by
              obtain ⟨n, hn⟩ := hPp.exists_card_eq
              rw [hn]
              exact hKcop.pow_left n
            have hCPcop : Nat.Coprime (Nat.card CP) (Nat.card K) :=
              hPcop.coprime_dvd_left (Subgroup.card_dvd_of_le hCPP)
            have hKCentCP : K ≤ Subgroup.centralizer (CP : Set G) :=
              coprime_odd_faithful_omegaOne_of_odd_card
                hCPp hKnormCP hCPcop (mFT_odd CP) hKCentOmega
            have hCPKs : CP ≤ Ks := by
              exact le_inf (hCPP.trans hPH)
                (Subgroup.le_centralizer_iff.mp hKCentCP)
            have hKsCP : Ks ≤ CP := by
              rw [hKsZ]
              simpa [Z, P, hCPcenter] using
                (omegaOneCenterAmbient_le_centerWithin p P)
            have hCenterKs : centerWithin P = Ks := by
              rw [← hCPcenter]
              exact le_antisymm hCPKs hKsCP

            have hSP : S ≤ P := by
              rw [hPPₛ]
              exact le_sup_left.trans_eq hSCsup
            have hCPartP : C ≤ P := by
              rw [hPPₛ]
              exact le_sup_right.trans_eq hSCsup
            have hCcomm : IsMulCommutative C := by
              letI : IsCyclic C := hCcyclic
              infer_instance
            have hCCentC : C ≤ Subgroup.centralizer (C : Set G) :=
              Subgroup.le_centralizer_iff_isMulCommutative.mpr hCcomm
            have hCCentP : C ≤ Subgroup.centralizer (P : Set G) := by
              rw [hPPₛ, ← hSCsup]
              exact le_centralizer_sup15 hCcent hCCentC
            have hCCP : C ≤ centerWithin P :=
              le_inf hCPartP hCCentP
            have hCKs : C ≤ Ks := by
              rw [← hCenterKs]
              exact hCCP
            have hSp : IsPGroup p S :=
              Pₛ.isPGroup'.to_le (by
                rw [← hSCsup]
                exact le_sup_left)
            have hSextra : IsExtraspecial S :=
              isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
                hSp hScard hSnoncomm
            have hOmegaNe : (omegaOne p C).map C.subtype ≠ ⊥ := by
              rw [hOmega]
              have hCenterS : Subgroup.center S ≠ ⊥ :=
                hSextra.center_ne_bot
              exact (not_congr (Subgroup.map_eq_bot_iff_of_injective
                (Subgroup.center S) S.subtype_injective)).mpr hCenterS
            have hCne : C ≠ ⊥ := by
              intro hCbot
              apply hOmegaNe
              exact le_bot_iff.mp
                ((Subgroup.map_subtype_le (omegaOne p C)).trans_eq hCbot)
            have hCp : IsPGroup p C := hPp.to_le hCPartP
            have hpC : p ∣ Nat.card C :=
              hCp.card_eq_or_dvd.resolve_left
                (fun hcard ↦ hCne (Subgroup.card_eq_one.mp hcard))
            have hCcard : Nat.card C = p := by
              have hCdvd : Nat.card C ∣ p := by
                rw [← hKsCard]
                exact Subgroup.card_dvd_of_le hCKs
              exact (Nat.dvd_prime hp).mp hCdvd |>.resolve_left
                (fun hOne ↦ hp.not_dvd_one (by
                  simpa [hOne] using hpC))
            have hCpow : ∀ c : C, c ^ p = 1 := by
              intro c
              rw [← hCcard]
              exact pow_card_eq_one'
            have hOmegaTop : omegaOne p C = ⊤ :=
              omegaOne_eq_top_of_pow_eq_one15 hCpow
            have hCcenterS : C = (Subgroup.center S).map S.subtype := by
              rw [hOmegaTop, ← MonoidHom.range_eq_map,
                Subgroup.range_subtype] at hOmega
              exact hOmega
            have hCS : C ≤ S := by
              rw [hCcenterS]
              exact Subgroup.map_subtype_le _
            have hPeqS : P = S := by
              rw [hPPₛ, ← hSCsup, sup_eq_left.mpr hCS]
            have hPcard : Nat.card P = p ^ 3 := by
              rw [hPeqS]
              exact hScard
            have hPextra : IsExtraspecial P :=
              isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
                hPp hPcard hPnoncomm

            /- Apply Theorem 2.5 inside `J = P K`.  Prime action identifies
            every nonidentity element centralizer with `Z(P) = K*`. -/
            have hAmbientCent : ∀ {k : G}, k ∈ K → k ≠ 1 →
                centralizerWithin P (Subgroup.zpowers k) =
                  centerWithin P := by
              intro k hkK hk1
              let R : Subgroup G := Subgroup.zpowers k
              have hRK : R ≤ K := Subgroup.zpowers_le.mpr hkK
              have hRne : R ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hk1
              have hcent := hprimeAction.centralizer_eq hRK hRne
              ext x
              constructor
              · intro hx
                have hxH : x ∈ centralizerWithin H R :=
                  ⟨hPH hx.1, hx.2⟩
                rw [hcent] at hxH
                rw [hCenterKs]
                exact hxH
              · intro hx
                have hxKs : x ∈ Ks := by
                  rw [← hCenterKs]
                  exact hx
                refine ⟨hx.1, ?_⟩
                intro y hy
                exact hKsCentK hxKs y (hRK hy)
            let J : Subgroup G := P ⊔ K
            let PJ : Subgroup J := P.subgroupOf J
            let KJ : Subgroup J := K.subgroupOf J
            have hdisPK : Disjoint P K :=
              Subgroup.disjoint_of_coprime_natCard (by
                rw [hPcard]
                exact hKcop.pow_left 3)
            have hPJnormal : PJ.Normal := by
              have hnormal :=
                Subgroup.normal_subgroupOf_sup_of_le_normalizer hKnormP
              rw [sup_comm] at hnormal
              simpa [PJ, J] using hnormal
            have hcompJK : PJ.IsComplement' KJ := by
              simpa [PJ, KJ, J] using
                subgroupOf_sup_isComplement15 hKnormP hdisPK
            have hcompTop :
                (PJ.subgroupOf (⊤ : Subgroup J)).IsComplement'
                  (KJ.subgroupOf (⊤ : Subgroup J)) := by
              apply Subgroup.isComplement'_of_card_mul_and_disjoint
              · simpa only [
                    Subgroup.card_top,
                    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
                      (show PJ ≤ (⊤ : Subgroup J) from le_top),
                    Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
                      (show KJ ≤ (⊤ : Subgroup J) from le_top)] using
                  hcompJK.card_mul
              · rw [disjoint_iff]
                apply le_antisymm _ bot_le
                intro x hx
                apply Subgroup.mem_bot.mpr
                apply Subtype.ext
                have hxbot : ((x : (⊤ : Subgroup J)) : J) ∈
                    (⊥ : Subgroup J) := by
                  rw [← disjoint_iff.mp hcompJK.disjoint]
                  exact hx
                exact Subgroup.mem_bot.mp hxbot
            have hsdJ : IsInternalSemidirectProductIn PJ KJ ⊤ :=
              ⟨le_top, le_top,
                Subgroup.Normal.subgroupOf hPJnormal (⊤ : Subgroup J),
                hcompTop⟩
            have hPJp : IsPGroup p PJ :=
              hPp.of_equiv
                (Subgroup.subgroupOfEquivOfLe
                  (show P ≤ J from le_sup_left)).symm
            have hPJcard : Nat.card PJ = p ^ 3 := by
              simpa [PJ,
                Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
                (show P ≤ J from le_sup_left)] using hPcard
            have hPJnoncomm : ¬ IsMulCommutative PJ := by
              intro hcomm
              apply hPnoncomm
              let ePJ : PJ ≃* P :=
                Subgroup.subgroupOfEquivOfLe
                  (show P ≤ J from le_sup_left)
              apply isMulCommutative_iff.mpr
              intro a b
              apply ePJ.symm.injective
              exact isMulCommutative_iff.mp hcomm
                (ePJ.symm a) (ePJ.symm b)
            have hPJextra : IsExtraspecial PJ :=
              isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
                hPJp hPJcard hPJnoncomm
            have hKJcyclic : IsCyclic KJ := by
              let eKJ : KJ ≃* K :=
                Subgroup.subgroupOfEquivOfLe
                  (show K ≤ J from le_sup_right)
              exact eKJ.isCyclic.mpr hKcyclic
            have hcentralJ : ∀ k : KJ, k ≠ 1 →
                centralizerWithin PJ (Subgroup.zpowers (k : J)) =
                  centerWithin PJ := by
              intro k hk
              have hkG : ((k : J) : G) ≠ 1 := by
                intro hkOne
                apply hk
                apply Subtype.ext
                apply Subtype.ext
                exact hkOne
              have hcentG := hAmbientCent k.property hkG
              apply Subgroup.map_injective J.subtype_injective
              change (centralizerWithin PJ (Subgroup.zpowers (k : J))).map
                    J.subtype =
                (centralizerWithin PJ PJ).map J.subtype
              rw [map_centralizerWithin_subgroupOf15
                    (show P ≤ J from le_sup_left),
                  map_centralizerWithin_subgroupOf15
                    (show P ≤ J from le_sup_left),
                  MonoidHom.map_zpowers,
                  Subgroup.map_subgroupOf_eq_of_le
                    (show P ≤ J from le_sup_left)]
              exact hcentG
            have hrepr :=
              Submission.OddOrder.BG.Section02.repr_extraspecial_prime_sdprod_cycle
                (p := p) (n := 1) PJ KJ hp hPJp hPJextra hsdJ
                  hKJcyclic hPJcard (by
                    simpa [KJ,
                      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
                      (show K ≤ J from le_sup_right)] using hKcop) hcentralJ
            have hreprG : Nat.card K ∣ p + 1 ∨
                Nat.card K ∣ p - 1 := by
              simpa [KJ, pow_one,
                Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
                (show K ≤ J from le_sup_right)] using hrepr
            right
            refine ⟨?_, hP₁, ?_⟩
            · calc
                Nat.card (pCore p H) = Nat.card P :=
                  (Subgroup.card_map_of_injective
                    H.subtype_injective).symm
                _ = p ^ 3 := hPcard
            · rw [hquotCard]
              exact hreprG.resolve_right hnotKpred
      exact
        { p_prime := by simpa [X, hXeq] using hp
          pcore_nonabelian := by simpa [H] using hpc
          pPrimeCore_cyclic := by simpa [H] using hp'cyc
          conclusion := by simpa [X, H, hXeq] using halt }

  exact
    { typeF_or_typeP1 := htype
      core_eq_sigma := by simpa [H] using hHsigma
      intersection_le_core := by simpa [X, H] using hXH
      intersection_cyclic := by simpa [X] using hXcyclic
      commutator_le_fitting := by
        simpa [derivedWithin] using hderivedFitting
      fitting_decomposition := hfitDecomp
      sigma_complement_structure := hCompl
      final_case := hfinal }

theorem nonTI_Fitting_facts
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hnonTI :
      ¬ IsNormalizedTI (subgroupNonidentity (fittingWithin M))
        (⊤ : Subgroup G) M) :
    M ∈ typeFMaximalSubgroups (G := G) ∨
      (M ∈ typeP1MaximalSubgroups (G := G) ∧
        Fitting_core M = sigmaCore M ∧
        derivedWithin M ≤ fittingWithin M) := by
  obtain ⟨g, hg, hmeet⟩ :=
    exists_nonTI_fitting_intersection hM hnonTI
  have hs := nonTI_Fitting_structure hM hg hmeet
  rcases hs.typeF_or_typeP1 with hF | hP1
  · exact Or.inl hF
  · exact Or.inr ⟨hP1, hs.core_eq_sigma,
      by simpa [derivedWithin] using hs.commutator_le_fitting⟩

end

end Submission.OddOrder.BG.Section15
