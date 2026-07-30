import Submission.OddOrder.BG.Section12.NonabelianUniqueness
import Submission.OddOrder.BG.Section01.CriticalOdd
import Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.BG.Section10.SigmaDisjointness
import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.MathlibSupport.ComplementQuotient
import Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension
import Submission.OddOrder.MathlibSupport.CrossPrimeHomKernel
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.NilpotentCentralizer
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal
import Submission.OddOrder.MathlibSupport.SolvableHallContainment
import Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport
import Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy
import Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer

/-!
# Bender--Glauberman Section 12: embedding sigma subgroups

This file ports the final block of `BGsection12.v`, lines 2203--2679:
Proposition 12.15, Corollary 12.16, and Lemmas 12.17--12.19.

Sylow predicates on ambiently represented subgroups use
`IsSylowSubgroupOf`.  Numerical rank at most one is rendered as exclusion of
an elementary-abelian rank-two subgroup, consistently with the earlier
Section 12 modules.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section06
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section08
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.MathlibSupport
open scoped Pointwise IsMulCommutative commutatorElement

noncomputable section

universe u

local instance decidablePropEmbedding (P : Prop) : Decidable P :=
  Classical.propDecidable P

private theorem IsSylowSubgroupOf.le_right
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {P K : Subgroup G}
    (hP : IsSylowSubgroupOf p P K) : P ≤ K := by
  rcases hP with ⟨S, rfl⟩
  exact Subgroup.map_subtype_le _

private theorem map_centralizerWithin_subgroupOf
    {G : Type u} [Group G]
    {J V A : Subgroup G} (hVJ : V ≤ J) (hAJ : A ≤ J) :
    (centralizerWithin (V.subgroupOf J) (A.subgroupOf J)).map
        J.subtype =
      centralizerWithin V A := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨hy.1, ?_⟩
    intro a ha
    let aJ : J := ⟨a, hAJ ha⟩
    exact congrArg Subtype.val (hy.2 aJ ha)
  · intro hx
    let xJ : J := ⟨x, hVJ hx.1⟩
    refine ⟨xJ, ?_, rfl⟩
    refine ⟨hx.1, ?_⟩
    intro a ha
    apply Subtype.ext
    exact hx.2 a ha

private theorem map_conj_map_conj_embedding
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_one_embedding
    {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem map_conj_inv_map_conj_embedding
    {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj_embedding]
  simpa only [inv_mul_cancel] using map_conj_one_embedding H

private theorem isHall_subgroupOf_map_mulEquiv_embedding
    {G : Type u} [Group G] [Finite G]
    {H L : Subgroup G} (hLH : L ≤ H)
    {pi : Set ℕ} (hL : IsHall pi (L.subgroupOf H))
    (e : G ≃* G) :
    IsHall pi
      ((L.map e.toMonoidHom).subgroupOf
        (H.map e.toMonoidHom)) := by
  let eH : H ≃* H.map e.toMonoidHom :=
    H.equivMapOfInjective e.toMonoidHom e.injective
  have hmap :
      (L.subgroupOf H).map eH.toMonoidHom =
        (L.map e.toMonoidHom).subgroupOf
          (H.map e.toMonoidHom) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change e (y : G) ∈ L.map e.toMonoidHom
      exact Subgroup.mem_map_equiv.mpr
        (by
          simpa only [e.symm_apply_apply] using
            (Subgroup.mem_subgroupOf.mp hy))
    · intro hx
      change (x : G) ∈ L.map e.toMonoidHom at hx
      have hx' := Subgroup.mem_map_equiv.mp hx
      let y : H := ⟨e.symm x, hLH hx'⟩
      refine ⟨y, hx', ?_⟩
      apply Subtype.ext
      exact e.apply_symm_apply (x : G)
  rw [← hmap]
  constructor
  · rw [Subgroup.card_map_of_injective eH.injective]
    exact hL.isPiNumber_card
  · have hindex :
        ((L.subgroupOf H).map eH.toMonoidHom).index =
          (L.subgroupOf H).index :=
      Subgroup.index_map_equiv (L.subgroupOf H) eH
    exact hindex.symm ▸ hL.isPiNumber_index

private theorem isHall_map_mulEquiv_embedding
    {G : Type u} {K : Type*} [Group G] [Group K]
    [Finite G] [Finite K] {pi : Set ℕ} {H : Subgroup G}
    (e : G ≃* K) (hH : IsHall pi H) :
    IsHall pi (H.map e.toMonoidHom) := by
  constructor
  · rw [Subgroup.card_map_of_injective e.injective]
    exact hH.isPiNumber_card
  · have hindex : (H.map e.toMonoidHom).index = H.index :=
      Subgroup.index_map_equiv H e
    exact hindex.symm ▸ hH.isPiNumber_index

private theorem subgroup_characteristic_of_isCyclic_embedding
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  obtain ⟨m, hm⟩ := e.toMonoidHom.map_cyclic
  rintro _ ⟨x, hx, rfl⟩
  rw [hm]
  exact H.zpow_mem hx m

private theorem characteristic_map_subtype_le_normalizer_embedding
    {G : Type*} [Group G] (E : Subgroup G)
    (R : Subgroup E) [R.Characteristic] :
    Subgroup.normalizer (E : Set G) ≤
      Subgroup.normalizer (R.map E.subtype : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro r
  constructor
  · intro hr
    exact characteristic_map_subtype_invariant_under_normalizer
      E (Subgroup.normalizer (E : Set G)) R le_rfl
      g hg r hr
  · intro hr
    have hginv : g⁻¹ ∈ Subgroup.normalizer (E : Set G) :=
      (Subgroup.normalizer (E : Set G)).inv_mem hg
    have h := characteristic_map_subtype_invariant_under_normalizer
      E (Subgroup.normalizer (E : Set G)) R le_rfl
      g⁻¹ hginv (g * r * g⁻¹) hr
    have hcancel : g⁻¹ * (g * r * g⁻¹) * (g⁻¹)⁻¹ = r := by
      group
    simpa only [hcancel] using h

private theorem isPiNumber_le_normal_isHall_embedding
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
  let q : K →* K ⧸ N := QuotientGroup.mk' N
  have horderL : orderOf (q x) ∣ Nat.card L :=
    (orderOf_map_dvd q x).trans (L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp horderOne)

private theorem piCore_isHall_of_isNilpotent_embedding
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    (pi : Set ℕ) : IsHall pi (piCore pi K) := by
  refine ⟨piCore_isPiNumber pi, ?_⟩
  intro p hp hpIndex hpPi
  letI : Fact p.Prime := ⟨hp⟩
  let P : Sylow p K := Classical.choice Sylow.nonempty
  have hPnormal : (P : Subgroup K).Normal := by infer_instance
  have hPle : (P : Subgroup K) ≤ piCore pi K :=
    le_piCore hPnormal
      (P.isPGroup'.isPiNumber_natCard hpPi)
  exact P.not_dvd_index
    (hpIndex.trans (Subgroup.index_dvd_of_le hPle))

private theorem nilpotent_subgroups_commute_of_coprime_pi
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {A B : Subgroup K}
    (hA : IsPiNumber pi (Nat.card A))
    (hB : IsPiNumber piᶜ (Nat.card B)) :
    A ≤ Subgroup.centralizer (B : Set K) := by
  let O : Subgroup K := piCore pi K
  let O' : Subgroup K := piCore piᶜ K
  have hAO : A ≤ O :=
    isPiNumber_le_normal_isHall_embedding
      (show O.Normal from inferInstance)
      (piCore_isHall_of_isNilpotent_embedding pi) hA
  have hBO' : B ≤ O' :=
    isPiNumber_le_normal_isHall_embedding
      (show O'.Normal from inferInstance)
      (piCore_isHall_of_isNilpotent_embedding piᶜ) hB
  have hdis : Disjoint O O' :=
    Subgroup.disjoint_of_coprime_natCard
      ((piCore_isPiNumber pi).coprime_compl
        (by simpa only [compl_compl] using
          (piCore_isPiNumber (G := K) piᶜ)))
  have hcomm := Subgroup.commute_of_normal_of_disjoint
    O O' (by infer_instance) (by infer_instance) hdis
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  exact (hcomm a b (hAO ha) (hBO' hb)).eq.symm

private theorem exists_sylow_eq_map_of_sylow_hall_embedding
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

/-- Intersecting a Hall subgroup with a normal subgroup gives a Hall
subgroup of the normal subgroup. -/
private theorem isHall_inf_normal_embedding
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
      exists_sylow_eq_map_of_sylow_hall_embedding
        hp hH hpPi PH
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

private theorem exists_rank_one_le_of_ne_bot
    {G : Type u} [Group G] [Finite G] {R : Subgroup G}
    (hR : R ≠ ⊥) :
    ∃ p : ℕ, p.Prime ∧ ∃ X : Subgroup G,
      X ≤ R ∧ IsElementaryAbelianOfRank p 1 X := by
  have hcard : 1 < Nat.card R := R.one_lt_card_iff_ne_bot.mpr hR
  obtain ⟨p, hp, hpR⟩ := Nat.exists_prime_and_dvd
    (by omega : Nat.card R ≠ 1)
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := R) p hpR
  let X₀ : Subgroup R := Subgroup.zpowers x
  have hX₀card : Nat.card X₀ = p := by
    simp [X₀, Nat.card_zpowers, hxorder]
  let X : Subgroup G := X₀.map R.subtype
  refine ⟨p, hp, X, Subgroup.map_subtype_le _, ?_⟩
  have hXcard : Nat.card X = p := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hX₀card]
  exact isElementaryAbelianOfRank_one_of_card_eq_prime hXcard

private theorem exists_rank_one_le_of_prime_dvd
    {G : Type u} [Group G] [Finite G] {R : Subgroup G}
    {p : ℕ} (hp : p.Prime) (hpR : p ∣ Nat.card R) :
    ∃ X : Subgroup G, X ≤ R ∧
      IsElementaryAbelianOfRank p 1 X := by
  letI : Fact p.Prime := ⟨hp⟩
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := R) p hpR
  let X₀ : Subgroup R := Subgroup.zpowers x
  have hX₀card : Nat.card X₀ = p := by
    simp [X₀, Nat.card_zpowers, hxorder]
  let X : Subgroup G := X₀.map R.subtype
  refine ⟨X, Subgroup.map_subtype_le _, ?_⟩
  have hXcard : Nat.card X = p := by
    rw [Subgroup.card_map_of_injective R.subtype_injective, hX₀card]
  exact isElementaryAbelianOfRank_one_of_card_eq_prime hXcard

/-- Ambient carrier form of a product decomposition by a subgroup normal
in the indicated ambient subgroup. -/
private theorem carrier_mul_eq_of_sup_eq
    {G : Type u} [Group G]
    {A B K : Subgroup G} (hAK : A ≤ K) (hBK : B ≤ K)
    (hA : (A.subgroupOf K).Normal) (hsup : A ⊔ B = K) :
    (A : Set G) * (B : Set G) = (K : Set G) := by
  let AK : Subgroup K := A.subgroupOf K
  let BK : Subgroup K := B.subgroupOf K
  letI : AK.Normal := by simpa [AK] using hA
  have hsupK : AK ⊔ BK = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hAK,
      Subgroup.map_subgroupOf_eq_of_le hBK,
      hsup, ← MonoidHom.range_eq_map, K.range_subtype]
  ext x
  constructor
  · rintro ⟨a, ha, b, hb, rfl⟩
    exact K.mul_mem (hAK ha) (hBK hb)
  · intro hx
    let xK : K := ⟨x, hx⟩
    have hxMul : xK ∈ (AK : Set K) * (BK : Set K) := by
      rw [← Subgroup.normal_mul AK BK, hsupK]
      trivial
    rcases hxMul with ⟨a, ha, b, hb, hab⟩
    refine ⟨(a : G), ha, (b : G), hb, ?_⟩
    exact congrArg Subtype.val hab

private theorem sup_eq_of_carrier_mul_eq
    {G : Type u} [Group G] {A B K : Subgroup G}
    (hAK : A ≤ K) (hBK : B ≤ K)
    (hmul : (A : Set G) * (B : Set G) = (K : Set G)) :
    A ⊔ B = K := by
  apply le_antisymm (sup_le hAK hBK)
  intro x hx
  have hxmul : x ∈ (A : Set G) * (B : Set G) := by
    rw [hmul]
    exact hx
  rcases hxmul with ⟨a, ha, b, hb, rfl⟩
  exact Subgroup.mul_mem_sup ha hb

/-- If a normal subgroup and `I` generate a finite group, then the index
of `I` divides the order of the normal factor.  This is the numerical form
of the second isomorphism theorem used in the two `p`-product arguments
below. -/
private theorem index_dvd_card_of_sup_eq_top_normal_left
    {K : Type u} [Group K] [Finite K]
    {N I : Subgroup K} (hN : N.Normal) (hsup : N ⊔ I = ⊤) :
    I.index ∣ Nat.card N := by
  letI : N.Normal := hN
  let J : Subgroup I := (N ⊓ I).subgroupOf I
  have hNindex : N.index = J.index := by
    calc
      N.index = N.relIndex (⊤ : Subgroup K) := N.relIndex_top_right.symm
      _ = N.relIndex (I ⊔ N) := by rw [sup_comm, hsup]
      _ = N.relIndex I := Subgroup.relIndex_sup_right I N
      _ = (N ⊓ I).relIndex I :=
        (Subgroup.inf_relIndex_right N I).symm
      _ = J.index := by rfl
  have hNcard : Nat.card N * J.index = Nat.card K := by
    rw [← hNindex]
    exact N.card_mul_index
  have hIcard : Nat.card I * I.index = Nat.card K :=
    I.card_mul_index
  have hJcard : Nat.card J * J.index = Nat.card I :=
    J.card_mul_index
  have hcancel :
      Nat.card N * J.index =
        (Nat.card J * I.index) * J.index := by
    calc
      Nat.card N * J.index = Nat.card K := hNcard
      _ = Nat.card I * I.index := hIcard.symm
      _ = (Nat.card J * J.index) * I.index := by rw [hJcard]
      _ = (Nat.card J * I.index) * J.index := by ac_rfl
  have hcard : Nat.card N = Nat.card J * I.index :=
    Nat.mul_right_cancel
      (Nat.pos_of_ne_zero J.index_ne_zero_of_finite) hcancel
  exact ⟨Nat.card J, by simpa [mul_comm] using hcard⟩

/-- A Sylow subgroup of the second factor in a normal product is still
Sylow in the whole group at every prime absent from the normal factor. -/
private theorem isSylowSubgroupOf_map_of_normal_sup
    {G : Type u} [Group G] [Finite G]
    {H N I : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hNH : N ≤ H) (hIH : I ≤ H)
    (hNnormal : (N.subgroupOf H).Normal)
    (hsup : N ⊔ I = H)
    {pi : Set ℕ} (hNpi : IsPiNumber pi (Nat.card N))
    (hpPi : p ∉ pi) (R : Sylow p I) :
    IsSylowSubgroupOf p
      ((R : Subgroup I).map I.subtype) H := by
  let NH : Subgroup H := N.subgroupOf H
  let IH : Subgroup H := I.subgroupOf H
  let Q : Subgroup G := (R : Subgroup I).map I.subtype
  have hQI : Q ≤ I := by
    simpa [Q] using Subgroup.map_subtype_le (R : Subgroup I)
  have hQH : Q ≤ H := hQI.trans hIH
  have hsupH : NH ⊔ IH = ⊤ := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hNH,
      Subgroup.map_subgroupOf_eq_of_le hIH,
      hsup, ← MonoidHom.range_eq_map, H.range_subtype]
  have hNHpi : IsPiNumber pi (Nat.card NH) := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hNH]
    exact hNpi
  have hpNH : ¬ p ∣ Nat.card NH := by
    intro hpCard
    exact hpPi (hNHpi Fact.out hpCard)
  have hpIHindex : ¬ p ∣ IH.index := by
    exact fun hpIndex ↦ hpNH
      (hpIndex.trans
        (index_dvd_card_of_sup_eq_top_normal_left
          hNnormal hsupH))
  let QH : Subgroup H := Q.subgroupOf H
  let QI : Subgroup I := Q.subgroupOf I
  have hQIeq : QI = (R : Subgroup I) := by
    dsimp [QI, Q]
    exact Subgroup.comap_map_eq_self_of_injective
      I.subtype_injective R
  have hQHp : IsPGroup p QH := by
    exact (R.isPGroup'.map I.subtype).of_equiv
      (Subgroup.subgroupOfEquivOfLe hQH).symm
  have hpQHindex : ¬ p ∣ QH.index := by
    have hfactor : QH.index = QI.index * IH.index := by
      change Q.relIndex H = Q.relIndex I * I.relIndex H
      exact (Q.relIndex_mul_relIndex I H hQI hIH).symm
    rw [hfactor, hQIeq]
    exact (Fact.out : p.Prime).not_dvd_mul
      R.not_dvd_index hpIHindex
  let P : Sylow p H := hQHp.toSylow hpQHindex
  refine ⟨P, ?_⟩
  change Q = QH.map H.subtype
  exact (Subgroup.map_subgroupOf_eq_of_le hQH).symm

/-- Promote a Hall subgroup through a product with a normal subgroup whose
prime support is complementary. -/
private theorem isHall_of_normal_complement_sup
    {G : Type u} [Group G] [Finite G]
    {L N I A : Subgroup G} {pi : Set ℕ}
    (hNL : N ≤ L) (hIL : I ≤ L) (hAI : A ≤ I)
    (hNnormal : (N.subgroupOf L).Normal)
    (hsup : N ⊔ I = L)
    (hNcompl : IsPiNumber piᶜ (Nat.card N))
    (hAHall : IsHall pi (A.subgroupOf I)) :
    IsHall pi (A.subgroupOf L) := by
  let NL : Subgroup L := N.subgroupOf L
  let IL : Subgroup L := I.subgroupOf L
  have hsupL : NL ⊔ IL = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup,
      Subgroup.map_subgroupOf_eq_of_le hNL,
      Subgroup.map_subgroupOf_eq_of_le hIL,
      hsup, ← MonoidHom.range_eq_map, L.range_subtype]
  have hILindexCompl : IsPiNumber piᶜ IL.index := by
    have hdvd := index_dvd_card_of_sup_eq_top_normal_left
      hNnormal hsupL
    have hNLcompl : IsPiNumber piᶜ (Nat.card NL) := by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hNL]
      exact hNcompl
    exact hNLcompl.of_dvd hdvd
  constructor
  · rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq (hAI.trans hIL)]
    have hcard := hAHall.isPiNumber_card
    rwa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hAI] at hcard
  · change IsPiNumber piᶜ (A.relIndex L)
    rw [← A.relIndex_mul_relIndex I L hAI hIL]
    exact hAHall.isPiNumber_index.mul hILindexCompl

/-- Elementary-abelian rank is the same in two ambient subgroups which
share an ambiently represented Sylow subgroup. -/
private theorem elementaryAbelianRankAtLeast_iff_of_common_sylow
    {G : Type u} [Group G] [Finite G]
    {H K Q : Subgroup G} {p n : ℕ} [Fact p.Prime]
    (hQH : IsSylowSubgroupOf p Q H)
    (hQK : IsSylowSubgroupOf p Q K) :
    HasElementaryAbelianRankAtLeast p n H ↔
      HasElementaryAbelianRankAtLeast p n K := by
  classical
  have forward : ∀ {L R : Subgroup G},
      IsSylowSubgroupOf p Q L →
      IsSylowSubgroupOf p Q R →
      HasElementaryAbelianRankAtLeast p n L →
      HasElementaryAbelianRankAtLeast p n R := by
    intro L R hQL hQR hRank
    rcases hQL with ⟨PL, hQPL⟩
    rcases hRank with ⟨A, hAL, hA⟩
    let AL : Subgroup L := A.subgroupOf L
    have hALrank : IsElementaryAbelianOfRank p n AL :=
      hA.subgroupOf hAL
    obtain ⟨T, hALT⟩ := hALrank.isPGroup.exists_le_sylow
    obtain ⟨l, hl⟩ := MulAction.exists_smul_eq L T PL
    let C : Subgroup L :=
      AL.map (MulAut.conj l).toMonoidHom
    have hTC :
        (T : Subgroup L).map (MulAut.conj l).toMonoidHom =
          (PL : Subgroup L) := by
      change MulAut.conj l • (T : Subgroup L) = (PL : Subgroup L)
      rw [← Sylow.coe_subgroup_smul, hl]
    have hCPL : C ≤ (PL : Subgroup L) :=
      (Subgroup.map_mono hALT).trans_eq hTC
    have hC : IsElementaryAbelianOfRank p n C :=
      hALrank.map_of_injective (MulAut.conj l).toMonoidHom
        (MulAut.conj l).injective
    let CG : Subgroup G := C.map L.subtype
    have hCGQ : CG ≤ Q := by
      dsimp [CG]
      rw [hQPL]
      exact Subgroup.map_mono hCPL
    exact ⟨CG, hCGQ.trans (IsSylowSubgroupOf.le_right hQR),
      hC.map_of_injective L.subtype L.subtype_injective⟩
  exact ⟨forward hQH hQK, forward hQK hQH⟩

/-- Choose a rank witness inside an ambiently represented Sylow
subgroup. -/
private theorem exists_elementaryAbelian_le_ambientSylow
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

/-- `BGsection12.v: sigma_subgroup_embedding`, Proposition 12.15. -/
theorem sigma_subgroup_embedding
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M H X : Subgroup G} {q : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hqM : q ∈ sigmaPrimes M)
    (hXM : X ≤ M) (hXq : IsPGroup q X) (hXne : X ≠ ⊥)
    (hHNX : H ∈ minSimple_max_groups_of (G := G)
      (Subgroup.normalizer (X : Set G) : Set G))
    (hne : H ≠ M) :
    (∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom) ∧
      ∀ S : Sylow q ↥(M ⊓ H),
        X ≤ ambientSylow (M ⊓ H) S →
        Subgroup.normalizer
            (ambientSylow (M ⊓ H) S : Set G) ≤ M ∧
          IsSylowSubgroupOf q (ambientSylow (M ⊓ H) S) H ∧
          if q ∈ sigmaPrimes H then
            (betaCore H : Set G) * ((M ⊓ H : Subgroup G) : Set G) =
                (H : Set G) ∧
              tau1Primes H ⊆ tau1Primes M ∪ alphaPrimes M ∧
              betaCore M = alphaCore M ∧ alphaCore M ≠ ⊥
          else
            q ∈ tau2Primes H ∧
              primeSupport (Nat.card M) ∩ sigmaPrimes H ⊆
                betaPrimes H ∧
              IsHall (sigmaPrimes H)ᶜ
                ((M ⊓ H).subgroupOf H) := by
  classical
  letI : Fact q.Prime := ⟨hqM.1⟩
  have hH : H ∈ minSimple_max_groups (G := G) := hHNX.1
  have hNXH : Subgroup.normalizer (X : Set G) ≤ H := hHNX.2
  have hXH : X ≤ H := Subgroup.le_normalizer.trans hNXH
  have hnotconj :
      ∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom :=
    mmax_norm_notJ hM hH hXq hXM hNXH
      (Or.inl ⟨hqM, hne.symm⟩)
  refine ⟨hnotconj, ?_⟩
  intro S hXS
  let I : Subgroup G := M ⊓ H
  let Q : Subgroup G := ambientSylow I S
  have hQq : IsPGroup q Q := by
    dsimp [Q, ambientSylow]
    exact S.isPGroup'.map I.subtype
  have hQI : Q ≤ I := by
    simpa [Q, I, ambientSylow] using
      Subgroup.map_subtype_le (S : Subgroup ↥(M ⊓ H))
  have hQM : Q ≤ M := hQI.trans inf_le_left
  have hQH : Q ≤ H := hQI.trans inf_le_right
  have hNQM : Subgroup.normalizer (Q : Set G) ≤ M := by
    by_cases hQcyc : IsCyclic Q
    · letI : IsCyclic Q := hQcyc
      let XQ : Subgroup Q := X.subgroupOf Q
      have hXQchar : XQ.Characteristic :=
        subgroup_characteristic_of_isCyclic_embedding XQ
      letI : XQ.Characteristic := hXQchar
      have hNQNX :
          Subgroup.normalizer (Q : Set G) ≤
            Subgroup.normalizer (X : Set G) := by
        have hchar :=
          characteristic_map_subtype_le_normalizer_embedding Q XQ
        have hmap : XQ.map Q.subtype = X :=
          Subgroup.map_subgroupOf_eq_of_le hXS
        simpa [hmap] using hchar
      have hNQH : Subgroup.normalizer (Q : Set G) ≤ H :=
        hNQNX.trans hNXH
      obtain ⟨PM, hPM⟩ :=
        exists_sylow_map_eq_of_sylow_inf_of_normalizer_le
          M H S hNQH
      have hnorm := norm_sigma_Sylow hqM PM
      simpa [Q, I, ambientSylow, hPM] using hnorm
    · exact norm_noncyclic_sigma hM hqM hQq hQM hQcyc
  let eI : ↥(M ⊓ H) ≃* ↥(H ⊓ M) :=
    MulEquiv.subgroupCongr (inf_comm M H)
  let S' : Sylow q ↥(H ⊓ M) :=
    S.mapSurjective (f := eI.toMonoidHom) eI.surjective
  have hSambient :
      (S' : Subgroup ↥(H ⊓ M)).map (H ⊓ M).subtype = Q := by
    dsimp [S', eI, Q, I, ambientSylow]
    rw [Subgroup.map_map]
    congr 1
  obtain ⟨PH, hPH⟩ :=
    exists_sylow_map_eq_of_sylow_inf_of_normalizer_le
      H M S' (by simpa [hSambient] using hNQM)
  have hQsylH : IsSylowSubgroupOf q Q H := by
    refine ⟨PH, ?_⟩
    exact (hPH.trans hSambient).symm
  have hclass := prime_class_mmax_norm hH hXq hNXH
  refine ⟨hNQM, hQsylH, ?_⟩
  by_cases hqH : q ∈ sigmaPrimes H
  · simp only [if_pos hqH]
    obtain ⟨SG, hSG⟩ := sigma_Sylow_G hH hqH PH
    have hSGQ : (SG : Subgroup G) = Q := by
      calc
        (SG : Subgroup G) = ambientSylow H PH := hSG
        _ = Q := hPH.trans hSambient
    have hNQH : Subgroup.normalizer (Q : Set G) ≤ H := by
      have hnorm := norm_sigma_Sylow hqH PH
      have hPHQ : ambientSylow H PH = Q := hPH.trans hSambient
      simpa [hPHQ] using hnorm
    have hNSG :
        Subgroup.normalizer ((SG : Subgroup G) : Set G) ≤ H ⊓ M := by
      simpa [hSGQ] using le_inf hNQH hNQM
    obtain ⟨hdefM, habM⟩ :=
      nonuniq_norm_Sylow_pprod hM hH hne SG hNSG
    have hNSG' :
        Subgroup.normalizer ((SG : Subgroup G) : Set G) ≤ M ⊓ H := by
      simpa [inf_comm] using hNSG
    obtain ⟨hdefH, habH⟩ :=
      nonuniq_norm_Sylow_pprod hH hM hne.symm SG hNSG'
    have hprodH :
        (betaCore H : Set G) * ((M ⊓ H : Subgroup G) : Set G) =
          (H : Set G) :=
      carrier_mul_eq_of_sup_eq (betaCore_le H) inf_le_right
        (betaCore_normal H) hdefH
    have hbetaAlphaM : betaCore M = alphaCore M := by
      simp only [betaCore, alphaCore]
      rw [habM]
    have hAlphaNe : alphaCore M ≠ ⊥ := by
      intro hAlpha
      have hBeta : betaCore M = ⊥ := hbetaAlphaM.trans hAlpha
      have hInf : H ⊓ M = M := by
        simpa [hBeta] using hdefM
      have hMH : M ≤ H := by
        rw [← hInf]
        exact inf_le_left
      exact hne (eq_mmax hM hH hMH).symm
    have hTau1 : tau1Primes H ⊆
        tau1Primes M ∪ alphaPrimes M := by
      intro r hrH
      by_cases hrAlpha : r ∈ alphaPrimes M
      · exact Or.inr hrAlpha
      letI : Fact r.Prime := ⟨hrH.1⟩
      let R : Sylow r I := Classical.choice Sylow.nonempty
      let Rg : Subgroup G := (R : Subgroup I).map I.subtype
      have hrBetaH : r ∉ betaPrimes H := by
        intro hr
        exact hrH.2.1 (beta_sub_sigma hH hr)
      have hrBetaM : r ∉ betaPrimes M := by
        intro hr
        exact hrAlpha ((beta_sub_alpha M) hr)
      have hRsylH : IsSylowSubgroupOf r Rg H := by
        apply isSylowSubgroupOf_map_of_normal_sup
          (N := betaCore H) (I := I)
          (betaCore_le H) inf_le_right (betaCore_normal H) hdefH
          (betaCore_isPiNumber H) hrBetaH R
      have hRsylM : IsSylowSubgroupOf r Rg M := by
        apply isSylowSubgroupOf_map_of_normal_sup
          (N := betaCore M) (I := I)
          (betaCore_le M) inf_le_left (betaCore_normal M)
          (by simpa [I, inf_comm] using hdefM)
          (betaCore_isPiNumber M) hrBetaM R
      have hRankIff :
          HasElementaryAbelianRankAtLeast r 1 H ↔
            HasElementaryAbelianRankAtLeast r 1 M :=
        elementaryAbelianRankAtLeast_iff_of_common_sylow
          hRsylH hRsylM
      have hRankTwoIff :
          HasElementaryAbelianRankAtLeast r 2 H ↔
            HasElementaryAbelianRankAtLeast r 2 M :=
        elementaryAbelianRankAtLeast_iff_of_common_sylow
          hRsylH hRsylM
      have hrDerM : ¬ r ∣ Nat.card (_root_.commutator M) := by
        have hRgM : Rg ≤ M := IsSylowSubgroupOf.le_right hRsylM
        rcases hRsylM with ⟨RM, hRM⟩
        rcases hRsylH with ⟨RH, hRH⟩
        let BM : Subgroup M := (betaCore M).subgroupOf M
        let IM : Subgroup M := I.subgroupOf M
        let QM : Subgroup M := Rg.subgroupOf M
        have hBMnormal : BM.Normal := by
          simpa [BM] using betaCore_normal M
        letI : BM.Normal := hBMnormal
        have hsupM : BM ⊔ IM = ⊤ := by
          apply Subgroup.map_injective M.subtype_injective
          rw [Subgroup.map_sup,
            Subgroup.map_subgroupOf_eq_of_le (betaCore_le M),
            Subgroup.map_subgroupOf_eq_of_le inf_le_left,
            show betaCore M ⊔ I = M by simpa [I, inf_comm] using hdefM,
            ← MonoidHom.range_eq_map, M.range_subtype]
        have hQMIM : QM ≤ IM := by
          intro x hx
          change (x : G) ∈ I
          change (x : G) ∈ Rg at hx
          exact Subgroup.map_subtype_le R hx
        have hBMpi :
            IsPiNumber (betaPrimes M) (Nat.card BM) := by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq (betaCore_le M)]
          exact betaCore_isPiNumber M
        have hQMpi :
            IsPiNumber (betaPrimes M)ᶜ (Nat.card QM) := by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
            hRgM]
          exact R.isPGroup'.map I.subtype |>.isPiNumber_natCard hrBetaM
        have hcop : (Nat.card BM).Coprime (Nat.card QM) :=
          hBMpi.coprime_compl hQMpi
        have hfocal :
            QM ⊓ _root_.commutator M = QM ⊓ ⁅IM, IM⁆ :=
          Section06.pprod_focal_coprime hsupM hQMIM hcop
        intro hrMder
        have hQM_eq : QM = (RM : Subgroup M) := by
          apply Subgroup.map_injective M.subtype_injective
          rw [Subgroup.map_subgroupOf_eq_of_le hRgM]
          exact hRM
        let Z : Sylow r (_root_.commutator M) :=
          normalIntersectionSylow RM (_root_.commutator M)
        have hZne : (Z : Subgroup (_root_.commutator M)) ≠ ⊥ :=
          Z.ne_bot_of_dvd_card hrMder
        have hleftNe :
            QM ⊓ _root_.commutator M ≠ ⊥ := by
          intro hbot
          have hmapZ := map_normalIntersectionSylow_eq_inf
            RM (_root_.commutator M)
          have hmapBot :
              (Z : Subgroup (_root_.commutator M)).map
                  (_root_.commutator M).subtype = ⊥ := by
            calc
              (Z : Subgroup (_root_.commutator M)).map
                    (_root_.commutator M).subtype =
                  (RM : Subgroup M) ⊓ _root_.commutator M := by
                simpa [Z] using hmapZ
              _ = QM ⊓ _root_.commutator M := by rw [hQM_eq]
              _ = ⊥ := hbot
          exact hZne ((Subgroup.map_eq_bot_iff_of_injective
            (Z : Subgroup (_root_.commutator M))
            (_root_.commutator M).subtype_injective).mp hmapBot)
        have hrightNe : QM ⊓ ⁅IM, IM⁆ ≠ ⊥ := by
          rwa [← hfocal]
        let W : Subgroup G :=
          (QM ⊓ ⁅IM, IM⁆).map M.subtype
        have hWne : W ≠ ⊥ := by
          intro hW
          exact hrightNe ((Subgroup.map_eq_bot_iff_of_injective
            (QM ⊓ ⁅IM, IM⁆) M.subtype_injective).mp hW)
        have hWr : IsPGroup r W := by
          apply (RM.isPGroup'.map M.subtype).to_le
          dsimp [W]
          exact Subgroup.map_mono (inf_le_left.trans_eq hQM_eq)
        have hrW : r ∣ Nat.card W :=
          hWr.card_eq_or_dvd.resolve_left
            (fun hc ↦ hWne (Subgroup.card_eq_one.mp hc))
        have hWHder : W ≤
            (_root_.commutator H).map H.subtype := by
          dsimp [W]
          calc
            (QM ⊓ ⁅IM, IM⁆).map M.subtype ≤
                ⁅IM, IM⁆.map M.subtype :=
              Subgroup.map_mono inf_le_right
            _ = ⁅IM.map M.subtype, IM.map M.subtype⁆ :=
              Subgroup.map_commutator _ _ M.subtype
            _ = ⁅I, I⁆ := by
              rw [Subgroup.map_subgroupOf_eq_of_le inf_le_left]
            _ ≤ ⁅H, H⁆ :=
              Subgroup.commutator_mono inf_le_right inf_le_right
            _ = (_root_.commutator H).map H.subtype :=
              H.map_subtype_commutator.symm
        apply hrH.2.2.2.2
        rw [← Subgroup.card_map_of_injective H.subtype_injective]
        exact hrW.trans (Subgroup.card_dvd_of_le hWHder)
      have hrNotSigmaM : r ∉ sigmaPrimes M := by
        intro hrSigma
        obtain ⟨A, hARg, hA⟩ :=
          exists_elementaryAbelian_le_ambientSylow
            hRsylH hrH.2.2.1
        have hRgSigma : Rg ≤ sigmaCore M := by
          have hRgM : Rg ≤ M := IsSylowSubgroupOf.le_right hRsylM
          have hle : Rg.subgroupOf M ≤
              (sigmaCore M).subgroupOf M := by
            apply isPiNumber_le_normal_isHall_embedding
              (by simpa using sigmaCore_normal M) (Msigma_Hall hM)
            rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hRgM]
            exact R.isPGroup'.map I.subtype |>.isPiNumber_natCard hrSigma
          intro x hx
          exact hle (show (⟨x, hRgM hx⟩ : M) ∈ Rg.subgroupOf M from hx)
        have hADer : A ≤ (_root_.commutator M).map M.subtype :=
          hARg.trans (hRgSigma.trans (Msigma_der1 hM))
        have hrA : r ∣ Nat.card A := by
          rw [hA.card_eq]
          exact dvd_pow_self r (by omega)
        apply hrDerM
        rw [← Subgroup.card_map_of_injective M.subtype_injective]
        exact hrA.trans (Subgroup.card_dvd_of_le hADer)
      exact Or.inl
        ⟨hrH.1, hrNotSigmaM, hRankIff.mp hrH.2.2.1,
          fun h ↦ hrH.2.2.2.1 (hRankTwoIff.mpr h), hrDerM⟩
    exact ⟨hprodH, hTau1, hbetaAlphaM, hAlphaNe⟩
  · simp only [if_neg hqH]
    have hqTau : q ∈ tau2Primes H := hclass.resolve_left hqH
    obtain ⟨A, hAQ, hA⟩ :=
      exists_elementaryAbelian_le_ambientSylow
        hQsylH hqTau.2.2.1
    have hAH : A ≤ H := hAQ.trans hQH
    have hAM : A ≤ M := hAQ.trans hQM
    have hApi : IsPiNumber (sigmaPrimes H)ᶜ (Nat.card A) :=
      hA.isPGroup.isPiNumber_natCard hqH
    obtain ⟨F, hAF, hFH, hHallF⟩ :=
      exists_ambient_isHall_ge_of_isSolvable
        hAH (mmax_sol hH) (sigmaPrimes H)ᶜ hApi
    have hcomplCtx :=
      tau2_compl_context hH hFH hHallF hqTau hAF hA
    have hNA_M : Subgroup.normalizer (A : Set G) ≤ M :=
      norm_noncyclic_sigma hM hqM hA.isPGroup hAM
        (hA.not_isCyclic hqM.1)
    have hFM : F ≤ M := by
      have hFNA : F ≤ Subgroup.normalizer (A : Set G) := by
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer hAF).mp
          hcomplCtx.A_normal
      exact hFNA.trans hNA_M
    have hFI : F ≤ I := le_inf hFM hFH
    have hSigmaInf : sigmaCore H ⊓ M = ⊥ := by
      have hctx := tau2_context hH hqTau hAH hA
      exact hctx.maximal_intersection_eq_bot ⟨hM, hAM⟩ hne.symm
    have hIF : I ≤ F := by
      have hsd := sdprod_sigma hH hFH hHallF
      change sigmaCore H ≤ H ∧ F ≤ H ∧
          ((sigmaCore H).subgroupOf H).Normal ∧
          ((sigmaCore H).subgroupOf H).IsComplement'
            (F.subgroupOf H) at hsd
      intro x hxI
      let xH : H := ⟨x, hxI.2⟩
      obtain ⟨sf, hsf⟩ := hsd.2.2.2.2 xH
      let s := sf.1
      let f := sf.2
      have hval : (s : G) * (f : G) = x :=
        congrArg Subtype.val hsf
      have hsM : (s : G) ∈ M := by
        have hfxM : (f : G) ∈ M := hFM f.property
        rw [← hval] at hxI
        simpa using
          M.mul_mem hxI.1 (M.inv_mem hfxM)
      have hsBot : (s : G) ∈ (⊥ : Subgroup G) := by
        rw [← hSigmaInf]
        exact ⟨s.property, hsM⟩
      have hsOne : s = 1 := by
        apply Subtype.ext
        simpa using hsBot
      have hxF : x = (f : G) := by
        simpa [hsOne] using hval.symm
      rw [hxF]
      exact f.property
    have hIFeq : I = F := le_antisymm hIF hFI
    have hHallI : IsHall (sigmaPrimes H)ᶜ (I.subgroupOf H) := by
      simpa [hIFeq] using hHallF
    have hPrimeIncl :
        primeSupport (Nat.card M) ∩ sigmaPrimes H ⊆
          betaPrimes H := by
      intro r hr
      by_contra hrBeta
      letI : Fact r.Prime := ⟨hr.1.1⟩
      have hrSigmaH : r ∈ sigmaPrimes H := hr.2
      have hrNotBetaH : r ∉ betaPrimes H := hrBeta
      have hqNotBetaH : q ∉ betaPrimes H := by
        intro hqBeta
        exact hqH (beta_sub_sigma hH hqBeta)
      have hnotconjSymm :
          ∀ g : G, M ≠ H.map (MulAut.conj g).toMonoidHom := by
        intro g hEq
        apply hnotconj g⁻¹
        have hmapped := congrArg
          (fun K : Subgroup G ↦
            K.map (MulAut.conj g⁻¹).toMonoidHom) hEq
        rw [map_conj_inv_map_conj_embedding] at hmapped
        exact hmapped.symm
      have hdis : Disjoint (sigmaPrimes H) (sigmaPrimes M) :=
        hcomplCtx.disjoint_sigma_of_nonconj hM hnotconjSymm |>.2
      have hrNotSigmaM : r ∉ sigmaPrimes M :=
        fun hrM ↦ Set.disjoint_left.mp hdis hrSigmaH hrM
      have hrNotBetaM : r ∉ betaPrimes M :=
        fun hrM ↦ hrNotSigmaM (beta_sub_sigma hM hrM)
      have hqNotBetaG : q ∉ betaPrimes (⊤ : Subgroup G) :=
        (tau2_not_beta hH hqTau).1
      have hqNotBetaM : q ∉ betaPrimes M := by
        intro hqBetaM
        have hpair : q ∈
            sigmaPrimes M ∩ betaPrimes (⊤ : Subgroup G) := by
          rw [predI_sigma_beta hM]
          exact hqBetaM
        exact hqNotBetaG hpair.2
      have hCAF : Subgroup.centralizer (A : Set G) ≤ F :=
        hcomplCtx.centralizer_le_E
      have hCAr' :
          IsPiNumber ({r} : Set ℕ)ᶜ
            (Nat.card (Subgroup.centralizer (A : Set G))) := by
        have hFpi :
            IsPiNumber (sigmaPrimes H)ᶜ (Nat.card F) := by
          rw [← Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hFH]
          exact hHallF.isPiNumber_card
        intro t ht htC htEq
        subst t
        exact hFpi ht
          (htC.trans (Subgroup.card_dvd_of_le hCAF)) hrSigmaH
      rcases lt_trichotomy r q with hrq | heq | hqr
      · let AH : Subgroup H := A.subgroupOf H
        have hAHq : IsPGroup q AH :=
          hA.isPGroup.of_equiv
            (Subgroup.subgroupOfEquivOfLe hAH).symm
        have hcent := (beta'_cent_Sylow hH hrNotBetaH hqNotBetaH
          (X := AH) hAHq
          (Or.inr hrq)).1
        obtain ⟨P, hAP⟩ := hcent
        let PG : Subgroup G :=
          ((P : Subgroup ((sigmaCore H).subgroupOf H)).map
            ((sigmaCore H).subgroupOf H).subtype).map H.subtype
        have hPGcent : PG ≤ Subgroup.centralizer (A : Set G) := by
          intro x hx
          rcases hx with ⟨y, hy, rfl⟩
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          have haAH : (⟨a, hAH ha⟩ : H) ∈ AH :=
            Subgroup.mem_subgroupOf.mpr ha
          have hcomm := Subgroup.mem_centralizer_iff.mp
            (hAP haAH) y hy
          exact (congrArg Subtype.val hcomm).symm
        have hrPG : r ∣ Nat.card PG := by
          dsimp [PG]
          rw [Subgroup.card_map_of_injective H.subtype_injective,
            Subgroup.card_map_of_injective
              ((sigmaCore H).subgroupOf H).subtype_injective]
          let SH : Subgroup H := (sigmaCore H).subgroupOf H
          have hrHcard : r ∣ Nat.card H :=
            (sigma_sub_primeSupport hH hrSigmaH).2
          have hrProd : r ∣ Nat.card SH * SH.index := by
            rw [SH.card_mul_index]
            exact hrHcard
          have hrIndex : ¬ r ∣ SH.index := by
            intro hrIdx
            exact (Msigma_Hall hH).isPiNumber_index
              hrSigmaH.1 hrIdx hrSigmaH
          have hrSH : r ∣ Nat.card SH :=
            (hrSigmaH.1.dvd_mul.mp hrProd).resolve_right hrIndex
          exact P.isPGroup'.card_eq_or_dvd.resolve_left
            (fun hc ↦ P.ne_bot_of_dvd_card hrSH
              (Subgroup.card_eq_one.mp hc))
        exact hCAr' hrSigmaH.1
          (hrPG.trans (Subgroup.card_dvd_of_le hPGcent)) rfl
      · exact hrNotSigmaM (heq ▸ hqM)
      · let PM : Sylow r M := Classical.choice Sylow.nonempty
        let PMG : Subgroup G := ambientSylow M PM
        have hPMr : IsPGroup r (PM : Subgroup M) := PM.isPGroup'
        have hcent := (beta'_cent_Sylow hM hqNotBetaM hrNotBetaM
          (X := (PM : Subgroup M)) hPMr (Or.inr hqr)).1
        obtain ⟨Q₁, hPMQ₁⟩ := hcent
        obtain ⟨Q₁M, hQ₁M⟩ :=
          exists_sylow_eq_map_of_sylow_hall_embedding
            hqM.1 (Msigma_Hall hM) hqM Q₁
        obtain ⟨e, heA⟩ :=
          exists_conjugate_le_sylow_map Q₁M hAM hA.isPGroup
        let x : G := (e : G)⁻¹
        have hPMxCA :
            PMG.map (MulAut.conj x).toMonoidHom ≤
              Subgroup.centralizer (A : Set G) := by
          intro y hy
          rcases hy with ⟨z, hz, rfl⟩
          rcases hz with ⟨zM, hzPM, hzval⟩
          rw [← hzval]
          rw [Subgroup.mem_centralizer_iff]
          intro a ha
          have heaM : (e : G) * a * (e : G)⁻¹ ∈ M :=
            M.mul_mem (M.mul_mem e.property (hAM ha))
              (M.inv_mem e.property)
          let aM : M := ⟨(e : G) * a * (e : G)⁻¹, heaM⟩
          have haQ₁M : aM ∈ (Q₁M : Subgroup M) := by
            apply (Subgroup.mem_map_iff_mem M.subtype_injective).mp
            simpa [aM] using heA a ha
          rw [hQ₁M] at haQ₁M
          have hcommM := Subgroup.mem_centralizer_iff.mp
            (hPMQ₁ hzPM) aM haQ₁M
          have hcommG := congrArg Subtype.val hcommM
          change (e : G) * a * (e : G)⁻¹ * (zM : G) =
            (zM : G) * ((e : G) * a * (e : G)⁻¹) at hcommG
          change a * ((e : G)⁻¹ * (zM : G) * ((e : G)⁻¹)⁻¹) =
            ((e : G)⁻¹ * (zM : G) * ((e : G)⁻¹)⁻¹) * a
          simp only [inv_inv]
          calc
            a * ((e : G)⁻¹ * (zM : G) * (e : G)) =
                (e : G)⁻¹ *
                  (((e : G) * a * (e : G)⁻¹) * (zM : G)) *
                    (e : G) := by group
            _ = (e : G)⁻¹ *
                  ((zM : G) * ((e : G) * a * (e : G)⁻¹)) *
                    (e : G) := by rw [hcommG]
            _ = ((e : G)⁻¹ * (zM : G) * (e : G)) * a := by group
        have hrPMx : r ∣
            Nat.card (PMG.map (MulAut.conj x).toMonoidHom) := by
          rw [Subgroup.card_map_of_injective (MulAut.conj x).injective]
          change r ∣ Nat.card ((PM : Subgroup M).map M.subtype)
          rw [Subgroup.card_map_of_injective M.subtype_injective]
          exact PM.isPGroup'.card_eq_or_dvd.resolve_left
            (fun hc ↦ PM.ne_bot_of_dvd_card hr.1.2
              (Subgroup.card_eq_one.mp hc))
        exact hCAr' hrSigmaH.1
          (hrPMx.trans (Subgroup.card_dvd_of_le hPMxCA)) rfl
    exact ⟨hqTau, hPrimeIncl, by simpa [I] using hHallI⟩

/-- `BGsection12.v: sigma_Jsub`, Corollary 12.16. -/
theorem sigma_Jsub
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M Y : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hYsigma : IsPiNumber (sigmaPrimes M) (Nat.card Y))
    (hYne : Y ≠ ⊥) :
    (∃ x : G,
        Y.map (MulAut.conj x).toMonoidHom ≤ sigmaCore M) ∧
      ∀ {E : Subgroup G} {p : ℕ} {H : Subgroup G},
        E ≤ M →
        IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M) →
        p ∈ primeSupport (Nat.card E) →
        p ∉ betaPrimes (⊤ : Subgroup G) →
        H ∈ minSimple_max_groups_of (G := G) (Y : Set G) →
        (∀ g : G, H ≠ M.map (MulAut.conj g).toMonoidHom) →
        ¬ HasElementaryAbelianRankAtLeast p 2
            (H ⊓ Subgroup.normalizer (Y : Set G)) ∧
          (p ∈ tau1Primes M →
            ¬ p ∣ Nat.card
              (_root_.commutator
                ↥(H ⊓ Subgroup.normalizer (Y : Set G)))) := by
  classical
  have hYproper : Y < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro hYtop
    have hGsigma : IsPiNumber (sigmaPrimes M) (Nat.card G) := by
      simpa [hYtop] using hYsigma
    have hHallG := Msigma_Hall_G hM
    have hIndexSigma :
        IsPiNumber (sigmaPrimes M) (sigmaCore M).index :=
      hGsigma.of_dvd (sigmaCore M).index_dvd_card
    have hcop := hIndexSigma.coprime_compl hHallG.isPiNumber_index
    have hindexOne : (sigmaCore M).index = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
    have hcoreTop : sigmaCore M = ⊤ :=
      Subgroup.index_eq_one.mp hindexOne
    exact (mmax_proper hM).ne
      (top_unique (by simpa [hcoreTop] using sigmaCore_le M))
  have hYsol : IsSolvable Y := mFT_sol hYproper
  let F : Subgroup G := fittingWithin Y
  have hFne : F ≠ ⊥ := by
    intro hF
    apply hYne
    exact eq_bot_of_fittingWithin_eq_bot_of_isSolvable
      Y hYsol (by simpa [F] using hF)
  obtain ⟨q, hq, hqF⟩ := Nat.exists_prime_and_dvd
    ((F.one_lt_card_iff_ne_bot.mpr hFne).ne')
  letI : Fact q.Prime := ⟨hq⟩
  let R : Subgroup Y := pCore q Y
  let X : Subgroup G := R.map Y.subtype
  have hqFcore : q ∣ Nat.card (fittingCore Y) := by
    dsimp [F, fittingWithin] at hqF
    rw [Subgroup.card_map_of_injective Y.subtype_injective] at hqF
    exact hqF
  have hRne : R ≠ ⊥ := by
    let RF : Subgroup (fittingCore Y) := pCore q (fittingCore Y)
    have hRFne : RF ≠ ⊥ :=
      (pCore_ne_bot_iff_dvd_card_of_isNilpotent
        (G := fittingCore Y) q).2 hqFcore
    intro hR
    have hmapBot : RF.map (fittingCore Y).subtype = ⊥ := by
      rw [map_pCore_fittingCore_eq_pCore Y q]
      exact hR
    exact hRFne ((Subgroup.map_eq_bot_iff_of_injective
      RF (fittingCore Y).subtype_injective).mp hmapBot)
  have hXne : X ≠ ⊥ := by
    intro hX
    exact hRne ((Subgroup.map_eq_bot_iff_of_injective
      R Y.subtype_injective).mp hX)
  have hXY : X ≤ Y := Subgroup.map_subtype_le R
  have hXq : IsPGroup q X := pCore_isPGroup.map Y.subtype
  have hNYNX :
      Subgroup.normalizer (Y : Set G) ≤
        Subgroup.normalizer (X : Set G) := by
    simpa [X, R] using
      characteristic_map_subtype_le_normalizer_embedding Y R
  have hqY : q ∣ Nat.card Y :=
    (hXq.card_eq_or_dvd.resolve_left
      (fun hc ↦ hXne (Subgroup.card_eq_one.mp hc))).trans
      (Subgroup.card_dvd_of_le hXY)
  have hqM : q ∈ sigmaPrimes M := hYsigma hq hqY

  have main : ∀ {M₀ : Subgroup G},
      M₀ ∈ minSimple_max_groups (G := G) →
      sigmaPrimes M₀ = sigmaPrimes M →
      X ≤ sigmaCore M₀ →
      ((∃ x : G,
          Y.map (MulAut.conj x).toMonoidHom ≤ sigmaCore M₀) ∧
        ∀ {E : Subgroup G} {p : ℕ} {H : Subgroup G},
          E ≤ M₀ →
          IsHall (sigmaPrimes M₀)ᶜ (E.subgroupOf M₀) →
          p ∈ primeSupport (Nat.card E) →
          p ∉ betaPrimes (⊤ : Subgroup G) →
          H ∈ minSimple_max_groups_of (G := G) (Y : Set G) →
          (∀ g : G,
            H ≠ M₀.map (MulAut.conj g).toMonoidHom) →
          ¬ HasElementaryAbelianRankAtLeast p 2
              (H ⊓ Subgroup.normalizer (Y : Set G)) ∧
            (p ∈ tau1Primes M₀ →
              ¬ p ∣ Nat.card
                (_root_.commutator
                  ↥(H ⊓ Subgroup.normalizer (Y : Set G))))) := by
    intro M₀ hM₀ hSigma hXcore
    have hqM₀ : q ∈ sigmaPrimes M₀ := by
      rw [hSigma]
      exact hqM
    have hXM₀ : X ≤ M₀ := hXcore.trans (sigmaCore_le M₀)
    have prePart : ∀ {E : Subgroup G} {p : ℕ} {H : Subgroup G},
        E ≤ M₀ →
        IsHall (sigmaPrimes M₀)ᶜ (E.subgroupOf M₀) →
        p ∈ primeSupport (Nat.card E) →
        H ∈ minSimple_max_groups_of (G := G) (Y : Set G) →
        (∀ g : G,
          H ≠ M₀.map (MulAut.conj g).toMonoidHom) →
        ¬ HasElementaryAbelianRankAtLeast p 2 (H ⊓ M₀) := by
      intro E p H hEM hHallE hpE hHY hnot rankTwo
      have hp : p.Prime := hpE.1
      letI : Fact p.Prime := ⟨hp⟩
      rcases rankTwo with ⟨A, hAHM, hA⟩
      have hAM₀ : A ≤ M₀ := hAHM.trans inf_le_right
      have hAH : A ≤ H := hAHM.trans inf_le_left
      have hpNotSigma : p ∉ sigmaPrimes M₀ := by
        have hpSub : p ∣ Nat.card (E.subgroupOf M₀) := by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEM]
          exact hpE.2
        exact hHallE.isPiNumber_card hp hpSub
      have hpNoRankThree :
          ¬ HasElementaryAbelianRankAtLeast p 3 M₀ := by
        rintro ⟨B, hBM₀, hB⟩
        exact hpNotSigma
          (alpha_sub_sigma hM₀ ⟨hp, B, hBM₀, hB⟩)
      have hpTau : p ∈ tau2Primes M₀ :=
        ⟨hp, hpNotSigma, ⟨A, hAM₀, hA⟩, hpNoRankThree⟩
      have hHne : H ≠ M₀ := by
        intro hEq
        exact hnot 1 (hEq.trans (map_conj_one_embedding M₀).symm)
      have hctx := tau2_context hM₀ hpTau hAM₀ hA
      have hHA : H ∈ minSimple_max_groups_of (G := G) (A : Set G) :=
        ⟨hHY.1, hAH⟩
      have hInf := hctx.maximal_intersection_eq_bot hHA hHne
      apply hXne
      apply le_bot_iff.mp
      rw [← hInf]
      exact le_inf hXcore (hXY.trans hHY.2)
    by_cases hNXM : Subgroup.normalizer (X : Set G) ≤ M₀
    · have hNYM : Subgroup.normalizer (Y : Set G) ≤ M₀ :=
        hNYNX.trans hNXM
      have hYM : Y ≤ M₀ := Subgroup.le_normalizer.trans hNYM
      have hYcore : Y ≤ sigmaCore M₀ := by
        let SM : Subgroup M₀ := (sigmaCore M₀).subgroupOf M₀
        let YM : Subgroup M₀ := Y.subgroupOf M₀
        have hSMnormal : SM.Normal := by
          simpa [SM] using sigmaCore_normal M₀
        have hYpi : IsPiNumber (sigmaPrimes M₀) (Nat.card YM) := by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hYM, hSigma]
          exact hYsigma
        have hle : YM ≤ SM :=
          isPiNumber_le_normal_isHall_embedding hSMnormal
            (by simpa [SM] using Msigma_Hall hM₀) hYpi
        intro y hy
        exact hle (show (⟨y, hYM hy⟩ : M₀) ∈ YM from hy)
      refine ⟨⟨1, ?_⟩, ?_⟩
      · rw [map_conj_one_embedding]
        exact hYcore
      · intro E p H hEM hHallE hpE hpBetaG hHY hnot
        have hNo := prePart hEM hHallE hpE hHY hnot
        let N : Subgroup G := H ⊓ Subgroup.normalizer (Y : Set G)
        have hNI : N ≤ H ⊓ M₀ :=
          le_inf inf_le_left (inf_le_right.trans hNYM)
        have hNoN : ¬ HasElementaryAbelianRankAtLeast p 2 N := by
          rintro ⟨A, hAN, hA⟩
          exact hNo ⟨A, hAN.trans hNI, hA⟩
        refine ⟨hNoN, ?_⟩
        intro hpTau hpDerN
        have hderLe :
            (_root_.commutator N).map N.subtype ≤
              (_root_.commutator M₀).map M₀.subtype := by
          rw [N.map_subtype_commutator, M₀.map_subtype_commutator]
          exact Subgroup.commutator_mono
            (inf_le_right.trans hNYM) (inf_le_right.trans hNYM)
        have hpMap : p ∣ Nat.card
            ((_root_.commutator N).map N.subtype) := by
          rwa [Subgroup.card_map_of_injective N.subtype_injective]
        have hpMapM : p ∣ Nat.card
            ((_root_.commutator M₀).map M₀.subtype) :=
          hpMap.trans (Subgroup.card_dvd_of_le hderLe)
        exact hpTau.2.2.2.2
          (by
            rwa [Subgroup.card_map_of_injective M₀.subtype_injective]
              at hpMapM)
    · have hNXproper : Subgroup.normalizer (X : Set G) < ⊤ :=
        mFT_norm_proper X hXne (mFT_pgroup_proper X hXq)
      obtain ⟨L, hL, hNXL⟩ :=
        mmax_exists (Subgroup.normalizer (X : Set G)) hNXproper
      have hLneM : L ≠ M₀ := by
        intro hEq
        apply hNXM
        simpa [hEq] using hNXL
      have hYL : Y ≤ L :=
        Subgroup.le_normalizer.trans (hNYNX.trans hNXL)
      let I : Subgroup G := M₀ ⊓ L
      have hXI : X ≤ I :=
        le_inf hXM₀ (Subgroup.le_normalizer.trans hNXL)
      let XI : Subgroup I := X.subgroupOf I
      have hXIq : IsPGroup q XI :=
        hXq.of_equiv (Subgroup.subgroupOfEquivOfLe hXI).symm
      obtain ⟨S, hXIS⟩ := hXIq.exists_le_sylow
      have hXS : X ≤ ambientSylow I S := by
        rw [← Subgroup.map_subgroupOf_eq_of_le hXI]
        exact Subgroup.map_mono hXIS
      have hLNX : L ∈ minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (X : Set G) : Set G) := ⟨hL, hNXL⟩
      obtain ⟨hnotL, hparts⟩ :=
        sigma_subgroup_embedding hM₀ hqM₀ hXM₀ hXq hXne
          hLNX hLneM
      have hpart := hparts S hXS
      let K : Subgroup G :=
        if q ∈ sigmaPrimes L then betaCore L else sigmaCore L
      have hKL : K ≤ L := by
        dsimp [K]
        split <;> simp_all only [betaCore_le, sigmaCore_le]
      have hKnormal : (K.subgroupOf L).Normal := by
        dsimp [K]
        split
        · simpa using betaCore_normal L
        · simpa using sigmaCore_normal L
      have hKI : K ⊔ I = L := by
        by_cases hqL : q ∈ sigmaPrimes L
        · have hpartL := hpart.2.2
          rw [if_pos hqL] at hpartL
          have hprod := hpartL.1
          apply sup_eq_of_carrier_mul_eq hKL inf_le_right
          simpa [K, hqL, I] using hprod
        · have hpartL := hpart.2.2
          rw [if_neg hqL] at hpartL
          have hHallI := hpartL.2.2
          have hsd := sdprod_sigma hL inf_le_right
            (by simpa [I] using hHallI)
          change sigmaCore L ≤ L ∧ I ≤ L ∧
              ((sigmaCore L).subgroupOf L).Normal ∧
              ((sigmaCore L).subgroupOf L).IsComplement'
                (I.subgroupOf L) at hsd
          have hcarrier :
              (sigmaCore L : Set G) * (I : Set G) = (L : Set G) :=
            carrier_mul_eq_of_sup_eq (sigmaCore_le L) inf_le_right
              (sigmaCore_normal L)
              (by
                have hmapped := congrArg (Subgroup.map L.subtype)
                  hsd.2.2.2.sup_eq_top
                rw [Subgroup.map_sup,
                  Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le L),
                  Subgroup.map_subgroupOf_eq_of_le inf_le_right,
                  ← MonoidHom.range_eq_map, L.range_subtype] at hmapped
                exact hmapped)
          apply sup_eq_of_carrier_mul_eq hKL inf_le_right
          simpa [K, hqL, I] using hcarrier
      have hnotSymm : ∀ g : G,
          M₀ ≠ L.map (MulAut.conj g).toMonoidHom := by
        intro g hEq
        apply hnotL g⁻¹
        have hmapped := congrArg
          (fun T : Subgroup G ↦
            T.map (MulAut.conj g⁻¹).toMonoidHom) hEq
        rw [map_conj_inv_map_conj_embedding] at hmapped
        exact hmapped.symm
      have hKsigma' :
          IsPiNumber (sigmaPrimes M₀)ᶜ (Nat.card K) := by
        by_cases hqL : q ∈ sigmaPrimes L
        · have hdis := (sigma_disjoint hL hM₀ hnotSymm).2.1
          intro r hr hrK hrM₀
          have hrBetaL : r ∈ betaPrimes L := by
            exact betaCore_isPiNumber L hr
              (by simpa [K, hqL] using hrK)
          exact Set.disjoint_left.mp hdis
            ((beta_sub_alpha L) hrBetaL) hrM₀
        · have hqTau : q ∈ tau2Primes L :=
            by
              have hpartL := hpart.2.2
              rw [if_neg hqL] at hpartL
              exact hpartL.1
          have hdis := (sigma_disjoint hL hM₀ hnotSymm).2.2
            (tau2_Msigma_nil hL hqTau) |>.2
          intro r hr hrK hrM₀
          exact Set.disjoint_left.mp hdis
            (sigmaCore_isPiNumber L hr (by simpa [K, hqL] using hrK))
            hrM₀
      have hIsol : IsSolvable I :=
        mFT_sol (lt_of_le_of_lt inf_le_left (mmax_proper hM₀))
      obtain ⟨J, hJI, hJHallI⟩ :=
        exists_ambient_isHall_of_isSolvable hIsol (sigmaPrimes M₀)
      have hJHallL : IsHall (sigmaPrimes M₀) (J.subgroupOf L) :=
        isHall_of_normal_complement_sup hKL inf_le_right hJI
          hKnormal hKI hKsigma' hJHallI
      have hYpiM₀ : IsPiNumber (sigmaPrimes M₀) (Nat.card Y) := by
        simpa [hSigma] using hYsigma
      obtain ⟨xL, hYJx, -, -, -, -, -⟩ :=
        exists_ambient_isHall_map_conj_ge_of_isSolvable
          (K := L) (A := Y) (H := J)
          hYL (hJI.trans inf_le_right) (mmax_sol hL)
          hYpiM₀ hJHallL
      let x : G := (xL : G)⁻¹
      have hxYJ : Y.map (MulAut.conj x).toMonoidHom ≤ J := by
        have hmapped := Subgroup.map_mono hYJx
          (f := (MulAut.conj (xL : G)⁻¹).toMonoidHom)
        have hback := map_conj_inv_map_conj_embedding J (xL : G)
        exact hmapped.trans_eq hback
      have hxYM₀ :
          Y.map (MulAut.conj x).toMonoidHom ≤ M₀ :=
        hxYJ.trans (hJI.trans inf_le_left)
      have hxYcore :
          Y.map (MulAut.conj x).toMonoidHom ≤ sigmaCore M₀ := by
        let Yx : Subgroup G :=
          Y.map (MulAut.conj x).toMonoidHom
        have hYxpi : IsPiNumber (sigmaPrimes M₀)
            (Nat.card (Yx.subgroupOf M₀)) := by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hxYM₀,
            Subgroup.card_map_of_injective (MulAut.conj x).injective,
            hSigma]
          exact hYsigma
        have hle : Yx.subgroupOf M₀ ≤
            (sigmaCore M₀).subgroupOf M₀ :=
          isPiNumber_le_normal_isHall_embedding
            (by simpa using sigmaCore_normal M₀) (Msigma_Hall hM₀) hYxpi
        intro y hy
        exact hle (show (⟨y, hxYM₀ hy⟩ : M₀) ∈
          Yx.subgroupOf M₀ from hy)
      refine ⟨⟨x, hxYcore⟩, ?_⟩
      intro E p H hEM hHallE hpE hpBetaG hHY hnotH
      have hp : p.Prime := hpE.1
      letI : Fact p.Prime := ⟨hp⟩
      have hpNotSigmaM : p ∉ sigmaPrimes M₀ := by
        have hpSub : p ∣ Nat.card (E.subgroupOf M₀) := by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEM]
          exact hpE.2
        exact hHallE.isPiNumber_card hp hpSub
      have hKp' : IsPiNumber ({p} : Set ℕ)ᶜ (Nat.card K) := by
        intro r hr hrK hrEq
        subst r
        by_cases hqL : q ∈ sigmaPrimes L
        · have hpBetaL : p ∈ betaPrimes L :=
            betaCore_isPiNumber L hp (by simpa [K, hqL] using hrK)
          have hpPair : p ∈
              sigmaPrimes L ∩ betaPrimes (⊤ : Subgroup G) := by
            rw [predI_sigma_beta hL]
            exact hpBetaL
          exact hpBetaG hpPair.2
        · have hpSigmaL : p ∈ sigmaPrimes L :=
            sigmaCore_isPiNumber L hp (by simpa [K, hqL] using hrK)
          have hpMcard : p ∈ primeSupport (Nat.card M₀) :=
            ⟨hp, hpE.2.trans (Subgroup.card_dvd_of_le hEM)⟩
          have hpBetaL :=
            by
              have hpartL := hpart.2.2
              rw [if_neg hqL] at hpartL
              exact hpartL.2.1 ⟨hpMcard, hpSigmaL⟩
          have hpPair : p ∈
              sigmaPrimes L ∩ betaPrimes (⊤ : Subgroup G) := by
            rw [predI_sigma_beta hL]
            exact hpBetaL
          exact hpBetaG hpPair.2
      let P : Sylow p I := Classical.choice Sylow.nonempty
      let PG : Subgroup G := (P : Subgroup I).map I.subtype
      have hPsylI : IsSylowSubgroupOf p PG I := ⟨P, rfl⟩
      have hPsylL : IsSylowSubgroupOf p PG L :=
        isSylowSubgroupOf_map_of_normal_sup hKL inf_le_right
          hKnormal hKI hKp' (by simp) P
      have hNoI : ¬ HasElementaryAbelianRankAtLeast p 2 I := by
        have hnotLI : ∀ g : G,
            L ≠ M₀.map (MulAut.conj g).toMonoidHom := hnotL
        simpa [I, inf_comm] using
          (prePart hEM hHallE hpE ⟨hL, hYL⟩ hnotLI)
      have hNoL : ¬ HasElementaryAbelianRankAtLeast p 2 L := by
        intro hRankL
        exact hNoI
          ((elementaryAbelianRankAtLeast_iff_of_common_sylow
            hPsylI hPsylL).mpr hRankL)
      let N : Subgroup G := H ⊓ Subgroup.normalizer (Y : Set G)
      have hNL : N ≤ L :=
        inf_le_right.trans (hNYNX.trans hNXL)
      have hNoN : ¬ HasElementaryAbelianRankAtLeast p 2 N := by
        rintro ⟨A, hAN, hA⟩
        exact hNoL ⟨A, hAN.trans hNL, hA⟩
      refine ⟨hNoN, ?_⟩
      intro hpTau hpDerN
      have hpDerI : ¬ p ∣ Nat.card (_root_.commutator I) := by
        intro hpI
        have hmapLe :
            (_root_.commutator I).map I.subtype ≤
              (_root_.commutator M₀).map M₀.subtype := by
          rw [I.map_subtype_commutator, M₀.map_subtype_commutator]
          exact Subgroup.commutator_mono inf_le_left inf_le_left
        have hpMap : p ∣ Nat.card
            ((_root_.commutator I).map I.subtype) := by
          rwa [Subgroup.card_map_of_injective I.subtype_injective]
        exact hpTau.2.2.2.2
          (by
            rw [← Subgroup.card_map_of_injective M₀.subtype_injective]
            exact hpMap.trans (Subgroup.card_dvd_of_le hmapLe))
      have hpDerL : ¬ p ∣ Nat.card (_root_.commutator L) := by
        have hPGL : PG ≤ L := IsSylowSubgroupOf.le_right hPsylL
        rcases hPsylL with ⟨PL, hPL⟩
        let KL : Subgroup L := K.subgroupOf L
        let IL : Subgroup L := I.subgroupOf L
        let QL : Subgroup L := PG.subgroupOf L
        have hKLnormal : KL.Normal := by simpa [KL] using hKnormal
        letI : KL.Normal := hKLnormal
        have hsupL : KL ⊔ IL = ⊤ := by
          apply Subgroup.map_injective L.subtype_injective
          rw [Subgroup.map_sup,
            Subgroup.map_subgroupOf_eq_of_le hKL,
            Subgroup.map_subgroupOf_eq_of_le inf_le_right,
            hKI, ← MonoidHom.range_eq_map, L.range_subtype]
        have hQLIL : QL ≤ IL := by
          intro x hx
          change (x : G) ∈ I
          change (x : G) ∈ PG at hx
          exact Subgroup.map_subtype_le P hx
        have hQL_eq : QL = (PL : Subgroup L) := by
          apply Subgroup.map_injective L.subtype_injective
          rw [Subgroup.map_subgroupOf_eq_of_le hPGL]
          exact hPL
        have hKLp' : IsPiNumber ({p} : Set ℕ)ᶜ (Nat.card KL) := by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hKL]
          exact hKp'
        have hQLp : IsPiNumber ({p} : Set ℕ) (Nat.card QL) := by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
            hPGL]
          exact P.isPGroup'.map I.subtype |>.isPiNumber_natCard
            (Set.mem_singleton p)
        have hfocal :
            QL ⊓ _root_.commutator L = QL ⊓ ⁅IL, IL⁆ :=
          Section06.pprod_focal_coprime hsupL hQLIL
            (hKLp'.coprime_compl
              (by simpa only [compl_compl] using hQLp))
        intro hpL
        let Z : Sylow p (_root_.commutator L) :=
          normalIntersectionSylow PL (_root_.commutator L)
        have hZne : (Z : Subgroup (_root_.commutator L)) ≠ ⊥ :=
          Z.ne_bot_of_dvd_card hpL
        have hleftNe : QL ⊓ _root_.commutator L ≠ ⊥ := by
          intro hbot
          have hmapZ := map_normalIntersectionSylow_eq_inf
            PL (_root_.commutator L)
          have hmapBot :
              (Z : Subgroup (_root_.commutator L)).map
                  (_root_.commutator L).subtype = ⊥ := by
            calc
              (Z : Subgroup (_root_.commutator L)).map
                    (_root_.commutator L).subtype =
                  (PL : Subgroup L) ⊓ _root_.commutator L := by
                simpa [Z] using hmapZ
              _ = QL ⊓ _root_.commutator L := by rw [hQL_eq]
              _ = ⊥ := hbot
          exact hZne ((Subgroup.map_eq_bot_iff_of_injective
            (Z : Subgroup (_root_.commutator L))
            (_root_.commutator L).subtype_injective).mp hmapBot)
        have hrightNe : QL ⊓ ⁅IL, IL⁆ ≠ ⊥ := by
          rwa [← hfocal]
        let W : Subgroup L := QL ⊓ ⁅IL, IL⁆
        have hWp : IsPGroup p W := by
          apply PL.isPGroup'.to_le
          exact inf_le_left.trans_eq hQL_eq
        have hpW : p ∣ Nat.card W :=
          hWp.card_eq_or_dvd.resolve_left
            (fun hc ↦ hrightNe (by simpa [W] using Subgroup.card_eq_one.mp hc))
        have hWderI : W.map L.subtype ≤
            (_root_.commutator I).map I.subtype := by
          dsimp [W]
          calc
            (QL ⊓ ⁅IL, IL⁆).map L.subtype ≤
                ⁅IL, IL⁆.map L.subtype :=
              Subgroup.map_mono inf_le_right
            _ = ⁅IL.map L.subtype, IL.map L.subtype⁆ :=
              Subgroup.map_commutator _ _ L.subtype
            _ = ⁅I, I⁆ := by
              rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right]
            _ = (_root_.commutator I).map I.subtype :=
              I.map_subtype_commutator.symm
        exact hpDerI
          (by
            rw [← Subgroup.card_map_of_injective I.subtype_injective]
            have hpWmap : p ∣ Nat.card (W.map L.subtype) := by
              rwa [Subgroup.card_map_of_injective L.subtype_injective]
            exact hpWmap.trans (Subgroup.card_dvd_of_le hWderI))
      have hderNL :
          (_root_.commutator N).map N.subtype ≤
            (_root_.commutator L).map L.subtype := by
        rw [N.map_subtype_commutator, L.map_subtype_commutator]
        exact Subgroup.commutator_mono hNL hNL
      have hpMapN : p ∣ Nat.card
          ((_root_.commutator N).map N.subtype) := by
        rwa [Subgroup.card_map_of_injective N.subtype_injective]
      exact hpDerL
        (by
          rw [← Subgroup.card_map_of_injective L.subtype_injective]
          exact hpMapN.trans (Subgroup.card_dvd_of_le hderNL))

  let Sσ : Subgroup G := sigmaCore M
  let Pσ : Sylow q Sσ := Classical.choice Sylow.nonempty
  obtain ⟨Q, hQ⟩ :=
    exists_sylow_eq_map_of_sylow_hall_embedding hq
      (Msigma_Hall_G hM) hqM Pσ
  let QTop : Sylow q (⊤ : Subgroup G) := Q.subtype le_top
  obtain ⟨gTop, hgX⟩ :=
    exists_conjugate_le_sylow_map QTop
      (show X ≤ (⊤ : Subgroup G) from le_top) hXq
  let g : G := (gTop : G)
  have hXgS : X.map (MulAut.conj g).toMonoidHom ≤ Sσ := by
    intro x hx
    rcases hx with ⟨y, hy, rfl⟩
    have hmem := hgX y hy
    have hmapTop :
        (QTop : Subgroup (⊤ : Subgroup G)).map
            (⊤ : Subgroup G).subtype = (Q : Subgroup G) := by
      simpa [QTop] using
        (Subgroup.map_subgroupOf_eq_of_le
          (show (Q : Subgroup G) ≤ (⊤ : Subgroup G) from le_top))
    rw [hmapTop] at hmem
    rw [hQ] at hmem
    exact Subgroup.map_subtype_le Pσ hmem
  let M₀ : Subgroup G := M.map (MulAut.conj g⁻¹).toMonoidHom
  have hM₀ : M₀ ∈ minSimple_max_groups (G := G) :=
    (mmaxJ M (MulAut.conj g⁻¹)).mpr hM
  have hSigma₀ : sigmaPrimes M₀ = sigmaPrimes M := by
    simpa [M₀] using sigmaPrimes_conj M g⁻¹
  have hXcore₀ : X ≤ sigmaCore M₀ := by
    have hmapped := Subgroup.map_mono hXgS
      (f := (MulAut.conj g⁻¹).toMonoidHom)
    rw [map_conj_inv_map_conj_embedding] at hmapped
    change X ≤ sigmaCore
      (M.map (MulAut.conj g⁻¹).toMonoidHom)
    rw [sigmaCore_conj]
    exact hmapped
  obtain ⟨hex, hfinal⟩ := main hM₀ hSigma₀ hXcore₀
  constructor
  · obtain ⟨x, hx⟩ := hex
    refine ⟨g * x, ?_⟩
    have hmapped := Subgroup.map_mono hx
      (f := (MulAut.conj g).toMonoidHom)
    have hMback :
        M₀.map (MulAut.conj g).toMonoidHom = M := by
      change (M.map (MulAut.conj g⁻¹).toMonoidHom).map
          (MulAut.conj g).toMonoidHom = M
      simpa only [inv_inv] using
        (map_conj_inv_map_conj_embedding M g⁻¹)
    have hSigmaBack :
        (sigmaCore M₀).map (MulAut.conj g).toMonoidHom =
          sigmaCore M := by
      rw [← sigmaCore_conj, hMback]
    rw [map_conj_map_conj_embedding, hSigmaBack] at hmapped
    exact hmapped
  · intro E p H hEM hHallE hpE hpBetaG hHY hnotH
    let E₀ : Subgroup G := E.map (MulAut.conj g⁻¹).toMonoidHom
    have hE₀M₀ : E₀ ≤ M₀ := Subgroup.map_mono hEM
    have hHallE₀ :
        IsHall (sigmaPrimes M₀)ᶜ (E₀.subgroupOf M₀) := by
      rw [hSigma₀]
      simpa [E₀, M₀] using
        isHall_subgroupOf_map_mulEquiv_embedding hEM hHallE
          (MulAut.conj g⁻¹)
    have hpE₀ : p ∈ primeSupport (Nat.card E₀) := by
      have hcard : Nat.card E₀ = Nat.card E := by
        dsimp [E₀]
        rw [Subgroup.card_map_of_injective
          (MulAut.conj g⁻¹).injective]
      rwa [hcard]
    have hnotH₀ : ∀ z : G,
        H ≠ M₀.map (MulAut.conj z).toMonoidHom := by
      intro z hEq
      apply hnotH (z * g⁻¹)
      change H =
        (M.map (MulAut.conj g⁻¹).toMonoidHom).map
          (MulAut.conj z).toMonoidHom at hEq
      rw [map_conj_map_conj_embedding] at hEq
      exact hEq
    have hres := hfinal hE₀M₀ hHallE₀ hpE₀ hpBetaG hHY hnotH₀
    have hTauEq : tau1Primes M₀ = tau1Primes M := by
      simpa [M₀] using tau1J M g⁻¹
    refine ⟨hres.1, ?_⟩
    intro hpTau
    exact hres.2 (by rwa [hTauEq])

/-- `BGsection12.v: sigma_compl_embedding`, Lemma 12.17. -/
theorem sigma_compl_embedding
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    centralizerWithin (sigmaCore M) E ≤
        (_root_.commutator (sigmaCore M)).map
          (sigmaCore M).subtype ∧
      ⁅sigmaCore M, E⁆ = sigmaCore M ∧
      ∀ g : G, g ∉ M →
        let T := sigmaCore M ⊓
          M.map (MulAut.conj g).toMonoidHom
        IsCyclic T ∧
          IsPiNumber (betaPrimes M)ᶜ (Nat.card T) ∧
          T ⊓ (_root_.commutator (sigmaCore M)).map
              (sigmaCore M).subtype = ⊥ := by
  classical
  let S : Subgroup G := sigmaCore M
  let SM : Subgroup M := S.subgroupOf M
  let EM : Subgroup M := E.subgroupOf M
  have hsd := sdprod_sigma hM hEM hHallE
  change S ≤ M ∧ E ≤ M ∧ (S.subgroupOf M).Normal ∧
      (S.subgroupOf M).IsComplement' (E.subgroupOf M) at hsd
  have hcomp : SM.IsComplement' EM := by
    simpa [SM, EM] using hsd.2.2.2
  letI : SM.Normal := by simpa [SM] using hsd.2.2.1
  have hnorm : EM ≤ Subgroup.normalizer (SM : Set M) :=
    Subgroup.le_normalizer_of_normal
  have hcop : Nat.Coprime (Nat.card SM) (Nat.card EM) := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq (show S ≤ M from sigmaCore_le M),
      Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEM]
    exact coprime_sigma_compl hEM hHallE
  have hSMder : SM ≤ _root_.commutator M := by
    apply (Subgroup.map_le_map_iff_of_injective
      M.subtype_injective).mp
    rw [Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)]
    exact Msigma_der1 hM
  letI : IsSolvable SM := by
    letI : IsSolvable M := mmax_sol hM
    exact isSolvable_of_injective SM.subtype SM.subtype_injective
  have hcopDer := coprime_der1_sdprod
    (G := M) (K := SM) (H := EM)
    hcomp hnorm hcop hSMder
  have hcentIntrinsic :
      centralizerWithin SM EM ≤ ⁅SM, SM⁆ := hcopDer.2
  have hcent :
      centralizerWithin S E ≤
        (_root_.commutator S).map S.subtype := by
    have hmapped := Subgroup.map_mono hcentIntrinsic
      (f := M.subtype)
    rw [map_centralizerWithin_subgroupOf (sigmaCore_le M) hEM,
      Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)] at hmapped
    rw [S.map_subtype_commutator]
    simpa [S, SM, EM] using hmapped
  have hmixed : ⁅S, E⁆ = S := by
    have hmapped := congrArg
      (fun L : Subgroup M => L.map M.subtype) hcopDer.1
    simpa [S, SM, EM, Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M),
      Subgroup.map_subgroupOf_eq_of_le hEM] using hmapped
  refine ⟨hcent, hmixed, ?_⟩
  intro g hg
  let Mg : Subgroup G := M.map (MulAut.conj g).toMonoidHom
  let T : Subgroup G := S ⊓ Mg
  let D : Subgroup G :=
    (_root_.commutator S).map S.subtype
  have hTM : T ≤ M :=
    inf_le_left.trans (by simpa [S] using sigmaCore_le M)
  have hTMg : T ≤ Mg := inf_le_right
  have hTpi : IsPiNumber (sigmaPrimes M) (Nat.card T) :=
    (sigmaCore_isPiNumber M).of_dvd
      (Subgroup.card_dvd_of_le inf_le_left)

  have hnotCent : ∀ {r : ℕ} [Fact r.Prime]
      {A : Subgroup G}, IsPGroup r A → A ≤ T → A ≠ ⊥ →
      ¬ Subgroup.centralizer (A : Set G) ≤ M := by
    intro r _ A hAr hAT hAne hCAM
    have hrSigma : r ∈ sigmaPrimes M := by
      have hrA : r ∣ Nat.card A :=
        hAr.card_eq_or_dvd.resolve_left
          (fun hcard => hAne (Subgroup.card_eq_one.mp hcard))
      exact hTpi Fact.out
        (hrA.trans (Subgroup.card_dvd_of_le hAT))
    have hAM : A ≤ M := hAT.trans hTM
    have hAMg : A ≤ Mg := hAT.trans hTMg
    have hAback :
        A.map (MulAut.conj g⁻¹).toMonoidHom ≤ M := by
      have hm := Subgroup.map_mono hAMg
        (f := (MulAut.conj g⁻¹).toMonoidHom)
      change A.map (MulAut.conj g⁻¹).toMonoidHom ≤
        (M.map (MulAut.conj g).toMonoidHom).map
          (MulAut.conj g⁻¹).toMonoidHom at hm
      rw [map_conj_inv_map_conj_embedding] at hm
      exact hm
    obtain ⟨c, hc, m, hm, hcm⟩ :=
      (sigma_group_trans hM hrSigma hAr).1 g hAM hAback
    apply hg
    rw [hcm]
    exact M.mul_mem (hCAM hc) hm

  have hNoRankTwo : ∀ r : ℕ, r.Prime →
      ¬ HasElementaryAbelianRankAtLeast r 2 T := by
    intro r hr
    rintro ⟨A, hAT, hA⟩
    letI : Fact r.Prime := ⟨hr⟩
    have hNCAM : Subgroup.normalizer (A : Set G) ≤ M :=
      norm_noncyclic_sigma hM
        (by
          have hrA : r ∣ Nat.card A := by
            rw [hA.card_eq]
            exact dvd_pow_self r (by omega)
          exact hTpi hr
            (hrA.trans (Subgroup.card_dvd_of_le hAT)))
        hA.isPGroup (hAT.trans hTM)
        (hA.not_isCyclic hr)
    exact (hnotCent hA.isPGroup hAT hA.ne_bot)
      ((Subgroup.centralizer_le_normalizer (A : Set G)).trans hNCAM)

  have hTD : T ⊓ D = ⊥ := by
    by_contra hne
    obtain ⟨r, hr, X, hXTD, hX⟩ :=
      exists_rank_one_le_of_ne_bot hne
    letI : Fact r.Prime := ⟨hr⟩
    have hXT : X ≤ T := hXTD.trans inf_le_left
    have hXD : X ≤ D := hXTD.trans inf_le_right
    have huniq := cent_der_sigma_uniq hM (hXT.trans hTM) hX
      (Or.inr (by simpa [D, S] using hXD))
    have hMfamily :
        M ∈ minSimple_max_groups_of (G := G)
          (Subgroup.centralizer (X : Set G) : Set G) := by
      rw [huniq.1]
      simp
    exact (hnotCent hX.isPGroup hXT hX.ne_bot) hMfamily.2

  have hTcomm : ⁅T, T⁆ = ⊥ := by
    apply le_antisymm _ bot_le
    rw [← hTD]
    exact le_inf (by
      simpa using
        (Subgroup.commutator_le_sup (H₁ := T) (H₂ := T)))
      ((Subgroup.commutator_mono inf_le_left inf_le_left).trans
        (by simpa [D, S] using
          (show ⁅S, S⁆ ≤ D from (S.map_subtype_commutator).ge)))
  letI : IsMulCommutative T := by
    apply isMulCommutative_iff.mpr
    intro a b
    apply Subtype.ext
    have hcentT : T ≤ Subgroup.centralizer (T : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hTcomm
    exact (Subgroup.mem_centralizer_iff.mp
      (hcentT a.property) b b.property).symm
  have hTZ : IsZGroup T := by
    apply (odd_isZGroup_iff_sylow_no_elementaryAbelian_rank_two
      (mFT_odd T)).mpr
    intro r hr P
    rintro ⟨A, hA⟩
    let AG : Subgroup G :=
      A.map (P : Subgroup T).subtype |>.map T.subtype
    have hAG : IsElementaryAbelianOfRank r 2 AG :=
      (hA.map_of_injective (P : Subgroup T).subtype
        (P : Subgroup T).subtype_injective).map_of_injective
          T.subtype T.subtype_injective
    exact hNoRankTwo r hr
      ⟨AG, Subgroup.map_subtype_le _, hAG⟩
  letI : IsZGroup T := hTZ
  letI : Group.IsNilpotent T := by infer_instance
  have hTcyclic : IsCyclic T := by infer_instance

  have hTbeta' :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card T) := by
    intro r hr hrT hrBeta
    obtain ⟨X, hXT, hX⟩ :=
      exists_rank_one_le_of_prime_dvd hr hrT
    letI : Fact r.Prime := ⟨hr⟩
    have huniq := cent_der_sigma_uniq hM (hXT.trans hTM) hX
      (Or.inl hrBeta)
    have hMfamily :
        M ∈ minSimple_max_groups_of (G := G)
          (Subgroup.centralizer (X : Set G) : Set G) := by
      rw [huniq.1]
      simp
    exact (hnotCent hX.isPGroup hXT hX.ne_bot) hMfamily.2
  simpa [T, Mg, S, D] using ⟨hTcyclic, hTbeta', hTD⟩

/-! ### The one remaining Section 1 compatibility seam for Lemma 12.18 -/

/-- If the alpha core is trivial, the derived subgroup of a maximal
subgroup is nilpotent.  This is the local form of the quotient argument at
source lines 2634--2639. -/
private theorem commutator_isNilpotent_of_alphaCore_eq_bot_embedding
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hbot : alphaCore M = ⊥) :
    Group.IsNilpotent (_root_.commutator M) := by
  have hsubbot : (alphaCore M).subgroupOf M = ⊥ := by
    simp [hbot]
  have hqnil := Malpha_quo_nil hM
  let eQ :
      (M ⧸ (alphaCore M).subgroupOf M) ≃*
        (M ⧸ (⊥ : Subgroup M)) :=
    QuotientGroup.quotientMulEquivOfEq hsubbot
  have heQrange : eQ.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr eQ.surjective
  have hmapQ :
      (_root_.commutator
          (M ⧸ (alphaCore M).subgroupOf M)).map
            eQ.toMonoidHom =
        _root_.commutator (M ⧸ (⊥ : Subgroup M)) := by
    simpa only [heQrange, _root_.commutator_def] using
      (map_commutator_eq
        (M ⧸ (alphaCore M).subgroupOf M) eQ.toMonoidHom)
  let eQD :
      _root_.commutator
          (M ⧸ (alphaCore M).subgroupOf M) ≃*
        _root_.commutator (M ⧸ (⊥ : Subgroup M)) :=
    (eQ.subgroupMap
      (_root_.commutator
        (M ⧸ (alphaCore M).subgroupOf M))).trans
      (MulEquiv.subgroupCongr hmapQ)
  letI : Group.IsNilpotent
      (_root_.commutator (M ⧸ (⊥ : Subgroup M))) := by
    exact Group.nilpotent_of_mulEquiv eQD
  let e : (M ⧸ (⊥ : Subgroup M)) ≃* M :=
    QuotientGroup.quotientBot
  have herange : e.toMonoidHom.range = ⊤ :=
    MonoidHom.range_eq_top.mpr e.surjective
  have hmap :
      (_root_.commutator (M ⧸ (⊥ : Subgroup M))).map
          e.toMonoidHom = _root_.commutator M := by
    simpa only [herange, _root_.commutator_def] using
      (map_commutator_eq (M ⧸ (⊥ : Subgroup M)) e.toMonoidHom)
  let eD : _root_.commutator (M ⧸ (⊥ : Subgroup M)) ≃*
      _root_.commutator M :=
    (e.subgroupMap
      (_root_.commutator (M ⧸ (⊥ : Subgroup M)))).trans
      (MulEquiv.subgroupCongr hmap)
  exact Group.nilpotent_of_mulEquiv eD

/-- Move the rank-three witness in `alpha(M)` into an arbitrary Sylow
subgroup and then back to the ambient group. -/
private theorem sylow_has_rank_three_of_mem_alpha_embedding
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpAlpha : p ∈ alphaPrimes M) (P : Sylow p M) :
    HasElementaryAbelianRankAtLeast p 3 (ambientSylow M P) := by
  classical
  rcases hpAlpha with ⟨_hp, E, hEM, hE⟩
  let EM : Subgroup M := E.subgroupOf M
  have hEMrank : IsElementaryAbelianOfRank p 3 EM :=
    hE.subgroupOf hEM
  obtain ⟨R, hEMR⟩ := hEMrank.isPGroup.exists_le_sylow
  obtain ⟨m, hm⟩ := MulAction.exists_smul_eq M R P
  let C : Subgroup M :=
    EM.map (MulAut.conj m).toMonoidHom
  have hRmap :
      (R : Subgroup M).map (MulAut.conj m).toMonoidHom =
        (P : Subgroup M) := by
    change MulAut.conj m • (R : Subgroup M) = (P : Subgroup M)
    rw [← Sylow.coe_subgroup_smul, hm]
  have hCP : C ≤ (P : Subgroup M) :=
    (Subgroup.map_mono hEMR).trans_eq hRmap
  have hC : IsElementaryAbelianOfRank p 3 C :=
    hEMrank.map_of_injective (MulAut.conj m).toMonoidHom
      (MulAut.conj m).injective
  let D : Subgroup G := C.map M.subtype
  exact ⟨D, Subgroup.map_mono hCP,
    hC.map_of_injective M.subtype M.subtype_injective⟩

/-- A normalized disjoint pair is complementary in the subgroup it
generates.  This local orientation is the one used by the two Frobenius
groups in Lemma 12.18. -/
private theorem subgroupOf_sup_isComplement_embedding
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
    apply le_antisymm _ bot_le
    intro x hx
    apply Subgroup.mem_bot.mpr
    apply Subtype.ext
    have hxbot : ((x : K) : G) ∈ (⊥ : Subgroup G) :=
      hdis.le_bot ⟨hx.1, hx.2⟩
    exact Subgroup.mem_bot.mp hxbot
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisK
  have htop : HK ⊔ RK = ⊤ := by
    change H.subgroupOf K ⊔ R.subgroupOf K = ⊤
    rw [← Subgroup.subgroupOf_sup
      (show H ≤ K from le_sup_left)
      (show R ≤ K from le_sup_right)]
    exact Subgroup.subgroupOf_self K
  rw [← Subgroup.normal_mul HK RK, htop]
  rfl

/-- In a normalized product `N Q`, an element fixed by an actor `P` has
trivial `Q`-coordinate when `C_Q(P)=1`. -/
private theorem centralizerWithin_sup_le_left_of_fixed_right_embedding
    {G : Type u} [Group G]
    {N Q P : Subgroup G}
    (hQnormN : Q ≤ Subgroup.normalizer (N : Set G))
    (hPnormN : P ≤ Subgroup.normalizer (N : Set G))
    (hPnormQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hdis : Disjoint N Q)
    (hfixed : centralizerWithin Q P = ⊥) :
    centralizerWithin (N ⊔ Q) P ≤ N := by
  classical
  let K : Subgroup G := N ⊔ Q
  let NK : Subgroup K := N.subgroupOf K
  let QK : Subgroup K := Q.subgroupOf K
  have hcomp : NK.IsComplement' QK := by
    simpa [NK, QK, K] using
      subgroupOf_sup_isComplement_embedding hQnormN hdis
  intro x hx
  let xK : K := ⟨x, hx.1⟩
  obtain ⟨⟨n, q⟩, hnq⟩ := hcomp.2 xK
  have hnqG : ((n : K) : G) * ((q : K) : G) = x :=
    congrArg (fun z : K => (z : G)) hnq
  have hqCent : ((q : K) : G) ∈ centralizerWithin Q P := by
    refine ⟨q.property, ?_⟩
    intro a ha
    have hnaN : a * ((n : K) : G) * a⁻¹ ∈ N :=
      (Subgroup.mem_normalizer_iff.mp (hPnormN ha) ((n : K) : G)).mp
        n.property
    have hqaQ : a * ((q : K) : G) * a⁻¹ ∈ Q :=
      (Subgroup.mem_normalizer_iff.mp (hPnormQ ha) ((q : K) : G)).mp
        q.property
    let n' : NK :=
      ⟨⟨a * ((n : K) : G) * a⁻¹,
        (show N ≤ K from le_sup_left) hnaN⟩, hnaN⟩
    let q' : QK :=
      ⟨⟨a * ((q : K) : G) * a⁻¹,
        (show Q ≤ K from le_sup_right) hqaQ⟩, hqaQ⟩
    have hax : a * x * a⁻¹ = x := by
      calc
        a * x * a⁻¹ = x * a * a⁻¹ := by rw [hx.2 a ha]
        _ = x := by simp
    have hnq' : (n' : K) * (q' : K) = xK := by
      apply Subtype.ext
      change
        (a * ((n : K) : G) * a⁻¹) *
            (a * ((q : K) : G) * a⁻¹) = x
      calc
        (a * ((n : K) : G) * a⁻¹) *
              (a * ((q : K) : G) * a⁻¹) =
            a * (((n : K) : G) * ((q : K) : G)) * a⁻¹ := by group
        _ = a * x * a⁻¹ := by rw [hnqG]
        _ = x := hax
    have hpairs : (n', q') = (n, q) :=
      hcomp.1 (hnq'.trans hnq.symm)
    have hqconj : a * ((q : K) : G) * a⁻¹ = ((q : K) : G) := by
      have hqeq := congrArg Prod.snd hpairs
      exact congrArg (fun z : QK => ((z : K) : G)) hqeq
    calc
      a * ((q : K) : G) =
          (a * ((q : K) : G) * a⁻¹) * a := by group
      _ = ((q : K) : G) * a := by rw [hqconj]
  have hqOne : ((q : K) : G) = 1 := by
    apply Subgroup.mem_bot.mp
    rw [← hfixed]
    exact hqCent
  rw [← hnqG, hqOne, mul_one]
  exact n.property

/-- A common normalizer of `D` and `A` normalizes the internal
centralizer `C_D(A)`. -/
private theorem centralizerWithin_normalized_by_common_normalizer_embedding
    {G : Type u} [Group G] {X D A : Subgroup G}
    (hXD : X ≤ Subgroup.normalizer (D : Set G))
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) :
    X ≤ Subgroup.normalizer (centralizerWithin D A : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro x hx y hy
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hXD hx) y).mp hy.1, ?_⟩
  intro a ha
  have hxInvA : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normalizer (A : Set G)).inv_mem (hXA hx)
  have ha' : x⁻¹ * a * x ∈ A :=
    by
      simpa only [inv_inv] using
        (Subgroup.mem_normalizer_iff.mp hxInvA a).mp ha
  have hcomm := hy.2 (x⁻¹ * a * x) ha'
  calc
    a * (x * y * x⁻¹) =
        x * ((x⁻¹ * a * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * y * x⁻¹) * a := by group

/-- A rank-three elementary abelian subgroup contains a plane. -/
private theorem exists_rank_two_le_of_rank_three_embedding
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hE : IsElementaryAbelianOfRank p 3 E) :
    ∃ A : Subgroup G, A ≤ E ∧ IsElementaryAbelianOfRank p 2 A := by
  have hpTwo : p ^ 2 ≤ Nat.card E := by
    rw [hE.card_eq]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  obtain ⟨A₀, hA₀card⟩ :=
    Sylow.exists_subgroup_card_pow_prime_of_le_card
      (G := E) (Fact.out : p.Prime) hE.isPGroup hpTwo
  have hA₀ : IsElementaryAbelianOfRank p 2 A₀ := by
    letI : IsMulCommutative E := hE.commutative
    refine
      { isPGroup := hE.isPGroup.to_subgroup A₀
        commutative := by infer_instance
        pow_eq_one := ?_
        card_eq := hA₀card }
    intro x
    apply Subtype.ext
    exact hE.pow_eq_one (x : E)
  let A : Subgroup G := A₀.map E.subtype
  exact ⟨A, Subgroup.map_subtype_le A₀,
    hA₀.map_of_injective E.subtype E.subtype_injective⟩

/-- Every ambient Sylow subgroup at an alpha prime contains a conjugate of
the rank-three witness from the definition of `alphaPrimes`. -/
private theorem global_sylow_has_rank_three_of_mem_alpha_embedding
    {G : Type u} [Group G] [Finite G]
    {M : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hpAlpha : p ∈ alphaPrimes M) (P : Sylow p G) :
    HasElementaryAbelianRankAtLeast p 3 (P : Subgroup G) := by
  classical
  rcases hpAlpha with ⟨_hp, E, _hEM, hE⟩
  obtain ⟨R, hER⟩ := hE.isPGroup.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R P
  let C : Subgroup G := E.map (MulAut.conj g).toMonoidHom
  have hRmap :
      (R : Subgroup G).map (MulAut.conj g).toMonoidHom =
        (P : Subgroup G) := by
    change MulAut.conj g • (R : Subgroup G) = (P : Subgroup G)
    rw [← Sylow.coe_subgroup_smul, hg]
  exact ⟨C, (Subgroup.map_mono hER).trans_eq hRmap,
    hE.map_of_injective (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective⟩

/-- A subgroup of order `p` is contained in every nontrivial subgroup of a
cyclic `p`-group.  The proof identifies both prime-order subgroups with
`Omega_1`. -/
private theorem card_prime_subgroup_le_nontrivial_cyclic_pgroup_embedding
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {C X Y : Subgroup G}
    (hCp : IsPGroup p C) (hCcyclic : IsCyclic C)
    (hXC : X ≤ C) (hXcard : Nat.card X = p)
    (hXpow : ∀ x : X, (x : G) ^ p = 1)
    (hYC : Y ≤ C) (hYp : IsPGroup p Y) (hYne : Y ≠ ⊥) :
    X ≤ Y := by
  classical
  letI : IsCyclic C := hCcyclic
  let XC : Subgroup C := X.subgroupOf C
  let YC : Subgroup C := Y.subgroupOf C
  have hCcardNe : Nat.card C ≠ 1 := by
    intro hcard
    have hpC : p ∣ Nat.card C := by
      rw [← hXcard]
      exact Subgroup.card_dvd_of_le hXC
    rw [hcard] at hpC
    exact (Fact.out : p.Prime).not_dvd_one hpC
  let O : Subgroup C := omegaOne p C
  have hOcard : Nat.card O = p :=
    card_omegaOne_of_isCyclic_isPGroup Fact.out hCp hCcardNe
  have hXCO : XC ≤ O := by
    intro x hx
    apply mem_omegaOne_of_pow_eq_one
    let xX : X := ⟨((x : C) : G), hx⟩
    apply Subtype.ext
    exact hXpow xX
  have hXCcard : Nat.card XC = p := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hXC, hXcard]
  have hXCOeq : XC = O := by
    apply Subgroup.eq_of_le_of_card_ge hXCO
    rw [hXCcard, hOcard]
  have hYCp : IsPGroup p YC :=
    hYp.of_equiv (Subgroup.subgroupOfEquivOfLe hYC).symm
  have hYCcyclic : IsCyclic YC := Subgroup.isCyclic_of_le le_top
  letI : IsCyclic YC := hYCcyclic
  have hYCcardNe : Nat.card YC ≠ 1 := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hYC]
    intro hcard
    exact hYne (Subgroup.card_eq_one.mp hcard)
  let OY : Subgroup C := (omegaOne p YC).map YC.subtype
  have hOYcard : Nat.card OY = p := by
    dsimp [OY]
    rw [Subgroup.card_map_of_injective YC.subtype_injective]
    exact card_omegaOne_of_isCyclic_isPGroup
      Fact.out hYCp hYCcardNe
  have hOYleO : OY ≤ O := by
    rintro _ ⟨y, hy, rfl⟩
    apply mem_omegaOne_of_pow_eq_one
    have hyker : y ∈ (powMonoidHom p : YC →* YC).ker := by
      rw [← omegaOne_eq_powMonoidHom_ker]
      exact hy
    exact congrArg Subtype.val (MonoidHom.mem_ker.mp hyker)
  have hOYeqO : OY = O := by
    apply Subgroup.eq_of_le_of_card_ge hOYleO
    rw [hOYcard, hOcard]
  intro x hx
  let xC : C := ⟨x, hXC hx⟩
  have hxO : xC ∈ O := by
    rw [← hXCOeq]
    exact hx
  have hxOY : xC ∈ OY := by rw [hOYeqO]; exact hxO
  exact (Subgroup.map_subtype_le (omegaOne p YC)) hxOY

/-- The fixed-point calculation at `BGsection12.v`, lines 2551--2627.
An invariant Sylow subgroup of `alpha(M)` supplies a critical subgroup.
The normalizer of its `Q`-fixed points, first before and then after
quotienting by those fixed points, gives the two prime-order Frobenius
contradictions. -/
private theorem critical_frobenius_fixed_point_embedding
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M P Q : Subgroup G} {p q : ℕ}
    [Fact p.Prime] [Fact q.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hAlphaNe : alphaCore M ≠ ⊥)
    (hpNotAlpha : p ∉ alphaPrimes M)
    (hqNotAlpha : q ∉ alphaPrimes M)
    (hqp : q ≠ p)
    (hP : IsElementaryAbelianOfRank p 1 P)
    (hQq : IsPGroup q Q)
    (hPM : P ≤ M) (hQM : Q ≤ M)
    (hPNQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hregular : centralizerWithin Q P = ⊥)
    (hRankQ : ∀ r : ℕ, r.Prime →
      ¬ HasElementaryAbelianRankAtLeast r 2
        (centralizerWithin (alphaCore M) Q))
    (hRankP : ∀ r : ℕ, r.Prime →
      ¬ HasElementaryAbelianRankAtLeast r 2
        (centralizerWithin (alphaCore M) P)) :
    centralizerWithin (alphaCore M) P ≠ ⊥ ∧
      centralizerWithin (alphaCore M) (Q ⊔ P) = ⊥ := by
  classical
  let A : Subgroup G := alphaCore M
  let J : Subgroup G := Q ⊔ P
  let C : Subgroup G := centralizerWithin A J
  have hPp : IsPGroup p P := hP.isPGroup
  have hJM : J ≤ M := sup_le hQM hPM
  have hMnormA : M ≤ Subgroup.normalizer (A : Set G) := by
    dsimp [A]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (alphaCore_le M)).mp (alphaCore_normal M)
  have hJnormA : J ≤ Subgroup.normalizer (A : Set G) :=
    hJM.trans hMnormA
  have hcopQP : (Nat.card Q).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne q p hqp Q P hQq hPp
  have hdisQP : Disjoint Q P :=
    Subgroup.disjoint_of_coprime_natCard hcopQP
  have hJcard : Nat.card J = Nat.card Q * Nat.card P := by
    have hcard :=
      natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        (H := P) (K := Q) hdisQP.symm hPNQ
    simpa [J, sup_comm, Nat.mul_comm] using hcard
  have hJalphaCompl :
      IsPiNumber (alphaPrimes M)ᶜ (Nat.card J) := by
    rw [hJcard]
    exact (hQq.isPiNumber_natCard hqNotAlpha).mul
      (hPp.isPiNumber_natCard hpNotAlpha)
  have hcopAJ : (Nat.card A).Coprime (Nat.card J) :=
    (alphaCore_isPiNumber M).coprime_compl hJalphaCompl
  have hAsol : IsSolvable A := by
    letI : IsSolvable M := mmax_sol hM
    exact isSolvable_of_injective
      (Subgroup.inclusion (show A ≤ M by
        simpa [A] using alphaCore_le M))
      (Subgroup.inclusion_injective (show A ≤ M by
        simpa [A] using alphaCore_le M))

  let W : Subgroup G := if C = ⊥ then A else C
  have hWne : W ≠ ⊥ := by
    by_cases hCbot : C = ⊥
    · simpa [W, hCbot, A] using hAlphaNe
    · simpa [W, hCbot]
  have hWcardNe : Nat.card W ≠ 1 :=
    (W.one_lt_card_iff_ne_bot.mpr hWne).ne'
  obtain ⟨r, hr, hrW⟩ := Nat.exists_prime_and_dvd hWcardNe
  letI : Fact r.Prime := ⟨hr⟩
  have hrAcard : r ∣ Nat.card A := by
    by_cases hCbot : C = ⊥
    · simpa [W, hCbot] using hrW
    · have hrC : r ∣ Nat.card C := by simpa [W, hCbot] using hrW
      exact hrC.trans (Subgroup.card_dvd_of_le
        (show C ≤ A from centralizerWithin_le_left A J))
  have hrAlpha : r ∈ alphaPrimes M := by
    exact alphaCore_isPiNumber M hr hrAcard
  have hrp : r ≠ p := by
    intro hrp
    subst r
    exact hpNotAlpha hrAlpha
  have hrq : r ≠ q := by
    intro hrq
    subst r
    exact hqNotAlpha hrAlpha

  let Rc : Sylow r C := Classical.choice Sylow.nonempty
  let X : Subgroup G := (Rc : Subgroup C).map C.subtype
  have hXC : X ≤ C := Subgroup.map_subtype_le _
  have hXA : X ≤ A := hXC.trans (centralizerWithin_le_left A J)
  have hXr : IsPGroup r X := Rc.isPGroup'.map C.subtype
  have hJcentX : J ≤ Subgroup.centralizer (X : Set G) := by
    intro j hj
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact ((hXC hx).2 j hj).symm
  have hJnormX : J ≤ Subgroup.normalizer (X : Set G) :=
    hJcentX.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  obtain ⟨RA, hJnormR, hXR⟩ :=
    exists_normalized_sylow_ge_of_coprime_of_isSolvable
      (p := r) hJnormA hcopAJ hAsol hXA hXr hJnormX
  let R : Subgroup G := (RA : Subgroup A).map A.subtype
  have hJnormR' : J ≤ Subgroup.normalizer (R : Set G) := by
    simpa [R] using hJnormR
  have hXR' : X ≤ R := by simpa [R] using hXR
  have hRA : R ≤ A := Subgroup.map_subtype_le _
  have hRM : R ≤ M := hRA.trans (by simpa [A] using alphaCore_le M)
  have hRr : IsPGroup r R := RA.isPGroup'.map A.subtype
  have hRne : R ≠ ⊥ := by
    intro hRbot
    have hRAbot : (RA : Subgroup A) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective
        (RA : Subgroup A) A.subtype_injective).mp (by simpa [R] using hRbot)
    exact RA.ne_bot_of_dvd_card hrAcard hRAbot
  have hRcardNe : Nat.card R ≠ 1 :=
    (R.one_lt_card_iff_ne_bot.mpr hRne).ne'
  obtain ⟨RG, hRG⟩ :=
    exists_sylow_eq_map_of_sylow_hall_embedding hr
      (Malpha_Hall_G hM) hrAlpha RA
  have hRrankThree : HasElementaryAbelianRankAtLeast r 3 R := by
    simpa [R, hRG] using
      global_sylow_has_rank_three_of_mem_alpha_embedding hrAlpha RG
  have hCRQne : centralizerWithin R Q ≠ R := by
    intro hfull
    rcases hRrankThree with ⟨E, hER, hE⟩
    obtain ⟨E₂, hE₂E, hE₂⟩ :=
      exists_rank_two_le_of_rank_three_embedding hE
    apply hRankQ r hr
    refine ⟨E₂, ?_, hE₂⟩
    intro x hx
    have hxR : x ∈ R := hER (hE₂E hx)
    have hxCent : x ∈ centralizerWithin R Q := by
      rw [hfull]
      exact hxR
    exact ⟨hRA hxR, hxCent.2⟩

  obtain ⟨H, hHchar, _hHcomm, _hHclass, hHexp, hHfix⟩ :=
    Submission.OddOrder.BG.Section01.critical_odd
      hRr (mFT_odd R) hRcardNe
  letI : H.Characteristic := hHchar
  have hHne : H ≠ ⊥ := by
    intro hHbot
    haveI : Subsingleton H :=
      ⟨fun x y => by
        apply Subtype.ext
        have hx : (x : R) = 1 := by
          apply Subgroup.mem_bot.mp
          rw [← hHbot]
          exact x.property
        have hy : (y : R) = 1 := by
          apply Subgroup.mem_bot.mp
          rw [← hHbot]
          exact y.property
        exact hx.trans hy.symm⟩
    have hExpOne : Monoid.exponent H = 1 :=
      Monoid.exp_eq_one_of_subsingleton
    exact hr.ne_one (hHexp.symm.trans hExpOne)
  let R1 : Subgroup G := H.map R.subtype
  have hR1R : R1 ≤ R := Subgroup.map_subtype_le _
  have hR1A : R1 ≤ A := hR1R.trans hRA
  have hR1r : IsPGroup r R1 := (hRr.to_subgroup H).map R.subtype
  have hR1ne : R1 ≠ ⊥ := by
    intro hbot
    exact hHne ((Subgroup.map_eq_bot_iff_of_injective
      H R.subtype_injective).mp (by simpa [R1] using hbot))
  have hJnormR1 : J ≤ Subgroup.normalizer (R1 : Set G) :=
    hJnormR'.trans
      (by simpa [R1] using
        characteristic_map_subtype_le_normalizer_embedding R H)
  have hQnormR : Q ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_left.trans hJnormR'
  have hPnormR : P ≤ Subgroup.normalizer (R : Set G) :=
    le_sup_right.trans hJnormR'
  have hQnormR1 : Q ≤ Subgroup.normalizer (R1 : Set G) :=
    le_sup_left.trans hJnormR1
  have hPnormR1 : P ≤ Subgroup.normalizer (R1 : Set G) :=
    le_sup_right.trans hJnormR1
  let eR1 : H ≃* R1 :=
    H.equivMapOfInjective R.subtype R.subtype_injective
  have hR1exp : Monoid.exponent R1 = r :=
    (Monoid.exponent_eq_of_mulEquiv eR1).symm.trans hHexp

  have hCR1Qne : centralizerWithin R1 Q ≠ R1 := by
    intro hfull
    let i : Q →* Subgroup.normalizer (R : Set G) :=
      Subgroup.inclusion hQnormR
    let rho : Q →* MulAut R := R.normalizerMonoidHom.comp i
    let rhoFix : Q →* fixingSubgroup (MulAut R) (H : Set R) :=
      { toFun := fun z => ⟨rho z, by
          rw [mem_fixingSubgroup_iff]
          intro x hx
          apply Subtype.ext
          have hxR1 : ((x : R) : G) ∈ R1 := ⟨x, hx, rfl⟩
          have hxCent : ((x : R) : G) ∈ centralizerWithin R1 Q := by
            rw [hfull]
            exact hxR1
          have hcomm := hxCent.2 (z : G) z.property
          change (z : G) * (x : R) * (z : G)⁻¹ = (x : R)
          calc
            (z : G) * (x : R) * (z : G)⁻¹ =
                (x : R) * (z : G) * (z : G)⁻¹ := by rw [hcomm]
            _ = (x : R) := by simp⟩
        map_one' := by
          apply Subtype.ext
          exact rho.map_one
        map_mul' := fun a b => by
          apply Subtype.ext
          exact rho.map_mul a b }
    have hrhoFix (z : Q) : rhoFix z = 1 :=
      apply_eq_one_of_isPGroup rhoFix hrq hQq hHfix z
    have hQcentR : Q ≤ Subgroup.centralizer (R : Set G) := by
      intro z hz
      have hrhoOne : rho ⟨z, hz⟩ = 1 :=
        congrArg
          (fun a : fixingSubgroup (MulAut R) (H : Set R) =>
            (a : MulAut R)) (hrhoFix ⟨z, hz⟩)
      have hker : i ⟨z, hz⟩ ∈ R.normalizerMonoidHom.ker := by
        rw [MonoidHom.mem_ker]
        exact hrhoOne
      rw [Subgroup.normalizerMonoidHom_ker] at hker
      exact hker
    apply hCRQne
    apply le_antisymm (centralizerWithin_le_left R Q)
    intro x hx
    refine ⟨hx, ?_⟩
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hQcentR hz) x hx).symm

  let R0 : Subgroup G := centralizerWithin R1 Q
  have hR0R1 : R0 ≤ R1 := centralizerWithin_le_left R1 Q
  have hJnormQ : J ≤ Subgroup.normalizer (Q : Set G) :=
    sup_le Subgroup.le_normalizer hPNQ
  have hJnormR0 : J ≤ Subgroup.normalizer (R0 : Set G) := by
    dsimp [R0]
    exact centralizerWithin_normalized_by_common_normalizer_embedding
      hJnormR1 hJnormQ
  let N : Subgroup G := R1 ⊓ Subgroup.normalizer (R0 : Set G)
  have hNR1 : N ≤ R1 := inf_le_left
  have hNnormR0 : N ≤ Subgroup.normalizer (R0 : Set G) := inf_le_right
  have hR0N : R0 ≤ N := le_inf hR0R1 Subgroup.le_normalizer
  have hJnormN : J ≤ Subgroup.normalizer (N : Set G) := by
    apply (le_inf hJnormR1
      (hJnormR0.trans Subgroup.le_normalizer)).trans
    exact Subgroup.inf_normalizer_le_normalizer_inf
  have hQnormN : Q ≤ Subgroup.normalizer (N : Set G) :=
    le_sup_left.trans hJnormN
  have hPnormN : P ≤ Subgroup.normalizer (N : Set G) :=
    le_sup_right.trans hJnormN
  have hNr : IsPGroup r N := hR1r.to_le hNR1
  have hdisNQ : Disjoint N Q :=
    IsPGroup.disjoint_of_ne r q hrq N Q hNr hQq
  let K : Subgroup G := N ⊔ Q
  have hKM : K ≤ M := sup_le (hNR1.trans (hR1A.trans
    (by simpa [A] using alphaCore_le M))) hQM
  have hPnormK : P ≤ Subgroup.normalizer (K : Set G) := by
    apply (le_inf hPnormN hPNQ).trans
    exact Subgroup.normalizer_inf_normalizer_le_normalizer_sup N Q
  have hKcard : Nat.card K = Nat.card N * Nat.card Q := by
    have hcard :=
      natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        (H := Q) (K := N) hdisNQ.symm hQnormN
    simpa [K, sup_comm, Nat.mul_comm] using hcard
  have hcopNP : (Nat.card N).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne r p hrp N P hNr hPp
  have hcopKP : (Nat.card K).Coprime (Nat.card P) := by
    rw [hKcard]
    exact hcopNP.mul_left hcopQP
  have hdisKP : Disjoint K P :=
    Subgroup.disjoint_of_coprime_natCard hcopKP
  have hCentKleN : centralizerWithin K P ≤ N := by
    simpa [K] using
      centralizerWithin_sup_le_left_of_fixed_right_embedding
        hQnormN hPnormN hPNQ hdisNQ hregular

  let F : Subgroup G := K ⊔ P
  let KF : Subgroup F := K.subgroupOf F
  let PF : Subgroup F := P.subgroupOf F
  have hFM : F ≤ M := sup_le hKM hPM
  have hFnormK : F ≤ Subgroup.normalizer (K : Set G) :=
    sup_le Subgroup.le_normalizer hPnormK
  letI : KF.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hFnormK
  have hcomp : KF.IsComplement' PF := by
    simpa [KF, PF, F] using
      subgroupOf_sup_isComplement_embedding hPnormK hdisKP
  have hPFprime : (Nat.card PF).Prime := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq (show P ≤ F from le_sup_right),
      hP.card_eq, pow_one]
    exact Fact.out
  have hsolF : IsSolvable F :=
    mFT_sol (lt_of_le_of_lt hFM (mmax_proper hM))
  have hKnormR0 : K ≤ Subgroup.normalizer (R0 : Set G) :=
    sup_le hNnormR0 (le_sup_left.trans hJnormR0)
  have hPnormR0 : P ≤ Subgroup.normalizer (R0 : Set G) :=
    le_sup_right.trans hJnormR0
  have hFnormR0 : F ≤ Subgroup.normalizer (R0 : Set G) :=
    sup_le hKnormR0 hPnormR0
  let R0F : Subgroup F := R0.subgroupOf F
  let NF : Subgroup F := N.subgroupOf F
  let QF : Subgroup F := Q.subgroupOf F
  letI : R0F.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hFnormR0
  have hR0FNF : R0F ≤ NF := by
    intro x hx
    exact hR0N hx
  have hNFKF : NF ≤ KF := by
    intro x hx
    exact (show N ≤ K from le_sup_left) hx
  have hQFKF : QF ≤ KF := by
    intro x hx
    exact (show Q ≤ K from le_sup_right) hx
  let qF : F →* F ⧸ R0F := QuotientGroup.mk' R0F
  let Nbar : Subgroup (F ⧸ R0F) := NF.map qF
  let Qbar : Subgroup (F ⧸ R0F) := QF.map qF
  let Kbar : Subgroup (F ⧸ R0F) := KF.map qF
  have hNbarKbar : Nbar ≤ Kbar := Subgroup.map_mono hNFKF
  have hQbarKbar : Qbar ≤ Kbar := Subgroup.map_mono hQFKF
  have hNFr : IsPGroup r NF :=
    hNr.of_equiv (Subgroup.subgroupOfEquivOfLe
      (show N ≤ F from le_sup_left.trans le_sup_left)).symm
  have hQFq : IsPGroup q QF :=
    hQq.of_equiv (Subgroup.subgroupOfEquivOfLe
      (show Q ≤ F from le_sup_right.trans le_sup_left)).symm
  have hNbarR : IsPGroup r Nbar := hNFr.map qF
  have hQbarQ : IsPGroup q Qbar := hQFq.map qF
  have hR0r : IsPGroup r R0 := hR1r.to_le hR0R1
  have hR0Fr : IsPGroup r R0F :=
    hR0r.of_equiv (Subgroup.subgroupOfEquivOfLe
      (show R0 ≤ F from hR0N.trans
        (le_sup_left.trans le_sup_left))).symm
  have hcopR0FQF : (Nat.card R0F).Coprime (Nat.card QF) :=
    IsPGroup.coprime_card_of_ne r q hrq R0F QF hR0Fr hQFq

  have hKbarNonNil : ¬ Group.IsNilpotent Kbar := by
    intro hnil
    letI : Group.IsNilpotent Kbar := hnil
    let Nb : Subgroup Kbar := Nbar.subgroupOf Kbar
    let Qb : Subgroup Kbar := Qbar.subgroupOf Kbar
    have hNbr : IsPGroup r Nb :=
      hNbarR.of_equiv
        (Subgroup.subgroupOfEquivOfLe hNbarKbar).symm
    have hQbq : IsPGroup q Qb :=
      hQbarQ.of_equiv
        (Subgroup.subgroupOfEquivOfLe hQbarKbar).symm
    have hcommNb : Nb ≤ Subgroup.centralizer (Qb : Set Kbar) :=
      nilpotent_subgroups_commute_of_coprime_pi
        (pi := ({r} : Set ℕ))
        (hNbr.isPiNumber_natCard (by simp))
        (hQbq.isPiNumber_natCard (by simp [Ne.symm hrq]))
    have hcommbar : Nbar ≤ Subgroup.centralizer (Qbar : Set (F ⧸ R0F)) := by
      intro n hn
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      let nK : Kbar := ⟨n, hNbarKbar hn⟩
      let zK : Kbar := ⟨z, hQbarKbar hz⟩
      have hcomm := Subgroup.mem_centralizer_iff.mp
        (hcommNb (show nK ∈ Nb from hn)) zK
        (show zK ∈ Qb from hz)
      exact congrArg Subtype.val hcomm
    have hcentbar : centralizerWithin Nbar Qbar = Nbar := by
      apply le_antisymm (centralizerWithin_le_left Nbar Qbar)
      intro n hn
      refine ⟨hn, ?_⟩
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp (hcommbar hn) z hz
    letI : Group.IsNilpotent QF := hQFq.isNilpotent
    letI : IsSolvable QF := by infer_instance
    have hmapCent :=
      map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
        (N := R0F) (Y := NF) (R := QF) hR0FNF hcopR0FQF
    have hmapEq :
        (centralizerWithin NF QF).map qF = NF.map qF := by
      simpa [qF, Nbar, Qbar, hcentbar] using hmapCent
    have hR0FCent : R0F ≤ centralizerWithin NF QF := by
      intro x hx
      refine ⟨hR0FNF hx, ?_⟩
      intro z hz
      apply Subtype.ext
      exact hx.2 ((z : F) : G) hz
    have hkerCent : qF.ker ≤ centralizerWithin NF QF := by
      simpa [qF, QuotientGroup.ker_mk'] using hR0FCent
    have hkerNF : qF.ker ≤ NF := by
      simpa [qF, QuotientGroup.ker_mk'] using hR0FNF
    have hcentNF : centralizerWithin NF QF = NF := by
      calc
        centralizerWithin NF QF =
            ((centralizerWithin NF QF).map qF).comap qF :=
          (Subgroup.comap_map_eq_self hkerCent).symm
        _ = (NF.map qF).comap qF := by rw [hmapEq]
        _ = NF := Subgroup.comap_map_eq_self hkerNF
    have hQcentN : Q ≤ Subgroup.centralizer (N : Set G) := by
      intro z hz
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      let zF : F := ⟨z,
        (show Q ≤ F from le_sup_right.trans le_sup_left) hz⟩
      let nF : F := ⟨n,
        (show N ≤ F from le_sup_left.trans le_sup_left) hn⟩
      have hnCent : nF ∈ centralizerWithin NF QF := by
        rw [hcentNF]
        exact hn
      exact (congrArg Subtype.val (hnCent.2 zF hz)).symm
    let CIn : Subgroup R1 := centralizerIn R1 Q
    let R0In : Subgroup R1 := R0.subgroupOf R1
    have hCInEq : CIn = R0In := by
      apply Subgroup.map_injective R1.subtype_injective
      rw [centralizerIn_map_subtype,
        Subgroup.map_subgroupOf_eq_of_le hR0R1]
    have hNormMap :
        (Subgroup.normalizer (CIn : Set R1)).map R1.subtype = N := by
      rw [hCInEq]
      dsimp [R0In, N]
      rw [← Subgroup.subgroupOf_normalizer_eq hR0R1,
        Subgroup.subgroupOf_map_subtype, inf_comm]
    letI : Group.IsNilpotent R1 := hR1r.isNilpotent
    have hQcentR1 : Q ≤ Subgroup.centralizer (R1 : Set G) := by
      apply centralizes_of_centralizes_normalizer_centralizer
        (H := R1) (A := Q)
      rw [show
        (Subgroup.normalizer (centralizerIn R1 Q : Set R1)).map
            R1.subtype = N by
          simpa [CIn] using hNormMap]
      exact hQcentN
    apply hCR1Qne
    apply le_antisymm (centralizerWithin_le_left R1 Q)
    intro x hx
    refine ⟨hx, ?_⟩
    intro z hz
    exact (Subgroup.mem_centralizer_iff.mp (hQcentR1 hz) x hx).symm

  let CP1 : Subgroup G := centralizerWithin R1 P
  have hCP1R1 : CP1 ≤ R1 := centralizerWithin_le_left R1 P
  have hCentKleCP1 : centralizerWithin K P ≤ CP1 := by
    intro x hx
    exact ⟨hNR1 (hCentKleN hx), hx.2⟩
  have hCP1ne : CP1 ≠ ⊥ := by
    intro hCP1bot
    have hCentKbot : centralizerWithin K P = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      have hxCP1 := hCentKleCP1 hx
      rw [hCP1bot] at hxCP1
      exact hxCP1
    have hCentKFPF : centralizerWithin KF PF = ⊥ := by
      apply le_antisymm _ bot_le
      intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      have hxAmbient : ((x : F) : G) ∈ centralizerWithin K P := by
        refine ⟨hx.1, ?_⟩
        intro z hz
        let zF : F := ⟨z, (show P ≤ F from le_sup_right) hz⟩
        exact congrArg Subtype.val (hx.2 zF hz)
      exact Subgroup.mem_bot.mp (by rw [← hCentKbot]; exact hxAmbient)
    have hnilKF : Group.IsNilpotent KF :=
      Submission.OddOrder.BG.Section03.prime_Frobenius_sol_kernel_nil
        hcomp (show KF.Normal from inferInstance) hsolF
        hPFprime hCentKFPF
    letI : Group.IsNilpotent KF := hnilKF
    have hnilKbar : Group.IsNilpotent Kbar := by
      exact Group.nilpotent_of_surjective
        (qF.subgroupMap KF) (qF.subgroupMap_surjective KF)
    exact hKbarNonNil hnilKbar
  have hCentPNe : centralizerWithin A P ≠ ⊥ := by
    intro hbot
    apply hCP1ne
    apply le_antisymm _ bot_le
    intro x hx
    have hxA : x ∈ centralizerWithin A P :=
      ⟨hR1A hx.1, hx.2⟩
    rw [hbot] at hxA
    exact hxA

  refine ⟨by simpa [A] using hCentPNe, ?_⟩
  change C = ⊥
  by_contra hCne
  have hrC : r ∣ Nat.card C := by
    simpa [W, hCne] using hrW
  have hRcne : (Rc : Subgroup C) ≠ ⊥ := Rc.ne_bot_of_dvd_card hrC
  have hXne : X ≠ ⊥ := by
    intro hXbot
    exact hRcne ((Subgroup.map_eq_bot_iff_of_injective
      (Rc : Subgroup C) C.subtype_injective).mp (by simpa [X] using hXbot))
  let CRJ : Subgroup G := centralizerWithin R J
  have hXCRJ : X ≤ CRJ := by
    intro x hx
    exact ⟨hXR' hx, (hXC hx).2⟩
  have hCRJne : CRJ ≠ ⊥ := by
    intro hbot
    apply hXne
    apply le_antisymm _ bot_le
    intro x hx
    have hx' := hXCRJ hx
    rw [hbot] at hx'
    exact hx'
  let CRP : Subgroup G := centralizerWithin R P
  have hCRPr : IsPGroup r CRP :=
    hRr.to_le (centralizerWithin_le_left R P)
  have hCRPnoPlane :
      ¬ ∃ E : Subgroup CRP, IsElementaryAbelianOfRank r 2 E := by
    rintro ⟨E, hE⟩
    let EG : Subgroup G := E.map CRP.subtype
    apply hRankP r hr
    exact ⟨EG,
      (Subgroup.map_subtype_le E).trans
        (centralizerWithin_mono_left hRA),
      hE.map_of_injective CRP.subtype CRP.subtype_injective⟩
  have hCRPcyclic : IsCyclic CRP :=
    (Submission.OddOrder.BG.Section04.odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hCRPr (mFT_odd CRP)).mpr hCRPnoPlane
  have hCP1CRP : CP1 ≤ CRP := by
    intro x hx
    exact ⟨hR1R hx.1, hx.2⟩
  have hCP1r : IsPGroup r CP1 := hR1r.to_le hCP1R1
  have hCP1cyclic : IsCyclic CP1 := by
    letI : IsCyclic CRP := hCRPcyclic
    exact Subgroup.isCyclic_of_le hCP1CRP
  have hCP1pow : ∀ x : CP1, (x : G) ^ r = 1 := by
    intro x
    let xR1 : R1 := ⟨(x : G), hCP1R1 x.property⟩
    exact congrArg Subtype.val
      (by simpa [hR1exp] using Monoid.pow_exponent_eq_one xR1)
  have hCP1card : Nat.card CP1 = r := by
    letI : IsCyclic CP1 := hCP1cyclic
    have hcardNe : Nat.card CP1 ≠ 1 :=
      (CP1.one_lt_card_iff_ne_bot.mpr hCP1ne).ne'
    have hOmegaCard :=
      card_omegaOne_of_isCyclic_isPGroup hr hCP1r hcardNe
    have hOmegaTop : omegaOne r CP1 = ⊤ := by
      apply top_unique
      intro x _
      apply mem_omegaOne_of_pow_eq_one
      apply Subtype.ext
      exact hCP1pow x
    rw [hOmegaTop, Subgroup.card_top] at hOmegaCard
    exact hOmegaCard
  have hCRJCRP : CRJ ≤ CRP :=
    centralizerWithin_antitone_right (show P ≤ J from le_sup_right)
  have hCRJr : IsPGroup r CRJ := hRr.to_le
    (centralizerWithin_le_left R J)
  have hCP1CRJ : CP1 ≤ CRJ :=
    card_prime_subgroup_le_nontrivial_cyclic_pgroup_embedding
      hCRPr hCRPcyclic hCP1CRP hCP1card hCP1pow
      hCRJCRP hCRJr hCRJne
  have hCP1R0 : CP1 ≤ R0 := by
    intro x hx
    have hxJ := hCP1CRJ hx
    exact ⟨hCP1R1 hx, fun z hz =>
      hxJ.2 z ((show Q ≤ J from le_sup_left) hz)⟩
  have hCentKleR0 : centralizerWithin K P ≤ R0 :=
    hCentKleCP1.trans hCP1R0
  have hCentKFPFleR0F : centralizerWithin KF PF ≤ R0F := by
    intro x hx
    have hxAmbient : ((x : F) : G) ∈ centralizerWithin K P := by
      refine ⟨hx.1, ?_⟩
      intro z hz
      let zF : F := ⟨z, (show P ≤ F from le_sup_right) hz⟩
      exact congrArg Subtype.val (hx.2 zF hz)
    exact hCentKleR0 hxAmbient
  have hPFp : IsPGroup p PF :=
    hPp.of_equiv (Subgroup.subgroupOfEquivOfLe
      (show P ≤ F from le_sup_right)).symm
  letI : Group.IsNilpotent PF := hPFp.isNilpotent
  letI : IsSolvable PF := by infer_instance
  have hcopR0FPF : (Nat.card R0F).Coprime (Nat.card PF) := by
    exact IsPGroup.coprime_card_of_ne r p hrp R0F PF hR0Fr hPFp
  have hmapCentP :=
    map_centralizerWithin_quotient_eq_of_coprime_of_solvable_right
      (N := R0F) (Y := KF) (R := PF)
      (show R0F ≤ KF from fun x hx =>
        (hR0N.trans le_sup_left) hx) hcopR0FPF
  have hmapCentBot : (centralizerWithin KF PF).map qF = ⊥ := by
    apply (Subgroup.map_eq_bot_iff (centralizerWithin KF PF)).mpr
    simpa [qF, QuotientGroup.ker_mk'] using hCentKFPFleR0F
  have hCentKbarPbar :
      centralizerWithin Kbar (PF.map qF) = ⊥ := by
    rw [← hmapCentP, hmapCentBot]
  have hcompbar : Kbar.IsComplement' (PF.map qF) := by
    exact Subgroup.IsComplement'.quotient_isComplement hcomp
      (show R0F ≤ KF from fun x hx =>
        (hR0N.trans le_sup_left) hx)
  have hPbarCard : Nat.card (PF.map qF) = Nat.card PF := by
    let f : PF → PF.map qF := qF.subgroupMap PF
    exact (Nat.card_congr (Equiv.ofBijective f
      ⟨Subgroup.IsComplement'.quotientRight_subgroupMap_injective
          hcomp (show R0F ≤ KF from fun x hx =>
            (hR0N.trans le_sup_left) hx),
        qF.subgroupMap_surjective PF⟩)).symm
  have hPbarPrime : (Nat.card (PF.map qF)).Prime := by
    rw [hPbarCard]
    exact hPFprime
  letI : Kbar.Normal :=
    Subgroup.Normal.map (show KF.Normal from inferInstance) qF
      (QuotientGroup.mk'_surjective R0F)
  have hsolQuot : IsSolvable (F ⧸ R0F) := by
    letI : IsSolvable F := hsolF
    exact isSolvable_quotient_of_isSolvable R0F
  have hnilKbar : Group.IsNilpotent Kbar :=
    Submission.OddOrder.BG.Section03.prime_Frobenius_sol_kernel_nil
      hcompbar (show Kbar.Normal from inferInstance) hsolQuot
      hPbarPrime hCentKbarPbar
  exact hKbarNonNil hnilKbar

/-- `BGsection12.v: cent_Malpha_reg_tau1`, Lemma 12.18.

MathComp's membership `P \in 'E_p^1(M)` is split into `P ≤ M` and the
rank-one elementary-abelian predicate.  We state the primality of `q`
explicitly: unlike MathComp's prime-local notation, Lean's `Sylow q M` and
`IsPGroup q Q` types are meaningful for composite `q`.  The generated
product `Q <*> P` is the subgroup supremum `Q ⊔ P`. -/
theorem cent_Malpha_reg_tau1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M P Q : Subgroup G} {p q : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hpTau : p ∈ tau1Primes M)
    (hq : q.Prime)
    (hqp : q ≠ p)
    (hPM : P ≤ M)
    (hP : IsElementaryAbelianOfRank p 1 P)
    (hQne : Q ≠ ⊥)
    (hPNQ : P ≤ Subgroup.normalizer (Q : Set G))
    (hregular : centralizerWithin Q P = ⊥)
    (hnonunique :
      minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (Q : Set G) : Set G) ≠ {M}) :
    (alphaCore M ≠ ⊥ →
        q ∉ alphaPrimes M →
        IsPGroup q Q →
        Q ≤ M →
        centralizerWithin (alphaCore M) P ≠ ⊥ ∧
          centralizerWithin (alphaCore M) (Q ⊔ P) = ⊥) ∧
      (IsSylowSubgroupOf q Q M →
        alphaPrimes M = betaPrimes M ∧
          alphaCore M ≠ ⊥ ∧
          q ∉ alphaPrimes M ∧
          centralizerWithin (alphaCore M) P ≠ ⊥ ∧
          centralizerWithin (alphaCore M) (Q ⊔ P) = ⊥) := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  letI : Fact q.Prime := ⟨hq⟩
  have hPp : IsPGroup p P := hP.isPGroup
  have hPne : P ≠ ⊥ := hP.ne_bot
  have hPproper : P < ⊤ := mFT_pgroup_proper P hPp
  have hNPproper : Subgroup.normalizer (P : Set G) < ⊤ :=
    mFT_norm_proper P hPne hPproper
  have hpNotAlpha : p ∉ alphaPrimes M := by
    intro hpAlpha
    exact hpTau.2.1 (alpha_sub_sigma hM hpAlpha)
  have hPalphaCompl :
      IsPiNumber (alphaPrimes M)ᶜ (Nat.card P) :=
    hPp.isPiNumber_natCard hpNotAlpha
  have hNPnotM : ¬ Subgroup.normalizer (P : Set G) ≤ M := by
    intro hNPM
    rcases prime_class_mmax_norm hM hPp hNPM with hpSigma | hpTau2
    · exact hpTau.2.1 hpSigma
    · exact (tau2'1 M hpTau) hpTau2
  have hRankP : ∀ r : ℕ, r.Prime →
      ¬ HasElementaryAbelianRankAtLeast r 2
        (centralizerWithin (alphaCore M) P) := by
    intro r hr hRank
    have hCentUnique := cent_alpha'_uniq hM hPM hPalphaCompl
      ⟨r, hr, hRank⟩
    have hCentFamily := def_uniq_mmax hCentUnique hM
      (centralizerWithin_le_left M P)
    apply hNPnotM
    exact sub_uniq_mmax hCentFamily
      (inf_le_right.trans
        (Subgroup.centralizer_le_normalizer (P : Set G)))
      hNPproper

  have part_a :
      alphaCore M ≠ ⊥ →
        q ∉ alphaPrimes M →
        IsPGroup q Q →
        Q ≤ M →
        centralizerWithin (alphaCore M) P ≠ ⊥ ∧
          centralizerWithin (alphaCore M) (Q ⊔ P) = ⊥ := by
    intro hAlphaNe hqNotAlpha hQq hQM
    have hQproper : Q < ⊤ := mFT_pgroup_proper Q hQq
    have hNQproper : Subgroup.normalizer (Q : Set G) < ⊤ :=
      mFT_norm_proper Q hQne hQproper
    have hQalphaCompl :
        IsPiNumber (alphaPrimes M)ᶜ (Nat.card Q) :=
      hQq.isPiNumber_natCard hqNotAlpha
    have hRankQ : ∀ r : ℕ, r.Prime →
        ¬ HasElementaryAbelianRankAtLeast r 2
          (centralizerWithin (alphaCore M) Q) := by
      intro r hr hRank
      have hCentUnique := cent_alpha'_uniq hM hQM hQalphaCompl
        ⟨r, hr, hRank⟩
      have hCentFamily := def_uniq_mmax hCentUnique hM
        (centralizerWithin_le_left M Q)
      exact hnonunique
        (def_uniq_mmaxS
          (inf_le_right.trans
            (Subgroup.centralizer_le_normalizer (Q : Set G)))
          hNQproper hCentFamily)
    exact critical_frobenius_fixed_point_embedding hM hAlphaNe
      hpNotAlpha hqNotAlpha hqp hP hQq hPM hQM hPNQ hregular
      hRankQ hRankP

  refine ⟨part_a, ?_⟩
  intro hQsylow
  have hQM : Q ≤ M := IsSylowSubgroupOf.le_right hQsylow
  have hQq : IsPGroup q Q := by
    rcases hQsylow with ⟨SQ, rfl⟩
    exact SQ.isPGroup'.map M.subtype
  have hQproper : Q < ⊤ := mFT_pgroup_proper Q hQq
  have hNQproper : Subgroup.normalizer (Q : Set G) < ⊤ :=
    mFT_norm_proper Q hQne hQproper
  have hcopQP : (Nat.card Q).Coprime (Nat.card P) :=
    IsPGroup.coprime_card_of_ne q p hqp Q P hQq hPp
  letI : Group.IsNilpotent Q := hQq.isNilpotent
  have hQcomm : Q ≤ ⁅P, Q⁆ := by
    have hdecomp :
        Q ≤ ⁅P, Q⁆ ⊔ centralizerWithin Q P :=
      le_commutator_sup_centralizerWithin_of_coprime hPNQ hcopQP
    simpa [hregular] using hdecomp
  let D : Subgroup M := _root_.commutator M
  have hQderG : Q ≤ D.map M.subtype := by
    rw [show D.map M.subtype = ⁅M, M⁆ by
      exact M.map_subtype_commutator]
    exact hQcomm.trans (Subgroup.commutator_mono hPM hQM)
  let QM : Subgroup M := Q.subgroupOf M
  have hQMder : QM ≤ D := by
    apply (Subgroup.map_le_map_iff_of_injective
      M.subtype_injective).mp
    simpa [QM, Subgroup.map_subgroupOf_eq_of_le hQM] using hQderG

  have hAlphaNe : alphaCore M ≠ ⊥ := by
    intro hAlphaBot
    letI : Group.IsNilpotent D :=
      commutator_isNilpotent_of_alphaCore_eq_bot_embedding
        hM hAlphaBot
    rcases hQsylow with ⟨S, hQS⟩
    have hQMS : QM = (S : Subgroup M) := by
      apply Subgroup.map_injective M.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hQM]
      exact hQS
    have hSD : (S : Subgroup M) ≤ D := by
      simpa [hQMS] using hQMder
    let SD : Sylow q D := S.subtype hSD
    let QD : Subgroup D := QM.subgroupOf D
    have hQDcore : pCore q D = QD := by
      rw [pCore_eq_sylow_of_isNilpotent SD]
      apply Subgroup.map_injective D.subtype_injective
      rw [Subgroup.map_subgroupOf_eq_of_le hQMder]
      simpa [SD, hQMS] using
        (Subgroup.map_subgroupOf_eq_of_le hSD)
    have hQDchar : QD.Characteristic := by
      rw [← hQDcore]
      infer_instance
    letI : D.Normal := by infer_instance
    letI : QD.Characteristic := hQDchar
    have hQMnormal : QM.Normal := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hQMder]
      infer_instance
    have hQnormal : (Q.subgroupOf M).Normal := by
      simpa [QM] using hQMnormal
    have hnormQ : Subgroup.normalizer (Q : Set G) = M :=
      mmax_normal hM hQM hQnormal hQne
    apply hnonunique
    rw [hnormQ]
    exact mmax_sup_id hM

  have hqNotAlpha : q ∉ alphaPrimes M := by
    intro hqAlpha
    rcases hQsylow with ⟨S, hQS⟩
    have hRankQ : HasElementaryAbelianRankAtLeast q 3 Q := by
      simpa [ambientSylow, hQS] using
        sylow_has_rank_three_of_mem_alpha_embedding hqAlpha S
    have hQunique :
        Q ∈ minSimple_uniq_max_groups (G := G) :=
      rank3_Uniqueness hQproper ⟨q, hq, hRankQ⟩
    have hQfamily := def_uniq_mmax hQunique hM hQM
    exact hnonunique
      (def_uniq_mmaxS Subgroup.le_normalizer hNQproper hQfamily)

  have hqNotBeta : q ∉ betaPrimes M := by
    intro hqBeta
    exact hqNotAlpha (beta_sub_alpha M hqBeta)
  have hAlphaBeta : alphaPrimes M ⊆ betaPrimes M := by
    intro r hrAlpha
    by_contra hrNotBeta
    letI : Fact r.Prime := ⟨hrAlpha.1⟩
    have hrq : r ≠ q := by
      intro hrq
      subst r
      exact hqNotAlpha hrAlpha
    have hQMq : IsPGroup q QM :=
      hQq.of_equiv (Subgroup.subgroupOfEquivOfLe hQM).symm
    have hCentUnique :=
      (beta'_cent_Sylow hM hrNotBeta hqNotBeta
        (X := QM) hQMq (Or.inl ⟨hrq, hQMder⟩)).2.1 hrAlpha
    have hCentUnique' :
        centralizerWithin M Q ∈
          minSimple_uniq_max_groups (G := G) := by
      simpa [QM, Subgroup.map_subgroupOf_eq_of_le hQM] using hCentUnique
    have hCentFamily := def_uniq_mmax hCentUnique' hM
      (centralizerWithin_le_left M Q)
    exact hnonunique
      (def_uniq_mmaxS
        (inf_le_right.trans
          (Subgroup.centralizer_le_normalizer (Q : Set G)))
        hNQproper hCentFamily)

  obtain ⟨hCentPNe, hCentJoin⟩ :=
    part_a hAlphaNe hqNotAlpha hQq hQM
  exact ⟨Set.Subset.antisymm hAlphaBeta (beta_sub_alpha M),
    hAlphaNe, hqNotAlpha, hCentPNe, hCentJoin⟩

/-- `BGsection12.v: der_compl_cent_beta'`, Lemma 12.19.

The subgroup is represented in the ambient group.  Its Hall property is
therefore stated after restriction to the sigma core. -/
theorem der_compl_cent_beta'
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    ∃ H : Subgroup G,
      H ≤ sigmaCore M ∧
        IsHall (betaPrimes M)ᶜ
          (H.subgroupOf (sigmaCore M)) ∧
        (_root_.commutator E).map E.subtype ≤
          Subgroup.centralizer (H : Set G) := by
  classical
  let D : Subgroup G :=
    (_root_.commutator M).map M.subtype
  let ED : Subgroup G :=
    (_root_.commutator E).map E.subtype
  let S : Subgroup G := sigmaCore M
  have hEDD : ED ≤ D := by
    simpa [ED, D, E.map_subtype_commutator,
      M.map_subtype_commutator] using
      (Subgroup.commutator_mono hEM hEM)
  have hEpi :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card E) := by
    rw [← Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEM]
    exact hHallE.isPiNumber_card
  have hEDsigma' :
      IsPiNumber (sigmaPrimes M)ᶜ (Nat.card ED) :=
    hEpi.of_dvd (Subgroup.card_dvd_of_le
      (by
        simpa [ED, E.map_subtype_commutator] using
          (show ⁅E, E⁆ ≤ E by
            simpa using
              (Subgroup.commutator_le_sup (H₁ := E) (H₂ := E)))))
  have hEDbeta' :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card ED) := by
    intro r hr hrED hrBeta
    exact hEDsigma' hr hrED (beta_sub_sigma hM hrBeta)
  have hDM : D ≤ M := by
    simpa [D] using
      (Subgroup.map_subtype_le (_root_.commutator M))
  have hDsol : IsSolvable D :=
    mFT_sol (lt_of_le_of_lt hDM (mmax_proper hM))
  obtain ⟨K, hEDK, hKD, hKHallD⟩ :=
    exists_ambient_isHall_ge_of_isSolvable
      hEDD hDsol (betaPrimes M)ᶜ hEDbeta'
  have hKbeta' :
      IsPiNumber (betaPrimes M)ᶜ (Nat.card K) := by
    have hcard := hKHallD.isPiNumber_card
    rwa [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hKD] at hcard
  letI : Group.IsNilpotent K := beta'_der1_nil hM hKbeta' hKD
  have hSD : S ≤ D := by
    simpa [S, D] using Msigma_der1 hM
  let KD : Subgroup D := K.subgroupOf D
  let SD : Subgroup D := S.subgroupOf D
  have hSDnormal : SD.Normal := by
    have hMnormS : M ≤ Subgroup.normalizer (S : Set G) := by
      dsimp [S]
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer
        (sigmaCore_le M)).mp (sigmaCore_normal M)
    exact Subgroup.normal_subgroupOf_of_le_normalizer
      (hDM.trans hMnormS)
  have hHallInfD :
      IsHall (betaPrimes M)ᶜ ((KD ⊓ SD).subgroupOf SD) := by
    apply isHall_inf_normal_embedding
    · simpa [KD] using hKHallD
    · exact hSDnormal
  let H : Subgroup G := K ⊓ S
  have hHS : H ≤ S := inf_le_right
  have hHHall :
      IsHall (betaPrimes M)ᶜ (H.subgroupOf S) := by
    let eSD : SD ≃* S := Subgroup.subgroupOfEquivOfLe hSD
    have hHallMap := isHall_map_mulEquiv_embedding eSD hHallInfD
    have hmap :
        ((KD ⊓ SD).subgroupOf SD).map eSD.toMonoidHom =
          H.subgroupOf S := by
      apply Subgroup.map_injective S.subtype_injective
      have he : S.subtype.comp eSD.toMonoidHom =
          D.subtype.comp SD.subtype := by
        ext x
        rfl
      rw [Subgroup.map_map, he, ← Subgroup.map_map,
        Subgroup.map_subgroupOf_eq_of_le inf_le_right,
        Subgroup.map_inf _ _ _ D.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le hKD,
        Subgroup.map_subgroupOf_eq_of_le hSD,
        Subgroup.map_subgroupOf_eq_of_le hHS]
    rwa [hmap] at hHallMap
  have hEDsigmaK :
      IsPiNumber (sigmaPrimes M)ᶜ
        (Nat.card (ED.subgroupOf K)) := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hEDK]
    exact hEDsigma'
  have hHsigma : IsPiNumber (sigmaPrimes M) (Nat.card H) :=
    (sigmaCore_isPiNumber M).of_dvd
      (Subgroup.card_dvd_of_le inf_le_right)
  have hHsigmaK :
      IsPiNumber (sigmaPrimes M)
        (Nat.card (H.subgroupOf K)) := by
    rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq inf_le_left]
    exact hHsigma
  have hcentK :
      ED.subgroupOf K ≤
        Subgroup.centralizer ((H.subgroupOf K : Subgroup K) : Set K) :=
    nilpotent_subgroups_commute_of_coprime_pi
      (pi := (sigmaPrimes M)ᶜ) hEDsigmaK
      (by simpa only [compl_compl] using hHsigmaK)
  refine ⟨H, hHS, hHHall, ?_⟩
  intro e he
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  let eK : K := ⟨e, hEDK he⟩
  let hK : K := ⟨h, hh.1⟩
  exact congrArg Subtype.val
    (hcentK (show eK ∈ ED.subgroupOf K from he)
      hK (show hK ∈ H.subgroupOf K from hh))
