import Submission.OddOrder.BG.Section13.SigmaPartition

/-!
# Bender--Glauberman Section 13: regularity of the tau-one and tau-three action

This file ports `BGsection13.v`, lines 822--1119: Theorem 13.10,
Corollary 13.11, and Lemmas 13.12--13.13.

The source uses two action predicates.  `IsSemiregularConjugation K A`
says that every nonidentity element of `A` acts fixed-point-freely on `K`,
whereas `IsPrimeAction K A` says that every nontrivial subgroup of `A` has
the same centralizer in `K`.
-/

namespace Submission.OddOrder.BG.Section13

open Submission.OddOrder.BG.Section03
open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section09
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section12
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

/-! ## Elementary adapters for the two action predicates -/

/-- A semiregular conjugation action has trivial centralizer on every
nontrivial subgroup of the actor. -/
private theorem centralizerWithin_eq_bot_of_semiregular
    {G : Type u} [Group G]
    {K A X : Subgroup G}
    (hreg : IsSemiregularConjugation K A)
    (hXA : X ≤ A) (hX : X ≠ ⊥) :
    centralizerWithin K X = ⊥ := by
  apply eq_bot_iff.mpr
  intro x hx
  letI : Nontrivial X := X.nontrivial_iff_ne_bot.mpr hX
  obtain ⟨a, ha⟩ := exists_ne (1 : X)
  let aA : A := ⟨a, hXA a.property⟩
  let xK : K := ⟨x, hx.1⟩
  have hcomm : (a : G) * x = x * (a : G) := hx.2 a a.property
  have hconj : (aA : G) * (xK : G) * (aA : G)⁻¹ = (xK : G) := by
    simpa [aA, xK, mul_assoc] using congrArg (fun z : G ↦ z * (a : G)⁻¹) hcomm
  have hxone : xK = 1 := hreg aA (by simpa [aA] using ha) xK hconj
  simpa [xK] using congrArg Subtype.val hxone

/-- Trivial centralizers of all nontrivial actor subgroups imply
semiregularity. -/
private theorem semiregular_of_centralizerWithin_eq_bot
    {G : Type u} [Group G]
    {K A : Subgroup G}
    (hcent : ∀ X : Subgroup G, X ≤ A → X ≠ ⊥ →
      centralizerWithin K X = ⊥) :
    IsSemiregularConjugation K A := by
  intro a ha x hax
  let X : Subgroup G := Subgroup.zpowers (a : G)
  have hXA : X ≤ A := Subgroup.zpowers_le.mpr a.property
  have hX : X ≠ ⊥ := by
    change Subgroup.zpowers (a : G) ≠ ⊥
    exact Subgroup.zpowers_ne_bot.mpr
      (fun h ↦ ha (Subtype.ext h))
  have hxcent : (x : G) ∈ centralizerWithin K X := by
    refine ⟨x.property, ?_⟩
    intro y hy
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hcomm : Commute (a : G) (x : G) := by
      rw [Commute]
      calc
        (a : G) * (x : G) =
            ((a : G) * (x : G) * (a : G)⁻¹) * (a : G) := by simp [mul_assoc]
        _ = (x : G) * (a : G) := by rw [hax]
    exact hcomm.zpow_left n
  have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
    rw [← hcent X hXA hX]
    exact hxcent
  apply Subtype.ext
  simpa using hxbot

/-- Semiregularity is equivalent to the centralizer form used throughout
the MathComp proof. -/
private theorem semiregular_iff_centralizerWithin_eq_bot
    {G : Type u} [Group G]
    {K A : Subgroup G} :
    IsSemiregularConjugation K A ↔
      ∀ X : Subgroup G, X ≤ A → X ≠ ⊥ →
        centralizerWithin K X = ⊥ :=
  ⟨fun h X hXA hX ↦
      centralizerWithin_eq_bot_of_semiregular h hXA hX,
    semiregular_of_centralizerWithin_eq_bot⟩

/-- A prime action whose full actor centralizer is trivial is
semiregular. -/
private theorem semiregular_of_prime_action_of_centralizer_eq_bot
    {G : Type u} [Group G]
    {K A : Subgroup G}
    (hprime : IsPrimeAction K A)
    (hfull : centralizerWithin K A = ⊥) :
    IsSemiregularConjugation K A := by
  apply semiregular_of_centralizerWithin_eq_bot
  intro X hXA hX
  exact (hprime X hXA hX).trans hfull

/-! ## Local adapters used by the source proof of Theorem 13.10 -/

/-- MathComp's `Sylow_gen`, in the eliminator form used in Theorem 13.10. -/
private theorem le_of_sylow_le_tau13
    {G : Type u} [Group G] [Finite G] {X K : Subgroup G}
    (h : ∀ {q : ℕ}, q ∈ primeSupport (Nat.card X) →
      ∀ Q : Sylow q X,
        ((Q : Subgroup X).map X.subtype : Subgroup G) ≤ K) :
    X ≤ K := by
  let L : Subgroup X := K.comap X.subtype
  have hLtop : L = ⊤ := by
    apply Subgroup.index_eq_one.mp
    by_contra hindex
    have hindexGt : 1 < L.index :=
      Nat.one_lt_iff_ne_zero_and_ne_one.mpr
        ⟨L.index_ne_zero_of_finite, hindex⟩
    obtain ⟨q, hq, hqIndex⟩ := Nat.exists_prime_and_dvd hindexGt.ne'
    letI : Fact q.Prime := ⟨hq⟩
    let Q : Sylow q X := default
    have hqX : q ∈ primeSupport (Nat.card X) :=
      ⟨hq, hqIndex.trans L.index_dvd_card⟩
    have hQK := h hqX Q
    have hQL : (Q : Subgroup X) ≤ L := by
      intro x hx
      exact hQK (Subgroup.mem_map_of_mem X.subtype hx)
    have hfactor : (Q : Subgroup X).index =
        (Q : Subgroup X).relIndex L * L.index :=
      ((Q : Subgroup X).relIndex_mul_index hQL).symm
    exact Q.not_dvd_index (hfactor ▸ dvd_mul_of_dvd_right hqIndex _)
  intro x hx
  let xX : X := ⟨x, hx⟩
  have hxL : xX ∈ L := by rw [hLtop]; trivial
  exact hxL

/-- Centralization is symmetric, in subgroup-containment form. -/
private theorem centralizer_le_symm_tau13
    {G : Type u} [Group G] {A B : Subgroup G}
    (h : A ≤ Subgroup.centralizer (B : Set G)) :
    B ≤ Subgroup.centralizer (A : Set G) := by
  intro b hb
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact (Subgroup.mem_centralizer_iff.mp (h ha) b hb).symm

/-- Full centralizers are antitone in the centralized subgroup. -/
private theorem centralizer_mono_tau13
    {G : Type u} [Group G] {A B : Subgroup G}
    (hAB : A ≤ B) :
    Subgroup.centralizer (B : Set G) ≤
      Subgroup.centralizer (A : Set G) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  exact Subgroup.mem_centralizer_iff.mp hx a (hAB ha)

/-- An elementwise centralizer of both factors centralizes their join. -/
private theorem le_centralizer_sup_tau13
    {G : Type u} [Group G] {X A B : Subgroup G}
    (hA : X ≤ Subgroup.centralizer (A : Set G))
    (hB : X ≤ Subgroup.centralizer (B : Set G)) :
    X ≤ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply Subgroup.le_centralizer_iff.mpr
  exact sup_le
    (Subgroup.le_centralizer_iff.mp hA)
    (Subgroup.le_centralizer_iff.mp hB)

/-- A pi-subgroup lies in a normal pi-Hall subgroup. -/
private theorem le_normal_isHall_of_isPiNumber_tau13
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {C K L : Subgroup G}
    (hKnormal : (K.subgroupOf C).Normal)
    (hKHall : IsHall pi (K.subgroupOf C))
    (hLC : L ≤ C) (hLpi : IsPiNumber pi (Nat.card L)) :
    L ≤ K := by
  let KC : Subgroup C := K.subgroupOf C
  letI : KC.Normal := by simpa only [KC] using hKnormal
  have hcop : (Nat.card L).Coprime KC.index := by
    apply Nat.coprime_of_dvd
    intro p hp hpL hpIndex
    exact hKHall.isPiNumber_index hp hpIndex (hLpi hp hpL)
  intro x hxL
  let xC : C := ⟨x, hLC hxL⟩
  let qC : C →* C ⧸ KC := QuotientGroup.mk' KC
  have horderL : orderOf (qC xC) ∣ Nat.card L :=
    (orderOf_map_dvd qC xC).trans (by
      simpa [xC] using L.orderOf_dvd_natCard hxL)
  have horderIndex : orderOf (qC xC) ∣ KC.index := by
    simpa only [KC.index_eq_card] using orderOf_dvd_natCard (qC xC)
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- A subgroup whose order is coprime to the index of a normal subgroup
lies in that normal subgroup. -/
private theorem le_normal_of_coprime_index_tau13
    {G : Type u} [Group G] [Finite G]
    {N P : Subgroup G} (hN : N.Normal)
    (hcop : Nat.Coprime (Nat.card P) N.index) :
    P ≤ N := by
  letI : N.Normal := hN
  let q : G →* G ⧸ N := QuotientGroup.mk' N
  intro x hx
  have horderP : orderOf (q x) ∣ Nat.card P :=
    (orderOf_map_dvd q x).trans (P.orderOf_dvd_natCard hx)
  have horderIndex : orderOf (q x) ∣ N.index := by
    simpa only [N.index_eq_card] using orderOf_dvd_natCard (q x)
  have horderOne : orderOf (q x) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderP horderIndex
  exact (QuotientGroup.eq_one_iff x).mp
    (by simpa [q] using orderOf_eq_one_iff.mp horderOne)

/-- Restricting a normal Hall subgroup to an intermediate subgroup gives
the corresponding Hall intersection. -/
private theorem isHall_inf_of_normal_le_tau13
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {H C M : Subgroup G}
    (hHM : H ≤ M) (hCM : C ≤ M)
    (hHnormal : (H.subgroupOf M).Normal)
    (hHHall : IsHall pi (H.subgroupOf M)) :
    IsHall pi ((H ⊓ C).subgroupOf C) := by
  constructor
  · rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
      inf_le_right]
    have hHpi : IsPiNumber pi (Nat.card H) := by
      simpa only [
        Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hHM] using
        hHHall.isPiNumber_card
    exact hHpi.of_dvd (Subgroup.card_dvd_of_le inf_le_left)
  · change IsPiNumber piᶜ ((H ⊓ C).relIndex C)
    rw [Subgroup.inf_relIndex_right]
    let HM : Subgroup M := H.subgroupOf M
    let CM : Subgroup M := C.subgroupOf M
    letI : HM.Normal := by simpa only [HM] using hHnormal
    have hdvd : HM.relIndex CM ∣ HM.index :=
      Subgroup.relIndex_dvd_index_of_normal HM CM
    have hrel : HM.relIndex CM = H.relIndex C := by
      simpa only [HM, CM] using
        Subgroup.relIndex_subgroupOf (H := H) hCM
    rw [hrel] at hdvd
    exact hHHall.isPiNumber_index.of_dvd hdvd

/-- Every subgroup of a cyclic group is characteristic. -/
private theorem subgroup_characteristic_of_isCyclic_tau13
    {C : Type*} [Group C] [IsCyclic C] (H : Subgroup C) :
    H.Characteristic := by
  rw [Subgroup.characteristic_iff_map_le]
  intro e
  obtain ⟨m, hm⟩ := e.toMonoidHom.map_cyclic
  rintro _ ⟨x, hx, rfl⟩
  rw [hm]
  exact H.zpow_mem hx m

/-- A characteristic subgroup is invariant under the full ambient
normalizer of its parent. -/
private theorem characteristic_map_subtype_le_normalizer_tau13
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

/-- The unique order-`q` subgroup of a nontrivial cyclic `q`-group lies
in every nontrivial internal centralizer. -/
private theorem map_omegaOne_le_centralizerWithin_of_cyclic_tau13
    {G : Type u} [Group G] [Finite G]
    {q : ℕ} [Fact q.Prime] {Q A : Subgroup G}
    (hQp : IsPGroup q Q) (hQcyc : IsCyclic Q)
    (hQne : Q ≠ ⊥)
    (hCne : centralizerWithin Q A ≠ ⊥) :
    (omegaOne q Q).map Q.subtype ≤ centralizerWithin Q A := by
  letI : IsCyclic Q := hQcyc
  obtain ⟨c, hcne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hCne
  let cQ : Q := ⟨(c : G), c.property.1⟩
  let H : Subgroup Q := Subgroup.zpowers cQ
  have hcQne : cQ ≠ 1 := by
    intro h
    apply hcne
    apply Subtype.ext
    exact congrArg (fun z : Q ↦ (z : G)) h
  have hHne : H ≠ ⊥ := by
    simpa [H, Subgroup.zpowers_eq_bot] using hcQne
  have hHp : IsPGroup q H := hQp.to_subgroup H
  have hHcardNe : Nat.card H ≠ 1 :=
    (H.one_lt_card_iff_ne_bot.mpr hHne).ne'
  have hQcardNe : Nat.card Q ≠ 1 :=
    (Q.one_lt_card_iff_ne_bot.mpr hQne).ne'
  have hHOmegaCard : Nat.card (omegaOne q H) = q :=
    card_omegaOne_of_isCyclic_isPGroup
      (Fact.out : q.Prime) hHp hHcardNe
  have hQOmegaCard : Nat.card (omegaOne q Q) = q :=
    card_omegaOne_of_isCyclic_isPGroup
      (Fact.out : q.Prime) hQp hQcardNe
  let W : Subgroup Q := (omegaOne q H).map H.subtype
  have hWOmega : W ≤ omegaOne q Q := map_omegaOne_le q H.subtype
  have hWcard : Nat.card W = q := by
    rw [Subgroup.card_map_of_injective H.subtype_injective,
      hHOmegaCard]
  have hWeq : W = omegaOne q Q := by
    apply Subgroup.eq_of_le_of_card_ge hWOmega
    rw [hWcard, hQOmegaCard]
  have hHC : H ≤ (centralizerWithin Q A).subgroupOf Q := by
    apply Subgroup.zpowers_le.mpr
    exact c.property
  rintro _ ⟨x, hx, rfl⟩
  have hxW : x ∈ W := by rw [hWeq]; exact hx
  rcases hxW with ⟨y, hy, rfl⟩
  exact hHC y.property

/-- A common normalizer of `D` and `A` normalizes `C_D(A)`. -/
private theorem centralizerWithin_normalized_by_common_normalizer_tau13
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
  have ha' : x⁻¹ * a * x ∈ A := by
    simpa only [inv_inv] using
      (Subgroup.mem_normalizer_iff.mp hxInvA a).mp ha
  have hcomm := hy.2 (x⁻¹ * a * x) ha'
  calc
    a * (x * y * x⁻¹) =
        x * ((x⁻¹ * a * x) * y) * x⁻¹ := by group
    _ = x * (y * (x⁻¹ * a * x)) * x⁻¹ := by rw [hcomm]
    _ = (x * y * x⁻¹) * a := by group

private theorem map_conj_one_tau13
    {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem map_conj_map_conj_tau13
    {G : Type*} [Group G] (H : Subgroup G) (a b : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj b).toMonoidHom =
      H.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem map_conj_inv_map_conj_tau13
    {G : Type*} [Group G] (H : Subgroup G) (a : G) :
    (H.map (MulAut.conj a).toMonoidHom).map
        (MulAut.conj a⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj_tau13]
  simpa only [inv_mul_cancel] using map_conj_one_tau13 H

/-- Full centralizers commute with ambient equivalences. -/
private theorem map_centralizer_equiv_tau13
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

/-- Cauchy's theorem in the rank-one subgroup language. -/
private theorem exists_rankOne_le_of_prime_dvd_tau13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hpK : p ∣ Nat.card K) :
    ∃ P : Subgroup G, P ≤ K ∧ IsElementaryAbelianOfRank p 1 P := by
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) p hpK
  let P : Subgroup G := (Subgroup.zpowers x).map K.subtype
  have hcardZ : Nat.card (Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers, hx]
  have hcardP : Nat.card P = p := by
    rw [Subgroup.card_map_of_injective K.subtype_injective, hcardZ]
  exact ⟨P, Subgroup.map_subtype_le _,
    isElementaryAbelianOfRank_one_of_card_eq_prime hcardP⟩

/-- A nontrivial proper subgroup of an elementary-abelian plane is a
line. -/
private theorem rankOne_of_nontrivial_proper_le_rankTwo_tau13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {A X : Subgroup G}
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hXA : X ≤ A) (hXne : X ≠ ⊥) (hXproper : X ≠ A) :
    IsElementaryAbelianOfRank p 1 X := by
  have hXp : IsPGroup p X :=
    (hA.isPGroup.to_subgroup (X.subgroupOf A)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hXA)
  obtain ⟨n, hn⟩ := hXp.exists_card_eq
  have hnpos : 0 < n := by
    by_contra hn0
    have hnzero : n = 0 := Nat.eq_zero_of_not_pos hn0
    apply hXne
    apply Subgroup.card_eq_one.mp
    simpa only [hn, hnzero, pow_zero]
  have hnle : n ≤ 2 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [← hn, ← hA.card_eq]
    exact Subgroup.card_le_of_le hXA
  have hnnotTwo : n ≠ 2 := by
    intro hntwo
    apply hXproper
    apply Subgroup.eq_of_le_of_card_ge hXA
    rw [hn, hntwo, hA.card_eq]
  have hnOne : n = 1 := by omega
  apply isElementaryAbelianOfRank_one_of_card_eq_prime
  simpa only [hn, hnOne, pow_one]

/-- The ambient image in `IsSylowSubgroupOf` lies in its ambient group. -/
private theorem IsSylowSubgroupOf.le_tau13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} {P K : Subgroup G}
    (hP : IsSylowSubgroupOf p P K) : P ≤ K := by
  rcases hP with ⟨S, rfl⟩
  exact Subgroup.map_subtype_le _

/-- Extend a Sylow subgroup through an intermediate subgroup whose index
is prime to the Sylow prime. -/
private theorem IsSylowSubgroupOf.extend_of_not_dvd_index_tau13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {S H K : Subgroup G}
    (hS : IsSylowSubgroupOf p S H) (hHK : H ≤ K)
    (hpIndex : ¬ p ∣ (H.subgroupOf K).index) :
    IsSylowSubgroupOf p S K := by
  have hSH : S ≤ H := by
    rcases hS with ⟨P, rfl⟩
    exact Subgroup.map_subtype_le _
  have hSK : S ≤ K := hSH.trans hHK
  let SK : Subgroup K := S.subgroupOf K
  have hSKp : IsPGroup p SK :=
    hS.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe hSK).symm
  have hpSIndexH : ¬ p ∣ (S.subgroupOf H).index := by
    obtain ⟨P, hP⟩ := hS
    have hindex : (S.subgroupOf H).index = P.index := by
      calc
        (S.subgroupOf H).index = S.relIndex H := rfl
        _ = ((P : Subgroup H).map H.subtype).relIndex H := by rw [hP]
        _ = (P : Subgroup H).relIndex ⊤ := by
          have hmapTop : (⊤ : Subgroup H).map H.subtype = H := by
            rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
          exact (congrArg
            (fun J : Subgroup G ↦
              ((P : Subgroup H).map H.subtype).relIndex J)
            hmapTop.symm).trans
              (Subgroup.relIndex_map_map_of_injective _ _
                H.subtype_injective)
        _ = P.index := (P : Subgroup H).relIndex_top_right
    rw [hindex]
    exact P.not_dvd_index
  have hpSKindex : ¬ p ∣ SK.index := by
    have hfactor : SK.index =
        (S.subgroupOf H).index * (H.subgroupOf K).index := by
      change S.relIndex K = S.relIndex H * H.relIndex K
      exact (S.relIndex_mul_relIndex H K hSH hHK).symm
    rw [hfactor]
    exact (Fact.out : p.Prime).not_dvd_mul hpSIndexH hpIndex
  let P : Sylow p K := hSKp.toSylow hpSKindex
  refine ⟨P, ?_⟩
  change S = SK.map K.subtype
  exact (Subgroup.map_subgroupOf_eq_of_le hSK).symm

/-- Restrict an ambient Sylow subgroup to an intermediate intersection
which still contains it. -/
private theorem isSylowSubgroupOf_inf_of_le_tau13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {S M L : Subgroup G}
    (hS : IsSylowSubgroupOf p S M) (hSL : S ≤ L) :
    IsSylowSubgroupOf p S (M ⊓ L) := by
  have hSI : S ≤ M ⊓ L :=
    le_inf (IsSylowSubgroupOf.le_tau13 hS) hSL
  have hSp : IsPGroup p S := hS.isPGroup
  obtain ⟨P, hP⟩ := hS
  let I : Subgroup G := M ⊓ L
  change S ≤ I at hSI
  let SI : Subgroup I := S.subgroupOf I
  have hSIp : IsPGroup p SI :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSI).symm
  obtain ⟨T, hSIT⟩ := hSIp.exists_le_sylow
  let TG : Subgroup G := (T : Subgroup I).map I.subtype
  have hTGp : IsPGroup p TG := T.isPGroup'.map I.subtype
  have hTGM : TG ≤ M :=
    (Subgroup.map_subtype_le (T : Subgroup I)).trans inf_le_left
  let TM : Subgroup M := TG.subgroupOf M
  have hTMp : IsPGroup p TM :=
    hTGp.of_equiv (Subgroup.subgroupOfEquivOfLe hTGM).symm
  have hPTM : (P : Subgroup M) ≤ TM := by
    intro x hx
    change (x : G) ∈ TG
    have hxS : (x : G) ∈ S := by
      rw [hP]
      exact Subgroup.mem_map_of_mem M.subtype hx
    let xI : I := ⟨x, hSI hxS⟩
    have hxSI : xI ∈ SI := hxS
    exact Subgroup.mem_map_of_mem I.subtype (hSIT hxSI)
  have hTMP : TM = (P : Subgroup M) := P.is_maximal' hTMp hPTM
  have hTGS : TG = S := by
    calc
      TG = TM.map M.subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hTGM).symm
      _ = (P : Subgroup M).map M.subtype := by rw [hTMP]
      _ = S := hP.symm
  refine ⟨T, ?_⟩
  change S = TG
  exact hTGS.symm

/-- Restrict an ambient Sylow statement to subgroup types. -/
private theorem isSylowSubgroupOf_subgroupOf_tau13
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {X D H : Subgroup G}
    (hXH : X ≤ H) (hDH : D ≤ H) (_hXD : X ≤ D)
    (hX : IsSylowSubgroupOf p X D) :
    IsSylowSubgroupOf p (X.subgroupOf H) (D.subgroupOf H) := by
  let DH : Subgroup H := D.subgroupOf H
  obtain ⟨S, hXS⟩ := hX
  let eDH : DH ≃* D := Subgroup.subgroupOfEquivOfLe hDH
  let SH : Sylow p DH :=
    S.mapSurjective (f := eDH.symm.toMonoidHom) eDH.symm.surjective
  have hSHcoe :
      (SH : Subgroup DH) =
        (S : Subgroup D).map eDH.symm.toMonoidHom := by
    change
      ((S.mapSurjective (f := eDH.symm.toMonoidHom)
          eDH.symm.surjective : Sylow p DH) : Subgroup DH) = _
    rw [Sylow.coe_mapSurjective]
  refine ⟨SH, by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hXH]
    rw [hSHcoe, Subgroup.map_map, Subgroup.map_map, hXS]
    apply congrArg (fun f : D →* G ↦ (S : Subgroup D).map f)
    ext d
    rfl⟩

/-! ## Source-facing conclusions -/

/-- The three conclusions of Bender--Glauberman Theorem 13.10. -/
structure Tau13RegularConclusion
    {G : Type u} [Group G] [Finite G]
    (M E₁ E₃ P : Subgroup G) : Prop where
  /-- Part (a): `E₁` acts fixed-point-freely on `E₃`. -/
  E₃_E₁_regular : IsSemiregularConjugation E₃ E₁
  /-- Part (b): `E₃` acts fixed-point-freely on the sigma core. -/
  sigma_E₃_regular : IsSemiregularConjugation (sigmaCore M) E₃
  /-- Part (c): the line `P` has nontrivial fixed points in the sigma
  core. -/
  sigma_P_centralizer_ne_bot :
    centralizerWithin (sigmaCore M) P ≠ ⊥

/-- The four conclusions of Bender--Glauberman Corollary 13.11. -/
structure Tau13NonregularConclusion
    {G : Type u} [Group G] [Finite G]
    (M E E₁ E₃ : Subgroup G) : Prop where
  /-- Part (a). -/
  E₁_ne_bot : E₁ ≠ ⊥
  /-- Part (b). -/
  E₃_E₁_sdprod : IsInternalSemidirectProductIn E₃ E₁ E
  /-- Part (c). -/
  sigma_prime_action : IsPrimeAction (sigmaCore M) E
  /-- Part (d): every elementary-abelian line of `E` is normal in
  `E`. -/
  rankOne_normal :
    ∀ {p : ℕ} [Fact p.Prime] {X : Subgroup G},
      RankOneLineIn p E X → (X.subgroupOf E).Normal

/-! ## Theorem 13.10 and Corollary 13.11 -/

/-- `BGsection13.v: tau13_regular`, Bender--Glauberman Theorem 13.10. -/
theorem tau13_regular
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ E₂ E₃ P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hP : RankOneLineIn p E₁ P)
    (hnotCentral : ¬ P ≤ Subgroup.centralizer (E₃ : Set G)) :
    Tau13RegularConclusion M E₁ E₃ P := by
  classical
  have hctx : SigmaComplementContext E E₁ E₂ E₃ :=
    sigma_compl_context hM hCompl
  have hPne : P ≠ ⊥ := hP.2.ne_bot
  have hPp : IsPGroup p P := hP.2.isPGroup
  have hpP : p ∣ Nat.card P :=
    hPp.card_eq_or_dvd.resolve_left
      (fun hcard ↦ hPne (Subgroup.card_eq_one.mp hcard))
  have hPE : P ≤ E := hP.1.trans hCompl.E₁_le_E
  have hPM : P ≤ M := hPE.trans hCompl.E_le_M
  have hpTau1 : p ∈ tau1Primes M :=
    hCompl.hall_E₁.isPiNumber_card (Fact.out : p.Prime) (by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        hCompl.E₁_le_E]
      exact hpP.trans (Subgroup.card_dvd_of_le hP.1))

  obtain ⟨q, hqSupport, Q₀, hPnotCentQ⟩ :
      ∃ q : ℕ, q ∈ primeSupport (Nat.card E₃) ∧
        ∃ Q₀ : Sylow q E₃,
          ¬ P ≤ Subgroup.centralizer
            (((Q₀ : Subgroup E₃).map E₃.subtype : Subgroup G) : Set G) := by
    by_contra hnone
    push_neg at hnone
    apply hnotCentral
    apply centralizer_le_symm_tau13
    apply le_of_sylow_le_tau13
    intro q hq Q₀
    exact centralizer_le_symm_tau13 (hnone q hq Q₀)
  have hq : q.Prime := hqSupport.1
  letI : Fact q.Prime := ⟨hq⟩
  let Q : Subgroup G :=
    (Q₀ : Subgroup E₃).map E₃.subtype
  have hQE₃ : Q ≤ E₃ := by
    simpa only [Q] using
      (Subgroup.map_subtype_le (Q₀ : Subgroup E₃))
  have hQE : Q ≤ E := hQE₃.trans hCompl.E₃_le_E
  have hQM : Q ≤ M := hQE.trans hCompl.E_le_M
  have hQq : IsPGroup q Q := Q₀.isPGroup'.map E₃.subtype
  have hQne : Q ≠ ⊥ := by
    intro hQ
    apply hPnotCentQ
    change P ≤ Subgroup.centralizer (Q : Set G)
    rw [hQ]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyOne : y = 1 := Subgroup.mem_bot.mp hy
    subst y
    simp
  have hqTau3 : q ∈ tau3Primes M :=
    hCompl.hall_E₃.isPiNumber_card hq (by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        hCompl.E₃_le_E]
      exact hqSupport.2)
  have hqp : q ≠ p := by
    intro hqp
    subst q
    exact (tau3'1 M hpTau1) hqTau3

  letI : IsCyclic E₃ := hctx.E₃_cyclic
  let Q₃ : Subgroup E₃ := (Q₀ : Subgroup E₃)
  have hQ₃char : Q₃.Characteristic :=
    subgroup_characteristic_of_isCyclic_tau13 Q₃
  letI : Q₃.Characteristic := hQ₃char
  have hEnormE₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCompl.E₃_le_E).mp
      hctx.E₃_normal
  have hPNQ : P ≤ Subgroup.normalizer (Q : Set G) := by
    exact hPE.trans (hEnormE₃.trans (by
      simpa only [Q, Q₃] using
        characteristic_map_subtype_le_normalizer_tau13 E₃ Q₃))
  have hQcyclic : IsCyclic Q := Subgroup.isCyclic_of_le hQE₃
  have hregQP : centralizerWithin Q P = ⊥ := by
    by_contra hfixedQ
    have hOmegaWithin :=
      map_omegaOne_le_centralizerWithin_of_cyclic_tau13
        hQq hQcyclic hQne hfixedQ
    have hOmegaCent :
        (omegaOne q Q).map Q.subtype ≤
          Subgroup.centralizer (P : Set G) :=
      hOmegaWithin.trans inf_le_right
    have hPCentOmega : P ≤ Subgroup.centralizer
        (((omegaOne q Q).map Q.subtype : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_iff.mp hOmegaCent
    have hcop : (Nat.card Q).Coprime (Nat.card P) :=
      IsPGroup.coprime_card_of_ne q p hqp Q P hQq hPp
    exact hPnotCentQ
      (coprime_odd_faithful_omegaOne_of_odd_card
        hQq hPNQ hcop (mFT_odd Q) hPCentOmega)

  have hQsylE₃ : IsSylowSubgroupOf q Q E₃ := ⟨Q₀, rfl⟩
  have hqIndexE₃ : ¬ q ∣ (E₃.subgroupOf E).index := by
    intro hdiv
    exact hCompl.hall_E₃.isPiNumber_index hq hdiv hqTau3
  have hQsylE : IsSylowSubgroupOf q Q E :=
    IsSylowSubgroupOf.extend_of_not_dvd_index_tau13 hQsylE₃
      hCompl.E₃_le_E hqIndexE₃
  have hqIndexE : ¬ q ∣ (E.subgroupOf M).index := by
    intro hdiv
    exact hCompl.hall_E.isPiNumber_index hq hdiv
      (show q ∈ (sigmaPrimes M)ᶜ from hqTau3.2.1)
  have hQsylM : IsSylowSubgroupOf q Q M :=
    IsSylowSubgroupOf.extend_of_not_dvd_index_tau13 hQsylE
      hCompl.E_le_M hqIndexE

  have hQproper : Q < ⊤ := mFT_pgroup_proper Q hQq
  have hNQproper : Subgroup.normalizer (Q : Set G) < ⊤ :=
    mFT_norm_proper Q hQne hQproper
  obtain ⟨L, hL, hNQL⟩ :=
    mmax_exists (Subgroup.normalizer (Q : Set G)) hNQproper
  have hQL : Q ≤ L := Subgroup.le_normalizer.trans hNQL
  have hnotConj : ∀ g : G,
      L ≠ M.map (MulAut.conj g).toMonoidHom :=
    mmax_norm_notJ hM hL hQq hQM hNQL
      (Or.inr (Or.inr hqTau3))
  have hNQnonunique :
      minSimple_max_groups_of (G := G)
          (Subgroup.normalizer (Q : Set G) : Set G) ≠ {M} := by
    intro huniq
    have hLM : L = M := eq_uniq_mmax huniq hL hNQL
    exact hnotConj 1 (by
      simpa only [map_conj_one_tau13] using hLM)
  rcases (cent_Malpha_reg_tau1 hM hpTau1 hq hqp hPM hP.2 hQne
      hPNQ hregQP hNQnonunique).2 hQsylM with
    ⟨hAlphaBeta, hAlphaNe, _hqNotAlpha,
      hAlphaP, hAlphaQP⟩

  have hSigmaP : centralizerWithin (sigmaCore M) P ≠ ⊥ := by
    intro hSigmaP
    apply hAlphaP
    apply le_antisymm
    · intro x hx
      have hxSigma : x ∈ centralizerWithin (sigmaCore M) P :=
        ⟨Malpha_sub_Msigma hM hx.1, hx.2⟩
      rw [hSigmaP] at hxSigma
      exact hxSigma
    · exact bot_le

  have hregE₃E₁ : IsSemiregularConjugation E₃ E₁ := by
    apply semiregular_of_centralizerWithin_eq_bot
    intro X hXE₁ hXne
    by_contra hfixedX
    have hnotRegular : ¬ IsSemiregularConjugation E₃ E₁ := by
      intro hregular
      exact hfixedX
        (centralizerWithin_eq_bot_of_semiregular hregular hXE₁ hXne)
    have hprimeJoin := tau13_primact_Msigma hM hCompl hnotRegular
    have hPJ : P ≤ E₃ ⊔ E₁ := hP.1.trans le_sup_right
    have hQPJ : Q ⊔ P ≤ E₃ ⊔ E₁ :=
      sup_le (hQE₃.trans le_sup_left) (hP.1.trans le_sup_right)
    have hQPne : Q ⊔ P ≠ ⊥ := by
      intro hbot
      apply hQne
      exact le_bot_iff.mp (le_sup_left.trans_eq hbot)
    have hSigmaEq : centralizerWithin (sigmaCore M) P =
        centralizerWithin (sigmaCore M) (Q ⊔ P) :=
      (hprimeJoin.centralizer_eq hPJ hPne).trans
        (hprimeJoin.centralizer_eq hQPJ hQPne).symm
    have hAlphaEq : centralizerWithin (alphaCore M) P =
        centralizerWithin (alphaCore M) (Q ⊔ P) := by
      ext x
      constructor
      · intro hx
        have hxSigma : x ∈ centralizerWithin (sigmaCore M) P :=
          ⟨Malpha_sub_Msigma hM hx.1, hx.2⟩
        have hxJoin : x ∈
            centralizerWithin (sigmaCore M) (Q ⊔ P) := by
          rw [← hSigmaEq]
          exact hxSigma
        exact ⟨hx.1, hxJoin.2⟩
      · intro hx
        have hxSigma : x ∈
            centralizerWithin (sigmaCore M) (Q ⊔ P) :=
          ⟨Malpha_sub_Msigma hM hx.1, hx.2⟩
        have hxP : x ∈ centralizerWithin (sigmaCore M) P := by
          rw [hSigmaEq]
          exact hxSigma
        exact ⟨hx.1, hxP.2⟩
    exact hAlphaP (hAlphaEq.trans hAlphaQP)

  have hprimeE₃ : IsPrimeAction (sigmaCore M) E₃ :=
    tau3_primact_Msigma hM hCompl.E_le_M hCompl.hall_E
      hCompl.E₃_le_E hCompl.hall_E₃
  have hSigmaE₃ : centralizerWithin (sigmaCore M) E₃ = ⊥ := by
    by_contra hfixedE₃
    let C : Subgroup G := centralizerWithin (sigmaCore M) E₃
    have hCne : C ≠ ⊥ := by simpa only [C] using hfixedE₃
    have hCcardNe : Nat.card C ≠ 1 :=
      (C.one_lt_card_iff_ne_bot.mpr hCne).ne'
    obtain ⟨u, hu, huC⟩ := Nat.exists_prime_and_dvd hCcardNe
    letI : Fact u.Prime := ⟨hu⟩
    have hCsigma : C ≤ sigmaCore M := centralizerWithin_le_left _ _
    have hCM : C ≤ M := hCsigma.trans (sigmaCore_le M)
    have huSigma : u ∈ sigmaPrimes M := by
      rw [← pi_Msigma hM]
      exact ⟨hu, huC.trans (Subgroup.card_dvd_of_le hCsigma)⟩
    have hEnormSigma : E ≤
        Subgroup.normalizer (sigmaCore M : Set G) :=
      hCompl.E_le_M.trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (sigmaCore_le M)).mp (sigmaCore_normal M))
    have hEnormC : E ≤ Subgroup.normalizer (C : Set G) :=
      centralizerWithin_normalized_by_common_normalizer_tau13
        hEnormSigma hEnormE₃
    have hcopCE : (Nat.card C).Coprime (Nat.card E) :=
      (coprime_sigma_compl hCompl.E_le_M hCompl.hall_E).coprime_dvd_left
        (Subgroup.card_dvd_of_le hCsigma)
    have hsolC : IsSolvable C := by
      letI : IsSolvable M := mmax_sol hM
      exact isSolvable_of_injective (Subgroup.inclusion hCM)
        (Subgroup.inclusion_injective hCM)
    obtain ⟨U₀, hEnormU⟩ :=
      exists_sylow_normalized_of_coprime_of_isSolvable
        (p := u) hEnormC hcopCE hsolC
    let U : Subgroup G :=
      (U₀ : Subgroup C).map C.subtype
    have hUC : U ≤ C := by
      simpa only [U] using
        (Subgroup.map_subtype_le (U₀ : Subgroup C))
    have hUsigma : U ≤ sigmaCore M := hUC.trans hCsigma
    have hUM : U ≤ M := hUsigma.trans (sigmaCore_le M)
    have hUu : IsPGroup u U := U₀.isPGroup'.map C.subtype
    have hUsylC : IsSylowSubgroupOf u U C := ⟨U₀, rfl⟩
    have hUne : U ≠ ⊥ := by
      intro hU
      have hUcard : Nat.card (U₀ : Subgroup C) = 1 := by
        rw [← Subgroup.card_map_of_injective C.subtype_injective]
        rw [show (U₀ : Subgroup C).map C.subtype = U from rfl,
          hU, Subgroup.card_bot]
      apply U₀.not_dvd_index
      rw [← one_mul U₀.index, ← hUcard,
        (U₀ : Subgroup C).card_mul_index]
      exact huC
    have hEU : E ≤ Subgroup.normalizer (U : Set G) := by
      simpa only [U] using hEnormU

    have hQML : Q ≤ M ⊓ L := le_inf hQM hQL
    have hQcentInf : Q ≤ Subgroup.centralizer
        ((sigmaCore M ⊓ L : Subgroup G) : Set G) :=
      (cent_norm_tau13_mmax hM hCompl.E_le_M hCompl.hall_E
        (Or.inr hqTau3) hQM hQq hL hNQL).1
          Q hQML hQq
    have hInfCentQ : sigmaCore M ⊓ L ≤
        Subgroup.centralizer (Q : Set G) :=
      centralizer_le_symm_tau13 hQcentInf
    have hCentQEq : centralizerWithin (sigmaCore M) Q = C := by
      simpa only [C] using hprimeE₃.centralizer_eq hQE₃ hQne
    have hInfC : sigmaCore M ⊓ L ≤ C := by
      have hle : sigmaCore M ⊓ L ≤
          centralizerWithin (sigmaCore M) Q :=
        le_inf inf_le_left hInfCentQ
      rwa [hCentQEq] at hle
    have hUL : U ≤ L :=
      hUC.trans (inf_le_right.trans
        (centralizer_mono_tau13 hQE₃)) |>.trans
          (Subgroup.centralizer_le_normalizer (Q : Set G)) |>.trans hNQL
    have hUInf : U ≤ sigmaCore M ⊓ L := le_inf hUsigma hUL
    have hUsylSigmaInf :
        IsSylowSubgroupOf u U (sigmaCore M ⊓ L) := by
      have hrestr :=
        isSylowSubgroupOf_inf_of_le_tau13 hUsylC hUInf
      simpa only [inf_eq_right.mpr hInfC] using hrestr
    have hHallSigmaInf : IsHall (sigmaPrimes M)
        ((sigmaCore M ⊓ L).subgroupOf (M ⊓ L)) := by
      simpa only [← inf_assoc,
        inf_eq_left.mpr (sigmaCore_le M)] using
        isHall_inf_of_normal_le_tau13 (sigmaCore_le M)
          (inf_le_left : M ⊓ L ≤ M)
          (sigmaCore_normal M) (Msigma_Hall hM)
    have huSigmaInfIndex :
        ¬ u ∣ ((sigmaCore M ⊓ L).subgroupOf (M ⊓ L)).index := by
      intro hdiv
      exact hHallSigmaInf.isPiNumber_index hu hdiv huSigma
    have hUsylML : IsSylowSubgroupOf u U (M ⊓ L) :=
      IsSylowSubgroupOf.extend_of_not_dvd_index_tau13 hUsylSigmaInf
        (inf_le_inf (sigmaCore_le M) le_rfl) huSigmaInfIndex

    have hPU : P ≤ Subgroup.normalizer (U : Set G) :=
      hPE.trans hEU
    have hUcentQ : U ≤ Subgroup.centralizer (Q : Set G) :=
      hUC.trans (inf_le_right.trans (centralizer_mono_tau13 hQE₃))
    obtain ⟨hNUM, hregUP⟩ :
        Subgroup.normalizer (U : Set G) ≤ M ∧
          centralizerWithin U P = ⊥ := by
      by_cases huBeta : u ∈ betaPrimes M
      · have hUbeta : IsPiNumber (betaPrimes M) (Nat.card U) :=
          hUu.isPiNumber_natCard huBeta
        have hUbetaCore : U ≤ betaCore M :=
          le_normal_isHall_of_isPiNumber_tau13
            (by simpa using betaCore_normal M)
            (Mbeta_Hall hM) hUM hUbeta
        refine ⟨beta_norm_sub_mmax hM hUM hUbeta hUne, ?_⟩
        apply le_antisymm ?_ bot_le
        rw [← hAlphaQP]
        intro x hx
        have hxQ : x ∈ Subgroup.centralizer (Q : Set G) :=
          hUcentQ hx.1
        have hxJoin : x ∈
            Subgroup.centralizer ((Q ⊔ P : Subgroup G) : Set G) :=
          le_centralizer_sup_tau13
            (show centralizerWithin U P ≤
              Subgroup.centralizer (Q : Set G) from
                fun y hy ↦ hUcentQ hy.1)
            (show centralizerWithin U P ≤
              Subgroup.centralizer (P : Set G) from inf_le_right) hx
        have hCoreEq : alphaCore M = betaCore M := by
          unfold alphaCore betaCore
          rw [hAlphaBeta]
        have hxAlpha : x ∈ alphaCore M := by
          rw [hCoreEq]
          exact hUbetaCore hx.1
        exact ⟨hxAlpha, hxJoin⟩
      · obtain ⟨H, hHSigma, hHHall, hEderCentH⟩ :=
          der_compl_cent_beta' hM hCompl.E_le_M hCompl.hall_E
        have hHcentEder : H ≤ Subgroup.centralizer
            (((_root_.commutator E).map E.subtype : Subgroup G) : Set G) :=
          centralizer_le_symm_tau13 hEderCentH
        have hHC : H ≤ C := by
          apply le_inf hHSigma
          exact hHcentEder.trans
            (centralizer_mono_tau13 hctx.E₃_le_commutator)
        have huHIndex :
            ¬ u ∣ (H.subgroupOf (sigmaCore M)).index := by
          intro hdiv
          apply huBeta
          simpa only [Set.mem_compl_iff, Set.mem_compl_iff, not_not] using
            hHHall.isPiNumber_index hu hdiv
        have huCIndex :
            ¬ u ∣ (C.subgroupOf (sigmaCore M)).index := by
          intro hdiv
          apply huHIndex
          exact hdiv.trans (by
            change C.relIndex (sigmaCore M) ∣ H.relIndex (sigmaCore M)
            exact Subgroup.relIndex_dvd_of_le_left (sigmaCore M) hHC)
        have hUsylSigma : IsSylowSubgroupOf u U (sigmaCore M) :=
          IsSylowSubgroupOf.extend_of_not_dvd_index_tau13 hUsylC
            hCsigma huCIndex
        have huSigmaIndex :
            ¬ u ∣ ((sigmaCore M).subgroupOf M).index := by
          intro hdiv
          exact (Msigma_Hall hM).isPiNumber_index hu hdiv huSigma
        have hUsylM : IsSylowSubgroupOf u U M :=
          IsSylowSubgroupOf.extend_of_not_dvd_index_tau13 hUsylSigma
            (sigmaCore_le M) huSigmaIndex
        obtain ⟨UM, hUMeq⟩ := hUsylM
        have hNUM : Subgroup.normalizer (U : Set G) ≤ M := by
          have hnorm := norm_sigma_Sylow huSigma UM
          simpa only [ambientSylow, ← hUMeq] using hnorm
        refine ⟨hNUM, ?_⟩
        by_contra hfixedUP
        let D : Subgroup G := centralizerWithin U P
        have hDne : D ≠ ⊥ := by simpa only [D] using hfixedUP
        have hDu : IsPGroup u D :=
          (hUu.to_subgroup (D.subgroupOf U)).of_equiv
            (Subgroup.subgroupOfEquivOfLe
              (centralizerWithin_le_left U P))
        have huD : u ∣ Nat.card D :=
          hDu.card_eq_or_dvd.resolve_left
            (fun hcard ↦ hDne (Subgroup.card_eq_one.mp hcard))
        obtain ⟨X, hXD, hX⟩ :=
          exists_rankOne_le_of_prime_dvd_tau13 huD
        have hXcent : X ≤ centralizerWithin (sigmaCore M) P :=
          le_inf
            (hXD.trans (centralizerWithin_le_left U P) |>.trans hUsigma)
            (hXD.trans inf_le_right)
        have huniq := cent_cent_Msigma_tau1_uniq hM hCompl.E_le_M
          hCompl.hall_E hCompl.E₁_le_E hCompl.hall_E₁
          hP.1 hPne hXcent hX
        have hUsylMsub := isSylowSubgroupOf_subgroupOf_tau13
          hUM (sigmaCore_le M) hUsigma hUsylSigma
        obtain ⟨S, hS⟩ := hUsylMsub
        have hfamily := huniq.2 S
        rw [← hS, Subgroup.map_subgroupOf_eq_of_le hUM] at hfamily
        have hLM : L = M := eq_uniq_mmax hfamily hL hUL
        exact hnotConj 1 (by
          simpa only [map_conj_one_tau13] using hLM)

    have hPML : P ≤ M ⊓ L :=
      le_inf hPM (hPNQ.trans hNQL)
    have hPnotCentInf : ¬ P ≤ Subgroup.centralizer
        ((sigmaCore M ⊓ L : Subgroup G) : Set G) := by
      intro hPcent
      have hInfCentP : sigmaCore M ⊓ L ≤
          Subgroup.centralizer (P : Set G) :=
        centralizer_le_symm_tau13 hPcent
      have hUfixed : U ≤ centralizerWithin U P :=
        le_inf le_rfl (hUInf.trans hInfCentP)
      have hUbot : U ≤ ⊥ := by rwa [hregUP] at hUfixed
      exact hUne (le_bot_iff.mp hUbot)
    have hcommNe : ⁅sigmaCore M ⊓ L, M ⊓ L⁆ ≠ ⊥ := by
      intro hcomm
      apply hPnotCentInf
      have hInfCentML : sigmaCore M ⊓ L ≤
          Subgroup.centralizer ((M ⊓ L : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      exact hPML.trans (centralizer_le_symm_tau13 hInfCentML)
    have hpESupport : p ∈ primeSupport (Nat.card E) :=
      ⟨Fact.out, hpP.trans (Subgroup.card_dvd_of_le hPE)⟩
    have hpLSupport : p ∈ primeSupport (Nat.card L) :=
      ⟨Fact.out, hpP.trans (Subgroup.card_dvd_of_le
        (hPNQ.trans hNQL))⟩
    have hpTau1L : p ∈ tau1Primes L := by
      by_contra hpNotTau1L
      have hcentral := Msigma_setI_mmax_central hM hCompl.E_le_M
        hCompl.hall_E hL hpESupport hpLSupport hpNotTau1L hcommNe hnotConj
      exact hPnotCentInf
        (hcentral.1 P hPML hPp)
    have hQsylML : IsSylowSubgroupOf q Q (M ⊓ L) :=
      isSylowSubgroupOf_inf_of_le_tau13 hQsylM hQL
    exact tau1_mmaxI_asymmetry hq hu hM hL hnotConj
      hpTau1 hpTau1L hPML hP.2 hQsylML hUsylML hPNQ hPU
      hregQP hregUP hNQL hNUM

  exact
    { E₃_E₁_regular := hregE₃E₁
      sigma_E₃_regular :=
        semiregular_of_prime_action_of_centralizer_eq_bot
          hprimeE₃ hSigmaE₃
      sigma_P_centralizer_ne_bot := hSigmaP }

/-- `BGsection13.v: tau13_nonregular`, Bender--Glauberman Corollary
13.11. -/
theorem tau13_nonregular
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : sigma_complement M E E₁ E₂ E₃)
    (hnotRegular :
      ¬ IsSemiregularConjugation (sigmaCore M) E₃) :
    Tau13NonregularConclusion M E E₁ E₃ := by
  classical
  have hctx : SigmaComplementContext E E₁ E₂ E₃ :=
    sigma_compl_context hM hCompl
  have hE₂ : E₂ = ⊥ := by
    by_contra hE₂ne
    have hcardNe : Nat.card E₂ ≠ 1 :=
      (E₂.one_lt_card_iff_ne_bot.mpr hE₂ne).ne'
    let q : ℕ := Nat.minFac (Nat.card E₂)
    have hq : q.Prime := Nat.minFac_prime hcardNe
    letI : Fact q.Prime := ⟨hq⟩
    have hqE₂ : q ∣ Nat.card E₂ := Nat.minFac_dvd _
    have hqTau2 : q ∈ tau2Primes M :=
      hCompl.hall_E₂.isPiNumber_card hq (by
        rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          hCompl.E₂_le_E]
        exact hqE₂)
    obtain ⟨A, hAE, _hAM, hA⟩ :=
      ex_tau2Elem hCompl.E_le_M hCompl.hall_E hqTau2
    exact hnotRegular
      (tau2_regular hM hCompl hqTau2 hAE hA).E₃_regular
  have hE₁ne : E₁ ≠ ⊥ := hctx.E₂_eq_bot_imp_E₁_ne_bot hE₂
  have hsd : IsInternalSemidirectProductIn E₃ E₁ E := by
    simpa only [hE₂, bot_sup_eq] using hctx.E₃_E₂₁_sdprod
  have hsupE : E₃ ⊔ E₁ = E := by
    have htop : E₃.subgroupOf E ⊔ E₁.subgroupOf E = ⊤ :=
      hsd.2.2.2.sup_eq_top
    calc
      E₃ ⊔ E₁ =
          (E₃.subgroupOf E).map E.subtype ⊔
            (E₁.subgroupOf E).map E.subtype := by
        rw [Subgroup.map_subgroupOf_eq_of_le hCompl.E₃_le_E,
          Subgroup.map_subgroupOf_eq_of_le hCompl.E₁_le_E]
      _ = (E₃.subgroupOf E ⊔ E₁.subgroupOf E).map E.subtype := by
        rw [Subgroup.map_sup]
      _ = (⊤ : Subgroup E).map E.subtype :=
        congrArg (Subgroup.map E.subtype) htop
      _ = E := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]

  have hLinesCentE₃ :
      ∀ {r : ℕ} [Fact r.Prime] {X : Subgroup G},
        RankOneLineIn r E₁ X →
          X ≤ Subgroup.centralizer (E₃ : Set G) := by
    intro r _ X hX
    by_contra hnotCent
    exact hnotRegular
      (tau13_regular hM hCompl hX hnotCent).sigma_E₃_regular

  have hprimeE : IsPrimeAction (sigmaCore M) E := by
    by_cases hE₃bot : E₃ = ⊥
    · have hprimeE₁ := tau1_primact_Msigma hM hCompl.E_le_M
        hCompl.hall_E hCompl.E₁_le_E hCompl.hall_E₁
      have hE₁eqE : E₁ = E := by
        simpa only [hE₃bot, bot_sup_eq] using hsupE
      simpa only [hE₁eqE] using hprimeE₁
    · have hnotReg31 :
          ¬ IsSemiregularConjugation E₃ E₁ := by
        intro hreg31
        have hE₁cardNe : Nat.card E₁ ≠ 1 :=
          (E₁.one_lt_card_iff_ne_bot.mpr hE₁ne).ne'
        let r : ℕ := Nat.minFac (Nat.card E₁)
        have hr : r.Prime := Nat.minFac_prime hE₁cardNe
        letI : Fact r.Prime := ⟨hr⟩
        obtain ⟨X, hXE₁, hX⟩ := exists_rankOne_le_of_prime_dvd_tau13
          (Nat.minFac_dvd (Nat.card E₁))
        have hXline : RankOneLineIn r E₁ X := ⟨hXE₁, hX⟩
        have hE₃centX : E₃ ≤ Subgroup.centralizer (X : Set G) :=
          centralizer_le_symm_tau13 (hLinesCentE₃ hXline)
        have hfixed : E₃ ≤ centralizerWithin E₃ X :=
          le_inf le_rfl hE₃centX
        have hbot := centralizerWithin_eq_bot_of_semiregular
          hreg31 hXE₁ hX.ne_bot
        rw [hbot] at hfixed
        exact hE₃bot (le_bot_iff.mp hfixed)
      have hprimeJoin := tau13_primact_Msigma hM hCompl hnotReg31
      simpa only [hsupE] using hprimeJoin

  have hnormalLines :
      ∀ {r : ℕ} [Fact r.Prime] {X : Subgroup G},
        RankOneLineIn r E X → (X.subgroupOf E).Normal := by
    intro r _ X hX
    have hXne : X ≠ ⊥ := hX.2.ne_bot
    have hrX : r ∣ Nat.card X :=
      hX.2.isPGroup.card_eq_or_dvd.resolve_left
        (fun hcard ↦ hXne (Subgroup.card_eq_one.mp hcard))
    have hcardE : Nat.card E₃ * Nat.card E₁ = Nat.card E := by
      rw [← Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
        hCompl.E₃_le_E,
        ← Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
          hCompl.E₁_le_E]
      exact hsd.2.2.2.card_mul_card
    have hrE : r ∣ Nat.card E :=
      hrX.trans (Subgroup.card_dvd_of_le hX.1)
    have hrFactor : r ∣ Nat.card E₃ ∨ r ∣ Nat.card E₁ := by
      rw [← hcardE] at hrE
      exact (Fact.out : r.Prime).dvd_mul.mp hrE
    rcases hrFactor with hrE₃ | hrE₁
    · have hrTau3 : r ∈ tau3Primes M :=
        hCompl.hall_E₃.isPiNumber_card Fact.out (by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
            hCompl.E₃_le_E]
          exact hrE₃)
      have hXE₃ : X ≤ E₃ :=
        le_normal_isHall_of_isPiNumber_tau13 hctx.E₃_normal
          hCompl.hall_E₃ hX.1
          (hX.2.isPGroup.isPiNumber_natCard hrTau3)
      letI : IsCyclic E₃ := hctx.E₃_cyclic
      let XE₃ : Subgroup E₃ := X.subgroupOf E₃
      have hXE₃char : XE₃.Characteristic :=
        subgroup_characteristic_of_isCyclic_tau13 XE₃
      letI : XE₃.Characteristic := hXE₃char
      have hEnormE₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          hCompl.E₃_le_E).mp hctx.E₃_normal
      have hEnormX : E ≤ Subgroup.normalizer (X : Set G) := by
        have hnorm := hEnormE₃.trans
          (characteristic_map_subtype_le_normalizer_tau13 E₃ XE₃)
        simpa only [XE₃,
          Subgroup.map_subgroupOf_eq_of_le hXE₃] using hnorm
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hX.1).mpr
        hEnormX
    · have hrTau1 : r ∈ tau1Primes M :=
        hCompl.hall_E₁.isPiNumber_card Fact.out (by
          rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq
            hCompl.E₁_le_E]
          exact hrE₁)
      have hsolE : IsSolvable E :=
        sigma_compl_sol hCompl.E_le_M hCompl.hall_E
      obtain ⟨e, hXE₁e, hE₁eE, _hHallE₁e,
          _hfit, _hdiv, _htransport⟩ :=
        exists_ambient_isHall_map_conj_ge_of_isSolvable
          (K := E) (A := X) (H := E₁)
          hX.1 hCompl.E₁_le_E hsolE
          (hX.2.isPGroup.isPiNumber_natCard hrTau1)
          hCompl.hall_E₁
      let ee : G ≃* G := MulAut.conj (e : G)
      let E₁e : Subgroup G := E₁.map ee.toMonoidHom
      change X ≤ E₁e at hXE₁e
      change E₁e ≤ E at hE₁eE
      let X₀ : Subgroup G :=
        X.map (MulAut.conj ((e : G)⁻¹)).toMonoidHom
      have hX₀E₁ : X₀ ≤ E₁ := by
        have hmapped := Subgroup.map_mono
          (f := (MulAut.conj ((e : G)⁻¹)).toMonoidHom) hXE₁e
        simpa only [X₀, E₁e, ee, map_conj_inv_map_conj_tau13]
          using hmapped
      have hX₀line : IsElementaryAbelianOfRank r 1 X₀ :=
        hX.2.map_of_injective
          (MulAut.conj ((e : G)⁻¹)).toMonoidHom
          (MulAut.conj ((e : G)⁻¹)).injective
      have hX₀centE₃ : X₀ ≤ Subgroup.centralizer (E₃ : Set G) :=
        hLinesCentE₃ ⟨hX₀E₁, hX₀line⟩
      have hEnormE₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer
          hCompl.E₃_le_E).mp hctx.E₃_normal
      have hE₃map : E₃.map ee.toMonoidHom = E₃ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp (hEnormE₃ e.property)
      have hX₀map : X₀.map ee.toMonoidHom = X := by
        dsimp only [X₀, ee]
        rw [map_conj_map_conj_tau13]
        simpa only [mul_inv_cancel] using map_conj_one_tau13 X
      have hXcentE₃ : X ≤ Subgroup.centralizer (E₃ : Set G) := by
        have hmapped := Subgroup.map_mono
          (f := ee.toMonoidHom) hX₀centE₃
        rw [map_centralizer_equiv_tau13 E₃ ee,
          hE₃map, hX₀map] at hmapped
        exact hmapped
      have hE₃normX : E₃ ≤ Subgroup.normalizer (X : Set G) :=
        (centralizer_le_symm_tau13 hXcentE₃).trans
          (Subgroup.centralizer_le_normalizer (X : Set G))
      have hE₁ecyclic : IsCyclic E₁e :=
        (ee.subgroupMap E₁).isCyclic.mp hctx.E₁_cyclic
      letI : IsCyclic E₁e := hE₁ecyclic
      let XE₁e : Subgroup E₁e := X.subgroupOf E₁e
      have hXE₁echar : XE₁e.Characteristic :=
        subgroup_characteristic_of_isCyclic_tau13 XE₁e
      letI : XE₁e.Characteristic := hXE₁echar
      have hE₁enormX : E₁e ≤ Subgroup.normalizer (X : Set G) := by
        have hnorm := (Subgroup.le_normalizer : E₁e ≤
          Subgroup.normalizer (E₁e : Set G)) |>.trans
            (characteristic_map_subtype_le_normalizer_tau13 E₁e XE₁e)
        simpa only [XE₁e,
          Subgroup.map_subgroupOf_eq_of_le hXE₁e] using hnorm
      have hEmap : E.map ee.toMonoidHom = E :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp
          ((Subgroup.le_normalizer : E ≤
            Subgroup.normalizer (E : Set G)) e.property)
      have hsupEe : E₃ ⊔ E₁e = E := by
        have hmapped := congrArg (fun K : Subgroup G ↦
          K.map ee.toMonoidHom) hsupE
        rw [Subgroup.map_sup, hE₃map, hEmap] at hmapped
        exact hmapped
      have hEnormX : E ≤ Subgroup.normalizer (X : Set G) := by
        rw [← hsupEe]
        exact sup_le hE₃normX hE₁enormX
      exact (Subgroup.normal_subgroupOf_iff_le_normalizer hX.1).mpr
        hEnormX

  exact
    { E₁_ne_bot := hE₁ne
      E₃_E₁_sdprod := hsd
      sigma_prime_action := hprimeE
      rankOne_normal := hnormalLines }

/-! ## Lemmas 13.12 and 13.13 -/

/-- `BGsection13.v: tau12_regular`, Bender--Glauberman Lemma 13.12. -/
theorem tau12_regular
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E P A : Subgroup G} {p q : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau1Primes M)
    (hP : RankOneLineIn p E P)
    (hqTau : q ∈ tau2Primes M)
    (hAE : A ≤ E)
    (hA : IsElementaryAbelianOfRank q 2 A)
    (hCAP : centralizerWithin A P ≠ ⊥) :
    centralizerWithin (sigmaCore M) P = ⊥ := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  letI : Fact q.Prime := ⟨hqTau.1⟩
  by_contra hfixed
  have hPne : P ≠ ⊥ := hP.2.ne_bot
  have hPp : IsPGroup p P := hP.2.isPGroup
  have hsolE : IsSolvable E := sigma_compl_sol hEM hHallE
  have hTau := tau2_compl_context hM hEM hHallE hqTau hAE hA
  obtain ⟨E₁, hPE₁, hE₁E, hHallE₁⟩ :=
    Submission.OddOrder.MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
      hP.1 hsolE
      (tau1Primes M) (hPp.isPiNumber_natCard hpTau)
  obtain ⟨E₃, hE₃E, hHallE₃⟩ := (ex_tau13_compl hEM hHallE).2
  obtain ⟨E₂, _hE₂E, _hHallE₂, hCompl⟩ :=
    ex_tau2_compl hEM hHallE hE₁E hHallE₁ hE₃E hHallE₃
  have hreg := tau2_regular hM hCompl hqTau hAE hA
  have hPnotCentA : ¬ P ≤ Subgroup.centralizer (A : Set G) := by
    intro hPcentA
    have hPactor : P ≤ centralizerWithin E₁ A :=
      le_inf hPE₁ hPcentA
    have hbot := centralizerWithin_eq_bot_of_semiregular
      hreg.centralizer_E₁_regular hPactor hPne
    exact hfixed hbot

  let Y : Subgroup G := centralizerWithin A P
  have hYA : Y ≤ A := centralizerWithin_le_left A P
  have hYne : Y ≠ ⊥ := by simpa only [Y] using hCAP
  have hYproper : Y ≠ A := by
    intro hYAeq
    apply hPnotCentA
    have hAcentP : A ≤ Subgroup.centralizer (P : Set G) := by
      intro a ha
      exact (show a ∈ Y from hYAeq ▸ ha).2
    exact centralizer_le_symm_tau13 hAcentP
  have hYline : IsElementaryAbelianOfRank q 1 Y :=
    rankOne_of_nontrivial_proper_le_rankTwo_tau13
      hA hYA hYne hYproper
  have hYE : Y ≤ E := hYA.trans hAE
  have hYcentP : Y ≤ Subgroup.centralizer (P : Set G) := inf_le_right
  have hYlineCentEP : RankOneLineIn q (centralizerWithin E P) Y :=
    ⟨le_inf hYE hYcentP, hYline⟩
  have hSigmaPLeY : centralizerWithin (sigmaCore M) P ≤
      centralizerWithin (sigmaCore M) Y :=
    cent_tau1Elem_Msigma hM hEM hHallE hpTau hqTau.1
      hP hYlineCentEP
  have hSigmaYne : centralizerWithin (sigmaCore M) Y ≠ ⊥ := by
    intro hSigmaY
    apply hfixed
    apply le_antisymm
    · rw [hSigmaY] at hSigmaPLeY
      exact hSigmaPLeY
    · exact bot_le
  have hYunique :
      minSimple_max_groups_of (G := G)
          (Subgroup.centralizer (Y : Set G) : Set G) = {M} :=
    hTau.line_centralizer_unique hYE hYline hSigmaYne

  have hAne : A ≠ ⊥ := hA.ne_bot
  have hAq : IsPGroup q A := hA.isPGroup
  have hAproper : A < ⊤ := mFT_pgroup_proper A hAq
  have hNAproper : Subgroup.normalizer (A : Set G) < ⊤ :=
    mFT_norm_proper A hAne hAproper
  obtain ⟨L, hL, hNAL⟩ :=
    mmax_exists (Subgroup.normalizer (A : Set G)) hNAproper
  have hEnormA : E ≤ Subgroup.normalizer (A : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAE).mp hTau.A_normal
  have hEL : E ≤ L := hEnormA.trans hNAL
  have hAL : A ≤ L := hAE.trans hEL
  have hPL : P ≤ L := hP.1.trans hEL
  have hprimeData := primes_norm_tau2Elem hM hEM hHallE hqTau
    hAE hA hL hNAL
  have hqSigmaL : q ∈ sigmaPrimes L :=
    (hprimeData.tau2_classification hqTau).1
  have hAinSigmaL : A ≤ sigmaCore L :=
    le_normal_isHall_of_isPiNumber_tau13
      (sigmaCore_normal L) (Msigma_Hall hL) hAL
      (hA.isPGroup.isPiNumber_natCard hqSigmaL)

  let C : Subgroup G := centralizerWithin E A
  let CE : Subgroup E := C.subgroupOf E
  have hCnormal : CE.Normal := by
    simpa only [C, CE] using
      (tau1_cent_tau2Elem_factor hM hEM hHallE hqTau hAE hA).centralizer_normal
  have hpQuotient : p ∣ CE.index := by
    by_contra hpIndex
    have hcop : (Nat.card (P.subgroupOf E)).Coprime CE.index := by
      rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hP.1,
        hP.2.card_eq, pow_one]
      exact (Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpIndex
    have hPCE : P.subgroupOf E ≤ CE :=
      le_normal_of_coprime_index_tau13 hCnormal hcop
    apply hPnotCentA
    intro x hx
    have hxCE : (⟨x, hP.1 hx⟩ : E) ∈ CE := hPCE hx
    exact hxCE.2
  have hpClassL : p ∈ tau1Primes L ∨ p ∈ tau2Primes L :=
    hprimeData.quotient_tau12 (Fact.out : p.Prime) hpQuotient
  have hLneM : L ≠ M := by
    intro hLM
    subst L
    exact hqTau.2.1 hqSigmaL
  have hpNotSigmaL : p ∉ sigmaPrimes L :=
    hpClassL.elim (fun h ↦ h.2.1) (fun h ↦ h.2.1)
  obtain ⟨F, hPF, hFL, hHallF⟩ :=
    Submission.OddOrder.MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
      hPL (mmax_sol hL) (sigmaPrimes L)ᶜ
        (hPp.isPiNumber_natCard hpNotSigmaL)
  have hYinSigmaCentP : Y ≤ centralizerWithin (sigmaCore L) P :=
    le_inf (hYA.trans hAinSigmaL) hYcentP
  have hSigmaLPne : centralizerWithin (sigmaCore L) P ≠ ⊥ := by
    intro hbot
    apply hYne
    apply le_bot_iff.mp
    rw [← hbot]
    exact hYinSigmaCentP

  rcases hpClassL with hpTau1L | hpTau2L
  · obtain ⟨F₁, hPF₁, hF₁F, hHallF₁⟩ :=
      Submission.OddOrder.MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
        hPF
        (sigma_compl_sol hFL hHallF) (tau1Primes L)
        (hPp.isPiNumber_natCard hpTau1L)
    have hLunique := cent_cent_Msigma_tau1_uniq hL hFL hHallF
      hF₁F hHallF₁ hPF₁ hPne hYinSigmaCentP hYline
    have hCYL : Subgroup.centralizer (Y : Set G) ≤ L :=
      (mem_uniq_mmax hLunique.1).2
    have hLM : L = M := eq_uniq_mmax hYunique hL hCYL
    exact hLneM hLM
  · obtain ⟨B, hBF, _hBL, hB⟩ := ex_tau2Elem hFL hHallF hpTau2L
    have hTauL := tau2_compl_context hL hFL hHallF hpTau2L hBF hB
    have hPunique :
        minSimple_max_groups_of (G := G)
          (Subgroup.centralizer (P : Set G) : Set G) = {L} :=
      hTauL.line_centralizer_unique hPF hP.2 hSigmaLPne
    have hCPL : Subgroup.centralizer (P : Set G) ≤ L :=
      (mem_uniq_mmax hPunique).2
    have hInfBot : sigmaCore M ⊓ L = ⊥ :=
      (tau2_context hM hqTau (hAE.trans hEM) hA)
        |>.maximal_intersection_eq_bot ⟨hL, hAL⟩ hLneM
    have hSigmaPInf : centralizerWithin (sigmaCore M) P ≤
        sigmaCore M ⊓ L :=
      le_inf (centralizerWithin_le_left _ _) (inf_le_right.trans hCPL)
    apply hfixed
    apply le_antisymm
    · rw [hInfBot] at hSigmaPInf
      exact hSigmaPInf
    · exact bot_le

/-- `BGsection13.v: tau13_nonregular_sigma`, Bender--Glauberman Lemma
13.13. -/
theorem tau13_nonregular_sigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E P : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHallE : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hP : RankOneLineIn p E P)
    (hpTau13 : p ∈ tau1Primes M ∨ p ∈ tau3Primes M)
    (hfixed : centralizerWithin (sigmaCore M) P ≠ ⊥) :
    ∀ {Mstar : Subgroup G},
      Mstar ∈ minSimple_max_groups_of (G := G)
        (Subgroup.normalizer (P : Set G) : Set G) →
      p ∈ sigmaPrimes Mstar := by
  classical
  have hp : p.Prime := hpTau13.elim (fun hp₁ ↦ hp₁.1) (fun hp₃ ↦ hp₃.1)
  letI : Fact p.Prime := ⟨hp⟩
  have hpNotSigmaM : p ∉ sigmaPrimes M :=
    hpTau13.elim (fun h ↦ h.2.1) (fun h ↦ h.2.1)
  have hpNotTau2M : p ∉ tau2Primes M := by
    intro hpTau2
    exact hpTau13.elim
      (fun hpTau1 ↦ (tau2'1 M hpTau1) hpTau2)
      (fun hpTau3 ↦ (tau3'2 M hpTau2) hpTau3)
  have hpNoRankTwo : ¬ HasElementaryAbelianRankAtLeast p 2 M :=
    hpTau13.elim (fun h ↦ h.2.2.2.1) (fun h ↦ h.2.2.2.1)
  have hPne : P ≠ ⊥ := hP.2.ne_bot
  have hPp : IsPGroup p P := hP.2.isPGroup
  have hsolE : IsSolvable E := sigma_compl_sol hEM hHallE

  intro L hLof
  rcases prime_class_mmax_norm hLof.1 hPp hLof.2 with
    hpSigma | hpTau2
  · exact hpSigma
  · have hL := hLof.1
    have hNPL := hLof.2
    have hPL : P ≤ L := Subgroup.le_normalizer.trans hNPL

    let C : Subgroup G := centralizerWithin (sigmaCore M) P
    have hCne : C ≠ ⊥ := by simpa only [C] using hfixed
    have hCcardNe : Nat.card C ≠ 1 :=
      (C.one_lt_card_iff_ne_bot.mpr hCne).ne'
    let q : ℕ := Nat.minFac (Nat.card C)
    have hq : q.Prime := Nat.minFac_prime hCcardNe
    letI : Fact q.Prime := ⟨hq⟩
    obtain ⟨Q, hQC, hQline⟩ := exists_rankOne_le_of_prime_dvd_tau13
      (Nat.minFac_dvd (Nat.card C))
    have hQne : Q ≠ ⊥ := hQline.ne_bot
    have hQsigma : Q ≤ sigmaCore M :=
      hQC.trans (centralizerWithin_le_left _ _)
    have hQcentP : Q ≤ Subgroup.centralizer (P : Set G) :=
      hQC.trans inf_le_right
    have hqQ : q ∣ Nat.card Q := by
      rw [hQline.card_eq, pow_one]
    have hqSigmaM : q ∈ sigmaPrimes M := by
      rw [← pi_Msigma hM]
      exact ⟨hq, hqQ.trans (Subgroup.card_dvd_of_le hQsigma)⟩
    have hQp : IsPGroup q Q := hQline.isPGroup
    have hqp : q ≠ p := by
      intro hqp
      exact hpNotSigmaM (hqp ▸ hqSigmaM)
    have hQL : Q ≤ L :=
      hQcentP.trans (Subgroup.centralizer_le_normalizer (P : Set G)) |>.trans
        hNPL
    have hnotConj : ∀ g : G,
        L ≠ M.map (MulAut.conj g).toMonoidHom := by
      intro g hEq
      apply hpNotTau2M
      rw [← tau2J M g, ← hEq]
      exact hpTau2
    have hqNotSigmaL : q ∉ sigmaPrimes L := by
      intro hqSigmaL
      exact Set.disjoint_left.mp (sigma_partition hM hL hnotConj)
        hqSigmaM hqSigmaL

    have hPQcomm : P ≤ Subgroup.centralizer (Q : Set G) :=
      centralizer_le_symm_tau13 hQcentP
    have hcopPQ : (Nat.card P).Coprime (Nat.card Q) :=
      IsPGroup.coprime_card_of_ne p q hqp.symm P Q hPp hQp
    have hdisPQ : Disjoint P Q := Subgroup.disjoint_of_coprime_natCard hcopPQ
    have hcardPQ : Nat.card (P ⊔ Q : Subgroup G) =
        Nat.card P * Nat.card Q :=
      natCard_sup_eq_mul_of_disjoint_of_commute hdisPQ (by
        intro x hx y hy
        exact (Subgroup.mem_centralizer_iff.mp (hPQcomm hx) y hy).symm)
    have hPQpi : IsPiNumber (sigmaPrimes L)ᶜ
        (Nat.card (P ⊔ Q : Subgroup G)) := by
      rw [hcardPQ]
      exact (hPp.isPiNumber_natCard hpTau2.2.1).mul
        (hQp.isPiNumber_natCard hqNotSigmaL)
    have hPQL : P ⊔ Q ≤ L := sup_le hPL hQL
    obtain ⟨F, hPQF, hFL, hHallF⟩ :=
      Submission.OddOrder.MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
        hPQL (mmax_sol hL)
        (sigmaPrimes L)ᶜ hPQpi
    have hPF : P ≤ F := le_sup_left.trans hPQF
    have hQF : Q ≤ F := le_sup_right.trans hPQF
    obtain ⟨A, hAF, _hAL, hA⟩ := ex_tau2Elem hFL hHallF hpTau2
    have hTauL := tau2_compl_context hL hFL hHallF hpTau2 hAF hA
    have hPA : P ≤ A :=
      ((hTauL.rankOne_iff P).mp ⟨hPF, hP.2⟩).1

    have hCQleM : Subgroup.centralizer (Q : Set G) ≤ M := by
      rcases hpTau13 with hpTau1M | hpTau3M
      · obtain ⟨E₁, hPE₁, hE₁E, hHallE₁⟩ :=
          Submission.OddOrder.MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
            hP.1 hsolE
            (tau1Primes M) (hPp.isPiNumber_natCard hpTau1M)
        have hQwithin : Q ≤ centralizerWithin (sigmaCore M) P := hQC
        have huniq := cent_cent_Msigma_tau1_uniq hM hEM hHallE
          hE₁E hHallE₁ hPE₁ hPne hQwithin hQline
        exact (mem_uniq_mmax huniq.1).2
      · obtain ⟨E₃, hPE₃, hE₃E, hHallE₃⟩ :=
          Submission.OddOrder.MathlibSupport.exists_ambient_isHall_ge_of_isSolvable
            hP.1 hsolE
            (tau3Primes M) (hPp.isPiNumber_natCard hpTau3M)
        obtain ⟨E₁, hE₁E, hHallE₁⟩ :=
          (ex_tau13_compl hEM hHallE).1
        obtain ⟨E₂, _hE₂E, _hHallE₂, hCompl⟩ :=
          ex_tau2_compl hEM hHallE hE₁E hHallE₁
            hE₃E hHallE₃
        by_cases hregE₃ :
            IsSemiregularConjugation (sigmaCore M) E₃
        · have hbot := centralizerWithin_eq_bot_of_semiregular
            hregE₃ hPE₃ hPne
          have hQbot : Q ≤ ⊥ := by
            rw [← hbot]
            exact hQC
          exact (hQne (le_bot_iff.mp hQbot)).elim
        · have hnonreg := tau13_nonregular hM hCompl hregE₃
          have hcentEqP := hnonreg.sigma_prime_action.centralizer_eq
            hP.1 hPne
          have hcentEqE₁ := hnonreg.sigma_prime_action.centralizer_eq
            hE₁E hnonreg.E₁_ne_bot
          have hQwithinE₁ : Q ≤
              centralizerWithin (sigmaCore M) E₁ := by
            rw [hcentEqE₁, ← hcentEqP]
            exact hQC
          have huniq := cent_cent_Msigma_tau1_uniq hM hEM hHallE
            hE₁E hHallE₁ le_rfl hnonreg.E₁_ne_bot
            hQwithinE₁ hQline
          exact (mem_uniq_mmax huniq.1).2

    have hAnotCentQ : ¬ A ≤ Subgroup.centralizer (Q : Set G) := by
      intro hAcentQ
      apply hpNoRankTwo
      exact ⟨A, hAcentQ.trans hCQleM, hA⟩

    let CFA : Subgroup G := centralizerWithin F A
    let CFAF : Subgroup F := CFA.subgroupOf F
    have hfactor := tau1_cent_tau2Elem_factor hL hFL hHallF
      hpTau2 hAF hA
    have hCFAFnormal : CFAF.Normal := by
      simpa only [CFA, CFAF] using hfactor.centralizer_normal
    have hqQuotient : q ∣ CFAF.index := by
      by_contra hqIndex
      have hcop : (Nat.card (Q.subgroupOf F)).Coprime CFAF.index := by
        rw [Submission.OddOrder.MathlibSupport.natCard_subgroupOf_eq hQF,
          hQline.card_eq, pow_one]
        exact hq.coprime_iff_not_dvd.mpr hqIndex
      have hQCFA : Q.subgroupOf F ≤ CFAF :=
        le_normal_of_coprime_index_tau13 hCFAFnormal hcop
      apply hAnotCentQ
      exact centralizer_le_symm_tau13 (by
        intro x hx
        have hxCFA : (⟨x, hQF hx⟩ : F) ∈ CFAF := hQCFA hx
        exact hxCFA.2)
    have hqTau1L : q ∈ tau1Primes L :=
      hfactor.quotient_isPiNumber hq hqQuotient

    let D : Subgroup G := centralizerWithin A Q
    have hPcentQ : P ≤ Subgroup.centralizer (Q : Set G) := hPQcomm
    have hPD : P ≤ D := le_inf hPA hPcentQ
    have hDne : D ≠ ⊥ := by
      intro hD
      apply hPne
      exact le_bot_iff.mp (hPD.trans_eq hD)
    have hDproper : D ≠ A := by
      intro hDA
      apply hAnotCentQ
      rw [← hDA]
      exact inf_le_right
    have hDline : IsElementaryAbelianOfRank p 1 D :=
      rankOne_of_nontrivial_proper_le_rankTwo_tau13 hA
        (centralizerWithin_le_left A Q) hDne hDproper
    have hDeqP : D = P := by
      symm
      apply Subgroup.eq_of_le_of_card_ge hPD
      rw [hDline.card_eq, hP.2.card_eq]
    have hregQ : centralizerWithin (sigmaCore L) Q = ⊥ :=
      tau12_regular hL hFL hHallF hqTau1L
        ⟨hQF, hQline⟩ hpTau2 hAF hA (by
          simpa only [D] using hDne)
    have hcommNe : tau1ActionCommutator A Q ≠ ⊥ := by
      intro hcomm
      apply hAnotCentQ
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have haction := tau1_act_tau2 hL hFL hHallF hpTau2 hAF hA
      hqTau1L hQF hQline hregQ hcommNe
    exfalso
    apply haction.A1_centralizer_not_le
    simpa only [tau1ActionFixedLine, D, hDeqP] using
      (Subgroup.centralizer_le_normalizer (P : Set G)).trans hNPL

end

end Submission.OddOrder.BG.Section13
