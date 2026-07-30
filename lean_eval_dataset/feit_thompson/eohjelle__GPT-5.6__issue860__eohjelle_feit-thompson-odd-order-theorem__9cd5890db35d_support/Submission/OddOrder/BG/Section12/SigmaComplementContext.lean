import Submission.OddOrder.BG.Section12.ComplementElementRank
import Submission.OddOrder.BG.Section10.SigmaNormalizerRankTwo
import Submission.OddOrder.BG.Section10.SigmaDisjointness
import Submission.OddOrder.BG.Section10.SigmaTransitivity
import Submission.OddOrder.BG.Section11.ExceptionalStructure
import Submission.OddOrder.MathlibSupport.ElementaryAbelianSup
import Submission.OddOrder.MathlibSupport.NilpotentPrimeCores
import Submission.OddOrder.MathlibSupport.PPrimeFactorIntersection

/-!
# Bender--Glauberman Section 12: structure of a sigma complement

This file ports `BGsection12.v`, lines 243--486.  The two displayed
semidirect products in `sigma_compl_context` are made explicit as three
internal semidirect-product assertions: the inner product `E₂ ⋊ E₁`, the
outer product `E₃ ⋊ (E₂ ⋊ E₁)`, and the left-associated product
`(E₃ ⋊ E₂) ⋊ E₁`.
-/

namespace Submission.OddOrder.BG.Section12

open Submission.OddOrder.BG.Section04
open Submission.OddOrder.BG.Section07
open Submission.OddOrder.BG.Section10
open Submission.OddOrder.BG.Section11
open Submission.OddOrder.MathlibSupport
open Submission.OddOrder.PF
open scoped Pointwise IsMulCommutative

noncomputable section

universe u

/-- The proposition-valued expansion of the five conclusions of
`BGsection12.v: sigma_compl_context`. -/
structure SigmaComplementContext
    {G : Type u} [Group G]
    (E E₁ E₂ E₃ : Subgroup G) : Prop where
  E₃_le_commutator : E₃ ≤ (_root_.commutator E).map E.subtype
  E₃_normal : (E₃.subgroupOf E).Normal
  E₂_eq_bot_imp_E₁_ne_bot : E₂ = ⊥ → E₁ ≠ ⊥
  E₁_cyclic : IsCyclic E₁
  E₃_cyclic : IsCyclic E₃
  E₂₁_sdprod : IsInternalSemidirectProductIn E₂ E₁ (E₂ ⊔ E₁)
  E₃_E₂₁_sdprod : IsInternalSemidirectProductIn E₃ (E₂ ⊔ E₁) E
  E₃₂_E₁_sdprod : IsInternalSemidirectProductIn (E₃ ⊔ E₂) E₁ E
  centralizerWithin_eq_bot : centralizerWithin E₃ E = ⊥

/-- A `pi`-subgroup lies in a normal `pi`-Hall subgroup. -/
private theorem le_normal_isHall_of_isPiNumber_12
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
  have horderOne : orderOf (qC xC) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop horderL horderIndex
  have hqOne : qC xC = 1 := orderOf_eq_one_iff.mp horderOne
  have hxKC : xC ∈ KC :=
    (QuotientGroup.eq_one_iff xC).mp (by simpa [qC] using hqOne)
  exact hxKC

/-- Quotient form of the commutator calculation used in Lemma 12.3.

Modulo `S`, the normal subgroup `S ⊔ A` is a `p`-group.  Thus a
`p'`-subgroup `K` can meet it only inside `S`; normality puts `[K,A]` in
that intersection. -/
private theorem commutator_le_inf_of_normal_sup_of_coprime
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {H S A B K : Subgroup G}
    (hSH : S ≤ H) (_hAH : A ≤ H) (hBH : B ≤ H)
    (hAB : A ≤ B) (hKH : K ≤ H)
    (hSnormal : (S.subgroupOf H).Normal)
    (hSBnormal : ((S ⊔ B).subgroupOf H).Normal)
    (hAnormK : A ≤ Subgroup.normalizer (K : Set G))
    (hBp : IsPGroup p B)
    (hKp' : IsPPrimeSubgroup p K) :
    ⁅K, A⁆ ≤ K ⊓ S := by
  let SH : Subgroup H := S.subgroupOf H
  let BH : Subgroup H := B.subgroupOf H
  let KH : Subgroup H := K.subgroupOf H
  let U : Subgroup H := (S ⊔ B).subgroupOf H
  letI : SH.Normal := by
    dsimp [SH]
    exact hSnormal
  let q : H →* H ⧸ SH := QuotientGroup.mk' SH
  have hBHp : IsPGroup p BH := by
    let eBH : BH ≃* B := Subgroup.subgroupOfEquivOfLe hBH
    exact hBp.of_equiv eBH.symm
  have hUeq : U = SH ⊔ BH := by
    dsimp [U, SH, BH]
    exact Subgroup.subgroupOf_sup hSH hBH
  have hSHmap : SH.map q = ⊥ := by
    apply (Subgroup.map_eq_bot_iff SH).mpr
    simp [q, QuotientGroup.ker_mk']
  have hfactor : IsPGroup p (U.map q) := by
    rw [hUeq, Subgroup.map_sup, hSHmap, bot_sup_eq]
    exact hBHp.map q
  have hKHp' : IsPPrimeSubgroup p KH := by
    change Nat.Coprime p (Nat.card KH)
    rw [natCard_subgroupOf_eq hKH]
    exact hKp'
  have hinf : KH ⊓ U ≤ SH :=
    inf_le_of_isPPrimeSubgroup_of_factor_isPGroup hKHp' hfactor
  have hcommK : ⁅K, A⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAnormK
  have hHnormSB : H ≤ Subgroup.normalizer ((S ⊔ B : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sup_le hSH hBH)).mp
      hSBnormal
  have hcommSB : ⁅K, A⁆ ≤ S ⊔ B :=
    (Subgroup.commutator_mono le_rfl (hAB.trans le_sup_right)).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hKH.trans hHnormSB))
  intro x hx
  have hxH : x ∈ H := hKH (hcommK hx)
  let xH : H := ⟨x, hxH⟩
  have hxinf : xH ∈ KH ⊓ U := ⟨hcommK hx, hcommSB hx⟩
  refine ⟨hcommK hx, ?_⟩
  change xH ∈ SH
  exact hinf hxinf

/-- Variant of the preceding calculation where the normal overgroup is
given directly and only its image modulo `S` is assumed to be a `p`-group. -/
private theorem commutator_le_inf_of_normal_factor_of_coprime
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    {H S A K U : Subgroup G}
    (_hSH : S ≤ H) (_hAH : A ≤ H) (hKH : K ≤ H) (hUH : U ≤ H)
    (hAU : A ≤ U)
    [hSnormal : (S.subgroupOf H).Normal]
    (hUnormal : (U.subgroupOf H).Normal)
    (hAnormK : A ≤ Subgroup.normalizer (K : Set G))
    (hfactor : IsPGroup p
      ((U.subgroupOf H).map
        (QuotientGroup.mk' (S.subgroupOf H))))
    (hKp' : IsPPrimeSubgroup p K) :
    ⁅K, A⁆ ≤ K ⊓ S := by
  let SH : Subgroup H := S.subgroupOf H
  let KH : Subgroup H := K.subgroupOf H
  let UH : Subgroup H := U.subgroupOf H
  let q : H →* H ⧸ SH := QuotientGroup.mk' SH
  have hKHp' : IsPPrimeSubgroup p KH := by
    change Nat.Coprime p (Nat.card KH)
    rw [natCard_subgroupOf_eq hKH]
    exact hKp'
  have hfactor' : IsPGroup p (UH.map q) := by
    simpa [SH, UH, q] using hfactor
  have hinf : KH ⊓ UH ≤ SH :=
    inf_le_of_isPPrimeSubgroup_of_factor_isPGroup hKHp' hfactor'
  have hcommK : ⁅K, A⁆ ≤ K :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hAnormK
  have hHnormU : H ≤ Subgroup.normalizer (U : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUH).mp hUnormal
  have hcommU : ⁅K, A⁆ ≤ U :=
    (Subgroup.commutator_mono le_rfl hAU).trans
      (Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hKH.trans hHnormU))
  intro x hx
  have hxH : x ∈ H := hKH (hcommK hx)
  let xH : H := ⟨x, hxH⟩
  have hxinf : xH ∈ KH ⊓ UH := ⟨hcommK hx, hcommU hx⟩
  refine ⟨hcommK hx, ?_⟩
  change xH ∈ SH
  exact hinf hxinf

/-! ### Local finite-group adapters for Lemma 12.1 -/

private theorem map_conj_one_12_1
    {G : Type*} [Group G] (H : Subgroup G) :
    H.map (MulAut.conj 1).toMonoidHom = H := by
  convert H.map_id using 1
  ext x
  simp

private theorem natCard_commutator_eq_of_mulEquiv_12_1
    {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    (e : A ≃* B) :
    Nat.card (_root_.commutator A) =
      Nat.card (_root_.commutator B) := by
  have hmap : (_root_.commutator A).map e.toMonoidHom =
      _root_.commutator B := by
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr e.surjective]
    exact (_root_.commutator_def B).symm
  rw [← hmap, Subgroup.card_map_of_injective e.injective]

/-- Restrict a Hall subgroup to an intermediate subgroup containing it. -/
private theorem isHall_subgroupOf_of_le_12_1
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

/-- A Hall subgroup of a finite nilpotent group is its corresponding
prime-set core. -/
private theorem hall_eq_piCore_of_isNilpotent_12_1
    {K : Type u} [Group K] [Finite K] [Group.IsNilpotent K]
    {pi : Set ℕ} {H : Subgroup K} (hH : IsHall pi H) :
    H = piCore pi K := by
  have hle : H ≤ piCore pi K := by
    calc
      H = (sylowSup H).map H.subtype := by
        rw [sylowSup_eq_top]
        exact H.range_subtype.symm.trans
          (MonoidHom.range_eq_map H.subtype)
      _ = ⨆ p : {p : ℕ // p.Prime},
          ((Classical.choice
            (Sylow.nonempty (p := (p : ℕ)) (G := H)) : Sylow p H) :
            Subgroup H).map H.subtype := by
        rw [sylowSup, Subgroup.map_iSup]
      _ ≤ piCore pi K := by
        apply iSup_le
        intro p
        letI : Fact (p : ℕ).Prime := ⟨p.property⟩
        let P : Sylow (p : ℕ) H := Classical.choice Sylow.nonempty
        by_cases hPbot : (P : Subgroup H) = ⊥
        · simp [P, hPbot]
        have hpP : (p : ℕ) ∣ Nat.card P :=
          P.isPGroup'.card_eq_or_dvd.resolve_left
            (fun hcard ↦ hPbot (Subgroup.card_eq_one.mp hcard))
        have hpPi : (p : ℕ) ∈ pi :=
          hH.isPiNumber_card p.property
            (hpP.trans (P : Subgroup H).card_subgroup_dvd_card)
        have hmapP : IsPGroup (p : ℕ)
            ((P : Subgroup H).map H.subtype) :=
          P.isPGroup'.map H.subtype
        exact hmapP.le_pCore_of_isNilpotent.trans
          (le_piCore (by infer_instance)
            (pCore_isPGroup.isPiNumber_natCard hpPi))
  have hrelPi : IsPiNumber pi (H.relIndex (piCore pi K)) :=
    (piCore_isPiNumber pi).of_dvd
      (Subgroup.relIndex_dvd_card H (piCore pi K))
  have hrelCompl : IsPiNumber piᶜ
      (H.relIndex (piCore pi K)) :=
    hH.isPiNumber_index.of_dvd
      (Subgroup.relIndex_dvd_index_of_le hle)
  have hcop : (H.relIndex (piCore pi K)).Coprime
      (H.relIndex (piCore pi K)) :=
    hrelPi.coprime_compl hrelCompl
  have hone : H.relIndex (piCore pi K) = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop dvd_rfl dvd_rfl
  exact le_antisymm hle (Subgroup.relIndex_eq_one.mp hone)

/-- A Sylow subgroup of a Hall subgroup is Sylow in the ambient group,
with the expected ambient image. -/
private theorem exists_ambient_sylow_eq_of_sylow_hall_12_1
    {G : Type u} [Group G] [Finite G]
    {pi : Set ℕ} {p : ℕ} (hp : p.Prime)
    {K H : Subgroup G} (hKH : K ≤ H)
    (hKHall : IsHall pi (K.subgroupOf H))
    (hpPi : p ∈ pi) (P : Sylow p K) :
    ∃ Q : Sylow p H,
      (Q : Subgroup H).map H.subtype =
        (P : Subgroup K).map K.subtype := by
  letI : Fact p.Prime := ⟨hp⟩
  let e : K.subgroupOf H ≃* K :=
    Subgroup.subgroupOfEquivOfLe hKH
  let P' : Sylow p (K.subgroupOf H) :=
    P.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  let S : Subgroup H :=
    (P' : Subgroup (K.subgroupOf H)).map (K.subgroupOf H).subtype
  have hSp : IsPGroup p S := P'.isPGroup'.map (K.subgroupOf H).subtype
  have hpKindex : ¬ p ∣ (K.subgroupOf H).index := by
    intro hpIndex
    exact hKHall.isPiNumber_index hp hpIndex hpPi
  have hpSindex : ¬ p ∣ S.index := by
    dsimp only [S]
    rw [Subgroup.index_map_subtype]
    exact hp.not_dvd_mul P'.not_dvd_index hpKindex
  let Q : Sylow p H := hSp.toSylow hpSindex
  refine ⟨Q, ?_⟩
  change S.map H.subtype = (P : Subgroup K).map K.subtype
  dsimp only [S, P', Sylow.coe_mapSurjective]
  rw [Subgroup.map_map, Subgroup.map_map]
  apply congrArg (fun f : K →* G ↦ (P : Subgroup K).map f)
  ext x
  rfl

/-- A subgroup whose order is coprime to the index of a normal subgroup
lies in that normal subgroup. -/
private theorem le_normal_of_coprime_index_12_1
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

/-- The prime divisors of a sigma complement lie in one of the three tau
classes. -/
private theorem primeSupport_sigma_complement_subset_tau_12_1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M)) :
    primeSupport (Nat.card E) ⊆
      tau1Primes M ∪ tau2Primes M ∪ tau3Primes M := by
  intro p hpE
  have hp : p.Prime := hpE.1
  letI : Fact p.Prime := ⟨hp⟩
  have hpMcard : p ∣ Nat.card M :=
    hpE.2.trans (Subgroup.card_dvd_of_le hEM)
  have hpNotSigma : p ∉ sigmaPrimes M := by
    have hpEsub : p ∣ Nat.card (E.subgroupOf M) := by
      simpa [natCard_subgroupOf_eq hEM] using hpE.2
    exact hHall.isPiNumber_card hp hpEsub
  obtain ⟨x, hxorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := M) p hpMcard
  let X : Subgroup G := (Subgroup.zpowers x).map M.subtype
  have hXcard : Nat.card X = p := by
    dsimp only [X]
    rw [Subgroup.card_map_of_injective M.subtype_injective,
      Nat.card_zpowers, hxorder]
  have hXrank : IsElementaryAbelianOfRank p 1 X :=
    isElementaryAbelianOfRank_one_of_card_eq_prime hXcard
  have hRankOne : HasElementaryAbelianRankAtLeast p 1 M :=
    ⟨X, Subgroup.map_subtype_le _, hXrank⟩
  by_cases hRankTwo : HasElementaryAbelianRankAtLeast p 2 M
  · have hNoRankThree :
        ¬ HasElementaryAbelianRankAtLeast p 3 M := by
      intro hRankThree
      exact hpNotSigma (alpha_sub_sigma hM ⟨hp, hRankThree⟩)
    exact Or.inl (Or.inr
      ⟨hp, hpNotSigma, hRankTwo, hNoRankThree⟩)
  · by_cases hpDer : p ∣ Nat.card (_root_.commutator M)
    · exact Or.inr
        ⟨hp, hpNotSigma, hRankOne, hRankTwo, hpDer⟩
    · exact Or.inl (Or.inl
        ⟨hp, hpNotSigma, hRankOne, hRankTwo, hpDer⟩)

/-- The `tau3` divisibility condition passes from `M'` to the derived
subgroup of any sigma complement. -/
private theorem tau3_dvd_complement_commutator_12_1
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E : Subgroup G} {p : ℕ}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hEM : E ≤ M)
    (hHall : IsHall (sigmaPrimes M)ᶜ (E.subgroupOf M))
    (hpTau : p ∈ tau3Primes M) :
    p ∣ Nat.card (_root_.commutator E) := by
  classical
  letI : Fact p.Prime := ⟨hpTau.1⟩
  let S : Subgroup M := (sigmaCore M).subgroupOf M
  let T : Subgroup M := E.subgroupOf M
  have hSnormal : S.Normal := by
    simpa [S] using sigmaCore_normal M
  letI : S.Normal := hSnormal
  let Q := M ⧸ S
  let q : M →* Q := QuotientGroup.mk' S
  let DM : Subgroup M := _root_.commutator M
  let f : DM →* Q := q.comp DM.subtype
  have hpS : ¬ p ∣ Nat.card S := by
    intro hpCard
    exact hpTau.2.1 (sigmaCore_isPiNumber M hpTau.1 (by
      rwa [natCard_subgroupOf_eq (sigmaCore_le M)] at hpCard))
  have hkerS : f.ker.map DM.subtype ≤ S := by
    rintro _ ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff (x : M)).mp (f.mem_ker.mp hx)
  have hpKer : ¬ p ∣ Nat.card f.ker := by
    intro hp
    apply hpS
    have hpMap : p ∣ Nat.card (f.ker.map DM.subtype) := by
      simpa only [Subgroup.card_map_of_injective DM.subtype_injective]
        using hp
    exact hpMap.trans (Subgroup.card_dvd_of_le hkerS)
  have hcardDM : Nat.card DM =
      Nat.card f.ker * Nat.card f.range := by
    rw [← f.ker.card_mul_index, Subgroup.index_ker]
  have hpRange : p ∣ Nat.card f.range := by
    have hpProd : p ∣ Nat.card f.ker * Nat.card f.range := by
      rw [← hcardDM]
      exact hpTau.2.2.2.2
    rcases hpTau.1.dvd_mul.mp hpProd with hpK | hpR
    · exact (hpKer hpK).elim
    · exact hpR
  have hrange : f.range = DM.map q := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨x, x.property, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨(⟨x, hx⟩ : DM), rfl⟩
  have hmapDM : DM.map q = _root_.commutator Q := by
    dsimp only [DM]
    rw [map_commutator_eq,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective S)]
    exact (_root_.commutator_def Q).symm
  have hpQ : p ∣ Nat.card (_root_.commutator Q) := by
    rwa [hrange, hmapDM] at hpRange
  have hsd := sdprod_sigma hM hEM hHall
  have hcomp : S.IsComplement' T := by
    simpa [S, T] using hsd.2.2.2
  let eQT : Q ≃* T := hcomp.symm.QuotientMulEquiv
  let eTE : T ≃* E := Subgroup.subgroupOfEquivOfLe hEM
  have hcardQE : Nat.card (_root_.commutator Q) =
      Nat.card (_root_.commutator E) :=
    (natCard_commutator_eq_of_mulEquiv_12_1 eQT).trans
      (natCard_commutator_eq_of_mulEquiv_12_1 eTE)
  rwa [← hcardQE]

/-- A cyclic Sylow subgroup which occurs in the nilpotent derived subgroup
is normal and acts as a regular derived factor.  This packages the transfer
argument in the source proof of Lemma 12.1. -/
private theorem cyclic_sylow_le_commutator_and_regular_12_1
    {K : Type u} [Group K] [Finite K]
    {p : ℕ} [Fact p.Prime]
    (P : Sylow p K) (hcyc : IsCyclic P)
    (hpD : p ∣ Nat.card (_root_.commutator K))
    (hDnil : Group.IsNilpotent (_root_.commutator K)) :
    (P : Subgroup K) ≤ _root_.commutator K ∧
      centralizerWithin (P : Subgroup K) (⊤ : Subgroup K) = ⊥ := by
  classical
  letI : IsCyclic P := hcyc
  let D : Subgroup K := _root_.commutator K
  have hDnormal : D.Normal := by dsimp [D]; infer_instance
  letI : D.Normal := hDnormal
  have hpDindex : ¬ p ∣ D.index := by
    rcases P.not_dvd_card_commutator_or_not_dvd_index_commutator with
      hpCard | hpIndex
    · exact (hpCard hpD).elim
    · simpa [D] using hpIndex
  obtain ⟨n, hPcard⟩ := P.isPGroup'.exists_card_eq
  have hcopPD : Nat.Coprime (Nat.card P) D.index := by
    rw [hPcard]
    exact ((Fact.out : p.Prime).coprime_iff_not_dvd.mpr hpDindex).pow_left n
  have hPD : (P : Subgroup K) ≤ D :=
    le_normal_of_coprime_index_12_1 hDnormal hcopPD
  let PD : Subgroup D := (P : Subgroup K).subgroupOf D
  have hPDp : IsPGroup p PD := by
    let e : PD ≃* P := Subgroup.subgroupOfEquivOfLe hPD
    exact P.isPGroup'.of_equiv e.symm
  have hpPDindex : ¬ p ∣ PD.index := by
    change ¬ p ∣ (P : Subgroup K).relIndex D
    intro hpIndex
    apply P.not_dvd_index
    exact hpIndex.trans (Subgroup.relIndex_dvd_index_of_le hPD)
  let R : Sylow p D := hPDp.toSylow hpPDindex
  letI : Group.IsNilpotent D := hDnil
  have hcore : pCore p D = PD := by
    rw [pCore_eq_sylow_of_isNilpotent R]
    exact IsPGroup.toSylow_coe hPDp hpPDindex
  have hPDchar : PD.Characteristic := by
    rw [← hcore]
    infer_instance
  letI : PD.Characteristic := hPDchar
  have hPnormal : (P : Subgroup K).Normal := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hPD]
    infer_instance
  letI : (P : Subgroup K).Normal := hPnormal
  obtain ⟨L, hL⟩ :=
    (P : Subgroup K).exists_left_complement'_of_coprime
      P.card_coprime_index
  rcases P.commutator_eq_bot_or_commutator_eq_self hL with
    htriv | hperfect
  · have hLcentP : L ≤ Subgroup.centralizer ((P : Subgroup K) : Set K) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp htriv
    have hPnormL : (P : Subgroup K) ≤
        Subgroup.normalizer (L : Set K) :=
      (Subgroup.le_centralizer_iff.mp hLcentP).trans
        (Subgroup.centralizer_le_normalizer (L : Set K))
    have hLnormal : L.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      apply top_unique
      rw [← hL.sup_eq_top]
      exact sup_le Subgroup.le_normalizer hPnormL
    letI : L.Normal := hLnormal
    have hDleL : D ≤ L := by
      dsimp [D]
      exact Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
        hL.sup_eq_top hcyc.isMulCommutative
    have hPbot : (P : Subgroup K) = ⊥ := by
      apply le_bot_iff.mp
      rw [← disjoint_iff.mp hL.disjoint]
      exact fun x hx ↦ ⟨hDleL (hPD hx), hx⟩
    exact (P.ne_bot_of_dvd_card
      (hpD.trans D.card_subgroup_dvd_card) hPbot).elim
  · have hcopPL : Nat.Coprime (Nat.card P) (Nat.card L) := by
      rw [← hL.index_eq_card]
      exact P.card_coprime_index
    have hLnormP : L ≤
        Subgroup.normalizer ((P : Subgroup K) : Set K) := by
      rw [(P : Subgroup K).normalizer_eq_top]
      exact le_top
    have hcentPL : centralizerWithin (P : Subgroup K) L = ⊥ := by
      letI : IsMulCommutative P := hcyc.isMulCommutative
      apply le_bot_iff.mp
      intro x hx
      let xP : P := ⟨x, hx.1⟩
      have hfix : ∀ a : L,
          (a : K) * (xP : K) * (a : K)⁻¹ = (xP : K) := by
        intro a
        calc
          (a : K) * (xP : K) * (a : K)⁻¹ =
              (xP : K) * (a : K) * (a : K)⁻¹ := by
                rw [hx.2 (a : K) a.2]
          _ = (xP : K) := by simp
      have hxOne : xP = 1 :=
        Submission.OddOrder.BG.Section06.fixed_eq_one_of_abelian_perfect_coprime_conjugation
          hLnormP hcopPL hperfect xP hfix
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxOne)
    refine ⟨hPD, le_antisymm ?_ bot_le⟩
    exact (centralizerWithin_antitone_right
      (show L ≤ (⊤ : Subgroup K) from le_top)).trans
        (le_of_eq hcentPL)

/-- If a coprime product `A * B` is a subgroup of `E`, and `B` meets
`E'` trivially, then the part of that product lying in `E'` is contained
in `A`.  This is the quotient calculation behind `nE21` in the source. -/
private theorem inf_commutator_le_left_of_coprime_product_12_1
    {E : Type u} [Group E] [Finite E]
    {A B K : Subgroup E}
    (_hAK : A ≤ K) (_hBK : B ≤ K)
    (hcarrier : (K : Set E) = (A : Set E) * (B : Set E))
    (hcop : Nat.Coprime (Nat.card A) (Nat.card B))
    (hBder : B ⊓ _root_.commutator E = ⊥) :
    K ⊓ _root_.commutator E ≤ A := by
  classical
  let D : Subgroup E := _root_.commutator E
  letI : D.Normal := by dsimp [D]; infer_instance
  let q : E →* E ⧸ D := QuotientGroup.mk' D
  intro x hx
  obtain ⟨a, ha, b, hb, hab⟩ :=
    Set.mem_mul.mp (hcarrier ▸ hx.1)
  let aE : E := a
  let bE : E := b
  have hxEq : aE * bE = x := hab
  have hqx : q x = 1 :=
    (QuotientGroup.eq_one_iff x).mpr hx.2
  have hqab : q aE * q bE = 1 := by
    rw [← map_mul, hxEq, hqx]
  have horderA : orderOf (q aE) ∣ Nat.card A := by
    exact (orderOf_map_dvd q aE).trans
      (by simpa [aE] using A.orderOf_dvd_natCard ha)
  have hqaInv : q aE = (q bE)⁻¹ := eq_inv_of_mul_eq_one_left hqab
  have horderB : orderOf (q aE) ∣ Nat.card B := by
    rw [hqaInv, orderOf_inv]
    exact (orderOf_map_dvd q bE).trans
      (by simpa [bE] using B.orderOf_dvd_natCard hb)
  have hqaOne : q aE = 1 := orderOf_eq_one_iff.mp
    (Nat.eq_one_of_dvd_coprimes hcop horderA horderB)
  have hqbOne : q bE = 1 := by
    rw [hqaOne, one_mul] at hqab
    exact hqab
  have hbD : b ∈ D := (QuotientGroup.eq_one_iff bE).mp hqbOne
  have hbBot : b ∈ (⊥ : Subgroup E) := by
    rw [← hBder]
    exact ⟨hb, hbD⟩
  have hbOne : b = 1 := Subgroup.mem_bot.mp hbBot
  dsimp [aE, bE] at hxEq
  rw [hbOne, mul_one] at hxEq
  exact hxEq ▸ ha

/-- `BGsection12.v: sigma_compl_context`, Lemma 12.1(b)--(f). -/
theorem sigma_compl_context
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M E E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ minSimple_max_groups (G := G))
    (hCompl : sigma_complement M E E₁ E₂ E₃) :
    SigmaComplementContext E E₁ E₂ E₃ := by
  classical
  let D : Subgroup E := _root_.commutator E
  let E₁E : Subgroup E := E₁.subgroupOf E
  let E₂E : Subgroup E := E₂.subgroupOf E
  let E₃E : Subgroup E := E₃.subgroupOf E
  have hDnil : Group.IsNilpotent D := by
    simpa [D] using
      der1_sigma_compl_nil hM hCompl.E_le_M hCompl.hall_E
  letI : Group.IsNilpotent D := hDnil

  have hcop₂₁ : Nat.Coprime (Nat.card E₂E) (Nat.card E₁E) :=
    hCompl.hall_E₂.isPiNumber_card.coprime_compl
      (hCompl.hall_E₁.isPiNumber_card.mono (tau2'1 M))
  have hcop₃₁ : Nat.Coprime (Nat.card E₃E) (Nat.card E₁E) :=
    hCompl.hall_E₃.isPiNumber_card.coprime_compl
      (hCompl.hall_E₁.isPiNumber_card.mono (tau3'1 M))
  have hcop₃₂ : Nat.Coprime (Nat.card E₃E) (Nat.card E₂E) :=
    hCompl.hall_E₃.isPiNumber_card.coprime_compl
      (hCompl.hall_E₂.isPiNumber_card.mono (tau3'2 M))
  have hdis₂₁ : Disjoint E₂E E₁E :=
    Subgroup.disjoint_of_coprime_natCard hcop₂₁
  have hdis₃₁ : Disjoint E₃E E₁E :=
    Subgroup.disjoint_of_coprime_natCard hcop₃₁
  have hdis₃₂ : Disjoint E₃E E₂E :=
    Subgroup.disjoint_of_coprime_natCard hcop₃₂

  /- The tau1 factor is abelian because it is disjoint from `E'`. -/
  let j : E →* M := Subgroup.inclusion hCompl.E_le_M
  have hj : Function.Injective j := by
    dsimp [j]
    exact Subgroup.inclusion_injective hCompl.E_le_M
  have hDmap : D.map j ≤ _root_.commutator M := by
    dsimp only [D]
    calc
      (_root_.commutator E).map j = ⁅j.range, j.range⁆ :=
        map_commutator_eq E j
      _ ≤ _root_.commutator M :=
        Subgroup.commutator_mono le_top le_top
  have hDnotTau₁ : IsPiNumber (tau1Primes M)ᶜ (Nat.card D) := by
    intro p hp hpD hpTau
    have hpMap : p ∣ Nat.card (D.map j) := by
      rwa [Subgroup.card_map_of_injective hj]
    have hpMder : p ∣ Nat.card (_root_.commutator M) :=
      hpMap.trans (Subgroup.card_dvd_of_le hDmap)
    exact hpTau.2.2.2.2 hpMder
  have hcop₁D : Nat.Coprime (Nat.card E₁E) (Nat.card D) :=
    hCompl.hall_E₁.isPiNumber_card.coprime_compl hDnotTau₁
  have hdis₁D : Disjoint E₁E D :=
    Subgroup.disjoint_of_coprime_natCard hcop₁D
  have hE₁Ecomm : IsMulCommutative E₁E := by
    apply (_root_.commutator_eq_bot_iff E₁E).mp
    apply (Subgroup.map_eq_bot_iff_of_injective
      (_root_.commutator E₁E) E₁E.subtype_injective).mp
    apply le_bot_iff.mp
    rw [← disjoint_iff.mp hdis₁D]
    rw [Subgroup.map_subtype_commutator]
    apply le_inf
    · exact Subgroup.le_normalizer_iff_commutator_le_left.mp
        (show E₁E ≤ Subgroup.normalizer (E₁E : Set E) from
          Subgroup.le_normalizer)
    · calc
        ⁅E₁E, E₁E⁆ ≤ ⁅(⊤ : Subgroup E), ⊤⁆ :=
          Subgroup.commutator_mono le_top le_top
        _ = D := by
          simpa [D] using (_root_.commutator_def E).symm
  have hE₁comm : IsMulCommutative E₁ := by
    let e : E₁E ≃* E₁ :=
      Subgroup.subgroupOfEquivOfLe hCompl.E₁_le_E
    apply isMulCommutative_iff.mpr
    intro x y
    apply e.symm.injective
    simpa only [map_mul] using
      (isMulCommutative_iff.mp hE₁Ecomm (e.symm x) (e.symm y))
  have hE₁Z : IsZGroup E₁ := by
    apply (odd_isZGroup_iff_sylow_no_elementaryAbelian_rank_two
      (mFT_odd E₁)).mpr
    intro p hp P
    rintro ⟨A, hA⟩
    have hpA : p ∣ Nat.card A := by
      rw [hA.card_eq]
      exact dvd_pow_self p (by omega)
    have hpE₁ : p ∣ Nat.card E₁ :=
      hpA.trans (A.card_subgroup_dvd_card.trans
        ((P : Subgroup E₁).card_subgroup_dvd_card))
    have hpE₁E : p ∣ Nat.card E₁E := by
      rwa [natCard_subgroupOf_eq hCompl.E₁_le_E]
    have hpTau : p ∈ tau1Primes M :=
      hCompl.hall_E₁.isPiNumber_card hp hpE₁E
    let A₁ : Subgroup E₁ := A.map (P : Subgroup E₁).subtype
    let AG : Subgroup G := A₁.map E₁.subtype
    have hA₁ : IsElementaryAbelianOfRank p 2 A₁ :=
      hA.map_of_injective (P : Subgroup E₁).subtype
        (P : Subgroup E₁).subtype_injective
    have hAG : IsElementaryAbelianOfRank p 2 AG :=
      hA₁.map_of_injective E₁.subtype E₁.subtype_injective
    exact hpTau.2.2.2.1
      ⟨AG, (Subgroup.map_subtype_le A₁).trans
        (hCompl.E₁_le_E.trans hCompl.E_le_M), hAG⟩
  have hE₁cyclic : IsCyclic E₁ := by
    letI : IsMulCommutative E₁ := hE₁comm
    letI : Group.IsNilpotent E₁ := inferInstance
    letI : IsZGroup E₁ := hE₁Z
    infer_instance

  /- Every Sylow subgroup of the tau3 factor is cyclic, lies in `E'`,
  and is regular on `E`. -/
  have hSylowE₃ : ∀ (p : ℕ) (hp : p.Prime) (P : Sylow p E₃),
      IsCyclic P ∧
      (P : Subgroup E₃).map E₃.subtype ≤ D.map E.subtype ∧
      centralizerWithin
          ((P : Subgroup E₃).map E₃.subtype) E = ⊥ := by
    intro p hp P
    letI : Fact p.Prime := ⟨hp⟩
    by_cases hPbot : (P : Subgroup E₃) = ⊥
    · have hPcyc : IsCyclic P := by
        change IsCyclic (P : Subgroup E₃)
        rw [hPbot]
        infer_instance
      refine ⟨hPcyc, ?_, ?_⟩
      · rw [hPbot]
        simp
      · rw [hPbot]
        simp [centralizerWithin]
    have hpP : p ∣ Nat.card P :=
      P.isPGroup'.card_eq_or_dvd.resolve_left
        (fun hcard ↦ hPbot (Subgroup.card_eq_one.mp hcard))
    have hpE₃ : p ∣ Nat.card E₃ :=
      hpP.trans (P : Subgroup E₃).card_subgroup_dvd_card
    have hpE₃E : p ∣ Nat.card E₃E := by
      rwa [natCard_subgroupOf_eq hCompl.E₃_le_E]
    have hpTau : p ∈ tau3Primes M :=
      hCompl.hall_E₃.isPiNumber_card hp hpE₃E
    have hPcyc : IsCyclic P :=
      (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        P.isPGroup'
          (odd_natCard_subgroup (P : Subgroup E₃) (mFT_odd E₃))).mpr (by
          rintro ⟨A, hA⟩
          let A₁ : Subgroup E₃ :=
            A.map (P : Subgroup E₃).subtype
          let AG : Subgroup G := A₁.map E₃.subtype
          have hA₁ : IsElementaryAbelianOfRank p 2 A₁ :=
            hA.map_of_injective (P : Subgroup E₃).subtype
              (P : Subgroup E₃).subtype_injective
          have hAG : IsElementaryAbelianOfRank p 2 AG :=
            hA₁.map_of_injective E₃.subtype E₃.subtype_injective
          exact hpTau.2.2.2.1
            ⟨AG, (Subgroup.map_subtype_le A₁).trans
              (hCompl.E₃_le_E.trans hCompl.E_le_M), hAG⟩)
    obtain ⟨Q, hQeq⟩ :=
      exists_ambient_sylow_eq_of_sylow_hall_12_1 hp
        hCompl.E₃_le_E hCompl.hall_E₃ hpTau P
    have hQcyc : IsCyclic Q :=
      (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        Q.isPGroup'
          (odd_natCard_subgroup (Q : Subgroup E) (mFT_odd E))).mpr (by
          rintro ⟨A, hA⟩
          let A₁ : Subgroup E := A.map (Q : Subgroup E).subtype
          let AG : Subgroup G := A₁.map E.subtype
          have hA₁ : IsElementaryAbelianOfRank p 2 A₁ :=
            hA.map_of_injective (Q : Subgroup E).subtype
              (Q : Subgroup E).subtype_injective
          have hAG : IsElementaryAbelianOfRank p 2 AG :=
            hA₁.map_of_injective E.subtype E.subtype_injective
          exact hpTau.2.2.2.1
            ⟨AG, (Subgroup.map_subtype_le A₁).trans hCompl.E_le_M,
              hAG⟩)
    have hpDerE : p ∣ Nat.card D := by
      simpa [D] using
        tau3_dvd_complement_commutator_12_1 hM
          hCompl.E_le_M hCompl.hall_E hpTau
    have hQcontext :=
      cyclic_sylow_le_commutator_and_regular_12_1
        Q hQcyc hpDerE hDnil
    have hPder : (P : Subgroup E₃).map E₃.subtype ≤
        D.map E.subtype := by
      rw [← hQeq]
      exact Subgroup.map_mono hQcontext.1
    refine ⟨hPcyc, hPder, ?_⟩
    apply le_antisymm ?_ bot_le
    intro x hx
    have hxQmap : x ∈ (Q : Subgroup E).map E.subtype := by
      rw [hQeq]
      exact hx.1
    obtain ⟨xE, hxQ, rfl⟩ := hxQmap
    have hxIntrinsic : xE ∈
        centralizerWithin (Q : Subgroup E) (⊤ : Subgroup E) := by
      refine ⟨hxQ, ?_⟩
      intro y _hy
      apply Subtype.ext
      exact hx.2 (y : G) y.property
    rw [hQcontext.2] at hxIntrinsic
    exact Subgroup.mem_bot.mpr
      (congrArg Subtype.val (Subgroup.mem_bot.mp hxIntrinsic))

  have hE₃der : E₃ ≤ D.map E.subtype := by
    calc
      E₃ = (sylowSup E₃).map E₃.subtype := by
        rw [sylowSup_eq_top]
        exact E₃.range_subtype.symm.trans
          (MonoidHom.range_eq_map E₃.subtype)
      _ = ⨆ p : {p : ℕ // p.Prime},
          ((Classical.choice
            (Sylow.nonempty (p := (p : ℕ)) (G := E₃)) : Sylow p E₃) :
            Subgroup E₃).map E₃.subtype := by
        rw [sylowSup, Subgroup.map_iSup]
      _ ≤ D.map E.subtype := by
        apply iSup_le
        intro p
        exact (hSylowE₃ (p : ℕ) p.property
          (Classical.choice Sylow.nonempty)).2.1
  have hE₃ED : E₃E ≤ D := by
    apply (Subgroup.map_le_map_iff_of_injective
      E.subtype_injective).mp
    change (E₃.subgroupOf E).map E.subtype ≤ D.map E.subtype
    rw [Subgroup.map_subgroupOf_eq_of_le hCompl.E₃_le_E]
    exact hE₃der

  have hE₃normal : E₃E.Normal := by
    let E₃D : Subgroup D := E₃E.subgroupOf D
    have hHallE₃D : IsHall (tau3Primes M) E₃D := by
      constructor
      · rw [natCard_subgroupOf_eq hE₃ED]
        simpa [E₃E] using hCompl.hall_E₃.isPiNumber_card
      · have hindexPi : IsPiNumber (tau3Primes M)ᶜ E₃E.index := by
          simpa [E₃E] using hCompl.hall_E₃.isPiNumber_index
        change IsPiNumber (tau3Primes M)ᶜ (E₃E.relIndex D)
        exact hindexPi.of_dvd
          (Subgroup.relIndex_dvd_index_of_le hE₃ED)
    have hcore : E₃D = piCore (tau3Primes M) D :=
      hall_eq_piCore_of_isNilpotent_12_1 hHallE₃D
    have hchar : E₃D.Characteristic := by
      rw [hcore]
      infer_instance
    letI : E₃D.Characteristic := hchar
    rw [← Subgroup.map_subgroupOf_eq_of_le hE₃ED]
    infer_instance
  letI : E₃E.Normal := hE₃normal
  have hE₃cyclic : IsCyclic E₃ := by
    have hZ : IsZGroup E₃ :=
      ⟨fun p hp P ↦ (hSylowE₃ p hp P).1⟩
    let E₃D : Subgroup D := E₃E.subgroupOf D
    let e₃D : E₃D ≃* E₃E :=
      Subgroup.subgroupOfEquivOfLe hE₃ED
    let e₃E : E₃E ≃* E₃ :=
      Subgroup.subgroupOfEquivOfLe hCompl.E₃_le_E
    let e₃ : E₃D ≃* E₃ := e₃D.trans e₃E
    have hnil : Group.IsNilpotent E₃ :=
      Group.nilpotent_of_mulEquiv e₃
    letI : Group.IsNilpotent E₃ := hnil
    letI : IsZGroup E₃ := hZ
    infer_instance

  have hcentE₃ : centralizerWithin E₃ E = ⊥ := by
    by_contra hne
    have hcard : Nat.card (centralizerWithin E₃ E) ≠ 1 :=
      fun hc ↦ hne (Subgroup.card_eq_one.mp hc)
    obtain ⟨p, hp, hpC⟩ := Nat.exists_prime_and_dvd hcard
    letI : Fact p.Prime := ⟨hp⟩
    obtain ⟨y, hyorder⟩ :=
      exists_prime_orderOf_dvd_card'
        (G := centralizerWithin E₃ E) p hpC
    have hyE₃ : (y : G) ∈ E₃ :=
      centralizerWithin_le_left E₃ E y.property
    let y₃ : E₃ := ⟨(y : G), hyE₃⟩
    have hy₃order : orderOf y₃ = p := by
      calc
        orderOf y₃ = orderOf (y : G) :=
          (orderOf_injective E₃.subtype E₃.subtype_injective y₃).symm
        _ = orderOf y :=
          orderOf_injective
            (centralizerWithin E₃ E).subtype
            (centralizerWithin E₃ E).subtype_injective y
        _ = p := hyorder
    let X : Subgroup E₃ := Subgroup.zpowers y₃
    have hXcard : Nat.card X = p := by
      dsimp only [X]
      rw [Nat.card_zpowers, hy₃order]
    have hXp : IsPGroup p X :=
      IsPGroup.of_card (n := 1) (by simpa using hXcard)
    obtain ⟨P, hXP⟩ := hXp.exists_le_sylow
    have hyP : (y : G) ∈
        (P : Subgroup E₃).map E₃.subtype := by
      exact Subgroup.mem_map_of_mem E₃.subtype
        (hXP (Subgroup.mem_zpowers y₃))
    have hyReg : (y : G) ∈ centralizerWithin
        ((P : Subgroup E₃).map E₃.subtype) E :=
      ⟨hyP, y.property.2⟩
    rw [(hSylowE₃ p hp P).2.2] at hyReg
    have hyOneG : (y : G) = 1 := Subgroup.mem_bot.mp hyReg
    have hyOne : y = 1 :=
      (centralizerWithin E₃ E).subtype_injective hyOneG
    have : p = 1 := by
      rw [← hyorder, orderOf_eq_one_iff]
      exact hyOne
    exact hp.ne_one this

  /- The supplied subgroup carrier `E₂ * E₁`, together with
  `E₁ ∩ E' = 1`, makes `E₂` normal in `E₂ ⊔ E₁`. -/
  obtain ⟨K, hKcarrier⟩ := hCompl.product_is_group
  have hE₂K : E₂ ≤ K := by
    intro x hx
    change x ∈ (K : Set G)
    have hxProd : x ∈ (E₂ : Set G) * (E₁ : Set G) := Set.mem_mul.mpr
      ⟨x, hx, 1, E₁.one_mem, mul_one x⟩
    exact hKcarrier.symm ▸ hxProd
  have hE₁K : E₁ ≤ K := by
    intro x hx
    change x ∈ (K : Set G)
    have hxProd : x ∈ (E₂ : Set G) * (E₁ : Set G) := Set.mem_mul.mpr
      ⟨1, E₂.one_mem, x, hx, one_mul x⟩
    exact hKcarrier.symm ▸ hxProd
  have hKE : K ≤ E := by
    intro x hx
    have hxK : x ∈ (K : Set G) := hx
    have hxProd : x ∈ (E₂ : Set G) * (E₁ : Set G) :=
      hKcarrier ▸ hxK
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hxProd
    exact E.mul_mem (hCompl.E₂_le_E ha) (hCompl.E₁_le_E hb)
  let KE : Subgroup E := K.subgroupOf E
  have hE₂KE : E₂E ≤ KE := by
    intro x hx
    exact hE₂K hx
  have hE₁KE : E₁E ≤ KE := by
    intro x hx
    exact hE₁K hx
  have hKEcarrier : (KE : Set E) =
      (E₂E : Set E) * (E₁E : Set E) := by
    ext x
    constructor
    · intro hx
      have hxK : (x : G) ∈ (K : Set G) := hx
      have hxProd : (x : G) ∈ (E₂ : Set G) * (E₁ : Set G) :=
        hKcarrier ▸ hxK
      obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hxProd
      refine Set.mem_mul.mpr
        ⟨(⟨a, hCompl.E₂_le_E ha⟩ : E), ha,
          (⟨b, hCompl.E₁_le_E hb⟩ : E), hb, ?_⟩
      apply Subtype.ext
      exact hab
    · rintro ⟨a, ha, b, hb, hab⟩
      have hxProd : (x : G) ∈ (E₂ : Set G) * (E₁ : Set G) := by
        refine Set.mem_mul.mpr
          ⟨(a : G), ha, (b : G), hb, ?_⟩
        exact congrArg Subtype.val hab
      have hxK : (x : G) ∈ (K : Set G) := hKcarrier.symm ▸ hxProd
      exact hxK
  have hKEinfD : KE ⊓ D ≤ E₂E :=
    inf_commutator_le_left_of_coprime_product_12_1
      hE₂KE hE₁KE hKEcarrier hcop₂₁
      (disjoint_iff.mp hdis₁D)
  have hcomm₂₁ : ⁅E₂E, E₁E⁆ ≤ E₂E := by
    apply (le_inf ?_ ?_).trans hKEinfD
    · exact (Subgroup.commutator_mono hE₂KE hE₁KE).trans
        (Subgroup.le_normalizer_iff_commutator_le_left.mp
          (show KE ≤ Subgroup.normalizer (KE : Set E) from
            Subgroup.le_normalizer))
    · calc
        ⁅E₂E, E₁E⁆ ≤ ⁅(⊤ : Subgroup E), ⊤⁆ :=
          Subgroup.commutator_mono le_top le_top
        _ = D := by
          simpa [D] using (_root_.commutator_def E).symm
  have hE₁normE₂ : E₁E ≤
      Subgroup.normalizer (E₂E : Set E) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hcomm₂₁
  have hcomm₂₁G : ⁅E₂, E₁⁆ ≤ E₂ := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hCompl.E₂_le_E,
      ← Subgroup.map_subgroupOf_eq_of_le hCompl.E₁_le_E,
      ← Subgroup.map_commutator]
    exact Subgroup.map_mono hcomm₂₁
  have hE₁normE₂G : E₁ ≤
      Subgroup.normalizer (E₂ : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hcomm₂₁G

  let H₂₁ : Subgroup E := E₂E ⊔ E₁E
  have hH₂₁card : Nat.card H₂₁ =
      Nat.card E₂E * Nat.card E₁E := by
    have hcard :=
      natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        hdis₂₁.symm hE₁normE₂
    simpa [H₂₁, sup_comm, Nat.mul_comm] using hcard
  have hcop₃H₂₁ : Nat.Coprime (Nat.card E₃E) (Nat.card H₂₁) := by
    rw [hH₂₁card]
    exact hcop₃₂.mul_right hcop₃₁
  have hdis₃H₂₁ : Disjoint E₃E H₂₁ :=
    Subgroup.disjoint_of_coprime_natCard hcop₃H₂₁

  have hsup₃₂₁ : E₃E ⊔ H₂₁ = ⊤ := by
    apply Subgroup.index_eq_one.mp
    by_cases hindex : (E₃E ⊔ H₂₁).index = 1
    · exact hindex
    · exfalso
      obtain ⟨p, hp, hpIndex⟩ :=
        @Nat.exists_prime_and_dvd (E₃E ⊔ H₂₁).index hindex
      have hpE : p ∣ Nat.card E :=
        hpIndex.trans (E₃E ⊔ H₂₁).index_dvd_card
      have hpSupport : p ∈ primeSupport (Nat.card E) := ⟨hp, hpE⟩
      have hpClass := primeSupport_sigma_complement_subset_tau_12_1
        hM hCompl.E_le_M hCompl.hall_E hpSupport
      have hpClass' :
          (p ∈ tau1Primes M ∨ p ∈ tau2Primes M) ∨
            p ∈ tau3Primes M := by
        simpa only [Set.mem_union] using hpClass
      cases hpClass' with
      | inl hpClass₁₂ =>
          cases hpClass₁₂ with
          | inl hpTau₁ =>
              have hpIndex₁ : p ∣ E₁E.index :=
                hpIndex.trans (Subgroup.index_dvd_of_le
                  ((show E₁E ≤ H₂₁ from le_sup_right).trans le_sup_right))
              exact (hCompl.hall_E₁.isPiNumber_index hp hpIndex₁) hpTau₁
          | inr hpTau₂ =>
              have hpIndex₂ : p ∣ E₂E.index :=
                hpIndex.trans (Subgroup.index_dvd_of_le
                  ((show E₂E ≤ H₂₁ from le_sup_left).trans le_sup_right))
              exact (hCompl.hall_E₂.isPiNumber_index hp hpIndex₂) hpTau₂
      | inr hpTau₃ =>
          have hpIndex₃ : p ∣ E₃E.index :=
            hpIndex.trans (Subgroup.index_dvd_of_le le_sup_left)
          exact (hCompl.hall_E₃.isPiNumber_index hp hpIndex₃) hpTau₃

  have hcomp₂₁ :
      (E₂.subgroupOf (E₂ ⊔ E₁)).IsComplement'
        (E₁.subgroupOf (E₂ ⊔ E₁)) := by
    let E₂H : Subgroup ↥(E₂ ⊔ E₁) := E₂.subgroupOf (E₂ ⊔ E₁)
    let E₁H : Subgroup ↥(E₂ ⊔ E₁) := E₁.subgroupOf (E₂ ⊔ E₁)
    have hnormal : E₂H.Normal := by
      dsimp [E₂H]
      rw [sup_comm E₂ E₁]
      exact Subgroup.normal_subgroupOf_sup_of_le_normalizer hE₁normE₂G
    letI : E₂H.Normal := hnormal
    have hdis : Disjoint E₂H E₁H := by
      rw [disjoint_iff]
      apply le_antisymm _ bot_le
      intro x hx
      apply Subgroup.mem_bot.mpr
      apply Subtype.ext
      let xE : E :=
        ⟨(x : G), hCompl.E₂_le_E hx.1⟩
      have hxBotE : xE ∈ (⊥ : Subgroup E) := by
        rw [← disjoint_iff.mp hdis₂₁]
        exact ⟨hx.1, hx.2⟩
      have hxOneE : xE = 1 := Subgroup.mem_bot.mp hxBotE
      have hxOneG : (xE : G) = (1 : G) :=
        congrArg (fun y : E ↦ (y : G)) hxOneE
      exact hxOneG
    have hsup : E₂H ⊔ E₁H = ⊤ := by
      rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
      exact Subgroup.subgroupOf_self (E₂ ⊔ E₁)
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis
    rw [← Subgroup.normal_mul E₂H E₁H, hsup]
    rfl

  have hcomp₃₂₁ : E₃E.IsComplement' H₂₁ := by
    letI : E₃E.Normal := hE₃normal
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdis₃H₂₁
    rw [← Subgroup.normal_mul E₃E H₂₁, hsup₃₂₁]
    rfl

  let N₃₂ : Subgroup E := E₃E ⊔ E₂E
  have hE₁normE₃ : E₁E ≤
      Subgroup.normalizer (E₃E : Set E) := by
    rw [E₃E.normalizer_eq_top]
    exact le_top
  have hE₁normN₃₂ : E₁E ≤
      Subgroup.normalizer (N₃₂ : Set E) := by
    dsimp only [N₃₂]
    exact (le_inf hE₁normE₃ hE₁normE₂).trans
      (Subgroup.normalizer_inf_normalizer_le_normalizer_sup E₃E E₂E)
  have hsup₃₂_₁ : N₃₂ ⊔ E₁E = ⊤ := by
    simpa [N₃₂, H₂₁, sup_assoc] using hsup₃₂₁
  have hN₃₂normal : N₃₂.Normal := by
    rw [← Subgroup.normalizer_eq_top_iff]
    apply top_unique
    rw [← hsup₃₂_₁]
    exact sup_le Subgroup.le_normalizer hE₁normN₃₂
  have hN₃₂card : Nat.card N₃₂ =
      Nat.card E₃E * Nat.card E₂E := by
    have hE₂normE₃ : E₂E ≤
        Subgroup.normalizer (E₃E : Set E) := by
      rw [E₃E.normalizer_eq_top]
      exact le_top
    have hcard :=
      natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        hdis₃₂.symm hE₂normE₃
    simpa [N₃₂, sup_comm, Nat.mul_comm] using hcard
  have hcopN₃₂₁ : Nat.Coprime (Nat.card N₃₂) (Nat.card E₁E) := by
    rw [hN₃₂card]
    exact hcop₃₁.mul_left hcop₂₁
  have hdisN₃₂₁ : Disjoint N₃₂ E₁E :=
    Subgroup.disjoint_of_coprime_natCard hcopN₃₂₁
  have hcomp₃₂_₁ : N₃₂.IsComplement' E₁E := by
    letI : N₃₂.Normal := hN₃₂normal
    apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ hdisN₃₂₁
    rw [← Subgroup.normal_mul N₃₂ E₁E, hsup₃₂_₁]
    rfl

  have hE₂botE₁ne : E₂ = ⊥ → E₁ ≠ ⊥ := by
    intro hE₂bot hE₁bot
    have hE₂Ebot : E₂E = ⊥ := by
      dsimp [E₂E]
      rw [hE₂bot]
      simp
    have hE₁Ebot : E₁E = ⊥ := by
      dsimp [E₁E]
      rw [hE₁bot]
      simp
    have hE₃Etop : E₃E = ⊤ := by
      simpa [H₂₁, hE₂Ebot, hE₁Ebot] using hsup₃₂₁
    have hDtop : D = ⊤ := by
      apply top_unique
      rw [← hE₃Etop]
      exact hE₃ED
    have hEperfect : _root_.commutator E = ⊤ := by
      simpa [D] using hDtop
    let S : Subgroup M := (sigmaCore M).subgroupOf M
    let T : Subgroup M := E.subgroupOf M
    have hSder : S ≤ _root_.commutator M := by
      apply (Subgroup.map_le_map_iff_of_injective
        M.subtype_injective).mp
      rw [show S.map M.subtype = sigmaCore M by
        exact Subgroup.map_subgroupOf_eq_of_le (sigmaCore_le M)]
      exact Msigma_der1 hM
    let jEM : E →* M := Subgroup.inclusion hCompl.E_le_M
    have hmapDer : (_root_.commutator E).map jEM ≤
        _root_.commutator M := by
      calc
        (_root_.commutator E).map jEM = ⁅jEM.range, jEM.range⁆ :=
          map_commutator_eq E jEM
        _ ≤ _root_.commutator M :=
          Subgroup.commutator_mono le_top le_top
    have hTder : T ≤ _root_.commutator M := by
      intro x hx
      let xE : E := ⟨(x : G), hx⟩
      have hxEDer : xE ∈ _root_.commutator E := by
        rw [hEperfect]
        trivial
      have hjx : jEM xE = x := by
        apply Subtype.ext
        rfl
      rw [← hjx]
      exact hmapDer (Subgroup.mem_map_of_mem jEM hxEDer)
    have hSTcomp : S.IsComplement' T := by
      simpa [S, T] using
        (sdprod_sigma hM hCompl.E_le_M hCompl.hall_E).2.2.2
    have hMperfect : _root_.commutator M = ⊤ := by
      apply top_unique
      rw [← hSTcomp.sup_eq_top]
      exact sup_le hSder hTder
    letI : IsSolvable M := mmax_sol hM
    letI : Nontrivial M :=
      (Subgroup.nontrivial_iff_ne_bot M).mpr (mmax_neq1 hM)
    exact (IsSolvable.commutator_lt_top_of_nontrivial M).ne hMperfect

  have hH₂₁sub : (E₂ ⊔ E₁).subgroupOf E = H₂₁ := by
    dsimp [H₂₁, E₂E, E₁E]
    exact Subgroup.subgroupOf_sup hCompl.E₂_le_E hCompl.E₁_le_E
  have hN₃₂sub : (E₃ ⊔ E₂).subgroupOf E = N₃₂ := by
    dsimp [N₃₂, E₃E, E₂E]
    exact Subgroup.subgroupOf_sup hCompl.E₃_le_E hCompl.E₂_le_E

  exact
    { E₃_le_commutator := by simpa [D] using hE₃der
      E₃_normal := by simpa [E₃E] using hE₃normal
      E₂_eq_bot_imp_E₁_ne_bot := hE₂botE₁ne
      E₁_cyclic := hE₁cyclic
      E₃_cyclic := hE₃cyclic
      E₂₁_sdprod :=
        ⟨le_sup_left, le_sup_right,
          (by
            rw [sup_comm E₂ E₁]
            exact Subgroup.normal_subgroupOf_sup_of_le_normalizer
              hE₁normE₂G),
          hcomp₂₁⟩
      E₃_E₂₁_sdprod := by
        refine ⟨hCompl.E₃_le_E,
          sup_le hCompl.E₂_le_E hCompl.E₁_le_E,
          ?_, ?_⟩
        · simpa [E₃E] using hE₃normal
        · rw [hH₂₁sub]
          simpa [E₃E] using hcomp₃₂₁
      E₃₂_E₁_sdprod := by
        refine ⟨sup_le hCompl.E₃_le_E hCompl.E₂_le_E,
          hCompl.E₁_le_E, ?_, ?_⟩
        · rw [hN₃₂sub]
          exact hN₃₂normal
        · rw [hN₃₂sub]
          simpa [E₁E] using hcomp₃₂_₁
      centralizerWithin_eq_bot := hcentE₃ }

/-- `BGsection12.v: prime_class_mmax_norm`, Lemma 12.2(a).

If a `p`-subgroup has its full ambient normalizer in a maximal subgroup,
then `p` is either a sigma prime or a `tau2` prime of that subgroup. -/
theorem prime_class_mmax_norm
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hXp : IsPGroup p X)
    (hNXM : Subgroup.normalizer (X : Set G) ≤ M) :
    p ∈ sigmaPrimes M ∨ p ∈ tau2Primes M := by
  by_cases hpSigma : p ∈ sigmaPrimes M
  · exact Or.inl hpSigma
  · have hRank : HasElementaryAbelianPRankTwo p M :=
      sigma'_norm_mmax_rank2 hM hpSigma hXp hNXM
    exact Or.inr ⟨Fact.out, hpSigma, hRank.1, hRank.2⟩

/-- `BGsection12.v: mmax_norm_notJ`, Lemma 12.2(b).

The conclusion is the direct Lean form of non-membership in the conjugacy
orbit of `M`. -/
theorem mmax_norm_notJ
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M Mstar X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hM : M ∈ minSimple_max_groups (G := G))
    (hMstar : Mstar ∈ minSimple_max_groups (G := G))
    (hXp : IsPGroup p X)
    (hXM : X ≤ M)
    (hNXMstar : Subgroup.normalizer (X : Set G) ≤ Mstar)
    (hpClass :
      (p ∈ sigmaPrimes M ∧ M ≠ Mstar) ∨
        p ∈ tau1Primes M ∨ p ∈ tau3Primes M) :
    ∀ g : G, Mstar ≠ M.map (MulAut.conj g).toMonoidHom := by
  intro g hMstarMap
  by_cases hpSigma : p ∈ sigmaPrimes M
  · have hMne : M ≠ Mstar := by
      rcases hpClass with h | h | h
      · exact h.2
      · exact (h.2.1 hpSigma).elim
      · exact (h.2.1 hpSigma).elim
    have hXMstar : X ≤ Mstar :=
      Subgroup.le_normalizer.trans hNXMstar
    have htrans := (sigma_group_trans hM hpSigma hXp).2.1
    obtain ⟨c, hcX, hmap⟩ := htrans
      ⟨⟨g, hMstarMap⟩, hXMstar⟩
      ⟨⟨1, (map_conj_one_12_1 M).symm⟩, hXM⟩
    have hcMstar : c ∈ Mstar :=
      hNXMstar (Subgroup.centralizer_le_normalizer (X : Set G) hcX)
    have hfix :
        Mstar.map (MulAut.conj c).toMonoidHom = Mstar :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (Subgroup.le_normalizer hcMstar)
    exact hMne (hmap.trans hfix)
  · rcases prime_class_mmax_norm hMstar hXp hNXMstar with
      hpMstarSigma | hpMstarTau2
    · have hpMSigma : p ∈ sigmaPrimes M := by
        rw [hMstarMap, sigmaPrimes_conj] at hpMstarSigma
        exact hpMstarSigma
      exact hpSigma hpMSigma
    · have hpMTau2 : p ∈ tau2Primes M := by
        rw [hMstarMap, tau2J] at hpMstarTau2
        exact hpMstarTau2
      rcases hpClass with h | h | h
      · exact hpSigma h.1
      · exact (tau2'1 M h) hpMTau2
      · exact (tau3'2 M hpMTau2) h

/-- `BGsection12.v: nonuniq_p2Elem_cent_sigma`, Lemma 12.3.

The MathComp memberships in the two elementary-abelian families are
expanded into containments and fixed-rank hypotheses. -/
theorem nonuniq_p2Elem_cent_sigma
    {G : Type u} [Group G] [Finite G] [IsMinSimpleOddGroup G]
    {M Mstar A A₀ : Subgroup G} {p : ℕ}
    (hp : p.Prime)
    (hM : M ∈ minSimple_max_groups (G := G))
    (hMstar : Mstar ∈ minSimple_max_groups (G := G))
    (hMstar_ne_M : Mstar ≠ M)
    (hAM : A ≤ M)
    (hA : IsElementaryAbelianOfRank p 2 A)
    (hA₀A : A₀ ≤ A)
    (hA₀ : IsElementaryAbelianOfRank p 1 A₀)
    (hNA₀Mstar : Subgroup.normalizer (A₀ : Set G) ≤ Mstar) :
    (p ∉ sigmaPrimes M →
      A ≤ Subgroup.centralizer
        ((sigmaCore M ⊓ Mstar : Subgroup G) : Set G)) ∧
    (p ∉ alphaPrimes M →
      A ≤ Subgroup.centralizer
        ((alphaCore M ⊓ Mstar : Subgroup G) : Set G)) := by
  classical
  letI : Fact p.Prime := ⟨hp⟩
  have hAcentA₀ : A ≤ Subgroup.centralizer (A₀ : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro a₀ ha₀
    letI : IsMulCommutative A := hA.commutative
    exact congrArg Subtype.val
      (mul_comm (⟨a₀, hA₀A ha₀⟩ : A) (⟨a, ha⟩ : A))
  have hAMstar : A ≤ Mstar :=
    hAcentA₀.trans
      ((Subgroup.centralizer_le_normalizer (A₀ : Set G)).trans
        hNA₀Mstar)
  have hSstarMstar : sigmaCore Mstar ≤ Mstar := sigmaCore_le Mstar
  have hSstarNormal :
      ((sigmaCore Mstar).subgroupOf Mstar).Normal :=
    sigmaCore_normal Mstar
  have hA_le_sigmaCore_star
      (hpStar : p ∈ sigmaPrimes Mstar) :
      A ≤ sigmaCore Mstar := by
    apply le_normal_isHall_of_isPiNumber_12
      hSstarNormal (Msigma_Hall hMstar) hAMstar
    exact hA.isPGroup.isPiNumber_natCard hpStar
  have hExceptionalStar
      (hpStar : p ∉ sigmaPrimes Mstar) :
      exceptional_FTmaximal p Mstar A₀ A :=
    { prime := hp
      sigma_compl := hpStar
      A_le := hAMstar
      A_rank_two := hA
      A₀_le := hA₀A
      A₀_rank_one := hA₀
      normalizer_A₀_le := hNA₀Mstar }
  have hSylowStar :
      ∃ P : Sylow p Mstar, A ≤ ambientSylow Mstar P := by
    let AMstar : Subgroup Mstar := A.subgroupOf Mstar
    let eA : AMstar ≃* A := Subgroup.subgroupOfEquivOfLe hAMstar
    have hAMstarp : IsPGroup p AMstar :=
      hA.isPGroup.of_equiv eA.symm
    obtain ⟨P, hAP⟩ := hAMstarp.exists_le_sylow
    refine ⟨P, ?_⟩
    rw [← Subgroup.map_subgroupOf_eq_of_le hAMstar]
    exact Subgroup.map_mono hAP
  have hSstar_sup_A_normal :
      ((sigmaCore Mstar ⊔ A).subgroupOf Mstar).Normal := by
    by_cases hpStar : p ∈ sigmaPrimes Mstar
    · rw [sup_eq_left.mpr (hA_le_sigmaCore_star hpStar)]
      exact hSstarNormal
    · obtain ⟨P, hAP⟩ := hSylowStar
      exact exceptional_mul_sigma_normal hMstar
        (hExceptionalStar hpStar) P hAP
  have hMnormAlpha :
      M ≤ Subgroup.normalizer (alphaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (alphaCore_le M)).mp
      (alphaCore_normal M)
  have hMnormSigma :
      M ≤ Subgroup.normalizer (sigmaCore M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (sigmaCore_le M)).mp
      (sigmaCore_normal M)
  have hAstarNorm : A ≤ Subgroup.normalizer (Mstar : Set G) :=
    hAMstar.trans Subgroup.le_normalizer
  by_cases hpM : p ∈ sigmaPrimes M
  · refine ⟨fun hpM' ↦ (hpM' hpM).elim, ?_⟩
    intro hpAlpha
    have hnotConj :
        ∀ g : G, Mstar ≠ M.map (MulAut.conj g).toMonoidHom :=
      mmax_norm_notJ hM hMstar hA₀.isPGroup
        (hA₀A.trans hAM) hNA₀Mstar
        (Or.inl ⟨hpM, hMstar_ne_M.symm⟩)
    have hdis : alphaCore M ⊓ sigmaCore Mstar = ⊥ :=
      alphaCore_inf_sigmaCore_eq_bot hM hMstar hnotConj
    let K : Subgroup G := alphaCore M ⊓ Mstar
    have hKp' : IsPPrimeSubgroup p K := by
      apply hp.coprime_iff_not_dvd.mpr
      intro hpK
      apply hpAlpha
      exact alphaCore_isPiNumber M hp
        (hpK.trans (Subgroup.card_dvd_of_le inf_le_left))
    have hAnormK : A ≤ Subgroup.normalizer (K : Set G) := by
      dsimp [K]
      exact (le_inf (hAM.trans hMnormAlpha) hAstarNorm).trans
        Subgroup.inf_normalizer_le_normalizer_inf
    have hcommLe : ⁅K, A⁆ ≤ K ⊓ sigmaCore Mstar :=
      commutator_le_inf_of_normal_sup_of_coprime
        (H := Mstar) (S := sigmaCore Mstar)
        (A := A) (B := A) (K := K)
        hSstarMstar hAMstar hAMstar le_rfl inf_le_right
        hSstarNormal hSstar_sup_A_normal hAnormK hA.isPGroup hKp'
    have hcommBot : ⁅K, A⁆ = ⊥ := by
      apply le_antisymm ?_ bot_le
      exact hcommLe.trans <| by
        calc
          K ⊓ sigmaCore Mstar ≤
              alphaCore M ⊓ sigmaCore Mstar :=
            inf_le_inf inf_le_left le_rfl
          _ = ⊥ := hdis
    apply Subgroup.le_centralizer_iff.mp
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
  · have hSigmaCent :
        A ≤ Subgroup.centralizer
          ((sigmaCore M ⊓ Mstar : Subgroup G) : Set G) := by
      let K : Subgroup G := sigmaCore M ⊓ Mstar
      have hKp' : IsPPrimeSubgroup p K := by
        apply hp.coprime_iff_not_dvd.mpr
        intro hpK
        apply hpM
        exact sigmaCore_isPiNumber M hp
          (hpK.trans (Subgroup.card_dvd_of_le inf_le_left))
      have hAnormK : A ≤ Subgroup.normalizer (K : Set G) := by
        dsimp [K]
        exact (le_inf (hAM.trans hMnormSigma) hAstarNorm).trans
          Subgroup.inf_normalizer_le_normalizer_inf
      by_cases hpStar : p ∈ sigmaPrimes Mstar
      · have hAstarSigma : A ≤ sigmaCore Mstar :=
          hA_le_sigmaCore_star hpStar
        let AlphaH : Subgroup Mstar :=
          (alphaCore Mstar).subgroupOf Mstar
        have hAlphaHnormal : AlphaH.Normal := by
          simpa [AlphaH] using alphaCore_normal Mstar
        letI : AlphaH.Normal := hAlphaHnormal
        let Q := Mstar ⧸ AlphaH
        let q : Mstar →* Q := QuotientGroup.mk' AlphaH
        let SigmaH : Subgroup Mstar :=
          (sigmaCore Mstar).subgroupOf Mstar
        have hSigmaHnormal : SigmaH.Normal := by
          simpa [SigmaH] using hSstarNormal
        let SigmaQ : Subgroup Q := SigmaH.map q
        have hSigmaQnormal : SigmaQ.Normal := by
          dsimp [SigmaQ]
          exact Subgroup.Normal.map hSigmaHnormal q
            (QuotientGroup.mk'_surjective AlphaH)
        letI : SigmaQ.Normal := hSigmaQnormal
        have hSigmaHder : SigmaH ≤ _root_.commutator Mstar := by
          have hmapped :
              SigmaH.map Mstar.subtype ≤
                (_root_.commutator Mstar).map Mstar.subtype := by
            rw [show SigmaH.map Mstar.subtype = sigmaCore Mstar by
              exact Subgroup.map_subgroupOf_eq_of_le
                (sigmaCore_le Mstar)]
            exact Msigma_der1 hMstar
          exact (Subgroup.map_le_map_iff_of_injective
            Mstar.subtype_injective).mp hmapped
        have hSigmaQder : SigmaQ ≤ _root_.commutator Q := by
          dsimp [SigmaQ]
          calc
            SigmaH.map q ≤
                (_root_.commutator Mstar).map q :=
              Subgroup.map_mono hSigmaHder
            _ = _root_.commutator Q := by
              rw [map_commutator_eq,
                MonoidHom.range_eq_top.mpr
                  (QuotientGroup.mk'_surjective AlphaH)]
              exact (_root_.commutator_def Q).symm
        have hSigmaQnil : Group.IsNilpotent SigmaQ := by
          letI : Group.IsNilpotent (_root_.commutator Q) := by
            simpa [Q, AlphaH] using Malpha_quo_nil hMstar
          letI : Group.IsNilpotent
              (SigmaQ.subgroupOf (_root_.commutator Q)) := inferInstance
          let e : SigmaQ.subgroupOf (_root_.commutator Q) ≃* SigmaQ :=
            Subgroup.subgroupOfEquivOfLe hSigmaQder
          exact Group.nilpotent_of_mulEquiv e
        letI : Group.IsNilpotent SigmaQ := hSigmaQnil
        let R : Subgroup Q := (pCore p SigmaQ).map SigmaQ.subtype
        have hRnormal : R.Normal := by
          dsimp [R]
          infer_instance
        have hRp : IsPGroup p R := by
          dsimp [R]
          exact pCore_isPGroup.map SigmaQ.subtype
        let UH : Subgroup Mstar := R.comap q
        have hUHnormal : UH.Normal :=
          Subgroup.Normal.comap hRnormal q
        let U : Subgroup G := UH.map Mstar.subtype
        have hUMstar : U ≤ Mstar := Subgroup.map_subtype_le UH
        have hUsubgroupOf : U.subgroupOf Mstar = UH := by
          change (UH.map Mstar.subtype).comap Mstar.subtype = UH
          exact Subgroup.comap_map_eq_self_of_injective
            Mstar.subtype_injective UH
        have hUnormal : (U.subgroupOf Mstar).Normal := by
          rw [hUsubgroupOf]
          exact hUHnormal
        let Astar : Subgroup Mstar := A.subgroupOf Mstar
        have hAstarP : IsPGroup p Astar := by
          let eA : Astar ≃* A := Subgroup.subgroupOfEquivOfLe hAMstar
          exact hA.isPGroup.of_equiv eA.symm
        have hAstarSigmaH : Astar ≤ SigmaH :=
          Subgroup.subgroupOf_mono Mstar hAstarSigma
        let AQ : Subgroup Q := Astar.map q
        have hAQp : IsPGroup p AQ := hAstarP.map q
        have hAQleSigmaQ : AQ ≤ SigmaQ :=
          Subgroup.map_mono hAstarSigmaH
        let AQS : Subgroup SigmaQ := AQ.subgroupOf SigmaQ
        have hAQSp : IsPGroup p AQS := by
          let eAQ : AQS ≃* AQ :=
            Subgroup.subgroupOfEquivOfLe hAQleSigmaQ
          exact hAQp.of_equiv eAQ.symm
        have hAQleR : AQ ≤ R := by
          calc
            AQ = AQS.map SigmaQ.subtype :=
              (Subgroup.map_subgroupOf_eq_of_le hAQleSigmaQ).symm
            _ ≤ (pCore p SigmaQ).map SigmaQ.subtype :=
              Subgroup.map_mono hAQSp.le_pCore_of_isNilpotent
            _ = R := rfl
        have hAU : A ≤ U := by
          intro a ha
          let aM : Mstar := ⟨a, hAMstar ha⟩
          have hqa : q aM ∈ AQ :=
            Subgroup.mem_map_of_mem q ha
          have haUH : aM ∈ UH := hAQleR hqa
          exact Subgroup.mem_map_of_mem Mstar.subtype haUH
        have hfactorU : IsPGroup p
            ((U.subgroupOf Mstar).map
              (QuotientGroup.mk'
                ((alphaCore Mstar).subgroupOf Mstar))) := by
          rw [hUsubgroupOf]
          change IsPGroup p (UH.map q)
          rw [show UH.map q = R by
            exact Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective AlphaH) R]
          exact hRp
        have hnotConj :
            ∀ g : G, M ≠
              Mstar.map (MulAut.conj g).toMonoidHom := by
          intro g hEq
          apply hpM
          rw [hEq, sigmaPrimes_conj]
          exact hpStar
        have hdis : alphaCore Mstar ⊓ sigmaCore M = ⊥ :=
          alphaCore_inf_sigmaCore_eq_bot hMstar hM hnotConj
        letI : ((alphaCore Mstar).subgroupOf Mstar).Normal :=
          alphaCore_normal Mstar
        have hcommLe : ⁅K, A⁆ ≤ K ⊓ alphaCore Mstar :=
          commutator_le_inf_of_normal_factor_of_coprime
            (H := Mstar) (S := alphaCore Mstar)
            (A := A) (K := K) (U := U)
            (alphaCore_le Mstar) hAMstar inf_le_right hUMstar hAU
            hUnormal hAnormK hfactorU hKp'
        have hcommBot : ⁅K, A⁆ = ⊥ := by
          apply le_antisymm ?_ bot_le
          exact hcommLe.trans <| by
            calc
              K ⊓ alphaCore Mstar ≤
                  sigmaCore M ⊓ alphaCore Mstar :=
                inf_le_inf inf_le_left le_rfl
              _ = ⊥ := by simpa only [inf_comm] using hdis
        apply Subgroup.le_centralizer_iff.mp
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
      · have hcommLe : ⁅K, A⁆ ≤ K ⊓ sigmaCore Mstar :=
          commutator_le_inf_of_normal_sup_of_coprime
            (H := Mstar) (S := sigmaCore Mstar)
            (A := A) (B := A) (K := K)
            hSstarMstar hAMstar hAMstar le_rfl inf_le_right
            hSstarNormal hSstar_sup_A_normal hAnormK
            hA.isPGroup hKp'
        have hcommBot : ⁅K, A⁆ = ⊥ := by
          by_contra hne
          have hcore : sigmaCore M ⊓ sigmaCore Mstar ≠ ⊥ := by
            intro hcoreBot
            apply hne
            apply le_antisymm ?_ bot_le
            exact hcommLe.trans <| by
              calc
                K ⊓ sigmaCore Mstar ≤
                    sigmaCore M ⊓ sigmaCore Mstar :=
                  inf_le_inf inf_le_left le_rfl
                _ = ⊥ := hcoreBot
          obtain ⟨P, hAP⟩ := hSylowStar
          have hEq : M = Mstar :=
            exceptional_sigma_uniq hMstar
              (hExceptionalStar hpStar) P hAP M
              ⟨hM, hAM⟩ hcore
          exact hMstar_ne_M hEq.symm
        apply Subgroup.le_centralizer_iff.mp
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcommBot
    refine ⟨fun _ ↦ hSigmaCent, ?_⟩
    intro _
    exact hSigmaCent.trans
      (Subgroup.centralizer_le
        (inf_le_inf (alphaCore_le_sigmaCore hM) le_rfl))

end

end Submission.OddOrder.BG.Section12
