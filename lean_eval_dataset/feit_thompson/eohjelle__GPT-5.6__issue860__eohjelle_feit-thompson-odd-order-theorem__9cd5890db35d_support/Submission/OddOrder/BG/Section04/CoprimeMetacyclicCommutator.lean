import Submission.OddOrder.BG.Section04.MetacyclicOmegaOne
import Submission.OddOrder.BG.Section04.MetacyclicComplementFactors
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent
import Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement
import Submission.OddOrder.MathlibSupport.CyclicNormalizerCommutator
import Submission.OddOrder.MathlibSupport.InvariantSubgroupAction
import Submission.OddOrder.MathlibSupport.MetacyclicSubgroups
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial
import Submission.OddOrder.MathlibSupport.SubgroupConjugationFactor
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Bender--Glauberman Theorem 4.12: the coprime-action decomposition of an
odd metacyclic `p`-group.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement IsMulCommutative

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

/-- A subgroup of an odd `p`-group whose image in a quotient is disjoint
from the image of omega-one is cyclic when the quotient kernel is cyclic. -/
private theorem isCyclic_comap_of_disjoint_map_omegaOne
    {P : Type u} [Group P] [Finite P]
    (hP : IsPGroup p P) (hodd : Odd (Nat.card P))
    (S : Subgroup P) [S.Normal] (hScyclic : IsCyclic S)
    (Xbar : Subgroup (P ⧸ S))
    (hdis : Disjoint
      ((omegaOne p P).map (QuotientGroup.mk' S)) Xbar) :
    IsCyclic (Xbar.comap (QuotientGroup.mk' S)) := by
  classical
  let X : Subgroup P := Xbar.comap (QuotientGroup.mk' S)
  have hXp : IsPGroup p X := hP.to_subgroup X
  have hXodd : Odd (Nat.card X) :=
    hodd.of_dvd_nat X.card_subgroup_dvd_card
  apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
    hXp hXodd).mpr
  rintro ⟨E, hE⟩
  have hES : ∀ e : E, (((e : X) : P) : P) ∈ S := by
    intro e
    let x : P := ((e : X) : P)
    have hxpow : x ^ p = 1 := by
      exact congrArg (fun z : E ↦ (((z : X) : P) : P))
        (hE.pow_eq_one e)
    have hxOmega : x ∈ omegaOne p P :=
      mem_omegaOne_of_pow_eq_one p hxpow
    have hqOmega : QuotientGroup.mk' S x ∈
        (omegaOne p P).map (QuotientGroup.mk' S) :=
      ⟨x, hxOmega, rfl⟩
    have hqX : QuotientGroup.mk' S x ∈ Xbar := (e : X).property
    have hqBot : QuotientGroup.mk' S x ∈
        ((omegaOne p P).map (QuotientGroup.mk' S) ⊓ Xbar) :=
      ⟨hqOmega, hqX⟩
    rw [disjoint_iff.mp hdis] at hqBot
    exact (QuotientGroup.eq_one_iff x).mp (Subgroup.mem_bot.mp hqBot)
  let toS : E →* S :=
    { toFun := fun e ↦ ⟨((e : X) : P), hES e⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hEcyclic : IsCyclic E := by
    apply isCyclic_of_injective toS
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun z : S ↦ (z : P)) hxy
  exact hE.not_isCyclic Fact.out hEcyclic

/-- Perfect-action case of the commutativity assertion in Theorem 4.12. -/
private theorem isMulCommutative_of_perfect_coprime_metacyclic_action
    (R A : Subgroup G)
    (hR : IsPGroup p R) (hodd : Odd (Nat.card R))
    (hmeta : IsMetacyclic R)
    (hnorm : A ≤ Subgroup.normalizer (R : Set G))
    (hcop : (Nat.card R).Coprime (Nat.card A))
    (hperfect : ⁅R, A⁆ = R) :
    IsMulCommutative R := by
  classical
  by_contra hnotcomm
  let D : Subgroup G := ⁅R, R⁆
  have hDcyclic : IsCyclic D := by
    have hroot : IsCyclic (_root_.commutator R) :=
      commutator_isCyclic_of_isMetacyclic hmeta
    let eD := Subgroup.equivMapOfInjective
      (_root_.commutator R) R.subtype R.subtype_injective
    rw [Subgroup.map_subtype_commutator] at eD
    exact isCyclic_of_surjective eD eD.surjective
  have hDR : D ≤ R := Subgroup.commutator_le_self R
  have hAD : A ≤ Subgroup.normalizer (D : Set G) := by
    change A ≤ Subgroup.normalizer ((⁅R, R⁆ : Subgroup G) : Set G)
    rw [Subgroup.le_normalizer_iff]
    rw [← R.map_subtype_commutator]
    exact characteristic_map_subtype_invariant_under_normalizer
      R A (_root_.commutator R) hnorm
  let candidates : Set (Subgroup G) :=
    {S | IsCyclic S ∧ S ≤ R ∧
      A ≤ Subgroup.normalizer (S : Set G) ∧ D ≤ S}
  have hcandidates : candidates.Nonempty :=
    ⟨D, hDcyclic, hDR, hAD, le_rfl⟩
  obtain ⟨S, hS, hSmax⟩ := candidates.toFinite.exists_maximal hcandidates
  have hScyclic : IsCyclic S := hS.1
  have hSR : S ≤ R := hS.2.1
  have hAS : A ≤ Subgroup.normalizer (S : Set G) := hS.2.2.1
  have hDS : D ≤ S := hS.2.2.2
  have hSne : S ≠ ⊥ := by
    intro hSbot
    apply hnotcomm
    apply IsMulCommutative.of_comm
    intro x y
    apply Subtype.ext
    apply commutatorElement_eq_one_iff_mul_comm.mp
    apply Subgroup.mem_bot.mp
    rw [← hSbot]
    exact hDS (Subgroup.commutator_mem_commutator x.property y.property)
  have hRnormS : R ≤ Subgroup.normalizer (S : Set G) := by
    apply Subgroup.le_normalizer_iff_commutator_le_right.mpr
    exact (Subgroup.commutator_mono le_rfl hSR).trans hDS
  have hScenter : S.subgroupOf R ≤ Subgroup.center R := by
    have hRAcentral : ⁅R, A⁆ ≤ Subgroup.centralizer (S : Set G) :=
      commutator_le_centralizer_of_normalizes_isCyclic
        S R A hScyclic hRnormS hAS
    rw [hperfect] at hRAcentral
    intro s hs
    rw [Subgroup.mem_center_iff]
    intro r
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (hRAcentral r.property) (s : G) hs).symm

  let SR : Subgroup R := S.subgroupOf R
  have hSRnormal : SR.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hRnormS
  letI : SR.Normal := hSRnormal
  have hrootSR : _root_.commutator R ≤ SR := by
    intro x hx
    apply hDS
    change R.subtype x ∈ ⁅R, R⁆
    rw [← R.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  let Q := R ⧸ SR
  let q : R →* Q := QuotientGroup.mk' SR
  have hQcomm : IsMulCommutative Q :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr hrootSR
  letI : IsMulCommutative Q := hQcomm
  have hQp : IsPGroup p Q := hR.to_quotient SR
  have hQodd : Odd (Nat.card Q) := by
    have hdvd : Nat.card Q ∣ Nat.card R := by
      rw [show Nat.card Q = SR.index by exact SR.index_eq_card.symm]
      exact SR.index_dvd_card
    exact hodd.of_dvd_nat hdvd

  let fR : A →* MulAut R :=
    R.normalizerMonoidHom.comp (Subgroup.inclusion hnorm)
  let fQ : A →* MulAut Q :=
    subgroupConjugationFactorHom S R A hnorm hAS
  let E : Subgroup Q := omegaOne p Q
  let U : Subgroup Q := (omegaOne p R).map q
  have hUE : U ≤ E := map_omegaOne_le p q
  have hEinv : ∀ a : A, E.map (fQ a).toMonoidHom = E := by
    intro a
    exact map_omegaOne_equiv p (fQ a)
  have hUinv : ∀ a : A, U.map (fQ a).toMonoidHom = U := by
    intro a
    rw [Subgroup.map_map]
    have hcomp : (fQ a).toMonoidHom.comp q =
        q.comp (fR a).toMonoidHom := by
      ext x
      change subgroupConjugationFactorHom S R A hnorm hAS a
          (QuotientGroup.mk' (S.subgroupOf R) x) =
        QuotientGroup.mk' (S.subgroupOf R)
          (R.normalizerMonoidHom
            ((Subgroup.inclusion hnorm) a) x)
      rw [subgroupConjugationFactorHom_apply_mk]
      rfl
    rw [hcomp, ← Subgroup.map_map, map_omegaOne_equiv]
  have hEpow : ∀ x : E, x ^ p = 1 := by
    intro x
    apply Subtype.ext
    exact omegaOne_pow_eq_one_of_mul_closed p
      (fun a b ha hb ↦ by rw [mul_pow, ha, hb, one_mul]) x.property
  have hpR : p ∣ Nat.card R := hR.card_eq_or_dvd.resolve_left (by
    intro hcard
    letI : Subsingleton R := (Nat.card_eq_one_iff_unique.mp hcard).1
    exact hnotcomm inferInstance)
  have hpA : ¬ p ∣ Nat.card A :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp
      (hcop.coprime_dvd_left hpR)
  let fE : A →* MulAut E := restrictMulAutHom E fQ hEinv
  let UE : Subgroup E := U.subgroupOf E
  have hUEinv : ∀ a : A, UE.map (fE a).toMonoidHom = UE := by
    intro a
    exact subgroupOf_map_restrictMulAutHom_eq
      E U hUE fQ hEinv hUinv a
  obtain ⟨XE, hcompl, hXEInv⟩ :=
    exists_invariant_complement_of_coprime_mulAut_action
      hEpow fE hpA UE hUEinv
  let Xbar : Subgroup Q := XE.map E.subtype
  have hXbarInv : ∀ a : A,
      Xbar.map (fQ a).toMonoidHom = Xbar := by
    intro a
    exact map_subtype_invariant_of_restrictMulAutHom
      E XE fQ hEinv hXEInv a
  have hdisUX : Disjoint U Xbar := by
    rw [disjoint_iff]
    apply le_antisymm _ bot_le
    intro y hy
    let e : E := ⟨y, hUE hy.1⟩
    have heUE : e ∈ UE := hy.1
    have heXE : e ∈ XE := by
      obtain ⟨x, hx, hxy⟩ := hy.2
      have hex : e = x := Subtype.ext hxy.symm
      exact hex.symm ▸ hx
    have hebot : e ∈ (⊥ : Subgroup E) := by
      rw [← disjoint_iff.mp hcompl.disjoint]
      exact ⟨heUE, heXE⟩
    exact Subgroup.mem_bot.mpr
      (congrArg (fun z : E ↦ (z : Q)) (Subgroup.mem_bot.mp hebot))
  let Xr : Subgroup R := Xbar.comap q
  have hXrCyclic : IsCyclic Xr :=
    isCyclic_comap_of_disjoint_map_omegaOne
      hR hodd SR (by
        exact (Subgroup.subgroupOfEquivOfLe hSR).isCyclic.mpr hScyclic)
      Xbar hdisUX
  let X : Subgroup G := Xr.map R.subtype
  have hXcyclic : IsCyclic X := by
    let eX := Subgroup.equivMapOfInjective Xr R.subtype R.subtype_injective
    exact isCyclic_of_surjective eX eX.surjective
  have hSX : S ≤ X := by
    intro s hs
    let sR : R := ⟨s, hSR hs⟩
    have hqs : q sR = 1 := (QuotientGroup.eq_one_iff sR).mpr hs
    exact ⟨sR, by
      change q sR ∈ Xbar
      rw [hqs]
      exact Xbar.one_mem, rfl⟩
  have hXR : X ≤ R := Subgroup.map_subtype_le Xr
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha x hx
    obtain ⟨r, hr, rfl⟩ := hx
    let ar : R := ⟨a * (r : G) * a⁻¹, (hnorm ha r).mp r.property⟩
    refine ⟨ar, ?_, rfl⟩
    change q ar ∈ Xbar
    have hqr : q r ∈ Xbar := hr
    have hmapmem : fQ ⟨a, ha⟩ (q r) ∈
        Xbar.map (fQ ⟨a, ha⟩).toMonoidHom :=
      ⟨q r, hqr, rfl⟩
    rw [hXbarInv ⟨a, ha⟩] at hmapmem
    change subgroupConjugationFactorHom S R A hnorm hAS ⟨a, ha⟩
        (QuotientGroup.mk' (S.subgroupOf R) r) ∈ Xbar at hmapmem
    rw [subgroupConjugationFactorHom_apply_mk] at hmapmem
    exact hmapmem
  have hDX : D ≤ X := hDS.trans hSX
  have hXS : X ≤ S :=
    hSmax ⟨hXcyclic, hXR, hAX, hDX⟩ hSX
  have hXeqS : X = S := le_antisymm hXS hSX
  have hXbarBot : Xbar = ⊥ := by
    apply le_antisymm _ bot_le
    intro y hy
    obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective SR y
    have hrXr : r ∈ Xr := hy
    have hrX : (r : G) ∈ X := ⟨r, hrXr, rfl⟩
    have hrS : (r : G) ∈ S := hXS hrX
    exact Subgroup.mem_bot.mpr ((QuotientGroup.eq_one_iff r).mpr hrS)
  have hXEBot : XE = ⊥ := by
    apply Subgroup.map_injective E.subtype_injective
    rw [Subgroup.map_bot]
    exact hXbarBot
  have hUETop : UE = ⊤ := by
    have hcodis : UE ⊔ XE = ⊤ := codisjoint_iff.mp hcompl.codisjoint
    rw [hXEBot, sup_bot_eq] at hcodis
    exact hcodis
  have hUEqE : U = E := by
    apply le_antisymm hUE
    intro y hy
    let e : E := ⟨y, hy⟩
    have he : e ∈ UE := by rw [hUETop]; trivial
    exact he

  let qOmega : omegaOne p R →* U :=
    { toFun := fun x ↦ ⟨q x, ⟨x, x.property, rfl⟩⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hqOmegaSurj : Function.Surjective qOmega := by
    intro y
    obtain ⟨x, hx, hxy⟩ := y.property
    exact ⟨⟨x, hx⟩, Subtype.ext hxy⟩
  have hSp : IsPGroup p S :=
    (hR.to_subgroup SR).of_equiv
      (Subgroup.subgroupOfEquivOfLe hSR)
  have hScardNeOne : Nat.card S ≠ 1 := by
    exact (S.one_lt_card_iff_ne_bot.mpr hSne).ne'
  have hOmegaSCard : Nat.card (omegaOne p S) = p := by
    letI : IsCyclic S := hScyclic
    exact card_omegaOne_of_isCyclic_isPGroup Fact.out hSp hScardNeOne
  have hOmegaSOneLt : 1 < Nat.card (omegaOne p S) := by
    rw [hOmegaSCard]
    exact (Fact.out : p.Prime).one_lt
  letI : Nontrivial (omegaOne p S) :=
    Finite.one_lt_card_iff_nontrivial.mp hOmegaSOneLt
  obtain ⟨z, hz⟩ := exists_ne (1 : omegaOne p S)
  let toR : S →* R :=
    { toFun := fun s ↦ ⟨s, hSR s.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hzOmegaR : toR z ∈ omegaOne p R :=
    map_omegaOne_le p toR (Subgroup.mem_map_of_mem toR z.property)
  let zR : omegaOne p R := ⟨toR z, hzOmegaR⟩
  have hzRne : zR ≠ 1 := by
    intro hzR
    apply hz
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun r : omegaOne p R ↦ ((r : R) : G)) hzR
  have hqz : qOmega zR = 1 := by
    apply Subtype.ext
    apply (QuotientGroup.eq_one_iff (zR : R)).mpr
    exact (z : S).property
  have hqOmegaNotInj : ¬ Function.Injective qOmega := by
    intro hinj
    exact hzRne (hinj (hqz.trans (map_one qOmega).symm))
  letI := Fintype.ofFinite (omegaOne p R)
  letI := Fintype.ofFinite U
  have hUcardLt : Nat.card U < Nat.card (omegaOne p R) := by
    simpa [Nat.card_eq_fintype_card] using
      Fintype.card_lt_of_surjective_not_injective
        qOmega hqOmegaSurj hqOmegaNotInj
  have hElemR : IsElementaryAbelianOfRank p 2 (omegaOne p R) :=
    omegaOne_isElementaryAbelian_rank_two_of_isMetacyclic
      hmeta hR hodd (fun hcyc ↦ hnotcomm hcyc.isMulCommutative)
  have hEcardLt : Nat.card E < p ^ 2 := by
    calc
      Nat.card E = Nat.card U :=
        Nat.card_congr (MulEquiv.subgroupCongr hUEqE.symm).toEquiv
      _ < Nat.card (omegaOne p R) := hUcardLt
      _ = p ^ 2 := hElemR.card_eq
  have hQcyclic : IsCyclic Q := by
    apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hQp hQodd).mpr
    rintro ⟨F, hF⟩
    have hFE : F ≤ E := by
      intro x hx
      apply mem_omegaOne_of_pow_eq_one p
      exact congrArg (fun z : F ↦ (z : Q)) (hF.pow_eq_one ⟨x, hx⟩)
    have hcardle := Subgroup.card_le_of_le hFE
    rw [hF.card_eq] at hcardle
    exact (not_lt_of_ge hcardle) hEcardLt
  letI : IsCyclic Q := hQcyclic
  apply hnotcomm
  apply q.isMulCommutative_of_isCyclic_of_ker_le_center
  rw [show q.ker = SR by exact QuotientGroup.ker_mk' SR]
  exact hScenter

/-- Part (a) of `BGsection4.v: coprime_metacyclic_cent_sdprod`: the
commutator of a coprime actor with an odd metacyclic `p`-group is
commutative. -/
theorem commutator_isMulCommutative_of_coprime_metacyclic
    (R A : Subgroup G)
    (hR : IsPGroup p R) (hodd : Odd (Nat.card R))
    (hmeta : IsMetacyclic R)
    (hnorm : A ≤ Subgroup.normalizer (R : Set G))
    (hcop : (Nat.card R).Coprime (Nat.card A)) :
    IsMulCommutative (⁅R, A⁆ : Subgroup G) := by
  classical
  let T : Subgroup G := ⁅R, A⁆
  have hTR : T ≤ R := by
    simpa [T, Subgroup.commutator_comm R A] using
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm)
  have hTp : IsPGroup p T := hR.to_subgroup (T.subgroupOf R) |>.of_equiv
    (Subgroup.subgroupOfEquivOfLe hTR)
  have hTodd : Odd (Nat.card T) := by
    have hdvd : Nat.card (T.subgroupOf R) ∣ Nat.card R :=
      (T.subgroupOf R).card_subgroup_dvd_card
    rw [Nat.card_congr
      (Subgroup.subgroupOfEquivOfLe hTR).toEquiv] at hdvd
    exact hodd.of_dvd_nat hdvd
  have hTmeta : IsMetacyclic T := by
    have hsub : IsMetacyclic (T.subgroupOf R) :=
      isMetacyclic_subgroup hmeta (T.subgroupOf R)
    exact isMetacyclic_of_mulEquiv T
      (Subgroup.subgroupOfEquivOfLe hTR).symm hsub
  have hTnorm : A ≤ Subgroup.normalizer (T : Set G) := by
    exact Subgroup.normalizer_commutator_ge_right R A
  have hTcop : (Nat.card T).Coprime (Nat.card A) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hTR)
  letI : Group.IsNilpotent R := hR.isNilpotent
  have hidem : ⁅A, ⁅A, R⁆⁆ = ⁅A, R⁆ :=
    commutator_commutator_eq_of_coprime
      (K := R) (R := A) hnorm hcop
  have hperfect : ⁅T, A⁆ = T := by
    calc
      ⁅T, A⁆ = ⁅A, T⁆ := Subgroup.commutator_comm T A
      _ = ⁅A, ⁅R, A⁆⁆ := rfl
      _ = ⁅A, ⁅A, R⁆⁆ := by rw [Subgroup.commutator_comm R A]
      _ = ⁅A, R⁆ := hidem
      _ = T := Subgroup.commutator_comm A R
  exact isMulCommutative_of_perfect_coprime_metacyclic_action
    T A hTp hTodd hTmeta hTnorm hTcop hperfect

/-- Coprime idempotence says that the actor acts perfectly on its mixed
commutator. -/
private theorem actor_commutator_perfect
    (R A : Subgroup G) (hR : IsPGroup p R)
    (hnorm : A ≤ Subgroup.normalizer (R : Set G))
    (hcop : (Nat.card R).Coprime (Nat.card A)) :
    ⁅A, ⁅R, A⁆⁆ = ⁅R, A⁆ := by
  letI : Group.IsNilpotent R := hR.isNilpotent
  have hidem : ⁅A, ⁅A, R⁆⁆ = ⁅A, R⁆ :=
    commutator_commutator_eq_of_coprime
      (K := R) (R := A) hnorm hcop
  calc
    ⁅A, ⁅R, A⁆⁆ = ⁅A, ⁅A, R⁆⁆ := by
      rw [Subgroup.commutator_comm R A]
    _ = ⁅A, R⁆ := hidem
    _ = ⁅R, A⁆ := Subgroup.commutator_comm A R

/-- The mixed commutator meets the actor-fixed subgroup trivially. -/
private theorem commutator_centralizerWithin_disjoint
    (R A : Subgroup G) (hR : IsPGroup p R)
    (hnorm : A ≤ Subgroup.normalizer (R : Set G))
    (hcop : (Nat.card R).Coprime (Nat.card A))
    (hcomm : IsMulCommutative (⁅R, A⁆ : Subgroup G)) :
    Disjoint ((⁅R, A⁆ : Subgroup G).subgroupOf R)
      ((centralizerWithin R A).subgroupOf R) := by
  classical
  let T : Subgroup G := ⁅R, A⁆
  let C : Subgroup G := centralizerWithin R A
  have hTR : T ≤ R := by
    simpa [T, Subgroup.commutator_comm R A] using
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm)
  have hTnormA : A ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.normalizer_commutator_ge_right R A
  have hTcop : (Nat.card T).Coprime (Nat.card A) :=
    hcop.coprime_dvd_left (Subgroup.card_dvd_of_le hTR)
  have hTperfect : ⁅A, T⁆ = T :=
    actor_commutator_perfect R A hR hnorm hcop
  letI : IsMulCommutative T := hcomm
  rw [disjoint_iff]
  apply le_antisymm _ bot_le
  intro x hx
  let xt : T := ⟨(x : R), hx.1⟩
  have hxC : ((x : R) : G) ∈ C := hx.2
  have hfix : ∀ a : A,
      (a : G) * (xt : G) * (a : G)⁻¹ = (xt : G) := by
    intro a
    calc
      (a : G) * (xt : G) * (a : G)⁻¹ =
          (xt : G) * (a : G) * (a : G)⁻¹ := by
            rw [hxC.2 (a : G) a.property]
      _ = (xt : G) := by simp
  have hxt : xt = 1 :=
    Submission.OddOrder.BG.Section06.fixed_eq_one_of_abelian_perfect_coprime_conjugation
      hTnormA hTcop hTperfect xt hfix
  apply Subgroup.mem_bot.mpr
  apply Subtype.ext
  exact congrArg (fun z : T ↦ (z : G)) hxt

set_option maxHeartbeats 600000 in
/-- Coprime central-product generation, specialized to a `p`-group. -/
private theorem commutator_sup_centralizerWithin_eq
    (R A : Subgroup G) (hR : IsPGroup p R)
    (hnorm : A ≤ Subgroup.normalizer (R : Set G))
    (hcop : (Nat.card R).Coprime (Nat.card A)) :
    ⁅R, A⁆ ⊔ centralizerWithin R A = R := by
  letI : Group.IsNilpotent R := hR.isNilpotent
  apply le_antisymm
  · exact sup_le
      (by simpa [Subgroup.commutator_comm R A] using
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm))
      (centralizerWithin_le_left R A)
  · rw [Subgroup.commutator_comm R A]
    exact le_commutator_sup_centralizerWithin_of_coprime
      (K := R) (R := A) hnorm hcop

set_option maxHeartbeats 400000 in
/-- The mixed commutator and the fixed-point subgroup form an internal
complement once the mixed commutator is commutative. -/
private theorem commutator_centralizerWithin_isComplement
    (R A : Subgroup G) (hR : IsPGroup p R)
    (hnorm : A ≤ Subgroup.normalizer (R : Set G))
    (hcop : (Nat.card R).Coprime (Nat.card A))
    (hcomm : IsMulCommutative (⁅R, A⁆ : Subgroup G)) :
    ((⁅R, A⁆ : Subgroup G).subgroupOf R).IsComplement'
      ((centralizerWithin R A).subgroupOf R) := by
  classical
  let T : Subgroup G := ⁅R, A⁆
  let C : Subgroup G := centralizerWithin R A
  let TR : Subgroup R := T.subgroupOf R
  let CR : Subgroup R := C.subgroupOf R
  change TR.IsComplement' CR
  have hTR : T ≤ R := by
    simpa [T, Subgroup.commutator_comm R A] using
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm)
  have hCR : C ≤ R := centralizerWithin_le_left R A
  have hsup : T ⊔ C = R :=
    commutator_sup_centralizerWithin_eq R A hR hnorm hcop
  have hsupR : TR ⊔ CR = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTR hCR, hsup]
    exact Subgroup.subgroupOf_self R
  have hTRnormal : TR.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.normalizer_commutator_ge_left R A)
  letI : TR.Normal := hTRnormal
  apply Subgroup.isComplement'_of_disjoint_and_mul_eq_univ
    (commutator_centralizerWithin_disjoint R A hR hnorm hcop hcomm)
  rw [← Subgroup.normal_mul TR CR, hsupR]
  rfl

/-- `BGsection4.v: coprime_metacyclic_cent_sdprod` (Bender--Glauberman
Theorem 4.12).  A coprime actor on an odd metacyclic `p`-group splits the
group into its commutator and fixed-point factors.  In the noncommutative,
nontrivial-action case both factors are cyclic and the derived subgroup is
contained in the commutator factor. -/
theorem coprime_metacyclic_cent_sdprod
    (R A : Subgroup G)
    (hR : IsPGroup p R) (hodd : Odd (Nat.card R))
    (hmeta : IsMetacyclic R)
    (hnorm : A ≤ Subgroup.normalizer (R : Set G))
    (hcop : (Nat.card R).Coprime (Nat.card A)) :
    let T : Subgroup G := ⁅R, A⁆
    let C : Subgroup G := centralizerWithin R A
    IsMulCommutative T ∧
      (T.subgroupOf R).IsComplement' (C.subgroupOf R) ∧
      (¬ IsMulCommutative R → T ≠ ⊥ →
        C ≠ ⊥ ∧ IsCyclic T ∧ IsCyclic C ∧ ⁅R, R⁆ ≤ T) := by
  classical
  let T : Subgroup G := ⁅R, A⁆
  let C : Subgroup G := centralizerWithin R A
  let TR : Subgroup R := T.subgroupOf R
  let CR : Subgroup R := C.subgroupOf R
  change IsMulCommutative T ∧ TR.IsComplement' CR ∧
    (¬ IsMulCommutative R → T ≠ ⊥ →
      C ≠ ⊥ ∧ IsCyclic T ∧ IsCyclic C ∧ ⁅R, R⁆ ≤ T)
  have hTR : T ≤ R := by
    simpa [T, Subgroup.commutator_comm R A] using
      (Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm)
  have hCR : C ≤ R := centralizerWithin_le_left R A
  have hcomm : IsMulCommutative T := by
    simpa [T] using commutator_isMulCommutative_of_coprime_metacyclic
      R A hR hodd hmeta hnorm hcop
  have hcomp : TR.IsComplement' CR := by
    simpa [T, C, TR, CR] using
      commutator_centralizerWithin_isComplement R A hR hnorm hcop hcomm
  refine ⟨hcomm, hcomp, ?_⟩
  intro hnotcomm hTne
  have hsup : T ⊔ C = R := by
    simpa [T, C] using
      commutator_sup_centralizerWithin_eq R A hR hnorm hcop
  have hCne : C ≠ ⊥ := by
    intro hCbot
    apply hnotcomm
    have hTR_eq : T = R := by
      simpa [hCbot] using hsup
    rw [← hTR_eq]
    exact hcomm
  have hTRne : TR ≠ ⊥ := by
    intro hTRbot
    apply hTne
    dsimp [TR] at hTRbot
    rw [← Subgroup.map_subgroupOf_eq_of_le hTR, hTRbot,
      Subgroup.map_bot]
  have hCRne : CR ≠ ⊥ := by
    intro hCRbot
    apply hCne
    dsimp [CR] at hCRbot
    rw [← Subgroup.map_subgroupOf_eq_of_le hCR, hCRbot,
      Subgroup.map_bot]
  have hnotcyclicR : ¬ IsCyclic R := fun hcyclic ↦
    hnotcomm hcyclic.isMulCommutative
  have hcyclicPair : IsCyclic TR ∧ IsCyclic CR :=
    isCyclic_pair_of_disjoint_of_isMetacyclic
      hR hodd hmeta hnotcyclicR TR CR hcomp.disjoint hTRne hCRne
  have hTcyclic : IsCyclic T :=
    (Subgroup.subgroupOfEquivOfLe hTR).isCyclic.mp hcyclicPair.1
  have hCcyclic : IsCyclic C :=
    (Subgroup.subgroupOfEquivOfLe hCR).isCyclic.mp hcyclicPair.2
  have hTRnormal : TR.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer
      (Subgroup.normalizer_commutator_ge_left R A)
  letI : TR.Normal := hTRnormal
  let eQ : R ⧸ TR ≃* CR := hcomp.symm.QuotientMulEquiv
  have hQcyclic : IsCyclic (R ⧸ TR) :=
    eQ.isCyclic.mpr hcyclicPair.2
  have hderivedTR : _root_.commutator R ≤ TR :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp
      hQcyclic.isMulCommutative
  have hderived : ⁅R, R⁆ ≤ T := by
    rw [← R.map_subtype_commutator,
      ← Subgroup.map_subgroupOf_eq_of_le hTR]
    exact Subgroup.map_mono hderivedTR
  exact ⟨hCne, hTcyclic, hCcyclic, hderived⟩

end

end Submission.OddOrder.BG.Section04
