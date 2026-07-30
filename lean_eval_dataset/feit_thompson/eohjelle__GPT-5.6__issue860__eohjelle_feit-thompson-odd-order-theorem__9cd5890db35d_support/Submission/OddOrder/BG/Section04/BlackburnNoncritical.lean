import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.MathlibSupport.CentralCommutatorPowers
import Submission.OddOrder.MathlibSupport.Centralizer
import Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer
import Submission.OddOrder.MathlibSupport.CommutatorSup
import Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement
import Submission.OddOrder.MathlibSupport.CyclicQuotientGenerator
import Submission.OddOrder.MathlibSupport.Extraspecial
import Submission.OddOrder.MathlibSupport.InvariantSubgroupAction
import Submission.OddOrder.MathlibSupport.NilpotentNormalCommutator
import Submission.OddOrder.MathlibSupport.NormalElementaryAbelianRankTwo
import Submission.OddOrder.MathlibSupport.OmegaOneFunctorial
import Submission.OddOrder.MathlibSupport.OddTwoLineAction
import Submission.OddOrder.MathlibSupport.PrimeIndex
import Submission.OddOrder.MathlibSupport.Section05RankTwoAction
import Submission.OddOrder.MathlibSupport.SubgroupCardinality
import Submission.OddOrder.MathlibSupport.SubgroupConjugationFactor

/-!
The noncritical branch in the proof of Bender--Glauberman Theorem 4.16.

This is Blackburn's argument beginning with `T = [S,R]` in
`BGsection4.v`.  The critical branch is handled separately by
`extraspecial_sup_centralizerWithin_eq`.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement IsMulCommutative

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

private theorem commutatorElement_pow_right_of_commute
    {H : Type*} [Group H] (a b : H)
    (hcomm : Commute b ⁅a, b⁆) :
    ∀ n : ℕ, ⁅a, b ^ n⁆ = ⁅a, b⁆ ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, _root_.commutatorElement_mul_right_eq_mul_conj,
        commutatorElement_pow_right_of_commute a b hcomm n, pow_succ]
      have hn := hcomm.pow_left n
      calc
        ⁅a, b⁆ ^ n * b ^ n * ⁅a, b⁆ * (b ^ n)⁻¹ =
            ⁅a, b⁆ ^ n * (b ^ n * ⁅a, b⁆) * (b ^ n)⁻¹ := by group
        _ = ⁅a, b⁆ ^ n * (⁅a, b⁆ * b ^ n) * (b ^ n)⁻¹ := by
          rw [hn.eq]
        _ = ⁅a, b⁆ ^ n * ⁅a, b⁆ := by group

private theorem commutatorElement_pow_left_of_commute
    {H : Type*} [Group H] (a b : H)
    (hcomm : Commute a ⁅a, b⁆) :
    ∀ n : ℕ, ⁅a ^ n, b⁆ = ⁅a, b⁆ ^ n
  | 0 => by simp
  | n + 1 => by
      rw [pow_succ, _root_.commutatorElement_mul_left_eq_conj_mul,
        commutatorElement_pow_left_of_commute a b hcomm n, pow_succ]
      have hn := hcomm.pow_left n
      calc
        a ^ n * ⁅a, b⁆ * (a ^ n)⁻¹ * ⁅a, b⁆ ^ n =
            (⁅a, b⁆ * a ^ n) * (a ^ n)⁻¹ * ⁅a, b⁆ ^ n := by
          rw [hn.eq]
        _ = ⁅a, b⁆ * ⁅a, b⁆ ^ n := by group
        _ = ⁅a, b⁆ ^ n * ⁅a, b⁆ := by
          exact (Commute.self_pow ⁅a, b⁆ n).eq

private theorem commutatorElement_pow_pow_of_commute
    {H : Type*} [Group H] (a b : H)
    (ha : Commute a ⁅a, b⁆) (hb : Commute b ⁅a, b⁆)
    (m n : ℕ) :
    ⁅a ^ m, b ^ n⁆ = ⁅a, b⁆ ^ (m * n) := by
  have hleft := commutatorElement_pow_left_of_commute a b ha m
  have hb' : Commute b ⁅a ^ m, b⁆ := hleft.symm ▸ hb.pow_right m
  rw [commutatorElement_pow_right_of_commute (a ^ m) b hb' n,
    hleft, ← pow_mul]

/-- The Blackburn noncritical branch in `BGsection4.v`: under a perfect
odd coprime action, the commutator of the extraspecial omega subgroup with
the ambient `p`-group cannot properly contain the derived subgroup. -/
theorem blackburn_noncritical_impossible
    (R A S : Subgroup G)
    (hR : IsPGroup p R)
    (hoddR : Odd (Nat.card R))
    (hOmega : (omegaOne p R).map R.subtype = S)
    (hS : IsExtraspecial S)
    (hScard : Nat.card S = p ^ 3)
    (hSexp : Monoid.exponent S ∣ p)
    (hperfect : ⁅R, A⁆ = R)
    (hAprime : Nat.Coprime p (Nat.card A))
    (hoddA : Odd (Nat.card A))
    (hOmegaC :
      (omegaOne p (centralizerWithin R S)).map
          (centralizerWithin R S).subtype =
        (_root_.commutator S).map S.subtype)
    (hnoncritical :
      ¬ ⁅S, R⁆ ≤ (_root_.commutator S).map S.subtype) :
    False := by
  classical
  let Z : Subgroup G := (_root_.commutator S).map S.subtype
  let T : Subgroup G := ⁅S, R⁆

  have hSR : S ≤ R := by
    rw [← hOmega]
    exact Subgroup.map_subtype_le _
  have hSp : IsPGroup p S :=
    (hR.to_subgroup (S.subgroupOf R)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hSR)
  have hZR : Z ≤ R := by
    dsimp [Z]
    exact (Subgroup.map_subtype_le _).trans hSR
  have hZS : Z ≤ S := by
    dsimp [Z]
    exact Subgroup.map_subtype_le _
  have hZcard : Nat.card Z = p := by
    calc
      Nat.card Z = Nat.card (_root_.commutator S) :=
          (show Nat.card ((_root_.commutator S).map S.subtype) =
            Nat.card (_root_.commutator S) from
          Subgroup.card_map_of_injective S.subtype_injective)
      _ = Nat.card (Subgroup.center S) := by
        rw [hS.toIsSpecial.commutator_eq_center]
      _ = p := hS.center_card_eq hSp

  have hRnormS : R ≤ Subgroup.normalizer (S : Set G) := by
    rw [← hOmega, Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      R R (omegaOne p R) Subgroup.le_normalizer
  have hTS : T ≤ S := by
    dsimp [T]
    exact Subgroup.le_normalizer_iff_commutator_le_left.mp hRnormS
  have hTR : T ≤ R := hTS.trans hSR
  have hZT : Z ≤ T := by
    dsimp [Z, T]
    rw [Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_mono le_rfl hSR
  have hZTlt : Z < T := by
    refine lt_of_le_of_ne hZT ?_
    intro hEq
    exact hnoncritical hEq.ge

  let SR : Subgroup R := S.subgroupOf R
  let TR : Subgroup R := T.subgroupOf R
  have hSRnormal : SR.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hRnormS
  letI : SR.Normal := hSRnormal
  letI : Group.IsNilpotent R := hR.isNilpotent
  have hcommSR : ⁅SR, (⊤ : Subgroup R)⁆ = TR := by
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_commutator,
      Subgroup.map_subgroupOf_eq_of_le hSR,
      ← MonoidHom.range_eq_map, R.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hTR]
  have hSRne : SR ≠ ⊥ := by
    apply SR.one_lt_card_iff_ne_bot.mp
    rw [natCard_subgroupOf_eq hSR, hScard]
    exact one_lt_pow₀ (Fact.out : p.Prime).one_lt (by decide : (3 : ℕ) ≠ 0)
  have hTRltSR : TR < SR := by
    rw [← hcommSR]
    exact commutator_top_lt_of_normal_ne_bot hSRne
  have hTSlt : T < S := by
    refine lt_of_le_of_ne hTS ?_
    intro hEq
    apply hTRltSR.ne
    apply Subgroup.map_injective R.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le hTR,
      Subgroup.map_subgroupOf_eq_of_le hSR, hEq]

  have hTp : IsPGroup p T :=
    (hR.to_subgroup TR).of_equiv
      (Subgroup.subgroupOfEquivOfLe hTR)
  obtain ⟨n, hTcardPow⟩ := hTp.exists_card_eq
  have hnLower : 1 < n := by
    have hcardlt := natCard_subgroup_lt_of_lt hZTlt
    rw [hZcard, hTcardPow] at hcardlt
    by_contra hn
    have hnle : n ≤ 1 := Nat.le_of_not_gt hn
    have hpownle : p ^ n ≤ p ^ 1 :=
      Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle
    exact (not_lt_of_ge hpownle) (by simpa using hcardlt)
  have hnUpper : n < 3 := by
    have hcardlt := natCard_subgroup_lt_of_lt hTSlt
    rw [hTcardPow, hScard] at hcardlt
    by_contra hn
    have hthree : 3 ≤ n := Nat.le_of_not_gt hn
    exact (not_lt_of_ge
      (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hthree)) hcardlt
  have hn : n = 2 := by omega
  have hTcard : Nat.card T = p ^ 2 := by simpa [hn] using hTcardPow
  have hTcomm : IsMulCommutative T :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hTcard
  have hTpow : ∀ x : T, x ^ p = 1 := by
    intro x
    let xS : S := ⟨x, hTS x.property⟩
    have hpow : xS ^ p = 1 := by
      apply (Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hSexp)
    apply Subtype.ext
    exact congrArg (fun z : S ↦ (z : G)) hpow
  have hTelem : IsElementaryAbelianOfRank p 2 T :=
    { isPGroup := hTp
      commutative := hTcomm
      pow_eq_one := hTpow
      card_eq := hTcard }

  let B : Subgroup G := centralizerWithin R T
  let BR : Subgroup R := B.subgroupOf R
  have hBR : B ≤ R := centralizerWithin_le_left R T
  have hTB : T ≤ B := by
    intro t ht
    refine ⟨hTR ht, ?_⟩
    intro u hu
    let tT : T := ⟨t, ht⟩
    let uT : T := ⟨u, hu⟩
    exact congrArg Subtype.val (show uT * tT = tT * uT from mul_comm uT tT)
  have hSnleB : ¬ S ≤ B := by
    intro hSB
    apply hnoncritical
    have hTcenter : T ≤ centerWithin S := by
      intro t ht
      refine ⟨hTS ht, ?_⟩
      intro s hs
      have hsB := hSB hs
      exact (hsB.2 t ht).symm
    calc
      T ≤ centerWithin S := hTcenter
      _ = (Subgroup.center S).map S.subtype :=
        (map_center_eq_centerWithin S).symm
      _ = Z := by
        dsimp [Z]
        rw [hS.toIsSpecial.commutator_eq_center]
  have hBneTop : BR ≠ ⊤ := by
    intro htop
    apply hSnleB
    intro s hs
    have hsR : (s : G) ∈ R := hSR hs
    have hsBR : (⟨s, hsR⟩ : R) ∈ BR := by rw [htop]; trivial
    exact hsBR

  have hRnormT : R ≤ Subgroup.normalizer (T : Set G) :=
    Subgroup.normalizer_commutator_ge_right S R
  let normalizerHom : R →* Subgroup.normalizer (T : Set G) :=
    R.subtype.codRestrict (Subgroup.normalizer (T : Set G))
      (fun r ↦ hRnormT r.property)
  let rho : R →* MulAut T := T.normalizerMonoidHom.comp normalizerHom
  have hker : rho.ker = BR := by
    ext r
    change normalizerHom r ∈ T.normalizerMonoidHom.ker ↔ (r : G) ∈ B
    rw [Subgroup.normalizerMonoidHom_ker]
    change (r : G) ∈ Subgroup.centralizer (T : Set G) ↔ (r : G) ∈ B
    simp only [B, centralizerWithin, Subgroup.mem_inf, r.property,
      true_and]
  have hQcard : Nat.card (R ⧸ rho.ker) ≤ p :=
    section05_natCard_quotient_ker_mulAut_le_prime hR hTelem rho
  have hindexLe : BR.index ≤ p := by
    rw [BR.index_eq_card, ← hker]
    exact hQcard
  have hindexOneLt : 1 < BR.index :=
    Subgroup.one_lt_index_of_ne_top hBneTop
  obtain ⟨m, hindexPow⟩ := hR.index BR
  have hmne : m ≠ 0 := by
    intro hm
    rw [hindexPow, hm, pow_zero] at hindexOneLt
    omega
  have hmpos : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hmne
  have hmle : m ≤ 1 := by
    apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
    rw [← hindexPow, pow_one]
    exact hindexLe
  have hm : m = 1 := by omega
  have hBindex : BR.index = p := by
    rw [hindexPow, hm, pow_one]
  have hBRnormal : BR.Normal :=
    normal_of_index_eq_prime (Fact.out : p.Prime) hR hBindex
  letI : BR.Normal := hBRnormal
  have hBRcoatom : IsCoatom BR :=
    isCoatom_of_index_eq_prime (Fact.out : p.Prime) hBindex
  have hSRnleBR : ¬ SR ≤ BR := by
    intro hle
    apply hSnleB
    intro s hs
    exact hle (show (⟨s, hSR hs⟩ : R) ∈ SR from hs)
  have hBRSR : BR ⊔ SR = ⊤ := by
    rcases hBRcoatom.le_iff.mp (show BR ≤ BR ⊔ SR from le_sup_left)
      with htop | heq
    · exact htop
    · exact (hSRnleBR (show SR ≤ BR from heq ▸ le_sup_right)).elim
  have hBS : B ⊔ S = R := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hBR,
      ← Subgroup.map_subgroupOf_eq_of_le hSR,
      ← Subgroup.map_sup, hBRSR,
      ← MonoidHom.range_eq_map, R.range_subtype]

  have hAnormR : A ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hperfect.le
  have hAnormS : A ≤ Subgroup.normalizer (S : Set G) := by
    rw [← hOmega, Subgroup.le_normalizer_iff]
    exact characteristic_map_subtype_invariant_under_normalizer
      R A (omegaOne p R) hAnormR
  have hAnormT : A ≤ Subgroup.normalizer (T : Set G) := by
    dsimp [T]
    apply Subgroup.le_normalizer_closure_iff.mpr
    rintro a ha _ ⟨s, hs, r, hr, rfl⟩
    rw [_root_.conjugate_commutatorElement]
    exact Subgroup.commutator_mem_commutator
      (Subgroup.le_normalizer_iff.mp hAnormS a ha s hs)
      (Subgroup.le_normalizer_iff.mp hAnormR a ha r hr)
  have hAnormZ : A ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha z hz
    exact characteristic_map_subtype_invariant_under_normalizer
      S A (_root_.commutator S) hAnormS a ha z hz

  let C : Subgroup G := centralizerWithin R S
  have hCR : C ≤ R := centralizerWithin_le_left R S
  have hCB : C ≤ B := centralizerWithin_antitone_right hTS
  have hNormalizerS : Subgroup.normalizer (S : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (S : Set G))).mp inferInstance
  have hAnormCentS : A ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) :=
    hAnormS.trans hNormalizerS
  have hAnormC : A ≤ Subgroup.normalizer (C : Set G) := by
    dsimp [C, centralizerWithin]
    exact (le_inf hAnormR hAnormCentS).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hRnormCentS : R ≤
      Subgroup.normalizer (Subgroup.centralizer (S : Set G) : Set G) :=
    hRnormS.trans hNormalizerS
  have hRnormC : R ≤ Subgroup.normalizer (C : Set G) := by
    dsimp [C, centralizerWithin]
    exact (le_inf Subgroup.le_normalizer hRnormCentS).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hNormalizerT : Subgroup.normalizer (T : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (T : Set G) : Set G) := by
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Subgroup.centralizer_le_normalizer (T : Set G))).mp inferInstance
  have hAnormCentT : A ≤
      Subgroup.normalizer (Subgroup.centralizer (T : Set G) : Set G) :=
    hAnormT.trans hNormalizerT
  have hAnormB : A ≤ Subgroup.normalizer (B : Set G) := by
    dsimp [B, centralizerWithin]
    exact (le_inf hAnormR hAnormCentT).trans
      Subgroup.inf_normalizer_le_normalizer_inf

  have hBcentT : B ≤ Subgroup.centralizer (T : Set G) := by
    intro b hb
    exact hb.2
  have hTBbot : ⁅T, B⁆ = ⊥ := by
    rw [Subgroup.commutator_comm,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hBcentT
  have hSBleT : ⁅S, B⁆ ≤ T :=
    Subgroup.commutator_mono le_rfl hBR
  have hSBBbot : ⁅⁅S, B⁆, B⁆ = ⊥ := by
    apply le_bot_iff.mp
    exact (Subgroup.commutator_mono hSBleT le_rfl).trans hTBbot.le
  have hBSBbot : ⁅⁅B, S⁆, B⁆ = ⊥ := by
    rw [Subgroup.commutator_comm B S]
    exact hSBBbot
  have hBBSbot : ⁅⁅B, B⁆, S⁆ = ⊥ :=
    Subgroup.commutator_commutator_eq_bot_of_rotate hBSBbot hSBBbot
  have hBBleC : ⁅B, B⁆ ≤ C := by
    have hcent : ⁅B, B⁆ ≤ Subgroup.centralizer (S : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBBSbot
    intro x hx
    exact ⟨hBR (Subgroup.commutator_le_self B hx), hcent hx⟩

  let CB : Subgroup B := C.subgroupOf B
  have hCBnormal : CB.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hBR.trans hRnormC)
  letI : CB.Normal := hCBnormal
  let Q := B ⧸ CB
  have hQcomm : IsMulCommutative Q := by
    apply Subgroup.Normal.quotient_commutative_iff_commutator_le.mpr
    intro x hx
    change ((x : B) : G) ∈ C
    apply hBBleC
    rw [← B.map_subtype_commutator]
    exact ⟨x, hx, rfl⟩
  letI : IsMulCommutative Q := hQcomm
  have hQpow : ∀ q : Q, q ^ p = 1 := by
    intro q
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective CB q
    apply (QuotientGroup.eq_one_iff (b ^ p)).mpr
    change (((b ^ p : B) : G)) ∈ C
    refine ⟨hBR (b ^ p).property, ?_⟩
    intro s hs
    have hsbT : ⁅s, (b : G)⁆ ∈ T :=
      Subgroup.commutator_mem_commutator hs (hBR b.property)
    have hbcomm : Commute (b : G) ⁅s, (b : G)⁆ := by
      have hcentral := Subgroup.mem_centralizer_iff.mp
        (hBcentT b.property) ⁅s, (b : G)⁆ hsbT
      exact hcentral.symm
    have hcommPow : ⁅s, (b : G)⁆ ^ p = 1 := by
      let cT : T := ⟨⁅s, (b : G)⁆, hsbT⟩
      exact congrArg (fun z : T ↦ (z : G)) (hTpow cT)
    have hone : ⁅s, (b : G) ^ p⁆ = 1 := by
      rw [commutatorElement_pow_right_of_commute s (b : G) hbcomm p,
        hcommPow]
    exact commutatorElement_eq_one_iff_mul_comm.mp hone

  let q : B →* Q := QuotientGroup.mk' CB
  let TB : Subgroup B := T.subgroupOf B
  let fB : A →* MulAut B :=
    B.normalizerMonoidHom.comp (Subgroup.inclusion hAnormB)
  let fQ : A →* MulAut Q :=
    subgroupConjugationFactorHom C B A hAnormB hAnormC
  have hTBinv : ∀ a : A, TB.map (fB a).toMonoidHom = TB := by
    intro a
    apply Subgroup.map_injective B.subtype_injective
    rw [Subgroup.map_map]
    have hcomp : B.subtype.comp (fB a).toMonoidHom =
        (MulAut.conj (a : G)).toMonoidHom.comp B.subtype := by
      ext b
      rfl
    rw [hcomp, ← Subgroup.map_map,
      Subgroup.map_subgroupOf_eq_of_le hTB]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (hAnormT a.property)
  let U : Subgroup Q := TB.map q
  have hUinv : ∀ a : A, U.map (fQ a).toMonoidHom = U := by
    intro a
    rw [Subgroup.map_map]
    have hcomp : (fQ a).toMonoidHom.comp q =
        q.comp (fB a).toMonoidHom := by
      ext b
      change subgroupConjugationFactorHom C B A hAnormB hAnormC a
          (QuotientGroup.mk' CB b) =
        QuotientGroup.mk' CB (fB a b)
      rw [subgroupConjugationFactorHom_apply_mk]
      rfl
    rw [hcomp, ← Subgroup.map_map, hTBinv]
  have hpA : ¬ p ∣ Nat.card A :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp hAprime
  obtain ⟨Xbar, hcompl, hXbarInv⟩ :=
    exists_invariant_complement_of_coprime_mulAut_action
      hQpow fQ hpA U hUinv
  let XB : Subgroup B := Xbar.comap q
  let X : Subgroup G := XB.map B.subtype
  have hXB : X ≤ B := Subgroup.map_subtype_le XB
  have hCX : C ≤ X := by
    intro c hc
    let cB : B := ⟨c, hCB hc⟩
    refine ⟨cB, ?_, rfl⟩
    change q cB ∈ Xbar
    have hcCB : cB ∈ CB := hc
    rw [show q cB = 1 from (QuotientGroup.eq_one_iff cB).mpr hcCB]
    exact Xbar.one_mem
  have hTXC : T ⊓ X ≤ C := by
    intro x hx
    obtain ⟨b, hbXB, rfl⟩ := hx.2
    have hbTB : b ∈ TB := hx.1
    have hqbU : q b ∈ U := ⟨b, hbTB, rfl⟩
    have hqbX : q b ∈ Xbar := hbXB
    have hqbBot : q b ∈ (U ⊓ Xbar) := ⟨hqbU, hqbX⟩
    rw [disjoint_iff.mp hcompl.disjoint] at hqbBot
    have hqbOne : q b = 1 := Subgroup.mem_bot.mp hqbBot
    exact (QuotientGroup.eq_one_iff b).mp hqbOne
  have hAX : A ≤ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro a ha x hx
    obtain ⟨b, hb, rfl⟩ := hx
    let b' : B :=
      ⟨(a : G) * (b : G) * (a : G)⁻¹,
        (hAnormB ha b).mp b.property⟩
    refine ⟨b', ?_, rfl⟩
    change q b' ∈ Xbar
    have hmapmem : fQ ⟨a, ha⟩ (q b) ∈
        Xbar.map (fQ ⟨a, ha⟩).toMonoidHom :=
      ⟨q b, hb, rfl⟩
    rw [hXbarInv ⟨a, ha⟩] at hmapmem
    change subgroupConjugationFactorHom C B A hAnormB hAnormC
        ⟨a, ha⟩ (QuotientGroup.mk' CB b) ∈ Xbar at hmapmem
    rw [subgroupConjugationFactorHom_apply_mk] at hmapmem
    exact hmapmem
  have hkerqXB : q.ker ≤ XB := by
    intro b hb
    change q b ∈ Xbar
    rw [MonoidHom.mem_ker.mp hb]
    exact Xbar.one_mem
  have hTBXB : TB ⊔ XB = ⊤ := by
    apply Subgroup.map_injective_of_ker_le q
      (hkerqXB.trans le_sup_right) le_top
    rw [Subgroup.map_sup]
    change U ⊔ XB.map q = (⊤ : Subgroup B).map q
    have hmapXB : XB.map q = Xbar := by
      dsimp [XB]
      rw [Subgroup.map_comap_eq,
        MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective CB),
        top_inf_eq]
    rw [hmapXB, codisjoint_iff.mp hcompl.codisjoint,
      Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective CB)]
  have hTXB : T ⊔ X = B := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hTB, ← Subgroup.map_sup,
      hTBXB, ← MonoidHom.range_eq_map, B.range_subtype]
  have hSX : S ⊔ X = R := by
    calc
      S ⊔ X = S ⊔ (T ⊔ X) := by
        rw [← sup_assoc, sup_eq_left.mpr hTS]
      _ = S ⊔ B := by rw [hTXB]
      _ = B ⊔ S := sup_comm S B
      _ = R := hBS

  let OB : Subgroup G := (omegaOne p B).map B.subtype
  have hTOB : T ≤ OB := by
    intro t ht
    let tB : B := ⟨t, hTB ht⟩
    have htPow : tB ^ p = 1 := by
      apply Subtype.ext
      exact congrArg (fun z : T ↦ (z : G)) (hTpow ⟨t, ht⟩)
    exact ⟨tB, mem_omegaOne_of_pow_eq_one p htPow, rfl⟩
  have hOBB : OB ≤ B := Subgroup.map_subtype_le _
  let toR : B →* R :=
    { toFun := fun b ↦ ⟨b, hBR b.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  have hOBS : OB ≤ S := by
    rintro _ ⟨b, hb, rfl⟩
    have hbMap : toR b ∈ (omegaOne p B).map toR :=
      ⟨b, hb, rfl⟩
    have hbOmegaR : toR b ∈ omegaOne p R :=
      map_omegaOne_le p toR hbMap
    rw [← hOmega]
    exact ⟨toR b, hbOmegaR, rfl⟩
  have hOBR : OB ≤ R := hOBS.trans hSR
  have hOBp : IsPGroup p OB :=
    (hR.to_subgroup (OB.subgroupOf R)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hOBR)
  have hOB : OB = T := by
    by_contra hne
    have hTltOB : T < OB :=
      lt_of_le_of_ne hTOB (Ne.symm hne)
    obtain ⟨d, hOBcard⟩ := hOBp.exists_card_eq
    have hpowlt : p ^ 2 < p ^ d := by
      calc
        p ^ 2 = Nat.card T := hTcard.symm
        _ < Nat.card OB := natCard_subgroup_lt_of_lt hTltOB
        _ = p ^ d := hOBcard
    have hd : 3 ≤ d := by
      by_contra hd
      have hdle : d ≤ 2 := by omega
      exact (not_lt_of_ge
        (Nat.pow_le_pow_right (Fact.out : p.Prime).pos hdle)) hpowlt
    have hcardGe : Nat.card S ≤ Nat.card OB := by
      rw [hScard, hOBcard]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hd
    have hOSEq : OB = S :=
      Subgroup.eq_of_le_of_card_ge hOBS hcardGe
    apply hSnleB
    rw [← hOSEq]
    exact hOBB

  have hXR : X ≤ R := hXB.trans hBR
  have hXp : IsPGroup p X :=
    (hR.to_subgroup (X.subgroupOf R)).of_equiv
      (Subgroup.subgroupOfEquivOfLe hXR)
  have hXodd : Odd (Nat.card X) :=
    hoddR.of_dvd_nat (Subgroup.card_dvd_of_le hXR)
  have hXcyclic : IsCyclic X := by
    apply (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
      hXp hXodd).mpr
    rintro ⟨E, hE⟩
    let EG : Subgroup G := E.map X.subtype
    have hEGX : EG ≤ X := Subgroup.map_subtype_le E
    have hEGT : EG ≤ T := by
      rintro _ ⟨e, he, rfl⟩
      let eB : B := ⟨(e : X), hXB e.property⟩
      have hePow : eB ^ p = 1 := by
        apply Subtype.ext
        exact congrArg (fun z : E ↦ ((z : X) : G))
          (hE.pow_eq_one ⟨e, he⟩)
      have heOB : ((e : X) : G) ∈ OB :=
        ⟨eB, mem_omegaOne_of_pow_eq_one p hePow, rfl⟩
      rw [hOB] at heOB
      exact heOB
    have hEGC : EG ≤ C :=
      (show EG ≤ T ⊓ X from le_inf hEGT hEGX).trans hTXC
    have hEGOmegaC : EG ≤ (omegaOne p C).map C.subtype := by
      intro g hg
      have hgC := hEGC hg
      obtain ⟨e, he, heg⟩ := hg
      let eC : C := ⟨g, hgC⟩
      have hePow : eC ^ p = 1 := by
        apply Subtype.ext
        change g ^ p = 1
        rw [← heg]
        exact congrArg (fun z : E ↦ ((z : X) : G))
          (hE.pow_eq_one ⟨e, he⟩)
      exact ⟨eC, mem_omegaOne_of_pow_eq_one p hePow, rfl⟩
    have hOmegaCZ : (omegaOne p C).map C.subtype = Z := by
      simpa [C, Z] using hOmegaC
    have hEGZ : EG ≤ Z := hEGOmegaC.trans_eq hOmegaCZ
    have hEGcard : Nat.card EG = Nat.card E :=
      Subgroup.card_map_of_injective X.subtype_injective
    have hcardLe := Subgroup.card_le_of_le hEGZ
    rw [hEGcard, hE.card_eq, hZcard] at hcardLe
    exact (not_lt_of_ge hcardLe)
      (by
        rw [pow_two]
        exact lt_mul_of_one_lt_right (Fact.out : p.Prime).pos
          (Fact.out : p.Prime).one_lt)

  have hnotSA : ¬ ⁅S, A⁆ ≤ T := by
    intro hSA
    let QR := R ⧸ BR
    let qR : R →* QR := QuotientGroup.mk' BR
    let fR : A →* MulAut QR :=
      subgroupConjugationFactorHom B R A hAnormR hAnormB
    have hmapBR : BR.map qR = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    have hmapSR : SR.map qR = ⊤ := by
      have hmap := congrArg (Subgroup.map qR) hBRSR
      rw [Subgroup.map_sup, hmapBR, bot_sup_eq,
        Subgroup.map_top_of_surjective qR
          (QuotientGroup.mk'_surjective BR)] at hmap
      exact hmap
    have hkerTop : fR.ker = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro a
      rw [MonoidHom.mem_ker]
      apply MulEquiv.ext
      intro z
      obtain ⟨r, rfl⟩ := QuotientGroup.mk'_surjective BR z
      have hqr : qR r ∈ SR.map qR := by rw [hmapSR]; trivial
      obtain ⟨s, hsSR, hqs⟩ := hqr
      rw [← hqs]
      rw [subgroupConjugationFactorHom_apply_mk]
      have hsS : (s : G) ∈ S := hsSR
      have hcommT : ⁅(a : G), (s : G)⁆ ∈ T := by
        apply hSA
        rw [← Subgroup.commutator_comm A S]
        exact Subgroup.commutator_mem_commutator a.property hsS
      let cR : R := ⟨⁅(a : G), (s : G)⁆, hTR hcommT⟩
      let sR : R := ⟨s, hSR hsS⟩
      have hsReq : sR = s := rfl
      have hconj :
          (⟨(a : G) * (s : G) * (a : G)⁻¹,
            (hAnormR a.property s).mp s.property⟩ : R) = cR * sR := by
        apply Subtype.ext
        exact _root_.conj_eq_commutatorElement_mul
      rw [hconj, map_mul,
        show qR cR = 1 from
          (QuotientGroup.eq_one_iff cR).mpr (hTB hcommT),
        one_mul, hsReq]
      simp
      rfl
    have hARleB : ⁅A, R⁆ ≤ B :=
      (subgroupConjugationFactorHom_ker_eq_top_iff
        B R A hAnormR hAnormB).mp hkerTop
    have hRAleB : ⁅R, A⁆ ≤ B := by
      rw [Subgroup.commutator_comm]
      exact hARleB
    apply hSnleB
    exact hSR.trans (hperfect ▸ hRAleB)

  have hRnormZ : R ≤ Subgroup.normalizer (Z : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro r hr z hz
    exact characteristic_map_subtype_invariant_under_normalizer
      S R (_root_.commutator S) hRnormS r hr z hz
  have hZcenter : Z = centerWithin S := by
    dsimp [Z]
    rw [hS.toIsSpecial.commutator_eq_center,
      map_center_eq_centerWithin]

  let TS : Subgroup S := T.subgroupOf S
  have hTSnormal : TS.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hSR.trans hRnormT)
  letI : TS.Normal := hTSnormal
  have hTScard : Nat.card TS = p ^ 2 := by
    rw [natCard_subgroupOf_eq hTS, hTcard]
  have hTSindex : TS.index = p := by
    have hmul : TS.index * p ^ 2 = p * p ^ 2 := by
      calc
        TS.index * p ^ 2 = TS.index * Nat.card TS := by rw [hTScard]
        _ = Nat.card S := TS.index_mul_card
        _ = p ^ 3 := hScard
        _ = p * p ^ 2 := by simp [pow_succ, Nat.mul_comm]
    exact Nat.mul_right_cancel (pow_pos (Fact.out : p.Prime).pos 2) hmul
  let ST := S ⧸ TS
  have hSTcard : Nat.card ST = p := by
    rw [← TS.index_eq_card]
    exact hTSindex
  letI : IsCyclic ST := isCyclic_of_prime_card hSTcard

  let ZT : Subgroup T := Z.subgroupOf T
  have hZTnormal : ZT.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hTR.trans hRnormZ)
  letI : ZT.Normal := hZTnormal
  have hZTcard : Nat.card ZT = p := by
    rw [natCard_subgroupOf_eq hZT, hZcard]
  have hZTindex : ZT.index = p := by
    have hmul : ZT.index * p = p * p := by
      calc
        ZT.index * p = ZT.index * Nat.card ZT := by rw [hZTcard]
        _ = Nat.card T := ZT.index_mul_card
        _ = p ^ 2 := hTcard
        _ = p * p := by rw [pow_two]
    exact Nat.mul_right_cancel (Fact.out : p.Prime).pos hmul
  let TZ := T ⧸ ZT
  have hTZcard : Nat.card TZ = p := by
    rw [← ZT.index_eq_card]
    exact hZTindex
  letI : IsCyclic TZ := isCyclic_of_prime_card hTZcard

  let fST : A →* MulAut ST :=
    subgroupConjugationFactorHom T S A hAnormS hAnormT
  have hfSTne : fST.ker ≠ ⊤ := by
    intro htop
    have hAS : ⁅A, S⁆ ≤ T :=
      (subgroupConjugationFactorHom_ker_eq_top_iff
        T S A hAnormS hAnormT).mp htop
    apply hnotSA
    rw [Subgroup.commutator_comm]
    exact hAS
  obtain ⟨a, _haTop, ha⟩ := SetLike.exists_of_lt
    (lt_top_iff_ne_top.mpr hfSTne)

  obtain ⟨y, hy⟩ :=
    exists_zpowers_sup_eq_top_of_quotient_isCyclic TS
  let qST : S →* ST := QuotientGroup.mk' TS
  have hmapTS : TS.map qST = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hybarTop : Subgroup.zpowers (qST y) = ⊤ := by
    have hmap := congrArg (Subgroup.map qST) hy
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hmapTS, sup_bot_eq,
      Subgroup.map_top_of_surjective qST
        (QuotientGroup.mk'_surjective TS)] at hmap
    exact hmap
  have hygen : ∀ w : ST, w ∈ Subgroup.zpowers (qST y) := by
    intro w
    rw [hybarTop]
    trivial
  have hSy : Subgroup.zpowers (y : G) ⊔ T = S := by
    have hmap := congrArg (Subgroup.map S.subtype) hy
    rw [Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hTS,
      ← MonoidHom.range_eq_map, S.range_subtype] at hmap
    exact hmap

  obtain ⟨z, hz⟩ :=
    exists_zpowers_sup_eq_top_of_quotient_isCyclic ZT
  let qTZ : T →* TZ := QuotientGroup.mk' ZT
  have hmapZT : ZT.map qTZ = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  have hzbarTop : Subgroup.zpowers (qTZ z) = ⊤ := by
    have hmap := congrArg (Subgroup.map qTZ) hz
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, hmapZT, sup_bot_eq,
      Subgroup.map_top_of_surjective qTZ
        (QuotientGroup.mk'_surjective ZT)] at hmap
    exact hmap
  have hzgen : ∀ w : TZ, w ∈ Subgroup.zpowers (qTZ z) := by
    intro w
    rw [hzbarTop]
    trivial
  have hTz : Subgroup.zpowers (z : G) ⊔ Z = T := by
    have hmap := congrArg (Subgroup.map T.subtype) hz
    rw [Subgroup.map_sup, MonoidHom.map_zpowers,
      Subgroup.map_subgroupOf_eq_of_le hZT,
      ← MonoidHom.range_eq_map, T.range_subtype] at hmap
    exact hmap

  let fTZ : A →* MulAut TZ :=
    subgroupConjugationFactorHom Z T A hAnormT hAnormZ
  letI : IsCyclic X := hXcyclic
  obtain ⟨x, hxgen⟩ := IsCyclic.exists_generator (α := X)
  let xa : X :=
    ⟨(a : G) * (x : G) * (a : G)⁻¹,
      (hAX a.property x).mp x.property⟩
  have hxaPow : xa ∈ Submonoid.powers x :=
    mem_powers_iff_mem_zpowers.mpr (hxgen xa)
  obtain ⟨i, hi⟩ := hxaPow
  have hyActPow : fST a (qST y) ∈ Submonoid.powers (qST y) :=
    mem_powers_iff_mem_zpowers.mpr (hygen (fST a (qST y)))
  obtain ⟨j, hj⟩ := hyActPow
  have hzActPow : fTZ a (qTZ z) ∈ Submonoid.powers (qTZ z) :=
    mem_powers_iff_mem_zpowers.mpr (hzgen (fTZ a (qTZ z)))
  obtain ⟨k, hk⟩ := hzActPow

  let ZR : Subgroup R := Z.subgroupOf R
  have hZRnormal : ZR.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hRnormZ
  letI : ZR.Normal := hZRnormal
  let RZ := R ⧸ ZR
  let qRZ : R →* RZ := QuotientGroup.mk' ZR
  have hRZp : IsPGroup p RZ := hR.to_quotient ZR
  let tR : T →* R :=
    { toFun := fun t ↦ ⟨t, hTR t.property⟩
      map_one' := rfl
      map_mul' := fun _ _ ↦ rfl }
  let gT : T →* RZ := qRZ.comp tR
  have hkergT : gT.ker = ZT := by
    ext t
    change qRZ (tR t) = 1 ↔ (t : G) ∈ Z
    constructor
    · intro ht
      exact (QuotientGroup.eq_one_iff (tR t)).mp ht
    · intro ht
      exact (QuotientGroup.eq_one_iff (tR t)).mpr ht
  let E : Subgroup RZ := gT.range
  have hEcard : Nat.card E = p := by
    calc
      Nat.card E = Nat.card (T ⧸ gT.ker) :=
        Nat.card_congr
          (QuotientGroup.quotientKerEquivRange gT).symm.toEquiv
      _ = Nat.card TZ := by rw [hkergT]
      _ = p := hTZcard
  have hTRnormal : TR.Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hRnormT
  have hEeq : E = TR.map qRZ := by
    ext w
    constructor
    · rintro ⟨t, rfl⟩
      exact ⟨tR t, t.property, rfl⟩
    · rintro ⟨r, hr, rfl⟩
      let t : T := ⟨r, hr⟩
      exact ⟨t, rfl⟩
  have hEnormal : E.Normal := by
    rw [hEeq]
    exact Subgroup.Normal.map hTRnormal qRZ
      (QuotientGroup.mk'_surjective ZR)
  letI : E.Normal := hEnormal
  have hEcenter : E ≤ Subgroup.center RZ :=
    normal_le_center_of_card_eq_prime
      (Fact.out : p.Prime) hRZp E hEcard

  let XR : Subgroup R := X.subgroupOf R
  have hSRXR : SR ⊔ XR = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hSR hXR, hSX,
      Subgroup.subgroupOf_self]
  have hnotXS : ¬ ⁅X, S⁆ ≤ Z := by
    intro hXS
    have hSSZR : ⁅SR, SR⁆ ≤ ZR := by
      intro c hc
      change ((c : R) : G) ∈ Z
      have hc' : ((c : R) : G) ∈ ⁅S, S⁆ := by
        have hcmap : R.subtype c ∈ Subgroup.map R.subtype ⁅SR, SR⁆ :=
          ⟨c, hc, rfl⟩
        rw [Subgroup.map_commutator,
          Subgroup.map_subgroupOf_eq_of_le hSR] at hcmap
        exact hcmap
      change ((c : R) : G) ∈
        (_root_.commutator S).map S.subtype
      rw [S.map_subtype_commutator]
      exact hc'
    have hSXRZR : ⁅SR, XR⁆ ≤ ZR := by
      intro c hc
      change ((c : R) : G) ∈ Z
      have hc' : ((c : R) : G) ∈ ⁅S, X⁆ := by
        have hcmap : R.subtype c ∈ Subgroup.map R.subtype ⁅SR, XR⁆ :=
          ⟨c, hc, rfl⟩
        rw [Subgroup.map_commutator,
          Subgroup.map_subgroupOf_eq_of_le hSR,
          Subgroup.map_subgroupOf_eq_of_le hXR] at hcmap
        exact hcmap
      apply hXS
      rw [Subgroup.commutator_comm]
      exact hc'
    have hbound : ⁅SR, SR ⊔ XR⁆ ≤ ZR :=
      commutator_sup_le_of_normal hSSZR hSXRZR
    rw [hSRXR] at hbound
    apply hnoncritical
    intro t ht
    let r : R := ⟨t, hTR ht⟩
    let tR' : TR := ⟨r, ht⟩
    have htZR : (tR' : R) ∈ ZR := by
      exact hbound (hcommSR.symm.le tR'.property)
    exact htZR

  let ya : S :=
    ⟨(a : G) * (y : G) * (a : G)⁻¹,
      (hAnormS a.property y).mp y.property⟩
  have hyaAction : fST a (qST y) = qST ya := by
    exact subgroupConjugationFactorHom_apply_mk
      T S A hAnormS hAnormT a y
  let u : S := y ^ j * ya⁻¹
  have huT : (u : G) ∈ T := by
    change u ∈ TS
    apply (QuotientGroup.eq_one_iff u).mp
    change qST (y ^ j * ya⁻¹) = 1
    rw [map_mul, map_pow, map_inv, ← hyaAction,
      show qST y ^ j = fST a (qST y) by simpa using hj]
    simp
  have hyj : (y : G) ^ j = (u : G) * (ya : G) := by
    dsimp [u]
    simp

  let za : T :=
    ⟨(a : G) * (z : G) * (a : G)⁻¹,
      (hAnormT a.property z).mp z.property⟩
  have hzaAction : fTZ a (qTZ z) = qTZ za := by
    exact subgroupConjugationFactorHom_apply_mk
      Z T A hAnormT hAnormZ a z
  let v : T := z ^ k * za⁻¹
  have hvZ : (v : G) ∈ Z := by
    change v ∈ ZT
    apply (QuotientGroup.eq_one_iff v).mp
    change qTZ (z ^ k * za⁻¹) = 1
    rw [map_mul, map_pow, map_inv, ← hzaAction,
      show qTZ z ^ k = fTZ a (qTZ z) by simpa using hk]
    simp
  have hzk : (z : G) ^ k = (v : G) * (za : G) := by
    dsimp [v]
    simp

  have hyzZ : ⁅(y : G), (z : G)⁆ ∈ Z := by
    change ⁅(y : G), (z : G)⁆ ∈
      (_root_.commutator S).map S.subtype
    rw [S.map_subtype_commutator]
    exact Subgroup.commutator_mem_commutator y.property (hTS z.property)
  have hyzNe : ⁅(y : G), (z : G)⁆ ≠ 1 := by
    intro hyzOne
    have hyzComm : (y : G) * (z : G) = (z : G) * (y : G) :=
      commutatorElement_eq_one_iff_mul_comm.mp hyzOne
    have hTcenty : T ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
      rw [← hTz]
      apply sup_le
      · rw [Subgroup.zpowers_le,
          Subgroup.mem_centralizer_singleton_iff]
        exact hyzComm.symm
      · intro c hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hcCenter : c ∈ centerWithin S := by
          rw [← hZcenter]
          exact hc
        exact (Subgroup.mem_centralizer_iff.mp hcCenter.2
          (y : G) y.property).symm
    have hyCentT : (y : G) ∈ Subgroup.centralizer (T : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact (Subgroup.mem_centralizer_iff.mp (hTcenty ht)
        (y : G) (by simp)).symm
    have hyB : (y : G) ∈ B := ⟨hSR y.property, hyCentT⟩
    apply hSnleB
    rw [← hSy]
    apply sup_le
    · rw [Subgroup.zpowers_le]
      exact hyB
    · exact hTB

  have hxyNotZ : ⁅(x : G), (y : G)⁆ ∉ Z := by
    intro hxyZ
    let xR : R := ⟨x, hXR x.property⟩
    let yR : R := ⟨y, hSR y.property⟩
    have hyR : Subgroup.zpowers (y : G) ≤ R :=
      Subgroup.zpowers_le.mpr (hSR y.property)
    let YR : Subgroup R := (Subgroup.zpowers (y : G)).subgroupOf R
    have hXRcyc : Subgroup.zpowers xR = XR := by
      apply le_antisymm
      · exact Subgroup.zpowers_le.mpr x.property
      · intro r hr
        have hr' := hxgen (⟨r, hr⟩ : X)
        rw [Subgroup.mem_zpowers_iff] at hr' ⊢
        obtain ⟨n, hn⟩ := hr'
        exact ⟨n, Subtype.ext (congrArg (fun z : X ↦ (z : G)) hn)⟩
    have hYRcyc : Subgroup.zpowers yR = YR := by
      apply le_antisymm
      · exact Subgroup.zpowers_le.mpr (Subgroup.mem_zpowers (y : G))
      · intro r hr
        change ((r : R) : G) ∈ Subgroup.zpowers (y : G) at hr
        rw [Subgroup.mem_zpowers_iff] at hr ⊢
        obtain ⟨n, hn⟩ := hr
        exact ⟨n, Subtype.ext hn⟩
    have hqxyOne : ⁅qRZ xR, qRZ yR⁆ = 1 := by
      rw [← map_commutatorElement]
      exact (QuotientGroup.eq_one_iff ⁅xR, yR⁆).mpr hxyZ
    have hqxy : Commute (qRZ xR) (qRZ yR) :=
      commutatorElement_eq_one_iff_mul_comm.mp hqxyOne
    have hqbot : ⁅XR.map qRZ, YR.map qRZ⁆ = ⊥ := by
      rw [← hXRcyc, ← hYRcyc,
        MonoidHom.map_zpowers, MonoidHom.map_zpowers,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro u hu
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      change v ∈ Subgroup.zpowers (qRZ yR) at hv
      rw [Subgroup.mem_zpowers_iff] at hu hv
      obtain ⟨m, rfl⟩ := hu
      obtain ⟨n, rfl⟩ := hv
      exact (hqxy.zpow_zpow m n).eq.symm
    have hXRYR : ⁅XR, YR⁆ ≤ ZR := by
      rw [← QuotientGroup.ker_mk' ZR,
        ← Subgroup.map_eq_bot_iff,
        Subgroup.map_commutator]
      exact hqbot
    have hXRTRbot : ⁅XR, TR⁆ = ⊥ := by
      apply Subgroup.map_injective R.subtype_injective
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le hXR,
        Subgroup.map_subgroupOf_eq_of_le hTR,
        Subgroup.map_bot,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hXB.trans hBcentT
    have hXRTR : ⁅XR, TR⁆ ≤ ZR := by
      rw [hXRTRbot]
      exact bot_le
    have hYRTR : YR ⊔ TR = SR := by
      rw [← Subgroup.subgroupOf_sup hyR hTR, hSy]
    have hXRSR : ⁅XR, SR⁆ ≤ ZR := by
      rw [← hYRTR]
      exact commutator_sup_le_of_normal hXRYR hXRTR
    apply hnotXS
    intro c hc
    have hcmap : c ∈ ⁅XR, SR⁆.map R.subtype := by
      rw [Subgroup.map_commutator,
        Subgroup.map_subgroupOf_eq_of_le hXR,
        Subgroup.map_subgroupOf_eq_of_le hSR]
      exact hc
    obtain ⟨r, hr, rfl⟩ := hcmap
    exact hXRSR hr

  let yzZ : Z := ⟨⁅(y : G), (z : G)⁆, hyzZ⟩
  have hyzOrder : orderOf ⁅(y : G), (z : G)⁆ = p := by
    have hdvd : orderOf yzZ ∣ p := by
      have := orderOf_dvd_natCard yzZ
      rwa [hZcard] at this
    have hneOne : orderOf yzZ ≠ 1 := by
      intro hone
      apply hyzNe
      have hyzOne : yzZ = 1 := orderOf_eq_one_iff.mp hone
      exact congrArg (fun c : Z ↦ (c : G)) hyzOne
    have heq : orderOf yzZ = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd).resolve_left hneOne
    exact (Subgroup.orderOf_coe yzZ).trans heq

  have hSclass2 : _root_.commutator S ≤ Subgroup.center S :=
    hS.toIsSpecial.commutator_eq_center.le
  let zS : S := ⟨z, hTS z.property⟩
  let vS : S := ⟨v, hTS v.property⟩
  let zaS : S := ⟨za, hTS za.property⟩
  let uT : T := ⟨u, huT⟩
  letI : IsMulCommutative T := hTcomm
  have huvza : Commute u (vS * zaS) := by
    rw [Commute]
    apply Subtype.ext
    change (uT : G) * ((v * za : T) : G) =
      ((v * za : T) : G) * (uT : G)
    exact congrArg (fun t : T ↦ (t : G)) (mul_comm uT (v * za))
  have hvCenter : (v : G) ∈ centerWithin S := by
    rw [← hZcenter]
    exact hvZ
  have hyav : Commute ya vS := by
    rw [Commute]
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hvCenter.2
      (ya : G) ya.property
  have hcorrS : ⁅u * ya, vS * zaS⁆ = ⁅ya, zaS⁆ := by
    calc
      ⁅u * ya, vS * zaS⁆ =
          ⁅u, vS * zaS⁆ * ⁅ya, vS * zaS⁆ :=
        commutatorElement_mul_left_of_commutator_le
          hSclass2 u ya (vS * zaS)
      _ = ⁅ya, vS * zaS⁆ := by rw [huvza.commutator_eq, one_mul]
      _ = ⁅ya, vS⁆ * ⁅ya, zaS⁆ :=
        commutatorElement_mul_right_of_commutator_le
          hSclass2 ya vS zaS
      _ = ⁅ya, zaS⁆ := by rw [hyav.commutator_eq, one_mul]
  have hpowCommG :
      ⁅(y : G) ^ j, (z : G) ^ k⁆ =
        ⁅(y : G), (z : G)⁆ ^ (j * k) := by
    have h := congrArg S.subtype
      (commutatorElement_pow_pow_of_commutator_le
        hSclass2 y zS j k)
    simp only [map_commutatorElement, map_pow] at h
    change ⁅(y : G) ^ j, (z : G) ^ k⁆ =
      ⁅(y : G), (z : G)⁆ ^ (j * k) at h
    exact h
  have hcorrG :
      ⁅(u : G) * (ya : G), (v : G) * (za : G)⁆ =
        ⁅(ya : G), (za : G)⁆ := by
    have h := congrArg S.subtype hcorrS
    simp only [map_commutatorElement, map_mul] at h
    change ⁅(u : G) * (ya : G), (v : G) * (za : G)⁆ =
      ⁅(ya : G), (za : G)⁆ at h
    exact h
  have hxiG : (x : G) ^ i =
      (a : G) * (x : G) * (a : G)⁻¹ := by
    simpa using congrArg (fun w : X ↦ (w : G)) hi
  have hyzCenter : ⁅(y : G), (z : G)⁆ ∈ centerWithin S := by
    rw [← hZcenter]
    exact hyzZ
  let yzX : X :=
    ⟨⁅(y : G), (z : G)⁆,
      hCX ⟨hZR hyzZ, hyzCenter.2⟩⟩
  have hyzPow : yzX ∈ Submonoid.powers x :=
    mem_powers_iff_mem_zpowers.mpr (hxgen yzX)
  obtain ⟨m, hm⟩ := hyzPow
  have hxmG : (x : G) ^ m = ⁅(y : G), (z : G)⁆ := by
    simpa using congrArg (fun w : X ↦ (w : G)) hm
  have hyzConj :
      (a : G) * ⁅(y : G), (z : G)⁆ * (a : G)⁻¹ =
        ⁅(y : G), (z : G)⁆ ^ i := by
    calc
      (a : G) * ⁅(y : G), (z : G)⁆ * (a : G)⁻¹ =
          (a : G) * (x : G) ^ m * (a : G)⁻¹ := by rw [hxmG]
      _ = ((a : G) * (x : G) * (a : G)⁻¹) ^ m :=
        conj_pow.symm
      _ = ((x : G) ^ i) ^ m := by rw [hxiG]
      _ = (x : G) ^ (i * m) := (pow_mul (x : G) i m).symm
      _ = (x : G) ^ (m * i) := by rw [Nat.mul_comm]
      _ = ((x : G) ^ m) ^ i := pow_mul (x : G) m i
      _ = ⁅(y : G), (z : G)⁆ ^ i := by rw [hxmG]
  have hyzPowEq :
      ⁅(y : G), (z : G)⁆ ^ (j * k) =
        ⁅(y : G), (z : G)⁆ ^ i := by
    calc
      ⁅(y : G), (z : G)⁆ ^ (j * k) =
          ⁅(y : G) ^ j, (z : G) ^ k⁆ := hpowCommG.symm
      _ = ⁅(u : G) * (ya : G), (v : G) * (za : G)⁆ := by
        rw [hyj, hzk]
      _ = ⁅(ya : G), (za : G)⁆ := hcorrG
      _ = (a : G) * ⁅(y : G), (z : G)⁆ * (a : G)⁻¹ :=
        (conjugate_commutatorElement
          (y : G) (z : G) (a : G)).symm
      _ = ⁅(y : G), (z : G)⁆ ^ i := hyzConj
  have hjk : j * k ≡ i [MOD p] := by
    rw [← hyzOrder]
    exact pow_eq_pow_iff_modEq.mp hyzPowEq

  let xR : R := ⟨x, hXR x.property⟩
  let yR : R := ⟨y, hSR y.property⟩
  let xaR : R := ⟨xa, hXR xa.property⟩
  let yaR : R := ⟨ya, hSR ya.property⟩
  let uR : R := ⟨u, hTR huT⟩
  have hyxT : ⁅(y : G), (x : G)⁆ ∈ T := by
    apply hSBleT
    exact Subgroup.commutator_mem_commutator y.property (hXB x.property)
  have hxyT : ⁅(x : G), (y : G)⁆ ∈ T := by
    have hinv : ⁅(y : G), (x : G)⁆⁻¹ =
        ⁅(x : G), (y : G)⁆ :=
      commutatorElement_inv (y : G) (x : G)
    exact hinv ▸ T.inv_mem hyxT
  let xyT : T := ⟨⁅(x : G), (y : G)⁆, hxyT⟩
  let w : RZ := ⁅qRZ xR, qRZ yR⁆
  have hwE : w ∈ E := by
    refine ⟨xyT, ?_⟩
    change qRZ (tR xyT) = ⁅qRZ xR, qRZ yR⁆
    rw [← map_commutatorElement]
    rfl
  have hwNe : w ≠ 1 := by
    intro hwOne
    apply hxyNotZ
    have hqOne : qRZ ⁅xR, yR⁆ = 1 := by
      rw [map_commutatorElement]
      exact hwOne
    exact (QuotientGroup.eq_one_iff ⁅xR, yR⁆).mp hqOne
  let wE : E := ⟨w, hwE⟩
  have hwOrder : orderOf w = p := by
    have hdvd : orderOf wE ∣ p := by
      have := orderOf_dvd_natCard wE
      rwa [hEcard] at this
    have hneOne : orderOf wE ≠ 1 := by
      intro hone
      apply hwNe
      have hwOne : wE = 1 := orderOf_eq_one_iff.mp hone
      exact congrArg (fun e : E ↦ (e : RZ)) hwOne
    have heq : orderOf wE = p :=
      ((Nat.dvd_prime (Fact.out : p.Prime)).mp hdvd).resolve_left hneOne
    exact (Subgroup.orderOf_coe wE).trans heq
  have hwCenter : w ∈ Subgroup.center RZ := hEcenter hwE
  have hxw : Commute (qRZ xR) w := by
    change qRZ xR * w = w * qRZ xR
    exact Subgroup.mem_center_iff.mp hwCenter (qRZ xR)
  have hyw : Commute (qRZ yR) w := by
    change qRZ yR * w = w * qRZ yR
    exact Subgroup.mem_center_iff.mp hwCenter (qRZ yR)
  have hpowW :
      ⁅(qRZ xR) ^ i, (qRZ yR) ^ j⁆ = w ^ (i * j) := by
    exact commutatorElement_pow_pow_of_commute
      (qRZ xR) (qRZ yR) hxw hyw i j

  have hZTker : ZT ≤ gT.ker := by rw [hkergT]
  let eTZ : TZ →* RZ := QuotientGroup.lift ZT gT hZTker
  have heTZ (t : T) : eTZ (qTZ t) = gT t := by
    exact QuotientGroup.lift_mk ZT hZTker t
  have hxyTZPow : qTZ xyT ∈ Submonoid.powers (qTZ z) :=
    mem_powers_iff_mem_zpowers.mpr (hzgen (qTZ xyT))
  obtain ⟨nxy, hnxy⟩ := hxyTZPow
  have hnxy' : (qTZ z) ^ nxy = qTZ xyT := by simpa using hnxy
  have hgTzxy : (gT z) ^ nxy = gT xyT := by
    have hh := congrArg eTZ hnxy'
    rw [map_pow, heTZ, heTZ] at hh
    exact hh
  have hwgTxy : w = gT xyT := by
    change ⁅qRZ xR, qRZ yR⁆ = qRZ (tR xyT)
    rw [← map_commutatorElement]
    rfl
  have hwz : w = (gT z) ^ nxy := hwgTxy.trans hgTzxy.symm
  have hzkTZ : (qTZ z) ^ k = qTZ za := by
    calc
      (qTZ z) ^ k = fTZ a (qTZ z) := by simpa using hk
      _ = qTZ za := hzaAction
  have hgTzk : (gT z) ^ k = gT za := by
    have hh := congrArg eTZ hzkTZ
    rw [map_pow, heTZ, heTZ] at hh
    exact hh

  let fRZ : A →* MulAut RZ :=
    subgroupConjugationFactorHom Z R A hAnormR hAnormZ
  have hactX : fRZ a (qRZ xR) = qRZ xaR := by
    change subgroupConjugationFactorHom Z R A hAnormR hAnormZ a
        (QuotientGroup.mk' (Z.subgroupOf R) xR) =
      QuotientGroup.mk' (Z.subgroupOf R) xaR
    rw [subgroupConjugationFactorHom_apply_mk]
  have hactY : fRZ a (qRZ yR) = qRZ yaR := by
    change subgroupConjugationFactorHom Z R A hAnormR hAnormZ a
        (QuotientGroup.mk' (Z.subgroupOf R) yR) =
      QuotientGroup.mk' (Z.subgroupOf R) yaR
    rw [subgroupConjugationFactorHom_apply_mk]
  have hxRpow : xR ^ i = xaR := by
    apply Subtype.ext
    exact hxiG
  have hyRpow : yR ^ j = uR * yaR := by
    apply Subtype.ext
    exact hyj
  have hqxPow : (qRZ xR) ^ i = fRZ a (qRZ xR) := by
    rw [← map_pow, hxRpow, hactX]
  have hqyPow :
      (qRZ yR) ^ j = qRZ uR * fRZ a (qRZ yR) := by
    rw [← map_pow, hyRpow, map_mul, hactY]
  have huE : qRZ uR ∈ E := by
    refine ⟨uT, ?_⟩
    rfl
  have huCenter : qRZ uR ∈ Subgroup.center RZ := hEcenter huE
  have huComm (r : RZ) : Commute r (qRZ uR) := by
    change r * qRZ uR = qRZ uR * r
    exact Subgroup.mem_center_iff.mp huCenter r
  have hcommAct :
      ⁅(qRZ xR) ^ i, (qRZ yR) ^ j⁆ = fRZ a w := by
    rw [hqxPow, hqyPow]
    calc
      ⁅fRZ a (qRZ xR), qRZ uR * fRZ a (qRZ yR)⁆ =
          ⁅fRZ a (qRZ xR), qRZ uR⁆ * qRZ uR *
            ⁅fRZ a (qRZ xR), fRZ a (qRZ yR)⁆ *
              (qRZ uR)⁻¹ :=
        _root_.commutatorElement_mul_right_eq_mul_conj
          (fRZ a (qRZ xR)) (qRZ uR) (fRZ a (qRZ yR))
      _ = qRZ uR *
            ⁅fRZ a (qRZ xR), fRZ a (qRZ yR)⁆ *
              (qRZ uR)⁻¹ := by
        rw [(huComm (fRZ a (qRZ xR))).commutator_eq, one_mul]
      _ = ⁅fRZ a (qRZ xR), fRZ a (qRZ yR)⁆ := by
        have hc := (huComm
          ⁅fRZ a (qRZ xR), fRZ a (qRZ yR)⁆).eq
        rw [← hc]
        group
      _ = fRZ a w := by
        exact (map_commutatorElement (fRZ a)
          (qRZ xR) (qRZ yR)).symm
  have hactZ : fRZ a (gT z) = gT za := by
    change subgroupConjugationFactorHom Z R A hAnormR hAnormZ a
        (QuotientGroup.mk' (Z.subgroupOf R) (tR z)) =
      QuotientGroup.mk' (Z.subgroupOf R) (tR za)
    rw [subgroupConjugationFactorHom_apply_mk]
    apply congrArg (QuotientGroup.mk' (Z.subgroupOf R))
    apply Subtype.ext
    rfl
  have hactW : fRZ a w = w ^ k := by
    calc
      fRZ a w = fRZ a ((gT z) ^ nxy) := by rw [hwz]
      _ = (fRZ a (gT z)) ^ nxy := map_pow (fRZ a) (gT z) nxy
      _ = (gT za) ^ nxy := by rw [hactZ]
      _ = ((gT z) ^ k) ^ nxy := by rw [hgTzk]
      _ = (gT z) ^ (k * nxy) :=
        (pow_mul (gT z) k nxy).symm
      _ = (gT z) ^ (nxy * k) := by rw [Nat.mul_comm]
      _ = ((gT z) ^ nxy) ^ k := pow_mul (gT z) nxy k
      _ = w ^ k := by rw [← hwz]
  have hpowWEq : w ^ (i * j) = w ^ k :=
    hpowW.symm.trans (hcommAct.trans hactW)
  have hij : i * j ≡ k [MOD p] := by
    rw [← hwOrder]
    exact pow_eq_pow_iff_modEq.mp hpowWEq

  have horderX : orderOf x = Nat.card X :=
    orderOf_eq_card_of_forall_mem_zpowers hxgen
  have hsemixa : SemiconjBy (a : G) (x : G) (xa : G) := by
    change (a : G) * (x : G) = (xa : G) * (a : G)
    dsimp [xa]
    group
  have horderXa : orderOf xa = orderOf x := by
    calc
      orderOf xa = orderOf (xa : G) := (Subgroup.orderOf_coe xa).symm
      _ = orderOf (x : G) :=
        (SemiconjBy.orderOf_eq (a : G) hsemixa).symm
      _ = orderOf x := Subgroup.orderOf_coe x
  have hxaTop : Subgroup.zpowers xa = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, horderXa, horderX]
  have hxXaPow : x ∈ Submonoid.powers xa := by
    apply mem_powers_iff_mem_zpowers.mpr
    rw [hxaTop]
    trivial
  obtain ⟨l, hl⟩ := hxXaPow
  have hxiX : x ^ i = xa := by simpa using hi
  have hilPow : x ^ (i * l) = x ^ 1 := by
    calc
      x ^ (i * l) = (x ^ i) ^ l := pow_mul x i l
      _ = xa ^ l := by rw [hxiX]
      _ = x := by simpa using hl
      _ = x ^ 1 := by simp
  have hilOrder : i * l ≡ 1 [MOD orderOf x] :=
    pow_eq_pow_iff_modEq.mp hilPow
  have hZC : Z ≤ C := by
    intro c hc
    have hcCenter : c ∈ centerWithin S := by
      rw [← hZcenter]
      exact hc
    exact ⟨hZR hc, hcCenter.2⟩
  have hpOrderX : p ∣ orderOf x := by
    rw [horderX, ← hZcard]
    exact Subgroup.card_dvd_of_le (hZC.trans hCX)
  have hil : i * l ≡ 1 [MOD p] := hilOrder.of_dvd hpOrderX

  have hjsq : j ^ 2 ≡ 1 [MOD p] := by
    have hpre : i * (j ^ 2) ≡ i [MOD p] := by
      calc
        i * (j ^ 2) = (i * j) * j := by simp [pow_two, Nat.mul_assoc]
        _ ≡ k * j [MOD p] := hij.mul_right j
        _ = j * k := Nat.mul_comm _ _
        _ ≡ i [MOD p] := hjk
    have hli : l * i ≡ 1 [MOD p] := by
      simpa [Nat.mul_comm] using hil
    calc
      j ^ 2 = 1 * (j ^ 2) := by simp
      _ ≡ (l * i) * (j ^ 2) [MOD p] :=
        (hli.mul_right (j ^ 2)).symm
      _ = l * (i * (j ^ 2)) := by rw [Nat.mul_assoc]
      _ ≡ l * i [MOD p] := hpre.mul_left l
      _ ≡ 1 [MOD p] := hli
  have hybarOrder : orderOf (qST y) = p := by
    rw [orderOf_eq_card_of_zpowers_eq_top hybarTop, hSTcard]
  have ha2gen : fST (a ^ 2) (qST y) = qST y := by
    calc
      fST (a ^ 2) (qST y) = (qST y) ^ (j ^ 2) := by
        calc
          fST (a ^ 2) (qST y) = fST a (fST a (qST y)) := by
            simp [pow_two]
          _ = fST a ((qST y) ^ j) := congrArg (fST a) hj.symm
          _ = (fST a (qST y)) ^ j := map_pow (fST a) (qST y) j
          _ = ((qST y) ^ j) ^ j :=
            congrArg (fun w : ST ↦ w ^ j) hj.symm
          _ = (qST y) ^ (j * j) := (pow_mul (qST y) j j).symm
          _ = (qST y) ^ (j ^ 2) := by rw [pow_two]
      _ = (qST y) ^ 1 := by
        rw [pow_eq_pow_iff_modEq, hybarOrder]
        exact hjsq
      _ = qST y := pow_one _
  have hfa2 : fST (a ^ 2) = 1 := by
    apply MulEquiv.ext
    intro w
    change fST (a ^ 2) w = w
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hygen w)
    rw [← hn, map_zpow, ha2gen]
  obtain ⟨n, han⟩ := exists_eq_sq_pow_of_odd_natCard hoddA a
  apply ha
  rw [MonoidHom.mem_ker, han, map_pow, hfa2, one_pow]

end

end Submission.OddOrder.BG.Section04
