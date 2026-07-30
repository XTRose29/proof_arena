import Submission.OddOrder.BG.Section04.ExponentOmegaOneRankTwo
import Submission.OddOrder.MathlibSupport.CentralizerConjugationFixedPoint
import Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent
import Submission.OddOrder.MathlibSupport.ExtraspecialCenterFaithfulness
import Submission.OddOrder.MathlibSupport.ExtraspecialQuotient
import Submission.OddOrder.MathlibSupport.InvariantSubgroupAction
import Submission.OddOrder.MathlibSupport.OddPGroupOmegaAction
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal
import Submission.OddOrder.MathlibSupport.OmegaOneSmallNilpotency
import Submission.OddOrder.MathlibSupport.PrimeDivisorSquareSubOne
import Submission.OddOrder.MathlibSupport.PrimeOrderCentralizer
import Submission.OddOrder.MathlibSupport.PrimeOrderElementaryAbelianAction
import Mathlib.GroupTheory.SemidirectProduct

/-!
Bender--Glauberman Lemmas 4.13 and 4.14.

The numerical `p`-rank bound is expressed, as in the preceding files, by
the absence of an elementary abelian subgroup of rank three.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

noncomputable section

universe u v

private theorem natCard_le_prime_sq_of_elementaryAbelian_no_rank_three
    {E : Type u} [Group E] [Finite E]
    {p : ℕ} [Fact p.Prime]
    (hEp : IsPGroup p E) (hcomm : IsMulCommutative E)
    (hpow : ∀ x : E, x ^ p = 1)
    (hrank : ¬ ∃ F : Subgroup E, IsElementaryAbelianOfRank p 3 F) :
    Nat.card E ≤ p ^ 2 := by
  classical
  letI : IsMulCommutative E := hcomm
  obtain ⟨n, hcard⟩ := hEp.exists_card_eq
  have hn : n ≤ 2 := by
    by_contra hnle
    have hthree : 3 ≤ n := by omega
    have htopcard : Nat.card (⊤ : Subgroup E) = p ^ n := by
      simpa using hcard
    obtain ⟨F, _hFtop, _hFnormal, hFcard⟩ :=
      exists_normal_subgroup_card_pow_le hEp (⊤ : Subgroup E)
        htopcard hthree
    apply hrank
    refine ⟨F,
      { isPGroup := hEp.to_subgroup F
        commutative := inferInstance
        pow_eq_one := ?_
        card_eq := hFcard }⟩
    intro x
    apply Subtype.ext
    exact hpow x
  rw [hcard]
  exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn

private theorem prime_dvd_sq_sub_one_of_special_prime_subgroup_action
    {X : Type u} [Group X] [Finite X]
    {K A : Subgroup X} {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) (hqp : q ≠ p) (hAcard : Nat.card A = q)
    (hKp : IsPGroup p K) (hKnoncomm : ¬ IsMulCommutative K)
    (hodd : Odd (Nat.card K))
    (hrank : ¬ ∃ E : Subgroup K, IsElementaryAbelianOfRank p 3 E)
    (hnorm : A ≤ Subgroup.normalizer (K : Set X))
    (hcop : (Nat.card K).Coprime (Nat.card A))
    (hOmegaTop : omegaOne p K = ⊤)
    (hSpecial : IsSpecial K)
    (hfixed : centralizerWithin K A =
      (Subgroup.center K).map K.subtype) :
    q ∣ p ^ 2 - 1 := by
  classical
  have hAprime : (Nat.card A).Prime := by simpa [hAcard] using hq
  letI : Fact (Nat.card A).Prime := ⟨hAprime⟩
  letI : Nontrivial A :=
    Finite.one_lt_card_iff_nontrivial.mp hAprime.one_lt
  letI : Nontrivial K := by
    by_contra htriv
    haveI : Subsingleton K := not_nontrivial_iff_subsingleton.mp htriv
    exact hKnoncomm inferInstance
  letI : Group.IsNilpotent K := hKp.isNilpotent
  have hpodd : Odd p := hodd.of_dvd_nat
    (hKp.card_eq_or_dvd.resolve_left
      (ne_of_gt (Finite.one_lt_card (α := K))))
  have hclassTwo : Group.nilpotencyClass K ≤ 2 :=
    nilpotencyClass_le_two_of_commutator_le_center
      hSpecial.commutator_le_center
  have hclass : Group.nilpotencyClass K ≤ if 3 < p then 3 else 2 := by
    split_ifs <;> omega
  have hpowK (x : K) : x ^ p = 1 :=
    omegaOne_pow_eq_one_of_small_nilpotencyClass
      p (Fact.out : p.Prime) hpodd hKp hclass x (by
        rw [hOmegaTop]
        trivial)
  have hexponent : Monoid.exponent K ∣ p :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpowK
  have hKcard : Nat.card K ≤ p ^ 3 :=
    natCard_le_prime_cube_of_exponent_prime_of_no_elementaryAbelian_rank_three
      hKp hrank hexponent
  let Z : Subgroup K := Subgroup.center K
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    apply hKnoncomm
    rw [← _root_.commutator_eq_bot_iff]
    rw [hSpecial.commutator_eq_center]
    exact hZbot
  have hZp : IsPGroup p Z := hKp.to_subgroup Z
  have hQp : IsPGroup p (K ⧸ Z) := hKp.to_quotient Z
  obtain ⟨m, hm⟩ := hZp.exists_card_eq
  obtain ⟨n, hn⟩ := hQp.exists_card_eq
  have hmpos : 0 < m := by
    by_contra hmzero
    have hm0 : m = 0 := by omega
    apply hZne
    apply Subgroup.card_eq_one.mp
    rw [hm, hm0, pow_zero]
  have hpowle : p ^ (n + m) ≤ p ^ 3 := by
    rw [pow_add, ← hn, ← hm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup Z]
    exact hKcard
  have hnm : n + m ≤ 3 :=
    (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp hpowle
  have hnle : n ≤ 2 := by omega
  have hQcard : Nat.card (K ⧸ Z) ≤ p ^ 2 := by
    rw [hn]
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hnle
  have hcenterNeTop : Subgroup.center K ≠ ⊤ := by
    intro htop
    exact hKnoncomm (Subgroup.center_eq_top_iff.mp htop)
  letI : Nontrivial (K ⧸ Z) := by
    apply QuotientGroup.nontrivial_iff.mpr
    simpa [Z] using hcenterNeTop
  letI : IsMulCommutative (K ⧸ Z) := by
    simpa [Z] using hSpecial.quotient_center_isMulCommutative
  have hQpow : ∀ x : K ⧸ Z, x ^ p = 1 := by
    intro x
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Z x
    exact congrArg (QuotientGroup.mk' Z) (hpowK x)
  have hfixed' : centralizerWithin K A = centerWithin K := by
    rw [← map_center_eq_centerWithin K]
    exact hfixed
  have hcenter : A ≤ Subgroup.centralizer (centerWithin K : Set X) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzfixed : z ∈ centralizerWithin K A := by
      rw [hfixed']
      exact hz
    exact ((mem_centralizerWithin.mp hzfixed).2 a ha).symm
  have hcentralizer : ∀ a : A, a ≠ 1 →
      centralizerWithin K (Subgroup.zpowers (a : X)) = centerWithin K := by
    intro a ha
    have haX : (a : X) ≠ 1 := by
      intro ha1
      exact ha (Subtype.ext ha1)
    exact (centralizerWithin_zpowers_eq_of_mem_prime_card
      K A hAprime a.property haX).trans hfixed'
  letI : MulDistribMulAction A K :=
    subgroupConjugationAction K A hnorm
  letI : MulAction.QuotientAction A Z := by
    simpa [Z] using subgroupConjugationCenterQuotientAction K A hnorm
  letI : MulDistribMulAction A (K ⧸ Z) :=
    (QuotientGroup.mk'_surjective Z).mulDistribMulAction
      (QuotientGroup.mk' Z) (fun _ _ ↦ rfl)
  let rhoQ : A →* MulAut (K ⧸ Z) :=
    MulDistribMulAction.toMulAut A (K ⧸ Z)
  have hfixedQ : ∀ a : A, a ≠ 1 → ∀ x : K ⧸ Z,
      a • x = x → x = 1 := by
    simpa [Z] using
      (centerQuotient_fixed_eq_one_of_centralizers
        K A hnorm hcop hcenter hcentralizer)
  have hrhoQne : rhoQ ≠ 1 := by
    intro hrhoQ
    obtain ⟨a, ha⟩ := exists_ne (1 : A)
    obtain ⟨x, hx⟩ := exists_ne (1 : K ⧸ Z)
    have hax : a • x = x := by
      have hrhoQa : rhoQ a = 1 := by rw [hrhoQ]; rfl
      simpa [rhoQ] using
        congrArg (fun f : MulAut (K ⧸ Z) ↦ f x) hrhoQa
    exact hx (hfixedQ a ha x hax)
  have hrhoQ : Function.Injective rhoQ :=
    (monoidHom_injective_iff_ne_one_of_prime_card rhoQ).mpr hrhoQne
  exact prime_dvd_sq_sub_one_of_faithful_elementaryAbelian_action
    hq hqp hAcard inferInstance hQpow hQcard rhoQ hrhoQ

private theorem prime_dvd_sq_sub_one_of_prime_subgroup_action
    {X : Type u} [Group X] [Finite X]
    {K A : Subgroup X} {p q : ℕ} [Fact p.Prime]
    (hq : q.Prime) (hqp : q ≠ p)
    (hKp : IsPGroup p K) (hodd : Odd (Nat.card K))
    (hrank : ¬ ∃ E : Subgroup K, IsElementaryAbelianOfRank p 3 E)
    (hAcard : Nat.card A = q)
    (hnorm : A ≤ Subgroup.normalizer (K : Set X))
    (hnoncentral : ¬ A ≤ Subgroup.centralizer (K : Set X)) :
    q ∣ p ^ 2 - 1 := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  have hAprime : (Nat.card A).Prime := by simpa [hAcard] using hq
  letI : Fact (Nat.card A).Prime := ⟨hAprime⟩
  have hAq : IsPGroup q A :=
    IsPGroup.of_card (n := 1) (by simpa using hAcard)
  let P : ℕ → Prop := fun n ↦
    ∀ (K' : Subgroup X), Nat.card K' = n →
      IsPGroup p K' → Odd (Nat.card K') →
      (¬ ∃ E : Subgroup K', IsElementaryAbelianOfRank p 3 E) →
      A ≤ Subgroup.normalizer (K' : Set X) →
      (¬ A ≤ Subgroup.centralizer (K' : Set X)) →
      q ∣ p ^ 2 - 1
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
      dsimp only [P]
      intro K' hcard hK'p hodd' hrank' hnorm' hnoncentral'
      letI : Group.IsNilpotent K' := hK'p.isNilpotent
      have hcop : (Nat.card K').Coprime (Nat.card A) :=
        IsPGroup.coprime_card_of_ne p q (Ne.symm hqp) K' A hK'p hAq
      let D : Subgroup X := ⁅A, K'⁆
      have hDK : D ≤ K' := by
        dsimp [D]
        exact Subgroup.le_normalizer_iff_commutator_le_right.mp hnorm'
      have hnormD : A ≤ Subgroup.normalizer (D : Set X) := by
        dsimp [D]
        exact Subgroup.normalizer_commutator_ge_left A K'
      have hperfectD : ⁅A, D⁆ = D := by
        simpa [D] using
          (commutator_commutator_eq_of_coprime hnorm' hcop)
      have hDnoncentral : ¬ A ≤ Subgroup.centralizer (D : Set X) := by
        intro hcentralD
        have hADbot : ⁅A, D⁆ = ⊥ :=
          Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcentralD
        have hDbot : D = ⊥ := hperfectD.symm.trans hADbot
        apply hnoncentral'
        rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
        simpa [D] using hDbot
      rcases lt_or_eq_of_le hDK with hDlt | hDeq
      · have hcardD : Nat.card D < n := by
          rw [← hcard]
          exact natCard_subgroup_lt_of_lt hDlt
        let toK : D →* K' :=
          { toFun := fun d ↦ ⟨d, hDK d.property⟩
            map_one' := rfl
            map_mul' := fun _ _ ↦ rfl }
        have hDp : IsPGroup p D :=
          hK'p.of_injective toK (fun a b hab ↦
            Subtype.ext (congrArg (fun z : K' ↦ (z : X)) hab))
        have hDodd : Odd (Nat.card D) :=
          hodd'.of_dvd_nat (Subgroup.card_dvd_of_le hDK)
        have hDrank :
            ¬ ∃ E : Subgroup D, IsElementaryAbelianOfRank p 3 E := by
          rintro ⟨E, hE⟩
          exact hrank' ⟨E.map toK,
            isElementaryAbelianOfRank_map_of_injective hE toK (by
              intro a b hab
              exact Subtype.ext
                (congrArg (fun z : K' ↦ (z : X)) hab))⟩
        exact ih (Nat.card D) hcardD D rfl hDp hDodd hDrank
          hnormD hDnoncentral
      · have hperfect : ⁅A, K'⁆ = K' := by
          simpa [D] using hDeq
        let W : Subgroup X := (omegaOne p K').map K'.subtype
        have hWK : W ≤ K' := by
          dsimp [W]
          exact Subgroup.map_subtype_le _
        rcases lt_or_eq_of_le hWK with hWlt | hWeq
        · by_cases hWcentral : A ≤ Subgroup.centralizer (W : Set X)
          · exfalso
            apply hnoncentral'
            exact coprime_odd_faithful_omegaOne_of_odd_card
              hK'p hnorm' hcop hodd' (by simpa [W] using hWcentral)
          · have hcardW : Nat.card W < n := by
              rw [← hcard]
              exact natCard_subgroup_lt_of_lt hWlt
            let toK : W →* K' :=
              { toFun := fun w ↦ ⟨w, hWK w.property⟩
                map_one' := rfl
                map_mul' := fun _ _ ↦ rfl }
            have hWp : IsPGroup p W :=
              hK'p.of_injective toK (fun a b hab ↦
                Subtype.ext (congrArg (fun z : K' ↦ (z : X)) hab))
            have hWodd : Odd (Nat.card W) :=
              hodd'.of_dvd_nat (Subgroup.card_dvd_of_le hWK)
            have hWrank :
                ¬ ∃ E : Subgroup W, IsElementaryAbelianOfRank p 3 E := by
              rintro ⟨E, hE⟩
              exact hrank' ⟨E.map toK,
                isElementaryAbelianOfRank_map_of_injective hE toK (by
                  intro a b hab
                  exact Subtype.ext
                    (congrArg (fun z : K' ↦ (z : X)) hab))⟩
            have hnormW : A ≤ Subgroup.normalizer (W : Set X) := by
              rw [Subgroup.le_normalizer_iff]
              exact characteristic_map_subtype_invariant_under_normalizer
                K' A (omegaOne p K') hnorm'
            exact ih (Nat.card W) hcardW W rfl hWp hWodd hWrank
              hnormW hWcentral
        · have hOmegaTop : omegaOne p K' = ⊤ := by
            apply Subgroup.map_injective K'.subtype_injective
            calc
              (omegaOne p K').map K'.subtype = K' := by simpa [W] using hWeq
              _ = K'.subtype.range := K'.range_subtype.symm
              _ = (⊤ : Subgroup K').map K'.subtype := by
                rw [← MonoidHom.range_eq_map]
          have hK'ne : K' ≠ ⊥ := by
            intro hbot
            apply hnoncentral'
            rw [hbot]
            intro a _
            rw [Subgroup.mem_centralizer_iff]
            intro x hx
            have hx1 : x = 1 := by simpa using hx
            subst x
            simp
          letI : Nontrivial K' :=
              (Subgroup.nontrivial_iff_ne_bot K').mpr hK'ne
          have hpodd : Odd p := hodd'.of_dvd_nat
              (hK'p.card_eq_or_dvd.resolve_left
                (ne_of_gt (Finite.one_lt_card (α := K'))))
          by_cases hK'comm : IsMulCommutative K'
          · letI : IsMulCommutative K' := hK'comm
            have hpowK : ∀ x : K', x ^ p = 1 := by
              intro x
              exact omegaOne_pow_eq_one_of_mul_closed p (by
                intro a b ha hb
                rw [mul_pow, ha, hb, one_mul]) (by
                  rw [hOmegaTop]
                  trivial)
            have hKcard : Nat.card K' ≤ p ^ 2 :=
              natCard_le_prime_sq_of_elementaryAbelian_no_rank_three
                hK'p hK'comm hpowK hrank'
            let rho : A →* MulAut K' :=
              K'.normalizerMonoidHom.comp (Subgroup.inclusion hnorm')
            have hrhoNe : rho ≠ 1 := by
              intro hrho
              apply hnoncentral'
              intro a ha
              rw [Subgroup.mem_centralizer_iff]
              intro x hx
              let aA : A := ⟨a, ha⟩
              let xK : K' := ⟨x, hx⟩
              have hrhoA : rho aA = 1 := by rw [hrho]; rfl
              have happ := congrArg (fun f : MulAut K' ↦ f xK) hrhoA
              have hconj : a * x * a⁻¹ = x :=
                congrArg Subtype.val happ
              calc
                x * a = (a * x * a⁻¹) * a := by rw [hconj]
                _ = a * x := by group
            have hrho : Function.Injective rho :=
              (monoidHom_injective_iff_ne_one_of_prime_card rho).mpr hrhoNe
            exact prime_dvd_sq_sub_one_of_faithful_elementaryAbelian_action
              hq hqp hAcard hK'comm hpowK hKcard rho hrho
          · by_cases hcharAll : ∀ (H : Subgroup K'),
                H.Characteristic → IsMulCommutative H →
                H.map K'.subtype ≤ Subgroup.centralizer (A : Set X)
            · have hchar : ∀ (H : Subgroup K') [H.Characteristic],
                  IsMulCommutative H →
                  H.map K'.subtype ≤
                    Subgroup.centralizer (A : Set X) := by
                intro H _ hHcomm
                exact hcharAll H inferInstance hHcomm
              obtain ⟨hSpecial, hfixed, _hcenterPow⟩ :=
                isSpecial_and_centralizerWithin_eq_center_of_characteristic_abelian_coprime
                  (Fact.out : p.Prime) hK'p hK'comm hnorm' hcop hperfect hchar
              exact prime_dvd_sq_sub_one_of_special_prime_subgroup_action
                hq hqp hAcard hK'p hK'comm hodd' hrank' hnorm' hcop hOmegaTop
                  hSpecial hfixed
            · push Not at hcharAll
              obtain ⟨H, hHchar, hHcomm, hHnoncentral⟩ := hcharAll
              letI : H.Characteristic := hHchar
              letI : IsMulCommutative H := hHcomm
              have hHneTop : H ≠ ⊤ := by
                intro htop
                apply hK'comm
                refine ⟨⟨fun x y ↦ ?_⟩⟩
                let xH : H := ⟨x, by rw [htop]; trivial⟩
                let yH : H := ⟨y, by rw [htop]; trivial⟩
                exact congrArg Subtype.val
                  (show xH * yH = yH * xH from mul_comm xH yH)
              let HA : Subgroup X := H.map K'.subtype
              have hHAK : HA ≤ K' := by
                dsimp [HA]
                exact Subgroup.map_subtype_le H
              have hHAlt : H < (⊤ : Subgroup K') :=
                lt_top_iff_ne_top.mpr hHneTop
              have hcardH : Nat.card H < Nat.card K' :=
                by simpa using natCard_subgroup_lt_of_lt hHAlt
              have hcardHAeq : Nat.card HA = Nat.card H := by
                dsimp [HA]
                exact Subgroup.card_map_of_injective K'.subtype_injective
              have hcardHA : Nat.card HA < n := by
                rw [hcardHAeq, ← hcard]
                exact hcardH
              let toK : HA →* K' :=
                { toFun := fun a ↦ ⟨a, hHAK a.property⟩
                  map_one' := rfl
                  map_mul' := fun _ _ ↦ rfl }
              have hHAp : IsPGroup p HA :=
                hK'p.of_injective toK (fun a b hab ↦
                  Subtype.ext (congrArg (fun z : K' ↦ (z : X)) hab))
              have hHAodd : Odd (Nat.card HA) :=
                hodd'.of_dvd_nat (Subgroup.card_dvd_of_le hHAK)
              have hHArank :
                  ¬ ∃ E : Subgroup HA,
                    IsElementaryAbelianOfRank p 3 E := by
                rintro ⟨E, hE⟩
                exact hrank' ⟨E.map toK,
                  isElementaryAbelianOfRank_map_of_injective hE toK (by
                    intro a b hab
                    exact Subtype.ext
                      (congrArg (fun z : K' ↦ (z : X)) hab))⟩
              have hnormHA : A ≤ Subgroup.normalizer (HA : Set X) := by
                rw [Subgroup.le_normalizer_iff]
                exact characteristic_map_subtype_invariant_under_normalizer
                  K' A H hnorm'
              have hHAnoncentral :
                  ¬ A ≤ Subgroup.centralizer (HA : Set X) := by
                intro hcentral
                apply hHnoncentral
                intro h hh
                rw [Subgroup.mem_centralizer_iff]
                intro a ha
                exact (Subgroup.mem_centralizer_iff.mp
                  (hcentral ha) h hh).symm
              exact ih (Nat.card HA) hcardHA HA rfl hHAp hHAodd
                hHArank hnormHA hHAnoncentral
  exact hP (Nat.card K) K rfl hKp hodd hrank hnorm hnoncentral

/-- `BGsection4.v: pi_Aut_rank2_pgroup` (Bender--Glauberman Lemmas 4.13
and 4.14). -/
theorem prime_dvd_mulAut_of_odd_pgroup_no_rank_three
    {R : Type u} [Group R] [Finite R]
    {p q : ℕ} [Fact p.Prime]
    (hR : IsPGroup p R) (hodd : Odd (Nat.card R))
    (hrank : ¬ ∃ E : Subgroup R, IsElementaryAbelianOfRank p 3 E)
    (hq : q.Prime) (hqAut : q ∣ Nat.card (MulAut R))
    (hqp : q ≠ p) :
    q ∣ p ^ 2 - 1 ∧ q < p ∧
      (q ∣ (p + 1) / 2 ∨ q ∣ (p - 1) / 2) := by
  classical
  letI : Fact q.Prime := ⟨hq⟩
  obtain ⟨a, haorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := MulAut R) q hqAut
  have ha : a ≠ 1 := by
    intro ha1
    subst a
    exact hq.ne_one (by simpa using haorder.symm)
  letI : Nontrivial R := by
    by_contra htriv
    haveI : Subsingleton R := not_nontrivial_iff_subsingleton.mp htriv
    apply ha
    apply MulEquiv.ext
    intro x
    exact Subsingleton.elim _ _
  have hpodd : Odd p := hodd.of_dvd_nat
    (hR.card_eq_or_dvd.resolve_left
      (ne_of_gt (Finite.one_lt_card (α := R))))
  let C : Subgroup (MulAut R) := Subgroup.zpowers a
  let phi : C →* MulAut R := C.subtype
  let X := R ⋊[phi] C
  letI : Finite X := by
    dsimp [X]
    exact Finite.of_equiv (R × C)
      (SemidirectProduct.equivProd (N := R) (G := C) (φ := phi)).symm
  let K : Subgroup X :=
    (SemidirectProduct.inl : R →* X).range
  let A : Subgroup X :=
    (SemidirectProduct.inr : C →* X).range
  let eK : R ≃* K :=
    MonoidHom.ofInjective
      (SemidirectProduct.inl_injective (N := R) (G := C) (φ := phi))
  let eA : C ≃* A :=
    MonoidHom.ofInjective
      (SemidirectProduct.inr_injective (N := R) (G := C) (φ := phi))
  have hKp : IsPGroup p K := hR.of_equiv eK
  have hKcard : Nat.card K = Nat.card R :=
    Nat.card_congr eK.toEquiv.symm
  have hKodd : Odd (Nat.card K) := by
    rw [hKcard]
    exact hodd
  have hKrank :
      ¬ ∃ E : Subgroup K, IsElementaryAbelianOfRank p 3 E := by
    rintro ⟨E, hE⟩
    exact hrank ⟨E.map eK.symm.toMonoidHom,
      isElementaryAbelianOfRank_map_of_injective hE
        eK.symm.toMonoidHom eK.symm.injective⟩
  have hAcard : Nat.card A = q := by
    calc
      Nat.card A = Nat.card C := Nat.card_congr eA.toEquiv.symm
      _ = q := by simpa [C, Nat.card_zpowers] using haorder
  letI : K.Normal := by
    dsimp [K]
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hnorm : A ≤ Subgroup.normalizer (K : Set X) := by
    rw [K.normalizer_eq_top]
    exact le_top
  have hmove : ∃ r : R, a r ≠ r := by
    by_contra hfix
    simp only [not_exists, not_ne_iff] at hfix
    apply ha
    apply MulEquiv.ext
    exact hfix
  obtain ⟨r, hr⟩ := hmove
  have hnoncentral :
      ¬ A ≤ Subgroup.centralizer (K : Set X) := by
    intro hcentral
    let c : C := ⟨a, Subgroup.mem_zpowers a⟩
    have hcA : (SemidirectProduct.inr c : X) ∈ A := ⟨c, rfl⟩
    have hrK : (SemidirectProduct.inl r : X) ∈ K := ⟨r, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp
      (hcentral hcA) (SemidirectProduct.inl r : X) hrK
    have hleft := congrArg SemidirectProduct.left hcomm
    apply hr
    simpa [X, phi, c] using hleft.symm
  have hdvd : q ∣ p ^ 2 - 1 :=
    prime_dvd_sq_sub_one_of_prime_subgroup_action
      hq hqp hKp hKodd hKrank hAcard hnorm hnoncentral
  obtain ⟨hlt, hhalf⟩ :=
    prime_lt_and_dvd_half_factor_of_dvd_sq_sub_one
      (Fact.out : p.Prime) hpodd hq hqp hdvd
  exact ⟨hdvd, hlt, hhalf⟩

end

end Submission.OddOrder.BG.Section04
