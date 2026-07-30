import Mathlib.Data.Nat.Find
import Submission.OddOrder.BG.Section04.ExponentOmegaOneRankTwo
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.MathlibSupport.NormalSubgroupPowerSeries
import Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal
import Submission.OddOrder.MathlibSupport.SubgroupCardinality

/-!
Bender--Glauberman Lemma 4.9.

For primes above three, the bound `|Omega₁(R)| ≤ p²` is inherited by every
quotient of the finite `p`-group `R`.  The proof follows the source's minimal
bad normal-subgroup argument.  Its final contradiction uses the power
homomorphism from Proposition 4.3.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped Classical
open scoped IsMulCommutative

noncomputable section

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p : ℕ} [Fact p.Prime]

private theorem omegaOne_eq_top_of_pow_eq_one
    {H : Type*} [Group H] (hpow : ∀ x : H, x ^ p = 1) :
    omegaOne p H = ⊤ := by
  apply top_unique
  intro x _
  exact mem_omegaOne_of_pow_eq_one p (hpow x)

private theorem natCard_omegaOne_eq_of_pow_eq_one
    {H : Type*} [Group H] [Finite H] (hpow : ∀ x : H, x ^ p = 1) :
    Nat.card (omegaOne p H) = Nat.card H := by
  rw [omegaOne_eq_top_of_pow_eq_one hpow, Subgroup.card_top]

private def normalQuotientOmegaOneCard
    {H : Type*} [Group H] [Finite H]
    (p : ℕ) (K : Subgroup H) (hK : K.Normal) : ℕ := by
  letI : K.Normal := hK
  exact Nat.card (omegaOne p (H ⧸ K))

/-- The cardinality-induction statement used for Lemma 4.9. -/
def QuotientOmegaOneRankTwoStatement (p n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = n →
    IsPGroup p G →
    Nat.card (omegaOne p G) ≤ p ^ 2 →
    3 < p →
    ∀ (K : Subgroup G) [K.Normal],
      Nat.card (omegaOne p (G ⧸ K)) ≤ p ^ 2

/-- Lemma 4.9 holds at every finite cardinality. -/
theorem quotientOmegaOneRankTwoStatement_all (p n : ℕ) [Fact p.Prime] :
    QuotientOmegaOneRankTwoStatement.{u} p n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ hGcard hGp hOmegaBound hp3 K _
      by_contra hKgood
      let BadSize : ℕ → Prop := fun m ↦
        ∃ (T : Subgroup G) (hT : T.Normal), Nat.card T = m ∧
          ¬ normalQuotientOmegaOneCard p T hT ≤ p ^ 2
      have hBadSize : ∃ m, BadSize m :=
        ⟨Nat.card K, K, inferInstance, rfl, hKgood⟩
      let m := Nat.find hBadSize
      obtain ⟨T, hTnormal, hTcard, hTbad⟩ := Nat.find_spec hBadSize
      letI : T.Normal := hTnormal
      have hTbad' : ¬ Nat.card (omegaOne p (G ⧸ T)) ≤ p ^ 2 := by
        simpa [normalQuotientOmegaOneCard] using hTbad
      have hTminimal (Z : Subgroup G) (hZnormal : Z.Normal)
          (hZbad : ¬ Nat.card (omegaOne p (G ⧸ Z)) ≤ p ^ 2) :
          Nat.card T ≤ Nat.card Z := by
        have hmZ : BadSize (Nat.card Z) :=
          ⟨Z, hZnormal, rfl, by
            simpa [normalQuotientOmegaOneCard] using hZbad⟩
        have hmle := Nat.find_min' hBadSize hmZ
        simpa [m, hTcard] using hmle
      have hTne : T ≠ ⊥ := by
        intro hTbot
        let e : G ⧸ T ≃* G :=
          (QuotientGroup.quotientMulEquivOfEq hTbot).trans
            QuotientGroup.quotientBot
        have hcardOmega := natCard_omegaOne_eq_of_mulEquiv p e
        apply hTbad'
        simpa [hcardOmega] using hOmegaBound
      have hTp : IsPGroup p T := hGp.to_subgroup T
      obtain ⟨t, htcard⟩ := hTp.exists_card_eq
      have htpos : 1 ≤ t := by
        by_contra ht
        have ht0 : t = 0 := by omega
        have hcardOne : Nat.card T = 1 := by simpa [ht0] using htcard
        exact (T.one_lt_card_iff_ne_bot.mpr hTne).ne' hcardOne
      obtain ⟨Z, hZT, hZnormal, hZcard⟩ :=
        exists_normal_subgroup_card_pow_le hGp T htcard htpos
      letI : Z.Normal := hZnormal
      have hZcardPrime : Nat.card Z = p := by simpa using hZcard
      have hZne : Z ≠ ⊥ := by
        rw [← Z.one_lt_card_iff_ne_bot, hZcardPrime]
        exact (Fact.out : p.Prime).one_lt
      have hTcardPrime : Nat.card T = p := by
        by_cases hZT_eq : Z = T
        · rw [← hZT_eq]
          exact hZcardPrime
        · have hZTlt : Z < T := lt_of_le_of_ne hZT hZT_eq
          have hZgood : Nat.card (omegaOne p (G ⧸ Z)) ≤ p ^ 2 := by
            by_contra hZbad
            have hmin := hTminimal Z hZnormal hZbad
            exact (not_le_of_gt (natCard_subgroup_lt_of_lt hZTlt)) hmin
          have hQZcardLt : Nat.card (G ⧸ Z) < n := by
            simpa [hGcard] using natCard_quotient_lt_of_ne_bot Z hZne
          let qZ : G →* G ⧸ Z := QuotientGroup.mk' Z
          let TZ : Subgroup (G ⧸ Z) := T.map qZ
          letI : TZ.Normal :=
            Subgroup.Normal.map (show T.Normal from inferInstance) qZ
              (QuotientGroup.mk'_surjective Z)
          have hiterated :
              Nat.card (omegaOne p ((G ⧸ Z) ⧸ TZ)) ≤ p ^ 2 :=
            ih (Nat.card (G ⧸ Z)) hQZcardLt (G ⧸ Z) rfl
              (hGp.to_quotient Z) hZgood hp3 TZ
          let eThird : ((G ⧸ Z) ⧸ TZ) ≃* G ⧸ T := by
            dsimp [TZ, qZ]
            exact QuotientGroup.quotientQuotientEquivQuotient Z T hZT
          have hthirdCard := natCard_omegaOne_eq_of_mulEquiv p eThird
          exact False.elim (hTbad' (by
            rw [← hthirdCard]
            exact hiterated))
      let Q := G ⧸ T
      let q : G →* Q := QuotientGroup.mk' T
      have hQp : IsPGroup p Q := hGp.to_quotient T
      have hQbad : p ^ 2 < Nat.card (omegaOne p Q) := by
        exact Nat.lt_of_not_ge hTbad'
      have hminimalSubgroup (U : Subgroup Q)
          (hUbad : p ^ 2 < Nat.card (omegaOne p U)) : U = ⊤ := by
        by_contra hUneTop
        let H : Subgroup G := U.comap q
        have hHneTop : H ≠ ⊤ := by
          intro hHtop
          apply hUneTop
          have hmap : H.map q = U := by
            dsimp [H, q]
            exact Subgroup.map_comap_eq_self_of_surjective
              (QuotientGroup.mk'_surjective T) U
          rw [← hmap, hHtop]
          exact Subgroup.map_top_of_surjective q
            (QuotientGroup.mk'_surjective T)
        have hHcardLt : Nat.card H < n := by
          simpa [hGcard] using natCard_subgroup_lt_of_ne_top H hHneTop
        have hHp : IsPGroup p H := hGp.to_subgroup H
        have hHOmega : Nat.card (omegaOne p H) ≤ p ^ 2 := by
          have hmapOmega :
              (omegaOne p H).map H.subtype ≤ omegaOne p G :=
            map_omegaOne_le p H.subtype
          calc
            Nat.card (omegaOne p H) =
                Nat.card ((omegaOne p H).map H.subtype) :=
              (Subgroup.card_map_of_injective H.subtype_injective).symm
            _ ≤ Nat.card (omegaOne p G) := Subgroup.card_le_of_le hmapOmega
            _ ≤ p ^ 2 := hOmegaBound
        have hTH : T ≤ H := by
          intro x hx
          change q x ∈ U
          have hqx : q x = 1 := by
            exact (QuotientGroup.eq_one_iff x).mpr hx
          rw [hqx]
          exact U.one_mem
        let TH : Subgroup H := T.subgroupOf H
        letI : TH.Normal := by
          dsimp [TH]
          infer_instance
        have hHquotient : Nat.card (omegaOne p (H ⧸ TH)) ≤ p ^ 2 :=
          ih (Nat.card H) hHcardLt H rfl hHp hHOmega hp3 TH
        have hHmap : H.map q = U := by
          dsimp [H, q]
          exact Subgroup.map_comap_eq_self_of_surjective
            (QuotientGroup.mk'_surjective T) U
        let eImage : H ⧸ TH ≃* H.map q :=
          QuotientGroup.liftEquiv TH
            (q.subgroupMap_surjective H) (by
              dsimp [TH]
              rw [Subgroup.ker_subgroupMap, QuotientGroup.ker_mk'])
        let eHU : H ⧸ TH ≃* U :=
          eImage.trans (MulEquiv.subgroupCongr hHmap)
        have hHUcard := natCard_omegaOne_eq_of_mulEquiv p eHU
        exact (not_lt_of_ge (by simpa [hHUcard] using hHquotient)) hUbad
      have hQcard : Nat.card Q = p ^ 3 := by
        by_cases hE : ∃ E : Subgroup Q, IsElementaryAbelianOfRank p 3 E
        · obtain ⟨E, hE⟩ := hE
          have hOmegaE : Nat.card (omegaOne p E) = p ^ 3 := by
            rw [natCard_omegaOne_eq_of_pow_eq_one hE.pow_eq_one, hE.card_eq]
          have hEtop : E = ⊤ :=
            hminimalSubgroup E (by
              rw [hOmegaE]
              exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
                (by omega))
          calc
            Nat.card Q = Nat.card (⊤ : Subgroup Q) := Subgroup.card_top.symm
            _ = Nat.card E := by rw [hEtop]
            _ = p ^ 3 := hE.card_eq
        · have hOmegaExp : Monoid.exponent (omegaOne p Q) ∣ p :=
            exponent_omegaOne_dvd_prime_of_no_elementaryAbelian_rank_three
              hQp hE hp3
          have hOmegaPow : ∀ x : omegaOne p Q, x ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hOmegaExp
          have hOmegaOmegaCard :
              Nat.card (omegaOne p (omegaOne p Q)) =
                Nat.card (omegaOne p Q) :=
            natCard_omegaOne_eq_of_pow_eq_one hOmegaPow
          have hOmegaTop : omegaOne p Q = ⊤ :=
            hminimalSubgroup (omegaOne p Q) (by
              simpa [hOmegaOmegaCard] using hQbad)
          have hQExp : Monoid.exponent Q ∣ p := by
            apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
            intro x
            let xOmega : omegaOne p Q :=
              ⟨x, by rw [hOmegaTop]; trivial⟩
            simpa [xOmega] using congrArg Subtype.val (hOmegaPow xOmega)
          have hQcardLe : Nat.card Q ≤ p ^ 3 :=
            natCard_le_prime_cube_of_exponent_prime_of_no_elementaryAbelian_rank_three
              hQp hE hQExp
          obtain ⟨d, hd⟩ := hQp.exists_card_eq
          have hdGt : 2 < d := by
            apply (Nat.pow_lt_pow_iff_right
              (Fact.out : p.Prime).one_lt).mp
            simpa [hOmegaTop, Subgroup.card_top, hd] using hQbad
          have hdLe : d ≤ 3 := by
            apply (Nat.pow_le_pow_iff_right
              (Fact.out : p.Prime).one_lt).mp
            simpa [hd] using hQcardLe
          have hd3 : d = 3 := by omega
          simpa [hd3] using hd
      have hQexp : Monoid.exponent Q ∣ p := by
        by_cases hE : ∃ E : Subgroup Q, IsElementaryAbelianOfRank p 3 E
        · obtain ⟨E, hE⟩ := hE
          have hOmegaE : Nat.card (omegaOne p E) = p ^ 3 := by
            rw [natCard_omegaOne_eq_of_pow_eq_one hE.pow_eq_one, hE.card_eq]
          have hEtop : E = ⊤ :=
            hminimalSubgroup E (by
              rw [hOmegaE]
              exact Nat.pow_lt_pow_right (Fact.out : p.Prime).one_lt
                (by omega))
          have hpowQ : ∀ x : Q, x ^ p = 1 := by
            intro x
            let xE : E := ⟨x, by rw [hEtop]; trivial⟩
            exact congrArg Subtype.val (hE.pow_eq_one xE)
          exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr hpowQ
        · have hOmegaExp : Monoid.exponent (omegaOne p Q) ∣ p :=
            exponent_omegaOne_dvd_prime_of_no_elementaryAbelian_rank_three
              hQp hE hp3
          have hOmegaPow : ∀ x : omegaOne p Q, x ^ p = 1 :=
            Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hOmegaExp
          have hOmegaOmegaCard :
              Nat.card (omegaOne p (omegaOne p Q)) =
                Nat.card (omegaOne p Q) :=
            natCard_omegaOne_eq_of_pow_eq_one hOmegaPow
          have hOmegaTop : omegaOne p Q = ⊤ :=
            hminimalSubgroup (omegaOne p Q) (by
              simpa [hOmegaOmegaCard] using hQbad)
          apply Monoid.exponent_dvd_iff_forall_pow_eq_one.mpr
          intro x
          let xOmega : omegaOne p Q :=
            ⟨x, by rw [hOmegaTop]; trivial⟩
          simpa [xOmega] using congrArg Subtype.val (hOmegaPow xOmega)
      have hGcardPrimeFour : Nat.card G = p ^ 4 := by
        calc
          Nat.card G = Nat.card Q * Nat.card T :=
            Subgroup.card_eq_card_quotient_mul_card_subgroup T
          _ = p ^ 3 * p := by rw [hQcard, hTcardPrime]
          _ = p ^ 4 := by ring
      have hpodd : Odd p :=
        (Fact.out : p.Prime).odd_of_ne_two (by omega)
      have hGodd : Odd (Nat.card G) := by
        rw [hGcardPrimeFour]
        exact hpodd.pow
      have hOmegaCard : Nat.card (omegaOne p G) = p ^ 2 := by
        obtain ⟨d, hd⟩ := (omegaOne_isPGroup p hGp).exists_card_eq
        have hdLe : d ≤ 2 := by
          apply (Nat.pow_le_pow_iff_right
            (Fact.out : p.Prime).one_lt).mp
          simpa [hd] using hOmegaBound
        have hnotLePrime : ¬ Nat.card (omegaOne p G) ≤ p := by
          intro hlePrime
          have hnoRankTwo :
              ¬ ∃ E : Subgroup G, IsElementaryAbelianOfRank p 2 E := by
            rintro ⟨E, hE⟩
            have hEOmega : E ≤ omegaOne p G := by
              intro x hx
              exact mem_omegaOne_of_pow_eq_one p (by
                simpa using congrArg Subtype.val
                  (hE.pow_eq_one ⟨x, hx⟩))
            have hcardE := Subgroup.card_le_of_le hEOmega
            rw [hE.card_eq] at hcardE
            have hpLtSq : p < p ^ 2 := by
              rw [pow_two]
              exact lt_mul_of_one_lt_right
                (Fact.out : p.Prime).pos (Fact.out : p.Prime).one_lt
            exact (not_le_of_gt hpLtSq) (hcardE.trans hlePrime)
          have hGcyclic : IsCyclic G :=
            (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
              hGp hGodd).mpr hnoRankTwo
          letI : IsCyclic G := hGcyclic
          have hQcyclic : IsCyclic Q :=
            isCyclic_of_surjective q (QuotientGroup.mk'_surjective T)
          letI : IsCyclic Q := hQcyclic
          have hQneOne : Nat.card Q ≠ 1 := by
            rw [hQcard]
            exact (one_lt_pow₀ (Fact.out : p.Prime).one_lt (by omega)).ne'
          have hQOmegaCard : Nat.card (omegaOne p Q) = p :=
            card_omegaOne_of_isCyclic_isPGroup Fact.out hQp hQneOne
          rw [hQOmegaCard] at hQbad
          have hpLeSq : p ≤ p ^ 2 := by
            rw [pow_two]
            exact Nat.le_mul_of_pos_right p (Fact.out : p.Prime).pos
          exact (not_lt_of_ge hpLeSq) hQbad
        have hdGt : 1 < d := by
          apply (Nat.pow_lt_pow_iff_right
            (Fact.out : p.Prime).one_lt).mp
          rw [← hd]
          exact lt_of_not_ge (by simpa using hnotLePrime)
        have hd2 : d = 2 := by omega
        simpa [hd2] using hd
      let W : Subgroup G := omegaOne p G
      letI : W.Normal := by dsimp [W]; infer_instance
      have hQWcard : Nat.card (G ⧸ W) = p ^ 2 := by
        have hcardFactor :=
          Subgroup.card_eq_card_quotient_mul_card_subgroup W
        have hp2pos : 0 < p ^ 2 := pow_pos (Fact.out : p.Prime).pos _
        apply Nat.eq_of_mul_eq_mul_right hp2pos
        calc
          Nat.card (G ⧸ W) * p ^ 2 =
              Nat.card (G ⧸ W) * Nat.card W := by
                rw [show Nat.card W = p ^ 2 by simpa [W] using hOmegaCard]
          _ = Nat.card G := hcardFactor.symm
          _ = p ^ 4 := hGcardPrimeFour
          _ = p ^ 2 * p ^ 2 := by ring
      have hQWcomm : IsMulCommutative (G ⧸ W) :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq hQWcard
      have hcommutator : _root_.commutator G ≤ W :=
        Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hQWcomm
      letI : Group.IsNilpotent G := hGp.isNilpotent
      have hclass : Group.nilpotencyClass G ≤ 3 :=
        nilpotencyClass_le_three_of_isPGroup_card_le_prime_four hGp
          (by rw [hGcardPrimeFour])
      have hclass' :
          Group.nilpotencyClass G ≤ if 3 < p then 3 else 2 := by
        simpa [hp3] using hclass
      have hOmegaExp : Monoid.exponent (omegaOne p G) ∣ p :=
        (exponent_odd_nil23 p Fact.out hpodd hGp hclass').1
      have hOmegaPow : ∀ z : G, z ∈ omegaOne p G → z ^ p = 1 := by
        intro z hz
        have hz' : (⟨z, hz⟩ : omegaOne p G) ^ p = 1 :=
          Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hOmegaExp ⟨z, hz⟩
        simpa using congrArg Subtype.val hz'
      have hderivedPow :
          ∀ r : G, r ∈ _root_.commutator G → r ^ p = 1 :=
        fun r hr ↦ hOmegaPow r (hcommutator hr)
      let f : G →* G :=
        exponentOddNil23PowerMap p Fact.out hpodd hclass' hderivedPow
      have hfapply (x : G) : f x = x ^ p := by
        simp [f]
      have hWker : W = f.ker := by
        dsimp [W]
        exact omegaOne_eq_ker_of_apply_eq_pow p f hfapply
      have hRangeT : f.range ≤ T := by
        rintro _ ⟨x, rfl⟩
        rw [hfapply]
        apply (QuotientGroup.eq_one_iff (x ^ p)).mp
        rw [QuotientGroup.mk_pow]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hQexp
          (QuotientGroup.mk' T x)
      have hquotientLe : Nat.card (G ⧸ W) ≤ Nat.card T := by
        calc
          Nat.card (G ⧸ W) = Nat.card (G ⧸ f.ker) := by rw [hWker]
          _ = Nat.card f.range :=
            Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv
          _ ≤ Nat.card T := Subgroup.card_le_of_le hRangeT
      rw [hQWcard, hTcardPrime] at hquotientLe
      have hpLtSq : p < p ^ 2 := by
        rw [pow_two]
        exact lt_mul_of_one_lt_right
          (Fact.out : p.Prime).pos (Fact.out : p.Prime).one_lt
      exact (not_le_of_gt hpLtSq) hquotientLe

/-- `BGsection4.v: quotient_p2_Ohm1` (Bender--Glauberman Lemma 4.9). -/
theorem natCard_omegaOne_quotient_le_prime_sq
    (hG : IsPGroup p G)
    (hOmega : Nat.card (omegaOne p G) ≤ p ^ 2)
    (hp3 : 3 < p)
    (K : Subgroup G) [K.Normal] :
    Nat.card (omegaOne p (G ⧸ K)) ≤ p ^ 2 :=
  quotientOmegaOneRankTwoStatement_all p (Nat.card G)
    G rfl hG hOmega hp3 K

end

end Submission.OddOrder.BG.Section04
