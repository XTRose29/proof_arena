import Submission.OddOrder.BG.Section04.BlackburnNoncritical
import Submission.OddOrder.BG.Section04.CoprimeMetacyclicCommutator
import Submission.OddOrder.BG.Section04.HuppertMetacyclic
import Submission.OddOrder.BG.Section04.RankTwoPGroupAutomorphismPrimes
import Submission.OddOrder.MathlibSupport.ExtraspecialCriticalCentralProduct
import Submission.OddOrder.MathlibSupport.OmegaOneCentralizerExtraspecial
import Submission.OddOrder.MathlibSupport.PrimeCubePGroupExtraspecial

/-!
Bender--Glauberman Theorem 4.16.

For a perfect coprime action on an odd `p`-group of rank at most two, the
prime is greater than three.  The group is either abelian, or its first omega
subgroup is extraspecial of order `p ^ 3` and forms a central product with its
cyclic centralizer.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement IsMulCommutative

noncomputable section

universe u

/-- `BGsection4.v: rank2_coprime_comm_cprod` (Bender--Glauberman Theorem
4.16). -/
theorem rankTwo_coprime_commutator_cprod
    {G : Type u} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime]
    (R A : Subgroup G)
    (hR : IsPGroup p R)
    (hoddR : Odd (Nat.card R))
    (hRne : R ≠ ⊥)
    (hrank : ¬ ∃ E : Subgroup R,
      IsElementaryAbelianOfRank p 3 E)
    (hperfect : ⁅R, A⁆ = R)
    (hAprime : Nat.Coprime p (Nat.card A))
    (hoddA : Odd (Nat.card A)) :
    3 < p ∧
      (IsMulCommutative R ∨
        ∃ S C : Subgroup G,
          ¬ IsMulCommutative S ∧
          Nat.card S = p ^ 3 ∧
          Monoid.exponent S ∣ p ∧
          C ≤ Subgroup.centralizer (S : Set G) ∧
          S ⊔ C = R ∧
          IsCyclic C ∧
          (omegaOne p C).map C.subtype =
            (_root_.commutator S).map S.subtype) := by
  classical
  have hAnormR : A ≤ Subgroup.normalizer (R : Set G) :=
    Subgroup.le_normalizer_iff_commutator_le_left.mpr hperfect.le
  have hAnoncentral : ¬ A ≤ Subgroup.centralizer (R : Set G) := by
    intro hcentral
    have hbot : ⁅R, A⁆ = ⊥ := by
      rw [Subgroup.commutator_comm,
        Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hcentral
    exact hRne (hperfect.symm.trans hbot)

  let rho : A →* MulAut R :=
    R.normalizerMonoidHom.comp (Subgroup.inclusion hAnormR)
  have hrhoNe : rho ≠ 1 := by
    intro hrho
    apply hAnoncentral
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro r hr
    let aA : A := ⟨a, ha⟩
    let rR : R := ⟨r, hr⟩
    have hrhoA : rho aA = 1 := by rw [hrho]; rfl
    have happ := congrArg (fun f : MulAut R ↦ f rR) hrhoA
    have hconj : a * r * a⁻¹ = r := congrArg Subtype.val happ
    calc
      r * a = (a * r * a⁻¹) * a := by rw [hconj]
      _ = a * r := by group
  have hrangeCardNe : Nat.card rho.range ≠ 1 := by
    intro hcard
    have hrangeBot : rho.range = ⊥ := Subgroup.card_eq_one.mp hcard
    exact hrhoNe (MonoidHom.range_eq_bot_iff.mp hrangeBot)
  obtain ⟨q, hq, hqRange⟩ := Nat.exists_prime_and_dvd hrangeCardNe
  have hqA : q ∣ Nat.card A :=
    hqRange.trans (Subgroup.card_range_dvd rho)
  have hqAut : q ∣ Nat.card (MulAut R) :=
    hqRange.trans rho.range.card_subgroup_dvd_card
  have hpNotA : ¬ p ∣ Nat.card A :=
    (Fact.out : p.Prime).coprime_iff_not_dvd.mp hAprime
  have hqp : q ≠ p := by
    intro h
    subst q
    exact hpNotA hqA
  have hqodd : Odd q := hoddA.of_dvd_nat hqA
  have hqlt : q < p :=
    (prime_dvd_mulAut_of_odd_pgroup_no_rank_three
      hR hoddR hrank hq hqAut hqp).2.1
  have hp3 : 3 < p := by
    have hq3 : 3 ≤ q := hq.odd_iff.mp hqodd
    omega

  refine ⟨hp3, ?_⟩
  by_cases hRcomm : IsMulCommutative R
  · exact Or.inl hRcomm
  · right
    let S : Subgroup G := (omegaOne p R).map R.subtype
    have hOmega : (omegaOne p R).map R.subtype = S := rfl
    have hSR : S ≤ R := Subgroup.map_subtype_le _
    have hSp : IsPGroup p S := by
      dsimp [S]
      exact (omegaOne_isPGroup p hR).map R.subtype
    have hSrank :
        ¬ ∃ E : Subgroup S, IsElementaryAbelianOfRank p 3 E := by
      rintro ⟨E, hE⟩
      let toR : S →* R := Subgroup.inclusion hSR
      exact hrank ⟨E.map toR,
        isElementaryAbelianOfRank_map_of_injective hE toR
          (Subgroup.inclusion_injective hSR)⟩
    have hOmegaExp : Monoid.exponent (omegaOne p R) ∣ p :=
      exponent_omegaOne_dvd_prime_of_no_elementaryAbelian_rank_three
        hR hrank hp3
    let eS : omegaOne p R ≃* S := by
      simpa [S] using
        Subgroup.equivMapOfInjective (omegaOne p R) R.subtype
          R.subtype_injective
    have hSexp : Monoid.exponent S ∣ p := by
      rw [← Monoid.exponent_eq_of_mulEquiv eS]
      exact hOmegaExp
    have hScardLe : Nat.card S ≤ p ^ 3 :=
      natCard_le_prime_cube_of_exponent_prime_of_no_elementaryAbelian_rank_three
        hSp hSrank hSexp
    have hScardMap : Nat.card S = Nat.card (omegaOne p R) := by
      dsimp [S]
      exact Subgroup.card_map_of_injective R.subtype_injective
    have hScardNotSmall : ¬ Nat.card S ≤ p ^ 2 := by
      intro hsmall
      have hOmegaCard : Nat.card (omegaOne p R) ≤ p ^ 2 := by
        rw [← hScardMap]
        exact hsmall
      have hmeta : IsMetacyclic R :=
        isMetacyclic_of_omegaOne_card_le_prime_sq hR hp3 hOmegaCard
      obtain ⟨n, hRcard⟩ := hR.exists_card_eq
      have hcop : Nat.Coprime (Nat.card R) (Nat.card A) := by
        rw [hRcard]
        exact hAprime.pow_left n
      have hcommRA : IsMulCommutative (⁅R, A⁆ : Subgroup G) :=
        (coprime_metacyclic_cent_sdprod
          R A hR hoddR hmeta hAnormR hcop).1
      rw [hperfect] at hcommRA
      exact hRcomm hcommRA
    obtain ⟨n, hScardPow⟩ := hSp.exists_card_eq
    have hnle : n ≤ 3 := by
      apply (Nat.pow_le_pow_iff_right (Fact.out : p.Prime).one_lt).mp
      simpa [hScardPow] using hScardLe
    have hnnotle : ¬ n ≤ 2 := by
      intro hn
      apply hScardNotSmall
      rw [hScardPow]
      exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos hn
    have hn : n = 3 := by omega
    have hScard : Nat.card S = p ^ 3 := by simpa [hn] using hScardPow
    have hSnoncomm : ¬ IsMulCommutative S := by
      intro hScomm
      letI : IsMulCommutative S := hScomm
      have hSpow : ∀ s : S, s ^ p = 1 :=
        Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hSexp
      apply hSrank
      refine ⟨⊤,
        { isPGroup := hSp.to_subgroup (⊤ : Subgroup S)
          commutative := inferInstance
          pow_eq_one := ?_
          card_eq := ?_ }⟩
      · intro x
        apply Subtype.ext
        exact hSpow x
      · simpa using hScard
    have hSextra : IsExtraspecial S :=
      isExtraspecial_of_isPGroup_of_natCard_eq_prime_cube_of_not_isMulCommutative
        hSp hScard hSnoncomm

    let C : Subgroup G := centralizerWithin R S
    have hCR : C ≤ R := centralizerWithin_le_left R S
    have hOmegaC :
        (omegaOne p C).map C.subtype =
          (_root_.commutator S).map S.subtype := by
      simpa [C] using
        map_omegaOne_centralizerWithin_eq_map_commutator_of_extraspecial
          hR hOmega hSextra
    have hcritical :
        ⁅S, R⁆ ≤ (_root_.commutator S).map S.subtype := by
      by_contra hnoncritical
      exact blackburn_noncritical_impossible
        R A S hR hoddR hOmega hSextra hScard hSexp hperfect hAprime
          hoddA hOmegaC hnoncritical
    have hsup : S ⊔ C = R := by
      simpa [C] using
        extraspecial_sup_centralizerWithin_eq hR hSR hSextra hcritical
    have hCcentral : C ≤ Subgroup.centralizer (S : Set G) := by
      exact inf_le_right

    have hCp : IsPGroup p C :=
      (hR.to_subgroup (C.subgroupOf R)).of_equiv
        (Subgroup.subgroupOfEquivOfLe hCR)
    have hCodd : Odd (Nat.card C) :=
      hoddR.of_dvd_nat (Subgroup.card_dvd_of_le hCR)
    have hOmegaCcard : Nat.card (omegaOne p C) = p := by
      calc
        Nat.card (omegaOne p C) =
            Nat.card ((omegaOne p C).map C.subtype) :=
          (Subgroup.card_map_of_injective C.subtype_injective).symm
        _ = Nat.card ((_root_.commutator S).map S.subtype) := by
          rw [hOmegaC]
        _ = Nat.card (_root_.commutator S) :=
          Subgroup.card_map_of_injective S.subtype_injective
        _ = Nat.card (Subgroup.center S) := by
          rw [hSextra.toIsSpecial.commutator_eq_center]
        _ = p := hSextra.center_card_eq hSp
    have hCnoRankTwo :
        ¬ ∃ E : Subgroup C, IsElementaryAbelianOfRank p 2 E := by
      rintro ⟨E, hE⟩
      have hEOmega : E ≤ omegaOne p C := by
        intro x hx
        let xE : E := ⟨x, hx⟩
        have hxpow : (x : C) ^ p = 1 := by
          exact congrArg Subtype.val (hE.pow_eq_one xE)
        exact mem_omegaOne_of_pow_eq_one p hxpow
      have hcardLe := Subgroup.card_le_of_le hEOmega
      rw [hE.card_eq, hOmegaCcard] at hcardLe
      nlinarith [(Fact.out : p.Prime).one_lt]
    have hCcyclic : IsCyclic C :=
      (odd_pgroup_isCyclic_iff_no_elementaryAbelian_rank_two
        hCp hCodd).mpr hCnoRankTwo
    exact ⟨S, C, hSnoncomm, hScard, hSexp, hCcentral, hsup,
      hCcyclic, hOmegaC⟩

end

end Submission.OddOrder.BG.Section04
