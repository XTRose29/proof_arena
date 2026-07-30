import Submission.OddOrder.BG.Section03.PrimeProductCyclic
import Submission.OddOrder.BG.Section03.FrobeniusInvariantSylow
import Submission.OddOrder.MathlibSupport.MinimalNormalUnderElementaryAbelian
import Submission.OddOrder.MathlibSupport.MinimalNormalUnderExistence

/-!
Reduction of the regular prime-product lemma to invariant Sylow existence.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {A : Type u} [Group A] [Fintype A]
variable {H R S : Subgroup A}
variable {p q ell : ℕ}

noncomputable section

/-- Once a nontrivial prime subgroup of `H` normalized by `R` has been
selected, the elementary-abelian reduction proves that the semiregular
prime-product actor is cyclic. -/
theorem regular_primeProduct_isCyclic_of_invariant_pSubgroup
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card R = p * q)
    (hell : ell.Prime) (hSp : IsPGroup ell S)
    (hSne : S ≠ ⊥) (hSH : S ≤ H)
    (hnormS : R ≤ Subgroup.normalizer (S : Set A))
    (hnormH : R ≤ Subgroup.normalizer (H : Set A))
    (hreg : IsSemiregularConjugation H R) :
    IsCyclic R := by
  letI : Fact ell.Prime := ⟨hell⟩
  have hcop : Nat.Coprime (Nat.card H) (Nat.card R) :=
    hreg.natCard_coprime hnormH
  obtain ⟨M, hMS, hmin⟩ := exists_minimalNormalUnder_le hSne hnormS
  have hMH : M ≤ H := hMS.trans hSH
  have hMp : IsPGroup ell M := hSp.to_le hMS
  have helem := hmin.isElementaryAbelian_of_isPGroup hMp
  letI : IsMulCommutative M := helem.1
  letI : Module (ZMod ell) (Additive M) :=
    elementaryAbelianZModModule M ell helem.2
  obtain ⟨n, hScard⟩ := hSp.exists_card_eq
  have hn : n ≠ 0 := by
    intro hn
    subst n
    have hcardOne : Nat.card S = 1 := by simpa using hScard
    have hcardGt : 1 < Nat.card S :=
      S.one_lt_card_iff_ne_bot.mpr hSne
    omega
  have hellS : ell ∣ Nat.card S := by
    rw [hScard]
    exact dvd_pow_self ell hn
  have hellH : ell ∣ Nat.card H :=
    hellS.trans (Subgroup.card_dvd_of_le hSH)
  have hqR : q ∣ Nat.card R := by
    rw [hcard]
    exact dvd_mul_left q p
  have hell_ne_q : ell ≠ q := by
    intro heq
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨q, hq, heq ▸ hellH, hqR⟩) hcop
  have hchar : (q : ZMod ell) ≠ 0 := by
    intro hzero
    have hellq : ell ∣ q :=
      (ZMod.natCast_eq_zero_iff q ell).mp hzero
    rcases (Nat.dvd_prime hq).mp hellq with hellOne | hellEq
    · exact hell.ne_one hellOne
    · exact hell_ne_q hellEq
  apply elementaryAbelian_primeProduct_isCyclic hp hq hpq hcard hell
    hmin.ne_bot hmin.le_normalizer (hreg.mono_left hMH) hchar

/-- Aschbacher 40.6(3), equivalently Gorenstein 3.14(iii): a nontrivial
group admitting a semiregular normalized action by a group of order `p*q`
is acted on by a cyclic group. This is `regular_pq_group_cyclic` in the
MathComp source. -/
theorem regular_primeProduct_isCyclic
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card R = p * q)
    (hH : H ≠ ⊥)
    (hnorm : R ≤ Subgroup.normalizer (H : Set A))
    (hreg : IsSemiregularConjugation H R) :
    IsCyclic R := by
  classical
  have hR : R ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hcard]
    nlinarith [hp.one_lt, hq.one_lt]
  have hHcard : Nat.card H ≠ 1 := by
    exact ne_of_gt (H.one_lt_card_iff_ne_bot.mpr hH)
  obtain ⟨ell, hell, hellH⟩ := Nat.exists_prime_and_dvd hHcard
  let J : Subgroup A := R ⊔ H
  let HJ : Subgroup J := H.subgroupOf J
  let RJ : Subgroup J := R.subgroupOf J
  have hFrob : IsFrobeniusDecomposition HJ RJ := by
    simpa [J, HJ, RJ] using
      hreg.isFrobeniusDecomposition_sup hnorm hH hR
  have hcardHJ : Nat.card HJ = Nat.card H := by
    have hc := Subgroup.card_map_of_injective
      (K := HJ) J.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le le_sup_right] at hc
    exact hc.symm
  have hcardRJ : Nat.card RJ = Nat.card R := by
    have hc := Subgroup.card_map_of_injective
      (K := RJ) J.subtype_injective
    rw [Subgroup.map_subgroupOf_eq_of_le le_sup_left] at hc
    exact hc.symm
  have hellHJ : ell ∣ Nat.card HJ := by rwa [hcardHJ]
  have hcardRJpq : Nat.card RJ = p * q := hcardRJ.trans hcard
  obtain ⟨S, hSHJ, hSne, hSp, hRJnormS⟩ :=
    hFrob.exists_invariant_pSubgroup_of_natCard_eq_mul_primes
      hp hq hpq hcardRJpq hell hellHJ
  have hcycRJ : IsCyclic RJ :=
    regular_primeProduct_isCyclic_of_invariant_pSubgroup
      hp hq hpq hcardRJpq hell hSp hSne hSHJ hRJnormS
        hFrob.complement_le_normalizer hFrob.fixedPointFree
  let f : RJ →* R :=
    (J.subtype.comp RJ.subtype).codRestrict R (by
      intro r
      exact r.property)
  have hf : Function.Surjective f := by
    intro r
    let rJ : J := ⟨r, (show R ≤ J from le_sup_left) r.property⟩
    let rRJ : RJ := ⟨rJ, r.property⟩
    refine ⟨rRJ, ?_⟩
    rfl
  letI : IsCyclic RJ := hcycRJ
  exact isCyclic_of_surjective f hf

/-- Source-shaped version of `regular_pq_group_cyclic`, symmetric in the
two distinct prime factors. -/
theorem regular_pq_group_cyclic
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcard : Nat.card R = p * q)
    (hH : H ≠ ⊥)
    (hnorm : R ≤ Subgroup.normalizer (H : Set A))
    (hreg : IsSemiregularConjugation H R) :
    IsCyclic R := by
  rcases lt_or_gt_of_ne hpq with hp_lt_q | hq_lt_p
  · exact regular_primeProduct_isCyclic hp hq hp_lt_q hcard
      hH hnorm hreg
  · exact regular_primeProduct_isCyclic hq hp hq_lt_p
      (hcard.trans (Nat.mul_comm p q)) hH hnorm hreg

end

end Submission.OddOrder.BG.Section03
