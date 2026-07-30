import Submission.OddOrder.BG.Section03.FrobeniusSubgroupNormalizer
import Submission.OddOrder.MathlibSupport.PrimeProductGroup

/-!
Conjugacy of prime-product complements in a finite Frobenius decomposition.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport

universe u

variable {G : Type u} [Group G] [Finite G]
variable {K R B : Subgroup G}
variable {p q : ℕ}

namespace IsFrobeniusDecomposition

/-- Any second complement of the Frobenius kernel is conjugate to a
prime-product complement by an element of the kernel. -/
theorem complement_eq_kernel_conjugate_of_natCard_eq_mul_primes
    (h : IsFrobeniusDecomposition K R)
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card R = p * q)
    (hB : K.IsComplement' B) :
    ∃ x : K, B = R.map (MulAut.conj (x : G)).toMonoidHom := by
  letI : Fact q.Prime := ⟨hq⟩
  have hcardB : Nat.card B = p * q := by
    have hmul : Nat.card K * Nat.card B = Nat.card K * Nat.card R :=
      hB.card_mul.trans h.card_mul_card.symm
    exact (Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := K)) hmul).trans hcard
  let Qb : Sylow q B := default
  have hQbcard : Nat.card Qb = q :=
    sylow_card_eq_left_prime_of_natCard_eq_mul hq hp hpq.ne'
      (hcardB.trans (Nat.mul_comm p q)) Qb
  have hQbne : (Qb : Subgroup B) ≠ ⊥ := by
    rw [← Subgroup.one_lt_card_iff_ne_bot, hQbcard]
    exact hq.one_lt
  letI : (Qb : Subgroup B).Normal :=
    sylow_right_normal_of_lt_of_natCard_eq_mul hp hq hpq hcardB Qb
  let Q : Subgroup G := (Qb : Subgroup B).map B.subtype
  have hQne : Q ≠ ⊥ := by
    intro hbot
    apply hQbne
    exact (Subgroup.map_eq_bot_iff_of_injective (Qb : Subgroup B)
      B.subtype_injective).mp hbot
  have hBnormQ : B ≤ Subgroup.normalizer (Q : Set G) := by
    intro b hb
    apply Subgroup.le_normalizer_map B.subtype
    refine ⟨⟨b, hb⟩, ?_, rfl⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top _
  letI : Nontrivial Qb := Qb.nontrivial_iff_ne_bot.mpr hQbne
  obtain ⟨t, htne⟩ := exists_ne (1 : Qb)
  have htNotK : (((t : Qb) : B) : G) ∉ K := by
    intro htK
    have htbot : (((t : Qb) : B) : G) ∈ (⊥ : Subgroup G) := by
      rw [← disjoint_iff.mp hB.disjoint]
      exact ⟨htK, (t : B).property⟩
    apply htne
    exact Subtype.ext (Subtype.ext (Subgroup.mem_bot.mp htbot))
  obtain ⟨x, htx⟩ := h.exists_kernel_conjugate_complement_of_not_mem htNotK
  let Rx : Subgroup G := R.map (MulAut.conj (x : G)).toMonoidHom
  have hQRx : Q ≤ Rx := by
    rintro z ⟨y, hy, rfl⟩
    let yQ : Qb := ⟨y, hy⟩
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp
      (mem_zpowers_of_prime_card hQbcard htne (g' := yQ))
    have hpow : ((((t : Qb) : B) : G) ^ n) ∈ Rx :=
      Rx.zpow_mem htx n
    have hnG : ((((t : Qb) : B) : G) ^ n) = ((yQ : B) : G) :=
      congrArg (fun z : Qb ↦ ((z : B) : G)) hn
    change ((yQ : B) : G) ∈ Rx
    rw [← hnG]
    exact hpow
  have hBRx : B ≤ Rx := hBnormQ.trans
    (h.normalizer_le_kernel_conjugate_complement x hQne hQRx)
  refine ⟨x, Subgroup.eq_of_le_of_card_ge hBRx ?_⟩
  have hcardRx : Nat.card Rx = Nat.card R :=
    Subgroup.card_map_of_injective (K := R) (MulAut.conj (x : G)).injective
  rw [hcardRx, hcardB, hcard]

end IsFrobeniusDecomposition

end Submission.OddOrder.BG.Section03
