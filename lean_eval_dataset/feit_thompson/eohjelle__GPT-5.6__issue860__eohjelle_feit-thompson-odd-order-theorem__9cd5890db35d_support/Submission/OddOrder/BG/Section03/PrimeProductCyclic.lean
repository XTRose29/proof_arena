import Submission.OddOrder.BG.Section03.ElementaryAbelianPrimeProduct

/-!
Cyclicity of the prime-product actor in the elementary-abelian reduction.
-/

namespace Submission.OddOrder.BG.Section03

open Submission.OddOrder.MathlibSupport
open scoped IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]
variable {p q : ℕ}

/-- A group of order `p * q` is cyclic when Sylow subgroups for the two
prime factors centralize one another. -/
theorem isCyclic_of_sylow_le_centralizer
    (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q)
    (hcard : Nat.card G = p * q) (P : Sylow p G) (Q : Sylow q G)
    (hcentral : (P : Subgroup G) ≤
      Subgroup.centralizer (Q : Set G)) :
    IsCyclic G := by
  letI : Fact p.Prime := ⟨hp⟩
  letI : Fact q.Prime := ⟨hq⟩
  have hPcard : Nat.card P = p :=
    sylow_card_eq_left_prime_of_natCard_eq_mul hp hq hpq hcard P
  have hQcard : Nat.card Q = q :=
    sylow_card_eq_left_prime_of_natCard_eq_mul hq hp hpq.symm
      (hcard.trans (Nat.mul_comm p q)) Q
  letI : IsCyclic P := isCyclic_of_prime_card hPcard
  letI : IsCyclic Q := isCyclic_of_prime_card hQcard
  obtain ⟨x, hx⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := P)
  obtain ⟨y, hy⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Q)
  have hcomm : Commute (x : G) (y : G) := by
    have hxcentral := hcentral x.property
    rw [Subgroup.mem_centralizer_iff] at hxcentral
    exact (hxcentral (y : G) y.property).symm
  apply isCyclic_iff_exists_orderOf_eq_natCard.mpr
  refine ⟨(x : G) * (y : G), ?_⟩
  rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime]
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx, hy,
      hPcard, hQcard, hcard]
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hx, hy,
      hPcard, hQcard]
    exact (Nat.coprime_primes hp hq).mpr hpq

variable {A : Type u} [Group A] [Fintype A]
variable {H R : Subgroup A}
variable {ell : ℕ}

noncomputable section

/-- In the elementary-abelian reduction, a semiregular group of squarefree
prime-product order is cyclic. -/
theorem elementaryAbelian_primeProduct_isCyclic
    (hp : p.Prime) (hq : q.Prime) (hpq : p < q)
    (hcard : Nat.card R = p * q)
    [IsMulCommutative H] [Module (ZMod ell) (Additive H)]
    (hell : ell.Prime)
    (hH : H ≠ ⊥)
    (hnorm : R ≤ Subgroup.normalizer (H : Set A))
    (hreg : IsSemiregularConjugation H R)
    (hchar : (q : ZMod ell) ≠ 0) :
    IsCyclic R := by
  let P : Sylow p R := default
  let Q : Sylow q R := default
  have hQcard : Nat.card Q = q :=
    sylow_card_eq_left_prime_of_natCard_eq_mul hq hp hpq.ne'
      (hcard.trans (Nat.mul_comm p q)) Q
  have hcentral : (P : Subgroup R) ≤
      Subgroup.centralizer (Q : Set R) := by
    apply elementaryAbelian_primeProduct_sylow_le_centralizer
      hp hq hpq hcard P Q hell hH hnorm hreg
    simpa [hQcard] using hchar
  exact isCyclic_of_sylow_le_centralizer hp hq hpq.ne hcard P Q hcentral

end

end Submission.OddOrder.BG.Section03
