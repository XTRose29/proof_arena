import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Tactic

/-!
The elementary number-theoretic opening of Bender--Glauberman Appendix C.

The Coq development writes the order of the group `U` as
`(p ^ q - 1) / (p - 1)`.  We use the equal geometric sum as the definition;
this avoids truncated-subtraction and exact-division side conditions in later
arguments.  `nU_eq_div` recovers the expression used in the source.
-/

namespace Submission.OddOrder.BG.AppendixC

open Finset

/-- The Appendix C geometric-series parameter
`1 + p + ... + p ^ (q - 1)`.-/
def nU (p q : ℕ) : ℕ :=
  ∑ i ∈ range q, p ^ i

@[simp]
theorem nU_zero (p : ℕ) : nU p 0 = 0 := by
  simp [nU]

theorem nU_succ (p q : ℕ) : nU p (q + 1) = nU p q + p ^ q := by
  simp [nU, sum_range_succ]

/-- The geometric sum is an exact factor of `p ^ q - 1` once `p ≥ 1`.-/
theorem nU_mul_sub_one (p q : ℕ) (hp : 1 ≤ p) :
    nU p q * (p - 1) = p ^ q - 1 := by
  simpa only [nU] using geom_sum_mul_of_one_le hp q

/-- In particular, `p - 1` divides `p ^ q - 1`, with quotient `nU p q`.-/
theorem sub_one_dvd_pow_sub_one (p q : ℕ) (hp : 1 ≤ p) :
    p - 1 ∣ p ^ q - 1 := by
  refine ⟨nU p q, ?_⟩
  calc
    p ^ q - 1 = nU p q * (p - 1) := (nU_mul_sub_one p q hp).symm
    _ = (p - 1) * nU p q := by rw [mul_comm]

/-- The quotient presentation of `nU` used in `BGappendixC.v`.-/
theorem nU_eq_div (p q : ℕ) (hp : 2 ≤ p) :
    nU p q = (p ^ q - 1) / (p - 1) := by
  simpa only [nU] using Nat.geomSum_eq hp q

/-- The quotient presentation under the prime hypothesis of Appendix C.-/
theorem nU_eq_div_of_prime {p q : ℕ} (hp : p.Prime) :
    nU p q = (p ^ q - 1) / (p - 1) :=
  nU_eq_div p q hp.two_le

/-- If `r` divides `p - 1`, then the geometric sum is congruent to its
length modulo `r`.-/
theorem nU_modEq_length_of_dvd_sub_one {p q r : ℕ}
    (hp : 1 ≤ p) (hr : r ∣ p - 1) :
    nU p q ≡ q [MOD r] := by
  have hpmod : p ≡ 1 [MOD r] :=
    ((Nat.modEq_iff_dvd' hp).2 hr).symm
  unfold nU
  induction q with
  | zero => exact Nat.ModEq.rfl
  | succ q ih =>
      rw [sum_range_succ]
      simpa [Nat.succ_eq_add_one] using ih.add (hpmod.pow q)

/-- Divisibility of the geometric sum is divisibility of its length modulo
every divisor of `p - 1`.-/
theorem dvd_nU_iff_dvd_length_of_dvd_sub_one {p q r : ℕ}
    (hp : 1 ≤ p) (hr : r ∣ p - 1) :
    r ∣ nU p q ↔ r ∣ q := by
  have hmod := nU_modEq_length_of_dvd_sub_one (p := p) (q := q) hp hr
  constructor
  · intro hnU
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr hnU))
  · intro hq
    exact Nat.modEq_zero_iff_dvd.mp
      (hmod.trans (Nat.modEq_zero_iff_dvd.mpr hq))

/-! ### Consequences of the Appendix C arithmetic hypotheses -/

/-- The positivity facts recorded at the start of the source proof.-/
theorem prime_parameter_pos {r : ℕ} (hr : r.Prime) : 0 < r :=
  hr.pos

/-- For prime `p`, the denominator `p - 1` is positive.-/
theorem prime_sub_one_pos {p : ℕ} (hp : p.Prime) : 0 < p - 1 := by
  exact Nat.sub_pos_of_lt hp.one_lt

/-- Bender--Glauberman Appendix C, Remark I: `q` does not divide `p - 1`.

The source proves this by reducing the geometric-series quotient modulo
`p - 1`.  The geometric-sum presentation makes the same argument direct.
-/
theorem not_dvd_q_sub_one {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hcop : (nU p q).Coprime (p - 1)) :
    ¬ q ∣ p - 1 := by
  intro hdiv
  have hqnU : q ∣ nU p q :=
    (dvd_nU_iff_dvd_length_of_dvd_sub_one hp.one_lt.le hdiv).2
      (dvd_refl q)
  exact (Nat.not_coprime_of_dvd_of_dvd hq.one_lt hqnU hdiv) hcop

/-- The prime `p` is odd when a prime `q` is strictly smaller than it.-/
theorem odd_p {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hqp : q < p) :
    Odd p := by
  apply hp.odd_of_ne_two
  have hq2 : 2 ≤ q := hq.two_le
  omega

/-- Bender--Glauberman Appendix C, Remark V: the prime `q` is odd.-/
theorem odd_q {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hcop : (nU p q).Coprime (p - 1)) (hqp : q < p) :
    Odd q := by
  have hpodd : Odd p := odd_p hp hq hqp
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have hpne2 : p ≠ 2 := by omega
  have hnotdvd : ¬ q ∣ p - 1 := not_dvd_q_sub_one hp hq hcop
  apply hq.odd_of_ne_two
  intro hq2
  apply hnotdvd
  rw [hq2]
  exact even_iff_two_dvd.mp
    (hp.even_sub_one hpne2)

/-- In the Appendix C situation, `q` is strictly larger than `2`.-/
theorem two_lt_q {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hcop : (nU p q).Coprime (p - 1)) (hqp : q < p) :
    2 < q := by
  have := (hq.odd_iff.mp (odd_q hp hq hcop hqp))
  omega

/-- In particular, the Appendix C parameter `q` is larger than `1`.-/
theorem one_lt_q {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hcop : (nU p q).Coprime (p - 1)) (hqp : q < p) :
    1 < q := by
  exact lt_trans (by decide) (two_lt_q hp hq hcop hqp)

/-- In the Appendix C situation, `p` is strictly larger than `4`.-/
theorem four_lt_p {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hcop : (nU p q).Coprime (p - 1)) (hqp : q < p) :
    4 < p := by
  have hq2 : 2 < q := two_lt_q hp hq hcop hqp
  rcases odd_p hp hq hqp with ⟨k, hk⟩
  omega

/-- The inequalities and parity facts extracted at the start of the Coq
Appendix C proof, bundled for later consumers.-/
theorem arithmetic_consequences {p q : ℕ}
    (hp : p.Prime) (hq : q.Prime)
    (hcop : (nU p q).Coprime (p - 1)) (hqp : q < p) :
    ¬ q ∣ p - 1 ∧ Odd p ∧ Odd q ∧ 2 < q ∧ 4 < p := by
  exact ⟨not_dvd_q_sub_one hp hq hcop, odd_p hp hq hqp,
    odd_q hp hq hcop hqp, two_lt_q hp hq hcop hqp,
    four_lt_p hp hq hcop hqp⟩

end Submission.OddOrder.BG.AppendixC
