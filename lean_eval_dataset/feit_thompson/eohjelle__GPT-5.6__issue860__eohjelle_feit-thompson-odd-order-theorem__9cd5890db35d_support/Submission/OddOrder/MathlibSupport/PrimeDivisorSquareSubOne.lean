import Mathlib.Data.Nat.Prime.Basic

/-!
Arithmetic for prime divisors of `p² - 1` when `p` is odd.

This is the numerical final step in Bender--Glauberman Lemmas 4.13--4.14.
-/

namespace Submission.OddOrder.MathlibSupport

/-- An odd-prime square-minus-one divisor is smaller than the prime and
divides one of the two half-factors. -/
theorem prime_lt_and_dvd_half_factor_of_dvd_sq_sub_one
    {p q : ℕ} (hp : p.Prime) (hpodd : Odd p)
    (hq : q.Prime) (hqp : q ≠ p) (hdvd : q ∣ p ^ 2 - 1) :
    q < p ∧ (q ∣ (p + 1) / 2 ∨ q ∣ (p - 1) / 2) := by
  have hp3 : 3 ≤ p := hp.odd_iff.mp hpodd
  have hfactor : p ^ 2 - 1 = (p + 1) * (p - 1) := by
    simpa using (Nat.sq_sub_sq p 1)
  have hqfactor : q ∣ (p + 1) * (p - 1) := by
    rwa [← hfactor]
  have hsplit : q ∣ p + 1 ∨ q ∣ p - 1 := hq.dvd_or_dvd hqfactor
  constructor
  · rcases hsplit with hplus | hminus
    · have hqle : q ≤ p + 1 := Nat.le_of_dvd (by omega) hplus
      rcases hq.eq_two_or_odd' with hq2 | hqodd
      · rw [hq2]
        exact hp3
      · obtain ⟨a, ha⟩ := hpodd
        obtain ⟨b, hb⟩ := hqodd
        omega
    · have hqle : q ≤ p - 1 := Nat.le_of_dvd (by omega) hminus
      omega
  · rcases hq.eq_two_or_odd' with hq2 | hqodd
    · subst q
      obtain ⟨k, hk | hk⟩ := Nat.even_or_odd' ((p - 1) / 2)
      · right
        exact ⟨k, hk⟩
      · left
        refine ⟨k + 1, ?_⟩
        obtain ⟨a, ha⟩ := hpodd
        omega
    · have hcop : q.Coprime 2 := hqodd.coprime_two_right
      rcases hsplit with hplus | hminus
      · left
        apply hcop.dvd_of_dvd_mul_left
        have heq : 2 * ((p + 1) / 2) = p + 1 := by
          obtain ⟨a, ha⟩ := hpodd
          omega
        rwa [heq]
      · right
        apply hcop.dvd_of_dvd_mul_left
        have heq : 2 * ((p - 1) / 2) = p - 1 := by
          obtain ⟨a, ha⟩ := hpodd
          omega
        rwa [heq]

end Submission.OddOrder.MathlibSupport
