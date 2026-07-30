import Mathlib

open scoped BigOperators Nat
open Polynomial Filter Finset

namespace Submission.Helpers

noncomputable section

theorem minpoly_eval_zero_ne {x : ℂ} (hx : IsIntegral ℤ x) (hx0 : x ≠ 0) :
    (minpoly ℤ x).eval 0 ≠ 0 := by
  intro h0
  have hdiv : (X : ℤ[X]) ∣ minpoly ℤ x := by
    simpa using dvd_iff_isRoot.mpr h0
  have hassoc : Associated (X : ℤ[X]) (minpoly ℤ x) :=
    irreducible_X.associated_of_dvd (minpoly.irreducible hx) hdiv
  obtain ⟨u, hu⟩ := hassoc.dvd'
  apply hx0
  calc
    x = aeval x (X : ℤ[X]) := by simp
    _ = aeval x ((minpoly ℤ x) * u) := by rw [hu]
    _ = 0 := by rw [map_mul, minpoly.aeval, zero_mul]

theorem no_integral_relation_exp (b : ℂ →₀ ℤ)
    (hb0 : b 0 ≠ 0)
    (hint : ∀ x ∈ b.support.erase 0, IsIntegral ℤ x)
    (hrel : (b 0 : ℂ) +
      ∑ x ∈ b.support.erase 0, (b x : ℂ) * Complex.exp x = 0)
    (hmoment : ∀ g : ℤ[X], ∃ z : ℤ,
      (z : ℂ) = ∑ x ∈ b.support.erase 0, (b x : ℂ) * aeval x g) : False := by
  let s := b.support.erase 0
  let f : ℤ[X] := ∏ x ∈ s, minpoly ℤ x
  have hs0 : ∀ x ∈ s, x ≠ 0 := fun x hx ↦ (Finset.mem_erase.mp hx).1
  have hf0 : f.eval 0 ≠ 0 := by
    simp only [f, eval_prod, Finset.prod_ne_zero_iff]
    exact fun x hx ↦ minpoly_eval_zero_ne (hint x hx) (hs0 x hx)
  obtain ⟨c, hc⟩ := LindemannWeierstrass.exp_polynomial_approx f hf0
  let A : ℝ := ∑ x ∈ s, |(b x : ℝ)|
  have hsmall : ∀ᶠ p : ℕ in atTop, A * |c| ^ p / (p - 1)! < 1 :=
    (FloorSemiring.tendsto_mul_pow_div_factorial_sub_atTop A |c| 1).eventually_lt_const
      zero_lt_one
  rw [eventually_atTop] at hsmall
  obtain ⟨N, hN⟩ := hsmall
  obtain ⟨p, hpN, hp⟩ := Nat.exists_infinite_primes
    (max N (max (f.eval 0).natAbs.succ (b 0).natAbs.succ))
  have hp_large_f : (f.eval 0).natAbs < p := by omega
  have hp_large_b0 : (b 0).natAbs < p := by omega
  obtain ⟨n, hpn, g, _hgdeg, hg⟩ := hc p hp_large_f hp
  obtain ⟨z, hz⟩ := hmoment g
  let w : ℤ := n * b 0 + (p : ℤ) * z
  have hw_ne : w ≠ 0 := by
    intro hw
    have hpd : (p : ℤ) ∣ n * b 0 := by
      refine ⟨-z, ?_⟩
      dsimp [w] at hw
      linear_combination hw
    have hpd' : p ∣ n.natAbs * (b 0).natAbs := by
      simpa only [Int.natAbs_mul] using Int.natCast_dvd.mp hpd
    rcases hp.dvd_mul.mp hpd' with hn | hb
    · exact hpn (Int.natCast_dvd.mpr hn)
    · exact (not_le_of_gt hp_large_b0) (Nat.le_of_dvd (Int.natAbs_pos.mpr hb0) hb)
  have hrel' : ∑ x ∈ s, (b x : ℂ) * Complex.exp x = -(b 0 : ℂ) := by
    dsimp [s]
    linear_combination hrel
  have hw_cast : (w : ℂ) =
      ∑ x ∈ s, (b x : ℂ) * ((p : ℂ) * aeval x g - (n : ℂ) * Complex.exp x) := by
    calc
      (w : ℂ) = (n : ℂ) * (b 0 : ℂ) + (p : ℂ) * (z : ℂ) := by
        simp only [w, Int.cast_add, Int.cast_mul, Int.cast_natCast]
      _ = (n : ℂ) * (b 0 : ℂ) +
          (p : ℂ) * ∑ x ∈ s, (b x : ℂ) * aeval x g := by rw [hz]
      _ = (p : ℂ) * ∑ x ∈ s, (b x : ℂ) * aeval x g -
          (n : ℂ) * ∑ x ∈ s, (b x : ℂ) * Complex.exp x := by rw [hrel']; ring
      _ = ∑ x ∈ s, (b x : ℂ) *
          ((p : ℂ) * aeval x g - (n : ℂ) * Complex.exp x) := by
            simp_rw [mul_sum]
            rw [← Finset.sum_sub_distrib]
            apply Finset.sum_congr rfl
            intro x hx
            ring
  have hbound : ‖(w : ℂ)‖ ≤ A * |c| ^ p / (p - 1)! := by
    rw [hw_cast]
    refine (norm_sum_le _ _).trans ?_
    dsimp [A]
    rw [Finset.sum_mul, Finset.sum_div]
    apply Finset.sum_le_sum
    intro x hx
    have hxroot : x ∈ f.aroots ℂ := by
      rw [mem_aroots]
      constructor
      · intro hf
        exact hf0 (by rw [hf]; simp)
      · rw [map_prod]
        apply Finset.prod_eq_zero hx
        exact minpoly.aeval ℤ x
    have hxapprox := hg hxroot
    simp only [zsmul_eq_mul, nsmul_eq_mul] at hxapprox
    calc
      ‖(b x : ℂ) * ((p : ℂ) * aeval x g - (n : ℂ) * Complex.exp x)‖ =
          |(b x : ℝ)| * ‖(n : ℂ) * Complex.exp x - (p : ℂ) * aeval x g‖ := by
            rw [norm_mul]
            have hnorm : ‖(p : ℂ) * aeval x g - (n : ℂ) * Complex.exp x‖ =
                ‖(n : ℂ) * Complex.exp x - (p : ℂ) * aeval x g‖ := by
              rw [← norm_neg]
              congr 1
              ring
            rw [hnorm]
            norm_cast
      _ ≤ |(b x : ℝ)| * (c ^ p / (p - 1)!) :=
        mul_le_mul_of_nonneg_left hxapprox (abs_nonneg _)
      _ ≤ |(b x : ℝ)| * |c| ^ p / (p - 1)! := by
        rw [mul_div_assoc]
        apply mul_le_mul_of_nonneg_left
        · apply div_le_div_of_nonneg_right
          exact (le_abs_self (c ^ p)).trans_eq (abs_pow c p)
          positivity
        · exact abs_nonneg _
  have hone : (1 : ℝ) ≤ ‖(w : ℂ)‖ := by
    rw [Complex.norm_intCast]
    norm_cast
    exact (Int.add_one_le_iff).2 (abs_pos.mpr hw_ne)
  exact (not_lt_of_ge hone) (hbound.trans_lt (hN p (le_trans (le_max_left _ _) hpN)))

end

end Submission.Helpers
