import Mathlib

open Polynomial Complex

namespace Submission.Helpers

set_option maxHeartbeats 800000 in
lemma coeff_norm_le_of_eval_norm_le (Q : ℂ[X]) (n : ℕ) (hn : Q.natDegree ≤ n)
    (hQ : ∀ z : Circle, ‖Q.eval (z : ℂ)‖ ≤ 1) (k : ℕ) :
    ‖Q.coeff k‖ ≤ 1 := by
  by_cases hk : Q.natDegree < k
  · rw [Polynomial.coeff_eq_zero_of_natDegree_lt hk, norm_zero]; positivity
  push_neg at hk
  -- Let N = n + 1 and ω = exp(2πi/N). Then ω is a primitive N-th root of unity.
  set N := n + 1
  set ω := Complex.exp (2 * Real.pi * Complex.I / N) with hω_def
  have hω_prim : IsPrimitiveRoot ω N := by
    exact Complex.isPrimitiveRoot_exp _ ( by aesop );
  -- Key DFT identity: N * Q.coeff k = ∑ j ∈ Finset.range N, Q(ω^j) * (ω^j)⁻¹^k
  have h_dft : N * Q.coeff k = ∑ j ∈ Finset.range N, Q.eval (ω ^ j) * (ω ^ j)⁻¹ ^ k := by
    -- By the properties of the roots of unity, we can rewrite the sum as:
    have h_sum_rewrite : ∑ j ∈ Finset.range N, Q.eval (ω ^ j) * (ω ^ j)⁻¹ ^ k = ∑ i ∈ Finset.range (n + 1), Q.coeff i * ∑ j ∈ Finset.range N, (ω ^ j) ^ (i - k : ℤ) := by
      have h_sum_rewrite : ∑ j ∈ Finset.range N, Q.eval (ω ^ j) * (ω ^ j)⁻¹ ^ k = ∑ j ∈ Finset.range N, ∑ i ∈ Finset.range (n + 1), Q.coeff i * (ω ^ j) ^ (i - k : ℤ) := by
        have h_sum_rewrite : ∀ j ∈ Finset.range N, Q.eval (ω ^ j) = ∑ i ∈ Finset.range (n + 1), Q.coeff i * (ω ^ j) ^ i := by
          intro j hj; rw [ Polynomial.eval_eq_sum_range' ] ; aesop;
        refine' Finset.sum_congr rfl fun j hj => _;
        rw [ h_sum_rewrite j hj, Finset.sum_mul _ _ _ ] ; refine' Finset.sum_congr rfl fun i hi => _ ; norm_num [ zpow_sub₀, show ω ≠ 0 from Complex.exp_ne_zero _ ] ; ring;
      rw [ h_sum_rewrite, Finset.sum_comm, Finset.sum_congr rfl fun _ _ => Finset.mul_sum _ _ _ ];
    -- For $i \neq k$, $\sum_{j=0}^{N-1} (\omega^j)^{i-k} = 0$ because it is a geometric series with common ratio $\omega^{i-k}$.
    have h_geo_series : ∀ i ∈ Finset.range (n + 1), i ≠ k → ∑ j ∈ Finset.range N, (ω ^ j) ^ (i - k : ℤ) = 0 := by
      intros i hi hik
      have h_geo_series : ∑ j ∈ Finset.range N, (ω ^ (i - k : ℤ)) ^ j = 0 := by
        rw [ geom_sum_eq ] <;> norm_num [ hω_prim.pow_eq_one ];
        · exact Or.inl ( by rw [ ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hω_prim.pow_eq_one, one_zpow, sub_self ] );
        · have := hω_prim.zpow_eq_one_iff_dvd ( i - k );
          simp +zetaDelta at *;
          exact fun h => hik <| by obtain ⟨ a, ha ⟩ := this.mp h; nlinarith [ show a = 0 by nlinarith ] ;
      convert h_geo_series using 2 ; group;
    rw [ h_sum_rewrite, Finset.sum_eq_single k ] <;> norm_num [ h_geo_series ];
    · ring;
    · exact fun i hi hi' => Or.inr <| h_geo_series i ( Finset.mem_range.mpr <| by linarith ) hi';
    · grind +splitIndPred;
  -- Since $ω^j$ is on the unit circle, we have $‖Q(ω^j)‖ ≤ 1$.
  have h_unit_circle : ∀ j ∈ Finset.range N, ‖Q.eval (ω ^ j)‖ ≤ 1 := by
    intro j hj; convert hQ ⟨ ω ^ j, _ ⟩ ;
    simp +decide [ Submonoid.unitSphere, Complex.norm_exp ];
    norm_num [ hω_def, Complex.norm_exp ];
  -- Applying the triangle inequality to the sum, we get $‖N * Q.coeff k‖ ≤ ∑ j ∈ Finset.range N, ‖Q(ω^j) * (ω^j)⁻¹^k‖$.
  have h_triangle : ‖N * Q.coeff k‖ ≤ ∑ j ∈ Finset.range N, ‖Q.eval (ω ^ j) * (ω ^ j)⁻¹ ^ k‖ := by
    exact h_dft ▸ norm_sum_le _ _;
  simp_all +decide [ Complex.norm_exp ];
  rw [ ← h_dft, norm_mul ] at h_triangle ; norm_cast at * ; simp_all +decide [ Nat.succ_eq_add_one ];
  norm_num +zetaDelta at *;
  exact le_of_not_gt fun h => by have := Finset.sum_le_sum fun i ( hi : i ∈ Finset.range ( n + 1 ) ) => h_unit_circle i ( Finset.mem_range_succ_iff.mp hi ) ; norm_num at * ; nlinarith;

end Submission.Helpers