import ChallengeDeps

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Polynomial interpolation in submodules

Key lemma: if a "polynomial-like" function evaluated at 0, 1, ..., k takes values
in a submodule A for the nonzero inputs, then the value at 0 is also in A.
-/

open Finset

namespace Submission.Interpolation

variable {R : Type*} [Field R]

/-
The k-th finite difference of the monomial t^m at 0, for m < k, is 0.
    Σ_{j=0}^k (-1)^{k-j} C(k,j) j^m = 0 for m < k.
-/
lemma alternating_binom_pow_eq_zero (k m : ℕ) (hm : m < k) :
    ∑ j ∈ range (k + 1), (-1 : R) ^ (k - j) * (k.choose j : R) * (j : R) ^ m = 0 := by
  -- We'll use induction on $k$. The base case is when $k = 0$.
  induction' k with k ih generalizing m;
  · contradiction;
  · -- Apply the identity $\sum_{j=0}^{k+1} (-1)^{k+1-j} \binom{k+1}{j} j^m = \sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j} ( (j+1)^m - j^m )$.
    have h_identity : ∑ j ∈ Finset.range (k + 2), (-1 : R) ^ (k + 1 - j) * Nat.choose (k + 1) j * (j : R) ^ m = ∑ j ∈ Finset.range (k + 1), (-1 : R) ^ (k - j) * Nat.choose k j * ((j + 1 : R) ^ m - (j : R) ^ m) := by
      rw [ Finset.sum_range_succ' ];
      simp +decide [ Nat.choose_succ_succ, add_mul, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, pow_succ' ];
      rw [ Finset.sum_range_succ' ];
      rw [ Finset.sum_range_succ ] ; simp +decide [ Finset.sum_range_succ', pow_succ' ] ; ring;
      simp +decide [ add_comm, add_left_comm, add_assoc, sub_eq_add_neg ];
      rw [ ← Finset.sum_neg_distrib ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ show k - x = k - ( x + 1 ) + 1 from tsub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show x + 1 ≤ k from Finset.mem_range.mp hx ] ] ; ring;
    -- Notice that $(j + 1)^m - j^m$ is a polynomial of degree $m - 1$.
    have h_poly : ∀ j : ℕ, ((j + 1 : R) ^ m - (j : R) ^ m) = ∑ i ∈ Finset.range m, Nat.choose m i * (j : R) ^ i := by
      simp +decide [ add_pow, mul_comm ];
      simp +decide [ Finset.sum_range_succ ];
    rcases m with ( _ | m ) <;> simp_all +decide [ Finset.mul_sum _ _ _, mul_assoc, mul_left_comm, Finset.sum_mul ];
    rw [ Finset.sum_comm ];
    exact Finset.sum_eq_zero fun i hi => by simpa [ mul_assoc, mul_comm, mul_left_comm, Finset.mul_sum _ _ _ ] using mul_eq_zero_of_right ( Nat.choose ( m + 1 ) i : R ) ( ih i ( by linarith [ Finset.mem_range.mp hi ] ) ) ;

/-
Σ_{j=0}^k (-1)^{k-j} C(k,j) j^k = k!
-/
lemma alternating_binom_pow_eq_factorial (k : ℕ) :
    ∑ j ∈ range (k + 1), (-1 : R) ^ (k - j) * (k.choose j : R) * (j : R) ^ k =
    (k.factorial : R) := by
  -- We prove this by induction on $k$.
  induction' k with k ih;
  · norm_num;
  · -- We use the identity $\sum_{j=0}^{k+1} (-1)^{k+1-j} \binom{k+1}{j} j^{k+1} = \sum_{j=0}^{k} (-1)^{k-j} \binom{k}{j} ((j+1)^{k+1} - j^{k+1})$.
    have h_identity : ∑ j ∈ Finset.range (k + 2), (-1 : R) ^ (k + 1 - j) * (Nat.choose (k + 1) j : R) * (j : R) ^ (k + 1) = ∑ j ∈ Finset.range (k + 1), (-1 : R) ^ (k - j) * (Nat.choose k j : R) * ((j + 1 : R) ^ (k + 1) - (j : R) ^ (k + 1)) := by
      rw [ Finset.sum_range_succ' ];
      simp +decide [ Nat.choose_succ_succ, add_mul, mul_add, add_assoc, Finset.sum_add_distrib ];
      rw [ Finset.sum_range_succ' ];
      rw [ Finset.sum_range_succ ] ; simp +decide [ Finset.sum_range_succ', pow_succ' ] ; ring;
      rw [ ← Finset.sum_add_distrib ] ; refine' congr_arg₂ _ ( Finset.sum_congr rfl fun x hx => _ ) rfl ; rw [ show k - x = k - ( 1 + x ) + 1 from tsub_eq_of_eq_add <| by linarith [ Nat.sub_add_cancel <| show 1 + x ≤ k from by linarith [ Finset.mem_range.mp hx ] ] ] ; ring;
    -- We expand $(j+1)^{k+1}$ using the binomial theorem.
    have h_expand : ∑ j ∈ Finset.range (k + 1), (-1 : R) ^ (k - j) * (Nat.choose k j : R) * ((j + 1 : R) ^ (k + 1) - (j : R) ^ (k + 1)) = ∑ j ∈ Finset.range (k + 1), (-1 : R) ^ (k - j) * (Nat.choose k j : R) * ∑ m ∈ Finset.range (k + 1), Nat.choose (k + 1) m * (j : R) ^ m := by
      simp +decide [ add_pow, mul_comm, Finset.sum_range_succ ];
    -- We interchange the order of summation.
    have h_interchange : ∑ j ∈ Finset.range (k + 1), (-1 : R) ^ (k - j) * (Nat.choose k j : R) * ∑ m ∈ Finset.range (k + 1), Nat.choose (k + 1) m * (j : R) ^ m = ∑ m ∈ Finset.range (k + 1), Nat.choose (k + 1) m * ∑ j ∈ Finset.range (k + 1), (-1 : R) ^ (k - j) * (Nat.choose k j : R) * (j : R) ^ m := by
      simpa only [ mul_assoc, mul_left_comm, Finset.mul_sum _ _ _ ] using Finset.sum_comm;
    -- We apply the induction hypothesis to each term in the sum.
    have h_apply_ih : ∑ m ∈ Finset.range (k + 1), Nat.choose (k + 1) m * ∑ j ∈ Finset.range (k + 1), (-1 : R) ^ (k - j) * (Nat.choose k j : R) * (j : R) ^ m = Nat.choose (k + 1) k * ∑ j ∈ Finset.range (k + 1), (-1 : R) ^ (k - j) * (Nat.choose k j : R) * (j : R) ^ k := by
      rw [ Finset.sum_eq_single k ] <;> simp +contextual [ Nat.choose_eq_zero_of_lt ];
      exact fun m hm₁ hm₂ => Or.inr ( alternating_binom_pow_eq_zero k m ( lt_of_le_of_ne hm₁ hm₂ ) );
    simp_all +decide [ Nat.factorial_succ, mul_comm ]

/-
The module-valued interpolation: If Σ_{j=0}^{k} (-1)^{k-j} C(k,j) v_j = 0 in a module V,
    and v_1, ..., v_k ∈ A (a submodule), then v_0 ∈ A.
    Here v is indexed by `Fin (k + 1)`.
-/
lemma mem_submodule_of_alternating_sum_zero {V : Type*} [AddCommGroup V] [Module R V]
    (A : Submodule R V) (k : ℕ) (v : Fin (k + 1) → V)
    (hsum : ∑ j : Fin (k + 1),
      ((-1 : R) ^ (k - (j : ℕ)) * (k.choose (j : ℕ) : R)) • v j = 0)
    (hv : ∀ j : Fin (k + 1), (j : ℕ) ≠ 0 → v j ∈ A) :
    v 0 ∈ A := by
  simp_all +decide [ Fin.sum_univ_succ ];
  -- Since the sum is in A, we can isolate v 0.
  have h_isolate : (-1 : R) ^ k • v 0 = -∑ x : Fin k, ((-1) ^ (k - (x.val + 1)) * (k.choose (x.val + 1) : R)) • v (Fin.succ x) := by
    exact eq_neg_of_add_eq_zero_left hsum;
  convert A.smul_mem ( ( -1 : R ) ^ k )⁻¹ ( A.neg_mem ( A.sum_mem fun x _ => A.smul_mem ( ( -1 : R ) ^ ( k - ( x.val + 1 ) ) * k.choose ( x.val + 1 ) ) ( hv _ ( ne_of_gt ( Fin.succ_pos x ) ) ) ) ) using 1 ; simp +decide [ h_isolate ];
  rw [ ← smul_neg, ← h_isolate, smul_smul ] ; norm_num

end Submission.Interpolation
