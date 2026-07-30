import Mathlib

open Polynomial Complex

namespace Submission.Helpers

/-! ## Conjugate-reciprocal polynomial -/

/-- Conjugate-reciprocal of a complex polynomial. -/
noncomputable def Pstar (P : ℂ[X]) : ℂ[X] := (P.map (starRingEnd ℂ)).mirror

@[simp] lemma Pstar_zero : Pstar 0 = 0 := by simp [Pstar]

lemma natDegree_Pstar (P : ℂ[X]) : (Pstar P).natDegree = P.natDegree := by
  unfold Pstar; rw [mirror_natDegree, natDegree_map]

private lemma natTrailingDegree_map_starRingEnd (P : ℂ[X]) :
    (P.map (starRingEnd ℂ)).natTrailingDegree = P.natTrailingDegree := by
  by_cases hP : P = 0
  · simp [hP]
  have hmap_ne : P.map (starRingEnd ℂ) ≠ 0 := by
    rwa [Ne, Polynomial.map_eq_zero_iff (RingHom.injective _)]
  apply le_antisymm
  · apply natTrailingDegree_le_of_ne_zero
    rw [Polynomial.coeff_map]
    have hne : P.coeff P.natTrailingDegree ≠ 0 := trailingCoeff_nonzero_iff_nonzero.mpr hP
    intro h
    have hinj : Function.Injective (starRingEnd ℂ) := RingHom.injective _
    exact hne (hinj (by simpa using h))
  · apply natTrailingDegree_le_of_ne_zero
    have hne : (P.map (starRingEnd ℂ)).coeff (P.map (starRingEnd ℂ)).natTrailingDegree ≠ 0 :=
      trailingCoeff_nonzero_iff_nonzero.mpr hmap_ne
    rw [Polynomial.coeff_map] at hne
    intro h
    exact hne (by rw [h]; simp)

lemma coeff_Pstar (P : ℂ[X]) (k : ℕ) :
    (Pstar P).coeff k =
      starRingEnd ℂ (P.coeff (revAt (P.natDegree + P.natTrailingDegree) k)) := by
  unfold Pstar
  rw [coeff_mirror, natDegree_map, natTrailingDegree_map_starRingEnd, Polynomial.coeff_map]

/-- The conjugate-reciprocal polynomial evaluated on the unit circle. -/
lemma Pstar_eval_on_circle (P : ℂ[X]) {z : ℂ} (hz : ‖z‖ = 1) :
    (Pstar P).eval z =
      z ^ (P.natDegree + P.natTrailingDegree) * starRingEnd ℂ (P.eval z) := by
  set N := P.natDegree + P.natTrailingDegree with hN
  have hz_ne : z ≠ 0 := by
    intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hconj : starRingEnd ℂ z = z⁻¹ := by
    have h2 : Complex.normSq z = 1 := by
      rw [Complex.normSq_eq_norm_sq, hz]; norm_num
    have h3 : starRingEnd ℂ z * z = 1 := by
      have := Complex.mul_conj z
      simp [h2] at this
      linear_combination this
    field_simp; linear_combination h3
  -- Evaluate (Pstar P) as a sum over range (N+1).
  have hbound : (Pstar P).natDegree ≤ N :=
    (natDegree_Pstar P).le.trans (Nat.le_add_right _ _)
  have heval : (Pstar P).eval z =
      ∑ k ∈ Finset.range (N + 1), (Pstar P).coeff k * z ^ k :=
    eval_eq_sum_range' (Nat.lt_succ_of_le hbound) z
  -- Evaluate P as a sum over range (N+1).
  have hPbound : P.natDegree ≤ N := Nat.le_add_right _ _
  have hevalP : P.eval z = ∑ k ∈ Finset.range (N + 1), P.coeff k * z ^ k :=
    eval_eq_sum_range' (Nat.lt_succ_of_le hPbound) z
  -- conj of P.eval z.
  have hconjP : starRingEnd ℂ (P.eval z) =
      ∑ k ∈ Finset.range (N + 1), starRingEnd ℂ (P.coeff k) * z⁻¹ ^ k := by
    rw [hevalP, map_sum]
    apply Finset.sum_congr rfl
    intros k _
    rw [map_mul, map_pow, hconj]
  rw [heval, hconjP, Finset.mul_sum]
  -- Now we need a sum reindexing.
  -- LHS sum: ∑_k (Pstar P).coeff k * z^k = ∑_k conj(P.coeff (N-k)) * z^k
  -- RHS sum: ∑_k z^N * (conj(P.coeff k) * z⁻¹^k) = ∑_k conj(P.coeff k) * z^(N-k)
  -- Both equal by the change of variable k ↦ N - k.
  rw [show (∑ k ∈ Finset.range (N + 1), z ^ N * (starRingEnd ℂ (P.coeff k) * z⁻¹ ^ k))
        = ∑ k ∈ Finset.range (N + 1), starRingEnd ℂ (P.coeff k) * z ^ (N - k) by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range, Nat.lt_succ_iff] at hk
      rw [show z ^ N * (starRingEnd ℂ (P.coeff k) * z⁻¹ ^ k)
            = starRingEnd ℂ (P.coeff k) * (z ^ N * z⁻¹ ^ k) by ring]
      congr 1
      rw [inv_pow, ← pow_sub₀ z hz_ne hk]]
  -- And LHS:
  rw [show (∑ k ∈ Finset.range (N + 1), (Pstar P).coeff k * z ^ k)
        = ∑ k ∈ Finset.range (N + 1), starRingEnd ℂ (P.coeff (N - k)) * z ^ k by
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_range, Nat.lt_succ_iff] at hk
      have hk' : k ≤ P.natDegree + P.natTrailingDegree := hk
      rw [coeff_Pstar, revAt_le hk']]
  -- Now reindex j = N - k.
  have hreflect := @Finset.sum_range_reflect ℂ _
    (fun k => starRingEnd ℂ (P.coeff k) * z ^ (N - k)) (N + 1)
  rw [show N + 1 - 1 = N from rfl] at hreflect
  rw [← hreflect]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  rw [Nat.sub_sub_self hk]

/-! ## Multiplicativity and basic identities -/

lemma Pstar_mul (P Q : ℂ[X]) : Pstar (P * Q) = Pstar P * Pstar Q := by
  unfold Pstar
  rw [Polynomial.map_mul, mirror_mul_of_domain]

lemma Pstar_one : Pstar 1 = 1 := by
  unfold Pstar
  rw [Polynomial.map_one]
  exact mirror_C 1

lemma Pstar_C (c : ℂ) : Pstar (C c) = C (starRingEnd ℂ c) := by
  unfold Pstar
  rw [Polynomial.map_C]
  exact mirror_C _

lemma Pstar_X : Pstar (X : ℂ[X]) = X := by
  unfold Pstar
  rw [Polynomial.map_X]
  exact mirror_X

lemma Pstar_X_pow (m : ℕ) : Pstar (X ^ m : ℂ[X]) = X ^ m := by
  induction m with
  | zero => rw [pow_zero, Pstar_one]
  | succ m ih => rw [pow_succ, Pstar_mul, ih, Pstar_X]

/-- Trailing degree of `Pstar P` equals trailing degree of `P`. -/
lemma natTrailingDegree_Pstar (P : ℂ[X]) :
    (Pstar P).natTrailingDegree = P.natTrailingDegree := by
  unfold Pstar
  rw [mirror_natTrailingDegree, natTrailingDegree_map_starRingEnd]

/-- `Pstar` is an involution on `ℂ[X]`. -/
lemma Pstar_Pstar (P : ℂ[X]) : Pstar (Pstar P) = P := by
  ext n
  rw [coeff_Pstar, coeff_Pstar, natDegree_Pstar, natTrailingDegree_Pstar,
      revAt_invol]
  simp

/-! ## X-power factoring -/

/-- Any nonzero `P : ℂ[X]` factors as `X^m * P₀` where `m = natTrailingDegree P`,
    `P₀ ≠ 0`, `P₀.coeff 0 ≠ 0`, and `P₀.natDegree = P.natDegree - m`. -/
lemma X_pow_natTrailingDegree_mul_split (P : ℂ[X]) (hP : P ≠ 0) :
    ∃ P₀ : ℂ[X],
      P = X ^ P.natTrailingDegree * P₀ ∧
      P₀ ≠ 0 ∧
      P₀.coeff 0 ≠ 0 ∧
      P₀.natTrailingDegree = 0 ∧
      P₀.natDegree = P.natDegree - P.natTrailingDegree := by
  -- X^m | P since coefficients below m are zero.
  have hmonic : Monic (X ^ P.natTrailingDegree : ℂ[X]) := monic_X_pow _
  have hdvd : (X ^ P.natTrailingDegree : ℂ[X]) ∣ P := by
    rw [X_pow_dvd_iff]
    intro d hd
    exact coeff_eq_zero_of_lt_natTrailingDegree hd
  obtain ⟨P₀, hP₀⟩ := hdvd
  refine ⟨P₀, hP₀, ?_, ?_, ?_, ?_⟩
  · -- P₀ ≠ 0
    intro h
    apply hP
    rw [hP₀, h, mul_zero]
  · -- P₀.coeff 0 ≠ 0
    have hcoef : P.coeff P.natTrailingDegree = P₀.coeff 0 := by
      have h1 : P.coeff P.natTrailingDegree
                = (X ^ P.natTrailingDegree * P₀).coeff P.natTrailingDegree := by
        rw [← hP₀]
      rw [h1]
      have h2 := coeff_X_pow_mul P₀ P.natTrailingDegree 0
      rw [zero_add] at h2
      exact h2
    rw [← hcoef]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hP
  · -- natTrailingDegree P₀ = 0
    rw [natTrailingDegree_eq_zero]
    right
    have hcoef : P.coeff P.natTrailingDegree = P₀.coeff 0 := by
      have h1 : P.coeff P.natTrailingDegree
                = (X ^ P.natTrailingDegree * P₀).coeff P.natTrailingDegree := by
        rw [← hP₀]
      rw [h1]
      have h2 := coeff_X_pow_mul P₀ P.natTrailingDegree 0
      rw [zero_add] at h2
      exact h2
    rw [← hcoef]
    exact trailingCoeff_nonzero_iff_nonzero.mpr hP
  · -- P₀.natDegree
    have hp0_ne : P₀ ≠ 0 := by
      intro h; apply hP; rw [hP₀, h, mul_zero]
    have hxpow_ne : (X ^ P.natTrailingDegree : ℂ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
    have hsum : P.natDegree = P.natTrailingDegree + P₀.natDegree := by
      conv_lhs => rw [hP₀]
      rw [natDegree_mul hxpow_ne hp0_ne, natDegree_X_pow]
    omega

/-! ## The defect polynomial `G = X^n − P · Pstar P` -/

/-- The polynomial whose factorization yields the complementary polynomial. -/
noncomputable def Gpoly (P : ℂ[X]) : ℂ[X] := X ^ P.natDegree - P * Pstar P

/-- Evaluation of `Gpoly P` at points on the unit circle (assuming
    `natTrailingDegree P = 0`). -/
lemma Gpoly_eval_on_circle (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (Gpoly P).eval z = z ^ P.natDegree * (1 - ‖P.eval z‖ ^ 2) := by
  unfold Gpoly
  rw [eval_sub, eval_pow, eval_X, eval_mul, Pstar_eval_on_circle P hz,
      hT, add_zero]
  -- LHS: z^n - P(z) · (z^n · conj(P(z)))
  rw [show z ^ P.natDegree * starRingEnd ℂ (P.eval z)
       = z ^ P.natDegree * starRingEnd ℂ (P.eval z) from rfl]
  have hsq : P.eval z * (z ^ P.natDegree * starRingEnd ℂ (P.eval z))
           = z ^ P.natDegree * (P.eval z * starRingEnd ℂ (P.eval z)) := by ring
  rw [hsq]
  have habs : P.eval z * starRingEnd ℂ (P.eval z) = (‖P.eval z‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj]
    rw [Complex.normSq_eq_norm_sq]
    push_cast
    ring
  rw [habs]
  ring

/-- `P · Pstar P` is self-Pstar. -/
lemma Pstar_P_mul_Pstar_P (P : ℂ[X]) : Pstar (P * Pstar P) = P * Pstar P := by
  rw [Pstar_mul, Pstar_Pstar, mul_comm]

/-- A polynomial `R` is **conjugate-palindromic of degree `N`** if
`R.coeff k = conj (R.coeff (N - k))` for all `k ≤ N`, and `R.natDegree ≤ N`.

This is the algebraic statement of self-reciprocity that underlies the
Fejér–Riesz factorization: `Gpoly P` is conjugate-palindromic of degree
`2 · natDegree P`. -/
def IsConjPalindromic (R : ℂ[X]) (N : ℕ) : Prop :=
  R.natDegree ≤ N ∧ ∀ k ≤ N, R.coeff k = starRingEnd ℂ (R.coeff (N - k))

lemma X_pow_isConjPalindromic_two_natDegree (P : ℂ[X]) :
    IsConjPalindromic (X ^ P.natDegree : ℂ[X]) (2 * P.natDegree) := by
  refine ⟨by rw [natDegree_X_pow]; omega, ?_⟩
  intro k hk
  simp only [Polynomial.coeff_X_pow]
  by_cases h1 : k = P.natDegree
  · subst h1
    simp [show 2 * P.natDegree - P.natDegree = P.natDegree by omega]
  · simp [h1]
    intro hk2
    omega

/-- For `natTrailingDegree P = 0`, `P · Pstar P` has trailing degree zero. -/
lemma natTrailingDegree_P_mul_Pstar_P (P : ℂ[X]) (hP : P ≠ 0)
    (hT : P.natTrailingDegree = 0) :
    (P * Pstar P).natTrailingDegree = 0 := by
  have hPs : Pstar P ≠ 0 := by
    intro h
    unfold Pstar at h
    rw [mirror_eq_zero] at h
    exact hP (by rwa [Polynomial.map_eq_zero_iff (RingHom.injective _)] at h)
  rw [natTrailingDegree_mul hP hPs, hT, natTrailingDegree_Pstar, hT]

/-- For `natTrailingDegree P = 0` and `P ≠ 0`, the natDegree of `P · Pstar P` is `2n`. -/
lemma natDegree_P_mul_Pstar_P (P : ℂ[X]) (hP : P ≠ 0)
    (hT : P.natTrailingDegree = 0) :
    (P * Pstar P).natDegree = 2 * P.natDegree := by
  have hPs : Pstar P ≠ 0 := by
    intro h
    unfold Pstar at h
    rw [mirror_eq_zero] at h
    exact hP (by rwa [Polynomial.map_eq_zero_iff (RingHom.injective _)] at h)
  rw [natDegree_mul hP hPs, natDegree_Pstar, two_mul]

/-- `IsConjPalindromic` is closed under subtraction (same degree bound). -/
lemma IsConjPalindromic.sub {R₁ R₂ : ℂ[X]} {N : ℕ}
    (h₁ : IsConjPalindromic R₁ N) (h₂ : IsConjPalindromic R₂ N) :
    IsConjPalindromic (R₁ - R₂) N := by
  refine ⟨?_, ?_⟩
  · exact (natDegree_sub_le _ _).trans (max_le h₁.1 h₂.1)
  intro k hk
  rw [Polynomial.coeff_sub, Polynomial.coeff_sub, h₁.2 k hk, h₂.2 k hk, map_sub]

/-- The product `P · Pstar P` is conjugate-palindromic of degree `2 · natDegree P`,
provided `P` has `natTrailingDegree = 0`. -/
lemma P_mul_Pstar_isConjPalindromic (P : ℂ[X])
    (hT : P.natTrailingDegree = 0) :
    IsConjPalindromic (P * Pstar P) (2 * P.natDegree) := by
  by_cases hP : P = 0
  · -- P = 0 case: everything is zero.
    refine ⟨?_, ?_⟩
    · simp [hP]
    · intro k _; simp [hP]
  -- P ≠ 0 case
  have hPs : Pstar P ≠ 0 := by
    intro h
    unfold Pstar at h
    rw [mirror_eq_zero] at h
    exact hP (by rwa [Polynomial.map_eq_zero_iff (RingHom.injective _)] at h)
  have hND := natDegree_P_mul_Pstar_P P hP hT
  have hTD := natTrailingDegree_P_mul_Pstar_P P hP hT
  refine ⟨hND.le, ?_⟩
  intro k hk
  -- Use Pstar(P · Pstar P) = P · Pstar P. Then coeff_Pstar gives the desired identity.
  have hSelf : Pstar (P * Pstar P) = P * Pstar P := Pstar_P_mul_Pstar_P P
  -- Apply coeff at k:
  have hcoeff : (Pstar (P * Pstar P)).coeff k = (P * Pstar P).coeff k := by
    rw [hSelf]
  rw [coeff_Pstar, hND, hTD, add_zero] at hcoeff
  -- hcoeff : conj((P · Pstar P).coeff (revAt (2n) k)) = (P · Pstar P).coeff k
  rw [revAt_le hk] at hcoeff
  -- Now hcoeff : conj((P · Pstar P).coeff (2n - k)) = (P · Pstar P).coeff k
  exact hcoeff.symm

/-- `Gpoly P = X^(natDegree P) - P · Pstar P` is conjugate-palindromic of degree `2 · natDegree P`,
provided `natTrailingDegree P = 0`. -/
lemma Gpoly_isConjPalindromic (P : ℂ[X])
    (hT : P.natTrailingDegree = 0) :
    IsConjPalindromic (Gpoly P) (2 * P.natDegree) := by
  unfold Gpoly
  exact (X_pow_isConjPalindromic_two_natDegree P).sub
    (P_mul_Pstar_isConjPalindromic P hT)

/-- For `natDegree P = n ≥ 1`, `P(0) ≠ 0`, the natDegree of `Gpoly P` is exactly `2n`. -/
lemma natDegree_Gpoly (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hn : 1 ≤ P.natDegree) :
    (Gpoly P).natDegree = 2 * P.natDegree := by
  have hP : P ≠ 0 := by
    intro h; rw [h, natDegree_zero] at hn; omega
  set n := P.natDegree with hndef
  -- Gpoly P = X^n - P · Pstar P. Leading term comes from -P · Pstar P at degree 2n.
  -- Leading coeff of P · Pstar P = leadingCoeff P * leadingCoeff (Pstar P)
  --                              = leadingCoeff P * trailingCoeff (P.map conj)
  --                              = leadingCoeff P * conj(P.coeff 0)
  have hPs_ne : Pstar P ≠ 0 := by
    intro h
    unfold Pstar at h
    rw [mirror_eq_zero] at h
    exact hP (by rwa [Polynomial.map_eq_zero_iff (RingHom.injective _)] at h)
  have hPPs : (P * Pstar P).natDegree = 2 * n := by
    rw [natDegree_mul hP hPs_ne, natDegree_Pstar]; omega
  have hXn : ((X : ℂ[X]) ^ n).natDegree = n := natDegree_X_pow n
  -- Now natDegree (Gpoly P) = natDegree (X^n - P · Pstar P).
  -- Since 2n > n (when n ≥ 1), the subtraction has natDegree = 2n.
  unfold Gpoly
  -- `natDegree_sub_eq_right_of_natDegree_lt` needs the *first* argument to have smaller degree.
  have : (X ^ n - P * Pstar P : ℂ[X]).natDegree = (P * Pstar P).natDegree := by
    rw [show ((X : ℂ[X]) ^ n - P * Pstar P) = - (P * Pstar P) + X ^ n by ring]
    rw [add_comm]
    -- now X^n + (-(P · Pstar P)). natDegree of sum where second's natDegree > first's.
    have h1 : ((X : ℂ[X]) ^ n).natDegree < (-(P * Pstar P)).natDegree := by
      rw [natDegree_neg, hPPs, hXn]; omega
    rw [natDegree_add_eq_right_of_natDegree_lt h1, natDegree_neg]
  rw [this, hPPs]

/-- For `natTrailingDegree P = 0` and `P ≠ 0`, the natTrailingDegree of `Gpoly P` is 0. -/
lemma natTrailingDegree_Gpoly (P : ℂ[X]) (hP : P ≠ 0)
    (hT : P.natTrailingDegree = 0) (hn : 1 ≤ P.natDegree) :
    (Gpoly P).natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero]
  right
  -- (Gpoly P).coeff 0 = (X^n).coeff 0 - (P · Pstar P).coeff 0 = 0 - a₀ · conj(a_n) = -a₀ · conj(a_n)
  -- This is nonzero since a₀ ≠ 0 (hT) and a_n ≠ 0 (P ≠ 0, natDegree = n).
  unfold Gpoly
  rw [Polynomial.coeff_sub, Polynomial.coeff_X_pow]
  by_cases hn0 : (0 : ℕ) = P.natDegree
  · -- contradiction: hn0 says natDegree = 0, but hn says ≥ 1.
    omega
  rw [if_neg hn0]
  simp only [zero_sub, neg_ne_zero]
  -- Need: (P · Pstar P).coeff 0 ≠ 0.
  -- (P · Pstar P).coeff 0 = P.coeff 0 · (Pstar P).coeff 0
  --                      = a₀ · conj(P.coeff (n - 0)) = a₀ · conj(a_n).
  rw [coeff_mul, Finset.Nat.antidiagonal_zero, Finset.sum_singleton]
  rw [coeff_Pstar, hT, add_zero]
  rw [show (revAt P.natDegree) 0 = P.natDegree by
    rw [revAt_le (by omega : 0 ≤ P.natDegree)]; omega]
  -- Now: a₀ · conj(a_n) ≠ 0.
  have ha0 : P.coeff 0 ≠ 0 := by
    have := trailingCoeff_nonzero_iff_nonzero.mpr hP
    rwa [trailingCoeff, hT] at this
  have han : P.coeff P.natDegree ≠ 0 := by
    have := leadingCoeff_ne_zero.mpr hP
    rwa [leadingCoeff] at this
  intro h
  rcases mul_eq_zero.mp h with h | h
  · exact ha0 h
  · -- starRingEnd ℂ (a_n) = 0 → a_n = 0
    apply han
    have : starRingEnd ℂ (P.coeff P.natDegree) = starRingEnd ℂ 0 := by
      rw [h, map_zero]
    exact (RingHom.injective _) this

/-- Self-Pstar of `Gpoly P` under the standard hypotheses. -/
lemma Pstar_Gpoly (P : ℂ[X]) (hP : P ≠ 0) (hT : P.natTrailingDegree = 0)
    (hn : 1 ≤ P.natDegree) :
    Pstar (Gpoly P) = Gpoly P := by
  ext k
  rw [coeff_Pstar]
  have h_pal := (Gpoly_isConjPalindromic P hT).2
  rw [natDegree_Gpoly P hT hn, natTrailingDegree_Gpoly P hP hT hn, add_zero]
  by_cases hk : k ≤ 2 * P.natDegree
  · rw [revAt_le hk]
    exact ((h_pal k hk).symm).symm.symm
  · push_neg at hk
    rw [revAt_eq_self_of_lt hk]
    -- coeff at k > 2n: both Pstar G and G have coeff 0 there.
    -- starRingEnd preserves 0.
    have hG : (Gpoly P).natDegree = 2 * P.natDegree := natDegree_Gpoly P hT hn
    have hgk : (Gpoly P).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hG]; omega
    rw [hgk, map_zero]

/-! ## Root pairing under `ρ ↦ 1/conj ρ`

The self-Pstar property of `G` implies that its multiset of roots is closed
under `ρ ↦ 1/conj ρ`. The proof goes via the fact that
`Pstar (X - ρ) = -conj(ρ) · (X - 1/conj ρ)` and `Pstar` is multiplicative.
-/

/-- The Pstar of a linear factor. -/
lemma Pstar_X_sub_C (ρ : ℂ) (hρ : ρ ≠ 0) :
    Pstar (X - C ρ) = -(C (starRingEnd ℂ ρ) * X) + 1 := by
  unfold Pstar
  rw [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C]
  -- We compute mirror(X - C(conj ρ)) coefficient-by-coefficient.
  have hnd : ((X - C (starRingEnd ℂ ρ) : ℂ[X])).natDegree = 1 := natDegree_X_sub_C _
  have hconj_ne : starRingEnd ℂ ρ ≠ 0 := by
    intro h
    apply hρ
    have hinj : Function.Injective (starRingEnd ℂ) := RingHom.injective _
    have h0 : starRingEnd ℂ ρ = starRingEnd ℂ 0 := by rw [h, map_zero]
    exact hinj h0
  have hntd : ((X - C (starRingEnd ℂ ρ) : ℂ[X])).natTrailingDegree = 0 := by
    rw [natTrailingDegree_eq_zero]
    right
    rw [Polynomial.coeff_sub, Polynomial.coeff_X_zero, Polynomial.coeff_C_zero,
        zero_sub, neg_ne_zero]
    exact hconj_ne
  ext k
  rw [coeff_mirror, hnd, hntd, add_zero]
  -- LHS: (X - C(conj ρ)).coeff (revAt 1 k)
  -- RHS: (-(C(conj ρ) * X) + 1).coeff k
  by_cases hk1 : k ≤ 1
  · rw [revAt_le hk1]
    interval_cases k
    · -- k = 0: revAt 1 0 = 1, LHS = (X - C(conj ρ)).coeff 1 = 1.
      -- RHS at 0: (-(C(conj ρ) * X) + 1).coeff 0 = 0 + 1 = 1.
      simp
    · -- k = 1: revAt 1 1 = 0, LHS = (X - C(conj ρ)).coeff 0 = -conj ρ.
      -- RHS at 1: (-(C(conj ρ) * X) + 1).coeff 1 = -conj ρ + 0 = -conj ρ.
      simp [Polynomial.coeff_one]
  · push_neg at hk1
    rw [revAt_eq_self_of_lt hk1]
    -- LHS: (X - C(conj ρ)).coeff k = 0 for k ≥ 2.
    -- RHS: (-(C(conj ρ) * X) + 1).coeff k = 0 for k ≥ 2.
    have h1 : (X - C (starRingEnd ℂ ρ) : ℂ[X]).coeff k = 0 := by
      apply Polynomial.coeff_eq_zero_of_natDegree_lt
      rw [hnd]; omega
    rw [h1]
    have h2 : (-(C (starRingEnd ℂ ρ) * X) + 1 : ℂ[X]).coeff k = 0 := by
      rw [show (-(C (starRingEnd ℂ ρ) * X) + 1 : ℂ[X])
            = (1 : ℂ[X]) + C (- starRingEnd ℂ ρ) * X by
        rw [C_neg]; ring]
      rw [Polynomial.coeff_add, Polynomial.coeff_one, Polynomial.coeff_C_mul,
          Polynomial.coeff_X]
      have hk0 : k ≠ 0 := by omega
      have hk1' : 1 ≠ k := by omega
      rw [if_neg hk0, if_neg hk1']
      ring
    exact h2.symm

/-- The Pstar of a linear factor, equivalent form. -/
lemma Pstar_X_sub_C_eq (ρ : ℂ) (hρ : ρ ≠ 0) :
    Pstar (X - C ρ) = -C (starRingEnd ℂ ρ) * (X - C ((starRingEnd ℂ ρ)⁻¹)) := by
  have hconj_ne : starRingEnd ℂ ρ ≠ 0 := by
    intro h
    apply hρ
    have hinj : Function.Injective (starRingEnd ℂ) := RingHom.injective _
    have h0 : starRingEnd ℂ ρ = starRingEnd ℂ 0 := by rw [h, map_zero]
    exact hinj h0
  rw [Pstar_X_sub_C ρ hρ]
  -- Show: -(C(conj ρ) * X) + 1 = -C(conj ρ) * (X - C(1/conj ρ))
  rw [show -C (starRingEnd ℂ ρ) * (X - C ((starRingEnd ℂ ρ)⁻¹))
        = -(C (starRingEnd ℂ ρ) * X) + C (starRingEnd ℂ ρ) * C ((starRingEnd ℂ ρ)⁻¹) by ring,
      ← Polynomial.C_mul, mul_inv_cancel₀ hconj_ne, C_1]

/-- Root pairing under `ρ ↦ 1/conj ρ` for self-Pstar polynomials. -/
lemma rootMultiplicity_pstar_pair (G : ℂ[X]) (hG : Pstar G = G) (ρ : ℂ) (hρ : ρ ≠ 0)
    (hG_ne : G ≠ 0) :
    G.rootMultiplicity ρ ≤ G.rootMultiplicity (starRingEnd ℂ ρ)⁻¹ := by
  set m := G.rootMultiplicity ρ
  -- (X - C ρ)^m ∣ G
  have hdvd : (X - C ρ) ^ m ∣ G := pow_rootMultiplicity_dvd G ρ
  -- Apply Pstar to both sides: Pstar((X - C ρ)^m) ∣ Pstar G = G.
  have hPdvd : Pstar ((X - C ρ) ^ m) ∣ Pstar G := by
    obtain ⟨q, hq⟩ := hdvd
    refine ⟨Pstar q, ?_⟩
    rw [hq, Pstar_mul]
  rw [hG] at hPdvd
  -- Now Pstar((X - C ρ)^m) = (-C(conj ρ))^m * (X - C(1/conj ρ))^m
  have hPstarPow : Pstar ((X - C ρ) ^ m) =
      (-C (starRingEnd ℂ ρ)) ^ m * (X - C ((starRingEnd ℂ ρ)⁻¹)) ^ m := by
    rw [show ((X - C ρ) ^ m : ℂ[X]) = (X - C ρ) ^ m from rfl]
    induction m with
    | zero => simp [Pstar_one]
    | succ m ih => rw [pow_succ, Pstar_mul, ih, Pstar_X_sub_C_eq ρ hρ, pow_succ, pow_succ]; ring
  rw [hPstarPow] at hPdvd
  -- Now (-C(conj ρ))^m is a unit (since conj ρ ≠ 0).
  have hconj_ne : starRingEnd ℂ ρ ≠ 0 := by
    intro h
    apply hρ
    have hinj : Function.Injective (starRingEnd ℂ) := RingHom.injective _
    have h0 : starRingEnd ℂ ρ = starRingEnd ℂ 0 := by rw [h, map_zero]
    exact hinj h0
  have hu : IsUnit ((-C (starRingEnd ℂ ρ)) ^ m) := by
    apply IsUnit.pow
    apply IsUnit.neg
    exact (isUnit_C).mpr (Ne.isUnit hconj_ne)
  -- Strip out the unit.
  have hdvd_lin : (X - C ((starRingEnd ℂ ρ)⁻¹)) ^ m ∣ G :=
    (IsUnit.mul_left_dvd hu).mp hPdvd
  exact (le_rootMultiplicity_iff hG_ne).mpr hdvd_lin

/-- Root pairing: for self-Pstar `G`, `rootMultiplicity ρ G = rootMultiplicity (1/conj ρ) G`. -/
lemma rootMultiplicity_pstar_eq (G : ℂ[X]) (hG : Pstar G = G) (ρ : ℂ) (hρ : ρ ≠ 0)
    (hG_ne : G ≠ 0) :
    G.rootMultiplicity ρ = G.rootMultiplicity (starRingEnd ℂ ρ)⁻¹ := by
  have hconj_ne : starRingEnd ℂ ρ ≠ 0 := by
    intro h
    apply hρ
    have hinj : Function.Injective (starRingEnd ℂ) := RingHom.injective _
    have h0 : starRingEnd ℂ ρ = starRingEnd ℂ 0 := by rw [h, map_zero]
    exact hinj h0
  have hinv_ne : (starRingEnd ℂ ρ)⁻¹ ≠ 0 := inv_ne_zero hconj_ne
  have h1 : G.rootMultiplicity ρ ≤ G.rootMultiplicity (starRingEnd ℂ ρ)⁻¹ :=
    rootMultiplicity_pstar_pair G hG ρ hρ hG_ne
  have h2 : G.rootMultiplicity (starRingEnd ℂ ρ)⁻¹ ≤
            G.rootMultiplicity (starRingEnd ℂ (starRingEnd ℂ ρ)⁻¹)⁻¹ :=
    rootMultiplicity_pstar_pair G hG (starRingEnd ℂ ρ)⁻¹ hinv_ne hG_ne
  have h3 : (starRingEnd ℂ (starRingEnd ℂ ρ)⁻¹)⁻¹ = ρ := by
    rw [map_inv₀, inv_inv]
    show starRingEnd ℂ (starRingEnd ℂ ρ) = ρ
    rw [Complex.conj_conj]
  rw [h3] at h2
  exact le_antisymm h1 h2

/-! ## Even multiplicity from non-negativity (real polynomials) -/

/-- A real polynomial that is non-negative on all of `ℝ` has even multiplicity at any root. -/
lemma Polynomial.even_rootMultiplicity_of_nonneg_real (p : ℝ[X])
    (hp : ∀ x : ℝ, 0 ≤ p.eval x) (r : ℝ) : Even (p.rootMultiplicity r) := by
  by_cases hp0 : p = 0
  · subst hp0; simp
  by_cases hmr : p.IsRoot r
  swap
  · -- r not a root, rootMultiplicity = 0.
    rw [rootMultiplicity_eq_zero hmr]; exact Even.zero
  -- r is a root. Let m = rootMultiplicity r p > 0.
  set m := p.rootMultiplicity r with hm_def
  -- (X - C r)^m * q = p, where q = p /ₘ (X - C r)^m has q(r) ≠ 0.
  have h_monic : Monic ((X - C r) ^ m : ℝ[X]) := (monic_X_sub_C r).pow _
  have h_pow_ne : ((X - C r) ^ m : ℝ[X]) ≠ 0 := pow_ne_zero _ (X_sub_C_ne_zero _)
  have h_dvd : (X - C r) ^ m ∣ p := pow_rootMultiplicity_dvd p r
  set q := p /ₘ ((X - C r) ^ m) with hq_def
  have hq_mul : p = (X - C r) ^ m * q := by
    have h1 : p %ₘ ((X - C r) ^ m) = 0 := (modByMonic_eq_zero_iff_dvd h_monic).mpr h_dvd
    have h2 := modByMonic_add_div p ((X - C r) ^ m)
    rw [h1, zero_add] at h2
    exact h2.symm
  have hq_eval_ne : q.eval r ≠ 0 := by
    intro hq_eval
    have h_root_q : (X - C r) ∣ q := dvd_iff_isRoot.mpr hq_eval
    have h_pow_succ : (X - C r) ^ (m + 1) ∣ p := by
      rw [hq_mul, pow_succ]
      exact mul_dvd_mul (dvd_refl _) h_root_q
    have h_mult_ge : m + 1 ≤ p.rootMultiplicity r :=
      (le_rootMultiplicity_iff hp0).mpr h_pow_succ
    omega
  -- p(x) = (x - r)^m · q(x) for all x.
  have h_eval : ∀ x : ℝ, p.eval x = (x - r) ^ m * q.eval x := by
    intro x
    rw [hq_mul, eval_mul, eval_pow, eval_sub, eval_X, eval_C]
  -- Step 1: q.eval r ≥ 0 (from the right).
  have hq_pos : 0 ≤ q.eval r := by
    -- Use continuity: q.eval is continuous, lim x→r+ q.eval x = q.eval r.
    -- For x > r small, q.eval x = p.eval x / (x - r)^m ≥ 0.
    have h_cont : Filter.Tendsto (fun x => q.eval x) (nhds r) (nhds (q.eval r)) :=
      (Polynomial.continuous q).continuousAt
    have h_within : Filter.Tendsto (fun x => q.eval x) (nhdsWithin r (Set.Ioi r))
        (nhds (q.eval r)) := h_cont.mono_left nhdsWithin_le_nhds
    refine ge_of_tendsto h_within ?_
    -- For x > r near r: (x - r)^m > 0, p(x) ≥ 0, so q(x) ≥ 0.
    rw [Filter.eventually_iff]
    refine Filter.mem_of_superset (self_mem_nhdsWithin) ?_
    intro x hx
    simp only [Set.mem_Ioi] at hx
    have hxr : 0 < x - r := by linarith
    have h_pow : 0 < (x - r) ^ m := pow_pos hxr _
    have hpx : 0 ≤ p.eval x := hp x
    rw [h_eval] at hpx
    -- (x - r)^m * q.eval x ≥ 0, and (x - r)^m > 0, so q.eval x ≥ 0.
    exact nonneg_of_mul_nonneg_right hpx h_pow
  -- Step 2: if m odd, q.eval r ≤ 0 (from the left), so q.eval r = 0, contradiction.
  by_contra h_odd
  -- h_odd : ¬ Even m, i.e., Odd m.
  rw [Nat.not_even_iff_odd] at h_odd
  have hq_neg : q.eval r ≤ 0 := by
    have h_cont : Filter.Tendsto (fun x => q.eval x) (nhds r) (nhds (q.eval r)) :=
      (Polynomial.continuous q).continuousAt
    have h_within : Filter.Tendsto (fun x => q.eval x) (nhdsWithin r (Set.Iio r))
        (nhds (q.eval r)) := h_cont.mono_left nhdsWithin_le_nhds
    refine le_of_tendsto h_within ?_
    rw [Filter.eventually_iff]
    refine Filter.mem_of_superset (self_mem_nhdsWithin) ?_
    intro x hx
    simp only [Set.mem_Iio] at hx
    have hxr : x - r < 0 := by linarith
    have h_pow_neg : (x - r) ^ m < 0 := Odd.pow_neg h_odd hxr
    have hpx : 0 ≤ p.eval x := hp x
    rw [h_eval] at hpx
    -- (x - r)^m * q.eval x ≥ 0 and (x - r)^m < 0, so q.eval x ≤ 0.
    by_contra h
    have h' : 0 < q.eval x := lt_of_not_ge h
    have hprod : (x - r) ^ m * q.eval x < 0 := mul_neg_of_neg_of_pos h_pow_neg h'
    linarith
  -- Combine: q.eval r = 0, contradiction.
  have : q.eval r = 0 := le_antisymm hq_neg hq_pos
  exact hq_eval_ne this

/-! ## Stereographic substitution polynomial

For a complex polynomial `S` and `ρ ∈ ℂ`, we define
`stereoPoly S ρ N := ∑_{k=0}^{N} (S.coeff k) · ρ^k · (1 + IT)^k · (1 - IT)^(N - k)`,
the polynomial obtained by substituting `z = ρ · (1 + iT)/(1 - iT)` into `S` and
clearing the denominator `(1 - iT)^N`. -/

/-- The stereographic-substitution polynomial. -/
noncomputable def stereoPoly (S : ℂ[X]) (ρ : ℂ) (N : ℕ) : ℂ[X] :=
  ∑ k ∈ Finset.range (N + 1),
    C (S.coeff k * ρ ^ k) * (1 + C Complex.I * X) ^ k *
      (1 - C Complex.I * X) ^ (N - k)

/-- Evaluation of `stereoPoly S ρ N` at `T = 0` recovers `S.eval ρ`
(when `S.natDegree ≤ N`). -/
lemma stereoPoly_eval_zero (S : ℂ[X]) (ρ : ℂ) (N : ℕ) (hS : S.natDegree ≤ N) :
    (stereoPoly S ρ N).eval 0 = S.eval ρ := by
  unfold stereoPoly
  rw [eval_finset_sum]
  have : ∀ k ∈ Finset.range (N + 1),
      (C (S.coeff k * ρ ^ k) * (1 + C Complex.I * X) ^ k *
        (1 - C Complex.I * X) ^ (N - k)).eval 0 = S.coeff k * ρ ^ k := by
    intros k _
    simp [eval_pow]
  rw [Finset.sum_congr rfl this]
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hS) ρ]

/-- Evaluation of `stereoPoly S ρ N` at `T : ℂ` expressed as the sum form. -/
lemma stereoPoly_eval (S : ℂ[X]) (ρ : ℂ) (N : ℕ) (T : ℂ) :
    (stereoPoly S ρ N).eval T = ∑ k ∈ Finset.range (N + 1),
      S.coeff k * ρ ^ k * (1 + Complex.I * T) ^ k * (1 - Complex.I * T) ^ (N - k) := by
  unfold stereoPoly
  rw [eval_finset_sum]
  apply Finset.sum_congr rfl
  intros k _
  simp [eval_pow, mul_assoc]

/-- The defining relation: for `T : ℂ` with `1 - I*T ≠ 0`,
    `(stereoPoly S ρ N).eval T = S.eval (ρ · (1 + I*T) / (1 - I*T)) · (1 - I*T)^N`,
    provided `S.natDegree ≤ N`. -/
lemma stereoPoly_eval_eq (S : ℂ[X]) (ρ : ℂ) (N : ℕ) (hS : S.natDegree ≤ N)
    (T : ℂ) (hT : 1 - Complex.I * T ≠ 0) :
    (stereoPoly S ρ N).eval T =
      S.eval (ρ * (1 + Complex.I * T) / (1 - Complex.I * T)) *
        (1 - Complex.I * T) ^ N := by
  rw [stereoPoly_eval]
  -- S.eval (ρ * (1+iT)/(1-iT)) = ∑_{k=0}^{N} S.coeff k * (ρ*(1+iT)/(1-iT))^k
  rw [Polynomial.eval_eq_sum_range' (Nat.lt_succ_of_le hS)]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intros k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  -- LHS term: S.coeff k * ρ^k * (1+iT)^k * (1-iT)^(N-k)
  -- RHS term: S.coeff k * (ρ * (1+iT)/(1-iT))^k * (1-iT)^N
  rw [div_pow, mul_pow]
  have hpow_ne : (1 - Complex.I * T) ^ k ≠ 0 := pow_ne_zero _ hT
  field_simp
  rw [show (1 - Complex.I * T) ^ N = (1 - Complex.I * T) ^ k * (1 - Complex.I * T) ^ (N - k) by
    rw [← pow_add, Nat.add_sub_cancel' hk]]
  ring

/-- For `|ρ| = 1` and `T : ℝ`, the stereographic image is on the unit circle. -/
lemma stereoPoint_norm_one {ρ : ℂ} (hρ : ‖ρ‖ = 1) (T : ℝ) :
    ‖ρ * (1 + Complex.I * T) / (1 - Complex.I * T)‖ = 1 := by
  -- Strategy: show ‖1 + I·T‖² = ‖1 - I·T‖² = 1 + T², then conclude.
  have h_normSq_plus : Complex.normSq (1 + Complex.I * (T : ℂ)) = 1 + T ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
    ring
  have h_normSq_minus : Complex.normSq (1 - Complex.I * (T : ℂ)) = 1 + T ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
    ring
  -- ‖z‖² = normSq z (from Complex.normSq_eq_norm_sq).
  have h_norm_plus_sq : ‖1 + Complex.I * (T : ℂ)‖ ^ 2 = 1 + T ^ 2 := by
    rw [Complex.normSq_eq_norm_sq] at h_normSq_plus
    exact h_normSq_plus
  have h_norm_minus_sq : ‖1 - Complex.I * (T : ℂ)‖ ^ 2 = 1 + T ^ 2 := by
    rw [Complex.normSq_eq_norm_sq] at h_normSq_minus
    exact h_normSq_minus
  have h_pos : (0 : ℝ) < 1 + T ^ 2 := by positivity
  have h_minus_ne : 1 - Complex.I * (T : ℂ) ≠ 0 := by
    intro h
    rw [h, norm_zero] at h_norm_minus_sq
    linarith
  rw [norm_div, norm_mul, hρ, one_mul]
  rw [show ‖1 + Complex.I * (T : ℂ)‖ = ‖1 - Complex.I * (T : ℂ)‖ from ?_, div_self]
  · -- ‖1 - I·T‖ ≠ 0
    rwa [ne_eq, norm_eq_zero]
  · -- ‖1 + I·T‖ = ‖1 - I·T‖
    have h_nn1 : 0 ≤ ‖1 + Complex.I * (T : ℂ)‖ := norm_nonneg _
    have h_nn2 : 0 ≤ ‖1 - Complex.I * (T : ℂ)‖ := norm_nonneg _
    nlinarith [h_norm_plus_sq, h_norm_minus_sq, sq_nonneg ‖1 + Complex.I * (T : ℂ)‖,
               sq_nonneg ‖1 - Complex.I * (T : ℂ)‖]

/-- For `T : ℝ`, `(1 + I·T)·(1 - I·T) = 1 + T²` as complex numbers. -/
lemma one_add_I_T_mul_one_sub_I_T (T : ℝ) :
    (1 + Complex.I * (T : ℂ)) * (1 - Complex.I * (T : ℂ)) = ((1 + T ^ 2 : ℝ) : ℂ) := by
  have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
  have : (1 + Complex.I * (T : ℂ)) * (1 - Complex.I * (T : ℂ)) =
      1 - Complex.I ^ 2 * (T : ℂ) ^ 2 := by ring
  rw [this, hI2]
  push_cast
  ring

/-- For `|ρ| = 1` and `T : ℝ`, the stereographic image of `T`. -/
private noncomputable abbrev stereoPt (ρ : ℂ) (T : ℝ) : ℂ :=
  ρ * (1 + Complex.I * (T : ℂ)) / (1 - Complex.I * (T : ℂ))

private lemma stereoPt_norm_one {ρ : ℂ} (hρ : ‖ρ‖ = 1) (T : ℝ) :
    ‖stereoPt ρ T‖ = 1 := stereoPoint_norm_one hρ T

private lemma one_sub_I_T_ne_zero (T : ℝ) :
    (1 - Complex.I * (T : ℂ)) ≠ 0 := by
  intro h
  have h_normSq : Complex.normSq (1 - Complex.I * (T : ℂ)) = 1 + T ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
    ring
  rw [h, Complex.normSq_zero] at h_normSq
  nlinarith [sq_nonneg T]

/-- For `|ρ| = 1`, `T : ℝ`, `n = natDegree P`, the stereographic image of `T` to the
power `n` equals `ρ^n · (1 + IT)^n / (1 - IT)^n`. -/
private lemma stereoPt_pow (ρ : ℂ) (T : ℝ) (n : ℕ) :
    stereoPt ρ T ^ n =
      ρ ^ n * (1 + Complex.I * (T : ℂ)) ^ n / (1 - Complex.I * (T : ℂ)) ^ n := by
  unfold stereoPt
  rw [div_pow, mul_pow]

/-- `stereoPoly (Gpoly P) ρ (2n)` at real `T`, with `|ρ| = 1` and
`natTrailingDegree P = 0`, equals `ρ^n · (1 + T²)^n · (1 - |P z(T)|²)`. -/
lemma stereoPoly_Gpoly_eval_real (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    {ρ : ℂ} (hρ : ‖ρ‖ = 1) (T : ℝ) :
    (stereoPoly (Gpoly P) ρ (2 * P.natDegree)).eval (T : ℂ) =
      ρ ^ P.natDegree * (1 + (T : ℂ) ^ 2) ^ P.natDegree *
        (1 - ((‖P.eval (stereoPt ρ T)‖ : ℂ)) ^ 2) := by
  set n := P.natDegree with hn_def
  set z := stereoPt ρ T with hz_def
  have hz : ‖z‖ = 1 := stereoPt_norm_one hρ T
  have hTne : (1 - Complex.I * (T : ℂ)) ≠ 0 := one_sub_I_T_ne_zero T
  have hGND : (Gpoly P).natDegree ≤ 2 * n := by
    unfold Gpoly
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_X_pow]; omega
    · refine (natDegree_mul_le).trans ?_
      rw [natDegree_Pstar]; omega
  -- Step 1: stereoPoly evaluation.
  rw [stereoPoly_eval_eq (Gpoly P) ρ (2 * n) hGND (T : ℂ) hTne]
  -- Step 2: Gpoly P at z = z^n * ↑(1 - |P z|²).
  rw [Gpoly_eval_on_circle P hT hz]
  -- Step 3: substitute z^n
  rw [stereoPt_pow ρ T n]
  push_cast
  have h_pow_ne : (1 - Complex.I * (T : ℂ)) ^ n ≠ 0 := pow_ne_zero _ hTne
  -- Use (1+IT)^n * (1-IT)^n = (1+T²)^n.
  have h_one_plus_T2 : (1 + Complex.I * (T : ℂ)) ^ n * (1 - Complex.I * (T : ℂ)) ^ n =
      (1 + (T : ℂ) ^ 2) ^ n := by
    rw [← mul_pow]
    congr 1
    have hI2 : Complex.I ^ 2 = -1 := Complex.I_sq
    have heq : (1 + Complex.I * (T : ℂ)) * (1 - Complex.I * (T : ℂ)) =
        1 - Complex.I ^ 2 * (T : ℂ) ^ 2 := by ring
    rw [heq, hI2]
    ring
  -- (1-IT)^{2n} = (1-IT)^n * (1-IT)^n
  have h_pow_2n : (1 - Complex.I * (T : ℂ)) ^ (2 * n) =
      (1 - Complex.I * (T : ℂ)) ^ n * (1 - Complex.I * (T : ℂ)) ^ n := by
    rw [← pow_add, ← two_mul]
  rw [h_pow_2n]
  field_simp
  linear_combination
    (ρ ^ n * (1 - (‖P.eval z‖ : ℂ) ^ 2)) * h_one_plus_T2

/-- `ρ ≠ 0` follows from `‖ρ‖ = 1`. -/
private lemma ne_zero_of_norm_one {ρ : ℂ} (hρ : ‖ρ‖ = 1) : ρ ≠ 0 := by
  intro h; rw [h, norm_zero] at hρ; exact zero_ne_one hρ

/-- The normalized stereographic polynomial evaluated at real `T` is the real number
`(1 + T²)^n · (1 - |P z(T)|²)`. -/
lemma stereoPoly_normalized_eval (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    {ρ : ℂ} (hρ : ‖ρ‖ = 1) (T : ℝ) :
    (C (ρ⁻¹ ^ P.natDegree) * stereoPoly (Gpoly P) ρ (2 * P.natDegree)).eval (T : ℂ) =
      ((1 + T ^ 2 : ℝ) : ℂ) ^ P.natDegree *
        (1 - ((‖P.eval (stereoPt ρ T)‖ : ℂ)) ^ 2) := by
  rw [eval_mul, eval_C, stereoPoly_Gpoly_eval_real P hT hρ T]
  have hρ_ne : ρ ≠ 0 := ne_zero_of_norm_one hρ
  have hinv_pow : ρ⁻¹ ^ P.natDegree * ρ ^ P.natDegree = 1 := by
    rw [← mul_pow, inv_mul_cancel₀ hρ_ne, one_pow]
  rw [show (1 + (T : ℂ) ^ 2) = ((1 + T ^ 2 : ℝ) : ℂ) by push_cast; ring]
  linear_combination
    (((1 + T ^ 2 : ℝ) : ℂ) ^ P.natDegree *
      (1 - (‖P.eval (stereoPt ρ T)‖ : ℂ) ^ 2)) * hinv_pow

/-- The normalized polynomial: a clean alias. -/
noncomputable def normalizedStereoPoly (P : ℂ[X]) (ρ : ℂ) : ℂ[X] :=
  C (ρ⁻¹ ^ P.natDegree) * stereoPoly (Gpoly P) ρ (2 * P.natDegree)

/-- The normalized polynomial has real (and non-negative) value at real `T`. -/
lemma normalizedStereoPoly_eval_nonneg (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    {ρ : ℂ} (hρ : ‖ρ‖ = 1)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) (T : ℝ) :
    ∃ y : ℝ, 0 ≤ y ∧ (normalizedStereoPoly P ρ).eval (T : ℂ) = (y : ℂ) := by
  unfold normalizedStereoPoly
  rw [stereoPoly_normalized_eval P hT hρ T]
  have hz : ‖stereoPt ρ T‖ = 1 := stereoPt_norm_one hρ T
  have hPz : ‖P.eval (stereoPt ρ T)‖ ≤ 1 := hPbd _ hz
  refine ⟨(1 + T ^ 2) ^ P.natDegree * (1 - ‖P.eval (stereoPt ρ T)‖ ^ 2), ?_, ?_⟩
  · have h1 : 0 ≤ (1 + T ^ 2) ^ P.natDegree := pow_nonneg (by positivity) _
    have h2 : 0 ≤ 1 - ‖P.eval (stereoPt ρ T)‖ ^ 2 := by
      have : ‖P.eval (stereoPt ρ T)‖ ^ 2 ≤ 1 := by
        rw [show (1 : ℝ) = 1 ^ 2 by ring]
        exact sq_le_sq' (by linarith [norm_nonneg (P.eval (stereoPt ρ T))]) hPz
      linarith
    exact mul_nonneg h1 h2
  · push_cast; ring

/-! ## Lifting from ℂ[X] to ℝ[X] when coefficients are real -/

/-- For `p : ℂ[X]` and `x : ℝ` cast to `ℂ`,
`(p.map (starRingEnd ℂ)).eval x = conj (p.eval x)`. -/
lemma eval_map_starRingEnd_real (p : ℂ[X]) (x : ℝ) :
    (p.map (starRingEnd ℂ)).eval ((x : ℂ)) = starRingEnd ℂ (p.eval ((x : ℂ))) := by
  rw [Polynomial.eval_map, Polynomial.eval₂_eq_sum_range]
  rw [Polynomial.eval_eq_sum_range ((x : ℂ)) (p := p)]
  rw [map_sum]
  apply Finset.sum_congr rfl
  intros k _
  rw [map_mul, map_pow]
  rw [Complex.conj_ofReal x]

/-- A polynomial in `ℂ[X]` real-valued at every real point is invariant under
coefficient conjugation. -/
lemma map_starRingEnd_eq_self_of_eval_real (p : ℂ[X])
    (hReal : ∀ T : ℝ, (p.eval (T : ℂ)).im = 0) :
    p.map (starRingEnd ℂ) = p := by
  refine eq_of_natDegree_lt_card_of_eval_eq
    (p.map (starRingEnd ℂ)) p
    (f := fun i : Fin (p.natDegree + 1) => (((i : ℕ) : ℝ) : ℂ)) ?_ ?_ ?_
  · intro i j hij
    have hijR : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
      have := hij
      exact Complex.ofReal_injective this
    have hijN : (i : ℕ) = (j : ℕ) := by exact_mod_cast hijR
    exact Fin.ext hijN
  · intro i
    rw [eval_map_starRingEnd_real]
    have h_im : (p.eval ((((i : ℕ) : ℝ)) : ℂ)).im = 0 := hReal _
    exact Complex.ext (by rfl) (by rw [Complex.conj_im]; linarith)
  · simp only [Polynomial.natDegree_map, Fintype.card_fin, max_self]
    exact Nat.lt_succ_self _

/-! ## Multiplicativity of `stereoPoly` -/

/-- The `stereoPoly` substitution respects multiplication. -/
lemma stereoPoly_mul (A B : ℂ[X]) (ρ : ℂ) (N_A N_B : ℕ)
    (hA : A.natDegree ≤ N_A) (hB : B.natDegree ≤ N_B) :
    stereoPoly (A * B) ρ (N_A + N_B) = stereoPoly A ρ N_A * stereoPoly B ρ N_B := by
  -- Both sides agree at every `T` where `1 - I·T ≠ 0`, in particular at the infinite
  -- family `T = ((i : ℕ) : ℂ)` for `i : ℕ` (since these are real, the `I·T` part
  -- has nonzero imaginary part for `i ≠ 0`, and at `i = 0` we have `1 - 0 = 1 ≠ 0`).
  have hAB : (A * B).natDegree ≤ N_A + N_B :=
    natDegree_mul_le.trans (Nat.add_le_add hA hB)
  -- Use polynomial uniqueness via eval at Fin (N_A + N_B + ND_rhs + 1) → ℂ.
  set d := max (stereoPoly (A * B) ρ (N_A + N_B)).natDegree
              (stereoPoly A ρ N_A * stereoPoly B ρ N_B).natDegree
  refine eq_of_natDegree_lt_card_of_eval_eq
    (stereoPoly (A * B) ρ (N_A + N_B))
    (stereoPoly A ρ N_A * stereoPoly B ρ N_B)
    (f := fun i : Fin (d + 1) => (((i : ℕ) : ℝ) : ℂ)) ?_ ?_ ?_
  · -- injective
    intro i j hij
    have hijR : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := Complex.ofReal_injective hij
    have hijN : (i : ℕ) = (j : ℕ) := by exact_mod_cast hijR
    exact Fin.ext hijN
  · intro i
    -- Eval at real point: use stereoPoly_eval_eq for both sides.
    have hTne : 1 - Complex.I * (((i : ℕ) : ℝ) : ℂ) ≠ 0 := one_sub_I_T_ne_zero _
    rw [eval_mul]
    rw [stereoPoly_eval_eq (A * B) ρ (N_A + N_B) hAB _ hTne]
    rw [stereoPoly_eval_eq A ρ N_A hA _ hTne]
    rw [stereoPoly_eval_eq B ρ N_B hB _ hTne]
    rw [eval_mul, pow_add]
    ring
  · rw [Fintype.card_fin]
    exact Nat.lt_succ_self _

/-- Bound: `stereoPoly S ρ N` has natDegree at most `N`. -/
lemma stereoPoly_natDegree_le (S : ℂ[X]) (ρ : ℂ) (N : ℕ) :
    (stereoPoly S ρ N).natDegree ≤ N := by
  unfold stereoPoly
  refine (Polynomial.natDegree_sum_le _ _).trans ?_
  refine Finset.fold_max_le _ |>.mpr ⟨by simp, ?_⟩
  intro k hk
  rw [Finset.mem_range, Nat.lt_succ_iff] at hk
  refine (natDegree_mul_le).trans ?_
  have h_lin : ((1 + C Complex.I * X : ℂ[X])).natDegree ≤ 1 := by
    refine (natDegree_add_le _ _).trans ?_
    have h1 : ((1 : ℂ[X])).natDegree = 0 := natDegree_one
    have h2 : (C Complex.I * X).natDegree ≤ 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_; rw [natDegree_X]
    rw [h1]; omega
  have h_lin' : ((1 - C Complex.I * X : ℂ[X])).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_
    have h1 : ((1 : ℂ[X])).natDegree = 0 := natDegree_one
    have h2 : (C Complex.I * X).natDegree ≤ 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_; rw [natDegree_X]
    rw [h1]; omega
  have h_add_pow : ((1 + C Complex.I * X) ^ k : ℂ[X]).natDegree ≤ k := by
    refine (natDegree_pow_le).trans ?_
    refine (Nat.mul_le_mul_left k h_lin).trans ?_
    omega
  have h_sub_pow : ((1 - C Complex.I * X) ^ (N - k) : ℂ[X]).natDegree ≤ N - k := by
    refine (natDegree_pow_le).trans ?_
    refine (Nat.mul_le_mul_left (N - k) h_lin').trans ?_
    omega
  have h_mul1 : (C (S.coeff k * ρ ^ k) * (1 + C Complex.I * X) ^ k).natDegree ≤ k := by
    refine (natDegree_C_mul_le _ _).trans h_add_pow
  refine (add_le_add h_mul1 h_sub_pow).trans ?_
  omega

/-- The stereographic image of a linear factor: `stereoPoly (X - C ρ) ρ 1 = 2ρI · X`. -/
lemma stereoPoly_X_sub_C (ρ : ℂ) :
    stereoPoly (X - C ρ) ρ 1 = C (2 * ρ * Complex.I) * X := by
  -- Verify via polynomial uniqueness over enough complex points.
  refine eq_of_natDegree_lt_card_of_eval_eq _ _
    (f := fun i : Fin (1 + 1 + 1) => (((i : ℕ) : ℝ) : ℂ)) ?_ ?_ ?_
  · intro i j hij
    have hijR : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := Complex.ofReal_injective hij
    have hijN : (i : ℕ) = (j : ℕ) := by exact_mod_cast hijR
    exact Fin.ext hijN
  · intro i
    have hTne : 1 - Complex.I * (((i : ℕ) : ℝ) : ℂ) ≠ 0 := one_sub_I_T_ne_zero _
    rw [stereoPoly_eval_eq (X - C ρ) ρ 1 (by rw [natDegree_X_sub_C]) _ hTne]
    rw [eval_sub, eval_X, eval_C]
    rw [eval_mul, eval_C, eval_X]
    field_simp
    ring
  · have h1 : (stereoPoly (X - C ρ) ρ 1).natDegree ≤ 1 := stereoPoly_natDegree_le _ _ _
    have h2 : (C (2 * ρ * Complex.I) * X).natDegree ≤ 1 := by
      refine (natDegree_C_mul_le _ _).trans ?_
      rw [natDegree_X]
    simp only [Fintype.card_fin]
    omega

/-- `stereoPoly S ρ N` at `T = 0` equals `S.eval ρ`. -/
lemma stereoPoly_eval_zero_eq (S : ℂ[X]) (ρ : ℂ) (N : ℕ) (hS : S.natDegree ≤ N) :
    (stereoPoly S ρ N).eval 0 = S.eval ρ := stereoPoly_eval_zero S ρ N hS

/-- If `H.eval ρ ≠ 0` and `H.natDegree ≤ N`, then `rootMultiplicity 0 (stereoPoly H ρ N) = 0`. -/
lemma rootMultiplicity_stereoPoly_eq_zero_of_eval_ne (H : ℂ[X]) (ρ : ℂ) (N : ℕ)
    (hH : H.natDegree ≤ N) (h_eval : H.eval ρ ≠ 0) :
    (stereoPoly H ρ N).rootMultiplicity 0 = 0 := by
  apply Polynomial.rootMultiplicity_eq_zero
  rw [Polynomial.IsRoot.def, stereoPoly_eval_zero H ρ N hH]
  exact h_eval

/-- `stereoPoly H ρ N ≠ 0` when `H.eval ρ ≠ 0` (otherwise eval at 0 would be 0). -/
lemma stereoPoly_ne_zero_of_eval_ne (H : ℂ[X]) (ρ : ℂ) (N : ℕ)
    (hH : H.natDegree ≤ N) (h_eval : H.eval ρ ≠ 0) :
    stereoPoly H ρ N ≠ 0 := by
  intro heq
  apply h_eval
  rw [← stereoPoly_eval_zero H ρ N hH, heq, Polynomial.eval_zero]

/-- Iterated linear factor: `stereoPoly ((X - C ρ)^m) ρ m = (2ρI)^m · X^m`. -/
lemma stereoPoly_X_sub_C_pow (ρ : ℂ) (m : ℕ) :
    stereoPoly ((X - C ρ) ^ m) ρ m = C ((2 * ρ * Complex.I) ^ m) * X ^ m := by
  induction m with
  | zero => simp [stereoPoly]
  | succ m ih =>
    have h1 : ((X - C ρ : ℂ[X])).natDegree ≤ 1 := by
      rw [natDegree_X_sub_C]
    have hm : (((X - C ρ : ℂ[X]) ^ m)).natDegree ≤ m := by
      refine (natDegree_pow_le).trans ?_
      rw [natDegree_X_sub_C, mul_one]
    rw [pow_succ]
    rw [stereoPoly_mul ((X - C ρ) ^ m) (X - C ρ) ρ m 1 hm h1]
    rw [ih, stereoPoly_X_sub_C]
    rw [pow_succ, pow_succ]
    rw [show C ((2 * ρ * Complex.I) ^ m * (2 * ρ * Complex.I)) =
            C ((2 * ρ * Complex.I) ^ m) * C (2 * ρ * Complex.I) from C_mul]
    ring

/-- **The multiplicity bridge**: for `G : ℂ[X]`, `ρ ≠ 0`, `G ≠ 0`, and `G.natDegree ≤ N`,
the multiplicity of `0` in `stereoPoly G ρ N` equals the multiplicity of `ρ` in `G`. -/
lemma rootMultiplicity_stereoPoly_eq (G : ℂ[X]) (hG : G ≠ 0) (ρ : ℂ) (hρ : ρ ≠ 0)
    (N : ℕ) (hND : G.natDegree ≤ N) :
    (stereoPoly G ρ N).rootMultiplicity 0 = G.rootMultiplicity ρ := by
  set m := G.rootMultiplicity ρ with hm_def
  have h_dvd : (X - C ρ) ^ m ∣ G := pow_rootMultiplicity_dvd G ρ
  have h_monic : Monic ((X - C ρ) ^ m : ℂ[X]) := (monic_X_sub_C ρ).pow _
  set H := G /ₘ ((X - C ρ) ^ m) with hH_def
  have hH_mul : G = (X - C ρ) ^ m * H := by
    have h1 : G %ₘ ((X - C ρ) ^ m) = 0 :=
      (modByMonic_eq_zero_iff_dvd h_monic).mpr h_dvd
    have h2 := modByMonic_add_div G ((X - C ρ) ^ m)
    rw [h1, zero_add] at h2
    exact h2.symm
  have hH_ne : H ≠ 0 := by
    intro h; apply hG; rw [hH_mul, h, mul_zero]
  have hH_eval : H.eval ρ ≠ 0 := by
    intro h_eval
    have h_root_H : (X - C ρ) ∣ H := dvd_iff_isRoot.mpr h_eval
    have h_dvd_succ : (X - C ρ) ^ (m + 1) ∣ G := by
      rw [hH_mul, pow_succ]
      exact mul_dvd_mul (dvd_refl _) h_root_H
    have h_mult_ge : m + 1 ≤ G.rootMultiplicity ρ :=
      (le_rootMultiplicity_iff hG).mpr h_dvd_succ
    omega
  have hmle : m ≤ G.natDegree := by
    have : (((X - C ρ : ℂ[X]) ^ m)).natDegree ≤ G.natDegree :=
      natDegree_le_of_dvd h_dvd hG
    rwa [natDegree_pow, natDegree_X_sub_C, mul_one] at this
  have hH_ND : H.natDegree ≤ N - m := by
    have hsum : G.natDegree = m + H.natDegree := by
      rw [hH_mul, natDegree_mul (pow_ne_zero _ (X_sub_C_ne_zero _)) hH_ne]
      rw [natDegree_pow, natDegree_X_sub_C, mul_one]
    omega
  have hX_sub_C_pow_ND : (((X - C ρ : ℂ[X]) ^ m)).natDegree ≤ m := by
    refine (natDegree_pow_le).trans ?_
    rw [natDegree_X_sub_C, mul_one]
  have hN_split : m + (N - m) = N := by
    have : m ≤ N := hmle.trans hND
    omega
  rw [hH_mul, ← hN_split]
  rw [stereoPoly_mul ((X - C ρ) ^ m) H ρ m (N - m) hX_sub_C_pow_ND hH_ND]
  rw [stereoPoly_X_sub_C_pow]
  set α := (2 * ρ * Complex.I) ^ m with hα_def
  have hα_ne : α ≠ 0 := by
    rw [hα_def]
    refine pow_ne_zero _ ?_
    exact mul_ne_zero (mul_ne_zero two_ne_zero hρ) Complex.I_ne_zero
  have hC_α_ne : C α ≠ 0 := by rw [Polynomial.C_ne_zero]; exact hα_ne
  have hXm_ne : (X ^ m : ℂ[X]) ≠ 0 := pow_ne_zero _ X_ne_zero
  have hsHρ_ne : stereoPoly H ρ (N - m) ≠ 0 :=
    stereoPoly_ne_zero_of_eval_ne H ρ (N - m) hH_ND hH_eval
  have hprod1_ne : C α * X ^ m ≠ 0 := mul_ne_zero hC_α_ne hXm_ne
  have hprod_ne : C α * X ^ m * stereoPoly H ρ (N - m) ≠ 0 := mul_ne_zero hprod1_ne hsHρ_ne
  rw [rootMultiplicity_mul hprod_ne]
  rw [rootMultiplicity_stereoPoly_eq_zero_of_eval_ne H ρ (N - m) hH_ND hH_eval, add_zero]
  rw [rootMultiplicity_mul hprod1_ne]
  rw [Polynomial.rootMultiplicity_C]
  rw [zero_add]
  rw [show (X : ℂ[X]) = X - C 0 by simp]
  rw [Polynomial.rootMultiplicity_X_sub_C_pow]

/-! ## Even multiplicity on the circle -/

/-- Explicit ℝ-lift of a ℂ-polynomial with conjugate-symmetric coefficients. -/
noncomputable def reLift (p : ℂ[X]) : ℝ[X] :=
  ∑ k ∈ Finset.range (p.natDegree + 1), (Polynomial.monomial k ((p.coeff k).re))

lemma reLift_coeff (p : ℂ[X]) (k : ℕ) (hk : k ≤ p.natDegree) :
    (reLift p).coeff k = (p.coeff k).re := by
  unfold reLift
  rw [Polynomial.finset_sum_coeff]
  rw [Finset.sum_eq_single k]
  · rw [Polynomial.coeff_monomial, if_pos rfl]
  · intros b _ hbk
    rw [Polynomial.coeff_monomial]
    by_cases h : b = k
    · exact (hbk h).elim
    · rw [if_neg h]
  · intros hk_not
    rw [Finset.mem_range, Nat.lt_succ_iff] at hk_not
    exact (hk_not hk).elim

lemma reLift_map_eq (p : ℂ[X]) (hp : p.map (starRingEnd ℂ) = p) :
    (reLift p).map (algebraMap ℝ ℂ) = p := by
  ext k
  rw [Polynomial.coeff_map]
  show ((reLift p).coeff k : ℂ) = p.coeff k
  by_cases hk : k ≤ p.natDegree
  · rw [reLift_coeff p k hk]
    -- ((p.coeff k).re : ℂ) = p.coeff k requires (p.coeff k).im = 0.
    have him : (p.coeff k).im = 0 := by
      have : (p.map (starRingEnd ℂ)).coeff k = p.coeff k := by rw [hp]
      rw [Polynomial.coeff_map] at this
      -- starRingEnd ℂ (p.coeff k) = p.coeff k → im = 0
      have := this
      have h_conj : starRingEnd ℂ (p.coeff k) = p.coeff k := this
      have h_im : -(p.coeff k).im = (p.coeff k).im := by
        have h1 := congrArg Complex.im h_conj
        rw [Complex.conj_im] at h1
        exact h1
      linarith
    -- ((p.coeff k).re : ℂ) = p.coeff k follows from im = 0.
    apply Complex.ext
    · simp
    · rw [Complex.ofReal_im, him]
  · push_neg at hk
    have h1 : (reLift p).coeff k = 0 := by
      unfold reLift
      rw [Polynomial.finset_sum_coeff]
      apply Finset.sum_eq_zero
      intros i hi
      rw [Finset.mem_range, Nat.lt_succ_iff] at hi
      rw [Polynomial.coeff_monomial, if_neg]
      omega
    rw [h1]
    have h2 : p.coeff k = 0 := Polynomial.coeff_eq_zero_of_natDegree_lt hk
    rw [h2]
    simp

/-- The reLift's eval at real T relates to original eval. -/
lemma reLift_eval_complex (p : ℂ[X]) (hp : p.map (starRingEnd ℂ) = p) (T : ℝ) :
    (((reLift p).eval T : ℝ) : ℂ) = p.eval ((T : ℂ)) := by
  have h1 : (((reLift p).map (algebraMap ℝ ℂ))).eval ((T : ℂ)) =
        (((reLift p).eval T : ℝ) : ℂ) := by
    rw [Polynomial.eval_map]
    rw [show ((T : ℂ)) = algebraMap ℝ ℂ T from rfl]
    rw [Polynomial.eval₂_at_apply]
    rfl
  rw [← h1, reLift_map_eq p hp]

/-- **Even multiplicity on the circle**: for `P` with `natTrailingDegree P = 0`,
`|ρ| = 1`, `|P| ≤ 1` on circle, and `Gpoly P ≠ 0`, `rootMultiplicity ρ (Gpoly P)` is even. -/
lemma even_rootMultiplicity_Gpoly_circle (P : ℂ[X])
    (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1)
    (hGne : Gpoly P ≠ 0)
    {ρ : ℂ} (hρ : ‖ρ‖ = 1) :
    Even ((Gpoly P).rootMultiplicity ρ) := by
  set N := normalizedStereoPoly P ρ with hN_def
  have hρ_ne : ρ ≠ 0 := ne_zero_of_norm_one hρ
  -- Step 1: N has values in ℝ at real points.
  have h_realval : ∀ T : ℝ, (N.eval (T : ℂ)).im = 0 := by
    intro T
    obtain ⟨y, hy0, hy_eq⟩ := normalizedStereoPoly_eval_nonneg P hT hρ hPbd T
    rw [hy_eq]
    simp
  -- Step 2: N has all real coefficients.
  have h_conj : N.map (starRingEnd ℂ) = N :=
    map_starRingEnd_eq_self_of_eval_real N h_realval
  -- Step 3: Define real lift R := reLift N.
  set R := reLift N with hR_def
  -- Step 4: R lifts to N.
  have hR_lift : R.map (algebraMap ℝ ℂ) = N := reLift_map_eq N h_conj
  -- Step 5: R.eval T ≥ 0 for T : ℝ.
  have hR_nonneg : ∀ T : ℝ, 0 ≤ R.eval T := by
    intro T
    obtain ⟨y, hy0, hy_eq⟩ := normalizedStereoPoly_eval_nonneg P hT hρ hPbd T
    have h_eval_eq : ((R.eval T : ℝ) : ℂ) = (y : ℂ) := by
      rw [reLift_eval_complex N h_conj T, hy_eq]
    have : R.eval T = y := by exact_mod_cast h_eval_eq
    rw [this]; exact hy0
  -- Step 6: R has even root mult at 0.
  have h_R_even : Even (R.rootMultiplicity 0) :=
    Polynomial.even_rootMultiplicity_of_nonneg_real R hR_nonneg 0
  -- Step 7: rootMultiplicity 0 R = rootMultiplicity 0 N via lift.
  have h_mult_eq : R.rootMultiplicity 0 = N.rootMultiplicity 0 := by
    have h_inj : Function.Injective (algebraMap ℝ ℂ) := Complex.ofReal_injective
    have := eq_rootMultiplicity_map (f := algebraMap ℝ ℂ) h_inj 0 (p := R)
    rw [this, hR_lift]
    simp
  -- Step 8: rootMultiplicity 0 N = rootMultiplicity ρ (Gpoly P).
  have hND : (Gpoly P).natDegree ≤ 2 * P.natDegree := by
    unfold Gpoly
    refine (natDegree_sub_le _ _).trans (max_le ?_ ?_)
    · rw [natDegree_X_pow]; omega
    · refine (natDegree_mul_le).trans ?_
      rw [natDegree_Pstar]; omega
  have h_bridge : (stereoPoly (Gpoly P) ρ (2 * P.natDegree)).rootMultiplicity 0
                  = (Gpoly P).rootMultiplicity ρ :=
    rootMultiplicity_stereoPoly_eq (Gpoly P) hGne ρ hρ_ne (2 * P.natDegree) hND
  have h_inv_pow_ne : (ρ⁻¹ ^ P.natDegree : ℂ) ≠ 0 := pow_ne_zero _ (inv_ne_zero hρ_ne)
  -- N.rootMultiplicity 0 = (C(ρ⁻¹^n) * stereoPoly...).rootMultiplicity 0
  --                     = rootMultiplicity 0 (C(ρ⁻¹^n)) + rootMultiplicity 0 stereoPoly
  --                     = 0 + (Gpoly P).rootMultiplicity ρ
  have h_N_mult : N.rootMultiplicity 0 = (Gpoly P).rootMultiplicity ρ := by
    rw [hN_def]
    unfold normalizedStereoPoly
    have h_C_ne : (C (ρ⁻¹ ^ P.natDegree) : ℂ[X]) ≠ 0 := by
      rw [Polynomial.C_ne_zero]; exact h_inv_pow_ne
    by_cases h_stereo : stereoPoly (Gpoly P) ρ (2 * P.natDegree) = 0
    · rw [h_stereo, mul_zero, Polynomial.rootMultiplicity_zero]
      rw [h_stereo, Polynomial.rootMultiplicity_zero] at h_bridge
      exact h_bridge
    · rw [rootMultiplicity_mul (mul_ne_zero h_C_ne h_stereo)]
      rw [Polynomial.rootMultiplicity_C]
      rw [zero_add, h_bridge]
  rw [← h_N_mult, ← h_mult_eq]
  exact h_R_even

/-! ## Q construction multiset

For our `G := Gpoly P` with self-Pstar property and even-multiplicity on the circle,
we pick a sub-multiset of roots: each interior root with full multiplicity, each
circle root with half multiplicity. By root pairing and even multiplicity, this
has cardinality `n = natDegree P`. -/

/-- For each `ρ`, the per-root multiset contribution to `Q`: full multiplicity inside,
half multiplicity on the circle, zero outside. -/
noncomputable def QrootSummand (G : ℂ[X]) (ρ : ℂ) : Multiset ℂ :=
  if ‖ρ‖ < 1 then Multiset.replicate (G.rootMultiplicity ρ) ρ
  else if ‖ρ‖ = 1 then Multiset.replicate (G.rootMultiplicity ρ / 2) ρ
  else 0

/-- Sub-multiset of roots used to build `Q`: interior roots full, circle roots halved. -/
noncomputable def QrootsMultiset (G : ℂ[X]) : Multiset ℂ :=
  ∑ ρ ∈ G.roots.toFinset, QrootSummand G ρ

lemma QrootSummand_card (G : ℂ[X]) (ρ : ℂ) :
    (QrootSummand G ρ).card =
      (if ‖ρ‖ < 1 then G.rootMultiplicity ρ
       else if ‖ρ‖ = 1 then G.rootMultiplicity ρ / 2
       else 0) := by
  unfold QrootSummand
  split_ifs <;> simp

/-- Cardinality of `QrootsMultiset` as a sum over distinct roots. -/
lemma QrootsMultiset_card (G : ℂ[X]) :
    (QrootsMultiset G).card =
      ∑ ρ ∈ G.roots.toFinset,
        (if ‖ρ‖ < 1 then G.rootMultiplicity ρ
         else if ‖ρ‖ = 1 then G.rootMultiplicity ρ / 2
         else 0) := by
  unfold QrootsMultiset
  rw [Multiset.card_sum]
  apply Finset.sum_congr rfl
  intros ρ _
  exact QrootSummand_card G ρ

/-! ### Cardinality of QrootsMultiset for Gpoly P -/

/-- The three subsets of distinct roots: inside, on circle, outside. -/
noncomputable def insideRoots (G : ℂ[X]) : Finset ℂ :=
  G.roots.toFinset.filter (fun ρ => ‖ρ‖ < 1)

noncomputable def circleRoots (G : ℂ[X]) : Finset ℂ :=
  G.roots.toFinset.filter (fun ρ => ‖ρ‖ = 1)

noncomputable def outsideRoots (G : ℂ[X]) : Finset ℂ :=
  G.roots.toFinset.filter (fun ρ => 1 < ‖ρ‖)

lemma insideRoots_outsideRoots_disjoint (G : ℂ[X]) :
    Disjoint (insideRoots G) (outsideRoots G) := by
  unfold insideRoots outsideRoots
  rw [Finset.disjoint_filter]
  intros ρ _ h
  intro h2; linarith

lemma insideRoots_circleRoots_disjoint (G : ℂ[X]) :
    Disjoint (insideRoots G) (circleRoots G) := by
  unfold insideRoots circleRoots
  rw [Finset.disjoint_filter]
  intros ρ _ h
  intro h2; linarith

lemma circleRoots_outsideRoots_disjoint (G : ℂ[X]) :
    Disjoint (circleRoots G) (outsideRoots G) := by
  unfold circleRoots outsideRoots
  rw [Finset.disjoint_filter]
  intros ρ _ h
  linarith

lemma toFinset_eq_inside_union_circle_union_outside (G : ℂ[X]) :
    G.roots.toFinset = insideRoots G ∪ circleRoots G ∪ outsideRoots G := by
  unfold insideRoots circleRoots outsideRoots
  ext ρ
  simp only [Finset.mem_union, Finset.mem_filter]
  constructor
  · intro h
    rcases lt_trichotomy ‖ρ‖ 1 with h1 | h1 | h1
    · left; left; exact ⟨h, h1⟩
    · left; right; exact ⟨h, h1⟩
    · right; exact ⟨h, h1⟩
  · rintro ((⟨h, _⟩ | ⟨h, _⟩) | ⟨h, _⟩) <;> exact h

/-- Decomposing the QrootsMultiset cardinality sum into inside + circle + outside parts. -/
lemma QrootsMultiset_card_decompose (G : ℂ[X]) :
    (QrootsMultiset G).card =
      (∑ ρ ∈ insideRoots G, G.rootMultiplicity ρ) +
      (∑ ρ ∈ circleRoots G, G.rootMultiplicity ρ / 2) := by
  rw [QrootsMultiset_card]
  rw [toFinset_eq_inside_union_circle_union_outside G]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
        ⟨insideRoots_outsideRoots_disjoint G, circleRoots_outsideRoots_disjoint G⟩)]
  rw [Finset.sum_union (insideRoots_circleRoots_disjoint G)]
  -- Now compute each piece.
  have h_inside : ∀ ρ ∈ insideRoots G,
      (if ‖ρ‖ < 1 then G.rootMultiplicity ρ
       else if ‖ρ‖ = 1 then G.rootMultiplicity ρ / 2
       else 0) = G.rootMultiplicity ρ := by
    intros ρ hρ
    unfold insideRoots at hρ
    rw [Finset.mem_filter] at hρ
    rw [if_pos hρ.2]
  have h_circle : ∀ ρ ∈ circleRoots G,
      (if ‖ρ‖ < 1 then G.rootMultiplicity ρ
       else if ‖ρ‖ = 1 then G.rootMultiplicity ρ / 2
       else 0) = G.rootMultiplicity ρ / 2 := by
    intros ρ hρ
    unfold circleRoots at hρ
    rw [Finset.mem_filter] at hρ
    rw [if_neg (by linarith : ¬ ‖ρ‖ < 1), if_pos hρ.2]
  have h_outside : ∀ ρ ∈ outsideRoots G,
      (if ‖ρ‖ < 1 then G.rootMultiplicity ρ
       else if ‖ρ‖ = 1 then G.rootMultiplicity ρ / 2
       else 0) = 0 := by
    intros ρ hρ
    unfold outsideRoots at hρ
    rw [Finset.mem_filter] at hρ
    rw [if_neg (by linarith : ¬ ‖ρ‖ < 1), if_neg (by linarith : ¬ ‖ρ‖ = 1)]
  rw [Finset.sum_congr rfl h_inside, Finset.sum_congr rfl h_circle,
      Finset.sum_congr rfl h_outside, Finset.sum_const_zero, add_zero]

/-- The conjugate-reciprocal map `ρ ↦ 1/conj(ρ)`. -/
noncomputable def reciprocalConj (ρ : ℂ) : ℂ := (starRingEnd ℂ ρ)⁻¹

lemma reciprocalConj_reciprocalConj (ρ : ℂ) (hρ : ρ ≠ 0) :
    reciprocalConj (reciprocalConj ρ) = ρ := by
  unfold reciprocalConj
  rw [map_inv₀, inv_inv]
  show starRingEnd ℂ (starRingEnd ℂ ρ) = ρ
  rw [Complex.conj_conj]

lemma reciprocalConj_ne_zero (ρ : ℂ) (hρ : ρ ≠ 0) : reciprocalConj ρ ≠ 0 := by
  unfold reciprocalConj
  apply inv_ne_zero
  intro h
  apply hρ
  have hinj : Function.Injective (starRingEnd ℂ) := RingHom.injective _
  exact hinj (by rw [h, map_zero])

lemma norm_reciprocalConj (ρ : ℂ) (hρ : ρ ≠ 0) :
    ‖reciprocalConj ρ‖ = 1 / ‖ρ‖ := by
  unfold reciprocalConj
  rw [norm_inv, Complex.norm_conj]
  field_simp

/-- Helper: ρ is in the root finset iff it has positive root multiplicity. -/
private lemma mem_roots_toFinset_iff_mult_pos {G : ℂ[X]} (hG_ne : G ≠ 0) (ρ : ℂ) :
    ρ ∈ G.roots.toFinset ↔ 0 < G.rootMultiplicity ρ := by
  rw [Multiset.mem_toFinset, Polynomial.mem_roots hG_ne,
      ← Polynomial.rootMultiplicity_pos hG_ne]

/-- For `G` with `Pstar G = G` and `G(0) ≠ 0`, the conjugate-reciprocal map sends
inside roots to outside roots and vice versa (bijectively). -/
lemma reciprocalConj_insideRoots_eq (G : ℂ[X]) (hG : Pstar G = G) (hG_ne : G ≠ 0)
    (hG_zero : G.eval 0 ≠ 0) :
    (insideRoots G).image reciprocalConj = outsideRoots G := by
  -- Helper: 0 ∉ G.roots.
  have h0_notin : (0 : ℂ) ∉ G.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hG_ne]
    intro h
    exact hG_zero h
  ext σ
  unfold insideRoots outsideRoots
  simp only [Finset.mem_image, Finset.mem_filter]
  constructor
  · rintro ⟨ρ, ⟨hρ_root, hρ_inside⟩, rfl⟩
    have hρ_ne : ρ ≠ 0 := by
      intro h; rw [h] at hρ_root; exact h0_notin hρ_root
    have hρ_pos : 0 < ‖ρ‖ := by
      rcases (norm_nonneg ρ).lt_or_eq with h | h
      · exact h
      · exfalso; apply hρ_ne; exact norm_eq_zero.mp h.symm
    refine ⟨?_, ?_⟩
    · rw [mem_roots_toFinset_iff_mult_pos hG_ne]
      rw [mem_roots_toFinset_iff_mult_pos hG_ne] at hρ_root
      exact lt_of_lt_of_le hρ_root (rootMultiplicity_pstar_pair G hG ρ hρ_ne hG_ne)
    · rw [norm_reciprocalConj ρ hρ_ne, one_div]
      rw [show (1 : ℝ) = 1⁻¹ by norm_num]
      exact (inv_lt_inv₀ (by norm_num) hρ_pos).mpr hρ_inside
  · rintro ⟨hσ_root, hσ_outside⟩
    have hσ_ne : σ ≠ 0 := fun h => by rw [h, norm_zero] at hσ_outside; linarith
    have hpos : 0 < ‖σ‖ := lt_trans (by norm_num : (0:ℝ) < 1) hσ_outside
    refine ⟨reciprocalConj σ, ⟨?_, ?_⟩, ?_⟩
    · rw [mem_roots_toFinset_iff_mult_pos hG_ne]
      rw [mem_roots_toFinset_iff_mult_pos hG_ne] at hσ_root
      exact lt_of_lt_of_le hσ_root (rootMultiplicity_pstar_pair G hG σ hσ_ne hG_ne)
    · rw [norm_reciprocalConj σ hσ_ne, one_div]
      rw [show (1 : ℝ) = 1⁻¹ by norm_num]
      exact (inv_lt_inv₀ hpos (by norm_num)).mpr hσ_outside
    · exact reciprocalConj_reciprocalConj σ hσ_ne

/-- The conjugate-reciprocal map is injective on inside roots. -/
lemma reciprocalConj_injOn_insideRoots (G : ℂ[X]) (hG_zero : G.eval 0 ≠ 0) (hG_ne : G ≠ 0) :
    Set.InjOn reciprocalConj (insideRoots G) := by
  intros ρ hρ σ hσ hRS
  have h0_notin : (0 : ℂ) ∉ G.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hG_ne]
    intro h; exact hG_zero h
  unfold insideRoots at hρ hσ
  rw [Finset.coe_filter, Set.mem_setOf_eq] at hρ hσ
  have hρ_ne : ρ ≠ 0 := by intro h; rw [h] at hρ; exact h0_notin hρ.1
  have hσ_ne : σ ≠ 0 := by intro h; rw [h] at hσ; exact h0_notin hσ.1
  -- reciprocalConj is injective on nonzero elements (it's its own inverse).
  have : reciprocalConj (reciprocalConj ρ) = reciprocalConj (reciprocalConj σ) := by
    rw [hRS]
  rwa [reciprocalConj_reciprocalConj ρ hρ_ne, reciprocalConj_reciprocalConj σ hσ_ne] at this

/-- Multiplicity sum equality: inside_sum = outside_sum for self-Pstar G. -/
lemma sum_insideRoots_mult_eq_sum_outsideRoots (G : ℂ[X])
    (hG : Pstar G = G) (hG_ne : G ≠ 0) (hG_zero : G.eval 0 ≠ 0) :
    ∑ ρ ∈ insideRoots G, G.rootMultiplicity ρ =
      ∑ ρ ∈ outsideRoots G, G.rootMultiplicity ρ := by
  rw [← reciprocalConj_insideRoots_eq G hG hG_ne hG_zero]
  rw [Finset.sum_image (reciprocalConj_injOn_insideRoots G hG_zero hG_ne)]
  apply Finset.sum_congr rfl
  intros ρ hρ
  have h0_notin : (0 : ℂ) ∉ G.roots.toFinset := by
    rw [Multiset.mem_toFinset, Polynomial.mem_roots hG_ne]
    intro h; exact hG_zero h
  unfold insideRoots at hρ
  rw [Finset.mem_filter] at hρ
  have hρ_ne : ρ ≠ 0 := by intro h; rw [h] at hρ; exact h0_notin hρ.1
  show G.rootMultiplicity ρ = G.rootMultiplicity (reciprocalConj ρ)
  unfold reciprocalConj
  exact rootMultiplicity_pstar_eq G hG ρ hρ_ne hG_ne

/-- Sum of multiplicities over distinct roots equals natDegree (for splitting G). -/
lemma sum_rootMultiplicity_eq_natDegree (G : ℂ[X]) (hG_ne : G ≠ 0) :
    ∑ ρ ∈ G.roots.toFinset, G.rootMultiplicity ρ = G.natDegree := by
  have h_eq_card : ∑ ρ ∈ G.roots.toFinset, G.rootMultiplicity ρ = G.roots.card := by
    classical
    conv_lhs =>
      rw [show (fun ρ => G.rootMultiplicity ρ) = (fun ρ => G.roots.count ρ) by
        ext ρ
        rw [← Polynomial.count_roots]]
    rw [← Multiset.toFinset_sum_count_eq G.roots]
  rw [h_eq_card]
  have h_split : G.Splits := IsAlgClosed.splits G
  exact (Polynomial.Splits.natDegree_eq_card_roots h_split).symm

/-- The cardinality of QrootsMultiset for Gpoly P. -/
lemma QrootsMultiset_card_eq_natDegree (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1)
    (hn : 1 ≤ P.natDegree) :
    (QrootsMultiset (Gpoly P)).card = P.natDegree := by
  have hP_ne : P ≠ 0 := by intro h; rw [h, natDegree_zero] at hn; omega
  have hG_ne : Gpoly P ≠ 0 := by
    intro h
    have hND : (Gpoly P).natDegree = 2 * P.natDegree := natDegree_Gpoly P hT hn
    rw [h, natDegree_zero] at hND
    omega
  have hG_palin : Pstar (Gpoly P) = Gpoly P := Pstar_Gpoly P hP_ne hT hn
  have hG_natDeg : (Gpoly P).natDegree = 2 * P.natDegree := natDegree_Gpoly P hT hn
  have hG_zero : (Gpoly P).eval 0 ≠ 0 := by
    have hntd : (Gpoly P).natTrailingDegree = 0 := natTrailingDegree_Gpoly P hP_ne hT hn
    have h_coef : (Gpoly P).coeff 0 ≠ 0 := by
      have hne : (Gpoly P).coeff (Gpoly P).natTrailingDegree ≠ 0 :=
        trailingCoeff_nonzero_iff_nonzero.mpr hG_ne
      rwa [hntd] at hne
    intro h
    apply h_coef
    rw [← Polynomial.coeff_zero_eq_eval_zero] at h
    exact h
  have h_even : ∀ ρ ∈ circleRoots (Gpoly P), Even ((Gpoly P).rootMultiplicity ρ) := by
    intros ρ hρ
    unfold circleRoots at hρ
    rw [Finset.mem_filter] at hρ
    exact even_rootMultiplicity_Gpoly_circle P hT hPbd hG_ne hρ.2
  -- Each circle mult = 2 * (mult/2).
  have h_two_mul : ∀ ρ ∈ circleRoots (Gpoly P),
      (Gpoly P).rootMultiplicity ρ = 2 * ((Gpoly P).rootMultiplicity ρ / 2) := by
    intros ρ hρ
    rcases h_even ρ hρ with ⟨k, hk⟩
    omega
  -- 2 * (Σ mult/2) = Σ mult on circle.
  have h_two_sum : 2 * (∑ ρ ∈ circleRoots (Gpoly P), (Gpoly P).rootMultiplicity ρ / 2) =
      ∑ ρ ∈ circleRoots (Gpoly P), (Gpoly P).rootMultiplicity ρ := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intros ρ hρ
    exact (h_two_mul ρ hρ).symm
  -- Inside + Circle + Outside = natDegree G.
  have h_total : (∑ ρ ∈ insideRoots (Gpoly P), (Gpoly P).rootMultiplicity ρ) +
                 (∑ ρ ∈ circleRoots (Gpoly P), (Gpoly P).rootMultiplicity ρ) +
                 (∑ ρ ∈ outsideRoots (Gpoly P), (Gpoly P).rootMultiplicity ρ) =
                 (Gpoly P).natDegree := by
    rw [← sum_rootMultiplicity_eq_natDegree (Gpoly P) hG_ne]
    rw [toFinset_eq_inside_union_circle_union_outside]
    rw [Finset.sum_union (Finset.disjoint_union_left.mpr
          ⟨insideRoots_outsideRoots_disjoint _, circleRoots_outsideRoots_disjoint _⟩)]
    rw [Finset.sum_union (insideRoots_circleRoots_disjoint _)]
  have h_pair := sum_insideRoots_mult_eq_sum_outsideRoots (Gpoly P) hG_palin hG_ne hG_zero
  rw [QrootsMultiset_card_decompose]
  rw [hG_natDeg] at h_total
  omega


/-- Monic polynomial part of `Q` (the choice of constant comes later). -/
noncomputable def QmonicPart (G : ℂ[X]) : ℂ[X] :=
  ((QrootsMultiset G).map (fun ρ => X - C ρ)).prod

/-- `QmonicPart G` is monic. -/
lemma QmonicPart_monic (G : ℂ[X]) : (QmonicPart G).Monic := by
  unfold QmonicPart
  rw [show ((QrootsMultiset G).map (fun ρ => X - C ρ)).prod
        = ((QrootsMultiset G).map (fun ρ => X - C ρ)).prod from rfl]
  apply Polynomial.monic_multiset_prod_of_monic
  intros i hi
  exact monic_X_sub_C i

/-- The natDegree of `QmonicPart G` equals the cardinality of `QrootsMultiset G`. -/
lemma natDegree_QmonicPart (G : ℂ[X]) :
    (QmonicPart G).natDegree = (QrootsMultiset G).card := by
  unfold QmonicPart
  rw [Polynomial.natDegree_multiset_prod_X_sub_C_eq_card]

/-- The unscaled `Q` polynomial: monic factor whose roots are interior plus
half-multiplicity circle roots of `Gpoly P`. -/
noncomputable def QpolyMonic (P : ℂ[X]) : ℂ[X] := QmonicPart (Gpoly P)

/-- For `P` with `natTrailingDegree P = 0` and `n ≥ 1`,
`(QpolyMonic P).natDegree = P.natDegree`. -/
lemma natDegree_QpolyMonic (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1)
    (hn : 1 ≤ P.natDegree) :
    (QpolyMonic P).natDegree = P.natDegree := by
  unfold QpolyMonic
  rw [natDegree_QmonicPart]
  exact QrootsMultiset_card_eq_natDegree P hT hPbd hn

/-- `QpolyMonic P` is monic. -/
lemma QpolyMonic_monic (P : ℂ[X]) : (QpolyMonic P).Monic := QmonicPart_monic _

/-! ## Multiset arithmetic of QrootsMultiset and Pstar -/

/-- `(QmonicPart G).roots = QrootsMultiset G`. -/
lemma roots_QmonicPart (G : ℂ[X]) :
    (QmonicPart G).roots = QrootsMultiset G := by
  unfold QmonicPart
  exact Polynomial.roots_multiset_prod_X_sub_C _

/-- `QmonicPart G ≠ 0`. -/
lemma QmonicPart_ne_zero (G : ℂ[X]) : QmonicPart G ≠ 0 := by
  exact (QmonicPart_monic G).ne_zero

/-- `QrootsMultiset` decomposes into inside-full + circle-half parts. -/
lemma QrootsMultiset_decompose (G : ℂ[X]) :
    QrootsMultiset G =
      (∑ ρ ∈ insideRoots G, Multiset.replicate (G.rootMultiplicity ρ) ρ) +
      (∑ ρ ∈ circleRoots G, Multiset.replicate (G.rootMultiplicity ρ / 2) ρ) := by
  unfold QrootsMultiset
  rw [toFinset_eq_inside_union_circle_union_outside]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
        ⟨insideRoots_outsideRoots_disjoint _, circleRoots_outsideRoots_disjoint _⟩)]
  rw [Finset.sum_union (insideRoots_circleRoots_disjoint _)]
  -- Inside: replicate(mult).
  have h_inside : ∀ ρ ∈ insideRoots G,
      QrootSummand G ρ = Multiset.replicate (G.rootMultiplicity ρ) ρ := by
    intros ρ hρ
    unfold insideRoots at hρ
    rw [Finset.mem_filter] at hρ
    unfold QrootSummand
    rw [if_pos hρ.2]
  have h_circle : ∀ ρ ∈ circleRoots G,
      QrootSummand G ρ = Multiset.replicate (G.rootMultiplicity ρ / 2) ρ := by
    intros ρ hρ
    unfold circleRoots at hρ
    rw [Finset.mem_filter] at hρ
    unfold QrootSummand
    rw [if_neg (by linarith : ¬ ‖ρ‖ < 1), if_pos hρ.2]
  have h_outside : ∀ ρ ∈ outsideRoots G, QrootSummand G ρ = 0 := by
    intros ρ hρ
    unfold outsideRoots at hρ
    rw [Finset.mem_filter] at hρ
    unfold QrootSummand
    rw [if_neg (by linarith : ¬ ‖ρ‖ < 1), if_neg (by linarith : ¬ ‖ρ‖ = 1)]
  rw [Finset.sum_congr rfl h_inside, Finset.sum_congr rfl h_circle,
      Finset.sum_congr rfl h_outside, Finset.sum_const_zero, add_zero]

/-- `Multiset.map` distributes over `Finset.sum`. -/
lemma multiset_map_finset_sum {α β ι : Type*} (f : α → β) (s : Finset ι)
    (g : ι → Multiset α) :
    Multiset.map f (∑ i ∈ s, g i) = ∑ i ∈ s, Multiset.map f (g i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intros a t hat ih
    rw [Finset.sum_insert hat, Finset.sum_insert hat, Multiset.map_add, ih]

/-- For circle roots (|ρ| = 1), `reciprocalConj ρ = ρ`. -/
lemma reciprocalConj_eq_self_on_circle {ρ : ℂ} (hρ : ‖ρ‖ = 1) : reciprocalConj ρ = ρ := by
  unfold reciprocalConj
  have hρ_ne : ρ ≠ 0 := by
    intro h; rw [h, norm_zero] at hρ; exact zero_ne_one hρ
  have h_normSq : Complex.normSq ρ = 1 := by
    rw [Complex.normSq_eq_norm_sq, hρ]; norm_num
  have h_mul : ρ * starRingEnd ℂ ρ = 1 := by
    have := Complex.mul_conj ρ
    rw [this, h_normSq]; rfl
  exact inv_eq_of_mul_eq_one_left h_mul

/-- `(image of QrootsMultiset under reciprocalConj) = outside-full + circle-half` for
G with self-Pstar and G(0) ≠ 0. -/
lemma map_reciprocalConj_QrootsMultiset (G : ℂ[X]) (hG_palin : Pstar G = G)
    (hG_ne : G ≠ 0) (hG_zero : G.eval 0 ≠ 0) :
    (QrootsMultiset G).map reciprocalConj =
      (∑ ρ ∈ outsideRoots G, Multiset.replicate (G.rootMultiplicity ρ) ρ) +
      (∑ ρ ∈ circleRoots G, Multiset.replicate (G.rootMultiplicity ρ / 2) ρ) := by
  rw [QrootsMultiset_decompose, Multiset.map_add]
  congr 1
  · -- inside part maps to outside via bijection
    rw [multiset_map_finset_sum]
    -- Replace replicate.map reciprocalConj with replicate (reciprocalConj ρ).
    have : ∀ ρ ∈ insideRoots G,
        (Multiset.replicate (G.rootMultiplicity ρ) ρ).map reciprocalConj =
          Multiset.replicate (G.rootMultiplicity ρ) (reciprocalConj ρ) := by
      intros ρ _; rw [Multiset.map_replicate]
    rw [Finset.sum_congr rfl this]
    -- Now reindex via reciprocalConj bijection inside ↔ outside.
    have h_inj := reciprocalConj_injOn_insideRoots G hG_zero hG_ne
    have h_image := reciprocalConj_insideRoots_eq G hG_palin hG_ne hG_zero
    rw [← h_image]
    rw [Finset.sum_image h_inj]
    -- For each ρ ∈ insideRoots, mult ρ = mult (reciprocalConj ρ).
    apply Finset.sum_congr rfl
    intros ρ hρ
    have h0_notin : (0 : ℂ) ∉ G.roots.toFinset := by
      rw [Multiset.mem_toFinset, Polynomial.mem_roots hG_ne]
      intro h; exact hG_zero h
    unfold insideRoots at hρ
    rw [Finset.mem_filter] at hρ
    have hρ_ne : ρ ≠ 0 := by intro h; rw [h] at hρ; exact h0_notin hρ.1
    have h_pair : G.rootMultiplicity ρ = G.rootMultiplicity (reciprocalConj ρ) := by
      unfold reciprocalConj
      exact rootMultiplicity_pstar_eq G hG_palin ρ hρ_ne hG_ne
    rw [h_pair]
  · -- circle part maps to itself
    rw [show ((∑ ρ ∈ circleRoots G, Multiset.replicate (G.rootMultiplicity ρ / 2) ρ).map
            reciprocalConj) =
          ∑ ρ ∈ circleRoots G, (Multiset.replicate (G.rootMultiplicity ρ / 2) ρ).map
            reciprocalConj by
      rw [multiset_map_finset_sum]]
    apply Finset.sum_congr rfl
    intros ρ hρ
    unfold circleRoots at hρ
    rw [Finset.mem_filter] at hρ
    rw [Multiset.map_replicate]
    rw [reciprocalConj_eq_self_on_circle hρ.2]

/-- `G.roots = inside + circle + outside` (multisets summing replicate by multiplicity). -/
lemma roots_eq_inside_plus_circle_plus_outside' (G : ℂ[X]) :
    G.roots =
      (∑ ρ ∈ insideRoots G, Multiset.replicate (G.rootMultiplicity ρ) ρ) +
      (∑ ρ ∈ circleRoots G, Multiset.replicate (G.rootMultiplicity ρ) ρ) +
      (∑ ρ ∈ outsideRoots G, Multiset.replicate (G.rootMultiplicity ρ) ρ) := by
  classical
  conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq G.roots]
  rw [toFinset_eq_inside_union_circle_union_outside]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
        ⟨insideRoots_outsideRoots_disjoint _, circleRoots_outsideRoots_disjoint _⟩)]
  rw [Finset.sum_union (insideRoots_circleRoots_disjoint _)]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intros ρ _
      rw [Polynomial.count_roots]
      exact Multiset.nsmul_singleton ρ _
    · apply Finset.sum_congr rfl
      intros ρ _
      rw [Polynomial.count_roots]
      exact Multiset.nsmul_singleton ρ _
  · apply Finset.sum_congr rfl
    intros ρ _
    rw [Polynomial.count_roots]
    exact Multiset.nsmul_singleton ρ _

/-- The key combined identity: `QrootsMultiset + image-under-reciprocalConj = G.roots`. -/
lemma QrootsMultiset_add_image_eq_roots (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) (hn : 1 ≤ P.natDegree) :
    QrootsMultiset (Gpoly P) +
      (QrootsMultiset (Gpoly P)).map reciprocalConj =
        (Gpoly P).roots := by
  have hP_ne : P ≠ 0 := by intro h; rw [h, natDegree_zero] at hn; omega
  have hG_ne : Gpoly P ≠ 0 := by
    intro h
    have hND : (Gpoly P).natDegree = 2 * P.natDegree := natDegree_Gpoly P hT hn
    rw [h, natDegree_zero] at hND; omega
  have hG_palin : Pstar (Gpoly P) = Gpoly P := Pstar_Gpoly P hP_ne hT hn
  have hG_zero : (Gpoly P).eval 0 ≠ 0 := by
    have hntd : (Gpoly P).natTrailingDegree = 0 := natTrailingDegree_Gpoly P hP_ne hT hn
    have h_coef : (Gpoly P).coeff 0 ≠ 0 := by
      have hne : (Gpoly P).coeff (Gpoly P).natTrailingDegree ≠ 0 :=
        trailingCoeff_nonzero_iff_nonzero.mpr hG_ne
      rwa [hntd] at hne
    intro h
    apply h_coef
    rw [← Polynomial.coeff_zero_eq_eval_zero] at h
    exact h
  rw [map_reciprocalConj_QrootsMultiset _ hG_palin hG_ne hG_zero]
  rw [QrootsMultiset_decompose]
  rw [roots_eq_inside_plus_circle_plus_outside']
  -- LHS: (inside + circle_half) + (outside + circle_half)
  -- RHS: inside + circle + outside
  -- Need: 2 * circle_half = circle (using even mult).
  have h_circle_double : (∑ ρ ∈ circleRoots (Gpoly P),
        Multiset.replicate ((Gpoly P).rootMultiplicity ρ / 2) ρ) +
      (∑ ρ ∈ circleRoots (Gpoly P),
        Multiset.replicate ((Gpoly P).rootMultiplicity ρ / 2) ρ) =
      ∑ ρ ∈ circleRoots (Gpoly P),
        Multiset.replicate ((Gpoly P).rootMultiplicity ρ) ρ := by
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intros ρ hρ
    rw [← Multiset.replicate_add]
    congr 1
    unfold circleRoots at hρ
    rw [Finset.mem_filter] at hρ
    rcases (even_rootMultiplicity_Gpoly_circle P hT hPbd hG_ne hρ.2) with ⟨k, hk⟩
    omega
  -- Rearrange and apply.
  set i := ∑ ρ ∈ insideRoots (Gpoly P), Multiset.replicate ((Gpoly P).rootMultiplicity ρ) ρ
  set c_half := ∑ ρ ∈ circleRoots (Gpoly P),
    Multiset.replicate ((Gpoly P).rootMultiplicity ρ / 2) ρ
  set c := ∑ ρ ∈ circleRoots (Gpoly P), Multiset.replicate ((Gpoly P).rootMultiplicity ρ) ρ
  set o := ∑ ρ ∈ outsideRoots (Gpoly P), Multiset.replicate ((Gpoly P).rootMultiplicity ρ) ρ
  -- LHS = (i + c_half) + (o + c_half)
  -- RHS = i + c + o
  -- h_circle_double : c_half + c_half = c
  show (i + c_half) + (o + c_half) = i + c + o
  rw [show (i + c_half) + (o + c_half) = i + o + (c_half + c_half) by abel]
  rw [h_circle_double]
  abel

/-- All roots of `Gpoly P` are nonzero (when `natTrailingDegree P = 0`, `n ≥ 1`). -/
lemma roots_Gpoly_ne_zero (P : ℂ[X]) (hT : P.natTrailingDegree = 0) (hn : 1 ≤ P.natDegree)
    (ρ : ℂ) (hρ : ρ ∈ (Gpoly P).roots) : ρ ≠ 0 := by
  have hP_ne : P ≠ 0 := by intro h; rw [h, natDegree_zero] at hn; omega
  have hG_ne : Gpoly P ≠ 0 := by
    intro h
    have hND : (Gpoly P).natDegree = 2 * P.natDegree := natDegree_Gpoly P hT hn
    rw [h, natDegree_zero] at hND; omega
  have hG_zero : (Gpoly P).eval 0 ≠ 0 := by
    have hntd : (Gpoly P).natTrailingDegree = 0 := natTrailingDegree_Gpoly P hP_ne hT hn
    have h_coef : (Gpoly P).coeff 0 ≠ 0 := by
      have hne : (Gpoly P).coeff (Gpoly P).natTrailingDegree ≠ 0 :=
        trailingCoeff_nonzero_iff_nonzero.mpr hG_ne
      rwa [hntd] at hne
    intro h; apply h_coef
    rw [← Polynomial.coeff_zero_eq_eval_zero] at h; exact h
  intro h
  rw [h] at hρ
  rw [Polynomial.mem_roots hG_ne] at hρ
  exact hG_zero hρ

/-- All elements of `QrootsMultiset (Gpoly P)` are nonzero (since they're roots of G). -/
lemma QrootsMultiset_ne_zero (P : ℂ[X]) (hT : P.natTrailingDegree = 0) (hn : 1 ≤ P.natDegree)
    (ρ : ℂ) (hρ : ρ ∈ QrootsMultiset (Gpoly P)) : ρ ≠ 0 := by
  unfold QrootsMultiset at hρ
  rw [Multiset.mem_sum] at hρ
  obtain ⟨σ, hσ_mem, hρ_in⟩ := hρ
  have hσ_root : σ ∈ (Gpoly P).roots := Multiset.mem_toFinset.mp hσ_mem
  have hσ_ne : σ ≠ 0 := roots_Gpoly_ne_zero P hT hn σ hσ_root
  unfold QrootSummand at hρ_in
  split_ifs at hρ_in with h1 h2
  · rw [Multiset.mem_replicate] at hρ_in
    rw [hρ_in.2]; exact hσ_ne
  · rw [Multiset.mem_replicate] at hρ_in
    rw [hρ_in.2]; exact hσ_ne
  · simp at hρ_in

/-- Pstar of a product of linear factors. -/
lemma Pstar_prod_X_sub_C (s : Multiset ℂ) (hs : ∀ ρ ∈ s, ρ ≠ 0) :
    Pstar ((s.map (fun ρ => X - C ρ)).prod) =
      C ((s.map fun ρ => -(starRingEnd ℂ ρ)).prod) *
        (s.map (fun ρ => X - C ((starRingEnd ℂ ρ)⁻¹))).prod := by
  induction s using Multiset.induction with
  | empty =>
    simp [Pstar_one]
  | cons a s ih =>
    have ha : a ≠ 0 := hs a (Multiset.mem_cons_self _ _)
    have hs' : ∀ ρ ∈ s, ρ ≠ 0 := fun ρ hρ => hs ρ (Multiset.mem_cons_of_mem hρ)
    rw [Multiset.map_cons, Multiset.prod_cons, Pstar_mul, ih hs',
        Pstar_X_sub_C_eq a ha]
    rw [Multiset.map_cons, Multiset.prod_cons, Multiset.map_cons, Multiset.prod_cons]
    rw [C_mul, C_neg]
    ring

/-- **Polynomial identity**: `QmonicPart (Gpoly P) · Pstar (QmonicPart (Gpoly P)) =
C (prod) · ∏(X - C ρ) over (Gpoly P).roots`, where `prod` is the product of
`-conj ρ` over `QrootsMultiset (Gpoly P)`. -/
lemma QmonicPart_mul_Pstar_eq (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) (hn : 1 ≤ P.natDegree) :
    QmonicPart (Gpoly P) * Pstar (QmonicPart (Gpoly P)) =
      C (((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod) *
        (((Gpoly P).roots).map (fun ρ => X - C ρ)).prod := by
  unfold QmonicPart
  rw [Pstar_prod_X_sub_C _ (QrootsMultiset_ne_zero P hT hn)]
  -- Setup: A := ∏(X - C ρ) over QrM, B := ∏(X - C(1/conj ρ)) over QrM,
  -- C(p) := C(prod -conj ρ over QrM).
  -- Goal: A * (C(p) * B) = C(p) * (prod over G.roots).
  -- Rearrange: A * (C(p) * B) = C(p) * (A * B) = C(p) * prod over (QrM + image).
  set A := ((QrootsMultiset (Gpoly P)).map (fun ρ => X - C ρ)).prod
  set B := ((QrootsMultiset (Gpoly P)).map (fun ρ => X - C ((starRingEnd ℂ ρ)⁻¹))).prod
  set Cp := C (((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod)
  show A * (Cp * B) = Cp * (((Gpoly P).roots).map (fun ρ => X - C ρ)).prod
  rw [show A * (Cp * B) = Cp * (A * B) by ring]
  congr 1
  -- A * B = prod over (QrM + image of QrM under reciprocalConj) of (X - C ρ).
  show A * B = (((Gpoly P).roots).map (fun ρ => X - C ρ)).prod
  rw [show A * B = (((QrootsMultiset (Gpoly P)).map (fun ρ => X - C ρ)) +
                    ((QrootsMultiset (Gpoly P)).map (fun ρ => X - C ((starRingEnd ℂ ρ)⁻¹)))).prod
        from (Multiset.prod_add _ _).symm]
  have h_map : (QrootsMultiset (Gpoly P)).map (fun ρ => X - C ((starRingEnd ℂ ρ)⁻¹)) =
      ((QrootsMultiset (Gpoly P)).map reciprocalConj).map (fun ρ => X - C ρ) := by
    rw [Multiset.map_map]; rfl
  rw [h_map]
  rw [show ((QrootsMultiset (Gpoly P)).map (fun ρ => X - C ρ)) +
            ((QrootsMultiset (Gpoly P)).map reciprocalConj).map (fun ρ => X - C ρ) =
          (QrootsMultiset (Gpoly P) +
            (QrootsMultiset (Gpoly P)).map reciprocalConj).map (fun ρ => X - C ρ) by
      rw [Multiset.map_add]]
  rw [QrootsMultiset_add_image_eq_roots P hT hPbd hn]

/-- For `G = Gpoly P` with our hypotheses,
`G = C (leadingCoeff G) · ∏(X - C ρ) over G.roots` (via Splits). -/
lemma Gpoly_eq_prod_roots (P : ℂ[X]) (hT : P.natTrailingDegree = 0) (hn : 1 ≤ P.natDegree) :
    Gpoly P = C (leadingCoeff (Gpoly P)) *
      (((Gpoly P).roots).map (fun ρ => X - C ρ)).prod := by
  have hG_ne : Gpoly P ≠ 0 := by
    intro h
    have hND : (Gpoly P).natDegree = 2 * P.natDegree := natDegree_Gpoly P hT hn
    rw [h, natDegree_zero] at hND; omega
  have h_split : (Gpoly P).Splits := IsAlgClosed.splits (Gpoly P)
  exact h_split.eq_prod_roots

/-- **Clean polynomial identity**:
`C (leadingCoeff (Gpoly P)) · QmonicPart · Pstar QmonicPart = C (prod) · Gpoly P`. -/
lemma scaled_QmonicPart_identity (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) (hn : 1 ≤ P.natDegree) :
    C (leadingCoeff (Gpoly P)) * (QmonicPart (Gpoly P) * Pstar (QmonicPart (Gpoly P))) =
      C (((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod) * Gpoly P := by
  set prodConst := C (((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod) with hp_def
  set lcConst := C (leadingCoeff (Gpoly P)) with hl_def
  set rootProd := (((Gpoly P).roots).map (fun ρ => X - C ρ)).prod with hr_def
  have h1 : QmonicPart (Gpoly P) * Pstar (QmonicPart (Gpoly P)) = prodConst * rootProd :=
    QmonicPart_mul_Pstar_eq P hT hPbd hn
  have h2 : Gpoly P = lcConst * rootProd := Gpoly_eq_prod_roots P hT hn
  rw [h1, h2]
  ring

/-- The leading coefficient of `Gpoly P` is nonzero (since natDegree = 2n ≥ 2). -/
lemma leadingCoeff_Gpoly_ne_zero (P : ℂ[X]) (hT : P.natTrailingDegree = 0) (hn : 1 ≤ P.natDegree) :
    leadingCoeff (Gpoly P) ≠ 0 := by
  intro h
  apply (show Gpoly P ≠ 0 by
    intro h
    have hND : (Gpoly P).natDegree = 2 * P.natDegree := natDegree_Gpoly P hT hn
    rw [h, natDegree_zero] at hND; omega)
  exact leadingCoeff_eq_zero.mp h

/-- The QrM-product is nonzero (product of nonzero complex numbers). -/
lemma QrootsMultiset_neg_conj_prod_ne_zero (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hn : 1 ≤ P.natDegree) :
    (((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod) ≠ 0 := by
  intro h
  rw [Multiset.prod_eq_zero_iff] at h
  rw [Multiset.mem_map] at h
  obtain ⟨ρ, hρ_mem, hρ_eq⟩ := h
  have hρ_ne : ρ ≠ 0 := QrootsMultiset_ne_zero P hT hn ρ hρ_mem
  apply hρ_ne
  have h_conj_zero : starRingEnd ℂ ρ = 0 := by linear_combination -hρ_eq
  have hinj : Function.Injective (starRingEnd ℂ) := RingHom.injective _
  exact hinj (by rw [h_conj_zero, map_zero])

/-! ## Existence of Q

The full Q construction `∃ Q, Q · Pstar Q = Gpoly P` requires the analytic fact
that `lc/prod ∈ ℝ_{≥0}`, where `lc = leadingCoeff (Gpoly P)` and `prod =
∏ -conj ρ` over `QrootsMultiset`. This follows from evaluating the scaled
polynomial identity `C(lc) · QmonicPart · Pstar QmonicPart = C(prod) · Gpoly P`
at any point `z₀` on the unit circle where both `QmonicPart(z₀) ≠ 0` and
`|P(z₀)| < 1`. Such `z₀` exists by cardinality (QmonicPart has only finitely
many roots; if `|P| ≡ 1` on the circle then `Gpoly P = 0`, contradicting
`natDegree Gpoly P = 2n ≥ 2`).

The remaining steps then are:
1. Pick `z₀` with both conditions.
2. Derive `lc · |QmonicPart(z₀)|² = prod · (1 - |P(z₀)|²)`, hence `lc/prod ∈ ℝ_{>0}`.
3. Set `c := Real.sqrt ((lc/prod).re)` cast to `ℂ`, satisfying `c · conj c = lc/prod`.
4. Define `Q := C c · QmonicPart`. Then `Q · Pstar Q = Gpoly P`.
5. Show `natDegree Q ≤ P.natDegree` using `natDegree_QmonicPart` and the
   cardinality computation.
6. On the unit circle, `|P|² + |Q|² = 1` follows from `Q · Pstar Q = Gpoly P`
   plus `Gpoly_eval_on_circle` and `Pstar_eval_on_circle`.
7. Handle the `n = 0` case (constant `P`) and `Gpoly P = 0` case separately,
   using `X^m` reduction for the `natTrailingDegree > 0` case.
8. Wrap up in `Submission.lean`. -/

/-- `G.roots = inside + circle + outside` (as multisets, summing replicate by multiplicity). -/
lemma roots_eq_inside_plus_circle_plus_outside (G : ℂ[X]) :
    G.roots =
      (∑ ρ ∈ insideRoots G, Multiset.replicate (G.rootMultiplicity ρ) ρ) +
      (∑ ρ ∈ circleRoots G, Multiset.replicate (G.rootMultiplicity ρ) ρ) +
      (∑ ρ ∈ outsideRoots G, Multiset.replicate (G.rootMultiplicity ρ) ρ) := by
  classical
  conv_lhs => rw [← Multiset.toFinset_sum_count_nsmul_eq G.roots]
  rw [toFinset_eq_inside_union_circle_union_outside]
  rw [Finset.sum_union (Finset.disjoint_union_left.mpr
        ⟨insideRoots_outsideRoots_disjoint _, circleRoots_outsideRoots_disjoint _⟩)]
  rw [Finset.sum_union (insideRoots_circleRoots_disjoint _)]
  congr 1
  · congr 1
    · apply Finset.sum_congr rfl
      intros ρ _
      rw [Polynomial.count_roots]
      exact Multiset.nsmul_singleton ρ _
    · apply Finset.sum_congr rfl
      intros ρ _
      rw [Polynomial.count_roots]
      exact Multiset.nsmul_singleton ρ _
  · apply Finset.sum_congr rfl
    intros ρ _
    rw [Polynomial.count_roots]
    exact Multiset.nsmul_singleton ρ _

/-- Total root-multiplicity sum (over distinct roots) equals card of roots multiset. -/
lemma sum_rootMultiplicity_eq_card_roots (G : ℂ[X]) :
    ∑ ρ ∈ G.roots.toFinset, G.rootMultiplicity ρ = G.roots.card := by
  classical
  conv_lhs =>
    rw [show (fun ρ => G.rootMultiplicity ρ) = (fun ρ => G.roots.count ρ) by
      ext ρ
      rw [← Polynomial.count_roots]]
  rw [← Multiset.toFinset_sum_count_eq G.roots]

-- Note: cardinality of `QrootsMultiset` can be computed as a sum over the
-- attached finset; the multiset/finset bookkeeping is intricate enough that
-- it's left for a follow-up session.

/-! ## Status note

The remaining work for `exists_complementary_polynomial_on_unit_circle` is the
Fejér–Riesz spectral factorization. Concretely, we have established that

* `Gpoly P (z) = z^n · (1 - |P z|²)` on `|z| = 1` (when `natTrailingDegree P = 0`);
* `Pstar (P · Pstar P) = P · Pstar P`, which combined with `Pstar (X^n) = X^n`
  gives `Pstar (Gpoly P) = Gpoly P` (the algebraic self-reciprocity of `G`).

To finish, one needs (writing `G := Gpoly P`):

1. Factor `G` over `ℂ` as `c · ∏(X - ρᵢ)` (uses `IsAlgClosed.splits` + `Splits.eq_prod_roots`).
2. From `Pstar G = G` deduce that the root multiset is closed under `ρ ↦ 1/conj ρ`.
3. From `G/z^n ≥ 0` on `|z| = 1` deduce that any root `ρ` with `|ρ| = 1` has even
   multiplicity in `G` (real-analytic Taylor argument: locally `h(θ) ~ c · θ^m`
   for `h` non-negative forces `m` even).
4. Choose `S = roots(G)` restricted to `|ρ| < 1` (with multiplicity) plus half of
   the circle roots (now well-defined by (3)). Then `|S| = (deg G)/2 = n`.
5. Define `Q := √α · ∏_{ρ ∈ S} (X - ρ)` for the unique `α > 0` making `Q · Pstar Q = G`.
6. Conclude `|Q|² = G/z^n = 1 - |P|²` on the circle.

Step (3) is the main analytic difficulty; the rest is multiset/polynomial bookkeeping.
-/

end Submission.Helpers
