import Submission.DeBrangesInitial
import Submission.ClausenGeneric

namespace Submission

open Finset PowerSeries

noncomputable def gasperWeightRatio (k m j : ℕ) : ℝ :=
  (((m - 2 * j : ℕ) : ℝ) * ((m - (2 * j + 1) : ℕ) : ℝ) *
      ((m + 2 * k + 2 * j + 2 : ℕ) : ℝ) *
      ((m + 2 * k + 2 * j + 3 : ℕ) : ℝ) *
      ((2 * k + 2 * j + 1 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) /
    (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
      ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
      ((2 * k + 4 * j + 3 : ℕ) : ℝ) ^ 2 *
      ((2 * k + 4 * j + 5 : ℕ) : ℝ))

noncomputable def gasperWeight (k m : ℕ) : ℕ → ℝ
  | 0 => 1
  | j + 1 => gasperWeight k m j * gasperWeightRatio k m j

lemma gasperWeightRatio_nonneg (k m j : ℕ) : 0 ≤ gasperWeightRatio k m j := by
  unfold gasperWeightRatio
  positivity

lemma gasperWeight_nonneg (k m j : ℕ) : 0 ≤ gasperWeight k m j := by
  induction j with
  | zero => simp [gasperWeight]
  | succ j ih =>
      rw [gasperWeight]
      exact mul_nonneg ih (gasperWeightRatio_nonneg k m j)

noncomputable def gasperSquareCoeff (k s j extra : ℕ) : ℕ → ℝ
  | 0 => 1
  | q + 1 =>
      gasperSquareCoeff k s j extra q *
        (-((s - j - q : ℕ) : ℝ)) *
        (2 * ((k + s + 1 + extra + j + q : ℕ) : ℝ)) /
        (((2 * k + 3 + 4 * j + 2 * q : ℕ) : ℝ) * ((q + 1 : ℕ) : ℝ))

noncomputable def gasperSquarePolynomial (k s j extra : ℕ) (x : ℝ) : ℝ :=
  ∑ q ∈ range (s - j + 1), gasperSquareCoeff k s j extra q * x ^ q

lemma gasperSquareCoeff_eq_gaussRecCoeff {k s j extra q : ℕ}
    (hq : q ≤ s - j) :
    gasperSquareCoeff k s j extra q =
      gaussRecCoeff (-((s - j : ℕ) : ℝ))
        ((k + s + 1 + extra + j : ℕ) : ℝ)
        (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) q := by
  induction q with
  | zero => simp [gasperSquareCoeff, gaussRecCoeff]
  | succ q ih =>
      have hq' : q ≤ s - j := by omega
      rw [gasperSquareCoeff, gaussRecCoeff, ih hq']
      rw [Nat.cast_sub (R := ℝ) (by omega : q ≤ s - j)]
      push_cast
      field_simp
      ring

lemma gasperSquareCoeff_add_succ_eq_zero (k s j extra q : ℕ) :
    gasperSquareCoeff k s j extra (s - j + 1 + q) = 0 := by
  induction q with
  | zero =>
      rw [show s - j + 1 + 0 = (s - j) + 1 by omega, gasperSquareCoeff]
      simp
  | succ q ih =>
      rw [show s - j + 1 + (q + 1) = (s - j + 1 + q) + 1 by omega,
        gasperSquareCoeff, ih]
      simp

lemma gasperSquareCoeff_eq_zero {k s j extra q : ℕ} (hq : s - j < q) :
    gasperSquareCoeff k s j extra q = 0 := by
  have hq' : q = s - j + 1 + (q - (s - j + 1)) := by omega
  rw [hq', gasperSquareCoeff_add_succ_eq_zero]

noncomputable def gasperSquareSeries (k s j extra : ℕ) : ℝ⟦X⟧ :=
  PowerSeries.mk (gasperSquareCoeff k s j extra)

lemma gasperSquareSeries_eq_gaussRecSeries (k s j extra : ℕ) :
    gasperSquareSeries k s j extra =
      gaussRecSeries (-((s - j : ℕ) : ℝ))
        ((k + s + 1 + extra + j : ℕ) : ℝ)
        (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) := by
  ext q
  simp only [gasperSquareSeries, PowerSeries.coeff_mk, coeff_gaussRecSeries]
  by_cases hq : q ≤ s - j
  · exact gasperSquareCoeff_eq_gaussRecCoeff hq
  · rw [gasperSquareCoeff_eq_zero (by omega),
      gaussRecCoeff_neg_nat_eq_zero _ _ (by omega)]

lemma gasperEvenSquareSeries_sq_eq_clausen (k s j : ℕ) (hj : j ≤ s) :
    gasperSquareSeries k s j 0 ^ 2 =
      clausenRecSeries (-((s - j : ℕ) : ℝ))
        ((k + s + 1 + j : ℕ) : ℝ)
        (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) := by
  rw [gasperSquareSeries_eq_gaussRecSeries, pow_two]
  apply gaussRecSquareSeries_eq_clausenRecSeries
  · push_cast
    rw [Nat.cast_sub (R := ℝ) hj]
    ring
  · intro q
    positivity
  · intro q
    push_cast
    rw [Nat.cast_sub (R := ℝ) hj]
    ring_nf
    positivity

noncomputable def gasperEvenInnerCoeff (k s j n : ℕ) : ℝ :=
  clausenRecCoeff (-((s - j : ℕ) : ℝ))
    ((k + s + 1 + j : ℕ) : ℝ)
    (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) n

set_option maxRecDepth 10000 in
lemma gasperEvenInnerCoeff_shift_two {k s j : ℕ} (hj : j < s) (n : ℕ) :
    gasperEvenInnerCoeff k s (j + 1) n *
        ((-2 * ((s - j : ℕ) : ℝ)) * (-2 * ((s - j : ℕ) : ℝ) + 1) *
          (2 * ((k + s + 1 + j : ℕ) : ℝ)) *
          (2 * ((k + s + 1 + j : ℕ) : ℝ) + 1) *
          ((k + 1 + 2 * j : ℕ) : ℝ) * ((k + 2 + 2 * j : ℕ) : ℝ)) *
        (((2 * k + 2 + 4 * j : ℕ) : ℝ) + (n + 2)) *
          (((2 * k + 2 + 4 * j : ℕ) : ℝ) + (n + 3)) =
      gasperEvenInnerCoeff k s j (n + 2) *
        (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
          (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) *
          ((((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) + 1) *
          ((2 * k + 2 + 4 * j : ℕ) : ℝ) *
          (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 1) *
          (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 2) *
          (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 3)) := by
  have hden (q : ℕ) :
      2 * (-((s - j : ℕ) : ℝ) + ((k + s + 1 + j : ℕ) : ℝ)) + q ≠ 0 ∧
        ((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2 + q ≠ 0 := by
    constructor <;> push_cast
    · rw [Nat.cast_sub (R := ℝ) hj.le]
      ring_nf
      positivity
    · positivity
  have h := clausenRecCoeff_shift_two
    (a := -((s - j : ℕ) : ℝ))
    (b := ((k + s + 1 + j : ℕ) : ℝ))
    (c := ((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) n hden
  rw [gasperEvenInnerCoeff, gasperEvenInnerCoeff]
  rw [Nat.cast_sub (R := ℝ) hj.le] at h ⊢
  rw [Nat.cast_sub (R := ℝ) (by omega : j + 1 ≤ s)]
  push_cast at h ⊢
  convert h using 1
  all_goals ring_nf

lemma gasperWeightRatio_even {k s j : ℕ} (hj : j < s) :
    gasperWeightRatio k (2 * s) j =
      ((2 * ((s - j : ℕ) : ℝ)) * (2 * ((s - j : ℕ) : ℝ) - 1) *
        (2 * ((k + s + 1 + j : ℕ) : ℝ)) *
        (2 * ((k + s + 1 + j : ℕ) : ℝ) + 1) *
        ((2 * k + 2 * j + 1 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) /
      (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
        ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
        ((2 * k + 4 * j + 3 : ℕ) : ℝ) ^ 2 *
        ((2 * k + 4 * j + 5 : ℕ) : ℝ)) := by
  unfold gasperWeightRatio
  rw [show 2 * s - 2 * j = 2 * (s - j) by omega,
    show 2 * s - (2 * j + 1) = 2 * (s - j) - 1 by omega]
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ 2 * (s - j))]
  push_cast
  congr 1
  all_goals ring

set_option maxRecDepth 10000 in
lemma gasperEvenAdjacentTerm {k s j : ℕ} (hj : j < s) (n : ℕ) :
    gasperWeight k (2 * s) (j + 1) * gasperEvenInnerCoeff k s (j + 1) n *
        (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
          ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
          ((2 * k + 4 * j + n + 4 : ℕ) : ℝ) *
          ((2 * k + 4 * j + n + 5 : ℕ) : ℝ)) =
      gasperWeight k (2 * s) j * gasperEvenInnerCoeff k s j (n + 2) *
        (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
          ((2 * k + 2 * j + 1 : ℕ) : ℝ) *
          ((2 * k + 4 * j + 5 : ℕ) : ℝ) *
          ((2 * j + 1 : ℕ) : ℝ)) := by
  have hshift := gasperEvenInnerCoeff_shift_two (k := k) hj n
  rw [gasperWeight, gasperWeightRatio_even hj]
  have hcancel :
      (((2 * k + 4 * j + 2 : ℕ) : ℝ) *
        ((2 * k + 4 * j + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
  apply mul_left_cancel₀ hcancel
  let F : ℝ :=
    4 * gasperWeight k (2 * s) j * ((2 * k + 2 * j + 1 : ℕ) : ℝ) *
      ((2 * j + 1 : ℕ) : ℝ) /
        (((2 * k + 4 * j + 3 : ℕ) : ℝ) ^ 2 *
          ((2 * k + 4 * j + 5 : ℕ) : ℝ))
  calc
    (((2 * k + 4 * j + 2 : ℕ) : ℝ) * ((2 * k + 4 * j + 4 : ℕ) : ℝ)) *
          (gasperWeight k (2 * s) j *
            (((2 * ((s - j : ℕ) : ℝ)) * (2 * ((s - j : ℕ) : ℝ) - 1) *
              (2 * ((k + s + 1 + j : ℕ) : ℝ)) *
              (2 * ((k + s + 1 + j : ℕ) : ℝ) + 1) *
              ((2 * k + 2 * j + 1 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) /
              (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
                ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
                ((2 * k + 4 * j + 3 : ℕ) : ℝ) ^ 2 *
                ((2 * k + 4 * j + 5 : ℕ) : ℝ))) *
            gasperEvenInnerCoeff k s (j + 1) n *
            (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
              ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
              ((2 * k + 4 * j + n + 4 : ℕ) : ℝ) *
              ((2 * k + 4 * j + n + 5 : ℕ) : ℝ))) =
        F *
          (gasperEvenInnerCoeff k s (j + 1) n *
            ((-2 * ((s - j : ℕ) : ℝ)) * (-2 * ((s - j : ℕ) : ℝ) + 1) *
              (2 * ((k + s + 1 + j : ℕ) : ℝ)) *
              (2 * ((k + s + 1 + j : ℕ) : ℝ) + 1) *
              ((k + 1 + 2 * j : ℕ) : ℝ) * ((k + 2 + 2 * j : ℕ) : ℝ)) *
            (((2 * k + 2 + 4 * j : ℕ) : ℝ) + (n + 2)) *
              (((2 * k + 2 + 4 * j : ℕ) : ℝ) + (n + 3))) := by
        dsimp only [F]
        push_cast
        field_simp
        ring
    _ = F *
          (gasperEvenInnerCoeff k s j (n + 2) *
            (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
              (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) *
              ((((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) + 1) *
              ((2 * k + 2 + 4 * j : ℕ) : ℝ) *
              (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 1) *
              (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 2) *
              (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 3))) := by rw [hshift]
    _ = (((2 * k + 4 * j + 2 : ℕ) : ℝ) *
          ((2 * k + 4 * j + 4 : ℕ) : ℝ)) *
        (gasperWeight k (2 * s) j * gasperEvenInnerCoeff k s j (n + 2) *
          (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
            ((2 * k + 2 * j + 1 : ℕ) : ℝ) *
            ((2 * k + 4 * j + 5 : ℕ) : ℝ) *
            ((2 * j + 1 : ℕ) : ℝ))) := by
        dsimp only [F]
        push_cast
        field_simp
        ring

noncomputable def gasperEvenSquareSum (k s : ℕ) (x : ℝ) : ℝ :=
  ∑ j ∈ range (s + 1),
    gasperWeight k (2 * s) j * x ^ (2 * j) *
      gasperSquarePolynomial k s j 0 x ^ 2

noncomputable def gasperOddSquareSum (k s : ℕ) (x : ℝ) : ℝ :=
  (1 - x) * ∑ j ∈ range (s + 1),
    gasperWeight k (2 * s + 1) j * x ^ (2 * j) *
      gasperSquarePolynomial k s j 1 x ^ 2

lemma even_pow_nonneg (x : ℝ) (j : ℕ) : 0 ≤ x ^ (2 * j) := by
  rw [show 2 * j = j + j by omega, pow_add]
  simpa [pow_two] using sq_nonneg (x ^ j)

lemma gasperEvenSquareSum_nonneg (k s : ℕ) (x : ℝ) :
    0 ≤ gasperEvenSquareSum k s x := by
  rw [gasperEvenSquareSum]
  apply sum_nonneg
  intro j hj
  exact mul_nonneg
    (mul_nonneg (gasperWeight_nonneg k (2 * s) j) (even_pow_nonneg x j))
    (sq_nonneg _)

lemma gasperOddSquareSum_nonneg (k s : ℕ) {x : ℝ} (hx : x ≤ 1) :
    0 ≤ gasperOddSquareSum k s x := by
  rw [gasperOddSquareSum]
  apply mul_nonneg (sub_nonneg.mpr hx)
  apply sum_nonneg
  intro j hj
  exact mul_nonneg
    (mul_nonneg (gasperWeight_nonneg k (2 * s + 1) j) (even_pow_nonneg x j))
    (sq_nonneg _)

noncomputable def deBrangesPolynomial (k m : ℕ) (x : ℝ) : ℝ :=
  ∑ r ∈ range (m + 1), deBrangesInitialTerm k m r * x ^ r

lemma deBrangesQCoefficient_add_eq_initial (k m r : ℕ) (hk : 0 < k)
    (hr : r ≤ m) :
    deBrangesQCoefficient (k + m) k (k + r) = deBrangesInitialTerm k m r := by
  rw [deBrangesQCoefficient,
    if_pos ⟨hk, Nat.le_add_right k r, by omega⟩]
  rw [deBrangesInitialTerm, if_pos hr]
  simp only [show k + r - k = r by omega,
    show 2 * (k + r) = 2 * k + 2 * r by omega,
    show k + m + (k + r) + 1 = 2 * k + m + r + 1 by omega,
    show k + m - (k + r) = m - r by omega]

lemma exp_neg_nat_mul_eq_pow (r : ℕ) (t : ℝ) :
    Real.exp (-((r : ℝ) * t)) = Real.exp (-t) ^ r := by
  rw [← Real.exp_nat_mul]
  congr 1
  ring

lemma explicitDeBrangesQ_eq_exp_mul_polynomial (k m : ℕ) (hk : 0 < k) (t : ℝ) :
    explicitDeBrangesQ (k + m) k t =
      Real.exp (-((k : ℝ) * t)) * deBrangesPolynomial k m (Real.exp (-t)) := by
  rw [explicitDeBrangesQ, show k + m + 1 = k + (m + 1) by omega, sum_range_add]
  have hprefix :
      (∑ j ∈ range k,
        deBrangesQCoefficient (k + m) k j * Real.exp (-((j : ℝ) * t))) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hjlt : j < k := mem_range.mp hj
    have hjk : ¬k ≤ j := by omega
    simp [deBrangesQCoefficient, hjk]
  rw [hprefix, zero_add, deBrangesPolynomial, Finset.mul_sum]
  apply sum_congr rfl
  intro r hr
  have hrle : r ≤ m := Nat.le_of_lt_succ (mem_range.mp hr)
  rw [deBrangesQCoefficient_add_eq_initial k m r hk hrle]
  rw [show -((((k + r : ℕ) : ℝ)) * t) =
      -((k : ℝ) * t) + -((r : ℝ) * t) by push_cast; ring,
    Real.exp_add, exp_neg_nat_mul_eq_pow r t]
  ring

def SatisfiesEvenGasperIdentity (k s : ℕ) : Prop :=
  ∀ x : ℝ,
    deBrangesPolynomial k (2 * s) x =
      (Nat.choose (2 * k + 2 * s + 1) (2 * s) : ℝ) *
        gasperEvenSquareSum k s x

def SatisfiesOddGasperIdentity (k s : ℕ) : Prop :=
  ∀ x : ℝ,
    deBrangesPolynomial k (2 * s + 1) x =
      (Nat.choose (2 * k + (2 * s + 1) + 1) (2 * s + 1) : ℝ) *
        gasperOddSquareSum k s x

def SatisfiesGasperIdentities : Prop :=
  (∀ k s : ℕ, 0 < k → SatisfiesEvenGasperIdentity k s) ∧
    ∀ k s : ℕ, 0 < k → SatisfiesOddGasperIdentity k s

lemma satisfiesEvenGasperIdentity_zero (k : ℕ) :
    SatisfiesEvenGasperIdentity k 0 := by
  intro x
  simp [deBrangesPolynomial, deBrangesInitialTerm,
    gasperEvenSquareSum, gasperWeight, gasperSquarePolynomial, gasperSquareCoeff]

lemma satisfiesOddGasperIdentity_zero (k : ℕ) :
    SatisfiesOddGasperIdentity k 0 := by
  intro x
  simp [deBrangesPolynomial, deBrangesInitialTerm, Finset.sum_range_succ,
    gasperOddSquareSum, gasperWeight, gasperSquarePolynomial, gasperSquareCoeff,
    Nat.choose_one_right]
  ring

lemma deBrangesPolynomial_even_nonneg_of_gasper {k s : ℕ}
    (hgasper : SatisfiesEvenGasperIdentity k s) (x : ℝ) :
    0 ≤ deBrangesPolynomial k (2 * s) x := by
  rw [hgasper x]
  exact mul_nonneg (by positivity) (gasperEvenSquareSum_nonneg k s x)

lemma deBrangesPolynomial_odd_nonneg_of_gasper {k s : ℕ}
    (hgasper : SatisfiesOddGasperIdentity k s) {x : ℝ} (hx : x ≤ 1) :
    0 ≤ deBrangesPolynomial k (2 * s + 1) x := by
  rw [hgasper x]
  exact mul_nonneg (by positivity) (gasperOddSquareSum_nonneg k s hx)

lemma explicitDeBrangesQ_nonneg_of_gasper (hgasper : SatisfiesGasperIdentities)
    {k m : ℕ} (hk : 0 < k) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ explicitDeBrangesQ (k + m) k t := by
  rw [explicitDeBrangesQ_eq_exp_mul_polynomial k m hk t]
  apply mul_nonneg (Real.exp_pos _).le
  rcases Nat.even_or_odd m with ⟨s, hs⟩ | ⟨s, hs⟩
  · subst m
    simpa [two_mul] using
      deBrangesPolynomial_even_nonneg_of_gasper (hgasper.1 k s hk) (Real.exp (-t))
  · subst m
    have hx : Real.exp (-t) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      linarith
    simpa [two_mul] using
      deBrangesPolynomial_odd_nonneg_of_gasper (hgasper.2 k s hk) hx

lemma explicitDeBrangesTauDot_nonpos_of_gasper (hgasper : SatisfiesGasperIdentities)
    {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) {t : ℝ} (ht : 0 ≤ t) :
    explicitDeBrangesTauDot N k t ≤ 0 := by
  have hN : N = k + (N - k) := by omega
  rw [hN]
  exact explicitDeBrangesTauDot_nonpos_of_Q_nonneg hk
    (explicitDeBrangesQ_nonneg_of_gasper hgasper hk ht)

end Submission
