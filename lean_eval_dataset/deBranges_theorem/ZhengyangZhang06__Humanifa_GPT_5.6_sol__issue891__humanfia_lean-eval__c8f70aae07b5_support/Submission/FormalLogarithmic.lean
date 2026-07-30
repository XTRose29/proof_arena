import Submission.RiemannConvergence
import Submission.LoewnerApproximation

open Filter Metric

namespace Submission

lemma taylorCoeff_power_monomial (d i : ℕ) :
    taylorCoeff (fun z : ℂ ↦ z ^ d) i = if i = d then 1 else 0 := by
  rw [taylorCoeff, iteratedDeriv_fun_pow_zero]
  by_cases hid : i = d
  · subst i
    simp [Nat.factorial_ne_zero]
  · simp [hid]

lemma taylorCoeff_finset_sum_formal
    {I : Type*} {s : Finset I} {F : I → ℂ → ℂ} {n : ℕ}
    (hF : ∀ i ∈ s, ContDiffAt ℂ n (F i) 0) :
    taylorCoeff (fun z ↦ ∑ i ∈ s, F i z) n =
      ∑ i ∈ s, taylorCoeff (F i) n := by
  rw [taylorCoeff, iteratedDeriv_fun_sum hF, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

lemma taylorCoeff_const_mul_formal (c : ℂ) (F : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (fun z ↦ c * F z) n = c * taylorCoeff F n := by
  simp only [taylorCoeff, iteratedDeriv_const_mul_field]
  ring

/-- The logarithmic coefficients determined, triangularly, by the Taylor
coefficients of a normalized power series. -/
noncomputable def formalLogarithmicCoeff (a : ℕ → ℂ) : ℕ → ℂ
  | 0 => 0
  | n + 1 =>
      a (n + 2) / 2 -
        (∑ j ∈ Finset.range n,
          a (j + 2) *
            (((n - j : ℕ) : ℂ) * (2 * formalLogarithmicCoeff a (n - j)))) /
          (2 * ((n + 1 : ℕ) : ℂ))

lemma formalLogarithmicCoeff_eq_logarithmicCoeff
    {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (ball 0 R))
    (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0)
    (hf1 : taylorCoeff f 1 = 1)
    (hexp : ∀ z ∈ ball (0 : ℂ) R,
      Complex.exp (L z) = dslope f 0 z) :
    ∀ n : ℕ, formalLogarithmicCoeff (taylorCoeff f) n =
      logarithmicCoeff L n := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [formalLogarithmicCoeff, logarithmicCoeff, taylorCoeff, hL0]
      | succ n =>
          have hrec := normalized_log_recurrence hR hf hL hexp n
          rw [Finset.sum_range_succ'] at hrec
          have htail :
              (∑ j ∈ Finset.range n,
                taylorCoeff f (j + 1 + 1) *
                  (((n - (j + 1) + 1 : ℕ) : ℂ) *
                    (2 * logarithmicCoeff L (n - (j + 1) + 1)))) =
                ∑ j ∈ Finset.range n,
                  taylorCoeff f (j + 2) *
                    (((n - j : ℕ) : ℂ) *
                      (2 * logarithmicCoeff L (n - j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            have hjn := Finset.mem_range.mp hj
            rw [show j + 1 + 1 = j + 2 by omega,
              show n - (j + 1) + 1 = n - j by omega]
          rw [htail] at hrec
          simp only [Nat.zero_add, Nat.sub_zero, Nat.cast_add, Nat.cast_one,
            hf1, one_mul] at hrec
          have hlower (j : ℕ) (hj : j ∈ Finset.range n) :
              formalLogarithmicCoeff (taylorCoeff f) (n - j) =
                logarithmicCoeff L (n - j) := by
            apply ih
            have hjn := Finset.mem_range.mp hj
            omega
          have htail' :
              (∑ j ∈ Finset.range n,
                taylorCoeff f (j + 2) *
                  (((n - j : ℕ) : ℂ) *
                    (2 * logarithmicCoeff L (n - j)))) =
                ∑ j ∈ Finset.range n,
                  taylorCoeff f (j + 2) *
                    (((n - j : ℕ) : ℂ) *
                      (2 * formalLogarithmicCoeff (taylorCoeff f) (n - j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [hlower j hj]
          rw [htail'] at hrec
          rw [formalLogarithmicCoeff]
          let S : ℂ := ∑ j ∈ Finset.range n,
            taylorCoeff f (j + 2) *
              (((n - j : ℕ) : ℂ) *
                (2 * formalLogarithmicCoeff (taylorCoeff f) (n - j)))
          let q : ℂ := ((n + 1 : ℕ) : ℂ)
          have hq : q ≠ 0 := by
            dsimp only [q]
            exact_mod_cast Nat.succ_ne_zero n
          have hrecS :
              q * taylorCoeff f (n + 2) =
                S + q * (2 * logarithmicCoeff L (n + 1)) := by
            dsimp only [q, S]
            push_cast
            exact hrec
          calc
            taylorCoeff f (n + 2) / 2 - S / (2 * q) =
                (q * taylorCoeff f (n + 2) - S) / (2 * q) := by
              field_simp [hq]
            _ = (q * (2 * logarithmicCoeff L (n + 1))) / (2 * q) := by
              congr 1
              linear_combination hrecS
            _ = logarithmicCoeff L (n + 1) := by
              field_simp [hq]

lemma tendsto_formalLogarithmicCoeff
    {a : ℕ → ℂ} {A : ℕ → ℕ → ℂ}
    (hA : ∀ n : ℕ, Tendsto (fun j ↦ A j n) atTop (nhds (a n))) :
    ∀ n : ℕ,
      Tendsto (fun j ↦ formalLogarithmicCoeff (A j) n) atTop
        (nhds (formalLogarithmicCoeff a n)) := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
      cases n with
      | zero =>
          simp [formalLogarithmicCoeff]
      | succ n =>
          simp only [formalLogarithmicCoeff]
          apply ((hA (n + 2)).div_const 2).sub
          apply (tendsto_finsetSum (Finset.range n) ?_).div_const
          intro j hj
          apply (hA (j + 2)).mul
          apply tendsto_const_nhds.mul
          exact (ih (n - j) (by
            have hjn := Finset.mem_range.mp hj
            omega)).const_mul 2

noncomputable def formalLogarithmicPolynomial
    (a : ℕ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range N,
    (2 * formalLogarithmicCoeff a (k + 1)) * z ^ (k + 1)

lemma taylorCoeff_formalLogarithmicPolynomial
    (a : ℕ → ℂ) {N n : ℕ} (hn : n ∈ Finset.range N) :
    taylorCoeff (formalLogarithmicPolynomial a N) (n + 1) =
      2 * formalLogarithmicCoeff a (n + 1) := by
  unfold formalLogarithmicPolynomial
  rw [taylorCoeff_finset_sum_formal]
  · rw [Finset.sum_eq_single n]
    · rw [taylorCoeff_const_mul_formal, taylorCoeff_power_monomial, if_pos rfl,
        mul_one]
    · intro k hk hkn
      rw [taylorCoeff_const_mul_formal, taylorCoeff_power_monomial,
        if_neg (by omega), mul_zero]
    · exact fun hnot ↦ (hnot hn).elim
  · intro k hk
    fun_prop

lemma logarithmicCoeff_formalLogarithmicPolynomial
    (a : ℕ → ℂ) {N n : ℕ} (hn : n ∈ Finset.range N) :
    logarithmicCoeff (formalLogarithmicPolynomial a N) (n + 1) =
      formalLogarithmicCoeff a (n + 1) := by
  rw [logarithmicCoeff, taylorCoeff_formalLogarithmicPolynomial a hn]
  ring

lemma tendsto_logarithmicCoeff_formalLogarithmicPolynomial
    {a : ℕ → ℂ} {A : ℕ → ℕ → ℂ}
    (hA : ∀ n : ℕ, Tendsto (fun j ↦ A j n) atTop (nhds (a n)))
    {N n : ℕ} (hn : n ∈ Finset.range N) :
    Tendsto
      (fun j ↦ logarithmicCoeff (formalLogarithmicPolynomial (A j) N) (n + 1))
      atTop (nhds (formalLogarithmicCoeff a (n + 1))) := by
  simpa only [logarithmicCoeff_formalLogarithmicPolynomial _ hn] using
    tendsto_formalLogarithmicCoeff hA (n + 1)

lemma exists_orderwise_formalLogarithmicPolynomial_approximation
    {f L : ℂ → ℂ} {R : ℝ} (hR1 : 1 < R)
    (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R,
      Complex.exp (L z) = dslope f 0 z) :
    ∃ A : ℕ → ℕ → ℂ → ℂ,
      ∀ N k, k ∈ Finset.range N →
        Tendsto (fun j ↦ logarithmicCoeff (A N j) (k + 1)) atTop
          (nhds (logarithmicCoeff L (k + 1))) := by
  rcases exists_scaledNormalizedDiskEmbedding hR1 hf with
    ⟨C, hC1, E₀, hE₀⟩
  rcases exists_normalizedPhaseCorrectedInverse_taylorCoeff_tendsto E₀ with
    ⟨E, hcoeff⟩
  have hC0 : (C : ℂ) ≠ 0 := by
    exact_mod_cast (zero_lt_one.trans hC1).ne'
  have hzeroR : (0 : ℂ) ∈ ball 0 R :=
    mem_ball_self (zero_lt_one.trans hR1)
  have hfAt : DifferentiableAt ℂ f 0 :=
    (hf.1 0 hzeroR).differentiableAt (isOpen_ball.mem_nhds hzeroR)
  have hEderiv : deriv E₀.toFun 0 = 1 / (C : ℂ) := by
    rw [hE₀]
    simpa only [hf.2.2.2, one_div] using
      (hfAt.hasDerivAt.div_const (C : ℂ)).deriv
  have hnormalized :
      (fun z ↦ E₀ z / deriv E₀.toFun 0) = f := by
    funext z
    rw [hEderiv, hE₀]
    field_simp [hC0]
  have hcoeff' : ∀ n : ℕ,
      Tendsto
        (fun j ↦ taylorCoeff (E j).normalizedPhaseCorrectedInverse n)
        atTop (nhds (taylorCoeff f n)) := by
    intro n
    simpa only [hnormalized] using hcoeff n
  let a : ℕ → ℕ → ℂ := fun j n ↦
    taylorCoeff (E j).normalizedPhaseCorrectedInverse n
  let A : ℕ → ℕ → ℂ → ℂ := fun N j ↦
    formalLogarithmicPolynomial (a j) N
  refine ⟨A, ?_⟩
  intro N k hk
  have htend := tendsto_logarithmicCoeff_formalLogarithmicPolynomial
    (a := taylorCoeff f) (A := a) (by simpa only [a] using hcoeff') hk
  rw [formalLogarithmicCoeff_eq_logarithmicCoeff
    (zero_lt_one.trans hR1) hf.1 hL hL0
    (taylorCoeff_one hf.2.2.2) hexp (k + 1)] at htend
  simpa only [A] using htend

end Submission
