import Submission.DiscreteLoewner

open Function

namespace Submission

noncomputable def taylorPolynomialFunction
    (f : ℂ → ℂ) (N : ℕ) (z : ℂ) : ℂ :=
  ∑ k ∈ Finset.range (N + 1), taylorCoeff f k * z ^ k

lemma taylorCoeff_taylorPolynomialFunction
    (f : ℂ → ℂ) {N k : ℕ} (hk : k ≤ N) :
    taylorCoeff (taylorPolynomialFunction f N) k = taylorCoeff f k := by
  unfold taylorPolynomialFunction
  rw [taylorCoeff_finset_sum_formal]
  · rw [Finset.sum_eq_single k]
    · rw [taylorCoeff_const_mul_formal, taylorCoeff_power_monomial,
        if_pos rfl, mul_one]
    · intro j hj hjk
      rw [taylorCoeff_const_mul_formal, taylorCoeff_power_monomial,
        if_neg (Ne.symm hjk), mul_zero]
    · exact fun hnot ↦ (hnot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hk))).elim
  · intro j hj
    fun_prop

lemma taylorCoeff_pow_eq_seriesPowCoeff
    {q : ℂ → ℂ} (hq : AnalyticAt ℂ q 0) :
    ∀ k n : ℕ,
      taylorCoeff (fun z ↦ q z ^ k) n =
        seriesPowCoeff (taylorCoeff q) k n := by
  intro k
  induction k with
  | zero =>
      intro n
      simpa [seriesPowCoeff] using taylorCoeff_power_monomial 0 n
  | succ k ih =>
      intro n
      rw [seriesPowCoeff, seriesMulCoeff]
      rw [show (fun z ↦ q z ^ (k + 1)) = q * fun z ↦ q z ^ k by
        funext z
        simpa [Pi.mul_apply, mul_comm] using pow_succ (q z) k]
      rw [taylorCoeff_mul (f := q) (g := fun z ↦ q z ^ k)
        hq.contDiffAt (hq.pow k).contDiffAt]
      apply Finset.sum_congr rfl
      intro j hj
      rw [ih]

lemma taylorCoeff_taylorPolynomialFunction_comp
    {f q : ℂ → ℂ} (hq : AnalyticAt ℂ q 0) (n : ℕ) :
    taylorCoeff (taylorPolynomialFunction f n ∘ q) n =
      ∑ k ∈ Finset.range (n + 1),
        taylorCoeff f k * seriesPowCoeff (taylorCoeff q) k n := by
  unfold taylorPolynomialFunction
  change taylorCoeff
    (fun z ↦ ∑ k ∈ Finset.range (n + 1), taylorCoeff f k * q z ^ k) n = _
  rw [taylorCoeff_finset_sum_formal]
  · apply Finset.sum_congr rfl
    intro k hk
    rw [taylorCoeff_const_mul_formal, taylorCoeff_pow_eq_seriesPowCoeff hq]
  · intro k hk
    exact contDiffAt_const.mul (hq.pow k).contDiffAt

lemma formalComposition_coeff_eq_of_outer_coeff_eq_up_to
    {a b q : ℕ → ℂ} {n : ℕ}
    (hab : ∀ k ≤ n, a k = b k) :
    ((FormalMultilinearSeries.ofScalars ℂ a).comp
        (FormalMultilinearSeries.ofScalars ℂ q)).coeff n =
      ((FormalMultilinearSeries.ofScalars ℂ b).comp
        (FormalMultilinearSeries.ofScalars ℂ q)).coeff n := by
  simp only [FormalMultilinearSeries.coeff,
    FormalMultilinearSeries.comp, ContinuousMultilinearMap.sum_apply]
  apply Finset.sum_congr rfl
  intro c hc
  rw [FormalMultilinearSeries.compAlongComposition_apply]
  have hout :
      FormalMultilinearSeries.ofScalars ℂ a c.length =
        FormalMultilinearSeries.ofScalars ℂ b c.length := by
    unfold FormalMultilinearSeries.ofScalars
    rw [hab c.length c.length_le]
  rw [hout]
  rfl

lemma taylorCoeff_comp_eq_sum_seriesPowCoeff
    {f q : ℂ → ℂ} (hf : AnalyticAt ℂ f 0)
    (hq : AnalyticAt ℂ q 0) (hq0 : q 0 = 0) (n : ℕ) :
    taylorCoeff (f ∘ q) n =
      ∑ k ∈ Finset.range (n + 1),
        taylorCoeff f k * seriesPowCoeff (taylorCoeff q) k n := by
  let P : ℂ → ℂ := taylorPolynomialFunction f n
  have hP : AnalyticAt ℂ P 0 := by
    change AnalyticAt ℂ
      (fun z ↦ ∑ k ∈ Finset.range (n + 1), taylorCoeff f k * z ^ k) 0
    fun_prop
  have hf' : AnalyticAt ℂ f (q 0) := by simpa only [hq0] using hf
  have hP' : AnalyticAt ℂ P (q 0) := by simpa only [hq0] using hP
  have hfcomp := hf'.hasFPowerSeriesAt.comp hq.hasFPowerSeriesAt
  have hPcomp := hP'.hasFPowerSeriesAt.comp hq.hasFPowerSeriesAt
  simp only [hq0] at hfcomp hPcomp
  have hformal := formalComposition_coeff_eq_of_outer_coeff_eq_up_to
    (q := taylorCoeff q) (n := n)
    (fun k hk ↦ (taylorCoeff_taylorPolynomialFunction f hk).symm)
  have hcoeff_f := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n)
    (hfcomp.eq_formalMultilinearSeries
      ((hf'.comp hq).hasFPowerSeriesAt))
  have hcoeff_P := congrArg
    (fun p : FormalMultilinearSeries ℂ ℂ ℂ ↦ p.coeff n)
    (hPcomp.eq_formalMultilinearSeries
      ((hP'.comp hq).hasFPowerSeriesAt))
  have heq : taylorCoeff (f ∘ q) n = taylorCoeff (P ∘ q) n := by
    simpa only [FormalMultilinearSeries.coeff_ofScalars, taylorCoeff] using
      hcoeff_f.symm.trans (hformal.trans hcoeff_P)
  rw [heq]
  exact taylorCoeff_taylorPolynomialFunction_comp hq n

end Submission
