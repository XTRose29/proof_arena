import Submission.Weinstein
import Submission.DeBrangesGasper
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

open MeasureTheory Metric Set

namespace Submission

/-- The finite Weinstein inequality associated with the de Branges weights.
It is the exact static inequality which replaces a Loewner representation. -/
def SatisfiesWeinsteinInequalities (L : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, ∀ t : ℝ, 0 ≤ t →
    (∑ k ∈ Finset.range N,
      explicitDeBrangesQ N (k + 1) t *
        ((((k + 1 : ℕ) : ℝ) ^ 2 * ‖logarithmicCoeff L (k + 1)‖ ^ 2) - 1)) ≤ 0

lemma integrableOn_explicitDeBrangesQ_Ioi (N : ℕ) {k : ℕ} (hk : 0 < k) :
    IntegrableOn (explicitDeBrangesQ N k) (Ioi (0 : ℝ)) := by
  unfold explicitDeBrangesQ
  apply MeasureTheory.integrable_finsetSum
  intro j hj
  by_cases hcoeff : deBrangesQCoefficient N k j = 0
  · simp [hcoeff]
  · have hkj : k ≤ j := by
      by_contra hnot
      have : deBrangesQCoefficient N k j = 0 := by
        simp [deBrangesQCoefficient, show ¬k ≤ j by omega]
      exact hcoeff this
    have hj0 : 0 < (j : ℝ) := by
      exact_mod_cast lt_of_lt_of_le hk hkj
    have hexp : IntegrableOn
        (fun t : ℝ => Real.exp ((-(j : ℝ)) * t)) (Ioi (0 : ℝ)) :=
      integrableOn_exp_mul_Ioi (by linarith) 0
    have hrewrite :
        (fun t : ℝ =>
          deBrangesQCoefficient N k j * Real.exp (-((j : ℝ) * t))) =
        (fun t : ℝ =>
          deBrangesQCoefficient N k j * Real.exp ((-(j : ℝ)) * t)) := by
      funext t
      congr 2
      ring
    rw [hrewrite]
    exact hexp.const_mul _

lemma integral_explicitDeBrangesQ_Ioi (N : ℕ) {k : ℕ} (hk : 0 < k) :
    (∫ t : ℝ in Ioi 0, explicitDeBrangesQ N k t) =
      explicitDeBrangesTau N k 0 / (k : ℝ) := by
  unfold explicitDeBrangesQ explicitDeBrangesTau
  rw [MeasureTheory.integral_finsetSum]
  · rw [Finset.sum_div]
    simp only [mul_zero, neg_zero, Real.exp_zero, mul_one]
    apply Finset.sum_congr rfl
    intro j hj
    by_cases hkj : k ≤ j
    · have hj0 : 0 < (j : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hk hkj
      rw [MeasureTheory.integral_const_mul]
      have hexp :
          (∫ t : ℝ in Ioi 0, Real.exp (-((j : ℝ) * t))) = 1 / (j : ℝ) := by
        simpa [neg_mul, ne_of_gt hj0] using
          (integral_exp_mul_Ioi (a := -(j : ℝ)) (by linarith) 0)
      rw [hexp]
      have hk0 : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
      have hjne : (j : ℝ) ≠ 0 := ne_of_gt hj0
      rw [deBrangesQCoefficient_eq hk]
      field_simp [hk0, hjne]
    · have hQ : deBrangesQCoefficient N k j = 0 := by
        simp [deBrangesQCoefficient, hkj]
      have hTau : deBrangesCoefficient N k j = 0 := by
        simp [deBrangesCoefficient, hkj]
      simp [hQ, hTau]
  · intro j hj
    by_cases hcoeff : deBrangesQCoefficient N k j = 0
    · simp [hcoeff]
    · have hkj : k ≤ j := by
        by_contra hnot
        have : deBrangesQCoefficient N k j = 0 := by
          simp [deBrangesQCoefficient, show ¬k ≤ j by omega]
        exact hcoeff this
      have hj0 : 0 < (j : ℝ) := by
        exact_mod_cast lt_of_lt_of_le hk hkj
      have hexp : IntegrableOn
          (fun t : ℝ => Real.exp ((-(j : ℝ)) * t)) (Ioi (0 : ℝ)) :=
        integrableOn_exp_mul_Ioi (by linarith) 0
      have hrewrite :
          (fun t : ℝ =>
            deBrangesQCoefficient N k j * Real.exp (-((j : ℝ) * t))) =
          (fun t : ℝ =>
            deBrangesQCoefficient N k j *
              Real.exp ((-(j : ℝ)) * t)) := by
        funext t
        congr 2
        ring
      rw [hrewrite]
      exact hexp.const_mul _

lemma satisfiesMilin_of_weinsteinInequalities {L : ℂ → ℂ}
    (hweinstein : SatisfiesWeinsteinInequalities L) : SatisfiesMilin L := by
  intro N
  let defect : ℕ → ℝ := fun k =>
    (((k : ℕ) : ℝ) ^ 2 * ‖logarithmicCoeff L k‖ ^ 2) - 1
  let integrand : ℝ → ℝ := fun t =>
    ∑ k ∈ Finset.range N,
      explicitDeBrangesQ N (k + 1) t * defect (k + 1)
  have hintegrable : IntegrableOn integrand (Ioi (0 : ℝ)) := by
    dsimp only [integrand]
    apply MeasureTheory.integrable_finsetSum
    intro k hk
    exact (integrableOn_explicitDeBrangesQ_Ioi N (Nat.succ_pos k)).mul_const _
  have hnonpos : ∀ᵐ t ∂volume.restrict (Ioi (0 : ℝ)), integrand t ≤ 0 := by
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact hweinstein N t ht.le
  have hintNonpos : (∫ t : ℝ in Ioi 0, integrand t) ≤ 0 :=
    integral_nonpos_of_ae hnonpos
  have hint :
      (∫ t : ℝ in Ioi 0, integrand t) = milinFunctional L N := by
    rw [milinFunctional_eq_weighted]
    dsimp only [integrand]
    rw [MeasureTheory.integral_finsetSum]
    · apply Finset.sum_congr rfl
      intro k hk
      rw [MeasureTheory.integral_mul_const,
        integral_explicitDeBrangesQ_Ioi N (Nat.succ_pos k),
        explicitDeBrangesTau_zero (Nat.succ_pos k) (Finset.mem_range.mp hk)]
      dsimp only [defect]
      have hk0 : (0 : ℝ) < (k + 1 : ℕ) := by positivity
      have hkN : k < N := Finset.mem_range.mp hk
      have hsub : N - k = 1 + (N - (k + 1)) := by
        omega
      rw [hsub]
      push_cast
      field_simp [ne_of_gt hk0]
      ring
    · intro k hk
      exact (integrableOn_explicitDeBrangesQ_Ioi N (Nat.succ_pos k)).mul_const _
  rwa [hint] at hintNonpos

end Submission
