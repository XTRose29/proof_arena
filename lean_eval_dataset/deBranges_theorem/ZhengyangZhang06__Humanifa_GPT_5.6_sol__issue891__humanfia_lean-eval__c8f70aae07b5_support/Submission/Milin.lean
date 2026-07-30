import Mathlib
import Submission.Robertson

open Metric

namespace Submission

lemma weighted_norm_sum_sq_le {ι : Type*} (s : Finset ι) (z : ι → ℂ) (w : ι → ℝ)
    (hw_pos : ∀ i ∈ s, 0 < w i) (hw_sum : ∑ i ∈ s, w i = 1) :
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ ∑ i ∈ s, ‖z i‖ ^ 2 / w i := by
  have hnorm : ‖∑ i ∈ s, z i‖ ≤ ∑ i ∈ s, ‖z i‖ := norm_sum_le _ _
  calc
    ‖∑ i ∈ s, z i‖ ^ 2 ≤ (∑ i ∈ s, ‖z i‖) ^ 2 := by gcongr
    _ = (∑ i ∈ s, ‖z i‖) ^ 2 / ∑ i ∈ s, w i := by rw [hw_sum]; simp
    _ ≤ ∑ i ∈ s, ‖z i‖ ^ 2 / w i := Finset.sq_sum_div_le_sum_sq_div s _ hw_pos

lemma taylorCoeff_div_two (L : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (fun z => L z / (2 : ℂ)) n = logarithmicCoeff L n := by
  rw [taylorCoeff, iteratedDeriv_div_const, logarithmicCoeff, taylorCoeff]
  ring

lemma deriv_halfExp_eq_mul_deriv_div_two {L : ℂ → ℂ} {R : ℝ}
    (hL : DifferentiableOn ℂ L (ball 0 R)) :
    Set.EqOn (deriv (halfExp L))
      ((halfExp L) * deriv (fun z => L z / (2 : ℂ))) (ball 0 R) := by
  intro z hz
  have hhalf : DifferentiableAt ℂ (fun w => L w / (2 : ℂ)) z :=
    (hL.differentiableAt (isOpen_ball.mem_nhds hz)).div_const (2 : ℂ)
  change deriv (fun w => Complex.exp (L w / (2 : ℂ))) z =
    Complex.exp (L z / (2 : ℂ)) * deriv (fun w => L w / (2 : ℂ)) z
  exact hhalf.hasDerivAt.cexp.deriv

lemma halfExp_coeff_recurrence {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (n : ℕ) :
    (n + 1 : ℕ) * taylorCoeff (halfExp L) (n + 1) =
      ∑ i ∈ Finset.range (n + 1),
        taylorCoeff (halfExp L) i *
          ((n - i + 1 : ℕ) * logarithmicCoeff L (n - i + 1)) := by
  have hhalfLog : DifferentiableOn ℂ (fun z => L z / (2 : ℂ)) (ball 0 R) :=
    hL.div_const (2 : ℂ)
  simpa only [taylorCoeff_div_two] using
    taylorCoeff_log_recurrence hR (differentiableOn_halfExp hL) hhalfLog
      (deriv_halfExp_eq_mul_deriv_div_two hL) n

lemma halfExp_coeff_cauchy_schwarz {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (n : ℕ) :
    ‖((n + 1 : ℕ) : ℂ) * taylorCoeff (halfExp L) (n + 1)‖ ^ 2 ≤
      (∑ i ∈ Finset.range (n + 1),
          ((n - i + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (n - i + 1)‖ ^ 2) *
        ∑ i ∈ Finset.range (n + 1),
          ((n - i + 1 : ℕ) : ℝ) * ‖taylorCoeff (halfExp L) i‖ ^ 2 := by
  rw [halfExp_coeff_recurrence hR hL n]
  have hnorm :
      ‖∑ i ∈ Finset.range (n + 1),
          taylorCoeff (halfExp L) i *
            ((n - i + 1 : ℕ) * logarithmicCoeff L (n - i + 1))‖ ≤
        ∑ i ∈ Finset.range (n + 1),
          ‖taylorCoeff (halfExp L) i‖ *
            (((n - i + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (n - i + 1)‖) := by
    calc
      _ ≤ ∑ i ∈ Finset.range (n + 1),
          ‖taylorCoeff (halfExp L) i *
            ((n - i + 1 : ℕ) * logarithmicCoeff L (n - i + 1))‖ :=
        norm_sum_le _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro i hi
        simp only [norm_mul, norm_natCast]
  calc
    ‖∑ i ∈ Finset.range (n + 1),
        taylorCoeff (halfExp L) i *
          ((n - i + 1 : ℕ) * logarithmicCoeff L (n - i + 1))‖ ^ 2 ≤
        (∑ i ∈ Finset.range (n + 1),
          ‖taylorCoeff (halfExp L) i‖ *
            (((n - i + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (n - i + 1)‖)) ^ 2 := by
      gcongr
    _ ≤ _ := by
      apply Finset.sum_sq_le_sum_mul_sum_of_sq_le_mul
      · intro i hi
        positivity
      · intro i hi
        positivity
      · intro i hi
        ring_nf
        exact le_rfl

noncomputable def logarithmicEnergy (L : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (k + 1 : ℕ) * ‖logarithmicCoeff L (k + 1)‖ ^ 2

noncomputable def priorCoeffEnergy (L : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, (N - i : ℕ) * ‖taylorCoeff (halfExp L) i‖ ^ 2

noncomputable def coeffSquareSum (L : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ i ∈ Finset.range N, ‖taylorCoeff (halfExp L) i‖ ^ 2

noncomputable def harmonicEnergy (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, 1 / ((k + 1 : ℕ) : ℝ)

noncomputable def milinFunctional (L : ℂ → ℂ) (N : ℕ) : ℝ :=
  ∑ m ∈ Finset.range N,
    (logarithmicEnergy L (m + 1) - harmonicEnergy (m + 1))

def SatisfiesMilin (L : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, milinFunctional L N ≤ 0

def SatisfiesLebedevMilin (L : ℂ → ℂ) : Prop :=
  ∀ N : ℕ, coeffSquareSum L (N + 1) ≤
    ((N + 1 : ℕ) : ℝ) * Real.exp (milinFunctional L N / ((N + 1 : ℕ) : ℝ))

noncomputable def weightedPrefix (a : ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑ k ∈ Finset.range N, (N - k : ℕ) * a k

lemma weightedPrefix_succ (a : ℕ → ℝ) (N : ℕ) :
    weightedPrefix a (N + 1) = weightedPrefix a N + ∑ k ∈ Finset.range (N + 1), a k := by
  rw [weightedPrefix, weightedPrefix, Finset.sum_range_succ]
  simp only [Nat.add_sub_cancel_left, Nat.cast_one, one_mul]
  have hterm (k : ℕ) (hk : k ∈ Finset.range N) :
      (((N + 1 - k : ℕ) : ℝ) * a k) = (((N - k : ℕ) : ℝ) * a k) + a k := by
    have hkn : k ≤ N := (Finset.mem_range.mp hk).le
    rw [show N + 1 - k = (N - k) + 1 by omega]
    push_cast
    ring
  calc
    (∑ k ∈ Finset.range N, ((N + 1 - k : ℕ) : ℝ) * a k) + a N =
        (∑ k ∈ Finset.range N, (((N - k : ℕ) : ℝ) * a k + a k)) + a N := by
      congr 1
      apply Finset.sum_congr rfl
      exact hterm
    _ = (∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) * a k) +
        ((∑ k ∈ Finset.range N, a k) + a N) := by
      rw [Finset.sum_add_distrib]
      ring
    _ = (∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) * a k) +
        ∑ k ∈ Finset.range (N + 1), a k := by
      rw [Finset.sum_range_succ]

lemma sum_prefix_eq_weightedPrefix (a : ℕ → ℝ) (N : ℕ) :
    (∑ m ∈ Finset.range N, ∑ k ∈ Finset.range (m + 1), a k) = weightedPrefix a N := by
  induction N with
  | zero => simp [weightedPrefix]
  | succ N ih =>
      rw [Finset.sum_range_succ, weightedPrefix_succ, ih]

lemma logarithmicEnergy_succ (L : ℂ → ℂ) (N : ℕ) :
    logarithmicEnergy L (N + 1) = logarithmicEnergy L N +
      ((N + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (N + 1)‖ ^ 2 := by
  simp [logarithmicEnergy, Finset.sum_range_succ]

lemma harmonicEnergy_succ (N : ℕ) :
    harmonicEnergy (N + 1) = harmonicEnergy N + 1 / ((N + 1 : ℕ) : ℝ) := by
  simp [harmonicEnergy, Finset.sum_range_succ]

lemma milinFunctional_succ (L : ℂ → ℂ) (N : ℕ) :
    milinFunctional L (N + 1) = milinFunctional L N +
      (logarithmicEnergy L (N + 1) - harmonicEnergy (N + 1)) := by
  simp [milinFunctional, Finset.sum_range_succ]
  ring

lemma milinFunctional_eq_weighted (L : ℂ → ℂ) (N : ℕ) :
    milinFunctional L N =
      ∑ k ∈ Finset.range N, ((N - k : ℕ) : ℝ) *
        (((k + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (k + 1)‖ ^ 2 -
          1 / ((k + 1 : ℕ) : ℝ)) := by
  let a : ℕ → ℝ := fun k =>
    ((k + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (k + 1)‖ ^ 2 -
      1 / ((k + 1 : ℕ) : ℝ)
  have hprefix (m : ℕ) :
      logarithmicEnergy L (m + 1) - harmonicEnergy (m + 1) =
        ∑ k ∈ Finset.range (m + 1), a k := by
    rw [logarithmicEnergy, harmonicEnergy, Finset.sum_sub_distrib]
  rw [milinFunctional]
  simp_rw [hprefix]
  simpa [weightedPrefix, a] using sum_prefix_eq_weightedPrefix a N

@[simp]
lemma taylorCoeff_halfExp_zero {L : ℂ → ℂ} (hL0 : L 0 = 0) :
    taylorCoeff (halfExp L) 0 = 1 := by
  simp [taylorCoeff, halfExp, hL0]

@[simp]
lemma coeffSquareSum_one {L : ℂ → ℂ} (hL0 : L 0 = 0) :
    coeffSquareSum L 1 = 1 := by
  simp [coeffSquareSum, hL0]

lemma halfExp_coeff_one {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0) :
    taylorCoeff (halfExp L) 1 = logarithmicCoeff L 1 := by
  simpa [hL0] using halfExp_coeff_recurrence hR hL 0

lemma coeffSquareSum_two {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0) :
    coeffSquareSum L 2 = 1 + ‖logarithmicCoeff L 1‖ ^ 2 := by
  simp [coeffSquareSum, Finset.sum_range_succ, hL0, halfExp_coeff_one hR hL hL0]

lemma milinFunctional_one (L : ℂ → ℂ) :
    milinFunctional L 1 = ‖logarithmicCoeff L 1‖ ^ 2 - 1 := by
  norm_num [milinFunctional, logarithmicEnergy, harmonicEnergy]

lemma one_add_le_two_mul_exp_sub_one_div_two (x : ℝ) :
    1 + x ≤ 2 * Real.exp ((x - 1) / 2) := by
  nlinarith [Real.add_one_le_exp ((x - 1) / 2)]

lemma lebedevMilin_zero {L : ℂ → ℂ} (hL0 : L 0 = 0) :
    coeffSquareSum L 1 ≤ (1 : ℝ) * Real.exp (milinFunctional L 0 / 1) := by
  simp [hL0, milinFunctional]

lemma lebedevMilin_one {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0) :
    coeffSquareSum L 2 ≤ (2 : ℝ) * Real.exp (milinFunctional L 1 / 2) := by
  rw [coeffSquareSum_two hR hL hL0, milinFunctional_one]
  exact one_add_le_two_mul_exp_sub_one_div_two _

lemma robertson_of_milin {L : ℂ → ℂ} (hmilin : SatisfiesMilin L)
    (hlebedevMilin : SatisfiesLebedevMilin L) (N : ℕ) :
    coeffSquareSum L (N + 1) ≤ N + 1 := by
  have hdenom : 0 ≤ (((N + 1 : ℕ) : ℝ)) := by positivity
  have hexponent : milinFunctional L N / ((N + 1 : ℕ) : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg (hmilin N) hdenom
  calc
    coeffSquareSum L (N + 1) ≤
        ((N + 1 : ℕ) : ℝ) *
          Real.exp (milinFunctional L N / ((N + 1 : ℕ) : ℝ)) := hlebedevMilin N
    _ ≤ ((N + 1 : ℕ) : ℝ) * 1 :=
      mul_le_mul_of_nonneg_left (Real.exp_le_one_iff.mpr hexponent) hdenom
    _ = N + 1 := by norm_num [Nat.cast_add, add_comm]

lemma normalized_coeff_bound_of_milin {f L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : NormalizedUnivalentOn f R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hmilin : SatisfiesMilin L) (hlebedevMilin : SatisfiesLebedevMilin L)
    (n : ℕ) : ‖taylorCoeff f n‖ ≤ n := by
  apply normalized_coeff_bound_of_robertson hR hf hL hexp
  intro N
  simpa [coeffSquareSum] using robertson_of_milin hmilin hlebedevMilin N

lemma coeffSquareSum_succ (L : ℂ → ℂ) (N : ℕ) :
    coeffSquareSum L (N + 1) =
      coeffSquareSum L N + ‖taylorCoeff (halfExp L) N‖ ^ 2 := by
  simp [coeffSquareSum, Finset.sum_range_succ]

lemma priorCoeffEnergy_succ (L : ℂ → ℂ) (N : ℕ) :
    priorCoeffEnergy L (N + 1) =
      priorCoeffEnergy L N + coeffSquareSum L (N + 1) := by
  simpa [priorCoeffEnergy, weightedPrefix, coeffSquareSum] using
    weightedPrefix_succ (fun i => ‖taylorCoeff (halfExp L) i‖ ^ 2) N

lemma priorCoeffEnergy_eq_sum_coeffSquareSum (L : ℂ → ℂ) (N : ℕ) :
    priorCoeffEnergy L N = ∑ m ∈ Finset.range N, coeffSquareSum L (m + 1) := by
  simpa [priorCoeffEnergy, weightedPrefix, coeffSquareSum] using
    (sum_prefix_eq_weightedPrefix (fun i => ‖taylorCoeff (halfExp L) i‖ ^ 2) N).symm

lemma reflected_logarithmicEnergy (L : ℂ → ℂ) (n : ℕ) :
    (∑ i ∈ Finset.range (n + 1),
        ((n - i + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (n - i + 1)‖ ^ 2) =
      logarithmicEnergy L (n + 1) := by
  simpa [logarithmicEnergy, Nat.add_comm] using
    (Finset.sum_range_reflect
      (fun k => ((k + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (k + 1)‖ ^ 2) (n + 1))

lemma halfExp_coeff_energy_bound {L : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (n : ℕ) :
    ((n + 1 : ℕ) : ℝ) ^ 2 * ‖taylorCoeff (halfExp L) (n + 1)‖ ^ 2 ≤
      logarithmicEnergy L (n + 1) * priorCoeffEnergy L (n + 1) := by
  have hprior :
      (∑ i ∈ Finset.range (n + 1),
          ((n - i + 1 : ℕ) : ℝ) * ‖taylorCoeff (halfExp L) i‖ ^ 2) =
        priorCoeffEnergy L (n + 1) := by
    rw [priorCoeffEnergy]
    apply Finset.sum_congr rfl
    intro i hi
    have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
    congr 2
    omega
  have h := halfExp_coeff_cauchy_schwarz hR hL n
  rw [reflected_logarithmicEnergy, hprior, norm_mul, Complex.norm_natCast, mul_pow] at h
  exact h

end Submission
