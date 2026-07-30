import Mathlib
import Submission.DeBrangesWeights

open Filter

namespace Submission

noncomputable def deBrangesPartialSum (c : ℕ → ℂ) (k : ℕ) : ℂ :=
  1 + 2 * ∑ j ∈ Finset.range k, ((j + 1 : ℕ) : ℂ) * c (j + 1)

noncomputable def deBrangesEnergy (N : ℕ) (tau : ℕ → ℝ) (c : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range N,
    ((k + 1 : ℕ) : ℝ) * tau (k + 1) * ‖c (k + 1)‖ ^ 2

noncomputable def deBrangesEnergyRate (N : ℕ) (tau tauDot : ℕ → ℝ)
    (c cDot : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range N,
    ((k + 1 : ℕ) : ℝ) *
      (tauDot (k + 1) * ‖c (k + 1)‖ ^ 2 +
        2 * tau (k + 1) * (cDot (k + 1) * starRingEnd ℂ (c (k + 1))).re)

def SatisfiesLoewnerLogarithmicODE (N : ℕ) (c cDot : ℕ → ℂ) : Prop :=
  ∀ k ∈ Finset.range N,
    cDot (k + 1) =
      (deBrangesPartialSum c k + deBrangesPartialSum c (k + 1)) / 2

def SatisfiesDeBrangesSystem (N : ℕ) (tau tauDot : ℕ → ℝ) : Prop :=
  tau (N + 1) = 0 ∧ tauDot (N + 1) = 0 ∧
    ∀ k ∈ Finset.range N,
      tau (k + 1) - tau (k + 2) =
        -tauDot (k + 1) / ((k + 1 : ℕ) : ℝ) -
          tauDot (k + 2) / ((k + 2 : ℕ) : ℝ)

lemma explicitDeBranges_satisfies_system (N : ℕ) (t : ℝ) :
    SatisfiesDeBrangesSystem N
      (fun k => explicitDeBrangesTau N k t)
      (fun k => explicitDeBrangesTauDot N k t) := by
  refine ⟨explicitDeBrangesTau_terminal N t,
    explicitDeBrangesTauDot_terminal N t, ?_⟩
  intro k hk
  have hkN : k + 1 ≤ N := Finset.mem_range.mp hk
  simpa only [Nat.add_assoc] using
    explicitDeBranges_system_eq (N := N) (k := k + 1) (by omega) hkN t

lemma deBrangesPartialSum_zero (c : ℕ → ℂ) : deBrangesPartialSum c 0 = 1 := by
  simp [deBrangesPartialSum]

lemma deBrangesPartialSum_succ (c : ℕ → ℂ) (k : ℕ) :
    deBrangesPartialSum c (k + 1) - deBrangesPartialSum c k =
      2 * ((k + 1 : ℕ) : ℂ) * c (k + 1) := by
  simp [deBrangesPartialSum, Finset.sum_range_succ]
  ring

lemma c_eq_partialSum_sub (c : ℕ → ℂ) (k : ℕ) :
    c (k + 1) =
      (deBrangesPartialSum c (k + 1) - deBrangesPartialSum c k) /
        (2 * ((k + 1 : ℕ) : ℂ)) := by
  rw [deBrangesPartialSum_succ]
  field_simp

lemma re_mul_conj_sub_add (x y : ℂ) :
    ((x + y) * starRingEnd ℂ (x - y)).re = ‖x‖ ^ 2 - ‖y‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.mul_re, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im, map_sub, Complex.conj_re, Complex.conj_im, Complex.normSq_apply]
  ring

lemma loewner_energy_term_eq {c cDot : ℕ → ℂ} {k : ℕ}
    (hode : cDot (k + 1) =
      (deBrangesPartialSum c k + deBrangesPartialSum c (k + 1)) / 2) :
    2 * ((k + 1 : ℕ) : ℝ) *
        (cDot (k + 1) * starRingEnd ℂ (c (k + 1))).re =
      (‖deBrangesPartialSum c (k + 1)‖ ^ 2 -
        ‖deBrangesPartialSum c k‖ ^ 2) / 2 := by
  rw [hode, c_eq_partialSum_sub c k]
  let x := deBrangesPartialSum c (k + 1)
  let y := deBrangesPartialSum c k
  have hk : (((k + 1 : ℕ) : ℂ)) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero k
  have hcancel :
      (2 * (((k + 1 : ℕ) : ℂ))) *
          (((y + x) / 2) * starRingEnd ℂ ((x - y) /
            (2 * (((k + 1 : ℕ) : ℂ))))) =
        ((x + y) * starRingEnd ℂ (x - y)) / 2 := by
    rw [map_div₀, map_sub]
    simp only [map_mul, map_ofNat, map_natCast]
    field_simp [hk]
    ring
  calc
    2 * ((k + 1 : ℕ) : ℝ) *
        (((y + x) / 2) * starRingEnd ℂ ((x - y) /
          (2 * (((k + 1 : ℕ) : ℂ))))).re =
        ((2 * (((k + 1 : ℕ) : ℂ))) *
          (((y + x) / 2) * starRingEnd ℂ ((x - y) /
            (2 * (((k + 1 : ℕ) : ℂ)))))).re := by
      simp [Complex.mul_re]
    _ = (((x + y) * starRingEnd ℂ (x - y)) / 2).re :=
      congrArg Complex.re hcancel
    _ = (‖x‖ ^ 2 - ‖y‖ ^ 2) / 2 := by
      rw [Complex.div_re, re_mul_conj_sub_add]
      norm_num
      ring

lemma norm_add_sq_add_norm_sub_sq (x y : ℂ) :
    ‖x + y‖ ^ 2 + ‖x - y‖ ^ 2 = 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq,
    ← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.sub_re,
    Complex.sub_im]
  ring

lemma sum_mul_sub_telescope (tau a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, tau (k + 1) * (a (k + 1) - a k)) =
      (∑ k ∈ Finset.range N,
        (tau (k + 1) - tau (k + 2)) * a (k + 1)) -
        tau 1 * a 0 + tau (N + 1) * a N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      ring

lemma sum_mul_sub_telescope_of_terminal_zero {tau a : ℕ → ℝ} {N : ℕ}
    (hterminal : tau (N + 1) = 0) :
    (∑ k ∈ Finset.range N, tau (k + 1) * (a (k + 1) - a k)) =
      (∑ k ∈ Finset.range N,
        (tau (k + 1) - tau (k + 2)) * a (k + 1)) - tau 1 * a 0 := by
  rw [sum_mul_sub_telescope, hterminal]
  ring

lemma weighted_coeff_norm_eq_partialSum {c : ℕ → ℂ} (k : ℕ) :
    ((k + 1 : ℕ) : ℝ) * ‖c (k + 1)‖ ^ 2 =
      ‖deBrangesPartialSum c (k + 1) - deBrangesPartialSum c k‖ ^ 2 /
        (4 * ((k + 1 : ℕ) : ℝ)) := by
  rw [deBrangesPartialSum_succ, norm_mul, norm_mul, Complex.norm_natCast]
  have hk : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
  norm_num
  field_simp [hk]
  ring

noncomputable def deBrangesEdgeRate (N : ℕ) (tau tauDot : ℕ → ℝ)
    (c : ℕ → ℂ) : ℝ :=
  (∑ k ∈ Finset.range N,
      tauDot (k + 1) /
          (4 * ((k + 1 : ℕ) : ℝ)) *
        ‖deBrangesPartialSum c (k + 1) - deBrangesPartialSum c k‖ ^ 2) +
    ((∑ k ∈ Finset.range N,
        (tau (k + 1) - tau (k + 2)) *
          ‖deBrangesPartialSum c (k + 1)‖ ^ 2) - tau 1) / 2

lemma deBrangesEnergyRate_eq_edgeRate {N : ℕ} {tau tauDot : ℕ → ℝ}
    {c cDot : ℕ → ℂ} (hterminal : tau (N + 1) = 0)
    (hode : SatisfiesLoewnerLogarithmicODE N c cDot) :
    deBrangesEnergyRate N tau tauDot c cDot =
      deBrangesEdgeRate N tau tauDot c := by
  rw [deBrangesEnergyRate, deBrangesEdgeRate]
  have hterm (k : ℕ) (hk : k ∈ Finset.range N) :
      ((k + 1 : ℕ) : ℝ) *
          (tauDot (k + 1) * ‖c (k + 1)‖ ^ 2 +
            2 * tau (k + 1) *
              (cDot (k + 1) * starRingEnd ℂ (c (k + 1))).re) =
        tauDot (k + 1) /
            (4 * ((k + 1 : ℕ) : ℝ)) *
          ‖deBrangesPartialSum c (k + 1) - deBrangesPartialSum c k‖ ^ 2 +
        tau (k + 1) *
          (‖deBrangesPartialSum c (k + 1)‖ ^ 2 -
            ‖deBrangesPartialSum c k‖ ^ 2) / 2 := by
    have hcoeff := weighted_coeff_norm_eq_partialSum (c := c) k
    have hloewner := loewner_energy_term_eq (hode k hk)
    calc
      ((k + 1 : ℕ) : ℝ) *
          (tauDot (k + 1) * ‖c (k + 1)‖ ^ 2 +
            2 * tau (k + 1) *
              (cDot (k + 1) * starRingEnd ℂ (c (k + 1))).re) =
          tauDot (k + 1) *
              (((k + 1 : ℕ) : ℝ) * ‖c (k + 1)‖ ^ 2) +
            tau (k + 1) *
              (2 * ((k + 1 : ℕ) : ℝ) *
                (cDot (k + 1) * starRingEnd ℂ (c (k + 1))).re) := by ring
      _ = tauDot (k + 1) *
              (‖deBrangesPartialSum c (k + 1) - deBrangesPartialSum c k‖ ^ 2 /
                (4 * ((k + 1 : ℕ) : ℝ))) +
            tau (k + 1) *
              ((‖deBrangesPartialSum c (k + 1)‖ ^ 2 -
                ‖deBrangesPartialSum c k‖ ^ 2) / 2) := by rw [hcoeff, hloewner]
      _ = _ := by ring
  calc
    (∑ k ∈ Finset.range N,
        ((k + 1 : ℕ) : ℝ) *
          (tauDot (k + 1) * ‖c (k + 1)‖ ^ 2 +
            2 * tau (k + 1) *
              (cDot (k + 1) * starRingEnd ℂ (c (k + 1))).re)) =
        ∑ k ∈ Finset.range N,
          (tauDot (k + 1) /
              (4 * ((k + 1 : ℕ) : ℝ)) *
            ‖deBrangesPartialSum c (k + 1) - deBrangesPartialSum c k‖ ^ 2 +
          tau (k + 1) *
            (‖deBrangesPartialSum c (k + 1)‖ ^ 2 -
              ‖deBrangesPartialSum c k‖ ^ 2) / 2) := by
      apply Finset.sum_congr rfl
      exact hterm
    _ = (∑ k ∈ Finset.range N,
          tauDot (k + 1) /
              (4 * ((k + 1 : ℕ) : ℝ)) *
            ‖deBrangesPartialSum c (k + 1) - deBrangesPartialSum c k‖ ^ 2) +
        (∑ k ∈ Finset.range N,
          tau (k + 1) *
            (‖deBrangesPartialSum c (k + 1)‖ ^ 2 -
              ‖deBrangesPartialSum c k‖ ^ 2)) / 2 := by
      rw [Finset.sum_add_distrib, Finset.sum_div]
    _ = _ := by
      have htelescope := sum_mul_sub_telescope_of_terminal_zero
        (tau := tau)
        (a := fun k => ‖deBrangesPartialSum c k‖ ^ 2) hterminal
      rw [htelescope]
      simp [deBrangesPartialSum_zero]

lemma deBranges_square_factorization_aux (a : ℕ → ℝ) (s : ℕ → ℂ) (N : ℕ) :
    (∑ k ∈ Finset.range N,
      (-a (k + 1) * ‖s (k + 1) - s k‖ ^ 2 +
        2 * (a (k + 1) + a (k + 2)) * ‖s (k + 1)‖ ^ 2)) =
      (∑ k ∈ Finset.range N, a (k + 1) * ‖s (k + 1) + s k‖ ^ 2) -
        2 * a 1 * ‖s 0‖ ^ 2 + 2 * a (N + 1) * ‖s N‖ ^ 2 := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      have hparallelogram := norm_add_sq_add_norm_sub_sq (s (N + 1)) (s N)
      have hmul := congrArg (fun r : ℝ => a (N + 1) * r) hparallelogram
      nlinarith [hmul]

lemma deBranges_square_factorization {a : ℕ → ℝ} {s : ℕ → ℂ} {N : ℕ}
    (hterminal : a (N + 1) = 0) :
    (∑ k ∈ Finset.range N,
      (-a (k + 1) * ‖s (k + 1) - s k‖ ^ 2 +
        2 * (a (k + 1) + a (k + 2)) * ‖s (k + 1)‖ ^ 2)) =
      (∑ k ∈ Finset.range N, a (k + 1) * ‖s (k + 1) + s k‖ ^ 2) -
        2 * a 1 * ‖s 0‖ ^ 2 := by
  rw [deBranges_square_factorization_aux, hterminal]
  ring

noncomputable def deBrangesSquareRate (N : ℕ) (tauDot : ℕ → ℝ)
    (c : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.range N,
    (-tauDot (k + 1) / (4 * ((k + 1 : ℕ) : ℝ))) *
      ‖deBrangesPartialSum c (k + 1) + deBrangesPartialSum c k‖ ^ 2

lemma sum_add_sub_div_two (u v : ℕ → ℝ) (N : ℕ) (t : ℝ) :
    (∑ k ∈ Finset.range N, u k) +
        ((∑ k ∈ Finset.range N, v k) - t) / 2 =
      (∑ k ∈ Finset.range N, (u k + v k / 2)) - t / 2 := by
  rw [sub_div, Finset.sum_div]
  calc
    (∑ k ∈ Finset.range N, u k) +
        ((∑ k ∈ Finset.range N, v k / 2) - t / 2) =
      ((∑ k ∈ Finset.range N, u k) +
        ∑ k ∈ Finset.range N, v k / 2) - t / 2 := by ring
    _ = _ := by rw [← Finset.sum_add_distrib]

lemma deBrangesEdgeRate_eq_squareRate {N : ℕ} {tau tauDot : ℕ → ℝ}
    {c : ℕ → ℂ} (hsystem : SatisfiesDeBrangesSystem N tau tauDot) :
    deBrangesEdgeRate N tau tauDot c =
      (tauDot 1 - tau 1) / 2 + deBrangesSquareRate N tauDot c := by
  let a : ℕ → ℝ := fun k => -tauDot k / (4 * (k : ℝ))
  rcases hsystem with ⟨htau, htauDot, hsystem⟩
  have haterminal : a (N + 1) = 0 := by simp [a, htauDot]
  have hdelta (k : ℕ) (hk : k ∈ Finset.range N) :
      (tau (k + 1) - tau (k + 2)) / 2 =
        2 * (a (k + 1) + a (k + 2)) := by
    rw [hsystem k hk]
    simp only [a]
    have hk1 : (((k + 1 : ℕ) : ℝ)) ≠ 0 := by positivity
    have hk2 : (((k + 2 : ℕ) : ℝ)) ≠ 0 := by positivity
    field_simp [hk1, hk2]
    ring
  let s : ℕ → ℂ := deBrangesPartialSum c
  have hfactor := deBranges_square_factorization (a := a) (s := s) haterminal
  calc
    deBrangesEdgeRate N tau tauDot c =
        (∑ k ∈ Finset.range N,
          (tauDot (k + 1) /
                (4 * ((k + 1 : ℕ) : ℝ)) *
              ‖s (k + 1) - s k‖ ^ 2 +
            ((tau (k + 1) - tau (k + 2)) * ‖s (k + 1)‖ ^ 2) / 2)) -
          tau 1 / 2 := by
      simpa only [deBrangesEdgeRate, s] using
        sum_add_sub_div_two
          (fun k => tauDot (k + 1) /
              (4 * ((k + 1 : ℕ) : ℝ)) * ‖s (k + 1) - s k‖ ^ 2)
          (fun k => (tau (k + 1) - tau (k + 2)) * ‖s (k + 1)‖ ^ 2) N (tau 1)
    _ = (∑ k ∈ Finset.range N,
          (-a (k + 1) * ‖s (k + 1) - s k‖ ^ 2 +
            2 * (a (k + 1) + a (k + 2)) * ‖s (k + 1)‖ ^ 2)) -
          tau 1 / 2 := by
      have hsum :
          (∑ k ∈ Finset.range N,
            (tauDot (k + 1) /
                  (4 * ((k + 1 : ℕ) : ℝ)) * ‖s (k + 1) - s k‖ ^ 2 +
              ((tau (k + 1) - tau (k + 2)) * ‖s (k + 1)‖ ^ 2) / 2)) =
            ∑ k ∈ Finset.range N,
              (-a (k + 1) * ‖s (k + 1) - s k‖ ^ 2 +
                2 * (a (k + 1) + a (k + 2)) * ‖s (k + 1)‖ ^ 2) := by
        apply Finset.sum_congr rfl
        intro k hk
        rw [show ((tau (k + 1) - tau (k + 2)) * ‖s (k + 1)‖ ^ 2) / 2 =
          ((tau (k + 1) - tau (k + 2)) / 2) * ‖s (k + 1)‖ ^ 2 by ring]
        rw [hdelta k hk]
        simp only [a]
        ring
      rw [hsum]
    _ = ((∑ k ∈ Finset.range N,
          a (k + 1) * ‖s (k + 1) + s k‖ ^ 2) -
            2 * a 1 * ‖s 0‖ ^ 2) - tau 1 / 2 := by rw [hfactor]
    _ = (tauDot 1 - tau 1) / 2 + deBrangesSquareRate N tauDot c := by
      simp [a, s, deBrangesSquareRate, deBrangesPartialSum_zero]
      ring

lemma deBrangesEnergyRate_eq_squareRate {N : ℕ} {tau tauDot : ℕ → ℝ}
    {c cDot : ℕ → ℂ} (hsystem : SatisfiesDeBrangesSystem N tau tauDot)
    (hode : SatisfiesLoewnerLogarithmicODE N c cDot) :
    deBrangesEnergyRate N tau tauDot c cDot =
      (tauDot 1 - tau 1) / 2 + deBrangesSquareRate N tauDot c := by
  rw [deBrangesEnergyRate_eq_edgeRate hsystem.1 hode]
  exact deBrangesEdgeRate_eq_squareRate hsystem

lemma deBrangesEnergyRate_lower_bound {N : ℕ} {tau tauDot : ℕ → ℝ}
    {c cDot : ℕ → ℂ} (hsystem : SatisfiesDeBrangesSystem N tau tauDot)
    (hode : SatisfiesLoewnerLogarithmicODE N c cDot)
    (htauDot : ∀ k ∈ Finset.range N, tauDot (k + 1) ≤ 0) :
    (tauDot 1 - tau 1) / 2 ≤ deBrangesEnergyRate N tau tauDot c cDot := by
  rw [deBrangesEnergyRate_eq_squareRate hsystem hode]
  suffices 0 ≤ deBrangesSquareRate N tauDot c by linarith
  rw [deBrangesSquareRate]
  apply Finset.sum_nonneg
  intro k hk
  exact mul_nonneg (div_nonneg (neg_nonneg.mpr (htauDot k hk)) (by positivity)) (sq_nonneg _)

noncomputable def rotateLoewnerCoeff (c : ℕ → ℂ) (omega : ℂ) (n : ℕ) : ℂ :=
  c n / omega ^ n

noncomputable def deBrangesDrivenPartialSum (c : ℕ → ℂ) (omega : ℂ) (k : ℕ) : ℂ :=
  omega ^ k * deBrangesPartialSum (fun n => rotateLoewnerCoeff c omega n) k

def SatisfiesDrivenLoewnerLogarithmicODE (N : ℕ) (c cDot : ℕ → ℂ)
    (omega : ℂ) : Prop :=
  ∀ k ∈ Finset.range N,
    cDot (k + 1) =
      (omega * deBrangesDrivenPartialSum c omega k +
        deBrangesDrivenPartialSum c omega (k + 1)) / 2

lemma drivenLoewnerODE_rotate {N : ℕ} {c cDot : ℕ → ℂ} {omega : ℂ}
    (homega : omega ≠ 0)
    (hode : SatisfiesDrivenLoewnerLogarithmicODE N c cDot omega) :
    SatisfiesLoewnerLogarithmicODE N
      (fun n => rotateLoewnerCoeff c omega n)
      (fun n => rotateLoewnerCoeff cDot omega n) := by
  intro k hk
  change cDot (k + 1) / omega ^ (k + 1) =
    (deBrangesPartialSum (fun n => rotateLoewnerCoeff c omega n) k +
      deBrangesPartialSum (fun n => rotateLoewnerCoeff c omega n) (k + 1)) / 2
  rw [hode k hk]
  simp only [deBrangesDrivenPartialSum, pow_succ]
  field_simp [homega]

lemma norm_rotateLoewnerCoeff {c : ℕ → ℂ} {omega : ℂ} (homega : ‖omega‖ = 1)
    (n : ℕ) : ‖rotateLoewnerCoeff c omega n‖ = ‖c n‖ := by
  rw [rotateLoewnerCoeff, norm_div, norm_pow, homega, one_pow, div_one]

lemma div_pow_mul_conj_div_pow_eq {a b omega : ℂ} (homega : ‖omega‖ = 1)
    (n : ℕ) :
    (a / omega ^ n) * starRingEnd ℂ (b / omega ^ n) =
      a * starRingEnd ℂ b := by
  have hu0 : omega ^ n ≠ 0 := pow_ne_zero n (by
    intro h
    simp [h] at homega)
  have hconj0 : starRingEnd ℂ (omega ^ n) ≠ 0 :=
    (map_ne_zero (starRingEnd ℂ)).2 hu0
  have hone : omega ^ n * starRingEnd ℂ (omega ^ n) = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, norm_pow, homega, one_pow]
    norm_num
  calc
    (a / omega ^ n) * starRingEnd ℂ (b / omega ^ n) =
        (a * starRingEnd ℂ b) /
          (omega ^ n * starRingEnd ℂ (omega ^ n)) := by
      rw [map_div₀]
      field_simp [hu0, hconj0]
    _ = a * starRingEnd ℂ b := by rw [hone, div_one]

lemma deBrangesEnergyRate_rotate {N : ℕ} {tau tauDot : ℕ → ℝ}
    {c cDot : ℕ → ℂ} {omega : ℂ} (homega : ‖omega‖ = 1) :
    deBrangesEnergyRate N tau tauDot c cDot =
      deBrangesEnergyRate N tau tauDot
        (fun n => rotateLoewnerCoeff c omega n)
        (fun n => rotateLoewnerCoeff cDot omega n) := by
  unfold deBrangesEnergyRate
  apply Finset.sum_congr rfl
  intro k hk
  rw [norm_rotateLoewnerCoeff homega]
  rw [show
    (rotateLoewnerCoeff cDot omega (k + 1) *
      starRingEnd ℂ (rotateLoewnerCoeff c omega (k + 1))).re =
        (cDot (k + 1) * starRingEnd ℂ (c (k + 1))).re by
      exact congrArg Complex.re (div_pow_mul_conj_div_pow_eq homega (k + 1))]

lemma deBrangesEnergyRate_lower_bound_driven {N : ℕ} {tau tauDot : ℕ → ℝ}
    {c cDot : ℕ → ℂ} {omega : ℂ}
    (hsystem : SatisfiesDeBrangesSystem N tau tauDot)
    (homega : ‖omega‖ = 1)
    (hode : SatisfiesDrivenLoewnerLogarithmicODE N c cDot omega)
    (htauDot : ∀ k ∈ Finset.range N, tauDot (k + 1) ≤ 0) :
    (tauDot 1 - tau 1) / 2 ≤ deBrangesEnergyRate N tau tauDot c cDot := by
  rw [deBrangesEnergyRate_rotate homega]
  exact deBrangesEnergyRate_lower_bound hsystem
    (drivenLoewnerODE_rotate (by
      intro h
      simp [h] at homega) hode) htauDot

noncomputable def deBrangesWeight (N : ℕ) (tau : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, tau (k + 1) / ((k + 1 : ℕ) : ℝ)

noncomputable def deBrangesWeightRate (N : ℕ) (tauDot : ℕ → ℝ) : ℝ :=
  ∑ k ∈ Finset.range N, tauDot (k + 1) / ((k + 1 : ℕ) : ℝ)

lemma zero_add_sum_shift_eq_sum_add_terminal (r : ℕ → ℝ) (N : ℕ) :
    r 0 + ∑ k ∈ Finset.range N, r (k + 1) =
      (∑ k ∈ Finset.range N, r k) + r N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      calc
        r 0 + ((∑ k ∈ Finset.range N, r (k + 1)) + r (N + 1)) =
            (r 0 + ∑ k ∈ Finset.range N, r (k + 1)) + r (N + 1) := by ring
        _ = _ := by rw [ih]

lemma sum_sub_shift_eq_first_sub_terminal (a : ℕ → ℝ) (N : ℕ) :
    (∑ k ∈ Finset.range N, (a k - a (k + 1))) = a 0 - a N := by
  induction N with
  | zero => simp
  | succ N ih =>
      simp only [Finset.sum_range_succ]
      rw [ih]
      ring

lemma deBrangesSystem_boundary_eq_weightRate {N : ℕ} {tau tauDot : ℕ → ℝ}
    (hsystem : SatisfiesDeBrangesSystem N tau tauDot) :
    (tauDot 1 - tau 1) / 2 = deBrangesWeightRate N tauDot := by
  rcases hsystem with ⟨htau, htauDot, hsystem⟩
  let r : ℕ → ℝ := fun k => tauDot (k + 1) / ((k + 1 : ℕ) : ℝ)
  have hrN : r N = 0 := by simp [r, htauDot]
  have hshift : r 0 + ∑ k ∈ Finset.range N, r (k + 1) =
      ∑ k ∈ Finset.range N, r k := by
    simpa [hrN] using zero_add_sum_shift_eq_sum_add_terminal r N
  have hsumSystem :
      (∑ k ∈ Finset.range N,
          (tau (k + 1) - tau (k + 2))) =
        ∑ k ∈ Finset.range N, (-r k - r (k + 1)) := by
    apply Finset.sum_congr rfl
    intro k hk
    rw [hsystem k hk]
    dsimp only [r]
    rw [show k + 2 = k + 1 + 1 by omega]
    ring
  have htelescope :
      (∑ k ∈ Finset.range N,
          (tau (k + 1) - tau (k + 2))) = tau 1 := by
    have h := sum_sub_shift_eq_first_sub_terminal (fun k => tau (k + 1)) N
    simpa [htau] using h
  rw [htelescope] at hsumSystem
  have hsumSystem' :
      tau 1 = -(∑ k ∈ Finset.range N, r k) -
        ∑ k ∈ Finset.range N, r (k + 1) := by
    calc
      tau 1 = ∑ k ∈ Finset.range N, (-r k - r (k + 1)) := hsumSystem
      _ = _ := by
        rw [Finset.sum_sub_distrib, Finset.sum_neg_distrib]
  have hgoal : (r 0 - tau 1) / 2 = ∑ k ∈ Finset.range N, r k := by
    linarith
  simpa [deBrangesWeightRate, r] using hgoal

lemma hasDerivAt_norm_sq_complex {f : ℝ → ℂ} {f' : ℂ} {t : ℝ}
    (hf : HasDerivAt f f' t) :
    HasDerivAt (fun u => ‖f u‖ ^ 2)
      (2 * (f' * starRingEnd ℂ (f t)).re) t := by
  simpa only [Complex.inner, mul_comm] using hf.norm_sq

lemma hasDerivAt_deBrangesEnergy {N : ℕ} {tau tauDot : ℕ → ℝ → ℝ}
    {c cDot : ℕ → ℝ → ℂ} {t : ℝ}
    (htau : ∀ k ∈ Finset.range N, HasDerivAt (tau (k + 1)) (tauDot (k + 1) t) t)
    (hc : ∀ k ∈ Finset.range N, HasDerivAt (c (k + 1)) (cDot (k + 1) t) t) :
    HasDerivAt
      (fun u => deBrangesEnergy N (fun k => tau k u) (fun k => c k u))
      (deBrangesEnergyRate N (fun k => tau k t) (fun k => tauDot k t)
        (fun k => c k t) (fun k => cDot k t)) t := by
  unfold deBrangesEnergy deBrangesEnergyRate
  apply HasDerivAt.fun_sum
  intro k hk
  have hnorm := hasDerivAt_norm_sq_complex (hc k hk)
  have hprod := (htau k hk).mul hnorm
  simpa only [Pi.mul_apply, mul_assoc, mul_left_comm, mul_comm] using
    HasDerivAt.const_mul (((k + 1 : ℕ) : ℝ)) hprod

lemma hasDerivAt_deBrangesWeight {N : ℕ} {tau tauDot : ℕ → ℝ → ℝ} {t : ℝ}
    (htau : ∀ k ∈ Finset.range N, HasDerivAt (tau (k + 1)) (tauDot (k + 1) t) t) :
    HasDerivAt
      (fun u => deBrangesWeight N (fun k => tau k u))
      (deBrangesWeightRate N (fun k => tauDot k t)) t := by
  unfold deBrangesWeight deBrangesWeightRate
  apply HasDerivAt.fun_sum
  intro k hk
  exact (htau k hk).div_const _

noncomputable def deBrangesGap (N : ℕ) (tau : ℕ → ℝ → ℝ)
    (c : ℕ → ℝ → ℂ) (t : ℝ) : ℝ :=
  deBrangesEnergy N (fun k => tau k t) (fun k => c k t) -
    deBrangesWeight N (fun k => tau k t)

lemma hasDerivAt_deBrangesGap {N : ℕ} {tau tauDot : ℕ → ℝ → ℝ}
    {c cDot : ℕ → ℝ → ℂ} {t : ℝ}
    (htau : ∀ k ∈ Finset.range N, HasDerivAt (tau (k + 1)) (tauDot (k + 1) t) t)
    (hc : ∀ k ∈ Finset.range N, HasDerivAt (c (k + 1)) (cDot (k + 1) t) t) :
    HasDerivAt (deBrangesGap N tau c)
      (deBrangesEnergyRate N (fun k => tau k t) (fun k => tauDot k t)
          (fun k => c k t) (fun k => cDot k t) -
        deBrangesWeightRate N (fun k => tauDot k t)) t := by
  exact (hasDerivAt_deBrangesEnergy htau hc).sub (hasDerivAt_deBrangesWeight htau)

structure DeBrangesMilinCertificate (L : ℂ → ℂ) (N : ℕ) where
  c : ℕ → ℝ → ℂ
  cDot : ℕ → ℝ → ℂ
  omega : ℝ → ℂ
  tau : ℕ → ℝ → ℝ
  tauDot : ℕ → ℝ → ℝ
  c_initial : ∀ k ∈ Finset.range N, c (k + 1) 0 = logarithmicCoeff L (k + 1)
  tau_initial : ∀ k ∈ Finset.range N, tau (k + 1) 0 = ((N - k : ℕ) : ℝ)
  hasDerivAt_c : ∀ k ∈ Finset.range N, ∀ t, 0 ≤ t → HasDerivAt (c (k + 1)) (cDot (k + 1) t) t
  hasDerivAt_tau :
    ∀ k ∈ Finset.range N, ∀ t, 0 ≤ t → HasDerivAt (tau (k + 1)) (tauDot (k + 1) t) t
  norm_omega : ∀ t, 0 ≤ t → ‖omega t‖ = 1
  loewnerODE : ∀ t, 0 ≤ t →
    SatisfiesDrivenLoewnerLogarithmicODE N
      (fun k => c k t) (fun k => cDot k t) (omega t)
  deBrangesSystem : ∀ t, 0 ≤ t →
    SatisfiesDeBrangesSystem N (fun k => tau k t) (fun k => tauDot k t)
  tauDot_nonpos : ∀ t, 0 ≤ t → ∀ k ∈ Finset.range N, tauDot (k + 1) t ≤ 0
  gap_tendsto_zero : Tendsto (deBrangesGap N tau c) atTop (nhds 0)

lemma DeBrangesMilinCertificate.hasDerivAt_gap {L : ℂ → ℂ} {N : ℕ}
    (cert : DeBrangesMilinCertificate L N) {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (deBrangesGap N cert.tau cert.c)
      (deBrangesEnergyRate N (fun k => cert.tau k t) (fun k => cert.tauDot k t)
          (fun k => cert.c k t) (fun k => cert.cDot k t) -
        deBrangesWeightRate N (fun k => cert.tauDot k t)) t := by
  exact hasDerivAt_deBrangesGap
    (fun k hk => cert.hasDerivAt_tau k hk t ht)
    (fun k hk => cert.hasDerivAt_c k hk t ht)

lemma DeBrangesMilinCertificate.gap_mono {L : ℂ → ℂ} {N : ℕ}
    (cert : DeBrangesMilinCertificate L N) :
    MonotoneOn (deBrangesGap N cert.tau cert.c) (Set.Ici 0) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 0)
  · intro t ht
    exact (cert.hasDerivAt_gap ht).continuousAt.continuousWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      have ht' : t ∈ Set.Ioi 0 := by simpa only [interior_Ici] using ht
      exact (Set.mem_Ioi.mp ht').le
    exact (cert.hasDerivAt_gap ht0).differentiableAt.differentiableWithinAt
  · intro t ht
    have ht0 : 0 ≤ t := by
      have ht' : t ∈ Set.Ioi 0 := by simpa only [interior_Ici] using ht
      exact (Set.mem_Ioi.mp ht').le
    have hgap := cert.hasDerivAt_gap ht0
    rw [hgap.deriv]
    have hrate := deBrangesEnergyRate_lower_bound_driven
      (cert.deBrangesSystem t ht0) (cert.norm_omega t ht0)
      (cert.loewnerODE t ht0) (cert.tauDot_nonpos t ht0)
    have hweight := deBrangesSystem_boundary_eq_weightRate (cert.deBrangesSystem t ht0)
    linarith

lemma DeBrangesMilinCertificate.gap_zero_eq_milinFunctional {L : ℂ → ℂ} {N : ℕ}
    (cert : DeBrangesMilinCertificate L N) :
    deBrangesGap N cert.tau cert.c 0 = milinFunctional L N := by
  rw [milinFunctional_eq_weighted]
  unfold deBrangesGap deBrangesEnergy deBrangesWeight
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro k hk
  change
    ((k + 1 : ℕ) : ℝ) * cert.tau (k + 1) 0 * ‖cert.c (k + 1) 0‖ ^ 2 -
        cert.tau (k + 1) 0 / ((k + 1 : ℕ) : ℝ) =
      ((N - k : ℕ) : ℝ) *
        (((k + 1 : ℕ) : ℝ) * ‖logarithmicCoeff L (k + 1)‖ ^ 2 -
          1 / ((k + 1 : ℕ) : ℝ))
  rw [cert.c_initial k hk, cert.tau_initial k hk]
  ring

lemma DeBrangesMilinCertificate.milinFunctional_nonpos {L : ℂ → ℂ} {N : ℕ}
    (cert : DeBrangesMilinCertificate L N) : milinFunctional L N ≤ 0 := by
  have hle : deBrangesGap N cert.tau cert.c 0 ≤ 0 := by
    apply ge_of_tendsto cert.gap_tendsto_zero
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with t ht
    exact cert.gap_mono (Set.mem_Ici.mpr le_rfl) (Set.mem_Ici.mpr ht) ht
  rwa [cert.gap_zero_eq_milinFunctional] at hle

lemma satisfiesMilin_of_deBranges_certificates {L : ℂ → ℂ}
    (hcert : ∀ N : ℕ, Nonempty (DeBrangesMilinCertificate L N)) : SatisfiesMilin L := by
  intro N
  exact (hcert N).some.milinFunctional_nonpos

end Submission
