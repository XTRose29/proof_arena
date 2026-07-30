import Submission.Newton

open LeanEval.Dynamics
open MeasureTheory
open scoped ContDiff

namespace Submission.Majorant

noncomputable section

/-- The derivative weight used in the majorant argument.  Its deliberately
generous quadratic exponent makes every finite derivative loss absorbable in
an exponential radius while still allowing a quadratically convergent Newton
scheme to converge in every derivative. -/
def weight (s n : ℕ) : ℝ := (2 : ℝ) ^ (s * n ^ 2)

theorem weight_nonneg (s n : ℕ) : 0 ≤ weight s n := by
  exact pow_nonneg (by norm_num) _

theorem weight_pos (s n : ℕ) : 0 < weight s n := by
  exact pow_pos (by norm_num) _

theorem weight_exponent_mono {s s' n : ℕ} (hss' : s ≤ s') :
    weight s n ≤ weight s' n := by
  unfold weight
  exact pow_le_pow_right₀ (by norm_num) (Nat.mul_le_mul_right (n ^ 2) hss')

theorem weight_succ (s n : ℕ) :
    weight s (n + 1) =
      2 ^ s * (2 ^ (2 * s)) ^ n * weight s n := by
  unfold weight
  rw [← pow_mul, ← pow_add, ← pow_add]
  congr 1
  ring

theorem nat_succ_le_two_pow (n : ℕ) : n + 1 ≤ 2 ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ]
      omega

/-- A global derivative majorant. -/
def Majorized (s : ℕ) (A R : ℝ) (g : ℝ → ℝ) : Prop :=
  ∀ n t, ‖iteratedFDeriv ℝ n g t‖ ≤ A * weight s n * R ^ n

theorem majorized_zero (s : ℕ) (R : ℝ) :
    Majorized s 0 R (fun _ : ℝ => 0) := by
  intro n t
  simp

theorem Majorized.amplitude_mono {s : ℕ} {A A' R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) (hAA' : A ≤ A') (hR : 0 ≤ R) :
    Majorized s A' R g := by
  intro n t
  apply (hg n t).trans
  calc
    A * weight s n * R ^ n = A * (weight s n * R ^ n) := by ring
    _ ≤ A' * (weight s n * R ^ n) :=
      mul_le_mul_of_nonneg_right hAA'
        (mul_nonneg (weight_nonneg s n) (pow_nonneg hR n))
    _ = A' * weight s n * R ^ n := by ring

theorem Majorized.radius_mono {s : ℕ} {A R R' : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) (hA : 0 ≤ A) (hR : 0 ≤ R)
    (hRR' : R ≤ R') : Majorized s A R' g := by
  intro n t
  apply (hg n t).trans
  gcongr
  exact mul_nonneg hA (weight_nonneg s n)

theorem Majorized.exponent_mono {s s' : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) (hss' : s ≤ s')
    (hA : 0 ≤ A) (hR : 0 ≤ R) : Majorized s' A R g := by
  intro n t
  apply (hg n t).trans
  gcongr
  exact weight_exponent_mono hss'

theorem Majorized.neg {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) : Majorized s A R (-g) := by
  intro n t
  rw [iteratedFDeriv_neg_apply, norm_neg]
  exact hg n t

theorem Majorized.const_mul {s : ℕ} {A R c : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) (hgs : ContDiff ℝ ∞ g) :
    Majorized s (|c| * A) R (fun t => c * g t) := by
  intro n t
  rw [show (fun t => c * g t) = c • g by rfl]
  rw [iteratedFDeriv_const_smul_apply
      (hgs.contDiffAt.of_le
        (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))),
    norm_smul, Real.norm_eq_abs]
  calc
    |c| * ‖iteratedFDeriv ℝ n g t‖ ≤
        |c| * (A * weight s n * R ^ n) := by
      gcongr
      exact hg n t
    _ = (|c| * A) * weight s n * R ^ n := by ring

theorem Majorized.add {s : ℕ} {A B R : ℝ} {g h : ℝ → ℝ}
    (hg : Majorized s A R g) (hh : Majorized s B R h)
    (hgs : ContDiff ℝ ∞ g) (hhs : ContDiff ℝ ∞ h) :
    Majorized s (A + B) R (fun t => g t + h t) := by
  intro n t
  calc
    ‖iteratedFDeriv ℝ n (fun t => g t + h t) t‖ =
        ‖iteratedFDeriv ℝ n g t + iteratedFDeriv ℝ n h t‖ := by
      rw [show (fun t => g t + h t) = g + h by rfl,
        iteratedFDeriv_add
          (hgs.of_le
            (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top)))
          (hhs.of_le
            (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))),
        Pi.add_apply]
    _ ≤ ‖iteratedFDeriv ℝ n g t‖ + ‖iteratedFDeriv ℝ n h t‖ :=
      norm_add_le _ _
    _ ≤ A * weight s n * R ^ n + B * weight s n * R ^ n :=
      add_le_add (hg n t) (hh n t)
    _ = (A + B) * weight s n * R ^ n := by ring

theorem Majorized.sub {s : ℕ} {A B R : ℝ} {g h : ℝ → ℝ}
    (hg : Majorized s A R g) (hh : Majorized s B R h)
    (hgs : ContDiff ℝ ∞ g) (hhs : ContDiff ℝ ∞ h) :
    Majorized s (A + B) R (fun t => g t - h t) := by
  simpa only [sub_eq_add_neg, Pi.neg_apply] using hg.add hh.neg hgs hhs.neg

theorem Majorized.shift (a : ℝ) {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) :
    Majorized s A R (fun t => g (t + a)) := by
  intro n t
  rw [iteratedFDeriv_comp_add_right]
  exact hg n (t + a)

theorem Majorized.shift_sub (a : ℝ) {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) :
    Majorized s A R (fun t => g (t - a)) := by
  simpa only [sub_eq_add_neg] using hg.shift (-a)

theorem Majorized.deriv {s : ℕ} {A R : ℝ} {g : ℝ → ℝ}
    (hg : Majorized s A R g) :
    Majorized s (A * R * 2 ^ s) (2 ^ (2 * s) * R) (_root_.deriv g) := by
  intro n t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have hgn := hg (n + 1) t
  rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv] at hgn
  rw [show iteratedDeriv n (_root_.deriv g) = iteratedDeriv (n + 1) g by
    rw [iteratedDeriv_succ']]
  apply hgn.trans_eq
  rw [weight_succ, pow_succ, mul_pow]
  ring

theorem weight_mul_le {s r n i : ℕ} (hi : i ≤ n) :
    weight s i * weight r (n - i) ≤ weight (max s r) n := by
  have hiSq : i ^ 2 + (n - i) ^ 2 ≤ n ^ 2 := by
    nlinarith [Nat.zero_le (i * (n - i)), Nat.sub_add_cancel hi]
  have hexp : s * i ^ 2 + r * (n - i) ^ 2 ≤ max s r * n ^ 2 := by
    calc
      s * i ^ 2 + r * (n - i) ^ 2 ≤
          max s r * i ^ 2 + max s r * (n - i) ^ 2 := by
        gcongr
        · exact le_max_left s r
        · exact le_max_right s r
      _ = max s r * (i ^ 2 + (n - i) ^ 2) := by ring
      _ ≤ max s r * n ^ 2 := Nat.mul_le_mul_left _ hiSq
  unfold weight
  rw [← pow_add]
  exact pow_le_pow_right₀ (by norm_num) hexp

theorem Majorized.mul {s r : ℕ} {A B R S : ℝ} {g h : ℝ → ℝ}
    (hg : Majorized s A R g) (hh : Majorized r B S h)
    (hgs : ContDiff ℝ ∞ g) (hhs : ContDiff ℝ ∞ h)
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hR : 0 ≤ R) (hS : 0 ≤ S) :
    Majorized (max s r) (A * B) (4 * max R S) (fun t => g t * h t) := by
  intro n t
  let p := max s r
  let M := max R S
  have hM : 0 ≤ M := hR.trans (le_max_left R S)
  have hsum := norm_iteratedFDeriv_mul_le hgs hhs t
    (n := n) (by exact_mod_cast (show (n : ℕ∞) ≤ ⊤ from le_top))
  apply hsum.trans
  calc
    (∑ i ∈ Finset.range (n + 1), (n.choose i : ℝ) *
        ‖iteratedFDeriv ℝ i g t‖ *
        ‖iteratedFDeriv ℝ (n - i) h t‖) ≤
      ∑ _i ∈ Finset.range (n + 1),
        (2 : ℝ) ^ n * (A * B * weight p n * M ^ n) := by
      apply Finset.sum_le_sum
      intro i hi
      simp only [Finset.mem_range] at hi
      have hi' : i ≤ n := Nat.le_of_lt_succ hi
      have hchoose : (n.choose i : ℝ) ≤ (2 : ℝ) ^ n := by
        exact_mod_cast Nat.choose_le_two_pow n i
      have hw : weight s i * weight r (n - i) ≤ weight p n :=
        weight_mul_le hi'
      have hpow : R ^ i * S ^ (n - i) ≤ M ^ n := by
        calc
          R ^ i * S ^ (n - i) ≤ M ^ i * M ^ (n - i) := by
            gcongr
            · exact le_max_left R S
            · exact le_max_right R S
          _ = M ^ n := by rw [← pow_add, Nat.add_sub_of_le hi']
      calc
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i g t‖ *
            ‖iteratedFDeriv ℝ (n - i) h t‖ ≤
          (n.choose i : ℝ) * (A * weight s i * R ^ i) *
            (B * weight r (n - i) * S ^ (n - i)) := by
          apply mul_le_mul
          · exact mul_le_mul_of_nonneg_left (hg i t) (by positivity)
          · exact hh (n - i) t
          · positivity
          · exact mul_nonneg (by positivity)
              (mul_nonneg (mul_nonneg hA (weight_nonneg s i))
                (pow_nonneg hR i))
        _ ≤ (2 : ℝ) ^ n * (A * B * weight p n * M ^ n) := by
          have hcore :
              (weight s i * weight r (n - i)) *
                  (R ^ i * S ^ (n - i)) ≤ weight p n * M ^ n :=
            mul_le_mul hw hpow
              (mul_nonneg (pow_nonneg hR i) (pow_nonneg hS (n - i)))
              (weight_nonneg p n)
          calc
            (n.choose i : ℝ) * (A * weight s i * R ^ i) *
                (B * weight r (n - i) * S ^ (n - i)) =
              ((n.choose i : ℝ) * A * B) *
                ((weight s i * weight r (n - i)) *
                  (R ^ i * S ^ (n - i))) := by ring
            _ ≤ ((2 : ℝ) ^ n * A * B) * (weight p n * M ^ n) := by
              have hcoef : (n.choose i : ℝ) * A * B ≤
                  (2 : ℝ) ^ n * A * B := by
                gcongr
              exact mul_le_mul hcoef hcore
                (mul_nonneg
                  (mul_nonneg (weight_nonneg s i) (weight_nonneg r (n - i)))
                  (mul_nonneg (pow_nonneg hR i) (pow_nonneg hS (n - i))))
                (mul_nonneg (mul_nonneg (by positivity) hA) hB)
            _ = (2 : ℝ) ^ n * (A * B * weight p n * M ^ n) := by ring
    _ = ((n + 1 : ℕ) : ℝ) *
        ((2 : ℝ) ^ n * (A * B * weight p n * M ^ n)) := by simp
    _ ≤ (2 : ℝ) ^ n *
        ((2 : ℝ) ^ n * (A * B * weight p n * M ^ n)) := by
      apply mul_le_mul_of_nonneg_right
      · exact_mod_cast nat_succ_le_two_pow n
      · exact mul_nonneg (by positivity)
          (mul_nonneg
            (mul_nonneg (mul_nonneg hA hB) (weight_nonneg p n))
            (pow_nonneg hM n))
    _ = (A * B) * weight p n * (4 * M) ^ n := by
      rw [mul_pow, show (4 : ℝ) = 2 * 2 by norm_num, mul_pow]
      ring

end

end Submission.Majorant
