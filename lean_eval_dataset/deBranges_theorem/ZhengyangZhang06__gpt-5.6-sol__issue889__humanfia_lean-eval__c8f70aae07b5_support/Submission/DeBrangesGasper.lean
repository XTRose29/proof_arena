import Submission.DeBrangesPositivity
import Submission.OddClausen

namespace Submission

open Finset

noncomputable def gasperEvenRecurrenceTerm (k s r j : ℕ) : ℝ :=
  gasperWeight k (2 * s) j * gasperEvenInnerCoeff k s j (r - 2 * j)

noncomputable def gasperEvenTelescoper (k r j : ℕ) : ℝ :=
  -(2 * (j : ℝ)) * (2 * (k : ℝ) + 2 * j) *
      (2 * (k : ℝ) + r + 2 * j) *
      (2 * (k : ℝ) + r + 2 * j + 1) /
    (2 * (k : ℝ) + 4 * j + 1)

noncomputable def gasperEvenResidualCoeff (k r j : ℕ) : ℝ :=
  -((r : ℝ) * ((r : ℝ) - 1)) +
    (2 * (k : ℝ) + 2 * r - 1) * (2 * (j : ℝ)) *
      (2 * (k : ℝ) + 2 * j + 1)

lemma gasperEven_telescope_algebra {K R J T U : ℝ}
    (hden : K + 4 * J + 1 ≠ 0)
    (hden' : K + 4 * J + 5 ≠ 0)
    (hadj :
      U * ((2 * J + 2) * (K + 2 * J + 2) * (K + 4 * J + 1) *
        (K + R + 2 * J + 2) * (K + R + 2 * J + 3)) =
      T * ((R - 2 * J - 1) * (R - 2 * J) * (K + 2 * J + 1) *
        (K + 4 * J + 5) * (2 * J + 1))) :
    (-R * (R - 1) + (K + 2 * R - 1) * (2 * J) * (K + 2 * J + 1)) * T =
      (-(2 * (J + 1)) * (K + 2 * (J + 1)) *
          (K + R + 2 * (J + 1)) * (K + R + 2 * (J + 1) + 1) /
          (K + 4 * (J + 1) + 1)) * U -
      (-(2 * J) * (K + 2 * J) * (K + R + 2 * J) *
          (K + R + 2 * J + 1) / (K + 4 * J + 1)) * T := by
  have hnext :
      (-(2 * (J + 1)) * (K + 2 * (J + 1)) *
          (K + R + 2 * (J + 1)) * (K + R + 2 * (J + 1) + 1) /
          (K + 4 * (J + 1) + 1)) * U =
        (-(R - 2 * J - 1) * (R - 2 * J) * (K + 2 * J + 1) *
          (2 * J + 1) / (K + 4 * J + 1)) * T := by
    rw [div_mul_eq_mul_div, div_mul_eq_mul_div]
    have hdenNext : K + 4 * (J + 1) + 1 ≠ 0 := by
      have heq : K + 4 * (J + 1) + 1 = K + 4 * J + 5 := by ring
      rw [heq]
      exact hden'
    apply (div_eq_iff hdenNext).2
    rw [div_mul_eq_mul_div]
    apply (eq_div_iff hden).2
    linear_combination -hadj
  rw [hnext]
  have hcoeff :
      -R * (R - 1) + (K + 2 * R - 1) * (2 * J) * (K + 2 * J + 1) =
        (-(R - 2 * J - 1) * (R - 2 * J) * (K + 2 * J + 1) *
            (2 * J + 1) / (K + 4 * J + 1)) -
          (-(2 * J) * (K + 2 * J) * (K + R + 2 * J) *
            (K + R + 2 * J + 1) / (K + 4 * J + 1)) := by
    rw [div_sub_div_same]
    apply (eq_div_iff hden).2
    ring
  rw [hcoeff]
  ring

lemma gasperEvenRecurrenceTerm_telescope {k s r j : ℕ}
    (hj : j < s) (hr : 2 * (j + 1) ≤ r) :
    gasperEvenResidualCoeff k r j * gasperEvenRecurrenceTerm k s r j =
      gasperEvenTelescoper k r (j + 1) *
          gasperEvenRecurrenceTerm k s r (j + 1) -
        gasperEvenTelescoper k r j * gasperEvenRecurrenceTerm k s r j := by
  have hadj := gasperEvenAdjacentTerm (k := k) (s := s) hj (r - 2 * (j + 1))
  have hsub0 : r - 2 * (j + 1) + 2 = r - 2 * j := by omega
  have hsub1 : r - 2 * (j + 1) + 1 = r - 2 * j - 1 := by omega
  have hindex4 :
      2 * k + 4 * j + (r - 2 * (j + 1)) + 4 = 2 * k + r + 2 * j + 2 := by omega
  have hindex5 :
      2 * k + 4 * j + (r - 2 * (j + 1)) + 5 = 2 * k + r + 2 * j + 3 := by omega
  rw [hsub0, hsub1, hindex4, hindex5] at hadj
  simp only [gasperEvenResidualCoeff, gasperEvenRecurrenceTerm,
    gasperEvenTelescoper]
  have hden : 2 * (k : ℝ) + 4 * j + 1 ≠ 0 := by positivity
  have hden' : 2 * (k : ℝ) + 4 * j + 5 ≠ 0 := by positivity
  have hadj' :
      (gasperWeight k (2 * s) (j + 1) *
          gasperEvenInnerCoeff k s (j + 1) (r - 2 * (j + 1))) *
          ((2 * (j : ℝ) + 2) * (2 * (k : ℝ) + 2 * j + 2) *
            (2 * (k : ℝ) + 4 * j + 1) *
            (2 * (k : ℝ) + r + 2 * j + 2) *
            (2 * (k : ℝ) + r + 2 * j + 3)) =
        (gasperWeight k (2 * s) j *
          gasperEvenInnerCoeff k s j (r - 2 * j)) *
          (((r : ℝ) - 2 * j - 1) * ((r : ℝ) - 2 * j) *
            (2 * (k : ℝ) + 2 * j + 1) *
            (2 * (k : ℝ) + 4 * j + 5) * (2 * (j : ℝ) + 1)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ r - 2 * j),
      Nat.cast_sub (by omega : 2 * j ≤ r)] at hadj
    push_cast at hadj ⊢
    exact hadj
  convert gasperEven_telescope_algebra
      (K := 2 * (k : ℝ)) (R := (r : ℝ)) (J := (j : ℝ))
      (T := gasperWeight k (2 * s) j * gasperEvenInnerCoeff k s j (r - 2 * j))
      (U := gasperWeight k (2 * s) (j + 1) *
        gasperEvenInnerCoeff k s (j + 1) (r - 2 * (j + 1)))
      hden hden' hadj' using 1 <;> push_cast <;> ring

lemma sum_range_forward_sub (a : ℕ → ℝ) (n : ℕ) :
    (∑ j ∈ range n, (a (j + 1) - a j)) = a n - a 0 := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [sum_range_succ, ih]
      ring

@[simp]
lemma gasperEvenTelescoper_zero (k r : ℕ) : gasperEvenTelescoper k r 0 = 0 := by
  simp [gasperEvenTelescoper]

lemma gasperEven_boundary_even (k s q : ℕ) :
    gasperEvenResidualCoeff k (2 * q) q *
        gasperEvenRecurrenceTerm k s (2 * q) q =
      -gasperEvenTelescoper k (2 * q) q *
        gasperEvenRecurrenceTerm k s (2 * q) q := by
  have hden : 2 * (k : ℝ) + 4 * q + 1 ≠ 0 := by positivity
  simp only [gasperEvenResidualCoeff, gasperEvenTelescoper]
  field_simp [hden]
  push_cast
  ring

lemma gasperEven_boundary_odd (k s q : ℕ) :
    gasperEvenResidualCoeff k (2 * q + 1) q *
        gasperEvenRecurrenceTerm k s (2 * q + 1) q =
      -gasperEvenTelescoper k (2 * q + 1) q *
        gasperEvenRecurrenceTerm k s (2 * q + 1) q := by
  have hden : 2 * (k : ℝ) + 4 * q + 1 ≠ 0 := by positivity
  simp only [gasperEvenResidualCoeff, gasperEvenTelescoper]
  field_simp [hden]
  push_cast
  ring

lemma sum_gasperEvenResidual_even {k s q : ℕ} (hq : q ≤ s) :
    (∑ j ∈ range (q + 1),
      gasperEvenResidualCoeff k (2 * q) j *
        gasperEvenRecurrenceTerm k s (2 * q) j) = 0 := by
  rw [sum_range_succ]
  have hprefix :
      (∑ j ∈ range q,
        gasperEvenResidualCoeff k (2 * q) j *
          gasperEvenRecurrenceTerm k s (2 * q) j) =
        ∑ j ∈ range q,
          (gasperEvenTelescoper k (2 * q) (j + 1) *
              gasperEvenRecurrenceTerm k s (2 * q) (j + 1) -
            gasperEvenTelescoper k (2 * q) j *
              gasperEvenRecurrenceTerm k s (2 * q) j) := by
    apply sum_congr rfl
    intro j hj
    have hjq : j < q := mem_range.mp hj
    exact gasperEvenRecurrenceTerm_telescope (by omega) (by omega)
  rw [hprefix, sum_range_forward_sub
    (fun j => gasperEvenTelescoper k (2 * q) j *
      gasperEvenRecurrenceTerm k s (2 * q) j) q]
  rw [gasperEvenTelescoper_zero, zero_mul, sub_zero,
    gasperEven_boundary_even]
  ring

lemma sum_gasperEvenResidual_odd {k s q : ℕ} (hq : q ≤ s) :
    (∑ j ∈ range (q + 1),
      gasperEvenResidualCoeff k (2 * q + 1) j *
        gasperEvenRecurrenceTerm k s (2 * q + 1) j) = 0 := by
  rw [sum_range_succ]
  have hprefix :
      (∑ j ∈ range q,
        gasperEvenResidualCoeff k (2 * q + 1) j *
          gasperEvenRecurrenceTerm k s (2 * q + 1) j) =
        ∑ j ∈ range q,
          (gasperEvenTelescoper k (2 * q + 1) (j + 1) *
              gasperEvenRecurrenceTerm k s (2 * q + 1) (j + 1) -
            gasperEvenTelescoper k (2 * q + 1) j *
              gasperEvenRecurrenceTerm k s (2 * q + 1) j) := by
    apply sum_congr rfl
    intro j hj
    have hjq : j < q := mem_range.mp hj
    exact gasperEvenRecurrenceTerm_telescope (by omega) (by omega)
  rw [hprefix, sum_range_forward_sub
    (fun j => gasperEvenTelescoper k (2 * q + 1) j *
      gasperEvenRecurrenceTerm k s (2 * q + 1) j) q]
  rw [gasperEvenTelescoper_zero, zero_mul, sub_zero,
    gasperEven_boundary_odd]
  ring

noncomputable def gasperEvenCoeff (k s r : ℕ) : ℝ :=
  ∑ j ∈ range (r / 2 + 1), gasperEvenRecurrenceTerm k s r j

noncomputable def deBrangesRecurrenceDen (k r : ℕ) : ℝ :=
  (r : ℝ) * (2 * (k : ℝ) + r) * (2 * (k : ℝ) + 2 * r + 1)

noncomputable def deBrangesRecurrenceNum (k s r : ℕ) : ℝ :=
  ((r : ℝ) - 1 - 2 * s) * (2 * (k : ℝ) + 2 * s + r + 1) *
    (2 * (k : ℝ) + 2 * r - 1)

lemma gasperEvenInnerRecurrence {k s r j : ℕ}
    (hjs : j ≤ s) (hjr : 2 * j < r) :
    gasperEvenRecurrenceTerm k s r j *
        (((r : ℝ) - 2 * j) * (2 * (k : ℝ) + r + 2 * j + 1) *
          (2 * (k : ℝ) + 2 * r + 1)) =
      gasperEvenRecurrenceTerm k s (r - 1) j *
        (((r : ℝ) - 1 - 2 * s) * (2 * (k : ℝ) + 2 * s + r + 1) *
          (2 * (k : ℝ) + 2 * r)) := by
  have hrec := clausenRecCoeff_succ
    (a := -((s - j : ℕ) : ℝ))
    (b := ((k + s + 1 + j : ℕ) : ℝ))
    (c := ((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2)
    (n := r - 1 - 2 * j)
    (by
      rw [Nat.cast_sub (R := ℝ) hjs]
      push_cast
      ring_nf
      positivity)
    (by positivity)
  have hnext : r - 1 - 2 * j + 1 = r - 2 * j := by omega
  rw [hnext] at hrec
  rw [gasperEvenRecurrenceTerm, gasperEvenRecurrenceTerm,
    gasperEvenInnerCoeff, gasperEvenInnerCoeff]
  rw [show r - 1 - 2 * j = (r - 1) - 2 * j by omega]
  rw [Nat.cast_sub (R := ℝ) hjs] at hrec
  rw [Nat.cast_sub (R := ℝ) (by omega : 2 * j ≤ r)] at hrec
  rw [Nat.cast_sub (R := ℝ) (by omega : 2 * j ≤ r - 1)] at hrec
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ r)] at hrec
  rw [Nat.cast_sub (R := ℝ) hjs]
  push_cast at hrec ⊢
  have hscaled := congrArg
    (fun x : ℝ => 2 * gasperWeight k (2 * s) j * x) hrec
  convert hscaled using 1 <;> ring

lemma gasperEvenTargetTermRecurrence {k s r j : ℕ}
    (hjs : j ≤ s) (hjr : 2 * j < r) :
    (2 * (k : ℝ) + 2 * r) *
        (deBrangesRecurrenceDen k r * gasperEvenRecurrenceTerm k s r j -
          deBrangesRecurrenceNum k s r *
            gasperEvenRecurrenceTerm k s (r - 1) j) =
      (2 * (k : ℝ) + 2 * r + 1) * gasperEvenResidualCoeff k r j *
        gasperEvenRecurrenceTerm k s r j := by
  have hinner := gasperEvenInnerRecurrence (k := k) (s := s) hjs hjr
  simp only [deBrangesRecurrenceDen, deBrangesRecurrenceNum,
    gasperEvenResidualCoeff]
  linear_combination
    (2 * (k : ℝ) + 2 * r - 1) * hinner

lemma gasperEvenCoeff_even (k s q : ℕ) :
    gasperEvenCoeff k s (2 * q) =
      ∑ j ∈ range (q + 1), gasperEvenRecurrenceTerm k s (2 * q) j := by
  rw [gasperEvenCoeff]
  congr 2
  omega

lemma gasperEvenCoeff_odd (k s q : ℕ) :
    gasperEvenCoeff k s (2 * q + 1) =
      ∑ j ∈ range (q + 1), gasperEvenRecurrenceTerm k s (2 * q + 1) j := by
  rw [gasperEvenCoeff]
  congr 2
  omega

lemma gasperEvenCoeff_recurrence_odd {k s q : ℕ} (hq : q ≤ s) :
    deBrangesRecurrenceDen k (2 * q + 1) * gasperEvenCoeff k s (2 * q + 1) =
      deBrangesRecurrenceNum k s (2 * q + 1) * gasperEvenCoeff k s (2 * q) := by
  rw [gasperEvenCoeff_odd, gasperEvenCoeff_even]
  let F : ℝ := 2 * (k : ℝ) + 2 * (2 * q + 1)
  let G : ℝ := 2 * (k : ℝ) + 2 * (2 * q + 1) + 1
  have hsum :
      F *
          (deBrangesRecurrenceDen k (2 * q + 1) *
              (∑ j ∈ range (q + 1),
                gasperEvenRecurrenceTerm k s (2 * q + 1) j) -
            deBrangesRecurrenceNum k s (2 * q + 1) *
              (∑ j ∈ range (q + 1),
                gasperEvenRecurrenceTerm k s (2 * q) j)) =
        G *
          ∑ j ∈ range (q + 1),
            gasperEvenResidualCoeff k (2 * q + 1) j *
              gasperEvenRecurrenceTerm k s (2 * q + 1) j := by
    calc
      _ = ∑ j ∈ range (q + 1),
          F *
            (deBrangesRecurrenceDen k (2 * q + 1) *
                gasperEvenRecurrenceTerm k s (2 * q + 1) j -
              deBrangesRecurrenceNum k s (2 * q + 1) *
                gasperEvenRecurrenceTerm k s (2 * q) j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
            Finset.mul_sum]
      _ = ∑ j ∈ range (q + 1),
          G * gasperEvenResidualCoeff k (2 * q + 1) j *
            gasperEvenRecurrenceTerm k s (2 * q + 1) j := by
          apply sum_congr rfl
          intro j hj
          have hjq : j ≤ q := Nat.le_of_lt_succ (mem_range.mp hj)
          simpa [F, G] using gasperEvenTargetTermRecurrence
            (k := k) (s := s) (r := 2 * q + 1) (j := j) (by omega) (by omega)
      _ = _ := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
  rw [sum_gasperEvenResidual_odd hq, mul_zero] at hsum
  have hF : F ≠ 0 := by
    dsimp only [F]
    positivity
  have hzero :
      deBrangesRecurrenceDen k (2 * q + 1) *
          (∑ j ∈ range (q + 1), gasperEvenRecurrenceTerm k s (2 * q + 1) j) -
        deBrangesRecurrenceNum k s (2 * q + 1) *
          (∑ j ∈ range (q + 1), gasperEvenRecurrenceTerm k s (2 * q) j) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left hF
  linarith

lemma gasperEvenTarget_boundary_even (k s q : ℕ) :
    (2 * (k : ℝ) + 2 * (2 * q)) *
        (deBrangesRecurrenceDen k (2 * q) *
          gasperEvenRecurrenceTerm k s (2 * q) q) =
      (2 * (k : ℝ) + 2 * (2 * q) + 1) *
        gasperEvenResidualCoeff k (2 * q) q *
          gasperEvenRecurrenceTerm k s (2 * q) q := by
  simp only [deBrangesRecurrenceDen, gasperEvenResidualCoeff]
  push_cast
  ring

lemma gasperEvenCoeff_recurrence_even {k s p : ℕ} (hp : p + 1 ≤ s) :
    deBrangesRecurrenceDen k (2 * (p + 1)) *
        gasperEvenCoeff k s (2 * (p + 1)) =
      deBrangesRecurrenceNum k s (2 * (p + 1)) *
        gasperEvenCoeff k s (2 * p + 1) := by
  rw [gasperEvenCoeff_even, gasperEvenCoeff_odd]
  let R : ℕ := 2 * (p + 1)
  let F : ℝ := 2 * (k : ℝ) + 2 * R
  let G : ℝ := 2 * (k : ℝ) + 2 * R + 1
  have hsum :
      F *
          (deBrangesRecurrenceDen k R *
              ((∑ j ∈ range (p + 1), gasperEvenRecurrenceTerm k s R j) +
                gasperEvenRecurrenceTerm k s R (p + 1)) -
            deBrangesRecurrenceNum k s R *
              (∑ j ∈ range (p + 1),
                gasperEvenRecurrenceTerm k s (2 * p + 1) j)) =
        G *
          ∑ j ∈ range (p + 2),
            gasperEvenResidualCoeff k R j *
              gasperEvenRecurrenceTerm k s R j := by
    have hdist :
        (∑ j ∈ range (p + 1),
          F *
            (deBrangesRecurrenceDen k R * gasperEvenRecurrenceTerm k s R j -
              deBrangesRecurrenceNum k s R *
                gasperEvenRecurrenceTerm k s (2 * p + 1) j)) =
          F *
            (deBrangesRecurrenceDen k R *
                (∑ j ∈ range (p + 1), gasperEvenRecurrenceTerm k s R j) -
              deBrangesRecurrenceNum k s R *
                (∑ j ∈ range (p + 1),
                  gasperEvenRecurrenceTerm k s (2 * p + 1) j)) := by
      calc
        _ = F * ∑ j ∈ range (p + 1),
            (deBrangesRecurrenceDen k R * gasperEvenRecurrenceTerm k s R j -
              deBrangesRecurrenceNum k s R *
                gasperEvenRecurrenceTerm k s (2 * p + 1) j) := by
              rw [Finset.mul_sum]
        _ = F *
            ((∑ j ∈ range (p + 1),
                deBrangesRecurrenceDen k R * gasperEvenRecurrenceTerm k s R j) -
              ∑ j ∈ range (p + 1),
                deBrangesRecurrenceNum k s R *
                  gasperEvenRecurrenceTerm k s (2 * p + 1) j) := by
              rw [Finset.sum_sub_distrib]
        _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ =
          (∑ j ∈ range (p + 1),
            F *
              (deBrangesRecurrenceDen k R * gasperEvenRecurrenceTerm k s R j -
                deBrangesRecurrenceNum k s R *
                  gasperEvenRecurrenceTerm k s (2 * p + 1) j)) +
            F * deBrangesRecurrenceDen k R *
              gasperEvenRecurrenceTerm k s R (p + 1) := by
          rw [hdist]
          ring
      _ =
          (∑ j ∈ range (p + 1),
            G * gasperEvenResidualCoeff k R j *
              gasperEvenRecurrenceTerm k s R j) +
            G * gasperEvenResidualCoeff k R (p + 1) *
              gasperEvenRecurrenceTerm k s R (p + 1) := by
          have hprefix :
              (∑ j ∈ range (p + 1),
                F *
                  (deBrangesRecurrenceDen k R * gasperEvenRecurrenceTerm k s R j -
                    deBrangesRecurrenceNum k s R *
                      gasperEvenRecurrenceTerm k s (2 * p + 1) j)) =
                ∑ j ∈ range (p + 1),
                  G * gasperEvenResidualCoeff k R j *
                    gasperEvenRecurrenceTerm k s R j := by
            apply sum_congr rfl
            intro j hj
            have hjp : j ≤ p := Nat.le_of_lt_succ (mem_range.mp hj)
            have hterm := gasperEvenTargetTermRecurrence
              (k := k) (s := s) (r := R) (j := j) (by omega) (by dsimp only [R]; omega)
            simpa [F, G, R, show R - 1 = 2 * p + 1 by dsimp only [R]; omega] using hterm
          have hboundary :
              F * deBrangesRecurrenceDen k R *
                  gasperEvenRecurrenceTerm k s R (p + 1) =
                G * gasperEvenResidualCoeff k R (p + 1) *
                  gasperEvenRecurrenceTerm k s R (p + 1) := by
            have hb := gasperEvenTarget_boundary_even k s (p + 1)
            push_cast at hb
            dsimp only [F, G, R]
            push_cast
            ring_nf at hb ⊢
            exact hb
          calc
            _ = (∑ j ∈ range (p + 1),
                  G * gasperEvenResidualCoeff k R j *
                    gasperEvenRecurrenceTerm k s R j) +
                F * deBrangesRecurrenceDen k R *
                  gasperEvenRecurrenceTerm k s R (p + 1) := by rw [hprefix]
            _ = _ := by rw [hboundary]
      _ = _ := by
          conv_rhs =>
            rw [sum_range_succ, mul_add, Finset.mul_sum]
          ring_nf
  have hres := sum_gasperEvenResidual_even (k := k) (s := s) (q := p + 1) hp
  change (∑ j ∈ range (p + 2),
    gasperEvenResidualCoeff k R j * gasperEvenRecurrenceTerm k s R j) = 0 at hres
  rw [hres, mul_zero] at hsum
  have hF : F ≠ 0 := by
    dsimp only [F, R]
    positivity
  have hzero :
      deBrangesRecurrenceDen k R *
          ((∑ j ∈ range (p + 1), gasperEvenRecurrenceTerm k s R j) +
            gasperEvenRecurrenceTerm k s R (p + 1)) -
        deBrangesRecurrenceNum k s R *
          (∑ j ∈ range (p + 1),
            gasperEvenRecurrenceTerm k s (2 * p + 1) j) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left hF
  dsimp only [R] at hzero
  have hsplit :
      (∑ j ∈ range (p + 2),
        gasperEvenRecurrenceTerm k s (2 * (p + 1)) j) =
        (∑ j ∈ range (p + 1),
          gasperEvenRecurrenceTerm k s (2 * (p + 1)) j) +
          gasperEvenRecurrenceTerm k s (2 * (p + 1)) (p + 1) := by
    rw [show p + 2 = (p + 1) + 1 by omega, sum_range_succ]
  rw [hsplit]
  linarith

lemma gasperEvenCoeff_recurrence {k s r : ℕ} (hr : 0 < r) (hrs : r ≤ 2 * s) :
    deBrangesRecurrenceDen k r * gasperEvenCoeff k s r =
      deBrangesRecurrenceNum k s r * gasperEvenCoeff k s (r - 1) := by
  rcases Nat.even_or_odd r with ⟨q, hq⟩ | ⟨q, hq⟩
  · subst r
    have hq0 : 0 < q := by omega
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0.ne'
    have hmain : p + 1 + (p + 1) = 2 * (p + 1) := by omega
    have hprev : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
    rw [hmain, hprev]
    exact gasperEvenCoeff_recurrence_even (k := k) (s := s) (p := p) (by omega)
  · subst r
    simpa [show 2 * q + 1 - 1 = 2 * q by omega] using
      gasperEvenCoeff_recurrence_odd (k := k) (s := s) (q := q) (by omega)

@[simp]
lemma gasperEvenCoeff_zero (k s : ℕ) : gasperEvenCoeff k s 0 = 1 := by
  simp [gasperEvenCoeff, gasperEvenRecurrenceTerm, gasperWeight,
    gasperEvenInnerCoeff, clausenRecCoeff]

noncomputable def deBrangesNormalizedCoeff (k m r : ℕ) : ℝ :=
  hypergeom3RecCoeff (-(m : ℝ)) (2 * (k : ℝ) + m + 2)
    ((k : ℝ) + 1 / 2) (2 * (k : ℝ) + 1) ((k : ℝ) + 3 / 2) r

@[simp]
lemma deBrangesNormalizedCoeff_zero (k m : ℕ) :
    deBrangesNormalizedCoeff k m 0 = 1 := by
  simp [deBrangesNormalizedCoeff]

lemma deBrangesNormalizedCoeff_recurrence {k s r : ℕ} (hr : 0 < r) :
    deBrangesRecurrenceDen k r * deBrangesNormalizedCoeff k (2 * s) r =
      deBrangesRecurrenceNum k s r * deBrangesNormalizedCoeff k (2 * s) (r - 1) := by
  have hrec := hypergeom3RecCoeff_succ
    (p := -((2 * s : ℕ) : ℝ))
    (q := 2 * (k : ℝ) + (2 * s : ℕ) + 2)
    (r := (k : ℝ) + 1 / 2)
    (u := 2 * (k : ℝ) + 1)
    (v := (k : ℝ) + 3 / 2)
    (n := r - 1) (by positivity) (by positivity)
  have hnext : r - 1 + 1 = r := by omega
  rw [hnext] at hrec
  simp only [deBrangesNormalizedCoeff, deBrangesRecurrenceDen,
    deBrangesRecurrenceNum]
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ r)] at hrec
  push_cast at hrec ⊢
  linear_combination 2 * hrec

lemma gasperEvenCoeff_eq_normalized {k s r : ℕ} (hr : r ≤ 2 * s) :
    gasperEvenCoeff k s r = deBrangesNormalizedCoeff k (2 * s) r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrec := gasperEvenCoeff_recurrence (k := k) (s := s)
        (r := r + 1) (by omega) hr
      have htarget := deBrangesNormalizedCoeff_recurrence
        (k := k) (s := s) (r := r + 1) (by omega)
      rw [show r + 1 - 1 = r by omega, ih (by omega)] at hrec
      rw [show r + 1 - 1 = r by omega] at htarget
      have hden : deBrangesRecurrenceDen k (r + 1) ≠ 0 := by
        unfold deBrangesRecurrenceDen
        positivity
      apply mul_left_cancel₀ hden
      exact hrec.trans htarget.symm

lemma deBrangesChooseLeftStep (k r : ℕ) (hr : 0 < r) :
    (r : ℝ) * ((2 * k + r : ℕ) : ℝ) * (Nat.choose (2 * k + 2 * r) r : ℝ) =
      ((2 * k + 2 * r - 1 : ℕ) : ℝ) * ((2 * k + 2 * r : ℕ) : ℝ) *
        (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) := by
  have htop := Nat.choose_mul_succ_eq (2 * k + 2 * r - 2) (r - 1)
  have hdiag := Nat.add_one_mul_choose_eq (2 * k + 2 * r - 1) (r - 1)
  have htopNat :
      Nat.choose (2 * k + 2 * r - 2) (r - 1) * (2 * k + 2 * r - 1) =
        Nat.choose (2 * k + 2 * r - 1) (r - 1) * (2 * k + r) := by
    rw [show 2 * k + 2 * r - 2 + 1 = 2 * k + 2 * r - 1 by omega] at htop
    rw [show 2 * k + 2 * r - 1 - (r - 1) = 2 * k + r by omega] at htop
    exact htop
  have hdiagNat :
      (2 * k + 2 * r) * Nat.choose (2 * k + 2 * r - 1) (r - 1) =
        Nat.choose (2 * k + 2 * r) r * r := by
    simpa only [show 2 * k + 2 * r - 1 + 1 = 2 * k + 2 * r by omega,
      show r - 1 + 1 = r by omega] using hdiag
  have htop' :
      (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) *
          ((2 * k + 2 * r - 1 : ℕ) : ℝ) =
        (Nat.choose (2 * k + 2 * r - 1) (r - 1) : ℝ) *
          ((2 * k + r : ℕ) : ℝ) := by
    exact_mod_cast htopNat
  have hdiag' :
      ((2 * k + 2 * r : ℕ) : ℝ) *
          (Nat.choose (2 * k + 2 * r - 1) (r - 1) : ℝ) =
        (Nat.choose (2 * k + 2 * r) r : ℝ) * (r : ℝ) := by
    exact_mod_cast hdiagNat
  calc
    (r : ℝ) * ((2 * k + r : ℕ) : ℝ) * (Nat.choose (2 * k + 2 * r) r : ℝ) =
        ((2 * k + r : ℕ) : ℝ) *
          (((2 * k + 2 * r : ℕ) : ℝ) *
            (Nat.choose (2 * k + 2 * r - 1) (r - 1) : ℝ)) := by
          rw [hdiag']
          ring
    _ = ((2 * k + 2 * r : ℕ) : ℝ) *
        ((Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) *
          ((2 * k + 2 * r - 1 : ℕ) : ℝ)) := by rw [htop']; ring
    _ = _ := by ring

lemma deBrangesChooseRightStep (k s r : ℕ) (hrs : r ≤ 2 * s) :
    ((2 * k + 2 * r : ℕ) : ℝ) * ((2 * k + 2 * r + 1 : ℕ) : ℝ) *
        (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r) : ℝ) =
      ((2 * k + 2 * s + r + 1 : ℕ) : ℝ) * ((2 * s - r + 1 : ℕ) : ℝ) *
        (Nat.choose (2 * k + 2 * s + r) (2 * s - r + 1) : ℝ) := by
  have htop := Nat.choose_mul_succ_eq (2 * k + 2 * s + r) (2 * s - r + 1)
  have hright := Nat.choose_succ_right_eq (2 * k + 2 * s + r + 1) (2 * s - r)
  have htopNat :
      Nat.choose (2 * k + 2 * s + r) (2 * s - r + 1) *
          (2 * k + 2 * s + r + 1) =
        Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r + 1) *
          (2 * k + 2 * r) := by
    rw [show 2 * k + 2 * s + r + 1 - (2 * s - r + 1) =
      2 * k + 2 * r by omega] at htop
    exact htop
  have hrightNat :
      Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r + 1) *
          (2 * s - r + 1) =
        Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r) *
          (2 * k + 2 * r + 1) := by
    rw [show 2 * k + 2 * s + r + 1 - (2 * s - r) =
      2 * k + 2 * r + 1 by omega] at hright
    exact hright
  have htop' :
      (Nat.choose (2 * k + 2 * s + r) (2 * s - r + 1) : ℝ) *
          ((2 * k + 2 * s + r + 1 : ℕ) : ℝ) =
        (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r + 1) : ℝ) *
          ((2 * k + 2 * r : ℕ) : ℝ) := by
    exact_mod_cast htopNat
  have hright' :
      (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r + 1) : ℝ) *
          ((2 * s - r + 1 : ℕ) : ℝ) =
        (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r) : ℝ) *
          ((2 * k + 2 * r + 1 : ℕ) : ℝ) := by
    exact_mod_cast hrightNat
  calc
    ((2 * k + 2 * r : ℕ) : ℝ) * ((2 * k + 2 * r + 1 : ℕ) : ℝ) *
        (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r) : ℝ) =
      ((2 * k + 2 * r : ℕ) : ℝ) *
        ((Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r + 1) : ℝ) *
          ((2 * s - r + 1 : ℕ) : ℝ)) := by
        rw [hright']
        ring
    _ = ((2 * s - r + 1 : ℕ) : ℝ) *
        ((Nat.choose (2 * k + 2 * s + r) (2 * s - r + 1) : ℝ) *
          ((2 * k + 2 * s + r + 1 : ℕ) : ℝ)) := by rw [htop']; ring
    _ = _ := by ring

lemma deBrangesInitialTerm_recurrence_even {k s r : ℕ}
    (hr0 : 0 < r) (hrs : r ≤ 2 * s) :
    deBrangesRecurrenceDen k r * deBrangesInitialTerm k (2 * s) r =
      deBrangesRecurrenceNum k s r * deBrangesInitialTerm k (2 * s) (r - 1) := by
  have hrprev : r - 1 ≤ 2 * s := by omega
  rw [deBrangesInitialTerm, if_pos hrs,
    deBrangesInitialTerm, if_pos hrprev]
  have hsign : (-1 : ℝ) ^ r = -((-1 : ℝ) ^ (r - 1)) := by
    calc
      (-1 : ℝ) ^ r = (-1 : ℝ) ^ ((r - 1) + 1) := by congr 1; omega
      _ = -((-1 : ℝ) ^ (r - 1)) := by rw [pow_succ]; ring
  rw [hsign]
  have hleft := deBrangesChooseLeftStep k r hr0
  have hright := deBrangesChooseRightStep k s r hrs
  simp only [deBrangesRecurrenceDen, deBrangesRecurrenceNum]
  simp only [show 2 * k + 2 * (r - 1) = 2 * k + 2 * r - 2 by omega,
    show 2 * k + 2 * s + (r - 1) + 1 = 2 * k + 2 * s + r by omega,
    show 2 * s - (r - 1) = 2 * s - r + 1 by omega]
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ 2 * k + 2 * r)] at hleft
  push_cast at hleft hright ⊢
  calc
    (r : ℝ) * (2 * (k : ℝ) + r) * (2 * (k : ℝ) + 2 * r + 1) *
        (-((-1 : ℝ) ^ (r - 1)) * (Nat.choose (2 * k + 2 * r) r : ℝ) *
          (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r) : ℝ)) =
      -(2 * (k : ℝ) + 2 * r + 1) * ((-1 : ℝ) ^ (r - 1)) *
        (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r) : ℝ) *
        ((r : ℝ) * (2 * (k : ℝ) + r) *
          (Nat.choose (2 * k + 2 * r) r : ℝ)) := by ring
    _ = -(2 * (k : ℝ) + 2 * r + 1) * ((-1 : ℝ) ^ (r - 1)) *
        (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r) : ℝ) *
        ((2 * (k : ℝ) + 2 * r - 1) * (2 * (k : ℝ) + 2 * r) *
          (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ)) := by rw [hleft]
    _ = -((-1 : ℝ) ^ (r - 1)) * (2 * (k : ℝ) + 2 * r - 1) *
        (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) *
        ((2 * (k : ℝ) + 2 * r) * (2 * (k : ℝ) + 2 * r + 1) *
          (Nat.choose (2 * k + 2 * s + r + 1) (2 * s - r) : ℝ)) := by ring
    _ = -((-1 : ℝ) ^ (r - 1)) * (2 * (k : ℝ) + 2 * r - 1) *
        (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) *
        ((2 * (k : ℝ) + 2 * s + r + 1) * ((((2 * s - r : ℕ) : ℝ)) + 1) *
          (Nat.choose (2 * k + 2 * s + r) (2 * s - r + 1) : ℝ)) := by rw [hright]
    _ = ((r : ℝ) - 1 - 2 * s) * (2 * (k : ℝ) + 2 * s + r + 1) *
        (2 * (k : ℝ) + 2 * r - 1) *
        (((-1 : ℝ) ^ (r - 1)) *
          (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) *
          (Nat.choose (2 * k + 2 * s + r) (2 * s - r + 1) : ℝ)) := by
          have hcast : ((((2 * s - r : ℕ) : ℝ)) + 1) = 2 * (s : ℝ) - r + 1 := by
            rw [Nat.cast_sub (R := ℝ) hrs]
            push_cast
            ring
          rw [hcast]
          ring

lemma deBrangesInitialTerm_eq_normalized_even {k s r : ℕ} (hr : r ≤ 2 * s) :
    deBrangesInitialTerm k (2 * s) r =
      (Nat.choose (2 * k + 2 * s + 1) (2 * s) : ℝ) *
        deBrangesNormalizedCoeff k (2 * s) r := by
  induction r with
  | zero =>
      simp [deBrangesInitialTerm]
  | succ r ih =>
      have hrec := deBrangesInitialTerm_recurrence_even
        (k := k) (s := s) (r := r + 1) (by omega) hr
      have htarget := deBrangesNormalizedCoeff_recurrence
        (k := k) (s := s) (r := r + 1) (by omega)
      rw [show r + 1 - 1 = r by omega, ih (by omega)] at hrec
      rw [show r + 1 - 1 = r by omega] at htarget
      have hscaled :
          deBrangesRecurrenceDen k (r + 1) *
              ((Nat.choose (2 * k + 2 * s + 1) (2 * s) : ℝ) *
                deBrangesNormalizedCoeff k (2 * s) (r + 1)) =
            deBrangesRecurrenceNum k s (r + 1) *
              ((Nat.choose (2 * k + 2 * s + 1) (2 * s) : ℝ) *
                deBrangesNormalizedCoeff k (2 * s) r) := by
        linear_combination
          (Nat.choose (2 * k + 2 * s + 1) (2 * s) : ℝ) * htarget
      have hden : deBrangesRecurrenceDen k (r + 1) ≠ 0 := by
        unfold deBrangesRecurrenceDen
        positivity
      apply mul_left_cancel₀ hden
      exact hrec.trans hscaled.symm

lemma deBrangesInitialTerm_eq_gasperEvenCoeff {k s r : ℕ} (hr : r ≤ 2 * s) :
    deBrangesInitialTerm k (2 * s) r =
      (Nat.choose (2 * k + 2 * s + 1) (2 * s) : ℝ) * gasperEvenCoeff k s r := by
  rw [deBrangesInitialTerm_eq_normalized_even hr,
    gasperEvenCoeff_eq_normalized hr]

noncomputable def gasperSquarePoly (k s j extra : ℕ) : Polynomial ℝ :=
  ∑ q ∈ range (s - j + 1), Polynomial.monomial q (gasperSquareCoeff k s j extra q)

lemma coeff_gasperSquarePoly (k s j extra n : ℕ) :
    (gasperSquarePoly k s j extra).coeff n = gasperSquareCoeff k s j extra n := by
  rw [gasperSquarePoly, Polynomial.finsetSum_coeff]
  by_cases hn : n ∈ range (s - j + 1)
  · simp [Polynomial.coeff_monomial, hn]
  · have hnlt : s - j < n := by
      simpa only [mem_range, Nat.lt_add_one_iff, not_le] using hn
    simp [Polynomial.coeff_monomial, hn, gasperSquareCoeff_eq_zero hnlt]

lemma coe_gasperSquarePoly (k s j extra : ℕ) :
    ((gasperSquarePoly k s j extra : Polynomial ℝ) : PowerSeries ℝ) =
      gasperSquareSeries k s j extra := by
  ext n
  simpa [gasperSquareSeries] using coeff_gasperSquarePoly k s j extra n

lemma eval_gasperSquarePoly (k s j extra : ℕ) (x : ℝ) :
    (gasperSquarePoly k s j extra).eval x = gasperSquarePolynomial k s j extra x := by
  rw [gasperSquarePoly, Polynomial.eval_finsetSum]
  simp [gasperSquarePolynomial]

lemma coeff_gasperSquarePoly_sq_even {k s j : ℕ} (hj : j ≤ s) (n : ℕ) :
    ((gasperSquarePoly k s j 0) ^ 2).coeff n = gasperEvenInnerCoeff k s j n := by
  have hseries := gasperEvenSquareSeries_sq_eq_clausen k s j hj
  calc
    ((gasperSquarePoly k s j 0) ^ 2).coeff n =
        PowerSeries.coeff n
          (((gasperSquarePoly k s j 0) ^ 2 : Polynomial ℝ) : PowerSeries ℝ) :=
            (Polynomial.coeff_coe
              (φ := (gasperSquarePoly k s j 0) ^ 2) n).symm
    _ =
        PowerSeries.coeff n
          (((gasperSquarePoly k s j 0 : Polynomial ℝ) : PowerSeries ℝ) ^ 2) := by
            exact congrArg (PowerSeries.coeff (R := ℝ) n)
              (Polynomial.coe_pow (φ := gasperSquarePoly k s j 0) 2)
    _ = PowerSeries.coeff n (gasperSquareSeries k s j 0 ^ 2) := by
          rw [coe_gasperSquarePoly]
    _ = PowerSeries.coeff n
          (clausenRecSeries (-((s - j : ℕ) : ℝ))
            ((k + s + 1 + j : ℕ) : ℝ)
            (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2)) := by
          rw [hseries]
    _ = gasperEvenInnerCoeff k s j n := by
          rw [coeff_clausenRecSeries]
          rfl

noncomputable def gasperEvenSumPoly (k s : ℕ) : Polynomial ℝ :=
  ∑ j ∈ range (s + 1),
    Polynomial.C (gasperWeight k (2 * s) j) *
      (Polynomial.X ^ (2 * j) * (gasperSquarePoly k s j 0) ^ 2)

lemma eval_gasperEvenSumPoly (k s : ℕ) (x : ℝ) :
    (gasperEvenSumPoly k s).eval x = gasperEvenSquareSum k s x := by
  rw [gasperEvenSumPoly, Polynomial.eval_finsetSum, gasperEvenSquareSum]
  apply sum_congr rfl
  intro j hj
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X, eval_gasperSquarePoly]
  ring

lemma coeff_gasperEvenSumPoly_term {k s j : ℕ} (hj : j ≤ s) (r : ℕ) :
    (Polynomial.C (gasperWeight k (2 * s) j) *
        (Polynomial.X ^ (2 * j) * (gasperSquarePoly k s j 0) ^ 2)).coeff r =
      if 2 * j ≤ r then gasperEvenRecurrenceTerm k s r j else 0 := by
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hjr : 2 * j ≤ r
  · rw [if_pos hjr, if_pos hjr, coeff_gasperSquarePoly_sq_even hj]
    rfl
  · rw [if_neg hjr, if_neg hjr]
    simp

lemma coeff_gasperEvenSumPoly {k s r : ℕ} (hr : r ≤ 2 * s) :
    (gasperEvenSumPoly k s).coeff r = gasperEvenCoeff k s r := by
  rw [gasperEvenSumPoly, Polynomial.finsetSum_coeff, gasperEvenCoeff]
  have hhalf : r / 2 ≤ s := by omega
  rw [show s + 1 = (r / 2 + 1) + (s - r / 2) by omega, sum_range_add]
  have hprefix :
      (∑ j ∈ range (r / 2 + 1),
        (Polynomial.C (gasperWeight k (2 * s) j) *
          (Polynomial.X ^ (2 * j) * (gasperSquarePoly k s j 0) ^ 2)).coeff r) =
        ∑ j ∈ range (r / 2 + 1), gasperEvenRecurrenceTerm k s r j := by
    apply sum_congr rfl
    intro j hj
    have hjhalf : j ≤ r / 2 := Nat.le_of_lt_succ (mem_range.mp hj)
    have hjs : j ≤ s := hjhalf.trans hhalf
    rw [coeff_gasperEvenSumPoly_term hjs, if_pos (by omega)]
  rw [hprefix]
  have hsuffix :
      (∑ j ∈ range (s - r / 2),
        (Polynomial.C (gasperWeight k (2 * s) (r / 2 + 1 + j)) *
          (Polynomial.X ^ (2 * (r / 2 + 1 + j)) *
            (gasperSquarePoly k s (r / 2 + 1 + j) 0) ^ 2)).coeff r) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hjs : r / 2 + 1 + j ≤ s := by
      have hjlt := mem_range.mp hj
      omega
    rw [coeff_gasperEvenSumPoly_term hjs, if_neg (by omega)]
  rw [hsuffix, add_zero]

lemma natDegree_gasperSquarePoly_le (k s j extra : ℕ) :
    (gasperSquarePoly k s j extra).natDegree ≤ s - j := by
  rw [gasperSquarePoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro q hq
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.le_of_lt_succ (mem_range.mp hq))

lemma natDegree_gasperEvenSumPoly_le (k s : ℕ) :
    (gasperEvenSumPoly k s).natDegree ≤ 2 * s := by
  rw [gasperEvenSumPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjs : j ≤ s := Nat.le_of_lt_succ (mem_range.mp hj)
  calc
    (Polynomial.C (gasperWeight k (2 * s) j) *
        (Polynomial.X ^ (2 * j) * (gasperSquarePoly k s j 0) ^ 2)).natDegree ≤
        (Polynomial.X ^ (2 * j) * (gasperSquarePoly k s j 0) ^ 2).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ 2 * j + 2 * (s - j) :=
      Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_X_pow_le (2 * j))
        (Polynomial.natDegree_pow_le_of_le 2 (natDegree_gasperSquarePoly_le k s j 0))
    _ = 2 * s := by omega

noncomputable def deBrangesPoly (k m : ℕ) : Polynomial ℝ :=
  ∑ r ∈ range (m + 1), Polynomial.monomial r (deBrangesInitialTerm k m r)

lemma coeff_deBrangesPoly (k m r : ℕ) :
    (deBrangesPoly k m).coeff r = deBrangesInitialTerm k m r := by
  rw [deBrangesPoly, Polynomial.finsetSum_coeff]
  by_cases hr : r ∈ range (m + 1)
  · simp [Polynomial.coeff_monomial, hr]
  · have hmr : m < r := by
      simpa only [mem_range, Nat.lt_add_one_iff, not_le] using hr
    simp [Polynomial.coeff_monomial, hr, deBrangesInitialTerm, show ¬r ≤ m by omega]

lemma eval_deBrangesPoly (k m : ℕ) (x : ℝ) :
    (deBrangesPoly k m).eval x = deBrangesPolynomial k m x := by
  rw [deBrangesPoly, Polynomial.eval_finsetSum]
  simp [deBrangesPolynomial]

lemma natDegree_deBrangesPoly_le (k m : ℕ) :
    (deBrangesPoly k m).natDegree ≤ m := by
  rw [deBrangesPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro r hr
  exact (Polynomial.natDegree_monomial_le _).trans
    (Nat.le_of_lt_succ (mem_range.mp hr))

lemma deBrangesPoly_eq_evenGasper (k s : ℕ) :
    deBrangesPoly k (2 * s) =
      Polynomial.C (Nat.choose (2 * k + 2 * s + 1) (2 * s) : ℝ) *
        gasperEvenSumPoly k s := by
  ext r
  by_cases hr : r ≤ 2 * s
  · rw [coeff_deBrangesPoly, Polynomial.coeff_C_mul,
      coeff_gasperEvenSumPoly hr, deBrangesInitialTerm_eq_gasperEvenCoeff hr]
  · have hrs : 2 * s < r := lt_of_not_ge hr
    rw [Polynomial.coeff_C_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_deBrangesPoly_le k (2 * s)).trans_lt hrs),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_gasperEvenSumPoly_le k s).trans_lt hrs), mul_zero]

lemma satisfiesEvenGasperIdentity (k s : ℕ) :
    SatisfiesEvenGasperIdentity k s := by
  intro x
  have hpoly := congrArg (Polynomial.eval x) (deBrangesPoly_eq_evenGasper k s)
  simpa [eval_deBrangesPoly, eval_gasperEvenSumPoly] using hpoly

noncomputable def gasperOddA (k s j : ℕ) : ℝ :=
  ((k + s + 1 + j : ℕ) : ℝ) + 1 / 2

noncomputable def gasperOddB (s j : ℕ) : ℝ :=
  -((s - j : ℕ) : ℝ) - 1 / 2

noncomputable def gasperOddC (k j : ℕ) : ℝ :=
  ((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2

lemma gasperOddSquareSeries_mul_eq_clausen (k s j : ℕ) (hj : j ≤ s) :
    (1 - PowerSeries.X) * gasperSquareSeries k s j 1 ^ 2 =
      clausenRecSeries (gasperOddA k s j) (gasperOddB s j) (gasperOddC k j) := by
  rw [gasperSquareSeries_eq_gaussRecSeries, pow_two]
  have h := gaussRecOddSquareSeries_eq_clausenRecSeries
    (a := -((s - j : ℕ) : ℝ))
    (b := ((k + s + 2 + j : ℕ) : ℝ))
    (c := ((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2)
    (by
      rw [Nat.cast_sub (R := ℝ) hj]
      push_cast
      ring)
    (by intro q; positivity)
    (by
      intro q
      rw [Nat.cast_sub (R := ℝ) hj]
      push_cast
      ring_nf
      positivity)
  change gaussRecOddSquareSeries
      (-((s - j : ℕ) : ℝ)) ((k + s + 2 + j : ℕ) : ℝ)
        (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) = _
  convert h using 1
  all_goals simp only [gasperOddA, gasperOddB, gasperOddC]
  all_goals rw [Nat.cast_sub (R := ℝ) hj]
  all_goals push_cast
  all_goals ring_nf

noncomputable def gasperOddInnerCoeff (k s j n : ℕ) : ℝ :=
  clausenRecCoeff (gasperOddA k s j) (gasperOddB s j) (gasperOddC k j) n

set_option maxRecDepth 10000 in
lemma gasperOddInnerCoeff_shift_two {k s j : ℕ} (hj : j < s) (n : ℕ) :
    gasperOddInnerCoeff k s (j + 1) n *
        ((-2 * ((s - j : ℕ) : ℝ) - 1) * (-2 * ((s - j : ℕ) : ℝ)) *
          ((2 * k + 2 * s + 2 * j + 3 : ℕ) : ℝ) *
          ((2 * k + 2 * s + 2 * j + 4 : ℕ) : ℝ) *
          ((k + 1 + 2 * j : ℕ) : ℝ) * ((k + 2 + 2 * j : ℕ) : ℝ)) *
        (((2 * k + 2 + 4 * j : ℕ) : ℝ) + (n + 2)) *
          (((2 * k + 2 + 4 * j : ℕ) : ℝ) + (n + 3)) =
      gasperOddInnerCoeff k s j (n + 2) *
        (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
          (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) *
          ((((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) + 1) *
          ((2 * k + 2 + 4 * j : ℕ) : ℝ) *
          (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 1) *
          (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 2) *
          (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 3)) := by
  have hden (q : ℕ) :
      2 * (gasperOddA k s j + gasperOddB s j) + q ≠ 0 ∧
        gasperOddC k j + q ≠ 0 := by
    constructor
    · simp only [gasperOddA, gasperOddB]
      rw [Nat.cast_sub (R := ℝ) hj.le]
      push_cast
      ring_nf
      positivity
    · simp only [gasperOddC]
      positivity
  have h := clausenRecCoeff_shift_two
    (a := gasperOddA k s j) (b := gasperOddB s j)
    (c := gasperOddC k j) n hden
  rw [gasperOddInnerCoeff, gasperOddInnerCoeff]
  simp only [gasperOddA, gasperOddB, gasperOddC] at h ⊢
  rw [Nat.cast_sub (R := ℝ) hj.le] at h ⊢
  rw [Nat.cast_sub (R := ℝ) (by omega : j + 1 ≤ s)]
  push_cast at h ⊢
  convert h using 1
  all_goals ring_nf

lemma gasperWeightRatio_odd {k s j : ℕ} (hj : j < s) :
    gasperWeightRatio k (2 * s + 1) j =
      ((2 * ((s - j : ℕ) : ℝ) + 1) * (2 * ((s - j : ℕ) : ℝ)) *
        ((2 * k + 2 * s + 2 * j + 3 : ℕ) : ℝ) *
        ((2 * k + 2 * s + 2 * j + 4 : ℕ) : ℝ) *
        ((2 * k + 2 * j + 1 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) /
      (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
        ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
        ((2 * k + 4 * j + 3 : ℕ) : ℝ) ^ 2 *
        ((2 * k + 4 * j + 5 : ℕ) : ℝ)) := by
  unfold gasperWeightRatio
  rw [show 2 * s + 1 - 2 * j = 2 * (s - j) + 1 by omega,
    show 2 * s + 1 - (2 * j + 1) = 2 * (s - j) by omega]
  push_cast
  congr 1
  all_goals ring

set_option maxRecDepth 10000 in
lemma gasperOddAdjacentTerm {k s j : ℕ} (hj : j < s) (n : ℕ) :
    gasperWeight k (2 * s + 1) (j + 1) * gasperOddInnerCoeff k s (j + 1) n *
        (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
          ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
          ((2 * k + 4 * j + n + 4 : ℕ) : ℝ) *
          ((2 * k + 4 * j + n + 5 : ℕ) : ℝ)) =
      gasperWeight k (2 * s + 1) j * gasperOddInnerCoeff k s j (n + 2) *
        (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
          ((2 * k + 2 * j + 1 : ℕ) : ℝ) *
          ((2 * k + 4 * j + 5 : ℕ) : ℝ) *
          ((2 * j + 1 : ℕ) : ℝ)) := by
  have hshift := gasperOddInnerCoeff_shift_two (k := k) hj n
  rw [gasperWeight, gasperWeightRatio_odd hj]
  have hcancel :
      (((2 * k + 4 * j + 2 : ℕ) : ℝ) *
        ((2 * k + 4 * j + 4 : ℕ) : ℝ)) ≠ 0 := by positivity
  apply mul_left_cancel₀ hcancel
  let F : ℝ :=
    4 * gasperWeight k (2 * s + 1) j * ((2 * k + 2 * j + 1 : ℕ) : ℝ) *
      ((2 * j + 1 : ℕ) : ℝ) /
        (((2 * k + 4 * j + 3 : ℕ) : ℝ) ^ 2 *
          ((2 * k + 4 * j + 5 : ℕ) : ℝ))
  calc
    (((2 * k + 4 * j + 2 : ℕ) : ℝ) * ((2 * k + 4 * j + 4 : ℕ) : ℝ)) *
          (gasperWeight k (2 * s + 1) j *
            (((2 * ((s - j : ℕ) : ℝ) + 1) * (2 * ((s - j : ℕ) : ℝ)) *
              ((2 * k + 2 * s + 2 * j + 3 : ℕ) : ℝ) *
              ((2 * k + 2 * s + 2 * j + 4 : ℕ) : ℝ) *
              ((2 * k + 2 * j + 1 : ℕ) : ℝ) * ((2 * j + 1 : ℕ) : ℝ)) /
              (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
                ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
                ((2 * k + 4 * j + 3 : ℕ) : ℝ) ^ 2 *
                ((2 * k + 4 * j + 5 : ℕ) : ℝ))) *
            gasperOddInnerCoeff k s (j + 1) n *
            (((2 * j + 2 : ℕ) : ℝ) * ((2 * k + 2 * j + 2 : ℕ) : ℝ) *
              ((2 * k + 4 * j + 1 : ℕ) : ℝ) *
              ((2 * k + 4 * j + n + 4 : ℕ) : ℝ) *
              ((2 * k + 4 * j + n + 5 : ℕ) : ℝ))) =
        F *
          (gasperOddInnerCoeff k s (j + 1) n *
            ((-2 * ((s - j : ℕ) : ℝ) - 1) * (-2 * ((s - j : ℕ) : ℝ)) *
              ((2 * k + 2 * s + 2 * j + 3 : ℕ) : ℝ) *
              ((2 * k + 2 * s + 2 * j + 4 : ℕ) : ℝ) *
              ((k + 1 + 2 * j : ℕ) : ℝ) * ((k + 2 + 2 * j : ℕ) : ℝ)) *
            (((2 * k + 2 + 4 * j : ℕ) : ℝ) + (n + 2)) *
              (((2 * k + 2 + 4 * j : ℕ) : ℝ) + (n + 3))) := by
        dsimp only [F]
        push_cast
        field_simp
        ring
    _ = F *
          (gasperOddInnerCoeff k s j (n + 2) *
            (((n + 2 : ℕ) : ℝ) * ((n + 1 : ℕ) : ℝ) *
              (((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) *
              ((((2 * k + 3 + 4 * j : ℕ) : ℝ) / 2) + 1) *
              ((2 * k + 2 + 4 * j : ℕ) : ℝ) *
              (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 1) *
              (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 2) *
              (((2 * k + 2 + 4 * j : ℕ) : ℝ) + 3))) := by rw [hshift]
    _ = (((2 * k + 4 * j + 2 : ℕ) : ℝ) *
          ((2 * k + 4 * j + 4 : ℕ) : ℝ)) *
        (gasperWeight k (2 * s + 1) j * gasperOddInnerCoeff k s j (n + 2) *
          (((n + 1 : ℕ) : ℝ) * ((n + 2 : ℕ) : ℝ) *
            ((2 * k + 2 * j + 1 : ℕ) : ℝ) *
            ((2 * k + 4 * j + 5 : ℕ) : ℝ) *
            ((2 * j + 1 : ℕ) : ℝ))) := by
        dsimp only [F]
        push_cast
        field_simp
        ring

noncomputable def gasperOddRecurrenceTerm (k s r j : ℕ) : ℝ :=
  gasperWeight k (2 * s + 1) j * gasperOddInnerCoeff k s j (r - 2 * j)

lemma gasperOddRecurrenceTerm_telescope {k s r j : ℕ}
    (hj : j < s) (hr : 2 * (j + 1) ≤ r) :
    gasperEvenResidualCoeff k r j * gasperOddRecurrenceTerm k s r j =
      gasperEvenTelescoper k r (j + 1) *
          gasperOddRecurrenceTerm k s r (j + 1) -
        gasperEvenTelescoper k r j * gasperOddRecurrenceTerm k s r j := by
  have hadj := gasperOddAdjacentTerm (k := k) (s := s) hj (r - 2 * (j + 1))
  have hsub0 : r - 2 * (j + 1) + 2 = r - 2 * j := by omega
  have hsub1 : r - 2 * (j + 1) + 1 = r - 2 * j - 1 := by omega
  have hindex4 :
      2 * k + 4 * j + (r - 2 * (j + 1)) + 4 = 2 * k + r + 2 * j + 2 := by omega
  have hindex5 :
      2 * k + 4 * j + (r - 2 * (j + 1)) + 5 = 2 * k + r + 2 * j + 3 := by omega
  rw [hsub0, hsub1, hindex4, hindex5] at hadj
  simp only [gasperEvenResidualCoeff, gasperOddRecurrenceTerm,
    gasperEvenTelescoper]
  have hden : 2 * (k : ℝ) + 4 * j + 1 ≠ 0 := by positivity
  have hden' : 2 * (k : ℝ) + 4 * j + 5 ≠ 0 := by positivity
  have hadj' :
      (gasperWeight k (2 * s + 1) (j + 1) *
          gasperOddInnerCoeff k s (j + 1) (r - 2 * (j + 1))) *
          ((2 * (j : ℝ) + 2) * (2 * (k : ℝ) + 2 * j + 2) *
            (2 * (k : ℝ) + 4 * j + 1) *
            (2 * (k : ℝ) + r + 2 * j + 2) *
            (2 * (k : ℝ) + r + 2 * j + 3)) =
        (gasperWeight k (2 * s + 1) j *
          gasperOddInnerCoeff k s j (r - 2 * j)) *
          (((r : ℝ) - 2 * j - 1) * ((r : ℝ) - 2 * j) *
            (2 * (k : ℝ) + 2 * j + 1) *
            (2 * (k : ℝ) + 4 * j + 5) * (2 * (j : ℝ) + 1)) := by
    rw [Nat.cast_sub (by omega : 1 ≤ r - 2 * j),
      Nat.cast_sub (by omega : 2 * j ≤ r)] at hadj
    push_cast at hadj ⊢
    exact hadj
  convert gasperEven_telescope_algebra
      (K := 2 * (k : ℝ)) (R := (r : ℝ)) (J := (j : ℝ))
      (T := gasperWeight k (2 * s + 1) j *
        gasperOddInnerCoeff k s j (r - 2 * j))
      (U := gasperWeight k (2 * s + 1) (j + 1) *
        gasperOddInnerCoeff k s (j + 1) (r - 2 * (j + 1)))
      hden hden' hadj' using 1
  all_goals push_cast
  all_goals ring

lemma gasperOdd_boundary_even (k s q : ℕ) :
    gasperEvenResidualCoeff k (2 * q) q *
        gasperOddRecurrenceTerm k s (2 * q) q =
      -gasperEvenTelescoper k (2 * q) q *
        gasperOddRecurrenceTerm k s (2 * q) q := by
  have hden : 2 * (k : ℝ) + 4 * q + 1 ≠ 0 := by positivity
  simp only [gasperEvenResidualCoeff, gasperEvenTelescoper]
  field_simp [hden]
  push_cast
  ring

lemma gasperOdd_boundary_odd (k s q : ℕ) :
    gasperEvenResidualCoeff k (2 * q + 1) q *
        gasperOddRecurrenceTerm k s (2 * q + 1) q =
      -gasperEvenTelescoper k (2 * q + 1) q *
        gasperOddRecurrenceTerm k s (2 * q + 1) q := by
  have hden : 2 * (k : ℝ) + 4 * q + 1 ≠ 0 := by positivity
  simp only [gasperEvenResidualCoeff, gasperEvenTelescoper]
  field_simp [hden]
  push_cast
  ring

lemma sum_gasperOddResidual_even {k s q : ℕ} (hq : q ≤ s) :
    (∑ j ∈ range (q + 1),
      gasperEvenResidualCoeff k (2 * q) j *
        gasperOddRecurrenceTerm k s (2 * q) j) = 0 := by
  rw [sum_range_succ]
  have hprefix :
      (∑ j ∈ range q,
        gasperEvenResidualCoeff k (2 * q) j *
          gasperOddRecurrenceTerm k s (2 * q) j) =
        ∑ j ∈ range q,
          (gasperEvenTelescoper k (2 * q) (j + 1) *
              gasperOddRecurrenceTerm k s (2 * q) (j + 1) -
            gasperEvenTelescoper k (2 * q) j *
              gasperOddRecurrenceTerm k s (2 * q) j) := by
    apply sum_congr rfl
    intro j hj
    have hjq : j < q := mem_range.mp hj
    exact gasperOddRecurrenceTerm_telescope (by omega) (by omega)
  rw [hprefix, sum_range_forward_sub
    (fun j => gasperEvenTelescoper k (2 * q) j *
      gasperOddRecurrenceTerm k s (2 * q) j) q]
  rw [gasperEvenTelescoper_zero, zero_mul, sub_zero,
    gasperOdd_boundary_even]
  ring

lemma sum_gasperOddResidual_odd {k s q : ℕ} (hq : q ≤ s) :
    (∑ j ∈ range (q + 1),
      gasperEvenResidualCoeff k (2 * q + 1) j *
        gasperOddRecurrenceTerm k s (2 * q + 1) j) = 0 := by
  rw [sum_range_succ]
  have hprefix :
      (∑ j ∈ range q,
        gasperEvenResidualCoeff k (2 * q + 1) j *
          gasperOddRecurrenceTerm k s (2 * q + 1) j) =
        ∑ j ∈ range q,
          (gasperEvenTelescoper k (2 * q + 1) (j + 1) *
              gasperOddRecurrenceTerm k s (2 * q + 1) (j + 1) -
            gasperEvenTelescoper k (2 * q + 1) j *
              gasperOddRecurrenceTerm k s (2 * q + 1) j) := by
    apply sum_congr rfl
    intro j hj
    have hjq : j < q := mem_range.mp hj
    exact gasperOddRecurrenceTerm_telescope (by omega) (by omega)
  rw [hprefix, sum_range_forward_sub
    (fun j => gasperEvenTelescoper k (2 * q + 1) j *
      gasperOddRecurrenceTerm k s (2 * q + 1) j) q]
  rw [gasperEvenTelescoper_zero, zero_mul, sub_zero,
    gasperOdd_boundary_odd]
  ring

noncomputable def gasperOddCoeff (k s r : ℕ) : ℝ :=
  ∑ j ∈ range (r / 2 + 1), gasperOddRecurrenceTerm k s r j

noncomputable def deBrangesOddRecurrenceNum (k s r : ℕ) : ℝ :=
  ((r : ℝ) - 2 * s - 2) * (2 * (k : ℝ) + 2 * s + r + 2) *
    (2 * (k : ℝ) + 2 * r - 1)

lemma gasperOddInnerRecurrence {k s r j : ℕ}
    (hjs : j ≤ s) (hjr : 2 * j < r) :
    gasperOddRecurrenceTerm k s r j *
        (((r : ℝ) - 2 * j) * (2 * (k : ℝ) + r + 2 * j + 1) *
          (2 * (k : ℝ) + 2 * r + 1)) =
      gasperOddRecurrenceTerm k s (r - 1) j *
        (((r : ℝ) - 2 * s - 2) * (2 * (k : ℝ) + 2 * s + r + 2) *
          (2 * (k : ℝ) + 2 * r)) := by
  have hrec := clausenRecCoeff_succ
    (a := gasperOddA k s j) (b := gasperOddB s j) (c := gasperOddC k j)
    (n := r - 1 - 2 * j)
    (by
      simp only [gasperOddA, gasperOddB]
      rw [Nat.cast_sub (R := ℝ) hjs]
      push_cast
      ring_nf
      positivity)
    (by simp only [gasperOddC]; positivity)
  have hnext : r - 1 - 2 * j + 1 = r - 2 * j := by omega
  rw [hnext] at hrec
  rw [gasperOddRecurrenceTerm, gasperOddRecurrenceTerm,
    gasperOddInnerCoeff, gasperOddInnerCoeff]
  rw [show r - 1 - 2 * j = (r - 1) - 2 * j by omega]
  simp only [gasperOddA, gasperOddB, gasperOddC] at hrec ⊢
  rw [Nat.cast_sub (R := ℝ) hjs] at hrec
  rw [Nat.cast_sub (R := ℝ) (by omega : 2 * j ≤ r)] at hrec
  rw [Nat.cast_sub (R := ℝ) (by omega : 2 * j ≤ r - 1)] at hrec
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ r)] at hrec
  rw [Nat.cast_sub (R := ℝ) hjs]
  push_cast at hrec ⊢
  have hscaled := congrArg
    (fun x : ℝ => 2 * gasperWeight k (2 * s + 1) j * x) hrec
  convert hscaled using 1
  all_goals ring_nf

lemma gasperOddTargetTermRecurrence {k s r j : ℕ}
    (hjs : j ≤ s) (hjr : 2 * j < r) :
    (2 * (k : ℝ) + 2 * r) *
        (deBrangesRecurrenceDen k r * gasperOddRecurrenceTerm k s r j -
          deBrangesOddRecurrenceNum k s r *
            gasperOddRecurrenceTerm k s (r - 1) j) =
      (2 * (k : ℝ) + 2 * r + 1) * gasperEvenResidualCoeff k r j *
        gasperOddRecurrenceTerm k s r j := by
  have hinner := gasperOddInnerRecurrence (k := k) (s := s) hjs hjr
  simp only [deBrangesRecurrenceDen, deBrangesOddRecurrenceNum,
    gasperEvenResidualCoeff]
  linear_combination
    (2 * (k : ℝ) + 2 * r - 1) * hinner

lemma gasperOddCoeff_even (k s q : ℕ) :
    gasperOddCoeff k s (2 * q) =
      ∑ j ∈ range (q + 1), gasperOddRecurrenceTerm k s (2 * q) j := by
  rw [gasperOddCoeff]
  congr 2
  omega

lemma gasperOddCoeff_odd (k s q : ℕ) :
    gasperOddCoeff k s (2 * q + 1) =
      ∑ j ∈ range (q + 1), gasperOddRecurrenceTerm k s (2 * q + 1) j := by
  rw [gasperOddCoeff]
  congr 2
  omega

lemma gasperOddCoeff_recurrence_odd {k s q : ℕ} (hq : q ≤ s) :
    deBrangesRecurrenceDen k (2 * q + 1) * gasperOddCoeff k s (2 * q + 1) =
      deBrangesOddRecurrenceNum k s (2 * q + 1) * gasperOddCoeff k s (2 * q) := by
  rw [gasperOddCoeff_odd, gasperOddCoeff_even]
  let F : ℝ := 2 * (k : ℝ) + 2 * (2 * q + 1)
  let G : ℝ := 2 * (k : ℝ) + 2 * (2 * q + 1) + 1
  have hsum :
      F *
          (deBrangesRecurrenceDen k (2 * q + 1) *
              (∑ j ∈ range (q + 1), gasperOddRecurrenceTerm k s (2 * q + 1) j) -
            deBrangesOddRecurrenceNum k s (2 * q + 1) *
              (∑ j ∈ range (q + 1), gasperOddRecurrenceTerm k s (2 * q) j)) =
        G *
          ∑ j ∈ range (q + 1),
            gasperEvenResidualCoeff k (2 * q + 1) j *
              gasperOddRecurrenceTerm k s (2 * q + 1) j := by
    calc
      _ = ∑ j ∈ range (q + 1),
          F *
            (deBrangesRecurrenceDen k (2 * q + 1) *
                gasperOddRecurrenceTerm k s (2 * q + 1) j -
              deBrangesOddRecurrenceNum k s (2 * q + 1) *
                gasperOddRecurrenceTerm k s (2 * q) j) := by
          rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib,
            Finset.mul_sum]
      _ = ∑ j ∈ range (q + 1),
          G * gasperEvenResidualCoeff k (2 * q + 1) j *
            gasperOddRecurrenceTerm k s (2 * q + 1) j := by
          apply sum_congr rfl
          intro j hj
          have hjq : j ≤ q := Nat.le_of_lt_succ (mem_range.mp hj)
          simpa [F, G] using gasperOddTargetTermRecurrence
            (k := k) (s := s) (r := 2 * q + 1) (j := j) (by omega) (by omega)
      _ = _ := by
        rw [Finset.mul_sum]
        apply sum_congr rfl
        intro j hj
        ring
  rw [sum_gasperOddResidual_odd hq, mul_zero] at hsum
  have hF : F ≠ 0 := by
    dsimp only [F]
    positivity
  have hzero :
      deBrangesRecurrenceDen k (2 * q + 1) *
          (∑ j ∈ range (q + 1), gasperOddRecurrenceTerm k s (2 * q + 1) j) -
        deBrangesOddRecurrenceNum k s (2 * q + 1) *
          (∑ j ∈ range (q + 1), gasperOddRecurrenceTerm k s (2 * q) j) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left hF
  linarith

lemma gasperOddTarget_boundary_even (k s q : ℕ) :
    (2 * (k : ℝ) + 2 * (2 * q)) *
        (deBrangesRecurrenceDen k (2 * q) *
          gasperOddRecurrenceTerm k s (2 * q) q) =
      (2 * (k : ℝ) + 2 * (2 * q) + 1) *
        gasperEvenResidualCoeff k (2 * q) q *
          gasperOddRecurrenceTerm k s (2 * q) q := by
  simp only [deBrangesRecurrenceDen, gasperEvenResidualCoeff]
  push_cast
  ring

lemma gasperOddCoeff_recurrence_even {k s p : ℕ} (hp : p + 1 ≤ s) :
    deBrangesRecurrenceDen k (2 * (p + 1)) *
        gasperOddCoeff k s (2 * (p + 1)) =
      deBrangesOddRecurrenceNum k s (2 * (p + 1)) *
        gasperOddCoeff k s (2 * p + 1) := by
  rw [gasperOddCoeff_even, gasperOddCoeff_odd]
  let R : ℕ := 2 * (p + 1)
  let F : ℝ := 2 * (k : ℝ) + 2 * R
  let G : ℝ := 2 * (k : ℝ) + 2 * R + 1
  have hsum :
      F *
          (deBrangesRecurrenceDen k R *
              ((∑ j ∈ range (p + 1), gasperOddRecurrenceTerm k s R j) +
                gasperOddRecurrenceTerm k s R (p + 1)) -
            deBrangesOddRecurrenceNum k s R *
              (∑ j ∈ range (p + 1),
                gasperOddRecurrenceTerm k s (2 * p + 1) j)) =
        G *
          ∑ j ∈ range (p + 2),
            gasperEvenResidualCoeff k R j *
              gasperOddRecurrenceTerm k s R j := by
    have hdist :
        (∑ j ∈ range (p + 1),
          F *
            (deBrangesRecurrenceDen k R * gasperOddRecurrenceTerm k s R j -
              deBrangesOddRecurrenceNum k s R *
                gasperOddRecurrenceTerm k s (2 * p + 1) j)) =
          F *
            (deBrangesRecurrenceDen k R *
                (∑ j ∈ range (p + 1), gasperOddRecurrenceTerm k s R j) -
              deBrangesOddRecurrenceNum k s R *
                (∑ j ∈ range (p + 1),
                  gasperOddRecurrenceTerm k s (2 * p + 1) j)) := by
      calc
        _ = F * ∑ j ∈ range (p + 1),
            (deBrangesRecurrenceDen k R * gasperOddRecurrenceTerm k s R j -
              deBrangesOddRecurrenceNum k s R *
                gasperOddRecurrenceTerm k s (2 * p + 1) j) := by
              rw [Finset.mul_sum]
        _ = F *
            ((∑ j ∈ range (p + 1),
                deBrangesRecurrenceDen k R * gasperOddRecurrenceTerm k s R j) -
              ∑ j ∈ range (p + 1),
                deBrangesOddRecurrenceNum k s R *
                  gasperOddRecurrenceTerm k s (2 * p + 1) j) := by
              rw [Finset.sum_sub_distrib]
        _ = _ := by rw [← Finset.mul_sum, ← Finset.mul_sum]
    calc
      _ =
          (∑ j ∈ range (p + 1),
            F *
              (deBrangesRecurrenceDen k R * gasperOddRecurrenceTerm k s R j -
                deBrangesOddRecurrenceNum k s R *
                  gasperOddRecurrenceTerm k s (2 * p + 1) j)) +
            F * deBrangesRecurrenceDen k R *
              gasperOddRecurrenceTerm k s R (p + 1) := by
          rw [hdist]
          ring
      _ =
          (∑ j ∈ range (p + 1),
            G * gasperEvenResidualCoeff k R j *
              gasperOddRecurrenceTerm k s R j) +
            G * gasperEvenResidualCoeff k R (p + 1) *
              gasperOddRecurrenceTerm k s R (p + 1) := by
          have hprefix :
              (∑ j ∈ range (p + 1),
                F *
                  (deBrangesRecurrenceDen k R * gasperOddRecurrenceTerm k s R j -
                    deBrangesOddRecurrenceNum k s R *
                      gasperOddRecurrenceTerm k s (2 * p + 1) j)) =
                ∑ j ∈ range (p + 1),
                  G * gasperEvenResidualCoeff k R j *
                    gasperOddRecurrenceTerm k s R j := by
            apply sum_congr rfl
            intro j hj
            have hjp : j ≤ p := Nat.le_of_lt_succ (mem_range.mp hj)
            have hterm := gasperOddTargetTermRecurrence
              (k := k) (s := s) (r := R) (j := j) (by omega) (by dsimp only [R]; omega)
            simpa [F, G, R, show R - 1 = 2 * p + 1 by dsimp only [R]; omega] using hterm
          have hboundary :
              F * deBrangesRecurrenceDen k R *
                  gasperOddRecurrenceTerm k s R (p + 1) =
                G * gasperEvenResidualCoeff k R (p + 1) *
                  gasperOddRecurrenceTerm k s R (p + 1) := by
            have hb := gasperOddTarget_boundary_even k s (p + 1)
            push_cast at hb
            dsimp only [F, G, R]
            push_cast
            ring_nf at hb ⊢
            exact hb
          calc
            _ = (∑ j ∈ range (p + 1),
                  G * gasperEvenResidualCoeff k R j *
                    gasperOddRecurrenceTerm k s R j) +
                F * deBrangesRecurrenceDen k R *
                  gasperOddRecurrenceTerm k s R (p + 1) := by rw [hprefix]
            _ = _ := by rw [hboundary]
      _ = _ := by
          conv_rhs =>
            rw [sum_range_succ, mul_add, Finset.mul_sum]
          ring_nf
  have hres := sum_gasperOddResidual_even (k := k) (s := s) (q := p + 1) hp
  change (∑ j ∈ range (p + 2),
    gasperEvenResidualCoeff k R j * gasperOddRecurrenceTerm k s R j) = 0 at hres
  rw [hres, mul_zero] at hsum
  have hF : F ≠ 0 := by
    dsimp only [F, R]
    positivity
  have hzero :
      deBrangesRecurrenceDen k R *
          ((∑ j ∈ range (p + 1), gasperOddRecurrenceTerm k s R j) +
            gasperOddRecurrenceTerm k s R (p + 1)) -
        deBrangesOddRecurrenceNum k s R *
          (∑ j ∈ range (p + 1),
            gasperOddRecurrenceTerm k s (2 * p + 1) j) = 0 :=
    (mul_eq_zero.mp hsum).resolve_left hF
  dsimp only [R] at hzero
  have hsplit :
      (∑ j ∈ range (p + 2),
        gasperOddRecurrenceTerm k s (2 * (p + 1)) j) =
        (∑ j ∈ range (p + 1),
          gasperOddRecurrenceTerm k s (2 * (p + 1)) j) +
          gasperOddRecurrenceTerm k s (2 * (p + 1)) (p + 1) := by
    rw [show p + 2 = (p + 1) + 1 by omega, sum_range_succ]
  rw [hsplit]
  linarith

lemma gasperOddCoeff_recurrence {k s r : ℕ} (hr : 0 < r) (hrs : r ≤ 2 * s + 1) :
    deBrangesRecurrenceDen k r * gasperOddCoeff k s r =
      deBrangesOddRecurrenceNum k s r * gasperOddCoeff k s (r - 1) := by
  rcases Nat.even_or_odd r with ⟨q, hq⟩ | ⟨q, hq⟩
  · subst r
    have hq0 : 0 < q := by omega
    obtain ⟨p, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hq0.ne'
    have hmain : p + 1 + (p + 1) = 2 * (p + 1) := by omega
    have hprev : 2 * (p + 1) - 1 = 2 * p + 1 := by omega
    rw [hmain, hprev]
    exact gasperOddCoeff_recurrence_even (k := k) (s := s) (p := p) (by omega)
  · subst r
    simpa [show 2 * q + 1 - 1 = 2 * q by omega] using
      gasperOddCoeff_recurrence_odd (k := k) (s := s) (q := q) (by omega)

@[simp]
lemma gasperOddCoeff_zero (k s : ℕ) : gasperOddCoeff k s 0 = 1 := by
  simp [gasperOddCoeff, gasperOddRecurrenceTerm, gasperWeight,
    gasperOddInnerCoeff, clausenRecCoeff]

noncomputable def deBrangesGeneralRecurrenceNum (k m r : ℕ) : ℝ :=
  ((r : ℝ) - m - 1) * (2 * (k : ℝ) + m + r + 1) *
    (2 * (k : ℝ) + 2 * r - 1)

lemma deBrangesNormalizedCoeff_recurrence_general {k m r : ℕ} (hr : 0 < r) :
    deBrangesRecurrenceDen k r * deBrangesNormalizedCoeff k m r =
      deBrangesGeneralRecurrenceNum k m r *
        deBrangesNormalizedCoeff k m (r - 1) := by
  have hrec := hypergeom3RecCoeff_succ
    (p := -((m : ℕ) : ℝ))
    (q := 2 * (k : ℝ) + m + 2)
    (r := (k : ℝ) + 1 / 2)
    (u := 2 * (k : ℝ) + 1)
    (v := (k : ℝ) + 3 / 2)
    (n := r - 1) (by positivity) (by positivity)
  have hnext : r - 1 + 1 = r := by omega
  rw [hnext] at hrec
  simp only [deBrangesNormalizedCoeff, deBrangesRecurrenceDen,
    deBrangesGeneralRecurrenceNum]
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ r)] at hrec
  push_cast at hrec ⊢
  linear_combination 2 * hrec

lemma deBrangesChooseRightStepGeneral (k m r : ℕ) (hrm : r ≤ m) :
    ((2 * k + 2 * r : ℕ) : ℝ) * ((2 * k + 2 * r + 1 : ℕ) : ℝ) *
        (Nat.choose (2 * k + m + r + 1) (m - r) : ℝ) =
      ((2 * k + m + r + 1 : ℕ) : ℝ) * ((m - r + 1 : ℕ) : ℝ) *
        (Nat.choose (2 * k + m + r) (m - r + 1) : ℝ) := by
  have htop := Nat.choose_mul_succ_eq (2 * k + m + r) (m - r + 1)
  have hright := Nat.choose_succ_right_eq (2 * k + m + r + 1) (m - r)
  have htopNat :
      Nat.choose (2 * k + m + r) (m - r + 1) * (2 * k + m + r + 1) =
        Nat.choose (2 * k + m + r + 1) (m - r + 1) *
          (2 * k + 2 * r) := by
    rw [show 2 * k + m + r + 1 - (m - r + 1) = 2 * k + 2 * r by omega]
      at htop
    exact htop
  have hrightNat :
      Nat.choose (2 * k + m + r + 1) (m - r + 1) * (m - r + 1) =
        Nat.choose (2 * k + m + r + 1) (m - r) *
          (2 * k + 2 * r + 1) := by
    rw [show 2 * k + m + r + 1 - (m - r) = 2 * k + 2 * r + 1 by omega]
      at hright
    exact hright
  have htop' :
      (Nat.choose (2 * k + m + r) (m - r + 1) : ℝ) *
          ((2 * k + m + r + 1 : ℕ) : ℝ) =
        (Nat.choose (2 * k + m + r + 1) (m - r + 1) : ℝ) *
          ((2 * k + 2 * r : ℕ) : ℝ) := by
    exact_mod_cast htopNat
  have hright' :
      (Nat.choose (2 * k + m + r + 1) (m - r + 1) : ℝ) *
          ((m - r + 1 : ℕ) : ℝ) =
        (Nat.choose (2 * k + m + r + 1) (m - r) : ℝ) *
          ((2 * k + 2 * r + 1 : ℕ) : ℝ) := by
    exact_mod_cast hrightNat
  calc
    ((2 * k + 2 * r : ℕ) : ℝ) * ((2 * k + 2 * r + 1 : ℕ) : ℝ) *
        (Nat.choose (2 * k + m + r + 1) (m - r) : ℝ) =
      ((2 * k + 2 * r : ℕ) : ℝ) *
        ((Nat.choose (2 * k + m + r + 1) (m - r + 1) : ℝ) *
          ((m - r + 1 : ℕ) : ℝ)) := by
        rw [hright']
        ring
    _ = ((m - r + 1 : ℕ) : ℝ) *
        ((Nat.choose (2 * k + m + r) (m - r + 1) : ℝ) *
          ((2 * k + m + r + 1 : ℕ) : ℝ)) := by
        rw [htop']
        ring
    _ = _ := by ring

lemma deBrangesInitialTerm_recurrence_general {k m r : ℕ}
    (hr0 : 0 < r) (hrm : r ≤ m) :
    deBrangesRecurrenceDen k r * deBrangesInitialTerm k m r =
      deBrangesGeneralRecurrenceNum k m r *
        deBrangesInitialTerm k m (r - 1) := by
  have hrprev : r - 1 ≤ m := by omega
  rw [deBrangesInitialTerm, if_pos hrm,
    deBrangesInitialTerm, if_pos hrprev]
  have hsign : (-1 : ℝ) ^ r = -((-1 : ℝ) ^ (r - 1)) := by
    calc
      (-1 : ℝ) ^ r = (-1 : ℝ) ^ ((r - 1) + 1) := by congr 1; omega
      _ = -((-1 : ℝ) ^ (r - 1)) := by rw [pow_succ]; ring
  rw [hsign]
  have hleft := deBrangesChooseLeftStep k r hr0
  have hright := deBrangesChooseRightStepGeneral k m r hrm
  simp only [deBrangesRecurrenceDen, deBrangesGeneralRecurrenceNum]
  simp only [show 2 * k + 2 * (r - 1) = 2 * k + 2 * r - 2 by omega,
    show 2 * k + m + (r - 1) + 1 = 2 * k + m + r by omega,
    show m - (r - 1) = m - r + 1 by omega]
  rw [Nat.cast_sub (R := ℝ) (by omega : 1 ≤ 2 * k + 2 * r)] at hleft
  push_cast at hleft hright ⊢
  calc
    (r : ℝ) * (2 * (k : ℝ) + r) * (2 * (k : ℝ) + 2 * r + 1) *
        (-((-1 : ℝ) ^ (r - 1)) * (Nat.choose (2 * k + 2 * r) r : ℝ) *
          (Nat.choose (2 * k + m + r + 1) (m - r) : ℝ)) =
      -(2 * (k : ℝ) + 2 * r + 1) * ((-1 : ℝ) ^ (r - 1)) *
        (Nat.choose (2 * k + m + r + 1) (m - r) : ℝ) *
        ((r : ℝ) * (2 * (k : ℝ) + r) *
          (Nat.choose (2 * k + 2 * r) r : ℝ)) := by ring
    _ = -(2 * (k : ℝ) + 2 * r + 1) * ((-1 : ℝ) ^ (r - 1)) *
        (Nat.choose (2 * k + m + r + 1) (m - r) : ℝ) *
        ((2 * (k : ℝ) + 2 * r - 1) * (2 * (k : ℝ) + 2 * r) *
          (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ)) := by rw [hleft]
    _ = -((-1 : ℝ) ^ (r - 1)) * (2 * (k : ℝ) + 2 * r - 1) *
        (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) *
        ((2 * (k : ℝ) + 2 * r) * (2 * (k : ℝ) + 2 * r + 1) *
          (Nat.choose (2 * k + m + r + 1) (m - r) : ℝ)) := by ring
    _ = -((-1 : ℝ) ^ (r - 1)) * (2 * (k : ℝ) + 2 * r - 1) *
        (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) *
        ((2 * (k : ℝ) + m + r + 1) * ((((m - r : ℕ) : ℝ)) + 1) *
          (Nat.choose (2 * k + m + r) (m - r + 1) : ℝ)) := by rw [hright]
    _ = ((r : ℝ) - m - 1) * (2 * (k : ℝ) + m + r + 1) *
        (2 * (k : ℝ) + 2 * r - 1) *
        (((-1 : ℝ) ^ (r - 1)) *
          (Nat.choose (2 * k + 2 * r - 2) (r - 1) : ℝ) *
          (Nat.choose (2 * k + m + r) (m - r + 1) : ℝ)) := by
          have hcast : ((((m - r : ℕ) : ℝ)) + 1) = (m : ℝ) - r + 1 := by
            rw [Nat.cast_sub (R := ℝ) hrm]
          rw [hcast]
          ring

lemma deBrangesInitialTerm_eq_normalized {k m r : ℕ} (hr : r ≤ m) :
    deBrangesInitialTerm k m r =
      (Nat.choose (2 * k + m + 1) m : ℝ) *
        deBrangesNormalizedCoeff k m r := by
  induction r with
  | zero =>
      simp [deBrangesInitialTerm]
  | succ r ih =>
      have hrec := deBrangesInitialTerm_recurrence_general
        (k := k) (m := m) (r := r + 1) (by omega) hr
      have htarget := deBrangesNormalizedCoeff_recurrence_general
        (k := k) (m := m) (r := r + 1) (by omega)
      rw [show r + 1 - 1 = r by omega, ih (by omega)] at hrec
      rw [show r + 1 - 1 = r by omega] at htarget
      have hscaled :
          deBrangesRecurrenceDen k (r + 1) *
              ((Nat.choose (2 * k + m + 1) m : ℝ) *
                deBrangesNormalizedCoeff k m (r + 1)) =
            deBrangesGeneralRecurrenceNum k m (r + 1) *
              ((Nat.choose (2 * k + m + 1) m : ℝ) *
                deBrangesNormalizedCoeff k m r) := by
        linear_combination
          (Nat.choose (2 * k + m + 1) m : ℝ) * htarget
      have hden : deBrangesRecurrenceDen k (r + 1) ≠ 0 := by
        unfold deBrangesRecurrenceDen
        positivity
      apply mul_left_cancel₀ hden
      exact hrec.trans hscaled.symm

lemma gasperOddCoeff_eq_normalized {k s r : ℕ} (hr : r ≤ 2 * s + 1) :
    gasperOddCoeff k s r = deBrangesNormalizedCoeff k (2 * s + 1) r := by
  induction r with
  | zero => simp
  | succ r ih =>
      have hrec := gasperOddCoeff_recurrence (k := k) (s := s)
        (r := r + 1) (by omega) hr
      have htarget := deBrangesNormalizedCoeff_recurrence_general
        (k := k) (m := 2 * s + 1) (r := r + 1) (by omega)
      have hnum :
          deBrangesGeneralRecurrenceNum k (2 * s + 1) (r + 1) =
            deBrangesOddRecurrenceNum k s (r + 1) := by
        simp only [deBrangesGeneralRecurrenceNum, deBrangesOddRecurrenceNum]
        push_cast
        ring
      rw [show r + 1 - 1 = r by omega, ih (by omega)] at hrec
      rw [show r + 1 - 1 = r by omega, hnum] at htarget
      have hden : deBrangesRecurrenceDen k (r + 1) ≠ 0 := by
        unfold deBrangesRecurrenceDen
        positivity
      apply mul_left_cancel₀ hden
      exact hrec.trans htarget.symm

lemma deBrangesInitialTerm_eq_gasperOddCoeff {k s r : ℕ} (hr : r ≤ 2 * s + 1) :
    deBrangesInitialTerm k (2 * s + 1) r =
      (Nat.choose (2 * k + (2 * s + 1) + 1) (2 * s + 1) : ℝ) *
        gasperOddCoeff k s r := by
  rw [deBrangesInitialTerm_eq_normalized hr,
    gasperOddCoeff_eq_normalized hr]

lemma coeff_gasperSquarePoly_mul_odd {k s j : ℕ} (hj : j ≤ s) (n : ℕ) :
    (((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2 : Polynomial ℝ)).coeff n =
      gasperOddInnerCoeff k s j n := by
  have hseries := gasperOddSquareSeries_mul_eq_clausen k s j hj
  calc
    (((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2 : Polynomial ℝ)).coeff n =
        PowerSeries.coeff n
          ((((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2 : Polynomial ℝ) :
            PowerSeries ℝ)) :=
      (Polynomial.coeff_coe
        (φ := ((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2 : Polynomial ℝ))
        n).symm
    _ = PowerSeries.coeff n
          ((1 - PowerSeries.X) *
            (((gasperSquarePoly k s j 1 : Polynomial ℝ) : PowerSeries ℝ) ^ 2)) := by
      congr 1
      simp
    _ = PowerSeries.coeff n
          ((1 - PowerSeries.X) * gasperSquareSeries k s j 1 ^ 2) := by
      rw [coe_gasperSquarePoly]
    _ = PowerSeries.coeff n
          (clausenRecSeries (gasperOddA k s j) (gasperOddB s j) (gasperOddC k j)) := by
      rw [hseries]
    _ = gasperOddInnerCoeff k s j n := by
      rw [coeff_clausenRecSeries]
      rfl

noncomputable def gasperOddSumPoly (k s : ℕ) : Polynomial ℝ :=
  ∑ j ∈ range (s + 1),
    Polynomial.C (gasperWeight k (2 * s + 1) j) *
      (Polynomial.X ^ (2 * j) *
        ((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2))

lemma eval_gasperOddSumPoly (k s : ℕ) (x : ℝ) :
    (gasperOddSumPoly k s).eval x = gasperOddSquareSum k s x := by
  rw [gasperOddSumPoly, Polynomial.eval_finsetSum, gasperOddSquareSum,
    Finset.mul_sum]
  apply sum_congr rfl
  intro j hj
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_sub, Polynomial.eval_one, Polynomial.eval_X,
    eval_gasperSquarePoly]
  ring_nf

lemma coeff_gasperOddSumPoly_term {k s j : ℕ} (hj : j ≤ s) (r : ℕ) :
    (Polynomial.C (gasperWeight k (2 * s + 1) j) *
        (Polynomial.X ^ (2 * j) *
          ((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2))).coeff r =
      if 2 * j ≤ r then gasperOddRecurrenceTerm k s r j else 0 := by
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow_mul']
  by_cases hjr : 2 * j ≤ r
  · rw [if_pos hjr, if_pos hjr, coeff_gasperSquarePoly_mul_odd hj]
    rfl
  · rw [if_neg hjr, if_neg hjr]
    simp

lemma coeff_gasperOddSumPoly {k s r : ℕ} (hr : r ≤ 2 * s + 1) :
    (gasperOddSumPoly k s).coeff r = gasperOddCoeff k s r := by
  rw [gasperOddSumPoly, Polynomial.finsetSum_coeff, gasperOddCoeff]
  have hhalf : r / 2 ≤ s := by omega
  rw [show s + 1 = (r / 2 + 1) + (s - r / 2) by omega, sum_range_add]
  have hprefix :
      (∑ j ∈ range (r / 2 + 1),
        (Polynomial.C (gasperWeight k (2 * s + 1) j) *
          (Polynomial.X ^ (2 * j) *
            ((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2))).coeff r) =
        ∑ j ∈ range (r / 2 + 1), gasperOddRecurrenceTerm k s r j := by
    apply sum_congr rfl
    intro j hj
    have hjhalf : j ≤ r / 2 := Nat.le_of_lt_succ (mem_range.mp hj)
    have hjs : j ≤ s := hjhalf.trans hhalf
    rw [coeff_gasperOddSumPoly_term hjs, if_pos (by omega)]
  rw [hprefix]
  have hsuffix :
      (∑ j ∈ range (s - r / 2),
        (Polynomial.C (gasperWeight k (2 * s + 1) (r / 2 + 1 + j)) *
          (Polynomial.X ^ (2 * (r / 2 + 1 + j)) *
            ((1 - Polynomial.X) *
              (gasperSquarePoly k s (r / 2 + 1 + j) 1) ^ 2))).coeff r) = 0 := by
    apply sum_eq_zero
    intro j hj
    have hjs : r / 2 + 1 + j ≤ s := by
      have hjlt := mem_range.mp hj
      omega
    rw [coeff_gasperOddSumPoly_term hjs, if_neg (by omega)]
  rw [hsuffix, add_zero]

lemma natDegree_one_sub_X_le :
    ((1 - Polynomial.X : Polynomial ℝ)).natDegree ≤ 1 := by
  exact (Polynomial.natDegree_sub_le (1 : Polynomial ℝ) Polynomial.X).trans
    (max_le (by simp) Polynomial.natDegree_X_le)

lemma natDegree_gasperOddSumPoly_le (k s : ℕ) :
    (gasperOddSumPoly k s).natDegree ≤ 2 * s + 1 := by
  rw [gasperOddSumPoly]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro j hj
  have hjs : j ≤ s := Nat.le_of_lt_succ (mem_range.mp hj)
  have hsquare := Polynomial.natDegree_pow_le_of_le 2
    (natDegree_gasperSquarePoly_le k s j 1)
  have hodd := Polynomial.natDegree_mul_le_of_le natDegree_one_sub_X_le hsquare
  calc
    (Polynomial.C (gasperWeight k (2 * s + 1) j) *
        (Polynomial.X ^ (2 * j) *
          ((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2))).natDegree ≤
        (Polynomial.X ^ (2 * j) *
          ((1 - Polynomial.X) * (gasperSquarePoly k s j 1) ^ 2)).natDegree :=
      Polynomial.natDegree_C_mul_le _ _
    _ ≤ 2 * j + (1 + 2 * (s - j)) :=
      Polynomial.natDegree_mul_le_of_le
        (Polynomial.natDegree_X_pow_le (2 * j)) hodd
    _ = 2 * s + 1 := by omega

lemma deBrangesPoly_eq_oddGasper (k s : ℕ) :
    deBrangesPoly k (2 * s + 1) =
      Polynomial.C (Nat.choose (2 * k + (2 * s + 1) + 1) (2 * s + 1) : ℝ) *
        gasperOddSumPoly k s := by
  ext r
  by_cases hr : r ≤ 2 * s + 1
  · rw [coeff_deBrangesPoly, Polynomial.coeff_C_mul,
      coeff_gasperOddSumPoly hr, deBrangesInitialTerm_eq_gasperOddCoeff hr]
  · have hrs : 2 * s + 1 < r := lt_of_not_ge hr
    rw [Polynomial.coeff_C_mul,
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_deBrangesPoly_le k (2 * s + 1)).trans_lt hrs),
      Polynomial.coeff_eq_zero_of_natDegree_lt
        ((natDegree_gasperOddSumPoly_le k s).trans_lt hrs), mul_zero]

lemma satisfiesOddGasperIdentity (k s : ℕ) :
    SatisfiesOddGasperIdentity k s := by
  intro x
  have hpoly := congrArg (Polynomial.eval x) (deBrangesPoly_eq_oddGasper k s)
  simpa [eval_deBrangesPoly, eval_gasperOddSumPoly] using hpoly

lemma satisfiesGasperIdentities : SatisfiesGasperIdentities := by
  exact ⟨fun k s hk => satisfiesEvenGasperIdentity k s,
    fun k s hk => satisfiesOddGasperIdentity k s⟩

end Submission
