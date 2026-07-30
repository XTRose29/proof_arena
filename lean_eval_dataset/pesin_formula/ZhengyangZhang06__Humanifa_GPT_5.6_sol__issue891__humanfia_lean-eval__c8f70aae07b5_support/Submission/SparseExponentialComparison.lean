import Submission.SparseNodeRecurrence

namespace Submission.Helpers

noncomputable def pathLeftExpWeight {N : ℕ}
    (t : Fin (N + 1) → ℝ) (q a : ℝ) (i : Fin (N + 1)) : ℝ :=
  q ^ i.val * Real.exp (a * (t i - t 0))

noncomputable def pathRightExpWeight {N : ℕ}
    (t : Fin (N + 1) → ℝ) (q b : ℝ) (i : Fin (N + 1)) : ℝ :=
  q ^ (N - i.val) * Real.exp (b * (t (Fin.last N) - t i))

lemma pathLeftExpWeight_pos {N : ℕ}
    (t : Fin (N + 1) → ℝ) {q : ℝ} (hq : 0 < q)
    (a : ℝ) (i : Fin (N + 1)) :
    0 < pathLeftExpWeight t q a i := by
  exact mul_pos (pow_pos hq _) (Real.exp_pos _)

lemma pathRightExpWeight_pos {N : ℕ}
    (t : Fin (N + 1) → ℝ) {q : ℝ} (hq : 0 < q)
    (b : ℝ) (i : Fin (N + 1)) :
    0 < pathRightExpWeight t q b i := by
  exact mul_pos (pow_pos hq _) (Real.exp_pos _)

/-- Exponential comparison on a nonuniform path.  The two diagonal terms cost
`A / q`; the two crossed terms cost `A * q * exp ((a+b) gap)`. -/
lemma finite_exponential_path_comparison
    {N : ℕ}
    (d : Fin (N + 1) → ℝ) (t : Fin (N + 1) → ℝ)
    {A q a b delta : ℝ}
    (hd : ∀ i, 0 ≤ d i) (hA : 0 ≤ A) (hq : 0 < q)
    (hdelta : 0 ≤ delta)
    (hAq : A / q ≤ 1 / 4)
    (hcross_left : ∀ i, 0 < i.val → i.val < N →
      A * q * Real.exp ((a + b) * (t i - t (pathPrev i))) ≤ 1 / 4)
    (hcross_right : ∀ i, 0 < i.val → i.val < N →
      A * q * Real.exp ((a + b) * (t (pathNext i) - t i)) ≤ 1 / 4)
    (hboundary_left : d 0 ≤ delta)
    (hboundary_right : d (Fin.last N) ≤ delta)
    (hstep : ∀ i, 0 < i.val → i.val < N →
      d i ≤
        (A * Real.exp (a * (t i - t (pathPrev i)))) * d (pathPrev i) +
        (A * Real.exp (b * (t (pathNext i) - t i))) * d (pathNext i)) :
    ∀ i, d i ≤ delta *
      (pathLeftExpWeight t q a i + pathRightExpWeight t q b i) := by
  let u : Fin (N + 1) → ℝ := pathLeftExpWeight t q a
  let v : Fin (N + 1) → ℝ := pathRightExpWeight t q b
  let left : Fin (N + 1) → ℝ := fun i =>
    A * Real.exp (a * (t i - t (pathPrev i)))
  let right : Fin (N + 1) → ℝ := fun i =>
    A * Real.exp (b * (t (pathNext i) - t i))
  have hu (i : Fin (N + 1)) : 0 < u i := pathLeftExpWeight_pos t hq a i
  have hv (i : Fin (N + 1)) : 0 < v i := pathRightExpWeight_pos t hq b i
  have hleft_nonneg (i : Fin (N + 1)) : 0 ≤ left i := by
    exact mul_nonneg hA (Real.exp_pos _).le
  have hright_nonneg (i : Fin (N + 1)) : 0 ≤ right i := by
    exact mul_nonneg hA (Real.exp_pos _).le
  apply finite_path_comparison_of_split_weights d u v left right
    hd hu hv hleft_nonneg hright_nonneg hdelta
    hboundary_left hboundary_right
  · dsimp [u, v, pathLeftExpWeight]
    simp only [pow_zero, one_mul, sub_self, mul_zero,
      Real.exp_zero]
    exact le_add_of_nonneg_right (pathRightExpWeight_pos t hq b 0).le
  · dsimp [u, v, pathRightExpWeight]
    simp only [Nat.sub_self, pow_zero, one_mul, sub_self,
      mul_zero, Real.exp_zero]
    exact le_add_of_nonneg_left
      (pathLeftExpWeight_pos t hq a (Fin.last N)).le
  · intro i hi0 hiN
    have hpow : q ^ i.val = q ^ (i.val - 1) * q := by
      conv_lhs => rw [show i.val = (i.val - 1) + 1 by omega, pow_succ]
    have hexp :
        Real.exp (a * (t i - t (pathPrev i))) *
            Real.exp (a * (t (pathPrev i) - t 0)) =
          Real.exp (a * (t i - t 0)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have heq : left i * u (pathPrev i) = (A / q) * u i := by
      dsimp [left, u, pathLeftExpWeight]
      rw [show (pathPrev i).val = i.val - 1 by rfl]
      calc
        A * Real.exp (a * (t i - t (pathPrev i))) *
              (q ^ (i.val - 1) *
                Real.exp (a * (t (pathPrev i) - t 0))) =
            A * q ^ (i.val - 1) *
              (Real.exp (a * (t i - t (pathPrev i))) *
                Real.exp (a * (t (pathPrev i) - t 0))) := by ring
        _ = A * q ^ (i.val - 1) * Real.exp (a * (t i - t 0)) := by
          rw [hexp]
        _ = (A / q) * (q ^ i.val * Real.exp (a * (t i - t 0))) := by
          rw [hpow]
          field_simp [hq.ne']
    rw [heq]
    calc
      (A / q) * u i ≤ (1 / 4) * u i :=
        mul_le_mul_of_nonneg_right hAq (hu i).le
      _ = u i / 4 := by ring
  · intro i hi0 hiN
    have hnext : pathNext i = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [pathNext, min_eq_left (Nat.succ_le_iff.mpr hiN)]
    have hpow : q ^ (i.val + 1) = q ^ i.val * q := pow_succ q i.val
    have hexp :
        Real.exp (b * (t (pathNext i) - t i)) *
            Real.exp (a * (t (pathNext i) - t 0)) =
          Real.exp ((a + b) * (t (pathNext i) - t i)) *
            Real.exp (a * (t i - t 0)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have heq : right i * u (pathNext i) =
        (A * q * Real.exp ((a + b) * (t (pathNext i) - t i))) * u i := by
      dsimp [right, u, pathLeftExpWeight]
      rw [show (pathNext i).val = i.val + 1 by simp [hnext], hpow]
      calc
        A * Real.exp (b * (t (pathNext i) - t i)) *
              (q ^ i.val * q * Real.exp (a * (t (pathNext i) - t 0))) =
            A * q * q ^ i.val *
              (Real.exp (b * (t (pathNext i) - t i)) *
                Real.exp (a * (t (pathNext i) - t 0))) := by ring
        _ = A * q * q ^ i.val *
              (Real.exp ((a + b) * (t (pathNext i) - t i)) *
                Real.exp (a * (t i - t 0))) := by rw [hexp]
        _ = (A * q * Real.exp ((a + b) * (t (pathNext i) - t i))) *
              (q ^ i.val * Real.exp (a * (t i - t 0))) := by ring
    rw [heq]
    calc
      (A * q * Real.exp ((a + b) * (t (pathNext i) - t i))) * u i ≤
          (1 / 4) * u i :=
        mul_le_mul_of_nonneg_right (hcross_right i hi0 hiN) (hu i).le
      _ = u i / 4 := by ring
  · intro i hi0 hiN
    have hpow : q ^ (N - (i.val - 1)) = q ^ (N - i.val) * q := by
      have hNi : i.val ≤ N := Nat.lt_succ_iff.mp i.isLt
      rw [show N - (i.val - 1) = (N - i.val) + 1 by omega, pow_succ]
    have hexp :
        Real.exp (a * (t i - t (pathPrev i))) *
            Real.exp (b * (t (Fin.last N) - t (pathPrev i))) =
          Real.exp ((a + b) * (t i - t (pathPrev i))) *
            Real.exp (b * (t (Fin.last N) - t i)) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    have heq : left i * v (pathPrev i) =
        (A * q * Real.exp ((a + b) * (t i - t (pathPrev i)))) * v i := by
      dsimp [left, v, pathRightExpWeight]
      rw [show (pathPrev i).val = i.val - 1 by rfl, hpow]
      calc
        A * Real.exp (a * (t i - t (pathPrev i))) *
              (q ^ (N - i.val) * q *
                Real.exp (b * (t (Fin.last N) - t (pathPrev i)))) =
            A * q * q ^ (N - i.val) *
              (Real.exp (a * (t i - t (pathPrev i))) *
                Real.exp (b * (t (Fin.last N) - t (pathPrev i)))) := by ring
        _ = A * q * q ^ (N - i.val) *
              (Real.exp ((a + b) * (t i - t (pathPrev i))) *
                Real.exp (b * (t (Fin.last N) - t i))) := by rw [hexp]
        _ = (A * q * Real.exp ((a + b) * (t i - t (pathPrev i)))) *
              (q ^ (N - i.val) *
                Real.exp (b * (t (Fin.last N) - t i))) := by ring
    rw [heq]
    calc
      (A * q * Real.exp ((a + b) * (t i - t (pathPrev i)))) * v i ≤
          (1 / 4) * v i :=
        mul_le_mul_of_nonneg_right (hcross_left i hi0 hiN) (hv i).le
      _ = v i / 4 := by ring
  · intro i hi0 hiN
    have hnext : pathNext i = ⟨i.val + 1, by omega⟩ := by
      apply Fin.ext
      simp [pathNext, min_eq_left (Nat.succ_le_iff.mpr hiN)]
    have hpow : q ^ (N - i.val) = q ^ (N - (i.val + 1)) * q := by
      have hi_succ : i.val + 1 ≤ N := Nat.succ_le_iff.mpr hiN
      conv_lhs =>
        rw [show N - i.val = (N - (i.val + 1)) + 1 by omega, pow_succ]
    have hexp :
        Real.exp (b * (t (pathNext i) - t i)) *
            Real.exp (b * (t (Fin.last N) - t (pathNext i))) =
          Real.exp (b * (t (Fin.last N) - t i)) := by
      rw [← Real.exp_add]
      congr 1
      ring
    have heq : right i * v (pathNext i) = (A / q) * v i := by
      dsimp [right, v, pathRightExpWeight]
      rw [show (pathNext i).val = i.val + 1 by simp [hnext]]
      calc
        A * Real.exp (b * (t (pathNext i) - t i)) *
              (q ^ (N - (i.val + 1)) *
                Real.exp (b * (t (Fin.last N) - t (pathNext i)))) =
            A * q ^ (N - (i.val + 1)) *
              (Real.exp (b * (t (pathNext i) - t i)) *
                Real.exp (b * (t (Fin.last N) - t (pathNext i)))) := by ring
        _ = A * q ^ (N - (i.val + 1)) *
              Real.exp (b * (t (Fin.last N) - t i)) := by
          rw [hexp]
        _ = (A / q) *
              (q ^ (N - i.val) * Real.exp (b * (t (Fin.last N) - t i))) := by
          rw [hpow]
          field_simp [hq.ne']
    rw [heq]
    calc
      (A / q) * v i ≤ (1 / 4) * v i :=
        mul_le_mul_of_nonneg_right hAq (hv i).le
      _ = v i / 4 := by ring
  · intro i hi0 hiN
    exact hstep i hi0 hiN

/-- The natural-time form of `finite_exponential_path_comparison`. -/
lemma finite_exponential_path_comparison_nat
    {N : ℕ}
    (d : Fin (N + 1) → ℝ) (t : Fin (N + 1) → ℕ)
    {A q a b delta : ℝ}
    (hd : ∀ i, 0 ≤ d i) (hA : 0 ≤ A) (hq : 0 < q)
    (hdelta : 0 ≤ delta)
    (ht : ∀ i j, i.val < j.val → t i < t j)
    (hAq : A / q ≤ 1 / 4)
    (hcross_left : ∀ i, 0 < i.val → i.val < N →
      A * q * Real.exp ((a + b) *
        ((t i - t (pathPrev i) : ℕ) : ℝ)) ≤ 1 / 4)
    (hcross_right : ∀ i, 0 < i.val → i.val < N →
      A * q * Real.exp ((a + b) *
        ((t (pathNext i) - t i : ℕ) : ℝ)) ≤ 1 / 4)
    (hboundary_left : d 0 ≤ delta)
    (hboundary_right : d (Fin.last N) ≤ delta)
    (hstep : ∀ i, 0 < i.val → i.val < N →
      d i ≤
        (A * Real.exp (a *
          ((t i - t (pathPrev i) : ℕ) : ℝ))) * d (pathPrev i) +
        (A * Real.exp (b *
          ((t (pathNext i) - t i : ℕ) : ℝ))) * d (pathNext i)) :
    ∀ i, d i ≤ delta *
      (q ^ i.val * Real.exp (a * ((t i : ℝ) - t 0)) +
        q ^ (N - i.val) *
          Real.exp (b * ((t (Fin.last N) : ℝ) - t i))) := by
  let tr : Fin (N + 1) → ℝ := fun i => t i
  have hprev (i : Fin (N + 1)) (hi0 : 0 < i.val) :
      t (pathPrev i) ≤ t i := by
    apply (ht (pathPrev i) i ?_).le
    change i.val - 1 < i.val
    omega
  have hnext (i : Fin (N + 1)) (hiN : i.val < N) :
      t i ≤ t (pathNext i) :=
    (ht i (pathNext i) (by
      simp [pathNext, min_eq_left (Nat.succ_le_iff.mpr hiN)])).le
  have hmain := finite_exponential_path_comparison d tr hd hA hq hdelta hAq
    (fun i hi0 hiN => by
      simpa [tr, Nat.cast_sub (hprev i hi0)] using hcross_left i hi0 hiN)
    (fun i hi0 hiN => by
      simpa [tr, Nat.cast_sub (hnext i hiN)] using hcross_right i hi0 hiN)
    hboundary_left hboundary_right
    (fun i hi0 hiN => by
      simpa [tr, Nat.cast_sub (hprev i hi0),
        Nat.cast_sub (hnext i hiN)] using hstep i hi0 hiN)
  intro i
  simpa [pathLeftExpWeight, pathRightExpWeight, tr] using hmain i

end Submission.Helpers
