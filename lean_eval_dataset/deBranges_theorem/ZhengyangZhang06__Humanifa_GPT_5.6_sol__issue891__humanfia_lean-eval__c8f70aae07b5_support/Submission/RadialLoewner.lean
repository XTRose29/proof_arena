import Submission.ConvexLoewner

namespace Submission

noncomputable def uniformLoewnerRoot (m : ℕ) : ℂ :=
  Complex.exp (2 * Real.pi * Complex.I / (m : ℂ))

lemma uniformLoewnerRoot_isPrimitive {m : ℕ} (hm : m ≠ 0) :
    IsPrimitiveRoot (uniformLoewnerRoot m) m := by
  exact Complex.isPrimitiveRoot_exp m hm

lemma sum_uniformLoewnerRoot_pow_eq_zero {m j : ℕ}
    (hm : m ≠ 0) (hj : 0 < j) (hjm : j < m) :
    ∑ i : Fin m, uniformLoewnerRoot m ^ ((i : ℕ) * j) = 0 := by
  change (∑ i : Fin m,
    (fun n : ℕ => uniformLoewnerRoot m ^ (n * j)) i) = 0
  rw [Fin.sum_univ_eq_sum_range
    (fun n : ℕ => uniformLoewnerRoot m ^ (n * j)) m]
  have hroot := uniformLoewnerRoot_isPrimitive hm
  have hne : uniformLoewnerRoot m ^ j ≠ 1 :=
    hroot.pow_ne_one_of_pos_of_lt hj.ne' hjm
  have hpow : (uniformLoewnerRoot m ^ j) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hroot.pow_eq_one, one_pow]
  have hgeom : ∑ i ∈ Finset.range m, (uniformLoewnerRoot m ^ j) ^ i = 0 := by
    apply eq_zero_of_ne_zero_of_mul_left_eq_zero
      (sub_ne_zero.mpr (Ne.symm hne))
    rw [mul_neg_geom_sum, hpow, sub_self]
  simpa only [pow_mul, mul_comm] using hgeom

noncomputable def drivenLoewnerVelocity (c : ℕ → ℂ) (omega : ℂ) (n : ℕ) : ℂ :=
  if n = 0 then 0 else
    (omega * deBrangesDrivenPartialSum c omega (n - 1) +
      deBrangesDrivenPartialSum c omega n) / 2

lemma drivenLoewnerVelocity_succ {c : ℕ → ℂ} {omega : ℂ}
    (homega : omega ≠ 0) (k : ℕ) :
    drivenLoewnerVelocity c omega (k + 1) =
      ((k + 1 : ℕ) : ℂ) * c (k + 1) + omega ^ (k + 1) +
        2 * ∑ j ∈ Finset.range k,
          ((j + 1 : ℕ) : ℂ) * c (j + 1) * omega ^ (k - j) := by
  have hpowdiv (j : ℕ) (hj : j < k) :
      omega ^ (k + 1) / omega ^ (j + 1) = omega ^ (k - j) := by
    apply (div_eq_iff (pow_ne_zero _ homega)).2
    rw [← pow_add]
    congr 1
    omega
  have hsum :
      omega ^ (k + 1) *
          (∑ j ∈ Finset.range k,
            ((j + 1 : ℕ) : ℂ) * (c (j + 1) / omega ^ (j + 1))) =
        ∑ j ∈ Finset.range k,
          ((j + 1 : ℕ) : ℂ) * c (j + 1) * omega ^ (k - j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    have hjk := Finset.mem_range.mp hj
    calc
      omega ^ (k + 1) *
          (((j + 1 : ℕ) : ℂ) * (c (j + 1) / omega ^ (j + 1))) =
          (((j + 1 : ℕ) : ℂ) * c (j + 1)) *
            (omega ^ (k + 1) / omega ^ (j + 1)) := by
              field_simp [homega]
      _ = ((j + 1 : ℕ) : ℂ) * c (j + 1) * omega ^ (k - j) := by
        rw [hpowdiv j hjk]
  have hlast :
      omega ^ (k + 1) *
          (((k + 1 : ℕ) : ℂ) * (c (k + 1) / omega ^ (k + 1))) =
        ((k + 1 : ℕ) : ℂ) * c (k + 1) := by
    field_simp [homega]
  simp only [drivenLoewnerVelocity, Nat.add_eq_zero_iff, Nat.one_ne_zero, and_false,
    ↓reduceIte, deBrangesDrivenPartialSum, deBrangesPartialSum,
    rotateLoewnerCoeff, Nat.add_sub_cancel]
  rw [Finset.sum_range_succ]
  have hfirst :
      omega *
          (omega ^ k *
            (1 + 2 * ∑ x ∈ Finset.range k,
              ((x + 1 : ℕ) : ℂ) * (c (x + 1) / omega ^ (x + 1)))) =
        omega ^ (k + 1) *
          (1 + 2 * ∑ x ∈ Finset.range k,
            ((x + 1 : ℕ) : ℂ) * (c (x + 1) / omega ^ (x + 1))) := by
    rw [← mul_assoc, show omega * omega ^ k = omega ^ (k + 1) by
      rw [pow_succ']]
  rw [hfirst]
  calc
    (omega ^ (k + 1) *
          (1 + 2 * ∑ x ∈ Finset.range k,
            ((x + 1 : ℕ) : ℂ) * (c (x + 1) / omega ^ (x + 1))) +
        omega ^ (k + 1) *
          (1 + 2 *
            ((∑ x ∈ Finset.range k,
              ((x + 1 : ℕ) : ℂ) * (c (x + 1) / omega ^ (x + 1))) +
              ((k + 1 : ℕ) : ℂ) *
                (c (k + 1) / omega ^ (k + 1))))) / 2 =
        omega ^ (k + 1) +
          2 * (omega ^ (k + 1) *
            ∑ x ∈ Finset.range k,
              ((x + 1 : ℕ) : ℂ) * (c (x + 1) / omega ^ (x + 1))) +
          omega ^ (k + 1) *
            (((k + 1 : ℕ) : ℂ) *
              (c (k + 1) / omega ^ (k + 1))) := by ring
    _ = _ := by rw [hsum, hlast]; ring

lemma sum_uniform_drivenLoewnerVelocity {c : ℕ → ℂ} {N k : ℕ}
    (hk : k ∈ Finset.range N) :
    (∑ i : Fin (N + 1),
        drivenLoewnerVelocity c
          (uniformLoewnerRoot (N + 1) ^ (i : ℕ)) (k + 1)) =
      ((N + 1 : ℕ) : ℂ) * (((k + 1 : ℕ) : ℂ) * c (k + 1)) := by
  let zeta := uniformLoewnerRoot (N + 1)
  have hN0 : N + 1 ≠ 0 := Nat.succ_ne_zero N
  have hroot : IsPrimitiveRoot zeta (N + 1) :=
    uniformLoewnerRoot_isPrimitive hN0
  have hzeta : zeta ≠ 0 := hroot.ne_zero hN0
  have homega (i : Fin (N + 1)) : zeta ^ (i : ℕ) ≠ 0 :=
    pow_ne_zero _ hzeta
  have hmoment (d : ℕ) (hd : 0 < d) (hdN : d < N + 1) :
      ∑ i : Fin (N + 1), (zeta ^ (i : ℕ)) ^ d = 0 := by
    simpa only [pow_mul] using
      (sum_uniformLoewnerRoot_pow_eq_zero hN0 hd hdN)
  have hkN : k < N := Finset.mem_range.mp hk
  have htail :
      (∑ i : Fin (N + 1),
        2 * ∑ j ∈ Finset.range k,
          ((j + 1 : ℕ) : ℂ) * c (j + 1) *
            (zeta ^ (i : ℕ)) ^ (k - j)) = 0 := by
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    apply Finset.sum_eq_zero
    intro j hj
    have hjk : j < k := Finset.mem_range.mp hj
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    rw [hmoment (k - j) (Nat.sub_pos_of_lt hjk) (by omega)]
    ring
  have hvelocity (i : Fin (N + 1)) :=
    drivenLoewnerVelocity_succ (c := c) (homega i) k
  dsimp only [zeta] at hvelocity
  simp_rw [hvelocity]
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_fin,
    nsmul_eq_mul]
  change
    ((N + 1 : ℕ) : ℂ) * (((k + 1 : ℕ) : ℂ) * c (k + 1)) +
        (∑ i : Fin (N + 1), (zeta ^ (i : ℕ)) ^ (k + 1)) +
        (∑ i : Fin (N + 1),
          2 * ∑ j ∈ Finset.range k,
            ((j + 1 : ℕ) : ℂ) * c (j + 1) *
              (zeta ^ (i : ℕ)) ^ (k - j)) = _
  rw [hmoment (k + 1) (by omega) (by omega), htail]
  ring

noncomputable def radialConvexLoewnerData (N : ℕ) (c : ℕ → ℂ) :
    FiniteConvexLoewnerData N c (fun n => (n : ℂ) * c n) where
  m := N + 1
  weight := fun _ => 1 / ((N + 1 : ℕ) : ℝ)
  direction := fun i =>
    drivenLoewnerVelocity c
      (uniformLoewnerRoot (N + 1) ^ (i : ℕ))
  omega := fun i => uniformLoewnerRoot (N + 1) ^ (i : ℕ)
  weight_nonneg := by
    intro i
    positivity
  weight_sum := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    field_simp
  norm_omega := by
    intro i
    rw [norm_pow,
      (uniformLoewnerRoot_isPrimitive (Nat.succ_ne_zero N)).norm'_eq_one
        (Nat.succ_ne_zero N), one_pow]
  point_ode := by
    intro i k hk
    simp [drivenLoewnerVelocity]
  average := by
    intro k hk
    rw [← Finset.mul_sum]
    rw [sum_uniform_drivenLoewnerVelocity hk]
    push_cast
    field_simp

end Submission
