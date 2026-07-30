import Submission.Carleman

open Filter

namespace Submission

noncomputable def deBrangesCoefficient (N k j : ℕ) : ℝ :=
  if 0 < k ∧ k ≤ j ∧ j ≤ N then
    (-1 : ℝ) ^ (j - k) * (k : ℝ) / (j : ℝ) *
      (Nat.choose (2 * j) (j - k) : ℝ) *
        (Nat.choose (N + j + 1) (N - j) : ℝ)
  else 0

noncomputable def explicitDeBrangesTau (N k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    deBrangesCoefficient N k j * Real.exp (-((j : ℝ) * t))

noncomputable def explicitDeBrangesTauDot (N k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    (-(j : ℝ)) * deBrangesCoefficient N k j * Real.exp (-((j : ℝ) * t))

noncomputable def deBrangesQCoefficient (N k j : ℕ) : ℝ :=
  if 0 < k ∧ k ≤ j ∧ j ≤ N then
    (-1 : ℝ) ^ (j - k) * (Nat.choose (2 * j) (j - k) : ℝ) *
      (Nat.choose (N + j + 1) (N - j) : ℝ)
  else 0

noncomputable def explicitDeBrangesQ (N k : ℕ) (t : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (N + 1),
    deBrangesQCoefficient N k j * Real.exp (-((j : ℝ) * t))

lemma hasDerivAt_exp_neg_nat_mul (j : ℕ) (t : ℝ) :
    HasDerivAt (fun u : ℝ => Real.exp (-((j : ℝ) * u)))
      (-(j : ℝ) * Real.exp (-((j : ℝ) * t))) t := by
  have hinner : HasDerivAt (fun u : ℝ => -((j : ℝ) * u)) (-(j : ℝ)) t := by
    simpa only [id_eq, mul_one, neg_mul] using
      (hasDerivAt_id t).const_mul (-(j : ℝ))
  simpa only [mul_comm] using hinner.exp

lemma hasDerivAt_explicitDeBrangesTau (N k : ℕ) (t : ℝ) :
    HasDerivAt (explicitDeBrangesTau N k) (explicitDeBrangesTauDot N k t) t := by
  unfold explicitDeBrangesTau explicitDeBrangesTauDot
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [mul_assoc, mul_left_comm, mul_comm] using
    (hasDerivAt_exp_neg_nat_mul j t).const_mul (deBrangesCoefficient N k j)

lemma choose_deBranges_step {k j : ℕ} (hkj : k < j) :
    ((j - k : ℕ) : ℝ) * (Nat.choose (2 * j) (j - k) : ℝ) =
      ((j + k + 1 : ℕ) : ℝ) * (Nat.choose (2 * j) (j - (k + 1)) : ℝ) := by
  have hsub : j - k = j - (k + 1) + 1 := by omega
  have hchoose := Nat.choose_succ_right_eq (2 * j) (j - (k + 1))
  rw [show 2 * j - (j - (k + 1)) = j + k + 1 by omega] at hchoose
  have hchoose' :
      (j - (k + 1) + 1) * Nat.choose (2 * j) (j - (k + 1) + 1) =
        (j + k + 1) * Nat.choose (2 * j) (j - (k + 1)) := by
    simpa only [mul_comm] using hchoose
  rw [hsub]
  exact_mod_cast hchoose'

lemma deBrangesCoefficient_system_algebra {K J S C C' D : ℝ}
    (hK : K ≠ 0) (hK' : K + 1 ≠ 0) (hJ : J ≠ 0)
    (hrel : (J - K) * C = (J + K + 1) * C') :
    (-S * K / J * C * D) - (S * (K + 1) / J * C' * D) =
      -((-J) * (-S * K / J * C * D)) / K -
        ((-J) * (S * (K + 1) / J * C' * D)) / (K + 1) := by
  field_simp [hK, hK', hJ]
  linear_combination S * D * hrel

lemma deBrangesCoefficient_system {N k j : ℕ} (hk0 : 0 < k) (hkN : k ≤ N) :
    deBrangesCoefficient N k j - deBrangesCoefficient N (k + 1) j =
      -((-(j : ℝ)) * deBrangesCoefficient N k j) / (k : ℝ) -
        ((-(j : ℝ)) * deBrangesCoefficient N (k + 1) j) / ((k + 1 : ℕ) : ℝ) := by
  by_cases hjN : j ≤ N
  · by_cases hjk : j = k
    · subst j
      simp [deBrangesCoefficient, hk0, hkN, Nat.ne_of_gt hk0]
    · have hkj : k < j ∨ j < k := lt_or_gt_of_ne (Ne.symm hjk)
      rcases hkj with hkj | hjk
      · rw [deBrangesCoefficient, if_pos ⟨hk0, hkj.le, hjN⟩]
        rw [deBrangesCoefficient,
          if_pos ⟨Nat.succ_pos k, Nat.succ_le_iff.mpr hkj, hjN⟩]
        have hsub : j - k = j - (k + 1) + 1 := by omega
        have hchoose := choose_deBranges_step hkj
        have hrel :
            ((j : ℝ) - (k : ℝ)) * (Nat.choose (2 * j) (j - k) : ℝ) =
              ((j : ℝ) + (k : ℝ) + 1) *
                (Nat.choose (2 * j) (j - (k + 1)) : ℝ) := by
          simpa only [Nat.cast_sub hkj.le, Nat.cast_add, Nat.cast_one] using hchoose
        have hsign :
            (-1 : ℝ) ^ (j - k) = -((-1 : ℝ) ^ (j - (k + 1))) := by
          rw [hsub, pow_succ]
          ring
        rw [hsign]
        simpa only [Nat.cast_add, Nat.cast_one] using deBrangesCoefficient_system_algebra
          (K := (k : ℝ)) (J := (j : ℝ))
          (S := (-1 : ℝ) ^ (j - (k + 1)))
          (C := (Nat.choose (2 * j) (j - k) : ℝ))
          (C' := (Nat.choose (2 * j) (j - (k + 1)) : ℝ))
          (D := (Nat.choose (N + j + 1) (N - j) : ℝ))
          (by exact_mod_cast Nat.ne_of_gt hk0)
          (by positivity)
          (by exact_mod_cast Nat.ne_of_gt (lt_trans hk0 hkj)) hrel
      · have hnotk : ¬k ≤ j := by omega
        have hnotks : ¬k + 1 ≤ j := by omega
        simp [deBrangesCoefficient, hnotk, hnotks]
  · have hnot : ¬j ≤ N := hjN
    simp [deBrangesCoefficient, hnot]

lemma explicitDeBranges_system_eq {N k : ℕ} (hk0 : 0 < k) (hkN : k ≤ N)
    (t : ℝ) :
    explicitDeBrangesTau N k t - explicitDeBrangesTau N (k + 1) t =
      -explicitDeBrangesTauDot N k t / (k : ℝ) -
        explicitDeBrangesTauDot N (k + 1) t / ((k + 1 : ℕ) : ℝ) := by
  unfold explicitDeBrangesTau explicitDeBrangesTauDot
  rw [← Finset.sum_sub_distrib, neg_div, Finset.sum_div,
    ← Finset.sum_neg_distrib, Finset.sum_div, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  calc
    deBrangesCoefficient N k j * Real.exp (-((j : ℝ) * t)) -
        deBrangesCoefficient N (k + 1) j * Real.exp (-((j : ℝ) * t)) =
      (deBrangesCoefficient N k j - deBrangesCoefficient N (k + 1) j) *
        Real.exp (-((j : ℝ) * t)) := by ring
    _ = _ := by rw [deBrangesCoefficient_system hk0 hkN]; ring

lemma deBrangesQCoefficient_eq {N k j : ℕ} (hk0 : 0 < k) :
    deBrangesQCoefficient N k j =
      (j : ℝ) * deBrangesCoefficient N k j / (k : ℝ) := by
  by_cases hkjN : k ≤ j ∧ j ≤ N
  · rcases hkjN with ⟨hkj, hjN⟩
    rw [deBrangesQCoefficient, if_pos ⟨hk0, hkj, hjN⟩]
    rw [deBrangesCoefficient, if_pos ⟨hk0, hkj, hjN⟩]
    have hj0 : (j : ℝ) ≠ 0 := by
      exact_mod_cast Nat.ne_of_gt (lt_of_lt_of_le hk0 hkj)
    have hk0' : (k : ℝ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hk0
    field_simp [hj0, hk0']
  · have hnot : ¬(0 < k ∧ k ≤ j ∧ j ≤ N) := by tauto
    simp [deBrangesQCoefficient, deBrangesCoefficient, hnot]

lemma explicitDeBrangesQ_eq_neg_tauDot_div {N k : ℕ} (hk0 : 0 < k) (t : ℝ) :
    explicitDeBrangesQ N k t = -explicitDeBrangesTauDot N k t / (k : ℝ) := by
  unfold explicitDeBrangesQ explicitDeBrangesTauDot
  rw [neg_div, Finset.sum_div, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  rw [deBrangesQCoefficient_eq hk0]
  ring

lemma explicitDeBrangesTauDot_nonpos_of_Q_nonneg {N k : ℕ} (hk0 : 0 < k) {t : ℝ}
    (hQ : 0 ≤ explicitDeBrangesQ N k t) : explicitDeBrangesTauDot N k t ≤ 0 := by
  rw [explicitDeBrangesQ_eq_neg_tauDot_div hk0] at hQ
  have hk0' : 0 < (k : ℝ) := by exact_mod_cast hk0
  rcases (div_nonneg_iff.mp hQ) with h | h
  · linarith [h.1]
  · exact (not_le_of_gt hk0' h.2).elim

lemma tendsto_deBranges_exp_term {N k j : ℕ} (hk0 : 0 < k) :
    Tendsto
      (fun t : ℝ =>
        deBrangesCoefficient N k j * Real.exp (-((j : ℝ) * t)))
      atTop (nhds 0) := by
  by_cases hkj : k ≤ j
  · have hj0 : 0 < (j : ℝ) := by exact_mod_cast lt_of_lt_of_le hk0 hkj
    have hmul : Tendsto (fun t : ℝ => (j : ℝ) * t) atTop atTop :=
      Filter.Tendsto.const_mul_atTop' hj0 tendsto_id
    simpa only [Function.comp_apply, mul_zero] using
      (Real.tendsto_exp_neg_atTop_nhds_zero.comp hmul).const_mul
        (deBrangesCoefficient N k j)
  · have hcoeff : deBrangesCoefficient N k j = 0 := by
      simp [deBrangesCoefficient, hkj]
    simp [hcoeff]

lemma tendsto_explicitDeBrangesTau (N k : ℕ) (hk0 : 0 < k) :
    Tendsto (explicitDeBrangesTau N k) atTop (nhds 0) := by
  unfold explicitDeBrangesTau
  simpa using tendsto_finsetSum (Finset.range (N + 1))
    (fun j hj => tendsto_deBranges_exp_term (N := N) (k := k) (j := j) hk0)

lemma tendsto_explicitDeBrangesTauDot (N k : ℕ) (hk0 : 0 < k) :
    Tendsto (explicitDeBrangesTauDot N k) atTop (nhds 0) := by
  unfold explicitDeBrangesTauDot
  convert
    tendsto_finsetSum (Finset.range (N + 1))
      (fun j hj => by
        simpa only [mul_zero] using
          (tendsto_deBranges_exp_term (N := N) (k := k) (j := j) hk0).const_mul
            (-(j : ℝ))) using 1 <;>
    simp [mul_assoc]

@[simp]
lemma explicitDeBrangesTau_terminal (N : ℕ) (t : ℝ) :
    explicitDeBrangesTau N (N + 1) t = 0 := by
  rw [explicitDeBrangesTau]
  apply Finset.sum_eq_zero
  intro j hj
  rw [deBrangesCoefficient, if_neg]
  · simp
  · intro h
    have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    omega

@[simp]
lemma explicitDeBrangesTauDot_terminal (N : ℕ) (t : ℝ) :
    explicitDeBrangesTauDot N (N + 1) t = 0 := by
  rw [explicitDeBrangesTauDot]
  apply Finset.sum_eq_zero
  intro j hj
  rw [deBrangesCoefficient, if_neg]
  · simp
  · intro h
    have hjN : j ≤ N := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
    omega

end Submission
