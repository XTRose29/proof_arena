import ChallengeDeps

open LeanEval.Analysis
open MeasureTheory
open scoped BigOperators NNReal

namespace Submission.Helpers

lemma sum_choose_neg_pow_mul_pow (x : ℝ) {k n : ℕ} (hkn : k ≤ n) :
    ∑ j ∈ Finset.Iic k,
        (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * x ^ (n - j) =
      x ^ (n - k) * (1 - x) ^ k := by
  rw [← Nat.range_succ_eq_Iic]
  calc
    ∑ j ∈ Finset.range (k + 1),
        (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * x ^ (n - j) =
        x ^ (n - k) * ∑ j ∈ Finset.range (k + 1),
          (-1 : ℝ) ^ (k - j) * (k.choose j : ℝ) * x ^ (k - j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j hj
      have hjk : j ≤ k := Nat.le_of_lt_succ (Finset.mem_range.mp hj)
      have hpow : x ^ (n - j) = x ^ (n - k) * x ^ (k - j) := by
        rw [← pow_add, show n - k + (k - j) = n - j by omega]
      rw [hpow]
      ring
    _ = x ^ (n - k) * (1 - x) ^ k := by
      congr 1
      rw [show 1 - x = 1 + -x by ring, add_pow]
      apply Finset.sum_congr rfl
      intro j _
      rw [neg_pow]
      simp only [one_pow]
      ring

lemma diff_prod_pow {d : ℕ} (x : Fin d → ℝ) {k n : Fin d → ℕ} (hkn : k ≤ n) :
    diff (fun m => ∏ i, x i ^ m i) k n =
      ∏ i, x i ^ (n i - k i) * (1 - x i) ^ k i := by
  classical
  rw [diff]
  simp only [multiChoose, Nat.cast_prod, Pi.sub_apply]
  change (∑ j ∈ Finset.Iic k,
      (-1 : ℝ) ^ (∑ i, (k i - j i)) *
        (∏ i, (k i).choose (j i) : ℝ) * (∏ i, x i ^ (n i - j i))) = _
  change (∑ j ∈ Fintype.piFinset (fun i => Finset.Iic (k i)),
      (-1 : ℝ) ^ (∑ i, (k i - j i)) *
        (∏ i, (k i).choose (j i) : ℝ) * (∏ i, x i ^ (n i - j i))) = _
  calc
    (∑ j ∈ Fintype.piFinset (fun i => Finset.Iic (k i)),
        (-1 : ℝ) ^ (∑ i, (k i - j i)) *
          (∏ i, (k i).choose (j i) : ℝ) * (∏ i, x i ^ (n i - j i))) =
        ∑ j ∈ Fintype.piFinset (fun i => Finset.Iic (k i)),
          ∏ i, (-1 : ℝ) ^ (k i - j i) *
            ((k i).choose (j i) : ℝ) * x i ^ (n i - j i) := by
      apply Finset.sum_congr rfl
      intro j _
      have hsign : (-1 : ℝ) ^ (∑ i, (k i - j i)) =
          ∏ i, (-1 : ℝ) ^ (k i - j i) := by
        symm
        simpa using Finset.prod_pow_eq_pow_sum Finset.univ
          (fun i => k i - j i) (-1 : ℝ)
      rw [hsign, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ j ∈ Finset.Iic (k i),
          (-1 : ℝ) ^ (k i - j) * ((k i).choose j : ℝ) * x i ^ (n i - j) := by
      rw [Finset.prod_univ_sum]
    _ = ∏ i, x i ^ (n i - k i) * (1 - x i) ^ k i := by
      apply Finset.prod_congr rfl
      intro i _
      exact sum_choose_neg_pow_mul_pow (x i) (hkn i)

lemma isCompact_cube (d : ℕ) : IsCompact (cube d) := by
  let e : EuclideanSpace ℝ (Fin d) ≃ₜ (Fin d → ℝ) :=
    PiLp.homeomorph 2 (fun _ : Fin d => ℝ)
  have hcompact : IsCompact
      (e ⁻¹' (Set.univ.pi fun _ : Fin d => Set.Icc (0 : ℝ) 1)) :=
    e.isCompact_preimage.mpr (isCompact_univ_pi fun _ => isCompact_Icc)
  convert hcompact using 1
  ext x
  simp only [cube, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_pi, Set.mem_univ,
    true_implies]
  dsimp [e, PiLp.homeomorph]
  constructor
  · intro h i
    exact h i
  · intro h i
    exact h i

lemma measurableSet_cube (d : ℕ) : MeasurableSet (cube d) :=
  (isCompact_cube d).measurableSet

lemma continuous_monomial {d : ℕ} (n : Fin d → ℕ) : Continuous (monomial n) := by
  unfold monomial
  fun_prop

/-- The tensor-product Bernstein kernel indexed by `k ≤ n`. -/
def kernel {d : ℕ} (n k : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (multiChoose n k : ℝ) * ∏ i, (x i) ^ (n i - k i) * (1 - x i) ^ k i

lemma continuous_kernel {d : ℕ} (n k : Fin d → ℕ) : Continuous (kernel n k) := by
  unfold kernel multiChoose
  fun_prop

lemma kernel_nonneg {d : ℕ} {n k : Fin d → ℕ} (x : EuclideanSpace ℝ (Fin d))
    (hx : x ∈ cube d) : 0 ≤ kernel n k x := by
  unfold kernel
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Finset.prod_nonneg
  intro i _
  apply mul_nonneg
  · exact pow_nonneg (hx i).1 _
  · exact pow_nonneg (sub_nonneg.mpr (hx i).2) _

lemma sum_kernel {d : ℕ} (n : Fin d → ℕ) (x : EuclideanSpace ℝ (Fin d)) :
    ∑ k ∈ Finset.Iic n, kernel n k x = 1 := by
  classical
  simp only [kernel, multiChoose, Nat.cast_prod]
  rw [show Finset.Iic n = Fintype.piFinset (fun i => Finset.Iic (n i)) by rfl]
  change (∑ k ∈ Fintype.piFinset (fun i => Finset.Iic (n i)),
      (∏ i, ((n i).choose (k i) : ℝ)) *
        ∏ i, (x i) ^ (n i - k i) * (1 - x i) ^ k i) = 1
  calc
    (∑ k ∈ Fintype.piFinset (fun i => Finset.Iic (n i)),
        (∏ i, ((n i).choose (k i) : ℝ)) *
          ∏ i, (x i) ^ (n i - k i) * (1 - x i) ^ k i) =
        ∑ k ∈ Fintype.piFinset (fun i => Finset.Iic (n i)),
          ∏ i, ((n i).choose (k i) : ℝ) *
            (x i) ^ (n i - k i) * (1 - x i) ^ k i := by
      apply Finset.sum_congr rfl
      intro k _
      rw [← Finset.prod_mul_distrib]
      apply Finset.prod_congr rfl
      intro i _
      ring
    _ = ∏ i, ∑ k ∈ Finset.Iic (n i),
          ((n i).choose k : ℝ) * (x i) ^ (n i - k) * (1 - x i) ^ k := by
      rw [Finset.prod_univ_sum]
    _ = 1 := by
      have hterm (i : Fin d) :
          (∑ k ∈ Finset.Iic (n i),
            ((n i).choose k : ℝ) * (x i) ^ (n i - k) * (1 - x i) ^ k) = 1 := by
        rw [← Nat.range_succ_eq_Iic]
        calc
          (∑ k ∈ Finset.range (n i + 1),
              ((n i).choose k : ℝ) * (x i) ^ (n i - k) * (1 - x i) ^ k) =
              ((1 - x i) + x i) ^ n i := by
            rw [add_pow]
            apply Finset.sum_congr rfl
            intro k _
            ring
          _ = 1 := by ring
      simp_rw [hterm]
      simp

lemma diff_sub {d : ℕ} (a b : (Fin d → ℕ) → ℝ) (k n : Fin d → ℕ) :
    diff (fun m => a m - b m) k n = diff a k n - diff b k n := by
  simp only [diff]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j _
  ring

lemma diff_momentOf {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] {k n : Fin d → ℕ} (hkn : k ≤ n) :
    diff (momentOf μ) k n =
      ∫ x in cube d, ∏ i, (x i) ^ (n i - k i) * (1 - x i) ^ k i ∂μ := by
  rw [diff]
  simp only [momentOf]
  calc
    (∑ j ∈ Finset.Iic k,
        (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) *
          ∫ x in cube d, monomial (n - j) x ∂μ) =
        ∑ j ∈ Finset.Iic k,
          ∫ x in cube d,
            ((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)) *
              monomial (n - j) x ∂μ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [integral_const_mul]
    _ = ∫ x in cube d,
        ∑ j ∈ Finset.Iic k,
          ((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)) *
            monomial (n - j) x ∂μ := by
      rw [integral_finsetSum]
      intro j _
      exact (continuous_const.mul (continuous_monomial (n - j))).continuousOn.integrableOn_compact
        (isCompact_cube d)
    _ = ∫ x in cube d, ∏ i, (x i) ^ (n i - k i) * (1 - x i) ^ k i ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      simpa only [diff, monomial] using diff_prod_pow (fun i => x i) hkn

lemma integrableOn_kernel {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (n k : Fin d → ℕ) : IntegrableOn (kernel n k) (cube d) μ :=
  (continuous_kernel n k).continuousOn.integrableOn_compact (isCompact_cube d)

lemma integral_kernel_nonneg {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    {n k : Fin d → ℕ} : 0 ≤ ∫ x in cube d, kernel n k x ∂μ := by
  apply integral_nonneg_of_ae
  filter_upwards [ae_restrict_mem (measurableSet_cube d)] with x hx
  exact kernel_nonneg x hx

lemma sum_integral_kernel {d : ℕ} (μ : Measure (EuclideanSpace ℝ (Fin d)))
    [IsFiniteMeasure μ] (n : Fin d → ℕ) :
    ∑ k ∈ Finset.Iic n, ∫ x in cube d, kernel n k x ∂μ = μ.real (cube d) := by
  calc
    (∑ k ∈ Finset.Iic n, ∫ x in cube d, kernel n k x ∂μ) =
        ∫ x in cube d, ∑ k ∈ Finset.Iic n, kernel n k x ∂μ := by
      symm
      rw [integral_finsetSum]
      intro k _
      exact integrableOn_kernel μ n k
    _ = ∫ _x in cube d, (1 : ℝ) ∂μ := by
      apply integral_congr_ae
      filter_upwards with x
      exact sum_kernel n x
    _ = μ.real (cube d) := by simp

lemma momentConfiguration_hausdorffBounded {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    IsMomentConfiguration a → HausdorffBounded a := by
  rintro ⟨μ, ν, hμ, hν, ha⟩
  letI : IsFiniteMeasure μ := hμ
  letI : IsFiniteMeasure ν := hν
  refine ⟨μ.real Set.univ + ν.real Set.univ, fun n => ?_⟩
  calc
    (∑ k ∈ Finset.Iic n, |(multiChoose n k : ℝ) * diff a k n|) ≤
        ∑ k ∈ Finset.Iic n,
          ((∫ x in cube d, kernel n k x ∂μ) + ∫ x in cube d, kernel n k x ∂ν) := by
      apply Finset.sum_le_sum
      intro k hk
      have hkn : k ≤ n := Finset.mem_Iic.mp hk
      have hdiff : (multiChoose n k : ℝ) * diff a k n =
          (∫ x in cube d, kernel n k x ∂μ) - ∫ x in cube d, kernel n k x ∂ν := by
        rw [show a = fun m => momentOf μ m - momentOf ν m by
          funext m
          exact ha m]
        rw [diff_sub, diff_momentOf μ hkn, diff_momentOf ν hkn]
        simp only [kernel, integral_const_mul]
        ring
      rw [hdiff]
      have hposμ : 0 ≤ ∫ x in cube d, kernel n k x ∂μ := integral_kernel_nonneg μ
      have hposν : 0 ≤ ∫ x in cube d, kernel n k x ∂ν := integral_kernel_nonneg ν
      calc
        |(∫ x in cube d, kernel n k x ∂μ) - ∫ x in cube d, kernel n k x ∂ν| =
            |(∫ x in cube d, kernel n k x ∂μ) +
              -(∫ x in cube d, kernel n k x ∂ν)| := by rw [sub_eq_add_neg]
        _ ≤ |∫ x in cube d, kernel n k x ∂μ| +
            |-(∫ x in cube d, kernel n k x ∂ν)| := abs_add_le _ _
        _ = (∫ x in cube d, kernel n k x ∂μ) +
            ∫ x in cube d, kernel n k x ∂ν := by
          rw [abs_of_nonneg hposμ, abs_neg, abs_of_nonneg hposν]
    _ = (∑ k ∈ Finset.Iic n, ∫ x in cube d, kernel n k x ∂μ) +
        ∑ k ∈ Finset.Iic n, ∫ x in cube d, kernel n k x ∂ν := by
      rw [Finset.sum_add_distrib]
    _ = μ.real (cube d) + ν.real (cube d) := by
      rw [sum_integral_kernel μ n, sum_integral_kernel ν n]
    _ ≤ μ.real Set.univ + ν.real Set.univ :=
      add_le_add (measureReal_mono (Set.subset_univ _))
        (measureReal_mono (Set.subset_univ _))

lemma alternating_choose_choose (N m : ℕ) :
    ∑ r ∈ Finset.Iic N,
        (-1 : ℝ) ^ (N - r) * (N.choose r : ℝ) * (r.choose m : ℝ) =
      if N = m then 1 else 0 := by
  rw [← Nat.range_succ_eq_Iic]
  have hInt :
      (∑ r ∈ Finset.range (N + 1),
          (-1 : ℤ) ^ (N - r) * (N.choose r : ℤ) * (r.choose m : ℤ)) =
        if N = m then 1 else 0 := by
    simpa [fwdDiff_iter_eq_sum_shift, mul_assoc] using fwdDiff_iter_choose_zero m N
  exact_mod_cast hInt

lemma alternating_choose_choose_of_le (N m n : ℕ) (hNn : N ≤ n) :
    ∑ r ∈ Finset.Iic n,
        (-1 : ℝ) ^ (N - r) * (N.choose r : ℝ) * (r.choose m : ℝ) =
      if N = m then 1 else 0 := by
  rw [← alternating_choose_choose N m]
  have hsub : Finset.Iic N ⊆ Finset.Iic n := by
    intro r hr
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hr).trans hNn)
  exact (Finset.sum_subset hsub fun r _ hr => by
    have hNr : N < r := by simpa only [Finset.mem_Iic, not_le] using hr
    simp [Nat.choose_eq_zero_of_lt hNr]).symm

lemma choose_diff_coefficient (n m j : ℕ) (hmn : m ≤ n) (hjn : j ≤ n) :
    ∑ k ∈ Finset.Iic n,
        (-1 : ℝ) ^ (k - j) * (n.choose k : ℝ) *
          (k.choose j : ℝ) * ((n - k).choose m : ℝ) =
      if j = n - m then (n.choose m : ℝ) else 0 := by
  rw [← Nat.range_succ_eq_Iic]
  calc
    (∑ k ∈ Finset.range (n + 1),
        (-1 : ℝ) ^ (k - j) * (n.choose k : ℝ) *
          (k.choose j : ℝ) * ((n - k).choose m : ℝ)) =
        ∑ r ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ ((n - r) - j) * (n.choose (n - r) : ℝ) *
            ((n - r).choose j : ℝ) * (r.choose m : ℝ) := by
      calc
        _ = ∑ r ∈ Finset.range (n + 1),
            (-1 : ℝ) ^ ((n - r) - j) * (n.choose (n - r) : ℝ) *
              ((n - r).choose j : ℝ) * ((n - (n - r)).choose m : ℝ) :=
          (Finset.sum_flip (n := n) (fun k =>
            (-1 : ℝ) ^ (k - j) * (n.choose k : ℝ) *
              (k.choose j : ℝ) * ((n - k).choose m : ℝ))).symm
        _ = _ := by
          apply Finset.sum_congr rfl
          intro r hr
          have hrn : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
          rw [Nat.sub_sub_self hrn]
    _ = ∑ r ∈ Finset.range (n + 1),
        (n.choose j : ℝ) *
          ((-1 : ℝ) ^ ((n - j) - r) * ((n - j).choose r : ℝ) *
            (r.choose m : ℝ)) := by
      apply Finset.sum_congr rfl
      intro r hr
      have hrn : r ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hr)
      by_cases hrj : r ≤ n - j
      · have hjnr : j ≤ n - r := by omega
        have hsub : (n - r) - j = (n - j) - r := by omega
        have hchoose : n.choose (n - r) * (n - r).choose j =
            n.choose j * (n - j).choose r := by
          calc
            n.choose (n - r) * (n - r).choose j =
                n.choose j * (n - j).choose ((n - r) - j) := Nat.choose_mul hjnr
            _ = n.choose j * (n - j).choose r := by
              rw [hsub, Nat.choose_symm hrj]
        have hchooseR : (n.choose (n - r) : ℝ) * ((n - r).choose j : ℝ) =
            (n.choose j : ℝ) * ((n - j).choose r : ℝ) := by
          exact_mod_cast hchoose
        rw [hsub]
        calc
          (-1 : ℝ) ^ (n - j - r) * (n.choose (n - r) : ℝ) *
              ((n - r).choose j : ℝ) * (r.choose m : ℝ) =
              (-1 : ℝ) ^ (n - j - r) *
                ((n.choose (n - r) : ℝ) * ((n - r).choose j : ℝ)) *
                  (r.choose m : ℝ) := by ring
          _ = (-1 : ℝ) ^ (n - j - r) *
                ((n.choose j : ℝ) * ((n - j).choose r : ℝ)) *
                  (r.choose m : ℝ) := by rw [hchooseR]
          _ = (n.choose j : ℝ) *
              ((-1 : ℝ) ^ (n - j - r) * ((n - j).choose r : ℝ) *
                (r.choose m : ℝ)) := by ring
      · have hjlt : n - r < j := by omega
        have hNr : n - j < r := by omega
        rw [Nat.choose_eq_zero_of_lt hjlt, Nat.choose_eq_zero_of_lt hNr]
        ring
    _ = (n.choose j : ℝ) *
        ∑ r ∈ Finset.range (n + 1),
          (-1 : ℝ) ^ ((n - j) - r) * ((n - j).choose r : ℝ) *
            (r.choose m : ℝ) := by
      rw [Finset.mul_sum]
    _ = (n.choose j : ℝ) * (if n - j = m then 1 else 0) := by
      rw [Nat.range_succ_eq_Iic, alternating_choose_choose_of_le]
      omega
    _ = if j = n - m then (n.choose m : ℝ) else 0 := by
      by_cases h : j = n - m
      · have h' : n - j = m := by omega
        rw [if_pos h, if_pos h', mul_one]
        norm_cast
        rw [h]
        exact Nat.choose_symm hmn
      · have h' : n - j ≠ m := by omega
        rw [if_neg h, if_neg h', mul_zero]

lemma multiChoose_eq_zero_of_not_le {d : ℕ} {k j : Fin d → ℕ} (hjk : ¬j ≤ k) :
    multiChoose k j = 0 := by
  classical
  simp only [Pi.le_def, not_forall] at hjk
  obtain ⟨i, hi⟩ := hjk
  unfold multiChoose
  apply Finset.prod_eq_zero (Finset.mem_univ i)
  exact Nat.choose_eq_zero_of_lt (Nat.lt_of_not_ge hi)

lemma multi_choose_diff_coefficient {d : ℕ} (n m j : Fin d → ℕ)
    (hmn : m ≤ n) (hjn : j ≤ n) :
    ∑ k ∈ Finset.Iic n,
        (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose n k : ℝ) *
          (multiChoose k j : ℝ) * (multiChoose (n - k) m : ℝ) =
      if j = n - m then (multiChoose n m : ℝ) else 0 := by
  classical
  simp only [multiChoose, Nat.cast_prod]
  rw [show Finset.Iic n = Fintype.piFinset (fun i => Finset.Iic (n i)) by rfl]
  calc
    (∑ k ∈ Fintype.piFinset (fun i => Finset.Iic (n i)),
        (-1 : ℝ) ^ (∑ i, (k i - j i)) *
          (∏ i, ((n i).choose (k i) : ℝ)) *
          (∏ i, ((k i).choose (j i) : ℝ)) *
          ∏ i, (((n - k) i).choose (m i) : ℝ)) =
        ∑ k ∈ Fintype.piFinset (fun i => Finset.Iic (n i)),
          ∏ i, (-1 : ℝ) ^ (k i - j i) * ((n i).choose (k i) : ℝ) *
            ((k i).choose (j i) : ℝ) * (((n - k) i).choose (m i) : ℝ) := by
      apply Finset.sum_congr rfl
      intro k _
      have hsign : (-1 : ℝ) ^ (∑ i, (k i - j i)) =
          ∏ i, (-1 : ℝ) ^ (k i - j i) := by
        symm
        simpa using Finset.prod_pow_eq_pow_sum Finset.univ
          (fun i => k i - j i) (-1 : ℝ)
      rw [hsign, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib,
        ← Finset.prod_mul_distrib]
    _ = ∏ i, ∑ k ∈ Finset.Iic (n i),
        (-1 : ℝ) ^ (k - j i) * ((n i).choose k : ℝ) *
          (k.choose (j i) : ℝ) * ((n i - k).choose (m i) : ℝ) := by
      rw [Finset.prod_univ_sum]
      simp only [Pi.sub_apply]
    _ = ∏ i, if j i = n i - m i then ((n i).choose (m i) : ℝ) else 0 := by
      apply Finset.prod_congr rfl
      intro i _
      exact choose_diff_coefficient (n i) (m i) (j i) (hmn i) (hjn i)
    _ = if j = n - m then ∏ i, ((n i).choose (m i) : ℝ) else 0 := by
      by_cases h : j = n - m
      · subst j
        simp
      · have hex : ∃ i, j i ≠ n i - m i := by
          contrapose! h
          exact funext h
        obtain ⟨i, hi⟩ := hex
        rw [if_neg h, Finset.prod_eq_zero (Finset.mem_univ i)]
        simp [hi]

lemma diff_eq_sum_Iic_of_le {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    {k n : Fin d → ℕ} (hkn : k ≤ n) :
    diff a k n = ∑ j ∈ Finset.Iic n,
      (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ) * a (n - j) := by
  rw [diff]
  apply Finset.sum_subset
  · intro j hj
    exact Finset.mem_Iic.mpr ((Finset.mem_Iic.mp hj).trans hkn)
  · intro j _ hj
    have hjk : ¬j ≤ k := by simpa only [Finset.mem_Iic] using hj
    rw [multiChoose_eq_zero_of_not_le hjk, Nat.cast_zero]
    ring

lemma bernstein_inversion {d : ℕ} (a : (Fin d → ℕ) → ℝ)
    {m n : Fin d → ℕ} (hmn : m ≤ n) :
    ∑ k ∈ Finset.Iic n,
        (multiChoose n k : ℝ) * diff a k n * (multiChoose (n - k) m : ℝ) =
      (multiChoose n m : ℝ) * a m := by
  classical
  calc
    (∑ k ∈ Finset.Iic n,
        (multiChoose n k : ℝ) * diff a k n * (multiChoose (n - k) m : ℝ)) =
        ∑ k ∈ Finset.Iic n, ∑ j ∈ Finset.Iic n,
          ((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose n k : ℝ) *
            (multiChoose k j : ℝ) * (multiChoose (n - k) m : ℝ)) * a (n - j) := by
      apply Finset.sum_congr rfl
      intro k hk
      rw [diff_eq_sum_Iic_of_le a (Finset.mem_Iic.mp hk), Finset.mul_sum,
        Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro j _
      ring
    _ = ∑ j ∈ Finset.Iic n,
        (∑ k ∈ Finset.Iic n,
          (-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose n k : ℝ) *
            (multiChoose k j : ℝ) * (multiChoose (n - k) m : ℝ)) * a (n - j) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro j _
      rw [Finset.sum_mul]
    _ = ∑ j ∈ Finset.Iic n,
        (if j = n - m then (multiChoose n m : ℝ) else 0) * a (n - j) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [multi_choose_diff_coefficient n m j hmn (Finset.mem_Iic.mp hj)]
    _ = (multiChoose n m : ℝ) * a m := by
      rw [Finset.sum_eq_single (n - m)]
      · simp only [if_pos]
        congr 2
        funext i
        exact Nat.sub_sub_self (hmn i)
      · intro j _ hj
        rw [if_neg hj, zero_mul]
      · intro h
        exact (h (Finset.mem_Iic.mpr (tsub_le_self : n - m ≤ n))).elim

end Submission.Helpers
