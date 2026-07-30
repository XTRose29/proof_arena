import Mathlib
import ChallengeDeps

open LeanEval.Analysis
open MeasureTheory
open scoped BigOperators NNReal Polynomial

set_option maxHeartbeats 800000

noncomputable def testMoment {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    MvPolynomial (Fin d) ℝ →ₗ[ℝ] ℝ :=
  Finsupp.lsum ℝ fun s : Fin d →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm (a fun i => s i)

lemma testMoment_monomial {d : ℕ} (a : (Fin d → ℕ) → ℝ) (s : Fin d →₀ ℕ) (c : ℝ) :
    testMoment a (MvPolynomial.monomial s c) = c * a (fun i => s i) := by
  change (Finsupp.lsum ℝ fun t : Fin d →₀ ℕ =>
    (LinearMap.ringLmapEquivSelf ℝ ℝ ℝ).symm (a fun i => t i))
      (Finsupp.single s c) = _
  rw [Finsupp.lsum_single]
  simp

noncomputable def testCoord {d : ℕ} (i : Fin d) (N j : ℕ) : MvPolynomial (Fin d) ℝ :=
  Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i) (bernsteinPolynomial ℝ N j)

noncomputable def testGrid (d N : ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun _ : Fin d => Finset.range (N + 1)

noncomputable def testBasis {d : ℕ} (N : ℕ) (j : Fin d → ℕ) :
    MvPolynomial (Fin d) ℝ :=
  ∏ i, testCoord i N (j i)

lemma testBasis_sum {d : ℕ} (N : ℕ) :
    (∑ j ∈ testGrid d N, testBasis N j) = (1 : MvPolynomial (Fin d) ℝ) := by
  simp only [testGrid, testBasis]
  rw [Finset.sum_prod_piFinset]
  simp only [testCoord, ← map_sum, bernsteinPolynomial.sum, map_one, Finset.prod_const_one]

theorem test_desc (N r : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
        (j.descFactorial r : ℝ) • bernsteinPolynomial ℝ N j) =
      (N.descFactorial r : ℝ) • Polynomial.X ^ r := by
  let Y : ℝ[X] := Polynomial.X
  let E : (ℝ[X])[X] →+* ℝ[X] :=
    Polynomial.eval₂RingHom
      (Polynomial.eval₂RingHom Polynomial.C (1 - (Polynomial.X : ℝ[X])))
      (Polynomial.X : ℝ[X])
  trans E (Polynomial.derivative^[r]
      ((Polynomial.X + Polynomial.C Y) ^ N)) * Polynomial.X ^ r
  · rw [add_pow, Polynomial.iterate_derivative_sum, map_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    have hterm :
        (Polynomial.X ^ j * Polynomial.C Y ^ (N - j) *
          (N.choose j : (ℝ[X])[X])) =
          Polynomial.C ((N.choose j : ℝ[X]) * Y ^ (N - j)) * Polynomial.X ^ j := by
      simp [Polynomial.C_mul, mul_comm, mul_left_comm]
    rw [hterm, Polynomial.iterate_derivative_C_mul,
      Polynomial.iterate_derivative_X_pow_eq_smul]
    by_cases hrj : r ≤ j
    · have hp : (Polynomial.X : ℝ[X]) ^ j =
          Polynomial.X ^ r * Polynomial.X ^ (j - r) := by
        rw [← pow_add, Nat.add_sub_of_le hrj]
      simp [E, Y, bernsteinPolynomial, Polynomial.coe_eval₂RingHom,
        Polynomial.eval₂_pow, Algebra.smul_def, hp,
        mul_comm, mul_left_comm, mul_assoc]
    · have hjr : j < r := Nat.lt_of_not_ge hrj
      simp [Nat.descFactorial_eq_zero_iff_lt.mpr hjr]
  · rw [Polynomial.iterate_derivative_X_add_pow]
    simp [E, Y, Polynomial.coe_eval₂RingHom, Polynomial.eval₂_pow,
      Polynomial.eval₂_add, Algebra.smul_def]

lemma test_coord_desc {d : ℕ} (i : Fin d) (N r : ℕ) :
    (∑ j ∈ Finset.range (N + 1),
        (j.descFactorial r : ℝ) • testCoord i N j) =
      (N.descFactorial r : ℝ) • MvPolynomial.X i ^ r := by
  simpa [testCoord, map_sum, map_smul, Algebra.smul_def] using congrArg
    (Polynomial.eval₂RingHom MvPolynomial.C (MvPolynomial.X i)) (test_desc N r)

noncomputable def testMultiDesc {d : ℕ} (N : ℕ) (r : Fin d → ℕ) : ℕ :=
  ∏ i, N.descFactorial (r i)

lemma test_basis_desc {d : ℕ} (N : ℕ) (r : Fin d → ℕ) :
    (∑ j ∈ testGrid d N,
        ((∏ i, (j i).descFactorial (r i) : ℕ) : ℝ) • testBasis N j) =
      ((testMultiDesc N r : ℕ) : ℝ) •
        ∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ r i := by
  simp only [testGrid, testBasis]
  calc
    (∑ j ∈ Fintype.piFinset fun _ : Fin d => Finset.range (N + 1),
        ((∏ i, (j i).descFactorial (r i) : ℕ) : ℝ) • ∏ i, testCoord i N (j i)) =
        ∑ j ∈ Fintype.piFinset fun _ : Fin d => Finset.range (N + 1),
          ∏ i, (((j i).descFactorial (r i) : ℕ) : ℝ) • testCoord i N (j i) := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [Nat.cast_prod]
      exact (Finset.prod_smul Finset.univ
          (fun i => ((j i).descFactorial (r i) : ℝ))
          (fun i => testCoord i N (j i))).symm
    _ = ∏ i, ∑ j ∈ Finset.range (N + 1),
          (((j.descFactorial (r i) : ℕ) : ℝ) • testCoord i N j) :=
      Finset.sum_prod_piFinset (Finset.range (N + 1))
        (fun i j => (((j.descFactorial (r i) : ℕ) : ℝ) • testCoord i N j))
    _ = ∏ i, (((N.descFactorial (r i) : ℕ) : ℝ) •
          (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ r i) := by
      congr 1
      funext i
      simpa only [Nat.cast_descFactorial] using test_coord_desc i N (r i)
    _ = ((testMultiDesc N r : ℕ) : ℝ) •
        ∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ r i := by
      rw [testMultiDesc, Nat.cast_prod]
      exact Finset.prod_smul Finset.univ
          (fun i => ((N.descFactorial (r i) : ℕ) : ℝ))
          (fun i => (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ r i)

lemma testMoment_prod_X {d : ℕ} (a : (Fin d → ℕ) → ℝ) (e : Fin d → ℕ) :
    testMoment a (∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ e i) = a e := by
  rw [MvPolynomial.prod_X_pow, testMoment_monomial]
  simp

lemma test_one_sub_pow {d : ℕ} (i : Fin d) (k : ℕ) :
    (1 - MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ k =
      ∑ r ∈ Finset.range (k + 1),
        ((-1 : ℝ) ^ r * k.choose r) • MvPolynomial.X i ^ r := by
  rw [show (1 - MvPolynomial.X i : MvPolynomial (Fin d) ℝ) =
    -(MvPolynomial.X i : MvPolynomial (Fin d) ℝ) + 1 by ring, add_pow]
  refine Finset.sum_congr rfl fun r hr => ?_
  rw [neg_pow, MvPolynomial.smul_eq_C_mul]
  simp only [one_pow, mul_one]
  have hchoose : (k.choose r : MvPolynomial (Fin d) ℝ) =
      MvPolynomial.C (k.choose r : ℝ) := by norm_cast
  have hneg : ((-1 : MvPolynomial (Fin d) ℝ) ^ r) =
      MvPolynomial.C ((-1 : ℝ) ^ r) := by
    rw [map_pow]
    norm_num
  rw [hchoose, hneg, map_mul]
  ring

noncomputable def testBox {d : ℕ} (k : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => Finset.range (k i + 1)

lemma test_poly_expand {d : ℕ} (n k : Fin d → ℕ) :
    (∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ (n i - k i) *
        (1 - MvPolynomial.X i) ^ k i) =
      ∑ r ∈ testBox k,
        ((-1 : ℝ) ^ (∑ i, r i) * (multiChoose k r : ℝ)) •
          ∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ (n i - k i + r i) := by
  simp_rw [test_one_sub_pow, Finset.mul_sum]
  rw [testBox, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp_rw [mul_smul_comm]
  rw [Finset.prod_smul Finset.univ]
  congr 1
  · simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, multiChoose,
      Nat.cast_prod]
  · apply Finset.prod_congr rfl
    intro i hi
    rw [← pow_add]

lemma test_one_sub_pow_rev {d : ℕ} (i : Fin d) (k : ℕ) :
    (1 - MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ k =
      ∑ j ∈ Finset.range (k + 1),
        ((-1 : ℝ) ^ (k - j) * k.choose j) • MvPolynomial.X i ^ (k - j) := by
  rw [test_one_sub_pow]
  conv_lhs => rw [← Finset.sum_range_reflect
    (fun r => ((-1 : ℝ) ^ r * k.choose r) •
      (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ r) (k + 1)]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hjk : j ≤ k := Nat.le_of_lt_succ (by simpa using Finset.mem_range.mp hj)
  simp only [Nat.add_sub_cancel_right, Nat.choose_symm hjk]

lemma testBox_eq_Iic {d : ℕ} (k : Fin d → ℕ) : testBox k = Finset.Iic k := by
  ext j
  simp [testBox, Pi.le_def]

lemma test_poly_expand_rev {d : ℕ} (n k : Fin d → ℕ) (hkn : k ≤ n) :
    (∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ (n i - k i) *
        (1 - MvPolynomial.X i) ^ k i) =
      ∑ j ∈ testBox k,
        ((-1 : ℝ) ^ (∑ i, (k i - j i)) * (multiChoose k j : ℝ)) •
          ∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ (n i - j i) := by
  simp_rw [test_one_sub_pow_rev, Finset.mul_sum]
  rw [testBox, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp_rw [mul_smul_comm]
  rw [Finset.prod_smul Finset.univ]
  congr 1
  · simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, multiChoose,
      Nat.cast_prod]
  · apply Finset.prod_congr rfl
    intro i hi
    have hji : j i ≤ k i := Nat.le_of_lt_succ <| by
      simpa using (Fintype.mem_piFinset.mp hj i)
    rw [← pow_add, Nat.sub_add_sub_cancel (hkn i) hji]

lemma testMoment_poly {d : ℕ} (a : (Fin d → ℕ) → ℝ) (n k : Fin d → ℕ)
    (hkn : k ≤ n) :
    testMoment a (∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ (n i - k i) *
        (1 - MvPolynomial.X i) ^ k i) = diff a k n := by
  rw [test_poly_expand_rev n k hkn, map_sum]
  simp only [map_smul, testMoment_prod_X]
  rw [testBox_eq_Iic]
  rfl

def testConstIndex (d N : ℕ) : Fin d → ℕ := fun _ => N

lemma test_mem_grid_le {d N : ℕ} {j : Fin d → ℕ} (hj : j ∈ testGrid d N) :
    j ≤ testConstIndex d N := by
  intro i
  exact Nat.le_of_lt_succ <| by
    simpa [testGrid, testConstIndex] using Fintype.mem_piFinset.mp hj i

lemma testCoord_eq {d : ℕ} (i : Fin d) (N j : ℕ) :
    testCoord i N j = (N.choose j : ℝ) •
      (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ j *
        (1 - MvPolynomial.X i) ^ (N - j) := by
  simp [testCoord, bernsteinPolynomial, Polynomial.coe_eval₂RingHom,
    Polynomial.eval₂_pow, Polynomial.eval₂_sub, MvPolynomial.smul_eq_C_mul, mul_assoc]

lemma testBasis_eq {d N : ℕ} {j : Fin d → ℕ} (hj : j ∈ testGrid d N) :
    testBasis N j = (multiChoose (testConstIndex d N) j : ℝ) •
      ∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^
          (testConstIndex d N i - (testConstIndex d N - j) i) *
        (1 - MvPolynomial.X i) ^ ((testConstIndex d N - j) i) := by
  rw [testBasis]
  simp_rw [testCoord_eq]
  simp_rw [smul_mul_assoc]
  rw [Finset.prod_smul Finset.univ]
  congr 1
  · simp [multiChoose, testConstIndex]
  · apply Finset.prod_congr rfl
    intro i hi
    have hji := test_mem_grid_le hj i
    simp only [Pi.sub_apply, testConstIndex]
    have hji' : j i ≤ N := by simpa [testConstIndex] using hji
    rw [Nat.sub_sub_self hji']

lemma testMoment_basis {d N : ℕ} (a : (Fin d → ℕ) → ℝ) {j : Fin d → ℕ}
    (hj : j ∈ testGrid d N) :
    testMoment a (testBasis N j) =
      (multiChoose (testConstIndex d N) j : ℝ) *
        diff a (testConstIndex d N - j) (testConstIndex d N) := by
  rw [testBasis_eq hj, map_smul, testMoment_poly]
  · rfl
  · intro i
    exact Nat.sub_le _ _

noncomputable def testWeight {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ)
    (j : Fin d → ℕ) : ℝ :=
  testMoment a (testBasis N j)

lemma testWeight_nonneg {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) {N : ℕ} {j : Fin d → ℕ}
    (hj : j ∈ testGrid d N) : 0 ≤ testWeight a N j := by
  rw [testWeight, testMoment_basis a hj]
  exact mul_nonneg (Nat.cast_nonneg _) (ha _ _ fun i => Nat.sub_le _ _)

lemma testWeight_coe_toNNReal {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) {N : ℕ} {j : Fin d → ℕ}
    (hj : j ∈ testGrid d N) :
    ((Real.toNNReal (testWeight a N j) : ℝ≥0) : ℝ) = testWeight a N j :=
  Real.coe_toNNReal _ (testWeight_nonneg ha hj)

lemma testMoment_one {d : ℕ} (a : (Fin d → ℕ) → ℝ) :
    testMoment a 1 = a 0 := by
  change testMoment a (MvPolynomial.monomial 0 1) = a 0
  rw [testMoment_monomial]
  simp only [one_mul]
  congr 1

lemma testWeight_sum {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    ∑ j ∈ testGrid d N, testWeight a N j = a 0 := by
  unfold testWeight
  rw [← map_sum, testBasis_sum, testMoment_one]

lemma testWeight_desc_sum {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ)
    (r : Fin d → ℕ) :
    ∑ j ∈ testGrid d N,
        (∏ i, (j i).descFactorial (r i) : ℕ) * testWeight a N j =
      testMultiDesc N r * a r := by
  unfold testWeight
  calc
    (∑ j ∈ testGrid d N,
        (∏ i, (j i).descFactorial (r i) : ℕ) * testMoment a (testBasis N j)) =
        testMoment a (∑ j ∈ testGrid d N,
          ((∏ i, (j i).descFactorial (r i) : ℕ) : ℝ) • testBasis N j) := by
      simp only [map_sum, map_smul, smul_eq_mul]
    _ = testMoment a (((testMultiDesc N r : ℕ) : ℝ) •
          ∏ i, (MvPolynomial.X i : MvPolynomial (Fin d) ℝ) ^ r i) := by
      rw [test_basis_desc]
    _ = testMultiDesc N r * a r := by
      rw [map_smul, testMoment_prod_X]
      simp only [smul_eq_mul]

lemma test_mul_descFactorial (x r : ℕ) :
    x * x.descFactorial r = x.descFactorial (r + 1) + r * x.descFactorial r := by
  by_cases hrx : r ≤ x
  · rw [Nat.descFactorial_succ]
    nth_rw 1 [← Nat.sub_add_cancel hrx]
    rw [add_mul]
  · have hxr : x < r := Nat.lt_of_not_ge hrx
    rw [Nat.descFactorial_eq_zero_iff_lt.mpr hxr,
      Nat.descFactorial_eq_zero_iff_lt.mpr (hxr.trans_le (Nat.le_add_right r 1))]
    simp

lemma test_pow_stirling (x m : ℕ) :
    x ^ m = ∑ r ∈ Finset.range (m + 1),
      Nat.stirlingSecond m r * x.descFactorial r := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [pow_succ, ih, Finset.sum_mul]
    conv_rhs => rw [Finset.sum_range_succ']
    simp only [Nat.stirlingSecond_succ_zero, zero_mul]
    have hrewrite :
        (∑ r ∈ Finset.range (m + 1),
          (Nat.stirlingSecond m r * x.descFactorial r) * x) =
        ∑ r ∈ Finset.range (m + 1),
          Nat.stirlingSecond m r *
            (x.descFactorial (r + 1) + r * x.descFactorial r) := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [mul_assoc, mul_comm (x.descFactorial r) x, test_mul_descFactorial]
    rw [hrewrite]
    simp_rw [mul_add]
    rw [Finset.sum_add_distrib]
    have hshift :
        (∑ r ∈ Finset.range (m + 1),
          Nat.stirlingSecond m r * (r * x.descFactorial r)) =
        ∑ r ∈ Finset.range (m + 1),
          (r + 1) * Nat.stirlingSecond m (r + 1) * x.descFactorial (r + 1) := by
      rw [Finset.sum_range_succ', Finset.sum_range_succ]
      simp only [Nat.stirlingSecond_eq_zero_of_lt (Nat.lt_succ_self m), zero_mul,
        mul_zero, add_zero]
      change
        (∑ r ∈ Finset.range m, Nat.stirlingSecond m (r + 1) *
          ((r + 1) * x.descFactorial (r + 1))) =
        ∑ r ∈ Finset.range m, (r + 1) * Nat.stirlingSecond m (r + 1) *
          x.descFactorial (r + 1)
      refine Finset.sum_congr rfl fun r hr => ?_
      ring
    rw [hshift]
    simp_rw [Nat.stirlingSecond_succ_succ, add_mul]
    simp_rw [Finset.sum_add_distrib]
    ring

noncomputable def testMultiStirling {d : ℕ} (m r : Fin d → ℕ) : ℕ :=
  ∏ i, Nat.stirlingSecond (m i) (r i)

lemma test_multi_pow_stirling {d : ℕ} (j m : Fin d → ℕ) :
    (∏ i, (j i) ^ (m i)) =
      ∑ r ∈ testBox m, testMultiStirling m r *
        ∏ i, (j i).descFactorial (r i) := by
  simp_rw [test_pow_stirling]
  rw [testBox, Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun r hr => ?_
  simp [testMultiStirling, Finset.prod_mul_distrib]

lemma testWeight_pow_sum {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ)
    (m : Fin d → ℕ) :
    ∑ j ∈ testGrid d N, (∏ i, (j i) ^ (m i) : ℕ) * testWeight a N j =
      ∑ r ∈ testBox m,
        testMultiStirling m r * testMultiDesc N r * a r := by
  calc
    (∑ j ∈ testGrid d N, (∏ i, (j i) ^ (m i) : ℕ) * testWeight a N j) =
        ∑ j ∈ testGrid d N, (∑ r ∈ testBox m,
          testMultiStirling m r * ∏ i, (j i).descFactorial (r i)) *
            testWeight a N j := by
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [test_multi_pow_stirling]
    _ = ∑ r ∈ testBox m, testMultiStirling m r *
          (∑ j ∈ testGrid d N,
            (∏ i, (j i).descFactorial (r i) : ℕ) * testWeight a N j) := by
      push_cast
      simp_rw [Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      ring
    _ = ∑ r ∈ testBox m,
        testMultiStirling m r * testMultiDesc N r * a r := by
      refine Finset.sum_congr rfl fun r hr => ?_
      rw [testWeight_desc_sum]
      ring

noncomputable def testGridPoint {d : ℕ} (N : ℕ) (j : Fin d → ℕ) :
    EuclideanSpace ℝ (Fin d) :=
  WithLp.toLp 2 fun i => (j i : ℝ) / N

lemma testGridPoint_mem_cube {d N : ℕ} (hN : 0 < N) {j : Fin d → ℕ}
    (hj : j ∈ testGrid d N) : testGridPoint N j ∈ cube d := by
  intro i
  change (0 : ℝ) ≤ (j i : ℝ) / N ∧ (j i : ℝ) / N ≤ 1
  constructor
  · exact div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)
  · rw [div_le_one (by exact_mod_cast hN)]
    exact_mod_cast test_mem_grid_le hj i

noncomputable def testDiracFinite {α : Type*} [MeasurableSpace α] (x : α) :
    FiniteMeasure α :=
  show FiniteMeasure α from ⟨Measure.dirac x, inferInstance⟩

lemma test_cube_measurable (d : ℕ) : MeasurableSet (cube d) := by
  have hclosed : IsClosed (⋂ i : Fin d,
      {x : EuclideanSpace ℝ (Fin d) | x i ∈ Set.Icc (0 : ℝ) 1}) := by
    apply isClosed_iInter
    intro i
    exact isClosed_Icc.preimage (EuclideanSpace.proj (𝕜 := ℝ) i).continuous
  apply hclosed.measurableSet.congr
  ext x
  simp [cube]

noncomputable def testApprox {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    FiniteMeasure (EuclideanSpace ℝ (Fin d)) :=
  show FiniteMeasure (EuclideanSpace ℝ (Fin d)) from
    ⟨∑ j ∈ testGrid d (N + 1),
      Real.toNNReal (testWeight a (N + 1) j) •
        Measure.dirac (testGridPoint (N + 1) j), inferInstance⟩

lemma testApprox_mass {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) (N : ℕ) :
    (testApprox a N).mass = Real.toNNReal (a 0) := by
  change (testApprox a N) Set.univ = Real.toNNReal (a 0)
  simp only [testApprox, FiniteMeasure.mk_apply, Measure.coe_finsetSum, Finset.sum_apply,
    Measure.smul_apply, Measure.dirac_apply' _ MeasurableSet.univ,
    Set.indicator_of_mem (Set.mem_univ _), Pi.one_apply, ENNReal.smul_one]
  rw [ENNReal.toNNReal_sum]
  · simp only [ENNReal.toNNReal_coe]
    rw [← Real.toNNReal_sum_of_nonneg fun j hj => testWeight_nonneg ha hj,
      testWeight_sum]
  · intro j hj
    simp

lemma testApprox_compl_cube {d : ℕ} (a : (Fin d → ℕ) → ℝ) (N : ℕ) :
    testApprox a N (cube d)ᶜ = 0 := by
  apply (FiniteMeasure.null_iff_toMeasure_null (testApprox a N) (cube d)ᶜ).mpr
  change (∑ j ∈ testGrid d (N + 1),
    Real.toNNReal (testWeight a (N + 1) j) •
      Measure.dirac (testGridPoint (N + 1) j)) (cube d)ᶜ = 0
  simp only [Measure.coe_finsetSum, Finset.sum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply, Measure.dirac_apply' _ (test_cube_measurable d).compl]
  simp [testGridPoint_mem_cube (Nat.succ_pos N) hj]

noncomputable def testClamp (x : ℝ) : ℝ :=
  Set.projIcc (0 : ℝ) 1 zero_le_one x

lemma testClamp_continuous : Continuous testClamp := by
  exact continuous_subtype_val.comp continuous_projIcc

lemma testClamp_mem (x : ℝ) : testClamp x ∈ Set.Icc (0 : ℝ) 1 :=
  (Set.projIcc (0 : ℝ) 1 zero_le_one x).prop

lemma testClamp_of_mem {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 1) : testClamp x = x := by
  simpa [testClamp] using congrArg Subtype.val (Set.projIcc_of_mem zero_le_one hx)

noncomputable def testClampedMonomial {d : ℕ} (m : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ℝ :=
  ∏ i, testClamp (x i) ^ m i

lemma testClampedMonomial_continuous {d : ℕ} (m : Fin d → ℕ) :
    Continuous (testClampedMonomial m) := by
  unfold testClampedMonomial
  apply continuous_finsetProd Finset.univ
  intro i hi
  exact (testClamp_continuous.comp (EuclideanSpace.proj (𝕜 := ℝ) i).continuous).pow _

lemma testClampedMonomial_nonneg {d : ℕ} (m : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : 0 ≤ testClampedMonomial m x := by
  apply Finset.prod_nonneg
  intro i hi
  exact pow_nonneg (testClamp_mem (x i)).1 _

lemma testClampedMonomial_norm_le {d : ℕ} (m : Fin d → ℕ)
    (x : EuclideanSpace ℝ (Fin d)) : ‖testClampedMonomial m x‖ ≤ 1 := by
  rw [Real.norm_eq_abs, abs_of_nonneg (testClampedMonomial_nonneg m x)]
  apply Finset.prod_le_one
  · intro i hi
    exact pow_nonneg (testClamp_mem (x i)).1 _
  · intro i hi
    exact pow_le_one₀ (testClamp_mem (x i)).1 (testClamp_mem (x i)).2

noncomputable def testClampedBCF {d : ℕ} (m : Fin d → ℕ) :
    BoundedContinuousFunction (EuclideanSpace ℝ (Fin d)) ℝ :=
  BoundedContinuousFunction.ofNormedAddCommGroup (testClampedMonomial m)
    (testClampedMonomial_continuous m) 1 (testClampedMonomial_norm_le m)

lemma testClampedMonomial_eq {d : ℕ} (m : Fin d → ℕ)
    {x : EuclideanSpace ℝ (Fin d)} (hx : x ∈ cube d) :
    testClampedMonomial m x = monomial m x := by
  simp only [testClampedMonomial, monomial]
  apply Finset.prod_congr rfl
  intro i hi
  rw [testClamp_of_mem (hx i)]

lemma test_grid_monomial {d N : ℕ} (j m : Fin d → ℕ) :
    monomial m (testGridPoint N j) =
      (∏ i, (j i) ^ (m i) : ℕ) / (N : ℝ) ^ (∑ i, m i) := by
  change (∏ i, ((j i : ℝ) / N) ^ m i) = _
  simp only [div_pow, Finset.prod_div_distrib, Finset.prod_pow_eq_pow_sum,
    Nat.cast_prod, Nat.cast_pow]

lemma test_integral_approx {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) (N : ℕ)
    (m : Fin d → ℕ) :
    ∫ x, testClampedMonomial m x ∂(testApprox a N) =
      ∑ r ∈ testBox m,
        ((testMultiStirling m r * testMultiDesc (N + 1) r : ℕ) : ℝ) /
          ((N + 1 : ℕ) : ℝ) ^ (∑ i, m i) * a r := by
  change ∫ x, testClampedMonomial m x ∂(∑ j ∈ testGrid d (N + 1),
    Real.toNNReal (testWeight a (N + 1) j) •
      Measure.dirac (testGridPoint (N + 1) j)) = _
  rw [integral_finsetSum_measure]
  · simp only [integral_smul_nnreal_measure, integral_dirac]
    calc
      _ = ∑ j ∈ testGrid d (N + 1),
          (((∏ i, (j i) ^ (m i) : ℕ) : ℝ) * testWeight a (N + 1) j) /
            ((N + 1 : ℕ) : ℝ) ^ (∑ i, m i) := by
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [testClampedMonomial_eq m
          (testGridPoint_mem_cube (Nat.succ_pos N) hj), test_grid_monomial]
        change ((Real.toNNReal (testWeight a (N + 1) j) : ℝ≥0) : ℝ) * _ = _
        rw [testWeight_coe_toNNReal ha hj]
        ring
      _ = _ := by
        rw [← Finset.sum_div]
        · rw [testWeight_pow_sum]
          simp_rw [Finset.sum_div]
          refine Finset.sum_congr rfl fun r hr => ?_
          push_cast
          ring
  · intro j hj
    exact (testClampedBCF m).integrable (μ :=
      Real.toNNReal (testWeight a (N + 1) j) •
        Measure.dirac (testGridPoint (N + 1) j))

lemma test_desc_ratio_tendsto (r m : ℕ) (hrm : r ≤ m) :
    Filter.Tendsto
      (fun N : ℕ =>
        (((N + 1).descFactorial r : ℕ) : ℝ) / (((N + 1 : ℕ) : ℝ) ^ m))
      Filter.atTop (nhds (if r = m then 1 else 0)) := by
  let P : ℝ[X] := descPochhammer ℝ r
  let Q : ℝ[X] := Polynomial.X ^ m
  have hP : P.degree = r := by
    rw [Polynomial.degree_eq_natDegree (monic_descPochhammer ℝ r).ne_zero]
    simp [descPochhammer_natDegree]
  have hQ : Q.degree = m := by
    simp [Q]
  by_cases hrmeq : r = m
  · subst m
    have hreal : Filter.Tendsto (fun x : ℝ => P.eval x / Q.eval x)
        Filter.atTop (nhds 1) := by
      convert P.div_tendsto_atTop_leadingCoeff_div_of_degree_eq Q (hP.trans hQ.symm) using 1
      simp [P, Q, monic_descPochhammer]
    have hbase : Filter.Tendsto
        (fun N : ℕ => ((N.descFactorial r : ℕ) : ℝ) / ((N : ℝ) ^ r))
        Filter.atTop (nhds 1) := by
      have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      apply hcomp.congr'
      exact Filter.Eventually.of_forall fun N => by
        dsimp [P, Q]
        rw [descPochhammer_eval_eq_descFactorial]
        simp
    simpa [Nat.cast_add, Nat.cast_one] using
      (Filter.tendsto_add_atTop_iff_nat 1).2 hbase
  · have hrlt : r < m := lt_of_le_of_ne hrm hrmeq
    have hdeg : P.degree < Q.degree := by
      rw [hP, hQ]
      exact_mod_cast hrlt
    have hreal : Filter.Tendsto (fun x : ℝ => P.eval x / Q.eval x)
        Filter.atTop (nhds 0) :=
      P.div_tendsto_atTop_zero_of_degree_lt Q hdeg
    have hbase : Filter.Tendsto
        (fun N : ℕ => ((N.descFactorial r : ℕ) : ℝ) / ((N : ℝ) ^ m))
        Filter.atTop (nhds 0) := by
      have hcomp := hreal.comp (tendsto_natCast_atTop_atTop (R := ℝ))
      apply hcomp.congr'
      exact Filter.Eventually.of_forall fun N => by
        dsimp [P, Q]
        rw [descPochhammer_eval_eq_descFactorial]
        simp
    simpa only [Nat.cast_add, Nat.cast_one, if_neg hrmeq] using
      (Filter.tendsto_add_atTop_iff_nat 1).2 hbase

lemma test_multi_desc_ratio_eq {d : ℕ} (N : ℕ) (r m : Fin d → ℕ) :
    ((testMultiDesc (N + 1) r : ℕ) : ℝ) /
        (((N + 1 : ℕ) : ℝ) ^ (∑ i, m i)) =
      ∏ i, ((((N + 1).descFactorial (r i) : ℕ) : ℝ) /
        (((N + 1 : ℕ) : ℝ) ^ (m i))) := by
  simp [testMultiDesc, Nat.cast_prod, Finset.prod_div_distrib,
    Finset.prod_pow_eq_pow_sum]

lemma test_multi_desc_ratio_tendsto {d : ℕ} (r m : Fin d → ℕ) (hrm : r ≤ m) :
    Filter.Tendsto
      (fun N : ℕ => ((testMultiDesc (N + 1) r : ℕ) : ℝ) /
        (((N + 1 : ℕ) : ℝ) ^ (∑ i, m i)))
      Filter.atTop (nhds (if r = m then 1 else 0)) := by
  have hprod : Filter.Tendsto
      (fun N : ℕ => ∏ i, ((((N + 1).descFactorial (r i) : ℕ) : ℝ) /
        (((N + 1 : ℕ) : ℝ) ^ (m i))))
      Filter.atTop (nhds (∏ i, if r i = m i then (1 : ℝ) else 0)) :=
    tendsto_finsetProd Finset.univ fun i hi => test_desc_ratio_tendsto (r i) (m i) (hrm i)
  have hlimit : (∏ i, if r i = m i then (1 : ℝ) else 0) =
      if r = m then 1 else 0 := by
    by_cases h : r = m
    · subst r
      simp
    · have hi : ∃ i, r i ≠ m i := by
        by_contra hn
        apply h
        funext i
        by_contra hi
        exact hn ⟨i, hi⟩
      obtain ⟨i, hi⟩ := hi
      rw [if_neg h]
      exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)
  rw [← hlimit]
  exact hprod.congr' (Filter.Eventually.of_forall fun N => (test_multi_desc_ratio_eq N r m).symm)

lemma test_integral_approx_tendsto {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) (m : Fin d → ℕ) :
    Filter.Tendsto (fun N : ℕ => ∫ x, testClampedMonomial m x ∂(testApprox a N))
      Filter.atTop (nhds (a m)) := by
  have hterm (r : Fin d → ℕ) (hr : r ∈ testBox m) :
      Filter.Tendsto
        (fun N : ℕ =>
          ((testMultiStirling m r * testMultiDesc (N + 1) r : ℕ) : ℝ) /
            (((N + 1 : ℕ) : ℝ) ^ (∑ i, m i)) * a r)
        Filter.atTop (nhds (if r = m then a m else 0)) := by
    have hrm : r ≤ m := by
      rw [testBox_eq_Iic] at hr
      exact Finset.mem_Iic.mp hr
    have hratio := test_multi_desc_ratio_tendsto r m hrm
    have hmul : Filter.Tendsto
        (fun N : ℕ => ((testMultiStirling m r : ℕ) : ℝ) *
          (((testMultiDesc (N + 1) r : ℕ) : ℝ) /
            (((N + 1 : ℕ) : ℝ) ^ (∑ i, m i))) * a r)
        Filter.atTop
          (nhds (((testMultiStirling m r : ℕ) : ℝ) *
            (if r = m then 1 else 0) * a r)) :=
      (tendsto_const_nhds.mul hratio).mul tendsto_const_nhds
    convert hmul using 1
    · funext N
      push_cast
      ring
    · by_cases h : r = m
      · subst r
        have hstir : testMultiStirling m m = 1 := by
          simp [testMultiStirling, Nat.stirlingSecond_self]
        rw [hstir]
        simp
      · simp [h]
  have hsum := tendsto_finsetSum (testBox m) hterm
  have hm : m ∈ testBox m := by
    simp [testBox]
  have hlimit : (∑ r ∈ testBox m, if r = m then a m else 0) = a m := by
    simp [hm]
  rw [hlimit] at hsum
  exact hsum.congr' (Filter.Eventually.of_forall fun N => (test_integral_approx ha N m).symm)

lemma test_cube_compact (d : ℕ) : IsCompact (cube d) := by
  let e := (EuclideanSpace.equiv (Fin d) ℝ).toHomeomorph
  have hpi : IsCompact {f : Fin d → ℝ | ∀ i, f i ∈ Set.Icc (0 : ℝ) 1} := by
    simpa [Set.pi] using
      (isCompact_univ_pi (fun _ : Fin d =>
        (isCompact_Icc : IsCompact (Set.Icc (0 : ℝ) 1))))
  change IsCompact (e ⁻¹' {f : Fin d → ℝ | ∀ i, f i ∈ Set.Icc (0 : ℝ) 1})
  exact e.isCompact_preimage.mpr hpi

lemma test_exists_measure_clamped {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) :
    ∃ μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)),
      μ (cube d)ᶜ = 0 ∧
        ∀ m, a m = ∫ x, testClampedMonomial m x ∂μ := by
  let K : Set (FiniteMeasure (EuclideanSpace ℝ (Fin d))) :=
    {μ | μ.mass ≤ Real.toNNReal (a 0) ∧ μ (cube d)ᶜ = 0}
  have hK : IsCompact K := by
    exact isCompact_setOf_finiteMeasure_le_of_isCompact
      (Real.toNNReal (a 0)) (test_cube_compact d)
  have hmem (N : ℕ) : testApprox a N ∈ K := by
    constructor
    · rw [testApprox_mass ha]
    · exact testApprox_compl_cube a N
  have hfreq : ∃ᶠ N : ℕ in Filter.atTop, testApprox a N ∈ K :=
    (Filter.Eventually.of_forall hmem).frequently
  obtain ⟨μ, hμK, hμcluster⟩ := hK.exists_mapClusterPt_of_frequently hfreq
  obtain ⟨U, hUtop, hUlim⟩ := mapClusterPt_iff_ultrafilter.mp hμcluster
  refine ⟨μ, hμK.2, fun m => ?_⟩
  have haU := (test_integral_approx_tendsto ha m).mono_left hUtop
  have hμU :=
    (FiniteMeasure.continuous_integral_boundedContinuousFunction
      (testClampedBCF m)).continuousAt.tendsto.comp hUlim
  exact tendsto_nhds_unique haU hμU

lemma test_momentOf_eq_clamped {d : ℕ}
    (μ : FiniteMeasure (EuclideanSpace ℝ (Fin d)))
    (hμ : μ (cube d)ᶜ = 0) (m : Fin d → ℕ) :
    momentOf (μ : Measure (EuclideanSpace ℝ (Fin d))) m =
      ∫ x, testClampedMonomial m x ∂μ := by
  have hnull : (μ : Measure (EuclideanSpace ℝ (Fin d))) (cube d)ᶜ = 0 :=
    (FiniteMeasure.null_iff_toMeasure_null μ (cube d)ᶜ).mp hμ
  have hae : ∀ᵐ x ∂(μ : Measure (EuclideanSpace ℝ (Fin d))), x ∈ cube d :=
    mem_ae_iff.mpr hnull
  have hrestrict : (μ : Measure (EuclideanSpace ℝ (Fin d))).restrict (cube d) = μ :=
    Measure.restrict_eq_self_of_ae_mem hae
  change (∫ x, monomial m x ∂(μ : Measure _).restrict (cube d)) = _
  rw [hrestrict]
  apply integral_congr_ae
  exact hae.mono fun x hx => (testClampedMonomial_eq m hx).symm

lemma test_positive_of_diff {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n) :
    IsPositiveMomentConfiguration a := by
  obtain ⟨μ, hμ, hmoment⟩ := test_exists_measure_clamped ha
  refine ⟨(μ : Measure (EuclideanSpace ℝ (Fin d))), inferInstance, fun m => ?_⟩
  exact (hmoment m).trans (test_momentOf_eq_clamped μ hμ m).symm

lemma test_eval_monomial {d : ℕ} (x : EuclideanSpace ℝ (Fin d))
    (s : Fin d →₀ ℕ) (c : ℝ) :
    MvPolynomial.eval x (MvPolynomial.monomial s c) =
      c * monomial (fun i => s i) x := by
  simp [MvPolynomial.eval_monomial, monomial, Finsupp.prod_fintype]

lemma testMoment_eq_integral {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsFiniteMeasure μ]
    (hmoment : ∀ m, a m = momentOf μ m) (p : MvPolynomial (Fin d) ℝ) :
    testMoment a p = ∫ x in cube d, MvPolynomial.eval x p ∂μ := by
  induction p using MvPolynomial.induction_on' with
  | monomial s c =>
      let e : Fin d → ℕ := fun i => s i
      calc
        testMoment a (MvPolynomial.monomial s c) = c * a e := by
          simpa [e] using testMoment_monomial a s c
        _ = c * momentOf μ e := by rw [hmoment]
        _ = ∫ x in cube d, c * monomial e x ∂μ := by
          rw [momentOf, integral_const_mul]
        _ = ∫ x in cube d, MvPolynomial.eval x (MvPolynomial.monomial s c) ∂μ := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun x => (test_eval_monomial x s c).symm
  | add p q hp hq =>
      have hcont (r : MvPolynomial (Fin d) ℝ) :
          Continuous (fun x : EuclideanSpace ℝ (Fin d) => MvPolynomial.eval x r) :=
        (MvPolynomial.continuous_eval r).comp (EuclideanSpace.equiv (Fin d) ℝ).continuous
      have heval : (fun x : EuclideanSpace ℝ (Fin d) => MvPolynomial.eval x (p + q)) =
          fun x : EuclideanSpace ℝ (Fin d) => MvPolynomial.eval x p + MvPolynomial.eval x q := by
        funext x
        simp
      rw [map_add, heval,
        integral_add
          (ContinuousOn.integrableOn_compact (test_cube_compact d) (hcont p).continuousOn)
          (ContinuousOn.integrableOn_compact (test_cube_compact d) (hcont q).continuousOn), hp, hq]

lemma test_diff_nonneg_of_positive {d : ℕ} {a : (Fin d → ℕ) → ℝ}
    (ha : IsPositiveMomentConfiguration a) :
    ∀ k n : Fin d → ℕ, k ≤ n → 0 ≤ diff a k n := by
  obtain ⟨μ, hμ, hmoment⟩ := ha
  intro k n hkn
  rw [← testMoment_poly a n k hkn, testMoment_eq_integral μ hmoment]
  apply setIntegral_nonneg (test_cube_compact d).measurableSet
  intro x hx
  simp only [map_prod, map_mul, map_pow, MvPolynomial.eval_X, map_sub, map_one]
  apply Finset.prod_nonneg
  intro i hi
  exact mul_nonneg (pow_nonneg (hx i).1 _) (pow_nonneg (sub_nonneg.mpr (hx i).2) _)
