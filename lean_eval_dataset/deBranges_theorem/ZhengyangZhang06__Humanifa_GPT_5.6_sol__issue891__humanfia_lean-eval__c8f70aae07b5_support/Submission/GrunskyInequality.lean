import Submission.AreaTheorem
import Submission.SignedArea
import Mathlib.RingTheory.LaurentSeries

open scoped PowerSeries
open scoped Topology

noncomputable section

namespace Submission

open HahnSeries LaurentSeries
open Filter Metric

/-- The formal exterior map `w⁻¹ A(w)` associated to a power series `A`. -/
noncomputable def formalExteriorMap (A : ℂ⟦X⟧) : ℂ⸨X⸩ :=
  HahnSeries.single (-1) 1 * (A : ℂ⸨X⸩)

lemma formalExteriorMap_pow (A : ℂ⟦X⟧) (n : ℕ) :
    formalExteriorMap A ^ n =
      HahnSeries.single (-(n : ℤ)) 1 * ((A ^ n : ℂ⟦X⟧) : ℂ⸨X⸩) := by
  rw [formalExteriorMap, mul_pow]
  simp

lemma coeff_formalExteriorMap_pow_neg (A : ℂ⟦X⟧) (n q : ℕ) :
    (formalExteriorMap A ^ n).coeff (-(q : ℤ)) =
      if q ≤ n then PowerSeries.coeff (n - q) (A ^ n) else 0 := by
  rw [formalExteriorMap_pow]
  by_cases hqn : q ≤ n
  · rw [if_pos hqn]
    have hindex : ((n - q : ℕ) : ℤ) + -(n : ℤ) = -(q : ℤ) := by omega
    rw [← hindex, HahnSeries.coeff_single_mul_add,
      LaurentSeries.coeff_coe_powerSeries, one_mul]
  · rw [if_neg hqn]
    have hindex : (-(q - n : ℕ) : ℤ) + -(n : ℤ) = -(q : ℤ) := by omega
    rw [← hindex, HahnSeries.coeff_single_mul_add, one_mul,
      PowerSeries.coeff_coe]
    rw [if_pos (by omega)]

lemma coeff_formalExteriorMap_pow (A : ℂ⟦X⟧) (n : ℕ) (e : ℤ) :
    (formalExteriorMap A ^ n).coeff e =
      if e + n < 0 then 0 else PowerSeries.coeff (e + n).natAbs (A ^ n) := by
  rw [formalExteriorMap_pow]
  have hindex : (e + (n : ℤ)) + -(n : ℤ) = e := by ring
  rw [← hindex, HahnSeries.coeff_single_mul_add, one_mul,
    PowerSeries.coeff_coe]
  rw [hindex]

/-- The Faber polynomial obtained by cancelling the lower principal terms recursively. -/
noncomputable def faberPolynomial (A : ℂ⟦X⟧) (n : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ n -
    ∑ k : Fin n,
      Polynomial.C (PowerSeries.coeff (n - k) (A ^ n)) * faberPolynomial A k
termination_by n

lemma faberPolynomial_monic_natDegree (A : ℂ⟦X⟧) (n : ℕ) :
    (faberPolynomial A n).Monic ∧ (faberPolynomial A n).natDegree = n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rw [faberPolynomial]
      let q : Polynomial ℂ :=
        ∑ k : Fin n,
          Polynomial.C (PowerSeries.coeff (n - k) (A ^ n)) * faberPolynomial A k
      have hq : q.degree < (Polynomial.X ^ n : Polynomial ℂ).degree := by
        rw [Polynomial.degree_X_pow]
        apply (Polynomial.degree_lt_iff_coeff_zero q n).2
        intro m hm
        change (∑ k : Fin n,
          Polynomial.C (PowerSeries.coeff (n - k) (A ^ n)) *
            faberPolynomial A k).coeff m = 0
        rw [Polynomial.finsetSum_coeff]
        apply Finset.sum_eq_zero
        intro k hk
        have hkm : (faberPolynomial A k).natDegree < m := by
          rw [(ih k k.isLt).2]
          exact k.isLt.trans_le hm
        rw [Polynomial.coeff_C_mul,
          Polynomial.coeff_eq_zero_of_natDegree_lt hkm, mul_zero]
      have hmonic : ((Polynomial.X ^ n : Polynomial ℂ) - q).Monic :=
        (Polynomial.monic_X_pow n).sub_of_left hq
      refine ⟨hmonic, ?_⟩
      change ((Polynomial.X ^ n : Polynomial ℂ) - q).natDegree = n
      have hdeg := Polynomial.degree_sub_eq_left_of_degree_lt hq
      rw [Polynomial.degree_eq_natDegree hmonic.ne_zero,
        Polynomial.degree_X_pow] at hdeg
      exact_mod_cast hdeg

/-- Formal Laurent expansion of the `n`th Faber polynomial on the exterior map. -/
noncomputable def faberLaurent (A : ℂ⟦X⟧) (n : ℕ) : ℂ⸨X⸩ :=
  Polynomial.eval₂ (algebraMap ℂ ℂ⸨X⸩) (formalExteriorMap A) (faberPolynomial A n)

lemma laurent_algebraMap_mul (c : ℂ) (x : ℂ⸨X⸩) :
    (algebraMap ℂ ℂ⸨X⸩) c * x = c • x := by
  rw [LaurentSeries.algebraMap_apply, HahnSeries.C_mul_eq_smul]

lemma faberLaurent_eq (A : ℂ⟦X⟧) (n : ℕ) :
    faberLaurent A n = formalExteriorMap A ^ n -
      ∑ k : Fin n, PowerSeries.coeff (n - k) (A ^ n) • faberLaurent A k := by
  rw [faberLaurent, faberPolynomial, Polynomial.eval₂_sub,
    Polynomial.eval₂_X_pow]
  change formalExteriorMap A ^ n -
      Polynomial.eval₂ (algebraMap ℂ ℂ⸨X⸩) (formalExteriorMap A)
        (∑ k : Fin n,
          Polynomial.C (PowerSeries.coeff (n - k) (A ^ n)) * faberPolynomial A k) = _
  rw [← Polynomial.coe_eval₂RingHom, map_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  change Polynomial.eval₂ (algebraMap ℂ ℂ⸨X⸩) (formalExteriorMap A)
      (Polynomial.C (PowerSeries.coeff (n - k) (A ^ n)) * faberPolynomial A k) = _
  rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, laurent_algebraMap_mul]
  rfl

lemma coeff_faberLaurent_neg_eq_zero_of_lt (A : ℂ⟦X⟧) (n q : ℕ) (hnq : n < q) :
    (faberLaurent A n).coeff (-(q : ℤ)) = 0 := by
  rw [faberLaurent, Polynomial.eval₂_eq_sum_range, HahnSeries.coeff_sum]
  apply Finset.sum_eq_zero
  intro i hi
  have hi_le : i ≤ n := by
    have hi' := Finset.mem_range.mp hi
    rw [(faberPolynomial_monic_natDegree A n).2] at hi'
    omega
  rw [laurent_algebraMap_mul, HahnSeries.coeff_smul,
    coeff_formalExteriorMap_pow_neg, if_neg (by omega), smul_zero]

lemma coeff_powerSeries_pow_zero {A : ℂ⟦X⟧}
    (hA : PowerSeries.constantCoeff A = 1) (n : ℕ) :
    PowerSeries.coeff 0 (A ^ n) = 1 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff, map_pow, hA, one_pow]

lemma faberLaurent_principal_part {A : ℂ⟦X⟧}
    (hA : PowerSeries.constantCoeff A = 1) (n : ℕ) :
    (faberLaurent A n).coeff (-(n : ℤ)) = 1 ∧
      ∀ q < n, (faberLaurent A n).coeff (-(q : ℤ)) = 0 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      constructor
      · rw [faberLaurent_eq, HahnSeries.coeff_sub,
          coeff_formalExteriorMap_pow_neg, if_pos le_rfl, Nat.sub_self,
          coeff_powerSeries_pow_zero hA, HahnSeries.coeff_sum]
        have hsum :
            ∑ k : Fin n,
                (PowerSeries.coeff (n - k) (A ^ n) • faberLaurent A k).coeff
                  (-(n : ℤ)) = 0 := by
          apply Finset.sum_eq_zero
          intro k hk
          rw [HahnSeries.coeff_smul,
            coeff_faberLaurent_neg_eq_zero_of_lt A k n k.isLt, smul_zero]
        rw [hsum, sub_zero]
      · intro q hqn
        rw [faberLaurent_eq, HahnSeries.coeff_sub,
          coeff_formalExteriorMap_pow_neg, if_pos hqn.le, HahnSeries.coeff_sum]
        let qFin : Fin n := ⟨q, hqn⟩
        have hsum :
            ∑ k : Fin n,
                (PowerSeries.coeff (n - k) (A ^ n) • faberLaurent A k).coeff
                  (-(q : ℤ)) = PowerSeries.coeff (n - q) (A ^ n) := by
          rw [Finset.sum_eq_single qFin]
          · rw [HahnSeries.coeff_smul, (ih q hqn).1, smul_eq_mul, mul_one]
          · intro k hk hkq
            rw [HahnSeries.coeff_smul]
            have hkq' : (k : ℕ) ≠ q := by
              intro heq
              exact hkq (Fin.ext heq)
            by_cases hk_lt_q : (k : ℕ) < q
            · rw [coeff_faberLaurent_neg_eq_zero_of_lt A k q hk_lt_q,
                smul_zero]
            · have hq_lt_k : q < (k : ℕ) := by omega
              rw [(ih k k.isLt).2 q hq_lt_k, smul_zero]
          · simp
        rw [hsum, sub_self]

/-- Formal Taylor series of the analytic exterior factor `exp (-L)`. -/
noncomputable def exteriorFactorPowerSeries (L : ℂ → ℂ) : ℂ⟦X⟧ :=
  PowerSeries.mk fun n => taylorCoeff (exteriorAnalyticFactor L) n

lemma exteriorFactorPowerSeries_constantCoeff {L : ℂ → ℂ} (hL0 : L 0 = 0) :
    PowerSeries.constantCoeff (exteriorFactorPowerSeries L) = 1 := by
  rw [← PowerSeries.coeff_zero_eq_constantCoeff]
  simp [exteriorFactorPowerSeries, taylorCoeff, exteriorAnalyticFactor_zero hL0]

lemma coeff_exteriorFactorPowerSeries_pow {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (Metric.ball 0 R)) (p n : ℕ) :
    PowerSeries.coeff n (exteriorFactorPowerSeries L ^ p) =
      taylorCoeff (fun z => exteriorAnalyticFactor L z ^ p) n := by
  have hE : DifferentiableOn ℂ (exteriorAnalyticFactor L) (Metric.ball 0 R) :=
    exteriorAnalyticFactor_differentiableOn hL
  have hzero : (0 : ℂ) ∈ Metric.ball 0 R := Metric.mem_ball_self hR
  induction p generalizing n with
  | zero =>
      by_cases hn : n = 0
      · subst n
        simp [taylorCoeff]
      · simp [taylorCoeff, hn, iteratedDeriv_const]
  | succ p ih =>
      have hECont : ContDiffAt ℂ n (exteriorAnalyticFactor L) 0 :=
        (hE.contDiffOn Metric.isOpen_ball).contDiffAt
          (Metric.isOpen_ball.mem_nhds hzero)
      rw [pow_succ, PowerSeries.coeff_mul]
      rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
        (fun i j => PowerSeries.coeff i (exteriorFactorPowerSeries L ^ p) *
          PowerSeries.coeff j (exteriorFactorPowerSeries L)) n]
      simp_rw [ih, exteriorFactorPowerSeries, PowerSeries.coeff_mk]
      have hPowCont : ContDiffAt ℂ n
          (fun z => exteriorAnalyticFactor L z ^ p) 0 := hECont.pow p
      rw [← taylorCoeff_mul hPowCont hECont]
      congr 1

lemma taylorCoeff_pow_function (d i : ℕ) :
    taylorCoeff (fun z : ℂ => z ^ d) i = if i = d then 1 else 0 := by
  rw [taylorCoeff, iteratedDeriv_fun_pow_zero]
  by_cases hid : i = d
  · subst i
    simp [Nat.factorial_ne_zero]
  · simp [hid]

lemma taylorCoeff_pow_mul {H : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hH : DifferentiableOn ℂ H (ball 0 R)) (d j : ℕ) :
    taylorCoeff (fun z : ℂ => z ^ d * H z) j =
      if d ≤ j then taylorCoeff H (j - d) else 0 := by
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hPowCont : ContDiffAt ℂ j (fun z : ℂ => z ^ d) 0 := by fun_prop
  have hHCont : ContDiffAt ℂ j H 0 :=
    (hH.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hzero)
  change taylorCoeff ((fun z : ℂ => z ^ d) * H) j = _
  rw [taylorCoeff_mul hPowCont hHCont]
  simp_rw [taylorCoeff_pow_function]
  by_cases hdj : d ≤ j
  · rw [if_pos hdj]
    rw [Finset.sum_eq_single d]
    · simp
    · intro i hi hid
      rw [if_neg hid, zero_mul]
    · intro hdmem
      exact (hdmem (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hdj))).elim
  · rw [if_neg hdj]
    apply Finset.sum_eq_zero
    intro i hi
    have hid : i ≠ d := by
      intro heq
      subst i
      exact hdj (Nat.le_of_lt_succ (Finset.mem_range.mp hi))
    rw [if_neg hid, zero_mul]

lemma taylorCoeff_const_mul_function (c : ℂ) (H : ℂ → ℂ) (n : ℕ) :
    taylorCoeff (fun z => c * H z) n = c * taylorCoeff H n := by
  simp only [taylorCoeff, iteratedDeriv_const_mul_field]
  ring

lemma taylorCoeff_finset_sum {I : Type*} {s : Finset I} {F : I → ℂ → ℂ}
    {n : ℕ} (hF : ∀ i ∈ s, ContDiffAt ℂ n (F i) 0) :
    taylorCoeff (fun z => ∑ i ∈ s, F i z) n =
      ∑ i ∈ s, taylorCoeff (F i) n := by
  rw [taylorCoeff, iteratedDeriv_fun_sum hF, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  rfl

/-- The pole-free shift `zⁿ Pₙ(z⁻¹ exp(-L z))` written as a finite holomorphic sum. -/
noncomputable def faberShiftFunction (L : ℂ → ℂ) (n : ℕ) (z : ℂ) : ℂ :=
  ∑ i ∈ Finset.range (n + 1),
    (faberPolynomial (exteriorFactorPowerSeries L) n).coeff i *
      (z ^ (n - i) * exteriorAnalyticFactor L z ^ i)

lemma faberShiftFunction_eq_eval {L : ℂ → ℂ} {n : ℕ} {w : ℂ} (hw : w ≠ 0) :
    faberShiftFunction L n w = w ^ n *
      (faberPolynomial (exteriorFactorPowerSeries L) n).eval
        (w⁻¹ * exteriorAnalyticFactor L w) := by
  rw [faberShiftFunction, Polynomial.eval_eq_sum_range,
    (faberPolynomial_monic_natDegree (exteriorFactorPowerSeries L) n).2,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hpow : w ^ n * (w⁻¹) ^ i = w ^ (n - i) := by
    rw [inv_pow, ← pow_sub₀ w hw hin]
  rw [mul_pow, ← hpow]
  ring

lemma taylorCoeff_faberShiftFunction {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R)) (n j : ℕ) :
    taylorCoeff (faberShiftFunction L n) j =
      (faberLaurent (exteriorFactorPowerSeries L) n).coeff
        ((j : ℤ) - (n : ℤ)) := by
  let A := exteriorFactorPowerSeries L
  let E := exteriorAnalyticFactor L
  let P := faberPolynomial A n
  have hE : DifferentiableOn ℂ E (ball 0 R) := exteriorAnalyticFactor_differentiableOn hL
  have hzero : (0 : ℂ) ∈ ball 0 R := mem_ball_self hR
  have hterms : ∀ i ∈ Finset.range (n + 1), ContDiffAt ℂ j
      (fun z => P.coeff i * (z ^ (n - i) * E z ^ i)) 0 := by
    intro i hi
    have hECont : ContDiffAt ℂ j E 0 :=
      (hE.contDiffOn isOpen_ball).contDiffAt (isOpen_ball.mem_nhds hzero)
    fun_prop
  change taylorCoeff (fun z => ∑ i ∈ Finset.range (n + 1),
    P.coeff i * (z ^ (n - i) * E z ^ i)) j = _
  rw [taylorCoeff_finset_sum hterms]
  unfold faberLaurent
  rw [Polynomial.eval₂_eq_sum_range,
    (faberPolynomial_monic_natDegree A n).2, HahnSeries.coeff_sum]
  apply Finset.sum_congr rfl
  intro i hi
  have hin : i ≤ n := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  rw [taylorCoeff_const_mul_function]
  change P.coeff i *
      taylorCoeff (fun z => z ^ (n - i) * (fun w => E w ^ i) z) j = _
  rw [taylorCoeff_pow_mul (H := fun z => E z ^ i) hR (hE.pow i) (n - i) j,
    laurent_algebraMap_mul, HahnSeries.coeff_smul,
    coeff_formalExteriorMap_pow]
  by_cases hshift : n - i ≤ j
  · rw [if_pos hshift, ← coeff_exteriorFactorPowerSeries_pow hR hL, if_neg]
    · rw [show (((j : ℤ) - (n : ℤ) + (i : ℤ)).natAbs) =
          j - (n - i) by
          have hnonneg : 0 ≤ (j : ℤ) - (n : ℤ) + (i : ℤ) := by omega
          have hcast :
              ((((j : ℤ) - (n : ℤ) + (i : ℤ)).natAbs : ℕ) : ℤ) =
                ((j - (n - i) : ℕ) : ℤ) := by
            rw [Int.natAbs_of_nonneg hnonneg]
            omega
          exact_mod_cast hcast, smul_eq_mul]
    · omega
  · rw [if_neg hshift, if_pos (by omega), smul_zero, mul_zero]

/-- The formal Grunsky coefficient is the positive Laurent coefficient divided by `n`. -/
noncomputable def grunskyCoeff (L : ℂ → ℂ) (n m : ℕ) : ℂ :=
  (faberLaurent (exteriorFactorPowerSeries L) n).coeff (m : ℤ) / n

lemma logarithmicFaber_principal_part {L : ℂ → ℂ} (hL0 : L 0 = 0) (n : ℕ) :
    (faberLaurent (exteriorFactorPowerSeries L) n).coeff (-(n : ℤ)) = 1 ∧
      ∀ q < n,
        (faberLaurent (exteriorFactorPowerSeries L) n).coeff (-(q : ℤ)) = 0 :=
  faberLaurent_principal_part (exteriorFactorPowerSeries_constantCoeff hL0) n

lemma taylorCoeff_faberShiftFunction_zero {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0) (n : ℕ) :
    taylorCoeff (faberShiftFunction L n) 0 = 1 := by
  rw [taylorCoeff_faberShiftFunction hR hL]
  simpa using (logarithmicFaber_principal_part hL0 n).1

lemma taylorCoeff_faberShiftFunction_eq_zero {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hL0 : L 0 = 0) {n j : ℕ} (hj : 0 < j) (hjn : j ≤ n) :
    taylorCoeff (faberShiftFunction L n) j = 0 := by
  rw [taylorCoeff_faberShiftFunction hR hL]
  let q := n - j
  have hq : q < n := by omega
  have hzero := (logarithmicFaber_principal_part hL0 n).2 q hq
  have hindex : (j : ℤ) - (n : ℤ) = -(q : ℤ) := by
    dsimp [q]
    rw [Nat.cast_sub hjn]
    ring
  rw [hindex]
  exact hzero

lemma taylorCoeff_faberShiftFunction_tail {L : ℂ → ℂ} {R : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    {n : ℕ} (hn : 0 < n) (m : ℕ) :
    taylorCoeff (faberShiftFunction L n) (n + m) =
      (n : ℂ) * grunskyCoeff L n m := by
  rw [taylorCoeff_faberShiftFunction hR hL]
  have hindex : (((n + m : ℕ) : ℤ) - (n : ℤ)) = (m : ℤ) := by omega
  rw [hindex]
  unfold grunskyCoeff
  field_simp [Nat.cast_ne_zero.mpr hn.ne']

noncomputable def polarComplexFDeriv (p : ℝ × ℝ) : ℝ × ℝ →L[ℝ] ℂ :=
  Complex.equivRealProdCLM.symm.toContinuousLinearMap.comp (fderivPolarCoordSymm p)

lemma hasFDerivAt_complex_polarCoord_symm (p : ℝ × ℝ) :
    HasFDerivAt Complex.polarCoord.symm (polarComplexFDeriv p) p := by
  simpa [polarComplexFDeriv, Complex.polarCoord] using
    Complex.equivRealProdCLM.symm.hasFDerivAt.comp p
      (hasFDerivAt_polarCoord_symm p)

lemma polarComplexFDeriv_radial (p : ℝ × ℝ) :
    polarComplexFDeriv p (1, 0) =
      (Real.cos p.2 : ℂ) + (Real.sin p.2 : ℂ) * Complex.I := by
  simp [polarComplexFDeriv, fderivPolarCoordSymm,
    Matrix.toLin_finTwoProd_apply, Complex.equivRealProdCLM_symm_apply]

lemma polarComplexFDeriv_angular (p : ℝ × ℝ) :
    polarComplexFDeriv p (0, 1) =
      -(p.1 * Real.sin p.2 : ℝ) + (p.1 * Real.cos p.2 : ℝ) * Complex.I := by
  simp [polarComplexFDeriv, fderivPolarCoordSymm,
    Matrix.toLin_finTwoProd_apply, Complex.equivRealProdCLM_symm_apply]

lemma signedCross_mul_left (d u v : ℂ) :
    signedCross (d * u) (d * v) = ‖d‖ ^ 2 * signedCross u v := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [signedCross, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma signedCross_harmonic (q u v : ℂ) :
    signedCross (u + q * starRingEnd ℂ u) (v + q * starRingEnd ℂ v) =
      (1 - ‖q‖ ^ 2) * signedCross u v := by
  rw [← Complex.normSq_eq_norm_sq]
  simp [signedCross, Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  ring

lemma signedCross_polar (p : ℝ × ℝ) :
    signedCross (polarComplexFDeriv p (1, 0))
      (polarComplexFDeriv p (0, 1)) = p.1 := by
  simp [polarComplexFDeriv, fderivPolarCoordSymm, Matrix.toLin_finTwoProd_apply,
    Complex.equivRealProdCLM_symm_apply, signedCross, Complex.mul_im]
  calc
    Real.cos p.2 * (p.1 * Real.cos p.2) +
        Real.sin p.2 * (p.1 * Real.sin p.2) =
      p.1 * (Real.sin p.2 ^ 2 + Real.cos p.2 ^ 2) := by ring
    _ = p.1 := by rw [Real.sin_sq_add_cos_sq]; ring

noncomputable def faberFillPolar (L : ℂ → ℂ) (A : ℝ) (P : Polynomial ℂ) :
    ℝ × ℝ → ℂ :=
  (fun w => P.eval w) ∘ exteriorHarmonicFill L A ∘ Complex.polarCoord.symm

lemma faberFillPolar_contDiffAt {L : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAR : 1 / A < R) (P : Polynomial ℂ)
    {p : ℝ × ℝ} (hp0 : 0 ≤ p.1) (hpA : p.1 ≤ A) :
    ContDiffAt ℝ 2 (faberFillPolar L A P) p := by
  let z : ℂ := Complex.polarCoord.symm p
  have hzA : z ∈ closedBall (0 : ℂ) A := by
    rw [mem_closedBall_zero_iff]
    change ‖Complex.polarCoord.symm p‖ ≤ A
    rw [Complex.norm_polarCoord_symm, abs_of_nonneg hp0]
    exact hpA
  have hwR : interiorReflection A z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, interiorReflection, norm_div, norm_pow,
      Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg hA.le]
    have hzNorm : ‖z‖ ≤ A := by simpa [mem_closedBall_zero_iff] using hzA
    calc
      ‖z‖ / A ^ 2 ≤ A / A ^ 2 := div_le_div_of_nonneg_right hzNorm (sq_nonneg A)
      _ = 1 / A := by field_simp [hA.ne']
      _ < R := hAR
  have hE : ContDiffAt ℂ ⊤ (exteriorAnalyticSlope L) (interiorReflection A z) :=
    ((exteriorAnalyticSlope_differentiableOn hR hL).contDiffOn isOpen_ball).contDiffAt
      (isOpen_ball.mem_nhds hwR)
  have href : ContDiffAt ℝ 2 (interiorReflection A) z := by
    unfold interiorReflection
    exact Complex.conjCLE.contDiff.contDiffAt.div_const ((A : ℂ) ^ 2)
  have hfill : ContDiffAt ℝ 2 (exteriorHarmonicFill L A) z := by
    unfold exteriorHarmonicFill
    exact contDiffAt_id.add ((hE.restrict_scalars ℝ).of_le (by norm_num) |>.comp z href)
  have hpolar : ContDiffAt ℝ 2 (fun q : ℝ × ℝ => Complex.polarCoord.symm q) p := by
    have hpair : ContDiffAt ℝ 2
        (fun q : ℝ × ℝ => (q.1 * Real.cos q.2, q.1 * Real.sin q.2)) p := by
      fun_prop
    simpa [Complex.polarCoord, Function.comp_def] using
      Complex.equivRealProdCLM.symm.contDiff.contDiffAt.comp p hpair
  have hpoly : ContDiffAt ℝ 2 (fun w : ℂ => P.eval w)
      (exteriorHarmonicFill L A z) := by
    have hc : ContDiffAt ℂ 2 (fun w : ℂ => P.eval w)
        (exteriorHarmonicFill L A z) := by
      induction P using Polynomial.induction_on' with
      | add P Q hP hQ =>
          simpa using hP.add hQ
      | monomial n a =>
          simpa [Polynomial.eval_monomial] using
            (contDiffAt_const.mul (contDiffAt_id.pow n))
    exact hc.restrict_scalars ℝ
  unfold faberFillPolar
  exact hpoly.comp p (hfill.comp p hpolar)

lemma faberFillPolar_polarJacobian {L : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAR : 1 / A < R) (P : Polynomial ℂ)
    {p : ℝ × ℝ} (hp0 : 0 ≤ p.1) (hpA : p.1 ≤ A) :
    polarJacobian (faberFillPolar L A P) p =
      p.1 * ‖P.derivative.eval
        (exteriorHarmonicFill L A (Complex.polarCoord.symm p))‖ ^ 2 *
        (1 - (‖deriv (exteriorAnalyticSlope L)
          (interiorReflection A (Complex.polarCoord.symm p))‖ / A ^ 2) ^ 2) := by
  let z : ℂ := Complex.polarCoord.symm p
  have hzA : z ∈ closedBall (0 : ℂ) A := by
    rw [mem_closedBall_zero_iff]
    change ‖Complex.polarCoord.symm p‖ ≤ A
    rw [Complex.norm_polarCoord_symm, abs_of_nonneg hp0]
    exact hpA
  have hpolar := hasFDerivAt_complex_polarCoord_symm p
  have hfill := hasFDerivAt_exteriorHarmonicFill hR hL hA hAR hzA
  have hpoly := (P.hasDerivAt (exteriorHarmonicFill L A z)).complexToReal_fderiv
  have hcomp := hpoly.comp p (hfill.comp p hpolar)
  have hcomp' : HasFDerivAt (faberFillPolar L A P)
      (((P.derivative.eval (exteriorHarmonicFill L A z)) •
          (1 : ℂ →L[ℝ] ℂ)).comp
        ((harmonicFillFDeriv L A z).comp (polarComplexFDeriv p))) p := by
    simpa only [faberFillPolar] using hcomp
  unfold polarJacobian
  rw [hcomp'.fderiv]
  change signedCross
      (P.derivative.eval (exteriorHarmonicFill L A z) *
        harmonicFillFDeriv L A z (polarComplexFDeriv p (1, 0)))
      (P.derivative.eval (exteriorHarmonicFill L A z) *
        harmonicFillFDeriv L A z (polarComplexFDeriv p (0, 1))) = _
  rw [signedCross_mul_left]
  have haction (u : ℂ) : harmonicFillFDeriv L A z u =
      u + (deriv (exteriorAnalyticSlope L) (interiorReflection A z) /
        (A : ℂ) ^ 2) * starRingEnd ℂ u := by
    unfold harmonicFillFDeriv
    change u + (deriv (exteriorAnalyticSlope L) (interiorReflection A z) /
      (A : ℂ) ^ 2) * starRingEnd ℂ u = _
    rfl
  rw [haction, haction, signedCross_harmonic, signedCross_polar]
  rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hA.le]
  dsimp only [z]
  ring

lemma harmonicFactor_nonneg {L : ℂ → ℂ} {A ρ : ℝ} {M : NNReal}
    (hA : 0 < A) (hAρ : 1 / A < ρ)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) A) :
    0 ≤ 1 - (‖deriv (exteriorAnalyticSlope L) (interiorReflection A z)‖ / A ^ 2) ^ 2 := by
  have hzA : ‖z‖ ≤ A := by simpa [mem_closedBall_zero_iff] using hz
  have hwρ : interiorReflection A z ∈ ball (0 : ℂ) ρ := by
    rw [mem_ball_zero_iff, interiorReflection, norm_div, norm_pow,
      Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg hA.le]
    calc
      ‖z‖ / A ^ 2 ≤ A / A ^ 2 := div_le_div_of_nonneg_right hzA (sq_nonneg A)
      _ = 1 / A := by field_simp [hA.ne']
      _ < ρ := hAρ
  have hclosed : closedBall (0 : ℂ) ρ ∈ 𝓝 (interiorReflection A z) :=
    Filter.mem_of_superset (isOpen_ball.mem_nhds hwρ) ball_subset_closedBall
  have hd : ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z)‖ ≤ M :=
    norm_deriv_le_of_lipschitzOn hclosed hP
  have hKreal : (M : ℝ) * (A ^ 2)⁻¹ < 1 := by
    have hcoe := NNReal.coe_lt_coe.mpr hK
    have hreflect : ((interiorReflectionLipschitzConstant A : NNReal) : ℝ) =
        1 / A ^ 2 := rfl
    simpa only [NNReal.coe_mul, NNReal.coe_one, hreflect, one_div] using hcoe
  have hq : ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z)‖ / A ^ 2 < 1 := by
    calc
      ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z)‖ / A ^ 2 ≤
          (M : ℝ) / A ^ 2 := div_le_div_of_nonneg_right hd (sq_nonneg A)
      _ = (M : ℝ) * (A ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ < 1 := hKreal
  have hq0 : 0 ≤ ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z)‖ / A ^ 2 :=
    div_nonneg (norm_nonneg _) (sq_nonneg A)
  nlinarith

lemma hasFDerivAt_faberFillPolar {L : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAR : 1 / A < R) (P : Polynomial ℂ)
    {p : ℝ × ℝ}
    (hzA : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) A) :
    HasFDerivAt (faberFillPolar L A P)
      (((P.derivative.eval
          (exteriorHarmonicFill L A (Complex.polarCoord.symm p))) •
          (1 : ℂ →L[ℝ] ℂ)).comp
        ((harmonicFillFDeriv L A (Complex.polarCoord.symm p)).comp
          (polarComplexFDeriv p))) p := by
  have hpolar := hasFDerivAt_complex_polarCoord_symm p
  have hfill := hasFDerivAt_exteriorHarmonicFill hR hL hA hAR hzA
  have hpoly := (P.hasDerivAt
    (exteriorHarmonicFill L A (Complex.polarCoord.symm p))).complexToReal_fderiv
  simpa only [faberFillPolar] using hpoly.comp p (hfill.comp p hpolar)

lemma faberFillPolar_radialAreaFlux_zero {L : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAR : 1 / A < R) (P : Polynomial ℂ) (theta : ℝ) :
    radialAreaFlux (faberFillPolar L A P) (0, theta) = 0 := by
  have hzA : Complex.polarCoord.symm ((0 : ℝ), theta) ∈
      closedBall (0 : ℂ) A := by
    rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm]
    simp [hA.le]
  have hd := hasFDerivAt_faberFillPolar hR hL hA hAR P hzA
  unfold radialAreaFlux
  rw [hd.fderiv]
  change (1 / 2 : ℝ) * signedCross _
    (P.derivative.eval _ *
      harmonicFillFDeriv L A _ (polarComplexFDeriv (0, theta) (0, 1))) = 0
  rw [polarComplexFDeriv_angular]
  simp [signedCross]

lemma faberFillPolar_angularAreaFlux_periodic {L : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAR : 1 / A < R) (P : Polynomial ℂ)
    {r : ℝ} (hr0 : 0 ≤ r) (hrA : r ≤ A) :
    angularAreaFlux (faberFillPolar L A P) (r, Real.pi) =
      angularAreaFlux (faberFillPolar L A P) (r, -Real.pi) := by
  have hzplus : Complex.polarCoord.symm (r, Real.pi) ∈
      closedBall (0 : ℂ) A := by
    rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm,
      abs_of_nonneg hr0]
    exact hrA
  have hzminus : Complex.polarCoord.symm (r, -Real.pi) ∈
      closedBall (0 : ℂ) A := by
    rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm,
      abs_of_nonneg hr0]
    exact hrA
  have hdplus := hasFDerivAt_faberFillPolar hR hL hA hAR P hzplus
  have hdminus := hasFDerivAt_faberFillPolar hR hL hA hAR P hzminus
  have hzEq : Complex.polarCoord.symm (r, Real.pi) =
      Complex.polarCoord.symm (r, -Real.pi) := by
    simp [Complex.polarCoord_symm_apply]
  have hval : faberFillPolar L A P (r, Real.pi) =
      faberFillPolar L A P (r, -Real.pi) := by
    simp only [faberFillPolar, Function.comp_apply]
    rw [hzEq]
  have hderiv : fderiv ℝ (faberFillPolar L A P) (r, Real.pi) (1, 0) =
      fderiv ℝ (faberFillPolar L A P) (r, -Real.pi) (1, 0) := by
    rw [hdplus.fderiv, hdminus.fderiv]
    change P.derivative.eval (exteriorHarmonicFill L A _) *
        harmonicFillFDeriv L A _ (polarComplexFDeriv (r, Real.pi) (1, 0)) =
      P.derivative.eval (exteriorHarmonicFill L A _) *
        harmonicFillFDeriv L A _ (polarComplexFDeriv (r, -Real.pi) (1, 0))
    rw [hzEq, polarComplexFDeriv_radial, polarComplexFDeriv_radial]
    simp
  unfold angularAreaFlux
  rw [hval, hderiv]

lemma faberFillPolar_radialAreaFlux_nonneg {L : ℂ → ℂ} {R A ρ : ℝ}
    {M : NNReal} (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAρ : 1 / A < ρ) (hρR : ρ < R)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    (P : Polynomial ℂ) :
    0 ≤ ∫ theta in -Real.pi..Real.pi,
      radialAreaFlux (faberFillPolar L A P) (A, theta) := by
  apply radialAreaFlux_nonneg_of_polarJacobian hA
  · intro p hp
    exact faberFillPolar_contDiffAt hR hL hA (hAρ.trans hρR) P hp.1.1 hp.2.1
  · intro r hr
    exact faberFillPolar_angularAreaFlux_periodic hR hL hA (hAρ.trans hρR) P
      hr.1 hr.2
  · intro theta htheta
    exact faberFillPolar_radialAreaFlux_zero hR hL hA (hAρ.trans hρR) P theta
  · intro p hp
    rw [faberFillPolar_polarJacobian hR hL hA (hAρ.trans hρR) P hp.1.1 hp.2.1]
    have hzA : Complex.polarCoord.symm p ∈ closedBall (0 : ℂ) A := by
      rw [mem_closedBall_zero_iff, Complex.norm_polarCoord_symm,
        abs_of_nonneg hp.1.1]
      exact hp.2.1
    exact mul_nonneg (mul_nonneg hp.1.1 (sq_nonneg _))
      (harmonicFactor_nonneg hA hAρ hP hK hzA)

end Submission
