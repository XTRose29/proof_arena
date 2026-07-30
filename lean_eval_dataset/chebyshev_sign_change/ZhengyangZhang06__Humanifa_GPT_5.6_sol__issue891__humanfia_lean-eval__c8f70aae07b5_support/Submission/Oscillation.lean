import Submission.Analytic
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open Filter Topology
open scoped Interval

namespace Submission.Oscillation

lemma exists_large_nsmul_mem_nhds_zero
    {G : Type*} [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
    [FirstCountableTopology G] [CompactSpace G]
    (x : G) {U : Set G} (hU : U ∈ 𝓝 (0 : G)) (N : ℕ) :
    ∃ n > N, n • x ∈ U := by
  let step := N + 1
  let u : ℕ → G := fun k => (k * step) • x
  obtain ⟨a, phi, hphi, hphiLim⟩ := CompactSpace.tendsto_subseq u
  have hphiLimSucc : Tendsto (fun k => u (phi (k + 1))) atTop (𝓝 a) := by
    simpa only [Function.comp_def] using
      hphiLim.comp (Filter.tendsto_add_atTop_nat 1)
  have hdiff : Tendsto (fun k => u (phi (k + 1)) - u (phi k)) atTop (𝓝 (0 : G)) := by
    simpa using hphiLimSucc.sub hphiLim
  have hevent : ∀ᶠ k in atTop, u (phi (k + 1)) - u (phi k) ∈ U :=
    hdiff.eventually hU
  obtain ⟨k, hk⟩ := hevent.exists
  let d := phi (k + 1) - phi k
  refine ⟨d * step, ?_, ?_⟩
  · have hd : 0 < d := Nat.sub_pos_of_lt (hphi (Nat.lt_succ_self k))
    have hstep : step ≤ d * step := by
      simpa using Nat.mul_le_mul_right step (Nat.succ_le_iff.mpr hd)
    exact (Nat.lt_succ_self N).trans_le (by simpa [step] using hstep)
  · have hphiLe : phi k * step ≤ phi (k + 1) * step :=
      Nat.mul_le_mul_right step (hphi.monotone (Nat.le_succ k))
    have hrew : u (phi (k + 1)) - u (phi k) = (d * step) • x := by
      dsimp [u, d]
      rw [Nat.sub_mul, sub_nsmul x hphiLe]
      simp only [sub_eq_add_neg]
    rwa [hrew] at hk

lemma exists_large_nat_phase_alignment
    {ι : Type*} [Fintype ι] (gamma : ι → ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (N : ℕ) :
    ∃ n > N, ∀ j : ι,
      ‖Complex.exp (((n : ℝ) * gamma j) * Complex.I) - 1‖ < epsilon := by
  let x : ι → Additive Circle := fun j => Additive.ofMul (Circle.exp (gamma j))
  obtain ⟨n, hn, hball⟩ := exists_large_nsmul_mem_nhds_zero x
    (Metric.ball_mem_nhds (0 : ι → Additive Circle) hepsilon) N
  refine ⟨n, hn, fun j => ?_⟩
  have hj := (dist_pi_lt_iff hepsilon).mp (Metric.mem_ball.mp hball) j
  change dist ((Circle.exp (gamma j)) ^ n) 1 < epsilon at hj
  rw [← Circle.exp_natCast_mul] at hj
  change dist (Circle.exp ((n : ℝ) * gamma j)).val (1 : Circle).val < epsilon at hj
  simpa only [Circle.coe_exp, Circle.coe_one, Complex.dist_eq, Complex.ofReal_mul] using hj

lemma exists_large_nat_phase_recurrence
    {ι : Type*} [Fintype ι] (gamma : ι → ℝ) {epsilon : ℝ} (hepsilon : 0 < epsilon)
    (k N : ℕ) :
    ∃ n > N, ∀ j : ι,
      ‖Complex.exp (((n : ℝ) * gamma j) * Complex.I) -
        Complex.exp (((k : ℝ) * gamma j) * Complex.I)‖ < epsilon := by
  obtain ⟨m, hmN, hm⟩ := exists_large_nat_phase_alignment gamma hepsilon N
  refine ⟨m + k, hmN.trans_le (Nat.le_add_right m k), fun j => ?_⟩
  calc
    ‖Complex.exp ((((m + k : ℕ) : ℝ) * gamma j) * Complex.I) -
        Complex.exp (((k : ℝ) * gamma j) * Complex.I)‖ =
        ‖(Complex.exp (((m : ℝ) * gamma j) * Complex.I) - 1) *
          Complex.exp (((k : ℝ) * gamma j) * Complex.I)‖ := by
      congr 1
      rw [sub_mul, one_mul]
      congr 1
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    _ = ‖Complex.exp (((m : ℝ) * gamma j) * Complex.I) - 1‖ := by
      rw [norm_mul, Complex.norm_exp]
      simp
    _ < epsilon := hm j

noncomputable def finiteExponentialSum
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ j, c j * Complex.exp ((t * gamma j) * Complex.I)

lemma exists_large_nat_finiteExponentialSum_close
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (k N : ℕ) :
    ∃ n > N, ‖finiteExponentialSum c gamma n - finiteExponentialSum c gamma k‖ < epsilon := by
  let C : ℝ := ∑ j, ‖c j‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hdelta : 0 < epsilon / (C + 1) := div_pos hepsilon (by positivity)
  obtain ⟨n, hnN, hn⟩ := exists_large_nat_phase_recurrence gamma hdelta k N
  refine ⟨n, hnN, ?_⟩
  rw [finiteExponentialSum, finiteExponentialSum, ← Finset.sum_sub_distrib]
  calc
    ‖∑ j, (c j * Complex.exp (((n : ℝ) * gamma j) * Complex.I) -
        c j * Complex.exp (((k : ℝ) * gamma j) * Complex.I))‖
        ≤ ∑ j, ‖c j * Complex.exp (((n : ℝ) * gamma j) * Complex.I) -
          c j * Complex.exp (((k : ℝ) * gamma j) * Complex.I)‖ := norm_sum_le _ _
    _ = ∑ j, ‖c j‖ * ‖Complex.exp (((n : ℝ) * gamma j) * Complex.I) -
          Complex.exp (((k : ℝ) * gamma j) * Complex.I)‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [← mul_sub, norm_mul]
    _ ≤ ∑ j, ‖c j‖ * (epsilon / (C + 1)) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hn j).le (norm_nonneg _)
    _ = C * (epsilon / (C + 1)) := by rw [Finset.sum_mul]
    _ < epsilon := by
      calc
        C * (epsilon / (C + 1)) = C * epsilon / (C + 1) := by ring
        _ < epsilon := (div_lt_iff₀ (by positivity : 0 < C + 1)).2 (by nlinarith)

lemma finiteExponentialSum_re_gt_frequently
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    {R : ℝ} {k : ℕ} (hk : R < (finiteExponentialSum c gamma k).re) :
    ∀ N : ℕ, ∃ n > N, R < (finiteExponentialSum c gamma n).re := by
  intro N
  let epsilon := ((finiteExponentialSum c gamma k).re - R) / 2
  have hepsilon : 0 < epsilon := div_pos (sub_pos.mpr hk) (by norm_num)
  obtain ⟨n, hnN, hn⟩ := exists_large_nat_finiteExponentialSum_close c gamma hepsilon k N
  refine ⟨n, hnN, ?_⟩
  have hre : |(finiteExponentialSum c gamma n).re -
      (finiteExponentialSum c gamma k).re| < epsilon := by
    calc
      |(finiteExponentialSum c gamma n).re - (finiteExponentialSum c gamma k).re| =
          |(finiteExponentialSum c gamma n - finiteExponentialSum c gamma k).re| := by
            rw [Complex.sub_re]
      _ ≤ ‖finiteExponentialSum c gamma n - finiteExponentialSum c gamma k‖ :=
        Complex.abs_re_le_norm _
      _ < epsilon := hn
  dsimp [epsilon] at hre
  have := neg_lt_of_abs_lt hre
  linarith

lemma finiteExponentialSum_re_lt_frequently
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    {R : ℝ} {k : ℕ} (hk : (finiteExponentialSum c gamma k).re < R) :
    ∀ N : ℕ, ∃ n > N, (finiteExponentialSum c gamma n).re < R := by
  intro N
  let epsilon := (R - (finiteExponentialSum c gamma k).re) / 2
  have hepsilon : 0 < epsilon := div_pos (sub_pos.mpr hk) (by norm_num)
  obtain ⟨n, hnN, hn⟩ := exists_large_nat_finiteExponentialSum_close c gamma hepsilon k N
  refine ⟨n, hnN, ?_⟩
  have hre : |(finiteExponentialSum c gamma n).re -
      (finiteExponentialSum c gamma k).re| < epsilon := by
    calc
      |(finiteExponentialSum c gamma n).re - (finiteExponentialSum c gamma k).re| =
          |(finiteExponentialSum c gamma n - finiteExponentialSum c gamma k).re| := by
            rw [Complex.sub_re]
      _ ≤ ‖finiteExponentialSum c gamma n - finiteExponentialSum c gamma k‖ :=
        Complex.abs_re_le_norm _
      _ < epsilon := hn
  dsimp [epsilon] at hre
  have := lt_of_abs_lt hre
  linarith

noncomputable def symmetricComplexMean (f : ℝ → ℂ) (n : ℕ) : ℂ :=
  (∫ t in -(n : ℝ)..(n : ℝ), f t) / (2 * (n : ℝ))

private lemma integral_complex_exponential_symmetric (gamma : ℝ) (n : ℕ)
    (hgamma : gamma ≠ 0) :
    (∫ t in -(n : ℝ)..(n : ℝ),
        Complex.exp ((t * gamma) * Complex.I)) =
      (Complex.exp (((n : ℝ) * gamma) * Complex.I) -
          Complex.exp ((-(n : ℝ) * gamma) * Complex.I)) /
        (gamma * Complex.I) := by
  have h := integral_exp_mul_complex
    (a := -(n : ℝ)) (b := (n : ℝ))
    (c := (gamma : ℂ) * Complex.I)
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hgamma) Complex.I_ne_zero)
  simpa only [Complex.ofReal_mul, Complex.ofReal_neg, Complex.ofReal_natCast,
    mul_assoc, mul_comm, mul_left_comm] using h

lemma tendsto_symmetricComplexMean_exp (gamma : ℝ) (hgamma : gamma ≠ 0) :
    Tendsto
      (fun n : ℕ => symmetricComplexMean
        (fun t => Complex.exp ((t * gamma) * Complex.I)) n)
      atTop (nhds 0) := by
  let u : ℕ → ℂ := fun n =>
    ((Complex.exp (((n : ℝ) * gamma) * Complex.I) -
        Complex.exp ((-(n : ℝ) * gamma) * Complex.I)) /
      (gamma * Complex.I)) / 2
  have hu : IsBoundedUnder (· ≤ ·) atTop (norm ∘ u) := by
    apply isBoundedUnder_of_eventually_le (a := 1 / |gamma|)
    filter_upwards [] with n
    dsimp [u]
    rw [norm_div, norm_div, Complex.norm_mul, Complex.norm_real, Complex.norm_I,
      mul_one, Real.norm_eq_abs]
    norm_num
    have hnum :
        ‖Complex.exp (((n : ℝ) * gamma) * Complex.I) -
            Complex.exp ((-(n : ℝ) * gamma) * Complex.I)‖ ≤ 2 := by
      calc
        _ ≤ ‖Complex.exp (((n : ℝ) * gamma) * Complex.I)‖ +
            ‖Complex.exp ((-(n : ℝ) * gamma) * Complex.I)‖ := norm_sub_le _ _
        _ = 2 := by
          simp only [Complex.norm_exp]
          norm_num
    have hnum' :
        ‖Complex.exp (((n : ℂ) * (gamma : ℂ)) * Complex.I) -
            Complex.exp (-(((n : ℂ) * (gamma : ℂ)) * Complex.I))‖ ≤ 2 := by
      simpa only [Complex.ofReal_natCast, Complex.ofReal_mul, map_neg, neg_mul] using hnum
    calc
      _ ≤ 2 / |gamma| / 2 := by
        exact div_le_div_of_nonneg_right
          (div_le_div_of_nonneg_right hnum' (abs_nonneg gamma)) (by norm_num)
      _ = 1 / |gamma| := by field_simp
      _ = |gamma|⁻¹ := by simp only [one_div]
  have hinv : Tendsto (fun n : ℕ => ((n : ℂ)⁻¹)) atTop (nhds 0) :=
    tendsto_inv_atTop_nhds_zero_nat
  have hprod := Filter.isBoundedUnder_le_mul_tendsto_zero hu hinv
  apply hprod.congr'
  filter_upwards [] with n
  rw [symmetricComplexMean, integral_complex_exponential_symmetric gamma n hgamma]
  dsimp [u]
  field_simp

lemma symmetricComplexMean_finiteExponentialSum
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ) (n : ℕ) :
    symmetricComplexMean (finiteExponentialSum c gamma) n =
      ∑ j, c j * symmetricComplexMean
        (fun t => Complex.exp ((t * gamma j) * Complex.I)) n := by
  rw [symmetricComplexMean]
  simp only [finiteExponentialSum]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul]
    simp only [symmetricComplexMean]
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro j _
    ring
  · intro j _
    exact (by fun_prop : Continuous fun t : ℝ =>
      c j * Complex.exp ((t * gamma j) * Complex.I)).intervalIntegrable _ _

lemma tendsto_symmetricComplexMean_finiteExponentialSum
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    (hgamma : ∀ j, gamma j ≠ 0) :
    Tendsto (fun n : ℕ => symmetricComplexMean (finiteExponentialSum c gamma) n)
      atTop (nhds 0) := by
  have hsum : Tendsto
      (fun n : ℕ => ∑ j, c j * symmetricComplexMean
        (fun t => Complex.exp ((t * gamma j) * Complex.I)) n)
      atTop (nhds (∑ _j : ι, (0 : ℂ))) := by
    apply tendsto_finsetSum
    intro j _
    simpa using (tendsto_const_nhds.mul (tendsto_symmetricComplexMean_exp (gamma j) (hgamma j)))
  simpa only [symmetricComplexMean_finiteExponentialSum, Finset.sum_const_zero] using hsum

lemma tendsto_symmetricComplexMean_one :
    Tendsto (fun n : ℕ => symmetricComplexMean (fun _t : ℝ => (1 : ℂ)) n)
      atTop (nhds 1) := by
  apply tendsto_const_nhds.congr'
  filter_upwards [eventually_ge_atTop 1] with n hn
  rw [symmetricComplexMean]
  simp only [intervalIntegral.integral_const, sub_neg_eq_add]
  rw [Complex.real_smul, mul_one]
  push_cast
  field_simp [Nat.ne_zero_of_lt hn]
  norm_num

lemma tendsto_symmetricComplexMean_exp_ite (gamma : ℝ) :
    Tendsto
      (fun n : ℕ => symmetricComplexMean
        (fun t => Complex.exp ((t * gamma) * Complex.I)) n)
      atTop (nhds (if gamma = 0 then 1 else 0)) := by
  by_cases hgamma : gamma = 0
  · subst gamma
    simpa using tendsto_symmetricComplexMean_one
  · simpa [hgamma] using tendsto_symmetricComplexMean_exp gamma hgamma

lemma tendsto_symmetricComplexMean_finiteExponentialSum_ite
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ) :
    Tendsto (fun n : ℕ => symmetricComplexMean (finiteExponentialSum c gamma) n)
      atTop (nhds (∑ j, if gamma j = 0 then c j else 0)) := by
  have hsum : Tendsto
      (fun n : ℕ => ∑ j, c j * symmetricComplexMean
        (fun t => Complex.exp ((t * gamma j) * Complex.I)) n)
      atTop (nhds (∑ j, c j * (if gamma j = 0 then 1 else 0))) := by
    apply tendsto_finsetSum
    intro j _
    exact tendsto_const_nhds.mul (tendsto_symmetricComplexMean_exp_ite (gamma j))
  convert hsum using 1
  · ext n
    exact symmetricComplexMean_finiteExponentialSum c gamma n
  · congr 1
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp

lemma finiteExponentialSum_mul
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (c : ι → ℂ) (gamma : ι → ℝ) (d : κ → ℂ) (delta : κ → ℝ) (t : ℝ) :
    finiteExponentialSum c gamma t * finiteExponentialSum d delta t =
      finiteExponentialSum
        (fun jk : ι × κ => c jk.1 * d jk.2)
        (fun jk : ι × κ => gamma jk.1 + delta jk.2) t := by
  rw [finiteExponentialSum, finiteExponentialSum, finiteExponentialSum,
    Finset.sum_mul_sum]
  rw [Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro k _
  calc
    _ = c j * d k *
        (Complex.exp ((t * gamma j) * Complex.I) *
          Complex.exp ((t * delta k) * Complex.I)) := by ring
    _ = c j * d k *
        Complex.exp (((t * gamma j) * Complex.I) + ((t * delta k) * Complex.I)) := by
          rw [Complex.exp_add]
    _ = _ := by
      congr 2
      push_cast
      ring

lemma finiteExponentialSum_conj
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ) (t : ℝ) :
    (starRingEnd ℂ) (finiteExponentialSum c gamma t) =
      finiteExponentialSum (fun j => (starRingEnd ℂ) (c j)) (fun j => -gamma j) t := by
  rw [finiteExponentialSum, finiteExponentialSum, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [map_mul, ← Complex.exp_conj]
  congr 1
  simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring_nf

lemma tendsto_symmetricComplexMean_finiteExponentialSum_mul_self
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    (hgamma : ∀ j, 0 < gamma j) :
    Tendsto
      (fun n : ℕ => symmetricComplexMean
        (fun t => finiteExponentialSum c gamma t * finiteExponentialSum c gamma t) n)
      atTop (nhds 0) := by
  let cp : ι × ι → ℂ := fun jk => c jk.1 * c jk.2
  let gp : ι × ι → ℝ := fun jk => gamma jk.1 + gamma jk.2
  have h := tendsto_symmetricComplexMean_finiteExponentialSum_ite cp gp
  have hzero : (∑ jk, if gp jk = 0 then cp jk else 0) = 0 := by
    apply Finset.sum_eq_zero
    rintro ⟨j, k⟩ _
    simp only [gp, cp]
    rw [if_neg (ne_of_gt (add_pos (hgamma j) (hgamma k)))]
  rw [hzero] at h
  apply h.congr'
  filter_upwards [] with n
  apply congrArg (fun f : ℝ → ℂ => symmetricComplexMean f n)
  funext t
  exact (finiteExponentialSum_mul c gamma c gamma t).symm

lemma tendsto_symmetricComplexMean_finiteExponentialSum_mul_conj
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    (hgamma : Function.Injective gamma) :
    Tendsto
      (fun n : ℕ => symmetricComplexMean
        (fun t => finiteExponentialSum c gamma t *
          (starRingEnd ℂ) (finiteExponentialSum c gamma t)) n)
      atTop (nhds (∑ j, (‖c j‖ : ℂ) ^ 2)) := by
  classical
  let cc : ι → ℂ := fun j => (starRingEnd ℂ) (c j)
  let ng : ι → ℝ := fun j => -gamma j
  let cp : ι × ι → ℂ := fun jk => c jk.1 * cc jk.2
  let gp : ι × ι → ℝ := fun jk => gamma jk.1 + ng jk.2
  have h := tendsto_symmetricComplexMean_finiteExponentialSum_ite cp gp
  have hdiag : (∑ jk, if gp jk = 0 then cp jk else 0) =
      ∑ j, (‖c j‖ : ℂ) ^ 2 := by
    have hiff (j k : ι) : gamma j + -gamma k = 0 ↔ j = k := by
      constructor
      · intro hzero
        apply hgamma
        linarith
      · rintro rfl
        simp
    rw [Fintype.sum_prod_type]
    simp only [gp, ng, cp, cc]
    simp [hiff, Complex.mul_conj']
  rw [hdiag] at h
  apply h.congr'
  filter_upwards [] with n
  apply congrArg (fun f : ℝ → ℂ => symmetricComplexMean f n)
  funext t
  rw [finiteExponentialSum_conj]
  exact (finiteExponentialSum_mul c gamma cc ng t).symm

noncomputable def realPartExponentialCoeff
    {ι : Type*} (c : ι → ℂ) : ι ⊕ ι → ℂ
  | .inl j => c j / 2
  | .inr j => (starRingEnd ℂ) (c j) / 2

def realPartExponentialFreq
    {ι : Type*} (gamma : ι → ℝ) : ι ⊕ ι → ℝ
  | .inl j => gamma j
  | .inr j => -gamma j

lemma finiteExponentialSum_real_eq
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ) (t : ℝ) :
    ((finiteExponentialSum c gamma t).re : ℂ) =
      finiteExponentialSum (realPartExponentialCoeff c) (realPartExponentialFreq gamma) t := by
  rw [Complex.re_eq_add_conj]
  change (finiteExponentialSum c gamma t +
      (starRingEnd ℂ) (finiteExponentialSum c gamma t)) / 2 =
    ∑ j : ι ⊕ ι, realPartExponentialCoeff c j *
      Complex.exp ((t * realPartExponentialFreq gamma j) * Complex.I)
  rw [Fintype.sum_sum_type]
  simp only [realPartExponentialCoeff, realPartExponentialFreq]
  simp_rw [div_mul_eq_mul_div]
  rw [← Finset.sum_div, ← Finset.sum_div]
  rw [← finiteExponentialSum]
  change (finiteExponentialSum c gamma t +
      (starRingEnd ℂ) (finiteExponentialSum c gamma t)) / 2 =
    finiteExponentialSum c gamma t / 2 +
      finiteExponentialSum (fun j => (starRingEnd ℂ) (c j)) (fun j => -gamma j) t / 2
  rw [← finiteExponentialSum_conj]
  ring

lemma tendsto_symmetricComplexMean_finiteExponentialSum_re_sq
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    (hgamma : ∀ j, 0 < gamma j) (hgammaInj : Function.Injective gamma) :
    Tendsto
      (fun n : ℕ => symmetricComplexMean
        (fun t => ((finiteExponentialSum c gamma t).re : ℂ) ^ 2) n)
      atTop (nhds ((∑ j, (‖c j‖ : ℂ) ^ 2) / 2)) := by
  classical
  let rc : ι ⊕ ι → ℂ := realPartExponentialCoeff c
  let rg : ι ⊕ ι → ℝ := realPartExponentialFreq gamma
  let cp : (ι ⊕ ι) × (ι ⊕ ι) → ℂ := fun jk => rc jk.1 * rc jk.2
  let gp : (ι ⊕ ι) × (ι ⊕ ι) → ℝ := fun jk => rg jk.1 + rg jk.2
  have h := tendsto_symmetricComplexMean_finiteExponentialSum_ite cp gp
  have hll (j k : ι) : gamma j + gamma k ≠ 0 :=
    ne_of_gt (add_pos (hgamma j) (hgamma k))
  have hrr (j k : ι) : -gamma j + -gamma k ≠ 0 :=
    ne_of_lt (add_neg (neg_lt_zero.mpr (hgamma j)) (neg_lt_zero.mpr (hgamma k)))
  have hlr (j k : ι) : gamma j + -gamma k = 0 ↔ j = k := by
    constructor
    · intro hzero
      apply hgammaInj
      linarith
    · rintro rfl
      simp
  have hrl (j k : ι) : -gamma j + gamma k = 0 ↔ j = k := by
    constructor
    · intro hzero
      apply hgammaInj
      linarith
    · rintro rfl
      simp
  have henergy : (∑ jk, if gp jk = 0 then cp jk else 0) =
      (∑ j, (‖c j‖ : ℂ) ^ 2) / 2 := by
    rw [Fintype.sum_prod_type, Fintype.sum_sum_type]
    simp only [gp, cp, rg, rc, realPartExponentialFreq, realPartExponentialCoeff,
      Fintype.sum_sum_type]
    simp [hll, hrr, hlr, hrl]
    have hleft (j : ι) : c j / 2 * ((starRingEnd ℂ) (c j) / 2) =
        (‖c j‖ : ℂ) ^ 2 / 4 := by
      rw [div_mul_div_comm, Complex.mul_conj']
      norm_num
    have hright (j : ι) : (starRingEnd ℂ) (c j) / 2 * (c j / 2) =
        (‖c j‖ : ℂ) ^ 2 / 4 := by
      rw [div_mul_div_comm, Complex.conj_mul']
      norm_num
    simp_rw [hleft, hright]
    rw [← Finset.sum_div]
    ring
  rw [henergy] at h
  apply h.congr'
  filter_upwards [] with n
  apply congrArg (fun f : ℝ → ℂ => symmetricComplexMean f n)
  funext t
  rw [finiteExponentialSum_real_eq]
  rw [pow_two]
  exact (finiteExponentialSum_mul rc rg rc rg t).symm

lemma symmetricComplexMean_re
    (f : ℝ → ℂ) (n : ℕ) (hn : n ≠ 0)
    (hf : IntervalIntegrable f MeasureTheory.volume (-(n : ℝ)) (n : ℝ)) :
    (symmetricComplexMean f n).re =
      (∫ t in -(n : ℝ)..(n : ℝ), (f t).re) / (2 * (n : ℝ)) := by
  rw [symmetricComplexMean, Complex.div_re]
  have hre : (∫ t in -(n : ℝ)..(n : ℝ), (f t).re) =
      (∫ t in -(n : ℝ)..(n : ℝ), f t).re := by
    simpa using intervalIntegral.intervalIntegral_re (𝕜 := ℂ) hf
  rw [hre]
  simp [Complex.normSq_apply]
  field_simp [hn]

lemma finiteExponentialSum_re_abs_le
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ) (t : ℝ) :
    |(finiteExponentialSum c gamma t).re| ≤ ∑ j, ‖c j‖ := by
  calc
    _ ≤ ‖finiteExponentialSum c gamma t‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ j, ‖c j * Complex.exp ((t * gamma j) * Complex.I)‖ := by
      rw [finiteExponentialSum]
      exact norm_sum_le _ _
    _ = ∑ j, ‖c j‖ := by
      apply Finset.sum_congr rfl
      intro j _
      rw [norm_mul, Complex.norm_exp]
      simp

lemma exists_finiteExponentialSum_re_neg
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    (hgamma : ∀ j, 0 < gamma j) (hgammaInj : Function.Injective gamma)
    (hc : ∃ j, c j ≠ 0) :
    ∃ t : ℝ, (finiteExponentialSum c gamma t).re < 0 := by
  classical
  by_contra! hnonneg
  let C : ℝ := ∑ j, ‖c j‖
  let E : ℝ := (∑ j, ‖c j‖ ^ 2) / 2
  have hEpos : 0 < E := by
    dsimp [E]
    apply div_pos
    · apply Finset.sum_pos' (fun j _ => sq_nonneg ‖c j‖)
      obtain ⟨j, hj⟩ := hc
      exact ⟨j, Finset.mem_univ j, sq_pos_of_pos (norm_pos_iff.mpr hj)⟩
    · norm_num
  have hmeanComplex := tendsto_symmetricComplexMean_finiteExponentialSum c gamma
    (fun j => (hgamma j).ne')
  have hmean : Tendsto
      (fun n : ℕ => (symmetricComplexMean (finiteExponentialSum c gamma) n).re)
      atTop (nhds 0) := by
    change Tendsto
      (Complex.re ∘ fun n : ℕ => symmetricComplexMean (finiteExponentialSum c gamma) n)
      atTop (nhds (Complex.re 0))
    exact Complex.continuous_re.continuousAt.tendsto.comp hmeanComplex
  have henergyComplex :=
    tendsto_symmetricComplexMean_finiteExponentialSum_re_sq c gamma hgamma hgammaInj
  have henergy : Tendsto
      (fun n : ℕ => (symmetricComplexMean
        (fun t => ((finiteExponentialSum c gamma t).re : ℂ) ^ 2) n).re)
      atTop (nhds E) := by
    convert Complex.continuous_re.continuousAt.tendsto.comp henergyComplex using 1
    · rfl
    · congr 1
      dsimp [E]
      norm_cast
  have hineq : ∀ᶠ n : ℕ in atTop,
      (symmetricComplexMean
        (fun t => ((finiteExponentialSum c gamma t).re : ℂ) ^ 2) n).re ≤
      C * (symmetricComplexMean (finiteExponentialSum c gamma) n).re := by
    filter_upwards [eventually_ge_atTop 1] with n hn
    have hn0 : n ≠ 0 := Nat.ne_zero_of_lt hn
    let f : ℝ → ℝ := fun t => (finiteExponentialSum c gamma t).re
    have hfcont : Continuous f := by
      dsimp [f, finiteExponentialSum]
      fun_prop
    have hFc : Continuous (finiteExponentialSum c gamma) := by
      unfold finiteExponentialSum
      fun_prop
    have hsqc : Continuous (fun t => ((f t : ℂ) ^ 2)) := by fun_prop
    rw [symmetricComplexMean_re _ n hn0 (hFc.intervalIntegrable _ _)]
    rw [symmetricComplexMean_re _ n hn0 (hsqc.intervalIntegrable _ _)]
    simp [pow_two, Complex.mul_re]
    have hab : -(n : ℝ) ≤ (n : ℝ) := neg_le_self (Nat.cast_nonneg n)
    have hmono : (∫ t in -(n : ℝ)..(n : ℝ), f t * f t) ≤
        ∫ t in -(n : ℝ)..(n : ℝ), C * f t := by
      apply intervalIntegral.integral_mono_on hab
        ((hfcont.mul hfcont).intervalIntegrable _ _)
        ((continuous_const.mul hfcont).intervalIntegrable _ _)
      intro t _
      have hft0 : 0 ≤ f t := hnonneg t
      have hftC : f t ≤ C := by
        exact (le_abs_self (f t)).trans (finiteExponentialSum_re_abs_le c gamma t)
      change f t * f t ≤ C * f t
      nlinarith
    rw [intervalIntegral.integral_const_mul] at hmono
    have hdenom : 0 ≤ 2 * (n : ℝ) := by positivity
    calc
      (∫ t in -(n : ℝ)..(n : ℝ), f t * f t) / (2 * (n : ℝ)) ≤
          (C * ∫ t in -(n : ℝ)..(n : ℝ), f t) / (2 * (n : ℝ)) :=
        div_le_div_of_nonneg_right hmono hdenom
      _ = C * ((∫ t in -(n : ℝ)..(n : ℝ), f t) / (2 * (n : ℝ))) := by ring
  have hright : Tendsto
      (fun n : ℕ => C * (symmetricComplexMean (finiteExponentialSum c gamma) n).re)
      atTop (nhds 0) := by
    simpa using tendsto_const_nhds.mul hmean
  have hEle : E ≤ 0 := le_of_tendsto_of_tendsto henergy hright hineq
  exact (not_le_of_gt hEpos) hEle

lemma finiteExponentialSum_neg
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ) (t : ℝ) :
    finiteExponentialSum (fun j => -c j) gamma t = -finiteExponentialSum c gamma t := by
  rw [finiteExponentialSum, finiteExponentialSum, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro j _
  rw [neg_mul]

lemma exists_finiteExponentialSum_re_pos
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    (hgamma : ∀ j, 0 < gamma j) (hgammaInj : Function.Injective gamma)
    (hc : ∃ j, c j ≠ 0) :
    ∃ t : ℝ, 0 < (finiteExponentialSum c gamma t).re := by
  have hcneg : ∃ j, -c j ≠ 0 := by
    obtain ⟨j, hj⟩ := hc
    exact ⟨j, neg_ne_zero.mpr hj⟩
  obtain ⟨t, ht⟩ := exists_finiteExponentialSum_re_neg
    (fun j => -c j) gamma hgamma hgammaInj hcneg
  refine ⟨t, ?_⟩
  rw [finiteExponentialSum_neg] at ht
  simp only [Complex.neg_re] at ht
  linarith

lemma exists_large_real_finiteExponentialSum_close
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    {epsilon : ℝ} (hepsilon : 0 < epsilon) (t₀ N : ℝ) :
    ∃ t > N, ‖finiteExponentialSum c gamma t - finiteExponentialSum c gamma t₀‖ < epsilon := by
  let C : ℝ := ∑ j, ‖c j‖
  have hC : 0 ≤ C := Finset.sum_nonneg fun _ _ => norm_nonneg _
  have hdelta : 0 < epsilon / (C + 1) := div_pos hepsilon (by positivity)
  obtain ⟨M, hM⟩ := exists_nat_gt (N - t₀)
  obtain ⟨m, hmM, hm⟩ := exists_large_nat_phase_alignment gamma hdelta M
  refine ⟨(m : ℝ) + t₀, ?_, ?_⟩
  · have hmreal : N - t₀ < (m : ℝ) := hM.trans (by exact_mod_cast hmM)
    linarith
  · rw [finiteExponentialSum, finiteExponentialSum, ← Finset.sum_sub_distrib]
    push_cast
    calc
      ‖∑ j, (c j * Complex.exp ((((m : ℝ) + t₀) * gamma j) * Complex.I) -
          c j * Complex.exp ((t₀ * gamma j) * Complex.I))‖
          ≤ ∑ j, ‖c j * Complex.exp ((((m : ℝ) + t₀) * gamma j) * Complex.I) -
            c j * Complex.exp ((t₀ * gamma j) * Complex.I)‖ := norm_sum_le _ _
      _ = ∑ j, ‖c j‖ * ‖Complex.exp (((m : ℝ) * gamma j) * Complex.I) - 1‖ := by
        apply Finset.sum_congr rfl
        intro j _
        rw [← mul_sub, norm_mul]
        congr 1
        have hexp :
            Complex.exp (((((m : ℝ) : ℂ) + (t₀ : ℂ)) * (gamma j : ℂ)) * Complex.I) =
              Complex.exp ((((m : ℝ) : ℂ) * (gamma j : ℂ)) * Complex.I) *
                Complex.exp (((t₀ : ℂ) * (gamma j : ℂ)) * Complex.I) := by
          rw [← Complex.exp_add]
          congr 1
          ring
        calc
          ‖Complex.exp ((((m : ℝ) + t₀) * gamma j) * Complex.I) -
              Complex.exp ((t₀ * gamma j) * Complex.I)‖ =
              ‖(Complex.exp (((m : ℝ) * gamma j) * Complex.I) - 1) *
                Complex.exp ((t₀ * gamma j) * Complex.I)‖ := by
                congr 1
                rw [hexp]
                ring
          _ = ‖Complex.exp (((m : ℝ) * gamma j) * Complex.I) - 1‖ := by
            rw [norm_mul, Complex.norm_exp]
            simp
      _ ≤ ∑ j, ‖c j‖ * (epsilon / (C + 1)) := by
        apply Finset.sum_le_sum
        intro j _
        exact mul_le_mul_of_nonneg_left (hm j).le (norm_nonneg _)
      _ = C * (epsilon / (C + 1)) := by rw [Finset.sum_mul]
      _ < epsilon := by
        calc
          C * (epsilon / (C + 1)) = C * epsilon / (C + 1) := by ring
          _ < epsilon := (div_lt_iff₀ (by positivity : 0 < C + 1)).2 (by nlinarith)

lemma finiteExponentialSum_re_oscillates
    {ι : Type*} [Fintype ι] (c : ι → ℂ) (gamma : ι → ℝ)
    (hgamma : ∀ j, 0 < gamma j) (hgammaInj : Function.Injective gamma)
    (hc : ∃ j, c j ≠ 0) :
    (∀ N : ℝ, ∃ t > N, 0 < (finiteExponentialSum c gamma t).re) ∧
      (∀ N : ℝ, ∃ t > N, (finiteExponentialSum c gamma t).re < 0) := by
  obtain ⟨tpos, htpos⟩ := exists_finiteExponentialSum_re_pos c gamma hgamma hgammaInj hc
  obtain ⟨tneg, htneg⟩ := exists_finiteExponentialSum_re_neg c gamma hgamma hgammaInj hc
  constructor
  · intro N
    let epsilon := (finiteExponentialSum c gamma tpos).re / 2
    have hepsilon : 0 < epsilon := half_pos htpos
    obtain ⟨t, htN, htclose⟩ :=
      exists_large_real_finiteExponentialSum_close c gamma hepsilon tpos N
    refine ⟨t, htN, ?_⟩
    have hre : |(finiteExponentialSum c gamma t).re -
        (finiteExponentialSum c gamma tpos).re| < epsilon := by
      calc
        _ = |(finiteExponentialSum c gamma t -
            finiteExponentialSum c gamma tpos).re| := by rw [Complex.sub_re]
        _ ≤ ‖finiteExponentialSum c gamma t - finiteExponentialSum c gamma tpos‖ :=
          Complex.abs_re_le_norm _
        _ < epsilon := htclose
    dsimp [epsilon] at hre
    linarith [neg_lt_of_abs_lt hre]
  · intro N
    let epsilon := -(finiteExponentialSum c gamma tneg).re / 2
    have hepsilon : 0 < epsilon := div_pos (neg_pos.mpr htneg) (by norm_num)
    obtain ⟨t, htN, htclose⟩ :=
      exists_large_real_finiteExponentialSum_close c gamma hepsilon tneg N
    refine ⟨t, htN, ?_⟩
    have hre : |(finiteExponentialSum c gamma t).re -
        (finiteExponentialSum c gamma tneg).re| < epsilon := by
      calc
        _ = |(finiteExponentialSum c gamma t -
            finiteExponentialSum c gamma tneg).re| := by rw [Complex.sub_re]
        _ ≤ ‖finiteExponentialSum c gamma t - finiteExponentialSum c gamma tneg‖ :=
          Complex.abs_re_le_norm _
        _ < epsilon := htclose
    dsimp [epsilon] at hre
    linarith [lt_of_abs_lt hre]


end Submission.Oscillation
