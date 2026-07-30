import Mathlib

namespace Submission.Fejer

noncomputable section

open Filter MeasureTheory Set Topology
open scoped ComplexConjugate ENNReal

variable {T : ℝ} [Fact (0 < T)]

def circlePartialSum (g : C(AddCircle T, ℂ)) (N : ℕ) : C(AddCircle T, ℂ) :=
  ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeff g n • fourier n

def circleCesaroMean (g : C(AddCircle T, ℂ)) (N : ℕ) : C(AddCircle T, ℂ) :=
  ((N + 1 : ℝ)⁻¹) • ∑ k ∈ Finset.range (N + 1), circlePartialSum g k

def geometricSum (N : ℕ) : C(AddCircle T, ℂ) :=
  ∑ j ∈ Finset.range (N + 1), fourier (j : ℤ)

def fejerKernel (N : ℕ) (x : AddCircle T) : ℝ :=
  Complex.normSq (geometricSum N x) / (N + 1)

def shellToSquare (k : ℕ) (n : ℤ) : ℕ × ℕ :=
  if 0 ≤ n then (k - n.toNat, k) else (k, k - (-n).toNat)

theorem shellToSquare_max {k : ℕ} {n : ℤ} (hlo : -(k : ℤ) ≤ n) (_hhi : n ≤ k) :
    max (shellToSquare k n).1 (shellToSquare k n).2 = k := by
  unfold shellToSquare
  split <;> omega

theorem shellToSquare_diff {k : ℕ} {n : ℤ} (hlo : -(k : ℤ) ≤ n) (hhi : n ≤ k) :
    ((shellToSquare k n).2 : ℤ) - (shellToSquare k n).1 = n := by
  unfold shellToSquare
  split <;> omega

omit [Fact (0 < T)] in
theorem sum_dirichletKernel_eq_normSq (N : ℕ) (x : AddCircle T) :
    ∑ k ∈ Finset.range (N + 1),
        ∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n x =
      (Complex.normSq (geometricSum N x) : ℂ) := by
  rw [Complex.normSq_eq_conj_mul_self]
  simp only [geometricSum, ContinuousMap.sum_apply, map_sum]
  rw [Finset.sum_mul]
  simp_rw [Finset.mul_sum]
  rw [← Finset.sum_sigma (Finset.range (N + 1))
    (fun k => Finset.Icc (-(k : ℤ)) k) (fun q => fourier q.2 x)]
  rw [← Finset.sum_product' (Finset.range (N + 1)) (Finset.range (N + 1))
    (fun l j => conj (fourier (l : ℤ) x) * fourier (j : ℤ) x)]
  refine Finset.sum_bij
    (fun q _ => shellToSquare q.1 q.2)
    ?_ ?_ ?_ ?_
  · rintro ⟨k, n⟩ hkn
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hkn
    simp only [Finset.mem_product, Finset.mem_range]
    have hmax := shellToSquare_max hkn.2.1 hkn.2.2
    omega
  · rintro ⟨k, n⟩ hkn ⟨k', n'⟩ hk'n' heq
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hkn hk'n'
    have hk := shellToSquare_max hkn.2.1 hkn.2.2
    have hk' := shellToSquare_max hk'n'.2.1 hk'n'.2.2
    have hn := shellToSquare_diff hkn.2.1 hkn.2.2
    have hn' := shellToSquare_diff hk'n'.2.1 hk'n'.2.2
    have hkk : k = k' := by
      calc
        k = max (shellToSquare k n).1 (shellToSquare k n).2 := hk.symm
        _ = max (shellToSquare k' n').1 (shellToSquare k' n').2 := by rw [heq]
        _ = k' := hk'
    subst k'
    have hnn : n = n' := by
      calc
        n = ((shellToSquare k n).2 : ℤ) - (shellToSquare k n).1 := hn.symm
        _ = ((shellToSquare k n').2 : ℤ) - (shellToSquare k n').1 := by rw [heq]
        _ = n' := hn'
    subst n'
    rfl
  · rintro ⟨l, j⟩ hlj
    simp only [Finset.mem_product, Finset.mem_range] at hlj
    let k := max l j
    let n : ℤ := (j : ℤ) - l
    have hk : k < N + 1 := by
      dsimp [k]
      exact max_lt hlj.1 hlj.2
    have hlk : l ≤ k := by
      exact le_max_left l j
    have hjk : j ≤ k := by
      exact le_max_right l j
    have hnlo : -(k : ℤ) ≤ n := by
      dsimp [n]
      omega
    have hnhi : n ≤ k := by
      dsimp [n]
      omega
    refine ⟨⟨k, n⟩, ?_, ?_⟩
    · simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc]
      exact ⟨hk, hnlo, hnhi⟩
    · change shellToSquare (max l j) ((j : ℤ) - l) = (l, j)
      by_cases hljle : l ≤ j
      · have hsign : 0 ≤ (j : ℤ) - l := by omega
        have hto : ((j : ℤ) - l).toNat = j - l := by omega
        simp [shellToSquare, hto, hljle]
        omega
      · have hjlle : j ≤ l := by omega
        have hsign : ¬0 ≤ (j : ℤ) - l := by omega
        have hto : (-((j : ℤ) - l)).toNat = l - j := by omega
        simp [shellToSquare, max_eq_left hjlle, hljle]
        omega
  · rintro ⟨k, n⟩ hkn
    simp only [Finset.mem_sigma, Finset.mem_range, Finset.mem_Icc] at hkn
    rw [← fourier_neg, ← fourier_add]
    have hdiff := shellToSquare_diff hkn.2.1 hkn.2.2
    have hind : n = -((shellToSquare k n).1 : ℤ) + (shellToSquare k n).2 := by
      omega
    exact congrArg (fun m : ℤ => fourier m x) hind

omit [Fact (0 < T)] in
theorem fejerKernel_eq_average_dirichlet (N : ℕ) (x : AddCircle T) :
    (fejerKernel N x : ℂ) =
      (∑ k ∈ Finset.range (N + 1),
        ∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n x) / (N + 1 : ℂ) := by
  rw [sum_dirichletKernel_eq_normSq]
  simp [fejerKernel, Complex.ofReal_div, Complex.ofReal_natCast]

omit [Fact (0 < T)] in
theorem fejerKernel_nonneg (N : ℕ) (x : AddCircle T) : 0 ≤ fejerKernel N x := by
  exact div_nonneg (Complex.normSq_nonneg _) (by positivity)

omit [Fact (0 < T)] in
theorem continuous_fejerKernel (N : ℕ) : Continuous (fejerKernel (T := T) N) := by
  unfold fejerKernel
  fun_prop

theorem integrable_of_continuous {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : AddCircle T → E} (hg : Continuous g) : Integrable g AddCircle.haarAddCircle :=
  hg.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace g)

omit [Fact (0 < T)] in
theorem fourier_sub_apply (n : ℤ) (x y : AddCircle T) :
    fourier n (x - y) = fourier n x * fourier (-n) y := by
  simp [fourier_apply, sub_eq_add_neg, AddCircle.toCircle_add, AddCircle.toCircle_neg]

theorem integral_fourier (n : ℤ) :
    ∫ x : AddCircle T, fourier n x ∂AddCircle.haarAddCircle = if n = 0 then 1 else 0 := by
  have h := congrFun (fourierCoeff_fourier (T := T) n) 0
  simpa [fourierCoeff, Pi.single_apply, eq_comm] using h

theorem integrable_dirichletKernel (k : ℕ) :
    Integrable (fun x : AddCircle T =>
      ∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n x) AddCircle.haarAddCircle :=
  integrable_of_continuous (by fun_prop)

theorem integral_dirichletKernel (k : ℕ) :
    ∫ x : AddCircle T, (∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n x)
      ∂AddCircle.haarAddCircle = 1 := by
  rw [integral_finsetSum (Finset.Icc (-(k : ℤ)) k)
    (fun n _ => integrable_of_continuous (fourier n).continuous)]
  simp_rw [integral_fourier]
  simp

theorem integral_fejerKernel (N : ℕ) :
    ∫ x : AddCircle T, fejerKernel N x ∂AddCircle.haarAddCircle = 1 := by
  apply Complex.ofReal_injective
  calc
    ((∫ x : AddCircle T, fejerKernel N x ∂AddCircle.haarAddCircle : ℝ) : ℂ) =
        ∫ x : AddCircle T, (fejerKernel N x : ℂ) ∂AddCircle.haarAddCircle :=
      integral_ofReal.symm
    _ = 1 := by
      rw [integral_congr_ae (ae_of_all _ fun x => fejerKernel_eq_average_dirichlet N x)]
      rw [integral_div]
      rw [integral_finsetSum (Finset.range (N + 1))
        (fun k _ => integrable_dirichletKernel k)]
      calc
        (∑ k ∈ Finset.range (N + 1),
            ∫ x : AddCircle T,
              (∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n x)
              ∂AddCircle.haarAddCircle) / (N + 1 : ℂ) =
            (∑ k ∈ Finset.range (N + 1), (1 : ℂ)) / (N + 1 : ℂ) := by
          congr 1
          apply Finset.sum_congr rfl
          intro k hk
          exact integral_dirichletKernel k
        _ = 1 := by
          simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one,
            Nat.cast_add, Nat.cast_one]
          exact div_self (Nat.cast_add_one_ne_zero N)
    _ = ((1 : ℝ) : ℂ) := by norm_num

theorem integral_fejerKernel_sub (N : ℕ) (x : AddCircle T) :
    ∫ y : AddCircle T, fejerKernel N (x - y) ∂AddCircle.haarAddCircle = 1 := by
  rw [integral_sub_left_eq_self (fejerKernel N) AddCircle.haarAddCircle x]
  exact integral_fejerKernel N

theorem integral_fourier_sub_mul (g : C(AddCircle T, ℂ)) (n : ℤ) (x : AddCircle T) :
    ∫ y : AddCircle T, fourier n (x - y) * g y ∂AddCircle.haarAddCircle =
      fourierCoeff g n * fourier n x := by
  calc
    ∫ y : AddCircle T, fourier n (x - y) * g y ∂AddCircle.haarAddCircle =
        ∫ y : AddCircle T, fourier n x * (fourier (-n) y * g y)
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [fourier_sub_apply]
      ring
    _ = fourier n x * ∫ y : AddCircle T, fourier (-n) y * g y
          ∂AddCircle.haarAddCircle := by
      rw [integral_const_mul]
    _ = fourierCoeff g n * fourier n x := by
      rw [fourierCoeff]
      simp only [smul_eq_mul]
      ring

theorem circlePartialSum_eq_integral (g : C(AddCircle T, ℂ)) (k : ℕ)
    (x : AddCircle T) :
    circlePartialSum g k x =
      ∫ y : AddCircle T,
        (∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n (x - y)) * g y
        ∂AddCircle.haarAddCircle := by
  rw [show (fun y : AddCircle T =>
      (∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n (x - y)) * g y) =
      fun y => ∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n (x - y) * g y by
    funext y
    rw [Finset.sum_mul]]
  rw [integral_finsetSum (Finset.Icc (-(k : ℤ)) k)
    (fun n _ => integrable_of_continuous (by fun_prop))]
  simp_rw [integral_fourier_sub_mul]
  simp [circlePartialSum, smul_eq_mul]

theorem circleCesaroMean_eq_integral (g : C(AddCircle T, ℂ)) (N : ℕ)
    (x : AddCircle T) :
    circleCesaroMean g N x =
      ∫ y : AddCircle T, (fejerKernel N (x - y) : ℂ) * g y
        ∂AddCircle.haarAddCircle := by
  symm
  calc
    ∫ y : AddCircle T, (fejerKernel N (x - y) : ℂ) * g y
        ∂AddCircle.haarAddCircle =
        ∫ y : AddCircle T,
          ((∑ k ∈ Finset.range (N + 1),
            ∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n (x - y)) / (N + 1 : ℂ)) * g y
          ∂AddCircle.haarAddCircle := by
      apply integral_congr_ae
      filter_upwards [] with y
      rw [fejerKernel_eq_average_dirichlet]
    _ = (∫ y : AddCircle T,
          (∑ k ∈ Finset.range (N + 1),
            ∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n (x - y)) * g y
          ∂AddCircle.haarAddCircle) / (N + 1 : ℂ) := by
      rw [← integral_div]
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ = (∑ k ∈ Finset.range (N + 1),
          ∫ y : AddCircle T,
            (∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n (x - y)) * g y
            ∂AddCircle.haarAddCircle) / (N + 1 : ℂ) := by
      congr 1
      rw [show (fun y : AddCircle T =>
          (∑ k ∈ Finset.range (N + 1),
            ∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n (x - y)) * g y) =
          fun y => ∑ k ∈ Finset.range (N + 1),
            (∑ n ∈ Finset.Icc (-(k : ℤ)) k, fourier n (x - y)) * g y by
        funext y
        rw [Finset.sum_mul]]
      rw [integral_finsetSum (Finset.range (N + 1))
        (fun k _ => integrable_of_continuous (by fun_prop))]
    _ = (∑ k ∈ Finset.range (N + 1), circlePartialSum g k x) / (N + 1 : ℂ) := by
      congr 1
      apply Finset.sum_congr rfl
      intro k hk
      exact (circlePartialSum_eq_integral g k x).symm
    _ = circleCesaroMean g N x := by
      simp [circleCesaroMean, Complex.real_smul, div_eq_mul_inv, mul_comm]

theorem norm_circleCesaroMean_sub_le (g p : C(AddCircle T, ℂ)) (N : ℕ)
    (x : AddCircle T) :
    ‖circleCesaroMean g N x - circleCesaroMean p N x‖ ≤ ‖g - p‖ := by
  rw [circleCesaroMean_eq_integral, circleCesaroMean_eq_integral]
  have hKcont : Continuous (fun y : AddCircle T => fejerKernel N (x - y)) :=
    (continuous_fejerKernel N).comp (continuous_const.sub continuous_id)
  have hKCcont : Continuous (fun y : AddCircle T => (fejerKernel N (x - y) : ℂ)) :=
    Complex.continuous_ofReal.comp hKcont
  have hgint : Integrable
      (fun y : AddCircle T => (fejerKernel N (x - y) : ℂ) * g y)
      AddCircle.haarAddCircle := integrable_of_continuous (hKCcont.mul g.continuous)
  have hpint : Integrable
      (fun y : AddCircle T => (fejerKernel N (x - y) : ℂ) * p y)
      AddCircle.haarAddCircle := integrable_of_continuous (hKCcont.mul p.continuous)
  calc
    ‖(∫ y, (fejerKernel N (x - y) : ℂ) * g y ∂AddCircle.haarAddCircle) -
        ∫ y, (fejerKernel N (x - y) : ℂ) * p y ∂AddCircle.haarAddCircle‖ =
        ‖∫ y, (fejerKernel N (x - y) : ℂ) * (g y - p y)
          ∂AddCircle.haarAddCircle‖ := by
      rw [← integral_sub hgint hpint]
      apply congrArg norm
      apply integral_congr_ae
      filter_upwards [] with y
      ring
    _ ≤ ∫ y : AddCircle T, fejerKernel N (x - y) * ‖g - p‖
          ∂AddCircle.haarAddCircle := by
      apply norm_integral_le_of_norm_le
        (integrable_of_continuous (hKcont.mul continuous_const))
      filter_upwards [] with y
      calc
        ‖(fejerKernel N (x - y) : ℂ) * (g y - p y)‖ =
            fejerKernel N (x - y) * ‖g y - p y‖ := by
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (fejerKernel_nonneg N (x - y))]
        _ ≤ fejerKernel N (x - y) * ‖g - p‖ :=
          mul_le_mul_of_nonneg_left
            (by simpa using ContinuousMap.norm_coe_le_norm (g - p) y)
            (fejerKernel_nonneg N (x - y))
    _ = ‖g - p‖ := by
      rw [integral_mul_const, integral_fejerKernel_sub, one_mul]

theorem summable_fourierCoeff_of_mem_span (g : C(AddCircle T, ℂ))
    (hg : g ∈ Submodule.span ℂ (Set.range (fourier (T := T)))) :
    Summable (fourierCoeff g) := by
  refine Submodule.span_induction
    (p := fun (q : C(AddCircle T, ℂ)) _ => Summable (fourierCoeff q))
    ?_ ?_ ?_ ?_ hg
  · intro q hq
    rcases hq with ⟨n, rfl⟩
    rw [fourierCoeff_fourier]
    refine (hasSum_ite_eq n (1 : ℂ)).summable.congr fun m => ?_
    by_cases hmn : m = n <;> simp [hmn]
  · have hzero : fourierCoeff (T := T) (⇑(0 : C(AddCircle T, ℂ))) = 0 := by
      ext n
      simp [fourierCoeff]
    rw [hzero]
    exact summable_zero
  · intro q r hq hr hqsum hrsum
    rw [show (⇑(q + r) : AddCircle T → ℂ) = ⇑q + ⇑r by rfl,
      fourierCoeff.add (integrable_of_continuous q.continuous)
        (integrable_of_continuous r.continuous)]
    exact hqsum.add hrsum
  · intro c q hq hqsum
    have hsmul : fourierCoeff (T := T) (⇑(c • q)) = c • fourierCoeff (⇑q) := by
      ext n
      exact fourierCoeff.const_smul (⇑q) c n
    rw [hsmul]
    exact hqsum.const_smul c

theorem tendsto_circlePartialSum_of_summable (g : C(AddCircle T, ℂ))
    (hg : Summable (fourierCoeff g)) :
    Tendsto (circlePartialSum g) atTop (𝓝 g) := by
  change Tendsto
    (fun N : ℕ => ∑ n ∈ Finset.Icc (-(N : ℤ)) N, fourierCoeff g n • fourier n)
    atTop (𝓝 g)
  exact SummationFilter.hasSum_symmetricIcc_iff.mp <|
    Filter.Tendsto.mono_left (hasSum_fourier_series_of_summable hg)
      SummationFilter.le_atTop

theorem tendsto_circleCesaroMean_of_summable (g : C(AddCircle T, ℂ))
    (hg : Summable (fourierCoeff g)) :
    Tendsto (circleCesaroMean g) atTop (𝓝 g) := by
  change Tendsto
    (fun N : ℕ => ((N + 1 : ℝ)⁻¹) •
      ∑ k ∈ Finset.range (N + 1), circlePartialSum g k) atTop (𝓝 g)
  have hfun :
      (fun N : ℕ => ((N + 1 : ℝ)⁻¹) •
        ∑ k ∈ Finset.range (N + 1), circlePartialSum g k) =
      ((fun n : ℕ => ((n : ℝ)⁻¹) •
        ∑ k ∈ Finset.range n, circlePartialSum g k) ∘ fun n => n + 1) := by
    funext N
    simp only [Function.comp_apply, Nat.cast_add, Nat.cast_one]
  rw [hfun]
  exact (tendsto_circlePartialSum_of_summable g hg).cesaro_smul.comp
    (tendsto_add_atTop_nat 1)

theorem tendsto_circleCesaroMean (g : C(AddCircle T, ℂ)) :
    Tendsto (circleCesaroMean g) atTop (𝓝 g) := by
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hdense : Dense
      (Submodule.span ℂ (Set.range (fourier (T := T))) : Set C(AddCircle T, ℂ)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.mpr span_fourier_closure_eq_top
  obtain ⟨p, hp, hgp⟩ := hdense.exists_dist_lt g (by linarith : 0 < ε / 3)
  have hpconv := tendsto_circleCesaroMean_of_summable p
    (summable_fourierCoeff_of_mem_span p hp)
  rw [Metric.tendsto_atTop] at hpconv
  obtain ⟨M, hM⟩ := hpconv (ε / 3) (by linarith)
  refine ⟨M, fun N hN => ?_⟩
  have hcontract : dist (circleCesaroMean g N) (circleCesaroMean p N) ≤ dist g p := by
    rw [dist_eq_norm, dist_eq_norm]
    apply (ContinuousMap.norm_le _ (norm_nonneg _)).2
    intro x
    exact norm_circleCesaroMean_sub_le g p N x
  calc
    dist (circleCesaroMean g N) g ≤
        dist (circleCesaroMean g N) (circleCesaroMean p N) +
          dist (circleCesaroMean p N) g := dist_triangle _ _ _
    _ ≤ dist (circleCesaroMean g N) (circleCesaroMean p N) +
          (dist (circleCesaroMean p N) p + dist p g) := by
      gcongr
      exact dist_triangle _ _ _
    _ < ε := by
      have hpN := hM N hN
      rw [dist_comm g p] at hcontract hgp
      linarith

end

end Submission.Fejer
