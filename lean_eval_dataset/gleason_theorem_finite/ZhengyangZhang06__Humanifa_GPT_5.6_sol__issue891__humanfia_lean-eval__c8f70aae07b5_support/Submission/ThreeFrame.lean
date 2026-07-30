import Submission.Helpers

namespace LeanEval.Analysis

noncomputable section

lemma FrameFunction.sum_homogeneousValue_orthonormalBasis_submodule
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    {ι : Type*} [Fintype ι] (b : OrthonormalBasis ι ℂ K) :
    ∑ i, f.homogeneousValue (b i : H) = f.μ K.starProjection := by
  classical
  let P : ι → H →L[ℂ] H :=
    fun i ↦ InnerProductSpace.rankOne ℂ (b i : H) (b i : H)
  have hP (i : ι) : IsOrthProj (P i) :=
    isOrthProj_iff_isStarProjection.mpr <|
      InnerProductSpace.isStarProjection_rankOne_self
        (b.orthonormal.norm_eq_one i)
  have horth (i j : ι) (hij : i ≠ j) : P i * P j = 0 := by
    rw [ContinuousLinearMap.mul_def, InnerProductSpace.rankOne_comp_rankOne]
    have hij' : inner ℂ (b i : H) (b j : H) = 0 := by
      simpa using b.inner_eq_zero hij
    rw [hij', zero_smul]
  have hsum := f.map_sum P hP horth
  rw [← b.starProjection_eq_sum_rankOne] at hsum
  calc
    ∑ i, f.homogeneousValue (b i : H) =
        ∑ i, f.unitValue (b i : H) := by
      apply Finset.sum_congr rfl
      intro i _
      exact f.homogeneousValue_of_norm_eq_one
        (b.orthonormal.norm_eq_one i)
    _ = ∑ i, f.μ (P i) := rfl
    _ = f.μ K.starProjection := hsum.symm

lemma FrameFunction.sum_homogeneousValue_of_orthonormal_submodule
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    {ι : Type*} [Fintype ι] [Nonempty ι] (v : ι → K)
    (hv : Orthonormal ℂ v)
    (hcard : Fintype.card ι = Module.finrank ℂ K) :
    ∑ i, f.homogeneousValue (v i : H) = f.μ K.starProjection := by
  classical
  let b₀ : Module.Basis ι ℂ K :=
    basisOfOrthonormalOfCardEqFinrank hv hcard
  have hb₀ : (b₀ : ι → K) = v :=
    coe_basisOfOrthonormalOfCardEqFinrank hv hcard
  let b : OrthonormalBasis ι ℂ K :=
    b₀.toOrthonormalBasis (by simpa [hb₀] using hv)
  have hb : (b : ι → K) = v := by
    simpa only [b, Module.Basis.coe_toOrthonormalBasis] using hb₀
  simpa only [hb] using
    f.sum_homogeneousValue_orthonormalBasis_submodule K b

/-- Three nonnegative lengths satisfying the triangle inequalities can be
realized as three complex numbers with zero sum.  The first number is chosen
on the real axis; retaining squared norms is the convenient form for later
coordinate calculations. -/
lemma exists_complex_triangle
    {A B C : ℝ} (hA : 0 < A) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hAB : A ≤ B + C) (hBA : B ≤ A + C) (hCA : C ≤ A + B) :
    ∃ z₂ z₃ : ℂ,
      (A : ℂ) + z₂ + z₃ = 0 ∧
      ‖z₂‖ ^ 2 = B ^ 2 ∧ ‖z₃‖ ^ 2 = C ^ 2 := by
  let X : ℝ := (C ^ 2 - A ^ 2 - B ^ 2) / (2 * A)
  have hfac :
      0 ≤ (A + B - C) * (A + B + C) *
        (A + C - B) * (B + C - A) := by
    have h₁ : 0 ≤ A + B - C := by linarith
    have h₂ : 0 ≤ A + B + C := by linarith
    have h₃ : 0 ≤ A + C - B := by linarith
    have h₄ : 0 ≤ B + C - A := by linarith
    positivity
  have hrad : 0 ≤ B ^ 2 - X ^ 2 := by
    have hid :
        4 * A ^ 2 * (B ^ 2 - X ^ 2) =
          (A + B - C) * (A + B + C) *
          (A + C - B) * (B + C - A) := by
      dsimp [X]
      field_simp [ne_of_gt hA]
      ring
    nlinarith [sq_pos_of_pos hA]
  let Y : ℝ := Real.sqrt (B ^ 2 - X ^ 2)
  let z₂ : ℂ := ⟨X, Y⟩
  let z₃ : ℂ := -(A : ℂ) - z₂
  have hY : Y ^ 2 = B ^ 2 - X ^ 2 := by
    exact Real.sq_sqrt hrad
  have hX : 2 * A * X = C ^ 2 - A ^ 2 - B ^ 2 := by
    dsimp [X]
    field_simp [ne_of_gt hA]
  refine ⟨z₂, z₃, ?_, ?_, ?_⟩
  · simp [z₃]
  · rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z₂]
    nlinarith
  · rw [Complex.sq_norm, Complex.normSq_apply]
    dsimp [z₃, z₂]
    nlinarith

lemma balanced_heron_nonneg
    {u v : ℝ} (hu₀ : 1 / 2 ≤ u) (hu₁ : u ≤ 1)
    (hv₀ : 1 / 2 ≤ v) (hv₁ : v ≤ 1)
    (huv : u + v ≤ 3 / 2) :
    0 ≤ 4 * u * ((1 - v) * v) - (v - u - u * v) ^ 2 := by
  let E : ℝ → ℝ :=
    fun x ↦ 4 * x * ((1 - v) * v) - (v - x - x * v) ^ 2
  by_cases hv : v = 1
  · subst v
    have hu : u = 1 / 2 := by linarith
    subst u
    norm_num [E]
  have hvlt : v < 1 := lt_of_le_of_ne hv₁ hv
  have huhi : u ≤ 3 / 2 - v := by linarith
  have hElo :
      0 ≤ E (1 / 2) := by
    have hfactor :
        E (1 / 2) = (1 - v) * (9 * v - 1) / 4 := by
      dsimp [E]
      ring
    have hfirst : 0 ≤ 1 - v := by linarith
    have hsecond : 0 ≤ 9 * v - 1 := by linarith
    rw [hfactor]
    positivity
  have hEhi :
      0 ≤ E (3 / 2 - v) := by
    have hfactor :
        E (3 / 2 - v) =
          (1 - v) * (v - 1 / 2) *
            (v ^ 2 - 3 / 2 * v + 9 / 2) := by
      dsimp [E]
      ring
    have hquad : 0 ≤ v ^ 2 - 3 / 2 * v + 9 / 2 := by
      nlinarith [sq_nonneg (v - 3 / 4)]
    rw [hfactor]
    positivity
  have hchord :
      (1 - v) * E u =
        (3 / 2 - v - u) * E (1 / 2) +
          (u - 1 / 2) * E (3 / 2 - v) +
          (u - 1 / 2) * (3 / 2 - v - u) *
            (1 - v) * (1 + v) ^ 2 := by
    dsimp [E]
    ring
  have hnonneg :
      0 ≤
        (3 / 2 - v - u) * E (1 / 2) +
          (u - 1 / 2) * E (3 / 2 - v) +
          (u - 1 / 2) * (3 / 2 - v - u) *
            (1 - v) * (1 + v) ^ 2 := by
    positivity
  change 0 ≤ E u
  nlinarith

lemma balanced_product_triangle
    {a b c : ℝ}
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (_hc₀ : 0 ≤ c)
    (ha₁ : a ≤ 1 / 2) (hb₁ : b ≤ 1 / 2) (hc₁ : c ≤ 1 / 2)
    (hsum : a + b + c = 1) :
    let A := Real.sqrt (1 - a)
    let B := Real.sqrt (b * (1 - b))
    let C := Real.sqrt ((1 - c) * (1 - b))
    A ≤ B + C ∧ B ≤ A + C ∧ C ≤ A + B := by
  let u : ℝ := 1 - a
  let v : ℝ := 1 - b
  let A : ℝ := Real.sqrt u
  let B : ℝ := Real.sqrt ((1 - v) * v)
  let C : ℝ := Real.sqrt ((2 - u - v) * v)
  have hu₀ : 1 / 2 ≤ u := by dsimp [u]; linarith
  have hu₁ : u ≤ 1 := by dsimp [u]; linarith
  have hv₀ : 1 / 2 ≤ v := by dsimp [v]; linarith
  have hv₁ : v ≤ 1 := by dsimp [v]; linarith
  have huv : u + v ≤ 3 / 2 := by
    dsimp [u, v]
    linarith
  have htwo : 0 ≤ 2 - u - v := by
    dsimp [u, v]
    linarith
  have hA₀ : 0 ≤ A := Real.sqrt_nonneg _
  have hB₀ : 0 ≤ B := Real.sqrt_nonneg _
  have hC₀ : 0 ≤ C := Real.sqrt_nonneg _
  have hApos : 0 < A := Real.sqrt_pos.2 (by linarith)
  have hA2 : A ^ 2 = u := Real.sq_sqrt (by linarith)
  have hB2 : B ^ 2 = (1 - v) * v :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hC2 : C ^ 2 = (2 - u - v) * v :=
    Real.sq_sqrt (mul_nonneg htwo (by linarith))
  have hD :
      0 ≤ 4 * A ^ 2 * B ^ 2 -
        (C ^ 2 - A ^ 2 - B ^ 2) ^ 2 := by
    rw [hA2, hB2, hC2]
    convert balanced_heron_nonneg hu₀ hu₁ hv₀ hv₁ huv using 1
    all_goals ring
  have hprod :
      0 ≤ (A + B - C) * (A + B + C) *
        (A + C - B) * (B + C - A) := by
    calc
      0 ≤ 4 * A ^ 2 * B ^ 2 -
          (C ^ 2 - A ^ 2 - B ^ 2) ^ 2 := hD
      _ = (A + B - C) * (A + B + C) *
          (A + C - B) * (B + C - A) := by ring
  have hAB : A ≤ B + C := by
    by_contra h
    have hneg : B + C - A < 0 := by linarith
    have hp₁ : 0 < A + B - C := by linarith
    have hp₂ : 0 < A + B + C := by linarith
    have hp₃ : 0 < A + C - B := by linarith
    have :
        (A + B - C) * (A + B + C) *
            (A + C - B) * (B + C - A) < 0 := by
      exact mul_neg_of_pos_of_neg (mul_pos (mul_pos hp₁ hp₂) hp₃) hneg
    linarith
  have hBA : B ≤ A + C := by
    by_contra h
    have hneg : A + C - B < 0 := by linarith
    have hp₁ : 0 < A + B - C := by linarith
    have hp₂ : 0 < A + B + C := by linarith
    have hp₃ : 0 < B + C - A := by linarith
    have :
        (A + B - C) * (A + B + C) *
            (A + C - B) * (B + C - A) < 0 := by
      calc
        _ = ((A + B - C) * (A + B + C) * (B + C - A)) *
            (A + C - B) := by ring
        _ < 0 :=
          mul_neg_of_pos_of_neg (mul_pos (mul_pos hp₁ hp₂) hp₃) hneg
    linarith
  have hCA : C ≤ A + B := by
    by_contra h
    have hneg : A + B - C < 0 := by linarith
    have hp₁ : 0 < A + B + C := by linarith
    have hp₂ : 0 < A + C - B := by linarith
    have hp₃ : 0 < B + C - A := by linarith
    have :
        (A + B - C) * (A + B + C) *
            (A + C - B) * (B + C - A) < 0 := by
      calc
        _ = ((A + B + C) * (A + C - B) * (B + C - A)) *
            (A + B - C) := by ring
        _ < 0 :=
          mul_neg_of_pos_of_neg (mul_pos (mul_pos hp₁ hp₂) hp₃) hneg
    linarith
  have htri : A ≤ B + C ∧ B ≤ A + C ∧ C ≤ A + B :=
    ⟨hAB, hBA, hCA⟩
  simpa [A, B, C, u, v, show 2 - (1 - a) - (1 - b) = 1 - c by linarith]
    using htri

lemma exists_balanced_coefficient_basis
    {a b c : ℝ}
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c)
    (ha₁ : a ≤ 1 / 2) (hb₁ : b ≤ 1 / 2) (hc₁ : c ≤ 1 / 2)
    (hsum : a + b + c = 1) :
    ∃ d : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)),
      d 0 =
        WithLp.toLp 2 ![((Real.sqrt ((1 - a) / 2) : ℝ) : ℂ),
          ((Real.sqrt ((1 - b) / 2) : ℝ) : ℂ),
          ((Real.sqrt ((1 - c) / 2) : ℝ) : ℂ)] ∧
      ‖(d 1) 0‖ ^ 2 = 1 / 2 ∧
      ‖(d 1) 1‖ ^ 2 = b / 2 ∧
      ‖(d 1) 2‖ ^ 2 = (1 - b) / 2 ∧
      ‖(d 2) 0‖ ^ 2 = a / 2 ∧
      ‖(d 2) 1‖ ^ 2 = 1 / 2 ∧
      ‖(d 2) 2‖ ^ 2 = (1 - a) / 2 := by
  classical
  let A : ℝ := Real.sqrt (1 - a)
  let B : ℝ := Real.sqrt (b * (1 - b))
  let C : ℝ := Real.sqrt ((1 - c) * (1 - b))
  have hApos : 0 < A := Real.sqrt_pos.2 (by linarith)
  have hB₀ : 0 ≤ B := Real.sqrt_nonneg _
  have hC₀ : 0 ≤ C := Real.sqrt_nonneg _
  obtain ⟨hAB, hBA, hCA⟩ :=
    balanced_product_triangle ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ hsum
  obtain ⟨z₂, z₃, hzsum, hz₂, hz₃⟩ :=
    exists_complex_triangle hApos hB₀ hC₀ hAB hBA hCA
  let r : Fin 3 → ℝ :=
    ![(1 - a) / 2, (1 - b) / 2, (1 - c) / 2]
  let p : Fin 3 → ℝ :=
    ![1 / 2, b / 2, (1 - b) / 2]
  let z : Fin 3 → ℂ := ![(A : ℂ), z₂, z₃]
  let V : EuclideanSpace ℂ (Fin 3) :=
    WithLp.toLp 2 (fun i ↦ ((Real.sqrt (r i) : ℝ) : ℂ))
  let U : EuclideanSpace ℂ (Fin 3) :=
    WithLp.toLp 2
      (fun i ↦ z i / ((2 * Real.sqrt (r i) : ℝ) : ℂ))
  have hrpos (i : Fin 3) : 0 < r i := by
    fin_cases i <;> simp [r] <;> linarith
  have hA2 : A ^ 2 = 1 - a := Real.sq_sqrt (by linarith)
  have hB2 : B ^ 2 = b * (1 - b) :=
    Real.sq_sqrt (mul_nonneg hb₀ (by linarith))
  have hC2 : C ^ 2 = (1 - c) * (1 - b) :=
    Real.sq_sqrt (mul_nonneg (by linarith) (by linarith))
  have hzcoord (i : Fin 3) : ‖z i‖ ^ 2 = 4 * r i * p i := by
    fin_cases i
    · change ‖(A : ℂ)‖ ^ 2 = 4 * ((1 - a) / 2) * (1 / 2)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hApos, hA2]
      ring
    · change ‖z₂‖ ^ 2 = 4 * ((1 - b) / 2) * (b / 2)
      rw [hz₂, hB2]
      ring
    · change ‖z₃‖ ^ 2 = 4 * ((1 - c) / 2) * ((1 - b) / 2)
      rw [hz₃, hC2]
      ring
  have hVcoord (i : Fin 3) : ‖V i‖ ^ 2 = r i := by
    change ‖((Real.sqrt (r i) : ℝ) : ℂ)‖ ^ 2 = r i
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sq_sqrt (le_of_lt (hrpos i))
  have hUcoord (i : Fin 3) : ‖U i‖ ^ 2 = p i := by
    change
      ‖z i / (((2 * Real.sqrt (r i) : ℝ) : ℂ))‖ ^ 2 =
        p i
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (mul_pos (by norm_num) (Real.sqrt_pos.2 (hrpos i))),
      div_pow]
    rw [hzcoord]
    have hden :
        (2 * Real.sqrt (r i)) ^ 2 = 4 * r i := by
      nlinarith [Real.sq_sqrt (le_of_lt (hrpos i))]
    rw [hden]
    field_simp [ne_of_gt (hrpos i)]
  have hVnormsq : ‖V‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp_rw [hVcoord]
    simp [r, Fin.sum_univ_succ]
    linarith
  have hUnormsq : ‖U‖ ^ 2 = 1 := by
    rw [PiLp.norm_sq_eq_of_L2]
    simp_rw [hUcoord]
    simp [p, Fin.sum_univ_succ]
    ring
  have hVnorm : ‖V‖ = 1 := by
    nlinarith [norm_nonneg V]
  have hUnorm : ‖U‖ = 1 := by
    nlinarith [norm_nonneg U]
  have hterm (i : Fin 3) : inner ℂ (V i) (U i) = z i / 2 := by
    have hsqrt : Real.sqrt (r i) ≠ 0 :=
      ne_of_gt (Real.sqrt_pos.2 (hrpos i))
    rw [RCLike.inner_apply]
    dsimp [V, U]
    change
      (z i / (((2 * Real.sqrt (r i) : ℝ) : ℂ))) *
          star (((Real.sqrt (r i) : ℝ) : ℂ)) =
        z i / 2
    have hstar :
        star (((Real.sqrt (r i) : ℝ) : ℂ)) =
          (((Real.sqrt (r i) : ℝ) : ℂ)) := by
      exact Complex.conj_ofReal _
    rw [hstar]
    field_simp [hsqrt]
    push_cast
    ring
  have hVU : inner ℂ V U = 0 := by
    rw [PiLp.inner_apply]
    simp_rw [hterm]
    simp [z, Fin.sum_univ_succ]
    linear_combination hzsum / 2
  obtain ⟨W, hWnorm, hVW, hUW⟩ :=
    exists_unit_orthogonal_pair
      (H := EuclideanSpace ℂ (Fin 3)) (by simp) V U
  let w : Fin 3 → EuclideanSpace ℂ (Fin 3) := ![V, U, W]
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    have hUV : inner ℂ U V = 0 := inner_eq_zero_symm.mp hVU
    have hWV : inner ℂ W V = 0 := inner_eq_zero_symm.mp hVW
    have hWU : inner ℂ W U = 0 := inner_eq_zero_symm.mp hUW
    fin_cases i <;> fin_cases j <;>
      simp [w, inner_self_eq_norm_sq_to_K, hVnorm, hUnorm, hWnorm,
        hVU, hUV, hVW, hWV, hUW, hWU]
  have hcard :
      Fintype.card (Fin 3) =
        Module.finrank ℂ (EuclideanSpace ℂ (Fin 3)) := by
    simp
  let d₀ : Module.Basis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) :=
    basisOfOrthonormalOfCardEqFinrank hw hcard
  have hd₀ : (d₀ : Fin 3 → EuclideanSpace ℂ (Fin 3)) = w :=
    coe_basisOfOrthonormalOfCardEqFinrank hw hcard
  let d : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) :=
    d₀.toOrthonormalBasis (by simpa [hd₀] using hw)
  have hd : (d : Fin 3 → EuclideanSpace ℂ (Fin 3)) = w := by
    simpa only [d, Module.Basis.coe_toOrthonormalBasis] using hd₀
  have hWcoord (i : Fin 3) : ‖W i‖ ^ 2 = 1 - r i - p i := by
    have hrow := d.sum_sq_norm_inner_left
      (EuclideanSpace.basisFun (Fin 3) ℂ i)
    simp only [EuclideanSpace.basisFun_inner,
      OrthonormalBasis.norm_eq_one, one_pow] at hrow
    simp_rw [hd] at hrow
    simp [w, Fin.sum_univ_succ] at hrow
    rw [hVcoord, hUcoord] at hrow
    linarith
  refine ⟨d, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [show d 0 = V by simp [hd, w]]
    ext i
    fin_cases i <;> simp [V, r]
  · simpa [hd, w, p] using hUcoord 0
  · simpa [hd, w, p] using hUcoord 1
  · simpa [hd, w, p] using hUcoord 2
  · rw [show (d 2) 0 = W 0 by simp [hd, w]]
    have h := hWcoord 0
    change ‖W 0‖ ^ 2 = 1 - (1 - a) / 2 - 1 / 2 at h
    linarith
  · rw [show (d 2) 1 = W 1 by simp [hd, w]]
    have h := hWcoord 1
    change ‖W 1‖ ^ 2 = 1 - (1 - b) / 2 - b / 2 at h
    linarith
  · rw [show (d 2) 2 = W 2 by simp [hd, w]]
    have h := hWcoord 2
    change ‖W 2‖ ^ 2 = 1 - (1 - c) / 2 - (1 - b) / 2 at h
    linarith

end

end LeanEval.Analysis
