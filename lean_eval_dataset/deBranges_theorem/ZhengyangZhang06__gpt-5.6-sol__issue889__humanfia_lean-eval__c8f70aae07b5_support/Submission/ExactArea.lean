import Submission.AreaExtension

open Metric Set MeasureTheory

open scoped ENNReal Topology

namespace Submission

lemma det_id_add_mul_conj (q : ℂ) :
    ((1 : ℂ →L[ℝ] ℂ) +
      (q • (1 : ℂ →L[ℝ] ℂ)).comp (Complex.conjCLE : ℂ →L[ℝ] ℂ)).det =
        1 - ‖q‖ ^ 2 := by
  have hmatrix :
      LinearMap.toMatrix Complex.basisOneI Complex.basisOneI
          ((1 : ℂ →L[ℝ] ℂ) +
            (q • (1 : ℂ →L[ℝ] ℂ)).comp
              (Complex.conjCLE : ℂ →L[ℝ] ℂ)).toLinearMap =
        !![1 + q.re, q.im; q.im, 1 - q.re] := by
    ext i j
    fin_cases i <;> fin_cases j
    all_goals simp [LinearMap.toMatrix_apply, Complex.mul_re, Complex.mul_im] <;> ring
  rw [ContinuousLinearMap.det, ← LinearMap.det_toMatrix Complex.basisOneI]
  rw [hmatrix, Matrix.det_fin_two]
  rw [← Complex.normSq_eq_norm_sq]
  simp [Complex.normSq_apply]
  ring

noncomputable def harmonicFillFDeriv (L : ℂ → ℂ) (A : ℝ) (z : ℂ) : ℂ →L[ℝ] ℂ :=
  (1 : ℂ →L[ℝ] ℂ) +
    ((deriv (exteriorAnalyticSlope L) (interiorReflection A z) /
        (A : ℂ) ^ 2) • (1 : ℂ →L[ℝ] ℂ)).comp
      (Complex.conjCLE : ℂ →L[ℝ] ℂ)

lemma hasFDerivAt_exteriorHarmonicFill {L : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAR : 1 / A < R) {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) A) :
    HasFDerivAt (exteriorHarmonicFill L A) (harmonicFillFDeriv L A z) z := by
  have hzA : ‖z‖ ≤ A := by simpa [mem_closedBall_zero_iff] using hz
  have hw : interiorReflection A z ∈ ball (0 : ℂ) R := by
    rw [mem_ball_zero_iff, interiorReflection, norm_div, norm_pow,
      Complex.norm_real, Complex.norm_conj, Real.norm_of_nonneg hA.le]
    calc
      ‖z‖ / A ^ 2 ≤ A / A ^ 2 := div_le_div_of_nonneg_right hzA (sq_nonneg A)
      _ = 1 / A := by field_simp [hA.ne']
      _ < R := hAR
  have hP : HasDerivAt (exteriorAnalyticSlope L)
      (deriv (exteriorAnalyticSlope L) (interiorReflection A z))
      (interiorReflection A z) :=
    (exteriorAnalyticSlope_differentiableOn hR hL).differentiableAt
      (isOpen_ball.mem_nhds hw) |>.hasDerivAt
  have href : HasFDerivAt (interiorReflection A)
      ((1 / A ^ 2 : ℝ) • (Complex.conjCLE : ℂ →L[ℝ] ℂ)) z := by
    have hfun : interiorReflection A =
        fun w : ℂ => (1 / A ^ 2 : ℝ) • starRingEnd ℂ w := by
      funext w
      rw [interiorReflection, Complex.real_smul]
      push_cast
      field_simp [hA.ne']
    rw [hfun]
    exact Complex.conjCLE.hasFDerivAt.const_smul (1 / A ^ 2 : ℝ)
  have hadd := (hasFDerivAt_id z).add (hP.complexToReal_fderiv.comp z href)
  have hfun : exteriorHarmonicFill L A =
      id + exteriorAnalyticSlope L ∘ interiorReflection A := by
    rfl
  rw [hfun]
  have hmap : harmonicFillFDeriv L A z =
      (ContinuousLinearMap.id ℝ ℂ +
        (deriv (exteriorAnalyticSlope L) (interiorReflection A z) •
          (1 : ℂ →L[ℝ] ℂ)).comp
            ((1 / A ^ 2 : ℝ) • (Complex.conjCLE : ℂ →L[ℝ] ℂ))) := by
    ext x
    change x +
        (deriv (exteriorAnalyticSlope L) (interiorReflection A z) / (A : ℂ) ^ 2) *
          starRingEnd ℂ x =
      x + deriv (exteriorAnalyticSlope L) (interiorReflection A z) *
        ((1 / A ^ 2 : ℝ) • starRingEnd ℂ x)
    rw [Complex.real_smul]
    push_cast
    field_simp [hA.ne']
  rw [hmap]
  exact hadd

lemma det_harmonicFillFDeriv (L : ℂ → ℂ) (A : ℝ) (z : ℂ) :
    (harmonicFillFDeriv L A z).det =
      1 - ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z) /
        (A : ℂ) ^ 2‖ ^ 2 := by
  exact det_id_add_mul_conj _

lemma abs_det_harmonicFillFDeriv_le_one {L : ℂ → ℂ} {A ρ : ℝ}
    {M : NNReal} (hA : 0 < A) (hAρ : 1 / A < ρ)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    {z : ℂ} (hz : z ∈ closedBall (0 : ℂ) A) :
    |(harmonicFillFDeriv L A z).det| ≤ 1 := by
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
  have hq : ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z) /
      (A : ℂ) ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, Complex.norm_real, Real.norm_of_nonneg hA.le]
    calc
      ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z)‖ / A ^ 2 ≤
          (M : ℝ) / A ^ 2 := div_le_div_of_nonneg_right hd (sq_nonneg A)
      _ = (M : ℝ) * (A ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ < 1 := hKreal
  have hq2 : ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z) /
      (A : ℂ) ^ 2‖ ^ 2 < 1 := by
    nlinarith [norm_nonneg (deriv (exteriorAnalyticSlope L) (interiorReflection A z) /
      (A : ℂ) ^ 2)]
  rw [det_harmonicFillFDeriv, abs_of_nonneg (sub_nonneg.mpr hq2.le)]
  nlinarith [sq_nonneg
    ‖deriv (exteriorAnalyticSlope L) (interiorReflection A z) / (A : ℂ) ^ 2‖]

def outsideClosedRadius (A : ℝ) : Set ℂ := {z | A ≤ ‖z‖}

lemma inv_lipschitzOnWith_outsideClosed {A : ℝ} (hA : 0 < A) :
    LipschitzOnWith (interiorReflectionLipschitzConstant A)
      (fun z : ℂ => z⁻¹) (outsideClosedRadius A) := by
  apply LipschitzOnWith.of_dist_le_mul
  intro x hx y hy
  have hxnorm : A ≤ ‖x‖ := hx
  have hynorm : A ≤ ‖y‖ := hy
  have hx0 : x ≠ 0 := by
    intro h
    subst x
    simp at hxnorm
    linarith
  have hy0 : y ≠ 0 := by
    intro h
    subst y
    simp at hynorm
    linarith
  rw [dist_inv_inv₀ hx0 hy0]
  change dist x y / (‖x‖ * ‖y‖) ≤ (1 / A ^ 2) * dist x y
  have hden : A ^ 2 ≤ ‖x‖ * ‖y‖ := by nlinarith [norm_nonneg x, norm_nonneg y]
  have hdenpos : 0 < ‖x‖ * ‖y‖ := mul_pos (norm_pos_iff.mpr hx0) (norm_pos_iff.mpr hy0)
  have hinv : (‖x‖ * ‖y‖)⁻¹ ≤ (A ^ 2)⁻¹ :=
    (inv_le_inv₀ hdenpos (sq_pos_of_pos hA)).2 hden
  rw [div_eq_mul_inv, one_div]
  nlinarith [(dist_nonneg : 0 ≤ dist x y)]

lemma inv_mapsTo_closedBall_of_outsideClosed {A ρ : ℝ} (hA : 0 < A)
    (hAρ : 1 / A ≤ ρ) :
    MapsTo (fun z : ℂ => z⁻¹) (outsideClosedRadius A) (closedBall 0 ρ) := by
  intro z hz
  have hznorm : A ≤ ‖z‖ := hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    simp at hznorm
    linarith
  rw [mem_closedBall_zero_iff, norm_inv]
  calc
    ‖z‖⁻¹ ≤ A⁻¹ := (inv_le_inv₀ (norm_pos_iff.mpr hz0) hA).2 hznorm
    _ = 1 / A := by rw [one_div]
    _ ≤ ρ := hAρ

noncomputable def exteriorGluedPerturbation (L : ℂ → ℂ) (A : ℝ) (z : ℂ) : ℂ :=
  if ‖z‖ ≤ A then exteriorAnalyticSlope L (interiorReflection A z)
  else exteriorAnalyticSlope L z⁻¹

@[simp]
lemma exteriorGluedPerturbation_of_mem_closedBall {L : ℂ → ℂ} {A : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) A) :
    exteriorGluedPerturbation L A z = exteriorAnalyticSlope L (interiorReflection A z) := by
  rw [exteriorGluedPerturbation, if_pos]
  simpa [mem_closedBall_zero_iff] using hz

@[simp]
lemma exteriorGluedPerturbation_of_mem_outsideRadius {L : ℂ → ℂ} {A : ℝ} {z : ℂ}
    (hz : z ∈ outsideRadius A) :
    exteriorGluedPerturbation L A z = exteriorAnalyticSlope L z⁻¹ := by
  rw [exteriorGluedPerturbation, if_neg]
  exact not_le.mpr hz

lemma exteriorGluedPerturbation_eq_on_sphere {L : ℂ → ℂ} {A : ℝ} {z : ℂ}
    (hz : z ∈ sphere (0 : ℂ) A) :
    exteriorGluedPerturbation L A z = exteriorAnalyticSlope L z⁻¹ := by
  have hnorm : ‖z‖ = A := by simpa [mem_sphere, dist_zero_right] using hz
  rw [exteriorGluedPerturbation, if_pos hnorm.le, interiorReflection,
    conj_div_real_sq_eq_inv hnorm]

lemma exteriorGluedPerturbation_lipschitzOnWith_inside {L : ℂ → ℂ} {A ρ : ℝ}
    {M : NNReal} (hA : 0 < A) (hAρ : 1 / A ≤ ρ)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ)) :
    LipschitzOnWith (M * interiorReflectionLipschitzConstant A)
      (exteriorGluedPerturbation L A) (closedBall (0 : ℂ) A) := by
  intro x hx y hy
  rw [exteriorGluedPerturbation_of_mem_closedBall hx,
    exteriorGluedPerturbation_of_mem_closedBall hy]
  simpa [exteriorHarmonicFill, interiorReflection] using
    (exteriorHarmonicPerturbation_lipschitzOnWith hA hAρ hP hx hy)

lemma exteriorGluedPerturbation_lipschitzOnWith_outside {L : ℂ → ℂ} {A ρ : ℝ}
    {M : NNReal} (hA : 0 < A) (hAρ : 1 / A ≤ ρ)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ)) :
    LipschitzOnWith (M * interiorReflectionLipschitzConstant A)
      (exteriorGluedPerturbation L A) (outsideClosedRadius A) := by
  have hcomp := hP.comp (inv_lipschitzOnWith_outsideClosed hA)
    (inv_mapsTo_closedBall_of_outsideClosed hA hAρ)
  intro x hx y hy
  have hxeq : exteriorGluedPerturbation L A x = exteriorAnalyticSlope L x⁻¹ := by
    by_cases hxs : ‖x‖ = A
    · exact exteriorGluedPerturbation_eq_on_sphere
        (by simpa [mem_sphere, dist_zero_right] using hxs)
    · rw [exteriorGluedPerturbation_of_mem_outsideRadius]
      exact lt_of_le_of_ne hx (Ne.symm hxs)
  have hyeq : exteriorGluedPerturbation L A y = exteriorAnalyticSlope L y⁻¹ := by
    by_cases hys : ‖y‖ = A
    · exact exteriorGluedPerturbation_eq_on_sphere
        (by simpa [mem_sphere, dist_zero_right] using hys)
    · rw [exteriorGluedPerturbation_of_mem_outsideRadius]
      exact lt_of_le_of_ne hy (Ne.symm hys)
  rw [hxeq, hyeq]
  exact hcomp hx hy

lemma exists_lineMap_norm_eq {A : ℝ} {x y : ℂ} (hx : ‖x‖ ≤ A) (hy : A ≤ ‖y‖) :
    ∃ t ∈ Icc (0 : ℝ) 1, ‖AffineMap.lineMap x y t‖ = A := by
  let g : ℝ → ℝ := fun t => ‖AffineMap.lineMap x y t‖
  have hg : ContinuousOn g (Icc (0 : ℝ) 1) := by
    fun_prop
  have hA : A ∈ Icc (g 0) (g 1) := by
    simpa [g] using And.intro hx hy
  rcases intermediate_value_Icc (show (0 : ℝ) ≤ 1 by norm_num) hg hA with
    ⟨t, ht, hgt⟩
  exact ⟨t, ht, hgt⟩

lemma dist_lineMap_add_dist_lineMap {x y : ℂ} {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    dist x (AffineMap.lineMap x y t) + dist (AffineMap.lineMap x y t) y =
      dist x y := by
  rw [dist_left_lineMap, dist_lineMap_right, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg ht.1, abs_of_nonneg (sub_nonneg.mpr ht.2)]
  ring

lemma exteriorGluedPerturbation_lipschitzWith {L : ℂ → ℂ} {A ρ : ℝ}
    {M : NNReal} (hA : 0 < A) (hAρ : 1 / A ≤ ρ)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ)) :
    LipschitzWith (M * interiorReflectionLipschitzConstant A)
      (exteriorGluedPerturbation L A) := by
  let K : NNReal := M * interiorReflectionLipschitzConstant A
  have hin : LipschitzOnWith K (exteriorGluedPerturbation L A)
      (closedBall (0 : ℂ) A) :=
    exteriorGluedPerturbation_lipschitzOnWith_inside hA hAρ hP
  have hout : LipschitzOnWith K (exteriorGluedPerturbation L A)
      (outsideClosedRadius A) :=
    exteriorGluedPerturbation_lipschitzOnWith_outside hA hAρ hP
  apply LipschitzWith.of_dist_le_mul
  intro x y
  by_cases hx : ‖x‖ ≤ A
  · by_cases hy : ‖y‖ ≤ A
    · exact hin.dist_le_mul x (by simpa [mem_closedBall_zero_iff]) y
        (by simpa [mem_closedBall_zero_iff])
    · have hyout : A ≤ ‖y‖ := (not_le.mp hy).le
      rcases exists_lineMap_norm_eq hx hyout with ⟨t, ht, hnorm⟩
      let p : ℂ := AffineMap.lineMap x y t
      have hpin : p ∈ closedBall (0 : ℂ) A := by
        simpa [p, mem_closedBall_zero_iff] using hnorm.le
      have hpout : p ∈ outsideClosedRadius A := by
        exact hnorm.ge
      calc
        dist (exteriorGluedPerturbation L A x) (exteriorGluedPerturbation L A y) ≤
            dist (exteriorGluedPerturbation L A x) (exteriorGluedPerturbation L A p) +
              dist (exteriorGluedPerturbation L A p)
                (exteriorGluedPerturbation L A y) := dist_triangle _ _ _
        _ ≤ K * dist x p + K * dist p y := add_le_add
          (hin.dist_le_mul x (by simpa [mem_closedBall_zero_iff]) p hpin)
          (hout.dist_le_mul p hpout y hyout)
        _ = K * dist x y := by
          rw [← mul_add, dist_lineMap_add_dist_lineMap ht]
  · by_cases hy : ‖y‖ ≤ A
    · have hxout : A ≤ ‖x‖ := (not_le.mp hx).le
      rcases exists_lineMap_norm_eq hy hxout with ⟨t, ht, hnorm⟩
      let p : ℂ := AffineMap.lineMap y x t
      have hpin : p ∈ closedBall (0 : ℂ) A := by
        simpa [p, mem_closedBall_zero_iff] using hnorm.le
      have hpout : p ∈ outsideClosedRadius A := by
        exact hnorm.ge
      calc
        dist (exteriorGluedPerturbation L A x) (exteriorGluedPerturbation L A y) =
            dist (exteriorGluedPerturbation L A y)
              (exteriorGluedPerturbation L A x) := dist_comm _ _
        _ ≤ dist (exteriorGluedPerturbation L A y)
              (exteriorGluedPerturbation L A p) +
            dist (exteriorGluedPerturbation L A p)
              (exteriorGluedPerturbation L A x) := dist_triangle _ _ _
        _ ≤ K * dist y p + K * dist p x := add_le_add
          (hin.dist_le_mul y (by simpa [mem_closedBall_zero_iff]) p hpin)
          (hout.dist_le_mul p hpout x hxout)
        _ = K * dist y x := by
          rw [← mul_add, dist_lineMap_add_dist_lineMap ht]
        _ = K * dist x y := by rw [dist_comm]
    · exact hout.dist_le_mul x (not_le.mp hx).le y (not_le.mp hy).le

noncomputable def exteriorGluedMap (L : ℂ → ℂ) (A : ℝ) (z : ℂ) : ℂ :=
  z + exteriorGluedPerturbation L A z

lemma exteriorGluedMap_eq_fill {L : ℂ → ℂ} {A : ℝ} {z : ℂ}
    (hz : z ∈ closedBall (0 : ℂ) A) :
    exteriorGluedMap L A z = exteriorHarmonicFill L A z := by
  rw [exteriorGluedMap, exteriorGluedPerturbation_of_mem_closedBall hz]
  rfl

lemma exteriorGluedMap_eq_exteriorTransform {f L : ℂ → ℂ} {R A : ℝ}
    (hR : 0 < R) (hRA : 1 / R < A) (hf : NormalizedUnivalentOn f R)
    (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    {z : ℂ} (hz : z ∈ outsideRadius A) :
    exteriorGluedMap L A z = exteriorTransform f z := by
  have hzext : z ∈ exteriorDisk R := hRA.trans hz
  have hz0 := ne_zero_of_mem_exteriorDisk hR hzext
  rw [exteriorGluedMap, exteriorGluedPerturbation_of_mem_outsideRadius hz,
    exteriorAnalyticSlope, dslope_of_ne _ (inv_ne_zero hz0), slope_def_field,
    exteriorAnalyticFactor_zero hL0,
    exteriorTransform_eq_mul_exp_neg hR hf hexp hzext]
  unfold exteriorAnalyticFactor
  field_simp [hz0]
  ring

lemma exists_exteriorGluedMap_homeomorph {L : ℂ → ℂ} {A ρ : ℝ}
    {M : NNReal} (hA : 0 < A) (hAρ : 1 / A ≤ ρ)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1) :
    ∃ e : ℂ ≃ₜ ℂ, ∀ z, e z = exteriorGluedMap L A z := by
  let K : NNReal := M * interiorReflectionLipschitzConstant A
  have hu : LipschitzWith K (exteriorGluedPerturbation L A) :=
    exteriorGluedPerturbation_lipschitzWith hA hAρ hP
  let idEquiv : ℂ ≃L[ℝ] ℂ := ContinuousLinearEquiv.refl ℝ ℂ
  have happrox : ApproximatesLinearOn (exteriorGluedMap L A)
      (idEquiv : ℂ →L[ℝ] ℂ) univ K := by
    intro x hx y hy
    change ‖(x + exteriorGluedPerturbation L A x) -
        (y + exteriorGluedPerturbation L A y) - (x - y)‖ ≤ K * ‖x - y‖
    calc
      ‖(x + exteriorGluedPerturbation L A x) -
          (y + exteriorGluedPerturbation L A y) - (x - y)‖ =
          ‖exteriorGluedPerturbation L A x -
            exteriorGluedPerturbation L A y‖ := by
        congr 1
        ring
      _ ≤ K * ‖x - y‖ := hu.norm_sub_le x y
  have hidnorm : ‖(idEquiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ = 1 := by
    simp [idEquiv]
  have hsmall : Subsingleton ℂ ∨ K < ‖(idEquiv.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := by
    right
    simpa only [hidnorm] using hK
  let e : ℂ ≃ₜ ℂ := happrox.toHomeomorph (exteriorGluedMap L A) hsmall
  exact ⟨e, fun _ => rfl⟩

lemma exteriorTransform_image_closedAnnulus_subset_fill_image
    {f L : ℂ → ℂ} {R r A : ℝ}
    (hR : 0 < R) (hRA : 1 / R < A) (hf : NormalizedUnivalentOn f R)
    (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) {e : ℂ ≃ₜ ℂ}
    (he : ∀ z, e z = exteriorGluedMap L A z) :
    exteriorTransform f '' closedAnnulus r A ⊆
      exteriorHarmonicFill L A '' closedBall (0 : ℂ) A := by
  have hfill : Set.EqOn (exteriorHarmonicFill L A) e (closedBall (0 : ℂ) A) := by
    intro z hz
    rw [he, exteriorGluedMap_eq_fill hz]
  rintro w ⟨z, hz, rfl⟩
  let u : ℂ := e.symm (exteriorTransform f z)
  have heu : e u = exteriorTransform f z := e.apply_symm_apply _
  have hu : u ∈ closedBall (0 : ℂ) A := by
    by_contra hu
    have huout : u ∈ outsideRadius A := by
      rw [outsideRadius, mem_setOf_eq]
      exact not_le.mp (by simpa [mem_closedBall_zero_iff] using hu)
    have huext : u ∈ exteriorDisk R := hRA.trans huout
    have hzext : z ∈ exteriorDisk R := closedAnnulus_subset_exteriorDisk hr hz
    have heuext : exteriorTransform f u = exteriorTransform f z := by
      rw [← exteriorGluedMap_eq_exteriorTransform hR hRA hf hL0 hexp huout,
        ← he u]
      exact heu
    have huz : u = z := exteriorTransform_injOn hR hf huext hzext heuext
    apply hu
    rw [huz]
    exact hz.1
  exact ⟨u, hu, by rw [hfill hu, heu]⟩

lemma volume_exteriorHarmonicFill_image_le {L : ℂ → ℂ} {R A ρ : ℝ}
    {M : NNReal} (hR : 0 < R) (hL : DifferentiableOn ℂ L (ball 0 R))
    (hA : 0 < A) (hAρ : 1 / A < ρ) (hρR : ρ < R)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1)
    (hinj : (closedBall (0 : ℂ) A).InjOn (exteriorHarmonicFill L A)) :
    volume (exteriorHarmonicFill L A '' closedBall (0 : ℂ) A) ≤
      ENNReal.ofReal A ^ 2 * NNReal.pi := by
  rw [← Complex.volume_closedBall (0 : ℂ) A]
  rw [← MeasureTheory.lintegral_abs_det_fderiv_eq_addHaar_image volume
    (measurableSet_closedBall : MeasurableSet (closedBall (0 : ℂ) A))
    (fun z hz => (hasFDerivAt_exteriorHarmonicFill hR hL hA
      (hAρ.trans hρR) hz).hasFDerivWithinAt) hinj]
  calc
    (∫⁻ z in closedBall (0 : ℂ) A,
        ENNReal.ofReal |(harmonicFillFDeriv L A z).det|) ≤
        ∫⁻ _ in closedBall (0 : ℂ) A, ENNReal.ofReal 1 := by
      apply MeasureTheory.setLIntegral_mono'
        (measurableSet_closedBall : MeasurableSet (closedBall (0 : ℂ) A))
      intro z hz
      exact ENNReal.ofReal_le_ofReal
        (abs_det_harmonicFillFDeriv_le_one hA hAρ hP hK hz)
    _ = volume (closedBall (0 : ℂ) A) := by simp

lemma exteriorTransform_area_le_exact {f L : ℂ → ℂ} {R r A ρ : ℝ}
    {M : NNReal} (hR : 0 < R) (hf : NormalizedUnivalentOn f R)
    (hL : DifferentiableOn ℂ L (ball 0 R)) (hL0 : L 0 = 0)
    (hexp : ∀ z ∈ ball (0 : ℂ) R, Complex.exp (L z) = dslope f 0 z)
    (hr : 1 / R < r) (hrA : r ≤ A) (hA : 0 < A)
    (hAρ : 1 / A < ρ) (hρR : ρ < R)
    (hP : LipschitzOnWith M (exteriorAnalyticSlope L) (closedBall (0 : ℂ) ρ))
    (hK : M * interiorReflectionLipschitzConstant A < 1) :
    (∫⁻ z in closedAnnulus r A,
      ENNReal.ofReal (‖deriv (exteriorTransform f) z‖ ^ 2)) ≤
        ENNReal.ofReal A ^ 2 * NNReal.pi := by
  have hRA : 1 / R < A := hr.trans_le hrA
  rcases exists_exteriorGluedMap_homeomorph hA hAρ.le hP hK with ⟨e, he⟩
  have hfill : Set.EqOn (exteriorHarmonicFill L A) e (closedBall (0 : ℂ) A) := by
    intro z hz
    rw [he, exteriorGluedMap_eq_fill hz]
  have hinjFill : (closedBall (0 : ℂ) A).InjOn (exteriorHarmonicFill L A) := by
    intro x hx y hy hxy
    apply e.injective
    rw [← hfill hx, ← hfill hy]
    exact hxy
  have himage := exteriorTransform_image_closedAnnulus_subset_fill_image
    hR hRA hf hL0 hexp hr he
  rw [lintegral_norm_deriv_sq_eq_volume_image
    (measurableSet_closedAnnulus r A)
    (fun z hz => exteriorTransform_differentiableAt hR hf
      (closedAnnulus_subset_exteriorDisk hr hz))
    ((exteriorTransform_injOn hR hf).mono (closedAnnulus_subset_exteriorDisk hr))]
  exact (measure_mono himage).trans
    (volume_exteriorHarmonicFill_image_le hR hL hA hAρ hρR hP hK hinjFill)

end Submission
