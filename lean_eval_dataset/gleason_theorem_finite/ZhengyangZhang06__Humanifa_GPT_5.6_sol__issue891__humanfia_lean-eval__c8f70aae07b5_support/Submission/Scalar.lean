import Submission.ThreeFrame

namespace LeanEval.Analysis

noncomputable section

/-- The average over the four coordinate-sign choices, modulo the global sign. -/
def signAverage3
    {H : Type*} [AddCommGroup H] (q : H → ℝ) (x y z : H) : ℝ :=
  (q (x + y + z) + q (x + y - z) +
    q (x - y + z) + q (x - y - z)) / 4

/-- The part of the three-coordinate sign average not accounted for by the
three coordinate axes. -/
def signResidual3
    {H : Type*} [AddCommGroup H] (q : H → ℝ) (x y z : H) : ℝ :=
  signAverage3 q x y z - q x - q y - q z

def coordinateTwist3 (s : Fin 3 → ℂ)
    (x : EuclideanSpace ℂ (Fin 3)) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 (fun i ↦ s i * x i)

lemma inner_coordinateTwist3
    (s : Fin 3 → ℂ) (hs : ∀ i, starRingEnd ℂ (s i) * s i = 1)
    (x y : EuclideanSpace ℂ (Fin 3)) :
    inner ℂ (coordinateTwist3 s x) (coordinateTwist3 s y) =
      inner ℂ x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  apply Finset.sum_congr rfl
  intro i _
  rw [RCLike.inner_apply', RCLike.inner_apply']
  simp only [coordinateTwist3, map_mul, starRingEnd_apply]
  have hs' : star (s i) * s i = 1 := by
    simpa only [starRingEnd_apply] using hs i
  calc
    _ = (star (s i) * s i) * (star (x i) * y i) := by ring
    _ = _ := by rw [hs']; simp

lemma FrameFunction.sum_signResidual3_orthonormalBasis
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    (e : OrthonormalBasis (Fin 3) ℂ K)
    (d : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3))) :
    ∑ j : Fin 3,
        signResidual3 f.homogeneousValue
          ((d j 0) • (e 0 : H))
          ((d j 1) • (e 1 : H))
          ((d j 2) • (e 2 : H)) = 0 := by
  classical
  let s₁ : Fin 3 → ℂ := ![1, 1, 1]
  let s₂ : Fin 3 → ℂ := ![1, 1, -1]
  let s₃ : Fin 3 → ℂ := ![1, -1, 1]
  let s₄ : Fin 3 → ℂ := ![1, -1, -1]
  let v (s : Fin 3 → ℂ) (j : Fin 3) : K :=
    e.repr.symm (coordinateTwist3 s (d j))
  have hs₁ (i : Fin 3) : starRingEnd ℂ (s₁ i) * s₁ i = 1 := by
    fin_cases i <;> norm_num [s₁]
  have hs₂ (i : Fin 3) : starRingEnd ℂ (s₂ i) * s₂ i = 1 := by
    fin_cases i <;> norm_num [s₂]
  have hs₃ (i : Fin 3) : starRingEnd ℂ (s₃ i) * s₃ i = 1 := by
    fin_cases i <;> norm_num [s₃]
  have hs₄ (i : Fin 3) : starRingEnd ℂ (s₄ i) * s₄ i = 1 := by
    fin_cases i <;> norm_num [s₄]
  have hv (s : Fin 3 → ℂ)
      (hs : ∀ i, starRingEnd ℂ (s i) * s i = 1) :
      Orthonormal ℂ (v s) := by
    rw [orthonormal_iff_ite]
    intro i j
    simp only [v, LinearIsometryEquiv.inner_map_map]
    rw [inner_coordinateTwist3 s hs]
    exact orthonormal_iff_ite.mp d.orthonormal i j
  have hcard :
      Fintype.card (Fin 3) = Module.finrank ℂ K := by
    rw [Module.finrank_eq_card_basis e.toBasis]
  have hsum (s : Fin 3 → ℂ)
      (hs : ∀ i, starRingEnd ℂ (s i) * s i = 1) :
      ∑ j, f.homogeneousValue (v s j : H) = f.μ K.starProjection :=
    f.sum_homogeneousValue_of_orthonormal_submodule K (v s) (hv s hs) hcard
  have hrepr (s : Fin 3 → ℂ) (j : Fin 3) :
      (v s j : H) =
        (s 0 * d j 0) • (e 0 : H) +
          (s 1 * d j 1) • (e 1 : H) +
          (s 2 * d j 2) • (e 2 : H) := by
    have h := congrArg Subtype.val
      (e.sum_repr_symm (coordinateTwist3 s (d j)))
    simp only [v, coordinateTwist3] at h ⊢
    simpa [Fin.sum_univ_succ, add_assoc] using h.symm
  have h₁ :
      ∑ j, f.homogeneousValue
        ((d j 0) • (e 0 : H) + (d j 1) • (e 1 : H) +
          (d j 2) • (e 2 : H)) = f.μ K.starProjection := by
    simpa [hrepr, s₁] using hsum s₁ hs₁
  have h₂ :
      ∑ j, f.homogeneousValue
        ((d j 0) • (e 0 : H) + (d j 1) • (e 1 : H) -
          (d j 2) • (e 2 : H)) = f.μ K.starProjection := by
    simpa [hrepr, s₂, sub_eq_add_neg] using hsum s₂ hs₂
  have h₃ :
      ∑ j, f.homogeneousValue
        ((d j 0) • (e 0 : H) - (d j 1) • (e 1 : H) +
          (d j 2) • (e 2 : H)) = f.μ K.starProjection := by
    simpa [hrepr, s₃, sub_eq_add_neg] using hsum s₃ hs₃
  have h₄ :
      ∑ j, f.homogeneousValue
        ((d j 0) • (e 0 : H) - (d j 1) • (e 1 : H) -
          (d j 2) • (e 2 : H)) = f.μ K.starProjection := by
    simpa [hrepr, s₄, sub_eq_add_neg] using hsum s₄ hs₄
  have hrow (i : Fin 3) : ∑ j, ‖d j i‖ ^ 2 = 1 := by
    simpa only [EuclideanSpace.basisFun_inner,
      OrthonormalBasis.norm_eq_one, one_pow] using
      d.sum_sq_norm_inner_left (EuclideanSpace.basisFun (Fin 3) ℂ i)
  have haxis (i : Fin 3) :
      ∑ j, f.homogeneousValue ((d j i) • (e i : H)) =
        f.homogeneousValue (e i : H) := by
    simp_rw [f.homogeneousValue_smul]
    rw [← Finset.sum_mul, hrow]
    ring
  have hbase :
      ∑ i, f.homogeneousValue (e i : H) = f.μ K.starProjection :=
    f.sum_homogeneousValue_orthonormalBasis_submodule K e
  rw [show (∑ j, signResidual3 f.homogeneousValue
      ((d j 0) • (e 0 : H)) ((d j 1) • (e 1 : H))
      ((d j 2) • (e 2 : H))) =
      ((∑ j, f.homogeneousValue
          ((d j 0) • (e 0 : H) + (d j 1) • (e 1 : H) +
            (d j 2) • (e 2 : H))) +
        (∑ j, f.homogeneousValue
          ((d j 0) • (e 0 : H) + (d j 1) • (e 1 : H) -
            (d j 2) • (e 2 : H))) +
        (∑ j, f.homogeneousValue
          ((d j 0) • (e 0 : H) - (d j 1) • (e 1 : H) +
            (d j 2) • (e 2 : H))) +
        (∑ j, f.homogeneousValue
          ((d j 0) • (e 0 : H) - (d j 1) • (e 1 : H) -
            (d j 2) • (e 2 : H)))) / 4 -
        (∑ j, f.homogeneousValue ((d j 0) • (e 0 : H))) -
        (∑ j, f.homogeneousValue ((d j 1) • (e 1 : H))) -
        (∑ j, f.homogeneousValue ((d j 2) • (e 2 : H))) by
      simp only [signResidual3, signAverage3, Finset.sum_sub_distrib]
      rw [← Finset.sum_div]
      simp only [Finset.sum_add_distrib]]
  rw [h₁, h₂, h₃, h₄, haxis 0, haxis 1, haxis 2]
  have hbase' :
      f.homogeneousValue (e 0 : H) +
          f.homogeneousValue (e 1 : H) +
        f.homogeneousValue (e 2 : H) =
      f.μ K.starProjection := by
    simpa [Fin.sum_univ_succ, add_assoc] using hbase
  linarith

lemma signResidual3_zero_right
    {H : Type*} [AddCommGroup H] (q : H → ℝ)
    (hzero : q 0 = 0) (x y : H) :
    signResidual3 q x y 0 = quadraticDefect q x y / 2 := by
  rw [signResidual3, signAverage3, quadraticDefect, hzero]
  simp only [add_zero, sub_zero]
  ring

lemma signResidual3_swap_first_two
    {H : Type*} [AddCommGroup H] (q : H → ℝ)
    (heven : ∀ v, q (-v) = q v) (x y z : H) :
    signResidual3 q x y z = signResidual3 q y x z := by
  rw [signResidual3, signResidual3, signAverage3, signAverage3,
    show y + x + z = x + y + z by abel,
    show y + x - z = x + y - z by abel]
  have h₁ : q (y - x + z) = q (x - y - z) := by
    rw [show y - x + z = -(x - y - z) by abel, heven]
  have h₂ : q (y - x - z) = q (x - y + z) := by
    rw [show y - x - z = -(x - y + z) by abel, heven]
  rw [h₁, h₂]
  ring

lemma signResidual3_swap_last_two
    {H : Type*} [AddCommGroup H] (q : H → ℝ) (x y z : H) :
    signResidual3 q x y z = signResidual3 q x z y := by
  rw [signResidual3, signResidual3, signAverage3, signAverage3,
    show x + z + y = x + y + z by abel,
    show x + z - y = x - y + z by abel,
    show x - z + y = x + y - z by abel,
    show x - z - y = x - y - z by abel]
  ring

lemma FrameFunction.signResidual3_smul
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (f : FrameFunction H) (c : ℂ) (x y z : H) :
    signResidual3 f.homogeneousValue (c • x) (c • y) (c • z) =
      ‖c‖ ^ 2 * signResidual3 f.homogeneousValue x y z := by
  rw [signResidual3, signResidual3, signAverage3, signAverage3,
    show c • x + c • y + c • z = c • (x + y + z) by module,
    show c • x + c • y - c • z = c • (x + y - z) by module,
    show c • x - c • y + c • z = c • (x - y + z) by module,
    show c • x - c • y - c • z = c • (x - y - z) by module]
  simp only [f.homogeneousValue_smul]
  ring

lemma FrameFunction.abs_signResidual3_le_of_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (f : FrameFunction H) {x y z : H}
    (hxy : inner ℂ x y = 0) (hxz : inner ℂ x z = 0)
    (hyz : inner ℂ y z = 0) :
    |signResidual3 f.homogeneousValue x y z| ≤
      ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
  have hxyz₁ :
      ‖x + y + z‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    calc
      ‖x + y + z‖ ^ 2 =
          ‖x + y‖ ^ 2 + 2 * RCLike.re (inner ℂ (x + y) z) + ‖z‖ ^ 2 :=
        norm_add_sq (𝕜 := ℂ) (x + y) z
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := ℂ), inner_add_left, hxy, hxz, hyz]
        norm_num
  have hxyz₂ :
      ‖x + y - z‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    calc
      ‖x + y - z‖ ^ 2 =
          ‖x + y‖ ^ 2 - 2 * RCLike.re (inner ℂ (x + y) z) + ‖z‖ ^ 2 :=
        norm_sub_sq (𝕜 := ℂ) (x + y) z
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
        rw [norm_add_sq (𝕜 := ℂ), inner_add_left, hxy, hxz, hyz]
        norm_num
  have hxyz₃ :
      ‖x - y + z‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    calc
      ‖x - y + z‖ ^ 2 =
          ‖x - y‖ ^ 2 + 2 * RCLike.re (inner ℂ (x - y) z) + ‖z‖ ^ 2 :=
        norm_add_sq (𝕜 := ℂ) (x - y) z
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
        rw [norm_sub_sq (𝕜 := ℂ), inner_sub_left, hxy, hxz, hyz]
        norm_num
  have hxyz₄ :
      ‖x - y - z‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    calc
      ‖x - y - z‖ ^ 2 =
          ‖x - y‖ ^ 2 - 2 * RCLike.re (inner ℂ (x - y) z) + ‖z‖ ^ 2 :=
        norm_sub_sq (𝕜 := ℂ) (x - y) z
      _ = ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
        rw [norm_sub_sq (𝕜 := ℂ), inner_sub_left, hxy, hxz, hyz]
        norm_num
  have havg_nonneg : 0 ≤ signAverage3 f.homogeneousValue x y z := by
    rw [signAverage3]
    linarith [f.homogeneousValue_nonneg (x + y + z),
      f.homogeneousValue_nonneg (x + y - z),
      f.homogeneousValue_nonneg (x - y + z),
      f.homogeneousValue_nonneg (x - y - z)]
  have havg_le : signAverage3 f.homogeneousValue x y z ≤
      ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    rw [signAverage3]
    nlinarith [f.homogeneousValue_le_norm_sq (x + y + z),
      f.homogeneousValue_le_norm_sq (x + y - z),
      f.homogeneousValue_le_norm_sq (x - y + z),
      f.homogeneousValue_le_norm_sq (x - y - z)]
  have haxes_nonneg : 0 ≤ f.homogeneousValue x + f.homogeneousValue y +
      f.homogeneousValue z := by
    linarith [f.homogeneousValue_nonneg x,
      f.homogeneousValue_nonneg y, f.homogeneousValue_nonneg z]
  have haxes_le : f.homogeneousValue x + f.homogeneousValue y +
      f.homogeneousValue z ≤ ‖x‖ ^ 2 + ‖y‖ ^ 2 + ‖z‖ ^ 2 := by
    linarith [f.homogeneousValue_le_norm_sq x,
      f.homogeneousValue_le_norm_sq y, f.homogeneousValue_le_norm_sq z]
  rw [signResidual3, abs_le]
  constructor <;> linarith

/-- If the middle squared norm is the sum of the other two, the
three-coordinate sign residual collapses to the residual on the opposite
edge. -/
lemma FrameFunction.signResidual3_of_orthogonal_norm_add
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (f : FrameFunction H) {x y z : H}
    (hxy : inner ℂ x y = 0) (hxz : inner ℂ x z = 0)
    (hyz : inner ℂ y z = 0)
    (hnorm : ‖y‖ ^ 2 = ‖x‖ ^ 2 + ‖z‖ ^ 2) :
    signResidual3 f.homogeneousValue x y z =
      quadraticDefect f.homogeneousValue x z / 2 := by
  have hyx : inner ℂ y x = 0 := inner_eq_zero_symm.mp hxy
  have hzx : inner ℂ z x = 0 := inner_eq_zero_symm.mp hxz
  have hzy : inner ℂ z y = 0 := inner_eq_zero_symm.mp hyz
  have hnorm' : ‖x‖ ^ 2 - ‖y‖ ^ 2 + ‖z‖ ^ 2 = 0 := by
    linarith
  have huv₁ : inner ℂ (x + y + z) (x - y + z) = 0 := by
    simp only [inner_add_left, inner_add_right, inner_sub_right,
      hxy, hxz, hyz, hyx, hzx, hzy,
      inner_self_eq_norm_sq_to_K]
    norm_num only [add_zero, zero_add, sub_zero, zero_sub]
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hnorm'
    push_cast at hc
    ring_nf at hc ⊢
    exact hc
  have huv₂ : inner ℂ (x + y - z) (x - y - z) = 0 := by
    simp only [inner_add_left, inner_sub_left, inner_sub_right,
      hxy, hxz, hyz, hyx, hzx, hzy,
      inner_self_eq_norm_sq_to_K]
    norm_num only [add_zero, zero_add, sub_zero, zero_sub]
    have hc := congrArg (fun t : ℝ => (t : ℂ)) hnorm'
    push_cast at hc
    ring_nf at hc ⊢
    exact hc
  have hnorm₁ : ‖x + y + z‖ = ‖x - y + z‖ := by
    have h₁ := norm_add_sq (𝕜 := ℂ) (x + z) y
    have h₂ := norm_sub_sq (𝕜 := ℂ) (x + z) y
    have horth : inner ℂ (x + z) y = 0 := by simp [hxy, hzy]
    rw [horth] at h₁ h₂
    norm_num at h₁ h₂
    rw [show x + y + z = (x + z) + y by abel,
      show x - y + z = (x + z) - y by abel]
    nlinarith [norm_nonneg ((x + z) + y), norm_nonneg ((x + z) - y)]
  have hnorm₂ : ‖x + y - z‖ = ‖x - y - z‖ := by
    have h₁ := norm_add_sq (𝕜 := ℂ) (x - z) y
    have h₂ := norm_sub_sq (𝕜 := ℂ) (x - z) y
    have horth : inner ℂ (x - z) y = 0 := by simp [hxy, hzy]
    rw [horth] at h₁ h₂
    norm_num at h₁ h₂
    rw [show x + y - z = (x - z) + y by abel,
      show x - y - z = (x - z) - y by abel]
    nlinarith [norm_nonneg ((x - z) + y), norm_nonneg ((x - z) - y)]
  have hpara₁ :=
    f.homogeneousValue_parallelogram_of_orthogonal_of_norm_eq huv₁ hnorm₁
  have hpara₂ :=
    f.homogeneousValue_parallelogram_of_orthogonal_of_norm_eq huv₂ hnorm₂
  rw [show x + y + z + (x - y + z) = (2 : ℂ) • (x + z) by module,
    show x + y + z - (x - y + z) = (2 : ℂ) • y by module,
    f.homogeneousValue_smul, f.homogeneousValue_smul] at hpara₁
  rw [show x + y - z + (x - y - z) = (2 : ℂ) • (x - z) by module,
    show x + y - z - (x - y - z) = (2 : ℂ) • y by module,
    f.homogeneousValue_smul, f.homogeneousValue_smul] at hpara₂
  norm_num at hpara₁ hpara₂
  rw [signResidual3, signAverage3, quadraticDefect]
  linarith

/-- The algebraic cancellation used to express an arbitrary quadratic defect
as a linear combination of defects on auxiliary pairs. -/
lemma quadraticDefect_orthogonalization_identity
    {E : Type*} [AddCommGroup E] (q : E → ℝ) (x y z w : E) :
    quadraticDefect q (x + z) (y + w) +
          quadraticDefect q (x - z) (y - w) -
          quadraticDefect q (x + y) (z + w) -
          quadraticDefect q (x - y) (z - w) =
      2 * quadraticDefect q x y - 2 * quadraticDefect q x z -
        2 * quadraticDefect q y w + 2 * quadraticDefect q z w := by
  simp only [quadraticDefect]
  abel_nf
  ring

lemma eq_zero_of_abs_two_pow_mul_le (a C : ℝ)
    (h : ∀ n : ℕ, |(2 : ℝ) ^ n * a| ≤ C) : a = 0 := by
  by_contra ha
  have habs : 0 < |a| := abs_pos.mpr ha
  obtain ⟨n, hn⟩ : ∃ n : ℕ, C / |a| < (2 : ℝ) ^ n :=
    (tendsto_pow_atTop_atTop_of_one_lt one_lt_two).eventually_gt_atTop
      (C / |a|) |>.exists
  have hlarge : C < (2 : ℝ) ^ n * |a| :=
    (div_lt_iff₀ habs).mp hn
  have hbound := h n
  rw [abs_mul, abs_pow, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)] at hbound
  linarith

lemma balanced_cocycle_middle_eq_zero
    (A B C : ℝ → ℝ)
    (_hA0 : A 0 = 0) (_hB0 : B 0 = 0) (_hC0 : C 0 = 0)
    (hAh : A (1 / 2) = 0) (hBh : B (1 / 2) = 0)
    (hCh : C (1 / 2) = 0)
    (hAcomp : ∀ t, 0 ≤ t → t ≤ 1 → A (1 - t) = -A t)
    (hBcomp : ∀ t, 0 ≤ t → t ≤ 1 → B (1 - t) = -B t)
    (hCcomp : ∀ t, 0 ≤ t → t ≤ 1 → C (1 - t) = -C t)
    (hbalanced : ∀ a b c,
      0 ≤ a → 0 ≤ b → 0 ≤ c →
      a ≤ 1 / 2 → b ≤ 1 / 2 → c ≤ 1 / 2 →
      a + b + c = 1 →
      B b + B c = A a + C a)
    (M : ℝ) (hbound : ∀ t, 0 ≤ t → t ≤ 1 → |B t| ≤ M) :
    ∀ t, 0 ≤ t → t ≤ 1 → B t = 0 := by
  have hreflect (t : ℝ) (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2) :
      B (1 / 2 - t) = -B t := by
    have h := hbalanced (1 / 2) t (1 / 2 - t)
      (by norm_num) ht₀ (by linarith)
      (by norm_num) hth (by linarith) (by ring)
    rw [hAh, hCh] at h
    linarith
  have haxis (t : ℝ) (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2) :
      B t = -A t - C t := by
    have h := hbalanced t (1 / 2) (1 / 2 - t)
      ht₀ (by norm_num) (by linarith)
      hth (by norm_num) (by linarith) (by ring)
    rw [hBh, hreflect t ht₀ hth] at h
    linarith
  have hadd (x y : ℝ) (hx₀ : 0 ≤ x) (hy₀ : 0 ≤ y)
      (hxh : x ≤ 1 / 2) (hyh : y ≤ 1 / 2) :
      B (x + y) = B x + B y := by
    by_cases hsum : x + y ≤ 1 / 2
    · have h := hbalanced (x + y) (1 / 2 - x) (1 / 2 - y)
        (by positivity) (by linarith) (by linarith)
        hsum (by linarith) (by linarith) (by ring)
      rw [hreflect x hx₀ hxh, hreflect y hy₀ hyh] at h
      rw [haxis (x + y) (by positivity) hsum]
      linarith
    · have hs₀ : 0 ≤ 1 - (x + y) := by linarith
      have hsh : 1 - (x + y) ≤ 1 / 2 := by linarith
      have h := hbalanced (1 - (x + y)) x y
        hs₀ hx₀ hy₀ hsh hxh hyh (by ring)
      have hcompA := hAcomp (x + y) (by positivity) (by linarith)
      have hcompB := hBcomp (x + y) (by positivity) (by linarith)
      have hcompC := hCcomp (x + y) (by positivity) (by linarith)
      have haxis' := haxis (1 - (x + y)) hs₀ hsh
      linarith
  have hperiod (t : ℝ) (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2) :
      B (1 / 2 + t) = B t := by
    have hc := hBcomp (1 / 2 + t) (by linarith) (by linarith)
    have hr := hreflect t ht₀ hth
    rw [show 1 - (1 / 2 + t) = 1 / 2 - t by ring] at hc
    linarith
  let T : ℝ → ℝ :=
    fun t ↦ if t ≤ 1 / 4 then 2 * t else 2 * t - 1 / 2
  have hT (t : ℝ) (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2) :
      0 ≤ T t ∧ T t ≤ 1 / 2 := by
    dsimp [T]
    split_ifs with ht <;> constructor <;> linarith
  have hstep (t : ℝ) (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2) :
      B (T t) = 2 * B t := by
    have hdouble := hadd t t ht₀ ht₀ hth hth
    dsimp [T]
    split_ifs with ht
    · simpa only [two_mul] using hdouble
    · have hp := hperiod (2 * t - 1 / 2) (by linarith) (by linarith)
      rw [show 1 / 2 + (2 * t - 1 / 2) = t + t by ring] at hp
      rw [← hp]
      simpa only [two_mul] using hdouble
  have hhalf (t : ℝ) (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2) : B t = 0 := by
    apply eq_zero_of_abs_two_pow_mul_le (B t) M
    intro n
    let u : ℕ → ℝ := fun k ↦ (T^[k]) t
    have hu (k : ℕ) : 0 ≤ u k ∧ u k ≤ 1 / 2 := by
      induction k with
      | zero =>
          simpa [u] using And.intro ht₀ hth
      | succ k ih =>
          simpa [u, Function.iterate_succ_apply'] using hT (u k) ih.1 ih.2
    have hvalue (k : ℕ) : B (u k) = (2 : ℝ) ^ k * B t := by
      induction k with
      | zero => simp [u]
      | succ k ih =>
          rw [show u (k + 1) = T (u k) by
            simp [u, Function.iterate_succ_apply'],
            hstep (u k) (hu k).1 (hu k).2, ih, pow_succ]
          ring
    rw [← hvalue]
    exact hbound (u n) (hu n).1 (by linarith [(hu n).2])
  intro t ht₀ ht₁
  by_cases hth : t ≤ 1 / 2
  · exact hhalf t ht₀ hth
  · have htc : 0 ≤ 1 - t := by linarith
    have htch : 1 - t ≤ 1 / 2 := by linarith
    have hz := hhalf (1 - t) htc htch
    rw [hBcomp t ht₀ ht₁] at hz
    linarith

lemma FrameFunction.quadraticDefect_eq_zero_of_iterated_amplification
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (f : FrameFunction H) {x y : H}
    (hamp : ∀ n : ℕ, ∃ u v : H,
      inner ℂ u v = 0 ∧
      ‖u‖ ^ 2 + ‖v‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2 ∧
      quadraticDefect f.homogeneousValue u v =
        (2 : ℝ) ^ n * quadraticDefect f.homogeneousValue x y) :
    quadraticDefect f.homogeneousValue x y = 0 := by
  apply eq_zero_of_abs_two_pow_mul_le _
    (2 * (‖x‖ ^ 2 + ‖y‖ ^ 2))
  intro n
  obtain ⟨u, v, _huv, hnorm, hamp⟩ := hamp n
  rw [← hamp]
  exact (f.abs_quadraticDefect_le u v).trans_eq (congrArg (2 * ·) hnorm)

lemma FrameFunction.quadraticDefect_eq_zero_of_amplification
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (f : FrameFunction H) {x y : H}
    (hxy : inner ℂ x y = 0)
    (hamp : ∀ {u v : H}, inner ℂ u v = 0 → ∃ u' v' : H,
      inner ℂ u' v' = 0 ∧
      ‖u'‖ ^ 2 + ‖v'‖ ^ 2 = ‖u‖ ^ 2 + ‖v‖ ^ 2 ∧
      quadraticDefect f.homogeneousValue u' v' =
        2 * quadraticDefect f.homogeneousValue u v) :
    quadraticDefect f.homogeneousValue x y = 0 := by
  apply f.quadraticDefect_eq_zero_of_iterated_amplification
  intro n
  induction n with
  | zero =>
      exact ⟨x, y, hxy, rfl, by norm_num⟩
  | succ n ih =>
      obtain ⟨u, v, huv, hnorm, hdefect⟩ := ih
      obtain ⟨u', v', hu'v', hnorm', hdefect'⟩ := hamp huv
      refine ⟨u', v', hu'v', hnorm'.trans hnorm, ?_⟩
      rw [hdefect', hdefect, pow_succ]
      ring

end

end LeanEval.Analysis
