import Submission.MaximumPrinciple

namespace Submission.Helpers

open Filter
open scoped ContDiff InnerProductSpace Topology

section AnnulusGeometry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

def closedAnnulus (q : E) (r : ℝ) : Set E :=
  Metric.closedBall q r \ Metric.ball q (r / 2)

def openAnnulus (q : E) (r : ℝ) : Set E :=
  Metric.ball q r ∩ {x | r / 2 < dist x q}

lemma isCompact_closedAnnulus [FiniteDimensional ℝ E] (q : E) (r : ℝ) :
    IsCompact (closedAnnulus q r) :=
  (isCompact_closedBall q r).diff (Metric.isOpen_ball)

omit [InnerProductSpace ℝ E] in
lemma isOpen_openAnnulus (q : E) (r : ℝ) :
    IsOpen (openAnnulus q r) :=
  Metric.isOpen_ball.inter
    (isOpen_lt continuous_const (by fun_prop))

omit [InnerProductSpace ℝ E] in
lemma openAnnulus_subset_closedAnnulus (q : E) (r : ℝ) :
    openAnnulus q r ⊆ closedAnnulus q r := by
  intro x hx
  refine ⟨Metric.ball_subset_closedBall hx.1, ?_⟩
  have hxlower : r / 2 < dist x q := hx.2
  simpa [Metric.mem_ball] using (not_lt_of_ge hxlower.le)

lemma closedAnnulus_slab {q e : E} {r : ℝ} (he : ‖e‖ = 1) :
    ∀ x ∈ closedAnnulus q r,
      ⟪q, e⟫_ℝ - r ≤ ⟪x, e⟫_ℝ ∧
        ⟪x, e⟫_ℝ ≤ ⟪q, e⟫_ℝ + r := by
  intro x hx
  have hnorm : ‖x - q‖ ≤ r := by
    simpa [closedAnnulus, Metric.mem_closedBall, dist_eq_norm] using hx.1
  have habs := abs_real_inner_le_norm (x - q) e
  rw [he, mul_one] at habs
  have hdecomp :
      ⟪x, e⟫_ℝ = ⟪q, e⟫_ℝ + ⟪x - q, e⟫_ℝ := by
    conv_lhs => rw [show x = q + (x - q) by abel]
    rw [inner_add_left]
  constructor
  · rw [hdecomp]
    linarith [neg_le_of_abs_le habs]
  · rw [hdecomp]
    linarith [le_of_abs_le habs]

omit [InnerProductSpace ℝ E] in
lemma closedAnnulus_mem_nhds_of_strict {q x : E} {r : ℝ}
    (hinner : r / 2 < dist x q) (houter : dist x q < r) :
    closedAnnulus q r ∈ 𝓝 x := by
  apply Filter.mem_of_superset
    ((isOpen_openAnnulus q r).mem_nhds ⟨houter, hinner⟩)
  exact openAnnulus_subset_closedAnnulus q r

end AnnulusGeometry

/-- A smooth Gaussian centered at `q`, written using the real inner
product so smoothness at the center is transparent to the calculus API. -/
noncomputable def gaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : E) (β : ℝ) (x : E) : ℝ :=
  Real.exp (-β * ⟪x - q, x - q⟫_ℝ)

lemma contDiff_gaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : E) (β : ℝ) :
    ContDiff ℝ ∞ (gaussian q β) := by
  unfold gaussian
  have hsub : ContDiff ℝ ∞ (fun x : E ↦ x - q) :=
    contDiff_id.sub contDiff_const
  have hinner :
      ContDiff ℝ ∞ (fun x : E ↦ ⟪x - q, x - q⟫_ℝ) :=
    hsub.inner ℝ hsub
  exact Real.contDiff_exp.comp (contDiff_const.mul hinner)

lemma gaussian_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : E) (β : ℝ) (x : E) :
    0 < gaussian q β x :=
  Real.exp_pos _

lemma gaussian_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q x : E} {β : ℝ} (hβ : 0 ≤ β) :
    gaussian q β x ≤ 1 := by
  rw [gaussian, Real.exp_le_one_iff]
  rw [neg_mul]
  exact neg_nonpos.mpr
    (mul_nonneg hβ (real_inner_self_nonneg (x := x - q)))

lemma iteratedFDeriv_gaussian_two_apply_self
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q x v : E) (β : ℝ) :
    iteratedFDeriv ℝ 2 (gaussian q β) x ![v, v] =
      (4 * β ^ 2 * ⟪x - q, v⟫_ℝ ^ 2 - 2 * β * ‖v‖ ^ 2) *
        gaussian q β x := by
  let A : ℝ := ⟪x - q, x - q⟫_ℝ
  let B : ℝ := ⟪x - q, v⟫_ℝ
  let C : ℝ := ⟪v, v⟫_ℝ
  let p : ℝ → ℝ := fun t ↦ -β * ((A + (2 * B) * t) + t ^ 2 * C)
  let p' : ℝ → ℝ := fun t ↦ -2 * β * (B + t * C)
  let line : ℝ → E := fun t ↦ x + t • v
  have hp (t : ℝ) : HasDerivAt p (p' t) t := by
    dsimp only [p, p']
    apply
      (((hasDerivAt_const t A).add
        ((hasDerivAt_id' t).const_mul (2 * B))).add
        (((hasDerivAt_id' t).pow 2).mul_const C)).const_mul (-β)
        |>.congr_deriv
    ring
  have hp' (t : ℝ) : HasDerivAt p' (-2 * β * C) t := by
    dsimp only [p']
    apply
      ((hasDerivAt_const t B).add
        ((hasDerivAt_id' t).mul_const C)).const_mul (-2 * β)
        |>.congr_deriv
    ring
  have hline :
      (gaussian q β ∘ line) = fun t ↦ Real.exp (p t) := by
    funext t
    apply congrArg Real.exp
    simp only [line, p, A, B, C]
    rw [show x + t • v - q = (x - q) + t • v by abel]
    simp only [inner_add_left, inner_add_right,
      real_inner_smul_left, real_inner_smul_right]
    rw [real_inner_comm v (x - q)]
    ring
  have hfirst : deriv (fun t ↦ Real.exp (p t)) =
      fun t ↦ Real.exp (p t) * p' t := by
    funext t
    exact (hp t).exp.deriv
  have hsecond (t : ℝ) :
      HasDerivAt (fun s ↦ Real.exp (p s) * p' s)
        (Real.exp (p t) * p' t * p' t +
          Real.exp (p t) * (-2 * β * C)) t := by
    exact (hp t).exp.mul (hp' t)
  rw [← iteratedDeriv_comp_affineLine_two (v := v)
    ((contDiff_gaussian q β).contDiffAt.of_le
      (WithTop.coe_le_coe.2 (OrderTop.le_top (α := ℕ∞) 2))), hline]
  have hrhs :
      (4 * β ^ 2 * ⟪x - q, v⟫_ℝ ^ 2 - 2 * β * ‖v‖ ^ 2) *
          gaussian q β x =
        Real.exp (p 0) * p' 0 * p' 0 +
          Real.exp (p 0) * (-2 * β * C) := by
    simp [p, p', A, B, C, gaussian]
    ring
  rw [hrhs]
  rw [show (2 : ℕ) = 1 + 1 by norm_num, iteratedDeriv_succ,
    iteratedDeriv_one, hfirst]
  exact (hsecond 0).deriv

/-- Explicit Laplacian of a Gaussian. -/
lemma laplacian_gaussian
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (q : E) (β : ℝ) (x : E) :
    Laplacian.laplacian (gaussian q β) x =
      (4 * β ^ 2 * ‖x - q‖ ^ 2 -
        2 * β * Module.finrank ℝ E) * gaussian q β x := by
  rw [congrFun
    (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis
      (gaussian q β)) x]
  simp_rw [iteratedFDeriv_gaussian_two_apply_self]
  calc
    ∑ i,
        (4 * β ^ 2 * ⟪x - q, (stdOrthonormalBasis ℝ E) i⟫_ℝ ^ 2 -
          2 * β * ‖(stdOrthonormalBasis ℝ E) i‖ ^ 2) *
            gaussian q β x =
        (4 * β ^ 2 * gaussian q β x) *
            ∑ i, ⟪x - q, (stdOrthonormalBasis ℝ E) i⟫_ℝ ^ 2 -
          (2 * β * gaussian q β x) *
            ∑ i, ‖(stdOrthonormalBasis ℝ E) i‖ ^ 2 := by
              simp_rw [Finset.mul_sum]
              rw [← Finset.sum_sub_distrib]
              apply Finset.sum_congr rfl
              intro i _
              ring
    _ = (4 * β ^ 2 * ‖x - q‖ ^ 2 -
          2 * β * Module.finrank ℝ E) * gaussian q β x := by
      rw [(stdOrthonormalBasis ℝ E).sum_sq_inner_left]
      simp
      ring

/-- The positive barrier used on a tangent annulus. -/
noncomputable def gaussianAnnulusBarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : E) (β r : ℝ) (x : E) : ℝ :=
  gaussian q β x - Real.exp (-β * r ^ 2)

lemma gaussianAnnulusBarrier_eq_zero_of_norm_eq
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q x : E} {β r : ℝ} (hx : ‖x - q‖ = r) :
    gaussianAnnulusBarrier q β r x = 0 := by
  rw [gaussianAnnulusBarrier, gaussian, real_inner_self_eq_norm_sq, hx]
  ring

lemma gaussianAnnulusBarrier_nonneg
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q x : E} {β r : ℝ} (hβ : 0 ≤ β)
    (hx : ‖x - q‖ ≤ r) :
    0 ≤ gaussianAnnulusBarrier q β r x := by
  rw [gaussianAnnulusBarrier, gaussian, real_inner_self_eq_norm_sq,
    sub_nonneg]
  apply Real.exp_le_exp.mpr
  have hr : ‖x - q‖ ^ 2 ≤ r ^ 2 := by
    nlinarith [norm_nonneg (x - q)]
  nlinarith [mul_le_mul_of_nonneg_left hr hβ]

lemma gaussianAnnulusBarrier_nonpos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q x : E} {β r : ℝ} (hβ : 0 ≤ β)
    (hr0 : 0 ≤ r) (hx : r ≤ ‖x - q‖) :
    gaussianAnnulusBarrier q β r x ≤ 0 := by
  rw [gaussianAnnulusBarrier, gaussian, real_inner_self_eq_norm_sq,
    sub_nonpos]
  apply Real.exp_le_exp.mpr
  have hr : r ^ 2 ≤ ‖x - q‖ ^ 2 := by
    nlinarith [norm_nonneg (x - q)]
  nlinarith [mul_le_mul_of_nonneg_left hr hβ]

lemma gaussianAnnulusBarrier_le_one
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {q x : E} {β r : ℝ} (hβ : 0 ≤ β) :
    gaussianAnnulusBarrier q β r x ≤ 1 := by
  calc
    gaussianAnnulusBarrier q β r x ≤ gaussian q β x := by
      rw [gaussianAnnulusBarrier]
      exact sub_le_self _ (Real.exp_pos _).le
    _ ≤ 1 := gaussian_le_one hβ

lemma contDiff_gaussianAnnulusBarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (q : E) (β r : ℝ) :
    ContDiff ℝ ∞ (gaussianAnnulusBarrier q β r) := by
  unfold gaussianAnnulusBarrier
  exact (contDiff_gaussian q β).sub contDiff_const

lemma laplacian_gaussianAnnulusBarrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (q : E) (β r : ℝ) (x : E) :
    Laplacian.laplacian (gaussianAnnulusBarrier q β r) x =
      (4 * β ^ 2 * ‖x - q‖ ^ 2 -
        2 * β * Module.finrank ℝ E) * gaussian q β x := by
  have hg : ContDiffAt ℝ 2 (gaussian q β) x :=
    (contDiff_gaussian q β).contDiffAt.of_le
      (WithTop.coe_le_coe.2 (OrderTop.le_top (α := ℕ∞) 2))
  have hc : ContDiffAt ℝ 2
      (fun _ : E ↦ Real.exp (-β * r ^ 2)) x := by
    fun_prop
  change Laplacian.laplacian
      (gaussian q β - fun _ : E ↦ Real.exp (-β * r ^ 2)) x = _
  rw [hg.laplacian_sub hc, laplacian_gaussian]
  simp

lemma gaussianAnnulusBarrier_operator_pos
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] {q x : E} {β r K c : ℝ}
    (hβ : 0 < β) (hr : 0 < r) (hK : 0 ≤ K)
    (hinner : r / 2 ≤ ‖x - q‖)
    (houter : ‖x - q‖ ≤ r) (hc : |c| ≤ K)
    (hlarge :
      K < β ^ 2 * r ^ 2 - 2 * β * Module.finrank ℝ E) :
    0 < Laplacian.laplacian (gaussianAnnulusBarrier q β r) x +
      c * gaussianAnnulusBarrier q β r x := by
  rw [laplacian_gaussianAnnulusBarrier]
  have hgpos : 0 < gaussian q β x := gaussian_pos q β x
  have hh_nonneg :
      0 ≤ gaussianAnnulusBarrier q β r x :=
    gaussianAnnulusBarrier_nonneg hβ.le houter
  have hh_le :
      gaussianAnnulusBarrier q β r x ≤ gaussian q β x := by
    rw [gaussianAnnulusBarrier]
    exact sub_le_self _ (Real.exp_pos _).le
  have hc_lower : -K ≤ c := by
    linarith [neg_le_of_abs_le hc]
  have hch :
      -K * gaussianAnnulusBarrier q β r x ≤
        c * gaussianAnnulusBarrier q β r x :=
    mul_le_mul_of_nonneg_right hc_lower hh_nonneg
  have hKh :
      -K * gaussian q β x ≤
        -K * gaussianAnnulusBarrier q β r x := by
    have := mul_le_mul_of_nonneg_left hh_le hK
    linarith
  have hrho :
      r ^ 2 ≤ 4 * ‖x - q‖ ^ 2 := by
    nlinarith [norm_nonneg (x - q)]
  have hcoeff :
      K <
        4 * β ^ 2 * ‖x - q‖ ^ 2 -
          2 * β * Module.finrank ℝ E := by
    have hβsq : 0 ≤ β ^ 2 := sq_nonneg β
    have hscaled :=
      mul_le_mul_of_nonneg_left hrho hβsq
    nlinarith
  have hmain :
      K * gaussian q β x <
        (4 * β ^ 2 * ‖x - q‖ ^ 2 -
          2 * β * Module.finrank ℝ E) * gaussian q β x :=
    mul_lt_mul_of_pos_right hcoeff hgpos
  linarith

/-- Comparison with the Gaussian barrier on a tangent annulus. -/
lemma gaussian_barrier_comparison_on_annulus
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Set E} {w c : E → ℝ} {q e : E}
    {r K α β ε : ℝ}
    (he : ‖e‖ = 1) (hr : 0 < r) (hK : 0 ≤ K)
    (hα : 0 < α) (hKα : K < α ^ 2)
    (hwidth : α * (2 * r) < Real.pi / 2)
    (hβ : 0 < β)
    (hlarge :
      K < β ^ 2 * r ^ 2 - 2 * β * Module.finrank ℝ E)
    (hε : 0 ≤ ε)
    (hSΩ : closedAnnulus q r ⊆ Ω)
    (hwcont : ContinuousOn w Ω)
    (hwc2 : ∀ x ∈ Ω, ContDiffAt ℝ 2 w x)
    (hwnonneg : ∀ x ∈ Ω, 0 ≤ w x)
    (hc : ∀ x ∈ Ω, |c x| ≤ K)
    (hpde : ∀ x ∈ Ω,
      Laplacian.laplacian w x + c x * w x = 0)
    (hinnerBoundary :
      ∀ x ∈ Metric.sphere q (r / 2), ε ≤ w x) :
    ∀ x ∈ closedAnnulus q r,
      0 ≤ w x - ε * gaussianAnnulusBarrier q β r x := by
  let h : E → ℝ := gaussianAnnulusBarrier q β r
  let v : E → ℝ := fun x ↦ w x - ε * h x
  have hhcont : Continuous h :=
    (contDiff_gaussianAnnulusBarrier q β r).continuous
  have hvcont : ContinuousOn v (closedAnnulus q r) := by
    exact (hwcont.mono hSΩ).sub
      (continuous_const.mul hhcont).continuousOn
  apply nonneg_of_narrow_slab
    (S := closedAnnulus q r) (w := v) (c := c)
    (e := e) (α := α)
    (a := ⟪q, e⟫_ℝ - r) (b := ⟪q, e⟫_ℝ + r)
  · exact isCompact_closedAnnulus q r
  · exact closedAnnulus_slab he
  · exact he
  · exact hα
  · convert hwidth using 1
    ring
  · exact hvcont
  · intro x hx hxneg
    have hxΩ := hSΩ hx
    exact (hwc2 x hxΩ).sub
      ((contDiff_gaussianAnnulusBarrier q β r).contDiffAt
        |>.of_le
          (WithTop.coe_le_coe.2 (OrderTop.le_top (α := ℕ∞) 2))
        |>.const_smul ε)
  · intro x hx hxneg
    have hxΩ := hSΩ hx
    have houter_le : dist x q ≤ r := by
      simpa [closedAnnulus, Metric.mem_closedBall] using hx.1
    have hinner_le : r / 2 ≤ dist x q := by
      apply le_of_not_gt
      intro hlt
      exact hx.2 (by simpa [Metric.mem_ball] using hlt)
    have houter_lt : dist x q < r := by
      apply lt_of_le_of_ne houter_le
      intro hout
      have hhzero : h x = 0 := by
        apply gaussianAnnulusBarrier_eq_zero_of_norm_eq
        simpa [dist_eq_norm] using hout
      have := hwnonneg x hxΩ
      dsimp [v] at hxneg
      rw [hhzero, mul_zero, sub_zero] at hxneg
      linarith
    have hinner_lt : r / 2 < dist x q := by
      apply lt_of_le_of_ne hinner_le
      intro hin
      have hxsphere : x ∈ Metric.sphere q (r / 2) := by
        rw [Metric.mem_sphere]
        exact hin.symm
      have hwε := hinnerBoundary x hxsphere
      have hhle : h x ≤ 1 :=
        gaussianAnnulusBarrier_le_one hβ.le
      dsimp [v] at hxneg
      nlinarith
    exact closedAnnulus_mem_nhds_of_strict hinner_lt houter_lt
  · intro x hx hxneg
    have hxΩ := hSΩ hx
    calc
      c x ≤ |c x| := le_abs_self _
      _ ≤ K := hc x hxΩ
      _ < α ^ 2 := hKα
  · intro x hx hxneg
    have hxΩ := hSΩ hx
    have houter : ‖x - q‖ ≤ r := by
      simpa [closedAnnulus, Metric.mem_closedBall, dist_eq_norm] using hx.1
    have hinner : r / 2 ≤ ‖x - q‖ := by
      have hnot : ¬ ‖x - q‖ < r / 2 := by
        intro hlt
        exact hx.2 (by
          simpa [Metric.mem_ball, dist_eq_norm] using hlt)
      exact le_of_not_gt hnot
    have hhop :
        0 < Laplacian.laplacian h x + c x * h x := by
      exact gaussianAnnulusBarrier_operator_pos hβ hr hK hinner
        houter (hc x hxΩ) hlarge
    have hwx := hwc2 x hxΩ
    have hhx : ContDiffAt ℝ 2 h x :=
      (contDiff_gaussianAnnulusBarrier q β r).contDiffAt.of_le
        (WithTop.coe_le_coe.2 (OrderTop.le_top (α := ℕ∞) 2))
    have hlapv :
        Laplacian.laplacian v x =
          Laplacian.laplacian w x -
            ε * Laplacian.laplacian h x := by
      change
        Laplacian.laplacian (w - fun y ↦ ε • h y) x =
          Laplacian.laplacian w x -
            ε * Laplacian.laplacian h x
      rw [hwx.laplacian_sub (hhx.const_smul ε)]
      change
        Laplacian.laplacian w x -
            Laplacian.laplacian (ε • h) x =
          Laplacian.laplacian w x -
            ε * Laplacian.laplacian h x
      rw [InnerProductSpace.laplacian_smul ε hhx]
      simp only [smul_eq_mul]
    rw [hlapv]
    have hwpde := hpde x hxΩ
    dsimp [v]
    nlinarith

/-- A nonnegative solution of a bounded-coefficient equation cannot have a
zero tangent to a ball on whose interior it is positive. -/
lemma no_tangent_zero_of_gaussian_barrier
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Set E} {w c : E → ℝ} {q z e : E}
    {r K α β : ℝ}
    (hΩopen : IsOpen Ω)
    (he : ‖e‖ = 1) (hr : 0 < r) (hK : 0 ≤ K)
    (hα : 0 < α) (hKα : K < α ^ 2)
    (hwidth : α * (2 * r) < Real.pi / 2)
    (hβ : 0 < β)
    (hlarge :
      K < β ^ 2 * r ^ 2 - 2 * β * Module.finrank ℝ E)
    (hball : Metric.closedBall q r ⊆ Ω)
    (hwcont : ContinuousOn w Ω)
    (hwc2 : ∀ x ∈ Ω, ContDiffAt ℝ 2 w x)
    (hwnonneg : ∀ x ∈ Ω, 0 ≤ w x)
    (hc : ∀ x ∈ Ω, |c x| ≤ K)
    (hpde : ∀ x ∈ Ω,
      Laplacian.laplacian w x + c x * w x = 0)
    (hinside : ∀ x ∈ Ω, dist x q < r → 0 < w x)
    (hzdist : dist z q = r) (hwz : w z = 0) :
    False := by
  have hhalf_lt : r / 2 < r := by linarith
  have hsphereΩ : Metric.sphere q (r / 2) ⊆ Ω := by
    intro x hx
    apply hball
    have hdist : dist x q = r / 2 := by
      simpa only [Metric.mem_sphere] using hx
    exact Metric.mem_closedBall.mpr (hdist.le.trans hhalf_lt.le)
  obtain ⟨ε, hεpos, hεlower⟩ :=
    (isCompact_sphere q (r / 2)).exists_forall_le'
      (hwcont.mono hsphereΩ)
      (fun x hx ↦ hinside x (hsphereΩ hx) (by
        have hdist : dist x q = r / 2 := by
          simpa only [Metric.mem_sphere] using hx
        linarith))
  have hSΩ : closedAnnulus q r ⊆ Ω := by
    intro x hx
    exact hball hx.1
  have hcompare :
      ∀ x ∈ closedAnnulus q r,
        0 ≤ w x - ε * gaussianAnnulusBarrier q β r x :=
    gaussian_barrier_comparison_on_annulus he hr hK hα hKα
      hwidth hβ hlarge hεpos.le hSΩ hwcont hwc2 hwnonneg hc
      hpde hεlower
  let h : E → ℝ := gaussianAnnulusBarrier q β r
  let v : E → ℝ := fun x ↦ w x - ε * h x
  have hzball : z ∈ Metric.closedBall q r := by
    exact Metric.mem_closedBall.mpr hzdist.le
  have hzΩ : z ∈ Ω := hball hzball
  have hznorm : ‖z - q‖ = r := by
    simpa [dist_eq_norm] using hzdist
  have hhz : h z = 0 := by
    exact gaussianAnnulusBarrier_eq_zero_of_norm_eq hznorm
  have hvz : v z = 0 := by
    simp [v, hwz, hhz]
  have heventual_v : ∀ᶠ y in 𝓝 z, 0 ≤ v y := by
    have hopenInner :
        IsOpen {y : E | r / 2 < dist y q} :=
      isOpen_lt continuous_const (by fun_prop)
    have hzinner : z ∈ {y : E | r / 2 < dist y q} := by
      dsimp
      rw [hzdist]
      linarith
    filter_upwards
      [hΩopen.mem_nhds hzΩ, hopenInner.mem_nhds hzinner]
      with y hyΩ hyinner
    by_cases hyout : dist y q ≤ r
    · apply hcompare y
      constructor
      · simpa [Metric.mem_closedBall] using hyout
      · simpa [Metric.mem_ball] using not_lt_of_ge hyinner.le
    · have hyr : r ≤ ‖y - q‖ := by
        have : r < dist y q := lt_of_not_ge hyout
        simpa [dist_eq_norm] using this.le
      have hhy : h y ≤ 0 :=
        gaussianAnnulusBarrier_nonpos hβ.le hr.le hyr
      have hwy := hwnonneg y hyΩ
      dsimp [v]
      nlinarith
  have hlocalv : IsLocalMin v z := by
    filter_upwards [heventual_v] with y hy
    rw [hvz]
    exact hy
  have hlocalw : IsLocalMin w z := by
    filter_upwards [hΩopen.mem_nhds hzΩ] with y hyΩ
    rw [hwz]
    exact hwnonneg y hyΩ
  let d : E := r⁻¹ • (q - z)
  let line : ℝ → E := fun t ↦ z + t • d
  have hline : ContDiffAt ℝ 2 line 0 := by
    fun_prop
  have hline_zero : line 0 = z := by simp [line]
  have hlocalwline : IsLocalMin (w ∘ line) 0 := by
    have hlocalw0 : IsLocalMin w (line 0) := by
      simpa [hline_zero] using hlocalw
    exact hlocalw0.comp_continuous hline.continuousAt
  have hlocalvline : IsLocalMin (v ∘ line) 0 := by
    have hlocalv0 : IsLocalMin v (line 0) := by
      simpa [hline_zero] using hlocalv
    exact hlocalv0.comp_continuous hline.continuousAt
  have hwline_c2 : ContDiffAt ℝ 2 (w ∘ line) 0 := by
    have hw0 : ContDiffAt ℝ 2 w (line 0) := by
      simpa [hline_zero] using hwc2 z hzΩ
    exact hw0.comp 0 hline
  have hvz_c2 : ContDiffAt ℝ 2 v z := by
    exact (hwc2 z hzΩ).sub
      ((contDiff_gaussianAnnulusBarrier q β r).contDiffAt
        |>.of_le
          (WithTop.coe_le_coe.2 (OrderTop.le_top (α := ℕ∞) 2))
        |>.const_smul ε)
  have hvline_c2 : ContDiffAt ℝ 2 (v ∘ line) 0 := by
    have hv0 : ContDiffAt ℝ 2 v (line 0) := by
      simpa [hline_zero] using hvz_c2
    exact hv0.comp 0 hline
  have hwderiv : deriv (w ∘ line) 0 = 0 :=
    hlocalwline.deriv_eq_zero
  have hvderiv : deriv (v ∘ line) 0 = 0 :=
    hlocalvline.deriv_eq_zero
  let p : ℝ → ℝ := fun t ↦ -β * (r - t) ^ 2
  have hp : HasDerivAt p (2 * β * r) 0 := by
    dsimp only [p]
    apply
      (((hasDerivAt_const 0 r).sub (hasDerivAt_id' 0)).pow 2
        |>.const_mul (-β)
        |>.congr_deriv)
    simp
    ring
  have hline_sub (t : ℝ) :
      line t - q = (1 - t * r⁻¹) • (z - q) := by
    dsimp [line, d]
    rw [show q - z = -(z - q) by abel, smul_neg]
    module
  have hhline :
      h ∘ line =
        fun t ↦ Real.exp (p t) - Real.exp (-β * r ^ 2) := by
    funext t
    dsimp [h, gaussianAnnulusBarrier, gaussian, Function.comp_apply]
    rw [hline_sub, real_inner_smul_left, real_inner_smul_right,
      real_inner_self_eq_norm_sq, hznorm]
    congr 1
    dsimp [p]
    field_simp [hr.ne']
  have hhderiv :
      HasDerivAt (h ∘ line)
        (Real.exp (-β * r ^ 2) * (2 * β * r)) 0 := by
    rw [hhline]
    apply (hp.exp.sub_const (Real.exp (-β * r ^ 2))).congr_deriv
    dsimp [p]
    ring
  have hwHas :
      HasDerivAt (w ∘ line) (deriv (w ∘ line) 0) 0 :=
    (hwline_c2.differentiableAt (by norm_num)).hasDerivAt
  have hvcalc :
      deriv (v ∘ line) 0 =
        deriv (w ∘ line) 0 -
          ε * (Real.exp (-β * r ^ 2) * (2 * β * r)) := by
    have hcalc := hwHas.sub (hhderiv.const_smul ε)
    have hvline :
        v ∘ line = (w ∘ line) - ε • (h ∘ line) := by
      funext t
      simp [v, Function.comp_def, smul_eq_mul]
    rw [hvline]
    exact hcalc.deriv
  rw [hwderiv, hvderiv] at hvcalc
  have hexp : 0 < Real.exp (-β * r ^ 2) := Real.exp_pos _
  have hterm :
      0 < ε * (Real.exp (-β * r ^ 2) * (2 * β * r)) := by
    positivity
  nlinarith

/-- Strong maximum principle for a nonnegative solution with a uniformly
bounded zeroth-order coefficient on a preconnected open set. -/
lemma strong_maximum_principle_of_bounded_coeff
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E]
    {Ω : Set E} {w c : E → ℝ} {e : E} {K α : ℝ}
    (hΩopen : IsOpen Ω) (hΩpre : IsPreconnected Ω)
    (he : ‖e‖ = 1) (hK : 0 ≤ K)
    (hα : 0 < α) (hKα : K < α ^ 2)
    (hwcont : ContinuousOn w Ω)
    (hwc2 : ∀ x ∈ Ω, ContDiffAt ℝ 2 w x)
    (hwnonneg : ∀ x ∈ Ω, 0 ≤ w x)
    (hc : ∀ x ∈ Ω, |c x| ≤ K)
    (hpde : ∀ x ∈ Ω,
      Laplacian.laplacian w x + c x * w x = 0) :
    (∀ x ∈ Ω, w x = 0) ∨ (∀ x ∈ Ω, 0 < w x) := by
  let Z : Set E := Ω ∩ {x | w x = 0}
  let P : Set E := Ω ∩ {x | 0 < w x}
  have hnonzeroOpen :
      IsOpen (Ω ∩ w ⁻¹' ({0}ᶜ : Set ℝ)) :=
    hwcont.isOpen_inter_preimage hΩopen isOpen_compl_singleton
  have hZopen : IsOpen Z := by
    rw [Metric.isOpen_iff]
    intro x hx
    have hxΩ : x ∈ Ω := hx.1
    have hwx : w x = 0 := hx.2
    obtain ⟨δ, hδ, hδΩ⟩ := Metric.isOpen_iff.mp hΩopen x hxΩ
    let R : ℝ := min (δ / 2) (Real.pi / (2 * α))
    have hπα : 0 < Real.pi / (2 * α) :=
      div_pos Real.pi_pos (mul_pos (by norm_num) hα)
    have hR : 0 < R := lt_min (by linarith) hπα
    have hRδ : R ≤ δ / 2 := min_le_left _ _
    have hRπ : R ≤ Real.pi / (2 * α) := min_le_right _ _
    refine ⟨R / 4, by positivity, ?_⟩
    intro q hq
    have hqx : dist q x < R / 4 := by
      simpa [Metric.mem_ball] using hq
    have hqδ : dist q x < δ := by
      have : R / 4 < δ := by linarith
      exact hqx.trans this
    have hqΩ : q ∈ Ω := hδΩ (by
      simpa [Metric.mem_ball] using hqδ)
    refine ⟨hqΩ, ?_⟩
    by_contra hwq
    have hwqne : w q ≠ 0 := by
      simpa using hwq
    have hwqpos : 0 < w q :=
      lt_of_le_of_ne (hwnonneg q hqΩ) hwqne.symm
    let C : Set E := Metric.closedBall x (R / 2)
    let N : Set E := Ω ∩ w ⁻¹' ({0}ᶜ : Set ℝ)
    let Zloc : Set E := C \ N
    have hCΩ : C ⊆ Ω := by
      intro y hy
      have hyd : dist y x ≤ R / 2 := by
        simpa [C, Metric.mem_closedBall] using hy
      apply hδΩ
      have : dist y x < δ := by linarith
      simpa [Metric.mem_ball] using this
    have hNopen : IsOpen N := by
      simpa [N] using hnonzeroOpen
    have hZlocCompact : IsCompact Zloc := by
      exact (isCompact_closedBall x (R / 2)).diff hNopen
    have hxC : x ∈ C := by
      dsimp [C]
      rw [Metric.mem_closedBall, dist_self]
      linarith
    have hxZloc : x ∈ Zloc := by
      refine ⟨hxC, ?_⟩
      intro hxN
      exact hxN.2 (by simp [hwx])
    obtain ⟨z, hzZloc, hzmin⟩ :=
      hZlocCompact.exists_isMinOn ⟨x, hxZloc⟩
        (by fun_prop : ContinuousOn (fun y : E ↦ dist y q) Zloc)
    have hzC : z ∈ C := hzZloc.1
    have hzΩ : z ∈ Ω := hCΩ hzC
    have hwz : w z = 0 := by
      by_contra hwz
      exact hzZloc.2 ⟨hzΩ, by simpa using hwz⟩
    let r : ℝ := dist z q
    have hrle : r ≤ dist x q := by
      exact hzmin hxZloc
    have hrR : r < R / 4 := hrle.trans_lt (by
      simpa [dist_comm] using hqx)
    have hzq : z ≠ q := by
      intro hzq
      subst z
      linarith
    have hr : 0 < r := by
      exact dist_pos.mpr hzq
    have hball : Metric.closedBall q r ⊆ Ω := by
      intro y hy
      have hyq : dist y q ≤ r := by
        simpa [Metric.mem_closedBall] using hy
      have hyx : dist y x < R / 2 := by
        calc
          dist y x ≤ dist y q + dist q x := dist_triangle _ _ _
          _ < R / 2 := by
            have hqx' : dist q x < R / 4 := hqx
            linarith
      exact hCΩ (by
        simpa [C, Metric.mem_closedBall] using hyx.le)
    have hinside :
        ∀ y ∈ Ω, dist y q < r → 0 < w y := by
      intro y hyΩ hyqr
      have hyx : dist y x < R / 2 := by
        calc
          dist y x ≤ dist y q + dist q x := dist_triangle _ _ _
          _ < R / 2 := by
            have hqx' : dist q x < R / 4 := hqx
            linarith
      have hyC : y ∈ C := by
        simpa [C, Metric.mem_closedBall] using hyx.le
      have hwy : w y ≠ 0 := by
        intro hwy
        have hyZloc : y ∈ Zloc := by
          refine ⟨hyC, ?_⟩
          intro hyN
          exact hyN.2 (by simp [hwy])
        have hzy : dist z q ≤ dist y q := hzmin hyZloc
        dsimp [r] at hyqr
        linarith
      exact lt_of_le_of_ne (hwnonneg y hyΩ) hwy.symm
    have hwidth : α * (2 * r) < Real.pi / 2 := by
      have hsmall : α * (2 * r) < α * (R / 2) := by
        nlinarith
      have hbound : α * (R / 2) ≤ Real.pi / 4 := by
        have hscaled :=
          mul_le_mul_of_nonneg_left hRπ hα.le
        field_simp [hα.ne'] at hscaled ⊢
        nlinarith
      nlinarith [Real.pi_pos]
    let A : ℝ := K + 2 * Module.finrank ℝ E + 1
    let β : ℝ := A / r ^ 2 + 1
    have hnrank : 0 ≤ (Module.finrank ℝ E : ℝ) := Nat.cast_nonneg _
    have hA : 0 < A := by
      dsimp [A]
      nlinarith
    have hβgt : 1 < β := by
      dsimp [β]
      have : 0 < A / r ^ 2 :=
        div_pos hA (sq_pos_of_pos hr)
      linarith
    have hβ : 0 < β := lt_trans (by norm_num) hβgt
    have hβr :
        β * r ^ 2 =
          K + 2 * Module.finrank ℝ E + 1 + r ^ 2 := by
      dsimp [β, A]
      field_simp [hr.ne']
    have hlarge :
        K < β ^ 2 * r ^ 2 - 2 * β * Module.finrank ℝ E := by
      calc
        K < β * (K + 1 + r ^ 2) := by
          nlinarith [sq_pos_of_pos hr]
        _ = β ^ 2 * r ^ 2 - 2 * β * Module.finrank ℝ E := by
          rw [show β ^ 2 * r ^ 2 = β * (β * r ^ 2) by ring,
            hβr]
          ring
    exact no_tangent_zero_of_gaussian_barrier hΩopen he hr hK hα
      hKα hwidth hβ hlarge hball hwcont hwc2 hwnonneg hc hpde
      hinside rfl hwz
  have hPopen : IsOpen P := by
    exact hwcont.isOpen_inter_preimage hΩopen isOpen_Ioi
  rcases Z.eq_empty_or_nonempty with hZempty | hZne
  · right
    intro x hxΩ
    have hwne : w x ≠ 0 := by
      intro hw
      have hxZ : x ∈ Z := ⟨hxΩ, hw⟩
      rw [hZempty] at hxZ
      exact hxZ
    exact lt_of_le_of_ne (hwnonneg x hxΩ) hwne.symm
  · left
    have hdisjoint : Disjoint Z P := by
      rw [Set.disjoint_left]
      intro x hxZ hxP
      have hxzero : w x = 0 := hxZ.2
      have hxpos : 0 < w x := hxP.2
      rw [hxzero] at hxpos
      exact (lt_irrefl 0 hxpos)
    have hcover : Ω ⊆ Z ∪ P := by
      intro x hxΩ
      rcases (hwnonneg x hxΩ).eq_or_lt with hxzero | hxpos
      · exact Or.inl ⟨hxΩ, hxzero.symm⟩
      · exact Or.inr ⟨hxΩ, hxpos⟩
    have hmeet : (Ω ∩ Z).Nonempty := by
      obtain ⟨x, hxZ⟩ := hZne
      exact ⟨x, hxZ.1, hxZ⟩
    have hΩZ : Ω ⊆ Z :=
      hΩpre.subset_left_of_subset_union hZopen hPopen hdisjoint
        hcover hmeet
    intro x hxΩ
    exact (hΩZ hxΩ).2

end Submission.Helpers
