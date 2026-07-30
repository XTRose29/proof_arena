import Submission.KernelExpansion

open Function Set
open scoped ContDiff Polynomial Topology

noncomputable section

namespace Submission.Helpers

/-- The Cauchy transform of the part of the Cauchy--Riemann defect whose
topological support misses `K`, bundled as a continuous function on `K`. -/
def farDefectMap {K : Set ℂ} [CompactSpace K]
    (g ψ : ℂ → ℂ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K) :
    C(K, ℂ) :=
  ∫ w : ℂ,
    cauchyDensityMap K
      (fun z ↦ (1 - ψ z) * crDefect g z) hdisj w

/-- The continuous frontier term left after subtracting the far Cauchy
transform from the Cauchy--Pompeiu representation of `g`.  The next
localization stage approximates this map by finite moment rational
expressions. -/
def frontierDefectMap {K : Set ℂ} [CompactSpace K]
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K) :
    C(K, ℂ) :=
  (-(2 * Real.pi * Complex.I : ℂ)) •
      restrictTo g hg.continuous.continuousOn -
    farDefectMap g ψ hdisj

/-- The far map belongs to the closed polynomial algebra. -/
theorem farDefectMap_mem_polynomialClosure
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ ∞ ψ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K) :
    farDefectMap g ψ hdisj ∈
      (polynomialFunctions K).topologicalClosure := by
  simpa only [farDefectMap] using
    cauchyFarDefectIntegral_mem_polynomialClosure
      hKc g ψ hg hgc hψ hdisj

/-- Pointwise, the bundled frontier map is exactly the Cauchy transform of
the localized near defect. -/
theorem frontierDefectMap_apply
    {K : Set ℂ} [CompactSpace K]
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ ∞ ψ)
    (hψc : HasCompactSupport ψ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (z : K) :
    frontierDefectMap g ψ hg hdisj z =
      ∫ w : ℂ,
        (w - (z : ℂ))⁻¹ * (ψ w * crDefect g w) := by
  let qnear : ℂ → ℂ := fun w ↦ ψ w * crDefect g w
  let qfar : ℂ → ℂ := fun w ↦ (1 - ψ w) * crDefect g w
  have hqnearContinuous : Continuous qnear :=
    hψ.continuous.mul (continuous_crDefect g hg)
  have hqnearCompact : HasCompactSupport qnear :=
    hψc.mul_right
  have hqfarContinuous : Continuous qfar :=
    (continuous_const.sub hψ.continuous).mul
      (continuous_crDefect g hg)
  have hqfarCompact : HasCompactSupport qfar :=
    (crDefect_hasCompactSupport g hgc).mul_left
  have hqfarDisjoint : Disjoint (tsupport qfar) K := by
    simpa only [qfar] using hdisj
  have hnearIntegrable :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ (w - (z : ℂ))⁻¹ * qnear w) :=
    integrable_cauchyKernel_mul_continuous_compact
      qnear hqnearContinuous hqnearCompact z
  have hfarIntegrable :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ (w - (z : ℂ))⁻¹ * qfar w) :=
    integrable_cauchyKernel_mul_continuous_compact
      qfar hqfarContinuous hqfarCompact z
  have hfarMapIntegrable :
      MeasureTheory.Integrable
        (cauchyDensityMap K qfar hqfarDisjoint) :=
    integrable_cauchyDensityMap
      qfar hqfarContinuous hqfarCompact hqfarDisjoint
  have hfarApply :
      farDefectMap g ψ hdisj z =
        ∫ w : ℂ, (w - (z : ℂ))⁻¹ * qfar w := by
    rw [farDefectMap,
      ContinuousMap.integral_apply hfarMapIntegrable]
    simp only [cauchyDensityMap_apply]
  have hsplit :
      (∫ w : ℂ, (w - (z : ℂ))⁻¹ * crDefect g w) =
        (∫ w : ℂ, (w - (z : ℂ))⁻¹ * qnear w) +
          ∫ w : ℂ, (w - (z : ℂ))⁻¹ * qfar w := by
    calc
      (∫ w : ℂ, (w - (z : ℂ))⁻¹ * crDefect g w) =
          ∫ w : ℂ,
            (w - (z : ℂ))⁻¹ * qnear w +
              (w - (z : ℂ))⁻¹ * qfar w := by
                apply MeasureTheory.integral_congr_ae
                filter_upwards with w
                dsimp only [qnear, qfar]
                ring
      _ = _ :=
        MeasureTheory.integral_add
          hnearIntegrable hfarIntegrable
  have hformula :=
    cauchyPompeiu_compactSupport g hg hgc (z : ℂ)
  have hcauchy :
      (-(2 * Real.pi * Complex.I : ℂ)) * g z =
        ∫ w : ℂ, (w - (z : ℂ))⁻¹ * crDefect g w := by
    linear_combination -hformula
  change
    (-(2 * Real.pi * Complex.I : ℂ)) * g z -
        farDefectMap g ψ hdisj z =
      ∫ w : ℂ, (w - (z : ℂ))⁻¹ * qnear w
  rw [hfarApply, hcauchy, hsplit]
  ring

/-- Quantitative endpoint of the frontier reduction.  If the remaining
frontier map is within `‖2πi‖ * (ε / 2)` of an element of the closed
polynomial algebra, then `g` is within `ε` of an actual polynomial on `K`.
The second half of the error budget converts the closed-algebra element to
one polynomial. -/
theorem exists_polynomial_approx_of_frontierDefectMap_approx
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ ∞ ψ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (ε : ℝ) (hε : 0 < ε)
    (r : (polynomialFunctions K).topologicalClosure)
    (hr :
      ‖frontierDefectMap g ψ hg hdisj -
          (r : C(K, ℂ))‖ <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  let c : ℂ := 2 * Real.pi * Complex.I
  have hc : c ≠ 0 := by
    dsimp [c]
    norm_num [Real.pi_ne_zero, Complex.I_ne_zero]
  have hcNorm : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let far :
      (polynomialFunctions K).topologicalClosure :=
    ⟨farDefectMap g ψ hdisj,
      farDefectMap_mem_polynomialClosure
        hKc g ψ hg hgc hψ hdisj⟩
  let a :
      (polynomialFunctions K).topologicalClosure :=
    (-c)⁻¹ • (r + far)
  have hga :
      restrictTo g hg.continuous.continuousOn -
          (a : C(K, ℂ)) =
        (-c)⁻¹ •
          (frontierDefectMap g ψ hg hdisj -
            (r : C(K, ℂ))) := by
    ext z
    change
      g z -
          (-c)⁻¹ *
            ((r : C(K, ℂ)) z + farDefectMap g ψ hdisj z) =
        (-c)⁻¹ *
          (((-c) * g z - farDefectMap g ψ hdisj z) -
            (r : C(K, ℂ)) z)
    field_simp [hc]
    ring
  have hgaNorm :
      ‖restrictTo g hg.continuous.continuousOn -
          (a : C(K, ℂ))‖ < ε / 2 := by
    rw [hga, norm_smul]
    simp only [norm_inv, norm_neg]
    calc
      ‖c‖⁻¹ *
          ‖frontierDefectMap g ψ hg hdisj -
            (r : C(K, ℂ))‖
          < ‖c‖⁻¹ * (‖c‖ * (ε / 2)) := by
              exact mul_lt_mul_of_pos_left
                (by simpa only [c] using hr) (inv_pos.mpr hcNorm)
      _ = ε / 2 := by
        field_simp [ne_of_gt hcNorm]
  have haClosure :
      (a : C(K, ℂ)) ∈
        closure (polynomialFunctions K : Set C(K, ℂ)) := by
    rw [← Subalgebra.topologicalClosure_coe]
    exact a.property
  rw [Metric.mem_closure_iff] at haClosure
  obtain ⟨pK, hpK, hap⟩ :=
    haClosure (ε / 2) (half_pos hε)
  rw [polynomialFunctions_coe] at hpK
  obtain ⟨p, rfl⟩ := hpK
  refine ⟨p, fun z hz ↦ ?_⟩
  let zK : K := ⟨z, hz⟩
  have hgaPoint :
      ‖g z - (a : C(K, ℂ)) zK‖ < ε / 2 := by
    exact lt_of_le_of_lt
      (by simpa using
        (restrictTo g hg.continuous.continuousOn -
          (a : C(K, ℂ))).norm_coe_le_norm zK)
      hgaNorm
  have hapPoint :
      ‖(a : C(K, ℂ)) zK - p.eval z‖ < ε / 2 := by
    exact lt_of_le_of_lt
      (by simpa using
        ((a : C(K, ℂ)) -
          p.toContinuousMapOn K).norm_coe_le_norm zK)
      (by
        simpa only [dist_eq_norm,
          Polynomial.toContinuousMapOnAlgHom_apply] using hap)
  calc
    ‖g z - p.eval z‖ =
        ‖(g z - (a : C(K, ℂ)) zK) +
          ((a : C(K, ℂ)) zK - p.eval z)‖ := by
            congr 1
            ring
    _ ≤ ‖g z - (a : C(K, ℂ)) zK‖ +
          ‖(a : C(K, ℂ)) zK - p.eval z‖ :=
      norm_add_le _ _
    _ < ε / 2 + ε / 2 :=
      add_lt_add hgaPoint hapPoint
    _ = ε := by ring

/-- Finite-piece fusion with a continuous residual.  Cutoff localization
naturally writes the frontier map as a finite sum of Cauchy transforms plus
a uniformly small continuous term; this theorem spends the error budget on
that residual and the first-moment errors together. -/
theorem exists_polynomial_approx_of_frontierMomentPieces_of_residual
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι]
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ ∞ ψ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (E : ι → Set ℂ) (q : ι → ℂ → ℂ) (a : ι → ℂ)
    (ha : ∀ i, a i ∉ K)
    (T : C(K, ℂ))
    (hT :
      ∀ z : K,
        T z =
          ∑ i, ∫ w : ℂ in E i,
            (w - (z : ℂ))⁻¹ * q i w)
    (e₀ : ℝ)
    (hres :
      ‖frontierDefectMap g ψ hg hdisj - T‖ ≤ e₀)
    (e : ι → ℝ) (he : ∀ i, 0 ≤ e i)
    (hpiece :
      ∀ i (z : K),
        ‖(∫ w : ℂ in E i,
              (w - (z : ℂ))⁻¹ * q i w) -
            ((a i - (z : ℂ))⁻¹ *
                (∫ w : ℂ in E i, q i w) -
              (a i - (z : ℂ))⁻¹ ^ 2 *
                (∫ w : ℂ in E i,
                  (w - a i) * q i w))‖ ≤
          e i)
    (ε : ℝ) (hε : 0 < ε)
    (herror :
      e₀ + ∑ i, e i <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  let m₀ : ι → ℂ := fun i ↦ ∫ w : ℂ in E i, q i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ in E i, (w - a i) * q i w
  obtain ⟨r, hr⟩ :=
    exists_firstMomentRational_mem_polynomialClosure
      hKc a m₀ m₁ ha
  apply exists_polynomial_approx_of_frontierDefectMap_approx
    hKc g ψ hg hgc hψ hdisj ε hε r
  have hsum_nonneg : 0 ≤ ∑ i, e i :=
    Finset.sum_nonneg fun i _hi ↦ he i
  have hTr : ‖T - (r : C(K, ℂ))‖ ≤ ∑ i, e i := by
    rw [(T - (r : C(K, ℂ))).norm_le hsum_nonneg]
    intro z
    change ‖T z - (r : C(K, ℂ)) z‖ ≤ ∑ i, e i
    rw [hT z, hr z]
    dsimp only [m₀, m₁]
    rw [← Finset.sum_sub_distrib]
    calc
      ‖∑ i,
          ((∫ w : ℂ in E i,
              (w - (z : ℂ))⁻¹ * q i w) -
            ((a i - (z : ℂ))⁻¹ *
                (∫ w : ℂ in E i, q i w) -
              (a i - (z : ℂ))⁻¹ ^ 2 *
                (∫ w : ℂ in E i,
                  (w - a i) * q i w)))‖
          ≤ ∑ i,
              ‖(∫ w : ℂ in E i,
                  (w - (z : ℂ))⁻¹ * q i w) -
                ((a i - (z : ℂ))⁻¹ *
                    (∫ w : ℂ in E i, q i w) -
                  (a i - (z : ℂ))⁻¹ ^ 2 *
                    (∫ w : ℂ in E i,
                      (w - a i) * q i w))‖ :=
        norm_sum_le _ _
      _ ≤ ∑ i, e i := by
        exact Finset.sum_le_sum fun i _hi ↦ hpiece i z
  calc
    ‖frontierDefectMap g ψ hg hdisj - (r : C(K, ℂ))‖ =
        ‖(frontierDefectMap g ψ hg hdisj - T) +
          (T - (r : C(K, ℂ)))‖ := by
            congr 1
            ring
    _ ≤ ‖frontierDefectMap g ψ hg hdisj - T‖ +
          ‖T - (r : C(K, ℂ))‖ :=
      norm_add_le _ _
    _ ≤ e₀ + ∑ i, e i :=
      add_le_add hres hTr
    _ < ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2) :=
      herror

/-- Aggregate finite-piece fusion with a continuous residual.  Unlike the
piecewise version, this interface retains cancellation between localized
errors and permits overlap estimates to use the partition identity directly. -/
theorem exists_polynomial_approx_of_frontierMomentPieces_of_aggregate
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι]
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ ∞ ψ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (E : ι → Set ℂ) (q : ι → ℂ → ℂ) (a : ι → ℂ)
    (ha : ∀ i, a i ∉ K)
    (T : C(K, ℂ))
    (hT :
      ∀ z : K,
        T z =
          ∑ i, ∫ w : ℂ in E i,
            (w - (z : ℂ))⁻¹ * q i w)
    (e₀ : ℝ)
    (hres :
      ‖frontierDefectMap g ψ hg hdisj - T‖ ≤ e₀)
    (e₁ : ℝ) (he₁ : 0 ≤ e₁)
    (haggregate :
      ∀ z : K,
        ‖∑ i,
            ((∫ w : ℂ in E i,
                (w - (z : ℂ))⁻¹ * q i w) -
              ((a i - (z : ℂ))⁻¹ *
                  (∫ w : ℂ in E i, q i w) -
                (a i - (z : ℂ))⁻¹ ^ 2 *
                  (∫ w : ℂ in E i,
                    (w - a i) * q i w)))‖ ≤
          e₁)
    (ε : ℝ) (hε : 0 < ε)
    (herror :
      e₀ + e₁ <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  let m₀ : ι → ℂ := fun i ↦ ∫ w : ℂ in E i, q i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ in E i, (w - a i) * q i w
  obtain ⟨r, hr⟩ :=
    exists_firstMomentRational_mem_polynomialClosure
      hKc a m₀ m₁ ha
  apply exists_polynomial_approx_of_frontierDefectMap_approx
    hKc g ψ hg hgc hψ hdisj ε hε r
  have hTr : ‖T - (r : C(K, ℂ))‖ ≤ e₁ := by
    rw [(T - (r : C(K, ℂ))).norm_le he₁]
    intro z
    change ‖T z - (r : C(K, ℂ)) z‖ ≤ e₁
    rw [hT z, hr z]
    dsimp only [m₀, m₁]
    rw [← Finset.sum_sub_distrib]
    exact haggregate z
  calc
    ‖frontierDefectMap g ψ hg hdisj - (r : C(K, ℂ))‖ =
        ‖(frontierDefectMap g ψ hg hdisj - T) +
          (T - (r : C(K, ℂ)))‖ := by
            congr 1
            ring
    _ ≤ ‖frontierDefectMap g ψ hg hdisj - T‖ +
          ‖T - (r : C(K, ℂ))‖ :=
      norm_add_le _ _
    _ ≤ e₀ + e₁ :=
      add_le_add hres hTr
    _ < ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2) :=
      herror

/-- Abstract finite-piece fusion.  It is enough to decompose the frontier
transform into finitely many localized transforms and bound, uniformly on
`K`, the error made by replacing each transform with its first-moment
rational model.  The pieces meeting `K` can therefore use a local estimate,
while separated evaluations can use the Laurent remainder estimate. -/
theorem exists_polynomial_approx_of_frontierMomentPieces_of_error
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι]
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ ∞ ψ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (E : ι → Set ℂ) (q : ι → ℂ → ℂ) (a : ι → ℂ)
    (ha : ∀ i, a i ∉ K)
    (hsource :
      ∀ z : K,
        frontierDefectMap g ψ hg hdisj z =
          ∑ i, ∫ w : ℂ in E i,
            (w - (z : ℂ))⁻¹ * q i w)
    (e : ι → ℝ)
    (hpiece :
      ∀ i (z : K),
        ‖(∫ w : ℂ in E i,
              (w - (z : ℂ))⁻¹ * q i w) -
            ((a i - (z : ℂ))⁻¹ *
                (∫ w : ℂ in E i, q i w) -
              (a i - (z : ℂ))⁻¹ ^ 2 *
                (∫ w : ℂ in E i,
                  (w - a i) * q i w))‖ ≤
          e i)
    (ε : ℝ) (hε : 0 < ε)
    (herror :
      ∑ i, e i <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  let m₀ : ι → ℂ := fun i ↦ ∫ w : ℂ in E i, q i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ in E i, (w - a i) * q i w
  obtain ⟨r, hr⟩ :=
    exists_firstMomentRational_mem_polynomialClosure
      hKc a m₀ m₁ ha
  apply exists_polynomial_approx_of_frontierDefectMap_approx
    hKc g ψ hg hgc hψ hdisj ε hε r
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [(frontierDefectMap g ψ hg hdisj -
      (r : C(K, ℂ))).norm_lt_iff
    (mul_pos (norm_pos_iff.mpr hc) (half_pos hε))]
  intro z
  change
    ‖frontierDefectMap g ψ hg hdisj z -
        (r : C(K, ℂ)) z‖ <
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)
  rw [hsource z, hr z]
  dsimp only [m₀, m₁]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i,
        ((∫ w : ℂ in E i,
            (w - (z : ℂ))⁻¹ * q i w) -
          ((a i - (z : ℂ))⁻¹ *
              (∫ w : ℂ in E i, q i w) -
            (a i - (z : ℂ))⁻¹ ^ 2 *
              (∫ w : ℂ in E i,
                (w - a i) * q i w)))‖
        ≤ ∑ i,
            ‖(∫ w : ℂ in E i,
                (w - (z : ℂ))⁻¹ * q i w) -
              ((a i - (z : ℂ))⁻¹ *
                  (∫ w : ℂ in E i, q i w) -
                (a i - (z : ℂ))⁻¹ ^ 2 *
                  (∫ w : ℂ in E i,
                    (w - a i) * q i w))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i, e i := by
      exact Finset.sum_le_sum fun i _hi ↦ hpiece i z
    _ < ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2) :=
      herror

/-- Fuse a finite family of localized Cauchy transforms into the frontier
approximation needed by `exists_polynomial_approx_of_frontierDefectMap_approx`.
Each piece is replaced by its zeroth/first-moment rational expression, and
the `L¹` second-order bounds are summed uniformly on `K`. -/
theorem exists_polynomial_approx_of_frontierMomentPieces
    {K : Set ℂ} [CompactSpace K] (hKc : IsConnected (Kᶜ))
    {ι : Type*} [Fintype ι]
    (g ψ : ℂ → ℂ) (hg : ContDiff ℝ ∞ g)
    (hgc : HasCompactSupport g) (hψ : ContDiff ℝ ∞ ψ)
    (hdisj :
      Disjoint
        (tsupport (fun z ↦ (1 - ψ z) * crDefect g z)) K)
    (E : ι → Set ℂ) (hE : ∀ i, MeasurableSet (E i))
    (q : ι → ℂ → ℂ) (a : ι → ℂ) (ρ d : ι → ℝ)
    (ha : ∀ i, a i ∉ K)
    (hsource :
      ∀ z : K,
        frontierDefectMap g ψ hg hdisj z =
          ∑ i, ∫ w : ℂ in E i,
            (w - (z : ℂ))⁻¹ * q i w)
    (hq : ∀ i, MeasureTheory.IntegrableOn (q i) (E i))
    (hq₁ :
      ∀ i,
        MeasureTheory.IntegrableOn
          (fun w ↦ (w - a i) * q i w) (E i))
    (hrem :
      ∀ i (z : K),
        MeasureTheory.IntegrableOn
          (fun w ↦
            ((w - a i) ^ 2 *
              ((a i - (z : ℂ))⁻¹ ^ 2 *
                (w - (z : ℂ))⁻¹)) * q i w) (E i))
    (hqnorm :
      ∀ i,
        MeasureTheory.IntegrableOn
          (fun w ↦ ‖q i w‖) (E i))
    (hwa : ∀ i w, w ∈ E i → ‖w - a i‖ ≤ ρ i)
    (haz : ∀ i (z : K), d i ≤ ‖a i - (z : ℂ)‖)
    (hwz :
      ∀ i w, w ∈ E i →
        ∀ z : K, d i ≤ ‖w - (z : ℂ)‖)
    (hd : ∀ i, 0 < d i)
    (ε : ℝ) (hε : 0 < ε)
    (herror :
      ∑ i,
          (ρ i ^ 2 * (d i)⁻¹ ^ 3) *
            ∫ w : ℂ in E i, ‖q i w‖ <
        ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)) :
    ∃ p : ℂ[X], ∀ z ∈ K, ‖g z - p.eval z‖ < ε := by
  classical
  let m₀ : ι → ℂ := fun i ↦ ∫ w : ℂ in E i, q i w
  let m₁ : ι → ℂ :=
    fun i ↦ ∫ w : ℂ in E i, (w - a i) * q i w
  obtain ⟨r, hr⟩ :=
    exists_firstMomentRational_mem_polynomialClosure
      hKc a m₀ m₁ ha
  apply exists_polynomial_approx_of_frontierDefectMap_approx
    hKc g ψ hg hgc hψ hdisj ε hε r
  have hc : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
    norm_num [Real.pi_ne_zero, Complex.I_ne_zero]
  rw [(frontierDefectMap g ψ hg hdisj -
      (r : C(K, ℂ))).norm_lt_iff
    (mul_pos (norm_pos_iff.mpr hc) (half_pos hε))]
  intro z
  change
    ‖frontierDefectMap g ψ hg hdisj z -
        (r : C(K, ℂ)) z‖ <
      ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2)
  rw [hsource z, hr z]
  dsimp only [m₀, m₁]
  rw [← Finset.sum_sub_distrib]
  calc
    ‖∑ i,
        ((∫ w : ℂ in E i,
            (w - (z : ℂ))⁻¹ * q i w) -
          ((a i - (z : ℂ))⁻¹ *
              (∫ w : ℂ in E i, q i w) -
            (a i - (z : ℂ))⁻¹ ^ 2 *
              (∫ w : ℂ in E i,
                (w - a i) * q i w)))‖
        ≤ ∑ i,
            ‖(∫ w : ℂ in E i,
                (w - (z : ℂ))⁻¹ * q i w) -
              ((a i - (z : ℂ))⁻¹ *
                  (∫ w : ℂ in E i, q i w) -
                (a i - (z : ℂ))⁻¹ ^ 2 *
                  (∫ w : ℂ in E i,
                    (w - a i) * q i w))‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i,
          (ρ i ^ 2 * (d i)⁻¹ ^ 3) *
            ∫ w : ℂ in E i, ‖q i w‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      apply norm_setIntegral_cauchyKernel_sub_moments_le
        (E i) (hE i) (q i)
      · intro hai
        apply ha i
        rw [hai]
        exact z.property
      · exact hq i
      · exact hq₁ i
      · exact hrem i z
      · exact hqnorm i
      · exact fun w hw ↦ hwa i w hw
      · exact haz i z
      · exact fun w hw ↦ hwz i w hw z
      · exact hd i
    _ < ‖(2 * Real.pi * Complex.I : ℂ)‖ * (ε / 2) :=
      herror

end Submission.Helpers
