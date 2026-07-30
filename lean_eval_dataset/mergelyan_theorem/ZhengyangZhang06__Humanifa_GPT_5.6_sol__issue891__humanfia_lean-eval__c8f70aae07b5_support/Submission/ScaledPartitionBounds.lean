import Mathlib.MeasureTheory.Covering.BesicovitchVectorSpace
import Submission.ScaledPartition

open Function Set
open scoped ContDiff Pointwise Topology

noncomputable section

namespace Submission.Helpers

/-- Complexification of one explicit uniform real bump. -/
def complexUniformBump
    (c : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) : ℂ :=
  uniformContDiffBump c r hr z

/-- The unit-scale reference member of the uniform bump family. -/
def referenceComplexBump (z : ℂ) : ℂ :=
  complexUniformBump 0 1 zero_lt_one z

/-- A complexified uniform bump is real-smooth. -/
theorem contDiff_complexUniformBump
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    ContDiff ℝ ∞ (complexUniformBump c r hr) := by
  change
    ContDiff ℝ ∞
      (Complex.ofRealCLM ∘ uniformContDiffBump c r hr)
  exact
    Complex.ofRealCLM.contDiff.comp
      (uniformContDiffBump c r hr).contDiff

/-- A complexified uniform bump has compact support. -/
theorem hasCompactSupport_complexUniformBump
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    HasCompactSupport (complexUniformBump c r hr) :=
  (uniformContDiffBump c r hr).hasCompactSupport.comp_left
    Complex.ofReal_zero

/-- The complexified raw bump is supported in its radius-`2r` closed
ball. -/
theorem tsupport_complexUniformBump_subset_closedBall
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    tsupport (complexUniformBump c r hr) ⊆
      Metric.closedBall c (2 * r) := by
  change
    tsupport
        (Complex.ofReal ∘
          (uniformContDiffBump c r hr : ℂ → ℝ)) ⊆
      Metric.closedBall c (2 * r)
  refine
    (tsupport_comp_subset Complex.ofReal_zero
      (uniformContDiffBump c r hr : ℂ → ℝ)).trans ?_
  simpa only [ContDiffBump.tsupport_eq, uniformContDiffBump] using
    (Subset.rfl :
      Metric.closedBall c (2 * r) ⊆
        Metric.closedBall c (2 * r))

/-- Every scaled bump is the reference bump precomposed with its affine
normalization map. -/
theorem complexUniformBump_eq_reference
    (c : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    complexUniformBump c r hr z =
      referenceComplexBump (r⁻¹ • (z - c)) := by
  simp [complexUniformBump, referenceComplexBump,
    uniformContDiffBump, ContDiffBump.apply,
    div_eq_mul_inv]
  congr 1 <;> field_simp [hr.ne']

/-- Lipschitz bounds rescale by exactly `r⁻¹` throughout the uniform bump
family. -/
theorem lipschitzWith_complexUniformBump
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ℂ) (r : ℝ) (hr : 0 < r) :
    LipschitzWith
      (C * (r⁻¹).toNNReal)
      (complexUniformBump c r hr) := by
  rw [lipschitzWith_iff_norm_sub_le]
  intro z w
  rw [complexUniformBump_eq_reference c r hr z,
    complexUniformBump_eq_reference c r hr w]
  calc
    ‖referenceComplexBump (r⁻¹ • (z - c)) -
        referenceComplexBump (r⁻¹ • (w - c))‖
        ≤ (C : ℝ) *
            ‖r⁻¹ • (z - c) - r⁻¹ • (w - c)‖ :=
      hC.norm_sub_le _ _
    _ = ((C * (r⁻¹).toNNReal : NNReal) : ℝ) *
          ‖z - w‖ := by
      rw [← smul_sub]
      have hsub :
          (z - c) - (w - c) = z - w := by ring
      rw [hsub, norm_smul, Real.norm_eq_abs,
        abs_of_pos (inv_pos.mpr hr)]
      rw [NNReal.coe_mul,
        Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)]
      ring

/-- Every complexified raw bump takes values in the complex unit disk. -/
theorem norm_complexUniformBump_le_one
    (c : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    ‖complexUniformBump c r hr z‖ ≤ 1 := by
  simpa [complexUniformBump, Complex.norm_real,
    abs_of_nonneg ((uniformContDiffBump c r hr).nonneg (x := z))] using
      (uniformContDiffBump c r hr).le_one (x := z)

/-- The complementary factor occurring in the sequential partition also
takes values in the complex unit disk. -/
theorem norm_one_sub_complexUniformBump_le_one
    (c : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    ‖1 - complexUniformBump c r hr z‖ ≤ 1 := by
  have hnonneg :
      0 ≤ 1 - uniformContDiffBump c r hr z := by
    linarith [(uniformContDiffBump c r hr).le_one (x := z)]
  calc
    ‖1 - complexUniformBump c r hr z‖ =
        ‖((1 - uniformContDiffBump c r hr z : ℝ) : ℂ)‖ := by
      congr 1
      simp [complexUniformBump]
    _ = |1 - uniformContDiffBump c r hr z| :=
      Complex.norm_real _
    _ = 1 - uniformContDiffBump c r hr z :=
      abs_of_nonneg hnonneg
    _ ≤ 1 := by
      linarith [(uniformContDiffBump c r hr).nonneg (x := z)]

/-- Pointwise derivative form of the scale-uniform Lipschitz estimate. -/
theorem norm_fderiv_complexUniformBump_le
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    ‖fderiv ℝ (complexUniformBump c r hr) z‖ ≤
      (C : ℝ) * r⁻¹ := by
  have hLip :=
    lipschitzWith_complexUniformBump C hC c r hr
  calc
    ‖fderiv ℝ (complexUniformBump c r hr) z‖
        ≤ ((C * (r⁻¹).toNNReal : NNReal) : ℝ) :=
      norm_fderiv_le_of_lipschitz ℝ hLip
    _ = (C : ℝ) * r⁻¹ := by
      rw [NNReal.coe_mul,
        Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)]

/-- The derivative of a finite product of unit-bounded complex functions is
bounded by the sum of the derivative norms of its factors. -/
theorem norm_fderiv_finsetProd_le_sum
    {ι : Type*} [DecidableEq ι] (t : Finset ι)
    (F : ι → ℂ → ℂ) (z : ℂ)
    (hFdiff : ∀ i ∈ t, DifferentiableAt ℝ (F i) z)
    (hFnorm : ∀ i ∈ t, ‖F i z‖ ≤ 1) :
    ‖fderiv ℝ (fun w ↦ ∏ i ∈ t, F i w) z‖ ≤
      ∑ i ∈ t, ‖fderiv ℝ (F i) z‖ := by
  rw [fderiv_finsetProd hFdiff]
  calc
    ‖∑ i ∈ t,
        (∏ j ∈ t.erase i, F j z) •
          fderiv ℝ (F i) z‖
        ≤ ∑ i ∈ t,
            ‖(∏ j ∈ t.erase i, F j z) •
              fderiv ℝ (F i) z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ i ∈ t, ‖fderiv ℝ (F i) z‖ := by
      apply Finset.sum_le_sum
      intro i hi
      rw [norm_smul]
      apply mul_le_of_le_one_left (norm_nonneg _)
      rw [norm_prod]
      exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
        fun j hj ↦ hFnorm j (Finset.mem_of_mem_erase hj)

open Classical in
/-- Indices of raw bumps whose topological supports contain a given
point. -/
def activeUniformBumps
    {ι : Type*} [Fintype ι] (c : ι → ℂ)
    (r : ℝ) (hr : 0 < r) (z : ℂ) : Finset ι :=
  Finset.univ.filter fun i ↦
    z ∈ tsupport (complexUniformBump (c i) r hr)

/-- The sum of all raw-bump derivative norms only counts bumps active at
the point. -/
theorem sum_norm_fderiv_complexUniformBump_le
    {ι : Type*} [Fintype ι]
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ) :
    (∑ i, ‖fderiv ℝ (complexUniformBump (c i) r hr) z‖) ≤
      (activeUniformBumps c r hr z).card *
        ((C : ℝ) * r⁻¹) := by
  classical
  calc
    (∑ i, ‖fderiv ℝ
        (complexUniformBump (c i) r hr) z‖)
        ≤ ∑ i, if z ∈
              tsupport (complexUniformBump (c i) r hr)
            then (C : ℝ) * r⁻¹ else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      split_ifs with hi
      · exact norm_fderiv_complexUniformBump_le C hC (c i) r hr z
      · rw [fderiv_of_notMem_tsupport ℝ hi, norm_zero]
    _ = (activeUniformBumps c r hr z).card *
          ((C : ℝ) * r⁻¹) := by
      rw [← Finset.sum_filter]
      change
        (∑ _ ∈ activeUniformBumps c r hr z,
          (C : ℝ) * r⁻¹) =
            (activeUniformBumps c r hr z).card *
              ((C : ℝ) * r⁻¹)
      rw [Finset.sum_const, nsmul_eq_mul]

open Classical in
/-- Pointwise formula for a member of the explicit sequential partition,
after complexifying its real values. -/
theorem complexPartitionCutoff_uniformSmoothPartition_eq
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (i : ι) (z : ℂ) :
    complexPartitionCutoff
        (uniformSmoothPartition S c r hr hcover) i z =
      complexUniformBump (c i) r hr z *
        ∏ j ∈ Finset.univ with WellOrderingRel j i,
          (1 - complexUniformBump (c j) r hr z) := by
  have hreal :=
    (uniformBumpCovering S c r hr hcover).toPartitionOfUnity_eq_mul_prod
      i z Finset.univ (by simp)
  change
    (((uniformBumpCovering S c r hr hcover).toPartitionOfUnity i z :
        ℝ) : ℂ) =
      ((uniformContDiffBump (c i) r hr z : ℝ) : ℂ) *
        ∏ j ∈ Finset.univ with WellOrderingRel j i,
          (1 - ((uniformContDiffBump (c j) r hr z : ℝ) : ℂ))
  exact_mod_cast hreal

open Classical in
/-- A member of the sequential partition has derivative controlled by the
total derivative mass of the active raw bumps.  This bound is independent
of the ordering used by `WellOrderingRel`. -/
theorem norm_fderiv_complexPartitionCutoff_uniform_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (i : ι) (z : ℂ) :
    ‖fderiv ℝ
        (complexPartitionCutoff
          (uniformSmoothPartition S c r hr hcover) i) z‖ ≤
      2 * (activeUniformBumps c r hr z).card *
        ((C : ℝ) * r⁻¹) := by
  let t : Finset ι :=
    Finset.univ.filter fun j ↦ WellOrderingRel j i
  let B : ι → ℂ → ℂ :=
    fun j ↦ complexUniformBump (c j) r hr
  let P : ℂ → ℂ :=
    fun w ↦ ∏ j ∈ t, (1 - B j w)
  have hBdiff (j : ι) :
      DifferentiableAt ℝ (B j) z :=
    (contDiff_complexUniformBump (c j) r hr).differentiable
      (by simp) z
  have hFdiff :
      ∀ j ∈ t,
        DifferentiableAt ℝ (fun w ↦ 1 - B j w) z := by
    intro j _hj
    exact (differentiableAt_const (1 : ℂ)).sub (hBdiff j)
  have hPdiff : DifferentiableAt ℝ P z := by
    dsimp only [P]
    exact
      (HasFDerivAt.finsetProd
        (g := fun j w ↦ 1 - B j w)
        (g' := fun j ↦
          fderiv ℝ (fun w ↦ 1 - B j w) z)
        fun j hj ↦ (hFdiff j hj).hasFDerivAt).differentiableAt
  have hPnorm : ‖P z‖ ≤ 1 := by
    dsimp only [P]
    rw [norm_prod]
    exact Finset.prod_le_one (fun _ _ ↦ norm_nonneg _)
      fun j hj ↦ by
        exact norm_one_sub_complexUniformBump_le_one
          (c j) r hr z
  have hDP :
      ‖fderiv ℝ P z‖ ≤
        ∑ j ∈ t, ‖fderiv ℝ (B j) z‖ := by
    have h :=
      norm_fderiv_finsetProd_le_sum t
        (fun j w ↦ 1 - B j w) z hFdiff
        (fun j _hj ↦
          norm_one_sub_complexUniformBump_le_one
            (c j) r hr z)
    simpa only [P, fderiv_const_sub, norm_neg] using h
  have hχfun :
      complexPartitionCutoff
          (uniformSmoothPartition S c r hr hcover) i =
        fun w ↦ B i w * P w := by
    funext w
    rw [complexPartitionCutoff_uniformSmoothPartition_eq
      S c r hr hcover i w]
  rw [hχfun, fderiv_fun_mul (hBdiff i) hPdiff]
  calc
    ‖B i z • fderiv ℝ P z +
        P z • fderiv ℝ (B i) z‖
        ≤ ‖B i z • fderiv ℝ P z‖ +
            ‖P z • fderiv ℝ (B i) z‖ :=
      norm_add_le _ _
    _ ≤ ‖fderiv ℝ P z‖ +
          ‖fderiv ℝ (B i) z‖ := by
      apply add_le_add
      · calc
          ‖B i z • fderiv ℝ P z‖
              ≤ ‖B i z‖ * ‖fderiv ℝ P z‖ :=
            norm_smul_le _ _
          _ ≤ 1 * ‖fderiv ℝ P z‖ := by
            gcongr
            exact norm_complexUniformBump_le_one
              (c i) r hr z
          _ = ‖fderiv ℝ P z‖ := one_mul _
      · calc
          ‖P z • fderiv ℝ (B i) z‖
              ≤ ‖P z‖ * ‖fderiv ℝ (B i) z‖ :=
            norm_smul_le _ _
          _ ≤ 1 * ‖fderiv ℝ (B i) z‖ := by
            gcongr
          _ = ‖fderiv ℝ (B i) z‖ := one_mul _
    _ ≤ (∑ j ∈ t, ‖fderiv ℝ (B j) z‖) +
          ‖fderiv ℝ (B i) z‖ :=
      add_le_add hDP le_rfl
    _ ≤ (∑ j, ‖fderiv ℝ (B j) z‖) +
          ∑ j, ‖fderiv ℝ (B j) z‖ := by
      apply add_le_add
      · exact Finset.sum_le_sum_of_subset_of_nonneg
          (Finset.filter_subset _ _)
          (fun _ _ _ ↦ norm_nonneg _)
      · exact Finset.univ.single_le_sum
          (f := fun j ↦ ‖fderiv ℝ (B j) z‖)
          (fun _ _ ↦ norm_nonneg _) (Finset.mem_univ i)
    _ = 2 * ∑ j, ‖fderiv ℝ (B j) z‖ := by ring
    _ ≤ 2 * ((activeUniformBumps c r hr z).card *
          ((C : ℝ) * r⁻¹)) := by
      gcongr
      simpa only [B] using
        sum_norm_fderiv_complexUniformBump_le
          C hC c r hr z
    _ = 2 * (activeUniformBumps c r hr z).card *
          ((C : ℝ) * r⁻¹) := by ring

open Classical in
/-- An inactive raw bump forces the corresponding sequential partition
member to vanish on a neighborhood, so its derivative is zero. -/
theorem fderiv_complexPartitionCutoff_uniform_eq_zero_of_inactive
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (i : ι) (z : ℂ)
    (hi : i ∉ activeUniformBumps c r hr z) :
    fderiv ℝ
      (complexPartitionCutoff
        (uniformSmoothPartition S c r hr hcover) i) z = 0 := by
  have hi' :
      z ∉ tsupport (complexUniformBump (c i) r hr) := by
    simpa [activeUniformBumps] using hi
  have hBzero :
      complexUniformBump (c i) r hr =ᶠ[𝓝 z] 0 := by
    simpa only [notMem_tsupport_iff_eventuallyEq] using hi'
  have hχzero :
      complexPartitionCutoff
          (uniformSmoothPartition S c r hr hcover) i =ᶠ[𝓝 z]
        0 := by
    filter_upwards [hBzero] with w hw
    rw [complexPartitionCutoff_uniformSmoothPartition_eq
      S c r hr hcover i w]
    simp [hw]
  apply fderiv_of_notMem_tsupport ℝ
  simpa only [notMem_tsupport_iff_eventuallyEq] using hχzero

open Classical in
/-- The total derivative mass of the explicit partition is controlled by
the square of the number of active raw bumps. -/
theorem sum_norm_fderiv_complexPartitionCutoff_uniform_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (z : ℂ) :
    (∑ i, ‖fderiv ℝ
        (complexPartitionCutoff
          (uniformSmoothPartition S c r hr hcover) i) z‖) ≤
      2 * (activeUniformBumps c r hr z).card ^ 2 *
        ((C : ℝ) * r⁻¹) := by
  let M : ℝ := (activeUniformBumps c r hr z).card
  let L : ℝ := (C : ℝ) * r⁻¹
  calc
    (∑ i, ‖fderiv ℝ
        (complexPartitionCutoff
          (uniformSmoothPartition S c r hr hcover) i) z‖)
        ≤ ∑ i, if i ∈ activeUniformBumps c r hr z
            then 2 * M * L else 0 := by
      apply Finset.sum_le_sum
      intro i _hi
      split_ifs with hi
      · simpa only [M, L] using
          norm_fderiv_complexPartitionCutoff_uniform_le
            S C hC c r hr hcover i z
      · rw [
          fderiv_complexPartitionCutoff_uniform_eq_zero_of_inactive
            S c r hr hcover i z hi,
          norm_zero]
    _ = (activeUniformBumps c r hr z).card *
          (2 * M * L) := by
      rw [← Finset.sum_filter]
      rw [Finset.filter_mem_eq_inter, Finset.univ_inter]
      change
        (∑ _ ∈ activeUniformBumps c r hr z, 2 * M * L) =
          (activeUniformBumps c r hr z).card * (2 * M * L)
      rw [Finset.sum_const, nsmul_eq_mul]
    _ = 2 * (activeUniformBumps c r hr z).card ^ 2 *
          ((C : ℝ) * r⁻¹) := by
      dsimp only [M, L]
      ring

/-- The Cauchy--Riemann defect is controlled by twice the operator norm of
the real Fréchet derivative.  The factor two is deliberately coarse and
keeps the estimate insensitive to normalization conventions. -/
theorem norm_crDefect_le_two_mul_norm_fderiv
    (F : ℂ → ℂ) (z : ℂ) :
    ‖crDefect F z‖ ≤
      2 * ‖fderiv ℝ F z‖ := by
  let D : ℂ →L[ℝ] ℂ := fderiv ℝ F z
  have hOne : ‖D 1‖ ≤ ‖D‖ := by
    simpa only [norm_one, mul_one] using D.le_opNorm (1 : ℂ)
  have hI : ‖D Complex.I‖ ≤ ‖D‖ := by
    simpa only [Complex.norm_I, mul_one] using
      D.le_opNorm Complex.I
  rw [crDefect]
  calc
    ‖Complex.I * D 1 - D Complex.I‖
        ≤ ‖Complex.I * D 1‖ + ‖D Complex.I‖ :=
      norm_sub_le _ _
    _ = ‖D 1‖ + ‖D Complex.I‖ := by
      rw [norm_mul, Complex.norm_I, one_mul]
    _ ≤ ‖D‖ + ‖D‖ :=
      add_le_add hOne hI
    _ = 2 * ‖fderiv ℝ F z‖ := by
      dsimp only [D]
      ring

/-- The aggregate Cauchy--Riemann defect of the explicit partition has the
same scale bound as its derivative aggregate. -/
theorem sum_norm_crDefect_complexPartitionCutoff_uniform_le
    {ι : Type*} [Fintype ι] (S : Set ℂ)
    (C : NNReal) (hC : LipschitzWith C referenceComplexBump)
    (c : ι → ℂ) (r : ℝ) (hr : 0 < r)
    (hcover : S ⊆ ⋃ i, Metric.ball (c i) (3 * r / 2))
    (z : ℂ) :
    (∑ i, ‖crDefect
        (complexPartitionCutoff
          (uniformSmoothPartition S c r hr hcover) i) z‖) ≤
      4 * (activeUniformBumps c r hr z).card ^ 2 *
        ((C : ℝ) * r⁻¹) := by
  calc
    (∑ i, ‖crDefect
        (complexPartitionCutoff
          (uniformSmoothPartition S c r hr hcover) i) z‖)
        ≤ ∑ i, 2 * ‖fderiv ℝ
            (complexPartitionCutoff
              (uniformSmoothPartition S c r hr hcover) i) z‖ := by
      apply Finset.sum_le_sum
      intro i _hi
      exact norm_crDefect_le_two_mul_norm_fderiv _ _
    _ = 2 * ∑ i, ‖fderiv ℝ
          (complexPartitionCutoff
            (uniformSmoothPartition S c r hr hcover) i) z‖ := by
      rw [Finset.mul_sum]
    _ ≤ 2 * (2 * (activeUniformBumps c r hr z).card ^ 2 *
          ((C : ℝ) * r⁻¹)) := by
      gcongr
      exact
        sum_norm_fderiv_complexPartitionCutoff_uniform_le
          S C hC c r hr hcover z
    _ = 4 * (activeUniformBumps c r hr z).card ^ 2 *
          ((C : ℝ) * r⁻¹) := by ring

/-- There is one constant controlling the Cauchy--Riemann defects of all
translated and rescaled raw bumps. -/
theorem exists_uniform_norm_crDefect_bump_le :
    ∃ C : NNReal, ∀ (c : ℂ) (r : ℝ) (hr : 0 < r) (z : ℂ),
      ‖crDefect (complexUniformBump c r hr) z‖ ≤
        (C : ℝ) * r⁻¹ := by
  have hrefSmooth :
      ContDiff ℝ ∞ referenceComplexBump := by
    change ContDiff ℝ ∞ (complexUniformBump 0 1 zero_lt_one)
    exact contDiff_complexUniformBump 0 1 zero_lt_one
  have hrefCompact :
      HasCompactSupport referenceComplexBump := by
    change HasCompactSupport (complexUniformBump 0 1 zero_lt_one)
    exact hasCompactSupport_complexUniformBump 0 1 zero_lt_one
  obtain ⟨C, hC⟩ :=
    ContDiff.lipschitzWith_of_hasCompactSupport
      hrefCompact hrefSmooth (by simp)
  refine ⟨2 * C, ?_⟩
  intro c r hr z
  have hLip :=
    lipschitzWith_complexUniformBump C hC c r hr
  calc
    ‖crDefect (complexUniformBump c r hr) z‖
        ≤ 2 *
            ‖fderiv ℝ (complexUniformBump c r hr) z‖ :=
      norm_crDefect_le_two_mul_norm_fderiv _ _
    _ ≤ 2 *
          ((C * (r⁻¹).toNNReal : NNReal) : ℝ) := by
      gcongr
      exact norm_fderiv_le_of_lipschitz ℝ hLip
    _ = ((2 * C : NNReal) : ℝ) * r⁻¹ := by
      rw [NNReal.coe_mul,
        Real.coe_toNNReal _ (inv_nonneg.mpr hr.le)]
      rw [NNReal.coe_mul]
      norm_num
      ring

/-- If equal-radius source balls split into finitely many pairwise-disjoint
families, the number of raw bumps active at any point is uniformly bounded.
The bound depends only on the number of families and the dimension of the
ambient plane, not on the scale or the size of the cover. -/
theorem card_activeUniformBumps_le_of_pairwiseDisjoint
    {ι κ : Type*} [Fintype ι] [Fintype κ]
    (family : ι → κ) (c : ι → ℂ)
    (r : ℝ) (hr : 0 < r)
    (hdisj :
      ∀ k,
        Set.Pairwise {i | family i = k}
          (Disjoint on fun i ↦ Metric.closedBall (c i) r))
    (z : ℂ) :
    (activeUniformBumps c r hr z).card ≤
      Fintype.card κ * 5 ^ Module.finrank ℝ ℂ := by
  classical
  let active : Finset ι := activeUniformBumps c r hr z
  have hcard :
      active.card =
        ∑ k, (active.filter fun i ↦ family i = k).card := by
    exact Finset.card_eq_sum_card_fiberwise
      (s := active) (t := Finset.univ) (f := family)
      (by simp)
  rw [hcard]
  calc
    (∑ k, (active.filter fun i ↦ family i = k).card)
        ≤ ∑ _ : κ, 5 ^ Module.finrank ℝ ℂ := by
      apply Finset.sum_le_sum
      intro k _hk
      let fiber : Finset ι :=
        active.filter fun i ↦ family i = k
      let F : ι → ℂ :=
        fun i ↦ r⁻¹ • (c i - z)
      let q : Finset ℂ := fiber.image F
      have hactive {i : ι} (hi : i ∈ fiber) :
          i ∈ active := (Finset.mem_filter.mp hi).1
      have hfamily {i : ι} (hi : i ∈ fiber) :
          family i = k := (Finset.mem_filter.mp hi).2
      have hnorm : ∀ v ∈ q, ‖v‖ ≤ 2 := by
        intro v hv
        rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
        have hiz :
            z ∈ Metric.closedBall (c i) (2 * r) := by
          apply tsupport_complexUniformBump_subset_closedBall
            (c i) r hr
          simpa only [active, activeUniformBumps,
            Finset.mem_filter, Finset.mem_univ, true_and] using
              hactive hi
        have hciz : ‖c i - z‖ ≤ 2 * r := by
          simpa only [Metric.mem_closedBall, dist_eq_norm,
            norm_sub_rev] using hiz
        calc
          ‖r⁻¹ • (c i - z)‖ =
              r⁻¹ * ‖c i - z‖ := by
            rw [norm_smul, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hr)]
          _ ≤ r⁻¹ * (2 * r) :=
            mul_le_mul_of_nonneg_left hciz
              (inv_nonneg.mpr hr.le)
          _ = 2 := by field_simp
      have hsepIndex :
          ∀ i ∈ fiber, ∀ j ∈ fiber, i ≠ j →
            1 ≤ ‖F i - F j‖ := by
        intro i hi j hj hij
        have hd :
            Disjoint (Metric.closedBall (c i) r)
              (Metric.closedBall (c j) r) :=
          hdisj k (hfamily hi) (hfamily hj) hij
        have hdist : 2 * r < dist (c i) (c j) := by
          have :=
            (disjoint_closedBall_closedBall_iff
              hr.le hr.le).mp hd
          linarith
        have hscaled :
            2 < r⁻¹ * dist (c i) (c j) := by
          calc
            2 = r⁻¹ * (2 * r) := by field_simp
            _ < r⁻¹ * dist (c i) (c j) :=
              mul_lt_mul_of_pos_left hdist (inv_pos.mpr hr)
        calc
          1 ≤ r⁻¹ * dist (c i) (c j) := by
            linarith
          _ = ‖F i - F j‖ := by
            dsimp only [F]
            rw [← smul_sub, norm_smul, Real.norm_eq_abs,
              abs_of_pos (inv_pos.mpr hr), dist_eq_norm]
            congr 2
            ring
      have hInj : Set.InjOn F fiber := by
        intro i hi j hj hijF
        by_contra hij
        have hsep := hsepIndex i hi j hj hij
        rw [hijF, sub_self, norm_zero] at hsep
        norm_num at hsep
      have hqcard : q.card = fiber.card := by
        exact Finset.card_image_iff.mpr hInj
      have hqsep :
          ∀ v ∈ q, ∀ w ∈ q, v ≠ w →
            1 ≤ ‖v - w‖ := by
        intro v hv w hw hvw
        rcases Finset.mem_image.mp hv with ⟨i, hi, rfl⟩
        rcases Finset.mem_image.mp hw with ⟨j, hj, rfl⟩
        exact hsepIndex i hi j hj fun hij ↦ hvw (congrArg F hij)
      have hqbound :
          q.card ≤ 5 ^ Module.finrank ℝ ℂ :=
        Besicovitch.card_le_of_separated q hnorm hqsep
      rw [hqcard] at hqbound
      simpa only [fiber] using hqbound
    _ = Fintype.card κ * 5 ^ Module.finrank ℝ ℂ := by
      simp

/-- Equal-radius specialization of the finite Besicovitch selection. -/
theorem exists_finite_equalRadius_besicovitch_ball_cover
    (S : Set ℂ) (hS : IsCompact S)
    (r : ℝ) (hr : 0 < r) :
    ∃ (N : ℕ) (A : Fin N → Set S)
        (t : Finset (Σ k : Fin N, {z : S // z ∈ A k})),
      (∀ k,
        (A k).PairwiseDisjoint
          (fun z ↦ Metric.closedBall (z : ℂ) r)) ∧
      S ⊆ ⋃ u ∈ t,
        Metric.ball (u.2.1 : ℂ) r := by
  obtain ⟨N, τ, hτ, hN⟩ :
      ∃ (N : ℕ) (τ : ℝ), 1 < τ ∧
        IsEmpty (Besicovitch.SatelliteConfig ℂ N τ) :=
    HasBesicovitchCovering.no_satelliteConfig
  let q : Besicovitch.BallPackage S ℂ :=
    { c := fun z ↦ (z : ℂ)
      r := fun _ ↦ r
      rpos := fun _ ↦ hr
      r_bound := r
      r_le := fun _ ↦ le_rfl }
  obtain ⟨A, hAdisjoint, hAcover⟩ :=
    Besicovitch.exist_disjoint_covering_families hτ hN q
  let U : (Σ k : Fin N, {z : S // z ∈ A k}) → Set ℂ :=
    fun u ↦ Metric.ball (u.2.1 : ℂ) r
  have hcover : S ⊆ ⋃ u, U u := by
    intro z hz
    have hzrange : z ∈ range q.c := by
      exact ⟨⟨z, hz⟩, rfl⟩
    have hzballs := hAcover hzrange
    rcases mem_iUnion.mp hzballs with ⟨k, hk⟩
    rcases mem_iUnion.mp hk with ⟨j, hj⟩
    rcases mem_iUnion.mp hj with ⟨hjA, hjball⟩
    apply mem_iUnion.mpr
    refine ⟨⟨k, ⟨j, hjA⟩⟩, ?_⟩
    simpa only [U, q] using hjball
  obtain ⟨t, ht⟩ :=
    hS.elim_finite_subcover U
      (fun _ ↦ Metric.isOpen_ball) hcover
  refine ⟨N, A, t, ?_, ?_⟩
  · simpa only [q] using hAdisjoint
  · simpa only [U] using ht

/-- A compact planar set has an equal-radius finite cover whose centers
split into finitely many disjoint families.  The associated explicit bump
family has a scale-independent overlap bound. -/
theorem exists_uniform_besicovitch_cover
    (S : Set ℂ) (hS : IsCompact S)
    (r : ℝ) (hr : 0 < r) :
    ∃ (N : ℕ) (A : Fin N → Set S)
        (t : Finset (Σ k : Fin N, {z : S // z ∈ A k})),
      (∀ k,
        (A k).PairwiseDisjoint
          (fun z ↦ Metric.closedBall (z : ℂ) r)) ∧
      S ⊆ ⋃ i : t,
        Metric.ball (i.1.2.1 : ℂ) (3 * r / 2) ∧
      ∀ z : ℂ,
        (activeUniformBumps
          (fun i : t ↦ (i.1.2.1 : ℂ)) r hr z).card ≤
            N * 25 := by
  obtain ⟨N, A, t, hAdisjoint, hcover⟩ :=
    exists_finite_equalRadius_besicovitch_ball_cover
      S hS r hr
  refine ⟨N, A, t, hAdisjoint, ?_, ?_⟩
  · intro z hz
    rcases mem_iUnion.mp (hcover hz) with ⟨u, hu⟩
    rcases mem_iUnion.mp hu with ⟨hut, hzu⟩
    apply mem_iUnion.mpr
    refine ⟨⟨u, hut⟩, ?_⟩
    exact Metric.ball_subset_ball (by linarith) hzu
  · have hindexDisjoint :
        ∀ k,
          Set.Pairwise
            {i : t | i.1.1 = k}
            (Disjoint on fun i ↦
              Metric.closedBall (i.1.2.1 : ℂ) r) := by
      intro k i hi j hj hij
      rcases i with ⟨⟨ki, xi⟩, hit⟩
      rcases j with ⟨⟨kj, xj⟩, hjt⟩
      change ki = k at hi
      change kj = k at hj
      subst ki
      subst kj
      have hxine : xi.1 ≠ xj.1 := by
        intro h
        have hx : xi = xj := Subtype.ext h
        subst xj
        exact hij rfl
      exact hAdisjoint k xi.2 xj.2 hxine
    intro z
    have hbound :=
      card_activeUniformBumps_le_of_pairwiseDisjoint
        (family := fun i : t ↦ i.1.1)
        (c := fun i : t ↦ (i.1.2.1 : ℂ))
        r hr hindexDisjoint z
    simpa [Complex.finrank_real_complex] using hbound

/-- The norm of the planar Cauchy kernel is integrable on every centered
ball. -/
theorem integrableOn_norm_inv_ball (R : ℝ) :
    MeasureTheory.IntegrableOn
      (fun w : ℂ ↦ ‖w⁻¹‖) (Metric.ball 0 R) :=
  MeasureTheory.IntegrableOn.mono_set
    (locallyIntegrable_inv.integrableOn_isCompact
      (isCompact_closedBall (0 : ℂ) R)).norm
    Metric.ball_subset_closedBall

/-- Translation to the origin preserves the integral of the norm of the
Cauchy kernel over a ball. -/
theorem integral_norm_inv_sub_ball_eq_centered
    (z : ℂ) (R : ℝ) :
    (∫ w : ℂ in Metric.ball z R, ‖(w - z)⁻¹‖) =
      ∫ w : ℂ in Metric.ball 0 R, ‖w⁻¹‖ := by
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.addRight (-z)
  have h :=
    (MeasureTheory.measurePreserving_add_right
        MeasureTheory.volume (-z)).setIntegral_preimage_emb
      e.measurableEmbedding (fun w : ℂ ↦ ‖w⁻¹‖)
      (Metric.ball 0 R)
  have hpre :
      (fun w : ℂ ↦ w + -z) ⁻¹' Metric.ball 0 R =
        Metric.ball z R := by
    ext w
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm,
      sub_eq_add_neg, neg_zero, add_zero]
  simpa only [e, sub_eq_add_neg, hpre] using h

/-- Exact scale covariance of the integral of the norm of the Cauchy
kernel on a centered ball. -/
theorem integral_norm_inv_ball_mul
    (R r : ℝ) (hr : 0 < r) :
    (∫ w : ℂ in Metric.ball 0 (r * R), ‖w⁻¹‖) =
      r * ∫ w : ℂ in Metric.ball 0 R, ‖w⁻¹‖ := by
  have h :=
    MeasureTheory.Measure.setIntegral_comp_smul_of_pos
      MeasureTheory.volume (fun w : ℂ ↦ ‖w⁻¹‖)
      (Metric.ball 0 R) hr
  have hscaled :
      (∫ w : ℂ in Metric.ball 0 R, ‖(r • w)⁻¹‖) =
        r⁻¹ * ∫ w : ℂ in Metric.ball 0 R, ‖w⁻¹‖ := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    rw [norm_inv, norm_smul, Real.norm_eq_abs,
      abs_of_pos hr, mul_inv, norm_inv]
  rw [hscaled] at h
  simp only [Complex.finrank_real_complex, smul_eq_mul,
    _root_.smul_ball hr.ne' (0 : ℂ), Real.norm_eq_abs,
    abs_of_pos hr, smul_zero] at h
  field_simp [hr.ne'] at h ⊢
  nlinarith

/-- The preceding covariance, with an arbitrary center. -/
theorem integral_norm_inv_sub_ball_mul
    (z : ℂ) (R r : ℝ) (hr : 0 < r) :
    (∫ w : ℂ in Metric.ball z (r * R), ‖(w - z)⁻¹‖) =
      r * ∫ w : ℂ in Metric.ball 0 R, ‖w⁻¹‖ := by
  rw [integral_norm_inv_sub_ball_eq_centered,
    integral_norm_inv_ball_mul R r hr]

/-- The cubic far-field kernel is integrable outside the unit ball. -/
theorem integrableOn_norm_inv_pow_three_compl_ball :
    MeasureTheory.IntegrableOn
      (fun w : ℂ ↦ ‖w‖⁻¹ ^ 3) (Metric.ball 0 1)ᶜ := by
  have hbase :
      MeasureTheory.Integrable
        (fun w : ℂ ↦ (1 + ‖w‖) ^ (-(3 : ℝ))) :=
    integrable_one_add_norm
      (E := ℂ) (μ := MeasureTheory.volume)
      (by norm_num [Complex.finrank_real_complex])
  have hmeas :
      MeasureTheory.AEStronglyMeasurable
        (fun w : ℂ ↦ ‖w‖⁻¹ ^ 3) MeasureTheory.volume :=
    ((measurable_inv.comp measurable_norm).pow_const 3).aestronglyMeasurable
  refine (hbase.const_mul 8).integrableOn.mono'
    hmeas.restrict ?_
  filter_upwards
    [MeasureTheory.ae_restrict_mem measurableSet_ball.compl] with w hw
  have hw' : 1 ≤ ‖w‖ := by
    simpa only [mem_compl_iff, Metric.mem_ball, dist_zero_right,
      not_lt] using hw
  have hwpos : 0 < ‖w‖ :=
    zero_lt_one.trans_le hw'
  have hpow :
      (1 + ‖w‖) ^ 3 ≤ 8 * ‖w‖ ^ 3 := by
    calc
      (1 + ‖w‖) ^ 3 ≤ (2 * ‖w‖) ^ 3 := by
        gcongr
        linarith
      _ = 8 * ‖w‖ ^ 3 := by ring
  have hkernel :
      ‖w‖⁻¹ ^ 3 ≤
        8 * (1 + ‖w‖)⁻¹ ^ 3 := by
    rw [inv_pow, inv_pow, inv_eq_one_div, inv_eq_one_div]
    rw [← mul_div_assoc, mul_one]
    rw [div_le_div_iff₀
      (pow_pos hwpos 3) (pow_pos (by positivity) 3)]
    simpa only [one_mul] using hpow
  have hrpow :
      (1 + ‖w‖) ^ (-(3 : ℝ)) =
        (1 + ‖w‖)⁻¹ ^ 3 := by
    rw [Real.rpow_neg (by positivity)]
    calc
      ((1 + ‖w‖) ^ (3 : ℝ))⁻¹ =
          ((1 + ‖w‖) ^ (3 : ℕ))⁻¹ :=
        congrArg Inv.inv (Real.rpow_natCast _ 3)
      _ = (1 + ‖w‖)⁻¹ ^ 3 :=
        (inv_pow _ 3).symm
  rw [hrpow]
  simpa only [Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (norm_nonneg _)) _),
    abs_of_nonneg
      (mul_nonneg (by norm_num)
        (pow_nonneg (inv_nonneg.mpr (by positivity)) _))] using hkernel

/-- Translation to the origin preserves the integral of the cubic
far-field kernel over the complement of a ball. -/
theorem integral_norm_sub_inv_pow_three_compl_ball_eq_centered
    (z : ℂ) (R : ℝ) :
    (∫ w : ℂ in (Metric.ball z R)ᶜ,
        ‖w - z‖⁻¹ ^ 3) =
      ∫ w : ℂ in (Metric.ball 0 R)ᶜ,
        ‖w‖⁻¹ ^ 3 := by
  let e : ℂ ≃ᵐ ℂ := MeasurableEquiv.addRight (-z)
  have h :=
    (MeasureTheory.measurePreserving_add_right
        MeasureTheory.volume (-z)).setIntegral_preimage_emb
      e.measurableEmbedding (fun w : ℂ ↦ ‖w‖⁻¹ ^ 3)
      (Metric.ball 0 R)ᶜ
  have hpre :
      (fun w : ℂ ↦ w + -z) ⁻¹' Metric.ball 0 R =
        Metric.ball z R := by
    ext w
    simp only [mem_preimage, Metric.mem_ball, dist_eq_norm,
      sub_eq_add_neg, neg_zero, add_zero]
  rw [preimage_compl, hpre] at h
  simpa only [e, sub_eq_add_neg] using h

/-- Exact scale covariance of the cubic far-field kernel over the
complement of a centered ball. -/
theorem integral_norm_inv_pow_three_compl_ball_mul
    (R r : ℝ) (hr : 0 < r) :
    (∫ w : ℂ in (Metric.ball 0 (r * R))ᶜ,
        ‖w‖⁻¹ ^ 3) =
      r⁻¹ * ∫ w : ℂ in (Metric.ball 0 R)ᶜ,
        ‖w‖⁻¹ ^ 3 := by
  have hset :
      r • (Metric.ball (0 : ℂ) R)ᶜ =
        (Metric.ball 0 (r * R))ᶜ := by
    rw [compl_eq_univ_sdiff,
      Set.smul_set_sdiff₀ hr.ne',
      Set.smul_set_univ₀ hr.ne',
      _root_.smul_ball hr.ne' (0 : ℂ)]
    simp only [Real.norm_eq_abs, abs_of_pos hr, smul_zero,
      compl_eq_univ_sdiff]
  have h :=
    MeasureTheory.Measure.setIntegral_comp_smul_of_pos
      MeasureTheory.volume
      (fun w : ℂ ↦ ‖w‖⁻¹ ^ 3)
      (Metric.ball 0 R)ᶜ hr
  have hscaled :
      (∫ w : ℂ in (Metric.ball 0 R)ᶜ,
          ‖r • w‖⁻¹ ^ 3) =
        r⁻¹ ^ 3 *
          ∫ w : ℂ in (Metric.ball 0 R)ᶜ,
            ‖w‖⁻¹ ^ 3 := by
    rw [← MeasureTheory.integral_const_mul]
    apply MeasureTheory.integral_congr_ae
    filter_upwards with w
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
      mul_inv, mul_pow]
  rw [hscaled, hset] at h
  simp only [Complex.finrank_real_complex, smul_eq_mul] at h
  field_simp [hr.ne'] at h ⊢
  nlinarith

/-- The preceding covariance, with an arbitrary center. -/
theorem integral_norm_sub_inv_pow_three_compl_ball_mul
    (z : ℂ) (R r : ℝ) (hr : 0 < r) :
    (∫ w : ℂ in (Metric.ball z (r * R))ᶜ,
        ‖w - z‖⁻¹ ^ 3) =
      r⁻¹ * ∫ w : ℂ in (Metric.ball 0 R)ᶜ,
        ‖w‖⁻¹ ^ 3 := by
  rw [integral_norm_sub_inv_pow_three_compl_ball_eq_centered,
    integral_norm_inv_pow_three_compl_ball_mul R r hr]

end Submission.Helpers
