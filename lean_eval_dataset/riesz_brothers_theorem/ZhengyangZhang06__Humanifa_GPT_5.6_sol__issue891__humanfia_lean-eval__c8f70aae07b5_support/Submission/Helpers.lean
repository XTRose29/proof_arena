import Mathlib

open MeasureTheory
open AddCircle
open Filter
open scoped ENNReal NNReal InnerProductSpace ComplexConjugate

namespace Submission.Helpers

lemma signedVariation_le_totalVariation {α : Type*} [MeasurableSpace α]
    (s : SignedMeasure α) : s.variation ≤ s.totalVariation := by
  calc
    s.variation =
        s.toJordanDecomposition.toSignedMeasure.variation := by
      rw [SignedMeasure.toSignedMeasure_toJordanDecomposition]
    _ ≤
        s.toJordanDecomposition.posPart.toSignedMeasure.variation +
          s.toJordanDecomposition.negPart.toSignedMeasure.variation := by
      rw [JordanDecomposition.toSignedMeasure]
      exact VectorMeasure.variation_sub_le
    _ = s.totalVariation := by
      simp [SignedMeasure.totalVariation]

lemma signedVariation_isFinite {α : Type*} [MeasurableSpace α]
    (s : SignedMeasure α) : IsFiniteMeasure s.variation := by
  letI : IsFiniteMeasure s.totalVariation := by
    unfold SignedMeasure.totalVariation
    infer_instance
  exact isFiniteMeasure_of_le s.totalVariation
    (signedVariation_le_totalVariation s)

lemma complexVariation_isFinite {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) : IsFiniteMeasure μ.variation := by
  let r : ComplexMeasure α := μ.re.toComplexMeasure 0
  let i : ComplexMeasure α := (0 : SignedMeasure α).toComplexMeasure μ.im
  have hre : IsFiniteMeasure μ.re.variation := signedVariation_isFinite μ.re
  have him : IsFiniteMeasure μ.im.variation := signedVariation_isFinite μ.im
  letI := hre
  letI := him
  have hr : r.variation ≤ μ.re.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro s hs
    calc
      ‖r s‖ₑ = ‖μ.re s‖ₑ := by
        rw [show r s = (μ.re s : ℂ) by
          apply Complex.ext <;>
            simp [r, SignedMeasure.toComplexMeasure_apply]]
        simp [enorm_eq_nnnorm]
      _ ≤ μ.re.variation s := VectorMeasure.enorm_measure_le_variation μ.re s
  have hi : i.variation ≤ μ.im.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro s hs
    calc
      ‖i s‖ₑ = ‖μ.im s‖ₑ := by
        rw [show i s = (μ.im s : ℂ) * Complex.I by
          apply Complex.ext <;>
            simp [i, SignedMeasure.toComplexMeasure_apply]]
        simp [enorm_eq_nnnorm]
      _ ≤ μ.im.variation s := VectorMeasure.enorm_measure_le_variation μ.im s
  have hμri : μ = r + i := by
    rw [show μ = μ.re.toComplexMeasure μ.im from
      μ.toComplexMeasure_to_signedMeasure.symm]
    ext s hs
    apply Complex.ext <;> simp [r, i, SignedMeasure.toComplexMeasure_apply]
  rw [hμri]
  exact isFiniteMeasure_of_le (μ.re.variation + μ.im.variation)
    (VectorMeasure.variation_add_le.trans (add_le_add hr hi))

lemma complexIntegral_smul {α : Type*} [MeasurableSpace α] (μ : ComplexMeasure α)
    (c : ℂ) (f : α → ℂ) :
    ∫ᵛ x, (c • f) x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
      c • ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
  simp only [VectorMeasure.integral_eq_setToFun]
  apply setToFun_smul
  intro d s x
  rw [transpose_eq_cbmApplyMeasure]
  simp only [cbmApplyMeasure_apply]
  change (d * x) * μ s = d * (x * μ s)
  ring

noncomputable def complexIntegralLinear {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) [IsFiniteMeasure μ.variation] :
    Lp ℂ 2 μ.variation →ₗ[ℂ] ℂ where
  toFun f := ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ]
  map_add' f g := by
    rw [VectorMeasure.integral_congr_ae (Lp.coeFn_add f g)]
    exact VectorMeasure.integral_add
      ((Lp.memLp f).integrable one_le_two) ((Lp.memLp g).integrable one_le_two)
  map_smul' c f := by
    rw [VectorMeasure.integral_congr_ae (Lp.coeFn_smul c f)]
    exact complexIntegral_smul μ c f

noncomputable def complexIntegralCLM {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) [IsFiniteMeasure μ.variation] :
    Lp ℂ 2 μ.variation →L[ℂ] ℂ :=
  (complexIntegralLinear μ).mkContinuous
    (‖ContinuousLinearMap.mul ℝ ℂ‖ *
      (μ.variation Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))).toReal)
    fun f ↦ by
      have hmono :
          eLpNorm f 1 μ.variation ≤
            eLpNorm f 2 μ.variation *
              μ.variation Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ)) := by
        simpa using eLpNorm_le_eLpNorm_mul_rpow_measure_univ
          (μ := μ.variation) (f := fun x ↦ f x)
          (p := (1 : ℝ≥0∞)) (q := (2 : ℝ≥0∞))
          one_le_two (Lp.aestronglyMeasurable f)
      calc
        ‖(complexIntegralLinear μ) f‖ ≤
            ‖ContinuousLinearMap.mul ℝ ℂ‖ * ∫ x, ‖f x‖ ∂μ.variation :=
          VectorMeasure.norm_integral_le_integral_norm
        _ = ‖ContinuousLinearMap.mul ℝ ℂ‖ * (eLpNorm f 1 μ.variation).toReal := by
          rw [integral_norm_eq_lintegral_enorm (Lp.aestronglyMeasurable f),
            eLpNorm_one_eq_lintegral_enorm]
        _ ≤ ‖ContinuousLinearMap.mul ℝ ℂ‖ *
            (eLpNorm f 2 μ.variation *
              μ.variation Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))).toReal := by
          exact mul_le_mul_of_nonneg_left
            (ENNReal.toReal_mono (by finiteness) hmono)
            (norm_nonneg (ContinuousLinearMap.mul ℝ ℂ))
        _ = (‖ContinuousLinearMap.mul ℝ ℂ‖ *
              (μ.variation Set.univ ^ (1 / (1 : ℝ) - 1 / (2 : ℝ))).toReal) * ‖f‖ := by
          rw [ENNReal.toReal_mul, ← Lp.norm_def]
          ring

@[simp]
lemma complexIntegralCLM_apply {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) [IsFiniteMeasure μ.variation] (f : Lp ℂ 2 μ.variation) :
    complexIntegralCLM μ f =
      ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := rfl

lemma complexIntegral_indicator_one {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) [IsFiniteMeasure μ.variation]
    {s : Set α} (hs : MeasurableSet s) :
    ∫ᵛ x, s.indicator (fun _ ↦ (1 : ℂ)) x
      ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = μ s := by
  simp only [VectorMeasure.integral_eq_setToFun]
  rw [setToFun_indicator_const _ hs (measure_ne_top μ.variation s)]
  rw [transpose_eq_cbmApplyMeasure]
  simp

noncomputable def representingVector {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) [IsFiniteMeasure μ.variation] : Lp ℂ 2 μ.variation :=
  (InnerProductSpace.toDual ℂ (Lp ℂ 2 μ.variation)).symm (complexIntegralCLM μ)

lemma inner_representingVector {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) [IsFiniteMeasure μ.variation] (f : Lp ℂ 2 μ.variation) :
    ⟪representingVector μ, f⟫_ℂ =
      ∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
  rw [representingVector, InnerProductSpace.toDual_symm_apply]
  rfl

lemma representingVector_ae_ne_zero {α : Type*} [MeasurableSpace α]
    (μ : ComplexMeasure α) [IsFiniteMeasure μ.variation] :
    ∀ᵐ x ∂μ.variation, representingVector μ x ≠ 0 := by
  rw [ae_iff]
  simp only [not_ne_iff]
  let s : Set α := {x | representingVector μ x = 0}
  have hs : MeasurableSet s := by
    exact (Lp.stronglyMeasurable (representingVector μ)).measurable
      (measurableSet_singleton 0)
  change μ.variation s = 0
  rw [VectorMeasure.variation_apply_eq_zero hs]
  intro t hts ht
  let e : Lp ℂ 2 μ.variation :=
    indicatorConstLp 2 ht (measure_ne_top μ.variation t) 1
  have he_inner : ⟪representingVector μ, e⟫_ℂ = 0 := by
    rw [inner_eq_zero_symm]
    rw [show ⟪e, representingVector μ⟫_ℂ =
        ∫ x in t, representingVector μ x ∂μ.variation by
      exact L2.inner_indicatorConstLp_one ht (measure_ne_top μ.variation t)
        (representingVector μ)]
    apply setIntegral_eq_zero_of_ae_eq_zero
    exact Eventually.of_forall fun x hx ↦ hts hx
  calc
    μ t = ∫ᵛ x, t.indicator (fun _ ↦ (1 : ℂ)) x
        ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := (complexIntegral_indicator_one μ ht).symm
    _ = ∫ᵛ x, e x ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
      apply VectorMeasure.integral_congr_ae
      exact (indicatorConstLp_coeFn (p := 2) (μ := μ.variation)
        (c := (1 : ℂ))).symm
    _ = ⟪representingVector μ, e⟫_ℂ := (inner_representingVector μ e).symm
    _ = 0 := he_inner

lemma norm_fourier_apply (k : ℤ) (x : UnitAddCircle) : ‖fourier k x‖ = 1 := by
  change ‖((toCircle (k • x) : Circle) : ℂ)‖ = 1
  exact Circle.norm_coe _

noncomputable def fourierLpTop (ν : Measure UnitAddCircle) (k : ℤ) :
    Lp ℂ ∞ ν :=
  (memLp_top_of_bound
      ((fourier k : C(UnitAddCircle, ℂ)).continuous.aestronglyMeasurable :
        AEStronglyMeasurable
        (fun x ↦ fourier k x) ν)
      1 (Eventually.of_forall fun x ↦ (norm_fourier_apply k x).le)).toLp
    (fun x ↦ fourier k x)

lemma fourierLpTop_coeFn (ν : Measure UnitAddCircle) (k : ℤ) :
    fourierLpTop ν k =ᵐ[ν] fun x ↦ fourier k x := by
  exact MemLp.coeFn_toLp _

noncomputable def fourierShift (ν : Measure UnitAddCircle) (k : ℤ) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν :=
  (ContinuousLinearMap.mul ℂ ℂ).holderL ν
    (∞ : ℝ≥0∞) (2 : ℝ≥0∞) (2 : ℝ≥0∞) (fourierLpTop ν k)

lemma fourierShift_coeFn (ν : Measure UnitAddCircle) (k : ℤ) (f : Lp ℂ 2 ν) :
    fourierShift ν k f =ᵐ[ν] fun x ↦ fourier k x * f x := by
  filter_upwards [
      (ContinuousLinearMap.mul ℂ ℂ).coeFn_holder
        (r := (2 : ℝ≥0∞)) (fourierLpTop ν k) f,
      fourierLpTop_coeFn ν k] with x hx hfourier
  simpa [fourierShift, hfourier] using hx

lemma fourierShift_add (ν : Measure UnitAddCircle) (k l : ℤ) (f : Lp ℂ 2 ν) :
    fourierShift ν (k + l) f = fourierShift ν k (fourierShift ν l f) := by
  apply Lp.ext
  filter_upwards [fourierShift_coeFn ν (k + l) f,
      fourierShift_coeFn ν k (fourierShift ν l f),
      fourierShift_coeFn ν l f] with x hkl hk hl
  rw [hkl, hk, hl, fourier_add]
  ring

@[simp]
lemma fourierShift_zero (ν : Measure UnitAddCircle) (f : Lp ℂ 2 ν) :
    fourierShift ν 0 f = f := by
  apply Lp.ext
  filter_upwards [fourierShift_coeFn ν 0 f] with x hx
  simpa using hx

lemma norm_fourierShift (ν : Measure UnitAddCircle) (k : ℤ) (f : Lp ℂ 2 ν) :
    ‖fourierShift ν k f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  apply eLpNorm_congr_norm_ae
  filter_upwards [fourierShift_coeFn ν k f] with x hx
  rw [hx, norm_mul, norm_fourier_apply, one_mul]

noncomputable def fourierShiftLI (ν : Measure UnitAddCircle) (k : ℤ) :
    Lp ℂ 2 ν →ₗᵢ[ℂ] Lp ℂ 2 ν where
  toLinearMap := (fourierShift ν k).toLinearMap
  norm_map' := norm_fourierShift ν k

noncomputable def fourierShiftLIE (ν : Measure UnitAddCircle) (k : ℤ) :
    Lp ℂ 2 ν ≃ₗᵢ[ℂ] Lp ℂ 2 ν :=
  LinearIsometryEquiv.ofSurjective (fourierShiftLI ν k) fun f ↦
    ⟨fourierShift ν (-k) f, by
      change fourierShift ν k (fourierShift ν (-k) f) = f
      rw [← fourierShift_add, add_neg_cancel, fourierShift_zero]⟩

@[simp]
lemma fourierShiftLIE_apply (ν : Measure UnitAddCircle) (k : ℤ) (f : Lp ℂ 2 ν) :
    fourierShiftLIE ν k f = fourierShift ν k f := rfl

@[simp]
lemma fourierShiftLIE_toLinearEquiv_apply
    (ν : Measure UnitAddCircle) (k : ℤ) (f : Lp ℂ 2 ν) :
    (fourierShiftLIE ν k).toLinearEquiv f = fourierShift ν k f := rfl

lemma inner_fourierShift_neg_left (ν : Measure UnitAddCircle) (k : ℤ)
    (f g : Lp ℂ 2 ν) :
    ⟪fourierShift ν (-k) f, g⟫_ℂ = ⟪f, fourierShift ν k g⟫_ℂ := by
  calc
    ⟪fourierShift ν (-k) f, g⟫_ℂ =
        ⟪fourierShiftLIE ν k (fourierShift ν (-k) f),
          fourierShiftLIE ν k g⟫_ℂ :=
      ((fourierShiftLIE ν k).inner_map_map (fourierShift ν (-k) f) g).symm
    _ = ⟪f, fourierShift ν k g⟫_ℂ := by
      simp only [fourierShiftLIE_apply]
      rw [← fourierShift_add, add_neg_cancel, fourierShift_zero]

noncomputable def fourierToLp (ν : Measure UnitAddCircle) [IsFiniteMeasure ν]
    (k : ℤ) : Lp ℂ 2 ν :=
  ContinuousMap.toLp 2 ν ℂ (fourier k : C(UnitAddCircle, ℂ))

lemma fourierToLp_coeFn (ν : Measure UnitAddCircle) [IsFiniteMeasure ν] (k : ℤ) :
    fourierToLp ν k =ᵐ[ν] fun x ↦ fourier k x :=
  ContinuousMap.coeFn_toLp ν (fourier k)

lemma span_fourierToLp_closure_eq_top (ν : Measure UnitAddCircle) [IsFiniteMeasure ν] :
    (Submodule.span ℂ (Set.range (fourierToLp ν))).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange ℂ ν ℂ
      (by norm_num : (2 : ℝ≥0∞) ≠ ∞)).topologicalClosure_map_submodule
        span_fourier_closure_eq_top
  rw [Submodule.map_span]
  unfold fourierToLp
  rw [Set.range_comp']
  simp only [ContinuousLinearMap.coe_coe]

lemma fourierShift_const_one (ν : Measure UnitAddCircle) [IsFiniteMeasure ν] (k : ℤ) :
    fourierShift ν k (Lp.const 2 ν 1) = fourierToLp ν k := by
  apply Lp.ext
  filter_upwards [fourierShift_coeFn ν k (Lp.const 2 ν 1),
      Lp.coeFn_const (p := 2) (μ := ν) (c := (1 : ℂ)),
      fourierToLp_coeFn ν k] with x hshift hone htoLp
  rw [hshift, hone, htoLp]
  simp

noncomputable def backwardOrbit (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) (n : ℕ) :
    Lp ℂ 2 ν :=
  fourierShift ν (-(n : ℤ)) x

@[simp]
lemma backwardOrbit_zero (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    backwardOrbit ν x 0 = x := by
  simp [backwardOrbit]

lemma backwardOrbit_succ (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) (n : ℕ) :
    backwardOrbit ν x (n + 1) = fourierShift ν (-1) (backwardOrbit ν x n) := by
  rw [backwardOrbit, backwardOrbit, ← fourierShift_add]
  congr 2
  push_cast
  ring

noncomputable def futureSubspace (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    Submodule ℂ (Lp ℂ 2 ν) :=
  (Submodule.span ℂ (Set.range (backwardOrbit ν x))).topologicalClosure

noncomputable def tailSubspace (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    Submodule ℂ (Lp ℂ 2 ν) :=
  (futureSubspace ν x).map
    ((fourierShiftLIE ν (-1)).toLinearEquiv :
      Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)

noncomputable instance tailSubspace_hasOrthogonalProjection
    (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    (tailSubspace ν x).HasOrthogonalProjection := by
  unfold tailSubspace futureSubspace
  infer_instance

lemma mem_futureSubspace_self (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    x ∈ futureSubspace ν x := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨0, backwardOrbit_zero ν x⟩

lemma fourierShift_neg_one_mem_futureSubspace (ν : Measure UnitAddCircle)
    (x y : Lp ℂ 2 ν) (hy : y ∈ futureSubspace ν x) :
    fourierShift ν (-1) y ∈ futureSubspace ν x := by
  let K := futureSubspace ν x
  let P : Submodule ℂ (Lp ℂ 2 ν) :=
    K.comap (fourierShift ν (-1)).toLinearMap
  have hP_closed : IsClosed (P : Set (Lp ℂ 2 ν)) := by
    exact (Submodule.isClosed_topologicalClosure
      (Submodule.span ℂ (Set.range (backwardOrbit ν x)))).preimage
        (fourierShift ν (-1)).continuous
  have hspan : Submodule.span ℂ (Set.range (backwardOrbit ν x)) ≤ P := by
    apply Submodule.span_le.2
    rintro y ⟨n, rfl⟩
    change fourierShift ν (-1) (backwardOrbit ν x n) ∈ K
    rw [← backwardOrbit_succ]
    change backwardOrbit ν x (n + 1) ∈ futureSubspace ν x
    unfold futureSubspace
    exact (Submodule.le_topologicalClosure
      (Submodule.span ℂ (Set.range (backwardOrbit ν x))))
        (Submodule.subset_span (Set.mem_range_self (n + 1)))
  have hKP : K ≤ P := by
    exact Submodule.topologicalClosure_minimal _ hspan hP_closed
  exact hKP hy

lemma tailSubspace_le_futureSubspace (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    tailSubspace ν x ≤ futureSubspace ν x := by
  intro y hy
  rw [tailSubspace] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact fourierShift_neg_one_mem_futureSubspace ν x z hz

noncomputable def wanderingVector (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    Lp ℂ 2 ν :=
  x - (tailSubspace ν x).starProjection x

lemma wanderingVector_mem_tail_orthogonal (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    wanderingVector ν x ∈ (tailSubspace ν x)ᗮ :=
  Submodule.sub_starProjection_mem_orthogonal x

lemma wanderingVector_mem_futureSubspace (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    wanderingVector ν x ∈ futureSubspace ν x := by
  exact (futureSubspace ν x).sub_mem (mem_futureSubspace_self ν x)
    (tailSubspace_le_futureSubspace ν x
      (Submodule.starProjection_apply_mem (tailSubspace ν x) x))

lemma futureSubspace_le_tail_sup_wandering (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    futureSubspace ν x ≤
      tailSubspace ν x ⊔ ℂ ∙ wanderingVector ν x := by
  let M := tailSubspace ν x
  let g := wanderingVector ν x
  let Q : Submodule ℂ (Lp ℂ 2 ν) := M ⊔ ℂ ∙ g
  change futureSubspace ν x ≤ Q
  have hM_Q : M ≤ Q := by
    dsimp only [Q]
    exact le_sup_left
  have hg_Q : g ∈ Q := by
    apply (show ℂ ∙ g ≤ Q by
      dsimp only [Q]
      exact le_sup_right)
    exact Submodule.mem_span_singleton_self g
  have hM_closed : IsClosed (M : Set (Lp ℂ 2 ν)) := by
    change IsClosed
      ((fourierShiftLIE ν (-1)) '' (futureSubspace ν x : Set (Lp ℂ 2 ν)))
    exact (fourierShiftLIE ν (-1)).toHomeomorph.isClosed_image.2
      (Submodule.isClosed_topologicalClosure
        (Submodule.span ℂ (Set.range (backwardOrbit ν x))))
  have hQ_closed : IsClosed (Q : Set (Lp ℂ 2 ν)) :=
    Submodule.isClosed_sup_finiteDimensional M (ℂ ∙ g) hM_closed
  unfold futureSubspace
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.2
    rintro y ⟨n, rfl⟩
    cases n with
    | zero =>
        rw [backwardOrbit_zero]
        have hp : M.starProjection x ∈ M :=
          Submodule.starProjection_apply_mem M x
        have hx : x = M.starProjection x + g := by
          dsimp only [M, g]
          unfold wanderingVector
          abel
        rw [hx]
        exact Q.add_mem (hM_Q hp) hg_Q
    | succ n =>
        rw [backwardOrbit_succ]
        apply hM_Q
        dsimp only [M, tailSubspace]
        exact Submodule.mem_map_of_mem
            (f := ((fourierShiftLIE ν (-1)).toLinearEquiv :
              Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν))
            ((Submodule.le_topologicalClosure
              (Submodule.span ℂ (Set.range (backwardOrbit ν x))))
                (Submodule.subset_span ⟨n, rfl⟩))
  · exact hQ_closed

lemma mem_tailSubspace_of_mem_future_inner_wandering_eq_zero
    (ν : Measure UnitAddCircle) (x y : Lp ℂ 2 ν)
    (hyK : y ∈ futureSubspace ν x)
    (hyg : ⟪wanderingVector ν x, y⟫_ℂ = 0) :
    y ∈ tailSubspace ν x := by
  have hyQ := futureSubspace_le_tail_sup_wandering ν x hyK
  rw [Submodule.mem_sup] at hyQ
  obtain ⟨m, hm, z, hz, hmz⟩ := hyQ
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hg_inner_m : ⟪wanderingVector ν x, m⟫_ℂ = 0 :=
    Submodule.inner_left_of_mem_orthogonal hm
      (wanderingVector_mem_tail_orthogonal ν x)
  have hc : c = 0 ∨ wanderingVector ν x = 0 := by
    have hcg :
        ⟪wanderingVector ν x, c • wanderingVector ν x⟫_ℂ = 0 := calc
      ⟪wanderingVector ν x, c • wanderingVector ν x⟫_ℂ
          = ⟪wanderingVector ν x, y - m⟫_ℂ := by rw [← hmz]; abel_nf
      _ = 0 := by rw [inner_sub_right, hyg, hg_inner_m, sub_zero]
    by_cases hc : c = 0
    · exact Or.inl hc
    · refine Or.inr ((inner_self_eq_zero (𝕜 := ℂ)).mp ?_)
      rw [inner_smul_right, mul_eq_zero] at hcg
      exact hcg.resolve_left hc
  rcases hc with rfl | hg
  · have hmy : m = y := by simpa using hmz
    exact hmy ▸ hm
  · have hmy : m = y := by simpa [hg] using hmz
    exact hmy ▸ hm

lemma const_one_mem_tail_orthogonal_of_positive_coefficients
    (ν : Measure UnitAddCircle) [IsFiniteMeasure ν] (x : Lp ℂ 2 ν)
    (hpos : ∀ n : ℕ, 1 ≤ n → ⟪x, fourierToLp ν n⟫_ℂ = 0) :
    Lp.const 2 ν 1 ∈ (tailSubspace ν x)ᗮ := by
  let e : Lp ℂ 2 ν := Lp.const 2 ν 1
  let N : Submodule ℂ (Lp ℂ 2 ν) :=
    { carrier := {z | ⟪fourierShift ν (-1) z, e⟫_ℂ = 0}
      zero_mem' := by simp
      add_mem' := by
        intro a b ha hb
        change ⟪fourierShift ν (-1) a, e⟫_ℂ = 0 at ha
        change ⟪fourierShift ν (-1) b, e⟫_ℂ = 0 at hb
        change ⟪fourierShift ν (-1) (a + b), e⟫_ℂ = 0
        rw [map_add, inner_add_left, ha, hb, add_zero]
      smul_mem' := by
        intro c a ha
        change ⟪fourierShift ν (-1) a, e⟫_ℂ = 0 at ha
        change ⟪fourierShift ν (-1) (c • a), e⟫_ℂ = 0
        rw [map_smul, inner_smul_left, ha, mul_zero] }
  have hN_closed : IsClosed (N : Set (Lp ℂ 2 ν)) := by
    exact isClosed_eq ((fourierShift ν (-1)).continuous.inner continuous_const)
      continuous_const
  have hspanN : Submodule.span ℂ (Set.range (backwardOrbit ν x)) ≤ N := by
    apply Submodule.span_le.2
    rintro z ⟨n, rfl⟩
    change ⟪fourierShift ν (-1) (backwardOrbit ν x n), e⟫_ℂ = 0
    rw [← backwardOrbit_succ]
    rw [backwardOrbit]
    rw [inner_fourierShift_neg_left]
    rw [fourierShift_const_one]
    exact hpos (n + 1) (by omega)
  have hKN : futureSubspace ν x ≤ N :=
    Submodule.topologicalClosure_minimal _ hspanN hN_closed
  rw [Submodule.mem_orthogonal]
  intro y hy
  rw [tailSubspace] at hy
  obtain ⟨z, hz, rfl⟩ := hy
  exact hKN hz

lemma fourierShift_neg_nat_mem_futureSubspace (ν : Measure UnitAddCircle)
    (x y : Lp ℂ 2 ν) (hy : y ∈ futureSubspace ν x) (n : ℕ) :
    fourierShift ν (-(n : ℤ)) y ∈ futureSubspace ν x := by
  induction n with
  | zero => simpa using hy
  | succ n ih =>
      rw [show -(↑(n + 1) : ℤ) = -1 + -(n : ℤ) by push_cast; ring]
      rw [fourierShift_add]
      exact fourierShift_neg_one_mem_futureSubspace ν x _ ih

noncomputable def unitaryPart (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    Submodule ℂ (Lp ℂ 2 ν) :=
  ⨅ n : ℕ,
    (futureSubspace ν x).map
      ((fourierShiftLIE ν (-(n : ℤ))).toLinearEquiv :
        Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)

lemma unitaryPart_le_tailSubspace (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    unitaryPart ν x ≤ tailSubspace ν x := by
  intro y hy
  have hy₁ := (show unitaryPart ν x ≤
      (futureSubspace ν x).map
        ((fourierShiftLIE ν (-(1 : ℤ))).toLinearEquiv :
          Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν) from
      iInf_le (fun n : ℕ ↦
        (futureSubspace ν x).map
          ((fourierShiftLIE ν (-(n : ℤ))).toLinearEquiv :
            Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) 1) hy
  simpa [tailSubspace] using hy₁

lemma fourierShift_mem_future_of_mem_unitaryPart
    (ν : Measure UnitAddCircle) (x y : Lp ℂ 2 ν)
    (hy : y ∈ unitaryPart ν x) (k : ℤ) :
    fourierShift ν k y ∈ futureSubspace ν x := by
  cases k with
  | ofNat n =>
      have hyn := (show unitaryPart ν x ≤
          (futureSubspace ν x).map
            ((fourierShiftLIE ν (-(n : ℤ))).toLinearEquiv :
              Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν) from
          iInf_le (fun m : ℕ ↦
            (futureSubspace ν x).map
              ((fourierShiftLIE ν (-(m : ℤ))).toLinearEquiv :
                Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) n) hy
      obtain ⟨z, hz, hzy⟩ := hyn
      change fourierShift ν (n : ℤ) y ∈ futureSubspace ν x
      rw [← hzy]
      change fourierShift ν (n : ℤ)
        (fourierShift ν (-(n : ℤ)) z) ∈ futureSubspace ν x
      rw [← fourierShift_add, add_neg_cancel, fourierShift_zero]
      exact hz
  | negSucc n =>
      change fourierShift ν (-((n : ℤ) + 1)) y ∈ futureSubspace ν x
      have hyK : y ∈ futureSubspace ν x :=
        ((unitaryPart_le_tailSubspace ν x).trans
          (tailSubspace_le_futureSubspace ν x)) hy
      simpa only [Nat.cast_add, Nat.cast_one] using
        fourierShift_neg_nat_mem_futureSubspace ν x y hyK (n + 1)

lemma fourierShift_mem_tail_of_mem_unitaryPart
    (ν : Measure UnitAddCircle) (x y : Lp ℂ 2 ν)
    (hy : y ∈ unitaryPart ν x) (k : ℤ) :
    fourierShift ν k y ∈ tailSubspace ν x := by
  have hz : fourierShift ν (k + 1) y ∈ futureSubspace ν x :=
    fourierShift_mem_future_of_mem_unitaryPart ν x y hy (k + 1)
  have hm := Submodule.mem_map_of_mem
    (f := ((fourierShiftLIE ν (-1)).toLinearEquiv :
      Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν)) hz
  have hindex : (-1 : ℤ) + (k + 1) = k := by ring
  change fourierShift ν (-1) (fourierShift ν (k + 1) y) ∈
    tailSubspace ν x at hm
  rw [← fourierShift_add, hindex] at hm
  exact hm

lemma unitaryPart_eq_bot_of_positive_coefficients
    (ν : Measure UnitAddCircle) [IsFiniteMeasure ν] (x : Lp ℂ 2 ν)
    (hpos : ∀ n : ℕ, 1 ≤ n → ⟪x, fourierToLp ν n⟫_ℂ = 0) :
    unitaryPart ν x = ⊥ := by
  apply (Submodule.eq_bot_iff (unitaryPart ν x)).2
  intro y hy
  have he : Lp.const 2 ν 1 ∈ (tailSubspace ν x)ᗮ :=
    const_one_mem_tail_orthogonal_of_positive_coefficients ν x hpos
  have hfourier : ∀ k : ℤ, ⟪fourierToLp ν k, y⟫_ℂ = 0 := by
    intro k
    rw [← fourierShift_const_one ν k]
    rw [show k = -(-k) by simp]
    rw [inner_fourierShift_neg_left ν (-k)]
    exact Submodule.inner_left_of_mem_orthogonal
      (fourierShift_mem_tail_of_mem_unitaryPart ν x y hy (-k)) he
  have hdense :
      Dense ((Submodule.span ℂ (Set.range (fourierToLp ν))) : Set (Lp ℂ 2 ν)) :=
    Submodule.dense_iff_topologicalClosure_eq_top.2
      (span_fourierToLp_closure_eq_top ν)
  exact hdense.eq_zero_of_inner_right ℂ fun v hv ↦
    Submodule.span_induction
      (fun v hv ↦ by obtain ⟨k, rfl⟩ := hv; exact hfourier k)
      (by simp)
      (fun a b _ _ ha hb ↦ by
        rw [inner_add_left, ha, hb, add_zero])
      (fun c a _ ha ↦ by
        rw [inner_smul_left, ha, mul_zero])
      hv

noncomputable def wanderingSubspace (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    Submodule ℂ (Lp ℂ 2 ν) :=
  (Submodule.span ℂ
    (Set.range (backwardOrbit ν (wanderingVector ν x)))).topologicalClosure

noncomputable instance wanderingSubspace_hasOrthogonalProjection
    (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    (wanderingSubspace ν x).HasOrthogonalProjection := by
  unfold wanderingSubspace
  infer_instance

lemma wanderingVector_mem_wanderingSubspace
    (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    wanderingVector ν x ∈ wanderingSubspace ν x := by
  apply Submodule.le_topologicalClosure
  apply Submodule.subset_span
  exact ⟨0, backwardOrbit_zero ν (wanderingVector ν x)⟩

lemma wanderingSubspace_le_futureSubspace (ν : Measure UnitAddCircle) (x : Lp ℂ 2 ν) :
    wanderingSubspace ν x ≤ futureSubspace ν x := by
  apply Submodule.topologicalClosure_minimal
  · apply Submodule.span_le.2
    rintro y ⟨n, rfl⟩
    exact fourierShift_neg_nat_mem_futureSubspace ν x (wanderingVector ν x)
      (wanderingVector_mem_futureSubspace ν x) n
  · exact Submodule.isClosed_topologicalClosure _

lemma fourierShift_neg_one_mem_wanderingSubspace
    (ν : Measure UnitAddCircle) (x y : Lp ℂ 2 ν)
    (hy : y ∈ wanderingSubspace ν x) :
    fourierShift ν (-1) y ∈ wanderingSubspace ν x := by
  let G := wanderingSubspace ν x
  let P : Submodule ℂ (Lp ℂ 2 ν) :=
    G.comap (fourierShift ν (-1)).toLinearMap
  have hP_closed : IsClosed (P : Set (Lp ℂ 2 ν)) := by
    exact (Submodule.isClosed_topologicalClosure
      (Submodule.span ℂ
        (Set.range (backwardOrbit ν (wanderingVector ν x))))).preimage
          (fourierShift ν (-1)).continuous
  have hspan : Submodule.span ℂ
      (Set.range (backwardOrbit ν (wanderingVector ν x))) ≤ P := by
    apply Submodule.span_le.2
    rintro z ⟨n, rfl⟩
    change fourierShift ν (-1)
      (backwardOrbit ν (wanderingVector ν x) n) ∈ G
    rw [← backwardOrbit_succ]
    change backwardOrbit ν (wanderingVector ν x) (n + 1) ∈
      wanderingSubspace ν x
    unfold wanderingSubspace
    exact (Submodule.le_topologicalClosure
      (Submodule.span ℂ
        (Set.range (backwardOrbit ν (wanderingVector ν x)))))
          (Submodule.subset_span (Set.mem_range_self (n + 1)))
  exact (Submodule.topologicalClosure_minimal _ hspan hP_closed) hy

lemma fourierShift_one_mem_future_of_mem_tail
    (ν : Measure UnitAddCircle) (x y : Lp ℂ 2 ν)
    (hy : y ∈ tailSubspace ν x) :
    fourierShift ν 1 y ∈ futureSubspace ν x := by
  rw [tailSubspace] at hy
  obtain ⟨z, hz, hzy⟩ := hy
  rw [← hzy]
  change fourierShift ν 1 (fourierShift ν (-1) z) ∈ futureSubspace ν x
  rw [← fourierShift_add, add_neg_cancel, fourierShift_zero]
  exact hz

lemma fourierShift_one_mem_wandering_orthogonal
    (ν : Measure UnitAddCircle) (x y : Lp ℂ 2 ν)
    (hy : y ∈ (wanderingSubspace ν x)ᗮ) :
    fourierShift ν 1 y ∈ (wanderingSubspace ν x)ᗮ := by
  rw [Submodule.mem_orthogonal]
  intro z hz
  calc
    ⟪z, fourierShift ν 1 y⟫_ℂ =
        ⟪fourierShiftLIE ν (-1) z,
          fourierShiftLIE ν (-1) (fourierShift ν 1 y)⟫_ℂ :=
      ((fourierShiftLIE ν (-1)).inner_map_map z (fourierShift ν 1 y)).symm
    _ = ⟪fourierShift ν (-1) z, y⟫_ℂ := by
      simp only [fourierShiftLIE_apply]
      rw [← fourierShift_add, neg_add_cancel, fourierShift_zero]
    _ = 0 := hy _ (fourierShift_neg_one_mem_wanderingSubspace ν x z hz)

lemma mem_unitaryPart_of_mem_future_wandering_orthogonal
    (ν : Measure UnitAddCircle) (x y : Lp ℂ 2 ν)
    (hyK : y ∈ futureSubspace ν x)
    (hyG : y ∈ (wanderingSubspace ν x)ᗮ) :
    y ∈ unitaryPart ν x := by
  have hiterate : ∀ n : ℕ,
      fourierShift ν n y ∈ futureSubspace ν x ∧
        fourierShift ν n y ∈ (wanderingSubspace ν x)ᗮ := by
    intro n
    induction n with
    | zero => simpa using And.intro hyK hyG
    | succ n ih =>
        have hinner :
            ⟪wanderingVector ν x, fourierShift ν n y⟫_ℂ = 0 :=
          Submodule.inner_right_of_mem_orthogonal
            (wanderingVector_mem_wanderingSubspace ν x)
            ih.2
        have htail := mem_tailSubspace_of_mem_future_inner_wandering_eq_zero
          ν x (fourierShift ν n y) ih.1 hinner
        constructor
        · have hs :=
            fourierShift_one_mem_future_of_mem_tail ν x _ htail
          rw [← fourierShift_add] at hs
          simpa [Nat.cast_add, Nat.cast_one, add_comm] using hs
        · have hs :=
            fourierShift_one_mem_wandering_orthogonal ν x _ ih.2
          rw [← fourierShift_add] at hs
          simpa [Nat.cast_add, Nat.cast_one, add_comm] using hs
  rw [unitaryPart, Submodule.mem_iInf]
  intro n
  refine ⟨fourierShift ν n y, (hiterate n).1, ?_⟩
  change fourierShift ν (-(n : ℤ)) (fourierShift ν (n : ℤ) y) = y
  rw [← fourierShift_add, neg_add_cancel, fourierShift_zero]

lemma futureSubspace_eq_wanderingSubspace_of_positive_coefficients
    (ν : Measure UnitAddCircle) [IsFiniteMeasure ν] (x : Lp ℂ 2 ν)
    (hpos : ∀ n : ℕ, 1 ≤ n → ⟪x, fourierToLp ν n⟫_ℂ = 0) :
    futureSubspace ν x = wanderingSubspace ν x := by
  apply le_antisymm
  · intro y hyK
    let G := wanderingSubspace ν x
    let q := G.starProjection y
    have hqG : q ∈ G := Submodule.starProjection_apply_mem G y
    have hqK : q ∈ futureSubspace ν x :=
      wanderingSubspace_le_futureSubspace ν x hqG
    have hdiffK : y - q ∈ futureSubspace ν x :=
      (futureSubspace ν x).sub_mem hyK hqK
    have hdiffG : y - q ∈ Gᗮ :=
      Submodule.sub_starProjection_mem_orthogonal y
    have hdiffU : y - q ∈ unitaryPart ν x :=
      mem_unitaryPart_of_mem_future_wandering_orthogonal ν x (y - q) hdiffK hdiffG
    have hdiff : y - q = 0 := by
      have := hdiffU
      rw [unitaryPart_eq_bot_of_positive_coefficients ν x hpos] at this
      simpa using this
    have : y = q := sub_eq_zero.mp hdiff
    exact this.symm ▸ hqG
  · exact wanderingSubspace_le_futureSubspace ν x

lemma wanderingVector_ae_ne_zero_of_positive_coefficients
    (ν : Measure UnitAddCircle) [IsFiniteMeasure ν] (x : Lp ℂ 2 ν)
    (hx : ∀ᵐ z ∂ν, x z ≠ 0)
    (hpos : ∀ n : ℕ, 1 ≤ n → ⟪x, fourierToLp ν n⟫_ℂ = 0) :
    ∀ᵐ z ∂ν, wanderingVector ν x z ≠ 0 := by
  let g := wanderingVector ν x
  let A : Set UnitAddCircle := {z | g z = 0}
  have hA : MeasurableSet A := by
    exact (Lp.stronglyMeasurable g).measurable (measurableSet_singleton 0)
  let R : Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 (ν.restrict A) :=
    LpToLpRestrictCLM UnitAddCircle ℂ ℂ ν 2 A
  have horbit : ∀ n : ℕ, backwardOrbit ν g n ∈ R.ker := by
    intro n
    rw [LinearMap.mem_ker]
    rw [Lp.eq_zero_iff_ae_eq_zero]
    filter_upwards [LpToLpRestrictCLM_coeFn ℂ A (backwardOrbit ν g n),
        (fourierShift_coeFn ν (-(n : ℤ)) g).restrict,
        ae_restrict_mem hA] with z hR hshift hzA
    change (R (backwardOrbit ν g n)) z = (0 : ℂ)
    have hR' : (R (backwardOrbit ν g n)) z =
        backwardOrbit ν g n z := by
      simpa [R] using hR
    rw [hR', backwardOrbit, hshift]
    simp [A] at hzA
    rw [hzA, mul_zero]
  have hGker : wanderingSubspace ν x ≤ R.ker := by
    apply Submodule.topologicalClosure_minimal
    · apply Submodule.span_le.2
      rintro y ⟨n, rfl⟩
      exact horbit n
    · exact R.isClosed_ker
  have hxG : x ∈ wanderingSubspace ν x := by
    rw [← futureSubspace_eq_wanderingSubspace_of_positive_coefficients ν x hpos]
    exact mem_futureSubspace_self ν x
  have hxR : R x = 0 := by
    exact LinearMap.mem_ker.mp (hGker hxG)
  have hxA_restrict : ∀ᵐ z ∂ν.restrict A, x z = 0 := by
    have hRcoe := LpToLpRestrictCLM_coeFn ℂ A x
    rw [hxR] at hRcoe
    exact hRcoe.symm.trans (Lp.coeFn_zero ℂ 2 (ν.restrict A))
  have hxA : ∀ᵐ z ∂ν, z ∈ A → x z = 0 :=
    (ae_restrict_iff' hA).mp hxA_restrict
  filter_upwards [hx, hxA] with z hxz hxAz
  intro hgz
  exact hxz (hxAz hgz)

lemma inner_wandering_backwardOrbit_eq_zero (ν : Measure UnitAddCircle)
    (x : Lp ℂ 2 ν) (n : ℕ) (hn : 1 ≤ n) :
    ⟪wanderingVector ν x, backwardOrbit ν (wanderingVector ν x) n⟫_ℂ = 0 := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hn
  rw [Nat.add_comm 1 m]
  rw [backwardOrbit_succ]
  have hm : fourierShift ν (-1)
      (backwardOrbit ν (wanderingVector ν x) m) ∈ tailSubspace ν x := by
    rw [tailSubspace]
    exact Submodule.mem_map_of_mem
      (f := ((fourierShiftLIE ν (-1)).toLinearEquiv :
        Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν))
      (fourierShift_neg_nat_mem_futureSubspace ν x (wanderingVector ν x)
        (wanderingVector_mem_futureSubspace ν x) m)
  exact Submodule.inner_left_of_mem_orthogonal
    hm
    (wanderingVector_mem_tail_orthogonal ν x)

lemma inner_wandering_fourierShift_eq_zero (ν : Measure UnitAddCircle)
    (x : Lp ℂ 2 ν) (k : ℤ) (hk : k ≠ 0) :
    ⟪wanderingVector ν x, fourierShift ν k (wanderingVector ν x)⟫_ℂ = 0 := by
  cases k with
  | ofNat n =>
      have hn : 1 ≤ n := by
        simpa using (Nat.one_le_iff_ne_zero.2 (by simpa using hk))
      rw [inner_eq_zero_symm]
      calc
        ⟪fourierShift ν (Int.ofNat n) (wanderingVector ν x),
            wanderingVector ν x⟫_ℂ =
            ⟪wanderingVector ν x,
              fourierShift ν (-(n : ℤ)) (wanderingVector ν x)⟫_ℂ := by
          simpa using inner_fourierShift_neg_left ν (-(n : ℤ))
            (wanderingVector ν x) (wanderingVector ν x)
        _ = 0 := by
          simpa [backwardOrbit] using
            inner_wandering_backwardOrbit_eq_zero ν x n hn
  | negSucc n =>
      change ⟪wanderingVector ν x,
        fourierShift ν (-((n : ℤ) + 1)) (wanderingVector ν x)⟫_ℂ = 0
      simpa [backwardOrbit, Nat.cast_add, Nat.cast_one] using
        inner_wandering_backwardOrbit_eq_zero ν x (n + 1) (by omega)

noncomputable def spectralDensity {ν : Measure UnitAddCircle}
    (g : Lp ℂ 2 ν) (z : UnitAddCircle) : ℝ≥0∞ :=
  ENNReal.ofReal (‖g z‖ ^ 2)

lemma spectralDensity_measurable {ν : Measure UnitAddCircle} (g : Lp ℂ 2 ν) :
    Measurable (spectralDensity g) := by
  exact ((Lp.stronglyMeasurable g).norm.measurable.pow_const 2).ennreal_ofReal

noncomputable def spectralMeasure (ν : Measure UnitAddCircle) (g : Lp ℂ 2 ν) :
    Measure UnitAddCircle :=
  ν.withDensity (spectralDensity g)

lemma spectralMeasure_isFinite (ν : Measure UnitAddCircle) (g : Lp ℂ 2 ν) :
    IsFiniteMeasure (spectralMeasure ν g) := by
  exact isFiniteMeasure_withDensity_ofReal
    ((Lp.memLp g).integrable_norm_pow (by norm_num)).hasFiniteIntegral

noncomputable def spectralMass {ν : Measure UnitAddCircle} (g : Lp ℂ 2 ν) : ℝ≥0 :=
  ⟨‖g‖ ^ 2, sq_nonneg ‖g‖⟩

lemma integral_fourier_spectralMeasure (ν : Measure UnitAddCircle)
    (g : Lp ℂ 2 ν) (k : ℤ) :
    ∫ z, fourier k z ∂spectralMeasure ν g =
      ⟪g, fourierShift ν k g⟫_ℂ := by
  rw [spectralMeasure,
    integral_withDensity_eq_integral_toReal_smul (spectralDensity_measurable g)
      (Eventually.of_forall fun _ ↦ by simp [spectralDensity])]
  rw [L2.inner_def]
  apply integral_congr_ae
  filter_upwards [fourierShift_coeFn ν k g] with z hz
  rw [hz]
  simp only [spectralDensity, ENNReal.toReal_ofReal (sq_nonneg ‖g z‖)]
  rw [Complex.real_smul, RCLike.inner_apply']
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
  ring

lemma integral_fourier_haar (k : ℤ) :
    ∫ z : UnitAddCircle, fourier k z ∂AddCircle.haarAddCircle =
      if k = 0 then 1 else 0 := by
  have h := (orthonormal_iff_ite.mp
    (orthonormal_fourier (T := (1 : ℝ)))) 0 k
  rw [ContinuousMap.inner_toLp] at h
  simpa [fourier_zero, eq_comm] using h

noncomputable def continuousIntegralCLM (ρ : Measure UnitAddCircle)
    [IsFiniteMeasure ρ] : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
  (innerSL ℂ
    (ContinuousMap.toLp 2 ρ ℂ (1 : C(UnitAddCircle, ℂ)))).comp
      (ContinuousMap.toLp 2 ρ ℂ)

@[simp]
lemma continuousIntegralCLM_apply (ρ : Measure UnitAddCircle)
    [IsFiniteMeasure ρ] (f : C(UnitAddCircle, ℂ)) :
    continuousIntegralCLM ρ f = ∫ z, f z ∂ρ := by
  rw [continuousIntegralCLM, ContinuousLinearMap.comp_apply,
    innerSL_apply_apply, ContinuousMap.inner_toLp]
  simp

lemma spectralMeasure_eq_smul_haar (ν : Measure UnitAddCircle)
    (g : Lp ℂ 2 ν)
    (hcoeff : ∀ k : ℤ, k ≠ 0 → ⟪g, fourierShift ν k g⟫_ℂ = 0) :
    spectralMeasure ν g = spectralMass g • AddCircle.haarAddCircle := by
  let ρ : Measure UnitAddCircle := spectralMeasure ν g
  let η : Measure UnitAddCircle :=
    spectralMass g • (AddCircle.haarAddCircle : Measure UnitAddCircle)
  letI : IsFiniteMeasure ρ := spectralMeasure_isFinite ν g
  letI : IsFiniteMeasure η := by infer_instance
  let D : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
    continuousIntegralCLM ρ - continuousIntegralCLM η
  have hfourier : ∀ k : ℤ,
      (fourier k : C(UnitAddCircle, ℂ)) ∈ D.ker := by
    intro k
    rw [LinearMap.mem_ker]
    change continuousIntegralCLM ρ (fourier k) -
      continuousIntegralCLM η (fourier k) = 0
    rw [continuousIntegralCLM_apply, continuousIntegralCLM_apply]
    rw [show ∫ z, fourier k z ∂ρ =
        ⟪g, fourierShift ν k g⟫_ℂ by
      exact integral_fourier_spectralMeasure ν g k]
    rw [integral_smul_nnreal_measure, integral_fourier_haar]
    by_cases hk : k = 0
    · subst k
      have hmass : (spectralMass g : ℝ) = ‖g‖ ^ 2 := rfl
      simp only [fourierShift_zero, inner_self_eq_norm_sq_to_K, if_pos,
        NNReal.smul_def, Complex.real_smul, mul_one]
      rw [hmass]
      push_cast
      exact sub_self ((‖g‖ : ℂ) ^ 2)
    · rw [if_neg hk, hcoeff k hk]
      simp
  have hspan : Submodule.span ℂ
      (Set.range (fun k : ℤ ↦ (fourier k : C(UnitAddCircle, ℂ)))) ≤
      D.ker := by
    apply Submodule.span_le.2
    rintro f ⟨k, rfl⟩
    exact hfourier k
  have hker : D.ker = ⊤ := by
    apply top_unique
    rw [← span_fourier_closure_eq_top]
    exact Submodule.topologicalClosure_minimal _ hspan D.isClosed_ker
  have hall : ∀ f : C(UnitAddCircle, ℂ),
      ∫ z, f z ∂ρ = ∫ z, f z ∂η := by
    intro f
    have hf : f ∈ D.ker := by rw [hker]; trivial
    rw [LinearMap.mem_ker] at hf
    change continuousIntegralCLM ρ f - continuousIntegralCLM η f = 0 at hf
    simpa using sub_eq_zero.mp hf
  change ρ = η
  apply ext_of_forall_integral_eq_of_IsFiniteMeasure
  intro f
  let fc : C(UnitAddCircle, ℂ) :=
    ⟨fun z ↦ (f z : ℂ), Complex.continuous_ofReal.comp f.continuous⟩
  have hfc := hall fc
  change (∫ z, (f z : ℂ) ∂ρ) = ∫ z, (f z : ℂ) ∂η at hfc
  rw [integral_complex_ofReal, integral_complex_ofReal] at hfc
  exact Complex.ofReal_injective hfc

lemma measure_absolutelyContinuous_spectralMeasure
    (ν : Measure UnitAddCircle) (g : Lp ℂ 2 ν)
    (hg : ∀ᵐ z ∂ν, g z ≠ 0) :
    ν ≪ spectralMeasure ν g := by
  apply withDensity_absolutelyContinuous'
  · exact (spectralDensity_measurable g).aemeasurable
  · filter_upwards [hg] with z hz
    simp [spectralDensity, hz]

lemma measure_absolutelyContinuous_haar_of_wandering
    (ν : Measure UnitAddCircle) [IsFiniteMeasure ν] (x : Lp ℂ 2 ν)
    (hx : ∀ᵐ z ∂ν, x z ≠ 0)
    (hpos : ∀ n : ℕ, 1 ≤ n → ⟪x, fourierToLp ν n⟫_ℂ = 0) :
    ν ≪ AddCircle.haarAddCircle := by
  let g := wanderingVector ν x
  have hg : ∀ᵐ z ∂ν, g z ≠ 0 :=
    wanderingVector_ae_ne_zero_of_positive_coefficients ν x hx hpos
  have hνg : ν ≪ spectralMeasure ν g :=
    measure_absolutelyContinuous_spectralMeasure ν g hg
  have hρ :
      spectralMeasure ν g = spectralMass g • AddCircle.haarAddCircle :=
    spectralMeasure_eq_smul_haar ν g fun k hk ↦
      inner_wandering_fourierShift_eq_zero ν x k hk
  have hsmul :
      spectralMass g • (AddCircle.haarAddCircle : Measure UnitAddCircle) ≪
        (AddCircle.haarAddCircle : Measure UnitAddCircle) :=
    Measure.smul_absolutelyContinuous
  have hρhaar :
      spectralMeasure ν g ≪ AddCircle.haarAddCircle := by
    simpa [hρ] using hsmul
  exact hνg.trans hρhaar

theorem riesz_brothers_theorem (μ : ComplexMeasure UnitAddCircle)
    (hμ : ∀ n : ℕ, 1 ≤ n →
      ∫ᵛ z, fourier n z ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = 0) :
    μ ≪ᵥ AddCircle.haarAddCircle.toENNRealVectorMeasure := by
  letI : IsFiniteMeasure μ.variation := complexVariation_isFinite μ
  let x := representingVector μ
  have hx : ∀ᵐ z ∂μ.variation, x z ≠ 0 :=
    representingVector_ae_ne_zero μ
  have hpos :
      ∀ n : ℕ, 1 ≤ n → ⟪x, fourierToLp μ.variation n⟫_ℂ = 0 := by
    intro n hn
    rw [inner_representingVector]
    calc
      ∫ᵛ z, fourierToLp μ.variation n z
          ∂[ContinuousLinearMap.mul ℝ ℂ; μ] =
          ∫ᵛ z, fourier n z
            ∂[ContinuousLinearMap.mul ℝ ℂ; μ] := by
        apply VectorMeasure.integral_congr_ae
        exact fourierToLp_coeFn μ.variation n
      _ = 0 := hμ n hn
  have hvar :
      μ.variation ≪ AddCircle.haarAddCircle :=
    measure_absolutelyContinuous_haar_of_wandering μ.variation x hx hpos
  apply (VectorMeasure.absolutelyContinuous μ).trans
  apply VectorMeasure.AbsolutelyContinuous.mk
  intro s hs hhaar
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs] at hhaar
  change μ.variation.toENNRealVectorMeasure s = 0
  rw [Measure.toENNRealVectorMeasure_apply_measurable hs]
  exact hvar hhaar

end Submission.Helpers
