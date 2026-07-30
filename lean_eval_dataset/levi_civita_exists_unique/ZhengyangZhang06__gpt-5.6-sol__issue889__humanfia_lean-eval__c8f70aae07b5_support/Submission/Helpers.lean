import ChallengeDeps

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

namespace Submission.Helpers

noncomputable section

set_option backward.isDefEq.respectTransparency false

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

/-! ### The smooth metric, in the original topology of the tangent bundle

Using `inner` directly here creates a typeclass diamond: the norm induced by the
Riemannian metric is propositionally, but not definitionally, the pre-existing
norm on tangent fibers.  The witness in `IsContMDiffRiemannianBundle` is a
continuous bilinear form for the original topology, so all bundle operations
below use that witness and only rewrite to `inner` at the boundary.
-/

/-- A smooth representative of the Riemannian metric in the original tangent
bundle topology. -/
def metricTensorFamily :
    (x : M) → TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  Classical.choose
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := ∞) (F := E) (E := fun x : M ↦ TangentSpace I x))

/-- The value of the selected smooth metric at a point. -/
def metricTensor (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  metricTensorFamily x

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma metricTensor_contMDiff :
    ContMDiff I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E →L[ℝ] ℝ))) ∞
      (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E →L[ℝ] ℝ)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y →L[ℝ] ℝ)
        x (metricTensor (I := I) (E := E) x)) :=
  (Classical.choose_spec
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := ∞) (F := E) (E := fun x : M ↦ TangentSpace I x))).1

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma inner_eq_metricTensor (x : M) (v w : TangentSpace I x) :
    inner ℝ v w = metricTensor x v w :=
  (Classical.choose_spec
    (IsContMDiffRiemannianBundle.exists_contMDiff
      (IB := I) (n := ∞) (F := E) (E := fun x : M ↦ TangentSpace I x))).2 x v w

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma metricTensor_symm (x : M) (v w : TangentSpace I x) :
    metricTensor x v w = metricTensor x w v := by
  rw [← inner_eq_metricTensor, ← inner_eq_metricTensor, real_inner_comm]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma mdifferentiableAt_metricTensor {x : M}
    {X Z : (x : M) → TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hZ : MDiffAt (T% Z) x) :
    MDiffAt (fun y ↦ metricTensor y (X y) (Z y)) x := by
  have h : MDifferentiableAt I (I.prod (modelWithCornersSelf ℝ ℝ))
      (fun y : M ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (metricTensor y (X y) (Z y))) x := by
    apply MDifferentiableAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact metricTensor_contMDiff.mdifferentiableAt (by simp)
    · exact hX
    · exact hZ
  simp only [mdifferentiableAt_totalSpace] at h
  exact h.2

/-! ### The Koszul form -/

/-- The scalar-valued Koszul expression. The first and third vector fields are
tensorial arguments; the middle vector field is the section being differentiated. -/
def koszulAux (X Y Z : (x : M) → TangentSpace I x) (x : M) : ℝ :=
  d% (fun y ↦ metricTensor y (Y y) (Z y)) x (X x)
    + d% (fun y ↦ metricTensor y (X y) (Z y)) x (Y x)
    - d% (fun y ↦ metricTensor y (X y) (Y y)) x (Z x)
    - metricTensor x (X x) (mlieBracket I Y Z x)
    - metricTensor x (Y x) (mlieBracket I X Z x)
    + metricTensor x (Z x) (mlieBracket I X Y x)

omit [FiniteDimensional ℝ E] in
lemma tensorial_koszulAux_left {x : M}
    (Y : (x : M) → TangentSpace I x) (hY : MDiffAt (T% Y) x)
    (Z : (x : M) → TangentSpace I x) (hZ : MDiffAt (T% Z) x) :
    TensorialAt I E (fun X ↦ koszulAux X Y Z x) x where
  smul {f X} hf hX := by
    simp [koszulAux,
      mvfderiv_fun_mul hf (mdifferentiableAt_metricTensor hX hZ),
      mvfderiv_fun_mul hf (mdifferentiableAt_metricTensor hX hY),
      mlieBracket_smul_left hf hX]
    rw [metricTensor_symm x (Z x) (X x), metricTensor_symm x (Y x) (X x)]
    ring
  add {X X'} hX hX' := by
    simp [koszulAux,
      mvfderiv_fun_add (mdifferentiableAt_metricTensor hX hZ)
        (mdifferentiableAt_metricTensor hX' hZ),
      mvfderiv_fun_add (mdifferentiableAt_metricTensor hX hY)
        (mdifferentiableAt_metricTensor hX' hY),
      mlieBracket_add_left hX hX']
    ring

omit [FiniteDimensional ℝ E] in
lemma tensorial_koszulAux_right {x : M}
    (X : (x : M) → TangentSpace I x) (hX : MDiffAt (T% X) x)
    (Y : (x : M) → TangentSpace I x) (hY : MDiffAt (T% Y) x) :
    TensorialAt I E (fun Z ↦ koszulAux X Y Z x) x where
  smul {f Z} hf hZ := by
    simp [koszulAux,
      mvfderiv_fun_mul hf (mdifferentiableAt_metricTensor hY hZ),
      mvfderiv_fun_mul hf (mdifferentiableAt_metricTensor hX hZ),
      mlieBracket_smul_right hf hZ]
    ring
  add {Z Z'} hZ hZ' := by
    simp [koszulAux,
      mvfderiv_fun_add (mdifferentiableAt_metricTensor hY hZ)
        (mdifferentiableAt_metricTensor hY hZ'),
      mvfderiv_fun_add (mdifferentiableAt_metricTensor hX hZ)
        (mdifferentiableAt_metricTensor hX hZ'),
      mlieBracket_add_right hZ hZ']
    ring

/-- The Koszul expression as a continuous bilinear form in its two tensorial
arguments, scaled by `1 / 2`. -/
def koszulForm (Y : (x : M) → TangentSpace I x) (x : M)
    (hY : MDiffAt (T% Y) x) :
    TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ :=
  (2 : ℝ)⁻¹ • TensorialAt.mkHom₂ (fun X Z ↦ koszulAux X Y Z x) x
    (fun Z hZ ↦ tensorial_koszulAux_left Y hY Z hZ)
    (fun X hX ↦ tensorial_koszulAux_right X hX Y hY)

lemma koszulForm_apply {x : M} {X Y Z : (x : M) → TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    koszulForm Y x hY (X x) (Z x) = (2 : ℝ)⁻¹ * koszulAux X Y Z x := by
  simp only [koszulForm, smul_apply, smul_eq_mul]
  rw [TensorialAt.mkHom₂_apply
    (fun Z hZ ↦ tensorial_koszulAux_left Y hY Z hZ)
    (fun X hX ↦ tensorial_koszulAux_right X hX Y hY) hX hZ]

/-! ### Raising an index with the metric -/

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma metricTensor_injective (x : M) :
    Function.Injective (metricTensor (I := I) (E := E) x) := by
  intro v w hvw
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (x := v - w) (𝕜 := ℝ)).mp
  rw [inner_eq_metricTensor]
  simp [hvw]

omit [CompleteSpace E]
    [IsContMDiffRiemannianBundle I ∞ E (fun x : M ↦ TangentSpace I x)] in
lemma metric_finrank_eq (x : M) :
    Module.finrank ℝ (TangentSpace I x) =
      Module.finrank ℝ (TangentSpace I x →L[ℝ] ℝ) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  calc
    Module.finrank ℝ (TangentSpace I x)
        = Module.finrank ℝ (Module.Dual ℝ (TangentSpace I x)) :=
          Subspace.dual_finrank_eq.symm
    _ = Module.finrank ℝ (TangentSpace I x →L[ℝ] ℝ) :=
      (LinearMap.toContinuousLinearMap :
        Module.Dual ℝ (TangentSpace I x) ≃ₗ[ℝ]
          (TangentSpace I x →L[ℝ] ℝ)).finrank_eq

/-- The metric's flat map, upgraded to a continuous linear equivalence. -/
def metricEquiv (x : M) :
    TangentSpace I x ≃L[ℝ] (TangentSpace I x →L[ℝ] ℝ) := by
  letI : FiniteDimensional ℝ (TangentSpace I x) :=
    VectorBundle.finiteDimensional ℝ E (TangentSpace I) x
  exact (LinearEquiv.ofInjectiveOfFinrankEq (metricTensor x).toLinearMap
    (metricTensor_injective x) (metric_finrank_eq x)).toContinuousLinearEquiv

omit [CompleteSpace E] in
@[simp] lemma metricEquiv_apply (x : M) (v : TangentSpace I x) :
    metricEquiv x v = metricTensor x v := rfl

/-- The pointwise Levi-Civita operator supplied by the Koszul formula. For a
section not differentiable at the point, its irrelevant junk value is zero. -/
def koszulDerivative (Y : (x : M) → TangentSpace I x) (x : M) :
    TangentSpace I x →L[ℝ] TangentSpace I x := by
  classical
  exact if hY : MDiffAt (T% Y) x then
      (metricEquiv x).symm.toContinuousLinearMap.comp (koszulForm Y x hY)
    else 0

lemma metric_koszulDerivative {x : M}
    {X Y Z : (x : M) → TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) :
    metricTensor x (koszulDerivative Y x (X x)) (Z x) =
      (2 : ℝ)⁻¹ * koszulAux X Y Z x := by
  rw [koszulDerivative, dif_pos hY]
  change metricEquiv x ((metricEquiv x).symm (koszulForm Y x hY (X x))) (Z x) = _
  rw [ContinuousLinearEquiv.apply_symm_apply, koszulForm_apply hX hY hZ]

/-! ### Algebraic identities for the Koszul expression -/

omit [FiniteDimensional ℝ E] in
lemma koszulAux_add_middle {x : M}
    {X Y Y' Z : (x : M) → TangentSpace I x}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hY' : MDiffAt (T% Y') x) (hZ : MDiffAt (T% Z) x) :
    koszulAux X (Y + Y') Z x = koszulAux X Y Z x + koszulAux X Y' Z x := by
  simp [koszulAux,
    mvfderiv_fun_add (mdifferentiableAt_metricTensor hY hZ)
      (mdifferentiableAt_metricTensor hY' hZ),
    mvfderiv_fun_add (mdifferentiableAt_metricTensor hX hY)
      (mdifferentiableAt_metricTensor hX hY'),
    mlieBracket_add_left hY hY', mlieBracket_add_right hY hY']
  ring

omit [FiniteDimensional ℝ E] in
lemma koszulAux_smul_middle {x : M}
    {X Y Z : (x : M) → TangentSpace I x} {f : M → ℝ}
    (hX : MDiffAt (T% X) x) (hY : MDiffAt (T% Y) x)
    (hZ : MDiffAt (T% Z) x) (hf : MDiffAt f x) :
    koszulAux X (f • Y) Z x =
      f x * koszulAux X Y Z x
        + 2 * d% f x (X x) * metricTensor x (Y x) (Z x) := by
  simp [koszulAux,
    mvfderiv_fun_mul hf (mdifferentiableAt_metricTensor hY hZ),
    mvfderiv_fun_mul hf (mdifferentiableAt_metricTensor hX hY),
    mlieBracket_smul_left hf hY, mlieBracket_smul_right hf hY]
  rw [metricTensor_symm x (Z x) (Y x)]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma koszulAux_swap_middle {x : M}
    {X Y Z : (x : M) → TangentSpace I x} :
    koszulAux X Y Z x - koszulAux Y X Z x =
      2 * metricTensor x (mlieBracket I X Y x) (Z x) := by
  simp only [koszulAux]
  rw [mlieBracket_swap_apply (I := I) (V := Y) (W := X)]
  simp only [map_neg, metricTensor_symm]
  ring

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma koszulAux_metric {x : M}
    {X Y Z : (x : M) → TangentSpace I x} :
    koszulAux X Y Z x + koszulAux X Z Y x =
      2 * d% (fun y ↦ metricTensor y (Y y) (Z y)) x (X x) := by
  simp only [koszulAux]
  rw [mlieBracket_swap_apply (I := I) (V := Z) (W := Y)]
  simp only [map_neg, metricTensor_symm]
  ring

/-! ### The bundled algebraic connection -/

/-- The covariant derivative defined pointwise by the Koszul formula. -/
def koszulCovariantDerivative :
    CovariantDerivative I E (TangentSpace I (M := M)) where
  toFun := koszulDerivative
  isCovariantDerivativeOnUniv := by
    constructor
    · intro Y Y' x hY hY' _
      ext u
      apply metricTensor_injective x
      ext w
      let X : (x : M) → TangentSpace I x := FiberBundle.extend E u
      let Z : (x : M) → TangentSpace I x := FiberBundle.extend E w
      have hX : MDiffAt (T% X) x := FiberBundle.mdifferentiableAt_extend I E u
      have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E w
      rw [← show X x = u by simp [X], ← show Z x = w by simp [Z]]
      simp only [add_apply, map_add]
      rw [metric_koszulDerivative hX (mdifferentiableAt_add_section hY hY') hZ,
        metric_koszulDerivative hX hY hZ,
        metric_koszulDerivative hX hY' hZ,
        koszulAux_add_middle hX hY hY' hZ]
      ring
    · intro Y f x hY hf _
      ext u
      apply metricTensor_injective x
      ext w
      let X : (x : M) → TangentSpace I x := FiberBundle.extend E u
      let Z : (x : M) → TangentSpace I x := FiberBundle.extend E w
      have hX : MDiffAt (T% X) x := FiberBundle.mdifferentiableAt_extend I E u
      have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E w
      rw [← show X x = u by simp [X], ← show Z x = w by simp [Z]]
      simp only [add_apply, smul_apply,
        ContinuousLinearMap.smulRight_apply, smul_eq_mul, map_add, map_smul]
      rw [metric_koszulDerivative hX (hf.smul_section hY) hZ,
        metric_koszulDerivative hX hY hZ,
        koszulAux_smul_middle hX hY hZ hf]
      simp [X]
      ring

/-! ### Torsion, compatibility, and uniqueness -/

omit [CompleteSpace E]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] in
/-- Every tangent vector is the value of a globally smooth vector field. The
Hausdorff hypothesis lets us multiply the canonical local extension by a
smooth bump function supported in its smoothness neighborhood. -/
lemma exists_contMDiff_vectorField_eq [T2Space M]
    (x : M) (v : TangentSpace I x) :
    ∃ X : (x : M) → TangentSpace I x, CMDiff ∞ (T% X) ∧ X x = v := by
  obtain ⟨u, hu, hv⟩ :=
    FiberBundle.exists_contMDiffOn_extend (k := ∞) I E v
  have hxiu : x ∈ interior u := mem_interior_iff_mem_nhds.mpr hu
  have hui : interior u ∈ nhds x := isOpen_interior.mem_nhds hxiu
  obtain ⟨f, hfu, -⟩ :=
    ((SmoothBumpFunction.nhds_basis_support (I := I) (c := x) hui).mem_iff).mp Filter.univ_mem
  let X : (x : M) → TangentSpace I x := (f : M → ℝ) • FiberBundle.extend E v
  refine ⟨X, ?_, ?_⟩
  · exact f.contMDiff.contMDiffOn.smul_section_of_tsupport isOpen_interior hfu
      (hv.mono interior_subset)
  · simp [X]

lemma koszulCovariantDerivative_torsion :
    (koszulCovariantDerivative (I := I) (E := E) (M := M)).torsion = 0 := by
  rw [CovariantDerivative.torsion_eq_zero_iff]
  intro X Y x hX hY
  apply metricTensor_injective x
  ext w
  let Z : (x : M) → TangentSpace I x := FiberBundle.extend E w
  have hZ : MDiffAt (T% Z) x := FiberBundle.mdifferentiableAt_extend I E w
  rw [← show Z x = w by simp [Z]]
  simp only [map_sub, sub_apply]
  change metricTensor x (koszulDerivative Y x (X x)) (Z x) -
      metricTensor x (koszulDerivative X x (Y x)) (Z x) =
    metricTensor x (mlieBracket I X Y x) (Z x)
  rw [metric_koszulDerivative hX hY hZ,
    metric_koszulDerivative hY hX hZ, ← mul_sub, koszulAux_swap_middle]
  ring

lemma koszulCovariantDerivative_metricCompatible :
    LeanEval.Geometry.LeviCivita.IsMetricCompatible
      (koszulCovariantDerivative (I := I) (E := E) (M := M)) := by
  intro Y Z hY hZ x v
  let X : (x : M) → TangentSpace I x := FiberBundle.extend E v
  have hX : MDiffAt (T% X) x := FiberBundle.mdifferentiableAt_extend I E v
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZx : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  simp_rw [inner_eq_metricTensor]
  change d% (fun y ↦ metricTensor y (Y y) (Z y)) x v =
    metricTensor x (koszulDerivative Y x v) (Z x) +
      metricTensor x (Y x) (koszulDerivative Z x v)
  rw [← show X x = v by simp [X]]
  rw [metricTensor_symm x (Y x) (koszulDerivative Z x (X x)),
    metric_koszulDerivative hX hYx hZx,
    metric_koszulDerivative hX hZx hYx]
  rw [← mul_add, koszulAux_metric]
  ring

/-- Any torsion-free metric connection satisfies the Koszul identity. -/
lemma inner_cov_eq_koszul
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (ht : cov.torsion = 0)
    (hm : LeanEval.Geometry.LeviCivita.IsMetricCompatible cov)
    {X Y Z : (x : M) → TangentSpace I x}
    (hX : CMDiff ∞ (T% X)) (hY : CMDiff ∞ (T% Y))
    (hZ : CMDiff ∞ (T% Z)) (x : M) :
    inner ℝ (cov Y x (X x)) (Z x) = (2 : ℝ)⁻¹ * koszulAux X Y Z x := by
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZx : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  have hXY := (CovariantDerivative.torsion_eq_zero_iff cov).mp ht hXx hYx
  have hXZ := (CovariantDerivative.torsion_eq_zero_iff cov).mp ht hXx hZx
  have hYZ := (CovariantDerivative.torsion_eq_zero_iff cov).mp ht hYx hZx
  have h₁ := hm Y Z hY hZ x (X x)
  have h₂ := hm X Z hX hZ x (Y x)
  have h₃ := hm X Y hX hY x (Z x)
  simp only [koszulAux]
  simp_rw [← inner_eq_metricTensor]
  rw [h₁, h₂, h₃, ← hYZ, ← hXZ, ← hXY]
  simp only [inner_sub_right]
  rw [real_inner_comm (cov Z x (Y x)) (X x),
    real_inner_comm (cov Z x (X x)) (Y x),
    real_inner_comm (cov Y x (X x)) (Z x),
    real_inner_comm (Y x) (cov X x (Z x)),
    real_inner_comm (Z x) (cov X x (Y x))]
  ring

lemma koszulCovariantDerivative_unique [T2Space M]
    (cov : CovariantDerivative I E (TangentSpace I (M := M)))
    (ht : cov.torsion = 0)
    (hm : LeanEval.Geometry.LeviCivita.IsMetricCompatible cov) :
    LeanEval.Geometry.LeviCivita.SameOnSmooth
      (koszulCovariantDerivative (I := I) (E := E) (M := M)) cov := by
  intro Y hY x v
  obtain ⟨X, hX, hXv⟩ := exists_contMDiff_vectorField_eq x v
  apply metricTensor_injective x
  ext w
  obtain ⟨Z, hZ, hZw⟩ := exists_contMDiff_vectorField_eq x w
  have hXx : MDiffAt (T% X) x := (hX x).mdifferentiableAt (by simp)
  have hYx : MDiffAt (T% Y) x := (hY x).mdifferentiableAt (by simp)
  have hZx : MDiffAt (T% Z) x := (hZ x).mdifferentiableAt (by simp)
  change metricTensor x (koszulDerivative Y x v) w = metricTensor x (cov Y x v) w
  rw [← hXv, ← hZw, metric_koszulDerivative hXx hYx hZx]
  rw [← inner_eq_metricTensor, inner_cov_eq_koszul cov ht hm hX hY hZ x]

end

end Submission.Helpers
