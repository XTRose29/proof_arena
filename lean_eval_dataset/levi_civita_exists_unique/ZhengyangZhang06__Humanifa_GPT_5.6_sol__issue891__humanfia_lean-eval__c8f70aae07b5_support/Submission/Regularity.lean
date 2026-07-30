import Submission.Helpers

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative

namespace Submission.Helpers

noncomputable section

set_option backward.isDefEq.respectTransparency false
set_option synthInstance.maxHeartbeats 200000

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ∞ M]
  [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
  [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)]

omit [FiniteDimensional ℝ E] [CompleteSpace E]
    [RiemannianBundle (fun (x : M) ↦ TangentSpace I x)]
    [IsContMDiffRiemannianBundle I ∞ E (fun (x : M) ↦ TangentSpace I x)] in
lemma contMDiffAt_mvfderiv_apply {f : M → ℝ}
    {X : (x : M) → TangentSpace I x} {x : M}
    (hf : CMDiffAt ∞ f x) (hX : CMDiffAt ∞ (T% X) x) :
    CMDiffAt ∞ (fun y ↦ d% f y (X y)) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hXc : CMDiffAt ∞ (fun y ↦ (e (TotalSpace.mk' E y (X y))).2) x := by
    exact (contMDiffAt_section (n := ∞) x).mp hX
  have hD : CMDiffAt ∞
      (inTangentCoordinates I (modelWithCornersSelf ℝ ℝ)
        id f (mfderiv% f) x) x :=
    hf.mfderiv_const (by simp)
  apply (hD.clm_apply hXc).congr_of_eventuallyEq
  filter_upwards [e.open_baseSet.mem_nhds (mem_baseSet_trivializationAt E (TangentSpace I) x),
    chart_source_mem_nhds H x] with y hy hcy
  simp only [e, mfld_simps] at hy ⊢
  rw [inTangentCoordinates_eq id f (mfderiv% f) hcy (by simp)]
  rw [tangentBundleCore_coordChange_model_space]
  simp only [mvfderiv, Function.id_def, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.id_apply]
  rw [← Trivialization.continuousLinearMapAt_apply_of_mem
    ℝ (trivializationAt E (TangentSpace I) x) hy (X y)]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt_eq_core hcy]
  change mfderiv% f y (X y) = mfderiv% f y
    (tangentCoordChange I x y y (tangentCoordChange I y x y (X y)))
  have hxy : y ∈ (extChartAt I x).source := by
    simpa only [extChartAt_source] using hcy
  have hyy : y ∈ (extChartAt I y).source := by
    simpa only [extChartAt_source] using mem_chart_source H y
  have hc := tangentCoordChange_comp (I := I) (w := y) (x := x)
    (y := y) (z := y) (v := X y) ⟨⟨hyy, hxy⟩, hyy⟩
  have hs := tangentCoordChange_self (I := I) (x := y) (z := y) (v := X y) hyy
  rw [hc, hs]

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma contMDiffAt_metricTensor {x : M}
    {X Z : (x : M) → TangentSpace I x}
    (hX : CMDiffAt ∞ (T% X) x) (hZ : CMDiffAt ∞ (T% Z) x) :
    CMDiffAt ∞ (fun y ↦ metricTensor y (X y) (Z y)) x := by
  have h : ContMDiffAt I (I.prod (modelWithCornersSelf ℝ ℝ)) ∞
      (fun y : M ↦ TotalSpace.mk' ℝ (E := Bundle.Trivial M ℝ) y
        (metricTensor y (X y) (Z y))) x := by
    apply ContMDiffAt.clm_bundle_apply₂ (F₁ := E) (F₂ := E)
    · exact metricTensor_contMDiff.contMDiffAt
    · exact hX
    · exact hZ
  simp only [contMDiffAt_totalSpace] at h
  exact h.2

omit [FiniteDimensional ℝ E] in
lemma contMDiffAt_koszulAux {x : M}
    {X Y Z : (x : M) → TangentSpace I x}
    (hX : CMDiffAt ∞ (T% X) x) (hY : CMDiffAt ∞ (T% Y) x)
    (hZ : CMDiffAt ∞ (T% Z) x) :
    CMDiffAt ∞ (fun y ↦ koszulAux X Y Z y) x := by
  letI : IsManifold I (minSmoothness ℝ 2) M :=
    IsManifold.of_le (n := ∞) (by
      simpa using (ENat.LEInfty.out (m := (2 : ℕ∞ω))))
  letI : IsManifold I ((∞ : ℕ∞ω) + 1) M := by
    simpa using (inferInstance : IsManifold I ∞ M)
  have hYZ : CMDiffAt ∞ (T% (mlieBracket I Y Z)) x :=
    hY.mlieBracket_vectorField (m := ⊤) (n := ⊤) hZ (by simp)
  have hXZ : CMDiffAt ∞ (T% (mlieBracket I X Z)) x :=
    hX.mlieBracket_vectorField (m := ⊤) (n := ⊤) hZ (by simp)
  have hXY : CMDiffAt ∞ (T% (mlieBracket I X Y)) x :=
    hX.mlieBracket_vectorField (m := ⊤) (n := ⊤) hY (by simp)
  exact (((
    (contMDiffAt_mvfderiv_apply (contMDiffAt_metricTensor hY hZ) hX).add
      (contMDiffAt_mvfderiv_apply (contMDiffAt_metricTensor hX hZ) hY)).sub
    (contMDiffAt_mvfderiv_apply (contMDiffAt_metricTensor hX hY) hZ)).sub
    (contMDiffAt_metricTensor hX hYZ)).sub
    (contMDiffAt_metricTensor hY hXZ) |>.add
    (contMDiffAt_metricTensor hZ hXY)

/-! ### Local coordinates for the Koszul form -/

/-- The matrix of the Koszul form in the tangent frame based at `x₀`. -/
def coordinateKoszulForm {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    (Y : (x : M) → TangentSpace I x) (x₀ y : M) :
    E →L[ℝ] E →L[ℝ] ℝ :=
  let e := trivializationAt E (TangentSpace I) x₀
  ∑ i, ∑ j, ((2 : ℝ)⁻¹ *
    koszulAux (e.localFrame b i) Y (e.localFrame b j) y) •
      (b.coord i).toContinuousLinearMap.smulRight
        (b.coord j).toContinuousLinearMap

lemma coordinateKoszulForm_contMDiffAt {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (Y : (x : M) → TangentSpace I x) (x : M)
    (hY : CMDiffAt ∞ (T% Y) x) :
    CMDiffAt ∞ (coordinateKoszulForm b Y x) x := by
  let e := trivializationAt E (TangentSpace I) x
  have hx : x ∈ e.baseSet := mem_baseSet_trivializationAt E (TangentSpace I) x
  unfold coordinateKoszulForm
  apply contMDiffAt_finsetSum
  intro i _
  apply contMDiffAt_finsetSum
  intro j _
  have hs : CMDiffAt ∞
      (fun y ↦ (2 : ℝ)⁻¹ *
        koszulAux (e.localFrame b i) Y (e.localFrame b j) y) x := by
    apply contMDiffAt_const.mul
    apply contMDiffAt_koszulAux
    · exact contMDiffAt_localFrame_of_mem (I := I) (n := ∞) e b i hx
    · exact hY
    · exact contMDiffAt_localFrame_of_mem (I := I) (n := ∞) e b j hx
  exact hs.smul contMDiffAt_const

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma continuousLinearMap_ext_basis {F : Type*} [NormedAddCommGroup F]
    [NormedSpace ℝ F] {ι : Type*} [Fintype ι] (b : Module.Basis ι ℝ E)
    {f g : E →L[ℝ] F} (h : ∀ i, f (b i) = g (b i)) : f = g := by
  apply ContinuousLinearMap.ext
  intro v
  conv_lhs => rw [← b.sum_repr v]
  conv_rhs => rw [← b.sum_repr v]
  simp only [map_sum, map_smul]
  simp_rw [h]

lemma coordinateKoszulForm_eq_inCoordinates {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) (Y : (x : M) → TangentSpace I x)
    {x₀ y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hY : MDiffAt (T% Y) y) :
    coordinateKoszulForm b Y x₀ y =
      ContinuousLinearMap.inCoordinates E (TangentSpace I)
        (E →L[ℝ] ℝ) (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ)
        x₀ y x₀ y (koszulForm Y y hY) := by
  classical
  let e := trivializationAt E (TangentSpace I) x₀
  apply continuousLinearMap_ext_basis b
  intro i
  apply continuousLinearMap_ext_basis b
  intro j
  have hSi : MDiffAt (T% (e.localFrame b i)) y :=
    (contMDiffAt_localFrame_of_mem (I := I) (n := ∞) e b i hy).mdifferentiableAt (by simp)
  have hSj : MDiffAt (T% (e.localFrame b j)) y :=
    (contMDiffAt_localFrame_of_mem (I := I) (n := ∞) e b j hy).mdifferentiableAt (by simp)
  rw [inCoordinates_apply_eq₂ hy hy (Set.mem_univ _)]
  have hy' : y ∈ (chartAt H x₀).source := by
    simpa [e] using hy
  have hi : (e.symm y) (b i) = e.localFrame b i y := by
    simp [e, Bundle.Trivialization.localFrame, Bundle.Trivialization.basisAt, hy']
  have hj : (e.symm y) (b j) = e.localFrame b j y := by
    simp [e, Bundle.Trivialization.localFrame, Bundle.Trivialization.basisAt, hy']
  rw [hi, hj, koszulForm_apply hSi hY hSj]
  simp [coordinateKoszulForm]
  rw [Fintype.sum_eq_single i]
  · rw [Fintype.sum_eq_single j]
    · simp [e]
    · intro k hkj
      simp [hkj]
  · intro k hki
    simp [hki]

/-! ### Local coordinates for raising an index -/

/-- The metric's flat map in tangent-bundle coordinates based at `x₀`. -/
def coordinateMetric (x₀ y : M) : E →L[ℝ] E →L[ℝ] ℝ :=
  ContinuousLinearMap.inCoordinates E (TangentSpace I)
    (E →L[ℝ] ℝ) (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ)
    x₀ y x₀ y (metricTensor y)

omit [FiniteDimensional ℝ E] [CompleteSpace E] in
lemma coordinateMetric_contMDiffAt (x : M) :
    CMDiffAt ∞ (coordinateMetric (I := I) (E := E) x) x := by
  have h := metricTensor_contMDiff (I := I) (E := E) (M := M) x
  rw [contMDiffAt_hom_bundle] at h
  exact h.2

omit [CompleteSpace E] in
lemma coordinateMetric_isInvertible {x₀ y : M}
    (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet) :
    (coordinateMetric (I := I) (E := E) x₀ y).IsInvertible := by
  rw [coordinateMetric, ContinuousLinearMap.inCoordinates_eq hy (by simpa using hy)]
  have hm : metricTensor (I := I) (E := E) y =
      (metricEquiv (I := I) (E := E) y :
        TangentSpace I y →L[ℝ] (TangentSpace I y →L[ℝ] ℝ)) := by
    ext v
    rfl
  rw [hm]
  simp

lemma coordinateMetric_inverse_contMDiffAt (x : M) :
    CMDiffAt ∞ (fun y ↦ (coordinateMetric (I := I) (E := E) x y).inverse) x := by
  have hi := coordinateMetric_isInvertible (I := I) (E := E)
    (mem_baseSet_trivializationAt E (TangentSpace I) x)
  exact hi.contDiffAt_map_inverse.comp_contMDiffAt
    (coordinateMetric_contMDiffAt (I := I) (E := E) x)

lemma metric_koszulDerivative_eq {Y : (x : M) → TangentSpace I x}
    {x : M} (hY : MDiffAt (T% Y) x) (u : TangentSpace I x) :
    metricTensor x (koszulDerivative Y x u) = koszulForm Y x hY u := by
  rw [koszulDerivative, dif_pos hY]
  change metricEquiv x ((metricEquiv x).symm (koszulForm Y x hY u)) = _
  exact ContinuousLinearEquiv.apply_symm_apply _ _

lemma coordinate_koszulDerivative_eq {ι : Type*} [Fintype ι]
    (b : Module.Basis ι ℝ E) {Y : (x : M) → TangentSpace I x}
    {x₀ y : M} (hy : y ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (hY : MDiffAt (T% Y) y) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) E (TangentSpace I)
        x₀ y x₀ y (koszulDerivative Y y) =
      (coordinateMetric (I := I) (E := E) x₀ y).inverse.comp
        (coordinateKoszulForm (I := I) (E := E) b Y x₀ y) := by
  rw [coordinateKoszulForm_eq_inCoordinates b Y hy hY]
  have hi := coordinateMetric_isInvertible (I := I) (E := E) hy
  apply ContinuousLinearMap.ext
  intro u
  apply hi.injective
  simp only [ContinuousLinearMap.comp_apply, hi.self_apply_inverse]
  have hy' : y ∈
      (trivializationAt (E →L[ℝ] ℝ)
        (fun z : M ↦ TangentSpace I z →L[ℝ] ℝ) x₀).baseSet := by
    simpa using hy
  rw [coordinateMetric, ContinuousLinearMap.inCoordinates_eq hy hy',
    ContinuousLinearMap.inCoordinates_eq hy hy,
    ContinuousLinearMap.inCoordinates_eq hy hy']
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe]
  rw [ContinuousLinearEquiv.symm_apply_apply]
  rw [metric_koszulDerivative_eq hY]

lemma koszulDerivative_contMDiff (Y : (x : M) → TangentSpace I x)
    (hY : CMDiff ∞ (T% Y)) :
    ContMDiff I (I.prod (modelWithCornersSelf ℝ (E →L[ℝ] E))) ∞
      (fun x : M ↦ TotalSpace.mk' (E →L[ℝ] E)
        (E := fun y : M ↦ TangentSpace I y →L[ℝ] TangentSpace I y)
        x (koszulDerivative Y x)) := by
  intro x
  rw [contMDiffAt_hom_bundle]
  refine ⟨contMDiffAt_id, ?_⟩
  let b := Module.finBasis ℝ E
  have hK := coordinateKoszulForm_contMDiffAt (I := I) (E := E)
    b Y x (hY x)
  have h := (coordinateMetric_inverse_contMDiffAt (I := I) (E := E) x).clm_comp hK
  apply h.congr_of_eventuallyEq
  filter_upwards [
    (trivializationAt E (TangentSpace I) x).open_baseSet.mem_nhds
      (mem_baseSet_trivializationAt E (TangentSpace I) x)] with y hy
  exact coordinate_koszulDerivative_eq (I := I) (E := E) b hy
    ((hY y).mdifferentiableAt (by simp))

lemma koszulCovariantDerivative_contMDiff :
    ContMDiffCovariantDerivative
      (koszulCovariantDerivative (I := I) (E := E) (M := M)) ∞ := by
  rw [← contMDiffCovariantDerivativeOn_univ_iff]
  constructor
  intro Y hY
  rw [contMDiffOn_univ] at hY ⊢
  apply koszulDerivative_contMDiff
  simpa using hY

end

end Submission.Helpers
