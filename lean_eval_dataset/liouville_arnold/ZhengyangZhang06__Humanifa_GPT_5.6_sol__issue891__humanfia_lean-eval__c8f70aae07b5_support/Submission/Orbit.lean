import Submission.Variation

namespace Submission.Helpers

open Function Metric Set Topology
open scoped BigOperators NNReal Topology

section JointFlowDerivative

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : E → E}

/-- The first-order time expansion of a bounded Lipschitz flow has a uniform quadratic
remainder. -/
theorem norm_flow_sub_linear_time_le (d : CompleteFieldData X) (x : E) (t : ℝ) :
    ‖d.flow t x - x - t • X x‖ ≤
      (d.K : ℝ) * (d.L : ℝ) * |t| * |t| := by
  let q : ℝ → E := fun s ↦ d.flow s x - s • X x
  have hq (s : ℝ) : HasDerivAt q (X (d.flow s x) - X x) s := by
    have hsmul : HasDerivAt (fun r : ℝ ↦ r • X x) (X x) s := by
      simpa using (hasDerivAt_id s).smul_const (X x)
    exact (d.flow_hasDerivAt x s).sub hsmul
  have habs {s : ℝ} (hs : s ∈ uIcc 0 t) : |s| ≤ |t| := by
    rw [mem_uIcc] at hs
    rcases hs with hs | hs
    · rw [abs_of_nonneg hs.1, abs_of_nonneg (hs.1.trans hs.2)]
      exact hs.2
    · rw [abs_of_nonpos hs.2, abs_of_nonpos (hs.1.trans hs.2)]
      linarith
  have hbound (s : ℝ) (hs : s ∈ uIcc 0 t) :
      ‖X (d.flow s x) - X x‖ ≤ (d.K : ℝ) * (d.L : ℝ) * |t| := by
    have hdisp : ‖d.flow s x - x‖ ≤ (d.L : ℝ) * |s| := by
      have h := (globalIntegralCurve_lipschitzWith_time
        d.lipschitzWith d.norm_le x).norm_sub_le s 0
      simpa [CompleteFieldData.flow_apply] using h
    calc
      ‖X (d.flow s x) - X x‖ ≤ (d.K : ℝ) * ‖d.flow s x - x‖ :=
        d.lipschitzWith.norm_sub_le _ _
      _ ≤ (d.K : ℝ) * ((d.L : ℝ) * |s|) :=
        mul_le_mul_of_nonneg_left hdisp d.K.2
      _ ≤ (d.K : ℝ) * ((d.L : ℝ) * |t|) := by
        exact mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (habs hs) d.L.2) d.K.2
      _ = (d.K : ℝ) * (d.L : ℝ) * |t| := by ring
  have hbound' (s : ℝ) (hs : s ∈ uIcc 0 t) :
      ‖deriv q s‖ ≤ (d.K : ℝ) * (d.L : ℝ) * |t| := by
    rw [(hq s).deriv]
    exact hbound s hs
  have hmv := Convex.norm_image_sub_le_of_norm_deriv_le
    (s := uIcc 0 t) (x := (0 : ℝ)) (y := t)
    (fun s _ ↦ (hq s).differentiableAt) hbound' (convex_uIcc 0 t)
    left_mem_uIcc right_mem_uIcc
  calc
    ‖d.flow t x - x - t • X x‖ = ‖q t - q 0‖ := by
      simp only [q, d.flow.map_zero_apply, zero_smul]
      congr 1
      module
    _ ≤ ((d.K : ℝ) * (d.L : ℝ) * |t|) * ‖t - 0‖ := hmv
    _ = (d.K : ℝ) * (d.L : ℝ) * |t| * |t| := by
      rw [sub_zero, Real.norm_eq_abs]

/-- The derivative of `(t, y) ↦ flow t y` at `(0, x)`: the time direction is the vector
field and the initial-point direction is the identity. -/
noncomputable def flowZeroProdDerivative (X : E → E) (x : E) :
    (ℝ × E) →L[ℝ] E :=
  ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ E) (X x) +
    ContinuousLinearMap.snd ℝ ℝ E

theorem flow_hasFDerivAt_zero_prod (d : CompleteFieldData X) (x : E) :
    HasFDerivAt (fun p : ℝ × E ↦ d.flow p.1 p.2)
      (flowZeroProdDerivative X x) (0, x) := by
  rw [hasFDerivAt_iff_isLittleO_nhds_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro c hc
  let C : ℝ := (d.K : ℝ) * (d.L : ℝ) + (d.K : ℝ)
  have hC : 0 ≤ C := by positivity
  have hCp : 0 < C + 1 := by linarith
  filter_upwards [ball_mem_nhds 0 (div_pos hc hCp)] with p hp
  have hp_lt : ‖p‖ < c / (C + 1) := by
    simpa [mem_ball, dist_eq_norm] using hp
  have ht : |p.1| ≤ ‖p‖ := by
    rw [Prod.norm_mk]
    exact le_max_left _ _
  have hz : ‖p.2‖ ≤ ‖p‖ := by
    rw [Prod.norm_mk]
    exact le_max_right _ _
  have htime := norm_flow_sub_linear_time_le d (x + p.2) p.1
  have hfield : ‖X (x + p.2) - X x‖ ≤ (d.K : ℝ) * ‖p.2‖ := by
    simpa using d.lipschitzWith.norm_sub_le (x + p.2) x
  have hsmul : ‖p.1 • (X (x + p.2) - X x)‖ ≤
      |p.1| * ((d.K : ℝ) * ‖p.2‖) := by
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_left hfield (abs_nonneg p.1)
  have hres :
      ‖d.flow p.1 (x + p.2) - x - (p.1 • X x + p.2)‖ ≤
        C * ‖p‖ * ‖p‖ := by
    calc
      ‖d.flow p.1 (x + p.2) - x - (p.1 • X x + p.2)‖ =
          ‖(d.flow p.1 (x + p.2) - (x + p.2) - p.1 • X (x + p.2)) +
            p.1 • (X (x + p.2) - X x)‖ := by
        congr 1
        module
      _ ≤ ‖d.flow p.1 (x + p.2) - (x + p.2) - p.1 • X (x + p.2)‖ +
          ‖p.1 • (X (x + p.2) - X x)‖ := norm_add_le _ _
      _ ≤ (d.K : ℝ) * (d.L : ℝ) * |p.1| * |p.1| +
          |p.1| * ((d.K : ℝ) * ‖p.2‖) := by
        exact add_le_add htime hsmul
      _ ≤ (d.K : ℝ) * (d.L : ℝ) * ‖p‖ * ‖p‖ +
          ‖p‖ * ((d.K : ℝ) * ‖p‖) := by
        gcongr
      _ = C * ‖p‖ * ‖p‖ := by
        dsimp [C]
        ring
  have hfactor : C * ‖p‖ ≤ c := by
    calc
      C * ‖p‖ ≤ (C + 1) * ‖p‖ := by
        gcongr
        linarith
      _ ≤ (C + 1) * (c / (C + 1)) :=
        mul_le_mul_of_nonneg_left hp_lt.le hCp.le
      _ = c := by field_simp
  simpa [flowZeroProdDerivative] using
    hres.trans (mul_le_mul_of_nonneg_right hfactor (norm_nonneg p))

end JointFlowDerivative

section RestrictedCommutingFlows

variable {ι E : Type*} [Fintype ι] [DecidableEq ι]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
  {X : ι → E → E} {M : Set E}
  (d : ∀ i, CompleteFieldData (X i))
  (hM : ∀ i, IsInvariant (d i).flow M)
  (hcomm : ∀ i j s t, ∀ x ∈ M,
    (d i).flow s ((d j).flow t x) = (d j).flow t ((d i).flow s x))

/-- Restrict each complete flow to the common invariant set. -/
noncomputable def restrictedFlows (i : ι) : Flow ℝ M :=
  (d i).flow.restrict (hM i)

omit [Fintype ι] [DecidableEq ι] in
@[simp]
theorem restrictedFlows_apply (i : ι) (t : ℝ) (x : M) :
    restrictedFlows d hM i t x = (d i).flow t x := rfl

omit [Fintype ι] [DecidableEq ι] in
include hcomm in
theorem restrictedFlows_commute (i j : ι) (s t : ℝ) :
    Function.Commute (restrictedFlows d hM i s) (restrictedFlows d hM j t) := by
  intro x
  apply Subtype.ext
  exact hcomm i j s t x x.2

private noncomputable def restrictedComponentHomeomorph
    (t : ι → ℝ) (i : ι) : M ≃ₜ M :=
  (restrictedFlows d hM i).toHomeomorph (t i)

omit [Fintype ι] [DecidableEq ι] in
include hcomm in
private theorem restrictedComponentHomeomorph_commute
    (t : ι → ℝ) (i j : ι) :
    Commute (restrictedComponentHomeomorph d hM t i)
      (restrictedComponentHomeomorph d hM t j) := by
  apply Homeomorph.ext
  intro x
  exact restrictedFlows_commute d hM hcomm i j (t i) (t j) x

include hcomm in
/-- The finite product used by the joint flow, exposed here to calculate its derivative. -/
private noncomputable def restrictedFlowProduct
    (s : Finset ι) (t : ι → ℝ) : M ≃ₜ M :=
  s.noncommProd (restrictedComponentHomeomorph d hM t) fun i _ j _ _ ↦
    restrictedComponentHomeomorph_commute d hM hcomm t i j

omit [Fintype ι] [DecidableEq ι] in
private theorem restrictedFlowProduct_empty (t : ι → ℝ) :
    restrictedFlowProduct d hM hcomm ∅ t = 1 := by
  simp [restrictedFlowProduct]

omit [Fintype ι] [DecidableEq ι] in
private theorem restrictedFlowProduct_cons
    (s : Finset ι) (a : ι) (ha : a ∉ s) (t : ι → ℝ) :
    restrictedFlowProduct d hM hcomm (Finset.cons a s ha) t =
      restrictedComponentHomeomorph d hM t a *
        restrictedFlowProduct d hM hcomm s t := by
  unfold restrictedFlowProduct
  rw [Finset.noncommProd_cons]

omit [Fintype ι] [DecidableEq ι] in
private theorem restrictedFlowProduct_zero (s : Finset ι) :
    restrictedFlowProduct d hM hcomm s 0 = 1 := by
  rw [restrictedFlowProduct,
    Finset.noncommProd_eq_pow_card _ _ _ (1 : M ≃ₜ M)]
  · simp
  · intro i hi
    apply Homeomorph.ext
    intro x
    exact (restrictedFlows d hM i).map_zero_apply x

/-- The linear combination of a finite family of tangent vectors. -/
noncomputable def familyCombinationOn (s : Finset ι) (v : ι → E) :
    (ι → ℝ) →L[ℝ] E :=
  ∑ i ∈ s, ContinuousLinearMap.smulRight (ContinuousLinearMap.proj i) (v i)

omit [Fintype ι] [DecidableEq ι] [CompleteSpace E] in
@[simp]
theorem familyCombinationOn_apply (s : Finset ι) (v : ι → E)
    (a : ι → ℝ) :
    familyCombinationOn s v a = ∑ i ∈ s, a i • v i := by
  simp [familyCombinationOn]

private theorem restrictedFlowProduct_hasFDerivAt_zero
    (s : Finset ι) (x : M) :
    HasFDerivAt
      (fun t : ι → ℝ ↦ ((restrictedFlowProduct d hM hcomm s t x : M) : E))
      (familyCombinationOn s (fun i ↦ X i x)) 0 := by
  induction s using Finset.cons_induction_on with
  | empty =>
      simpa [restrictedFlowProduct_empty, familyCombinationOn] using
        (hasFDerivAt_const (x := (0 : ι → ℝ)) (c := (x : E)))
  | @cons a s ha ih =>
      have hpair : HasFDerivAt
          (fun t : ι → ℝ ↦
            (t a, ((restrictedFlowProduct d hM hcomm s t x : M) : E)))
          ((ContinuousLinearMap.proj a).prod
            (familyCombinationOn s (fun i ↦ X i x))) 0 :=
        (hasFDerivAt_apply a (0 : ι → ℝ)).prodMk ih
      have hjoint : HasFDerivAt
          (fun p : ℝ × E ↦ (d a).flow p.1 p.2)
          (flowZeroProdDerivative (X a) (x : E))
          (0, ((restrictedFlowProduct d hM hcomm s 0 x : M) : E)) := by
        simpa [restrictedFlowProduct_zero] using
          flow_hasFDerivAt_zero_prod (d a) (x : E)
      have hcomp := hjoint.comp 0 hpair
      have hfun :
          (fun t : ι → ℝ ↦
            ((restrictedFlowProduct d hM hcomm (Finset.cons a s ha) t x : M) : E)) =
            (fun p : ℝ × E ↦ (d a).flow p.1 p.2) ∘
              fun t : ι → ℝ ↦
                (t a, ((restrictedFlowProduct d hM hcomm s t x : M) : E)) := by
        funext t
        rw [restrictedFlowProduct_cons d hM hcomm s a ha]
        rfl
      have hderiv :
          familyCombinationOn (Finset.cons a s ha) (fun i ↦ X i x) =
            flowZeroProdDerivative (X a) (x : E) ∘L
              (ContinuousLinearMap.proj a).prod
                (familyCombinationOn s (fun i ↦ X i x)) := by
        ext t
        simp [flowZeroProdDerivative, familyCombinationOn_apply, ha]
      rw [hfun, hderiv]
      exact hcomp

/-- At the zero parameter, the orbit map of the joint restricted flow has derivative equal to
the linear combination of its generating vector fields. -/
theorem piFlow_restricted_hasFDerivAt_zero (x : M) :
    HasFDerivAt
      (fun t : ι → ℝ ↦
        (((piFlow (restrictedFlows d hM) (restrictedFlows_commute d hM hcomm)) t x : M) : E))
      (familyCombinationOn Finset.univ (fun i ↦ X i x)) 0 := by
  convert restrictedFlowProduct_hasFDerivAt_zero d hM hcomm Finset.univ x using 1
  funext t
  rfl

/-- The derivative of the restricted joint orbit at an arbitrary parameter is the linear
combination of the generating fields at the corresponding orbit point. -/
theorem piFlow_restricted_hasFDerivAt (x : M) (t : ι → ℝ) :
    HasFDerivAt
      (fun q : ι → ℝ ↦
        (((piFlow (restrictedFlows d hM) (restrictedFlows_commute d hM hcomm)) q x : M) : E))
      (familyCombinationOn Finset.univ fun i ↦
        X i ((piFlow (restrictedFlows d hM)
          (restrictedFlows_commute d hM hcomm)) t x : M)) t := by
  let φ := piFlow (restrictedFlows d hM) (restrictedFlows_commute d hM hcomm)
  let y : M := φ t x
  have hzero := piFlow_restricted_hasFDerivAt_zero d hM hcomm y
  have hshift : HasFDerivAt (fun q : ι → ℝ ↦ q - t)
      (ContinuousLinearMap.id ℝ (ι → ℝ)) t := by
    simpa using
      ((hasFDerivAt_id t : HasFDerivAt (fun q : ι → ℝ ↦ q)
        (ContinuousLinearMap.id ℝ (ι → ℝ)) t).sub_const t)
  have hzero' : HasFDerivAt
      (fun r : ι → ℝ ↦ ((φ r y : M) : E))
      (familyCombinationOn Finset.univ fun i ↦ X i y) (t - t) := by
    simpa [φ] using hzero
  have hcomp := hzero'.comp (f := fun q : ι → ℝ ↦ q - t) t hshift
  have hfun : (fun q : ι → ℝ ↦ ((φ q x : M) : E)) =
      (fun r : ι → ℝ ↦ ((φ r y : M) : E)) ∘ fun q ↦ q - t := by
    funext q
    change ((φ q x : M) : E) = ((φ (q - t) (φ t x) : M) : E)
    rw [← φ.map_add]
    congr 2
    module
  have hderiv :
      (familyCombinationOn Finset.univ fun i ↦ X i y) ∘L
          ContinuousLinearMap.id ℝ (ι → ℝ) =
        familyCombinationOn Finset.univ fun i ↦ X i (φ t x) := by
    ext a
    simp [y]
  rw [← hfun, hderiv] at hcomp
  simpa [φ] using hcomp

omit [DecidableEq ι] in
/-- Continuity of the derivative field of a joint orbit. -/
theorem continuous_familyCombinationOn_piFlow
    (hX : ∀ i, Continuous (X i)) (x : M) :
    Continuous (fun t : ι → ℝ ↦
      familyCombinationOn Finset.univ fun i ↦
        X i ((piFlow (restrictedFlows d hM)
          (restrictedFlows_commute d hM hcomm)) t x : M)) := by
  let φ := piFlow (restrictedFlows d hM) (restrictedFlows_commute d hM hcomm)
  have horbit : Continuous (fun t : ι → ℝ ↦ ((φ t x : M) : E)) :=
    continuous_subtype_val.comp (φ.continuous continuous_id continuous_const)
  change Continuous (fun t : ι → ℝ ↦
    ∑ i ∈ Finset.univ,
      ContinuousLinearMap.smulRight (ContinuousLinearMap.proj i)
        (X i ((φ t x : M) : E)))
  exact continuous_finsetSum Finset.univ fun i _ ↦
    ((ContinuousLinearMap.smulRightL ℝ (ι → ℝ) E)
      (ContinuousLinearMap.proj i)).continuous.comp ((hX i).comp horbit)

/-- A joint orbit of continuous generating fields is strictly differentiable; this follows
from its pointwise derivative formula and the continuity of that derivative. -/
theorem piFlow_restricted_hasStrictFDerivAt
    (hX : ∀ i, Continuous (X i)) (x : M) (t : ι → ℝ) :
    HasStrictFDerivAt
      (fun q : ι → ℝ ↦
        (((piFlow (restrictedFlows d hM) (restrictedFlows_commute d hM hcomm)) q x : M) : E))
      (familyCombinationOn Finset.univ fun i ↦
        X i ((piFlow (restrictedFlows d hM)
          (restrictedFlows_commute d hM hcomm)) t x : M)) t := by
  apply hasStrictFDerivAt_of_hasFDerivAt_of_continuousAt
    (f' := fun q : ι → ℝ ↦
      familyCombinationOn Finset.univ fun i ↦
        X i ((piFlow (restrictedFlows d hM)
          (restrictedFlows_commute d hM hcomm)) q x : M))
  · exact Filter.Eventually.of_forall fun q ↦
      piFlow_restricted_hasFDerivAt d hM hcomm x q
  · exact (continuous_familyCombinationOn_piFlow d hM hcomm hX x).continuousAt

end RestrictedCommutingFlows

end Submission.Helpers
