import Submission.QuaternionHomotopy
import Mathlib.Analysis.Normed.Module.Ball.Homeomorph
import Mathlib.Analysis.Normed.Module.Ball.RadialEquiv
import Mathlib.Topology.Gluing

/-!
# A connected sum of two quaternionic space forms

The connected sum is presented as the gluing of two punctured copies of the
quaternionic spherical space form.  In a ball chart at the puncture, the
transition reverses the radial coordinate.  Keeping the transition explicit
also makes the two quaternion subgroups visible at the level of loops.
-/

open LeanEval.Topology
open Metric
open TopologicalSpace
open CategoryTheory

namespace Submission.ConnectedSum

open QuaternionSpaceForm
open QuaternionObstruction
open QuaternionPaths
open QuaternionHomotopy

noncomputable section

abbrev EuclideanThree := EuclideanSpace ℝ (Fin 3)

noncomputable local instance : ChartedSpace EuclideanThree SpaceForm :=
  QuaternionSpaceForm.closed3Manifold.charted

noncomputable local instance : SecondCountableTopology SpaceForm :=
  QuaternionSpaceForm.closed3Manifold.secondCountable

/-- The image of the generic quaternion-sphere point used as the puncture. -/
noncomputable def puncture : SpaceForm :=
  Quotient.mk'' QuaternionSpaceForm.genericPoint

theorem puncture_ne_basepoint : puncture ≠ basepoint := by
  intro h
  have horbit :
      QuaternionSpaceForm.genericPoint ∈
        MulAction.orbit QuaternionObstruction.Q8 (1 : SphereThree) :=
    Quotient.exact h
  obtain ⟨q, hq⟩ := MulAction.mem_orbit_iff.mp horbit
  exact genericPoint_ne_baseOrbit q hq.symm

/-- The punctured space form, as an open subspace. -/
def puncturedOpen : Opens SpaceForm :=
  ⟨({puncture}ᶜ : Set SpaceForm), isOpen_compl_singleton⟩

abbrev Punctured := puncturedOpen

/-- The original basepoint lies in the punctured space form. -/
noncomputable def puncturedBasepoint : Punctured :=
  ⟨basepoint, by
    simpa [puncturedOpen] using puncture_ne_basepoint.symm⟩

noncomputable instance : ChartedSpace EuclideanThree Punctured where
  atlas :=
    ⋃ x : Punctured,
      {(chartAt EuclideanThree x.1).subtypeRestr ⟨x⟩}
  chartAt x :=
    (chartAt EuclideanThree x.1).subtypeRestr ⟨x⟩
  mem_chart_source x := ⟨trivial, mem_chart_source EuclideanThree x.1⟩
  chart_mem_atlas x := by
    simp only [Set.mem_iUnion, Set.mem_singleton_iff]
    exact ⟨x, rfl⟩

/-- The complement of the puncture is path connected. -/
noncomputable instance : PathConnectedSpace Punctured := by
  let U : Set SphereThree := genericOrbitᶜ
  let f : U → Punctured := fun z =>
    ⟨Quotient.mk'' z.1, by
      intro h
      have horbit :
          z.1 ∈ MulAction.orbit QuaternionObstruction.Q8
            QuaternionSpaceForm.genericPoint :=
        Quotient.exact h
      exact z.2 horbit⟩
  have hf : Continuous f :=
    (quotientMap.continuous.comp continuous_subtype_val).subtype_mk _
  have hfs : Function.Surjective f := by
    intro x
    obtain ⟨z, hz⟩ := Quotient.exists_rep x.1
    have hzU : z ∈ U := by
      intro hzorb
      apply x.2
      rw [← hz]
      exact Quotient.sound hzorb
    exact ⟨⟨z, hzU⟩, Subtype.ext hz⟩
  letI : PathConnectedSpace U :=
    isPathConnected_iff_pathConnectedSpace.mp <|
      SphereComplement.compl_finite_isPathConnected
        QuaternionSpaceForm.genericPoint genericOrbit genericOrbit_finite
        genericPoint_mem_genericOrbit
  exact hfs.pathConnectedSpace hf

/-- The preferred chart at the puncture. -/
noncomputable def punctureLocalChart :
    OpenPartialHomeomorph SpaceForm EuclideanThree :=
  chartAt EuclideanThree puncture

/-- The chart coordinate of the puncture. -/
noncomputable def punctureChartCenter : EuclideanThree :=
  punctureLocalChart puncture

/-- The finite union of the projected preferred quaternion paths. -/
def supportedTrace : Set SpaceForm :=
  ⋃ q : Q8,
    Set.range fun t =>
      (Quotient.mk'' (supportedPath q t) : SpaceForm)

private theorem supportedTrace_isCompact :
    IsCompact supportedTrace := by
  apply isCompact_iUnion
  intro q
  exact isCompact_range <|
    quotientMap.continuous.comp (supportedPath q).continuous

private theorem puncture_not_mem_supportedTrace :
    puncture ∉ supportedTrace := by
  rw [supportedTrace, Set.mem_iUnion]
  rintro ⟨q, t, ht⟩
  have horbit :
      supportedPath q t ∈
        MulAction.orbit Q8 QuaternionSpaceForm.genericPoint :=
    Quotient.exact ht
  exact supportedPath_not_mem_genericOrbit q t horbit

/--
Chart coordinates whose inverse images avoid the compact trace of all
preferred quaternion loops.
-/
noncomputable def safeChartTarget : Set EuclideanThree :=
  punctureLocalChart.target ∩
    punctureLocalChart.symm ⁻¹' supportedTraceᶜ

private theorem safeChartTarget_isOpen :
    IsOpen safeChartTarget :=
  punctureLocalChart.symm.isOpen_inter_preimage <|
    supportedTrace_isCompact.isClosed.isOpen_compl

private theorem punctureChartCenter_mem_safeChartTarget :
    punctureChartCenter ∈ safeChartTarget := by
  have hp : puncture ∈ punctureLocalChart.source :=
    mem_chart_source EuclideanThree puncture
  refine ⟨punctureLocalChart.map_source hp, ?_⟩
  change punctureLocalChart.symm punctureChartCenter ∉ supportedTrace
  rw [show punctureLocalChart.symm punctureChartCenter = puncture by
    exact punctureLocalChart.left_inv hp]
  exact puncture_not_mem_supportedTrace

/--
A positive radius whose closed coordinate ball is contained in the target of
the puncture chart and avoids all preferred quaternion loops.
-/
noncomputable def chartRadiusData :
    {r : ℝ //
      0 < r ∧
        closedBall punctureChartCenter r ⊆ safeChartTarget} := by
  let hex :=
    Metric.isOpen_iff.mp safeChartTarget_isOpen
      punctureChartCenter punctureChartCenter_mem_safeChartTarget
  let ε : ℝ := Classical.choose hex
  have hε : 0 < ε := (Classical.choose_spec hex).1
  have hball :
      ball punctureChartCenter ε ⊆ safeChartTarget :=
    (Classical.choose_spec hex).2
  refine ⟨ε / 2, half_pos hε, ?_⟩
  intro y hy
  apply hball
  rw [mem_ball']
  exact (mem_closedBall'.1 hy).trans_lt (half_lt_self hε)

noncomputable def chartRadius : ℝ :=
  chartRadiusData.1

theorem chartRadius_pos : 0 < chartRadius :=
  chartRadiusData.2.1

theorem closedBall_chartRadius_subset :
    closedBall punctureChartCenter chartRadius ⊆
      punctureLocalChart.target :=
  fun _ hy => (chartRadiusData.2.2 hy).1

theorem closedBall_chartRadius_avoids_supportedTrace
    {y : EuclideanThree}
    (hy : y ∈ closedBall punctureChartCenter chartRadius) :
    punctureLocalChart.symm y ∉ supportedTrace :=
  (chartRadiusData.2.2 hy).2

/-- The punctured coordinate ball on which the two summands overlap. -/
noncomputable def collar : Opens Punctured where
  carrier :=
    {x |
      x.1 ∈ punctureLocalChart.source ∧
        punctureLocalChart x.1 ∈
          ball punctureChartCenter chartRadius}
  is_open' := by
    let W : Set SpaceForm :=
      punctureLocalChart.source ∩
        punctureLocalChart ⁻¹' ball punctureChartCenter chartRadius
    have hW : IsOpen W :=
      punctureLocalChart.isOpen_inter_preimage isOpen_ball
    exact hW.preimage continuous_subtype_val

theorem collar_avoids_supportedTrace
    (x : Punctured) (hx : x ∈ collar) :
    x.1 ∉ supportedTrace := by
  have hsafe :=
    closedBall_chartRadius_avoids_supportedTrace <|
      mem_closedBall'.2 (mem_ball'.1 hx.2).le
  rw [punctureLocalChart.left_inv hx.1] at hsafe
  exact hsafe

abbrev PolarCollar :=
  sphere (0 : EuclideanThree) 1 × Set.Ioo (0 : ℝ) chartRadius

private theorem collar_coordinate_ne_center (x : collar) :
    punctureLocalChart x.1.1 ≠ punctureChartCenter := by
  intro h
  apply x.1.2
  apply punctureLocalChart.injOn x.2.1
    (mem_chart_source EuclideanThree puncture)
  exact h

noncomputable def collarOffset
    (x : collar) : ({0}ᶜ : Set EuclideanThree) :=
  ⟨punctureLocalChart x.1.1 - punctureChartCenter,
    sub_ne_zero.mpr (collar_coordinate_ne_center x)⟩

theorem collarOffset_continuous : Continuous collarOffset := by
  apply Continuous.subtype_mk
  exact
    (punctureLocalChart.continuousOn.comp_continuous
      (continuous_subtype_val.comp continuous_subtype_val)
      fun x => x.2.1).sub continuous_const

noncomputable def collarToPolar (x : collar) : PolarCollar :=
  let z := homeomorphUnitSphereProd EuclideanThree (collarOffset x)
  ⟨z.1, ⟨z.2.1, z.2.2, by
    rw [homeomorphUnitSphereProd_apply_snd_coe]
    simpa [collarOffset, mem_ball', dist_eq_norm, norm_sub_rev] using
      x.2.2⟩⟩

theorem collarToPolar_continuous : Continuous collarToPolar := by
  have hz :
      Continuous fun x : collar =>
        homeomorphUnitSphereProd EuclideanThree (collarOffset x) :=
    (homeomorphUnitSphereProd EuclideanThree).continuous.comp
      collarOffset_continuous
  exact hz.fst.prodMk <|
    (continuous_subtype_val.comp hz.snd).subtype_mk _

noncomputable def polarUnitProduct
    (z : PolarCollar) :
      sphere (0 : EuclideanThree) 1 × Set.Ioi (0 : ℝ) :=
  ⟨z.1, ⟨z.2.1, z.2.2.1⟩⟩

theorem polarUnitProduct_continuous :
    Continuous polarUnitProduct :=
  continuous_fst.prodMk <|
    (continuous_subtype_val.comp continuous_snd).subtype_mk _

noncomputable def polarOffset
    (z : PolarCollar) : ({0}ᶜ : Set EuclideanThree) :=
  (homeomorphUnitSphereProd EuclideanThree).symm
    (polarUnitProduct z)

theorem polarOffset_continuous : Continuous polarOffset :=
  (homeomorphUnitSphereProd EuclideanThree).symm.continuous.comp
    polarUnitProduct_continuous

theorem norm_polarOffset (z : PolarCollar) :
    ‖(polarOffset z : EuclideanThree)‖ = z.2.1 := by
  rw [show (polarOffset z : EuclideanThree) =
      z.2.1 • (z.1 : EuclideanThree) by
    exact homeomorphUnitSphereProd_symm_apply_coe
      EuclideanThree (polarUnitProduct z)]
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos z.2.2.1]
  have hz : ‖(z.1 : EuclideanThree)‖ = 1 := by
    simpa only [mem_sphere_zero_iff_norm] using z.1.2
  simp [hz]

noncomputable def polarPoint (z : PolarCollar) : EuclideanThree :=
  polarOffset z + punctureChartCenter

theorem polarPoint_continuous : Continuous polarPoint :=
  (continuous_subtype_val.comp polarOffset_continuous).add continuous_const

theorem polarPoint_mem_ball (z : PolarCollar) :
    polarPoint z ∈ ball punctureChartCenter chartRadius := by
  rw [mem_ball', dist_eq_norm]
  have hsub :
      punctureChartCenter - polarPoint z =
        -(polarOffset z : EuclideanThree) := by
    simp [polarPoint, sub_eq_add_neg, add_comm]
  rw [hsub, norm_neg, norm_polarOffset]
  exact z.2.2.2

theorem polarPoint_mem_target (z : PolarCollar) :
    polarPoint z ∈ punctureLocalChart.target :=
  closedBall_chartRadius_subset <|
    mem_closedBall'.2 (mem_ball'.1 (polarPoint_mem_ball z)).le

noncomputable def polarPreimage (z : PolarCollar) : SpaceForm :=
  punctureLocalChart.symm (polarPoint z)

theorem polarPreimage_mem_source (z : PolarCollar) :
    polarPreimage z ∈ punctureLocalChart.source :=
  punctureLocalChart.map_target (polarPoint_mem_target z)

theorem polarPreimage_ne_puncture (z : PolarCollar) :
    polarPreimage z ≠ puncture := by
  intro h
  have hw :
      polarPoint z = punctureChartCenter := by
    calc
      polarPoint z =
          punctureLocalChart (punctureLocalChart.symm (polarPoint z)) :=
        (punctureLocalChart.right_inv (polarPoint_mem_target z)).symm
      _ = punctureLocalChart puncture := congr_arg punctureLocalChart h
      _ = punctureChartCenter := rfl
  apply (polarOffset z).2
  apply add_right_cancel (b := punctureChartCenter)
  simpa [polarPoint] using hw

noncomputable def polarToCollar (z : PolarCollar) : collar :=
  ⟨⟨polarPreimage z, by
      simpa [puncturedOpen] using polarPreimage_ne_puncture z⟩,
    polarPreimage_mem_source z, by
      change punctureLocalChart (polarPreimage z) ∈
        ball punctureChartCenter chartRadius
      change
        punctureLocalChart (punctureLocalChart.symm (polarPoint z)) ∈
          ball punctureChartCenter chartRadius
      rw [punctureLocalChart.right_inv (polarPoint_mem_target z)]
      exact polarPoint_mem_ball z⟩

theorem polarToCollar_continuous : Continuous polarToCollar := by
  have hx : Continuous polarPreimage :=
    punctureLocalChart.symm.continuousOn.comp_continuous
      polarPoint_continuous polarPoint_mem_target
  exact (hx.subtype_mk _).subtype_mk _

theorem polarOffset_collarToPolar (x : collar) :
    polarOffset (collarToPolar x) = collarOffset x := by
  apply Subtype.ext
  exact congr_arg Subtype.val <|
    (homeomorphUnitSphereProd EuclideanThree).symm_apply_apply
      (collarOffset x)

theorem collarOffset_polarToCollar (z : PolarCollar) :
    collarOffset (polarToCollar z) = polarOffset z := by
  apply Subtype.ext
  change
    punctureLocalChart (polarPreimage z) - punctureChartCenter =
      (polarOffset z : EuclideanThree)
  change
    punctureLocalChart (punctureLocalChart.symm (polarPoint z)) -
        punctureChartCenter =
      (polarOffset z : EuclideanThree)
  rw [punctureLocalChart.right_inv (polarPoint_mem_target z)]
  simp [polarPoint]

/-- Polar coordinates on the punctured chart ball. -/
noncomputable def collarPolar : collar ≃ₜ PolarCollar where
  toFun := collarToPolar
  invFun := polarToCollar
  left_inv := by
    intro x
    apply Subtype.ext
    apply Subtype.ext
    apply punctureLocalChart.injOn
      (polarPreimage_mem_source (collarToPolar x)) x.2.1
    rw [show punctureLocalChart (polarPreimage (collarToPolar x)) =
      polarPoint (collarToPolar x) by
        exact punctureLocalChart.right_inv
          (polarPoint_mem_target (collarToPolar x))]
    simp [polarPoint, polarOffset_collarToPolar, collarOffset]
  right_inv := by
    intro z
    have h :=
      (homeomorphUnitSphereProd EuclideanThree).apply_symm_apply
        (polarUnitProduct z)
    apply Prod.ext
    · change
        (homeomorphUnitSphereProd EuclideanThree
          (collarOffset (polarToCollar z))).1 = z.1
      rw [collarOffset_polarToCollar]
      exact congr_arg Prod.fst h
    · apply Subtype.ext
      change
        ((homeomorphUnitSphereProd EuclideanThree
          (collarOffset (polarToCollar z))).2 : ℝ) = z.2.1
      rw [collarOffset_polarToCollar]
      exact congr_arg (fun w => (w.2 : ℝ)) h
  continuous_toFun := collarToPolar_continuous
  continuous_invFun := polarToCollar_continuous

/-- Reversal of the radial coordinate in the punctured chart ball. -/
noncomputable def polarFlip : PolarCollar ≃ₜ PolarCollar where
  toFun z :=
    ⟨z.1,
      ⟨chartRadius - z.2.1,
        sub_pos.mpr z.2.2.2,
        sub_lt_self chartRadius z.2.2.1⟩⟩
  invFun z :=
    ⟨z.1,
      ⟨chartRadius - z.2.1,
        sub_pos.mpr z.2.2.2,
        sub_lt_self chartRadius z.2.2.1⟩⟩
  left_inv z := by
    ext <;> simp
  right_inv z := by
    ext <;> simp
  continuous_toFun := by
    fun_prop
  continuous_invFun := by
    fun_prop

/-- The involutive transition map between the two punctured summands. -/
noncomputable def collarFlip : collar ≃ₜ collar :=
  collarPolar.trans <| polarFlip.trans collarPolar.symm

theorem collarFlip_involutive (x : collar) :
    collarFlip (collarFlip x) = x := by
  simp [collarFlip, polarFlip]

/-- The overlap chosen for each ordered pair of summands. -/
noncomputable def overlap : Bool → Bool → Opens Punctured
  | false, false => ⊤
  | false, true => collar
  | true, false => collar
  | true, true => ⊤

/-- Identity transitions on a patch and radial reversal between patches. -/
private noncomputable def identityTransition (i : Bool) :
    (Opens.toTopCat (TopCat.of Punctured)).obj (overlap i i) ⟶
      (Opens.toTopCat (TopCat.of Punctured)).obj (overlap i i) :=
  𝟙 _

noncomputable def transition :
    ∀ i j : Bool,
      (Opens.toTopCat (TopCat.of Punctured)).obj (overlap i j) ⟶
        (Opens.toTopCat (TopCat.of Punctured)).obj (overlap j i)
  | false, false => identityTransition false
  | false, true =>
      TopCat.ofHom ⟨collarFlip, collarFlip.continuous⟩
  | true, false =>
      TopCat.ofHom ⟨collarFlip, collarFlip.continuous⟩
  | true, true => identityTransition true

/-- Elementwise gluing data for the two punctured summands. -/
noncomputable abbrev glueCore : TopCat.GlueData.MkCore where
  J := Bool
  U := fun _ => TopCat.of Punctured
  V := overlap
  t := transition
  V_id := by
    intro i
    cases i <;> rfl
  t_id := by
    intro i
    cases i <;> funext x <;>
      simp [transition, identityTransition]
  t_inter := by
    intro i j k x hx
    cases i <;> cases j <;> cases k <;>
      simp_all [overlap, transition, identityTransition]
    all_goals exact hx
  cocycle := by
    intro i j k x hx
    cases i <;> cases j <;> cases k <;>
      simp_all [overlap, transition, identityTransition]
    all_goals
      first
      | rfl
      | (change (collarFlip (collarFlip x)).1 = x.1
         exact congr_arg Subtype.val (collarFlip_involutive x))

noncomputable abbrev glueData : TopCat.GlueData :=
  TopCat.GlueData.mk' glueCore

/-- The underlying topological connected sum. -/
abbrev Carrier :=
  glueData.glued

/-- The canonical open embedding of a punctured summand. -/
noncomputable abbrev patchInclusion (i : Bool) : C(Punctured, Carrier) :=
  (glueData.ι i).hom

theorem patchInclusion_isOpenEmbedding (i : Bool) :
    Topology.IsOpenEmbedding (patchInclusion i) :=
  by
    set_option backward.isDefEq.respectTransparency false in
      exact glueData.ι_isOpenEmbedding i

private noncomputable def representativeIndex (x : Carrier) : Bool :=
  (glueData.ι_jointly_surjective x).choose

private noncomputable def representativePoint (x : Carrier) : Punctured :=
  (glueData.ι_jointly_surjective x).choose_spec.choose

private theorem patchInclusion_representative (x : Carrier) :
    patchInclusion (representativeIndex x) (representativePoint x) = x :=
  by
    set_option backward.isDefEq.respectTransparency false in
      exact (glueData.ι_jointly_surjective x).choose_spec.choose_spec

noncomputable instance : ChartedSpace EuclideanThree Carrier where
  atlas :=
    Set.range fun x : Carrier =>
      (chartAt EuclideanThree (representativePoint x)).lift_openEmbedding
        (patchInclusion_isOpenEmbedding (representativeIndex x))
  chartAt x :=
    (chartAt EuclideanThree (representativePoint x)).lift_openEmbedding
      (patchInclusion_isOpenEmbedding (representativeIndex x))
  mem_chart_source x := by
    rw [OpenPartialHomeomorph.lift_openEmbedding_source]
    exact
      ⟨representativePoint x,
        mem_chart_source EuclideanThree (representativePoint x),
        patchInclusion_representative x⟩
  chart_mem_atlas x :=
    ⟨x, rfl⟩

/-- The quotient map from the disjoint union of the two patches. -/
noncomputable def patchQuotient : Punctured ⊕ Punctured → Carrier :=
  Sum.elim (patchInclusion false) (patchInclusion true)

theorem patchQuotient_continuous : Continuous patchQuotient :=
  continuous_sumElim.mpr
    ⟨(patchInclusion false).continuous, (patchInclusion true).continuous⟩

theorem patchQuotient_isOpenMap : IsOpenMap patchQuotient :=
  isOpenMap_sumElim.mpr
    ⟨(patchInclusion_isOpenEmbedding false).isOpenMap,
      (patchInclusion_isOpenEmbedding true).isOpenMap⟩

theorem patchQuotient_surjective :
    Function.Surjective patchQuotient := by
  intro x
  obtain ⟨i, y, hy⟩ := glueData.ι_jointly_surjective x
  cases i
  · exact ⟨Sum.inl y, by
      set_option backward.isDefEq.respectTransparency false in
        exact hy⟩
  · exact ⟨Sum.inr y, by
      set_option backward.isDefEq.respectTransparency false in
        exact hy⟩

theorem patchQuotient_isOpenQuotientMap :
    IsOpenQuotientMap patchQuotient :=
  ⟨patchQuotient_surjective, patchQuotient_continuous,
    patchQuotient_isOpenMap⟩

noncomputable instance : SecondCountableTopology Carrier :=
  patchQuotient_isOpenQuotientMap.isQuotientMap.secondCountableTopology
    patchQuotient_isOpenMap

private noncomputable def polarMidpoint : PolarCollar := by
  have hs :
      (sphere (0 : EuclideanThree) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr zero_le_one
  exact
    ⟨⟨hs.choose, hs.choose_spec⟩,
      ⟨chartRadius / 2, half_pos chartRadius_pos,
        half_lt_self chartRadius_pos⟩⟩

noncomputable def seamPoint : collar :=
  collarPolar.symm polarMidpoint

theorem collarFlip_seamPoint :
    collarFlip seamPoint = seamPoint := by
  apply collarPolar.injective
  simp [collarFlip, seamPoint, polarMidpoint, polarFlip]
  ring

theorem patchInclusion_seamPoint :
    patchInclusion false seamPoint.1 =
      patchInclusion true (collarFlip seamPoint).1 := by
  set_option backward.isDefEq.respectTransparency false in
    exact (glueData.glue_condition_apply false true seamPoint).symm

noncomputable instance : PathConnectedSpace Carrier := by
  have hfalse :
      IsPathConnected (Set.range (patchInclusion false)) :=
    isPathConnected_range (patchInclusion false).continuous
  have htrue :
      IsPathConnected (Set.range (patchInclusion true)) :=
    isPathConnected_range (patchInclusion true).continuous
  have hinter :
      (Set.range (patchInclusion false) ∩ Set.range (patchInclusion true)).Nonempty := by
    refine
      ⟨patchInclusion false seamPoint.1,
        ⟨Set.mem_range_self seamPoint.1, ?_⟩⟩
    exact
      ⟨(collarFlip seamPoint).1, patchInclusion_seamPoint.symm⟩
  have hunion :
      Set.range (patchInclusion false) ∪ Set.range (patchInclusion true) =
        (Set.univ : Set Carrier) := by
    apply Set.eq_univ_of_forall
    intro x
    obtain ⟨i, y, hy⟩ := glueData.ι_jointly_surjective x
    cases i
    · exact Or.inl ⟨y, by
        set_option backward.isDefEq.respectTransparency false in
          exact hy⟩
    · exact Or.inr ⟨y, by
        set_option backward.isDefEq.respectTransparency false in
          exact hy⟩
  apply pathConnectedSpace_iff_univ.mpr
  rw [← hunion]
  exact hfalse.union htrue hinter

theorem collarFlip_radius (x : collar) :
    dist (punctureLocalChart (collarFlip x).1.1)
        punctureChartCenter =
      chartRadius -
        dist (punctureLocalChart x.1.1) punctureChartCenter := by
  have hpolar :
      collarPolar (collarFlip x) = polarFlip (collarPolar x) := by
    simp [collarFlip]
  have hr := congr_arg (fun z : PolarCollar => z.2.1) hpolar
  change
    (collarToPolar (collarFlip x)).2.1 =
      chartRadius - (collarToPolar x).2.1 at hr
  have hr' :
      ‖(collarOffset (collarFlip x) : EuclideanThree)‖ =
        chartRadius - ‖(collarOffset x : EuclideanThree)‖ := by
    simpa only [collarToPolar,
      homeomorphUnitSphereProd_apply_snd_coe] using hr
  simpa [collarOffset, dist_eq_norm, norm_sub_rev] using hr'

/--
In chart coordinates, the collar flip preserves direction and replaces radius
`r` by `chartRadius - r`.
-/
theorem collarFlip_offset (x : collar) :
    (collarOffset (collarFlip x) : EuclideanThree) =
      ((chartRadius - ‖(collarOffset x : EuclideanThree)‖) /
          ‖(collarOffset x : EuclideanThree)‖) •
        (collarOffset x : EuclideanThree) := by
  let z : PolarCollar := collarToPolar x
  have hzpos : 0 < z.2.1 := z.2.2.1
  have hznorm :
      ‖(collarOffset x : EuclideanThree)‖ = z.2.1 := by
    simp [z, collarToPolar]
  have hxoffset :
      (collarOffset x : EuclideanThree) =
        z.2.1 • (z.1 : EuclideanThree) := by
    calc
      (collarOffset x : EuclideanThree) =
          (polarOffset z : EuclideanThree) := by
        exact congr_arg Subtype.val (polarOffset_collarToPolar x).symm
      _ = z.2.1 • (z.1 : EuclideanThree) := by
        simp [polarOffset, polarUnitProduct]
  have hflipPolar :
      collarToPolar (collarFlip x) = polarFlip z := by
    change
      collarPolar
          (collarPolar.symm (polarFlip (collarPolar x))) =
        polarFlip z
    rw [collarPolar.apply_symm_apply]
    rfl
  have hflipOffset :
      (collarOffset (collarFlip x) : EuclideanThree) =
        (chartRadius - z.2.1) • (z.1 : EuclideanThree) := by
    calc
      (collarOffset (collarFlip x) : EuclideanThree) =
          (polarOffset (collarToPolar (collarFlip x)) :
            EuclideanThree) := by
        exact congr_arg Subtype.val
          (polarOffset_collarToPolar (collarFlip x)).symm
      _ = (polarOffset (polarFlip z) : EuclideanThree) := by
        rw [hflipPolar]
      _ = (chartRadius - z.2.1) •
          (z.1 : EuclideanThree) := by
        simp [polarOffset, polarUnitProduct, polarFlip]
  rw [hflipOffset, hznorm, hxoffset, smul_smul]
  congr 1
  field_simp

/-- A smaller chart ball removed to obtain a compact core. -/
noncomputable def innerBall : Opens SpaceForm where
  carrier :=
    punctureLocalChart.source ∩
      punctureLocalChart ⁻¹'
        ball punctureChartCenter (chartRadius / 2)
  is_open' :=
    punctureLocalChart.isOpen_inter_preimage isOpen_ball

private theorem puncture_mem_innerBall :
    puncture ∈ innerBall := by
  refine ⟨mem_chart_source EuclideanThree puncture, ?_⟩
  exact mem_ball'.2 (by
    rw [show punctureLocalChart puncture =
      punctureChartCenter from rfl, dist_self]
    exact half_pos chartRadius_pos)

abbrev CompactCore :=
  ((innerBall : Set SpaceForm)ᶜ : Set SpaceForm)

noncomputable local instance : CompactSpace CompactCore :=
  innerBall.isOpen.isClosed_compl.isClosedEmbedding_subtypeVal.compactSpace

noncomputable def compactCoreToPunctured
    (x : CompactCore) : Punctured :=
  ⟨x.1, by
    change x.1 ∈ ({puncture}ᶜ : Set SpaceForm)
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using
      (fun h : x.1 = puncture =>
        x.2 (h.symm ▸ puncture_mem_innerBall))⟩

private theorem collarFlip_mem_compactCore
    (x : collar)
    (hx :
      dist (punctureLocalChart x.1.1) punctureChartCenter <
        chartRadius / 2) :
    (collarFlip x).1.1 ∈ CompactCore := by
  intro hinner
  have hy :
      dist (punctureLocalChart (collarFlip x).1.1)
          punctureChartCenter <
        chartRadius / 2 :=
    hinner.2
  rw [collarFlip_radius x] at hy
  linarith

theorem patchInclusion_collarFlip (x : collar) :
    patchInclusion false x.1 =
      patchInclusion true (collarFlip x).1 := by
  set_option backward.isDefEq.respectTransparency false in
    exact (glueData.glue_condition_apply false true x).symm

/-- A compact two-core cover of the glued space. -/
noncomputable def compactCover :
    CompactCore ⊕ CompactCore → Carrier :=
  Sum.elim
    (fun x => patchInclusion false (compactCoreToPunctured x))
    (fun x => patchInclusion true (compactCoreToPunctured x))

theorem compactCover_continuous : Continuous compactCover :=
  continuous_sumElim.mpr
    ⟨(patchInclusion false).continuous.comp
        (continuous_subtype_val.subtype_mk _),
      (patchInclusion true).continuous.comp
        (continuous_subtype_val.subtype_mk _)⟩

theorem compactCover_surjective :
    Function.Surjective compactCover := by
  intro z
  obtain ⟨x, rfl⟩ := patchQuotient_surjective z
  cases x with
  | inl x =>
      by_cases hx : x.1 ∈ innerBall
      · have hxcollar : x ∈ collar :=
          ⟨hx.1,
            mem_ball'.2 <|
              (mem_ball'.1 hx.2).trans <|
                half_lt_self chartRadius_pos⟩
        let xc : collar := ⟨x, hxcollar⟩
        let y : CompactCore :=
          ⟨(collarFlip xc).1.1,
            collarFlip_mem_compactCore xc hx.2⟩
        refine ⟨Sum.inr y, ?_⟩
        simpa [compactCover, patchQuotient, y, compactCoreToPunctured] using
          (patchInclusion_collarFlip xc).symm
      · let y : CompactCore := ⟨x.1, hx⟩
        exact ⟨Sum.inl y, rfl⟩
  | inr x =>
      by_cases hx : x.1 ∈ innerBall
      · have hxcollar : x ∈ collar :=
          ⟨hx.1,
            mem_ball'.2 <|
              (mem_ball'.1 hx.2).trans <|
                half_lt_self chartRadius_pos⟩
        let xc : collar := ⟨x, hxcollar⟩
        let y : CompactCore :=
          ⟨(collarFlip xc).1.1,
            collarFlip_mem_compactCore xc hx.2⟩
        refine ⟨Sum.inl y, ?_⟩
        simpa [compactCover, patchQuotient, y, compactCoreToPunctured,
          collarFlip_involutive] using
            patchInclusion_collarFlip (collarFlip xc)
      · let y : CompactCore := ⟨x.1, hx⟩
        exact ⟨Sum.inr y, rfl⟩

noncomputable instance : CompactSpace Carrier :=
  compactCover_surjective.compactSpace compactCover_continuous

/--
The closed half-radius chart ball, transported back to the spherical space
form.  Its complement supplies uniform exterior neighborhoods on the two
patches.
-/
noncomputable def halfChartImage : Set SpaceForm :=
  punctureLocalChart.symm ''
    closedBall punctureChartCenter (chartRadius / 2)

private theorem closedBall_half_subset_target :
    closedBall punctureChartCenter (chartRadius / 2) ⊆
      punctureLocalChart.target := by
  intro y hy
  apply closedBall_chartRadius_subset
  rw [mem_closedBall'] at hy ⊢
  exact hy.trans (half_le_self chartRadius_pos.le)

private theorem halfChartImage_isClosed :
    IsClosed halfChartImage := by
  apply IsCompact.isClosed
  exact
    (isCompact_closedBall punctureChartCenter (chartRadius / 2)).image_of_continuousOn
      (punctureLocalChart.symm.continuousOn.mono
        closedBall_half_subset_target)

/--
Points outside the closed half-radius chart core.  Every point outside the
full collar belongs to this open set.
-/
noncomputable def exterior : Opens Punctured where
  carrier := Subtype.val ⁻¹' halfChartImageᶜ
  is_open' :=
    halfChartImage_isClosed.isOpen_compl.preimage continuous_subtype_val

private theorem mem_exterior_of_not_mem_collar
    {x : Punctured} (hx : x ∉ collar) :
    x ∈ exterior := by
  change x.1 ∉ halfChartImage
  intro hhalf
  rcases hhalf with ⟨y, hy, hxy⟩
  have hytarget : y ∈ punctureLocalChart.target :=
    closedBall_half_subset_target hy
  have hxsource : x.1 ∈ punctureLocalChart.source := by
    rw [← hxy]
    exact punctureLocalChart.map_target hytarget
  have hchart : punctureLocalChart x.1 = y := by
    rw [← hxy]
    exact punctureLocalChart.right_inv hytarget
  apply hx
  refine ⟨hxsource, ?_⟩
  rw [mem_ball', hchart]
  exact (mem_closedBall'.1 hy).trans_lt
    (half_lt_self chartRadius_pos)

private theorem half_lt_radius_of_mem_exterior
    (x : Punctured) (hx : x ∈ exterior) (hc : x ∈ collar) :
    chartRadius / 2 <
      dist (punctureLocalChart x.1) punctureChartCenter := by
  rw [lt_iff_not_ge]
  intro hr
  change x.1 ∉ halfChartImage at hx
  apply hx
  refine
    ⟨punctureLocalChart x.1,
      mem_closedBall'.2 (by simpa [dist_comm] using hr), ?_⟩
  exact punctureLocalChart.left_inv hc.1

theorem patchInclusion_cross_data
    {x y : Punctured}
    (hxy : patchInclusion false x = patchInclusion true y) :
    ∃ z : collar,
      z.1 = x ∧ (collarFlip z).1 = y := by
  have hxy' :
      glueData.toGlueData.ι false x =
        glueData.toGlueData.ι true y := by
    set_option backward.isDefEq.respectTransparency false in
      exact hxy
  rcases (glueData.ι_eq_iff_rel false true x y).mp hxy' with
    ⟨z, hzx, hzy⟩
  exact ⟨z, hzx, hzy⟩

private theorem separated_patch_false_true
    (x y : Punctured)
    (hxy : patchInclusion false x ≠ patchInclusion true y) :
    ∃ u v : Set Carrier,
      IsOpen u ∧ IsOpen v ∧
        patchInclusion false x ∈ u ∧
        patchInclusion true y ∈ v ∧
        Disjoint u v := by
  by_cases hx : x ∈ collar
  · let z : collar := ⟨x, hx⟩
    have heq :
        patchInclusion false x =
          patchInclusion true (collarFlip z).1 := by
      simpa [z] using patchInclusion_collarFlip z
    have hne :
        patchInclusion true (collarFlip z).1 ≠
          patchInclusion true y := by
      intro h
      exact hxy (heq.trans h)
    obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ :=
      separated_by_isOpenEmbedding
        (patchInclusion_isOpenEmbedding true)
        (x := (collarFlip z).1) (y := y)
        (fun h => hne (congr_arg (patchInclusion true) h))
    exact ⟨u, v, hu, hv, heq.symm ▸ hxu, hyv, huv⟩
  · by_cases hy : y ∈ collar
    · let z : collar := ⟨y, hy⟩
      have heq :
          patchInclusion false (collarFlip z).1 =
            patchInclusion true y := by
        calc
          patchInclusion false (collarFlip z).1 =
              patchInclusion true
                (collarFlip (collarFlip z)).1 :=
            patchInclusion_collarFlip (collarFlip z)
          _ = patchInclusion true y := by
            rw [collarFlip_involutive z]
      have hne :
          patchInclusion false x ≠
            patchInclusion false (collarFlip z).1 := by
        intro h
        exact hxy (h.trans heq)
      obtain ⟨u, v, hu, hv, hxu, hyv, huv⟩ :=
        separated_by_isOpenEmbedding
          (patchInclusion_isOpenEmbedding false)
          (x := x) (y := (collarFlip z).1)
          (fun h => hne (congr_arg (patchInclusion false) h))
      exact ⟨u, v, hu, hv, hxu, heq ▸ hyv, huv⟩
    · have hxext : x ∈ exterior :=
        mem_exterior_of_not_mem_collar hx
      have hyext : y ∈ exterior :=
        mem_exterior_of_not_mem_collar hy
      refine
        ⟨patchInclusion false '' exterior,
          patchInclusion true '' exterior,
          (patchInclusion_isOpenEmbedding false).isOpenMap
            exterior exterior.isOpen,
          (patchInclusion_isOpenEmbedding true).isOpenMap
            exterior exterior.isOpen,
          ⟨x, hxext, rfl⟩, ⟨y, hyext, rfl⟩, ?_⟩
      rw [Set.disjoint_left]
      rintro w ⟨a, ha, haw⟩ ⟨b, hb, hbw⟩
      have hab :
          patchInclusion false a =
            patchInclusion true b :=
        haw.trans hbw.symm
      obtain ⟨z, hza, hzb⟩ :=
        patchInclusion_cross_data hab
      subst a
      subst b
      have hra :=
        half_lt_radius_of_mem_exterior z.1 ha z.2
      have hrb :=
        half_lt_radius_of_mem_exterior
          (collarFlip z).1 hb (collarFlip z).2
      have hflip := collarFlip_radius z
      linarith

noncomputable instance : T2Space Carrier where
  t2 x y hxy := by
    obtain ⟨i, a, rfl⟩ := glueData.ι_jointly_surjective x
    obtain ⟨j, b, rfl⟩ := glueData.ι_jointly_surjective y
    cases i <;> cases j
    · apply separated_by_isOpenEmbedding
        (patchInclusion_isOpenEmbedding false)
      intro hab
      apply hxy
      simp [hab]
    · exact separated_patch_false_true a b <| by
        set_option backward.isDefEq.respectTransparency false in
          exact hxy
    · obtain ⟨u, v, hu, hv, hbu, hav, huv⟩ :=
        separated_patch_false_true b a <| by
          set_option backward.isDefEq.respectTransparency false in
            exact hxy.symm
      exact ⟨v, u, hv, hu, hav, hbu, huv.symm⟩
    · apply separated_by_isOpenEmbedding
        (patchInclusion_isOpenEmbedding true)
      intro hab
      apply hxy
      simp [hab]

end
end Submission.ConnectedSum
