import Submission.ConnectedSum
import Mathlib.Topology.Piecewise

/-!
# Retractions of the connected sum

The collar flip extends continuously across the rest of a punctured summand
by sending the exterior to the puncture.  This supplies maps from the
connected sum back to either spherical space-form summand.
-/

open Metric

namespace Submission.ConnectedSumRetraction

open QuaternionSpaceForm
open ConnectedSum

noncomputable section

noncomputable local instance : ChartedSpace EuclideanThree SpaceForm :=
  QuaternionSpaceForm.closed3Manifold.charted

/-- The closed chart ball supporting the extended collar flip. -/
noncomputable def closedCollarImage : Set SpaceForm :=
  punctureLocalChart.symm ''
    closedBall punctureChartCenter chartRadius

private theorem closedCollarImage_isClosed :
    IsClosed closedCollarImage := by
  apply IsCompact.isClosed
  exact
    (isCompact_closedBall punctureChartCenter chartRadius).image_of_continuousOn
      (punctureLocalChart.symm.continuousOn.mono
        closedBall_chartRadius_subset)

private def closedCollar : Set Punctured :=
  Subtype.val ⁻¹' closedCollarImage

private theorem closedCollar_isClosed :
    IsClosed closedCollar :=
  closedCollarImage_isClosed.preimage continuous_subtype_val

private theorem collar_subset_closedCollar :
    (collar : Set Punctured) ⊆ closedCollar := by
  intro x hx
  refine
    ⟨punctureLocalChart x.1,
      mem_closedBall'.2 (mem_ball'.1 hx.2).le, ?_⟩
  exact punctureLocalChart.left_inv hx.1

private theorem closure_collar_subset_closedCollar :
    closure (collar : Set Punctured) ⊆ closedCollar :=
  closure_minimal collar_subset_closedCollar closedCollar_isClosed

private theorem source_of_mem_closedCollar
    {x : Punctured} (hx : x ∈ closedCollar) :
    x.1 ∈ punctureLocalChart.source := by
  rcases hx with ⟨y, hy, hxy⟩
  rw [← hxy]
  exact punctureLocalChart.map_target <|
    closedBall_chartRadius_subset hy

private theorem chart_mem_closedBall_of_mem_closedCollar
    {x : Punctured} (hx : x ∈ closedCollar) :
    punctureLocalChart x.1 ∈
      closedBall punctureChartCenter chartRadius := by
  rcases hx with ⟨y, hy, hxy⟩
  have hytarget : y ∈ punctureLocalChart.target :=
    closedBall_chartRadius_subset hy
  rw [← hxy, punctureLocalChart.right_inv hytarget]
  exact hy

/-- The chart offset of a point in the punctured summand. -/
noncomputable def rawOffset (x : Punctured) : EuclideanThree :=
  punctureLocalChart x.1 - punctureChartCenter

private theorem rawOffset_ne_zero_of_mem_closedCollar
    {x : Punctured} (hx : x ∈ closedCollar) :
    rawOffset x ≠ 0 := by
  intro hzero
  have hsource := source_of_mem_closedCollar hx
  have hchart :
      punctureLocalChart x.1 = punctureChartCenter :=
    sub_eq_zero.mp hzero
  have hxp : x.1 = puncture :=
    punctureLocalChart.injOn hsource
      (mem_chart_source EuclideanThree puncture) hchart
  exact x.2 hxp

/-- Radial extension of the collar flip in chart coordinates. -/
noncomputable def collapseCoordinate (x : Punctured) : EuclideanThree :=
  ((chartRadius - ‖rawOffset x‖) / ‖rawOffset x‖) •
      rawOffset x +
    punctureChartCenter

private theorem collapseCoordinate_mem_closedBall
    {x : Punctured} (hx : x ∈ closedCollar) :
    collapseCoordinate x ∈
      closedBall punctureChartCenter chartRadius := by
  have hball := chart_mem_closedBall_of_mem_closedCollar hx
  have hle :
      ‖rawOffset x‖ ≤ chartRadius := by
    rw [mem_closedBall', dist_eq_norm] at hball
    simpa [rawOffset, norm_sub_rev] using hball
  have hpos : 0 < ‖rawOffset x‖ := by
    exact norm_pos_iff.mpr (rawOffset_ne_zero_of_mem_closedCollar hx)
  rw [mem_closedBall', dist_eq_norm]
  have hsub :
      punctureChartCenter - collapseCoordinate x =
        -(((chartRadius - ‖rawOffset x‖) / ‖rawOffset x‖) •
          rawOffset x) := by
    simp [collapseCoordinate, sub_eq_add_neg, add_comm]
  rw [hsub, norm_neg, norm_smul, Real.norm_eq_abs,
    abs_of_nonneg (div_nonneg (sub_nonneg.mpr hle) (norm_nonneg _))]
  rw [div_mul_cancel₀ _ hpos.ne']
  linarith [norm_nonneg (rawOffset x)]

private theorem collapseCoordinate_mem_target
    {x : Punctured} (hx : x ∈ closedCollar) :
    collapseCoordinate x ∈ punctureLocalChart.target :=
  closedBall_chartRadius_subset <|
    collapseCoordinate_mem_closedBall hx

/-- The radial formula before it is glued to the exterior puncture map. -/
noncomputable def collapseFormula (x : Punctured) : SpaceForm :=
  punctureLocalChart.symm (collapseCoordinate x)

private theorem collapseFormula_continuousOn :
    ContinuousOn collapseFormula
      (closure (collar : Set Punctured)) := by
  have hoffset :
      ContinuousOn rawOffset
        (closure (collar : Set Punctured)) := by
    exact
      (punctureLocalChart.continuousOn.comp
        continuous_subtype_val.continuousOn fun x hx =>
          source_of_mem_closedCollar
            (closure_collar_subset_closedCollar hx)).sub
        continuousOn_const
  have hnorm :
      ContinuousOn (fun x : Punctured => ‖rawOffset x‖)
        (closure (collar : Set Punctured)) :=
    hoffset.norm
  have hscalar :
      ContinuousOn
        (fun x : Punctured =>
          (chartRadius - ‖rawOffset x‖) / ‖rawOffset x‖)
        (closure (collar : Set Punctured)) :=
    (continuousOn_const.sub hnorm).div hnorm fun x hx =>
      (norm_pos_iff.mpr <|
        rawOffset_ne_zero_of_mem_closedCollar <|
          closure_collar_subset_closedCollar hx).ne'
  have hcoordinate :
      ContinuousOn collapseCoordinate
        (closure (collar : Set Punctured)) :=
    (hscalar.smul hoffset).add continuousOn_const
  exact
    punctureLocalChart.symm.continuousOn.comp hcoordinate fun x hx =>
      collapseCoordinate_mem_target <|
        closure_collar_subset_closedCollar hx

private theorem collapseFormula_eq_puncture_of_frontier
    (x : Punctured) (hx : x ∈ frontier (collar : Set Punctured)) :
    collapseFormula x = puncture := by
  have hxclosure : x ∈ closure (collar : Set Punctured) :=
    frontier_subset_closure hx
  have hxclosed : x ∈ closedCollar :=
    closure_collar_subset_closedCollar hxclosure
  have hxsource := source_of_mem_closedCollar hxclosed
  have hxball := chart_mem_closedBall_of_mem_closedCollar hxclosed
  have hxnot : x ∉ collar := by
    rw [collar.isOpen.frontier_eq] at hx
    exact hx.2
  have hge :
      chartRadius ≤
        dist (punctureLocalChart x.1) punctureChartCenter := by
    apply le_of_not_gt
    intro hlt
    exact hxnot
      ⟨hxsource, mem_ball'.2 (by simpa [dist_comm] using hlt)⟩
  have hle :
      dist (punctureLocalChart x.1) punctureChartCenter ≤
        chartRadius := by
    have hle' := mem_closedBall'.1 hxball
    simpa [dist_comm] using hle'
  have hradius :
      ‖rawOffset x‖ = chartRadius := by
    rw [← le_antisymm hle hge, dist_eq_norm]
    simp [rawOffset, norm_sub_rev]
  rw [collapseFormula]
  have hcoordinate :
      collapseCoordinate x = punctureChartCenter := by
    simp [collapseCoordinate, hradius]
  rw [hcoordinate]
  exact punctureLocalChart.left_inv
    (mem_chart_source EuclideanThree puncture)

/--
The collar flip extended by the puncture on the exterior of the collar.
-/
noncomputable def collapse (x : Punctured) : SpaceForm :=
  by
    classical
    exact if x ∈ collar then collapseFormula x else puncture

theorem collapse_continuous : Continuous collapse := by
  classical
  unfold collapse
  apply continuous_if
  · exact collapseFormula_eq_puncture_of_frontier
  · exact collapseFormula_continuousOn
  · exact continuous_const.continuousOn

theorem collapse_of_mem_collar
    (x : Punctured) (hx : x ∈ collar) :
    collapse x = (collarFlip ⟨x, hx⟩).1.1 := by
  rw [collapse, if_pos hx, collapseFormula]
  let xc : collar := ⟨x, hx⟩
  have hoffset := collarFlip_offset xc
  have hcoordinate :
      collapseCoordinate x =
        punctureLocalChart (collarFlip xc).1.1 := by
    rw [collapseCoordinate]
    change
      ((chartRadius -
            ‖(collarOffset xc : EuclideanThree)‖) /
          ‖(collarOffset xc : EuclideanThree)‖) •
            (collarOffset xc : EuclideanThree) +
          punctureChartCenter =
        punctureLocalChart (collarFlip xc).1.1
    rw [← hoffset]
    simp [collarOffset]
  rw [hcoordinate]
  exact punctureLocalChart.left_inv (collarFlip xc).2.1

/--
On the selected summand this is the inclusion into the original space form;
on the other summand it is the extended collar flip.
-/
noncomputable def summandMap :
    Bool → C(Punctured ⊕ Punctured, SpaceForm)
  | false =>
      ⟨Sum.elim Subtype.val collapse,
        continuous_sumElim.mpr
          ⟨continuous_subtype_val, collapse_continuous⟩⟩
  | true =>
      ⟨Sum.elim collapse Subtype.val,
        continuous_sumElim.mpr
          ⟨collapse_continuous, continuous_subtype_val⟩⟩

private theorem summandMap_factorsThrough (i : Bool) :
    Function.FactorsThrough (summandMap i) patchQuotient := by
  intro a b hab
  cases a with
  | inl a =>
      cases b with
      | inl b =>
          have hab' :
              patchInclusion false a =
                patchInclusion false b := by
            simpa [patchQuotient] using hab
          have hab'' : a = b :=
            (patchInclusion_isOpenEmbedding false).injective hab'
          subst b
          rfl
      | inr b =>
          have hab' :
              patchInclusion false a =
                patchInclusion true b := by
            simpa [patchQuotient] using hab
          obtain ⟨z, hza, hzb⟩ :=
            patchInclusion_cross_data hab'
          subst a
          subst b
          cases i
          · change z.1.1 = collapse (collarFlip z).1
            rw [collapse_of_mem_collar
              (collarFlip z).1 (collarFlip z).2]
            exact congr_arg (fun w : collar => w.1.1)
              (collarFlip_involutive z).symm
          · change collapse z.1 = (collarFlip z).1.1
            exact collapse_of_mem_collar z.1 z.2
  | inr a =>
      cases b with
      | inl b =>
          have hab' :
              patchInclusion false b =
                patchInclusion true a := by
            simpa [patchQuotient] using hab.symm
          obtain ⟨z, hzb, hza⟩ :=
            patchInclusion_cross_data hab'
          subst b
          subst a
          cases i
          · change collapse (collarFlip z).1 = z.1.1
            rw [collapse_of_mem_collar
              (collarFlip z).1 (collarFlip z).2]
            exact congr_arg (fun w : collar => w.1.1)
              (collarFlip_involutive z)
          · change (collarFlip z).1.1 = collapse z.1
            exact (collapse_of_mem_collar z.1 z.2).symm
      | inr b =>
          have hab' :
              patchInclusion true a =
                patchInclusion true b := by
            simpa [patchQuotient] using hab
          have hab'' : a = b :=
            (patchInclusion_isOpenEmbedding true).injective hab'
          subst b
          rfl

private noncomputable def patchQuotientMap :
    C(Punctured ⊕ Punctured, Carrier) :=
  ⟨patchQuotient, patchQuotient_continuous⟩

private theorem patchQuotientMap_isQuotientMap :
    Topology.IsQuotientMap patchQuotientMap :=
  patchQuotient_isOpenQuotientMap.isQuotientMap

private theorem summandMap_factorsThroughMap (i : Bool) :
    Function.FactorsThrough (summandMap i) patchQuotientMap := by
  intro a b hab
  exact summandMap_factorsThrough i hab

/-- Collapse the connected sum onto either original spherical space form. -/
noncomputable def retraction (i : Bool) : C(Carrier, SpaceForm) :=
  Topology.IsQuotientMap.lift (f := patchQuotientMap)
    patchQuotientMap_isQuotientMap (summandMap i)
      (summandMap_factorsThroughMap i)

private theorem retraction_patchQuotientMap
    (i : Bool) (z : Punctured ⊕ Punctured) :
    retraction i (patchQuotientMap z) = summandMap i z := by
  have h :=
    Topology.IsQuotientMap.lift_comp (f := patchQuotientMap)
      patchQuotientMap_isQuotientMap
      (summandMap i) (summandMap_factorsThroughMap i)
  exact congr_arg
    (fun f : C(Punctured ⊕ Punctured, SpaceForm) => f z) h

theorem retraction_patch_false (x : Punctured) :
    retraction false (patchInclusion false x) = x.1 := by
  set_option backward.isDefEq.respectTransparency false in
    exact retraction_patchQuotientMap false (Sum.inl x)

theorem retraction_patch_true (x : Punctured) :
    retraction true (patchInclusion true x) = x.1 := by
  set_option backward.isDefEq.respectTransparency false in
    exact retraction_patchQuotientMap true (Sum.inr x)

theorem retraction_false_patch_true (x : Punctured) :
    retraction false (patchInclusion true x) = collapse x := by
  set_option backward.isDefEq.respectTransparency false in
    exact retraction_patchQuotientMap false (Sum.inr x)

theorem retraction_true_patch_false (x : Punctured) :
    retraction true (patchInclusion false x) = collapse x := by
  set_option backward.isDefEq.respectTransparency false in
    exact retraction_patchQuotientMap true (Sum.inl x)

theorem retraction_patch_same (i : Bool) (x : Punctured) :
    retraction i (patchInclusion i x) = x.1 := by
  cases i
  · exact retraction_patch_false x
  · exact retraction_patch_true x

theorem retraction_patch_other (i : Bool) (x : Punctured) :
    retraction i (patchInclusion (!i) x) = collapse x := by
  cases i
  · exact retraction_false_patch_true x
  · exact retraction_true_patch_false x

end
end Submission.ConnectedSumRetraction
