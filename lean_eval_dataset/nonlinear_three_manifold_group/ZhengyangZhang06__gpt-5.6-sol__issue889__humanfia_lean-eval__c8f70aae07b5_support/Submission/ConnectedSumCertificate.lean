import Submission.ConnectedSumRetraction
import Submission.Helpers
import Submission.PuncturedQuaternion

/-!
# Quaternion factors in the connected sum

Both punctured summands carry the quaternion subgroup.  We move its basepoint
to the fixed midpoint of the gluing collar, map it into the connected sum,
and use the two summand retractions to prove that both copies remain embedded.
-/

open LeanEval.Topology
open Matrix
open CategoryTheory

namespace Submission.ConnectedSumCertificate

open QuaternionObstruction
open QuaternionSpaceForm
open QuaternionPaths
open QuaternionHomotopy
open ConnectedSum
open ConnectedSumRetraction
open PuncturedQuaternion

noncomputable section

private theorem fundamentalGroupMulEquivOfPath_fromPath
    {X : Type*} [TopologicalSpace X] {x y : X}
    (p : Path x y) (q : Path x x) :
    FundamentalGroup.fundamentalGroupMulEquivOfPath p
        (FundamentalGroup.fromPath (.mk q)) =
      FundamentalGroup.fromPath
        (.mk ((p.symm.trans q).trans p)) := by
  let α : FundamentalGroupoid.mk x ≅ FundamentalGroupoid.mk y :=
    (Groupoid.isoEquivHom _ _).symm
      (Path.Homotopic.Quotient.mk p)
  change
    α.conj (FundamentalGroup.fromPath
      (Path.Homotopic.Quotient.mk q)) =
      FundamentalGroup.fromPath
        (Path.Homotopic.Quotient.mk
          ((p.symm.trans q).trans p))
  rw [CategoryTheory.Iso.conj_apply]
  have hhom :
      α.hom = Path.Homotopic.Quotient.mk p := rfl
  have hinv :
      α.inv = Path.Homotopic.Quotient.mk p.symm := rfl
  rw [hhom, hinv, FundamentalGroupoid.comp_eq,
    FundamentalGroupoid.comp_eq,
    ← Path.Homotopic.Quotient.trans_assoc]
  rfl

/-- The Q8 subgroup after inclusion into the unpunctured space form. -/
noncomputable def spaceSupportedQ8Hom :
    Q8 →* FundamentalGroup SpaceForm basepoint :=
  puncturedToSpaceHom.comp puncturedQ8Hom

theorem spaceSupportedQ8Hom_apply (q : Q8) :
    spaceSupportedQ8Hom q = spaceSupportedElement q⁻¹ := by
  simp [spaceSupportedQ8Hom, puncturedQ8Hom,
    puncturedToSpaceHom_element]

theorem spaceSupportedQ8Hom_injective :
    Function.Injective spaceSupportedQ8Hom := by
  intro q r hqr
  rw [spaceSupportedQ8Hom_apply,
    spaceSupportedQ8Hom_apply] at hqr
  have hinv : q⁻¹ = r⁻¹ := by
    apply fiberPoint_injective
    rw [← spaceSupportedElement_monodromy q⁻¹,
      ← spaceSupportedElement_monodromy r⁻¹, hqr]
  exact inv_injective hinv

/-- A connector from the original quotient basepoint to the gluing seam. -/
noncomputable def baseToSeam :
    Path puncturedBasepoint seamPoint.1 :=
  PathConnectedSpace.somePath puncturedBasepoint seamPoint.1

/-- Conjugate a punctured loop to the seam basepoint. -/
noncomputable def seamLoop (q : Q8) :
    Path seamPoint.1 seamPoint.1 :=
  ((baseToSeam.symm.trans (puncturedLoop q))).trans baseToSeam

/-- The punctured quaternion subgroup based at the seam. -/
noncomputable def seamQ8Hom :
    Q8 →* FundamentalGroup Punctured seamPoint.1 :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      baseToSeam).toMonoidHom.comp
    puncturedQ8Hom

theorem seamQ8Hom_apply (q : Q8) :
    seamQ8Hom q =
      FundamentalGroup.fromPath
        (.mk (seamLoop q⁻¹)) := by
  set_option backward.isDefEq.respectTransparency false in
    change
      FundamentalGroup.fundamentalGroupMulEquivOfPath
          baseToSeam
          (FundamentalGroup.fromPath
            (.mk (puncturedLoop q⁻¹))) =
        FundamentalGroup.fromPath
          (.mk (seamLoop q⁻¹))
  simpa only [seamLoop] using
    fundamentalGroupMulEquivOfPath_fromPath
      baseToSeam (puncturedLoop q⁻¹)

theorem seamQ8Hom_injective :
    Function.Injective seamQ8Hom :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      baseToSeam).injective.comp
    puncturedQ8Hom_injective

/-- The common seam point in the connected sum. -/
noncomputable def carrierBasepoint : Carrier :=
  patchInclusion false seamPoint.1

theorem patch_true_seam_eq :
    patchInclusion true seamPoint.1 = carrierBasepoint := by
  have h := patchInclusion_seamPoint
  rw [collarFlip_seamPoint] at h
  exact h.symm

theorem patch_seam_eq (i : Bool) :
    patchInclusion i seamPoint.1 = carrierBasepoint := by
  cases i
  · rfl
  · exact patch_true_seam_eq

/-- A loop from one quaternion factor, now based at the common seam point. -/
noncomputable def factorLoop (i : Bool) (q : Q8) :
    Path carrierBasepoint carrierBasepoint :=
  ((seamLoop q).map (patchInclusion i).continuous).cast
    (patch_seam_eq i).symm (patch_seam_eq i).symm

/-- The two quaternion factor inclusions into the connected-sum group. -/
noncomputable def factorInclusion (i : Bool) :
    Q8 →* FundamentalGroup Carrier carrierBasepoint :=
  (FundamentalGroup.mapOfEq (patchInclusion i)
      (patch_seam_eq i)).comp
    seamQ8Hom

theorem factorInclusion_apply (i : Bool) (q : Q8) :
    factorInclusion i q =
      FundamentalGroup.fromPath
        (.mk (factorLoop i q⁻¹)) := by
  rw [factorInclusion, MonoidHom.comp_apply, seamQ8Hom_apply,
    FundamentalGroup.mapOfEq_apply]
  rfl

theorem retraction_basepoint_eq (i : Bool) :
    retraction i carrierBasepoint = seamPoint.1.1 := by
  cases i
  · exact retraction_patch_false seamPoint.1
  · rw [← patch_true_seam_eq]
    exact retraction_patch_true seamPoint.1

/-- The homomorphism on fundamental groups induced by one summand retraction. -/
noncomputable def retractionHom (i : Bool) :
    FundamentalGroup Carrier carrierBasepoint →*
      FundamentalGroup SpaceForm seamPoint.1.1 :=
  FundamentalGroup.mapOfEq (retraction i)
    (retraction_basepoint_eq i)

/-- The corresponding connector and quaternion subgroup in the space form. -/
noncomputable def spaceBaseToSeam :
    Path basepoint seamPoint.1.1 :=
  baseToSeam.map puncturedInclusion.continuous

noncomputable def spaceSeamLoop (q : Q8) :
    Path seamPoint.1.1 seamPoint.1.1 :=
  seamLoop q |>.map puncturedInclusion.continuous

noncomputable def spaceSeamQ8Hom :
    Q8 →* FundamentalGroup SpaceForm seamPoint.1.1 :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      spaceBaseToSeam).toMonoidHom.comp
    spaceSupportedQ8Hom

theorem spaceSeamQ8Hom_apply (q : Q8) :
    spaceSeamQ8Hom q =
      FundamentalGroup.fromPath
        (.mk (spaceSeamLoop q⁻¹)) := by
  rw [spaceSeamQ8Hom, MonoidHom.comp_apply,
    spaceSupportedQ8Hom_apply, spaceSupportedElement]
  have hpath :
      ((spaceBaseToSeam.symm.trans
          (spaceSupportedLoop q⁻¹)).trans
        spaceBaseToSeam) =
      spaceSeamLoop q⁻¹ := by
    rw [spaceBaseToSeam,
      ← puncturedLoop_map_inclusion,
      spaceSeamLoop, seamLoop,
      Path.map_trans, Path.map_trans]
    apply Path.ext
    funext t
    set_option backward.isDefEq.respectTransparency false in
      rfl
  calc
    FundamentalGroup.fundamentalGroupMulEquivOfPath
          spaceBaseToSeam
          (FundamentalGroup.fromPath
            (.mk (spaceSupportedLoop q⁻¹))) =
        FundamentalGroup.fromPath
          (.mk ((spaceBaseToSeam.symm.trans
            (spaceSupportedLoop q⁻¹)).trans
              spaceBaseToSeam)) :=
      fundamentalGroupMulEquivOfPath_fromPath
        spaceBaseToSeam (spaceSupportedLoop q⁻¹)
    _ = FundamentalGroup.fromPath
          (.mk (spaceSeamLoop q⁻¹)) :=
      congr_arg FundamentalGroup.fromPath <|
        congr_arg Path.Homotopic.Quotient.mk hpath

theorem spaceSeamQ8Hom_injective :
    Function.Injective spaceSeamQ8Hom :=
  (FundamentalGroup.fundamentalGroupMulEquivOfPath
      spaceBaseToSeam).injective.comp
    spaceSupportedQ8Hom_injective

theorem retractionHom_factorInclusion
    (i : Bool) (q : Q8) :
    retractionHom i (factorInclusion i q) =
      spaceSeamQ8Hom q := by
  rw [factorInclusion_apply, retractionHom,
    FundamentalGroup.mapOfEq_apply,
    spaceSeamQ8Hom_apply]
  have hpath :
      ((factorLoop i q⁻¹).map
          (retraction i).continuous).cast
        (retraction_basepoint_eq i).symm
        (retraction_basepoint_eq i).symm =
      spaceSeamLoop q⁻¹ := by
    apply Path.ext
    funext t
    exact retraction_patch_same i (seamLoop q⁻¹ t)
  exact congr_arg FundamentalGroup.fromPath <|
    congr_arg Path.Homotopic.Quotient.mk hpath

theorem factorInclusion_injective (i : Bool) :
    Function.Injective (factorInclusion i) := by
  intro q r hqr
  apply spaceSeamQ8Hom_injective
  rw [← retractionHom_factorInclusion i q,
    ← retractionHom_factorInclusion i r, hqr]

private theorem puncturedLoop_mem_supportedTrace
    (q : Q8) (t) :
    (puncturedLoop q t).1 ∈ supportedTrace := by
  rw [supportedTrace, Set.mem_iUnion]
  exact ⟨q, ⟨t, rfl⟩⟩

private theorem puncturedLoop_not_mem_collar
    (q : Q8) (t) :
    puncturedLoop q t ∉ collar := by
  intro hcollar
  exact
    (collar_avoids_supportedTrace
      (puncturedLoop q t) hcollar)
      (puncturedLoop_mem_supportedTrace q t)

theorem collapse_puncturedLoop_point (q : Q8) (t) :
    collapse (puncturedLoop q t) = puncture := by
  rw [collapse, if_neg (puncturedLoop_not_mem_collar q t)]

theorem collapse_puncturedBasepoint :
    collapse puncturedBasepoint = puncture := by
  have h := collapse_puncturedLoop_point 1 0
  rwa [(puncturedLoop 1).source] at h

theorem collapse_seamPoint :
    collapse seamPoint.1 = seamPoint.1.1 := by
  rw [collapse_of_mem_collar seamPoint.1 seamPoint.2,
    collarFlip_seamPoint]

/-- The image of the basepoint connector under the collar collapse. -/
noncomputable def collapsedConnector :
    Path puncture seamPoint.1.1 :=
  (baseToSeam.map collapse_continuous).cast
    collapse_puncturedBasepoint.symm collapse_seamPoint.symm

noncomputable def collapsedPuncturedLoop (q : Q8) :
    Path puncture puncture :=
  ((puncturedLoop q).map collapse_continuous).cast
    collapse_puncturedBasepoint.symm
    collapse_puncturedBasepoint.symm

theorem collapsedPuncturedLoop_eq_refl (q : Q8) :
    collapsedPuncturedLoop q = Path.refl puncture := by
  apply Path.ext
  funext t
  exact collapse_puncturedLoop_point q t

noncomputable def collapsedSeamLoop (q : Q8) :
    Path seamPoint.1.1 seamPoint.1.1 :=
  ((seamLoop q).map collapse_continuous).cast
    collapse_seamPoint.symm collapse_seamPoint.symm

private theorem collapsedSeamLoop_decomp (q : Q8) :
    collapsedSeamLoop q =
      ((collapsedConnector.symm.trans
        (collapsedPuncturedLoop q))).trans
          collapsedConnector := by
  apply Path.ext
  funext t
  simp only [collapsedSeamLoop, collapsedConnector,
    collapsedPuncturedLoop, seamLoop, Path.cast_coe,
    Path.map_coe, Function.comp_apply, Path.trans_apply,
    Path.symm_apply]
  split_ifs <;> rfl

theorem collapsedSeamLoop_homotopic_refl (q : Q8) :
    (collapsedSeamLoop q).Homotopic
      (Path.refl seamPoint.1.1) := by
  rw [collapsedSeamLoop_decomp,
    collapsedPuncturedLoop_eq_refl]
  have hremove :
      ((collapsedConnector.symm.trans
          (Path.refl puncture)).trans
        collapsedConnector).Homotopic
      (collapsedConnector.symm.trans
        collapsedConnector) :=
    (show
      (collapsedConnector.symm.trans
        (Path.refl puncture)).Homotopic
          collapsedConnector.symm from
        ⟨Path.Homotopy.transRefl
          collapsedConnector.symm⟩).hcomp
      (.refl collapsedConnector)
  exact hremove.trans
    ⟨(Path.Homotopy.reflSymmTrans
      collapsedConnector).symm⟩

theorem retractionHom_false_factor_true
    (q : Q8) :
    retractionHom false (factorInclusion true q) = 1 := by
  rw [factorInclusion_apply, retractionHom,
    FundamentalGroup.mapOfEq_apply]
  have hpath :
      ((factorLoop true q⁻¹).map
          (retraction false).continuous).cast
        (retraction_basepoint_eq false).symm
        (retraction_basepoint_eq false).symm =
      collapsedSeamLoop q⁻¹ := by
    apply Path.ext
    funext t
    exact retraction_false_patch_true
      (seamLoop q⁻¹ t)
  rw [show
      FundamentalGroup.fromPath
          (.mk (((factorLoop true q⁻¹).map
            (retraction false).continuous).cast
              (retraction_basepoint_eq false).symm
              (retraction_basepoint_eq false).symm)) =
        FundamentalGroup.fromPath
          (.mk (collapsedSeamLoop q⁻¹)) by
      exact congr_arg FundamentalGroup.fromPath <|
        congr_arg Path.Homotopic.Quotient.mk hpath]
  exact Quotient.sound
    (collapsedSeamLoop_homotopic_refl q⁻¹)

theorem centralInvolutions_ne :
    factorInclusion false centralInvolution ≠
      factorInclusion true centralInvolution := by
  intro hcentral
  have hmapped :=
    congr_arg (retractionHom false) hcentral
  rw [retractionHom_factorInclusion,
    retractionHom_false_factor_true] at hmapped
  have hnontrivial :
      spaceSeamQ8Hom centralInvolution ≠ 1 := by
    intro h
    apply centralInvolution_ne_one
    apply spaceSeamQ8Hom_injective
    simpa using h
  exact hnontrivial hmapped

/-- The connected sum, bundled as a closed connected three-manifold. -/
noncomputable def closed3Manifold : Closed3Manifold where
  carrier := Carrier
  topology := inferInstance
  t2 := inferInstance
  secondCountable := inferInstance
  charted := inferInstance
  compact := inferInstance
  connected := inferInstance

/-- The completed double-quaternion certificate. -/
noncomputable def certificate :
    Submission.Helpers.DoubleQuaternionManifoldCertificate where
  manifold := closed3Manifold
  basepoint := carrierBasepoint
  inclusion := factorInclusion
  inclusion_injective := factorInclusion_injective
  centralInvolutions_ne := centralInvolutions_ne

end
end Submission.ConnectedSumCertificate
