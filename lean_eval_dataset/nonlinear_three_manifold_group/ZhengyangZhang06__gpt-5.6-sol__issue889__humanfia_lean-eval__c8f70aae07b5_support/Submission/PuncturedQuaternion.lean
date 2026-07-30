import Submission.ConnectedSum

/-!
# Quaternion loops in the punctured space form

Preferred coordinate paths lift to the complement of the puncture orbit.
Their coordinate-hyperplane multiplication homotopies lift as well, producing
an embedded quaternion subgroup in the punctured space form.
-/

namespace Submission.PuncturedQuaternion

open QuaternionObstruction
open QuaternionSpaceForm
open QuaternionPaths
open QuaternionHomotopy
open ConnectedSum

noncomputable section

abbrev UpstairsPunctured :=
  (genericOrbitᶜ : Set SphereThree)

private noncomputable def upstairsBasepoint : UpstairsPunctured :=
  ⟨1, by simpa using baseOrbit_not_mem_genericOrbit 1⟩

private noncomputable def upstairsTarget (q : Q8) : UpstairsPunctured :=
  ⟨q • 1, baseOrbit_not_mem_genericOrbit q⟩

private theorem quotient_ne_puncture (z : UpstairsPunctured) :
    (Quotient.mk'' z.1 : SpaceForm) ≠ puncture := by
  intro h
  have horbit :
      z.1 ∈ MulAction.orbit Q8
        QuaternionSpaceForm.genericPoint :=
    Quotient.exact h
  exact z.2 horbit

/-- The orbit projection, restricted over the punctured quotient. -/
noncomputable def puncturedQuotientMap :
    C(UpstairsPunctured, Punctured) where
  toFun z :=
    ⟨Quotient.mk'' z.1, by
      simpa [puncturedOpen] using quotient_ne_puncture z⟩
  continuous_toFun :=
    (quotientMap.continuous.comp continuous_subtype_val).subtype_mk
      fun z => by
        simpa [puncturedOpen, quotientMap] using
          quotient_ne_puncture z

private theorem puncturedQuotientMap_basepoint :
    puncturedQuotientMap upstairsBasepoint = puncturedBasepoint := by
  apply Subtype.ext
  simp [puncturedQuotientMap, upstairsBasepoint,
    puncturedBasepoint, basepoint]

private theorem puncturedQuotientMap_target (q : Q8) :
    puncturedQuotientMap (upstairsTarget q) = puncturedBasepoint := by
  apply Subtype.ext
  simpa [puncturedQuotientMap, upstairsTarget,
    puncturedBasepoint] using quotient_smul_one_eq q

/-- A preferred path lifted to the complement of the puncture orbit. -/
noncomputable def upstairsPath (q : Q8) :
    Path upstairsBasepoint (upstairsTarget q) where
  toFun t :=
    ⟨supportedPath q t, supportedPath_not_mem_genericOrbit q t⟩
  continuous_toFun :=
    (supportedPath q).continuous.subtype_mk _
  source' :=
    Subtype.ext (supportedPath q).source
  target' :=
    Subtype.ext (supportedPath q).target

/-- The preferred loop in the punctured quotient. -/
noncomputable def puncturedLoop (q : Q8) :
    Path puncturedBasepoint puncturedBasepoint :=
  ((upstairsPath q).map puncturedQuotientMap.continuous).cast
    puncturedQuotientMap_basepoint.symm
    (puncturedQuotientMap_target q).symm

/-- The fundamental-group element represented by a preferred punctured loop. -/
noncomputable def puncturedElement (q : Q8) :
    FundamentalGroup Punctured puncturedBasepoint :=
  FundamentalGroup.fromPath (.mk (puncturedLoop q))

private theorem supportedProductPath_not_mem_genericOrbit
    (q r : Q8) (t) :
    supportedProductPath q r t ∉ genericOrbit := by
  obtain ⟨H, hH⟩ :=
    supportedProductPath_homotopy_avoids_genericOrbit q r
  intro hmem
  apply hH (0, t)
  change H.toFun (0, t) ∈ genericOrbit
  rw [H.map_zero_left t]
  exact hmem

private noncomputable def upstairsProductPath (q r : Q8) :
    Path upstairsBasepoint (upstairsTarget (q * r)) where
  toFun t :=
    ⟨supportedProductPath q r t,
      supportedProductPath_not_mem_genericOrbit q r t⟩
  continuous_toFun :=
    (supportedProductPath q r).continuous.subtype_mk _
  source' :=
    Subtype.ext (supportedProductPath q r).source
  target' :=
    Subtype.ext (supportedProductPath q r).target

private theorem upstairsProductPath_homotopic
    (q r : Q8) :
    (upstairsProductPath q r).Homotopic
      (upstairsPath (q * r)) := by
  obtain ⟨H, hH⟩ :=
    supportedProductPath_homotopy_avoids_genericOrbit q r
  let H' :
      (upstairsProductPath q r).Homotopy
        (upstairsPath (q * r)) :=
    { toFun := fun z => ⟨H z, hH z⟩
      continuous_toFun := H.continuous.subtype_mk _
      map_zero_left := fun t =>
        Subtype.ext (H.map_zero_left t)
      map_one_left := fun t =>
        Subtype.ext (H.map_one_left t)
      prop' := fun t x hx =>
        Subtype.ext (H.prop' t x hx) }
  exact ⟨H'⟩

private theorem punctured_productPath_eq_loop_trans
    (q r : Q8) :
    ((upstairsProductPath q r).map
          puncturedQuotientMap.continuous).cast
        puncturedQuotientMap_basepoint.symm
        (puncturedQuotientMap_target (q * r)).symm =
      (puncturedLoop q).trans (puncturedLoop r) := by
  apply Path.ext
  funext t
  apply Subtype.ext
  set_option backward.isDefEq.respectTransparency false in
    change
      Quotient.mk'' (supportedProductPath q r t) =
        (((puncturedLoop q).trans (puncturedLoop r)) t).1
  rw [supportedProductPath, Path.trans_apply, Path.trans_apply]
  split_ifs
  · rfl
  · exact Quotient.sound ⟨q, rfl⟩

theorem puncturedLoop_mul_homotopic (q r : Q8) :
    ((puncturedLoop q).trans (puncturedLoop r)).Homotopic
      (puncturedLoop (q * r)) := by
  have h :=
    (upstairsProductPath_homotopic q r).map
      puncturedQuotientMap
  have h' :=
    h.pathCast puncturedQuotientMap_basepoint.symm
      (puncturedQuotientMap_target (q * r)).symm
  rw [punctured_productPath_eq_loop_trans q r] at h'
  exact h'

theorem puncturedElement_mul (q r : Q8) :
    puncturedElement q * puncturedElement r =
      puncturedElement (r * q) := by
  exact Quotient.sound (puncturedLoop_mul_homotopic r q)

theorem puncturedElement_one :
    puncturedElement 1 = 1 := by
  apply mul_left_cancel (a := puncturedElement 1)
  simpa using puncturedElement_mul 1 1

/-- The quaternion subgroup in the punctured space form. -/
noncomputable def puncturedQ8Hom :
    Q8 →* FundamentalGroup Punctured puncturedBasepoint where
  toFun q := puncturedElement q⁻¹
  map_one' := by simpa using puncturedElement_one
  map_mul' q r := by
    simpa only [mul_inv_rev] using
      (puncturedElement_mul q⁻¹ r⁻¹).symm

noncomputable def spaceSupportedLoop (q : Q8) :
    Path basepoint basepoint :=
  ((supportedPath q).map quotientMap.continuous).cast rfl
    (quotient_smul_one_eq q).symm

noncomputable def spaceSupportedElement (q : Q8) :
    FundamentalGroup SpaceForm basepoint :=
  FundamentalGroup.fromPath (.mk (spaceSupportedLoop q))

theorem spaceSupportedElement_monodromy (q : Q8) :
    quotient_isCoveringMap.monodromy
        (FundamentalGroup.toPath (spaceSupportedElement q))
        ⟨1, rfl⟩ =
      fiberPoint q := by
  apply Subtype.ext
  have h := congr_arg Subtype.val <|
    quotient_isCoveringMap.monodromy_map
      (Path.Homotopic.Quotient.mk (supportedPath q))
  exact h

/-- The inclusion of the punctured space form into the original one. -/
def puncturedInclusion : C(Punctured, SpaceForm) :=
  ⟨Subtype.val, continuous_subtype_val⟩

private theorem puncturedInclusion_basepoint :
    puncturedInclusion puncturedBasepoint = basepoint :=
  rfl

theorem puncturedLoop_map_inclusion (q : Q8) :
    (puncturedLoop q).map puncturedInclusion.continuous =
      spaceSupportedLoop q := by
  apply Path.ext
  funext t
  set_option backward.isDefEq.respectTransparency false in
    rfl

noncomputable def puncturedToSpaceHom :
    FundamentalGroup Punctured puncturedBasepoint →*
      FundamentalGroup SpaceForm basepoint :=
  FundamentalGroup.mapOfEq puncturedInclusion
    puncturedInclusion_basepoint

theorem puncturedToSpaceHom_element (q : Q8) :
    puncturedToSpaceHom (puncturedElement q) =
      spaceSupportedElement q := by
  rw [puncturedToSpaceHom, puncturedElement,
    FundamentalGroup.mapOfEq_apply, spaceSupportedElement]
  exact congr_arg FundamentalGroup.fromPath <|
    congr_arg Path.Homotopic.Quotient.mk <|
      puncturedLoop_map_inclusion q

theorem puncturedQ8Hom_injective :
    Function.Injective puncturedQ8Hom := by
  intro q r hqr
  change puncturedElement q⁻¹ = puncturedElement r⁻¹ at hqr
  have hmap :=
    congr_arg puncturedToSpaceHom hqr
  rw [puncturedToSpaceHom_element,
    puncturedToSpaceHom_element] at hmap
  have hinv : q⁻¹ = r⁻¹ := by
    apply fiberPoint_injective
    rw [← spaceSupportedElement_monodromy q⁻¹,
      ← spaceSupportedElement_monodromy r⁻¹, hmap]
  exact inv_injective hinv

end
end Submission.PuncturedQuaternion
