import ChallengeDeps
import Mathlib.AlgebraicTopology.FundamentalGroupoid.SimplyConnected
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Analysis.Quaternion
import Mathlib.Geometry.Manifold.Instances.Sphere

/-!
# Paths in punctured quaternion spheres

Stereographic projection identifies the complement of one point in the unit
quaternion sphere with a real three-dimensional vector space.  This file
packages the two consequences needed by the spherical-space-form
construction: paths avoiding one point are homotopic, and the complement of a
finite nonempty set is path connected.
-/

open Metric
open scoped Quaternion

namespace Submission.SphereComplement

abbrev QuaternionSphere := sphere (0 : ℍ) 1

noncomputable def complementHomeomorph
    (v : QuaternionSphere) :
    ({v}ᶜ : Set QuaternionSphere) ≃ₜ (ℝ ∙ v.1)ᗮ := by
  let e := stereographic (norm_eq_of_mem_sphere v)
  have hs : e.source = ({v}ᶜ : Set QuaternionSphere) := by
    simp [e, stereographic_source]
  have ht : e.target = (Set.univ : Set ((ℝ ∙ v.1)ᗮ)) := by
    simp [e, stereographic_target]
  exact
    (Homeomorph.setCongr hs.symm).trans <|
      e.toHomeomorphSourceTarget.trans <|
        (Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)

/-- Any two paths with common endpoints that avoid the same sphere point are homotopic. -/
theorem paths_homotopic_of_avoid
    {x y : QuaternionSphere} (v : QuaternionSphere)
    (p q : Path x y)
    (hp : ∀ t, p t ≠ v) (hq : ∀ t, q t ≠ v) :
    p.Homotopic q := by
  let U : Set QuaternionSphere := {v}ᶜ
  let e : U ≃ₜ (ℝ ∙ v.1)ᗮ := complementHomeomorph v
  letI : ContractibleSpace U := e.contractibleSpace
  letI : SimplyConnectedSpace U := SimplyConnectedSpace.ofContractible U
  let x' : U := ⟨x, by simpa [U] using hp 0⟩
  let y' : U := ⟨y, by simpa [U] using hp 1⟩
  let p' : Path x' y' :=
    { toFun := fun t => ⟨p t, by simpa [U] using hp t⟩
      continuous_toFun := p.continuous.subtype_mk
        (fun t => by simpa [U] using hp t)
      source' := Subtype.ext p.source
      target' := Subtype.ext p.target }
  let q' : Path x' y' :=
    { toFun := fun t => ⟨q t, by simpa [U] using hq t⟩
      continuous_toFun := q.continuous.subtype_mk
        (fun t => by simpa [U] using hq t)
      source' := Subtype.ext q.source
      target' := Subtype.ext q.target }
  have h := (SimplyConnectedSpace.paths_homotopic p' q').map
    ⟨Subtype.val, continuous_subtype_val⟩
  dsimp [x', y'] at h
  have hp' : p'.map continuous_subtype_val = p := by
    apply Path.ext
    funext t
    exact Subtype.ext rfl
  have hq' : q'.map continuous_subtype_val = q := by
    apply Path.ext
    funext t
    exact Subtype.ext rfl
  rwa [hp', hq'] at h

local instance : Fact (Module.finrank ℝ ℍ = 3 + 1) :=
  ⟨by simpa using (Quaternion.finrank_eq_four (R := ℝ))⟩

/-- The unit quaternion sphere remains path connected after deleting a finite nonempty set. -/
theorem compl_finite_isPathConnected
    (v : QuaternionSphere) (F : Set QuaternionSphere)
    (hF : F.Finite) (hv : v ∈ F) :
    IsPathConnected Fᶜ := by
  let e := stereographic' 3 v
  let A : Set (EuclideanSpace ℝ (Fin 3)) := e '' (F \ {v})
  have hA : A.Finite := (hF.subset Set.sdiff_subset).image e
  have hApc : IsPathConnected Aᶜ :=
    hA.countable.isPathConnected_compl_of_one_lt_rank <|
      Module.one_lt_rank_of_one_lt_finrank (by simp)
  let g : {x // x ∉ A} → {x // x ∉ F} := fun y =>
    ⟨e.symm y, by
      intro hey
      have hesource : e.symm y ∈ e.source := by
        apply e.map_target
        simp [e, stereographic'_target]
      have hene : e.symm y ≠ v := by
        intro hev
        rw [hev] at hesource
        simp [e, stereographic'_source] at hesource
      have hmemA : e (e.symm y) ∈ A :=
        ⟨e.symm y, ⟨hey, by simpa using hene⟩, rfl⟩
      have hright : e (e.symm y) = y := by
        apply e.rightInvOn
        simp [e, stereographic'_target]
      exact y.2 (hright ▸ hmemA)⟩
  have hecont : Continuous e.symm := by
    rw [← continuousOn_univ]
    simpa [e, stereographic'_target] using e.continuousOn_invFun
  have hgcont : Continuous g :=
    (hecont.comp continuous_subtype_val).subtype_mk _
  have hgsurj : Function.Surjective g := by
    intro x
    have hxv : x.1 ≠ v := fun hx => x.2 (hx ▸ hv)
    have hxsource : x.1 ∈ e.source := by
      simpa [e, stereographic'_source] using hxv
    have heA : e x.1 ∉ A := by
      rintro ⟨z, ⟨hzF, hzv⟩, hez⟩
      have hxz := e.injOn hxsource
        (by simpa [e, stereographic'_source] using hzv) hez.symm
      exact x.2 (hxz ▸ hzF)
    let y : {x // x ∉ A} := ⟨e x.1, heA⟩
    refine ⟨y, Subtype.ext ?_⟩
    exact e.leftInvOn hxsource
  letI : PathConnectedSpace {x // x ∉ A} :=
    isPathConnected_iff_pathConnectedSpace.mp hApc
  rw [isPathConnected_iff_pathConnectedSpace]
  exact hgsurj.pathConnectedSpace hgcont

end Submission.SphereComplement
