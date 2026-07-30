import Submission.QuaternionPaths

/-!
# Homotopies of coordinate paths away from the puncture orbit

The preferred quaternion paths and their product paths share a vanishing
coordinate.  They can therefore be homotoped inside the corresponding
two-sphere.  Every point of the chosen puncture orbit has all four coordinates
nonzero, so this homotopy stays in the punctured covering space.
-/

open Metric
open scoped Quaternion

namespace Submission.QuaternionHomotopy

open QuaternionObstruction
open QuaternionSpaceForm
open QuaternionPaths

noncomputable section

private noncomputable def sphereComplementHomeomorph
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : sphere (0 : E) 1) :
    ({v}ᶜ : Set (sphere (0 : E) 1)) ≃ₜ (ℝ ∙ v.1)ᗮ := by
  let e := stereographic (norm_eq_of_mem_sphere v)
  have hs : e.source = ({v}ᶜ : Set (sphere (0 : E) 1)) := by
    simp [e, stereographic_source]
  have ht : e.target = (Set.univ : Set ((ℝ ∙ v.1)ᗮ)) := by
    simp [e, stereographic_target]
  exact
    (Homeomorph.setCongr hs.symm).trans <|
      e.toHomeomorphSourceTarget.trans <|
        (Homeomorph.setCongr ht).trans (Homeomorph.Set.univ _)

private theorem spherePaths_homotopic_of_avoid
    {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    {x y : sphere (0 : E) 1} (v : sphere (0 : E) 1)
    (p q : Path x y)
    (hp : ∀ t, p t ≠ v) (hq : ∀ t, q t ≠ v) :
    p.Homotopic q := by
  let U : Set (sphere (0 : E) 1) := {v}ᶜ
  let e : U ≃ₜ (ℝ ∙ v.1)ᗮ := sphereComplementHomeomorph v
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

/-- A quaternion coordinate as a real linear map. -/
noncomputable def coordinateLinear (k : Fin 4) : ℍ →ₗ[ℝ] ℝ :=
  ![(QuaternionAlgebra.reₗ _ _ _ : ℍ →ₗ[ℝ] ℝ),
    (QuaternionAlgebra.imIₗ _ _ _ : ℍ →ₗ[ℝ] ℝ),
    (QuaternionAlgebra.imJₗ _ _ _ : ℍ →ₗ[ℝ] ℝ),
    (QuaternionAlgebra.imKₗ _ _ _ : ℍ →ₗ[ℝ] ℝ)] k

@[simp]
theorem coordinateLinear_apply (k : Fin 4) (x : ℍ) :
    coordinateLinear k x = coordinate k x := by
  fin_cases k <;> rfl

/-- The coordinate hyperplane used by a product homotopy. -/
def zeroHyperplane (k : Fin 4) : Submodule ℝ ℍ :=
  LinearMap.ker (coordinateLinear k)

abbrev HyperplaneSphere (k : Fin 4) :=
  sphere (0 : zeroHyperplane k) 1

private noncomputable def liftPoint
    (k : Fin 4) (x : SphereThree)
    (hx : coordinate k x.1 = 0) :
    HyperplaneSphere k :=
  ⟨⟨x.1, by
      change coordinateLinear k x.1 = 0
      simpa using hx⟩, by
    rw [mem_sphere_zero_iff_norm]
    exact norm_eq_of_mem_sphere x⟩

private noncomputable def hyperplaneInclusion
    (k : Fin 4) : C(HyperplaneSphere k, SphereThree) where
  toFun z :=
    ⟨z.1.1, by
      rw [mem_sphere_zero_iff_norm]
      exact norm_eq_of_mem_sphere z⟩
  continuous_toFun :=
    (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

private noncomputable def liftPath
    {x y : SphereThree} (k : Fin 4)
    (hx : coordinate k x.1 = 0)
    (hy : coordinate k y.1 = 0)
    (p : Path x y)
    (hp : ∀ t, coordinate k (p t).1 = 0) :
    Path (liftPoint k x hx) (liftPoint k y hy) where
  toFun t := liftPoint k (p t) (hp t)
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact continuous_subtype_val.comp p.continuous
  source' := by
    apply Subtype.ext
    change
      (⟨(p 0).1, _⟩ : zeroHyperplane k) =
        (⟨x.1, _⟩ : zeroHyperplane k)
    have hval : (p 0).1 = x.1 :=
      congr_arg (fun z : SphereThree => z.1) p.source
    exact Subtype.ext hval
  target' := by
    apply Subtype.ext
    change
      (⟨(p 1).1, _⟩ : zeroHyperplane k) =
        (⟨y.1, _⟩ : zeroHyperplane k)
    have hval : (p 1).1 = y.1 :=
      congr_arg (fun z : SphereThree => z.1) p.target
    exact Subtype.ext hval

private theorem paths_homotopic_in_coordinate
    {x y : SphereThree} (k : Fin 4)
    (p q : Path x y)
    (hp : ∀ t, coordinate k (p t).1 = 0)
    (hq : ∀ t, coordinate k (q t).1 = 0)
    (v : SphereThree) (hv : coordinate k v.1 = 0)
    (hpv : ∀ t, p t ≠ v) (hqv : ∀ t, q t ≠ v) :
    ∃ H : p.Homotopy q,
      ∀ z, coordinate k (H z).1 = 0 := by
  have hx : coordinate k x.1 = 0 := by
    rw [← p.source]
    exact hp 0
  have hy : coordinate k y.1 = 0 := by
    rw [← p.target]
    exact hp 1
  let p' := liftPath k hx hy p hp
  let q' := liftPath k hx hy q hq
  have hp' : ∀ t, p' t ≠ liftPoint k v hv := by
    intro t h
    apply hpv t
    apply Subtype.ext
    exact congr_arg (fun z : HyperplaneSphere k => z.1.1) h
  have hq' : ∀ t, q' t ≠ liftPoint k v hv := by
    intro t h
    apply hqv t
    apply Subtype.ext
    exact congr_arg (fun z : HyperplaneSphere k => z.1.1) h
  obtain ⟨H⟩ :=
    spherePaths_homotopic_of_avoid
      (liftPoint k v hv) p' q' hp' hq'
  let H' : p.Homotopy q :=
    { toFun := fun z => hyperplaneInclusion k (H z)
      continuous_toFun :=
        (hyperplaneInclusion k).continuous.comp H.continuous
      map_zero_left := fun t => by
        change hyperplaneInclusion k (H (0, t)) = p t
        exact Subtype.ext <|
          congr_arg (fun z : HyperplaneSphere k => z.1.1)
            (H.map_zero_left t)
      map_one_left := fun t => by
        change hyperplaneInclusion k (H (1, t)) = q t
        exact Subtype.ext <|
          congr_arg (fun z : HyperplaneSphere k => z.1.1)
            (H.map_one_left t)
      prop' := fun t u hu => by
        change hyperplaneInclusion k (H (t, u)) = p u
        exact Subtype.ext <|
          congr_arg (fun z : HyperplaneSphere k => z.1.1)
            (H.prop' t u hu) }
  refine ⟨H', ?_⟩
  intro z
  change coordinate k (H z).1.1 = 0
  have hz := (H z).1.2
  change coordinateLinear k (H z).1.1 = 0 at hz
  simpa only [coordinateLinear_apply] using hz

/-- Every point in the puncture orbit has all four coordinates nonzero. -/
theorem genericOrbit_coordinate_ne_zero
    {x : SphereThree} (hx : x ∈ genericOrbit) (k : Fin 4) :
    coordinate k x.1 ≠ 0 := by
  rcases hx with ⟨q, rfl⟩
  rcases q with q | q <;> fin_cases q <;> fin_cases k
  all_goals
    simp only [MulAction.compHom_smul_def]
    change coordinate _
      ((q8ToSphere _).1 * QuaternionSpaceForm.genericPoint.1) ≠ 0
    rw [q8ToSphere_coe]
    simp +decide [coordinate, q8RealValue, q8IntValue,
      intQuaternionCast, QuaternionSpaceForm.genericPoint,
      Quaternion.re_mul,
      Quaternion.imI_mul, Quaternion.imJ_mul, Quaternion.imK_mul]

private theorem exists_omitted_coordinate (q : Q8) :
    ∃ k : Fin 4, k ≠ 0 ∧ k ≠ pathAxis q := by
  rcases q with q | q <;> fin_cases q <;> decide

/-- Every preferred coordinate path avoids the full puncture orbit. -/
theorem supportedPath_not_mem_genericOrbit (q : Q8) (t) :
    supportedPath q t ∉ genericOrbit := by
  obtain ⟨k, hk0, hka⟩ := exists_omitted_coordinate q
  intro hmem
  exact genericOrbit_coordinate_ne_zero hmem k <|
    supportedPath_supported q t k hk0 hka

/--
The multiplication homotopy between preferred paths stays in the complement
of the full puncture orbit.
-/
theorem supportedProductPath_homotopy_avoids_genericOrbit
    (q r : Q8) :
    ∃ H :
        (supportedProductPath q r).Homotopy
          (supportedPath (q * r)),
      ∀ z, H z ∉ genericOrbit := by
  let k := commonZeroCoordinate q r
  obtain ⟨H, hH⟩ :=
    paths_homotopic_in_coordinate k
      (supportedProductPath q r) (supportedPath (q * r))
      (supportedProductPath_commonZero q r)
      (supportedPath_product_commonZero q r)
      (hyperplanePoint k) (coordinate_hyperplanePoint_self k)
      (supportedProductPath_ne_hyperplanePoint q r)
      (supportedPath_product_ne_hyperplanePoint q r)
  refine ⟨H, ?_⟩
  intro z hmem
  exact genericOrbit_coordinate_ne_zero hmem k (hH z)

end
end Submission.QuaternionHomotopy
