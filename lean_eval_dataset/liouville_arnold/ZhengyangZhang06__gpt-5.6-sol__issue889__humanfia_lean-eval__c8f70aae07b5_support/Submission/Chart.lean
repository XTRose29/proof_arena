import Submission.Orbit

namespace Submission.Helpers

open Function Module Set Topology
open scoped ContDiff NNReal Topology BigOperators

open LeanEval.Geometry.LiouvilleArnold

section RegularLevelChart

/-- The derivative of the joint integral map. -/
noncomputable def jointDifferential {n : ℕ} (F : Fin n → E n → ℝ) (x : E n) :
    E n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ fderiv ℝ (F i) x

@[simp]
theorem jointDifferential_apply {n : ℕ} (F : Fin n → E n → ℝ)
    (x v : E n) (i : Fin n) :
    jointDifferential F x v i = fderiv ℝ (F i) x v := rfl

/-- Linear independence of the component differentials makes the joint differential
surjective. -/
theorem jointDifferential_surjective {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    Function.Surjective (jointDifferential F x) := by
  let D := jointDifferential F x
  have hFL : LinearIndependent ℝ
      (fun i ↦ (fderiv ℝ (F i) x : E n →ₗ[ℝ] ℝ)) := by
    have hmap := hF.map' (ContinuousLinearMap.coeLM ℝ)
      (LinearMap.ker_eq_bot.mpr ContinuousLinearMap.coe_injective)
    simpa [Function.comp_def] using hmap
  have hmem (i : Fin n) :
      (fderiv ℝ (F i) x : E n →ₗ[ℝ] ℝ) ∈ LinearMap.range D.toLinearMap.dualMap := by
    refine ⟨(ContinuousLinearMap.proj i : (Fin n → ℝ) →L[ℝ] ℝ).toLinearMap, ?_⟩
    ext v
    rfl
  have hspan :
      Submodule.span ℝ (Set.range fun i ↦ (fderiv ℝ (F i) x : E n →ₗ[ℝ] ℝ)) ≤
        LinearMap.range D.toLinearMap.dualMap := by
    apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact hmem i
  have hlow : n ≤ finrank ℝ (LinearMap.range D.toLinearMap.dualMap) := by
    calc
      n = finrank ℝ
          (Submodule.span ℝ
            (Set.range fun i ↦ (fderiv ℝ (F i) x : E n →ₗ[ℝ] ℝ))) := by
        simpa using (finrank_span_eq_card hFL).symm
      _ ≤ finrank ℝ (LinearMap.range D.toLinearMap.dualMap) :=
        Submodule.finrank_mono hspan
  have hlow' : n ≤ finrank ℝ (LinearMap.range D.toLinearMap) := by
    rw [LinearMap.finrank_range_dualMap_eq_finrank_range] at hlow
    exact hlow
  change Function.Surjective D.toLinearMap
  rw [← LinearMap.range_eq_top]
  apply Submodule.eq_of_le_of_finrank_le le_top
  simpa using hlow'

theorem finrank_jointDifferential_ker {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    finrank ℝ (jointDifferential F x).ker = n := by
  have h := (jointDifferential F x).toLinearMap.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr (jointDifferential_surjective F x hF)] at h
  have h' : n + finrank ℝ (jointDifferential F x).ker = 2 * n := by
    simpa using h
  omega

/-- Arbitrary continuous coordinates on the tangent kernel of the joint level map. -/
noncomputable def jointKernelEquiv {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    (jointDifferential F x).ker ≃L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearEquiv.ofFinrankEq (by
    simpa using finrank_jointDifferential_ker F x hF)

/-- Extend kernel coordinates to the ambient space by orthogonal projection. -/
noncomputable def transverseCoordinates {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    E n →L[ℝ] (Fin n → ℝ) :=
  (jointKernelEquiv F x hF).toContinuousLinearMap.comp
    (jointDifferential F x).ker.orthogonalProjectionOnto

theorem transverseCoordinates_surjective {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    Function.Surjective (transverseCoordinates F x hF) := by
  intro y
  let z : (jointDifferential F x).ker := (jointKernelEquiv F x hF).symm y
  refine ⟨(z : E n), ?_⟩
  simp [transverseCoordinates, z]

theorem transverseCoordinates_ker {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    (transverseCoordinates F x hF).ker = (jointDifferential F x).kerᗮ := by
  ext v
  simp [transverseCoordinates]

/-- The derivative used for the ambient inverse-function chart. -/
noncomputable def regularLevelDerivative {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    E n ≃L[ℝ] ((Fin n → ℝ) × (Fin n → ℝ)) := by
  let D := jointDifferential F x
  let G := transverseCoordinates F x hF
  have hD : D.range = ⊤ :=
    LinearMap.range_eq_top.mpr (jointDifferential_surjective F x hF)
  have hG : G.range = ⊤ :=
    LinearMap.range_eq_top.mpr (transverseCoordinates_surjective F x hF)
  have hcompl : IsCompl D.ker G.ker := by
    rw [transverseCoordinates_ker F x hF]
    exact D.ker.isCompl_orthogonal
  exact ContinuousLinearMap.equivProdOfSurjectiveOfIsCompl D G hD hG hcompl

/-- The ambient nonlinear map whose first coordinates are the integrals and whose second
coordinates parametrize the level set. -/
noncomputable def regularLevelMap {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x) :
    E n → ((Fin n → ℝ) × (Fin n → ℝ)) :=
  fun y ↦ (fun i ↦ F i y, transverseCoordinates F x hF y)

theorem regularLevelMap_hasFDerivAt {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hdiff : ∀ i, DifferentiableAt ℝ (F i) x) :
    HasFDerivAt (regularLevelMap F x hF)
      (regularLevelDerivative F x hF).toContinuousLinearMap x := by
  have hfirst : HasFDerivAt (fun y : E n ↦ fun i ↦ F i y)
      (jointDifferential F x) x := by
    apply hasFDerivAt_pi.mpr
    intro i
    exact (hdiff i).hasFDerivAt
  have hprod := hfirst.prodMk (transverseCoordinates F x hF).hasFDerivAt
  have heq : (regularLevelDerivative F x hF).toContinuousLinearMap =
      (jointDifferential F x).prod (transverseCoordinates F x hF) := by
    ext v <;> rfl
  rw [heq]
  change HasFDerivAt
    (fun y : E n ↦ (fun i ↦ F i y, transverseCoordinates F x hF y)) _ x
  exact hprod

theorem regularLevelMap_contDiffAt {n : ℕ} (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hsmooth : ∀ i, ContDiffAt ℝ 1 (F i) x) :
    ContDiffAt ℝ 1 (regularLevelMap F x hF) x := by
  exact (contDiffAt_pi.mpr hsmooth).prodMk
    (transverseCoordinates F x hF).contDiff.contDiffAt

/-- The ambient inverse-function chart for the joint integral map and transverse
coordinates. -/
noncomputable def regularLevelOpenPartialHomeomorph {n : ℕ}
    (F : Fin n → E n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hsmooth : ∀ i, ContDiffAt ℝ 1 (F i) x) :
    OpenPartialHomeomorph (E n) ((Fin n → ℝ) × (Fin n → ℝ)) :=
  (regularLevelMap_contDiffAt F x hF hsmooth).toOpenPartialHomeomorph
    (regularLevelMap F x hF)
    (regularLevelMap_hasFDerivAt F x hF fun i ↦
      (hsmooth i).differentiableAt one_ne_zero)
    one_ne_zero

@[simp]
theorem regularLevelOpenPartialHomeomorph_apply {n : ℕ}
    (F : Fin n → E n → ℝ) (x y : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hsmooth : ∀ i, ContDiffAt ℝ 1 (F i) x) :
    regularLevelOpenPartialHomeomorph F x hF hsmooth y =
      regularLevelMap F x hF y := rfl

theorem regularLevelOpenPartialHomeomorph_symm_mem_levelSet {n : ℕ}
    (F : Fin n → E n → ℝ) (c : Fin n → ℝ) (x : E n)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hsmooth : ∀ i, ContDiffAt ℝ 1 (F i) x) {q : Fin n → ℝ}
    (hq : (c, q) ∈ (regularLevelOpenPartialHomeomorph F x hF hsmooth).target) :
    (regularLevelOpenPartialHomeomorph F x hF hsmooth).symm (c, q) ∈
      levelSet F c := by
  let e := regularLevelOpenPartialHomeomorph F x hF hsmooth
  have hr := e.right_inv hq
  change regularLevelMap F x hF (e.symm (c, q)) = (c, q) at hr
  change ∀ i, F i (e.symm (c, q)) = c i
  intro i
  exact congrFun (congrArg Prod.fst hr) i

/-- Restrict the ambient regular-level chart to the fixed level set. -/
noncomputable def levelSetOpenPartialHomeomorph {n : ℕ}
    (F : Fin n → E n → ℝ) (c : Fin n → ℝ) (x : E n)
    (hx : x ∈ levelSet F c)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hsmooth : ∀ i, ContDiffAt ℝ 1 (F i) x) :
    OpenPartialHomeomorph (levelSet F c) (Fin n → ℝ) := by
  classical
  let e := regularLevelOpenPartialHomeomorph F x hF hsmooth
  let source : Set (levelSet F c) := {z | (z : E n) ∈ e.source}
  let target : Set (Fin n → ℝ) := {q | (c, q) ∈ e.target}
  let inv : (Fin n → ℝ) → levelSet F c := fun q ↦
    if hq : q ∈ target then
      ⟨e.symm (c, q), regularLevelOpenPartialHomeomorph_symm_mem_levelSet
        F c x hF hsmooth hq⟩
    else ⟨x, hx⟩
  have hmap (z : levelSet F c) (hz : z ∈ source) :
      transverseCoordinates F x hF z ∈ target := by
    have hm := e.map_source hz
    change (c, transverseCoordinates F x hF z) ∈ e.target
    convert hm using 1
    ext i
    · exact (z.property i).symm
    · simp [e, regularLevelMap]
  have hraw : ContinuousOn (fun q : Fin n → ℝ ↦ e.symm (c, q)) target :=
    e.continuousOn_symm.comp
      (continuous_const.prodMk continuous_id).continuousOn fun _ hq ↦ hq
  exact
    { toPartialEquiv :=
        { toFun := fun z ↦ transverseCoordinates F x hF z
          invFun := inv
          source := source
          target := target
          map_source' := hmap
          map_target' := by
            intro q hq
            simp only [inv, dif_pos hq]
            exact e.map_target hq
          left_inv' := by
            intro z hz
            have htarget := hmap z hz
            apply Subtype.ext
            simp only [inv, dif_pos htarget]
            have hl := e.left_inv hz
            rw [show (c, transverseCoordinates F x hF z) = e z by
              congr 1
              ext i
              exact (z.property i).symm]
            exact hl
          right_inv' := by
            intro q hq
            simp only [inv, dif_pos hq]
            have hr := e.right_inv hq
            exact congrArg Prod.snd hr }
      continuousOn_toFun :=
        (transverseCoordinates F x hF).continuous.comp
          continuous_subtype_val |>.continuousOn
      continuousOn_invFun := by
        rw [continuousOn_iff_continuous_restrict]
        let j : target → levelSet F c := fun q ↦
          ⟨e.symm (c, q), regularLevelOpenPartialHomeomorph_symm_mem_levelSet
            F c x hF hsmooth q.property⟩
        have hjval : Continuous (fun q : target ↦ e.symm (c, (q : Fin n → ℝ))) :=
          hraw.restrict
        have hj : Continuous j := hjval.subtype_mk _
        apply hj.congr
        intro q
        apply Subtype.ext
        simp [j, inv, q.property]
      open_source := e.open_source.preimage continuous_subtype_val
      open_target := e.open_target.preimage
        (continuous_const.prodMk continuous_id) }

@[simp]
theorem levelSetOpenPartialHomeomorph_apply {n : ℕ}
    (F : Fin n → E n → ℝ) (c : Fin n → ℝ) (x : E n)
    (hx : x ∈ levelSet F c)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hsmooth : ∀ i, ContDiffAt ℝ 1 (F i) x) (z : levelSet F c) :
    levelSetOpenPartialHomeomorph F c x hx hF hsmooth z =
      transverseCoordinates F x hF z := rfl

theorem self_mem_levelSetOpenPartialHomeomorph_source {n : ℕ}
    (F : Fin n → E n → ℝ) (c : Fin n → ℝ) (x : E n)
    (hx : x ∈ levelSet F c)
    (hF : LinearIndependent ℝ fun i ↦ fderiv ℝ (F i) x)
    (hsmooth : ∀ i, ContDiffAt ℝ 1 (F i) x) :
    (⟨x, hx⟩ : levelSet F c) ∈
      (levelSetOpenPartialHomeomorph F c x hx hF hsmooth).source := by
  exact (regularLevelMap_contDiffAt F x hF hsmooth).mem_toOpenPartialHomeomorph_source
    (regularLevelMap_hasFDerivAt F x hF fun i ↦
      (hsmooth i).differentiableAt one_ne_zero)
    one_ne_zero

end RegularLevelChart

end Submission.Helpers
