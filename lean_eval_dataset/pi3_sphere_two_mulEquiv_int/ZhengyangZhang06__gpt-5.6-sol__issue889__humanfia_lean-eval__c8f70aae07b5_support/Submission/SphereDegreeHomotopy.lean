import Submission.SphereDegreeInvariant
import Submission.SphereSmoothRepresentative

open scoped ContDiff

noncomputable section

namespace Submission.SphereDegreeHomotopy

open Set
open MeasureTheory
open Submission.SphereRegularApprox
open Submission.SphereSmoothRepresentative

variable {m : ℕ}

/-- The standard frame in the spatial dimension of an `m`-sphere map. -/
def spatialFrame (j : Fin (m + 1)) :
    Fin (m + 1) → ℝ :=
  Pi.single j 1

/-- The coefficient of the pulled-back sphere volume form in the standard
orientation. -/
def density
    (F : (Fin (m + 1) → ℝ) → Target m)
    (x : Fin (m + 1) → ℝ) : ℝ :=
  SphereDegreeInvariant.pulledVolumeForm F x
    (spatialFrame (m := m))

theorem differentiable_density
    {F : (Fin (m + 1) → ℝ) → Target m}
    (hF : ContDiff ℝ ∞ F) :
    Differentiable ℝ (density F) := by
  intro x
  change DifferentiableAt ℝ
    (fun y => SphereDegreeInvariant.pulledVolumeForm F y
      (spatialFrame (m := m))) x
  have hfd : ContDiff ℝ ∞ (fderiv ℝ F) :=
    (contDiff_infty_iff_fderiv.mp hF).2
  have hform : DifferentiableAt ℝ
      (fun y => SphereDegreeForm.volumeForm m (F y)) x :=
    (SphereDegreeForm.volumeForm m).differentiableAt.comp x
      (hF.differentiable (by simp) x)
  have hpulled : DifferentiableAt ℝ
      (SphereDegreeInvariant.pulledVolumeForm F) x :=
    hform.continuousAlternatingMapCompContinuousLinearMap
      (hfd.differentiable (by simp) x)
  let V : Fin (m + 1) →
      (Fin (m + 1) → ℝ) → (Fin (m + 1) → ℝ) :=
    fun j _ => spatialFrame j
  have hV : ∀ j, DifferentiableAt ℝ (V j) x := by
    intro j
    fun_prop
  simpa only [V] using
    hpulled.continuousAlternatingMap_apply hV

theorem continuous_density
    {F : (Fin (m + 1) → ℝ) → Target m}
    (hF : ContDiff ℝ ∞ F) :
    Continuous (density F) :=
  (differentiable_density hF).continuous

/-- Insert a zero in one coordinate, as a continuous linear map. -/
def insertZeroCLM (i : Fin (m + 2)) :
    (Fin (m + 1) → ℝ) →L[ℝ] (Fin (m + 2) → ℝ) :=
  ⟨{
    toFun := fun x => i.insertNth 0 x
    map_add' := fun x y => by
      ext j
      cases j using i.succAboveCases <;> simp
    map_smul' := fun c x => by
      ext j
      cases j using i.succAboveCases <;> simp
  }, LinearMap.continuous_of_finiteDimensional _⟩

@[simp]
theorem insertZeroCLM_apply
    (i : Fin (m + 2)) (x : Fin (m + 1) → ℝ) :
    insertZeroCLM i x = i.insertNth 0 x :=
  rfl

/-- The affine parametrization of a coordinate face. -/
def face (i : Fin (m + 2)) (c : ℝ)
    (x : Fin (m + 1) → ℝ) :
    Fin (m + 2) → ℝ :=
  i.insertNth c x

theorem hasFDerivAt_face
    (i : Fin (m + 2)) (c : ℝ)
    (x : Fin (m + 1) → ℝ) :
    HasFDerivAt (face i c) (insertZeroCLM i) x := by
  have hface :
      face i c = fun y =>
        i.insertNth c (0 : Fin (m + 1) → ℝ) +
          insertZeroCLM i y := by
    funext y
    ext j
    cases j using i.succAboveCases <;> simp [face]
  rw [hface]
  exact (insertZeroCLM i).hasFDerivAt.const_add
    (i.insertNth c (0 : Fin (m + 1) → ℝ))

@[fun_prop]
theorem contDiff_face
    (i : Fin (m + 2)) (c : ℝ) :
    ContDiff ℝ ∞ (face i c) := by
  have h :
      face i c =
        fun x =>
          i.insertNth c (0 : Fin (m + 1) → ℝ) +
            insertZeroCLM i x := by
    funext x
    ext j
    cases j using i.succAboveCases <;> simp [face]
  rw [h]
  fun_prop

theorem fderiv_face
    (i : Fin (m + 2)) (c : ℝ)
    (x : Fin (m + 1) → ℝ) :
    fderiv ℝ (face i c) x = insertZeroCLM i :=
  (hasFDerivAt_face i c x).fderiv

private theorem insertZeroCLM_spatialFrame
    (i : Fin (m + 2)) (j : Fin (m + 1)) :
    insertZeroCLM i (spatialFrame j) =
      i.removeNth
        (SphereDegreeInvariant.standardFrame (m := m)) j := by
  ext k
  cases k using i.succAboveCases
  · simp [insertZeroCLM, spatialFrame,
      SphereDegreeInvariant.standardFrame, Fin.removeNth]
  · simp [insertZeroCLM, spatialFrame,
      SphereDegreeInvariant.standardFrame, Fin.removeNth,
      Pi.single_apply]

/-- Flux through a face is the pulled-back volume density of its face
parametrization, with the cofactor sign. -/
theorem fluxComponent_face
    {F : (Fin (m + 2) → ℝ) → Target m}
    (hF : Differentiable ℝ F)
    (i : Fin (m + 2)) (c : ℝ)
    (x : Fin (m + 1) → ℝ) :
    SphereDegreeInvariant.fluxComponent F i (face i c x) =
      (-1 : ℝ) ^ i.val *
        density (F ∘ face i c) x := by
  rw [SphereDegreeInvariant.fluxComponent, density,
    SphereDegreeInvariant.pulledVolumeForm,
    SphereDegreeInvariant.pulledVolumeForm]
  congr 1
  apply congrArg
    (SphereDegreeForm.volumeForm m (F (face i c x)))
  funext j
  rw [fderiv_comp x (hF (face i c x))
    (hasFDerivAt_face i c x).differentiableAt,
    fderiv_face]
  exact congrArg (fderiv ℝ F (face i c x))
    (insertZeroCLM_spatialFrame i j).symm

private theorem density_congr
    {F G : (Fin (m + 1) → ℝ) → Target m}
    (_hF : ContDiff ℝ ∞ F) (_hG : ContDiff ℝ ∞ G)
    (h : F = G) :
    density F = density G := by
  subst G
  rfl

private theorem density_const :
    density
      (fun _ : Fin (m + 1) → ℝ =>
        (SphereGenerator.canonicalBasepoint m : Target m)) = 0 := by
  funext x
  simp [density, SphereDegreeInvariant.pulledVolumeForm,
    SphereDegreeForm.volumeForm_apply]
  apply (SphereDegreeForm.determinantForm m).map_coord_zero
    (1 : Fin (m + 2))
  simp

/-- The unnormalized real degree integral of a smooth compact sphere map. -/
def degree (F : Map m) : ℝ :=
  ∫ x in Set.Icc (0 : Fin (m + 1) → ℝ) 1,
    density F x

theorem integrableOn_density (F : Map m) :
    IntegrableOn (density F)
      (Set.Icc (0 : Fin (m + 1) → ℝ) 1) :=
  (continuous_density F.contDiff_toFun).continuousOn.integrableOn_compact
    isCompact_Icc

/-- Smooth relative homotopies preserve the volume integral. -/
theorem degree_eq_of_smoothHomotopy
    {F G : Map 2}
    (K : SmoothHomotopy F G) :
    degree F = degree G := by
  have hstokes :=
    SphereDegreeInvariant.integral_flux_faces_eq_zero
      K.contDiff_toFun K.norm_toFun
  have hface0 :
      (fun x : Fin 3 → ℝ => K.toFun (face 0 0 x)) = F := by
    funext x
    simpa [face, prepend, Fin.insertNth_zero'] using K.map_zero x
  have hface1 :
      (fun x : Fin 3 → ℝ => K.toFun (face 0 1 x)) = G := by
    funext x
    simpa [face, prepend, Fin.insertNth_zero'] using K.map_one x
  have hside :
      ∀ (i : Fin 3) (c : ℝ), c = 0 ∨ c = 1 →
        (fun x : Fin 3 → ℝ =>
          K.toFun (face i.succ c x)) =
        (fun _ =>
          (SphereGenerator.canonicalBasepoint 2 : Target 2)) := by
    intro i c hc
    funext x
    apply K.map_spatialBoundary _ i
    rcases hc with rfl | rfl
    · left
      simp [face]
    · right
      simp [face]
  have hflux0 :
      ∀ c : ℝ,
        (fun x : Fin 3 → ℝ =>
          SphereDegreeInvariant.fluxField K.toFun
            ((0 : Fin 4).insertNth c x) 0) =
        density (K.toFun ∘ face 0 c) := by
    intro c
    funext x
    simpa [SphereDegreeInvariant.fluxField, face] using
      fluxComponent_face
        (K.contDiff_toFun.differentiable (by norm_num)) 0 c x
  have hfluxSide :
      ∀ (i : Fin 3) (c : ℝ), c = 0 ∨ c = 1 →
        (fun x : Fin 3 → ℝ =>
          SphereDegreeInvariant.fluxField K.toFun
            (i.succ.insertNth c x) i.succ) = 0 := by
    intro i c hc
    funext x
    change
      SphereDegreeInvariant.fluxComponent K.toFun i.succ
        (face i.succ c x) = 0
    rw [fluxComponent_face
        (K.contDiff_toFun.differentiable (by norm_num))]
    rw [show K.toFun ∘ face i.succ c =
        (fun _ =>
          (SphereGenerator.canonicalBasepoint 2 : Target 2)) by
      funext y
      exact congrFun (hside i c hc) y]
    rw [congrFun density_const x]
    simp
  have hflux11 :
      (fun x : Fin 3 → ℝ =>
        SphereDegreeInvariant.fluxField K.toFun
          ((1 : Fin 4).insertNth 1 x) 1) = 0 := by
    simpa using hfluxSide 0 1 (Or.inr rfl)
  have hflux10 :
      (fun x : Fin 3 → ℝ =>
        SphereDegreeInvariant.fluxField K.toFun
          ((1 : Fin 4).insertNth 0 x) 1) = 0 := by
    simpa using hfluxSide 0 0 (Or.inl rfl)
  have hflux21 :
      (fun x : Fin 3 → ℝ =>
        SphereDegreeInvariant.fluxField K.toFun
          ((2 : Fin 4).insertNth 1 x) 2) = 0 := by
    simpa using hfluxSide 1 1 (Or.inr rfl)
  have hflux20 :
      (fun x : Fin 3 → ℝ =>
        SphereDegreeInvariant.fluxField K.toFun
          ((2 : Fin 4).insertNth 0 x) 2) = 0 := by
    simpa using hfluxSide 1 0 (Or.inl rfl)
  have hflux31 :
      (fun x : Fin 3 → ℝ =>
        SphereDegreeInvariant.fluxField K.toFun
          ((3 : Fin 4).insertNth 1 x) 3) = 0 := by
    simpa using hfluxSide 2 1 (Or.inr rfl)
  have hflux30 :
      (fun x : Fin 3 → ℝ =>
        SphereDegreeInvariant.fluxField K.toFun
          ((3 : Fin 4).insertNth 0 x) 3) = 0 := by
    simpa using hfluxSide 2 0 (Or.inl rfl)
  rw [Fin.sum_univ_four] at hstokes
  rw [hflux0 1, hflux0 0, hflux11, hflux10,
    hflux21, hflux20, hflux31, hflux30] at hstokes
  have h0 :
      density (K.toFun ∘ face 0 0) = density F :=
    density_congr
      (K.contDiff_toFun.comp <| by
        exact contDiff_face 0 0)
      F.contDiff_toFun hface0
  have h1 :
      density (K.toFun ∘ face 0 1) = density G :=
    density_congr
      (K.contDiff_toFun.comp <| by
        exact contDiff_face 0 1)
      G.contDiff_toFun hface1
  rw [h0, h1] at hstokes
  have hdegree : degree G - degree F = 0 := by
    simpa only [degree, integral_zero', sub_zero, zero_sub, add_zero]
      using hstokes
  exact sub_eq_zero.mp hdegree |>.symm

/-- A cubical relative homotopy between smooth representatives preserves
their degree integral. -/
theorem degree_eq_of_homotopic
    {F G : Map 2}
    (h : GenLoop.Homotopic F.genLoop G.genLoop) :
    degree F = degree G := by
  obtain ⟨H⟩ := h
  obtain ⟨K⟩ := exists_smoothHomotopy H
  exact degree_eq_of_smoothHomotopy K

end Submission.SphereDegreeHomotopy
