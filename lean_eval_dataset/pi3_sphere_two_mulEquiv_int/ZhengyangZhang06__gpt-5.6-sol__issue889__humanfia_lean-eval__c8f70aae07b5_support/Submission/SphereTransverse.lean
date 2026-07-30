import Submission.SphereFiniteCut
import Submission.SphereRegularLocal

open scoped ContDiff unitInterval Topology

noncomputable section

namespace Submission.SphereTransverse

open Set
open Matrix
open Submission.SphereRegularApprox

variable {m : ℕ}

/-- A cubical sphere map is regular at an antipode preimage when, near that
point, it is represented by a smooth ambient sphere map whose horizontal
derivative is invertible. -/
structure RegularAt
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (t : Fin (m + 1) → I) where
  map : Domain m → Target m
  contDiff_map : ContDiff ℝ ∞ map
  norm_map : ∀ v, ‖map v‖ = 1
  agree :
    (fun s => (p s : Target m)) =ᶠ[𝓝 t]
      fun s => map (cubeDomain m s)
  det_ne_zero :
    (fderiv ℝ (fun v => horizontal m (map v))
      (cubeDomain m t)).det ≠ 0

/-- Every antipode preimage is transverse. -/
def Transverse
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) : Prop :=
  ∀ t, p t = -(SphereGenerator.canonicalBasepoint m) →
    Nonempty (RegularAt p t)

theorem regularizedGenLoop_transverse
    {q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)}
    (a : SmoothSphereApprox.Approximation q)
    {y : Domain m} (hy : ‖y‖ < 1 / 2)
    (hregular : ∀ v, horizontalMap a v = y →
      (fderiv ℝ (horizontalMap a) v).det ≠ 0) :
    Transverse (regularizedGenLoop a y hy) := by
  intro t ht
  refine ⟨{
    map := SphereRegularLocal.normalizedTransformed a y
    contDiff_map :=
      SphereRegularLocal.contDiff_normalizedTransformed a hy
    norm_map :=
      SphereRegularLocal.norm_normalizedTransformed a hy
    agree := Filter.Eventually.of_forall fun s => rfl
    det_ne_zero := ?_
  }⟩
  exact SphereRegularLocal.det_fderiv_horizontalNormalized_ne_zero
    a hy hregular ht

def regularAt_plateau
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (d : SpherePlateau.Datum)
    {t : Fin (m + 1) → I}
    (ht : p t = -(SphereGenerator.canonicalBasepoint m))
    (h : RegularAt p t) :
    RegularAt (SpherePlateau.genLoop d p) t := by
  have hvert :
      vertical m (p t) = 1 := by
    rw [ht]
    simp [vertical, coe_canonicalBasepoint]
  have hopen :
      IsOpen
        {s : Fin (m + 1) → I |
          d.upper < vertical m (p s)} :=
    isOpen_lt continuous_const <| by
      fun_prop
  have htopen :
      t ∈
        {s : Fin (m + 1) → I |
          d.upper < vertical m (p s)} := by
    change d.upper < vertical m (p t)
    rw [hvert]
    exact d.upper_lt_one
  have heq :
      (fun s => (SpherePlateau.genLoop d p s : Target m)) =ᶠ[𝓝 t]
        fun s => (p s : Target m) := by
    filter_upwards [hopen.mem_nhds htopen] with s hs
    exact congrArg Subtype.val <|
      SpherePlateau.map_eq_self_of_upper_le_vertical d hs.le
  exact {
    map := h.map
    contDiff_map := h.contDiff_map
    norm_map := h.norm_map
    agree := heq.trans h.agree
    det_ne_zero := h.det_ne_zero
  }

theorem transverse_plateau
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (d : SpherePlateau.Datum)
    (hp : Transverse p) :
    Transverse (SpherePlateau.genLoop d p) := by
  intro t ht
  have ht' : p t = -(SphereGenerator.canonicalBasepoint m) :=
    (SpherePlateau.map_eq_antipode_iff d (p t)).mp ht
  obtain ⟨h⟩ := hp t ht'
  exact ⟨regularAt_plateau p d ht' h⟩

/-- Diagonal scaling of one ambient cube coordinate. -/
def coordinateScaleMatrix
    (i : Fin (m + 1)) (c : ℝ) :
    Matrix (Fin (m + 1)) (Fin (m + 1)) ℝ :=
  diagonal fun j => if j = i then c else 1

def coordinateScaleCLM
    (i : Fin (m + 1)) (c : ℝ) :
    Domain m →L[ℝ] Domain m :=
  Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℝ)
    (coordinateScaleMatrix i c)

def coordinateShift
    (i : Fin (m + 1)) (c : ℝ) : Domain m :=
  WithLp.toLp 2 fun j => if j = i then c else 0

def leftAffine
    (i : Fin (m + 1)) (c : ℝ) (v : Domain m) :
    Domain m :=
  coordinateScaleCLM i c v

def rightAffine
    (i : Fin (m + 1)) (c : ℝ) (v : Domain m) :
    Domain m :=
  coordinateShift i c +
    coordinateScaleCLM i (1 - c) v

@[fun_prop]
theorem contDiff_leftAffine
    (i : Fin (m + 1)) (c : ℝ) :
    ContDiff ℝ ∞ (leftAffine i c) :=
  (coordinateScaleCLM i c).contDiff

@[fun_prop]
theorem contDiff_rightAffine
    (i : Fin (m + 1)) (c : ℝ) :
    ContDiff ℝ ∞ (rightAffine i c) := by
  unfold rightAffine
  fun_prop

theorem cubeDomain_leftCube
    (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (t : Fin (m + 1) → I) :
    cubeDomain m
        (SphereSplit.leftCube i c hc0 hc1 t) =
      leftAffine i c (cubeDomain m t) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubeDomain, SphereSplit.leftCube,
      SmoothSphereApprox.cubeCoe, SphereSplit.leftCoordinate, leftAffine,
      coordinateScaleCLM, coordinateScaleMatrix,
      Matrix.mulVec_diagonal]
  · simp [cubeDomain, SphereSplit.leftCube,
      SmoothSphereApprox.cubeCoe, leftAffine,
      coordinateScaleCLM, coordinateScaleMatrix,
      Matrix.mulVec_diagonal, hji]

theorem cubeDomain_rightCube
    (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (t : Fin (m + 1) → I) :
    cubeDomain m
        (SphereSplit.rightCube i c hc0 hc1 t) =
      rightAffine i c (cubeDomain m t) := by
  ext j
  by_cases hji : j = i
  · subst j
    simp [cubeDomain, SphereSplit.rightCube,
      SmoothSphereApprox.cubeCoe, SphereSplit.rightCoordinate, rightAffine,
      coordinateShift, coordinateScaleCLM,
      coordinateScaleMatrix, Matrix.mulVec_diagonal]
  · simp [cubeDomain, SphereSplit.rightCube,
      SmoothSphereApprox.cubeCoe, rightAffine,
      coordinateShift, coordinateScaleCLM,
      coordinateScaleMatrix, Matrix.mulVec_diagonal, hji]

theorem coordinateScaleMatrix_det_ne_zero
    (i : Fin (m + 1)) {c : ℝ} (hc : c ≠ 0) :
    (coordinateScaleMatrix i c).det ≠ 0 := by
  rw [coordinateScaleMatrix, det_diagonal]
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  by_cases hji : j = i
  · simpa [hji] using hc
  · simp [hji]

theorem coordinateScaleCLM_det_ne_zero
    (i : Fin (m + 1)) {c : ℝ} (hc : c ≠ 0) :
    (coordinateScaleCLM i c).det ≠ 0 := by
  change
    LinearMap.det
      (Matrix.toEuclideanCLM (n := Fin (m + 1)) (𝕜 := ℝ)
        (coordinateScaleMatrix i c) : Domain m →ₗ[ℝ] Domain m) ≠ 0
  rw [Matrix.coe_toEuclideanCLM_eq_toEuclideanLin,
    Matrix.toEuclideanLin_eq_toLin_orthonormal,
    LinearMap.det_toLin]
  exact coordinateScaleMatrix_det_ne_zero (m := m) i hc

theorem fderiv_leftAffine
    (i : Fin (m + 1)) (c : ℝ) (v : Domain m) :
    fderiv ℝ (leftAffine i c) v =
      coordinateScaleCLM i c :=
  (coordinateScaleCLM i c).hasFDerivAt.fderiv

theorem fderiv_rightAffine
    (i : Fin (m + 1)) (c : ℝ) (v : Domain m) :
    fderiv ℝ (rightAffine i c) v =
      coordinateScaleCLM i (1 - c) := by
  unfold rightAffine
  rw [fderiv_const_add]
  exact (coordinateScaleCLM i (1 - c)).hasFDerivAt.fderiv

private def regularAt_comp_affine
    (p r : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    {s t : Fin (m + 1) → I}
    (e : (Fin (m + 1) → I) → (Fin (m + 1) → I))
    (he : Continuous e)
    (affine : Domain m → Domain m)
    (haffine : ContDiff ℝ ∞ affine)
    (hcube : ∀ u, cubeDomain m (e u) = affine (cubeDomain m u))
    (happly : ∀ u, r u = p (e u))
    (hst : e s = t)
    (hdet :
      (fderiv ℝ affine (cubeDomain m s)).det ≠ 0)
    (h : RegularAt p t) :
    RegularAt r s := by
  let F : Domain m → Target m :=
    fun v => h.map (affine v)
  refine {
    map := F
    contDiff_map := h.contDiff_map.comp haffine
    norm_map := fun v => h.norm_map (affine v)
    agree := ?_
    det_ne_zero := ?_
  }
  · have he_at : Filter.Tendsto e (𝓝 s) (𝓝 t) := by
      have he_at' : Filter.Tendsto e (𝓝 s) (𝓝 (e s)) :=
        he.continuousAt
      rwa [hst] at he_at'
    have hagree := h.agree.comp_tendsto he_at
    filter_upwards [hagree] with u hu
    change (r u : Target m) = h.map (affine (cubeDomain m u))
    rw [happly u]
    change
      (p (e u) : Target m) = h.map (cubeDomain m (e u)) at hu
    rw [hu, hcube]
  · have hhorizontal :
        (fun v => horizontal m (F v)) =
          (fun v => horizontal m (h.map v)) ∘ affine :=
      rfl
    rw [hhorizontal, fderiv_comp
      (g := fun v => horizontal m (h.map v)) (cubeDomain m s)
      (((contDiff_horizontal m).comp h.contDiff_map
        |>.differentiable (by norm_num)).differentiableAt)
      ((haffine.differentiable
        (by norm_num)).differentiableAt)]
    change
      LinearMap.det
        ((fderiv ℝ (fun v => horizontal m (h.map v))
            (affine (cubeDomain m s))).toLinearMap.comp
          (fderiv ℝ affine (cubeDomain m s)).toLinearMap) ≠ 0
    rw [LinearMap.det_comp]
    apply mul_ne_zero
    · have hpoint :
          affine (cubeDomain m s) = cubeDomain m t := by
        rw [← hcube s, hst]
      simpa only [hpoint] using h.det_ne_zero
    · exact hdet

def regularAt_leftGenLoop
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t, (t i : ℝ) = c →
      p t = SphereGenerator.canonicalBasepoint m)
    {s : Fin (m + 1) → I}
    (h :
      RegularAt p
        (SphereSplit.leftCube i c hc0 hc1 s)) :
    RegularAt
      (SphereSplit.leftGenLoop p i c hc0 hc1 hcut) s := by
  apply regularAt_comp_affine p
    (SphereSplit.leftGenLoop p i c hc0 hc1 hcut)
    (SphereSplit.leftCube i c hc0 hc1)
    (SphereSplit.continuous_leftCube i c hc0 hc1)
    (leftAffine i c)
    (contDiff_leftAffine i c)
    (cubeDomain_leftCube i c hc0 hc1)
    (fun _ => rfl)
    rfl
    (by
      rw [fderiv_leftAffine]
      exact coordinateScaleCLM_det_ne_zero i hc0.ne')
    h

def regularAt_rightGenLoop
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t, (t i : ℝ) = c →
      p t = SphereGenerator.canonicalBasepoint m)
    {s : Fin (m + 1) → I}
    (h :
      RegularAt p
        (SphereSplit.rightCube i c hc0 hc1 s)) :
    RegularAt
      (SphereSplit.rightGenLoop p i c hc0 hc1 hcut) s := by
  apply regularAt_comp_affine p
    (SphereSplit.rightGenLoop p i c hc0 hc1 hcut)
    (SphereSplit.rightCube i c hc0 hc1)
    (SphereSplit.continuous_rightCube i c hc0 hc1)
    (rightAffine i c)
    (contDiff_rightAffine i c)
    (cubeDomain_rightCube i c hc0 hc1)
    (fun _ => rfl)
    rfl
    (by
      rw [fderiv_rightAffine]
      exact coordinateScaleCLM_det_ne_zero i <|
        sub_ne_zero.mpr hc1.ne')
    h

theorem transverse_leftGenLoop
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (hp : Transverse p)
    (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t, (t i : ℝ) = c →
      p t = SphereGenerator.canonicalBasepoint m) :
    Transverse
      (SphereSplit.leftGenLoop p i c hc0 hc1 hcut) := by
  intro s hs
  obtain ⟨h⟩ := hp _ hs
  exact ⟨regularAt_leftGenLoop p i c hc0 hc1 hcut h⟩

theorem transverse_rightGenLoop
    (p : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (hp : Transverse p)
    (i : Fin (m + 1)) (c : ℝ)
    (hc0 : 0 < c) (hc1 : c < 1)
    (hcut : ∀ t, (t i : ℝ) = c →
      p t = SphereGenerator.canonicalBasepoint m) :
    Transverse
      (SphereSplit.rightGenLoop p i c hc0 hc1 hcut) := by
  intro s hs
  obtain ⟨h⟩ := hp _ hs
  exact ⟨regularAt_rightGenLoop p i c hc0 hc1 hcut h⟩

end Submission.SphereTransverse
