import Submission.SphereDegreeHomotopy
import Submission.SphereSmoothBubbleCore

open scoped ContDiff unitInterval Topology

noncomputable section

namespace Submission.SphereSmoothJoin

open Set
open Submission.SphereRegularApprox
open Submission.SphereSmoothRepresentative
open Submission.SphereDegreeHomotopy

abbrev Space :=
  Fin 3 → ℝ

/-- A smooth compact representative with a quantitatively nonempty collar
on which it is the base point. -/
structure CollaredMap where
  toMap : Map 2
  collar : ℝ
  collar_pos : 0 < collar
  map_collar :
    ∀ x i, x i ≤ collar ∨ 1 - collar ≤ x i →
      toMap x =
        (SphereGenerator.canonicalBasepoint 2 : Target 2)

instance : CoeFun CollaredMap fun _ => Space → Target 2 :=
  ⟨fun F => F.toMap⟩

@[fun_prop]
theorem CollaredMap.contDiff (F : CollaredMap) :
    ContDiff ℝ ∞ F :=
  F.toMap.contDiff_toFun

def bubble : CollaredMap where
  toMap := SphereSmoothBubble.smoothMap
  collar := 1 / 4
  collar_pos := by norm_num
  map_collar := by
    intro x i hi
    apply SphereSmoothBubble.sphereMap_eq_basepoint_of_one_le_radiusSq
    apply SphereSmoothBubble.one_le_radiusSq_localCoordinates_of_quarter
    norm_num at hi ⊢
    exact hi

def leftTransform (x : Space) : Space :=
  Function.update x 0 (2 * x 0)

def rightTransform (x : Space) : Space :=
  Function.update x 0 (2 * x 0 - 1)

@[fun_prop]
theorem contDiff_leftTransform :
    ContDiff ℝ ∞ leftTransform := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [leftTransform, Function.update_self]
    fun_prop
  · simp [leftTransform, Function.update, hi]
    fun_prop

@[fun_prop]
theorem contDiff_rightTransform :
    ContDiff ℝ ∞ rightTransform := by
  rw [contDiff_pi]
  intro i
  by_cases hi : i = 0
  · subst i
    simp only [rightTransform, Function.update_self]
    fun_prop
  · simp [rightTransform, Function.update, hi]
    fun_prop

@[simp]
theorem leftTransform_zero (x : Space) :
    leftTransform x 0 = 2 * x 0 := by
  simp [leftTransform]

@[simp]
theorem rightTransform_zero (x : Space) :
    rightTransform x 0 = 2 * x 0 - 1 := by
  simp [rightTransform]

theorem leftTransform_apply_of_ne
    (x : Space) {i : Fin 3} (hi : i ≠ 0) :
    leftTransform x i = x i := by
  simp [leftTransform, hi]

theorem rightTransform_apply_of_ne
    (x : Space) {i : Fin 3} (hi : i ≠ 0) :
    rightTransform x i = x i := by
  simp [rightTransform, hi]

/-- Smooth connected sum along the first cubical coordinate. -/
def joinMap (F G : CollaredMap) : Map 2 where
  toFun := fun x =>
    F (leftTransform x) + G (rightTransform x) -
      (SphereGenerator.canonicalBasepoint 2 : Target 2)
  contDiff_toFun := by
    fun_prop
  norm_toFun := by
    intro x
    by_cases hx : x 0 ≤ 1 / 2
    · rw [G.toMap.map_outer (rightTransform x) 0
        (Or.inl <| by simp; linarith)]
      simp
      exact F.toMap.norm_toFun _
    · rw [F.toMap.map_outer (leftTransform x) 0
        (Or.inr <| by simp; linarith)]
      simp
      exact G.toMap.norm_toFun _
  map_outer := by
    intro x i hi
    have hF :
        F (leftTransform x) =
          (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
      by_cases hi0 : i = 0
      · subst i
        rcases hi with hi | hi
        · apply F.toMap.map_outer _ 0 (Or.inl ?_)
          simp
          linarith
        · apply F.toMap.map_outer _ 0 (Or.inr ?_)
          simp
          linarith
      · apply F.toMap.map_outer _ i
        simpa [leftTransform_apply_of_ne x hi0] using hi
    have hG :
        G (rightTransform x) =
          (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
      by_cases hi0 : i = 0
      · subst i
        rcases hi with hi | hi
        · apply G.toMap.map_outer _ 0 (Or.inl ?_)
          simp
          linarith
        · apply G.toMap.map_outer _ 0 (Or.inr ?_)
          simp
          linarith
      · apply G.toMap.map_outer _ i
        simpa [rightTransform_apply_of_ne x hi0] using hi
    rw [hF, hG]
    module

def join (F G : CollaredMap) : CollaredMap where
  toMap := joinMap F G
  collar := min F.collar G.collar / 2
  collar_pos := half_pos (lt_min F.collar_pos G.collar_pos)
  map_collar := by
    intro x i hi
    have hwidthF :
        min F.collar G.collar ≤ F.collar :=
      min_le_left _ _
    have hwidthG :
        min F.collar G.collar ≤ G.collar :=
      min_le_right _ _
    have hwidth_pos :
        0 < min F.collar G.collar :=
      lt_min F.collar_pos G.collar_pos
    have hF :
        F (leftTransform x) =
          (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
      by_cases hi0 : i = 0
      · subst i
        rcases hi with hi | hi
        · apply F.map_collar _ 0 (Or.inl ?_)
          simp
          linarith
        · apply F.map_collar _ 0 (Or.inr ?_)
          simp
          linarith
      · apply F.map_collar _ i
        rcases hi with hi | hi
        · left
          rw [leftTransform_apply_of_ne x hi0]
          linarith
        · right
          rw [leftTransform_apply_of_ne x hi0]
          linarith
    have hG :
        G (rightTransform x) =
          (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
      by_cases hi0 : i = 0
      · subst i
        rcases hi with hi | hi
        · apply G.map_collar _ 0 (Or.inl ?_)
          simp
          linarith
        · apply G.map_collar _ 0 (Or.inr ?_)
          simp
          linarith
      · apply G.map_collar _ i
        rcases hi with hi | hi
        · left
          rw [rightTransform_apply_of_ne x hi0]
          linarith
        · right
          rw [rightTransform_apply_of_ne x hi0]
          linarith
    change
      F (leftTransform x) + G (rightTransform x) -
        (SphereGenerator.canonicalBasepoint 2 : Target 2) =
      (SphereGenerator.canonicalBasepoint 2 : Target 2)
    rw [hF, hG]
    module

theorem join_genLoop
    (F G : CollaredMap) :
    (join F G).toMap.genLoop =
      GenLoop.transAt (0 : Fin 3)
        F.toMap.genLoop G.toMap.genLoop := by
  apply GenLoop.ext
  intro t
  apply Subtype.ext
  change
    F (leftTransform (SmoothSphereApprox.cubeCoe t)) +
        G (rightTransform (SmoothSphereApprox.cubeCoe t)) -
          (SphereGenerator.canonicalBasepoint 2 : Target 2) =
      ((GenLoop.transAt (0 : Fin 3)
        F.toMap.genLoop G.toMap.genLoop t : UnitSphere 2) :
          Target 2)
  rw [GenLoop.transAt, GenLoop.coe_copy]
  split_ifs with ht
  · rw [G.toMap.map_outer
      (rightTransform (SmoothSphereApprox.cubeCoe t)) 0
      (Or.inl <| by
        simp [rightTransform, SmoothSphereApprox.cubeCoe]
        linarith)]
    simp only [add_sub_cancel_right]
    congr 2
    ext i
    by_cases hi : i = 0
    · subst i
      simp [leftTransform, SmoothSphereApprox.cubeCoe,
        Function.update]
      rw [projIcc_of_mem]
      constructor <;> linarith [t 0 |>.property.1]
    · simp [leftTransform, SmoothSphereApprox.cubeCoe,
        Function.update, hi]
  · rw [F.toMap.map_outer
      (leftTransform (SmoothSphereApprox.cubeCoe t)) 0
      (Or.inr <| by
        simp [leftTransform, SmoothSphereApprox.cubeCoe]
        linarith)]
    simp only [add_sub_cancel_left]
    congr 2
    ext i
    by_cases hi : i = 0
    · subst i
      simp [rightTransform, SmoothSphereApprox.cubeCoe,
        Function.update]
      rw [projIcc_of_mem]
      constructor
      · linarith [t 0 |>.property.1]
      · have := t 0 |>.property.2
        linarith
    · simp [rightTransform, SmoothSphereApprox.cubeCoe,
        Function.update, hi]

private theorem eventually_join_eq_left
    (F G : CollaredMap) {x : Space}
    (hx : x 0 < 1 / 2) :
    (join F G : Space → Target 2) =ᶠ[𝓝 x]
      fun y => F (leftTransform y) := by
  have hopen : IsOpen {y : Space | y 0 < 1 / 2} :=
    isOpen_lt (continuous_apply 0) continuous_const
  filter_upwards [hopen.mem_nhds hx] with y hy
  change
    F (leftTransform y) + G (rightTransform y) -
        (SphereGenerator.canonicalBasepoint 2 : Target 2) =
      F (leftTransform y)
  rw [G.toMap.map_outer (rightTransform y) 0
    (Or.inl <| by simp; linarith)]
  module

private theorem eventually_join_eq_right
    (F G : CollaredMap) {x : Space}
    (hx : 1 / 2 < x 0) :
    (join F G : Space → Target 2) =ᶠ[𝓝 x]
      fun y => G (rightTransform y) := by
  have hopen : IsOpen {y : Space | 1 / 2 < y 0} :=
    isOpen_lt continuous_const (continuous_apply 0)
  filter_upwards [hopen.mem_nhds hx] with y hy
  change
    F (leftTransform y) + G (rightTransform y) -
        (SphereGenerator.canonicalBasepoint 2 : Target 2) =
      G (rightTransform y)
  rw [F.toMap.map_outer (leftTransform y) 0
    (Or.inr <| by simp; linarith)]
  module

private theorem eventually_join_eq_base_at_middle
    (F G : CollaredMap) {x : Space}
    (hx : x 0 = 1 / 2) :
    (join F G : Space → Target 2) =ᶠ[𝓝 x]
      fun _ =>
        (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
  let δ := min F.collar G.collar / 2
  have hδ : 0 < δ :=
    half_pos (lt_min F.collar_pos G.collar_pos)
  have hopen :
      IsOpen {y : Space | |y 0 - 1 / 2| < δ} :=
    isOpen_lt (by fun_prop) continuous_const
  have hxopen : x ∈ {y : Space | |y 0 - 1 / 2| < δ} := by
    simp [hx, hδ]
  filter_upwards [hopen.mem_nhds hxopen] with y hy
  have hylo : 1 / 2 - δ < y 0 := by
    rw [abs_lt] at hy
    linarith
  have hyhi : y 0 < 1 / 2 + δ := by
    rw [abs_lt] at hy
    linarith
  have hF :
      F (leftTransform y) =
        (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
    apply F.map_collar _ 0
    right
    simp only [leftTransform_zero]
    dsimp [δ] at hylo
    have := min_le_left F.collar G.collar
    linarith
  have hG :
      G (rightTransform y) =
        (SphereGenerator.canonicalBasepoint 2 : Target 2) := by
    apply G.map_collar _ 0
    left
    simp only [rightTransform_zero]
    dsimp [δ] at hyhi
    have := min_le_right F.collar G.collar
    linarith
  change
    F (leftTransform y) + G (rightTransform y) -
        (SphereGenerator.canonicalBasepoint 2 : Target 2) =
      (SphereGenerator.canonicalBasepoint 2 : Target 2)
  rw [hF, hG]
  module

def scaleFirstCLM : Space →L[ℝ] Space where
  toFun v := Function.update v 0 (2 * v 0)
  map_add' v w := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp
      ring
    · simp [hi]
  map_smul' c v := by
    ext i
    by_cases hi : i = 0
    · subst i
      simp
      ring
    · simp [hi]
  cont := by fun_prop

@[simp]
theorem scaleFirstCLM_apply (v : Space) :
    scaleFirstCLM v =
      Function.update v 0 (2 * v 0) :=
  rfl

theorem fderiv_leftTransform (x : Space) :
    fderiv ℝ leftTransform x = scaleFirstCLM := by
  exact scaleFirstCLM.hasFDerivAt.fderiv

theorem fderiv_rightTransform (x : Space) :
    fderiv ℝ rightTransform x = scaleFirstCLM := by
  have h :
      rightTransform =
        fun y => leftTransform y -
          Function.update (0 : Space) 0 1 := by
    funext y
    ext i
    by_cases hi : i = 0
    · subst i
      simp [rightTransform, leftTransform]
    · simp [rightTransform, leftTransform, hi]
  rw [h, fderiv_sub_const]
  exact fderiv_leftTransform x

private theorem scaleFirstCLM_frame
    (i : Fin 3) :
    scaleFirstCLM (spatialFrame i) =
      if i = 0 then
        (2 : ℝ) • spatialFrame 0
      else spatialFrame i := by
  ext j
  fin_cases i <;> fin_cases j <;>
    simp [scaleFirstCLM, spatialFrame]

private theorem density_comp_transform
    {F : Space → Target 2}
    (hF : ContDiff ℝ ∞ F)
    (T : Space → Space)
    (hT : ContDiff ℝ ∞ T)
    (hderiv : ∀ x, fderiv ℝ T x = scaleFirstCLM)
    (x : Space) :
    density (F ∘ T) x =
      2 * density F (T x) := by
  rw [density, density,
    SphereDegreeInvariant.pulledVolumeForm,
    SphereDegreeInvariant.pulledVolumeForm,
    fderiv_comp x
      ((hF.differentiable
        (by norm_num)).differentiableAt)
      ((hT.differentiable
        (by norm_num)).differentiableAt),
    hderiv]
  let V : Fin 3 → Target 2 :=
    fun i => fderiv ℝ F (T x) (spatialFrame i)
  have hvec :
      (fun i =>
        fderiv ℝ F (T x)
          (scaleFirstCLM (spatialFrame i))) =
        Function.update V 0 ((2 : ℝ) • V 0) := by
    funext i
    fin_cases i
    · rw [scaleFirstCLM_frame]
      change
        fderiv ℝ F (T x) ((2 : ℝ) • spatialFrame 0) =
          (2 : ℝ) • fderiv ℝ F (T x) (spatialFrame 0)
      exact map_smul (fderiv ℝ F (T x)) 2 (spatialFrame 0)
    · rw [scaleFirstCLM_frame]
      simp [V]
    · rw [scaleFirstCLM_frame]
      simp [V]
  change
    SphereDegreeForm.volumeForm 2 (F (T x))
        (fun i =>
          fderiv ℝ F (T x)
            (scaleFirstCLM (spatialFrame i))) =
      2 *
        SphereDegreeForm.volumeForm 2 (F (T x))
          (fun i =>
            fderiv ℝ F (T x) (spatialFrame i))
  rw [hvec]
  change
    SphereDegreeForm.volumeForm 2 (F (T x))
        (Function.update V 0 ((2 : ℝ) • V 0)) =
      2 * SphereDegreeForm.volumeForm 2 (F (T x)) V
  calc
    _ = 2 •
        SphereDegreeForm.volumeForm 2 (F (T x))
          (Function.update V 0 (V 0)) :=
      (SphereDegreeForm.volumeForm 2 (F (T x))).map_update_smul
        V 0 2 (V 0)
    _ = _ := by simp

theorem density_comp_leftTransform
    {F : Space → Target 2}
    (hF : ContDiff ℝ ∞ F) (x : Space) :
    density (F ∘ leftTransform) x =
      2 * density F (leftTransform x) :=
  density_comp_transform hF leftTransform
    contDiff_leftTransform fderiv_leftTransform x

theorem density_comp_rightTransform
    {F : Space → Target 2}
    (hF : ContDiff ℝ ∞ F) (x : Space) :
    density (F ∘ rightTransform) x =
      2 * density F (rightTransform x) :=
  density_comp_transform hF rightTransform
    contDiff_rightTransform fderiv_rightTransform x

theorem density_join_of_lt
    (F G : CollaredMap) {x : Space}
    (hx : x 0 < 1 / 2) :
    density (join F G) x =
      2 * density F (leftTransform x) := by
  calc
    density (join F G) x =
        density (fun y => F (leftTransform y)) x := by
      unfold density SphereDegreeInvariant.pulledVolumeForm
      rw [(eventually_join_eq_left F G hx).self_of_nhds,
        (eventually_join_eq_left F G hx).fderiv_eq]
    _ = 2 * density F (leftTransform x) := by
      change
        density (F.toMap.toFun ∘ leftTransform) x =
          2 * density F.toMap.toFun (leftTransform x)
      exact density_comp_leftTransform F.contDiff x

theorem density_join_of_gt
    (F G : CollaredMap) {x : Space}
    (hx : 1 / 2 < x 0) :
    density (join F G) x =
      2 * density G (rightTransform x) := by
  calc
    density (join F G) x =
        density (fun y => G (rightTransform y)) x := by
      unfold density SphereDegreeInvariant.pulledVolumeForm
      rw [(eventually_join_eq_right F G hx).self_of_nhds,
        (eventually_join_eq_right F G hx).fderiv_eq]
    _ = 2 * density G (rightTransform x) := by
      change
        density (G.toMap.toFun ∘ rightTransform) x =
          2 * density G.toMap.toFun (rightTransform x)
      exact density_comp_rightTransform G.contDiff x

theorem density_join_of_eq
    (F G : CollaredMap) {x : Space}
    (hx : x 0 = 1 / 2) :
    density (join F G) x = 0 := by
  have heq := eventually_join_eq_base_at_middle F G hx
  unfold density SphereDegreeInvariant.pulledVolumeForm
  rw [heq.self_of_nhds, heq.fderiv_eq, fderiv_const_apply]
  simp [SphereDegreeForm.volumeForm_apply]
  apply (SphereDegreeForm.determinantForm 2).map_coord_zero
    (1 : Fin 4)
  simp

theorem neg_density_join_nonneg
    (F G : CollaredMap)
    (hF : ∀ x, 0 ≤ -density F x)
    (hG : ∀ x, 0 ≤ -density G x)
    (x : Space) :
    0 ≤ -density (join F G) x := by
  rcases lt_trichotomy (x 0) (1 / 2) with hx | hx | hx
  · rw [density_join_of_lt F G hx]
    linarith [hF (leftTransform x)]
  · rw [density_join_of_eq F G hx]
    norm_num
  · rw [density_join_of_gt F G hx]
    linarith [hG (rightTransform x)]

theorem density_join_left_nonzero
    (F G : CollaredMap) {x : Space}
    (hx : x 0 < 1 / 2)
    (h : density F (leftTransform x) ≠ 0) :
    density (join F G) x ≠ 0 := by
  rw [density_join_of_lt F G hx]
  exact mul_ne_zero (by norm_num) h

theorem density_join_right_nonzero
    (F G : CollaredMap) {x : Space}
    (hx : 1 / 2 < x 0)
    (h : density G (rightTransform x) ≠ 0) :
    density (join F G) x ≠ 0 := by
  rw [density_join_of_gt F G hx]
  exact mul_ne_zero (by norm_num) h

end Submission.SphereSmoothJoin
