import Submission.SmoothSphereApprox
import Submission.SphereRegularApprox

open scoped unitInterval Topology ContDiff

noncomputable section

namespace Submission.SphereSmoothRepresentative

open Set
open Submission.SphereRegularApprox
open Submission.SphereHomotopy

variable {m : ℕ}

abbrev Ambient (m : ℕ) :=
  Fin (m + 1) → ℝ

abbrev HomotopyAmbient (m : ℕ) :=
  Fin (m + 2) → ℝ

/-- A globally smooth unit-sphere map which is the base point on and beyond
every face of the ambient unit cube. -/
structure Map (m : ℕ) where
  toFun : Ambient m → Target m
  contDiff_toFun : ContDiff ℝ ∞ toFun
  norm_toFun : ∀ v, ‖toFun v‖ = 1
  map_outer :
    ∀ v i, v i ≤ 0 ∨ 1 ≤ v i →
      toFun v =
        (SphereGenerator.canonicalBasepoint m : Target m)

instance : CoeFun (Map m) fun _ => Ambient m → Target m :=
  ⟨Map.toFun⟩

@[fun_prop]
theorem Map.contDiff (F : Map m) :
    ContDiff ℝ ∞ F :=
  F.contDiff_toFun

theorem Map.continuous (F : Map m) :
    Continuous F :=
  F.contDiff_toFun.continuous

def Map.toUnitSphere (F : Map m) (v : Ambient m) :
    UnitSphere m :=
  ⟨F v, by
    rw [Metric.mem_sphere, dist_zero_right]
    exact F.norm_toFun v⟩

theorem Map.continuous_toUnitSphere (F : Map m) :
    Continuous F.toUnitSphere :=
  F.continuous.subtype_mk _

theorem Map.map_cubeBoundary
    (F : Map m) {t : Fin (m + 1) → I}
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    F (SmoothSphereApprox.cubeCoe t) =
      (SphereGenerator.canonicalBasepoint m : Target m) := by
  obtain ⟨i, hi | hi⟩ := ht
  · apply F.map_outer _ i (Or.inl ?_)
    simp [SmoothSphereApprox.cubeCoe, hi]
  · apply F.map_outer _ i (Or.inr ?_)
    simp [SmoothSphereApprox.cubeCoe, hi]

/-- Restrict a smooth compact ambient map to the unit cube. -/
def Map.genLoop (F : Map m) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨fun t => F.toUnitSphere (SmoothSphereApprox.cubeCoe t),
      F.continuous_toUnitSphere.comp
        SmoothSphereApprox.continuous_cubeCoe⟩,
    fun t ht => by
      apply Subtype.ext
      exact F.map_cubeBoundary ht⟩

@[simp]
theorem Map.genLoop_apply (F : Map m)
    (t : Fin (m + 1) → I) :
    (F.genLoop t : Target m) =
      F (SmoothSphereApprox.cubeCoe t) :=
  rfl

/-- The constant smooth representative. -/
def const (m : ℕ) : Map m where
  toFun := fun _ =>
    (SphereGenerator.canonicalBasepoint m : Target m)
  contDiff_toFun := contDiff_const
  norm_toFun := fun _ =>
    SphereGenerator.sphere_norm_eq_one m
      (SphereGenerator.canonicalBasepoint m)
  map_outer := fun _ _ _ => rfl

@[simp]
theorem const_genLoop :
    (const m).genLoop = GenLoop.const := by
  ext t
  rfl

private theorem project_eq_self_of_mem_cube
    {v : Ambient m}
    (hv : v ∈ Set.Icc (0 : Ambient m) 1) :
    SmoothSphereApprox.cubeCoe
        (SmoothSphereApprox.project v) = v := by
  funext i
  rw [SmoothSphereApprox.cubeCoe, SmoothSphereApprox.project,
    coe_projIcc]
  change max 0 (min 1 (v i)) = v i
  have hlow : 0 ≤ v i := by simpa using hv.1 i
  have hupp : v i ≤ 1 := by simpa using hv.2 i
  simp [hlow, hupp]

theorem Map.project_eq (F : Map m) (v : Ambient m) :
    F (SmoothSphereApprox.cubeCoe
        (SmoothSphereApprox.project v)) = F v := by
  by_cases hv : v ∈ Set.Icc (0 : Ambient m) 1
  · rw [project_eq_self_of_mem_cube hv]
  · rw [Set.mem_Icc, not_and_or] at hv
    rcases hv with hv | hv
    · change ¬ ∀ i, 0 ≤ v i at hv
      push Not at hv
      obtain ⟨i, hi⟩ := hv
      rw [F.map_outer v i (Or.inl hi.le)]
      apply F.map_outer _ i
      left
      change
        ((projIcc 0 1 zero_le_one (v i) : I) : ℝ) ≤ 0
      rw [projIcc_of_le_left zero_le_one hi.le]
    · change ¬ ∀ i, v i ≤ 1 at hv
      push Not at hv
      obtain ⟨i, hi⟩ := hv
      rw [F.map_outer v i (Or.inr hi.le)]
      apply F.map_outer _ i
      right
      change
        1 ≤ ((projIcc 0 1 zero_le_one (v i) : I) : ℝ)
      rw [projIcc_of_right_le zero_le_one hi.le]

def prepend (s : ℝ) (x : Ambient m) :
    HomotopyAmbient m :=
  Fin.cons s x

def spatialPart (v : HomotopyAmbient m) :
    Ambient m :=
  fun i => v i.succ

@[simp]
theorem prepend_zero_apply (s : ℝ) (x : Ambient m) :
    prepend s x 0 = s :=
  rfl

@[simp]
theorem prepend_succ_apply (s : ℝ) (x : Ambient m)
    (i : Fin (m + 1)) :
    prepend s x i.succ = x i :=
  rfl

@[simp]
theorem spatialPart_prepend (s : ℝ) (x : Ambient m) :
    spatialPart (prepend s x) = x :=
  rfl

@[fun_prop]
theorem contDiff_spatialPart :
    ContDiff ℝ ∞ (@spatialPart m) := by
  unfold spatialPart
  fun_prop

def projectHomotopy (v : HomotopyAmbient m) :
    I × (Fin (m + 1) → I) :=
  (SmoothSphereApprox.project v 0,
    fun i => SmoothSphereApprox.project v i.succ)

@[fun_prop]
theorem continuous_projectHomotopy :
    Continuous (@projectHomotopy m) := by
  unfold projectHomotopy
  fun_prop

theorem projectHomotopy_prepend
    (s : I) (x : Ambient m) :
    projectHomotopy (prepend (s : ℝ) x) =
      (s, SmoothSphereApprox.project x) := by
  apply Prod.ext
  · apply Subtype.ext
    change
      ((projIcc 0 1 zero_le_one (s : ℝ) : I) : ℝ) = s
    exact congrArg Subtype.val
      (projIcc_of_mem zero_le_one s.property)
  · funext i
    rfl

variable {F G : Map m}

/-- Extend a relative cubical homotopy continuously to all ambient
coordinates by projecting each coordinate to the unit interval. -/
def extended
    (H : F.genLoop.1.HomotopyRel G.genLoop.1
      (Cube.boundary (Fin (m + 1))))
    (v : HomotopyAmbient m) : Target m :=
  (H (projectHomotopy v) : UnitSphere m)

theorem continuous_extended
    (H : F.genLoop.1.HomotopyRel G.genLoop.1
      (Cube.boundary (Fin (m + 1)))) :
    Continuous (extended H) :=
  continuous_subtype_val.comp <|
    H.continuous.comp continuous_projectHomotopy

/-- The smooth affine reference joining the prescribed endpoint maps. -/
def reference (F G : Map m)
    (v : HomotopyAmbient m) : Target m :=
  (1 - v 0) • F (spatialPart v) +
    v 0 • G (spatialPart v)

@[fun_prop]
theorem contDiff_reference (F G : Map m) :
    ContDiff ℝ ∞ (reference F G) := by
  unfold reference
  fun_prop

def residual
    (H : F.genLoop.1.HomotopyRel G.genLoop.1
      (Cube.boundary (Fin (m + 1))))
    (v : HomotopyAmbient m) : Target m :=
  extended H v - reference F G v

theorem continuous_residual
    (H : F.genLoop.1.HomotopyRel G.genLoop.1
      (Cube.boundary (Fin (m + 1)))) :
    Continuous (residual H) :=
  (continuous_extended H).sub
    (contDiff_reference F G).continuous

theorem residual_prepend_zero
    (H : F.genLoop.1.HomotopyRel G.genLoop.1
      (Cube.boundary (Fin (m + 1))))
    (x : Ambient m) :
    residual H (prepend 0 x) = 0 := by
  have hp :
      projectHomotopy (prepend 0 x) =
        ((0 : I), SmoothSphereApprox.project x) :=
    projectHomotopy_prepend (0 : I) x
  rw [residual, extended, hp, reference,
    prepend_zero_apply, spatialPart_prepend]
  norm_num
  exact sub_eq_zero.mpr (F.project_eq x)

theorem residual_prepend_one
    (H : F.genLoop.1.HomotopyRel G.genLoop.1
      (Cube.boundary (Fin (m + 1))))
    (x : Ambient m) :
    residual H (prepend 1 x) = 0 := by
  have hp :
      projectHomotopy (prepend 1 x) =
        ((1 : I), SmoothSphereApprox.project x) :=
    projectHomotopy_prepend (1 : I) x
  rw [residual, extended, hp, reference,
    prepend_zero_apply, spatialPart_prepend]
  norm_num
  exact sub_eq_zero.mpr (G.project_eq x)

private theorem projectedSpatial_mem_boundary
    {v : HomotopyAmbient m} {i : Fin (m + 1)}
    (hi : v i.succ ≤ 0 ∨ 1 ≤ v i.succ) :
    (projectHomotopy v).2 ∈
      Cube.boundary (Fin (m + 1)) := by
  refine ⟨i, ?_⟩
  rcases hi with hi | hi
  · left
    apply Subtype.ext
    simp [projectHomotopy, SmoothSphereApprox.project, hi]
  · right
    apply Subtype.ext
    simp [projectHomotopy, SmoothSphereApprox.project, hi]

theorem residual_spatialBoundary
    (H : F.genLoop.1.HomotopyRel G.genLoop.1
      (Cube.boundary (Fin (m + 1))))
    {v : HomotopyAmbient m} {i : Fin (m + 1)}
    (hi : v i.succ ≤ 0 ∨ 1 ≤ v i.succ) :
    residual H v = 0 := by
  have hboundary := projectedSpatial_mem_boundary hi
  have hF :
      F (spatialPart v) =
        (SphereGenerator.canonicalBasepoint m : Target m) :=
    F.map_outer _ i hi
  have hG :
      G (spatialPart v) =
        (SphereGenerator.canonicalBasepoint m : Target m) :=
    G.map_outer _ i hi
  have hH :
      extended H v =
        (SphereGenerator.canonicalBasepoint m : Target m) := by
    apply congrArg Subtype.val
    exact calc
      H (projectHomotopy v) =
          F.genLoop (projectHomotopy v).2 :=
        H.prop' (projectHomotopy v).1
          (projectHomotopy v).2 hboundary
      _ = SphereGenerator.canonicalBasepoint m :=
        F.genLoop.property _ hboundary
  rw [residual, hH, reference, hF, hG]
  module

/-- A globally smooth sphere-valued relative homotopy with exact prescribed
smooth endpoint maps. -/
structure SmoothHomotopy (F G : Map m) where
  toFun : HomotopyAmbient m → Target m
  contDiff_toFun : ContDiff ℝ ∞ toFun
  norm_toFun : ∀ v, ‖toFun v‖ = 1
  map_zero : ∀ x, toFun (prepend 0 x) = F x
  map_one : ∀ x, toFun (prepend 1 x) = G x
  map_spatialBoundary :
    ∀ (v : HomotopyAmbient m) (i : Fin (m + 1)),
      v i.succ ≤ 0 ∨ 1 ≤ v i.succ →
      toFun v =
        (SphereGenerator.canonicalBasepoint m : Target m)

/-- Smooth approximation relative to all endpoint and spatial boundary
hyperplanes. -/
theorem exists_smoothHomotopy
    (H : F.genLoop.1.HomotopyRel G.genLoop.1
      (Cube.boundary (Fin (m + 1)))) :
    Nonempty (SmoothHomotopy F G) := by
  obtain ⟨g, hg, hclose, hsupp⟩ :=
    (continuous_residual H).exists_contDiff_approx ⊤
      (ε := fun _ => (1 / 2 : ℝ)) continuous_const
      (fun _ => by norm_num)
  have hgzero :
      ∀ v, residual H v = 0 → g v = 0 := by
    intro v hv
    by_contra hgv
    exact (hsupp hgv) hv
  let raw : HomotopyAmbient m → Target m :=
    fun v => reference F G v + g v
  have hrawDiff : ContDiff ℝ ∞ raw :=
    (contDiff_reference F G).add hg
  have hrawClose :
      ∀ v, dist (raw v) (extended H v) < 1 / 2 := by
    intro v
    have heq :
        raw v - extended H v =
          g v - residual H v := by
      dsimp only [raw, residual]
      module
    rw [dist_eq_norm, heq]
    simpa only [dist_eq_norm] using hclose v
  have hrawNe : ∀ v, raw v ≠ 0 := by
    intro v hv
    have h := hrawClose v
    rw [hv, dist_zero_left, show ‖extended H v‖ = 1 from
      SphereHomotopy.norm_coe_unitSphere
        (H (projectHomotopy v))] at h
    norm_num at h
  let K : HomotopyAmbient m → Target m :=
    fun v => NormedSpace.normalize (raw v)
  have hKDiff : ContDiff ℝ ∞ K := by
    change ContDiff ℝ ∞ (fun v => ‖raw v‖⁻¹ • raw v)
    exact
      ((hrawDiff.norm ℝ hrawNe).inv fun v =>
        norm_ne_zero_iff.mpr (hrawNe v)).smul hrawDiff
  have hKnorm : ∀ v, ‖K v‖ = 1 :=
    fun v => NormedSpace.norm_normalize (hrawNe v)
  have hKeq :
      ∀ v, residual H v = 0 → K v = extended H v := by
    intro v hv
    have hg0 := hgzero v hv
    have hraw : raw v = extended H v := by
      simp only [raw, hg0, add_zero]
      exact (sub_eq_zero.mp hv).symm
    simp only [K, hraw]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (SphereHomotopy.norm_coe_unitSphere
        (H (projectHomotopy v)))
  refine ⟨{
    toFun := K
    contDiff_toFun := hKDiff
    norm_toFun := hKnorm
    map_zero := fun x => ?_
    map_one := fun x => ?_
    map_spatialBoundary := fun v i hi => ?_
  }⟩
  · rw [hKeq _ (residual_prepend_zero H x)]
    have hp :
        projectHomotopy (prepend 0 x) =
          ((0 : I), SmoothSphereApprox.project x) :=
      projectHomotopy_prepend (0 : I) x
    rw [extended, hp]
    calc
      ((H ((0 : I), SmoothSphereApprox.project x) :
          UnitSphere m) : Target m) =
          (F.genLoop (SmoothSphereApprox.project x) :
            UnitSphere m) :=
        congrArg Subtype.val
          (H.map_zero_left (SmoothSphereApprox.project x))
      _ = F x := F.project_eq x
  · rw [hKeq _ (residual_prepend_one H x)]
    have hp :
        projectHomotopy (prepend 1 x) =
          ((1 : I), SmoothSphereApprox.project x) :=
      projectHomotopy_prepend (1 : I) x
    rw [extended, hp]
    calc
      ((H ((1 : I), SmoothSphereApprox.project x) :
          UnitSphere m) : Target m) =
          (G.genLoop (SmoothSphereApprox.project x) :
            UnitSphere m) :=
        congrArg Subtype.val
          (H.map_one_left (SmoothSphereApprox.project x))
      _ = G x := G.project_eq x
  · rw [hKeq _ (residual_spatialBoundary H hi)]
    unfold extended
    apply congrArg Subtype.val
    have hboundary := projectedSpatial_mem_boundary hi
    exact calc
      H (projectHomotopy v) =
          F.genLoop (projectHomotopy v).2 :=
        H.prop' (projectHomotopy v).1
          (projectHomotopy v).2 hboundary
      _ = SphereGenerator.canonicalBasepoint m :=
        F.genLoop.property _ hboundary

end Submission.SphereSmoothRepresentative
