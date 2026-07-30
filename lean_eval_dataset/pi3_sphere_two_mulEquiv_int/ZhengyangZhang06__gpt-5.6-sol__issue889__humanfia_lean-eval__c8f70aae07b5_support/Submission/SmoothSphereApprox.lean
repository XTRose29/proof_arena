import Mathlib
import Submission.CubeCollar
import Submission.SphereRawHomotopy

open scoped unitInterval Topology ContDiff

noncomputable section

namespace Submission.SmoothSphereApprox

open Set
open Submission.SphereHomotopy

variable {N E : Type*}
variable [NormedAddCommGroup E]

abbrev Ambient (N : Type*) :=
  N → ℝ

/-- Project ambient coordinates to the unit cube. -/
def project (v : Ambient N) : N → I :=
  fun i => projIcc 0 1 zero_le_one (v i)

@[continuity, fun_prop]
theorem continuous_project : Continuous (@project N) := by
  change Continuous (fun v : Ambient N => fun i =>
    projIcc 0 1 zero_le_one (v i))
  exact continuous_pi fun i => continuous_projIcc.comp (continuous_apply i)

/-- Include the unit cube in its ambient real vector space. -/
def cubeCoe (t : N → I) : Ambient N :=
  fun i => (t i : ℝ)

@[continuity, fun_prop]
theorem continuous_cubeCoe : Continuous (@cubeCoe N) := by
  change Continuous (fun t : N → I => fun i => (t i : ℝ))
  exact continuous_pi fun i =>
    continuous_subtype_val.comp (continuous_apply i)

@[simp]
theorem project_cubeCoe (t : N → I) :
    project (cubeCoe t) = t := by
  ext i
  exact congrArg Subtype.val (projIcc_val zero_le_one (t i))

/-- The union of the coordinate hyperplanes through the cubical boundary. -/
def ambientBoundary (N : Type*) : Set (Ambient N) :=
  {v | ∃ i, v i = 0 ∨ v i = 1}

theorem isClosed_ambientBoundary (N : Type*) [Fintype N] :
    IsClosed (ambientBoundary N) := by
  rw [show ambientBoundary N =
      ⋃ i, {v : Ambient N | v i = 0} ∪ {v : Ambient N | v i = 1} by
    ext v
    simp [ambientBoundary]]
  apply isClosed_iUnion_of_finite
  intro i
  exact
    (isClosed_eq (continuous_apply i) continuous_const).union
      (isClosed_eq (continuous_apply i) continuous_const)

/-- An ambient open neighborhood of all cubical boundary hyperplanes. -/
def ambientNeighborhood (N : Type*) : Set (Ambient N) :=
  {v | ∃ i, v i < 1 / 4 ∨ 3 / 4 < v i}

theorem isOpen_ambientNeighborhood (N : Type*) :
    IsOpen (ambientNeighborhood N) := by
  rw [show ambientNeighborhood N =
      ⋃ i, {v : Ambient N | v i < 1 / 4} ∪
        {v : Ambient N | 3 / 4 < v i} by
    ext v
    simp [ambientNeighborhood]]
  apply isOpen_iUnion
  intro i
  exact
    (isOpen_lt (continuous_apply i) continuous_const).union
      (isOpen_lt continuous_const (continuous_apply i))

theorem ambientBoundary_subset_neighborhood (N : Type*) :
    ambientBoundary N ⊆ ambientNeighborhood N := by
  rintro v ⟨i, hi | hi⟩
  · exact ⟨i, Or.inl (by norm_num [hi])⟩
  · exact ⟨i, Or.inr (by norm_num [hi])⟩

theorem cubeCoe_mem_ambientBoundary {t : N → I}
    (ht : t ∈ Cube.boundary N) :
    cubeCoe t ∈ ambientBoundary N := by
  obtain ⟨i, hi | hi⟩ := ht
  · exact ⟨i, Or.inl (by simp [cubeCoe, hi])⟩
  · exact ⟨i, Or.inr (by simp [cubeCoe, hi])⟩

theorem project_mem_collar {v : Ambient N}
    (hv : v ∈ ambientNeighborhood N) :
    project v ∈ CubeCollar.neighborhood N := by
  obtain ⟨i, hi | hi⟩ := hv
  · refine ⟨i, Or.inl ?_⟩
    rw [project, coe_projIcc]
    exact max_lt (by norm_num) ((min_le_right 1 (v i)).trans_lt hi)
  · refine ⟨i, Or.inr ?_⟩
    rw [project, coe_projIcc]
    exact (lt_min (by norm_num) hi).trans_le (le_max_right 0 (min 1 (v i)))

variable {x : UnitSphere (E := E)}

/-- Extend a collared generalized loop continuously to the ambient vector
space by coordinatewise projection to the cube. -/
def extended (p : GenLoop N (UnitSphere (E := E)) x)
    (v : Ambient N) : E :=
  (CubeCollar.collared p (project v) : UnitSphere (E := E))

theorem continuous_extended
    (p : GenLoop N (UnitSphere (E := E)) x) :
    Continuous (extended p) :=
  continuous_subtype_val.comp <|
    (CubeCollar.collared p).1.continuous.comp continuous_project

@[simp]
theorem extended_cubeCoe
    (p : GenLoop N (UnitSphere (E := E)) x) (t : N → I) :
    extended p (cubeCoe t) = (CubeCollar.collared p t : E) := by
  simp [extended]

theorem norm_extended
    (p : GenLoop N (UnitSphere (E := E)) x) (v : Ambient N) :
    ‖extended p v‖ = 1 :=
  norm_coe_unitSphere _

theorem extended_eq_basepoint_on_neighborhood
    (p : GenLoop N (UnitSphere (E := E)) x)
    {v : Ambient N} (hv : v ∈ ambientNeighborhood N) :
    extended p v = (x : E) := by
  exact congrArg Subtype.val <|
    CubeCollar.collared_eq_basepoint_on_neighborhood p
      (project_mem_collar hv)

variable [Fintype N] [NormedSpace ℝ E]

theorem contDiffOn_extended_neighborhood
    (p : GenLoop N (UnitSphere (E := E)) x) :
    ContDiffOn ℝ ∞ (extended p) (ambientNeighborhood N) := by
  have hconst :
      ContDiffOn ℝ ∞ (fun _ : Ambient N => (x : E))
        (ambientNeighborhood N) :=
    contDiff_const.contDiffOn
  exact hconst.congr fun v hv =>
    extended_eq_basepoint_on_neighborhood p hv

/-- A smooth ambient representative of the homotopy class of `p`. Its
normalization on the cube is recorded as `representative`. -/
structure Approximation (p : GenLoop N (UnitSphere (E := E)) x) where
  raw : Ambient N → E
  contDiff_raw : ContDiff ℝ ∞ raw
  raw_ne_zero : ∀ v, raw v ≠ 0
  representative : GenLoop N (UnitSphere (E := E)) x
  representative_apply : ∀ t,
    (representative t : E) =
      NormedSpace.normalize (raw (cubeCoe t))
  homotopic : GenLoop.Homotopic p representative

/-- Every cubical sphere loop has a homotopic representative obtained by
normalizing a globally smooth, everywhere nonzero ambient map. -/
theorem exists_approximation
    (p : GenLoop N (UnitSphere (E := E)) x) :
    Nonempty (Approximation p) := by
  obtain ⟨g, hg, hclose, heq, _⟩ :=
    (continuous_extended p).exists_contDiff_approx_and_eqOn ⊤
      (ε := fun _ => (1 / 2 : ℝ)) continuous_const (fun _ => by norm_num)
      (isClosed_ambientBoundary N)
      ((isOpen_ambientNeighborhood N).mem_nhdsSet.mpr
        (ambientBoundary_subset_neighborhood N))
      (contDiffOn_extended_neighborhood p)
  have hg_ne : ∀ v, g v ≠ 0 := by
    intro v hzero
    have h := hclose v
    rw [hzero, dist_zero_left, norm_extended] at h
    norm_num at h
  let fMap : C(N → I, UnitSphere (E := E)) :=
    (CubeCollar.collared p).1
  let gMap : C(N → I, E) :=
    ⟨fun t => g (cubeCoe t), hg.continuous.comp continuous_cubeCoe⟩
  have hfg : ∀ t, dist (fMap t : E) (gMap t) < 1 := by
    intro t
    calc
      dist (fMap t : E) (gMap t) =
          dist (g (cubeCoe t)) (extended p (cubeCoe t)) := by
        rw [dist_comm, extended_cubeCoe]
        rfl
      _ < 1 / 2 := hclose (cubeCoe t)
      _ < 1 := by norm_num
  have hrel : ∀ t ∈ Cube.boundary N, gMap t = (fMap t : E) := by
    intro t ht
    have h := heq (cubeCoe_mem_ambientBoundary ht)
    change g (cubeCoe t) = (CubeCollar.collared p t : E)
    simpa only [extended_cubeCoe] using h
  let H :=
    SphereRawHomotopy.normalizedRawHomotopyRel
      fMap gMap hfg (Cube.boundary N) hrel
  let qMap :=
    SphereRawHomotopy.normalizeMap gMap
      (SphereRawHomotopy.map_ne_zero_of_dist_lt_one fMap gMap hfg)
  let q : GenLoop N (UnitSphere (E := E)) x :=
    ⟨qMap, fun t ht => by
      rw [← H.fst_eq_snd ht]
      exact (CubeCollar.collared p).property t ht⟩
  refine ⟨{
    raw := g
    contDiff_raw := hg
    raw_ne_zero := hg_ne
    representative := q
    representative_apply := ?_
    homotopic :=
      (CubeCollar.homotopic_collared p).trans
        (show GenLoop.Homotopic (CubeCollar.collared p) q from ⟨H⟩)
  }⟩
  intro t
  rfl

/-- Every homotopy class admits one of the smooth representatives constructed
above. -/
theorem exists_approximation_of_homotopy_class
    (z : HomotopyGroup N (UnitSphere (E := E)) x) :
    ∃ p : GenLoop N (UnitSphere (E := E)) x,
      ∃ a : Approximation p, z = Quotient.mk' a.representative := by
  refine Quotient.inductionOn z ?_
  intro p
  obtain ⟨a⟩ := exists_approximation p
  exact ⟨p, a, Quotient.sound a.homotopic⟩

end Submission.SmoothSphereApprox
