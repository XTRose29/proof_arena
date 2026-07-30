import Submission.SphereRegularApprox

open scoped unitInterval

noncomputable section

namespace Submission.SphereBubble

open Submission.SphereRegularApprox

/-- The truncated Euclidean radius used by the standard compactly supported
sphere bubble. -/
def radius (m : ℕ) (v : Domain m) : ℝ :=
  min ‖v‖ 1

theorem radius_nonneg (m : ℕ) (v : Domain m) :
    0 ≤ radius m v :=
  le_min (norm_nonneg v) zero_le_one

theorem radius_le_one (m : ℕ) (v : Domain m) :
    radius m v ≤ 1 :=
  min_le_right _ _

theorem radius_eq_one_of_one_le_norm (m : ℕ) {v : Domain m}
    (hv : 1 ≤ ‖v‖) :
    radius m v = 1 :=
  min_eq_right hv

@[simp]
theorem radius_zero (m : ℕ) :
    radius m 0 = 0 := by
  simp [radius]

theorem continuous_radius (m : ℕ) :
    Continuous (radius m) :=
  continuous_norm.min continuous_const

/-- An ambient representative of the standard sphere bubble. It is the south
pole outside the closed unit ball and the north pole at the origin. -/
def raw (m : ℕ) (v : Domain m) : Target m :=
  WithLp.toLp 2 <|
    Fin.lastCases (1 - 2 * radius m v)
      fun i => (1 - radius m v) * v i

@[simp]
theorem raw_last (m : ℕ) (v : Domain m) :
    raw m v (Fin.last (m + 1)) = 1 - 2 * radius m v := by
  simp [raw]

@[simp]
theorem raw_castSucc (m : ℕ) (v : Domain m) (i : Fin (m + 1)) :
    raw m v i.castSucc = (1 - radius m v) * v i := by
  simp [raw]

theorem raw_ne_zero (m : ℕ) (v : Domain m) :
    raw m v ≠ 0 := by
  intro hzero
  have hlast := congrArg
    (fun w : Target m => w (Fin.last (m + 1))) hzero
  simp only [raw_last, PiLp.zero_apply] at hlast
  have hradius : radius m v = 1 / 2 := by
    linarith
  have hv : v = 0 := by
    ext i
    change v i = (0 : ℝ)
    have hi := congrArg (fun w : Target m => w i.castSucc) hzero
    simp only [raw_castSucc, PiLp.zero_apply, hradius] at hi
    change (1 - 1 / 2 : ℝ) * v i = 0 at hi
    norm_num at hi
    exact hi
  have hradiusZero : radius m v = 0 := by
    simp [radius, hv]
  linarith

theorem continuous_raw (m : ℕ) :
    Continuous (raw m) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (m + 2) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last =>
      simp only [Fin.lastCases_last]
      change Continuous ((fun _ => (1 : ℝ)) - (fun _ => (2 : ℝ)) * radius m)
      exact continuous_const.sub (continuous_const.mul (continuous_radius m))
  | cast j =>
      simp only [Fin.lastCases_castSucc]
      change Continuous (fun v : Domain m => (1 - radius m v) * v j)
      exact (continuous_const.sub (continuous_radius m)).mul <|
        (PiLp.continuous_apply (p := 2)
          (β := fun _ : Fin (m + 1) => ℝ) j)

/-- The standard compactly supported bubble as a unit-sphere-valued map. -/
def map (m : ℕ) (v : Domain m) : UnitSphere m :=
  ⟨NormedSpace.normalize (raw m v), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize (raw_ne_zero m v)⟩

theorem continuous_map (m : ℕ) :
    Continuous (map m) := by
  apply Continuous.subtype_mk
  change Continuous (fun v => ‖raw m v‖⁻¹ • raw m v)
  exact
    ((continuous_raw m).norm.inv₀ fun v =>
      norm_ne_zero_iff.mpr (raw_ne_zero m v)).smul
        (continuous_raw m)

theorem horizontal_raw (m : ℕ) (v : Domain m) :
    horizontal m (raw m v) = (1 - radius m v) • v := by
  ext i
  simp [horizontal, raw]

theorem horizontal_map (m : ℕ) (v : Domain m) :
    horizontal m (map m v : Target m) =
      ‖raw m v‖⁻¹ • ((1 - radius m v) • v) := by
  ext i
  simp [map, NormedSpace.normalize, horizontal, raw]

theorem norm_raw_pos (m : ℕ) (v : Domain m) :
    0 < ‖raw m v‖ :=
  norm_pos_iff.mpr (raw_ne_zero m v)

theorem raw_eq_canonicalBasepoint_of_one_le_norm
    (m : ℕ) {v : Domain m} (hv : 1 ≤ ‖v‖) :
    raw m v =
      (SphereGenerator.canonicalBasepoint m : Target m) := by
  rw [SphereRegularApprox.coe_canonicalBasepoint]
  have hradius := radius_eq_one_of_one_le_norm m hv
  ext i
  cases i using Fin.lastCases with
  | last =>
      norm_num [raw, hradius]
  | cast j =>
      simp [raw, hradius]

theorem map_eq_canonicalBasepoint_of_one_le_norm
    (m : ℕ) {v : Domain m} (hv : 1 ≤ ‖v‖) :
    map m v = SphereGenerator.canonicalBasepoint m := by
  apply Subtype.ext
  change
    NormedSpace.normalize (raw m v) =
      (SphereGenerator.canonicalBasepoint m : Target m)
  rw [raw_eq_canonicalBasepoint_of_one_le_norm m hv]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (SphereGenerator.sphere_norm_eq_one m
      (SphereGenerator.canonicalBasepoint m))

@[simp]
theorem map_zero (m : ℕ) :
    map m 0 = -(SphereGenerator.canonicalBasepoint m) := by
  apply Subtype.ext
  change
    NormedSpace.normalize (raw m 0) =
      -(SphereGenerator.canonicalBasepoint m : Target m)
  have hraw :
      raw m 0 =
        -(SphereGenerator.canonicalBasepoint m : Target m) := by
    rw [SphereRegularApprox.coe_canonicalBasepoint]
    ext i
    cases i using Fin.lastCases with
    | last =>
        simp [raw]
    | cast j =>
        simp [raw]
  rw [hraw]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (by
      rw [norm_neg]
      exact SphereGenerator.sphere_norm_eq_one m
        (SphereGenerator.canonicalBasepoint m))

theorem one_le_norm_centered_of_mem_boundary
    (m : ℕ) (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    1 ≤ ‖SphereGenerator.centered m t‖ := by
  obtain ⟨i, hi | hi⟩ := ht
  · calc
      1 = ‖SphereGenerator.centered m t i‖ := by
        norm_num [SphereGenerator.centered_apply, hi]
      _ ≤ ‖SphereGenerator.centered m t‖ :=
        PiLp.norm_apply_le _ _
  · calc
      1 = ‖SphereGenerator.centered m t i‖ := by
        norm_num [SphereGenerator.centered_apply, hi]
      _ ≤ ‖SphereGenerator.centered m t‖ :=
        PiLp.norm_apply_le _ _

/-- The standard bubble pulled back to the centered unit cube. -/
def cubicalMap (m : ℕ) (t : Fin (m + 1) → I) : UnitSphere m :=
  map m (SphereGenerator.centered m t)

theorem continuous_cubicalMap (m : ℕ) :
    Continuous (cubicalMap m) :=
  (continuous_map m).comp (SphereGenerator.continuous_centered m)

theorem cubicalMap_boundary
    (m : ℕ) (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    cubicalMap m t = SphereGenerator.canonicalBasepoint m :=
  map_eq_canonicalBasepoint_of_one_le_norm m
    (one_le_norm_centered_of_mem_boundary m t ht)

/-- The standard Euclidean radial bubble as a generalized cubical loop. -/
def cubicalGenLoop (m : ℕ) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨cubicalMap m, continuous_cubicalMap m⟩,
    cubicalMap_boundary m⟩

/-- The homotopy class of the Euclidean radial bubble. -/
def bubbleClass (m : ℕ) :
    HomotopyGroup.Pi (m + 1) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  Quotient.mk' (cubicalGenLoop m)

/-- Interpolate between the sup radius of the original cubical generator and
the truncated Euclidean radius of the radial bubble. -/
def interpolatedRadius (m : ℕ)
    (z : I × (Fin (m + 1) → I)) : ℝ :=
  (1 - (z.1 : ℝ)) * SphereGenerator.cubeRadius m z.2 +
    (z.1 : ℝ) * radius m (SphereGenerator.centered m z.2)

theorem interpolatedRadius_nonneg (m : ℕ)
    (z : I × (Fin (m + 1) → I)) :
    0 ≤ interpolatedRadius m z := by
  exact add_nonneg
    (mul_nonneg (sub_nonneg.mpr z.1.property.2)
      (SphereGenerator.cubeRadius_nonneg m z.2))
    (mul_nonneg z.1.property.1
      (radius_nonneg m (SphereGenerator.centered m z.2)))

theorem interpolatedRadius_le_one (m : ℕ)
    (z : I × (Fin (m + 1) → I)) :
    interpolatedRadius m z ≤ 1 := by
  calc
    interpolatedRadius m z ≤
        (1 - (z.1 : ℝ)) * 1 + (z.1 : ℝ) * 1 := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left
          (SphereGenerator.cubeRadius_le_one m z.2)
          (sub_nonneg.mpr z.1.property.2))
        (mul_le_mul_of_nonneg_left
          (radius_le_one m (SphereGenerator.centered m z.2))
          z.1.property.1)
    _ = 1 := by ring

theorem continuous_interpolatedRadius (m : ℕ) :
    Continuous (interpolatedRadius m) := by
  unfold interpolatedRadius
  exact
    ((continuous_const.sub
      (continuous_subtype_val.comp continuous_fst)).mul
        ((SphereGenerator.continuous_cubeRadius m).comp continuous_snd)).add
      ((continuous_subtype_val.comp continuous_fst).mul
        ((continuous_radius m).comp <|
          (SphereGenerator.continuous_centered m).comp continuous_snd))

@[simp]
theorem interpolatedRadius_zero (m : ℕ)
    (t : Fin (m + 1) → I) :
    interpolatedRadius m (0, t) =
      SphereGenerator.cubeRadius m t := by
  simp [interpolatedRadius]

@[simp]
theorem interpolatedRadius_one (m : ℕ)
    (t : Fin (m + 1) → I) :
    interpolatedRadius m (1, t) =
      radius m (SphereGenerator.centered m t) := by
  simp [interpolatedRadius]

theorem interpolatedRadius_boundary (m : ℕ) (s : I)
    (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    interpolatedRadius m (s, t) = 1 := by
  rw [interpolatedRadius,
    SphereGenerator.cubeRadius_eq_one_of_mem_boundary m t ht,
    radius_eq_one_of_one_le_norm m
      (one_le_norm_centered_of_mem_boundary m t ht)]
  ring

/-- The ambient vector used in the radial comparison homotopy. -/
def interpolatedRaw (m : ℕ)
    (z : I × (Fin (m + 1) → I)) : Target m :=
  WithLp.toLp 2 <|
    Fin.lastCases (1 - 2 * interpolatedRadius m z)
      fun i =>
        (1 - interpolatedRadius m z) *
          SphereGenerator.centered m z.2 i

@[simp]
theorem interpolatedRaw_last (m : ℕ)
    (z : I × (Fin (m + 1) → I)) :
    interpolatedRaw m z (Fin.last (m + 1)) =
      1 - 2 * interpolatedRadius m z := by
  simp [interpolatedRaw]

@[simp]
theorem interpolatedRaw_castSucc (m : ℕ)
    (z : I × (Fin (m + 1) → I)) (i : Fin (m + 1)) :
    interpolatedRaw m z i.castSucc =
      (1 - interpolatedRadius m z) *
        SphereGenerator.centered m z.2 i := by
  simp [interpolatedRaw]

theorem interpolatedRaw_ne_zero (m : ℕ)
    (z : I × (Fin (m + 1) → I)) :
    interpolatedRaw m z ≠ 0 := by
  intro hzero
  have hlast := congrArg
    (fun w : Target m => w (Fin.last (m + 1))) hzero
  simp only [interpolatedRaw_last, PiLp.zero_apply] at hlast
  have hradius : interpolatedRadius m z = 1 / 2 := by
    linarith
  have hcentered : SphereGenerator.centered m z.2 = 0 := by
    ext i
    change SphereGenerator.centered m z.2 i = (0 : ℝ)
    have hi := congrArg (fun w : Target m => w i.castSucc) hzero
    simp only [interpolatedRaw_castSucc, PiLp.zero_apply, hradius] at hi
    change
      (1 - 1 / 2 : ℝ) * SphereGenerator.centered m z.2 i = 0 at hi
    norm_num at hi
    exact hi
  have hcube : SphereGenerator.cubeRadius m z.2 = 0 := by
    unfold SphereGenerator.cubeRadius
    simp [hcentered]
  have hradial :
      radius m (SphereGenerator.centered m z.2) = 0 := by
    simp [hcentered, radius]
  have : interpolatedRadius m z = 0 := by
    simp [interpolatedRadius, hcube, hradial]
  linarith

theorem continuous_interpolatedRaw (m : ℕ) :
    Continuous (interpolatedRaw m) := by
  refine (PiLp.continuous_toLp 2 (fun _ : Fin (m + 2) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last =>
      simp only [Fin.lastCases_last]
      change Continuous
        ((fun _ => (1 : ℝ)) - (fun _ => (2 : ℝ)) * interpolatedRadius m)
      exact continuous_const.sub
        (continuous_const.mul (continuous_interpolatedRadius m))
  | cast j =>
      simp only [Fin.lastCases_castSucc]
      change Continuous
        (fun z : I × (Fin (m + 1) → I) =>
          (1 - interpolatedRadius m z) *
            SphereGenerator.centered m z.2 j)
      exact
        (continuous_const.sub (continuous_interpolatedRadius m)).mul <|
          (PiLp.continuous_apply (p := 2)
            (β := fun _ : Fin (m + 1) => ℝ) j).comp <|
              (SphereGenerator.continuous_centered m).comp continuous_snd

@[simp]
theorem interpolatedRaw_zero (m : ℕ)
    (t : Fin (m + 1) → I) :
    interpolatedRaw m (0, t) =
      SphereGenerator.rawGenerator m t := by
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [interpolatedRaw, SphereGenerator.rawGenerator]
  | cast j =>
      simp [interpolatedRaw, SphereGenerator.rawGenerator]

@[simp]
theorem interpolatedRaw_one (m : ℕ)
    (t : Fin (m + 1) → I) :
    interpolatedRaw m (1, t) =
      raw m (SphereGenerator.centered m t) := by
  ext i
  cases i using Fin.lastCases with
  | last =>
      simp [interpolatedRaw, raw]
  | cast j =>
      simp [interpolatedRaw, raw]

/-- The Euclidean radial bubble represents the same class as the original
sup-radial cubical generator. -/
def comparisonHomotopyRel (m : ℕ) :
    (SphereGenerator.canonicalGenLoop m).1.HomotopyRel
      (cubicalGenLoop m).1 (Cube.boundary (Fin (m + 1))) where
  toFun z :=
    ⟨NormedSpace.normalize (interpolatedRaw m z), by
      rw [Metric.mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize (interpolatedRaw_ne_zero m z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous
      (fun z => ‖interpolatedRaw m z‖⁻¹ • interpolatedRaw m z)
    exact
      ((continuous_interpolatedRaw m).norm.inv₀ fun z =>
        norm_ne_zero_iff.mpr (interpolatedRaw_ne_zero m z)).smul
          (continuous_interpolatedRaw m)
  map_zero_left t := by
    apply Subtype.ext
    change
      NormedSpace.normalize (interpolatedRaw m (0, t)) =
        NormedSpace.normalize (SphereGenerator.rawGenerator m t)
    rw [interpolatedRaw_zero]
  map_one_left t := by
    apply Subtype.ext
    change
      NormedSpace.normalize (interpolatedRaw m (1, t)) =
        NormedSpace.normalize
          (raw m (SphereGenerator.centered m t))
    rw [interpolatedRaw_one]
  prop' s t ht := by
    apply Subtype.ext
    change
      NormedSpace.normalize (interpolatedRaw m (s, t)) =
        (SphereGenerator.canonicalGenerator m t :
          Target m)
    have hradius : interpolatedRadius m (s, t) = 1 :=
      interpolatedRadius_boundary m s t ht
    have hraw :
        interpolatedRaw m (s, t) =
          (SphereGenerator.canonicalBasepoint m : Target m) := by
      rw [SphereRegularApprox.coe_canonicalBasepoint]
      ext i
      cases i using Fin.lastCases with
      | last =>
          norm_num [interpolatedRaw, hradius]
      | cast j =>
          simp [interpolatedRaw, hradius]
    rw [hraw]
    calc
      NormedSpace.normalize
          (SphereGenerator.canonicalBasepoint m : Target m) =
          (SphereGenerator.canonicalBasepoint m : Target m) :=
        NormedSpace.normalize_eq_self_of_norm_eq_one
          (SphereGenerator.sphere_norm_eq_one m
            (SphereGenerator.canonicalBasepoint m))
      _ = (SphereGenerator.canonicalGenerator m t : Target m) :=
        congrArg Subtype.val
          (SphereGenerator.canonicalGenerator_boundary m t ht).symm

theorem homotopic_cubicalGenLoop (m : ℕ) :
    GenLoop.Homotopic
      (SphereGenerator.canonicalGenLoop m) (cubicalGenLoop m) :=
  ⟨comparisonHomotopyRel m⟩

theorem class_eq_canonicalGeneratorClass (m : ℕ) :
    bubbleClass m = SphereGenerator.canonicalGeneratorClass m :=
  (Quotient.sound (homotopic_cubicalGenLoop m)).symm

/-- A center and radius whose open Euclidean support ball lies inside the
unit cube. -/
structure LocalDatum (m : ℕ) where
  center : Fin (m + 1) → I
  scale : ℝ
  scale_pos : 0 < scale
  scale_le_left : ∀ i, scale ≤ (center i : ℝ)
  scale_le_right : ∀ i, scale ≤ 1 - (center i : ℝ)

/-- The centered radius-one datum underlying `cubicalGenLoop`. -/
def standardDatum (m : ℕ) : LocalDatum m where
  center := fun _ => ⟨1 / 2, by constructor <;> norm_num⟩
  scale := 1 / 2
  scale_pos := by norm_num
  scale_le_left := by intro i; rfl
  scale_le_right := by intro i; norm_num

/-- Around every interior cubical point there is a valid local bubble datum
with arbitrarily small positive scale. -/
theorem exists_localDatum_centered_lt
    {m : ℕ} (t : Fin (m + 1) → I)
    (ht : ∀ i, 0 < (t i : ℝ) ∧ (t i : ℝ) < 1)
    {R : ℝ} (hR : 0 < R) :
    ∃ d : LocalDatum m, d.center = t ∧ d.scale < R := by
  let margin : Fin (m + 1) → ℝ :=
    fun i => min (t i : ℝ) (1 - (t i : ℝ))
  let μ : ℝ :=
    Finset.univ.inf' Finset.univ_nonempty margin
  have hμpos : 0 < μ := by
    dsimp only [μ]
    rw [Finset.lt_inf'_iff]
    intro i _
    exact lt_min (ht i).1 (sub_pos.mpr (ht i).2)
  let r : ℝ := min (R / 2) (μ / 2)
  have hrpos : 0 < r := by
    dsimp only [r]
    exact lt_min (half_pos hR) (half_pos hμpos)
  have hrR : r < R := by
    calc
      r ≤ R / 2 := min_le_left _ _
      _ < R := half_lt_self hR
  have hrμ : r ≤ μ := by
    calc
      r ≤ μ / 2 := min_le_right _ _
      _ ≤ μ := half_le_self hμpos.le
  let d : LocalDatum m := {
    center := t
    scale := r
    scale_pos := hrpos
    scale_le_left := fun i => by
      calc
        r ≤ μ := hrμ
        _ ≤ margin i :=
          Finset.inf'_le _ (Finset.mem_univ i)
        _ ≤ (t i : ℝ) := min_le_left _ _
    scale_le_right := fun i => by
      calc
        r ≤ μ := hrμ
        _ ≤ margin i :=
          Finset.inf'_le _ (Finset.mem_univ i)
        _ ≤ 1 - (t i : ℝ) := min_le_right _ _
  }
  exact ⟨d, rfl, hrR⟩

/-- Rescale cubical coordinates around an interior center. -/
def localCoordinates {m : ℕ} (d : LocalDatum m)
    (t : Fin (m + 1) → I) : Domain m :=
  d.scale⁻¹ • (cubeDomain m t - cubeDomain m d.center)

@[simp]
theorem localCoordinates_apply {m : ℕ} (d : LocalDatum m)
    (t : Fin (m + 1) → I) (i : Fin (m + 1)) :
    localCoordinates d t i =
      d.scale⁻¹ * ((t i : ℝ) - (d.center i : ℝ)) := by
  rfl

theorem continuous_localCoordinates {m : ℕ} (d : LocalDatum m) :
    Continuous (localCoordinates d) := by
  unfold localCoordinates
  fun_prop

theorem scale_smul_localCoordinates {m : ℕ} (d : LocalDatum m)
    (t : Fin (m + 1) → I) :
    d.scale • localCoordinates d t =
      cubeDomain m t - cubeDomain m d.center := by
  rw [localCoordinates, smul_smul]
  field_simp [d.scale_pos.ne']
  simp

theorem norm_cubeDomain_sub_center {m : ℕ} (d : LocalDatum m)
    (t : Fin (m + 1) → I) :
    ‖cubeDomain m t - cubeDomain m d.center‖ =
      d.scale * ‖localCoordinates d t‖ := by
  rw [← scale_smul_localCoordinates d t, norm_smul,
    Real.norm_eq_abs, abs_of_pos d.scale_pos]

theorem one_le_norm_localCoordinates_of_mem_boundary
    {m : ℕ} (d : LocalDatum m)
    (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    1 ≤ ‖localCoordinates d t‖ := by
  obtain ⟨i, hi | hi⟩ := ht
  · have hcoord :
        ‖localCoordinates d t i‖ =
          (d.center i : ℝ) / d.scale := by
      rw [localCoordinates_apply, hi]
      simp only [Set.Icc.coe_zero, zero_sub, Real.norm_eq_abs,
        abs_mul, abs_neg, abs_inv, abs_of_pos d.scale_pos,
        abs_of_nonneg (d.center i).property.1]
      ring
    calc
      1 ≤ ‖localCoordinates d t i‖ := by
        rw [hcoord]
        exact (le_div_iff₀ d.scale_pos).2 (by
          simpa using d.scale_le_left i)
      _ ≤ ‖localCoordinates d t‖ :=
        PiLp.norm_apply_le _ _
  · have hcoord :
        ‖localCoordinates d t i‖ =
          (1 - (d.center i : ℝ)) / d.scale := by
      rw [localCoordinates_apply, hi]
      simp only [Set.Icc.coe_one, Real.norm_eq_abs, abs_mul,
        abs_inv, abs_of_pos d.scale_pos,
        abs_of_nonneg (sub_nonneg.mpr (d.center i).property.2)]
      ring
    calc
      1 ≤ ‖localCoordinates d t i‖ := by
        rw [hcoord]
        exact (le_div_iff₀ d.scale_pos).2 (by
          simpa using d.scale_le_right i)
      _ ≤ ‖localCoordinates d t‖ :=
        PiLp.norm_apply_le _ _

/-- A translated and rescaled standard bubble supported in the cube. -/
def localCubicalMap {m : ℕ} (d : LocalDatum m)
    (t : Fin (m + 1) → I) : UnitSphere m :=
  map m (localCoordinates d t)

theorem continuous_localCubicalMap {m : ℕ} (d : LocalDatum m) :
    Continuous (localCubicalMap d) :=
  (continuous_map m).comp (continuous_localCoordinates d)

theorem localCubicalMap_boundary {m : ℕ} (d : LocalDatum m)
    (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    localCubicalMap d t = SphereGenerator.canonicalBasepoint m :=
  map_eq_canonicalBasepoint_of_one_le_norm m
    (one_le_norm_localCoordinates_of_mem_boundary d t ht)

/-- The local bubble associated to a valid center and scale. -/
def localGenLoop {m : ℕ} (d : LocalDatum m) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨localCubicalMap d, continuous_localCubicalMap d⟩,
    localCubicalMap_boundary d⟩

theorem localCoordinates_standardDatum (m : ℕ)
    (t : Fin (m + 1) → I) :
    localCoordinates (standardDatum m) t =
      SphereGenerator.centered m t := by
  ext i
  norm_num [localCoordinates_apply, standardDatum,
    SphereGenerator.centered_apply]
  ring

theorem localGenLoop_standardDatum (m : ℕ) :
    localGenLoop (standardDatum m) = cubicalGenLoop m := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  exact congrArg (map m) (localCoordinates_standardDatum m t)

/-- Convex interpolation preserves the validity inequalities for local
bubble data. -/
def interpolateDatum {m : ℕ} (d e : LocalDatum m) (s : I) :
    LocalDatum m where
  center i :=
    ⟨(1 - (s : ℝ)) * (d.center i : ℝ) +
        (s : ℝ) * (e.center i : ℝ), by
      constructor
      · exact add_nonneg
          (mul_nonneg (sub_nonneg.mpr s.property.2)
            (d.center i).property.1)
          (mul_nonneg s.property.1 (e.center i).property.1)
      · calc
          (1 - (s : ℝ)) * (d.center i : ℝ) +
                (s : ℝ) * (e.center i : ℝ) ≤
              (1 - (s : ℝ)) * 1 + (s : ℝ) * 1 :=
            add_le_add
              (mul_le_mul_of_nonneg_left
                (d.center i).property.2
                (sub_nonneg.mpr s.property.2))
              (mul_le_mul_of_nonneg_left
                (e.center i).property.2 s.property.1)
          _ = 1 := by ring⟩
  scale := (1 - (s : ℝ)) * d.scale + (s : ℝ) * e.scale
  scale_pos := by
    by_cases hs : (s : ℝ) = 1
    · simp [hs, e.scale_pos]
    · have hslt : (s : ℝ) < 1 :=
        lt_of_le_of_ne s.property.2 hs
      exact add_pos_of_pos_of_nonneg
        (mul_pos (sub_pos.mpr hslt) d.scale_pos)
        (mul_nonneg s.property.1 e.scale_pos.le)
  scale_le_left i := by
    dsimp
    nlinarith [mul_le_mul_of_nonneg_left (d.scale_le_left i)
        (sub_nonneg.mpr s.property.2),
      mul_le_mul_of_nonneg_left (e.scale_le_left i) s.property.1]
  scale_le_right i := by
    dsimp
    nlinarith [mul_le_mul_of_nonneg_left (d.scale_le_right i)
        (sub_nonneg.mpr s.property.2),
      mul_le_mul_of_nonneg_left (e.scale_le_right i) s.property.1]

@[simp]
theorem interpolateDatum_zero {m : ℕ} (d e : LocalDatum m) :
    interpolateDatum d e 0 = d := by
  cases d
  simp [interpolateDatum]

@[simp]
theorem interpolateDatum_one {m : ℕ} (d e : LocalDatum m) :
    interpolateDatum d e 1 = e := by
  cases e
  simp [interpolateDatum]

theorem continuous_interpolatedLocalCoordinates {m : ℕ}
    (d e : LocalDatum m) :
    Continuous
      (fun z : I × (Fin (m + 1) → I) =>
        localCoordinates (interpolateDatum d e z.1) z.2) := by
  refine (PiLp.continuous_toLp 2
    (fun _ : Fin (m + 1) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  change Continuous
    (fun z : I × (Fin (m + 1) → I) =>
      ((1 - (z.1 : ℝ)) * d.scale + (z.1 : ℝ) * e.scale)⁻¹ *
        ((z.2 i : ℝ) -
          ((1 - (z.1 : ℝ)) * (d.center i : ℝ) +
            (z.1 : ℝ) * (e.center i : ℝ))))
  apply Continuous.mul
  · apply Continuous.inv₀
    · fun_prop
    · intro z
      exact (interpolateDatum d e z.1).scale_pos.ne'
  · fun_prop

/-- Moving the center and scale through valid data gives a boundary-relative
homotopy of local bubbles. -/
def localComparisonHomotopyRel {m : ℕ} (d e : LocalDatum m) :
    (localGenLoop d).1.HomotopyRel
      (localGenLoop e).1 (Cube.boundary (Fin (m + 1))) where
  toFun z :=
    map m (localCoordinates (interpolateDatum d e z.1) z.2)
  continuous_toFun :=
    (continuous_map m).comp
      (continuous_interpolatedLocalCoordinates d e)
  map_zero_left t := by
    change
      map m (localCoordinates (interpolateDatum d e 0) t) =
        map m (localCoordinates d t)
    rw [interpolateDatum_zero]
  map_one_left t := by
    change
      map m (localCoordinates (interpolateDatum d e 1) t) =
        map m (localCoordinates e t)
    rw [interpolateDatum_one]
  prop' s t ht := by
    calc
      map m (localCoordinates (interpolateDatum d e s) t) =
          SphereGenerator.canonicalBasepoint m :=
        map_eq_canonicalBasepoint_of_one_le_norm m
          (one_le_norm_localCoordinates_of_mem_boundary
            (interpolateDatum d e s) t ht)
      _ = localGenLoop d t :=
        (localCubicalMap_boundary d t ht).symm

theorem localGenLoop_homotopic {m : ℕ} (d e : LocalDatum m) :
    GenLoop.Homotopic (localGenLoop d) (localGenLoop e) :=
  ⟨localComparisonHomotopyRel d e⟩

theorem localGenLoop_homotopic_canonical {m : ℕ} (d : LocalDatum m) :
    GenLoop.Homotopic (localGenLoop d)
      (SphereGenerator.canonicalGenLoop m) :=
  (localGenLoop_homotopic d (standardDatum m)).trans
    (by
      rw [localGenLoop_standardDatum]
      exact (homotopic_cubicalGenLoop m).symm)

theorem localGenLoop_class_eq_canonical {m : ℕ} (d : LocalDatum m) :
    (Quotient.mk' (localGenLoop d) :
      HomotopyGroup.Pi (m + 1) (UnitSphere m)
        (SphereGenerator.canonicalBasepoint m)) =
      SphereGenerator.canonicalGeneratorClass m :=
  Quotient.sound (localGenLoop_homotopic_canonical d)

/-- Reflection in the first coordinate of the bubble domain. -/
def firstReflection (m : ℕ) (v : Domain m) : Domain m :=
  WithLp.toLp 2 fun i => if i = 0 then -v i else v i

@[simp]
theorem firstReflection_apply_zero (m : ℕ) (v : Domain m) :
    firstReflection m v 0 = -v 0 := by
  simp [firstReflection]

theorem firstReflection_apply_of_ne {m : ℕ} (v : Domain m)
    {i : Fin (m + 1)} (hi : i ≠ 0) :
    firstReflection m v i = v i := by
  simp [firstReflection, hi]

theorem continuous_firstReflection (m : ℕ) :
    Continuous (firstReflection m) := by
  refine (PiLp.continuous_toLp 2
    (fun _ : Fin (m + 1) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  by_cases hi : i = 0
  · simp [hi]
    fun_prop
  · simp [hi]
    fun_prop

theorem norm_firstReflection (m : ℕ) (v : Domain m) :
    ‖firstReflection m v‖ = ‖v‖ := by
  have hsquare :
      ‖firstReflection m v‖ ^ 2 = ‖v‖ ^ 2 := by
    rw [EuclideanSpace.real_norm_sq_eq,
      EuclideanSpace.real_norm_sq_eq]
    apply Finset.sum_congr rfl
    intro i _
    by_cases hi : i = 0
    · subst i
      simp
    · rw [firstReflection_apply_of_ne v hi]
  nlinarith [norm_nonneg (firstReflection m v), norm_nonneg v]

/-- A local bubble with negative orientation. -/
def reflectedLocalCubicalMap {m : ℕ} (d : LocalDatum m)
    (t : Fin (m + 1) → I) : UnitSphere m :=
  map m (firstReflection m (localCoordinates d t))

theorem continuous_reflectedLocalCubicalMap {m : ℕ}
    (d : LocalDatum m) :
    Continuous (reflectedLocalCubicalMap d) :=
  (continuous_map m).comp <|
    (continuous_firstReflection m).comp
      (continuous_localCoordinates d)

theorem reflectedLocalCubicalMap_boundary {m : ℕ}
    (d : LocalDatum m) (t : Fin (m + 1) → I)
    (ht : t ∈ Cube.boundary (Fin (m + 1))) :
    reflectedLocalCubicalMap d t =
      SphereGenerator.canonicalBasepoint m := by
  apply map_eq_canonicalBasepoint_of_one_le_norm
  rw [norm_firstReflection]
  exact one_le_norm_localCoordinates_of_mem_boundary d t ht

/-- The negative local bubble associated to a valid center and scale. -/
def reflectedLocalGenLoop {m : ℕ} (d : LocalDatum m) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨reflectedLocalCubicalMap d,
      continuous_reflectedLocalCubicalMap d⟩,
    reflectedLocalCubicalMap_boundary d⟩

/-- Moving valid data also preserves the class of a reflected local bubble. -/
def reflectedLocalComparisonHomotopyRel {m : ℕ}
    (d e : LocalDatum m) :
    (reflectedLocalGenLoop d).1.HomotopyRel
      (reflectedLocalGenLoop e).1
      (Cube.boundary (Fin (m + 1))) where
  toFun z :=
    map m <| firstReflection m <|
      localCoordinates (interpolateDatum d e z.1) z.2
  continuous_toFun :=
    (continuous_map m).comp <|
      (continuous_firstReflection m).comp
        (continuous_interpolatedLocalCoordinates d e)
  map_zero_left t := by
    change
      map m
          (firstReflection m
            (localCoordinates (interpolateDatum d e 0) t)) =
        map m (firstReflection m (localCoordinates d t))
    rw [interpolateDatum_zero]
  map_one_left t := by
    change
      map m
          (firstReflection m
            (localCoordinates (interpolateDatum d e 1) t)) =
        map m (firstReflection m (localCoordinates e t))
    rw [interpolateDatum_one]
  prop' s t ht := by
    calc
      map m
          (firstReflection m
            (localCoordinates (interpolateDatum d e s) t)) =
          SphereGenerator.canonicalBasepoint m := by
        apply map_eq_canonicalBasepoint_of_one_le_norm
        rw [norm_firstReflection]
        exact one_le_norm_localCoordinates_of_mem_boundary
          (interpolateDatum d e s) t ht
      _ = reflectedLocalGenLoop d t :=
        (reflectedLocalCubicalMap_boundary d t ht).symm

theorem reflectedLocalGenLoop_homotopic {m : ℕ}
    (d e : LocalDatum m) :
    GenLoop.Homotopic
      (reflectedLocalGenLoop d) (reflectedLocalGenLoop e) :=
  ⟨reflectedLocalComparisonHomotopyRel d e⟩

theorem reflectedLocalGenLoop_standardDatum (m : ℕ) :
    reflectedLocalGenLoop (standardDatum m) =
      GenLoop.symmAt (0 : Fin (m + 1)) (cubicalGenLoop m) := by
  apply Subtype.ext
  apply ContinuousMap.ext
  intro t
  simp only [GenLoop.symmAt]
  apply congrArg (map m)
  ext i
  by_cases hi : i = 0
  · subst i
    rw [firstReflection_apply_zero,
      localCoordinates_standardDatum]
    simp only [SphereGenerator.centered_apply]
    simp only [if_pos, unitInterval.coe_symm_eq]
    ring
  · rw [firstReflection_apply_of_ne _ hi,
      localCoordinates_standardDatum]
    simp [SphereGenerator.centered_apply, hi]

theorem reflectedLocalGenLoop_class_eq_inverse {m : ℕ}
    (d : LocalDatum m) :
    (Quotient.mk' (reflectedLocalGenLoop d) :
      HomotopyGroup.Pi (m + 1) (UnitSphere m)
        (SphereGenerator.canonicalBasepoint m)) =
      (SphereGenerator.canonicalGeneratorClass m)⁻¹ := by
  letI : Nonempty (Fin (m + 1)) := ⟨0⟩
  letI : Group
      (HomotopyGroup.Pi (m + 1) (UnitSphere m)
        (SphereGenerator.canonicalBasepoint m)) :=
    HomotopyGroup.group (Fin (m + 1))
  calc
    Quotient.mk' (reflectedLocalGenLoop d) =
        Quotient.mk' (reflectedLocalGenLoop (standardDatum m)) :=
      Quotient.sound
        (reflectedLocalGenLoop_homotopic d (standardDatum m))
    _ = Quotient.mk'
          (GenLoop.symmAt (0 : Fin (m + 1))
            (cubicalGenLoop m)) := by
      rw [reflectedLocalGenLoop_standardDatum]
    _ = (bubbleClass m)⁻¹ := by
      unfold bubbleClass
      exact
      (HomotopyGroup.inv_spec
        (N := Fin (m + 1))
        (X := UnitSphere m)
        (x := SphereGenerator.canonicalBasepoint m)
        (p := cubicalGenLoop m)
        (i := (0 : Fin (m + 1)))).symm
    _ = (SphereGenerator.canonicalGeneratorClass m)⁻¹ := by
      rw [class_eq_canonicalGeneratorClass]

end Submission.SphereBubble
