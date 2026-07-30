import Submission.SphereBubble

open scoped unitInterval

noncomputable section

namespace Submission.SphereCap

open Submission.SphereRegularApprox

/-- A cutoff strictly between the two poles. -/
structure Datum where
  cutoff : ℝ
  neg_one_lt : -1 < cutoff
  lt_one : cutoff < 1

namespace Datum

theorem denominator_pos (d : Datum) :
    0 < 1 - d.cutoff :=
  sub_pos.mpr d.lt_one

end Datum

theorem vertical_le_one {m : ℕ} (y : UnitSphere m) :
    vertical m y ≤ 1 := by
  have hv := PiLp.norm_apply_le
    (y : Target m) (Fin.last (m + 1))
  rw [SphereGenerator.sphere_norm_eq_one m y,
    Real.norm_eq_abs] at hv
  exact (le_abs_self (vertical m y)).trans hv

theorem eq_antipode_of_vertical_eq_one {m : ℕ}
    (y : UnitSphere m) (hy : vertical m y = 1) :
    y = -(SphereGenerator.canonicalBasepoint m) := by
  have hdecomp := norm_sq_horizontal_add_vertical m (y : Target m)
  rw [SphereGenerator.sphere_norm_eq_one m y, hy] at hdecomp
  have hhorizontalNorm : ‖horizontal m y‖ = 0 := by
    nlinarith [norm_nonneg (horizontal m y)]
  have hhorizontal : horizontal m y = 0 :=
    norm_eq_zero.mp hhorizontalNorm
  apply Subtype.ext
  change
    (y : Target m) =
      -(SphereGenerator.canonicalBasepoint m : Target m)
  rw [SphereRegularApprox.coe_canonicalBasepoint]
  ext i
  cases i using Fin.lastCases with
  | last =>
      simpa [vertical] using hy
  | cast j =>
      have hj := congrArg (fun v : Domain m => v j) hhorizontal
      simpa [horizontal] using hj

theorem vertical_eq_one_iff {m : ℕ} (y : UnitSphere m) :
    vertical m y = 1 ↔
      y = -(SphereGenerator.canonicalBasepoint m) := by
  constructor
  · exact eq_antipode_of_vertical_eq_one y
  · rintro rfl
    simp [vertical, SphereRegularApprox.coe_canonicalBasepoint]

/-- A truncated radial coordinate which is zero at the north pole and one
below the prescribed spherical cap. -/
def radius {m : ℕ} (d : Datum) (y : UnitSphere m) : ℝ :=
  min ((1 - vertical m y) / (1 - d.cutoff)) 1

theorem radius_nonneg {m : ℕ} (d : Datum) (y : UnitSphere m) :
    0 ≤ radius d y := by
  exact le_min
    (div_nonneg (sub_nonneg.mpr (vertical_le_one y))
      d.denominator_pos.le)
    zero_le_one

theorem radius_le_one {m : ℕ} (d : Datum) (y : UnitSphere m) :
    radius d y ≤ 1 :=
  min_le_right _ _

theorem continuous_radius {m : ℕ} (d : Datum) :
    Continuous (radius (m := m) d) := by
  unfold radius
  fun_prop

/-- The ambient cap-collapse vector. -/
def raw {m : ℕ} (d : Datum) (y : UnitSphere m) : Target m :=
  WithLp.toLp 2 <|
    Fin.lastCases (1 - 2 * radius d y)
      fun i => (1 - radius d y) * horizontal m y i

@[simp]
theorem raw_last {m : ℕ} (d : Datum) (y : UnitSphere m) :
    raw d y (Fin.last (m + 1)) = 1 - 2 * radius d y := by
  simp [raw]

@[simp]
theorem raw_castSucc {m : ℕ} (d : Datum) (y : UnitSphere m)
    (i : Fin (m + 1)) :
    raw d y i.castSucc =
      (1 - radius d y) * horizontal m y i := by
  simp [raw]

theorem continuous_raw {m : ℕ} (d : Datum) :
    Continuous (raw (m := m) d) := by
  refine (PiLp.continuous_toLp 2
    (fun _ : Fin (m + 2) => ℝ)).comp ?_
  apply continuous_pi
  intro i
  cases i using Fin.lastCases with
  | last =>
      simp only [Fin.lastCases_last]
      change Continuous
        ((fun _ => (1 : ℝ)) - (fun _ => (2 : ℝ)) * radius d)
      exact continuous_const.sub
        (continuous_const.mul (continuous_radius d))
  | cast j =>
      simp only [Fin.lastCases_castSucc]
      change Continuous
        (fun y : UnitSphere m =>
          (1 - radius d y) * horizontal m y j)
      exact
        (continuous_const.sub (continuous_radius d)).mul <|
          (PiLp.continuous_apply (p := 2)
            (β := fun _ : Fin (m + 1) => ℝ) j).comp <|
              (contDiff_horizontal m).continuous.comp
                continuous_subtype_val

theorem radius_eq_zero_of_vertical_eq_one {m : ℕ}
    (d : Datum) {y : UnitSphere m}
    (hy : vertical m y = 1) :
    radius d y = 0 := by
  change min ((1 - vertical m y) / (1 - d.cutoff)) 1 = 0
  rw [hy]
  norm_num

theorem radius_eq_one_of_vertical_eq_neg_one {m : ℕ}
    (d : Datum) {y : UnitSphere m}
    (hy : vertical m y = -1) :
    radius d y = 1 := by
  rw [radius, hy]
  apply min_eq_right
  apply (le_div_iff₀ d.denominator_pos).2
  nlinarith [d.neg_one_lt]

theorem raw_eq_self_of_horizontal_eq_zero {m : ℕ}
    (d : Datum) (y : UnitSphere m)
    (hy : horizontal m y = 0) :
    raw d y = (y : Target m) := by
  have hdecomp := norm_sq_horizontal_add_vertical m (y : Target m)
  rw [SphereGenerator.sphere_norm_eq_one m y, hy, norm_zero] at hdecomp
  have hsq : vertical m y ^ 2 = 1 := by
    norm_num at hdecomp
    exact hdecomp.symm
  rcases sq_eq_one_iff.mp hsq with hk | hk
  · have hradius : radius d y = 0 :=
      radius_eq_zero_of_vertical_eq_one d hk
    ext i
    cases i using Fin.lastCases with
    | last =>
        change raw d y (Fin.last (m + 1)) = vertical m y
        calc
          raw d y (Fin.last (m + 1)) = 1 - 2 * radius d y :=
            raw_last d y
          _ = 1 := by rw [hradius]; norm_num
          _ = vertical m y := hk.symm
    | cast j =>
        rw [raw_castSucc, hradius]
        norm_num
  · have hradius : radius d y = 1 :=
      radius_eq_one_of_vertical_eq_neg_one d hk
    ext i
    cases i using Fin.lastCases with
    | last =>
        change raw d y (Fin.last (m + 1)) = vertical m y
        calc
          raw d y (Fin.last (m + 1)) = 1 - 2 * radius d y :=
            raw_last d y
          _ = -1 := by rw [hradius]; norm_num
          _ = vertical m y := hk.symm
    | cast j =>
        have hj := congrArg (fun v : Domain m => v j) hy
        rw [raw_castSucc, hradius]
        norm_num
        exact hj.symm

theorem raw_ne_zero {m : ℕ} (d : Datum) (y : UnitSphere m) :
    raw d y ≠ 0 := by
  intro hzero
  have hlast := congrArg
    (fun w : Target m => w (Fin.last (m + 1))) hzero
  simp only [raw_last, PiLp.zero_apply] at hlast
  have hradius : radius d y = 1 / 2 := by
    linarith
  have hhorizontal : horizontal m y = 0 := by
    ext i
    change horizontal m y i = (0 : ℝ)
    have hi := congrArg (fun w : Target m => w i.castSucc) hzero
    simp only [raw_castSucc, PiLp.zero_apply, hradius] at hi
    change (1 - 1 / 2 : ℝ) * horizontal m y i = 0 at hi
    norm_num at hi
    exact hi
  have hself := raw_eq_self_of_horizontal_eq_zero d y hhorizontal
  rw [hself] at hzero
  have hnorm := SphereGenerator.sphere_norm_eq_one m y
  rw [hzero, norm_zero] at hnorm
  norm_num at hnorm

/-- Collapse the complement of an upper spherical cap to the south pole. -/
def map {m : ℕ} (d : Datum) (y : UnitSphere m) : UnitSphere m :=
  ⟨NormedSpace.normalize (raw d y), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize (raw_ne_zero d y)⟩

theorem continuous_map {m : ℕ} (d : Datum) :
    Continuous (map (m := m) d) := by
  apply Continuous.subtype_mk
  change Continuous (fun y => ‖raw d y‖⁻¹ • raw d y)
  exact
    ((continuous_raw d).norm.inv₀ fun y =>
      norm_ne_zero_iff.mpr (raw_ne_zero d y)).smul
        (continuous_raw d)

theorem radius_eq_one_of_vertical_le_cutoff {m : ℕ}
    (d : Datum) {y : UnitSphere m}
    (hy : vertical m y ≤ d.cutoff) :
    radius d y = 1 := by
  unfold radius
  apply min_eq_right
  apply (le_div_iff₀ d.denominator_pos).2
  linarith

theorem map_eq_basepoint_of_vertical_le_cutoff {m : ℕ}
    (d : Datum) {y : UnitSphere m}
    (hy : vertical m y ≤ d.cutoff) :
    map d y = SphereGenerator.canonicalBasepoint m := by
  have hradius := radius_eq_one_of_vertical_le_cutoff d hy
  apply Subtype.ext
  change
    NormedSpace.normalize (raw d y) =
      (SphereGenerator.canonicalBasepoint m : Target m)
  have hraw :
      raw d y =
        (SphereGenerator.canonicalBasepoint m : Target m) := by
    rw [SphereRegularApprox.coe_canonicalBasepoint]
    ext i
    cases i using Fin.lastCases with
    | last =>
        norm_num [raw, hradius]
    | cast j =>
        simp [raw, hradius]
  rw [hraw]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (SphereGenerator.sphere_norm_eq_one m
      (SphereGenerator.canonicalBasepoint m))

@[simp]
theorem map_basepoint {m : ℕ} (d : Datum) :
    map d (SphereGenerator.canonicalBasepoint m) =
      SphereGenerator.canonicalBasepoint m := by
  apply map_eq_basepoint_of_vertical_le_cutoff
  rw [vertical_canonicalBasepoint]
  exact d.neg_one_lt.le

/-- The affine deformation from the identity to the cap-collapse vector. -/
def deformationRaw {m : ℕ} (d : Datum)
    (z : I × UnitSphere m) : Target m :=
  (1 - (z.1 : ℝ)) • (z.2 : Target m) +
    (z.1 : ℝ) • raw d z.2

theorem continuous_deformationRaw {m : ℕ} (d : Datum) :
    Continuous (deformationRaw (m := m) d) := by
  unfold deformationRaw
  exact
    (continuous_const.sub
      (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_subtype_val.comp continuous_snd) |>.add <|
      (continuous_subtype_val.comp continuous_fst).smul
        ((continuous_raw d).comp continuous_snd)

theorem deformationRaw_ne_zero {m : ℕ} (d : Datum)
    (z : I × UnitSphere m) :
    deformationRaw d z ≠ 0 := by
  by_cases hs : (z.1 : ℝ) = 1
  · simpa [deformationRaw, hs] using raw_ne_zero d z.2
  · have hslt : (z.1 : ℝ) < 1 :=
      lt_of_le_of_ne z.1.property.2 hs
    have hcoeff :
        0 <
          (1 - (z.1 : ℝ)) +
            (z.1 : ℝ) * (1 - radius d z.2) := by
      exact add_pos_of_pos_of_nonneg
        (sub_pos.mpr hslt)
        (mul_nonneg z.1.property.1
          (sub_nonneg.mpr (radius_le_one d z.2)))
    intro hzero
    have hhorizontal : horizontal m z.2 = 0 := by
      ext i
      have hi := congrArg
        (fun w : Target m => w i.castSucc) hzero
      have hi' :
          (1 - (z.1 : ℝ)) * horizontal m z.2 i +
              (z.1 : ℝ) *
                ((1 - radius d z.2) * horizontal m z.2 i) =
            0 := by
        simpa [deformationRaw] using hi
      have :
          ((1 - (z.1 : ℝ)) +
              (z.1 : ℝ) * (1 - radius d z.2)) *
              horizontal m z.2 i =
            0 := by
        linarith [hi']
      exact (mul_eq_zero.mp this).resolve_left hcoeff.ne'
    have hself :=
      raw_eq_self_of_horizontal_eq_zero d z.2 hhorizontal
    have hdeform :
        deformationRaw d z = (z.2 : Target m) := by
      rw [deformationRaw, hself]
      module
    rw [hdeform] at hzero
    have hnorm := SphereGenerator.sphere_norm_eq_one m z.2
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm

/-- The cap collapse is homotopic to the identity, fixing the south pole. -/
def homotopyRel {m : ℕ} (d : Datum) :
    (ContinuousMap.id (UnitSphere m)).HomotopyRel
      ⟨map d, continuous_map d⟩
      {SphereGenerator.canonicalBasepoint m} where
  toFun z :=
    ⟨NormedSpace.normalize (deformationRaw d z), by
      rw [Metric.mem_sphere, dist_zero_right]
      exact NormedSpace.norm_normalize
        (deformationRaw_ne_zero d z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    change Continuous
      (fun z => ‖deformationRaw d z‖⁻¹ • deformationRaw d z)
    exact
      ((continuous_deformationRaw d).norm.inv₀ fun z =>
        norm_ne_zero_iff.mpr (deformationRaw_ne_zero d z)).smul
          (continuous_deformationRaw d)
  map_zero_left y := by
    apply Subtype.ext
    change
      NormedSpace.normalize (deformationRaw d (0, y)) =
        (y : Target m)
    rw [show deformationRaw d (0, y) = (y : Target m) by
      simp [deformationRaw]]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (SphereGenerator.sphere_norm_eq_one m y)
  map_one_left y := by
    apply Subtype.ext
    change
      NormedSpace.normalize (deformationRaw d (1, y)) =
        NormedSpace.normalize (raw d y)
    rw [show deformationRaw d (1, y) = raw d y by
      simp [deformationRaw]]
  prop' s y hy := by
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Subtype.ext
    change
      NormedSpace.normalize
          (deformationRaw d
            (s, SphereGenerator.canonicalBasepoint m)) =
        (SphereGenerator.canonicalBasepoint m : Target m)
    have hraw :
        raw d (SphereGenerator.canonicalBasepoint m) =
          (SphereGenerator.canonicalBasepoint m : Target m) := by
      have hhorizontal :
          horizontal m
              (SphereGenerator.canonicalBasepoint m : Target m) =
            0 :=
        horizontal_canonicalBasepoint m
      exact raw_eq_self_of_horizontal_eq_zero d _ hhorizontal
    rw [show deformationRaw d
        (s, SphereGenerator.canonicalBasepoint m) =
          (SphereGenerator.canonicalBasepoint m : Target m) by
      rw [deformationRaw, hraw]
      module]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (SphereGenerator.sphere_norm_eq_one m
        (SphereGenerator.canonicalBasepoint m))

/-- Postcompose a generalized loop by cap collapse. -/
def genLoop {m : ℕ} (d : Datum)
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨fun t => map d (q t),
      (continuous_map d).comp q.1.continuous⟩,
    fun t ht =>
      (congrArg (map d) (q.property t ht)).trans (map_basepoint d)⟩

theorem genLoop_homotopic {m : ℕ} (d : Datum)
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    GenLoop.Homotopic q (genLoop d q) := by
  refine ⟨{
    toHomotopy := (homotopyRel d).toHomotopy.compContinuousMap q.1
    prop' := ?_
  }⟩
  intro s t ht
  change
    (homotopyRel d) (s, q t) = q t
  exact (homotopyRel d).prop' s _
    (Set.mem_singleton_iff.mpr (q.property t ht))

end Submission.SphereCap
