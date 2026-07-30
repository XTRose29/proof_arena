import Submission.SphereSplit

open scoped unitInterval

noncomputable section

namespace Submission.SpherePlateau

open Set
open Submission.SphereRegularApprox

variable {m : ℕ}

/-- Two target latitudes specifying a collapse below `lower` which is the
identity above `upper`. -/
structure Datum where
  lower : ℝ
  upper : ℝ
  neg_one_lt_lower : -1 < lower
  lower_lt_upper : lower < upper
  upper_lt_one : upper < 1

namespace Datum

theorem denominator_pos (d : Datum) :
    0 < d.upper - d.lower :=
  sub_pos.mpr d.lower_lt_upper

end Datum

/-- A continuous weight which is one below the lower latitude and zero above
the upper latitude. -/
def weight (d : Datum) (y : UnitSphere m) : I :=
  projIcc 0 1 zero_le_one
    ((d.upper - vertical m y) / (d.upper - d.lower))

theorem continuous_weight (d : Datum) :
    Continuous (weight (m := m) d) := by
  unfold weight
  fun_prop

theorem weight_eq_one_of_vertical_le_lower (d : Datum)
    {y : UnitSphere m} (hy : vertical m y ≤ d.lower) :
    weight d y = 1 := by
  unfold weight
  apply projIcc_of_right_le
  apply (le_div_iff₀ d.denominator_pos).2
  linarith

theorem weight_eq_zero_of_upper_le_vertical (d : Datum)
    {y : UnitSphere m} (hy : d.upper ≤ vertical m y) :
    weight d y = 0 := by
  unfold weight
  apply projIcc_of_le_left
  apply div_nonpos_of_nonpos_of_nonneg
  · linarith
  · exact d.denominator_pos.le

theorem weight_antipode (d : Datum) :
    weight d (-(SphereGenerator.canonicalBasepoint m)) = 0 := by
  apply weight_eq_zero_of_upper_le_vertical
  have hvertical :
      vertical m (-(SphereGenerator.canonicalBasepoint m) : UnitSphere m) = 1 := by
    simp [vertical, SphereRegularApprox.coe_canonicalBasepoint]
  rw [hvertical]
  exact d.upper_lt_one.le

/-- Interpolate toward the south pole with the plateau weight. -/
def raw (d : Datum) (y : UnitSphere m) : Target m :=
  AffineMap.lineMap (y : Target m)
    (SphereGenerator.canonicalBasepoint m : Target m)
    (weight d y : ℝ)

theorem continuous_raw (d : Datum) :
    Continuous (raw (m := m) d) := by
  unfold raw
  apply Continuous.lineMap
  · exact continuous_subtype_val
  · exact continuous_const
  · exact continuous_subtype_val.comp (continuous_weight d)

theorem horizontal_raw (d : Datum) (y : UnitSphere m) :
    horizontal m (raw d y) =
      (1 - (weight d y : ℝ)) • horizontal m y := by
  ext i
  simp [raw, AffineMap.lineMap_apply, horizontal,
    SphereRegularApprox.coe_canonicalBasepoint]
  ring

theorem raw_antipode (d : Datum) :
    raw d (-(SphereGenerator.canonicalBasepoint m)) =
      -(SphereGenerator.canonicalBasepoint m : Target m) := by
  simp [raw, weight_antipode, AffineMap.lineMap_apply]

theorem raw_ne_zero (d : Datum) (y : UnitSphere m) :
    raw d y ≠ 0 := by
  by_cases hy :
      y = -(SphereGenerator.canonicalBasepoint m)
  · subst y
    rw [raw_antipode]
    exact neg_ne_zero.mpr fun hzero => by
      have hnorm := SphereGenerator.sphere_norm_eq_one m
        (SphereGenerator.canonicalBasepoint m)
      rw [hzero, norm_zero] at hnorm
      norm_num at hnorm
  · let f : C(Unit, UnitSphere m) := ContinuousMap.const Unit y
    let g : C(Unit, UnitSphere m) :=
      ContinuousMap.const Unit (SphereGenerator.canonicalBasepoint m)
    let s : I := weight d y
    have hdist :
        ∀ a : Unit, dist (f a) (g a) < 2 := by
      intro a
      exact SphereAvoidance.dist_lt_two_of_ne_neg y
        (SphereGenerator.canonicalBasepoint m) hy
    have hne :=
      SphereHomotopy.lineRaw_ne_zero f g hdist (s, ())
    simpa [raw, SphereHomotopy.lineRaw, f, g, s] using hne

/-- The plateau collapse as a sphere self-map. -/
def map (d : Datum) (y : UnitSphere m) : UnitSphere m :=
  ⟨NormedSpace.normalize (raw d y), by
    rw [Metric.mem_sphere, dist_zero_right]
    exact NormedSpace.norm_normalize (raw_ne_zero d y)⟩

theorem continuous_map (d : Datum) :
    Continuous (map (m := m) d) := by
  apply Continuous.subtype_mk
  change Continuous (fun y => ‖raw d y‖⁻¹ • raw d y)
  exact
    ((continuous_raw d).norm.inv₀ fun y =>
      norm_ne_zero_iff.mpr (raw_ne_zero d y)).smul
        (continuous_raw d)

theorem map_eq_basepoint_of_vertical_le_lower (d : Datum)
    {y : UnitSphere m} (hy : vertical m y ≤ d.lower) :
    map d y = SphereGenerator.canonicalBasepoint m := by
  have hw := weight_eq_one_of_vertical_le_lower d hy
  apply Subtype.ext
  change
    NormedSpace.normalize (raw d y) =
      (SphereGenerator.canonicalBasepoint m : Target m)
  have hraw :
      raw d y =
        (SphereGenerator.canonicalBasepoint m : Target m) := by
    simp [raw, AffineMap.lineMap_apply, hw]
  rw [hraw]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (SphereGenerator.sphere_norm_eq_one m
      (SphereGenerator.canonicalBasepoint m))

theorem map_eq_self_of_upper_le_vertical (d : Datum)
    {y : UnitSphere m} (hy : d.upper ≤ vertical m y) :
    map d y = y := by
  have hw := weight_eq_zero_of_upper_le_vertical d hy
  apply Subtype.ext
  change NormedSpace.normalize (raw d y) = (y : Target m)
  have hraw : raw d y = (y : Target m) := by
    simp [raw, AffineMap.lineMap_apply, hw]
  rw [hraw]
  exact NormedSpace.normalize_eq_self_of_norm_eq_one
    (SphereGenerator.sphere_norm_eq_one m y)

@[simp]
theorem map_basepoint (d : Datum) :
    map d (SphereGenerator.canonicalBasepoint m) =
      SphereGenerator.canonicalBasepoint m := by
  apply map_eq_basepoint_of_vertical_le_lower
  rw [vertical_canonicalBasepoint]
  exact d.neg_one_lt_lower.le

@[simp]
theorem map_antipode (d : Datum) :
    map d (-(SphereGenerator.canonicalBasepoint m)) =
      -(SphereGenerator.canonicalBasepoint m) := by
  apply map_eq_self_of_upper_le_vertical
  have hvertical :
      vertical m (-(SphereGenerator.canonicalBasepoint m) : UnitSphere m) = 1 := by
    simp [vertical, SphereRegularApprox.coe_canonicalBasepoint]
  rw [hvertical]
  exact d.upper_lt_one.le

theorem eq_basepoint_of_vertical_eq_neg_one
    (y : UnitSphere m) (hy : vertical m y = -1) :
    y = SphereGenerator.canonicalBasepoint m := by
  have hdecomp := norm_sq_horizontal_add_vertical m (y : Target m)
  rw [SphereGenerator.sphere_norm_eq_one m y, hy] at hdecomp
  have hhorizontalNorm : ‖horizontal m y‖ = 0 := by
    nlinarith [norm_nonneg (horizontal m y)]
  have hhorizontal : horizontal m y = 0 :=
    norm_eq_zero.mp hhorizontalNorm
  apply Subtype.ext
  rw [SphereRegularApprox.coe_canonicalBasepoint]
  ext i
  cases i using Fin.lastCases with
  | last =>
      simpa [vertical] using hy
  | cast j =>
      have hj := congrArg (fun v : Domain m => v j) hhorizontal
      simpa [horizontal] using hj

theorem map_eq_antipode_iff (d : Datum) (y : UnitSphere m) :
    map d y = -(SphereGenerator.canonicalBasepoint m) ↔
      y = -(SphereGenerator.canonicalBasepoint m) := by
  constructor
  · intro hmap
    have hnormalize :
        NormedSpace.normalize (raw d y) =
          -(SphereGenerator.canonicalBasepoint m : Target m) := by
      simpa [map] using congrArg Subtype.val hmap
    have hraw :
        raw d y =
          ‖raw d y‖ •
            (-(SphereGenerator.canonicalBasepoint m : Target m)) := by
      calc
        raw d y = ‖raw d y‖ • NormedSpace.normalize (raw d y) :=
          (NormedSpace.norm_smul_normalize (raw d y)).symm
        _ = _ := by rw [hnormalize]
    have hhorizontalRaw : horizontal m (raw d y) = 0 := by
      rw [hraw]
      ext i
      simp [horizontal, SphereRegularApprox.coe_canonicalBasepoint]
    rw [horizontal_raw] at hhorizontalRaw
    have hweight : (weight d y : ℝ) ≠ 1 := by
      intro hw
      have hsouth :
          map d y = SphereGenerator.canonicalBasepoint m := by
        apply Subtype.ext
        change
          NormedSpace.normalize (raw d y) =
            (SphereGenerator.canonicalBasepoint m : Target m)
        have hrawSouth :
            raw d y =
              (SphereGenerator.canonicalBasepoint m : Target m) := by
          simp [raw, AffineMap.lineMap_apply, hw]
        rw [hrawSouth]
        exact NormedSpace.normalize_eq_self_of_norm_eq_one
          (SphereGenerator.sphere_norm_eq_one m
            (SphereGenerator.canonicalBasepoint m))
      rw [hmap] at hsouth
      exact SphereRegularApprox.canonicalBasepoint_ne_neg m hsouth.symm
    have hhorizontal : horizontal m y = 0 :=
      (smul_eq_zero.mp hhorizontalRaw).resolve_left
        (sub_ne_zero.mpr hweight.symm)
    have hdecomp := norm_sq_horizontal_add_vertical m (y : Target m)
    rw [SphereGenerator.sphere_norm_eq_one m y, hhorizontal,
      norm_zero] at hdecomp
    norm_num at hdecomp
    rcases sq_eq_one_iff.mp hdecomp.symm with hvertical | hvertical
    · exact SphereCap.eq_antipode_of_vertical_eq_one y hvertical
    · have hySouth := eq_basepoint_of_vertical_eq_neg_one y hvertical
      rw [hySouth, map_basepoint] at hmap
      exfalso
      exact (SphereRegularApprox.canonicalBasepoint_ne_neg m) hmap
  · rintro rfl
    exact map_antipode d

/-- The interpolation from the identity to the plateau collapse. -/
def deformationRaw (d : Datum) (z : I × UnitSphere m) : Target m :=
  AffineMap.lineMap (z.2 : Target m)
    (SphereGenerator.canonicalBasepoint m : Target m)
    ((z.1 : ℝ) * (weight d z.2 : ℝ))

theorem continuous_deformationRaw (d : Datum) :
    Continuous (deformationRaw (m := m) d) := by
  unfold deformationRaw
  apply Continuous.lineMap
  · exact continuous_subtype_val.comp continuous_snd
  · exact continuous_const
  · fun_prop

theorem deformationRaw_ne_zero (d : Datum)
    (z : I × UnitSphere m) :
    deformationRaw d z ≠ 0 := by
  by_cases hy :
      z.2 = -(SphereGenerator.canonicalBasepoint m)
  · have hw : weight d z.2 = 0 := by
      rw [hy]
      exact weight_antipode d
    have hraw :
        deformationRaw d z = (z.2 : Target m) := by
      simp [deformationRaw, AffineMap.lineMap_apply, hw]
    rw [hraw]
    intro hzero
    have hnorm := SphereGenerator.sphere_norm_eq_one m z.2
    rw [hzero, norm_zero] at hnorm
    norm_num at hnorm
  · let f : C(Unit, UnitSphere m) :=
      ContinuousMap.const Unit z.2
    let g : C(Unit, UnitSphere m) :=
      ContinuousMap.const Unit
        (SphereGenerator.canonicalBasepoint m)
    let s : I :=
      ⟨(z.1 : ℝ) * (weight d z.2 : ℝ), by
        constructor
        · exact mul_nonneg z.1.property.1 (weight d z.2).property.1
        · exact mul_le_one₀ z.1.property.2
            (weight d z.2).property.1
            (weight d z.2).property.2⟩
    have hdist :
        ∀ a : Unit, dist (f a) (g a) < 2 := by
      intro a
      exact SphereAvoidance.dist_lt_two_of_ne_neg z.2
        (SphereGenerator.canonicalBasepoint m) hy
    have hne :=
      SphereHomotopy.lineRaw_ne_zero f g hdist (s, ())
    simpa [deformationRaw, SphereHomotopy.lineRaw, f, g, s] using hne

/-- The plateau collapse is homotopic to the identity and fixes the south
pole. -/
def homotopyRel (d : Datum) :
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
        norm_ne_zero_iff.mpr
          (deformationRaw_ne_zero d z)).smul
            (continuous_deformationRaw d)
  map_zero_left y := by
    apply Subtype.ext
    change
      NormedSpace.normalize (deformationRaw d (0, y)) =
        (y : Target m)
    have hraw :
        deformationRaw d (0, y) = (y : Target m) := by
      simp [deformationRaw, AffineMap.lineMap_apply]
    rw [hraw]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (SphereGenerator.sphere_norm_eq_one m y)
  map_one_left y := by
    apply Subtype.ext
    change
      NormedSpace.normalize (deformationRaw d (1, y)) =
        NormedSpace.normalize (raw d y)
    congr 1
    simp [deformationRaw, raw]
  prop' s y hy := by
    rw [Set.mem_singleton_iff] at hy
    subst y
    apply Subtype.ext
    change
      NormedSpace.normalize
          (deformationRaw d
            (s, SphereGenerator.canonicalBasepoint m)) =
        (SphereGenerator.canonicalBasepoint m : Target m)
    have hvertical :
        vertical m (SphereGenerator.canonicalBasepoint m) ≤ d.lower := by
      rw [vertical_canonicalBasepoint]
      exact d.neg_one_lt_lower.le
    have hw :=
      weight_eq_one_of_vertical_le_lower d hvertical
    have hraw :
        deformationRaw d
            (s, SphereGenerator.canonicalBasepoint m) =
          (SphereGenerator.canonicalBasepoint m : Target m) := by
      simp [deformationRaw, hw]
    rw [hraw]
    exact NormedSpace.normalize_eq_self_of_norm_eq_one
      (SphereGenerator.sphere_norm_eq_one m
        (SphereGenerator.canonicalBasepoint m))

/-- Postcompose a generalized loop with a plateau collapse. -/
def genLoop (d : Datum)
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨fun t => map d (q t),
      (continuous_map d).comp q.1.continuous⟩,
    fun t ht =>
      (congrArg (map d) (q.property t ht)).trans (map_basepoint d)⟩

theorem genLoop_homotopic (d : Datum)
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    GenLoop.Homotopic q (genLoop d q) := by
  refine ⟨{
    toHomotopy := (homotopyRel d).toHomotopy.compContinuousMap q.1
    prop' := ?_
  }⟩
  intro s t ht
  change (homotopyRel d) (s, q t) = q t
  exact (homotopyRel d).prop' s _
    (Set.mem_singleton_iff.mpr (q.property t ht))

theorem vertical_neg_one_le (y : UnitSphere m) :
    -1 ≤ vertical m y := by
  have hv := PiLp.norm_apply_le
    (y : Target m) (Fin.last (m + 1))
  rw [SphereGenerator.sphere_norm_eq_one m y,
    Real.norm_eq_abs] at hv
  exact neg_le_of_abs_le hv

/-- On a compact set disjoint from the north-pole fiber, one can choose a
plateau collapse which is constant on that set and remains the identity in a
target neighborhood of the north pole. -/
theorem exists_datum_constant_on_compact
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    (K : Set (Fin (m + 1) → I))
    (hK : IsCompact K)
    (havoid :
      ∀ t ∈ K,
        q t ≠ -(SphereGenerator.canonicalBasepoint m)) :
    ∃ d : Datum,
      GenLoop.Homotopic q (genLoop d q) ∧
      (∀ t ∈ K,
        genLoop d q t = SphereGenerator.canonicalBasepoint m) ∧
      (∀ t, d.upper ≤ vertical m (q t) →
        genLoop d q t = q t) := by
  by_cases hnonempty : K.Nonempty
  · have hcontinuous :
        Continuous
          (fun t : Fin (m + 1) → I =>
            vertical m (q t)) := by
      fun_prop
    obtain ⟨t₀, ht₀, hmax⟩ :=
      hK.exists_isMaxOn hnonempty hcontinuous.continuousOn
    let z : ℝ := vertical m (q t₀)
    have hzlt : z < 1 := by
      have hzle : z ≤ 1 := SphereCap.vertical_le_one (q t₀)
      exact lt_of_le_of_ne hzle fun hz => by
        exact havoid t₀ ht₀
          (SphereCap.eq_antipode_of_vertical_eq_one (q t₀) hz)
    have hzlower : -1 ≤ z :=
      vertical_neg_one_le (q t₀)
    let lower : ℝ := (z + 1) / 2
    let upper : ℝ := (lower + 1) / 2
    have hlowerNeg : -1 < lower := by
      dsimp only [lower]
      linarith
    have hzleLower : z ≤ lower := by
      dsimp only [lower]
      linarith
    have hlowerUpper : lower < upper := by
      dsimp only [upper, lower]
      linarith
    have hupperOne : upper < 1 := by
      dsimp only [upper, lower]
      linarith
    let d : Datum :=
      ⟨lower, upper, hlowerNeg, hlowerUpper, hupperOne⟩
    refine ⟨d, genLoop_homotopic d q, ?_, ?_⟩
    · intro t ht
      change map d (q t) = SphereGenerator.canonicalBasepoint m
      apply map_eq_basepoint_of_vertical_le_lower
      exact (hmax ht).trans hzleLower
    · intro t ht
      change map d (q t) = q t
      exact map_eq_self_of_upper_le_vertical d ht
  · have hKempty : K = ∅ :=
      not_nonempty_iff_eq_empty.mp hnonempty
    let d : Datum :=
      ⟨0, 1 / 2, by norm_num, by norm_num, by norm_num⟩
    refine ⟨d, genLoop_homotopic d q, ?_, ?_⟩
    · intro t ht
      rw [hKempty] at ht
      contradiction
    · intro t ht
      change map d (q t) = q t
      exact map_eq_self_of_upper_le_vertical d ht

end Submission.SpherePlateau
