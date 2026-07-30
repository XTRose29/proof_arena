import Submission.SphereAvoidance
import Submission.SphereLocalNormal

open scoped unitInterval

noncomputable section

namespace Submission.SphereUpperChart

open Submission.SphereRegularApprox

variable {m : ℕ}

/-- The horizontal radius of the latitude selected by a cap cutoff. -/
def scale (d : SphereCap.Datum) : ℝ :=
  Real.sqrt (1 - d.cutoff ^ 2)

theorem scale_pos (d : SphereCap.Datum) (hc : 0 < d.cutoff) :
    0 < scale d := by
  apply Real.sqrt_pos.2
  nlinarith [d.lt_one]

theorem scale_sq (d : SphereCap.Datum) (hc : 0 < d.cutoff) :
    scale d ^ 2 = 1 - d.cutoff ^ 2 := by
  apply Real.sq_sqrt
  nlinarith [d.lt_one]

theorem scale_le_one (d : SphereCap.Datum) :
    scale d ≤ 1 := by
  rw [scale]
  apply (Real.sqrt_le_iff).2
  constructor
  · norm_num
  · nlinarith [sq_nonneg d.cutoff]

/-- Rescale the horizontal projection so that the selected latitude becomes
the unit Euclidean sphere. -/
def coordinate (d : SphereCap.Datum) (y : UnitSphere m) : Domain m :=
  (scale d)⁻¹ • horizontal m y

theorem continuous_coordinate (d : SphereCap.Datum) :
    Continuous (coordinate (m := m) d) := by
  unfold coordinate
  exact (continuous_const_smul (scale d)⁻¹).comp <|
    (contDiff_horizontal m).continuous.comp continuous_subtype_val

theorem norm_horizontal_eq_one_of_vertical_eq_zero
    (y : UnitSphere m) (hy : vertical m y = 0) :
    ‖horizontal m y‖ = 1 := by
  have hdecomp := norm_sq_horizontal_add_vertical m (y : Target m)
  rw [SphereGenerator.sphere_norm_eq_one m y, hy] at hdecomp
  have hnonneg := norm_nonneg (horizontal m y)
  nlinarith

theorem one_le_norm_coordinate_of_vertical_eq_zero
    (d : SphereCap.Datum) (hc : 0 < d.cutoff)
    (y : UnitSphere m) (hy : vertical m y = 0) :
    1 ≤ ‖coordinate d y‖ := by
  rw [coordinate, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (scale_pos d hc)),
    norm_horizontal_eq_one_of_vertical_eq_zero y hy, mul_one]
  exact (one_le_inv₀ (scale_pos d hc)).2 (scale_le_one d)

theorem one_le_norm_coordinate_of_vertical_le_cutoff
    (d : SphereCap.Datum) (hc : 0 < d.cutoff)
    (y : UnitSphere m) (hy0 : 0 ≤ vertical m y)
    (hyc : vertical m y ≤ d.cutoff) :
    1 ≤ ‖coordinate d y‖ := by
  have hdecomp := norm_sq_horizontal_add_vertical m (y : Target m)
  rw [SphereGenerator.sphere_norm_eq_one m y] at hdecomp
  have hscaleSq := scale_sq d hc
  have hhorizontal : scale d ≤ ‖horizontal m y‖ := by
    have hs0 := (scale_pos d hc).le
    have hh0 := norm_nonneg (horizontal m y)
    nlinarith
  rw [coordinate, norm_smul, Real.norm_eq_abs,
    abs_of_pos (inv_pos.mpr (scale_pos d hc))]
  exact (one_le_inv_mul₀ (scale_pos d hc)).2 hhorizontal

/-- Collapse the lower hemisphere and identify the chosen upper cap with the
standard compactly supported Euclidean bubble. -/
def map (d : SphereCap.Datum) (y : UnitSphere m) : UnitSphere m :=
  if 0 ≤ vertical m y then
    SphereBubble.map m (coordinate d y)
  else
    SphereGenerator.canonicalBasepoint m

theorem continuous_map (d : SphereCap.Datum) (hc : 0 < d.cutoff) :
    Continuous (map (m := m) d) := by
  let k : UnitSphere m → ℝ := fun y => vertical m y
  have hk : Continuous k :=
    (contDiff_vertical m).continuous.comp continuous_subtype_val
  have hcoordinate : Continuous
      (fun y : UnitSphere m => SphereBubble.map m (coordinate d y)) :=
    (SphereBubble.continuous_map m).comp (continuous_coordinate d)
  change Continuous
    (fun y : UnitSphere m =>
      if (fun _ => (0 : ℝ)) y ≤ k y then
        SphereBubble.map m (coordinate d y)
      else SphereGenerator.canonicalBasepoint m)
  exact Continuous.if_le hcoordinate continuous_const continuous_const hk
    fun y hy => SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m
      (one_le_norm_coordinate_of_vertical_eq_zero d hc y hy.symm)

theorem map_eq_basepoint_of_vertical_le_cutoff
    (d : SphereCap.Datum) (hc : 0 < d.cutoff)
    (y : UnitSphere m) (hy : vertical m y ≤ d.cutoff) :
    map d y = SphereGenerator.canonicalBasepoint m := by
  by_cases hy0 : 0 ≤ vertical m y
  · rw [map, if_pos hy0]
    exact SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m
      (one_le_norm_coordinate_of_vertical_le_cutoff d hc y hy0 hy)
  · rw [map, if_neg hy0]

@[simp]
theorem map_basepoint (d : SphereCap.Datum) (hc : 0 < d.cutoff) :
    map d (SphereGenerator.canonicalBasepoint m) =
      SphereGenerator.canonicalBasepoint m := by
  apply map_eq_basepoint_of_vertical_le_cutoff d hc
  rw [vertical_canonicalBasepoint]
  exact d.neg_one_lt.le

@[simp]
theorem horizontal_antipode :
    horizontal m
        (-(SphereGenerator.canonicalBasepoint m) : UnitSphere m) = 0 := by
  ext i
  simp [horizontal, SphereRegularApprox.coe_canonicalBasepoint]

theorem horizontal_neg (w : Target m) :
    horizontal m (-w) = -horizontal m w := by
  ext i
  simp [horizontal]

@[simp]
theorem map_antipode (d : SphereCap.Datum) :
    map d (-(SphereGenerator.canonicalBasepoint m)) =
      -(SphereGenerator.canonicalBasepoint m) := by
  have hvertical :
      vertical m (-(SphereGenerator.canonicalBasepoint m) : UnitSphere m) = 1 := by
    simp [vertical, SphereRegularApprox.coe_canonicalBasepoint]
  have hhorizontal :
      horizontal m
          (-(SphereGenerator.canonicalBasepoint m) : UnitSphere m) = 0 := by
    exact horizontal_antipode
  rw [map, if_pos (by rw [hvertical]; norm_num)]
  rw [coordinate, hhorizontal, smul_zero, SphereBubble.map_zero]

theorem self_ne_neg_map (d : SphereCap.Datum) (hc : 0 < d.cutoff)
    (y : UnitSphere m) :
    y ≠ -map d y := by
  intro hy
  by_cases hk : 0 ≤ vertical m y
  · rw [map, if_pos hk] at hy
    by_cases hv : 1 ≤ ‖coordinate d y‖
    · rw [SphereBubble.map_eq_canonicalBasepoint_of_one_le_norm m hv] at hy
      have hyNorth :
          y = -(SphereGenerator.canonicalBasepoint m) :=
        hy
      have hcoordinate : coordinate d y = 0 := by
        rw [hyNorth]
        rw [coordinate, horizontal_antipode, smul_zero]
      rw [hcoordinate, norm_zero] at hv
      norm_num at hv
    · have hvlt : ‖coordinate d y‖ < 1 := lt_of_not_ge hv
      let v : Domain m := coordinate d y
      let c : ℝ :=
        ‖SphereBubble.raw m v‖⁻¹ *
          (1 - SphereBubble.radius m v) * (scale d)⁻¹
      have hradius :
          SphereBubble.radius m v = ‖v‖ := by
        exact min_eq_left hvlt.le
      have hcpos : 0 < c := by
        dsimp only [c]
        have hraw : 0 < ‖SphereBubble.raw m v‖⁻¹ :=
          inv_pos.mpr (SphereBubble.norm_raw_pos m v)
        have hradiusPos : 0 < 1 - SphereBubble.radius m v := by
          rw [hradius]
          linarith
        have hscale : 0 < (scale d)⁻¹ :=
          inv_pos.mpr (scale_pos d hc)
        positivity
      have hhorizontal :
          horizontal m y = -(c • horizontal m y) := by
        have h := congrArg
          (fun z : UnitSphere m => horizontal m (z : Target m)) hy
        change
          horizontal m y =
            horizontal m
              (-(SphereBubble.map m (coordinate d y) : Target m)) at h
        rw [horizontal_neg, SphereBubble.horizontal_map] at h
        change
          horizontal m y =
            -(‖SphereBubble.raw m v‖⁻¹ •
              ((1 - SphereBubble.radius m v) • v)) at h
        simpa [v, coordinate, c, smul_smul, mul_assoc] using h
      have hhorizontalZero : horizontal m y = 0 := by
        have hsum :
            (1 + c) • horizontal m y = 0 := by
          calc
            (1 + c) • horizontal m y =
                horizontal m y + c • horizontal m y := by module
            _ = -(c • horizontal m y) +
                c • horizontal m y :=
              congrArg (fun w => w + c • horizontal m y) hhorizontal
            _ = 0 := neg_add_cancel _
        exact (smul_eq_zero.mp hsum).resolve_left (by
          exact ne_of_gt (by linarith))
      have hmapNorth :
          SphereBubble.map m (coordinate d y) =
            -(SphereGenerator.canonicalBasepoint m) := by
        rw [coordinate, hhorizontalZero, smul_zero,
          SphereBubble.map_zero]
      rw [hmapNorth] at hy
      have hvertical := congrArg
        (fun z : UnitSphere m => vertical m z) hy
      have :
          vertical m y = -1 := by
        simpa [vertical, SphereRegularApprox.coe_canonicalBasepoint]
          using hvertical
      linarith
  · rw [map, if_neg hk] at hy
    have hvertical := congrArg
      (fun z : UnitSphere m => vertical m z) hy
    have :
        vertical m y = 1 := by
      simpa [vertical, SphereRegularApprox.coe_canonicalBasepoint]
        using hvertical
    exact hk (by rw [this]; norm_num)

/-- The upper-chart collapse is homotopic to the identity while fixing the
south pole. -/
def homotopyRel (d : SphereCap.Datum) (hc : 0 < d.cutoff) :
    (ContinuousMap.id (UnitSphere m)).HomotopyRel
      ⟨map d, continuous_map d hc⟩
      {SphereGenerator.canonicalBasepoint m} :=
  SphereHomotopy.normalizedLineHomotopyRel
    (ContinuousMap.id (UnitSphere m))
    ⟨map d, continuous_map d hc⟩
    (fun y =>
      SphereAvoidance.dist_lt_two_of_ne_neg y (map d y)
        (self_ne_neg_map d hc y))
    {SphereGenerator.canonicalBasepoint m}
    fun y hy => by
      rw [Set.mem_singleton_iff] at hy
      subst y
      exact (map_basepoint d hc).symm

/-- Postcompose a generalized loop by the upper-cap Euclidean chart. -/
def genLoop (d : SphereCap.Datum) (hc : 0 < d.cutoff)
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m) :=
  ⟨⟨fun t => map d (q t),
      (continuous_map d hc).comp q.1.continuous⟩,
    fun t ht =>
      (congrArg (map d) (q.property t ht)).trans (map_basepoint d hc)⟩

theorem genLoop_homotopic (d : SphereCap.Datum) (hc : 0 < d.cutoff)
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m)) :
    GenLoop.Homotopic q (genLoop d hc q) := by
  refine ⟨{
    toHomotopy :=
      (homotopyRel d hc).toHomotopy.compContinuousMap q.1
    prop' := ?_
  }⟩
  intro s t ht
  change (homotopyRel d hc) (s, q t) = q t
  exact (homotopyRel d hc).prop' s _
    (Set.mem_singleton_iff.mpr (q.property t ht))

/-- A positive cap cutoff can be chosen arbitrarily close to one, and hence
with arbitrarily small horizontal scale, while remaining above a prescribed
latitude. -/
theorem exists_datum_above_with_scale_lt
    {z δ : ℝ} (hz : z < 1) (hδ : 0 < δ) :
    ∃ d : SphereCap.Datum,
      0 < d.cutoff ∧ z < d.cutoff ∧ scale d < δ := by
  let e : ℝ :=
    min ((1 - z) / 2) (min (1 / 4) (δ ^ 2 / 4))
  have hepos : 0 < e := by
    dsimp only [e]
    exact lt_min
      (by linarith)
      (lt_min (by norm_num) (by positivity))
  have hez : e ≤ (1 - z) / 2 :=
    min_le_left _ _
  have hequarter : e ≤ 1 / 4 :=
    (min_le_right _ _).trans (min_le_left _ _)
  have heδ : e ≤ δ ^ 2 / 4 :=
    (min_le_right _ _).trans (min_le_right _ _)
  let c : ℝ := 1 - e
  have hcpos : 0 < c := by
    dsimp only [c]
    linarith
  have hcneg : -1 < c := by
    dsimp only [c]
    linarith
  have hcone : c < 1 := by
    dsimp only [c]
    linarith
  have hzc : z < c := by
    dsimp only [c]
    linarith
  let d : SphereCap.Datum := ⟨c, hcneg, hcone⟩
  have hscaleSq : scale d ^ 2 = 1 - c ^ 2 :=
    scale_sq d hcpos
  have hscaleNonneg : 0 ≤ scale d :=
    Real.sqrt_nonneg _
  have hscaleSqLt : scale d ^ 2 < δ ^ 2 := by
    rw [hscaleSq]
    dsimp only [c]
    nlinarith [sq_nonneg e, sq_pos_of_pos hδ]
  have hscaleLt : scale d < δ :=
    (sq_lt_sq₀ hscaleNonneg hδ.le).mp hscaleSqLt
  exact ⟨d, hcpos, hzc, hscaleLt⟩

/-- The upper-chart representative can be made constant away from any open
neighborhood of its finite north-pole fiber. -/
theorem exists_genLoop_constant_off
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    {U : Set (Fin (m + 1) → I)}
    (hU : IsOpen U)
    (hfiber :
      {t |
        q t = -(SphereGenerator.canonicalBasepoint m)} ⊆ U) :
    ∃ (d : SphereCap.Datum) (hc : 0 < d.cutoff),
      GenLoop.Homotopic q (genLoop d hc q) ∧
      ∀ t ∉ U,
        genLoop d hc q t =
          SphereGenerator.canonicalBasepoint m := by
  obtain ⟨d, hc, _, hvertical, _⟩ :=
    SphereLocalNormal.exists_capDatum_constant_off q hU hfiber
  refine ⟨d, hc, genLoop_homotopic d hc q, ?_⟩
  intro t ht
  exact map_eq_basepoint_of_vertical_le_cutoff d hc (q t)
    (hvertical t ht)

/-- The upper-chart representative can be localized as above while making
its Euclidean chart scale smaller than any prescribed positive number. -/
theorem exists_genLoop_constant_off_scale_lt
    (q : GenLoop (Fin (m + 1)) (UnitSphere m)
      (SphereGenerator.canonicalBasepoint m))
    {U : Set (Fin (m + 1) → I)}
    (hU : IsOpen U)
    (hfiber :
      {t |
        q t = -(SphereGenerator.canonicalBasepoint m)} ⊆ U)
    {δ : ℝ} (hδ : 0 < δ) :
    ∃ (d : SphereCap.Datum) (hc : 0 < d.cutoff),
      scale d < δ ∧
      GenLoop.Homotopic q (genLoop d hc q) ∧
      ∀ t ∉ U,
        genLoop d hc q t =
          SphereGenerator.canonicalBasepoint m := by
  obtain ⟨d₀, hc₀, _, hvertical, _⟩ :=
    SphereLocalNormal.exists_capDatum_constant_off q hU hfiber
  obtain ⟨d, hc, hd₀d, hscale⟩ :=
    exists_datum_above_with_scale_lt d₀.lt_one hδ
  refine ⟨d, hc, hscale, genLoop_homotopic d hc q, ?_⟩
  intro t ht
  exact map_eq_basepoint_of_vertical_le_cutoff d hc (q t) <|
    (hvertical t ht).trans hd₀d.le

end Submission.SphereUpperChart
