import Submission.GlobalFlow
import Submission.Transport

open Filter Metric Set Topology
open scoped Convex

open LeanEval.Dynamics

namespace Submission.Transversal

noncomputable section

/-- The real linear functional which, after translating by a base point,
measures displacement in the direction of a nonzero vector `v`. -/
def transverseFunctional (v : Plane) : Plane →L[ℝ] ℝ :=
  Complex.reCLM.comp
    ((ContinuousLinearMap.lsmul ℝ ℂ
      (Transport.planeEquiv v)⁻¹).comp
        Transport.planeEquiv.toContinuousLinearMap)

theorem transverseFunctional_apply (v y : Plane) :
    transverseFunctional v y =
      ((Transport.planeEquiv v)⁻¹ * Transport.planeEquiv y).re := by
  simp [transverseFunctional, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

def transverseValue (v p y : Plane) : ℝ :=
  transverseFunctional v (y - p)

def velocityValue (G : Plane → Plane) (p y : Plane) : ℝ :=
  transverseFunctional (G p) (G y)

theorem continuous_velocityValue {G : Plane → Plane} (hG : Continuous G)
    (p : Plane) :
    Continuous (velocityValue G p) :=
  (transverseFunctional (G p)).continuous.comp hG

/-- The normalized coordinate along the affine transversal perpendicular to
`v`. -/
def sectionFunctional (v : Plane) : Plane →L[ℝ] ℝ :=
  Complex.imCLM.comp
    ((ContinuousLinearMap.lsmul ℝ ℂ
      (Transport.planeEquiv v)⁻¹).comp
        Transport.planeEquiv.toContinuousLinearMap)

theorem sectionFunctional_apply (v y : Plane) :
    sectionFunctional v y =
      ((Transport.planeEquiv v)⁻¹ * Transport.planeEquiv y).im := by
  simp [sectionFunctional, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.lsmul_apply, smul_eq_mul]

def sectionValue (v p y : Plane) : ℝ :=
  sectionFunctional v (y - p)

theorem continuous_sectionValue (v p : Plane) :
    Continuous (sectionValue v p) :=
  (sectionFunctional v).continuous.comp
    (continuous_id.sub continuous_const)

theorem velocityValue_self {G : Plane → Plane} {p : Plane}
    (hp : G p ≠ 0) :
    velocityValue G p p = 1 := by
  have hz : Transport.planeEquiv (G p) ≠ 0 :=
    Transport.planeEquiv.map_ne_zero_iff.mpr hp
  rw [velocityValue, transverseFunctional_apply, inv_mul_cancel₀ hz]
  norm_num

/-- A parametrization of the affine line through `p` transverse to `v`. -/
def sectionPoint (v p : Plane) (u : ℝ) : Plane :=
  Transport.planeEquiv.symm
    (Transport.planeEquiv p +
      Transport.planeEquiv v * ((u : ℂ) * Complex.I))

theorem continuous_sectionPoint (v p : Plane) :
    Continuous (sectionPoint v p) := by
  apply Transport.planeEquiv.symm.continuous.comp
  fun_prop

@[simp]
theorem sectionPoint_zero (v p : Plane) :
    sectionPoint v p 0 = p := by
  apply Transport.planeEquiv.injective
  simp [sectionPoint]

theorem sectionPoint_injective {v p : Plane} (hv : v ≠ 0) :
    Function.Injective (sectionPoint v p) := by
  intro u w huw
  have hz : Transport.planeEquiv v ≠ 0 :=
    Transport.planeEquiv.map_ne_zero_iff.mpr hv
  have hcomplex := congrArg Transport.planeEquiv huw
  simp only [sectionPoint, Transport.planeEquiv.apply_symm_apply] at hcomplex
  have hmul :
      Transport.planeEquiv v * ((u : ℂ) * Complex.I) =
        Transport.planeEquiv v * ((w : ℂ) * Complex.I) :=
    add_left_cancel hcomplex
  have hui : (u : ℂ) * Complex.I = (w : ℂ) * Complex.I :=
    mul_left_cancel₀ hz hmul
  have huc : (u : ℂ) = (w : ℂ) :=
    mul_right_cancel₀ Complex.I_ne_zero hui
  exact_mod_cast huc

theorem transverseValue_sectionPoint {v p : Plane} (hv : v ≠ 0)
    (u : ℝ) :
    transverseValue v p (sectionPoint v p u) = 0 := by
  have hz : Transport.planeEquiv v ≠ 0 :=
    Transport.planeEquiv.map_ne_zero_iff.mpr hv
  rw [transverseValue, transverseFunctional_apply]
  simp only [sectionPoint, map_sub,
    Transport.planeEquiv.apply_symm_apply, add_sub_cancel_left]
  rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
  simp

theorem transverseFunctional_self {v : Plane} (hv : v ≠ 0) :
    transverseFunctional v v = 1 := by
  have hz : Transport.planeEquiv v ≠ 0 :=
    Transport.planeEquiv.map_ne_zero_iff.mpr hv
  rw [transverseFunctional_apply, inv_mul_cancel₀ hz]
  norm_num

/-- Moving a point of the affine transversal by `c • v` changes the
longitudinal coordinate by exactly `c`. -/
theorem transverseValue_offset_sectionPoint {v p : Plane} (hv : v ≠ 0)
    (u c : ℝ) :
    transverseValue v p (sectionPoint v p u + c • v) = c := by
  have hzero := transverseValue_sectionPoint (p := p) hv u
  unfold transverseValue at hzero ⊢
  rw [show sectionPoint v p u + c • v - p =
      (sectionPoint v p u - p) + c • v by module]
  rw [map_add, map_smul, transverseFunctional_self hv]
  simp [hzero]

theorem transverseValue_recenter_sectionPoint {v p : Plane} (hv : v ≠ 0)
    (u : ℝ) (z : Plane) :
    transverseFunctional v (z - sectionPoint v p u) =
      transverseValue v p z := by
  have hzero := transverseValue_sectionPoint (p := p) hv u
  unfold transverseValue at hzero ⊢
  rw [show z - sectionPoint v p u =
      (z - p) - (sectionPoint v p u - p) by module]
  rw [map_sub]
  rw [hzero, sub_zero]

theorem dist_offset_sectionPoint (v p : Plane) (u c : ℝ) :
    dist (sectionPoint v p u + c • v) (sectionPoint v p u) =
      |c| * ‖v‖ := by
  rw [dist_eq_norm]
  simp only [add_sub_cancel_left, norm_smul, Real.norm_eq_abs]

theorem sectionValue_sectionPoint {v p : Plane} (hv : v ≠ 0)
    (u : ℝ) :
    sectionValue v p (sectionPoint v p u) = u := by
  have hz : Transport.planeEquiv v ≠ 0 :=
    Transport.planeEquiv.map_ne_zero_iff.mpr hv
  rw [sectionValue, sectionFunctional_apply]
  simp only [sectionPoint, map_sub,
    Transport.planeEquiv.apply_symm_apply, add_sub_cancel_left]
  rw [← mul_assoc, inv_mul_cancel₀ hz, one_mul]
  simp

theorem sectionPoint_sectionValue {v p y : Plane} (hv : v ≠ 0)
    (hy : transverseValue v p y = 0) :
    sectionPoint v p (sectionValue v p y) = y := by
  have hz : Transport.planeEquiv v ≠ 0 :=
    Transport.planeEquiv.map_ne_zero_iff.mpr hv
  apply Transport.planeEquiv.injective
  rw [sectionPoint, Transport.planeEquiv.apply_symm_apply]
  rw [sectionValue, sectionFunctional_apply]
  have hre :
      ((Transport.planeEquiv v)⁻¹ *
        Transport.planeEquiv (y - p)).re = 0 := by
    simpa only [transverseValue, transverseFunctional_apply] using hy
  let z : ℂ :=
    (Transport.planeEquiv v)⁻¹ * Transport.planeEquiv (y - p)
  have hzdecomp : z = (z.im : ℂ) * Complex.I := by
    apply Complex.ext
    · simpa [z] using hre
    · simp
  rw [← hzdecomp]
  dsimp only [z]
  rw [← mul_assoc, mul_inv_cancel₀ hz, one_mul, map_sub]
  abel

theorem dist_sectionPoint_self {v p : Plane} (u : ℝ) :
    dist (sectionPoint v p u) p = ‖v‖ * |u| := by
  rw [dist_eq_norm]
  rw [← Transport.planeEquiv.norm_map]
  simp only [sectionPoint, map_sub,
    Transport.planeEquiv.apply_symm_apply, add_sub_cancel_left]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Transport.planeEquiv.norm_map]
  rw [Real.norm_eq_abs]

theorem dist_sectionPoint (v p : Plane) (u w : ℝ) :
    dist (sectionPoint v p u) (sectionPoint v p w) =
      ‖v‖ * |u - w| := by
  rw [dist_eq_norm, ← Transport.planeEquiv.norm_map]
  simp only [sectionPoint, map_sub,
    Transport.planeEquiv.apply_symm_apply]
  rw [show
      (Transport.planeEquiv p +
          Transport.planeEquiv v * ((u : ℂ) * Complex.I)) -
        (Transport.planeEquiv p +
          Transport.planeEquiv v * ((w : ℂ) * Complex.I)) =
        Transport.planeEquiv v * (((u - w : ℝ) : ℂ) * Complex.I) by
      push_cast
      ring]
  rw [norm_mul, norm_mul, Complex.norm_real, Complex.norm_I,
    mul_one, Transport.planeEquiv.norm_map]
  rw [Real.norm_eq_abs]

theorem lineMap_sectionPoint (v p : Plane) (a b t : ℝ) :
    AffineMap.lineMap (sectionPoint v p a) (sectionPoint v p b) t =
      sectionPoint v p ((1 - t) * a + t * b) := by
  rw [AffineMap.lineMap_apply_module]
  apply Transport.planeEquiv.injective
  simp only [sectionPoint, map_add, map_smul,
    Transport.planeEquiv.apply_symm_apply]
  simp only [Complex.real_smul]
  push_cast
  ring

theorem sectionPoint_mem_segment {v p : Plane} {a b u : ℝ}
    (hab : a < b) (hu : u ∈ Icc a b) :
    sectionPoint v p u ∈
      [sectionPoint v p a -[ℝ] sectionPoint v p b] := by
  rw [segment_eq_image]
  let t : ℝ := (u - a) / (b - a)
  have ht : t ∈ Icc (0 : ℝ) 1 := by
    constructor
    · exact div_nonneg (sub_nonneg.mpr hu.1)
        (sub_nonneg.mpr hab.le)
    · exact (div_le_one (sub_pos.mpr hab)).2
        (sub_le_sub_right hu.2 a)
  refine ⟨t, ht, ?_⟩
  change
    (1 - t) • sectionPoint v p a + t • sectionPoint v p b =
      sectionPoint v p u
  rw [← AffineMap.lineMap_apply_module]
  rw [lineMap_sectionPoint]
  congr 1
  dsimp [t]
  field_simp [sub_ne_zero.mpr hab.ne.symm]
  ring

theorem exists_eq_sectionPoint_of_mem_segment
    {v p : Plane} {a b : ℝ} (hab : a < b) {z : Plane}
    (hz : z ∈
      [sectionPoint v p a -[ℝ] sectionPoint v p b]) :
    ∃ u ∈ Icc a b, z = sectionPoint v p u := by
  rw [segment_eq_image] at hz
  obtain ⟨t, ht, rfl⟩ := hz
  let u : ℝ := (1 - t) * a + t * b
  have hu : u ∈ Icc a b := by
    dsimp [u]
    constructor <;> nlinarith [ht.1, ht.2, hab]
  refine ⟨u, hu, ?_⟩
  change
    (1 - t) • sectionPoint v p a + t • sectionPoint v p b =
      sectionPoint v p u
  rw [← AffineMap.lineMap_apply_module]
  exact lineMap_sectionPoint v p a b t

theorem hasDerivAt_transverseValue
    {G : Plane → Plane} {β : ℝ → Plane}
    (hβ : IsIntegralCurve β (fun _ y ↦ G y))
    (v p : Plane) (t : ℝ) :
    HasDerivAt (fun s ↦ transverseValue v p (β s))
      (transverseFunctional v (G (β t))) t := by
  have hsub :
      HasDerivAt (fun s ↦ β s - p) (G (β t)) t :=
    (hβ t).sub_const p
  simpa [transverseValue, Function.comp_def] using
    (transverseFunctional v).hasFDerivAt.comp_hasDerivAt t hsub

theorem exists_ball_velocityValue_pos
    {G : Plane → Plane} (hG : Continuous G) {p : Plane}
    (hp : G p ≠ 0) :
    ∃ r : ℝ, 0 < r ∧
      ∀ y ∈ ball p r, (1 / 2 : ℝ) < velocityValue G p y := by
  have hopen :
      Ioi (1 / 2 : ℝ) ∈ 𝓝 (velocityValue G p p) := by
    rw [velocityValue_self hp]
    exact Ioi_mem_nhds (by norm_num)
  have hevent :
      {y | (1 / 2 : ℝ) < velocityValue G p y} ∈ 𝓝 p :=
    (continuous_velocityValue hG p).continuousAt.eventually hopen
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hevent
  exact ⟨r, hr, fun y hy ↦ hball hy⟩

/-- Inside a sufficiently small regular flow box, time is strictly
increasing in the normalized longitudinal coordinate. -/
theorem strictMonoOn_transverseValue
    {G : Plane → Plane} {β : ℝ → Plane}
    (hβ : IsIntegralCurve β (fun _ y ↦ G y))
    {p : Plane} {r c d : ℝ}
    (hvel : ∀ y ∈ ball p r, (1 / 2 : ℝ) < velocityValue G p y)
    (hstay : ∀ t ∈ Icc c d, β t ∈ ball p r) :
    StrictMonoOn (fun t ↦ transverseValue (G p) p (β t)) (Icc c d) := by
  apply strictMonoOn_of_hasDerivWithinAt_pos (convex_Icc c d)
  · exact
      ((transverseFunctional (G p)).continuous.comp
        (hβ.continuous.sub continuous_const)).continuousOn
  · intro t _ht
    exact
      (hasDerivAt_transverseValue hβ (G p) p t).hasDerivWithinAt
  · intro t ht
    have ht' : t ∈ Icc c d := interior_subset ht
    exact (half_pos zero_lt_one).trans (hvel (β t) (hstay t ht'))

/-- Quantitative form of the preceding monotonicity statement. -/
theorem half_mul_sub_le_transverseValue_sub
    {G : Plane → Plane} {β : ℝ → Plane}
    (hβ : IsIntegralCurve β (fun _ y ↦ G y))
    {p : Plane} {r c d s t : ℝ}
    (hvel : ∀ y ∈ ball p r, (1 / 2 : ℝ) < velocityValue G p y)
    (hstay : ∀ u ∈ Icc c d, β u ∈ ball p r)
    (hs : s ∈ Icc c d) (ht : t ∈ Icc c d) (hst : s ≤ t) :
    (1 / 2 : ℝ) * (t - s) ≤
      transverseValue (G p) p (β t) -
        transverseValue (G p) p (β s) := by
  let f : ℝ → ℝ := fun u ↦ transverseValue (G p) p (β u)
  have hfcont : ContinuousOn f (Icc c d) := by
    exact
      ((transverseFunctional (G p)).continuous.comp
        (hβ.continuous.sub continuous_const)).continuousOn
  have hfdiff : DifferentiableOn ℝ f (interior (Icc c d)) := by
    intro u _hu
    exact
      (hasDerivAt_transverseValue hβ (G p) p u).differentiableAt
        |>.differentiableWithinAt
  have hfderiv :
      ∀ u ∈ interior (Icc c d), (1 / 2 : ℝ) ≤ deriv f u := by
    intro u hu
    rw [(hasDerivAt_transverseValue hβ (G p) p u).deriv]
    exact (hvel (β u) (hstay u (interior_subset hu))).le
  exact
    (convex_Icc c d).mul_sub_le_image_sub_of_le_deriv
      hfcont hfdiff hfderiv s hs t ht hst

end

end Submission.Transversal
