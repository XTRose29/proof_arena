import Submission.AlgebraicPhase
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff

open Complex

namespace Submission.PeripheralTube

noncomputable section

abbrev CSphere := Milnor.CSphere
abbrev Binding := {q : CSphere // Milnor.polynomial q = 0}

def normalize (z : ℂ) (hz : z ≠ 0) : Circle :=
  ⟨z / ‖z‖, by simp [Submonoid.unitSphere, hz]⟩

@[simp] theorem normalize_coe (z : ℂ) (hz : z ≠ 0) :
    (normalize z hz : ℂ) = z / ‖z‖ :=
  rfl

theorem binding_normSq (q : Binding) :
    normSq q.1.1.1 = 9 / 25 ∧ normSq q.1.1.2 = 16 / 25 :=
  AlgebraicTrefoil.normSq_eq_of_polynomial_zero q.1.2 q.2

theorem binding_z_ne (q : Binding) : q.1.1.1 ≠ 0 := by
  intro h
  have hz := (binding_normSq q).1
  rw [h, map_zero] at hz
  norm_num at hz

theorem binding_w_ne (q : Binding) : q.1.1.2 ≠ 0 := by
  intro h
  have hw := (binding_normSq q).2
  rw [h, map_zero] at hw
  norm_num at hw

def bindingZPhase (q : Binding) : Circle :=
  normalize q.1.1.1 (binding_z_ne q)

def bindingWPhase (q : Binding) : Circle :=
  normalize (-q.1.1.2) (neg_ne_zero.mpr (binding_w_ne q))

def bindingParameter (q : Binding) : Circle :=
  bindingZPhase q / bindingWPhase q

def bindingPoint (u : Circle) : Binding :=
  ⟨⟨(((3 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 3,
      ((-4 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 2), by
        rw [normSq_mul, normSq_mul, normSq_ofReal, normSq_ofReal]
        simp [Submonoid.unitSphere]
        norm_num⟩, by
    change 64 * (((3 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 3) ^ 2 +
        45 * (((-4 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 2) ^ 3 = 0
    norm_num
    ring⟩

@[simp] theorem bindingPoint_z (u : Circle) :
    (bindingPoint u).1.1.1 = ((3 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 3 :=
  rfl

@[simp] theorem bindingPoint_w (u : Circle) :
    (bindingPoint u).1.1.2 = ((-4 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 2 :=
  rfl

@[simp] theorem bindingZPhase_bindingPoint (u : Circle) :
    bindingZPhase (bindingPoint u) = u ^ 3 := by
  apply Subtype.ext
  change (((3 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 3) /
      ‖((3 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 3‖ = (u : ℂ) ^ 3
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 3 / 5),
    norm_pow, Circle.norm_coe, one_pow]
  norm_num

@[simp] theorem bindingWPhase_bindingPoint (u : Circle) :
    bindingWPhase (bindingPoint u) = u ^ 2 := by
  apply Subtype.ext
  change (-((( -4 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 2)) /
      ‖-((( -4 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 2)‖ = (u : ℂ) ^ 2
  rw [show -((( -4 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 2) =
    ((4 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 2 by push_cast; ring]
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (by norm_num : (0 : ℝ) < 4 / 5), norm_pow,
    Circle.norm_coe, one_pow]
  norm_num

@[simp] theorem bindingParameter_bindingPoint (u : Circle) :
    bindingParameter (bindingPoint u) = u := by
  rw [bindingParameter, bindingZPhase_bindingPoint, bindingWPhase_bindingPoint]
  apply Subtype.ext
  change (u : ℂ) ^ 3 / (u : ℂ) ^ 2 = (u : ℂ)
  have hu : (u : ℂ) ≠ 0 := Circle.coe_ne_zero u
  field_simp

theorem binding_z_eq_phase (q : Binding) :
    q.1.1.1 = ((3 / 5 : ℝ) : ℂ) * bindingZPhase q := by
  change q.1.1.1 = ((3 / 5 : ℝ) : ℂ) *
    (q.1.1.1 / ‖q.1.1.1‖)
  have hnormSq := (binding_normSq q).1
  have hnorm : ‖q.1.1.1‖ = 3 / 5 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 3 / 5)]
    rw [← normSq_eq_norm_sq, hnormSq]
    norm_num
  rw [hnorm]
  field_simp

theorem binding_w_eq_phase (q : Binding) :
    q.1.1.2 = ((-4 / 5 : ℝ) : ℂ) * bindingWPhase q := by
  change q.1.1.2 = ((-4 / 5 : ℝ) : ℂ) *
    (-q.1.1.2 / ‖-q.1.1.2‖)
  have hnormSq := (binding_normSq q).2
  have hnorm : ‖q.1.1.2‖ = 4 / 5 := by
    rw [← sq_eq_sq₀ (norm_nonneg _) (by norm_num : (0 : ℝ) ≤ 4 / 5)]
    rw [← normSq_eq_norm_sq, hnormSq]
    norm_num
  rw [norm_neg, hnorm]
  field_simp
  push_cast
  ring

theorem binding_phase_relation (q : Binding) :
    bindingZPhase q ^ 2 = bindingWPhase q ^ 3 := by
  apply Subtype.ext
  have hzero := q.2
  rw [Milnor.polynomial, binding_z_eq_phase, binding_w_eq_phase] at hzero
  change 64 * (((3 / 5 : ℝ) : ℂ) * (bindingZPhase q : ℂ)) ^ 2 +
      45 * (((-4 / 5 : ℝ) : ℂ) * (bindingWPhase q : ℂ)) ^ 3 = 0 at hzero
  change (bindingZPhase q : ℂ) ^ 2 = (bindingWPhase q : ℂ) ^ 3
  norm_num at hzero ⊢
  linear_combination (25 / 576 : ℂ) * hzero

theorem bindingParameter_sq (q : Binding) :
    bindingParameter q ^ 2 = bindingWPhase q := by
  apply Subtype.ext
  change ((bindingZPhase q : ℂ) / (bindingWPhase q : ℂ)) ^ 2 =
    (bindingWPhase q : ℂ)
  have hw : (bindingWPhase q : ℂ) ≠ 0 := Circle.coe_ne_zero _
  field_simp
  simpa [pow_succ] using congrArg Subtype.val (binding_phase_relation q)

theorem bindingParameter_cube (q : Binding) :
    bindingParameter q ^ 3 = bindingZPhase q := by
  calc
    bindingParameter q ^ 3 = bindingParameter q * bindingParameter q ^ 2 := by
      rw [pow_succ']
    _ = bindingParameter q * bindingWPhase q := by rw [bindingParameter_sq]
    _ = bindingZPhase q := by
      apply Subtype.ext
      change ((bindingZPhase q : ℂ) / (bindingWPhase q : ℂ)) *
          (bindingWPhase q : ℂ) = (bindingZPhase q : ℂ)
      exact div_mul_cancel₀ _ (Circle.coe_ne_zero _)

@[simp] theorem bindingPoint_bindingParameter (q : Binding) :
    bindingPoint (bindingParameter q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change ((3 / 5 : ℝ) : ℂ) * (bindingParameter q : ℂ) ^ 3 = q.1.1.1
    rw [show (bindingParameter q : ℂ) ^ 3 = (bindingZPhase q : ℂ) by
      exact congrArg Subtype.val (bindingParameter_cube q)]
    exact (binding_z_eq_phase q).symm
  · change ((-4 / 5 : ℝ) : ℂ) * (bindingParameter q : ℂ) ^ 2 = q.1.1.2
    rw [show (bindingParameter q : ℂ) ^ 2 = (bindingWPhase q : ℂ) by
      exact congrArg Subtype.val (bindingParameter_sq q)]
    exact (binding_w_eq_phase q).symm

theorem bindingZPhase_continuous : Continuous bindingZPhase := by
  apply Continuous.subtype_mk
  have hz : Continuous (fun q : Binding => q.1.1.1) := by fun_prop
  exact hz.div (Complex.continuous_ofReal.comp hz.norm) (fun q =>
    ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (binding_z_ne q)))

theorem bindingWPhase_continuous : Continuous bindingWPhase := by
  apply Continuous.subtype_mk
  have hw : Continuous (fun q : Binding => -q.1.1.2) := by fun_prop
  exact hw.div (Complex.continuous_ofReal.comp hw.norm) (fun q =>
    ofReal_ne_zero.mpr
      (norm_ne_zero_iff.mpr (neg_ne_zero.mpr (binding_w_ne q))))

theorem bindingParameter_continuous : Continuous bindingParameter := by
  exact bindingZPhase_continuous.mul bindingWPhase_continuous.inv

theorem bindingPoint_continuous : Continuous bindingPoint := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  exact (continuous_const.mul
    ((continuous_subtype_val : Continuous fun u : Circle => (u : ℂ)).pow 3)).prodMk
      (continuous_const.mul
        ((continuous_subtype_val : Continuous fun u : Circle => (u : ℂ)).pow 2))

def bindingHomeomorph : Binding ≃ₜ Circle where
  toFun := bindingParameter
  invFun := bindingPoint
  left_inv := bindingPoint_bindingParameter
  right_inv := bindingParameter_bindingPoint
  continuous_toFun := bindingParameter_continuous
  continuous_invFun := bindingPoint_continuous

abbrev OpenUnit := Set.Ioo (0 : ℝ) 1
abbrev TorusRegion := {q : CSphere // q.1.1 ≠ 0 ∧ q.1.2 ≠ 0}
abbrev TorusCoordinates := OpenUnit × Circle × Circle

def zPhase (q : TorusRegion) : Circle :=
  normalize q.1.1.1 q.2.1

def wPhase (q : TorusRegion) : Circle :=
  normalize (-q.1.1.2) (neg_ne_zero.mpr q.2.2)

def longitude (q : TorusRegion) : Circle :=
  zPhase q / wPhase q

def normalPhase (q : TorusRegion) : Circle :=
  zPhase q ^ 2 / wPhase q ^ 3

def radial (q : TorusRegion) : OpenUnit :=
  ⟨normSq q.1.1.2, normSq_pos.mpr q.2.2, by
    have hz : 0 < normSq q.1.1.1 := normSq_pos.mpr q.2.1
    linarith [q.1.2]⟩

def torusCoordinates (q : TorusRegion) : TorusCoordinates :=
  (radial q, longitude q, normalPhase q)

def coordinateZPhase (x : TorusCoordinates) : Circle :=
  x.2.1 ^ 3 / x.2.2

def coordinateWPhase (x : TorusCoordinates) : Circle :=
  x.2.1 ^ 2 / x.2.2

@[simp] theorem coordinateZPhase_coe (x : TorusCoordinates) :
    (coordinateZPhase x : ℂ) = (x.2.1 : ℂ) ^ 3 / (x.2.2 : ℂ) :=
  rfl

@[simp] theorem coordinateWPhase_coe (x : TorusCoordinates) :
    (coordinateWPhase x : ℂ) = (x.2.1 : ℂ) ^ 2 / (x.2.2 : ℂ) :=
  rfl

def torusPoint (x : TorusCoordinates) : TorusRegion :=
  ⟨⟨(((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) * coordinateZPhase x,
      -(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) * coordinateWPhase x)), by
        rw [normSq_mul, normSq_neg, normSq_mul, normSq_ofReal, normSq_ofReal]
        rw [normSq_eq_norm_sq, normSq_eq_norm_sq, Circle.norm_coe,
          Circle.norm_coe]
        have hz := Real.sq_sqrt (sub_nonneg.mpr x.1.2.2.le)
        have hw := Real.sq_sqrt x.1.2.1.le
        nlinarith⟩, by
    constructor
    · exact mul_ne_zero
        (ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr x.1.2.2))))
        (Circle.coe_ne_zero _)
    · exact neg_ne_zero.mpr (mul_ne_zero
        (ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 x.1.2.1)))
        (Circle.coe_ne_zero _))⟩

@[simp] theorem radial_torusPoint (x : TorusCoordinates) :
    radial (torusPoint x) = x.1 := by
  apply Subtype.ext
  change normSq (-(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) * coordinateWPhase x)) = x.1
  rw [normSq_neg, normSq_mul, normSq_ofReal, normSq_eq_norm_sq,
    Circle.norm_coe]
  simpa [pow_two] using Real.sq_sqrt x.1.2.1.le

@[simp] theorem zPhase_torusPoint (x : TorusCoordinates) :
    zPhase (torusPoint x) = coordinateZPhase x := by
  apply Subtype.ext
  change (((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) * coordinateZPhase x) /
      ‖((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) * coordinateZPhase x‖ =
        coordinateZPhase x
  rw [norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 (sub_pos.mpr x.1.2.2)), Circle.norm_coe]
  field_simp [ofReal_ne_zero.mpr
    (ne_of_gt (Real.sqrt_pos.2 (sub_pos.mpr x.1.2.2)))]

@[simp] theorem wPhase_torusPoint (x : TorusCoordinates) :
    wPhase (torusPoint x) = coordinateWPhase x := by
  apply Subtype.ext
  change (-(-(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) * coordinateWPhase x))) /
      ‖-(-(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) * coordinateWPhase x))‖ =
        coordinateWPhase x
  rw [neg_neg, norm_mul, norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.sqrt_pos.2 x.1.2.1), Circle.norm_coe]
  field_simp [ofReal_ne_zero.mpr (ne_of_gt (Real.sqrt_pos.2 x.1.2.1))]

@[simp] theorem longitude_torusPoint (x : TorusCoordinates) :
    longitude (torusPoint x) = x.2.1 := by
  rw [longitude, zPhase_torusPoint, wPhase_torusPoint,
    coordinateZPhase, coordinateWPhase]
  apply Subtype.ext
  change (((x.2.1 : ℂ) ^ 3 / x.2.2) /
      ((x.2.1 : ℂ) ^ 2 / x.2.2)) = x.2.1
  field_simp [Circle.coe_ne_zero]

@[simp] theorem normalPhase_torusPoint (x : TorusCoordinates) :
    normalPhase (torusPoint x) = x.2.2 := by
  rw [normalPhase, zPhase_torusPoint, wPhase_torusPoint,
    coordinateZPhase, coordinateWPhase]
  apply Subtype.ext
  change ((((x.2.1 : ℂ) ^ 3 / x.2.2) ^ 2) /
      (((x.2.1 : ℂ) ^ 2 / x.2.2) ^ 3)) = x.2.2
  field_simp [Circle.coe_ne_zero]

@[simp] theorem torusCoordinates_torusPoint (x : TorusCoordinates) :
    torusCoordinates (torusPoint x) = x := by
  apply Prod.ext
  · exact radial_torusPoint x
  · apply Prod.ext
    · exact longitude_torusPoint x
    · exact normalPhase_torusPoint x

theorem z_eq_norm_mul_zPhase (q : TorusRegion) :
    q.1.1.1 = ((‖q.1.1.1‖ : ℝ) : ℂ) * zPhase q := by
  change q.1.1.1 = ((‖q.1.1.1‖ : ℝ) : ℂ) *
    (q.1.1.1 / ‖q.1.1.1‖)
  field_simp [norm_ne_zero_iff.mpr q.2.1]

theorem w_eq_neg_norm_mul_wPhase (q : TorusRegion) :
    q.1.1.2 = -(((‖q.1.1.2‖ : ℝ) : ℂ) * wPhase q) := by
  change q.1.1.2 = -(((‖q.1.1.2‖ : ℝ) : ℂ) *
    (-q.1.1.2 / ‖-q.1.1.2‖))
  rw [norm_neg]
  field_simp [norm_ne_zero_iff.mpr q.2.2]

theorem norm_z_eq_sqrt_one_sub_radial (q : TorusRegion) :
    ‖q.1.1.1‖ = Real.sqrt (1 - (radial q : ℝ)) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
    ← normSq_eq_norm_sq, Real.sq_sqrt]
  · dsimp [radial]
    linarith [q.1.2]
  · exact sub_nonneg.mpr (radial q).2.2.le

theorem norm_w_eq_sqrt_radial (q : TorusRegion) :
    ‖q.1.1.2‖ = Real.sqrt (radial q : ℝ) := by
  rw [← sq_eq_sq₀ (norm_nonneg _) (Real.sqrt_nonneg _),
    ← normSq_eq_norm_sq, Real.sq_sqrt (radial q).2.1.le]
  rfl

theorem coordinateZPhase_torusCoordinates (q : TorusRegion) :
    coordinateZPhase (torusCoordinates q) = zPhase q := by
  rw [coordinateZPhase, torusCoordinates, longitude, normalPhase]
  apply Subtype.ext
  change (((zPhase q : ℂ) / wPhase q) ^ 3) /
      (((zPhase q : ℂ) ^ 2) / (wPhase q : ℂ) ^ 3) = zPhase q
  field_simp [Circle.coe_ne_zero]

theorem coordinateWPhase_torusCoordinates (q : TorusRegion) :
    coordinateWPhase (torusCoordinates q) = wPhase q := by
  rw [coordinateWPhase, torusCoordinates, longitude, normalPhase]
  apply Subtype.ext
  change (((zPhase q : ℂ) / wPhase q) ^ 2) /
      (((zPhase q : ℂ) ^ 2) / (wPhase q : ℂ) ^ 3) = wPhase q
  field_simp [Circle.coe_ne_zero]

@[simp] theorem torusPoint_torusCoordinates (q : TorusRegion) :
    torusPoint (torusCoordinates q) = q := by
  apply Subtype.ext
  apply Subtype.ext
  apply Prod.ext
  · change ((Real.sqrt (1 - (radial q : ℝ)) : ℝ) : ℂ) *
      coordinateZPhase (torusCoordinates q) = q.1.1.1
    rw [coordinateZPhase_torusCoordinates, ← norm_z_eq_sqrt_one_sub_radial,
      ← z_eq_norm_mul_zPhase]
  · change -(((Real.sqrt (radial q : ℝ) : ℝ) : ℂ) *
      coordinateWPhase (torusCoordinates q)) = q.1.1.2
    rw [coordinateWPhase_torusCoordinates, ← norm_w_eq_sqrt_radial,
      ← w_eq_neg_norm_mul_wPhase]

theorem zPhase_continuous : Continuous zPhase := by
  apply Continuous.subtype_mk
  have hz : Continuous (fun q : TorusRegion => q.1.1.1) := by fun_prop
  exact hz.div (Complex.continuous_ofReal.comp hz.norm) (fun q =>
    ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr q.2.1))

theorem wPhase_continuous : Continuous wPhase := by
  apply Continuous.subtype_mk
  have hw : Continuous (fun q : TorusRegion => -q.1.1.2) := by fun_prop
  exact hw.div (Complex.continuous_ofReal.comp hw.norm) (fun q =>
    ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr (neg_ne_zero.mpr q.2.2)))

theorem radial_continuous : Continuous radial := by
  apply Continuous.subtype_mk
  exact Complex.continuous_normSq.comp (by fun_prop)

theorem coordinateZPhase_continuous : Continuous coordinateZPhase := by
  have hu : Continuous (fun x : TorusCoordinates => x.2.1) :=
    continuous_fst.comp continuous_snd
  have hv : Continuous (fun x : TorusCoordinates => x.2.2) :=
    continuous_snd.comp continuous_snd
  exact (hu.pow 3).mul hv.inv

theorem coordinateWPhase_continuous : Continuous coordinateWPhase := by
  have hu : Continuous (fun x : TorusCoordinates => x.2.1) :=
    continuous_fst.comp continuous_snd
  have hv : Continuous (fun x : TorusCoordinates => x.2.2) :=
    continuous_snd.comp continuous_snd
  exact (hu.pow 2).mul hv.inv

theorem torusCoordinates_continuous : Continuous torusCoordinates := by
  exact radial_continuous.prodMk
    ((zPhase_continuous.mul wPhase_continuous.inv).prodMk
      ((zPhase_continuous.pow 2).mul (wPhase_continuous.pow 3).inv))

theorem torusPoint_continuous : Continuous torusPoint := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  have hr : Continuous (fun x : TorusCoordinates => (x.1 : ℝ)) := by fun_prop
  have hzScalar : Continuous (fun x : TorusCoordinates =>
      ((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ)) := by fun_prop
  have hwScalar : Continuous (fun x : TorusCoordinates =>
      ((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ)) := by fun_prop
  exact (hzScalar.mul
    (continuous_subtype_val.comp coordinateZPhase_continuous)).prodMk
      (hwScalar.mul
        (continuous_subtype_val.comp coordinateWPhase_continuous)).neg

def torusHomeomorph : TorusRegion ≃ₜ TorusCoordinates where
  toFun := torusCoordinates
  invFun := torusPoint
  left_inv := torusPoint_torusCoordinates
  right_inv := torusCoordinates_torusPoint
  continuous_toFun := torusCoordinates_continuous
  continuous_invFun := torusPoint_continuous

def bindingRadial : ℝ := 16 / 25

def normalFactor (x : TorusCoordinates) : ℂ :=
  Complex.I *
    (((16 * (1 - (x.1 : ℝ)) : ℝ) : ℂ) * (x.2.2 : ℂ) -
      ((9 * (x.1 : ℝ) : ℝ) : ℂ)) / (x.2.2 : ℂ) ^ 3

theorem radialCube_neg_circle (u : Circle) :
    RadialMilnor.radialCube (-(u : ℂ)) = -(u : ℂ) ^ 3 := by
  rw [RadialMilnor.radialCube_of_ne (neg_ne_zero.mpr (Circle.coe_ne_zero u)),
    norm_neg, Circle.norm_coe]
  simp only [ofReal_one]
  ring

theorem radialCube_torusPoint (x : TorusCoordinates) :
    RadialMilnor.radialCube (torusPoint x).1.1.2 =
      -((x.1 : ℝ) : ℂ) * (coordinateWPhase x : ℂ) ^ 3 := by
  change RadialMilnor.radialCube
      (-(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) * coordinateWPhase x)) = _
  rw [show -(((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) * coordinateWPhase x) =
      (((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) * -(coordinateWPhase x : ℂ)) by ring,
    RadialMilnor.radialCube_smul_of_nonneg (Real.sqrt (x.1 : ℝ))
      (Real.sqrt_nonneg _) (-(coordinateWPhase x : ℂ)),
    radialCube_neg_circle]
  have hsqrt := Real.sq_sqrt x.1.2.1.le
  have hsqrtComplex : (((Real.sqrt (x.1 : ℝ) : ℝ) : ℂ) ^ 2) =
      ((x.1 : ℝ) : ℂ) := by
    exact_mod_cast hsqrt
  rw [hsqrtComplex]
  ring

theorem polynomial_torusPoint (x : TorusCoordinates) :
    RadialMilnor.polynomial (torusPoint x).1 =
      (x.2.1 : ℂ) ^ 6 * normalFactor x := by
  rw [RadialMilnor.polynomial, RadialMilnor.basePolynomial]
  change Complex.I *
      (16 * ((((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) *
          coordinateZPhase x) ^ 2) +
        9 * RadialMilnor.radialCube (torusPoint x).1.1.2) = _
  rw [radialCube_torusPoint, mul_pow]
  have hsqrt := Real.sq_sqrt (sub_nonneg.mpr x.1.2.2.le)
  have hsqrtComplex : (((Real.sqrt (1 - (x.1 : ℝ)) : ℝ) : ℂ) ^ 2) =
      ((1 - (x.1 : ℝ) : ℝ) : ℂ) := by
    exact_mod_cast hsqrt
  have hv : (x.2.2 : ℂ) ≠ 0 := Circle.coe_ne_zero x.2.2
  rw [coordinateZPhase_coe, coordinateWPhase_coe]
  unfold normalFactor
  rw [hsqrtComplex]
  field_simp [hv]
  push_cast
  ring

@[simp] theorem normalFactor_binding (u : Circle) :
    normalFactor
      (⟨bindingRadial, by norm_num [bindingRadial]⟩, u, 1) = 0 := by
  simp [normalFactor, bindingRadial]
  ring

theorem normalFactor_continuous : Continuous normalFactor := by
  unfold normalFactor
  have hnum : Continuous (fun x : TorusCoordinates =>
      (((16 * (1 - (x.1 : ℝ)) : ℝ) : ℂ) * (x.2.2 : ℂ) -
        ((9 * (x.1 : ℝ) : ℝ) : ℂ))) := by
    fun_prop
  have hden : Continuous (fun x : TorusCoordinates => (x.2.2 : ℂ) ^ 3) := by
    fun_prop
  exact (continuous_const.mul hnum).div hden fun x =>
    pow_ne_zero 3 (Circle.coe_ne_zero x.2.2)

abbrev NormalPlane := EuclideanSpace ℝ (Fin 2)

def normalA (p : NormalPlane) : ℝ :=
  16 * (1 - (bindingRadial + p.ofLp 0)) * Real.cos (p.ofLp 1) -
    9 * (bindingRadial + p.ofLp 0)

def normalB (p : NormalPlane) : ℝ :=
  16 * (1 - (bindingRadial + p.ofLp 0)) * Real.sin (p.ofLp 1)

def normalModelReal (p : NormalPlane) : NormalPlane :=
  WithLp.toLp 2 ![
    normalA p * Real.sin (3 * p.ofLp 1) -
      normalB p * Real.cos (3 * p.ofLp 1),
    normalA p * Real.cos (3 * p.ofLp 1) +
      normalB p * Real.sin (3 * p.ofLp 1)]

def normalLinearEquiv : NormalPlane ≃L[ℝ] NormalPlane where
  toLinearEquiv :=
    { toFun := fun p =>
        WithLp.toLp 2 ![-144 / 25 * p.ofLp 1, -25 * p.ofLp 0]
      invFun := fun z =>
        WithLp.toLp 2 ![-z.ofLp 1 / 25, -25 * z.ofLp 0 / 144]
      map_add' := by
        intro x y
        ext i
        fin_cases i <;> simp <;> ring
      map_smul' := by
        intro c x
        ext i
        fin_cases i <;> simp <;> ring
      left_inv := by
        intro x
        ext i
        fin_cases i
        · simp
        · simp
          ring
      right_inv := by
        intro z
        ext i
        fin_cases i
        · simp
          ring
        · simp
          ring }
  continuous_toFun := by
    apply (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 2 => ℝ)).symm.continuous.comp
    fun_prop
  continuous_invFun := by
    apply (PiLp.continuousLinearEquiv 2 ℝ
      (fun _ : Fin 2 => ℝ)).symm.continuous.comp
    fun_prop

def pairToNormalPlane : (ℝ × ℝ) ≃L[ℝ] NormalPlane :=
  (ContinuousLinearEquiv.finTwoArrow ℝ ℝ).symm |>.trans
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : Fin 2 => ℝ)).symm

theorem normalModelReal_hasFDerivAt_zero :
    HasFDerivAt normalModelReal
      (normalLinearEquiv : NormalPlane →L[ℝ] NormalPlane) 0 := by
  have ha : HasFDerivAt (fun p : NormalPlane => p.ofLp (0 : Fin 2))
      (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)) 0 :=
    by simpa using (EuclideanSpace.proj (𝕜 := ℝ) (0 : Fin 2)).hasFDerivAt
  have hb : HasFDerivAt (fun p : NormalPlane => p.ofLp (1 : Fin 2))
      (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)) 0 :=
    by simpa using (EuclideanSpace.proj (𝕜 := ℝ) (1 : Fin 2)).hasFDerivAt
  have hr := ha.const_add bindingRadial
  have honeSub :=
    (hasFDerivAt_const (x := (0 : NormalPlane)) (c := (1 : ℝ))).sub hr
  have hcos := (Real.hasDerivAt_cos 0).comp_hasFDerivAt 0 hb
  have hsin := (Real.hasDerivAt_sin 0).comp_hasFDerivAt 0 hb
  have hA := ((honeSub.const_mul 16).mul hcos).sub (hr.const_mul 9)
  have hB := (honeSub.const_mul 16).mul hsin
  change HasFDerivAt normalA _ 0 at hA
  change HasFDerivAt normalB _ 0 at hB
  have hcosThree : HasFDerivAt
      (fun p : NormalPlane => Real.cos (3 * p.ofLp 1))
      (fderiv ℝ (fun p : NormalPlane => Real.cos (3 * p.ofLp 1)) 0) 0 :=
    (by fun_prop : DifferentiableAt ℝ
      (fun p : NormalPlane => Real.cos (3 * p.ofLp 1)) 0).hasFDerivAt
  have hsinThree : HasFDerivAt
      (fun p : NormalPlane => Real.sin (3 * p.ofLp 1))
      (fderiv ℝ (fun p : NormalPlane => Real.sin (3 * p.ofLp 1)) 0) 0 :=
    (by fun_prop : DifferentiableAt ℝ
      (fun p : NormalPlane => Real.sin (3 * p.ofLp 1)) 0).hasFDerivAt
  have hre := (hA.mul hsinThree).sub (hB.mul hcosThree)
  have him := (hA.mul hcosThree).add (hB.mul hsinThree)
  change HasFDerivAt (fun p =>
      normalA p * Real.sin (3 * p.ofLp 1) -
        normalB p * Real.cos (3 * p.ofLp 1)) _ 0 at hre
  change HasFDerivAt (fun p =>
      normalA p * Real.cos (3 * p.ofLp 1) +
        normalB p * Real.sin (3 * p.ofLp 1)) _ 0 at him
  have hpair := hre.prodMk him
  have htoLp := pairToNormalPlane.hasFDerivAt.comp 0 hpair
  change HasFDerivAt normalModelReal _ 0 at htoLp
  apply htoLp.congr_fderiv
  ext p i
  fin_cases i <;>
    simp [normalLinearEquiv, normalA, normalB, bindingRadial,
      pairToNormalPlane, EuclideanSpace.proj,
      ContinuousLinearMap.prod_apply] <;>
    ring

theorem normalModelReal_contDiff :
    ContDiff ℝ (⊤ : ℕ∞) normalModelReal := by
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.contDiff.comp
  apply contDiff_pi.mpr
  intro i
  fin_cases i <;>
    simp [normalA, normalB, bindingRadial] <;>
    fun_prop

def normalChart : OpenPartialHomeomorph NormalPlane NormalPlane :=
  normalModelReal_contDiff.contDiffAt.toOpenPartialHomeomorph normalModelReal
    normalModelReal_hasFDerivAt_zero (by simp)

theorem normalModelReal_zero : normalModelReal 0 = 0 := by
  ext i
  fin_cases i <;>
    norm_num [normalModelReal, normalA, normalB, bindingRadial]

theorem zero_mem_normalChart_source : (0 : NormalPlane) ∈ normalChart.source :=
  normalModelReal_contDiff.contDiffAt.mem_toOpenPartialHomeomorph_source
    normalModelReal_hasFDerivAt_zero (by simp)

theorem zero_mem_normalChart_target : (0 : NormalPlane) ∈ normalChart.target := by
  rw [← normalModelReal_zero]
  exact normalChart.map_source zero_mem_normalChart_source

def normalComplex (p : NormalPlane) : ℂ :=
  ⟨(normalModelReal p).ofLp 0, (normalModelReal p).ofLp 1⟩

def normalRadial (p : NormalPlane)
    (h0 : 0 < bindingRadial + p.ofLp 0)
    (h1 : bindingRadial + p.ofLp 0 < 1) : OpenUnit :=
  ⟨bindingRadial + p.ofLp 0, h0, h1⟩

theorem normalProduct_re (a b c s : ℝ) :
    (I * ((a : ℂ) + (b : ℂ) * I) * ((c : ℂ) - (s : ℂ) * I)).re =
      a * s - b * c := by
  norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_sq]
  ring

theorem normalProduct_im (a b c s : ℝ) :
    (I * ((a : ℂ) + (b : ℂ) * I) * ((c : ℂ) - (s : ℂ) * I)).im =
      a * c + b * s := by
  norm_num [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_sq]
  ring

theorem normalFactor_normalRadial (p : NormalPlane)
    (h0 : 0 < bindingRadial + p.ofLp 0)
    (h1 : bindingRadial + p.ofLp 0 < 1) (u : Circle) :
    normalFactor (normalRadial p h0 h1, u, Circle.exp (p.ofLp 1)) =
      normalComplex p := by
  have hunit : Complex.exp (((p.ofLp 1 : ℝ) : ℂ) * I) =
      (Real.cos (p.ofLp 1) : ℂ) + (Real.sin (p.ofLp 1) : ℂ) * I :=
    Complex.exp_ofReal_mul_I (p.ofLp 1)
  have hnumerator :
      (((16 * (1 - (bindingRadial + p.ofLp 0)) : ℝ) : ℂ) *
          Complex.exp (((p.ofLp 1 : ℝ) : ℂ) * I) -
        ((9 * (bindingRadial + p.ofLp 0) : ℝ) : ℂ)) =
        (normalA p : ℂ) + (normalB p : ℂ) * I := by
    rw [hunit]
    apply Complex.ext
    · simp [normalA, normalB, Complex.mul_re]
    · simp [normalA, normalB, Complex.mul_im]
  have hexpThree :
      Complex.exp (((p.ofLp 1 : ℝ) : ℂ) * I) ^ 3 =
        Complex.exp ((((3 * p.ofLp 1 : ℝ) : ℂ) * I)) := by
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [normalFactor, normalRadial]
  rw [Circle.coe_exp]
  rw [hnumerator, hexpThree, div_eq_mul_inv, ← Complex.exp_neg]
  have hnegArg :
      -(((3 * p.ofLp 1 : ℝ) : ℂ) * I) =
        (((-(3 * p.ofLp 1) : ℝ) : ℂ) * I) := by
    push_cast
    ring
  have hnegExp :
      Complex.exp (-(((3 * p.ofLp 1 : ℝ) : ℂ) * I)) =
        (Real.cos (3 * p.ofLp 1) : ℂ) -
          (Real.sin (3 * p.ofLp 1) : ℂ) * I := by
    rw [hnegArg, Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  rw [hnegExp]
  apply Complex.ext
  · change
      ((I * ((normalA p : ℂ) + (normalB p : ℂ) * I)) *
        ((Real.cos (3 * p.ofLp 1) : ℂ) -
          (Real.sin (3 * p.ofLp 1) : ℂ) * I)).re =
        normalA p * Real.sin (3 * p.ofLp 1) -
          normalB p * Real.cos (3 * p.ofLp 1)
    exact normalProduct_re _ _ _ _
  · change
      ((I * ((normalA p : ℂ) + (normalB p : ℂ) * I)) *
        ((Real.cos (3 * p.ofLp 1) : ℂ) -
          (Real.sin (3 * p.ofLp 1) : ℂ) * I)).im =
        normalA p * Real.cos (3 * p.ofLp 1) +
          normalB p * Real.sin (3 * p.ofLp 1)
    exact normalProduct_im _ _ _ _

theorem exists_normalTargetRadius :
    ∃ ε : ℝ, 0 < ε ∧ ∀ y : NormalPlane, ‖y‖ < ε →
      y ∈ normalChart.target ∧ ‖normalChart.symm y‖ < 1 / 4 := by
  obtain ⟨εTarget, hεTarget, htarget⟩ :=
    Metric.isOpen_iff.mp normalChart.open_target 0 zero_mem_normalChart_target
  have hcont := normalChart.continuousAt_symm zero_mem_normalChart_target
  rw [Metric.continuousAt_iff] at hcont
  obtain ⟨εInv, hεInv, hinv⟩ := hcont (1 / 4) (by norm_num)
  refine ⟨min εTarget εInv, lt_min hεTarget hεInv, ?_⟩
  intro y hy
  have hyTarget : y ∈ normalChart.target := by
    apply htarget
    simpa [Metric.mem_ball, dist_zero_right] using
      lt_of_lt_of_le hy (min_le_left _ _)
  have hyInv := hinv (by
    simpa [dist_zero_right] using lt_of_lt_of_le hy (min_le_right _ _))
  have hsymmZero : normalChart.symm (0 : NormalPlane) = 0 := by
    calc
      normalChart.symm (0 : NormalPlane) = normalChart.symm (normalModelReal 0) :=
        congrArg normalChart.symm normalModelReal_zero.symm
      _ = 0 := normalChart.left_inv zero_mem_normalChart_source
  rw [hsymmZero, dist_zero_right] at hyInv
  exact ⟨hyTarget, hyInv⟩

theorem normalInverse_radial_bounds {y : NormalPlane}
    (hy : ‖normalChart.symm y‖ < 1 / 4) :
    0 < bindingRadial + (normalChart.symm y).ofLp 0 ∧
      bindingRadial + (normalChart.symm y).ofLp 0 < 1 := by
  have hcoord : ‖(normalChart.symm y).ofLp 0‖ < 1 / 4 :=
    lt_of_le_of_lt (PiLp.norm_apply_le (normalChart.symm y) 0) hy
  rw [Real.norm_eq_abs] at hcoord
  constructor <;> dsimp [bindingRadial] <;>
    nlinarith [le_abs_self ((normalChart.symm y).ofLp 0),
      neg_le_abs ((normalChart.symm y).ofLp 0)]

theorem normalInverse_angle_bound {y : NormalPlane}
    (hy : ‖normalChart.symm y‖ < 1 / 4) :
    |(normalChart.symm y).ofLp 1| < 1 / 4 := by
  have hcoord : ‖(normalChart.symm y).ofLp 1‖ < 1 / 4 :=
    lt_of_le_of_lt (PiLp.norm_apply_le (normalChart.symm y) 1) hy
  simpa [Real.norm_eq_abs] using hcoord

end

end Submission.PeripheralTube
