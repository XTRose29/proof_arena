import Submission.DegreeAlgebra
import Submission.CoreMapAlgebra

open Complex
open scoped unitInterval

namespace Submission.AlgebraicPhase

noncomputable section

abbrev Complement := RadialPhase.Complement

def oldPhase : C(Complement, Circle) :=
  ⟨fun q => ⟨Milnor.polynomial q.1 / ‖Milnor.polynomial q.1‖, by
      simp [Submonoid.unitSphere, norm_ne_zero_iff.mpr q.2]⟩, by
    apply Continuous.subtype_mk
    have hpoly : Continuous (fun q : Complement => Milnor.polynomial q.1) := by
      unfold Milnor.polynomial
      fun_prop
    exact hpoly.div (Complex.continuous_ofReal.comp hpoly.norm) (fun q => by
      exact_mod_cast norm_ne_zero_iff.mpr q.2)⟩

@[simp] theorem oldPhase_coe (q : Complement) :
    (oldPhase q : ℂ) = Milnor.polynomial q.1 / ‖Milnor.polynomial q.1‖ :=
  rfl

def minusI : Circle := ⟨-Complex.I, by simp [Submonoid.unitSphere]⟩

def minusIMap : C(Complement, Circle) :=
  ContinuousMap.const Complement minusI

def minusILift : C(Complement, ℝ) :=
  ContinuousMap.const Complement (-(Real.pi / 2))

theorem exp_minusILift (q : Complement) :
    Circle.exp (minusILift q) = minusIMap q := by
  apply Subtype.ext
  change Complex.exp (((-(Real.pi / 2) : ℝ) : ℂ) * Complex.I) = -Complex.I
  have hcast : (((-(Real.pi / 2) : ℝ) : ℂ)) =
      -(Real.pi : ℂ) / 2 := by
    push_cast
    ring_nf
  rw [hcast]
  exact Complex.exp_neg_pi_div_two_mul_I

def basePhase : C(Complement, Circle) :=
  CircleMapAlgebra.mapMul minusIMap PhaseDegree.phaseMap

theorem degree_minusIMap : DeckDegree.degree minusIMap = 0 :=
  DegreeAlgebra.degree_eq_zero_of_global_lift minusIMap minusILift exp_minusILift

theorem degree_basePhase : DeckDegree.degree basePhase = 1 := by
  rw [basePhase, DegreeAlgebra.degree_mapMul, degree_minusIMap,
    PhaseDegree.degree_phase]
  norm_num

def coefficient (s : unitInterval) (w : ℂ) : ℝ :=
  1 - (s : ℝ) + (s : ℝ) * (5 * ‖w‖ / 4)

theorem coefficient_nonneg (s : unitInterval) (w : ℂ) :
    0 ≤ coefficient s w := by
  unfold coefficient
  exact add_nonneg (sub_nonneg.mpr s.2.2)
    (mul_nonneg s.2.1 (by positivity))

def interpolatedPolynomial (s : unitInterval) (q : Milnor.CSphere) : ℂ :=
  16 * q.1.1 ^ 2 +
    (coefficient s q.1.2 : ℂ) * (9 * RadialMilnor.radialCube q.1.2)

theorem interpolatedPolynomial_continuous :
    Continuous (fun x : unitInterval × Milnor.CSphere =>
      interpolatedPolynomial x.1 x.2) := by
  have hz : Continuous (fun x : unitInterval × Milnor.CSphere => x.2.1.1) := by
    fun_prop
  have hw : Continuous (fun x : unitInterval × Milnor.CSphere => x.2.1.2) := by
    fun_prop
  have hc : Continuous (fun x : unitInterval × Milnor.CSphere =>
      coefficient x.1 x.2.1.2) := by
    unfold coefficient
    fun_prop
  unfold interpolatedPolynomial
  exact (continuous_const.mul (hz.pow 2)).add
    ((Complex.continuous_ofReal.comp hc).mul
      (continuous_const.mul (RadialMilnor.radialCube_continuous.comp hw)))

theorem interpolatedPolynomial_ne_zero (s : unitInterval) (q : Complement) :
    interpolatedPolynomial s q.1 ≠ 0 := by
  intro hzero
  let r : ℝ := ‖q.1.1.2‖
  have hr0 : 0 ≤ r := norm_nonneg _
  have hrSq : r ^ 2 = normSq q.1.1.2 := by
    dsimp [r]
    exact (normSq_eq_norm_sq q.1.1.2).symm
  have hzSq : normSq q.1.1.1 = 1 - r ^ 2 := by
    rw [hrSq]
    linarith [q.1.2]
  have hc : 0 ≤ coefficient s q.1.1.2 := coefficient_nonneg s q.1.1.2
  have heq : (16 : ℂ) * q.1.1.1 ^ 2 =
      -((coefficient s q.1.1.2 : ℂ) *
        (9 * RadialMilnor.radialCube q.1.1.2)) :=
    eq_neg_of_add_eq_zero_left hzero
  have hnorm := congrArg norm heq
  rw [norm_mul, norm_ofNat, norm_pow, norm_neg, norm_mul,
    norm_real, Real.norm_eq_abs, abs_of_nonneg hc, norm_mul, norm_ofNat,
    RadialMilnor.norm_radialCube] at hnorm
  rw [← normSq_eq_norm_sq, ← normSq_eq_norm_sq, hzSq, ← hrSq] at hnorm
  have hnorm' :
      16 * (1 - r ^ 2) =
        (1 - (s : ℝ) + (s : ℝ) * (5 * r / 4)) * (9 * r ^ 2) := by
    simpa [coefficient, r] using hnorm
  have hfactor :
      (4 - 5 * r) * (9 * (s : ℝ) * r ^ 2 + 20 * r + 16) = 0 := by
    calc
      (4 - 5 * r) * (9 * (s : ℝ) * r ^ 2 + 20 * r + 16) =
          4 * (16 * (1 - r ^ 2) -
            (1 - (s : ℝ) + (s : ℝ) * (5 * r / 4)) * 9 * r ^ 2) := by
        ring
      _ = 0 := by rw [hnorm']; ring
  have hpositive : 0 < 9 * (s : ℝ) * r ^ 2 + 20 * r + 16 := by
    have hs : 0 ≤ 9 * (s : ℝ) * r ^ 2 :=
      mul_nonneg (mul_nonneg (by norm_num) s.2.1) (sq_nonneg r)
    have hr : 0 ≤ 20 * r := mul_nonneg (by norm_num) hr0
    linarith
  have hr : r = 4 / 5 := by
    have hfirst : 4 - 5 * r = 0 :=
      (mul_eq_zero.mp hfactor).resolve_right (ne_of_gt hpositive)
    linarith
  have hcoefficient : coefficient s q.1.1.2 = 1 := by
    unfold coefficient
    rw [show ‖q.1.1.2‖ = r by rfl, hr]
    ring
  have hbase : RadialMilnor.basePolynomial q.1 = 0 := by
    simpa [interpolatedPolynomial, RadialMilnor.basePolynomial,
      hcoefficient] using hzero
  have hradial : RadialMilnor.polynomial q.1 = 0 := by
    simp [RadialMilnor.polynomial, hbase]
  exact q.2 ((RadialPhase.polynomial_zero_iff q.1).mp hradial)

def interpolatedPhase : C(unitInterval × Complement, Circle) :=
  ⟨fun x => ⟨interpolatedPolynomial x.1 x.2.1 /
      ‖interpolatedPolynomial x.1 x.2.1‖, by
        simp [Submonoid.unitSphere,
          norm_ne_zero_iff.mpr (interpolatedPolynomial_ne_zero x.1 x.2)]⟩, by
    apply Continuous.subtype_mk
    have hpair : Continuous (fun x : unitInterval × Complement => (x.1, x.2.1)) :=
      continuous_fst.prodMk (continuous_subtype_val.comp continuous_snd)
    have hcomp := interpolatedPolynomial_continuous.comp hpair
    have hp : Continuous (fun x : unitInterval × Complement =>
        interpolatedPolynomial x.1 x.2.1) := by
      simpa only [Function.comp_def] using hcomp
    exact hp.div (Complex.continuous_ofReal.comp hp.norm) (fun x => by
      exact_mod_cast norm_ne_zero_iff.mpr
        (interpolatedPolynomial_ne_zero x.1 x.2))⟩

theorem interpolatedPolynomial_zero_time (q : Milnor.CSphere) :
    interpolatedPolynomial 0 q = RadialMilnor.basePolynomial q := by
  simp [interpolatedPolynomial, coefficient, RadialMilnor.basePolynomial]

theorem interpolatedPhase_zero (q : Complement) :
    interpolatedPhase (0, q) = basePhase q := by
  apply Subtype.ext
  rw [show (interpolatedPhase (0, q) : ℂ) =
      interpolatedPolynomial 0 q.1 /
        ‖interpolatedPolynomial 0 q.1‖ by rfl]
  rw [show (basePhase q : ℂ) =
      (-Complex.I) * (RadialMilnor.polynomial q.1 /
        ‖RadialMilnor.polynomial q.1‖) by rfl]
  rw [interpolatedPolynomial_zero_time]
  rw [RadialMilnor.polynomial, norm_mul, norm_I, one_mul]
  rw [div_eq_mul_inv]
  ring_nf
  rw [Complex.I_sq]
  simp

theorem interpolatedPolynomial_one_time (q : Milnor.CSphere) :
    interpolatedPolynomial 1 q = Milnor.polynomial q / 4 := by
  by_cases hw : q.1.2 = 0
  · simp [interpolatedPolynomial, coefficient, RadialMilnor.radialCube,
      Milnor.polynomial, hw]
    ring
  · rw [interpolatedPolynomial, coefficient,
      RadialMilnor.radialCube_of_ne hw, Milnor.polynomial]
    have hnorm : ‖q.1.2‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    have hnormComplex : (‖q.1.2‖ : ℂ) ≠ 0 := by exact_mod_cast hnorm
    push_cast
    field_simp [hnormComplex]
    ring

theorem interpolatedPhase_one (q : Complement) :
    interpolatedPhase (1, q) = oldPhase q := by
  apply Subtype.ext
  change interpolatedPolynomial 1 q.1 / ‖interpolatedPolynomial 1 q.1‖ =
    Milnor.polynomial q.1 / ‖Milnor.polynomial q.1‖
  rw [interpolatedPolynomial_one_time, norm_div]
  norm_num
  field_simp [norm_ne_zero_iff.mpr q.2]

def ratioHomotopy : C(unitInterval × Complement, Circle) :=
  CircleMapAlgebra.mapMul interpolatedPhase
    (CircleMapAlgebra.mapInv
      (basePhase.comp ⟨Prod.snd, continuous_snd⟩))

theorem ratioHomotopy_zero (q : Complement) :
    ratioHomotopy (0, q) = Circle.exp (0 : ℝ) := by
  apply Subtype.ext
  rw [show (ratioHomotopy (0, q) : ℂ) =
      (interpolatedPhase (0, q) : ℂ) * (basePhase q : ℂ)⁻¹ by rfl]
  rw [show (Circle.exp (0 : ℝ) : ℂ) = 1 by simp]
  rw [interpolatedPhase_zero]
  simp

def ratioLift : C(Complement, ℝ) :=
  ⟨fun q => Circle.isCoveringMap_exp.liftHomotopy ratioHomotopy
      (ContinuousMap.const Complement (0 : ℝ)) ratioHomotopy_zero (1, q),
    (Circle.isCoveringMap_exp.liftHomotopy ratioHomotopy
      (ContinuousMap.const Complement (0 : ℝ)) ratioHomotopy_zero).continuous.comp
        (continuous_const.prodMk continuous_id)⟩

def ratioMap : C(Complement, Circle) :=
  CircleMapAlgebra.mapMul oldPhase (CircleMapAlgebra.mapInv basePhase)

theorem exp_ratioLift (q : Complement) :
    Circle.exp (ratioLift q) = ratioMap q := by
  have hlifts := Circle.isCoveringMap_exp.liftHomotopy_lifts ratioHomotopy
    (ContinuousMap.const Complement (0 : ℝ)) ratioHomotopy_zero
  have h := congrFun hlifts (1, q)
  change Circle.exp (ratioLift q) = ratioHomotopy (1, q) at h
  simpa [ratioMap, ratioHomotopy, CircleMapAlgebra.mapMul,
    CircleMapAlgebra.mapInv, interpolatedPhase_one] using h

theorem degree_ratioMap : DeckDegree.degree ratioMap = 0 :=
  DegreeAlgebra.degree_eq_zero_of_global_lift ratioMap ratioLift exp_ratioLift

theorem oldPhase_eq_ratio_mul_base :
    oldPhase = CircleMapAlgebra.mapMul ratioMap basePhase := by
  ext q
  change (oldPhase q : ℂ) =
    ((oldPhase q : ℂ) * (basePhase q : ℂ)⁻¹) * (basePhase q : ℂ)
  simp

theorem degree_oldPhase : DeckDegree.degree oldPhase = 1 := by
  rw [oldPhase_eq_ratio_mul_base, DegreeAlgebra.degree_mapMul,
    degree_ratioMap, degree_basePhase]
  norm_num

theorem windingReal_oldPhase_eq_phase {q : Complement} (gamma : Path q q) :
    CircleWinding.windingReal (gamma.map oldPhase.continuous) =
      CircleWinding.windingReal (gamma.map PhaseDegree.phaseMap.continuous) := by
  have hratio := CoreMapAlgebra.windingReal_eq_zero_of_lift
    ratioMap ratioLift exp_ratioLift gamma
  have hminus := CoreMapAlgebra.windingReal_eq_zero_of_lift
    minusIMap minusILift exp_minusILift gamma
  rw [oldPhase_eq_ratio_mul_base, CircleMapAlgebra.windingReal_mapMul,
    basePhase, CircleMapAlgebra.windingReal_mapMul, hratio, hminus]
  ring

end

end Submission.AlgebraicPhase
