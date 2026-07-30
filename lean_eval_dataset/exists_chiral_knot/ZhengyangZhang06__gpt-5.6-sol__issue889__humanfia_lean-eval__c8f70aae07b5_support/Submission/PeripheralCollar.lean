import Submission.PeripheralTube

open Complex

namespace Submission.PeripheralCollar

noncomputable section

open PeripheralTube

noncomputable def collarRadius : ℝ :=
  Classical.choose exists_normalTargetRadius

theorem collarRadius_pos : 0 < collarRadius :=
  (Classical.choose_spec exists_normalTargetRadius).1

theorem collarRadius_spec (y : NormalPlane) (hy : ‖y‖ < collarRadius) :
    y ∈ normalChart.target ∧ ‖normalChart.symm y‖ < 1 / 4 :=
  (Classical.choose_spec exists_normalTargetRadius).2 y hy

def complexToNormalPlane : ℂ ≃L[ℝ] NormalPlane :=
  Complex.equivRealProdCLM.trans pairToNormalPlane

@[simp] theorem complexToNormalPlane_apply_zero (z : ℂ) :
    (complexToNormalPlane z).ofLp 0 = z.re := by
  rfl

@[simp] theorem complexToNormalPlane_apply_one (z : ℂ) :
    (complexToNormalPlane z).ofLp 1 = z.im := by
  rfl

theorem norm_complexToNormalPlane (z : ℂ) :
    ‖complexToNormalPlane z‖ = ‖z‖ := by
  have hp := EuclideanSpace.norm_sq_eq (complexToNormalPlane z)
  have hc := Complex.sq_norm z
  simp [complexToNormalPlane_apply_zero, complexToNormalPlane_apply_one,
    Complex.normSq_apply] at hp hc
  nlinarith [norm_nonneg (complexToNormalPlane z), norm_nonneg z]

def pageNormalValue (rho : ℝ) (u : Circle) : ℂ :=
  (rho : ℂ) / (u : ℂ) ^ 6

theorem norm_pageNormalValue {rho : ℝ} (hrho : 0 ≤ rho) (u : Circle) :
    ‖pageNormalValue rho u‖ = rho := by
  rw [pageNormalValue, norm_div, norm_real, Real.norm_eq_abs,
    abs_of_nonneg hrho, norm_pow, Circle.norm_coe, one_pow, div_one]

def pageNormalPlane (rho : ℝ) (u : Circle) : NormalPlane :=
  complexToNormalPlane (pageNormalValue rho u)

theorem norm_pageNormalPlane {rho : ℝ} (hrho : 0 ≤ rho) (u : Circle) :
    ‖pageNormalPlane rho u‖ = rho := by
  rw [pageNormalPlane, norm_complexToNormalPlane, norm_pageNormalValue hrho]

def CollarParameter := {x : ℝ × Circle // 0 < x.1 ∧ x.1 < collarRadius}

instance : TopologicalSpace CollarParameter := by
  unfold CollarParameter
  infer_instance

def parameterNormalPlane (x : CollarParameter) : NormalPlane :=
  pageNormalPlane x.1.1 x.1.2

theorem parameterNormalPlane_norm (x : CollarParameter) :
    ‖parameterNormalPlane x‖ = x.1.1 :=
  norm_pageNormalPlane x.2.1.le x.1.2

theorem parameterNormalPlane_mem_target (x : CollarParameter) :
    parameterNormalPlane x ∈ normalChart.target := by
  apply (collarRadius_spec (parameterNormalPlane x) ?_).1
  rw [parameterNormalPlane_norm]
  exact x.2.2

theorem parameterNormalInverse_bound (x : CollarParameter) :
    ‖normalChart.symm (parameterNormalPlane x)‖ < 1 / 4 := by
  apply (collarRadius_spec (parameterNormalPlane x) ?_).2
  rw [parameterNormalPlane_norm]
  exact x.2.2

def parameterNormalCoordinates (x : CollarParameter) : NormalPlane :=
  normalChart.symm (parameterNormalPlane x)

theorem parameterNormalCoordinates_radial_bounds (x : CollarParameter) :
    0 < bindingRadial + (parameterNormalCoordinates x).ofLp 0 ∧
      bindingRadial + (parameterNormalCoordinates x).ofLp 0 < 1 :=
  normalInverse_radial_bounds (parameterNormalInverse_bound x)

def collarCoordinates (x : CollarParameter) : TorusCoordinates :=
  (normalRadial (parameterNormalCoordinates x)
      (parameterNormalCoordinates_radial_bounds x).1
      (parameterNormalCoordinates_radial_bounds x).2,
    x.1.2, Circle.exp ((parameterNormalCoordinates x).ofLp 1))

def collarSphere (x : CollarParameter) : Milnor.CSphere :=
  (torusPoint (collarCoordinates x)).1

theorem normalComplex_parameterNormalCoordinates (x : CollarParameter) :
    normalComplex (parameterNormalCoordinates x) =
      pageNormalValue x.1.1 x.1.2 := by
  have hinv := normalChart.right_inv (parameterNormalPlane_mem_target x)
  change normalModelReal (parameterNormalCoordinates x) = parameterNormalPlane x at hinv
  apply Complex.ext
  · change (normalModelReal (parameterNormalCoordinates x)).ofLp 0 =
      (pageNormalValue x.1.1 x.1.2).re
    rw [hinv]
    exact complexToNormalPlane_apply_zero _
  · change (normalModelReal (parameterNormalCoordinates x)).ofLp 1 =
      (pageNormalValue x.1.1 x.1.2).im
    rw [hinv]
    exact complexToNormalPlane_apply_one _

theorem normalFactor_collarCoordinates (x : CollarParameter) :
    normalFactor (collarCoordinates x) = pageNormalValue x.1.1 x.1.2 := by
  rw [collarCoordinates, normalFactor_normalRadial,
    normalComplex_parameterNormalCoordinates]

theorem polynomial_collarSphere (x : CollarParameter) :
    RadialMilnor.polynomial (collarSphere x) = (x.1.1 : ℂ) := by
  rw [collarSphere, polynomial_torusPoint, normalFactor_collarCoordinates]
  change (x.1.2 : ℂ) ^ 6 * pageNormalValue x.1.1 x.1.2 = (x.1.1 : ℂ)
  unfold pageNormalValue
  field_simp [Circle.coe_ne_zero x.1.2]

def collarFiber (x : CollarParameter) : RadialMilnor.Fiber :=
  ⟨collarSphere x, by
    rw [polynomial_collarSphere]
    constructor
    · simpa using x.2.1
    · simp⟩

theorem pageNormalValue_continuous :
    Continuous (fun x : ℝ × Circle => pageNormalValue x.1 x.2) := by
  unfold pageNormalValue
  have hnum : Continuous (fun x : ℝ × Circle => ((x.1 : ℝ) : ℂ)) := by
    fun_prop
  have hden : Continuous (fun x : ℝ × Circle => (x.2 : ℂ) ^ 6) := by
    fun_prop
  exact hnum.div hden fun x => pow_ne_zero 6 (Circle.coe_ne_zero x.2)

theorem parameterNormalPlane_continuous : Continuous parameterNormalPlane := by
  exact complexToNormalPlane.continuous.comp
    (pageNormalValue_continuous.comp continuous_subtype_val)

theorem parameterNormalCoordinates_continuous :
    Continuous parameterNormalCoordinates := by
  exact normalChart.symm.continuousOn.comp_continuous
    parameterNormalPlane_continuous parameterNormalPlane_mem_target

theorem collarCoordinates_continuous : Continuous collarCoordinates := by
  have hradial : Continuous (fun x : CollarParameter =>
      bindingRadial + (parameterNormalCoordinates x).ofLp 0) :=
    continuous_const.add
      ((EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.comp
        parameterNormalCoordinates_continuous)
  have hradialSubtype : Continuous (fun x : CollarParameter =>
      normalRadial (parameterNormalCoordinates x)
        (parameterNormalCoordinates_radial_bounds x).1
        (parameterNormalCoordinates_radial_bounds x).2) := by
    apply Continuous.subtype_mk
    exact hradial
  have hlongitude : Continuous (fun x : CollarParameter => x.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hangle : Continuous (fun x : CollarParameter =>
      (parameterNormalCoordinates x).ofLp 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.comp
      parameterNormalCoordinates_continuous
  have hnormalPhase : Continuous (fun x : CollarParameter =>
      Circle.exp ((parameterNormalCoordinates x).ofLp 1)) := by
    exact Circle.exp.continuous.comp hangle
  exact hradialSubtype.prodMk (hlongitude.prodMk hnormalPhase)

theorem collarSphere_continuous : Continuous collarSphere := by
  exact continuous_subtype_val.comp
    (torusPoint_continuous.comp collarCoordinates_continuous)

theorem collarFiber_continuous : Continuous collarFiber := by
  unfold collarFiber
  apply Continuous.subtype_mk
  exact collarSphere_continuous

def ClosedCollarParameter :=
  {x : ℝ × Circle // 0 ≤ x.1 ∧ x.1 < collarRadius}

instance : TopologicalSpace ClosedCollarParameter := by
  unfold ClosedCollarParameter
  infer_instance

def closedParameterNormalPlane (x : ClosedCollarParameter) : NormalPlane :=
  pageNormalPlane x.1.1 x.1.2

theorem closedParameterNormalPlane_norm (x : ClosedCollarParameter) :
    ‖closedParameterNormalPlane x‖ = x.1.1 :=
  norm_pageNormalPlane x.2.1 x.1.2

theorem closedParameterNormalPlane_mem_target (x : ClosedCollarParameter) :
    closedParameterNormalPlane x ∈ normalChart.target := by
  apply (collarRadius_spec (closedParameterNormalPlane x) ?_).1
  rw [closedParameterNormalPlane_norm]
  exact x.2.2

theorem closedParameterNormalInverse_bound (x : ClosedCollarParameter) :
    ‖normalChart.symm (closedParameterNormalPlane x)‖ < 1 / 4 := by
  apply (collarRadius_spec (closedParameterNormalPlane x) ?_).2
  rw [closedParameterNormalPlane_norm]
  exact x.2.2

def closedParameterNormalCoordinates (x : ClosedCollarParameter) : NormalPlane :=
  normalChart.symm (closedParameterNormalPlane x)

theorem closedParameterNormalCoordinates_radial_bounds (x : ClosedCollarParameter) :
    0 < bindingRadial + (closedParameterNormalCoordinates x).ofLp 0 ∧
      bindingRadial + (closedParameterNormalCoordinates x).ofLp 0 < 1 :=
  normalInverse_radial_bounds (closedParameterNormalInverse_bound x)

def closedCollarCoordinates (x : ClosedCollarParameter) : TorusCoordinates :=
  (normalRadial (closedParameterNormalCoordinates x)
      (closedParameterNormalCoordinates_radial_bounds x).1
      (closedParameterNormalCoordinates_radial_bounds x).2,
    x.1.2, Circle.exp ((closedParameterNormalCoordinates x).ofLp 1))

def closedCollarSphere (x : ClosedCollarParameter) : Milnor.CSphere :=
  (torusPoint (closedCollarCoordinates x)).1

theorem closedNormalComplex_parameterNormalCoordinates (x : ClosedCollarParameter) :
    normalComplex (closedParameterNormalCoordinates x) =
      pageNormalValue x.1.1 x.1.2 := by
  have hinv := normalChart.right_inv (closedParameterNormalPlane_mem_target x)
  change normalModelReal (closedParameterNormalCoordinates x) =
    closedParameterNormalPlane x at hinv
  apply Complex.ext
  · change (normalModelReal (closedParameterNormalCoordinates x)).ofLp 0 =
      (pageNormalValue x.1.1 x.1.2).re
    rw [hinv]
    exact complexToNormalPlane_apply_zero _
  · change (normalModelReal (closedParameterNormalCoordinates x)).ofLp 1 =
      (pageNormalValue x.1.1 x.1.2).im
    rw [hinv]
    exact complexToNormalPlane_apply_one _

theorem normalFactor_closedCollarCoordinates (x : ClosedCollarParameter) :
    normalFactor (closedCollarCoordinates x) = pageNormalValue x.1.1 x.1.2 := by
  rw [closedCollarCoordinates, normalFactor_normalRadial,
    closedNormalComplex_parameterNormalCoordinates]

theorem polynomial_closedCollarSphere (x : ClosedCollarParameter) :
    RadialMilnor.polynomial (closedCollarSphere x) = (x.1.1 : ℂ) := by
  rw [closedCollarSphere, polynomial_torusPoint,
    normalFactor_closedCollarCoordinates]
  change (x.1.2 : ℂ) ^ 6 * pageNormalValue x.1.1 x.1.2 = (x.1.1 : ℂ)
  unfold pageNormalValue
  field_simp [Circle.coe_ne_zero x.1.2]

theorem closedParameterNormalPlane_continuous :
    Continuous closedParameterNormalPlane := by
  exact complexToNormalPlane.continuous.comp
    (pageNormalValue_continuous.comp continuous_subtype_val)

theorem closedParameterNormalCoordinates_continuous :
    Continuous closedParameterNormalCoordinates := by
  exact normalChart.symm.continuousOn.comp_continuous
    closedParameterNormalPlane_continuous closedParameterNormalPlane_mem_target

theorem closedCollarCoordinates_continuous : Continuous closedCollarCoordinates := by
  have hradial : Continuous (fun x : ClosedCollarParameter =>
      bindingRadial + (closedParameterNormalCoordinates x).ofLp 0) :=
    continuous_const.add
      ((EuclideanSpace.proj (𝕜 := ℝ) 0).continuous.comp
        closedParameterNormalCoordinates_continuous)
  have hradialSubtype : Continuous (fun x : ClosedCollarParameter =>
      normalRadial (closedParameterNormalCoordinates x)
        (closedParameterNormalCoordinates_radial_bounds x).1
        (closedParameterNormalCoordinates_radial_bounds x).2) := by
    apply Continuous.subtype_mk
    exact hradial
  have hlongitude : Continuous (fun x : ClosedCollarParameter => x.1.2) :=
    continuous_snd.comp continuous_subtype_val
  have hangle : Continuous (fun x : ClosedCollarParameter =>
      (closedParameterNormalCoordinates x).ofLp 1) :=
    (EuclideanSpace.proj (𝕜 := ℝ) 1).continuous.comp
      closedParameterNormalCoordinates_continuous
  have hnormalPhase : Continuous (fun x : ClosedCollarParameter =>
      Circle.exp ((closedParameterNormalCoordinates x).ofLp 1)) :=
    Circle.exp.continuous.comp hangle
  exact hradialSubtype.prodMk (hlongitude.prodMk hnormalPhase)

theorem closedCollarSphere_continuous : Continuous closedCollarSphere := by
  exact continuous_subtype_val.comp
    (torusPoint_continuous.comp closedCollarCoordinates_continuous)

def toClosedCollarParameter (x : CollarParameter) : ClosedCollarParameter :=
  ⟨x.1, x.2.1.le, x.2.2⟩

theorem closedCollarSphere_toClosed (x : CollarParameter) :
    closedCollarSphere (toClosedCollarParameter x) = collarSphere x := by
  rfl

theorem closedParameterNormalCoordinates_zero (u : Circle) :
    closedParameterNormalCoordinates
      ⟨(0, u), le_rfl, collarRadius_pos⟩ = 0 := by
  have hplane : closedParameterNormalPlane
      ⟨(0, u), le_rfl, collarRadius_pos⟩ = 0 := by
    ext i
    fin_cases i <;> simp [closedParameterNormalPlane, pageNormalPlane,
      pageNormalValue]
  change normalChart.symm
      (closedParameterNormalPlane ⟨(0, u), le_rfl, collarRadius_pos⟩) = 0
  rw [hplane]
  calc
    normalChart.symm (0 : NormalPlane) = normalChart.symm (normalModelReal 0) :=
      congrArg normalChart.symm normalModelReal_zero.symm
    _ = 0 := normalChart.left_inv zero_mem_normalChart_source

def bindingTorusCoordinates (u : Circle) : TorusCoordinates :=
  (⟨bindingRadial, by norm_num [bindingRadial]⟩, u, 1)

theorem closedCollarCoordinates_zero (u : Circle) :
    closedCollarCoordinates ⟨(0, u), le_rfl, collarRadius_pos⟩ =
      bindingTorusCoordinates u := by
  have hnormal := closedParameterNormalCoordinates_zero u
  have hnormalZero := congrArg
    (fun p : NormalPlane => p.ofLp (0 : Fin 2)) hnormal
  have hnormalOne := congrArg
    (fun p : NormalPlane => p.ofLp (1 : Fin 2)) hnormal
  unfold closedCollarCoordinates bindingTorusCoordinates
  apply Prod.ext
  · apply Subtype.ext
    change bindingRadial +
        (closedParameterNormalCoordinates
          ⟨(0, u), le_rfl, collarRadius_pos⟩).ofLp 0 = bindingRadial
    rw [hnormalZero]
    simp
  · apply Prod.ext
    · rfl
    · change Circle.exp
        ((closedParameterNormalCoordinates
          ⟨(0, u), le_rfl, collarRadius_pos⟩).ofLp 1) = 1
      rw [hnormalOne]
      simp

theorem closedCollarSphere_zero (u : Circle) :
    closedCollarSphere ⟨(0, u), le_rfl, collarRadius_pos⟩ =
      (bindingPoint u).1 := by
  let x : ClosedCollarParameter := ⟨(0, u), le_rfl, collarRadius_pos⟩
  let radialZero : OpenUnit := ⟨bindingRadial, by norm_num [bindingRadial]⟩
  have hx : x = ⟨(0, u), le_rfl, collarRadius_pos⟩ := rfl
  have hnormal : closedParameterNormalCoordinates x = 0 := by
    rw [hx]
    exact closedParameterNormalCoordinates_zero u
  have hnormalZero := congrArg
    (fun p : NormalPlane => p.ofLp (0 : Fin 2)) hnormal
  have hnormalOne := congrArg
    (fun p : NormalPlane => p.ofLp (1 : Fin 2)) hnormal
  have hcoords : closedCollarCoordinates x = (radialZero, u, 1) := by
    unfold closedCollarCoordinates
    apply Prod.ext
    · apply Subtype.ext
      change bindingRadial + (closedParameterNormalCoordinates x).ofLp 0 =
        (radialZero : ℝ)
      rw [hnormalZero]
      simp [radialZero]
    · apply Prod.ext
      · rfl
      · change Circle.exp ((closedParameterNormalCoordinates x).ofLp 1) = 1
        rw [hnormalOne]
        simp
  change closedCollarSphere x = (bindingPoint u).1
  rw [closedCollarSphere, hcoords]
  apply Subtype.ext
  apply Prod.ext
  · change ((Real.sqrt (1 - bindingRadial) : ℝ) : ℂ) *
        ((u : ℂ) ^ 3 / (1 : ℂ)) =
      ((3 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 3
    norm_num [bindingRadial]
  · change -(((Real.sqrt bindingRadial : ℝ) : ℂ) *
        ((u : ℂ) ^ 2 / (1 : ℂ))) =
      ((-4 / 5 : ℝ) : ℂ) * (u : ℂ) ^ 2
    norm_num [bindingRadial]

def torusNormalCoordinates (q : TorusRegion) : NormalPlane :=
  WithLp.toLp 2 ![(radial q : ℝ) - bindingRadial,
    Complex.arg (normalPhase q : ℂ)]

@[simp] theorem torusNormalCoordinates_zero (q : TorusRegion) :
    (torusNormalCoordinates q).ofLp 0 = (radial q : ℝ) - bindingRadial := by
  rfl

@[simp] theorem torusNormalCoordinates_one (q : TorusRegion) :
    (torusNormalCoordinates q).ofLp 1 = Complex.arg (normalPhase q : ℂ) := by
  rfl

theorem torusNormalCoordinates_radial_bounds (q : TorusRegion) :
    0 < bindingRadial + (torusNormalCoordinates q).ofLp 0 ∧
      bindingRadial + (torusNormalCoordinates q).ofLp 0 < 1 := by
  have hr0 : 0 < (radial q : ℝ) := (radial q).2.1
  have hr1 : (radial q : ℝ) < 1 := (radial q).2.2
  constructor
  · rw [torusNormalCoordinates_zero]
    nlinarith
  · rw [torusNormalCoordinates_zero]
    nlinarith

theorem torusCoordinates_from_normal (q : TorusRegion) :
    (normalRadial (torusNormalCoordinates q)
        (torusNormalCoordinates_radial_bounds q).1
        (torusNormalCoordinates_radial_bounds q).2,
      longitude q, Circle.exp ((torusNormalCoordinates q).ofLp 1)) =
      torusCoordinates q := by
  apply Prod.ext
  · apply Subtype.ext
    change bindingRadial + (torusNormalCoordinates q).ofLp 0 = (radial q : ℝ)
    rw [torusNormalCoordinates_zero]
    ring
  · apply Prod.ext
    · rfl
    · change Circle.exp (Complex.arg (normalPhase q : ℂ)) = normalPhase q
      exact Circle.exp_arg (normalPhase q)

theorem normalComplex_torusNormalCoordinates (q : TorusRegion) :
    normalComplex (torusNormalCoordinates q) =
      normalFactor (torusCoordinates q) := by
  have hfactor := normalFactor_normalRadial (torusNormalCoordinates q)
    (torusNormalCoordinates_radial_bounds q).1
    (torusNormalCoordinates_radial_bounds q).2 (longitude q)
  rw [torusCoordinates_from_normal] at hfactor
  exact hfactor.symm

theorem complexToNormalPlane_normalComplex (p : NormalPlane) :
    complexToNormalPlane (normalComplex p) = normalModelReal p := by
  ext i
  fin_cases i <;> rfl

theorem polynomial_eq_positive_real (q : RadialMilnor.Fiber) :
    RadialMilnor.polynomial q.1 = ((RadialMilnor.polynomial q.1).re : ℂ) := by
  apply Complex.ext
  · simp
  · simpa using q.2.2

theorem norm_normalFactor_torusCoordinates (q : RadialMilnor.Fiber)
    (hq : TorusRegion) (heq : hq.1 = q.1) :
    ‖normalFactor (torusCoordinates hq)‖ =
      (RadialMilnor.polynomial q.1).re := by
  have hpoly := polynomial_torusPoint (torusCoordinates hq)
  rw [torusPoint_torusCoordinates] at hpoly
  have hpolyQ : RadialMilnor.polynomial hq.1 =
      ((RadialMilnor.polynomial q.1).re : ℂ) := by
    calc
      RadialMilnor.polynomial hq.1 = RadialMilnor.polynomial q.1 :=
        congrArg RadialMilnor.polynomial heq
      _ = ((RadialMilnor.polynomial q.1).re : ℂ) :=
        polynomial_eq_positive_real q
  rw [hpolyQ] at hpoly
  have hnorm := congrArg norm hpoly
  rw [norm_mul, norm_pow, Circle.norm_coe, one_pow, one_mul,
    norm_real, Real.norm_eq_abs, abs_of_pos q.2.1] at hnorm
  exact hnorm.symm

def collarParameterOfFiber (q : RadialMilnor.Fiber) (hq : TorusRegion)
    (heq : hq.1 = q.1)
    (hsmall : ‖normalFactor (torusCoordinates hq)‖ < collarRadius) :
    CollarParameter :=
  ⟨((RadialMilnor.polynomial q.1).re, longitude hq), q.2.1,
    (norm_normalFactor_torusCoordinates q hq heq).symm ▸ hsmall⟩

theorem pageNormalValue_collarParameterOfFiber (q : RadialMilnor.Fiber)
    (hq : TorusRegion) (heq : hq.1 = q.1)
    (hsmall : ‖normalFactor (torusCoordinates hq)‖ < collarRadius) :
    pageNormalValue (collarParameterOfFiber q hq heq hsmall).1.1
        (collarParameterOfFiber q hq heq hsmall).1.2 =
      normalFactor (torusCoordinates hq) := by
  have hpoly := polynomial_torusPoint (torusCoordinates hq)
  rw [torusPoint_torusCoordinates] at hpoly
  have hpolyQ : RadialMilnor.polynomial hq.1 =
      ((RadialMilnor.polynomial q.1).re : ℂ) := by
    calc
      RadialMilnor.polynomial hq.1 = RadialMilnor.polynomial q.1 :=
        congrArg RadialMilnor.polynomial heq
      _ = ((RadialMilnor.polynomial q.1).re : ℂ) :=
        polynomial_eq_positive_real q
  rw [hpolyQ] at hpoly
  change (((RadialMilnor.polynomial q.1).re : ℝ) : ℂ) /
      (longitude hq : ℂ) ^ 6 = normalFactor (torusCoordinates hq)
  rw [div_eq_iff (pow_ne_zero 6 (Circle.coe_ne_zero (longitude hq)))]
  calc
    (((RadialMilnor.polynomial q.1).re : ℝ) : ℂ) =
        (longitude hq : ℂ) ^ 6 * normalFactor (torusCoordinates hq) := hpoly
    _ = normalFactor (torusCoordinates hq) * (longitude hq : ℂ) ^ 6 :=
      mul_comm _ _

theorem parameterNormalCoordinates_collarParameterOfFiber
    (q : RadialMilnor.Fiber) (hq : TorusRegion) (heq : hq.1 = q.1)
    (hsmall : ‖normalFactor (torusCoordinates hq)‖ < collarRadius)
    (hsource : torusNormalCoordinates hq ∈ normalChart.source) :
    parameterNormalCoordinates (collarParameterOfFiber q hq heq hsmall) =
      torusNormalCoordinates hq := by
  change normalChart.symm
      (pageNormalPlane (collarParameterOfFiber q hq heq hsmall).1.1
        (collarParameterOfFiber q hq heq hsmall).1.2) = _
  have hplane :
      pageNormalPlane (collarParameterOfFiber q hq heq hsmall).1.1
          (collarParameterOfFiber q hq heq hsmall).1.2 =
        normalModelReal (torusNormalCoordinates hq) := by
    rw [pageNormalPlane,
      pageNormalValue_collarParameterOfFiber q hq heq hsmall,
      ← normalComplex_torusNormalCoordinates,
      complexToNormalPlane_normalComplex]
  rw [hplane]
  exact normalChart.left_inv hsource

theorem collarCoordinates_collarParameterOfFiber
    (q : RadialMilnor.Fiber) (hq : TorusRegion) (heq : hq.1 = q.1)
    (hsmall : ‖normalFactor (torusCoordinates hq)‖ < collarRadius)
    (hsource : torusNormalCoordinates hq ∈ normalChart.source) :
    collarCoordinates (collarParameterOfFiber q hq heq hsmall) =
      torusCoordinates hq := by
  have hp := parameterNormalCoordinates_collarParameterOfFiber
    q hq heq hsmall hsource
  have hpZero := congrArg (fun p : NormalPlane => p.ofLp (0 : Fin 2)) hp
  have hpOne := congrArg (fun p : NormalPlane => p.ofLp (1 : Fin 2)) hp
  unfold collarCoordinates
  apply Prod.ext
  · apply Subtype.ext
    change bindingRadial +
        (parameterNormalCoordinates
          (collarParameterOfFiber q hq heq hsmall)).ofLp 0 =
      (radial hq : ℝ)
    rw [hpZero]
    simp [torusNormalCoordinates]
  · apply Prod.ext
    · rfl
    · change Circle.exp
        ((parameterNormalCoordinates
          (collarParameterOfFiber q hq heq hsmall)).ofLp 1) = normalPhase hq
      rw [hpOne]
      exact Circle.exp_arg (normalPhase hq)

theorem collarFiber_collarParameterOfFiber
    (q : RadialMilnor.Fiber) (hq : TorusRegion) (heq : hq.1 = q.1)
    (hsmall : ‖normalFactor (torusCoordinates hq)‖ < collarRadius)
    (hsource : torusNormalCoordinates hq ∈ normalChart.source) :
    collarFiber (collarParameterOfFiber q hq heq hsmall) = q := by
  apply Subtype.ext
  change (torusPoint
      (collarCoordinates (collarParameterOfFiber q hq heq hsmall))).1 = q.1
  rw [collarCoordinates_collarParameterOfFiber q hq heq hsmall hsource,
    torusPoint_torusCoordinates, heq]

def LocalTubeSet : Set TorusRegion :=
  {q | 0 < (normalPhase q : ℂ).re ∧
    torusNormalCoordinates q ∈ normalChart.source ∧
      ‖normalFactor (torusCoordinates q)‖ < collarRadius}

theorem torusNormalCoordinates_continuousAt {q : TorusRegion}
    (hq : 0 < (normalPhase q : ℂ).re) :
    ContinuousAt torusNormalCoordinates q := by
  have hphase : Continuous (fun x : TorusRegion => normalPhase x) := by
    change Continuous (fun x : TorusRegion => (torusCoordinates x).2.2)
    exact continuous_snd.comp (continuous_snd.comp torusCoordinates_continuous)
  have hphaseCoe : Continuous (fun x : TorusRegion => (normalPhase x : ℂ)) :=
    continuous_subtype_val.comp hphase
  have harg : ContinuousAt (fun x : TorusRegion =>
      Complex.arg (normalPhase x : ℂ)) q :=
    Filter.Tendsto.comp (Complex.continuousAt_arg (Or.inl hq))
      hphaseCoe.continuousAt
  apply (PiLp.continuousLinearEquiv 2 ℝ
    (fun _ : Fin 2 => ℝ)).symm.continuousAt.comp
  apply continuousAt_pi.mpr
  intro i
  fin_cases i
  · exact (continuous_subtype_val.comp radial_continuous).continuousAt.sub
      continuousAt_const
  · exact harg

theorem localTubeSet_isOpen : IsOpen LocalTubeSet := by
  rw [isOpen_iff_mem_nhds]
  intro q hq
  rcases hq with ⟨hphase, hsource, hsmall⟩
  have hphaseContinuous : Continuous (fun x : TorusRegion =>
      (normalPhase x : ℂ).re) := by
    have hnormal : Continuous (fun x : TorusRegion => normalPhase x) := by
      change Continuous (fun x : TorusRegion => (torusCoordinates x).2.2)
      exact continuous_snd.comp (continuous_snd.comp torusCoordinates_continuous)
    exact Complex.continuous_re.comp (continuous_subtype_val.comp hnormal)
  have hfactor : Continuous (fun x : TorusRegion =>
      ‖normalFactor (torusCoordinates x)‖) :=
    (normalFactor_continuous.comp torusCoordinates_continuous).norm
  filter_upwards
    [hphaseContinuous.continuousAt (isOpen_Ioi.mem_nhds hphase),
      (torusNormalCoordinates_continuousAt hphase)
        (normalChart.open_source.mem_nhds hsource),
      hfactor.continuousAt (isOpen_Iio.mem_nhds hsmall)] with x hx hsourceX hsmallX
  exact ⟨hx, hsourceX, hsmallX⟩

def BindingTorusPoint (u : Circle) : TorusRegion :=
  ⟨(bindingPoint u).1, binding_z_ne (bindingPoint u), binding_w_ne (bindingPoint u)⟩

theorem bindingTorusPoint_eq (u : Circle) :
    BindingTorusPoint u = torusPoint (bindingTorusCoordinates u) := by
  apply Subtype.ext
  rw [← closedCollarCoordinates_zero u]
  exact (closedCollarSphere_zero u).symm

theorem bindingTorusPoint_mem_localTubeSet (u : Circle) :
    BindingTorusPoint u ∈ LocalTubeSet := by
  rw [bindingTorusPoint_eq]
  rw [LocalTubeSet]
  constructor
  · rw [normalPhase_torusPoint]
    norm_num [bindingTorusCoordinates]
  · constructor
    · have hnormal : torusNormalCoordinates
          (torusPoint (bindingTorusCoordinates u)) = 0 := by
        ext i
        fin_cases i
        · simp [torusNormalCoordinates, bindingTorusCoordinates]
        · simp [torusNormalCoordinates, bindingTorusCoordinates]
      rw [hnormal]
      exact zero_mem_normalChart_source
    · have hfactor : normalFactor (bindingTorusCoordinates u) = 0 := by
        rw [← closedCollarCoordinates_zero u,
          normalFactor_closedCollarCoordinates]
        simp [pageNormalValue]
      rw [torusCoordinates_torusPoint]
      rw [hfactor, norm_zero]
      exact collarRadius_pos

def TorusRegionSet : Set CSphere :=
  {q | q.1.1 ≠ 0 ∧ q.1.2 ≠ 0}

theorem torusRegionSet_isOpen : IsOpen TorusRegionSet := by
  have hz : Continuous (fun q : CSphere => q.1.1) := by fun_prop
  have hw : Continuous (fun q : CSphere => q.1.2) := by fun_prop
  exact (isOpen_ne.preimage hz).inter (isOpen_ne.preimage hw)

def LocalTubeSphere : Set CSphere :=
  Subtype.val '' LocalTubeSet

theorem localTubeSphere_isOpen : IsOpen LocalTubeSphere := by
  unfold LocalTubeSphere
  exact localTubeSet_isOpen.trans torusRegionSet_isOpen

theorem bindingPoint_mem_localTubeSphere (u : Circle) :
    (bindingPoint u).1 ∈ LocalTubeSphere :=
  ⟨BindingTorusPoint u, bindingTorusPoint_mem_localTubeSet u, rfl⟩

end

end Submission.PeripheralCollar
