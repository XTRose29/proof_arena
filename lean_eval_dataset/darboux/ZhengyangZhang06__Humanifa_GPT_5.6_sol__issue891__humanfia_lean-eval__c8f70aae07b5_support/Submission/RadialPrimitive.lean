import Submission.LinearNormal
import Mathlib.Analysis.Calculus.ParametricIntervalIntegral
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.MeasureTheory.Integral.IntervalIntegral.ContDiff

open Set Function Matrix MeasureTheory Metric
open scoped Interval

namespace Submission.RadialPrimitive

noncomputable section

universe u

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Contraction of a two-form with a vector in its first argument. -/
def contract (ω : V [⋀^Fin 2]→L[ℝ] ℝ) (z : V) : V →L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv (ω.curryLeft z)

@[simp]
theorem contract_apply (ω : V [⋀^Fin 2]→L[ℝ] ℝ) (z v : V) :
    contract ω z v = ω ![z, v] := by
  have htail : (fun _ : Fin 1 => v) = ![v] := by
    funext i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    rfl
  change ω (Matrix.vecCons z fun _ : Fin 1 => v) = ω (Matrix.vecCons z ![v])
  rw [htail]

@[simp]
theorem contract_zero (ω : V [⋀^Fin 2]→L[ℝ] ℝ) : contract ω 0 = 0 := by
  ext v
  rw [contract_apply]
  exact ω.map_coord_zero 0 (by simp)

/-- The radial homotopy integrand for a two-form field. -/
def radialIntegrand (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (z : V) (t : ℝ) : V →L[ℝ] ℝ :=
  t • contract (δ (t • z)) z

@[simp]
theorem radialIntegrand_apply (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (z v : V) (t : ℝ) :
    radialIntegrand δ z t v = t * δ (t • z) ![z, v] := by
  simp [radialIntegrand, contract_apply]

/-- The standard radial primitive of a two-form field based at the origin. -/
def radialPrimitive (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (z : V) : V →L[ℝ] ℝ :=
  ∫ t in (0 : ℝ)..1, radialIntegrand δ z t

theorem radialPrimitive_apply (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (z v : V)
    (hint : IntervalIntegrable (radialIntegrand δ z) volume 0 1) :
    radialPrimitive δ z v = ∫ t in (0 : ℝ)..1, t * δ (t • z) ![z, v] := by
  rw [radialPrimitive, ContinuousLinearMap.intervalIntegral_apply hint v]
  simp only [radialIntegrand_apply]

@[simp]
theorem radialPrimitive_zero (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) :
    radialPrimitive δ 0 = 0 := by
  simp [radialPrimitive, radialIntegrand]

open scoped ContDiff

theorem contract_contDiff {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    {form : X → V [⋀^Fin 2]→L[ℝ] ℝ} {z : X → V}
    (hform : ContDiff ℝ ∞ form) (hz : ContDiff ℝ ∞ z) :
    ContDiff ℝ ∞ fun x => contract (form x) (z x) := by
  let curry : (V [⋀^Fin 2]→L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] V [⋀^Fin 1]→L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.curryLeftLI
      (𝕜 := ℝ) (E := V) (F := ℝ) (n := 1)).toContinuousLinearMap
  have hcurryMap : ContDiff ℝ ∞ curry :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := V [⋀^Fin 2]→L[ℝ] ℝ) (F := V →L[ℝ] V [⋀^Fin 1]→L[ℝ] ℝ)
      (n := ∞) curry
  have hcurry : ContDiff ℝ ∞ fun x => curry (form x) := hcurryMap.comp hform
  have happly : ContDiff ℝ ∞ fun x => curry (form x) (z x) := hcurry.clm_apply hz
  let uncurry : (V [⋀^Fin 1]→L[ℝ] ℝ) →L[ℝ] (V →L[ℝ] ℝ) :=
    (ContinuousAlternatingMap.ofSubsingletonLIE
      (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).symm.toContinuousLinearEquiv.toContinuousLinearMap
  have huncurry : ContDiff ℝ ∞ uncurry :=
    ContinuousLinearMap.contDiff (𝕜 := ℝ)
      (E := V [⋀^Fin 1]→L[ℝ] ℝ) (F := V →L[ℝ] ℝ) (n := ∞) uncurry
  convert huncurry.comp happly using 1
  funext x
  rfl

/-- Scalar form of the radial integrand, with the parameter bundled into a product. -/
def scalarIntegrand (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (v : V) (p : V × ℝ) : ℝ :=
  p.2 * δ (p.2 • p.1) ![p.1, v]

theorem scalarIntegrand_contDiff (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (v : V) : ContDiff ℝ ∞ (scalarIntegrand δ v) := by
  unfold scalarIntegrand
  have hform : ContDiff ℝ ∞ fun p : V × ℝ => δ (p.2 • p.1) := by fun_prop
  have hcontract : ContDiff ℝ ∞ fun p : V × ℝ => contract (δ (p.2 • p.1)) p.1 :=
    contract_contDiff hform (by fun_prop)
  simpa only [contract_apply] using (by fun_prop : ContDiff ℝ ∞ fun p : V × ℝ =>
    p.2 * (contract (δ (p.2 • p.1)) p.1) v)

/-- Derivative of the scalar radial integrand in its spatial variable. -/
def scalarPartialFDeriv (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (v : V)
    (p : V × ℝ) : V →L[ℝ] ℝ :=
  fderiv ℝ (scalarIntegrand δ v) p ∘L ContinuousLinearMap.inl ℝ V ℝ

theorem scalarPartialFDeriv_contDiff (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (v : V) :
    ContDiff ℝ ∞ (scalarPartialFDeriv δ v) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (scalarIntegrand δ v)) :=
    (scalarIntegrand_contDiff δ hδ v).fderiv_right (by simp)
  unfold scalarPartialFDeriv
  fun_prop

theorem scalarIntegrand_hasFDerivAt_left (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (v z : V) (t : ℝ) :
    HasFDerivAt (fun y => scalarIntegrand δ v (y, t))
      (scalarPartialFDeriv δ v (z, t)) z := by
  exact (((scalarIntegrand_contDiff δ hδ v).differentiable (by simp)).differentiableAt.hasFDerivAt.comp z
    (hasFDerivAt_prodMk_left z t))

theorem hasFDerivAt_scalarRadialIntegral [FiniteDimensional ℝ V]
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) (v z : V) :
    HasFDerivAt
      (fun y => ∫ t in (0 : ℝ)..1, scalarIntegrand δ v (y, t))
      (∫ t in (0 : ℝ)..1, scalarPartialFDeriv δ v (z, t)) z := by
  let K : Set (V × ℝ) := closedBall z 1 ×ˢ Icc 0 1
  have hK : IsCompact K := IsCompact.prod (isCompact_closedBall z 1) isCompact_Icc
  have hpartial : Continuous (scalarPartialFDeriv δ v) :=
    (scalarPartialFDeriv_contDiff δ hδ v).continuous
  have himage : IsCompact (scalarPartialFDeriv δ v '' K) := hK.image hpartial
  obtain ⟨C, hC⟩ := himage.isBounded.exists_norm_le
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (s := ball z 1) (bound := fun _ => C) (ball_mem_nhds z zero_lt_one)
  · exact Filter.Eventually.of_forall fun y => by
      have h : Continuous fun t : ℝ => scalarIntegrand δ v (y, t) :=
        (scalarIntegrand_contDiff δ hδ v).continuous.comp
          (continuous_const.prodMk continuous_id)
      exact h.aestronglyMeasurable
  · exact ((scalarIntegrand_contDiff δ hδ v).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable (μ := volume) 0 1
  · exact ((scalarPartialFDeriv_contDiff δ hδ v).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with t
    intro ht y hy
    apply hC (scalarPartialFDeriv δ v (y, t))
    refine ⟨(y, t), ?_, rfl⟩
    constructor
    · exact mem_closedBall'.mpr (mem_ball'.mp hy).le
    · rw [uIoc_of_le (by norm_num)] at ht
      exact ⟨ht.1.le, ht.2⟩
  · exact intervalIntegrable_const
  · filter_upwards [] with t
    intro _ht y _hy
    exact scalarIntegrand_hasFDerivAt_left δ hδ v y t

theorem fderiv_alternating_radial (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (z u v : V) (t : ℝ) :
    fderiv ℝ (fun y => δ (t • y) ![y, v]) z u =
      t * fderiv ℝ δ (t • z) u ![z, v] + δ (t • z) ![u, v] := by
  have hδdiff : Differentiable ℝ δ := hδ.differentiable (by simp)
  have hform : DifferentiableAt ℝ (fun y => δ (t • y)) z :=
    (hδdiff (t • z)).comp z (differentiableAt_id.const_smul t)
  have hargs : ∀ i, DifferentiableAt ℝ (fun y : V => ![y, v] i) z := by
    intro i
    fin_cases i
    · change DifferentiableAt ℝ (fun y : V => y) z
      exact differentiableAt_id
    · change DifferentiableAt ℝ (fun _ : V => v) z
      exact differentiableAt_const (c := v)
  rw [fderiv_continuousAlternatingMap_apply_apply hform hargs]
  simp only [Fin.sum_univ_two]
  simp only [fderiv_comp_smul]
  have hu0 : Function.update (fun i => ![z, v] i) 0 u = ![u, v] := by
    funext i
    fin_cases i <;> simp
  have hu1 : Function.update (fun i => ![z, v] i) 1 0 = ![z, 0] := by
    funext i
    fin_cases i <;> simp
  have hd0 : fderiv ℝ (fun y : V => ![y, v] (0 : Fin 2)) z u = u := by simp
  have hd1 : fderiv ℝ (fun y : V => ![y, v] (1 : Fin 2)) z u = 0 := by simp
  rw [hd0, hu0, hd1, hu1]
  have hz0 : (δ (t • z)) ![z, 0] = 0 :=
    (δ (t • z)).map_coord_zero (m := ![z, 0]) 1 rfl
  rw [hz0]
  simp only [add_zero]
  change t * ((fderiv ℝ δ (t • z)) u) ![z, v] + (δ (t • z)) ![u, v] = _
  ring

theorem scalarPartialFDeriv_apply (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (z u v : V) (t : ℝ) :
    scalarPartialFDeriv δ v (z, t) u =
      t ^ 2 * fderiv ℝ δ (t • z) u ![z, v] + t * δ (t • z) ![u, v] := by
  have hleft := scalarIntegrand_hasFDerivAt_left δ hδ v z t
  rw [← hleft.fderiv]
  unfold scalarIntegrand
  have hinner : DifferentiableAt ℝ (fun y => δ (t • y) ![y, v]) z := by
    have hδdiff : Differentiable ℝ δ := hδ.differentiable (by simp)
    have hform : DifferentiableAt ℝ (fun y => δ (t • y)) z :=
      (hδdiff (t • z)).comp z (differentiableAt_id.const_smul t)
    have hargs : ∀ i, DifferentiableAt ℝ (fun y : V => ![y, v] i) z := by
      intro i
      fin_cases i
      · change DifferentiableAt ℝ (fun y : V => y) z
        exact differentiableAt_id
      · change DifferentiableAt ℝ (fun _ : V => v) z
        exact differentiableAt_const (c := v)
    exact hform.continuousAlternatingMap_apply hargs
  rw [fderiv_const_mul hinner t]
  change t * fderiv ℝ (fun y => δ (t • y) ![y, v]) z u = _
  rw [fderiv_alternating_radial δ hδ]
  ring

section ParameterIntegral

variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

def parameterPartialFDeriv (g : V × ℝ → W) (p : V × ℝ) : V →L[ℝ] W :=
  fderiv ℝ g p ∘L ContinuousLinearMap.inl ℝ V ℝ

omit [CompleteSpace W] in theorem parameterPartialFDeriv_contDiff
    (g : V × ℝ → W) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ (parameterPartialFDeriv g) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ g) := hg.fderiv_right (by simp)
  unfold parameterPartialFDeriv
  fun_prop

omit [CompleteSpace W] in theorem parameter_hasFDerivAt_interval
    (g : V × ℝ → W) (hg : ContDiff ℝ ∞ g)
    [FiniteDimensional ℝ V] (z : V) (a b : ℝ) :
    HasFDerivAt
      (fun y => ∫ t in a..b, g (y, t))
      (∫ t in a..b, parameterPartialFDeriv g (z, t)) z := by
  let K : Set (V × ℝ) := closedBall z 1 ×ˢ uIcc a b
  have hK : IsCompact K := IsCompact.prod (isCompact_closedBall z 1) isCompact_uIcc
  have hpartial : Continuous (parameterPartialFDeriv g) :=
    (parameterPartialFDeriv_contDiff g hg).continuous
  have himage : IsCompact (parameterPartialFDeriv g '' K) := hK.image hpartial
  obtain ⟨C, hC⟩ := himage.isBounded.exists_norm_le
  apply intervalIntegral.hasFDerivAt_integral_of_dominated_of_fderiv_le
    (μ := volume) (s := ball z 1) (bound := fun _ => C) (ball_mem_nhds z zero_lt_one)
  · exact Filter.Eventually.of_forall fun y =>
      (hg.continuous.comp (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · exact (hg.continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable (μ := volume) a b
  · exact ((parameterPartialFDeriv_contDiff g hg).continuous.comp
      (continuous_const.prodMk continuous_id)).aestronglyMeasurable
  · filter_upwards [] with t
    intro ht y hy
    apply hC (parameterPartialFDeriv g (y, t))
    refine ⟨(y, t), ?_, rfl⟩
    constructor
    · exact mem_closedBall'.mpr (mem_ball'.mp hy).le
    · exact uIoc_subset_uIcc ht
  · exact intervalIntegrable_const
  · filter_upwards [] with t
    intro _ht y _hy
    exact (((hg.differentiable (by simp)) (y, t)).hasFDerivAt.comp y
      (hasFDerivAt_prodMk_left y t))

omit [CompleteSpace W] in theorem parameter_hasFDerivAt
    (g : V × ℝ → W) (hg : ContDiff ℝ ∞ g)
    [FiniteDimensional ℝ V] (z : V) :
    HasFDerivAt
      (fun y => ∫ t in (0 : ℝ)..1, g (y, t))
      (∫ t in (0 : ℝ)..1, parameterPartialFDeriv g (z, t)) z :=
  parameter_hasFDerivAt_interval g hg z 0 1

theorem parameterIntegral_contDiff_nat [FiniteDimensional ℝ V]
    (k : ℕ) (g : V × ℝ → W) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ k fun y => ∫ t in (0 : ℝ)..1, g (y, t) := by
  induction k generalizing W with
  | zero =>
      have hdiff : Differentiable ℝ fun y => ∫ t in (0 : ℝ)..1, g (y, t) :=
        fun z => (parameter_hasFDerivAt g hg z).differentiableAt
      exact contDiff_zero.mpr hdiff.continuous
  | succ k ih =>
      change ContDiff ℝ ((↑k : ℕ∞) + 1) fun y => ∫ t in (0 : ℝ)..1, g (y, t)
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun z => (parameter_hasFDerivAt g hg z).differentiableAt, by simp, ?_⟩
      have hpartial : ContDiff ℝ ∞ (parameterPartialFDeriv g) :=
        parameterPartialFDeriv_contDiff g hg
      have hrec := ih (parameterPartialFDeriv g) hpartial
      have hfderiv :
          fderiv ℝ (fun y => ∫ t in (0 : ℝ)..1, g (y, t)) =
            fun z => ∫ t in (0 : ℝ)..1, parameterPartialFDeriv g (z, t) := by
        funext z
        exact (parameter_hasFDerivAt g hg z).fderiv
      rw [hfderiv]
      exact hrec

theorem parameterIntegral_contDiff [FiniteDimensional ℝ V]
    (g : V × ℝ → W) (hg : ContDiff ℝ ∞ g) :
    ContDiff ℝ ∞ fun y => ∫ t in (0 : ℝ)..1, g (y, t) :=
  contDiff_infty.mpr fun k => parameterIntegral_contDiff_nat k g hg

end ParameterIntegral

def bundledRadialIntegrand (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (p : V × ℝ) : V →L[ℝ] ℝ :=
  radialIntegrand δ p.1 p.2

theorem bundledRadialIntegrand_contDiff (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) : ContDiff ℝ ∞ (bundledRadialIntegrand δ) := by
  unfold bundledRadialIntegrand radialIntegrand
  have hform : ContDiff ℝ ∞ fun p : V × ℝ => δ (p.2 • p.1) := by fun_prop
  have hcontract : ContDiff ℝ ∞ fun p : V × ℝ => contract (δ (p.2 • p.1)) p.1 :=
    contract_contDiff hform (by fun_prop)
  fun_prop

theorem radialIntegrand_intervalIntegrable (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (z : V) :
    IntervalIntegrable (radialIntegrand δ z) volume 0 1 := by
  exact ((bundledRadialIntegrand_contDiff δ hδ).continuous.comp
    (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1

theorem fderiv_radialPrimitive_apply [FiniteDimensional ℝ V]
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) (z u v : V) :
    fderiv ℝ (fun y => radialPrimitive δ y v) z u =
      ∫ t in (0 : ℝ)..1,
        (t ^ 2 * fderiv ℝ δ (t • z) u ![z, v] + t * δ (t • z) ![u, v]) := by
  have heq : (fun y => radialPrimitive δ y v) =
      fun y => ∫ t in (0 : ℝ)..1, scalarIntegrand δ v (y, t) := by
    funext y
    rw [radialPrimitive_apply δ y v (radialIntegrand_intervalIntegrable δ hδ y)]
    rfl
  rw [heq, (hasFDerivAt_scalarRadialIntegral δ hδ v z).fderiv]
  have hint : IntervalIntegrable (fun t => scalarPartialFDeriv δ v (z, t)) volume 0 1 :=
    ((scalarPartialFDeriv_contDiff δ hδ v).continuous.comp
      (continuous_const.prodMk continuous_id)).intervalIntegrable 0 1
  rw [ContinuousLinearMap.intervalIntegral_apply hint u]
  congr 1
  funext t
  exact scalarPartialFDeriv_apply δ hδ z u v t

def radialPrimitiveForm (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (z : V) :
    V [⋀^Fin 1]→L[ℝ] ℝ :=
  (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)) (radialPrimitive δ z)

@[simp]
theorem radialPrimitiveForm_apply (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (z v : V) :
    radialPrimitiveForm δ z ![v] = radialPrimitive δ z v := by
  rfl

theorem radialPrimitive_contDiff [FiniteDimensional ℝ V]
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) :
    ContDiff ℝ ∞ (radialPrimitive δ) := by
  change ContDiff ℝ ∞ fun y => ∫ t in (0 : ℝ)..1, radialIntegrand δ y t
  exact parameterIntegral_contDiff (bundledRadialIntegrand δ)
    (bundledRadialIntegrand_contDiff δ hδ)

theorem radialPrimitiveForm_contDiff [FiniteDimensional ℝ V]
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) :
    ContDiff ℝ ∞ (radialPrimitiveForm δ) := by
  unfold radialPrimitiveForm
  exact (ContinuousAlternatingMap.ofSubsingletonLIE
    (𝕜 := ℝ) (E := V) (F := ℝ) (0 : Fin 1)).contDiff.comp
      (radialPrimitive_contDiff δ hδ)

theorem closed_fderiv_identity (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (p r u v : V) (hclosed : extDeriv δ p = 0) :
    fderiv ℝ δ p u ![r, v] - fderiv ℝ δ p v ![r, u] =
      fderiv ℝ δ p r ![u, v] := by
  have h := congrArg (fun η : V [⋀^Fin 3]→L[ℝ] ℝ => η ![r, u, v]) hclosed
  rw [extDeriv_apply ((hδ.differentiable (by simp)) p) (![r, u, v])] at h
  simp only [Fin.sum_univ_succ] at h
  simp at h
  have hremove1 : (1 : Fin 3).removeNth ![r, u, v] = ![r, v] := by
    funext i
    fin_cases i <;> rfl
  have hremove2 : (2 : Fin 3).removeNth ![r, u, v] = ![r, u] := by
    funext i
    fin_cases i <;> rfl
  rw [hremove1, hremove2] at h
  have hδp : DifferentiableAt ℝ δ p := (hδ.differentiable (by simp)) p
  rw [fderiv_continuousAlternatingMap_apply_const_apply hδp ![u, v] r,
    fderiv_continuousAlternatingMap_apply_const_apply hδp ![r, v] u,
    fderiv_continuousAlternatingMap_apply_const_apply hδp ![r, u] v] at h
  linarith

def radialBoundary (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (z u v : V) (t : ℝ) : ℝ :=
  t ^ 2 * δ (t • z) ![u, v]

theorem radialBoundary_hasDerivAt (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (z u v : V) (t : ℝ) :
    HasDerivAt (radialBoundary δ z u v)
      (2 * t * δ (t • z) ![u, v] + t ^ 2 * fderiv ℝ δ (t • z) z ![u, v]) t := by
  have hδdiff : Differentiable ℝ δ := hδ.differentiable (by simp)
  have htz : HasDerivAt (fun s : ℝ => s • z) z t := by
    simpa using (hasDerivAt_id t).smul_const z
  have hc : HasDerivAt (fun s : ℝ => δ (s • z) ![u, v])
      (fderiv ℝ δ (t • z) z ![u, v]) t := by
    have hcomp := (hδdiff (t • z)).hasFDerivAt.comp t htz.hasFDerivAt
    have hc' := (hcomp.continuousAlternatingMap_apply_const ![u, v]).hasDerivAt
    change HasDerivAt (fun s : ℝ => δ (s • z) ![u, v]) _ t at hc'
    apply hc'.congr_deriv
    simp
  unfold radialBoundary
  have hp := ((hasDerivAt_id t).pow 2).mul hc
  change HasDerivAt (fun s : ℝ => s ^ 2 * δ (s • z) ![u, v]) _ t at hp
  apply hp.congr_deriv
  simp

theorem extDeriv_radialPrimitiveForm_apply [FiniteDimensional ℝ V]
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ) (z u v : V) :
    extDeriv (radialPrimitiveForm δ) z ![u, v] =
      ∫ t in (0 : ℝ)..1,
        (t ^ 2 * (fderiv ℝ δ (t • z) u ![z, v] -
          fderiv ℝ δ (t • z) v ![z, u]) + 2 * t * δ (t • z) ![u, v]) := by
  rw [extDeriv_apply (((radialPrimitiveForm_contDiff δ hδ).differentiable (by simp)) z)
    (![u, v])]
  simp only [Fin.sum_univ_succ]
  simp
  have hremove : (1 : Fin 2).removeNth ![u, v] = ![u] := by
    funext i
    fin_cases i
    rfl
  rw [hremove]
  change fderiv ℝ (fun x => radialPrimitive δ x v) z u +
    -fderiv ℝ (fun x => radialPrimitive δ x u) z v = _
  rw [fderiv_radialPrimitive_apply δ hδ z u v,
    fderiv_radialPrimitive_apply δ hδ z v u]
  have hpartialV : Continuous fun t => scalarPartialFDeriv δ v (z, t) u :=
    ((scalarPartialFDeriv_contDiff δ hδ v).continuous.comp
      (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have hpartialU : Continuous fun t => scalarPartialFDeriv δ u (z, t) v :=
    ((scalarPartialFDeriv_contDiff δ hδ u).continuous.comp
      (continuous_const.prodMk continuous_id)).clm_apply continuous_const
  have hAcont : Continuous fun t =>
      t ^ 2 * fderiv ℝ δ (t • z) u ![z, v] + t * δ (t • z) ![u, v] := by
    simpa only [scalarPartialFDeriv_apply δ hδ] using hpartialV
  have hBcont : Continuous fun t =>
      t ^ 2 * fderiv ℝ δ (t • z) v ![z, u] + t * δ (t • z) ![v, u] := by
    simpa only [scalarPartialFDeriv_apply δ hδ] using hpartialU
  have hA : IntervalIntegrable (fun t =>
      t ^ 2 * fderiv ℝ δ (t • z) u ![z, v] + t * δ (t • z) ![u, v]) volume 0 1 :=
    hAcont.intervalIntegrable 0 1
  have hB : IntervalIntegrable (fun t =>
      t ^ 2 * fderiv ℝ δ (t • z) v ![z, u] + t * δ (t • z) ![v, u]) volume 0 1 :=
    hBcont.intervalIntegrable 0 1
  rw [← sub_eq_add_neg, ← intervalIntegral.integral_sub hA hB]
  congr 1
  funext t
  have hswap : ![u, v] ∘ Equiv.swap (0 : Fin 2) 1 = ![v, u] := by
    funext i
    fin_cases i <;> rfl
  have halt := (δ (t • z)).map_swap (v := ![u, v]) (by decide : (0 : Fin 2) ≠ 1)
  rw [hswap] at halt
  have halt' : δ (t • z) ![v, u] = -δ (t • z) ![u, v] := by
    change (δ (t • z)).toAlternatingMap ![v, u] =
      -(δ (t • z)).toAlternatingMap ![u, v]
    exact halt
  rw [halt']
  ring

theorem radialBoundary_contDiff (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ)
    (hδ : ContDiff ℝ ∞ δ) (z u v : V) : ContDiff ℝ ∞ (radialBoundary δ z u v) := by
  have hform : ContDiff ℝ ∞ fun t : ℝ => δ (t • z) := hδ.comp (by fun_prop)
  have heval : ContDiff ℝ ∞ fun t : ℝ => δ (t • z) ![u, v] :=
    (ContinuousAlternatingMap.apply ℝ V ℝ ![u, v]).contDiff.comp hform
  unfold radialBoundary
  exact (contDiff_id.pow 2).mul heval

theorem extDeriv_radialPrimitiveForm_apply_of_closed_segment [FiniteDimensional ℝ V]
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (z u v : V) (hclosed : ∀ t ∈ Icc (0 : ℝ) 1, extDeriv δ (t • z) = 0) :
    extDeriv (radialPrimitiveForm δ) z ![u, v] = δ z ![u, v] := by
  rw [extDeriv_radialPrimitiveForm_apply δ hδ z u v]
  calc
    (∫ t in (0 : ℝ)..1,
        (t ^ 2 * (fderiv ℝ δ (t • z) u ![z, v] -
          fderiv ℝ δ (t • z) v ![z, u]) + 2 * t * δ (t • z) ![u, v])) =
        ∫ t in (0 : ℝ)..1,
          (t ^ 2 * fderiv ℝ δ (t • z) z ![u, v] +
            2 * t * δ (t • z) ![u, v]) := by
      apply intervalIntegral.integral_congr
      intro t _ht
      change t ^ 2 * (fderiv ℝ δ (t • z) u ![z, v] -
        fderiv ℝ δ (t • z) v ![z, u]) + 2 * t * δ (t • z) ![u, v] = _
      have ht : t ∈ Icc (0 : ℝ) 1 := by
        simpa [uIcc_of_le (by norm_num : (0 : ℝ) ≤ 1)] using _ht
      rw [closed_fderiv_identity δ hδ (t • z) z u v (hclosed t ht)]
    _ = ∫ t in (0 : ℝ)..1, deriv (radialBoundary δ z u v) t := by
      apply intervalIntegral.integral_congr
      intro t _ht
      rw [(radialBoundary_hasDerivAt δ hδ z u v t).deriv]
      ring
    _ = radialBoundary δ z u v 1 - radialBoundary δ z u v 0 := by
      exact intervalIntegral.integral_deriv_of_contDiffOn_Icc
        ((radialBoundary_contDiff δ hδ z u v).of_le (by simp)).contDiffOn (by norm_num)
    _ = δ z ![u, v] := by simp [radialBoundary]

theorem extDeriv_radialPrimitiveForm_apply_of_closed [FiniteDimensional ℝ V]
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (hclosed : ∀ p, extDeriv δ p = 0) (z u v : V) :
    extDeriv (radialPrimitiveForm δ) z ![u, v] = δ z ![u, v] :=
  extDeriv_radialPrimitiveForm_apply_of_closed_segment δ hδ
    z u v (fun t _ht => hclosed (t • z))

theorem extDeriv_radialPrimitiveForm_of_closed [FiniteDimensional ℝ V]
    (δ : V → V [⋀^Fin 2]→L[ℝ] ℝ) (hδ : ContDiff ℝ ∞ δ)
    (hclosed : ∀ p, extDeriv δ p = 0) (z : V) :
    extDeriv (radialPrimitiveForm δ) z = δ z := by
  ext m
  have hm : m = ![m 0, m 1] := by
    funext i
    fin_cases i <;> rfl
  rw [hm]
  exact extDeriv_radialPrimitiveForm_apply_of_closed δ hδ hclosed z (m 0) (m 1)

end

end Submission.RadialPrimitive
