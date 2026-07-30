import Submission.LocalForms
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.ContDiff
import Mathlib.Analysis.Calculus.UniformLimitsDeriv
import Mathlib.Analysis.ODE.ExistUnique

open Set Function MeasureTheory Metric Filter
open scoped ContDiff Interval Topology NNReal

namespace Submission.MoserFlow

noncomputable section

universe u

variable {P : Type u} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [FiniteDimensional ℝ P]
variable {W : Type u} [NormedAddCommGroup W] [NormedSpace ℝ W] [CompleteSpace W]

omit [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
  [CompleteSpace W] in
/-- Rewrite a parameter-dependent integral with variable upper endpoint as an integral over
the fixed interval `[0, 1]`. This makes smoothness a direct application of the parameter-integral
lemma proved for the radial primitive. -/
theorem variableIntervalIntegral_eq
    (g : P × ℝ → W) (t₀ : ℝ) (p : P × ℝ) :
    (∫ s in t₀..p.2, g (p.1, s)) =
      ∫ u in (0 : ℝ)..1, (p.2 - t₀) • g (p.1, t₀ + (p.2 - t₀) * u) := by
  rw [intervalIntegral.integral_smul]
  symm
  simpa using intervalIntegral.smul_integral_comp_add_mul
    (fun s => g (p.1, s)) (a := (0 : ℝ)) (b := 1) (p.2 - t₀) t₀

theorem variableIntervalIntegral_contDiff (g : P × ℝ → W)
    (hg : ContDiff ℝ ∞ g) (t₀ : ℝ) :
    ContDiff ℝ ∞ fun p : P × ℝ => ∫ s in t₀..p.2, g (p.1, s) := by
  let rescaled : (P × ℝ) × ℝ → W := fun q =>
    (q.1.2 - t₀) • g (q.1.1, t₀ + (q.1.2 - t₀) * q.2)
  have hrescaled : ContDiff ℝ ∞ rescaled := by
    dsimp [rescaled]
    fun_prop
  have hfixed := Submission.RadialPrimitive.parameterIntegral_contDiff rescaled hrescaled
  simpa only [rescaled, variableIntervalIntegral_eq] using hfixed

variable {V : Type u} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Raw Picard iterates, kept outside the bounded `ODE.FunSpace` subtype so that their dependence
on the initial point can be differentiated. -/
def picardIter (f : ℝ → V → V) (t₀ : ℝ) : ℕ → V → ℝ → V
  | 0 => fun x _ => x
  | n + 1 => fun x t => ODE.picard f t₀ x (picardIter f t₀ n x) t

omit [FiniteDimensional ℝ V] in
@[simp]
theorem picardIter_zero
    (f : ℝ → V → V) (t₀ : ℝ) (x : V) (t : ℝ) :
    picardIter f t₀ 0 x t = x := rfl

omit [FiniteDimensional ℝ V] in
@[simp]
theorem picardIter_succ
    (f : ℝ → V → V) (t₀ : ℝ) (n : ℕ) (x : V) (t : ℝ) :
    picardIter f t₀ (n + 1) x t =
      x + ∫ s in t₀..t, f s (picardIter f t₀ n x s) := rfl

theorem picardIter_contDiff (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t₀ : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ fun p : V × ℝ => picardIter f t₀ n p.1 p.2 := by
  induction n with
  | zero =>
      simp only [picardIter_zero]
      fun_prop
  | succ n ih =>
      let g : V × ℝ → V := fun q => f q.2 (picardIter f t₀ n q.1 q.2)
      have hg : ContDiff ℝ ∞ g := by
        dsimp [g]
        exact hf.comp (contDiff_snd.prodMk ih)
      have hint : ContDiff ℝ ∞ fun p : V × ℝ => ∫ s in t₀..p.2, g (p.1, s) :=
        variableIntervalIntegral_contDiff g hg t₀
      simpa only [picardIter_succ, g] using contDiff_fst.add hint

theorem picardIter_time_contDiff (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t₀ t : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ fun x : V => picardIter f t₀ n x t :=
  (picardIter_contDiff f hf t₀ n).comp (contDiff_id.prodMk contDiff_const)

/-- The derivative in the spatial variable of a time-dependent field, obtained as a partial
derivative of its uncurried form. -/
def spaceFDeriv (f : ℝ → V → V) (p : ℝ × V) : V →L[ℝ] V :=
  fderiv ℝ (uncurry f) p ∘L ContinuousLinearMap.inr ℝ ℝ V

omit [FiniteDimensional ℝ V] in theorem fderiv_timeSlice_eq_spaceFDeriv
    (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t : ℝ) (z : V) :
    fderiv ℝ (f t) z = spaceFDeriv f (t, z) := by
  have h := ((hf.differentiable (by simp)) (t, z)).hasFDerivAt.comp z
    (hasFDerivAt_prodMk_right t z)
  exact h.fderiv

omit [FiniteDimensional ℝ V] in theorem spaceFDeriv_contDiff (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) : ContDiff ℝ ∞ (spaceFDeriv f) := by
  have hD : ContDiff ℝ ∞ (fderiv ℝ (uncurry f)) := hf.fderiv_right (by simp)
  unfold spaceFDeriv
  fun_prop

/-- The field on a tangent vector that governs first derivatives of the flow. -/
def tangentField (f : ℝ → V → V) (t : ℝ) (q : V × (V →L[ℝ] V)) :
    V × (V →L[ℝ] V) :=
  (f t q.1, (spaceFDeriv f (t, q.1)).comp q.2)

omit [FiniteDimensional ℝ V] in theorem tangentField_contDiff (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) :
    ContDiff ℝ ∞ (uncurry (tangentField f)) := by
  have hfield : ContDiff ℝ ∞ fun p : ℝ × (V × (V →L[ℝ] V)) => f p.1 p.2.1 :=
    hf.comp (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  have hspace : ContDiff ℝ ∞ fun p : ℝ × (V × (V →L[ℝ] V)) =>
      spaceFDeriv f (p.1, p.2.1) :=
    (spaceFDeriv_contDiff f hf).comp
      (contDiff_fst.prodMk (contDiff_fst.comp contDiff_snd))
  have hA : ContDiff ℝ ∞ fun p : ℝ × (V × (V →L[ℝ] V)) => p.2.2 :=
    contDiff_snd.comp contDiff_snd
  exact hfield.prodMk (hspace.clm_comp hA)

def picardIntegrand (f : ℝ → V → V) (t₀ : ℝ) (n : ℕ) (p : V × ℝ) : V :=
  f p.2 (picardIter f t₀ n p.1 p.2)

theorem picardIntegrand_contDiff (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t₀ : ℝ) (n : ℕ) :
    ContDiff ℝ ∞ (picardIntegrand f t₀ n) := by
  unfold picardIntegrand
  exact hf.comp (contDiff_snd.prodMk (picardIter_contDiff f hf t₀ n))

theorem parameterPartialFDeriv_picardIntegrand (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t₀ : ℝ) (n : ℕ) (x : V) (s : ℝ) :
    Submission.RadialPrimitive.parameterPartialFDeriv (picardIntegrand f t₀ n) (x, s) =
      (spaceFDeriv f (s, picardIter f t₀ n x s)).comp
        (fderiv ℝ (fun y => picardIter f t₀ n y s) x) := by
  have hg := picardIntegrand_contDiff f hf t₀ n
  have hleft : HasFDerivAt (fun y : V => (y, s))
      (ContinuousLinearMap.inl ℝ V ℝ) x := hasFDerivAt_prodMk_left x s
  have hpartial : HasFDerivAt
      (fun y => picardIntegrand f t₀ n (y, s))
      (Submission.RadialPrimitive.parameterPartialFDeriv
        (picardIntegrand f t₀ n) (x, s)) x := by
    have hraw := ((hg.differentiable (by simp)) (x, s)).hasFDerivAt.comp x hleft
    exact hraw.congr_of_eventuallyEq (Filter.Eventually.of_forall fun _ => rfl)
  have hslice : HasFDerivAt (f s)
      (spaceFDeriv f (s, picardIter f t₀ n x s)) (picardIter f t₀ n x s) := by
    rw [← fderiv_timeSlice_eq_spaceFDeriv f hf]
    exact ((hf.comp (contDiff_const.prodMk contDiff_id)).differentiable (by simp)
      (picardIter f t₀ n x s)).hasFDerivAt
  have hPn : HasFDerivAt (fun y => picardIter f t₀ n y s)
      (fderiv ℝ (fun y => picardIter f t₀ n y s) x) x :=
    ((picardIter_time_contDiff f hf t₀ s n).differentiable (by simp) x).hasFDerivAt
  have hchain := hslice.comp x hPn
  simpa [picardIntegrand] using hpartial.fderiv.symm.trans hchain.fderiv

theorem fderiv_picardIter_succ (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t₀ : ℝ) (n : ℕ) (x : V) (t : ℝ) :
    fderiv ℝ (fun y => picardIter f t₀ (n + 1) y t) x =
      ContinuousLinearMap.id ℝ V +
        ∫ s in t₀..t, (spaceFDeriv f (s, picardIter f t₀ n x s)).comp
          (fderiv ℝ (fun y => picardIter f t₀ n y s) x) := by
  have hg := picardIntegrand_contDiff f hf t₀ n
  have hint := Submission.RadialPrimitive.parameter_hasFDerivAt_interval
    (picardIntegrand f t₀ n) hg x t₀ t
  have hsum := (hasFDerivAt_id x).add hint
  have hfun : (fun y => picardIter f t₀ (n + 1) y t) =
      id + fun y => ∫ s in t₀..t, picardIntegrand f t₀ n (y, s) := by
    funext y
    simp only [Pi.add_apply, id_eq, picardIter_succ, picardIntegrand]
  rw [hfun, hsum.fderiv]
  congr 1
  apply intervalIntegral.integral_congr
  intro s _hs
  exact parameterPartialFDeriv_picardIntegrand f hf t₀ n x s

theorem picardIter_tangentField (f : ℝ → V → V)
    (hf : ContDiff ℝ ∞ (uncurry f)) (t₀ : ℝ) (n : ℕ) (x : V) (t : ℝ) :
    picardIter (tangentField f) t₀ n (x, ContinuousLinearMap.id ℝ V) t =
      (picardIter f t₀ n x t, fderiv ℝ (fun y => picardIter f t₀ n y t) x) := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      rw [picardIter_succ, picardIter_succ, fderiv_picardIter_succ f hf]
      have hprev : ContDiff ℝ ∞ fun s =>
          picardIter (tangentField f) t₀ n (x, ContinuousLinearMap.id ℝ V) s :=
        (picardIter_contDiff (tangentField f) (tangentField_contDiff f hf) t₀ n).comp
          (contDiff_const.prodMk contDiff_id)
      have hintegrand : IntervalIntegrable (fun s =>
          tangentField f s
            (picardIter (tangentField f) t₀ n
              (x, ContinuousLinearMap.id ℝ V) s)) volume t₀ t :=
        ((tangentField_contDiff f hf).comp
          (contDiff_id.prodMk hprev)).continuous.intervalIntegrable t₀ t
      apply Prod.ext
      · change x + (ContinuousLinearMap.fst ℝ V (V →L[ℝ] V))
            (∫ s in t₀..t, tangentField f s
              (picardIter (tangentField f) t₀ n
                (x, ContinuousLinearMap.id ℝ V) s)) =
          x + ∫ s in t₀..t, f s (picardIter f t₀ n x s)
        rw [← (ContinuousLinearMap.fst ℝ V (V →L[ℝ] V)).intervalIntegral_comp_comm
          hintegrand]
        congr 1
        apply intervalIntegral.integral_congr
        intro s _hs
        change (tangentField f s (picardIter (tangentField f) t₀ n
          (x, ContinuousLinearMap.id ℝ V) s)).1 = f s (picardIter f t₀ n x s)
        rw [ih s]
        rfl
      · change ContinuousLinearMap.id ℝ V +
            (ContinuousLinearMap.snd ℝ V (V →L[ℝ] V))
              (∫ s in t₀..t, tangentField f s
                (picardIter (tangentField f) t₀ n
                  (x, ContinuousLinearMap.id ℝ V) s)) =
          ContinuousLinearMap.id ℝ V +
            ∫ s in t₀..t, (spaceFDeriv f (s, picardIter f t₀ n x s)).comp
              (fderiv ℝ (fun y => picardIter f t₀ n y s) x)
        rw [← (ContinuousLinearMap.snd ℝ V (V →L[ℝ] V)).intervalIntegral_comp_comm
          hintegrand]
        congr 1
        apply intervalIntegral.integral_congr
        intro s _hs
        change (tangentField f s (picardIter (tangentField f) t₀ n
          (x, ContinuousLinearMap.id ℝ V) s)).2 =
            (spaceFDeriv f (s, picardIter f t₀ n x s)).comp
              (fderiv ℝ (fun y => picardIter f t₀ n y s) x)
        rw [ih s]
        rfl

section PicardLimit

variable {f : ℝ → V → V} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
  {x₀ x : V} {a r L K : ℝ≥0}

/-- The constant curve at an admissible initial point, used as the zeroth raw Picard iterate. -/
def constantCurve (hx : x ∈ closedBall x₀ r) : ODE.FunSpace t₀ x₀ r L where
  toFun := fun _ => x
  lipschitzWith := (LipschitzWith.const _).weaken zero_le
  mem_closedBall₀ := hx

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in
@[simp]
theorem constantCurve_apply (hx : x ∈ closedBall x₀ r) (t : Icc tmin tmax) :
    constantCurve (t₀ := t₀) (L := L) hx t = x := rfl

/-- A selected Picard fixed point. Uniqueness makes all later properties independent of the
particular classical choice. -/
def solutionCurve (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) : ODE.FunSpace t₀ x₀ r L :=
  Classical.choose (ODE.FunSpace.exists_isFixedPt_next hpl hx)

theorem solutionCurve_isFixedPt (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) :
    IsFixedPt (ODE.FunSpace.next hpl hx) (solutionCurve hpl hx) :=
  Classical.choose_spec (ODE.FunSpace.exists_isFixedPt_next hpl hx)

theorem solutionCurve_initial (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) : solutionCurve hpl hx t₀ = x := by
  rw [← solutionCurve_isFixedPt hpl hx, ODE.FunSpace.next_apply₀]

theorem solutionCurve_hasDerivWithinAt
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (t : Icc tmin tmax) :
    HasDerivWithinAt (solutionCurve hpl hx).compProj
      (f t (solutionCurve hpl hx t)) (Icc tmin tmax) t := by
  have hfixed := solutionCurve_isFixedPt hpl hx
  have hderiv : HasDerivWithinAt (solutionCurve hpl hx).compProj
      (f t ((solutionCurve hpl hx).compProj t)) (Icc tmin tmax) t := by
    apply ODE.hasDerivWithinAt_picard_Icc t₀.2 hpl.continuousOn_uncurry
      (solutionCurve hpl hx).continuous_compProj.continuousOn
      (fun _ hs => (solutionCurve hpl hx).compProj_mem_closedBall hpl.mul_max_le)
      x t.2 |>.congr_of_mem _ t.2
    intro s hs
    nth_rw 1 [← hfixed]
    rw [ODE.FunSpace.compProj_of_mem hs, ODE.FunSpace.next_apply]
  simpa only [ODE.FunSpace.compProj_val] using hderiv

open Classical in
/-- A total representative of the selected flow at a fixed time. Only its values on the
admissible initial ball are used. -/
def solutionAt (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (t : Icc tmin tmax) (x : V) : V :=
  if hx : x ∈ closedBall x₀ r then solutionCurve hpl hx t else 0

@[simp]
theorem solutionAt_of_mem (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (t : Icc tmin tmax) (hx : x ∈ closedBall x₀ r) :
    solutionAt hpl t x = solutionCurve hpl hx t := by
  simp [solutionAt, hx]

theorem solutionAt_initial (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) : solutionAt hpl t₀ x = x := by
  rw [solutionAt_of_mem hpl t₀ hx, solutionCurve_initial]

theorem solutionAt_eq_of_equilibrium
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (hzero : ∀ t : ℝ, f t x = 0)
    (t : Icc tmin tmax) : solutionAt hpl t x = x := by
  have hconst : IsFixedPt (ODE.FunSpace.next hpl hx)
      (constantCurve (t₀ := t₀) (L := L) hx) := by
    rw [ODE.FunSpace.isFixedPt_next_iff]
    intro s
    rw [ODE.picard_apply]
    simp [constantCurve, ODE.FunSpace.compProj, hzero]
  obtain ⟨m, C, hcontract⟩ := ODE.FunSpace.exists_contractingWith_iterate_next hpl
  have hcurves : solutionCurve hpl hx = constantCurve (t₀ := t₀) (L := L) hx :=
    (hcontract x hx).fixedPoint_unique'
      ((solutionCurve_isFixedPt hpl hx).iterate m) (hconst.iterate m)
  rw [solutionAt_of_mem hpl t hx, hcurves]
  rfl

theorem solutionAt_hasDerivWithinAt_time
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (t : Icc tmin tmax) :
    HasDerivWithinAt (fun s : ℝ => solutionAt hpl
      (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) s) x)
      (f t (solutionAt hpl t x)) (Icc tmin tmax) t := by
  have heq : (fun s : ℝ => solutionAt hpl
      (projIcc tmin tmax (le_trans t₀.2.1 t₀.2.2) s) x) =
      (solutionCurve hpl hx).compProj := by
    funext s
    rw [solutionAt_of_mem hpl _ hx]
    rfl
  rw [heq, solutionAt_of_mem hpl t hx]
  exact solutionCurve_hasDerivWithinAt hpl hx t

omit [NormedSpace ℝ V] [FiniteDimensional ℝ V] in theorem funSpace_dist_le_two_radius
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (α β : ODE.FunSpace t₀ x₀ r L) : dist α β ≤ 2 * (a : ℝ) := by
  rw [← MetricSpace.isometry_induced ODE.FunSpace.toContinuousMap
    ODE.FunSpace.toContinuousMap.injective |>.dist_eq, ContinuousMap.dist_le]
  · intro t
    calc
      dist (α t) (β t) ≤ dist (α t) x₀ + dist (β t) x₀ := dist_triangle_right _ _ _
      _ ≤ (a : ℝ) + a := add_le_add
        (mem_closedBall.mp (α.mem_closedBall hpl.mul_max_le))
        (mem_closedBall.mp (β.mem_closedBall hpl.mul_max_le))
      _ = 2 * (a : ℝ) := by ring
  · positivity

omit [FiniteDimensional ℝ V] in theorem iterate_next_constantCurve_apply
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (n : ℕ) (t : Icc tmin tmax) :
    ((ODE.FunSpace.next hpl hx)^[n] (constantCurve (t₀ := t₀) (L := L) hx)) t =
      picardIter f t₀ n x t := by
  induction n generalizing t with
  | zero => simp
  | succ n ih =>
      rw [iterate_succ_apply', ODE.FunSpace.next_apply]
      simp only [ODE.picard_apply, picardIter_succ]
      congr 1
      apply intervalIntegral.integral_congr
      intro s hs
      have hsIcc : s ∈ Icc tmin tmax := uIcc_subset_Icc t₀.2 t.2 hs
      change f s (((ODE.FunSpace.next hpl hx)^[n]
        (constantCurve (t₀ := t₀) (L := L) hx)).compProj s) =
          f s (picardIter f t₀ n x s)
      rw [ODE.FunSpace.compProj_of_mem hsIcc, ih ⟨s, hsIcc⟩]

theorem picardIter_tendsto_solutionCurve
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (hx : x ∈ closedBall x₀ r) (t : Icc tmin tmax) :
    Tendsto (fun n => picardIter f t₀ n x t) atTop (𝓝 (solutionCurve hpl hx t)) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (g := fun n =>
      ((K : ℝ) * |(t : ℝ) - (t₀ : ℝ)|) ^ n / (Nat.factorial n : ℝ) *
        dist (constantCurve (t₀ := t₀) (L := L) hx) (solutionCurve hpl hx))
    (fun _ => dist_nonneg) ?_ ?_
  · intro n
    rw [← iterate_next_constantCurve_apply hpl hx n t]
    have hbound := ODE.FunSpace.dist_iterate_next_apply_le hpl hx
      (constantCurve (t₀ := t₀) (L := L) hx) (solutionCurve hpl hx) n t
    rw [(solutionCurve_isFixedPt hpl hx).iterate n] at hbound
    exact hbound
  · have hfactor :=
      FloorSemiring.tendsto_pow_div_factorial_atTop (K * |(t : ℝ) - (t₀ : ℝ)|)
    simpa using hfactor.mul_const
      (dist (constantCurve (t₀ := t₀) (L := L) hx) (solutionCurve hpl hx))

theorem picardIter_tendstoUniformlyOn_solutionAt
    (hpl : IsPicardLindelof f t₀ x₀ a r L K) (t : Icc tmin tmax) :
    TendstoUniformlyOn (fun n x => picardIter f t₀ n x t) (solutionAt hpl t)
      atTop (closedBall x₀ r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have hfactor :=
    FloorSemiring.tendsto_pow_div_factorial_atTop (K * |(t : ℝ) - (t₀ : ℝ)|)
  have hbound : Tendsto (fun n =>
      ((K : ℝ) * |(t : ℝ) - (t₀ : ℝ)|) ^ n / (Nat.factorial n : ℝ) *
        (2 * (a : ℝ))) atTop (𝓝 0) := by
    simpa using hfactor.mul_const (2 * (a : ℝ))
  refine ((tendsto_order.1 hbound).2 ε hε).mono fun n hn x hx => ?_
  rw [solutionAt_of_mem hpl t hx, ← iterate_next_constantCurve_apply hpl hx n t,
    dist_comm]
  have hiterate := ODE.FunSpace.dist_iterate_next_apply_le hpl hx
    (constantCurve (t₀ := t₀) (L := L) hx) (solutionCurve hpl hx) n t
  rw [(solutionCurve_isFixedPt hpl hx).iterate n] at hiterate
  exact lt_of_le_of_lt (hiterate.trans <| mul_le_mul_of_nonneg_left
    (funSpace_dist_le_two_radius hpl _ _) (by positivity)) hn

def solutionFDerivAt
    {aT LT KT : ℝ≥0}
    (hplT : IsPicardLindelof (tangentField f) t₀
      (x₀, ContinuousLinearMap.id ℝ V) aT r LT KT)
    (t : Icc tmin tmax) (x : V) : V →L[ℝ] V :=
  (solutionAt hplT t (x, ContinuousLinearMap.id ℝ V)).2

omit [FiniteDimensional ℝ V] in theorem tangentInitial_mem_closedBall
    (hx : x ∈ closedBall x₀ r) :
    (x, ContinuousLinearMap.id ℝ V) ∈
      closedBall (x₀, ContinuousLinearMap.id ℝ V) r := by
  simpa [mem_closedBall, Prod.dist_eq] using hx

theorem fderiv_picardIter_tendstoUniformlyOn_solutionFDerivAt
    (hf : ContDiff ℝ ∞ (uncurry f))
    {aT LT KT : ℝ≥0}
    (hplT : IsPicardLindelof (tangentField f) t₀
      (x₀, ContinuousLinearMap.id ℝ V) aT r LT KT)
    (t : Icc tmin tmax) :
    TendstoUniformlyOn
      (fun n x => fderiv ℝ (fun y => picardIter f t₀ n y t) x)
      (solutionFDerivAt hplT t) atTop (closedBall x₀ r) := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  have htan := Metric.tendstoUniformlyOn_iff.mp
    (picardIter_tendstoUniformlyOn_solutionAt hplT t) ε hε
  filter_upwards [htan] with n hn
  intro x hx
  have hxT := tangentInitial_mem_closedBall (V := V) hx
  change dist (solutionAt hplT t (x, ContinuousLinearMap.id ℝ V)).2
    (fderiv ℝ (fun y => picardIter f t₀ n y t) x) < ε
  have hsecond :
      (picardIter (tangentField f) t₀ n
        (x, ContinuousLinearMap.id ℝ V) t).2 =
        fderiv ℝ (fun y => picardIter f t₀ n y t) x :=
    congrArg Prod.snd (picardIter_tangentField f hf t₀ n x t)
  rw [← hsecond]
  calc
    dist (solutionAt hplT t (x, ContinuousLinearMap.id ℝ V)).2
        (picardIter (tangentField f) t₀ n
          (x, ContinuousLinearMap.id ℝ V) t).2 ≤
        max
          (dist (solutionAt hplT t (x, ContinuousLinearMap.id ℝ V)).1
            (picardIter (tangentField f) t₀ n
              (x, ContinuousLinearMap.id ℝ V) t).1)
          (dist (solutionAt hplT t (x, ContinuousLinearMap.id ℝ V)).2
            (picardIter (tangentField f) t₀ n
              (x, ContinuousLinearMap.id ℝ V) t).2) := le_max_right _ _
    _ = dist (solutionAt hplT t (x, ContinuousLinearMap.id ℝ V))
        (picardIter (tangentField f) t₀ n
          (x, ContinuousLinearMap.id ℝ V) t) := rfl
    _ < ε := hn _ hxT

theorem solutionAt_hasFDerivAt
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    {aT LT KT : ℝ≥0}
    (hplT : IsPicardLindelof (tangentField f) t₀
      (x₀, ContinuousLinearMap.id ℝ V) aT r LT KT)
    (t : Icc tmin tmax) {x : V} (hx : x ∈ ball x₀ r) :
    HasFDerivAt (solutionAt hpl t) (solutionFDerivAt hplT t x) x := by
  apply hasFDerivAt_of_tendstoUniformlyOn isOpen_ball
    ((fderiv_picardIter_tendstoUniformlyOn_solutionFDerivAt hf hplT t).mono
      ball_subset_closedBall)
  · intro n y _hy
    exact ((picardIter_time_contDiff f hf t₀ t n).differentiable (by simp) y).hasFDerivAt
  · intro y hy
    exact (picardIter_tendstoUniformlyOn_solutionAt hpl t).tendsto_at
      (ball_subset_closedBall hy)
  · exact hx

theorem solutionAt_contDiffOn_one
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    {aT LT KT : ℝ≥0}
    (hplT : IsPicardLindelof (tangentField f) t₀
      (x₀, ContinuousLinearMap.id ℝ V) aT r LT KT)
    (t : Icc tmin tmax) :
    ContDiffOn ℝ 1 (solutionAt hpl t) (ball x₀ r) := by
  have h : ContDiffOn ℝ ((0 : ℕ∞ω) + 1) (solutionAt hpl t) (ball x₀ r) := by
    rw [contDiffOn_succ_iff_fderivWithin isOpen_ball.uniqueDiffOn]
    refine ⟨?_, by simp, ?_⟩
    · intro x hx
      exact (solutionAt_hasFDerivAt hf hpl hplT t hx).differentiableAt.differentiableWithinAt
    · apply contDiffOn_zero.mpr
      have hcontinuous : ContinuousOn (solutionFDerivAt hplT t) (closedBall x₀ r) :=
        (fderiv_picardIter_tendstoUniformlyOn_solutionFDerivAt hf hplT t).continuousOn
          (Frequently.of_forall fun n =>
            ((picardIter_time_contDiff f hf t₀ t n).fderiv_right (m := 0)
              (by
                change (1 : ℕ∞ω) ≤ ∞
                exact ENat.LEInfty.out)).continuous.continuousOn)
      refine (hcontinuous.mono ball_subset_closedBall).congr fun x hx => ?_
      rw [fderivWithin_of_isOpen isOpen_ball hx]
      exact (solutionAt_hasFDerivAt hf hpl hplT t hx).fderiv
  simpa using h

theorem exists_local_isPicardLindelof
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (f : ℝ → X → X) (hf : ContDiff ℝ ∞ (uncurry f))
    (tcenter : ℝ) (xcenter : X) (r : ℝ≥0) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ a L K : ℝ≥0,
      IsPicardLindelof f
        (tmin := tcenter - ε) (tmax := tcenter + ε)
        ⟨tcenter, by constructor <;> linarith⟩ xcenter a r L K := by
  let a : ℝ≥0 := r + 1
  let Q : Set (ℝ × X) := Icc (tcenter - 1) (tcenter + 1) ×ˢ closedBall xcenter a
  have hQ : IsCompact Q := isCompact_Icc.prod (isCompact_closedBall xcenter a)
  have hfield : Continuous (uncurry f) := hf.continuous
  have hfieldImage : IsCompact (uncurry f '' Q) := hQ.image hfield
  obtain ⟨C, hC⟩ := hfieldImage.isBounded.exists_norm_le
  have hcenterQ : (tcenter, xcenter) ∈ Q := by
    constructor
    · constructor <;> linarith
    · exact mem_closedBall_self (by positivity)
  have hC0 : 0 ≤ C :=
    norm_nonneg (f tcenter xcenter) |>.trans
      (hC (f tcenter xcenter) ⟨(tcenter, xcenter), hcenterQ, rfl⟩)
  let L : ℝ≥0 := ⟨C, hC0⟩
  have hspace : Continuous (spaceFDeriv f) := (spaceFDeriv_contDiff f hf).continuous
  have hspaceImage : IsCompact (spaceFDeriv f '' Q) := hQ.image hspace
  obtain ⟨D, hD⟩ := hspaceImage.isBounded.exists_norm_le
  have hD0 : 0 ≤ D :=
    norm_nonneg (spaceFDeriv f (tcenter, xcenter)) |>.trans
      (hD (spaceFDeriv f (tcenter, xcenter))
        ⟨(tcenter, xcenter), hcenterQ, rfl⟩)
  let K : ℝ≥0 := ⟨D, hD0⟩
  let ε : ℝ := 1 / (2 * ((L : ℝ) + 1))
  have hε : 0 < ε := by
    dsimp [ε]
    positivity
  have hεle : ε ≤ 1 := by
    dsimp [ε]
    apply (div_le_one (by positivity : (0 : ℝ) < 2 * ((L : ℝ) + 1))).2
    nlinarith [L.coe_nonneg]
  refine ⟨ε, hε, a, L, K, ?_⟩
  refine {
    lipschitzOnWith := ?_
    continuousOn := ?_
    norm_le := ?_
    mul_max_le := ?_ }
  · intro t ht
    have htQ : t ∈ Icc (tcenter - 1) (tcenter + 1) := by
      constructor <;> linarith [ht.1, ht.2, hεle]
    apply (convex_closedBall xcenter (a : ℝ)).lipschitzOnWith_of_nnnorm_fderiv_le
      (𝕜 := ℝ)
    · intro x _hx
      have htDiff : ContDiff ℝ ∞ (fun y : X => f t y) :=
        hf.comp (contDiff_const.prodMk contDiff_id)
      exact (htDiff.differentiable (by simp)) x
    · intro x hx
      change ‖fderiv ℝ (fun y : X => f t y) x‖ ≤ D
      rw [fderiv_timeSlice_eq_spaceFDeriv f hf]
      exact hD (spaceFDeriv f (t, x)) ⟨(t, x), ⟨htQ, hx⟩, rfl⟩
  · intro x _hx
    exact (hf.continuous.comp (continuous_id.prodMk continuous_const)).continuousOn
  · intro t ht x hx
    have htQ : t ∈ Icc (tcenter - 1) (tcenter + 1) := by
      constructor <;> linarith [ht.1, ht.2, hεle]
    exact hC (f t x) ⟨(t, x), ⟨htQ, hx⟩, rfl⟩
  · simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
    have hden : (0 : ℝ) < 2 * ((L : ℝ) + 1) := by positivity
    have hgap : (a : ℝ) - (r : ℝ) = 1 := by simp [a]
    rw [hgap]
    dsimp [ε]
    rw [mul_one_div]
    exact (div_le_one hden).2 (by nlinarith [L.coe_nonneg])

/-- Picard–Lindelöf data for successive tangent equations. A tail of depth `k` is precisely the
extra existence input needed to prove that the base time map is `C^k`. -/
def HasPicardTail {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X] (f : ℝ → X → X) {tmin tmax : ℝ}
    (t₀ : Icc tmin tmax) (x₀ : X) (r : ℝ≥0) : ℕ → Prop
  | 0 => True
  | n + 1 => ∃ aT LT KT : ℝ≥0,
      IsPicardLindelof (tangentField f) t₀
        (x₀, ContinuousLinearMap.id ℝ X) aT r LT KT ∧
      HasPicardTail (X := X × (X →L[ℝ] X)) (tangentField f) t₀
        (x₀, ContinuousLinearMap.id ℝ X) r n

theorem HasPicardTail.shrink_time
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {f : ℝ → X → X} {tmin tmax tmin' tmax' : ℝ}
    {t₀ : Icc tmin tmax} (t₀' : Icc tmin' tmax')
    (ht₀ : (t₀ : ℝ) = t₀') (htmin : tmin ≤ tmin') (htmax : tmax' ≤ tmax)
    {x₀ : X} {r : ℝ≥0} {n : ℕ} (h : HasPicardTail f t₀ x₀ r n) :
    HasPicardTail f t₀' x₀ r n := by
  cases n with
  | zero => trivial
  | succ n =>
      change ∃ aT LT KT : ℝ≥0,
        IsPicardLindelof (tangentField f) t₀
          (x₀, ContinuousLinearMap.id ℝ X) aT r LT KT ∧
        HasPicardTail (X := X × (X →L[ℝ] X)) (tangentField f) t₀
          (x₀, ContinuousLinearMap.id ℝ X) r n at h
      obtain ⟨aT, LT, KT, hplT, htail⟩ := h
      refine ⟨aT, LT, KT, hplT.shrink_time t₀' ht₀ htmin htmax, ?_⟩
      exact HasPicardTail.shrink_time
        (X := X × (X →L[ℝ] X)) (f := tangentField f) (n := n)
        t₀' ht₀ htmin htmax htail
termination_by n

theorem HasPicardTail.shrink
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {f : ℝ → X → X} {tmin tmax tmin' tmax' : ℝ}
    {t₀ : Icc tmin tmax} (t₀' : Icc tmin' tmax')
    (htmin : tmin ≤ tmin') (htmax : tmax' ≤ tmax)
    (hspan : max (tmax' - t₀') (t₀' - tmin') ≤
      max (tmax - t₀) (t₀ - tmin))
    {x₀ : X} {r : ℝ≥0} {n : ℕ} (h : HasPicardTail f t₀ x₀ r n) :
    HasPicardTail f t₀' x₀ r n := by
  cases n with
  | zero => trivial
  | succ n =>
      change ∃ aT LT KT : ℝ≥0,
        IsPicardLindelof (tangentField f) t₀
          (x₀, ContinuousLinearMap.id ℝ X) aT r LT KT ∧
        HasPicardTail (X := X × (X →L[ℝ] X)) (tangentField f) t₀
          (x₀, ContinuousLinearMap.id ℝ X) r n at h
      obtain ⟨aT, LT, KT, hplT, htail⟩ := h
      have htime : (LT : ℝ) * max (tmax' - t₀') (t₀' - tmin') ≤
          (aT : ℝ) - (r : ℝ) :=
        (mul_le_mul_of_nonneg_left hspan LT.coe_nonneg).trans hplT.mul_max_le
      refine ⟨aT, LT, KT, hplT.shrink t₀' htmin htmax le_rfl htime, ?_⟩
      exact HasPicardTail.shrink
        (X := X × (X →L[ℝ] X)) (f := tangentField f) (n := n)
        t₀' htmin htmax hspan htail
termination_by n

theorem exists_local_picardTower
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (f : ℝ → X → X) (hf : ContDiff ℝ ∞ (uncurry f))
    (tcenter : ℝ) (xcenter : X) (r : ℝ≥0) (n : ℕ) :
    ∃ ε : ℝ, ∃ hε : 0 < ε, ∃ a L K : ℝ≥0,
      IsPicardLindelof f
        (tmin := tcenter - ε) (tmax := tcenter + ε)
        ⟨tcenter, by constructor <;> linarith⟩ xcenter a r L K ∧
      HasPicardTail f
        (tmin := tcenter - ε) (tmax := tcenter + ε)
        ⟨tcenter, by constructor <;> linarith⟩ xcenter r n := by
  cases n with
  | zero =>
      obtain ⟨ε, hε, a, L, K, hpl⟩ :=
        exists_local_isPicardLindelof f hf tcenter xcenter r
      exact ⟨ε, hε, a, L, K, hpl, trivial⟩
  | succ n =>
      obtain ⟨εB, hεB, aB, LB, KB, hplB⟩ :=
        exists_local_isPicardLindelof f hf tcenter xcenter r
      obtain ⟨εT, hεT, aT, LT, KT, hplT, htailT⟩ :=
        exists_local_picardTower
          (X := X × (X →L[ℝ] X)) (tangentField f)
          (tangentField_contDiff f hf) tcenter
          (xcenter, ContinuousLinearMap.id ℝ X) r n
      let ε := min εB εT
      have hε : 0 < ε := lt_min hεB hεT
      let t₀ : Icc (tcenter - ε) (tcenter + ε) :=
        ⟨tcenter, by constructor <;> linarith⟩
      have hBmin : tcenter - εB ≤ tcenter - ε := by
        dsimp [ε]
        linarith [min_le_left εB εT]
      have hBmax : tcenter + ε ≤ tcenter + εB := by
        dsimp [ε]
        linarith [min_le_left εB εT]
      have hTmin : tcenter - εT ≤ tcenter - ε := by
        dsimp [ε]
        linarith [min_le_right εB εT]
      have hTmax : tcenter + ε ≤ tcenter + εT := by
        dsimp [ε]
        linarith [min_le_right εB εT]
      have hplB' := hplB.shrink_time t₀ rfl hBmin hBmax
      have hplT' := hplT.shrink_time t₀ rfl hTmin hTmax
      have htailT' := HasPicardTail.shrink_time
        (tmin := tcenter - εT) (tmax := tcenter + εT)
        (tmin' := tcenter - ε) (tmax' := tcenter + ε)
        t₀ rfl hTmin hTmax htailT
      refine ⟨ε, hε, aB, LB, KB, hplB', ?_⟩
      exact ⟨aT, LT, KT, hplT', htailT'⟩

structure PicardTowerData
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (f : ℝ → X → X) (tcenter : ℝ) (xcenter : X) (r : ℝ≥0) (n : ℕ) where
  ε : ℝ
  hε : 0 < ε
  a : ℝ≥0
  L : ℝ≥0
  K : ℝ≥0
  hpl : IsPicardLindelof f
    (tmin := tcenter - ε) (tmax := tcenter + ε)
    ⟨tcenter, by constructor <;> linarith⟩ xcenter a r L K
  tail : HasPicardTail f
    (tmin := tcenter - ε) (tmax := tcenter + ε)
    ⟨tcenter, by constructor <;> linarith⟩ xcenter r n

theorem exists_picardTowerData
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (f : ℝ → X → X) (hf : ContDiff ℝ ∞ (uncurry f))
    (tcenter : ℝ) (xcenter : X) (r : ℝ≥0) (n : ℕ) :
    Nonempty (PicardTowerData f tcenter xcenter r n) := by
  obtain ⟨ε, hε, a, L, K, hpl, htail⟩ :=
    exists_local_picardTower f hf tcenter xcenter r n
  exact ⟨⟨ε, hε, a, L, K, hpl, htail⟩⟩

noncomputable def localPicardTowerData
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (f : ℝ → X → X) (hf : ContDiff ℝ ∞ (uncurry f))
    (tcenter : ℝ) (xcenter : X) (r : ℝ≥0) (n : ℕ) :
    PicardTowerData f tcenter xcenter r n :=
  Classical.choice (exists_picardTowerData f hf tcenter xcenter r n)

structure PicardStepData
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    (f : ℝ → X → X) (tmin tmax : ℝ) (xcenter : X) (r : ℝ≥0) (n : ℕ) where
  htime : tmin ≤ tmax
  a : ℝ≥0
  L : ℝ≥0
  K : ℝ≥0
  hpl : IsPicardLindelof f
    (tmin := tmin) (tmax := tmax)
    ⟨tmin, by exact ⟨le_rfl, htime⟩⟩ xcenter a r L K
  tail : HasPicardTail f
    (tmin := tmin) (tmax := tmax)
    ⟨tmin, by exact ⟨le_rfl, htime⟩⟩ xcenter r n

def PicardTowerData.toStep
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {f : ℝ → X → X} {tcenter : ℝ} {xcenter : X} {r : ℝ≥0} {n : ℕ}
    (d : PicardTowerData f tcenter xcenter r n)
    {tmin tmax : ℝ} (htime : tmin ≤ tmax)
    (hmin : tcenter - d.ε ≤ tmin) (hmax : tmax ≤ tcenter + d.ε)
    (hspan : max (tmax - tmin) (tmin - tmin) ≤
      max ((tcenter + d.ε) - tcenter) (tcenter - (tcenter - d.ε))) :
    PicardStepData f tmin tmax xcenter r n := by
  let t₀' : Icc tmin tmax := ⟨tmin, by exact ⟨le_rfl, htime⟩⟩
  have hbound : (d.L : ℝ) * max (tmax - t₀') (t₀' - tmin) ≤
      (d.a : ℝ) - (r : ℝ) :=
    (mul_le_mul_of_nonneg_left hspan d.L.coe_nonneg).trans d.hpl.mul_max_le
  exact {
    htime := htime
    a := d.a
    L := d.L
    K := d.K
    hpl := d.hpl.shrink t₀' hmin hmax le_rfl hbound
    tail := HasPicardTail.shrink t₀' hmin hmax hspan d.tail }

def PicardStepData.endTime
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {f : ℝ → X → X} {tmin tmax : ℝ} {xcenter : X} {r : ℝ≥0} {n : ℕ}
    (d : PicardStepData f tmin tmax xcenter r n) : Icc tmin tmax :=
  ⟨tmax, by exact ⟨d.htime, le_rfl⟩⟩

def PicardStepData.map
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {f : ℝ → X → X} {tmin tmax : ℝ} {xcenter : X} {r : ℝ≥0} {n : ℕ}
    (d : PicardStepData f tmin tmax xcenter r n) (x : X) : X :=
  solutionAt d.hpl d.endTime x

theorem solutionAt_contDiffOn_zero
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (t : Icc tmin tmax) :
    ContDiffOn ℝ 0 (solutionAt hpl t) (ball x₀ r) := by
  apply contDiffOn_zero.mpr
  exact ((picardIter_tendstoUniformlyOn_solutionAt hpl t).continuousOn
    (Frequently.of_forall fun n =>
      (picardIter_time_contDiff f hf t₀ t n).continuous.continuousOn)).mono
        ball_subset_closedBall

theorem solutionAt_contDiffOn_nat
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {f : ℝ → X → X} {tmin tmax : ℝ} {t₀ : Icc tmin tmax}
    {x₀ : X} {a r L K : ℝ≥0}
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (n : ℕ) (htail : HasPicardTail f t₀ x₀ r n)
    (t : Icc tmin tmax) : ContDiffOn ℝ n (solutionAt hpl t) (ball x₀ r) := by
  cases n with
  | zero => exact solutionAt_contDiffOn_zero hf hpl t
  | succ n =>
      change ∃ aT LT KT : ℝ≥0,
        IsPicardLindelof (tangentField f) t₀
          (x₀, ContinuousLinearMap.id ℝ X) aT r LT KT ∧
        HasPicardTail (X := X × (X →L[ℝ] X)) (tangentField f) t₀
          (x₀, ContinuousLinearMap.id ℝ X) r n at htail
      obtain ⟨aT, LT, KT, hplT, tail⟩ := htail
      have htailReg := solutionAt_contDiffOn_nat
        (X := X × (X →L[ℝ] X)) (f := tangentField f)
        (tangentField_contDiff f hf) hplT n tail t
      have hemb : ContDiff ℝ ∞ fun x : X => (x, ContinuousLinearMap.id ℝ X) :=
        contDiff_id.prodMk contDiff_const
      have hembn : ContDiffOn ℝ n (fun x : X => (x, ContinuousLinearMap.id ℝ X))
          (ball x₀ r) :=
        (hemb.of_le (show (n : ℕ∞ω) ≤ ∞ from ENat.LEInfty.out)).contDiffOn
      have hmaps : MapsTo (fun x : X => (x, ContinuousLinearMap.id ℝ X))
          (ball x₀ r) (ball (x₀, ContinuousLinearMap.id ℝ X) r) := by
        intro x hx
        simpa [mem_ball, Prod.dist_eq] using hx
      have hcomposed : ContDiffOn ℝ n
          (fun x : X => solutionAt hplT t (x, ContinuousLinearMap.id ℝ X))
          (ball x₀ r) :=
        htailReg.comp hembn hmaps
      have hsolutionD : ContDiffOn ℝ n (solutionFDerivAt hplT t) (ball x₀ r) := by
        unfold solutionFDerivAt
        exact (ContinuousLinearMap.snd ℝ X (X →L[ℝ] X)).contDiff.comp_contDiffOn hcomposed
      have hdiff : DifferentiableOn ℝ (solutionAt hpl t) (ball x₀ r) :=
        (solutionAt_contDiffOn_one hf hpl hplT t).differentiableOn (by norm_num)
      have hderiv : ContDiffOn ℝ n
          (fderivWithin ℝ (solutionAt hpl t) (ball x₀ r)) (ball x₀ r) :=
        hsolutionD.congr fun x hx => by
          rw [fderivWithin_of_isOpen isOpen_ball hx]
          exact (solutionAt_hasFDerivAt hf hpl hplT t hx).fderiv
      have hsucc : ContDiffOn ℝ ((n : ℕ∞ω) + 1)
          (solutionAt hpl t) (ball x₀ r) := by
        rw [contDiffOn_succ_iff_fderivWithin isOpen_ball.uniqueDiffOn]
        exact ⟨hdiff, by simp, hderiv⟩
      simpa [Nat.cast_add, Nat.cast_one] using hsucc
termination_by n

theorem PicardStepData.map_contDiffOn
    {X : Type u} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [FiniteDimensional ℝ X]
    {f : ℝ → X → X} (hf : ContDiff ℝ ∞ (uncurry f))
    {tmin tmax : ℝ} {xcenter : X} {r : ℝ≥0} {n : ℕ}
    (d : PicardStepData f tmin tmax xcenter r n) :
    ContDiffOn ℝ n d.map (ball xcenter r) :=
  solutionAt_contDiffOn_nat hf d.hpl n d.tail d.endTime

theorem solutionAt_contDiffOn_infty
    (hf : ContDiff ℝ ∞ (uncurry f))
    (hpl : IsPicardLindelof f t₀ x₀ a r L K)
    (htails : ∀ n : ℕ, HasPicardTail f t₀ x₀ r n)
    (t : Icc tmin tmax) :
    ContDiffOn ℝ ∞ (solutionAt hpl t) (ball x₀ r) := by
  rw [contDiffOn_infty]
  intro n
  exact solutionAt_contDiffOn_nat hf hpl n (htails n) t

end PicardLimit

end

end Submission.MoserFlow
