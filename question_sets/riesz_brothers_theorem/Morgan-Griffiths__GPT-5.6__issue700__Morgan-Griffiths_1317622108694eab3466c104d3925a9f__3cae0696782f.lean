import Mathlib
namespace Submission

set_option maxHeartbeats 800000

open MeasureTheory

/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
open scoped ENNReal NNReal
noncomputable section

lemma signed_variation_finite {α : Type*} [MeasurableSpace α]
    (s : SignedMeasure α) : IsFiniteMeasure s.variation := by
  let p : Measure α := s.toJordanDecomposition.posPart
  let n : Measure α := s.toJordanDecomposition.negPart
  haveI hp : IsFiniteMeasure p := by dsimp [p]; infer_instance
  haveI hn : IsFiniteMeasure n := by dsimp [n]; infer_instance
  have hs : s = p.toSignedMeasure - n.toSignedMeasure := by
    simpa [p, n, JordanDecomposition.toSignedMeasure] using
      (s.toSignedMeasure_toJordanDecomposition.symm)
  have hle : s.variation ≤ p + n := by
    rw [hs]
    calc
      (p.toSignedMeasure - n.toSignedMeasure).variation ≤
          p.toSignedMeasure.variation + n.toSignedMeasure.variation :=
            VectorMeasure.variation_sub_le
      _ = p + n := by simp
  exact isFiniteMeasure_of_le (p+n) hle

lemma complex_variation_finite {α : Type*} [MeasurableSpace α]
    (c : ComplexMeasure α) : IsFiniteMeasure c.variation := by
  let r : SignedMeasure α := c.re
  let i : SignedMeasure α := c.im
  letI hr : IsFiniteMeasure r.variation := signed_variation_finite r
  letI hi : IsFiniteMeasure i.variation := signed_variation_finite i
  have hle : c.variation ≤ r.variation + i.variation := by
    apply VectorMeasure.variation_le_of_forall_enorm_le
    intro E hE
    calc
      ‖c E‖ₑ = ENNReal.ofReal ‖c E‖ := (ofReal_norm _).symm
      _ ≤ ENNReal.ofReal (|(c E).re| + |(c E).im|) :=
        ENNReal.ofReal_mono (Complex.norm_le_abs_re_add_abs_im (c E))
      _ = ENNReal.ofReal |(c E).re| + ENNReal.ofReal |(c E).im| := by
        rw [ENNReal.ofReal_add (abs_nonneg _) (abs_nonneg _)]
      _ = ‖r E‖ₑ + ‖i E‖ₑ := by
        simp [r, i, ← ofReal_norm, Real.norm_eq_abs]
      _ ≤ r.variation E + i.variation E := by
        gcongr <;> apply VectorMeasure.enorm_measure_le_variation
      _ = (r.variation + i.variation) E := by simp
  exact isFiniteMeasure_of_le (r.variation + i.variation) hle


/-- Polar-density starting point. Every complex measure is already absolutely
continuous with respect to its variation, so the (two-coordinate)
Radon--Nikodym derivative with respect to the variation represents it with no
singular summand. This is useful in the Hilbert-space proof: the ambient `L²`
space is `L²(c.variation)` rather than Haar. -/
lemma complex_withDensityv_variation {α : Type*} [MeasurableSpace α]
    (c : ComplexMeasure α) :
    c.variation.withDensityᵥ (c.rnDeriv c.variation) = c := by
  letI : IsFiniteMeasure c.variation := complex_variation_finite c
  have hr : c.re ≪ᵥ c.variation.toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable hs] at h0
    have hc : c s = 0 :=
      (VectorMeasure.variation_apply_eq_zero (μ:=c) hs).1 h0 s (by
        exact fun _ h => h) hs
    exact congrArg Complex.re hc
  have hi : c.im ≪ᵥ c.variation.toENNRealVectorMeasure := by
    refine VectorMeasure.AbsolutelyContinuous.mk fun s hs h0 => ?_
    rw [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable hs] at h0
    have hc : c s = 0 :=
      (VectorMeasure.variation_apply_eq_zero (μ:=c) hs).1 h0 s (by
        exact fun _ h => h) hs
    exact congrArg Complex.im hc
  -- The signed-measure Radon--Nikodym theorem is stated coordinatewise; this
  -- also supplies the sigma-finiteness required by that theorem.
  have hre := SignedMeasure.withDensityᵥ_rnDeriv_eq c.re c.variation hr
  have him := SignedMeasure.withDensityᵥ_rnDeriv_eq c.im c.variation hi
  ext s hs
  rw [withDensityᵥ_apply (c.integrable_rnDeriv c.variation) hs]
  apply Complex.ext
  · rw [← RCLike.re_eq_complex_re,
        ← integral_re (c.integrable_rnDeriv c.variation).integrableOn,
        RCLike.re_eq_complex_re]
    change (∫ (x : α) in s, c.re.rnDeriv c.variation x ∂c.variation) = (c s).re
    have h := congrArg (fun q : SignedMeasure α => q s) hre
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at h
    exact h
  · rw [← RCLike.im_eq_complex_im,
        ← integral_im (c.integrable_rnDeriv c.variation).integrableOn,
        RCLike.im_eq_complex_im]
    change (∫ (x : α) in s, c.im.rnDeriv c.variation x ∂c.variation) = (c s).im
    have h := congrArg (fun q : SignedMeasure α => q s) him
    rw [withDensityᵥ_apply (SignedMeasure.integrable_rnDeriv _ _) hs] at h
    exact h


/-- The density above cannot vanish on a set of positive variation.  This
  weaker (and often sufficient) part of the polar decomposition uses just the
  definition of variation: if every measurable subset of a set integrates to
  zero then its variation is zero.  In particular no positivity property of a
  complex measure is being smuggled in here. -/
lemma rnDeriv_variation_ae_ne_zero {α : Type*} [MeasurableSpace α]
    (c : ComplexMeasure α) :
    ∀ᵐ x ∂c.variation, c.rnDeriv c.variation x ≠ 0 := by
  letI : IsFiniteMeasure c.variation := complex_variation_finite c
  have hf : Measurable (c.rnDeriv c.variation) := by
    apply measurable_of_re_im
    · exact SignedMeasure.measurable_rnDeriv _ _
    · exact SignedMeasure.measurable_rnDeriv _ _
  let A : Set α := {x | c.rnDeriv c.variation x = 0}
  have hA : MeasurableSet A := hf (measurableSet_singleton (0 : ℂ))
  have heq := complex_withDensityv_variation c
  have hnull : c.variation A = 0 := by
    apply (VectorMeasure.variation_apply_eq_zero (μ:=c) hA).2
    intro t ht htm
    rw [← heq]
    rw [withDensityᵥ_apply (c.integrable_rnDeriv c.variation) htm]
    have hae : (c.rnDeriv c.variation) =ᵐ[c.variation.restrict t] 0 := by
      refine (ae_restrict_iff' htm).2 ?_
      filter_upwards [] with x hx
      exact ht hx
    calc
      (∫ (a : α) in t, c.rnDeriv c.variation a ∂c.variation) =
          ∫ (a : α), (0 : α → ℂ) a ∂(c.variation.restrict t) :=
            integral_congr_ae hae
      _ = _ := by simp
  rw [ae_iff]
  simpa [A] using hnull

lemma withDensityᵥ_complex_absolutelyContinuous {α : Type*} [MeasurableSpace α]
    (m : Measure α) (f : α → ℂ) :
    m.withDensityᵥ f ≪ᵥ m.toENNRealVectorMeasure := by
  by_cases hf : Integrable f m
  · refine VectorMeasure.AbsolutelyContinuous.mk fun i hi h0 => ?_
    rw [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable hi] at h0
    rw [withDensityᵥ_apply hf hi, Measure.restrict_zero_set h0, integral_zero_measure]
  · rw [Measure.withDensityᵥ, dif_neg hf]
    exact VectorMeasure.AbsolutelyContinuous.zero _

lemma ac_of_singularPart_zero {α : Type*} [MeasurableSpace α]
    (c : ComplexMeasure α) (m : Measure α)
    [c.HaveLebesgueDecomposition m]
    (hzero : c.singularPart m = 0) :
    c ≪ᵥ m.toENNRealVectorMeasure := by
  have h := ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq
    (c := c) (μ := m)
  rw [hzero, zero_add] at h
  rw [← h]
  exact withDensityᵥ_complex_absolutelyContinuous m _



/-- A small measure-theoretic endpoint useful in the Hilbert-space proof of F. and M. Riesz.
If the squared norm density is absolutely continuous, so is the vector density.  Notice that
one cannot replace this by a positivity assertion about a complex measure. -/
lemma withDensityv_ac_of_sq {α : Type*} [MeasurableSpace α]
    {ν m : Measure α} {f : α → ℂ} (hf : Integrable f ν)
    (hfm : Measurable fun x => (ENNReal.ofReal (‖f x‖ ^ 2)))
    (hAC : ν.withDensity (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) ≪ m) :
    ν.withDensityᵥ f ≪ᵥ m.toENNRealVectorMeasure := by
  refine VectorMeasure.AbsolutelyContinuous.mk fun s hs hms => ?_
  rw [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable hs] at hms
  have hz : (ν.withDensity (fun x => ENNReal.ofReal (‖f x‖ ^ 2))) s = 0 :=
    hAC hms
  rw [withDensity_apply _ hs] at hz
  -- Vanishing of the nonnegative integral means that the vector density itself
  -- vanishes a.e. on this set.  This is the convenient robust way to pass from
  -- an L2 spectral measure to the original complex measure.
  have hae' : (fun x => ENNReal.ofReal (‖f x‖ ^ 2)) =ᵐ[ν.restrict s] 0 :=
    (lintegral_eq_zero_iff' (hfm.aemeasurable.restrict)).1 hz
  have hae : f =ᵐ[ν.restrict s] 0 := by
    filter_upwards [hae'] with x hx
    change f x = 0
    have hx0 : (‖f x‖ : ℝ) ^ 2 ≤ 0 := (ENNReal.ofReal_eq_zero.mp hx)
    have hxnorm : ‖f x‖ = 0 := by
      have hn : 0 ≤ ‖f x‖ := norm_nonneg _
      nlinarith
    exact norm_eq_zero.mp hxnorm
  rw [withDensityᵥ_apply hf hs]
  have hzero : (∫ x : α in s, f x ∂ν) = (∫ _ : α, (0 : ℂ) ∂(ν.restrict s)) := by
    exact integral_congr_ae hae
  rw [hzero, integral_zero]


variable {α : Type*} [MeasurableSpace α]
def lpMulLeft (ν : Measure α) (g : Lp ℂ ∞ ν) :
    Lp ℂ 2 ν →L[ℂ] Lp ℂ 2 ν := by
  let A : Lp ℂ 2 ν →ₗ[ℂ] Lp ℂ 2 ν :=
    { toFun := fun u => (g • u : Lp ℂ 2 ν)
      map_add' := fun x y => by exact Lp.add_smul g x y
      map_smul' := by
        intro c x
        apply Lp.ext
        filter_upwards [Lp.coeFn_lpSMul (r:=2) g (c • x),
          Lp.coeFn_lpSMul (r:=2) g x,
          Lp.coeFn_smul c x,
          Lp.coeFn_smul c (g • x : Lp ℂ 2 ν)] with z h1 h2 h3 h4
        change _ = _
        -- scalars commute
        simp only [Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 ⊢
        change _ = ⇑(c • (g • x : Lp ℂ 2 ν)) z
        simp only [Pi.mul_apply] at h1 h2 ⊢
        rw [h1, h4, h3, h2]
        ring
    }
  exact LinearMap.mkContinuous A ‖g‖ (by
    intro x
    exact Lp.norm_smul_le g x)


def lpMulLeftOne (ν : Measure α) (g : Lp ℂ ∞ ν) :
    Lp ℂ 1 ν →L[ℂ] Lp ℂ 1 ν := by
  let A : Lp ℂ 1 ν →ₗ[ℂ] Lp ℂ 1 ν :=
    { toFun := fun u => (g • u : Lp ℂ 1 ν)
      map_add' := fun x y => by exact Lp.add_smul g x y
      map_smul' := by
        intro c x
        apply Lp.ext
        filter_upwards [Lp.coeFn_lpSMul (r:=1) g (c • x),
          Lp.coeFn_lpSMul (r:=1) g x,
          Lp.coeFn_smul c x,
          Lp.coeFn_smul c (g • x : Lp ℂ 1 ν)] with z h1 h2 h3 h4
        change _ = _
        simp only [Pi.smul_apply, smul_eq_mul] at h1 h2 h3 h4 ⊢
        change _ = ⇑(c • (g • x : Lp ℂ 1 ν)) z
        simp only [Pi.mul_apply] at h1 h2 ⊢
        rw [h1, h4, h3, h2]
        ring
    }
  exact LinearMap.mkContinuous A ‖g‖ (by
    intro x
    exact Lp.norm_smul_le g x)

def indicatorLpTop (ν : Measure α) (s : Set α) (hs : MeasurableSet s) : Lp ℂ ∞ ν := by
  have hm : AEStronglyMeasurable (s.indicator fun _ : α => (1:ℂ)) ν :=
    (aestronglyMeasurable_const.indicator hs)
  have hb : ∀ᵐ x ∂ν, ‖s.indicator (fun _ : α => (1:ℂ)) x‖ ≤ (1:ℝ) := by
    filter_upwards [] with x
    by_cases hx:x∈s <;> simp [Set.indicator, hx]
  let hf : MemLp (s.indicator fun _ : α => (1:ℂ)) ∞ ν := memLp_top_of_bound hm 1 hb
  exact hf.toLp (s.indicator fun _ : α => (1:ℂ))

lemma coe_indicatorLpTop (ν : Measure α) (s : Set α) (hs : MeasurableSet s) :
    (indicatorLpTop ν s hs : α → ℂ) =ᵐ[ν] s.indicator (fun _ : α => (1:ℂ)) := by
  simp [indicatorLpTop]
  exact MemLp.coeFn_toLp _

lemma lpMul_indicator_eq_zero_iff (ν : Measure α) (s : Set α) (hs : MeasurableSet s)
    (u : Lp ℂ 2 ν) :
    lpMulLeft ν (indicatorLpTop ν s hs) u = 0 ↔
      ∀ᵐ x ∂ν.restrict s, u x = 0 := by
  constructor
  · intro h
    have hae' : (lpMulLeft ν (indicatorLpTop ν s hs) u : α → ℂ) =ᵐ[ν]
        (0 : α → ℂ) := by
      have := congrArg (fun v : Lp ℂ 2 ν => (v : α →ₘ[ν] ℂ)) h
      -- easier Lp.coeFn_zero
      rw [h]
      exact Lp.coeFn_zero _ _ _
    have hh : ∀ᵐ x ∂ν, x ∈ s → (u x : ℂ) = 0 := by
      have hmul := Lp.coeFn_lpSMul (r:=2) (indicatorLpTop ν s hs) u
      have hcoe := coe_indicatorLpTop ν s hs
      filter_upwards [hae', hmul, hcoe] with x hzero hmulx hgx
      intro hx
      simp only [Pi.smul_apply, smul_eq_mul] at hmulx
      rw [Set.indicator_of_mem hx] at hgx
      have hmulx' : (indicatorLpTop ν s hs x) * u x = 0 := by
        rw [← Pi.mul_apply]
        rw [← hmulx]
        exact hzero
      have : (indicatorLpTop ν s hs x) * u x = 0 := hmulx' 
      simpa [hgx] using this
    exact (ae_restrict_iff' hs).2 hh
  · intro h
    apply Lp.ext
    change (lpMulLeft ν (indicatorLpTop ν s hs) u : α → ℂ) =ᵐ[ν] (0 : Lp ℂ 2 ν)
    have hh : ∀ᵐ x ∂ν, x ∈ s → (u x : ℂ) = 0 := (ae_restrict_iff' hs).1 h
    have hmul := Lp.coeFn_lpSMul (r:=2) (indicatorLpTop ν s hs) u
    have hcoe := coe_indicatorLpTop ν s hs
    have hzero := Lp.coeFn_zero ℂ 2 ν
    change ((indicatorLpTop ν s hs • u : Lp ℂ 2 ν) : α → ℂ) =ᵐ[ν] (0 : Lp ℂ 2 ν)
    filter_upwards [hh, hmul, hcoe, hzero] with x hx hmx hg hz
    rw [hmx]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [Pi.mul_apply]
    by_cases hxs : x ∈ s
    · rw [Set.indicator_of_mem hxs] at hg
      have hL : ((indicatorLpTop ν s hs : α → ℂ) x) * u x = 0 := by simp [hg, hx hxs]
      rw [hL]
      exact hz.symm
    · rw [Set.indicator_of_notMem hxs] at hg
      have hL : ((indicatorLpTop ν s hs : α → ℂ) x) * u x = 0 := by simp [hg]
      rw [hL]
      exact hz.symm

lemma ae_zero_restrict_of_tendsto {ν : Measure α} {s : Set α} (hs : MeasurableSet s)
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (u : ι → Lp ℂ 2 ν) (v : Lp ℂ 2 ν) (hu : Filter.Tendsto u l (nhds v))
    (hzero : ∀ᶠ i in l, ∀ᵐ x ∂ν.restrict s, (u i) x = 0) :
    ∀ᵐ x ∂ν.restrict s, v x = 0 := by
  have hi : ∀ᶠ i in l, u i ∈ LinearMap.ker (lpMulLeft ν (indicatorLpTop ν s hs)).toLinearMap := by
    filter_upwards [hzero] with i hi
    change lpMulLeft ν (indicatorLpTop ν s hs) (u i) = 0
    exact (lpMul_indicator_eq_zero_iff ν s hs (u i)).2 hi
  have hv : v ∈ LinearMap.ker (lpMulLeft ν (indicatorLpTop ν s hs)).toLinearMap :=
    (lpMulLeft ν (indicatorLpTop ν s hs)).isClosed_ker.mem_of_tendsto hu hi
  exact (lpMul_indicator_eq_zero_iff ν s hs v).1 hv


/-- The character `z ↦ z^k` has absolute value one, so it defines a bounded
  multiplier on any `L²(ν)`.  This uses an arbitrary measure, not Haar: in the
  operator proof the Hilbert space is built with the variation of the analytic
  measure. -/
def circleCharLpTop (ν : Measure UnitAddCircle) (k : ℤ) : Lp ℂ ∞ ν := by
  have hm : AEStronglyMeasurable (fun x : UnitAddCircle => fourier k x) ν :=
    (fourier k).continuous.aestronglyMeasurable
  have hb : ∀ᵐ x ∂ν, ‖fourier k x‖ ≤ (1:ℝ) := by
    filter_upwards [] with x
    change ‖(↑((k • x).toCircle) : ℂ)‖ ≤ (1:ℝ)
    simp
  let hf : MemLp (fun x : UnitAddCircle => fourier k x) ∞ ν :=
    memLp_top_of_bound hm 1 hb
  exact hf.toLp (fun x : UnitAddCircle => fourier k x)

lemma coe_circleCharLpTop (ν : Measure UnitAddCircle) (k : ℤ) :
    (circleCharLpTop ν k : UnitAddCircle → ℂ) =ᵐ[ν]
      (fun x : UnitAddCircle => fourier k x) := by
  simp [circleCharLpTop]
  exact MemLp.coeFn_toLp _

/-- Multiplication by a circle character is an isometry on `L²` for *any*
  measure on the circle.  Thus the shift in the Hilbert-space proof really is
  an isometry before any absolute-continuity conclusion has been made. -/
lemma lpMul_circleChar_norm (ν : Measure UnitAddCircle) (k : ℤ)
    (u : Lp ℂ 2 ν) :
    ‖lpMulLeft ν (circleCharLpTop ν k) u‖ = ‖u‖ := by
  rw [Lp.norm_def, Lp.norm_def]
  congr 1
  -- It is important to compare norms, not the functions themselves: the
  -- multiplier has modulus one, but of course is not the constant function.
  apply eLpNorm_congr_norm_ae
  have hmul := Lp.coeFn_lpSMul (r:=2) (circleCharLpTop ν k) u
  have hchar := coe_circleCharLpTop ν k
  filter_upwards [hmul, hchar] with x hx hχ
  -- `coeFn_lpSMul` is stated for pointwise products of the representatives.
  change ‖(lpMulLeft ν (circleCharLpTop ν k) u : UnitAddCircle → ℂ) x‖ =
    ‖(u : UnitAddCircle → ℂ) x‖
  change ‖(((circleCharLpTop ν k • u : Lp ℂ 2 ν) : UnitAddCircle → ℂ) x)‖ = _
  rw [hx]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [Pi.mul_apply]
  rw [hχ]
  change ‖(fourier k x : ℂ) * u x‖ = ‖u x‖
  rw [norm_mul]
  change ‖(↑((k • x).toCircle) : ℂ)‖ * ‖u x‖ = _
  simp

lemma lpMul_circleChar_add (ν : Measure UnitAddCircle) (m n : ℤ)
    (u : Lp ℂ 2 ν) :
    lpMulLeft ν (circleCharLpTop ν m)
        (lpMulLeft ν (circleCharLpTop ν n) u) =
      lpMulLeft ν (circleCharLpTop ν (m+n)) u := by
  apply Lp.ext
  have hm1 := Lp.coeFn_lpSMul (r:=2) (circleCharLpTop ν m)
        (lpMulLeft ν (circleCharLpTop ν n) u)
  have hn1 := Lp.coeFn_lpSMul (r:=2) (circleCharLpTop ν n) u
  have hmn := Lp.coeFn_lpSMul (r:=2) (circleCharLpTop ν (m+n)) u
  have hm := coe_circleCharLpTop ν m
  have hn := coe_circleCharLpTop ν n
  have hma := coe_circleCharLpTop ν (m+n)
  change (lpMulLeft ν (circleCharLpTop ν m)
        (lpMulLeft ν (circleCharLpTop ν n) u) : UnitAddCircle → ℂ) =ᵐ[ν]
      (lpMulLeft ν (circleCharLpTop ν (m+n)) u : UnitAddCircle → ℂ)
  filter_upwards [hm1, hn1, hmn, hm, hn, hma] with x hmx hnx hmnx hm' hn' ha'
  calc
    (lpMulLeft ν (circleCharLpTop ν m)
        (lpMulLeft ν (circleCharLpTop ν n) u) : UnitAddCircle → ℂ) x =
        (circleCharLpTop ν m : UnitAddCircle → ℂ) x *
          ((lpMulLeft ν (circleCharLpTop ν n) u : UnitAddCircle → ℂ) x) := by
            change (((circleCharLpTop ν m •
              (lpMulLeft ν (circleCharLpTop ν n) u) : Lp ℂ 2 ν) : UnitAddCircle → ℂ) x) = _
            simpa [Pi.smul_apply, smul_eq_mul] using hmx
    _ = (circleCharLpTop ν m : UnitAddCircle → ℂ) x *
          ((circleCharLpTop ν n : UnitAddCircle → ℂ) x * u x) := by
            change _ *
              (((circleCharLpTop ν n • u : Lp ℂ 2 ν) : UnitAddCircle → ℂ) x) = _
            rw [hnx]
            rfl
    _ = (circleCharLpTop ν (m+n) : UnitAddCircle → ℂ) x * u x := by
            rw [hm', hn', ha', fourier_add]
            ring
    _ = (lpMulLeft ν (circleCharLpTop ν (m+n)) u : UnitAddCircle → ℂ) x := by
            change _ = (((circleCharLpTop ν (m+n) • u : Lp ℂ 2 ν) : UnitAddCircle → ℂ) x)
            simpa [Pi.smul_apply, smul_eq_mul] using hmnx.symm


@[simp] lemma lpMul_circleChar_zero (ν : Measure UnitAddCircle)
    (u : Lp ℂ 2 ν) : lpMulLeft ν (circleCharLpTop ν 0) u = u := by
  apply Lp.ext
  have hz := Lp.coeFn_lpSMul (r:=2) (circleCharLpTop ν 0) u
  have hχ := coe_circleCharLpTop ν 0
  change (lpMulLeft ν (circleCharLpTop ν 0) u : UnitAddCircle → ℂ) =ᵐ[ν]
      (u : UnitAddCircle → ℂ)
  filter_upwards [hz, hχ] with x hx hcx
  change (((circleCharLpTop ν 0 • u : Lp ℂ 2 ν) : UnitAddCircle → ℂ) x) = _
  rw [hx]
  change (circleCharLpTop ν 0 : UnitAddCircle → ℂ) x * u x = _
  rw [hcx]
  have hzero : (fourier (0:ℤ) x : ℂ) = 1 := fourier_zero
  rw [hzero]
  simp

lemma lpMul_circleChar_neg_left (ν : Measure UnitAddCircle) (k : ℤ)
    (u : Lp ℂ 2 ν) :
    lpMulLeft ν (circleCharLpTop ν (-k))
       (lpMulLeft ν (circleCharLpTop ν k) u) = u := by
  rw [lpMul_circleChar_add, neg_add_cancel]
  exact lpMul_circleChar_zero _ _

lemma lpMul_circleChar_neg_right (ν : Measure UnitAddCircle) (k : ℤ)
    (u : Lp ℂ 2 ν) :
    lpMulLeft ν (circleCharLpTop ν k)
       (lpMulLeft ν (circleCharLpTop ν (-k)) u) = u := by
  rw [lpMul_circleChar_add, add_neg_cancel]
  exact lpMul_circleChar_zero _ _



lemma complex_singularPart_mutuallySingular
 (c : ComplexMeasure α) (m : Measure α) :
 c.singularPart m ⟂ᵥ m.toENNRealVectorMeasure := by
  obtain ⟨s, hs, hs1, hs2⟩ := SignedMeasure.mutuallySingular_singularPart c.re m
  obtain ⟨t, ht, ht1, ht2⟩ := SignedMeasure.mutuallySingular_singularPart c.im m
  refine VectorMeasure.MutuallySingular.mk (s ∩ t) (hs.inter ht) ?_ ?_
  · intro u hu humeas
    change (c.re.singularPart m).toComplexMeasure (c.im.singularPart m) u = 0
    have h1 : c.re.singularPart m u = 0 := hs1 u (Set.Subset.trans hu Set.inter_subset_left)
    have h2 : c.im.singularPart m u = 0 := ht1 u (Set.Subset.trans hu Set.inter_subset_right)
    rw [SignedMeasure.toComplexMeasure_apply, h1, h2]
    exact Complex.ext (by simp) (by simp)
  · intro u hu humeas
    rw [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable humeas]
    have hz₁ : m (sᶜ) = 0 := by
      have := hs2 (sᶜ) (by rfl)
      simpa [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable hs.compl] using this
    have hz₂ : m (tᶜ) = 0 := by
      have := ht2 (tᶜ) (by rfl)
      simpa [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable ht.compl] using this
    have hsub : u ⊆ sᶜ ∪ tᶜ := by simpa [Set.compl_inter] using hu
    apply le_zero_iff.mp
    calc m u ≤ m (sᶜ ∪ tᶜ) := MeasureTheory.measure_mono hsub
         _ ≤ m (sᶜ) + m (tᶜ) := measure_union_le _ _
         _ = 0 := by rw [hz₁, hz₂]; simp


-- On the circle every character is continuous and bounded.  Vector-measure
-- integrability means ordinary Bochner integrability for the variation
-- measure; spelling this out is convenient because there is no global
-- `IsFiniteMeasure c.variation` instance for complex measures.
lemma complex_integrable_fourier (c : ComplexMeasure UnitAddCircle)
    [IsFiniteMeasure c.variation] (k : ℤ) :
    c.Integrable (fun z : UnitAddCircle => fourier k z) := by
  change Integrable (fun z : UnitAddCircle => fourier k z) c.variation
  exact
    (fourier k).continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)



lemma integral_complex_smul (c : ComplexMeasure UnitAddCircle)
    (a : ℂ) (f : UnitAddCircle → ℂ) :
    (∫ᵛ z, a • f z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) =
      a • (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) := by
  change MeasureTheory.setToFun c.variation (c.transpose (ContinuousLinearMap.mul ℝ ℂ))
      (MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure c
        (ContinuousLinearMap.mul ℝ ℂ)) (a • f) = _
  apply MeasureTheory.setToFun_smul
  intro b t x
  change (ContinuousLinearMap.mul ℝ ℂ) (b • x) (c t) =
    b • (ContinuousLinearMap.mul ℝ ℂ) x (c t)
  -- Multiplication of complex scalars is on the left; commuting the other
  -- factor is not needed here.
  change (b * x) * c t = b * (x * c t)
  exact mul_assoc _ _ _

-- Continuity of the functional on continuous test functions (with an
-- explicit variation bound). This is the uniform-limit step; it avoids
-- assuming any positivity of the complex measure.
lemma norm_integral_sub_le (c : ComplexMeasure UnitAddCircle)
    [IsFiniteMeasure c.variation]
    (f g : C(UnitAddCircle, ℂ)) :
    ‖(∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) -
      (∫ᵛ z, g z ∂[ContinuousLinearMap.mul ℝ ℂ; c])‖ ≤
      ‖f - g‖ * ‖(ContinuousLinearMap.mul ℝ ℂ)‖ * c.variation.real Set.univ := by
  have hf : c.Integrable (fun z : UnitAddCircle => f z) := by
    change Integrable (fun z : UnitAddCircle => f z) c.variation
    exact f.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hg : c.Integrable (fun z : UnitAddCircle => g z) := by
    change Integrable (fun z : UnitAddCircle => g z) c.variation
    exact g.continuous.integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  calc
    _ = ‖(∫ᵛ z : UnitAddCircle, f z - g z
        ∂[ContinuousLinearMap.mul ℝ ℂ; c])‖ := by
      rw [MeasureTheory.VectorMeasure.integral_fun_sub hf hg]
    _ ≤ ‖f - g‖ * ‖(ContinuousLinearMap.mul ℝ ℂ)‖ * c.variation.real Set.univ := by
      apply MeasureTheory.VectorMeasure.norm_integral_le_of_norm_le_const
      filter_upwards [] with x
      exact ContinuousMap.norm_coe_le_norm (f - g) x

lemma continuous_integral_on_C (c : ComplexMeasure UnitAddCircle)
    [IsFiniteMeasure c.variation] :
    Continuous (fun f : C(UnitAddCircle, ℂ) =>
      (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c])) := by
  apply Metric.continuous_iff.2
  intro b ε hε
  let D : ℝ := ‖(ContinuousLinearMap.mul ℝ ℂ)‖ * c.variation.real Set.univ
  have hD : 0 ≤ D := mul_nonneg (norm_nonneg (ContinuousLinearMap.mul ℝ ℂ)) (by positivity)
  refine ⟨ε / (D + 1), by positivity, ?_⟩
  intro a ha
  have hb := norm_integral_sub_le c a b
  have hdist : dist a b = ‖a - b‖ := dist_eq_norm a b
  have hdist' : dist
       (∫ᵛ z, a z ∂[ContinuousLinearMap.mul ℝ ℂ; c])
       (∫ᵛ z, b z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) =
       ‖(∫ᵛ z, a z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) -
         (∫ᵛ z, b z ∂[ContinuousLinearMap.mul ℝ ℂ; c])‖ := dist_eq_norm _ _
  rw [hdist']
  have hle :
      ‖(∫ᵛ z, a z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) -
         (∫ᵛ z, b z ∂[ContinuousLinearMap.mul ℝ ℂ; c])‖ ≤ ‖a - b‖ * D := by
    simpa [D, mul_assoc] using hb
  have hab : ‖a - b‖ < ε / (D + 1) := by simpa [hdist] using ha
  calc
    _ ≤ ‖a - b‖ * D := hle
    _ ≤ ‖a - b‖ * (D + 1) := by
      gcongr
      linarith
    _ < (ε / (D + 1)) * (D + 1) := by
      exact mul_lt_mul_of_pos_right hab (by linarith)
    _ = ε := by
      field_simp

lemma integral_zero_of_uniform_limit (c : ComplexMeasure UnitAddCircle)
    [IsFiniteMeasure c.variation]
    (F : ℕ → C(UnitAddCircle, ℂ)) (g : C(UnitAddCircle, ℂ))
    (hF : Filter.Tendsto F Filter.atTop (nhds g))
    (h0 : ∀ n, (∫ᵛ z, F n z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) = 0) :
    (∫ᵛ z, g z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) = 0 := by
  have ht : Filter.Tendsto
      (fun f : C(UnitAddCircle, ℂ) =>
        (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c]))
      (nhds g)
      (nhds (∫ᵛ z, g z ∂[ContinuousLinearMap.mul ℝ ℂ; c])) :=
    (continuous_integral_on_C c).tendsto g
  have hlim : Filter.Tendsto
      (fun n => (∫ᵛ z, F n z ∂[ContinuousLinearMap.mul ℝ ℂ; c]))
      Filter.atTop
      (nhds (∫ᵛ z, g z ∂[ContinuousLinearMap.mul ℝ ℂ; c])) := ht.comp hF
  have hzero : Filter.Tendsto
      (fun n => (∫ᵛ z, F n z ∂[ContinuousLinearMap.mul ℝ ℂ; c]))
      Filter.atTop (nhds (0 : ℂ)) := by
    simpa [h0]  -- the sequence is identically zero
  exact tendsto_nhds_unique hzero hlim |>.symm

lemma integral_sum_fourier_pos (c : ComplexMeasure UnitAddCircle)
    [IsFiniteMeasure c.variation]
    (h : ∀ n : ℕ, 1 ≤ n →
      ∫ᵛ z, fourier n z ∂[ContinuousLinearMap.mul ℝ ℂ; c] = 0)
    (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (a : ℕ → ℂ) :
    (∫ᵛ z : UnitAddCircle, (∑ n ∈ s, a n • fourier (n : ℤ) z)
      ∂[ContinuousLinearMap.mul ℝ ℂ; c]) = 0 := by
  classical
  have hfi : ∀ n ∈ s,
      c.Integrable (fun z : UnitAddCircle => a n • fourier (n : ℤ) z) := by
    intro n hn
    exact (complex_integrable_fourier c (n : ℤ)).smul (a n)
  rw [MeasureTheory.VectorMeasure.integral_finsetSum s hfi]
  apply Finset.sum_eq_zero
  intro n hn
  rw [integral_complex_smul]
  rw [h n (hs n hn)]
  simp






/-- A continuous-test uniqueness fact for complex measures on the compact circle.
It is the simple Fourier-uniqueness endpoint of the analytic measure argument: the
hard part of F. and M. Riesz can focus on obtaining the missing moments. -/
lemma complexMeasure_eq_zero_of_integral_continuous
    (c : ComplexMeasure UnitAddCircle) [IsFiniteMeasure c.variation]
    (hz : ∀ f : C(UnitAddCircle, ℂ),
      (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) = 0) : c = 0 := by
  classical
  -- The vector integral is the continuous extension of its map on `L¹(|c|)`.
  let hT := MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure
      c (ContinuousLinearMap.mul ℝ ℂ)
  let S : (Lp ℂ 1 c.variation) →L[ℝ] ℂ := MeasureTheory.L1.setToL1 hT
  have hs (f : C(UnitAddCircle, ℂ)) :
      S ((ContinuousMap.toLp 1 c.variation ℝ) f) = 0 := by
    have hf : Integrable (fun x : UnitAddCircle => f x) c.variation :=
      f.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have heq : hf.toL1 (fun x : UnitAddCircle => f x) =
        (ContinuousMap.toLp 1 c.variation ℝ) f := by
      apply Lp.ext
      exact hf.coeFn_toL1.trans (ContinuousMap.coeFn_toLp c.variation f).symm
    have hset :
        MeasureTheory.setToFun c.variation
          (c.transpose (ContinuousLinearMap.mul ℝ ℂ)) hT
            (fun x : UnitAddCircle => f x)
          = S (hf.toL1 (fun x : UnitAddCircle => f x)) :=
      MeasureTheory.setToFun_eq hT hf
    have hi :
        (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) =
          MeasureTheory.setToFun c.variation
            (c.transpose (ContinuousLinearMap.mul ℝ ℂ)) hT
              (fun x : UnitAddCircle => f x) :=
      MeasureTheory.VectorMeasure.integral_eq_setToFun
    rw [← heq]
    exact hset ▸ hz f
  have hSdense : DenseRange
      (ContinuousMap.toLp 1 c.variation ℝ : C(UnitAddCircle, ℂ) → Lp ℂ 1 c.variation) :=
    ContinuousMap.toLp_denseRange ℂ c.variation ℝ (by simp)
  have hzero_fun : (S : (Lp ℂ 1 c.variation) → ℂ) = (fun _ => 0) := by
    apply hSdense.equalizer S.continuous continuous_const
    funext f
    exact hs f
  have hSz (u : Lp ℂ 1 c.variation) : S u = 0 :=
    congrFun hzero_fun u
  -- Apply the extension to characteristic functions.  This recovers the
  -- values of the vector measure itself.
  apply MeasureTheory.VectorMeasure.ext
  intro t ht
  have ht_top : c.variation t ≠ ∞ := measure_ne_top _ _
  have hsetzero :
      MeasureTheory.setToFun c.variation
        (c.transpose (ContinuousLinearMap.mul ℝ ℂ)) hT
          (t.indicator (fun _ : UnitAddCircle => (1 : ℂ))) = 0 := by
    have hf : Integrable (t.indicator (fun _ : UnitAddCircle => (1 : ℂ))) c.variation := by
      exact (integrable_indicator_iff ht).2
        (integrableOn_const (C := (1 : ℂ)) ht_top (by finiteness))
    rw [MeasureTheory.setToFun_eq hT hf]
    exact hSz _
  have hind :=
    MeasureTheory.setToFun_indicator_const (E := ℂ) (F := ℂ)
      hT ht ht_top (1 : ℂ)
  change c t = (0 : ComplexMeasure UnitAddCircle) t
  have hc : (c.transpose (ContinuousLinearMap.mul ℝ ℂ) t) (1 : ℂ) = c t := by
    change (1 : ℂ) * c t = c t
    simp
  rw [← hc]
  -- `hind` computes the same characteristic function via simple functions.
  have : (c.transpose (ContinuousLinearMap.mul ℝ ℂ) t) (1 : ℂ) = 0 := by
    rw [← hind]
    exact hsetzero
  simpa using this


-- Fourier uniqueness for finite complex measures once *all* the moments (not
-- just the analytic half) have vanished. The density invoked here is the
-- Stone--Weierstrass theorem already available for `AddCircle`.
lemma complexMeasure_eq_zero_of_all_fourier
    (c : ComplexMeasure UnitAddCircle) [IsFiniteMeasure c.variation]
    (hall : ∀ k : ℤ,
      (∫ᵛ z, fourier k z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) = 0) :
    c = 0 := by
  classical
  let I : C(UnitAddCircle, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c])
      map_add' := by
        intro f g
        have hf : c.Integrable (fun z : UnitAddCircle => f z) := by
          change Integrable (fun z : UnitAddCircle => f z) c.variation
          exact f.continuous.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        have hg : c.Integrable (fun z : UnitAddCircle => g z) := by
          change Integrable (fun z : UnitAddCircle => g z) c.variation
          exact g.continuous.integrable_of_hasCompactSupport
            (HasCompactSupport.of_compactSpace _)
        exact MeasureTheory.VectorMeasure.integral_fun_add hf hg
      map_smul' := by
        intro a f
        exact integral_complex_smul c a f }
  have hspan : Submodule.span ℂ (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ))) ≤
        LinearMap.ker I := by
    refine (Submodule.span_le).2 ?_
    rintro f ⟨k, rfl⟩
    change (∫ᵛ z : UnitAddCircle, fourier k z
      ∂[ContinuousLinearMap.mul ℝ ℂ; c]) = 0
    exact hall k
  have hclosed : IsClosed (LinearMap.ker I : Set C(UnitAddCircle, ℂ)) := by
    change IsClosed {f : C(UnitAddCircle, ℂ) |
      (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) = 0}
    exact isClosed_eq (continuous_integral_on_C c) continuous_const
  have hle := Submodule.topologicalClosure_minimal
    (Submodule.span ℂ (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ))))
    hspan hclosed
  rw [span_fourier_closure_eq_top] at hle
  have hz : ∀ f : C(UnitAddCircle, ℂ),
      (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; c]) = 0 := by
    intro f
    have hfker : f ∈ LinearMap.ker I := hle (by simp)
    exact hfker
  exact complexMeasure_eq_zero_of_integral_continuous c hz


-- Ordinary finite Borel measures on the circle are determined by their
-- (complex) trigonometric moments.
lemma measure_eq_of_all_fourier_integral {q q' : Measure UnitAddCircle}
    [IsFiniteMeasure q] [IsFiniteMeasure q']
    (h : ∀ k : ℤ, (∫ x : UnitAddCircle, fourier k x ∂q) =
                      ∫ x : UnitAddCircle, fourier k x ∂q') : q = q' := by
  classical
  let Jq : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
    (MeasureTheory.L1.integralCLM' (α:=UnitAddCircle) (E:=ℂ) ℂ (μ:=q)).comp
      (ContinuousMap.toLp 1 q ℂ)
  let Jr : C(UnitAddCircle, ℂ) →L[ℂ] ℂ :=
    (MeasureTheory.L1.integralCLM' (α:=UnitAddCircle) (E:=ℂ) ℂ (μ:=q')).comp
      (ContinuousMap.toLp 1 q' ℂ)
  have hJq (f : C(UnitAddCircle, ℂ)) : Jq f = ∫ x, f x ∂q := by
    dsimp [Jq]
    rw [← MeasureTheory.L1.integral_eq' ℂ]
    have hf : Integrable (fun x : UnitAddCircle => f x) q :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [MeasureTheory.integral_eq _ hf]
    apply congrArg MeasureTheory.L1.integral
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (p:=(1:ENNReal)) (𝕜:=ℂ) q f).trans hf.coeFn_toL1.symm
  have hJr (f : C(UnitAddCircle, ℂ)) : Jr f = ∫ x, f x ∂q' := by
    dsimp [Jr]
    rw [← MeasureTheory.L1.integral_eq' ℂ]
    have hf : Integrable (fun x : UnitAddCircle => f x) q' :=
      f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    rw [MeasureTheory.integral_eq _ hf]
    apply congrArg MeasureTheory.L1.integral
    apply Lp.ext
    exact (ContinuousMap.coeFn_toLp (p:=(1:ENNReal)) (𝕜:=ℂ) q' f).trans hf.coeFn_toL1.symm
  let D : C(UnitAddCircle, ℂ) →L[ℂ] ℂ := Jq - Jr
  have hspan : Submodule.span ℂ (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ))) ≤
        LinearMap.ker D.toLinearMap := by
    refine (Submodule.span_le).2 ?_
    rintro f ⟨k, rfl⟩
    change D (fourier k) = 0
    dsimp [D]
    rw [ContinuousLinearMap.sub_apply, hJq, hJr, sub_eq_zero]
    exact h k
  have hzero : ∀ f : C(UnitAddCircle, ℂ), D f = 0 := by
    have hclosed : IsClosed (LinearMap.ker D.toLinearMap : Set C(UnitAddCircle, ℂ)) :=
      D.isClosed_ker
    have hle := Submodule.topologicalClosure_minimal
      (Submodule.span ℂ (Set.range (fourier : ℤ → C(UnitAddCircle, ℂ)))) hspan hclosed
    rw [span_fourier_closure_eq_top] at hle
    intro f
    exact hle (by simp)
  -- equality of the real continuous integrals determines a finite Borel measure
  apply MeasureTheory.ext_of_forall_integral_eq_of_IsFiniteMeasure
      (μ:=q) (ν:=q')
  intro f
  -- coerce a real bounded continuous function to a complex continuous function
  let fc : C(UnitAddCircle, ℂ) :=
    { toFun := fun x => (f x : ℂ)
      continuous_toFun := Complex.continuous_ofReal.comp f.continuous }
  have hz : (∫ x : UnitAddCircle, (f x : ℂ) ∂q) =
        ∫ x : UnitAddCircle, (f x : ℂ) ∂q' := by
    have hd : D fc = 0 := hzero fc
    dsimp [D] at hd
    rw [ContinuousLinearMap.sub_apply, hJq, hJr, sub_eq_zero] at hd
    exact hd
  -- take real parts
  have hz' := congrArg Complex.re hz
  have hzq : (∫ x : UnitAddCircle, (f x : ℂ) ∂q) =
        (↑(∫ x : UnitAddCircle, f x ∂q) : ℂ) := integral_ofReal
  have hzr : (∫ x : UnitAddCircle, (f x : ℂ) ∂q') =
        (↑(∫ x : UnitAddCircle, f x ∂q') : ℂ) := integral_ofReal
  rw [hzq, hzr] at hz
  exact_mod_cast hz


open scoped ComplexConjugate
lemma inner_lpMul_fourier (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (w : Lp ℂ 2 q) (k : ℤ) :
    @inner ℂ _ _ w (lpMulLeft q (circleCharLpTop q k) w) =
       ∫ x : UnitAddCircle, fourier k x * ( (‖w x‖ : ℝ)^2 : ℂ) ∂q := by
  rw [MeasureTheory.L2.inner_def]
  apply integral_congr_ae
  have hm := Lp.coeFn_lpSMul (r:=2) (circleCharLpTop q k) w
  have hc := coe_circleCharLpTop q k
  filter_upwards [hm, hc] with x hx hcx
  change @inner ℂ _ _ (w x) ((lpMulLeft q (circleCharLpTop q k) w : UnitAddCircle → ℂ) x) = _
  change @inner ℂ _ _ (w x)
    (((circleCharLpTop q k • w : Lp ℂ 2 q) : UnitAddCircle → ℂ) x) = _
  rw [hx]
  change @inner ℂ _ _ (w x) (((circleCharLpTop q k : UnitAddCircle → ℂ) x) * w x) = _
  rw [hcx]
  rw [RCLike.inner_apply]
  -- collect the `x * conj x` pair
  rw [mul_assoc, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  simp


def spectralMeasure (q : Measure UnitAddCircle) (w : Lp ℂ 2 q) : Measure UnitAddCircle :=
  q.withDensity (fun x => ENNReal.ofReal ((‖w x‖ : ℝ)^2))

lemma spectralMeasure_finite (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (w : Lp ℂ 2 q) : IsFiniteMeasure (spectralMeasure q w) := by
  dsimp [spectralMeasure]
  apply MeasureTheory.isFiniteMeasure_withDensity_ofReal
  exact (MeasureTheory.memLp_two_iff_integrable_sq_norm (Lp.aestronglyMeasurable w)).1
    (Lp.memLp w) |>.2

lemma spectralMeasure_fourier (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (w : Lp ℂ 2 q) (k : ℤ) :
    (∫ x : UnitAddCircle, fourier k x ∂(spectralMeasure q w)) =
      @inner ℂ _ _ w (lpMulLeft q (circleCharLpTop q k) w) := by
  have hm0 : AEMeasurable (fun x : UnitAddCircle => ENNReal.ofReal ((‖w x‖:ℝ)^2)) q :=
    ((Lp.aestronglyMeasurable w).norm.aemeasurable.pow_const _).ennreal_ofReal
  have ht : ∀ᵐ x : UnitAddCircle ∂q,
      ENNReal.ofReal ((‖w x‖:ℝ)^2) < ∞ := by
    filter_upwards [] with x
    exact ENNReal.ofReal_lt_top
  rw [spectralMeasure, integral_withDensity_eq_integral_toReal_smul₀ hm0 ht]
  rw [inner_lpMul_fourier]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [ENNReal.toReal_ofReal (sq_nonneg _), Complex.real_smul]
  push_cast
  ring

lemma haar_integral_fourier (k:ℤ) :
   (∫ x : UnitAddCircle, fourier k x ∂AddCircle.haarAddCircle) =
      if (0:ℤ) = k then 1 else 0 := by
  have hh := (orthonormal_iff_ite.1
    (orthonormal_fourier (T:= (1:ℝ)))) (0:ℤ) k
  rw [ContinuousMap.inner_toLp] at hh
  simpa [fourier_zero] using hh

lemma spectralMeasure_eq_haar_of_wandering (q : Measure UnitAddCircle)
    [IsFiniteMeasure q] (w : Lp ℂ 2 q)
    (hw : ∀ k : ℤ, k ≠ 0 →
       @inner ℂ _ _ w (lpMulLeft q (circleCharLpTop q k) w) = 0) :
    spectralMeasure q w = (ENNReal.ofReal (‖w‖^2)) • AddCircle.haarAddCircle := by
  letI : IsFiniteMeasure (spectralMeasure q w) := spectralMeasure_finite q w
  letI : IsFiniteMeasure ((ENNReal.ofReal (‖w‖^2)) • AddCircle.haarAddCircle) := by
    exact Measure.smul_finite (AddCircle.haarAddCircle : Measure UnitAddCircle) ENNReal.ofReal_ne_top
  apply measure_eq_of_all_fourier_integral
  intro k
  rw [spectralMeasure_fourier]
  rw [integral_smul_measure]
  rw [haar_integral_fourier]
  by_cases hk : k = 0
  · subst k
    rw [if_pos rfl, lpMul_circleChar_zero,
      inner_self_eq_norm_sq_to_K]
    simp [Lp.norm_def]
  · rw [if_neg]
    · simp [hw k hk]
    · intro h0
      exact hk h0.symm


abbrev fourierLpAny (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (k : ℤ) : Lp ℂ 2 q := (ContinuousMap.toLp 2 q ℂ) (fourier k)
lemma coe_fourierLpAny (q : Measure UnitAddCircle) [IsFiniteMeasure q] (k:ℤ) :
   (fourierLpAny q k : UnitAddCircle → ℂ) =ᵐ[q] fourier k :=
  ContinuousMap.coeFn_toLp (p:=2) (𝕜:=ℂ) q _
lemma fourierLpAny_mul (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (a b : ℤ) :
    lpMulLeft q (circleCharLpTop q a) (fourierLpAny q b) = fourierLpAny q (a+b) := by
  apply Lp.ext
  have hm := Lp.coeFn_lpSMul (r:=2) (circleCharLpTop q a) (fourierLpAny q b)
  have ha := coe_circleCharLpTop q a
  have hb := coe_fourierLpAny q b
  have hc := coe_fourierLpAny q (a+b)
  change (lpMulLeft q (circleCharLpTop q a) (fourierLpAny q b) : UnitAddCircle → ℂ) =ᵐ[q]
    (fourierLpAny q (a+b) : UnitAddCircle → ℂ)
  filter_upwards [hm,ha,hb,hc] with x hx ha hb hc
  change (((circleCharLpTop q a • fourierLpAny q b : Lp ℂ 2 q) : UnitAddCircle → ℂ) x) = _
  rw [hx]
  change (circleCharLpTop q a : UnitAddCircle → ℂ) x * (fourierLpAny q b : UnitAddCircle → ℂ) x = _
  rw [ha, hb, hc, fourier_add]

lemma span_fourierLpAny_closure_eq_top (q : Measure UnitAddCircle) [IsFiniteMeasure q] :
   (Submodule.span ℂ (Set.range (fourierLpAny q))).topologicalClosure = ⊤ := by
  convert!
    (ContinuousMap.toLp_denseRange ℂ q ℂ (by simp : (2:ENNReal) ≠ ∞)).topologicalClosure_map_submodule
      (span_fourier_closure_eq_top (T:=(1:ℝ)))
  rw [Submodule.map_span]
  rw [Set.range_comp']
  apply congrArg (Submodule.span ℂ)
  ext x
  constructor
  · rintro ⟨k, hk0, hk⟩
    refine ⟨fourier k, ⟨k, rfl⟩, ?_⟩
    exact hk
  · rintro ⟨f, ⟨k, rfl⟩, hk⟩
    exact ⟨k, ⟨k, rfl⟩, hk⟩


lemma spectralMeasure_ac_of_wandering (q : Measure UnitAddCircle)
    [IsFiniteMeasure q] (w : Lp ℂ 2 q)
    (hw : ∀ k : ℤ, k ≠ 0 →
       @inner ℂ _ _ w (lpMulLeft q (circleCharLpTop q k) w) = 0) :
    spectralMeasure q w ≪ AddCircle.haarAddCircle := by
  rw [spectralMeasure_eq_haar_of_wandering q w hw]
  intro t ht
  rw [Measure.smul_apply, smul_eq_mul, ht, mul_zero]


lemma spectralMeasure_fourier_neg (q : Measure UnitAddCircle)
    [IsFiniteMeasure q] (w : Lp ℂ 2 q) (k : ℤ) :
    @inner ℂ _ _ w (lpMulLeft q (circleCharLpTop q (-k)) w) =
      starRingEnd ℂ (@inner ℂ _ _ w (lpMulLeft q (circleCharLpTop q k) w)) := by
  rw [← spectralMeasure_fourier, ← spectralMeasure_fourier]
  rw [← integral_conj]
  apply integral_congr_ae
  filter_upwards [] with x
  exact fourier_neg

lemma spectralMeasure_ac_of_wandering_nat (q : Measure UnitAddCircle)
    [IsFiniteMeasure q] (w : Lp ℂ 2 q)
    (hw : ∀ n : ℕ, 1 ≤ n →
       @inner ℂ _ _ w (lpMulLeft q (circleCharLpTop q (n:ℤ)) w) = 0) :
    spectralMeasure q w ≪ AddCircle.haarAddCircle := by
  apply spectralMeasure_ac_of_wandering q w
  intro k hk
  rcases lt_or_gt_of_ne hk with hneg | hpos
  · obtain ⟨n, hkcast, hn⟩ : ∃ n : ℕ, (-(k)) = n ∧ 1 ≤ n := by
      refine ⟨Int.toNat (-k), ?_, ?_⟩
      · exact (Int.toNat_of_nonneg (by omega : 0 ≤ -k)).symm
      · omega
    have hkk : - (n:ℤ) = k := by omega
    rw [← hkk, spectralMeasure_fourier_neg]
    rw [hw n hn]
    simp
  · have hk' : 1 ≤ k := by omega
    have hkn : (Int.toNat k : ℤ) = k := Int.toNat_of_nonneg (by omega)
    rw [← hkn]
    exact hw (Int.toNat k) (by omega)



-- `rnDeriv c |c|` is in fact the polar direction of `c`.  For the
-- construction of the vector in `L² (|c|)` one only needs that it is
-- bounded.  The following coordinate estimate is a useful elementary
-- substitute for the full polar-decomposition lemma.  It uses only the
-- defining extremal inequality for variation.
lemma rnDeriv_variation_ae_abs_re_im_le_one {β : Type*} [MeasurableSpace β]
    (c : ComplexMeasure β) :
    ∀ᵐ x ∂c.variation,
      |(c.rnDeriv c.variation x).re| ≤ (1 : ℝ) ∧
      |(c.rnDeriv c.variation x).im| ≤ (1 : ℝ) := by
  letI : IsFiniteMeasure c.variation := complex_variation_finite c
  have hrepr := complex_withDensityv_variation c
  have hf : Integrable (c.rnDeriv c.variation) c.variation :=
    ComplexMeasure.integrable_rnDeriv _ _
  have hfre : Integrable (fun x => (c.rnDeriv c.variation x).re) c.variation :=
    hf.re
  have hfim : Integrable (fun x => (c.rnDeriv c.variation x).im) c.variation :=
    hf.im
  -- The two real coordinates of the density integrate to the coordinates
  -- of the vector measure on every measurable set.
  have hre (s : Set β) (hs : MeasurableSet s) :
      (∫ x in s, (c.rnDeriv c.variation x).re ∂c.variation) = (c s).re := by
    have h := congrArg (fun q : ComplexMeasure β => q s) hrepr
    rw [withDensityᵥ_apply hf hs] at h
    -- take real parts of the Bochner integral
    have h' := congrArg Complex.re h
    rw [← RCLike.re_eq_complex_re,
      ← integral_re hf.integrableOn,
      RCLike.re_eq_complex_re] at h'
    exact h'
  have him (s : Set β) (hs : MeasurableSet s) :
      (∫ x in s, (c.rnDeriv c.variation x).im ∂c.variation) = (c s).im := by
    have h := congrArg (fun q : ComplexMeasure β => q s) hrepr
    rw [withDensityᵥ_apply hf hs] at h
    have h' := congrArg Complex.im h
    rw [← RCLike.im_eq_complex_im,
      ← integral_im hf.integrableOn,
      RCLike.im_eq_complex_im] at h'
    exact h'
  -- Put the ENNReal estimate `‖c s‖ ≤ |c| s` into ordinary reals.  Finiteness
  -- of variation on all sets is essential for `toReal`.
  have hnorm (s : Set β) (hs : MeasurableSet s) :
      ‖c s‖ ≤ c.variation.real s := by
    have hle : ENNReal.ofReal ‖c s‖ ≤ c.variation s := by
      simpa [ofReal_norm] using (VectorMeasure.enorm_measure_le_variation c s)
    have htop : c.variation s ≠ ∞ := measure_ne_top _ _
    -- applying `toReal` is legitimate on the finite right hand side
    have hreal := ENNReal.toReal_mono htop hle
    simpa [ENNReal.toReal_ofReal (norm_nonneg _), Measure.real] using hreal
  have hone_int (s : Set β) (hs : MeasurableSet s) :
      (∫ _x : β in s, (1 : ℝ) ∂c.variation) = c.variation.real s := by
    simp [Measure.real, hs]
  have hmone_int (s : Set β) (hs : MeasurableSet s) :
      (∫ _x : β in s, (-1 : ℝ) ∂c.variation) = -(c.variation.real s) := by
    simp [Measure.real, hs]
  have hre_le :
      (fun x => (c.rnDeriv c.variation x).re) ≤ᵐ[c.variation] (fun _ : β => (1:ℝ)) := by
    refine ae_le_of_forall_setIntegral_le hfre (integrable_const (1:ℝ)) ?_
    intro s hs hfin
    rw [hre s hs, hone_int s hs]
    exact (le_trans (le_abs_self _) (le_trans (Complex.abs_re_le_norm _) (hnorm s hs)))
  have hre_ge :
      (fun _ : β => (-1:ℝ)) ≤ᵐ[c.variation] (fun x => (c.rnDeriv c.variation x).re) := by
    refine ae_le_of_forall_setIntegral_le (integrable_const (-1:ℝ)) hfre ?_
    intro s hs hfin
    rw [hmone_int s hs, hre s hs]
    have hA : |(c s).re| ≤ c.variation.real s :=
      le_trans (Complex.abs_re_le_norm _) (hnorm s hs)
    linarith [neg_le_of_abs_le hA]
  have him_le :
      (fun x => (c.rnDeriv c.variation x).im) ≤ᵐ[c.variation] (fun _ : β => (1:ℝ)) := by
    refine ae_le_of_forall_setIntegral_le hfim (integrable_const (1:ℝ)) ?_
    intro s hs hfin
    rw [him s hs, hone_int s hs]
    exact (le_trans (le_abs_self _) (le_trans (Complex.abs_im_le_norm _) (hnorm s hs)))
  have him_ge :
      (fun _ : β => (-1:ℝ)) ≤ᵐ[c.variation] (fun x => (c.rnDeriv c.variation x).im) := by
    refine ae_le_of_forall_setIntegral_le (integrable_const (-1:ℝ)) hfim ?_
    intro s hs hfin
    rw [hmone_int s hs, him s hs]
    have hA : |(c s).im| ≤ c.variation.real s :=
      le_trans (Complex.abs_im_le_norm _) (hnorm s hs)
    linarith [neg_le_of_abs_le hA]
  filter_upwards [hre_le, hre_ge, him_le, him_ge] with x hx₁ hx₂ hx₃ hx₄
  constructor
  · exact (abs_le).2 ⟨by linarith, hx₁⟩
  · exact (abs_le).2 ⟨by linarith, hx₃⟩




-- all rotated real supporting hyperplanes also give a pointwise bound.
lemma rnDeriv_variation_ae_mul_re_le_norm {β : Type*} [MeasurableSpace β]
    (c : ComplexMeasure β) (a : ℂ) :
    (fun x => (a * c.rnDeriv c.variation x).re) ≤ᵐ[c.variation]
        (fun _ : β => (‖a‖ : ℝ)) := by
  letI : IsFiniteMeasure c.variation := complex_variation_finite c
  have hf : Integrable (c.rnDeriv c.variation) c.variation :=
    ComplexMeasure.integrable_rnDeriv _ _
  have hfa0 : Integrable (fun x => a * c.rnDeriv c.variation x) c.variation := by
    simpa [Pi.smul_def, smul_eq_mul] using hf.smul a
  have hfa : Integrable (fun x => (a * c.rnDeriv c.variation x).re) c.variation :=
    hfa0.re
  have hrepr := complex_withDensityv_variation c
  have hnorm (s : Set β) (hs : MeasurableSet s) : ‖c s‖ ≤ c.variation.real s := by
    have hle : ENNReal.ofReal ‖c s‖ ≤ c.variation s := by
      simpa [ofReal_norm] using (VectorMeasure.enorm_measure_le_variation c s)
    have htop : c.variation s ≠ ∞ := measure_ne_top _ _
    have hreal := ENNReal.toReal_mono htop hle
    simpa [ENNReal.toReal_ofReal (norm_nonneg _), Measure.real] using hreal
  refine ae_le_of_forall_setIntegral_le hfa (integrable_const (‖a‖ : ℝ)) ?_
  intro s hs hfin
  have hcset : (∫ x in s, c.rnDeriv c.variation x ∂c.variation) = c s := by
    have h := congrArg (fun q : ComplexMeasure β => q s) hrepr
    rw [withDensityᵥ_apply hf hs] at h
    exact h
  have hmul : (∫ x in s, a * c.rnDeriv c.variation x ∂c.variation) = a * c s := by
    calc
      _ = a • (∫ x in s, c.rnDeriv c.variation x ∂c.variation) := by
        simpa [smul_eq_mul] using
          (integral_smul a (fun x : β => c.rnDeriv c.variation x)
            (μ:=c.variation.restrict s))
      _ = _ := by rw [hcset, smul_eq_mul]
  have hmulre := congrArg Complex.re hmul
  have hleft : (∫ x in s, (a * c.rnDeriv c.variation x).re ∂c.variation)
      = (a * c s).re := by
    calc
      _ = ((∫ x in s, a * c.rnDeriv c.variation x ∂c.variation) : ℂ).re := by
        exact integral_re hfa0.integrableOn
      _ = _ := hmulre

  have hright : (∫ _x : β in s, (‖a‖ : ℝ) ∂c.variation)
      = ‖a‖ * c.variation.real s := by
    simp [Measure.real, mul_comm]
  rw [hleft, hright]
  calc
    (a * c s).re ≤ |(a * c s).re| := le_abs_self _
    _ ≤ ‖a * c s‖ := Complex.abs_re_le_norm _
    _ = ‖a‖ * ‖c s‖ := norm_mul _ _
    _ ≤ ‖a‖ * c.variation.real s := by
      exact mul_le_mul_of_nonneg_left (hnorm s hs) (norm_nonneg _)


private lemma complex_norm_le_one_of_rat_re_mul
    (z : ℂ)
    (h : ∀ p q : ℚ,
      ((((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I) * z).re ≤
        ‖(((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)‖) :
    ‖z‖ ≤ (1:ℝ) := by
  -- first extend the rational supporting-hyperplane inequalities in each
  -- of the two real coordinates by continuity.
  have hreal : ∀ p q : ℝ,
      ((((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I) * z).re ≤
        ‖(((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)‖ := by
    intro p q
    have hq_rat (q0 : ℚ) : ∀ p' : ℝ,
        ((((p' : ℝ) : ℂ) + (((q0 : ℚ) : ℝ) : ℂ) * Complex.I) * z).re ≤
          ‖(((p' : ℝ) : ℂ) + (((q0 : ℚ) : ℝ) : ℂ) * Complex.I)‖ := by
      intro p'
      refine Rat.denseRange_cast.induction_on p' ?_ ?_
      · exact isClosed_le (by fun_prop) (by fun_prop)
      · intro r
        exact h r q0
    -- now extend the second coordinate as well, keeping the chosen real p.
    refine Rat.denseRange_cast.induction_on q ?_ ?_
    · exact isClosed_le (by fun_prop) (by fun_prop)
    · intro r
      exact hq_rat r p
  have hz := hreal (z.re) (-z.im)
  have ha : (((z.re : ℝ) : ℂ) + ((-z.im : ℝ) : ℂ) * Complex.I) =
      starRingEnd ℂ z := by
    apply Complex.ext <;> simp
  rw [ha, Complex.conj_mul'] at hz
  -- taking `a = conj z` in the extended inequality gives `‖z‖² ≤ ‖z‖`.
  -- Norm nonnegativity then supplies the claimed upper bound.
  have hz' : ‖z‖ ^ (2:ℕ) ≤ ‖z‖ := by
    convert hz using 1
    · norm_num [pow_two, Complex.mul_re]
    · exact (Complex.norm_conj z).symm
  have hn : 0 ≤ ‖z‖ := norm_nonneg _
  nlinarith

lemma rnDeriv_variation_norm_le_one {β : Type*} [MeasurableSpace β]
    (c : ComplexMeasure β) :
      ∀ᵐ x ∂c.variation, ‖c.rnDeriv c.variation x‖ ≤ (1:ℝ) := by
  -- keep the dense, countable family of supporting hyperplanes in a single
  -- a.e. statement before applying the elementary plane argument.
  have hr : ∀ p q : ℚ,
      ∀ᵐ x ∂c.variation,
        ((((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I) *
          c.rnDeriv c.variation x).re ≤
          ‖(((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)‖ := by
    intro p q
    exact rnDeriv_variation_ae_mul_re_le_norm c
      (((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)
  have hall : ∀ᵐ x ∂c.variation, ∀ p : ℚ, ∀ q : ℚ,
        ((((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I) *
          c.rnDeriv c.variation x).re ≤
          ‖(((p : ℝ) : ℂ) + ((q : ℝ) : ℂ) * Complex.I)‖ := by
    rw [ae_all_iff]
    intro p
    rw [ae_all_iff]
    intro q
    exact hr p q
  filter_upwards [hall] with x hx
  exact complex_norm_le_one_of_rat_re_mul _ hx



lemma integral_mul_rnDeriv_eq_vector
    (t : ComplexMeasure UnitAddCircle) [IsFiniteMeasure t.variation]
    (f : C(UnitAddCircle, ℂ)) :
    (∫ x : UnitAddCircle, t.rnDeriv t.variation x * f x ∂t.variation) =
      (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; t]) := by
  classical
  let ψ : UnitAddCircle → ℂ := t.rnDeriv t.variation
  have hψint : Integrable ψ t.variation := ComplexMeasure.integrable_rnDeriv _ _
  have hψm : Measurable ψ := by
    dsimp [ψ]
    apply measurable_of_re_im
    · exact SignedMeasure.measurable_rnDeriv _ _
    · exact SignedMeasure.measurable_rnDeriv _ _
  have hψb : ∀ᵐ x ∂t.variation, ‖ψ x‖ ≤ (1:ℝ) :=
    rnDeriv_variation_norm_le_one t
  let gm : MemLp ψ ∞ t.variation := memLp_top_of_bound hψm.aestronglyMeasurable 1 hψb
  let g : Lp ℂ ∞ t.variation := gm.toLp ψ
  have hg : (g : UnitAddCircle → ℂ) =ᵐ[t.variation] ψ := MemLp.coeFn_toLp _
  let T := t.transpose (ContinuousLinearMap.mul ℝ ℂ)
  let hT := MeasureTheory.dominatedFinMeasAdditive_cbmApplyMeasure t
      (ContinuousLinearMap.mul ℝ ℂ)
  have hsmul : ∀ a : ℂ, ∀ s x, T s (a • x) = a • T s x := by
    intro a s x
    change (a * x) * t s = a * (x * t s)
    exact mul_assoc _ _ _
  let S : (Lp ℂ 1 t.variation) →L[ℂ] ℂ :=
      MeasureTheory.L1.setToL1' ℂ hT hsmul
  let M : Lp ℂ 1 t.variation →L[ℂ] Lp ℂ 1 t.variation :=
      lpMulLeftOne t.variation g
  let J : Lp ℂ 1 t.variation →L[ℂ] ℂ :=
      (MeasureTheory.L1.integralCLM' (α:=UnitAddCircle) (E:=ℂ) ℂ
        (μ:=t.variation)).comp M
  have hSJ : ∀ u : Lp ℂ 1 t.variation, S u = J u := by
    -- induction on the dense simple functions in L1
    refine MeasureTheory.Lp.induction (p:=(1:ENNReal)) (by simp : (1:ENNReal) ≠ ∞)
      (motive := fun u : Lp ℂ 1 t.variation => S u = J u) ?_ ?_ ?_ 
    · intro c s hs hfin
      -- evaluate both maps on an indicator
      change S (Lp.simpleFunc.indicatorConst (1:ENNReal) hs hfin.ne c : Lp ℂ 1 t.variation) = _
      have hleft : S (Lp.simpleFunc.indicatorConst (1:ENNReal) hs hfin.ne c : Lp ℂ 1 t.variation) =
          c * t s := by
        dsimp [S]
        rw [← MeasureTheory.L1.setToL1_eq_setToL1' hT hsmul]
        rw [MeasureTheory.L1.setToL1_indicatorConstLp hT hs hfin.ne c]
        rfl
      rw [hleft]
      -- compute the ordinary integral using representatives
      change c * t s = MeasureTheory.L1.integralCLM'
          (α:=UnitAddCircle) (E:=ℂ) ℂ (μ:=t.variation)
          (M (Lp.simpleFunc.indicatorConst (1:ENNReal) hs hfin.ne c : Lp ℂ 1 t.variation))
      rw [← MeasureTheory.L1.integral_eq' ℂ]
      have hrepr :
          (M (Lp.simpleFunc.indicatorConst (1:ENNReal) hs hfin.ne c : Lp ℂ 1 t.variation) :
              UnitAddCircle → ℂ) =ᵐ[t.variation]
            s.indicator (fun x => ψ x * c) := by
        have hm := Lp.coeFn_lpSMul (r:=1) g
          (Lp.simpleFunc.indicatorConst (1:ENNReal) hs hfin.ne c : Lp ℂ 1 t.variation)
        have hi := @indicatorConstLp_coeFn UnitAddCircle ℂ _ (1:ENNReal) _ _ _ hs hfin.ne c
        filter_upwards [hm, hg, hi] with x hx hgx hix
        change (((g • (Lp.simpleFunc.indicatorConst (1:ENNReal) hs hfin.ne c : Lp ℂ 1 t.variation) : Lp ℂ 1 t.variation) : UnitAddCircle → ℂ) x) = _
        rw [hx]
        change (g : UnitAddCircle → ℂ) x * _ = _
        rw [hgx]
        change ψ x * ((indicatorConstLp (1:ENNReal) hs hfin.ne c : Lp ℂ 1 t.variation) : UnitAddCircle → ℂ) x = _
        rw [hix]
        by_cases hx' : x ∈ s <;> simp [Set.indicator, hx']
      rw [MeasureTheory.L1.integral_eq_integral]
      rw [integral_congr_ae hrepr]
      rw [integral_indicator hs]
      -- use the reconstruction of the measure
      have hrep := complex_withDensityv_variation t
      have hts : t s = ∫ x in s, ψ x ∂t.variation := by
        have h := congrArg (fun v : ComplexMeasure UnitAddCircle => v s) hrep
        rw [withDensityᵥ_apply hψint hs] at h
        exact h.symm
      rw [hts]
      calc
        c * (∫ x in s, ψ x ∂t.variation) =
            c • (∫ x in s, ψ x ∂t.variation) := rfl
        _ = ∫ x in s, c • ψ x ∂t.variation := by
            rw [integral_smul]
        _ = ∫ x in s, ψ x * c ∂t.variation := by
            apply integral_congr_ae
            filter_upwards [] with x
            simp [smul_eq_mul, mul_comm]
    · intro a b ha hb hd ia ib
      rw [map_add, map_add, ia, ib]
    · exact isClosed_eq S.continuous J.continuous
  have hfint : Integrable (fun x : UnitAddCircle => f x) t.variation :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hset := MeasureTheory.setToFun_eq hT hfint
  let uf : Lp ℂ 1 t.variation := hfint.toL1 (fun x : UnitAddCircle => f x)
  have hu := hSJ uf
  have hL : S uf = (∫ᵛ x, f x ∂[ContinuousLinearMap.mul ℝ ℂ; t]) := by
    dsimp [S]
    rw [← MeasureTheory.L1.setToL1_eq_setToL1' hT hsmul]
    have hh := MeasureTheory.setToFun_eq hT hfint
    exact hh.symm
  have hfu : (uf : UnitAddCircle → ℂ) =ᵐ[t.variation] (fun x => f x) :=
    hfint.coeFn_toL1
  have hMU : (M uf : UnitAddCircle → ℂ) =ᵐ[t.variation]
      (fun x => ψ x * f x) := by
    have hm := Lp.coeFn_lpSMul (r:=1) g uf
    filter_upwards [hm, hg, hfu] with x hx hgx hfx
    change (((g • uf : Lp ℂ 1 t.variation) : UnitAddCircle → ℂ) x) = _
    rw [hx]
    change (g : UnitAddCircle → ℂ) x * (uf : UnitAddCircle → ℂ) x = _
    rw [hgx, hfx]
  have hR : J uf = (∫ x : UnitAddCircle, ψ x * f x ∂t.variation) := by
    change MeasureTheory.L1.integralCLM'
       (α:=UnitAddCircle) (E:=ℂ) ℂ (μ:=t.variation) (M uf) = _
    rw [← MeasureTheory.L1.integral_eq' ℂ]
    rw [MeasureTheory.L1.integral_eq_integral]
    exact integral_congr_ae hMU
  change (∫ x : UnitAddCircle, ψ x * f x ∂t.variation) = _
  rw [← hR, ← hu, hL]

/-- The polar density is at least square--integrable with respect to variation.
Only the coordinate bound is needed; avoiding the equality `‖d c /d|c|‖=1`
makes this little preparatory fact independent of the polar decomposition
machinery. -/
lemma rnDeriv_variation_memLp_two {β : Type*} [MeasurableSpace β]
    (c : ComplexMeasure β) :
    MemLp (c.rnDeriv c.variation) 2 c.variation := by
  letI : IsFiniteMeasure c.variation := complex_variation_finite c
  have hm : Measurable (c.rnDeriv c.variation) := by
    apply measurable_of_re_im
    · exact SignedMeasure.measurable_rnDeriv _ _
    · exact SignedMeasure.measurable_rnDeriv _ _
  have hsm : AEStronglyMeasurable (c.rnDeriv c.variation) c.variation :=
    hm.aestronglyMeasurable
  refine (memLp_two_iff_integrable_sq_norm hsm).2 ?_
  have hsm' : AEStronglyMeasurable
      (fun x : β => ‖c.rnDeriv c.variation x‖ ^ (2:ℕ)) c.variation := by
    simpa [Pi.pow_def] using hsm.norm.pow 2
  refine Integrable.mono' (μ:=c.variation) (f:=fun x : β => ‖c.rnDeriv c.variation x‖ ^ (2:ℕ))
       (g:=fun _ : β => (2:ℝ))
       (integrable_const (2:ℝ)) hsm' ?_
  filter_upwards [rnDeriv_variation_ae_abs_re_im_le_one c] with x hx
  change |‖c.rnDeriv c.variation x‖ ^ (2:ℕ)| ≤ (2:ℝ)
  have hr := (abs_le.1 hx.1)
  have hi := (abs_le.1 hx.2)
  have hsq : ‖c.rnDeriv c.variation x‖ ^ (2:ℕ)
        = (c.rnDeriv c.variation x).re * (c.rnDeriv c.variation x).re +
          (c.rnDeriv c.variation x).im * (c.rnDeriv c.variation x).im := by
    rw [Complex.sq_norm, Complex.normSq_apply]
  have hnon : 0 ≤ ‖c.rnDeriv c.variation x‖ ^ (2:ℕ) := sq_nonneg _
  rw [abs_of_nonneg hnon, hsq]
  nlinarith

/-- A concrete representative of the polar vector in `L²(|c|)`. -/
noncomputable def rnDerivVariationLpTwo {β : Type*} [MeasurableSpace β]
    (c : ComplexMeasure β) : Lp ℂ 2 c.variation :=
  (rnDeriv_variation_memLp_two c).toLp (c.rnDeriv c.variation)

lemma coe_rnDerivVariationLpTwo {β : Type*} [MeasurableSpace β]
    (c : ComplexMeasure β) :
    (rnDerivVariationLpTwo c : β → ℂ) =ᵐ[c.variation]
       c.rnDeriv c.variation := by
  exact MemLp.coeFn_toLp _


lemma spectralMeasure_rnDerivVariationLpTwo
    (c : ComplexMeasure UnitAddCircle) :
    spectralMeasure c.variation (rnDerivVariationLpTwo c) =
      c.variation.withDensity
        (fun x : UnitAddCircle => ENNReal.ofReal (‖c.rnDeriv c.variation x‖ ^ 2)) := by
  unfold spectralMeasure
  apply withDensity_congr_ae
  filter_upwards [coe_rnDerivVariationLpTwo c] with x hx
  rw [hx]


-- EXTRA WOLD HELPERS TEST
noncomputable def shiftLpEquiv (q : Measure UnitAddCircle) (k : ℤ) :
    Lp ℂ 2 q ≃ₗᵢ[ℂ] Lp ℂ 2 q where
  toFun := lpMulLeft q (circleCharLpTop q k)
  invFun := lpMulLeft q (circleCharLpTop q (-k))
  left_inv := by
    intro u
    exact lpMul_circleChar_neg_left q k u
  right_inv := by
    intro u
    exact lpMul_circleChar_neg_right q k u
  map_add' := (lpMulLeft q (circleCharLpTop q k)).map_add
  map_smul' := (lpMulLeft q (circleCharLpTop q k)).map_smul
  norm_map' := lpMul_circleChar_norm q k

noncomputable def nonnegFourierSub (q : Measure UnitAddCircle) [IsFiniteMeasure q] :
    Submodule ℂ (Lp ℂ 2 q) :=
  (Submodule.span ℂ (Set.range (fun n : ℕ => fourierLpAny q (n:ℤ)))).topologicalClosure

noncomputable def posFourierSub (q : Measure UnitAddCircle) [IsFiniteMeasure q] :
    Submodule ℂ (Lp ℂ 2 q) := (nonnegFourierSub q).map (shiftLpEquiv q 1 : Lp ℂ 2 q →ₗ[ℂ] _)

lemma nonnegFourierSub_isClosed (q : Measure UnitAddCircle) [IsFiniteMeasure q] :
    IsClosed (nonnegFourierSub q : Set (Lp ℂ 2 q)) :=
  Submodule.isClosed_topologicalClosure _

lemma posFourierSub_isClosed (q : Measure UnitAddCircle) [IsFiniteMeasure q] :
    IsClosed (posFourierSub q : Set (Lp ℂ 2 q)) := by
  -- an equivalence is a closed map
  have h := ((shiftLpEquiv q 1).toHomeomorph.isClosed_image (s:=(nonnegFourierSub q : Set _))).2
      (nonnegFourierSub_isClosed q)
  simpa [posFourierSub, Set.image_image] using h



lemma posFourierSub_le (q : Measure UnitAddCircle) [IsFiniteMeasure q] :
    posFourierSub q ≤ nonnegFourierSub q := by
  let N : Submodule ℂ (Lp ℂ 2 q) :=
    Submodule.span ℂ (Set.range (fun n : ℕ => fourierLpAny q (n:ℤ)))
  have hgen : Submodule.map (shiftLpEquiv q 1 : _ →ₗ[ℂ] _) N ≤ N := by
    refine (Submodule.map_le_iff_le_comap).2 ?_
    -- prove on generators
    refine (Submodule.span_le).2 ?_
    rintro x ⟨n, rfl⟩
    -- image of a generator is the following generator
    change (shiftLpEquiv q 1) (fourierLpAny q (n:ℤ)) ∈ N
    have heq : (shiftLpEquiv q 1) (fourierLpAny q (n:ℤ)) =
        fourierLpAny q ((n+1:ℕ):ℤ) := by
      change lpMulLeft q (circleCharLpTop q 1) (fourierLpAny q (n:ℤ)) = _
      -- reorder the integer sum
      convert fourierLpAny_mul q 1 (n:ℤ) using 1 <;> norm_cast <;> simp [Nat.cast_add, Nat.cast_one, add_comm]
    rw [heq]
    exact Submodule.subset_span ⟨(n+1), rfl⟩
  change Submodule.map (shiftLpEquiv q 1 : _ →ₗ[ℂ] _) N.topologicalClosure ≤
    N.topologicalClosure
  refine le_trans (Submodule.topologicalClosure_map _ _) ?_
  exact Submodule.topologicalClosure_minimal _
    (le_trans hgen (Submodule.le_topologicalClosure _))
    (Submodule.isClosed_topologicalClosure _)

lemma nonneg_shift_nat (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (n : ℕ) {u : Lp ℂ 2 q} (hu : u ∈ nonnegFourierSub q) :
    lpMulLeft q (circleCharLpTop q (n:ℤ)) u ∈ nonnegFourierSub q := by
  induction n with
  | zero => simpa using hu
  | succ n ih =>
    have hprev := ih
    have hm : lpMulLeft q (circleCharLpTop q 1)
        (lpMulLeft q (circleCharLpTop q (n:ℤ)) u) ∈ nonnegFourierSub q := by
      apply posFourierSub_le q
      exact ⟨_, hprev, rfl⟩
    rw [lpMul_circleChar_add] at hm
    convert hm using 1 <;> norm_cast <;> simp [Nat.cast_add, Nat.cast_one, add_comm]

lemma nonneg_shift_nat_mem_pos (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (n : ℕ) (hn : 1 ≤ n) {u : Lp ℂ 2 q} (hu : u ∈ nonnegFourierSub q) :
    lpMulLeft q (circleCharLpTop q (n:ℤ)) u ∈ posFourierSub q := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  have hj := nonneg_shift_nat q j hu
  -- 1 + j as exponent
  have mem : lpMulLeft q (circleCharLpTop q 1)
      (lpMulLeft q (circleCharLpTop q (j:ℤ)) u) ∈ posFourierSub q :=
    ⟨_, hj, rfl⟩
  rw [lpMul_circleChar_add] at mem
  convert mem using 1 <;> norm_cast <;> simp [Nat.cast_add, Nat.cast_one, add_comm]

lemma inner_zero_of_opposite_support (q : Measure UnitAddCircle)
    (E : Set UnitAddCircle) (hE : MeasurableSet E)
    (u v : Lp ℂ 2 q)
    (hu : ∀ᵐ x ∂q.restrict Eᶜ, (u : UnitAddCircle → ℂ) x = 0)
    (hv : ∀ᵐ x ∂q.restrict E, (v : UnitAddCircle → ℂ) x = 0) :
    @inner ℂ _ _ u v = 0 := by
  rw [MeasureTheory.L2.inner_def]
  have hu' : ∀ᵐ x ∂q, x ∈ Eᶜ → (u : UnitAddCircle → ℂ) x = 0 :=
    (ae_restrict_iff' hE.compl).1 hu
  have hv' : ∀ᵐ x ∂q, x ∈ E → (v : UnitAddCircle → ℂ) x = 0 :=
    (ae_restrict_iff' hE).1 hv
  have hzero : (fun x : UnitAddCircle => @inner ℂ _ _ (u x) (v x)) =ᵐ[q] 0 := by
    filter_upwards [hu', hv'] with x hx hy
    by_cases h : x ∈ E
    · simp [hy h]
    · have hc : x ∈ Eᶜ := h
      simp [hx hc]
  exact integral_eq_zero_of_ae hzero

lemma spectral_ae_zero_on_null (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (w : Lp ℂ 2 q) (E : Set UnitAddCircle) (hE : MeasurableSet E)
    (hE0 : AddCircle.haarAddCircle E = 0)
    (hwac : spectralMeasure q w ≪ AddCircle.haarAddCircle) :
    ∀ᵐ x ∂q.restrict E, (w : UnitAddCircle → ℂ) x = 0 := by
  have hz : (spectralMeasure q w) E = 0 := hwac hE0
  have hmeas : AEMeasurable
      (fun x : UnitAddCircle => ENNReal.ofReal ((‖w x‖ : ℝ)^2)) (q.restrict E) :=
    ((Lp.aestronglyMeasurable w).norm.aemeasurable.restrict.pow_const _).ennreal_ofReal
  change (q.withDensity (fun x : UnitAddCircle => ENNReal.ofReal ((‖w x‖ : ℝ)^2))) E = 0 at hz
  rw [withDensity_apply _ hE] at hz
  have hh : (fun x : UnitAddCircle => ENNReal.ofReal ((‖w x‖ : ℝ)^2)) =ᵐ[q.restrict E] 0 :=
    (lintegral_eq_zero_iff' hmeas).1 hz
  filter_upwards [hh] with x hx
  have hle : (‖w x‖ : ℝ)^2 ≤ 0 := ENNReal.ofReal_eq_zero.mp hx
  have hnorm : ‖w x‖ = 0 := by
    have hn : 0 ≤ ‖w x‖ := norm_nonneg _
    nlinarith
  exact norm_eq_zero.mp hnorm
lemma wandering_zero_on_null (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (E : Set UnitAddCircle) (hE : MeasurableSet E)
    (hE0 : AddCircle.haarAddCircle E = 0)
    (u : Lp ℂ 2 q) (hu0 : u ∈ nonnegFourierSub q)
    (hu1 : u ∈ (posFourierSub q)ᗮ) :
    ∀ᵐ x ∂q.restrict E, (u : UnitAddCircle → ℂ) x = 0 := by
  have hwand : ∀ n : ℕ, 1 ≤ n →
      @inner ℂ _ _ u (lpMulLeft q (circleCharLpTop q (n:ℤ)) u) = 0 := by
    intro n hn
    exact Submodule.inner_left_of_mem_orthogonal
      (nonneg_shift_nat_mem_pos q n hn hu0) hu1
  exact spectral_ae_zero_on_null q u E hE hE0
    (spectralMeasure_ac_of_wandering_nat q u hwand)


def shiftBackSub (q : Measure UnitAddCircle) [IsFiniteMeasure q] (n : ℕ) :
    Submodule ℂ (Lp ℂ 2 q) :=
  (nonnegFourierSub q).map (shiftLpEquiv q (-(n:ℤ)) : Lp ℂ 2 q →ₗ[ℂ] _)

lemma mem_shiftBack (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (n : ℕ) (x : Lp ℂ 2 q) :
    x ∈ shiftBackSub q n ↔
      lpMulLeft q (circleCharLpTop q (n:ℤ)) x ∈ nonnegFourierSub q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    change lpMulLeft q (circleCharLpTop q (n:ℤ))
      (lpMulLeft q (circleCharLpTop q (-(n:ℤ))) y) ∈ _
    rw [lpMul_circleChar_neg_right]
    exact hy
  · intro hx
    refine ⟨lpMulLeft q (circleCharLpTop q (n:ℤ)) x, hx, ?_⟩
    change lpMulLeft q (circleCharLpTop q (-(n:ℤ)))
      (lpMulLeft q (circleCharLpTop q (n:ℤ)) x) = x
    exact lpMul_circleChar_neg_left q (n:ℤ) x

lemma shiftBack_mono (q : Measure UnitAddCircle) [IsFiniteMeasure q] (n : ℕ) :
    shiftBackSub q n ≤ shiftBackSub q (n+1) := by
  intro x hx
  apply (mem_shiftBack q (n+1) x).2
  have hy := (mem_shiftBack q n x).1 hx
  have hh : lpMulLeft q (circleCharLpTop q 1)
      (lpMulLeft q (circleCharLpTop q (n:ℤ)) x) ∈ nonnegFourierSub q := by
    apply posFourierSub_le q
    exact ⟨_, hy, rfl⟩
  rw [lpMul_circleChar_add] at hh
  convert hh using 1 <;> norm_cast <;> simp [Nat.cast_add, Nat.cast_one, add_comm]

lemma shiftBack_decompose (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (n : ℕ) {x : Lp ℂ 2 q} (hx : x ∈ shiftBackSub q (n+1)) :
    ∃ y ∈ shiftBackSub q n, ∃ w,
      w ∈ nonnegFourierSub q ∧ w ∈ (posFourierSub q)ᗮ ∧
      x = y + lpMulLeft q (circleCharLpTop q (-((n+1:ℕ):ℤ))) w := by
  -- decompose U^(n+1) x inside M into its projection on U M
  let M1 := posFourierSub q
  have hclosed := posFourierSub_isClosed q
  letI : CompleteSpace M1 := by
    change CompleteSpace (posFourierSub q)
    exact @IsClosed.completeSpace_coe _ _ _ _ hclosed
  letI : Submodule.HasOrthogonalProjection M1 :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M1
  have hxM : lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) x ∈
      nonnegFourierSub q := (mem_shiftBack q (n+1) x).1 hx
  obtain ⟨v, hv, hworth⟩ :=
    (Submodule.HasOrthogonalProjection.exists_orthogonal (K:=M1)
      (lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) x))
  let w : Lp ℂ 2 q := lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) x - v
  have hw : w ∈ M1ᗮ := by exact hworth
  have hv0 : v ∈ nonnegFourierSub q := posFourierSub_le q hv
  have hw0 : w ∈ nonnegFourierSub q := Submodule.sub_mem _ hxM hv0
  obtain ⟨v0, hv0M, hv0eq⟩ := hv
  -- v = U v0
  let y : Lp ℂ 2 q := lpMulLeft q (circleCharLpTop q (-(n:ℤ))) v0
  have hy : y ∈ shiftBackSub q n := by
    apply (mem_shiftBack q n y).2
    dsimp [y]
    rw [lpMul_circleChar_neg_right]
    exact hv0M
  refine ⟨y, hy, w, hw0, hw, ?_⟩
  -- apply U^(n+1) to the equality
  apply (shiftLpEquiv q ((n+1:ℕ):ℤ)).injective
  change lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) x = _
  rw [map_add]
  have hycalc : lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) y = v := by
    dsimp [y]
    rw [lpMul_circleChar_add]
    -- exponents (n+1) + (-n) = 1
    have hnum : (n:ℤ) + 1 + -(n:ℤ) = 1 := by omega
    rw [hnum]
    exact hv0eq
  change _ = lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) y +
      lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ))
        (lpMulLeft q (circleCharLpTop q (-((n+1:ℕ):ℤ))) w)
  rw [hycalc]
  change _ = v + lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ))
      (lpMulLeft q (circleCharLpTop q (-((n+1:ℕ):ℤ))) w)
  rw [lpMul_circleChar_neg_right]
  dsimp [w]
  abel

lemma shiftBack_incr_neutral (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (n : ℕ) {p : Lp ℂ 2 q} (hp : p ∈ shiftBackSub q n)
    {w : Lp ℂ 2 q} (hw : w ∈ (posFourierSub q)ᗮ) :
    @inner ℂ _ _ p (lpMulLeft q (circleCharLpTop q (-((n+1:ℕ):ℤ))) w) = 0 := by
  have hp' := (mem_shiftBack q n p).1 hp
  -- express both terms by U^-(n+1)
  have hinner := (shiftLpEquiv q ((n+1:ℕ):ℤ)).inner_map_map p
      (lpMulLeft q (circleCharLpTop q (-((n+1:ℕ):ℤ))) w)
  -- after applying the equivalence, the second is w and first is U p with exponent n+1
  have hfirst : lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) p ∈
      posFourierSub q := by
    change _ ∈ _
    have hh : lpMulLeft q (circleCharLpTop q 1)
        (lpMulLeft q (circleCharLpTop q (n:ℤ)) p) ∈ posFourierSub q := ⟨_, hp', rfl⟩
    rw [lpMul_circleChar_add] at hh
    convert hh using 1 <;> norm_cast <;> simp [Nat.cast_add, Nat.cast_one, add_comm]
  have hz : @inner ℂ _ _
        (lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) p) w = 0 :=
    Submodule.inner_right_of_mem_orthogonal hfirst hw
  change @inner ℂ _ _
      (lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ)) p)
      (lpMulLeft q (circleCharLpTop q ((n+1:ℕ):ℤ))
        (lpMulLeft q (circleCharLpTop q (-((n+1:ℕ):ℤ))) w)) = _ at hinner
  rw [lpMul_circleChar_neg_right] at hinner
  exact hinner.symm ▸ hz



lemma supported_mem_posFourier (q : Measure UnitAddCircle) [IsFiniteMeasure q]
    (E : Set UnitAddCircle) (hE : MeasurableSet E)
    (hE0 : AddCircle.haarAddCircle E = 0)
    (g : Lp ℂ 2 q)
    (hg : ∀ᵐ x ∂q.restrict Eᶜ, (g : UnitAddCircle → ℂ) x = 0) :
    g ∈ posFourierSub q := by
  let M0 := nonnegFourierSub q
  have hclosed0 := nonnegFourierSub_isClosed q
  letI : CompleteSpace M0 := by
    change CompleteSpace (nonnegFourierSub q)
    exact @IsClosed.completeSpace_coe _ _ _ _ hclosed0
  letI : Submodule.HasOrthogonalProjection M0 :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M0
  obtain ⟨p, hp, hrp⟩ :=
    (Submodule.HasOrthogonalProjection.exists_orthogonal (K:=M0) g)
  let r : Lp ℂ 2 q := g - p
  have hr0 : r ∈ (nonnegFourierSub q)ᗮ := hrp
  -- orthogonality to all backwards shifts
  have hrn : ∀ n : ℕ, r ∈ (shiftBackSub q n)ᗮ := by
    intro n
    induction n with
    | zero =>
        refine (Submodule.mem_orthogonal _ _).2 ?_
        intro x hx
        have hx' := (mem_shiftBack q 0 x).1 hx
        have hx0 : x ∈ nonnegFourierSub q := by simpa using hx'
        exact (Submodule.mem_orthogonal _ _).1 hr0 x hx0
    | succ n ih =>
      refine (Submodule.mem_orthogonal _ _).2 ?_
      intro x hx
      obtain ⟨y, hy, w, hw0, hw1, hxy⟩ := shiftBack_decompose q n hx
      have hy0 : @inner ℂ _ _ y r = 0 := (Submodule.mem_orthogonal _ _).1 ih y hy
      let z : Lp ℂ 2 q := lpMulLeft q (circleCharLpTop q (-((n+1:ℕ):ℤ))) w
      have hwE : ∀ᵐ x ∂q.restrict E, (w : UnitAddCircle → ℂ) x = 0 :=
        wandering_zero_on_null q E hE hE0 w hw0 hw1
      have hzE : ∀ᵐ x ∂q.restrict E, (z : UnitAddCircle → ℂ) x = 0 := by
        have hm := Lp.coeFn_lpSMul (r:=2) (circleCharLpTop q (-((n+1:ℕ):ℤ))) w
        have hm' : ∀ᵐ x ∂q.restrict E,
            (((circleCharLpTop q (-((n+1:ℕ):ℤ)) • w : Lp ℂ 2 q) : UnitAddCircle → ℂ) x) =
            (((circleCharLpTop q (-((n+1:ℕ):ℤ)) : UnitAddCircle → ℂ) *
              (w : UnitAddCircle → ℂ)) x) :=
          Filter.Eventually.filter_mono (MeasureTheory.ae_mono (Measure.restrict_le_self)) hm
        filter_upwards [hwE, hm'] with x hxw hmul
        change (((circleCharLpTop q (-((n+1:ℕ):ℤ)) • w : Lp ℂ 2 q) : UnitAddCircle → ℂ) x) = 0
        rw [hmul]
        simp [hxw]
      have hgz : @inner ℂ _ _ g z = 0 :=
        inner_zero_of_opposite_support q E hE g z hg hzE
      have hzg : @inner ℂ _ _ z g = 0 := by
        rw [← inner_conj_symm] 
        simp [hgz]
      have hp_n : p ∈ shiftBackSub q n := by
        apply (mem_shiftBack q n p).2
        exact nonneg_shift_nat q n hp
      have hpz : @inner ℂ _ _ p z = 0 := shiftBack_incr_neutral q n hp_n hw1
      have hzp : @inner ℂ _ _ z p = 0 := by
        rw [← inner_conj_symm]
        simp [hpz]
      have hzr : @inner ℂ _ _ z r = 0 := by
        change @inner ℂ _ _ z (g - p) = 0
        rw [inner_sub_right, hzg, hzp]
        simp
      change @inner ℂ _ _ x r = 0
      rw [hxy, inner_add_left, hy0]
      exact (zero_add _).trans hzr
  -- the characters all occur in one of these backwards shifts
  let A : Submodule ℂ (Lp ℂ 2 q) := Submodule.span ℂ (Set.range (fourierLpAny q))
  have hrA : r ∈ Aᗮ := by
    refine (Submodule.mem_orthogonal _ _).2 ?_
    intro x hx
    -- linear induction on the span
    refine Submodule.span_induction (p:=fun x _ => @inner ℂ _ _ x r = 0) ?_ ?_ ?_ ?_ hx
    · intro v hv
      obtain ⟨k, rfl⟩ := hv
      let n : ℕ := Int.toNat (-k)
      have hkn : 0 ≤ k + (n:ℤ) := by dsimp [n]; omega
      let j : ℕ := Int.toNat (k + (n:ℤ))
      have hj : (j:ℤ) = k + (n:ℤ) := by
        dsimp [j]
        exact Int.toNat_of_nonneg hkn
      have hmem : fourierLpAny q k ∈ shiftBackSub q n := by
        apply (mem_shiftBack q n _).2
        rw [fourierLpAny_mul]
        have hsum : (n:ℤ) + k = (j:ℤ) := by rw [hj]; abel
        rw [hsum]
        exact (Submodule.le_topologicalClosure _)
          (Submodule.subset_span ⟨j, rfl⟩)
      exact (Submodule.mem_orthogonal _ _).1 (hrn n) _ hmem
    · simp
    · intro a b ha hb hia hib
      simp [inner_add_left, hia, hib]
    · intro a x hx hi
      simp [inner_smul_left, hi]
  have hAbot : Aᗮ = (⊥ : Submodule ℂ (Lp ℂ 2 q)) :=
    (Submodule.topologicalClosure_eq_top_iff).1 (span_fourierLpAny_closure_eq_top q)
  have hrzero : r = 0 := by
    have : r ∈ (⊥ : Submodule ℂ (Lp ℂ 2 q)) := hAbot ▸ hrA
    simpa using this
  have hgp : g = p := by
    have : g - p = 0 := hrzero
    exact sub_eq_zero.mp this
  -- now do the one step inside M: its orthogonal component is again null on E
  have hg0 : g ∈ nonnegFourierSub q := hgp ▸ hp
  have hclosed1 := posFourierSub_isClosed q
  let M1 := posFourierSub q
  letI : CompleteSpace M1 := by
    change CompleteSpace (posFourierSub q)
    exact @IsClosed.completeSpace_coe _ _ _ _ hclosed1
  letI : Submodule.HasOrthogonalProjection M1 :=
    Submodule.HasOrthogonalProjection.ofCompleteSpace M1
  obtain ⟨v, hv, hdv⟩ :=
    (Submodule.HasOrthogonalProjection.exists_orthogonal (K:=M1) g)
  let d : Lp ℂ 2 q := g - v
  have hd1 : d ∈ (posFourierSub q)ᗮ := hdv
  have hv0 : v ∈ nonnegFourierSub q := posFourierSub_le q hv
  have hd0 : d ∈ nonnegFourierSub q := Submodule.sub_mem _ hg0 hv0
  have hdE : ∀ᵐ x ∂q.restrict E, (d : UnitAddCircle → ℂ) x = 0 :=
    wandering_zero_on_null q E hE hE0 d hd0 hd1
  have hgd : @inner ℂ _ _ g d = 0 :=
    inner_zero_of_opposite_support q E hE g d hg hdE
  have hvd : @inner ℂ _ _ v d = 0 :=
    Submodule.inner_right_of_mem_orthogonal hv hd1
  have hdd : @inner ℂ _ _ d d = 0 := by
    change @inner ℂ _ _ (g - v) d = 0
    rw [inner_sub_left, hgd, hvd]
    simp
  have hdzero : d = 0 := (inner_self_eq_zero.mp hdd)
  have : g = v := sub_eq_zero.mp hdzero
  rw [this]
  exact hv
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem riesz_brothers_theorem (μ : ComplexMeasure UnitAddCircle)
    (hμ : ∀ n : ℕ, 1 ≤ n → ∫ᵛ z, fourier n z ∂[ContinuousLinearMap.mul ℝ ℂ; μ] = 0) :
    μ ≪ᵥ AddCircle.haarAddCircle.toENNRealVectorMeasure :=
/-ResultProofBegin-/ by
  -- Work at the finite normalized Haar measure.  Scalar vector measures really do have
  -- finite variation; it isn't an instance for arbitrary Banach-valued measures.
  letI : IsFiniteMeasure μ.variation := complex_variation_finite μ
  -- The ordinary Lebesgue decomposition exists for both coordinates against Haar.
  letI : μ.HaveLebesgueDecomposition AddCircle.haarAddCircle :=
    ⟨inferInstance, inferInstance⟩
  -- Consequently the Fourier hypothesis annihilates every finite analytic
  -- polynomial with zero constant term (over `ℂ`, not merely over `ℝ`).
  -- Pulling a complex coefficient through the vector integral is the subtle
  -- point; `integral` is a priori only real-linear.
  have hpoly (s : Finset ℕ) (hs : ∀ n ∈ s, 1 ≤ n) (a : ℕ → ℂ) :
      (∫ᵛ z : UnitAddCircle, (∑ n ∈ s, a n • fourier (n : ℤ) z)
        ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) = 0 :=
    integral_sum_fourier_pos μ hμ s hs a
  apply ac_of_singularPart_zero μ AddCircle.haarAddCircle
  -- At the final analytic step it is enough to identify the Fourier moments of the
  -- singular summand.  We make the reduction to moment uniqueness explicit; the
  -- Hahn--Jordan and L¹ density arguments above mean uniqueness itself does not
  -- hide a positivity assumption.
  let m : Measure UnitAddCircle := AddCircle.haarAddCircle
  let σ : ComplexMeasure UnitAddCircle := μ.singularPart m
  let ρ : ComplexMeasure UnitAddCircle := m.withDensityᵥ (μ.rnDeriv m)
  have hd : σ + ρ = μ := by
    dsimp [σ, ρ, m]
    exact ComplexMeasure.singularPart_add_withDensity_rnDeriv_eq
      (c := μ) (μ := AddCircle.haarAddCircle)
  have hsing : σ ⟂ᵥ m.toENNRealVectorMeasure := by
    dsimp [σ]
    exact complex_singularPart_mutuallySingular μ m
  letI : IsFiniteMeasure σ.variation := complex_variation_finite σ
  letI : IsFiniteMeasure ρ.variation := complex_variation_finite ρ
  have hmom_add (k : ℤ) :
      (∫ᵛ z, fourier k z ∂[ContinuousLinearMap.mul ℝ ℂ; μ]) =
        (∫ᵛ z, fourier k z ∂[ContinuousLinearMap.mul ℝ ℂ; σ]) +
        (∫ᵛ z, fourier k z ∂[ContinuousLinearMap.mul ℝ ℂ; ρ]) := by
    rw [← hd]
    exact MeasureTheory.VectorMeasure.integral_add_vectorMeasure
      (complex_integrable_fourier σ k) (complex_integrable_fourier ρ k)
  have hpos (n : ℕ) (hn : 1 ≤ n) :
      (∫ᵛ z, fourier (n : ℤ) z ∂[ContinuousLinearMap.mul ℝ ℂ; σ]) =
       -(∫ᵛ z, fourier (n : ℤ) z ∂[ContinuousLinearMap.mul ℝ ℂ; ρ]) := by
    have hh := hmom_add (n : ℤ)
    rw [hμ n hn] at hh
    -- the moment of the singular part is the negative of the density part
    exact eq_neg_of_add_eq_zero_left hh.symm
  -- The singular term really is concentrated on a Haar null Borel set; the
  -- side of the set in `VectorMeasure.MutuallySingular` is the zero side for σ.
  -- Separating this mundane support issue from the analytic assertion is useful:
  -- no positivity of σ is available.
  obtain ⟨Z, hZ, hσZ, hmZ⟩ := hsing
  have hmcompl : m Zᶜ = 0 := by
    have hx : m.toENNRealVectorMeasure Zᶜ = 0 := hmZ (Zᶜ) (by rfl)
    simpa [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable hZ.compl] using hx
  have hσinside {t : Set UnitAddCircle} (ht : t ⊆ Z) : σ t = 0 := hσZ t ht
  change σ = 0
  -- In the shift proof the remaining scalar spectral measure is exactly this
  -- square-density measure on `L²(|σ|)`. Isolating it avoids asking for
  -- impossible positivity statements about `σ` itself.
  have hfσ : Measurable (σ.rnDeriv σ.variation) := by
    apply measurable_of_re_im
    · exact SignedMeasure.measurable_rnDeriv _ _
    · exact SignedMeasure.measurable_rnDeriv _ _
  have hvarZ : σ.variation Z = 0 := by
    -- The singular vector measure vanishes on every subset of `Z`; this is
    -- just the defining zero criterion for variation (and uses
    -- measurability only for the outer set).
    exact (VectorMeasure.variation_apply_eq_zero (μ:=σ) hZ).2 (by
      intro t ht htmeas
      exact hσZ t ht)
  have hsq : Measurable (fun x : UnitAddCircle =>
        ENNReal.ofReal (‖σ.rnDeriv σ.variation x‖ ^ 2)) := by
    fun_prop
  have hL2 : σ.variation.withDensity
        (fun x : UnitAddCircle => ENNReal.ofReal (‖σ.rnDeriv σ.variation x‖ ^ 2)) ≪ m := by
    -- In measure form the endpoint is a scalar statement on each Haar-null
    -- Borel set.  All the algebra involved in replacing a wandering vector
    -- by its spectral measure was isolated above (`spectralMeasure_*`);
    -- nothing about a complex measure can turn this integral into a
    -- positive integral without that step.
    refine Measure.AbsolutelyContinuous.mk (μ :=
      σ.variation.withDensity
        (fun x : UnitAddCircle => ENNReal.ofReal
          (‖σ.rnDeriv σ.variation x‖ ^ 2))) (ν:=m) ?_
    intro s hs hs0
    rw [withDensity_apply _ hs]
    -- In particular all sets on the zero side for the vector measure have
    -- already gone away; only the Haar-null side `Zᶜ` can carry the
    -- wandering component.
    by_cases hsub : s ⊆ Z
    · exact setLIntegral_measure_zero s _
        (measure_mono_null hsub hvarZ)
    ·
      -- Work on the sum of the two variations.  The ac variation is included
      -- here (rather than Haar itself) so that its polar vector is an L² vector.
      let E : Set UnitAddCircle := Zᶜ
      have hE : MeasurableSet E := hZ.compl
      have hρac : ρ ≪ᵥ m.toENNRealVectorMeasure := by
        dsimp [ρ]
        exact withDensityᵥ_complex_absolutelyContinuous m _
      have hρE : ρ.variation E = 0 := by
        apply (VectorMeasure.variation_apply_eq_zero (μ:=ρ) hE).2
        intro t ht htmeas
        apply hρac
        rw [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable htmeas]
        exact measure_mono_null (ht) hmcompl
      let q : Measure UnitAddCircle := σ.variation + ρ.variation
      letI : IsFiniteMeasure q := by dsimp [q]; infer_instance
      -- The conjugate polar vector of the singular summand, as a vector for q.
      let fg : UnitAddCircle → ℂ :=
        E.indicator (fun x => starRingEnd ℂ (σ.rnDeriv σ.variation x))
      have hfgm : Measurable fg := by
        dsimp [fg]
        exact (Complex.continuous_conj.measurable.comp hfσ).indicator hE
      have hfgb : ∀ᵐ x ∂q, ‖fg x‖ ≤ (1:ℝ) := by
        have hσb : ∀ᵐ x ∂σ.variation, ‖fg x‖ ≤ (1:ℝ) := by
          filter_upwards [rnDeriv_variation_norm_le_one σ] with x hx
          by_cases hxe : x ∈ E
          · simpa [fg, Set.indicator_of_mem hxe] using hx
          · simp [fg, Set.indicator_of_notMem hxe]
        have hρnot : ∀ᵐ x ∂ρ.variation, x ∉ E := by
          rw [ae_iff]
          simpa using hρE
        have hρb : ∀ᵐ x ∂ρ.variation, ‖fg x‖ ≤ (1:ℝ) := by
          filter_upwards [hρnot] with x hx
          simp [fg, Set.indicator_of_notMem hx]
        exact (ae_add_measure_iff).2 ⟨hσb, hρb⟩
      let Gmem : MemLp fg 2 q :=
        MemLp.of_bound hfgm.aestronglyMeasurable 1 hfgb
      let G : Lp ℂ 2 q := Gmem.toLp fg
      have hGcoe : (G : UnitAddCircle → ℂ) =ᵐ[q] fg :=
        MemLp.coeFn_toLp _
      have hGsupp : ∀ᵐ x ∂q.restrict Eᶜ, (G : UnitAddCircle → ℂ) x = 0 := by
        have hh : ∀ᵐ x ∂q.restrict Eᶜ, (G : UnitAddCircle → ℂ) x = fg x :=
          Filter.Eventually.filter_mono (MeasureTheory.ae_mono (Measure.restrict_le_self)) hGcoe
        have hnot : ∀ᵐ x ∂q.restrict Eᶜ, x ∉ E := by
          refine (ae_restrict_iff' hE.compl).2 ?_
          filter_upwards [] with x hx
          exact hx
        filter_upwards [hh, hnot] with x hx hn
        simpa [fg, Set.indicator_of_notMem hn] using hx
      have hGpos : G ∈ posFourierSub q :=
        supported_mem_posFourier q E hE (by simpa [E, m] using hmcompl) G hGsupp

      have hfρ : Measurable (ρ.rnDeriv ρ.variation) := by
        apply measurable_of_re_im
        · exact SignedMeasure.measurable_rnDeriv _ _
        · exact SignedMeasure.measurable_rnDeriv _ _
      let fr : UnitAddCircle → ℂ :=
        Z.indicator (fun x => starRingEnd ℂ (ρ.rnDeriv ρ.variation x))
      have hfrm : Measurable fr := by
        exact (Complex.continuous_conj.measurable.comp hfρ).indicator hZ
      have hfrb : ∀ᵐ x ∂q, ‖fr x‖ ≤ (1:ℝ) := by
        have hn : ∀ᵐ x ∂σ.variation, x ∉ Z := by
          rw [ae_iff]; simpa using hvarZ
        have h1 : ∀ᵐ x ∂σ.variation, ‖fr x‖ ≤ (1:ℝ) := by
          filter_upwards [hn] with x hx
          simp [fr, Set.indicator_of_notMem hx]
        have h2 : ∀ᵐ x ∂ρ.variation, ‖fr x‖ ≤ (1:ℝ) := by
          filter_upwards [rnDeriv_variation_norm_le_one ρ] with x hx
          by_cases hxm : x ∈ Z
          · simpa [fr, Set.indicator_of_mem hxm] using hx
          · simp [fr, Set.indicator_of_notMem hxm]
        exact (ae_add_measure_iff).2 ⟨h1, h2⟩
      let Rmem : MemLp fr 2 q := MemLp.of_bound hfrm.aestronglyMeasurable 1 hfrb
      let R : Lp ℂ 2 q := Rmem.toLp fr
      have hRcoe : (R : UnitAddCircle → ℂ) =ᵐ[q] fr := MemLp.coeFn_toLp _
      let B : Lp ℂ 2 q := G + R
      -- This elementary change-of-measure calculation is the remaining scalar
      -- endpoint: the two indicator supports turn the q-integral into the two
      -- variation integrals.
      have htest (f : C(UnitAddCircle, ℂ)) :
          @inner ℂ _ _ B ((ContinuousMap.toLp 2 q ℂ) f) =
            (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; σ]) +
            (∫ᵛ z, f z ∂[ContinuousLinearMap.mul ℝ ℂ; ρ]) := by

        have hσint : Integrable (fun x : UnitAddCircle =>
              σ.rnDeriv σ.variation x * f x) σ.variation := by
          have hbase := (ComplexMeasure.integrable_rnDeriv σ σ.variation)
          have hbounded : ∀ᵐ x ∂σ.variation, ‖(f : UnitAddCircle → ℂ) x‖ ≤ ‖f‖ := by
            filter_upwards [] with x
            exact ContinuousMap.norm_coe_le_norm f x
          have hh := hbase.bdd_mul f.continuous.aestronglyMeasurable hbounded
          -- bdd_mul puts the bounded factor on the left
          simpa [mul_comm] using hh
        have hρint : Integrable (fun x : UnitAddCircle =>
              ρ.rnDeriv ρ.variation x * f x) ρ.variation := by
          have hbase := (ComplexMeasure.integrable_rnDeriv ρ ρ.variation)
          have hbounded : ∀ᵐ x ∂ρ.variation, ‖(f : UnitAddCircle → ℂ) x‖ ≤ ‖f‖ := by
            filter_upwards [] with x
            exact ContinuousMap.norm_coe_le_norm f x
          have hh := hbase.bdd_mul f.continuous.aestronglyMeasurable hbounded
          simpa [mul_comm] using hh
        have hfc : ((ContinuousMap.toLp 2 q ℂ) f : UnitAddCircle → ℂ) =ᵐ[q]
            (fun x => f x) := ContinuousMap.coeFn_toLp q f
        have hfcσ : ((ContinuousMap.toLp 2 q ℂ) f : UnitAddCircle → ℂ) =ᵐ[σ.variation]
            (fun x => f x) := Filter.Eventually.filter_mono
              (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_right (le_rfl))) hfc
        have hfcρ : ((ContinuousMap.toLp 2 q ℂ) f : UnitAddCircle → ℂ) =ᵐ[ρ.variation]
            (fun x => f x) := Filter.Eventually.filter_mono
              (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_left (le_rfl))) hfc
        have hBcoe : (B : UnitAddCircle → ℂ) =ᵐ[q]
            ((G : UnitAddCircle → ℂ) + (R : UnitAddCircle → ℂ)) := Lp.coeFn_add G R
        have hBσ := Filter.Eventually.filter_mono
              (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_right (le_rfl))) hBcoe
        have hBρ := Filter.Eventually.filter_mono
              (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_left (le_rfl))) hBcoe
        have hGσ := Filter.Eventually.filter_mono
              (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_right (le_rfl))) hGcoe
        have hGρ := Filter.Eventually.filter_mono
              (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_left (le_rfl))) hGcoe
        have hRσ := Filter.Eventually.filter_mono
              (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_right (le_rfl))) hRcoe
        have hRρ := Filter.Eventually.filter_mono
              (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_left (le_rfl))) hRcoe
        have hnotσ : ∀ᵐ x ∂σ.variation, x ∉ Z := by
          rw [ae_iff]; simpa using hvarZ
        have hmemρ : ∀ᵐ x ∂ρ.variation, x ∈ Z := by
          have : ∀ᵐ x ∂ρ.variation, x ∉ E := by rw [ae_iff]; simpa using hρE
          filter_upwards [this] with x hx
          simpa [E] using hx
        have haeσ : (fun x : UnitAddCircle => @inner ℂ _ _ (B x)
              (((ContinuousMap.toLp 2 q ℂ) f : UnitAddCircle → ℂ) x)) =ᵐ[σ.variation]
              (fun x => σ.rnDeriv σ.variation x * f x) := by
          filter_upwards [hBσ, hGσ, hRσ, hfcσ, hnotσ] with x hb hg hr hf' hn
          have he : x ∈ E := by simpa [E] using hn
          rw [hb]; simp only [Pi.add_apply]; rw [hg, hr, hf']
          simp [fg, fr, Set.indicator_of_mem he, Set.indicator_of_notMem hn,
            RCLike.inner_apply, mul_comm]
        have haeρ : (fun x : UnitAddCircle => @inner ℂ _ _ (B x)
              (((ContinuousMap.toLp 2 q ℂ) f : UnitAddCircle → ℂ) x)) =ᵐ[ρ.variation]
              (fun x => ρ.rnDeriv ρ.variation x * f x) := by
          filter_upwards [hBρ, hGρ, hRρ, hfcρ, hmemρ] with x hb hg hr hf' hm'
          have he : x ∉ E := by simpa [E] using hm'
          rw [hb]; simp only [Pi.add_apply]; rw [hg, hr, hf']
          simp [fg, fr, Set.indicator_of_notMem he, Set.indicator_of_mem hm',
            RCLike.inner_apply, mul_comm]
        rw [MeasureTheory.L2.inner_def]
        -- The only surviving issue is the standard change-of-density identity
        -- for the vector integral of a continuous scalar test function.
        rw [integral_add_measure ((Integrable.congr hσint haeσ.symm)) ((Integrable.congr hρint haeρ.symm))]
        rw [integral_congr_ae haeσ, integral_congr_ae haeρ]
        rw [integral_mul_rnDeriv_eq_vector σ f,
          integral_mul_rnDeriv_eq_vector ρ f]
      have hBgen (n : ℕ) :
          @inner ℂ _ _ B
            (lpMulLeft q (circleCharLpTop q 1) (fourierLpAny q (n:ℤ))) = 0 := by
        rw [fourierLpAny_mul]
        have hcast : (1:ℤ) + (n:ℤ) = ((n+1:ℕ):ℤ) := by
          norm_cast; simp [add_comm]
        rw [hcast]
        have hf := htest (fourier ((n+1:ℕ):ℤ))
        have heq : (fourierLpAny q ((n+1:ℕ):ℤ)) =
             (ContinuousMap.toLp 2 q ℂ) (fourier ((n+1:ℕ):ℤ)) := rfl
        rw [heq, hf]
        have hh := hmom_add ((n+1:ℕ):ℤ)
        rw [hμ (n+1) (by omega)] at hh
        exact hh.symm
      -- The continuous functional x | ⟨B,Ux⟩ therefore vanishes on M.
      let T : Lp ℂ 2 q →L[ℂ] ℂ :=
        ((innerSL ℂ) B).comp (lpMulLeft q (circleCharLpTop q 1))
      have hMker : nonnegFourierSub q ≤ LinearMap.ker T.toLinearMap := by
        change (Submodule.span ℂ (Set.range (fun n : ℕ => fourierLpAny q (n:ℤ)))).topologicalClosure ≤ _
        apply Submodule.topologicalClosure_minimal _ ?_ T.isClosed_ker
        refine (Submodule.span_le).2 ?_
        rintro x ⟨n, rfl⟩
        exact hBgen n
      have hBorth : B ∈ (posFourierSub q)ᗮ := by
        refine (Submodule.mem_orthogonal' _ _).2 ?_
        intro x hx
        obtain ⟨y, hy, rfl⟩ := hx
        change @inner ℂ _ _ B
          (lpMulLeft q (circleCharLpTop q 1) y) = 0
        exact hMker hy
      have hRzeroE : ∀ᵐ x ∂q.restrict E, (R : UnitAddCircle → ℂ) x = 0 := by
        have hh : ∀ᵐ x ∂q.restrict E, (R : UnitAddCircle → ℂ) x = fr x :=
          Filter.Eventually.filter_mono (MeasureTheory.ae_mono (Measure.restrict_le_self)) hRcoe
        have hnot : ∀ᵐ x ∂q.restrict E, x ∉ Z := by
          refine (ae_restrict_iff' hE).2 ?_
          filter_upwards [] with x hx
          exact hx
        filter_upwards [hh, hnot] with x hx hn
        simpa [fr, Set.indicator_of_notMem hn] using hx

      have hGR : @inner ℂ _ _ G R = 0 :=
        inner_zero_of_opposite_support q E hE G R hGsupp hRzeroE
      have hRG : @inner ℂ _ _ R G = 0 := by
        rw [← inner_conj_symm]
        simp [hGR]
      have hBG : @inner ℂ _ _ B G = 0 :=
        Submodule.inner_left_of_mem_orthogonal hGpos hBorth
      have hGG : @inner ℂ _ _ G G = 0 := by
        change @inner ℂ _ _ (G + R) G = 0 at hBG
        rw [inner_add_left, hRG, add_zero] at hBG
        exact hBG
      have hG0 : G = 0 := inner_self_eq_zero.mp hGG
      -- Hence the singular polar vector vanishes on its whole support.
      have hfgzero : fg =ᵐ[σ.variation] (0 : UnitAddCircle → ℂ) := by
        have hfgq : fg =ᵐ[q] (0 : UnitAddCircle → ℂ) := by
          have hzfun : (G : UnitAddCircle → ℂ) =ᵐ[q]
              (0 : Lp ℂ 2 q) := by rw [hG0]
          exact hGcoe.symm.trans (hzfun.trans (Lp.coeFn_zero ℂ 2 q))
        exact Filter.Eventually.filter_mono
          (MeasureTheory.ae_mono (by dsimp [q]; exact Measure.le_add_right (le_rfl))) hfgq
      have hnotZ : ∀ᵐ x ∂σ.variation, x ∉ Z := by
        rw [ae_iff]; simpa using hvarZ
      have hpolarzero : (σ.rnDeriv σ.variation) =ᵐ[σ.variation]
            (0 : UnitAddCircle → ℂ) := by
        filter_upwards [hfgzero, hnotZ] with x hx hn
        have hem : x ∈ E := by simpa [E] using hn
        have : starRingEnd ℂ (σ.rnDeriv σ.variation x) = 0 := by
          simpa [fg, Set.indicator_of_mem hem] using hx
        simpa using congrArg (starRingEnd ℂ) this
      have hsigzero : σ = 0 := by
        rw [← complex_withDensityv_variation σ]
        apply MeasureTheory.VectorMeasure.ext
        intro t ht
        rw [withDensityᵥ_apply (ComplexMeasure.integrable_rnDeriv _ _) ht]
        have he : (σ.rnDeriv σ.variation) =ᵐ[σ.variation.restrict t]
              (0 : UnitAddCircle → ℂ) :=
          Filter.Eventually.filter_mono (MeasureTheory.ae_mono (Measure.restrict_le_self)) hpolarzero
        rw [integral_congr_ae he]
        simp
      -- with σ=0 the branch, and indeed the whole scalar measure, is trivial.
      have hvar0 : σ.variation = 0 := by rw [hsigzero]; simp
      have : (∫⁻ a in s, ENNReal.ofReal (‖σ.rnDeriv σ.variation a‖ ^ 2)
              ∂σ.variation) = 0 := by simp [hvar0]
      exact this
  have hacσ : σ ≪ᵥ m.toENNRealVectorMeasure := by
    rw [← complex_withDensityv_variation σ]
    exact withDensityv_ac_of_sq (ComplexMeasure.integrable_rnDeriv _ _) hsq hL2
  -- From this scalar conclusion the support bookkeeping is elementary.
  apply MeasureTheory.VectorMeasure.ext
  intro t ht
  change σ t = (0 : ComplexMeasure UnitAddCircle) t
  have hz₁ : σ (t ∩ Z) = 0 := hσinside Set.inter_subset_right
  have hzₘ : m (t ∩ Zᶜ) = 0 :=
    measure_mono_null Set.inter_subset_right hmcompl
  have hz₂ : σ (t ∩ Zᶜ) = 0 := by
    apply hacσ
    simpa [MeasureTheory.Measure.toENNRealVectorMeasure_apply_measurable
      (ht.inter hZ.compl)] using hzₘ
  have hdis : Disjoint (t ∩ Z) (t ∩ Zᶜ) := by
    apply Set.disjoint_left.2
    intro x hx hy
    exact hy.2 hx.2
  have hu : (t ∩ Z) ∪ (t ∩ Zᶜ) = t := by
    aesop
  rw [← hu, VectorMeasure.of_union hdis (ht.inter hZ) (ht.inter hZ.compl), hz₁, hz₂]
  simp

/-ResultProofEnd-/
/-ResultEnd-/

end
end Submission
