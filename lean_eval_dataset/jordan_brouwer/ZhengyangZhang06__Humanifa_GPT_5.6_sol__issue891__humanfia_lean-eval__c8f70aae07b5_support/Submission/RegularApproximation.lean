import Submission.Cone

namespace Submission.Helpers

open Function Set
open MeasureTheory
open scoped ContDiff

noncomputable section

/-- A smooth compactly supported approximation of the extended inverse of a
sphere embedding, shifted by a small regular value. -/
structure RegularApproximation (d : ℕ)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d)) where
  g : EuclideanSpace ℝ (Fin d) → EuclideanSpace ℝ (Fin d)
  a : EuclideanSpace ℝ (Fin d)
  smooth' : ContDiff ℝ ∞ g
  a_ne_zero : a ≠ 0
  close_on_sphere : ∀ z, ‖(g (r z) - a) - z‖ < 1
  roots_finite : {x | g x = a}.Finite
  regular : ∀ x, g x = a → (fderiv ℝ g x).det ≠ 0

/-- Every root of a regular approximation lies off the embedded sphere. -/
theorem RegularApproximation.root_not_mem_range {d : ℕ}
    {r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d)} (A : RegularApproximation d r)
    {x : EuclideanSpace ℝ (Fin d)} (hx : A.g x = A.a) :
    x ∉ Set.range r := by
  rintro ⟨z, rfl⟩
  have hclose := A.close_on_sphere z
  rw [hx, sub_self, zero_sub, norm_neg,
    mem_sphere_zero_iff_norm.mp z.2] at hclose
  exact (lt_irrefl 1) hclose

/-- The boundary condition of a regular approximation forces it to have a
root.  Otherwise normalization would give a global sphere-valued map whose
restriction to the embedded sphere is both nullhomotopic and, by the
strict one-unit estimate, homotopic to the identity. -/
theorem RegularApproximation.roots_nonempty {d : ℕ}
    {r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d)} (hcont : Continuous r)
    (A : RegularApproximation d r) :
    {x | A.g x = A.a}.Nonempty := by
  classical
  by_contra hroots
  rw [Set.not_nonempty_iff_eq_empty] at hroots
  have hne (x : EuclideanSpace ℝ (Fin d)) : A.g x - A.a ≠ 0 := by
    rw [sub_ne_zero]
    intro hx
    have : x ∈ ({y | A.g y = A.a} :
        Set (EuclideanSpace ℝ (Fin d))) := hx
    rw [hroots] at this
    exact this
  let uGlobal : C(EuclideanSpace ℝ (Fin d),
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    { toFun := fun x ↦ ⟨NormedSpace.normalize (A.g x - A.a), by
        rw [mem_sphere_zero_iff_norm]
        exact NormedSpace.norm_normalize (hne x)⟩
      continuous_toFun := by
        have hv : Continuous (fun x ↦ A.g x - A.a) :=
          A.smooth'.continuous.sub continuous_const
        apply Continuous.subtype_mk
        change Continuous (fun x ↦ ‖A.g x - A.a‖⁻¹ • (A.g x - A.a))
        exact (hv.norm.inv₀ fun x ↦
          norm_ne_zero_iff.mpr (hne x)).smul hv }
  let rMap : C(Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1,
      EuclideanSpace ℝ (Fin d)) := ⟨r, hcont⟩
  let u : C(Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1,
      Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1) :=
    uGlobal.comp rMap
  let closeVector : unitInterval × Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d) := fun q ↦
    (q.2 : EuclideanSpace ℝ (Fin d)) + (q.1 : ℝ) •
      ((A.g (r q.2) - A.a) - q.2)
  have hcloseVector (q : unitInterval × Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1) : closeVector q ≠ 0 := by
    intro hzero
    have hzero' : (q.2 : EuclideanSpace ℝ (Fin d)) +
        (q.1 : ℝ) • ((A.g (r q.2) - A.a) - q.2) = 0 := by
      simpa only [closeVector] using hzero
    have heq : (q.2 : EuclideanSpace ℝ (Fin d)) =
        -(q.1 : ℝ) • ((A.g (r q.2) - A.a) - q.2) := by
      calc
        (q.2 : EuclideanSpace ℝ (Fin d)) =
            ((q.2 : EuclideanSpace ℝ (Fin d)) +
              (q.1 : ℝ) • ((A.g (r q.2) - A.a) - q.2)) -
                (q.1 : ℝ) • ((A.g (r q.2) - A.a) - q.2) := by abel
        _ = -(q.1 : ℝ) • ((A.g (r q.2) - A.a) - q.2) := by
          rw [hzero', zero_sub, neg_smul]
    have ht0 : 0 ≤ (q.1 : ℝ) := q.1.2.1
    have ht1 : (q.1 : ℝ) ≤ 1 := q.1.2.2
    have hnorm : (1 : ℝ) ≤ ‖(A.g (r q.2) - A.a) - q.2‖ := by
      calc
        (1 : ℝ) = ‖(q.2 : EuclideanSpace ℝ (Fin d))‖ :=
          (mem_sphere_zero_iff_norm.mp q.2.2).symm
        _ = ‖-(q.1 : ℝ) • ((A.g (r q.2) - A.a) - q.2)‖ :=
          congrArg norm heq
        _ = (q.1 : ℝ) * ‖(A.g (r q.2) - A.a) - q.2‖ := by
          rw [norm_smul, Real.norm_eq_abs,
            abs_of_nonpos (neg_nonpos.mpr ht0), neg_neg]
        _ ≤ 1 * ‖(A.g (r q.2) - A.a) - q.2‖ :=
          mul_le_mul_of_nonneg_right ht1 (norm_nonneg _)
        _ = ‖(A.g (r q.2) - A.a) - q.2‖ := one_mul _
    exact (not_le_of_gt (A.close_on_sphere q.2)) hnorm
  have hcloseContinuous : Continuous closeVector := by
    dsimp [closeVector]
    exact (continuous_subtype_val.comp continuous_snd).add
      ((continuous_subtype_val.comp continuous_fst).smul
        (((A.smooth'.continuous.comp (hcont.comp continuous_snd)).sub
          continuous_const).sub
            (continuous_subtype_val.comp continuous_snd)))
  have hid_u : ContinuousMap.Homotopic (ContinuousMap.id _) u := by
    refine ⟨{
      toFun := fun q ↦
        ⟨NormedSpace.normalize (closeVector q), by
          rw [mem_sphere_zero_iff_norm]
          exact NormedSpace.norm_normalize (hcloseVector q)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        change Continuous (fun q ↦ ‖closeVector q‖⁻¹ • closeVector q)
        exact (hcloseContinuous.norm.inv₀ fun q ↦
          norm_ne_zero_iff.mpr (hcloseVector q)).smul hcloseContinuous
      map_zero_left := by
        intro z
        apply Subtype.ext
        change NormedSpace.normalize
            ((z : EuclideanSpace ℝ (Fin d)) +
              (0 : ℝ) • ((A.g (r z) - A.a) - z)) = z
        simp only [zero_smul, add_zero]
        exact NormedSpace.normalize_eq_self_of_norm_eq_one
          (mem_sphere_zero_iff_norm.mp z.2)
      map_one_left := by
        intro z
        apply Subtype.ext
        change NormedSpace.normalize
            ((z : EuclideanSpace ℝ (Fin d)) +
              (1 : ℝ) • ((A.g (r z) - A.a) - z)) =
          NormedSpace.normalize (A.g (r z) - A.a)
        congr 1
        module }⟩
  let contractionVector : unitInterval × Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d) := fun q ↦
    A.g ((1 - (q.1 : ℝ)) • r q.2) - A.a
  have hcontractionVector (q : unitInterval × Metric.sphere
      (0 : EuclideanSpace ℝ (Fin d)) 1) : contractionVector q ≠ 0 :=
    hne _
  have hcontractionContinuous : Continuous contractionVector := by
    dsimp [contractionVector]
    exact A.smooth'.continuous.comp
      ((continuous_const.sub
        (continuous_subtype_val.comp continuous_fst)).smul
          (hcont.comp continuous_snd)) |>.sub continuous_const
  let c : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 :=
    ⟨NormedSpace.normalize (A.g 0 - A.a), by
      rw [mem_sphere_zero_iff_norm]
      exact NormedSpace.norm_normalize (hne 0)⟩
  have hu_const : ContinuousMap.Homotopic u
      (ContinuousMap.const _ c) := by
    refine ⟨{
      toFun := fun q ↦
        ⟨NormedSpace.normalize (contractionVector q), by
          rw [mem_sphere_zero_iff_norm]
          exact NormedSpace.norm_normalize (hcontractionVector q)⟩
      continuous_toFun := by
        apply Continuous.subtype_mk
        change Continuous (fun q ↦
          ‖contractionVector q‖⁻¹ • contractionVector q)
        exact (hcontractionContinuous.norm.inv₀ fun q ↦
          norm_ne_zero_iff.mpr (hcontractionVector q)).smul
            hcontractionContinuous
      map_zero_left := by
        intro z
        apply Subtype.ext
        change NormedSpace.normalize
            (A.g ((1 - (0 : ℝ)) • r z) - A.a) =
          NormedSpace.normalize (A.g (r z) - A.a)
        simp
      map_one_left := by
        intro z
        apply Subtype.ext
        change NormedSpace.normalize
            (A.g ((1 - (1 : ℝ)) • r z) - A.a) =
          NormedSpace.normalize (A.g 0 - A.a)
        simp
      }⟩
  have hnull : SphereMapNullhomotopic d (ContinuousMap.id _) :=
    ⟨c, hid_u.trans hu_const⟩
  obtain ⟨G, hG⟩ :=
    exists_closedBall_extension_of_sphereMapNullhomotopic d
      (ContinuousMap.id _) hnull
  exact noUnitSphereRetraction_all d ⟨G, fun z ↦ by simpa using hG z⟩

/-- Smooth approximation, Sard's theorem, and the inverse function theorem
produce a regular approximation with a finite root set in every positive
dimension relevant to Jordan--Brouwer. -/
theorem exists_regularApproximation (d : ℕ) (hd : 2 ≤ d)
    (r : Metric.sphere (0 : EuclideanSpace ℝ (Fin d)) 1 →
      EuclideanSpace ℝ (Fin d))
    (hcont : Continuous r) (hinj : Function.Injective r) :
    Nonempty (RegularApproximation d r) := by
  classical
  letI : Nonempty (Fin d) :=
    ⟨⟨0, lt_of_lt_of_le (by norm_num) hd⟩⟩
  let E := EuclideanSpace ℝ (Fin d)
  obtain ⟨F, hF, _hFle, _hFlt⟩ :=
    exists_strict_unitBall_extension d hd r hcont hinj
  obtain ⟨R, hR⟩ := (isCompact_range hcont).isBounded.subset_ball (0 : E)
  let cutoff : E → ℝ := fun x ↦ max 0 (min 1 (R + 1 - ‖x‖))
  have hcutoff_cont : Continuous cutoff := by
    exact continuous_const.max
      (continuous_const.min (continuous_const.sub continuous_norm))
  have hcutoff_range (z : Metric.sphere (0 : E) 1) :
      cutoff (r z) = 1 := by
    have hz := hR (⟨z, rfl⟩ : r z ∈ Set.range r)
    rw [Metric.mem_ball, dist_zero_right] at hz
    have : 1 < R + 1 - ‖r z‖ := by linarith
    simp [cutoff, min_eq_left this.le]
  have hcutoff_far {x : E} (hx : R + 1 ≤ ‖x‖) : cutoff x = 0 := by
    have : R + 1 - ‖x‖ ≤ 0 := sub_nonpos.mpr hx
    dsimp [cutoff]
    rw [show min 1 (R + 1 - ‖x‖) = R + 1 - ‖x‖ by
      exact min_eq_right (this.trans zero_le_one)]
    exact max_eq_left this
  let f : E → E := fun x ↦ cutoff x • F x
  have hfcont : Continuous f := hcutoff_cont.smul F.continuous
  have hfrange (z : Metric.sphere (0 : E) 1) : f (r z) = z := by
    change cutoff (r z) • F (r z) = z
    rw [hcutoff_range, hF z]
    simp
  have hfsupport : Function.support f ⊆ Metric.closedBall (0 : E) (R + 1) := by
    intro x hx
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra hnorm
    have hnorm' : R + 1 ≤ ‖x‖ := le_of_not_ge hnorm
    exact hx (by simp [f, hcutoff_far hnorm'])
  obtain ⟨g, hg, hgclose, hgsupport⟩ :=
    hfcont.exists_contDiff_approx ⊤
      (continuous_const : Continuous fun _ : E ↦ (1 / 16 : ℝ))
      (fun _ ↦ by norm_num)
  let critical : Set E := {x | (fderiv ℝ g x).det = 0}
  have hgdiff : Differentiable ℝ g := hg.differentiable (by simp)
  have hcritical : volume (g '' critical) = 0 := by
    apply MeasureTheory.addHaar_image_eq_zero_of_det_fderivWithin_eq_zero
      (s := critical) (f' := fun x ↦ fderiv ℝ g x)
    · intro x _hx
      exact (hgdiff x).hasFDerivAt.hasFDerivWithinAt
    · intro x hx
      exact hx
  let bad : Set E := g '' critical ∪ {0}
  have hbad : volume bad = 0 := by
    exact measure_union_null hcritical (by simp)
  have hdense : Dense badᶜ := by
    rw [dense_iff_closure_eq, closure_compl,
      MeasureTheory.Measure.interior_eq_empty_of_null hbad]
    simp
  obtain ⟨a, habad, haball⟩ := hdense.exists_mem_open
    (Metric.isOpen_ball : IsOpen (Metric.ball (0 : E) (1 / 16)))
    (Metric.nonempty_ball.mpr (by norm_num))
  have ha0 : a ≠ 0 := by
    intro ha
    apply habad
    exact Or.inr (by simp [ha])
  have hanorm : ‖a‖ < 1 / 16 := by
    simpa [Metric.mem_ball, dist_zero_right] using haball
  have haregular (x : E) (hx : g x = a) :
      (fderiv ℝ g x).det ≠ 0 := by
    intro hdet
    apply habad
    exact Or.inl ⟨x, hdet, hx⟩
  let roots : Set E := {x | g x = a}
  have hroots_closed : IsClosed roots :=
    isClosed_singleton.preimage hg.continuous
  have hroots_subset : roots ⊆ Metric.closedBall (0 : E) (R + 1) := by
    intro x hx
    apply hfsupport (hgsupport ?_)
    change g x ≠ 0
    rw [hx]
    exact ha0
  have hroots_compact : IsCompact roots :=
    (isCompact_closedBall (0 : E) (R + 1)).of_isClosed_subset
      hroots_closed hroots_subset
  have hroots_discrete : IsDiscrete roots := by
    rw [isDiscrete_iff_forall_exists_isOpen]
    intro x hx
    let A : E ≃L[ℝ] E :=
      (fderiv ℝ g x).toContinuousLinearEquivOfDetNeZero
        (haregular x hx)
    have hfd : HasFDerivAt g (fderiv ℝ g x) x :=
      (hgdiff x).hasFDerivAt
    have hstrict : HasStrictFDerivAt g (A : E →L[ℝ] E) x := by
      simpa only [A,
        ContinuousLinearMap.coe_toContinuousLinearEquivOfDetNeZero] using
        hg.contDiffAt.hasStrictFDerivAt' hfd (by simp)
    let e : OpenPartialHomeomorph E E :=
      hstrict.toOpenPartialHomeomorph g
    refine ⟨e.source, e.open_source, ?_⟩
    ext y
    constructor
    · rintro ⟨hySource, hyRoot⟩
      have hyx : y = x := by
        apply e.injOn hySource
          hstrict.mem_toOpenPartialHomeomorph_source
        exact hyRoot.trans hx.symm
      simp [hyx]
    · intro hy
      have hyx : y = x := by simpa using hy
      subst y
      exact ⟨hstrict.mem_toOpenPartialHomeomorph_source, hx⟩
  have hroots_finite : roots.Finite :=
    hroots_compact.finite hroots_discrete
  refine ⟨{
    g := g
    a := a
    smooth' := hg
    a_ne_zero := ha0
    close_on_sphere := fun z ↦ ?_
    roots_finite := hroots_finite
    regular := haregular }⟩
  calc
    ‖(g (r z) - a) - z‖ ≤ ‖g (r z) - z‖ + ‖a‖ := by
      calc
        ‖(g (r z) - a) - z‖ = ‖(g (r z) - z) - a‖ := by
          congr 1
          abel
        _ ≤ ‖g (r z) - z‖ + ‖a‖ := norm_sub_le _ _
    _ < 1 / 16 + 1 / 16 := by
      gcongr
      simpa [dist_eq_norm, hfrange] using hgclose (r z)
    _ < 1 := by norm_num

end

end Submission.Helpers
