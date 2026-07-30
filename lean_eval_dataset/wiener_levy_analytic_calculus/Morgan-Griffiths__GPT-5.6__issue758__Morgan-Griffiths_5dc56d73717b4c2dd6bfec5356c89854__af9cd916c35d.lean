import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Basic.lean

/-! Elementary Fourier synthesis for absolutely summable coefficients.
These facts are convenient since mathlib's `lp` supplies the Banach space but
`Analysis/Fourier/AddCircle` only states the inverse theorem for coefficients
of an already continuous function. -/
noncomputable section
open Set MeasureTheory
open scoped ENNReal lp ComplexConjugate Real BigOperators

namespace WL

/-- The Banach space of absolutely summable Laurent coefficients.  We don't put
any multiplicative structure on it here. -/
abbrev L1 := ℓ¹(ℤ, ℂ)

lemma memL1_of_summable {a : ℤ → ℂ} (ha : Summable a) : Memℓp a (1 : ℝ≥0∞) := by
  apply memℓp_gen
  simpa using ha.norm

/-- Regard an absolutely summable family as an `ℓ¹` vector. -/
def ofSummable (a : ℤ → ℂ) (ha : Summable a) : L1 :=
  ⟨a, memL1_of_summable ha⟩

@[simp] lemma ofSummable_apply (a : ℤ → ℂ) (ha : Summable a) (n : ℤ) :
    ofSummable a ha n = a n := rfl

lemma summable_norm (a : L1) : Summable (fun n : ℤ => ‖a n‖) := by
  simpa using (memℓp_gen_iff (p := (1:ℝ≥0∞)) (by norm_num : 0 < (1:ℝ≥0∞).toReal)).1 a.2

lemma summable (a : L1) : Summable (fun n : ℤ => a n) :=
  .of_norm (summable_norm a)

lemma norm_eq (a : L1) : ‖a‖ = ∑' n : ℤ, ‖a n‖ := by
  simpa using (lp.norm_eq_tsum_rpow (p := (1:ℝ≥0∞))
    (by norm_num : 0 < (1:ℝ≥0∞).toReal) a)

variable {T : ℝ} [Fact (0 < T)]

/-- The summable family of monomials associated to a sequence. -/
lemma summable_monomials (a : L1) :
    Summable (fun n : ℤ => a n • (fourier (T:=T) n)) := by
  apply Summable.of_norm
  -- the norm in continuous functions is the sup norm; monomials have norm one.
  simpa [norm_smul, fourier_norm] using (summable_norm a)

/-- Fourier synthesis on `ℓ¹`: the normally convergent Laurent series. -/
def synth (a : L1) : C(AddCircle T, ℂ) :=
  ∑' n : ℤ, a n • (fourier (T:=T) n)

lemma hasSum_synth (a : L1) :
    HasSum (fun n : ℤ => a n • (fourier (T:=T) n)) (synth (T:=T) a) :=
  (summable_monomials (T:=T) a).hasSum

/-- Integrability of a continuous function on the compact circle. -/
lemma integrable_continuous (f : C(AddCircle T, ℂ)) :
    Integrable (f : AddCircle T → ℂ) AddCircle.haarAddCircle :=
  f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The nth Fourier coefficient is a bounded linear functional for the uniform norm.
The norm is at most one, since Haar measure here is normalized to mass one. -/
def coeffCLM (n : ℤ) : C(AddCircle T, ℂ) →L[ℂ] ℂ := by
  let F : C(AddCircle T, ℂ) →ₗ[ℂ] ℂ :=
    { toFun := fun f => fourierCoeff (T:=T) f n
      map_add' := by
        intro f g
        have h := fourierCoeff.add (T:=T) (integrable_continuous f)
          (integrable_continuous g)
        simpa using congrFun h n
      map_smul' := by
        intro c f
        simpa using (fourierCoeff.const_smul (T:=T) (f : AddCircle T → ℂ) c n) }
  refine LinearMap.mkContinuous F 1 ?_
  intro f
  -- estimate by the integral of the constant bound
  change ‖fourierCoeff (T:=T) (f : AddCircle T → ℂ) n‖ ≤ (1:ℝ) * ‖f‖
  unfold fourierCoeff
  have hb : ∀ x : AddCircle T,
      ‖(fourier (-n : ℤ) x) • (f x)‖ ≤ ‖f‖ := by
    intro x
    rw [norm_smul]
    have hone : ‖fourier (T:=T) (-n : ℤ) x‖ = (1:ℝ) := Circle.norm_coe _
    rw [hone, one_mul]
    exact ContinuousMap.norm_coe_le_norm f x
  have h := norm_integral_le_of_norm_le_const
    (μ := AddCircle.haarAddCircle)
    (Filter.Eventually.of_forall hb)
  simpa [measureReal_univ_eq_one] using h

@[simp] lemma coeffCLM_apply (n : ℤ) (f : C(AddCircle T, ℂ)) :
    coeffCLM (T:=T) n f = fourierCoeff (T:=T) f n := rfl

/-- Coefficients of a normally convergent Laurent series are the specified coefficients. -/
theorem coeff_synth (a : L1) :
    fourierCoeff (T:=T) (synth (T:=T) a) = (fun n => a n) := by
  funext k
  have hs := (coeffCLM (T:=T) k).hasSum (hasSum_synth (T:=T) a)
  -- each monomial has the expected coefficient
  have hs' : HasSum (fun n : ℤ => (if k = n then a n else 0 : ℂ))
        (fourierCoeff (T:=T) (synth (T:=T) a) k) := by
    convert hs using 1
    · ext n
      -- compute the coefficient of a scalar multiple
      change _ = fourierCoeff (T:=T)
        (fun x : AddCircle T => a n * (fourier (T:=T) n) x) k
      rw [fourierCoeff.const_mul (T:=T)
        ((fourier (T:=T) n : C(AddCircle T, ℂ)) : AddCircle T → ℂ) (a n) k,
        fourierCoeff_fourier (T:=T) n]
      classical
      by_cases h : k = n
      · subst n; simp
      · simp [Pi.single_apply, h]
    · rfl

  classical
  simpa using hs'.tsum_eq.symm

/-- Fourier synthesis and mathlib's inverse Fourier theorem agree for every Wiener
function. This formulation is often the most useful one, and in particular gives
uniqueness. -/
theorem synth_coeff (f : C(AddCircle T, ℂ)) (h : Summable (fourierCoeff f)) :
    synth (T:=T) (ofSummable (fourierCoeff f) h) = f := by
  -- this is exactly the uniform Fourier inversion theorem.
  exact (hasSum_fourier_series_of_summable h).unique
    (hasSum_synth (T:=T) (ofSummable (fourierCoeff f) h)) |>.symm

end WL

namespace WL
open Set MeasureTheory
open scoped ENNReal lp ComplexConjugate Real BigOperators
variable {T : ℝ} [Fact (0 < T)]

lemma synth_injective : Function.Injective (synth (T:=T)) := by
  intro a b h
  have hh := congrArg (fun u : C(AddCircle T, ℂ) => fourierCoeff (T:=T) (u : AddCircle T → ℂ)) h
  apply lp.ext
  funext n
  have hn := congrFun hh n
  simpa [coeff_synth (T:=T)] using hn

/-- Intrinsic characterization of the normally convergent series image. -/
lemma mem_range_synth (f : C(AddCircle T, ℂ)) :
    Summable (fourierCoeff f) ↔ ∃ a : L1, synth (T:=T) a = f := by
  constructor
  · intro h
    exact ⟨ofSummable (fourierCoeff f) h, synth_coeff f h⟩
  · rintro ⟨a, rfl⟩
    -- coefficients are the absolutely summable original family
    rw [coeff_synth]
    exact summable a

/-- The representing summable vector of a Wiener function is unique. -/
lemma synth_unique {f : C(AddCircle T, ℂ)} {a : L1}
    (h : synth (T:=T) a = f) :
    a = ofSummable (fourierCoeff f)
      ((mem_range_synth (T:=T) f).2 ⟨a, h⟩) := by
  apply synth_injective (T:=T)
  rw [synth_coeff]
  exact h

end WL

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Basic.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Planar.lean

/-! Small scalar planar lemmas used in the contour part.  We spell the
boundary integral with four real intervals; this is the same convention as
`Complex.integral_boundary_rect_eq_zero...`.  The elementary grid argument is
much less painful with this additive notation. -/
noncomputable section
open Set MeasureTheory intervalIntegral
open scoped Real Interval BigOperators Topology
namespace WL.Planar

/-- Positively oriented boundary of the box `[l,r] × [b,t]`, in real
coordinates.  Degenerate and reversed intervals use the usual oriented
interval convention. -/
def box (l r b t : ℝ) (q : ℂ → ℂ) : ℂ :=
    (∫ x : ℝ in l..r, q (x + b * Complex.I)) -
      (∫ x : ℝ in l..r, q (x + t * Complex.I)) +
      Complex.I * (∫ y : ℝ in b..t, q (r + y * Complex.I)) -
      Complex.I * (∫ y : ℝ in b..t, q (l + y * Complex.I))

/-- mathlib's rectangle Goursat in the `box` notation. -/
lemma box_eq_zero_of_differentiableOn (l r b t : ℝ) (q : ℂ → ℂ)
    (h : DifferentiableOn ℂ q ([[l,r]] ×ℂ [[b,t]])) :
    box l r b t q = 0 := by
  let z : ℂ := (l:ℂ) + (b:ℂ) * Complex.I
  let w : ℂ := (r:ℂ) + (t:ℂ) * Complex.I
  have hzr : z.re = l := by simp [z]
  have hzi : z.im = b := by simp [z]
  have hwr : w.re = r := by simp [w]
  have hwi : w.im = t := by simp [w]
  have := Complex.integral_boundary_rect_eq_zero_of_differentiableOn
    q z w (by simpa [hzr, hzi, hwr, hwi] using h)
  -- `I • u` is multiplication in `ℂ`.
  simpa [box, hzr, hzi, hwr, hwi, mul_comm] using this

/-- Additivity when a box is cut by a horizontal line. `q` only has to be
continuous on the six line segments involved; we state the slightly stronger
but more convenient global hypothesis. -/
lemma box_split_horizontal (l r b u t : ℝ) (q : ℂ → ℂ) (hq : Continuous q) :
    box l r b u q + box l r u t q = box l r b t q := by
  have hyR : ∀ A B C : ℝ,
      (∫ y : ℝ in A..B, q (r + y * Complex.I)) +
      (∫ y : ℝ in B..C, q (r + y * Complex.I)) =
      ∫ y : ℝ in A..C, q (r + y * Complex.I) := by
    intro A B C
    exact intervalIntegral.integral_add_adjacent_intervals
      ((hq.comp (by fun_prop)).intervalIntegrable A B)
      ((hq.comp (by fun_prop)).intervalIntegrable B C)
  have hyL : ∀ A B C : ℝ,
      (∫ y : ℝ in A..B, q (l + y * Complex.I)) +
      (∫ y : ℝ in B..C, q (l + y * Complex.I)) =
      ∫ y : ℝ in A..C, q (l + y * Complex.I) := by
    intro A B C
    exact intervalIntegral.integral_add_adjacent_intervals
      ((hq.comp (by fun_prop)).intervalIntegrable A B)
      ((hq.comp (by fun_prop)).intervalIntegrable B C)
  simp only [box]
  rw [← hyR b u t, ← hyL b u t]
  ring

lemma box_split_vertical (l u r b t : ℝ) (q : ℂ → ℂ) (hq : Continuous q) :
    box l u b t q + box u r b t q = box l r b t q := by
  have hxB : ∀ A B C : ℝ,
      (∫ x : ℝ in A..B, q (x + b * Complex.I)) +
      (∫ x : ℝ in B..C, q (x + b * Complex.I)) =
      ∫ x : ℝ in A..C, q (x + b * Complex.I) := by
    intro A B C
    exact intervalIntegral.integral_add_adjacent_intervals
      ((hq.comp (by fun_prop)).intervalIntegrable A B)
      ((hq.comp (by fun_prop)).intervalIntegrable B C)
  have hxT : ∀ A B C : ℝ,
      (∫ x : ℝ in A..B, q (x + t * Complex.I)) +
      (∫ x : ℝ in B..C, q (x + t * Complex.I)) =
      ∫ x : ℝ in A..C, q (x + t * Complex.I) := by
    intro A B C
    exact intervalIntegral.integral_add_adjacent_intervals
      ((hq.comp (by fun_prop)).intervalIntegrable A B)
      ((hq.comp (by fun_prop)).intervalIntegrable B C)
  simp only [box]
  rw [← hxB l u r, ← hxT l u r]
  ring

/-- A version of the splitting formulas with `ContinuousOn` on the union is
occasionally needed for a resolvent with a pole. Stating it just with the six
one-dimensional integrability assumptions avoids any choices at the crossing. -/
lemma box_split_horizontal' (l r b u t : ℝ) (q : ℂ → ℂ)
    (hr1 : IntervalIntegrable (fun y : ℝ => q (r + y * Complex.I))
      volume b u)
    (hr2 : IntervalIntegrable (fun y : ℝ => q (r + y * Complex.I))
      volume u t)
    (hl1 : IntervalIntegrable (fun y : ℝ => q (l + y * Complex.I))
      volume b u)
    (hl2 : IntervalIntegrable (fun y : ℝ => q (l + y * Complex.I))
      volume u t) :
    box l r b u q + box l r u t q = box l r b t q := by
  have R := intervalIntegral.integral_add_adjacent_intervals hr1 hr2
  have L := intervalIntegral.integral_add_adjacent_intervals hl1 hl2
  simp only [box]
  rw [← R, ← L]
  ring

lemma box_split_vertical' (l u r b t : ℝ) (q : ℂ → ℂ)
    (hb1 : IntervalIntegrable (fun x : ℝ => q (x + b * Complex.I)) volume l u)
    (hb2 : IntervalIntegrable (fun x : ℝ => q (x + b * Complex.I)) volume u r)
    (ht1 : IntervalIntegrable (fun x : ℝ => q (x + t * Complex.I)) volume l u)
    (ht2 : IntervalIntegrable (fun x : ℝ => q (x + t * Complex.I)) volume u r) :
    box l u b t q + box u r b t q = box l r b t q := by
  have B := intervalIntegral.integral_add_adjacent_intervals hb1 hb2
  have T := intervalIntegral.integral_add_adjacent_intervals ht1 ht2
  simp only [box]
  rw [← B, ← T]
  ring

end WL.Planar

namespace WL.Planar
open Set MeasureTheory intervalIntegral
open scoped Real Interval BigOperators
/-- The bottom side contribution for a square centred at the origin.  Keeping
this elementary computation in the scalar library avoids any use of a
winding-number API. -/
lemma square_bottom (r : ℝ) (hr : 0 < r) :
    (∫ x : ℝ in -r..r, ((x : ℂ) - (r : ℂ) * Complex.I)⁻¹)
       = (Real.pi / 2 : ℝ) * Complex.I := by
  have hpoint (x : ℝ) :
    ((x : ℂ) - (r : ℂ) * Complex.I)⁻¹ =
       ((x / (x^2+r^2) : ℝ) : ℂ) +
         ((r / (r^2+x^2) : ℝ) : ℂ) * Complex.I := by
    have hn : (x:ℂ) - (r:ℂ)*Complex.I ≠ 0 := by
      intro h; have h' := congrArg Complex.im h
      simp at h'; linarith
    have hp : x^2 + r^2 ≠ 0 := by nlinarith
    have hp' : r^2 + x^2 ≠ 0 := by nlinarith
    apply (mul_left_cancel₀ hn)
    rw [mul_inv_cancel₀ hn]
    push_cast
    ring_nf
    rw [Complex.I_sq]
    have hc : (x:ℂ)^2 + (r:ℂ)^2 ≠ 0 := by exact_mod_cast hp
    field_simp
    ring
  simp_rw [hpoint]
  rw [intervalIntegral.integral_add]
  · simp_rw [intervalIntegral.integral_mul_const]
    rw [intervalIntegral.integral_ofReal]
    rw [intervalIntegral.integral_ofReal]
    have hodd : (∫ x : ℝ in -r..r, x / (x^2+r^2)) = 0 := by
      let k : ℝ → ℝ := fun x => x / (x^2+r^2)
      have hc (x : ℝ) : k (-x) = - k x := by dsimp [k]; ring
      have hcomp := intervalIntegral.integral_comp_neg (a := -r) (b := r) k
      have hneg : (∫ x : ℝ in -r..r, k (-x)) = -(∫ x : ℝ in -r..r, k x) := by
        simp_rw [hc]
        rw [intervalIntegral.integral_neg]
      have hh : (∫ x : ℝ in -r..r, k x) = -(∫ x : ℝ in -r..r, k x) := by
        rw [hcomp] at hneg
        simpa using hneg
      dsimp [k] at hh ⊢
      linarith
    rw [hodd]
    simp
    rw [integral_div_sq_add_sq (a := -r) (b := r) (c := r)]
    have hn : r ≠ 0 := ne_of_gt hr
    rw [div_self hn]
    rw [neg_div, div_self hn]
    rw [Real.arctan_neg, Real.arctan_one]
    push_cast
    ring
  · have hcont : Continuous (fun x : ℝ => ((x / (x^2+r^2):ℝ):ℂ)) := by
      exact Complex.continuous_ofReal.comp
        ( (continuous_id.div₀ (continuous_id.pow 2 |>.add continuous_const)
            (fun x => by nlinarith [sq_nonneg x])))
    exact hcont.intervalIntegrable _ _
  · have hcont : Continuous (fun x : ℝ => (((r / (r^2+x^2):ℝ):ℂ) * Complex.I)) := by
      apply Continuous.mul _ continuous_const
      exact Complex.continuous_ofReal.comp
        ( (continuous_const.div₀ (continuous_const.add (continuous_id.pow 2))
            (fun x => by nlinarith [sq_nonneg x])))
    exact hcont.intervalIntegrable _ _

/-- The positively oriented square has winding integral `2πi`. -/
lemma box_inv_square (r : ℝ) (hr : 0 < r) :
  box (-r) r (-r) r (fun z : ℂ => z⁻¹) = (2*(Real.pi:ℂ)*Complex.I) := by
  have hJ : (∫ x : ℝ in -r..r, ((x : ℂ) - (r : ℂ) * Complex.I)⁻¹)
       = (Real.pi / 2 : ℝ) * Complex.I := square_bottom r hr
  let J : ℂ := ∫ x : ℝ in -r..r, ((x : ℂ) - (r : ℂ) * Complex.I)⁻¹
  have bot : (∫ x : ℝ in -r..r, ((x:ℂ) + (-r:ℝ) * Complex.I)⁻¹) = J := by
    simp [J, sub_eq_add_neg]
  have top0 (x : ℝ) : (((-x:ℝ):ℂ) + (r:ℝ) * Complex.I)⁻¹ =
      - (((x:ℂ) - (r:ℂ)*Complex.I)⁻¹) := by
    rw [show ((-x:ℝ):ℂ) + (r:ℝ)*Complex.I = - ((x:ℂ) - (r:ℂ)*Complex.I) by push_cast; ring]
    rw [inv_neg]
  have top : -(∫ x : ℝ in -r..r, ((x:ℂ) + (r:ℝ) * Complex.I)⁻¹) = J := by
    have hh := intervalIntegral.integral_comp_neg (a := -r) (b := r)
      (fun x : ℝ => ((x:ℂ)+(r:ℝ)*Complex.I)⁻¹)
    simp only [neg_neg] at hh
    simp_rw [top0] at hh
    rw [intervalIntegral.integral_neg] at hh
    dsimp [J]
    linear_combination hh
  have right0 (x : ℝ) :
      Complex.I * (((r:ℝ):ℂ) + (x:ℝ)*Complex.I)⁻¹ =
        ((x:ℂ) - (r:ℂ)*Complex.I)⁻¹ := by
    have hn : Complex.I ≠ 0 := Complex.I_ne_zero
    rw [show ((r:ℝ):ℂ)+(x:ℝ)*Complex.I =
        Complex.I * ((x:ℂ)-(r:ℂ)*Complex.I) by push_cast; ring_nf; rw [Complex.I_sq]; ring]
    rw [mul_inv_rev]; rw [mul_comm Complex.I, mul_assoc, inv_mul_cancel₀ hn, mul_one]
  have right : Complex.I *
       (∫ x : ℝ in -r..r, (((r:ℝ):ℂ) + (x:ℝ)*Complex.I)⁻¹) = J := by
    rw [← intervalIntegral.integral_const_mul]
    simp_rw [right0]
    rfl
  have left0 (x : ℝ) :
      (-Complex.I) * (((-r:ℝ):ℂ) + ((-x:ℝ):ℂ)*Complex.I)⁻¹ =
        ((x:ℂ) - (r:ℂ)*Complex.I)⁻¹ := by
    rw [show ((-r:ℝ):ℂ)+((-x:ℝ):ℂ)*Complex.I =
        -Complex.I * ((x:ℂ)-(r:ℂ)*Complex.I) by push_cast; ring_nf; rw [Complex.I_sq]; ring]
    have hn : (-Complex.I) ≠ 0 := neg_ne_zero.mpr Complex.I_ne_zero
    rw [mul_inv_rev]; rw [mul_comm (-Complex.I), mul_assoc, inv_mul_cancel₀ hn, mul_one]
  have left : -Complex.I *
       (∫ x : ℝ in -r..r, (((-r:ℝ):ℂ) + (x:ℝ)*Complex.I)⁻¹) = J := by
    rw [← intervalIntegral.integral_const_mul]
    have hh := intervalIntegral.integral_comp_neg (a := -r) (b := r)
      (fun x : ℝ => (-Complex.I) * (((-r:ℝ):ℂ) + (x:ℝ)*Complex.I)⁻¹)
    simp only [neg_neg] at hh
    rw [← hh]
    simp_rw [left0]
    rfl
  simp only [box]
  have hsum : J + J + J + J = (2*(Real.pi:ℂ)*Complex.I) := by
    dsimp [J]
    rw [hJ]
    push_cast
    ring
  calc
    _ = J + J + J + J := by
      linear_combination bot + top + right + left
    _ = _ := hsum
end WL.Planar

namespace WL.Planar
open Set MeasureTheory intervalIntegral
open scoped Real Interval BigOperators
/-- Countable-hole version.  In the grid proof the one exceptional point is
the pole. -/
lemma box_eq_zero_off (l r b t : ℝ) (q : ℂ → ℂ) (s : Set ℂ)
    (hs : s.Countable)
    (hc : ContinuousOn q ([[l,r]] ×ℂ [[b,t]]))
    (hd : ∀ z ∈ (Ioo (min l r) (max l r) ×ℂ Ioo (min b t) (max b t)) \ s,
      DifferentiableAt ℂ q z) :
    box l r b t q = 0 := by
  let z : ℂ := (l:ℂ) + (b:ℂ) * Complex.I
  let w : ℂ := (r:ℂ) + (t:ℂ) * Complex.I
  have hzr : z.re = l := by simp [z]
  have hzi : z.im = b := by simp [z]
  have hwr : w.re = r := by simp [w]
  have hwi : w.im = t := by simp [w]
  have h := Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    q z w s hs (by simpa [hzr,hzi,hwr,hwi] using hc)
      (by simpa [hzr,hzi,hwr,hwi] using hd)
  simpa [box, hzr,hzi,hwr,hwi, mul_comm] using h

/-- Pointwise equalities on four infinite lines are enough for box integrals;
no integrability assumption is needed for `_congr`. This is handy for the
`slope` at the removable pole. -/
lemma box_congr_lines (l r b t : ℝ) {q p : ℂ → ℂ}
    (hb : ∀ x : ℝ, q (x + b * Complex.I) = p (x + b * Complex.I))
    (ht : ∀ x : ℝ, q (x + t * Complex.I) = p (x + t * Complex.I))
    (hr : ∀ y : ℝ, q (r + y * Complex.I) = p (r + y * Complex.I))
    (hl : ∀ y : ℝ, q (l + y * Complex.I) = p (l + y * Complex.I)) :
    box l r b t q = box l r b t p := by
  have B : (∫ x : ℝ in l..r, q (x + b * Complex.I)) =
      ∫ x : ℝ in l..r, p (x + b * Complex.I) :=
    intervalIntegral.integral_congr (fun x _ => hb x)
  have T : (∫ x : ℝ in l..r, q (x + t * Complex.I)) =
      ∫ x : ℝ in l..r, p (x + t * Complex.I) :=
    intervalIntegral.integral_congr (fun x _ => ht x)
  have R : (∫ x : ℝ in b..t, q (r + x * Complex.I)) =
      ∫ x : ℝ in b..t, p (r + x * Complex.I) :=
    intervalIntegral.integral_congr (fun x _ => hr x)
  have L : (∫ x : ℝ in b..t, q (l + x * Complex.I)) =
      ∫ x : ℝ in b..t, p (l + x * Complex.I) :=
    intervalIntegral.integral_congr (fun x _ => hl x)
  simp [box, B, T, R, L]
end WL.Planar

namespace WL.Planar
open Set
open scoped Real Interval
/-- The linear parametrisations used for surviving grid edges. Domain is all
of `ℝ` so it can be fed directly to an interval integral. -/
def edge (p q : ℂ) (t : ℝ) : ℂ := p + (t : ℂ) * (q - p)

def edge' (p q : ℂ) (_t : ℝ) : ℂ := q - p

lemma edge_continuous (p q : ℂ) : Continuous (edge p q) := by
  unfold edge
  fun_prop
lemma edge'_continuous (p q : ℂ) : Continuous (edge' p q) := by
  unfold edge'
  fun_prop
@[simp] lemma edge_zero (p q : ℂ) : edge p q 0 = p := by simp [edge]
@[simp] lemma edge_one (p q : ℂ) : edge p q 1 = q := by simp [edge]
/-- Rough bound (no square roots) for keeping a little edge in a compact
buffer. -/
lemma dist_edge_left {p q : ℂ} {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    dist (edge p q t) p ≤ dist q p := by
  rw [edge, dist_eq_norm, add_sub_cancel_left]
  rw [norm_mul, Complex.norm_real, dist_eq_norm]
  have h : |t| ≤ 1 := by rw [abs_of_nonneg ht.1]; exact ht.2
  simpa using
    (mul_le_of_le_one_left (norm_nonneg (q-p)) h)
end WL.Planar

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Planar.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Convolution.lean
noncomputable section
open Set
open scoped ENNReal lp ComplexConjugate Real BigOperators
namespace WL

private def shear : (ℤ × ℤ) ≃ (ℤ × ℤ) where
  toFun p := (p.1 + p.2, p.1)
  invFun q := (q.2, q.1 - q.2)
  left_inv p := by ext <;> simp
  right_inv q := by ext <;> simp

/-- The product of the absolute values on two `ℓ¹` families is summable on
`ℤ × ℤ`. -/
lemma summable_prod_norm (a b : L1) :
    Summable (fun p : ℤ × ℤ => ‖a p.1‖ * ‖b p.2‖) := by
  rw [summable_prod_of_nonneg (by intro p; positivity)]
  constructor
  · intro k
    change Summable (fun y : ℤ => ‖a k‖ * ‖b y‖)
    exact (summable_norm b).mul_left _
  · -- outer series is a constant multiple of the first one
    simpa [← tsum_mul_left] using
      (summable_norm a).mul_right (∑' l : ℤ, ‖b l‖)

/-- The sheared summable double family. This change of coordinates is the useful
one for Laurent convolution. -/
lemma summable_shear_norm (a b : L1) :
    Summable (fun p : ℤ × ℤ => ‖a p.2‖ * ‖b (p.1 - p.2)‖) := by
  let F : ℤ × ℤ → ℝ := fun p => ‖a p.1‖ * ‖b p.2‖
  have h := summable_prod_norm a b
  have h' : Summable (F ∘ (shear : (ℤ×ℤ) ≃ (ℤ×ℤ)).symm) :=
    ((shear : (ℤ×ℤ) ≃ (ℤ×ℤ)).symm.summable_iff).2 h
  -- the inverse shear has exactly the formula above
  simpa [F, Function.comp_def, shear] using h'

lemma summable_inner_norm (a b : L1) (n : ℤ) :
    Summable (fun k : ℤ => ‖a k‖ * ‖b (n-k)‖) := by
  have h := summable_shear_norm a b
  have := (summable_prod_of_nonneg (f := fun p : ℤ × ℤ =>
    ‖a p.2‖ * ‖b (p.1-p.2)‖) (by intro p; positivity)).1 h
  simpa using this.1 n

lemma summable_norm_majorant (a b : L1) :
    Summable (fun n : ℤ => ∑' k : ℤ, ‖a k‖ * ‖b (n-k)‖) := by
  have h := summable_shear_norm a b
  have := (summable_prod_of_nonneg (f := fun p : ℤ × ℤ =>
    ‖a p.2‖ * ‖b (p.1-p.2)‖) (by intro p; positivity)).1 h
  simpa using this.2

/-- Laurent convolution of two absolutely summable coefficient families. -/
def conv (a b : L1) : L1 := by
  let c : ℤ → ℂ := fun n => ∑' k : ℤ, a k * b (n-k)
  have bound (n : ℤ) : ‖c n‖ ≤ ∑' k : ℤ, ‖a k‖ * ‖b (n-k)‖ := by
    have hh : Summable (fun k : ℤ => ‖a k * b (n-k)‖) := by
      simpa [norm_mul] using (summable_inner_norm a b n)
    simpa [c, norm_mul] using (norm_tsum_le_tsum_norm hh)
  have hs : Summable (fun n : ℤ => ‖c n‖) :=
    Summable.of_nonneg_of_le (fun n => norm_nonneg _)
      bound (summable_norm_majorant a b)
  exact ofSummable c (.of_norm hs)

@[simp] lemma conv_apply (a b : L1) (n : ℤ) :
    conv a b n = ∑' k : ℤ, a k * b (n-k) := rfl

lemma norm_conv_le (a b : L1) : ‖conv a b‖ ≤ ‖a‖ * ‖b‖ := by
  rw [norm_eq, norm_eq, norm_eq]
  have inner (n : ℤ) :
      ‖conv a b n‖ ≤ ∑' k : ℤ, ‖a k‖ * ‖b (n-k)‖ := by
    have hh : Summable (fun k : ℤ => ‖a k * b (n-k)‖) := by
      simpa [norm_mul] using (summable_inner_norm a b n)
    simpa [conv_apply, norm_mul] using (norm_tsum_le_tsum_norm hh)
  calc
    (∑' n : ℤ, ‖conv a b n‖) ≤
        ∑' n : ℤ, ∑' k : ℤ, ‖a k‖ * ‖b (n-k)‖ :=
      Summable.tsum_le_tsum inner (summable_norm (conv a b))
        (summable_norm_majorant a b)
    _ = ∑' p : ℤ × ℤ, ‖a p.2‖ * ‖b (p.1-p.2)‖ := by
      exact (summable_shear_norm a b).tsum_prod.symm
    _ = ∑' p : ℤ × ℤ, ‖a p.1‖ * ‖b p.2‖ := by
      -- invariance of summation under shear
      simpa [Function.comp_def, shear] using
        ((shear : (ℤ×ℤ) ≃ (ℤ×ℤ)).symm.tsum_eq
          (fun p : ℤ×ℤ => ‖a p.1‖ * ‖b p.2‖))
    _ = (∑' k : ℤ, ‖a k‖) * (∑' l : ℤ, ‖b l‖) := by
      exact (Summable.tsum_mul_tsum (summable_norm a)
        (summable_norm b) (summable_prod_norm a b)).symm

end WL

section extra
open WL Set
open scoped ENNReal lp ComplexConjugate Real BigOperators
noncomputable section

lemma WL.norm_monomial {T : ℝ} [Fact (0 < T)] (c : ℂ) (n : ℤ) :
    ‖c • (fourier (T:=T) n)‖ = ‖c‖ := by
  simp [norm_smul, fourier_norm]

lemma WL.synth_conv {T : ℝ} [Fact (0 < T)] (a b : WL.L1) :
    WL.synth (T:=T) (WL.conv a b) =
      WL.synth (T:=T) a * WL.synth (T:=T) b := by
  let P : ℤ × ℤ → C(AddCircle T, ℂ) := fun p =>
    (a p.2 * b (p.1-p.2)) • fourier (T:=T) p.1
  let Q : ℤ × ℤ → C(AddCircle T, ℂ) := fun p =>
    (a p.1 • fourier (T:=T) p.1) *
      (b p.2 • fourier (T:=T) p.2)
  have hP : Summable P := by
    apply Summable.of_norm
    simpa [P, WL.norm_monomial, norm_mul] using WL.summable_shear_norm a b
  have hQnorm1 : Summable (fun k : ℤ => ‖a k • fourier (T:=T) k‖) := by
    simpa [WL.norm_monomial] using WL.summable_norm a
  have hQnorm2 : Summable (fun k : ℤ => ‖b k • fourier (T:=T) k‖) := by
    simpa [WL.norm_monomial] using WL.summable_norm b
  have hleft : WL.synth (T:=T) (WL.conv a b) = ∑' p : ℤ × ℤ, P p := by
    change (∑' n : ℤ, WL.conv a b n • fourier (T:=T) n) = _
    calc
      (∑' n : ℤ, WL.conv a b n • fourier (T:=T) n)
          = ∑' n : ℤ, ∑' k : ℤ,
              (a k * b (n-k)) • fourier (T:=T) n := by
            apply tsum_congr
            intro n
            have hs : Summable (fun k : ℤ => a k * b (n-k)) :=
              .of_norm (by simpa [norm_mul] using WL.summable_inner_norm a b n)
            simpa [WL.conv_apply] using
              (hs.hasSum.smul_const (fourier (T:=T) n)).tsum_eq.symm
      _ = ∑' p : ℤ × ℤ, P p := by
            exact hP.tsum_prod.symm
  have hright : WL.synth (T:=T) a * WL.synth (T:=T) b = ∑' p : ℤ × ℤ, Q p := by
    change (∑' n : ℤ, a n • fourier (T:=T) n) *
      (∑' n : ℤ, b n • fourier (T:=T) n) = _
    exact tsum_mul_tsum_of_summable_norm hQnorm1 hQnorm2
  rw [hleft, hright]
  -- the two double series differ by the integral shear `(k,l) ↦ (k+l,k)`.
  -- Write the equivalence out rather than appealing to conditional Cauchy
  -- products: all these series are absolutely summable.
  have reindex : (∑' p : ℤ × ℤ, Q p) = ∑' p : ℤ × ℤ, P p := by
    -- coordinates q=(k,l), p=(k+l,k)
    have eqfun : (fun q : ℤ × ℤ => P (WL.shear q)) = Q := by
      funext q
      rcases q with ⟨k,l⟩
      -- equality in the algebra of continuous maps follows pointwise
      ext x
      dsimp [P, Q, WL.shear]
      -- the Fourier characters multiply by adding their indices
      -- and scalar multiplication is pointwise multiplication.
      simp [Pi.add_apply, fourier_add]
      -- ring suffices after simplifying the integer subtraction
      <;> ring
    -- invariance of tsum under an equivalence
    have h := (WL.shear).tsum_eq P
    -- h : sum over q, P(shear q) = sum p, P p
    simpa [eqfun] using h
  exact reindex.symm
end
end extra

namespace WL
open Set
open scoped ENNReal lp ComplexConjugate Real BigOperators
noncomputable section
variable {T : ℝ} [Fact (0 < T)]

/-- Absolutely summable Fourier series are closed under pointwise products. Proving
this directly with integrals is unpleasant; normal convergence and the Laurent
convolution give a clean statement. -/
lemma summable_fourierCoeff_mul (f h : C(AddCircle T, ℂ))
    (hf : Summable (fourierCoeff f)) (hh : Summable (fourierCoeff h)) :
    Summable (fourierCoeff (f * h)) := by
  obtain ⟨a, ha⟩ := (mem_range_synth (T:=T) f).1 hf
  obtain ⟨b, hb⟩ := (mem_range_synth (T:=T) h).1 hh
  apply (mem_range_synth (T:=T) (f*h)).2
  exact ⟨conv a b, by rw [synth_conv, ha, hb]⟩

end
end WL

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Convolution.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Grid.lean

noncomputable section
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
namespace WL.Planar

variable {s : ℝ}

/- Elementary real lattice used for the rectangular chain. Keeping the lower
coordinate as `((m:ℝ)*s)` (rather than `(m*s : ℝ)` after an integer
multiplication) makes the adjacent sides definitional. -/
def lo (s : ℝ) (m : ℤ) : ℝ := (m:ℝ) * s
def hi (s : ℝ) (m : ℤ) : ℝ := (m:ℝ) * s + s

def pt (x y : ℝ) : ℂ := (x:ℂ) + (y:ℂ) * Complex.I

def cell (s : ℝ) (i : ℤ × ℤ) : Set ℂ :=
  {z | z.re ∈ Set.Icc (lo s i.1) (hi s i.1) ∧
       z.im ∈ Set.Icc (lo s i.2) (hi s i.2)}

lemma hi_eq_lo_succ (s : ℝ) (m : ℤ) : hi s m = lo s (m+1) := by
  dsimp [lo, hi]
  push_cast
  ring

lemma lo_le_hi (hs : 0 ≤ s) (m : ℤ) : lo s m ≤ hi s m := by
  dsimp [lo,hi]; linarith

@[simp] lemma re_pt (x y : ℝ) : (pt x y).re = x := by simp [pt]
@[simp] lemma im_pt (x y : ℝ) : (pt x y).im = y := by simp [pt]

lemma mem_cell_iff (s : ℝ) (i : ℤ×ℤ) (z : ℂ) :
    z ∈ cell s i ↔
      lo s i.1 ≤ z.re ∧ z.re ≤ hi s i.1 ∧
      lo s i.2 ≤ z.im ∧ z.im ≤ hi s i.2 := by
  constructor
  · intro h
    exact ⟨h.1.1, h.1.2, h.2.1, h.2.2⟩
  · rintro ⟨a,b,c,d⟩
    exact ⟨⟨a,b⟩,⟨c,d⟩⟩

lemma cell_subset_U_of_point {s : ℝ} (hs : 0 < s) {K U : Set ℂ}
    (buffer : ∀ {z w : ℂ}, w ∈ K → dist z w ≤ 4*s → z ∈ U)
    {i : ℤ×ℤ} (hmeet : (cell s i ∩ K).Nonempty) : cell s i ⊆ U := by
  intro z hz
  obtain ⟨w, hwcell, hwK⟩ := hmeet
  have a1 := (mem_cell_iff s i z).1 hz
  have a2 := (mem_cell_iff s i w).1 hwcell
  -- use coordinate sup bound, the constant 4 avoids square roots
  have hre : |z.re - w.re| ≤ s := by
    rw [abs_le]
    dsimp [lo,hi] at *
    constructor <;> linarith
  have him : |z.im - w.im| ≤ s := by
    rw [abs_le]
    dsimp [lo,hi] at *
    constructor <;> linarith
  have hnorm : dist z w ≤ 4*s := by
    rw [dist_eq_norm]
    -- the crude l1 estimate for the euclidean norm is sufficient.
    have htri : ‖z-w‖ ≤ |(z-w).re| + |(z-w).im| := Complex.norm_le_abs_re_add_abs_im _
    have hr' : |(z-w).re| ≤ s := by simpa using hre
    have hi' : |(z-w).im| ≤ s := by simpa using him
    exact htri.trans (by linarith)
  exact buffer hwK hnorm

/-- Integer coordinate of a point; points on a lattice line are assigned the
box on its positive side. -/
def ix (s : ℝ) (x : ℝ) : ℤ := ⌊x / s⌋

lemma coord_mem (hs : 0 < s) (x : ℝ) :
    lo s (ix s x) ≤ x ∧ x ≤ hi s (ix s x) := by
  dsimp [lo, hi, ix]
  have h1 : (⌊x / s⌋ : ℤ) ≤ ⌊x / s⌋ := le_rfl
  have h1' : (⌊x / s⌋ : ℝ) ≤ x / s := Int.floor_le _
  have h2' : x / s < (⌊x / s⌋ : ℝ) + 1 := Int.lt_floor_add_one _
  constructor
  · calc
      (⌊x / s⌋ : ℝ) * s ≤ (x/s) * s :=
        (mul_le_mul_of_nonneg_right h1' (le_of_lt hs))
      _ = x := by field_simp
  · have : x/s ≤ (⌊x / s⌋ : ℝ) + 1 := le_of_lt h2'
    have := mul_le_mul_of_nonneg_right this (le_of_lt hs)
    calc
      x = (x/s)*s := by field_simp
      _ ≤ ((⌊x / s⌋ : ℝ)+1)*s := this
      _ = (⌊x / s⌋ : ℝ)*s + s := by ring

lemma coord_strict (hs : 0 < s) {x : ℝ}
    (hx : ∀ m : ℤ, x ≠ lo s m) :
    lo s (ix s x) < x ∧ x < hi s (ix s x) := by
  have h := coord_mem hs x
  constructor
  · exact lt_of_le_of_ne h.1 (Ne.symm (hx _))
  · have hnot : x ≠ hi s (ix s x) := by
      rw [hi_eq_lo_succ]
      exact hx _
    exact lt_of_le_of_ne h.2 hnot

lemma mem_own_cell (hs : 0 < s) (z : ℂ) :
    z ∈ cell s (ix s z.re, ix s z.im) := by
  apply (mem_cell_iff ..).2
  exact ⟨(coord_mem hs _).1, (coord_mem hs _).2,
    (coord_mem hs _).1, (coord_mem hs _).2⟩

/-- On the open stratum of the lattice a point belongs to a unique closed
box. This is the small fact that lets us postpone points on internal lines to
continuity. -/
lemma eq_own_of_mem_of_strict (hs : 0 < s) {z : ℂ}
    (hx : ∀ m : ℤ, z.re ≠ lo s m) (hy : ∀ n : ℤ, z.im ≠ lo s n)
    {i : ℤ × ℤ} (hi' : z ∈ cell s i) : i = (ix s z.re, ix s z.im) := by
  have h := (mem_cell_iff s i z).1 hi'
  have ux := coord_strict hs hx
  have uy := coord_strict hs hy
  -- disjointness of two intervals of the positive grid follows already from
  -- the floor inequalities.
  have one (k j : ℤ) {x : ℝ}
      (A : lo s k ≤ x) (B : x ≤ hi s k)
      (C : lo s j < x) (D : x < hi s j) : k = j := by
    by_contra ne
    rcases lt_or_gt_of_ne ne with hlt | hgt
    · -- k < j; right endpoint of k is at most left endpoint of j
      have hle : k + 1 ≤ j := by omega
      have hz : lo s (k+1) ≤ lo s j := by
        dsimp [lo]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hs)
      have : hi s k ≤ lo s j := by simpa [hi_eq_lo_succ] using hz
      linarith
    · have hle : j + 1 ≤ k := by omega
      have hz : lo s (j+1) ≤ lo s k := by
        dsimp [lo]
        exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hs)
      have : hi s j ≤ lo s k := by simpa [hi_eq_lo_succ] using hz
      linarith
  have hxe : i.1 = ix s z.re := one _ _ h.1 h.2.1 ux.1 ux.2
  have hye : i.2 = ix s z.im := one _ _ h.2.2.1 h.2.2.2 uy.1 uy.2
  exact Prod.ext hxe hye

end WL.Planar

namespace WL.Planar
open Set MeasureTheory Metric
open scoped Real Interval BigOperators
/-- There are only finitely many grid boxes meeting a bounded set. We keep an
actual finset together with its membership theorem; subsequent sides can thus
be filtered without quotients. -/
lemma finite_cells {s : ℝ} (hs : 0 < s) {K : Set ℂ} (hK : IsCompact K) :
    ∃ S : Finset (ℤ × ℤ), ∀ i : ℤ × ℤ,
       i ∈ S ↔ (cell s i ∩ K).Nonempty := by
  classical
  obtain ⟨r, hr⟩ := hK.isBounded.subset_closedBall (0:ℂ)
  let B : ℝ := max r 0
  have hB : 0 ≤ B := (le_max_right _ _)
  have hnorm : ∀ z ∈ K, ‖z‖ ≤ B := by
    intro z hz
    have hh := hr hz
    have : ‖z‖ ≤ r := by simpa [Metric.mem_closedBall] using hh
    exact this.trans (le_max_left _ _)
  obtain ⟨N, hN⟩ := exists_int_gt (B/s + 2)
  have hNs : B + 2*s < (N:ℝ)*s := by
    have := mul_lt_mul_of_pos_right hN hs
    have hs0 : s ≠ 0 := ne_of_gt hs
    calc
      B + 2*s = (B/s + 2)*s := by field_simp
      _ < (N:ℝ)*s := this
  let base : Finset (ℤ × ℤ) := (Finset.Icc (-N) N).product (Finset.Icc (-N) N)
  let S : Finset (ℤ × ℤ) := base.filter (fun i => (cell s i ∩ K).Nonempty)
  refine ⟨S, ?_⟩
  intro i
  simp only [S, Finset.mem_filter]
  constructor
  · exact fun h => h.2
  · intro h
    refine ⟨?_, h⟩
    obtain ⟨z, hzcell, hzK⟩ := h
    have hh := (mem_cell_iff s i z).1 hzcell
    have hzN := hnorm z hzK
    have hre := Complex.abs_re_le_norm z
    have him := Complex.abs_im_le_norm z
    have hre' : |z.re| ≤ B := hre.trans hzN
    have him' : |z.im| ≤ B := him.trans hzN
    have bound (m : ℤ) (x : ℝ) (ha : lo s m ≤ x) (hb : x ≤ hi s m)
        (hx : |x| ≤ B) : -N ≤ m ∧ m ≤ N := by
      have hx1 : x ≤ B := (le_abs_self x).trans hx
      have hx0 : -B ≤ x := (neg_le_of_abs_le hx)
      have hmU : (m:ℝ)*s ≤ B := by dsimp [lo] at ha; linarith
      have hmL : -B ≤ (m:ℝ)*s+s := by dsimp [hi] at hb; linarith
      have hu : (m:ℝ) < (N:ℝ) := by
        nlinarith
      have hl : (-N:ℝ) < (m:ℝ) := by
        push_cast
        nlinarith
      have hu' : m ≤ N := le_of_lt (by exact_mod_cast hu)
      have hl' : -N ≤ m := le_of_lt (by exact_mod_cast hl)
      exact ⟨hl', hu'⟩
    have hx := bound i.1 z.re hh.1 hh.2.1 hre'
    have hy := bound i.2 z.im hh.2.2.1 hh.2.2.2 him'
    exact Finset.mem_product.2
      ⟨Finset.mem_Icc.2 hx, Finset.mem_Icc.2 hy⟩
end WL.Planar
namespace WL.Planar
open scoped BigOperators
inductive Side where | bot | top | right | left
  deriving DecidableEq, Fintype
open Side

def nb (i : ℤ×ℤ) : Side → ℤ×ℤ
 | bot => (i.1, i.2-1)
 | top => (i.1, i.2+1)
 | right => (i.1+1, i.2)
 | left => (i.1-1, i.2)

def opp (u : (ℤ×ℤ) × Side) : (ℤ×ℤ) × Side :=
  match u.2 with
  | bot => (nb u.1 bot, top)
  | top => (nb u.1 top, bot)
  | right => (nb u.1 right, left)
  | left => (nb u.1 left, right)

@[simp] lemma opp_fst (u : (ℤ×ℤ) × Side) : (opp u).1 = nb u.1 u.2 := by
  cases u with | mk i d => cases d <;> rfl
lemma opp_ne (u : (ℤ×ℤ) × Side) : opp u ≠ u := by
  rcases u with ⟨⟨m,n⟩, d⟩
  cases d <;> intro h
  all_goals
    have hh := congrArg Prod.snd h
    simp [opp, nb] at hh
@[simp] lemma opp_opp (u : (ℤ×ℤ) × Side) : opp (opp u) = u := by
  rcases u with ⟨⟨m,n⟩, d⟩
  cases d <;> simp [opp, nb]

lemma univ_side : (Finset.univ : Finset Side) = {bot, top, right, left} := by
  ext d
  cases d <;> decide

def allSides (S : Finset (ℤ×ℤ)) : Finset ((ℤ×ℤ) × Side) := S.product Finset.univ

def boundary (S : Finset (ℤ×ℤ)) : Finset ((ℤ×ℤ) × Side) :=
  (allSides S).filter (fun u => nb u.1 u.2 ∉ S)

def internal (S : Finset (ℤ×ℤ)) : Finset ((ℤ×ℤ) × Side) :=
  (allSides S).filter (fun u => nb u.1 u.2 ∈ S)

lemma mem_allSides {S : Finset (ℤ×ℤ)} {u : (ℤ×ℤ) × Side} :
    u ∈ allSides S ↔ u.1 ∈ S := by
  simp [allSides]
lemma mem_boundary {S : Finset (ℤ×ℤ)} {u : (ℤ×ℤ) × Side} :
    u ∈ boundary S ↔ u.1 ∈ S ∧ nb u.1 u.2 ∉ S := by
  simp [boundary, mem_allSides]
lemma mem_internal {S : Finset (ℤ×ℤ)} {u : (ℤ×ℤ) × Side} :
    u ∈ internal S ↔ u.1 ∈ S ∧ nb u.1 u.2 ∈ S := by
  simp [internal, mem_allSides]

variable {M : Type*} [AddCommGroup M]
/-- The algebraic cancellation of the internal sides of a union of grid
boxes. No integrability of the functions on internal lines is used here; it
is an identity between four (possibly arbitrary) line values. -/
lemma sum_boundary (S : Finset (ℤ×ℤ)) (H V : ℤ → ℤ → M) :
    (∑ u ∈ boundary S,
      match u.2 with
      | bot => H u.1.1 u.1.2
      | top => - H u.1.1 (u.1.2+1)
      | right => V (u.1.1+1) u.1.2
      | left => - V u.1.1 u.1.2) =
    ∑ i ∈ S, (H i.1 i.2 - H i.1 (i.2+1) +
                         V (i.1+1) i.2 - V i.1 i.2) := by
  classical
  let val : ((ℤ×ℤ) × Side) → M := fun u =>
      match u.2 with
      | bot => H u.1.1 u.1.2
      | top => - H u.1.1 (u.1.2+1)
      | right => V (u.1.1+1) u.1.2
      | left => - V u.1.1 u.1.2
  have valopp (u : (ℤ×ℤ) × Side) : val u + val (opp u) = 0 := by
    rcases u with ⟨⟨m,n⟩, d⟩
    cases d <;> simp [val, opp, nb] <;> try {rfl} <;>
      congr 2 <;> omega
  have intzero : (∑ u ∈ internal S, val u) = 0 := by
    apply Finset.sum_involution (s:=internal S)
      (fun u _ => opp u)
    · intro u hu
      exact valopp u
    · intro u hu hn
      exact opp_ne u
    · intro u hu
      rw [mem_internal] at hu ⊢
      constructor
      · simpa [opp_fst] using hu.2
      · have : nb (opp u).1 (opp u).2 = u.1 := by
          have h := congrArg Prod.fst (opp_opp u)
          simpa only [opp_fst] using h
        rw [this]
        exact hu.1
    · intro u hu
      exact opp_opp u
  have split : boundary S ∪ internal S = allSides S := by
    ext u
    by_cases h : nb u.1 u.2 ∈ S <;> simp [mem_boundary, mem_internal, mem_allSides, h]
  have disj : Disjoint (boundary S) (internal S) := by
    exact Finset.disjoint_left.2 (by
      intro u hb hi
      exact (mem_boundary.1 hb).2 (mem_internal.1 hi).2)
  have htotal : (∑ u ∈ boundary S, val u) = ∑ u ∈ allSides S, val u := by
    have he := Finset.sum_union disj (f:=val)
    rw [split, intzero, add_zero] at he
    exact he.symm
  change (∑ u ∈ boundary S, val u) = _
  rw [htotal]
  -- group the four directions at each cell
  have hdir (i : ℤ×ℤ) :
      (∑ d : Side, val (i,d)) =
        H i.1 i.2 - H i.1 (i.2+1) +
          V (i.1+1) i.2 - V i.1 i.2 := by
    rw [univ_side]
    -- `sum_insert` twice leaves a harmless order of the four terms
    simp [val]
    abel
  calc
    (∑ u ∈ (S.product (Finset.univ : Finset Side)), val u) =
        ∑ i ∈ S, ∑ d : Side, val (i,d) :=
          Finset.sum_product S (Finset.univ : Finset Side) val
    _ = _ := by
      apply Finset.sum_congr rfl
      intro i hi
      exact hdir i
end WL.Planar
namespace WL.Planar
open Set Metric
open scoped Real Interval BigOperators
open Side

def p0 (s : ℝ) (i : ℤ×ℤ) : Side → ℂ
 | bot => pt (lo s i.1) (lo s i.2)
 | top => pt (hi s i.1) (hi s i.2)
 | right => pt (hi s i.1) (lo s i.2)
 | left => pt (lo s i.1) (hi s i.2)

def p1 (s : ℝ) (i : ℤ×ℤ) : Side → ℂ
 | bot => pt (hi s i.1) (lo s i.2)
 | top => pt (lo s i.1) (hi s i.2)
 | right => pt (hi s i.1) (hi s i.2)
 | left => pt (lo s i.1) (lo s i.2)

def path (s : ℝ) (u : (ℤ×ℤ)×Side) := edge (p0 s u.1 u.2) (p1 s u.1 u.2)
def vel (s : ℝ) (u : (ℤ×ℤ)×Side) := edge' (p0 s u.1 u.2) (p1 s u.1 u.2)

lemma side_mem_both {s : ℝ} (hs : 0 < s)
    (u : (ℤ×ℤ)×Side) {t : ℝ} (ht : t ∈ Set.Icc (0:ℝ) 1) :
    path s u t ∈ cell s u.1 ∩ cell s (nb u.1 u.2) := by
  rcases u with ⟨⟨m,n⟩,d⟩
  rcases ht with ⟨ht0,ht1⟩
  cases d <;>
    simp [path, p0, p1, edge, pt, cell, lo, hi, nb,
      Complex.mul_re, Complex.mul_im, Complex.sub_re, Complex.sub_im,
      Complex.add_re, Complex.add_im] <;>
    constructor <;> constructor <;> try constructor <;>
      try constructor <;> push_cast
  all_goals nlinarith

/-- Every selected cell is in the buffer and a boundary side, unlike an
internal one, is disjoint from the compact set. -/
lemma boundary_maps {s : ℝ} (hs : 0 < s) {K U : Set ℂ}
    (buffer : ∀ {z w : ℂ}, w ∈ K → dist z w ≤ 4*s → z ∈ U)
    (S : Finset (ℤ×ℤ))
    (hS : ∀ i : ℤ×ℤ, i ∈ S ↔ (cell s i ∩ K).Nonempty)
    {u : (ℤ×ℤ)×Side} (hu : u ∈ boundary S) :
    Set.MapsTo (path s u) (Set.uIcc (0:ℝ) 1) (U ∩ Kᶜ) := by
  intro t ht
  have ht' : t ∈ Set.Icc (0:ℝ) 1 := by simpa using ht
  have hb := side_mem_both hs u ht'
  have hsel : u.1 ∈ S := (mem_boundary.1 hu).1
  have hnot : nb u.1 u.2 ∉ S := (mem_boundary.1 hu).2
  have hmeet : (cell s u.1 ∩ K).Nonempty := (hS _).1 hsel
  refine ⟨cell_subset_U_of_point hs buffer hmeet hb.1, ?_⟩
  intro hK
  apply hnot
  apply (hS _).2
  exact ⟨path s u t, hb.2, hK⟩

end WL.Planar
namespace WL.Planar
open Set MeasureTheory intervalIntegral
open scoped Real Interval BigOperators
open Side

def edgeInt (s : ℝ) (u : (ℤ×ℤ)×Side) (q : ℂ → ℂ) : ℂ :=
  ∫ t : ℝ in (0:ℝ)..1, vel s u t * q (path s u t)

def lineH (s : ℝ) (q : ℂ → ℂ) (m n : ℤ) : ℂ :=
  ∫ x : ℝ in lo s m..hi s m, q (pt x (lo s n))
def lineV (s : ℝ) (q : ℂ → ℂ) (m n : ℤ) : ℂ :=
  Complex.I * (∫ y : ℝ in lo s n..hi s n, q (pt (lo s m) y))

lemma box_cell (s : ℝ) (i:ℤ×ℤ) (q : ℂ → ℂ) :
    box (lo s i.1) (hi s i.1) (lo s i.2) (hi s i.2) q =
      lineH s q i.1 i.2 - lineH s q i.1 (i.2+1) +
        lineV s q (i.1+1) i.2 - lineV s q i.1 i.2 := by
  simp [box, lineH, lineV, pt, hi_eq_lo_succ]

end WL.Planar
namespace WL.Planar
open Set Filter
/-- The removable quotient at a differentiability point, with the value
filled in by the derivative. This is the convenient continuous summand when
subtracting the polar part of Cauchy's kernel on the one box containing the
point. -/
def slopeFill (φ : ℂ → ℂ) (w : ℂ) : ℂ → ℂ :=
  Function.update (slope φ w) w (deriv φ w)
lemma slopeFill_same (φ : ℂ → ℂ) (w : ℂ) : slopeFill φ w w = deriv φ w := by
  simp [slopeFill]
lemma slopeFill_of_ne (φ : ℂ → ℂ) (w : ℂ) {z : ℂ} (hz : z ≠ w) :
    slopeFill φ w z = (φ z - φ w) * (z - w)⁻¹ := by
  rw [slopeFill, Function.update_of_ne hz]
  rw [slope_def_field]
  simp [div_eq_mul_inv]
lemma continuousAt_slopeFill (φ : ℂ → ℂ) {w : ℂ}
    (hw : DifferentiableAt ℂ φ w) : ContinuousAt (slopeFill φ w) w := by
  rw [slopeFill, continuousAt_update_same]
  exact (hasDerivAt_iff_tendsto_slope.mp hw.hasDerivAt)

/-- The filled slope is continuous on a rectangle as soon as `φ` is
continuous/differentiable there and at the center. Off the center it is just
an elementary quotient, so no analytic extension API is needed. -/
lemma continuousOn_slopeFill {φ : ℂ → ℂ} {w : ℂ} {A : Set ℂ}
    (hw : DifferentiableAt ℂ φ w)
    (hc : ContinuousOn φ A) : ContinuousOn (slopeFill φ w) A := by
  intro z hz
  by_cases he : z = w
  · simpa [he] using (continuousAt_slopeFill φ hw).continuousWithinAt
  · have hn : ∀ᶠ y in nhdsWithin z A, y ≠ w := by
      exact (eventually_nhdsWithin_of_eventually_nhds
        (eventually_ne_nhds he))
    have hform :
        (slopeFill φ w) =ᶠ[nhdsWithin z A]
          (fun y => (φ y - φ w) * (y-w)⁻¹) :=
      hn.mono (fun y hy => slopeFill_of_ne φ w hy)
    have hne : z - w ≠ 0 := sub_ne_zero.mpr he
    have hcont : ContinuousWithinAt
        (fun y => (φ y - φ w) * (y-w)⁻¹) A z :=
      ((hc z hz).sub continuousWithinAt_const).mul
        ((continuousWithinAt_id.sub continuousWithinAt_const).inv₀
          (by exact hne))
    exact hcont.congr_of_eventuallyEq hform (slopeFill_of_ne φ w he)
end WL.Planar


namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
open Side
lemma edgeInt_bot (s : ℝ) (q : ℂ → ℂ) (m n : ℤ) :
 edgeInt s ((m,n),Side.bot) q = lineH s q m n := by
  simp [edgeInt, vel, path, p0, p1, edge, edge', pt, lo, hi,
     lineH]
  let f : ℝ → ℂ := fun y => q ((y:ℂ) + (n:ℝ)*s*Complex.I)
  have hh := intervalIntegral.smul_integral_comp_add_mul
    (a:=(0:ℝ)) (b:=1) f s ((m:ℝ)*s)
  simp only [mul_zero, mul_one, add_zero] at hh
  -- align left integrand
  -- target scalar 
  change (s • ∫ t : ℝ in (0:ℝ)..1,
       q ((m:ℝ)*s + (n:ℝ)*s*Complex.I + (t:ℂ)*s)) = _
  calc
    (s • ∫ t : ℝ in (0:ℝ)..1,
       q ((m:ℝ)*s + (n:ℝ)*s*Complex.I + (t:ℂ)*s)) =
       s • ∫ t : ℝ in (0:ℝ)..1, f ((m:ℝ)*s + s*t) := by
         congr 1
         apply intervalIntegral.integral_congr
         intro t ht
         dsimp [f]
         push_cast
         ring_nf
    _ = ∫ y : ℝ in (m:ℝ)*s..(m:ℝ)*s+s, f y := by
         simpa only [mul_one, mul_zero, add_zero] using hh
    _ = _ := by
      apply intervalIntegral.integral_congr
      intro y hy
      dsimp [f]
lemma edgeInt_top (s : ℝ) (q : ℂ → ℂ) (m n : ℤ) :
 edgeInt s ((m,n),Side.top) q = - lineH s q m (n+1) := by
 simp [edgeInt, vel, path, p0, p1, edge, edge', pt, lo, hi,
     lineH]
 let f : ℝ → ℂ := fun y => q ((y:ℂ) + (((n:ℝ)*s+s:ℝ):ℂ)*Complex.I)
 have hh := intervalIntegral.smul_integral_comp_add_mul
    (a:=(0:ℝ)) (b:=1) f (-s) ((m:ℝ)*s+s)
 -- normalize bounds then negate
 simp only [mul_one, mul_zero, add_zero, neg_mul, one_mul] at hh
 have hh' := congrArg Neg.neg hh
 have hmain : s • (∫ t : ℝ in (0:ℝ)..1, f ((m:ℝ)*s+s + (-s)*t)) =
       ∫ y : ℝ in (m:ℝ)*s..(m:ℝ)*s+s, f y := by
   -- hh lhs simpl neg (-s • A)
   have hc : (m:ℝ)*s+s + -s = (m:ℝ)*s := by ring
   rw [hc] at hh'
   rw [intervalIntegral.integral_symm ((m:ℝ)*s) ((m:ℝ)*s+s)] at hh'
   -- now both negs
   simpa [neg_smul, add_assoc, add_comm, add_left_comm] using hh'
 change (s • ∫ t : ℝ in (0:ℝ)..1,
       q ((m:ℝ)*s+s + ((n:ℝ)*s+s)*Complex.I + (-((t:ℂ)*s)))) = _
 calc
  _ = s • (∫ t : ℝ in (0:ℝ)..1, f ((m:ℝ)*s+s + (-s)*t)) := by
    congr 1
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp [f]
    push_cast
    ring_nf
  _ = ∫ y : ℝ in (m:ℝ)*s..(m:ℝ)*s+s, f y := hmain
  _ = _ := by
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp [f]
    push_cast
    congr 2 <;> ring
lemma edgeInt_right (s : ℝ) (q : ℂ → ℂ) (m n : ℤ) :
 edgeInt s ((m,n),Side.right) q = lineV s q (m+1) n := by
 simp [edgeInt, vel, path, p0, p1, edge, edge', pt, lo, hi,
     lineV]
 push_cast
 ring_nf
 let f : ℝ → ℂ := fun y => q ((s:ℂ)+(s:ℂ)*(m:ℂ) + Complex.I*(y:ℂ))
 have hh := intervalIntegral.smul_integral_comp_add_mul
    (a:=(0:ℝ)) (b:=1) f s ((n:ℝ)*s)
 simp only [mul_one, mul_zero, add_zero] at hh

 calc
  _ = Complex.I * (s • ∫ t : ℝ in (0:ℝ)..1, f ((n:ℝ)*s + s*t)) := by
    change (s:ℂ)*Complex.I * (∫ t : ℝ in (0:ℝ)..1,
       q ( (n:ℂ)*(s:ℂ)*Complex.I + (s:ℂ) + (s:ℂ)*Complex.I*(t:ℂ) + (s:ℂ)*(m:ℂ))) = _
    have hAB : (∫ t : ℝ in (0:ℝ)..1,
       q ( (n:ℂ)*(s:ℂ)*Complex.I + (s:ℂ) + (s:ℂ)*Complex.I*(t:ℂ) + (s:ℂ)*(m:ℂ))) =
        ∫ t : ℝ in (0:ℝ)..1, f ((n:ℝ)*s + s*t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [f]
      push_cast
      ring_nf
    rw [hAB]
    change (s:ℂ)*Complex.I * _ = Complex.I * ((s:ℂ) * _)
    ring
  _ = Complex.I * (∫ y : ℝ in (n:ℝ)*s..(n:ℝ)*s+s, f y) := by
    rw [hh]
  _ = _ := by
    apply congrArg (fun v : ℂ => Complex.I * v)
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp [f]
lemma edgeInt_left (s : ℝ) (q : ℂ → ℂ) (m n : ℤ) :
 edgeInt s ((m,n),Side.left) q = - lineV s q m n := by
 simp [edgeInt, vel, path, p0, p1, edge, edge', pt, lo, hi,
     lineV]
 push_cast
 ring_nf
 let f : ℝ → ℂ := fun y => q ((s:ℂ)*(m:ℂ) + Complex.I*(y:ℂ))
 have hh := intervalIntegral.smul_integral_comp_add_mul
    (a:=(0:ℝ)) (b:=1) f (-s) ((n:ℝ)*s+s)
 simp only [mul_one, mul_zero, add_zero, neg_mul] at hh
 have hh' := congrArg Neg.neg hh
 have hmain : s • (∫ t : ℝ in (0:ℝ)..1, f ((n:ℝ)*s+s + (-s)*t)) =
       ∫ y : ℝ in (n:ℝ)*s..(n:ℝ)*s+s, f y := by
   have hc : (n:ℝ)*s+s + -s = (n:ℝ)*s := by ring
   rw [hc] at hh'
   rw [intervalIntegral.integral_symm ((n:ℝ)*s) ((n:ℝ)*s+s)] at hh'
   simpa [neg_smul, add_assoc, add_comm, add_left_comm] using hh'
 -- prove inners equality and negate
 congr 1
 -- now inner goal?
 calc
  _ = Complex.I * (s • ∫ t : ℝ in (0:ℝ)..1, f ((n:ℝ)*s+s + (-s)*t)) := by
    have hAB : (∫ t : ℝ in (0:ℝ)..1,
       q ((n:ℂ)*(s:ℂ)*Complex.I + (s:ℂ)*Complex.I - (s:ℂ)*Complex.I*(t:ℂ) + (s:ℂ)*(m:ℂ))) =
       ∫ t : ℝ in (0:ℝ)..1, f ((n:ℝ)*s+s + (-s)*t) := by
      apply intervalIntegral.integral_congr
      intro t ht
      dsimp [f]
      push_cast
      ring_nf
    rw [hAB]
    change (s:ℂ)*Complex.I * _ = Complex.I * ((s:ℂ) * _)
    ring
  _ = Complex.I * (∫ y : ℝ in (n:ℝ)*s..(n:ℝ)*s+s, f y) := by rw [hmain]
  _ = _ := by
    apply congrArg (fun v : ℂ => Complex.I * v)
    apply intervalIntegral.integral_congr
    intro y hy
    dsimp [f]

end WL.Planar

namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
open Side
/-- Reparametrising the little straight sides and cancelling every internal side
identifies the boundary chain with the sum of the four-edge boxes. This is
purely algebraic/change of variables; no integrability is needed. -/
lemma sum_edges_boxes (s : ℝ) (S : Finset (ℤ×ℤ)) (q : ℂ → ℂ) :
 (∑ u ∈ boundary S, edgeInt s u q) =
 ∑ i ∈ S, box (lo s i.1) (hi s i.1) (lo s i.2) (hi s i.2) q := by
 have h := sum_boundary S (lineH s q) (lineV s q)
 have one (u : (ℤ×ℤ)×Side) :
      edgeInt s u q =
      match u.2 with
      | bot => lineH s q u.1.1 u.1.2
      | top => - lineH s q u.1.1 (u.1.2+1)
      | right => lineV s q (u.1.1+1) u.1.2
      | left => - lineV s q u.1.1 u.1.2 := by
    rcases u with ⟨⟨m,n⟩,d⟩
    cases d
    · apply edgeInt_bot
    · apply edgeInt_top
    · apply edgeInt_right
    · apply edgeInt_left
 simp_rw [one]
 calc
  _ = ∑ i ∈ S, (lineH s q i.1 i.2 - lineH s q i.1 (i.2+1) +
                         lineV s q (i.1+1) i.2 - lineV s q i.1 i.2) := h
  _ = _ := by
   apply Finset.sum_congr rfl
   intro i hi'
   exact (box_cell s i q).symm
end WL.Planar

namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
lemma diff_slopeFill_off {φ : ℂ → ℂ} {w z : ℂ} (hne : z ≠ w)
 (hz : DifferentiableAt ℂ φ z) : DifferentiableAt ℂ (slopeFill φ w) z := by
 have hn : ∀ᶠ y in nhds z, y ≠ w := eventually_ne_nhds hne
 have hev : (slopeFill φ w) =ᶠ[nhds z]
          (fun y => (φ y - φ w) * (y-w)⁻¹) :=
    hn.mono (fun y hy => slopeFill_of_ne φ w hy)
 have h0 : z-w ≠ 0 := sub_ne_zero.mpr hne
 have hdiff : DifferentiableAt ℂ (fun y => (φ y - φ w) * (y-w)⁻¹) z :=
    (hz.sub (differentiableAt_const (c:=φ w))).mul
      ((differentiableAt_id.sub (differentiableAt_const (c:=w))).inv (by exact h0))
 exact hdiff.congr_of_eventuallyEq hev
end WL.Planar
namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
lemma rect_eq_cell {s : ℝ} (hs : 0 ≤ s) (i : ℤ×ℤ) :
    ([[lo s i.1, hi s i.1]] ×ℂ [[lo s i.2, hi s i.2]]) = cell s i := by
 ext z
 simp [cell, Complex.mem_reProdIm, uIcc_of_le (lo_le_hi hs _)]
lemma box_cell_slope_zero {s : ℝ} (hs : 0 ≤ s) {φ : ℂ → ℂ} {w : ℂ} {U : Set ℂ}
 (hφ : AnalyticOnNhd ℂ φ U) {i : ℤ×ℤ}
 (hc : cell s i ⊆ U) (hw : w ∈ U) :
 box (lo s i.1) (hi s i.1) (lo s i.2) (hi s i.2)
     (slopeFill φ w) = 0 := by
 apply box_eq_zero_off _ _ _ _ _ {w} (Set.countable_singleton w)
 · --continuous
   rw [rect_eq_cell hs i]
   apply continuousOn_slopeFill
   · exact (hφ w hw).differentiableAt
   · intro z hz
     exact (hφ z (hc hz)).continuousAt.continuousWithinAt
 · intro z hz
   have hzne : z ≠ w := by simpa using hz.2
   apply diff_slopeFill_off hzne
   apply (hφ z (hc ?_)).differentiableAt
   -- interior subset cell
   apply (mem_cell_iff ..).2
   rcases hz.1 with ⟨hzr,hzi⟩
   have hre := hzr
   have him := hzi
   simp [min_eq_left (lo_le_hi hs _), max_eq_right (lo_le_hi hs _)] at hre him
   exact ⟨le_of_lt hre.1, le_of_lt hre.2, le_of_lt him.1, le_of_lt him.2⟩
end WL.Planar


namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
lemma box_cell_kernel_zero {s : ℝ} (hs : 0 ≤ s) {φ : ℂ → ℂ} {w : ℂ}
 {U : Set ℂ} (hφ : AnalyticOnNhd ℂ φ U) {i : ℤ×ℤ}
 (hcell : cell s i ⊆ U) (hw : w ∉ cell s i) :
 box (lo s i.1) (hi s i.1) (lo s i.2) (hi s i.2)
   (fun z => φ z * (z-w)⁻¹) = 0 := by
 apply box_eq_zero_off _ _ _ _ _ (∅ : Set ℂ) Set.countable_empty
 · rw [rect_eq_cell hs i]
   have hne : ∀ z ∈ cell s i, z - w ≠ 0 := by
    intro z hz he
    exact hw (sub_eq_zero.mp he ▸ hz)
   exact ((hφ.continuousOn.mono hcell)).mul
    ((continuousOn_id.sub continuousOn_const).inv₀ hne)
 · intro z hz
   have hzcell : z ∈ cell s i := by
     apply (mem_cell_iff ..).2
     rcases hz.1 with ⟨hre,him⟩
     simp [min_eq_left (lo_le_hi hs _), max_eq_right (lo_le_hi hs _)] at hre him
     exact ⟨le_of_lt hre.1, le_of_lt hre.2, le_of_lt him.1, le_of_lt him.2⟩
   have hne : z - w ≠ 0 := by
     intro he
     exact hw (sub_eq_zero.mp he ▸ hzcell)
   exact ((hφ z (hcell hzcell)).differentiableAt).mul
    ((differentiableAt_id.sub (differentiableAt_const (c:=w))).inv hne)
end WL.Planar

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Grid.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Algebra.lean
noncomputable section
open Set
open scoped ENNReal lp ComplexConjugate Real BigOperators
namespace WL

/-- Point masses in the Laurent group algebra. -/
def pt (n : ℤ) (z : ℂ) : L1 := lp.single (1:ℝ≥0∞) n z
abbrev u (n : ℤ) : L1 := pt n 1
@[simp] lemma pt_apply (n k : ℤ) (z : ℂ) : pt n z k = (Pi.single n z : ℤ → ℂ) k := rfl
lemma norm_pt (n : ℤ) (z : ℂ) : ‖pt n z‖ = ‖z‖ := by
  exact lp.norm_single (by norm_num : (0:ℝ≥0∞) < 1) _ _

@[simp] lemma synth_zero {T : ℝ} [Fact (0 < T)] : synth (T:=T) (0:L1) = 0 := by
  change (∑' n : ℤ, (0:ℂ) • fourier (T:=T) n) = 0
  simp
lemma synth_add' {T : ℝ} [Fact (0 < T)] (a b : L1) :
    synth (T:=T) (a+b) = synth (T:=T) a + synth (T:=T) b := by
  have h := (hasSum_synth (T:=T) a).add (hasSum_synth (T:=T) b)
  have h' : HasSum (fun n : ℤ => (a+b) n • fourier (T:=T) n)
      (synth (T:=T) a + synth (T:=T) b) := by
    convert h using 1
    ext n x
    simp [add_smul]
  exact (hasSum_synth (T:=T) (a+b)).unique h'
lemma synth_smul' {T : ℝ} [Fact (0 < T)] (c : ℂ) (a : L1) :
    synth (T:=T) (c • a) = c • synth (T:=T) a := by
  have h := (hasSum_synth (T:=T) a).const_smul c
  have h' : HasSum (fun n : ℤ => (c • a) n • fourier (T:=T) n)
      (c • synth (T:=T) a) := by
    convert h using 1
    ext n x
    simp [smul_smul]
  exact (hasSum_synth (T:=T) (c • a)).unique h'
lemma synth_neg' {T : ℝ} [Fact (0 < T)] (a : L1) :
    synth (T:=T) (-a) = - synth (T:=T) a := by
  simpa using (synth_smul' (T:=T) (-1) a)
@[simp] lemma synth_pt {T : ℝ} [Fact (0 < T)] (n : ℤ) (z : ℂ) :
    synth (T:=T) (pt n z) = z • fourier (T:=T) n := by
  change (∑' k : ℤ, ((Pi.single n z : ℤ → ℂ) k) • fourier (T:=T) k) = _
  classical
  rw [tsum_eq_single n]
  · simp [Pi.single_apply]
  · intro b hb
    simp [Pi.single_apply, hb]

-- Pointwise multiplication on coefficients will be convolution.
instance : Mul L1 := ⟨conv⟩
instance : One L1 := ⟨pt 0 1⟩
@[simp] lemma mul_def (a b : L1) : a * b = conv a b := rfl
@[simp] lemma one_def : (1:L1) = pt 0 1 := rfl

@[simp] lemma synth_mul {T : ℝ} [Fact (0 < T)] (a b : L1) :
    synth (T:=T) (a*b) = synth (T:=T) a * synth (T:=T) b := synth_conv a b
@[simp] lemma synth_one {T : ℝ} [Fact (0 < T)] : synth (T:=T) (1:L1) = 1 := by
  rw [one_def, synth_pt]
  ext x
  simp

-- algebra laws via synthesis

instance : CommRing L1 := by
  letI fact1 : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
  refine { mul_assoc := ?_
           one_mul := ?_
           mul_one := ?_
           zero_mul := ?_
           mul_zero := ?_
           left_distrib := ?_
           right_distrib := ?_
           mul_comm := ?_ }
  · intro a b c
    apply synth_injective (T:=(1:ℝ))
    simp [mul_def, synth_conv, mul_assoc]
  · intro a
    apply synth_injective (T:=(1:ℝ))
    rw [mul_def, synth_conv, synth_one]
    exact one_mul _
  · intro a
    apply synth_injective (T:=(1:ℝ))
    rw [mul_def, synth_conv, synth_one]
    exact mul_one _
  · intro a
    apply synth_injective (T:=(1:ℝ))
    rw [mul_def, synth_conv, synth_zero]
    exact zero_mul _
  · intro a
    apply synth_injective (T:=(1:ℝ))
    rw [mul_def, synth_conv, synth_zero]
    exact mul_zero _
  · intro a b c
    apply synth_injective (T:=(1:ℝ))
    simp [mul_def, synth_conv, synth_add', mul_add]
  · intro a b c
    apply synth_injective (T:=(1:ℝ))
    simp [mul_def, synth_conv, synth_add', add_mul]
  · intro a b
    apply synth_injective (T:=(1:ℝ))
    rw [mul_def, mul_def, synth_conv, synth_conv]
    exact mul_comm _ _

-- compatibility simp forms retain the original additive structure
@[simp] lemma synth_add {T : ℝ} [Fact (0 < T)] (a b : L1) :
  synth (T:=T) (a+b) = synth (T:=T) a + synth (T:=T) b := synth_add' a b
@[simp] lemma synth_smul {T : ℝ} [Fact (0 < T)] (z:ℂ) (a:L1) :
  synth (T:=T) (z • a) = z • synth (T:=T) a := synth_smul' z a

lemma pt_mul_pt (m n : ℤ) (z w : ℂ) : pt m z * pt n w = pt (m+n) (z*w) := by
  letI : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
  apply synth_injective (T:=(1:ℝ))
  rw [synth_mul, synth_pt, synth_pt, synth_pt]
  ext x
  change z * (fourier (T:=(1:ℝ)) m x) * (w * (fourier (T:=(1:ℝ)) n x)) =
    (z*w) * (fourier (T:=(1:ℝ)) (m+n) x)
  rw [fourier_add]
  ring

lemma pt_smul (n:ℤ) (z:ℂ) : pt n z = z • (u n) := by
  ext k
  classical
  by_cases h : n = k
  · subst k; simp [pt, u]
  · simp [pt, u, Pi.single_apply, h]

@[simp] lemma u_mul (m n : ℤ) : u m * u n = u (m+n) := by
  simpa using pt_mul_pt m n 1 1
@[simp] lemma norm_u (n : ℤ) : ‖u n‖ = 1 := by simp [u, norm_pt]

-- The Banach algebra instances, with the usual `ℓ¹` norm.
instance : SeminormedRing L1 where
  __ : Ring L1 := inferInstance
  __ : SeminormedAddCommGroup L1 := inferInstance
  norm_mul_le a b := by exact norm_conv_le a b
instance : NormedRing L1 where
  __ : NormedAddCommGroup L1 := inferInstance
  __ : SeminormedRing L1 := inferInstance
instance : NormedCommRing L1 where
  __ : NormedRing L1 := inferInstance
  __ : CommRing L1 := inferInstance

/-- Scalars sit at coefficient zero. -/
@[simp] lemma pt_zero_add (z w : ℂ) : pt 0 (z+w) = pt 0 z + pt 0 w := by
  ext k
  classical
  by_cases h : (0:ℤ) = k
  · subst k; simp [pt]
  · simp [pt, Pi.single_eq_of_ne h]
@[simp] lemma pt_zero_neg (z : ℂ) : pt 0 (-z) = -(pt 0 z) := by
  ext k
  classical
  by_cases h : (0:ℤ) = k
  · subst k; simp [pt]
  · simp [pt, Pi.single_eq_of_ne h]
@[simp] lemma pt_zero_mul (z w : ℂ) : pt 0 (z*w) = pt 0 z * pt 0 w := by
  simpa using (pt_mul_pt (0:ℤ) 0 z w).symm
  -- orientation of `pt_mul_pt`

/-- The inherited coordinatewise scalar action is multiplication by the point
mass at zero. -/
lemma pt_zero_mul' (z : ℂ) (a : L1) : pt 0 z * a = z • a := by
  letI : Fact (0 < (1:ℝ)) := ⟨by norm_num⟩
  apply synth_injective (T:=(1:ℝ))
  rw [synth_mul, synth_pt, synth_smul]
  ext x
  simp [fourier_zero]

instance : Algebra ℂ L1 where
  algebraMap :=
    { toFun := fun z => pt 0 z
      map_one' := by rfl
      map_mul' := by intro z w; simpa using (pt_mul_pt (0:ℤ) 0 z w)
      map_zero' := by
        ext k
        classical
        simp [pt, Pi.single_apply]
      map_add' := pt_zero_add }
  commutes' z a := by
    -- commutativity of convolution
    exact mul_comm _ _
  smul_def' z a := (pt_zero_mul' z a).symm

instance : NormedAlgebra ℂ L1 where
  norm_smul_le := by
    intro z a
    exact le_of_eq (norm_smul z a)

/-- Every coefficient vector is the norm-convergent sum of its point masses. -/
lemma summable_pt (a : L1) : Summable (fun n : ℤ => pt n (a n)) := by
  apply Summable.of_norm
  simpa [norm_pt] using summable_norm a
lemma hasSum_pt (a : L1) : HasSum (fun n : ℤ => pt n (a n)) a := by
  have h := (summable_pt a).hasSum
  have vals : (∑' n : ℤ, pt n (a n)) = a := by
    apply lp.ext
    funext k
    let ev : L1 →L[ℂ] ℂ := lp.evalCLM ℂ (fun _ : ℤ => ℂ) (1:ℝ≥0∞) k
    have he := ev.hasSum h
    have he' : HasSum (fun n : ℤ => (if k = n then a k else 0))
          (ev (∑' n : ℤ, pt n (a n))) := by
      convert he using 1
      ext n
      classical
      by_cases hn : k = n
      · subst n; simp [ev, pt, lp.evalCLM, lp.evalₗ]
      · have hn' : n ≠ k := Ne.symm hn
        simp [ev, pt, lp.evalCLM, lp.evalₗ, Pi.single_apply, hn, hn']
    classical
    have hs : HasSum (fun n : ℤ => (if k = n then a k else 0)) (a k) :=
      hasSum_ite_eq' k (a k)
    have eq := hs.unique he'
    -- evaluation is the kth coordinate
    simpa [ev, lp.evalCLM, lp.evalₗ] using eq.symm
  simpa [vals] using h

end WL

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Algebra.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Residue.lean
noncomputable section
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
namespace WL.Planar

/-- translate the elementary square computation to a square with real centre `(a,b)`. -/
lemma box_inv_center (a b r : ℝ) (hr : 0 < r) :
    box (a-r) (a+r) (b-r) (b+r)
      (fun z : ℂ => (z - ((a:ℂ) + (b:ℂ)*Complex.I))⁻¹) =
        (2 * (Real.pi:ℂ) * Complex.I) := by
  let Q : ℂ → ℂ := fun z => (z - ((a:ℂ) + (b:ℂ)*Complex.I))⁻¹
  let P : ℂ → ℂ := fun z => z⁻¹
  -- the four one-dimensional translates
  have hor (v : ℝ) :
      (∫ x : ℝ in a-r..a+r, Q ((x:ℂ) + ((b+v:ℝ):ℂ)*Complex.I)) =
        ∫ x : ℝ in -r..r, P ((x:ℂ) + (v:ℂ)*Complex.I) := by
    let f : ℝ → ℂ := fun x => P ((x:ℂ) + (v:ℂ)*Complex.I)
    have heq2 (y : ℝ) :
        Q ((y:ℂ) + ((b+v:ℝ):ℂ)*Complex.I) = f (y-a) := by
      dsimp [f,P,Q]
      push_cast
      congr 1
      ring
    have htrans : (∫ y : ℝ in a-r..a+r,
          Q ((y:ℂ) + ((b+v:ℝ):ℂ)*Complex.I)) =
        ∫ y : ℝ in a-r..a+r, f (y-a) :=
      intervalIntegral.integral_congr (fun y _ => heq2 y)
    -- direct `integral_comp_sub_right`
    have hs := intervalIntegral.integral_comp_sub_right (a:=a-r) (b:=a+r) f a
    rw [show a-r - a = -r by ring, show a+r - a = r by ring] at hs
    rw [htrans]
    exact hs
  have ver (u : ℝ) :
      (∫ y : ℝ in b-r..b+r, Q (((a+u:ℝ):ℂ) + (y:ℂ)*Complex.I)) =
        ∫ y : ℝ in -r..r, P ((u:ℂ) + (y:ℂ)*Complex.I) := by
    let f : ℝ → ℂ := fun y => P ((u:ℂ) + (y:ℂ)*Complex.I)
    have heq (y : ℝ) :
        Q (((a+u:ℝ):ℂ) + (y:ℂ)*Complex.I) = f (y-b) := by
      dsimp [f,P,Q]
      push_cast
      congr 1
      ring
    have htrans : (∫ y : ℝ in b-r..b+r,
        Q (((a+u:ℝ):ℂ) + (y:ℂ)*Complex.I)) =
       ∫ y : ℝ in b-r..b+r, f (y-b) :=
      intervalIntegral.integral_congr (fun y _ => heq y)
    have hs := intervalIntegral.integral_comp_sub_right (a:=b-r) (b:=b+r) f b
    rw [show b-r - b = -r by ring, show b+r - b = r by ring] at hs
    rw [htrans]
    exact hs
  have horB := hor (-r)
  have horT := hor r
  have verR := ver r
  have verL := ver (-r)
  -- expand the box, the four translated integrals above are exactly its sides.
  change box (a-r) (a+r) (b-r) (b+r) Q = _
  simp only [box]
  change _ = _ at horB horT verR verL
  simp only [sub_eq_add_neg] at horB horT verR verL ⊢
  rw [horB, horT, verR, verL]
  simpa [box, P, sub_eq_add_neg] using (box_inv_square r hr)

end WL.Planar
namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
lemma box_inv_zero_of_not_mem (l r b t : ℝ) (w : ℂ)
 (hw : w ∉ ([[l,r]] ×ℂ [[b,t]])) :
 box l r b t (fun z : ℂ => (z-w)⁻¹) = 0 := by
 apply box_eq_zero_of_differentiableOn
 intro z hz
 have hn : z - w ≠ 0 := by
   intro h
   have : z = w := sub_eq_zero.mp h
   exact hw (this ▸ hz)
 exact ((differentiableAt_id.sub (differentiableAt_const (c:=w))).inv hn).differentiableWithinAt

lemma box_inv_shift_residue (l r b t : ℝ) (w : ℂ)
 (hl : l < w.re) (hr : w.re < r) (hb : b < w.im) (ht : w.im < t) :
 box l r b t (fun z : ℂ => (z-w)⁻¹) =
       (2 * (Real.pi:ℂ) * Complex.I) := by
 let a : ℝ := w.re
 let d : ℝ := w.im
 -- choose a smaller centred square.
 let ρ : ℝ := min (min (a-l) (r-a)) (min (d-b) (t-d)) / 2
 have hρ : 0 < ρ := by
   dsimp [ρ,a,d]
   have h1 : 0 < w.re - l := sub_pos.mpr hl
   have h2 : 0 < r - w.re := sub_pos.mpr hr
   have h3 : 0 < w.im - b := sub_pos.mpr hb
   have h4 : 0 < t - w.im := sub_pos.mpr ht
   exact half_pos (lt_min (lt_min h1 h2) (lt_min h3 h4))
 have hxL : l < a-ρ := by
   dsimp [ρ]
   have hh : min (min (a-l) (r-a)) (min (d-b) (t-d)) ≤ a-l :=
     le_trans (min_le_left _ _) (min_le_left _ _)
   linarith
 have hxR : a+ρ < r := by
   dsimp [ρ]
   have hh : min (min (a-l) (r-a)) (min (d-b) (t-d)) ≤ r-a :=
     le_trans (min_le_left _ _) (min_le_right _ _)
   linarith
 have hyB : b < d-ρ := by
   dsimp [ρ]
   have hh : min (min (a-l) (r-a)) (min (d-b) (t-d)) ≤ d-b :=
     le_trans (min_le_right _ _) (min_le_left _ _)
   linarith
 have hyT : d+ρ < t := by
   dsimp [ρ]
   have hh : min (min (a-l) (r-a)) (min (d-b) (t-d)) ≤ t-d :=
     le_trans (min_le_right _ _) (min_le_right _ _)
   linarith
 have wa : w = ((a:ℝ):ℂ) + (d:ℝ)*Complex.I := by
   dsimp [a,d]
   exact (Complex.re_add_im w).symm
 let q : ℂ → ℂ := fun z => (z-w)⁻¹
 -- continuity/integrability on horizontal or vertical lines missing the pole
 have intH (y α β : ℝ) (hy : y ≠ d) :
     IntervalIntegrable (fun x : ℝ => q ((x:ℂ)+(y:ℂ)*Complex.I)) volume α β := by
   have hnon : ∀ x : ℝ, ( (x:ℂ)+(y:ℂ)*Complex.I - w) ≠ 0 := by
     intro x h
     have he := congrArg Complex.im h
     dsimp [d] at hy
     rw [Complex.sub_im, Complex.add_im, Complex.mul_im] at he
     -- simp clears real casts
     simp at he
     -- he : y - w.im = 0
     exact hy (by linarith)
   have hc : Continuous (fun x : ℝ => q ((x:ℂ)+(y:ℂ)*Complex.I)) := by
     dsimp [q]
     fun_prop (disch := (aesop))
   exact hc.intervalIntegrable _ _
 have intV (x α β : ℝ) (hx : x ≠ a) :
     IntervalIntegrable (fun y : ℝ => q ((x:ℂ)+(y:ℂ)*Complex.I)) volume α β := by
   have hnon : ∀ y : ℝ, ((x:ℂ)+(y:ℂ)*Complex.I - w) ≠ 0 := by
     intro y h
     have he := congrArg Complex.re h
     dsimp [a] at hx
     rw [Complex.sub_re, Complex.add_re, Complex.mul_re] at he
     simp at he
     exact hx (by linarith)
   have hc : Continuous (fun y : ℝ => q ((x:ℂ)+(y:ℂ)*Complex.I)) := by
     dsimp [q]
     fun_prop (disch := (aesop))
   exact hc.intervalIntegrable _ _
 -- rectangles wholly to one side vanish
 have zeroLeft : box l (a-ρ) b t q = 0 := by
   apply box_inv_zero_of_not_mem l (a-ρ) b t w
   intro hw'
   have hh : w.re ∈ Set.uIcc l (a-ρ) := (Complex.mem_reProdIm.1 hw').1
   simp [uIcc_of_le (le_of_lt hxL)] at hh
   dsimp [a] at hxL
   linarith
 have zeroRight : box (a+ρ) r b t q = 0 := by
   apply box_inv_zero_of_not_mem (a+ρ) r b t w
   intro hw'
   have hh : w.re ∈ Set.uIcc (a+ρ) r := (Complex.mem_reProdIm.1 hw').1
   simp [uIcc_of_le (le_of_lt hxR)] at hh
   dsimp [a] at hxR
   linarith
 have zeroBot : box (a-ρ) (a+ρ) b (d-ρ) q = 0 := by
   apply box_inv_zero_of_not_mem (a-ρ) (a+ρ) b (d-ρ) w
   intro hw'
   have hh : w.im ∈ Set.uIcc b (d-ρ) := (Complex.mem_reProdIm.1 hw').2
   simp [uIcc_of_le (le_of_lt hyB)] at hh
   dsimp [d] at hyB
   linarith
 have zeroTop : box (a-ρ) (a+ρ) (d+ρ) t q = 0 := by
   apply box_inv_zero_of_not_mem (a-ρ) (a+ρ) (d+ρ) t w
   intro hw'
   have hh : w.im ∈ Set.uIcc (d+ρ) t := (Complex.mem_reProdIm.1 hw').2
   simp [uIcc_of_le (le_of_lt hyT)] at hh
   dsimp [d] at hyT
   linarith
 -- cut at the four safe lines.
 have split1 := box_split_vertical' l (a-ρ) r b t q
    (intH b l (a-ρ) (by dsimp [d]; linarith))
    (intH b (a-ρ) r (by dsimp [d]; linarith))
    (intH t l (a-ρ) (by dsimp [d]; linarith))
    (intH t (a-ρ) r (by dsimp [d]; linarith))
 have split2 := box_split_vertical' (a-ρ) (a+ρ) r b t q
    (intH b (a-ρ) (a+ρ) (by dsimp [d]; linarith))
    (intH b (a+ρ) r (by dsimp [d]; linarith))
    (intH t (a-ρ) (a+ρ) (by dsimp [d]; linarith))
    (intH t (a+ρ) r (by dsimp [d]; linarith))
 have splity1 := box_split_horizontal' (a-ρ) (a+ρ) b (d-ρ) t q
    (by
      -- right line x=a+ρ
      -- the expressions in the lemma use coerced r + yI
      simpa using (intV (a+ρ) b (d-ρ) (by linarith : a+ρ ≠ a)))
    (by simpa using (intV (a+ρ) (d-ρ) t (by linarith : a+ρ ≠ a)))
    (by simpa using (intV (a-ρ) b (d-ρ) (by linarith : a-ρ ≠ a)))
    (by simpa using (intV (a-ρ) (d-ρ) t (by linarith : a-ρ ≠ a)))
 have splity2 := box_split_horizontal' (a-ρ) (a+ρ) (d-ρ) (d+ρ) t q
    (by simpa using (intV (a+ρ) (d-ρ) (d+ρ) (by linarith : a+ρ ≠ a)))
    (by simpa using (intV (a+ρ) (d+ρ) t (by linarith : a+ρ ≠ a)))
    (by simpa using (intV (a-ρ) (d-ρ) (d+ρ) (by linarith : a-ρ ≠ a)))
    (by simpa using (intV (a-ρ) (d+ρ) t (by linarith : a-ρ ≠ a)))
 have center : box (a-ρ) (a+ρ) (d-ρ) (d+ρ) q =
       (2 * (Real.pi:ℂ) * Complex.I) := by
   dsimp [q]
   rw [wa]
   exact box_inv_center a d ρ hρ
 linear_combination split1.symm + split2.symm + splity1.symm + splity2.symm +
    center + zeroLeft + zeroRight + zeroBot + zeroTop
end WL.Planar
namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
/-- a coordinate not on a grid line belongs to just its floor interval. -/
lemma coord_eq_own {s : ℝ} (hs : 0 < s) {x : ℝ}
 (hx : ∀ m : ℤ, x ≠ lo s m) {k : ℤ}
 (A : lo s k ≤ x) (B : x ≤ hi s k) : k = ix s x := by
 -- use the two-dimensional uniqueness lemma with arbitrary height coordinate
 let z : ℂ := (x:ℂ)
 have hz : z.re = x := by simp [z]
 -- a direct separation of intervals
 have C := coord_strict hs hx
 by_contra ne
 rcases lt_or_gt_of_ne ne with hlt | hgt
 · have hle : k + 1 ≤ ix s x := by omega
   have hmono : lo s (k+1) ≤ lo s (ix s x) := by
      dsimp [lo]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hs)
   have hh' : hi s k ≤ lo s (ix s x) := by simpa [hi_eq_lo_succ] using hmono
   linarith
 · have hle : ix s x + 1 ≤ k := by omega
   have hmono : lo s (ix s x + 1) ≤ lo s k := by
      dsimp [lo]
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hle) (le_of_lt hs)
   have hh' : hi s (ix s x) ≤ lo s k := by simpa [hi_eq_lo_succ] using hmono
   linarith

lemma coord_eq_line {s : ℝ} (hs : 0 < s) {x : ℝ} (m k : ℤ)
 (hx : x = lo s m) (A : lo s k ≤ x) (B : x ≤ hi s k) :
 k = m ∨ k = m-1 := by
 have h1 : (k:ℝ) ≤ m := by
   dsimp [lo] at A hx
   have : (k:ℝ)*s ≤ (m:ℝ)*s := by linarith
   exact le_of_mul_le_mul_right this hs
 have h2 : (m:ℝ) ≤ k+1 := by
   dsimp [lo,hi] at B hx
   have : (m:ℝ)*s ≤ ((k:ℝ)+1)*s := by
     push_cast
     linarith
   exact le_of_mul_le_mul_right this hs
 have h1' : k ≤ m := by exact_mod_cast h1
 have h2' : m ≤ k+1 := by exact_mod_cast h2
 omega

end WL.Planar
namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
lemma int_kernel_H (w : ℂ) (y α β : ℝ) (hy : y ≠ w.im) :
 IntervalIntegrable (fun x : ℝ => (((x:ℂ)+(y:ℂ)*Complex.I)-w)⁻¹) volume α β := by
 have hnon : ∀ x : ℝ, (((x:ℂ)+(y:ℂ)*Complex.I)-w) ≠ 0 := by
   intro x h
   have he := congrArg Complex.im h
   rw [Complex.sub_im, Complex.add_im, Complex.mul_im] at he
   simp at he
   exact hy (by linarith)
 have hc : Continuous (fun x : ℝ => (((x:ℂ)+(y:ℂ)*Complex.I)-w)⁻¹) := by
   fun_prop (disch := (aesop))
 exact hc.intervalIntegrable _ _
lemma int_kernel_V (w : ℂ) (x α β : ℝ) (hx : x ≠ w.re) :
 IntervalIntegrable (fun y : ℝ => (((x:ℂ)+(y:ℂ)*Complex.I)-w)⁻¹) volume α β := by
 have hnon : ∀ y : ℝ, (((x:ℂ)+(y:ℂ)*Complex.I)-w) ≠ 0 := by
   intro y h
   have he := congrArg Complex.re h
   rw [Complex.sub_re, Complex.add_re, Complex.mul_re] at he
   simp at he
   exact hx (by linarith)
 have hc : Continuous (fun y : ℝ => (((x:ℂ)+(y:ℂ)*Complex.I)-w)⁻¹) := by
   fun_prop (disch := (aesop))
 exact hc.intervalIntegrable _ _

/-- four rectangles at a crossing.  Only the outer lines must be integrable;
the possibly singular inner lines cancel before any splitting. -/
lemma box_four (l u r b v t : ℝ) (q : ℂ → ℂ)
 (hb1 : IntervalIntegrable (fun x : ℝ => q (x + b*Complex.I)) volume l u)
 (hb2 : IntervalIntegrable (fun x : ℝ => q (x + b*Complex.I)) volume u r)
 (ht1 : IntervalIntegrable (fun x : ℝ => q (x + t*Complex.I)) volume l u)
 (ht2 : IntervalIntegrable (fun x : ℝ => q (x + t*Complex.I)) volume u r)
 (hl1 : IntervalIntegrable (fun y : ℝ => q (l + y*Complex.I)) volume b v)
 (hl2 : IntervalIntegrable (fun y : ℝ => q (l + y*Complex.I)) volume v t)
 (hr1 : IntervalIntegrable (fun y : ℝ => q (r + y*Complex.I)) volume b v)
 (hr2 : IntervalIntegrable (fun y : ℝ => q (r + y*Complex.I)) volume v t) :
 box l u b v q + box u r b v q + box l u v t q + box u r v t q =
 box l r b t q := by
 have B := intervalIntegral.integral_add_adjacent_intervals hb1 hb2
 have T := intervalIntegral.integral_add_adjacent_intervals ht1 ht2
 have L := intervalIntegral.integral_add_adjacent_intervals hl1 hl2
 have R := intervalIntegral.integral_add_adjacent_intervals hr1 hr2
 simp only [box]
 rw [← B, ← T, ← L, ← R]
 ring
end WL.Planar
namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
open scoped Classical
/-- the kernel has winding one about every point of the selected compact set,
even on a grid line (where four neighbouring boxes are combined before
splitting). -/
lemma sum_boxes_kernel {s : ℝ} (hs : 0 < s) {K : Set ℂ} (S : Finset (ℤ×ℤ))
 (hS : ∀ i : ℤ×ℤ, i ∈ S ↔ (cell s i ∩ K).Nonempty)
 {w : ℂ} (hwK : w ∈ K) :
 (∑ i ∈ S, box (lo s i.1) (hi s i.1) (lo s i.2) (hi s i.2)
      (fun z : ℂ => (z-w)⁻¹)) = (2*(Real.pi:ℂ)*Complex.I) := by
 classical
 let Q (i : ℤ×ℤ) : ℂ := box (lo s i.1) (hi s i.1) (lo s i.2) (hi s i.2)
      (fun z : ℂ => (z-w)⁻¹)
 have zmem (i : ℤ×ℤ) (hiw : w ∈ cell s i) : i ∈ S :=
   (hS i).2 ⟨w, hiw, hwK⟩
 have zero (i : ℤ×ℤ) (hn : w ∉ cell s i) : Q i = 0 := by
   apply box_inv_zero_of_not_mem _ _ _ _ w
   simpa [rect_eq_cell (le_of_lt hs) i] using hn
 -- the sum may be restricted to any list which is exactly the cells through w
 have restrict (L : Finset (ℤ×ℤ))
    (hsub : ∀ i, i ∈ L → w ∈ cell s i)
    (hall : ∀ i, w ∈ cell s i → i ∈ L) :
      (∑ i ∈ S, Q i) = ∑ i ∈ L, Q i := by
   symm
   apply Finset.sum_subset
   · intro i hi
     exact zmem i (hsub i hi)
   · intro i hiS hiL
     apply zero
     intro h
     exact hiL (hall i h)
 by_cases hx : ∃ m : ℤ, w.re = lo s m
 · obtain ⟨m, hm⟩ := hx
   by_cases hy : ∃ n : ℤ, w.im = lo s n
   · obtain ⟨n, hn⟩ := hy
     let A : ℤ×ℤ := (m-1,n-1)
     let B : ℤ×ℤ := (m,n-1)
     let C : ℤ×ℤ := (m-1,n)
     let D : ℤ×ℤ := (m,n)
     let L : Finset (ℤ×ℤ) := {A,B,C,D}
     have hiff (i : ℤ×ℤ) : w ∈ cell s i ↔ i = A ∨ i = B ∨ i = C ∨ i = D := by
       have coord := mem_cell_iff s i w
       constructor
       · intro hi'
         have aa := coord.1 hi'
         have ex := coord_eq_line hs m i.1 hm aa.1 aa.2.1
         have ey := coord_eq_line hs n i.2 hn aa.2.2.1 aa.2.2.2
         rcases ex with ex|ex <;> rcases ey with ey|ey
         · exact Or.inr (Or.inr (Or.inr (by
                show i = D
                dsimp [D]
                exact Prod.ext ex ey)))
         · exact Or.inr (Or.inl (by
                show i = B
                dsimp [B]
                exact Prod.ext ex ey))
         · exact Or.inr (Or.inr (Or.inl (by
                show i = C
                dsimp [C]
                exact Prod.ext ex ey)))
         · exact Or.inl (by
                show i = A
                dsimp [A]
                exact Prod.ext ex ey)
       · intro hi'
         apply coord.2
         rcases hi' with h|h|h|h <;> subst i
         · dsimp [A]
           have hix : hi s (m-1) = lo s m := by
             calc
               hi s (m-1) = lo s ((m-1)+1) := hi_eq_lo_succ s (m-1)
               _ = lo s m := by congr 1 <;> omega
           have hiy : hi s (n-1) = lo s n := by
             calc
               hi s (n-1) = lo s ((n-1)+1) := hi_eq_lo_succ s (n-1)
               _ = lo s n := by congr 1 <;> omega
           rw [hm, hn] -- rw direction? hm : w.re = ...
           exact ⟨by dsimp [lo]; push_cast; nlinarith,
             le_of_eq hix.symm, by dsimp [lo]; push_cast; nlinarith,
             le_of_eq hiy.symm⟩
         · dsimp [B]
           have hiy : hi s (n-1) = lo s n := by
             calc
               hi s (n-1) = lo s ((n-1)+1) := hi_eq_lo_succ s (n-1)
               _ = lo s n := by congr 1 <;> omega
           rw [hm, hn]
           exact ⟨le_rfl, lo_le_hi (le_of_lt hs) _,
             by dsimp [lo]; push_cast; nlinarith, le_of_eq hiy.symm⟩
         · dsimp [C]
           have hix : hi s (m-1) = lo s m := by
             calc
               hi s (m-1) = lo s ((m-1)+1) := hi_eq_lo_succ s (m-1)
               _ = lo s m := by congr 1 <;> omega
           rw [hm, hn]
           exact ⟨by dsimp [lo]; push_cast; nlinarith, le_of_eq hix.symm,
             le_rfl, lo_le_hi (le_of_lt hs) _⟩
         · dsimp [D]
           rw [hm,hn]
           exact ⟨le_rfl, lo_le_hi (le_of_lt hs) _, le_rfl,
             lo_le_hi (le_of_lt hs) _⟩
     have sumL : (∑ i ∈ S, Q i) = Q A + Q B + Q C + Q D := by
       rw [restrict L (fun i hi => (hiff i).2 (by simpa [L] using hi))
         (fun i hi => (by simpa [L] using (hiff i).1 hi))]
       -- four different pairs
       have hAB : A ≠ B := by intro e; have := congrArg Prod.fst e; dsimp [A,B] at this; omega
       have hAC : A ≠ C := by intro e; have := congrArg Prod.snd e; dsimp [A,C] at this; omega
       have hAD : A ≠ D := by intro e; have := congrArg Prod.fst e; dsimp [A,D] at this; omega
       have hBC : B ≠ C := by intro e; have := congrArg Prod.fst e; dsimp [B,C] at this; omega
       have hBD : B ≠ D := by intro e; have := congrArg Prod.snd e; dsimp [B,D] at this; omega
       have hCD : C ≠ D := by intro e; have := congrArg Prod.fst e; dsimp [C,D] at this; omega
       simp [L, hAB, hAC, hAD, hBC, hBD, hCD]
       ring
     rw [sumL]
     -- put common bounds on the four equations
     have hxcut : hi s (m-1) = lo s m := by
       calc
               hi s (m-1) = lo s ((m-1)+1) := hi_eq_lo_succ s (m-1)
               _ = lo s m := by congr 1 <;> omega
     have hycut : hi s (n-1) = lo s n := by
       calc
               hi s (n-1) = lo s ((n-1)+1) := hi_eq_lo_succ s (n-1)
               _ = lo s n := by congr 1 <;> omega
     let l := lo s (m-1); let u := lo s m; let r := hi s m
     let bot := lo s (n-1); let v := lo s n; let top := hi s n
     have hlw : l < w.re := by dsimp [l,lo] at *; push_cast; nlinarith
     have hrw : w.re < r := by dsimp [r,hi,lo] at *; push_cast; nlinarith
     have hbw : bot < w.im := by dsimp [bot,lo] at *; push_cast; nlinarith
     have htw : w.im < top := by dsimp [top,hi,lo] at *; push_cast; nlinarith
     have combine : Q A + Q B + Q C + Q D =
          box l r bot top (fun z : ℂ => (z-w)⁻¹) := by
       dsimp [Q,A,B,C,D,l,u,r,bot,v,top]
       -- normalize adjacent endpoints
       rw [hxcut, hycut]
       -- outer bounds remain written uniformly after this rewrite
       apply box_four
       · simpa using int_kernel_H w (lo s (n-1)) (lo s (m-1)) (lo s m) (by dsimp [lo] at *; push_cast; nlinarith)
       · simpa using int_kernel_H w (lo s (n-1)) (lo s m) (hi s m) (by dsimp [lo] at *; push_cast; nlinarith)
       · simpa using int_kernel_H w (hi s n) (lo s (m-1)) (lo s m) (by dsimp [hi,lo] at *; push_cast; nlinarith)
       · simpa using int_kernel_H w (hi s n) (lo s m) (hi s m) (by dsimp [hi,lo] at *; push_cast; nlinarith)
       · simpa using int_kernel_V w (lo s (m-1)) (lo s (n-1)) (lo s n) (by dsimp [lo] at *; push_cast; nlinarith)
       · simpa using int_kernel_V w (lo s (m-1)) (lo s n) (hi s n) (by dsimp [lo, hi] at *; push_cast; nlinarith)
       · simpa using int_kernel_V w (hi s m) (lo s (n-1)) (lo s n) (by dsimp [lo, hi] at *; push_cast; nlinarith)
       · simpa using int_kernel_V w (hi s m) (lo s n) (hi s n) (by dsimp [lo, hi] at *; push_cast; nlinarith)
     rw [combine]
     exact box_inv_shift_residue l r bot top w hlw hrw hbw htw
   · -- x on a line, y in one interval
     push_neg at hy
     let j : ℤ := ix s w.im
     let A : ℤ×ℤ := (m-1,j)
     let B : ℤ×ℤ := (m,j)
     have sy := coord_strict hs hy
     have hiff (i:ℤ×ℤ) : w ∈ cell s i ↔ i=A ∨ i=B := by
       have coord := mem_cell_iff s i w
       constructor
       · intro hh
         have aa := coord.1 hh
         rcases coord_eq_line hs m i.1 hm aa.1 aa.2.1 with ex|ex
         · right; exact Prod.ext ex (coord_eq_own hs hy aa.2.2.1 aa.2.2.2)
         · left; exact Prod.ext ex (coord_eq_own hs hy aa.2.2.1 aa.2.2.2)
       · intro h
         apply coord.2
         rcases h with h|h <;> subst i
         · dsimp [A,j]; rw [hm]
           have hcut : hi s (m-1) = lo s m := by calc
               hi s (m-1) = lo s ((m-1)+1) := hi_eq_lo_succ s (m-1)
               _ = lo s m := by congr 1 <;> omega
           exact ⟨by dsimp [lo]; push_cast; nlinarith, le_of_eq hcut.symm,
             (coord_mem hs _).1, (coord_mem hs _).2⟩
         · dsimp [B,j]; rw [hm]
           exact ⟨le_rfl, lo_le_hi (le_of_lt hs) _, (coord_mem hs _).1, (coord_mem hs _).2⟩
     have sumL : (∑ i ∈ S, Q i) = Q A + Q B := by
       rw [restrict {A,B} (fun i hi => (hiff i).2 (by simpa using hi))
          (fun i hi => (by simpa using (hiff i).1 hi))]
       have ne : A ≠ B := by intro e; have := congrArg Prod.fst e; dsimp [A,B] at this; omega
       simp [ne]
     rw [sumL]
     have hcut : hi s (m-1) = lo s m := by calc
               hi s (m-1) = lo s ((m-1)+1) := hi_eq_lo_succ s (m-1)
               _ = lo s m := by congr 1 <;> omega
     let l := lo s (m-1); let r := hi s m; let bot := lo s j; let top := hi s j
     have hlw : l < w.re := by dsimp [l,lo] at *; push_cast; nlinarith
     have hrw : w.re < r := by dsimp [r,hi,lo] at *; push_cast; nlinarith
     have combine : Q A + Q B = box l r bot top (fun z : ℂ => (z-w)⁻¹) := by
       dsimp [Q,A,B,l,r,bot,top]
       rw [hcut]
       exact box_split_vertical' (lo s (m-1)) (lo s m) (hi s m)
          (lo s j) (hi s j) (fun z : ℂ => (z-w)⁻¹)
         (by simpa using int_kernel_H w (lo s j) (lo s (m-1)) (lo s m) (ne_of_lt sy.1))
         (by simpa using int_kernel_H w (lo s j) (lo s m) (hi s m) (ne_of_lt sy.1))
         (by simpa using int_kernel_H w (hi s j) (lo s (m-1)) (lo s m) (ne_of_gt sy.2))
         (by simpa using int_kernel_H w (hi s j) (lo s m) (hi s m) (ne_of_gt sy.2))
     rw [combine]
     exact box_inv_shift_residue l r bot top w hlw hrw sy.1 sy.2
 · push_neg at hx
   by_cases hy : ∃ n : ℤ, w.im = lo s n
   · -- symmetric pair horizontal
     obtain ⟨n, hn⟩ := hy
     let j : ℤ := ix s w.re
     let A : ℤ×ℤ := (j,n-1)
     let B : ℤ×ℤ := (j,n)
     have sx := coord_strict hs hx
     have hiff (i:ℤ×ℤ) : w ∈ cell s i ↔ i=A ∨ i=B := by
       have coord := mem_cell_iff s i w
       constructor
       · intro hh
         have aa := coord.1 hh
         rcases coord_eq_line hs n i.2 hn aa.2.2.1 aa.2.2.2 with ey|ey
         · right; exact Prod.ext (coord_eq_own hs hx aa.1 aa.2.1) ey
         · left; exact Prod.ext (coord_eq_own hs hx aa.1 aa.2.1) ey
       · intro h
         apply coord.2
         rcases h with h|h <;> subst i
         · dsimp [A,j]; rw [hn]
           have hcut : hi s (n-1) = lo s n := by calc
               hi s (n-1) = lo s ((n-1)+1) := hi_eq_lo_succ s (n-1)
               _ = lo s n := by congr 1 <;> omega
           exact ⟨(coord_mem hs _).1, (coord_mem hs _).2,
             by dsimp [lo]; push_cast; nlinarith, le_of_eq hcut.symm⟩
         · dsimp [B,j]; rw [hn]
           exact ⟨(coord_mem hs _).1, (coord_mem hs _).2, le_rfl, lo_le_hi (le_of_lt hs) _⟩
     have sumL : (∑ i ∈ S, Q i) = Q A + Q B := by
       rw [restrict {A,B} (fun i hi => (hiff i).2 (by simpa using hi))
          (fun i hi => (by simpa using (hiff i).1 hi))]
       have ne : A ≠ B := by intro e; have := congrArg Prod.snd e; dsimp [A,B] at this; omega
       simp [ne]
     rw [sumL]
     have hcut : hi s (n-1) = lo s n := by calc
               hi s (n-1) = lo s ((n-1)+1) := hi_eq_lo_succ s (n-1)
               _ = lo s n := by congr 1 <;> omega
     let l := lo s j; let r := hi s j; let bot := lo s (n-1); let top := hi s n
     have hbw : bot < w.im := by dsimp [bot,lo] at *; push_cast; nlinarith
     have htw : w.im < top := by dsimp [top,hi,lo] at *; push_cast; nlinarith
     have combine : Q A + Q B = box l r bot top (fun z : ℂ => (z-w)⁻¹) := by
       dsimp [Q,A,B,l,r,bot,top]
       rw [hcut]
       exact box_split_horizontal' (lo s j) (hi s j) (lo s (n-1)) (lo s n) (hi s n)
          (fun z : ℂ => (z-w)⁻¹)
         (by simpa using int_kernel_V w (hi s j) (lo s (n-1)) (lo s n) (ne_of_gt sx.2))
         (by simpa using int_kernel_V w (hi s j) (lo s n) (hi s n) (ne_of_gt sx.2))
         (by simpa using int_kernel_V w (lo s j) (lo s (n-1)) (lo s n) (ne_of_lt sx.1))
         (by simpa using int_kernel_V w (lo s j) (lo s n) (hi s n) (ne_of_lt sx.1))
     rw [combine]
     exact box_inv_shift_residue l r bot top w sx.1 sx.2 hbw htw
   · push_neg at hy
     let A : ℤ×ℤ := (ix s w.re, ix s w.im)
     have sx := coord_strict hs hx
     have sy := coord_strict hs hy
     have hiff (i:ℤ×ℤ) : w ∈ cell s i ↔ i=A := by
       constructor
       · intro h
         have aa := (mem_cell_iff s i w).1 h
         exact Prod.ext (coord_eq_own hs hx aa.1 aa.2.1)
             (coord_eq_own hs hy aa.2.2.1 aa.2.2.2)
       · intro h; subst i
         exact mem_own_cell hs w
     have sumL : (∑ i ∈ S, Q i) = Q A := by
       rw [Finset.sum_eq_single A (fun i hi ne => zero i (by intro h; exact ne ((hiff i).1 h)))
         (fun h => (h (zmem A ((hiff A).2 rfl))).elim)]
     rw [sumL]
     exact box_inv_shift_residue _ _ _ _ w sx.1 sx.2 sy.1 sy.2
end WL.Planar
namespace WL.Planar
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Real Interval BigOperators Topology
lemma sum_boundary_cauchy {s : ℝ} (hs : 0 < s)
 {K U : Set ℂ} (S : Finset (ℤ×ℤ))
 (hS : ∀ i : ℤ×ℤ, i ∈ S ↔ (cell s i ∩ K).Nonempty)
 (cellU : ∀ i ∈ S, cell s i ⊆ U)
 {φ : ℂ → ℂ} (hφ : AnalyticOnNhd ℂ φ U)
 {w : ℂ} (hwK : w ∈ K) (hwU : w ∈ U) :
 (∑ u ∈ boundary S, edgeInt s u (fun z => φ z * (z-w)⁻¹)) =
   φ w * (2*(Real.pi:ℂ)*Complex.I) := by
 classical
 let k : ℂ → ℂ := fun z => (z-w)⁻¹
 let p : ℂ → ℂ := slopeFill φ w
 have now (u : (ℤ×ℤ)×Side) (hu : u ∈ boundary S) {t : ℝ}
     (ht : t ∈ Set.uIcc (0:ℝ) 1) : path s u t ≠ w := by
   intro e
   have hboth := side_mem_both hs u (by simpa using ht)
   have hnot := (mem_boundary.1 hu).2
   apply hnot
   apply (hS _).2
   refine ⟨w, ?_, hwK⟩
   rw [← e]
   exact hboth.2
 have one (u : (ℤ×ℤ)×Side) (hu : u ∈ boundary S) :
     edgeInt s u (fun z => φ z * (z-w)⁻¹) =
       edgeInt s u p + φ w * edgeInt s u k := by
   -- all three integrands are continuous on the side; the pole is not there.
   have hkcont : ContinuousOn (fun t : ℝ => k (path s u t))
         (Set.uIcc (0:ℝ) 1) := by
     dsimp [k]
     have hbase : Continuous (fun t : ℝ => (path s u t - w)) := by
       exact ( (edge_continuous _ _).sub continuous_const)
     exact (hbase.continuousOn).inv₀ (fun t ht h0 =>
       now u hu ht (sub_eq_zero.mp h0))
   have hpcont : ContinuousOn (fun t : ℝ => p (path s u t))
         (Set.uIcc (0:ℝ) 1) := by
     have hcell : cell s u.1 ⊆ U := cellU _ (mem_boundary.1 hu).1
     have cp : ContinuousOn p (cell s u.1) :=
       continuousOn_slopeFill (hφ w hwU).differentiableAt
         (hφ.continuousOn.mono hcell)
     exact cp.comp (edge_continuous _ _).continuousOn
       (fun t ht => (side_mem_both hs u (by simpa using ht)).1)
   have hvcont : Continuous (vel s u) := edge'_continuous _ _
   have ik : IntervalIntegrable
       (fun t : ℝ => vel s u t * k (path s u t)) volume 0 1 :=
     (hvcont.continuousOn.mul hkcont).intervalIntegrable
   have ip : IntervalIntegrable
       (fun t : ℝ => vel s u t * p (path s u t)) volume 0 1 :=
     (hvcont.continuousOn.mul hpcont).intervalIntegrable
   have ic : IntervalIntegrable
       (fun t : ℝ => (φ w) * (vel s u t * k (path s u t))) volume 0 1 :=
     (ik.const_mul _)
   have hpoint (t : ℝ) (ht : t ∈ Set.uIcc (0:ℝ) 1) :
       vel s u t * (φ (path s u t) * (path s u t - w)⁻¹) =
       vel s u t * p (path s u t) + φ w * (vel s u t * k (path s u t)) := by
     have hn := now u hu ht
     dsimp [p, k]
     rw [slopeFill_of_ne φ w hn]
     field_simp
     <;> ring
   dsimp [edgeInt]
   rw [← intervalIntegral.integral_const_mul]
   rw [← intervalIntegral.integral_add ip ic]
   apply intervalIntegral.integral_congr
   intro t ht
   exact hpoint t (by simpa using ht)

 -- slope boxes vanish
 have hpzero : (∑ u ∈ boundary S, edgeInt s u p) = 0 := by
   rw [sum_edges_boxes]
   apply Finset.sum_eq_zero
   intro i hi
   exact box_cell_slope_zero (le_of_lt hs) hφ (cellU i hi) hwU
 have hkval : (∑ u ∈ boundary S, edgeInt s u k) =
       (2*(Real.pi:ℂ)*Complex.I) := by
   rw [sum_edges_boxes]
   exact sum_boxes_kernel hs S hS hwK
 -- sum the edge identity
 calc
 _ = (∑ u ∈ boundary S, (edgeInt s u p + φ w * edgeInt s u k)) := by
       apply Finset.sum_congr rfl
       intro j hj
       exact one j hj
 _ = _ := by rw [Finset.sum_add_distrib]
             rw [← Finset.mul_sum]
             rw [hpzero, hkval]
             ring
end WL.Planar

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Residue.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Characters.lean
noncomputable section
open Set WeakDual
open scoped ENNReal lp Real ComplexConjugate BigOperators
namespace WL

lemma char_bound (χ : characterSpace ℂ L1) (a : L1) : ‖χ a‖ ≤ ‖a‖ := by
  have h := WeakDual.CharacterSpace.norm_le_norm_one χ
  have hh := (WeakDual.toStrongDual (χ : WeakDual ℂ L1)).le_opNorm a
  exact hh.trans (by simpa using mul_le_mul_of_nonneg_right h (norm_nonneg a))
lemma char_u_norm (χ : characterSpace ℂ L1) (n : ℤ) : ‖χ (u n)‖ = 1 := by
  have le1 (j : ℤ) : ‖χ (u j)‖ ≤ 1 := (char_bound χ _).trans_eq (norm_u j)
  have prod : χ (u n) * χ (u (-n)) = 1 := by
    rw [← map_mul, u_mul]
    have e : n + -n = (0:ℤ) := by omega
    rw [e]
    exact map_one χ
  have hn : ‖χ (u n)‖ * ‖χ (u (-n))‖ = 1 := by simpa [norm_mul] using congrArg norm prod
  have ge : 1 ≤ ‖χ (u n)‖ := by nlinarith [le1 (-n), norm_nonneg (χ (u n)), norm_nonneg (χ (u (-n)))]
  exact le_antisymm (le1 n) ge

lemma char_u (χ : characterSpace ℂ L1) (n : ℤ) :
    χ (u n) = (χ (u 1)) ^ n := by
  have nat : ∀ k : ℕ, χ (u (k:ℤ)) = (χ (u 1)) ^ k := by
    intro k
    induction k with
    | zero => exact map_one χ
    | succ k ih =>
      calc
        χ (u ((k+1:ℕ):ℤ)) = χ (u (k:ℤ) * u 1) := by
          rw [u_mul]; norm_num
        _ = χ (u (k:ℤ)) * χ (u 1) := map_mul χ _ _
        _ = _ := by rw [ih, pow_succ]
  cases n with
  | ofNat k => simpa using nat k
  | negSucc k =>
    let j : ℕ := k+1
    have rel : χ (u (-(j:ℤ))) * χ (u (j:ℤ)) = 1 := by
      rw [← map_mul, u_mul]
      have e : (-(j:ℤ)) + (j:ℤ) = 0 := by omega
      rw [e]
      exact map_one χ
    have val : χ (u (-(j:ℤ))) = (χ (u (j:ℤ)))⁻¹ :=
      by
        have hy : χ (u (j:ℤ)) ≠ 0 := by
          intro h; rw [h, mul_zero] at rel; exact zero_ne_one rel
        convert (eq_div_iff hy).2 rel using 1 <;> simp
    have en : Int.negSucc k = -(j:ℤ) := by simp [Int.negSucc_eq, j]
    rw [en, val, nat j]
    simp
lemma char_pt (χ : characterSpace ℂ L1) (n : ℤ) (z : ℂ) :
    χ (pt n z) = z * (χ (u 1)) ^ n := by
  rw [pt_smul, map_smul, char_u]
  rfl

end WL

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Characters.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Wiener.lean
set_option maxHeartbeats 800000
noncomputable section
open Set WeakDual
open scoped ENNReal lp Real ComplexConjugate BigOperators
namespace WL

/-- A character of the absolutely summable convolution algebra is obtained by
sampling the normally convergent Fourier series at a point of the circle.
This is the elementary Gelfand-space part of Wiener's lemma. -/
lemma char_point {T : ℝ} [Fact (0 < T)] (χ : characterSpace ℂ L1) :
    ∃ x : AddCircle T, ∀ a : L1, χ a = (synth (T:=T) a) x := by
  obtain ⟨x, hx⟩ : ∃ x : AddCircle T, fourier (T:=T) 1 x = χ (u 1) := by
    have hs : ‖χ (u 1)‖ = (1:ℝ) := char_u_norm χ 1
    let z : Circle := ⟨χ (u 1), (mem_sphere_zero_iff_norm.mpr hs)⟩
    have hT : T ≠ 0 := ne_of_gt (Fact.out : 0 < T)
    let x : AddCircle T := (AddCircle.homeomorphCircle hT).symm z
    refine ⟨x, ?_⟩
    rw [fourier_one, ← AddCircle.homeomorphCircle_apply]
    change (↑((AddCircle.homeomorphCircle hT) x) : ℂ) = χ (u 1)
    dsimp [x]
    simp [z]
  have hpow (n : ℤ) : fourier (T:=T) n x = (χ (u 1)) ^ n := by
    calc
      fourier (T:=T) n x = (↑((n • x).toCircle) : ℂ) := rfl
      _ = (↑(x.toCircle ^ n) : ℂ) := by rw [AddCircle.toCircle_zsmul]
      _ = ((↑(x.toCircle) : ℂ)^ n) := Circle.coe_zpow _ _
      _ = (fourier (T:=T) 1 x) ^ n := by rw [fourier_one]
      _ = (χ (u 1)) ^ n := by rw [hx]
  refine ⟨x, ?_⟩
  intro a
  have hchars : HasSum (fun n : ℤ => χ (pt n (a n))) (χ a) :=
    (WeakDual.CharacterSpace.toCLM χ).hasSum (hasSum_pt a)
  have hev : HasSum (fun n : ℤ =>
      ((a n • (fourier (T:=T) n)) : C(AddCircle T, ℂ)) x)
      ((synth (T:=T) a) x) :=
    (ContinuousMap.evalCLM ℂ x).hasSum (hasSum_synth (T:=T) a)
  have eqterm (n : ℤ) : χ (pt n (a n)) =
      ((a n • (fourier (T:=T) n)) : C(AddCircle T, ℂ)) x := by
    rw [char_pt]
    change a n * (χ (u 1)) ^ n = a n * fourier (T:=T) n x
    rw [hpow]
  have hs : HasSum (fun n : ℤ => χ (pt n (a n)))
      ((synth (T:=T) a) x) :=
    hev.congr_fun (fun n => eqterm n)
  exact hchars.unique hs

/-- Evaluation of a normally convergent Fourier series is an algebra homomorphism.
This is useful for both directions of the spectrum computation. -/
noncomputable def evalAlg {T : ℝ} [Fact (0 < T)] (x : AddCircle T) :
    L1 →ₐ[ℂ] ℂ where
  toFun a := synth (T:=T) a x
  map_one' := by rw [synth_one]; rfl
  map_mul' a b := by rw [synth_mul]; rfl
  map_zero' := by rw [synth_zero]; rfl
  map_add' a b := by rw [synth_add]; rfl
  commutes' z := by
    change synth (T:=T) (pt 0 z) x = z
    rw [synth_pt]
    simp

/-- The continuous character at a point. Continuity here comes for free from
`AlgHom.toContinuousLinearMap` for homomorphisms into a complete normed field. -/
noncomputable def evalChar {T : ℝ} [Fact (0 < T)] (x : AddCircle T) :
    characterSpace ℂ L1 :=
  WeakDual.CharacterSpace.equivAlgHom.symm (evalAlg (T:=T) x)
@[simp] lemma evalChar_apply {T : ℝ} [Fact (0 < T)] (x : AddCircle T) (a : L1) :
    evalChar (T:=T) x a = synth (T:=T) a x := rfl

/-- The spectrum in `ℓ¹(ℤ)` consists exactly of the pointwise values of its
normally convergent Fourier series. The nontrivial direction uses characters. -/
lemma mem_spectrum_iff_exists_point {T : ℝ} [Fact (0 < T)] (a : L1) (z : ℂ) :
    z ∈ spectrum ℂ a ↔ ∃ x : AddCircle T, synth (T:=T) a x = z := by
  rw [WeakDual.CharacterSpace.mem_spectrum_iff_exists]
  constructor
  · rintro ⟨χ, hχ⟩
    obtain ⟨x, hx⟩ := char_point (T:=T) χ
    refine ⟨x, ?_⟩
    exact (hx a).symm.trans hχ
  · rintro ⟨x, hx⟩
    exact ⟨evalChar (T:=T) x, hx⟩

/-- Wiener inverse criterion in the Banach algebra form. -/
lemma isUnit_sub_iff_nonvanish {T : ℝ} [Fact (0 < T)] (a : L1) (z : ℂ) :
    IsUnit ((algebraMap ℂ L1) z - a) ↔
      ∀ x : AddCircle T, z ≠ synth (T:=T) a x := by
  rw [← spectrum.notMem_iff]
  rw [mem_spectrum_iff_exists_point (T:=T) a z]
  simp [eq_comm]

lemma isUnit_iff_nonzero_synth {T : ℝ} [Fact (0 < T)] (a : L1) :
    IsUnit a ↔ ∀ x : AddCircle T, synth (T:=T) a x ≠ 0 := by
  have h := isUnit_sub_iff_nonvanish (T:=T) a (0:ℂ)
  rw [map_zero, zero_sub] at h
  constructor
  · intro ha x hx
    have hn : IsUnit (-a) := ha.neg
    have hh := h.mp hn x
    exact hh (by simpa using hx.symm)
  · intro H
    have hn : IsUnit (-a) := h.mpr (fun x hx => H x (by simpa using hx.symm))
    simpa using hn.neg

/-- Once the Fourier series has no zero, the inverse is represented by an
`ℓ¹` vector. This is the pointwise inverse version of Wiener's lemma. -/
lemma exists_inverse_pointwise {T : ℝ} [Fact (0 < T)] (a : L1)
    (ha : ∀ x : AddCircle T, synth (T:=T) a x ≠ 0) :
    ∃ b : L1, ∀ x : AddCircle T,
      synth (T:=T) b x = (synth (T:=T) a x)⁻¹ := by
  have hu : IsUnit a := (isUnit_iff_nonzero_synth (T:=T) a).2 ha
  rcases hu with ⟨v, hv⟩
  let b : L1 := (↑(v⁻¹) : L1)
  have hab : a * b = 1 := by
    change a * (↑(v⁻¹) : L1) = 1
    rw [← hv]
    change (↑v : L1) * (↑(v⁻¹) : L1) = 1
    exact Units.mul_inv v
  refine ⟨b, ?_⟩
  intro x
  have hprod : synth (T:=T) a x * synth (T:=T) b x = 1 := by
    rw [← ContinuousMap.mul_apply]
    rw [← synth_mul]
    rw [hab]
    rw [synth_one]
    rfl

  exact (eq_inv_of_mul_eq_one_right hprod) -- orient?

/-- Resolvents, in pointwise form. This isolates the inverse-closedness input
that will be used when building the Cauchy integral. -/
lemma exists_resolvent_pointwise {T : ℝ} [Fact (0 < T)] (a : L1) (z : ℂ)
    (hz : ∀ x : AddCircle T, z ≠ synth (T:=T) a x) :
    ∃ b : L1, ∀ x : AddCircle T,
      synth (T:=T) b x = (z - synth (T:=T) a x)⁻¹ := by
  let c : L1 := (algebraMap ℂ L1) z - a
  have hcform (x : AddCircle T) : synth (T:=T) c x = z - synth (T:=T) a x := by
    change synth (T:=T) (_ + (-a)) x = _
    rw [synth_add, synth_neg']
    change (synth (T:=T) (pt 0 z) + -(synth (T:=T) a)) x = _
    rw [synth_pt]
    -- at zero the Fourier character is one
    simp [sub_eq_add_neg]
  have hc : ∀ x : AddCircle T, synth (T:=T) c x ≠ 0 := by
    intro x
    rw [hcform]
    exact sub_ne_zero.mpr (hz x)
  obtain ⟨b, hb⟩ := exists_inverse_pointwise (T:=T) c hc
  refine ⟨b, ?_⟩
  intro x
  simpa [hcform] using hb x

end WL

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Wiener.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Calculus.lean

noncomputable section
open Set
open scoped ENNReal lp Real ComplexConjugate BigOperators Topology
namespace WL

/-- Evaluation of the *canonical* Banach algebra resolvent is pointwise
scalar resolvent. The earlier inverse lemma only produced an existential
inverse; for integration it is important to use the canonical continuously
varying one. -/
lemma synth_resolvent_apply {T : ℝ} [Fact (0 < T)] (a : L1) {z : ℂ}
    (hz : z ∈ resolventSet ℂ a) (x : AddCircle T) :
    synth (T:=T) (resolvent a z) x = (z - synth (T:=T) a x)⁻¹ := by
  have hm : ((algebraMap ℂ L1) z - a) * (resolvent a z) = 1 := by
    rw [spectrum.resolvent_eq hz]
    exact hz.unit.val_inv
  have he := congrArg (fun q : L1 => evalAlg (T:=T) x q) hm
  have he' : (z - synth (T:=T) a x) * synth (T:=T) (resolvent a z) x = 1 := by
    rw [map_mul, map_sub, map_one] at he
    simpa [evalAlg] using he
  exact eq_inv_of_mul_eq_one_right he'

/-- Same assertion with the spectrum phrasing. -/
lemma synth_resolvent_apply_of_not_mem {T : ℝ} [Fact (0 < T)] (a : L1)
    {z : ℂ} (hz : z ∉ spectrum ℂ a) (x : AddCircle T) :
    synth (T:=T) (resolvent a z) x = (z - synth (T:=T) a x)⁻¹ :=
  synth_resolvent_apply (T:=T) a ((spectrum.notMem_iff).mp hz) x

/-- `synth` evaluated at a point is a continuous linear map, not only an
algebra hom. This is the map with which we commute the Bochner contour
integrals. -/
noncomputable def evalCLM {T : ℝ} [Fact (0 < T)] (x : AddCircle T) :
    L1 →L[ℂ] ℂ := (WeakDual.CharacterSpace.toCLM (evalChar (T:=T) x))

@[simp] lemma evalCLM_apply {T : ℝ} [Fact (0 < T)] (x : AddCircle T)
    (a : L1) : evalCLM (T:=T) x a = synth (T:=T) a x := rfl

/-- Resolvent and the scalar factor are continuous on any closed path in the
resolvent set.  This elementary observation supplies integrability of the
Banach-valued paths used below without any measurable-selection inverse. -/
lemma continuousAt_resolvent_of_mem {a : L1} {z : ℂ}
    (hz : z ∈ resolventSet ℂ a) : ContinuousAt (resolvent a) z :=
  (spectrum.hasDerivAt_resolvent_const_left hz).continuousAt

lemma continuousOn_resolvent_of_subset {a : L1} {s : Set ℂ}
    (hs : s ⊆ resolventSet ℂ a) : ContinuousOn (resolvent a) s := by
  intro z hz
  exact (continuousAt_resolvent_of_mem (a:=a) (hs hz)).continuousWithinAt

end WL

open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology
namespace WL

/-- A continuous linear map commutes with the circle integral when the original
integrand is circle integrable. (CircleIntegral only supplies additive/smul
lemmas; exposing this frequently used fact avoids any interchange argument
at the functional-calculus site.) -/
lemma clm_circleIntegral {E F : Type*} [NormedAddCommGroup E]
    [NormedAddCommGroup F] [NormedSpace ℂ E] [NormedSpace ℂ F]
    [CompleteSpace E] [CompleteSpace F]
    (L : E →L[ℂ] F) {q : ℂ → E} {c : ℂ} {R : ℝ}
    (hq : CircleIntegrable q c R) :
    L (∮ z in C(c, R), q z) =
      ∮ z in C(c, R), L (q z) := by
  have hi : IntervalIntegrable (fun θ : ℝ =>
      deriv (circleMap c R) θ • q (circleMap c R θ)) volume 0 (2*Real.pi) :=
    (circleIntegrable_iff R).1 hq
  simp only [circleIntegral]
  rw [← L.intervalIntegral_comp_comm hi]
  apply intervalIntegral.integral_congr
  intro θ hθ
  change L (_ • _) = _ • _
  exact L.map_smul _ _

/-- The single-contour (disc) case of analytic calculus. No simply-connected
assumption on the ambient `U` is hidden here: the explicit additional
hypothesis is that one disc inside `U` already surrounds the spectrum.
The general construction later uses finitely many boundary contours; this
lemma is the local piece and fixes all map/integral/norm bookkeeping. -/
lemma exists_calculus_circle {T : ℝ} [Fact (0 < T)] (a : L1)
    (φ : ℂ → ℂ) (U : Set ℂ) (hφ : AnalyticOnNhd ℂ φ U)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hdisc : closedBall c R ⊆ U)
    (hinside : ∀ x : AddCircle T, synth (T:=T) a x ∈ ball c R) :
    ∃ b : L1, ∀ x : AddCircle T,
       synth (T:=T) b x = φ (synth (T:=T) a x) := by
  have hsph : sphere c R ⊆ resolventSet ℂ a := by
    intro z hz
    have hn : ∀ x : AddCircle T, z ≠ synth (T:=T) a x := by
      intro x hx
      have hh := hinside x
      have hz' : dist (synth (T:=T) a x) c < R := by simpa [dist_comm] using hh
      have he : dist z c = R := by simpa [dist_eq_norm_sub] using hz
      have : dist (synth (T:=T) a x) c = R := by simpa [hx] using he
      exact (ne_of_lt hz') this
    exact (WL.isUnit_sub_iff_nonvanish (T:=T) a z).2 hn
  have hcontφ : ContinuousOn φ (closedBall c R) := hφ.continuousOn.mono hdisc
  have hdiffφ : ∀ z ∈ ball c R, DifferentiableAt ℂ φ z := by
    intro z hz
    exact (hφ (z) (hdisc (ball_subset_closedBall hz))).differentiableAt
  let q : ℂ → L1 := fun z => φ z • resolvent a z
  have hqcont : ContinuousOn q (sphere c R) := by
    have h1 : ContinuousOn φ (sphere c R) := hcontφ.mono sphere_subset_closedBall
    have h2 : ContinuousOn (resolvent a) (sphere c R) :=
      continuousOn_resolvent_of_subset hsph
    exact h1.smul h2
  have hq : CircleIntegrable q c R := hqcont.circleIntegrable hR.le
  let b : L1 := ( (2 * (Real.pi:ℂ) * Complex.I)⁻¹) • (∮ z in C(c,R), q z)
  refine ⟨b, ?_⟩
  intro x
  have hm := clm_circleIntegral (evalCLM (T:=T) x) hq
  have hscalar_int :
      (∮ z in C(c,R),
          (z - synth (T:=T) a x)⁻¹ • φ z) =
        (2 * Real.pi * Complex.I : ℂ) • φ (synth (T:=T) a x) := by
    exact Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
      (R:=R) (c:=c) (w:=synth (T:=T) a x)
      (s:= (∅ : Set ℂ)) Set.countable_empty
      (by simpa using hinside x) hcontφ (by
        intro z hz
        exact hdiffφ z hz.1)
  -- identify the evaluated integrand on the contour by the resolvent formula.
  have hfun :
      (∮ z in C(c,R), (evalCLM (T:=T) x) (q z)) =
      (∮ z in C(c,R), (z - synth (T:=T) a x)⁻¹ • φ z) := by
    apply circleIntegral.integral_congr hR.le
    intro z hz
    have hz' : z ∈ resolventSet ℂ a := hsph hz
    change (evalCLM (T:=T) x) (q z) = _
    rw [show q z = φ z • resolvent a z from rfl]
    rw [map_smul, evalCLM_apply,
        synth_resolvent_apply (T:=T) a hz' x]
    -- commutativity in ℂ converts the two scalar factors
    change φ z * (z - synth (T:=T) a x)⁻¹ =
      (z - synth (T:=T) a x)⁻¹ * φ z
    exact mul_comm _ _
  change synth (T:=T) b x = _
  change (evalCLM (T:=T) x) b = _
  change (evalCLM (T:=T) x) (_ • _) = _
  rw [map_smul, hm, hfun, hscalar_int]
  -- the normalization is a nonzero scalar.
  have hp : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
    exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
      Complex.I_ne_zero
  -- scalar smuls on ℂ
  change (2 * (Real.pi:ℂ) * Complex.I)⁻¹ *
        ((2 * (Real.pi:ℂ) * Complex.I) * φ (synth (T:=T) a x)) = _
  rw [inv_mul_cancel_left₀ hp]

end WL

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Calculus.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Contours.lean

noncomputable section
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology ENNReal lp BigOperators ComplexConjugate
namespace WL

/-- Banach algebra part of the finite-contour construction. This lemma asks only
 for the elementary scalar index calculation on the chosen curves. The curves
 can be rectangle edges, polygon edges, or smooth circles; there is no use of a
 measurable choice of inverse. `d` is their velocity (it is convenient not to
 require a particular parametrisation here). The two continuity hypotheses are
 also enough for Bochner integrals. Thus the genuinely planar part of the
 usual holomorphic-calculus proof is separated from the algebraic part. -/
lemma exists_calculus_contours {T : ℝ} [Fact (0 < T)] (a : L1)
    (φ : ℂ → ℂ) (U : Set ℂ) (hφ : AnalyticOnNhd ℂ φ U)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (γ d : ι → ℝ → ℂ)
    (hγ : ∀ i, ContinuousOn (γ i) (uIcc (0:ℝ) 1))
    (hd : ∀ i, ContinuousOn (d i) (uIcc (0:ℝ) 1))
    (hin : ∀ i, MapsTo (γ i) (uIcc (0:ℝ) 1) U)
    (hr : ∀ i, MapsTo (γ i) (uIcc (0:ℝ) 1) (resolventSet ℂ a))
    (hscalar : ∀ x : AddCircle T,
      ((2 * (Real.pi:ℂ) * Complex.I)⁻¹) *
       (∑ i : ι, ∫ t : ℝ in (0:ℝ)..1,
          (d i t * φ (γ i t)) *
            (γ i t - synth (T:=T) a x)⁻¹) =
        φ (synth (T:=T) a x)) :
    ∃ b : L1, ∀ x : AddCircle T,
      synth (T:=T) b x = φ (synth (T:=T) a x) := by
  classical
  let q : ι → ℝ → L1 := fun i t =>
    d i t • (φ (γ i t) • resolvent a (γ i t))
  have hqi (i : ι) : IntervalIntegrable (q i) volume (0:ℝ) 1 := by
    have A : ContinuousOn (fun t : ℝ => φ (γ i t)) (uIcc (0:ℝ) 1) :=
      hφ.continuousOn.comp (hγ i) (hin i)
    have B0 : ContinuousOn (resolvent a)
        (γ i '' (uIcc (0:ℝ) 1)) :=
      continuousOn_resolvent_of_subset (a:=a) (by
        rintro z ⟨t, ht, rfl⟩
        exact hr i ht)
    have B : ContinuousOn (fun t : ℝ => resolvent a (γ i t))
        (uIcc (0:ℝ) 1) :=
      B0.comp (hγ i) (by
        intro t ht
        exact ⟨t, ht, rfl⟩)
    exact ((hd i).smul (A.smul B)).intervalIntegrable

  let b : L1 := ((2 * (Real.pi:ℂ) * Complex.I)⁻¹) •
      (∑ i : ι, ∫ t : ℝ in (0:ℝ)..1, q i t)
  refine ⟨b, ?_⟩
  intro x
  change (evalCLM (T:=T) x) b = _
  change (evalCLM (T:=T) x) (_ • _) = _
  rw [map_smul, map_sum]
  have each (i : ι) :
      (evalCLM (T:=T) x) (∫ t : ℝ in (0:ℝ)..1, q i t) =
        (∫ t : ℝ in (0:ℝ)..1,
          (d i t * φ (γ i t)) * (γ i t - synth (T:=T) a x)⁻¹) := by
    rw [← (evalCLM (T:=T) x).intervalIntegral_comp_comm (hqi i)]
    apply intervalIntegral.integral_congr
    intro t ht
    have hz : γ i t ∈ resolventSet ℂ a := hr i ht
    change (evalCLM (T:=T) x)
      (d i t • (φ (γ i t) • resolvent a (γ i t))) = _
    rw [map_smul, map_smul, evalCLM_apply,
        synth_resolvent_apply (T:=T) a hz x]
    -- All the scalar actions are multiplication in `ℂ`.
    simp [smul_eq_mul, mul_assoc]
  simp_rw [each]
  -- now precisely the scalar index assertion
  exact hscalar x


end WL

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Contours.lean

-- BEGIN INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Multi.lean

noncomputable section
open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology ENNReal lp BigOperators ComplexConjugate
namespace WL

open scoped ComplexConjugate


/-- One circle is also useful as a *piece* of a contour. It need not enclose
 the whole spectrum: it may catch some of the values of `a`, provided no
 value lies on its boundary. Points in the disc give the Cauchy value and
 points outside give zero. This is the additivity unit in the finite-contour
 construction. -/
lemma exists_calculus_circle_piece {T : ℝ} [Fact (0 < T)] (a : L1)
    (φ : ℂ → ℂ) (U : Set ℂ) (hφ : AnalyticOnNhd ℂ φ U)
    {c : ℂ} {R : ℝ} (hR : 0 < R)
    (hdisc : closedBall c R ⊆ U)
    (havoid : ∀ x : AddCircle T,
      synth (T:=T) a x ∈ ball c R ∨ synth (T:=T) a x ∉ closedBall c R) :
    ∃ b : L1, (∀ x : AddCircle T, synth (T:=T) a x ∈ ball c R →
          synth (T:=T) b x = φ (synth (T:=T) a x)) ∧
        (∀ x : AddCircle T, synth (T:=T) a x ∉ closedBall c R →
          synth (T:=T) b x = 0) := by
  classical
  -- the contour itself is in the resolvent set
  have hsph : sphere c R ⊆ resolventSet ℂ a := by
    intro z hz
    apply (WL.isUnit_sub_iff_nonvanish (T:=T) a z).2
    intro x hx
    rcases havoid x with hi | ho
    · have hi' : dist (synth (T:=T) a x) c < R := by
        simpa [Metric.mem_ball, dist_comm] using hi
      have hz' : dist z c = R := by
        rw [Metric.mem_sphere] at hz
        exact hz
      have he : dist (synth (T:=T) a x) c = R := by simpa [hx] using hz'
      exact (ne_of_lt hi') he
    · have hz' : z ∈ closedBall c R := sphere_subset_closedBall hz
      exact ho (by simpa [← hx] using hz')
  have hcontφ : ContinuousOn φ (closedBall c R) := hφ.continuousOn.mono hdisc
  have hdiffφ : ∀ z ∈ ball c R, DifferentiableAt ℂ φ z := by
    intro z hz
    exact (hφ z (hdisc (ball_subset_closedBall hz))).differentiableAt
  let q : ℂ → L1 := fun z => φ z • resolvent a z
  have hqcont : ContinuousOn q (sphere c R) :=
    (hcontφ.mono sphere_subset_closedBall).smul
      (continuousOn_resolvent_of_subset hsph)
  have hq : CircleIntegrable q c R := hqcont.circleIntegrable hR.le
  let b : L1 := ((2 * (Real.pi:ℂ) * Complex.I)⁻¹) • (∮ z in C(c,R), q z)
  refine ⟨b, ?_, ?_⟩
  · intro x hi
    have hm := clm_circleIntegral (evalCLM (T:=T) x) hq
    have hfun :
        (∮ z in C(c,R), (evalCLM (T:=T) x) (q z)) =
          (∮ z in C(c,R), (z - synth (T:=T) a x)⁻¹ • φ z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hz' : z ∈ resolventSet ℂ a := hsph hz
      change (evalCLM (T:=T) x) (q z) = _
      rw [show q z = φ z • resolvent a z from rfl]
      rw [map_smul, evalCLM_apply,
          synth_resolvent_apply (T:=T) a hz' x]
      change φ z * (z - synth (T:=T) a x)⁻¹ =
        (z - synth (T:=T) a x)⁻¹ * φ z
      exact mul_comm _ _
    change (evalCLM (T:=T) x) b = _
    change (evalCLM (T:=T) x) (_ • _) = _
    rw [map_smul, hm, hfun]
    have hp : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
      exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
        Complex.I_ne_zero
    have hv :
        (∮ z in C(c,R),
          (z - synth (T:=T) a x)⁻¹ • φ z) =
          (2 * Real.pi * Complex.I : ℂ) • φ (synth (T:=T) a x) :=
      Complex.circleIntegral_sub_inv_smul_of_differentiable_on_off_countable
        (R:=R) (c:=c) (w:=synth (T:=T) a x)
        (s:=(∅ : Set ℂ)) Set.countable_empty hi hcontφ (by
          intro z hz
          exact hdiffφ z hz.1)
    rw [hv]
    change (2 * (Real.pi:ℂ) * Complex.I)⁻¹ *
      ((2 * (Real.pi:ℂ) * Complex.I) * φ (synth (T:=T) a x)) = _
    rw [inv_mul_cancel_left₀ hp]
  · intro x ho
    have hm := clm_circleIntegral (evalCLM (T:=T) x) hq
    have hfun :
        (∮ z in C(c,R), (evalCLM (T:=T) x) (q z)) =
          (∮ z in C(c,R), (z - synth (T:=T) a x)⁻¹ • φ z) := by
      apply circleIntegral.integral_congr hR.le
      intro z hz
      have hz' : z ∈ resolventSet ℂ a := hsph hz
      change (evalCLM (T:=T) x) (q z) = _
      rw [show q z = φ z • resolvent a z from rfl]
      rw [map_smul, evalCLM_apply,
          synth_resolvent_apply (T:=T) a hz' x]
      change φ z * (z - synth (T:=T) a x)⁻¹ =
        (z - synth (T:=T) a x)⁻¹ * φ z
      exact mul_comm _ _
    change (evalCLM (T:=T) x) b = (0:ℂ)
    change (evalCLM (T:=T) x) (_ • _) = (0:ℂ)
    rw [map_smul, hm, hfun]
    have hne : ∀ z ∈ closedBall c R, z - synth (T:=T) a x ≠ 0 := by
      intro z hz hzero
      have he : z = synth (T:=T) a x := sub_eq_zero.mp hzero
      exact ho (by simpa [← he] using hz)
    have hkc : ContinuousOn
        (fun z : ℂ => (z - synth (T:=T) a x)⁻¹ • φ z) (closedBall c R) :=
      ((continuousOn_id.sub continuousOn_const).inv₀ hne).smul hcontφ
    have hkd : ∀ z ∈ ball c R \ (∅ : Set ℂ),
        DifferentiableAt ℂ (fun z : ℂ => (z - synth (T:=T) a x)⁻¹ • φ z) z := by
      intro z hz
      have he := hne z (ball_subset_closedBall hz.1)
      have h1 : DifferentiableAt ℂ (fun z : ℂ =>
          (z - synth (T:=T) a x)⁻¹) z :=
        (differentiableAt_id.sub (differentiableAt_const
          (c:=synth (T:=T) a x))).inv he
      have h2 := hdiffφ z hz.1
      exact h1.smul h2
    have hv :
        (∮ z in C(c,R), (z - synth (T:=T) a x)⁻¹ • φ z) = 0 :=
      Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable
        (R:=R) (c:=c) hR.le (s:=(∅ : Set ℂ)) Set.countable_empty hkc hkd
    rw [hv, smul_zero]

end WL

open Set MeasureTheory intervalIntegral Metric Filter Function
open scoped Interval Real NNReal ENNReal Topology ENNReal lp BigOperators ComplexConjugate
namespace WL

/-- A finite weighted chain of circles. The combinatorial hypothesis says its
index is one at every spectral value. It avoids building one huge measurable
choice of inverses; all inverses used here are the canonical resolvent. In
applications the little circles can be replaced by any finite contour pieces
with the same scalar index calculation. -/
lemma exists_calculus_circles_weighted {T : ℝ} [Fact (0 < T)] (a : L1)
    (φ : ℂ → ℂ) (U : Set ℂ) (hφ : AnalyticOnNhd ℂ φ U)
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (c : ι → ℂ) (R : ι → ℝ) (v : ι → ℂ)
    (hR : ∀ i, 0 < R i)
    (hdisc : ∀ i, closedBall (c i) (R i) ⊆ U)
    (havoid : ∀ i (x : AddCircle T),
      synth (T:=T) a x ∈ ball (c i) (R i) ∨
        synth (T:=T) a x ∉ closedBall (c i) (R i))
    (hindex : ∀ x : AddCircle T,
      (∑ i : ι, if dist (synth (T:=T) a x) (c i) < R i
        then v i else 0) = 1) :
    ∃ b : L1, ∀ x : AddCircle T,
      synth (T:=T) b x = φ (synth (T:=T) a x) := by
  classical
  have pieces (i : ι) :
      ∃ b : L1,
        (∀ x : AddCircle T, synth (T:=T) a x ∈ ball (c i) (R i) →
          synth (T:=T) b x = φ (synth (T:=T) a x)) ∧
        (∀ x : AddCircle T, synth (T:=T) a x ∉ closedBall (c i) (R i) →
          synth (T:=T) b x = 0) :=
    exists_calculus_circle_piece (T:=T) a φ U hφ (hR i) (hdisc i) (havoid i)
  choose p hp_in hp_out using fun i => pieces i
  let b : L1 := ∑ i : ι, v i • p i
  refine ⟨b, ?_⟩
  intro x
  have hpx (i : ι) :
      synth (T:=T) (p i) x =
        if dist (synth (T:=T) a x) (c i) < R i
          then φ (synth (T:=T) a x) else 0 := by
    split_ifs with h
    · apply hp_in i x
      simpa [Metric.mem_ball] using h
    · have hb0 : synth (T:=T) a x ∉ ball (c i) (R i) := by
        simpa [Metric.mem_ball] using h
      rcases havoid i x with hi | ho
      · exact False.elim (hb0 hi)
      · exact hp_out i x ho
  change (evalCLM (T:=T) x) b = _
  change (evalCLM (T:=T) x) (∑ i : ι, v i • p i) = _
  rw [map_sum]
  simp_rw [map_smul, evalCLM_apply, hpx]
  -- factor the common value out of the finite sum of indices.
  have heq (i : ι) :
      v i • (if dist (synth (T:=T) a x) (c i) < R i
          then φ (synth (T:=T) a x) else 0) =
        (if dist (synth (T:=T) a x) (c i) < R i then v i else 0) *
          φ (synth (T:=T) a x) := by
    by_cases h : dist (synth (T:=T) a x) (c i) < R i
    · simp [h, smul_eq_mul]
    · simp [h]
  simp_rw [heq]
  rw [← Finset.sum_mul, hindex x, one_mul]

end WL

end

-- END INLINED FILE: Mathlib/Support/wiener_levy_analytic_calculus_64feeb4f40/Multi.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval.Analysis.WienerLevy

/-!
# Wiener–Lévy theorem (analytic functional calculus)

§226 of Oliver Knill's *Some Fundamental Theorems in Mathematics*. The
Wiener–Lévy theorem: if `φ` is complex-analytic on a neighbourhood of the
range of a Wiener-algebra function `f`, then the composition `φ ∘ f` is again
in the Wiener algebra.

mathlib has the additive circle, the Fourier characters `fourier`, Fourier
coefficients `fourierCoeff`, and `hasSum_fourier_series_of_summable`, but not
the Wiener algebra or its analytic functional calculus.
-/

open Set
open scoped ComplexConjugate Real

noncomputable section

variable {T : ℝ} [Fact (0 < T)]

/-- The Wiener-algebra predicate on the additive circle: a continuous
complex-valued function whose Fourier coefficients are absolutely summable.
For complex series, `Summable` is equivalent to absolute summability of the
norms. -/
def InWienerAlgebra (f : C(AddCircle T, ℂ)) : Prop :=
  Summable (fourierCoeff f)



end

end LeanEval.Analysis.WienerLevy

open LeanEval.Analysis.WienerLevy
open Set
open scoped ComplexConjugate Real

variable {T : ℝ} [Fact (0 < T)]
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem wiener_levy_analytic_calculus (f : C(AddCircle T, ℂ))
    (φ : ℂ → ℂ) (U : Set ℂ) (hf : InWienerAlgebra f)
    (hU : IsOpen U) (hrange : range f ⊆ U)
    (hφ : AnalyticOnNhd ℂ φ U) :
    ∃ g : C(AddCircle T, ℂ),
      (∀ x, g x = φ (f x)) ∧ InWienerAlgebra g :=
/-ResultProofBegin-/by
  -- The analytic local hypothesis first gives an honest continuous composition;
  -- no extension of `φ` off `U` is necessary.
  have hc : Continuous (fun x : AddCircle T => φ (f x)) := by
    have hcont : ContinuousOn φ U := hφ.continuousOn
    have hx : ∀ x : AddCircle T, f x ∈ U := by
      intro x
      exact hrange ⟨x, rfl⟩
    simpa [Function.comp_def] using
      (hcont.comp_continuous f.continuous hx)
  let g : C(AddCircle T, ℂ) := ⟨fun x => φ (f x), hc⟩
  refine ⟨g, ?_, ?_⟩
  · intro x; rfl
  -- By normal convergence, membership in A(T) is exactly membership in the
  -- image of Fourier synthesis on `ℓ¹(ℤ,ℂ)`. This isolates the hard
  -- holomorphic-closure assertion from continuity/inversion of Fourier
  -- series; those inverse statements are proved in the support file.
  change Summable (fourierCoeff g)
  have ha : ∃ a : WL.L1, WL.synth (T:=T) a = f :=
    (WL.mem_range_synth (T:=T) f).1 hf
  obtain ⟨a, ha⟩ := ha
  -- we use the unique coefficient vector, not arbitrary Fourier coefficients;
  -- this is the Banach algebra input for the remaining analytic-calculus step.
  have aspec : fourierCoeff (T:=T) (f : AddCircle T → ℂ) =
      (fun n : ℤ => a n) := by
    simpa [← ha] using (WL.coeff_synth (T:=T) a)
  -- turn the remaining assertion into the genuinely Banach-algebraic one: find
  -- a normally convergent Laurent series for the analytic function of `a`.
  apply (WL.mem_range_synth (T:=T) g).2
  -- The convolution support lemmas justify the multiplication in this reduction:
  -- products of synthesized series are synthesized convolutions, with the correct
  -- Banach estimate `WL.norm_conv_le`. What is still needed here is inverse-closedness
  -- (Wiener's lemma), followed by the holomorphic functional calculus.
  -- Its spectrum has now been computed in the support theory. In particular it
  -- is already contained in the required analytic open set: there are no
  -- hidden extra Gelfand characters. This is the inverse-closed part of
  -- Wiener's theorem.
  have hrpoint (x : AddCircle T) : WL.synth (T:=T) a x = f x := by
    have h := congrArg (fun q : C(AddCircle T, ℂ) => q x) ha
    exact h
  have hspec : spectrum ℂ a ⊆ U := by
    intro z hz
    obtain ⟨x, hx⟩ :=
      (WL.mem_spectrum_iff_exists_point (T:=T) a z).1 hz
    have hfx : f x = z := (hrpoint x).symm.trans hx
    exact hfx ▸ hrange ⟨x, rfl⟩
  -- In particular every scalar off the pointwise range has an honest
  -- ℓ¹-resolvent. This follows from the character computation and is the
  -- precise Wiener inverse lemma, rather than a formal inverse in continuous
  -- functions.
  have hres (z : ℂ) (hz : ∀ x : AddCircle T,
        z ≠ WL.synth (T:=T) a x) :
      ∃ b : WL.L1, ∀ x : AddCircle T,
        WL.synth (T:=T) b x = (z - WL.synth (T:=T) a x)⁻¹ :=
    WL.exists_resolvent_pointwise (T:=T) a z hz
  -- The remaining goal is the holomorphic-calculus construction from these
  -- resolvents on a neighbourhood of `spectrum ℂ a`. No coefficient or
  -- inverse-closedness assertion is being hidden here.
  -- The local case where one contour surrounds the spectrum is enough quite
  -- often (e.g. entire functions, or range in a disc of analyticity).  Using a
  -- canonical resolvent rather than the existential `hres` is important,
  -- since it varies continuously along the contour.
  by_cases hball : ∃ (c : ℂ) (R : ℝ), 0 < R ∧ Metric.closedBall c R ⊆ U ∧
      ∀ x : AddCircle T, WL.synth (T:=T) a x ∈ Metric.ball c R
  · rcases hball with ⟨c, R, hR, hd, hi⟩
    obtain ⟨b, hb⟩ :=
      WL.exists_calculus_circle (T:=T) a φ U hφ hR hd hi
    refine ⟨b, ?_⟩
    ext x
    change WL.synth (T:=T) b x = φ (f x)
    simpa [hrpoint x] using hb x
  · -- Even if the supplied neighbourhood is small, an *entire* function can
    -- use the large circle in `univ`; this deals in particular with ordinary
    -- power-series calculus without changing its domain in the statement.
    by_cases hentire : AnalyticOnNhd ℂ φ (Set.univ : Set ℂ)
    · let R : ℝ := ‖WL.synth (T:=T) a‖ + 1
      have hR : 0 < R := by
        dsimp [R]
        exact add_pos_of_nonneg_of_pos (norm_nonneg _) zero_lt_one
      have hi : ∀ x : AddCircle T,
          WL.synth (T:=T) a x ∈ Metric.ball (0:ℂ) R := by
        intro x
        rw [Metric.mem_ball, dist_zero_right]
        exact lt_of_le_of_lt (ContinuousMap.norm_coe_le_norm _ x)
          (lt_add_one _)
      have hd : Metric.closedBall (0:ℂ) R ⊆ (Set.univ : Set ℂ) :=
        Set.subset_univ _
      obtain ⟨b, hb⟩ :=
        WL.exists_calculus_circle (T:=T) a φ Set.univ hentire hR hd hi
      refine ⟨b, ?_⟩
      ext x
      change WL.synth (T:=T) b x = φ (f x)
      simpa [hrpoint x] using hb x
    · -- Only the scalar planar-chain assertion is left here.  All the
      -- Banach-algebra-valued integration follows functorially from it: paths
      -- in the resolvent carry the canonical continuous inverse.  Asking for
      -- velocities rather than a `C¹`-path structure is exactly what allows
      -- a grid of (horizontally and vertically parametrised) rectangle edges.
      -- Interior edges cancel.  On the outer edges the resolvent formula is
      -- pointwise evaluation.
      classical
      obtain ⟨n, γ, d, hγ, hd, hin, hr, hscalar⟩ :
          ∃ (n : ℕ) (γ d : Fin n → ℝ → ℂ),
            (∀ i, ContinuousOn (γ i) (Set.uIcc (0:ℝ) 1)) ∧
            (∀ i, ContinuousOn (d i) (Set.uIcc (0:ℝ) 1)) ∧
            (∀ i, Set.MapsTo (γ i) (Set.uIcc (0:ℝ) 1) U) ∧
            (∀ i, Set.MapsTo (γ i) (Set.uIcc (0:ℝ) 1)
              (resolventSet ℂ a)) ∧
            (∀ x : AddCircle T,
              ((2 * (Real.pi:ℂ) * Complex.I)⁻¹) *
                (∑ i : Fin n, ∫ t : ℝ in (0:ℝ)..1,
                  (d i t * φ (γ i t)) *
                    (γ i t - WL.synth (T:=T) a x)⁻¹) =
                φ (WL.synth (T:=T) a x)) := by
        -- this is now a purely *scalar* Cauchy-chain lemma.  The compact
        -- neighbourhood is harmless and can already be chosen once and for
        -- all; no regularity of `φ` outside it is ever requested.
        let F : AddCircle T → ℂ := fun x => WL.synth (T:=T) a x
        have hF : Continuous F := (WL.synth (T:=T) a).continuous
        have hK : IsCompact (Set.range F) := isCompact_range hF
        have hKU : Set.range F ⊆ U := by
          rintro z ⟨x, rfl⟩
          have hx : f x ∈ U := hrange ⟨x, rfl⟩
          simpa [F, hrpoint x] using hx
        obtain ⟨L, hL, hKL, hLU⟩ :=
          exists_compact_between hK hU hKU
        obtain ⟨δ, hδ0, hδ⟩ :=
          hK.exists_cthickening_subset_open isOpen_interior hKL
        -- `cthickening δ` is a genuine *closed* uniform buffer.  Small
        -- axis-parallel cells meeting the compact range can consequently be
        -- taken inside `interior L`; the boundary edges will still lie in
        -- `U` after one extra layer of cells.
        have offRange {z : ℂ} (hz : z ∉ Set.range F) :
            z ∈ resolventSet ℂ a := by
          apply (spectrum.notMem_iff).mp
          intro hs
          obtain ⟨x, hx⟩ :=
            (WL.mem_spectrum_iff_exists_point (T:=T) a z).1 hs
          exact hz ⟨x, hx⟩
        -- The missing assertion is therefore completely scalar/planar: tile
        -- the compact `L` by small closed rectangles, keep the cells in its
        -- interior which meet the range, and add their oriented boundary
        -- edges. Internal edges cancel. The outer edges are outside `range F`
        -- (hence `resolventSet` by
        -- `WL.mem_spectrum_iff_exists_point`) and are still in `U`.
        -- Cauchy--Goursat on the finitely many boxes gives the displayed
        -- scalar equality. No Banach-valued integral remains in this goal.
        -- Settle the elementary quantitative part of the grid construction.  In
        -- particular no local compactness or measurable choice of the
        -- centre of a little square will be needed below: there is a fixed
        -- finite net *whose centres belong to the compact range*. Points of
        -- a sufficiently small cell meeting that net are in the good open
        -- set.
        let ε : ℝ := δ / 20
        have hε : 0 < ε := by
          dsimp [ε]
          linarith
        have inBuffer {z w : ℂ} (hw : w ∈ Set.range F)
            (hzw : dist z w ≤ δ) : z ∈ U := by
          have h' := Metric.mem_cthickening_of_dist_le z w δ
            (Set.range F) hw hzw
          exact hLU (interior_subset (hδ h'))
        -- A useful strengthened, strict version.  The diagonal of a square of
        -- side `ε` is at most `2 ε`; the wasteful constant 20 leaves room
        -- both for the neighbouring cell and for taking its boundary.
        have cellBuffer {z w : ℂ} (hw : w ∈ Set.range F)
            (hzw : dist z w ≤ 4 * ε) : z ∈ U := by
          apply inBuffer hw
          refine hzw.trans ?_
          dsimp [ε]
          linarith
        obtain ⟨v, hv⟩ :=
          hK.elim_finite_subcover
            (fun w : {z : ℂ // z ∈ Set.range F} =>
              Metric.ball (w : ℂ) ε)
            (fun _ => Metric.isOpen_ball)
            (by
              intro z hz
              have hz' : z ∈ Metric.ball z ε :=
                Metric.mem_ball_self hε
              -- it is important here to index by the *range* and not by all
              -- of `ℂ`: boundary cells sharing an edge are then certified by
              -- the very same finite cover.
              exact Set.mem_iUnion.2
                ⟨(⟨z, hz⟩ : {q : ℂ // q ∈ Set.range F}), hz'⟩)
        -- Algebra of oriented boxes was separated from the Banach part.  The
        -- Goursat statement is available in the same coordinates as the box
        -- grid, including its countable-hole version (for the removable
        -- slope at a pole) and the normalisation for the central square.
        have hbox (r : ℝ) (hr : 0 < r) :
            WL.Planar.box (-r) r (-r) r (fun z : ℂ => z⁻¹) =
              (2 * (Real.pi:ℂ) * Complex.I) :=
          WL.Planar.box_inv_square r hr
        have hedge (p q : ℂ) :
            ContinuousOn (WL.Planar.edge p q) (Set.uIcc (0:ℝ) 1) ∧
            ContinuousOn (WL.Planar.edge' p q) (Set.uIcc (0:ℝ) 1) :=
          ⟨(WL.Planar.edge_continuous p q).continuousOn,
            (WL.Planar.edge'_continuous p q).continuousOn⟩
        have hedgeDist {p q : ℂ} {t : ℝ} (ht : t ∈ Set.uIcc (0:ℝ) 1) :
            dist (WL.Planar.edge p q t) p ≤ max (dist q p) (dist p q) := by
          rcases (Set.mem_uIcc.1 ht) with h | h
          · exact (WL.Planar.dist_edge_left h).trans (le_max_left _ _)
          · -- reversing the inequalities in `uIcc` here just means the
            -- endpoints are 0 and 1, so this case cannot actually be reversed.
            -- use the same ordered bounds after `simp`.
            have h' : t ∈ Set.Icc (0:ℝ) 1 := by
              -- both endpoints of this particular unoriented interval are ordered
              simpa using ht
            exact (WL.Planar.dist_edge_left h').trans (le_max_left _ _)
        -- What remains is combinatorial subdivision. Index small boxes
        -- `[mε,(m+1)ε] × [nε,(n+1)ε]` meeting the finite cover `hv`;
        -- include all cells whose closure meets `range F` and retain exactly
        -- the sides with the opposite neighbour absent. Such a side is
        -- disjoint from the range (otherwise that neighbour would also have
        -- been chosen), while `cellBuffer` puts the entire construction in
        -- `U`.  `Planar.box_split_vertical'` and
        -- `Planar.box_split_horizontal'` are the integral identities for the
        -- cancellation, `Planar.box_eq_zero_off` is Goursat on the other
        -- cells, and `hbox` fixes the one winding number.
        -- Use the actual finite square chain.  The boxes used here are exactly
        -- the closures meeting the compact range; unlike a ball subcover this
        -- makes every boundary edge disjoint from the range (a point on a common
        -- side would put the neighbouring cell in `S`).
        obtain ⟨S, hS⟩ := WL.Planar.finite_cells hε hK
        let B : Finset ((ℤ×ℤ) × WL.Planar.Side) := WL.Planar.boundary S
        let ι := {u // u ∈ B}
        let e : Fin (Fintype.card ι) ≃ ι :=
          (Fintype.equivFin ι).symm
        let gg : Fin (Fintype.card ι) → ℝ → ℂ := fun j =>
          WL.Planar.path ε (e j).1
        let vv : Fin (Fintype.card ι) → ℝ → ℂ := fun j =>
          WL.Planar.vel ε (e j).1
        refine ⟨Fintype.card ι, gg, vv, ?_, ?_, ?_, ?_, ?_⟩
        · intro j
          exact (WL.Planar.edge_continuous _ _).continuousOn
        · intro j
          exact (WL.Planar.edge'_continuous _ _).continuousOn
        · intro j
          have hm := WL.Planar.boundary_maps (s:=ε) hε
            (K:=Set.range F) (U:=U)
            (by
              intro z w hw hzw
              exact cellBuffer hw hzw)
            S hS (show (e j).1 ∈ WL.Planar.boundary S by exact (e j).2)
          intro t ht
          exact (hm ht).1
        · intro j
          have hm := WL.Planar.boundary_maps (s:=ε) hε
            (K:=Set.range F) (U:=U)
            (by
              intro z w hw hzw
              exact cellBuffer hw hzw)
            S hS (show (e j).1 ∈ WL.Planar.boundary S by exact (e j).2)
          intro t ht
          exact offRange (hm ht).2
        · -- At this point the planar target has no more covering or boundary
          -- selection in it.  It is the one scalar identity for the explicit
          -- finite square chain `boundary S`. Internal sides have already an
          -- algebraic cancellation lemma `WL.Planar.sum_boundary`; the
          -- remaining step is the residue of the one selected box.
          dsimp [gg, vv]
          intro x
          let w : ℂ := F x
          let q : ℂ → ℂ := fun z => φ z * (z - w)⁻¹
          have rewrite_one (u : (ℤ×ℤ) × WL.Planar.Side) :
              (∫ t : ℝ in (0:ℝ)..1,
                 (WL.Planar.vel ε u t * φ (WL.Planar.path ε u t)) *
                    (WL.Planar.path ε u t - WL.synth (T:=T) a x)⁻¹) =
                WL.Planar.edgeInt ε u q := by
            apply intervalIntegral.integral_congr
            intro t ht
            dsimp [WL.Planar.edgeInt, q, w, F]
            ring
          have hsums :
              (∑ j : Fin (Fintype.card ι), ∫ t : ℝ in (0:ℝ)..1,
                 (WL.Planar.vel ε (e j).1 t * φ (WL.Planar.path ε (e j).1 t)) *
                    (WL.Planar.path ε (e j).1 t - WL.synth (T:=T) a x)⁻¹) =
                ∑ u ∈ WL.Planar.boundary S, WL.Planar.edgeInt ε u q := by
            simp_rw [rewrite_one]
            calc
              (∑ j : Fin (Fintype.card ι), WL.Planar.edgeInt ε (e j).1 q) =
                   ∑ u : ι, WL.Planar.edgeInt ε u.1 q :=
                     Equiv.sum_comp e (fun u : ι => WL.Planar.edgeInt ε u.1 q)
              _ = _ := by
                simpa [ι, B] using
                  (Finset.sum_attach (WL.Planar.boundary S)
                    (fun u => WL.Planar.edgeInt ε u q))
          rw [hsums]
          -- Thus the sole outstanding calculation is a residue formula for
          -- an explicit finite boundary finset.  In particular no enumeration,
          -- maps-to, or compactness facts remain in the hole.
          change ((2 * (Real.pi:ℂ) * Complex.I)⁻¹) *
              (∑ u ∈ WL.Planar.boundary S,
                WL.Planar.edgeInt ε u q) = φ (WL.synth (T:=T) a x)
          have hxK : w ∈ Set.range F := by
            dsimp [w]
            exact ⟨x, rfl⟩
          have hcU : ∀ i ∈ S, WL.Planar.cell ε i ⊆ U := by
            intro i hi'
            apply WL.Planar.cell_subset_U_of_point (K:=Set.range F) (U:=U) hε (by
              intro z w hw hz
              exact cellBuffer hw hz)
            exact (hS i).1 hi'
          have hwU : w ∈ U := hKU hxK
          have key := WL.Planar.sum_boundary_cauchy hε S hS hcU hφ hxK hwU
          have kne : (2 * (Real.pi:ℂ) * Complex.I) ≠ 0 := by
            exact mul_ne_zero (mul_ne_zero (by norm_num) (by exact_mod_cast Real.pi_ne_zero))
              Complex.I_ne_zero
          dsimp [q, w, F] at key ⊢
          rw [key]
          field_simp
      obtain ⟨b, hb⟩ :=
        WL.exists_calculus_contours (T:=T) a φ U hφ γ d hγ hd hin hr hscalar
      refine ⟨b, ?_⟩
      ext x
      change WL.synth (T:=T) b x = φ (f x)
      simpa [hrpoint x] using hb x/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
