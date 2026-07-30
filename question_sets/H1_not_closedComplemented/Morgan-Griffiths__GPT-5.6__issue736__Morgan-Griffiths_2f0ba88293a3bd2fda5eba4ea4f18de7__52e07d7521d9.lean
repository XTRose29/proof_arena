import Mathlib

-- BEGIN INLINED FILE: Mathlib/Support/H1_not_closedComplemented_1b7e6bfda5/Basic.lean

set_option maxHeartbeats 800000

open scoped BigOperators ENNReal
open MeasureTheory Complex Set Function
open AddCircle ContinuousMap

namespace HardyAux

noncomputable section

abbrev μ1 : Measure (AddCircle (1:ℝ)) := AddCircle.haarAddCircle
abbrev X := Lp ℂ 1 μ1

/-- The exponential monomial on the circle of length one, as a continuous map. -/
abbrev e (n : ℤ) : C(AddCircle (1:ℝ), ℂ) := fourier (T:=(1:ℝ)) n
/-- Its class in `L^1`. -/
abbrev v (n : ℤ) : X := fourierLp (T:=(1:ℝ)) 1 n

lemma norm_e_point (n : ℤ) (x : AddCircle (1:ℝ)) : ‖e n x‖ = 1 :=
  Circle.norm_coe _

@[simp] lemma e_zero (x : AddCircle (1:ℝ)) : e 0 x = 1 := fourier_zero
@[simp] lemma e_eval_zero (n : ℤ) : e n (0 : AddCircle (1:ℝ)) = 1 := fourier_eval_zero n
lemma e_add (i j : ℤ) (x : AddCircle (1:ℝ)) : e (i+j) x = e i x * e j x :=
  fourier_add
lemma e_neg (i : ℤ) (x : AddCircle (1:ℝ)) : e (-i) x = (starRingEnd ℂ) (e i x) := fourier_neg

lemma coe_v (n : ℤ) :
    (v n : AddCircle (1:ℝ) → ℂ) =ᵐ[μ1] e n :=
  coeFn_fourierLp (T:=(1:ℝ)) 1 n

/-- Fourier coefficients of the `L^1` monomial. -/
lemma coeff_v (j : ℤ) :
    fourierCoeff (v j) = Pi.single j (1 : ℂ) := by
  rw [fourierCoeff_congr_ae (coe_v j)]
  exact fourierCoeff_fourier j

@[simp] lemma coeff_v_apply (j n : ℤ) : fourierCoeff (v j) n = if j = n then 1 else 0 := by
  rw [coeff_v j]
  classical
  by_cases h : j = n
  · subst n; simp
  · -- Pi.single j 1 n
    simp [Pi.single_apply, h]

/-- Integral of a character for normalized Haar measure. -/
lemma integral_e (n : ℤ) :
    (∫ x : AddCircle (1:ℝ), e n x ∂μ1) = if n = 0 then 1 else 0 := by
  have h := coeff_v_apply n 0
  -- compute coefficient zero directly on the continuous monomial
  have h' : fourierCoeff (e n : AddCircle (1:ℝ) → ℂ) 0 =
      (if n = 0 then 1 else 0) := by
    have hc := fourierCoeff_fourier (T := (1:ℝ)) n
    convert (congrFun hc 0) using 1 <;> classical
    by_cases hn : n = 0 <;> simp [Pi.single_apply, hn]
  -- coefficient 0 is integral, since the zero character is 1
  simpa [fourierCoeff, fourier_zero] using h'

/-- A finite Fourier polynomial, as a continuous function, with a chosen finite set of
coefficients. Coefficients outside the set play no role. Keeping the indexing as integers
makes the character identities painless. -/
noncomputable def poly (s : Finset ℤ) (a : ℤ → ℂ) : C(AddCircle (1:ℝ), ℂ) :=
  ∑ j ∈ s, a j • e j

@[simp] lemma poly_apply (s : Finset ℤ) (a : ℤ → ℂ) (t : AddCircle (1:ℝ)) :
    poly s a t = ∑ j ∈ s, a j * e j t := by
  classical
  simp [poly]

/-- The same polynomial regarded in `L^1`. -/
noncomputable def polyLp (s : Finset ℤ) (a : ℤ → ℂ) : X :=
  ContinuousMap.toLp (E:=ℂ) (μ:=μ1) (p:= (1:ℝ≥0∞)) ℂ (poly s a)

lemma coe_polyLp (s : Finset ℤ) (a : ℤ → ℂ) :
    (polyLp s a : AddCircle (1:ℝ) → ℂ) =ᵐ[μ1] poly s a := by
  simpa [polyLp] using (ContinuousMap.coeFn_toLp (E:=ℂ) (p:=(1:ℝ≥0∞))
    (𝕜:=ℂ) μ1 (poly s a))

lemma polyLp_eq_sum (s : Finset ℤ) (a : ℤ → ℂ) :
    polyLp s a = ∑ j ∈ s, a j • v j := by
  classical
  -- The continuous-to-Lp map is linear.
  change ContinuousMap.toLp (E:=ℂ) (μ:=μ1) (p:=(1:ℝ≥0∞)) ℂ (poly s a) = _
  simp [poly, v, map_sum]

/-- Rotating all characters by a point. This is written only for finite polynomials; no
continuity of the translation representation on `L^1` is needed below. -/
noncomputable def phase (s : Finset ℤ) (a : ℤ → ℂ) (x : AddCircle (1:ℝ)) :
    C(AddCircle (1:ℝ), ℂ) := poly s (fun j => a j * e j x)

lemma phase_apply (s : Finset ℤ) (a : ℤ → ℂ)
    (x t : AddCircle (1:ℝ)) :
    phase s a x t = poly s a (t + x) := by
  classical
  rw [phase]
  simp only [poly_apply]
  apply Finset.sum_congr rfl
  intro j hj
  have hchar : e j (t+x) = e j t * e j x := by
    change ((AddCircle.toCircle (j • (t+x) : AddCircle (1:ℝ)) : Circle) : ℂ) = _
    rw [zsmul_add, AddCircle.toCircle_add, Circle.coe_mul]
    rfl
  rw [hchar]
  ring


/-- Norm of a continuous polynomial in `L¹`. -/
lemma norm_polyLp (s : Finset ℤ) (a : ℤ → ℂ) :
    ‖polyLp s a‖ = ∫ t : AddCircle (1:ℝ), ‖poly s a t‖ ∂μ1 := by
  rw [MeasureTheory.L1.norm_eq_integral_norm]
  apply integral_congr_ae
  filter_upwards [coe_polyLp s a] with t ht
  rw [ht]

/-- Rotation does not change the L¹ norm of a finite polynomial. -/
lemma norm_phaseLp (s : Finset ℤ) (a : ℤ → ℂ) (x : AddCircle (1:ℝ)) :
    ‖polyLp s (fun j => a j * e j x)‖ = ‖polyLp s a‖ := by
  rw [norm_polyLp, norm_polyLp]
  have hpoint (t : AddCircle (1:ℝ)) :
      poly s (fun j => a j * e j x) t = poly s a (t+x) := phase_apply s a x t
  simp_rw [hpoint]
  exact MeasureTheory.integral_add_right_eq_self (fun t : AddCircle (1:ℝ) => ‖poly s a t‖) x

/-- Sup-norm estimate for a rotated continuous polynomial. -/
lemma norm_phase_le (s : Finset ℤ) (a : ℤ → ℂ) (x t : AddCircle (1:ℝ)) :
    ‖poly s (fun j => a j * e j x) t‖ ≤ ‖poly s a‖ := by
  change ‖phase s a x t‖ ≤ _
  rw [phase_apply s a x t]
  exact ContinuousMap.norm_coe_le_norm _ _

/-- Pairing an `L¹` vector with a continuous bounded function. -/
noncomputable def pair (u : X) (h : C(AddCircle (1:ℝ), ℂ)) : ℂ :=
  ∫ t : AddCircle (1:ℝ), u t * h t ∂μ1

lemma pair_bound (u : X) (h : C(AddCircle (1:ℝ), ℂ)) :
    ‖pair u h‖ ≤ ‖u‖ * ‖h‖ := by
  unfold pair
  -- dominate the integrand by the integrable function `‖u t‖ * ‖h‖`
  have hu : Integrable (fun t : AddCircle (1:ℝ) => ‖u t‖) μ1 :=
    (MeasureTheory.L1.integrable_coeFn u).norm
  have hg : Integrable (fun t : AddCircle (1:ℝ) => ‖u t‖ * ‖h‖) μ1 := hu.mul_const _
  have hdom : ∀ᵐ t ∂μ1, ‖u t * h t‖ ≤ ‖u t‖ * ‖h‖ :=
    Filter.Eventually.of_forall (fun t => by
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm h t) (norm_nonneg _))
  refine (norm_integral_le_of_norm_le hg hdom).trans ?_
  rw [integral_mul_const]
  rw [← MeasureTheory.L1.norm_eq_integral_norm]

/-- Pairing is linear in an `L¹` vector (proved by its integral formula). -/
lemma pair_add (u w : X) (h : C(AddCircle (1:ℝ), ℂ)) :
    pair (u+w) h = pair u h + pair w h := by
  unfold pair
  have hu : Integrable (fun t : AddCircle (1:ℝ) => u t) μ1 := MeasureTheory.L1.integrable_coeFn u
  have hw : Integrable (fun t : AddCircle (1:ℝ) => w t) μ1 := MeasureTheory.L1.integrable_coeFn w
  have hh : ∀ y, ‖h y‖ ≤ ‖h‖ := ContinuousMap.norm_coe_le_norm h
  have int_u : Integrable (fun t : AddCircle (1:ℝ) => u t * h t) μ1 := by
    exact hu.mul_bdd (map_continuous h).aestronglyMeasurable (Filter.Eventually.of_forall hh)
  have int_w : Integrable (fun t : AddCircle (1:ℝ) => w t * h t) μ1 := by
    exact hw.mul_bdd (map_continuous h).aestronglyMeasurable (Filter.Eventually.of_forall hh)
  rw [← integral_add int_u int_w]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.Lp.coeFn_add u w] with t ht
  change (u+w : X) t * h t = _
  rw [ht]
  change (u t + w t) * h t = _
  ring

lemma pair_smul (c : ℂ) (u : X) (h : C(AddCircle (1:ℝ), ℂ)) :
    pair (c • u) h = c * pair u h := by
  unfold pair
  change (∫ t : AddCircle (1:ℝ), (c • u : X) t * h t ∂μ1) = c • (∫ t : AddCircle (1:ℝ), u t * h t ∂μ1)
  rw [← integral_smul]
  apply integral_congr_ae
  filter_upwards [MeasureTheory.Lp.coeFn_smul c u] with t ht
  change (c • u : X) t * h t = _
  rw [ht]
  change (c * u t) * h t = c • (u t * h t)
  simp [mul_assoc]

lemma pair_add_right (u : X) (h k : C(AddCircle (1:ℝ), ℂ)) :
    pair u (h+k) = pair u h + pair u k := by
  unfold pair
  have hu : Integrable (fun t : AddCircle (1:ℝ) => u t) μ1 := MeasureTheory.L1.integrable_coeFn u
  have hh : ∀ y, ‖h y‖ ≤ ‖h‖ := ContinuousMap.norm_coe_le_norm h
  have hk : ∀ y, ‖k y‖ ≤ ‖k‖ := ContinuousMap.norm_coe_le_norm k
  have int_h : Integrable (fun t : AddCircle (1:ℝ) => u t * h t) μ1 := by
    exact hu.mul_bdd (map_continuous h).aestronglyMeasurable (Filter.Eventually.of_forall hh)
  have int_k : Integrable (fun t : AddCircle (1:ℝ) => u t * k t) μ1 := by
    exact hu.mul_bdd (map_continuous k).aestronglyMeasurable (Filter.Eventually.of_forall hk)
  rw [← integral_add int_h int_k]
  apply integral_congr_ae
  filter_upwards [] with t
  change u t * (h t + k t) = _
  ring

lemma pair_smul_right (u : X) (c : ℂ) (h : C(AddCircle (1:ℝ), ℂ)) :
    pair u (c • h) = c * pair u h := by
  unfold pair
  change (∫ t : AddCircle (1:ℝ), u t * (c • h) t ∂μ1) = c • (∫ t : AddCircle (1:ℝ), u t * h t ∂μ1)
  rw [← integral_smul]
  congr 1
  funext t
  change u t * (c * h t) = c • (u t * h t)
  ring

/-- Pairing with a character reads off a Fourier coefficient. -/
lemma pair_char (u : X) (m : ℤ) :
    pair u (e m) = fourierCoeff u (-m) := by
  unfold pair fourierCoeff
  -- the character in the coefficient is `m`.
  simp only [neg_neg, smul_eq_mul]
  congr 1
  funext t
  ring

lemma pair_poly_right (u : X) (s : Finset ℤ) (b : ℤ → ℂ) :
    pair u (poly s b) = ∑ j ∈ s, b j * fourierCoeff u (-j) := by
  classical
  -- finite linearity on the right
  unfold poly
  induction s using Finset.induction_on with
  | empty => simp [pair, fourierCoeff]
  | @insert j s hj ih =>
      -- expand the outer `∈` sum via simplification
      simp [Finset.sum_insert, hj, pair_add_right, pair_smul_right, pair_char, ih]

/-- Evaluation of a polynomial at zero is the sum of its coefficients. -/
lemma poly_at_zero (s : Finset ℤ) (a : ℤ → ℂ) :
    poly s a (0 : AddCircle (1:ℝ)) = ∑ j ∈ s, a j := by
  classical
  simp [poly_apply]

end
end HardyAux

-- END INLINED FILE: Mathlib/Support/H1_not_closedComplemented_1b7e6bfda5/Basic.lean

-- BEGIN INLINED FILE: Mathlib/Support/H1_not_closedComplemented_1b7e6bfda5/Projection.lean
set_option maxHeartbeats 1000000
open scoped BigOperators ENNReal
open MeasureTheory Complex Set Function
open AddCircle ContinuousMap
open HardyAux
namespace HardyAux
noncomputable section

lemma pair_map_poly_left (A : X →L[ℂ] X) (s : Finset ℤ) (a : ℤ → ℂ)
    (h : C(AddCircle (1:ℝ), ℂ)) :
    pair (A (polyLp s a)) h = ∑ j ∈ s, a j * pair (A (v j)) h := by
  classical
  rw [polyLp_eq_sum]
  -- first distribute the map
  simp_rw [map_sum, ContinuousLinearMap.map_smul]
  -- linearity of `pair` on the resulting finite sum
  induction s using Finset.induction_on with
  | empty => simp [pair]
  | @insert j s hj ih =>
    simp [Finset.sum_insert, hj, pair_add, pair_smul, ih]

lemma pair_map_poly (A : X →L[ℂ] X) (s t : Finset ℤ) (a b : ℤ → ℂ) :
    pair (A (polyLp s a)) (poly t b) =
      ∑ j ∈ s, ∑ k ∈ t, (a j * b k) * pair (A (v j)) (e k) := by
  classical
  rw [pair_map_poly_left]
  apply Finset.sum_congr rfl
  intro j hj
  rw [pair_poly_right]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro k hk
  rw [pair_char]
  ring

lemma continuous_integrable {f : AddCircle (1:ℝ) → ℂ} (hf : Continuous f) :
    Integrable f μ1 := by
  rw [← integrableOn_univ]
  exact ContinuousOn.integrableOn_compact isCompact_univ hf.continuousOn

/-- Integrating the two phase factors extracts the opposite frequencies.  Notice that no
continuity of the projection under rotations is used; we only rotate the *polynomials*. -/
lemma integrate_rotated_pair (A : X →L[ℂ] X) (s t : Finset ℤ) (a b : ℤ → ℂ) :
    (∫ x : AddCircle (1:ℝ),
       pair (A (polyLp s (fun j => a j * e j x)))
         (poly t (fun k => b k * e k x)) ∂μ1) =
      ∑ j ∈ s, ∑ k ∈ t,
        if j + k = 0 then (a j * b k) * pair (A (v j)) (e k) else 0 := by
  classical
  -- expand finite sums first
  simp_rw [pair_map_poly]
  -- move integrals past finite sums
  rw [integral_finset_sum]
  · -- outer
    apply Finset.sum_congr rfl
    intro j hj
    rw [integral_finset_sum]
    · apply Finset.sum_congr rfl
      intro k hk
      -- the integrand is just a character times a constant
      have hpoint (x : AddCircle (1:ℝ)) :
          ((a j * e j x) * (b k * e k x)) * pair (A (v j)) (e k)
            = (((a j * b k) * pair (A (v j)) (e k)) • (e (j+k) x)) := by
          -- scalar smul in ℂ
          change _ = ((a j * b k) * pair (A (v j)) (e k)) * e (j+k) x
          rw [e_add]
          ring
      simp_rw [hpoint]
      rw [integral_smul]
      rw [integral_e]
      split_ifs with hz
      · simp
      · simp
    · intro k hk
      -- integrability of each scalar multiple of a character
      have hc : Continuous (fun x : AddCircle (1:ℝ) =>
          ((a j * e j x) * (b k * e k x)) * pair (A (v j)) (e k)) := by
        fun_prop
      exact continuous_integrable hc
  · intro j hj
    -- before inner rewrite
    -- finite sum of continuous functions
    have hinner : Integrable (∑ k ∈ t, fun x : AddCircle (1:ℝ) =>
        ((a j * e j x) * (b k * e k x)) * pair (A (v j)) (e k)) μ1 := by
      apply integrable_finsetSum'
      intro k hk
      apply continuous_integrable
      fun_prop
    rw [Finset.sum_fn] at hinner
    exact hinner

/-- A convenient bound for the same integral. -/
lemma rotated_pair_bound (A : X →L[ℂ] X) (s t : Finset ℤ) (a b : ℤ → ℂ) :
    ‖(∫ x : AddCircle (1:ℝ),
       pair (A (polyLp s (fun j => a j * e j x)))
         (poly t (fun k => b k * e k x)) ∂μ1)‖
      ≤ (‖A‖ * ‖polyLp s a‖) * ‖poly t b‖ := by
  let C : ℝ := (‖A‖ * ‖polyLp s a‖) * ‖poly t b‖
  have hbound (x : AddCircle (1:ℝ)) :
      ‖pair (A (polyLp s (fun j => a j * e j x)))
         (poly t (fun k => b k * e k x))‖ ≤ C := by
    calc
      _ ≤ ‖A (polyLp s (fun j => a j * e j x))‖ *
            ‖poly t (fun k => b k * e k x)‖ := pair_bound _ _
      _ ≤ ((‖A‖ * ‖polyLp s (fun j => a j * e j x)‖) * ‖poly t b‖) := by
        have hA : ‖A (polyLp s (fun j => a j * e j x))‖ ≤
            ‖A‖ * ‖polyLp s (fun j => a j * e j x)‖ :=
          ContinuousLinearMap.le_opNorm _ _
        have hh : ‖poly t (fun k => b k * e k x)‖ ≤ ‖poly t b‖ := by
          -- pointwise bound gave only sup for evaluations; sup bound of a translation is also
          -- at most the original sup.
          rw [ContinuousMap.norm_eq_iSup_norm]
          refine ciSup_le ?_
          intro y
          exact norm_phase_le t b x y
        exact mul_le_mul hA hh (norm_nonneg _) (by positivity)
      _ = C := by rw [norm_phaseLp s a x]
  have main := norm_integral_le_of_norm_le_const (μ:=μ1)
      (f := fun x : AddCircle (1:ℝ) =>
        pair (A (polyLp s (fun j => a j * e j x)))
          (poly t (fun k => b k * e k x)))
      (C := C) (Filter.Eventually.of_forall hbound)
  -- the Haar measure is a probability measure
  simpa [C, measureReal_univ_eq_one] using main

/-- Abstract consequence for projections onto the nonnegative frequencies.  This is the
part of the argument that turns an arbitrary bounded projection into the forbidden Riesz
inequality on polynomials. -/
lemma diagonal_bound_of_analytic_projection
    (A : X →L[ℂ] X)
    (hfix : ∀ n : ℤ, 0 ≤ n → A (v n) = v n)
    (hneg : ∀ (u : X), ∀ n : ℤ, n < 0 → fourierCoeff (A u) n = 0)
    (s t : Finset ℤ) (a b : ℤ → ℂ) :
    ‖∑ j ∈ s, ∑ k ∈ t,
       if j + k = 0 ∧ 0 ≤ j then a j * b k else 0‖
       ≤ (‖A‖ * ‖polyLp s a‖) * ‖poly t b‖ := by
  classical
  have hmat {j k : ℤ} (hjk : j + k = 0) :
      pair (A (v j)) (e k) = if 0 ≤ j then 1 else 0 := by
    have hk : k = -j := by omega
    subst k
    by_cases hj : 0 ≤ j
    · rw [pair_char, hfix j hj]
      simp only [neg_neg]
      change fourierCoeff (v j) j = _
      rw [coeff_v_apply]
      simp [hj]
    · have hn : j < 0 := lt_of_not_ge hj
      have hz := hneg (v j) j hn
      simp [pair_char, hz, hj]
  have eqs :
      (∑ j ∈ s, ∑ k ∈ t,
         if j + k = 0 ∧ 0 ≤ j then a j * b k else 0)
       = ∑ j ∈ s, ∑ k ∈ t,
         if j + k = 0 then (a j * b k) * pair (A (v j)) (e k) else 0 := by
    apply Finset.sum_congr rfl
    intro j hj
    apply Finset.sum_congr rfl
    intro k hk
    by_cases hz : j + k = 0
    · rw [hmat hz]
      by_cases hp : 0 ≤ j
      · simp [hz, hp]
      · simp [hz, hp]
    · simp [hz]
  rw [eqs, ← integrate_rotated_pair A s t a b]
  exact rotated_pair_bound A s t a b

end
end HardyAux

-- END INLINED FILE: Mathlib/Support/H1_not_closedComplemented_1b7e6bfda5/Projection.lean

-- BEGIN INLINED FILE: Mathlib/Support/H1_not_closedComplemented_1b7e6bfda5/Counter.lean

open scoped BigOperators ENNReal
open MeasureTheory Complex Set Function
open AddCircle ContinuousMap

namespace HardyAux
noncomputable section

/-- Differences of two numbers in `0,...,L-1`.  This is the support of the elementary
Fejer kernel.  We keep this definition separate from `Icc`, which makes book-keeping
of the end points less painful. -/
def diffset (L : ℕ) : Finset ℤ :=
  Finset.image₂ (fun p q : ℕ => (p : ℤ) - (q : ℤ)) (Finset.range L) (Finset.range L)

lemma mem_diffset (L : ℕ) (p q : ℕ) (hp : p < L) (hq : q < L) :
    (p : ℤ) - (q : ℤ) ∈ diffset L := by
  classical
  exact Finset.mem_image₂.mpr ⟨p, Finset.mem_range.mpr hp, q,
    Finset.mem_range.mpr hq, rfl⟩

/-- The coefficients of the Fejer polynomial, written as a count of pairs.  This avoids
any ambiguity at the two end points and is quite convenient for changing the order of
three finite sums. -/
def Fcoef (L : ℕ) (j : ℤ) : ℂ :=
  (∑ p ∈ Finset.range L, ∑ q ∈ Finset.range L,
       if (p : ℤ) - (q : ℤ) = j then (1 : ℂ) else 0) / (L : ℂ)

private lemma group_diff_aux (L : ℕ) (x : AddCircle (1:ℝ)) :
    (∑ j ∈ diffset L,
        (∑ p ∈ Finset.range L, ∑ q ∈ Finset.range L,
          if (p : ℤ) - (q : ℤ) = j then (1 : ℂ) else 0) * e j x)
      = ∑ p ∈ Finset.range L, ∑ q ∈ Finset.range L,
          e ((p : ℤ) - (q : ℤ)) x := by
  classical
  -- move the two inner sums to the outside.  On the resulting singleton only one
  -- value of `j` remains.
  simp_rw [Finset.sum_mul]
  -- (((sum p (sum q ...)) inside each j) * ?) was distributed only over j? Need expand.
--  simp_rw [Finset.sum_mul]
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  conv_lhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro q hq
  -- the only surviving term of the `j` sum is the difference
  -- and it belongs to `diffset L`.
  classical
  have hmem : (p : ℤ) - (q : ℤ) ∈ diffset L :=
    mem_diffset L p q (Finset.mem_range.mp hp) (Finset.mem_range.mp hq)
  simp [hmem]
  --rw [Finset.sum_comm]

lemma Fejer_value (L : ℕ) (x : AddCircle (1:ℝ)) :
    poly (diffset L) (Fcoef L) x =
      ((∑ p ∈ Finset.range L, e (p:ℤ) x) *
        (starRingEnd ℂ) (∑ q ∈ Finset.range L, e (q:ℤ) x)) / (L : ℂ) := by
  classical
  rw [poly_apply]
  simp_rw [Fcoef]
  -- first group the equal differences
  calc
    _ = (∑ j ∈ diffset L,
        (∑ p ∈ Finset.range L, ∑ q ∈ Finset.range L,
          if (p : ℤ) - (q : ℤ) = j then (1 : ℂ) else 0) * e j x) / (L : ℂ) := by
          -- pull the real constant through the finite sum
          rw [Finset.sum_div]
          apply Finset.sum_congr rfl
          intro j hj
          -- field identity (a/L)*e = (a*e)/L
          ring
    _ = (∑ p ∈ Finset.range L, ∑ q ∈ Finset.range L,
        e ((p : ℤ) - (q : ℤ)) x) / (L : ℂ) := by
          rw [group_diff_aux]
    _ = _ := by
      congr 1
      -- distribute the conjugation and then the product
      simp_rw [map_sum]
      simp_rw [← e_neg]
      rw [Finset.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro p hp
      apply Finset.sum_congr rfl
      intro q hq
      rw [sub_eq_add_neg, e_add]
      

lemma Fejer_real (L : ℕ) (hL : 0 < L) (x : AddCircle (1:ℝ)) :
    poly (diffset L) (Fcoef L) x =
      ((Complex.normSq (∑ p ∈ Finset.range L, e (p:ℤ) x) / (L:ℝ) : ℝ) : ℂ) := by
  rw [Fejer_value]
  rw [Complex.mul_conj]
  norm_cast

lemma norm_Fejer_point (L : ℕ) (hL : 0 < L) (x : AddCircle (1:ℝ)) :
    ‖poly (diffset L) (Fcoef L) x‖ =
      Complex.normSq (∑ p ∈ Finset.range L, e (p:ℤ) x) / (L:ℝ) := by
  rw [Fejer_real L hL]
  rw [Complex.norm_real, Real.norm_eq_abs]
  exact abs_of_nonneg (div_nonneg (Complex.normSq_nonneg _) (Nat.cast_nonneg _))

lemma integral_Fejer (L : ℕ) (hL : 0 < L) :
    (∫ x : AddCircle (1:ℝ), poly (diffset L) (Fcoef L) x ∂μ1) = (1:ℂ) := by
  classical
  simp_rw [poly_apply]
  rw [integral_finset_sum]
  · -- each coefficient off zero integrates to zero
    have hzero : (0:ℤ) ∈ diffset L := mem_diffset L 0 0 hL hL
    -- the term j=0 is one
    have hc0 : Fcoef L 0 = (1:ℂ) := by
      unfold Fcoef
      -- only pairs with p=q contribute
      have hi : (∑ p ∈ Finset.range L, ∑ q ∈ Finset.range L,
           if (p : ℤ) - (q : ℤ) = 0 then (1:ℂ) else 0) = (L : ℂ) := by
        -- for fixed p just q=p
        calc
          _ = ∑ p ∈ Finset.range L, (1:ℂ) := by
            apply Finset.sum_congr rfl
            intro p hp
            -- sum has a single nonzero position
            classical
            have hp' : p ∈ Finset.range L := hp
            calc
              _ = ∑ q ∈ Finset.range L, if q = p then (1:ℂ) else 0 := by
                apply Finset.sum_congr rfl
                intro q hq
                by_cases he : q = p
                · subst q; simp
                · have hz : (q : ℤ) - (p : ℤ) ≠ 0 := by
                    intro hh
                    have : (q:ℤ) = (p:ℤ) := sub_eq_zero.mp hh
                    exact he (Int.ofNat_inj.mp this)
                  have hz' : (p : ℤ) - (q : ℤ) ≠ 0 := by
                    intro hh
                    have hhh : (p:ℤ) = (q:ℤ) := sub_eq_zero.mp hh
                    have hpq : p = q := Int.ofNat_inj.mp hhh
                    exact he hpq.symm
                  simp [he, hz']
              _ = (1:ℂ) := by simp [hp']
          _ = (L : ℂ) := by simp
      rw [hi]
      have hne : (L:ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hL)
      exact div_self hne
    -- identify the integral of every character
    -- rewrite each integrand as a scalar multiple
    simp_rw [← smul_eq_mul]
    simp_rw [integral_smul, integral_e]
    -- extract the entry at zero
    calc
      (∑ j ∈ diffset L, Fcoef L j • (if j = 0 then (1:ℂ) else 0)) =
          ∑ j ∈ diffset L, if j = 0 then (1:ℂ) else 0 := by
            apply Finset.sum_congr rfl
            intro j hj
            by_cases hz : j = 0
            · subst j; simp [hc0]
            · simp [hz]
      _ = (1:ℂ) := by simp [hzero]
  · intro j hj
    apply continuous_integrable
    fun_prop

lemma norm_FejerLp (L : ℕ) (hL : 0 < L) :
    ‖polyLp (diffset L) (Fcoef L)‖ = (1:ℝ) := by
  rw [norm_polyLp]
  have hc : ((∫ x : AddCircle (1:ℝ), ‖poly (diffset L) (Fcoef L) x‖ ∂μ1 : ℝ) : ℂ)
        = (1 : ℂ) := by
    calc
      ((↑(∫ x : AddCircle (1:ℝ), ‖poly (diffset L) (Fcoef L) x‖ ∂μ1) : ℂ)) =
        (∫ x : AddCircle (1:ℝ), (↑(‖poly (diffset L) (Fcoef L) x‖) : ℂ) ∂μ1) := by
          exact (integral_ofReal (𝕜 := ℂ)).symm
      _ = (∫ x : AddCircle (1:ℝ), poly (diffset L) (Fcoef L) x ∂μ1) := by
          congr 1
          funext x
          rw [norm_Fejer_point L hL, Fejer_real L hL]
      _ = (1:ℂ) := integral_Fejer L hL
  -- injectivity of the real inclusion
  exact_mod_cast hc

private lemma count_inner (L r q : ℕ) :
 (∑ p ∈ Finset.range L, if (p:ℤ) - (q:ℤ) = (r:ℤ) then (1:ℂ) else 0)
     = if q + r < L then (1:ℂ) else 0 := by
  classical
  have eqcond (p : ℕ) : ((p:ℤ) - (q:ℤ) = (r:ℤ)) ↔ p = q+r := by omega
  simp_rw [eqcond]
  by_cases h : q+r < L
  · simp only [if_pos h]
    rw [Finset.sum_boole]
    have heq : {p ∈ Finset.range L | p = q+r} = {q+r} := by
      ext p
      simp [h]
    simp [heq]
  · have hm : q+r ∉ Finset.range L := by simpa using h
    simp [h]

lemma Fcoef_nat (L r : ℕ) (hr : r ≤ L) :
    Fcoef L (r:ℤ) = (( (L-r : ℕ) : ℝ) / (L:ℝ) : ℝ) := by
  classical
  unfold Fcoef
  -- swap the two natural indices
  conv_lhs =>
    arg 1
    rw [Finset.sum_comm]
  -- count p for each q
  simp_rw [count_inner L r]
  have hcond (q : ℕ) : q + r < L ↔ q < L - r := by omega
  simp_rw [hcond]
  have hi : (∑ q ∈ Finset.range L, if q < L-r then (1:ℂ) else 0) =
      ((L-r : ℕ) : ℂ) := by
    rw [Finset.sum_boole]
    have heq : {q ∈ Finset.range L | q < L-r} = Finset.range (L-r) := by
      ext q
      simp only [Finset.mem_filter, Finset.mem_range]
      omega
    simp [heq]
  rw [hi]
  exact (Complex.ofReal_div _ _).symm

/-- Positive and negative, non-zero, indices. -/
def ipos (M : ℕ) : Finset ℤ := (Finset.range M).image (fun i : ℕ => ( (i+1 : ℕ) : ℤ))
def ineg (M : ℕ) : Finset ℤ := (Finset.range M).image (fun i : ℕ => - ( (i+1 : ℕ) : ℤ))
def sinsupp (M : ℕ) : Finset ℤ := ipos M ∪ ineg M

def Scoef (k : ℤ) : ℂ :=
  if 0 < k then - ( ((1:ℝ) / ( (Int.natAbs k : ℕ) : ℝ) : ℝ) : ℂ)
  else if k < 0 then (( (1:ℝ) / ((Int.natAbs k : ℕ) : ℝ) : ℝ) : ℂ)
  else 0

-- simpler unrestricted versions
private lemma posinj {a b : ℕ} (h : (((a+1:ℕ):ℤ)) = (b+1:ℕ)) : a = b := by omega
private lemma neginj {a b : ℕ} (h : (-((a+1:ℕ):ℤ)) = -((b+1:ℕ):ℤ)) : a=b := by omega

lemma Scoef_pos (n : ℕ) : Scoef ( (n+1 : ℕ) : ℤ) =
    - (((1:ℝ) / ((n+1:ℕ) : ℝ) : ℝ) : ℂ) := by
  have h : (0:ℤ) < ((n+1:ℕ):ℤ) := by exact_mod_cast Nat.succ_pos n
  rw [Scoef, if_pos h]
  have hh : (((n+1:ℕ):ℤ)).natAbs = n+1 := by
    change (Int.ofNat (n+1)).natAbs = _
    exact Int.natAbs_ofNat' _
  rw [hh]
lemma Scoef_neg (n : ℕ) : Scoef (- ((n+1 : ℕ) : ℤ)) =
    (((1:ℝ) / ((n+1:ℕ) : ℝ) : ℝ) : ℂ) := by
  have h : (-((n+1:ℕ):ℤ)) < (0:ℤ) := by exact neg_lt_zero.mpr (by exact_mod_cast Nat.succ_pos n)
  have hn : ¬(0:ℤ) < (-((n+1:ℕ):ℤ)) := by omega
  rw [Scoef, if_neg hn, if_pos h]
  rw [Int.natAbs_neg]
  have hh : (((n+1:ℕ):ℤ)).natAbs = n+1 := by
    change (Int.ofNat (n+1)).natAbs = _
    exact Int.natAbs_ofNat' _
  rw [hh]

lemma sin_value (M : ℕ) (x : AddCircle (1:ℝ)) :
   poly (sinsupp M) Scoef x =
    ∑ n ∈ Finset.range M,
      (((1:ℝ) / ((n+1:ℕ) : ℝ)) : ℂ) *
        (e (-((n+1:ℕ):ℤ)) x - e ((n+1:ℕ):ℤ) x) := by
  classical
  rw [poly_apply]
  -- split the two images
  have hd : Disjoint (ipos M) (ineg M) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk1
    obtain ⟨q, hq, hbad⟩ := Finset.mem_image.mp hk2
    have : (0:ℤ) < ((p+1:ℕ):ℤ) := by omega
    have : ((q+1:ℕ):ℤ) > 0 := by omega
    omega
  rw [sinsupp, Finset.sum_union hd]
  have hpos :
      (∑ k ∈ ipos M, Scoef k * e k x) =
        ∑ n ∈ Finset.range M,
          (- (((1:ℝ)/((n+1:ℕ):ℝ)) : ℂ)) * e ((n+1:ℕ):ℤ) x := by
    unfold ipos
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [Scoef_pos]
      push_cast
      rfl
    · intro u hu v hv he
      exact posinj he
  have hneg :
      (∑ k ∈ ineg M, Scoef k * e k x) =
        ∑ n ∈ Finset.range M,
          ((((1:ℝ)/((n+1:ℕ):ℝ)) : ℂ)) * e (-((n+1:ℕ):ℤ)) x := by
    unfold ineg
    rw [Finset.sum_image]
    · apply Finset.sum_congr rfl
      intro n hn
      rw [Scoef_neg]
      push_cast
      rfl
    · intro u hu v hv he
      exact neginj he
  rw [hpos, hneg]
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  ring
lemma e_natpow (x : AddCircle (1:ℝ)) (n : ℕ) : e (n:ℤ) x = (e 1 x) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ, e_add, ih]
    norm_num
    rw [pow_succ]

lemma e_neg_natpow (x : AddCircle (1:ℝ)) (n : ℕ) : e (- (n:ℤ)) x = ((starRingEnd ℂ) (e 1 x)) ^ n := by
  rw [e_neg]
  rw [e_natpow]
  exact (map_pow _ _ _)

lemma geom_bound (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z^n - 1‖ ≤ (n:ℝ) * ‖z-1‖ := by
  induction n with
  | zero => simp
  | succ n ih =>
    calc
      ‖z^(n+1) - 1‖ = ‖z^n * (z-1) + (z^n - 1)‖ := by congr 1; ring
      _ ≤ ‖z^n * (z-1)‖ + ‖z^n - 1‖ := norm_add_le _ _
      _ ≤ ‖z^n * (z-1)‖ + (n:ℝ) * ‖z-1‖ := by linarith
      _ = ((n+1:ℕ):ℝ) * ‖z-1‖ := by
        rw [norm_mul, norm_pow, hz]
        push_cast
        ring

lemma unit_star_dist (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(starRingEnd ℂ) z - 1‖ = ‖z-1‖ := by
  -- conjugation is an isometry
  calc
    _ = ‖(starRingEnd ℂ) (z-1)‖ := by rw [map_sub, map_one]
    _ = _ := Complex.norm_conj _

lemma diagonal_Fejer_sin (L M : ℕ) (hML : M < L) :
  (∑ j ∈ diffset L, ∑ k ∈ sinsupp M,
     if j+k=0 ∧ 0 ≤ j then Fcoef L j * Scoef k else 0)
    = ∑ n ∈ Finset.range M,
       ((( (L-(n+1) : ℕ) : ℝ)/(L:ℝ) * (1 / ((n+1:ℕ):ℝ))) : ℝ) := by
  classical
  -- swap the order
  conv_lhs => rw [Finset.sum_comm]
  have extract (k : ℤ) :
      (∑ j ∈ diffset L,
        if j+k=0 ∧ 0 ≤ j then Fcoef L j * Scoef k else 0) =
        if ((-k) ∈ diffset L ∧ (0:ℤ) ≤ -k) then
          Fcoef L (-k) * Scoef k else 0 := by
      by_cases hm : -k ∈ diffset L
      · -- there is at most this position
        calc
          _ = ∑ j ∈ diffset L, if j = -k ∧ 0 ≤ -k then
                Fcoef L j * Scoef k else 0 := by
              apply Finset.sum_congr rfl
              intro j hj
              by_cases hz : j + k = 0
              · have he : j = -k := by omega
                subst j; simp
              · have he : j ≠ -k := by omega
                simp [hz, he]
          _ = _ := by
              by_cases hk : (0:ℤ) ≤ -k
              · have hk' : k ≤ 0 := by omega
                simp [hm, hk']
              · have hk' : ¬ k ≤ 0 := by omega
                simp [hm, hk']
      · have hm' : ¬ ((-k) ∈ diffset L ∧ (0:ℤ) ≤ -k) := by simp [hm]
        rw [if_neg hm']
        apply Finset.sum_eq_zero
        intro j hj
        have hne : j+k ≠ 0 := by
          intro hh; have he : j = -k := by omega
          exact hm (he ▸ hj)
        simp [hne]
  simp_rw [extract]
  -- split signs
  have hd : Disjoint (ipos M) (ineg M) := by
    rw [Finset.disjoint_left]
    intro k hk1 hk2
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hk1
    obtain ⟨q, hq, hbad⟩ := Finset.mem_image.mp hk2
    have hp0 : (0:ℤ) < ((p+1:ℕ):ℤ) := by omega
    have hq0 : (0:ℤ) < ((q+1:ℕ):ℤ) := by omega
    omega
  rw [sinsupp, Finset.sum_union hd]
  -- the positive half vanishes
  have hzpos : (∑ k ∈ ipos M,
       if -k ∈ diffset L ∧ (0:ℤ) ≤ -k then Fcoef L (-k) * Scoef k else 0)
       = 0 := by
    apply Finset.sum_eq_zero
    intro k hk
    obtain ⟨n, hn, rfl⟩ := Finset.mem_image.mp hk
    have hbad : ¬ ( (0:ℤ) ≤ - (((n+1:ℕ):ℤ)) ) := by
      change ¬ ( (0:ℤ) ≤ -( ((n+1:ℕ):ℤ)))
      omega
    have hbad' : ¬( - (((n+1:ℕ):ℤ)) ∈ diffset L ∧ (0:ℤ) ≤ - (((n+1:ℕ):ℤ)) ) := by
      intro hh; exact hbad hh.2
    rw [if_neg]
    change ¬( - (((n+1:ℕ):ℤ)) ∈ diffset L ∧ (0:ℤ) ≤ - (((n+1:ℕ):ℤ)) )
    exact hbad'
  rw [hzpos, zero_add]
  unfold ineg
  rw [Finset.sum_image]
  · push_cast
    apply Finset.sum_congr rfl
    intro n hn
    have hnlt : n < M := Finset.mem_range.mp hn
    have hnL : n+1 ≤ L := by omega
    have hnmem : ((n+1:ℕ):ℤ) ∈ diffset L := by
       -- at the endpoint equality coefficient is zero but the pair p=L is absent.
       by_cases eqend : n+1 = L
       · -- impossible since n<M and M≤L
         omega
       · have hstrict : n+1 < L := by omega
         exact mem_diffset L (n+1) 0 hstrict (by omega)
    have hnnon : (0:ℤ) ≤ ((n+1:ℕ):ℤ) := by omega
    have hnegneg : - (-((n+1:ℕ):ℤ)) = ((n+1:ℕ):ℤ) := by ring
    -- Reduce the double negative before using the indicator.
    simp only [neg_neg]
    change (if (((n+1:ℕ):ℤ) ∈ diffset L ∧ (0:ℤ) ≤ ((n+1:ℕ):ℤ)) then
       Fcoef L ((n+1:ℕ):ℤ) * Scoef (-((n+1:ℕ):ℤ)) else 0) = _
    rw [if_pos ⟨hnmem, hnnon⟩]
    rw [Fcoef_nat L (n+1) hnL, Scoef_neg]
    push_cast
    ring

  · intro a ha b hb hab
    exact neginj hab

end
end HardyAux

-- END INLINED FILE: Mathlib/Support/H1_not_closedComplemented_1b7e6bfda5/Counter.lean

-- BEGIN INLINED FILE: Mathlib/Support/H1_not_closedComplemented_1b7e6bfda5/SineBound.lean

open scoped BigOperators ENNReal
open MeasureTheory Complex Set Function
open AddCircle ContinuousMap

namespace HardyAux
noncomputable section

/-- The elementary geometric identity, with an arbitrary initial exponent.
Writing it with `range` makes it a convenient Dirichlet bound later on. -/
lemma geom_interval (z : ℂ) (a k : ℕ) :
    (z - 1) * (∑ i ∈ Finset.range k, z ^ (a + i)) = z ^ (a + k) - z ^ a := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ]
    simp only [mul_add, ih]
    -- the last two powers telescope
    ring_nf
    -- `ring` knows the successor power law after this rewrite.

/-- A geometric block on the unit circle has norm at most `2 / ‖z-1‖`.
The assertion is also true for its conjugate (apply with that `z`). -/
lemma norm_geom_interval (z : ℂ) (hz : ‖z‖ = (1:ℝ))
    (hd : 0 < ‖z-1‖) (a k : ℕ) :
    ‖∑ i ∈ Finset.range k, z ^ (a+i)‖ ≤ (2:ℝ) / ‖z-1‖ := by
  have hiden := geom_interval z a k
  have hmul : ‖z-1‖ * ‖∑ i ∈ Finset.range k, z ^ (a+i)‖
        = ‖z ^ (a+k) - z^a‖ := by
    rw [← norm_mul]
    rw [hiden]
  have hle : ‖z ^ (a+k) - z^a‖ ≤ (2:ℝ) := by
    calc
      ‖z ^ (a+k) - z^a‖ ≤ ‖z ^ (a+k)‖ + ‖z^a‖ := norm_sub_le _ _
      _ = (2:ℝ) := by rw [norm_pow, norm_pow, hz]; norm_num
  apply (le_div_iff₀ hd).2
  -- switch the order of the product to match the lemma above
  calc
    ‖∑ i ∈ Finset.range k, z ^ (a+i)‖ * ‖z-1‖
        = ‖z-1‖ * ‖∑ i ∈ Finset.range k, z ^ (a+i)‖ := by ring
    _ = ‖z ^ (a+k) - z^a‖ := hmul
    _ ≤ (2:ℝ) := hle

/-- The (unweighted) blocks appearing in the sine polynomial have bounded
partial sums. -/
lemma norm_diff_interval (z : ℂ) (hz : ‖z‖ = (1:ℝ))
    (hd : 0 < ‖z-1‖) (a k : ℕ) :
    ‖∑ i ∈ Finset.range k,
        ((starRingEnd ℂ z) ^ (a+i) - z ^ (a+i))‖ ≤ (4:ℝ) / ‖z-1‖ := by
  have hcz : ‖(starRingEnd ℂ) z‖ = (1:ℝ) := by
    simpa [Complex.norm_conj] using hz
  have hdcz : 0 < ‖(starRingEnd ℂ) z - 1‖ := by
    rw [unit_star_dist z hz]
    exact hd
  have hp := norm_geom_interval z hz hd a k
  have hc := norm_geom_interval ((starRingEnd ℂ) z) hcz hdcz a k
  rw [unit_star_dist z hz] at hc
  rw [Finset.sum_sub_distrib]
  calc
    ‖(∑ i ∈ Finset.range k, (starRingEnd ℂ z) ^ (a+i)) -
        (∑ i ∈ Finset.range k, z ^ (a+i))‖
        ≤ ‖∑ i ∈ Finset.range k, (starRingEnd ℂ z) ^ (a+i)‖ +
          ‖∑ i ∈ Finset.range k, z ^ (a+i)‖ := norm_sub_le _ _
    _ ≤ (2:ℝ) / ‖z-1‖ + (2:ℝ) / ‖z-1‖ := add_le_add hc hp
    _ = (4:ℝ) / ‖z-1‖ := by ring

end
end HardyAux

namespace HardyAux
noncomputable section

/-- The `n`-th term (where `n` starts at zero) of the harmonic sine sum,
written as a real scalar multiple. -/
def hterm (z : ℂ) (n : ℕ) : ℂ :=
  ((1:ℝ) / ((n+1:ℕ):ℝ)) •
    ((starRingEnd ℂ z) ^ (n+1) - z ^(n+1))

lemma norm_hterm_le (z : ℂ) (hz : ‖z‖ = (1:ℝ)) (n : ℕ) :
    ‖hterm z n‖ ≤ (2:ℝ) * ‖z-1‖ := by
  let d : ℝ := ‖z-1‖
  have hcz : ‖(starRingEnd ℂ) z‖ = (1:ℝ) := by
    simpa [Complex.norm_conj] using hz
  have A := geom_bound z hz (n+1)
  have B := geom_bound ((starRingEnd ℂ) z) hcz (n+1)
  rw [unit_star_dist z hz] at B
  have hw : ‖(starRingEnd ℂ z) ^ (n+1) - z^(n+1)‖
        ≤ (2:ℝ) * ((n+1:ℕ):ℝ) * ‖z-1‖ := by
    calc
      ‖(starRingEnd ℂ z) ^ (n+1) - z^(n+1)‖
          ≤ ‖(starRingEnd ℂ z)^(n+1) - 1‖ + ‖z^(n+1) - 1‖ := by
              -- subtract the same midpoint
              calc
                _ = ‖((starRingEnd ℂ z)^(n+1) - 1) - (z^(n+1)-1)‖ := by ring_nf
                _ ≤ _ := norm_sub_le _ _
      _ ≤ ((n+1:ℕ):ℝ) * ‖z-1‖ + ((n+1:ℕ):ℝ) * ‖z-1‖ :=
            add_le_add B A
      _ = (2:ℝ) * ((n+1:ℕ):ℝ) * ‖z-1‖ := by ring
  unfold hterm
  rw [norm_smul]
  rw [Real.norm_eq_abs, abs_of_nonneg (div_nonneg (by norm_num)
            (by exact_mod_cast (Nat.zero_le (n+1))))]
  -- cancel the positive integer denominator
  have hn : (0:ℝ) < ((n+1:ℕ):ℝ) := by exact_mod_cast (Nat.succ_pos n)
  calc
    ((1:ℝ) / ((n+1:ℕ):ℝ)) *
        ‖(starRingEnd ℂ z) ^ (n+1) - z^(n+1)‖
      ≤ ((1:ℝ) / ((n+1:ℕ):ℝ)) *
        ((2:ℝ) * ((n+1:ℕ):ℝ) * ‖z-1‖) :=
            mul_le_mul_of_nonneg_left hw (by positivity)
    _ = (2:ℝ) * ‖z-1‖ := by field_simp

lemma norm_hsum_prefix (z : ℂ) (hz : ‖z‖ = (1:ℝ)) (K : ℕ) :
    ‖∑ n ∈ Finset.range K, hterm z n‖ ≤
       (2:ℝ) * (K:ℝ) * ‖z-1‖ := by
  calc
    ‖∑ n ∈ Finset.range K, hterm z n‖
        ≤ ∑ n ∈ Finset.range K, ‖hterm z n‖ := norm_sum_le _ _
    _ ≤ ∑ _n ∈ Finset.range K, ((2:ℝ) * ‖z-1‖) := by
          exact Finset.sum_le_sum fun i hi => norm_hterm_le z hz i
    _ = (2:ℝ) * (K:ℝ) * ‖z-1‖ := by
          simp
          ring

end
end HardyAux

namespace HardyAux
noncomputable section
open scoped BigOperators

/-- Dirichlet (or Abel summation) estimate for the tail of the harmonic sum.
It is important that the right hand side depends only on the *first* denominator. -/
lemma norm_hsum_tail (z : ℂ) (hz : ‖z‖ = (1:ℝ))
    (hd : 0 < ‖z-1‖) (N T : ℕ) :
    ‖∑ i ∈ Finset.range T, hterm z (N+i)‖
       ≤ ((4:ℝ) / ‖z-1‖) * (1 / ((N+1:ℕ):ℝ)) := by
  classical
  by_cases hT : T = 0
  · subst T
    simp
    positivity
  let f : ℕ → ℝ := fun i => (1:ℝ) / ((N+i+1:ℕ):ℝ)
  let g : ℕ → ℂ := fun i =>
    ((starRingEnd ℂ z) ^ (N+i+1) - z ^ (N+i+1))
  let B : ℝ := (4:ℝ) / ‖z-1‖
  have hf0 (i : ℕ) : 0 ≤ f i := by
    dsimp [f]
    positivity
  have hfmono (i : ℕ) : f (i+1) ≤ f i := by
    dsimp [f]
    apply one_div_le_one_div_of_le
    · exact_mod_cast (Nat.succ_pos (N+i))
    · exact_mod_cast (show N+i+1 ≤ N+(i+1)+1 by omega)
  have hG (k : ℕ) : ‖∑ i ∈ Finset.range k, g i‖ ≤ B := by
    have hh := norm_diff_interval z hz hd (N+1) k
    -- the two descriptions of the exponents differ only by associativity
    simpa [g, B, add_assoc, add_left_comm, add_comm] using hh
  have hterm' (i : ℕ) : hterm z (N+i) = f i • g i := by
    dsimp [hterm, f, g]
  have hmain : ‖f (T-1) • (∑ i ∈ Finset.range T, g i)‖ ≤
        f (T-1) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hf0 _)]
    exact mul_le_mul_of_nonneg_left (hG T) (hf0 _)
  have hpiece (i : ℕ) :
      ‖(f (i+1) - f i) • (∑ j ∈ Finset.range (i+1), g j)‖
          ≤ (f i - f (i+1)) * B := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonpos (sub_nonpos.mpr (hfmono i))]
    have he : -(f (i+1) - f i) = f i - f (i+1) := by ring
    rw [he]
    exact mul_le_mul_of_nonneg_left (hG (i+1)) (sub_nonneg.mpr (hfmono i))
  calc
    ‖∑ i ∈ Finset.range T, hterm z (N+i)‖
        = ‖∑ i ∈ Finset.range T, f i • g i‖ := by
            congr 2
    _ = ‖f (T-1) • (∑ i ∈ Finset.range T, g i) -
            ∑ i ∈ Finset.range (T-1),
              (f (i+1) - f i) • (∑ j ∈ Finset.range (i+1), g j)‖ := by
            rw [Finset.sum_range_by_parts f g T]
    _ ≤ ‖f (T-1) • (∑ i ∈ Finset.range T, g i)‖ +
          ‖∑ i ∈ Finset.range (T-1),
              (f (i+1) - f i) • (∑ j ∈ Finset.range (i+1), g j)‖ :=
            norm_sub_le _ _
    _ ≤ ‖f (T-1) • (∑ i ∈ Finset.range T, g i)‖ +
          ∑ i ∈ Finset.range (T-1),
            ‖(f (i+1) - f i) • (∑ j ∈ Finset.range (i+1), g j)‖ := by
            exact add_le_add_right (norm_sum_le _ _) _
    _ ≤ f (T-1) * B +
          ∑ i ∈ Finset.range (T-1), ((f i - f (i+1)) * B) := by
            exact add_le_add hmain (Finset.sum_le_sum fun i hi => hpiece i)
    _ = f 0 * B := by
          rw [← Finset.sum_mul]
          rw [Finset.sum_range_sub']
          ring
    _ = ((4:ℝ) / ‖z-1‖) * (1 / ((N+1:ℕ):ℝ)) := by
          dsimp [f, B]
          ring

end
end HardyAux

namespace HardyAux
noncomputable section
open scoped BigOperators

/-- Uniform Dirichlet bound for the finite harmonic sine sums on the unit circle.
A very generous constant is useful, since no sharp estimate is needed. -/
lemma norm_hsum_le (z : ℂ) (hz : ‖z‖ = (1:ℝ)) (M : ℕ) :
    ‖∑ n ∈ Finset.range M, hterm z n‖ ≤ (10:ℝ) := by
  classical
  let d : ℝ := ‖z-1‖
  by_cases hd0 : d = 0
  · have hp := norm_hsum_prefix z hz M
    have hd' : ‖z-1‖ = (0:ℝ) := hd0
    rw [hd'] at hp
    norm_num at hp
    rw [hp]
    norm_num
  have hd : 0 < ‖z-1‖ := by
    change 0 < d
    exact lt_of_le_of_ne (norm_nonneg _) (Ne.symm hd0)
  let N : ℕ := ⌊(1:ℝ) / ‖z-1‖⌋₊
  have hN : (N:ℝ) ≤ (1:ℝ) / ‖z-1‖ := by
    dsimp [N]
    exact Nat.floor_le (by positivity)
  have hNd : (N:ℝ) * ‖z-1‖ ≤ (1:ℝ) :=
    (le_div_iff₀ hd).mp hN
  have hsucc : (1:ℝ) / ‖z-1‖ < (N:ℝ) + 1 := by
    have hh := (Nat.lt_floor_add_one ((1:ℝ) / ‖z-1‖))
    exact_mod_cast hh
  have hprod' : (1:ℝ) < ((N:ℝ) + 1) * ‖z-1‖ :=
    (div_lt_iff₀ hd).mp hsucc
  have hprod : (1:ℝ) ≤ ‖z-1‖ * ((N+1:ℕ):ℝ) := by
    have hcast : ((N+1:ℕ):ℝ) = (N:ℝ) + 1 := by push_cast; ring
    rw [hcast]
    nlinarith
  by_cases hMN : M ≤ N
  · have hp := norm_hsum_prefix z hz M
    have hMd : (M:ℝ) * ‖z-1‖ ≤ 1 :=
      le_trans (mul_le_mul_of_nonneg_right (by exact_mod_cast hMN)
          (norm_nonneg _)) hNd
    calc
      ‖∑ n ∈ Finset.range M, hterm z n‖
          ≤ (2:ℝ) * (M:ℝ) * ‖z-1‖ := hp
      _ ≤ (10:ℝ) := by nlinarith
  · have hNM : N < M := lt_of_not_ge hMN
    have hsplit :
        (∑ n ∈ Finset.range M, hterm z n) =
          (∑ n ∈ Finset.range N, hterm z n) +
            ∑ i ∈ Finset.range (M-N), hterm z (N+i) := by
        rw [← Finset.sum_range_add]
        rw [Nat.add_sub_of_le (Nat.le_of_lt hNM)]
    have hp := norm_hsum_prefix z hz N
    have hp' : ‖∑ n ∈ Finset.range N, hterm z n‖ ≤ (2:ℝ) := by
      calc
        _ ≤ (2:ℝ) * (N:ℝ) * ‖z-1‖ := hp
        _ ≤ (2:ℝ) := by nlinarith
    have ht := norm_hsum_tail z hz hd N (M-N)
    have hboundtail : ((4:ℝ) / ‖z-1‖) * (1 / ((N+1:ℕ):ℝ))
            ≤ (4:ℝ) := by
      have hiden : ((4:ℝ) / ‖z-1‖) * (1 / ((N+1:ℕ):ℝ)) =
          (4:ℝ) / (‖z-1‖ * ((N+1:ℕ):ℝ)) := by ring
      rw [hiden]
      exact div_le_self (by norm_num) hprod
    have ht' : ‖∑ i ∈ Finset.range (M-N), hterm z (N+i)‖ ≤ (4:ℝ) :=
      ht.trans hboundtail
    rw [hsplit]
    calc
      ‖(∑ n ∈ Finset.range N, hterm z n) +
          ∑ i ∈ Finset.range (M-N), hterm z (N+i)‖
        ≤ ‖∑ n ∈ Finset.range N, hterm z n‖ +
          ‖∑ i ∈ Finset.range (M-N), hterm z (N+i)‖ := norm_add_le _ _
      _ ≤ (10:ℝ) := by linarith

end
end HardyAux

namespace HardyAux
noncomputable section
open scoped BigOperators

lemma sinpoly_hsum (M : ℕ) (x : AddCircle (1:ℝ)) :
    poly (sinsupp M) Scoef x =
       ∑ n ∈ Finset.range M, hterm (e 1 x) n := by
  classical
  rw [sin_value]
  apply Finset.sum_congr rfl
  intro n hn
  rw [e_natpow x (n+1), e_neg_natpow x (n+1)]
  simp [hterm, Complex.real_smul]

/-- The companion polynomial is uniformly bounded, independently of its length.
This is the Abel--Dirichlet estimate. -/
lemma norm_sinpoly_le (M : ℕ) :
    ‖poly (sinsupp M) Scoef‖ ≤ (10:ℝ) := by
  classical
  apply (ContinuousMap.norm_le _ (by norm_num)).2
  intro x
  rw [sinpoly_hsum]
  apply norm_hsum_le
  exact norm_e_point 1 x

end
end HardyAux

namespace HardyAux
noncomputable section
open scoped BigOperators

/-- In an odd Fejer polynomial the first `M` coefficients retain at least
one half of their mass. -/
lemma Fejer_diag_lower (M : ℕ) :
    ( (1:ℝ) / 2) *
       (∑ n ∈ Finset.range M, (1 / ((n+1:ℕ):ℝ)))
       ≤ ∑ n ∈ Finset.range M,
            (((((2*M+1) - (n+1) : ℕ) : ℝ) /
                ((2*M+1:ℕ):ℝ)) * (1 / ((n+1:ℕ):ℝ))) := by
  classical
  have hL : (0:ℝ) < ((2*M+1:ℕ):ℝ) := by exact_mod_cast (by omega : 0 < 2*M+1)
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro n hn
  have hnlt : n < M := Finset.mem_range.mp hn
  have hnrpos : (0:ℝ) ≤ (1 / ((n+1:ℕ):ℝ)) := by positivity
  apply mul_le_mul_of_nonneg_right _ hnrpos
  -- clear the positive denominator `2*M+1`
  apply (le_div_iff₀ hL).2
  have hsub : n+1 ≤ 2*M+1 := by omega
  have hnle : (n:ℝ) + 1 ≤ (M:ℝ) := by exact_mod_cast (Nat.succ_le_of_lt hnlt)
  rw [Nat.cast_sub hsub]
  push_cast
  nlinarith

end
end HardyAux

-- END INLINED FILE: Mathlib/Support/H1_not_closedComplemented_1b7e6bfda5/SineBound.lean

namespace Submission

-- BEGIN INLINED FILE: Main.lean

namespace LeanEval
namespace Analysis

/-!
# Nonexistence of bounded projections from `L^1` onto `H^1`

The Hardy space `H^1` consists of those `L^1` functions on the unit circle whose
negative Fourier coefficients vanish. D. J. Newman showed that there is no bounded
linear projection from `L^1` onto `H^1`. The theorem below phrases the result
using `Submodule.ClosedComplemented`.
-/

open MeasureTheory Submodule

/-- The boundary Hardy space `H^1`: those `L^1` functions whose negative Fourier
coefficients vanish. -/
def H1 : Submodule ℂ (Lp ℂ 1 (AddCircle.haarAddCircle (T := 1))) where
  carrier := {f | ∀ n : ℤ, n < 0 → fourierCoeff f n = 0}
  zero_mem' := by simp [fourierCoeff]
  add_mem' := by
    intro f g hf hg n hn
    rw [fourierCoeff_congr_ae (Lp.coeFn_add f g),
      fourierCoeff.add (L1.integrable_coeFn f) (L1.integrable_coeFn g)]
    simp_all
  smul_mem' := by
    intro c f n hn
    rw [fourierCoeff_congr_ae (Lp.coeFn_smul c f), fourierCoeff.const_smul]
    simp_all



end Analysis
end LeanEval

open LeanEval.Analysis
open MeasureTheory Submodule
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/

/-ResultBegin-/

theorem H1_not_closedComplemented :
    ¬ H1.ClosedComplemented :=
/-ResultProofBegin-/by
  classical
  intro hp
  rcases hp with ⟨P, hP⟩
  -- compose with the subtype to obtain an honest operator on `L¹`.
  let A : HardyAux.X →L[ℂ] HardyAux.X :=
    (H1.subtypeL : H1 →L[ℂ] HardyAux.X).comp P
  have hfix (n : ℤ) (hn : 0 ≤ n) : A (HardyAux.v n) = HardyAux.v n := by
    -- nonnegative characters lie in the Hardy subspace
    have hv : HardyAux.v n ∈ H1 := by
      intro k hk
      rw [HardyAux.coeff_v_apply]
      split_ifs with hkn
      · subst k; omega
      · exact rfl
    let u : H1 := ⟨HardyAux.v n, hv⟩
    change (H1.subtypeL) (P (HardyAux.v n)) = HardyAux.v n
    have hu : P u = u := hP u
    -- coercing the equality in the subspace
    have := congrArg (fun z : H1 => (z : HardyAux.X)) hu
    exact this
  have hneg (u : HardyAux.X) (n : ℤ) (hn : n < 0) :
      fourierCoeff (A u) n = 0 := by
    change fourierCoeff ((H1.subtypeL) (P u)) n = 0
    exact (P u).property n hn
  -- Only a classical elementary lemma about trigonometric polynomials remains: the
  -- one-sided diagonal functional is not bounded for the `L¹` norm.  All reduction from
  -- an arbitrary bounded projection is the rotation argument above, which takes place on
  -- finite polynomials.
  have no_diagonal :
      ∀ C : ℝ, ∃ (s t : Finset ℤ) (a b : ℤ → ℂ),
        (C * ‖HardyAux.polyLp s a‖) * ‖HardyAux.poly t b‖ <
          ‖∑ j ∈ s, ∑ k ∈ t,
             if j + k = 0 ∧ 0 ≤ j then a j * b k else 0‖ := by
    intro C
    by_cases hC : C < 1
    · refine ⟨({0} : Finset ℤ), ({0} : Finset ℤ), (fun _ => (1:ℂ)), (fun _ => (1:ℂ)), ?_⟩
      have hf : ‖HardyAux.polyLp ({0}:Finset ℤ) (fun _ => (1:ℂ))‖ = 1 := by
        rw [HardyAux.norm_polyLp]
        have hh : ∀ x : AddCircle (1:ℝ), ‖HardyAux.poly ({0}:Finset ℤ)
            (fun _ => (1:ℂ)) x‖ = (1:ℝ) := by
          intro x
          simp [HardyAux.poly_apply]
        simp_rw [hh]
        simp
      have hg : ‖HardyAux.poly ({0}:Finset ℤ) (fun _ => (1:ℂ))‖ = 1 := by
        have hx : HardyAux.poly ({0}:Finset ℤ) (fun _ => (1:ℂ)) =
            (1 : C(AddCircle (1:ℝ), ℂ)) := by
          ext x
          simp [HardyAux.poly_apply]
        rw [hx]
        exact norm_one
      have hd : (∑ j ∈ ({0}:Finset ℤ), ∑ k ∈ ({0}:Finset ℤ),
            if j + k = 0 ∧ (0:ℤ) ≤ j then (1:ℂ) * 1 else 0) = 1 := by
        simp only [Finset.sum_singleton]
        norm_num
      -- On constants the putative estimate is precisely `C < 1`.
      simp only [hf, hg, mul_one]
      simp only [Finset.sum_singleton]
      norm_num
      exact hC
    · -- The difficult regime is the genuine harmonic-analysis estimate; one needs
      -- Fejér kernels and bounded approximants to a step function.
      have hlarge : (1:ℝ) ≤ C := le_of_not_gt hC
      -- The positive test input can be chosen to be the Fejer polynomial.  The proof that
      -- its L¹ norm is exactly one (`norm_FejerLp`) uses positivity of a square, not an
      -- estimate by the triangle inequality.  Keep its length odd, so that all the
      -- negative sine coefficients used in the second polynomial are strictly internal.
      -- What remains below is solely the uniform bound for the harmonic sine polynomial.
      -- No Fourier or operator-theoretic facts are involved in this goal.
      let R : ℝ := 100 * (C + 1)
      obtain ⟨M, hM⟩ : ∃ M : ℕ,
          R < ∑ i ∈ Finset.range M, (1 / (i+1) : ℝ) := by
        have ht := (Real.tendsto_sum_range_one_div_nat_succ_atTop)
        have hev : ∀ᶠ r : ℝ in Filter.atTop, R < r :=
          Filter.eventually_gt_atTop R
        rcases (Filter.eventually_atTop.1 ((ht.eventually hev))) with ⟨N, hN⟩
        exact ⟨N, hN N (le_rfl)⟩
      let L : ℕ := 2*M + 1
      have hLM : M < L := by dsimp [L]; omega
      have hL : 0 < L := by dsimp [L]; omega
      refine ⟨HardyAux.diffset L, HardyAux.sinsupp M,
          HardyAux.Fcoef L, HardyAux.Scoef, ?_⟩
      rw [HardyAux.norm_FejerLp L hL]
      rw [HardyAux.diagonal_Fejer_sin L M hLM]
      simp only [mul_one]
      -- The elementary Abel--Dirichlet estimate for the companion sine polynomial
      -- is now independent of the operator.  Its proof is finite summation by parts.
      have hsine : ‖HardyAux.poly (HardyAux.sinsupp M) HardyAux.Scoef‖ ≤ (10:ℝ) :=
        HardyAux.norm_sinpoly_le M
      let H : ℝ := ∑ n ∈ Finset.range M, (1 / ((n+1:ℕ):ℝ))
      let W : ℝ := ∑ n ∈ Finset.range M,
          ((((L-(n+1):ℕ):ℝ) / (L:ℝ)) * (1 / ((n+1:ℕ):ℝ)))
      have hH : 100 * (C+1) < H := by simpa [H, R] using hM
      have hlow : ((1:ℝ)/2) * H ≤ W := by
        simpa [H, W, L] using (HardyAux.Fejer_diag_lower M)
      have hHnon : (0:ℝ) ≤ H := by
        dsimp [H]
        exact Finset.sum_nonneg (fun i hi => by positivity)
      have hWnon : (0:ℝ) ≤ W :=
        le_trans (mul_nonneg (by norm_num) hHnon) hlow
      have hCnon : (0:ℝ) ≤ C := le_trans (by norm_num) hlarge
      have hCW : C * ‖HardyAux.poly (HardyAux.sinsupp M) HardyAux.Scoef‖ < W := by
        calc
          C * ‖HardyAux.poly (HardyAux.sinsupp M) HardyAux.Scoef‖
              ≤ C * 10 := mul_le_mul_of_nonneg_left hsine hCnon
          _ < ((1:ℝ)/2) * H := by nlinarith
          _ ≤ W := hlow
      -- Convert the real positive sum to its complex norm.
      change C * ‖HardyAux.poly (HardyAux.sinsupp M) HardyAux.Scoef‖ < ‖(W:ℂ)‖
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hWnon]
      exact hCW
  obtain ⟨s, t, a, b, hab⟩ := no_diagonal ‖A‖
  exact (not_lt_of_ge
    (HardyAux.diagonal_bound_of_analytic_projection A hfix hneg s t a b)) hab
/-ResultProofEnd-/
/-ResultEnd-/
-- END INLINED FILE: Main.lean

end Submission
