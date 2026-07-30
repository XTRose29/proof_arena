import Mathlib
import Submission.Helpers

open Polynomial Complex Submission.Helpers

namespace Submission.Helpers

/-! ## Trailing degree of QmonicPart -/

/-- `(QmonicPart G).eval 0 = ∏ (-ρ)` over `QrootsMultiset G`. -/
lemma eval_zero_QmonicPart (G : ℂ[X]) :
    (QmonicPart G).eval 0 =
      ((QrootsMultiset G).map (fun ρ => -ρ)).prod := by
  unfold QmonicPart
  rw [Polynomial.eval_multiset_prod, Multiset.map_map]
  congr 1
  apply Multiset.map_congr rfl
  intros ρ _
  simp [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C]

/-- For `P` with `natTrailingDegree P = 0` and `n ≥ 1`, the natTrailingDegree of
`QmonicPart (Gpoly P)` is zero. -/
lemma natTrailingDegree_QmonicPart_Gpoly (P : ℂ[X])
    (hT : P.natTrailingDegree = 0) (hn : 1 ≤ P.natDegree) :
    (QmonicPart (Gpoly P)).natTrailingDegree = 0 := by
  rw [natTrailingDegree_eq_zero]
  right
  rw [Polynomial.coeff_zero_eq_eval_zero, eval_zero_QmonicPart]
  intro h
  rw [Multiset.prod_eq_zero_iff] at h
  rw [Multiset.mem_map] at h
  obtain ⟨ρ, hρ_mem, hρ_eq⟩ := h
  have hρ_ne : ρ ≠ 0 := QrootsMultiset_ne_zero P hT hn ρ hρ_mem
  exact hρ_ne (neg_eq_zero.mp hρ_eq)

/-! ## Existence of a "good" point on the unit circle -/

/-- Parametrization of the unit circle by `T ↦ (1 + IT)/(1 - IT)`. -/
private noncomputable abbrev circlePt (T : ℝ) : ℂ :=
  (1 + Complex.I * (T : ℂ)) / (1 - Complex.I * (T : ℂ))

private lemma one_sub_IT_ne_zero (T : ℝ) : (1 - Complex.I * (T : ℂ)) ≠ 0 := by
  intro h
  have h_normSq : Complex.normSq (1 - Complex.I * (T : ℂ)) = 1 + T ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
    ring
  rw [h, Complex.normSq_zero] at h_normSq
  nlinarith [sq_nonneg T]

private lemma circlePt_norm_one (T : ℝ) : ‖circlePt T‖ = 1 := by
  have h_normSq_plus : Complex.normSq (1 + Complex.I * (T : ℂ)) = 1 + T ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
    ring
  have h_normSq_minus : Complex.normSq (1 - Complex.I * (T : ℂ)) = 1 + T ^ 2 := by
    rw [Complex.normSq_apply]
    simp [Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
          Complex.I_re, Complex.I_im]
    ring
  have h_norm_plus_sq : ‖1 + Complex.I * (T : ℂ)‖ ^ 2 = 1 + T ^ 2 := by
    rw [Complex.normSq_eq_norm_sq] at h_normSq_plus; exact h_normSq_plus
  have h_norm_minus_sq : ‖1 - Complex.I * (T : ℂ)‖ ^ 2 = 1 + T ^ 2 := by
    rw [Complex.normSq_eq_norm_sq] at h_normSq_minus; exact h_normSq_minus
  have h_pos : (0 : ℝ) < 1 + T ^ 2 := by positivity
  have h_minus_ne : 1 - Complex.I * (T : ℂ) ≠ 0 := one_sub_IT_ne_zero T
  unfold circlePt
  rw [norm_div]
  rw [show ‖1 + Complex.I * (T : ℂ)‖ = ‖1 - Complex.I * (T : ℂ)‖ from ?_, div_self]
  · rwa [ne_eq, norm_eq_zero]
  · have h_nn1 : 0 ≤ ‖1 + Complex.I * (T : ℂ)‖ := norm_nonneg _
    have h_nn2 : 0 ≤ ‖1 - Complex.I * (T : ℂ)‖ := norm_nonneg _
    nlinarith [h_norm_plus_sq, h_norm_minus_sq, sq_nonneg ‖1 + Complex.I * (T : ℂ)‖,
               sq_nonneg ‖1 - Complex.I * (T : ℂ)‖]

/-- The circle parametrization is injective. -/
private lemma circlePt_injective : Function.Injective circlePt := by
  intro T₁ T₂ h
  unfold circlePt at h
  have hne₁ : (1 - Complex.I * (T₁ : ℂ)) ≠ 0 := one_sub_IT_ne_zero T₁
  have hne₂ : (1 - Complex.I * (T₂ : ℂ)) ≠ 0 := one_sub_IT_ne_zero T₂
  field_simp at h
  -- After field_simp: (1 + I T₁)(1 - I T₂) = (1 + I T₂)(1 - I T₁)
  have h1 : (2 * Complex.I) * ((T₁ : ℂ) - T₂) = 0 := by linear_combination h
  have hne : (2 * Complex.I) ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  have h2 : ((T₁ : ℂ) - T₂) = 0 := (mul_eq_zero.mp h1).resolve_left hne
  have h3 : (T₁ : ℂ) = (T₂ : ℂ) := by linear_combination h2
  exact Complex.ofReal_injective h3

/-- For nonzero `R : ℂ[X]`, there exists a point on the unit circle where `R` does
not vanish. -/
lemma exists_on_circle_eval_ne_zero (R : ℂ[X]) (hR : R ≠ 0) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ R.eval z ≠ 0 := by
  by_contra h
  push_neg at h
  -- Every point on the circle is a root of R.
  -- In particular, every circlePt T is a root.
  have h_all_root : ∀ T : ℝ, R.eval (circlePt T) = 0 := by
    intro T
    exact h (circlePt T) (circlePt_norm_one T)
  -- Apply uniqueness-of-polynomials-by-values lemma.
  refine hR (eq_of_natDegree_lt_card_of_eval_eq R 0
    (f := fun i : Fin (R.natDegree + 1) => circlePt ((i : ℕ) : ℝ)) ?_ ?_ ?_)
  · intros i j hij
    have h1 : circlePt ((i : ℕ) : ℝ) = circlePt ((j : ℕ) : ℝ) := hij
    have h2 : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := circlePt_injective h1
    have h3 : (i : ℕ) = (j : ℕ) := by exact_mod_cast h2
    exact Fin.ext h3
  · intro i; rw [Polynomial.eval_zero]; exact h_all_root _
  · simp

/-- For nonzero `R₁ R₂ : ℂ[X]`, there exists a point on the unit circle where both
are nonzero. -/
lemma exists_on_circle_both_ne_zero (R₁ R₂ : ℂ[X]) (hR₁ : R₁ ≠ 0) (hR₂ : R₂ ≠ 0) :
    ∃ z : ℂ, ‖z‖ = 1 ∧ R₁.eval z ≠ 0 ∧ R₂.eval z ≠ 0 := by
  have hR : R₁ * R₂ ≠ 0 := mul_ne_zero hR₁ hR₂
  obtain ⟨z, hz, hRz⟩ := exists_on_circle_eval_ne_zero (R₁ * R₂) hR
  refine ⟨z, hz, ?_, ?_⟩
  · intro h; apply hRz; rw [eval_mul, h, zero_mul]
  · intro h; apply hRz; rw [eval_mul, h, mul_zero]

/-! ## Pointwise identity at z on the circle -/

/-- The pointwise version of `scaled_QmonicPart_identity`: for `z` on the unit
circle, `lc · |QmonicPart(z)|² = prod · (1 - |P(z)|²)`. -/
lemma scaled_QmonicPart_identity_on_circle (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) (hn : 1 ≤ P.natDegree)
    {z : ℂ} (hz : ‖z‖ = 1) :
    (leadingCoeff (Gpoly P) : ℂ) * ((‖(QmonicPart (Gpoly P)).eval z‖ : ℂ)) ^ 2 =
      (((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod) *
        (1 - (‖P.eval z‖ : ℂ) ^ 2) := by
  have hQND : (QmonicPart (Gpoly P)).natDegree = P.natDegree :=
    natDegree_QpolyMonic P hT hPbd hn
  have hQTD : (QmonicPart (Gpoly P)).natTrailingDegree = 0 :=
    natTrailingDegree_QmonicPart_Gpoly P hT hn
  have hz_ne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hz_pow_ne : (z : ℂ) ^ P.natDegree ≠ 0 := pow_ne_zero _ hz_ne
  -- Evaluate the scaled identity at z.
  have h_id := scaled_QmonicPart_identity P hT hPbd hn
  have h_id_eval := congrArg (fun p => p.eval z) h_id
  simp only [eval_mul, eval_C] at h_id_eval
  rw [Pstar_eval_on_circle (QmonicPart (Gpoly P)) hz, hQND, hQTD, add_zero] at h_id_eval
  rw [Gpoly_eval_on_circle P hT hz] at h_id_eval
  -- h_id_eval :
  --   lc * (QmonicPart.eval z * (z^n * conj(QmonicPart.eval z)))
  --     = prod * (z^n * (1 - ‖P.eval z‖^2))
  -- Use |QmonicPart(z)|² identity.
  set qz := (QmonicPart (Gpoly P)).eval z with hqz_def
  have habs : qz * starRingEnd ℂ qz = (‖qz‖ : ℂ) ^ 2 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  -- Restate the eval identity in clean form.
  have hRearrange : (Gpoly P).leadingCoeff * (qz * (z ^ P.natDegree * starRingEnd ℂ qz)) =
      z ^ P.natDegree * ((Gpoly P).leadingCoeff * (‖qz‖ : ℂ) ^ 2) := by
    have : qz * (z ^ P.natDegree * starRingEnd ℂ qz) =
        z ^ P.natDegree * (qz * starRingEnd ℂ qz) := by ring
    rw [this, habs]; ring
  rw [hRearrange] at h_id_eval
  have key : (z : ℂ) ^ P.natDegree *
      ((leadingCoeff (Gpoly P) : ℂ) * ((‖qz‖ : ℂ)) ^ 2) =
        (z : ℂ) ^ P.natDegree *
          ((((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod) *
            (1 - (‖P.eval z‖ : ℂ) ^ 2)) := by
    linear_combination h_id_eval
  exact mul_left_cancel₀ hz_pow_ne key

/-! ## Existence of Q in the main Fejér-Riesz case -/

/-- Main Fejér-Riesz construction: for `P` with `natTrailingDegree = 0`, `n ≥ 1`,
and `Gpoly P ≠ 0`, there exists `Q` of degree at most `n` whose squared modulus
on the circle equals `1 - |P|²`. -/
lemma exists_Q_FejerRiesz (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) (hn : 1 ≤ P.natDegree)
    (hG_ne : Gpoly P ≠ 0) :
    ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by
  have hlc_ne : (Gpoly P).leadingCoeff ≠ 0 := leadingCoeff_Gpoly_ne_zero P hT hn
  have hprod_ne : ((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod ≠ 0 :=
    QrootsMultiset_neg_conj_prod_ne_zero P hT hn
  have hQ_ne : QmonicPart (Gpoly P) ≠ 0 := QmonicPart_ne_zero _
  -- Pick z₀ on circle with both Gpoly P (z₀) ≠ 0 and QmonicPart (Gpoly P) (z₀) ≠ 0.
  obtain ⟨z₀, hz₀, hGz₀, hQz₀⟩ :=
    exists_on_circle_both_ne_zero (Gpoly P) (QmonicPart (Gpoly P)) hG_ne hQ_ne
  -- At z₀: |P z₀| < 1 (strictly), from Gpoly P z₀ ≠ 0.
  have hPz₀_lt : ‖P.eval z₀‖ < 1 := by
    have hP_le := hPbd z₀ hz₀
    have hGev := Gpoly_eval_on_circle P hT hz₀
    by_contra h
    push_neg at h
    have hPz₀_eq : ‖P.eval z₀‖ = 1 := le_antisymm hP_le h
    apply hGz₀
    rw [hGev, hPz₀_eq]
    push_cast; ring
  -- ‖QmonicPart (Gpoly P) z₀‖ > 0.
  have hQz₀_pos : 0 < ‖(QmonicPart (Gpoly P)).eval z₀‖ := by
    rcases (norm_nonneg ((QmonicPart (Gpoly P)).eval z₀)).lt_or_eq with h | h
    · exact h
    · exfalso; apply hQz₀; exact norm_eq_zero.mp h.symm
  have hQz₀_sq_pos : 0 < ‖(QmonicPart (Gpoly P)).eval z₀‖ ^ 2 := pow_pos hQz₀_pos 2
  -- Apply the pointwise identity at z₀ and arbitrary z.
  have h_at_z₀ := scaled_QmonicPart_identity_on_circle P hT hPbd hn hz₀
  -- (1 - |P z₀|²) > 0 as a real number.
  have h1mP_pos : 0 < 1 - ‖P.eval z₀‖ ^ 2 := by
    have : ‖P.eval z₀‖ ^ 2 < 1 := by
      rw [show (1 : ℝ) = 1 ^ 2 by ring]
      exact sq_lt_sq' (by linarith [norm_nonneg (P.eval z₀)]) hPz₀_lt
    linarith
  -- Define α := (1 - |P z₀|²) / ‖QmonicPart z₀‖² > 0.
  set α : ℝ := (1 - ‖P.eval z₀‖ ^ 2) / ‖(QmonicPart (Gpoly P)).eval z₀‖ ^ 2 with hα_def
  have hα_pos : 0 < α := div_pos h1mP_pos hQz₀_sq_pos
  -- The cast identity (α : ℂ) * ‖QmonicPart z₀‖² = 1 - ‖P z₀‖² (over ℂ).
  have hα_z₀ : (α : ℂ) * (‖(QmonicPart (Gpoly P)).eval z₀‖ : ℂ) ^ 2 =
        (1 - (‖P.eval z₀‖ : ℂ) ^ 2) := by
    have hcast : (α : ℂ) * (‖(QmonicPart (Gpoly P)).eval z₀‖ : ℂ) ^ 2 =
        ((α * ‖(QmonicPart (Gpoly P)).eval z₀‖ ^ 2 : ℝ) : ℂ) := by push_cast; ring
    rw [hcast]
    have h_real : α * ‖(QmonicPart (Gpoly P)).eval z₀‖ ^ 2 = 1 - ‖P.eval z₀‖ ^ 2 := by
      rw [hα_def, div_mul_cancel₀]
      exact ne_of_gt hQz₀_sq_pos
    rw [h_real]; push_cast; ring
  -- Show (α : ℂ) = lc / prod (deduced from h_at_z₀ and hα_z₀).
  set lc : ℂ := (Gpoly P).leadingCoeff
  set prod : ℂ := ((QrootsMultiset (Gpoly P)).map (fun ρ => -(starRingEnd ℂ ρ))).prod
  have hα_eq : (α : ℂ) * prod = lc := by
    have hQz₀_sq_ne : (‖(QmonicPart (Gpoly P)).eval z₀‖ : ℂ) ^ 2 ≠ 0 := by
      refine pow_ne_zero _ ?_
      simp only [ne_eq, Complex.ofReal_eq_zero]
      exact ne_of_gt hQz₀_pos
    -- From h_at_z₀: lc * |Q|² = prod * (1 - |P|²). And hα_z₀ gives (α : ℂ) * |Q|² = (1 - |P|²).
    -- Multiply hα_z₀ by prod: α * prod * |Q|² = prod * (1 - |P|²) = lc * |Q|².
    -- Cancel |Q|² (nonzero): α * prod = lc.
    have step : ((α : ℂ) * prod) * (‖(QmonicPart (Gpoly P)).eval z₀‖ : ℂ) ^ 2 =
        lc * (‖(QmonicPart (Gpoly P)).eval z₀‖ : ℂ) ^ 2 := by
      have h1 : (α : ℂ) * prod * (‖(QmonicPart (Gpoly P)).eval z₀‖ : ℂ) ^ 2 =
          prod * ((α : ℂ) * (‖(QmonicPart (Gpoly P)).eval z₀‖ : ℂ) ^ 2) := by ring
      rw [h1, hα_z₀]
      linear_combination -h_at_z₀
    exact mul_right_cancel₀ hQz₀_sq_ne step
  -- Now define Q := C(c) * QmonicPart.
  let c : ℝ := Real.sqrt α
  have hc_pos : 0 < c := Real.sqrt_pos.mpr hα_pos
  have hc_sq : c ^ 2 = α := Real.sq_sqrt hα_pos.le
  have hc_C_ne : (c : ℂ) ≠ 0 := by
    simp only [ne_eq, Complex.ofReal_eq_zero]; exact ne_of_gt hc_pos
  refine ⟨C ((c : ℂ)) * QmonicPart (Gpoly P), ?_, ?_⟩
  · rw [Polynomial.natDegree_C_mul hc_C_ne]
    exact (natDegree_QpolyMonic P hT hPbd hn).le
  intro z hz
  -- The pointwise identity at z.
  have h_at_z := scaled_QmonicPart_identity_on_circle P hT hPbd hn hz
  -- |Q z|² = α * ‖QmonicPart z‖².
  have hQ_norm_sq : ‖(C ((c : ℂ)) * QmonicPart (Gpoly P)).eval z‖ ^ 2 =
      α * ‖(QmonicPart (Gpoly P)).eval z‖ ^ 2 := by
    rw [eval_mul, eval_C, norm_mul, mul_pow, Complex.norm_real,
        Real.norm_of_nonneg hc_pos.le, hc_sq]
  -- For arbitrary z on circle: α * ‖QmonicPart z‖² = 1 - ‖P z‖².
  have hα_z : (α : ℂ) * (‖(QmonicPart (Gpoly P)).eval z‖ : ℂ) ^ 2 =
        (1 - (‖P.eval z‖ : ℂ) ^ 2) := by
    -- h_at_z: lc * |Q z|² = prod * (1 - |P z|²)
    -- With hα_eq: lc = α * prod
    -- So (α * prod) * |Q z|² = prod * (1 - |P z|²)
    -- Cancel prod (nonzero): α * |Q z|² = 1 - |P z|².
    have step : prod * ((α : ℂ) * (‖(QmonicPart (Gpoly P)).eval z‖ : ℂ) ^ 2) =
        prod * (1 - (‖P.eval z‖ : ℂ) ^ 2) := by
      have h1 : prod * ((α : ℂ) * (‖(QmonicPart (Gpoly P)).eval z‖ : ℂ) ^ 2) =
          ((α : ℂ) * prod) * (‖(QmonicPart (Gpoly P)).eval z‖ : ℂ) ^ 2 := by ring
      rw [h1, hα_eq]; exact h_at_z
    exact mul_left_cancel₀ hprod_ne step
  -- Cast back to ℝ.
  have hα_z_real : α * ‖(QmonicPart (Gpoly P)).eval z‖ ^ 2 = 1 - ‖P.eval z‖ ^ 2 := by
    have h_eq : (((α * ‖(QmonicPart (Gpoly P)).eval z‖ ^ 2) : ℝ) : ℂ) =
        (((1 - ‖P.eval z‖ ^ 2) : ℝ) : ℂ) := by
      push_cast
      linear_combination hα_z
    exact Complex.ofReal_injective h_eq
  rw [hQ_norm_sq]
  linarith [hα_z_real]

/-! ## Existence in the constant case -/

/-- When `P` is constant, the construction is immediate: pick a real square root. -/
lemma exists_Q_constant (P : ℂ[X]) (hND : P.natDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by
  set c : ℂ := P.coeff 0 with hc_def
  have hP_eq : P = C c := by
    rw [hc_def]; exact Polynomial.eq_C_of_natDegree_eq_zero hND
  -- ‖c‖ ≤ 1 from hPbd at z = 1.
  have h_bound : ‖c‖ ≤ 1 := by
    have h := hPbd 1 (by simp)
    rw [hP_eq, eval_C] at h; exact h
  -- ‖c‖² ≤ 1.
  have h_norm_sq : ‖c‖ ^ 2 ≤ 1 := by
    rw [show (1 : ℝ) = 1 ^ 2 by ring]
    exact sq_le_sq' (by linarith [norm_nonneg c]) h_bound
  set r : ℝ := Real.sqrt (1 - ‖c‖ ^ 2)
  have hr_nonneg : 0 ≤ r := Real.sqrt_nonneg _
  have hr_sq : r ^ 2 = 1 - ‖c‖ ^ 2 := Real.sq_sqrt (by linarith)
  refine ⟨C ((r : ℂ)), ?_, ?_⟩
  · -- natDegree (C ↑r) ≤ natDegree P = 0.
    rw [hND]
    exact Polynomial.natDegree_C _ |>.le
  intros z hz
  have h_P_eval : P.eval z = c := by rw [hP_eq, eval_C]
  rw [h_P_eval, eval_C, Complex.norm_real, Real.norm_of_nonneg hr_nonneg]
  linarith [hr_sq]

/-! ## Existence when Gpoly P = 0 -/

/-- When `Gpoly P = 0` and natDegree P ≥ 1, `|P(z)| ≡ 1` on the circle, so `Q = 0`. -/
lemma exists_Q_Gpoly_zero (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hn : 1 ≤ P.natDegree) (hG : Gpoly P = 0) :
    ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by
  refine ⟨0, by simp, ?_⟩
  intros z hz
  have hz_ne : z ≠ 0 := by intro h; rw [h, norm_zero] at hz; exact zero_ne_one hz
  have hzn_ne : z ^ P.natDegree ≠ 0 := pow_ne_zero _ hz_ne
  have hG_ev : (Gpoly P).eval z = 0 := by rw [hG]; simp
  rw [Gpoly_eval_on_circle P hT hz] at hG_ev
  -- z^n * (1 - ‖P z‖²) = 0; cancel z^n.
  have h1 : (1 - (‖P.eval z‖ : ℂ) ^ 2 : ℂ) = 0 :=
    (mul_eq_zero.mp hG_ev).resolve_left hzn_ne
  have h3 : ‖P.eval z‖ ^ 2 = 1 := by
    have h4 : ((‖P.eval z‖ ^ 2 : ℝ) : ℂ) = ((1 : ℝ) : ℂ) := by push_cast; linear_combination -h1
    exact_mod_cast h4
  simp [h3]

/-! ## Combined: natTrailingDegree = 0 case -/

/-- The full natTrailingDegree = 0 case, combining the three subcases. -/
lemma exists_Q_natTrailing_zero (P : ℂ[X]) (hT : P.natTrailingDegree = 0)
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by
  by_cases hn : 1 ≤ P.natDegree
  · by_cases hG : Gpoly P = 0
    · exact exists_Q_Gpoly_zero P hT hn hG
    · exact exists_Q_FejerRiesz P hT hPbd hn hG
  · -- natDegree = 0
    push_neg at hn
    have hND : P.natDegree = 0 := by omega
    exact exists_Q_constant P hND hPbd

/-! ## General case via X^m reduction -/

/-- General existence: for any `P : ℂ[X]` bounded by 1 on the circle, there exists `Q`. -/
lemma exists_Q_general (P : ℂ[X])
    (hPbd : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ≤ 1) :
    ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧
      ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ ^ 2 + ‖Q.eval z‖ ^ 2 = 1 := by
  by_cases hP : P = 0
  · refine ⟨1, ?_, ?_⟩
    · simp
    · intros z hz; simp [hP]
  -- P ≠ 0: extract X^m factor.
  obtain ⟨P₀, hP_eq, hP₀_ne, _hP₀_coeff0_ne, hT₀, hND₀⟩ :=
    X_pow_natTrailingDegree_mul_split P hP
  -- For z on circle, ‖P.eval z‖ = ‖P₀.eval z‖.
  have hP_eval_eq : ∀ z : ℂ, ‖z‖ = 1 → ‖P.eval z‖ = ‖P₀.eval z‖ := by
    intros z hz
    rw [hP_eq, eval_mul, eval_pow, eval_X, norm_mul, norm_pow, hz, one_pow, one_mul]
  -- Translate hPbd to P₀.
  have hPbd₀ : ∀ z : ℂ, ‖z‖ = 1 → ‖P₀.eval z‖ ≤ 1 := by
    intros z hz
    rw [← hP_eval_eq z hz]
    exact hPbd z hz
  -- Apply natTrailingDegree = 0 case to P₀.
  obtain ⟨Q, hQND, hQ_eq⟩ := exists_Q_natTrailing_zero P₀ hT₀ hPbd₀
  refine ⟨Q, ?_, ?_⟩
  · -- natDeg Q ≤ natDeg P.
    calc Q.natDegree ≤ P₀.natDegree := hQND
      _ = P.natDegree - P.natTrailingDegree := hND₀
      _ ≤ P.natDegree := Nat.sub_le _ _
  · intros z hz
    rw [hP_eval_eq z hz]
    exact hQ_eq z hz

end Submission.Helpers
