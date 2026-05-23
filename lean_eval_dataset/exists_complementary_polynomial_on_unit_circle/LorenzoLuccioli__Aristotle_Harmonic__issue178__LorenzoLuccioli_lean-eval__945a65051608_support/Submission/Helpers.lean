import Mathlib
import Submission.StrictCase
import Submission.CoeffBound

open Polynomial Complex

namespace Submission.Helpers

/-! ## Circle properties -/

lemma circle_norm_eq_one (z : Circle) : ‖(z : ℂ)‖ = 1 :=
  Circle.norm_coe z

lemma circle_ne_zero (z : Circle) : (z : ℂ) ≠ 0 :=
  Circle.coe_ne_zero z

lemma circle_conj_eq_inv (z : Circle) : starRingEnd ℂ (z : ℂ) = (z : ℂ)⁻¹ := by
  rw [Complex.inv_def, Complex.normSq_eq_norm_sq, circle_norm_eq_one]; norm_num

lemma circle_mul_conj (z : Circle) : (z : ℂ) * starRingEnd ℂ (z : ℂ) = 1 := by
  rw [circle_conj_eq_inv, mul_inv_cancel₀ (circle_ne_zero z)]

/-! ## Key identities on the circle -/

lemma norm_sq_eval_circle (P : ℂ[X]) (z : Circle) :
    ‖P.eval (z : ℂ)‖ ^ 2 = (P.eval (z : ℂ) * starRingEnd ℂ (P.eval (z : ℂ))).re := by
  rw [Complex.mul_conj']; norm_cast

/-! ## Base cases -/

lemma exists_complementary_const (c : ℂ) (hc : ‖c‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ (Polynomial.C c).natDegree ∧
        ∀ z : Circle, ‖(Polynomial.C c).eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  refine' ⟨ Polynomial.C ( Complex.ofReal ( Real.sqrt ( 1 - ‖c‖ ^ 2 ) ) ), _, _ ⟩ <;> norm_num [ hc ]

lemma exists_complementary_X_mul (P' : ℂ[X]) (hP' : P' ≠ 0)
    (hQ : ∃ Q : ℂ[X], Q.natDegree ≤ P'.natDegree ∧
      ∀ z : Circle, ‖P'.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ (X * P').natDegree ∧
        ∀ z : Circle, ‖(X * P').eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  cases' hQ with Q hQ; use Q; simp_all +decide [ Polynomial.natDegree_mul' ] ;
  linarith

/-! ## Helper lemmas for induction -/

lemma exists_X_mul_of_coeff_zero_eq_zero (P : ℂ[X]) (hP : P ≠ 0) (h0 : P.coeff 0 = 0) :
    ∃ P' : ℂ[X], P = X * P' ∧ P' ≠ 0 ∧ P'.natDegree < P.natDegree := by
  obtain ⟨Q, hQ⟩ : ∃ Q : ℂ[X], P = Polynomial.X * Q := by
    simpa using Polynomial.X_dvd_iff.mpr h0;
  simp_all +decide [ Polynomial.natDegree_mul' ]

lemma eval_norm_X_mul (P : ℂ[X]) (z : Circle) :
    ‖(X * P).eval (z : ℂ)‖ = ‖P.eval (z : ℂ)‖ := by
  simp +decide [ circle_norm_eq_one ]

/-! ## Fejér-Riesz: Strict case (1 - ‖P‖² > 0 on circle)

In this case, the "defect polynomial" R has no roots on the unit circle.
Roots pair as (α, 1/conj α) by the self-reciprocal property,
and we can construct Q from the "inside" roots. -/

/-- The strict Fejér-Riesz: when ‖P(z)‖ is strictly less than 1 everywhere on the circle. -/
lemma fejer_riesz_strict (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1)
    (hP_strict : ∃ δ : ℝ, 0 < δ ∧ ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1 - δ) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  -- Reduce to the core case by handling P = 0, constant, or P(0) = 0
  suffices h : ∀ n : ℕ, ∀ P : ℂ[X], P.natDegree ≤ n →
      (∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) →
      (∀ z : Circle, ‖P.eval (z : ℂ)‖ < 1) →
      ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 by
    obtain ⟨δ, hδ, hPs⟩ := hP_strict
    exact h P.natDegree P le_rfl hP (fun z => lt_of_le_of_lt (hPs z) (by linarith))
  intro n
  induction n with
  | zero =>
    intro P hPn hPb hPs
    have hconst : P.natDegree = 0 := Nat.le_zero.mp hPn
    rw [Polynomial.natDegree_eq_zero] at hconst
    obtain ⟨c, rfl⟩ := hconst
    exact exists_complementary_const c (by simpa using hPb ⟨1, by simp⟩)
  | succ n ih =>
    intro P hPn hPb hPs
    by_cases hP0 : P = 0
    · subst hP0; exact ⟨1, by norm_num⟩
    by_cases hdeg : P.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hdeg
      obtain ⟨c, rfl⟩ := hdeg
      exact exists_complementary_const c (by simpa using hPb ⟨1, by simp⟩)
    by_cases hc0 : P.coeff 0 = 0
    · obtain ⟨P', rfl, hP'ne, hP'deg⟩ := exists_X_mul_of_coeff_zero_eq_zero P hP0 hc0
      apply exists_complementary_X_mul P' hP'ne
      apply ih P' (by omega)
      · intro z; rw [← eval_norm_X_mul P' z]; exact hPb z
      · intro z; rw [← eval_norm_X_mul P' z]; exact hPs z
    · exact fejer_riesz_strict_core P hP0 (by omega) hc0 hPs

/-! ## Fejér-Riesz via limit argument -/

/-
Key bound: if ‖Q(z)‖² ≤ 1 on the circle, coefficients are bounded.
-/
-- coeff_norm_le_of_eval_norm_le is defined in Submission/CoeffBound.lean

/-
The Fejér-Riesz theorem (hard case): P nonzero, deg P ≥ 1, P(0) ≠ 0.
-/
lemma fejer_riesz_hard (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1)
    (hP_ne : P ≠ 0)
    (hP_deg : 1 ≤ P.natDegree)
    (hP_c0 : P.coeff 0 ≠ 0) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  have h_bounded : ∀ k : ℕ, ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧ ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 * (1 - 1 / (k + 2)) ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
    intro k
    obtain ⟨Q_k, hQ_k⟩ : ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧ ∀ z : Circle, ‖(P * Polynomial.C (1 - 1 / (k + 2) : ℂ)).eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
      convert fejer_riesz_strict ( P * Polynomial.C ( 1 - 1 / ( k + 2 : ℂ ) ) ) _ _ using 1;
      · rw [ Polynomial.natDegree_mul' ] <;> norm_num [ hP_ne ];
        exact ne_of_apply_ne ( Polynomial.eval 0 ) ( by norm_num; exact sub_ne_zero_of_ne <| by norm_num [ Complex.ext_iff ] ; linarith );
      · simp_all +decide [ Complex.norm_def, Complex.normSq ];
        exact fun z => mul_le_one₀ ( Real.sqrt_le_iff.mpr ⟨ by positivity, by linarith [ hP z ] ⟩ ) ( Real.sqrt_nonneg _ ) ( Real.sqrt_le_iff.mpr ⟨ by positivity, by nlinarith [ inv_mul_cancel₀ ( by linarith : ( k : ℝ ) + 2 ≠ 0 ), inv_pos.mpr ( by linarith : 0 < ( k : ℝ ) + 2 ) ] ⟩ );
      · refine' ⟨ 1 / ( k + 2 ), _, _ ⟩ <;> norm_num;
        · exact_mod_cast Nat.succ_pos _;
        · norm_num [ Complex.norm_def, Complex.normSq ] at *;
          exact fun z => by rw [ Real.sqrt_mul_self ( by nlinarith [ inv_mul_cancel₀ ( by linarith : ( k : ℝ ) + 2 ≠ 0 ) ] ) ] ; exact mul_le_of_le_one_left ( by nlinarith [ inv_mul_cancel₀ ( by linarith : ( k : ℝ ) + 2 ≠ 0 ) ] ) ( Real.sqrt_le_iff.mpr ⟨ by nlinarith [ inv_mul_cancel₀ ( by linarith : ( k : ℝ ) + 2 ≠ 0 ) ], by nlinarith [ hP z ] ⟩ ) ;
    simp_all +decide [ mul_pow, mul_assoc, mul_comm, mul_left_comm ];
    refine' ⟨ Q_k, hQ_k.1, fun z => _ ⟩ ; convert hQ_k.2 z using 2 ; norm_num [ Complex.normSq, Complex.sq_norm ] ; ring;
    norm_num;
  choose Q hQ using h_bounded;
  -- By the properties of the coefficients, the sequence of polynomials $Q_k$ is bounded in the space of polynomials of degree at most $n$.
  have h_bounded_coeffs : ∀ k : ℕ, ∀ i : ℕ, i ≤ P.natDegree → ‖(Q k).coeff i‖ ≤ 1 := by
    intros k i hi
    have h_eval_bound : ∀ z : Circle, ‖(Q k).eval (z : ℂ)‖ ≤ 1 := by
      exact fun z => by nlinarith [ hQ k |>.2 z, show 0 ≤ ‖eval ( z : ℂ ) P‖ ^ 2 * ( 1 - 1 / ( k + 2 : ℝ ) ) ^ 2 by positivity ] ;
    apply coeff_norm_le_of_eval_norm_le (Q k) P.natDegree (hQ k).left h_eval_bound i;
  -- By the properties of the coefficients, the sequence of polynomials $Q_k$ is bounded in the space of polynomials of degree at most $n$, and hence has a convergent subsequence.
  obtain ⟨Q_lim, hQ_lim⟩ : ∃ Q_lim : Fin (P.natDegree + 1) → ℂ, ∃ subseq : ℕ → ℕ, StrictMono subseq ∧ ∀ i : Fin (P.natDegree + 1), Filter.Tendsto (fun k => (Q (subseq k)).coeff i) Filter.atTop (nhds (Q_lim i)) := by
    have h_compact : IsCompact (Set.pi Set.univ fun i : Fin (P.natDegree + 1) => Metric.closedBall (0 : ℂ) 1) := by
      exact isCompact_univ_pi fun _ => ProperSpace.isCompact_closedBall _ _;
    have := h_compact.isSeqCompact fun k => show ( fun i : Fin ( P.natDegree + 1 ) => ( Q k |> Polynomial.coeff ) i ) ∈ Set.pi Set.univ fun i : Fin ( P.natDegree + 1 ) => Metric.closedBall 0 1 from fun i _ => mem_closedBall_zero_iff.mpr ( h_bounded_coeffs k i ( Fin.is_le i ) );
    exact ⟨ this.choose, this.choose_spec.2.choose, this.choose_spec.2.choose_spec.1, fun i => tendsto_pi_nhds.mp this.choose_spec.2.choose_spec.2 i ⟩;
  obtain ⟨ subseq, hsubseq₁, hsubseq₂ ⟩ := hQ_lim;
  refine' ⟨ ∑ i : Fin ( P.natDegree + 1 ), Q_lim i • Polynomial.X ^ ( i : ℕ ), _, _ ⟩;
  · exact le_trans ( Polynomial.natDegree_sum_le _ _ ) ( Finset.sup_le fun i hi => Polynomial.natDegree_smul_le _ _ |> le_trans <| Polynomial.natDegree_X_pow_le _ |> le_trans <| Nat.le_of_lt_succ <| Fin.is_lt i );
  · intro z
    have h_eval_lim : Filter.Tendsto (fun k => ‖(Q (subseq k)).eval (z : ℂ)‖ ^ 2) Filter.atTop (nhds (‖(∑ i : Fin (P.natDegree + 1), Q_lim i • Polynomial.X ^ (i : ℕ)).eval (z : ℂ)‖ ^ 2)) := by
      have h_eval_lim : Filter.Tendsto (fun k => ∑ i : Fin (P.natDegree + 1), (Q (subseq k)).coeff i * (z : ℂ) ^ (i : ℕ)) Filter.atTop (nhds (∑ i : Fin (P.natDegree + 1), Q_lim i * (z : ℂ) ^ (i : ℕ))) := by
        exact tendsto_finset_sum _ fun i _ => Filter.Tendsto.mul ( hsubseq₂ i ) tendsto_const_nhds;
      convert h_eval_lim.norm.pow 2 using 2 <;> norm_num [ Polynomial.eval_finset_sum ];
      rw [ Polynomial.eval_eq_sum_range' ];
      rw [ Finset.sum_range ];
      linarith [ hQ ( subseq ‹_› ) ];
    have h_eval_lim : Filter.Tendsto (fun k => ‖P.eval (z : ℂ)‖ ^ 2 * (1 - 1 / (subseq k + 2)) ^ 2 + ‖(Q (subseq k)).eval (z : ℂ)‖ ^ 2) Filter.atTop (nhds (‖P.eval (z : ℂ)‖ ^ 2 + ‖(∑ i : Fin (P.natDegree + 1), Q_lim i • Polynomial.X ^ (i : ℕ)).eval (z : ℂ)‖ ^ 2)) := by
      refine' Filter.Tendsto.add _ h_eval_lim;
      exact le_trans ( Filter.Tendsto.mul tendsto_const_nhds <| Filter.Tendsto.pow ( tendsto_const_nhds.sub <| tendsto_const_nhds.div_atTop <| Filter.tendsto_atTop_add_const_right _ _ <| tendsto_natCast_atTop_atTop.comp hsubseq₁.tendsto_atTop ) _ ) <| by norm_num;
    exact tendsto_nhds_unique h_eval_lim ( by simpa only [ hQ _ |>.2 ] using tendsto_const_nhds )

/-! ## Main theorem combining all cases -/

lemma exists_complementary_core (P : ℂ[X])
    (hP : ∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  suffices h : ∀ n : ℕ, ∀ P : ℂ[X], P.natDegree ≤ n →
      (∀ z : Circle, ‖P.eval (z : ℂ)‖ ≤ 1) →
      ∃ Q : ℂ[X], Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 from
    h P.natDegree P le_rfl hP
  intro n
  induction n with
  | zero =>
    intro P hPn hPb
    have hconst : P.natDegree = 0 := Nat.le_zero.mp hPn
    rw [Polynomial.natDegree_eq_zero] at hconst
    obtain ⟨c, rfl⟩ := hconst
    exact exists_complementary_const c (by simpa using hPb ⟨1, by simp⟩)
  | succ n ih =>
    intro P hPn hPb
    by_cases hP0 : P = 0
    · subst hP0; exact ⟨1, by norm_num⟩
    by_cases hdeg : P.natDegree = 0
    · rw [Polynomial.natDegree_eq_zero] at hdeg
      obtain ⟨c, rfl⟩ := hdeg
      exact exists_complementary_const c (by simpa using hPb ⟨1, by simp⟩)
    by_cases hc0 : P.coeff 0 = 0
    · obtain ⟨P', rfl, hP'ne, hP'deg⟩ := exists_X_mul_of_coeff_zero_eq_zero P hP0 hc0
      apply exists_complementary_X_mul P' hP'ne
      apply ih P' (by omega)
      intro z; rw [← eval_norm_X_mul P' z]; exact hPb z
    · exact fejer_riesz_hard P hPb hP0 (by omega) hc0

end Submission.Helpers