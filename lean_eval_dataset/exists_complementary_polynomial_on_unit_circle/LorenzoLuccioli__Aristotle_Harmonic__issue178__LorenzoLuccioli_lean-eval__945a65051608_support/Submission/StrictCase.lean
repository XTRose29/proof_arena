import Mathlib
import Submission.MultisetPair
import Submission.SpectralFactor

set_option maxHeartbeats 1600000

open Polynomial Complex

namespace Submission.Helpers

noncomputable def conjReverse (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  (Polynomial.reflect n P).map (starRingEnd ℂ)

lemma conjReverse_eval_circle (P : ℂ[X]) (n : ℕ) (hn : P.natDegree ≤ n)
    (z : Circle) :
    (conjReverse n P).eval (z : ℂ) = (z : ℂ) ^ n * starRingEnd ℂ (P.eval (z : ℂ)) := by
  unfold conjReverse; simp +decide [ Polynomial.eval_map ] ;
  simp +decide [ Polynomial.eval₂_eq_sum, Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.reflect ];
  rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; simp +decide [ Polynomial.toFinsupp_apply, revAt ] ; ring;
  rw [ if_pos ( le_trans ( Polynomial.le_natDegree_of_mem_supp _ hx ) hn ) ] ; rw [ show ( z : ℂ ) ^ n = ( z : ℂ ) ^ ( n - x ) * ( z : ℂ ) ^ x by rw [ ← pow_add, Nat.sub_add_cancel ( le_trans ( Polynomial.le_natDegree_of_mem_supp _ hx ) hn ) ] ] ; simp +decide [ mul_assoc, mul_comm, mul_left_comm ] ;
  simp +decide [ mul_left_comm ( z ^ x : ℂ ), mul_assoc, z.2 ];
  simp +decide [ ← mul_pow, Complex.mul_conj, Complex.normSq_eq_norm_sq ]

lemma mul_conjReverse_eq_norm_sq (P : ℂ[X]) (n : ℕ) (hn : P.natDegree ≤ n)
    (z : Circle) :
    P.eval (z : ℂ) * (conjReverse n P).eval (z : ℂ) =
    (z : ℂ) ^ n * ↑(‖P.eval (z : ℂ)‖ ^ 2) := by
  rw [conjReverse_eval_circle P n hn z]
  have : P.eval (z : ℂ) * ((z : ℂ) ^ n * starRingEnd ℂ (P.eval (z : ℂ))) =
    (z : ℂ) ^ n * (P.eval (z : ℂ) * starRingEnd ℂ (P.eval (z : ℂ))) := by ring
  rw [this, Complex.mul_conj']
  simp

lemma conjReverse_natDegree' (P : ℂ[X]) (n : ℕ) (hn : P.natDegree ≤ n) :
    (conjReverse n P).natDegree ≤ n := by
  unfold conjReverse
  exact le_trans (Polynomial.natDegree_map_le ..)
    (le_trans Polynomial.natDegree_reflect_le (max_le le_rfl hn))

/-! ## Spectral factorization: halving the roots of the defect polynomial.

The defect polynomial R = X^n - P·P* is self-reciprocal and has no roots on the
unit circle. Its roots pair under α ↦ (conj α)⁻¹, so Multiset.halving gives
a half-set T of roots. From T we build Q. -/

/-- The involution on ℂ used for root pairing: α ↦ (conj α)⁻¹. -/
noncomputable def conjInv : ℂ → ℂ := fun α => (starRingEnd ℂ α)⁻¹

lemma conjInv_invol : ∀ α : ℂ, conjInv (conjInv α) = α := by
  -- By definition of conjugation, we know that conj (conj α) = α. Therefore, applying conj to both sides gives us the desired result.
  simp [conjInv, Complex.ext_iff]

lemma defectPoly_natDegree_le (P : ℂ[X]) (n : ℕ) (hn : P.natDegree ≤ n) :
    (defectPoly n P).natDegree ≤ 2 * n := by
  refine' le_trans ( Polynomial.natDegree_sub_le _ _ ) ( max_le _ _ ) <;> norm_num [ hn ];
  · grind;
  · refine' le_trans ( Polynomial.natDegree_mul_le .. ) _;
    exact le_trans ( add_le_add hn ( conjReverse_natDegree' _ _ hn ) ) ( by linarith )

/-
No root of the defect polynomial is zero (when n = P.natDegree).
-/
lemma defectPoly_root_ne_zero (P : ℂ[X]) (n : ℕ) (hn : P.natDegree = n)
    (hP_ne : P ≠ 0) (hP_deg : 1 ≤ n) (hP_c0 : P.coeff 0 ≠ 0)
    (α : ℂ) (hα : α ∈ (defectPoly n P).roots) : α ≠ 0 := by
  unfold defectPoly at hα; simp_all +decide [ Polynomial.coeff_zero_eq_eval_zero ] ;
  intro h; simp_all +decide [ sub_eq_iff_eq_add ] ;
  -- Since $n \geq 1$, we have $0^n = 0$.
  have h_zero_pow : (0 : ℂ) ^ n = 0 := by
    rw [ zero_pow ( by linarith ) ];
  unfold conjReverse' at hα; simp_all +decide [ Polynomial.eval_map ] ;
  rw [ ← hn, Polynomial.coeff_natDegree ] at hα ; aesop

/-
The roots multiset of the defect polynomial is invariant under conjInv.
-/
lemma defectPoly_roots_map_conjInv (P : ℂ[X]) (n : ℕ) (hn : P.natDegree = n)
    (hP_ne : P ≠ 0) (hP_deg : 1 ≤ n) (hP_c0 : P.coeff 0 ≠ 0)
    (hP_strict : ∀ z : Circle, ‖P.eval (z : ℂ)‖ < 1) :
    (defectPoly n P).roots.map conjInv = (defectPoly n P).roots := by
  have h_coeff_zero : (defectPoly n P).coeff 0 ≠ 0 := by
    unfold defectPoly; simp_all +decide [ Polynomial.coeff_zero_eq_eval_zero ] ;
    unfold conjReverse'; simp_all +decide [ Polynomial.eval_map ] ;
    rw [ zero_pow ] <;> aesop;
  have h_natDegree : (defectPoly n P).natDegree = 2 * n := by
    refine' Polynomial.natDegree_eq_of_le_of_coeff_ne_zero _ _;
    · apply defectPoly_natDegree_le P n hn.le;
    · unfold defectPoly; simp_all +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ;
      unfold conjReverse'; simp_all +decide [ Polynomial.coeff_mul ] ;
      rw [ Finset.sum_eq_single ( n, n ) ] <;> simp_all +decide [ two_mul, Polynomial.coeff_eq_zero_of_natDegree_lt ];
      · rw [ ← hn, Polynomial.coeff_natDegree ] ; aesop;
      · intro a b hab h; cases lt_or_gt_of_ne ( show a ≠ n from fun h' => h h' <| by linarith ) <;> first | left; rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; linarith | right; rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; simp +decide [ *, revAt ] ;
        split_ifs <;> omega;
  have h_reflect_natDegree : (Polynomial.reflect (2 * n) (defectPoly n P)).natDegree = (defectPoly n P).natDegree := by
    rw [ Polynomial.natDegree_eq_of_degree_eq_some ] ; rw [ Polynomial.degree_eq_of_le_of_coeff_ne_zero ] <;> norm_num [ Polynomial.coeff_reflect, h_natDegree, h_coeff_zero ];
    rw [ Polynomial.degree_le_iff_coeff_zero ];
    simp +contextual [ Polynomial.revAt ];
    exact fun m hm => by rw [ if_neg ( by norm_cast at hm; linarith ) ] ; exact Polynomial.coeff_eq_zero_of_natDegree_lt <| by norm_cast at hm; linarith;
  have h_roots_conjReverse : (conjReverse' (2 * n) (defectPoly n P)).roots = (defectPoly n P).roots.map conjInv := by
    apply roots_conjReverse_eq_map_conjInv;
    · aesop;
    · linarith;
    · assumption;
    · exact h_reflect_natDegree;
  rw [ ← h_roots_conjReverse, defectPoly_self_reciprocal P n hn.le ]

/-- conjInv preserves root counts of the defect polynomial. -/
lemma defectPoly_root_count_conjInv (P : ℂ[X]) (n : ℕ) (hn : P.natDegree = n)
    (hP_ne : P ≠ 0) (hP_deg : 1 ≤ n) (hP_c0 : P.coeff 0 ≠ 0)
    (hP_strict : ∀ z : Circle, ‖P.eval (z : ℂ)‖ < 1)
    (α : ℂ) (hα : α ∈ (defectPoly n P).roots) :
    (defectPoly n P).roots.count α = (defectPoly n P).roots.count (conjInv α) := by
  have h := defectPoly_roots_map_conjInv P n hn hP_ne hP_deg hP_c0 hP_strict
  have hinj : Function.Injective conjInv := by
    intro a b hab; have := congr_arg conjInv hab; simp [conjInv_invol] at this; exact this
  conv_rhs => rw [← h]
  rw [Multiset.count_map_eq_count' conjInv _ hinj]

/-
The halved roots produce a polynomial that satisfies the Fejér-Riesz identity on the circle.
-/
lemma fejer_riesz_from_halving (P : ℂ[X]) (n : ℕ) (hn : P.natDegree = n)
    (hP_ne : P ≠ 0) (hP_deg : 1 ≤ n) (hP_c0 : P.coeff 0 ≠ 0)
    (hP_strict : ∀ z : Circle, ‖P.eval (z : ℂ)‖ < 1)
    (T : Multiset ℂ)
    (hT : (defectPoly n P).roots = T + T.map conjInv)
    (hTcard : 2 * T.card = (defectPoly n P).roots.card) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ n ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  -- Let's define the polynomial Q₀ as the product of the linear factors corresponding to the roots in T.
  set Q₀ : Polynomial ℂ := Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C α) T) with hQ₀_def
  have hQ₀_deg : Q₀.natDegree = T.card := by
    rw [ Polynomial.natDegree_multiset_prod ] ; aesop;
    norm_num [ Polynomial.X_sub_C_ne_zero ];
  -- Let's define the polynomial Q as Q₀ multiplied by a constant s such that |s|² = 1/c, where c = |lc|/∏|αᵢ|.
  obtain ⟨s, hs⟩ : ∃ s : ℂ, s ≠ 0 ∧ ∀ z : Circle, ‖(defectPoly n P).eval (z : ℂ)‖ = ‖s‖^2 * ‖Q₀.eval (z : ℂ)‖^2 := by
    -- By definition of $Q₀$, we know that $defectPoly n P = C(lc) * Q₀ * Q₁$, where $Q₁$ is the product of the linear factors corresponding to the roots in $T.map conjInv$.
    obtain ⟨lc, Q₁, hQ₁⟩ : ∃ lc : ℂ, lc ≠ 0 ∧ ∃ Q₁ : Polynomial ℂ, defectPoly n P = Polynomial.C lc * Q₀ * Q₁ ∧ Q₁ = Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C (conjInv α)) T) := by
      have h_factor : defectPoly n P = Polynomial.C (Polynomial.leadingCoeff (defectPoly n P)) * Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C α) (T + T.map conjInv)) := by
        convert Polynomial.Splits.eq_prod_roots _;
        exact hT.symm;
        exact?;
      refine' ⟨ Polynomial.leadingCoeff ( defectPoly n P ), _, _, _, rfl ⟩;
      · intro h; simp_all +singlePass ;
        exact absurd h_factor ( defectPoly_ne_zero P n ( by linarith ) hP_strict );
      · convert h_factor using 1 ; norm_num [ mul_assoc ];
        exact Or.inl <| Or.inl rfl;
    -- On the unit circle, $|Q₁(z)| = |Q₀(z)| / \prod |αᵢ|$.
    have hQ₁_eval_circle : ∀ z : Circle, ‖(hQ₁.choose.eval (z : ℂ))‖ = ‖(Q₀.eval (z : ℂ))‖ / Multiset.prod (Multiset.map (fun α => ‖α‖) T) := by
      intro z
      have hQ₁_eval_circle_step : ∀ α ∈ T, ‖(Polynomial.eval (z : ℂ) (Polynomial.X - Polynomial.C (conjInv α)))‖ = ‖(Polynomial.eval (z : ℂ) (Polynomial.X - Polynomial.C α))‖ / ‖α‖ := by
        intro α hα
        have hQ₁_eval_circle_step : ‖(z : ℂ) - (starRingEnd ℂ α)⁻¹‖ = ‖(z : ℂ) - α‖ / ‖α‖ := by
          have hQ₁_eval_circle_step : ‖(z : ℂ) - (starRingEnd ℂ α)⁻¹‖ = ‖(z : ℂ) * starRingEnd ℂ α - 1‖ / ‖starRingEnd ℂ α‖ := by
            rw [ inv_eq_one_div, sub_div' ] <;> norm_num;
            intro hα_zero
            have h_defect_zero : (defectPoly n P).eval 0 = 0 := by
              replace hT := congr_arg Multiset.toFinset hT; rw [ Finset.ext_iff ] at hT; specialize hT 0; aesop;
            unfold defectPoly at h_defect_zero; simp_all +decide [ Polynomial.coeff_zero_eq_eval_zero ] ;
            cases n <;> simp_all +decide [ sub_eq_iff_eq_add ];
            unfold conjReverse' at h_defect_zero; simp_all +decide [ Polynomial.coeff_zero_eq_eval_zero ] ;
            simp_all +decide [ Polynomial.eval, Polynomial.eval₂_eq_sum_range ];
            simp_all +decide [ Finset.sum_range_succ', revAt ];
            have := hn ▸ Polynomial.coeff_natDegree; aesop;
          convert hQ₁_eval_circle_step using 2;
          · simp +decide [ Complex.norm_def, Complex.normSq ];
            ring;
            exact congrArg Real.sqrt ( by rw [ show ( z : ℂ ).re ^ 2 = 1 - ( z : ℂ ).im ^ 2 by nlinarith only [ z.2, show ( z : ℂ ).re ^ 2 + ( z : ℂ ).im ^ 2 = 1 from by simp [ ← Complex.normSq_add_mul_I, Complex.normSq_eq_norm_sq ] ] ] ; ring );
          · norm_num [ Complex.norm_def, Complex.normSq ];
        convert hQ₁_eval_circle_step using 1 <;> norm_num [ conjInv ];
      have hQ₁_eval_circle_step : ‖(Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C (conjInv α)) T)).eval (z : ℂ)‖ = Multiset.prod (Multiset.map (fun α => ‖(Polynomial.eval (z : ℂ) (Polynomial.X - Polynomial.C (conjInv α)))‖) T) := by
        have hQ₁_eval_circle_step : ∀ (ms : Multiset ℂ), ‖(Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C (conjInv α)) ms)).eval (z : ℂ)‖ = Multiset.prod (Multiset.map (fun α => ‖(Polynomial.eval (z : ℂ) (Polynomial.X - Polynomial.C (conjInv α)))‖) ms) := by
          intro ms; induction ms using Multiset.induction <;> aesop;
        apply hQ₁_eval_circle_step;
      have hQ₁_eval_circle_step : ‖(Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C α) T)).eval (z : ℂ)‖ = Multiset.prod (Multiset.map (fun α => ‖(Polynomial.eval (z : ℂ) (Polynomial.X - Polynomial.C α))‖) T) := by
        have hQ₁_eval_circle_step : ∀ (ms : Multiset ℂ), ‖(Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C α) ms)).eval (z : ℂ)‖ = Multiset.prod (Multiset.map (fun α => ‖(Polynomial.eval (z : ℂ) (Polynomial.X - Polynomial.C α))‖) ms) := by
          intro ms; induction ms using Multiset.induction <;> aesop;
        apply hQ₁_eval_circle_step;
      have := hQ₁.choose_spec.2; aesop;
    -- Let's choose $s$ such that $|s|^2 = |lc| / \prod |αᵢ|$.
    obtain ⟨s, hs⟩ : ∃ s : ℂ, s ≠ 0 ∧ ‖s‖^2 = ‖lc‖ / Multiset.prod (Multiset.map (fun α => ‖α‖) T) := by
      have h_prod_pos : 0 < Multiset.prod (Multiset.map (fun α => ‖α‖) T) := by
        have h_prod_pos : ∀ α ∈ T, α ≠ 0 := by
          intro α hα
          have hα_root : α ∈ (defectPoly n P).roots := by
            exact hT.symm ▸ Multiset.mem_add.mpr ( Or.inl hα );
          exact?;
        exact Multiset.prod_pos <| Multiset.forall_mem_map_iff.mpr fun x hx => norm_pos_iff.mpr <| h_prod_pos x hx;
      use Real.sqrt (‖lc‖ / Multiset.prod (Multiset.map (fun α => ‖α‖) T));
      norm_num +zetaDelta at *;
      exact ⟨ ⟨ Q₁, ne_of_gt <| Real.sqrt_pos.mpr h_prod_pos ⟩, by rw [ abs_of_nonneg <| Real.sqrt_nonneg _, abs_of_nonneg <| Real.sqrt_nonneg _, div_pow, Real.sq_sqrt <| by positivity, Real.sq_sqrt <| by positivity ] ⟩;
    use s;
    simp_all +decide [ mul_assoc, mul_div_cancel₀ ];
    intro z; rw [ hQ₁.choose_spec.1 ] ; simp +decide [ hQ₁_eval_circle z, mul_assoc, mul_comm, mul_left_comm, sq ] ;
    grind +extAll;
  refine' ⟨ Polynomial.C s * Q₀, _, _ ⟩ <;> simp_all +decide [ Polynomial.natDegree_C_mul ];
  · have := Polynomial.card_roots' ( defectPoly n P ) ; simp_all +decide [ Polynomial.natDegree_le_iff_degree_le ] ;
    linarith [ show Polynomial.natDegree ( defectPoly n P ) ≤ 2 * n from defectPoly_natDegree_le P n hn.le ];
  · intro z
    have h_eval : ‖(defectPoly n P).eval (z : ℂ)‖ = ‖(z : ℂ) ^ n * (1 - ‖P.eval (z : ℂ)‖ ^ 2)‖ := by
      convert congr_arg Norm.norm ( defectPoly_eval_circle P n hn.le z ) using 1;
      norm_cast;
    simp_all +decide [ mul_pow ];
    norm_cast ; norm_num [ abs_of_nonneg, hP_strict z |> le_of_lt ]

/-! ## The strict Fejér-Riesz core. -/

lemma fejer_riesz_strict_core (P : ℂ[X])
    (hP_ne : P ≠ 0) (hP_deg : 1 ≤ P.natDegree) (hP_c0 : P.coeff 0 ≠ 0)
    (hP_strict : ∀ z : Circle, ‖P.eval (z : ℂ)‖ < 1) :
    ∃ Q : ℂ[X],
      Q.natDegree ≤ P.natDegree ∧
        ∀ z : Circle, ‖P.eval (z : ℂ)‖ ^ 2 + ‖Q.eval (z : ℂ)‖ ^ 2 = 1 := by
  set n := P.natDegree
  set R := defectPoly n P
  have hR_ne : R ≠ 0 := defectPoly_ne_zero P n le_rfl hP_strict
  have hR_self : conjReverse' (2 * n) R = R := defectPoly_self_reciprocal P n le_rfl
  have hR_deg : R.natDegree ≤ 2 * n := defectPoly_natDegree_le P n le_rfl
  have hR_no_circle : ∀ z : Circle, R.eval (z : ℂ) ≠ 0 :=
    defectPoly_no_roots_circle P n le_rfl hP_strict
  -- Apply Multiset.halving to the roots of R
  have h_invol : ∀ α, conjInv (conjInv α) = α := conjInv_invol
  have h_fp_free : ∀ α ∈ R.roots, conjInv α ≠ α := by
    intro α hα
    exact Ne.symm (ne_conj_inv_of_norm_ne_one α
      (root_norm_ne_one_of_no_circle_roots R α hα hR_no_circle)
      (defectPoly_root_ne_zero P n rfl hP_ne hP_deg hP_c0 α hα))
  have h_closed : ∀ α ∈ R.roots, conjInv α ∈ R.roots := by
    intro α hα
    have : R.IsRoot (conjInv α) :=
      self_reciprocal_root_inv R (2 * n) hR_ne hR_deg hR_self α
        (Polynomial.isRoot_of_mem_roots hα)
    exact (Polynomial.mem_roots hR_ne).mpr this
  have h_count : ∀ α ∈ R.roots, R.roots.count α = R.roots.count (conjInv α) :=
    defectPoly_root_count_conjInv P n rfl hP_ne hP_deg hP_c0 hP_strict
  obtain ⟨T, hT, hTcard⟩ :=
    Multiset.halving R.roots conjInv h_invol h_fp_free h_closed h_count
  exact fejer_riesz_from_halving P n rfl hP_ne hP_deg hP_c0 hP_strict T hT hTcard

end Submission.Helpers