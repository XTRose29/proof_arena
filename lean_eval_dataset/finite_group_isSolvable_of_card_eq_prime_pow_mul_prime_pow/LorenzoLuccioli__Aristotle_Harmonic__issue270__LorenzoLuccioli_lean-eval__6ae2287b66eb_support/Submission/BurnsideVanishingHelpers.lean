import Mathlib

/-!
# Helper lemmas for Burnside vanishing

This file provides the algebraic/analytic helper lemmas needed for the
Burnside vanishing argument: the coprime integrality (Bezout), eigenvalue bounds,
Kronecker-type argument, and scalar contradiction.
-/

set_option maxHeartbeats 800000

open scoped Classical
noncomputable section

namespace Submission.BurnsideVanishingHelpers

/-! ## Bezout integrality -/

/-- If χ is an algebraic integer, cs*χ/d is an algebraic integer, and gcd(d,cs) = 1,
    then χ/d is an algebraic integer. -/
lemma integral_of_coprime (χ : ℂ) (d cs : ℕ)
    (hd : (d : ℂ) ≠ 0)
    (hχ : IsIntegral ℤ χ)
    (hω : IsIntegral ℤ (cs * χ / (d : ℂ)))
    (hcop : Nat.Coprime d cs) :
    IsIntegral ℤ (χ / (d : ℂ)) := by
  obtain ⟨a, b, hab⟩ : ∃ a b : ℤ, a * d + b * cs = 1 := by
    have h_bezout : ∃ a b : ℤ, a * d + b * cs = Nat.gcd d cs := by
      exact Int.gcd_eq_gcd_ab d cs ▸ ⟨ Int.gcdA d cs, Int.gcdB d cs, by ring ⟩;
    aesop;
  have h_eq : χ / (d : ℂ) = a * χ + b * (cs * χ / (d : ℂ)) := by
    field_simp;
    norm_cast; ring_nf at *; aesop;
  exact h_eq.symm ▸ IsIntegral.add ( IsIntegral.mul ( isIntegral_algebraMap ) hχ ) ( IsIntegral.mul ( isIntegral_algebraMap ) hω )

/-! ## Norm of root of unity -/

/-- If z^N = 1 with N > 0, then ‖z‖ = 1. -/
lemma norm_root_of_unity (z : ℂ) (N : ℕ) (hN : 0 < N) (hz : z ^ N = 1) : ‖z‖ = 1 := by
  simpa [ hN.ne', pow_eq_one_iff_of_nonneg ] using congr_arg Norm.norm hz

/-! ## Eigenvalue bound: |trace(M)| ≤ d when M^N = I -/

/-- For a matrix M with M^N = I (N > 0), |tr(M)| ≤ d (the dimension). -/
lemma norm_trace_le_dim {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) (N : ℕ) (hN : 0 < N)
    (hM : M ^ N = 1) :
    ‖Matrix.trace M‖ ≤ d := by
  have h_eigenvalues : ∀ (r : ℂ), r ∈ (Matrix.charpoly M).roots → r ^ N = 1 := by
    intro r hr;
    nontriviality;
    obtain ⟨ v, hv ⟩ := ( Matrix.exists_mulVec_eq_zero_iff.mpr <| show Matrix.det ( M - Matrix.scalar ( Fin d ) r ) = 0 from by
                                                                    rw [ Matrix.det_eq_sign_charpoly_coeff ];
                                                                    simp_all +decide [ Matrix.charpoly, Matrix.det_apply' ];
                                                                    simp_all +decide [ Polynomial.eval_finset_sum, Polynomial.eval_prod, Polynomial.coeff_zero_eq_eval_zero ];
                                                                    convert hr.2 using 1;
                                                                    exact Finset.sum_congr rfl fun _ _ => by congr; ext; by_cases h : ‹Equiv.Perm ( Fin d )› ‹_› = ‹_› <;> simp +decide [ h ] ; );
    have h_eigenvalue_pow : (M ^ N).mulVec v = r ^ N • v := by
      refine' Nat.recOn N _ _ <;> simp_all +decide [ pow_succ', mul_assoc, map_mul ] ;
      intro n hn; simp_all +decide [ ← Matrix.mulVec_mulVec, sub_eq_iff_eq_add ] ;
      simp_all +decide [ sub_eq_iff_eq_add, Matrix.sub_mulVec ];
      rw [ Matrix.mulVec_smul, hv.2, smul_smul, mul_comm ];
    exact smul_left_injective _ hv.1 <| by simpa [ hM ] using h_eigenvalue_pow.symm;
  have h_trace : ‖Matrix.trace M‖ ≤ ∑ r ∈ (Matrix.charpoly M).roots.toFinset, Multiset.count r (Matrix.charpoly M).roots := by
    have h_trace : Matrix.trace M = ∑ r ∈ (Matrix.charpoly M).roots.toFinset, Multiset.count r (Matrix.charpoly M).roots * r := by
      have h_trace : Matrix.trace M = Multiset.sum (Polynomial.roots (Matrix.charpoly M)) := by
        exact Matrix.trace_eq_sum_roots_charpoly M;
      rw [ h_trace, Finset.sum_multiset_count ];
      norm_num [ Algebra.smul_def ];
    rw [ h_trace ];
    refine' le_trans ( norm_sum_le _ _ ) _;
    norm_num [ norm_mul ];
    exact Finset.sum_le_sum fun x hx => mul_le_of_le_one_right ( Nat.cast_nonneg _ ) ( by have := h_eigenvalues x ( Multiset.mem_toFinset.mp hx ) ; have := congr_arg Norm.norm this; norm_num at this; rw [ pow_eq_one_iff_of_nonneg ] at this <;> aesop );
  refine le_trans h_trace ?_;
  norm_cast;
  have := Polynomial.card_roots' ( Matrix.charpoly M );
  rw [ ← Multiset.toFinset_sum_count_eq ] at * ; aesop

/-! ## Kronecker-type vanishing: sub-lemmas -/

/-
For a monic polynomial p over ℂ, eval at 0 = (-1)^deg * product of roots
-/
lemma monic_eval_zero_eq_neg_one_pow_mul_prod_roots (p : Polynomial ℂ) (hp : p.Monic) :
    p.eval 0 = (-1) ^ p.natDegree * p.roots.prod := by
  nth_rw 2 [ ← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp ];
  · simp +decide [ Polynomial.eval_multiset_prod ];
    conv_lhs => rw [ ← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq hp ( by
      exact IsAlgClosed.card_roots_eq_natDegree ) ];
    induction p.roots using Multiset.induction <;> simp_all +decide [ pow_succ, mul_assoc ];
    ring;
  · exact IsAlgClosed.card_roots_eq_natDegree

/-
The constant term of minpoly ℤ α is a nonzero integer when α ≠ 0
-/
lemma minpoly_const_term_ne_zero (α : ℂ) (hα : α ≠ 0) (hint : IsIntegral ℤ α) :
    (minpoly ℤ α).eval 0 ≠ 0 := by
  by_contra htra;
  -- Since $0$ is a root of the minimal polynomial, we have $minpoly ℤ α = X * q$ for some polynomial $q$.
  obtain ⟨q, hq⟩ : ∃ q : Polynomial ℤ, minpoly ℤ α = Polynomial.X * q := by
    simpa using Polynomial.dvd_iff_isRoot.mpr htra;
  have := minpoly.aeval ℤ α; simp_all +decide [ mul_assoc ] ;
  have := minpoly.irreducible ‹IsIntegral ℤ α›; simp_all +decide [ Polynomial.aeval_def ] ;
  rw [ irreducible_mul_iff ] at this;
  simp_all +decide [ Polynomial.isUnit_iff ];
  rcases this with ( ⟨ h₁, r, hr, rfl ⟩ | ⟨ h₁, r, hr, hr' ⟩ ) <;> simp_all +decide [ Polynomial.eval₂_eq_eval_map ];
  exact absurd ( congr_arg Polynomial.derivative hr' ) ( by norm_num )

/-
Product of reals ≤ 1 in [0,∞) equals 1 implies each = 1
-/
lemma multiset_prod_eq_one_of_le_one (s : Multiset ℝ) (hs : ∀ x ∈ s, 0 ≤ x ∧ x ≤ 1)
    (hprod : s.prod = 1) : ∀ x ∈ s, x = 1 := by
  by_contra h_contra; push_neg at h_contra; obtain ⟨x, hx, hx_ne⟩ : ∃ x ∈ s, x ≠ 1 := by
    exact h_contra;
  -- Since $x$ is in $s$ and $x \neq 1$, we have $0 \leq x < 1$.
  have hx_lt_one : 0 ≤ x ∧ x < 1 := by
    exact ⟨ hs x hx |>.1, lt_of_le_of_ne ( hs x hx |>.2 ) hx_ne ⟩;
  -- Since $x$ is in $s$ and $x < 1$, removing $x$ from $s$ and multiplying the remaining elements will result in a product less than 1.
  have h_prod_lt_one : Multiset.prod (s.erase x) ≤ 1 := by
    have h_prod_lt_one : ∀ {t : Multiset ℝ}, (∀ x ∈ t, 0 ≤ x ∧ x ≤ 1) → Multiset.prod t ≤ 1 := by
      intros t ht; induction t using Multiset.induction <;> norm_num;
      exact mul_le_one₀ ( ht _ ( Multiset.mem_cons_self _ _ ) |>.2 ) ( by apply_rules [ Multiset.prod_nonneg ] ; intros; linarith [ ht _ ( Multiset.mem_cons_of_mem ‹_› ) ] ) ( by apply_assumption; intros; exact ht _ ( Multiset.mem_cons_of_mem ‹_› ) );
    exact h_prod_lt_one fun y hy => hs y <| Multiset.mem_of_mem_erase hy;
  have := Multiset.prod_erase hx; nlinarith;

/-
Mapping minpoly ℤ to ℂ gives the same polynomial as mapping minpoly ℚ to ℂ
-/
lemma minpoly_map_eq (α : ℂ) (hint : IsIntegral ℤ α) :
    (minpoly ℤ α).map (algebraMap ℤ ℂ) = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
  convert Polynomial.map_map ( algebraMap ℚ ℂ ) _ _ using 1;
  any_goals exact minpoly ℚ α;
  any_goals exact RingHom.id ℂ;
  · have := minpoly.isIntegrallyClosed_eq_field_fractions' ℚ ‹_›;
    aesop;
  · rfl

/-! ## Kronecker-type vanishing (main) -/

/-
If α ∈ ℂ is a nonzero algebraic integer with
    all roots of its minimal polynomial over ℚ (evaluated in ℂ) having |·| ≤ 1,
    then |α| = 1.
-/
lemma abs_eq_one_of_integral_bounded (α : ℂ) (hα : α ≠ 0)
    (hint : IsIntegral ℤ α)
    (hbound : ∀ β : ℂ, ((minpoly ℚ α).map (algebraMap ℚ ℂ)).IsRoot β → ‖β‖ ≤ 1) :
    ‖α‖ = 1 := by
  -- Let p = (minpoly ℤ α).map (algebraMap ℤ ℂ). By minpoly_map_eq, p = (minpoly ℚ α).map (algebraMap ℚ ℂ).
  set p : Polynomial ℂ := (minpoly ℤ α).map (algebraMap ℤ ℂ)
  have hp_map : p = (minpoly ℚ α).map (algebraMap ℚ ℂ) := by
    convert minpoly_map_eq α ‹_›;
  -- Step 6: ‖p.eval 0‖ = ∏ ‖root‖ (use norm_mul, norm_pow, norm_neg, fact that |(-1)^n| = 1, and Multiset.map_prod/norm_multiset_prod).
  have h_norm_prod : ‖p.eval 0‖ = Multiset.prod (Multiset.map (fun x => ‖x‖) p.roots) := by
    -- By definition of polynomial multiplication and the fact that p is monic, we have p.eval 0 = (-1)^p.natDegree * p.roots.prod.
    have h_eval_zero : p.eval 0 = (-1) ^ p.natDegree * p.roots.prod := by
      apply monic_eval_zero_eq_neg_one_pow_mul_prod_roots;
      exact Polynomial.Monic.map _ ( minpoly.monic ‹_› );
    norm_num [ h_eval_zero ];
    induction p.roots using Multiset.induction <;> aesop;
  -- Step 7: p.eval 0 = (algebraMap ℤ ℂ) ((minpoly ℤ α).eval 0), which is a nonzero integer. So ‖p.eval 0‖ ≥ 1.
  have h_norm_eval_zero : ‖p.eval 0‖ ≥ 1 := by
    have h_norm_eval_zero : ‖p.eval 0‖ = ‖(minpoly ℤ α).eval 0‖ := by
      simp [p];
      norm_num [ Norm.norm ];
    have h_norm_eval_zero : ‖(minpoly ℤ α).eval 0‖ ≥ 1 := by
      have h_eval_zero_ne_zero : (minpoly ℤ α).eval 0 ≠ 0 := by
        grind +suggestions
      norm_num +zetaDelta at *;
      exact h_norm_eval_zero ▸ mod_cast abs_pos.mpr h_eval_zero_ne_zero;
    linarith;
  -- Step 8: ∏ ‖root‖ ≤ 1 (from step 3, product of ≤ 1 terms). Combined with step 7: ∏ ‖root‖ = 1.
  have h_prod_one : Multiset.prod (Multiset.map (fun x => ‖x‖) p.roots) = 1 := by
    refine' le_antisymm _ _;
    · have h_prod_le_one : ∀ x ∈ p.roots, ‖x‖ ≤ 1 := by
        aesop;
      have h_prod_le_one : ∀ {s : Multiset ℂ}, (∀ x ∈ s, ‖x‖ ≤ 1) → Multiset.prod (Multiset.map (fun x => ‖x‖) s) ≤ 1 := by
        intros s hs; induction s using Multiset.induction <;> norm_num at *;
        exact mul_le_one₀ hs.1 ( Multiset.prod_nonneg <| by aesop ) ( by aesop );
      exact h_prod_le_one ‹_›;
    · linarith;
  -- Step 9: By multiset_prod_eq_one_of_le_one, each ‖root‖ = 1.
  have h_each_one : ∀ x ∈ p.roots, ‖x‖ = 1 := by
    intros x hx_eq_one_of_le_one;
    apply_rules [ multiset_prod_eq_one_of_le_one ];
    · simp +zetaDelta at *;
      rintro _ x hx₁ hx₂ rfl; specialize hbound x; simp_all +decide [ Polynomial.aeval_def, Polynomial.eval_map ] ;
    · exact Multiset.mem_map_of_mem _ hx_eq_one_of_le_one;
  convert h_each_one α _;
  simp +zetaDelta at *;
  exact ⟨ by rw [ Polynomial.map_eq_zero_iff ] <;> aesop_cat, by rw [ Polynomial.eval_map ] ; exact minpoly.aeval ℤ α ⟩

/-! ## Triangle inequality equality for unit complex numbers -/

/-
If complex numbers all have norm 1 and their sum has norm equal to the count,
    then they are all equal.
-/
lemma all_eq_of_norm_sum_eq_card {ι : Type*} [Fintype ι] (z : ι → ℂ)
    (hz : ∀ i, ‖z i‖ = 1) (hsum : ‖∑ i, z i‖ = Fintype.card ι) :
    ∀ i j, z i = z j := by
  -- Let $u = S / d$.
  obtain ⟨u, hu⟩ : ∃ u : ℂ, ‖u‖ = 1 ∧ ∑ i, (z i * starRingEnd ℂ u).re = Fintype.card ι := by
    by_cases h : ∑ i, z i = 0 <;> simp_all +decide [ Complex.normSq, Complex.norm_def ];
    · exact ⟨ 1, by norm_num, by simpa [ ← hsum ] using congr_arg Complex.re h ⟩;
    · refine' ⟨ ( ∑ i, z i ) / ↑ ( Fintype.card ι ), _, _ ⟩ <;> simp_all +decide [ Complex.normSq, Complex.div_re, Complex.div_im ];
      · rw [ Real.sqrt_eq_iff_mul_self_eq ] at hsum;
        · field_simp;
          rw [ div_eq_iff ] <;> nlinarith [ show ( Fintype.card ι : ℝ ) > 0 from Nat.cast_pos.mpr ( Fintype.card_pos_iff.mpr ⟨ Classical.choose ( Finset.nonempty_of_sum_ne_zero ( show ∑ i, z i ≠ 0 from h ) ) ⟩ ) ];
        · nlinarith;
        · positivity;
      · by_cases h' : Fintype.card ι = 0 <;> simp_all +decide [ ← Finset.sum_mul _ _ _, mul_div_mul_right ];
        simp_all +decide [ Finset.sum_add_distrib, ← Finset.sum_mul _ _ _ ];
        grind +extAll;
  -- For any $i$, we have $\|z_i - u\|^2 = 2 - 2(z_i \overline{u}).re$.
  have h_sq_norm : ∀ i, ‖z i - u‖^2 = 2 - 2 * (z i * starRingEnd ℂ u).re := by
    simp_all +decide [ Complex.normSq, Complex.sq_norm ];
    simp_all +decide [ Complex.normSq, Complex.norm_def ];
    intro i; linear_combination' hz i + hu.1;
  -- Since $\sum_{i} (z_i \overline{u}).re = d$, we have $\sum_{i} \|z_i - u\|^2 = 0$.
  have h_sum_sq_norm : ∑ i, ‖z i - u‖^2 = 0 := by
    simp_all +decide [ ← Finset.mul_sum _ _ _, ← Finset.sum_mul ];
    ring;
  rw [ Finset.sum_eq_zero_iff_of_nonneg fun _ _ => sq_nonneg _ ] at h_sum_sq_norm;
  simp_all +decide [ sub_eq_iff_eq_add ]

/-! ## Matrix is scalar from charpoly and finite order -/

/-
If M^N = I (N > 0) and charpoly M = (X - ζ)^d, then M = ζ · I.
    Proof: minpoly M divides both X^N - 1 (separable) and (X - ζ)^d,
    so minpoly divides X - ζ, hence M = ζI.
-/
lemma matrix_scalar_of_pow_eq_one_charpoly {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (ζ : ℂ) (N : ℕ) (hN : 0 < N) (hM : M ^ N = 1)
    (hchar : M.charpoly = (Polynomial.X - Polynomial.C ζ) ^ d) :
    M = ζ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  -- The minimal polynomial of M divides X^N - 1 (since M^N = I, so aeval M (X^N - 1) = 0, and minpoly.dvd gives the divisibility).
  have hminpoly_divides_Xn_minus_1 : minpoly ℂ M ∣ Polynomial.X ^ N - 1 := by
    exact minpoly.dvd ℂ M ( by aesop );
  -- Since minpoly ℂ M divides X^N - 1 and (X - ζ)^d, it must be that minpoly ℂ M is a power of (X - ζ).
  have hminpoly_power_of_X_minus_zeta : ∃ k : ℕ, k ≤ d ∧ minpoly ℂ M = (Polynomial.X - Polynomial.C ζ) ^ k := by
    have hminpoly_power_of_X_minus_zeta : minpoly ℂ M ∣ (Polynomial.X - Polynomial.C ζ) ^ d := by
      exact hchar ▸ Matrix.minpoly_dvd_charpoly M;
    rw [ dvd_prime_pow ] at hminpoly_power_of_X_minus_zeta;
    · obtain ⟨ k, hk₁, hk₂ ⟩ := hminpoly_power_of_X_minus_zeta;
      exact ⟨ k, hk₁, Polynomial.eq_of_monic_of_associated ( minpoly.monic ( show IsIntegral ℂ M from by exact ( Matrix.isIntegral M ) ) ) ( Polynomial.monic_X_sub_C ζ |> Polynomial.Monic.pow <| k ) hk₂ ⟩;
    · exact Polynomial.prime_X_sub_C ζ;
  rcases hminpoly_power_of_X_minus_zeta with ⟨ k, hk₁, hk₂ ⟩ ; rcases k with ( _ | k ) <;> simp_all +decide [ Polynomial.dvd_iff_isRoot ] ;
  · nontriviality;
    have := minpoly.aeval ℂ M; aesop;
  · have := congr_arg ( Polynomial.derivative ) hminpoly_divides_Xn_minus_1.choose_spec; norm_num at this; replace this := congr_arg ( Polynomial.eval ζ ) this; simp_all +decide [ Polynomial.derivative_pow ] ;
    rcases k with ( _ | k ) <;> simp_all +decide [ pow_succ' ];
    · have := minpoly.aeval ℂ M; simp_all +decide [ sub_eq_iff_eq_add ] ;
      simp +decide [ Algebra.smul_def ];
    · cases this <;> simp_all +decide [ ne_of_gt ];
      obtain ⟨ p, hp ⟩ := hminpoly_divides_Xn_minus_1; replace hp := congr_arg ( Polynomial.eval 0 ) hp; norm_num [ hN.ne' ] at hp;

/-! ## All-eigenvalues-equal from trace norm -/

/-
If M^N = I and |tr(M)| = d, then all eigenvalues are equal,
    i.e., M is a scalar matrix.
-/
lemma scalar_of_norm_trace_eq_dim {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ)
    (N : ℕ) (hN : 0 < N) (hM : M ^ N = 1)
    (htrace : ‖Matrix.trace M‖ = d) :
    ∃ ζ : ℂ, M = ζ • (1 : Matrix (Fin d) (Fin d) ℂ) := by
  -- The eigenvalues (roots of charpoly) of M are N-th roots of unity, each with norm 1. Write trace = sum of roots of charpoly using Matrix.trace_eq_sum_roots_charpoly. The roots are exactly the eigenvalues with multiplicity.
  have h_eigenvalues : ∀ β ∈ M.charpoly.roots, ‖β‖ = 1 := by
    intro β hβ
    have hβ_pow : β ^ N = 1 := by
      -- Since β is an eigenvalue of M, there exists a nonzero vector v such that Mv = βv.
      obtain ⟨v, hv⟩ : ∃ v : Fin d → ℂ, v ≠ 0 ∧ M.mulVec v = β • v := by
        have := Matrix.exists_mulVec_eq_zero_iff.mpr ( show Matrix.det ( M - β • 1 ) = 0 from ?_ );
        · simp_all +decide [ sub_eq_iff_eq_add, Matrix.sub_mulVec ];
          simp_all +decide [ Matrix.smul_eq_diagonal_mul ];
        · rw [ Matrix.det_eq_sign_charpoly_coeff ];
          simp_all +decide [ Matrix.charpoly, Matrix.det_apply' ];
          convert hβ.2 using 1;
          simp +decide [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Polynomial.coeff_zero_eq_eval_zero ];
          exact Finset.sum_congr rfl fun _ _ => by congr; ext; by_cases h : ‹Equiv.Perm ( Fin d ) › ‹_› = ‹_› <;> simp +decide [ h ] ;
      -- Applying M^N to v gives us β^N * v.
      have h_apply : (M ^ N).mulVec v = β ^ N • v := by
        refine' Nat.recOn N _ _ <;> simp_all +decide [ pow_succ', Matrix.mulVec_smul ];
        intro n hn; simp_all +decide [ ← Matrix.mulVec_mulVec, ← smul_assoc ] ;
        rw [ Matrix.mulVec_smul, hv.2, smul_smul, mul_comm ];
      exact smul_left_injective _ hv.1 <| by simpa [ hM ] using h_apply.symm;
    exact norm_root_of_unity β N hN hβ_pow;
  -- Since the trace is the sum of the eigenvalues and their norms are all 1, all eigenvalues must be equal.
  have h_all_equal : ∃ ζ : ℂ, M.charpoly.roots = Multiset.replicate d ζ := by
    -- By all_eq_of_norm_sum_eq_card (if we can apply it to roots), all eigenvalues are equal. Let's denote this common eigenvalue by ζ.
    obtain ⟨ζ, hζ⟩ : ∃ ζ : ℂ, ∀ β ∈ M.charpoly.roots, β = ζ := by
      have h_sum_roots : ‖M.trace‖ = ‖(M.charpoly.roots.sum : ℂ)‖ := by
        rw [ Matrix.trace_eq_sum_roots_charpoly ];
      have h_all_eq : ∀ (s : Multiset ℂ), (∀ β ∈ s, ‖β‖ = 1) → ‖s.sum‖ = s.card → ∀ β ∈ s, ∀ γ ∈ s, β = γ := by
        intros s hs hsum β hβ γ hγ;
        -- Convert the multiset to a list and apply the lemma.
        obtain ⟨l, hl⟩ : ∃ l : List ℂ, s = Multiset.ofList l := by
          exact ⟨ s.toList, by simpa ⟩;
        have h_all_eq : ∀ (l : List ℂ), (∀ β ∈ l, ‖β‖ = 1) → ‖l.sum‖ = l.length → ∀ β ∈ l, ∀ γ ∈ l, β = γ := by
          intros l hl hsum β hβ γ hγ;
          have := all_eq_of_norm_sum_eq_card ( fun i : Fin l.length => l.get i ) ?_ ?_ <;> simp_all +decide [ Finset.sum_range, List.sum_ofFn ];
          obtain ⟨ i, hi ⟩ := List.mem_iff_get.mp hβ; obtain ⟨ j, hj ⟩ := List.mem_iff_get.mp hγ; specialize this ⟨ i, by aesop ⟩ ⟨ j, by aesop ⟩ ; aesop;
        specialize h_all_eq l ; aesop;
      have h_card_roots : Multiset.card M.charpoly.roots = d := by
        have h_card_roots : Multiset.card M.charpoly.roots = Polynomial.natDegree M.charpoly := by
          nontriviality;
          exact IsAlgClosed.card_roots_eq_natDegree;
        rw [ h_card_roots, Matrix.charpoly_natDegree_eq_dim ] ; aesop;
      by_cases h : M.charpoly.roots = 0;
      · aesop;
      · exact ⟨ Classical.choose ( Multiset.exists_mem_of_ne_zero h ), fun β hβ => h_all_eq _ h_eigenvalues ( by aesop ) _ hβ _ ( Classical.choose_spec ( Multiset.exists_mem_of_ne_zero h ) ) ⟩;
    have h_card : Multiset.card M.charpoly.roots = d := by
      have h_card_roots : Multiset.card (M.charpoly.roots) = M.charpoly.natDegree := by
        nontriviality;
        exact IsAlgClosed.card_roots_eq_natDegree;
      rw [ h_card_roots, Matrix.charpoly_natDegree_eq_dim ] ; aesop;
    exact ⟨ ζ, Multiset.eq_replicate.mpr ⟨ h_card, hζ ⟩ ⟩;
  -- Since the roots of the characteristic polynomial are all equal to ζ, the characteristic polynomial is (X - ζ)^d.
  obtain ⟨ζ, hζ⟩ := h_all_equal
  have h_charpoly : M.charpoly = (Polynomial.X - Polynomial.C ζ) ^ d := by
    rw [ ← Polynomial.prod_multiset_X_sub_C_of_monic_of_roots_card_eq ( Matrix.charpoly_monic M ) ] <;> aesop;
  exact ⟨ ζ, matrix_scalar_of_pow_eq_one_charpoly M ζ N hN hM h_charpoly ⟩

/-! ## Scalar matrices in Wedderburn factor contradiction -/

/-
If G is simple and the i-th Wedderburn representation sends g ≠ 1
    to a scalar matrix, then d_i ≤ 1.
-/
lemma wedderburn_scalar_implies_dim_one (G : Type) [Group G] [Fintype G] [DecidableEq G]
    (hsimple : IsSimpleGroup G)
    {n : ℕ} (d : Fin n → ℕ) (hd : ∀ i, NeZero (d i))
    (e : MonoidAlgebra ℂ G ≃ₐ[ℂ] ∀ i, Matrix (Fin (d i)) (Fin (d i)) ℂ)
    (g : G) (hg : g ≠ 1) (i : Fin n)
    (hscalar : ∃ ζ : ℂ, (e (MonoidAlgebra.single g 1)) i = ζ • (1 : Matrix (Fin (d i)) (Fin (d i)) ℂ)) :
    d i ≤ 1 := by
  have h_subalgebra : ∀ h : G, ∃ ζ : ℂ, e (MonoidAlgebra.single h 1) i = ζ • 1 := by
    -- Since $g$ is in the normal subgroup $K$, and $K$ is normal, for any $h \in G$, $hgh^{-1} \in K$.
    have h_normal_subgroup : ∀ h : G, ∃ ζ : ℂ, e (MonoidAlgebra.single (h * g * h⁻¹) 1) i = ζ • 1 := by
      intro h
      obtain ⟨ζ, hζ⟩ := hscalar
      use ζ;
      have h_conj : e (MonoidAlgebra.single (h * g * h⁻¹) 1) = e (MonoidAlgebra.single h 1) * e (MonoidAlgebra.single g 1) * e (MonoidAlgebra.single h⁻¹ 1) := by
        simp +decide [ ← map_mul ];
      replace h_conj := congr_fun h_conj i; simp_all +decide [ Matrix.mul_assoc ] ;
      have h_conj : e (MonoidAlgebra.single h 1) * e (MonoidAlgebra.single h⁻¹ 1) = 1 := by
        rw [ ← map_mul ] ; aesop;
      replace h_conj := congr_fun h_conj i; aesop;
    -- Since $g$ is in the normal subgroup $K$, and $K$ is normal, for any $h \in G$, $hgh^{-1} \in K$. Therefore, $K = G$.
    have h_normal_subgroup_eq_G : ∀ h : G, h ∈ Subgroup.closure {h * g * h⁻¹ | h : G} := by
      have h_normal_subgroup_eq_G : Subgroup.closure {h * g * h⁻¹ | h : G} = ⊤ := by
        have h_normal_subgroup_eq_G : Subgroup.Normal (Subgroup.closure {h * g * h⁻¹ | h : G}) := by
          constructor;
          intro n hn g_1;
          refine' Subgroup.closure_induction ( fun x hx => _ ) _ _ _ hn;
          · rcases hx with ⟨ h, rfl ⟩ ; exact Subgroup.subset_closure ⟨ g_1 * h, by group ⟩ ;
          · simp +decide [ Subgroup.one_mem ];
          · exact fun x y hx hy hx' hy' => by simpa [ mul_assoc ] using Subgroup.mul_mem _ hx' hy';
          · exact fun x hx hx' => by simpa [ mul_assoc ] using Subgroup.inv_mem _ hx';
        have := hsimple.2 ( Subgroup.closure { x | ∃ h : G, h * g * h⁻¹ = x } ) h_normal_subgroup_eq_G;
        exact this.resolve_left fun h => hg <| by simpa using Subgroup.mem_bot.mp <| h ▸ Subgroup.subset_closure ⟨ 1, by simp +decide ⟩ ;
      aesop;
    intro h; specialize h_normal_subgroup_eq_G h; induction h_normal_subgroup_eq_G using Subgroup.closure_induction ; aesop;
    · exact ⟨ 1, by erw [ show e ( MonoidAlgebra.single 1 1 ) = 1 from e.map_one ] ; simp +decide ⟩;
    · rename_i x y hx hy hx' hy';
      obtain ⟨ ζ₁, hζ₁ ⟩ := hx'; obtain ⟨ ζ₂, hζ₂ ⟩ := hy'; use ζ₁ * ζ₂; simp_all +decide [ mul_assoc, Algebra.smul_def ] ;
      convert congr_arg ( fun z => z i ) ( e.map_mul ( MonoidAlgebra.single x 1 ) ( MonoidAlgebra.single y 1 ) ) using 1 ; aesop;
      exact hζ₁.symm ▸ hζ₂.symm ▸ rfl;
    · rename_i x hx ih; obtain ⟨ ζ, hζ ⟩ := ih; use ζ⁻¹; simp_all +decide [ Algebra.smul_def ] ;
      have h_inv : e (MonoidAlgebra.single x 1) i * e (MonoidAlgebra.single x⁻¹ 1) i = 1 := by
        have h_inv : e (MonoidAlgebra.single x 1 * MonoidAlgebra.single x⁻¹ 1) i = 1 := by
          simp +decide [ MonoidAlgebra.single_mul_single ];
          convert congr_fun ( e.map_one ) i using 1;
        convert h_inv using 1;
        exact congr_arg ( fun f => f i ) ( e.map_mul _ _ ) ▸ rfl;
      by_cases hζ : ζ = 0 <;> simp_all +decide [ Algebra.algebraMap_eq_smul_one ];
      exact eq_inv_smul_iff₀ hζ |>.2 h_inv ▸ by norm_num;
  have h_subalgebra : ∀ x : Matrix (Fin (d i)) (Fin (d i)) ℂ, x ∈ Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (fun h : G => e (MonoidAlgebra.single h 1) i))) → ∃ ζ : ℂ, x = ζ • 1 := by
    intro x hx
    induction' hx using Algebra.adjoin_induction with x hx ihx y hx hy ihx ihy x hx ihx
    all_goals norm_num at *;
    · rcases hx with ⟨ y, rfl ⟩ ; exact h_subalgebra y;
    · exact ⟨ ihx, by simp +decide [ Algebra.smul_def ] ⟩;
    · rcases ihy with ⟨ ζ₁, rfl ⟩ ; rcases x with ⟨ ζ₂, rfl ⟩ ; exact ⟨ ζ₁ + ζ₂, by simp +decide [ add_smul ] ⟩ ;
    · rename_i hx ihx hx' ihx';
      obtain ⟨ ζ₁, hζ₁ ⟩ := hx'; obtain ⟨ ζ₂, hζ₂ ⟩ := ihx'; use ζ₁ * ζ₂; simp +decide [ hζ₁, hζ₂, mul_assoc, smul_smul ] ;
      ring;
  have h_subalgebra : Subalgebra.toSubmodule (Algebra.adjoin ℂ (Set.range (fun h : G => e (MonoidAlgebra.single h 1) i))) = ⊤ := by
    have h_subalgebra : Algebra.adjoin ℂ (Set.range (fun h : G => e (MonoidAlgebra.single h 1) i)) = ⊤ := by
      have h_surjective : Function.Surjective (fun x : MonoidAlgebra ℂ G => e x i) := by
        exact fun x => ⟨ e.symm ( Pi.single i x ), by simp +decide ⟩
      have h_subalgebra : Algebra.adjoin ℂ (Set.range (fun h : G => e (MonoidAlgebra.single h 1) i)) = Algebra.adjoin ℂ (Set.range (fun x : MonoidAlgebra ℂ G => e x i)) := by
        refine' le_antisymm _ _ <;> rw [ Algebra.adjoin_le_iff ] <;> simp +decide [ Set.range_subset_iff ];
        · exact fun x => Algebra.subset_adjoin ⟨ _, rfl ⟩;
        · intro x; induction x using MonoidAlgebra.induction_on; aesop;
          · aesop;
          · convert Subalgebra.smul_mem _ ‹_› _ using 1 ; aesop;
      rw [ h_subalgebra, Algebra.eq_top_iff ];
      exact fun x => by obtain ⟨ y, rfl ⟩ := h_surjective x; exact Algebra.subset_adjoin ⟨ y, rfl ⟩ ;
    exact h_subalgebra.symm ▸ rfl;
  have h_subalgebra : ∀ x : Matrix (Fin (d i)) (Fin (d i)) ℂ, ∃ ζ : ℂ, x = ζ • 1 := by
    simp_all +decide [ SetLike.ext_iff ];
  contrapose! h_subalgebra;
  use Matrix.of (fun j k => if j = ⟨0, by linarith⟩ ∧ k = ⟨1, by linarith⟩ then 1 else 0);
  intro ζ hζ; have := congr_fun ( congr_fun hζ ⟨ 0, by linarith ⟩ ) ⟨ 1, by linarith ⟩ ; norm_num at this;

/-! ## Norm-one via Algebra.norm -/

/-
If α ∈ K (a finite algebraic extension of ℚ inside ℂ) is an algebraic integer,
    α ≠ 0, and every embedding σ : K →ₐ[ℚ] ℂ gives ‖σ(α)‖ ≤ 1,
    then ‖(α : ℂ)‖ = 1.
-/
lemma norm_one_of_integral_embeddings_bounded
    (K : IntermediateField ℚ ℂ) [FiniteDimensional ℚ K]
    (x : K) (hx_ne : x ≠ 0)
    (hx_int : IsIntegral ℤ (algebraMap K ℂ x))
    (hbound : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ ≤ 1) :
    ‖(algebraMap K ℂ x)‖ = 1 := by
  have h_norm_eq_one : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ x)‖ = ∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ := by
    have h_norm_eq_one : (algebraMap ℚ ℂ) (Algebra.norm ℚ x) = ∏ σ : K →ₐ[ℚ] ℂ, σ x := by
      convert Algebra.norm_eq_prod_embeddings ℚ ℂ x;
    rw [ h_norm_eq_one, norm_prod ];
  -- Since each ‖σ x‖ ≤ 1, the product has norm ≤ 1:
  have h_prod_le_one : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ x)‖ ≤ 1 := by
    exact h_norm_eq_one ▸ Finset.prod_le_one ( fun _ _ => norm_nonneg _ ) fun _ _ => hbound _;
  -- Since Algebra.norm ℚ x is an integer, we have ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ x)‖ = 1.
  have h_norm_int : ∃ n : ℤ, (algebraMap ℚ ℂ) (Algebra.norm ℚ x) = n := by
    have h_norm_int : IsIntegral ℤ (Algebra.norm ℚ x) := by
      have h_norm_int : IsIntegral ℤ x := by
        exact IntermediateField.coe_isIntegral_iff.mp hx_int;
      exact Algebra.isIntegral_norm ℚ h_norm_int;
    have h_norm_int : ∀ {q : ℚ}, IsIntegral ℤ q → ∃ n : ℤ, q = n := by
      intro q hq; exact (by
      exact IsIntegrallyClosed.isIntegral_iff.mp hq |> fun ⟨ n, hn ⟩ => ⟨ n, hn.symm ⟩);
    obtain ⟨ n, hn ⟩ := h_norm_int ‹_›; use n; aesop;
  -- Since the norm of an integer is at least 1, we have ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ x)‖ = 1.
  obtain ⟨n, hn⟩ := h_norm_int
  have h_norm_one : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ x)‖ = 1 := by
    have h_norm_one : ‖(algebraMap ℚ ℂ) (Algebra.norm ℚ x)‖ ≥ 1 := by
      have h_norm_one : n ≠ 0 := by
        intro hn_zero
        simp [hn_zero] at hn;
        contradiction;
      simp [hn];
      exact mod_cast abs_pos.mpr h_norm_one;
    exact le_antisymm h_prod_le_one h_norm_one;
  have h_all_one : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ = 1 := by
    intro σ
    by_contra h_contra
    have h_prod_lt_one : ∏ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ < 1 := by
      rw [ Finset.prod_eq_prod_diff_singleton_mul <| Finset.mem_univ σ ];
      exact lt_of_le_of_lt ( mul_le_of_le_one_left ( norm_nonneg _ ) ( Finset.prod_le_one ( fun _ _ => norm_nonneg _ ) fun _ _ => hbound _ ) ) ( lt_of_le_of_ne ( hbound _ ) h_contra )
    linarith [h_norm_eq_one];
  convert h_all_one ( show K →ₐ[ℚ] ℂ from K.val ) using 1

end Submission.BurnsideVanishingHelpers