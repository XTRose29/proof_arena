import Mathlib
import Submission.MultisetPair

set_option maxHeartbeats 1600000

open Polynomial Complex

namespace Submission.Helpers

noncomputable def conjReverse' (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  (Polynomial.reflect n P).map (starRingEnd ℂ)

noncomputable def defectPoly (n : ℕ) (P : ℂ[X]) : ℂ[X] :=
  Polynomial.X ^ n - P * conjReverse' n P

lemma defectPoly_eval_circle (P : ℂ[X]) (n : ℕ) (hn : P.natDegree ≤ n)
    (z : Circle) :
    (defectPoly n P).eval (z : ℂ) =
    (z : ℂ) ^ n * (1 - ↑(‖P.eval (z : ℂ)‖ ^ 2)) := by
  have h_conjReverse : ((P * conjReverse' n P).eval (z : ℂ)) = (z : ℂ) ^ n * (P.eval (z : ℂ) * starRingEnd ℂ (P.eval (z : ℂ))) := by
    have h_conjReverse : (conjReverse' n P).eval (z : ℂ) = (z : ℂ) ^ n * starRingEnd ℂ (P.eval (z : ℂ)) := by
      unfold conjReverse';
      simp +decide [ Polynomial.eval_map, Polynomial.eval₂_def, Polynomial.sum_def, Polynomial.reflect ];
      rw [ Polynomial.eval_eq_sum, Polynomial.sum_def ];
      simp +decide [ revAt, Polynomial.toFinsupp_apply ];
      rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ if_pos ( le_trans ( Polynomial.le_natDegree_of_mem_supp _ hx ) hn ) ] ; rw [ show ( z : ℂ ) ^ ( n - x ) = ( z : ℂ ) ^ n / ( z : ℂ ) ^ x from _ ] ; ring;
      · simp +decide [ Complex.inv_def, Complex.normSq_eq_norm_sq, Complex.norm_exp ];
      · rw [ eq_div_iff ( pow_ne_zero _ <| by simp ), ← pow_add, Nat.sub_add_cancel <| le_trans ( Polynomial.le_natDegree_of_mem_supp _ hx ) hn ];
    rw [ Polynomial.eval_mul, h_conjReverse, mul_left_comm ];
  unfold defectPoly; simp_all +decide [ Complex.mul_conj, Complex.normSq_eq_norm_sq ] ; ring;

lemma defectPoly_no_roots_circle (P : ℂ[X]) (n : ℕ) (hn : P.natDegree ≤ n)
    (hP_strict : ∀ z : Circle, ‖P.eval (z : ℂ)‖ < 1) :
    ∀ z : Circle, (defectPoly n P).eval (z : ℂ) ≠ 0 := by
  intro z
  rw [defectPoly_eval_circle P n hn z];
  exact mul_ne_zero ( pow_ne_zero _ ( by simp ) ) ( sub_ne_zero_of_ne <| Ne.symm <| by norm_cast; nlinarith [ hP_strict z, norm_nonneg ( P.eval ( z : ℂ ) ) ] )

/-
The defect polynomial is nonzero (since it's nonzero on the circle).
-/
lemma defectPoly_ne_zero (P : ℂ[X]) (n : ℕ) (hn : P.natDegree ≤ n)
    (hP_strict : ∀ z : Circle, ‖P.eval (z : ℂ)‖ < 1) :
    defectPoly n P ≠ 0 := by
  by_contra h;
  exact absurd ( congr_arg ( Polynomial.eval 1 ) h ) ( by norm_num; have := @defectPoly_no_roots_circle P n hn hP_strict 1; aesop )

/-
The defect polynomial is self-reciprocal: conjReverse'(2n, R) = R.
-/
lemma defectPoly_self_reciprocal (P : ℂ[X]) (n : ℕ) (hn : P.natDegree ≤ n) :
    conjReverse' (2 * n) (defectPoly n P) = defectPoly n P := by
  have h_deg : Polynomial.natDegree (defectPoly n P) ≤ 2 * n := by
    refine' le_trans ( Polynomial.natDegree_sub_le _ _ ) _;
    refine' max_le _ _;
    · simp +arith +decide;
    · refine' le_trans ( Polynomial.natDegree_mul_le .. ) _;
      refine' le_trans ( add_le_add hn ( Polynomial.natDegree_map_le .. ) ) _;
      rw [ two_mul ];
      simp +zetaDelta at *;
      rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ];
      simp +decide [ Polynomial.coeff_reflect ];
      intro m hm; rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; simp +decide [ revAt, hm.le ] ;
      grind;
  -- To show that the polynomials agree on the circle, we use the evaluation formula for conjReverse' and the definition of the defect polynomial.
  have h_circle_agree : ∀ z : Circle, (conjReverse' (2 * n) (defectPoly n P)).eval (z : ℂ) = (defectPoly n P).eval (z : ℂ) := by
    intro z
    have h_eval : (conjReverse' (2 * n) (defectPoly n P)).eval (z : ℂ) = (z : ℂ) ^ (2 * n) * starRingEnd ℂ ((defectPoly n P).eval (starRingEnd ℂ (z : ℂ)⁻¹)) := by
      unfold conjReverse';
      simp +decide [ Polynomial.eval_map, Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.reflect ];
      simp +decide [ Polynomial.eval_eq_sum, Polynomial.sum_def, revAt ];
      rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; rw [ if_pos ( by linarith [ Polynomial.le_natDegree_of_mem_supp _ hx ] ) ] ; simp +decide [ ← mul_assoc, ← pow_add, Nat.sub_add_cancel ( show x ≤ 2 * n from by linarith [ Polynomial.le_natDegree_of_mem_supp _ hx ] ) ] ;
      field_simp;
      rw [ mul_assoc, ← pow_add, Nat.sub_add_cancel ( show x ≤ 2 * n from by linarith [ Polynomial.le_natDegree_of_mem_supp _ hx ] ) ] ; ring!;
    -- Since $z$ is on the unit circle, we have $z \cdot \overline{z} = 1$, thus $\overline{z}^{-1} = z$.
    have h_unit_circle : starRingEnd ℂ (z : ℂ)⁻¹ = z := by
      simp +decide [ Complex.inv_def, Complex.normSq_eq_norm_sq, z.2 ];
    have := defectPoly_eval_circle P n hn z; simp_all +decide [ pow_mul' ] ;
    rw [ show ( starRingEnd ℂ z : ℂ ) = ( z : ℂ ) ⁻¹ from by simp [ Complex.ext_iff ] ] ; ring;
    simp +decide [ pow_mul, show ( z : ℂ ) ≠ 0 from by simp ];
    simp +decide [ sq, mul_assoc, show ( z : ℂ ) ≠ 0 from by simp ];
  -- Since the polynomials agree on the unit circle, which has infinitely many points, and both have degree ≤ 2n, they must be equal.
  have h_poly_eq : ∀ p q : Polynomial ℂ, p.natDegree ≤ 2 * n → q.natDegree ≤ 2 * n → (∀ z : Circle, p.eval (z : ℂ) = q.eval (z : ℂ)) → p = q := by
    intros p q hp hq h_eq
    have h_inf_roots : Set.Infinite {z : ℂ | p.eval z = q.eval z} := by
      have h_inf_roots : Set.Infinite (Set.image (fun θ : ℝ => Complex.exp (θ * Complex.I)) (Set.Ico 0 (2 * Real.pi))) := by
        refine' Set.Infinite.image _ ( Set.Ico_infinite ( by positivity ) );
        intros θ₁ hθ₁ θ₂ hθ₂ h_eq; rw [ Complex.exp_eq_exp_iff_exists_int ] at h_eq; obtain ⟨ k, hk ⟩ := h_eq; replace hk := congr_arg Complex.im hk; simp_all +decide [ Complex.exp_im ];
        rcases k with ⟨ _ | k ⟩ <;> norm_num at * <;> nlinarith [ Real.pi_pos ];
      refine h_inf_roots.mono ?_;
      rintro _ ⟨ θ, hθ, rfl ⟩ ; specialize h_eq ⟨ Complex.exp ( θ * Complex.I ), ?_ ⟩ <;> simp_all +decide [ Complex.norm_exp ] ;
      simp +decide [ Submonoid.unitSphere, Complex.norm_exp ];
    exact Classical.not_not.1 fun h => h_inf_roots <| Set.Finite.subset ( p - q |> Polynomial.roots |> Multiset.toFinset |> Finset.finite_toSet ) fun x hx => by simp_all +decide [ sub_eq_iff_eq_add ] ;
  refine' h_poly_eq _ _ _ h_deg h_circle_agree;
  refine' le_trans ( Polynomial.natDegree_map_le .. ) _;
  rw [ Polynomial.natDegree_le_iff_degree_le, Polynomial.degree_le_iff_coeff_zero ];
  simp +decide [ Polynomial.revAt ];
  intro m hm; split_ifs <;> norm_cast at hm ; linarith [ Polynomial.coeff_eq_zero_of_natDegree_lt ( by linarith : Polynomial.natDegree ( defectPoly n P ) < m ) ] ;
  exact Polynomial.coeff_eq_zero_of_natDegree_lt <| by linarith;

/-
If R is self-reciprocal and α is a root, then (starRingEnd ℂ α)⁻¹ is also a root.
-/
lemma self_reciprocal_root_inv (R : ℂ[X]) (N : ℕ) (hR : R ≠ 0) (hN : R.natDegree ≤ N)
    (hself : conjReverse' N R = R) (α : ℂ) (hα : R.IsRoot α) :
    R.IsRoot ((starRingEnd ℂ α)⁻¹) := by
  have h_eval : R.eval ((starRingEnd ℂ α)⁻¹) = ((Polynomial.reflect N R).map (starRingEnd ℂ)).eval ((starRingEnd ℂ α)⁻¹) := by
    exact?;
  by_cases h : α = 0 <;> simp_all +decide [ Polynomial.eval_map, Polynomial.eval₂_at_apply ];
  · rw [ eq_comm ] at h_eval ; aesop;
  · simp_all +decide [ Polynomial.eval₂_eq_sum, Polynomial.sum_def, Polynomial.reflect ];
    have h_eval : ∑ x ∈ R.toFinsupp.support, R.toFinsupp x * α ^ x = 0 := by
      rw [ ← hα, Polynomial.eval_eq_sum, Polynomial.sum_def ];
      rfl;
    convert congr_arg ( fun x : ℂ => starRingEnd ℂ x * ( starRingEnd ℂ α ) ⁻¹ ^ N ) h_eval using 1 <;> simp +decide [ h, mul_assoc, mul_comm, mul_left_comm, pow_add, pow_mul, Finset.mul_sum _ _ _, Finset.sum_mul ];
    refine' Finset.sum_congr rfl fun x hx => _ ; simp +decide [ revAt, h, pow_add, pow_mul, mul_assoc, mul_comm, mul_left_comm ];
    split_ifs <;> simp_all +decide [ ← mul_assoc, ← pow_add, Nat.sub_add_cancel ];
    · rw [ show ( starRingEnd ℂ α ) ^ N = ( starRingEnd ℂ α ) ^ ( N - x ) * ( starRingEnd ℂ α ) ^ x by rw [ ← pow_add, Nat.sub_add_cancel ‹x ≤ N› ] ] ; ring;
      simp +decide [ mul_assoc, mul_comm, mul_left_comm, h ];
    · exact False.elim <| hx <| Polynomial.toFinsupp_apply _ _ |> fun h => h.symm ▸ by rw [ Polynomial.coeff_eq_zero_of_natDegree_lt ] ; linarith;

/-
Roots of a polynomial with no roots on the unit circle satisfy ‖α‖ ≠ 1.
-/
lemma root_norm_ne_one_of_no_circle_roots (R : ℂ[X]) (α : ℂ) (hα : α ∈ R.roots)
    (hno_circle : ∀ z : Circle, R.eval (z : ℂ) ≠ 0) :
    ‖α‖ ≠ 1 := by
  contrapose! hno_circle;
  -- Since α is a root of R and ‖α‖ = 1, we can consider α as an element of the Circle.
  use ⟨α, by
    -- Since ‖α‖ = 1, we have α ∈ Submonoid.unitSphere ℂ by definition.
    simp [Submonoid.unitSphere, hno_circle]⟩
  generalize_proofs at *;
  aesop

/-
If ‖α‖ ≠ 1 and α ≠ 0 then α ≠ (starRingEnd ℂ α)⁻¹.
-/
lemma ne_conj_inv_of_norm_ne_one (α : ℂ) (h : ‖α‖ ≠ 1) (h0 : α ≠ 0) :
    α ≠ (starRingEnd ℂ α)⁻¹ := by
  field_simp;
  rw [ Ne.eq_def, eq_div_iff ] <;> simp_all +decide [ Complex.ext_iff ];
  exact fun h' => False.elim <| h <| by simpa [ Complex.norm_def, sq ] using h';

/-
For p with no zero roots, roots of (reflect N p) = roots of p mapped by (·⁻¹),
    assuming natDegree conditions.
-/
lemma roots_reflect_eq_map_inv (p : ℂ[X]) (N : ℕ) (hp : p ≠ 0) (hN : p.natDegree ≤ N)
    (hp0 : p.coeff 0 ≠ 0)
    (hrefl_deg : (Polynomial.reflect N p).natDegree = p.natDegree) :
    (Polynomial.reflect N p).roots = p.roots.map (·⁻¹) := by
  -- Write p as a product of its roots and leading coefficient.
  have hp_factor : p = Polynomial.C (p.leadingCoeff) * Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C α) p.roots) := by
    convert Polynomial.Splits.eq_prod_roots _;
    exact?;
  -- By definition of reflection, we have that reflect N p = Polynomial.C (p.leadingCoeff) * Polynomial.C (∏ α ∈ p.roots.toFinset, (-α) ^ (Multiset.count α p.roots)) * Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C (α⁻¹)) p.roots).
  have h_refl_def : reflect N p = Polynomial.C (p.leadingCoeff) * Polynomial.C (∏ α ∈ p.roots.toFinset, (-α) ^ (Multiset.count α p.roots)) * Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C (α⁻¹)) p.roots) := by
    have h_refl_poly : ∀ z : ℂ, z ≠ 0 → (reflect N p).eval z = z ^ N * p.eval (z⁻¹) := by
      intro z hz;
      simp +decide [ Polynomial.eval_eq_sum, Polynomial.sum_def, Polynomial.reflect ];
      rw [ Finset.mul_sum _ _ _ ] ; refine' Finset.sum_congr rfl fun x hx => _ ; simp +decide [ revAt, hz, Polynomial.toFinsupp_apply ] ; ring;
      split_ifs <;> simp +decide [ hz, mul_assoc, ← pow_add, Nat.sub_add_cancel ( show x ≤ N from le_trans ( Polynomial.le_natDegree_of_mem_supp _ hx ) hN ) ];
      · exact Or.inl ( eq_div_of_mul_eq ( pow_ne_zero _ hz ) ( by rw [ ← pow_add, Nat.sub_add_cancel ‹x ≤ N› ] ) );
      · exact False.elim <| ‹¬x ≤ N› <| le_trans ( Polynomial.le_natDegree_of_mem_supp _ hx ) hN;
    have h_refl_poly_eq : ∀ z : ℂ, z ≠ 0 → (reflect N p).eval z = Polynomial.eval z (Polynomial.C (p.leadingCoeff) * Polynomial.C (∏ α ∈ p.roots.toFinset, (-α) ^ (Multiset.count α p.roots)) * Multiset.prod (Multiset.map (fun α => Polynomial.X - Polynomial.C (α⁻¹)) p.roots)) := by
      intro z hz
      rw [h_refl_poly z hz];
      conv_lhs => rw [ hp_factor ];
      norm_num [ Polynomial.eval_multiset_prod, Finset.prod_multiset_map_count ];
      simp +decide [ Polynomial.eval_prod, mul_assoc, mul_comm, mul_left_comm, Finset.prod_mul_distrib ];
      rw [ show N = p.natDegree from _ ];
      · -- By simplifying, we can see that the two expressions are equal.
        have h_simp : ∏ x ∈ p.roots.toFinset, (z⁻¹ - x) ^ rootMultiplicity x p = ∏ x ∈ p.roots.toFinset, ((z - x⁻¹) ^ rootMultiplicity x p) * ((-x) ^ rootMultiplicity x p) * z⁻¹ ^ rootMultiplicity x p := by
          refine Finset.prod_congr rfl fun x hx => ?_;
          rw [ ← mul_pow, ← mul_pow ] ; ring;
          by_cases hx' : x = 0 <;> simp +decide [ hx', hz ];
          · simp +decide [ hx', Polynomial.coeff_zero_eq_eval_zero ] at hx;
            exact False.elim <| hp0 <| by simpa [ Polynomial.coeff_zero_eq_eval_zero ] using hx.2;
          · ring;
        rw [ h_simp, Finset.prod_mul_distrib, Finset.prod_mul_distrib ];
        simp +decide [ mul_assoc, mul_comm, mul_left_comm, Finset.prod_pow_eq_pow_sum, hz ];
        rw [ show ∑ i ∈ p.roots.toFinset, rootMultiplicity i p = p.natDegree from ?_ ];
        · exact Or.inl ( by rw [ ← mul_assoc, mul_inv_cancel₀ ( pow_ne_zero _ hz ), one_mul ] );
        · replace hp_factor := congr_arg Polynomial.natDegree hp_factor; rw [ Polynomial.natDegree_C_mul ] at hp_factor <;> norm_num at *;
          · rw [ hp_factor, ← Multiset.toFinset_sum_count_eq ];
            exact Finset.sum_congr rfl fun x hx => by aesop;
          · exact hp;
      · refine' le_antisymm _ hN;
        contrapose! hrefl_deg;
        refine' ne_of_gt ( lt_of_lt_of_le _ ( Polynomial.le_natDegree_of_ne_zero _ ) );
        exact hrefl_deg;
        simp +decide [ Polynomial.coeff_reflect, hp0 ];
    refine' Polynomial.eq_of_infinite_eval_eq _ _ _;
    exact Set.infinite_of_finite_compl ( Set.Finite.subset ( Set.finite_singleton 0 ) fun x hx => Classical.not_not.1 fun hx' => hx <| h_refl_poly_eq x hx' );
  rw [ h_refl_def, Polynomial.roots_mul, Polynomial.roots_mul ];
  · rw [ Polynomial.roots_C, Polynomial.roots_C, Polynomial.roots_multiset_prod ];
    · erw [ Multiset.bind_map ];
      norm_num;
    · norm_num [ Polynomial.X_sub_C_ne_zero ];
  · simp +decide [ hp, Polynomial.C_eq_zero ];
    exact Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ <| neg_ne_zero.mpr <| Polynomial.C_ne_zero.mpr <| by rintro rfl; exact hp0 <| by simpa using Polynomial.coeff_zero_eq_eval_zero p ▸ Polynomial.isRoot_of_mem_roots ( Multiset.mem_toFinset.mp hx ) ;
  · simp +decide [ hp, Polynomial.X_sub_C_ne_zero ];
    exact Finset.prod_ne_zero_iff.mpr fun x hx => pow_ne_zero _ <| neg_ne_zero.mpr <| Polynomial.C_ne_zero.mpr <| by rintro rfl; exact hp0 <| by simpa using Polynomial.coeff_zero_eq_eval_zero p ▸ Polynomial.isRoot_of_mem_roots ( Multiset.mem_toFinset.mp hx ) ;

/-
Roots of (p.map f) when card roots = natDegree.
-/
lemma roots_conjReverse_eq_map_conjInv (p : ℂ[X]) (N : ℕ) (hp : p ≠ 0) (hN : p.natDegree ≤ N)
    (hp0 : p.coeff 0 ≠ 0)
    (hrefl_deg : (Polynomial.reflect N p).natDegree = p.natDegree) :
    (conjReverse' N p).roots = p.roots.map (fun α => ((starRingEnd ℂ) α)⁻¹) := by
  unfold conjReverse';
  rw [ Polynomial.Splits.roots_map, roots_reflect_eq_map_inv ];
  all_goals norm_num [ hp, hN, hp0, hrefl_deg ];
  exact?

end Submission.Helpers