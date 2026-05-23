import Mathlib
import Submission.Analysis

open NumberField Polynomial Complex Real Finset

namespace Submission.Helpers

/-
Key analytic lemma: if z is real with |z| ≤ 2, roots of t²-zt+1=0 have norm 1
-/
lemma norm_root_eq_one {z : ℂ} (hz_im : z.im = 0) (hz_norm : ‖z‖ ≤ 2) {w : ℂ}
    (hw : w ^ 2 - z * w + 1 = 0) (_hw0 : w ≠ 0) : ‖w‖ = 1 := by
  simp_all +decide [ Complex.ext_iff, sq ];
  simp_all +decide [ Complex.normSq, Complex.norm_def ];
  rw [ Real.sqrt_le_left ] at hz_norm <;> cases eq_or_ne w.im 0 <;> simp_all +decide;
  · nlinarith [ sq_nonneg ( w.re - z.re / 2 ) ];
  · grind

/-- For orderOf γ ∈ {1,2} with β = γ + γ⁻¹, house β ≥ 2. -/
private lemma house_ge_two_of_low_order {K : Type*} [Field K] [NumberField K]
    {β : K} {L : Type*} [Field L] [NumberField L] [Algebra K L]
    {γ : L} (hγ_ne : γ ≠ 0) (hβ_eq : algebraMap K L β = γ + γ⁻¹)
    (hord_pos : 0 < orderOf γ) (hord : orderOf γ ≤ 2) (hβ_ne : β ≠ 0) : house β ≥ 2 := by
  interval_cases _ : orderOf γ;
  · have hβ_val : β = 2 := by
      apply_fun ( algebraMap K L ) at *; simp_all +decide [ pow_succ' ] ;
      · erw [ map_ofNat ];
        norm_num;
      · exact RingHom.injective _;
    simp +decide [ hβ_val, house ];
    simp +decide [ Norm.norm ];
    refine' mod_cast le_trans _ ( Finset.le_sup <| Finset.mem_univ <| ( Classical.arbitrary _ ) );
    erw [ map_ofNat ] ; norm_num;
  · have h_order_two : γ ^ 2 = 1 ∧ γ ≠ 1 := by
      exact ⟨ by rw [ ← ‹orderOf γ = 2›, pow_orderOf_eq_one ], by rintro rfl; simp_all +decide ⟩;
    have h_order_two : γ = -1 := by
      exact Or.resolve_left ( sq_eq_one_iff.mp h_order_two.1 ) h_order_two.2;
    have h_beta_neg_two : β = -2 := by
      have h_beta_neg_two : algebraMap K L β = algebraMap K L (-2) := by
        simp_all +decide;
        erw [ map_ofNat ] ; ring;
      exact ( algebraMap K L ).injective h_beta_neg_two;
    simp +decide [ house, h_beta_neg_two ];
    erw [ Pi.norm_def ] ; norm_num;
    erw [ show ( fun b : K →+* ℂ => ‖b 2‖₊ ) = fun _ => 2 by ext; erw [ map_ofNat ] ; norm_num ];
    exact_mod_cast Finset.le_sup ( f := fun _ => 2 ) ( Finset.mem_univ ( Classical.arbitrary _ ) )

private lemma natDegree_quad (K : Type*) [Field K] (β : K) :
    (X ^ 2 - C β * X + 1 : K[X]).natDegree = 2 := by
  rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> by_cases h : β = 0 <;> simp +decide [ h ]

private lemma monic_quad (K : Type*) [Field K] (β : K) :
    (X ^ 2 - C β * X + 1 : K[X]).Monic := by
  rw [ Polynomial.Monic, Polynomial.leadingCoeff ];
  rw [ Polynomial.natDegree_add_eq_left_of_natDegree_lt ] <;> rw [ Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> by_cases h : β = 0 <;> simp +decide [ Polynomial.coeff_eq_zero_of_natDegree_lt, h ]

private lemma isIntegral_of_quadratic_root {K L : Type*} [Field K] [NumberField K]
    [Field L] [Algebra K L] [NumberField L]
    {β : K} (hβ_int : IsIntegral ℤ β) {γ : L}
    (hγ_eq : γ ^ 2 - algebraMap K L β * γ + 1 = 0) : IsIntegral ℤ γ := by
  set b : L := algebraMap K L β
  have hb_int : IsIntegral ℤ b := IsIntegral.algebraMap hβ_int
  have hS_int : Algebra.IsIntegral ℤ (Algebra.adjoin ℤ {b}) := by
    have hS_int : ∀ x ∈ Algebra.adjoin ℤ {b}, IsIntegral ℤ x := by
      intro x hx; induction hx using Algebra.adjoin_induction ; aesop;
      · exact isIntegral_algebraMap;
      · exact IsIntegral.add ‹_› ‹_›;
      · exact IsIntegral.mul ‹_› ‹_›;
    exact (Subalgebra.isIntegral_iff _).mpr hS_int
  have hγ_poly : γ ^ 2 - (⟨b, Algebra.subset_adjoin (by simp)⟩ : Algebra.adjoin ℤ {b}) * γ + 1 = 0 := by
    exact hγ_eq;
  have hγ_int : IsIntegral (Algebra.adjoin ℤ {b}) γ := by
    refine' ⟨ Polynomial.X ^ 2 - Polynomial.C ( ⟨ b, Algebra.subset_adjoin ( by simp ) ⟩ : Algebra.adjoin ℤ { b } ) * Polynomial.X + 1, _, _ ⟩;
    · erw [ Polynomial.Monic, Polynomial.leadingCoeff, Polynomial.natDegree_add_C, Polynomial.natDegree_sub_eq_left_of_natDegree_lt ] <;> norm_num;
      · norm_num [ Polynomial.coeff_one ];
      · by_cases h : ( ⟨ b, Algebra.subset_adjoin ( by simp ) ⟩ : Algebra.adjoin ℤ { b } ) = 0 <;> simp +decide [ h ];
    · simpa using hγ_poly;
  apply_rules [ isIntegral_trans ];
  infer_instance

private lemma quad_root_eq {K L : Type*} [Field K] [Field L] [Algebra K L]
    (β : K) (γ : L)
    (hγ_eq : γ ^ 2 - algebraMap K L β * γ + 1 = 0) (hγ_ne : γ ≠ 0) :
    algebraMap K L β = γ + γ⁻¹ := by
  grind

private noncomputable instance numberField_splittingField
    {K : Type*} [Field K] [NumberField K] [Algebra ℚ K] (p : K[X]) :
    NumberField (SplittingField p) where
  to_charZero := inferInstance
  to_finiteDimensional := FiniteDimensional.trans ℚ K (SplittingField p)

private lemma quad_root_in_splittingField {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (β : K) :
    let p := X ^ 2 - C β * X + 1
    let L := SplittingField p
    ∃ γ : L,
      γ ^ 2 - algebraMap K L β * γ + 1 = 0 ∧
      γ ≠ 0 := by
  obtain ⟨γ, hγ⟩ : ∃ γ : (Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X + 1 : Polynomial K).SplittingField, (Polynomial.eval γ (Polynomial.map (algebraMap K (Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X + 1 : Polynomial K).SplittingField) (Polynomial.X ^ 2 - Polynomial.C β * Polynomial.X + 1))) = 0 := by
    convert Polynomial.Splits.exists_eval_eq_zero _ _;
    · exact Polynomial.SplittingField.splits _;
    · rw [ Polynomial.degree_map, Polynomial.degree_add_eq_left_of_degree_lt ] <;> rw [ Polynomial.degree_sub_eq_left_of_degree_lt ] <;> by_cases h : β = 0 <;> simp +decide [ h ];
  aesop

private lemma norm_of_quad_root_le_one {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    {β : K}
    (hβ_real : β ∈ NumberField.maximalRealSubfield K)
    (hhouse_lt : house β < 2)
    {L : Type*} [Field L] [NumberField L] [Algebra K L]
    {γ : L}
    (hγ_eq : γ ^ 2 - algebraMap K L β * γ + 1 = 0) :
    ∀ τ : L →+* ℂ, ‖τ γ‖ ≤ 1 := by
  intro τ;
  set σ : K →+* ℂ := τ.comp (algebraMap K L);
  have hσβ_im : (σ β).im = 0 := conj_eq_iff_im.mp (hβ_real σ)
  have hσβ_norm : ‖σ β‖ ≤ house β := by
    convert NumberField.norm_embedding_le_house β;
    constructor <;> intro h;
    · exact fun σ => norm_embedding_le_house β σ;
    · exact h σ;
  have := norm_root_eq_one hσβ_im ( hσβ_norm.trans hhouse_lt.le ) ( show τ γ ^ 2 - σ β * τ γ + 1 = 0 from ?_ ) ?_;
  · exact this.le;
  · simpa using congr_arg τ hγ_eq;
  · intro h; replace hγ_eq := congr_arg τ hγ_eq; simp_all +decide ;

/-
============================================================
Core decomposition for house_eq_cos_of_high_order
============================================================

Extension of embeddings: for any σ : K →+* ℂ with K, L number fields,
    there exists τ : L →+* ℂ extending σ
-/
private lemma exists_extension {K L : Type*} [Field K] [Field L] [Algebra K L]
    [NumberField K] [NumberField L]
    (σ : K →+* ℂ) : ∃ τ : L →+* ℂ, ∀ x : K, τ (algebraMap K L x) = σ x := by
  -- Use the given embedding `σ` to give ℂ a K-algebra structure via `σ`.
  let _ : Algebra K ℂ := σ.toAlgebra;
  have h_alg_closure : Nonempty (L →ₐ[K] ℂ) := by
    exact ⟨ IsAlgClosed.lift ⟩;
  exact ⟨ h_alg_closure.some.toRingHom, fun x => h_alg_closure.some.commutes x ⟩

/-
Existence of an embedding mapping γ to exp(2πi/d)
-/
set_option maxHeartbeats 1600000 in
private lemma exists_embedding_to_root {L : Type*} [Field L] [NumberField L]
    {γ : L} {d : ℕ} (hd : 3 ≤ d) (hord : orderOf γ = d) :
    ∃ τ : L →+* ℂ, τ γ = exp (2 * ↑π * I / ↑d) := by
  have hprim : IsPrimitiveRoot γ d := IsPrimitiveRoot.iff_orderOf.mpr hord
  have hd_pos : 0 < d := by omega
  have hmin : minpoly ℚ γ = cyclotomic d ℚ := by
    symm; exact minpoly.eq_of_irreducible_of_monic
      (cyclotomic.irreducible_rat hd_pos)
      (by rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]; exact hprim.isRoot_cyclotomic hd_pos)
      (cyclotomic.monic d ℚ)
  have hγ_int : IsIntegral ℚ γ := IsIntegral.of_finite ℚ γ
  have hroot : exp (2 * ↑π * I / ↑d) ∈ (minpoly ℚ γ).aroots ℂ := by
    rw [mem_aroots]
    refine ⟨minpoly.ne_zero hγ_int, ?_⟩
    rw [hmin, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact (Complex.isPrimitiveRoot_exp d (by omega)).isRoot_cyclotomic hd_pos
  set φ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hγ_int).symm ⟨_, hroot⟩
  have hφ_gen : φ (IntermediateField.AdjoinSimple.gen ℚ γ) = exp (2 * ↑π * I / ↑d) := by
    have h := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hγ_int).apply_symm_apply ⟨_, hroot⟩
    exact congr_arg Subtype.val h
  letI : Algebra (↥(IntermediateField.adjoin ℚ ({γ} : Set L))) ℂ := φ.toRingHom.toAlgebra
  haveI : FiniteDimensional (↥(IntermediateField.adjoin ℚ ({γ} : Set L))) L :=
    FiniteDimensional.right ℚ _ L
  let τ := (IsAlgClosed.lift (R := ↥(IntermediateField.adjoin ℚ ({γ} : Set L))) (S := L) (M := ℂ)).toRingHom
  refine ⟨τ, ?_⟩
  have hγeq : γ = (algebraMap (↥(IntermediateField.adjoin ℚ ({γ} : Set L))) L)
    (IntermediateField.AdjoinSimple.gen ℚ γ) := by simp
  rw [hγeq]
  simp only [τ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact hφ_gen

/-
For any embedding τ : L →+* ℂ and γ with order d, |τ(γ) + τ(γ)⁻¹| = 2|cos(2πk/d)|
    for some k coprime to d
-/
private lemma embedding_value_form {L : Type*} [Field L] [NumberField L]
    {γ : L} {d : ℕ} (hd : 3 ≤ d) (hord : orderOf γ = d) (τ : L →+* ℂ) :
    ∃ k : ℤ, Int.gcd k d = 1 ∧
      ‖τ γ + (τ γ)⁻¹‖ = 2 * |Real.cos (2 * π * k / d)| := by
  -- By orderOf_injective τ.toMonoidHom τ.injective γ, orderOf (τ γ) = d.
  have hord_τ : orderOf (τ γ) = d := by
    rw [ ← hord, orderOf_eq_orderOf_iff ];
    exact fun n => ⟨ fun h => by simpa using τ.injective ( by aesop ), fun h => by simpa using congr_arg τ h ⟩;
  -- Since τ(γ)^d = 1, by root_of_unity_eq_exp (or Complex.isPrimitiveRoot_exp and eq_pow_of_pow_eq_one), τ(γ) = exp(2πij/d) for some j < d.
  obtain ⟨j, hj⟩ : ∃ j : ℕ, j < d ∧ τ γ = Complex.exp (2 * Real.pi * Complex.I * j / d) := by
    -- Since τ(γ)^d = 1, by root_of_unity_eq_exp (or Complex.isPrimitiveRoot_exp and eq_pow_of_pow_eq_one), τ(γ) = exp(2πij/d) for some j.
    have h_root_of_unity : ∃ j : ℤ, τ γ = Complex.exp (2 * Real.pi * Complex.I * j / d) := by
      -- Since τ(γ) is a root of unity, we have τ(γ)^d = 1.
      have h_root_of_unity : τ γ ^ d = 1 := by
        rw [ ← hord_τ, pow_orderOf_eq_one ];
      -- Since τ(γ) is a root of unity, we can write it as e^(iθ) for some θ.
      obtain ⟨θ, hθ⟩ : ∃ θ : ℝ, τ γ = Complex.exp (θ * Complex.I) := by
        have h_abs : ‖τ γ‖ = 1 := by
          simpa [ show d ≠ 0 by positivity, pow_eq_one_iff_of_nonneg ] using congr_arg Norm.norm h_root_of_unity;
        rw [ Complex.norm_eq_one_iff ] at h_abs ; tauto;
      simp_all +decide [ ← Complex.exp_nat_mul ];
      rw [ Complex.exp_eq_one_iff ] at h_root_of_unity; obtain ⟨ j, hj ⟩ := h_root_of_unity; exact ⟨ j, congr_arg Complex.exp <| by rw [ eq_div_iff ( Nat.cast_ne_zero.mpr <| by linarith ) ] ; linear_combination' hj ⟩ ;
    obtain ⟨ j, hj ⟩ := h_root_of_unity;
    refine' ⟨ Int.toNat ( j % d ), _, _ ⟩;
    · linarith [ Int.emod_nonneg j ( by positivity : ( d : ℤ ) ≠ 0 ), Int.emod_lt_of_pos j ( by positivity : ( d : ℤ ) > 0 ), Int.toNat_of_nonneg ( Int.emod_nonneg j ( by positivity : ( d : ℤ ) ≠ 0 ) ) ];
    · obtain ⟨ k, hk ⟩ := Int.eq_ofNat_of_zero_le ( Int.emod_nonneg j ( by positivity : ( d : ℤ ) ≠ 0 ) ) ; simp_all +decide [ Int.emod_eq_of_lt ];
      rw [ ← Int.emod_add_mul_ediv j d, hk ] ; push_cast ; ring;
      exact Complex.exp_eq_exp_iff_exists_int.mpr ⟨ j / d, by ring_nf; norm_num [ show d ≠ 0 by positivity ] ⟩;
  refine' ⟨ j, _, _ ⟩;
  · -- Since τ(γ) = exp(2πij/d), we have that τ(γ)^k = 1 if and only if exp(2πijk/d) = 1, which implies that d divides jk.
    have h_div : ∀ k : ℕ, τ γ ^ k = 1 ↔ d ∣ j * k := by
      intro k
      simp [hj.right];
      rw [ ← Complex.exp_nat_mul, mul_comm, Complex.exp_eq_one_iff ];
      field_simp;
      exact ⟨ fun ⟨ n, hn ⟩ => Int.natCast_dvd_natCast.mp ⟨ n, by rw [ ← @Int.cast_inj ℂ ] ; push_cast; rw [ div_eq_iff ( Nat.cast_ne_zero.mpr <| by linarith ) ] at hn; linear_combination' hn ⟩, fun ⟨ n, hn ⟩ => ⟨ n, by rw [ div_eq_iff ( Nat.cast_ne_zero.mpr <| by linarith ) ] ; norm_cast; linarith ⟩ ⟩;
    -- Since τ(γ) has order d, we know that d is the smallest positive integer such that τ(γ)^d = 1.
    have h_order : ∀ k : ℕ, 0 < k → k < d → ¬(d ∣ j * k) := by
      intro k hk hk' hk''; have := orderOf_dvd_iff_pow_eq_one.mpr ( show τ γ ^ k = 1 from h_div k |>.2 hk'' ) ; simp_all +decide ;
      linarith [ Nat.le_of_dvd hk this ];
    refine' Nat.coprime_of_dvd' _;
    intro k hk hk₁ hk₂; specialize h_order ( d / k ) ( Nat.div_pos ( Nat.le_of_dvd ( by linarith ) hk₂ ) hk.pos ) ( Nat.div_lt_self ( by linarith ) hk.one_lt ) ; simp_all +decide [ Nat.dvd_div_iff_mul_dvd ] ;
    exact False.elim ( h_order ( dvd_trans ( by rw [ Nat.mul_div_cancel' hk₂ ] ) ( mul_dvd_mul hk₁ ( dvd_refl _ ) ) ) );
  · simp_all +decide [ Complex.norm_def, Complex.normSq, Complex.exp_re, Complex.exp_im ];
    norm_num [ ← sq ];
    rw [ Real.sqrt_sq_eq_abs, ← two_mul, abs_mul, abs_two ]

/-
Generalized: exists embedding mapping γ to exp(2πi·k/d) for any coprime k
-/
private lemma exists_embedding_to_coprime_root {L : Type*} [Field L] [NumberField L]
    {γ : L} {d : ℕ} (hd : 3 ≤ d) (hord : orderOf γ = d)
    {k : ℕ} (hk : k.Coprime d) (hk_pos : 0 < k) (hk_lt : k < d) :
    ∃ τ : L →+* ℂ, τ γ = exp (2 * ↑π * I * ↑k / ↑d) := by
  have hprim : IsPrimitiveRoot γ d := IsPrimitiveRoot.iff_orderOf.mpr hord
  have hd_pos : 0 < d := by omega
  have hmin : minpoly ℚ γ = cyclotomic d ℚ := by
    symm; exact minpoly.eq_of_irreducible_of_monic
      (cyclotomic.irreducible_rat hd_pos)
      (by rw [aeval_def, eval₂_eq_eval_map, map_cyclotomic]; exact hprim.isRoot_cyclotomic hd_pos)
      (cyclotomic.monic d ℚ)
  have hγ_int : IsIntegral ℚ γ := IsIntegral.of_finite ℚ γ
  have hexp_prim : IsPrimitiveRoot (exp (2 * ↑π * I * ↑k / ↑d)) d := by
    rw [Complex.isPrimitiveRoot_iff _ _ (by omega)]
    exact ⟨k, hk_lt, hk, by ring⟩
  have hroot : exp (2 * ↑π * I * ↑k / ↑d) ∈ (minpoly ℚ γ).aroots ℂ := by
    rw [mem_aroots]
    refine ⟨minpoly.ne_zero hγ_int, ?_⟩
    rw [hmin, aeval_def, eval₂_eq_eval_map, map_cyclotomic]
    exact hexp_prim.isRoot_cyclotomic hd_pos
  set φ := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hγ_int).symm ⟨_, hroot⟩
  have hφ_gen : φ (IntermediateField.AdjoinSimple.gen ℚ γ) = exp (2 * ↑π * I * ↑k / ↑d) := by
    have h := (IntermediateField.algHomAdjoinIntegralEquiv ℚ hγ_int).apply_symm_apply ⟨_, hroot⟩
    exact congr_arg Subtype.val h
  letI : Algebra (↥(IntermediateField.adjoin ℚ ({γ} : Set L))) ℂ := φ.toRingHom.toAlgebra
  haveI : FiniteDimensional (↥(IntermediateField.adjoin ℚ ({γ} : Set L))) L :=
    FiniteDimensional.right ℚ _ L
  let τ := (IsAlgClosed.lift (R := ↥(IntermediateField.adjoin ℚ ({γ} : Set L))) (S := L) (M := ℂ)).toRingHom
  refine ⟨τ, ?_⟩
  have hγeq : γ = (algebraMap (↥(IntermediateField.adjoin ℚ ({γ} : Set L))) L)
    (IntermediateField.AdjoinSimple.gen ℚ γ) := by simp
  rw [hγeq]
  simp only [τ, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  exact hφ_gen

/-
Upper bound: for each σ : K →+* ℂ, ‖σ β‖ ≤ bound depending on parity of d
-/
private lemma house_upper_bound {K : Type*} [Field K] [NumberField K]
    {β : K} {L : Type*} [Field L] [NumberField L] [Algebra K L]
    {γ : L} (hβ_eq : algebraMap K L β = γ + γ⁻¹)
    {d : ℕ} (hd : 3 ≤ d) (hord : orderOf γ = d) (σ : K →+* ℂ)
    (bound : ℝ) (hbound : ∀ k : ℤ, Int.gcd k d = 1 →
      |Real.cos (2 * π * k / d)| ≤ bound / 2) :
    ‖σ β‖ ≤ bound := by
  -- Use exists_extension to get τ : L →+* ℂ with τ ∘ algebraMap K L = σ.
  obtain ⟨τ, hτ⟩ : ∃ τ : L →+* ℂ, τ ∘ algebraMap K L = σ := by
    convert exists_extension σ;
    all_goals first | infer_instance | simp +decide [ funext_iff ] ;
  -- By embedding_value_form (hd) (hord) τ, get k : ℤ with Int.gcd k d = 1 and ‖τ γ + (τ γ)⁻¹‖ = 2 * |cos(2πk/d)|.
  obtain ⟨k, hk_gcd, hk⟩ : ∃ k : ℤ, Int.gcd k d = 1 ∧ ‖τ γ + (τ γ)⁻¹‖ = 2 * |Real.cos (2 * Real.pi * k / d)| := by
    exact?;
  have h_sigma_beta : σ β = τ γ + (τ γ)⁻¹ := by
    replace hτ := congr_fun hτ β; aesop;
  exact h_sigma_beta ▸ hk.le.trans ( by linarith [ hbound k hk_gcd ] )

/-
Lower bound: there exists σ achieving 2|cos(2π/d)|
-/
private lemma house_lower_bound {K : Type*} [Field K] [NumberField K]
    {β : K} {L : Type*} [Field L] [NumberField L] [Algebra K L]
    {γ : L} (hβ_eq : algebraMap K L β = γ + γ⁻¹)
    {d : ℕ} (hd : 3 ≤ d) (hord : orderOf γ = d) :
    ∃ σ : K →+* ℂ, ‖σ β‖ = 2 * |Real.cos (2 * π / d)| := by
  -- Use exists_embedding_to_root to get τ : L →+* ℂ with τ(γ) = exp(2πi/d).
  obtain ⟨τ, hτ⟩ : ∃ τ : L →+* ℂ, τ γ = Complex.exp (2 * Real.pi * Complex.I / d) := by
    exact?;
  refine' ⟨ _, _ ⟩;
  exact τ.comp ( algebraMap K L );
  simp_all +decide [ Complex.norm_def, Complex.normSq ];
  norm_num [ Complex.exp_re, Complex.exp_im, Real.cos_sq' ] ; ring;
  rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> norm_num <;> nlinarith [ Real.sin_sq_add_cos_sq ( Real.pi * ( d : ℝ ) ⁻¹ * 2 ), abs_mul_abs_self ( Real.cos ( Real.pi * ( d : ℝ ) ⁻¹ * 2 ) ) ]

/-
Lower bound odd: there exists σ achieving 2cos(π/d) for odd d
-/
private lemma house_lower_bound_odd {K : Type*} [Field K] [NumberField K]
    {β : K} {L : Type*} [Field L] [NumberField L] [Algebra K L]
    {γ : L} (hβ_eq : algebraMap K L β = γ + γ⁻¹)
    {d : ℕ} (hd : 3 ≤ d) (hd_odd : d % 2 = 1) (hord : orderOf γ = d) :
    ∃ σ : K →+* ℂ, ‖σ β‖ = 2 * Real.cos (π / d) := by
  -- Use exists_embedding_to_coprime_root to get τ with τ(γ) = exp(2πi(d-1)/(2d)).
  obtain ⟨τ, hτ⟩ : ∃ τ : L →+* ℂ, τ γ = Complex.exp (2 * Real.pi * Complex.I * (d - 1) / (2 * d)) := by
    obtain ⟨τ, hτ⟩ : ∃ τ : L →+* ℂ, τ γ = Complex.exp (2 * Real.pi * Complex.I * ((d - 1) / 2) / d) := by
      have h_coprime : Nat.Coprime ((d - 1) / 2) d := by
        cases Nat.even_or_odd' d ; aesop
      have h_pos : 0 < (d - 1) / 2 := by
        omega
      have h_lt : (d - 1) / 2 < d := by
        omega
      convert exists_embedding_to_coprime_root hd hord h_coprime h_pos h_lt using 1;
      rw [ Nat.cast_div ( Nat.dvd_of_mod_eq_zero ( by omega ) ) ( by norm_num ) ] ; norm_num [ Nat.cast_sub ( by linarith : 1 ≤ d ) ];
    grind;
  refine' ⟨ τ.comp ( algebraMap K L ), _ ⟩;
  simp_all +decide [ Complex.norm_def, Complex.normSq ];
  norm_num [ Complex.exp_re, Complex.exp_im, div_eq_mul_inv ];
  norm_num [ sq, mul_assoc, ne_of_gt ( zero_lt_three.trans_le hd ) ] ; ring_nf ; norm_num [ mul_div, ne_of_gt ( zero_lt_three.trans_le hd ) ];
  rw [ Real.sqrt_eq_iff_mul_self_eq ] <;> nlinarith [ Real.cos_sq' ( Real.pi * ( d : ℝ ) ⁻¹ ), show 0 ≤ Real.cos ( Real.pi * ( d : ℝ ) ⁻¹ ) from Real.cos_nonneg_of_mem_Icc ⟨ by nlinarith [ Real.pi_pos, show ( d : ℝ ) ≥ 3 by norm_cast, mul_inv_cancel₀ ( by positivity : ( d : ℝ ) ≠ 0 ) ], by nlinarith [ Real.pi_pos, show ( d : ℝ ) ≥ 3 by norm_cast, mul_inv_cancel₀ ( by positivity : ( d : ℝ ) ≠ 0 ) ] ⟩ ]

/-
For orderOf γ ≥ 3 with β = γ + γ⁻¹ and house β < 2,
    there exists m > 0 with house β = 2cos(π/m).
-/
private lemma house_eq_cos_of_high_order {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    {β : K} (hβ_ne : β ≠ 0) (_hhouse_lt : house β < 2)
    {L : Type*} [Field L] [NumberField L] [Algebra K L] [Algebra ℚ L] [IsScalarTower ℚ K L]
    {γ : L} (_hγ_ne : γ ≠ 0)
    (hβ_eq : algebraMap K L β = γ + γ⁻¹)
    (d : ℕ) (hd : 3 ≤ d) (hord : orderOf γ = d) :
    ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (Real.pi / m) := by
  by_cases h_even : d % 2 = 0;
  · by_cases h_d_ge_6 : 6 ≤ d;
    · -- For $d \geq 6$ and even, we have $house \beta = 2 \cos(2\pi/d)$.
      have h_house_even : house β = 2 * Real.cos (2 * Real.pi / d) := by
        have h_upper_bound : ∀ σ : K →+* ℂ, ‖σ β‖ ≤ 2 * Real.cos (2 * Real.pi / d) := by
          intro σ
          apply house_upper_bound hβ_eq (by linarith) hord σ (2 * Real.cos (2 * Real.pi / d)) (by
          intro k hk_coprime
          have h_cos_bound : |Real.cos (2 * Real.pi * k / d)| ≤ Real.cos (2 * Real.pi / d) := by
            have := Submission.Analysis.abs_cos_le_cos_two_pi_div_of_even ( by linarith : 4 ≤ d ) h_even ( show Int.gcd k d = 1 from hk_coprime ) ; aesop;
          linarith [h_cos_bound]);
        have h_lower_bound : ∃ σ : K →+* ℂ, ‖σ β‖ = 2 * Real.cos (2 * Real.pi / d) := by
          have := house_lower_bound hβ_eq hd hord;
          exact this.imp fun σ hσ => by rw [ hσ, abs_of_nonneg ( Real.cos_nonneg_of_mem_Icc ⟨ by rw [ le_div_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( d : ℝ ) ≥ 6 by norm_cast ], by rw [ div_le_iff₀ ( by positivity ) ] ; nlinarith [ Real.pi_pos, show ( d : ℝ ) ≥ 6 by norm_cast ] ⟩ ) ] ;
        unfold house;
        refine' le_antisymm _ _;
        · exact?;
        · obtain ⟨ σ, hσ ⟩ := h_lower_bound;
          rw [ ← hσ ];
          convert norm_embedding_le_house β σ using 1;
      use d / 2;
      exact ⟨ Nat.div_pos ( by linarith ) zero_lt_two, h_house_even.trans ( by rw [ Nat.cast_div ( Nat.dvd_of_mod_eq_zero h_even ) ( by norm_num ) ] ; ring ) ⟩;
    · interval_cases d <;> simp_all +decide;
      -- Since γ has order 4, we have γ^4 = 1 and γ^2 = -1.
      have hγ4 : γ ^ 4 = 1 := by
        rw [ ← hord, pow_orderOf_eq_one ]
      have hγ2 : γ ^ 2 = -1 := by
        have hγ2 : γ ^ 2 ≠ 1 := by
          exact fun h => by have := orderOf_dvd_iff_pow_eq_one.mpr h; simp_all +decide ;
        exact mul_left_cancel₀ ( sub_ne_zero_of_ne hγ2 ) ( by linear_combination' hγ4 );
      have hγ_inv : γ⁻¹ = -γ := by
        exact inv_eq_of_mul_eq_one_right ( by linear_combination' -hγ2 );
      aesop;
  · have h_cos : ∀ σ : K →+* ℂ, ‖σ β‖ ≤ 2 * Real.cos (Real.pi / d) := by
      intro σ
      apply house_upper_bound hβ_eq hd hord σ (2 * Real.cos (Real.pi / d)) (fun k hk => by
        have := Submission.Analysis.abs_cos_le_cos_pi_div_of_odd hd ( Nat.mod_two_ne_zero.mp h_even ) hk; ring_nf at this ⊢; linarith;)
    generalize_proofs at *; (
    obtain ⟨σ, hσ⟩ : ∃ σ : K →+* ℂ, ‖σ β‖ = 2 * Real.cos (Real.pi / d) := by
      apply_rules [ house_lower_bound_odd ];
      exact Nat.mod_two_ne_zero.mp h_even
    generalize_proofs at *; (
    refine' ⟨ d, by linarith, le_antisymm _ _ ⟩ <;> simp_all +decide [ house ];
    · grind +suggestions;
    · rw [ ← hσ ];
      exact norm_embedding_le_house β σ))

private lemma house_from_root_of_unity {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    {β : K} (hβ_ne : β ≠ 0) (hhouse_lt : house β < 2)
    {L : Type*} [Field L] [NumberField L] [Algebra K L] [Algebra ℚ L] [IsScalarTower ℚ K L]
    {γ : L} {d : ℕ} (hd : 0 < d) (hγ_pow : γ ^ d = 1) (hγ_ne : γ ≠ 0)
    (hβ_eq : algebraMap K L β = γ + γ⁻¹) :
    ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (Real.pi / m) := by
  have hord_pos : 0 < orderOf γ :=
    (isOfFinOrder_iff_pow_eq_one.mpr ⟨d, hd, hγ_pow⟩).orderOf_pos
  by_cases hord : orderOf γ ≤ 2
  · exact absurd (house_ge_two_of_low_order hγ_ne hβ_eq hord_pos hord hβ_ne) (not_le.mpr hhouse_lt)
  · push_neg at hord
    have hord_ge : 3 ≤ orderOf γ := by omega
    exact house_eq_cos_of_high_order hβ_ne hhouse_lt hγ_ne hβ_eq (orderOf γ) hord_ge rfl

set_option maxHeartbeats 1600000 in
/-- The core hard case: β ≠ 0 with house < 2 implies house = 2cos(π/m). -/
theorem house_eq_cos_core {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] {β : K}
    (hβ_int : IsIntegral ℤ β)
    (hβ_real : β ∈ NumberField.maximalRealSubfield K)
    (hβ_ne : β ≠ 0) (hhouse_lt : house β < 2) :
    ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (Real.pi / m) := by
  set p : K[X] := X ^ 2 - C β * X + 1 with hp_def
  set L := SplittingField p
  obtain ⟨γ, hγ_eq, hγ_ne⟩ := quad_root_in_splittingField β
  have hγ_int : IsIntegral ℤ γ := isIntegral_of_quadratic_root hβ_int hγ_eq
  have hγ_norm := norm_of_quad_root_le_one hβ_real hhouse_lt hγ_eq
  have h_kron := @Embeddings.pow_eq_one_of_norm_le_one L _ _ ℂ _ _ _ γ hγ_ne hγ_int hγ_norm
  obtain ⟨d, hd_pos, hγ_pow⟩ := h_kron
  have hβ_eq : algebraMap K L β = γ + γ⁻¹ := quad_root_eq β γ hγ_eq hγ_ne
  exact house_from_root_of_unity hβ_ne hhouse_lt hd_pos hγ_pow hγ_ne hβ_eq

end Submission.Helpers