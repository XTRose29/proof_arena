import Mathlib

open NumberField Polynomial IntermediateField

namespace Submission.Helpers

noncomputable section

lemma exists_embedding_norm_eq_house {K : Type*} [Field K] [NumberField K] (x : K) :
    ∃ φ : K →+* ℂ, ‖φ x‖ = house x := by
  obtain ⟨φ, -, hφ⟩ :=
    Finset.exists_mem_eq_sup' (Finset.univ_nonempty : (Finset.univ : Finset (K →+* ℂ)).Nonempty)
      (fun ψ : K →+* ℂ ↦ ‖ψ x‖₊)
  refine ⟨φ, ?_⟩
  rw [house_eq_sup', hφ]
  rfl

lemma map_aeval_rat {A B : Type*} [Field A] [Field B] [Algebra ℚ A] [Algebra ℚ B]
    (f : A →+* B) (x : A) (p : ℚ[X]) : f (Polynomial.aeval x p) = Polynomial.aeval (f x) p := by
  have h := Polynomial.map_aeval_eq_aeval_map
    (R := ℚ) (S := A) (T := ℚ) (U := B) (φ := RingHom.id ℚ) (ψ := f)
    (by ext r; simp) p x
  simpa using h

lemma exp_mul_I_add_inv (t : ℝ) :
    Complex.exp (t * Complex.I) + (Complex.exp (t * Complex.I))⁻¹ =
      (2 * Real.cos t : ℂ) := by
  rw [← Complex.exp_neg, Complex.exp_mul_I]
  rw [show -(↑t * Complex.I) = (↑(-t) : ℂ) * Complex.I by push_cast; ring,
    Complex.exp_mul_I]
  rw [← Complex.ofReal_cos t, ← Complex.ofReal_sin t,
    ← Complex.ofReal_cos (-t), ← Complex.ofReal_sin (-t), Real.cos_neg, Real.sin_neg]
  push_cast
  ring_nf

lemma two_le_norm_add_inv_real {x : ℝ} (hx0 : x ≠ 0) : 2 ≤ ‖x + x⁻¹‖ := by
  rw [Real.norm_eq_abs]
  have hmul : x * x⁻¹ = 1 := mul_inv_cancel₀ hx0
  rcases lt_or_gt_of_ne hx0 with hx | hx
  · rw [abs_of_nonpos]
    · nlinarith [sq_nonneg (x + 1)]
    · nlinarith [sq_nonneg (x + 1)]
  · rw [abs_of_nonneg]
    · nlinarith [sq_nonneg (x - 1)]
    · nlinarith [sq_nonneg (x - 1)]

lemma norm_eq_one_of_add_inv_real {z b : ℂ} (hz : z ≠ 0) (hzb : z + z⁻¹ = b)
    (hb_real : star b = b) (hb_lt : ‖b‖ < 2) : ‖z‖ = 1 := by
  have hb_im : b.im = 0 := Complex.conj_eq_iff_im.mp hb_real
  have him : z.im - z.im / Complex.normSq z = 0 := by
    have := congrArg Complex.im hzb
    simpa [Complex.inv_im, hb_im, sub_eq_add_neg, div_eq_mul_inv] using this
  have hnormSq_pos : 0 < Complex.normSq z := Complex.normSq_pos.mpr hz
  have hfactor : z.im * (Complex.normSq z - 1) = 0 := by
    field_simp [ne_of_gt hnormSq_pos] at him
    nlinarith
  rcases mul_eq_zero.mp hfactor with hz_im | hnormSq
  · let x : ℝ := z.re
    have hz_real : z = (x : ℂ) := by
      apply Complex.ext
      · rfl
      · simp [x, hz_im]
    have hx : x ≠ 0 := by
      intro h
      apply hz
      rw [hz_real, h]
      simp
    have hb_norm : ‖b‖ = ‖x + x⁻¹‖ := by
      calc
        ‖b‖ = ‖z + z⁻¹‖ := congrArg norm hzb.symm
        _ = ‖(x : ℂ) + (x : ℂ)⁻¹‖ := by rw [hz_real]
        _ = ‖x + x⁻¹‖ := by
          simp [← Complex.ofReal_add, ← Complex.ofReal_inv, Complex.norm_real]
    rw [hb_norm] at hb_lt
    exact (not_lt_of_ge (two_le_norm_add_inv_real hx) hb_lt).elim
  · have hsq : ‖z‖ ^ 2 = 1 := by
      rw [Complex.sq_norm, sub_eq_zero.mp hnormSq]
    nlinarith [norm_nonneg z]

lemma exists_primitiveRoot_add_inv_eq {K : Type*} [Field K] [NumberField K]
    {α : K} (hα_int : IsIntegral ℤ α)
    (hα_real : α ∈ NumberField.maximalRealSubfield K) (hα_lt : house α < 2)
    (φ : K →+* ℂ) :
    ∃ z : ℂ, ∃ n : ℕ, 0 < n ∧ IsPrimitiveRoot z n ∧ z + z⁻¹ = φ α := by
  let a : ℂ := φ α
  let q : ℂ[X] := Polynomial.X ^ 2 - Polynomial.C a * Polynomial.X + 1
  have hq_monic : q.Monic := by
    dsimp [q]
    rw [sub_eq_add_neg, add_assoc]
    apply Polynomial.monic_X_pow_add
    compute_degree
    all_goals norm_num
  have hq_natDegree : q.natDegree = 2 := by
    dsimp [q]
    compute_degree
    all_goals norm_num
  have hq_degree : q.degree ≠ 0 := by
    have hq_degree_eq : q.degree = 2 := by
      dsimp [q]
      compute_degree
      all_goals norm_num
    rw [hq_degree_eq]
    norm_num
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root q hq_degree
  have hz_poly : z ^ 2 - a * z + 1 = 0 := by
    simpa [q] using hz
  have hz0 : z ≠ 0 := by
    intro h
    subst z
    norm_num at hz_poly
  have hza : z + z⁻¹ = a := by
    field_simp [hz0]
    linear_combination hz_poly
  have ha_int : IsIntegral ℤ a := by
    dsimp [a]
    exact hα_int.map φ.toRatAlgHom
  have hz_int : IsIntegral ℤ z := by
    refine IsIntegral.of_aeval_monic_of_isIntegral_coeff hq_monic ?_ ?_ ?_
    · rw [hq_natDegree]
      norm_num
    · rw [Polynomial.IsRoot.def] at hz
      rw [hz]
      exact isIntegral_zero
    · intro i
      dsimp [q]
      rw [Polynomial.coeff_add, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
      exact (by
        have hpow : IsIntegral ℤ ((Polynomial.X ^ 2 : ℂ[X]).coeff i) := by
          rw [Polynomial.coeff_X_pow]
          split_ifs
          · exact isIntegral_one
          · exact isIntegral_zero
        have hX : IsIntegral ℤ ((Polynomial.X : ℂ[X]).coeff i) := by
          rw [Polynomial.coeff_X]
          split_ifs
          · exact isIntegral_one
          · exact isIntegral_zero
        have hone : IsIntegral ℤ ((1 : ℂ[X]).coeff i) := by
          rw [Polynomial.coeff_one]
          split_ifs
          · exact isIntegral_one
          · exact isIntegral_zero
        exact (hpow.sub (ha_int.mul hX)).add hone)
  let L := ℚ⟮z⟯
  let y : L := ⟨z, IntermediateField.mem_adjoin_simple_self ℚ z⟩
  letI : NumberField L := {
    to_charZero := ℚ⟮z⟯.charZero
    to_finiteDimensional := IntermediateField.adjoin.finiteDimensional hz_int.tower_top
  }
  have hy0 : y ≠ 0 := by
    exact Subtype.coe_ne_coe.mp hz0
  have hy_int : IsIntegral ℤ y := IntermediateField.coe_isIntegral_iff.mp hz_int
  have hy_add_inv : algebraMap L ℂ (y + y⁻¹) = a := by
    simpa [y] using hza
  have hmin_y : Polynomial.aeval (y + y⁻¹) (minpoly ℚ α) = 0 := by
    apply (algebraMap L ℂ).injective
    rw [map_zero]
    calc
      algebraMap L ℂ (Polynomial.aeval (y + y⁻¹) (minpoly ℚ α)) =
          Polynomial.aeval (algebraMap L ℂ (y + y⁻¹)) (minpoly ℚ α) :=
        map_aeval_rat (algebraMap L ℂ) _ _
      _ = Polynomial.aeval a (minpoly ℚ α) := by rw [hy_add_inv]
      _ = φ (Polynomial.aeval α (minpoly ℚ α)) := by
        exact (map_aeval_rat φ α (minpoly ℚ α)).symm
      _ = 0 := by rw [minpoly.aeval, map_zero]
  have hy_norm : ∀ ψ : L →+* ℂ, ‖ψ y‖ = 1 := by
    intro ψ
    let b : ℂ := ψ (y + y⁻¹)
    have hb_root : b ∈ (minpoly ℚ α).rootSet ℂ := by
      rw [Polynomial.mem_rootSet]
      refine ⟨minpoly.ne_zero hα_int.tower_top, ?_⟩
      calc
        Polynomial.aeval b (minpoly ℚ α) =
            ψ (Polynomial.aeval (y + y⁻¹) (minpoly ℚ α)) := by
          exact (map_aeval_rat ψ (y + y⁻¹) (minpoly ℚ α)).symm
        _ = 0 := by rw [hmin_y, map_zero]
    rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ α] at hb_root
    obtain ⟨τ, hτ⟩ := hb_root
    have hb_real : star b = b := by
      rw [← hτ]
      exact hα_real τ
    have hb_lt : ‖b‖ < 2 := by
      rw [← hτ]
      exact (norm_embedding_le_house α τ).trans_lt hα_lt
    apply norm_eq_one_of_add_inv_real ((map_ne_zero ψ).mpr hy0) _ hb_real hb_lt
    simp [b]
  obtain ⟨N, hN, hyN⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one L ℂ hy0 hy_int
      (fun ψ ↦ (hy_norm ψ).le)
  obtain ⟨n, hn, hprim_y⟩ := IsPrimitiveRoot.exists_pos hyN hN.ne'
  refine ⟨z, n, hn, ?_, hza⟩
  simpa [y] using hprim_y.map_of_injective (algebraMap L ℂ).injective

lemma norm_add_inv_le_house_of_same_primitiveRoot {K : Type*} [Field K] [NumberField K]
    {α : K} (hα_int : IsIntegral ℤ α) (φ : K →+* ℂ) {z u : ℂ} {n : ℕ}
    (hn : 0 < n) (hz : IsPrimitiveRoot z n) (hu : IsPrimitiveRoot u n)
    (hzα : z + z⁻¹ = φ α) : ‖u + u⁻¹‖ ≤ house α := by
  have hz_int : IsIntegral ℤ z := hz.isIntegral hn
  have hz_rat : IsIntegral ℚ z := hz_int.tower_top
  let L := ℚ⟮z⟯
  let y : L := ⟨z, IntermediateField.mem_adjoin_simple_self ℚ z⟩
  have hu_root : u ∈ (minpoly ℚ z).aroots ℂ := by
    rw [Polynomial.mem_aroots]
    refine ⟨minpoly.ne_zero hz_rat, ?_⟩
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hz hn,
      Polynomial.cyclotomic_eq_minpoly_rat hu hn]
    exact minpoly.aeval ℚ u
  let ψ : L →ₐ[ℚ] ℂ :=
    (IntermediateField.algHomAdjoinIntegralEquiv ℚ hz_rat).symm ⟨u, hu_root⟩
  have hψy : ψ y = u := by
    change ((IntermediateField.algHomAdjoinIntegralEquiv ℚ hz_rat).symm ⟨u, hu_root⟩)
      (IntermediateField.AdjoinSimple.gen ℚ z) = u
    exact IntermediateField.algHomAdjoinIntegralEquiv_symm_apply_gen ℚ hz_rat ⟨u, hu_root⟩
  have hy_add_inv : algebraMap L ℂ (y + y⁻¹) = φ α := by
    simpa [y] using hzα
  have hmin_y : Polynomial.aeval (y + y⁻¹) (minpoly ℚ α) = 0 := by
    apply (algebraMap L ℂ).injective
    rw [map_zero]
    calc
      algebraMap L ℂ (Polynomial.aeval (y + y⁻¹) (minpoly ℚ α)) =
          Polynomial.aeval (algebraMap L ℂ (y + y⁻¹)) (minpoly ℚ α) :=
        map_aeval_rat (algebraMap L ℂ) _ _
      _ = Polynomial.aeval (φ α) (minpoly ℚ α) := by rw [hy_add_inv]
      _ = φ (Polynomial.aeval α (minpoly ℚ α)) := by
        exact (map_aeval_rat φ α (minpoly ℚ α)).symm
      _ = 0 := by rw [minpoly.aeval, map_zero]
  have hu_sum_root : u + u⁻¹ ∈ (minpoly ℚ α).rootSet ℂ := by
    rw [Polynomial.mem_rootSet]
    refine ⟨minpoly.ne_zero hα_int.tower_top, ?_⟩
    calc
      Polynomial.aeval (u + u⁻¹) (minpoly ℚ α) =
          Polynomial.aeval (ψ (y + y⁻¹)) (minpoly ℚ α) := by simp [hψy]
      _ = ψ (Polynomial.aeval (y + y⁻¹) (minpoly ℚ α)) := by
        exact (map_aeval_rat ψ.toRingHom (y + y⁻¹) (minpoly ℚ α)).symm
      _ = 0 := by rw [hmin_y, map_zero]
  rw [← NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ α] at hu_sum_root
  obtain ⟨τ, hτ⟩ := hu_sum_root
  rw [← hτ]
  exact norm_embedding_le_house α τ

lemma house_eq_two_mul_cos_of_embedding_eq_house {K : Type*} [Field K] [NumberField K]
    {α : K} (hα_int : IsIntegral ℤ α)
    (hα_real : α ∈ NumberField.maximalRealSubfield K) (hα_lt : house α < 2)
    (φ : K →+* ℂ) (hφ : φ α = (house α : ℂ)) :
    ∃ m : ℕ, 0 < m ∧ house α = 2 * Real.cos (Real.pi / m) := by
  obtain ⟨z, n, hn, hz, hzφ⟩ :=
    exists_primitiveRoot_add_inv_eq hα_int hα_real hα_lt φ
  have hn0 : n ≠ 0 := hn.ne'
  have hz0 : z ≠ 0 := hz.ne_zero hn0
  have hznorm : ‖z‖ = 1 := hz.norm'_eq_one hn0
  have hzsum : z + z⁻¹ = (house α : ℂ) := hzφ.trans hφ
  have hhouse_cos_arg : house α = 2 * Real.cos z.arg := by
    have hre := congrArg Complex.re hzsum
    rw [Complex.add_re, Complex.inv_re, ← Complex.sq_norm, hznorm, Complex.ofReal_re] at hre
    have hcos : Real.cos z.arg = z.re := by
      simpa [hznorm] using Complex.cos_arg hz0
    nlinarith
  have hz_ne_one : z ≠ 1 := by
    intro h
    subst z
    have hre := congrArg Complex.re hzsum
    norm_num at hre
    nlinarith
  have harg_ne : z.arg ≠ 0 := by
    intro h
    exact hz_ne_one ((hz.arg_eq_zero_iff hn0).mp h)
  obtain ⟨i, harg, -, -⟩ := hz.arg hn0
  have hi0 : i ≠ 0 := by
    intro h
    subst i
    norm_num at harg
    exact harg_ne harg
  have hi_abs_one : (1 : ℝ) ≤ |(i : ℝ)| := by
    exact_mod_cast Int.one_le_abs hi0
  have hn_real : (0 : ℝ) < n := by exact_mod_cast hn
  let t : ℝ := 2 * Real.pi / n
  have ht_nonneg : 0 ≤ t := by positivity
  have hangle_lower : t ≤ |z.arg| := by
    calc
      t = (1 / (n : ℝ)) * (2 * Real.pi) := by simp [t]; ring_nf
      _ ≤ (|(i : ℝ)| / (n : ℝ)) * (2 * Real.pi) := by gcongr
      _ = |(i : ℝ) / (n : ℝ) * (2 * Real.pi)| := by
        rw [abs_mul, abs_div, abs_of_pos hn_real,
          abs_of_pos (mul_pos (by norm_num) Real.pi_pos)]
      _ = |z.arg| := by rw [harg]
  have hcos_nonneg : 0 ≤ Real.cos z.arg := by
    nlinarith [house_nonneg α]
  have hangle_upper : |z.arg| ≤ Real.pi / 2 := by
    rw [abs_le]
    constructor
    · by_contra h
      have hneg : Real.cos z.arg < 0 := by
        rw [← Real.cos_neg]
        apply Real.cos_neg_of_pi_div_two_lt_of_lt
        · linarith
        · linarith [Complex.neg_pi_lt_arg z, Real.pi_pos]
      linarith
    · by_contra h
      have hneg : Real.cos z.arg < 0 := by
        apply Real.cos_neg_of_pi_div_two_lt_of_lt
        · linarith
        · linarith [Complex.arg_le_pi z, Real.pi_pos]
      linarith
  have ht_le : t ≤ Real.pi / 2 := hangle_lower.trans hangle_upper
  have hn_four : 4 ≤ n := by
    have hmul := (div_le_iff₀ hn_real).mp ht_le
    have hn_four_real : (4 : ℝ) ≤ n := by nlinarith [Real.pi_pos]
    exact_mod_cast hn_four_real
  have hhouse_upper : house α ≤ 2 * Real.cos t := by
    have hcos_le : Real.cos z.arg ≤ Real.cos t := by
      rw [← Real.cos_abs]
      exact Real.cos_le_cos_of_nonneg_of_le_pi ht_nonneg
        (hangle_upper.trans (by linarith [Real.pi_pos])) hangle_lower
    nlinarith
  let u : ℂ := Complex.exp (t * Complex.I)
  have hu : IsPrimitiveRoot u n := by
    dsimp [u, t]
    convert Complex.isPrimitiveRoot_exp n hn0 using 1
    push_cast
    ring_nf
  have hu_sum : u + u⁻¹ = (2 * Real.cos t : ℂ) := by
    exact exp_mul_I_add_inv t
  have hcos_t_nonneg : 0 ≤ Real.cos t := by
    exact Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) ht_le
  have hhouse_lower : 2 * Real.cos t ≤ house α := by
    have hbound := norm_add_inv_le_house_of_same_primitiveRoot hα_int φ hn hz hu hzφ
    rw [hu_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcos_t_nonneg] at hbound
    norm_num at hbound
    exact hbound
  have hhouse : house α = 2 * Real.cos t := le_antisymm hhouse_upper hhouse_lower
  have hn_even : Even n := by
    by_contra hneven
    have hn_odd : Odd n := Nat.not_even_iff_odd.mp hneven
    obtain ⟨r, hr⟩ := hn_odd
    have hr_coprime : r.Coprime n := by
      rw [hr, show 2 * r + 1 = (r + 1) + r by omega, Nat.coprime_add_self_right,
        show r + 1 = 1 + r by omega, Nat.coprime_add_self_right]
      exact Nat.coprime_one_right r
    let v : ℂ := Complex.exp (2 * Real.pi * Complex.I * (r / n))
    have hv : IsPrimitiveRoot v n := by
      exact Complex.isPrimitiveRoot_exp_of_coprime r n hn0 hr_coprime
    have hv_exp : v = Complex.exp ((2 * Real.pi * r / n) * Complex.I) := by
      dsimp [v]
      congr 1
      ring_nf
    have hangle_r : (2 * Real.pi * r / n : ℝ) = Real.pi - Real.pi / n := by
      rw [hr]
      push_cast
      field_simp
      ring_nf
    have hv_sum : v + v⁻¹ = (-2 * Real.cos (Real.pi / n) : ℂ) := by
      rw [hv_exp]
      calc
        Complex.exp ((2 * Real.pi * r / n) * Complex.I) +
            (Complex.exp ((2 * Real.pi * r / n) * Complex.I))⁻¹ =
            (2 * Real.cos (2 * Real.pi * r / n) : ℂ) := by
          convert exp_mul_I_add_inv (2 * Real.pi * r / n) using 1
          push_cast
          ring_nf
        _ = (-2 * Real.cos (Real.pi / n) : ℂ) := by
          rw [hangle_r, Real.cos_pi_sub]
          push_cast
          ring_nf
    have hpi_div_nonneg : 0 ≤ Real.pi / (n : ℝ) := by positivity
    have hpi_div_le : Real.pi / (n : ℝ) ≤ Real.pi / 2 := by
      have hn_two_real : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
      exact (div_le_div_iff_of_pos_left Real.pi_pos hn_real (by norm_num)).mpr hn_two_real
    have hcos_pi_div_nonneg : 0 ≤ Real.cos (Real.pi / n) :=
      Real.cos_nonneg_of_neg_pi_div_two_le_of_le (by linarith [Real.pi_pos]) hpi_div_le
    have hv_bound := norm_add_inv_le_house_of_same_primitiveRoot hα_int φ hn hz hv hzφ
    rw [hv_sum, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hcos_pi_div_nonneg] at hv_bound
    norm_num at hv_bound
    have hpi_div_lt_t : Real.pi / (n : ℝ) < t := by
      dsimp [t]
      rw [show 2 * Real.pi / (n : ℝ) = 2 * (Real.pi / n) by ring_nf]
      nlinarith [div_pos Real.pi_pos hn_real]
    have hcos_strict : Real.cos t < Real.cos (Real.pi / n) :=
      Real.cos_lt_cos_of_nonneg_of_le_pi_div_two hpi_div_nonneg ht_le hpi_div_lt_t
    nlinarith
  obtain ⟨m, hm⟩ := hn_even
  have hm_pos : 0 < m := by omega
  refine ⟨m, hm_pos, ?_⟩
  rw [hhouse]
  congr 2
  dsimp [t]
  rw [hm]
  push_cast
  field_simp
  ring_nf

end

end Submission.Helpers
