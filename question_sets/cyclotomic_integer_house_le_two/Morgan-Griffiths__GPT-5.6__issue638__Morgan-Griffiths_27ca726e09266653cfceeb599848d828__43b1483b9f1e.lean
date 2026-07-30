import Mathlib

namespace Submission

open IntermediateField Polynomial
open NumberField
/-ResultDefinitionsBegin-/
/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/
/-ResultDefinitionsEnd-/


-- The elementary analytic fact behind the `2` in this question.  Notice that
-- it is a statement about complex numbers (and so does not use a chosen real
-- embedding).
private lemma quadratic_on_unit_circle
    (t w : ℂ) (ht : star t = t) (ht' : ‖t‖ ≤ (2:ℝ))
    (hw : w ≠ 0) (he : w^2 - t*w + 1 = 0) : ‖w‖ = (1:ℝ) := by
  have tim : t.im = 0 := by
    have h := congrArg Complex.im ht
    -- conjugation changes just the imaginary part
    simp [Complex.star_def] at h
    linarith
  -- We only use the two real equations in the quadratic.  This avoids
  -- having to make a choice of square root.
  have reeq : w.re^2 - t.re*w.re - w.im^2 + 1 = 0 := by
    have h := congrArg Complex.re he
    simp [Complex.mul_re, pow_two, tim] at h
    nlinarith
  have imeq : (2*w.re - t.re) * w.im = 0 := by
    have h := congrArg Complex.im he
    simp [Complex.mul_im, pow_two, tim] at h
    nlinarith
  have tn : |t.re| ≤ (2:ℝ) := by
    have tre : (t.re : ℂ) = t := by apply Complex.ext <;> simp [tim]
    rw [← tre, Complex.norm_real, Real.norm_eq_abs] at ht'
    exact ht'
  rcases mul_eq_zero.mp imeq with ha | hb
  · have ha' : t.re = 2*w.re := by linarith
    have hab : w.re*w.re + w.im*w.im = 1 := by
      rw [ha'] at reeq
      nlinarith [reeq]
    have hs := Complex.sq_norm w
    rw [Complex.normSq_apply] at hs
    have hn : 0 ≤ ‖w‖ := norm_nonneg _
    nlinarith
  · have bim : w.im = 0 := hb
    have are : w.re ≠ 0 := by
      intro h
      apply hw
      apply Complex.ext <;> simp [h, bim]
    have abseq : w.re = 1 ∨ w.re = -1 := by
      rcases lt_or_gt_of_ne are with an | ap
      · right
        have lo : -2 ≤ t.re := (abs_le.mp tn).1
        rw [bim] at reeq
        nlinarith [mul_nonpos_of_nonneg_of_nonpos (sub_nonneg.mpr lo) (le_of_lt an)]
      · left
        have hi : t.re ≤ 2 := (abs_le.mp tn).2
        rw [bim] at reeq
        nlinarith [mul_nonneg (sub_nonneg.mpr hi) (le_of_lt ap)]
    rcases abseq with h | h
    · have hn : ‖w‖ ^ 2 = 1 := by rw [Complex.sq_norm, Complex.normSq_apply, bim, h]; norm_num
      have hh := norm_nonneg w
      nlinarith
    · have hn : ‖w‖ ^ 2 = 1 := by rw [Complex.sq_norm, Complex.normSq_apply, bim, h]; norm_num
      have hh := norm_nonneg w
      nlinarith

private lemma primitive_data {K : Type*} [Field K] [NumberField K]
    {b : K} (bi : IsIntegral ℤ b)
    (br : b ∈ NumberField.maximalRealSubfield K) (bh : house b ≤ 2) :
    ∃ (z : ℂ) (r : ℕ), 0 < r ∧ IsPrimitiveRoot z r ∧
       house b = ‖z + z⁻¹‖ ∧
       (∀ ξ : ℂ, IsPrimitiveRoot ξ r → ‖ξ + ξ⁻¹‖ ≤ house b) := by
  classical
  obtain ⟨φ, -, hφ⟩ := Finset.exists_mem_eq_sup'
    (s := (Finset.univ : Finset (K →+* ℂ))) Finset.univ_nonempty
      (fun σ : K →+* ℂ => ‖σ b‖₊)
  have hmax : house b = ‖φ b‖ := by
    rw [NumberField.house_eq_sup']
    rw [hφ]
    rfl
  let t : ℂ := φ b
  have treal : star t = t := br φ
  have tnorm : ‖t‖ ≤ (2:ℝ) := hmax ▸ bh
  let q : Polynomial ℂ := Polynomial.X^2 - Polynomial.C t * Polynomial.X + Polynomial.C (1:ℂ)
  have qcoeff : q.coeff 2 = 1 := by simp [q, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one]
  have qnz : q ≠ 0 := by
    intro h
    simpa [h] using qcoeff
  have qnat : 2 ≤ q.natDegree := Polynomial.le_natDegree_of_ne_zero (by simpa [qcoeff] : q.coeff 2 ≠ 0)
  have qdeg : q.degree ≠ 0 := by
    intro h
    rw [Polynomial.degree_eq_natDegree qnz] at h
    have : q.natDegree = 0 := WithBot.coe_eq_zero.mp h
    omega
  obtain ⟨z, hz⟩ := IsAlgClosed.exists_root q qdeg
  have zeq : z^2 - t*z + 1 = 0 := by
    simpa [q, Polynomial.IsRoot.def] using hz
  have z0 : z ≠ 0 := by
    intro h
    rw [h] at zeq
    norm_num at zeq
  have zsum : z + z⁻¹ = t := by
    apply (mul_left_cancel₀ z0)
    field_simp
    -- clearing the nonzero z leaves exactly the quadratic
    linear_combination zeq
  have tint : IsIntegral ℤ t := by
    dsimp [t]
    exact bi.map φ.toIntAlgHom
  have zint : IsIntegral ℤ z := by
    refine IsIntegral.of_aeval_monic_of_isIntegral_coeff (p := q)
      (by unfold q; monicity <;> norm_num) (by omega)
      ?_ ?_
    · -- evaluation of the quadratic vanishes
      have h : Polynomial.eval z q = 0 := by simpa [Polynomial.IsRoot.def] using hz
      rw [h]
      exact isIntegral_zero
    · intro i
      by_cases h2 : i = 2
      · subst i; simpa [qcoeff] using (isIntegral_one : IsIntegral ℤ (1:ℂ))
      by_cases h1 : i = 1
      · subst i
        have : q.coeff 1 = -t := by simp [q, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one]
        rw [this]
        exact tint.neg
      by_cases h0 : i = 0
      · subst i
        have : q.coeff 0 = 1 := by simp [q, Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one]
        rw [this]
        exact isIntegral_one
      have hc : q.coeff i = 0 := by
        unfold q
        simp [Polynomial.coeff_sub, Polynomial.coeff_add, Polynomial.coeff_one,
          Polynomial.coeff_X_pow, Polynomial.coeff_X, h2, h1, h0, Ne.symm h1]
      rw [hc]
      exact isIntegral_zero
  -- Make the (small) number field generated by this root.  Working in this
  -- field, rather than in ℂ, is important when applying Kronecker's theorem.
  let L := ℚ⟮z⟯
  letI : NumberField L := {
    to_charZero := (ℚ⟮z⟯).charZero,
    to_finiteDimensional := IntermediateField.adjoin.finiteDimensional
      (zint.tower_top : IsIntegral ℚ z) }
  let y : L := ⟨z, IntermediateField.mem_adjoin_simple_self ℚ z⟩
  have y0 : y ≠ 0 := by intro h; exact z0 (congrArg Subtype.val h)
  have yint : IsIntegral ℤ y :=
    IntermediateField.coe_isIntegral_iff.mp zint
  let u : L := y + y⁻¹
  have uval : (u : ℂ) = t := by
    change z + z⁻¹ = t
    exact zsum
  -- This element has the same rational polynomial relation as b.
  have bxroot : Polynomial.aeval t (minpoly ℚ b) = 0 := by
    dsimp [t]
    rw [Polynomial.aeval_def]
    have he := Polynomial.hom_eval₂ (minpoly ℚ b) (algebraMap ℚ K) φ b
    have hc : φ.comp (algebraMap ℚ K) = (algebraMap ℚ ℂ) := by ext a; simp
    rw [← hc, ← he, ← Polynomial.aeval_def, minpoly.aeval, map_zero]
  have uroot : Polynomial.aeval u (minpoly ℚ b) = 0 := by
    -- check in ℂ, where u is t
    apply ((ℚ⟮z⟯).val.toRingHom).injective
    rw [map_zero]
    rw [Polynomial.aeval_def]
    rw [Polynomial.hom_eval₂]
    change Polynomial.eval₂ _ (u:ℂ) (minpoly ℚ b) = 0
    have hc : (((ℚ⟮z⟯).val.toRingHom).comp (algebraMap ℚ L)) =
        (algebraMap ℚ ℂ) := by ext a; simp
    rw [hc]
    simpa [uval] using (by simpa [Polynomial.aeval_def] using bxroot)
  have allconj (ψ : L →+* ℂ) :
      ∃ σ : K →+* ℂ, σ b = ψ u := by
    have hr : Polynomial.aeval (ψ u) (minpoly ℚ b) = 0 := by
      rw [Polynomial.aeval_def]
      have he := Polynomial.hom_eval₂ (minpoly ℚ b) (algebraMap ℚ L) ψ u
      have hc : ψ.comp (algebraMap ℚ L) = (algebraMap ℚ ℂ) := by ext a; simp
      rw [← hc, ← he, ← Polynomial.aeval_def, uroot, map_zero]
    have hm : ψ u ∈ (minpoly ℚ b).rootSet ℂ :=
      (Polynomial.mem_rootSet_of_ne (minpoly.ne_zero (IsAlgebraic.isIntegral
        (Algebra.IsAlgebraic.isAlgebraic b)))).2 hr
    exact (NumberField.Embeddings.range_eval_eq_rootSet_minpoly K ℂ b).symm.subset hm
  have ynorm (ψ : L →+* ℂ) : ‖ψ y‖ ≤ (1:ℝ) := by
    have ⟨σ, hσ⟩ := allconj ψ
    apply le_of_eq
    have rel : (ψ y)^2 - (ψ u) * (ψ y) + 1 = 0 := by
      have hne : ψ y ≠ 0 := (map_ne_zero ψ).2 y0
      dsimp [u]
      simp only [map_add, map_inv₀]
      field_simp
      ring
    exact quadratic_on_unit_circle (ψ u) (ψ y)
      (by rw [← hσ]; exact br σ)
      (by rw [← hσ]; exact (NumberField.norm_embedding_le_house b σ).trans bh)
      ((map_ne_zero ψ).2 y0) rel
  obtain ⟨a, apos, ya⟩ :=
    NumberField.Embeddings.pow_eq_one_of_norm_le_one L ℂ y0 yint ynorm
  have za : z ^ a = 1 := by
    have h := congrArg (fun w : L => (w : ℂ)) ya
    simpa [y] using h
  obtain ⟨r, rpos, hzprim⟩ := IsPrimitiveRoot.exists_pos za (by omega)
  refine ⟨z, r, rpos, hzprim, ?_, ?_⟩
  · rw [zsum]
    exact hmax
  intro ξ hξ
  -- a primitive root of the same order is a conjugate of y
  have hyprim : IsPrimitiveRoot y r :=
    hzprim.of_map_of_injective (f := (ℚ⟮z⟯).val.toRingHom)
      ((ℚ⟮z⟯).val.toRingHom).injective
  have hroot : Polynomial.aeval ξ (minpoly ℚ y) = 0 := by
    rw [← Polynomial.cyclotomic_eq_minpoly_rat hyprim rpos,
        Polynomial.cyclotomic_eq_minpoly_rat hξ rpos]
    exact minpoly.aeval ℚ ξ
  have hm : ξ ∈ (minpoly ℚ y).rootSet ℂ :=
    (Polynomial.mem_rootSet_of_ne (minpoly.ne_zero
       (IsAlgebraic.isIntegral (Algebra.IsAlgebraic.isAlgebraic y)))).2 hroot
  obtain ⟨ψ, hψ⟩ :=
    (NumberField.Embeddings.range_eval_eq_rootSet_minpoly L ℂ y).symm.subset hm
  have ⟨σ, hσ⟩ := allconj ψ
  have hsum : ξ + ξ⁻¹ = σ b := calc
    _ = ψ y + (ψ y)⁻¹ := by rw [← hψ]
    _ = ψ u := by simp [u]
    _ = σ b := hσ.symm
  rw [hsum]
  exact NumberField.norm_embedding_le_house b σ

private lemma mynorm (x : ℝ) :
    ‖Complex.exp ((x:ℂ) * Complex.I) + (Complex.exp ((x:ℂ)*Complex.I))⁻¹‖
      = |2 * Real.cos x| := by
  have hinv : (Complex.exp ((x:ℂ)*Complex.I))⁻¹ =
      Complex.exp ((-(x):ℝ) * Complex.I) := by
    rw [← Complex.exp_neg]
    congr 1
    -- `norm_cast`?
    push_cast
    ring
  rw [hinv, Complex.exp_ofReal_mul_I, Complex.exp_ofReal_mul_I]
  -- x and -x
  rw [Real.cos_neg, Real.sin_neg]
  have heq : ((Real.cos x : ℂ) + (Real.sin x : ℂ) * Complex.I) +
      ((Real.cos x : ℂ) + ((- Real.sin x : ℝ) : ℂ) * Complex.I) =
      ((2 * Real.cos x : ℝ) : ℂ) := by
    push_cast
    ring
  rw [heq, Complex.norm_real, Real.norm_eq_abs]
private lemma exprewrite (k r : ℕ) :
  Complex.exp (2 * (Real.pi:ℂ) * Complex.I * ((k:ℂ)/(r:ℂ))) =
  Complex.exp ((((2*Real.pi*(k:ℝ)/(r:ℝ)):ℝ) : ℂ) * Complex.I) := by
  congr 1
  push_cast
  ring
private lemma ac_bound {d x : ℝ} (d0 : 0 ≤ d) (dpi : d ≤ Real.pi/2)
    (hx : (d ≤ x ∧ x ≤ Real.pi - d) ∨
      (Real.pi + d ≤ x ∧ x ≤ 2*Real.pi-d)) :
    |Real.cos x| ≤ Real.cos d := by
  have aux : ∀ y : ℝ, d ≤ y → y ≤ Real.pi - d →
      |Real.cos y| ≤ Real.cos d := by
    intro y h1 h2
    apply (abs_le).2
    constructor
    · have h := Real.cos_le_cos_of_nonneg_of_le_pi
          (show 0 ≤ y by linarith)
          (show Real.pi - d ≤ Real.pi by linarith) h2
      -- cos (pi-d) ≤ cos y
      rw [Real.cos_pi_sub] at h
      exact h
    · exact Real.cos_le_cos_of_nonneg_of_le_pi d0
          (show y ≤ Real.pi by linarith) h1
  rcases hx with hx | hx
  · exact aux x hx.1 hx.2
  · let y := 2*Real.pi - x
    have hy : d ≤ y ∧ y ≤ Real.pi - d := by
      dsimp [y]
      constructor <;> linarith
    have h := aux y hy.1 hy.2
    rwa [Real.cos_two_pi_sub] at h
private lemma even_core (s k : ℕ) (hs : 2 ≤ s) (hkpos : 0 < k)
    (hklt : k < 2*s) (hkne : k ≠ s) :
    |Real.cos (Real.pi * (k:ℝ) / (s:ℝ))| ≤ Real.cos (Real.pi / (s:ℝ)) := by
  have hsR : 0 < (s:ℝ) := by exact_mod_cast (lt_of_lt_of_le (by omega : 0<2) hs)
  have hp := Real.pi_pos
  let d : ℝ := Real.pi / (s:ℝ)
  let x : ℝ := Real.pi * (k:ℝ) / (s:ℝ)
  have d0 : 0 ≤ d := by dsimp [d]; positivity
  have dpi : d ≤ Real.pi/2 := by
    dsimp [d]
    apply div_le_div_of_nonneg_left (le_of_lt hp) (by norm_num : (0:ℝ)<2)
    exact_mod_cast hs
  apply ac_bound d0 dpi
  change (d ≤ x ∧ x ≤ Real.pi - d) ∨ (Real.pi + d ≤ x ∧ x ≤ 2*Real.pi - d)
  rcases lt_or_gt_of_ne hkne with hks | hks
  · left
    constructor
    · dsimp [d, x]
      apply div_le_div_of_nonneg_right ?_ (le_of_lt hsR)
      have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
      nlinarith
    · dsimp [d, x]
      apply (div_le_iff₀ hsR).2
      have heq : (Real.pi / (s:ℝ)) * (s:ℝ) = Real.pi := by field_simp
      rw [sub_mul, heq]
      have hkN : k + 1 ≤ s := by omega
      have hkR : (k:ℝ) + 1 ≤ (s:ℝ) := by exact_mod_cast hkN
      nlinarith
  · right
    constructor
    · dsimp [d, x]
      apply (le_div_iff₀ hsR).2
      have heq : (Real.pi / (s:ℝ)) * (s:ℝ) = Real.pi := by field_simp
      rw [add_mul, heq]
      have hkN : s+1 ≤ k := by omega
      have hkR : (s:ℝ) + 1 ≤ (k:ℝ) := by exact_mod_cast hkN
      nlinarith
    · dsimp [d, x]
      apply (div_le_iff₀ hsR).2
      have heq : (Real.pi / (s:ℝ)) * (s:ℝ) = Real.pi := by field_simp
      rw [sub_mul, heq]
      have hkN : k + 1 ≤ 2*s := by omega
      have hkR : (k:ℝ) + 1 ≤ 2*(s:ℝ) := by exact_mod_cast hkN
      nlinarith
private lemma odd_core (s k : ℕ) (hs : 1 ≤ s) (hkpos : 0 < k)
    (hklt : k < 2*s+1) :
    |Real.cos (2*Real.pi * (k:ℝ) / ( (2*s+1:ℕ):ℝ))| ≤
      Real.cos (Real.pi / ((2*s+1:ℕ):ℝ)) := by
  let N : ℕ := 2*s+1
  have hNpos : 0 < N := by dsimp [N]; omega
  have hNR : 0 < (N:ℝ) := by exact_mod_cast hNpos
  have heN : ((2*s+1:ℕ):ℝ) = (N:ℝ) := by rfl
  rw [heN]
  have hp := Real.pi_pos
  let d : ℝ := Real.pi / (N:ℝ)
  let x : ℝ := 2*Real.pi*(k:ℝ)/(N:ℝ)
  have d0 : 0 ≤ d := by dsimp [d]; positivity
  have dpi : d ≤ Real.pi/2 := by
    dsimp [d]
    apply div_le_div_of_nonneg_left (le_of_lt hp) (by norm_num : (0:ℝ)<2)
    have : 2 ≤ N := by dsimp [N]; omega
    exact_mod_cast this
  apply ac_bound d0 dpi
  change (d ≤ x ∧ x ≤ Real.pi-d) ∨ (Real.pi+d ≤ x ∧ x ≤ 2*Real.pi-d)
  by_cases hks : k ≤ s
  · left
    constructor
    · dsimp [d,x]
      apply (le_div_iff₀ hNR).2
      have heq : (Real.pi / (N:ℝ)) * (N:ℝ) = Real.pi := by field_simp
      -- inequality d*N <= 2π*k
      rw [heq]
      have hkR : (1:ℝ) ≤ (k:ℝ) := by exact_mod_cast hkpos
      nlinarith
    · dsimp [d,x]
      apply (div_le_iff₀ hNR).2
      have heq : (Real.pi / (N:ℝ)) * (N:ℝ) = Real.pi := by field_simp
      rw [sub_mul, heq]
      have hsR : (s:ℝ) ≥ (k:ℝ) := by exact_mod_cast hks
      have hNe : (N:ℝ) = 2*(s:ℝ)+1 := by dsimp [N]; push_cast; ring
      rw [hNe]
      nlinarith
  · right
    have hks' : s + 1 ≤ k := by omega
    constructor
    · dsimp [d,x]
      apply (le_div_iff₀ hNR).2
      have heq : (Real.pi / (N:ℝ)) * (N:ℝ) = Real.pi := by field_simp
      rw [add_mul, heq]
      have hkR : (s:ℝ)+1 ≤ (k:ℝ) := by exact_mod_cast hks'
      have hNe : (N:ℝ) = 2*(s:ℝ)+1 := by dsimp [N]; push_cast; ring
      rw [hNe]
      nlinarith
    · dsimp [d,x]
      apply (div_le_iff₀ hNR).2
      have heq : (Real.pi / (N:ℝ)) * (N:ℝ) = Real.pi := by field_simp
      -- (2*pi-d)*N
      rw [sub_mul, heq]
      have hkN : k + 1 ≤ N := by dsimp [N]; omega
      have hkR : (k:ℝ)+1 ≤ (N:ℝ) := by exact_mod_cast hkN
      nlinarith
private lemma scopr (s : ℕ) : Nat.Coprime s (2*s+1) := by
  have h1 : Nat.Coprime s (1+s) :=
    (Nat.coprime_add_self_right (m:=s) (n:=1)).2 (Nat.coprime_one_right s)
  have h1' : Nat.Coprime s (s+1) := by simpa [Nat.add_comm] using h1
  have h2 : Nat.Coprime s ((s+1)+s) :=
    (Nat.coprime_add_self_right (m:=s) (n:=s+1)).2 h1'
  convert h2 using 1 <;> omega
private lemma angle_even (s k : ℕ) (hs : 0 < s) :
    2*Real.pi*(k:ℝ)/(((2*s:ℕ):ℕ):ℝ) =
      Real.pi*(k:ℝ)/(s:ℝ) := by
  have hsR : (s:ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hs)
  push_cast
  field_simp
  try ring
private lemma angle_odd_s (s : ℕ) :
    2*Real.pi*(s:ℝ)/((2*s+1:ℕ):ℝ) =
      Real.pi - Real.pi/((2*s+1:ℕ):ℝ) := by
  have h : ((2*s+1:ℕ):ℝ) ≠ 0 := by exact_mod_cast (by omega : (2*s+1:ℕ) ≠ 0)
  push_cast
  field_simp
  try ring
private lemma prim_norm {r : ℕ} (hr : r ≠ 0) {w : ℂ}
    (hw : IsPrimitiveRoot w r) :
    ∃ k < r, k.Coprime r ∧
      ‖w + w⁻¹‖ = |2 * Real.cos (2*Real.pi*(k:ℝ)/(r:ℝ))| := by
  obtain ⟨k,hk,hc,he⟩ := (Complex.isPrimitiveRoot_iff w r hr).1 hw
  refine ⟨k,hk,hc,?_⟩
  rw [← he, exprewrite]
  apply mynorm
private lemma even_candidate (s : ℕ) (hs : 2 ≤ s) :
  let r : ℕ := 2*s
  let ξ : ℂ := Complex.exp (2*(Real.pi:ℂ)*Complex.I *
      (((1:ℕ):ℂ)/(r:ℂ)))
  IsPrimitiveRoot ξ r ∧
    ‖ξ + ξ⁻¹‖ = 2 * Real.cos (Real.pi/(s:ℝ)) := by
  dsimp
  constructor
  · apply Complex.isPrimitiveRoot_exp_of_coprime 1 (2*s) (by omega)
      (Nat.coprime_one_left (2*s))
  · rw [exprewrite]
    rw [mynorm]
    -- angle_even k=1
    rw [angle_even s 1 (by omega)]
    norm_num -- hopefully norm_num simplifies pi*1
    -- check goal
    have hd : Real.pi/(s:ℝ) ∈ Set.Icc (-(Real.pi/2)) (Real.pi/2) := by
      constructor
      · have h0 : 0 ≤ Real.pi/(s:ℝ) := by positivity
        have hp := Real.pi_pos
        nlinarith
      · apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos) (by norm_num : (0:ℝ)<2)
        exact_mod_cast hs
    have hc := Real.cos_nonneg_of_mem_Icc hd
    exact hc
private lemma odd_candidate (s : ℕ) (hs : 1 ≤ s) :
  let r : ℕ := 2*s+1
  let ξ : ℂ := Complex.exp (2*(Real.pi:ℂ)*Complex.I *
      ((s:ℂ)/(r:ℂ)))
  IsPrimitiveRoot ξ r ∧
    ‖ξ + ξ⁻¹‖ = 2 * Real.cos (Real.pi/(r:ℝ)) := by
  dsimp
  constructor
  · exact Complex.isPrimitiveRoot_exp_of_coprime s (2*s+1) (by omega) (scopr s)
  · rw [exprewrite]
    rw [mynorm]
    rw [angle_odd_s, Real.cos_pi_sub]
    have hC : 0 ≤ Real.cos (Real.pi / ((↑(2*s+1)) : ℝ)) := by
      apply Real.cos_nonneg_of_mem_Icc
      constructor
      · have h0 : 0 ≤ Real.pi / (((2*s+1:ℕ):ℝ)) := by positivity
        have hp := Real.pi_pos
        nlinarith
      · apply div_le_div_of_nonneg_left (le_of_lt Real.pi_pos)
          (by norm_num : (0:ℝ) < 2)
        exact_mod_cast (by omega : (2:ℕ) ≤ 2*s+1)
    -- goal with abs of 2 * - cos
    rw [mul_neg]
    -- | - (2*cos)|
    rw [abs_neg, abs_mul]
    norm_num
    have hCr : 0 ≤ Real.cos (Real.pi /(2*(s:ℝ)+1)) := by
      convert hC using 1 <;> push_cast <;> ring
    exact hCr
private lemma even_upper (s : ℕ) (hs : 2 ≤ s) {w : ℂ}
    (hw : IsPrimitiveRoot w (2*s)) :
    ‖w + w⁻¹‖ ≤ 2 * Real.cos (Real.pi/(s:ℝ)) := by
  have hr : (2*s:ℕ) ≠ 0 := by omega
  obtain ⟨k,hklt,hkc,hn⟩ := prim_norm hr hw
  rw [hn]
  rw [angle_even s k (by omega)]
  have hk0 : k ≠ 0 := by
    intro h
    subst k
    have hh : (2*s:ℕ) = 1 := (Nat.coprime_zero_left _).1 hkc
    omega
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hkne : k ≠ s := by
    intro h
    subst k
    have hh : s = 1 := Nat.Coprime.eq_one_of_dvd hkc (by exact ⟨2, by omega⟩)
    omega
  have hcore := even_core s k hs hkpos hklt hkne
  rw [abs_mul]
  norm_num
  linarith
private lemma odd_upper (s : ℕ) (hs : 1 ≤ s) {w : ℂ}
    (hw : IsPrimitiveRoot w (2*s+1)) :
    ‖w + w⁻¹‖ ≤ 2 * Real.cos (Real.pi/((2*s+1:ℕ):ℝ)) := by
  have hr : (2*s+1:ℕ) ≠ 0 := by omega
  obtain ⟨k,hklt,hkc,hn⟩ := prim_norm hr hw
  rw [hn]
  have hk0 : k ≠ 0 := by
    intro h; subst k
    have hh : (2*s+1:ℕ) = 1 := (Nat.coprime_zero_left _).1 hkc
    omega
  have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
  have hcore := odd_core s k hs hkpos hklt
  push_cast at hcore
  rw [abs_mul]
  norm_num
  linarith

/-ResultBegin-/

theorem cyclotomic_integer_house_le_two {K : Type*} [Field K] [NumberField K] [Algebra ℚ K]
    (n : ℕ) [NeZero n] [IsCyclotomicExtension {n} ℚ K] {β : K}
    (hβ_int : IsIntegral ℤ β)
    (hβ_real : β ∈ NumberField.maximalRealSubfield K) :
    house β ≤ 2 →
      house β = 2 ∨ ∃ m : ℕ, 0 < m ∧ house β = 2 * Real.cos (Real.pi / m) :=
/-ResultProofBegin-/by
  intro hb
  obtain ⟨z, r, rp, hz, hhouse, hbig⟩ :=
    primitive_data hβ_int hβ_real hb
  classical
  by_cases r1 : r = 1
  · left
    subst r
    have zz : z = 1 := by simpa using hz.pow_eq_one
    norm_num [zz] at hhouse ⊢
    exact hhouse
  by_cases r2 : r = 2
  · left
    subst r
    have zz : z = (1:ℂ) ∨ z = -1 := sq_eq_one_iff.mp hz.pow_eq_one
    rcases zz with zz|zz <;> norm_num [zz] at hhouse ⊢ <;> exact hhouse
  have r3 : 3 ≤ r := by omega
  right
  obtain ⟨s, hs | hs⟩ := Nat.even_or_odd' r
  · subst r
    have hs2 : 2 ≤ s := by omega
    refine ⟨s, by omega, ?_⟩
    have hu : ‖z + z⁻¹‖ ≤ 2 * Real.cos (Real.pi/(s:ℝ)) :=
      even_upper s hs2 hz
    have hc := even_candidate s hs2
    dsimp at hc
    rcases hc with ⟨hcP, hcN⟩
    have hl : 2 * Real.cos (Real.pi/(s:ℝ)) ≤ house β := by
      rw [← hcN]
      exact hbig _ hcP
    rw [hhouse] at hl
    calc
      house β = ‖z + z⁻¹‖ := hhouse
      _ = 2 * Real.cos (Real.pi/(s:ℝ)) := le_antisymm hu hl
  · subst r
    have hs1 : 1 ≤ s := by omega
    refine ⟨2*s+1, by omega, ?_⟩
    have hu : ‖z + z⁻¹‖ ≤ 2 * Real.cos (Real.pi/((2*s+1:ℕ):ℝ)) :=
      odd_upper s hs1 hz
    have hc := odd_candidate s hs1
    dsimp at hc
    rcases hc with ⟨hcP, hcN⟩
    have hl : 2 * Real.cos (Real.pi/((2*s+1:ℕ):ℝ)) ≤ house β := by
      rw [← hcN]
      exact hbig _ hcP
    rw [hhouse] at hl
    calc
      house β = ‖z + z⁻¹‖ := hhouse
      _ = 2 * Real.cos (Real.pi/((2*s+1:ℕ):ℝ)) := le_antisymm hu hl

/-ResultProofEnd-/
/-ResultEnd-/

end Submission
