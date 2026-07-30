import ChallengeDeps

/-! Helper lemmas for the Landsberg–Schaar relation. -/

open Complex Real Finset Filter Topology

noncomputable section

namespace Submission.Helpers

lemma norm_jacobiTheta₂_sub_one_le_of_im_eq_zero {z τ : ℂ} (hz : z.im = 0)
    (hτ : 0 < τ.im) :
    ‖jacobiTheta₂ z τ - 1‖ ≤
      2 / (1 - Real.exp (-π * τ.im)) * Real.exp (-π * τ.im) := by
  let f : ℤ → ℂ := fun n ↦ jacobiTheta₂_term n z τ
  have hf (n : ℤ) :
      ‖f n‖ ≤ Real.exp (-π * τ.im) ^ n.natAbs := by
    have h := norm_exp_mul_sq_le hτ n
    rw [Complex.norm_exp] at h
    have hre : (π * I * (n : ℂ) ^ 2 * τ).re = -π * τ.im * (n : ℝ) ^ 2 := by
      rw [(by push_cast; ring :
        (π * I * (n : ℂ) ^ 2 * τ) = (π * (n : ℝ) ^ 2 : ℝ) * (τ * I)),
        re_ofReal_mul, mul_I_re]
      ring
    rw [hre] at h
    change ‖jacobiTheta₂_term n z τ‖ ≤ _
    rw [norm_jacobiTheta₂_term, hz, mul_zero, sub_zero]
    simpa only [mul_assoc, mul_comm, mul_left_comm] using h
  have hs : HasSum
      (fun n : ℕ ↦ f (n + 1) + f (-(n + 1))) (jacobiTheta₂ z τ - 1) := by
    have h := (hasSum_jacobiTheta₂_term z hτ).nat_add_neg
    rw [← hasSum_nat_add_iff' 1] at h
    simpa [f, jacobiTheta₂_term] using h
  have hnorm : Summable fun n : ℕ ↦ ‖f (n + 1) + f (-(n + 1))‖ :=
    hs.summable.norm
  have hle (n : ℕ) :
      ‖f (n + 1) + f (-(n + 1))‖ ≤
        2 * Real.exp (-π * τ.im) ^ (n + 1) := by
    have hpos := hf (↑n + 1)
    have hneg := hf (-(↑n + 1))
    rw [show (↑n + 1 : ℤ) = ↑(n + 1) by omega, Int.natAbs_natCast] at hpos
    rw [Int.natAbs_neg, show (↑n + 1 : ℤ) = ↑(n + 1) by omega,
      Int.natAbs_natCast] at hneg
    calc
      ‖f (n + 1) + f (-(n + 1))‖ ≤ ‖f (n + 1)‖ + ‖f (-(n + 1))‖ := norm_add_le ..
      _ ≤ Real.exp (-π * τ.im) ^ (n + 1) +
          Real.exp (-π * τ.im) ^ (n + 1) := add_le_add hpos hneg
      _ = 2 * Real.exp (-π * τ.im) ^ (n + 1) := by ring
  have hgeom : HasSum (fun n : ℕ ↦ Real.exp (-π * τ.im) ^ (n + 1))
      (Real.exp (-π * τ.im) / (1 - Real.exp (-π * τ.im))) := by
    simp_rw [pow_succ', div_eq_mul_inv,
      hasSum_mul_left_iff (Real.exp_ne_zero (-π * τ.im))]
    exact hasSum_geometric_of_lt_one (Real.exp_pos _).le
      (Real.exp_lt_one_iff.mpr (mul_neg_of_neg_of_pos (neg_lt_zero.mpr pi_pos) hτ))
  have hgeom₂ : HasSum (fun n : ℕ ↦ 2 * Real.exp (-π * τ.im) ^ (n + 1))
      (2 / (1 - Real.exp (-π * τ.im)) * Real.exp (-π * τ.im)) := by
    simpa only [div_eq_mul_inv, mul_assoc, mul_comm, mul_left_comm] using hgeom.mul_left 2
  rw [← hs.tsum_eq]
  exact (norm_tsum_le_tsum_norm hnorm).trans
    ((hnorm.tsum_mono hgeom₂.summable hle).trans_eq hgeom₂.tsum_eq)

lemma tendsto_jacobiTheta₂_one_of_im_tendsto_atTop {α : Type*} {l : Filter α}
    {z : ℂ} (hz : z.im = 0) {τ : α → ℂ}
    (hτ : Tendsto (fun x ↦ (τ x).im) l atTop) :
    Tendsto (fun x ↦ jacobiTheta₂ z (τ x)) l (𝓝 1) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  have he : Tendsto (fun x ↦ Real.exp (-π * (τ x).im)) l (𝓝 0) :=
    tendsto_exp_atBot.comp (hτ.const_mul_atTop_of_neg (neg_lt_zero.mpr pi_pos))
  have hb : Tendsto
      (fun x ↦ 2 / (1 - Real.exp (-π * (τ x).im)) * Real.exp (-π * (τ x).im))
      l (𝓝 0) := by
    have hone : Tendsto (fun x ↦ (1 : ℝ) - Real.exp (-π * (τ x).im)) l (𝓝 1) := by
      simpa using (tendsto_const_nhds.sub he)
    have hquot : Tendsto
        (fun x ↦ (2 : ℝ) / (1 - Real.exp (-π * (τ x).im))) l (𝓝 (2 / 1)) :=
      tendsto_const_nhds.div hone (by norm_num)
    simpa using hquot.mul he
  refine squeeze_zero' (Eventually.of_forall fun _ ↦ norm_nonneg _)
    ?_ hb
  filter_upwards [hτ.eventually (eventually_gt_atTop 0)] with x hx
  exact norm_jacobiTheta₂_sub_one_le_of_im_eq_zero hz hx

lemma scaled_shifted_gaussian_eq (N : ℕ) (hN : 0 < N) (z : ℂ) (hz : 0 < z.re)
    (r : Fin N) :
    (z * (N : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
        (∑' k : ℤ, Complex.exp (-π * z * ((N : ℂ) * k + (r : ℂ)) ^ 2)) =
      jacobiTheta₂ ((r : ℂ) / N) (I / (z * (N : ℂ) ^ 2)) := by
  let A : ℂ := z * (N : ℂ) ^ 2
  let u : ℂ := I * z * N * r
  let t : ℂ := I * z * (N : ℂ) ^ 2
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hz0 : z ≠ 0 := ne_of_apply_ne re hz.ne'
  have hA : A ≠ 0 := mul_ne_zero hz0 (pow_ne_zero 2 hNc)
  have hsqrt : A ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, Complex.cpow_eq_zero_iff]
    simp [hA]
  have hsum :
      (∑' k : ℤ, Complex.exp (-π * z * ((N : ℂ) * k + (r : ℂ)) ^ 2)) =
        Complex.exp (-π * z * (r : ℂ) ^ 2) * jacobiTheta₂ u t := by
    rw [jacobiTheta₂, ← tsum_mul_left]
    congr 1 with k
    rw [jacobiTheta₂_term, ← Complex.exp_add]
    congr 1
    simp only [u, t]
    ring_nf
    simp [I_sq, sub_eq_add_neg]
  rw [hsum, jacobiTheta₂_functional_equation]
  have hbase : -I * t = A := by
    simp only [t, A]
    ring_nf
    simp [I_sq]
  have hquot : u / t = (r : ℂ) / N := by
    simp only [u, t]
    field_simp [hz0, hNc]
  have hinv : -1 / t = I / A := by
    simp only [t, A]
    field_simp [hz0, hNc]
    rw [I_sq]
  have hexp : -π * I * u ^ 2 / t = π * z * (r : ℂ) ^ 2 := by
    simp only [u, t]
    field_simp [hz0, hNc]
    rw [I_sq]
    ring
  rw [hbase, hquot, hinv, hexp]
  change A ^ (1 / 2 : ℂ) *
      (Complex.exp (-π * z * (r : ℂ) ^ 2) *
        (1 / A ^ (1 / 2 : ℂ) * Complex.exp (π * z * (r : ℂ) ^ 2) *
          jacobiTheta₂ ((r : ℂ) / N) (I / A))) =
    jacobiTheta₂ ((r : ℂ) / N) (I / A)
  field_simp [hsqrt]
  rw [← Complex.exp_add]
  ring_nf
  simp

noncomputable def quadraticSum (a : ℤ) (N : ℕ) : ℂ :=
  ∑ r : Fin N, Complex.exp (π * I * (r : ℂ) ^ 2 * (a : ℂ) / (N : ℂ))

lemma jacobiTheta_eq_residue_sum (a : ℤ) (N : ℕ) (hN : 0 < N)
    (hEven : Even (a * (N : ℤ))) (z : ℂ) (hz : 0 < z.re) :
    jacobiTheta ((a : ℂ) / N + I * z) =
      ∑ r : Fin N,
        Complex.exp (π * I * (r : ℂ) ^ 2 * (a : ℂ) / (N : ℂ)) *
          ∑' k : ℤ, Complex.exp (-π * z * ((N : ℂ) * k + (r : ℂ)) ^ 2) := by
  letI : NeZero N := ⟨hN.ne'⟩
  let τ : ℂ := (a : ℂ) / N + I * z
  let e : Fin N × ℤ ≃ ℤ :=
    (Equiv.prodComm (Fin N) ℤ).trans (Int.divModEquiv N).symm
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hτ : τ.im = z.re := by
    simp [τ, div_im, normSq]
  have hs : Summable (fun n : ℤ ↦ jacobiTheta₂_term n 0 τ) :=
    (summable_jacobiTheta₂_term_iff 0 τ).mpr (hτ.symm ▸ hz)
  have hse : Summable (fun p : Fin N × ℤ ↦ jacobiTheta₂_term (e p) 0 τ) :=
    hs.comp_injective e.injective
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta₂]
  change (∑' n : ℤ, jacobiTheta₂_term n 0 τ) = _
  rw [← e.tsum_eq, hse.tsum_prod, tsum_fintype]
  apply Finset.sum_congr rfl
  intro r _
  rw [← tsum_mul_left]
  apply tsum_congr
  intro k
  obtain ⟨c, hc⟩ := hEven
  have hcC : (a : ℂ) * (N : ℂ) = (c : ℂ) + c := by exact_mod_cast hc
  have he_apply : e (r, k) = k * N + r := by
    simp [e, Int.divModEquiv_symm_apply]
  rw [he_apply, jacobiTheta₂_term]
  have hexponent :
      2 * π * I * (k * (N : ℤ) + (r : ℤ)) * 0 +
          π * I * (k * (N : ℤ) + (r : ℤ)) ^ 2 * τ =
        π * I * (r : ℂ) ^ 2 * (a : ℂ) / (N : ℂ) +
          (-π * z * ((N : ℂ) * k + (r : ℂ)) ^ 2) +
          ((c * k ^ 2 + a * k * (r : ℤ) : ℤ) : ℂ) * (2 * π * I) := by
    simp only [τ]
    field_simp [hNc]
    ring_nf
    simp only [I_sq, one_mul, neg_mul, sub_eq_add_neg] at *
    ring_nf
    push_cast
    linear_combination (I * (k : ℂ) ^ 2 * (N : ℂ)) * hcC
  simp only [Int.cast_natCast] at hexponent
  push_cast
  rw [hexponent, Complex.exp_add, Complex.exp_add,
    Complex.exp_int_mul_two_pi_mul_I, mul_one]

lemma scaled_jacobiTheta_eq_sum (a : ℤ) (N : ℕ) (hN : 0 < N)
    (hEven : Even (a * (N : ℤ))) (z : ℂ) (hz : 0 < z.re) :
    (z * (N : ℂ) ^ 2) ^ (1 / 2 : ℂ) * jacobiTheta ((a : ℂ) / N + I * z) =
      ∑ r : Fin N,
        Complex.exp (π * I * (r : ℂ) ^ 2 * (a : ℂ) / (N : ℂ)) *
          jacobiTheta₂ ((r : ℂ) / N) (I / (z * (N : ℂ) ^ 2)) := by
  rw [jacobiTheta_eq_residue_sum a N hN hEven z hz, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  rw [show (z * (N : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
      (Complex.exp (π * I * (r : ℂ) ^ 2 * (a : ℂ) / (N : ℂ)) *
        ∑' k : ℤ, Complex.exp (-π * z * ((N : ℂ) * k + (r : ℂ)) ^ 2)) =
      Complex.exp (π * I * (r : ℂ) ^ 2 * (a : ℂ) / (N : ℂ)) *
        ((z * (N : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
          ∑' k : ℤ, Complex.exp (-π * z * ((N : ℂ) * k + (r : ℂ)) ^ 2)) by ring]
  rw [scaled_shifted_gaussian_eq N hN z hz r]

lemma tendsto_scaled_jacobiTheta (a : ℤ) (N : ℕ) (hN : 0 < N)
    (hEven : Even (a * (N : ℤ))) {α : Type*} {l : Filter α} (z : α → ℂ)
    (hz : ∀ x, 0 < (z x).re)
    (hinv : Tendsto (fun x ↦ (I / (z x * (N : ℂ) ^ 2)).im) l atTop) :
    Tendsto
      (fun x ↦ (z x * (N : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
        jacobiTheta ((a : ℂ) / N + I * z x)) l
      (𝓝 (quadraticSum a N)) := by
  have hsum : Tendsto
      (fun x ↦ ∑ r : Fin N,
        Complex.exp (π * I * (r : ℂ) ^ 2 * (a : ℂ) / (N : ℂ)) *
          jacobiTheta₂ ((r : ℂ) / N) (I / (z x * (N : ℂ) ^ 2))) l
      (𝓝 (quadraticSum a N)) := by
    rw [quadraticSum]
    apply tendsto_finsetSum
    intro r _
    have ht := tendsto_jacobiTheta₂_one_of_im_tendsto_atTop
      (z := (r : ℂ) / N) (τ := fun x ↦ I / (z x * (N : ℂ) ^ 2)) (by simp) hinv
    simpa using tendsto_const_nhds.mul ht
  apply hsum.congr'
  exact Eventually.of_forall fun x ↦ (scaled_jacobiTheta_eq_sum a N hN hEven (z x) (hz x)).symm

lemma ofReal_mul_cpow (s : ℝ) (hs : 0 < s) (x : ℂ) (hx : x ≠ 0) (r : ℂ) :
    ((s : ℂ) * x) ^ r = (s : ℂ) ^ r * x ^ r := by
  rw [Complex.cpow_def_of_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne') hx),
    Complex.log_ofReal_mul hs hx, add_mul, Complex.exp_add,
    Complex.ofReal_log hs.le,
    ← Complex.cpow_def_of_ne_zero (Complex.ofReal_ne_zero.mpr hs.ne'),
    ← Complex.cpow_def_of_ne_zero hx]

lemma exp_pi_div_four_mul_sqrt_neg_I :
    Complex.exp ((π : ℂ) * I / 4) * Complex.sqrt (-I) = 1 := by
  rw [show (π : ℂ) * I / 4 = ((π / 4 : ℝ) : ℂ) * I by push_cast; ring,
    Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin,
    Real.cos_pi_div_four, Real.sin_pi_div_four,
    Complex.sqrt_neg_I]
  have hs : √(2 : ℝ) ≠ 0 := by positivity
  have hsprod : √(2 : ℝ) * √(1 / 2 : ℝ) = 1 := by
    rw [← Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 2)]
    norm_num
  have hsprodC : (√(2 : ℝ) : ℂ) * (√(1 / 2 : ℝ) : ℂ) = 1 := by exact_mod_cast hsprod
  push_cast
  field_simp [hs]
  ring_nf
  rw [I_sq]
  linear_combination 2 * hsprodC

lemma jacobiTheta_neg_inv (τ : ℂ) (hτ : 0 < τ.im) :
    jacobiTheta (-1 / τ) = (-I * τ) ^ (1 / 2 : ℂ) * jacobiTheta τ := by
  have hτ0 : τ ≠ 0 := ne_of_apply_ne im (zero_im.symm ▸ hτ.ne')
  have hroot : (-I * τ) ^ (1 / 2 : ℂ) ≠ 0 := by
    rw [Ne, cpow_eq_zero_iff, not_and_or]
    exact Or.inl (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hτ0)
  rw [jacobiTheta_eq_jacobiTheta₂, jacobiTheta_eq_jacobiTheta₂,
    jacobiTheta₂_functional_equation 0 τ]
  simp only [zero_pow two_ne_zero, mul_zero, zero_div, Complex.exp_zero, mul_one, one_div]
  field_simp [hroot]

lemma quadraticSum_reciprocity_core (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hEven : Even ((M : ℤ) * (N : ℤ))) :
    quadraticSum (-(N : ℤ)) M =
      (-I * ((M : ℂ) / (N : ℂ))) ^ (1 / 2 : ℂ) * quadraticSum (M : ℤ) N := by
  let s : ℕ → ℝ := fun n ↦ 1 / ((n : ℝ) + 1)
  let z : ℕ → ℂ := fun n ↦ (s n : ℂ)
  let L : ℂ := -I * (M : ℂ) / (N : ℂ)
  let B : ℕ → ℂ := fun n ↦ z n + L
  let w : ℕ → ℂ := fun n ↦ (B n)⁻¹ - I * (N : ℂ) / (M : ℂ)
  let R : ℕ → ℂ := fun n ↦ L / B n
  let τ : ℕ → ℂ := fun n ↦ (M : ℂ) / (N : ℂ) + I * z n
  have hMc : (M : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hM.ne'
  have hNc : (N : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hN.ne'
  have hspos (n : ℕ) : 0 < s n := by simp only [s]; positivity
  have hzpos (n : ℕ) : 0 < (z n).re := by simpa [z] using hspos n
  have hLne : L ≠ 0 := by
    simp only [L]
    exact div_ne_zero (mul_ne_zero (neg_ne_zero.mpr I_ne_zero) hMc) hNc
  have hBpos (n : ℕ) : 0 < (B n).re := by
    simpa [B, L, z] using hspos n
  have hBne (n : ℕ) : B n ≠ 0 := ne_of_apply_ne re (hBpos n).ne'
  have hwpos (n : ℕ) : 0 < (w n).re := by
    have hnorm : 0 < normSq (B n) := normSq_pos.mpr (hBne n)
    simpa [w, inv_re] using div_pos (hBpos n) hnorm
  have hEven' : Even ((-(N : ℤ)) * (M : ℤ)) := by
    simpa [mul_comm] using hEven.neg
  have hs0 : Tendsto s atTop (𝓝 0) := by
    simpa [s] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hz0 : Tendsto z atTop (𝓝 0) := by
    simpa [z] using hs0.ofReal
  have hB : Tendsto B atTop (𝓝 L) := by
    simpa [B] using hz0.add (tendsto_const_nhds (x := L))
  have hR : Tendsto R atTop (𝓝 1) := by
    have hdiv : Tendsto (fun n ↦ L / B n) atTop (𝓝 (L / L)) :=
      (tendsto_const_nhds (x := L)).div hB hLne
    simpa [R, div_self hLne] using hdiv
  have hRhalf : Tendsto (fun n ↦ (R n) ^ (1 / 2 : ℂ)) atTop (𝓝 1) := by
    simpa using hR.cpow tendsto_const_nhds (Or.inl (by norm_num))
  have hLim : L.im ≠ 0 := by
    have hmn : 0 < (M : ℝ) / (N : ℝ) := div_pos (Nat.cast_pos.mpr hM) (Nat.cast_pos.mpr hN)
    simpa [L, div_im, normSq] using hmn.ne'
  have hBhalf : Tendsto (fun n ↦ (B n) ^ (1 / 2 : ℂ)) atTop
      (𝓝 (L ^ (1 / 2 : ℂ))) :=
    hB.cpow tendsto_const_nhds (Or.inr hLim)
  have hC : Tendsto (fun n ↦ (R n) ^ (1 / 2 : ℂ) * (B n) ^ (1 / 2 : ℂ)) atTop
      (𝓝 (L ^ (1 / 2 : ℂ))) := by simpa using hRhalf.mul hBhalf
  have hT : Tendsto (fun n : ℕ ↦ ((n : ℝ) + 1) / (N : ℝ) ^ 2) atTop atTop := by
    exact Tendsto.atTop_div_const (sq_pos_of_pos (Nat.cast_pos.mpr hN))
      (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
  have hinv_z_eq (n : ℕ) :
      (I / (z n * (N : ℂ) ^ 2)).im = ((n : ℝ) + 1) / (N : ℝ) ^ 2 := by
    let t : ℝ := ((n : ℝ) + 1) / (N : ℝ) ^ 2
    have hn : ((n : ℝ) + 1) ≠ 0 := by positivity
    have hfull : I / (z n * (N : ℂ) ^ 2) = I * (t : ℂ) := by
      simp only [z, s]
      simp only [t]
      push_cast
      field_simp [hNc, hn]
    rw [hfull]
    simp only [mul_im, I_re, ofReal_im, I_im, ofReal_re, zero_mul, one_mul]
    simp only [zero_add, t]
  have hinv_z : Tendsto (fun n ↦ (I / (z n * (N : ℂ) ^ 2)).im) atTop atTop := by
    simpa only [hinv_z_eq] using hT
  have hwB (n : ℕ) : w n * B n = -I * (N : ℂ) * z n / (M : ℂ) := by
    simp only [w]
    field_simp [hMc, hBne n]
    simp only [B, L]
    field_simp [hNc]
    ring_nf
    simp [I_sq]
  have hwne (n : ℕ) : w n ≠ 0 := ne_of_apply_ne re (hwpos n).ne'
  have hwfull (n : ℕ) :
      I / (w n * (M : ℂ) ^ 2) = -B n / ((M : ℂ) * (N : ℂ) * z n) := by
    have hz_ne : z n ≠ 0 := by
      simpa [z] using Complex.ofReal_ne_zero.mpr (hspos n).ne'
    have hleft : w n * (M : ℂ) ^ 2 ≠ 0 :=
      mul_ne_zero (hwne n) (pow_ne_zero _ hMc)
    have hright : (M : ℂ) * (N : ℂ) * z n ≠ 0 :=
      mul_ne_zero (mul_ne_zero hMc hNc) hz_ne
    apply (div_eq_div_iff hleft hright).2
    rw [show -B n * (w n * (M : ℂ) ^ 2) =
      -(M : ℂ) ^ 2 * (w n * B n) by ring, hwB n]
    field_simp [hMc]
  have hinv_w_eq (n : ℕ) :
      (I / (w n * (M : ℂ) ^ 2)).im = ((n : ℝ) + 1) / (N : ℝ) ^ 2 := by
    rw [hwfull]
    simp [B, L, z, s, div_im, normSq]
    field_simp
  have hinv_w : Tendsto (fun n ↦ (I / (w n * (M : ℂ) ^ 2)).im) atTop atTop := by
    simpa only [hinv_w_eq] using hT
  have hF := tendsto_scaled_jacobiTheta (M : ℤ) N hN hEven z hzpos hinv_z
  have hG := tendsto_scaled_jacobiTheta (-(N : ℤ)) M hM hEven' w hwpos hinv_w
  have hbase (n : ℕ) : -I * τ n = B n := by
    simp only [τ, B, L]
    field_simp [hNc]
    ring_nf
    simp [I_sq]
  have hτim (n : ℕ) : 0 < (τ n).im := by simpa [τ] using hzpos n
  have hnegInv (n : ℕ) :
      -1 / τ n = -(N : ℂ) / (M : ℂ) + I * w n := by
    have hτne : τ n ≠ 0 := by
      intro hzero
      apply hBne n
      rw [← hbase n, hzero]
      simp
    have hright : -(N : ℂ) / (M : ℂ) + I * w n = I * (B n)⁻¹ := by
      simp only [w]
      field_simp [hMc]
      ring_nf
      simp [I_sq]
    rw [hright, ← hbase n]
    field_simp [hτne]
  have hscale (n : ℕ) :
      w n * (M : ℂ) ^ 2 = ((s n * (N : ℝ) ^ 2 : ℝ) : ℂ) * R n := by
    have hRB : R n * B n = L := by
      rw [show R n = L / B n by rfl, div_mul_cancel₀ _ (hBne n)]
    apply mul_right_cancel₀ (hBne n)
    rw [show (w n * (M : ℂ) ^ 2) * B n = (M : ℂ) ^ 2 * (w n * B n) by ring,
      hwB n,
      show (((s n * (N : ℝ) ^ 2 : ℝ) : ℂ) * R n) * B n =
        ((s n * (N : ℝ) ^ 2 : ℝ) : ℂ) * (R n * B n) by ring,
      hRB]
    simp only [L, z]
    push_cast
    field_simp [hMc, hNc]
  have hRne (n : ℕ) : R n ≠ 0 := div_ne_zero hLne (hBne n)
  have hrel (n : ℕ) :
      (w n * (M : ℂ) ^ 2) ^ (1 / 2 : ℂ) *
          jacobiTheta (-(N : ℂ) / (M : ℂ) + I * w n) =
        ((R n) ^ (1 / 2 : ℂ) * (B n) ^ (1 / 2 : ℂ)) *
          ((z n * (N : ℂ) ^ 2) ^ (1 / 2 : ℂ) * jacobiTheta (τ n)) := by
    rw [← hnegInv n, jacobiTheta_neg_inv (τ n) (hτim n), hbase n, hscale n,
      ofReal_mul_cpow _ (mul_pos (hspos n) (sq_pos_of_pos (Nat.cast_pos.mpr hN)))
        _ (hRne n) (1 / 2 : ℂ)]
    have hzN : (((s n * (N : ℝ) ^ 2 : ℝ) : ℂ)) = z n * (N : ℂ) ^ 2 := by
      simp [z]
    rw [hzN]
    ring
  have hprod := hC.mul hF
  have hG' : Tendsto
      (fun n ↦ ((R n) ^ (1 / 2 : ℂ) * (B n) ^ (1 / 2 : ℂ)) *
        ((z n * (N : ℂ) ^ 2) ^ (1 / 2 : ℂ) * jacobiTheta (τ n))) atTop
      (𝓝 (quadraticSum (-(N : ℤ)) M)) := by
    apply hG.congr'
    exact Eventually.of_forall fun n ↦ by simpa using hrel n
  have h := tendsto_nhds_unique hG' hprod
  rw [← mul_div_assoc]
  exact h

lemma cpow_neg_I_mul_nat_ratio (M N : ℕ) (hM : 0 < M) (hN : 0 < N) :
    (-I * ((M : ℂ) / (N : ℂ))) ^ (1 / 2 : ℂ) =
      ((√((M : ℝ) / (N : ℝ)) : ℝ) : ℂ) * Complex.sqrt (-I) := by
  have hs : 0 < (M : ℝ) / (N : ℝ) :=
    div_pos (Nat.cast_pos.mpr hM) (Nat.cast_pos.mpr hN)
  rw [show -I * ((M : ℂ) / (N : ℂ)) =
      (((M : ℝ) / (N : ℝ) : ℝ) : ℂ) * -I by push_cast; ring,
    ofReal_mul_cpow _ hs _ (neg_ne_zero.mpr I_ne_zero) (1 / 2 : ℂ)]
  congr 1
  · rw [Real.sqrt_eq_rpow, Complex.ofReal_cpow hs.le]
    norm_num
  · norm_num [Complex.sqrt]

lemma quadraticSum_reciprocity (M N : ℕ) (hM : 0 < M) (hN : 0 < N)
    (hEven : Even ((M : ℤ) * (N : ℤ))) :
    ((√(N : ℝ) : ℝ) : ℂ)⁻¹ * quadraticSum (M : ℤ) N =
      Complex.exp ((π : ℂ) * I / 4) * ((√(M : ℝ) : ℝ) : ℂ)⁻¹ *
        quadraticSum (-(N : ℤ)) M := by
  rw [quadraticSum_reciprocity_core M N hM hN hEven,
    cpow_neg_I_mul_nat_ratio M N hM hN,
    Real.sqrt_div (Nat.cast_nonneg M)]
  have hsm : ((√(M : ℝ) : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (Real.sqrt_pos.2 (Nat.cast_pos.mpr hM)).ne'
  push_cast
  rw [show Complex.exp ((π : ℂ) * I / 4) * ((√(M : ℝ) : ℝ) : ℂ)⁻¹ *
      ((((√(M : ℝ) : ℝ) : ℂ) / ((√(N : ℝ) : ℝ) : ℂ)) *
        Complex.sqrt (-I) * quadraticSum (M : ℤ) N) =
      (Complex.exp ((π : ℂ) * I / 4) * Complex.sqrt (-I)) *
        (((√(M : ℝ) : ℝ) : ℂ)⁻¹ * ((√(M : ℝ) : ℝ) : ℂ)) *
          (((√(N : ℝ) : ℝ) : ℂ)⁻¹ * quadraticSum (M : ℤ) N) by ring,
    exp_pi_div_four_mul_sqrt_neg_I, inv_mul_cancel₀ hsm]
  ring

open LeanEval.NumberTheory.LandsbergSchaar

lemma gaussS_eq_quadraticSum (a : ℤ) (N : ℕ) :
    gaussS a N = ((√(N : ℝ) : ℝ) : ℂ)⁻¹ * quadraticSum a N := by
  rw [gaussS, quadraticSum]
  congr 1
  calc
    ∑ x ∈ Finset.range N,
        Complex.exp ((π : ℂ) * I * ((x : ℂ) ^ 2 * (a : ℂ) / (N : ℂ))) =
      ∑ x ∈ Finset.range N,
        Complex.exp ((π : ℂ) * I * (x : ℂ) ^ 2 * (a : ℂ) / (N : ℂ)) := by
      apply Finset.sum_congr rfl
      intro x _
      congr 1
      ring
    _ = ∑ r : Fin N,
        Complex.exp ((π : ℂ) * I * (r : ℂ) ^ 2 * (a : ℂ) / (N : ℂ)) := by
      symm
      simpa using Fin.sum_univ_eq_sum_range
        (fun x : ℕ ↦ Complex.exp ((π : ℂ) * I * (x : ℂ) ^ 2 * (a : ℂ) / (N : ℂ))) N

theorem landsberg_schaar_aux (p q : ℕ) (hp : Odd p) (hq : Odd q) :
    gaussS (2 * q : ℕ) p =
      Complex.exp ((Real.pi : ℂ) * Complex.I / 4) * gaussS (-(p : ℤ)) (2 * q) := by
  have hp_pos : 0 < p := hp.pos
  have hq_pos : 0 < q := hq.pos
  have htwoq_pos : 0 < 2 * q := Nat.mul_pos (by norm_num) hq_pos
  have hEven : Even (((2 * q : ℕ) : ℤ) * (p : ℤ)) := by
    refine ⟨(q : ℤ) * (p : ℤ), ?_⟩
    push_cast
    ring
  rw [gaussS_eq_quadraticSum, gaussS_eq_quadraticSum]
  simpa only [mul_assoc] using
    quadraticSum_reciprocity (2 * q) p htwoq_pos hp_pos hEven

end Submission.Helpers
