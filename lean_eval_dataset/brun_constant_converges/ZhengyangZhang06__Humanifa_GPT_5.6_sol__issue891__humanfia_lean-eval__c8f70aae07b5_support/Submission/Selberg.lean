import Mathlib.Algebra.Order.Antidiag.Nat
import Mathlib.NumberTheory.SelbergSieve

open scoped ArithmeticFunction.Moebius ArithmeticFunction.omega BigOperators

open ArithmeticFunction Finset Nat Real

noncomputable section

namespace Submission.Selberg

private theorem lambdaSquared_eq_zero_of_support_wlog {w : ℕ → ℝ} {height : ℝ}
    (hw : ∀ d : ℕ, ¬(d : ℝ) ^ 2 ≤ height → w d = 0) {d : ℕ} (hd : ¬(d : ℝ) ≤ height)
    (d1 d2 : ℕ) (h : d = Nat.lcm d1 d2) (hle : d1 ≤ d2) :
    w d1 * w d2 = 0 := by
  rw [hw d2]
  · ring
  by_contra hyp
  apply hd
  apply le_trans _ hyp
  norm_cast
  calc
    d ≤ d1.lcm d2 := by rw [h]
    _ ≤ d1 * d2 := Nat.div_le_self _ _
    _ ≤ d2 ^ 2 := by rw [pow_two]; gcongr

theorem lambdaSquared_eq_zero_of_not_le_height (w : ℕ → ℝ) (height : ℝ)
    (hw : ∀ d : ℕ, ¬(d : ℝ) ^ 2 ≤ height → w d = 0) (d : ℕ) (hd : ¬(d : ℝ) ≤ height) :
    BoundingSieve.lambdaSquared w d = 0 := by
  simp only [BoundingSieve.lambdaSquared]
  by_cases hheight : 0 ≤ height
  swap
  · push Not at hd hheight
    have hw0 : ∀ d' : ℕ, w d' = 0 := by
      intro d'
      apply hw
      have : (0 : ℝ) ≤ (d' : ℝ) ^ 2 := sq_nonneg _
      linarith
    apply sum_eq_zero
    intro d1 _
    apply sum_eq_zero
    intro d2 _
    rw [hw0 d1, hw0 d2]
    simp
  apply sum_eq_zero
  intro d1 _
  apply sum_eq_zero
  intro d2 _
  split_ifs with h
  swap
  · rfl
  rcases Nat.le_or_le d1 d2 with hle | hle
  · exact lambdaSquared_eq_zero_of_support_wlog hw hd d1 d2 h hle
  · rw [mul_comm]
    exact lambdaSquared_eq_zero_of_support_wlog hw hd d2 d1 (Nat.lcm_comm d1 d2 ▸ h) hle

/-- The finite normalizing sum used by the Selberg upper-bound weights. -/
def boundingSum (s : SelbergSieve) : ℝ :=
  ∑ l ∈ divisors s.prodPrimes,
    if (l : ℝ) ^ 2 ≤ s.level then s.toBoundingSieve.selbergTerms l else 0

theorem boundingSum_pos (s : SelbergSieve) : 0 < boundingSum s := by
  rw [boundingSum, ← sum_filter]
  apply sum_pos
  · intro l hl
    rw [mem_filter, mem_divisors] at hl
    exact BoundingSieve.selbergTerms_pos hl.1.1
  · refine ⟨1, ?_⟩
    simp only [mem_filter]
    exact ⟨one_mem_divisors.mpr s.toBoundingSieve.prodPrimes_ne_zero, by simpa using s.one_le_level⟩

theorem boundingSum_ne_zero (s : SelbergSieve) : boundingSum s ≠ 0 :=
  ne_of_gt (boundingSum_pos s)

theorem boundingSum_nonneg (s : SelbergSieve) : 0 ≤ boundingSum s :=
  (boundingSum_pos s).le

/-- The optimal finite Selberg weights at the chosen level. -/
def weights (s : SelbergSieve) : ℕ → ℝ := fun d =>
  if d ∣ s.prodPrimes then
    (s.nu d)⁻¹ * s.toBoundingSieve.selbergTerms d * (μ d : ℝ) * (boundingSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then
          s.toBoundingSieve.selbergTerms m
        else 0
  else 0

theorem weights_eq_zero_of_not_dvd (s : SelbergSieve) {d : ℕ} (hd : ¬d ∣ s.prodPrimes) :
    weights s d = 0 := by
  rw [weights, if_neg hd]

theorem weights_eq_zero (s : SelbergSieve) (d : ℕ) (hd : ¬(d : ℝ) ^ 2 ≤ s.level) :
    weights s d = 0 := by
  simp only [weights]
  split_ifs with h
  · rw [mul_eq_zero_of_right]
    apply sum_eq_zero
    intro m hm
    rw [if_neg]
    intro hyp
    have hle : (d : ℝ) ^ 2 ≤ ((d * m : ℕ) : ℝ) ^ 2 := by
      norm_cast
      exact Nat.pow_le_pow_left (Nat.le_mul_of_pos_right d (Nat.pos_of_mem_divisors hm)) 2
    linarith [hyp.1]
  · rfl

theorem weights_mul_moebius_nonneg (s : SelbergSieve) (d : ℕ) (hdP : d ∣ s.prodPrimes) :
    0 ≤ weights s d * (μ d : ℝ) := by
  simp only [weights, if_pos hdP, mul_assoc]
  trans ((μ d : ℝ) ^ 2 * (s.nu d)⁻¹ * s.toBoundingSieve.selbergTerms d *
      (boundingSum s)⁻¹ *
      ∑ m ∈ divisors s.prodPrimes,
        if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then
          s.toBoundingSieve.selbergTerms m
        else 0)
  · apply mul_nonneg
    · positivity [boundingSum_nonneg s,
        BoundingSieve.nu_pos_of_dvd_prodPrimes hdP,
        BoundingSieve.selbergTerms_pos hdP]
    · apply sum_nonneg
      intro m hm
      split_ifs with h
      · exact (BoundingSieve.selbergTerms_pos <| dvd_of_mem_divisors hm).le
      · exact le_rfl
  · apply le_of_eq
    ring

private theorem divisors_image_mul (n d : ℕ) (hd : d ≠ 0) :
    n.divisors.image (d * ·) = (d * n).divisors.filter (fun k => d ∣ k) := by
  ext r
  simp only [mem_image, mem_divisors, ne_eq, mem_filter, mul_eq_zero, not_or]
  constructor
  · rintro ⟨x, ⟨hx, hn⟩, rfl⟩
    exact ⟨⟨Nat.mul_dvd_mul_left d hx, hd, hn⟩, d.dvd_mul_right x⟩
  · rintro ⟨⟨hrdn, hd', hn⟩, hdr⟩
    exact ⟨r / d, ⟨(div_dvd_iff_dvd_mul hdr (Nat.pos_of_ne_zero hd')).mpr hrdn, hn⟩,
      Nat.mul_div_cancel' hdr⟩

private lemma sum_mul_subst (k n : ℕ) {f : ℕ → ℝ}
    (h : ∀ l, l ∣ n → ¬k ∣ l → f l = 0) :
    ∑ l ∈ n.divisors, f l =
      ∑ m ∈ n.divisors, if k * m ∣ n then f (k * m) else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  by_cases hk : k = 0
  · simp [hk, hn] at h ⊢
    apply sum_eq_zero
    simp +contextual [mem_divisors, ne_zero_of_dvd_ne_zero hn, h]
  trans ∑ l ∈ image (fun x => k * x) n.divisors, if l ∣ n then f l else 0
  · rw [divisors_image_mul _ _ hk, ← sum_filter, filter_comm,
      divisors_filter_dvd_of_dvd, eq_comm]
    · apply sum_subset
      · exact filter_subset (fun k' => k ∣ k') n.divisors
      · simp only [mem_divisors, ne_eq, mem_filter, not_and, and_imp]
        intro l hl hn' h'
        exact h l hl (h' hl hn')
    · positivity
    · exact Nat.dvd_mul_left n k
  · rw [sum_image]
    intro _ _ _ _ heq
    exact (Nat.mul_right_inj hk).mp heq

private theorem weights_aux (s : SelbergSieve) (d : ℕ) (hd : d ∣ s.prodPrimes) :
    (∑ l ∈ divisors s.prodPrimes,
      if d ∣ l ∧ (l : ℝ) ^ 2 ≤ s.level then s.toBoundingSieve.selbergTerms l else 0) =
      s.toBoundingSieve.selbergTerms d *
        ∑ m ∈ divisors s.prodPrimes,
          if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then
            s.toBoundingSieve.selbergTerms m
          else 0 := by
  rw [sum_mul_subst d s.prodPrimes (by simp +contextual)]
  simp_rw [← sum_filter, mul_sum]
  apply sum_congr
  · ext m
    simp only [dvd_mul_right, Nat.cast_mul, true_and, mem_filter, mem_divisors, ne_eq,
      and_assoc, and_congr_right_iff]
    rw [and_comm, and_congr_right_iff]
    intro hmP hP _
    constructor
    · intro hdm
      exact Coprime.symm <| coprime_of_squarefree_mul <|
        s.prodPrimes_squarefree.squarefree_of_dvd hdm
    · intro hcop
      exact Coprime.mul_dvd_of_dvd_of_dvd hcop.symm hd hmP
  · intro m hm
    simp only [mem_filter, mem_divisors, ne_eq] at hm
    exact BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime hm.2.2.symm

theorem nu_mul_weights_eq_dvds_sum (s : SelbergSieve) (d : ℕ) :
    s.nu d * weights s d =
      (boundingSum s)⁻¹ * (μ d : ℝ) *
        ∑ l ∈ divisors s.prodPrimes,
          if d ∣ l ∧ (l : ℝ) ^ 2 ≤ s.level then s.toBoundingSieve.selbergTerms l else 0 := by
  by_cases hd : d ∣ s.prodPrimes
  swap
  · rw [weights_eq_zero_of_not_dvd s hd]
    rw [sum_eq_zero]
    · ring
    intro l hl
    rw [mem_divisors] at hl
    rw [if_neg]
    intro h
    exact hd (h.1.trans hl.1)
  rw [weights, if_pos hd]
  repeat rw [mul_sum]
  symm
  simp_rw [← mul_sum, weights_aux s d hd, ← mul_assoc]
  rw [mul_inv_cancel₀ (BoundingSieve.nu_ne_zero hd)]
  ring

private theorem moebius_inv_dvd_lower_bound (l m : ℕ) (hm : Squarefree m) :
    (∑ d ∈ m.divisors, if l ∣ d then μ d else 0) = if l = m then μ l else 0 := by
  have hm_pos : 0 < m := Nat.pos_of_ne_zero hm.ne_zero
  revert hm
  revert m
  apply (ArithmeticFunction.sum_eq_iff_sum_smul_moebius_eq_on {n | Squarefree n}
    (fun _ _ => Squarefree.squarefree_of_dvd)).mpr
  intro m hm_pos hm
  change Squarefree m at hm
  rw [sum_divisorsAntidiagonal' (f := fun r s => μ r • if l = s then μ l else 0)]
  by_cases hl : l ∣ m
  · rw [if_pos hl, sum_eq_single l]
    · have hmul : m / l * l = m := Nat.div_mul_cancel hl
      rw [if_pos rfl, smul_eq_mul, ← isMultiplicative_moebius.map_mul_of_coprime, hmul]
      exact coprime_of_squarefree_mul (hmul.symm ▸ hm)
    · intro d _ hdl
      rw [if_neg hdl.symm, smul_zero]
    · intro h
      rw [mem_divisors] at h
      exact (h ⟨hl, (Nat.ne_of_lt hm_pos).symm⟩).elim
  · rw [if_neg hl, sum_eq_zero]
    intro d hd
    rw [if_neg, smul_zero]
    intro h
    rw [← h] at hd
    exact hl (dvd_of_mem_divisors hd)

theorem weights_diagonalisation (s : SelbergSieve) (l : ℕ)
    (hl : l ∈ divisors s.prodPrimes) :
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * weights s d else 0) =
      if (l : ℝ) ^ 2 ≤ s.level then
        s.toBoundingSieve.selbergTerms l * (μ l : ℝ) * (boundingSum s)⁻¹
      else 0 := by
  calc
    (∑ d ∈ divisors s.prodPrimes, if l ∣ d then s.nu d * weights s d else 0) =
        ∑ k ∈ divisors s.prodPrimes,
          if (k : ℝ) ^ 2 ≤ s.level then
            (∑ d ∈ divisors s.prodPrimes,
              if d ∣ k ∧ l ∣ d then (μ d : ℝ) else 0) *
                s.toBoundingSieve.selbergTerms k * (boundingSum s)⁻¹
          else 0 := by
      simp_rw [nu_mul_weights_eq_dvds_sum, ← sum_filter, mul_sum, sum_mul, sum_filter,
        ite_sum_zero, ← ite_and]
      rw [sum_comm]
      congr with d
      simp_rw [← sum_filter]
      apply sum_congr
      · ext x
        simp only [mem_filter]
        tauto
      · intro x hx
        ring
    _ = ∑ x ∈ divisors s.prodPrimes,
        if x = l then
          if (l : ℝ) ^ 2 ≤ s.level then
            s.toBoundingSieve.selbergTerms l * (μ l : ℝ) * (boundingSum s)⁻¹
          else 0
        else 0 := by
      apply sum_congr rfl
      intro k hk
      norm_cast
      simp_rw [ite_and, ← sum_filter,
        divisors_filter_dvd_of_dvd s.toBoundingSieve.prodPrimes_ne_zero
          (dvd_of_mem_divisors hk),
        sum_filter]
      rw [moebius_inv_dvd_lower_bound _ _
        (s.toBoundingSieve.squarefree_of_mem_divisors_prodPrimes hk)]
      push_cast
      rw [← ite_and, ite_zero_mul, ite_zero_mul, ← ite_and]
      apply if_ctx_congr _ _ fun _ => rfl
      · rw [and_comm, eq_comm]
        refine and_congr_right fun heq => ?_
        rw [heq]
      · intro h
        rw [h.1]
        ring
    _ = _ := by
      rw [sum_ite_eq_of_mem' _ _ _ hl]

/-- The upper-Moebius coefficients obtained from the finite Selberg weights. -/
def muPlus (s : SelbergSieve) : ℕ → ℝ :=
  BoundingSieve.lambdaSquared (weights s)

theorem weights_one (s : SelbergSieve) : weights s 1 = 1 := by
  rw [weights, if_pos (one_dvd s.prodPrimes)]
  simp only [s.nu_mult.map_one, BoundingSieve.selbergTerms_isMultiplicative.map_one,
    inv_one, mul_one, isUnit_one, IsUnit.squarefree, moebius_apply_of_squarefree,
    cardFactors_one, pow_zero, Int.cast_one]
  rw [show (∑ m ∈ divisors s.prodPrimes,
      if ((1 * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime 1 then
        s.toBoundingSieve.selbergTerms m
      else 0) = boundingSum s by simp [boundingSum]]
  simpa only [one_mul] using inv_mul_cancel₀ (boundingSum_ne_zero s)

theorem muPlus_eq_zero (s : SelbergSieve) (d : ℕ) (hd : ¬(d : ℝ) ≤ s.level) :
    muPlus s d = 0 := by
  apply lambdaSquared_eq_zero_of_not_le_height _ s.level _ d hd
  exact weights_eq_zero s

theorem upperMoebius_muPlus (s : SelbergSieve) :
    BoundingSieve.IsUpperMoebius (muPlus s) :=
  BoundingSieve.upperMoebius_lambdaSquared (weights s) (weights_one s)

theorem mainSum_muPlus (s : SelbergSieve) :
    s.toBoundingSieve.mainSum (muPlus s) = (boundingSum s)⁻¹ := by
  trans ∑ l ∈ divisors s.prodPrimes,
      if (l : ℝ) ^ 2 ≤ s.level then
        s.toBoundingSieve.selbergTerms l * (boundingSum s)⁻¹ ^ 2
      else 0
  · rw [muPlus, BoundingSieve.mainSum_lambdaSquared_eq_sum_mul_sum_sq]
    apply sum_congr rfl
    intro l hl
    rw [weights_diagonalisation s l hl, ite_pow, zero_pow, mul_ite_zero]
    · congr 1
      trans (s.toBoundingSieve.selbergTerms l)⁻¹ *
          s.toBoundingSieve.selbergTerms l * s.toBoundingSieve.selbergTerms l *
            (μ l : ℝ) ^ 2 * (boundingSum s)⁻¹ ^ 2
      · ring
      rw_mod_cast [moebius_sq_eq_one_of_squarefree
        (s.toBoundingSieve.squarefree_of_mem_divisors_prodPrimes hl)]
      rw [inv_mul_cancel₀ (ne_of_gt <| BoundingSieve.selbergTerms_pos <|
        dvd_of_mem_divisors hl)]
      ring
    · norm_num
  · rw [← sum_filter, ← sum_mul, sum_filter, ← boundingSum, pow_two, ← mul_assoc,
      mul_inv_cancel₀ (boundingSum_ne_zero s), one_mul]

private theorem eq_gcd_mul_of_dvd_of_coprime {k d m : ℕ} (hkd : k ∣ d)
    (hmd : Coprime m d) (hk : k ≠ 0) :
    k = d.gcd (k * m) := by
  rcases hkd with ⟨r, rfl⟩
  have hrdvd : r ∣ k * r := by use k; rw [mul_comm]
  symm
  rw [Nat.gcd_mul_left, mul_eq_left₀ hk, Nat.gcd_comm]
  exact Coprime.coprime_dvd_right hrdvd hmd

private theorem cutoff_factorization (s : SelbergSieve) {k d m : ℕ} (hkd : k ∣ d)
    (hk : k ∈ divisors s.prodPrimes) (hm : m ∈ divisors s.prodPrimes) :
    k * m ∣ s.prodPrimes ∧ k = Nat.gcd d (k * m) ∧
        (((k * m : ℕ) : ℝ) ^ 2 ≤ s.level) ↔
      (((k * m : ℕ) : ℝ) ^ 2 ≤ s.level) ∧ Coprime m d := by
  constructor
  · intro h
    refine ⟨h.2.2, ?_⟩
    rcases hkd with ⟨r, rfl⟩
    rw [Nat.gcd_mul_left, eq_comm, mul_eq_left₀ (by rintro rfl; simp at hk)] at h
    rw [Nat.coprime_mul_iff_right]
    exact ⟨(coprime_of_squarefree_mul <|
      s.prodPrimes_squarefree.squarefree_of_dvd h.1).symm,
      by simpa [Nat.Coprime, Nat.gcd_comm] using h.2.1⟩
  · intro h
    refine ⟨?_, ?_, h.1⟩
    · apply Nat.Coprime.mul_dvd_of_dvd_of_dvd
      · exact (Coprime.symm h.2).coprime_dvd_left hkd
      · exact dvd_of_mem_divisors hk
      · exact dvd_of_mem_divisors hm
    · exact eq_gcd_mul_of_dvd_of_coprime hkd h.2 (by rintro rfl; simp at hk)

theorem boundingSum_ge (s : SelbergSieve) {d : ℕ} (hdP : d ∣ s.prodPrimes) :
    boundingSum s ≥ weights s d * (μ d : ℝ) * boundingSum s := by
  calc
    boundingSum s =
        ∑ k ∈ divisors s.prodPrimes, ∑ l ∈ divisors s.prodPrimes,
          if k = d.gcd l ∧ (l : ℝ) ^ 2 ≤ s.level then
            s.toBoundingSieve.selbergTerms l
          else 0 := by
      rw [boundingSum, sum_comm]
      apply sum_congr rfl
      intro l hl
      simp_rw [ite_and]
      rw [sum_ite_eq_of_mem']
      rw [mem_divisors]
      exact ⟨(Nat.gcd_dvd_left d l).trans hdP, s.toBoundingSieve.prodPrimes_ne_zero⟩
    _ = ∑ k ∈ divisors s.prodPrimes,
        if k ∣ d then
          s.toBoundingSieve.selbergTerms k *
            ∑ m ∈ divisors s.prodPrimes,
              if ((k * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then
                s.toBoundingSieve.selbergTerms m
              else 0
        else 0 := by
      apply sum_congr rfl
      intro k hk
      rw [mul_sum]
      split_ifs with hkd
      swap
      · rw [sum_eq_zero]
        intro l _
        rw [if_neg]
        push Not
        intro h
        exfalso
        rw [h] at hkd
        exact hkd (Nat.gcd_dvd_left d l)
      rw [sum_mul_subst k s.prodPrimes, sum_congr rfl]
      · intro m hm
        rw [mul_ite_zero, ← ite_and]
        apply if_ctx_congr _ _ fun _ => rfl
        · exact_mod_cast cutoff_factorization s hkd hk hm
        · intro h
          exact BoundingSieve.selbergTerms_isMultiplicative.map_mul_of_coprime <|
            h.2.symm.coprime_dvd_left hkd
      · intro l _ hkl
        rw [if_neg]
        push Not
        intro h
        exfalso
        rw [h] at hkl
        exact hkl (Nat.gcd_dvd_right d l)
    _ ≥ ∑ k ∈ divisors s.prodPrimes,
        if k ∣ d then
          s.toBoundingSieve.selbergTerms k *
            ∑ m ∈ divisors s.prodPrimes,
              if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then
                s.toBoundingSieve.selbergTerms m
              else 0
        else 0 := by
      apply sum_le_sum
      intro k hk
      split_ifs with hkd
      swap
      · rfl
      gcongr with m hm
      · exact (BoundingSieve.selbergTerms_pos <| hkd.trans hdP).le
      · split_ifs with h h'
        · rfl
        · exfalso
          apply h'
          refine ⟨le_trans ?_ h.1, h.2⟩
          gcongr
          exact Nat.le_of_dvd
            (Nat.pos_of_ne_zero <| ne_zero_of_dvd_ne_zero
              s.toBoundingSieve.prodPrimes_ne_zero hdP) hkd
        · exact (BoundingSieve.selbergTerms_pos <| dvd_of_mem_divisors hm).le
        · rfl
    _ = weights s d * (μ d : ℝ) * boundingSum s := by
      simp_rw [← ite_zero_mul, ← sum_mul,
        BoundingSieve.sum_divisors_selbergTerms_eq_selbergTerms_mul_nu_inv hdP]
      trans boundingSum s * (boundingSum s)⁻¹ * (μ d : ℝ) ^ 2 * (s.nu d)⁻¹ *
          s.toBoundingSieve.selbergTerms d *
            ∑ m ∈ divisors s.prodPrimes,
              if ((d * m : ℕ) : ℝ) ^ 2 ≤ s.level ∧ m.Coprime d then
                s.toBoundingSieve.selbergTerms m
              else 0
      · rw [mul_inv_cancel₀ (boundingSum_ne_zero s), ← Int.cast_pow,
          moebius_sq_eq_one_of_squarefree
            (s.prodPrimes_squarefree.squarefree_of_dvd hdP)]
        ring
      · rw [weights, if_pos hdP]
        ring

theorem abs_weights_le_one (s : SelbergSieve) (d : ℕ) : |weights s d| ≤ 1 := by
  by_cases hdP : d ∣ s.prodPrimes
  swap
  · rw [weights_eq_zero_of_not_dvd s hdP]
    norm_num
  have h := boundingSum_ge s hdP
  have hmul : weights s d * (μ d : ℝ) ≤ 1 := by
    apply le_of_mul_le_mul_of_pos_right (by simpa only [one_mul] using h) (boundingSum_pos s)
  convert hmul using 1
  rw [← abs_of_nonneg (weights_mul_moebius_nonneg s d hdP), abs_mul,
    ← Int.cast_abs, abs_moebius_eq_one_of_squarefree
      (s.prodPrimes_squarefree.squarefree_of_dvd hdP),
    Int.cast_one, mul_one]

theorem abs_muPlus_le (s : SelbergSieve) (n : ℕ) (hn : n ∈ divisors s.prodPrimes) :
    |muPlus s n| ≤ (3 : ℝ) ^ ω n := by
  let f : ℕ → ℕ → ℝ := fun x z => if n = x.lcm z then 1 else 0
  rw [muPlus, BoundingSieve.lambdaSquared]
  calc
    |∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
        if n = d1.lcm d2 then weights s d1 * weights s d2 else 0| ≤
        ∑ d1 ∈ n.divisors,
          |∑ d2 ∈ n.divisors,
            if n = d1.lcm d2 then weights s d1 * weights s d2 else 0| :=
      abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors,
        |if n = d1.lcm d2 then weights s d1 * weights s d2 else 0| := by
      gcongr
      exact abs_sum_le_sum_abs _ _
    _ ≤ ∑ d1 ∈ n.divisors, ∑ d2 ∈ n.divisors, f d1 d2 := by
      gcongr with d1 hd1 d2 hd2
      rw [apply_ite abs, abs_zero, abs_mul]
      simp only [f]
      by_cases h : n = d1.lcm d2
      · rw [if_pos h, if_pos h]
        exact mul_le_one₀ (abs_weights_le_one s d1) (abs_nonneg _) (abs_weights_le_one s d2)
      · rw [if_neg h, if_neg h]
    _ = (n.divisors ×ˢ n.divisors).sum fun p => f p.1 p.2 := by
      rw [← sum_product']
    _ = #((n.divisors ×ˢ n.divisors).filter fun p : ℕ × ℕ => n = p.1.lcm p.2) := by
      simp [f]
    _ = (3 : ℕ) ^ ω n := by
      norm_cast
      simpa [eq_comm] using Nat.card_pair_lcm_eq
        (s.toBoundingSieve.squarefree_of_mem_divisors_prodPrimes hn)
    _ = (3 : ℝ) ^ ω n := by norm_num

theorem errSum_muPlus_le (s : SelbergSieve) :
    s.toBoundingSieve.errSum (muPlus s) ≤
      ∑ d ∈ divisors s.prodPrimes,
        if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.toBoundingSieve.rem d| else 0 := by
  rw [BoundingSieve.errSum]
  gcongr with d hd
  split_ifs with h
  · apply mul_le_mul (abs_muPlus_le s d hd) le_rfl (abs_nonneg _) (pow_nonneg (by norm_num) _)
  · rw [muPlus_eq_zero s d h, abs_zero, zero_mul]

/-- The fundamental finite Selberg upper-bound inequality. -/
theorem bound (s : SelbergSieve) :
    s.toBoundingSieve.siftedSum ≤
      s.totalMass / boundingSum s +
        ∑ d ∈ divisors s.prodPrimes,
          if (d : ℝ) ≤ s.level then (3 : ℝ) ^ ω d * |s.toBoundingSieve.rem d| else 0 := by
  calc
    s.toBoundingSieve.siftedSum ≤
        s.totalMass * s.toBoundingSieve.mainSum (muPlus s) +
          s.toBoundingSieve.errSum (muPlus s) :=
      BoundingSieve.siftedSum_le_mainSum_errSum_of_upperMoebius _ (upperMoebius_muPlus s)
    _ ≤ _ := by
      gcongr
      · rw [mainSum_muPlus, div_eq_mul_inv]
      · exact errSum_muPlus_le s

end Submission.Selberg
