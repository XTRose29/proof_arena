import Submission.Scalar

namespace LeanEval.Analysis

noncomputable section

/-- A bounded Pexider equation on a group has no nonconstant one-variable
part.  Boundedness is used only along the powers of a single group element. -/
lemma pexider_left_eq_const_of_bounded
    {G : Type*} [Group G] (A E D : G → ℝ)
    (hpex : ∀ p q, A q + E (p * q) = D p)
    (M : ℝ) (hA : ∀ q, |A q| ≤ M) :
    ∀ q, A q = A 1 := by
  have hadd (p q : G) :
      A 1 - A (p * q) = (A 1 - A p) + (A 1 - A q) := by
    have hpq := hpex p q
    have hp := hpex 1 p
    have hpq' := hpex 1 (p * q)
    have hp1 := hpex p 1
    rw [one_mul] at hp hpq'
    rw [mul_one] at hp1
    linarith
  intro q
  have hpow (n : ℕ) :
      A 1 - A (q ^ ((2 : ℕ) ^ n)) =
        (2 : ℝ) ^ n * (A 1 - A q) := by
    induction n with
    | zero => simp
    | succ n ih =>
        rw [pow_succ, pow_mul, pow_two, hadd, ih]
        rw [pow_succ]
        ring
  have hbound (n : ℕ) :
      |(2 : ℝ) ^ n * (A 1 - A q)| ≤ 2 * M := by
    rw [← hpow]
    calc
      |A 1 - A (q ^ ((2 : ℕ) ^ n))| ≤
          |A 1| + |A (q ^ ((2 : ℕ) ^ n))| := abs_sub _ _
      _ ≤ 2 * M := by
        linarith [hA 1, hA (q ^ ((2 : ℕ) ^ n))]
  have hz := eq_zero_of_abs_two_pow_mul_le (A 1 - A q) (2 * M) hbound
  linarith

/-- Cyclically permute three complex coordinates, sending `(x₀,x₁,x₂)` to
`(x₂,x₀,x₁)`. -/
def cycleCoordinates3
    (x : EuclideanSpace ℂ (Fin 3)) : EuclideanSpace ℂ (Fin 3) :=
  WithLp.toLp 2 ![x 2, x 0, x 1]

@[simp] lemma cycleCoordinates3_apply_zero
    (x : EuclideanSpace ℂ (Fin 3)) : cycleCoordinates3 x 0 = x 2 := by
  simp [cycleCoordinates3]

@[simp] lemma cycleCoordinates3_apply_one
    (x : EuclideanSpace ℂ (Fin 3)) : cycleCoordinates3 x 1 = x 0 := by
  simp [cycleCoordinates3]

@[simp] lemma cycleCoordinates3_apply_two
    (x : EuclideanSpace ℂ (Fin 3)) : cycleCoordinates3 x 2 = x 1 := by
  simp [cycleCoordinates3]

lemma inner_cycleCoordinates3
    (x y : EuclideanSpace ℂ (Fin 3)) :
    inner ℂ (cycleCoordinates3 x) (cycleCoordinates3 y) = inner ℂ x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp [cycleCoordinates3, Fin.sum_univ_succ]
  ring

lemma orthonormal_cycleCoordinates3
    (d : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3))) :
    Orthonormal ℂ (fun j ↦ cycleCoordinates3 (d j)) := by
  rw [orthonormal_iff_ite]
  intro i j
  rw [inner_cycleCoordinates3]
  exact orthonormal_iff_ite.mp d.orthonormal i j

lemma FrameFunction.sum_signResidual3_orthonormal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    (e : OrthonormalBasis (Fin 3) ℂ K)
    (d : Fin 3 → EuclideanSpace ℂ (Fin 3))
    (hd : Orthonormal ℂ d) :
    ∑ j : Fin 3,
        signResidual3 f.homogeneousValue
          ((d j 0) • (e 0 : H))
          ((d j 1) • (e 1 : H))
          ((d j 2) • (e 2 : H)) = 0 := by
  classical
  have hcard :
      Fintype.card (Fin 3) =
        Module.finrank ℂ (EuclideanSpace ℂ (Fin 3)) := by
    simp
  let b₀ : Module.Basis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) :=
    basisOfOrthonormalOfCardEqFinrank hd hcard
  have hb₀ :
      (b₀ : Fin 3 → EuclideanSpace ℂ (Fin 3)) = d :=
    coe_basisOfOrthonormalOfCardEqFinrank hd hcard
  let b : OrthonormalBasis (Fin 3) ℂ (EuclideanSpace ℂ (Fin 3)) :=
    b₀.toOrthonormalBasis (by simpa [hb₀] using hd)
  have hb :
      (b : Fin 3 → EuclideanSpace ℂ (Fin 3)) = d := by
    simpa only [b, Module.Basis.coe_toOrthonormalBasis] using hb₀
  simpa only [hb] using f.sum_signResidual3_orthonormalBasis K e b

lemma exists_orthonormalBasis_span_fin3
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (v : Fin 3 → H) (hv : Orthonormal ℂ v) :
    ∃ (K : Submodule ℂ H) (e : OrthonormalBasis (Fin 3) ℂ K),
      ∀ i, (e i : H) = v i := by
  classical
  let K : Submodule ℂ H := Submodule.span ℂ (Set.range v)
  let w : Fin 3 → K :=
    fun i ↦ ⟨v i, Submodule.subset_span (Set.mem_range_self i)⟩
  have hw : Orthonormal ℂ w := by
    rw [orthonormal_iff_ite]
    intro i j
    exact orthonormal_iff_ite.mp hv i j
  have hcard : Fintype.card (Fin 3) = Module.finrank ℂ K := by
    change Fintype.card (Fin 3) =
      Module.finrank ℂ (Submodule.span ℂ (Set.range v))
    rw [finrank_span_eq_card hv.linearIndependent]
  let b₀ : Module.Basis (Fin 3) ℂ K :=
    basisOfOrthonormalOfCardEqFinrank hw hcard
  have hb₀ : (b₀ : Fin 3 → K) = w :=
    coe_basisOfOrthonormalOfCardEqFinrank hw hcard
  let e : OrthonormalBasis (Fin 3) ℂ K :=
    b₀.toOrthonormalBasis (by simpa [hb₀] using hw)
  have he : (e : Fin 3 → K) = w := by
    simpa only [e, Module.Basis.coe_toOrthonormalBasis] using hb₀
  refine ⟨K, e, ?_⟩
  intro i
  simp [he, w]

lemma FrameFunction.signResidual3_of_orthogonal_norm_add_first
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (f : FrameFunction H) {x y z : H}
    (hxy : inner ℂ x y = 0) (hxz : inner ℂ x z = 0)
    (hyz : inner ℂ y z = 0)
    (hnorm : ‖x‖ ^ 2 = ‖y‖ ^ 2 + ‖z‖ ^ 2) :
    signResidual3 f.homogeneousValue x y z =
      quadraticDefect f.homogeneousValue y z / 2 := by
  rw [signResidual3_swap_first_two f.homogeneousValue
    f.homogeneousValue_neg]
  exact f.signResidual3_of_orthogonal_norm_add
    (inner_eq_zero_symm.mp hxy) hyz hxz hnorm

lemma FrameFunction.signResidual3_of_orthogonal_norm_add_last
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (f : FrameFunction H) {x y z : H}
    (hxy : inner ℂ x y = 0) (hxz : inner ℂ x z = 0)
    (hyz : inner ℂ y z = 0)
    (hnorm : ‖z‖ ^ 2 = ‖x‖ ^ 2 + ‖y‖ ^ 2) :
    signResidual3 f.homogeneousValue x y z =
      quadraticDefect f.homogeneousValue x y / 2 := by
  rw [signResidual3_swap_last_two]
  exact f.signResidual3_of_orthogonal_norm_add
    hxz hxy (inner_eq_zero_symm.mp hyz) hnorm

lemma FrameFunction.balanced_edge_phase_orbit
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    (e : OrthonormalBasis (Fin 3) ℂ K)
    {a b c : ℝ}
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c)
    (ha₁ : a ≤ 1 / 2) (hb₁ : b ≤ 1 / 2) (hc₁ : c ≤ 1 / 2)
    (hsum : a + b + c = 1) :
    ∃ u v : ℂ,
      ‖u‖ ^ 2 = b / 2 ∧ ‖v‖ ^ 2 = (1 - b) / 2 ∧
      ∀ z : Circle,
        quadraticDefect f.homogeneousValue
            (((z : ℂ) * u) • (e 1 : H)) (v • (e 2 : H)) =
          quadraticDefect f.homogeneousValue
            (u • (e 1 : H)) (v • (e 2 : H)) := by
  classical
  obtain ⟨d, hd0, hd10, hd11, hd12, hd20, hd21, hd22⟩ :=
    exists_balanced_coefficient_basis ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ hsum
  obtain ⟨d', hd'0, hd'10, hd'11, hd'12, hd'20, hd'21, hd'22⟩ :=
    exists_balanced_coefficient_basis hb₀ hc₀ ha₀ hb₁ hc₁ ha₁ (by linarith)
  let dcyc : Fin 3 → EuclideanSpace ℂ (Fin 3) :=
    fun j ↦ cycleCoordinates3 (d' j)
  have hdcyc : Orthonormal ℂ dcyc := by
    simpa only [dcyc] using orthonormal_cycleCoordinates3 d'
  have hfirst : d 0 = dcyc 0 := by
    rw [hd0]
    simp only [dcyc, hd'0]
    ext i
    fin_cases i <;> simp [cycleCoordinates3]
  have hdc10 : ‖dcyc 1 0‖ ^ 2 = (1 - c) / 2 := by
    simpa [dcyc] using hd'12
  have hdc11 : ‖dcyc 1 1‖ ^ 2 = 1 / 2 := by
    simpa [dcyc] using hd'10
  have hdc12 : ‖dcyc 1 2‖ ^ 2 = c / 2 := by
    simpa [dcyc] using hd'11
  have hdc20 : ‖dcyc 2 0‖ ^ 2 = (1 - b) / 2 := by
    simpa [dcyc] using hd'22
  have hdc21 : ‖dcyc 2 1‖ ^ 2 = b / 2 := by
    simpa [dcyc] using hd'20
  have hdc22 : ‖dcyc 2 2‖ ^ 2 = 1 / 2 := by
    simpa [dcyc] using hd'21
  have hunit (z : Circle) :
      starRingEnd ℂ (z : ℂ) * (z : ℂ) = 1 := by
    calc
      _ = (Complex.normSq (z : ℂ) : ℂ) :=
        (Complex.normSq_eq_conj_mul_self (z := (z : ℂ))).symm
      _ = 1 := by rw [Circle.normSq_coe]; norm_num
  let A : Circle → ℝ := fun z ↦
    quadraticDefect f.homogeneousValue
      (((z : ℂ) * d 1 1) • (e 1 : H)) ((d 1 2) • (e 2 : H))
  let B : Circle → ℝ := fun z ↦
    quadraticDefect f.homogeneousValue
      (((z : ℂ) * d 2 0) • (e 0 : H)) ((d 2 2) • (e 2 : H))
  let C : Circle → ℝ := fun z ↦
    quadraticDefect f.homogeneousValue
      (((z : ℂ) * dcyc 1 0) • (e 0 : H))
      ((dcyc 1 2) • (e 2 : H))
  let D : Circle → ℝ := fun z ↦
    quadraticDefect f.homogeneousValue
      (((z : ℂ) * dcyc 2 0) • (e 0 : H))
      ((dcyc 2 1) • (e 1 : H))
  have heorth (i j : Fin 3) (hij : i ≠ j) :
      inner ℂ (e i : H) (e j : H) = 0 := by
    change inner ℂ (e i) (e j) = 0
    rw [orthonormal_iff_ite.mp e.orthonormal i j, if_neg hij]
  have henorm (i : Fin 3) : ‖(e i : H)‖ = 1 := by
    change ‖e i‖ = 1
    exact e.norm_eq_one i
  have horth (i j : Fin 3) (hij : i ≠ j) (x y : ℂ) :
      inner ℂ (x • (e i : H)) (y • (e j : H)) = 0 := by
    simp only [inner_smul_left, inner_smul_right, heorth i j hij, mul_zero]
  have hpex (p q : Circle) : A q + (B (p * q) - C (p * q)) = D p := by
    let s : Fin 3 → ℂ := ![((p * q : Circle) : ℂ), (q : ℂ), 1]
    have hs (i : Fin 3) : starRingEnd ℂ (s i) * s i = 1 := by
      fin_cases i
      · simpa [s] using hunit (p * q)
      · simpa [s] using hunit q
      · simp [s]
    let dt : Fin 3 → EuclideanSpace ℂ (Fin 3) :=
      fun j ↦ coordinateTwist3 s (d j)
    let dct : Fin 3 → EuclideanSpace ℂ (Fin 3) :=
      fun j ↦ coordinateTwist3 s (dcyc j)
    have hdt : Orthonormal ℂ dt := by
      rw [orthonormal_iff_ite]
      intro i j
      simp only [dt]
      rw [inner_coordinateTwist3 s hs]
      exact orthonormal_iff_ite.mp d.orthonormal i j
    have hdct : Orthonormal ℂ dct := by
      rw [orthonormal_iff_ite]
      intro i j
      simp only [dct]
      rw [inner_coordinateTwist3 s hs]
      exact orthonormal_iff_ite.mp hdcyc i j
    have hsumd := f.sum_signResidual3_orthonormal K e dt hdt
    have hsumdc := f.sum_signResidual3_orthonormal K e dct hdct
    have hrow0 :
        signResidual3 f.homogeneousValue
            ((dt 0 0) • (e 0 : H)) ((dt 0 1) • (e 1 : H))
              ((dt 0 2) • (e 2 : H)) =
          signResidual3 f.homogeneousValue
            ((dct 0 0) • (e 0 : H)) ((dct 0 1) • (e 1 : H))
              ((dct 0 2) • (e 2 : H)) := by
      rw [show dt 0 = dct 0 by simp only [dt, dct, hfirst]]
    have htrade :
        signResidual3 f.homogeneousValue
              ((dt 1 0) • (e 0 : H)) ((dt 1 1) • (e 1 : H))
                ((dt 1 2) • (e 2 : H)) +
            signResidual3 f.homogeneousValue
              ((dt 2 0) • (e 0 : H)) ((dt 2 1) • (e 1 : H))
                ((dt 2 2) • (e 2 : H)) =
          signResidual3 f.homogeneousValue
              ((dct 1 0) • (e 0 : H)) ((dct 1 1) • (e 1 : H))
                ((dct 1 2) • (e 2 : H)) +
            signResidual3 f.homogeneousValue
              ((dct 2 0) • (e 0 : H)) ((dct 2 1) • (e 1 : H))
                ((dct 2 2) • (e 2 : H)) := by
      simp [Fin.sum_univ_succ] at hsumd hsumdc
      rw [hrow0] at hsumd
      linarith
    have hnorm_dt (j i : Fin 3) : ‖dt j i‖ = ‖d j i‖ := by
      simp only [dt, coordinateTwist3, norm_mul]
      rw [show ‖s i‖ = 1 by
        fin_cases i <;> simp [s]]
      simp
    have hnorm_dct (j i : Fin 3) : ‖dct j i‖ = ‖dcyc j i‖ := by
      simp only [dct, coordinateTwist3, norm_mul]
      rw [show ‖s i‖ = 1 by
        fin_cases i <;> simp [s]]
      simp
    have hr1 :
        signResidual3 f.homogeneousValue
            ((dt 1 0) • (e 0 : H)) ((dt 1 1) • (e 1 : H))
              ((dt 1 2) • (e 2 : H)) = A q / 2 := by
      rw [f.signResidual3_of_orthogonal_norm_add_first
        (horth 0 1 (by decide) _ _) (horth 0 2 (by decide) _ _)
        (horth 1 2 (by decide) _ _)]
      · simp [A, dt, coordinateTwist3, s]
      · simp only [norm_smul, henorm, mul_one, hnorm_dt]
        rw [hd10, hd11, hd12]
        ring
    have hr2 :
        signResidual3 f.homogeneousValue
            ((dt 2 0) • (e 0 : H)) ((dt 2 1) • (e 1 : H))
              ((dt 2 2) • (e 2 : H)) = B (p * q) / 2 := by
      rw [f.signResidual3_of_orthogonal_norm_add
        (horth 0 1 (by decide) _ _) (horth 0 2 (by decide) _ _)
        (horth 1 2 (by decide) _ _)]
      · simp [B, dt, coordinateTwist3, s]
      · simp only [norm_smul, henorm, mul_one, hnorm_dt]
        rw [hd20, hd21, hd22]
        ring
    have hrc1 :
        signResidual3 f.homogeneousValue
            ((dct 1 0) • (e 0 : H)) ((dct 1 1) • (e 1 : H))
              ((dct 1 2) • (e 2 : H)) = C (p * q) / 2 := by
      rw [f.signResidual3_of_orthogonal_norm_add
        (horth 0 1 (by decide) _ _) (horth 0 2 (by decide) _ _)
        (horth 1 2 (by decide) _ _)]
      · simp [C, dct, coordinateTwist3, s]
      · simp only [norm_smul, henorm, mul_one, hnorm_dct]
        rw [hdc10, hdc11, hdc12]
        ring
    have hrc2 :
        signResidual3 f.homogeneousValue
            ((dct 2 0) • (e 0 : H)) ((dct 2 1) • (e 1 : H))
              ((dct 2 2) • (e 2 : H)) = D p / 2 := by
      rw [f.signResidual3_of_orthogonal_norm_add_last
        (horth 0 1 (by decide) _ _) (horth 0 2 (by decide) _ _)
        (horth 1 2 (by decide) _ _)]
      · have hscale := f.quadraticDefect_smul (q : ℂ)
          (((p : ℂ) * dcyc 2 0) • (e 0 : H))
          ((dcyc 2 1) • (e 1 : H))
        rw [Circle.norm_coe, one_pow, one_mul] at hscale
        simpa [D, dct, coordinateTwist3, s, smul_smul, mul_assoc,
          mul_comm, mul_left_comm] using hscale
      · simp only [norm_smul, henorm, mul_one, hnorm_dct]
        rw [hdc20, hdc21, hdc22]
        ring
    rw [hr1, hr2, hrc1, hrc2] at htrade
    linarith
  have hAbound (z : Circle) : |A z| ≤ 1 := by
    refine (f.abs_quadraticDefect_le
      (((z : ℂ) * d 1 1) • (e 1 : H))
      ((d 1 2) • (e 2 : H))).trans_eq ?_
    simp only [norm_smul, henorm, mul_one, norm_mul,
      Circle.norm_coe, one_mul, hd11, hd12]
    ring
  have hAconst := pexider_left_eq_const_of_bounded
    A (fun z ↦ B z - C z) D hpex 1 hAbound
  refine ⟨d 1 1, d 1 2, hd11, hd12, ?_⟩
  intro z
  simpa [A] using hAconst z

lemma FrameFunction.quadraticDefect_phase_independent_half
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    (e : OrthonormalBasis (Fin 3) ℂ K)
    {t : ℝ} (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2)
    {α β : ℂ} (hα : ‖α‖ ^ 2 = t / 2)
    (hβ : ‖β‖ ^ 2 = (1 - t) / 2) :
    quadraticDefect f.homogeneousValue
        (α • (e 1 : H)) (β • (e 2 : H)) =
      quadraticDefect f.homogeneousValue
        (((Real.sqrt (t / 2) : ℝ) : ℂ) • (e 1 : H))
        (((Real.sqrt ((1 - t) / 2) : ℝ) : ℂ) • (e 2 : H)) := by
  have hc₀ : 0 ≤ 1 / 2 - t := by linarith
  have hc₁ : 1 / 2 - t ≤ 1 / 2 := by linarith
  obtain ⟨u, v, hu, hv, horbit⟩ :=
    f.balanced_edge_phase_orbit K e
      (a := 1 / 2) (b := t) (c := 1 / 2 - t)
      (by norm_num) ht₀ hc₀ (by norm_num) hth hc₁ (by ring)
  by_cases ht : t = 0
  · subst t
    have hα0 : α = 0 :=
      norm_eq_zero.mp (by nlinarith [norm_nonneg α])
    have hu0 : u = 0 :=
      norm_eq_zero.mp (by nlinarith [norm_nonneg u])
    subst α
    subst u
    simp only [zero_div, Real.sqrt_zero, Complex.ofReal_zero, zero_smul,
      quadraticDefect, zero_add, zero_sub, f.homogeneousValue_zero,
      f.homogeneousValue_neg]
    ring
  have htpos : 0 < t := lt_of_le_of_ne ht₀ (Ne.symm ht)
  have hupos : 0 < ‖u‖ := by
    have huSq : 0 < ‖u‖ ^ 2 := by rw [hu]; positivity
    nlinarith [norm_nonneg u]
  have hvpos : 0 < ‖v‖ := by
    have hvSq : 0 < ‖v‖ ^ 2 := by rw [hv]; linarith
    nlinarith [norm_nonneg v]
  have hαpos : 0 < ‖α‖ := by
    have hαSq : 0 < ‖α‖ ^ 2 := by rw [hα]; positivity
    nlinarith [norm_nonneg α]
  have hβpos : 0 < ‖β‖ := by
    have hβSq : 0 < ‖β‖ ^ 2 := by rw [hβ]; linarith
    nlinarith [norm_nonneg β]
  have huα : ‖u‖ = ‖α‖ := by
    nlinarith [norm_nonneg u, norm_nonneg α]
  have hvβ : ‖v‖ = ‖β‖ := by
    nlinarith [norm_nonneg v, norm_nonneg β]
  have hcompare (a b : ℂ)
      (ha : ‖a‖ = ‖u‖) (hb : ‖b‖ = ‖v‖) :
      quadraticDefect f.homogeneousValue
          (a • (e 1 : H)) (b • (e 2 : H)) =
        quadraticDefect f.homogeneousValue
          (u • (e 1 : H)) (v • (e 2 : H)) := by
    have hu0 : u ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hupos)
    have hv0 : v ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hvpos)
    have ha0 : a ≠ 0 := norm_ne_zero_iff.mp <| by rw [ha]; exact ne_of_gt hupos
    have hb0 : b ≠ 0 := norm_ne_zero_iff.mp <| by rw [hb]; exact ne_of_gt hvpos
    let phase : Circle :=
      ⟨b / v, mem_sphere_zero_iff_norm.mpr (by
        rw [norm_div, hb, div_self (ne_of_gt hvpos)])⟩
    have hphasev : (phase : ℂ) * v = b := by
      dsimp [phase]
      field_simp
    have hphaseu0 : (phase : ℂ) * u ≠ 0 :=
      mul_ne_zero (Circle.coe_ne_zero phase) hu0
    let z : Circle :=
      ⟨a / ((phase : ℂ) * u), mem_sphere_zero_iff_norm.mpr (by
        rw [norm_div, norm_mul, Circle.norm_coe, one_mul, ha,
          div_self (ne_of_gt hupos)])⟩
    have hzu : (phase : ℂ) * ((z : ℂ) * u) = a := by
      dsimp [z]
      field_simp
    have horbit' := horbit z
    have hscale_left := f.quadraticDefect_smul (phase : ℂ)
      (((z : ℂ) * u) • (e 1 : H)) (v • (e 2 : H))
    rw [Circle.norm_coe, one_pow, one_mul] at hscale_left
    calc
      quadraticDefect f.homogeneousValue
          (a • (e 1 : H)) (b • (e 2 : H)) =
        quadraticDefect f.homogeneousValue
          ((phase : ℂ) • (((z : ℂ) * u) • (e 1 : H)))
          ((phase : ℂ) • (v • (e 2 : H))) := by
            simp only [smul_smul]
            rw [hzu, hphasev]
      _ = quadraticDefect f.homogeneousValue
          (((z : ℂ) * u) • (e 1 : H)) (v • (e 2 : H)) :=
        hscale_left
      _ = quadraticDefect f.homogeneousValue
          (u • (e 1 : H)) (v • (e 2 : H)) := horbit'
  have hleft := hcompare α β huα.symm hvβ.symm
  have hsqrtα :
      ‖(((Real.sqrt (t / 2) : ℝ) : ℂ))‖ = ‖u‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsquare := Real.sq_sqrt (by positivity : 0 ≤ t / 2)
    nlinarith [Real.sqrt_nonneg (t / 2), norm_nonneg u]
  have hsqrtβ :
      ‖(((Real.sqrt ((1 - t) / 2) : ℝ) : ℂ))‖ = ‖v‖ := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    have hsquare := Real.sq_sqrt (by linarith : 0 ≤ (1 - t) / 2)
    nlinarith [Real.sqrt_nonneg ((1 - t) / 2), norm_nonneg v]
  exact hleft.trans (hcompare _ _ hsqrtα hsqrtβ).symm

/-- The normalized half-energy edge defect on an ordered orthonormal pair. -/
def FrameFunction.edgeDefectHalf
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (f : FrameFunction H) (x y : H) (t : ℝ) : ℝ :=
  quadraticDefect f.homogeneousValue
    (((Real.sqrt (t / 2) : ℝ) : ℂ) • x)
    (((Real.sqrt ((1 - t) / 2) : ℝ) : ℂ) • y)

lemma FrameFunction.quadraticDefect_phase_independent_half_zero_two
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    (e : OrthonormalBasis (Fin 3) ℂ K)
    {t : ℝ} (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2)
    {α β : ℂ} (hα : ‖α‖ ^ 2 = t / 2)
    (hβ : ‖β‖ ^ 2 = (1 - t) / 2) :
    quadraticDefect f.homogeneousValue
        (α • (e 0 : H)) (β • (e 2 : H)) =
      f.edgeDefectHalf (e 0 : H) (e 2 : H) t := by
  let e' := e.reindex (Equiv.swap (0 : Fin 3) 1)
  have h := f.quadraticDefect_phase_independent_half K e' ht₀ hth hα hβ
  have hswap1 :
      (Equiv.swap (0 : Fin 3) 1).symm (1 : Fin 3) = 0 := by decide
  have hswap2 :
      (Equiv.swap (0 : Fin 3) 1).symm (2 : Fin 3) = 2 := by decide
  change quadraticDefect f.homogeneousValue
      (α • (e 0 : H)) (β • (e 2 : H)) =
    quadraticDefect f.homogeneousValue
      (((Real.sqrt (t / 2) : ℝ) : ℂ) • (e 0 : H))
      (((Real.sqrt ((1 - t) / 2) : ℝ) : ℂ) • (e 2 : H))
  simpa only [e', OrthonormalBasis.reindex_apply, hswap1, hswap2] using h

lemma FrameFunction.quadraticDefect_phase_independent_half_zero_one
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    (e : OrthonormalBasis (Fin 3) ℂ K)
    {t : ℝ} (ht₀ : 0 ≤ t) (hth : t ≤ 1 / 2)
    {α β : ℂ} (hα : ‖α‖ ^ 2 = t / 2)
    (hβ : ‖β‖ ^ 2 = (1 - t) / 2) :
    quadraticDefect f.homogeneousValue
        (α • (e 0 : H)) (β • (e 1 : H)) =
      f.edgeDefectHalf (e 0 : H) (e 1 : H) t := by
  let σ : Fin 3 ≃ Fin 3 :=
    (Equiv.swap (1 : Fin 3) 2).trans (Equiv.swap (0 : Fin 3) 1)
  let e' := e.reindex σ
  have h := f.quadraticDefect_phase_independent_half K e' ht₀ hth hα hβ
  have hσ1 : σ.symm (1 : Fin 3) = 0 := by decide
  have hσ2 : σ.symm (2 : Fin 3) = 1 := by decide
  change quadraticDefect f.homogeneousValue
      (α • (e 0 : H)) (β • (e 1 : H)) =
    quadraticDefect f.homogeneousValue
      (((Real.sqrt (t / 2) : ℝ) : ℂ) • (e 0 : H))
      (((Real.sqrt ((1 - t) / 2) : ℝ) : ℂ) • (e 1 : H))
  simpa only [e', OrthonormalBasis.reindex_apply, hσ1, hσ2] using h

lemma FrameFunction.edgeDefectHalf_balanced
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    (e : OrthonormalBasis (Fin 3) ℂ K)
    {a b c : ℝ}
    (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c)
    (ha₁ : a ≤ 1 / 2) (hb₁ : b ≤ 1 / 2) (hc₁ : c ≤ 1 / 2)
    (hsum : a + b + c = 1) :
    f.edgeDefectHalf (e 0 : H) (e 2 : H) b +
        f.edgeDefectHalf (e 0 : H) (e 2 : H) c =
      -f.edgeDefectHalf (e 1 : H) (e 2 : H) a -
        f.edgeDefectHalf (e 0 : H) (e 1 : H) a := by
  classical
  obtain ⟨d, hd0, hd10, hd11, hd12, hd20, hd21, hd22⟩ :=
    exists_balanced_coefficient_basis hb₀ ha₀ hc₀ hb₁ ha₁ hc₁ (by linarith)
  obtain ⟨d', hd'0, hd'10, hd'11, hd'12, hd'20, hd'21, hd'22⟩ :=
    exists_balanced_coefficient_basis ha₀ hc₀ hb₀ ha₁ hc₁ hb₁ (by linarith)
  let dcyc : Fin 3 → EuclideanSpace ℂ (Fin 3) :=
    fun j ↦ cycleCoordinates3 (d' j)
  have hdcyc : Orthonormal ℂ dcyc := by
    simpa only [dcyc] using orthonormal_cycleCoordinates3 d'
  have hfirst : d 0 = dcyc 0 := by
    rw [hd0]
    simp only [dcyc, hd'0]
    ext i
    fin_cases i <;> simp [cycleCoordinates3]
  have hdc10 : ‖dcyc 1 0‖ ^ 2 = (1 - c) / 2 := by
    simpa [dcyc] using hd'12
  have hdc11 : ‖dcyc 1 1‖ ^ 2 = 1 / 2 := by
    simpa [dcyc] using hd'10
  have hdc12 : ‖dcyc 1 2‖ ^ 2 = c / 2 := by
    simpa [dcyc] using hd'11
  have hdc20 : ‖dcyc 2 0‖ ^ 2 = (1 - a) / 2 := by
    simpa [dcyc] using hd'22
  have hdc21 : ‖dcyc 2 1‖ ^ 2 = a / 2 := by
    simpa [dcyc] using hd'20
  have hdc22 : ‖dcyc 2 2‖ ^ 2 = 1 / 2 := by
    simpa [dcyc] using hd'21
  have hsumd := f.sum_signResidual3_orthonormalBasis K e d
  have hsumdc := f.sum_signResidual3_orthonormal K e dcyc hdcyc
  have hrow0 :
      signResidual3 f.homogeneousValue
          ((d 0 0) • (e 0 : H)) ((d 0 1) • (e 1 : H))
            ((d 0 2) • (e 2 : H)) =
        signResidual3 f.homogeneousValue
          ((dcyc 0 0) • (e 0 : H)) ((dcyc 0 1) • (e 1 : H))
            ((dcyc 0 2) • (e 2 : H)) := by
    rw [hfirst]
  have htrade :
      signResidual3 f.homogeneousValue
            ((d 1 0) • (e 0 : H)) ((d 1 1) • (e 1 : H))
              ((d 1 2) • (e 2 : H)) +
          signResidual3 f.homogeneousValue
            ((d 2 0) • (e 0 : H)) ((d 2 1) • (e 1 : H))
              ((d 2 2) • (e 2 : H)) =
        signResidual3 f.homogeneousValue
            ((dcyc 1 0) • (e 0 : H)) ((dcyc 1 1) • (e 1 : H))
              ((dcyc 1 2) • (e 2 : H)) +
          signResidual3 f.homogeneousValue
            ((dcyc 2 0) • (e 0 : H)) ((dcyc 2 1) • (e 1 : H))
              ((dcyc 2 2) • (e 2 : H)) := by
    simp [Fin.sum_univ_succ] at hsumd hsumdc
    rw [hrow0] at hsumd
    linarith
  have heorth (i j : Fin 3) (hij : i ≠ j) :
      inner ℂ (e i : H) (e j : H) = 0 := by
    change inner ℂ (e i) (e j) = 0
    rw [orthonormal_iff_ite.mp e.orthonormal i j, if_neg hij]
  have henorm (i : Fin 3) : ‖(e i : H)‖ = 1 := by
    change ‖e i‖ = 1
    exact e.norm_eq_one i
  have horth (i j : Fin 3) (hij : i ≠ j) (x y : ℂ) :
      inner ℂ (x • (e i : H)) (y • (e j : H)) = 0 := by
    simp only [inner_smul_left, inner_smul_right, heorth i j hij, mul_zero]
  have hr1 :
      signResidual3 f.homogeneousValue
          ((d 1 0) • (e 0 : H)) ((d 1 1) • (e 1 : H))
            ((d 1 2) • (e 2 : H)) =
        quadraticDefect f.homogeneousValue
          ((d 1 1) • (e 1 : H)) ((d 1 2) • (e 2 : H)) / 2 := by
    apply f.signResidual3_of_orthogonal_norm_add_first
      (horth 0 1 (by decide) _ _) (horth 0 2 (by decide) _ _)
      (horth 1 2 (by decide) _ _)
    simp only [norm_smul, henorm, mul_one]
    rw [hd10, hd11, hd12]
    ring
  have hr2 :
      signResidual3 f.homogeneousValue
          ((d 2 0) • (e 0 : H)) ((d 2 1) • (e 1 : H))
            ((d 2 2) • (e 2 : H)) =
        quadraticDefect f.homogeneousValue
          ((d 2 0) • (e 0 : H)) ((d 2 2) • (e 2 : H)) / 2 := by
    apply f.signResidual3_of_orthogonal_norm_add
      (horth 0 1 (by decide) _ _) (horth 0 2 (by decide) _ _)
      (horth 1 2 (by decide) _ _)
    simp only [norm_smul, henorm, mul_one]
    rw [hd20, hd21, hd22]
    ring
  have hrc1 :
      signResidual3 f.homogeneousValue
          ((dcyc 1 0) • (e 0 : H)) ((dcyc 1 1) • (e 1 : H))
            ((dcyc 1 2) • (e 2 : H)) =
        quadraticDefect f.homogeneousValue
          ((dcyc 1 0) • (e 0 : H)) ((dcyc 1 2) • (e 2 : H)) / 2 := by
    apply f.signResidual3_of_orthogonal_norm_add
      (horth 0 1 (by decide) _ _) (horth 0 2 (by decide) _ _)
      (horth 1 2 (by decide) _ _)
    simp only [norm_smul, henorm, mul_one]
    rw [hdc10, hdc11, hdc12]
    ring
  have hrc2 :
      signResidual3 f.homogeneousValue
          ((dcyc 2 0) • (e 0 : H)) ((dcyc 2 1) • (e 1 : H))
            ((dcyc 2 2) • (e 2 : H)) =
        quadraticDefect f.homogeneousValue
          ((dcyc 2 0) • (e 0 : H)) ((dcyc 2 1) • (e 1 : H)) / 2 := by
    apply f.signResidual3_of_orthogonal_norm_add_last
      (horth 0 1 (by decide) _ _) (horth 0 2 (by decide) _ _)
      (horth 1 2 (by decide) _ _)
    simp only [norm_smul, henorm, mul_one]
    rw [hdc20, hdc21, hdc22]
    ring
  have hphase12 :
      quadraticDefect f.homogeneousValue
          ((d 1 1) • (e 1 : H)) ((d 1 2) • (e 2 : H)) =
        f.edgeDefectHalf (e 1 : H) (e 2 : H) a := by
    simpa [FrameFunction.edgeDefectHalf] using
      f.quadraticDefect_phase_independent_half K e ha₀ ha₁ hd11 hd12
  have hphase02 :
      quadraticDefect f.homogeneousValue
          ((d 2 0) • (e 0 : H)) ((d 2 2) • (e 2 : H)) =
        f.edgeDefectHalf (e 0 : H) (e 2 : H) b :=
    f.quadraticDefect_phase_independent_half_zero_two K e hb₀ hb₁ hd20 hd22
  have he0 : ‖(e 0 : H)‖ = 1 := henorm 0
  have he1 : ‖(e 1 : H)‖ = 1 := henorm 1
  have he2 : ‖(e 2 : H)‖ = 1 := henorm 2
  have he02 : inner ℂ (e 0 : H) (e 2 : H) = 0 := heorth 0 2 (by decide)
  have he01 : inner ℂ (e 0 : H) (e 1 : H) = 0 := heorth 0 1 (by decide)
  have hphasec :
      quadraticDefect f.homogeneousValue
          ((dcyc 1 0) • (e 0 : H)) ((dcyc 1 2) • (e 2 : H)) =
        -f.edgeDefectHalf (e 0 : H) (e 2 : H) c := by
    have hswap := f.quadraticDefect_swap_complex_scalars
      he0 he2 he02 (dcyc 1 0) (dcyc 1 2)
    have hsmall :
        quadraticDefect f.homogeneousValue
            ((starRingEnd ℂ (dcyc 1 2)) • (e 0 : H))
            ((starRingEnd ℂ (dcyc 1 0)) • (e 2 : H)) =
          f.edgeDefectHalf (e 0 : H) (e 2 : H) c := by
      apply f.quadraticDefect_phase_independent_half_zero_two K e hc₀ hc₁
      · rw [starRingEnd_apply, norm_star]
        exact hdc12
      · rw [starRingEnd_apply, norm_star]
        exact hdc10
    rw [hswap, hsmall]
  have hphasea :
      quadraticDefect f.homogeneousValue
          ((dcyc 2 0) • (e 0 : H)) ((dcyc 2 1) • (e 1 : H)) =
        -f.edgeDefectHalf (e 0 : H) (e 1 : H) a := by
    have hswap := f.quadraticDefect_swap_complex_scalars
      he0 he1 he01 (dcyc 2 0) (dcyc 2 1)
    have hsmall :
        quadraticDefect f.homogeneousValue
            ((starRingEnd ℂ (dcyc 2 1)) • (e 0 : H))
            ((starRingEnd ℂ (dcyc 2 0)) • (e 1 : H)) =
          f.edgeDefectHalf (e 0 : H) (e 1 : H) a := by
      apply f.quadraticDefect_phase_independent_half_zero_one K e ha₀ ha₁
      · rw [starRingEnd_apply, norm_star]
        exact hdc21
      · rw [starRingEnd_apply, norm_star]
        exact hdc20
    rw [hswap, hsmall]
  rw [hr1, hr2, hrc1, hrc2, hphase12, hphase02, hphasec, hphasea] at htrade
  linarith

lemma FrameFunction.edgeDefectHalf_zero
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (K : Submodule ℂ H)
    (e : OrthonormalBasis (Fin 3) ℂ K) :
    ∀ t, 0 ≤ t → t ≤ 1 →
      f.edgeDefectHalf (e 0 : H) (e 2 : H) t = 0 := by
  let A : ℝ → ℝ :=
    fun t ↦ -f.edgeDefectHalf (e 1 : H) (e 2 : H) t
  let B : ℝ → ℝ :=
    fun t ↦ f.edgeDefectHalf (e 0 : H) (e 2 : H) t
  let C : ℝ → ℝ :=
    fun t ↦ -f.edgeDefectHalf (e 0 : H) (e 1 : H) t
  have heorth (i j : Fin 3) (hij : i ≠ j) :
      inner ℂ (e i : H) (e j : H) = 0 := by
    change inner ℂ (e i) (e j) = 0
    rw [orthonormal_iff_ite.mp e.orthonormal i j, if_neg hij]
  have henorm (i : Fin 3) : ‖(e i : H)‖ = 1 := by
    change ‖e i‖ = 1
    exact e.norm_eq_one i
  have hzero (i j : Fin 3) :
      f.edgeDefectHalf (e i : H) (e j : H) 0 = 0 := by
    simp [FrameFunction.edgeDefectHalf, quadraticDefect,
      f.homogeneousValue_neg]
    ring
  have hhalf (i j : Fin 3) (hij : i ≠ j) :
      f.edgeDefectHalf (e i : H) (e j : H) (1 / 2) = 0 := by
    apply f.quadraticDefect_eq_zero_of_orthogonal_of_norm_eq
    · simp only [inner_smul_left, inner_smul_right,
        heorth i j hij, mul_zero]
    · simp only [norm_smul, henorm, mul_one,
        Complex.norm_real, Real.norm_eq_abs]
      all_goals norm_num
  have hcomp (i j : Fin 3) (hij : i ≠ j)
      (t : ℝ) (_ht₀ : 0 ≤ t) (_ht₁ : t ≤ 1) :
      f.edgeDefectHalf (e i : H) (e j : H) (1 - t) =
        -f.edgeDefectHalf (e i : H) (e j : H) t := by
    have hswap := f.quadraticDefect_swap_real_scalars
      (henorm i) (henorm j) (heorth i j hij)
      (Real.sqrt ((1 - t) / 2)) (Real.sqrt (t / 2))
    simpa [FrameFunction.edgeDefectHalf] using hswap
  have hbound (t : ℝ) (ht₀ : 0 ≤ t) (ht₁ : t ≤ 1) : |B t| ≤ 1 := by
    have hsqt := Real.sq_sqrt (by positivity : 0 ≤ t / 2)
    have hsqc := Real.sq_sqrt (by positivity : 0 ≤ (1 - t) / 2)
    refine (f.abs_quadraticDefect_le
      ((((Real.sqrt (t / 2) : ℝ) : ℂ)) • (e 0 : H))
      ((((Real.sqrt ((1 - t) / 2) : ℝ) : ℂ)) • (e 2 : H))).trans_eq ?_
    simp only [norm_smul, henorm,
      mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _)]
    nlinarith
  have hbalanced (a b c : ℝ)
      (ha₀ : 0 ≤ a) (hb₀ : 0 ≤ b) (hc₀ : 0 ≤ c)
      (ha₁ : a ≤ 1 / 2) (hb₁ : b ≤ 1 / 2) (hc₁ : c ≤ 1 / 2)
      (hsum : a + b + c = 1) :
      B b + B c = A a + C a := by
    simpa only [A, B, C, sub_eq_add_neg] using
      f.edgeDefectHalf_balanced K e ha₀ hb₀ hc₀ ha₁ hb₁ hc₁ hsum
  have hvanish := balanced_cocycle_middle_eq_zero A B C
    (by simp [A, hzero]) (by simp [B, hzero]) (by simp [C, hzero])
    (by
      show -f.edgeDefectHalf (e 1 : H) (e 2 : H) (1 / 2) = 0
      rw [hhalf 1 2 (by decide)]
      simp)
    (hhalf 0 2 (by decide))
    (by
      show -f.edgeDefectHalf (e 0 : H) (e 1 : H) (1 / 2) = 0
      rw [hhalf 0 1 (by decide)]
      simp)
    (by
      intro t ht₀ ht₁
      simp only [A]
      rw [hcomp 1 2 (by decide) t ht₀ ht₁]
      )
    (hcomp 0 2 (by decide))
    (by
      intro t ht₀ ht₁
      simp only [C]
      rw [hcomp 0 1 (by decide) t ht₀ ht₁]
      )
    hbalanced 1 hbound
  simpa [B] using hvanish

lemma FrameFunction.quadraticDefect_eq_zero_of_orthogonal
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] [FiniteDimensional ℂ H]
    (f : FrameFunction H) (hdim : 3 ≤ Module.finrank ℂ H)
    {x y : H} (hxy : inner ℂ x y = 0) :
    quadraticDefect f.homogeneousValue x y = 0 := by
  have hsmall {u v : H} (huv : inner ℂ u v = 0)
      (hnorm : ‖u‖ ≤ ‖v‖) :
      quadraticDefect f.homogeneousValue u v = 0 := by
    by_cases hu0 : u = 0
    · subst u
      simp only [quadraticDefect, zero_add, zero_sub,
        f.homogeneousValue_zero]
      rw [f.homogeneousValue_neg]
      ring
    by_cases hv0 : v = 0
    · subst v
      simp only [quadraticDefect, add_zero, sub_zero,
        f.homogeneousValue_zero]
      ring
    have hunorm : ‖u‖ ≠ 0 := norm_ne_zero_iff.mpr hu0
    have hvnorm : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv0
    let u₀ : H := ((‖u‖ : ℂ)⁻¹) • u
    let v₀ : H := ((‖v‖ : ℂ)⁻¹) • v
    have hu₀ : ‖u₀‖ = 1 := by simp [u₀, norm_smul, hunorm]
    have hv₀ : ‖v₀‖ = 1 := by simp [v₀, norm_smul, hvnorm]
    have huv₀ : inner ℂ u₀ v₀ = 0 := by simp [u₀, v₀, huv]
    obtain ⟨z, hz, huz, hvz⟩ := exists_unit_orthogonal_pair hdim u v
    have hu₀z : inner ℂ u₀ z = 0 := by simp [u₀, huz]
    have hzv₀ : inner ℂ z v₀ = 0 := by
      apply inner_eq_zero_symm.mp
      simp only [v₀, inner_smul_left, hvz, mul_zero]
    let w : Fin 3 → H := ![u₀, z, v₀]
    have hw : Orthonormal ℂ w := by
      rw [orthonormal_iff_ite]
      intro i j
      have hv₀u : inner ℂ v₀ u₀ = 0 := inner_eq_zero_symm.mp huv₀
      have hzu₀ : inner ℂ z u₀ = 0 := inner_eq_zero_symm.mp hu₀z
      have hv₀z : inner ℂ v₀ z = 0 := inner_eq_zero_symm.mp hzv₀
      fin_cases i <;> fin_cases j <;>
        simp [w, hu₀, hv₀, hz, huv₀, hv₀u, hu₀z, hzu₀, hzv₀, hv₀z,
          inner_self_eq_norm_sq_to_K]
    obtain ⟨K, e, he⟩ := exists_orthonormalBasis_span_fin3 w hw
    have he0 : (e 0 : H) = u₀ := by simpa [w] using he 0
    have he2 : (e 2 : H) = v₀ := by simpa [w] using he 2
    let E : ℝ := ‖u‖ ^ 2 + ‖v‖ ^ 2
    have hEpos : 0 < E := by
      dsimp [E]
      positivity
    let r : ℝ := Real.sqrt (2 * E)
    have hrpos : 0 < r := Real.sqrt_pos.2 (by positivity)
    have hr0 : r ≠ 0 := ne_of_gt hrpos
    have hr2 : r ^ 2 = 2 * E := Real.sq_sqrt (by positivity)
    let t : ℝ := ‖u‖ ^ 2 / E
    have ht₀ : 0 ≤ t := by positivity
    have hth : t ≤ 1 / 2 := by
      dsimp [t, E]
      apply (div_le_iff₀ hEpos).2
      nlinarith [sq_nonneg ‖u‖, sq_nonneg ‖v‖,
        mul_self_le_mul_self (norm_nonneg u) hnorm]
    have ht₁ : t ≤ 1 := hth.trans (by norm_num)
    let α : ℂ := ((‖u‖ / r : ℝ) : ℂ)
    let β : ℂ := ((‖v‖ / r : ℝ) : ℂ)
    have hα : ‖α‖ ^ 2 = t / 2 := by
      have hur : 0 ≤ ‖u‖ / r := div_nonneg (norm_nonneg u) hrpos.le
      simp only [α, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hur]
      dsimp [t]
      field_simp [hr0, ne_of_gt hEpos]
      nlinarith
    have hβ : ‖β‖ ^ 2 = (1 - t) / 2 := by
      have hvr : 0 ≤ ‖v‖ / r := div_nonneg (norm_nonneg v) hrpos.le
      simp only [β, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hvr]
      dsimp [t, E] at *
      field_simp [hr0, ne_of_gt hEpos]
      nlinarith
    have hedge := f.edgeDefectHalf_zero K e t ht₀ ht₁
    have hphase :=
      f.quadraticDefect_phase_independent_half_zero_two K e ht₀ hth hα hβ
    rw [hedge] at hphase
    have hscale := f.quadraticDefect_smul (r : ℂ)
      (α • (e 0 : H)) (β • (e 2 : H))
    have hru : (r : ℂ) • (α • (e 0 : H)) = u := by
      rw [he0, smul_smul]
      have hrα : (r : ℂ) * α = (‖u‖ : ℂ) := by
        dsimp [α]
        push_cast
        field_simp [hr0]
      rw [hrα]
      simp [u₀, hunorm]
    have hrv : (r : ℂ) • (β • (e 2 : H)) = v := by
      rw [he2, smul_smul]
      have hrβ : (r : ℂ) * β = (‖v‖ : ℂ) := by
        dsimp [β]
        push_cast
        field_simp [hr0]
      rw [hrβ]
      simp [v₀, hvnorm]
    rw [hru, hrv, hphase, mul_zero] at hscale
    exact hscale
  rcases le_total ‖x‖ ‖y‖ with hle | hle
  · exact hsmall hxy hle
  · have hyx : inner ℂ y x = 0 := inner_eq_zero_symm.mp hxy
    have hz := hsmall hyx hle
    rw [quadraticDefect_comm_of_even f.homogeneousValue
      f.homogeneousValue_neg] at hz
    exact hz

end

end LeanEval.Analysis
