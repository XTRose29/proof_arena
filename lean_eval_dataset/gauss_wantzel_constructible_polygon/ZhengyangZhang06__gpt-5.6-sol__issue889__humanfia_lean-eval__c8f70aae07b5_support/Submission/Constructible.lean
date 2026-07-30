import Submission.Helpers

open LeanEval.NumberTheory.GaussWantzel

namespace Submission.Helpers

/-! The coordinatewise version of real constructibility is convenient when
working in a cyclotomic extension inside `ℂ`. -/

def ComplexConstructible (z : ℂ) : Prop :=
  IsConstructible z.re ∧ IsConstructible z.im

namespace ComplexConstructible

lemma of_rat (q : ℚ) : ComplexConstructible (algebraMap ℚ ℂ q) := by
  constructor
  · simpa using IsConstructible.base q
  · simpa using IsConstructible.base 0

lemma of_real {x : ℝ} (hx : IsConstructible x) : ComplexConstructible x := by
  exact ⟨by simpa, by simpa using IsConstructible.base 0⟩

lemma add {z w : ℂ} (hz : ComplexConstructible z) (hw : ComplexConstructible w) :
    ComplexConstructible (z + w) := by
  exact ⟨by simpa using hz.1.add hw.1, by simpa using hz.2.add hw.2⟩

lemma neg {z : ℂ} (hz : ComplexConstructible z) : ComplexConstructible (-z) := by
  exact ⟨by simpa using hz.1.neg, by simpa using hz.2.neg⟩

lemma sub {z w : ℂ} (hz : ComplexConstructible z) (hw : ComplexConstructible w) :
    ComplexConstructible (z - w) := by
  rw [sub_eq_add_neg]
  exact hz.add hw.neg

lemma mul {z w : ℂ} (hz : ComplexConstructible z) (hw : ComplexConstructible w) :
    ComplexConstructible (z * w) := by
  constructor
  · simpa [sub_eq_add_neg] using (hz.1.mul hw.1).add (hz.2.mul hw.2).neg
  · simpa using (hz.1.mul hw.2).add (hz.2.mul hw.1)

lemma normSq {z : ℂ} (hz : ComplexConstructible z) : IsConstructible z.normSq := by
  simpa [Complex.normSq_apply] using (hz.1.mul hz.1).add (hz.2.mul hz.2)

lemma norm {z : ℂ} (hz : ComplexConstructible z) : IsConstructible ‖z‖ := by
  rw [Complex.norm_def]
  exact hz.normSq.sqrt

lemma inv {z : ℂ} (hz : ComplexConstructible z) : ComplexConstructible z⁻¹ := by
  constructor
  · simpa [Complex.inv_re, div_eq_mul_inv] using hz.1.mul hz.normSq.inv
  · simpa [Complex.inv_im, div_eq_mul_inv] using hz.2.neg.mul hz.normSq.inv

lemma div {z w : ℂ} (hz : ComplexConstructible z) (hw : ComplexConstructible w) :
    ComplexConstructible (z / w) := by
  rw [div_eq_mul_inv]
  exact hz.mul hw.inv

lemma sqrt {z : ℂ} (hz : ComplexConstructible z) : ComplexConstructible z.sqrt := by
  have hhalf : IsConstructible ((2 : ℝ)⁻¹) := by
    simpa using (IsConstructible.base (2 : ℚ)).inv
  have hre : IsConstructible (Real.sqrt ((‖z‖ + z.re) / 2)) := by
    simpa [div_eq_mul_inv] using (hz.norm.add hz.1).mul hhalf |>.sqrt
  have him : IsConstructible (Real.sqrt ((‖z‖ - z.re) / 2)) := by
    simpa [div_eq_mul_inv, sub_eq_add_neg] using (hz.norm.add hz.1.neg).mul hhalf |>.sqrt
  rw [Complex.sqrt_eq_real_add_ite]
  by_cases h : 0 ≤ z.im
  · rw [if_pos h]
    exact ⟨by simpa using hre, by simpa using him⟩
  · rw [if_neg h]
    exact ⟨by simpa using hre, by simpa using him.neg⟩

private lemma complex_sqrt_sq (z : ℂ) : z.sqrt ^ 2 = z := by
  by_cases hz : z = 0
  · simp [hz]
  rw [sqrt_eq_exp hz, pow_two, ← Complex.exp_add]
  have hhalf : Complex.log z / 2 + Complex.log z / 2 = Complex.log z := by ring
  rw [hhalf, Complex.exp_log hz]

lemma sqrt_square {z : ℂ} (hz : ComplexConstructible (z ^ 2)) :
    ComplexConstructible z := by
  have hsqrt := hz.sqrt
  have hsquare : (z ^ 2).sqrt ^ 2 = z ^ 2 := complex_sqrt_sq _
  have hor : (z ^ 2).sqrt = z ∨ (z ^ 2).sqrt = -z := by
    have hfactor : ((z ^ 2).sqrt - z) * ((z ^ 2).sqrt + z) = 0 := by
      calc
        ((z ^ 2).sqrt - z) * ((z ^ 2).sqrt + z) = (z ^ 2).sqrt ^ 2 - z ^ 2 := by ring
        _ = 0 := by rw [hsquare, sub_self]
    rcases mul_eq_zero.mp hfactor with h | h
    · exact Or.inl (sub_eq_zero.mp h)
    · exact Or.inr (add_eq_zero_iff_eq_neg.mp h)
  rcases hor with h | h
  · simpa [h] using hsqrt
  · rw [h] at hsqrt
    simpa using hsqrt.neg

end ComplexConstructible

section QuadraticExtension

variable {F E : Type*} [Field F] [Field E]
variable [Algebra ℚ F] [Algebra ℚ E] [Algebra F E] [IsScalarTower ℚ F E]

omit [Algebra ℚ F] [IsScalarTower ℚ F E] in
lemma complexConstructible_of_sq_adjoin_eq_top (ι : E →ₐ[ℚ] ℂ)
    (hF : ∀ x : F, ComplexConstructible (ι (algebraMap F E x)))
    {α : E} (hαsq : α ^ 2 ∈ Set.range (algebraMap F E))
    (hα : IntermediateField.adjoin F {α} = ⊤) (x : E) :
    ComplexConstructible (ι x) := by
  obtain ⟨a, ha⟩ := hαsq
  have hgen : ComplexConstructible (ι α) := by
    apply ComplexConstructible.sqrt_square
    rw [← map_pow, ← ha]
    exact hF a
  have hx : x ∈ IntermediateField.adjoin F {α} := by
    rw [hα]
    exact IntermediateField.mem_top
  induction hx using IntermediateField.adjoin_induction with
  | mem y hy =>
      simp only [Set.mem_singleton_iff] at hy
      subst y
      exact hgen
  | algebraMap y => exact hF y
  | add y z _ _ hy hz => simpa using hy.add hz
  | mul y z _ _ hy hz => simpa using hy.mul hz
  | inv y _ hy => simpa using hy.inv

omit [IsScalarTower ℚ F E] in
lemma complexConstructible_of_quadratic_extension (ι : E →ₐ[ℚ] ℂ)
    [FiniteDimensional F E] [IsGalois F E]
    (hF : ∀ x : F, ComplexConstructible (ι (algebraMap F E x)))
    (hfin : Module.finrank F E = 2) (x : E) : ComplexConstructible (ι x) := by
  letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  letI : CharP F 0 := algebraRat.charP_zero F
  letI : IsCyclic Gal(E/F) := isCyclic_of_prime_card <| by
    rw [IsGalois.card_aut_eq_finrank, hfin]
  have hroots : (primitiveRoots (Module.finrank F E) F).Nonempty := by
    rw [hfin]
    refine ⟨-1, (mem_primitiveRoots (by norm_num)).2 ?_⟩
    exact IsPrimitiveRoot.neg_one 0 (by norm_num)
  obtain ⟨α, hαsq, hα⟩ := exists_root_adjoin_eq_top_of_isCyclic F E hroots
  rw [hfin] at hαsq
  exact complexConstructible_of_sq_adjoin_eq_top ι hF hαsq hα x

end QuadraticExtension

open scoped IsMulCommutative

lemma complexConstructible_of_abelian_two_extension
    {F E : Type} [Field F] [Field E]
    [Algebra ℚ F] [Algebra ℚ E] [Algebra F E] [IsScalarTower ℚ F E]
    [FiniteDimensional F E] [IsAbelianGalois F E]
    (ι : E →ₐ[ℚ] ℂ) (hF : ∀ x : F, ComplexConstructible (ι (algebraMap F E x)))
    (k : ℕ) (hfin : Module.finrank F E = 2 ^ k) (x : E) :
    ComplexConstructible (ι x) := by
  induction k generalizing F with
  | zero =>
      simp only [pow_zero] at hfin
      obtain ⟨a, rfl⟩ := (Algebra.finrank_eq_one_iff_bijective_algebraMap.mp hfin).2 x
      exact hF a
  | succ k ih =>
      letI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hcard : Nat.card Gal(E/F) = 2 ^ (k + 1) := by
        rw [IsGalois.card_aut_eq_finrank, hfin]
      have hdvd : 2 ^ k ∣ Nat.card Gal(E/F) := by
        rw [hcard]
        exact pow_dvd_pow 2 (Nat.le_succ k)
      obtain ⟨H, hH⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
      letI : H.Normal := Subgroup.normal_of_isMulCommutative H
      let K := IntermediateField.fixedField H
      have hKE : Module.finrank K E = 2 ^ k := by
        simpa [K, hH] using (IntermediateField.finrank_fixedField_eq_card (H := H))
      have hFK_mul : Module.finrank F K * 2 ^ k = 2 * 2 ^ k := by
        calc
          Module.finrank F K * 2 ^ k = Module.finrank F K * Module.finrank K E := by rw [hKE]
          _ = Module.finrank F E := Module.finrank_mul_finrank F K E
          _ = 2 ^ (k + 1) := hfin
          _ = 2 * 2 ^ k := by rw [pow_succ']
      have hFK : Module.finrank F K = 2 :=
        Nat.mul_right_cancel (pow_pos (by norm_num) k) hFK_mul
      let ιK : K →ₐ[ℚ] ℂ := ι.comp (IsScalarTower.toAlgHom ℚ K E)
      have hbaseK (a : F) : ComplexConstructible (ιK (algebraMap F K a)) := by
        simpa [ιK] using hF a
      have hconstructK (y : K) : ComplexConstructible (ιK y) :=
        complexConstructible_of_quadratic_extension ιK hbaseK hFK y
      have hbaseE (y : K) : ComplexConstructible (ι (algebraMap K E y)) := by
        simpa [ιK] using hconstructK y
      exact ih hbaseE hKE

lemma isConstructible_cos_of_isTwoPower_totient {n : ℕ} (hn : 0 < n)
    (htot : IsTwoPower n.totient) : IsConstructible (Real.cos (2 * Real.pi / n)) := by
  obtain ⟨k, hk⟩ := htot
  letI : NeZero n := ⟨hn.ne'⟩
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hn.ne'
  let L : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ {ζ}
  have hζalg : IsAlgebraic ℚ ζ := by
    exact ⟨Polynomial.X ^ n - 1,
      (Polynomial.monic_X_pow_sub_C (1 : ℚ) hn.ne').ne_zero, by simp [hζ.pow_eq_one]⟩
  letI : IsCyclotomicExtension {n} ℚ L := by
    change IsCyclotomicExtension {n} ℚ L.toSubalgebra
    rw [show L.toSubalgebra = Algebra.adjoin ℚ {ζ} by
      exact IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic
        hζalg]
    exact hζ.adjoin_isCyclotomicExtension ℚ
  letI : FiniteDimensional ℚ L := IsCyclotomicExtension.finiteDimensional {n} ℚ L
  letI : IsAbelianGalois ℚ L := IsCyclotomicExtension.isAbelianGalois {n} ℚ L
  let ιL : L →ₐ[ℚ] ℂ := IsScalarTower.toAlgHom ℚ L ℂ
  have hbase (q : ℚ) : ComplexConstructible (ιL (algebraMap ℚ L q)) := by
    simpa [ιL] using ComplexConstructible.of_rat q
  have hfin : Module.finrank ℚ L = 2 ^ k := by
    rw [IsCyclotomicExtension.finrank L (Polynomial.cyclotomic.irreducible_rat hn), hk]
  let ζL : L := ⟨ζ, IntermediateField.mem_adjoin_simple_self ℚ ζ⟩
  have hconstructible : ComplexConstructible (ιL ζL) :=
    complexConstructible_of_abelian_two_extension ιL hbase k hfin ζL
  have harg :
      (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) =
        ((2 * Real.pi / (n : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hreal : (ιL ζL).re = Real.cos (2 * Real.pi / n) := by
    change ζ.re = _
    change (Complex.exp (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ))).re = _
    rw [harg]
    exact Complex.exp_ofReal_mul_I_re _
  rw [← hreal]
  exact hconstructible.1

end Submission.Helpers
