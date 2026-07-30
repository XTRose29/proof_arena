import Submission.Constructible

open LeanEval.NumberTheory.GaussWantzel

namespace Submission.Helpers

/-! A quadratic field is obtained inside `ℂ` by a finite sequence of square
adjunctions starting from `ℚ`. -/

inductive QuadraticField : IntermediateField ℚ ℂ → Prop
  | bot : QuadraticField ⊥
  | adjoin {K : IntermediateField ℚ ℂ} (hK : QuadraticField K) (z : ℂ)
      (hz : z ^ 2 ∈ K) :
      QuadraticField ((IntermediateField.adjoin K {z}).restrictScalars ℚ)

namespace QuadraticField

private lemma integral_of_sq_mem {K : IntermediateField ℚ ℂ} {z : ℂ} (hz : z ^ 2 ∈ K) :
    IsIntegral K z := by
  let a : K := ⟨z ^ 2, hz⟩
  exact ⟨Polynomial.X ^ 2 - Polynomial.C a,
    Polynomial.monic_X_pow_sub_C a two_ne_zero, by simp [a]⟩

lemma common_extension {K L : IntermediateField ℚ ℂ} (hK : QuadraticField K)
    (hL : QuadraticField L) :
    ∃ M : IntermediateField ℚ ℂ, QuadraticField M ∧ K ≤ M ∧ L ≤ M := by
  induction hL with
  | bot => exact ⟨K, hK, le_rfl, bot_le⟩
  | @adjoin L hL z hz ih =>
      obtain ⟨M, hM, hKM, hLM⟩ := ih
      have hzM : z ^ 2 ∈ M := hLM hz
      let N : IntermediateField ℚ ℂ :=
        (IntermediateField.adjoin M {z}).restrictScalars ℚ
      have hN : QuadraticField N := QuadraticField.adjoin hM z hzM
      have hMN : M ≤ N := by
        intro y hy
        exact IntermediateField.algebraMap_mem _ (⟨y, hy⟩ : M)
      have hLN :
          (IntermediateField.adjoin L {z}).restrictScalars ℚ ≤ N := by
        change (IntermediateField.adjoin L {z} : Set ℂ) ⊆
          IntermediateField.adjoin M {z}
        rw [IntermediateField.adjoin_subset_adjoin_iff]
        constructor
        · rintro _ ⟨y, rfl⟩
          exact IntermediateField.algebraMap_mem _ (⟨y, hLM y.2⟩ : M)
        · exact IntermediateField.subset_adjoin M {z}
      exact ⟨N, hN, hKM.trans hMN, hLN⟩

lemma finite_and_isTwoPower_finrank {K : IntermediateField ℚ ℂ} (hK : QuadraticField K) :
    Module.Finite ℚ K ∧ IsTwoPower (Module.finrank ℚ K) := by
  induction hK with
  | bot => exact ⟨inferInstance, ⟨0, by simp⟩⟩
  | @adjoin K hK z hz ih =>
      obtain ⟨hKfinite, k, hk⟩ := ih
      letI : Module.Finite ℚ K := hKfinite
      have hzint : IsIntegral K z := integral_of_sq_mem hz
      let A : IntermediateField K ℂ := IntermediateField.adjoin K {z}
      letI : FiniteDimensional K A := IntermediateField.adjoin.finiteDimensional hzint
      letI : Module.Free K A := Module.Free.of_divisionRing K A
      letI : Module.Finite ℚ A := Module.Finite.trans K A
      let B : IntermediateField ℚ ℂ := A.restrictScalars ℚ
      let e : B ≃ₐ[ℚ] A :=
        { toFun := fun x ↦ ⟨x.1, x.2⟩
          invFun := fun x ↦ ⟨x.1, x.2⟩
          left_inv := fun _ ↦ rfl
          right_inv := fun _ ↦ rfl
          map_mul' := fun _ _ ↦ rfl
          map_add' := fun _ _ ↦ rfl
          commutes' := fun _ ↦ rfl }
      have hmin_dvd : minpoly K z ∣ Polynomial.X ^ 2 - Polynomial.C (⟨z ^ 2, hz⟩ : K) := by
        apply minpoly.dvd
        simp
      have hdegree : (minpoly K z).natDegree ≤ 2 := by
        have hle := Polynomial.natDegree_le_of_dvd hmin_dvd
          (Polynomial.monic_X_pow_sub_C (⟨z ^ 2, hz⟩ : K) two_ne_zero).ne_zero
        simpa using hle
      have hrel_le : Module.finrank K A ≤ 2 := by
        rw [show A = IntermediateField.adjoin K {z} from rfl,
          IntermediateField.adjoin.finrank hzint]
        exact hdegree
      have hrel : Module.finrank K A = 1 ∨ Module.finrank K A = 2 := by
        have hpos : 0 < Module.finrank K A := Module.finrank_pos
        omega
      have htower :
          Module.finrank ℚ ((IntermediateField.adjoin K {z}).restrictScalars ℚ) =
            Module.finrank ℚ K * Module.finrank K A := by
        calc
          Module.finrank ℚ ((IntermediateField.adjoin K {z}).restrictScalars ℚ) =
              Module.finrank ℚ B := by rfl
          _ = Module.finrank ℚ A := e.toLinearEquiv.finrank_eq
          _ = Module.finrank ℚ K * Module.finrank K A :=
            (Module.finrank_mul_finrank ℚ K A).symm
      have hfinite :
          Module.Finite ℚ ((IntermediateField.adjoin K {z}).restrictScalars ℚ) := by
        change Module.Finite ℚ B
        exact Module.Finite.equiv e.symm.toLinearEquiv
      constructor
      · exact hfinite
      · rcases hrel with hrel | hrel
        · exact ⟨k, by rw [htower, hk, hrel, mul_one]⟩
        · exact ⟨k + 1, by rw [htower, hk, hrel, pow_succ]⟩

end QuadraticField

def HasQuadraticField (z : ℂ) : Prop :=
  ∃ K : IntermediateField ℚ ℂ, QuadraticField K ∧ z ∈ K

namespace HasQuadraticField

lemma of_rat (q : ℚ) : HasQuadraticField (algebraMap ℚ ℂ q) := by
  exact ⟨⊥, QuadraticField.bot, IntermediateField.algebraMap_mem _ q⟩

lemma add {z w : ℂ} (hz : HasQuadraticField z) (hw : HasQuadraticField w) :
    HasQuadraticField (z + w) := by
  obtain ⟨K, hK, hzK⟩ := hz
  obtain ⟨L, hL, hwL⟩ := hw
  obtain ⟨M, hM, hKM, hLM⟩ := hK.common_extension hL
  exact ⟨M, hM, M.add_mem (hKM hzK) (hLM hwL)⟩

lemma neg {z : ℂ} (hz : HasQuadraticField z) : HasQuadraticField (-z) := by
  obtain ⟨K, hK, hzK⟩ := hz
  exact ⟨K, hK, K.neg_mem hzK⟩

lemma sub {z w : ℂ} (hz : HasQuadraticField z) (hw : HasQuadraticField w) :
    HasQuadraticField (z - w) := by
  rw [sub_eq_add_neg]
  exact hz.add hw.neg

lemma mul {z w : ℂ} (hz : HasQuadraticField z) (hw : HasQuadraticField w) :
    HasQuadraticField (z * w) := by
  obtain ⟨K, hK, hzK⟩ := hz
  obtain ⟨L, hL, hwL⟩ := hw
  obtain ⟨M, hM, hKM, hLM⟩ := hK.common_extension hL
  exact ⟨M, hM, M.mul_mem (hKM hzK) (hLM hwL)⟩

lemma inv {z : ℂ} (hz : HasQuadraticField z) : HasQuadraticField z⁻¹ := by
  obtain ⟨K, hK, hzK⟩ := hz
  exact ⟨K, hK, K.inv_mem hzK⟩

lemma of_square {z : ℂ} (hz : HasQuadraticField (z ^ 2)) : HasQuadraticField z := by
  obtain ⟨K, hK, hzK⟩ := hz
  let L : IntermediateField ℚ ℂ :=
    (IntermediateField.adjoin K {z}).restrictScalars ℚ
  refine ⟨L, QuadraticField.adjoin hK z hzK, ?_⟩
  exact IntermediateField.subset_adjoin K {z} (Set.mem_singleton z)

lemma I : HasQuadraticField Complex.I := by
  apply of_square
  simpa using of_rat (-1)

lemma sqrt_ofReal {x : ℝ} (hx : HasQuadraticField x) :
    HasQuadraticField (Real.sqrt x) := by
  obtain ⟨K, hK, hxK⟩ := hx
  by_cases hnonneg : 0 ≤ x
  · let z : ℂ := Real.sqrt x
    have hzsq : z ^ 2 ∈ K := by
      have heq : z ^ 2 = (x : ℂ) := by
        calc
          z ^ 2 = Complex.ofRealHom (Real.sqrt x ^ 2) := by
            exact (map_pow Complex.ofRealHom (Real.sqrt x) 2).symm
          _ = Complex.ofRealHom x := congrArg Complex.ofRealHom (Real.sq_sqrt hnonneg)
          _ = (x : ℂ) := rfl
      rw [heq]
      exact hxK
    let L : IntermediateField ℚ ℂ :=
      (IntermediateField.adjoin K {z}).restrictScalars ℚ
    refine ⟨L, QuadraticField.adjoin hK z hzsq, ?_⟩
    exact IntermediateField.subset_adjoin K {z} (Set.mem_singleton z)
  · rw [Real.sqrt_eq_zero_of_nonpos (le_of_not_ge hnonneg)]
    exact ⟨K, hK, K.zero_mem⟩

lemma of_isConstructible {x : ℝ} (hx : IsConstructible x) : HasQuadraticField x := by
  induction hx with
  | base q => simpa using of_rat q
  | add hx hy ihx ihy => simpa using ihx.add ihy
  | neg hx ih => simpa using ih.neg
  | mul hx hy ihx ihy => simpa using ihx.mul ihy
  | inv hx ih => simpa using ih.inv
  | sqrt hx ih => exact ih.sqrt_ofReal

end HasQuadraticField

lemma isTwoPower_totient_of_isConstructible_cos {n : ℕ} (hn : 3 ≤ n)
    (hcos : IsConstructible (Real.cos (2 * Real.pi / n))) : IsTwoPower n.totient := by
  let θ : ℝ := 2 * Real.pi / n
  have hnR : (2 : ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
  have hnRpos : (0 : ℝ) < n := by positivity
  have hθnonneg : 0 ≤ θ := by
    dsimp [θ]
    positivity
  have hθle : θ ≤ Real.pi := by
    dsimp [θ]
    rw [div_le_iff₀ hnRpos]
    nlinarith [Real.pi_pos]
  have hsin_nonneg : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθnonneg hθle
  have hone : IsConstructible (1 : ℝ) := by
    simpa using IsConstructible.base (1 : ℚ)
  have hrad : IsConstructible (Real.sqrt (1 - Real.cos θ ^ 2)) := by
    simpa [θ, pow_two, sub_eq_add_neg] using (hone.add (hcos.mul hcos).neg).sqrt
  have hsineq : Real.sqrt (1 - Real.cos θ ^ 2) = Real.sin θ := by
    rw [← Real.abs_sin_eq_sqrt_one_sub_cos_sq, abs_of_nonneg hsin_nonneg]
  have hsin : IsConstructible (Real.sin θ) := by
    rw [← hsineq]
    exact hrad
  let ζ : ℂ := Complex.exp (2 * Real.pi * Complex.I / n)
  have harg :
      (2 * (Real.pi : ℂ) * Complex.I / (n : ℂ)) = (θ : ℂ) * Complex.I := by
    dsimp [θ]
    push_cast
    ring
  have hζeq : ζ = (Real.cos θ : ℂ) + (Real.sin θ : ℂ) * Complex.I := by
    dsimp [ζ]
    rw [harg, Complex.exp_ofReal_mul_I]
  have hζfield : HasQuadraticField ζ := by
    rw [hζeq]
    exact (HasQuadraticField.of_isConstructible hcos).add
      ((HasQuadraticField.of_isConstructible hsin).mul HasQuadraticField.I)
  obtain ⟨K, hK, hζK⟩ := hζfield
  obtain ⟨hKfinite, hKdegree⟩ := hK.finite_and_isTwoPower_finrank
  letI : Module.Finite ℚ K := hKfinite
  have hnpos : 0 < n := by omega
  have hζ : IsPrimitiveRoot ζ n := Complex.isPrimitiveRoot_exp n hnpos.ne'
  have hζalg : IsAlgebraic ℚ ζ := by
    exact ⟨Polynomial.X ^ n - 1,
      (Polynomial.monic_X_pow_sub_C (1 : ℚ) hnpos.ne').ne_zero, by simp [hζ.pow_eq_one]⟩
  have hdegree_adjoin : Module.finrank ℚ (IntermediateField.adjoin ℚ {ζ}) = n.totient := by
    rw [IntermediateField.adjoin.finrank hζalg.isIntegral,
      ← Polynomial.cyclotomic_eq_minpoly_rat hζ hnpos,
      Polynomial.natDegree_cyclotomic]
  have hadjoin_le : IntermediateField.adjoin ℚ {ζ} ≤ K := by
    rw [IntermediateField.adjoin_le_iff]
    simpa using hζK
  have hdvd : n.totient ∣ Module.finrank ℚ K := by
    rw [← hdegree_adjoin]
    exact IntermediateField.finrank_dvd_of_le_right hadjoin_le
  obtain ⟨m, hm⟩ := hKdegree
  rw [hm] at hdvd
  obtain ⟨j, _, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  exact ⟨j, hj⟩

end Submission.Helpers
