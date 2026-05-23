/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: brauer_character_in_cyclotomic
user: sqrt-of-2
model: Aristotle (Harmonic)
submission_repo: sqrt-of-2/10151d147aef1f8bd884d245442a3a12
submission_ref: bd0142e19e36f3a42be5761dc04dc634e88d820e
issue_number: 216
-/
import Mathlib

namespace Submission

/-
Over an algebraically closed field, the trace of a linear map equals
    the sum of the roots of its characteristic polynomial.
-/
lemma trace_eq_sum_charpoly_roots {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) :
    (LinearMap.trace K V) f = f.charpoly.roots.sum := by
  convert Matrix.trace_eq_sum_roots_charpoly _;
  · exact?;
  · infer_instance

/-
If `f ^ n = 1` (as a linear map), then every root of `f.charpoly` satisfies `μ ^ n = 1`.
-/
lemma charpoly_root_pow_eq_one {K V : Type*} [Field K] [IsAlgClosed K]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V]
    (f : V →ₗ[K] V) (n : ℕ) (hf : f ^ n = 1) (μ : K) (hμ : μ ∈ f.charpoly.roots) :
    μ ^ n = 1 := by
  -- Since μ is an eigenvalue of f, there exists a nonzero vector v such that f v = μ • v.
  obtain ⟨v, hv⟩ : ∃ v : V, v ≠ 0 ∧ f v = μ • v := by
    have h_eigenvalue : ∃ v : V, v ≠ 0 ∧ f v = μ • v := by
      have h_eigenvalue_def : ∃ v : V, v ≠ 0 ∧ (f - μ • 1) v = 0 := by
        have h_eigenvalue_def : LinearMap.det (f - μ • 1) = 0 := by
          rw [ LinearMap.det_eq_sign_charpoly_coeff ];
          simp_all +decide [ LinearMap.charpoly, Matrix.charpoly ];
          convert hμ.2 using 1;
          simp +decide [ Matrix.det_apply', Polynomial.eval_finset_sum ];
          simp +decide [ Polynomial.coeff_zero_eq_eval_zero, Polynomial.eval_prod ];
          exact Finset.sum_congr rfl fun _ _ => by congr; ext; by_cases h : ‹Equiv.Perm ( Module.Free.ChooseBasisIndex K V ) › ‹_› = ‹_› <;> simp +decide [ h ] ;
        have := LinearMap.isUnit_det ( f - μ • 1 );
        simp_all +decide [ LinearMap.isUnit_iff_ker_eq_bot ];
        simp_all +decide [ Submodule.eq_bot_iff ];
        tauto
      simp_all +decide [ sub_eq_zero ];
    exact h_eigenvalue;
  -- Since $f^n = id$, we have $f^n(v) = v$ for any vector $v$.
  have h_fn : f^[n] v = v := by
    convert congr_arg ( fun g : V →ₗ[K] V => g v ) hf;
    exact?;
  -- Since $f(v) = μ • v$, we have $f^n(v) = μ^n • v$.
  have h_fn_v : f^[n] v = μ^n • v := by
    refine' Nat.recOn n _ _ <;> simp_all +decide [ pow_succ', Function.iterate_succ_apply', smul_smul ];
    exact fun _ _ => mul_comm _ _;
  exact smul_left_injective _ hv.1 ( by aesop )

/-
Every `n`-th root of unity in `ℂ` lies in the range of any `ℚ`-algebra map from
    `CyclotomicField n ℚ` into `ℂ`, provided `n ≠ 0`.
-/
lemma root_of_unity_mem_cyclotomic_range
    (n : ℕ) (hn : n ≠ 0)
    (φ : CyclotomicField n ℚ →ₐ[ℚ] ℂ)
    (ω : ℂ) (hω : ω ^ n = 1) :
    ω ∈ φ.toRingHom.range := by
  -- Since $\zeta$ is a primitive $n$-th root of unity, the set $\{ \zeta^k \mid k = 0, 1, 2, \ldots, n-1 \}$ is precisely the set of $n$-th roots of unity.
  obtain ⟨ζ, hζ⟩ : ∃ ζ : CyclotomicField n ℚ, IsPrimitiveRoot ζ n := by
    have h_cyclotomic : IsCyclotomicExtension {n} ℚ (CyclotomicField n ℚ) := by
      exact CyclotomicField.instIsCyclotomicExtensionSingletonNatSetOfCharZero n ℚ
    have := h_cyclotomic;
    cases this ; aesop
  have h_roots_of_unity : ∀ ω : ℂ, ω ^ n = 1 → ∃ k : Fin n, ω = (φ ζ) ^ (k : ℕ) := by
    intro ω hω
    have h_roots_of_unity : Finset.image (fun k : Fin n => (φ ζ) ^ (k : ℕ)) (Finset.univ : Finset (Fin n)) = Multiset.toFinset (Polynomial.roots (Polynomial.X ^ n - 1 : Polynomial ℂ)) := by
      refine' Finset.eq_of_subset_of_card_le ( _ ) _;
      · simp_all +decide [ Finset.subset_iff ];
        exact fun a => ⟨ ne_of_apply_ne ( Polynomial.eval 0 ) ( by norm_num [ hn ] ), by rw [ ← pow_mul, Nat.mul_comm, pow_mul, show φ ζ ^ n = 1 from by simpa [ ← map_pow ] using congr_arg ( φ ) ( hζ.pow_eq_one ) ] ; norm_num ⟩;
      · rw [ Finset.card_image_of_injective _ fun a b h => _ ];
        · exact le_trans ( Multiset.toFinset_card_le _ ) ( le_trans ( Polynomial.card_roots' _ ) ( by erw [ Polynomial.natDegree_X_pow_sub_C ] ; simpa ) );
        · intro a b hab; have := hζ.pow_inj ( Fin.is_lt a ) ( Fin.is_lt b ) ; simp_all +decide [ ← map_pow ] ;
          exact Fin.ext ( this <| by simpa [ hn ] using φ.injective hab );
    replace h_roots_of_unity := Finset.ext_iff.mp h_roots_of_unity ω; simp_all +decide [ sub_eq_iff_eq_add ] ;
    exact h_roots_of_unity.mpr ( ne_of_apply_ne Polynomial.natDegree <| by aesop ) |> fun ⟨ k, hk ⟩ => ⟨ k, hk.symm ⟩;
  obtain ⟨ k, rfl ⟩ := h_roots_of_unity ω hω; exact ⟨ ζ ^ ( k : ℕ ), by simp +decide ⟩ ;

theorem brauer_character_in_cyclotomic (G : Type) [Group G] [Fintype G] :
    ∃ φ : CyclotomicField (Monoid.exponent G) ℚ →+* ℂ,
      ∀ (V : Type) (_ : AddCommGroup V) (_ : Module ℂ V) (_ : FiniteDimensional ℂ V)
        (ρ : Representation ℂ G V) (g : G),
        LinearMap.trace ℂ V (ρ g) ∈ φ.range := by
  constructor;
  intro V _ _ _ ρ g;
  have h_trace : (LinearMap.trace ℂ V) (ρ g) = (ρ g).charpoly.roots.sum := by
    convert trace_eq_sum_charpoly_roots ( ρ g ) using 1;
  have h_roots : ∀ μ ∈ (ρ g).charpoly.roots, μ ^ Monoid.exponent G = 1 := by
    apply charpoly_root_pow_eq_one;
    simp +decide [ ← map_pow, Monoid.pow_exponent_eq_one ];
  have h_roots_mem : ∀ μ ∈ (ρ g).charpoly.roots, μ ∈ (IsAlgClosed.lift : CyclotomicField (Monoid.exponent G) ℚ →ₐ[ℚ] ℂ).toRingHom.range := by
    by_cases h : Monoid.exponent G = 0;
    · exact absurd h ( Monoid.exponent_ne_zero_of_finite );
    · exact?;
  convert Subring.multiset_sum_mem _ _ _;
  exacts [ h_trace, h_roots_mem ]

end Submission
