import Mathlib
import Submission.BurnsideVanishing

/-!
# Character theory ingredients for Burnside's theorem
-/

namespace Submission.CharTheory

open scoped Classical
noncomputable section

/-!
## Algebraic integrality of character values
-/

/-
A root of unity in ℂ is an algebraic integer.
-/
theorem isIntegral_rootOfUnity (n : ℕ) (hn : 0 < n) (ζ : ℂ) (hζ : ζ ^ n = 1) :
    IsIntegral ℤ ζ := by
  exact ⟨ Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by aesop ⟩

/-
The character of an FDRep at a group element is an algebraic integer.
    This holds because character values are sums of roots of unity.
-/
theorem fdRep_char_isIntegral {G : Type} [Group G] [Fintype G]
    (V : FDRep ℂ G) (g : G) : IsIntegral ℤ (V.character g) := by
  have h_eigenvalues : ∀ ζ : ℂ, ζ ∈ (V.ρ g).charpoly.roots → ∃ n : ℕ, n > 0 ∧ ζ ^ n = 1 := by
    intro ζ hζ
    have h_eigenvalue : ∃ v : V.V, v ≠ 0 ∧ (V.ρ g) v = ζ • v := by
      have h_eigenvalue : ∃ v : V.V, v ≠ 0 ∧ (V.ρ g - ζ • 1) v = 0 := by
        have h_eigenvalue : LinearMap.det (V.ρ g - ζ • 1) = 0 := by
          rw [ LinearMap.det_eq_sign_charpoly_coeff ];
          simp_all +decide [ Polynomial.coeff_zero_eq_eval_zero ];
          convert hζ.2 using 1;
          simp +decide [ LinearMap.charpoly, Matrix.charpoly ];
          simp +decide [ Matrix.det_apply', Polynomial.eval_finset_sum ];
          simp +decide [ Polynomial.eval_prod, Matrix.charmatrix ];
          simp +decide [ Matrix.one_apply ];
          exact Finset.sum_congr rfl fun _ _ => by congr; ext; aesop;
        have := LinearMap.isUnit_det ( V.ρ g - ζ • 1 );
        simp_all +decide [ LinearMap.isUnit_iff_ker_eq_bot ];
        simp_all +decide [ Submodule.eq_bot_iff ];
        tauto;
      simp_all +decide [ sub_eq_iff_eq_add ];
    have h_eigenvalue_pow : ∀ k : ℕ, (V.ρ (g ^ k)) h_eigenvalue.choose = ζ ^ k • h_eigenvalue.choose := by
      intro k; induction k <;> simp_all +decide [ pow_succ', map_mul ] ;
      rw [ h_eigenvalue.choose_spec.2, smul_smul, mul_comm ];
    specialize h_eigenvalue_pow ( orderOf g );
    exact ⟨ orderOf g, orderOf_pos g, by simpa [ h_eigenvalue.choose_spec.1 ] using smul_left_injective _ h_eigenvalue.choose_spec.1 <| by simpa [ h_eigenvalue.choose_spec.1 ] using h_eigenvalue_pow.symm ⟩;
  have h_alg_int : ∀ ζ : ℂ, ζ ∈ (V.ρ g).charpoly.roots → IsIntegral ℤ ζ := by
    exact fun ζ hζ => by obtain ⟨ n, hn, hn' ⟩ := h_eigenvalues ζ hζ; exact ⟨ Polynomial.X ^ n - 1, Polynomial.monic_X_pow_sub_C _ hn.ne', by aesop ⟩ ;
  have h_trace : V.character g = Multiset.sum (Polynomial.roots (V.ρ g).charpoly) := by
    nontriviality;
    unfold FDRep.character;
    have := LinearMap.trace_eq_matrix_trace ℂ ( Module.Free.chooseBasis ℂ V.V );
    rw [ this, Matrix.trace_eq_sum_roots_charpoly ];
    congr 1;
  exact h_trace ▸ IsIntegral.multiset_sum fun x hx => h_alg_int x hx

/-!
## The core character-theoretic fact for Burnside's theorem

Proved using the Wedderburn-based infrastructure from BurnsideVanishing.lean.
-/

/-- The core character-theoretic fact for Burnside's theorem. -/
theorem burnside_char_core {G : Type} [Group G] [Fintype G]
    {q k : ℕ} (hq : Nat.Prime q) (hk : 0 < k)
    (g : G) (hg : g ≠ 1)
    (hindex : (Subgroup.centralizer ({g} : Set G)).index = q ^ k)
    (hsimple : IsSimpleGroup G)
    (hnonabelian : ∃ (p : ℕ), p.Prime ∧ p ≠ q ∧ p ∣ Fintype.card G) :
    IsIntegral ℤ ((q : ℂ)⁻¹) := by
  haveI : DecidableEq G := Classical.decEq _
  exact Submission.BurnsideVanishing.burnside_char_core_proof hq hk g hg hindex hsimple hnonabelian

end
end Submission.CharTheory
