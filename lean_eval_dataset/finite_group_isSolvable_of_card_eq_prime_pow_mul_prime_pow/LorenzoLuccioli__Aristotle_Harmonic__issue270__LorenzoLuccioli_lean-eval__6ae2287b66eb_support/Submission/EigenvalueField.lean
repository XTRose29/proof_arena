import Mathlib
import Submission.BurnsideVanishingHelpers

/-!
# Eigenvalue field approach for norm-one bound
-/

set_option maxHeartbeats 1600000

open scoped Classical
noncomputable section

namespace Submission.EigenvalueField

open Submission.BurnsideVanishingHelpers

lemma alg_hom_preserves_root_of_unity
    (K : IntermediateField ℚ ℂ) (σ : K →ₐ[ℚ] ℂ)
    (ε : K) (N : ℕ) (hε : (ε : ℂ) ^ N = 1) :
    (σ ε) ^ N = 1 := by
  have : ε ^ N = 1 := Subtype.ext (by simpa using hε)
  rw [show σ ε ^ N = σ (ε ^ N) from (map_pow σ ε N).symm, this, map_one]

lemma embedding_bound_from_roots_of_unity
    (K : IntermediateField ℚ ℂ) (σ : K →ₐ[ℚ] ℂ)
    (roots : Multiset K) (d : ℕ) (hd : 0 < d)
    (N : ℕ) (hN : 0 < N)
    (hroots : ∀ ε ∈ roots, (ε : ℂ) ^ N = 1)
    (hcard : roots.card = d)
    (x : K) (hx : (x : ℂ) = (roots.sum : ℂ) / (d : ℂ)) :
    ‖σ x‖ ≤ 1 := by
  -- By hypothesis, σ(x) = σ(roots.sum) / σ(d).
  have hσx : σ x = (Multiset.map σ roots).sum / (d : ℂ) := by
    convert congr_arg σ ( show x = roots.sum / d from Subtype.ext hx ) using 1;
    simp +decide [ div_eq_mul_inv, map_multiset_sum ];
  have hσ_sum : ‖(Multiset.map σ roots).sum‖ ≤ d := by
    have hσ_sum : ∀ ε ∈ roots, ‖σ ε‖ = 1 := by
      intro ε hε; specialize hroots ε hε; have := alg_hom_preserves_root_of_unity K σ ε N hroots; exact norm_root_of_unity _ _ hN this;
    have hσ_sum : ∀ (s : Multiset ℂ), (∀ ε ∈ s, ‖ε‖ = 1) → ‖s.sum‖ ≤ s.card := by
      exact fun s hs => le_trans ( norm_multiset_sum_le _ ) ( by aesop );
    specialize hσ_sum (Multiset.map σ roots) ; aesop;
  simp_all +decide [ div_le_iff₀, hd.ne' ]

/-
The combined norm-one lemma using the eigenvalue field approach.
-/
theorem norm_one_of_trace_div_dim {di : ℕ} (hdi : 0 < di)
    (M : Matrix (Fin di) (Fin di) ℂ) (N : ℕ) (hN : 0 < N) (hM : M ^ N = 1)
    (α : ℂ) (hα : α = Matrix.trace M / (di : ℂ))
    (hint : IsIntegral ℤ α) (hα_ne : α ≠ 0) :
    ‖α‖ = 1 := by
  -- Let S = (↑M.charpoly.roots.toFinset ∪ {α} : Set ℂ). Let K = IntermediateField.adjoin ℚ S.
  set S : Set ℂ := (M.charpoly.roots.toFinset : Set ℂ) ∪ {α}
  set K : IntermediateField ℚ ℂ := IntermediateField.adjoin ℚ S;
  -- Each eigenvalue ε of M satisfies ε^N = 1.
  have h_eigenvalue_root_of_unity : ∀ ε ∈ M.charpoly.roots, (ε : ℂ) ^ N = 1 := by
    intro ε hε
    obtain ⟨v, hv⟩ : ∃ v : Fin di → ℂ, v ≠ 0 ∧ M.mulVec v = ε • v := by
      have := Matrix.exists_mulVec_eq_zero_iff.mpr ( show Matrix.det ( M - Matrix.scalar ( Fin di ) ε ) = 0 from ?_ );
      · simp_all +decide [ sub_eq_iff_eq_add, Matrix.sub_mulVec ];
      · rw [ Matrix.det_eq_sign_charpoly_coeff ];
        simp_all +decide [ Matrix.charpoly, Matrix.det_apply' ];
        convert hε.2 using 1;
        simp +decide [ Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_prod, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_one, Polynomial.coeff_zero_eq_eval_zero ];
        exact Finset.sum_congr rfl fun _ _ => by congr; ext; by_cases h : ‹Equiv.Perm ( Fin di ) › ‹_› = ‹_› <;> simp +decide [ h ] ;
    -- Applying M^N to v gives ε^N • v.
    have h_apply_MN : (M ^ N).mulVec v = ε ^ N • v := by
      refine' Nat.recOn N _ _ <;> simp_all +decide [ pow_succ', Matrix.mulVec_smul ];
      intro n hn; simp_all +decide [ ← Matrix.mulVec_mulVec, mul_assoc ] ;
      rw [ Matrix.mulVec_smul, hv.2, smul_smul, mul_comm ];
    exact smul_left_injective _ hv.1 <| by simpa [ hM ] using h_apply_MN.symm;
  have h_finiteDimensional : FiniteDimensional ℚ K := by
    have h_finiteDimensional : Set.Finite S ∧ ∀ ε ∈ S, IsIntegral ℚ ε := by
      refine' ⟨ Set.toFinite _, _ ⟩;
      intro ε hε
      cases' hε with hε_root hε_alpha;
      · exact ⟨ Polynomial.X ^ N - 1, Polynomial.monic_X_pow_sub_C _ hN.ne', by aesop ⟩;
      · exact hε_alpha.symm ▸ IsIntegral.tower_top ( R := ℤ ) ( by simpa using ‹IsIntegral ℤ α› );
    convert IntermediateField.finiteDimensional_adjoin h_finiteDimensional.2;
  -- Lift α to x : K via ⟨α, IntermediateField.subset_adjoin _ _ (Set.mem_union_right _ rfl)⟩.
  obtain ⟨x, hx⟩ : ∃ x : K, (x : ℂ) = α := by
    exact ⟨ ⟨ α, IntermediateField.subset_adjoin ℚ S <| Set.mem_union_right _ <| Set.mem_singleton _ ⟩, rfl ⟩;
  -- Lift M.charpoly.roots to a Multiset K. For each ε ∈ M.charpoly.roots, ε ∈ S (via toFinset). So ε ∈ K via IntermediateField.subset_adjoin. Define roots_K = M.charpoly.roots.map (fun ε => (⟨ε, proof⟩ : K)).
  obtain ⟨roots_K, hroots_K⟩ : ∃ roots_K : Multiset K, (roots_K.map (fun ε => (ε : ℂ))) = M.charpoly.roots ∧ roots_K.card = di := by
    have h_roots_K : ∃ roots_K : Multiset K, (roots_K.map (fun ε => (ε : ℂ))) = M.charpoly.roots := by
      have h_roots_K : ∀ ε ∈ M.charpoly.roots, ∃ ε' : K, (ε' : ℂ) = ε := by
        exact fun ε hε => ⟨ ⟨ ε, IntermediateField.subset_adjoin ℚ S <| Set.mem_union_left _ <| Multiset.mem_toFinset.mpr hε ⟩, rfl ⟩;
      choose! f hf using h_roots_K;
      use Multiset.map f M.charpoly.roots;
      simp +zetaDelta at *;
      rw [ Multiset.map_congr rfl ];
      exacts [ Multiset.map_id _, fun x hx => hf x ( by exact Matrix.charpoly_monic M |> fun h => h.ne_zero ) ( by exact Polynomial.isRoot_of_mem_roots hx ) ];
    obtain ⟨ roots_K, hroots_K ⟩ := h_roots_K; use roots_K; simp_all +decide [ Matrix.charpoly_degree_eq_dim ] ;
    have h_card_roots : Multiset.card M.charpoly.roots = di := by
      have h_card_roots : Multiset.card M.charpoly.roots = Polynomial.natDegree M.charpoly := by
        exact IsAlgClosed.card_roots_eq_natDegree;
      rw [ h_card_roots, Matrix.charpoly_natDegree_eq_dim ] ; aesop;
    rw [ ← h_card_roots, ← hroots_K, Multiset.card_map ];
  -- The lift x : K satisfies (x : ℂ) = (roots_K.sum : ℂ) / (di : ℂ).
  have hx_sum : (x : ℂ) = (roots_K.sum : ℂ) / (di : ℂ) := by
    have h_trace_eq_sum_roots : Matrix.trace M = Multiset.sum (M.charpoly.roots) := by
      exact Matrix.trace_eq_sum_roots_charpoly M;
    simp_all +decide [ Multiset.sum_map_mul_right ];
  -- Each σ : K →ₐ[ℚ] ℂ gives ‖σ x‖ ≤ 1 by embedding_bound_from_roots_of_unity.
  have h_embedding_bound : ∀ σ : K →ₐ[ℚ] ℂ, ‖σ x‖ ≤ 1 := by
    intros σ
    apply embedding_bound_from_roots_of_unity K σ roots_K di hdi N hN;
    · intro ε hε; replace hroots_K := congr_arg Multiset.toFinset hroots_K.1; rw [ Finset.ext_iff ] at hroots_K; specialize hroots_K ε; aesop;
    · exact hroots_K.2;
    · exact hx_sum;
  have h_norm_one : ‖(x : ℂ)‖ = 1 := by
    apply norm_one_of_integral_embeddings_bounded K x (by
    exact fun h => hα_ne <| hx ▸ h ▸ rfl) (by
    convert ‹IsIntegral ℤ α› using 1) h_embedding_bound;
  exact hx ▸ h_norm_one

end Submission.EigenvalueField
