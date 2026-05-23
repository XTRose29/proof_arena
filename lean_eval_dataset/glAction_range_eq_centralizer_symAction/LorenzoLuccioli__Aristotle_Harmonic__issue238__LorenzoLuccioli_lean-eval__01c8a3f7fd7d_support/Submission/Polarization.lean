import ChallengeDeps
import Submission.Interpolation
import Submission.TensorExpansion
import Submission.IdempotentShift
import Submission.DiagMapTarget

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Proof that diagonal maps are in the GL-algebra
-/

open LeanEval.RepresentationTheory Finset
open scoped TensorProduct

namespace Submission.Polarization

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
  {k : ℕ} [Invertible (k.factorial : R)]

/-- If f is a unit, then f^⊗k is in the algebra. -/
lemma map_isUnit_mem (f : M →ₗ[R] M) (hf : IsUnit f) :
    PiTensorProduct.map (fun (_ : Fin k) => f) ∈
    Algebra.adjoin R (Set.range (glAction R M k)) := by
  obtain ⟨g, rfl⟩ := hf; exact Algebra.subset_adjoin ⟨g, rfl⟩

/-- The identity map's tensor power is in the algebra (it's the algebra's 1). -/
lemma map_id_mem :
    PiTensorProduct.map (fun (_ : Fin k) => (LinearMap.id : M →ₗ[R] M)) ∈
    Algebra.adjoin R (Set.range (glAction R M k)) := by
  apply map_isUnit_mem
  exact isUnit_one

/-
For nilpotent N, N^⊗k is in the algebra.
-/
lemma map_nilpotent_mem (N : M →ₗ[R] M) (hN : IsNilpotent N) :
    PiTensorProduct.map (fun (_ : Fin k) => N) ∈
    Algebra.adjoin R (Set.range (glAction R M k)) := by
  obtain ⟨ m, hm ⟩ := hN
  have h_unit : ∀ j : ℕ, IsUnit (1 + (j : R) • N) := by
    intro j
    have h_nilpotent : IsNilpotent ((j : R) • N) := by
      use m; rw [smul_pow, hm, smul_zero]
    exact h_nilpotent.isUnit_one_add
  have h_lhs : (k.factorial : R) • (PiTensorProduct.map (fun (_ : Fin k) => N)) ∈
      Algebra.adjoin R (Set.range (glAction R M k)) := by
    have h_sum : ∑ j ∈ Finset.range (k + 1),
        ((-1 : R) ^ (k - j) * (k.choose j : R)) •
        (PiTensorProduct.map (fun (_ : Fin k) => (1 + (j : R) • N))) ∈
        Algebra.adjoin R (Set.range (glAction R M k)) :=
      Subalgebra.sum_mem _ fun j _ => Subalgebra.smul_mem _ (map_isUnit_mem _ (h_unit j)) _
    rw [show (k.factorial : R) • PiTensorProduct.map (fun _ : Fin k => N) =
      ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k - j) * (k.choose j : R)) •
        PiTensorProduct.map (fun _ : Fin k => 1 + (j : R) • N) from by
      rw [← Submission.TensorExpansion.alternating_binom_map_eq]]
    exact h_sum
  have : ⅟ (k.factorial : R) • ((k.factorial : R) •
    PiTensorProduct.map (fun _ : Fin k => N)) =
    PiTensorProduct.map (fun _ : Fin k => N) := by
    simp [← smul_assoc]
  rw [← this]
  exact Subalgebra.smul_mem _ h_lhs _

omit [FiniteDimensional R M] in
/-
Given the alternating sum formula and that g^⊗k ∈ A and (f+j•g)^⊗k ∈ A for j=1,...,k,
    then f^⊗k ∈ A.
-/
lemma extract_from_alternating_sum (f g : M →ₗ[R] M)
    (hg : PiTensorProduct.map (fun _ : Fin k => g) ∈
      Algebra.adjoin R (Set.range (glAction R M k)))
    (hfg : ∀ j : ℕ, 1 ≤ j → j ≤ k →
      PiTensorProduct.map (fun _ : Fin k => f + (j : R) • g) ∈
        Algebra.adjoin R (Set.range (glAction R M k))) :
    PiTensorProduct.map (fun (_ : Fin k) => f) ∈
    Algebra.adjoin R (Set.range (glAction R M k)) := by
  have h_sum : ∑ j ∈ Finset.range (k + 1), ((-1 : R) ^ (k - j) * (k.choose j : R)) • PiTensorProduct.map (fun (_ : Fin k) => f + (j : R) • g) = (k.factorial : R) • PiTensorProduct.map (fun (_ : Fin k) => g) := by
    exact Submission.TensorExpansion.alternating_binom_map_eq k f g
  have h_isolate : (-1 : R) ^ k • PiTensorProduct.map (fun (_ : Fin k) => f) =
      (k.factorial : R) • PiTensorProduct.map (fun (_ : Fin k) => g) -
      ∑ j ∈ Finset.Ico 1 (k + 1),
        ((-1 : R) ^ (k - j) * (k.choose j : R)) •
          PiTensorProduct.map (fun (_ : Fin k) => f + (j : R) • g) := by
            rw [ ← h_sum, Finset.sum_Ico_eq_sub _ ] <;> simp +decide [ Finset.sum_range_succ' ];
  have h_isolate : (-1 : R) ^ k • PiTensorProduct.map (fun (_ : Fin k) => f) ∈ Algebra.adjoin R (Set.range (glAction R M k)) := by
    exact h_isolate.symm ▸ Subalgebra.sub_mem _ ( Subalgebra.smul_mem _ hg _ ) ( Subalgebra.sum_mem _ fun j hj => Subalgebra.smul_mem _ ( hfg j ( Finset.mem_Ico.mp hj |>.1 ) ( Nat.le_of_lt_succ ( Finset.mem_Ico.mp hj |>.2 ) ) ) _ );
  convert Subalgebra.smul_mem _ h_isolate ( ( -1 : R ) ^ k ) using 1 ; simp +decide [ smul_smul ];
  norm_num [ ← mul_pow ]

/-- If all shifts f + j (j=1,...,k) are units, then f^⊗k ∈ A. -/
lemma diag_map_mem_adjoin_of_shifts_isUnit (f : M →ₗ[R] M)
    (hf : ∀ j : ℕ, 1 ≤ j → j ≤ k → IsUnit (f + (j : R) • LinearMap.id)) :
    PiTensorProduct.map (fun (_ : Fin k) => f) ∈
    Algebra.adjoin R (Set.range (glAction R M k)) := by
  apply extract_from_alternating_sum f LinearMap.id map_id_mem
  intro j hj1 hjk
  exact map_isUnit_mem _ (hf j hj1 hjk)

/-- Products of constant PiTensorProduct.maps compose. -/
lemma map_const_mul (f g : M →ₗ[R] M) :
    PiTensorProduct.map (fun (_ : Fin k) => f) * PiTensorProduct.map (fun (_ : Fin k) => g) =
    PiTensorProduct.map (fun (_ : Fin k) => f ∘ₗ g) := by
  ext; simp +decide [PiTensorProduct.map_tprod]

/-
For any idempotent e, the diagonal tensor power map e^⊗k is in the GL algebra.
-/
lemma idem_diag_mem_adjoin (e : Module.End R M) (he : e * e = e) :
    PiTensorProduct.map (fun (_ : Fin k) => e) ∈
    Algebra.adjoin R (Set.range (glAction R M k)) := by
  by_cases he0 : e = 0;
  · exact map_nilpotent_mem e ( by simp +decide [ he, he0 ] );
  · by_cases he1 : e = 1;
    · aesop;
    · -- Otherwise e ≠ 0, e ≠ 1. We need to find a unit u such that e + j • ↑u is a unit for all j = 1,...,k.
      obtain ⟨u, hu⟩ : ∃ u : (Module.End R M)ˣ, IsNilpotent (↑u⁻¹ * e) := by
        exact?;
      -- Then e + j • ↑u = j • ↑u * (1 + j⁻¹ • (↑u⁻¹ * e)) is a unit because:
      -- - j ≠ 0 in R (since Invertible k! means char > k ≥ j ≥ 1)
      -- - u is a unit
      -- - 1 + nilpotent is a unit (IsNilpotent.isUnit_one_add)
      have h_unit : ∀ j : ℕ, 1 ≤ j → j ≤ k → IsUnit (e + (j : R) • (u : Module.End R M)) := by
        intro j hj1 hjk
        have h_unit : IsUnit (1 + (j : R)⁻¹ • (↑u⁻¹ * e)) := by
          have h_unit : IsNilpotent ((j : R)⁻¹ • (↑u⁻¹ * e)) := by
            obtain ⟨ n, hn ⟩ := hu;
            refine' ⟨ n, _ ⟩;
            rw [ smul_pow, hn, smul_zero ];
          exact?;
        have h_unit : IsUnit ((j : R) • (u : Module.End R M) * (1 + (j : R)⁻¹ • (↑u⁻¹ * e))) := by
          refine' IsUnit.mul _ h_unit;
          have h_unit : IsUnit (j : R) := by
            have h_unit : (j : R) ≠ 0 := by
              intro h;
              have h_contra : (k.factorial : R) = 0 := by
                rw [ ← Nat.mul_div_cancel' ( Nat.dvd_factorial ( by linarith ) hjk ), Nat.cast_mul, h, MulZeroClass.zero_mul ];
              exact absurd h_contra ( by have := Invertible.ne_zero ( k.factorial : R ) ; aesop );
            exact isUnit_iff_ne_zero.mpr h_unit;
          exact IsUnit.smul ( Units.mk0 _ h_unit.ne_zero ) u.isUnit;
        convert h_unit using 1 ; simp +decide [ mul_add, add_mul, mul_assoc, mul_left_comm, ne_of_gt ( zero_lt_one.trans_le hj1 ) ] ; abel_nf;
        nontriviality;
        rw [ inv_smul_smul₀ ( by aesop ) ] ; abel_nf;
      apply extract_from_alternating_sum e (u : Module.End R M);
      · exact map_isUnit_mem _ u.isUnit;
      · exact fun j hj₁ hj₂ => map_isUnit_mem _ ( h_unit j hj₁ hj₂ )

set_option maxHeartbeats 800000

/-
For any `f : M →ₗ[R] M`, the diagonal tensor power map is in the GL algebra.
-/
lemma diag_map_mem_adjoin (f : M →ₗ[R] M) :
    PiTensorProduct.map (fun (_ : Fin k) => f) ∈
    Algebra.adjoin R (Set.range (glAction R M k)) := by
  -- By the lemma `exists_unit_mul_idem`, there exists a unit `u` and an idempotent `e` such that `f = u * e`.
  obtain ⟨u, e, he, hf⟩ : ∃ (u : (Module.End R M)ˣ) (e : Module.End R M), e * e = e ∧ f = u * e := by
    exact?;
  -- By the lemma `map_const_mul`, we have PiTensorProduct.map (fun _ : Fin k => f) = PiTensorProduct.map (fun _ : Fin k => u) * PiTensorProduct.map (fun _ : Fin k => e).
  have h_map_mul : PiTensorProduct.map (fun _ : Fin k => f) = PiTensorProduct.map (fun _ : Fin k => (u : M →ₗ[R] M)) * PiTensorProduct.map (fun _ : Fin k => e) := by
    ext; simp [hf, map_const_mul];
  exact h_map_mul.symm ▸ Subalgebra.mul_mem _ ( map_isUnit_mem _ u.isUnit ) ( idem_diag_mem_adjoin _ he )

end Submission.Polarization
