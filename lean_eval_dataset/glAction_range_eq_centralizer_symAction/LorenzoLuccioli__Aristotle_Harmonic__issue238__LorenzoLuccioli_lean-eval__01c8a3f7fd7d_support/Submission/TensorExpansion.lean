import ChallengeDeps
import Submission.Interpolation

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# The finite difference identity for tensor powers
-/

open LeanEval.RepresentationTheory Finset
open scoped TensorProduct

namespace Submission.TensorExpansion

set_option maxHeartbeats 800000

section CommRing

variable {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- The multilinear expansion of tprod. -/
lemma tprod_add_smul_expansion (k : ℕ) (a b : Fin k → M) (c : R) :
    PiTensorProduct.tprod R (fun i => a i + c • b i) =
    ∑ S ∈ Finset.univ.powerset,
      c ^ S.card • PiTensorProduct.tprod R (fun i => if i ∈ S then b i else a i) := by
  have h_expand : (PiTensorProduct.tprod R) (fun i => a i + c • b i) = ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (PiTensorProduct.tprod R) (fun i => if i ∈ S then c • b i else a i) := by
    have h_expand : ∀ (f : Fin k → M), (PiTensorProduct.tprod R) (fun i => f i + c • b i) = ∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), (PiTensorProduct.tprod R) (fun i => if i ∈ S then c • b i else f i) := by
      intro f;
      have := @MultilinearMap.map_sum_finset;
      convert this ( PiTensorProduct.tprod R ) ( fun i => fun j : Fin 2 => if j = 0 then f i else c • b i ) ( fun i => { 0, 1 } ) using 1;
      · simp +decide [ Finset.sum_pair ];
      · refine' Finset.sum_bij ( fun S _ => fun i => if i ∈ S then 1 else 0 ) _ _ _ _ <;> simp +decide;
        · exact fun _ _ => em' _;
        · intro a₁ a₂ h; ext i; replace h := congr_fun h i; aesop;
        · exact fun b hb => ⟨ Finset.univ.filter fun i => b i = 1, funext fun i => by cases hb i <;> simp +decide [ * ] ⟩;
    exact h_expand a;
  rw [ h_expand ];
  refine' Finset.sum_congr rfl fun S _ => _;
  have h_factor : ∀ (f : Fin k → M), (PiTensorProduct.tprod R) (fun i => c ^ (if i ∈ S then 1 else 0) • f i) = c ^ (Finset.card S) • (PiTensorProduct.tprod R) f := by
    intro f
    have h_factor : (PiTensorProduct.tprod R) (fun i => c ^ (if i ∈ S then 1 else 0) • f i) = (∏ i : Fin k, c ^ (if i ∈ S then 1 else 0)) • (PiTensorProduct.tprod R) f := by
      exact?;
    simp_all +decide [ Finset.prod_ite ];
  convert h_factor ( fun i => if i ∈ S then b i else a i ) using 2 ; aesop

end CommRing

section Field

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M]

/-- The main identity on pure tensors. -/
lemma alternating_binom_tprod_eq (k : ℕ) (f g : M →ₗ[R] M) (v : Fin k → M) :
    ∑ j ∈ range (k + 1),
      ((-1 : R) ^ (k - j) * (k.choose j : R)) •
        PiTensorProduct.tprod R (fun i => (f + (j : R) • g) (v i)) =
    (k.factorial : R) • PiTensorProduct.tprod R (fun i => g (v i)) := by
  have hfun : ∀ j : ℕ, (fun i => (f + (j : R) • g) (v i)) = (fun i => f (v i) + (j : R) • g (v i)) :=
    fun j => funext fun i => by simp [LinearMap.add_apply, LinearMap.smul_apply]
  simp_rw [hfun]
  simp_rw [tprod_add_smul_expansion k (fun i => f (v i)) (fun i => g (v i))]
  simp only [Finset.smul_sum, smul_smul]
  rw [Finset.sum_comm]
  rw [Finset.sum_eq_single (Finset.univ : Finset (Fin k))]
  · simp only [Finset.card_univ, Fintype.card_fin, Finset.mem_univ, ite_true]
    rw [← Finset.sum_smul]; congr 1
    exact Submission.Interpolation.alternating_binom_pow_eq_factorial k
  · intro S hS hne
    have hcard : S.card < k := by
      have hsub : S ⊆ Finset.univ := Finset.mem_powerset.mp hS
      exact lt_of_le_of_ne (by simpa using Finset.card_le_card hsub)
        (fun h => hne (Finset.eq_of_subset_of_card_le hsub (by simp [h])))
    have hzero := Submission.Interpolation.alternating_binom_pow_eq_zero (R := R) k S.card hcard
    simp only [← Finset.sum_smul]
    rw [hzero, zero_smul]
  · intro h; exact absurd (Finset.mem_powerset.mpr (Finset.Subset.refl _)) h

/-
The main identity for PiTensorProduct.map.
-/
lemma alternating_binom_map_eq (k : ℕ) (f g : M →ₗ[R] M) :
    ∑ j ∈ range (k + 1),
      ((-1 : R) ^ (k - j) * (k.choose j : R)) •
        PiTensorProduct.map (fun (_ : Fin k) => f + (j : R) • g) =
    (k.factorial : R) • PiTensorProduct.map (fun (_ : Fin k) => g) := by
  refine' PiTensorProduct.ext _;
  convert alternating_binom_tprod_eq k f g using 1;
  simp +decide [ funext_iff, MultilinearMap.ext_iff ]

end Field

end Submission.TensorExpansion
