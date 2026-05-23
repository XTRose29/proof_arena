import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Multilinear polarization and spanning for PiTensorProduct

Standalone file for theorem proving subagent.
-/

open Finset
open scoped TensorProduct

namespace Submission.MultilinearPol

variable {R : Type*} [CommRing R]
  {M : Type*} [AddCommGroup M] [Module R M]
  {k : ℕ}

set_option maxHeartbeats 6400000

lemma multilinear_polarization (f : Fin k → (M →ₗ[R] M)) :
    ∑ S ∈ (Finset.univ : Finset (Fin k)).powerset,
      ((-1 : R) ^ (k - S.card) : R) •
        PiTensorProduct.map (fun (_ : Fin k) => ∑ i ∈ S, f i) =
    ∑ σ : Equiv.Perm (Fin k), PiTensorProduct.map (f ∘ ⇑σ) := by
  -- By Fubini's theorem, we can interchange the order of summation.
  have h_fubini : ∑ S ∈ Finset.univ.powerset, (-1 : R) ^ (k - S.card) • (PiTensorProduct.map (fun x => ∑ i ∈ S, f i)) = ∑ τ : Fin k → Fin k, (∑ S ∈ Finset.univ.powerset, (-1 : R) ^ (k - S.card) * (∏ x : Fin k, if τ x ∈ S then 1 else 0)) • (PiTensorProduct.map (f ∘ τ)) := by
    simp +decide only [sum_smul];
    rw [ Finset.sum_comm, Finset.sum_congr rfl ];
    intro S hS;
    ext x;
    simp +decide [ PiTensorProduct.map_tprod, MultilinearMap.map_sum_finset ];
    simp +decide [ Finset.smul_sum, Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
    rw [ ← Finset.sum_subset ( Finset.subset_univ _ ) ];
    congr! 1;
    · rw [ Finset.card_sdiff ] ; aesop;
    · simp +contextual [ Finset.ext_iff ];
  -- The inner sum over $S$ is zero unless $\tau$ is surjective.
  have h_inner_zero : ∀ τ : Fin k → Fin k, (∑ S ∈ Finset.univ.powerset, (-1 : R) ^ (k - S.card) * (∏ x : Fin k, if τ x ∈ S then 1 else 0)) = if Function.Surjective τ then 1 else 0 := by
    intro τ
    have h_inner_zero : (∑ S ∈ Finset.univ.powerset, (-1 : R) ^ (k - S.card) * (∏ x : Fin k, if τ x ∈ S then 1 else 0)) = (∑ S ∈ Finset.powerset (Finset.univ \ Finset.image τ Finset.univ), (-1 : R) ^ (k - (Finset.univ \ S).card)) := by
      have h_inner_zero : (∑ S ∈ Finset.univ.powerset, (-1 : R) ^ (k - S.card) * (∏ x : Fin k, if τ x ∈ S then 1 else 0)) = (∑ S ∈ Finset.powerset (Finset.univ : Finset (Fin k)), if Finset.image τ Finset.univ ⊆ S then (-1 : R) ^ (k - S.card) else 0) := by
        refine' Finset.sum_congr rfl fun S hS => _;
        simp +decide [ Finset.prod_ite, Finset.filter_mem_eq_inter, Finset.filter_not ];
        split_ifs <;> simp_all +decide [ Finset.subset_iff ];
      rw [ h_inner_zero, ← Finset.sum_filter ];
      refine' Finset.sum_bij ( fun S hS => Finset.univ \ S ) _ _ _ _ <;> simp +decide [ Finset.subset_iff ];
      · exact fun S hS x hx y hy => hx <| hy ▸ hS y;
      · intro a₁ ha₁ a₂ ha₂ h; rw [ ← Finset.sdiff_sdiff_eq_self ( Finset.subset_univ a₁ ), h, Finset.sdiff_sdiff_eq_self ( Finset.subset_univ a₂ ) ] ;
      · intro b hb; use Finset.univ \ b; simp +decide [ Finset.subset_iff, hb ] ;
        exact fun x hx => hb hx x rfl;
    split_ifs with h;
    · simp_all +decide [ Finset.ext_iff, Function.Surjective ];
      rw [ show image τ Finset.univ = Finset.univ from Finset.eq_univ_of_forall fun x => by obtain ⟨ y, hy ⟩ := h x; exact Finset.mem_image.mpr ⟨ y, Finset.mem_univ _, hy ⟩ ] ; simp +decide [ Finset.card_sdiff ] ;
    · have h_inner_zero : (∑ S ∈ Finset.powerset (Finset.univ \ Finset.image τ Finset.univ), (-1 : R) ^ (Finset.card S)) = 0 := by
        have h_inner_zero : (∑ S ∈ Finset.powerset (Finset.univ \ Finset.image τ Finset.univ), (-1 : R) ^ (Finset.card S)) = (1 - 1) ^ (Finset.card (Finset.univ \ Finset.image τ Finset.univ)) := by
          rw [ sub_eq_neg_add, add_pow ] ; simp +decide [ Finset.sum_powerset ];
          exact Finset.sum_congr rfl fun i hi => by rw [ Finset.sum_congr rfl fun S hS => by rw [ Finset.mem_powersetCard.mp hS |>.2 ] ] ; simp +decide [ mul_comm ] ;
        simp_all +decide [ Finset.ext_iff, Function.Surjective ];
      have h_inner_zero : ∀ S ∈ Finset.powerset (Finset.univ \ Finset.image τ Finset.univ), (-1 : R) ^ (k - (Finset.univ \ S).card) = (-1 : R) ^ (Finset.card S) * (-1 : R) ^ (k - k) := by
        simp +decide [ Finset.card_sdiff ];
        exact fun S hS => by rw [ Nat.sub_sub_self ( le_trans ( Finset.card_le_univ _ ) ( by simp +decide ) ) ] ;
      rw [ ‹ ( ∑ S ∈ univ.powerset, ( -1 : R ) ^ ( k - #S ) * ∏ x, if τ x ∈ S then 1 else 0 ) = ∑ S ∈ ( univ \ image τ univ ).powerset, ( -1 : R ) ^ ( k - # ( univ \ S ) ) ›, Finset.sum_congr rfl h_inner_zero ] ; aesop;
  rw [ h_fubini, Finset.sum_congr rfl fun τ hτ => by rw [ h_inner_zero τ ] ];
  rw [ ← Finset.sum_subset ( Finset.subset_univ ( Finset.image ( fun σ : Equiv.Perm ( Fin k ) => ⇑σ ) Finset.univ ) ) ];
  · rw [ Finset.sum_image ] <;> simp +decide [ Function.Surjective ];
    · exact Finset.sum_congr rfl fun σ _ => if_pos fun b => ⟨ σ.symm b, by simp +decide ⟩;
    · exact fun σ τ h => Equiv.Perm.ext fun x => by simpa using congr_fun h x;
  · simp +contextual [ Function.Surjective ];
    exact fun x hx₁ hx₂ => False.elim ( hx₁ ( Equiv.ofBijective x ⟨ Finite.injective_iff_surjective.mpr hx₂, hx₂ ⟩ ) rfl )

end Submission.MultilinearPol
