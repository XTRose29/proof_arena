import Mathlib

set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

/-!
# Product maps span End(M^⊗k)
-/

open Finset
open scoped TensorProduct

namespace Submission.Spanning

variable {R : Type*} [Field R]
  {M : Type*} [AddCommGroup M] [Module R M] [FiniteDimensional R M]
  {k : ℕ}

set_option maxHeartbeats 3200000

/-
Product maps span End(M^⊗k). Uses a basis decomposition: each matrix unit
in the PiTensorProduct basis is a product map of rank-1 endomorphisms.
-/
lemma endomorphism_mem_span (T : (⨂[R]^k M) →ₗ[R] (⨂[R]^k M)) :
    T ∈ Submodule.span R
      (Set.range (fun f : Fin k → (M →ₗ[R] M) => PiTensorProduct.map f)) := by
  -- Let $b$ be a basis of $M$ and $ptb$ be the induced basis on the tensor product.
  set b := Module.finBasis R M
  set ptb := Basis.piTensorProduct (fun _ : Fin k => b);
  -- Each matrix unit (sending ptb J to ptb I and zeroing out other basis vectors) equals PiTensorProduct.map (fun r => (b.coord (J r)).smulRight (b (I r))).
  have h_matrix_unit : ∀ I J : Fin k → Fin (Module.finrank R M), (ptb.constr R) (fun L => if L = J then ptb I else 0) ∈ Submodule.span R (Set.range (fun f : Fin k → Module.End R M => PiTensorProduct.map f)) := by
    intro I J;
    refine' Submodule.subset_span ⟨ fun r => ( b.coord ( J r ) ).smulRight ( b ( I r ) ), _ ⟩;
    refine' ptb.ext fun L => _;
    by_cases h : L = J <;> simp +decide [ h, ptb ];
    rw [ Finset.prod_eq_zero ( Finset.mem_univ ( Classical.choose ( Function.ne_iff.mp h ) ) ) ] <;> simp +decide [ Classical.choose_spec ( Function.ne_iff.mp h ) ];
    exact MultilinearMap.map_coord_zero _ ( Classical.choose ( Function.ne_iff.mp h ) ) ( by simp +decide [ Classical.choose_spec ( Function.ne_iff.mp h ) ] );
  -- Decompose $T$ as a sum of matrix units.
  have h_decomp : T = ∑ I : Fin k → Fin (Module.finrank R M), ∑ J : Fin k → Fin (Module.finrank R M), (ptb.repr (T (ptb J))) I • (ptb.constr R) (fun L => if L = J then ptb I else 0) := by
    ext x;
    -- By definition of $ptb$, we can write $x$ as a linear combination of the basis elements.
    obtain ⟨c, hc⟩ : ∃ c : (Fin k → Fin (Module.finrank R M)) → R, PiTensorProduct.tprod R x = ∑ J, c J • ptb J := by
      exact ⟨ _, Eq.symm ( ptb.sum_repr _ ) ⟩;
    simp +decide [ hc, map_sum, map_smul ];
  exact h_decomp.symm ▸ Submodule.sum_mem _ fun I _ => Submodule.sum_mem _ fun J _ => Submodule.smul_mem _ _ ( h_matrix_unit I J )

end Submission.Spanning
