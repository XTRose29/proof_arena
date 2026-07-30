import ChallengeDeps
import Mathlib.Combinatorics.Enumerative.InclusionExclusion
import Mathlib.LinearAlgebra.PiTensorProduct.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Basic

open scoped TensorProduct

namespace Submission.TensorInvariant

open Function

variable (R A : Type*) [CommRing R] [AddCommGroup A] [Module R A]

/-- The subspace of a tensor power spanned by tensors whose factors are all equal. -/
def diagonalSpan (k : ℕ) : Submodule R (⨂[R]^k A) :=
  Submodule.span R (Set.range fun a : A ↦
    PiTensorProduct.tprod R (fun _ : Fin k ↦ a))

theorem diagonal_mem_diagonalSpan (k : ℕ) (a : A) :
    PiTensorProduct.tprod R (fun _ : Fin k ↦ a) ∈ diagonalSpan R A k :=
  Submodule.subset_span (Set.mem_range_self a)

private def missingValue (k : ℕ) (i : Fin k) : Finset (Fin k → Fin k) :=
  Finset.univ.filter fun f ↦ ∀ j, f j ≠ i

private theorem inf_missingValue (k : ℕ) (s : Finset (Fin k)) :
    s.inf (missingValue k) = Fintype.piFinset fun _ : Fin k ↦ sᶜ := by
  classical
  ext f
  simp only [Finset.mem_inf, Fintype.mem_piFinset, Finset.mem_compl, Finset.mem_univ,
    true_and, missingValue, Finset.mem_filter]
  constructor
  · intro h i
    by_contra hi
    exact h (f i) hi i rfl
  · intro h i hi j hij
    exact h j (hij ▸ hi)

private theorem inf_compl_missingValue (k : ℕ) :
    Finset.univ.inf (fun i ↦ (missingValue k i)ᶜ) =
      Finset.univ.filter Surjective := by
  classical
  ext f
  simp only [Finset.mem_inf, Finset.mem_compl, Finset.mem_univ, true_implies,
    missingValue, Finset.mem_filter]
  constructor
  · intro h
    refine ⟨trivial, fun i ↦ ?_⟩
    by_contra hi
    apply h i
    exact ⟨trivial, fun j hj ↦ hi ⟨j, hj⟩⟩
  · rintro ⟨_, h⟩ i
    rintro ⟨_, hi⟩
    obtain ⟨j, hj⟩ := h i
    exact hi j hj

private noncomputable def permEquivSurjective (k : ℕ) :
    Equiv.Perm (Fin k) ≃ {f : Fin k → Fin k // Surjective f} :=
  Equiv.bijectiveEquiv.symm.trans <|
    Equiv.subtypeEquivProp <| funext fun _ ↦
      propext (Finite.surjective_iff_bijective).symm

private theorem sum_surjective_eq_sum_perm (k : ℕ)
    (F : (Fin k → Fin k) → (⨂[R]^k A)) :
    ∑ f ∈ Finset.univ.filter Surjective, F f =
      ∑ σ : Equiv.Perm (Fin k), F σ := by
  classical
  rw [← Finset.sum_subtype_eq_sum_filter]
  have huniv :
      Finset.subtype Surjective
          (Finset.univ : Finset (Fin k → Fin k)) = Finset.univ := by
    ext f
    simp
  rw [huniv]
  exact Fintype.sum_equiv (permEquivSurjective k).symm
    (fun f : {f : Fin k → Fin k // Surjective f} ↦ F f)
    (fun σ : Equiv.Perm (Fin k) ↦ F σ) fun _ ↦ rfl

/-- The sum of all permutations of a pure tensor is in the span of diagonal tensors.

This is the polarization identity, organized as inclusion-exclusion over the values omitted by an
endomap of the finite indexing set. -/
theorem sum_reindex_tprod_mem_diagonalSpan (k : ℕ) (f : Fin k → A) :
    (∑ σ : Equiv.Perm (Fin k),
        PiTensorProduct.reindex R (fun _ : Fin k ↦ A) σ
          (PiTensorProduct.tprod R f)) ∈ diagonalSpan R A k := by
  classical
  let F : (Fin k → Fin k) → (⨂[R]^k A) :=
    fun g ↦ PiTensorProduct.tprod R (fun i ↦ f (g i))
  have hpolar :
      (∑ g ∈ Finset.univ.filter Surjective, F g) =
        ∑ s ∈ Finset.univ.powerset, (-1 : ℤ) ^ s.card •
          PiTensorProduct.tprod R
            (fun _ : Fin k ↦ ∑ i ∈ sᶜ, f i) := by
    rw [← inf_compl_missingValue k,
      Finset.inclusion_exclusion_sum_inf_compl Finset.univ (missingValue k) F]
    apply Finset.sum_congr rfl
    intro s hs
    congr 1
    rw [inf_missingValue k s]
    exact ((PiTensorProduct.tprod R).map_sum_finset
      (fun _ i ↦ f i) (fun _ : Fin k ↦ sᶜ)).symm
  have hrhs :
      (∑ s ∈ Finset.univ.powerset, (-1 : ℤ) ^ s.card •
          PiTensorProduct.tprod R
            (fun _ : Fin k ↦ ∑ i ∈ sᶜ, f i)) ∈ diagonalSpan R A k := by
    apply Submodule.sum_mem
    intro s hs
    rw [← Int.cast_smul_eq_zsmul R]
    exact (diagonalSpan R A k).smul_mem _
      (diagonal_mem_diagonalSpan R A k _)
  have hsurj :
      (∑ g ∈ Finset.univ.filter Surjective, F g) ∈ diagonalSpan R A k := by
    rw [hpolar]
    exact hrhs
  rw [sum_surjective_eq_sum_perm R A k F] at hsurj
  have hsymm :
      (∑ σ : Equiv.Perm (Fin k), F σ.symm) =
        ∑ σ : Equiv.Perm (Fin k), F σ := by
    exact Fintype.sum_bijective (fun σ : Equiv.Perm (Fin k) ↦ σ.symm)
      Equiv.symm_bijective _ _ fun _ ↦ rfl
  have hsurj' :
      (∑ σ : Equiv.Perm (Fin k), F σ.symm) ∈ diagonalSpan R A k := by
    rw [hsymm]
    exact hsurj
  simpa only [F, PiTensorProduct.reindex_tprod] using hsurj'

/-- Sum the reindexing action of the full symmetric group. -/
noncomputable def permSum (k : ℕ) : Module.End R (⨂[R]^k A) :=
  ∑ σ : Equiv.Perm (Fin k),
    (PiTensorProduct.reindex R (fun _ : Fin k ↦ A) σ).toLinearMap

theorem permSum_apply (k : ℕ) (x : ⨂[R]^k A) :
    permSum R A k x =
      ∑ σ : Equiv.Perm (Fin k),
        PiTensorProduct.reindex R (fun _ : Fin k ↦ A) σ x := by
  simp [permSum]

theorem permSum_mem_diagonalSpan (k : ℕ) (x : ⨂[R]^k A) :
    permSum R A k x ∈ diagonalSpan R A k := by
  induction x using PiTensorProduct.induction_on with
  | smul_tprod r f =>
      rw [map_smul]
      exact (diagonalSpan R A k).smul_mem r (by
        simpa [permSum_apply] using sum_reindex_tprod_mem_diagonalSpan R A k f)
  | add x y hx hy =>
      rw [map_add]
      exact Submodule.add_mem _ hx hy

/-- An invariant tensor is a linear combination of diagonal tensors when the group order is
invertible. -/
theorem mem_diagonalSpan_of_reindex_eq
    (k : ℕ) [Invertible (k.factorial : R)] (x : ⨂[R]^k A)
    (hx : ∀ σ : Equiv.Perm (Fin k),
      PiTensorProduct.reindex R (fun _ : Fin k ↦ A) σ x = x) :
    x ∈ diagonalSpan R A k := by
  have hsum := permSum_mem_diagonalSpan R A k x
  rw [permSum_apply, Finset.sum_congr rfl (fun σ _ ↦ hx σ), Finset.sum_const,
    Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
    ← Nat.cast_smul_eq_nsmul R] at hsum
  exact (diagonalSpan R A k).smul_mem_iff_of_isUnit
    (isUnit_of_invertible (k.factorial : R)) |>.mp hsum

end Submission.TensorInvariant
