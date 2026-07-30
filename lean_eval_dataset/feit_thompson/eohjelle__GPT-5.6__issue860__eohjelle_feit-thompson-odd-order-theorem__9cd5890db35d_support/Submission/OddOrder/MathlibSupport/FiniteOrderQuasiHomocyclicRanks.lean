import Submission.OddOrder.MathlibSupport.FiniteOrderConjugationFinrank
import Submission.OddOrder.MathlibSupport.GeneralQuasiHomocyclicRanks
import Submission.OddOrder.MathlibSupport.IndependentSubmoduleFinrank

/-!
Quasi-homocyclic eigenspace ranks from finite-order conjugation rank drops.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- A one-dimensional drop in every nontrivial conjugation eigenspace
forces the eigenspace ranks of the original finite-order operator to be
quasi-homocyclic. -/
theorem finiteOrder_quasiHomocyclic_rank_profile
    {h : Nat} [NeZero h] (hh : 1 < h) {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [IsAlgClosed k]
    [FiniteDimensional k V] (f : V ≃ₗ[k] V)
    (hpow : f.toLinearMap ^ h = 1)
    (hdrop : ∀ m : ZMod h, m ≠ 0 ->
      Module.finrank k
          (Module.End.eigenspace (linearEquivConjugation f)
            (primitiveRootUnitWeight homega 0 : k)) =
        Module.finrank k
            (Module.End.eigenspace (linearEquivConjugation f)
              (primitiveRootUnitWeight homega m : k)) + 1) :
    ∃ n : Nat, ∃ i : ZMod h,
      Nat.dist (Module.finrank k V) (h * n) = 1 ∧
      Nat.dist
          (Module.finrank k
            (Module.End.eigenspace f.toLinearMap
              (primitiveRootUnitWeight homega i : k))) n = 1 ∧
      ∀ j : ZMod h, j ≠ i ->
        Module.finrank k
          (Module.End.eigenspace f.toLinearMap
            (primitiveRootUnitWeight homega j : k)) = n := by
  let rank : ZMod h -> Nat := fun i =>
    Module.finrank k
      (Module.End.eigenspace f.toLinearMap
        (primitiveRootUnitWeight homega i : k))
  have hcorrelation (m : ZMod h) (hm : m ≠ 0) :
      cyclicRankCorrelation rank 0 =
        cyclicRankCorrelation rank m + 1 := by
    rw [← finrank_linearEquivConjugation_eq_cyclicRankCorrelation_of_pow_eq_one
      homega f hpow 0,
      ← finrank_linearEquivConjugation_eq_cyclicRankCorrelation_of_pow_eq_one
        homega f hpow m]
    exact hdrop m hm
  obtain ⟨n, i, htotal, hi, hothers⟩ :=
    general_quasiHomocyclic_rank_profile_of_correlation rank
      (by simpa using hh) hcorrelation
  have hindependent : iSupIndep (fun i : ZMod h =>
      Module.End.eigenspace f.toLinearMap
        (primitiveRootUnitWeight homega i : k)) := by
    change iSupIndep
      (Module.End.eigenspace f.toLinearMap ∘
        fun i : ZMod h => (primitiveRootUnitWeight homega i : k))
    exact (Module.End.eigenspaces_iSupIndep f.toLinearMap).comp
      (primitiveRootUnitWeight_val_injective homega)
  have hsum : Module.finrank k V = ∑ i : ZMod h, rank i := by
    exact finrank_eq_sum_finrank_of_iSupIndep
      (fun i : ZMod h =>
        Module.End.eigenspace f.toLinearMap
          (primitiveRootUnitWeight homega i : k))
      hindependent
      (iSup_primitiveRootUnitWeight_eigenspace_eq_top
        homega f.toLinearMap hpow)
  refine ⟨n, i, ?_, hi, hothers⟩
  rw [hsum]
  simpa using htotal

end Submission.OddOrder.MathlibSupport
