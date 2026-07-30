import Submission.OddOrder.MathlibSupport.FiniteOrderQuasiHomocyclicRanks

/-!
The free finite-order specialization of the quasi-homocyclic rank theorem.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v

variable {k : Type u} {V : Type v}
variable [Field k] [AddCommGroup V] [Module k V]

/-- If the eigenvalue-one eigenspace vanishes, the quasi-homocyclic rank
profile is exactly one-dimensional at every nontrivial root, and the
operator order is one more than the ambient finrank. -/
theorem finiteOrder_free_quasiHomocyclic_rank_profile
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [IsAlgClosed k]
    [FiniteDimensional k V] (f : V ≃ₗ[k] V)
    (hpow : f.toLinearMap ^ h = 1)
    (hrank_zero :
      Module.finrank k
        (Module.End.eigenspace f.toLinearMap
          (primitiveRootUnitWeight homega 0 : k)) = 0)
    (hdim : 1 < Module.finrank k V)
    (hdrop : ∀ m : ZMod h, m ≠ 0 ->
      Module.finrank k
          (Module.End.eigenspace (linearEquivConjugation f)
            (primitiveRootUnitWeight homega 0 : k)) =
        Module.finrank k
            (Module.End.eigenspace (linearEquivConjugation f)
              (primitiveRootUnitWeight homega m : k)) + 1) :
    h = Module.finrank k V + 1 ∧
      ∀ m : ZMod h, m ≠ 0 ->
        Module.finrank k
          (Module.End.eigenspace f.toLinearMap
            (primitiveRootUnitWeight homega m : k)) = 1 := by
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
  obtain ⟨hcard, hrank⟩ :=
    quasiHomocyclic_rank_profile_of_correlation rank hrank_zero
      (by simpa [← hsum] using hdim) hcorrelation
  constructor
  · simpa [ZMod.card, ← hsum] using hcard
  · exact hrank

end Submission.OddOrder.MathlibSupport
