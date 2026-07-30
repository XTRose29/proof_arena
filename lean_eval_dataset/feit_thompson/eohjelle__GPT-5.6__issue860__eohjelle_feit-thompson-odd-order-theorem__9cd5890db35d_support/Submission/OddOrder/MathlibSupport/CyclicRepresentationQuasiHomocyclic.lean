import Submission.OddOrder.MathlibSupport.FiniteOrderFreeQuasiHomocyclic
import Submission.OddOrder.MathlibSupport.RepresentationLinearEquiv

/-!
Quasi-homocyclic rank theorems for a represented cyclic element.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [AddCommGroup V] [Module k V]

/-- Representation-native form of the finite-order quasi-homocyclic
rank-profile theorem. -/
theorem cyclicRepresentation_quasiHomocyclic_rank_profile
    {h : Nat} [NeZero h] (hh : 1 < h) {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [IsAlgClosed k]
    [FiniteDimensional k V] (rho : Representation k G V) (z : G)
    (hzpow : z ^ h = 1)
    (hdrop : ∀ m : ZMod h, m ≠ 0 ->
      Module.finrank k
          (Module.End.eigenspace
            (linearEquivConjugation (representationLinearEquiv rho z))
            (primitiveRootUnitWeight homega 0 : k)) =
        Module.finrank k
            (Module.End.eigenspace
              (linearEquivConjugation (representationLinearEquiv rho z))
              (primitiveRootUnitWeight homega m : k)) + 1) :
    ∃ n : Nat, ∃ i : ZMod h,
      Nat.dist (Module.finrank k V) (h * n) = 1 ∧
      Nat.dist
          (Module.finrank k
            (Module.End.eigenspace (rho z)
              (primitiveRootUnitWeight homega i : k))) n = 1 ∧
      ∀ j : ZMod h, j ≠ i ->
        Module.finrank k
          (Module.End.eigenspace (rho z)
            (primitiveRootUnitWeight homega j : k)) = n := by
  obtain ⟨n, i, htotal, hi, hothers⟩ :=
    finiteOrder_quasiHomocyclic_rank_profile hh homega
      (representationLinearEquiv rho z)
      (representationLinearEquiv_pow_eq_one rho z h hzpow) hdrop
  exact ⟨n, i, htotal, hi, hothers⟩

/-- Representation-native free specialization: a vanishing
eigenvalue-one space forces rank one at every nontrivial root. -/
theorem cyclicRepresentation_free_quasiHomocyclic_rank_profile
    {h : Nat} [NeZero h] {omega : kˣ}
    (homega : IsPrimitiveRoot omega h) [IsAlgClosed k]
    [FiniteDimensional k V] (rho : Representation k G V) (z : G)
    (hzpow : z ^ h = 1)
    (hrank_zero :
      Module.finrank k
        (Module.End.eigenspace (rho z)
          (primitiveRootUnitWeight homega 0 : k)) = 0)
    (hdim : 1 < Module.finrank k V)
    (hdrop : ∀ m : ZMod h, m ≠ 0 ->
      Module.finrank k
          (Module.End.eigenspace
            (linearEquivConjugation (representationLinearEquiv rho z))
            (primitiveRootUnitWeight homega 0 : k)) =
        Module.finrank k
            (Module.End.eigenspace
              (linearEquivConjugation (representationLinearEquiv rho z))
              (primitiveRootUnitWeight homega m : k)) + 1) :
    h = Module.finrank k V + 1 ∧
      ∀ m : ZMod h, m ≠ 0 ->
        Module.finrank k
          (Module.End.eigenspace (rho z)
            (primitiveRootUnitWeight homega m : k)) = 1 := by
  obtain ⟨horder, hrank⟩ :=
    finiteOrder_free_quasiHomocyclic_rank_profile homega
      (representationLinearEquiv rho z)
      (representationLinearEquiv_pow_eq_one rho z h hzpow)
      hrank_zero hdim hdrop
  exact ⟨horder, hrank⟩

end Submission.OddOrder.MathlibSupport
