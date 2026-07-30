import Mathlib.RepresentationTheory.Invariants

/-!
Norm operators for restrictions of finite-group representations.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Group G] [Fintype G]
variable [AddCommGroup V] [Module k V]

namespace Representation

/-- The norm operator takes every vector into the fixed subspace. -/
theorem norm_mem_invariants (rho : _root_.Representation k G V) (v : V) :
    rho.norm v ∈ rho.invariants := by
  rw [_root_.Representation.mem_invariants]
  intro g
  exact _root_.Representation.self_norm_apply rho g v

/-- If a finite-group representation has no fixed vectors, its norm operator
is zero. -/
theorem norm_eq_zero_of_invariants_eq_bot
    (rho : _root_.Representation k G V) (hfix : rho.invariants = ⊥) :
    rho.norm = 0 := by
  ext v
  have hv := norm_mem_invariants rho v
  rw [hfix] at hv
  exact (Submodule.mem_bot k).mp hv

/-- If a restricted fixed space is zero, then the ambient norm operator is
zero as well. -/
theorem norm_eq_zero_of_restrict_invariants_eq_bot
    (rho : _root_.Representation k G V) (H : Subgroup G) [Fintype H]
    (hfix : _root_.Representation.invariants
      (rho.comp H.subtype : _root_.Representation k H V) = ⊥) :
    rho.norm = 0 := by
  ext v
  have hv : rho.norm v ∈ _root_.Representation.invariants
      (rho.comp H.subtype : _root_.Representation k H V) := by
    rw [_root_.Representation.mem_invariants]
    intro h
    exact _root_.Representation.self_norm_apply rho (h : G) v
  rw [hfix] at hv
  exact (Submodule.mem_bot k).mp hv

omit [Fintype G] in
/-- A conjugate of a subgroup norm is the sum over the corresponding
conjugate subgroup. -/
theorem sum_conjugates_eq_mul_norm_mul_inv
    (rho : _root_.Representation k G V) (H : Subgroup G) [Fintype H]
    (x : G) :
    (∑ h : H, rho (x * (h : G) * x⁻¹)) =
      rho x * _root_.Representation.norm
        (rho.comp H.subtype : _root_.Representation k H V) * rho x⁻¹ := by
  rw [_root_.Representation.norm, Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro h _
  change rho (x * (h : G) * x⁻¹) = rho x * rho (h : G) * rho x⁻¹
  simp only [map_mul]

omit [Fintype G] in
/-- If the subgroup norm is its order times the identity, and that order is
nonzero in the coefficient field, the subgroup acts trivially. -/
theorem subgroup_le_ker_of_norm_eq_card_nsmul_one
    (rho : _root_.Representation k G V) (H : Subgroup G) [Fintype H]
    (hcard : _root_.Representation.norm
        (rho.comp H.subtype : _root_.Representation k H V) =
      Fintype.card H • (1 : Module.End k V))
    (hcard_ne : (Fintype.card H : k) ≠ 0) :
    H ≤ rho.ker := by
  intro x hx
  apply MonoidHom.mem_ker.mpr
  apply LinearMap.ext
  intro v
  have hnorm := _root_.Representation.norm_self_apply
    (rho.comp H.subtype : _root_.Representation k H V) ⟨x, hx⟩ v
  rw [hcard] at hnorm
  have hnorm' : (Fintype.card H : k) • rho x v =
      (Fintype.card H : k) • v := by
    simpa [Nat.cast_smul_eq_nsmul] using hnorm
  exact smul_right_injective V hcard_ne hnorm'

end Representation

end Submission.OddOrder.MathlibSupport
