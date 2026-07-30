import Submission.OddOrder.PF.Section01.Induction

/-!
# Induction from conjugate subgroups

This file transports class functions across conjugation of an arbitrary
subgroup and proves that induction is invariant under that transport.

Our orientation is
`conjugateSubgroup H x = x H x⁻¹`, following `MulAut.conj x`.  Thus a
class function on `H` is transported to `x H x⁻¹` by evaluating at the
pullback `x⁻¹ h x`.  Coq's Peterfalvi development often writes the
opposite orientation `x⁻¹ H x`; it is obtained here by replacing `x` with
`x⁻¹`.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v

variable {G : Type u} [Group G]

/-- The conjugate subgroup `x H x⁻¹`. -/
def conjugateSubgroup (H : Subgroup G) (x : G) : Subgroup G :=
  H.map (MulAut.conj x).toMonoidHom

/-- Conjugation by `x` as an equivalence from `H` to `x H x⁻¹`. -/
def conjugateSubgroupEquiv (H : Subgroup G) (x : G) :
    H ≃* conjugateSubgroup H x :=
  (MulAut.conj x).subgroupMap H

@[simp]
theorem conjugateSubgroupEquiv_apply_coe (H : Subgroup G) (x : G) (h : H) :
    ((conjugateSubgroupEquiv H x h : conjugateSubgroup H x) : G) =
      x * (h : G) * x⁻¹ :=
  rfl

@[simp]
theorem conjugateSubgroupEquiv_symm_apply_coe
    (H : Subgroup G) (x : G) (h : conjugateSubgroup H x) :
    (((conjugateSubgroupEquiv H x).symm h : H) : G) =
      x⁻¹ * (h : G) * x :=
  rfl

namespace ClassFunction

variable {R : Type v} [Ring R]

/-- Transport a class function on `H` to `x H x⁻¹` by conjugation.
At `h' ∈ x H x⁻¹`, its value is `f (x⁻¹ h' x)`. -/
def conjugateSubgroupClassFunction (H : Subgroup G) (x : G)
    (f : ClassFunction H R) : ClassFunction (conjugateSubgroup H x) R :=
  ⟨fun h ↦ f ((conjugateSubgroupEquiv H x).symm h), by
    intro y h
    simpa only [map_mul, map_inv] using
      ClassFunction.conj_apply f
        ((conjugateSubgroupEquiv H x).symm y)
        ((conjugateSubgroupEquiv H x).symm h)⟩

@[simp]
theorem conjugateSubgroupClassFunction_apply (H : Subgroup G) (x : G)
    (f : ClassFunction H R) (h : conjugateSubgroup H x) :
    conjugateSubgroupClassFunction H x f h =
      f ((conjugateSubgroupEquiv H x).symm h) :=
  rfl

@[simp]
theorem conjugateSubgroupClassFunction_apply_equiv
    (H : Subgroup G) (x : G) (f : ClassFunction H R) (h : H) :
    conjugateSubgroupClassFunction H x f (conjugateSubgroupEquiv H x h) = f h := by
  simp

section Finite

variable {k : Type v} [Field k] [Fintype G]

/-- Induction is unchanged when both the inducing subgroup and its class
function are transported by ambient conjugation. -/
theorem induce_conjugateSubgroup
    (H : Subgroup G) (x : G) (f : ClassFunction H k) :
    ClassFunction.induce (conjugateSubgroup H x)
        (conjugateSubgroupClassFunction H x f) =
      ClassFunction.induce H f := by
  classical
  ext g
  rw [induce_apply_formula, induce_apply_formula]
  have hcard : Nat.card (conjugateSubgroup H x) = Nat.card H :=
    Nat.card_congr (conjugateSubgroupEquiv H x).symm.toEquiv
  rw [hcard]
  congr 1
  refine Fintype.sum_equiv (Equiv.mulRight x)
    (fun z : G ↦ inductionKernel (conjugateSubgroup H x)
      (conjugateSubgroupClassFunction H x f) z g)
    (fun z : G ↦ inductionKernel H f z g) fun z ↦ ?_
  change inductionKernel (conjugateSubgroup H x)
      (conjugateSubgroupClassFunction H x f) z g =
    inductionKernel H f (z * x) g
  have hmem :
      z⁻¹ * g * z ∈ conjugateSubgroup H x ↔
        (z * x)⁻¹ * g * (z * x) ∈ H := by
    rw [show z⁻¹ * g * z ∈ conjugateSubgroup H x ↔
        (MulAut.conj x).symm (z⁻¹ * g * z) ∈ H by
      exact Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply, mul_inv_rev, mul_assoc]
  by_cases hz : z⁻¹ * g * z ∈ conjugateSubgroup H x
  · have hzx : (z * x)⁻¹ * g * (z * x) ∈ H := hmem.mp hz
    rw [inductionKernel_of_mem _ _ z g hz,
      inductionKernel_of_mem _ _ (z * x) g hzx,
      conjugateSubgroupClassFunction_apply]
    apply congrArg f
    apply Subtype.ext
    change (MulAut.conj x).symm (z⁻¹ * g * z) =
      (z * x)⁻¹ * g * (z * x)
    simp only [MulAut.conj_symm_apply, mul_inv_rev]
    group
  · have hzx : (z * x)⁻¹ * g * (z * x) ∉ H := by
      exact fun h ↦ hz (hmem.mpr h)
    rw [inductionKernel_of_notMem _ _ z g hz,
      inductionKernel_of_notMem _ _ (z * x) g hzx]

end Finite

end ClassFunction

end

end Submission.OddOrder.PF
