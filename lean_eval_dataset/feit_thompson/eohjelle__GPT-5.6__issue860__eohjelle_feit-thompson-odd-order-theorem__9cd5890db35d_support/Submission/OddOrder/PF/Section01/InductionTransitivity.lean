import Submission.OddOrder.PF.Section01.ConstituentExpansion
import Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter

/-!
# Transitivity of class-function induction

Peterfalvi 1.7 repeatedly induces first from a normal subgroup to its
inertia subgroup and then to the ambient group.  Lean represents a subgroup
`H ≤ T` inside `T` as `H.subgroupOf T`, so this file supplies both the
canonical transport of class functions to that copy and the corresponding
transitivity theorem.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v

namespace ClassFunction

variable {G : Type u} {k : Type v}
  [Group G] [Field k] [Fintype G]

/-- Move a class function on `H` to the copy of `H` inside a containing
subgroup `T`. -/
def toSubgroupOf (H T : Subgroup G) (hHT : H ≤ T) :
    ClassFunction H k →ₗ[k] ClassFunction (H.subgroupOf T) k :=
  comap (Subgroup.subgroupOfEquivOfLe hHT).toMonoidHom

omit [Fintype G] in
@[simp]
theorem toSubgroupOf_apply (H T : Subgroup G) (hHT : H ≤ T)
    (f : ClassFunction H k) (h : H.subgroupOf T) :
    toSubgroupOf H T hHT f h =
      f (Subgroup.subgroupOfEquivOfLe hHT h) :=
  rfl

/-- One summand of two-stage induction is the normalized sum of the
corresponding one-stage summands. -/
theorem inductionKernel_induce_subgroupOf
    (H T : Subgroup G) (hHT : H ≤ T) (f : ClassFunction H k)
    (x g : G) :
    inductionKernel T
        (induce (H.subgroupOf T) (toSubgroupOf H T hHT f)) x g =
      (Nat.card H : k)⁻¹ *
        ∑ y : T, inductionKernel H f (x * (y : G)) g := by
  by_cases hx : x⁻¹ * g * x ∈ T
  · rw [inductionKernel_of_mem _ _ _ _ hx, induce_apply_formula]
    have hcard : Nat.card (H.subgroupOf T) = Nat.card H :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHT).toEquiv
    rw [hcard]
    apply congrArg ((Nat.card H : k)⁻¹ * ·)
    apply Fintype.sum_congr
    intro y
    have heq :
        (((y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y : T) : T) : G) =
          (x * (y : G))⁻¹ * g * (x * (y : G)) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    have hmem :
        y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y ∈ H.subgroupOf T ↔
          (x * (y : G))⁻¹ * g * (x * (y : G)) ∈ H := by
      change
        (((y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y : T) : T) : G) ∈ H ↔ _
      rw [heq]
    by_cases hy : (x * (y : G))⁻¹ * g * (x * (y : G)) ∈ H
    · have hy' :
          y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y ∈ H.subgroupOf T :=
        hmem.2 hy
      rw [dif_pos hy', inductionKernel_of_mem _ _ _ _ hy,
        toSubgroupOf_apply]
      apply congrArg f
      apply Subtype.ext
      exact heq
    · have hy' :
          y⁻¹ * ⟨x⁻¹ * g * x, hx⟩ * y ∉ H.subgroupOf T :=
        hmem.not.mpr hy
      rw [dif_neg hy', inductionKernel_of_notMem _ _ _ _ hy]
  · rw [inductionKernel_of_notMem _ _ _ _ hx]
    simp only [zero_eq_mul]
    right
    apply Fintype.sum_eq_zero
    intro y
    apply inductionKernel_of_notMem
    intro hy
    apply hx
    have hyT : (x * (y : G))⁻¹ * g * (x * (y : G)) ∈ T :=
      hHT hy
    have hconj := T.mul_mem (T.mul_mem y.property hyT) (T.inv_mem y.property)
    convert hconj using 1
    all_goals group

/-- Right multiplication by all elements of a subgroup counts every
ambient-group summand exactly `|T|` times. -/
theorem sum_inductionKernel_mul_subgroup
    (T : Subgroup G) (F : G → k) :
    (∑ x : G, ∑ y : T, F (x * (y : G))) =
      Nat.card T • ∑ z : G, F z := by
  rw [Finset.sum_comm]
  have hy (y : T) : (∑ x : G, F (x * (y : G))) = ∑ z : G, F z := by
    exact Fintype.sum_equiv (Equiv.mulRight (y : G)) _ _ (fun _ ↦ rfl)
  simp_rw [hy]
  rw [Finset.sum_const, Finset.card_univ, ← Nat.card_eq_fintype_card]

/-- Transitivity of class-function induction along `H ≤ T ≤ G`. -/
theorem induce_trans [CharZero k]
    (H T : Subgroup G) (hHT : H ≤ T) (f : ClassFunction H k) :
    induce T (induce (H.subgroupOf T) (toSubgroupOf H T hHT f)) =
      induce H f := by
  ext g
  simp only [induce_apply, inductionValue]
  simp_rw [inductionKernel_induce_subgroupOf H T hHT f]
  rw [← Finset.mul_sum]
  rw [sum_inductionKernel_mul_subgroup T
    (fun z : G ↦ inductionKernel H f z g)]
  rw [← Nat.cast_smul_eq_nsmul k, smul_eq_mul]
  have hcard : (Nat.card T : k) ≠ 0 :=
    Nat.cast_ne_zero.mpr Nat.card_pos.ne'
  field_simp [hcard]

end ClassFunction

end

end Submission.OddOrder.PF
