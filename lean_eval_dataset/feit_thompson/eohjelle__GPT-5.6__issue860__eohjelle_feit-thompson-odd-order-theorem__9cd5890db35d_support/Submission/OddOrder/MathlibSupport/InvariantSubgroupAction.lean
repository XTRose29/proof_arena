import Mathlib.Algebra.Group.Subgroup.Map
import Mathlib.GroupTheory.GroupAction.ConjAct

/-!
Restriction of an automorphism action to an invariant subgroup.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {Q : Type u} {A : Type v} [Group Q] [Group A]

/-- Restrict an action by automorphisms to an invariant subgroup. -/
noncomputable def restrictMulAutHom
    (E : Subgroup Q) (f : A →* MulAut Q)
    (hE : ∀ a : A, E.map (f a).toMonoidHom = E) :
    A →* MulAut E where
  toFun a := (f a).subgroupMap E |>.trans (MulEquiv.subgroupCongr (hE a))
  map_one' := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    apply Subtype.ext
    simp

@[simp]
theorem coe_restrictMulAutHom_apply
    (E : Subgroup Q) (f : A →* MulAut Q)
    (hE : ∀ a : A, E.map (f a).toMonoidHom = E)
    (a : A) (x : E) :
    ((restrictMulAutHom E f hE a x : E) : Q) = f a (x : Q) :=
  rfl

/-- Invariance descends from the ambient group to an invariant overgroup. -/
theorem subgroupOf_map_restrictMulAutHom_eq
    (E U : Subgroup Q) (hUE : U ≤ E)
    (f : A →* MulAut Q)
    (hE : ∀ a : A, E.map (f a).toMonoidHom = E)
    (hU : ∀ a : A, U.map (f a).toMonoidHom = U)
    (a : A) :
    (U.subgroupOf E).map
        (restrictMulAutHom E f hE a).toMonoidHom = U.subgroupOf E := by
  apply Subgroup.map_injective E.subtype_injective
  rw [Subgroup.map_map]
  have hcomp : E.subtype.comp
      (restrictMulAutHom E f hE a).toMonoidHom =
      (f a).toMonoidHom.comp E.subtype := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hUE, hU a]

/-- An invariant subgroup of the restricted action maps to an invariant
subgroup of the ambient action. -/
theorem map_subtype_invariant_of_restrictMulAutHom
    (E : Subgroup Q) (X : Subgroup E) (f : A →* MulAut Q)
    (hE : ∀ a : A, E.map (f a).toMonoidHom = E)
    (hX : ∀ a : A,
      X.map (restrictMulAutHom E f hE a).toMonoidHom = X)
    (a : A) :
    (X.map E.subtype).map (f a).toMonoidHom = X.map E.subtype := by
  rw [Subgroup.map_map]
  have hcomp : (f a).toMonoidHom.comp E.subtype =
      E.subtype.comp (restrictMulAutHom E f hE a).toMonoidHom := by
    ext x
    rfl
  rw [hcomp, ← Subgroup.map_map, hX a]

end Submission.OddOrder.MathlibSupport
