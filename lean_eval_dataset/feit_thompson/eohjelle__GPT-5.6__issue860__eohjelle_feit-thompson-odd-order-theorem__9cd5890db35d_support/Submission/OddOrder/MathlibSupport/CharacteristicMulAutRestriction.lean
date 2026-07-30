import Submission.OddOrder.MathlibSupport.InvariantSubgroupAction
import Mathlib.GroupTheory.GroupAction.FixingSubgroup

/-!
Restriction of the full automorphism group to a characteristic subgroup.

The kernel is the pointwise fixing subgroup for the natural action of
`MulAut G` on `G`.  This packages the automorphism centralizer occurring in
`BGsection5.v: Aut_narrow` without introducing a second fixed-subgroup
abstraction alongside mathlib's `fixingSubgroup`.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v

variable {G : Type u} {A : Type v} [Group G] [Group A]

/-- Restrict every automorphism of a group to a characteristic subgroup. -/
noncomputable def characteristicRestrictMulAutHom
    (H : Subgroup G) [H.Characteristic] :
    MulAut G →* MulAut H :=
  restrictMulAutHom H (MonoidHom.id (MulAut G)) fun a ↦
    Subgroup.characteristic_iff_map_eq.mp
      (inferInstance : H.Characteristic) a

/-- Restriction agrees with the original automorphism after coercion to the
ambient group. -/
@[simp]
theorem characteristicRestrictMulAutHom_apply
    (H : Subgroup G) [H.Characteristic]
    (a : MulAut G) (h : H) :
    ((characteristicRestrictMulAutHom H a h : H) : G) = a (h : G) := by
  rfl

/-- The restriction kernel consists exactly of the automorphisms fixing the
characteristic subgroup pointwise. -/
@[simp]
theorem mem_characteristicRestrictMulAutHom_ker_iff
    (H : Subgroup G) [H.Characteristic] (a : MulAut G) :
    a ∈ (characteristicRestrictMulAutHom H).ker ↔
      ∀ h : H, a (h : G) = h := by
  rw [MonoidHom.mem_ker]
  constructor
  · intro ha h
    have hh := congrArg (fun e : MulAut H ↦ e h) ha
    exact congrArg Subtype.val hh
  · intro ha
    apply MulEquiv.ext
    intro h
    apply Subtype.ext
    exact ha h

/-- For an arbitrary automorphism action, the kernel after characteristic
restriction is the pointwise kernel of that action on the subgroup. -/
@[simp]
theorem mem_characteristicRestrictMulAutHom_comp_ker_iff
    (H : Subgroup G) [H.Characteristic]
    (f : A →* MulAut G) (a : A) :
    a ∈ ((characteristicRestrictMulAutHom H).comp f).ker ↔
      ∀ h : H, f a (h : G) = h := by
  exact mem_characteristicRestrictMulAutHom_ker_iff H (f a)

/-- The restriction kernel is mathlib's pointwise fixing subgroup for the
natural automorphism action. -/
theorem characteristicRestrictMulAutHom_ker_eq_fixingSubgroup
    (H : Subgroup G) [H.Characteristic] :
    (characteristicRestrictMulAutHom H).ker =
      fixingSubgroup (MulAut G) (H : Set G) := by
  ext a
  rw [mem_characteristicRestrictMulAutHom_ker_iff,
    mem_fixingSubgroup_iff]
  constructor
  · intro ha h hh
    exact ha ⟨h, hh⟩
  · intro ha h
    exact ha h h.property

end Submission.OddOrder.MathlibSupport
