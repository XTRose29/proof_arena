import Mathlib

/-!
Centralizers internal to a subgroup.

MathComp writes `'C_D(A)` for the elements of `D` centralizing `A`.  Mathlib's
`Subgroup.centralizer` lives in the ambient group, so `centralizerWithin` is the
small bridge used by the Bender--Glauberman port.
-/

namespace Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The elements of `D` that centralize every element of `A`. -/
def centralizerWithin (D A : Subgroup G) : Subgroup G :=
  D ⊓ Subgroup.centralizer (A : Set G)

/-- The center of a subgroup, represented as a subgroup of the ambient group. -/
def centerWithin (D : Subgroup G) : Subgroup G :=
  centralizerWithin D D

@[simp]
theorem mem_centralizerWithin {D A : Subgroup G} {x : G} :
    x ∈ centralizerWithin D A ↔ x ∈ D ∧ ∀ a ∈ A, a * x = x * a :=
  Iff.rfl

@[simp]
theorem mem_centerWithin {D : Subgroup G} {x : G} :
    x ∈ centerWithin D ↔ x ∈ D ∧ ∀ d ∈ D, d * x = x * d :=
  Iff.rfl

theorem centralizerWithin_le_left (D A : Subgroup G) : centralizerWithin D A ≤ D :=
  inf_le_left

theorem centralizerWithin_mono_left {D E A : Subgroup G} (hDE : D ≤ E) :
    centralizerWithin D A ≤ centralizerWithin E A :=
  inf_le_inf_right _ hDE

theorem centralizerWithin_antitone_right {D A B : Subgroup G} (hAB : A ≤ B) :
    centralizerWithin D B ≤ centralizerWithin D A :=
  inf_le_inf_left _ (Subgroup.centralizer_le hAB)

theorem centerWithin_le_centralizerWithin {D A : Subgroup G} (hAD : A ≤ D) :
    centerWithin D ≤ centralizerWithin D A :=
  centralizerWithin_antitone_right hAD

/-- The internal center is the ordinary center of the subgroup subtype,
transported back into the ambient group. -/
theorem map_center_eq_centerWithin (D : Subgroup G) :
    (Subgroup.center D).map D.subtype = centerWithin D := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, ?_⟩
    intro y hy
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨y, hy⟩)
  · rintro ⟨hxD, hxC⟩
    refine ⟨⟨x, hxD⟩, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact hxC y y.2

instance centerWithin_isMulCommutative (D : Subgroup G) :
    IsMulCommutative (centerWithin D) := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  intro x hx y hy
  exact hx.2 y hy.1

theorem centerWithin_ne_bot {p : ℕ} [Fact p.Prime] (D : Subgroup G)
    [Finite D] [Nontrivial D] (hD : IsPGroup p D) : centerWithin D ≠ ⊥ := by
  rw [← map_center_eq_centerWithin D]
  exact (not_congr (Subgroup.map_eq_bot_iff_of_injective (Subgroup.center D)
    D.subtype_injective)).mpr hD.bot_lt_center.ne'

end Submission.OddOrder.MathlibSupport
