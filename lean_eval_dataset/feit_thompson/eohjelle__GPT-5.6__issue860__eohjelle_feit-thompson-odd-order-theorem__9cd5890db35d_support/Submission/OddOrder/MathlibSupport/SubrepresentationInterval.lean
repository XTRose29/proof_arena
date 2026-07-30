import Mathlib.RepresentationTheory.Irreducible

/-!
Subrepresentations of a subrepresentation are the ambient subrepresentations
lying below it.
-/

namespace Submission.OddOrder.MathlibSupport

universe u v w

variable {k : Type u} {G : Type v} {V : Type w}
variable [Field k] [Monoid G] [AddCommGroup V] [Module k V]

/-- Regard a subrepresentation of `U.toRepresentation` as an ambient
subrepresentation lying below `U`. -/
def subrepresentationUnder
    (rho : Representation k G V) (U : Subrepresentation rho)
    (W : Subrepresentation U.toRepresentation) : Subrepresentation rho where
  toSubmodule := W.toSubmodule.map U.toSubmodule.subtype
  apply_mem_toSubmodule g v hv := by
    obtain ⟨x, hx, rfl⟩ := hv
    refine ⟨U.toRepresentation g x, W.apply_mem_toSubmodule g hx, ?_⟩
    rfl

theorem subrepresentationUnder_le
    (rho : Representation k G V) (U : Subrepresentation rho)
    (W : Subrepresentation U.toRepresentation) :
    subrepresentationUnder rho U W ≤ U := by
  rintro v ⟨x, _, rfl⟩
  exact x.property

/-- Pull an ambient subrepresentation below `U` back to a subrepresentation
of `U.toRepresentation`. -/
def subrepresentationOfUnder
    (rho : Representation k G V) (U : Subrepresentation rho)
    (W : Set.Iic U) : Subrepresentation U.toRepresentation where
  toSubmodule := W.1.toSubmodule.comap U.toSubmodule.subtype
  apply_mem_toSubmodule g _ hx := W.1.apply_mem_toSubmodule g hx

/-- The subrepresentation lattice of `U.toRepresentation` is the interval of
ambient subrepresentations below `U`. -/
def subrepresentationMapIic
    (rho : Representation k G V) (U : Subrepresentation rho) :
    Subrepresentation U.toRepresentation ≃o Set.Iic U where
  toFun W := ⟨subrepresentationUnder rho U W, subrepresentationUnder_le rho U W⟩
  invFun := subrepresentationOfUnder rho U
  left_inv W := by
    apply SetLike.ext
    intro x
    constructor
    · rintro ⟨y, hy, hyx⟩
      have hxy : y = x := Subtype.ext hyx
      change x ∈ W.toSubmodule
      simpa [hxy] using hy
    · intro hx
      exact ⟨x, hx, rfl⟩
  right_inv W := by
    apply Subtype.ext
    apply SetLike.ext
    intro v
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact hx
    · intro hv
      exact ⟨⟨v, W.2 hv⟩, hv, rfl⟩
  map_rel_iff' := by
    intro W X
    constructor
    · intro h x hx
      have hx' : (x : V) ∈ subrepresentationUnder rho U W := ⟨x, hx, rfl⟩
      obtain ⟨y, hy, hyx⟩ := h hx'
      have hxy : y = x := Subtype.ext hyx
      change x ∈ X.toSubmodule
      simpa [hxy] using hy
    · intro h v hv
      obtain ⟨x, hx, rfl⟩ := hv
      exact ⟨x, h hx, rfl⟩

/-- A subrepresentation is simple precisely when it is an atom of the ambient
subrepresentation lattice. -/
theorem irreducible_toRepresentation_iff_isAtom
    (rho : Representation k G V) (U : Subrepresentation rho) :
    Representation.IsIrreducible U.toRepresentation ↔ IsAtom U :=
  (subrepresentationMapIic rho U).isSimpleOrder_iff.trans
    Set.isSimpleOrder_Iic_iff_isAtom

end Submission.OddOrder.MathlibSupport
