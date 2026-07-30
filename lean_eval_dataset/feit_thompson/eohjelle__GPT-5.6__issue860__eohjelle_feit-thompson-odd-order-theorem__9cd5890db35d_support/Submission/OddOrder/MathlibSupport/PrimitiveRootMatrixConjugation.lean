import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Submission.OddOrder.MathlibSupport.MatrixEntrywiseEigenspace
import Submission.OddOrder.MathlibSupport.ShiftedSigmaPairCard

/-!
Eigenspace dimensions for diagonal conjugation with primitive-root
weights.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v

variable {k : Type u} [Field k] {h : Nat} {omega : kˣ}

/-- The unit-valued character of `ZMod h` determined by a primitive
`h`-th root of unity. -/
noncomputable def primitiveRootUnitWeight (homega : IsPrimitiveRoot omega h)
    (i : ZMod h) : kˣ :=
  (homega.zmodEquivZPowers i).toMul.1

@[simp]
theorem primitiveRootUnitWeight_add
    (homega : IsPrimitiveRoot omega h) (i j : ZMod h) :
    primitiveRootUnitWeight homega (i + j) =
      primitiveRootUnitWeight homega i * primitiveRootUnitWeight homega j := by
  apply Units.ext
  simp [primitiveRootUnitWeight]

theorem primitiveRootUnitWeight_injective
    (homega : IsPrimitiveRoot omega h) :
    Function.Injective (primitiveRootUnitWeight homega) := by
  intro i j hij
  apply homega.zmodEquivZPowers.injective
  apply Additive.ext
  apply Subtype.ext
  exact hij

theorem primitiveRootUnitWeight_div_eq_iff
    (homega : IsPrimitiveRoot omega h) (i j m : ZMod h) :
    (primitiveRootUnitWeight homega i)⁻¹ *
        primitiveRootUnitWeight homega j =
      primitiveRootUnitWeight homega m ↔
      j = i + m := by
  constructor
  · intro hweight
    apply primitiveRootUnitWeight_injective homega
    rw [primitiveRootUnitWeight_add]
    calc
      primitiveRootUnitWeight homega j =
          primitiveRootUnitWeight homega i *
            ((primitiveRootUnitWeight homega i)⁻¹ *
              primitiveRootUnitWeight homega j) := by group
      _ = primitiveRootUnitWeight homega i *
          primitiveRootUnitWeight homega m := by rw [hweight]
  · rintro rfl
    rw [primitiveRootUnitWeight_add]
    group

/-- Entry weight of conjugation by a diagonal operator whose diagonal
is indexed by primitive-root powers. -/
noncomputable def primitiveRootConjugationEntryWeight
    (homega : IsPrimitiveRoot omega h) (fiber : ZMod h -> Type v)
    (p : (Σ i, fiber i) × (Σ i, fiber i)) : k :=
  ↑((primitiveRootUnitWeight homega p.1.1)⁻¹ *
    primitiveRootUnitWeight homega p.2.1)

/-- Coordinate pairs carrying the `m`-th conjugation eigenvalue are
exactly pairs whose base indices differ by `m`. -/
theorem primitiveRootConjugationEntryWeight_eq_iff
    (homega : IsPrimitiveRoot omega h) (fiber : ZMod h -> Type v)
    (p : (Σ i, fiber i) × (Σ i, fiber i)) (m : ZMod h) :
    primitiveRootConjugationEntryWeight homega fiber p =
        ↑(primitiveRootUnitWeight homega m) ↔
      p.2.1 = p.1.1 + m := by
  rw [primitiveRootConjugationEntryWeight, Units.val_inj]
  exact primitiveRootUnitWeight_div_eq_iff homega p.1.1 p.2.1 m

/-- The `m`-th eigenspace of primitive-root diagonal conjugation has
finrank equal to the cyclic autocorrelation of the block sizes. -/
theorem finrank_primitiveRootConjugationEntryWeight_eigenspace
    [NeZero h] (homega : IsPrimitiveRoot omega h)
    (fiber : ZMod h -> Type v) [∀ i, Finite (fiber i)] (m : ZMod h) :
    Module.finrank k
      (Module.End.eigenspace
        (matrixEntrywiseScale
          (primitiveRootConjugationEntryWeight homega fiber))
        ↑(primitiveRootUnitWeight homega m)) =
      ∑ i : ZMod h, Nat.card (fiber i) * Nat.card (fiber (i + m)) := by
  letI : Fintype (Σ i, fiber i) := Fintype.ofFinite _
  rw [finrank_matrixEntrywiseScale_eigenspace]
  let e :
      {p : (Σ i, fiber i) × (Σ i, fiber i) //
        primitiveRootConjugationEntryWeight homega fiber p =
          ↑(primitiveRootUnitWeight homega m)} ≃
      {p : (Σ i, fiber i) × (Σ i, fiber i) //
        p.2.1 = p.1.1 + m} :=
    { toFun := fun p =>
        ⟨p.1,
          (primitiveRootConjugationEntryWeight_eq_iff
            homega fiber p.1 m).mp p.2⟩
      invFun := fun p =>
        ⟨p.1,
          (primitiveRootConjugationEntryWeight_eq_iff
            homega fiber p.1 m).mpr p.2⟩
      left_inv := fun p => by rfl
      right_inv := fun p => by rfl }
  rw [Nat.card_congr e, natCard_shiftedSigmaPair fiber m]

end Submission.OddOrder.MathlibSupport
