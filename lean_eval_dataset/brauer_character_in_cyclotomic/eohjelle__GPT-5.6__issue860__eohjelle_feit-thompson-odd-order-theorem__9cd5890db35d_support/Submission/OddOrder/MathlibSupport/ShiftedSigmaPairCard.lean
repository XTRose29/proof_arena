import Mathlib.Data.Fintype.Card
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.SetTheory.Cardinal.Finite

/-!
Counting pairs in a dependent finite family whose base indices differ by
a fixed shift.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u v

variable {A : Type u} (fiber : A -> Type v)

/-- A pair of dependent coordinates with second base index `i + m` is
the same data as an element of `fiber i × fiber (i + m)`. -/
def shiftedSigmaPairEquiv [Add A] (m : A) :
    {p : (Σ i, fiber i) × (Σ i, fiber i) //
      p.2.1 = p.1.1 + m} ≃ Σ i, fiber i × fiber (i + m) where
  toFun p :=
    ⟨p.1.1.1, p.1.1.2,
      p.2 ▸ p.1.2.2⟩
  invFun p :=
    ⟨(⟨p.1, p.2.1⟩, ⟨p.1 + m, p.2.2⟩), rfl⟩
  left_inv p := by
    rcases p with ⟨⟨⟨i, x⟩, ⟨j, y⟩⟩, h⟩
    change j = i + m at h
    subst j
    rfl
  right_inv p := by
    rcases p with ⟨i, x, y⟩
    rfl

/-- Cardinality form of `shiftedSigmaPairEquiv`. -/
theorem natCard_shiftedSigmaPair
    [Add A] [Fintype A] [∀ i, Finite (fiber i)] (m : A) :
    Nat.card {p : (Σ i, fiber i) × (Σ i, fiber i) //
      p.2.1 = p.1.1 + m} =
      ∑ i : A, Nat.card (fiber i) * Nat.card (fiber (i + m)) := by
  rw [Nat.card_congr (shiftedSigmaPairEquiv fiber m), Nat.card_sigma]
  simp [Nat.card_prod]

end Submission.OddOrder.MathlibSupport
