import Mathlib.NumberTheory.MulChar.Duality
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Submission.OddOrder.PF.Section01.InertiaInductionCorrespondence

/-!
# Scalar characters of finite abelian groups

The proof of Peterfalvi 1.7(b) twists an inertia constituent by every
one-dimensional character of the abelian quotient.  We use `MulChar` as the
indexing type for those scalar characters and record its cardinality and
column-orthogonality sum.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical IsMulCommutative

universe u

namespace ClassFunction

variable {Q k : Type u} [Group Q] [Fintype Q] [IsMulCommutative Q]
  [Field k] [IsAlgClosed k] [CharZero k]

noncomputable instance mulCharFintype : Fintype (MulChar Q k) :=
  Fintype.ofFinite _

/-- A finite abelian group has as many scalar characters over an
algebraically closed characteristic-zero field as it has elements. -/
theorem natCard_mulChar_eq (Q k : Type u)
    [Group Q] [Fintype Q] [IsMulCommutative Q]
    [Field k] [IsAlgClosed k] [CharZero k] :
    Nat.card (MulChar Q k) = Nat.card Q := by
  calc
    Nat.card (MulChar Q k) = Nat.card Qˣ :=
      MulChar.card_eq_card_units_of_hasEnoughRootsOfUnity Q k
    _ = Nat.card Q := Nat.card_congr toUnits.toEquiv.symm

/-- Sum of all scalar characters of a finite abelian group. -/
theorem sum_mulChar_apply (q : Q) :
    (∑ chi : MulChar Q k, chi q) =
      if q = 1 then (Nat.card Q : k) else 0 := by
  by_cases hq : q = 1
  · subst q
    rw [if_pos rfl]
    simp only [map_one, Finset.sum_const, nsmul_eq_mul, mul_one,
      Finset.card_univ, ← Nat.card_eq_fintype_card]
    rw [natCard_mulChar_eq Q k]
  · rw [if_neg hq]
    obtain ⟨chi0, hchi0⟩ :=
      MulChar.exists_apply_ne_one_of_hasEnoughRootsOfUnity Q k hq
    let S : k := ∑ chi : MulChar Q k, chi q
    have htranslate : chi0 q * S = S := by
      calc
        chi0 q * S = ∑ chi : MulChar Q k, (chi0 * chi) q := by
          simp [S, Finset.mul_sum]
        _ = ∑ chi : MulChar Q k, chi q := by
          exact Fintype.sum_bijective _ (Group.mulLeft_bijective chi0)
            _ _ (fun _ ↦ rfl)
        _ = S := rfl
    exact eq_zero_of_mul_eq_self_left hchi0 htranslate

end ClassFunction

end

end Submission.OddOrder.PF
