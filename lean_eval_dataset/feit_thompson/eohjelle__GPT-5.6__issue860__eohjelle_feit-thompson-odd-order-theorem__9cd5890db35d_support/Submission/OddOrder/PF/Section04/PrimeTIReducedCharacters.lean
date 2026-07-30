import Submission.OddOrder.PF.Section04.PrimeTICharacters

/-!
# Reduced columns of prime-TI irreducible characters

This file introduces the reduced columns used after Peterfalvi 4.3(c).  The
central object is the (usually reducible) column sum

`primeTIRed j = ∑ i, primeTICharacter i j`.

Ordinary characters are represented intrinsically in the virtual-character
lattice: a virtual character is ordinary when all its irreducible
coefficients are nonnegative.  This is the exact free-lattice counterpart of
the source predicate `\is a character` and avoids choosing a particular
iterated direct-sum realization.  The degree, automorphism, and structural
results for these columns are proved in the subsequent Section 4 modules.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators Classical

universe u v

variable {Gamma k : Type u} [Group Gamma] [Fintype Gamma]
  [Field k] [IsAlgClosed k] [CharZero k]
  {L K W W₁ W₂ : Subgroup Gamma}
  {defW : IsInternalDirectProductIn W₁ W₂ W}

local instance primeTIReducedInvertibleCard
    {H : Type u} [Group H] [Fintype H] :
    Invertible (Nat.card H : k) :=
  invertibleOfNonzero (Nat.cast_ne_zero.mpr Nat.card_pos.ne')

namespace VirtualCharacter

/-- A virtual character is ordinary when every irreducible coefficient is
nonnegative.  Since `VirtualCharacter` is the free integral lattice on the
irreducible characters, this is the intrinsic ordinary-character predicate. -/
def IsOrdinary {G : Type v} [Group G]
    (v : VirtualCharacter G k) : Prop :=
  ∀ chi, 0 ≤ v chi

end VirtualCharacter

namespace ClassFunction

/-- A class function is an ordinary character when it is realized by a
coefficientwise nonnegative virtual character. -/
def IsOrdinaryCharacter {G : Type v} [Group G]
    (phi : ClassFunction G k) : Prop :=
  ∃ v : VirtualCharacter G k,
    v.IsOrdinary ∧ VirtualCharacter.realize v = phi

end ClassFunction

namespace PrimeTIHypothesis

variable (h : PrimeTIHypothesis L K W W₁ W₂ defW)
  (iso : CyclicTIIsometryData (k := k) h.prime_cycTIhyp)

/-- The nonnegative virtual character underlying the reduced `j`-column. -/
def primeTIRedVirtualCharacter
    (j : IrreducibleCharacter W₂ k) : VirtualCharacter L k :=
  ∑ i : IrreducibleCharacter W₁ k,
    Finsupp.single (h.primeTIIndex iso (i, j)) 1

/-- The reducible column sum denoted `mu_ j` in the source. -/
def primeTIRed
    (j : IrreducibleCharacter W₂ k) : ClassFunction L k :=
  VirtualCharacter.realize (h.primeTIRedVirtualCharacter iso j)

@[simp]
theorem primeTIRed_eq_sum
    (j : IrreducibleCharacter W₂ k) :
    h.primeTIRed iso j =
      ∑ i : IrreducibleCharacter W₁ k,
        h.primeTICharacter iso i j := by
  simp [primeTIRed, primeTIRedVirtualCharacter, primeTICharacter]

/-- The source sequence `uniform_prTIred_seq`: reduced columns of the same
degree as `j₀`, with the trivial column removed. -/
def uniform_prTIred_seq
    (j₀ : IrreducibleCharacter W₂ k) : Set (ClassFunction L k) :=
  h.primeTIRed iso ''
    {j | j ≠ IrreducibleCharacter.trivial ∧
      h.primeTIRed iso j 1 = h.primeTIRed iso j₀ 1}

/-- Each reduced column is an ordinary character. -/
theorem prTIred_char (j : IrreducibleCharacter W₂ k) :
    ClassFunction.IsOrdinaryCharacter (h.primeTIRed iso j) := by
  refine ⟨h.primeTIRedVirtualCharacter iso j, ?_, rfl⟩
  intro chi
  rw [primeTIRedVirtualCharacter, Finsupp.finsetSum_apply]
  exact Finset.sum_nonneg fun i _ ↦ by
    by_cases hi : h.primeTIIndex iso (i, j) = chi <;>
      simp [Finsupp.single_apply, hi]

end PrimeTIHypothesis

end

end Submission.OddOrder.PF
