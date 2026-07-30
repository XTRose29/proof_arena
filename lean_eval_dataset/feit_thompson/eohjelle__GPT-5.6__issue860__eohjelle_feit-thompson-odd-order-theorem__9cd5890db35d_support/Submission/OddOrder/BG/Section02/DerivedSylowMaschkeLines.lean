import Submission.OddOrder.BG.Section02.DerivedSylowPartAbelian
import Submission.OddOrder.MathlibSupport.MaschkeTwoLines
import Submission.OddOrder.MathlibSupport.PGroupCardCast

/-!
The Maschke two-line decomposition for the derived-Sylow intersection in
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra IsMulCommutative

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [IsAlgClosed F] [Group G] [Finite G]
  [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Nontrivial V]

/-- The ambient representation restricted to the derived-Sylow part. -/
def derivedSylowRepresentation {q : ℕ}
    (rho : Representation F G V) (Q : Sylow q G) :
    Representation F (derivedSylowPart Q) V :=
  rho.comp (derivedSylowPart Q).subtype

/-- Restricting to an abelian derived-Sylow part yields complementary
one-dimensional invariant subspaces. -/
theorem exists_derivedSylow_complementary_lines
    {p q : ℕ} [CharP F p] [Fact p.Prime] [Fact q.Prime]
    (rho : Representation F G V) (hdim : Module.finrank F V = 2)
    (hpq : p ≠ q) (Q : Sylow q G)
    (habel : IsMulCommutative (derivedSylowPart Q)) :
    ∃ m n : Submodule F[derivedSylowPart Q]
        (derivedSylowRepresentation rho Q).asModule,
      IsSimpleModule F[derivedSylowPart Q] m ∧ IsCompl m n ∧
        Module.finrank F (m.restrictScalars F) = 1 ∧
        Module.finrank F (n.restrictScalars F) = 1 := by
  letI : IsMulCommutative (derivedSylowPart Q) := habel
  letI : NeZero (Nat.card (derivedSylowPart Q) : F) :=
    neZero_natCard_cast_of_isPGroup (derivedSylowPart_isPGroup Q) hpq
  exact exists_complementary_simpleLine_finrank_one
    (derivedSylowRepresentation rho Q) hdim

end Submission.OddOrder.BG.Section02
