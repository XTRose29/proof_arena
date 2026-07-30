import Submission.OddOrder.BG.Section02.DerivedSylowLineDeterminant
import Submission.OddOrder.MathlibSupport.InvariantLineScalarSeparation

/-!
Distinct scalar actions on the two derived-Sylow invariant lines in
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- A nonidentity odd-order element of the derived-Sylow part has distinct
scalars on the two complementary invariant lines. This is `ne_ab` in the
source proof. -/
theorem derivedSylow_line_scalars_ne
    {q k : ℕ} (rho : Representation F G V)
    (hrho : Function.Injective rho) (Q : Sylow q G)
    (m n : Submodule F[derivedSylowPart Q]
      (derivedSylowRepresentation rho Q).asModule)
    (hmn : IsCompl m n) (x : derivedSylowPart Q) (hx : x ≠ 1)
    (hkodd : Odd k) (hkpow : x ^ k = 1) (a b : F)
    (hma : invariantLineAction (derivedSylowRepresentation rho Q) m x =
      a • LinearMap.id)
    (hna : invariantLineAction (derivedSylowRepresentation rho Q) n x =
      b • LinearMap.id)
    (hmdim : Module.finrank F (m.restrictScalars F) = 1)
    (hndim : Module.finrank F (n.restrictScalars F) = 1) :
    a ≠ b := by
  have hrhoQ : Function.Injective (derivedSylowRepresentation rho Q) := by
    intro y z hyz
    exact Subtype.ext (hrho hyz)
  have hab : a * b = 1 :=
    derivedSylow_line_scalars_mul_eq_one
      rho Q m n hmn x a b hma hna hmdim hndim
  exact invariantLineScalars_ne_of_odd
    (derivedSylowRepresentation rho Q) hrhoQ m n hmn x hx
    hkodd hkpow a b hma hna hmdim hab

end Submission.OddOrder.BG.Section02
