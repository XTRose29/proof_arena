import Submission.OddOrder.BG.Section02.DerivedSylowMaschkeLines
import Submission.OddOrder.MathlibSupport.InvariantLineScalarPower

/-!
Power relations for the two derived-Sylow invariant-line scalars in
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [AddCommGroup V] [Module F V]

/-- Both invariant-line scalars inherit every power relation of the acting
derived-Sylow element. The first component is `ap1` in the source proof. -/
theorem derivedSylow_line_scalars_pow_eq_one
    {q n : ℕ} (rho : Representation F G V) (Q : Sylow q G)
    (m k : Submodule F[derivedSylowPart Q]
      (derivedSylowRepresentation rho Q).asModule)
    (x : derivedSylowPart Q) (hxpow : x ^ n = 1) (a b : F)
    (hma : invariantLineAction (derivedSylowRepresentation rho Q) m x =
      a • LinearMap.id)
    (hka : invariantLineAction (derivedSylowRepresentation rho Q) k x =
      b • LinearMap.id)
    (hmdim : Module.finrank F (m.restrictScalars F) = 1)
    (hkdim : Module.finrank F (k.restrictScalars F) = 1) :
    a ^ n = 1 ∧ b ^ n = 1 :=
  ⟨invariantLineScalar_pow_eq_one
      (derivedSylowRepresentation rho Q) m hmdim x n hxpow a hma,
    invariantLineScalar_pow_eq_one
      (derivedSylowRepresentation rho Q) k hkdim x n hxpow b hka⟩

end Submission.OddOrder.BG.Section02
