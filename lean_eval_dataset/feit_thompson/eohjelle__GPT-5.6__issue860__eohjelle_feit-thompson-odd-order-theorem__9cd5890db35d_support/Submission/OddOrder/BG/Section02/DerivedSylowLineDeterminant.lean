import Submission.OddOrder.BG.Section02.DerivedSylowMaschkeLines
import Submission.OddOrder.MathlibSupport.RepresentationDeterminant
import Submission.OddOrder.MathlibSupport.RepresentationLineDeterminant

/-!
The determinant-one relation for the two derived-Sylow invariant lines in
`BGsection2.der1_odd_GL2_charf`.
-/

namespace Submission.OddOrder.BG.Section02

open Submission.OddOrder.MathlibSupport
open scoped MonoidAlgebra

universe u v w

variable {F : Type v} {G : Type u} {V : Type w}
  [Field F] [Group G] [AddCommGroup V] [Module F V]
  [FiniteDimensional F V]

/-- The scalar actions of a derived-Sylow element on complementary invariant
lines have product one. This is `ab1` in the source proof. -/
theorem derivedSylow_line_scalars_mul_eq_one
    {q : ℕ} (rho : Representation F G V) (Q : Sylow q G)
    (m n : Submodule F[derivedSylowPart Q]
      (derivedSylowRepresentation rho Q).asModule)
    (hmn : IsCompl m n) (x : derivedSylowPart Q) (a b : F)
    (hma : invariantLineAction (derivedSylowRepresentation rho Q) m x =
      a • LinearMap.id)
    (hna : invariantLineAction (derivedSylowRepresentation rho Q) n x =
      b • LinearMap.id)
    (hmdim : Module.finrank F (m.restrictScalars F) = 1)
    (hndim : Module.finrank F (n.restrictScalars F) = 1) :
    a * b = 1 := by
  have hmul : ((derivedSylowRepresentation rho Q) x).det = a * b :=
    representation_det_eq_mul_of_complementary_invariant_lines
      (derivedSylowRepresentation rho Q) m n hmn x a b hma hna hmdim hndim
  have hxcomm : (x : G) ∈ _root_.commutator G :=
    derivedSylowPart_le_commutator Q x.property
  have hxunit := representationDeterminant_eq_one_of_mem_commutator rho hxcomm
  have hxdet : (rho (x : G)).det = 1 := by
    have := congrArg Units.val hxunit
    simpa [representationDeterminant, representationLinearEquivHom,
      representationLinearEquiv] using this
  rw [← hmul]
  simpa [derivedSylowRepresentation] using hxdet

end Submission.OddOrder.BG.Section02
