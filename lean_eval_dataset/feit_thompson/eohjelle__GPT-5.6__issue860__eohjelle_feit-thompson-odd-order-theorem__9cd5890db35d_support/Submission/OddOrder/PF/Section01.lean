import Submission.OddOrder.PF.Section01.ClassFunction
import Submission.OddOrder.PF.Section01.ClassFunctionRingHom
import Submission.OddOrder.PF.Section01.ClassFunctionSupport
import Submission.OddOrder.PF.Section01.TwistedCharacterPairing
import Submission.OddOrder.PF.Section01.CentralInertiaInduction
import Submission.OddOrder.PF.Section01.CoprimeCyclotomicAutomorphism
import Submission.OddOrder.PF.Section01.HallCentralInertiaAssembly
import Submission.OddOrder.PF.Section01.Induction
import Submission.OddOrder.PF.Section01.InertiaInductionCorrespondence
import Submission.OddOrder.PF.Section01.IntegralLattice
import Submission.OddOrder.PF.Section01.IrreducibleCharacter
import Submission.OddOrder.PF.Section01.IrreducibleDegreeQuotientBound
import Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels
import Submission.OddOrder.PF.Section01.NormalSubgroupInduction
import Submission.OddOrder.PF.Section01.PiCharacterAutomorphism
import Submission.OddOrder.PF.Section01.PrimePrimitiveRootDivisibility
import Submission.OddOrder.PF.Section01.PrimitiveRootCharacterCongruence
import Submission.OddOrder.PF.Section01.QuotientDescent
import Submission.OddOrder.PF.Section01.QuotientInduction
import Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter
import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence
import Submission.OddOrder.PF.Section01.RestrictionComplementEquivalenceSet
import Submission.OddOrder.PF.Section01.SubgroupInductionConjugation
import Submission.OddOrder.PF.Section01.VirtualCharacter
import Submission.OddOrder.PF.Section01.VirtualCharacterInduction
import Submission.OddOrder.PF.Section01.VirtualCharacterIsometry
import Submission.OddOrder.PF.Section01.VirtualCharacterIsometryBase
import Submission.OddOrder.PF.Section01.VirtualCharacterNormTwo
import Submission.OddOrder.PF.Section01.VirtualCharacterOfFDRep
import Submission.OddOrder.PF.Section01.VirtualCharacterPullback

/-!
Peterfalvi Section 1: character-theory foundation.

This aggregate exposes the class-function, induction/restriction,
orthogonality, irreducible-character, and virtual-character substrate together
with Peterfalvi 1.3, the tuple-level integral-lattice form of 1.4, and the
normal-subgroup induction formulas and orbit dichotomy of 1.5.
It also includes Brauer's permutation argument, the representation-level
induction bridge, and the kernel, constituent, quotient-inflation, and
quotient-descent results completing 1.6.
It now also includes the full inertia-subgroup Clifford correspondence and
weighted induction expansion of Peterfalvi 1.7(a).
The abelian-inertia-quotient multiplicity, constituent-count, and degree
formulas of Peterfalvi 1.7(b), and their Hall-subgroup specialization with
multiplicity one in Peterfalvi 1.7(c), are included as well.
Finally, Peterfalvi 1.8 bounds an ambient irreducible degree by the index of
a subgroup times the square root of a central-quotient index.
Peterfalvi 1.9(a) extends a prescribed automorphism of one cyclotomic field
while fixing a cyclotomic field of coprime conductor.
Peterfalvi 1.9(b) then constructs a power automorphism on selected virtual-
character values while fixing the values at elements of coprime order.
Peterfalvi 1.10 completes the section with the primitive-root congruence for
virtual-character values and its integer-divisibility consequence.
The reusable class-function layer also includes pointwise transport of
coefficient values along a ring homomorphism.
It now also exposes the value-twisted and star pairings matching MathComp's
`cfdot` convention, together with their support-restriction laws.
The reusable expansion layer converts arbitrary finite-dimensional
representation characters to virtual characters, transports virtual
characters along group homomorphisms, induces them from arbitrary subgroups,
and identifies induction from conjugate subgroups.
-/

namespace Submission.OddOrder.PF.Section01

end Submission.OddOrder.PF.Section01
