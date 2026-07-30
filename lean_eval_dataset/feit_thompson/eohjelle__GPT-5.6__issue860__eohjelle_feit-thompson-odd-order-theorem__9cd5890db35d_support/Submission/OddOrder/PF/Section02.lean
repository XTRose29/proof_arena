import Submission.OddOrder.PF.Section02.ClassSupportPartition
import Submission.OddOrder.PF.Section02.DadeHypothesis
import Submission.OddOrder.PF.Section02.DadeCoverTI
import Submission.OddOrder.PF.Section02.DadeExpansion
import Submission.OddOrder.PF.Section02.DadeExpansionOrbitAveraging
import Submission.OddOrder.PF.Section02.DadeExpansionRestriction
import Submission.OddOrder.PF.Section02.DadeInducedVirtualCharacter
import Submission.OddOrder.PF.Section02.DadeInduction
import Submission.OddOrder.PF.Section02.DadeInductionExpansion
import Submission.OddOrder.PF.Section02.DadeInductionRestrictionConjugation
import Submission.OddOrder.PF.Section02.DadeMap
import Submission.OddOrder.PF.Section02.DadeBasicProperties
import Submission.OddOrder.PF.Section02.DadeAutomorphism
import Submission.OddOrder.PF.Section02.DadeSupportPartition
import Submission.OddOrder.PF.Section02.DadeReciprocity
import Submission.OddOrder.PF.Section02.DadeSignalizer
import Submission.OddOrder.PF.Section02.DadeSetCentralizer
import Submission.OddOrder.PF.Section02.DadeSetSignalizer
import Submission.OddOrder.PF.Section02.DadeSubsetOrbits
import Submission.OddOrder.PF.Section02.DadeSupportTI
import Submission.OddOrder.PF.Section02.DadeRestriction
import Submission.OddOrder.PF.Section02.DadeVirtualCharacter
import Submission.OddOrder.PF.Section02.DadeZIsometry
import Submission.OddOrder.PF.Section02.NormalizedTIDade
import Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset

/-!
Peterfalvi Section 2: Dade signalizers and the Dade isometry setup.

The current port covers Peterfalvi 2.1, the partition of a coprime
centralizer right coset by subgroup conjugates, and Definition 2.2, the
full Dade hypothesis with its shared signalizer family.  Peterfalvi 2.3
then constructs the canonical Dade signalizer and characterizes normalized
TI sets by its triviality.  Peterfalvi 2.4 establishes conjugation
equivariance of the signalizers and their class supports, proves the supports
are TI, and identifies the normalizer of every signalizer right coset.
The Definition 2.5 block constructs the global normal Dade support and the
associated linear map from class functions on `L` to class functions on `G`,
together with its evaluation formula on each first-support component.
The following block proves its support, identity, and coefficient-
automorphism properties through `Dade_conjC`.
The normalized-TI and support-block partitions yield the general Dade
reciprocity formula and its restriction specialization.  The resulting
`Dade_isometry` proves that the Dade map preserves the source-faithful star
pairing on functions supported on `A`; `Dade_Ind` also identifies the map with
ordinary induction under the normalized-TI hypothesis.
Peterfalvi 2.8 packages the common signalizer of a nonempty subset of `A`
and its internal semidirect product with the relative set normalizer.
The following expansion infrastructure chooses representatives for the
`L`-conjugacy orbits of nonempty Dade subsets and identifies the signalizer
of `insert a B` with the centralizer of `a` inside the signalizer of `B`.
Peterfalvi 2.9--2.10 then restricts class functions through each set
normalizer, proves conjugacy invariance of the induced terms, and evaluates
them by an explicit conjugator count.  The corresponding orbit-stabilizer
cardinality and virtual-character induction transports are available for
the global alternating expansion.  The expansion itself is integral on
virtual characters, and `Dade_Zisometry` packages both its star-pairing
isometry and its virtual-character image supported away from the identity.
Peterfalvi 2.11 shows that the Dade construction restricts functorially to an
`L`-stable subset, while the normalized-TI tail constructs the trivial
signalizer hypothesis and records the resulting induction identity and
star-pairing isometry.  This completes the Section 2 port.
-/

namespace Submission.OddOrder.PF.Section02

end Submission.OddOrder.PF.Section02
