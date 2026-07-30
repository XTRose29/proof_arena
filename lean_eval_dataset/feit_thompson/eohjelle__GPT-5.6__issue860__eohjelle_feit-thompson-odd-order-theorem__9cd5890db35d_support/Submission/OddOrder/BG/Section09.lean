import Submission.OddOrder.BG.Section09.AnyCentralizerRankThreeUniqueness
import Submission.OddOrder.BG.Section09.AnyFittingRankThreeUniqueness
import Submission.OddOrder.BG.Section09.CentralizerUniqueMaximal
import Submission.OddOrder.BG.Section09.ExtremalPOverlap
import Submission.OddOrder.BG.Section09.NoncyclicCentralizerUniqueness
import Submission.OddOrder.BG.Section09.NoncyclicNormedSubUniqueness
import Submission.OddOrder.BG.Section09.NormalizedPrimeComplementCore
import Submission.OddOrder.BG.Section09.RankThreeUniqueness
import Submission.OddOrder.BG.Section09.SCNCommutatorUniqueMaximal
import Submission.OddOrder.BG.Section09.SCNFittingPrimeComplementCentralizer
import Submission.OddOrder.BG.Section09.SCNRankThreeSylowNormalizer
import Submission.OddOrder.BG.Section09.SCNRankThreeUniqueness
import Submission.OddOrder.BG.Section09.SylowNormalizerCommutator
import Submission.OddOrder.BG.Section09.SylowNormalizerContainment

/-!
Bender--Glauberman Section 9: uniqueness consequences of local rank.

The opening port proves both parts of Theorem 9.1.  For 9.1(b), an extremal
Sylow overlap and the prime-complement core force the Fitting subgroup of a
competing maximal subgroup into the chosen maximal subgroup; the rank-three
case uses Section 8 uniqueness and the rank-two case closes by the
Fitting--Frattini argument.  Theorem 9.1(a) derives the required normalized
`p'`-subgroup containment from the centralizers of the nonidentity elements
of the elementary-abelian subgroup.
Corollary 9.2 propagates uniqueness through a centralizing subgroup of
elementary-abelian rank at least two.  Corollary 9.3 combines two such
centralizer transfers around a normal rank-two subgroup of a Sylow subgroup,
and Corollary 9.4 applies that result to every rank-three `p`-subgroup when a
maximal subgroup has rank three in its Fitting subgroup.
Lemma 9.5 is complete.  Assuming a rank-three SCN subgroup were not unique,
the proof first rules out rank-three Fitting subgroups and forces the
associated Sylow normalizer into every relevant maximal subgroup.  It then
centralizes the Fitting prime-complement core by the Sylow-normalizer
commutator, proves that commutator's normalizer has a unique maximal
overgroup, and derives the final contradiction by applying that conclusion
to two maximal overgroups of the SCN centralizer.
The final Lemma 9.6 block upgrades rank-three uniqueness to arbitrary
rank-three subgroups, transfers it through centralizers, and proves the
nonmaximal rank-two elementary-abelian uniqueness criterion used in Section
10.  Thus the full Coq `BGsection9.v` file is now represented here.
-/

namespace Submission.OddOrder.BG.Section09

end Submission.OddOrder.BG.Section09
