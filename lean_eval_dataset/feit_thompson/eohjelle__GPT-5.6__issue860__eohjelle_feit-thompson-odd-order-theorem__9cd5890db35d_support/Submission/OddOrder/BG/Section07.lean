import Submission.OddOrder.BG.Section07.CentralCoreAction
import Submission.OddOrder.BG.Section07.MaximalSubgroups
import Submission.OddOrder.BG.Section07.MinimalCounterexample
import Submission.OddOrder.BG.Section07.NormedConstrainedHall
import Submission.OddOrder.BG.Section07.NormedConstrainedMeetTrans
import Submission.OddOrder.BG.Section07.PLengthOneNormedConstrained
import Submission.OddOrder.BG.Section07.SCNNormedConstrained
import Submission.OddOrder.BG.Section07.NormedConstrainedRankTwoTrans
import Submission.OddOrder.BG.Section07.NormedConstrainedRankThreeTrans
import Submission.OddOrder.BG.Section07.NormedTransSuperset
import Submission.OddOrder.BG.Section07.NormedSubgroups
import Submission.OddOrder.BG.Section07.ThompsonTransitivity
import Submission.OddOrder.BG.Section07.UniqueMaximal

/-!
Bender--Glauberman Section 7: the minimal odd-order counterexample and its
maximal subgroups.

The current port covers the minimal-counterexample induction and elementary
consequences through quotient solvability, then the opening maximal-subgroup
infrastructure through self-normality of every maximal subgroup.
It also includes the full consecutive unique-maximal-overgroup block through
the upward closure lemma `uniq_mmaxS`.
The normalized prime-set subgroup families and their maximality/uniqueness
lemmas are ported through `max_normed_uniq`, followed by the centralizer-core
action `cent_core_acts_max_norm` and the Hall-core observation immediately
preceding Lemma 7.1.
Lemma 7.1 itself is included as well: maximal normalized `q`-subgroups that
meet a common proper overgroup of `A` are conjugate by the prime-complement
core of `C_G(A)`.
Theorem 7.2 then removes the common-overgroup hypothesis when the center of
`A` has elementary-abelian rank at least three.
Theorem 7.3 obtains the same transitivity from centralizer divisibility when
the center of `A` has elementary-abelian rank at least two.
Theorem 7.4 transports this transitivity and the associated focal and
normalizer-factorization consequences along subnormal prime-set supersets.
Proposition 7.5(a) proves the normalized-constrained hypothesis for every
nontrivial maximal elementary-abelian subgroup when all proper subgroups
have p-length at most one.
Proposition 7.5(b) proves the same hypothesis for every SCN subgroup of
rank at least two.
Theorem 7.6 then combines the rank-three case with that constraint to obtain
Thompson transitivity under the mapped `p`-prime core of the centralizer.
-/

namespace Submission.OddOrder.BG.Section07

end Submission.OddOrder.BG.Section07
