import Submission.OddOrder.BG.Section04.ExponentOddNil23
import Submission.OddOrder.BG.Section04.CoprimeMetacyclicCommutator
import Submission.OddOrder.BG.Section04.RankTwoExponentPrime
import Submission.OddOrder.BG.Section04.ExponentOmegaOneRankTwo
import Submission.OddOrder.BG.Section04.HuppertMetacyclic
import Submission.OddOrder.BG.Section04.MetacyclicOmegaOne
import Submission.OddOrder.BG.Section04.NormalRankTwo
import Submission.OddOrder.BG.Section04.OddNormalRankTwoExists
import Submission.OddOrder.BG.Section04.OddPGroupRankOne
import Submission.OddOrder.BG.Section04.OddZGroupRankOne
import Submission.OddOrder.BG.Section04.OmegaOneUpperCentral
import Submission.OddOrder.BG.Section04.QuotientOmegaOneRankTwo
import Submission.OddOrder.BG.Section04.RankTwoAutomorphismDerived
import Submission.OddOrder.BG.Section04.RankTwoChiefFactorCentralizer
import Submission.OddOrder.BG.Section04.RankTwoChiefFactorCoreFree
import Submission.OddOrder.BG.Section04.RankTwoCharacteristicSylowNormal
import Submission.OddOrder.BG.Section04.RankTwoCoprimeCommutatorCentralProduct
import Submission.OddOrder.BG.Section04.RankTwoDerivedComplement
import Submission.OddOrder.BG.Section04.RankTwoDerivedPrimeCore
import Submission.OddOrder.BG.Section04.RankTwoFittingDerived
import Submission.OddOrder.BG.Section04.RankTwoMaximalPrimeCoreSylow
import Submission.OddOrder.BG.Section04.RankTwoMinimalPrimeComplement
import Submission.OddOrder.BG.Section04.RankTwoMinimalPrimeCoreHall
import Submission.OddOrder.BG.Section04.RankTwoPGroupAutomorphismPrimes
import Submission.OddOrder.BG.Section04.RankTwoPrimeCutoffCoreHall
import Submission.OddOrder.BG.Section04.RankTwoPrimeDivisors
import Submission.OddOrder.BG.Section04.SCNSylowCentralizer
import Submission.OddOrder.BG.Section04.SCNRankThreeEmpty
import Submission.OddOrder.MathlibSupport.ExtraspecialCriticalCentralProduct

/-!
Bender-Glauberman Section 4: small-rank Fitting subgroup structure, through
the exact rank-two/empty-SCN-three equivalence of Lemma 4.7, the metacyclic
omega-one result of Lemma 4.10, and Huppert's metacyclicity criterion,
Proposition 4.11.  It now also includes the coprime-action splitting,
cyclic-factor conclusions, and derived-subgroup bound of Theorem 4.12.
Lemmas 4.13--4.14 then constrain every prime divisor of the automorphism
group of an odd `p`-group of rank at most two.
The critical-extraspecial central-product theorem cited for Lemma 4.15 is
included through its general support module.
Theorem 4.16 is included as well: a perfect coprime action on a nontrivial
odd rank-two `p`-group forces `3 < p` and either commutativity or an
extraspecial-by-cyclic central-product decomposition.
Theorem 4.17 proves that the derived subgroup of every odd solvable
automorphism group of such a `p`-group is itself a `p`-group.  All clauses of
Theorem 4.18 are included as well: prime-divisor bounds, the least-prime Hall
complement, the derived Hall `p'`-core, containment of derived `p'`-subgroups,
and the abelian `p'` quotient by `O_{p',p}`.
Corollary 4.19 proves that the ambient derived subgroup centralizes every
chief prime-power factor below a normal rank-two subgroup.  Theorem 4.20(a)
then applies Hall's chief-factor stabilizer criterion to place the derived
subgroup inside the Fitting subgroup.  Theorem 4.20(b) makes characteristic
subgroups of Sylow derived subgroups normal.  Its final clause constructs the
normal Hall factors associated to every prime cutoff, including the least-
prime `p'`-core and greatest-prime `p`-core endpoints.  This completes the
Lean port of Bender--Glauberman Section 4.
-/
