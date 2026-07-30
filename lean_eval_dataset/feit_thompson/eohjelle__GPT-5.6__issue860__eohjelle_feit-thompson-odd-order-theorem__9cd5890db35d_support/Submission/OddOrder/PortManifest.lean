/-!
Compiled port manifest for the Feit-Thompson odd-order theorem.

This file records the intended source-to-target map for the MathComp odd-order
port.  It is intentionally data-only: proof modules should update the status
field as sections move from planned scaffolding to checked Lean formalization.
-/

namespace Submission.OddOrder

structure PortEntry where
  coqFile : String
  leanModule : String
  role : String
  mappedDeclarations : List String := []
  unresolvedGaps : List String := []
  notes : List String := []
  directDependencies : List String := []
  status : String
deriving Repr, DecidableEq

def mathlibSupportManifest : List PortEntry :=
  [ { coqFile := "mathlib/mathcomp support"
      leanModule := "Submission.OddOrder.MathlibSupport.Cardinality"
      role := "Nat.card, quotient-card, subgroup-card, and oddness wrappers"
      status := "complete" },
    { coqFile := "BGappendixAB.v: internal center and centralizer notation"
      leanModule := "Submission.OddOrder.MathlibSupport.Centralizer"
      role := "Subgroup-internal centralizers, centers, and finite p-group center support"
      status := "complete" },
    { coqFile := "mathcomp hall"
      leanModule := "Submission.OddOrder.MathlibSupport.Hall"
      role := "Prime-set Hall predicates, element-order/cardinality and coprime bridges, and complement existence"
      status := "complete" },
    { coqFile := "mathcomp solvable/hall.v: q'-Hall arithmetic"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeComplement"
      role := "Specialized prime-complement predicate, Sylow generation, and conjugation invariance"
      status := "complete" },
    { coqFile := "mathcomp solvable/hall.v: solvable q'-Hall existence"
      leanModule := "Submission.OddOrder.MathlibSupport.SolvablePrimeComplement"
      role := "Construct a q'-Hall subgroup of every finite solvable group by minimal-normal induction"
      status := "complete" },
    { coqFile := "mathcomp solvable/hall.v: Hall subgroup containment"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeComplementContainment"
      role := "Conjugate a q'-Hall subgroup to contain a prescribed coprime prime-order factor"
      status := "complete" },
    { coqFile := "BGsection3.v: q'-Hall intersection in the semidirect kernel"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeComplementIntersection"
      role := "Intersect a containing Hall subgroup with the normal kernel and prove normalization and Sylow generation"
      status := "complete" },
    { coqFile := "BGsection3.v: prime-order cyclic centralizer identity"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeOrderCentralizer"
      role := "Identify the centralizer of any nonidentity complement element with the centralizer of the whole prime-order complement"
      status := "complete" },
    { coqFile := "BGsection1.v: coprime_cent_prod in the prime-complement factorization"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimePrimeOrderCentralProduct"
      role := "Use local Sylow conjugacy to decompose the kernel into its mixed commutator and complement centralizer"
      status := "complete" },
    { coqFile := "BGsection1.v: coprime_commGid in the prime-complement factorization"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimePrimeOrderCommutator"
      role := "Derive idempotence of the coprime mixed commutator from the central-product decomposition"
      status := "complete" },
    { coqFile := "BGsection3.v: prime-product Sylow arithmetic"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeProductGroup"
      role := "Sylow orders, indices, normality, complements, and solvability for groups of order p*q"
      status := "complete" },
    { coqFile := "mathlib Sylow map support"
      leanModule := "Submission.OddOrder.MathlibSupport.SylowFunctorial"
      role := "Surjective images of Sylow subgroups onto p-group targets"
      status := "complete" },
    { coqFile := "BGappendixAB.v: lift cross-prime elements through local quotient maps"
      leanModule := "Submission.OddOrder.MathlibSupport.SylowSurjectiveElementLift"
      role := "Lift a p-element through a surjective homomorphism inside a Sylow p-subgroup of the source"
      status := "complete" },
    { coqFile := "BGsection1.v: Sylow intersection with a normal subgroup"
      leanModule := "Submission.OddOrder.MathlibSupport.SylowIntersection"
      role := "Realize the intersection of an ambient Sylow subgroup with a normal subgroup as a Sylow subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: max_SCN selection support"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalAbelian"
      role := "Normal abelian predicates and finite inclusion-maximal selection"
      status := "complete" },
    { coqFile := "BGsection1.v: minnormal_solvable_abelem"
      leanModule := "Submission.OddOrder.MathlibSupport.MinimalNormal"
      role := "Minimal normal subgroup API and the solvable elementary-abelian theorem"
      status := "complete" },
    { coqFile := "BGappendixAB.v: minnormal_solvable local form"
      leanModule := "Submission.OddOrder.MathlibSupport.MinimalNormalElementaryAbelian"
      role := "Elementary-abelian structure assuming solvability only of the minimal normal subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: abelem_repr and rker_abelem"
      leanModule := "Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation"
      role := "Normalizer conjugation representation over ZMod p with centralizer kernel"
      status := "complete" },
    { coqFile := "BGappendixAB.v: abelem invariant-subspace bridge"
      leanModule := "Submission.OddOrder.MathlibSupport.ElementaryAbelianSubmodule"
      role := "Identify ZMod p submodules of Additive E with multiplicative subgroups of E"
      status := "complete" },
    { coqFile := "BGappendixAB.v: abelem_mx_irrP"
      leanModule := "Submission.OddOrder.MathlibSupport.ElementaryAbelianIrreducible"
      role := "Derive irreducibility of restricted conjugation from minimal invariant subgroups"
      status := "complete" },
    { coqFile := "BGappendixAB.v: minnormal E G to irrG"
      leanModule := "Submission.OddOrder.MathlibSupport.MinimalNormalUnder"
      role := "Express local minimal normality and derive irreducibility of conjugation"
      status := "complete" },
    { coqFile := "BGappendixAB.v: mingroup selection relative to the generated pair"
      leanModule := "Submission.OddOrder.MathlibSupport.MinimalNormalUnderExistence"
      role := "Select a minimal nontrivial subgroup inside E normalized by a prescribed acting subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: minnormal_solvable_abelem relative form"
      leanModule := "Submission.OddOrder.MathlibSupport.MinimalNormalUnderElementaryAbelian"
      role := "Show that a finite p-subgroup minimal normal under an acting subgroup is commutative and has exponent p"
      status := "complete" },
    { coqFile := "BGappendixAB.v: characteristic subgroup invariance under local normalizers"
      leanModule := "Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer"
      role := "Show that characteristic subgroups of E remain invariant under every acting subgroup contained in N_G(E)"
      status := "complete" },
    { coqFile := "BGappendixAB.v: kquo_repr and kquo_mx_faithful"
      leanModule := "Submission.OddOrder.MathlibSupport.FaithfulQuotientRepresentation"
      role := "Factor any representation through its kernel and prove the quotient representation faithful"
      status := "complete" },
    { coqFile := "BGappendixAB.v: faithful local abelem representation"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalConjugationRepresentation"
      role := "Descend conjugation to N(E)/C(E) and restrict it faithfully to local subgroups"
      status := "complete" },
    { coqFile := "BGappendixAB.v: Ax2 and Ay2"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticRepresentation"
      role := "Show quadratic conjugation deviations from the identity are square-zero linear maps"
      status := "complete" },
    { coqFile := "BGappendixAB.v: central anticommutator algebra"
      leanModule := "Submission.OddOrder.MathlibSupport.SquareZeroAnticommutator"
      role := "Show the anticommutator of two square-zero operators commutes with both"
      status := "complete" },
    { coqFile := "BGappendixAB.v: definition of A and generator centrality"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticAnticommutator"
      role := "Construct the quadratic anticommutator and prove it commutes with both representation generators"
      status := "complete" },
    { coqFile := "BGappendixAB.v: centgmx generated-subgroup support"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationCentralizer"
      role := "Package elements centralizing a fixed represented endomorphism as a subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: cAG"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticAnticommutatorCentral"
      role := "Prove the quadratic anticommutator centralizes the represented local two-generator group"
      status := "complete" },
    { coqFile := "BGappendixAB.v: central matrix as module endomorphism"
      leanModule := "Submission.OddOrder.MathlibSupport.CentralIntertwining"
      role := "Package an endomorphism centralizing a representation as an intertwining map"
      status := "complete" },
    { coqFile := "BGappendixAB.v: A as a local intertwining endomorphism"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticCentralIntertwining"
      role := "Bundle the quadratic anticommutator in the local representation endomorphism ring"
      status := "complete" },
    { coqFile := "BGappendixAB.v: gen_of field support"
      leanModule := "Submission.OddOrder.MathlibSupport.FiniteSchurField"
      role := "Use Schur and Little Wedderburn to construct the finite endomorphism field"
      status := "complete" },
    { coqFile := "mathlib support: finite carrier implies finite free module"
      leanModule := "Submission.OddOrder.MathlibSupport.FiniteCarrierModule"
      role := "Derive module-finiteness from a finite underlying carrier by choosing a finite basis"
      status := "complete" },
    { coqFile := "BGappendixAB.v: gen_repr"
      leanModule := "Submission.OddOrder.MathlibSupport.SchurScalarRepresentation"
      role := "View the original group action as linear over its Schur endomorphism field"
      status := "complete" },
    { coqFile := "BGappendixAB.v: gen_mx_irr scalar-extension support"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleScalarExtension"
      role := "Preserve irreducibility when the same action is linear over an extended scalar field"
      status := "complete" },
    { coqFile := "BGappendixAB.v: irrG restriction and quotient-action support"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationIrreducibleComp"
      role := "Transfer irreducibility from an action composed with a monoid homomorphism to the original representation"
      status := "complete" },
    { coqFile := "BGappendixAB.v: gen_mx_irr"
      leanModule := "Submission.OddOrder.MathlibSupport.SchurScalarIrreducible"
      role := "Prove irreducibility of the representation over its canonical finite Schur field"
      status := "complete" },
    { coqFile := "BGappendixAB.v: in_gen, val_gen, Ax2, Ay2, and mxval_groot"
      leanModule := "Submission.OddOrder.MathlibSupport.SchurAnticommutatorScalar"
      role := "Transport deviations to the group-module carrier and realize the central anticommutator as a Schur-field scalar"
      status := "complete" },
    { coqFile := "BGappendixAB.v: U, Umod, and rank_leq_row"
      leanModule := "Submission.OddOrder.MathlibSupport.SquareZeroPairSpan"
      role := "Construct the stable span of Xu and YXu and prove its dimension at most two"
      status := "complete" },
    { coqFile := "BGappendixAB.v: Umod invariant under <<x, y>>"
      leanModule := "Submission.OddOrder.BG.AppendixAB.SquareZeroPairGenerated"
      role := "Package the square-zero pair span as a subrepresentation of the pair-generated group"
      status := "complete" },
    { coqFile := "BGappendixAB.v: irrG, Umod != 0, and dim_leq2"
      leanModule := "Submission.OddOrder.BG.AppendixAB.SquareZeroIrreducibleDimension"
      role := "Use irreducibility to identify the pair span with the whole module and bound its dimension by two"
      status := "complete" },
    { coqFile := "BGappendixAB.v: defG, irrAG, nzU, and dim_leq2"
      leanModule := "Submission.OddOrder.BG.AppendixAB.SquareZeroGeneratedTopDimension"
      role := "Apply the pair-span argument directly when the two quadratic elements generate the acting group"
      status := "complete" },
    { coqFile := "BGappendixAB.v: FA, rAG, irrAG, and dA <= 2"
      leanModule := "Submission.OddOrder.BG.AppendixAB.SchurPairDimension"
      role := "Compose Schur scalarization, irreducibility, and the pair-span argument into the canonical dimension bound"
      status := "complete" },
    { coqFile := "BGappendixAB.v: dA_gt0 and def_dA = 2"
      leanModule := "Submission.OddOrder.BG.AppendixAB.SchurPairDimensionTwo"
      role := "Use finite-carrier positivity and noncommutation to force canonical Schur dimension exactly two"
      status := "complete" },
    { coqFile := "BGappendixAB.v: der1_odd_GL2_charf application at dA = 2"
      leanModule := "Submission.OddOrder.BG.AppendixAB.SchurTwoDimensionalBranch"
      role := "Transfer the faithful local action to its characteristic-p Schur field and apply the odd GL2 theorem to make the local commutator a p-group"
      status := "complete" },
    { coqFile := "BGappendixAB.v: noncommuting local quadratic-pair branch"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalSchurNoncommutingBranch"
      role := "Restrict conjugation to the generated quotient pair, derive square-zero deviations and the central intertwiner, force Schur dimension two, and conclude the local commutator is a p-group"
      status := "complete" },
    { coqFile := "BGappendixAB.v: complete irreducible local quadratic-pair branch"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalSchurQuadraticBranch"
      role := "Inherit oddness through the normalizer quotient and combine the commuting and noncommuting represented-generator cases into a p-primary local commutator"
      status := "complete" },
    { coqFile := "BGappendixAB.v: defG and local quotient image"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalQuotientPairHom"
      role := "Map the pair-generated subgroup inside the normalizer surjectively onto its local quotient pair and identify the pulled-back conjugation action"
      status := "complete" },
    { coqFile := "BGappendixAB.v: common-domain action kernels for E and its invariant subgroups"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PairGeneratedLocalQuotientHom"
      role := "Map pairGenerated x y onto each local quotient pair, identify its kernel with the relevant centralizer, and prove kernel monotonicity under M <= E"
      status := "complete" },
    { coqFile := "BGappendixAB.v: restriction from the action on E to the action on M <= E"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalQuotientPairRestriction"
      role := "Induce a surjective homomorphism between nested local quotient pairs and map the larger derived subgroup onto the smaller derived subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: lift the p-primary local derived subgroup across restriction"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalQuotientPairRestrictionPGroup"
      role := "Reduce p-primary structure of the larger local derived subgroup to the smaller derived subgroup and the restricted action kernel"
      status := "complete" },
    { coqFile := "BGappendixAB.v: q != p reduction inside the restriction kernel"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalQuotientPairRestrictionPrimeOrder"
      role := "Reduce p-primary structure of the restriction kernel to triviality of its elements of prime order q different from p"
      status := "complete" },
    { coqFile := "BGappendixAB.v: Sylow lift of a restriction-kernel element"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalRestrictionKernelSylowLift"
      role := "Lift a prime-order restriction-kernel element to a Sylow subgroup of the pair-generated group while retaining trivial action on the smaller subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: cyclic q-subgroup attached to a restriction-kernel element"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalRestrictionKernelCyclicLift"
      role := "Package a lifted kernel element into a q-primary cyclic subgroup that centralizes the smaller invariant subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: stable-factor elimination of the restriction kernel"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalRestrictionKernelStableFactor"
      role := "Use coprime stable-factor centralization to eliminate cross-prime kernel elements once their cyclic lifts act trivially on E/M"
      status := "complete" },
    { coqFile := "BGappendixAB.v: cyclic quotient action used by stable_factor_cent"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PairGeneratedFactorAction"
      role := "Attach a canonical action on E/(M intersect E) to each pair-generated cyclic lift and feed action triviality into the local p-group reduction"
      status := "complete" },
    { coqFile := "BGappendixAB.v: oddness of the local quotient generated by x and y"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalQuotientPairOdd"
      role := "Transfer odd cardinality from the ambient pair-generated subgroup through its canonical surjection onto the local quotient pair"
      status := "complete" },
    { coqFile := "BGappendixAB.v: irrG and the minimal-normal quadratic branch"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalMinimalNormalQuadraticBranch"
      role := "Derive irreducibility from minimal normality under the generated pair and conclude that the local quadratic commutator is a p-group"
      status := "complete" },
    { coqFile := "BGappendixAB.v: minnormal_solvable_abelem through the local Schur conclusion"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalMinimalNormalPGroupBranch"
      role := "Install the canonical elementary-abelian ZMod p structure for a minimal normal p-subgroup and conclude that the local quadratic commutator is a p-group"
      status := "complete" },
    { coqFile := "BGappendixAB.v: minimal-normal branch under odd <<x, y>>"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalMinimalNormalPairOddBranch"
      role := "Run the complete minimal-normal quadratic branch using only oddness of the ambient pair-generated subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: mingroup restriction of p_xp to a minimal invariant subgroup"
      leanModule := "Submission.OddOrder.BG.AppendixAB.MinimalQuadraticSubgroup"
      role := "Select a minimal invariant p-subgroup and restrict both normalizer and quadratic-pair hypotheses to it"
      status := "complete" },
    { coqFile := "BGappendixAB.v: selected minimal subgroup local conclusion"
      leanModule := "Submission.OddOrder.BG.AppendixAB.SelectedMinimalQuadraticBranch"
      role := "Select a minimal invariant subgroup from a nontrivial quadratic p-subgroup and discharge its pair-odd local commutator conclusion"
      status := "complete" },
    { coqFile := "BGappendixAB.v: mx11_scalar support"
      leanModule := "Submission.OddOrder.MathlibSupport.OneDimensionalEndomorphism"
      role := "Show all endomorphisms of a one-dimensional vector space commute"
      status := "complete" },
    { coqFile := "BGappendixAB.v: dA = 1 implies represented commutators vanish"
      leanModule := "Submission.OddOrder.MathlibSupport.SchurOneDimensional"
      role := "Reflect rank-one commutation from the canonical Schur representation to the original action"
      status := "complete" },
    { coqFile := "mathcomp maximal.v: special and extraspecial support for BGsection2 Theorem 2.5"
      leanModule := "Submission.OddOrder.MathlibSupport.Extraspecial"
      role := "Define extraspecial groups and derive prime-center, nonabelian, and center-order-p facts"
      status := "complete" },
    { coqFile := "mathcomp fingroup.v and maximal.v: Burnside basis support for finite p-groups"
      leanModule := "Submission.OddOrder.MathlibSupport.FrattiniPGroup"
      role := "Show maximal-subgroup quotients have order p and the Frattini quotient has exponent p"
      status := "complete" },
    { coqFile := "BGsection3.v: odd-order exclusion of the exceptional equality after Theorem 2.5"
      leanModule := "Submission.OddOrder.MathlibSupport.OddPrimePowerSucc"
      role := "Rule out h = p^n + 1 when both the complement order and base prime are odd"
      status := "complete" },
    { coqFile := "BGsection2.v: rfix_mx cyclic-complement kernel bridge in Theorem 2.5"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicInvariantKernel"
      role := "Identify cyclic common fixed vectors with the kernel of a generator minus identity"
      status := "complete" },
    { coqFile := "mathcomp maximal.v and mxabelem.v: center quotient of an extraspecial group"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotient"
      role := "Show the extraspecial center quotient is nontrivial and abelian"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: extraspecial center-quotient order in Theorem 2.5"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientCard"
      role := "Show an extraspecial p-group of order p^(2n+1) has center quotient order p^(2n)"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: central commutator form for extraspecial representation structure"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialCommutatorPairing"
      role := "Construct the central commutator pairing, prove bilinearity, and identify its radical with the center"
      status := "complete" },
    { coqFile := "PFsection11.v: class-two quotient commutator pairing support for Peterfalvi (11.7)"
      leanModule := "Submission.OddOrder.MathlibSupport.ClassTwoQuotientCommutatorPairing"
      role := "Construct and evaluate the generic commutator pairing from an abelianization into a central derived quotient, without packaging any PF11 conclusion"
      mappedDeclarations :=
        [ "classTwoQuotientCommutatorPairing",
          "classTwoQuotientCommutatorPairing_mk_mk" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.CentralCommutatorPowers" ]
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: symplectic form on the extraspecial center quotient"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientPairing"
      role := "Descend the central commutator pairing to the center quotient and prove nondegeneracy"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: alternating extraspecial quotient form"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientAlternating"
      role := "Prove the quotient commutator form is alternating, skew-symmetric, and nondegenerate on both sides"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: elementary-abelian extraspecial center quotient"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientExponent"
      role := "Prove every nontrivial center-quotient element has order p and the quotient has exponent p"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: vector-space structure on extraspecial center and quotient"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientModule"
      role := "Install canonical ZMod p module structures on the additive center and center quotient"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: bilinear extraspecial commutator form"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientBilinear"
      role := "Linearize the nondegenerate alternating quotient pairing as a ZMod p map into the dual"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: extraspecial center and quotient dimensions"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientFinrank"
      role := "Compute center dimension one and center-quotient dimension 2n from the extraspecial order formula"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: TI_center_nil faithfulness reductions"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialNormal"
      role := "Show nontrivial normal subgroups contain the center and reduce homomorphism injectivity to the center"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: irr_center_scalar and faithful center restriction"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleCenterCharacter"
      role := "Construct the center character in group-algebra endomorphism units and characterize representation faithfulness"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: irr_center_scalar over a splitting field"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleCenterScalar"
      role := "Identify irreducible central actions with base-field scalars and compute their ordinary character values"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: faithful center-character criterion"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialCenterFaithfulness"
      role := "Detect faithfulness of extraspecial representations by a nontrivial prime-order center character"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: phiZ and primitive central values"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialCenterCharacter"
      role := "Produce primitive pth roots from faithful irreducible extraspecial center-character values"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: nonlinear character support on the center"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialCharacterVanishing"
      role := "Use a nontrivial central commutator to prove faithful irreducible characters vanish off the center"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: faithful_repr_extraspecial_pchar degree"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleDegree"
      role := "Derive the p^n degree of faithful irreducibles directly from center support and character orthogonality"
      status := "complete" },
    { coqFile := "mathcomp character orthogonality: irreducible character rigidity"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleCharacterRigidity"
      role := "Recover equivalence of irreducible representations from equality of their ordinary characters"
      status := "complete" },
    { coqFile := "mathcomp mxabelem.v: faithful_repr_extraspecial_pchar rigidity"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleRigidity"
      role := "Determine faithful irreducible extraspecial representations by their scalar center character"
      status := "complete" },
    { coqFile := "mathcomp representation twists by group automorphisms"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationAutomorphismTwist"
      role := "Preserve faithfulness, irreducibility, and character evaluation under automorphism precomposition"
      status := "complete" },
    { coqFile := "BGsection2.v: center character under complement conjugation"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleCenterScalarTwist"
      role := "Keep scalar Schur center characters unchanged under automorphisms fixing the center pointwise"
      status := "complete" },
    { coqFile := "BGsection2.v: extraspecial constituent invariance under conjugation"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialAutomorphismRigidity"
      role := "Equate faithful extraspecial irreducibles with every center-fixing automorphism twist"
      status := "complete" },
    { coqFile := "BGsection2.v: Clifford_iso for ambient conjugates"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialConjugationRigidity"
      role := "Turn ambient centralization of the internal center into equivalence with the conjugate representation twist"
      status := "complete" },
    { coqFile := "mathcomp Clifford support: conjugates of normal-restriction constituents"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalRestrictionConjugates"
      role := "Translate normal-restriction subrepresentations by ambient elements as lattice order automorphisms"
      status := "complete" },
    { coqFile := "mathcomp Clifford support: simple constituents as lattice atoms"
      leanModule := "Submission.OddOrder.MathlibSupport.SubrepresentationInterval"
      role := "Identify subrepresentations of a constituent with the ambient interval below it and characterize simplicity by atomicity"
      status := "complete" },
    { coqFile := "mathcomp Clifford support: conjugate constituent invariants"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalRestrictionConstituents"
      role := "Preserve simplicity and dimension when translating normal-restriction constituents by ambient elements"
      status := "complete" },
    { coqFile := "mathcomp Clifford support: normal constituent orbit span"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentOrbit"
      role := "Build the finite orbit supremum of a normal constituent and show ambient irreducibility makes it span the whole representation"
      status := "complete" },
    { coqFile := "mathcomp Clifford support: distinct conjugate constituents"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentOrbitFinset"
      role := "Deduplicate the constituent orbit, prove distinct simple translates are disjoint, and recover the same finite supremum"
      status := "complete" },
    { coqFile := "mathcomp Clifford support: constituent subspace stabilizer"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentSubspaceStabilizer"
      role := "Define the ambient action on the restriction lattice, contain N in each subspace stabilizer, and identify its index with the orbit size"
      status := "complete" },
    { coqFile := "mathcomp Clifford support: constituent twist-translate equivalence"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentTwistEquiv"
      role := "Identify the inverse-conjugation twist of a normal constituent with the representation on its translated subspace"
      status := "complete" },
    { coqFile := "mathcomp Clifford support: character inertia subgroup"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentCharacterStabilizer"
      role := "Define constituent character inertia and characterize membership by equivalence to twists and translated constituent representations"
      status := "complete" },
    { coqFile := "BGsection2.v: full inertia of the extraspecial constituent"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialCharacterInertia"
      role := "Use center-centralizing extraspecial rigidity to make the faithful simple constituent's character inertia equal the ambient group"
      status := "complete" },
    { coqFile := "mathlib Clifford support: representation/module equivalences"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationModuleEquiv"
      role := "Convert representation equivalences to and from linear equivalences over the monoid algebra"
      status := "complete" },
    { coqFile := "mathlib Clifford support: subrepresentation module equivalence"
      leanModule := "Submission.OddOrder.MathlibSupport.SubrepresentationModuleEquiv"
      role := "Identify the module of a subrepresentation with its ambient monoid-algebra submodule and transport simplicity and equivalence"
      status := "complete" },
    { coqFile := "mathlib Clifford support: semisimple isotypic spanning"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationIsotypic"
      role := "Show every simple constituent is equivalent to a member of any finite simple family spanning a semisimple representation"
      status := "complete" },
    { coqFile := "BGsection2.v: Clifford homogeneity under full inertia"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalRestrictionIsotypic"
      role := "Use Maschke, ambient orbit spanning, and full character inertia to prove the normal restriction is isotypic"
      status := "complete" },
    { coqFile := "BGsection2.v: enveloping algebra density in mx_irr_prime_index"
      leanModule := "Submission.OddOrder.MathlibSupport.BurnsideDensity"
      role := "Use Jacobson density and Schur's lemma to make the acting algebra surject onto all linear endomorphisms of a finite-dimensional simple module"
      status := "complete" },
    { coqFile := "BGsection2.v: matrix-algebra form of enveloping algebra density"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationBurnsideDensity"
      role := "Transport density across the representation module equivalence and prove that the monoid-algebra action map is surjective"
      status := "complete" },
    { coqFile := "BGsection2.v: cyclic quotient generator and defG in mx_irr_prime_index"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicQuotientGenerator"
      role := "Lift a cyclic quotient generator, decompose every ambient element modulo the normal subgroup, and prove the lift together with the subgroup generates the whole group"
      status := "complete" },
    { coqFile := "BGsection2.v: absM enveloping-algebra extension in mx_irr_prime_index"
      leanModule := "Submission.OddOrder.MathlibSupport.SubrepresentationBurnsideExtension"
      role := "Embed a subgroup algebra into the ambient group algebra and realize every endomorphism of a finite-dimensional simple constituent by its ambient action"
      status := "complete" },
    { coqFile := "BGsection2.v: hom_envelop_mxC conjugation support in cHtau_x"
      leanModule := "Submission.OddOrder.MathlibSupport.SubgroupAlgebraConjugation"
      role := "Identify conjugation of a normal subgroup-algebra element with conjugation of its represented ambient endomorphism"
      status := "complete" },
    { coqFile := "BGsection2.v: Clifford_basis and def1 extensionality in mx_irr_prime_index"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentOrbitExt"
      role := "Use the top orbit span of a nonzero normal constituent to prove ambient linear maps equal from agreement on every translated constituent"
      status := "complete" },
    { coqFile := "BGsection2.v: hom_f and enveloping-algebra factorization in cHtau_x"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentIntertwinerFactor"
      role := "Factor an equivalence from a simple normal constituent to an ambient translate as translation after a normal subgroup-algebra operator"
      status := "complete" },
    { coqFile := "BGsection2.v: hom_envelop_mxC transport across Clifford isomorphisms"
      leanModule := "Submission.OddOrder.MathlibSupport.SubrepresentationAlgebraIntertwiner"
      role := "Extend a subrepresentation equivalence's group intertwining equation to the action of every subgroup-algebra element"
      status := "complete" },
    { coqFile := "BGsection2.v: tau'K in mx_irr_prime_index"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentAlgebraExt"
      role := "Propagate equality and one-sided inverse identities for normal subgroup-algebra actions from one constituent through all equivalent translates to the ambient irreducible module"
      status := "complete" },
    { coqFile := "BGsection2.v: tau, tau', defMtau, defMtau', and tau'K package"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentCorrectionPair"
      role := "Construct subgroup-algebra correction operators for a constituent translate equivalence and prove their corrected-action and ambient inverse identities"
      status := "complete" },
    { coqFile := "BGsection2.v: cHtau_x in mx_irr_prime_index"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentCorrectedCentralizer"
      role := "Correct ambient translation by a normal subgroup-algebra operator and prove the resulting endomorphism commutes with the whole normal subgroup action"
      status := "complete" },
    { coqFile := "BGsection2.v: envelop_mxP linear extension used in cGtau_x"
      leanModule := "Submission.OddOrder.MathlibSupport.SubgroupAlgebraCentralizer"
      role := "Extend commutation with every represented subgroup element to commutation with every element of the represented subgroup algebra"
      status := "complete" },
    { coqFile := "BGsection2.v: cGtau_x in mx_irr_prime_index"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalConstituentCyclicCentralizer"
      role := "Use the correction inverse and cyclic quotient generation to upgrade normal-subgroup commutation to commutation with the full ambient representation"
      status := "complete" },
    { coqFile := "BGsection2.v: mx_abs_irr_cent_scalar and def_tau_x"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleCommutantScalar"
      role := "Apply Schur's lemma over an algebraically closed field to identify every ambient endomorphism commuting with an irreducible representation as scalar"
      status := "complete" },
    { coqFile := "BGsection2.v: mx_irr_prime_index (Bender-Glauberman Proposition 2.2(a))"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalRestrictionCyclicIrreducible"
      role := "Combine cyclic quotient generation, full constituent inertia, Burnside density, and Schur's lemma to prove the normal restriction irreducible"
      status := "complete" },
    { coqFile := "BGsection2.v: irrP step inside repr_extraspecial_prime_sdprod_cycle (Theorem 2.5)"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialNormalRestrictionIrreducible"
      role := "Combine extraspecial full character inertia with cyclic Clifford theory to prove irreducibility of the restriction to the normal extraspecial subgroup"
      status := "complete" },
    { coqFile := "BGsection2.v: def_q after irrP in repr_extraspecial_prime_sdprod_cycle"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialNormalRestrictionDegree"
      role := "Carry ambient faithfulness to the normal extraspecial restriction and derive the representation degree p^n from its irreducibility"
      status := "complete" },
    { coqFile := "BGsection2.v: EPfull after absP in repr_extraspecial_prime_sdprod_cycle"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleRestrictionBurnsideDensity"
      role := "Identify the embedded subgroup-algebra action with the restriction's algebra map and use Burnside density to realize every ambient endomorphism"
      status := "complete" },
    { coqFile := "BGsection2.v: gE conjugation action in repr_extraspecial_prime_sdprod_cycle"
      leanModule := "Submission.OddOrder.MathlibSupport.EndomorphismConjugationRepresentation"
      role := "Represent the ambient group on End(V) by conjugation, fix scalar endomorphisms, and identify invariant endomorphisms with the representation commutant"
      status := "complete" },
    { coqFile := "BGsection2.v: invertibility of the gE inverse-conjugation operator"
      leanModule := "Submission.OddOrder.MathlibSupport.LinearEquivConjugationEquiv"
      role := "Bundle inverse conjugation on End(V) as a linear equivalence whose underlying map is the existing eigenspace operator"
      status := "complete" },
    { coqFile := "BGsection2.v: scalar line contribution to rankE0"
      leanModule := "Submission.OddOrder.MathlibSupport.EndomorphismConjugationInvariants"
      role := "Identify invariant endomorphisms under conjugation with self-intertwining maps and prove their space is one-dimensional for an irreducible representation"
      status := "complete" },
    { coqFile := "BGsection2.v: eigenvalue-one term in rankE0"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicGeneratorEigenspace"
      role := "Identify the eigenvalue-one eigenspace of a cyclic generator with invariants and compute its dimension for the endomorphism conjugation representation"
      status := "complete" },
    { coqFile := "BGsection2.v: represented-element linear-equivalence support"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationLinearEquivBasic"
      role := "Provide the shared linear equivalence underlying a represented group element for determinant and inverse-conjugation arguments"
      status := "complete" },
    { coqFile := "BGsection2.v: representation-facing gE, gh1, and eigenvalue-one inverse-conjugation bridge"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationLinearEquiv"
      role := "Bundle represented elements as linear equivalences, transport group power relations, identify inverse conjugation with the conjugation representation at the inverse, and transfer the irreducible cyclic invariant-line computation"
      status := "complete" },
    { coqFile := "BGsection2.v: dxE in repr_extraspecial_prime_sdprod_cycle"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimitiveRootEigenspaces"
      role := "Prove independence and pairwise disjointness of eigenspaces indexed by powers of a primitive root"
      status := "complete" },
    { coqFile := "BGsection2.v: splitting-field and Maschke core of mxdirect_sum_eigenspace_cycle (Proposition 2.4(a)), algebraically closed form"
      leanModule := "Submission.OddOrder.MathlibSupport.FiniteOrderPrimitiveRootEigenspaces"
      role := "Use the squarefree annihilator X^h - 1 to prove that a finite-order operator is spanned by primitive-root indexed eigenspaces"
      status := "complete" },
    { coqFile := "BGsection2.v: total-rank consequence of mxdirect_sum_eigenspace_cycle (Proposition 2.4(a))"
      leanModule := "Submission.OddOrder.MathlibSupport.IndependentSubmoduleFinrank"
      role := "Compute finrank from a finite internal direct sum and specialize to primitive-root indexed eigenspaces"
      status := "complete" },
    { coqFile := "BGsection2.v: coordinate block counting in mxdirect_sum_proj_eigenspace_cycle and rank_proj_eigenspace_cycle (Proposition 2.4(c)-(d))"
      leanModule := "Submission.OddOrder.MathlibSupport.MatrixEntrywiseEigenspace"
      role := "Identify an entrywise-scaling matrix eigenspace with functions on matching coordinate pairs and compute its finrank"
      status := "complete" },
    { coqFile := "BGsection2.v: shifted coordinate-pair count in rank_quasi_cent_cycle (Proposition 2.4(g))"
      leanModule := "Submission.OddOrder.MathlibSupport.ShiftedSigmaPairCard"
      role := "Count dependent coordinate pairs whose eigenspace indices differ by a fixed cyclic shift as the corresponding rank autocorrelation sum"
      status := "complete" },
    { coqFile := "BGsection2.v: rank_quasi_cent_cycle (Proposition 2.4(g)), diagonal-coordinate form"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimitiveRootMatrixConjugation"
      role := "Use the primitive-root character of ZMod h to identify diagonal-conjugation entry weights with cyclic shifts and compute eigenspace finranks"
      status := "complete" },
    { coqFile := "mathlib support for transporting Proposition 2.4(g) from eigenbasis coordinates"
      leanModule := "Submission.OddOrder.MathlibSupport.EigenspaceIntertwining"
      role := "Restrict an intertwining linear equivalence to corresponding eigenspaces and preserve their finranks"
      status := "complete" },
    { coqFile := "BGsection2.v: eigenbasis matrix transport for rank_quasi_cent_cycle (Proposition 2.4(g))"
      leanModule := "Submission.OddOrder.MathlibSupport.EigenbasisConjugationMatrix"
      role := "Identify inverse conjugation in an eigenbasis with entrywise quotient scaling and transport eigenspace finranks to matrices"
      status := "complete" },
    { coqFile := "BGsection2.v: rank_quasi_cent_cycle (Proposition 2.4(g)), coordinate-free form"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimitiveRootConjugationFinrank"
      role := "Compute inverse-conjugation eigenspace finranks as cyclic autocorrelations by collecting a complete primitive-root eigenspace decomposition into an eigenbasis"
      status := "complete" },
    { coqFile := "BGsection2.v: rank_quasi_cent_cycle (Proposition 2.4(g)), finite-order algebraically closed form"
      leanModule := "Submission.OddOrder.MathlibSupport.FiniteOrderConjugationFinrank"
      role := "Derive the inverse-conjugation cyclic autocorrelation formula directly from the finite-order relation using primitive-root semisimplicity"
      status := "complete" },
    { coqFile := "BGsection2.v: counting core of rank_eigenspaces_free_quasi_homocyclic"
      leanModule := "Submission.OddOrder.MathlibSupport.FiniteTranslateOverlap"
      role := "Double-count finite translate overlaps and derive the all-nonzero subset conclusion from constant all-but-one overlap"
      status := "complete" },
    { coqFile := "BGsection2.v: zero-baseline numerical core of rank_eigenspaces_free_quasi_homocyclic"
      leanModule := "Submission.OddOrder.MathlibSupport.QuasiHomocyclicRanks"
      role := "Convert squared-distance rank energy under cyclic shifts into the all-nonzero rank-one profile and ambient cardinality formula"
      status := "complete" },
    { coqFile := "BGsection2.v: diff_rank_quasi_cent_cycle and its use in Proposition 2.4(j)-(k)"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicRankCorrelation"
      role := "Relate cyclic rank autocorrelation to squared-distance energy and turn a one-rank correlation drop into the quasi-homocyclic profile"
      status := "complete" },
    { coqFile := "BGsection2.v: tight dimension argument in rankEi, rankE0, and rankE inside repr_extraspecial_prime_sdprod_cycle"
      leanModule := "Submission.OddOrder.MathlibSupport.EigenspaceBlockRankDrop"
      role := "Turn equal-rank block inclusions, one disjoint scalar line, independent spanning eigenspaces, and the tight ambient dimension into the exact one-rank conjugation drop"
      status := "complete" },
    { coqFile := "BGsection2.v: primitive-root conjugation specialization of rankEi, rankE0, and rankE"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimitiveRootConjugationBlockRankDrop"
      role := "Specialize the block dimension theorem to primitive-root conjugation eigenspaces and derive the exact nonzero-weight rank drop"
      status := "complete" },
    { coqFile := "BGsection2.v: defB1 scalar identity line inside rankE0"
      leanModule := "Submission.OddOrder.MathlibSupport.EndomorphismScalarLine"
      role := "Place the scalar identity line in the zero-weight conjugation eigenspace and reduce the rank-drop application to block spanning and exclusion of the identity from B0"
      status := "complete" },
    { coqFile := "BGsection2.v: cycle_repr_structure, Wi_yr, and the per-orbit B2 Fourier lines"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicOrbitFourierBasis"
      role := "Construct a primitive-root Fourier eigenbasis from a freely shifted cyclic basis, with nonzero one-dimensional eigenlines and full spanning"
      status := "complete" },
    { coqFile := "BGsection2.v: Bfree, dxB, Wi_yr, and the global B2 Fourier family"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicOrbitFourierFamily"
      role := "Transform globally independent free cyclic orbit vectors into globally independent primitive-root eigenvectors while preserving their total span"
      status := "complete" },
    { coqFile := "BGsection2.v: global Fourier span transfer in defSB"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicOrbitFourierGlobalSpan"
      role := "Identify the total span of the weight-first Fourier family with the original orbit-first family span"
      status := "complete" },
    { coqFile := "BGsection2.v: B1, rankB1, and the grouped-block part of defSB"
      leanModule := "Submission.OddOrder.MathlibSupport.IndependentWeightBlocks"
      role := "Group a globally independent rectangular family by weight, compute every block rank as the orbit count, and preserve the total span"
      status := "complete" },
    { coqFile := "BGsection2.v: assembly of sB1E, rankB1, defSB, rankEi, rankE0, and rankE"
      leanModule := "Submission.OddOrder.MathlibSupport.IndependentConjugationBlockRankDrop"
      role := "Derive the exact primitive-root conjugation rank drop from an independent weighted endomorphism family, scalar identity line, spanning, and the tight dimension equation"
      status := "complete" },
    { coqFile := "BGsection2.v: free conjugation-orbit assembly from B and Bfree through rankE"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicOrbitConjugationRankDrop"
      role := "Fourier-transform independent endomorphism orbits shifted by inverse conjugation and derive the exact primitive-root rank drop from their original span"
      status := "complete" },
    { coqFile := "BGsection2.v: card_clPqH orbit-stabilizer core"
      leanModule := "Submission.OddOrder.MathlibSupport.FreeOrbitCardinality"
      role := "Turn pointwise freeness of a finite group action into a trivial stabilizer and an orbit whose cardinality is the order of the acting group"
      status := "complete" },
    { coqFile := "BGsection2.v: card_clPqH fixed-point-free reduction"
      leanModule := "Submission.OddOrder.MathlibSupport.FixedPointFreeOrbit"
      role := "Deduce full-size nonidentity orbits when each nonidentity acting element fixes only the identity of the target group"
      status := "complete" },
    { coqFile := "BGsection2.v: card_clPqH quotient fixed-point lifting bridge"
      leanModule := "Submission.OddOrder.MathlibSupport.QuotientFixedPointOrbit"
      role := "Convert a representative-level fixed-coset lifting property into singleton quotient fixed sets and full-size nonidentity quotient orbits"
      status := "complete" },
    { coqFile := "BGsection2.v: coprime_quotient_cent special case used by card_clPqH"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeCentralFixedPoint"
      role := "Kill a pointwise-central fixed-coset error by coprime iteration and derive full-size quotient orbits from representative centralizers"
      status := "complete" },
    { coqFile := "BGsection2.v: coPH and element-order coprimality inside card_clPqH"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeCentralQuotientOrbit"
      role := "Descend kernel-complement cardinality coprimality through a quotient subgroup and each acting element order to obtain full-size quotient orbits"
      status := "complete" },
    { coqFile := "BGsection2.v: conjugation action descent to P / Z(P)"
      leanModule := "Submission.OddOrder.MathlibSupport.CharacteristicQuotientAction"
      role := "Descend any automorphism action through a characteristic subgroup, with a direct specialization to the center quotient"
      status := "complete" },
    { coqFile := "BGsection2.v: nPH conjugation action on P and P / Z(P)"
      leanModule := "Submission.OddOrder.MathlibSupport.SubgroupConjugationQuotientAction"
      role := "Construct the action of a subgroup of N(P) on P by ambient conjugation, expose its coercion formula, and descend it to the center quotient"
      status := "complete" },
    { coqFile := "BGappendixAB.v: quotient_cents factor-action support"
      leanModule := "Submission.OddOrder.MathlibSupport.SubgroupConjugationFactor"
      role := "Construct conjugation on E/(M intersect E) and identify its kernel with the commutator bound [H,E] <= M"
      status := "complete" },
    { coqFile := "BGsection2.v: card_clPqH ambient conjugation form"
      leanModule := "Submission.OddOrder.MathlibSupport.SubgroupConjugationOrbit"
      role := "Prove every nonidentity orbit on P / Z(P) has cardinality |H| from kernel-complement coprimality, centralization of Z(P), and fixed-point control in P"
      status := "complete" },
    { coqFile := "BGsection2.v: card_clPqH centralizer form"
      leanModule := "Submission.OddOrder.MathlibSupport.CentralizerConjugationOrbit"
      role := "Derive full-size nonidentity orbits on P / Z(P) directly from H centralizing Z(P) and the internal centralizer equalities C_P(<h>) = Z(P)"
      status := "complete" },
    { coqFile := "BGsection2.v: clPqH orbit-quotient indexing and card_clPqH"
      leanModule := "Submission.OddOrder.MathlibSupport.FixedPointFreeOrbitQuotient"
      role := "Identify the singleton identity orbit-quotient class and prove every other orbit-quotient class has cardinality equal to the acting group"
      status := "complete" },
    { coqFile := "BGsection2.v: clPqH orbit partition cardinality equation"
      leanModule := "Submission.OddOrder.MathlibSupport.FixedPointFreeOrbitCount"
      role := "Sum the identity orbit and uniform nonidentity orbit fibers to prove |X| = 1 + (# nonidentity orbits) * |G|"
      status := "complete" },
    { coqFile := "BGsection2.v: fixed-point-free quotient action underlying card_clPqH"
      leanModule := "Submission.OddOrder.MathlibSupport.CentralizerConjugationFixedPoint"
      role := "Convert the internal centralizer hypotheses into the statement that every nonidentity h in H fixes only the identity coset in P / Z(P)"
      status := "complete" },
    { coqFile := "BGsection2.v: clPqH quotient-action orbit count"
      leanModule := "Submission.OddOrder.MathlibSupport.FixedOneMulActionOrbitCount"
      role := "Count arbitrary multiplicative actions with a fixed identity point and uniform nonidentity orbit fibers"
      status := "complete" },
    { coqFile := "BGsection2.v: card_clPqH center-quotient cardinality equation"
      leanModule := "Submission.OddOrder.MathlibSupport.CentralizerConjugationOrbitCount"
      role := "Assemble the centralizer hypotheses and fixed-one orbit partition into |P / Z(P)| = 1 + (# nonidentity H-orbits) * |H|"
      status := "complete" },
    { coqFile := "BGsection2.v: rank_eigenspaces_quasi_homocyclic (Proposition 2.4(j))"
      leanModule := "Submission.OddOrder.MathlibSupport.GeneralQuasiHomocyclicRanks"
      role := "Show that correlation drops by one under every nonzero cyclic shift force one exceptional rank at distance one and the corresponding total-rank equation"
      status := "complete" },
    { coqFile := "BGsection2.v: finite-order assembly of rank_eigenspaces_quasi_homocyclic (Proposition 2.4(j))"
      leanModule := "Submission.OddOrder.MathlibSupport.FiniteOrderQuasiHomocyclicRanks"
      role := "Combine finite-order primitive-root decomposition, conjugation autocorrelation, rank drops, and total eigenspace finrank into the quasi-homocyclic conclusion"
      status := "complete" },
    { coqFile := "BGsection2.v: rank_eigenspaces_free_quasi_homocyclic (Proposition 2.4(k)), finite-order form"
      leanModule := "Submission.OddOrder.MathlibSupport.FiniteOrderFreeQuasiHomocyclic"
      role := "Specialize the finite-order rank profile at a vanishing eigenvalue-one space to obtain h = finrank V + 1 and rank one at every nontrivial root"
      status := "complete" },
    { coqFile := "BGsection2.v: representation-native applications of rank_eigenspaces_quasi_homocyclic and rank_eigenspaces_free_quasi_homocyclic"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicRepresentationQuasiHomocyclic"
      role := "Apply the finite-order quasi-homocyclic rank theorems directly to a represented element satisfying z^h = 1"
      status := "complete" },
    { coqFile := "BGsection2.v: determinant-one action of G^`(1)"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationDeterminant"
      role := "Turn a representation into a general-linear homomorphism and place its commutator subgroup in the determinant kernel"
      status := "complete" },
    { coqFile := "BGsection2.v: cross-prime centralization in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.MathlibSupport.CrossPrimeCommutatorCentralizer"
      role := "Centralize a normal q-subgroup when the ambient commutator is a p-group for a distinct prime"
      status := "complete" },
    { coqFile := "BGsection2.v: proper-normalizer Burnside branch of der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2NormalizerComplement"
      role := "Turn the normalizer induction output into centralization and a normal Sylow complement via Burnside transfer"
      status := "complete" },
    { coqFile := "BGsection2.v: proper-normalizer contradiction in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2NormalizerExclusion"
      role := "Place the ambient commutator in the transfer kernel and exclude the selected Sylow prime from its order"
      status := "complete" },
    { coqFile := "BGsection2.v: abelQ in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.MathlibSupport.CrossPrimeDerivedAbelian"
      role := "Make a q-group abelian when induction makes its commutator a p-group for a distinct prime"
      status := "complete" },
    { coqFile := "BGsection2.v: pgroupP and wlog_neg prime selection"
      leanModule := "Submission.OddOrder.MathlibSupport.NonPGroupPrimeDivisor"
      role := "Select a prime distinct from p dividing the order of a finite group that is not p-primary"
      status := "complete" },
    { coqFile := "BGappendixAB.v: cross-prime element criterion for p-primary kernels"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupPrimeOrderCriterion"
      role := "Prove a finite group p-primary by ruling out nontrivial elements of prime order q different from p"
      status := "complete" },
    { coqFile := "BGsection2.v: IHm applications in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2SubgroupInduction"
      role := "Restrict the faithful representation to proper subgroups and transport oddness and strict cardinality descent"
      status := "complete" },
    { coqFile := "BGsection2.v: nPG in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2SylowNormalizerTop"
      role := "Rule out a proper Sylow normalizer by combining subgroup induction with the Burnside-transfer exclusion"
      status := "complete" },
    { coqFile := "BGsection2.v: Q := G^`(1) :&: P and abelQ reduction"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowPart"
      role := "Define the derived-Sylow intersection and prove its primary, normal, and conditional commutativity properties"
      status := "complete" },
    { coqFile := "BGsection2.v: nilpotent Sylow obstruction in the proof of abelQ"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupCommutatorProper"
      role := "Show a nontrivial finite p-group cannot equal its commutator via nilpotence and solvability"
      status := "complete" },
    { coqFile := "BGsection2.v: properness argument inside abelQ"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowPartProper"
      role := "Show the derived-Sylow intersection is proper whenever its own commutator is nontrivial"
      status := "complete" },
    { coqFile := "BGsection2.v: completed abelQ in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowPartAbelian"
      role := "Combine strictness with strong induction to prove the derived-Sylow intersection commutative"
      status := "complete" },
    { coqFile := "BGsection2.v: pQ in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowPartDivisibility"
      role := "Use Cauchy and Sylow conjugacy to transfer a commutator prime divisor into the derived-Sylow intersection"
      status := "complete" },
    { coqFile := "BGsection2.v: mxsimple_exists and mxsimple_abelian_linear"
      leanModule := "Submission.OddOrder.MathlibSupport.MaschkeSimpleLine"
      role := "Extract a simple summand by Maschke and prove it is one-dimensional for a finite abelian acting group"
      status := "complete" },
    { coqFile := "BGsection2.v: mx_Maschke, sumUV, and dxUV"
      leanModule := "Submission.OddOrder.MathlibSupport.MaschkeTwoLines"
      role := "Split a two-dimensional finite abelian representation into complementary invariant lines"
      status := "complete" },
    { coqFile := "BGsection2.v: Maschke cross-characteristic premise"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupCardCast"
      role := "Show a finite q-group order is nonzero in characteristic p for distinct primes"
      status := "complete" },
    { coqFile := "BGsection2.v: rQ through dxUV in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowMaschkeLines"
      role := "Specialize the complementary invariant-line decomposition to the abelian derived-Sylow subgroup"
      status := "complete" },
    { coqFile := "BGsection2.v: scalar actions def_ux and def_vx"
      leanModule := "Submission.OddOrder.MathlibSupport.InvariantLineScalar"
      role := "Express each represented group element on a one-dimensional invariant summand as a unique scalar"
      status := "complete" },
    { coqFile := "BGsection2.v: representation-power calculation in ap1"
      leanModule := "Submission.OddOrder.MathlibSupport.InvariantLineScalarPower"
      role := "Transfer an element power relation to the scalar acting on a one-dimensional invariant submodule"
      status := "complete" },
    { coqFile := "BGsection2.v: algebraic and faithful-action core of ne_ab"
      leanModule := "Submission.OddOrder.MathlibSupport.InvariantLineScalarSeparation"
      role := "Separate equal complementary-line scalars using odd exponent, product one, and representation faithfulness"
      status := "complete" },
    { coqFile := "BGsection2.v: nx_uv in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.MathlibSupport.DistinctEigenlines"
      role := "Classify eigenvectors and invariant finrank-one subspaces for two distinct complementary eigenvalues"
      status := "complete" },
    { coqFile := "BGsection2.v: normality transport used by nAx"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalInvariantSubspaceTranslate"
      role := "Preserve finrank and subgroup invariance when translating an invariant subspace under a normal subgroup"
      status := "complete" },
    { coqFile := "BGsection2.v: ambient representation action used by redG"
      leanModule := "Submission.OddOrder.MathlibSupport.SubgroupModuleAmbientAction"
      role := "Package ambient represented elements as a linear-equivalence action on a subgroup-restriction module"
      status := "complete" },
    { coqFile := "BGsection2.v: nAx in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowTranslatedLine"
      role := "Classify every ambient translate of a one-dimensional derived-Sylow invariant subspace into the two eigenlines"
      status := "complete" },
    { coqFile := "BGsection2.v: odd-order no-swap core of redG"
      leanModule := "Submission.OddOrder.MathlibSupport.OddTwoLineAction"
      role := "Show an odd-cardinality group action fixing an unordered pair of complementary lines fixes each line"
      status := "complete" },
    { coqFile := "BGsection2.v: redG in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowAmbientLineFixing"
      role := "Use translated-line classification and odd order to prove every ambient element fixes both eigenlines"
      status := "complete" },
    { coqFile := "BGsection2.v: diagonal-image commutativity after redG"
      leanModule := "Submission.OddOrder.MathlibSupport.ComplementaryLineCommuting"
      role := "Show endomorphisms preserving the same complementary one-dimensional decomposition commute"
      status := "complete" },
    { coqFile := "BGsection2.v: abelian ambient image after redG"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowAmbientAbelian"
      role := "Reflect simultaneous diagonal commutativity through a faithful representation and trivialize the ambient commutator"
      status := "complete" },
    { coqFile := "BGsection2.v: strong-induction contradiction in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2AlgebraicallyClosedStep"
      role := "Assemble Sylow transfer, derived-Sylow line analysis, and faithful diagonalization into the algebraically closed induction step"
      status := "complete" },
    { coqFile := "BGsection2.v: cardinal induction in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2AlgebraicallyClosed"
      role := "Close strong cardinal induction and prove the characteristic-primary commutator theorem over algebraically closed fields"
      status := "complete" },
    { coqFile := "BGsection2.v: group_closure_field reduction"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationBaseChange"
      role := "Extend representations faithfully to an algebraic closure while preserving finite dimension and characteristic"
      status := "complete" },
    { coqFile := "BGsection2.v: der1_odd_GL2_charf in positive characteristic"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2PrimeCharacteristic"
      role := "Apply faithful scalar extension to prove the characteristic-primary commutator theorem over any field of prime characteristic"
      status := "complete" },
    { coqFile := "BGsection2.v: der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2Characteristic"
      role := "Package the result in mathlib's IsPGroup API, whose p = 0 case is tautological"
      status := "complete" },
    { coqFile := "BGsection2.v: characteristic-zero induction step in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2CharZeroAlgebraicallyClosedStep"
      role := "Use auxiliary prime two and the derived-Sylow line argument to trivialize the commutator in characteristic zero"
      status := "complete" },
    { coqFile := "BGsection2.v: characteristic-zero cardinal induction in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2CharZeroAlgebraicallyClosed"
      role := "Close cardinal induction and prove the commutator trivial over algebraically closed characteristic-zero fields"
      status := "complete" },
    { coqFile := "BGsection2.v: exact characteristic-zero form of der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2CharZero"
      role := "Extend scalars and prove the exact commutator-trivial and abelian conclusions over arbitrary characteristic-zero fields"
      status := "complete" },
    { coqFile := "BGsection2.v: pnat_1 step in charf'_GL2_abelian"
      leanModule := "Submission.OddOrder.MathlibSupport.PSubgroupAbsentPrime"
      role := "Trivialize a finite p-subgroup when p does not divide the ambient group order"
      status := "complete" },
    { coqFile := "BGsection2.v: charf'_GL2_abelian (Theorem 2.6(a))"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2CrossCharacteristicAbelian"
      role := "Combine the primary commutator theorem with absent characteristic divisibility to prove the represented odd group abelian"
      status := "complete" },
    { coqFile := "BGsection2.v: pG' and Sylow_superset in Theorem 2.6(b)"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2DerivedSylowContainment"
      role := "Place the characteristic-primary ambient commutator inside a Sylow subgroup"
      status := "complete" },
    { coqFile := "BGsection2.v: rfix_pgroup_char in Theorem 2.6(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupInvariantVector"
      role := "Produce a nonzero common fixed vector for a finite p-group in characteristic p"
      status := "complete" },
    { coqFile := "BGsection2.v: rfix_pgroup_char quotient step in Theorem 2.6(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupInvariantQuotient"
      role := "Trivialize the quotient by common fixed vectors in dimension at most two"
      status := "complete" },
    { coqFile := "BGsection2.v: abelian p-subgroup step in Theorem 2.6(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupRepresentationAbelian"
      role := "Show a faithfully represented finite p-group in characteristic p and dimension at most two is abelian"
      status := "complete" },
    { coqFile := "BGsection2.v: charf_GL2_der_subS_abelian_Sylow (Theorem 2.6(b))"
      leanModule := "Submission.OddOrder.BG.Section02.OddGL2DerivedSylowAbelian"
      role := "Place the ambient commutator in an abelian Sylow subgroup in defining characteristic"
      status := "complete" },
    { coqFile := "BGsection2.v: determinant calculation from sumUV and dxUV"
      leanModule := "Submission.OddOrder.MathlibSupport.ComplementaryLineDeterminant"
      role := "Compute the determinant as the product of scalar actions on complementary invariant lines"
      status := "complete" },
    { coqFile := "BGsection2.v: sumUV identity-action consequence"
      leanModule := "Submission.OddOrder.MathlibSupport.ComplementarySubspaceIdentity"
      role := "Show an endomorphism is the identity when it is the identity on complementary invariant subspaces"
      status := "complete" },
    { coqFile := "BGsection2.v: representation form of the block determinant calculation"
      leanModule := "Submission.OddOrder.MathlibSupport.RepresentationLineDeterminant"
      role := "Bridge monoid-algebra invariant lines to the determinant of the original represented element"
      status := "complete" },
    { coqFile := "BGsection2.v: ab1 in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowLineDeterminant"
      role := "Use derived-subgroup determinant one to prove that the two invariant-line scalars multiply to one"
      status := "complete" },
    { coqFile := "BGsection2.v: ap1 and its second-line analogue"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowLinePowers"
      role := "Specialize element power relations to both complementary derived-Sylow line scalars"
      status := "complete" },
    { coqFile := "BGsection2.v: ne_ab in der1_odd_GL2_charf"
      leanModule := "Submission.OddOrder.BG.Section02.DerivedSylowLineSeparation"
      role := "Combine restricted faithfulness, determinant one, and odd exponent to separate the two line scalars"
      status := "complete" },
    { coqFile := "BGappendixAB.v: def_dA = 1 branch"
      leanModule := "Submission.OddOrder.BG.AppendixAB.SchurOneDimensionalBranch"
      role := "Use faithful rank-one commutation to make the local group abelian and its commutator a p-group"
      status := "complete" },
    { coqFile := "BGappendixAB.v: commutative generator branch support"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PairGeneratedCommutative"
      role := "Show a group generated by a commuting pair is commutative"
      status := "complete" },
    { coqFile := "BGappendixAB.v: commuting representation branch"
      leanModule := "Submission.OddOrder.BG.AppendixAB.CommutingRepresentationBranch"
      role := "Use faithfulness to make the local group abelian and its commutator a p-group"
      status := "complete" },
    { coqFile := "BGsection1.v: sol_chief_abelem"
      leanModule := "Submission.OddOrder.MathlibSupport.ChiefFactor"
      role := "Quotient-oriented chief factors and solvable elementary-abelian factors"
      status := "complete" },
    { coqFile := "mathcomp mingroup_exists and chief_series_exists selection support"
      leanModule := "Submission.OddOrder.MathlibSupport.MinimalNormalExistence"
      role := "Minimal normal subgroup existence and chief-factor selection in finite groups"
      status := "complete" },
    { coqFile := "BGsection1.v: Fitting support through Fitting_eq_pcore"
      leanModule := "Submission.OddOrder.MathlibSupport.Fitting"
      role := "Characteristic prime-core supremum, normal nilpotent containment, and p-core collapse"
      status := "complete" },
    { coqFile := "mathcomp Fitting_nil"
      leanModule := "Submission.OddOrder.MathlibSupport.FittingNilpotent"
      role := "Internal direct-product proof that the finite Fitting core is nilpotent"
      status := "complete" },
    { coqFile := "BGsection1.v: cent_sub_Fitting"
      leanModule := "Submission.OddOrder.MathlibSupport.FittingSelfCentralizing"
      role := "The Fitting core of a finite solvable group contains its centralizer"
      status := "complete" },
    { coqFile := "BGsection1.v: Fitting_eq_pcore plus cent_sub_Fitting"
      leanModule := "Submission.OddOrder.MathlibSupport.FittingPCore"
      role := "Self-centralizing p-core and p-group centralizer when the p-prime core is trivial"
      status := "complete" },
    { coqFile := "BGappendixAB.v: SCN_P fixed-point support"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupCenter"
      role := "Nontrivial normal subgroups of finite p-groups meet the center"
      status := "complete" },
    { coqFile := "BGsection1.v: coprime_nil_faithful_cent_stab, normalizer-condition half"
      leanModule := "Submission.OddOrder.MathlibSupport.NilpotentCentralizer"
      role := "Internal fixed-point centralizer and nilpotent normalizer-condition argument"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki p-group normalizer condition"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupNormalizer"
      role := "Strict normalizer growth internally and in ambient subgroup-intersection form"
      status := "complete" },
    { coqFile := "BGsection1.v: stable_factor_cent"
      leanModule := "Submission.OddOrder.MathlibSupport.StableFactor"
      role := "Pointwise stable-factor coprime action, stronger than the solvable source statement"
      status := "complete" },
    { coqFile := "BGsection1.v: coprime_nil_faithful_cent_stab"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeNilpotentCentralizer"
      role := "Full nilpotent faithful coprime-action centralizer theorem"
      status := "complete" },
    { coqFile := "BGappendixAB.v: A.5.2 centralizer p-group argument"
      leanModule := "Submission.OddOrder.MathlibSupport.ConstrainedCentralizer"
      role := "Ambient centralizer is a p-group under the p-core fixed-point constraint"
      status := "complete" },
    { coqFile := "BGappendixAB.v: max_SCN and SCN_P"
      leanModule := "Submission.OddOrder.MathlibSupport.SelfCentralizing"
      role := "Existence of self-centralizing normal abelian subgroups in finite p-groups"
      status := "complete" },
    { coqFile := "mathcomp pcore support"
      leanModule := "Submission.OddOrder.MathlibSupport.PCore"
      role := "Largest normal p-subgroup, characteristicity, and Sylow containment"
      status := "complete" },
    { coqFile := "mathcomp pcore quotient support"
      leanModule := "Submission.OddOrder.MathlibSupport.PCoreFunctorial"
      role := "Surjective p-core functoriality for p-group kernels"
      status := "complete" },
    { coqFile := "mathcomp p'-core support"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimeCore"
      role := "Greatest normal p-coprime subgroup, characteristicity, and p-core disjointness"
      status := "complete" },
    { coqFile := "mathcomp pseries: O_{p',p}"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimePCore"
      role := "Two-step p-prime, p core with quotient image and collapse properties"
      status := "complete" },
    { coqFile := "BGsection1.v: quotient pseries Sylow image"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimePCoreSylow"
      role := "Canonical core quotient and surjectivity of two-step-core Sylow images"
      status := "complete" },
    { coqFile := "BGsection1.v: quotient by O_{p',p}"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimePCoreQuotient"
      role := "Trivial p-core after quotienting by the two-step p-prime, p core"
      status := "complete" },
    { coqFile := "mathcomp trivg_pcore_quotient"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient"
      role := "Trivial p-prime core after quotienting by the p-prime core"
      status := "complete" },
    { coqFile := "BGsection1.v: p_elt_gen"
      leanModule := "Submission.OddOrder.MathlibSupport.PElement"
      role := "p-elements, generated subgroup, characteristicity, and functoriality"
      status := "complete" },
    { coqFile := "BGsection1.v: p_constrained and trivial p'-core case"
      leanModule := "Submission.OddOrder.BG.Section01.Constrained"
      role := "Ambient Sylow embedding, p-constrained predicate, and Fitting reduction"
      status := "complete" },
    { coqFile := "BGsection1.v: solvable_p_constrained"
      leanModule := "Submission.OddOrder.BG.Section01.ConstrainedSolvable"
      role := "Quotient reduction proving finite solvable groups are p-constrained"
      status := "complete" },
    { coqFile := "BGsection1.v: p_stable_abelian_constrained"
      leanModule := "Submission.OddOrder.BG.Section01.AbelianConstrained"
      role := "Gorenstein 8.1.3: p-stable constrained groups are p-abelian-constrained"
      status := "complete" },
    { coqFile := "BGsection6.v: odd_p_abelian_constrained handoff"
      leanModule := "Submission.OddOrder.BG.Section01.AbelianConstrainedSolvable"
      role := "Solvable p-stable groups are p-abelian-constrained; odd p-stability remains the sole input"
      mappedDeclarations := ["solvable_isPAbelianConstrained_of_isPStable"]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section01.AbelianConstrained",
          "Submission.OddOrder.BG.Section01.ConstrainedSolvable" ]
      status := "complete" },
    { coqFile := "BGsection1.v: generated_by through Puig1"
      leanModule := "Submission.OddOrder.BG.Section01.Puig"
      role := "normalized abelian generators and elementary Puig-series properties"
      status := "complete" },
    { coqFile := "BGsection1.v: Puig_at_cont through Puig_cont"
      leanModule := "Submission.OddOrder.BG.Section01.PuigFunctorial"
      role := "homomorphic inclusions and equivalence invariance for the Puig series"
      status := "complete" },
    { coqFile := "BGsection1.v: p_stable"
      leanModule := "Submission.OddOrder.BG.Section01.PStability"
      role := "Normalizer-centralizer quotient model and the Bender-Glauberman p-stability predicate"
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_p_stable local p_xp predicate"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticElement"
      role := "Quadratic p-elements and the bridge from vanishing double commutators"
      status := "complete" },
    { coqFile := "BGappendixAB.v: p_xp conjugation transport"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticConjugation"
      role := "Invariance of quadratic p-elements under the normalizer of the acted-on subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: quotient transport of the local quadratic-pair hypotheses"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticPairFunctorial"
      role := "Transport quadratic elements, normalizer membership, generated-pair oddness, and p-primary acted-on subgroups through group homomorphisms"
      status := "complete" },
    { coqFile := "BGappendixAB.v: strict quotient descent in the odd_p_stable induction"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticPairNormalQuotient"
      role := "Transport the full quadratic-pair hypothesis through a normal quotient and prove strict cardinality descent for a nontrivial kernel inside E"
      status := "complete" },
    { coqFile := "BGappendixAB.v: quotient induction inside E <*> <<x,y>>"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticPairInvariantQuotient"
      role := "Form the invariant ambient extension E join pairGenerated x y, quotient by a subgroup normal there, transport the local hypotheses, and retain strict descent against E"
      status := "complete" },
    { coqFile := "BGappendixAB.v: faithful normalizer-centralizer quotient action"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalizerQuotientConjugation"
      role := "Embed the normalizer-centralizer quotient faithfully into automorphisms of the acted-on subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: cross-prime subgroup action"
      leanModule := "Submission.OddOrder.MathlibSupport.CrossPrimeHomKernel"
      role := "Show every homomorphism from a q-group to a p-group is trivial when p and q are distinct"
      status := "complete" },
    { coqFile := "BGappendixAB.v: cross-prime local quotient centralization"
      leanModule := "Submission.OddOrder.BG.AppendixAB.LocalQuotientPairCrossPrime"
      role := "Turn p-primary local quotient actions into centralization by q-subgroups of the acting pair"
      status := "complete" },
    { coqFile := "BGappendixAB.v: quotient branch of the odd_p_stable induction"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticPairInductionStep"
      role := "Use strict quotient induction to force a cross-prime commutator subgroup into each nontrivial invariant factor"
      status := "complete" },
    { coqFile := "BGappendixAB.v: minnormal E (E <*> G)"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticPairMinimality"
      role := "Combine subgroup and quotient induction with stable-factor centralization to force minimal normality"
      status := "complete" },
    { coqFile := "BGappendixAB.v: strong induction closing the local p_xp predicate"
      leanModule := "Submission.OddOrder.BG.AppendixAB.QuadraticPairLocalPrinciple"
      role := "Lift cross-prime witnesses, invoke the irreducible minimal-normal branch, and prove the local quotient pair is p-primary"
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_p_stable"
      leanModule := "Submission.OddOrder.BG.AppendixAB.OddPStable"
      role := "Discharge the quadratic-pair premise and conclude p-stability for every finite odd-order group by Baer-Suzuki"
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_p_stable Baer_Suzuki wrapper"
      leanModule := "Submission.OddOrder.BG.AppendixAB.OddPStableBaerSuzuki"
      role := "Reduce odd-order p-stability to the local two-generator quadratic-pair principle"
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_p_stable derived-subgroup reduction"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PGroupDerivedReduction"
      role := "Recover a two-generated p-group from p-element generators and a p-group commutator subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_p_stable local derived principle"
      leanModule := "Submission.OddOrder.BG.AppendixAB.OddPStableDerivedReduction"
      role := "Reduce the local quadratic-pair conclusion to a p-group statement for its commutator subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_p_stable two-generator setup"
      leanModule := "Submission.OddOrder.BG.AppendixAB.TwoGenerator"
      role := "Two-generator subgroups, normalizer containment, p-group inheritance, and oddness"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki endpoint"
      leanModule := "Submission.OddOrder.MathlibSupport.ConjugacyGenerated"
      role := "Least normal subgroup generated by one element and reduction to membership in the p-core"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki conjugacy class E"
      leanModule := "Submission.OddOrder.MathlibSupport.ConjugacyClassGenerated"
      role := "Identify the subgroup generated by the conjugacy class with the normal closure of one element"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki initial Sylow selection"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiSylow"
      role := "Pairwise conjugacy-class p-group predicate and a Sylow subgroup containing the distinguished element"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki conjugate-pair reduction"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiPairs"
      role := "Equivalence of the one-sided conjugate-pair and arbitrary conjugacy-class pair p-group hypotheses"
      status := "complete" },
    { coqFile := "mathcomp support: two-generator subgroup restriction"
      leanModule := "Submission.OddOrder.MathlibSupport.PairGeneratedSubtype"
      role := "Identify two-generator subgroups after restriction to a subgroup and transport p-group structure"
      status := "complete" },
    { coqFile := "mathcomp support: proper-subgroup cardinal descent"
      leanModule := "Submission.OddOrder.MathlibSupport.SubgroupCardinality"
      role := "Strict Nat.card descent to a proper subgroup, including set normalizers"
      status := "complete" },
    { coqFile := "mathcomp support: cyclic subgroup of a p-element"
      leanModule := "Submission.OddOrder.MathlibSupport.PElementCyclic"
      role := "Turn the power condition on a p-element into a p-group structure on its cyclic subgroup"
      status := "complete" },
    { coqFile := "mathcomp support: finite p-group extension"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupExtension"
      role := "Recover a finite p-group from a normal p-subgroup and p-group quotient"
      status := "complete" },
    { coqFile := "BGappendixAB.v: lift p-primary structure through an action kernel"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupMapKernel"
      role := "Recover p-group structure on a subgroup from its image and the kernel of the restricted homomorphism"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Sylow_Jsub support"
      leanModule := "Submission.OddOrder.MathlibSupport.SylowConjugateEmbedding"
      role := "Conjugate an ambient p-subgroup into a selected Sylow subgroup of a containing subgroup"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki induction hypothesis restriction"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiSubgroupPairs"
      role := "Inherit the ambient conjugacy-pair p-group hypothesis inside a containing subgroup"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki branch E subset P"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiNormalCase"
      role := "Close the induction when the conjugacy class is contained in the selected Sylow subgroup"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki maximal set D"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiMaximal"
      role := "Subgroup-shaped maximal candidate selection for the hard Baer-Suzuki branch"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki faithful maximal set D"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiSetCandidate"
      role := "Set-of-conjugates candidate predicate and maximal selection above the singleton x"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki maxset above singleton x"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiMaximalContaining"
      role := "Strengthen maximal-candidate selection so the distinguished element remains in D"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki defD"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiCandidateClosure"
      role := "Maximality identity D = P intersect generated witness p-group intersect conjugacy closure"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki faithful defD"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiSetCandidateClosure"
      role := "Maximality identity D = P intersect generated witness p-group intersect the actual conjugacy class"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki proper D"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiCandidateProper"
      role := "Use Sylow maximality to prove every hard-branch candidate is proper in the selected Sylow subgroup"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki nDD"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiNormalizerGrowth"
      role := "Produce a selected-Sylow element normalizing a candidate while lying strictly outside it"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki faithful nDD"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiSetNormalizer"
      role := "Show every element of the maximal candidate set normalizes that set"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki case nDG"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiGlobalNormalizer"
      role := "Close the branch in which the whole ambient group normalizes the candidate D"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki faithful case nDG"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiSetGlobalNormalizer"
      role := "Close the globally normalized branch using the normal p-subgroup generated by the set candidate"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki pN"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiNormalizerGenerated"
      role := "Upgrade recursive p-core membership of normalizing conjugates to a generated p-subgroup"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki IH on N_G(D)"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiNormalizerInduction"
      role := "Apply cardinal induction inside the proper set normalizer and establish pN"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki exists y1"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiFirstNormalizerWitness"
      role := "Use p-group normalizer growth to obtain a normalizing conjugate outside the selected Sylow subgroup"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki exists y2"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiSecondNormalizerWitness"
      role := "Use Sylow conjugacy or normalizer growth to obtain a normalizing conjugate in P but outside D"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki final maxD contradiction"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzukiMaximalContradiction"
      role := "Adjoin y2, retain y1 as witness, and contradict maximality of D"
      status := "complete" },
    { coqFile := "mathcomp solvable/sylow.v: Baer_Suzuki"
      leanModule := "Submission.OddOrder.MathlibSupport.BaerSuzuki"
      role := "Complete finite-group Baer-Suzuki theorem by strong cardinality induction"
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_abelian_gen_stable"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PStableGenerated"
      role := "A.5.1 generated-subgroup consequence of p-stability and ambient quotient transport"
      mappedDeclarations := ["abelianGenerated_quotient_le_pCore_of_isPStable"]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section01.PStability",
          "Submission.OddOrder.BG.Section01.Puig" ]
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_abelian_gen_constrained, quotient-lifting half"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PStableLift"
      role := "Lift A.5.1 through a p-group centralizer and expose the remaining coprime-action input"
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_abelian_gen_constrained from p-stability"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PStableConstrained"
      role := "Full A.5.2 constrained-generator theorem conditional only on p-stability"
      mappedDeclarations := ["abelianGeneratedConstrained_of_isPStable"]
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixAB.PStableLift",
          "Submission.OddOrder.MathlibSupport.ConstrainedCentralizer" ]
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd_abelian_gen_constrained at P = O_p(G)"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PStablePCore"
      role := "Unconditional p-core specialization of the A.5.2 lift from p-stability"
      mappedDeclarations := ["abelianGenerated_pCore_le_pCore_of_isPStable"]
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixAB.PStableLift",
          "Submission.OddOrder.MathlibSupport.FittingPCore" ]
      status := "complete" },
    { coqFile := "BGappendixAB.v: Puig_succS through Puig_inf_sub_Puig"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigOrder"
      role := "alternating Puig-chain order and the inclusion Puig_inf <= Puig"
      status := "complete" },
    { coqFile := "BGappendixAB.v: Puig_limit and Puig_inf_def"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigLimit"
      role := "finite stabilization and the second terminal Puig recurrence"
      status := "complete" },
    { coqFile := "BGappendixAB.v: Puig_char and abelian_norm_Puig"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigStructural"
      role := "characteristic Puig terms and normal-abelian inclusion"
      status := "complete" },
    { coqFile := "BGappendixAB.v: center_Puig_char through trivg_center_Puig_pgroup"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigCentralizer"
      role := "characteristic Puig center, all six B.1(f) inclusions, and the trivial-center consequence"
      status := "complete" },
    { coqFile := "BGappendixAB.v: sub_Puig_eq"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigRestriction"
      role := "B.2 restriction stability for subgroups containing the terminal Puig subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: norm_abgen_pgroup"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigPGroup"
      role := "Upgrade normalized abelian generators of a p-group to p-subgroups"
      status := "complete" },
    { coqFile := "BGappendixAB.v: pcore_Sylow_Puig_sub"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigPCore"
      role := "B.3 alternating Puig comparison between a Sylow subgroup and the p-core"
      status := "complete" },
    { coqFile := "BGappendixAB.v: pcore_Sylow_Puig_sub from p-stability"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PStablePuigPCore"
      role := "B.3 Puig comparison conditional only on the Appendix A p-stability theorem"
      mappedDeclarations := ["pCore_sylow_puig_sub_of_isPStable"]
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixAB.PStableConstrained",
          "Submission.OddOrder.BG.AppendixAB.PuigPCore" ]
      status := "complete" },
    { coqFile := "BGappendixAB.v: odd-order specializations after odd_p_stable"
      leanModule := "Submission.OddOrder.BG.AppendixAB.OddPStableConsequences"
      role := "Discharge p-stability assumptions in A.5, p-abelian constraint, and B.3 for finite odd-order groups"
      status := "complete" },
    { coqFile := "BGappendixAB.v: Puig_center_normal (Theorem B.4(b))"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigCenterNormal"
      role := "Prove normality in G of the center of the Puig subgroup of a Sylow p-subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: injective restriction functoriality used by Puig_factorization"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigInjectiveFunctorial"
      role := "Commute Puig subgroups and their centers with homomorphisms injective on the source subgroup"
      status := "complete" },
    { coqFile := "BGappendixAB.v: Puig_factorization (Theorem B.4(a))"
      leanModule := "Submission.OddOrder.BG.AppendixAB.PuigFactorization"
      role := "Factor G as its p-prime core together with the normalizer of the center of the Sylow Puig subgroup"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius decomposition context and Lemma 3.1"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusBasic"
      role := "Internal kernel-complement decomposition, fixed-point-free action, orbit sizes, and coprime orders"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius normalizer and partition support"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusNormalizer"
      role := "Unique coordinates, self-normalizing and malnormal complement, complement centralizer control, and trivial ambient center"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius_partition"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusPartition"
      role := "Surjective kernel commutator maps and covering by kernel-conjugates of the complement"
      status := "complete" },
    { coqFile := "BGsection3.v: algebraic part of Frobenius_proper_quotient"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusQuotientComplement"
      role := "Injective complement image and complementary nontrivial normal kernel/complement images in proper kernel quotients"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius_proper_quotient, centralized-kernel case"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusCentralQuotient"
      role := "Coprime fixed-coset lifting and the full Frobenius quotient theorem when the complement centralizes the quotient kernel"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius_proper_quotient"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusQuotient"
      role := "Full proper-kernel quotient theorem using surjective fixed-point-free commutator maps"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius_normal_proper_ker and Frobenius_quotient"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusNormalSubgroup"
      role := "Normal-subgroup kernel dichotomy and quotient theorem in the source hypothesis form"
      status := "complete" },
    { coqFile := "BGsection3.v: finite partition identity used by Frobenius_rfix_compl"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusPartitionSum"
      role := "Unique complement-conjugate partition, explicit finite equivalence, and additive norm identity"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius_rfix_compl (Lemma 3.3)"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusRepresentation"
      role := "Nontrivial kernel action forces a nonzero complement-fixed space in coprime characteristic"
      status := "complete" },
    { coqFile := "BGsection3.v: semiregular action and prime_FrobeniusP support"
      leanModule := "Submission.OddOrder.BG.Section03.PrimeProductFrobenius"
      role := "Turn semiregular normalized pairs into Frobenius decompositions and identify the noncentral p*q Sylow action"
      status := "complete" },
    { coqFile := "BGsection3.v: regular_pq_group_cyclic representation branch"
      leanModule := "Submission.OddOrder.BG.Section03.PrimeProductRepresentation"
      role := "Use Lemma 3.3 to force centralization or a trivial normal-Sylow action"
      status := "complete" },
    { coqFile := "BGsection3.v: regular_pq_group_cyclic elementary-abelian case"
      leanModule := "Submission.OddOrder.BG.Section03.PrimeProductCyclic"
      role := "Prove centralization in the elementary-abelian reduction and derive cyclicity from commuting Sylow generators"
      status := "complete" },
    { coqFile := "mathcomp hall.v: specialized solvable coprime Sylow input"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusInvariantSylow"
      role := "Use Frobenius malnormality, prime-product complement conjugacy, Frattini, and Schur-Zassenhaus to select an invariant Sylow subgroup of the kernel"
      status := "complete" },
    { coqFile := "BGsection3.v: regular_pq_group_cyclic"
      leanModule := "Submission.OddOrder.BG.Section03.RegularPrimeProduct"
      role := "Reduce through an invariant minimal elementary-abelian subgroup and prove the full regular prime-product group is cyclic"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius_rfix_compl contrapositive in Theorem 3.4"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusZeroInvariants"
      role := "Turn a zero complement-fixed space into a Frobenius-kernel and mixed-commutator kernel bound"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, ker_ltK"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectProperKernel"
      role := "Transport all hypotheses to a smaller generated semidirect product and invoke strong cardinality induction"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, quotient centralizer combination"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectKernelGenerators"
      role := "Combine two proper invariant kernel factors modulo the representation kernel"
      status := "complete" },
    { coqFile := "mathcomp hall.v: prime-order coprime invariant Sylow selection"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow"
      role := "Select a Sylow subgroup fixed by a coprime prime-order action and transport it to the ambient normalizer"
      status := "complete" },
    { coqFile := "mathcomp Sylow transport used in BGsection15.v"
      leanModule := "Submission.OddOrder.MathlibSupport.AmbientSylowTransport"
      role := "Extend and restrict ambiently represented Sylow subgroups across an intermediate subgroup"
      mappedDeclarations :=
        [ "IsSylowSubgroupOf.extend_of_not_dvd_index",
          "IsSylowSubgroupOf.restrict_of_le" ]
      notes :=
        [ "The owned-file exact check and the batched root targeted build both pass without diagnostics; root integration review confirms the two public transport statements and sole direct import" ]
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow" ]
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, q/q'-Hall reduction"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectHallReduction"
      role := "Supply the invariant Sylow factor and close Theorem 3.4 once the normalized solvable q'-Hall partner is available"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, solvable Hall partner"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectHallPartner"
      role := "Construct the normalized proper q'-Hall partner and discharge the non-q-group kernel branch"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, without loss q.-group K"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectPGroupReduction"
      role := "Choose a prime divisor of the kernel order and reduce Theorem 3.4 to the prime-power kernel case"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, without loss [K,R] = K"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectPerfectKernelReduction"
      role := "Use coprime commutator idempotence and proper-kernel induction to reduce to a perfect complement action"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, combined structural reduction"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectStructuralReduction"
      role := "Combine the Hall and commutator branches into the prime-power perfect-action case"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, mxsemisimple constituent selection"
      leanModule := "Submission.OddOrder.MathlibSupport.MaschkeNormalConstituent"
      role := "Select a simple Maschke constituent that detects a nontrivially acting normal subgroup"
      status := "complete" },
    { coqFile := "mathcomp hall.v: sub_normal_Hall, prime-complement specialization"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalPrimeComplement"
      role := "Place a normal subgroup disjoint from the prime-order complement inside the normal Hall factor"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, faithful quotient branch"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectFaithfulReduction"
      role := "Factor a selected constituent through its kernel and use quotient cardinality induction to force faithfulness"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0, full faithful irreducible reduction"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectIrreducibleReduction"
      role := "Combine Hall, perfect-action, constituent, and quotient branches into the finite faithful irreducible prime-power-kernel case"
      status := "complete" },
    { coqFile := "mathcomp mxrepresentation.v: mx_faithful_irr_center_cyclic"
      leanModule := "Submission.OddOrder.MathlibSupport.FaithfulIrreducibleCenter"
      role := "Embed the center through the faithful Schur character into the finite Schur field and prove it cyclic"
      status := "complete" },
    { coqFile := "BGsection3.v: characteristic-subgroup step before abelian_charsimple_special"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectCharacteristic"
      role := "Show every proper characteristic kernel subgroup centralizes the complement under a faithful representation"
      status := "complete" },
    { coqFile := "BGsection3.v: abelian and nonabelian faithful branches"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectNonabelianReduction"
      role := "Eliminate the abelian perfect-action case and reduce the faithful branch to a nonabelian prime-power kernel"
      status := "complete" },
    { coqFile := "BGsection3.v: abelian_charsimple_special"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectSpecialKernel"
      role := "Derive special and then extraspecial structure from the characteristic-subgroup centralizer theorem"
      status := "complete" },
    { coqFile := "BGsection2.v: independent cyclic center-quotient orbit representatives"
      leanModule := "Submission.OddOrder.MathlibSupport.FixedPointFreeCyclicOrbitRepresentatives"
      role := "Enumerate all nonidentity points of a fixed-point-free cyclic action without collisions"
      status := "complete" },
    { coqFile := "BGsection2.v: extraspecial quotient operator basis"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientEndomorphismBasis"
      role := "Prove that represented center-quotient elements form a basis of the endomorphism algebra"
      status := "complete" },
    { coqFile := "BGsection2.v: faithful extraspecial irreducible degree"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleDegreeNonmodular"
      role := "Identify the degree square with the order of the extraspecial center quotient in nonmodular characteristic"
      status := "complete" },
    { coqFile := "BGsection2.v: extraspecial conjugation rigidity"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleRigidityNonmodular"
      role := "Recover equivalence of faithful irreducibles from their common central scalar character"
      status := "complete" },
    { coqFile := "BGsection2.v: extraspecial normal restriction"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialNormalRestrictionNonmodular"
      role := "Prove irreducibility on a normal extraspecial subgroup with cyclic quotient"
      status := "complete" },
    { coqFile := "BGsection2.v: repr_clP over an algebraically closed field"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialCyclicFixedVector"
      role := "Combine the extraspecial endomorphism basis and cyclic Fourier rank drop to force a complement-fixed vector"
      status := "complete" },
    { coqFile := "BGsection2.v: repr_clP in arbitrary nonmodular characteristic"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialCyclicFixedVectorNonmodular"
      role := "Descend the extraspecial fixed-vector theorem through algebraic closure and irreducible constituents"
      status := "complete" },
    { coqFile := "BGsection3.v: final extraspecial branch of odd_prime_sdprod_rfix0"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectExtraspecial"
      role := "Discharge the final faithful extraspecial callback using the Section 2 fixed-vector theorem"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_rfix0 (Theorem 3.4)"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeSemidirectTheorem"
      role := "Close all subgroup and quotient recursion by strong induction on the ambient group order"
      status := "complete" },
    { coqFile := "BGsection3.v: odd_prime_sdprod_abelem_cent1"
      leanModule := "Submission.OddOrder.BG.Section03.OddPrimeElementaryAbelianCentralizer"
      role := "Apply Theorem 3.4 to an odd solvable prime-complement action and force the mixed commutator to centralize a coprime fixed-point-free elementary-abelian module"
      mappedDeclarations := ["odd_prime_sdprod_abelem_cent1"]
      notes :=
        [ "The owned-file exact check passes without output; the root targeted build completes across 8746 jobs, and root integration review confirms the source-facing statement, representation construction, invariant-space reduction, and ambient commutator transport" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.OddPrimeSemidirectTheorem",
          "Submission.OddOrder.MathlibSupport.Centralizer",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelian",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation",
          "Submission.OddOrder.MathlibSupport.RepresentationSubgroupRestriction",
          "Submission.OddOrder.MathlibSupport.SubgroupCardinality" ]
      status := "complete" },
    { coqFile := "BGsection3.v: semiprime and odd_sdprod_primact_commg_sub_Fitting (Theorem 3.8)"
      leanModule := "Submission.OddOrder.BG.Section03.PrimeActionCommutatorFitting"
      role := "Reduce a semiprime coprime action through K/F(K), prime-order actors, and both chief-factor characteristics to place the mixed commutator in F(K)"
      mappedDeclarations :=
        [ "IsSemiprimeAction",
          "odd_sdprod_primact_commg_sub_Fitting",
          "odd_sdprod_primact_commg_sub_Fitting_of_internal" ]
      notes :=
        [ "The Coq theorem is exposed under its original name; the top-agent-approved `_of_internal` wrapper is an additional declaration that unfolds the later PF semidirect-product predicate locally and avoids a Section 3 to PF dependency cycle",
          "The final owned-file exact check exits zero; the root targeted build completes across 8762 jobs, and root integration review confirms the public theorem statement, strong-induction reduction, both chief-factor branches, and Section 15 wrapper call shape" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.OddPrimeSemidirectTheorem",
          "Submission.OddOrder.BG.Section03.OddPrimeElementaryAbelianCentralizer",
          "Submission.OddOrder.MathlibSupport.AmbientFitting",
          "Submission.OddOrder.MathlibSupport.ChiefFactorFaithfulPCore",
          "Submission.OddOrder.MathlibSupport.ChiefStabilizerFitting",
          "Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent",
          "Submission.OddOrder.MathlibSupport.CoprimeFittingCentralizer",
          "Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy",
          "Submission.OddOrder.MathlibSupport.SylowFunctorial" ]
      status := "complete" },
    { coqFile := "BGsection3.v: prime_Frobenius_sol_kernel_nil"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel"
      role := "Prove nilpotence of a solvable Frobenius kernel with prime-order complement"
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius_sol_kernel_nil"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel"
      role := "Extend Frobenius-kernel nilpotence from a prime complement to every solvable complement"
      mappedDeclarations := ["Frobenius_sol_kernel_nil"]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel",
          "Submission.OddOrder.BG.Section03.SemiregularConjugation" ]
      status := "complete" },
    { coqFile := "BGsection15.v: quotient Frobenius-kernel step in Fcore_structure"
      leanModule := "Submission.OddOrder.BG.Section03.PrimeFrobeniusQuotientKernel"
      role := "Descend a prime complement through a coprime normal kernel and prove the literal subgroup quotient nilpotent"
      mappedDeclarations := ["primeFrobeniusQuotientKernel_nilpotent"]
      notes :=
        [ "The owned-file exact check passes without output; the batched root targeted build completes across 8656 jobs, and root integration review confirms the quotient complement, centralizer, actor-cardinality, and nilpotence transport interface" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel",
          "Submission.OddOrder.MathlibSupport.ComplementQuotient",
          "Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy" ]
      status := "complete" },
    { coqFile := "BGsection3.v: Frobenius_prime_rfix1 and Frobenius_prime_cent_prime (Theorem 3.5)"
      leanModule := "Submission.OddOrder.BG.Section03.FrobeniusPrimeFixedPoint"
      role := "Prove the one-dimensional fixed-space theorem for a prime Frobenius complement and its elementary-abelian action corollary"
      status := "complete" },
    { coqFile := "BGsection4.v: class-two Hall-Petresco support for exponent_odd_nil23"
      leanModule := "Submission.OddOrder.MathlibSupport.NilpotencyClassTwoPowers"
      role := "Collect powers in class two and construct the odd-prime power homomorphism"
      status := "complete" },
    { coqFile := "BGsection4.v: expMR_fg Hall-Petresco formula"
      leanModule := "Submission.OddOrder.MathlibSupport.NilpotencyClassThreePowers"
      role := "Prove the class-three product formula with both weight-three binomial corrections"
      status := "complete" },
    { coqFile := "BGsection4.v: nil_class branches in exponent_odd_nil23"
      leanModule := "Submission.OddOrder.MathlibSupport.NilpotencyClassPowerMaps"
      role := "Derive central triple commutators from nilpotency class and package the pth-power homomorphisms"
      status := "complete" },
    { coqFile := "mathcomp gfunctor.v: first omega subgroup"
      leanModule := "Submission.OddOrder.MathlibSupport.OmegaOne"
      role := "Define omega one as the subgroup generated by p-torsion and connect element powers to its exponent"
      status := "complete" },
    { coqFile := "mathcomp gfunctor.v: first omega subgroup functoriality"
      leanModule := "Submission.OddOrder.MathlibSupport.OmegaOneFunctorial"
      role := "Map omega one through homomorphisms and equivalences, and package its characteristic, normal, and p-group structure"
      status := "complete" },
    { coqFile := "mathcomp finmodule.v: elementary abelian rank"
      leanModule := "Submission.OddOrder.MathlibSupport.ElementaryAbelian"
      role := "Package elementary abelian p-groups of fixed rank and exclude cyclicity in rank two"
      status := "complete" },
    { coqFile := "mathcomp fingroup.v: prime-index subgroup support"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeIndex"
      role := "Show prime-index subgroups are maximal and are normal inside finite p-groups"
      status := "complete" },
    { coqFile := "BGsection4.v: strict lower-central descent in p-groups"
      leanModule := "Submission.OddOrder.MathlibSupport.NilpotentNormalCommutator"
      role := "Force the mixed commutator of a nontrivial normal subgroup to be proper in a finite p-group"
      status := "complete" },
    { coqFile := "BGsection4.v: upper-central class-two support"
      leanModule := "Submission.OddOrder.MathlibSupport.UpperCentralDerived"
      role := "Bound the lower central series and nilpotency class of the second upper-central subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: normal p2Elem lies in Z2"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalElementaryAbelianRankTwo"
      role := "Place a normal elementary abelian rank-two subgroup of a finite p-group inside its second upper center"
      status := "complete" },
    { coqFile := "BGsection4.v: Ohm1_odd_ucn2 structural support"
      leanModule := "Submission.OddOrder.MathlibSupport.UpperCentralOmegaOne"
      role := "Derive noncyclicity and exponent-p structure of omega one in Z2 from a normal elementary abelian rank-two subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: expR1p induction in exponent_odd_nil23"
      leanModule := "Submission.OddOrder.MathlibSupport.OmegaOneSmallNilpotency"
      role := "Prove omega one has exponent dividing p by strong induction through maximal normal subgroups"
      status := "complete" },
    { coqFile := "BGsection4.v: exponent_odd_nil23 (Proposition 4.3)"
      leanModule := "Submission.OddOrder.BG.Section04.ExponentOddNil23"
      role := "Combine the omega-one exponent bound with multiplicativity of pth powers under the derived-subgroup hypothesis"
      status := "complete" },
    { coqFile := "BGsection4.v: Burnside normal-complement support for SCN_Sylow_cent_dprod"
      leanModule := "Submission.OddOrder.MathlibSupport.CentralSylowPrimeCore"
      role := "Identify the Burnside transfer kernel with the p-prime core when a Sylow subgroup is central"
      status := "complete" },
    { coqFile := "BGsection4.v: SCN intersection and centralizer transport"
      leanModule := "Submission.OddOrder.MathlibSupport.SCNCentralizer"
      role := "Realize an SCN subgroup as a central Sylow subgroup of its full centralizer"
      status := "complete" },
    { coqFile := "BGsection4.v: max_SCN selection used in Lemma 4.7"
      leanModule := "Submission.OddOrder.MathlibSupport.SCNExistence"
      role := "Extend a prescribed normal abelian subgroup of a finite p-group to a self-centralizing normal abelian subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: SCN_Sylow_cent_dprod (Proposition 4.4(b))"
      leanModule := "Submission.OddOrder.BG.Section04.SCNSylowCentralizer"
      role := "Decompose the SCN centralizer as its p-prime core complemented by the induced Sylow subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: odd cyclic-maximal automorphism support"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicPrimePowerAutomorphism"
      role := "Show that a p-torsion automorphism of a cyclic odd-prime-power group fixes all pth powers"
      status := "complete" },
    { coqFile := "BGsection4.v: Ohm1_extremal_odd (Lemma 4.5(b))"
      leanModule := "Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal"
      role := "Identify omega one as elementary abelian of rank two when a noncyclic odd p-group has a cyclic subgroup of index p"
      status := "complete" },
    { coqFile := "BGsection4.v: normal_pgroup support for ex_odd_normal_p2Elem"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalSubgroupPowerSeries"
      role := "Construct ambient-normal subgroups of every prescribed prime-power order inside a normal p-subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: ex_odd_normal_p2Elem (Lemma 4.5(a))"
      leanModule := "Submission.OddOrder.BG.Section04.NormalRankTwo"
      role := "Construct a normal elementary abelian rank-two subgroup in every noncyclic finite odd p-group"
      status := "complete" },
    { coqFile := "BGsection4.v: odd_normal_p2Elem_exists (Proposition 4.6)"
      leanModule := "Submission.OddOrder.BG.Section04.OddNormalRankTwoExists"
      role := "Choose the normal elementary abelian rank-two subgroup inside a prescribed noncyclic normal subgroup"
      status := "complete" },
    { coqFile := "solvable/maximal.v: Ohm1_cent_max_normal_abelem (Aschbacher 23.16)"
      leanModule := "Submission.OddOrder.MathlibSupport.OmegaOneCentralizerMaxNormal"
      role := "Identify omega one of the centralizer of a maximal normal elementary-abelian subgroup in an odd p-group"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_SCN3_empty (Lemma 4.7)"
      leanModule := "Submission.OddOrder.BG.Section04.SCNRankThreeEmpty"
      role := "Equate the absence of elementary-abelian rank three with emptiness of the rank-three SCN family"
      status := "complete" },
    { coqFile := "BGsection4.v: odd_pgroup_rank1_cyclic"
      leanModule := "Submission.OddOrder.BG.Section04.OddPGroupRankOne"
      role := "Characterize cyclic odd p-groups by the absence of an elementary abelian rank-two subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: odd_rank1_Zgroup"
      leanModule := "Submission.OddOrder.BG.Section04.OddZGroupRankOne"
      role := "Characterize odd-order Z-groups by the rank-one condition on every Sylow subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: Ohm1_odd_ucn2 (Lemma 4.5(c))"
      leanModule := "Submission.OddOrder.BG.Section04.OmegaOneUpperCentral"
      role := "Derive noncyclicity and exponent p of omega one in the second upper-central subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: logn_quotient_cent_abelem support for Proposition 4.8(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.PSubgroupGeneralLinearTwo"
      role := "Bound p-subgroups of GL in dimensions at most two and package the faithful-representation cardinal estimate"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_exponent_p_p3group (Proposition 4.8(a))"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoExponentPrime"
      role := "Bound an exponent-p finite p-group of local elementary-abelian rank at most two by p cubed"
      status := "complete" },
    { coqFile := "BGsection4.v: exponent_Ohm1_rank2 (Proposition 4.8(b))"
      leanModule := "Submission.OddOrder.BG.Section04.ExponentOmegaOneRankTwo"
      role := "Prove omega one has exponent p for primes above three under the local rank-two hypothesis"
      status := "complete" },
    { coqFile := "BGsection4.v: quotient_p2_Ohm1 (Lemma 4.9)"
      leanModule := "Submission.OddOrder.BG.Section04.QuotientOmegaOneRankTwo"
      role := "Show the omega-one cardinal bound by p squared is inherited by every quotient for primes above three"
      status := "complete" },
    { coqFile := "BGsection4.v: metacyclic predicate support"
      leanModule := "Submission.OddOrder.MathlibSupport.Metacyclic"
      role := "Package a cyclic normal subgroup with cyclic quotient as the metacyclic group interface"
      status := "complete" },
    { coqFile := "BGsection4.v: Ohm1_metacyclic_p2Elem (Lemma 4.10)"
      leanModule := "Submission.OddOrder.BG.Section04.MetacyclicOmegaOne"
      role := "Prove that a finite odd noncyclic metacyclic p-group has elementary-abelian omega one of rank two"
      status := "complete" },
    { coqFile := "BGsection4.v: central prime kernel and cyclic-lift setup in p2_Ohm1_metacyclic"
      leanModule := "Submission.OddOrder.MathlibSupport.HuppertCentralKernel"
      role := "Choose the central order-p kernel and separate the power-subgroup and exponent-p derived branches"
      status := "complete" },
    { coqFile := "BGsection4.v: two-generator commutator calculation in p2_Ohm1_metacyclic"
      leanModule := "Submission.OddOrder.MathlibSupport.HuppertDerivedCyclic"
      role := "Lift a metacyclic quotient tower and prove the derived subgroup is generated by one central commutator"
      status := "complete" },
    { coqFile := "BGsection4.v: maximal cyclic overgroup step in p2_Ohm1_metacyclic"
      leanModule := "Submission.OddOrder.BG.Section04.HuppertMaximalCyclic"
      role := "Use Lemma 4.10 and the omega-one cardinal bound to force the quotient by a maximal cyclic normal subgroup to be cyclic"
      status := "complete" },
    { coqFile := "BGsection4.v: p2_Ohm1_metacyclic (Proposition 4.11)"
      leanModule := "Submission.OddOrder.BG.Section04.HuppertMetacyclic"
      role := "Prove Huppert's metacyclicity criterion by strong induction on the p-group cardinality"
      status := "complete" },
    { coqFile := "BGsection4.v: metacyclic subgroup and derived-subgroup support for Theorem 4.12"
      leanModule := "Submission.OddOrder.MathlibSupport.MetacyclicSubgroups"
      role := "Restrict metacyclicity to subgroups and show the derived subgroup of a metacyclic group is cyclic"
      status := "complete" },
    { coqFile := "BGsection4.v: coprime commutator idempotence in Theorem 4.12"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent"
      role := "Show a coprime action acts perfectly on its mixed commutator"
      status := "complete" },
    { coqFile := "BGsection4.v: Maschke complement in Theorem 4.12(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement"
      role := "Construct an invariant complement inside an elementary-abelian module for a coprime automorphism action"
      status := "complete" },
    { coqFile := "BGsection4.v: cyclic normalizer commutator support for Theorem 4.12(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclicNormalizerCommutator"
      role := "Make the commutator of two groups normalizing a cyclic subgroup centralize that subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: restricted invariant-subgroup actions in Theorem 4.12(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.InvariantSubgroupAction"
      role := "Restrict automorphisms to invariant subgroups and transport invariant complements back to the ambient group"
      status := "complete" },
    { coqFile := "BGsection4.v: omega-one factor argument in Theorem 4.12(c)"
      leanModule := "Submission.OddOrder.BG.Section04.MetacyclicComplementFactors"
      role := "Use disjoint omega-one factors in a rank-two metacyclic p-group to force both complement factors cyclic"
      status := "complete" },
    { coqFile := "BGsection4.v: coprime_metacyclic_cent_sdprod (Theorem 4.12)"
      leanModule := "Submission.OddOrder.BG.Section04.CoprimeMetacyclicCommutator"
      role := "Split an odd metacyclic p-group into its mixed commutator and fixed-point factors and prove the guarded cyclicity and derived-subgroup conclusions"
      status := "complete" },
    { coqFile := "BGsection4.v: arithmetic support for pi_Aut_rank2_pgroup"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeDivisorSquareSubOne"
      role := "Place a prime divisor of p squared minus one below p and in one of its two half-factors"
      status := "complete" },
    { coqFile := "BGsection4.v: elementary-abelian action support for pi_Aut_rank2_pgroup"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeOrderElementaryAbelianAction"
      role := "Force a distinct prime-order faithful action in elementary-abelian rank at most two to divide p squared minus one"
      status := "complete" },
    { coqFile := "BGsection4.v: pi_Aut_rank2_pgroup (Lemmas 4.13--4.14)"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoPGroupAutomorphismPrimes"
      role := "Constrain prime divisors of the automorphism group of an odd p-group with no elementary-abelian rank-three subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: critical_extraspecial coverage of Lemma 4.15"
      leanModule := "Submission.OddOrder.MathlibSupport.ExtraspecialCriticalCentralProduct"
      role := "Generate a p-group from an extraspecial subgroup and its centralizer when the mixed commutator lies in the derived subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: prime-cube extraspecial support for Theorem 4.16"
      leanModule := "Submission.OddOrder.MathlibSupport.PrimeCubePGroupExtraspecial"
      role := "Recognize every noncommutative p-group of order p cubed as extraspecial, including the p equals two cases"
      status := "complete" },
    { coqFile := "BGsection4.v: omega-one centralizer equality in Theorem 4.16"
      leanModule := "Submission.OddOrder.MathlibSupport.OmegaOneCentralizerExtraspecial"
      role := "Identify omega one of the centralizer of an extraspecial omega subgroup with its ambient mapped derived subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: noncritical Blackburn branch of Theorem 4.16"
      leanModule := "Submission.OddOrder.BG.Section04.BlackburnNoncritical"
      role := "Eliminate the noncritical extraspecial branch by the rank-two quotient-action and scalar-congruence argument"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_coprime_comm_cprod (Theorem 4.16)"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoCoprimeCommutatorCentralProduct"
      role := "Classify an odd rank-two p-group under a perfect coprime action as abelian or an extraspecial-cyclic central product and prove p exceeds three"
      status := "complete" },
    { coqFile := "BGsection4.v: Frattini-quotient automorphism support for Theorem 4.17"
      leanModule := "Submission.OddOrder.MathlibSupport.FrattiniQuotientAutomorphism"
      role := "Act on the Frattini quotient and prove the Burnside-basis kernel is a p-group"
      status := "complete" },
    { coqFile := "BGsection4.v: exponent-p Frattini-rank support for Theorem 4.17"
      leanModule := "Submission.OddOrder.MathlibSupport.FrattiniQuotientRankTwo"
      role := "Bound the Frattini quotient by p squared for exponent-p groups with no elementary-abelian rank-three subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: der1_Aut_rank2_pgroup (Theorem 4.17)"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoAutomorphismDerived"
      role := "Restrict to a critical subgroup and use its one- or two-dimensional Frattini action to prove the automorphism derived subgroup is a p-group"
      status := "complete" },
    { coqFile := "BGsection4.v: p-rank transport across the p-prime-core quotient for Theorem 4.18(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimeQuotientElementaryAbelian"
      role := "Lift a rank-three elementary-abelian subgroup across the p-prime core by a Schur-Zassenhaus complement"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_max_pdiv (Theorem 4.18(a))"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoPrimeDivisors"
      role := "Bound every prime divisor of the quotient by the p-prime core using its self-centralizing p-core and the rank-two automorphism theorem"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_min_p_complement (Theorem 4.18(b))"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoMinimalPrimeComplement"
      role := "Use least-prime minimality and the quotient prime-divisor bound to make the p-prime core a Hall p-prime subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: derived Hall support for Theorem 4.18(c)"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimeCoreDerivedHall"
      role := "Lift a p-group derived quotient to a normal Hall p-prime core of the ambient derived subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: O_{p',p} third-isomorphism support for Theorem 4.18(e)"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimePCoreThirdIsomorphism"
      role := "Identify the iterated quotient by the p-prime core and quotient p-core with the quotient by O_{p',p}"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_der1_complement (Theorem 4.18(c,e))"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoDerivedComplement"
      role := "Prove the derived p-prime core is a Hall complement and identify the abelian p-prime quotient by O_{p',p}"
      status := "complete" },
    { coqFile := "BGsection4.v: normal Hall containment support for Theorem 4.18(d)"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalPrimeComplementContainment"
      role := "Place every p-prime subgroup inside a normal Hall p-prime complement"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_sub_p'core_der1 (Theorem 4.18(d))"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoDerivedPrimeCore"
      role := "Place every ambient p-prime subgroup of the derived subgroup in its mapped p-prime core"
      status := "complete" },
    { coqFile := "BGsection4.v: faithful action on a chief p-factor for Corollary 4.19"
      leanModule := "Submission.OddOrder.MathlibSupport.ChiefFactorFaithfulPCore"
      role := "Identify the faithful chief-factor quotient action and eliminate its p-core"
      status := "complete" },
    { coqFile := "BGsection4.v: quotient transport for Corollary 4.19"
      leanModule := "Submission.OddOrder.MathlibSupport.ChiefFactorQuotient"
      role := "Transport chief factors and their prime-power structure across a quotient"
      status := "complete" },
    { coqFile := "BGsection4.v: p-prime-core quotient support for Corollary 4.19"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimeCoreFunctorial"
      role := "Transport the p-prime core through canonical quotient-image equivalences"
      status := "complete" },
    { coqFile := "BGsection4.v: coprime kernel intersection in Corollary 4.19"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimeFactorIntersection"
      role := "Place the intersection of a p-prime kernel with a chief p-factor inside its lower term"
      status := "complete" },
    { coqFile := "BGsection4.v: core-free branch of rank2_der1_cent_chief (Corollary 4.19)"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoChiefFactorCoreFree"
      role := "Use the rank-two automorphism theorem on the p-core action to centralize a chief p-factor"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_der1_cent_chief (Corollary 4.19)"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoChiefFactorCentralizer"
      role := "Remove the p-prime core by quotienting and lift the chief-factor centralizer conclusion"
      status := "complete" },
    { coqFile := "BGsection4.v: chief-factor stabilizer support for Theorem 4.20(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.ChiefStabilizerFitting"
      role := "Place a normal subgroup stabilizing every chief factor inside the Fitting subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_der1_sub_Fitting (Theorem 4.20(a))"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoFittingDerived"
      role := "Use Corollary 4.19 on all chief factors below the Fitting subgroup to contain the derived subgroup"
      status := "complete" },
    { coqFile := "BGsection4.v: Fitting/Sylow Frattini support for Theorem 4.20(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.FittingSylowFrattini"
      role := "Factor through the Fitting subgroup and a Sylow normalizer, then control characteristic derived subgroups"
      status := "complete" },
    { coqFile := "BGsection4.v: rank2_char_Sylow_normal (Theorem 4.20(b))"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoCharacteristicSylowNormal"
      role := "Make every characteristic subgroup below a Sylow derived subgroup normal in the ambient group"
      status := "complete" },
    { coqFile := "BGsection4.v: nilpotent prime-core Hall and quotient support for Theorem 4.20(c)"
      leanModule := "Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall"
      role := "Show the p-prime core of a finite nilpotent group is Hall and lift it across normal p-group quotients"
      status := "complete" },
    { coqFile := "BGsection4.v: rank transport into a containing Sylow subgroup for Theorem 4.20(c)"
      leanModule := "Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport"
      role := "Transport elementary-abelian rank-three witnesses through subgroup-of and Sylow containment"
      status := "complete" },
    { coqFile := "BGsection4.v: least-prime factor of Theorem 4.20(c)"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoMinimalPrimeCoreHall"
      role := "Prove the p-prime core is a Hall complement for the least prime divisor"
      status := "complete" },
    { coqFile := "BGsection4.v: pi-core infrastructure for Theorem 4.20(c)"
      leanModule := "Submission.OddOrder.MathlibSupport.PiCore"
      role := "Define the largest normal subgroup supported on a prime set and prove its functorial core properties"
      status := "complete" },
    { coqFile := "BGsection4.v: Fitting-rank restriction for the cutoff induction in Theorem 4.20(c)"
      leanModule := "Submission.OddOrder.MathlibSupport.FittingRankRestriction"
      role := "Restrict the absence of elementary-abelian rank three from a group to a normal subgroup's Fitting core"
      status := "complete" },
    { coqFile := "BGsection4.v: intermediate factors of Theorem 4.20(c)"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoPrimeCutoffCoreHall"
      role := "Construct the normal Hall subgroup supported on all primes above an arbitrary cutoff"
      status := "complete" },
    { coqFile := "BGsection4.v: greatest-prime factor of Theorem 4.20(c)"
      leanModule := "Submission.OddOrder.BG.Section04.RankTwoMaximalPrimeCoreSylow"
      role := "Identify the cutoff core at the greatest prime divisor with the Sylow p-core"
      status := "complete" },
    { coqFile := "BGsection6.v: Theorems 6.1 and 6.2"
      leanModule := "Submission.OddOrder.BG.Section06.PuigConsequences"
      role := "Specialize odd p-stability to p-abelian-constrained groups and derive Puig factorization and normality"
      status := "complete" },
    { coqFile := "BGsection6.v: coprime_der1_sdprod (Lemma 6.3(a))"
      leanModule := "Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect"
      role := "Identify the mixed commutator in a coprime semidirect product and bound the complement centralizer by the kernel derived subgroup"
      status := "complete" },
    { coqFile := "BGsection6.v: prime_nil_der1_factor (Lemma 6.3(b))"
      leanModule := "Submission.OddOrder.BG.Section06.PrimeNilDerivedFactor"
      role := "For nilpotent derived subgroup and prime abelianization, prove coprime factorization and identify every complement mixed commutator"
      status := "complete" },
    { coqFile := "BGsection6.v: Schur-Zassenhaus complement conjugacy support for Lemma 6.5"
      leanModule := "Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy"
      role := "Prove conjugacy of complements to a solvable normal Hall subgroup by induction through its derived subgroup"
      status := "complete" },
    { coqFile := "BGsection6.v: pprod_focal_coprime, pprod_norm_coprime_prod, and pprod_trans_coprime (Lemma 6.5)"
      leanModule := "Submission.OddOrder.BG.Section06.PProdCoprime"
      role := "Identify focal intersections and factor normalizers and transporters in a coprime product"
      status := "complete" },
    { coqFile := "BGsection6.v: p.-length_1 support for Lemma 6.6"
      leanModule := "Submission.OddOrder.MathlibSupport.PLengthOne"
      role := "Express p-length at most one through the p-core of the quotient by the p-prime core"
      status := "complete" },
    { coqFile := "BGsection6.v: plength1_Sylow_prod through plength1_Sylow_Jsub (Lemma 6.6)"
      leanModule := "Submission.OddOrder.BG.Section06.PLengthOneProduct"
      role := "Derive the Frattini factorization, focal consequence, transporter factorization, and controlled Sylow conjugacy for p-length-one groups"
      status := "complete" },
    { coqFile := "mathcomp pmaxElemP, pmaxElemS, and pmaxElem_LdivP"
      leanModule := "Submission.OddOrder.MathlibSupport.PMaxElem"
      role := "Package maximal elementary-abelian p-subgroups and characterize maximality by their p-torsion centralizer"
      status := "complete" },
    { coqFile := "BGsection1.v: abelian omega-one action support for Theorem 1.11"
      leanModule := "Submission.OddOrder.MathlibSupport.AbelianPGroupOmegaAction"
      role := "Promote centralization of p-torsion to centralization of an abelian p-group under a coprime action"
      status := "complete" },
    { coqFile := "BGsection1.v: coprime_cent_prod support for Theorem 1.11"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct"
      role := "Decompose a solvable coprime action group into its mixed commutator and action centralizer"
      status := "complete" },
    { coqFile := "BGsection1.v: characteristic perfect-action reduction for Theorem 1.11"
      leanModule := "Submission.OddOrder.MathlibSupport.CharacteristicPerfectCoprimePGroup"
      role := "Analyze characteristic abelian subgroups under a perfect coprime action and derive the special p-group branch"
      status := "complete" },
    { coqFile := "BGsection1.v: coprime_odd_faithful_Ohm1 (Theorem 1.11)"
      leanModule := "Submission.OddOrder.MathlibSupport.OddPGroupOmegaAction"
      role := "Show a coprime action on an odd p-group is trivial when it centralizes omega one"
      status := "complete" },
    { coqFile := "BGsection1.v: coprime_odd_faithful_cent_abelem (Corollary 1.12)"
      leanModule := "Submission.OddOrder.MathlibSupport.OddPGroupElementaryCentralizer"
      role := "Convert the maximal-elementary p-torsion centralizer condition into centralization of the whole odd p-group"
      status := "complete" },
    { coqFile := "BGsection1.v: critical-subgroup infrastructure for Theorem 1.13"
      leanModule := "Submission.OddOrder.MathlibSupport.Critical"
      role := "Package critical subgroups, characteristic lattice operations, omega-one nontriviality, and the class-two bound"
      status := "complete" },
    { coqFile := "BGsection1.v: Thompson critical subgroup existence for Theorem 1.13"
      leanModule := "Submission.OddOrder.MathlibSupport.ThompsonCritical"
      role := "Construct a critical characteristic subgroup of every finite p-group"
      status := "complete" },
    { coqFile := "BGsection1.v: characteristic automorphism restriction support for Theorem 1.13"
      leanModule := "Submission.OddOrder.MathlibSupport.CharacteristicMulAutRestriction"
      role := "Restrict ambient automorphisms to a characteristic subgroup and identify pointwise-fixer kernels"
      status := "complete" },
    { coqFile := "BGsection1.v: p-core quotient support for critical_p_stab_Aut"
      leanModule := "Submission.OddOrder.MathlibSupport.PCoreSelfQuotient"
      role := "Control the p-core and prime divisors after quotienting a finite nilpotent group by its p-core"
      status := "complete" },
    { coqFile := "BGsection1.v: critical_p_stab_Aut"
      leanModule := "Submission.OddOrder.MathlibSupport.CriticalAutomorphism"
      role := "Show that automorphisms fixing a critical subgroup pointwise form a p-group"
      status := "complete" },
    { coqFile := "BGsection1.v: prime-order omega-one fixer step in critical_odd"
      leanModule := "Submission.OddOrder.MathlibSupport.CriticalOmegaAutomorphism"
      role := "Promote fixation of mapped omega one to fixation of a critical subgroup for a prime-order automorphism"
      status := "complete" },
    { coqFile := "BGsection1.v: critical_odd (Theorem 1.13)"
      leanModule := "Submission.OddOrder.BG.Section01.CriticalOdd"
      role := "Construct the characteristic class-two exponent-p subgroup whose pointwise automorphism fixer is a p-group"
      status := "complete" },
    { coqFile := "BGsection6.v: plength1_norm_pmaxElem (Theorem 6.7)"
      leanModule := "Submission.OddOrder.BG.Section06.PLengthOneMaximalElementary"
      role := "Put every normalized p-prime subgroup inside the p-prime core under a maximal elementary subgroup in a solvable p-length-one group"
      status := "complete" },
    { coqFile := "BGsection5.v: narrow, narrow_structure, injm_narrow, isog_narrow, and narrowJ"
      leanModule := "Submission.OddOrder.BG.Section05.Equivariance"
      role := "Define narrow groups and transport narrowness through injective images, isomorphisms, and conjugation"
      status := "complete" },
    { coqFile := "BGsection5.v: narrow_pmaxElem"
      leanModule := "Submission.OddOrder.BG.Section05.NarrowMaximalElementary"
      role := "Extract a maximal elementary-abelian rank-two subgroup from the rank-three narrowness hypothesis"
      status := "complete" },
    { coqFile := "BGsection5.v: rank3_SCN3 and normal_p2Elem_SCN3 (Lemma 5.1(a-b))"
      leanModule := "Submission.OddOrder.BG.Section05.NormalRankTwoSCNRankThree"
      role := "Produce a rank-three SCN subgroup and enlarge every normal elementary-abelian rank-two subgroup into one"
      status := "complete" },
    { coqFile := "BGsection5.v: Z, W, and T setup for Ohm1_ucn_p2maxElem"
      leanModule := "Submission.OddOrder.BG.Section05.OmegaUpperCentralSetup"
      role := "Define the mapped omega-one center, mapped omega-one second upper center, and their characteristic ambient centralizer"
      status := "complete" },
    { coqFile := "BGsection5.v: sWRZ in Ohm1_ucn_p2maxElem"
      leanModule := "Submission.OddOrder.BG.Section05.OmegaUpperCentralCommutator"
      role := "Place the mixed commutator of omega one of the second upper center inside omega one of the center"
      status := "complete" },
    { coqFile := "BGsection5.v: noncyclic exponent-p structure in Ohm1_ucn_p2maxElem"
      leanModule := "Submission.OddOrder.BG.Section05.OmegaUpperCentralStructure"
      role := "Transport the Section 4 upper-central result to show the mapped subgroup is noncyclic of exponent p"
      status := "complete" },
    { coqFile := "BGsection5.v: cardZ in Ohm1_ucn_p2maxElem"
      leanModule := "Submission.OddOrder.BG.Section05.OmegaCenterMaximal"
      role := "Show every maximal rank-two elementary subgroup contains omega one of the center and force its cardinality to p"
      status := "complete" },
    { coqFile := "BGsection5.v: C_W(E) = Z in Ohm1_ucn_p2maxElem"
      leanModule := "Submission.OddOrder.BG.Section05.OmegaUpperCentralCentralizer"
      role := "Compute the centralizer kernel of the upper-central omega subgroup acting on the maximal elementary subgroup"
      status := "complete" },
    { coqFile := "BGsection5.v: rank-two linear-action estimate in Ohm1_ucn_p2maxElem"
      leanModule := "Submission.OddOrder.MathlibSupport.Section05RankTwoAction"
      role := "Bound the faithful p-group quotient of an action on an elementary-abelian rank-two group by p"
      status := "complete" },
    { coqFile := "BGsection5.v: cardW and rank W in Ohm1_ucn_p2maxElem"
      leanModule := "Submission.OddOrder.BG.Section05.OmegaUpperCentralRankTwo"
      role := "Use the action kernel and cardinal bound to prove omega one of the second upper center has elementary-abelian rank two"
      status := "complete" },
    { coqFile := "BGsection5.v: strict centralizer and index calculation in Ohm1_ucn_p2maxElem"
      leanModule := "Submission.OddOrder.BG.Section05.OmegaUpperCentralIndex"
      role := "Prove the maximal elementary subgroup is not centralized by W and that C_G(W) has index p"
      status := "complete" },
    { coqFile := "BGsection5.v: Ohm1_ucn_p2maxElem (Lemma 5.2)"
      leanModule := "Submission.OddOrder.BG.Section05.OmegaUpperCentralMaximal"
      role := "Assemble the five exact omega-center, rank-two, characteristic, noncentrality, and prime-index conclusions"
      status := "complete" },
    { coqFile := "BGsection5.v: elementary-abelian direct-product arithmetic for narrow_cent_dprod"
      leanModule := "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup"
      role := "Add ranks and cardinalities for commuting disjoint elementary-abelian subgroups"
      status := "complete" },
    { coqFile := "BGsection5.v: maximality of S <*> Ohm_1(Z(R)) in narrow_cent_dprod"
      leanModule := "Submission.OddOrder.BG.Section05.NarrowPrimeSupMaximal"
      role := "Show that a prime-order subgroup joined with omega one of the center is maximal elementary abelian of rank two"
      status := "complete" },
    { coqFile := "BGsection5.v: centralizer decomposition in narrow_cent_dprod"
      leanModule := "Submission.OddOrder.BG.Section05.NarrowPrimeCentralizerDecomposition"
      role := "Derive the prime-index factorization, derived-subgroup intersection, and centralizer join decomposition"
      status := "complete" },
    { coqFile := "BGsection5.v: narrow_cent_dprod (Theorem 5.3(d))"
      leanModule := "Submission.OddOrder.BG.Section05.NarrowCentralizerDirectProduct"
      role := "Identify the prime-order centralizer as an internal direct product with a cyclic factor"
      status := "complete" },
    { coqFile := "BGsection5.v: narrow_centP (Corollary 5.4)"
      leanModule := "Submission.OddOrder.BG.Section05.NarrowCentralizerCharacterization"
      role := "Characterize narrowness by a prime-order subgroup whose ambient centralizer has p-rank at most two"
      status := "complete" },
    { coqFile := "BGsection5.v: narrow_structureP (Theorem 5.3)"
      leanModule := "Submission.OddOrder.BG.Section05.NarrowStructureCharacterization"
      role := "Prove the equivalence between narrowness and the cyclic internal direct-product structure of a centralizer"
      status := "complete" },
    { coqFile := "BGsection5.v: Aut_narrow and narrow_der1_complement_max_pdiv (Theorems 5.5(a,b) and 5.6(a,c))"
      leanModule := "Submission.OddOrder.BG.Section05.NarrowAutomorphismAndComplement"
      role := "Derive the automorphism consequences of narrowness and the maximal-prime complement structure of the derived subgroup"
      status := "complete" },
    { coqFile := "BGsection7.v: minimal-counterexample reduction through mFT_quo_sol"
      leanModule := "Submission.OddOrder.BG.Section07.MinimalCounterexample"
      role := "Package a minimal simple odd-order counterexample and its elementary subgroup and quotient consequences"
      status := "complete" },
    { coqFile := "BGsection7.v: maximal-subgroup infrastructure through norm_mmax"
      leanModule := "Submission.OddOrder.BG.Section07.MaximalSubgroups"
      role := "Develop maximal overgroups of the minimal counterexample through self-normality"
      status := "complete" },
    { coqFile := "BGsection7.v: mmaxJ through uniq_mmaxS"
      leanModule := "Submission.OddOrder.BG.Section07.UniqueMaximal"
      role := "Develop automorphism invariance and the upward-closed family of subgroups with a unique maximal overgroup"
      status := "complete" },
    { coqFile := "BGsection7.v: normed_pgroups through max_normed_uniq"
      leanModule := "Submission.OddOrder.BG.Section07.NormedSubgroups"
      role := "Define normalized prime-set subgroups and prove existence, conjugation invariance, and uniqueness of maximal members"
      status := "complete" },
    { coqFile := "BGsection7.v: cent_core_acts_max_norm"
      leanModule := "Submission.OddOrder.BG.Section07.CentralCoreAction"
      role := "Show that the prime-complement core of the centralizer acts on maximal normalized q-subgroups"
      status := "complete" },
    { coqFile := "BGsection7.v: normed_constrained_Hall"
      leanModule := "Submission.OddOrder.BG.Section07.NormedConstrainedHall"
      role := "Show that the prime-complement core of the centralizer is a Hall subgroup under Hypothesis 7.1"
      status := "complete" },
    { coqFile := "BGsection7.v: coprime_Hall_subset support for Lemma 7.1"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension"
      role := "Extend an invariant p-subgroup to an invariant Sylow subgroup under a coprime action on a solvable group"
      status := "complete" },
    { coqFile := "BGsection7.v: coprime_Hall_trans support for Lemma 7.1"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy"
      role := "Conjugate two invariant Sylow subgroups by an element of the acted-on group centralizing the coprime actor"
      status := "complete" },
    { coqFile := "BGsection7.v: normed_constrained_meet_trans (Lemma 7.1)"
      leanModule := "Submission.OddOrder.BG.Section07.NormedConstrainedMeetTrans"
      role := "Prove transitivity on maximal normalized q-subgroups meeting a common proper overgroup by cardinal-difference induction"
      status := "complete" },
    { coqFile := "BGsection7.v: coprime_abelian_gen_cent support for Theorem 7.2"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGeneration"
      role := "Find a normal cocyclic subgroup of an abelian actor whose centralizer in a nontrivial p-group is nontrivial"
      status := "complete" },
    { coqFile := "BGsection7.v: normed_constrained_rank3_trans (Theorem 7.2)"
      leanModule := "Submission.OddOrder.BG.Section07.NormedConstrainedRankThreeTrans"
      role := "Prove transitivity on maximal normalized q-subgroups when the center of the constraining subgroup has rank at least three"
      status := "complete" },
    { coqFile := "BGsection7.v: normed_constrained_rank2_trans (Theorem 7.3)"
      leanModule := "Submission.OddOrder.BG.Section07.NormedConstrainedRankTwoTrans"
      role := "Prove transitivity from q-divisibility of the centralizer when the constraining subgroup has center rank at least two"
      status := "complete" },
    { coqFile := "BGsection7.v: maximal normal quotient support for Theorem 7.4"
      leanModule := "Submission.OddOrder.MathlibSupport.SubnormalMaximalNormal"
      role := "Interpolate a maximal proper normal subgroup above a proper subnormal subgroup and prove the resulting quotient simple"
      status := "complete" },
    { coqFile := "BGsection7.v: prime-complement core functoriality for Theorem 7.4"
      leanModule := "Submission.OddOrder.BG.Section07.PrimeSetCoreFunctorial"
      role := "Transport prime-set cores through automorphisms and identify the centralizer core used after subnormal ascent"
      status := "complete" },
    { coqFile := "BGsection7.v: coprime conjugator adjustment for Theorem 7.4"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeHallConjugatorAdjustment"
      role := "Replace a conjugator in a coprime normal Hall factor by one centralizing the controlling subgroup"
      status := "complete" },
    { coqFile := "BGsection7.v: focal and normalizer consequences used in Theorem 7.4"
      leanModule := "Submission.OddOrder.BG.Section07.NormedTransitiveConsequences"
      role := "Derive the ambient focal containment and exact normalizer factorization from normalized transitivity"
      status := "complete" },
    { coqFile := "BGsection7.v: quotient fixed-point step in Theorem 7.4"
      leanModule := "Submission.OddOrder.BG.Section07.NormedQuotientFixedPoint"
      role := "Find a maximal normalized subgroup fixed by a quotient p-group using transitivity and orbit cardinality"
      status := "complete" },
    { coqFile := "BGsection7.v: normed_trans_superset (Theorem 7.4)"
      leanModule := "Submission.OddOrder.BG.Section07.NormedTransSuperset"
      role := "Ascend normalized transitivity through a subnormal prime-set superset and obtain the core, focal, and normalizer conclusions"
      status := "complete" },
    { coqFile := "BGsection7.v: maximal elementary-abelian subtype support for Proposition 7.5(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.PMaxElemSubtype"
      role := "Transport maximal elementary-abelian subgroup data into an ambient subgroup subtype"
      status := "complete" },
    { coqFile := "BGsection7.v: p-group prime-support support for Proposition 7.5(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.PGroupPrimeSupport"
      role := "Identify the prime support of a nontrivial finite p-group with the singleton containing p"
      status := "complete" },
    { coqFile := "BGsection7.v: plength_1_normed_constrained (Proposition 7.5(a))"
      leanModule := "Submission.OddOrder.BG.Section07.PLengthOneNormedConstrained"
      role := "Derive the normalized-constrained condition for a nontrivial maximal elementary subgroup from p-length one in every proper subgroup"
      status := "complete" },
    { coqFile := "BGsection7.v: solvable quotient-centralizer support for Proposition 7.5(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.SolvableQuotientCentralizer"
      role := "Lift centralizers through coprime quotients of finite solvable groups by complement conjugacy"
      status := "complete" },
    { coqFile := "BGsection7.v: coprime_abelian_gen_cent1 support for Proposition 7.5(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable"
      role := "Generate a solvable coprime subgroup from its centralizers under a noncyclic abelian action"
      status := "complete" },
    { coqFile := "BGsection7.v: centralizer p-prime-core support for Proposition 7.5(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.PPrimeCoreCentralizer"
      role := "Map the p-prime core of a p-subgroup centralizer into the ambient p-prime core"
      status := "complete" },
    { coqFile := "BGsection7.v: rank-two centralizer-index support for Proposition 7.5(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.RankTwoCentralizerIndex"
      role := "Bound the index of the centralizer of a normal elementary-abelian rank-two subgroup in a p-group by p"
      status := "complete" },
    { coqFile := "BGsection7.v: SCN rank-two subgroup selection for Proposition 7.5(b)"
      leanModule := "Submission.OddOrder.BG.Section07.SCNRankTwoSubgroup"
      role := "Choose a normal rank-two subgroup relative to omega one of the Sylow center and prove the required dichotomy"
      status := "complete" },
    { coqFile := "BGsection7.v: SCN prime-core step for Proposition 7.5(b)"
      leanModule := "Submission.OddOrder.BG.Section07.SCNPrimeCore"
      role := "Restrict SCN data to centralizers and place normalized p-prime subgroups in their p-prime cores"
      status := "complete" },
    { coqFile := "BGsection7.v: SCN_normed_constrained (Proposition 7.5(b))"
      leanModule := "Submission.OddOrder.BG.Section07.SCNNormedConstrained"
      role := "Derive the normalized-constrained condition for every rank-at-least-two SCN subgroup"
      status := "complete" },
    { coqFile := "BGsection7.v: elementary-abelian image support for Theorem 7.6"
      leanModule := "Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial"
      role := "Transport elementary-abelian cardinal rank through injective group homomorphisms"
      status := "complete" },
    { coqFile := "BGsection7.v: metacyclic rank support for Theorem 7.6"
      leanModule := "Submission.OddOrder.MathlibSupport.MetacyclicRank"
      role := "Bound the generator rank of every finite metacyclic group by two"
      status := "complete" },
    { coqFile := "BGsection7.v: rank-three elementary-abelian support for Theorem 7.6"
      leanModule := "Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree"
      role := "Extract an ambient elementary-abelian rank-three subgroup from an abelian p-group of generator rank at least three"
      status := "complete" },
    { coqFile := "BGsection7.v: p-prime core identification for Theorem 7.6"
      leanModule := "Submission.OddOrder.BG.Section07.PrimeSetCorePPrime"
      role := "Identify the singleton-complement prime-set core with the mapped p-prime core"
      status := "complete" },
    { coqFile := "BGsection7.v: Thompson_transitivity (Theorem 7.6)"
      leanModule := "Submission.OddOrder.BG.Section07.ThompsonTransitivity"
      role := "Prove transitivity on maximal normalized q-subgroups under the p-prime core of an SCN centralizer"
      status := "complete" },
    { coqFile := "group_representation/inertia.v: dvd_irr1_cardG"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleCharacterDegreeDivides"
      role := "Prove that an irreducible characteristic-zero representation degree divides the finite group order via integral conjugacy-class sums"
      status := "complete" },
    { coqFile := "group_representation/inertia.v: extend_solvable_coprime_irr specialization"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleHallExtension"
      role := "Extend an invariant irreducible character from a normal Hall subgroup by correcting its projective quotient action"
      status := "complete" },
    { coqFile := "PFsection1.v: scalar action from a central quotient in irr1_bound_quo"
      leanModule := "Submission.OddOrder.MathlibSupport.QuotientCentralScalarAction"
      role := "Use Schur's lemma to make a subgroup central modulo the representation kernel act by scalars"
      status := "complete" },
    { coqFile := "PFsection1.v: Burnside-density degree bound in irr1_bound_quo"
      leanModule := "Submission.OddOrder.MathlibSupport.IrreducibleDegreeIndexBound"
      role := "Bound the square of an irreducible representation degree by the index of a scalar-acting subgroup"
      status := "complete" },
    { coqFile := "PFsection1.v: Qn_aut_exists support for extend_coprime_Qn_aut"
      leanModule := "Submission.OddOrder.MathlibSupport.CyclotomicPowerAutomorphism"
      role := "Extend a coprime power action on roots of unity to an automorphism of an algebraic closure of the rationals"
      status := "complete" },
    { coqFile := "PFsection1.v: cyclotomic character-value support for dvd_restrict_cfAut and make_pi_cfAut"
      leanModule := "Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic"
      role := "Express finite-order traces in cyclotomic fields and transport Galois power actions through virtual-character values"
      status := "complete" },
    { coqFile := "PFsection13.v: sum_norm2_char_generators algebraic-norm support"
      leanModule := "Submission.OddOrder.MathlibSupport.CharacterGeneratorNorm"
      role := "Identify cyclic-generator character values as a cyclotomic Galois orbit and prove their norm-square product is a natural number"
      mappedDeclarations :=
        [ "cyclicGenerators", "mem_cyclicGenerators",
          "character_generator_product_intCast",
          "character_generator_normSq_product_natCast" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.CharacterValueCyclotomic" ]
      status := "complete" },
    { coqFile := "PFsection1.v: algebraic-integer congruence support for Peterfalvi 1.10"
      leanModule := "Submission.OddOrder.MathlibSupport.AlgebraicIntegerCongruence"
      role := "Model MathComp congruence modulo an algebraic integer and provide its additive and integral-multiplicative closure rules"
      status := "complete" },
    { coqFile := "BGsection1.v: coprime_cent_Fitting support used in Theorem 8.1(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeFittingCentralizer"
      role := "Show that a coprime normalizing subgroup centralizing the Fitting subgroup of a solvable group centralizes the whole group"
      status := "complete" },
    { coqFile := "BGsection8.v: ambient Fitting notation and prime-core transport"
      leanModule := "Submission.OddOrder.MathlibSupport.AmbientFitting"
      role := "View subgroup Fitting cores in the ambient group and transport p-cores and p-prime cores through them"
      status := "complete" },
    { coqFile := "BGsection8.v: nilpotent prime-core support for Theorem 8.1(a)"
      leanModule := "Submission.OddOrder.MathlibSupport.NilpotentPrimeCores"
      role := "Relate Sylow, p-core, p-prime-core, centralizer, and center support inside finite nilpotent groups"
      status := "complete" },
    { coqFile := "BGsection8.v: bigcap_p'core introduction step in Theorem 8.1(a)"
      leanModule := "Submission.OddOrder.BG.Section08.PrimeSetCoreIntersection"
      role := "Place a subgroup lying in every selected mapped p-prime core into the complementary prime-set core"
      status := "complete" },
    { coqFile := "BGsection8.v: Fitting_pcore in Theorem 8.1(a)"
      leanModule := "Submission.OddOrder.BG.Section08.PrimeSetCoreFitting"
      role := "Identify the ambient Fitting subgroup of a prime-set core with the corresponding core of the ambient Fitting subgroup"
      status := "complete" },
    { coqFile := "BGsection8.v: constrained-centralizer setup for Theorem 8.1(a)"
      leanModule := "Submission.OddOrder.BG.Section08.NonPCoreFittingConstrained"
      role := "Construct the normed-constrained Fitting centralizer and its prime-core containment interface"
      status := "complete" },
    { coqFile := "BGsection8.v: singleton max_normed_pgroups step in Theorem 8.1(a)"
      leanModule := "Submission.OddOrder.BG.Section08.NonPCoreFittingMaxNorm"
      role := "Show that every complementary-prime maximal normalized family over the Fitting centralizer is trivial"
      status := "complete" },
    { coqFile := "BGsection8.v: maximal-overgroup comparison in Theorem 8.1(a)"
      leanModule := "Submission.OddOrder.BG.Section08.NonPCoreFittingMaximalOvergroup"
      role := "Identify every maximal subgroup containing the Fitting centralizer with the original maximal subgroup"
      status := "complete" },
    { coqFile := "BGsection8.v: non_pcore_Fitting_Uniqueness (Theorem 8.1(a))"
      leanModule := "Submission.OddOrder.BG.Section08.NonPCoreFittingUniqueness"
      role := "Prove uniqueness of the maximal overgroup of the centralizer of a rank-three maximal elementary-abelian subgroup"
      status := "complete" },
    { coqFile := "BGsection8.v: p-core and Fitting reductions for Theorem 8.1(b)"
      leanModule := "Submission.OddOrder.BG.Section08.SCNFittingReduction"
      role := "Reduce the p-group Fitting branch to a trivial p-prime core and identify the mapped p-core"
      status := "complete" },
    { coqFile := "BGsection8.v: Puig-center and ambient Sylow support for Theorem 8.1(b)"
      leanModule := "Submission.OddOrder.BG.Section08.SCNFittingPuigCenter"
      role := "Transport the canonical Puig center and upgrade mapped Sylow subgroups to ambient Sylow subgroups"
      status := "complete" },
    { coqFile := "BGsection8.v: SCN--Fitting setup for Theorem 8.1(b)"
      leanModule := "Submission.OddOrder.BG.Section08.SCNFittingSetup"
      role := "Place the SCN subgroup in the Fitting subgroup and trivialize complementary-prime normalized subgroups"
      status := "complete" },
    { coqFile := "BGsection8.v: extremal maximal-overgroup argument for Theorem 8.1(b)"
      leanModule := "Submission.OddOrder.BG.Section08.SCNFittingMaximalOvergroup"
      role := "Promote an extremal intersection Sylow subgroup and identify every maximal overgroup using a common Puig center"
      status := "complete" },
    { coqFile := "BGsection8.v: SCN_Fitting_Uniqueness (Theorem 8.1(b))"
      leanModule := "Submission.OddOrder.BG.Section08.SCNFittingUniqueness"
      role := "Prove ambient Sylow existence, Fitting containment, and uniqueness of the maximal overgroup in the SCN branch"
      status := "complete" },
    { coqFile := "BGsection8.v: pmaxElem_exists support for Fitting_Uniqueness"
      leanModule := "Submission.OddOrder.MathlibSupport.PMaxElemExistence"
      role := "Extend an elementary-abelian subgroup to a maximal elementary-abelian subgroup inside a finite ambient subgroup"
      status := "complete" },
    { coqFile := "BGsection8.v: injective SCN transport for rank3_SCN3"
      leanModule := "Submission.OddOrder.MathlibSupport.SCNFunctorial"
      role := "Transport self-centralizing normal abelian subgroup data through injective group homomorphisms"
      status := "complete" },
    { coqFile := "BGsection8.v: elementary p-rank to generator-rank bridge"
      leanModule := "Submission.OddOrder.MathlibSupport.AbelianPGroupRankThreeConverse"
      role := "Recover generator rank three for a commutative p-group from an elementary-abelian subgroup of cardinal rank three"
      status := "complete" },
    { coqFile := "BGsection8.v: rank3_SCN3 transport in Fitting_Uniqueness"
      leanModule := "Submission.OddOrder.BG.Section08.FittingRankThreeSCN"
      role := "Construct and transport a rank-three SCN subgroup inside an ambient p-subgroup"
      status := "complete" },
    { coqFile := "BGsection8.v: Fitting_Uniqueness"
      leanModule := "Submission.OddOrder.BG.Section08.FittingUniqueness"
      role := "Combine both branches of Theorem 8.1 to prove uniqueness for every rank-three Fitting subgroup"
      status := "complete" },
    { coqFile := "BGsection9.v: normalized prime-complement core support for Theorem 9.1(b)"
      leanModule := "Submission.OddOrder.BG.Section09.NormalizedPrimeComplementCore"
      role := "Place a normalized p-prime subgroup in the mapped p-prime core and normalize that core from the ambient Sylow normalizer"
      status := "complete" },
    { coqFile := "BGsection9.v: Sylow-intersection normalizer support for Theorem 9.1(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer"
      role := "Promote a Sylow subgroup of an intersection to an ambient Sylow subgroup under normalizer containment"
      status := "complete" },
    { coqFile := "BGsection9.v: Fitting prime-core decomposition support for Theorem 9.1(b)"
      leanModule := "Submission.OddOrder.MathlibSupport.FittingSylowPrimeComplement"
      role := "Contain the Fitting subgroup in a chosen Sylow subgroup joined with the p-prime core"
      status := "complete" },
    { coqFile := "BGsection9.v: Sylow-normalizer containment in Theorem 9.1(b)"
      leanModule := "Submission.OddOrder.BG.Section09.SylowNormalizerContainment"
      role := "Force the ambient normalizer of the mapped Sylow subgroup into the chosen maximal subgroup"
      status := "complete" },
    { coqFile := "BGsection9.v: extremal Sylow overlap in Theorem 9.1(b)"
      leanModule := "Submission.OddOrder.BG.Section09.ExtremalPOverlap"
      role := "Choose a competing maximal subgroup with maximal Sylow intersection and prove its Sylow normalizer is controlled"
      status := "complete" },
    { coqFile := "BGsection9.v: noncyclic_normed_sub_Uniqueness (Theorem 9.1(b))"
      leanModule := "Submission.OddOrder.BG.Section09.NoncyclicNormedSubUniqueness"
      role := "Combine extremal overlap, Fitting uniqueness, and the rank-two Fitting--Frattini fallback"
      status := "complete" },
    { coqFile := "BGsection9.v: noncyclic_cent1_sub_Uniqueness (Theorem 9.1(a))"
      leanModule := "Submission.OddOrder.BG.Section09.NoncyclicCentralizerUniqueness"
      role := "Generate normalized p-prime subgroups from element centralizers and apply Theorem 9.1(b)"
      status := "complete" },
    { coqFile := "BGsection9.v: cent_uniq_Uniqueness (Corollary 9.2)"
      leanModule := "Submission.OddOrder.BG.Section09.CentralizerUniqueMaximal"
      role := "Propagate uniqueness from a subgroup to a centralizing subgroup with elementary-abelian rank two"
      status := "complete" },
    { coqFile := "BGsection9.v: centralizer-rank support for Corollary 9.3"
      leanModule := "Submission.OddOrder.MathlibSupport.ElementaryAbelianCentralizerRank"
      role := "Find an elementary-abelian rank-two subgroup in the centralizer of a normal rank-two subgroup"
      status := "complete" },
    { coqFile := "BGsection9.v: any_cent_rank3_Uniqueness (Corollary 9.3)"
      leanModule := "Submission.OddOrder.BG.Section09.AnyCentralizerRankThreeUniqueness"
      role := "Transfer uniqueness between rank-three p-subgroups through successive centralizers"
      status := "complete" },
    { coqFile := "BGsection9.v: any_rank3_Fitting_Uniqueness (Corollary 9.4)"
      leanModule := "Submission.OddOrder.BG.Section09.AnyFittingRankThreeUniqueness"
      role := "Make every rank-three p-subgroup unique when a maximal subgroup has rank-three Fitting subgroup"
      status := "complete" },
    { coqFile := "BGsection9.v: maximal-prime support in Lemma 9.5"
      leanModule := "Submission.OddOrder.MathlibSupport.MaximalPrimeDivisor"
      role := "Choose a largest prime divisor for the low Fitting-rank branch"
      status := "complete" },
    { coqFile := "BGsection9.v: first SCN-normalizer block in Lemma 9.5"
      leanModule := "Submission.OddOrder.BG.Section09.SCNRankThreeSylowNormalizer"
      role := "Exclude rank-three Fitting witnesses and force the associated Sylow normalizer into every maximal overgroup of the SCN centralizer"
      status := "complete" },
    { coqFile := "BGsection9.v: nontrivial Sylow-normalizer commutator in Lemma 9.5"
      leanModule := "Submission.OddOrder.BG.Section09.SylowNormalizerCommutator"
      role := "Use Burnside transfer to prove that a nontrivial Sylow subgroup has nontrivial commutator with its normalizer"
      status := "complete" },
    { coqFile := "BGsection9.v: specialized cocyclic-generation support for cDP0"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeAbelianCocyclicCentralizerGeneration"
      role := "Apply the noncyclic/solvable instance of cocyclic centralizer generation needed by Lemma 9.5"
      status := "complete" },
    { coqFile := "BGsection9.v: chief-factor centralization support for cDP0"
      leanModule := "Submission.OddOrder.MathlibSupport.RankTwoNormalCentralizer"
      role := "Centralize a rank-at-most-two normal subgroup by a coprime subgroup of the ambient derived group"
      status := "complete" },
    { coqFile := "BGsection9.v: cDP0 in Lemma 9.5"
      leanModule := "Submission.OddOrder.BG.Section09.SCNFittingPrimeComplementCentralizer"
      role := "Centralize each relevant maximal subgroup's mapped Fitting p-prime core by the Sylow-normalizer commutator"
      status := "complete" },
    { coqFile := "BGsection9.v: unique maximal overgroup of [P, N(P)] in Lemma 9.5"
      leanModule := "Submission.OddOrder.BG.Section09.SCNCommutatorUniqueMaximal"
      role := "Identify the unique maximal overgroup of the normalizer of the Sylow-normalizer commutator"
      status := "complete" },
    { coqFile := "BGsection9.v: SCN_3_Uniqueness (Lemma 9.5)"
      leanModule := "Submission.OddOrder.BG.Section09.SCNRankThreeUniqueness"
      role := "Derive uniqueness of every rank-three SCN subgroup by comparing the commutator-normalizer family at two maximal overgroups"
      status := "complete" },
    { coqFile := "BGsection9.v: rank3_Uniqueness through nonmaxElem2_Uniqueness (Lemma 9.6)"
      leanModule := "Submission.OddOrder.BG.Section09.RankThreeUniqueness"
      role := "Complete Section 9 by propagating rank-three uniqueness through centralizers and treating nonmaximal rank-two elementary-abelian subgroups"
      status := "complete" },
    { coqFile := "BGsection10.v: alpha, beta, sigma predicates and cores"
      leanModule := "Submission.OddOrder.BG.Section10.CorePredicates"
      role := "Define the Section 10 prime predicates and cores and prove their conjugation invariance, containment, normality, and prime-core transport properties"
      status := "complete" },
    { coqFile := "BGsection10.v: beta/alpha/sigma inclusions through core intersection formulas"
      leanModule := "Submission.OddOrder.BG.Section10.MaximalCoreFacts"
      role := "Establish the opening core inclusions, Sylow and prime-support facts, and alpha/beta intersection identities for maximal subgroups"
      status := "complete" },
    { coqFile := "BGsection1.v: subgroup inheritance and Sylow-generation criterion for p-length one"
      leanModule := "Submission.OddOrder.BG.Section01.PLengthOneFunctorial"
      role := "Transport p-length one to subgroups and characterize it through the subgroup generated by p-elements"
      status := "complete" },
    { coqFile := "BGsection3.v/BGappendixC.v: solvable complement conjugacy and quotient-centralizer transport"
      leanModule := "Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy"
      role := "Conjugate solvable complements and identify centralizers after quotienting a coprime normal kernel"
      status := "complete" },
    { coqFile := "solvable/hall.v: coprime_Hall_exists specialized to a prime complement"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeInvariantHall"
      role := "Construct a prime-complement Hall subgroup normalized by a coprime actor"
      status := "complete" },
    { coqFile := "wielandt_fixpoint.v: opening homocyclic decomposition support"
      leanModule := "Submission.OddOrder.MathlibSupport.WielandtFixpoint"
      role := "Develop homocyclic p-groups, invariant Frattini quotients, and the exponent-prime action decomposition"
      status := "complete" },
    { coqFile := "BGsection10.v: sigma_Sylow_trans and sigma_group_trans"
      leanModule := "Submission.OddOrder.BG.Section10.SigmaTransitivity"
      role := "Prove transitivity of maximal-subgroup conjugation on sigma Sylow subgroups and sigma subgroups"
      status := "complete" },
    { coqFile := "BGsection10.v: Malpha_Hall through Msigma_neq1"
      leanModule := "Submission.OddOrder.BG.Section10.AlphaSigmaCore"
      role := "Establish Hall, quotient-rank, nilpotence, derived-subgroup, and nontriviality facts for alpha and sigma cores"
      status := "complete" },
    { coqFile := "BGsection10.v: cent_alpha_compl_uniq and cent_alpha'_uniq"
      leanModule := "Submission.OddOrder.BG.Section10.AlphaComplementCentralizerUniqueness"
      role := "Prove unique maximal overgroups for centralizers of alpha complements"
      status := "complete" },
    { coqFile := "BGsection10.v: sigma-complement derived quotient, centralizer, and rank lemmas"
      leanModule := "Submission.OddOrder.BG.Section10.SigmaComplementRank"
      role := "Control Z-group centralizers and elementary-abelian rank two in sigma complements"
      status := "complete" },
    { coqFile := "BGsection10.v: rank two in normalizers of sigma complements"
      leanModule := "Submission.OddOrder.BG.Section10.SigmaNormalizerRankTwo"
      role := "Promote sigma-complement rank two to maximal normalizers"
      status := "complete" },
    { coqFile := "BGsection10.v: disjointness of nilpotent sigma cores"
      leanModule := "Submission.OddOrder.BG.Section10.SigmaDisjoint"
      role := "Show distinct maximal subgroups have disjoint nilpotent sigma cores"
      status := "complete" },
    { coqFile := "BGsection12.v: tau prime sets and sigma-complement data"
      leanModule := "Submission.OddOrder.BG.Section12.TauDefinitions"
      role := "Define the three tau prime sets and package sigma complements"
      status := "complete" },
    { coqFile := "BGsection12.v: ex_sigma_compl through ex_tau13_compl"
      leanModule := "Submission.OddOrder.BG.Section12.ComplementExistence"
      role := "Construct sigma complements and their tau-one/tau-three Hall factors"
      status := "complete" },
    { coqFile := "BGsection12.v: ex_tau2_compl through sdprod_sigma"
      leanModule := "Submission.OddOrder.BG.Section12.ComplementDecomposition"
      role := "Construct the tau-two factor and split a sigma complement as the required semidirect product"
      status := "complete" },
    { coqFile := "BGsection12.v: ex_tau2Elem through tau2_not_beta"
      leanModule := "Submission.OddOrder.BG.Section12.ComplementElementRank"
      role := "Extract tau-two elements and prove the derived nilpotence and rank consequences"
      status := "complete" },
    { coqFile := "mathlib/mathcomp support"
      leanModule := "Submission.OddOrder.MathlibSupport.Solvability"
      role := "IsSolvable transport and simple-group wrappers"
      status := "complete" },
    { coqFile := "mathcomp solvable/hall.v: solvable Hall existence and containment"
      leanModule := "Submission.OddOrder.MathlibSupport.SolvableHallContainment"
      role := "Construct Hall subgroups containing prescribed prime-set subgroups in finite solvable groups"
      status := "complete" },
    { coqFile := "BGsection13.v: Hall conjugacy transport (lines 621--628)"
      leanModule := "Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport"
      role := "Conjugate Hall subgroups in solvable groups and transport ambient containment and Fitting-cardinality data"
      status := "complete" },
    { coqFile := "BGsection13.v: beta-quotient commutator step (lines 674--689)"
      leanModule := "Submission.OddOrder.MathlibSupport.BetaQuotientCommutator"
      role := "Pull a nilpotent quotient prime core back to force the coprime-action commutator into the second beta core"
      mappedDeclarations := ["commutator_le_betaCore_of_coprime_regular_action"]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section10.BetaHallStructure",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct",
          "Submission.OddOrder.MathlibSupport.PPrimeFactorIntersection" ]
      status := "complete" },
    { coqFile := "BGsection12.v: extraspecial quotient-action step (lines 2111--2143)"
      leanModule := "Submission.OddOrder.MathlibSupport.CoprimeExtraspecialCentralizerGeneration"
      role := "Generate the centralizer of the ambient omega-one center from rank-two fixed-point centralizers of an extraspecial coprime actor"
      mappedDeclarations :=
        [ "le_of_rankTwo_centralizers_of_coprime_extraspecial_action" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section07.SCNRankTwoSubgroup",
          "Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientExponent" ]
      status := "complete" },
    { coqFile := "BGsection2.v: repr_extraspecial_prime_sdprod_cycle (Theorem 2.5), numerical endpoint"
      leanModule := "Submission.OddOrder.BG.Section02.ExtraspecialPrimeSemidirectCycle"
      role := "Assemble the extraspecial cyclic semidirect-product representation argument and derive the adjacent-power divisibility alternative used in BG15"
      mappedDeclarations := ["repr_extraspecial_prime_sdprod_cycle"]
      notes :=
        [ "Approved source decomposition: the Coq theorem's bundled conjunction is split, and the original name is retained here for its numerical divisibility clause, the only clause consumed by the odd-order dependency graph",
          "The source representation fixed-point branch is decomposed into the completed normal-restriction, conjugation-eigenspace, and quasi-homocyclic MathlibSupport modules rather than re-bundled into this downstream interface" ]
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.CentralizerConjugationOrbitCount",
          "Submission.OddOrder.MathlibSupport.CyclicOrbitConjugationRankDrop",
          "Submission.OddOrder.MathlibSupport.CyclicRepresentationQuasiHomocyclic",
          "Submission.OddOrder.MathlibSupport.EndomorphismScalarLine",
          "Submission.OddOrder.MathlibSupport.ExtraspecialIrreducibleDegree",
          "Submission.OddOrder.MathlibSupport.ExtraspecialNormalRestrictionNonmodular",
          "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientEndomorphismBasis",
          "Submission.OddOrder.MathlibSupport.ExtraspecialQuotientFinrank",
          "Submission.OddOrder.MathlibSupport.FixedPointFreeCyclicOrbitRepresentatives",
          "Submission.OddOrder.MathlibSupport.MaschkeNormalConstituent",
          "Submission.OddOrder.MathlibSupport.RepresentationLinearEquiv",
          "Submission.OddOrder.PF.Section02.DadeHypothesis" ]
      status := "complete" } ]

def peterfalviCharacterSupportManifest : List PortEntry :=
  [ { coqFile := "PFsection1.v: class functions and character pairing"
      leanModule := "Submission.OddOrder.PF.Section01.ClassFunction"
      role := "Bundled class functions, restriction, and normalized character orthogonality"
      status := "complete" },
    { coqFile := "PFsection1.v: support and complement class-function spaces"
      leanModule := "Submission.OddOrder.PF.Section01.ClassFunctionSupport"
      role := "Conjugation-stable support decompositions and pairing orthogonality for PF1.3"
      status := "complete" },
    { coqFile := "PFsection1.v: induction and Frobenius reciprocity"
      leanModule := "Submission.OddOrder.PF.Section01.Induction"
      role := "Induced class-function formula and character-level Frobenius reciprocity"
      status := "complete" },
    { coqFile := "PFsection1.v: integral virtual-character lattice"
      leanModule := "Submission.OddOrder.PF.Section01.IntegralLattice"
      role := "Integral coefficient pairing and norm-two signed-difference classification"
      status := "complete" },
    { coqFile := "PFsection1.v: irreducible character indexing and row orthogonality"
      leanModule := "Submission.OddOrder.PF.Section01.IrreducibleCharacter"
      role := "Extensional irreducible characters, orthogonality, linear independence, and finiteness"
      status := "complete" },
    { coqFile := "PFsection1.v: virtual characters"
      leanModule := "Submission.OddOrder.PF.Section01.VirtualCharacter"
      role := "Injective realization of integral irreducible-character combinations and coefficient pairing"
      status := "complete" },
    { coqFile := "PFsection1.v: norm-two virtual-character classification"
      leanModule := "Submission.OddOrder.PF.Section01.VirtualCharacterNormTwo"
      role := "Signed irreducible differences underlying the PF1.4 isometry base"
      status := "complete" },
    { coqFile := "PFsection1.v: equiv_restrict_compl and equiv_restrict_compl_ortho (1.3)"
      leanModule := "Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence"
      role := "Characterize restriction agreement by arbitrary support-basis pairings and derive the orthonormal-family corollary"
      status := "complete" },
    { coqFile := "PFsection1.v: vchar_isometry_base3 and vchar_isometry_base4"
      leanModule := "Submission.OddOrder.PF.Section01.VirtualCharacterIsometry"
      role := "Orient paired norm-two augmentation-zero virtual characters as signed differences with a common endpoint"
      status := "complete" },
    { coqFile := "PFsection1.v: vchar_isometry_base (1.4)"
      leanModule := "Submission.OddOrder.PF.Section01.VirtualCharacterIsometryBase"
      role := "Construct the uniformly signed injective target tuple for a pairing-preserving family of virtual-character differences"
      status := "complete" },
    { coqFile := "PFsection1.v: irreducible-character completeness underlying Brauer permutation"
      leanModule := "Submission.OddOrder.PF.Section01.CharacterCompleteness"
      role := "Prove irreducible characters span all class functions using the center of the group algebra and Maschke semisimplicity"
      status := "complete" },
    { coqFile := "PFsection1.v: Brauer permutation lemma and odd_eq_conj_irr1 (1.1)"
      leanModule := "Submission.OddOrder.PF.Section01.BrauerPermutation"
      role := "Compare row duality and column inversion through the complete character table and deduce the unique self-dual irreducible in odd order, polymorphic in independent group and coefficient universes"
      mappedDeclarations :=
        [ "ClassFunction.onConjClasses", "ClassFunction.conjClassesLinearEquiv",
          "dualPermutationLinear", "inverseClassPermutationLinear",
          "brauerPermutationCardinality", "odd_eq_conj_irr1" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section01.CharacterCompleteness",
          "Submission.OddOrder.PF.Section01.OddConjugateIrreducible" ]
      status := "complete" },
    { coqFile := "PFsection1.v: cfResInd_sum_cfclass, cfnorm_Ind_irr, and cfclass_Ind_cases (1.5)"
      leanModule := "Submission.OddOrder.PF.Section01.NormalSubgroupInduction"
      role := "Develop ambient conjugation orbits and inertia, prove the exact restriction and norm formulas, and establish the equal-or-orthogonal induction dichotomy"
      status := "complete" },
    { coqFile := "PFsection1.v: induced representation compatibility and inertia_Ind_irr (1.5)"
      leanModule := "Submission.OddOrder.PF.Section01.InducedCharacterCompatibility"
      role := "Identify custom class-function induction with Mathlib finite-dimensional induction and promote norm one to actual irreducibility"
      status := "complete" },
    { coqFile := "PFsection1.v: consequences through odd_induced_orthogonal (1.5(d-e))"
      leanModule := "Submission.OddOrder.PF.Section01.NormalSubgroupInductionConsequences"
      role := "Compute induction fibers as normal conjugacy orbits and prove the scaled restriction sum and odd induced orthogonality"
      status := "complete" },
    { coqFile := "PFsection1.v: sub_ker_induce and cfInd_irr_eq1 (1.6(a))"
      leanModule := "Submission.OddOrder.PF.Section01.NormalSubgroupInductionKernel"
      role := "Characterize the kernel of subgroup induction and the equality of an induced irreducible with the induced trivial character"
      status := "complete" },
    { coqFile := "PFsection1.v: restriction and induction constituent kernels (1.6)"
      leanModule := "Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels"
      role := "Relate character constituents by Frobenius reciprocity and transport representation kernels across restriction and induction"
      status := "complete" },
    { coqFile := "PFsection1.v: cfIndMod quotient inflation (1.6(b))"
      leanModule := "Submission.OddOrder.PF.Section01.QuotientInduction"
      role := "Prove that class-function pullback along a finite surjection commutes with induction from a subgroup containing its kernel"
      status := "complete" },
    { coqFile := "PFsection1.v: cfIndQuo quotient descent (1.6(b))"
      leanModule := "Submission.OddOrder.PF.Section01.QuotientDescent"
      role := "Descend class functions through finite surjections and prove that descent commutes with induction"
      status := "complete" },
    { coqFile := "PFsection1.v: literal subgroup-quotient forms of cfIndMod and cfIndQuo (1.6(b))"
      leanModule := "Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter"
      role := "Identify the inducing subgroup quotient with its image in the ambient quotient and expose source-shaped quotient induction statements"
      status := "complete" },
    { coqFile := "PFsection1.v: multiplicity and Hom-space rigidity for cfInd_sum_Inertia (1.7(a))"
      leanModule := "Submission.OddOrder.PF.Section01.InertiaHomRigidity"
      role := "Turn the inertia norm identity into rank-one endomorphism spaces and vanishing cross-Hom spaces"
      status := "complete" },
    { coqFile := "PFsection1.v: cfInd_sum_Inertia (1.7(a))"
      leanModule := "Submission.OddOrder.PF.Section01.InertiaInductionCorrespondence"
      role := "Prove irreducibility, injectivity, exact constituent correspondence, and the weighted inertia-induction expansion"
      status := "complete" },
    { coqFile := "PFsection1.v: quotient-linear twists and uniform inertia multiplicity for cfInd_central_Inertia"
      leanModule := "Submission.OddOrder.PF.Section01.InertiaUniformMultiplicity"
      role := "Develop abelian quotient characters, irreducible twists, restriction multiplicities, and their transitive action on inertia constituents"
      status := "complete" },
    { coqFile := "PFsection1.v: cfInd_central_Inertia (1.7(b))"
      leanModule := "Submission.OddOrder.PF.Section01.CentralInertiaInduction"
      role := "Prove common positive multiplicity, the ambient constituent sum, the constituent count, and the common degree formula"
      status := "complete" },
    { coqFile := "PFsection1.v: cfInd_Hall_central_Inertia (1.7(c))"
      leanModule := "Submission.OddOrder.PF.Section01.HallCentralInertiaAssembly"
      role := "Use invariant Hall-character extension to force multiplicity one and obtain the exact constituent sum, count, and degree formula"
      status := "complete" },
    { coqFile := "PFsection1.v: cfker for an irreducible character"
      leanModule := "Submission.OddOrder.PF.Section01.IrreducibleCharacterTranslationKernel"
      role := "Identify the class-function translation kernel with the kernel of a realizing irreducible representation"
      status := "complete" },
    { coqFile := "PFsection1.v: nonzero restriction constituent support for irr1_bound_quo"
      leanModule := "Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent"
      role := "Select an irreducible constituent of a nonzero realized character and bound its degree by the realizing dimension"
      status := "complete" },
    { coqFile := "PFsection1.v: irr1_bound_quo (1.8)"
      leanModule := "Submission.OddOrder.PF.Section01.IrreducibleDegreeQuotientBound"
      role := "Bound an irreducible degree by an ambient subgroup index times the square root of a central-quotient index"
      status := "complete" },
    { coqFile := "PFsection1.v: extend_coprime_Qn_aut (1.9(a))"
      leanModule := "Submission.OddOrder.PF.Section01.CoprimeCyclotomicAutomorphism"
      role := "Combine coprime cyclotomic automorphisms through the Chinese remainder theorem in a common algebraic closure"
      status := "complete" },
    { coqFile := "PFsection1.v: dvd_restrict_cfAut (1.9(b) intermediate)"
      leanModule := "Submission.OddOrder.PF.Section01.RestrictedCharacterAutomorphism"
      role := "Preserve a cyclotomic automorphism on order-dividing values while fixing ambient coprime-order virtual-character values"
      status := "complete" },
    { coqFile := "PFsection1.v: make_pi_cfAut (1.9(b))"
      leanModule := "Submission.OddOrder.PF.Section01.PiCharacterAutomorphism"
      role := "Construct the uniform power action on selected virtual-character values with the complementary fixed-value property"
      status := "complete" },
    { coqFile := "PFsection1.v: vchar_ker_mod_prim (1.10(a))"
      leanModule := "Submission.OddOrder.PF.Section01.PrimitiveRootCharacterCongruence"
      role := "Prove the primitive-root congruence between a virtual-character value at xy and its value at y when x and y commute, with a backward-compatible algebraically-closed-field variant for later complex-character use"
      status := "complete" },
    { coqFile := "PFsection1.v: int_eqAmod_prime_prim (1.10(b))"
      leanModule := "Submission.OddOrder.PF.Section01.PrimePrimitiveRootDivisibility"
      role := "Deduce prime divisibility of an integer from its algebraic-integer congruence modulo one minus a primitive root, with a backward-compatible algebraically-closed-field variant for later complex-character use"
      status := "complete" },
    { coqFile := "PFsection2.v: partition_cent_rcoset (2.1)"
      leanModule := "Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset"
      role := "Partition a coprime centralizer right coset into subgroup conjugates and compute the number of blocks"
      status := "complete" },
    { coqFile := "PFsection2.v: is_Dade_signalizer and Dade_hypothesis (Definition 2.2)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeHypothesis"
      role := "Define the Dade signalizer and the normality, conjugacy, semidirect-product, and coprimality hypotheses"
      status := "complete" },
    { coqFile := "PFsection2.v: pi-prime core support for the canonical Dade signalizer"
      leanModule := "Submission.OddOrder.MathlibSupport.PiPrimeCore"
      role := "Construct the largest normal ambient subgroup with complementary prime support, prove Hall uniqueness, and transport it through automorphisms"
      status := "complete" },
    { coqFile := "PFsection2.v: normedTI support through cent1_normedTI"
      leanModule := "Submission.OddOrder.MathlibSupport.NormalizedTI"
      role := "Define normalized TI sets, characterize conjugate membership, control cyclic centralizers, and identify the relative normalizer"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade signalizer construction through Dade_normedTI_P (2.3)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeSignalizer"
      role := "Construct the canonical Dade signalizer, prove its semidirect and coprimality properties, and characterize normalized TI sets by trivial signalizers"
      status := "complete" },
    { coqFile := "PFsection2.v: DadeJ and Dade_support1_id (2.4(a))"
      leanModule := "Submission.OddOrder.PF.Section02.DadeSupportConjugation"
      role := "Transport canonical Dade signalizers and their right-coset class supports through conjugation by L"
      status := "complete" },
    { coqFile := "PFsection2.v: piHA and constt support for 2.4(b-c)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeCosetPower"
      role := "Use a CRT exponent to recover the right factor of two conjugate Dade signalizer cosets"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_support1_TI (2.4(b))"
      leanModule := "Submission.OddOrder.PF.Section02.DadeSupportTI"
      role := "Show that intersecting Dade class supports have L-conjugate defining elements"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_cover_TI and norm_Dade_cover (2.4(c))"
      leanModule := "Submission.OddOrder.PF.Section02.DadeCoverTI"
      role := "Prove normalized TI for each Dade signalizer right coset and identify its relative normalizer with the element centralizer"
      status := "complete" },
    { coqFile := "PFsection2.v: generic class-support properties used in Definition 2.5"
      leanModule := "Submission.OddOrder.PF.Section02.ClassSupportProperties"
      role := "Control containment and conjugation stability of the right-conjugacy saturation of a set"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_support through Dade_support_subD1 (Definition 2.5)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeGlobalSupport"
      role := "Construct the global Dade support, exclude the identity, and prove its normal-subset properties"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_subproof through DadeE (Definition 2.5)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeMap"
      role := "Construct the linear Dade map on class functions and evaluate it on every first-support component"
      status := "complete" },
    { coqFile := "PFsection2.v: coefficient-ring transport support for Dade_aut"
      leanModule := "Submission.OddOrder.PF.Section01.ClassFunctionRingHom"
      role := "Apply a ring homomorphism pointwise to class functions as an additive homomorphism"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_id through Dade_id1"
      leanModule := "Submission.OddOrder.PF.Section02.DadeBasicProperties"
      role := "Prove the Dade map support, identity, and identity-value properties"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_aut and Dade_conjC"
      leanModule := "Submission.OddOrder.PF.Section02.DadeAutomorphism"
      role := "Show that the Dade map commutes with coefficient ring endomorphisms and star conjugation"
      status := "complete" },
    { coqFile := "PFsection2.v: cfdot and cfdotEl support for Dade reciprocity"
      leanModule := "Submission.OddOrder.PF.Section01.TwistedCharacterPairing"
      role := "Model MathComp's value-twisted and star class-function pairings and restrict them to the left support"
      status := "complete" },
    { coqFile := "PFsection2.v: normalized-TI partition support for Dade reciprocity"
      leanModule := "Submission.OddOrder.PF.Section02.ClassSupportPartition"
      role := "Decompose sums over finite set partitions and partition a normalized-TI class support by conjugate blocks"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_Ind"
      leanModule := "Submission.OddOrder.PF.Section02.DadeInduction"
      role := "Identify the Dade map with class-function induction under the normalized-TI hypothesis"
      status := "complete" },
    { coqFile := "PFsection2.v: support partitions used in Dade reciprocity"
      leanModule := "Submission.OddOrder.PF.Section02.DadeSupportPartition"
      role := "Partition the global Dade support and A-conjugacy classes into corresponding blocks and compute their cardinalities"
      status := "complete" },
    { coqFile := "PFsection2.v: general_Dade_reciprocity through Dade_isometry"
      leanModule := "Submission.OddOrder.PF.Section02.DadeReciprocity"
      role := "Prove general and restricted Dade reciprocity and the resulting star-pairing isometry"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_set_signalizer through Dade_set_sdprod (2.8)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeSetSignalizer"
      role := "Intersect the signalizers of a nonempty Dade subset and split its generated normalizer as an internal semidirect product"
      status := "complete" },
    { coqFile := "PFsection2.v: semidirect-product projection used by DadeExpansion"
      leanModule := "Submission.OddOrder.MathlibSupport.InternalSemidirectProjection"
      role := "Project an internal semidirect product canonically onto its complement"
      status := "complete" },
    { coqFile := "PFsection2.v: representation-character virtuality support for DadeExpansion"
      leanModule := "Submission.OddOrder.PF.Section01.VirtualCharacterOfFDRep"
      role := "Package the character of every finite-dimensional representation as a virtual character"
      status := "complete" },
    { coqFile := "PFsection2.v: cfMorph support for DadeExpansion"
      leanModule := "Submission.OddOrder.PF.Section01.VirtualCharacterPullback"
      role := "Pull virtual characters back along arbitrary group homomorphisms and identify their realizations"
      status := "complete" },
    { coqFile := "PFsection2.v: cfInd support for DadeExpansion"
      leanModule := "Submission.OddOrder.PF.Section01.VirtualCharacterInduction"
      role := "Induce virtual characters from arbitrary subgroups and identify the realized class function"
      status := "complete" },
    { coqFile := "PFsection2.v: conjugate-subgroup induction support for Dade_Ind_restr_J"
      leanModule := "Submission.OddOrder.PF.Section01.SubgroupInductionConjugation"
      role := "Transport class functions across subgroup conjugation and prove induction invariance"
      status := "complete" },
    { coqFile := "PFsection2.v: calP orbit transversal for Dade expansion"
      leanModule := "Submission.OddOrder.PF.Section02.DadeSubsetOrbits"
      role := "Form conjugation orbits of nonempty Dade subsets and choose representatives with concrete conjugators"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_setU1"
      leanModule := "Submission.OddOrder.PF.Section02.DadeSetCentralizer"
      role := "Identify the signalizer of an inserted subset with a cyclic centralizer inside the smaller signalizer"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_restrm through Dade_restriction_vchar"
      leanModule := "Submission.OddOrder.PF.Section02.DadeExpansionRestriction"
      role := "Restrict class functions and virtual characters through the semidirect projection for every nonempty Dade subset, polymorphic in independent ambient and coefficient universes"
      unresolvedGaps := []
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_Ind_restr_J (2.10.1)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeInductionRestrictionConjugation"
      role := "Prove conjugacy invariance of the induced restriction terms and pass to orbit representatives"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_Ind_expansion (2.10.3)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeInductionExpansion"
      role := "Evaluate every induced restriction by the explicit set-normalizer conjugator count"
      status := "complete" },
    { coqFile := "PFsection2.v: orbit-stabilizer support for Dade_expansion"
      leanModule := "Submission.OddOrder.PF.Section02.DadeExpansionOrbitAveraging"
      role := "Identify the subset stabilizer with the Dade set-normalizer complement and transport its cardinality"
      status := "complete" },
    { coqFile := "PFsection2.v: virtual-character induction support for Dade_vchar"
      leanModule := "Submission.OddOrder.PF.Section02.DadeInducedVirtualCharacter"
      role := "Pull the restricted virtual character to the subgroup copy, induce it, and identify its realization, polymorphic in independent ambient and coefficient universes"
      unresolvedGaps := []
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_expansion (2.10)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeExpansion"
      role := "Express the Dade map as the alternating sum of induced restrictions over nonempty subset orbits"
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_vchar"
      leanModule := "Submission.OddOrder.PF.Section02.DadeVirtualCharacter"
      role := "Realize the integral alternating expansion as an explicit virtual character, polymorphic in independent ambient and coefficient universes"
      unresolvedGaps := []
      status := "complete" },
    { coqFile := "PFsection2.v: Dade_Zisometry"
      leanModule := "Submission.OddOrder.PF.Section02.DadeZIsometry"
      role := "Package star-pairing preservation and the supported virtual-character image of the Dade map, polymorphic in independent ambient and coefficient universes"
      unresolvedGaps := []
      status := "complete" },
    { coqFile := "PFsection2.v: restr_Dade_hyp through restr_DadeE (2.11)"
      leanModule := "Submission.OddOrder.PF.Section02.DadeRestriction"
      role := "Restrict the Dade hypothesis and map to an invariant subset while preserving signalizers, supports, and supported values"
      status := "complete" },
    { coqFile := "PFsection2.v: normedTI_Dade through normedTI_isometry"
      leanModule := "Submission.OddOrder.PF.Section02.NormalizedTIDade"
      role := "Construct the trivial-signalizer Dade hypothesis for normalized TI sets and derive the induction identity and isometry"
      status := "complete" },
    { coqFile := "PFsection3.v: set-valued form of equiv_restrict_compl and equiv_restrict_compl_ortho"
      leanModule := "Submission.OddOrder.PF.Section01.RestrictionComplementEquivalenceSet"
      role := "Generalize Peterfalvi 1.3 from normal subgroups to conjugation- and inverse-stable sets for the cyclic-TI support"
      status := "complete" },
    { coqFile := "PFsection3.v: cyclicTIset and cyclicTI_hypothesis"
      leanModule := "Submission.OddOrder.PF.Section03.InternalDirectProduct"
      role := "Package the fixed internal direct product, its canonical equivalence and projections, and the cyclic normalized-TI hypothesis"
      status := "complete" },
    { coqFile := "PFsection3.v: direct-product irreducible-character support for cyclicTIirr"
      leanModule := "Submission.OddOrder.PF.Section03.DirectProductCharacters"
      role := "Classify irreducible characters of a direct product by external tensor products and commute the classification with coefficient automorphisms"
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section01.BrauerPermutation",
          "Submission.OddOrder.PF.Section01.ClassFunctionRingHom" ]
      status := "complete" },
    { coqFile := "PFsection3.v: cyclicTIirr through cfker_cycTIr"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTICharacters"
      role := "Transport direct-product characters to the internal product and prove indexing, factor, kernel, pairing, swap, and automorphism formulas"
      status := "complete" },
    { coqFile := "PFsection3.v: card_cycTIset and elementary cyclic-TI group consequences"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIGroupFacts"
      role := "Compute the cyclic-TI support cardinality and derive factor cyclicity, coprimality, oddness, nontriviality, and stability"
      status := "complete" },
    { coqFile := "PFsection3.v: cyclic irreducible-character cardinality, linearity, and odd duality support"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicCharacterFacts"
      role := "Show cyclic irreducibles have degree one, count them by group order, and exclude nontrivial self-dual rows in odd order"
      status := "complete" },
    { coqFile := "PFsection3.v: dim_cfun_on_abelian support for cfCycTIbase_basis"
      leanModule := "Submission.OddOrder.PF.Section03.AbelianSupportedClassFunctions"
      role := "Identify supported class functions on a finite abelian group with functions on the support and expose its delta basis and dimension"
      status := "complete" },
    { coqFile := "PFsection3.v: cfun_irr_sum support for cyclicTIiso_exists"
      leanModule := "Submission.OddOrder.PF.Section03.IrreducibleCharacterBasis"
      role := "Package irreducible characters as a basis of all class functions with ordinary character-pairing coordinates"
      status := "complete" },
    { coqFile := "PFsection3.v: ordinary-pairing specialization of normedTI_isometry"
      leanModule := "Submission.OddOrder.PF.Section03.NormalizedTICharacterPairing"
      role := "Prove that normalized-TI induction preserves the inverse-argument character pairing on an inverse-stable support"
      status := "complete" },
    { coqFile := "PFsection3.v: cfCyclicTIset through cfCycTIbase_basis (Peterfalvi 3.4)"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIVirtualBasis"
      role := "Construct the four-term cyclic-TI virtual characters and prove that the nontrivial factor pairs form a basis of the supported class functions"
      status := "complete" },
    { coqFile := "PFsection3.v: cyclic-TI specialization of normalized-TI induction"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIInduction"
      role := "Package induction from the cyclic-TI normalizer, its ordinary pairing and value formulas, and its action on virtual characters"
      status := "complete" },
    { coqFile := "PFsection3.v: Zbeta through beta_modelP in cyclicTIiso_basis_exists"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIBeta"
      role := "Normalize induced four-term virtual characters by the trivial character and prove the exact norm-three grid Gram matrix"
      status := "complete" },
    { coqFile := "PFsection3.v: column_pivot in cyclicTIiso_basis_exists (Peterfalvi 3.5.2--3.5.5)"
      leanModule := "Submission.OddOrder.PF.Section03.ColumnPivot"
      role := "Prove the signed-coordinate column detector for every rectangular norm-three Gram grid, together with its transpose"
      status := "complete" },
    { coqFile := "PFsection3.v: cyclicTIiso_basis_exists"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIIsometryBasis"
      role := "Assemble the signed rectangular orthonormal family selected by the row and column pivots"
      status := "complete" },
    { coqFile := "PFsection3.v: cyclic-TI isometry construction"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIIsometry"
      role := "Extend the signed irreducible rectangle to the class-function and virtual-character isometry"
      status := "complete" },
    { coqFile := "PFsection3.v: pairing exchange after cyclic-TI induction"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIPairingExchange"
      role := "Exchange source and target character pairings across the cyclic-TI isometry"
      status := "complete" },
    { coqFile := "PFsection3.v: cyclicTI_NC coefficient-support API"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTICoefficientSupport"
      role := "Count the nonzero irreducible coefficients detected by the cyclic-TI isometry rectangle"
      status := "complete" },
    { coqFile := "PFsection3.v: small_cycTI_NC and cycTI_NC_minn (Peterfalvi 3.8)"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTISmallSupport"
      role := "Classify small rectangular coefficient support and derive the row-or-column support bound"
      status := "complete" },
    { coqFile := "PFsection3.v: eq_signed_sub_cTIiso"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTISignedDifference"
      role := "Promote supported equality of a norm-two virtual character to a global signed-difference identity"
      status := "complete" },
    { coqFile := "PFsection3.v: eq_in_cycTIiso and cfAut_cycTIiso (Peterfalvi 3.9(a))"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIUniqueness"
      role := "Prove uniqueness of the cyclic-TI isometry and its naturality under coefficient-field automorphisms"
      status := "complete" },
    { coqFile := "PFsection3.v: cycTIiso_aut_exists and Cint_cycTIiso_coprime (Peterfalvi 3.9(b,c))"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTIAutomorphismIntegrality"
      role := "Construct conductor automorphisms of the cyclic-TI isometry and prove coprime integral values"
      status := "complete" },
    { coqFile := "PFsection3.v: cycTIisoC, cycTIiso_irrelC, and cycTIiso_irrel"
      leanModule := "Submission.OddOrder.PF.Section03.CyclicTISymmetry"
      role := "Prove symmetry under swapping the cyclic factors and independence from construction proofs"
      status := "complete" },
    { coqFile := "PFsection4.v: two orthonormal pairs (Peterfalvi 4.1)"
      leanModule := "Submission.OddOrder.PF.Section04.VirtualCharacterPairs"
      role := "Classify two orthonormal virtual-character pairs with equal pairwise differences"
      status := "complete" },
    { coqFile := "PFsection4.v: primeTI_hypothesis and normalized-TI setup"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIHypothesis"
      role := "Package the prime-TI semidirect hypotheses and derive the normalized-TI cyclic specialization"
      status := "complete" },
    { coqFile := "PFsection4.v: quotient setup for the prime-TI kernel"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIQuotient"
      role := "Construct the quotient data and transport the prime-TI structure through it"
      status := "complete" },
    { coqFile := "PFsection4.v: prime-TI irreducible rectangle (Peterfalvi 4.3(b,c))"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTICharacters"
      role := "Induce the cyclic-TI difference basis, select signed irreducible columns, and prove the rectangle specification"
      status := "complete" },
    { coqFile := "PFsection4.v: reduced prime-TI columns after Peterfalvi 4.3(c)"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIReducedCharacters"
      role := "Define the ordinary reduced column sums and their canonical irreducible sequences"
      status := "complete" },
    { coqFile := "PFsection4.v: prTIirr1_mod, prTIsign_aut, and prTIirr_aut after Peterfalvi 4.3(c)"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIDegreeAndAutomorphisms"
      role := "Prove the prime-TI degree congruence and naturality of the rectangle signs and indices under coefficient-field automorphisms"
      status := "complete" },
    { coqFile := "PFsection4.v: reduced-column structure through Peterfalvi 4.5(a)"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIReducedStructure"
      role := "Prove reduced-column pairing, degree, duality, and injectivity formulas and identify their irreducible kernel restrictions"
      mappedDeclarations :=
        [ "cfdot_prTIirr_red", "cfdot_prTIred", "cfnorm_prTIred", "prTIred_neq0",
          "prTIred_1_gt0", "prTIred_inj", "primeTISign_dual", "primeTIIndex_dual",
          "prTIred_aut", "prTIred_not_real", "prTIsign0", "prTIirr00",
          "cfRes_prTIirr_eq0", "prTIirr_1", "prTIred_1", "primeTI_Ires",
          "prTIres_spec", "cfRes_prTIirr", "cfInd_prTIres", "cfRes_prTIred",
          "prTIres_aut", "prTIres_inj", "prTIirr0P" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section01.IrreducibleCharacterTranslationKernel",
          "Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent",
          "Submission.OddOrder.PF.Section04.PrimeTIDegreeAndAutomorphisms" ]
      status := "complete" },
    { coqFile := "PFsection4.v: Peterfalvi 4.5(b) induction alternatives"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIInductionCases"
      role := "Classify kernel and ambient irreducibles into the selected prime-TI rectangle cases and the irreducibly induced alternatives"
      mappedDeclarations := ["prTIres_irr_cases", "prTIred_not_irr", "prTIind_irr_cases"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.PrimeOrderFixedPoint",
          "Submission.OddOrder.PF.Section04.PrimeTIReducedStructure" ]
      status := "complete" },
    { coqFile := "PFsection5.v: induced irreducible families and Beta cluster (lines 57--261)"
      leanModule := "Submission.OddOrder.PF.Section05.InducedIrreducibles"
      role := "Build duplicate-free induced-character families, their integral lattice and support theory, and weighted differences"
      mappedDeclarations :=
        [ "Iirr_ker", "Iirr_kerD", "seqInd", "seqInd_uniq", "seqIndP", "seqInd_on",
          "seqInd_char", "Cnat_seqInd1", "Cint_seqInd1", "seqInd_neq0",
          "seqInd_orthogonal", "seqInd_free", "seqInd_zchar", "nonidentitySet",
          "zcharD1_seqInd", "zcharD1_seqInd_Dade", "dvd_index_seqInd1",
          "sub_seqInd_on", "sub_seqInd_zchar", "seqInd_sub_lin_vchar" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section01.ClassFunctionSupport",
          "Submission.OddOrder.PF.Section01.IrreducibleCharacterTranslationKernel",
          "Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent",
          "Submission.OddOrder.PF.Section01.NormalSubgroupInductionConsequences",
          "Submission.OddOrder.PF.Section01.VirtualCharacterInduction",
          "Submission.OddOrder.PF.Section03.DirectProductCharacters" ]
      status := "complete" },
    { coqFile := "PFsection5.v: sum_Iirr_ker_square through mem_Iirr_ker1 (lines 70--110)"
      leanModule := "Submission.OddOrder.PF.Section05.KernelCounting"
      role := "Count irreducible-character degree squares by normal-subgroup kernels and characterize the trivial-kernel family"
      mappedDeclarations := ["sum_Iirr_ker_square", "sum_Iirr_kerD_square", "mem_Iirr_ker1"]
      unresolvedGaps := []
      directDependencies := ["Submission.OddOrder.PF.Section05.InducedIrreducibles"]
      status := "complete" },
    { coqFile := "PFsection5.v: seqIndT through sum_seqIndC1_square (lines 265--441)"
      leanModule := "Submission.OddOrder.PF.Section05.SeqIndGlobal"
      role := "Develop global induced-character kernel layers, their automorphism and dual closure, odd-order orthogonality, and degree-square identities"
      mappedDeclarations :=
        [ "seqIndS", "seqIndT", "seqInd_subT", "mem_seqIndT", "seqIndT_Ind1",
          "seqIndD", "seqIndDY", "cfAut_seqIndT", "cfAut_seqInd", "mem_seqInd",
          "seqIndC1P", "seqIndC1_filter", "seqIndC1_rem", "seqInd_inverse_mem",
          "seqInd_conjC_subset1", "seqInd_sub_aut_zchar", "seqIndD_nonempty",
          "seqInd_sub", "seqInd_ortho_Ind1", "seqInd_ortho_cfuni", "seqInd_ortho_1",
          "sum_seqIndD_square", "seqInd_conjC_ortho", "seqInd_notReal",
          "seqInd_nontrivial", "seqInd_nontrivial_irr", "sum_seqIndC1_square" ]
      unresolvedGaps :=
        []
      directDependencies := ["Submission.OddOrder.PF.Section05.KernelCounting"]
      status := "complete" },
    { coqFile := "PFsection5.v: coherence foundations (lines 446--633)"
      leanModule := "Submission.OddOrder.PF.Section05.CoherenceBasics"
      role := "Define coherent and subcoherent families and prove the elementary dual, subfamily, permutation, two-character, and pivot constructions"
      mappedDeclarations :=
        [ "ClassFunction.IsVirtual", "cfConjC_closed", "cfConjC_subset",
          "coherent_with", "coherent", "subcoherent", "dual_iso",
          "subgen_coherent", "subset_coherent", "subset_coherent_with", "perm_coherent",
          "dual_coherence", "coherent_seqInd_conjCirr", "pivot_coherence" ]
      unresolvedGaps :=
        []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section01.BrauerPermutation",
          "Submission.OddOrder.PF.Section01.RestrictionComplementEquivalence",
          "Submission.OddOrder.PF.Section04.PrimeTIReducedCharacters",
          "Submission.OddOrder.PF.Section05.InducedIrreducibles" ]
      status := "complete" },
    { coqFile := "PFsection9.v: orthogonal_split support for (9.11.7)--(9.11.8)"
      leanModule := "Submission.OddOrder.PF.Section05.OrthogonalIntegralSpan"
      role := "Split a virtual character into its integral projection onto a finite orthonormal family and an orthogonal virtual remainder"
      mappedDeclarations := ["orthogonal_split_virtual"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section05.CoherenceBasics" ]
      status := "complete" } ]

def frontierManifest : List PortEntry :=
  [ { coqFile := "BGsection3.v: Theorem 3.6"
      leanModule := "Submission.OddOrder.BG.Section03.OddSemidirectZGroupPLength"
      role := "Odd semidirect Z-group centralizer theorem and p-length-one conclusion"
      mappedDeclarations :=
        [ "OddSemidirectZGroupPLengthStatement",
          "oddSemidirectZGroupPLengthStatement_all",
          "odd_sdprod_Zgroup_cent_prime_plength1",
          "odd_sdprod_Zgroup_cent_prime_plength1_of_subgroup" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixC.ElementaryAbelianDecomposition",
          "Submission.OddOrder.BG.Section01.PLengthOneFunctorial",
          "Submission.OddOrder.BG.Section03.OddPrimeSemidirectTheorem",
          "Submission.OddOrder.BG.Section03.FrobeniusPrimeFixedPoint",
          "Submission.OddOrder.BG.Section03.SemidirectProperKernel",
          "Submission.OddOrder.BG.Section04.RankTwoAutomorphismDerived",
          "Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect" ]
      status := "complete" },
    { coqFile := "BGsection10.v: Lemma 10.5(2) through Corollary 10.7(e)"
      leanModule := "Submission.OddOrder.BG.Section10.SigmaElementaryControl"
      role := "Control elementary abelian subgroups and Sylow normalizers at sigma-complement primes"
      mappedDeclarations :=
        [ "sigma'1Elem_sub_p2Elem", "mFT_proper_plength1", "mFT_Sylow_der1",
          "mFT_Sylow_sdprod_commg", "mFT_rank2_Sylow_cprod",
          "mFT_sub_Sylow_trans", "mFT_subnorm_Sylow", "mFT_Sylow_normalS" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section01.PLengthOneFunctorial",
          "Submission.OddOrder.BG.Section03.OddSemidirectZGroupPLength",
          "Submission.OddOrder.BG.Section04.RankTwoCoprimeCommutatorCentralProduct",
          "Submission.OddOrder.BG.Section10.SigmaNormalizerRankTwo",
          "Submission.OddOrder.BG.Section10.SigmaTransitivity",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.PElementCyclic",
          "Submission.OddOrder.MathlibSupport.SolvablePrimeComplement" ]
      status := "complete" },
    { coqFile := "BGsection10.v: Corollary 10.8 through Corollary 10.9(b)"
      leanModule := "Submission.OddOrder.BG.Section10.BetaHallStructure"
      role := "Establish beta-core derived, Hall, quotient-nilpotence, and nonunique-normalizer structure"
      mappedDeclarations :=
        [ "Mbeta_der1", "beta_max_pdiv", "Mbeta_Hall", "Mbeta_Hall_G",
          "Mbeta_quo_nil", "beta'_der1_nil", "beta'_cent_Sylow",
          "nonuniq_norm_Sylow_pprod" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section05.NarrowAutomorphismAndComplement",
          "Submission.OddOrder.BG.Section06.PProdCoprime",
          "Submission.OddOrder.BG.Section09.RankThreeUniqueness",
          "Submission.OddOrder.BG.Section10.SigmaElementaryControl",
          "Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension",
          "Submission.OddOrder.MathlibSupport.FittingNilpotent",
          "Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall",
          "Submission.OddOrder.MathlibSupport.NilpotentCentralizer",
          "Submission.OddOrder.MathlibSupport.NormalPrimeComplementContainment",
          "Submission.OddOrder.MathlibSupport.PiCore",
          "Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow",
          "Submission.OddOrder.MathlibSupport.SolvableHallContainment",
          "Submission.OddOrder.MathlibSupport.SylowIntersection" ]
      status := "complete" },
    { coqFile := "BGsection10.v: Propositions 10.10--10.11 and Lemma 10.12"
      leanModule := "Submission.OddOrder.BG.Section10.SigmaDisjointness"
      role := "Prove sigma-complement structure and disjointness of the alpha and sigma prime sets"
      mappedDeclarations :=
        [ "max_normed_2Elem_signaliser", "sigma'_not_uniq",
          "sub'cent_sigma_rank1", "sub'cent_sigma_cyclic",
          "commG_sigma'_1Elem_cyclic", "alphaPrimes_disjoint_sigmaPrimes",
          "alphaCore_inf_sigmaCore_eq_bot",
          "sigmaPrimes_disjoint_sigmaPrimes_of_nilpotent", "sigma_disjoint" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section10.BetaHallStructure",
          "Submission.OddOrder.BG.Section10.SigmaDisjoint",
          "Submission.OddOrder.BG.Section05.NarrowAutomorphismAndComplement",
          "Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel",
          "Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect",
          "Submission.OddOrder.BG.Section07.NormedTransSuperset",
          "Submission.OddOrder.BG.Section07.PLengthOneNormedConstrained",
          "Submission.OddOrder.BG.Section07.PrimeSetCorePPrime",
          "Submission.OddOrder.MathlibSupport.CoprimeCommutatorIdempotent",
          "Submission.OddOrder.MathlibSupport.Critical",
          "Submission.OddOrder.MathlibSupport.CrossPrimeHomKernel",
          "Submission.OddOrder.MathlibSupport.CyclicNormalizerCommutator",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.FittingSelfCentralizing",
          "Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy",
          "Submission.OddOrder.MathlibSupport.SubgroupCardinality" ]
      status := "complete" },
    { coqFile := "BGsection10.v: Lemma 10.13 and Proposition 10.14"
      leanModule := "Submission.OddOrder.BG.Section10.BasicMaximalStructure"
      role := "Establish the basic rank-two decomposition and beta maximal-subgroup uniqueness consequences"
      mappedDeclarations :=
        [ "RankOneLineIn", "basic_p2maxElem_structure", "beta_not_narrow",
          "beta_noncyclic_uniq", "beta_subnorm_uniq", "beta_norm_sub_mmax" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section05.NarrowCentralizerDirectProduct",
          "Submission.OddOrder.BG.Section05.OmegaUpperCentralMaximal",
          "Submission.OddOrder.BG.Section08.NonPCoreFittingMaximalOvergroup",
          "Submission.OddOrder.BG.Section10.SigmaDisjointness",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport",
          "Submission.OddOrder.MathlibSupport.PGroupNormalizer",
          "Submission.OddOrder.MathlibSupport.PMaxElemSubtype" ]
      status := "complete" },
    { coqFile := "BGsection11.v: exceptional opening setup through exceptional_pmaxElem"
      leanModule := "Submission.OddOrder.BG.Section11.ExceptionalSetup"
      role := "Package the exceptional maximal-subgroup hypothesis and its rank-two and maximal-element consequences"
      mappedDeclarations :=
        [ "exceptional_FTmaximal", "sigma'_Sylow_contra",
          "p_rank_exceptional", "exceptional_pmaxElem" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section10.MaximalCoreFacts",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial",
          "Submission.OddOrder.MathlibSupport.PMaxElem",
          "Submission.OddOrder.MathlibSupport.SubgroupCardinality" ]
      status := "complete" },
    { coqFile := "BGsection11.v: Lemma 11.1 and Corollary 11.2"
      leanModule := "Submission.OddOrder.BG.Section11.ExceptionalTI"
      role := "Prove the exceptional sigma-core TI lemmas and their maximal-subgroup conjugacy transport"
      mappedDeclarations := ["exceptional_TIsigmaJ", "exceptional_TI_MsigmaJ"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section07.NormedConstrainedMeetTrans",
          "Submission.OddOrder.BG.Section07.PLengthOneNormedConstrained",
          "Submission.OddOrder.BG.Section10.SigmaElementaryControl",
          "Submission.OddOrder.BG.Section11.ExceptionalSetup",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension" ]
      status := "complete" },
    { coqFile := "BGsection11.v: Theorem 11.3 and Corollary 11.4"
      leanModule := "Submission.OddOrder.BG.Section11.ExceptionalSigmaNil"
      role := "Prove nilpotence of the exceptional sigma core and uniqueness from nontrivial sigma-core intersection"
      mappedDeclarations := ["exceptional_sigma_nil", "exceptional_sigma_uniq"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel",
          "Submission.OddOrder.BG.Section03.SemidirectProperKernel",
          "Submission.OddOrder.BG.Section10.SigmaDisjoint",
          "Submission.OddOrder.BG.Section11.ExceptionalTI" ]
      status := "complete" },
    { coqFile := "BGsection11.v: Theorem 11.5 through Theorem 11.7"
      leanModule := "Submission.OddOrder.BG.Section11.ExceptionalStructure"
      role := "Derive the exceptional Sylow, omega-one, centralizer, regular-line, and sigma-normal structure"
      mappedDeclarations :=
        [ "exceptional_Sylow_abelian", "exceptional_structure",
          "exceptional_mul_sigma_normal" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section10.BasicMaximalStructure",
          "Submission.OddOrder.BG.Section10.SigmaDisjointness",
          "Submission.OddOrder.BG.Section11.ExceptionalSigmaNil",
          "Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer",
          "Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.OddPGroupOmegaAction",
          "Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal",
          "Submission.OddOrder.MathlibSupport.OmegaOneFunctorial",
          "Submission.OddOrder.MathlibSupport.RepresentationSubgroupRestriction",
          "Submission.OddOrder.MathlibSupport.SolvableHallContainment" ]
      status := "complete" },
    { coqFile := "BGsection12.v: sigma_compl_context through nonuniq_p2Elem_cent_sigma"
      leanModule := "Submission.OddOrder.BG.Section12.SigmaComplementContext"
      role := "Package sigma complements and prove the opening maximal-normalizer and rank-two centralizer consequences"
      mappedDeclarations :=
        [ "SigmaComplementContext", "sigma_compl_context",
          "prime_class_mmax_norm", "mmax_norm_notJ",
          "nonuniq_p2Elem_cent_sigma" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.ComplementElementRank",
          "Submission.OddOrder.BG.Section10.SigmaNormalizerRankTwo",
          "Submission.OddOrder.BG.Section10.SigmaDisjointness",
          "Submission.OddOrder.BG.Section10.SigmaTransitivity",
          "Submission.OddOrder.BG.Section11.ExceptionalStructure",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.NilpotentPrimeCores",
          "Submission.OddOrder.MathlibSupport.PPrimeFactorIntersection" ]
      status := "complete" },
    { coqFile := "BGsection12.v: p2Elem_mmax through tau2_regular"
      leanModule := "Submission.OddOrder.BG.Section12.Tau2Maximal"
      role := "Establish maximal-overgroup, sigma-nilpotence, complement, and regularity contexts for tau-two primes"
      mappedDeclarations :=
        [ "Tau2Context", "Tau2ComplementContext", "Tau2RegularContext",
          "p2Elem_mmax", "tau2_Msigma_nil", "tau2_context",
          "tau2_compl_context", "tau2_regular" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.SigmaComplementContext",
          "Submission.OddOrder.BG.Section09.RankThreeUniqueness",
          "Submission.OddOrder.BG.Section03.SemiregularConjugation",
          "Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer",
          "Submission.OddOrder.MathlibSupport.CoprimeAbelianCocyclicCentralizerGeneration",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.PElementCyclic" ]
      status := "complete" },
    { coqFile := "BGsection12.v: Theorem 12.7, nonabelian_tau2"
      leanModule := "Submission.OddOrder.BG.Section12.NonabelianTau2"
      role := "Derive the five structural consequences of a nonabelian tau-two Sylow subgroup"
      mappedDeclarations := ["NonabelianTau2Conclusion", "nonabelian_tau2"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.Tau2Maximal",
          "Submission.OddOrder.BG.Section10.BasicMaximalStructure",
          "Submission.OddOrder.BG.Section10.SigmaDisjointness",
          "Submission.OddOrder.MathlibSupport.AmbientFitting",
          "Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable",
          "Submission.OddOrder.MathlibSupport.CoprimeElementaryAbelianComplement",
          "Submission.OddOrder.MathlibSupport.FrattiniQuotientAutomorphism",
          "Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall",
          "Submission.OddOrder.PF.Section03.InternalDirectProduct" ]
      status := "complete" },
    { coqFile := "BGsection12.v: abelian tau-two structure and tau-one action (lines 1003--1260)"
      leanModule := "Submission.OddOrder.BG.Section12.AbelianTau2"
      role := "Control abelian tau-two Sylow subgroups, their normalizers, and the tau-one action"
      mappedDeclarations :=
        [ "AbelianTau2SubFittingConclusion", "AbelianTau2Conclusion",
          "Tau1ActTau2Conclusion", "abelian_tau2_sub_Fitting",
          "abelian_tau2", "abelian_tau2_norm_Sylow", "tau1_act_tau2" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect",
          "Submission.OddOrder.BG.Section12.NonabelianTau2" ]
      status := "complete" },
    { coqFile := "BGsection12.v: sigma-complement nilpotence consequences (lines 1316--1462)"
      leanModule := "Submission.OddOrder.BG.Section12.SigmaNilpotent"
      role := "Derive abelianness of nilpotent sigma-prime subgroups and the tau-one/tau-two centralizer consequences"
      mappedDeclarations :=
        [ "sigma'_nil_abelian", "sigmaPrime_complement_nil_abelian",
          "der_mmax_compl_abelian", "tau2_compl_abelian",
          "tau1_cent_tau2Elem_factor", "norm_noncyclic_sigma",
          "cent1_nreg_sigma_uniq" ]
      directDependencies := ["Submission.OddOrder.BG.Section12.AbelianTau2"]
      status := "complete" },
    { coqFile := "BGsection12.v: Theorem 12.12 abelian cyclic-factor branch (split support)"
      leanModule := "Submission.OddOrder.BG.Section12.AbelianTau2CyclicFactor"
      role := "Construct the cyclic last-power factor in the central abelian Sylow branch"
      mappedDeclarations :=
        [ "lastPower_eq_zpowers_of_rankTwo_proper",
          "map_omegaOne_zpowers_eq_zpowers_lastPower",
          "map_omegaOne_zpowers_exponentWitness" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal",
          "Submission.OddOrder.MathlibSupport.SubgroupCardinality",
          "Submission.OddOrder.MathlibSupport.WielandtFixpoint" ]
      status := "complete" },
    { coqFile := "BGsection12.v: Theorem 12.12 coprime cyclic split (split support)"
      leanModule := "Submission.OddOrder.BG.Section12.Tau2CoprimeCyclicSplit"
      role := "Split a rank-two abelian Sylow subgroup into cyclic coprime-action factors"
      mappedDeclarations :=
        [ "centralizerWithin_commutator_eq_bot_of_coprime_abelian_12_12",
          "coprime_abelian_commutator_centralizer_directProduct_12_12",
          "quotient_regular_qgroup_isCyclic_12_12",
          "exists_mixed_subgroup_of_rank_two_coprime_kernel_12_12",
          "cyclic_factors_of_rank_two_coprime_decomposition_12_12",
          "exponent_eq_max_card_of_cyclic_pgroup_direct_product_12_12",
          "exists_coprime_split_witness_12_12" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section04.MetacyclicComplementFactors",
          "Submission.OddOrder.BG.Section12.AbelianTau2",
          "Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree",
          "Submission.OddOrder.MathlibSupport.CoprimeAbelianCocyclicCentralizerGeneration",
          "Submission.OddOrder.MathlibSupport.OmegaOneFunctorial",
          "Submission.OddOrder.PF.Section03.InternalDirectProduct" ]
      status := "complete" },
    { coqFile := "BGsection12.v: Theorem 12.12 selected-Sylow assembly (split support)"
      leanModule := "Submission.OddOrder.BG.Section12.Tau2SelectedSylowAssembly"
      role := "Select cyclic regular factors prime by prime and assemble the Frobenius complement"
      mappedDeclarations :=
        [ "CyclicRegularTau2Factor", "CyclicRegularTau2FactorFamily",
          "exponent_eq_of_selected_sylow_factors_12_12",
          "semiregular_of_cyclic_regular_tau2_factors_12_12",
          "exists_tau2_selected_sylow_assembly_12_12" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.SemiregularConjugation",
          "Submission.OddOrder.BG.Section12.ComplementExistence",
          "Submission.OddOrder.BG.Section12.TauDefinitions",
          "Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal",
          "Submission.OddOrder.MathlibSupport.PElementCyclic",
          "Submission.OddOrder.MathlibSupport.PPrimeCore" ]
      status := "complete" },
    { coqFile := "BGsection12.v: Lemma 12.11 and generalized Theorem 12.12 (lines 1463--2015)"
      leanModule := "Submission.OddOrder.BG.Section12.Tau2NormalizerFTType"
      role := "Control tau-two element normalizers and construct the generalized type-F complement"
      mappedDeclarations := ["primes_norm_tau2Elem", "FTtypeF_complement"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.AbelianTau2",
          "Submission.OddOrder.BG.Section12.AbelianTau2CyclicFactor",
          "Submission.OddOrder.BG.Section12.SigmaNilpotent",
          "Submission.OddOrder.BG.Section12.Tau2CoprimeCyclicSplit",
          "Submission.OddOrder.BG.Section12.Tau2SelectedSylowAssembly",
          "Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal",
          "Submission.OddOrder.MathlibSupport.SCNCentralizer",
          "Submission.OddOrder.MathlibSupport.SylowIntersection" ]
      status := "complete" },
    { coqFile := "BGsection12.v: Theorem 12.13 and Corollary 12.14 (lines 2016--2202)"
      leanModule := "Submission.OddOrder.BG.Section12.NonabelianUniqueness"
      role := "Prove uniqueness of maximal overgroups for nonabelian p-subgroups and derived sigma centralizers"
      mappedDeclarations := ["nonabelian_Uniqueness", "cent_der_sigma_uniq"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section09.RankThreeUniqueness",
          "Submission.OddOrder.BG.Section10.BetaHallStructure",
          "Submission.OddOrder.BG.Section12.Tau2NormalizerFTType",
          "Submission.OddOrder.MathlibSupport.ComplementQuotient",
          "Submission.OddOrder.MathlibSupport.CommutatorSup",
          "Submission.OddOrder.MathlibSupport.CoprimeExtraspecialCentralizerGeneration",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianRankSylowTransport",
          "Submission.OddOrder.MathlibSupport.PGroupNormalizer",
          "Submission.OddOrder.MathlibSupport.PrimeComplement",
          "Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer" ]
      status := "complete" },
    { coqFile := "BGsection12.v: Proposition 12.15 through Lemma 12.19 (lines 2203--2679)"
      leanModule := "Submission.OddOrder.BG.Section12.SigmaEmbedding"
      role := "Embed sigma subgroups and complete complement-centralizer control"
      mappedDeclarations :=
        [ "sigma_subgroup_embedding", "sigma_Jsub", "sigma_compl_embedding",
          "cent_Malpha_reg_tau1", "der_compl_cent_beta'" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section01.CriticalOdd",
          "Submission.OddOrder.BG.Section03.FrobeniusNilpotentKernel",
          "Submission.OddOrder.BG.Section04.OddPGroupRankOne",
          "Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect",
          "Submission.OddOrder.BG.Section10.SigmaDisjointness",
          "Submission.OddOrder.BG.Section12.NonabelianUniqueness",
          "Submission.OddOrder.MathlibSupport.ComplementQuotient",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension",
          "Submission.OddOrder.MathlibSupport.CrossPrimeHomKernel",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.NilpotentCentralizer",
          "Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal",
          "Submission.OddOrder.MathlibSupport.SolvableHallContainment",
          "Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport",
          "Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy",
          "Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer" ]
      status := "complete" },
    { coqFile := "PFsection4.v: prime-Dade restrictions"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIDadeRestrictions"
      role := "Support and kernel restrictions for the prime-Dade reduced columns"
      mappedDeclarations :=
        [ "primeDadeCentralizerSupport", "primeDadeSupport", "signalizerInKernel",
          "set_subset_dadeSet", "dadeMap", "irr_reg_off_ker_0", "prDade_irr_on",
          "prDade_Ind_irr_on", "cfker_prTIres", "prDade_TIres_on",
          "prDade_TIred_on", "prDade_TIsign_eq" ]
      unresolvedGaps :=
        []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section04.PrimeTIInductionCases",
          "Submission.OddOrder.PF.Section02.ClassSupportProperties",
          "Submission.OddOrder.PF.Section02.DadeMap" ]
      status := "complete" },
    { coqFile := "PFsection4.v: prime-Dade coherence"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIDadeCoherence"
      role := "Prime-Dade signed-difference coherence and support disjointness"
      mappedDeclarations :=
        [ "prDade_sub_TIirr_on", "prDade_sub_TIirr", "prDade_supp_disjoint",
          "uniform_prTIred_coherent" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section04.PrimeTIDadeRestrictions",
          "Submission.OddOrder.PF.Section03.CyclicTISignedDifference",
          "Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset",
          "Submission.OddOrder.PF.Section02.DadeZIsometry" ]
      status := "complete" },
    { coqFile := "PFsection4.v: prime-Dade double subtraction"
      leanModule := "Submission.OddOrder.PF.Section04.PrimeTIDadeDoubleSubtraction"
      role := "Two-row subtraction theorem closing the PF4 prime-Dade chain"
      mappedDeclarations := ["prDade_sub2_TIirr"]
      unresolvedGaps := []
      directDependencies := ["Submission.OddOrder.PF.Section04.PrimeTIDadeCoherence"]
      status := "complete" },
    { coqFile := "PFsection5.v: subcoherent construction"
      leanModule := "Submission.OddOrder.PF.Section05.SubcoherentConstruction"
      role := "Construct the prime-Dade reduced image family and its subcoherent decomposition"
      mappedDeclarations :=
        [ "irr_subcoherent", "primeDadeSignedColumn", "primeDadeReducedImageFamily",
          "card_primeDadeSignedColumn", "sum_primeDadeSignedColumn",
          "sum_primeDadeReducedImageFamily", "prDade_subcoherent" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section05.SeqIndGlobal",
          "Submission.OddOrder.PF.Section05.CoherenceBasics",
          "Submission.OddOrder.PF.Section04.PrimeTIDadeCoherence" ]
      status := "complete" },
    { coqFile := "PFsection5.v: subcoherent properties"
      leanModule := "Submission.OddOrder.PF.Section05.SubcoherentProperties"
      role := "Norm, splitting, orthogonality, and coherent-extension properties"
      mappedDeclarations :=
        [ "integralDegree", "normLE", "orthogonalFamilies", "nil_coherent",
          "subset_subcoherent", "subcoherent_split", "subcoherent_norm",
          "coherent_sum_subseq", "mem_coherent_sum_subseq", "coherent_ortho",
          "bridge_coherent", "extend_coherent_with" ]
      unresolvedGaps := []
      directDependencies := ["Submission.OddOrder.PF.Section05.SubcoherentConstruction"]
      status := "complete" },
    { coqFile := "PFsection5.v: coherence extension"
      leanModule := "Submission.OddOrder.PF.Section05.CoherenceExtension"
      role := "Extend coherent families and prove the prime-Dade coherence alternative"
      mappedDeclarations :=
        [ "coherenceDegreeWeight", "coherenceDegreeSum", "extend_coherent",
          "uniform_degree_coherence", "pair_degree_coherence", "coherent_prDade_TIred" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section05.SubcoherentProperties",
          "Submission.OddOrder.PF.Section03.CyclicTIPairingExchange" ]
      status := "complete" },
    { coqFile := "PFsection5.v: Dade automorphism coherence"
      leanModule := "Submission.OddOrder.PF.Section05.DadeAutomorphismCoherence"
      role := "Coherence under coefficient automorphisms and complex conjugation"
      mappedDeclarations :=
        [ "cfConjC", "cfAut_Dade_coherent", "cfConjC_Dade_coherent",
          "Dade_irr_sub_conjC" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section02.DadeVirtualCharacter",
          "Submission.OddOrder.PF.Section05.SeqIndGlobal",
          "Submission.OddOrder.PF.Section05.CoherenceBasics" ]
      status := "complete" },
    { coqFile := "PFsection6.v: opening through Peterfalvi (6.3)"
      leanModule := "Submission.OddOrder.PF.Section06.BoundedSeqIndCoherence"
      role := "Construct bounded sequential-induction coherence from maximal normal and chief-factor reductions"
      mappedDeclarations :=
        [ "exists_linInd", "coherent_seqIndD_bound",
          "bounded_seqIndD_coherence" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer",
          "Submission.OddOrder.MathlibSupport.ChiefFactor",
          "Submission.OddOrder.MathlibSupport.NilpotentNormalCenter",
          "Submission.OddOrder.PF.Section01.IrreducibleDegreeQuotientBound",
          "Submission.OddOrder.PF.Section01.MulCharacterTwist",
          "Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter",
          "Submission.OddOrder.PF.Section05.CoherenceExtension",
          "Submission.OddOrder.PF.Section05.SeqIndGlobal" ]
      status := "complete" },
    { coqFile := "PFsection6.v: Peterfalvi (6.4)--(6.6)"
      leanModule := "Submission.OddOrder.PF.Section06.OddFrobeniusQuotient"
      role := "Analyze the odd Frobenius quotient and derive the chief-factor and sequential-induction coherence alternatives"
      mappedDeclarations :=
        [ "odd_Frobenius_quotient", "non_coherent_chief",
          "seqIndD_irr_coherence" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusBasic",
          "Submission.OddOrder.BG.Section06.PrimeNilDerivedFactor",
          "Submission.OddOrder.MathlibSupport.ChiefFactor",
          "Submission.OddOrder.MathlibSupport.FaithfulQuotientRepresentation",
          "Submission.OddOrder.MathlibSupport.IrreducibleCenterScalar",
          "Submission.OddOrder.MathlibSupport.IrreducibleCharacterDegreeDivides",
          "Submission.OddOrder.MathlibSupport.IrreducibleDegreeIndexBound",
          "Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall",
          "Submission.OddOrder.MathlibSupport.RepresentationIrreducibleComp",
          "Submission.OddOrder.MathlibSupport.Solvability",
          "Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels",
          "Submission.OddOrder.PF.Section06.BoundedSeqIndCoherence" ]
      status := "complete" },
    { coqFile := "PFsection6.v: constant_irr_mod_TI_Sylow (lines 391--565)"
      leanModule := "Submission.OddOrder.PF.Section06.ConstantIrrModTISylow"
      role := "Prove integrality and congruence for irreducible characters constant on a nontrivial central TI layer"
      mappedDeclarations := ["constant_irr_mod_TI_Sylow"]
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixC.NormEquationCharacterBranch",
          "Submission.OddOrder.MathlibSupport.AlgebraicIntegerCongruence",
          "Submission.OddOrder.MathlibSupport.FreeOrbitCardinality",
          "Submission.OddOrder.MathlibSupport.NormalizedTI",
          "Submission.OddOrder.MathlibSupport.PElementCyclic",
          "Submission.OddOrder.PF.Section01.OddConjugateIrreducible",
          "Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset",
          "Submission.OddOrder.PF.Section06.OddFrobeniusQuotient" ]
      status := "complete" },
    { coqFile := "mathcomp inertia.v: Frobenius-kernel irreducible induction"
      leanModule := "Submission.OddOrder.PF.Section06.FrobeniusKernelInduction"
      role := "Show that a nontrivial irreducible character of a Frobenius kernel induces irreducibly"
      mappedDeclarations := ["inertia_Frobenius_ker", "irr_induced_Frobenius_ker"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusBasic",
          "Submission.OddOrder.PF.Section01.InducedCharacterCompatibility",
          "Submission.OddOrder.PF.Section04.PrimeTIInductionCases" ]
      status := "complete" },
    { coqFile := "PFsection7.v: odd_Frobenius_index_ler, dependency-lowered for PF6"
      leanModule := "Submission.OddOrder.PF.Section06.OddFrobeniusIndexBound"
      role := "Bound the complement index in an odd Frobenius decomposition by half the nonidentity kernel size"
      mappedDeclarations := ["odd_Frobenius_index_ler"]
      unresolvedGaps := []
      directDependencies := ["Submission.OddOrder.BG.Section03.FrobeniusBasic"]
      status := "complete" },
    { coqFile := "PFsection6.v: cfcenter_Res and Clifford central-restriction adapters"
      leanModule := "Submission.OddOrder.PF.Section06.CentralRestrictionClifford"
      role := "Expose the central-subgroup restriction and constituent multiplicity corollaries needed in Sibley Case B"
      mappedDeclarations :=
        [ "centralRestrictionMultiplicity",
          "characterPairing_restrict_eq_centralRestrictionMultiplicity",
          "exists_central_restriction_eq_degree_smul",
          "central_restriction_eq_multiplicity_smul_of_induce_pairing_ne_zero" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.IrreducibleCenterScalar",
          "Submission.OddOrder.MathlibSupport.IrreducibleHallExtensionFDRep",
          "Submission.OddOrder.PF.Section01.CharacterCompleteness",
          "Submission.OddOrder.PF.Section01.FiniteAbelianMulCharacters",
          "Submission.OddOrder.PF.Section01.Induction" ]
      status := "complete" },
    { coqFile := "PFsection6.v: Sylow_subnorm and normalized-TI centralizer adapters"
      leanModule := "Submission.OddOrder.PF.Section06.NormalizedTISylowAdapters"
      role := "Promote the Case-A normalized subgroup to an ambient Sylow subgroup and identify its cyclic centralizer"
      mappedDeclarations :=
        [ "normalizedTI_subgroupOf",
          "exists_sylow_subgroupOf_eq_of_normalizedTI_isComplement",
          "centralizerWithin_top_zpowers_eq_frobeniusKernel",
          "centralizerWithin_subgroupOf_zpowers_eq_frobeniusKernel" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusNormalizer",
          "Submission.OddOrder.MathlibSupport.NormalizedTI",
          "Submission.OddOrder.MathlibSupport.PGroupNormalizer",
          "Submission.OddOrder.MathlibSupport.SubgroupCardinality",
          "Submission.OddOrder.PF.Section05.InducedIrreducibles" ]
      status := "complete" },
    { coqFile := "PFsection6.v: Sibley Case A alignment calculation (lines 773--945)"
      leanModule := "Submission.OddOrder.PF.Section06.CaseAAlignment"
      role := "Package the regular-quotient character calculation and original-or-dual coherence alignment used in Sibley Case A"
      mappedDeclarations :=
        [ "regularQuotientDifference",
          "regularQuotientDifference_one",
          "regularQuotientDifference_apply_of_mem_ne_one",
          "regularQuotientDifference_sub_one_of_mem_ne_one",
          "CaseAAlignmentContext", "caseA_alignment" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.OneDimensionalEndomorphism",
          "Submission.OddOrder.MathlibSupport.RepresentationDeterminant",
          "Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter",
          "Submission.OddOrder.PF.Section05.SubcoherentProperties",
          "Submission.OddOrder.PF.Section06.ConstantIrrModTISylow" ]
      status := "complete" },
    { coqFile := "PFsection1.v: make_pi_cfAut specialized to complex values (split support for PFsection6.v)"
      leanModule := "Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism"
      role := "Extend algebraic cyclotomic power automorphisms to the complex numbers without a false algebraic-closure instance"
      mappedDeclarations :=
        [ "exists_complex_algEquiv_extending_algebraicClosure",
          "make_pi_cfAut_complex",
          "exists_prime_cyclic_irreducible_algEquiv" ]
      notes :=
        [ "The new prime-cyclic Galois-transitivity theorem is implemented directly and placeholder-free; the fourth owned-file exact check and root targeted build both pass, and integration review confirms the exact requested signature and expanded direct imports" ]
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.RepresentationDeterminant",
          "Submission.OddOrder.PF.Section01.PiCharacterAutomorphism",
          "Submission.OddOrder.PF.Section03.CyclicCharacterFacts",
          "Submission.OddOrder.PF.Section03.DirectProductCharacters" ]
      status := "complete" },
    { coqFile := "PFsection6.v: Sibley Case B pivot calculation (lines 947--1278)"
      leanModule := "Submission.OddOrder.PF.Section06.CaseBPivot"
      role := "Construct the Case-B original-or-dual pivot and the constituent decomposition used by Sibley coherence"
      mappedDeclarations :=
        [ "sibleyCaseBPivotCandidate", "SibleyCaseBContext",
          "sibley_caseB_pivot" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism",
          "Submission.OddOrder.PF.Section01.ConstituentExpansion",
          "Submission.OddOrder.PF.Section01.PiCharacterAutomorphism",
          "Submission.OddOrder.PF.Section01.VirtualCharacterPullback",
          "Submission.OddOrder.PF.Section03.CyclicCharacterFacts",
          "Submission.OddOrder.PF.Section05.DadeAutomorphismCoherence",
          "Submission.OddOrder.PF.Section05.SubcoherentProperties",
          "Submission.OddOrder.PF.Section06.CentralRestrictionClifford",
          "Submission.OddOrder.PF.Section06.ConstantIrrModTISylow" ]
      status := "complete" },
    { coqFile := "PFsection6.v: Sibley coherence theorem (lines 566--end)"
      leanModule := "Submission.OddOrder.PF.Section06.SibleyCoherence"
      role := "Complete Sibley's coherence theorem by the quotient, Case-A, Case-B, and finite-extension branches"
      mappedDeclarations := ["Sibley_coherence"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusQuotient",
          "Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel",
          "Submission.OddOrder.PF.Section01.CharacterCompleteness",
          "Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport",
          "Submission.OddOrder.PF.Section01.QuotientSubgroupAdapter",
          "Submission.OddOrder.PF.Section01.VirtualCharacterInduction",
          "Submission.OddOrder.PF.Section01.VirtualCharacterPullback",
          "Submission.OddOrder.PF.Section02.DadeRestriction",
          "Submission.OddOrder.PF.Section03.NormalizedTICharacterPairing",
          "Submission.OddOrder.PF.Section04.PrimeTIQuotient",
          "Submission.OddOrder.PF.Section05.CoherenceExtension",
          "Submission.OddOrder.PF.Section05.DadeAutomorphismCoherence",
          "Submission.OddOrder.PF.Section05.SubcoherentConstruction",
          "Submission.OddOrder.PF.Section06.BoundedSeqIndCoherence",
          "Submission.OddOrder.PF.Section06.ConstantIrrModTISylow",
          "Submission.OddOrder.PF.Section06.FrobeniusKernelInduction",
          "Submission.OddOrder.PF.Section06.OddFrobeniusIndexBound",
          "Submission.OddOrder.PF.Section06.OddFrobeniusQuotient",
          "Submission.OddOrder.PF.Section06.CentralRestrictionClifford",
          "Submission.OddOrder.PF.Section06.NormalizedTISylowAdapters",
          "Submission.OddOrder.PF.Section06.CaseAAlignment",
          "Submission.OddOrder.PF.Section06.CaseBPivot" ]
      status := "complete" },
    { coqFile := "PFsection7.v: inverse Dade map through cfnormE_invDade"
      leanModule := "Submission.OddOrder.PF.Section07.InverseDade"
      role := "Construct the inverse Dade map and prove reciprocity, support, and norm identities"
      mappedDeclarations :=
        [ "invDade_subproof", "invDade", "invDade_is_linear", "invDade_on",
          "invDade_cfun1", "invDade_reciprocity", "DadeK",
          "leC_norm_invDade", "leC_cfnorm_invDade_support",
          "cfnormE_invDade" ]
      directDependencies :=
        [ "Submission.OddOrder.PF.Section01.OddConjugateIrreducible",
          "Submission.OddOrder.PF.Section02.DadeReciprocity" ]
      status := "complete" },
    { coqFile := "PFsection7.v: Dade cover and sequential-induction subtraction (lines 167--500)"
      leanModule := "Submission.OddOrder.PF.Section07.DadeCoverSeqInd"
      role := "Prove the Dade-cover inequality and sequential-induction inverse-Dade subtraction formulas"
      mappedDeclarations :=
        [ "Dade_cover_inequality", "IsInvDadeSeqIndSum",
          "invDade_seqInd_sum", "DadeInd1SubLinConclusion",
          "Dade_Ind1_sub_lin" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section02.DadeVirtualCharacter",
          "Submission.OddOrder.PF.Section05.CoherenceBasics",
          "Submission.OddOrder.PF.Section05.SeqIndGlobal",
          "Submission.OddOrder.PF.Section07.InverseDade" ]
      status := "complete" },
    { coqFile := "PFsection7.v: orthogonality and coherent Frobenius partition exclusion (lines 503--834)"
      leanModule := "Submission.OddOrder.PF.Section07.CoherentFrobeniusPartition"
      role := "Combine Dade orthogonality, Frobenius index bounds, and coherence to exclude a full support partition"
      mappedDeclarations :=
        [ "cfReal", "evenCharacterPairing", "cfdot_real_vchar_even",
          "disjoint_Dade_ortho", "disjoint_coherent_ortho",
          "Dade_sub_lin_nonorthogonal",
          "coherentFrobeniusRemainder", "coherent_Frobenius_bound",
          "no_coherent_Frobenius_partition" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusBasic",
          "Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel",
          "Submission.OddOrder.PF.Section04.VirtualCharacterPairs",
          "Submission.OddOrder.PF.Section05.DadeAutomorphismCoherence",
          "Submission.OddOrder.PF.Section06.FrobeniusKernelInduction",
          "Submission.OddOrder.PF.Section06.OddFrobeniusIndexBound",
          "Submission.OddOrder.PF.Section06.SibleyCoherence",
          "Submission.OddOrder.PF.Section07.DadeCoverSeqInd" ]
      status := "complete" } ]

/-! Downstream source ports.  These entries freeze the file decomposition and
public interfaces while their owners prepare source-only drafts behind the
current BG11/PF6 validation frontier. -/
def downstreamManifest : List PortEntry :=
  [ { coqFile := "BGsection13.v: tau-one prime-complement invariant Sylow transfer (split support, lines 711--743)"
      leanModule := "Submission.OddOrder.MathlibSupport.Tau1PrimeComplementInvariantSylow"
      role := "Construct the tau-one ambient prime complement and transfer an invariant Sylow subgroup into the required centralizer-normalizer intersection"
      mappedDeclarations :=
        [ "pPrimeCore_isPrimeComplement_of_not_dvd_commutator",
          "tau1_pPrimeCore_isPrimeComplement",
          "betaCore_le_map_pPrimeCore_of_tau1",
          "betaCore_sup_inf_map_pPrimeCore_eq_of_tau1",
          "exists_rankOne_le_centralizerWithin_inf_normalizer_of_tau1" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section10.BetaHallStructure",
          "Submission.OddOrder.BG.Section12.TauDefinitions",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall",
          "Submission.OddOrder.MathlibSupport.NormalPrimeComplementContainment",
          "Submission.OddOrder.MathlibSupport.PPrimeCoreQuotient" ]
      status := "complete" },
    { coqFile := "BGsection13.v: sigma-core centrality and prime actions (lines 1--575)"
      leanModule := "Submission.OddOrder.BG.Section13.MsigmaCentrality"
      role := "Establish sigma-core intersection centrality and tau-one/tau-three prime-action consequences"
      mappedDeclarations :=
        [ "Msigma_setI_mmax_central", "cent_norm_tau13_mmax",
          "cyclic_primact_Msigma", "tau3_primact_Msigma",
          "cent_tau1Elem_Msigma", "tau1_primact_Msigma",
          "cent_cent_Msigma_tau1_uniq", "tau13_primact_Msigma" ]
      notes :=
        [ "All artificial bridge/result records and public parameters are removed",
          "The three source conjunction conclusions are restored directly and all eight proof kernels are placeholder-free" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.SemiregularConjugation",
          "Submission.OddOrder.BG.Section12.AbelianTau2",
          "Submission.OddOrder.BG.Section12.NonabelianUniqueness",
          "Submission.OddOrder.BG.Section12.SigmaComplementContext",
          "Submission.OddOrder.BG.Section12.SigmaEmbedding",
          "Submission.OddOrder.BG.Section12.Tau2CoprimeCyclicSplit",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableCentralProduct",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension",
          "Submission.OddOrder.MathlibSupport.PPrimeFactorIntersection",
          "Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport" ]
      status := "complete" },
    { coqFile := "BGsection13.v: maximal-intersection asymmetry and sigma partition (lines 576--821)"
      leanModule := "Submission.OddOrder.BG.Section13.SigmaPartition"
      role := "Prove tau-one maximal-intersection asymmetry and the global sigma partition"
      mappedDeclarations := ["tau1_mmaxI_asymmetry", "sigma_partition"]
      notes :=
        [ "All artificial compatibility records and public parameters are removed",
          "Both source theorems are direct and placeholder-free",
          "Exact owned-file checking and the root targeted build both pass; only non-fatal lint warnings remain" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.NonabelianUniqueness",
          "Submission.OddOrder.BG.Section12.SigmaComplementContext",
          "Submission.OddOrder.BG.Section12.SigmaEmbedding",
          "Submission.OddOrder.BG.Section13.MsigmaCentrality",
          "Submission.OddOrder.MathlibSupport.AmbientFitting",
          "Submission.OddOrder.MathlibSupport.BetaQuotientCommutator",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowExtension",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.MathlibSupport.PGroupCenter",
          "Submission.OddOrder.MathlibSupport.PPrimeCoreDerivedHall",
          "Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow",
          "Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport",
          "Submission.OddOrder.MathlibSupport.SylowIntersectionNormalizer",
          "Submission.OddOrder.MathlibSupport.Tau1PrimeComplementInvariantSylow" ]
      status := "complete" },
    { coqFile := "BGsection13.v: tau regularity and nonregularity (lines 822--1119)"
      leanModule := "Submission.OddOrder.BG.Section13.TauRegularity"
      role := "Complete the tau-one/tau-three regularity alternatives used by Section 14"
      mappedDeclarations :=
        [ "tau13_regular", "tau13_nonregular", "tau12_regular",
          "tau13_nonregular_sigma" ]
      notes :=
        [ "All four public source theorems are directly implemented with artificial bridge records and parameters removed",
          "Exact owned-file checking and the root targeted build both pass; only non-fatal lint and deprecation warnings remain" ]
      directDependencies := ["Submission.OddOrder.BG.Section13.SigmaPartition"]
      status := "complete" },
    { coqFile := "BGsection14.v: definitions through kappa/type classification"
      leanModule := "Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes"
      role := "Define sigma decompositions, FT signalizers, kappa primes, complements, and F/P-type maximal families"
      mappedDeclarations :=
        [ "sigma_decomposition", "sigma_length", "sigma_mmax_of",
          "FT_signalizer_base", "FT_signalizer", "sigma_cover", "tau13",
          "kappa", "sigma_kappa", "kappa_complement", "TypeF_maxgroups",
          "TypeP_maxgroups", "TypeP1_maxgroups", "TypeP2_maxgroups",
          "mem_sigma_decomposition", "sigma_mmaxJ", "card_sigma_mmaxJ",
          "sigma_decompositionJ", "sigma_decomposition_constt'",
          "sigma_mmax_exists", "sigma_decomposition_subG",
          "prod_sigma_decomposition", "ell_sigmaJ", "ell_sigma0P",
          "ell_sigma1P", "ell_sigma_le1", "ell1_decomposition", "Msigma_ell1",
          "kappaJ", "kappa_tau13", "kappa_sigma'", "kappa_pi", "rank_kappa",
          "kappa_nonregular", "sigma'_kappa'_facts", "ex_kappa_compl",
          "FtypeP", "PtypeP", "trivg_kappa", "not_sigma_mmax",
          "trivg_kappa_compl", "FtypeJ", "PtypeJ", "P1typeJ", "P2typeJ",
          "notP1type_Msigma_nil" ]
      notes :=
        [ "All source declarations through notP1type_Msigma_nil are bridge-free and placeholder-free",
          "Approved public adaptation: sigma'_kappa'_facts uses S : Sylow p M to internalize the source Sylow premise and returns proposition-valued SigmaKappaPrimeFacts; its omega-cardinality field card Omega1(S) <= p^2 is the finite p-group form of the source logn p #|Omega1(S)| <= 2 clause",
          "The owned-file exact check and root targeted build both pass; only non-fatal lint and deprecation warnings remain" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section10.BasicMaximalStructure",
          "Submission.OddOrder.BG.Section12.Tau2Maximal",
          "Submission.OddOrder.BG.Section13.TauRegularity",
          "Submission.OddOrder.MathlibSupport.OmegaOneCyclicMaximal",
          "Submission.OddOrder.MathlibSupport.PiCore",
          "Submission.OddOrder.MathlibSupport.SolvableHallContainment",
          "Submission.OddOrder.MathlibSupport.SylowConjugateEmbedding" ]
      status := "complete" },
    { coqFile := "BGsection14.v: Proposition 14.2 through Theorem 14.4"
      leanModule := "Submission.OddOrder.BG.Section14.PTypeStructure"
      role := "Package P-type maximal structure, kappa complements, and FT signalizer contexts"
      mappedDeclarations :=
        [ "Ptype_structure", "kappa_compl_context", "pi_of_cent_sigma",
          "FT_signalizer_context" ]
      notes :=
        [ "All four mapped declarations are direct and placeholder-free source-side; the Proposition 14.2(a)--(g) structure proof now includes the coprime normalizer, tau-one centralizer, TI, Sylow uniqueness, sigma-intersection, and P2 sigma/beta phases",
          "Approved public adaptation: the long source conjunction for Ptype_structure is exposed as PTypeStructure := Nonempty (PTypeStructureData M K), with choice-backed named projections preserving the public API; the kappa_compl_context and FT_signalizer_context conjunctions use proposition-valued records with named projections, and Ptype_structure makes the K <= M premise implicit in the source Hall notation explicit",
          "Public helpers Kstar_line_unique and rankOne_normalizer explicitly assume `[Fact p.Prime]`, restoring the prime-indexed semantics of the Coq rank-one-line family `'E^1(K)` that the more general Lean predicate alone does not provide",
          "The tenth owned-file exact check and root targeted build both pass with warnings only; integration review confirmed the four mapped declarations, approved public packaging, direct imports, and clean placeholder scan" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel",
          "Submission.OddOrder.BG.Section12.SigmaEmbedding",
          "Submission.OddOrder.BG.Section13.TauRegularity",
          "Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes",
          "Submission.OddOrder.MathlibSupport.CoprimeHallConjugatorAdjustment",
          "Submission.OddOrder.MathlibSupport.CoprimeSolvableInvariantSylowConjugacy",
          "Submission.OddOrder.MathlibSupport.NormalizedTI",
          "Submission.OddOrder.MathlibSupport.WielandtSolvableFixpoint",
          "Submission.OddOrder.PF.Section03.InternalDirectProduct",
          "Submission.OddOrder.PF.Section05.InducedIrreducibles" ]
      status := "complete" },
    { coqFile := "BGsection14.v: sigma support and disjointness (lines 1008--1314)"
      leanModule := "Submission.OddOrder.BG.Section14.SigmaSupport"
      role := "Prove conjugation, disjointness, cardinality, and dichotomy facts for sigma covers and supports"
      mappedDeclarations :=
        [ "cent1_sub_uniq_sigma_mmax", "FT_signalizer_baseJ",
          "FT_signalizerJ", "sigma_coverJ", "sigma_supportJ",
          "sigma_cover_disjoint", "sigma_support_disjoint",
          "card_class_support_sigma", "sigma_decomposition_dichotomy" ]
      notes :=
        [ "All nine mapped declarations are direct and placeholder-free source-side",
          "sigma_decomposition_dichotomy restores the source exclusive sum; its exhaustive half and compatibility alias are split as sigma_decomposition_dichotomy_or and sigma_decomposition_dichotomy_exclusive",
          "All nine mapped declarations are direct and placeholder-free; the fifth owned-file exact check and root targeted build both pass with warnings only, and integration review confirms the direct imports and intended statements" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes",
          "Submission.OddOrder.BG.Section14.PTypeStructure",
          "Submission.OddOrder.MathlibSupport.SolvableHallConjugacyTransport",
          "Submission.OddOrder.PF.Section02.ClassSupportProperties" ]
      status := "complete" },
    { coqFile := "BGsection14.v: Ptype_embedding through Ptype_trans (lines 1315--1946)"
      leanModule := "Submission.OddOrder.BG.Section14.PTypeEmbedding"
      role := "Establish P-type embedding and conjugacy transitivity"
      mappedDeclarations := ["Ptype_embedding", "P1type_trans", "Ptype_trans"]
      notes :=
        [ "All known invented helpers and placeholders are removed source-side",
          "The normalized-T, outside-disjointness, derived semidirect-product, kappa=tau1, rank-one uniqueness, and transitivity phases are direct Coq drafts",
          "The former unsound P2 support-cardinality shortcut is replaced by the source pairwise-support partition/counting argument",
          "All three mapped declarations are direct and placeholder-free with the approved PTypeEmbedding record packaging; the tenth owned-file exact check and root targeted build both pass with warnings only, and integration review confirms the intended public statements and all eight direct project imports" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.ComplementExistence",
          "Submission.OddOrder.BG.Section14.PTypeStructure",
          "Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes",
          "Submission.OddOrder.BG.Section14.SigmaSupport",
          "Submission.OddOrder.MathlibSupport.NormalizedTI",
          "Submission.OddOrder.PF.Section02.ClassSupportPartition",
          "Submission.OddOrder.PF.Section02.ClassSupportProperties",
          "Submission.OddOrder.PF.Section03.CyclicTIGroupFacts" ]
      status := "complete" },
    { coqFile := "BGsection14.v: partition and signalizers (lines 1947--2510)"
      leanModule := "Submission.OddOrder.BG.Section14.PartitionAndSignalizers"
      role := "Prove the maximal-family partition and final P2/non-F signalizer consequences"
      mappedDeclarations :=
        [ "mFT_partition", "ell_sigma_leq_2", "primes_non_Fitting_Ftype",
          "P2type_signalizer", "non_disjoint_signalizer_Frobenius" ]
      notes :=
        [ "The Lemma 14.11 signalizer calculation is direct source-side, including the tau1 Fitting prime complement, Frattini commutator, tau2 direct-factor, normalized-centralizer, and uniqueness phases",
          "P2type_signalizer explicitly assumes `[Fact r.Prime]`, restoring the prime-Sylow semantics implicit in the Coq binder; IsSylowSubgroupOf alone does not imply primality",
          "All five mapped declarations are direct and placeholder-free with the explicit prime binder; after root refreshed the added InternalSemidirectProjection dependency, the sixth owned-file exact check and root targeted build both pass with warnings only, and integration review confirms all intended statements and nine direct project imports" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.Tau2NormalizerFTType",
          "Submission.OddOrder.BG.Section14.PTypeEmbedding",
          "Submission.OddOrder.BG.Section14.PTypeStructure",
          "Submission.OddOrder.BG.Section14.SigmaDecompositionAndTypes",
          "Submission.OddOrder.BG.Section14.SigmaSupport",
          "Submission.OddOrder.MathlibSupport.InternalSemidirectProjection",
          "Submission.OddOrder.PF.Section02.DadeSupportConjugation",
          "Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset",
          "Submission.OddOrder.PF.Section05.InducedIrreducibles" ]
      status := "complete" },
    { coqFile := "BGsection15.v: Fitting core definitions through Fcore_eq_Msigma (lines 1--206)"
      leanModule := "Submission.OddOrder.BG.Section15.FittingCore"
      role := "Define the join of normal Sylow subgroups and port its normality, Hall, functorial, and sigma-core properties"
      mappedDeclarations :=
        [ "Fitting_core", "Fcore_normal", "Fcore_sub", "Fcore_sub_Fitting",
          "Fcore_nil", "Fcore_max", "Fcore_dprod", "Fcore_pcore_Sylow",
          "p_core_Fcore", "Fcore_Hall", "pcore_Fcore", "Fcore_pcore_Hall",
          "morphim_Fcore", "Fcore_char", "FcoreJ", "injm_Fcore",
          "isom_Fcore", "isog_Fcore", "Fcore_sub_Msigma", "Fcore_eq_Msigma" ]
      notes :=
        [ "All twenty mapped declarations are direct and placeholder-free source-side",
          "The third owned-file exact check passes without output; root integration review confirms all twenty intended declarations and six direct project imports, and the targeted root build passes across 9221 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section14.PartitionAndSignalizers",
          "Submission.OddOrder.MathlibSupport.AmbientFitting",
          "Submission.OddOrder.MathlibSupport.NilpotentPrimeCores",
          "Submission.OddOrder.MathlibSupport.PCoreFunctorial",
          "Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow",
          "Submission.OddOrder.MathlibSupport.SolvableHallContainment" ]
      status := "complete" },
    { coqFile := "BGsection15.v: kappa_structure through Ptype_cyclics (lines 207--938)"
      leanModule := "Submission.OddOrder.BG.Section15.FittingCoreStructure"
      role := "Develop kappa, Fitting, and P-type structure around the genuine normal-Sylow F-core"
      mappedDeclarations :=
        [ "kappa_structure", "Fcore_structure", "cent_Hall_sigma_sdprod",
          "sigma_Hall_tame", "nilpotent_Hall_sigma", "Fitting_structure",
          "Ptype_cyclics" ]
      notes :=
        [ "All seven mapped declarations are direct and placeholder-free, including complete source-level proofs of Corollaries 15.4--15.6",
          "The final owned-file exact check exits 0 with warnings only; root integration review confirms all seven intended declarations and thirty-two direct project imports, and the targeted root build succeeds across 9226 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section15.FittingCore",
          "Submission.OddOrder.BG.Section14.PTypeEmbedding",
          "Submission.OddOrder.BG.Section14.PTypeStructure",
          "Submission.OddOrder.BG.Section14.PartitionAndSignalizers",
          "Submission.OddOrder.BG.Section13.TauRegularity",
          "Submission.OddOrder.BG.Section12.SigmaNilpotent",
          "Submission.OddOrder.BG.Section12.ComplementExistence",
          "Submission.OddOrder.BG.Section04.OddPGroupRankOne",
          "Submission.OddOrder.BG.Section04.RankTwoFittingDerived",
          "Submission.OddOrder.BG.Section05.NarrowAutomorphismAndComplement",
          "Submission.OddOrder.BG.Section03.PrimeActionCommutatorFitting",
          "Submission.OddOrder.BG.Section03.PrimeFrobeniusQuotientKernel",
          "Submission.OddOrder.BG.Section03.FrobeniusSolvableKernel",
          "Submission.OddOrder.BG.Section03.FrobeniusPrimeFixedPoint",
          "Submission.OddOrder.BG.Section06.CoprimeDerivedSemidirect",
          "Submission.OddOrder.MathlibSupport.AmbientFitting",
          "Submission.OddOrder.MathlibSupport.AmbientSylowTransport",
          "Submission.OddOrder.MathlibSupport.CoprimeInvariantHall",
          "Submission.OddOrder.MathlibSupport.CommutatorSup",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelian",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianFunctorial",
          "Submission.OddOrder.MathlibSupport.MinimalNormal",
          "Submission.OddOrder.MathlibSupport.MinimalNormalElementaryAbelian",
          "Submission.OddOrder.MathlibSupport.NilpotentPrimeCoreHall",
          "Submission.OddOrder.MathlibSupport.NormalPrimeComplementContainment",
          "Submission.OddOrder.MathlibSupport.PGroupNormalizer",
          "Submission.OddOrder.MathlibSupport.PSubgroupAbsentPrime",
          "Submission.OddOrder.MathlibSupport.PCoreSelfQuotient",
          "Submission.OddOrder.MathlibSupport.PrimeOrderInvariantSylow",
          "Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy",
          "Submission.OddOrder.MathlibSupport.StableFactor",
          "Submission.OddOrder.PF.Section03.InternalDirectProduct" ]
      status := "complete" },
    { coqFile := "BGsection15.v: Theorem 15.7 and nonTI_Fitting_facts"
      leanModule := "Submission.OddOrder.BG.Section15.NonTIFittingAndSignalizer"
      role := "Prove the non-TI Fitting alternative and expose the shared Section 15 conclusion interfaces"
      mappedDeclarations :=
        [ "nonTI_Fitting_structure", "nonTI_Fitting_facts" ]
      notes :=
        [ "Top-approved decomposition keeps the 1,900-line Theorem 15.7 proof in this module and moves Theorems 15.8 and 15.9 into dependency-ordered phase modules, avoiding repeated elaboration of the large proof",
          "Corrected elementNormalizer15 to the source ftSignalizerBase and restored the distributed nonTI_Fitting_facts alternative",
          "The Type-F branch uses the Frobenius-complement exponent bound, while the Type-P1 branch constructs the faithful coprime rank-two action and invokes repr_extraspecial_prime_sdprod_cycle directly",
          "The final cold exact check exited 0 in 16.6 seconds; root integration review found both mapped statements, the shared result interfaces, eleven direct project imports, and no placeholders, and the targeted build completed successfully with 9229 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section02.ExtraspecialPrimeSemidirectCycle",
          "Submission.OddOrder.BG.Section03.FrobeniusBasic",
          "Submission.OddOrder.BG.Section10.BasicMaximalStructure",
          "Submission.OddOrder.BG.Section12.AbelianTau2",
          "Submission.OddOrder.BG.Section12.NonabelianTau2",
          "Submission.OddOrder.BG.Section12.SigmaEmbedding",
          "Submission.OddOrder.BG.Section14.PTypeEmbedding",
          "Submission.OddOrder.BG.Section14.PartitionAndSignalizers",
          "Submission.OddOrder.BG.Section15.FittingCore",
          "Submission.OddOrder.BG.Section15.FittingCoreStructure",
          "Submission.OddOrder.MathlibSupport.NormalizedTI" ]
      status := "complete" },
    { coqFile := "BGsection15.v: Theorem 15.8 (tau2_P2type_signalizer)"
      leanModule := "Submission.OddOrder.BG.Section15.Tau2P2TypeSignalizer"
      role := "Prove the type-P2 tau2 signalizer conclusion"
      mappedDeclarations := [ "tau2_P2type_signalizer" ]
      notes :=
        [ "Top-approved phase split after the parent target reached 2890 lines and repeated snapshot-assisted checks exceeded eight minutes or exited 137",
          "The public signature explicitly assumes [Fact r.Prime], matching the prime-Sylow semantics of the Coq binder and the already-corrected P2type_signalizer interface",
          "The reconstructed persistent proof is placeholder-free; its final cold exact check exited 0 in 6.11 seconds, root review confirmed the mapped statement and two direct imports, and the targeted build completed successfully with 9230 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section06.PProdCoprime",
          "Submission.OddOrder.BG.Section15.NonTIFittingAndSignalizer" ]
      status := "complete" },
    { coqFile := "BGsection15.v: Theorem 15.9 (nonFtype_signalizer_base)"
      leanModule := "Submission.OddOrder.BG.Section15.NonFTypeSignalizerBase"
      role := "Construct the non-F-type signalizer base and Frobenius complement"
      mappedDeclarations := [ "nonFtype_signalizer_base" ]
      notes :=
        [ "Top-approved phase split makes this theorem downstream of the separate Theorem 15.8 module",
          "The recovered persistent implementation is placeholder-free; its first check-safe cold exact check exited 0 in 7.96 seconds, root review confirmed the mapped statement and single direct import, and the targeted build completed successfully with 9231 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section15.Tau2P2TypeSignalizer" ]
      status := "complete" },
    { coqFile := "BGsection16.v: type and support definitions (lines 1--538, foundation phase)"
      leanModule := "Submission.OddOrder.BG.Section16.TypeDefinitions"
      role := "Define FT types, cores, supports, transversals, and basic core properties"
      mappedDeclarations :=
        [ "is_typeF_inertia", "is_typeF_complement", "of_typeF", "of_typeI",
          "of_typeP", "of_typeII_IV", "of_typeII", "of_typeIII",
          "of_typeIV", "of_typeV", "exists_typeP", "FTtype_spec", "FTtype",
          "FTtype_range", "FTcore", "FTder", "FTsupport1", "FTsupport",
          "FTsupport0", "mmax_transversal", "FTcore_char", "FTcore_normal" ]
      notes :=
        [ "Top-approved decomposition isolates the stable definitions needed by two parallel downstream phases",
          "The fresh 368-line rewrite preserves the mapped and downstream-used public API; its mandatory cold exact check exited 0 in 4.95 seconds, root review found no placeholders or API drift, and the targeted build completed successfully with 9227 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section15.FittingCoreStructure",
          "Submission.OddOrder.MathlibSupport.NormalizedTI",
          "Submission.OddOrder.MathlibSupport.PPrimeCore" ]
      status := "complete" },
    { coqFile := "BGsection16.v: type and support definitions (lines 1--538, classification phase)"
      leanModule := "Submission.OddOrder.BG.Section16.TypeClassification"
      role := "Classify maximal subgroups by numerical FT type and identify the selected core"
      mappedDeclarations := [ "def_FTcore" ]
      notes :=
        [ "Top-approved decomposition permits this phase to proceed independently of support conjugation once TypeDefinitions is complete",
          "The fresh 367-line rewrite preserves every classification and core declaration used downstream; its final cold exact check exited 0 in 6.42 seconds, root integration review found no placeholders or API drift, and the targeted build completed successfully with 9229 jobs" ]
      directDependencies := [ "Submission.OddOrder.BG.Section16.TypeDefinitions" ]
      status := "complete" },
    { coqFile := "BGsection16.v: type and support definitions (lines 1--538, conjugation phase)"
      leanModule := "Submission.OddOrder.BG.Section16.SupportConjugation"
      role := "Transport FT types and supports under conjugation and prove generic support containment"
      mappedDeclarations :=
        [ "FTcoreJ", "FTsupp1J", "FTsuppJ", "FTsupp0J", "FTsupp_sub" ]
      notes :=
        [ "Top-approved decomposition permits this phase to proceed independently of maximal-subgroup classification once TypeDefinitions is complete",
          "The fresh 332-line rewrite preserves every downstream-used conjugation, containment, and normalizer declaration; after the first-validation build exposed three final normalization errors, the reserved owner repaired them, the final cold exact check exited 0 in 4.61 seconds, root review found no placeholders or API drift, and the targeted rebuild completed successfully with 9228 jobs" ]
      directDependencies := [ "Submission.OddOrder.BG.Section16.TypeDefinitions" ]
      status := "complete" },
    { coqFile := "BGsection16.v: type and support definitions through FTsupp_eq1 (lines 1--538, final phase)"
      leanModule := "Submission.OddOrder.BG.Section16.TypesAndSupport"
      role := "Expose the original import facade and prove maximal-subgroup support consequences"
      mappedDeclarations :=
        [ "FTsupp1_sub", "Fcore_sub_FTsupp", "Fitting_sub_FTsupp",
          "FTsupp_eq1" ]
      notes :=
        [ "The original module name is retained as the downstream import facade",
          "The fresh 211-line facade preserves every maximal-support declaration used downstream; its final cold exact check exited 0 in 4.3 seconds, root review found no placeholders or API drift, and the targeted build completed successfully with 9230 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SupportConjugation",
          "Submission.OddOrder.BG.Section16.TypeClassification" ]
      status := "complete" },
    { coqFile := "BGsection16.v: BG summaries A--C (lines 539--789, summary A phase)"
      leanModule := "Submission.OddOrder.BG.Section16.SummaryA"
      role := "Package Bender--Glauberman summary A and the type-selected derived decomposition"
      mappedDeclarations := ["BGsummaryA", "sdprod_FTder"]
      notes :=
        [ "Top-approved decomposition isolates the shared Summary A dependency before parallel Summary B and C phases",
          "The fresh 375-line rewrite preserves the two predicates, full BGSummaryA result structure, and both mapped theorems; its terminal cold exact check exited 0 in 4.82 seconds with no diagnostics, root review found no placeholders or API drift, and the targeted build completed successfully with 9234 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.SigmaNilpotent",
          "Submission.OddOrder.BG.Section14.PTypeEmbedding",
          "Submission.OddOrder.BG.Section14.PTypeStructure",
          "Submission.OddOrder.BG.Section14.PartitionAndSignalizers",
          "Submission.OddOrder.BG.Section15.FittingCoreStructure",
          "Submission.OddOrder.BG.Section15.NonTIFittingAndSignalizer",
          "Submission.OddOrder.BG.Section16.TypesAndSupport",
          "Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.PF.Section03.InternalDirectProduct" ]
      status := "complete" },
    { coqFile := "BGsection16.v: BG summaries A--C (lines 539--789, summary B phase)"
      leanModule := "Submission.OddOrder.BG.Section16.SummaryB"
      role := "Package Bender--Glauberman summary B"
      mappedDeclarations := ["BGsummaryB"]
      notes :=
        [ "Top-approved decomposition allows Summary B and Summary C to proceed independently once Summary A is complete",
          "The fresh 489-line rewrite preserves BGSummaryB and BGsummaryB, contains no placeholders, passed its terminal cold check in 4.86 seconds, passed root integration review, and completed the batched targeted build with 9236 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SummaryA",
          "Submission.OddOrder.MathlibSupport.AbelianPGroupRankThree" ]
      status := "complete" },
    { coqFile := "BGsection16.v: BG summaries A--C (lines 539--789, summary C phase)"
      leanModule := "Submission.OddOrder.BG.Section16.SummaryC"
      role := "Package Bender--Glauberman summary C"
      mappedDeclarations := ["BGsummaryC"]
      notes :=
        [ "Top-approved decomposition allows Summary C and Summary B to proceed independently once Summary A is complete",
          "The dependent Mstar data forces BGSummaryC to live in Type and BGsummaryC to be a noncomputable definition selected from the proved existential; all field names, field types, arguments, result type, and downstream projection syntax are preserved",
          "The fresh 617-line rewrite contains no placeholders, passed its terminal cold check in 5.88 seconds, passed root integration review, and completed the batched targeted build with 9236 jobs" ]
      directDependencies := [ "Submission.OddOrder.BG.Section16.SummaryA" ]
      status := "complete" },
    { coqFile := "BGsection16.v: BG summaries A--C (lines 539--789, import facade)"
      leanModule := "Submission.OddOrder.BG.Section16.SummaryABC"
      role := "Preserve the original downstream import path for summaries A, B, and C"
      mappedDeclarations := []
      notes :=
        [ "The fresh eight-line compatibility facade imports the complete SummaryB and SummaryC phases, passed its cold check and root review, and completed the batched targeted build with 9240 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SummaryB",
          "Submission.OddOrder.BG.Section16.SummaryC" ]
      status := "complete" },
    { coqFile := "BGsection16.v: BG summaries D--E (lines 790--1027)"
      leanModule := "Submission.OddOrder.BG.Section16.SummaryDE"
      role := "Package summary theorems D and E and the maximal transversal specification"
      mappedDeclarations :=
        [ "maximalConjugatesContaining", "BGsummaryD", "mmax_transversalP",
          "BGsummaryE" ]
      notes :=
        [ "Summary D(3) is restored as the ordinary centralizer Hall condition and the fixed-maximal conjugate family",
          "The false ordinary-normalizer equality is removed; elementNormalizer15 is the source signalizer base",
          "The complement witness forces BGSummaryDTypeP2Case, BGSummaryDEscapingCentralizer, and BGSummaryDConclusion to live in Type; BGsummaryD is consequently a noncomputable definition with its arguments, result, fields, and downstream projection syntax preserved",
          "The fresh 734-line rewrite preserves all four mapped declarations and six public result structures, contains no placeholders, passed its final cold check in 4.75 seconds and root integration review, and completed the batched targeted build with 9240 jobs" ]
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.SigmaEmbedding",
          "Submission.OddOrder.BG.Section14.PartitionAndSignalizers",
          "Submission.OddOrder.BG.Section14.SigmaSupport",
          "Submission.OddOrder.BG.Section15.FittingCoreStructure",
          "Submission.OddOrder.BG.Section15.NonFTypeSignalizerBase",
          "Submission.OddOrder.BG.Section16.TypesAndSupport",
          "Submission.OddOrder.MathlibSupport.SolvableHallContainment",
          "Submission.OddOrder.PF.Section02.ClassSupportPartition" ]
      status := "complete" },
    { coqFile := "BGsection16.v: FTtypeP through BGsummaryII (lines 1028--1362, type-spec infrastructure)"
      leanModule := "Submission.OddOrder.BG.Section16.TypeSpecInfrastructure"
      role := "Prove the reusable Hall, complement, and type-P facts used by the numerical type classification"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SummaryABC",
          "Submission.OddOrder.BG.Section16.TypesAndSupport" ]
      status := "complete" },
    { coqFile := "BGsection16.v: FTtypeP through BGsummaryII (lines 1028--1362, Lemma 16.1 phase)"
      leanModule := "Submission.OddOrder.BG.Section16.FTTypeSpec"
      role := "Identify the numerical FT type with the five semantic type predicates"
      mappedDeclarations := ["FTtypeP"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.TypeSpecInfrastructure" ]
      status := "complete" },
    { coqFile := "BGsection16.v: FTtypeP through BGsummaryII (lines 1028--1362, summary I phase)"
      leanModule := "Submission.OddOrder.BG.Section16.SummaryI"
      role := "Package and prove Bender--Glauberman Theorem I"
      mappedDeclarations := ["BGsummaryI"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SummaryABC" ]
      status := "complete" },
    { coqFile := "BGsection16.v: FTtypeP through BGsummaryII (lines 1028--1362, outer-support phase)"
      leanModule := "Submission.OddOrder.BG.Section16.SupportZero"
      role := "Identify the two remaining outer support sets and provide the support calculations for Theorem II"
      mappedDeclarations := ["FTsupp0_type1", "FTsupp0_typeP"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SummaryABC",
          "Submission.OddOrder.BG.Section16.TypeSpecInfrastructure" ]
      status := "complete" },
    { coqFile := "BGsection16.v: FTtypeP through BGsummaryII (lines 1028--1362, summary II phase)"
      leanModule := "Submission.OddOrder.BG.Section16.SummaryII"
      role := "Package and prove the Peterfalvi-facing form of Bender--Glauberman Theorem II"
      mappedDeclarations := ["BGsummaryII"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SummaryABC",
          "Submission.OddOrder.BG.Section16.SummaryDE",
          "Submission.OddOrder.BG.Section16.SummaryI",
          "Submission.OddOrder.BG.Section16.SupportZero" ]
      status := "complete" },
    { coqFile := "BGsection16.v: FTtypeP through BGsummaryII (lines 1028--1362, import facade)"
      leanModule := "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary"
      role := "Preserve the original downstream import path for Lemma 16.1 and summaries I and II"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.FTTypeSpec",
          "Submission.OddOrder.BG.Section16.SummaryI",
          "Submission.OddOrder.BG.Section16.SummaryII",
          "Submission.OddOrder.BG.Section16.SupportZero" ]
      status := "complete" },
    { coqFile := "PFsection8.v: FT contexts and Dade supports (lines 1--707, definitions and transport)"
      leanModule := "Submission.OddOrder.PF.Section08.FTContextDefinitions"
      role := "Define the FT signalizer/support interfaces and reusable conjugation transports"
      mappedDeclarations :=
        [ "FTsignalizer", "FTsupports", "FT_Dade_support",
          "FT_Dade_supportS", "Frobenius_of_typeF" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SummaryABC",
          "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.BG.Section16.TypesAndSupport" ]
      status := "complete" },
    { coqFile := "PFsection8.v: FT contexts and Dade supports (lines 1--707, type-F phase)"
      leanModule := "Submission.OddOrder.PF.Section08.FTTypeFContext"
      role := "Construct the type-F context and the all-type-I alternative"
      mappedDeclarations := ["typeF_context", "all_FTtype1"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section12.Tau2CoprimeCyclicSplit",
          "Submission.OddOrder.MathlibSupport.CoprimeHallConjugatorAdjustment",
          "Submission.OddOrder.PF.Section03.CyclicTIGroupFacts",
          "Submission.OddOrder.PF.Section06.FrobeniusKernelInduction",
          "Submission.OddOrder.PF.Section08.FTContextDefinitions" ]
      status := "complete" },
    { coqFile := "PFsection8.v: FT contexts and Dade supports (lines 1--707, type-P phase)"
      leanModule := "Submission.OddOrder.PF.Section08.FTTypePContext"
      role := "Construct type-P contexts, semantic completions, and the exceptional pair"
      mappedDeclarations :=
        [ "typePF_exclusion", "typeP_context", "FTtypeP_neq1",
          "typeP_pair", "FTtypeP_pair_cases" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.PF.Section08.FTTypeFContext" ]
      status := "complete" },
    { coqFile := "PFsection8.v: FT contexts and Dade supports (lines 1--707, support-facts phase)"
      leanModule := "Submission.OddOrder.PF.Section08.FTSupportFacts"
      role := "Package one-maximal-subgroup core, support, and normalizer facts"
      mappedDeclarations :=
        [ "FTcore_facts", "FTtypeI_II_facts", "FTsupport_facts",
          "norm_FTsupp1", "norm_FTsupp", "norm_FTsupp0" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.PF.Section08.FTTypePContext" ]
      status := "complete" },
    { coqFile := "PFsection8.v: FT contexts and Dade supports (lines 1--707, Dade phase)"
      leanModule := "Submission.OddOrder.PF.Section08.FTDade"
      role := "Construct the four canonical Dade hypotheses, maps, supports, and conjugation laws"
      mappedDeclarations :=
        [ "FTsignalizerJ", "FT_Dade0_hyp", "FT_Dade_hyp",
          "FT_Dade1_hyp", "FT_DadeF_hyp", "def_FTsignalizer0",
          "def_FTsignalizer", "def_FTsignalizer1", "def_FTsignalizerF",
          "FT_DadeE", "FT_Dade1E", "FT_DadeF_E",
          "FT_Dade0_supportE", "FT_Dade_supportE", "FT_Dade1_supportE",
          "FT_DadeF_supportE", "FT_Dade0_supportJ", "FT_Dade1_supportJ",
          "FT_Dade_supportJ" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport",
          "Submission.OddOrder.PF.Section01.OddConjugateIrreducible",
          "Submission.OddOrder.PF.Section02.DadeRestriction",
          "Submission.OddOrder.PF.Section02.PartitionCentralizerRightCoset",
          "Submission.OddOrder.PF.Section08.FTSupportFacts" ]
      status := "complete" },
    { coqFile := "PFsection8.v: FT contexts and Dade supports (lines 1--707, import facade)"
      leanModule := "Submission.OddOrder.PF.Section08.FTTypeContexts"
      role := "Preserve the original downstream import path for the complete FT context and Dade phases"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies := [ "Submission.OddOrder.PF.Section08.FTDade" ]
      status := "complete" },
    { coqFile := "PFsection8.v: FT prime-Dade coherence (lines 708--923)"
      leanModule := "Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence"
      role := "Build the FT type-P prime-Dade hypotheses and coherent reduced base; the coherence and counting declarations follow Section05's universe-0 specialization while the group-theoretic declarations remain universe-polymorphic"
      mappedDeclarations :=
        [ "FT_cyclicTI_hyp", "FTtypeP_pair_witness", "of_typeP_pair",
          "FT_primeTI_hyp", "FTtypeP_supp0_def", "FT_Fcore_prime_Dade_def",
          "FT_prDade_hypF", "FT_core_prime_Dade_def", "FT_prDade_hyp",
          "FTtypeP_coh_base_sig", "FTtypeP_coh_base", "FTtypeP_subcoherent",
          "FTtypeP_base_ortho", "FTtypeP_base_TIred",
          "coherent_ortho_cycTIiso", "FTtypeP_coherent_TIred",
          "size_red_subseq_seqInd_typeP", "FTtypeII_ker_TI" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section05.CoherenceExtension",
          "Submission.OddOrder.PF.Section07.DadeCoverSeqInd",
          "Submission.OddOrder.PF.Section08.FTTypeContexts" ]
      status := "complete" },
    { coqFile := "PFsection8.v: FT support partition and disjointness (lines 924--1132)"
      leanModule := "Submission.OddOrder.PF.Section08.FTSupportPartition"
      role := "Partition the global support and prove Dade-support disjointness"
      mappedDeclarations :=
        [ "FT_Dade_support_partition", "FT_Dade_support_disjoint",
          "FT_Dade1_support_disjoint" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section14.PartitionAndSignalizers",
          "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.PF.Section07.CoherentFrobeniusPartition",
          "Submission.OddOrder.PF.Section08.FTTypeContexts",
          "Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type F-core and complement kernels (lines 1--322, context phase)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeFCoreContext"
      role := "Construct the type-P F-core context and prove the Section 9.2--9.3 structural conclusions"
      mappedDeclarations :=
        [ "Ptype_Fcore_sdprod", "Ptype_Fcore_coprime",
          "Ptype_compl_Frobenius", "typeII_IV_core" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.SemiregularConjugation",
          "Submission.OddOrder.BG.Section03.FrobeniusQuotient",
          "Submission.OddOrder.BG.Section15.FittingCore",
          "Submission.OddOrder.BG.Section15.FittingCoreStructure",
          "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.MathlibSupport.WielandtSolvableFixpoint",
          "Submission.OddOrder.PF.Section03.InternalDirectProduct",
          "Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence",
          "Submission.OddOrder.PF.Section08.FTSupportPartition",
          "Submission.OddOrder.PF.Section08.FTTypeContexts" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type F-core and complement kernels (lines 1--322, kernel and action phase)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeFCoreActions"
      role := "Select the chief-factor and complement kernels and prove their normality and fixed-coset action properties"
      mappedDeclarations :=
        [ "Ptype_Fcore_kernel", "Ptype_Fcore_kernel_exists",
          "Ptype_Fcompl_kernel", "Ptype_Fcore_extensions_normal" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.CharacteristicUnderNormalizer",
          "Submission.OddOrder.MathlibSupport.MinimalNormalExistence",
          "Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy",
          "Submission.OddOrder.MathlibSupport.SubgroupConjugationFactor",
          "Submission.OddOrder.MathlibSupport.SubnormalMaximalNormal",
          "Submission.OddOrder.PF.Section09.PTypeFCoreContext" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type F-core and complement kernels (lines 1--322, factor-facts phase)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeFCoreFactorFacts"
      role := "Prove the elementary chief-factor, joint-minimality, fixed-point, and prime conclusions"
      mappedDeclarations :=
        [ "Ptype_Fcore_factor_facts", "def_Ptype_factor_prime",
          "typeIII_IV_core_prime" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.ElementaryAbelianSup",
          "Submission.OddOrder.PF.Section09.PTypeFCoreActions" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type F-core and complement kernels (lines 1--322, import facade)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeFCoreKernel"
      role := "Preserve the original downstream import path for the complete F-core kernel development"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeFCoreFactorFacts" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type Galois action (lines 323--844, generic action infrastructure)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeActionInfrastructure"
      role := "Develop invariant subgroups, pointwise kernels, direct-product families, and intertwining conjugation"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.InvariantSubgroupAction",
          "Submission.OddOrder.MathlibSupport.RepresentationLinearEquivBasic",
          "Submission.OddOrder.PF.Section09.PTypeFCoreKernel" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type Galois action (lines 323--844, canonical factor action)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeFactorAction"
      role := "Extract the canonical factor action and prove its common structural hypotheses"
      mappedDeclarations := ["typeP_Galois"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeActionInfrastructure" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type Galois action (lines 323--844, non-Galois branch)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisAction"
      role := "Analyze a proper minimal invariant constituent and prove the Pn alternative"
      mappedDeclarations := ["typeP_Galois_Pn"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeFactorAction" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type Galois action (lines 323--844, finite-field branch)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeGaloisFieldAction"
      role := "Construct the finite-field structure and prove the P alternative"
      mappedDeclarations := ["typeP_Galois_P"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixC.FiniteFieldImage",
          "Submission.OddOrder.BG.AppendixC.FiniteFieldUnitDecomposition",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelian",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianRepresentation",
          "Submission.OddOrder.MathlibSupport.ElementaryAbelianSubmodule",
          "Submission.OddOrder.MathlibSupport.IrreducibleCenterCharacter",
          "Submission.OddOrder.MathlibSupport.SchurScalarIrreducible",
          "Submission.OddOrder.PF.Section09.PTypeFactorAction" ]
      status := "complete" },
    { coqFile := "PFsection9.v: P-type Galois action (lines 323--844, import facade)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeGaloisAction"
      role := "Preserve the original downstream import path for both Galois-action branches"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeGaloisFieldAction",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisAction" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, interfaces and arithmetic)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure"
      role := "Define the source-facing character families, subgroup notation, action indices, and lower-bound arithmetic"
      mappedDeclarations :=
        [ "pTypeIrreducibleDegree", "pTypeIsIrreducibleOfDegree",
          "pTypeReducibleLayer", "pTypeIsLinearCharacter", "pTypeIsIndHC",
          "pTypeNonGaloisLowerNumerator", "pTypeNonGaloisLowerDenominator",
          "pTypeNonGaloisDegreeCount", "pTypeHUInMaximal", "pTypeHInDerived",
          "pTypeH0InDerived", "pTypeH0CInDerived",
          "pTypeNonGaloisChiefFactor", "pTypeActionKernelInMaximal",
          "pTypeActionFactorCard", "pTypeNonGaloisIndex",
          "one_lt_pTypeNonGaloisIndex", "pTypeNonGaloisIndex_dvd_prime_pred",
          "pTypeDerived_le_nonGaloisActionKernel", "pTypeLowerDenominator_dvd_of_le",
          "pTypeNonGaloisLowerDenominator_dvd_internal",
          "pTypeDerivedComplementInMaximal",
          "pTypeNonGaloisLowerDenominator_dvd_mapped",
          "pTypeSubgroupConjugationHom" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.PF.Section01.InertiaInductionCorrespondence",
          "Submission.OddOrder.PF.Section01.IrreducibleCharacterTransport",
          "Submission.OddOrder.PF.Section01.MulCharacterTwist",
          "Submission.OddOrder.PF.Section01.NonzeroCharacterConstituent",
          "Submission.OddOrder.PF.Section01.NormalSubgroupConstituentKernels",
          "Submission.OddOrder.PF.Section01.QuotientDescent",
          "Submission.OddOrder.PF.Section03.DirectProductCharacters",
          "Submission.OddOrder.PF.Section05.SeqIndGlobal",
          "Submission.OddOrder.PF.Section08.FTSupportPartition",
          "Submission.OddOrder.PF.Section09.PTypeFCoreKernel",
          "Submission.OddOrder.PF.Section09.PTypeGaloisAction" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, quotient and reducible layer)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer"
      role := "Descend the prime-TI character layer through quotients and prove the canonical reducible-layer count"
      mappedDeclarations := ["pType_nb_redM_H0"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, fixed-degree divisibility)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisFixedDegree"
      role := "Prove clause (a), the fixed-degree divisibility in the non-Galois branch"
      mappedDeclarations := ["pTypeNonGalois_fixed_degree_divisibility"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, coordinate-character core)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore"
      role := "Build scalar direct-product characters, coordinate actions, cardinalities, and the concrete HC subgroups"
      mappedDeclarations :=
        [ "pTypeHCInDerived", "pTypeH0DerivedComplementInDerived",
          "pTypeHCInMaximal" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, HC projection and equivariance)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisHCProjection"
      role := "Identify H/H0 with HC/H0C and prove projection, extension, and conjugation formulas"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, HU character families)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisHUFamily"
      role := "Construct the all-nonprincipal and constant HC/HU families and prove inertia and cardinality facts"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisHCProjection" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, reducible characters)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleCharacters"
      role := "Identify the constant ambient family with the complete reducible layer and establish clause (b)"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisHUFamily",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, clause c)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisClauseC"
      role := "Extract a nonconstant intermediate character and prove the induced irreducible conclusion of clause (c)"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleCharacters" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, selected coordinate)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisSelectedCoordinate"
      role := "Construct the selected H1 coordinate, its HU-to-U projection, and exact inertia subgroup"
      mappedDeclarations :=
        [ "pTypeNonGaloisHUToUProjection",
          "pTypeNonGaloisHUToUProjection_surjective",
          "pTypeNonGaloisHUToUProjection_ker",
          "pTypeNonGaloisH1InertiaInHU",
          "pTypeNonGaloisH1InertiaInHU_index" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, inertia core)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisInertiaCore"
      role := "Construct the selected H-character projections and prove its exact ambient and HU inertia"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisSelectedCoordinate" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, inertia extensions)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisInertiaExtensions"
      role := "Extend the selected character from its exact inertia and construct the quotient-twist family"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisInertiaCore" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, Clifford support)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisCliffordSupport"
      role := "Provide split-universe Clifford correspondence, constituent, irreducibility, and induction-injectivity adapters"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisInertiaExtensions" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, twist induction and lower bounds)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisTwistInduction"
      role := "Induce the twist family through HU and M and prove clause (d)'s divisibility and count bounds"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisCliffordSupport" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, two-coordinate inertia core)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisTwoCoordinateCore"
      role := "Construct the two-coordinate factor character and compute its exact HU inertia"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisInertiaExtensions" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, two-coordinate core character)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisTwoCoordinate"
      role := "Extend and induce the two-coordinate character needed by Peterfalvi (9.11.2)"
      mappedDeclarations := ["pTypeNonGalois_twoCoordinate_coreCharacter"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisTwoCoordinateCore" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, final packaging)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisConclusion"
      role := "Package the four clauses of Peterfalvi (9.8) in the public non-Galois conclusion"
      mappedDeclarations :=
        [ "PTypeNonGaloisCharactersConclusion", "typeP_nonGalois_characters" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisFixedDegree",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisClauseC",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisTwistInduction",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisTwoCoordinate" ]
      status := "complete" },
    { coqFile := "PFsection9.v: non-Galois characters (lines 845--1257, import facade)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeNonGaloisCharacters"
      role := "Preserve the original downstream import path for the decomposed non-Galois character development"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeNonGaloisConclusion" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Galois characters and reducible-core cases (lines 1258--1483, quotient and subgroup infrastructure)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeGaloisInfrastructure"
      role := "Develop quotient inertia, irreducible descent, Clifford splicing, and the canonical derived-subgroup notation"
      mappedDeclarations :=
        [ "ptypeQuotientImage", "pTypeUInDerived", "pTypeCInDerived",
          "pTypeH0CPrimeInDerived", "pTypeH0InDerived_normal",
          "PTypeCoreInduced" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusBasic",
          "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.PF.Section01.InductionTransitivity",
          "Submission.OddOrder.PF.Section04.PrimeTIReducedCharacters",
          "Submission.OddOrder.PF.Section05.SeqIndGlobal",
          "Submission.OddOrder.PF.Section06.FrobeniusKernelInduction",
          "Submission.OddOrder.PF.Section08.FTSupportPartition",
          "Submission.OddOrder.PF.Section09.PTypeGaloisAction",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisInfrastructure" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Galois characters and reducible-core cases (lines 1258--1483, character arithmetic)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeGaloisCharacterArithmetic"
      role := "Prove linearity, induced-degree, nonprincipal-character counting, and geometric-quotient identities"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeGaloisInfrastructure",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Galois characters and reducible-core cases (lines 1258--1483, subgroup and quotient adapters)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeGaloisSubgroupAdapters"
      role := "Build HC/H0C transports, complement/index formulas, commutator bounds, and two-sided quotient algebra"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeGaloisInfrastructure",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Galois characters and reducible-core cases (lines 1258--1483, local Frobenius phase)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeGaloisLocalFrobenius"
      role := "Construct the canonical local Frobenius quotient and force the action kernel to vanish in the all-reducible case"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeGaloisCharacterArithmetic",
          "Submission.OddOrder.PF.Section09.PTypeGaloisSubgroupAdapters" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Galois characters and reducible-core cases (lines 1258--1483, Galois conclusion)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeGaloisConclusion"
      role := "Prove the induced, divisibility, reducible-layer, counting, and type-II conclusions in the Galois branch"
      mappedDeclarations := ["typeP_Galois_characters"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeGaloisLocalFrobenius",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisCliffordSupport",
          "Submission.OddOrder.PF.Section09.PTypeCoreContext" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Galois characters and reducible-core cases (lines 1258--1483, common reducible-core cases)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeReducibleCoreCases"
      role := "Combine the Galois and non-Galois branches into the two public reducible-core alternatives"
      mappedDeclarations :=
        [ "typeP_reducible_core_Ind", "typeP_reducible_core_cases" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeGaloisConclusion",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisConclusion" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Galois characters and reducible-core cases (lines 1258--1483, import facade)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeGaloisCharacters"
      role := "Preserve the original downstream import path for Galois characters and reducible-core cases"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeReducibleCoreCases" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, context and degree bounds)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreContext"
      role := "Define the canonical core families and prove their subgroup, normality, index, degree, and support-layer facts"
      mappedDeclarations :=
        [ "pTypeCoreDerived", "pTypeCoreFitting", "pTypeCoreKernel",
          "pTypeCoreKernelDerivedComplement", "pTypeCoreFamilyOfContext",
          "pTypeCoreFamily" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.SummaryABC",
          "Submission.OddOrder.BG.Section16.SummaryDE",
          "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.BG.Section16.TypesAndSupport",
          "Submission.OddOrder.PF.Section05.CoherenceExtension",
          "Submission.OddOrder.PF.Section05.OrthogonalIntegralSpan",
          "Submission.OddOrder.PF.Section05.SubcoherentProperties",
          "Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence",
          "Submission.OddOrder.PF.Section08.FTSupportPartition",
          "Submission.OddOrder.PF.Section08.FTTypeContexts",
          "Submission.OddOrder.PF.Section09.PTypeFCoreKernel",
          "Submission.OddOrder.PF.Section09.PTypeGaloisAction",
          "Submission.OddOrder.PF.Section09.PTypeGaloisInfrastructure",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisCoordinateCore",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisReducibleLayer" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, slices and rigid bounds)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreBounds"
      role := "Build the degree slices, lower bounds, rigid equality package, and degree-sum estimates of (9.11.1)"
      mappedDeclarations :=
        [ "pTypeCoreDegreeSlice", "pTypeCoreRemainder",
          "pTypeCoreIrreducibleRemainder", "pTypeConjugateSubgroup",
          "pTypeCoreDegreeReal", "pTypeCoreNormReal",
          "pTypeCoreDegreeWeight", "pTypeCoreDegreeSum",
          "pTypeCoreAlphaNorm" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreContext",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisConclusion" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, action-kernel phase)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreActionKernel"
      role := "Prove the rigid action-kernel intersection and numerical conclusions using the two-coordinate character"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreBounds",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisTwoCoordinate" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, gamma norm calculation)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreGamma"
      role := "Construct alpha and gamma and compute translated selected-inertia intersections and the induced-trivial norm"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreActionKernel",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisSelectedCoordinate" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, support and orthogonality)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreSupport"
      role := "Place gamma and the rigid slices in the prime-Dade support and prove the required orthogonality statements"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreGamma" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, virtual pairings)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCorePairing"
      role := "Prove the alpha/beta pairing identities, integrality, zero-norm, Fourier, and orthonormal cardinal bounds"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreSupport" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, Boolean decomposition)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreBoolean"
      role := "Carry out the two-stage integral orthogonal split and eliminate the Boolean coefficient"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCorePairing" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, Galois branch)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreGaloisBranch"
      role := "Close the Galois branch and package the common extension/remainder machinery"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreContext",
          "Submission.OddOrder.PF.Section09.PTypeGaloisConclusion" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, non-Galois dichotomy and counts)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreNonGaloisDichotomy"
      role := "Prove the early-or-rigid dichotomy and the rigid degree-square and remainder bounds"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreActionKernel",
          "Submission.OddOrder.PF.Section09.PTypeNonGaloisConclusion" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, rigid extension)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreNonGaloisExtension"
      role := "Transport alpha through coherence, build the rigid extension input, and prove one non-Galois progress step"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreBoolean",
          "Submission.OddOrder.PF.Section09.PTypeCoreNonGaloisDichotomy",
          "Submission.OddOrder.PF.Section09.PTypeCoreGaloisBranch" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, finite closure and final theorem)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreClosure"
      role := "Run the finite dual-extension recursion and prove the public P-type core coherence theorem"
      mappedDeclarations := ["Ptype_core_coherence"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreGaloisBranch",
          "Submission.OddOrder.PF.Section09.PTypeCoreNonGaloisExtension" ]
      status := "complete" },
    { coqFile := "PFsection9.v: Ptype_core_coherence (lines 1484--2228, import facade)"
      leanModule := "Submission.OddOrder.PF.Section09.PTypeCoreCoherence"
      role := "Preserve the original downstream import path for the decomposed P-type core coherence proof"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreClosure" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, reference and constants)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345Constants"
      role := "Construct the type-345 reference character and numerical constants against the completed P-type core API"
      mappedDeclarations :=
        [ "FTtypeP_ref_irr", "FTtype345_core_prime", "FTtype345_TIirr_degree",
          "FTtype345_TIsign", "FTtype345_ratio", "FTtype345_constants" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeCoreCoherence",
          "Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, support and norm)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345SupportNorm"
      role := "Build the bridge and prove its support, virtuality, Dade transport, and norm identities"
      mappedDeclarations :=
        [ "FTtype345_bridge", "supp_FTtype345_bridge",
          "vchar_FTtype345_bridge", "vchar_Dade_FTtype345_bridge",
          "norm_FTtype345_bridge" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section10.FTType345Constants" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, bridge coherence)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345BridgeCoherence"
      role := "Prove coherence of the transported type-345 bridge family"
      mappedDeclarations := ["FTtype345_bridge_coherence"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section10.FTType345SupportNorm" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, tau-alpha identity)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345TauAlpha"
      role := "Prove the first reduced-column identity for the coherent bridge"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section10.FTType345BridgeCoherence" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, reduced-column sums)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345TauReduced"
      role := "Compute the nonzero and zero reduced-column sums"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section10.FTType345TauAlpha" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, coprime norm)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345Coprime"
      role := "Derive the off-support coprime-order lower bound for the reduced column"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section10.FTType345TauReduced" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, coherence import facade)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345Coherence"
      role := "Preserve the coherence-phase import path after reduced-column decomposition"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section10.FTType345Coprime" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, final contradiction)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345Noncoherence"
      role := "Assemble Suzuki and partner-counting bounds into the final type-345 noncoherence theorem"
      mappedDeclarations := ["FTtype345_noncoherence_main"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section03.CyclicTISymmetry",
          "Submission.OddOrder.PF.Section08.FTContextDefinitions",
          "Submission.OddOrder.PF.Section09.PTypeReducibleCoreCases",
          "Submission.OddOrder.PF.Section10.FTType345Coherence" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-345 bridge and main noncoherence (lines 1--795, import facade)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType345Bridge"
      role := "Preserve the original Section 10 bridge import path after dependency-shaped decomposition"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section10.FTType345Noncoherence" ]
      status := "complete" },
    { coqFile := "PFsection10.v: type-5 exclusion and prime consequences (lines 796--1224)"
      leanModule := "Submission.OddOrder.PF.Section10.FTType5Exclusion"
      role := "Exclude type 5, package type-345 noncoherence, and derive P-pair prime facts"
      mappedDeclarations :=
        [ "FTtype345_Dade_bridge0", "FTtype5_exclusion_main",
          "FTtype345_noncoherence", "FTtype5_exclusion", "FTtypeP_pair_primes",
          "FTtypeP_primes", "FTtypeII_prime_facts" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.BG.Section16.TypesAndSupport",
          "Submission.OddOrder.PF.Section06.OddFrobeniusQuotient",
          "Submission.OddOrder.PF.Section06.SibleyCoherence",
          "Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence",
          "Submission.OddOrder.PF.Section09.PTypeCoreCoherence",
          "Submission.OddOrder.PF.Section09.PTypeFCoreKernel",
          "Submission.OddOrder.PF.Section10.FTType345Bridge" ]
      status := "complete" },
    { coqFile := "PFsection11.v: type-3/4 bounds and F-core kernel (lines 1--542, through Peterfalvi (11.6))"
      leanModule := "Submission.OddOrder.PF.Section11.FTType34BoundsCore"
      role := "Establish the type-3/4 lower bounds, noncoherence, second-derived structure, and factor facts at the universe-0 ambient forced by the canonical coherence API"
      mappedDeclarations :=
        [ "lbound_expn_odd_prime", "FTtype34_noncoherence",
          "bounded_proper_coherent", "FTtype34_der2", "FTtype34_facts" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section15.FittingCoreStructure",
          "Submission.OddOrder.PF.Section06.BoundedSeqIndCoherence",
          "Submission.OddOrder.PF.Section08.FTPrimeDadeCoherence",
          "Submission.OddOrder.PF.Section08.FTSupportPartition",
          "Submission.OddOrder.PF.Section09.PTypeCoreCoherence",
          "Submission.OddOrder.PF.Section10.FTType5Exclusion" ]
      status := "complete" },
    { coqFile := "PFsection11.v: type-3/4 bounds and F-core kernel (lines 1--542, Peterfalvi (11.7))"
      leanModule := "Submission.OddOrder.PF.Section11.FTType34Bounds"
      role := "Use the generic class-two quotient pairing to prove triviality of the type-3/4 F-core kernel while preserving the original downstream import path"
      mappedDeclarations := ["FTtype34_Fcore_kernel_trivial"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.ClassTwoQuotientCommutatorPairing",
          "Submission.OddOrder.PF.Section11.FTType34BoundsCore" ]
      status := "complete" },
    { coqFile := "PFsection11.v: type-3/4 complement kernel and structure (lines 543--1199, common infrastructure)"
      leanModule := "Submission.OddOrder.PF.Section11.FTType34StructureInfrastructure"
      role := "Identify the complement-action kernel and construct the common universe-0 character, coherence, and canonical-action infrastructure for Peterfalvi (11.8)--(11.9)"
      mappedDeclarations := ["Ptype_Fcompl_kernel_cent"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section09.PTypeReducibleCoreCases",
          "Submission.OddOrder.PF.Section11.FTType34Bounds" ]
      status := "complete" },
    { coqFile := "PFsection11.v: type-3/4 complement kernel and structure (lines 543--1199, nonorthogonality coefficients)"
      leanModule := "Submission.OddOrder.PF.Section11.FTType34StructureNonorthogonalityCore"
      role := "Derive the cyclic-TI coefficient, bridge, norm, and tau-alpha identities used by Peterfalvi (11.8)"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section04.PrimeTIDadeDoubleSubtraction",
          "Submission.OddOrder.PF.Section11.FTType34StructureInfrastructure" ]
      status := "complete" },
    { coqFile := "PFsection11.v: type-3/4 complement kernel and structure (lines 543--1199, Peterfalvi (11.8))"
      leanModule := "Submission.OddOrder.PF.Section11.FTType34StructureNonorthogonality"
      role := "Exclude cyclic-TI orthogonality using the raw source-facing local-let statement"
      mappedDeclarations := ["FTtype34_not_ortho_cycTIiso"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section11.FTType34StructureNonorthogonalityCore" ]
      status := "complete" },
    { coqFile := "PFsection11.v: type-3/4 complement kernel and structure (lines 543--1199, Peterfalvi (11.9)(a))"
      leanModule := "Submission.OddOrder.PF.Section11.FTType34StructureProjection"
      role := "Prove the raw-let zero-row projection clause of the final type-3/4 structure theorem"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section11.FTType34StructureNonorthogonality" ]
      status := "complete" },
    { coqFile := "PFsection11.v: type-3/4 complement kernel and structure (lines 543--1199, Peterfalvi (11.9)(b--c))"
      leanModule := "Submission.OddOrder.PF.Section11.FTType34StructureFinalArithmetic"
      role := "Assemble the zero-row projection, p<q, type-three, and canonical Galois clauses into the direct four-conjunct endpoint"
      mappedDeclarations := ["FTtype34_structure"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section11.FTType34StructureProjection" ]
      status := "complete" },
    { coqFile := "PFsection11.v: type-3/4 complement kernel and structure (lines 543--1199, import facade)"
      leanModule := "Submission.OddOrder.PF.Section11.FTType34Structure"
      role := "Preserve the original downstream import path for the decomposed type-3/4 structure development"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section11.FTType34StructureFinalArithmetic" ]
      status := "complete" },
    { coqFile := "PFsection12.v: type-1 coherence and Frobenius analysis (lines 1--555, infrastructure)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1Infrastructure"
      role := "Define the universe-0 type-I character families, source result records, context, and reusable pairing and semidirect-product adapters"
      mappedDeclarations :=
        [ "FTType1FittingIn", "FTType1SeqIndFamily", "FTType1IrrIndex",
          "FTType1IrrFamily", "FTType1CharacterSupport",
          "FTType1FittingDerivedLayer", "FTType1ConstituentFamily",
          "FTType1Orthonormal", "FTType1SeqIndFacts",
          "FTType1IrrIsometryConclusion", "FTType1Context" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusBasic",
          "Submission.OddOrder.BG.Section03.FrobeniusPartition",
          "Submission.OddOrder.BG.Section16.TypeSpecAndFinalSummary",
          "Submission.OddOrder.PF.Section05.SubcoherentProperties",
          "Submission.OddOrder.PF.Section07.CoherentFrobeniusPartition",
          "Submission.OddOrder.PF.Section07.InverseDade",
          "Submission.OddOrder.PF.Section08.FTSupportPartition",
          "Submission.OddOrder.PF.Section11.FTType34Structure" ]
      status := "complete" },
    { coqFile := "PFsection12.v: type-1 coherence and Frobenius analysis (lines 1--555, partition and isometry)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1Partition"
      role := "Construct the universe-0 reference irreducibles, constituent partition, sequential-induction facts, isometry, and initial subcoherence"
      mappedDeclarations :=
        [ "FTtype1_ref_irr", "FTtype1_irrP", "FTtype1_irr_partition",
          "FTtype1_seqInd_facts", "FTtype1_irr_isometry",
          "FTtype1_irr_subcoherent" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section12.FTType1Infrastructure" ]
      status := "complete" },
    { coqFile := "PFsection12.v: type-1 coherence and Frobenius analysis (lines 1--555, subcoherence)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1Subcoherence"
      role := "Complete the universe-0 paired irreducible targets and canonical type-I subcoherence package"
      mappedDeclarations := ["FTtype1_subcoherent"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section12.FTType1Partition" ]
      status := "complete" },
    { coqFile := "PFsection12.v: type-1 coherence and Frobenius analysis (lines 1--555, sequential orthogonality)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1SequentialOrthogonality"
      role := "Prove orthogonality of the universe-0 canonical sequential-induction image families"
      mappedDeclarations := ["FTtype1_seqInd_ortho"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section12.FTType1Subcoherence" ]
      status := "complete" },
    { coqFile := "PFsection12.v: type-1 coherence and Frobenius analysis (lines 1--555, constituent constants)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1ConstituentConstants"
      role := "Prove universe-0 constituent restriction, Fourier, and inverse-Dade constancy in Peterfalvi (12.4)--(12.5)"
      mappedDeclarations :=
        [ "FTtype1_ortho_constant", "FtypeI_invDade_ortho_constant" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section12.FTType1SequentialOrthogonality" ]
      status := "complete" },
    { coqFile := "PFsection12.v: type-1 coherence and Frobenius analysis (lines 1--555, Frobenius specialization)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1Frobenius"
      role := "Specialize the universe-0 type-I development to Frobenius maximals and construct the final coherence alternative"
      mappedDeclarations :=
        [ "FT_Frobenius_type1", "FTsupp_Frobenius",
          "FT_Frobenius_coherence" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section12.FTType1ConstituentConstants" ]
      status := "complete" },
    { coqFile := "PFsection12.v: type-1 coherence and Frobenius analysis (lines 1--555, import facade)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1Coherence"
      role := "Preserve the original downstream import path for the decomposed type-I coherence and Frobenius development"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section12.FTType1Frobenius" ]
      status := "complete" },
    { coqFile := "PFsection12.v: non-Frobenius type-1 contradiction (lines 556--1276, Peterfalvi (12.9) witness)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1NonFrobeniusWitness"
      role := "Construct the universe-0 rank-two witness for the non-Frobenius type-I contradiction"
      mappedDeclarations := ["non_Frobenius_FTtype1_witness"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.MathlibSupport.AbelianPGroupRankThreeConverse",
          "Submission.OddOrder.MathlibSupport.CoprimeAbelianCentralizerGenerationSolvable",
          "Submission.OddOrder.MathlibSupport.OmegaOne",
          "Submission.OddOrder.MathlibSupport.SolvableHallContainment",
          "Submission.OddOrder.PF.Section08.FTSupportPartition",
          "Submission.OddOrder.PF.Section12.FTType1Coherence" ]
      status := "complete" },
    { coqFile := "PFsection12.v: non-Frobenius type-1 contradiction (lines 556--1276, group-theoretic bridge)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1NonFrobeniusGroupBridge"
      role := "Derive the second-Fitting containment and non-Frobenius maximal-subgroup bridge used by the character contradiction"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section02.OddGL2CrossCharacteristicAbelian",
          "Submission.OddOrder.BG.Section04.RankTwoPGroupAutomorphismPrimes",
          "Submission.OddOrder.MathlibSupport.WielandtSolvableFixpoint",
          "Submission.OddOrder.PF.Section09.PTypeGaloisSubgroupAdapters",
          "Submission.OddOrder.PF.Section12.FTType1NonFrobeniusWitness" ]
      status := "complete" },
    { coqFile := "PFsection12.v: non-Frobenius type-1 contradiction (lines 556--1276, character contradiction)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1NonFrobeniusCharacterContradiction"
      role := "Use the group bridge and primitive-root congruence to derive the witness and global non-Frobenius contradictions"
      mappedDeclarations :=
        [ "FTtype1_nonFrobenius_witness_contradiction",
          "FTtype1_nonFrobenius_contradiction" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section01.PrimitiveRootCharacterCongruence",
          "Submission.OddOrder.PF.Section01.PrimePrimitiveRootDivisibility",
          "Submission.OddOrder.PF.Section12.FTType1NonFrobeniusGroupBridge" ]
      status := "complete" },
    { coqFile := "PFsection12.v: non-Frobenius type-1 contradiction (lines 556--1276, import facade)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1NonFrobenius"
      role := "Preserve the original downstream import path for the decomposed non-Frobenius contradiction"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section12.FTType1NonFrobeniusCharacterContradiction" ]
      status := "complete" },
    { coqFile := "PFsection12.v: type-1 exclusion and global alternative (lines 1277--1362)"
      leanModule := "Submission.OddOrder.PF.Section12.FTType1Exclusion"
      role := "At the universe-0 ambient boundary, force type-1 maximals to be Frobenius and exclude the all-type-1 case"
      mappedDeclarations := ["FTtype1_Frobenius", "not_all_FTtype1"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section04.OddPGroupRankOne",
          "Submission.OddOrder.PF.Section12.FTType1NonFrobenius" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type setup and coherence (lines 1--594)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePSetupAndCoherence"
      role := "At the universe-0 ambient boundary, set up Fitting-induced characters and establish the type-P coherent family"
      mappedDeclarations :=
        [ "irr_Ind_Fitting", "Ptype_factor_prime",
          "Ptype_Fcore_kernel_trivial", "Ptype_Fcompl_kernel_cent",
          "FTtypeP_facts", "FTseqInd_TIred", "FTtypeP_Fitting_abelian",
          "FTtypeP_Ind_Fitting_1", "FTprTIred_Ind_Fitting",
          "FTprTIred1", "FTprTIsign", "FTtypeP_no_Ind_Fitting_facts",
          "typeP_TIred_coherent", "FTtypeP_coherence" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section11.FTType34Structure",
          "Submission.OddOrder.PF.Section12.FTType1Exclusion" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, inverse-Dade infrastructure)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePBoundsInfrastructure"
      role := "Define the analytic notation and isolate the inverse-Dade coherent residual norm"
      mappedDeclarations :=
        [ "ftTypePSumNormSq", "ftTypePSetCard", "ftTypePLeftIndex",
          "ftTypePRightIndex" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixC.NormEquationCharacterBranch",
          "Submission.OddOrder.MathlibSupport.CharacterGeneratorNorm",
          "Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism",
          "Submission.OddOrder.PF.Section13.FTTypePSetupAndCoherence" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, cyclic rectangle and support)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePCyclicRectangle"
      role := "Build eta10/eta01, the cyclic-TI rectangle pairings, non-Fitting support, and the G0 row identity"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section13.FTTypePBoundsInfrastructure" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, integral-square and generator bounds)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePGeneratorBounds"
      role := "Convert residual norms to square sums and prove the integral-square and cyclic-generator estimates"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section13.FTTypePCyclicRectangle" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, cyclic cover)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePCyclicCover"
      role := "Partition non-Fitting support by cyclic generator fibers and prove the finite cover lower bound"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section13.FTTypePGeneratorBounds" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, induced-Fitting and cyclic-TI bounds)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePBoundsFirstThree"
      role := "Assemble the induced-Fitting and two cyclic-TI lower bounds in Peterfalvi (13.6)--(13.8)"
      mappedDeclarations :=
        [ "FTtypeP_sum_Ind_Fitting_lb", "FTtypeP_sum_cycTIiso10_lb",
          "FTtypeP_sum_cycTIiso01_lb" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section13.FTTypePCyclicCover" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, non-Fitting bound)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePBoundsNonFitting"
      role := "Expose Peterfalvi (13.9)(b) from the cyclic-generator cover"
      mappedDeclarations := [ "FTtypeP_sum_nonFitting_lb" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section13.FTTypePCyclicCover" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, complement-kernel ratio)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePBoundsRatio"
      role := "Combine the four local lower bounds with the paired type-P argument to prove the complement-kernel ratio estimate"
      mappedDeclarations := [ "FTtypeP_compl_ker_ratio_lb" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section13.FTTypePBoundsFirstThree",
          "Submission.OddOrder.PF.Section13.FTTypePBoundsNonFitting" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, conclusion facade)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePBoundsConclusion"
      role := "Preserve the original conclusion-module import path for the decomposed source-facing bounds"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section13.FTTypePBoundsRatio" ]
      status := "complete" },
    { coqFile := "PFsection13.v: P-type analytic lower bounds (lines 595--1265, import facade)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePBounds"
      role := "Preserve the original downstream import path for the decomposed analytic lower-bound development"
      mappedDeclarations := []
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section13.FTTypePBoundsConclusion" ]
      status := "complete" },
    { coqFile := "PFsection13.v: regular F-core and complement consequences (lines 1266--1658)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePRegularCore"
      role := "Force regularity of the P-type F-core and identify its complement normalizer and centralizer"
      mappedDeclarations :=
        [ "FTtypeP_Ind_Fitting_reg_Fcore",
          "FTtypeP_Ind_Fitting_nonGalois_facts",
          "FTtypeP_Ind_Fitting_Galois_ub", "FTtypeP_reg_Fcore",
          "Ptype_Fcompl_kernel_trivial", "FTtypeP_nonGalois_facts",
          "FTtypeP_primes_mod_cases", "card_FTtypeP_Galois_compl",
          "FTtypeP_norm_cent_compl" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixC.Arithmetic",
          "Submission.OddOrder.PF.Section13.FTTypePBounds" ]
      status := "complete" },
    { coqFile := "PFsection13.v: type-II supports and cross-type bridges (lines 1659--2191)"
      leanModule := "Submission.OddOrder.PF.Section13.FTTypePSupportBridges"
      role := "Analyze type-II supports and construct the type-P and type-I bridge virtual characters"
      mappedDeclarations :=
        [ "FTtypeII_support_facts", "FTtypeP_bridge", "FTtypeP_bridge_gap",
          "FTtypeP_bridge_facts", "FTtype1_coherence", "FTtype1_Ind_irr",
          "FTtypeI_bridge_facts" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.RegularPrimeProduct",
          "Submission.OddOrder.PF.Section07.CoherentFrobeniusPartition",
          "Submission.OddOrder.PF.Section07.DadeCoverSeqInd",
          "Submission.OddOrder.PF.Section13.FTTypePRegularCore" ]
      status := "complete" },
    { coqFile := "PFsection14.v: global Galois-structure contradiction (lines 1--477)"
      leanModule := "Submission.OddOrder.PF.Section14.FullGaloisExclusion"
      role := "Combine type-P and type-1 support coherence to exclude the full Galois structure"
      mappedDeclarations :=
        [ "FTtypeP_complV_ltr", "coprime_typeP_Galois_core",
          "FTtype2_cc_core_ler", "FTtype2_support_coherence",
          "disjoint_Dade_FTtype1", "coherent_FTtype1_ortho",
          "coherent_FTtype1_core_ltr", "no_full_FT_Galois_structure" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.AppendixC",
          "Submission.OddOrder.PF.Section13.FTTypePSupportBridges" ]
      status := "complete" },
    { coqFile := "PFsection14.v: type-II maximal/minimal exclusion (lines 478--1209)"
      leanModule := "Submission.OddOrder.PF.Section14.FTType2Exclusion"
      role := "Analyze maximal and minimal type-II configurations and derive the final type-II contradiction"
      mappedDeclarations :=
        [ "FTtypeP_max_typeII", "FTtypeP_min_typeII", "FTtype2_exclusion" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Mathlib.Analysis.Complex.ExponentialBounds",
          "Submission.OddOrder.MathlibSupport.ComplexCyclotomicPowerAutomorphism",
          "Submission.OddOrder.PF.Section14.FullGaloisExclusion" ]
      status := "complete" },
    { coqFile := "PFsection14.v: odd-order theorem wrapper (lines 1210--1260)"
      leanModule := "Submission.OddOrder.PF.Section14.OddOrderTheorem"
      role := "Eliminate the minimal odd simple counterexample and expose the Feit--Thompson theorem"
      mappedDeclarations :=
        [ "no_minSimple_odd_group", "Feit_Thompson", "simple_odd_group_prime" ]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.PF.Section14.FTType2Exclusion",
          "Submission.OddOrder.BG.Section07.MinimalCounterexample" ]
      status := "complete" } ]

def appendixManifest : List PortEntry :=
  [ { coqFile := "BGappendixAB.v"
      leanModule := "Submission.OddOrder.BG.AppendixAB"
      role := "Bender-Glauberman appendices A and B"
      status := "complete" },
    { coqFile := "BGappendixC.v: arithmetic parameter identities"
      leanModule := "Submission.OddOrder.BG.AppendixC.Arithmetic"
      role := "Establish the geometric-sum cardinal identities, divisibility exclusions, and odd-prime bounds used throughout Appendix C"
      status := "complete" },
    { coqFile := "BGappendixC.v: elementary-abelian centralizer/commutator decomposition and Remark XI"
      leanModule := "Submission.OddOrder.BG.AppendixC.ElementaryAbelianDecomposition"
      role := "Split the elementary-abelian subgroup into fixed-point and commutator factors and adjust conjugators into the commutator factor"
      status := "complete" },
    { coqFile := "BGappendixC.v: finite-field image and multiplicative actor"
      leanModule := "Submission.OddOrder.BG.AppendixC.FiniteFieldImage"
      role := "Package the additive finite-field image of the p-group and its injective unit action"
      status := "complete" },
    { coqFile := "BGappendixC.v: image of psi and the norm-one equation"
      leanModule := "Submission.OddOrder.BG.AppendixC.FiniteFieldNormCocycle"
      role := "Identify the actor image with the finite-field norm-one subgroup"
      status := "complete" },
    { coqFile := "BGappendixC.v: cyclicity of the finite-field unit action"
      leanModule := "Submission.OddOrder.BG.AppendixC.FiniteFieldUnitAction"
      role := "Prove the acting subgroup is cyclic and commutative"
      status := "complete" },
    { coqFile := "BGappendixC.v: defFU finite-field unit decomposition"
      leanModule := "Submission.OddOrder.BG.AppendixC.FiniteFieldUnitDecomposition"
      role := "Decompose finite-field units into the prime-field factor and the norm-one actor image"
      status := "complete" },
    { coqFile := "BGappendixC.v: norm-equation cardinal bound"
      leanModule := "Submission.OddOrder.BG.AppendixC.NormEquationBound"
      role := "Bound the extension degree from inverse stability of the norm-equation solution set"
      status := "complete" },
    { coqFile := "BGappendixC.v: cubic branch of the norm equation"
      leanModule := "Submission.OddOrder.BG.AppendixC.NormEquationCubic"
      role := "Construct nontrivial norm-equation solutions in the cubic and small odd-degree cases"
      status := "complete" },
    { coqFile := "BGappendixC.v: character-sum and analytic infrastructure for the large-character branch"
      leanModule := "Submission.OddOrder.BG.AppendixC.NormEquationCharacterBranch"
      role := "Develop class-product coefficients, character-table expansion, column bounds, and the final numerical estimate"
      status := "complete" },
    { coqFile := "BGappendixC.v: source-specific large-degree character calculation"
      leanModule := "Submission.OddOrder.BG.AppendixC.NormEquationLargeDegree"
      role := "Identify the two-norm count with a Frobenius class-product coefficient and discharge the large-degree character estimate"
      status := "complete" },
    { coqFile := "BGappendixC.v: Frobenius-kernel setup"
      leanModule := "Submission.OddOrder.BG.AppendixC.FrobeniusKernelSetup"
      role := "Derive the fixed-point-free action, Frobenius data, and initial subgroup arithmetic"
      status := "complete" },
    { coqFile := "BGappendixC.v: Steps 1--2 of the final semidirect argument"
      leanModule := "Submission.OddOrder.BG.AppendixC.SemidirectTripleFactorization"
      role := "Split the first factor and exclude the corresponding split for the unit actor"
      status := "complete" },
    { coqFile := "BGappendixC.v: Step 3 of the final semidirect argument"
      leanModule := "Submission.OddOrder.BG.AppendixC.SemidirectTIIntersection"
      role := "Prove the required TI intersection from irreducibility of the scalar action"
      status := "complete" },
    { coqFile := "BGappendixC.v: Step 4 of the final semidirect argument (lines 569--749)"
      leanModule := "Submission.OddOrder.BG.AppendixC.SemidirectStep4"
      role := "Carry out the final conjugation word calculation and prove stability of the pulled-back two-norm equation set"
      status := "complete" },
    { coqFile := "BGappendixC.v"
      leanModule := "Submission.OddOrder.BG.AppendixC"
      role := "Bender-Glauberman appendix C"
      status := "complete" },
    { coqFile := "wielandt_fixpoint.v: iso_quotient_homocyclic_sdprod"
      leanModule := "Submission.OddOrder.MathlibSupport.WielandtQuotientHomocyclic"
      role := "Construct the equivariant homocyclic prime-power cover and its quotient action"
      status := "complete" },
    { coqFile := "wielandt_fixpoint.v; BGsection3.v: Frobenius_Wielandt_fixpoint (Peterfalvi 9.1)"
      leanModule := "Submission.OddOrder.MathlibSupport.WielandtSolvableFixpoint"
      role := "Prove the solvable fixed-point product identity and its source Frobenius-kernel specialization"
      mappedDeclarations := ["solvable_Wielandt_fixpoint", "Frobenius_Wielandt_fixpoint"]
      unresolvedGaps := []
      directDependencies :=
        [ "Submission.OddOrder.BG.Section03.FrobeniusPartitionSum",
          "Submission.OddOrder.MathlibSupport.MinimalNormalElementaryAbelian",
          "Submission.OddOrder.MathlibSupport.MinimalNormalExistence",
          "Submission.OddOrder.MathlibSupport.SolvableComplementActorConjugacy",
          "Submission.OddOrder.MathlibSupport.SolvableComplementConjugacy",
          "Submission.OddOrder.MathlibSupport.SubgroupCardinality",
          "Submission.OddOrder.MathlibSupport.WielandtQuotientHomocyclic" ]
      status := "complete" },
    { coqFile := "stripped_odd_order_theorem.v"
      leanModule := "Submission.OddOrder.Bridge"
      role := "minimal-counterexample bridge from the simple odd-order core to the Lean Eval statement"
      mappedDeclarations := ["OddOrderSimpleCore", "isSolvable_of_odd_order_simple_core"]
      unresolvedGaps := []
      directDependencies := ["Submission.OddOrder.MathlibSupport.Solvability"]
      status := "complete" } ]

def portManifest : List PortEntry :=
  mathlibSupportManifest ++ appendixManifest ++ peterfalviCharacterSupportManifest ++
    frontierManifest ++ downstreamManifest

def completedPortEntries : List PortEntry :=
  portManifest.filter (fun entry => entry.status == "complete")

def plannedPortEntries : List PortEntry :=
  portManifest.filter (fun entry => entry.status == "draft")

end Submission.OddOrder
