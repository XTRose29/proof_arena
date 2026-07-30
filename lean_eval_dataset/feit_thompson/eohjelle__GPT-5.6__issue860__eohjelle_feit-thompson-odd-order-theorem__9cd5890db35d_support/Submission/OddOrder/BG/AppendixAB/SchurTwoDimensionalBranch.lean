import Submission.OddOrder.BG.AppendixAB.SchurPairDimensionTwo
import Submission.OddOrder.BG.AppendixAB.LocalConjugationRepresentation
import Submission.OddOrder.BG.Section02.OddGL2Characteristic

/-!
The two-dimensional branch of the local Schur representation argument.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative MonoidAlgebra
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- Schur dimension two lets the odd faithful `GL₂` theorem make the local
commutator a `p`-group. -/
theorem local_commutator_isPGroup_of_schur_finrank_eq_two
    (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    [Finite (Additive E)]
    (Q : Subgroup
      ((Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E))
    [Finite Q]
    [Representation.IsIrreducible
      (localSubgroupConjugationRepresentation E p Q)]
    (hdim :
      let rho := localSubgroupConjugationRepresentation E p Q
      letI : Field (Module.End (ZMod p)[Q] rho.asModule) :=
        finiteSchurField rho
      Module.finrank (Module.End (ZMod p)[Q] rho.asModule) rho.asModule = 2)
    (hodd : Odd (Nat.card Q)) :
    IsPGroup p (_root_.commutator Q) := by
  let rho := localSubgroupConjugationRepresentation E p Q
  let D := Module.End (ZMod p)[Q] rho.asModule
  letI : Field D := finiteSchurField rho
  letI : CharP D p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) D).injective p
  let rhoD := schurScalarRepresentation rho
  letI : Finite rho.asModule :=
    Finite.of_injective rho.asModuleEquiv rho.asModuleEquiv.injective
  letI : Module.Finite D rho.asModule := moduleFiniteOfFiniteCarrier
  have hrhoD : Function.Injective rhoD := by
    intro x y hxy
    apply localSubgroupConjugationRepresentation_injective E p Q
    apply LinearMap.ext
    intro v
    let w := rho.asModuleEquiv.symm v
    have hv := DFunLike.congr_fun hxy w
    change schurScalarRepresentation rho x w =
      schurScalarRepresentation rho y w at hv
    rw [schurScalarRepresentation_apply,
      schurScalarRepresentation_apply] at hv
    have hv' := congrArg rho.asModuleEquiv hv
    change rho x v = rho y v at hv'
    exact hv'
  exact Section02.odd_faithful_finrank_two_commutator_isPGroup_charP
    rhoD hrhoD hdim hodd

end Submission.OddOrder.BG.AppendixAB
