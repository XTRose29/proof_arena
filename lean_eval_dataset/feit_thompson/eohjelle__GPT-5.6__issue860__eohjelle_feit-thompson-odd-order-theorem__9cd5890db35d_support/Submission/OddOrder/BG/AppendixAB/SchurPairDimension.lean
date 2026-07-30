import Submission.OddOrder.BG.AppendixAB.SquareZeroGeneratedTopDimension
import Submission.OddOrder.MathlibSupport.SchurAnticommutatorScalar
import Submission.OddOrder.MathlibSupport.SchurScalarIrreducible

/-!
The Schur-field dimension bound for a top-generating quadratic pair.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped MonoidAlgebra
open Submission.OddOrder.MathlibSupport

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- The representation-theoretic dimension endpoint used in the
noncommuting branch of odd p-stability. -/
theorem schurPair_finrank_le_two
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    [Finite V] (x y : G)
    (hgen : pairGenerated x y = ⊤)
    (hX : (rho x - 1) * (rho x - 1) = 0)
    (hY : (rho y - 1) * (rho y - 1) = 0)
    (A : Representation.IntertwiningMap rho rho)
    (hA : A.toLinearMap = anticommutator (rho x - 1) (rho y - 1))
    (hXne : rho x - 1 ≠ 0) :
    letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
    Module.finrank (Module.End k[G] rho.asModule) rho.asModule ≤ 2 := by
  letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
  let rhoD := schurScalarRepresentation rho
  let X := schurDeviation rho x
  let Y := schurDeviation rho y
  let a := (Representation.IntertwiningMap.equivAlgEnd (ρ := rho)) A
  letI : Representation.IsIrreducible rhoD := by
    dsimp only [rhoD]
    exact schurScalarRepresentation_isIrreducible rho
  have hrhoX : rhoD x = 1 + X := by
    dsimp only [rhoD, X, schurDeviation]
    noncomm_ring
  have hrhoY : rhoD y = 1 + Y := by
    dsimp only [rhoD, Y, schurDeviation]
    noncomm_ring
  have hXD : X * X = 0 := by
    dsimp only [X]
    exact schurDeviation_mul_self_eq_zero rho x hX
  have hYD : Y * Y = 0 := by
    dsimp only [Y]
    exact schurDeviation_mul_self_eq_zero rho y hY
  have hAD : anticommutator X Y =
      a • (1 : Module.End (Module.End k[G] rho.asModule) rho.asModule) := by
    dsimp only [X, Y, a]
    exact schurDeviation_anticommutator_eq_smul rho x y A hA
  have hXneD : X ≠ 0 := by
    intro hzero
    apply hXne
    apply (asModuleEndRingEquiv rho).injective
    have htransport : asModuleEndRingEquiv rho (rho x - 1) = 0 := by
      ext v
      have hv := LinearMap.congr_fun hzero v
      dsimp only [X] at hv
      rw [schurDeviation_apply] at hv
      simpa using hv
    simpa only [map_zero] using htransport
  exact finrank_le_two_of_square_zero_pair_generates_top
    rhoD x y X Y a hgen hrhoX hrhoY hXD hYD hAD hXneD

end Submission.OddOrder.BG.AppendixAB
