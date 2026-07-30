import Submission.OddOrder.BG.AppendixAB.SchurPairDimension
import Submission.OddOrder.MathlibSupport.FiniteCarrierModule
import Submission.OddOrder.MathlibSupport.SchurOneDimensional

/-!
The noncommuting Schur pair has dimension exactly two.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped MonoidAlgebra
open Submission.OddOrder.MathlibSupport

variable {k G V : Type*} [Field k] [Group G]
variable [AddCommGroup V] [Module k V]

/-- A noncommuting pair satisfying the square-zero Schur hypotheses has
canonical Schur dimension exactly two. -/
theorem schurPair_finrank_eq_two
    (rho : Representation k G V) [Representation.IsIrreducible rho]
    [Finite V] (x y : G)
    (hgen : pairGenerated x y = ⊤)
    (hX : (rho x - 1) * (rho x - 1) = 0)
    (hY : (rho y - 1) * (rho y - 1) = 0)
    (A : Representation.IntertwiningMap rho rho)
    (hA : A.toLinearMap = anticommutator (rho x - 1) (rho y - 1))
    (hXne : rho x - 1 ≠ 0)
    (hnotcomm : ¬Commute (rho x) (rho y)) :
    letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
    Module.finrank (Module.End k[G] rho.asModule) rho.asModule = 2 := by
  letI : Field (Module.End k[G] rho.asModule) := finiteSchurField rho
  let D := Module.End k[G] rho.asModule
  letI : Finite rho.asModule :=
    Finite.of_injective rho.asModuleEquiv rho.asModuleEquiv.injective
  letI : Module.Finite D rho.asModule := moduleFiniteOfFiniteCarrier
  obtain ⟨v, hv⟩ : ∃ v : V, (rho x - 1) v ≠ 0 := by
    by_contra h
    push Not at h
    apply hXne
    ext w
    exact h w
  let w : rho.asModule := rho.asModuleEquiv.symm ((rho x - 1) v)
  have hw : w ≠ 0 := by
    exact rho.asModuleEquiv.symm.map_ne_zero_iff.mpr hv
  letI : Nontrivial rho.asModule := ⟨⟨w, 0, hw⟩⟩
  have hpos : 0 < Module.finrank D rho.asModule := Module.finrank_pos
  have hle : Module.finrank D rho.asModule ≤ 2 :=
    schurPair_finrank_le_two rho x y hgen hX hY A hA hXne
  have hneone : Module.finrank D rho.asModule ≠ 1 := by
    intro hone
    exact hnotcomm
      (representation_images_commute_of_schur_finrank_eq_one rho hone x y)
  dsimp only [D] at hpos hle hneone ⊢
  omega

end Submission.OddOrder.BG.AppendixAB
