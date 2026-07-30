import Submission.OddOrder.BG.AppendixAB.CommutingRepresentationBranch
import Submission.OddOrder.MathlibSupport.SchurOneDimensional

/-!
The one-dimensional branch of the local Schur representation argument.
-/

namespace Submission.OddOrder.BG.AppendixAB

open scoped IsMulCommutative MonoidAlgebra
open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- Schur dimension one makes a faithfully represented, two-generated local
group abelian. -/
theorem local_commutator_isPGroup_of_schur_finrank_eq_one
    (E : Subgroup G) (p : ℕ) [Fact p.Prime]
    [IsMulCommutative E] [Module (ZMod p) (Additive E)]
    [Finite (Additive E)]
    (Q : Subgroup
      ((Subgroup.normalizer (E : Set G)) ⧸ normalizerCentralizer E))
    (x y : Q) (hgen : pairGenerated x y = ⊤)
    [Representation.IsIrreducible
      (localSubgroupConjugationRepresentation E p Q)]
    (hdim :
      let rho := localSubgroupConjugationRepresentation E p Q
      letI : Field (Module.End (ZMod p)[Q] rho.asModule) :=
        finiteSchurField rho
      Module.finrank (Module.End (ZMod p)[Q] rho.asModule) rho.asModule = 1) :
    IsPGroup p (_root_.commutator Q) := by
  let rho := localSubgroupConjugationRepresentation E p Q
  have hcommRep : Commute (rho x) (rho y) :=
    representation_images_commute_of_schur_finrank_eq_one rho hdim x y
  have hxy : Commute x y := by
    rw [commute_iff_eq] at hcommRep ⊢
    apply localSubgroupConjugationRepresentation_injective E p Q
    rw [map_mul, map_mul]
    exact hcommRep
  letI : IsMulCommutative Q :=
    isMulCommutative_of_pairGenerated_eq_top hgen hxy
  rw [_root_.commutator_eq_bot Q]
  exact IsPGroup.of_bot

end Submission.OddOrder.BG.AppendixAB
