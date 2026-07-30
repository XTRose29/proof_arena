import ChallengeDeps
import Submission.GolodShafarevich

open LeanEval.GroupTheory
open CategoryTheory
open Submission.GroupAlgebra Submission.GeneratorRank Submission.Presentation
  Submission.RelationCocycle Submission.GolodShafarevich

namespace Submission

theorem golod_shafarevich_inequality (p : ℕ) [Fact p.Prime] (Q : Type)
    [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q]
    [DiscreteTopology Q] [Finite Q] :
    IsPGroup p Q → Nontrivial Q →
      (generatorRank Q : ℝ) ^ 2 < 4 * (relationRank p Q : ℝ) := by
  intro hQ hnontrivial
  letI : Nontrivial Q := hnontrivial
  have hnil : IsNilpotent (augmentationIdeal (ZMod p) Q) :=
    augmentationIdeal_isNilpotent p Q hQ
  have hgenerator : generatorRank Q =
      Module.finrank (ZMod p) (AugmentationCotangent (ZMod p) Q) :=
    generatorRank_eq_finrank_augmentationCotangent (ZMod p) Q hnil
  obtain ⟨g, hlin, hspan⟩ :=
    exists_groupElements_cotangent_basis (ZMod p) Q
  have hd : 0 < Module.finrank (ZMod p)
      (AugmentationCotangent (ZMod p) Q) := by
    rw [← hgenerator]
    exact Helpers.generatorRank_pos Q
  have hminimal := minimalPresentation_inequality (ZMod p) Q
    g hlin hspan hnil hd
  have hrelation := relationSpace_finrank_le_groupH2 (ZMod p) Q
    g hlin hspan hnil
  have hcomparison : Module.finrank (ZMod p)
      (groupCohomology.H2 (trivialRep (ZMod p) Q)) = relationRank p Q := by
    rw [relationRank]
    exact LinearEquiv.finrank_eq
      (CohomologyComparison.groupH2ContinuousLinearEquiv p Q)
  have hrelation' : Module.finrank (ZMod p) (RelationSpace (ZMod p) Q g) ≤
      relationRank p Q := hrelation.trans_eq hcomparison
  have hrelationReal :
      (Module.finrank (ZMod p) (RelationSpace (ZMod p) Q g) : ℝ) ≤
        (relationRank p Q : ℝ) := by
    exact_mod_cast hrelation'
  calc
    (generatorRank Q : ℝ) ^ 2 =
        (Module.finrank (ZMod p) (AugmentationCotangent (ZMod p) Q) : ℝ) ^ 2 := by
      rw [hgenerator]
    _ < 4 *
        (Module.finrank (ZMod p) (RelationSpace (ZMod p) Q g) : ℝ) := hminimal
    _ ≤ 4 * (relationRank p Q : ℝ) := by nlinarith

end Submission
