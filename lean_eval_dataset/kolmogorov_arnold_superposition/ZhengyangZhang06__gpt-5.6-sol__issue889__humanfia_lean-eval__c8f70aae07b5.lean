import Mathlib
import Submission.Helpers

open scoped BigOperators BoundedContinuousFunction

namespace Submission

theorem kolmogorov_arnold (n : ℕ) (_hn : 1 ≤ n)
    (f : (Fin n → ℝ) → ℝ) (_hf : ContinuousOn f (Set.Icc 0 1)) :
    ∃ (g : ℝ → ℝ) (φ : Fin (2 * n + 1) → Fin n → ℝ → ℝ),
      Continuous g ∧ (∀ k l, Continuous (φ k l)) ∧
      ∀ x ∈ Set.Icc (0 : Fin n → ℝ) 1,
        f x = ∑ k, g (∑ l, φ k l (x l)) := by
  classical
  letI : CompactSpace (Helpers.Cube n) :=
    isCompact_iff_compactSpace.mp isCompact_Icc
  let fCube : C(Helpers.Cube n, ℝ) :=
    ⟨fun x ↦ f x.1, _hf.restrict⟩
  let F : Helpers.Cube n →ᵇ ℝ :=
    BoundedContinuousFunction.mkOfCompact fCube
  obtain ⟨ψ, H, hsuperpose⟩ :=
    Helpers.exactSuperposition_of_approximationStep n F
      (Helpers.approximationStep_exists n _hn)
  have hext (k : Fin (2 * n + 1)) (l : Fin n) :
      ∃ p : ℝ →ᵇ ℝ, ∀ t : Helpers.UnitInterval, p t = ψ k l t := by
    obtain ⟨p, _hpNorm, hp⟩ :=
      BoundedContinuousFunction.exists_extension_norm_eq_of_isClosedEmbedding
        (ψ k l) isClosed_Icc.isClosedEmbedding_subtypeVal
    exact ⟨p, congr_fun hp⟩
  choose p hp using hext
  obtain ⟨g, φ, hg, hφ, hcombine⟩ :=
    Helpers.combineOuterFunctions n _hn
      (fun k t ↦ H k t) (fun k l t ↦ p k l t)
      (fun k ↦ (H k).continuous) (fun k l ↦ (p k l).continuous)
  refine ⟨g, φ, hg, hφ, ?_⟩
  intro x hx
  have hrepresentation :
      f x = ∑ k, H k (∑ l, p k l (x l)) := by
    have hpoint := congrArg
      (fun q : Helpers.Cube n →ᵇ ℝ ↦ q ⟨x, hx⟩) hsuperpose
    simpa [F, fCube, Helpers.superpose_apply, Helpers.innerSum_apply,
      Helpers.cubeCoord, ← hp] using hpoint
  exact hrepresentation.trans (hcombine x hx)

end Submission
