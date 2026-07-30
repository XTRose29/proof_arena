import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis
open Set Topology
open scoped Pointwise

namespace Submission

theorem banach_alaoglu_bourbaki (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (U : Set E) (_hU : U ∈ 𝓝 (0 : E)) :
    IsCompact (weakStarPolar E U) := by
  letI : ContinuousNeg E := ⟨by
    simpa only [neg_one_smul] using
      (continuous_const_smul (-1 : ℝ) : Continuous fun x : E => (-1 : ℝ) • x)⟩
  letI : IsTopologicalAddGroup E := ⟨⟩
  have h_absorb : ∀ x : E, ∃ c : ℝ, 0 < c ∧ x ∈ c • U := by
    intro x
    obtain ⟨c, hc, hcU⟩ :=
      ((absorbent_nhds_zero (𝕜 := ℝ) _hU).absorbs (x := x)).exists_pos
    refine ⟨c, hc, hcU c ?_ (by simp)⟩
    simp [Real.norm_eq_abs, abs_of_pos hc]
  choose C hCpos hxC using h_absorb
  have h_image_eq :
      ((fun φ : WeakDual ℝ E => (φ : E → ℝ)) '' weakStarPolar E U) =
        Set.range ((↑) : (E →ₗ[ℝ] ℝ) → E → ℝ) ∩
          {f : E → ℝ | ∀ x ∈ U, ‖f x‖ ≤ 1} := by
    ext f
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact ⟨⟨(StrongDual.toWeakDual.symm φ).toLinearMap, rfl⟩, hφ⟩
    · rintro ⟨⟨l, rfl⟩, hl⟩
      have hb : Bornology.IsVonNBounded ℝ (l '' U) := by
        apply Bornology.IsVonNBounded.subset ?_
          (NormedSpace.isVonNBounded_closedBall ℝ ℝ 1)
        rintro y ⟨x, hx, rfl⟩
        exact mem_closedBall_zero_iff.mpr (hl x hx)
      let φ : E →L[ℝ] ℝ :=
        l.clmOfExistsBoundedImage ⟨U, _hU, hb⟩
      refine ⟨StrongDual.toWeakDual φ, ?_, ?_⟩
      · intro x hx
        change ‖φ x‖ ≤ 1
        simpa [φ] using hl x hx
      · funext x
        simp [φ]
  have h_closed :
      IsClosed ((fun φ : WeakDual ℝ E => (φ : E → ℝ)) '' weakStarPolar E U) := by
    rw [h_image_eq]
    apply (LinearMap.isClosed_range_coe E ℝ (RingHom.id ℝ)).inter
    simp only [setOf_forall]
    exact isClosed_biInter fun x _ =>
      isClosed_Iic.preimage (continuous_apply x).norm
  have h_coord (φ : WeakDual ℝ E) (hφ : φ ∈ weakStarPolar E U) (x : E) :
      φ x ∈ Set.Icc (-C x) (C x) := by
    obtain ⟨u, hu, hux⟩ := Set.mem_smul_set.mp (hxC x)
    apply abs_le.mp
    calc
      |φ x| = |φ (C x • u)| := by rw [hux]
      _ = C x * |φ u| := by simp [abs_mul, abs_of_pos (hCpos x)]
      _ ≤ C x * 1 :=
        mul_le_mul_of_nonneg_left (by simpa [Real.norm_eq_abs] using hφ u hu) (hCpos x).le
      _ = C x := mul_one _
  apply DFunLike.coe_injective.isEmbedding_induced.isCompact_iff.mpr
  refine IsCompact.of_isClosed_subset
    (isCompact_univ_pi (s := fun x : E => Set.Icc (-C x) (C x)) fun _ => isCompact_Icc)
    h_closed ?_
  rintro f ⟨φ, hφ, rfl⟩ x _
  exact h_coord φ hφ x

end Submission
