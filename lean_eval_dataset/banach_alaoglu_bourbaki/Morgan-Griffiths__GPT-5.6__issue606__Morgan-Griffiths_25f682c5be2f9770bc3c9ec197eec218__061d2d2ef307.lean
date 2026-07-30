import ChallengeDeps
import Submission.Helpers

open LeanEval.Analysis
open Set Topology

namespace Submission

/-ResultProofDefinitionsBegin-/
open scoped Pointwise

-- a linear functional bounded on a neighbourhood is continuous
lemma continuous_of_bound_on_nhds_zero_real
    {E : Type*} [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    {U : Set E} (hU : U ∈ 𝓝 (0 : E)) {f : E →ₗ[ℝ] ℝ}
    (hf : ∀ x ∈ U, ‖f x‖ ≤ (1 : ℝ)) : Continuous f := by
  letI : ContinuousNeg E :=
    ⟨by
      have h := (continuous_const_smul (-1 : ℝ) : Continuous (fun x : E => (-1 : ℝ) • x))
      simpa using h⟩
  letI : IsTopologicalAddGroup E := {}
  -- it suffices to check convergence at zero for the additive homomorphism
  apply continuous_of_tendsto_nhds_zero f
  refine (Metric.tendsto_nhds).2 ?_
  intro ε hε
  let c : ℝ := ε / 2
  have hcpos : 0 < c := by dsimp [c]; linarith
  have hc : c ≠ 0 := ne_of_gt hcpos
  have hV : c • U ∈ 𝓝 (0 : E) :=
    (set_smul_mem_nhds_zero_iff hc).2 hU
  filter_upwards [hV] with x hx
  rcases (Set.mem_smul_set.mp hx) with ⟨y, hy, hxy⟩
  -- `x` is a small scalar multiple of a point of `U`
  subst x
  have hle : ‖f y‖ ≤ (1 : ℝ) := hf y hy
  -- compute the norm of the image
  rw [map_smul, dist_zero_right, norm_smul]
  have hnormc : ‖c‖ = c := Real.norm_of_nonneg (le_of_lt hcpos)
  rw [hnormc]
  calc
    c * ‖f y‖ ≤ c * 1 := mul_le_mul_of_nonneg_left hle (le_of_lt hcpos)
    _ < ε := by dsimp [c]; linarith

-- functions in the algebraic, bounded candidate subset of the product
private def polarCandidate (E : Type*) [AddCommGroup E] [Module ℝ E]
    (U : Set E) : Set (E → ℝ) :=
  {g | (∀ x ∈ U, ‖g x‖ ≤ (1:ℝ)) ∧
       (∀ x y, g (x + y) = g x + g y) ∧
       (∀ a : ℝ, ∀ x, g (a • x) = a • g x)}

private lemma isClosed_polarCandidate
    {E : Type*} [AddCommGroup E] [Module ℝ E] (U : Set E) :
    IsClosed (polarCandidate E U) := by
  -- all the equations and inequalities are closed equations between coordinate projections
  change IsClosed {g : E → ℝ |
     (∀ x ∈ U, ‖g x‖ ≤ (1:ℝ)) ∧
       (∀ x y, g (x + y) = g x + g y) ∧
       (∀ a : ℝ, ∀ x, g (a • x) = a • g x)}
  -- give the three intersections separately, using `isClosed_iInter`
  have hbound : IsClosed {g : E → ℝ | ∀ x ∈ U, ‖g x‖ ≤ (1:ℝ)} := by
    simp only [setOf_forall]
    -- after rewriting the universal predicates it is an intersection
    exact isClosed_iInter (fun x => isClosed_iInter (fun hx =>
      isClosed_le ( (continuous_apply x).norm ) continuous_const))
  have hadd : IsClosed {g : E → ℝ | ∀ x y, g (x + y) = g x + g y} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun x => isClosed_iInter (fun y =>
      isClosed_eq (continuous_apply (x+y)) ((continuous_apply x).add (continuous_apply y))))
  have hsmul : IsClosed {g : E → ℝ | ∀ a : ℝ, ∀ x, g (a • x) = a • g x} := by
    simp only [setOf_forall]
    exact isClosed_iInter (fun a => isClosed_iInter (fun x =>
      isClosed_eq (continuous_apply (a • x)) ((continuous_apply x).const_smul a)))
  exact hbound.inter (hadd.inter hsmul)

/-ResultProofDefinitionsEnd-/


theorem banach_alaoglu_bourbaki (E : Type*) [AddCommGroup E] [Module ℝ E]
    [TopologicalSpace E] [ContinuousAdd E] [ContinuousSMul ℝ E]
    [LocallyConvexSpace ℝ E] (U : Set E) (_hU : U ∈ 𝓝 (0 : E)) :
    IsCompact (weakStarPolar E U) := by
  classical
  -- every vector is a positive scalar multiple of a point of the neighbourhood
  have hex : ∀ x : E, ∃ r : ℝ, 0 < r ∧ ∃ y ∈ U, r • y = x := by
    intro x
    obtain ⟨r, hrpos, hrall⟩ := ((absorbent_nhds_zero (𝕜:=ℝ) _hU).absorbs (x:=x)).exists_pos
    have hsub : ({x} : Set E) ⊆ (r : ℝ) • U := by
      have hnorm : ‖(r:ℝ)‖ = r := Real.norm_of_nonneg (le_of_lt hrpos)
      exact hrall (r:ℝ) (by rw [hnorm])
    have hxmem : x ∈ (r:ℝ) • U := hsub (by simp)
    rcases (Set.mem_smul_set.mp hxmem) with ⟨y, hy, hxy⟩
    exact ⟨r, hrpos, y, hy, hxy⟩
  choose r hr using hex
  have hrpos : ∀ x : E, 0 < r x := fun x => (hr x).1
  have hrrep : ∀ x : E, ∃ y ∈ U, r x • y = x := fun x => (hr x).2
  let K : Set (E → ℝ) := (Set.univ).pi (fun x : E => Metric.closedBall (0 : ℝ) (r x))
  have hK : IsCompact K := by
    dsimp [K]
    apply isCompact_univ_pi
    intro x
    exact ProperSpace.isCompact_closedBall (0 : ℝ) (r x)
  have hsubK : polarCandidate E U ⊆ K := by
    intro g hg
    rcases hg with ⟨hb, ha, hs⟩
    -- pointwise boundedness at an arbitrary point follows by writing it as r times a point of U
    refine Set.mem_pi.mpr ?_
    intro x hx
    rcases hrrep x with ⟨y, hyU, hyx⟩
    apply (mem_closedBall_zero_iff).2
    have heval : g x = (r x) • g y := by
      rw [← hs (r x) y, hyx]
    rw [heval, norm_smul, Real.norm_of_nonneg (le_of_lt (hrpos x))]
    calc
      r x * ‖g y‖ ≤ r x * 1 :=
        mul_le_mul_of_nonneg_left (hb y hyU) (le_of_lt (hrpos x))
      _ = r x := by ring
  have hAcompact : IsCompact (polarCandidate E U) :=
    hK.of_isClosed_subset (isClosed_polarCandidate (E:=E) U) hsubK
  -- the candidate set is exactly the image of the polar under the coefficient embedding
  have himage :
      (((↑) : WeakDual ℝ E → (E → ℝ)) '' (weakStarPolar E U)) =
        polarCandidate E U := by
    ext g
    constructor
    · intro hg
      rcases hg with ⟨φ, hφ, rfl⟩
      change
        (∀ x ∈ U, ‖(φ : E → ℝ) x‖ ≤ (1:ℝ)) ∧
        (∀ x y, (φ : E → ℝ) (x+y) = (φ : E → ℝ) x + (φ : E → ℝ) y) ∧
        (∀ a : ℝ, ∀ x, (φ : E → ℝ) (a • x) = a • (φ : E → ℝ) x)
      refine ⟨?_, ?_, ?_⟩
      · exact hφ
      · intro x y
        exact map_add (WeakDual.toStrongDual φ) x y
      · intro a x
        exact map_smul (WeakDual.toStrongDual φ) a x
    · intro hg
      rcases hg with ⟨hb, ha, hs⟩
      let lm : E →ₗ[ℝ] ℝ :=
        { toFun := g
          map_add' := ha
          map_smul' := hs }
      have hlm : Continuous lm := by
        apply continuous_of_bound_on_nhds_zero_real _hU
        intro x hx
        exact hb x hx
      let clm : E →L[ℝ] ℝ := ContinuousLinearMap.mk lm hlm
      let φ : WeakDual ℝ E := StrongDual.toWeakDual clm
      have hφ : φ ∈ weakStarPolar E U := by
        intro x hx
        change ‖lm x‖ ≤ (1:ℝ)
        exact hb x hx
      refine ⟨φ, hφ, ?_⟩
      rfl
  have hEmb : IsEmbedding ((↑) : WeakDual ℝ E → (E → ℝ)) :=
    DFunLike.coe_injective.isEmbedding_induced
  exact hEmb.isCompact_iff.mpr (himage ▸ hAcompact)


end Submission
