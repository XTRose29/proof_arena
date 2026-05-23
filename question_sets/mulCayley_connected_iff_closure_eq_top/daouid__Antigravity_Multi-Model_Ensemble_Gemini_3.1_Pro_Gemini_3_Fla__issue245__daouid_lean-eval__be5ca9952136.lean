/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: mulCayley_connected_iff_closure_eq_top
user: daouid
model: Antigravity (Multi-Model Ensemble: Gemini 3.1 Pro, Gemini 3 Flash, Claude 4.6 Sonnet/Opus)
submission_repo: daouid/lean-eval
submission_ref: be5ca99521362ea9131eca9a2d95d91ec6fff0f4
issue_number: 245
-/
import Mathlib

namespace Submission

lemma Reachable_mul_left {G : Type*} [Group G] {S : Set G} {a x y : G}
    (h : (SimpleGraph.mulCayley S).Reachable x y) :
    (SimpleGraph.mulCayley S).Reachable (a * x) (a * y) := by
  rw [SimpleGraph.reachable_iff_reflTransGen] at h ⊢
  induction h with
  | refl => exact Relation.ReflTransGen.refl
  | tail h_path h_adj ih =>
    rename_i y' y
    apply Relation.ReflTransGen.tail ih
    rw [SimpleGraph.mulCayley_adj] at h_adj ⊢
    rcases h_adj with ⟨hne, hS⟩
    constructor
    · exact fun h_eq => hne (mul_left_cancel h_eq)
    · rcases hS with hS1 | hS2
      · left
        have h_eq : (a * y')⁻¹ * (a * y) = y'⁻¹ * y := by group
        rw [h_eq]
        exact hS1
      · right
        have h_eq : (a * y)⁻¹ * (a * y') = y⁻¹ * y' := by group
        rw [h_eq]
        exact hS2

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro h
    rw [Subgroup.eq_top_iff']
    intro g
    have h_reach : (SimpleGraph.mulCayley S).Reachable 1 g := (h.preconnected 1 g)
    rw [SimpleGraph.reachable_iff_reflTransGen] at h_reach
    induction h_reach with
    | refl => exact Subgroup.one_mem _
    | tail h_path h_adj ih =>
      rename_i y' y
      rw [SimpleGraph.mulCayley_adj] at h_adj
      rcases h_adj.2 with hS | hS
      · have : y = y' * (y'⁻¹ * y) := mul_inv_cancel_left y' y |>.symm
        rw [this]
        exact Subgroup.mul_mem (Subgroup.closure S) ih (Subgroup.subset_closure hS)
      · have : y = y' * (y⁻¹ * y')⁻¹ := by group
        rw [this]
        apply Subgroup.mul_mem (Subgroup.closure S) ih
        apply Subgroup.inv_mem (Subgroup.closure S)
        exact Subgroup.subset_closure hS
  · intro h
    refine ⟨fun u v => ?_⟩
    have h_reach_one : ∀ g, (SimpleGraph.mulCayley S).Reachable 1 g := by
      intro g
      have hg : g ∈ Subgroup.closure S := by rw [h]; exact Subgroup.mem_top g
      induction hg using Subgroup.closure_induction with
      | mem x hx =>
        by_cases hx1 : x = 1
        · subst hx1; exact SimpleGraph.Reachable.refl 1
        · apply SimpleGraph.Adj.reachable
          rw [SimpleGraph.mulCayley_adj]
          exact ⟨Ne.symm hx1, Or.inl (by simp [hx])⟩
      | one => exact SimpleGraph.Reachable.refl 1
      | mul x y _ _ ihx ihy =>
        have h_trans : (SimpleGraph.mulCayley S).Reachable x (x * y) := by
          have h_mul := Reachable_mul_left (a := x) ihy
          rw [mul_one] at h_mul
          exact h_mul
        exact ihx.trans h_trans
      | inv x _ ihx =>
        have h_inv : (SimpleGraph.mulCayley S).Reachable 1 x⁻¹ := by
          have h_mul := Reachable_mul_left (a := x⁻¹) ihx
          rw [inv_mul_cancel, mul_one] at h_mul
          exact h_mul.symm
        exact h_inv
    exact (h_reach_one u).symm.trans (h_reach_one v)

end Submission