/-
Downloaded from the public lean-eval leaderboard provenance.
problem_id: mulCayley_connected_iff_closure_eq_top
user: sqrt-of-2
model: Gemini 3.1 Pro
submission_repo: sqrt-of-2/19e53094d302b7c924c62ff55508365e
submission_ref: 75cab7139ace8c092d8d2f0273c4e6c35833f0f6
issue_number: 190
-/
import Mathlib

open SimpleGraph Matrix

namespace Submission

theorem walk_mem_closure {G : Type*} [Group G] {S : Set G} {u v : G}
    (W : (mulCayley S).Walk u v) : u⁻¹ * v ∈ Subgroup.closure S := by
  induction W with
  | nil => 
    simp only [inv_mul_cancel, Subgroup.one_mem]
  | @cons u v w hadj W' ih =>
    rw [mulCayley_adj] at hadj
    rw [show u⁻¹ * w = (u⁻¹ * v) * (v⁻¹ * w) by group]
    apply Subgroup.mul_mem
    · rcases hadj.2 with hS | hS
      · exact Subgroup.subset_closure hS
      · have := Subgroup.subset_closure hS
        have := Subgroup.inv_mem _ this
        simpa using this
    · exact ih

theorem mem_closure_reachable {G : Type*} [Group G] {S : Set G} {g : G}
    (h : g ∈ Subgroup.closure S) : (mulCayley S).Reachable 1 g := by
  induction h using Subgroup.closure_induction with
  | mem s hs =>
    by_cases h1s : 1 = s
    · cases h1s; exact Reachable.refl 1
    · apply Adj.reachable; rw [mulCayley_adj]; simp [h1s, hs]
  | one => exact Reachable.refl 1
  | inv s _ ih =>
    let f : (mulCayley S) →g (mulCayley S) := {
      toFun := fun x => s⁻¹ * x
      map_rel' := fun {u v} h => by
        simp only [mulCayley_adj] at h ⊢
        simpa using h
    }
    have h_s1 := ih.symm.map f
    simpa [f] using h_s1
  | mul x y _ _ ihx ihy =>
    let f : (mulCayley S) →g (mulCayley S) := {
      toFun := fun g => x * g
      map_rel' := fun {u v} h => by
        simp only [mulCayley_adj] at h ⊢
        simpa using h
    }
    have h_xy := ihy.map f
    simp [f] at h_xy
    exact ihx.trans h_xy

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro h
    rw [Subgroup.eq_top_iff']
    intro g
    have h1g := h.preconnected 1 g
    obtain ⟨W⟩ := h1g
    have := walk_mem_closure W
    simpa using this
  · intro h
    constructor
    intro u v
    have : u⁻¹ * v ∈ Subgroup.closure S := by rw [h]; exact Subgroup.mem_top _
    have h1uv := mem_closure_reachable this
    let f : (mulCayley S) →g (mulCayley S) := {
      toFun := fun x => u * x
      map_rel' := fun {u' v'} h => by
        simp only [mulCayley_adj] at h ⊢
        simpa using h
    }
    have := h1uv.map f
    simp [f] at this
    exact this

end Submission
