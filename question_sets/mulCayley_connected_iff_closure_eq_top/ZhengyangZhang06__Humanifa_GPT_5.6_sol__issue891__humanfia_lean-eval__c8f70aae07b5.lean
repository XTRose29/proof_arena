import Mathlib
import Submission.Helpers

namespace Submission

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro h
    apply top_unique
    intro g htop
    clear htop
    have hg :=
      (SimpleGraph.reachable_iff_reflTransGen (G := SimpleGraph.mulCayley S) 1 g).mp (h 1 g)
    induction hg with
    | refl =>
        exact Subgroup.one_mem _
    | @tail u v huv hadj ih =>
        rcases (SimpleGraph.mulCayley_adj' S u v).mp hadj with
          ⟨_, s, hs, hus | hus⟩
        · rw [← hus]
          exact (Subgroup.closure S).mul_mem ih (Subgroup.subset_closure hs)
        · simpa [hus] using
            (Subgroup.closure S).mul_mem ih
              ((Subgroup.closure S).inv_mem (Subgroup.subset_closure hs))
  · intro h
    rw [SimpleGraph.connected_iff_exists_forall_reachable]
    refine ⟨1, fun g => ?_⟩
    have hg : g ∈ Subgroup.closure S := by simp [h]
    induction hg using Subgroup.closure_induction_right with
    | one =>
        exact SimpleGraph.Reachable.rfl
    | mul_right x _ s hs ih =>
        by_cases hxs : x * s = x
        · simpa only [hxs] using ih
        · apply ih.trans
          apply SimpleGraph.Adj.reachable
          exact (SimpleGraph.mulCayley_adj' S x (x * s)).mpr
            ⟨fun h => hxs h.symm, s, hs, Or.inl rfl⟩
    | mul_inv_cancel x _ s hs ih =>
        by_cases hxs : x * s⁻¹ = x
        · simpa only [hxs] using ih
        · apply ih.trans
          apply SimpleGraph.Adj.reachable
          exact (SimpleGraph.mulCayley_adj' S x (x * s⁻¹)).mpr
            ⟨fun h => hxs h.symm, s, hs, Or.inr (by simp [mul_assoc])⟩

end Submission
