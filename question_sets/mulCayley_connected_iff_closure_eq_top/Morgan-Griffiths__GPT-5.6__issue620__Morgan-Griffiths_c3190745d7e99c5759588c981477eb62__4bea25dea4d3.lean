import Mathlib
import Submission.Helpers

namespace Submission

/-ResultProofDefinitionsBegin-/
/-ResultProofDefinitionsEnd-/


theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ := by
  constructor
  · intro hcon
    refine (Subgroup.eq_top_iff' (Subgroup.closure S)).2 ?_
    intro g
    have reach : (SimpleGraph.mulCayley S).Reachable (1 : G) g := hcon (1 : G) g
    rcases reach with ⟨p⟩
    have walk_mem : ∀ {u v : G},
        (SimpleGraph.mulCayley S).Walk u v →
          u ∈ Subgroup.closure S → v ∈ Subgroup.closure S := by
      intro u v q
      induction q with
      | nil =>
          intro hu
          exact hu
      | @cons u v w huv q ih =>
          intro hu
          have hv : v ∈ Subgroup.closure S := by
            obtain ⟨hne, t, ht, hmul | hmul⟩ :=
              (SimpleGraph.mulCayley_adj' S u v).1 huv
            · have hprod : u * t ∈ Subgroup.closure S :=
                (Subgroup.closure S).mul_mem hu (Subgroup.subset_closure ht)
              rw [hmul] at hprod
              exact hprod
            · have ht' : t ∈ Subgroup.closure S := Subgroup.subset_closure ht
              have hvt : v * t ∈ Subgroup.closure S := by
                rw [← hmul]
                exact hu
              have hprodinv : (v * t) * t⁻¹ ∈ Subgroup.closure S :=
                (Subgroup.closure S).mul_mem hvt ((Subgroup.closure S).inv_mem ht')
              simpa using hprodinv
          exact ih hv
    exact walk_mem p ((Subgroup.closure S).one_mem)
  · intro htop
    have reach_mul_gen : ∀ (x : G), x ∈ Subgroup.closure S →
        ∀ a : G, (SimpleGraph.mulCayley S).Reachable a (a * x) := by
      intro x hx
      induction hx using Subgroup.closure_induction_right with
      | one =>
          intro a
          simpa using (SimpleGraph.Reachable.refl (G := SimpleGraph.mulCayley S) a)
      | @mul_right x hx y hy ih =>
          intro a
          have h₁ : (SimpleGraph.mulCayley S).Reachable a (a * x) := ih a
          have hstep : (SimpleGraph.mulCayley S).Reachable (a * x) ((a * x) * y) := by
            by_cases heq : a * x = (a * x) * y
            · -- if multiplication by the generator does not move the vertex
              rw [← heq]
            · have hadj : (SimpleGraph.mulCayley S).Adj (a * x) ((a * x) * y) :=
                  (SimpleGraph.mulCayley_adj' S (a * x) ((a * x) * y)).2
                    ⟨heq, y, hy, Or.inl rfl⟩
              exact hadj.reachable
          have htot : (SimpleGraph.mulCayley S).Reachable a ((a * x) * y) :=
            h₁.trans hstep
          simpa [mul_assoc] using htot
      | @mul_inv_cancel x hx y hy ih =>
          intro a
          have h₁ : (SimpleGraph.mulCayley S).Reachable a (a * x) := ih a
          have hstep : (SimpleGraph.mulCayley S).Reachable (a * x) ((a * x) * y⁻¹) := by
            by_cases heq : a * x = (a * x) * y⁻¹
            · rw [← heq]
            · have hlast : a * x = ((a * x) * y⁻¹) * y := by
                simp [mul_assoc]
              have hadj : (SimpleGraph.mulCayley S).Adj (a * x) ((a * x) * y⁻¹) :=
                  (SimpleGraph.mulCayley_adj' S (a * x) ((a * x) * y⁻¹)).2
                    ⟨heq, y, hy, Or.inr hlast⟩
              exact hadj.reachable
          have htot : (SimpleGraph.mulCayley S).Reachable a ((a * x) * y⁻¹) :=
            h₁.trans hstep
          simpa [mul_assoc] using htot
    -- the group is nonempty (it has its identity)
    refine ⟨?_⟩
    intro u v
    -- it suffices to travel from u by the group element u⁻¹*v
    have hx : u⁻¹ * v ∈ Subgroup.closure S := by
      rw [htop]
      trivial
    have hr := reach_mul_gen (u⁻¹ * v) hx u
    simpa [mul_assoc] using hr


end Submission
