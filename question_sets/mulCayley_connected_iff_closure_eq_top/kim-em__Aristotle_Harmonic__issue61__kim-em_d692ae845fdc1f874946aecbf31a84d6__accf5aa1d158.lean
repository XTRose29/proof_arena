import Mathlib

namespace Submission

private lemma adj_implies_mem_closure {G : Type*} [Group G] {S : Set G} {u v : G}
    (hu : u ∈ Subgroup.closure S) (hadj : (SimpleGraph.mulCayley S).Adj u v) :
    v ∈ Subgroup.closure S := by
  rw [SimpleGraph.mulCayley_adj] at hadj
  obtain ⟨_, h1 | h1⟩ := hadj
  · have hmem : u⁻¹ * v ∈ Subgroup.closure S := Subgroup.subset_closure h1
    have : v = u * (u⁻¹ * v) := by group
    rw [this]
    exact Subgroup.mul_mem _ hu hmem
  · have hmem : (v⁻¹ * u)⁻¹ ∈ Subgroup.closure S :=
      Subgroup.inv_mem _ (Subgroup.subset_closure h1)
    have : v = u * (v⁻¹ * u)⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hu hmem

private lemma walk_end_mem_closure {G : Type*} [Group G] {S : Set G} {u v : G}
    (hu : u ∈ Subgroup.closure S) (w : (SimpleGraph.mulCayley S).Walk u v) :
    v ∈ Subgroup.closure S := by
  induction w with
  | nil => exact hu
  | cons hadj _ ih => exact ih (adj_implies_mem_closure hu hadj)

private lemma closure_eq_top_of_connected {G : Type*} [Group G] {S : Set G}
    (hconn : (SimpleGraph.mulCayley S).Connected) :
    Subgroup.closure S = ⊤ := by
  rw [Subgroup.eq_top_iff']
  intro g
  obtain ⟨w⟩ := hconn.preconnected 1 g
  exact walk_end_mem_closure (Subgroup.one_mem _) w

private def leftMulHom {G : Type*} [Group G] (S : Set G) (d : G) :
    (SimpleGraph.mulCayley S) →g (SimpleGraph.mulCayley S) where
  toFun := (d * ·)
  map_rel' := by
    intro u v hadj
    rwa [SimpleGraph.mulCayley_adj_mul_iff_right]

private lemma reachable_left_mul {G : Type*} [Group G] {S : Set G} {u v : G} (d : G)
    (h : (SimpleGraph.mulCayley S).Reachable u v) :
    (SimpleGraph.mulCayley S).Reachable (d * u) (d * v) := by
  obtain ⟨w⟩ := h
  exact ⟨w.map (leftMulHom S d)⟩

private noncomputable def reachableSubgroup {G : Type*} [Group G] (S : Set G) : Subgroup G where
  carrier := {g | (SimpleGraph.mulCayley S).Reachable 1 g}
  one_mem' := SimpleGraph.Reachable.refl _
  mul_mem' := by
    intro a b ha hb
    have hab : (SimpleGraph.mulCayley S).Reachable a (a * b) := by
      have := reachable_left_mul a hb
      rwa [mul_one] at this
    exact ha.trans hab
  inv_mem' := by
    intro a ha
    have : (SimpleGraph.mulCayley S).Reachable (a⁻¹ * 1) (a⁻¹ * a) :=
      reachable_left_mul a⁻¹ ha
    simp at this
    exact this.symm

private lemma connected_of_closure_eq_top {G : Type*} [Group G] {S : Set G}
    (hclosure : Subgroup.closure S = ⊤) :
    (SimpleGraph.mulCayley S).Connected := by
  constructor
  · intro u v
    suffices h : ∀ g : G, (SimpleGraph.mulCayley S).Reachable 1 g from
      (h u).symm.trans (h v)
    intro g
    have hg : g ∈ (reachableSubgroup S : Set G) := by
      have : Subgroup.closure S ≤ reachableSubgroup S := by
        rw [Subgroup.closure_le]
        intro s hs
        show (SimpleGraph.mulCayley S).Reachable 1 s
        by_cases h : s = 1
        · subst h; exact SimpleGraph.Reachable.refl _
        · exact ⟨SimpleGraph.Walk.cons
            (by rw [SimpleGraph.mulCayley_adj]; exact ⟨Ne.symm h, by simp [hs]⟩)
            SimpleGraph.Walk.nil⟩
      rw [hclosure] at this
      exact this trivial
    exact hg

theorem mulCayley_connected_iff_closure_eq_top {G : Type*} [Group G]
    (S : Set G) :
    (SimpleGraph.mulCayley S).Connected ↔ Subgroup.closure S = ⊤ :=
  ⟨closure_eq_top_of_connected, connected_of_closure_eq_top⟩

end Submission
