import Submission.SylowBlocks

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs
open scoped Pointwise

namespace Submission.Helpers

universe u

/-- In the minimal-counterexample induction, every proper subgroup generated
by conjugates of `x` is a `p`-group. -/
theorem closure_isPGroup_of_subset_conjugates_of_ne_top_of_induction
    {G : Type u} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hind : ∀ {K : Type u} [Group K] [Finite K],
      Nat.card K < Nat.card G → ∀ y : K,
        y ∈ pCore p K ↔
          ∀ k : K, IsPGroup p
            (Subgroup.closure ({y, k * y * k⁻¹} : Set K)))
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (S : Set G)
    (hS : S ⊆ Group.conjugatesOfSet ({x} : Set G))
    (hne : Subgroup.closure S ≠ ⊤) :
    IsPGroup p (Subgroup.closure S) := by
  let K : Subgroup G := Subgroup.closure S
  have hK : K < ⊤ :=
    lt_top_iff_ne_top.mpr hne
  have hp :
      IsPGroup p (conjugateClosureIn x K) :=
    conjugateClosureIn_isPGroup_proper_subgroup_of_induction
      hind x K hK h
  have heq : Subgroup.closure S = conjugateClosureIn x K := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro y hy
      apply Subgroup.subset_closure
      exact
        ⟨hS hy, Subgroup.subset_closure hy⟩
    · exact conjugateClosureIn_le x K
  rwa [heq]

/-- A conjugate of `x` fixes the closure block attached to `P` exactly
when it belongs to the corresponding conjugacy-class closure. -/
theorem conjugate_mem_stabilizer_sylowClosureBlock_iff
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    (P : Sylow p G) {y : G}
    (hy : y ∈ Group.conjugatesOfSet ({x} : Set G)) :
    y ∈ MulAction.stabilizer G (sylowClosureBlock x P) ↔
      y ∈ sylowConjugateClosure x P := by
  rw [stabilizer_sylowClosureBlock]
  exact conjugate_mem_normalizer_iff_mem_sylowConjugateClosure
    x h P hy

/-- Every two conjugates of `x` belong to a common Sylow-closure subgroup. -/
theorem exists_sylow_mem_sylowConjugateClosure_of_pair
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (x : G)
    (h : ∀ g : G, IsPGroup p
      (Subgroup.closure ({x, g * x * g⁻¹} : Set G)))
    {y z : G}
    (hy : y ∈ Group.conjugatesOfSet ({x} : Set G))
    (hz : z ∈ Group.conjugatesOfSet ({x} : Set G)) :
    ∃ P : Sylow p G,
      y ∈ sylowConjugateClosure x P ∧
        z ∈ sylowConjugateClosure x P := by
  obtain ⟨a, ha⟩ : ∃ a : G, a * x * a⁻¹ = y := by
    obtain ⟨w, hw, hwy⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    rw [Set.mem_singleton_iff] at hw
    subst w
    obtain ⟨a, ha⟩ := isConj_iff.mp hwy
    exact ⟨a, ha⟩
  obtain ⟨b, hb⟩ : ∃ b : G, b * x * b⁻¹ = z := by
    obtain ⟨w, hw, hwz⟩ := Group.mem_conjugatesOfSet_iff.mp hz
    rw [Set.mem_singleton_iff] at hw
    subst w
    obtain ⟨b, hb⟩ := isConj_iff.mp hwz
    exact ⟨b, hb⟩
  have hp :
      IsPGroup p (Subgroup.closure ({y, z} : Set G)) := by
    rw [← ha, ← hb]
    exact conjugatePair_isPGroup_of_pairwise x h a b
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  refine ⟨P, ?_, ?_⟩
  · apply Subgroup.subset_closure
    exact
      ⟨hy, hP (Subgroup.subset_closure (by simp))⟩
  · apply Subgroup.subset_closure
    exact
      ⟨hz, hP (Subgroup.subset_closure (by simp))⟩

end Submission.Helpers
