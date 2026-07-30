import ChallengeDeps
import Submission.OddOrder.MathlibSupport.BaerSuzuki

open LeanEval.GroupTheory
open LeanEval.GroupTheory.Defs

namespace Submission

/-- The Baer–Suzuki theorem, stated using the challenge's `pCore`. -/
theorem baer_suzuki {G : Type*} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] (x : G) :
    x ∈ pCore p G ↔
      ∀ g : G, IsPGroup p
        (Subgroup.closure ({x, g * x * g⁻¹} : Set G)) := by
  have hpCore :
      LeanEval.GroupTheory.Defs.pCore p G =
        OddOrder.MathlibSupport.pCore p G := by
    unfold LeanEval.GroupTheory.Defs.pCore OddOrder.MathlibSupport.pCore
    congr 1
    ext P
    simp only [Set.mem_setOf_eq]
    exact and_comm
  have hpairGenerated (a b : G) :
      OddOrder.BG.AppendixAB.pairGenerated a b =
        Subgroup.closure ({a, b} : Set G) := by
    apply le_antisymm
    · exact OddOrder.BG.AppendixAB.pairGenerated_le_iff.mpr
        ⟨Subgroup.subset_closure (by simp),
          Subgroup.subset_closure (by simp)⟩
    · rw [Subgroup.closure_le]
      intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with hy | hy
      · rw [hy]
        exact OddOrder.BG.AppendixAB.mem_pairGenerated_left a b
      · simpa only [Set.mem_singleton_iff] using
          hy ▸ OddOrder.BG.AppendixAB.mem_pairGenerated_right a b
  rw [hpCore]
  constructor
  · intro hx g
    have hconj :
        g * x * g⁻¹ ∈ OddOrder.MathlibSupport.pCore p G :=
      (show (OddOrder.MathlibSupport.pCore p G).Normal from inferInstance).conj_mem
        x hx g
    have hpairs : IsPGroup p
        (OddOrder.BG.AppendixAB.pairGenerated x (g * x * g⁻¹)) :=
      OddOrder.BG.AppendixAB.pairGenerated_isPGroup_of_mem
        OddOrder.MathlibSupport.pCore_isPGroup hx hconj
    rw [hpairGenerated] at hpairs
    exact hpairs
  · intro hpairs
    apply OddOrder.MathlibSupport.baer_suzuki
    intro g
    rw [hpairGenerated]
    exact hpairs g

end Submission
