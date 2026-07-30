import Submission.OddOrder.BG.AppendixAB.LocalRestrictionKernelSylowLift

/-!
Cyclic q-subgroups lifted from local restriction kernels.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- A prime-order element of the local derived restriction kernel has a
preimage whose cyclic subgroup is q-primary and centralizes the smaller
invariant subgroup. -/
theorem exists_cyclic_sylow_preimage_of_mem_localDerivedRestrictionKernel
    {q : ℕ} [Fact q.Prime]
    {M E : Subgroup G} (hME : M ≤ E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G))
    (a : localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM)
    (haorder : orderOf a = q) :
    ∃ (P : Sylow q (pairGenerated x y)) (g : pairGenerated x y),
      g ∈ P ∧
      pairGeneratedLocalQuotientHom E hxNE hyNE g =
        ((a : _root_.commutator (localQuotientPair E hxNE hyNE)) :
          localQuotientPair E hxNE hyNE) ∧
      IsPGroup q (Subgroup.zpowers (g : G)) ∧
      Subgroup.zpowers (g : G) ≤ Subgroup.centralizer (M : Set G) := by
  obtain ⟨P, g, hgP, hga, hgM⟩ :=
    exists_sylow_preimage_of_mem_localDerivedRestrictionKernel
      hME hxNE hyNE hxNM hyNM a haorder
  have hgqP : IsPElement q (⟨g, hgP⟩ : P) := P.isPGroup' ⟨g, hgP⟩
  have hgqPair : IsPElement q g :=
    IsPElement.map (P : Subgroup (pairGenerated x y)).subtype hgqP
  have hgqG : IsPElement q (g : G) :=
    IsPElement.map (pairGenerated x y).subtype hgqPair
  have hgCentralizesM : (g : G) ∈ Subgroup.centralizer (M : Set G) := by
    rw [← mem_ker_pairGeneratedLocalQuotientHom_iff M hxNM hyNM]
    exact MonoidHom.mem_ker.mpr hgM
  refine ⟨P, g, hgP, hga, hgqG.zpowers_isPGroup, ?_⟩
  rw [Subgroup.zpowers_le]
  exact hgCentralizesM

end Submission.OddOrder.BG.AppendixAB
