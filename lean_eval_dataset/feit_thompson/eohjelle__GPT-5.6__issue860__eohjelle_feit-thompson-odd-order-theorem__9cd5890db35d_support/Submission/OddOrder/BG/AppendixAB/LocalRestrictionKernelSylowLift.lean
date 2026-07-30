import Submission.OddOrder.BG.AppendixAB.LocalQuotientPairRestrictionPrimeOrder
import Submission.OddOrder.MathlibSupport.SylowSurjectiveElementLift

/-!
Sylow lifts of cross-prime elements in local restriction kernels.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- A prime-order element of the local derived restriction kernel lifts to
an element of a Sylow subgroup of `pairGenerated x y`, and that lift acts
trivially on the smaller invariant subgroup. -/
theorem exists_sylow_preimage_of_mem_localDerivedRestrictionKernel
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
      pairGeneratedLocalQuotientHom M hxNM hyNM g = 1 := by
  let D := _root_.commutator (localQuotientPair E hxNE hyNE)
  let K := localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM
  let aE : localQuotientPair E hxNE hyNE := ((a : D) : _)
  have haorderE : orderOf aE = q := by
    calc
      orderOf aE = orderOf (a : D) :=
        orderOf_injective D.subtype D.subtype_injective (a : D)
      _ = orderOf a :=
        orderOf_injective K.subtype K.subtype_injective a
      _ = q := haorder
  have haP : IsPElement q aE := by
    refine ⟨1, ?_⟩
    simpa [haorderE] using pow_orderOf_eq_one aE
  obtain ⟨P, g, hgP, hga⟩ := exists_sylow_preimage_of_isPElement
    (pairGeneratedLocalQuotientHom E hxNE hyNE)
    (pairGeneratedLocalQuotientHom_surjective E hxNE hyNE) haP
  refine ⟨P, g, hgP, hga, ?_⟩
  have haKer :
      localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM aE = 1 :=
    MonoidHom.mem_ker.mp a.property
  have hcomp := DFunLike.congr_fun
    (localQuotientPairRestrictionHom_comp
      hME hxNE hyNE hxNM hyNM) g
  calc
    pairGeneratedLocalQuotientHom M hxNM hyNM g =
        localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM
          (pairGeneratedLocalQuotientHom E hxNE hyNE g) := hcomp.symm
    _ = localQuotientPairRestrictionHom hME hxNE hyNE hxNM hyNM aE :=
      congrArg _ hga
    _ = 1 := haKer

end Submission.OddOrder.BG.AppendixAB
