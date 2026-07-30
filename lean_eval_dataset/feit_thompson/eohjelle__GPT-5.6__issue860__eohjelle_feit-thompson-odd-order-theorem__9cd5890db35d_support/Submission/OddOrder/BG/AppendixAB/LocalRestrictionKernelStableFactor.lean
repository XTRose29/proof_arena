import Submission.OddOrder.BG.AppendixAB.LocalRestrictionKernelCyclicLift
import Submission.OddOrder.MathlibSupport.StableFactor

/-!
Stable-factor elimination of cross-prime local restriction kernels.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement

variable {G : Type*} [Group G] [Finite G]

/-- A cross-prime element of the local derived restriction kernel is trivial
once a lifted cyclic subgroup acts trivially on the factor `E / M`. -/
theorem localDerivedRestrictionKernel_eq_one_of_cyclic_factor
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hqp : q ≠ p)
    {M E : Subgroup G} (hME : M ≤ E) (hE : IsPGroup p E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G))
    (a : localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM)
    (haorder : orderOf a = q)
    (hfactor : ∀ g : pairGenerated x y,
      pairGeneratedLocalQuotientHom E hxNE hyNE g =
        ((a : _root_.commutator (localQuotientPair E hxNE hyNE)) :
          localQuotientPair E hxNE hyNE) →
      ⁅Subgroup.zpowers (g : G), E⁆ ≤ M) :
    a = 1 := by
  obtain ⟨P, g, hgP, hga, hgq, hgM⟩ :=
    exists_cyclic_sylow_preimage_of_mem_localDerivedRestrictionKernel
      hME hxNE hyNE hxNM hyNM a haorder
  let A : Subgroup G := Subgroup.zpowers (g : G)
  have hcoprime : Nat.Coprime (Nat.card E) (Nat.card A) := by
    exact IsPGroup.coprime_card_of_ne p q (Ne.symm hqp) E A hE hgq
  have hAE : A ≤ Subgroup.centralizer (E : Set G) := by
    apply stableFactor_centralizes hgM hME (hfactor g hga) hcoprime
  have hgCentralizesE : (g : G) ∈ Subgroup.centralizer (E : Set G) :=
    hAE (Subgroup.mem_zpowers (g : G))
  have hgKer :
      g ∈ (pairGeneratedLocalQuotientHom E hxNE hyNE).ker := by
    rw [mem_ker_pairGeneratedLocalQuotientHom_iff]
    exact hgCentralizesE
  have hgOne : pairGeneratedLocalQuotientHom E hxNE hyNE g = 1 :=
    MonoidHom.mem_ker.mp hgKer
  have haOne :
      (((a : _root_.commutator (localQuotientPair E hxNE hyNE)) :
        localQuotientPair E hxNE hyNE)) = 1 :=
    hga.symm.trans hgOne
  apply Subtype.ext
  apply Subtype.ext
  exact haOne

/-- The local derived restriction kernel is p-primary once every lifted
cross-prime cyclic subgroup acts trivially on the corresponding factor. -/
theorem localDerivedRestrictionKernel_isPGroup_of_cyclic_factor
    {p : ℕ} [Fact p.Prime]
    {M E : Subgroup G} (hME : M ≤ E) (hE : IsPGroup p E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G))
    (hfactor : ∀ (q : ℕ), q.Prime → q ≠ p →
      ∀ a : localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM,
        orderOf a = q →
        ∀ g : pairGenerated x y,
          pairGeneratedLocalQuotientHom E hxNE hyNE g =
            ((a : _root_.commutator (localQuotientPair E hxNE hyNE)) :
              localQuotientPair E hxNE hyNE) →
          ⁅Subgroup.zpowers (g : G), E⁆ ≤ M) :
    IsPGroup p
      (localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM) := by
  apply localDerivedRestrictionKernel_isPGroup_of_prime_order_elements
  intro q hq hqp a haorder
  letI : Fact q.Prime := ⟨hq⟩
  exact localDerivedRestrictionKernel_eq_one_of_cyclic_factor
    hqp hME hE hxNE hyNE hxNM hyNM a haorder
      (hfactor q hq hqp a haorder)

/-- Stable-factor elimination of the restriction kernel lifts a p-primary
result from the smaller local derived subgroup to the larger one. -/
theorem local_commutator_isPGroup_of_cyclic_factor
    {p : ℕ} [Fact p.Prime]
    {M E : Subgroup G} (hME : M ≤ E) (hE : IsPGroup p E) {x y : G}
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hxNM : x ∈ Subgroup.normalizer (M : Set G))
    (hyNM : y ∈ Subgroup.normalizer (M : Set G))
    (hsmall : IsPGroup p
      (_root_.commutator (localQuotientPair M hxNM hyNM)))
    (hfactor : ∀ (q : ℕ), q.Prime → q ≠ p →
      ∀ a : localDerivedRestrictionKernel hME hxNE hyNE hxNM hyNM,
        orderOf a = q →
        ∀ g : pairGenerated x y,
          pairGeneratedLocalQuotientHom E hxNE hyNE g =
            ((a : _root_.commutator (localQuotientPair E hxNE hyNE)) :
              localQuotientPair E hxNE hyNE) →
          ⁅Subgroup.zpowers (g : G), E⁆ ≤ M) :
    IsPGroup p
      (_root_.commutator (localQuotientPair E hxNE hyNE)) := by
  apply local_commutator_isPGroup_of_restriction
    hME hxNE hyNE hxNM hyNM hsmall
  exact localDerivedRestrictionKernel_isPGroup_of_cyclic_factor
    hME hE hxNE hyNE hxNM hyNM hfactor

end Submission.OddOrder.BG.AppendixAB
