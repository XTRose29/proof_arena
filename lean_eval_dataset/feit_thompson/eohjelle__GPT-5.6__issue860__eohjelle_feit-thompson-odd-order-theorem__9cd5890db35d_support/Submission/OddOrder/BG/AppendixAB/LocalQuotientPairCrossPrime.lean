import Submission.OddOrder.BG.AppendixAB.PairGeneratedLocalQuotientHom
import Submission.OddOrder.MathlibSupport.CrossPrimeHomKernel
import Submission.OddOrder.MathlibSupport.NormalizerQuotientConjugation

/-!
Cross-prime subgroups acting through a p-primary local quotient pair.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The local quotient pair acts faithfully on the subgroup by conjugation. -/
def localQuotientPairConjugationHom
    (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    localQuotientPair E hxN hyN →* MulAut E :=
  (normalizerQuotientConjugationHom E).comp
    (localQuotientPair E hxN hyN).subtype

theorem localQuotientPairConjugationHom_injective
    (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    Function.Injective (localQuotientPairConjugationHom E hxN hyN) :=
  (normalizerQuotientConjugationHom_injective E).comp
    (localQuotientPair E hxN hyN).subtype_injective

theorem localQuotientPairConjugationHom_ker_eq_bot
    (E : Subgroup G) {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)) :
    (localQuotientPairConjugationHom E hxN hyN).ker = ⊥ :=
  MonoidHom.ker_eq_bot _
    (localQuotientPairConjugationHom_injective E hxN hyN)

/-- If the local quotient pair is p-primary, every q-subgroup of the
pair-generated ambient subgroup centralizes `E` for `q != p`. -/
theorem crossPrime_subgroup_le_centralizer_of_localQuotientPair_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {E A : Subgroup G} {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hAxy : A ≤ pairGenerated x y) (hAq : IsPGroup q A)
    (hlocal : IsPGroup p (localQuotientPair E hxN hyN)) :
    A ≤ Subgroup.centralizer (E : Set G) := by
  let f : A →* localQuotientPair E hxN hyN :=
    (pairGeneratedLocalQuotientHom E hxN hyN).comp
      (Subgroup.inclusion hAxy)
  intro a ha
  let aPair : pairGenerated x y := ⟨a, hAxy ha⟩
  have hfOne : f ⟨a, ha⟩ = 1 :=
    apply_eq_one_of_isPGroup f hpq hAq hlocal ⟨a, ha⟩
  have haKer :
      aPair ∈ (pairGeneratedLocalQuotientHom E hxN hyN).ker := by
    apply MonoidHom.mem_ker.mpr
    have hpair : Subgroup.inclusion hAxy ⟨a, ha⟩ = aPair :=
      Subtype.ext rfl
    change pairGeneratedLocalQuotientHom E hxN hyN
      (Subgroup.inclusion hAxy ⟨a, ha⟩) = 1 at hfOne
    rwa [hpair] at hfOne
  exact (mem_ker_pairGeneratedLocalQuotientHom_iff
    E hxN hyN aPair).mp haKer

/-- Elementwise form of the cross-prime centralization result. -/
theorem crossPrime_mem_centralizer_of_localQuotientPair_isPGroup
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {E A : Subgroup G} {x y a : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hAxy : A ≤ pairGenerated x y) (hAq : IsPGroup q A)
    (ha : a ∈ A)
    (hlocal : IsPGroup p (localQuotientPair E hxN hyN)) :
    a ∈ Subgroup.centralizer (E : Set G) :=
  crossPrime_subgroup_le_centralizer_of_localQuotientPair_isPGroup
    hpq hxN hyN hAxy hAq hlocal ha

end Submission.OddOrder.BG.AppendixAB
