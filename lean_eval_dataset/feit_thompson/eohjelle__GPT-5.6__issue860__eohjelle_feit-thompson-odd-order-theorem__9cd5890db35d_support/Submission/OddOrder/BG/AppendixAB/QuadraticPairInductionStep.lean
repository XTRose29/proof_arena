import Submission.OddOrder.BG.AppendixAB.LocalQuotientPairCrossPrime
import Submission.OddOrder.BG.AppendixAB.QuadraticPairInvariantQuotient
import Submission.OddOrder.MathlibSupport.PairGeneratedSubtype

/-!
The proper invariant-quotient step in the odd quadratic-pair induction.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.MathlibSupport
open scoped commutatorElement

universe u

/-- The local quadratic-pair conclusion for acted-on subgroups whose
cardinality is strictly below `n`. -/
def OddQuadraticLocalPrincipleBelow (p n : ℕ) : Prop :=
  ∀ (K : Type u) [Group K] [Finite K]
    (E : Subgroup K) (x y : K)
    (hxN : x ∈ Subgroup.normalizer (E : Set K))
    (hyN : y ∈ Subgroup.normalizer (E : Set K)),
    Nat.card E < n →
      Odd (Nat.card (pairGenerated x y)) →
      IsPGroup p E →
      IsQuadraticPElement p E x →
      IsQuadraticPElement p E y →
      IsPGroup p (localQuotientPair E hxN hyN)

variable {G : Type u} [Group G] [Finite G]

/-- In the proper invariant-quotient branch, every cross-prime subgroup of
the pair-generated group centralizes `E` modulo the invariant subgroup `D`.
-/
theorem commutator_le_of_quadraticPair_invariantQuotient
    {p q : ℕ} [Fact p.Prime] [Fact q.Prime] (hpq : p ≠ q)
    {D E A : Subgroup G} {x y : G}
    (hDE : D ≤ E) (hD : D ≠ ⊥)
    (hED : E ≤ Subgroup.normalizer (D : Set G))
    (hxND : x ∈ Subgroup.normalizer (D : Set G))
    (hyND : y ∈ Subgroup.normalizer (D : Set G))
    (hxNE : x ∈ Subgroup.normalizer (E : Set G))
    (hyNE : y ∈ Subgroup.normalizer (E : Set G))
    (hodd : Odd (Nat.card (pairGenerated x y)))
    (hE : IsPGroup p E)
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y)
    (hAxy : A ≤ pairGenerated x y) (hAq : IsPGroup q A)
    (hIH : OddQuadraticLocalPrincipleBelow.{u} p (Nat.card E)) :
    ⁅A, E⁆ ≤ D := by
  let J : Subgroup G := pairExtension E x y
  let DJ : Subgroup J := D.subgroupOf J
  let EJ : Subgroup J := E.subgroupOf J
  let xJ : J := pairExtensionLeft E x y
  let yJ : J := pairExtensionRight E x y
  letI : DJ.Normal := pairExtension_subgroupOf_normal hED hxND hyND
  let qJ : J →* J ⧸ DJ := QuotientGroup.mk' DJ
  let Eq : Subgroup (J ⧸ DJ) := EJ.map qJ
  let xq : J ⧸ DJ := qJ xJ
  let yq : J ⧸ DJ := qJ yJ
  obtain ⟨hxNq, hyNq, hoddq, hEq, hxq, hyq, hcardq⟩ :=
    quadraticPair_invariantQuotient hDE hD hED hxND hyND
      hxNE hyNE hodd hE hx hy
  have hlocal : IsPGroup p (localQuotientPair Eq hxNq hyNq) :=
    hIH (J ⧸ DJ) Eq xq yq hxNq hyNq hcardq
      hoddq hEq hxq hyq
  have hAJ : A ≤ J :=
    hAxy.trans (pairGenerated_le_pairExtension E x y)
  let AJ : Subgroup J := A.subgroupOf J
  let Aq : Subgroup (J ⧸ DJ) := AJ.map qJ
  have hAJq : IsPGroup q AJ :=
    hAq.of_equiv (Subgroup.subgroupOfEquivOfLe hAJ).symm
  have hAqq : IsPGroup q Aq := hAJq.map qJ
  have hAJpair : AJ ≤ pairGenerated xJ yJ := by
    intro a ha
    rw [pairGenerated_subtype]
    exact hAxy ha
  have hAqPair : Aq ≤ pairGenerated xq yq := by
    rw [← pairGenerated_map_hom qJ xJ yJ]
    exact Subgroup.map_mono hAJpair
  have hAqCent : Aq ≤ Subgroup.centralizer (Eq : Set (J ⧸ DJ)) :=
    crossPrime_subgroup_le_centralizer_of_localQuotientPair_isPGroup
      hpq hxNq hyNq hAqPair hAqq hlocal
  apply Subgroup.commutator_le.mpr
  intro a ha e he
  let aJ : J := ⟨a, hAJ ha⟩
  let eJ : J := ⟨e, le_pairExtension E x y he⟩
  have hqa : qJ aJ ∈ Aq := by
    refine ⟨aJ, ?_, rfl⟩
    exact ha
  have hqe : qJ eJ ∈ Eq := by
    exact ⟨eJ, he, rfl⟩
  have hcomm : qJ aJ * qJ eJ = qJ eJ * qJ aJ :=
    (Subgroup.mem_centralizer_iff.mp (hAqCent hqa) (qJ eJ) hqe).symm
  have hqcommOne : qJ ⁅aJ, eJ⁆ = 1 := by
    rw [map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.mpr hcomm
  have hmemDJ : ⁅aJ, eJ⁆ ∈ DJ :=
    (QuotientGroup.eq_one_iff (N := DJ) ⁅aJ, eJ⁆).mp hqcommOne
  exact hmemDJ

end Submission.OddOrder.BG.AppendixAB
