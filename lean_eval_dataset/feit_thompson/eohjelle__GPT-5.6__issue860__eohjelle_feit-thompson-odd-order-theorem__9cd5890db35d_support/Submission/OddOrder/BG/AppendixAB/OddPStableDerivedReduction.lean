import Submission.OddOrder.BG.AppendixAB.OddPStableBaerSuzuki
import Submission.OddOrder.BG.AppendixAB.PGroupDerivedReduction

/-!
Reduction of the odd quadratic-pair principle to a derived subgroup.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- The representation-theoretic core needed for odd p-stability: the
derived subgroup of each local two-generator quotient is a p-group. -/
def OddQuadraticDerivedPrinciple (p : ℕ) (G : Type*)
    [Group G] [Finite G] : Prop :=
  ∀ (E : Subgroup G) (x y : G)
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)),
    Odd (Nat.card (pairGenerated x y)) →
    IsPGroup p E →
    IsQuadraticPElement p E x → IsQuadraticPElement p E y →
    let Q :=
      pairGenerated
        (QuotientGroup.mk' (normalizerCentralizer E) ⟨x, hxN⟩)
        (QuotientGroup.mk' (normalizerCentralizer E) ⟨y, hyN⟩)
    IsPGroup p (_root_.commutator Q)

theorem oddQuadraticPairPrinciple_of_derivedPrinciple
    {p : ℕ} [Fact p.Prime]
    (hderived : OddQuadraticDerivedPrinciple p G) :
    OddQuadraticPairPrinciple p G := by
  intro E x y hxN hyN hodd hE hx hy
  let q := QuotientGroup.mk' (normalizerCentralizer E)
  let xq := q ⟨x, hxN⟩
  let yq := q ⟨y, hyN⟩
  let Q := pairGenerated xq yq
  let xQ : Q := ⟨xq, mem_pairGenerated_left xq yq⟩
  let yQ : Q := ⟨yq, mem_pairGenerated_right xq yq⟩
  have hgen : pairGenerated xQ yQ = ⊤ := by
    rw [pairGenerated_subtype]
    change Q.comap Q.subtype = ⊤
    ext z
    simp
  have hxNelt : IsPElement p
      (⟨x, hxN⟩ : Subgroup.normalizer (E : Set G)) :=
    IsPElement.of_map_of_injective
      (Subgroup.normalizer (E : Set G)).subtype
      (Subgroup.normalizer (E : Set G)).subtype_injective hx.1
  have hyNelt : IsPElement p
      (⟨y, hyN⟩ : Subgroup.normalizer (E : Set G)) :=
    IsPElement.of_map_of_injective
      (Subgroup.normalizer (E : Set G)).subtype
      (Subgroup.normalizer (E : Set G)).subtype_injective hy.1
  have hxq : IsPElement p xq := hxNelt.map q
  have hyq : IsPElement p yq := hyNelt.map q
  have hxQ : IsPElement p xQ :=
    IsPElement.of_map_of_injective Q.subtype Q.subtype_injective hxq
  have hyQ : IsPElement p yQ :=
    IsPElement.of_map_of_injective Q.subtype Q.subtype_injective hyq
  have hder : IsPGroup p (_root_.commutator Q) :=
    hderived E x y hxN hyN hodd hE hx hy
  exact isPGroup_of_pairGenerated_eq_top_of_commutator_isPGroup
    hgen hxQ hyQ hder

end Submission.OddOrder.BG.AppendixAB
