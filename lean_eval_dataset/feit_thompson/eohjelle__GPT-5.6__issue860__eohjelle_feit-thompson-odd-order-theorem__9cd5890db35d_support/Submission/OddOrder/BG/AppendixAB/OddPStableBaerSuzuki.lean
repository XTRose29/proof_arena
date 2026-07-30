import Submission.OddOrder.BG.AppendixAB.TwoGenerator
import Submission.OddOrder.MathlibSupport.BaerSuzuki

/-!
The Baer-Suzuki wrapper in the proof of odd-order p-stability.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G] [Finite G]

/-- The local two-generator conclusion used by `odd_p_stable`: two quadratic
p-elements normalizing `E` generate a p-group modulo `C(E)`. -/
def OddQuadraticPairPrinciple (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ (E : Subgroup G) (x y : G)
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G)),
    Odd (Nat.card (pairGenerated x y)) →
    IsPGroup p E →
    IsQuadraticPElement p E x → IsQuadraticPElement p E y →
    IsPGroup p
      (pairGenerated
        (QuotientGroup.mk' (normalizerCentralizer E) ⟨x, hxN⟩)
        (QuotientGroup.mk' (normalizerCentralizer E) ⟨y, hyN⟩))

/-- Once the local quadratic-pair principle is known, Baer-Suzuki gives
p-stability for an odd-order finite group. -/
theorem isPStable_of_odd_quadraticPairPrinciple {p : ℕ} [Fact p.Prime]
    (hodd : Odd (Nat.card G)) (hpair : OddQuadraticPairPrinciple p G) :
    IsPStable p G := by
  intro P A hP _ hA hAN hquadratic z hz
  let N : Subgroup G := Subgroup.normalizer (P : Set G)
  let C : Subgroup N := normalizerCentralizer P
  let q : N →* N ⧸ C := QuotientGroup.mk' C
  change z ∈ (A.subgroupOf N).map q at hz
  obtain ⟨a, haA, rfl⟩ := hz
  apply baer_suzuki
  intro g
  obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective C g
  let x : G := a
  let y : G := (n : G) * x * (n : G)⁻¹
  have hxN : x ∈ N := a.property
  have hnN : (n : G) ∈ N := n.property
  have hyN : y ∈ N := N.mul_mem (N.mul_mem hnN hxN) (N.inv_mem hnN)
  have hxA : x ∈ A := haA
  have hxquad : IsQuadraticPElement p P x :=
    isQuadraticPElement_of_mem_isPGroup_of_commutator_commutator_eq_bot
      hA hxA hquadratic
  have hyquad : IsQuadraticPElement p P y :=
    hxquad.conj_of_mem_normalizer hnN
  have hp := hpair P x y hxN hyN
    (odd_natCard_pairGenerated hodd) hP hxquad hyquad
  have hxa : (⟨x, hxN⟩ : N) = a := Subtype.ext rfl
  have hyn : (⟨y, hyN⟩ : N) = n * a * n⁻¹ := Subtype.ext rfl
  rw [hxa, hyn] at hp
  rw [map_mul, map_mul, map_inv] at hp
  change IsPGroup p
    (pairGenerated
      ((QuotientGroup.mk' (normalizerCentralizer P)) a)
      ((QuotientGroup.mk' (normalizerCentralizer P)) n *
        (QuotientGroup.mk' (normalizerCentralizer P)) a *
        ((QuotientGroup.mk' (normalizerCentralizer P)) n)⁻¹))
  exact hp

end Submission.OddOrder.BG.AppendixAB
