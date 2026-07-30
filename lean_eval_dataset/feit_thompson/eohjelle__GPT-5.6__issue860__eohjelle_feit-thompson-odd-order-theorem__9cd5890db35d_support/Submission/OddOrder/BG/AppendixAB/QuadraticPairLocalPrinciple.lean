import Submission.OddOrder.BG.AppendixAB.LocalMinimalNormalPairOddBranch
import Submission.OddOrder.BG.AppendixAB.QuadraticPairMinimality
import Submission.OddOrder.BG.AppendixAB.PGroupDerivedReduction
import Submission.OddOrder.MathlibSupport.PGroupPrimeOrderCriterion
import Submission.OddOrder.MathlibSupport.SylowSurjectiveElementLift

/-!
Strong-induction closure of the local odd quadratic-pair principle.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport
open scoped commutatorElement IsMulCommutative

universe u

variable {G : Type u} [Group G] [Finite G]

/-- Once the local derived subgroup is p-primary, the distinguished
p-element generators make the whole local quotient pair p-primary. -/
theorem localQuotientPair_isPGroup_of_commutator_isPGroup
    {p : ℕ} [Fact p.Prime]
    {E : Subgroup G} {x y : G}
    (hxN : x ∈ Subgroup.normalizer (E : Set G))
    (hyN : y ∈ Subgroup.normalizer (E : Set G))
    (hx : IsPElement p x) (hy : IsPElement p y)
    (hder : IsPGroup p
      (_root_.commutator (localQuotientPair E hxN hyN))) :
    IsPGroup p (localQuotientPair E hxN hyN) := by
  let N : Subgroup G := Subgroup.normalizer (E : Set G)
  let qN : N →* N ⧸ normalizerCentralizer E :=
    QuotientGroup.mk' (normalizerCentralizer E)
  let xQ : localQuotientPair E hxN hyN :=
    localQuotientPairLeft E hxN hyN
  let yQ : localQuotientPair E hxN hyN :=
    localQuotientPairRight E hxN hyN
  have hxNelt : IsPElement p (⟨x, hxN⟩ : N) :=
    IsPElement.of_map_of_injective N.subtype N.subtype_injective hx
  have hyNelt : IsPElement p (⟨y, hyN⟩ : N) :=
    IsPElement.of_map_of_injective N.subtype N.subtype_injective hy
  have hxQ : IsPElement p xQ := by
    apply IsPElement.of_map_of_injective
      (localQuotientPair E hxN hyN).subtype
      (localQuotientPair E hxN hyN).subtype_injective
    exact hxNelt.map qN
  have hyQ : IsPElement p yQ := by
    apply IsPElement.of_map_of_injective
      (localQuotientPair E hxN hyN).subtype
      (localQuotientPair E hxN hyN).subtype_injective
    exact hyNelt.map qN
  exact isPGroup_of_pairGenerated_eq_top_of_commutator_isPGroup
    (pairGenerated_localQuotientPair_eq_top E hxN hyN) hxQ hyQ hder

/-- The local quadratic-pair conclusion for every finite group of the chosen
universe. This is the strong-cardinality induction at the core of
`odd_p_stable`. -/
theorem oddQuadraticLocalPrinciple
    {p : ℕ} [Fact p.Prime]
    (K : Type u) [Group K] [Finite K]
    (E : Subgroup K) (x y : K)
    (hxN : x ∈ Subgroup.normalizer (E : Set K))
    (hyN : y ∈ Subgroup.normalizer (E : Set K))
    (hodd : Odd (Nat.card (pairGenerated x y)))
    (hE : IsPGroup p E)
    (hx : IsQuadraticPElement p E x)
    (hy : IsQuadraticPElement p E y) :
    IsPGroup p (localQuotientPair E hxN hyN) := by
  let P : ℕ → Prop := fun n ↦
    ∀ (L : Type u) [Group L] [Finite L]
      (D : Subgroup L) (a b : L)
      (haN : a ∈ Subgroup.normalizer (D : Set L))
      (hbN : b ∈ Subgroup.normalizer (D : Set L)),
      Nat.card D = n →
        Odd (Nat.card (pairGenerated a b)) →
        IsPGroup p D →
        IsQuadraticPElement p D a →
        IsQuadraticPElement p D b →
        IsPGroup p (localQuotientPair D haN hbN)
  have hP : ∀ n, P n := by
    intro n
    induction n using Nat.strong_induction_on with
    | h n ih =>
        dsimp only [P]
        intro L _ _ D a b haN hbN hcard hoddD hDp ha hb
        have hIH : OddQuadraticLocalPrincipleBelow.{u} p (Nat.card D) := by
          intro M _ _ F c d hcN hdN hlt hoddF hFp hc hd
          have hlt' : Nat.card F < n := by
            simpa [hcard] using hlt
          exact ih (Nat.card F) hlt' M F c d hcN hdN rfl
            hoddF hFp hc hd
        apply isPGroup_of_prime_order_elements
        intro q hq hqp z hzOrder
        letI : Fact q.Prime := ⟨hq⟩
        by_cases hzOne : z = 1
        · exact hzOne
        have hzq : IsPElement q z := by
          refine ⟨1, ?_⟩
          simpa [hzOrder] using pow_orderOf_eq_one z
        obtain ⟨Q, g, hgQ, hgz⟩ :=
          exists_sylow_preimage_of_isPElement
            (pairGeneratedLocalQuotientHom D haN hbN)
            (pairGeneratedLocalQuotientHom_surjective D haN hbN) hzq
        let A : Subgroup L := Subgroup.zpowers (g : L)
        have hgqQ : IsPElement q (⟨g, hgQ⟩ : Q) :=
          Q.isPGroup' ⟨g, hgQ⟩
        have hgqPair : IsPElement q g :=
          hgqQ.map (Q : Subgroup (pairGenerated a b)).subtype
        have hgqL : IsPElement q (g : L) :=
          hgqPair.map (pairGenerated a b).subtype
        have hAq : IsPGroup q A := hgqL.zpowers_isPGroup
        have hApair : A ≤ pairGenerated a b := by
          rw [Subgroup.zpowers_le]
          exact g.property
        have hAnot : ¬A ≤ Subgroup.centralizer (D : Set L) := by
          intro hcent
          have hgCent : (g : L) ∈ Subgroup.centralizer (D : Set L) :=
            hcent (Subgroup.mem_zpowers (g : L))
          have hgOne : pairGeneratedLocalQuotientHom D haN hbN g = 1 :=
            MonoidHom.mem_ker.mp
              ((mem_ker_pairGeneratedLocalQuotientHom_iff
                D haN hbN g).mpr hgCent)
          exact hzOne (hgz.symm.trans hgOne)
        have hminJ : IsMinimalNormalUnder D (pairExtension D a b) :=
          isMinimalNormalUnder_pairExtension_of_crossPrime_not_centralizer
            (Ne.symm hqp) haN hbN hoddD hDp ha hb
              hApair hAq hAnot hIH
        have habel := hminJ.isElementaryAbelian_of_isPGroup hDp
        letI : IsMulCommutative D := habel.1
        have hminPair : IsMinimalNormalUnder D (pairGenerated a b) := by
          refine ⟨hminJ.ne_bot, pairGenerated_le_normalizer haN hbN, ?_⟩
          intro F hFD hF hFinv
          have hpairNF : pairGenerated a b ≤
              Subgroup.normalizer (F : Set L) :=
            Subgroup.le_normalizer_iff.mpr hFinv
          have hDNF : D ≤ Subgroup.normalizer (F : Set L) := by
            rw [Subgroup.le_normalizer_iff_commutator_le_right]
            apply Subgroup.commutator_le.mpr
            intro d hd f hf
            have hcomm : d * f = f * d := by
              have hcommD :
                  (⟨d, hd⟩ : D) * ⟨f, hFD hf⟩ =
                    ⟨f, hFD hf⟩ * ⟨d, hd⟩ :=
                mul_comm _ _
              exact congrArg Subtype.val hcommD
            rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
            exact F.one_mem
          apply hminJ.2.2 F hFD hF
          exact Subgroup.le_normalizer_iff.mp (sup_le hDNF hpairNF)
        have hder : IsPGroup p
            (_root_.commutator (localQuotientPair D haN hbN)) :=
          local_commutator_isPGroup_of_minimalNormalUnder_pair_odd
            D p hDp haN hbN ha hb hoddD hminPair
        have hlocal : IsPGroup p (localQuotientPair D haN hbN) :=
          localQuotientPair_isPGroup_of_commutator_isPGroup
            haN hbN ha.1 hb.1 hder
        let Zq : Subgroup (localQuotientPair D haN hbN) :=
          Subgroup.zpowers z
        have hzEqOne := apply_eq_one_of_isPGroup
          Zq.subtype (Ne.symm hqp) hzq.zpowers_isPGroup hlocal
            (⟨z, Subgroup.mem_zpowers z⟩ : Zq)
        exact hzEqOne
  exact hP (Nat.card E) K E x y hxN hyN rfl hodd hE hx hy

end Submission.OddOrder.BG.AppendixAB
