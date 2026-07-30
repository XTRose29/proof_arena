import Submission.OddOrder.BG.Section04.HuppertMaximalCyclic
import Submission.OddOrder.BG.Section04.QuotientOmegaOneRankTwo
import Submission.OddOrder.MathlibSupport.HuppertAbelian
import Submission.OddOrder.MathlibSupport.HuppertCentralKernel
import Submission.OddOrder.MathlibSupport.MetacyclicCentralExtension

/-!
Bender--Glauberman Proposition 4.11, due to Huppert.
-/

namespace Submission.OddOrder.BG.Section04

open Submission.OddOrder.MathlibSupport

noncomputable section

universe u

variable {p : ℕ} [Fact p.Prime]

/-- Cardinality-indexed form of Huppert's Proposition 4.11. -/
def HuppertMetacyclicStatement (p n : ℕ) : Prop :=
  ∀ (G : Type u) [Group G] [Finite G],
    Nat.card G = n →
    IsPGroup p G →
    3 < p →
    Nat.card (omegaOne p G) ≤ p ^ 2 →
    IsMetacyclic G

/-- Huppert's criterion holds at every finite group cardinality. -/
theorem huppertMetacyclicStatement_all (p n : ℕ) [Fact p.Prime] :
    HuppertMetacyclicStatement.{u} p n := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro G _ _ hGcard hG hp3 hOmega
      by_cases hcomm : IsMulCommutative G
      · letI : IsMulCommutative G := hcomm
        exact
          isMetacyclic_of_isMulCommutative_of_omegaOne_card_le_prime_sq
            hG hOmega
      · obtain ⟨T, hTnormal, hTcard, hTcenter, _hTDerived, hbranch⟩ :=
          exists_huppert_central_kernel hG hcomm
        letI : T.Normal := hTnormal
        have hTne : T ≠ ⊥ := by
          intro hTbot
          have hpone : p = 1 := by
            rw [← hTcard, hTbot]
            exact Subgroup.card_bot
          exact (Fact.out : p.Prime).ne_one hpone
        let Q := G ⧸ T
        have hQp : IsPGroup p Q := hG.to_quotient T
        have hQOmega : Nat.card (omegaOne p Q) ≤ p ^ 2 :=
          natCard_omegaOne_quotient_le_prime_sq hG hOmega hp3 T
        have hQcardLt : Nat.card Q < n := by
          simpa [Q, hGcard] using natCard_quotient_lt_of_ne_bot T hTne
        have hQmeta : IsMetacyclic Q :=
          ih (Nat.card Q) hQcardLt Q rfl hQp hp3 hQOmega
        rcases hbranch with hTpower | hPowerBot
        · exact
            isMetacyclic_of_central_prime_quotient_of_commutator_power
              T hTnormal hTcenter hTcard hQmeta hTpower
        · have hDerivedPow :
              ∀ d : G, d ∈ _root_.commutator G → d ^ p = 1 := by
            intro d hd
            let dD : _root_.commutator G := ⟨d, hd⟩
            have hdPower : d ^ p ∈
                (iteratedPowerSubgroup p 1 (_root_.commutator G)).map
                  (_root_.commutator G).subtype := by
              refine ⟨dD ^ p, ?_, rfl⟩
              simpa using pow_mem_iteratedPowerSubgroup p 1 dD
            rw [hPowerBot] at hdPower
            exact Subgroup.mem_bot.mp hdPower
          obtain ⟨X, hXnormal, hTX, hInnerCyclic, hOuterCyclic⟩ :=
            exists_normal_over_of_quotient_isMetacyclic
              G T hTnormal hQmeta
          letI : X.Normal := hXnormal
          let TX : Subgroup X := T.subgroupOf X
          letI : IsCyclic (X ⧸ TX) := by
            simpa [TX] using hInnerCyclic
          letI : IsCyclic (G ⧸ X) := hOuterCyclic
          obtain ⟨x, y, hDerivedEq, _hrCenter⟩ :=
            commutator_eq_zpowers_of_huppert_cyclic_tower
              hG T X hTX hTcenter hcomm hDerivedPow
          have hDerivedCyclic : IsCyclic (_root_.commutator G) := by
            rw [hDerivedEq]
            infer_instance
          have hpOdd : Odd p :=
            (Fact.out : p.Prime).odd_of_ne_two (by omega)
          obtain ⟨k, hk⟩ := hG.exists_card_eq
          have hGodd : Odd (Nat.card G) := by
            rw [hk]
            exact hpOdd.pow
          exact
            isMetacyclic_of_commutator_isCyclic_of_omegaOne_card_le_prime_sq
              hG hGodd hOmega hDerivedCyclic

/-- `BGsection4.v: p2_Ohm1_metacyclic` (Bender--Glauberman Proposition
4.11, due to Huppert).  For a prime above three, a finite `p`-group whose
first omega subgroup has cardinality at most `p²` is metacyclic. -/
theorem isMetacyclic_of_omegaOne_card_le_prime_sq
    {G : Type u} [Group G] [Finite G]
    (hG : IsPGroup p G) (hp3 : 3 < p)
    (hOmega : Nat.card (omegaOne p G) ≤ p ^ 2) :
    IsMetacyclic G :=
  huppertMetacyclicStatement_all p (Nat.card G)
    G rfl hG hp3 hOmega

end

end Submission.OddOrder.BG.Section04
