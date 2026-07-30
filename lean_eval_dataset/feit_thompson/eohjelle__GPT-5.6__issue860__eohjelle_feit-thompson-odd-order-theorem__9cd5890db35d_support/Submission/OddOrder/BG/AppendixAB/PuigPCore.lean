import Submission.OddOrder.BG.AppendixAB.PuigCentralizer
import Submission.OddOrder.BG.AppendixAB.PuigPGroup
import Submission.OddOrder.MathlibSupport.PCore
import Submission.OddOrder.MathlibSupport.PPrimeCore

/-!
The Puig comparison between a Sylow subgroup and the `p`-core.

This module isolates the one deep Appendix A input as
`AbelianGeneratedConstrained`, then ports the complete alternating-series
argument of `BGappendixAB.pcore_Sylow_Puig_sub`.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01
open Submission.OddOrder.MathlibSupport

variable {G : Type*} [Group G]

/-- The exact constrained-generator consequence of odd `p`-stability used by
B.3.  Appendix A proves this property for odd solvable finite groups. -/
def AbelianGeneratedConstrained (p : ℕ) (G : Type*) [Group G] [Finite G] : Prop :=
  ∀ {P X : Subgroup G}, IsPGroup p P → P.Normal →
    GeneratedBy (PNormalizedAbelian p P) X →
    pPrimeCore p G = ⊥ → centralizerWithin (pCore p G) P ≤ P →
    X ≤ pCore p G

/-- Conditional form of B & G Lemma B.3.  The condition is discharged by the
odd `p`-stability port from Appendix A. -/
theorem pCore_sylow_puig_sub_of_constrained [Finite G] {p : ℕ} [Fact p.Prime]
    (S : Sylow p G) (hconstrained : AbelianGeneratedConstrained p G)
    (hprimeCore : pPrimeCore p G = ⊥) :
    puigInf (S : Subgroup G) ≤ puigInf (pCore p G) ∧
      puig (pCore p G) ≤ puig (S : Subgroup G) := by
  let T : Subgroup G := pCore p G
  letI : T.Characteristic := by
    dsimp [T]
    infer_instance
  have hTgroup : IsPGroup p T := by
    dsimp [T]
    exact pCore_isPGroup
  have hTS : T ≤ (S : Subgroup G) := by
    dsimp [T]
    exact pCore_le_sylow S
  have hterms : ∀ k,
      puigEven k (S : Subgroup G) ≤ puigEven k T ∧
        puigOdd k T ≤ puigOdd k (S : Subgroup G) := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp
        · simpa using hTS
    | succ k ih =>
        have hPgroup : IsPGroup p (puigOdd k T) :=
          IsPGroup.to_le hTgroup (puigAt_le _ T)
        have hPnormal : (puigOdd k T).Normal := by
          dsimp [puigOdd]
          infer_instance
        have hXgroup : IsPGroup p (puigEven (k + 1) (S : Subgroup G)) :=
          IsPGroup.to_le S.isPGroup' (puigAt_le _ (S : Subgroup G))
        have hgenNorm :
            GeneratedBy (NormalizedAbelian (puigOdd k T))
              (puigEven (k + 1) (S : Subgroup G)) := by
          rw [puigEven_succ]
          exact normalizedGenerated_mono ih.2
            (puigGenerated (S : Subgroup G) (puigOdd k (S : Subgroup G)))
        have hcent : centralizerWithin T (puigOdd k T) ≤ puigOdd k T := by
          simpa [puigOdd] using
            centralizerWithin_puigAt_le (p := p) (2 * k + 1) T (by omega) hTgroup
        have hXT : puigEven (k + 1) (S : Subgroup G) ≤ T :=
          hconstrained hPgroup hPnormal
            (normalizedGenerated_isPGroup hXgroup hgenNorm) hprimeCore hcent
        have heven : puigEven (k + 1) (S : Subgroup G) ≤ puigEven (k + 1) T := by
          rw [puigEven_succ k T]
          exact puigMax hgenNorm hXT
        have hodd : puigOdd (k + 1) T ≤ puigOdd (k + 1) (S : Subgroup G) := by
          rw [puigOdd_eq_succ_even, puigOdd_eq_succ_even]
          apply puigMax
            (normalizedGenerated_mono heven
              (puigGenerated T (puigEven (k + 1) T)))
          rw [← puigOdd_eq_succ_even (k + 1) T]
          exact (puigAt_le _ T).trans hTS
        exact ⟨heven, hodd⟩
  obtain ⟨mS, hmS⟩ := puig_limit (S : Subgroup G)
  obtain ⟨mT, hmT⟩ := puig_limit T
  let k := max mS mT
  have hSlimit := hmS k (le_max_left mS mT)
  have hTlimit := hmT k (le_max_right mS mT)
  have hk := hterms k
  constructor
  · calc
      puigInf (S : Subgroup G) = puigEven k (S : Subgroup G) := hSlimit.1.symm
      _ ≤ puigEven k T := hk.1
      _ = puigInf T := hTlimit.1
  · calc
      puig T = puigOdd k T := hTlimit.2.symm
      _ ≤ puigOdd k (S : Subgroup G) := hk.2
      _ = puig (S : Subgroup G) := hSlimit.2

end Submission.OddOrder.BG.AppendixAB
