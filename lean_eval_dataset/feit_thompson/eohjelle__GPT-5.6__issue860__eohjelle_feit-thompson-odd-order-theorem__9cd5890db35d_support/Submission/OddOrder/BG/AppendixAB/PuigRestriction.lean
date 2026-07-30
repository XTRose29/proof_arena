import Submission.OddOrder.BG.AppendixAB.PuigLimit

/-!
Restriction stability of the terminal Puig subgroup.

This ports `BGappendixAB.sub_Puig_eq`: once a subgroup lies between the Puig
subgroup of `D` and `D`, computing the Puig subgroup inside it gives the same
result.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01

variable {G : Type*} [Group G]

/-- This is `BGappendixAB.sub_Puig_eq`, i.e. B & G Lemma B.2. -/
theorem puig_eq_of_puig_le_of_le [Finite G] {H D : Subgroup G}
    (hHD : H ≤ D) (hPuigH : puig D ≤ H) : puig H = puig D := by
  have hcross : ∀ k,
      puigEven k D ≤ puigEven k H ∧ puigOdd k H ≤ puigOdd k D := by
    intro k
    induction k with
    | zero =>
        constructor
        · simp
        · simpa using hHD
    | succ k ih =>
        have heven : puigEven (k + 1) D ≤ puigEven (k + 1) H := by
          rw [puigEven_succ, puigEven_succ]
          apply puigMax
            (normalizedGenerated_mono ih.2 (puigGenerated D (puigOdd k D)))
          rw [← puigEven_succ k D]
          exact (puigEven_le_puigOdd (k + 1) (Nat.card D) D).trans hPuigH
        have hodd : puigOdd (k + 1) H ≤ puigOdd (k + 1) D := by
          rw [puigOdd_eq_succ_even, puigOdd_eq_succ_even]
          apply puigMax
            (normalizedGenerated_mono heven (puigGenerated H (puigEven (k + 1) H)))
          rw [← puigOdd_eq_succ_even (k + 1) H]
          exact (puigAt_le _ H).trans hHD
        exact ⟨heven, hodd⟩
  obtain ⟨mD, hmD⟩ := puig_limit D
  obtain ⟨mH, hmH⟩ := puig_limit H
  let k := max mD mH
  have hDlimit := hmD k (le_max_left mD mH)
  have hHlimit := hmH k (le_max_right mD mH)
  have hPuigHle : puig H ≤ puig D := by
    rw [← hHlimit.2, ← hDlimit.2]
    exact (hcross k).2
  have hgenPuig : GeneratedBy (NormalizedAbelian (puigInf D)) (puig D) := by
    rw [puig_def]
    exact puigGenerated D (puigInf D)
  have htrap : ∀ n,
      puigEven n H ≤ puigInf D ∧ puig D ≤ puigOdd n H := by
    intro n
    induction n with
    | zero =>
        constructor
        · simp
        · simpa using hPuigH
    | succ n ih =>
        have heven : puigEven (n + 1) H ≤ puigInf D := by
          rw [puigEven_succ]
          calc
            puigSucc H (puigOdd n H) ≤ puigSucc D (puig D) := by
              apply puigMax
                (normalizedGenerated_mono ih.2 (puigGenerated H (puigOdd n H)))
              exact (puigSucc_le H (puigOdd n H)).trans hHD
            _ = puigInf D := (puigInf_eq_succ_puig D).symm
        have hodd : puig D ≤ puigOdd (n + 1) H := by
          rw [puigOdd_eq_succ_even]
          exact puigMax (normalizedGenerated_mono heven hgenPuig) hPuigH
        exact ⟨heven, hodd⟩
  have hPuigleH : puig D ≤ puig H := by
    calc
      puig D ≤ puigOdd k H := (htrap k).2
      _ = puig H := hHlimit.2
  exact le_antisymm hPuigHle hPuigleH

end Submission.OddOrder.BG.AppendixAB
