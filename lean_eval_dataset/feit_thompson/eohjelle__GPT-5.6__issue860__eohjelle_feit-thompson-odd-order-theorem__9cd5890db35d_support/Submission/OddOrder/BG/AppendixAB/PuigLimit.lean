import Submission.OddOrder.BG.AppendixAB.PuigOrder

/-!
Finite stabilization of the Puig series.

This ports `BGappendixAB.Puig_limit` and `Puig_inf_def`.  The proof replaces
MathComp's finite-cardinality induction with the corresponding strict growth
argument for mathlib subgroup cardinalities.
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01

variable {G : Type*} [Group G]

theorem natCard_lt_of_subgroup_lt {H K : Subgroup G} [Finite K] (hHK : H < K) :
    Nat.card H < Nat.card K := by
  have hcard : Nat.card H ≤ Nat.card K := Subgroup.card_le_of_le hHK.le
  exact lt_of_le_of_ne hcard fun heq =>
    hHK.ne (Subgroup.eq_of_le_of_card_ge hHK.le heq.ge)

theorem exists_puigEven_fixed [Finite G] (D : Subgroup G) :
    ∃ m < Nat.card D, puigEven (m + 1) D = puigEven m D := by
  by_contra hfixed
  push Not at hfixed
  have hgrowth : ∀ m ≤ Nat.card D, m + 1 ≤ Nat.card (puigEven m D) := by
    intro m hm
    induction m with
    | zero => simp
    | succ m ih =>
        have hm_lt : m < Nat.card D := by omega
        have hproper : puigEven m D < puigEven (m + 1) D :=
          lt_of_le_of_ne (puigEven_mono (Nat.le_succ m)) (hfixed m hm_lt).symm
        have hcardlt := natCard_lt_of_subgroup_lt hproper
        have hprev := ih (by omega)
        omega
  have hlarge := hgrowth (Nat.card D) le_rfl
  have hbounded : Nat.card (puigEven (Nat.card D) D) ≤ Nat.card D :=
    Subgroup.card_le_of_le (puigAt_le _ D)
  omega

theorem puig_terms_eq_of_even_fixed {m : ℕ} {D : Subgroup G}
    (hfixed : puigEven (m + 1) D = puigEven m D) :
    ∀ k, m ≤ k →
      puigEven k D = puigEven m D ∧ puigOdd k D = puigOdd m D := by
  have hoffset : ∀ d,
      puigEven (m + d) D = puigEven m D ∧
        puigOdd (m + d) D = puigOdd m D := by
    intro d
    induction d with
    | zero => simp
    | succ d ih =>
        have hindex : m + (d + 1) = (m + d) + 1 := by omega
        have heven : puigEven (m + (d + 1)) D = puigEven m D := by
          rw [hindex, puigEven_succ, ih.2, ← puigEven_succ m D, hfixed]
        refine ⟨heven, ?_⟩
        calc
          puigOdd (m + (d + 1)) D = puigSucc D (puigEven (m + (d + 1)) D) :=
            puigOdd_eq_succ_even _ _
          _ = puigSucc D (puigEven m D) := congrArg (puigSucc D) heven
          _ = puigOdd m D := (puigOdd_eq_succ_even m D).symm
  intro k hmk
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hmk
  exact hoffset d

/-- This is `BGappendixAB.Puig_limit`, i.e. B & G Lemma B.1(c). -/
theorem puig_limit [Finite G] (D : Subgroup G) :
    ∃ m, ∀ k, m ≤ k →
      puigEven k D = puigInf D ∧ puigOdd k D = puig D := by
  obtain ⟨m, hmcard, hfixed⟩ := exists_puigEven_fixed D
  have hstable := puig_terms_eq_of_even_fixed hfixed
  have hmN : m ≤ Nat.card D := Nat.le_of_lt hmcard
  have hterminal := hstable (Nat.card D) hmN
  refine ⟨m, fun k hmk => ?_⟩
  have hk := hstable k hmk
  constructor
  · calc
      puigEven k D = puigEven m D := hk.1
      _ = puigEven (Nat.card D) D := hterminal.1.symm
      _ = puigInf D := by rfl
  · calc
      puigOdd k D = puigOdd m D := hk.2
      _ = puigOdd (Nat.card D) D := hterminal.2.symm
      _ = puig D := by rfl

/-- This is `BGappendixAB.Puig_inf_def`, the second half of B & G Lemma B.1(g). -/
theorem puigInf_eq_succ_puig [Finite G] (D : Subgroup G) :
    puigInf D = puigSucc D (puig D) := by
  obtain ⟨m, hm⟩ := puig_limit D
  have hm0 := hm m le_rfl
  have hm1 := hm (m + 1) (Nat.le_succ m)
  calc
    puigInf D = puigEven (m + 1) D := hm1.1.symm
    _ = puigSucc D (puigOdd m D) := puigEven_succ m D
    _ = puigSucc D (puig D) := congrArg (puigSucc D) hm0.2

end Submission.OddOrder.BG.AppendixAB
