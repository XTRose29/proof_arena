import Submission.OddOrder.BG.Section01.Puig

/-!
Order properties of the Puig series from Bender-Glauberman Appendix B.

The successor reverses inclusion in its normalizing argument.  Consequently,
the even Puig terms form an increasing sequence, the odd terms form a
decreasing sequence, and every even term is contained in every odd term.  This
ports the order-theoretic part of B & G Lemma B.1(a-d).
-/

namespace Submission.OddOrder.BG.AppendixAB

open Submission.OddOrder.BG.Section01

variable {G : Type*} [Group G]

/-- The even-indexed terms of the Puig series. -/
def puigEven (n : ℕ) (D : Subgroup G) : Subgroup G :=
  puigAt (2 * n) D

/-- The odd-indexed terms of the Puig series. -/
def puigOdd (n : ℕ) (D : Subgroup G) : Subgroup G :=
  puigAt (2 * n + 1) D

/-- This is `BGappendixAB.Puig_succS`. -/
theorem puigSucc_antitone {D E K : Subgroup G} (hDE : D ≤ E) :
    puigSucc K E ≤ puigSucc K D :=
  puigMax (normalizedGenerated_mono hDE (puigGenerated K E)) (puigSucc_le K E)

theorem antitone_puigSucc (K : Subgroup G) : Antitone (puigSucc K) :=
  fun _ _ => puigSucc_antitone

@[simp]
theorem puigEven_zero (D : Subgroup G) : puigEven 0 D = ⊥ := by
  simp [puigEven]

@[simp]
theorem puigOdd_zero (D : Subgroup G) : puigOdd 0 D = D := by
  simpa [puigOdd] using puigAt_one D

theorem puigOdd_eq_succ_even (n : ℕ) (D : Subgroup G) :
    puigOdd n D = puigSucc D (puigEven n D) := by
  rw [puigOdd, puigEven, puigAt_succ]

theorem puigEven_succ (n : ℕ) (D : Subgroup G) :
    puigEven (n + 1) D = puigSucc D (puigOdd n D) := by
  rw [puigEven, show 2 * (n + 1) = (2 * n + 1) + 1 by omega, puigAt_succ]
  rfl

/-- This is `BGappendixAB.Puig_sub_even`. -/
theorem monotone_puigEven (D : Subgroup G) : Monotone fun n => puigEven n D := by
  let f : Subgroup G → Subgroup G := puigSucc D
  have hf : Antitone f := antitone_puigSucc D
  have hff : Monotone (f^[2]) := by
    intro A B hAB
    exact hf (hf hAB)
  have hiter : Monotone fun n => (f^[2])^[n] (⊥ : Subgroup G) :=
    hff.monotone_iterate_of_le_map bot_le
  intro m n hmn
  simpa [puigEven, puigAt, f, Function.iterate_mul] using hiter hmn

theorem puigEven_mono {m n : ℕ} {D : Subgroup G} (hmn : m ≤ n) :
    puigEven m D ≤ puigEven n D :=
  monotone_puigEven D hmn

/-- This is `BGappendixAB.Puig_sub_odd`. -/
theorem antitone_puigOdd (D : Subgroup G) : Antitone fun n => puigOdd n D := by
  intro m n hmn
  change puigOdd n D ≤ puigOdd m D
  rw [puigOdd_eq_succ_even, puigOdd_eq_succ_even]
  exact puigSucc_antitone (puigEven_mono hmn)

theorem puigOdd_anti {m n : ℕ} {D : Subgroup G} (hmn : m ≤ n) :
    puigOdd n D ≤ puigOdd m D :=
  antitone_puigOdd D hmn

/-- This is `BGappendixAB.Puig_sub_even_odd`. -/
theorem puigEven_le_puigOdd (m n : ℕ) (D : Subgroup G) :
    puigEven m D ≤ puigOdd n D := by
  let P : ℕ → Prop := fun k =>
    ∀ m n : ℕ, m + n = k → puigEven m D ≤ puigOdd n D
  have hP : ∀ k, P k := by
    intro k
    exact Nat.strong_induction_on (p := P) k fun k ih => by
      intro m n hmn
      cases m with
      | zero => simp
      | succ m =>
          cases n with
          | zero =>
              rw [puigOdd_zero]
              exact puigAt_le _ D
          | succ n =>
              rw [puigEven_succ, puigOdd_eq_succ_even (n + 1) D]
              apply puigSucc_antitone
              exact ih ((n + 1) + m) (by omega) (n + 1) m rfl
  exact hP (m + n) m n rfl

/-- This is the second inclusion in B & G Lemma B.1(d). -/
theorem puigInf_le_puig (D : Subgroup G) : puigInf D ≤ puig D := by
  simpa [puigInf, puig, puigEven, puigOdd] using
    puigEven_le_puigOdd (Nat.card D) (Nat.card D) D

end Submission.OddOrder.BG.AppendixAB
