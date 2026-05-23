/-
# Chen's Theorem for Markoff Graphs – Algebraic Core

Penner coordinates and Vieta involution algebra for triples in
`ZMod p × ZMod p × ZMod p`. The final graph-theoretic application
is in `Submission.lean`.
-/

import Mathlib

open Finset BigOperators

set_option maxHeartbeats 8000000
set_option maxRecDepth 4000

noncomputable section

namespace Markoff

variable (p : ℕ) [hp : Fact (Nat.Prime p)]

/-! ## Section 1 – Core Definitions -/

/-- The Markoff equation: a² + b² + c² = 3abc. -/
@[simp] def IsMarkoffSol (t : ZMod p × ZMod p × ZMod p) : Prop :=
  t.1 ^ 2 + t.2.1 ^ 2 + t.2.2 ^ 2 = 3 * t.1 * t.2.1 * t.2.2

instance (t : ZMod p × ZMod p × ZMod p) : Decidable (IsMarkoffSol p t) :=
  inferInstanceAs (Decidable (_ = _))

/-- The i-th Vieta involution on a triple: replace the i-th coordinate
    with its Vieta conjugate. -/
def vieta : Fin 3 → (ZMod p × ZMod p × ZMod p) → (ZMod p × ZMod p × ZMod p)
  | 0, (a, b, c) => (3 * b * c - a, b, c)
  | 1, (a, b, c) => (a, 3 * a * c - b, c)
  | 2, (a, b, c) => (a, b, 3 * a * b - c)

/-- Penner coordinate yᵢ for the i-th component. -/
def penner : Fin 3 → (ZMod p × ZMod p × ZMod p) → ZMod p
  | 0, (a, b, c) => if b * c ≠ 0 then a / (3 * b * c) else 1 / 2
  | 1, (a, b, c) => if a * c ≠ 0 then b / (3 * a * c) else 1 / 2
  | 2, (a, b, c) => if a * b ≠ 0 then c / (3 * a * b) else 1 / 2

/-! ## Section 2 – Algebraic Lemmas on Vieta Involutions -/

lemma vieta_preserves (i : Fin 3) (t : ZMod p × ZMod p × ZMod p)
    (h : IsMarkoffSol p t) : IsMarkoffSol p (vieta p i t) := by
  fin_cases i <;> obtain ⟨a, b, c⟩ := t <;>
    simp only [vieta, IsMarkoffSol] at h ⊢ <;> linear_combination h

lemma vieta_involutive (i : Fin 3) (t : ZMod p × ZMod p × ZMod p) :
    vieta p i (vieta p i t) = t := by
  fin_cases i <;> obtain ⟨a, b, c⟩ := t <;> simp [vieta, sub_sub_cancel]

lemma vieta_zero (i : Fin 3) : vieta p i (0, 0, 0) = (0, 0, 0) := by
  fin_cases i <;> simp [vieta]

lemma vieta_preserves_nonzero (i : Fin 3) (t : ZMod p × ZMod p × ZMod p)
    (hne : t ≠ (0, 0, 0)) : vieta p i t ≠ (0, 0, 0) := by
  intro heq; apply hne
  rw [← vieta_involutive p i t, heq, vieta_zero]

/-! ## Utility lemmas for ZMod p -/

private lemma zmod_ne_zero_of_lt (n : ℕ) (hn : 0 < n) (hlt : n < p) :
    (n : ZMod p) ≠ 0 := by
  rw [Ne, CharP.cast_eq_zero_iff (ZMod p) p]
  intro h
  exact absurd (Nat.le_of_dvd hn h) (by omega)

lemma zmod_three_ne_zero (hp3 : p > 3) : (3 : ZMod p) ≠ 0 :=
  zmod_ne_zero_of_lt p 3 (by omega) (by omega)

lemma zmod_two_ne_zero (hp3 : p > 3) : (2 : ZMod p) ≠ 0 :=
  zmod_ne_zero_of_lt p 2 (by omega) (by omega)

private lemma half_plus_half (hp3 : p > 3) : (1 : ZMod p) / 2 + 1 / 2 = 1 := by
  have : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero p hp3
  field_simp; norm_num

/-! ## Section 3 – Penner Coordinate Properties -/

lemma penner_sum (t : ZMod p × ZMod p × ZMod p)
    (h : IsMarkoffSol p t) (hne : t ≠ (0, 0, 0)) (hp3 : p > 3) :
    penner p 0 t + penner p 1 t + penner p 2 t = 1 := by
  obtain ⟨a, b, c⟩ := t
  simp only [IsMarkoffSol] at h
  simp only [penner]
  have h3 : (3 : ZMod p) ≠ 0 := zmod_three_ne_zero p hp3
  by_cases ha : a = 0
  · subst ha
    have hb : b ≠ 0 := by intro hb; subst hb; simp at h; exact hne (by simp [h])
    have hc : c ≠ 0 := by intro hc; subst hc; simp at h; exact hne (by simp [h])
    simp only [zero_mul, mul_zero, ne_eq, not_true_eq_false, ite_false,
      mul_ne_zero hb hc, not_false_eq_true, ite_true, zero_div, zero_add]
    exact half_plus_half p hp3
  · by_cases hb : b = 0
    · subst hb
      have hc : c ≠ 0 := by intro hc; subst hc; simp at h; exact hne (by simp [h])
      simp only [mul_zero, zero_mul, ne_eq, not_true_eq_false, ite_false,
        mul_ne_zero ha hc, not_false_eq_true, ite_true, zero_div, add_zero]
      exact half_plus_half p hp3
    · by_cases hc : c = 0
      · subst hc
        simp only [mul_zero, ne_eq, not_true_eq_false, ite_false,
          mul_ne_zero ha hb, not_false_eq_true, ite_true, zero_div, add_zero]
        exact half_plus_half p hp3
      · simp only [mul_ne_zero hb hc, not_false_eq_true, ite_true, ne_eq,
          mul_ne_zero ha hc, mul_ne_zero ha hb]
        have : a ≠ 0 := ha
        have : b ≠ 0 := hb
        have : c ≠ 0 := hc
        field_simp
        linear_combination h

lemma vieta_penner_pair (i : Fin 3) (t : ZMod p × ZMod p × ZMod p)
    (h : IsMarkoffSol p t) (hne : t ≠ (0, 0, 0)) (hp3 : p > 3) :
    penner p i t + penner p i (vieta p i t) = 1 := by
  have h3 : (3 : ZMod p) ≠ 0 := zmod_three_ne_zero p hp3
  fin_cases i <;> obtain ⟨a, b, c⟩ := t <;> simp only [penner, vieta]
  all_goals split_ifs with hprod
  all_goals try exact half_plus_half p hp3
  all_goals (
    have := left_ne_zero_of_mul hprod
    have := right_ne_zero_of_mul hprod
    field_simp
    ring)

/-! ## Section 4 – General Combinatorial Lemma -/

lemma Finset.two_mul_sum_of_involution {ι : Type*} [DecidableEq ι]
    {R : Type*} [CommRing R]
    (S : Finset ι) (σ : ι → ι) (f : ι → R) (c : R)
    (hσ_closed : ∀ a ∈ S, σ a ∈ S)
    (hσ_inv : ∀ a ∈ S, σ (σ a) = a)
    (hf : ∀ a ∈ S, f a + f (σ a) = c) :
    2 * ∑ a ∈ S, f a = S.card • c := by
  have key : ∑ a ∈ S, f (σ a) = ∑ a ∈ S, f a := by
    apply Finset.sum_nbij σ hσ_closed
    · intro a ha b hb hab
      have := congr_arg σ hab
      rwa [hσ_inv a ha, hσ_inv b hb] at this
    · intro b hb
      exact ⟨σ b, hσ_closed b hb, hσ_inv b hb⟩
    · intro a _; rfl
  have sum_pair : ∑ a ∈ S, (f a + f (σ a)) = S.card • c := by
    rw [Finset.sum_congr rfl hf, Finset.sum_const]
  rw [Finset.sum_add_distrib, key] at sum_pair
  linear_combination sum_pair

/-! ## Section 5 – Main Theorem (Vieta-closed Finset version) -/

/-- For any prime p > 3 and any finite set S of nonzero Markoff triples
    mod p that is closed under all three Vieta involutions, p ∣ |S|. -/
theorem vieta_closed_card_dvd (hp3 : p > 3)
    (S : Finset (ZMod p × ZMod p × ZMod p))
    (hMarkoff : ∀ t ∈ S, IsMarkoffSol p t)
    (hNonzero : ∀ t ∈ S, t ≠ (0, 0, 0))
    (hClosed : ∀ t ∈ S, ∀ i : Fin 3, vieta p i t ∈ S) :
    p ∣ S.card := by
  rw [← CharP.cast_eq_zero_iff (ZMod p) p]
  have h_half : ∀ i : Fin 3, 2 * (∑ t ∈ S, penner p i t) = (S.card : ZMod p) := by
    intro i
    have := Finset.two_mul_sum_of_involution S (vieta p i) (penner p i) 1
      (fun t ht => hClosed t ht i)
      (fun t _ => vieta_involutive p i t)
      (fun t ht => vieta_penner_pair p i t (hMarkoff t ht) (hNonzero t ht) hp3)
    rw [nsmul_eq_mul, mul_one] at this
    exact this
  have h_sum : (∑ t ∈ S, penner p 0 t) + (∑ t ∈ S, penner p 1 t) +
      (∑ t ∈ S, penner p 2 t) = (S.card : ZMod p) := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl fun t ht =>
      penner_sum p t (hMarkoff t ht) (hNonzero t ht) hp3]
    rw [Finset.sum_const, nsmul_eq_mul, mul_one]
  have h0 := h_half 0
  have h1 := h_half 1
  have h2 := h_half 2
  have : 2 * (S.card : ZMod p) = 3 * (S.card : ZMod p) := by
    calc 2 * (S.card : ZMod p)
        = 2 * ((∑ t ∈ S, penner p 0 t) + (∑ t ∈ S, penner p 1 t) +
            (∑ t ∈ S, penner p 2 t)) := by rw [h_sum]
      _ = 2 * (∑ t ∈ S, penner p 0 t) + 2 * (∑ t ∈ S, penner p 1 t) +
            2 * (∑ t ∈ S, penner p 2 t) := by ring
      _ = (S.card : ZMod p) + (S.card : ZMod p) + (S.card : ZMod p) := by
            rw [h0, h1, h2]
      _ = 3 * (S.card : ZMod p) := by ring
  have h_zero : (0 : ZMod p) = (S.card : ZMod p) := by linear_combination this
  exact h_zero.symm

end Markoff
