import Mathlib.Data.Nat.Dist
import Mathlib.Tactic
import Submission.OddOrder.MathlibSupport.FiniteTranslateOverlap

/-!
The numerical core of the quasi-homocyclic eigenspace rank argument.
-/

namespace Submission.OddOrder.MathlibSupport

open scoped BigOperators

universe u

variable {A : Type u} [AddCommGroup A] [Fintype A] [DecidableEq A]

/-- A rank profile whose squared-distance energy is two under every
nonzero shift is the indicator of the nonzero elements. -/
theorem quasiHomocyclic_rank_profile
    (rank : A -> Nat) (hrank_zero : rank 0 = 0)
    (htotal : 1 < ∑ x : A, rank x)
    (henergy : ∀ a : A, a ≠ 0 ->
      ∑ x : A, Nat.dist (rank x) (rank (x + a)) ^ 2 = 2) :
    Fintype.card A = (∑ x : A, rank x) + 1 ∧
      ∀ a : A, a ≠ 0 -> rank a = 1 := by
  have hrank_le_one (a : A) : rank a ≤ 1 := by
    rcases eq_or_ne a 0 with rfl | ha
    · simp [hrank_zero]
    · have hterm :
          Nat.dist (rank 0) (rank (0 + a)) ^ 2 ≤
            ∑ x : A, Nat.dist (rank x) (rank (x + a)) ^ 2 := by
        exact Finset.single_le_sum
          (s := Finset.univ)
          (f := fun x : A => Nat.dist (rank x) (rank (x + a)) ^ 2)
          (fun _ _ => Nat.zero_le _) (Finset.mem_univ (0 : A))
      rw [henergy a ha] at hterm
      simp [hrank_zero, Nat.dist_zero_left] at hterm
      nlinarith
  have hrank_cases (a : A) : rank a = 0 ∨ rank a = 1 := by
    have := hrank_le_one a
    omega
  let support : Finset A := Finset.univ.filter fun a => rank a = 1
  have hsupport_card : support.card = ∑ x : A, rank x := by
    calc
      support.card = ∑ x : A, if rank x = 1 then 1 else 0 := by
        simp [support]
      _ = ∑ x : A, rank x := by
        apply Finset.sum_congr rfl
        intro x _
        rcases hrank_cases x with hx | hx <;> simp [hx]
  have hsupport_zero : 0 ∉ support := by
    simp [support, hrank_zero]
  have hsupport_overlap (a : A) (ha : a ≠ 0) :
      translateOverlap support a = support.card - 1 := by
    have hoverlap_sum :
        translateOverlap support a =
          ∑ x : A,
            if rank x = 1 ∧ rank (x + a) = 1 then 1 else 0 := by
      unfold translateOverlap
      rw [Finset.sum_boole]
      congr 1
      ext x
      simp [support]
    have hpoint (x : A) :
        Nat.dist (rank x) (rank (x + a)) ^ 2 +
            2 * (if rank x = 1 ∧ rank (x + a) = 1 then 1 else 0) =
          rank x + rank (x + a) := by
      rcases hrank_cases x with hx | hx <;>
        rcases hrank_cases (x + a) with hxa | hxa <;>
        simp [hx, hxa, Nat.dist]
    have hsum_point :
        ∑ x : A,
            (Nat.dist (rank x) (rank (x + a)) ^ 2 +
              2 * (if rank x = 1 ∧ rank (x + a) = 1 then 1 else 0)) =
          ∑ x : A, (rank x + rank (x + a)) := by
      apply Finset.sum_congr rfl
      intro x _
      exact hpoint x
    rw [Finset.sum_add_distrib, ← Finset.mul_sum,
      ← hoverlap_sum, Finset.sum_add_distrib] at hsum_point
    have hshift :
        ∑ x : A, rank (x + a) = ∑ x : A, rank x :=
      Fintype.sum_equiv (Equiv.addRight a) _ _ (fun _ => rfl)
    rw [henergy a ha, hshift, ← hsupport_card] at hsum_point
    have hcard_pos : 1 ≤ support.card := by
      rw [hsupport_card]
      exact Nat.le_of_lt htotal
    have hcard_sub : support.card - 1 + 1 = support.card :=
      Nat.sub_add_cancel hcard_pos
    nlinarith
  have hsupport_large : 1 < support.card := by
    rwa [hsupport_card]
  have hsupport_eq : support = Finset.univ.erase 0 :=
    eq_univ_erase_zero_of_translateOverlap support hsupport_zero
      hsupport_large hsupport_overlap
  constructor
  · rw [← hsupport_card]
    exact fintype_card_eq_card_add_one_of_translateOverlap support
      hsupport_large hsupport_overlap
  · intro a ha
    have ha_support : a ∈ support := by
      rw [hsupport_eq]
      simp [ha]
    simpa [support] using ha_support

end Submission.OddOrder.MathlibSupport
