import Submission.OddOrder.PF.Section01.InertiaInductionExpansion

/-!
# Rigidity from equality of multiplicity norms

The Clifford-correspondence argument in Peterfalvi 1.7(a) compares the
norm before and after induction.  Once the two norms are written as natural
number sums, equality forces every diagonal Hom multiplicity to be one and
every off-diagonal Hom multiplicity to vanish.  This file isolates that
elementary finite-sum argument from the character theory around it.
-/

namespace Submission.OddOrder.PF

noncomputable section

open scoped BigOperators

/-- If positive multiplicities have the same square norm before and after a
nonnegative change of Gram matrix whose diagonal is positive, then that Gram
matrix is the identity on the support. -/
theorem positiveMultiplicity_norm_rigidity {I : Type*} [DecidableEq I]
    (s : Finset I) (m : I → ℕ) (d : I → I → ℕ)
    (hm : ∀ i ∈ s, 0 < m i) (hd : ∀ i ∈ s, 0 < d i i)
    (heq : (∑ i ∈ s, m i * m i) =
      ∑ i ∈ s, ∑ j ∈ s, m i * m j * d i j) :
    (∀ i ∈ s, d i i = 1) ∧
      ∀ i ∈ s, ∀ j ∈ s, i ≠ j → d i j = 0 := by
  let L := ∑ i ∈ s, m i * m i
  let D := ∑ i ∈ s, m i * m i * d i i
  let E := ∑ i ∈ s, m i * m i * (d i i - 1)
  let O := ∑ i ∈ s, ∑ j ∈ s.erase i, m i * m j * d i j
  have hdiag (i : I) (hi : i ∈ s) :
      m i * m i * d i i =
        m i * m i + m i * m i * (d i i - 1) := by
    have hd1 : d i i = 1 + (d i i - 1) := by
      simpa [Nat.succ_eq_add_one, Nat.add_comm] using
        (Nat.succ_pred_eq_of_pos (hd i hi)).symm
    calc
      m i * m i * d i i = m i * m i * (1 + (d i i - 1)) :=
        congrArg (fun n ↦ m i * m i * n) hd1
      _ = m i * m i + m i * m i * (d i i - 1) := by
        rw [Nat.mul_add, Nat.mul_one]
  have hD : D = L + E := by
    dsimp only [D, L, E]
    calc
      (∑ i ∈ s, m i * m i * d i i) =
          ∑ i ∈ s,
            (m i * m i + m i * m i * (d i i - 1)) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hdiag i hi
      _ = _ := by rw [Finset.sum_add_distrib]
  have hsplit (i : I) (hi : i ∈ s) :
      (∑ j ∈ s, m i * m j * d i j) =
        m i * m i * d i i +
          ∑ j ∈ s.erase i, m i * m j * d i j := by
    exact (Finset.add_sum_erase s (fun j ↦ m i * m j * d i j) hi).symm
  have hR :
      (∑ i ∈ s, ∑ j ∈ s, m i * m j * d i j) = D + O := by
    dsimp only [D, O]
    calc
      _ = ∑ i ∈ s,
          (m i * m i * d i i +
            ∑ j ∈ s.erase i, m i * m j * d i j) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact hsplit i hi
      _ = _ := by rw [Finset.sum_add_distrib]
  have htotal : L = L + E + O := by
    rw [← hD, ← hR]
    exact heq
  have hE : E = 0 := by omega
  have hO : O = 0 := by omega
  constructor
  · intro i hi
    have hiE : m i * m i * (d i i - 1) = 0 :=
      (Finset.sum_eq_zero_iff.mp hE) i hi
    have hmi : m i * m i ≠ 0 := Nat.mul_ne_zero (hm i hi).ne' (hm i hi).ne'
    have hsub : d i i - 1 = 0 :=
      (Nat.mul_eq_zero.mp hiE).resolve_left hmi
    exact Nat.le_antisymm (Nat.sub_eq_zero_iff_le.mp hsub) (hd i hi)
  · intro i hi j hj hij
    have hiO : (∑ j ∈ s.erase i, m i * m j * d i j) = 0 :=
      (Finset.sum_eq_zero_iff.mp hO) i hi
    have hjErase : j ∈ s.erase i := Finset.mem_erase.mpr ⟨hij.symm, hj⟩
    have hijZero : m i * m j * d i j = 0 :=
      (Finset.sum_eq_zero_iff.mp hiO) j hjErase
    have hmij : m i * m j ≠ 0 :=
      Nat.mul_ne_zero (hm i hi).ne' (hm j hj).ne'
    exact (Nat.mul_eq_zero.mp hijZero).resolve_left hmij

end

end Submission.OddOrder.PF
