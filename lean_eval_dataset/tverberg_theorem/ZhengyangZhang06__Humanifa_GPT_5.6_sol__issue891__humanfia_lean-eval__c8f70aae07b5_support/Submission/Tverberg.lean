import ChallengeDeps
import Submission.Helpers

open LeanEval.Combinatorics.Tverberg
open scoped BigOperators
open Fintype Set

namespace Submission

noncomputable section

private theorem euclideanSpace_sum_apply {α β : Type*} [DecidableEq α] [Fintype β]
    (s : Finset α) (v : α → EuclideanSpace ℝ β) (b : β) :
    (∑ i ∈ s, v i) b = ∑ i ∈ s, v i b := by
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih => simp [ha, ih]

set_option maxHeartbeats 4000000 in
/-- Sarkaria's tensor construction turns colorful Carathéodory into the
affine Tverberg theorem.  The parameter `q` is one less than the number
of parts. -/
theorem tverberg_succ (d q : ℕ)
    (f : Fin (q * (d + 1) + 1) → Space d) :
    HasTverbergPartition (r := q + 1) f := by
  classical
  let η := Fin q × Fin (d + 1)
  have hcard :
      Fintype.card η + 1 = q * (d + 1) + 1 := by
    simp [η]
  let reindex : Fin (Fintype.card η + 1) ≃ Fin (q * (d + 1) + 1) :=
    finCongr hcard
  let g : Fin (Fintype.card η + 1) → Space d := fun i ↦ f (reindex i)
  let lift (i : Fin (Fintype.card η + 1)) (b : Fin (d + 1)) : ℝ :=
    Fin.lastCases 1 (fun k ↦ g i k) b
  let simplex (j : Fin (q + 1)) (k : Fin q) : ℝ :=
    if j = k.castSucc then 1 else if j = Fin.last q then -1 else 0
  let tensor (i : Fin (Fintype.card η + 1)) (j : Fin (q + 1)) :
      EuclideanSpace ℝ η :=
    WithLp.toLp 2 fun p ↦ simplex j p.1 * lift i p.2
  have hsimplex (k : Fin q) : ∑ j : Fin (q + 1), simplex j k = 0 := by
    have hk : Fin.last q ≠ k.castSucc := (Fin.castSucc_ne_last k).symm
    rw [Fin.sum_univ_castSucc]
    simp [simplex, hk]
  have hcolor (i : Fin (Fintype.card η + 1)) :
      0 ∈ convexHull ℝ (Set.range (tensor i)) := by
    let weight : Fin (q + 1) → ℝ := fun _ ↦ ((q + 1 : ℕ) : ℝ)⁻¹
    apply mem_convexHull_of_exists_fintype weight (tensor i)
    · intro j
      positivity
    · rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
      simp only [nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
      exact mul_inv_cancel₀ (by positivity)
    · exact fun j ↦ Set.mem_range_self j
    · ext p
      rw [euclideanSpace_sum_apply Finset.univ
        (fun j ↦ weight j • tensor i j) p]
      simp only [PiLp.smul_apply, tensor, PiLp.zero_apply, smul_eq_mul]
      calc
        ∑ j : Fin (q + 1),
            weight j * (simplex j p.1 * lift i p.2) =
            (((q + 1 : ℕ) : ℝ)⁻¹ * lift i p.2) *
              ∑ j : Fin (q + 1), simplex j p.1 := by
                simp only [weight]
                rw [Finset.mul_sum]
                apply Finset.sum_congr rfl
                intro j _
                ring
        _ = 0 := by rw [hsimplex]; simp
  obtain ⟨choose, hchoose⟩ :=
    Helpers.colorful_caratheodory tensor hcolor
  rw [convexHull_range_eq_exists_affineCombination] at hchoose
  obtain ⟨support, weight, hweight_nonneg, hweight_sum, hcombination⟩ := hchoose
  have htensor_sum :
      ∑ i ∈ support, weight i • tensor i (choose i) = 0 := by
    rw [affineCombination_eq_centerMass hweight_sum,
      Finset.centerMass_eq_of_sum_1 _ _ hweight_sum] at hcombination
    exact hcombination
  let group (j : Fin (q + 1)) :=
    support.filter fun i ↦ choose i = j
  let mass (j : Fin (q + 1)) : ℝ :=
    ∑ i ∈ group j, weight i
  let weightedPoint (j : Fin (q + 1)) : Space d :=
    ∑ i ∈ group j, weight i • g i
  have htensor_coord (k : Fin q) (b : Fin (d + 1)) :
      ∑ i ∈ support,
          weight i * (simplex (choose i) k * lift i b) = 0 := by
    have h := congrArg (fun v : EuclideanSpace ℝ η ↦ v (k, b)) htensor_sum
    rw [euclideanSpace_sum_apply support
      (fun i ↦ weight i • tensor i (choose i)) (k, b)] at h
    simpa only [PiLp.smul_apply, tensor, PiLp.zero_apply, smul_eq_mul] using h
  have hlift (k : Fin q) (b : Fin (d + 1)) :
      ∑ i ∈ group k.castSucc, weight i * lift i b =
        ∑ i ∈ group (Fin.last q), weight i * lift i b := by
    have h := htensor_coord k b
    simp only [group, Finset.sum_filter] at ⊢
    simp only [simplex, mul_ite, ite_mul] at h
    rw [← sub_eq_zero] at ⊢
    rw [← Finset.sum_sub_distrib]
    convert h using 1
    all_goals
      apply Finset.sum_congr rfl
      intro i hi
      by_cases hik : choose i = k.castSucc
      · by_cases hil : choose i = Fin.last q
        · exact False.elim ((Fin.castSucc_ne_last k) (hik.symm.trans hil))
        · simp_all
      · by_cases hil : choose i = Fin.last q
        · simp_all
        · simp_all
  have hmass_cast (k : Fin q) :
      mass k.castSucc = mass (Fin.last q) := by
    simpa only [mass, lift, Fin.lastCases_last, mul_one] using
      hlift k (Fin.last d)
  have hpoint_cast (k : Fin q) :
      weightedPoint k.castSucc = weightedPoint (Fin.last q) := by
    ext b
    simp only [weightedPoint]
    rw [euclideanSpace_sum_apply (group k.castSucc)
        (fun i ↦ weight i • g i) b,
      euclideanSpace_sum_apply (group (Fin.last q))
        (fun i ↦ weight i • g i) b]
    simpa only [PiLp.smul_apply, lift, Fin.lastCases_castSucc, smul_eq_mul] using
      hlift k b.castSucc
  have hmass (j : Fin (q + 1)) :
      mass j = mass (Fin.last q) := by
    exact Fin.lastCases rfl hmass_cast j
  have hpoint (j : Fin (q + 1)) :
      weightedPoint j = weightedPoint (Fin.last q) := by
    exact Fin.lastCases rfl hpoint_cast j
  have hmass_total : ∑ j : Fin (q + 1), mass j = 1 := by
    rw [← hweight_sum]
    simp only [mass, group, Finset.sum_filter]
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i hi
    simp
  have hmass_last_formula :
      (((q + 1 : ℕ) : ℝ) * mass (Fin.last q)) = 1 := by
    calc
      (((q + 1 : ℕ) : ℝ) * mass (Fin.last q)) =
          ∑ _j : Fin (q + 1), mass (Fin.last q) := by simp
      _ = ∑ j : Fin (q + 1), mass j := by
        apply Finset.sum_congr rfl
        intro j _
        exact (hmass j).symm
      _ = 1 := hmass_total
  have hmass_pos : 0 < mass (Fin.last q) := by
    have hq : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
    nlinarith
  have hmass_pos' (j : Fin (q + 1)) : 0 < mass j := by
    rw [hmass j]
    exact hmass_pos
  let common : Space d :=
    (group (Fin.last q)).centerMass weight g
  have hcenter (j : Fin (q + 1)) :
      (group j).centerMass weight g = common := by
    change (mass j)⁻¹ • weightedPoint j =
      (mass (Fin.last q))⁻¹ • weightedPoint (Fin.last q)
    rw [hmass j, hpoint j]
  let parts : Fin (q + 1) → Set (Fin (q * (d + 1) + 1)) :=
    fun j ↦ {i | choose (reindex.symm i) = j}
  refine ⟨parts, ?_, ?_, common, ?_⟩
  · intro i j hij
    rw [Set.disjoint_left]
    intro k hki hkj
    simp only [parts, Set.mem_setOf_eq] at hki hkj
    exact hij (hki.symm.trans hkj)
  · ext i
    simp [parts]
  · intro j
    rw [← hcenter j]
    apply (group j).centerMass_mem_convexHull
    · intro i hi
      exact hweight_nonneg i (Finset.mem_filter.mp hi).1
    · simpa only [mass] using hmass_pos' j
    · intro i hi
      have hi_group := (Finset.mem_filter.mp hi).2
      refine ⟨reindex i, ?_, rfl⟩
      simpa only [parts, Set.mem_setOf_eq, Equiv.symm_apply_apply] using hi_group

end

end Submission
