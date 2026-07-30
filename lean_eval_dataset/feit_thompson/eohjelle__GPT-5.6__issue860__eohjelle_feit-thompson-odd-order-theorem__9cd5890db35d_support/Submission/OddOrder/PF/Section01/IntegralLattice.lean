import Mathlib

namespace Submission.OddOrder.PF

/-- The free integral lattice on `ι`. -/
abbrev IntegralLattice (ι : Type*) := ι →₀ ℤ

/-- The standard symmetric integral pairing on a free integral lattice. -/
def coeffDot {ι : Type*} (f g : IntegralLattice ι) : ℤ :=
  f.sum fun i a => a * g i

/-- The squared norm for the standard pairing. -/
def normSq {ι : Type*} (f : IntegralLattice ι) : ℤ :=
  coeffDot f f

/-- The sum of all coefficients (the augmentation map). -/
def coeffSum {ι : Type*} (f : IntegralLattice ι) : ℤ :=
  f.sum fun _ a => a

/-- An integer sign is either `1` or `-1`. -/
def IsSign (ε : ℤ) : Prop := ε = 1 ∨ ε = -1

theorem isSign_iff_sq_eq_one {ε : ℤ} : IsSign ε ↔ ε ^ 2 = 1 := by
  exact sq_eq_one_iff.symm

theorem isSign_ne_zero {ε : ℤ} (hε : IsSign ε) : ε ≠ 0 := by
  rcases hε with rfl | rfl <;> norm_num

@[simp]
theorem coeffDot_zero_left {ι : Type*} (f : IntegralLattice ι) :
    coeffDot 0 f = 0 := by
  simp [coeffDot]

@[simp]
theorem coeffDot_zero_right {ι : Type*} (f : IntegralLattice ι) :
    coeffDot f 0 = 0 := by
  simp [coeffDot]

theorem coeffDot_add_left {ι : Type*} (f g h : IntegralLattice ι) :
    coeffDot (f + g) h = coeffDot f h + coeffDot g h := by
  unfold coeffDot
  apply Finsupp.sum_add_index'
  · intro i
    simp
  · intro i a b
    simp [add_mul]

theorem coeffDot_add_right {ι : Type*} (f g h : IntegralLattice ι) :
    coeffDot f (g + h) = coeffDot f g + coeffDot f h := by
  simp [coeffDot, mul_add]

theorem coeffDot_neg_left {ι : Type*} (f g : IntegralLattice ι) :
    coeffDot (-f) g = -coeffDot f g := by
  have h := Finsupp.sum_sub_index (f := (0 : IntegralLattice ι)) (g := f)
    (h := fun i a => a * g i) (fun i a b => by simp [sub_mul])
  simpa [coeffDot] using h

theorem coeffDot_neg_right {ι : Type*} (f g : IntegralLattice ι) :
    coeffDot f (-g) = -coeffDot f g := by
  simp [coeffDot]

theorem coeffDot_smul_left {ι : Type*} (a : ℤ) (f g : IntegralLattice ι) :
    coeffDot (a • f) g = a * coeffDot f g := by
  classical
  rw [coeffDot, coeffDot, Finsupp.sum_smul_index (fun _ => by simp)]
  change (∑ i ∈ f.support, (a * f i) * g i) = a * ∑ i ∈ f.support, f i * g i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coeffDot_smul_right {ι : Type*} (a : ℤ) (f g : IntegralLattice ι) :
    coeffDot f (a • g) = a * coeffDot f g := by
  classical
  unfold coeffDot
  change (∑ i ∈ f.support, f i * (a * g i)) = a * ∑ i ∈ f.support, f i * g i
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem coeffDot_comm {ι : Type*} (f g : IntegralLattice ι) :
    coeffDot f g = coeffDot g f := by
  classical
  unfold coeffDot
  change (∑ i ∈ f.support, f i * g i) = ∑ i ∈ g.support, g i * f i
  calc
    (∑ i ∈ f.support, f i * g i) =
        ∑ i ∈ f.support ∪ g.support, f i * g i := by
      apply Finset.sum_subset Finset.subset_union_left
      intro i hi hif
      simp_all
    _ = ∑ i ∈ f.support ∪ g.support, g i * f i := by
      apply Finset.sum_congr rfl
      intro i hi
      ring
    _ = ∑ i ∈ g.support, g i * f i := by
      symm
      apply Finset.sum_subset Finset.subset_union_right
      intro i hi hig
      simp_all

@[simp]
theorem coeffDot_single_left {ι : Type*} (i : ι) (a : ℤ) (f : IntegralLattice ι) :
    coeffDot (Finsupp.single i a) f = a * f i := by
  simp [coeffDot]

@[simp]
theorem coeffDot_single_right {ι : Type*} (f : IntegralLattice ι) (i : ι) (a : ℤ) :
    coeffDot f (Finsupp.single i a) = f i * a := by
  rw [coeffDot_comm]
  simp [mul_comm]

theorem normSq_eq_sum {ι : Type*} (f : IntegralLattice ι) :
    normSq f = ∑ i ∈ f.support, f i ^ 2 := by
  unfold normSq coeffDot
  change (∑ i ∈ f.support, f i * f i) = ∑ i ∈ f.support, f i ^ 2
  simp [pow_two]

theorem normSq_nonneg {ι : Type*} (f : IntegralLattice ι) :
    0 ≤ normSq f := by
  rw [normSq_eq_sum]
  positivity

theorem normSq_single_add {ι : Type*} (i : ι) (a : ℤ) (f : IntegralLattice ι)
    (hi : i ∉ f.support) :
    normSq (Finsupp.single i a + f) = a ^ 2 + normSq f := by
  have hfi : f i = 0 := by simpa using hi
  unfold normSq
  rw [coeffDot_add_left, coeffDot_add_right, coeffDot_add_right]
  simp [hfi, pow_two]

theorem normSq_eq_zero_iff {ι : Type*} (f : IntegralLattice ι) :
    normSq f = 0 ↔ f = 0 := by
  classical
  rw [normSq_eq_sum, Finset.sum_eq_zero_iff_of_nonneg]
  · constructor
    · intro h
      ext i
      by_cases hi : i ∈ f.support
      · have hs := h i hi
        simpa using (sq_eq_zero_iff.mp hs)
      · simpa using hi
    · intro h i hi
      simp [h]
  · intro i hi
    positivity

@[simp]
theorem coeffSum_zero {ι : Type*} :
    coeffSum (0 : IntegralLattice ι) = 0 := by
  simp [coeffSum]

theorem coeffSum_add {ι : Type*} (f g : IntegralLattice ι) :
    coeffSum (f + g) = coeffSum f + coeffSum g := by
  unfold coeffSum
  apply Finsupp.sum_add_index'
  · intro i
    simp
  · intro i a b
    simp

theorem coeffSum_neg {ι : Type*} (f : IntegralLattice ι) :
    coeffSum (-f) = -coeffSum f := by
  have h := Finsupp.sum_sub_index (f := (0 : IntegralLattice ι)) (g := f)
    (h := fun _ a => a) (fun i a b => rfl)
  simpa [coeffSum] using h

theorem coeffSum_smul {ι : Type*} (a : ℤ) (f : IntegralLattice ι) :
    coeffSum (a • f) = a * coeffSum f := by
  classical
  rw [coeffSum, coeffSum, Finsupp.sum_smul_index (fun _ => by simp)]
  change (∑ i ∈ f.support, a * f i) = a * ∑ i ∈ f.support, f i
  rw [Finset.mul_sum]

@[simp]
theorem coeffSum_single {ι : Type*} (i : ι) (a : ℤ) :
    coeffSum (Finsupp.single i a : IntegralLattice ι) = a := by
  simp [coeffSum]

/-- A lattice vector of squared norm one is a signed basis vector. -/
theorem eq_signed_single_of_normSq_eq_one {ι : Type*} (f : IntegralLattice ι)
    (hf : normSq f = 1) :
    ∃ i ε, IsSign ε ∧ f = Finsupp.single i ε := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp [normSq, coeffDot] at hf
  | single_add i a f hi ha ih =>
      rw [normSq_single_add i a f hi] at hf
      have ha_lt : a ^ 2 < 4 := by
        linarith [normSq_nonneg f]
      have ha_sq : a ^ 2 = 1 := Int.sq_eq_one_of_sq_lt_four ha_lt ha
      have hf_zero : normSq f = 0 := by
        linarith
      have hf0 : f = 0 := (normSq_eq_zero_iff f).mp hf_zero
      refine ⟨i, a, (isSign_iff_sq_eq_one.mpr ha_sq), ?_⟩
      simp [hf0]

/--
Every vector of squared norm two is the sum of two signed, distinct basis vectors.

The two signs need not be opposite unless an augmentation-zero hypothesis is added;
for example, two basis vectors with coefficient `1` also have squared norm two.
-/
theorem eq_sum_signed_singles_of_normSq_eq_two {ι : Type*} (f : IntegralLattice ι)
    (hf : normSq f = 2) :
    ∃ i j ε δ, i ≠ j ∧ IsSign ε ∧ IsSign δ ∧
      f = Finsupp.single i ε + Finsupp.single j δ := by
  classical
  induction f using Finsupp.induction with
  | zero =>
      simp [normSq, coeffDot] at hf
  | single_add i a f hi ha ih =>
      rw [normSq_single_add i a f hi] at hf
      have ha_lt : a ^ 2 < 4 := by
        linarith [normSq_nonneg f]
      have ha_sq : a ^ 2 = 1 := Int.sq_eq_one_of_sq_lt_four ha_lt ha
      have hf_one : normSq f = 1 := by
        linarith
      obtain ⟨j, δ, hδ, rfl⟩ := eq_signed_single_of_normSq_eq_one f hf_one
      have hij : i ≠ j := by
        intro hij
        subst j
        apply hi
        simp [isSign_ne_zero hδ]
      exact ⟨i, j, a, δ, hij, isSign_iff_sq_eq_one.mpr ha_sq, hδ, rfl⟩

/--
The norm-two classification in the augmentation-zero lattice: such a vector is a
signed difference of two distinct basis vectors. This is the form used in PF1.4.
-/
theorem eq_sign_smul_single_sub_single_of_normSq_eq_two {ι : Type*}
    (f : IntegralLattice ι) (hnorm : normSq f = 2) (hsum : coeffSum f = 0) :
    ∃ i j ε, i ≠ j ∧ IsSign ε ∧
      f = ε • (Finsupp.single i 1 - Finsupp.single j 1) := by
  classical
  obtain ⟨i, j, ε, δ, hij, hε, hδ, rfl⟩ :=
    eq_sum_signed_singles_of_normSq_eq_two f hnorm
  have hεδ : ε + δ = 0 := by
    simpa [coeffSum_add] using hsum
  have hδeq : δ = -ε := by
    linarith
  refine ⟨i, j, ε, hij, hε, ?_⟩
  rw [hδeq]
  ext k
  by_cases hki : k = i
  · subst k
    simp [hij]
  · by_cases hkj : k = j
    · subst k
      simp [hki]
    · simp [hki, hkj]

end Submission.OddOrder.PF
